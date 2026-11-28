import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36320.Model
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


end PEqualNP.Outside.L_meta_36320.Model

namespace PEqualNP.Outside.L_meta_36320
open PEqualNP.Outside.L_meta_36320.Model
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

def SBf (j : Nat) : Nat := [6, 6, 8, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36320

namespace PEqualNP.Outside.L_meta_36320
open PEqualNP.Outside.L_meta_36320.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x8c40480e0520a031160143bf43bd43be42bc42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x4c000108ea98852c525065ca5205554430
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => packedAt s0K4 (208+((h/4+packedAt s0K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s0K3 (111+((h/1+packedAt s0K3 (108+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 2 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 3 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x8040888500808002904c02240229109408d131
  | 2 => 0x10891048252442502a11214921422528a22486
  | 3 => 0x895229034a480ca58426541654054a85454b18
  | 4 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36320
namespace PEqualNP.Outside.L_meta_36320
open PEqualNP.Outside.L_meta_36320.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x154021d090180200160180200c40de43dd43de32dc32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x8b00008eaa0654c524c66aa2205394a30
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => packedAt s1K4 (212+((h/4+packedAt s1K4 (192+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s1K3 (111+((h/1+packedAt s1K3 (108+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7ffffe07fff07e0ffff83ffff07ff03e79f3f3
  | 2 => 0x83f07ff87ffffff0783fc3c0ff87ffffa64c7f
  | 3 => 0xfc007fff83ff87ff803ffc00fff87fc1c78f9c
  | 4 => 0x7ffffc0007ffffc00000ffff8001f80fe0
  | 5 => 0xffff8000000007ffffffffff00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x860023008208001884804463008908c0891b1
  | 2 => 0x2084a441214442503212428844852530a24446
  | 3 => 0x112948921a880ca6842ca81299504a85458a98
  | 4 => 0x5ace712550ed573b5e862224ee660319f80f60
  | 5 => 0x630c61c6630e67cc673733380c440c21f76000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaa0f0a0faaafaaafaa0f0a0faaafaaafaa0f0a0faaafaaafaa0f0a0faaafaaafaa0f0a0faaafaaafaa0f0a0faaafaaafaa0f0a0faaafaaafaa0f0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36320
namespace PEqualNP.Outside.L_meta_36320
open PEqualNP.Outside.L_meta_36320.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xc817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a07bd4940b7a92817c52503d8a4a05b14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330ef21e61dd43cc2fca5987b94b30b7296617d52cc3daa5985b54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30f7294616e528c2faa5187b54a30b6a94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930ef19261dc324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea9441ef42883d885107b8ca20f6994417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42483de64907b0c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107bd0820f621041ee32083da64105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd18421f930843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443f460887e4c110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccbde85997b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbc86997750d32f721265ed424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c837e52907dca520db94a41bea9483ed52906daa520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63de438c7ba8718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa9263ef524c6dea498df14931f6292636c524c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f790c31eea18637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f7a1643ec42c87dc6590fb4cb21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f7a1243ec42487dc6490fb4c921fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1
  | 2 => 0x8824001210000009d0001244ec858003c0758cf16d00046cca800000260b781f4164b07f87a2be000002520000000012729e64046a064cc049420000000005700010895516000000788130000000003024000011c0000039c78c0028c00000000000010308000000002c4000000000011487c4c2304288000000c00011c0000002a8f1272659388003b2000000fe428734b51eb408a39318002184fc012970006bcf99873b0280c225c17ea193fa1304019c8282e18aa1475000000904000654367c4dc800110000000003940000000047c22cc98163a0000ac1b50000005e00000a000000894ce950000be00040c8c8000000000000000000123800000000000f40963986b1b10b4620a28ce0b643c361293ba354c121739e92c000f20984003180a23a2993627238c0181c87935074919042342000000193567f05b00000014c2508000063c188000002d4a5a2a000000001b647a4480003d0008e40006b3f04c00006f4c088c000dd1c49e8a48000340000000031200000000166000000000008bd468000004940000032e49000000462000da21208a0004e0000060010780046e938d3062526000e980000000000000000000000150001500000026e9ac7a800000000e10000008011b0002ba034001df34e000002460003e400000000000000000005f8eb80009a5987c0a80e048d0f81d2e65000026a00037c00000000440be12200025d4383a23c000001c80000000000100000e0000080500200c040000020040100400c00000000004000008010020080000000001c000000000080b0010020000000001a0100700000c0100000700200401008000010000040020000700000000c0000c00000800800006014020000000040300000e04004000006008000020060200180001205c00000002024010000000000200001200c0000401200400800000000020000020000200e0000040200100200400808004004000010120280180001801012805000000020020020240180a0040140180100000c0280300401c000060000000000b00000c0480201202000001014004008160000000000c0160040180a00200000000000000020000080100080000000004800004004018020020000000000000401005002000008010020000300000800001000bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485e
  | 3 => 0x4ee0c80009621a3cc2e1440921dcd714c4ae0000003c0002a852800000000faa16000175251d100000000192158000000000000006d1b81a078440a590004d88982c28400000066000000080002081a0000002e80000020c4d04d000000000000000000002ec00000000000000eb38a000000214064cd042192c0000fc9012f2000fd2501966280000000075006181000000000003985b84516c442000b883e0820605e8cf0523dd24a7c0000ec4f8005208ed26858522794582641ec5e81792627859c001700006392d0000882bc0008200001d1a80018824c321c9000001478000000000004e4fa1646b8000004b45b8001c0000000000008380001c1c2000000fd42a1b80000010a93c760000000008302700052030a8903c0b400128300118002800000000026d0be00008a4c1680002b92a000000f69e4000674c18ba29a9609593815a001399852d20003d80000004c000000001cc3a9be4be005110000007f54584f3fc6700000045a7fc0000000000000076000000be800000978001750000000000026a0a8bf8a927a0001a0000903bc988950006880000000041c00000000000002424a26ec6d8002ac988000000003c000163448000000001b8920a38001060a0bb000000550990003d0898b425d2c46a44709b3547103498b4f0584488780fc0000025b000660a88001da000ed8ca000000f60b80ac278fd80041423ced000000000d1a2048a70c4d2010007a81ba0d10c2508fa814e88084c8000008e80026e00054063a440568140a00b0005c8ee21c00090c8b8002945dc972074f2000a310e0122e46f0503188783514114636055a2e0e229c000a14566641221a29c3000003544a458000d93cc8fd1803f0003ec61800528000b200000006c002880008a0f90004780000000e4d2001329080000013f0001442c929a82422548ac8000006c8f821000859472a3321456c438003d2334979200000007d02235a0000015a0006fcdea7501e348e386d1d00000019b118a0c00000286000000000000000000000010000000000000d28a400086000000000000888e44de0013d9ba0003b800000000148de000366650000000bc700000000fa45464800382424d80002d60000001733e000000360007bd1c02330c79c1283327c1d06a0001ce000a9a701a6000d21d50001fc8a27636e0001c0003bc874fa0002aa6448c0002346b1450722f02747e0002aea4874a563347dd1a17b3ec89c689ee31a000661cb00032000000000318480001c60014a9022bc68021a962b
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x310c25f654c0309ed95300c25e63153209758c54c823e6414f208f59053c82ad640cb208f99251c823d6494720b318d21c825e63d52209758f548825e63152209758c548827661152209d584548823e6494e208f592538831e6494e20c7592538834d6294e20d394f42882cd6310a20d394c428834e538ca20d394d32882ae6488620d394e218834e5308620d394f208823e64951209bd89544825e63151209758c544823e6515120c798c544831d6315120cb588544823e6494d208f592534826d6294d208fd91534823c6454d209dd8553482746154d209b996424832c54909209b195424832c54509209b997324832c54cc9209b99432482ad640c920cb150324826e65c8520cb153214832c5448520b318d214832c5488120b398e204825e63150209758c540826e62150209d984540827561150209b98b530823e6414c208f59053082766114c209d584530826d65d08209b59442082cd63108209b596320826f654c82097d8d510825c63544209b59621082ae64884209798e500825d63940209bd9520082ac64480209ed95200826e62d53109b58b54c425e63953109758e54c426e62953109b58a54c426f6254f109b18953c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c425f6354b109718d52c426f62552109b189548425e63152109758c548426e62152109b588548426e62d4e109b58b538423e6494e108f592538426e6294e109b58a538425e63d4a109758f528423f6454a108f191528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10d6580534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c524433454905109d1954144358538c1109e195304425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c109e980530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520433554c40109e596100435953840109dd95100433554440109ed9510043595344010
  | 1 => 0xc74c528c5319b98b540c66d62d50319e983540c67960d50318f596540c71e63950318f990540c66e62150319b588540c67a60150319e580540c65d6590c31c7951430c6cc6250c31cb952520c72d5494831cb951520c72d5454831d390d520c74d4354831d354a320c69d640c83197d95310c6cc624c4319dd95310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c75a4354031d650d500c75a3254031d60c9500c75b3154031d64c5500c65e63153219758c54c863e6414f218f59053c86cd6310b219798e50c865d63943219798e548865d6395221c798e548871d6395221cb58a548863e64d4e218f593538863e6414e218f590538867a6014e219e580538872e5490a21cb951428872e54cca21ab590328872e540ca21cb953218865e63951219758e544866d629512197d8d544865c63551219ed81544867860551219798e534866f6254d218f990534863d6414d2197994534871e6414d21c7590534874d6214d219b997424874c53d09219b99442486cd6310921d314c424866e658c921d314e324866c654c921d314d32486ae6488521d314e214866e62d50219798c540865d63150219e980540867960150218f990530863d6414c219b988530867a6014c219e580530866d65908219bd95420866d65cc8219b59432086ad640c8218f992510863d64944219bd9521086cc63484219dd95210863f64540218f191500866f6254f409b18953d026e62947409b58a51d026e6294e409b58a53902ac6250e40a758c429025f63546409718d519026f62546409b18951902ae62906408f997415032c52d0540cb149415032c5290140c794d43102ac6250c40d394e521034d5394840d394d521034d5354840cbd0d521032d4354840cb54a421029d6310840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cdd0d51103354354440cd909511033442544408f59641102ae6290440cd54641103355110440cd547401023f6550040ab189401033551500409ed95401026e62d53309b58b54cc31e63953309b98854cc26d6215330c795143cc2cc6250f30cb95252cc32d5494b30cb95152cc32d5454b30d390d52cc34d4354b30d354a32cc29d640cb30b318931cc26e62d52309b58b548c26e62152309b588548c27661152309d584548c34e528c630d3948318c2d9600c630d394b308c26f62551309b189544c27761551309d185544c26e62151309b588544c25c6550d30b3189434c2d86050d30a7590324c23e64145308f590514c26e62145309b588514c25e65cc530b3189314c2ce628c1309bd89540c26c62550309798c540c26e62150309b588540c27661150309d584540c23e6494c308f592530c26f62544309b189510c25d658c430b658
  | 2 => 0xf2484b800000000078169482200000000010a60c3605f1747a4c71012c26e0000c60ac810b99570007b8000e92cc0007a80016e00000014276298eaa0e32a3f00000000048c001e60003ec00000000660000000000000002b0001601e8001140000002900000101907000000001033b600000214000618a111821873c751be0724203695c3bc144bc99a01c29c560000007bc002130000000020d062000d480000010400a0c3383b0000163ec78c6f14f2b05a41d9f3412224e490e0005889d0000ee5dc180003e850c641d438831d0914b2fc7c8ed0763626b800178434000e52161066a04590400000000000250348218980b6014cf0dd2fe4bc7e9b33d40bc0000004800085800000310f2175000000000002a05346580000004cee87d32203008008020080001c0100806000000140702c0801c020140600c0100003008030000001408000080180700000008050000000003000000040202c0700403004000080101c000280500c010000400000014000000003c020500a000000040900c2f0180002c000040000c0500000030050340002c0500002024020180209c000040000002048020000302002008000100f008020000300401000000040b038000180501000010010001700c010000005c0300000004080040000404000000040d00400000050080d0000400002008030180a000000000600c0001011000060466e62947439b58a51d0e6f62543439b18950d0e6f62546439b1895190e6e62942439b58a5090e3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210eac6250f4297d8d5190a5c63546429798e5090a5d6394242d31895310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7a60d53329e58354ccacc6250f32e350f42ccacd6310b328f992518ca3d64946328fd91508ca3c64542329d986544ca7561951329bd89544ca5c6550d329b996424ca6c6550932e350d424ca3d6595032cb189540ca3e64150329798c540ca6e62150329b597420cb2d54d08329b594420cb2d5410832b358c420cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320cb1e5350f41ab18943d074e5394b41d354e52d074e5354b41d354d52d072f4354b41cb50d52d072d5290b41a758c42d072e52d06419b988535066d6214d41ab18943506b46150d41a758c42506ae62905419798c505065d63141419b988505066d62141419bd89531066c6254c418fd95411067765504419bd89501066c62540419bd8954cc66c62553319b98854cc66d62153319b98a50cc66d62943319b98b548c66d62d52319b98a548c66d6295231b3189438c69d640ca318fd91508c63c64542319bd89508c66c62542319758e544c66e62951319b58a544c66f62551319b189544c67b60551319e181544
  | 3 => 0x1472402185a9364226e8000000007581f800000000001bc1621c0af80022264c000000000b90580036e00829156000450112061dc064569f50002040000013c1ecbe12a39a304c28af000428000000000dc000003e00000500000054400192000000069450000001e17d1680a0000001fe250848c023662890800000000000001182e0001c00f2760000000ca6f4f00003d00001a0fa3080e0990e23ca098778003be370af13d000820041d208e000000da16421c000001e8000001822004c40002000000089800000000001340000000004900079c91187096630e38002da1883d0e811e5306c2150005809f0000004180391f000000060000000009c8000002fc21000000000688be3b20000000009e00000000000454e316814a070221a22ce15c9c1a60005742f0000006c0000e40000005e0002e2664a20001e400050012000174e411907c00cd1874000000810933ae270ad0360003c400000000000f89fc03a56c6f80031270c00159292704108ed0000247814e0000b00016f15c000000001c0000001d002a0187f03a1aa5ac6b9702801144f93f2d866c4107f1f26d0001eb0dc2ec508001a08281180010083c000003200000d1272ec6d5028cf0ea3dc0017a000468000000004f0e707112e0009b8a3000314298e708c324d21fd3720008b16400072c2a800238000000003fe3285480021e34c000003400000f8001348403987c000554ff0001ac65c9a8ab11c2e4510613a65ec5b06809819c3917222438c000f309c6d8001aa25a1503181b2a6364b5202022290302180000000000000809c001410007e0350db2943d82e0002520001a80020a85c3c12c01e474669c233a190d29e1302308ba2011a82649289b342168491ad0002a8e28e53d8060201b22ca2588b800400000000000000004813004a198000001f0000540e1432550000000000000008d2c60000002a34e6b0e60c32567e4f10b3000478a31801cc000001d102e6ac440321d61200816e0001a45e99f31a62c999523762104e86b0001284a9fa3b80003f2070002440010d31e0002806f000000058000007ec269883da2c0cb1af19c650930cc0667dc2c9b
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x3902582020010160004801403000003c000000054034a0000000c000000001110700b0005d40000060000000000004c00000004003000800005835516310832a90e4a1aa018d19740c9500c6a439262a80638358d6295221a1ae72a28510c2d769503288706b22c429a43135d85310921a1ae829a6490e0e6414e214869239286a8881455cc4254440c4cc4a8c8220624625454010325292c018c61835916294e2089aed298851050d7494d3288307324a710c418358d6215120a1ae62a2849042d7615032483062a0c690a41831526388120
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x650080d87990538852180d87992538862080d87150634852080d871526388120
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 6 => packedAt s2K6 (718+((h/13+packedAt s2K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s2K5 (20359+((h/221+packedAt s2K5 (17928+(h % 221)*11) 11) % 1059)*11) 11
  | 4 => packedAt s2K4 (22272+((h/179+packedAt s2K4 (20482+(h % 179)*10) 10) % 782)*11) 11
  | 3 => packedAt s2K3 (1281+((h/8+packedAt s2K3 (1225+(h % 8)*7) 7) % 81)*6) 6
  | 2 => packedAt s2K2 (243+((h/1+packedAt s2K2 (240+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x87ffffc0ffc3fe0ff0ff0ffff87f03fd31f3cf
  | 1 => 0xf81f87ff0ffffff07f0ff0e07f87fffece4c7f
  | 3 => 0xffe007fff003e3ff800fff007ff803830f8f8c
  | 4 => 0x7fffffc03fffff000007ffffc03f00ff0
  | 5 => 0xfffff800000003ffffffffff80000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x908500460084400190110123280910a81091c5
  | 1 => 0x242088825010050210610441082495046441a
  | 3 => 0x314b551263aa86b6888baa095d502a1b0b8e8c
  | 4 => 0x659466248a20cb2b5aa088126664b023b00b60
  | 5 => 0x46184438cc3313cc6ccccc9c0440c043ed6000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36320
namespace PEqualNP.Outside.L_meta_36320
open PEqualNP.Outside.L_meta_36320.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x83a402518000106502c201b5bf42bd42df32dd32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x141810084c018d424ca5aa5a0d354831aca80632d521026aa2205354b30
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
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
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s3K3 (197+((h/2+packedAt s3K3 (189+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf8ffffc1fc3e1fe1fc3f0fffc3f8387f4cf70f
  | 1 => 0xff0787fe3fffe1fe1fc3f0e0fc3fff87b349f3
  | 2 => 0xfff807ffc03ffe3fe003ff00ffc03ff8c38e3c
  | 4 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8110044004420002404012240488812041305
  | 1 => 0x10400888101002040841104404121204114052
  | 2 => 0xa22255108aa9106ac222aa08aa812560c28c28
  | 4 => 0x86b566252a0d54b376a88812f3258132ec0f80
  | 5 => 0xc4c64439b331993d9b33cc9c22060644fbe000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36320
namespace PEqualNP.Outside.L_meta_36320
open PEqualNP.Outside.L_meta_36320.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x9200980090018b80287400000011ab4e0001c4438002504068b369002918200112a10016061550000800184a1cc803c6908a007c0131e0000c000a0c0000100000ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4617c548c2faa7185754e30bf294617d528c37e85186f50a30bf28c617d518c2fca11877cc230fd984617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a261df434c3bc86987750d30ee21a617f524c2f8a4986fd0930dea1261df324c3bc6498774c930ee192617f514c2f8a29877cc530ef18a61dd314c3b862987ecc130ef18261df544c33ea8987795130eeaa261dc544c338a89877d4930ef29261dd524c3b8a49877d0930cfa1261de424c3ba84986750930ee21261df514c3bca2987754530ee28a61df414c3bc82987750530ee20a61df214c3bc42987748530ee10a61df504c3b6a09877d0130ef20261dd404c3b880985fd5030bf2a0617d540c2f8a8185f94c30af298617e520c2faa4186fd0830dea10617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20dfa1641ee42c837a85907b50b20d6a16417e51c82faa3907bc8720f690e41df30c83ba61905fd5220bf2a4417d54882f8a9105fd4e20bf29c41de53882bca7105f54e20eea9c415d53882f8a7105f54a20dfa1441bd42882fca3105f54620bf28441df30883f46110774c220fc98441d930883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20dfa1241ee424837a84907b50920d6a12417f51482f8a2907bc8520f690a41df30483f46090774c120fc98241d930483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf29041bf420837a84105f94420fb288417651082faa2107d54420baa88417e50083be6010774c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43ec83887d50710fb10e21f521c43be6188774c310bfaa4217e54842faa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10bfa94217e52842faa5085f14a10dfa1421bd42842faa3085f94210ef98421dd30843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c524437e84886f50910fb20a21f541443ec42887d48510ef98221dd30443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810bf288217e50043be6008774c010fb88021fa10043ea20087e44010
  | 1 => 0xc535077c86a0ef10d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea9083bf421077a8420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc7be8798f710f31bf296637d52cc77e8598ef50b31ef99663dd32cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c637e528c6faa518efd0a31dea1463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931dfa1263bd424c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418efd0831dea1063de320c7b86418df94431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c877e8590ef50b21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21dea14437e51887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21dfa1243bd42487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043bf420877a8410df94421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53903bca7205794e40bea9c81dd53902baa7206f90e40de21c817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940dfa1281bd42502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206fd0840dea10817e51103eca2205d94440bea8881f551102eaa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3be87987790f30eea1e61dc43cc2fca5985f54b30dfa1661bd42cc3be6598778cb30ee99661dc32cc2fca3985f54730ef98e61de31cc3ba6398770c730efaa661de54cc3baa9987715330efa9661de52cc3baa5987714b30efa16619f42cc3bc85987750b30cea1661dc42cc3bea3987794730eea8e61dc51cc3be83987790730eea0e61dc41cc3be43987788730ee90e61dc21cc3be81987790330eea0661dc40cc2fea9185f95230beaa
  | 2 => 0x10000060200280000403c040030060140080102a000058010000040580100600000008000008000020140000180200204c00006000000000050040100081504a000000000000000100200001400010000000020020100100080200600c0000801c014038020020240580000e040000060000000100003c0000600300c0000082001e0040000103a00001001000014000080000000080100200c0080400002006800008000008000000340080300c0140380d01e004008010000000000001201000000002010060000040040000b002000038010080000680c00001801004006004008000040000080100800400014014000078010260180000900005c000030000100100100a0140000101000c02005000000000020080540480000000400800002000058000000140380f00800000006bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f90f42dea1e85bc43d0afca3a15f54742bf286857d50d0b7ea7a16f94f42dea9e85bc53d0b7ea3a16f94742dea8e85bc51d0b7ea1a16f94342dea8685bc50d0afaa9214f55242bf29c857d5390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350bbea6a157d4d42be29a85dc5350ab8a6a16fd0d42df21a85bd4350b7886a17bd0942df212857f5150af8a2a15fd4142be28285bf5350b3ea6a16f94d42dea9a85bc5350b38a6a16fd4942d7a9285bf5150b7ca2a16f54542de28a85bf5050b7ca0a16f54142de282857e5410a7ca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccb7e85996f50b32bf28e657d51ccafca1995f54332bfaa4657e548cb7ca9194f95232beaa465bd548ca7aa9195f15232bea9c65df438cbb887195f94a32dfa1465bd428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132dfa1265bd424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832dfa1065bd420cbbe64197b8c832ee99065ed320cafca2197d94432bb288657d510cbeaa2195d54432bf28065fa500caf4a0195f54032fca806579500cafca7a0df54f41df21e83bc43d06fca5a0df54b41dfa1683bd42d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837
  | 3 => 0x800000000000000000010d1680000c8c68001280e0c4000534cc4978002f83053820d28678c00000000b390080064c8c80000000092853800210000ab0002c6269410093b4b040000030acac00000610a80543141d42005a0006607340000030221c290ad4703cc002e0000000000000000004c8005ba00177ac2000000002973ce76d90aa2000abc000003e851cb5301452a34e09fd2f03c02da111bc460861c0498418c500064045c001770569b55aae30045340b800396ca0001821b4000598002baa2c8584c348444000000000000001b256ae5418d25ac000b3ada3fc365599140c0000002d10009a4d88004aa1f8ab8000006c9140000004d0002db0006d8002a71a81a40012e0004f038000000550000005d20000000059e000002641aa13ce40004a4000000bb0002f49025d192529910c43920517c8000008e91200021c0006c2a80000000000024e540000970000013b00000002000000462000000000849e1949e40000794e1e133ab557f9d75e2a4d828000004fcbaa5b53e0001a054330320418891524e8d580300032d69a44246114c9000288001330000507a53fa2051e9f0080ce40e9c4ff800248c6c5fa351d02704a9300b090c000000000000006a342000000000000000000004a000000000001e17b1e20a27bd0528a5981ad06000282000ca2b45da000000560fa44ca4000254bd480af30003d4139326229b80ca5f07891cc324e2324b0ac970158001490eb0001a07f1f60000009b800000001288000006b4b08004420016c2480004a400000000b0c79190284818528000003a4ea8001ac285010a20008ec0e99347eb70530e00001c94f0000004340017e400000ae1df2146951700037eb49480006460000e2411ba2c816aa901c0dc280883acc355e8cd2e84985c0b70007802726f0c465cda8003603d196b2c41e000151d9000995772ae39474d1c92211e0000000000000000000000a8c0017f000000550001dc001992801200d53b94938a1204c21d1da8202e9c6518601112c0000000b29aa000c405b2c9378a10102331cc0008022d000b5d058000007446115f1f68d07d218000000b613b4c00003795303eb6455a232bc000000000000000000049a000d12be626494000000000000019909a1ed8a8000ea40d7e95839c08ca914f13ea50940001269885d0af65c0600031f2b6000370000000009084b0000018b0220ee9015b0060000015d0000cc0000030a53681400286148408b58715ee0010e0000000000025944e0013d254576a986babc000ab45f02c2e6c2d1e95531e61d33a120c69f4c48410005bd831f760e011081d200401602000801002000000040040000080e01c01c010010000000000102201c008050220080080100e0000180200c00004020002000000060000400600200e000028000040000
  | 4 => 0x850b7104306a600022a00e00128000588ba0000430008b1640155560000000d3f00000026a00081000226116afc001dd0b40000032548aca8003331181f00000058e0009a800236228a00cf0ce00048800000c703d19b0000004b0f81fa9598f00063a000f331a1b82750cb024d084c078000b2bc863aa521e00136000000000000003d8568000000006d12988643e0000013133c000002370ec0c42b9c7074184d60240000005700008e000002d00008540000000038ce22cb000000000fc000001179793e40006f9602cc8d97213637a0ec722b250a74124ab737c208cd1d407270d7e2ea53228d7d8003dc6b85aa3c0da9601993d5ccb78d780035200005ae50be1d000000194000000003e600140800000bb1438004560014b08e0b82c0be91009234ce13183700a4a8aaa180000dd8001ce698000d10002e4ee00022c68c1b0f10cac30182b02f63193ab09594384502cd4bca911800000073c0d1ba0aa6440003e0f2000002030000004909e05e479358c5042000d02731b6a750f2e202421587a090222f18c8001c46cd230003f44e000000000000848b10004e52baeb5420002300042c7ad89176000c380005326686c001455be0000b11d1de190a33243f6a540019c20a0007ca3e000001309f90000000014b00041c002171ecbf8000000000001f8004b400000000000000000005620013199f4f26a0b21f010247ce6000000110000730026dccb0001363402f18c3e29f84227b5f4000f4000000001212880d84f8469f52e45c4c71de4e8a24b10ff41cb841332f1ca04c8918b5700b962b003b0000002f422a0000028e07a000000ec5a8c9d8b8003ca000a70c332abe0b491a496100f525c372c1002ae70945b48e17a0001fc0024f000000000005e0ab00500052200000000000001390cc3080009680034e7f00014c0003dd63000000000062250007b581
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xc53082766114c209d584530827a6014c208f992520823d64948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb94942083365494420cd55251083565394420d554e51083374294420cd50a51083365454420cd55151083565354420d554d51083374254420cd509510825e63940209758e500825d65cc020c7953300831d54cc020d5947300835551cc02097d95300831e544c020c75513008356514c020d5545300835a504c020cb553200836551c8020d654e200837151880209bd95200832d5448020d9545200827b6548020d654d200837151480209798f54c425d63d53108f99353c423d64d4f108f99252c423d6494b1097d8d52c425c6354b108f99052c423d6414b109798c52c425d6314b109798f548425d63d52109798c548425d63152109b988548426d62152108fd91538423c6454e10c7d91538431c6454e109798f528425d63d4a108f992528423d6494a108f990528423d6414a109798c528425d6314a10c794f428431d53d0a10c794d428431d5350a10cb949428432d5250a10d654e20843595348210ea509208425e63d51109758f544431e63d5110c758f544423d62d51108f992544423e65151108f588544433561151108f992534423d6494d108fd91534423c6454d109bd89534426c6254d108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d09108f995424423c6550910cd15241442746550510bc18141442746548510c7d53304431c54cc110c7d51304431c544c1109e19520443a94248110f8485204425e63d50109758f540426e62d50109b58b540423d65950108f58a540423f62550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530425f6054c1097581530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48108f992520423d64948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520432e5454810cb551520434e5354810d354d520432e6454810cb591520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d52508109798e500425d639401097597300431e54cc010c7553300434e52cc010d354b300425f654c010c7951300431d544c010d3949300434d524c010cd553100436552c40109e596100436952840109dd9510043355444010d954910043d130440109ed9510043695244010
  | 1 => 0xc31c54cc530a7992314c29d648c530c7151314c354514c530a758b544c29e6495130b6582544c2db6055130a7994544c31e6515130a7588544c29e6494930a7592524c31c5494930b6582524c29f6454930a7191524c2d76154930b5185524c2db6054930a7990524c29d6414930c7150524c2d66114930b5584524c29e65d0930a7197424c29d6490930b6982424c2d9609093097d95424c25c6550930c7d95424c29e6550930a7195424c31c655093087195424c38f6250930a7990424c2da6010930b6580424c31c54d4530a7992514c29d6494530b6582514c29f6454530a7191514c31c5454530b3d89514c2cc6254530b6d81514c355511453097996414c25d6590530b6d81414c2d86050530b6980414c2d96010530a7993214c29d64c8530b6983214c2d960c853097d95214c25c654853097994214c25d6508530a7990214c29d6408530b6980214c2d96008530c7d53504c31c54d4130e6d53504c39854d4130b658b504c39b42d4130e650b504c25e659013097994404c2ce6210130b3588404c2d66110130b5584404c39940101309798f540c25e63150309b988540c26d62150309d984540c27561150308f992520c23d6494830c794f420c31e5350830cb949420c32d525083097d95300c27b654c030d694d300c32e629532097d8d54c825c6355320c7d8d54c831c63553208f99353c823d64d4f208f99053c823d6414f209d98453c82756114f20cb95142c82af6550b20cbd9542c838f6350b20e318d42c825f63547209718d51c82ad64c8720c795330c831d54cc320e350b30c831e544c320c755130c838d424c3209798f548825d63d52209798c548825d63152209d98454882756115220d6982538823f6454e208f191538831f6454e20c7191538831e53d0a20c754f428831e5350a20c754d428823f64546208f191518835a534c220b6d95308835b654c220e6d913088398644c220e6d093088399424c22097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d20ab592424826c6550920cbd95424832c6550920e3d8d424838c6350920ead8142483a860509208f990514823d64145209798c514825d6314520ab593214838d42cc120b658e30483a9428c120e35093048278654c120ea509304835b654c120d6195304839b644c120e619130483cb624c120f2189304839b424c120f29093048399424c120f25093048389424c120f2c8530483c9214c120ea50b20483c930881209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798
  | 2 => 0x624c5218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530865d6094c21c7951530871d5454c2197d81530863e6414c218f590530865e6314c219d984530867a6014c219e580530863e64948218f592520863d65d0821c794f420871d53d08218fd95420871e5350821c754d420875553884219bd9521086776548421d554d21087a542484219798e500865d6394021ce95250087395494021d694e50087595394021d698e50087596394021ced0a50087394294021ce95150087395454021d694d50087595354021d698d50087596354021ced0950087394254021dac8550087722154021da4855008771215402197d8d52d025c6354b40cb54b42d025e63947409758e51d031d5310e40c794f429031d53d0a40a718d429031e5350a40c754d429032e5250a40cb549429029e6390640cbd49425023e65d0540c754e43102b96010c40d394e521034d5394840d394d521034d5354840cb991521032e4354840cb10d521031e53d0840c754f421032d52d0840a718d421031e5350840c754d421032e5250840d594e51103555394440d994a51103655294440cdd0a51103354294440d594d51103555354440d994951103655254440cd90d51103344354440cdd09511033542544408f596411029e6390440cb54a41103355190440cb54841103355110440cb54b401033551d00408fd95401032d5250040cd545401027b65500409d98754cc27561d53308f99252cc23d6494b30a799232cc29d648cb30a799032cc29d640cb30b598432cc2d5610cb308f99251cc23d6494730a799231cc29d648c730d554431cc2d661d5330b558754cc2d960d5330b658054cc2d960d4b30a799252cc29d6494b30a799052cc29d6414b30b598452cc2d56114b30b658052cc25f6550b309719542cc31f6550b30c719542cc38f6250b30a799351cc29d64d4730b658351cc29e6494730a759251cc3555114730b658051cc25e65907309759641cc29e64c8730a759321cc25f65487309719521cc25e65087309759421cc29e6408730a759021cc2da6008730b658021cc2ce6210330b358840cc2d66110330b558440cc26e62152309b588548c27661152309d584548c23e6494a308f592528c32e5250a30cb549428c31d63d51308f58b544c23e64951308f994544c31d63151308f588544c25e65d0d30c7152434c25c6550d30c7d50434c23e64149308f590524c27661149309d584524c23e65d09308f197424c23e65509308f195424c29e648c930a7592324c31c548c930b6982324c29e640c930a7590324c31c540c930b5984324c2d5610c930b6980324
  | 3 => 0xd42a798e5350aad6294d42abd895350a9e6514d42c79945350a9d6014d42c7d4f5250b1c53d4942e3d4f5250b8c53d4942ab5835250b1c53d4542a798e5150a9d6394542a7d8d5150a9c6354542c714d5150abb6054542ae1815150b355114542a798e5050a9d6394142c714e5050a9f6354142a718d5050ab76154142ad1855050a9e6314142a758c5050b1c5314142ad9845050ab561141428fd954210a6f6550842cb9514210a5e63940429758e5010a3e64947328f59251cca3f64543328f19150ccb1f6355232c7550438ca7661951329d586544ca5f63551329d987540ca7561d50329e983540ca7960d50328f596540cb1c63550328f990540ca7661150329d584540ca7a60150329e580540cb1d54d0c3297594430cacd6210c328f992520ca3d64948328f597420ca3f655083297d95320cb8d424c8329bd95320cb365494432cd552510cb374294432cd50a510cb365454432cd551510cb574354432d510d510cb374254432cd509510cb573254432d54c9510cb3a5494032ce552500cb725194032dc546500cb3b4294032ce50a500cb3a5454032ce551500cb725154032dc545500cb5a6354032d6d0d500cb584354032ced09500cb394254032d6cc9500cb593254032cb54b42d069c6350b419798e50d065d639434197582539065f6054e41c794f429071d53d0a41c794d429071d5350a41cb549429071e53d06419798e509065d6394241ad986435069c6350941cbd4942506b46150941a798e415065e63141419758c505066e62141419b588505065f63548419718d521072d52d0841ad587421063f65504419dd95411065e63940419758e501067a60d53319e58354cc63e6494b318f59252cc63d62952318fd89548c63e6494a318f592528c63f65d0a318f597428c63f6550a318f595428c71e548ca31c7950328c6d5610ca31b6580328c71e54cc6319b98a544c66d629513197997434c6d661d0d318f990524c63d64149319e980524c6796014931cbd49424c72c525093197997324c69e648c5319798f540c66e62150319b588540c67a60150319e580540c63e64948318f592520c72e5250831cb549420c65d658c831b5584320c6d9600c8318f992510c63d649443197d95310c677654c4318fd91500c63c645403197d8d54c865c6355321c7d8d54c871c63553218f99353c863d64d4f218f99053c863d6414f219e98053c86796014f219798e50c865d63943219798f548865d63d52218f993538863d64d4e219798e508865d63942218fd91508863c64542219798e544865d639512197d8d544865c63551219ed81544867860551218f993534863d64d4d21c7993534871d64d4d2197583534865e6394d219799453487556114d2197580534871f53d0921c714f424871f5350921c714d4248754538c5219d19531486e4
  | 4 => 0x486a873cc4c5571a75c22e0000136540006d00017c4cd808000002900016f220000000b955e7b860a4c00000000280000000c317c18ec20d115828e2f0308003b238c00127000904842c8000b48ae0bd0d070d3125e21eb740028560417d1ca330003b00014d0008e00010303603c001cd0004a5939880005b13d80000e0000034b000b30002b64e2000000003ea6344890b426d9d23a48392dd40b818218b94d42d022c030758853fea34491d2442658c215f6b85391e03f0c0159adb532508c1538314b6160d7002000000000ad0003c8000001de45c11800416730003221fc841ad1a61869d04096938a4a80f1cf48c0c058b0c0009253eb0d1ee00064800224000d7af15f06744c8001f45543d00008a2c14d85e5b65d5a13406be95c3f8354e00000e91342c1d0de02f2b2000002fd4b0001a0b712e20000029765e0009080000000103acb6ae9109e37a3e20ec000005b260400000000c91bc97d0000000017368ada80000858cae8000002ac4b8db2ea0da3d410130000001009a53068090b800000001b7800000d759a2d800000171800000975b62144580013f0000000013fa9f000260f18002b4098001da0fa280a0a0a0249e0d800047c6786888644ace58a87b042d58aeabc3042ed0f00380000e028000000160040080f000000008000000580000200a0040680d00001800000008018000000000000300200000008021030004010020000580080a00a0040000100200c0280700802c000000180080400d000000018070060000c80402e0080080e0080000280000000c0300001400806818018000000150040041200b00e020020080040000302900a0080000000601c0000300000800803000004030050020000400100000800801004008020070000000000400007c070010000180181302200402009014004018000040140100000a0900800002402c00002024000010000420100000300000400008000010000000040000000106a0240000802c0040000103a00c010090000140300300403000820008000000140000040580900201c018090000080081e01802404800018054050000020001c8010000040000e000010018010020100080100a000000020000001280001c0ac008030000640080002a0040980001006c028020020000980300001800001000054050090000000100000203400804002000008020080500200a018000008058fd954310e5f6550c439798e51d0a5d63947429798e50d0a5d6394342ab58b53d0ab661d4f42ad58753d0aad6214f42a798f51d0a9d63d4742a798e51d0a9d6394742cd54451d0a9e6394342a758e50d0a9e6314342a758c50d0ab66114342ad58450d0a5e63942429758e5090a5d60d4d42975805350b1c53d0d42c7d4c4350a5e63141429758c5050a7661141429d5845050a9d60d4
  | 5 => 0x4696e2c93c4940a48004861d45a8330009f1848510002cc153051ca6a54d0000007cc0d28f5e642800336374001ac8e86ee860000002c4ad1b29bd2f02510e04016816800000000000001970000f175800658639931a36ec0f8ab8004a24448d8005845a98d9064eec840030a69e31005289322360c29ca336c782eb4a0f2328ee8000006502b852380790cfb0e000000000003385fc9e9000005413680000012d0600000084400000000d51be1d73bc0b800260000000000041983980000020a364388695169cc14882692889881db26e50cfd9e5372da081000000c449200015ecfca8a8300a000ef90e000ab00030f000040f614f47e4d40002c5d80015980037e8393ca26288cc50186549a095558cf0000014eab05e4b0c0005958048d023124800006fb385a2df566a63092ae4798ee538498e205c04e3d835a2859e2884a800090000002ad4d674c749fd23ea58003164dc000b69930008a8319f4000718002e60002281b80024a0012505b000c644f847382338ba0003e42fd3b0d33fc63d628e45246ac751701e87c0003435a66c48e0f81966cd5b8dd3ecd117788b2ee868120c5526cd532b470e00009b04d468271360ae504590ea25a53c0d90e96b626600d23296f6ba5982270a01bc000ed5b4034320a10004b50a9e963a2d8af23a180234bb2a6650cf8c614c6400598224e5da25ce736218cad57a1ac6987a82506257e6540012f5ac1b1b0a06270000548006c891415800638000dc000202bed340460000004ea530000000023d038044f3b2565c8ad48a2e354501b99184c23c11ab0724466510306690508e59b241a0016ba3b1fa1a97b16500047511800000348b7323000000a296654000000284000000003702fc761a68d64eadb839352424b7c00000000000000004b800000000552a84c5b6b1184fc000b7212000c80006f0000260d5028000e80005c4624cc2a2000708cd1190ee41daf0cd0741559d8004de000ee00055095495800000c2c0007c0000014c22d0005ed591fa0a8241ba33a5ea684fb8a8000038f0003000d44daaee002aed6a0000006f80019262e0000000010e0a0b39ed000ac4421f9000000000fb6d2340a58804640016220f000000002aa01272000000664a38f41680442c8299340000017ba8a0167856a8d462800000000000451003182f455127b3700c89000187000b78990783f0111ac1200000000003d0dc754b91390009644780063400044ae758e06552abe314a64da14a4ac0b44f0e0502000000000680015c31f0009900020959ca4033a666e4478e3873518864000ac1363f03f1b70000000001f000b90bcaff600bf052abd35a56c278000000001904200000055a375fc001040004f40000022f1bc90800000000139290ba000000002f950ccf05526a000d80d025f22a86c3b0e128c74
  | 6 => 0x930007580013b00020d96b5011c299a31fc072388dda545c04b04b3662c6a506b8db00028c1c00046ca91a73334e4bc00010452a29c7f80067a0012580040ab046e000000b28a914800087d7d288606a8ca99ef6dacac000880005807893e1849a4219eb0008a400000082ba0001614620004d0004ced8c640000cc0000000002a3e5aa93a1ce
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x2e000e762200003a0012000c00006c04701600000000000056000042585c00363400004c00002a001e0000000000606400000008104a02000000247c38000014541c7e000000300000182c4e000000786e00005000007a823c680646005e005a526200840000282666000044000000006a00000000000000000000000080481a742086000a00003e327200400000000001000301000000000001000000010000010000c30a6302a2a1530705445150a8cb80a6282858514d6114142a8ae421aa219705424c9510caa4b9086a8065c250932540328b2e031aa420d0d72950328c70b2a2c21946386951600ca31a52e02928498c2d72191500c60f3b6a6a1243385c0624c521e0aa6a124210f21424855008694b8086a9081265c06350840a62e021aa22051473509511024cb84c7208818398d5290440c2cc6a8c822041d76150324c286b90a81926185151610c930a1ae42a0a49861454584524c20f3accaa1261831506254530a88e4a88a2984c972181414c20e3aac990a61a25894010130d22c2a00809841c7655130c82463b28498641071d95350a20930eca12611060c6518d42482c4b80c6a1241625cc6050920d10c630284905a17118142482463b284982412a1d9424c120c30ca32260905897219130482c4ba0c498241a2190624c120b82e2312609058974909304824c3b28498241321d9424c120d16eca12609058a7650930482c43b28498241a21d9424c120910eca12609058974c85304820e3b2a6a1421c254d42482109c2e4302828841e76d513044388aa26088021d05493044010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xb00180021c6694403a46a090c00980a118014d6114142a0582951610ca31a0982951600ca31911801cd4254440a098098d5290440a118098d5190440a0582151610c930a05821516114930c08655c06350920c80635c46050920c08655c8644c120c80645c4624c12088a869d9424c120888865d3214c1209088754d4248210
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
  | 4 => packedAt s4K4 (37250+((h/298+packedAt s4K4 (33972+(h % 298)*11) 11) % 1180)*11) 11
  | 3 => packedAt s4K3 (3508+((h/22+packedAt s4K3 (3332+(h % 22)*8) 8) % 141)*8) 8
  | 2 => packedAt s4K2 (925+((h/5+packedAt s4K2 (900+(h % 5)*5) 5) % 19)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc7f8ffff078ff1f871e3e3ffe383f0fe0cf4cf
  | 1 => 0xf87f0f8ff80ffe3f81fc7c707c03ff1e7348f3
  | 2 => 0x7ff00ffff1ffc7fe007f807ffc7fe1838f3c
  | 3 => 0xff80000ffffe0007ffff80007fff8001fc0fc0
  | 5 => 0xfffffff000000007ffffffff80000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x50082101101022001020809120889044041445
  | 1 => 0x831242122124c04180c4242244112618314892
  | 2 => 0x242004244201000a2200490409204880828128
  | 3 => 0x1106ab4895086494d5690009725a024d5c0ec0
  | 5 => 0x2644cc00e64d89276992724e00600c91ebe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaf8e8f8e8feeafeeaf8e8f8e8feeafeeaf8e8f8e8feeafeeaf8e8f8e8feeafeeaf8e8f8e8feeafeeaf8e8f8e8feeafeeaf8e8f8e8feeafeeaf8e8f8e8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36320
namespace PEqualNP.Outside.L_meta_36320
open PEqualNP.Outside.L_meta_36320.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x410980061c240055401198264051a06340214e9521e0000e002254014321c9014088d9f18000021600b0000a15801e5ce80520800c5280046022082081ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa81bd41503be62a0774c540fda0281be40502fca8205f94c40bea98817e52102faa4206fd0840dea10817e51102faa2206f90440de20881df31103ba62205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330efa1e61dc43cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28e617d51cc3be6398774c730bfaa4617e548c37ca9184f95230beaa461bd548c27aa9185f15230bea9c617e528c2faa5186fd0a30dea1461de328c3b865185f94630bea8c61df318c3ba63185f94230ef98461fb308c2fea8985f95130beaa2617c544c3be86987710d30bfa92617c524c37e84986f50930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4186fd0830dea1061de320c3b864185f94430bea8861df310c3ba62185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20dfa1641bd42c82fca3905f54720ef98e41dd31c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441bf428837a85105f94620bea8c41df31883ba63105f94220fd18441f930883de41107ec8220bfaa2417e54482faa8905f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20dfa1241bd42482fea2905f14520ef98a41dd31483de42907b48520fd18241f930483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf29041bf420837a84105f94420fb288417651082faa2107d54420baa8841df31083ba62105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43be6388774c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437e85086f50a10bea8c21df31843ba63085f94210fd20421f940843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c524437e84886f50910ef98a21dd31443ec42887d48510fd20221f940443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810bf28821df31043ba62085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc53506fea4a0df14941dfa1283bd42507ee82a0ef90541bfa82837c50506fca820df94c41ef298835e53106faa620f754c41aea9883be43107788620df94841f7290836e52106faa420fb54841b6a9083bf421077a8420df94441dfa0883f6411077a8220fd50441bf28083fa50106f4a020df54041fca80837950106fea998df95331beaa6637c54cc7be8798f790f31eea1e63dc43cc6fca598df54b31dfa1663bd42cc7be6598f78cb31ee99663dc32cc6fca198df54331efaa663de54cc7baa998f715331efa9663de52cc7baa598f714b31efa16639f42cc7bc8598f750b31cea1663dc42cc7be8398f790731eea0e63dc41cc7bea198f794331eea8663dc50cc6fea918df95231beaa4637c548c6faa718d754e31bf294637d528c77e8518ef50a31bf28c63df318c7ee6318df94231bea84637f544c77ea898cfd5131bf2a2637d544c6f8a898ef151319e2a263df434c7bc8698f750d31ee21a637f524c6f8a498efd0931dea1263df324c7bc6498f74c931ee19263f7314c7bc6298dfd4131be28263df544c73ea898f795131eeaa263dc544c738a898f7d4931ef29263dd524c7b8a498f7d0931cfa1263de424c7ba8498e750931ee21263df514c7aea298f7d0531ef20a63dd414c7b88298f7d4131ef28263dd504c7b8a098dfd5031bf2a0637d540c6f8a818df94c31af298637e520c6faa418efd0831dea10637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21dfa1643ee42c877a8590fb50b21d6a1643df31c87ba6390df94321bea86437f54886fca910df55221be2a4437f53886fca710f794e21af29c437d53887baa710d754e21be29c437d528877e8510ef50a21bf28c43df31887ec6310f74c621fa98c43d531887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c534877e8490fb90921dea1243ed424875a8490f7cc521fb18a43dd31487ea6290f54c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043bf420877a8410df94421ef98843dd31087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740ef98e81dd31d02faa9205f94e40ef29c815e53902faa7207754e40aea9c817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c81df31903ba63205f94240dfa0481fb40902fea6a05f14d40df21a81bc43502fea4a05f14940dfa1281bd42502fea2a05f14540dfa0
  | 2 => 0x180400e00008006000018080070000040202400000000802000000010120020000080500c0040001c006000028160000200e000016028078010240040080b000048010030120002381b00403c0800e00e0040b80300a004008000020100000c026004008080080040000d0000000000b00400c0c80500001800011002010110010200140680000c01c0000a002010000010000100000000401c0180800a004038010060080380001e000000040000040080400c004000000080001b81300200400000000000000060080081180a00600019816004004000060000000000000400c0100000006c0600700e004000150060041800300c0000500300002c0100600e0000380100001c0080d0000040180300000804001000030018000000000800b0000200500c0220080280002401c01800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f90f42dea1e85bc43d0afca3a15f54742bf286857d50d0b7ea7a16f94f42dea9e85bc53d0b7ea3a16f94742dea8e85bc51d0b7ea1a16f94342dea8685bc50d0afaa9214f55242bf29c857d5390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350bbea6a157d4d42be29a85dc5350ab8a6a16fd0d42df21a85bd4350b7886a17bd0942df212857f5150af8a2a15fd4142be28285bf5350b3ea6a16f94d42dea9a85bc5350b38a6a16fd4942d7a9285bf5150b7ca2a16f54542de28a85bf5050b7ca0a16f54142de282857e5410a7ca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccb7e85996f50b32bf28e657d51ccafca1995f54332bfaa4657e548cb7ca9194f95232beaa465bd548ca7aa9195f15232bea9c65df438cbb887195f94a32dfa1465bd428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132dfa1265bd424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832dfa1065bd420cbbe64197b8c832ee99065ed320cafca2197d94432bb288657d510cbeaa2195d54432bf28065fa500caf4a0195f54032fca806579500cafca7a0df54f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837
  | 3 => 0x82b5f20001b1f459211c00001508c15398ed4ec1f8bc9590008f8409c00008710a1b93001e4789fc33035c1716d1c00000000054a9a02a8315a63f5401f04526b4001e01860018403e01c0006e2630602d4000e33c42742f8e43960000006e39274cf3000000cc5921a3000199302cf384c60000ff6027200020e5c81e0d82410006718002d0000000000000000000000000188001b4440a796c07520a000d8800204000940000000016d80054e0ccf694e4a2334000b400021000255000ae8ec91d530bfc001f71bea50001f25e29791f8000004b90ca1e3f64558f000000068002cd31c0008b8002f0000748000000009380042c28800000000991688002fe0012600000007c000004f648caa156626b48731cf20c82081ac14024b55ab2e64e95826000000ac0a6a495ca428aeafa5780307501c5dc42c000a933e000a40244b800000275000bbd019d00ce000a1291000000000000a8634000005babf40000002a7a8df93d170a415f13a0c2000e724632cc8c771833a22816580000046800000000000028000002ac002100000000000015a238001d43f2bac9c800146c51940b30004cc000191c2000000000006b0c78ec222000000e700079d502331305459914300062000073010ad996a15120bc83b30e2e2060613110005481a11f4c2c08df1db0b0b6590121000000b31a0084c49832f65ce570780cc49aa650009b0000005828518000158a135c4614d3a6b4bea20c880000099d141194a40000000040a8906493655c7051b169112b18c208a0000000000000078c0019e65e0002d30b24c0f07d2c04b0c0ca62c708c450e19f33285dc000855e0a300001e0de000001bd0000017d8001824d0779f50000a8001ff1165f82500b008001470c5262b41160bb22606c108bc46a0ec3dafe3ba0007c9471bc8498da1838e4fc6504e0ac3cc29a443323d8680e22d85895d9073024a8b80c44a6440b79891fc7d841a8147485c3682c43a83183a4e1ac19400000652c5c1c2ca4e29b88489345436c1fab817282c25aac15e2c4001372827304f0f80006ec24aa3408094d280013e354000800002fc002ab0006a98b07d0000018695a4427493c0fc64c1c93300007486d7c2f300033d1802853809c000e83b0b84690a80146c9982861e8000080910009f40028300096cef9385f87550529522c43d3ca3b0000bcaf014314bd04b86935c299459ba3dc088f280052e8bc000005be460002a800004400272000a1c961af4d28e1522d72c0000cd000256000c996b61e4313a16844c6918c92052c8ac11b2243e5d1578000c84006c950000001670401b01e8a2aa10000040100080201a0140480a00a00c0f0100040000280900000007800000000018010020500000301e018008080160000200200601000009014004008120060480180100407c0
  | 4 => 0x2f08d64a91556b1f138c554917a02e62cbe0513947f4adaa95b848911800000000000a52640015fa4a0f800113ac51e423cc619549e0015b8000004d51cade00015c000630002c8cb96425291c0023c00053d4980016ea24ce91e366c1103000202448e32e000041146a9f4645ec9e10d0d6000a59401180015932c0a4bb5169f819c00147963000264002480000000026c000b08268000000004d00036a000d327a2be844282775d8cacf48f74c4000758000d892d049b84d4175219cd0004956d1762fa0494dad41580a52827f4b29080029d18cb98000e52486899515525e6d8550cb0ee648099824da6ad6b0704a8000000006148945b1300e80c97500017a8dd5e80048000141000128808000680004f95a000000470a9800000b200783930c018001eb566114d40d341e61c001fa0008d0de0441747c4f42e9000000000006340017b80063a000e21ec000c84491d71a85b80011b0000000b2c41ea784ac26f598000d08000002b800000554420438203fc218ed0881bac3024167292a68b90953c8bd51e8c72881650d1de3ac09803a5d3de0745f15728c00c0699b0b85d574009000834000000003ec00265000000000004e095c2086007a0001b8a700000000222000a88522a6000000410000008c40000029477171800000c712d03521c10c388a136e1a8689a94f81fd6aa8a12c000b2b100005851700027600903800000ccc001733207153f30909e16c6416a1b4ae561
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x530823e64948208f592520823d65d0820c794f420831d53d08208fd95420831e5350820c754d420825e63944209758e51083365494420cd55251083565394420d554e51083566394420d558e51083374294420cd50a51083365454420cd55151083565354420d554d51083566354420d558d51083374254420cd509510825f65cc42097597310831e54cc420c7553310835651cc420d5547310825f654c42097595310831e544c420c75513108356514c420d5545310836551c8020d654e200837151880209bd95200836551480209ed9520083595348020ea509200837151480209798f54c425d63d53109798c54c425d63153109b98854c426d62153108fd9153c423c6454f10c7d9153c431c6454f109798f52c425d63d4b108f99252c423d6494b108f99052c423d6414b109798c52c425d6314b10c794f42c431d53d0b10c794d42c431d5350b10cb94942c432d5250b10d554e21c43555348710e950921c425e63d52109758f548423e64d4e108f593538423e6494a108f592528425f6354a109718d528423e6414a108f590528425e6314a109758c528425e63d51109758f544431e63d5110c758f544423d62d51108f992544423e65151108f588544433960151108f992534423d6494d108fd91534423c6454d109bd89534426c6254d108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d09108f995424423c6550910c7d53314431c54cc510c7d51314431c544c5109d19521443a54248510ce15240442786550110bc18540442786548110f8485204425e63d50109758f540426e62d50109b58b540423d65950108f58a540423f62550108f990540425e63150109758c540426e62150109b588540427a60150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530425f6154c1097585530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48108f992520423d64948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520432e5454810cb551520434e5354810d354d520432e6454810cb591520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d52508109798e510425d639441097597310431e54cc410c7553310434e52cc410d354b310425f654c410c7951310431d544c410d3949310434d524c410d954b10042796584010ce552100436952840109dd95100436552440109ed9510043395444010da54910043d13144010
  | 1 => 0x87555348421ce95250087395494021d694e50087595394021ced0a50087394294021d6cc650087593194021ce95150087395454021d694d50087595354021ced0950087394254021d6cc550087593154021dac8550087722154021da48550087712154021cb54b42d029c6350b409798e51d025d639474097586539025f6154e40c794f429031d53d0a40c794d429031d5350a40cb549429025e63946409758e519031e5390640c794c41902ad6210640ae580419025f65cc64097597319025f654c64097595319031e53d0240ae982435029c6350940cbd4942502b860509409798c515025d63145409b988515026d62145408f9974150357514c540d5145315029e639014097d8d521025c6354840cb54b42102b960d08409798e511025d63944408f59641102ad6210440ae5804110356514c440d5545311023f65500409ed95401027661d53309d58754cc23e6494b308f59252cc35551cc730a719131cc23d62952308fd89548c23e6494a308f592528c23f65d0a308f597428c23f6550a308f595428c31e548ca30c7950328c2d5610ca30b6580328c31e54cc630c7553318c31e544c630c7551318c355514c630c7953308c26e62951309b58a544c25e65d0d30b6983434c23e64149308f590524c27661149309d584524c32f5250930cb149424c25e65cc930a7191314c357514c530b6181314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e64948308f592520c32e5250830cb549420c25d658c830b5584320c2d9600c8308fd91510c23c6454430d5547310c2d960cc4308f992500c23d649403097d95300c27b654c03097d8d54c825c6355320c7d8d54c831c63553208f99353c823d64d4f208f99053c823d6414f209d98453c82756114f209798e51c825d6394720c795331c831d54cc720c795131c831d544c720d594531c8355514c720cb55321c832d5448720f14c521c825e63d52209758f548823e64d4e208f593538825e63946209758e518823f64546208f191518825e63951209758e544825f63551209718d544827761551209d185544823e64d4d208f593534831e64d4d20c7593534825d61d4d209798e534825e6514d209758453483596014d20c7d4f424831c53d0920c7d4d424831c53509208f990514823d64145209798c514825d631452097997314825c65cc52097995314825c654c520f14c52148358538c1209e19530482e8624c1209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530825d6194c20c7951530831d5454c2097d85530823e6414c208f590530825e6314c209d98453082756114c209e98
  | 2 => 0x640c931c7150324c6d6610c931b6980324c6d9600c931a758b544c69e6495131b5586544c6d76155131a7994544c71e6515131a7588544c69e6494931a7592524c71c5494931b5586524c69f6454931a7191524c6d76154931b6d81524c6d86054931a7990524c69d6414931c7150524c6da6014931b6580524c69e65d0931a7197424c69d6490931b5986424c6d5619093197d95424c65c6550931c7d95424c69e6550931a7195424c71c655093187195424c78f6250931a7990424c6d66110931b5584424c71f54d4531c7153514c79754d4531e5153514c6d562d4531e5d0b514c79542d453197996414c65e6510531b3988414c6cd6210531e5504414c6da6010531b6580414c71c54d4131a7992504c69d6494131a7d91504c69c6454131c7151504c6cf6254131b3189504c75950141319798f540c65e63150319b988540c66d62150319e980540c67960150318f992520c63d6494831c794f420c71e5350831cb949420c72d525083197d95310c677654c431d594d310c72e629532197d8d54c865c6355321c7d8d54c871c63553218f99353c863d64d4f218f99053c863d6414f219e98053c86796014f21cb95142c86af6550b21cbd9542c878f6350b21e318d42c871e54cc721c755331c878d42cc721c795131c871d544c721e350931c865f63543219718d50c865e63d52219758f548865e63152219758c548867a60152219e58054887566194e218fd91538863c6454e21c7d91538871c6454e21c794f428871d53d0a21c794d428871d5350a21d594d31886d7654c621d5d953188797644c621e51913188797424c621e5509318863f64542218f191508865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e18153486ad64909219b195424872f6550921cb195424878f6350921e318d42487a76150921e9185424878d42cc521b558e31487a5428c521e35093148674654c521e95093148757654c521d51953148797644c521e519131487c7624c521f11893148797424c521f19093148795424c521f15093148785424c521e950b21487c531885218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219b988540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c218f990530863d6414c219798c53086766114c219e98053086796014c218f992520863d64948218f597420871e53d0821c754f420863f6550821c794d420871d5350821cb949420865e63944219758e510865d65cc421c7953310871d54cc42197d95310871e544c421c75513108756514c421cb553210875553884219bd95210872d54484219dd95210
  | 3 => 0xd42a798e5350aad6294d42abd895350a9e6514d42c79945350a9d6114d42c7d4f5250b1c53d4942e3d4f5250b8c53d4942ab5875250a9e6394542a758e5150b1c5394542a7d8d5150a9c6354542aed815150ab86054542a798c5150a9d6314542c714c5150aba6014542ae5805150b1c53d4142a798e5050a9d6394142a7d8d5050a9c6354142c714d5050ab76154142ad1855050b3950141428fd954210a6f6550842cb9514210a5e63944429758e5110a3f64547328f19151cca3e64943328f59250ccb1f6355232c7550438ca7a60951329e582544ca5f63551329d987540ca7561d50329e983540ca7960d50328f596540cb1c63550328f990540ca7661150329d584540ca7a60150329e580540cb1d54d0c3297594430cacd6210c328f992520ca3d64948328f597420ca3f655083297d95320cb8d424c8329bd95320cb365494432cd552510cb374294432cd50a510cb365454432cd551510cb566354432d5d0d510cb544354432cdd09510cb354254432d5cc9510cb553254432ce952500cb395494032dc946500cb715194032ced0a500cb394294032ce951500cb395454032dc945500cb715154032d6d0d500cb584354032ced09500cb394254032d6cc9500cb59325403297d8d52d065c6354b41cb54b42d065e63943419758e50d071d5310e41c794f429071d53d0a41a718d429071e5350a41c754d429072e5250a41cb549429072f5250941c754e43106b56110c41d394e521074d5394841d394d521074d5354841cb991521072e4354841cb10d521071e53d0841c754f421072d52d0841a718d421071e5350841c754d421072e5250841cb54b411063f6550441cb54941106776550441d694e50107595394041da94a50107695294041ced0a50107394294041d694d50107595354041da94950107695254041ce90d50107384354041ced0950107394254041ced05501073941540419e98354cc67960d53318f99252cc63d6494b31a799232cc69d648cb31a799032cc69d640cb31b698032cc6d9600cb318f99250cc63d6494331b558754cc6da60d5331b658354cc6d56115331b558752cc69e6494b31a759252cc69e6414b31a759052cc6d56114b31b698052cc6d96014b3197d9542cc65c6550b31c7d9542cc71c6550b31e3d8942cc6ce6210731b358841cc6da6010731b658041cc69e64d4331a759350cc69e6494331a759250cc75950143319b988548c66d62152319e980548c67960152318f992528c63d6494a31cb949428c72d5250a31c758f544c63d62d51318f992544c63e6515131c758c544c63d621513197997434c71c5490d3197195434c71f5410d318f990524c63d64149319e980524c67960149318f997424c63c65d09318f995424c63c6550931a7992324c69d648c931c7152324c6d6618c931a7990324c69d
  | 4 => 0x1a0afe45a5e581adb60c7e86983c2ee16d342964fea00b91111505118f9cd2f06909d2e64d4841858535d454ca1a7a24c9dd45ac5692d64639cb5aaa843e18534ca1803a220004d8b328841c008898775362c05911c684810ee15f3467ddab8831c8089a79a165a3b406102088c858b2311ce5004c9084b0350412da6563d12f2a900073d929c40c29cc6da43576944508cc5b877ccf84910213c8a24800024d24a1a000b942a2bf08ec5dbdad463244174917596a7cd8213046754f4b700004ec0003d28a9f5140000de8013e2633bc1cc1d1f06fa0009f127000adc3d0166966e40019a000d14fcb6356698851000000a30a7aff564aa14d0b96dcabc5d91e37c0008e8005b22811a8b1000b7c3ca7505a1a4bf9f82706a88502b666484fe0c46accd58493c6ca3c4ce2ae5a6a800022c56a00000327262ae0ab12a0fcb0c002a65940002f8004020006f33c000000e1b44000b352a0000003585636c664001649ac61455536afb0006cc0a000000000fdb780c80017c90b3c84cc370e66a664c522414765859c80026e9e0df969000a797190144eca16b2e8190a40d5b4c554384aca5b02ec14992f4000bcc00000000a05b22c72fc4351e2a41e00252c9ed2904c0202ce2a089489282674da4000000010140901380001a104010080020680200c01e010000320420180000000004c0000401e0700f00c0800700400101e0000102101e00c030090040040102b00e0000000b00c07008001012010008020000000880000e03c000240160000100000004c03807002010030000020041400800002c0081200a038000060000100081700000c07003002030048090000000e80000201000000006010008030000080100002401c0000b00c0040380a0080180200000201c000000140140200a00602c0000300a024000110160000d006016040008050040000000b0060440100000a04c0080b0000200080300800c0100d00e008008050000600c80c00c0200b80001a07c008000040000300500001c0b8030000580000000a000138010180100101101a00c0200900c04805800000080020000020000180405600c120000020040000c00001003000032008000020020000a8000020b00080000c078158060120040200101e0000c8000060000581001209c040020000000100000000400805022000048050060040100d00c1c80001900607400005024008170078fd954310e5f6550c439798e51d0a5d63947429798e50d0a5d6394342ab58b53d0aba60d4f42ae58353d0aad6214f42a798e51d0a9d6394742a798c51d0a9d6314742ae98051d0ab96014742a798f50d0a9d63d4342a798e50d0a9d6394342ce54050d0a5e63946429758e5190a5d61d4d42975845350b1c53d0d42c7d4c4350a5e63145429758c5150a7a60145429e5805150a9d61d4
  | 5 => 0xd48dc5a24616222318c69d2b00006660cf40190003d4000312d862c6cb106aade42a81e416c394e00e6de045893155da33443b1334a995b991549caf85c0000009c8228cf000d28443465ea2d104b0d1f0d1c1080d3c0080c7000000d457e86b0c0495971c5000000f3206000104003140c60000009a4d60000029d0003b0ff8f3464230dda5a000000000c94d81447db7411a340cd87b2ea010040574bab212e03748ca3978952568bb14218c43843cbd96717c900f19eb0ca7b97120c310d49a7120002068152bd1a29b8570b700c000848004980013a0003900280a9233c4df0003766b4328ac2ba522a3c38b543e82500035c0000d9b51000006292582e100000001d0000c3c44a9917e6808d0fd640659451d316c3547d36206a5a08f94c1824e4550ea4de8a4ab91b15299845974052618000003c25d8ce85e5c20005384d000c743ab363acdb4470005de0000014627e6d5b3989000000001db18400092000284648beb3854a149088702505b99323a2829483608f4a0d6c4bb683e61f52386a32e6b56104e000c050a2f00da00067119000dacec3404f20edaf180662000001ca000d758209c5c07f4059d43b2d20ff226060a150b2031301c865b2a63814097b3e1fc97d2783467a8c0e495a4fc854833083e2131090121462e81c000456b7400024618ae4002970f091400096000188001ef0009d8e625538cdc4000461dc1082e00033285c001af60e2d4000000d06457922125c8dda6859000360fa9165980f84a9b414c5cc9a0565bc0bcb68df3e4550dd20241a4b47b8eb000c60000002c699c00271180c782e8e03d8d85bd269036a8c000e30002ac000c3000001af80037a650079a85805ad0e8e2000070000002c8c90002342440000003f094000000c5000a4da80000308e4821c105800143800000000000f900026da1800000001630000000006d00027a000dc1ce54461c94b2f644a25100ff0004b00014b56010c0015d2c400158afc00000119aad43c910e92380500004800065200000000660b600020831ead8a39c735c295560f66ea5941399e2a2814748000ec654ada942d47d89a9076b0928002e46341fd690e552a2cc0001317a0000037747c4ac001c200040c00067364b5c00000000be80285a2c00000eaf74a6160082f60006d8a70746360012100010a534490004c05291eaab04a211679dd2bc0c91533f00086d079714ae000330002e027d3d8003b407cf51bc1e475cdba194e02f0d890562200c7e2bc000b9cb7a363ce3bc1333b530cd1608004c2cdd3204b1ba524c0800072661b910e506218578001a4828e00ad45c87db30003208611204830463596292646689268e800035d7c0006c081ce88915dc27546a3f13ca9d8110c3ca8bc002d06005e8ae2eb114000001840005f
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xf0c958480082018001f088ea1869a800006000b800002198000000010971c859792801b800011870003110a930021001c0e1e801a000a16801d000001960400209019079395009e0d0f949d98811f838b0d899b09121402850c000a000050e0638001160000300347023c84200a2ae2298a2a1618535805150b0a298c2a82854c1c55014142a8ae421aa219705424c9510caa4b9086a8065c25093254032a4ae221aa420c957118d4210698b8886a8083461cd425404183aec2a06498d0d72150324c70c2a2c019263435c85414931c30a8b00a498c1e75995424c742b128220a63a45056010531c18a8312a098d4872540504c60e3b2a898e43231d9424c721838eca9a8510c94765093188706328c6a1243615c46350921b0ae630a8490e846318542486d0b80c2a1243231d9424c521948eca126290e146519131486c2b90c898a43615d0624c521d08c83126290dc17018931486c2ba48498a43251d9424c521988eca126290e877650931486c33b28498a43611d9424c521d08eca126290c8476509314868ab8ca620c818394d6210640c34a6b00832054572145315022ab88c6a9081435ca540ca30c2ca8b08651861a54580328c292b88a4a12610b5c86454430838ecaa26390705544c521c820f3b6a6a1241385c4624c120e12a6a12401072142545200820e3b2a6a1621c154d424871083cedaa262884e1721854044388aa26288021d05493144010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x38c02004a001a1424001b0eb280019063a118114d6014542911811cd4254041a0982151600c931a09821516014931c04655c46350921c80635c06150921c04655c8644c521c80645c0624c521886869d9424c521a058194d6210640a118194d6010640a0582951610ca30a0982951600ca309048755131487209048754d4248710
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 58)*7) 7
  | 5 => packedAt s5K5 (25143+((h/273+packedAt s5K5 (22140+(h % 273)*11) 11) % 1083)*11) 11
  | 4 => packedAt s5K4 (37250+((h/298+packedAt s5K4 (33972+(h % 298)*11) 11) % 1073)*11) 11
  | 3 => packedAt s5K3 (3486+((h/22+packedAt s5K3 (3332+(h % 22)*7) 7) % 90)*8) 8
  | 2 => packedAt s5K2 (925+((h/5+packedAt s5K2 (900+(h % 5)*5) 5) % 22)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc3f87f8f0f8ff1f8f1e3e3f06383f1fe1dc4cf
  | 1 => 0xfc7f8ffff00ffe3f01fc7c7ffc03fe1e6278f3
  | 2 => 0x7ff00ffff1ffc7fe007f807ffc7fe1838f3c
  | 3 => 0xff80000ffffe0007ffff80007fff8001fc0fc0
  | 4 => 0xfffffff000000007ffffffff80000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x580a21112214a20030a0a092208890d40cc445
  | 1 => 0x81110202012040410044042144112408201892
  | 2 => 0x222004244401000a4200490409204900830128
  | 3 => 0x9056b48a908649595690009725a044d740ec0
  | 4 => 0x32464c00ce4d8926e992724e00600991dbe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeecf8e8feecf8e8feecf8e8feecf8e8feecf8e8feecf8e8feecf8e8feecf8e8feecf8e8feecf8e8feecf8e8feecf8e8feecf8e8feecf8e8feecf8e8feecf8e8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36320
namespace PEqualNP.Outside.L_meta_36320
open PEqualNP.Outside.L_meta_36320.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x24719000c6244e816804478a1d00bd906005892b34fd4000441f2e4cdc505582079778e4f8474000a3683439b4a84a9100f40335401b0000d401c76000290001c0b6000000624c01811000800104040821400b800004a031228900017fd5005fe54017f55005fc5401ffd4c07fe5301ff54c07fc53017fd0c05fe43017f50c05fc4300ffd48037f5200ff94803fd5200df54803fc5200ffd0803bf4200ff90803fd4200ef50803fc4200ffcc803fe3200ff4c803fc3201ffd4407fe5101ff54407fc51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc3100ffc8403fe2100ff48403fc2101ffd4007fe5001ff54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200cff1951001df8ca880337c65440073e32a200bffd911005dfec888003bf64440015fb22200bff99110015fcc88802ffd64440177eb22200bff19110015f8c88802fbc64440055e322200bffd511005ffca88802ffd5444017fe2a22000ffd8d10005fec688003fe63440137f31a2000ff58d10005fac688003fc63440137e31a200cffd4d10067fca688033fd5344019fe29a200bffd0d1005ffc868802ffd4344017fe21a200affd8910055fec48802bfe62440037f312200aff58910055fac48802bfc62440037e312200affd4910056fea48802bfe5244015fea92200adf54910057f8a48802bff4244015dfa12200aff90910057fa848802bbd4244015fe212200affcc910057fc648802bfd3244015fe192200cffd4510027fca288033f65144019fea8a200cfd54510027f8a28802fff4144009ff20a200bff50510027f88288003ff3144009ff18a2000ff4c510027f8628802bff2144009ff10a200afd88510057fa428802bf52144009fe10a200cffd411002ffca088033fd504400bfe282200bffd011002ffc808802ffa4044017fea02200bfe5011002ff88088003ff304400bff1822000ff4c11002ff8608802bff204400bff102200afe88110057fa408802bf9204400bfe1022004ffc4110027f62088017fe104400bfb0822005ffd941002dfeca08017fe65040077f3282005df9941001cfcca08017fd65040117eb282005df59410004faca08017fc650400b7e3282005ffd901002dfec808017fe64040057f3202005ef990100157cc808017fd640400f7eb202005ef590100057ac808017fc640400b7e3202007ffd501003ffca80801ffd540400ffe2a02005ffd8c1002dfec608017fe63040137f3182005f798c10005bcc608017fd63040017eb182005f758c10005bac608017fc630400b7e3182008ffd4c10047fca608023fd5304011fe2982007ffd0c1003ffc860801ffd430400ffe2182005ffd881002dfec408017fe62040037f3102005fb9881000ddcc408017fd620400d7eb102005fb58810005dac408017fc620400b7e3102006ffd4810036fea40801bfe520400dfea902006df54810037f8a40801bff420400ddfa102006ff90810037fa840801bbd420400dfe2102006ffcc810037fc640801bfd320400dfe1902004bf98410027fea208013fe5104009fea882004ff14410027fe8208013fe4104009fea082004ff10410027fe6208013fe3104009fe9882004ff0c410027fe4208013fe2104009fe9082004ff0841002dfcc008017ff500400bff2802005ff5401002ff8a008017ff400400bff2002005ff5001002ff88008017ff300400bff1802005ff4c01002ff86008017ff200400bff1002005ff4801002ff84008017ff100400bfb8802005ff8401002ff42008017fd100400bfa8802004fe44010
  | 1 => 0x7fd500c00bfe2806005ffd003002ffc8018017fd400c00bfe2006005ffcc03002fbe6018017fe300c00bfd1806005ff4c03002fba6018027f9300c00bff9006005ff8803002ffa4018017fc200c009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2012bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98800afe64c4009feb262011bf59310027f8c988012fc64c4023ffaa62011ff9531008ffaa988047fc54c4009ffb1e2004bfd8f10027fcc788026fe63c4009feb1e2000bf58f10027f8c788012fc63c4025ffa9e2012ff94f10097faa78804bfc53c4023ffa1e2011ff90f1008ffa8788047fc43c4009ffb162004bfd8b10027fcc588006fe62c4009feb162010bf58b10027f8c588012fc62c4021ffa962010dfd4b10087fca588043fd52c4021bea962010ff14b10087fe8588043bf42c4021ff2162010ff50b100877a8588043fc42c4021ff9962010ff8cb10087fa6588043fc32c4009ffa8e2004ff94710027eca388013fd51c4025faa8e2004ff14710027fe8388013fe41c4009fea0e2004ff10710027fe6388013fe31c4009fe98e2004ff0c710027fe4388013fe21c4009fb10e2004ff48710087ea4388013fc21c4025ffa862005ff94310097faa188017fc50c4023ffa062005ff9031008ffa8188017fc40c4001ff9862005ff8c310007fa6188017fc30c4021ff9062005ff88310087fa4188017fc20c400bffb2c2005bfd961002ffccb0800efe658400bfeb2c200fbf5961002ff8cb08016fc658400bffb242005bfd921002ffcc90800afe648400bfeb24200ebf5921002ff8c908016fc648401dffaa4200eff95210077faa90803bfc548400bffb1c2005bfd8e1002ffcc708026fe638400bfeb1c2000bf58e1002ff8c708016fc638401fffa9c200fff94e1007ffaa70803ffc538401dffa1c200eff90e10077fa870803bfc438400bffb142005bfd8a1002ffcc508006fe628400bfeb14200dbf58a1002ff8c508016fc628401bffa94200ddfd4a1006ffca508037fd528401bbea94200dff14a1006ffe8508037bf428401bff214200dff50a1006f7a8508037fc428401bff994200dff8ca1006ffa6508037fc32840157eb0c200fffd4610027fca30803ffd5184009fe28c200effd0610027fc830803bfd4184009fe20c2000ffcc610027fc6308003fd3184009fe18c200dffc8610027fc4308037fd2184009fe10c2005bf9821002ffea108017fe508400bfea842005ff1421002ffe8108017fe408400bfd2042005ff50210077f28108017fc408400bff9842005ff8c21002ffa6108017fc308400bff9042005ff8821002ff44108017fd208401bfc9042005ff0821002ffe2108017f71084009fd884200cffd9510065feca880037f65440013fb2a200cff9951001dfcca88033fd65440197eb
  | 2 => 0x3002ffcc318012fe618c00bfeb0c6000bf5863002ff8c31806fff518c037ff28c601bff546300dff8a31806bff418c035ff20c601aff506300d7f88318027ff318c001ff18c6000ff4c63004ff86318067ff218c033ff10c6019ff486300cff84318016fe608c00bffa846005ff9423002ffaa118017fc508c00bffa046005ff9023002ffa8118017fc408c00bff9846005f7cc23004ff66118017ff208c00bff1046005fe8823002ffa4118067f9208c00bfe1046018ffd95300c5feca980037f654c0013fb2a6018ff9953001dfcca98063fd654c0317eb2a6018ff1953001df8ca980637c654c0073e32a6017ffd91300bdfec89805ffe644c0057f3226017ff591300bdfac89805ffc644c0057e3226017ffd51300bffca89805ffd544c02ffe2a26018ffd4d3004ffca698063de534c031fea9a6018f754d3004ff8a69805fff434c02fefa1a6009ff90d300bffa8698027fc434c02fee21a6016ffd89300b5fec49805bfe624c0037f3126016ff589300b5fac49805bfc624c0037e3126016ffd49300b6fea49805bfe524c02dfea926016df549300b7f8a49805bff424c02ddfa126016ff909300b7fa849805bbd424c02dfe2126009ffcc9300b7be649805bfe324c02dfe9926016f74c93004ff86498003ff614c0017fb0a6000ff98530007fac298003fc614c0097e30a6018ffd45300c7fca298063fd514c031fe28a6017ffd05300bffc829805ffd414c02ffe20a6009ffcc530007be6298003fe314c001fe98a6000f74c53004ff8629805bff214c02dff10a6016ff485300b7f84298063ff504c00bff2826018ff5413002ff8a09805fff404c00bff2026017ff5013002ff88098027ff304c013fd9826005ff8c13002fbc609805bff204c00bff1026016fe881300b7fa409805bf9204c00bfe1026005ffd943002dfeca18017fe650c0077f3286005ff594300adfaca18017fc650c00b7e3286005ffd903002dfec818017fe640c0057f3206005ff590300a5fac818017fc640c00b7e3206014ffd50300a7fca818053fd540c029fe2a06009bf98c3004ffea618027fe530c013fea986009ff14c3004ffe8618027fe430c013fea186009ff10c3002ffec418016ff620c00bff3106001bf9883002ffac41804efd620c00bfe3106005bf1883009ffea41804f7f520c027ff2906013ff5483009efaa41804ffc520c027ffa106013efd083009ffc841804ffd420c027dea106013ff1083004ffe6418027fe320c013fe9906009ff0c83002ffec218017fe610c0097f3086005ff58430005fac218017fc610c02bffa886015ff944300affaa218057fc510c029ffa086014ff904300a7fa8218053fc410c013ff9886009ff8c43004ffa6218027fc310c027ff9086013ff8843009ffa421804ffc210c00b7f3006005ffd403002ffca01801
  | 3 => 0xfa986209ff94c3104ffaa618827fc530c413ffa186209ff90c3104ffa8618827fc430c409ffb106204bfd8831027fcc418806fe620c409feb10621fbf58831027f8c418812fc620c43fffa90621fdfd48310fffca41887ffd520c43fbea90621fff148310fffe841887fbf420c43fff210621fff508310ff7a841887ffc420c413ff9906209ff8c83104ffa6418827fc320c4097f3086204ffd4431027fca218813fd510c409fe2886204ffd0431027fc8218813fd410c409fe2086204ffcc431027be6218813fe310c409fb1886204ff4c431027ba6218827f5310c409ff9086204ff88431027fa4218813fc210c409ffb006204ff9803102dfcc018813fd600c4017eb006204ff1803110ffea018887fe500c443fea806221ff14031107fe8018883fe400c441fea006220ff100310fffe401887ffe200c43ffe900621fff0803104ffecb98026ff65cc013ff32e6003bf9973004ffacb9807afd65cc013fe32e6009bf1973004ffec998026ff64cc013ff3266002bf9933004ffac998076fd64cc013fe3266009bf193300effea998077fe54cc03bfeaa6601dff1533004ffea798027fe53cc013ef29e6009ff54f300f7baa798027fc53cc013ffa1e601df7d0f3004ffc8798027fd43cc013fe21e6009f710f3004ffec598026ff62cc013ff3166001bf98b3004ffac598072fd62cc013fe3166001bf18b300e7fea5980737f52cc039ff296601cff54b300e6faa598073fc52cc039ffa16601cefd0b300e7fc8598073fd42cc039dea16601cff10b3004ffe6598027df32cc013ff1966009ff4cb300e7ba6598027fc32cc013ffb0e6009ff98730025fcc398027fd61cc0017eb0e6009ff187300f7fea39807bfe51cc03dfea8e601eff147300effe8398077fe41cc03bfea0e601dff1073004ffe6398027df31cc013ff18e6009ff4c730007ba6398027fc31cc039ff90e601cff887300e7fa4398073fc21cc03dffa866005ff943300f7faa198017fc50cc03bffa066005ff903300effa8198017fc40cc039ff9066005ff883300e7fa4198017fc20cc00bffb2c6005bfd963002ffccb1800efe658c00bfeb2c601bbf5963002ff8cb18016fc658c00bffb246005bfd923002ffcc91800afe648c00bdf3246002af9923002ffac91806afd648c00bdeb246000af5923002ff8c918016fc648c035ffaa4601aff952300d7faa91806bfc548c02d7eb1c601bffd4e3004ffca71806ffd538c013fe29c601affd0e3004ffc871806bfd438c013fe21c6005ffd8a3002dfec518017fe628c0037f3146005ff58a300cdfac518017fc628c00b7e3146019ffd4a300cefea518067fe528c033fea946019df54a300cff8a518067ff428c033dfa146019ff90a300cffa8518067bd428c033fe2146009ffcca300cffc6518067fd328c013fe1946005ffd86
  | 4 => 0x8abfc50cc453ffa066229ff9033114ffa81988a7fc40cc451ff9066228ff88331147fa41988a3fc20cc409ffb2c6204bfd9631027fccb1880efe658c409bf32c62039f99631027facb1889efd658c409beb2c62009f59631027f8cb18812fc658c409ffb246204bfd9231027fcc91880afe648c409feb246226bf59231027f8c918812fc648c44dffaa46226ff95231137faa91889bfc548c4457eb1c6227ffd4e3104ffca71889ffd538c413fe29c6226ffd0e3104ffc871889bfd438c413fe21c6204ffd8a31025fec518813fe628c4037f3146204ff58a3112dfac518813fc628c4097e3146225ffd4a3112efea518897fe528c44bfea946225df54a3112ff8a518897ff428c44bdfa146225ff90a3112ffa8518897bd428c44bfe2146209ffcca3112ffc6518897fd328c413fe1946204bf98631027fea318813fe518c409fea8c6204ff14631027fe8318813fe418c409fea0c6204ff10631027fe6318813df318c413fb98c6204ffc8631027fc4318813f6218c409fe90c6225fd48631027f84318813ff608c409ff3046205bf98231027fac118802fd608c409fe3046227ffd423113ffca11889ffd508c44ffe2846226ffd0231137fc811889bfd408c44dfe2046225ffc823112ffc4118897fd208c44bfe1046224ffd9531125feca98893fe654c4077f32a6224ff59531125faca98893fc654c4077e32a6223ffd913111dfec898803bf644c4015fb226223ff99131015fcc89888ffd644c4477eb226223ff19131015f8c89888fbc644c4055e3226223ffd513111ffca89888ffd544c447fe2a26224ffd4d31127bea698827fe534c449fea9a6209ff14d31127b8a69888fff434c413ff21a6223f790d3111ffa869888fdd434c413fe21a6222ffd8931115fec49888bfe624c4037f3126222ff58931115fac49888bfc624c4037e3126222ffd4931116fea49888bfe524c445fea926222df54931117f8a49888bff424c445dfa126222ff90931117fa849888bbd424c445fe2126209ffcc931117be649888bfe324c445fe9926222f74c93104ff86498893ff514c409ff28a6224ff54531027f8a29888fff414c409ff20a6223ff50531027f88298827ff314c413fb98a6204ff8c531027bc629888bff214c409ff10a6222fd88531117fa429888bf5214c409fe10a6200ffd8131005fec098803fe604c401feb026200ff1813102df8c098893ff504c449ff2826224ff54131127f8a09888fff404c447ff2026223ff5013111ff8809888bff204c445ff1026222ff48131117f84098813ff650c4097fb286204ff9943101dfcca18813fd650c4437eb286204ff19431025f8ca18813ff640c4097fb206204ff99031015fcc818813fd640c4417eb206204ff19031025f8c818883ff540c441ff2a06220ff55031107f8a818826fe630c413f
  | 5 => 0x4102c544d3af2af3c92f440404d28d46c2210263091f622c2792f30743a12e21b71bd26138f3d10b943a3a81ce0b73a434742234f03538431d30b3df4861dc23232f2d80be09802d1ec32e1d40af42a0fb21e34c30a08328a1e209514608012f30016440a3b843d44909131148f2f61b52ce1c70020080181082112a0500404201a074000080080040000905600008804028008000030020040000100009c0400000001407800004000020030460080f007046000000000200fc018010040040d001016038000000000000180300c0100080000c0540200c0140046380f0440080900100401c068000040041300501001c008500000080d8170000040200200a0880101300a0000980502400c010020020082d80900402c020000000040b80300e0101280402e1681b0070020180180102a0040000002a00800001008088028050120f80300d00200c048440000d80082900002c0100602002802003004000000000060000000105e0140886401a008020010360000300200a0180000a0000140201000200001005052058000000040100180102a0100400500c09c02806002000038150460000200900c0040000700420c0180a02c00801007018018000000180080080500200000803000054000160000981d800000000370010220140000000e00801800038008008000041c81285000000801001000098040000020280d022000044238000000840001400000c0a800000000000010060040001100a030198000060080202e0000000380c0680000c00800201011896006040188000100040080001c004000060060740500000607c098030100140080104808c008150020740388300001c008090280000000e0000080000701a054010000000640000c01e02c018000060080180400202c0480a00001c13ffb2e6209bfd973104ffccb9880efe65cc413feb2e622abf5973104ff8cb98826fc65cc413ffb266209bfd933104ffcc99880afe64cc413feb266229bf5933104ff8c998826fc64cc453ffaa66229ff9533114ffaa9988a7fc54cc413ffa9e622af7d4f3104ffca798827fd53cc413fe29e6209f714f3104ffe8798827fe43cc413ef21e6209ff50f3114fba8798827fc43cc413ffb166209bfd8b3104ffcc598806fe62cc413feb166228bf58b3104ff8c598806fc62cc451ffa966228dfd4b31147fca5988a3fd52cc451bea966228ff14b31147fe85988a3bf42cc451ff2166228ff50b311477a85988a3fc42cc413ff9966209f7ccb3104ffc6598827fd32cc451ee9966209ff0cb31157fea398813fe51cc455fea8e6204ff1473114ffe8398813fe41cc453fea0e6204ff10731147fe4398813fe21cc451fe90e6204ff0873104ffec198827fe60cc40b7f3066209ff58331005fac198827fc60cc455ffa86622aff94331157faa198
  | 6 => 0x133a212217a00032812c2261294030a04673292ba00042e26b04426e2ef16c20f21d24a2431b100017200024400041827e2a60060861c327409443736d0b63cb36147b47a02013827709205015335843127314544149c29b2e44212291c109c13936549d2a440c2ac0180b53a624d3dc23105807f3380dc06123c0ba0413672e137d1ed3e33f501941c1b418a44643239e2a232037408217404026645f25911f3273632bf3122541ae32135f03a43932609910d29e01443c0db3db4482823ca38d1c833135b0072a838721113b0002b411a2c43712d11120000d648409610b1f44130042ea3d43fe02c1c52e32b72303832401a01ac2bd21707d2360000880550001b80000000003820002bc2e73790000001a20003fd2d40f446223e37620c05d41a0d52d90c019037a41e0000000003de1b31f32f000041600024203312120b0e54203ee42c16718e00027000023a14208e11444c31b00002a39600025200000a45148300042f4253d300000019f06c00005300025738a0001e70000ce12a3c229148d2a51584340003620002e600000000008c3530000e225b3dd0750474430000004351bc00d29d1e635a29f00000010825c1d301c3ac0000000cd00000009d13107a1d00002dd26805a2514550b41e50001800110000000000002023fa0000e11a800000004e12e00027b0000313351cb0000001d248c25624c29741d3c102916d1e44280454571821e94561cf3992063722ed02103745835c20140e41500f01e3462412a92cd2c61d137b01a22b1613a70701352390d804a0000b300000c2b50000b20fa15f05100046516900000000003003c03d2052ae14e0002634230000c40003c43f21e839d0681fe0780000000001871230002140d70001512c00000000000b109706a00000002429541710c1661c604308d4592000001fd06e00023b39f3a00c30280000001be2470591a142d13c1632e800039445a00000000000025338b04f0000003c80d00002de1020e43501ff0000843c30e30003b409008f1ba4601a31001911bf28e36a45c0f508a14c29800005715532d03428037f0000000792db18f0002601aa2df33a02b30f32c0cf01344503f00000000000000018d0a425d12713200043e0762d20001d74a003930e0000ee00014000015b3680364050003c74a145d0323bb2690000000002fb33f4530483e80f13b100038e22d02e10707203840b3b300844a0170000002ca0003bf0000e600022800026c2923f70000ab46d19a3a30ec18104b3541591de0641041a92190a200007e1d50003cd44728637e3e70a11ad20418449405b2882c83020f72081483483410ca3e02f80bb0873452f73d605c1242d51ee27d1431833912fa2c23b02450b827812d2b94742070a90813cc40f30806b16a0933132b246a3b91b220349336f1c2275492
  | 7 => 0x4501c43320a81c03061f13371b046924f0100e915a0c80000003ab0004952d64612e910a2e54723752e02b831849a21246838535500026d4823d548a06f40700003b02f1a62270000000001ca48504949b2201a444e09b0c734b00000009e2491db47845e15d43619215c0000002ec2243100660671570000000c93ef00000014a3f42ff0000000001f500000120d0000690000602163bc1af0004403b232228106d33b43039300038842631c1710002653170e713d33d4643b60d22584713232c100010500000019b4004062720ac0d42c700013e3ba3be0890001df0a32ab1d648e36c2233fb0000fd4381b938c29007c2aa0033d237c3c00d13523ce3030aa1782f90003ec1850003c61940fe2da00046b14d21a0000000d30233f80b016f0ae1dd00007b3660000a600000030d0f91e10f33d74750151d90bc1ab4521e300030c1ef3010000e80000003fc0000001f20bf3050711883d81972fd1332d300030720a00031500026f1110e00002be15040d31a0000000cb16000047334d1f71f83eb2d000022a3c528b47700046f0000cc47918648b06315444b19c48700042431e31f0000003bd17e2833ad3811653ff34202714117626701b09f06229314926414438016e11800000039c3394421250002f21fc0004903b510f24817c2840ed01d0de40834915204231434315e2f11621a70df27f32518b49146622f0ad32414f0f039011e31943f1fb2711e03300a500238924b3691cc3401282251d847e00b04629c0dd1930001370003f90c230435910113a2cb0fc21b2ee47f1751a52fc07300e3b739b1683ea1964761fa0000000f60851da0220560001b640100036b4274023e211600046e00516b1473d001f21c3f63ed1f92fe0c110e0772d70000a72c92a32181260f205e00029a20936044f0bd10625e11c0091030002c341426a27600035701233322e2960ff0000000000003e612000012b1f02384440003e90ef0c621f39817900000000000004c0001950003a545b17015600031617b2cc2b34703702ad0540002b00002873cf05f06511525f2372f523f3e13da49e2bb47c39541b2cf0c539a10933c17741249823548937836e4963aa27c3f00da33639717348049f14b47d00013017d3e51eb35620e1361892a149749929435e0002620162b128529900041100013f18c3344810001c909a27a19d00038642b0002a724600032a2500d91981ea28928c43b34e34a08b32b2eb3d90000003443a92b63641bb3732101190000f843311019919e3513f325a4880000250000000003772150001342dc0000004190001173f105200023400000011d4633ae3e40eb03e42917f00023d00040911b0003920002a028f2222330ea35d45424e25541f0001cd00011333e2
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c1002cff7358c1002edf7358c10006df5358c10006de5358c10006dd5358c10006dc5358c10006df4358c10006de4358c10006dd4358c10006dc4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c100067f5258c100067d5258c10006bf4258c10006bd4258c10006df3258c10006de3258c10006dd3258c10006dc3258c10024ff7158c10024fe7158c10024fd7158c10024fc7158c10026de3158c10026dc3158c1002cff7058c1002cfe7058c1002cfd7058c1002cfc7058c1002ede3058c1002edc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c100065f5258c10006de5258c10006dd5258c100065d5258c10006dc5258c10006df4258c100069f4258c10006de4258c10006dd4258c100069d4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c10026de5158c10026dd5158c10026dc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c1002edf7058c1002ede7058c1002edd7058c1002edc7058c1002edf5058c1002ede5058c1002edd5058c1002edc5058c1002edf4058c1002ede4058c1002edd4058c1002edc4058c1002edf2058c1002ede2058c1002edd2058c1002edc2058c1002edf1058c1002ede1058c1002edd1058c1002edc1058c10006ef7558810006ee75588100066e7558810006ed75588100066d7558810006ec7558810006ef7458810006ee7458810006ae7458810006ed7458810006ad7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026ef5158810026ee5158810026ed5158810026ec5158810026ef4158810026ee4158810026ed4158810026ec4158810026ef3158810026ee3158810026ed3158810026ec315881002eef705881002eee705881002eed705881002eec705881002eef505881002eee505881002eed505881002eec505881002eef405881002eee405881002eed405881002eec405881002eef305881002eee305881002eed305881002eec305881002eef105881002ee7105881002eee105881002eea105881002eed105881002ee51058810026e9105881002eec1058810
  | 1 => 0x94100267e71594100267d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c215941002e7f705941002e7e705941002e7d705941002e7c705941002e7f405941002e7e405941002e7d405941002e7c405941002e7f305941002e7e305941002e7d305941002e7c305941002e7f205941002e7e205941002e7d205941002e7c205941002e7f105941002e77105941002e7e105941002e7d105941002e75105941002e7c1059410006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010004bf7259010006be7259010006bd7259010004bd7259010006bc7259010006bf52590100063f5259010006be5259010006bd52590100063d5259010006bc5259010006bf3259010006be3259010006bd3259010006bc3259010026bf7159010026be7159010026bd7159010026bc7159010026bf5159010026be5159010026bd5159010026bc5159010026bf3159010026be3159010026bd3159010026bc3159010026bf2159010026be2159010026bd2159010026bc215901002ebf705901002ebe705901002ebd705901002ebc705901002ebf505901002ebe505901002ebd505901002ebc505901002ebf305901002ebe305901002ebd305901002ebc305901002ebf205901002ebe205901002ebd205901002ebc205901002ebf105901002ebe105901002eba105901002ebd1059010026b9105901002ebc105901004edf7598c1004ede7598c1004edd7598c1004edc7598c1004edf7498c1004ede7498c1004edd7498c1004edc7498c10006df5498c10006de5498c10006dd5498c10006dc5498c1004edf7298c1004ede7298c1004edd7298c1004edc7298c10006df5298c100065f5298c10006de5298c10006dd5298c100065d5298c10006dc5298c10006df4298c100069f4298c10006de4298c10006dd4298c100069d4298c10006dc4298c10026df7198c10026de7198c10026dd7198c10026dc7198c10026df5198c10026de5198c10026dd5198c10026dc5198c10026df4198c10026de4198c10026dd4198c10026dc4198c10026df2198c10026de2198c10026dd2198c10026dc2198c1002edf7098c1002ede7098c1002edd7098c1002edc7098c1002edf5098c1002ede5098c1002edd5098c1002edc5098c1002edf4098c1002ede4098c1002edd4098c1002edc4098c1002edf2098c1002ede2098c1002edd2098c1002edc2098c1002edf1098c1002ede1098c1002edd1098c1002edc1098c10004ff7558c1001cfe7558c10004fd7558c1001cf
  | 2 => 0x4cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d100067f52d8d100067d52d8d10006bf42d8d10006bd42d8d10006de32d8d10006dc32d8d10024fe71d8d10024fc71d8d10006f621d8d10006f521d8d1002cfe70d8d1002cfc70d8d10006fa20d8d10006f920d8d100657e7598d100057d7598d100067f6598d100067c6598d1005dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d100057f7558d100657c7558d100067f6558d100067c6558d10005bf7458d1005dbc7458d10006bf6458d10006bc6458d10005ef7258d10055ec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d100067f5258d100067d5258d10006bf4258d10006bd4258d10006df3258d10006dd3258d10004ff7158d10006f77158d10006f62158d10006f52158d10004ff7058d10006fb7058d10006fa2058d10006f92058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d1004ede6318d10006dd6318d1002cfe76cc51002cfc76cc5100067f65cc5101567c65cc510006bf64cc51014ebc64cc510006df63cc51004edc63cc51002dfa70cc510005f970cc51002cfc764c5100067f654c5101267c654c510005bf744c51005dbc744c510006bf644c51011ebc644c510006df634c51004edc634c510005fb704c51002df8704c510027f0104c510024fe76cc110024fc76cc1100067f65cc1100f67c65cc110006bf64cc1100eebc64cc110006df63cc11004edc63cc110025f671cc110005f571cc11004cff764c110004fd764c110024fc764c1100057f754c1100657c754c1100067f654c1100c67c654c110006bf644c1100bebc644c110006df634c11004edc634c110005f7714c110025f4714c11002ff0104c1100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100047f72594100067e72594100067d72594100047d72594100067c72594100067f42594100063f42594100067e42594100067d42594100063d42594100067c42594100067f32594100067e32594100067d32594100067c32594100267f715
  | 3 => 0xf72d95100057d72d95100067f62d95100067e62d95100067d62d95100067c62d95100073f42d95100073d42d951016f7771d95100677471d95100077621d95100077521d95100077a40d95100077940d95100077a20d95100077920d95101777b10d951016f7610d951016f7410d95101777810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100047f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f42d95100063f42d95100067e42d95100067d42d95100063d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d951016e7f71d95101767e71d95100667d71d95101767c71d95100067f41d95101767e41d95100067d41d95101767c41d95101767e31d95101767c31d95100067f21d95101767e21d95100067d21d95101767c21d95101767f70d951016e7e70d95100667d70d951016e7c70d95100067f40d951016e7e40d95100067d40d951016e7c40d951016e7e30d951016e7c30d95100067f20d951016e7e20d95100067d20d951016e7c20d95101767f10d951016e7e10d95100667d10d951016e7c10d951005dbe76d911005ebe76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110005bf72d9110005bd72d9110006bf62d9110006be62d9110006bd62d9110006bc62d91100073f52d91100073d52d9110007b651d9110007b551d9110007b621d9110007b521d9110167bb70d911005fb870d9110007ba20d9110007b920d9110167bb10d911015fb610d911015fb410d9110167b810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110004bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d91100063f52d9110006be52d9110006bd52d91100063d52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d911015ebf71d9110166be71d911005ebd71d9110166bc71d9110006bf51d9110166be51d9110006bd51d9110166bc51d9110166be31d9110166bc31d9110006bf21d9110166be21d9110006bd21d9110166bc21d9110166bf70d911015ebe70d911005ebd70d911015ebc70d9110006bf50d911015ebe50d9110006bd50d911015ebc50d911015ebe30d911015ebc30d9110006bf20d911015ebe20d9110006bd20d911015ebc20d9110166bf10d911015ebe10d911005ebd10d911015ebc10d9110
  | 4 => 0xc53002df8704c53002cdc764c53019ddf754c53019ddd754c5300075f654c530126de654c530126dc654c5301975c654c5301265c654c5300079f744c5300bdde744c5300bddc744c53018f9c744c5300bd9c744c53018edf644c53018edd644c530185df724c530185dd724c53017edf624c53017edd624c53017f5f524c53017f5d524c53017f9f424c53017f9d424c53004ddf714c53004fd7714c530007d7614c530026de614c530026dc614c530007d4614c53017fd6214c53017fd5214c530007db704c53002dde704c53002ddc704c530007d8704c53004edf604c53004fdb604c53017fda204c53017fd9204c530004ff755843001cfe7558430004fd755843001cfc7558430004ff7458430006bf7458430004bf7458430014fe7458430004fd7458430014fc7458430006bc7458430014bc7458430004ff725843000cfe7258430004fd725843000cfc72584300067f52584300067d5258430006bf4258430006bd425843002ef77158430006f65158430006f55158430006f64158430006f5415843004ef7315843004ef43158430006f62158430006f5215843002cff705843002cfd705843002edf305843002edd305843002ef6105843002ef41058430004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10006bf7458f10004bf7458f10014fe7458f10004fd7458f10014fc7458f10006bc7458f10014bc7458f10026df7358f10006df5358f10006dc5358f10006de4358f10006dd4358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f100067f5258f100067d5258f10006bf4258f10006bd4258f10006df3258f10006dd3258f1002cfc7158f10026de3158f10026dc3158f10026f62158f10006f52158f1004ede63cc310006dd63cc310025f671cc310005f571cc31004cff764c3100057f754c3100957c754c31004ede634c310006dd634c310005f7714c310025f4714c310004ff7558e100067f7558e100047f7558e1001cfe7558e10004fd7558e1001cfc7558e100067c7558e1001c7c7558e10004ff7458e10014fe7458e10004fd7458e10014fc7458e1002edf7358e10006de5358e10006dd5358e10006df4358e10006dc4358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e100067f5258e100067d5258e10006bf4258e10006bd4258e10006df3258e10006dd3258e1002cfc7058e1002ede3058e1002edc3058e1002efa2058e10006f92058e1004ede63cc610006dd63cc61002dfa70cc610005f970cc61004cff764c610005bf744c610075bc744c61004ede634c610006dd634c610005fb704c61002df8704c6100657e76d95100667e76d951001c7e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100057
  | 5 => 0x67e64d95300067d64d95300067c64d95301cf5f73d95300c75c73d95300075f43d95300075c43d95300057f72d95300057d72d95300067f62d95300067e62d95300067d62d95300067c62d95300073f42d95300073d42d95300075f32d95300075d32d95301d77b30d95301cf5e30d95301cf5c30d95301d77830d95300077a20d95300077920d95300067f74d95300067e74d95300067d74d95300067c74d95301ce7f73d95301d67e73d95300c67d73d95301d67c73d95300067f43d95301d67e43d95300067d43d95301d67c43d95300067f72d95300047f72d95300067e72d95300067d72d95300047d72d95300067c72d95300067f42d95300063f42d95300067e42d95300067d42d95300063d42d95300067c42d95301d67f32d95300067e32d95300067d32d95301d67c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95301d67f31d95301d67c31d95300067f21d95300067e21d95300067d21d95300067c21d95301d67f70d95301ce7e70d95300c67d70d95301ce7c70d95300067f40d95301ce7e40d95300067d40d95301ce7c40d95301d67f30d95301ce7e30d95300c67d30d95301ce7c30d95300067f20d95301ce7e20d95300067d20d95301ce7c20d95301ce7e10d95301ce7c10d95300067f65d85300067c65d8530004ff75d853001cfe75d8530004fd75d853001cfc75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d8530004ff72d853000cfe72d8530004fd72d853000cfc72d85300067f52d85300067d52d8530006bf42d8530006bd42d8530006df32d8530006dd32d853002cfe70d853002cfc70d8530006fa20d8530006f920d85300c57e75985300057d75985300067f65985300067c6598530006f761985300057f75585300c57c75585300067f65585300067c6558530005bf74585300bdbc7458530005ef72585300b5ec72585300067f65185300067c6518530026f66118530006f56118530005de76cc53004ede76cc53004ddf75cc5301c5dd75cc5300075f65cc530156de65cc530156dc65cc5301bf5c65cc5301565c65cc5300bdde74cc53004ddc74cc5301b6df64cc5301b6dd64cc53004ddf72cc5301addd72cc5301a6df62cc5301a6dd62cc5301a75f52cc5301a75d52cc5301a79f42cc5301a79d42cc530026de61cc530026dc61cc53002dde70cc53002ddc70cc53004edf60cc53004fdb60cc5301a7da20cc5301a7d920cc53002cfe768c5300c57e758c5300057d758c5300067f658c53013e7c658c530185dd738c530006f7618c530026f4618c53002dfa708c530005f9708c53002cfc764c5300067f654c5301267c654c530005bf744c5300bdbc744c530006f7614c530026f4614c530005fb704
  | 6 => 0xa4058031006f9405803104efb305803104ef83058031006fa2058031006f92058031026fb1058031026f81058031004ff755873001cfe7558730004fd755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc745873002cfc7358730004ff725873000cfe7258730004fd725873000cfc72587300067f52587300067d5258730006bf4258730006bd425873004edf3258730006dd325873004ef7715873004ef7315873004ef43158730006f62158730006f5215873004ddf764c730006df764c7301fddf754c7301fddd754c730126de654c73004edc654c7300079f744c7300edde744c7300eddc744c7301f79c744c7300ed9c744c73004edf644c7301f6dd644c7301eddf724c7301eddd724c73004edf624c7301e6dd624c7301e75f524c7301e75d524c7301e79f424c7301e79d424c73004fd7714c730026de614c730026dc614c7301e7d6214c7301e7d5214c73002dde704c73002ddc704c730006bf7559230006be7559230006bd7559230006bc75592300d6bf73592301debe7359230006bd73592301debc7359230006bf53592301debe5359230006bd53592301debc5359230006bf7259230004bf7259230006be7259230006bd7259230004bd7259230006bc7259230006bf52592300063f5259230006be5259230006bd52592300063d5259230006bc52592301debf3259230006be3259230006bd32592301debc3259230006bf7159230006be7159230006bd7159230006bc7159230006bf5159230006be5159230006bd5159230006bc51592301debf31592301debc3159230006bf2159230006be2159230006bd2159230006bc215923002ebf705923002ebe705923002ebd705923002ebc705923002ebf505923002ebe505923002ebd505923002ebc505923002ebf305923002ebe305923002ebd305923002ebc305923002ebf205923002ebe205923002ebd205923002ebc205923002ebf105923002ebe105923002ebd105923002ebc1059230004ff755863001cfe7558630004fd755863001cfc7558630004ff7458630014fe7458630004fd7458630014fc7458630004ff725863000cfe7258630004fd725863000cfc72586300067f52586300067d5258630006bf4258630006bd425863002ef77158630006f65158630006f55158630006f62158630006f5215863002cfc705863002edf305863002edd305863002efa2058630006f9205863002ef6105863002ef410586300dd7e758c6300057d758c630136be648c630006bd648c630026f6618c630006f5618c63002dfa708c630005f9708c630024ff764c630005bf744c6300d5bc744c63011ebe644c630006bd644c630026f6614c630006f5614c630005fb704c63002df8704c6300c57e76d95300c67e76d953001c7e76d95300067f64d9530
  | 7 => 0x823100cfe7258231004fd725823100cfc72582310067f52582310067d5258231006bf4258231006bd4258231024fc7158231026df3158231026dd3158231026f62158231006f52158231026fb7058231006fa4058231006f94058231006fa2058231006f92058231026fb1058231026f8105823111dbe76d913111ebe76d9131014be76d9131006bf65d9131006be65d9131006bd65d9131006bc65d91312079f73d913111f9c73d91310079f53d91310079c53d9131005bf72d9131005bd72d9131006bf62d9131006be62d9131006bd62d9131006bc62d91310073f52d91310073d52d91310079f32d91310079d32d913120fb731d91312079e31d91312079c31d913120fb431d9131007b621d9131007b521d9131006bf75d9131006be75d9131006bd75d9131006bc75d9131206bf73d913120ebe73d913111ebd73d913120ebc73d9131006bf53d913120ebe53d9131006bd53d913120ebc53d9131006bf72d9131004bf72d9131006be72d9131006bd72d9131004bd72d9131006bc72d9131006bf52d91310063f52d9131006be52d9131006bd52d91310063d52d9131006bc52d913120ebf32d9131006be32d9131006bd32d913120ebc32d913120ebf71d9131206be71d913111ebd71d9131206bc71d9131006bf51d9131206be51d9131006bd51d9131206bc51d913120ebf31d9131206be31d913111ebd31d9131206bc31d9131006bf21d9131206be21d9131006bd21d9131206bc21d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d913120ebf30d913120ebc30d9131006bf20d9131006be20d9131006bd20d9131006bc20d9131206bf10d9131206bc10d9131006bf64d8131006bc64d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d8131004ff72d813100cfe72d8131004fd72d813100cfc72d81310067f52d81310067d52d8131006bf42d8131006bd42d8131006df32d8131006dd32d8131006f621d8131006f521d813111dbe7498131005bd7498131006bf6498131006bc6498131006fb60981310057f75581311257c7558131005bf745813111dbc7458131006bf6458131006bc6458131005ef7258131115ec7258131006bf6418131006bc641813102efa6018131006f96018131004ff75580310067f75580310047f755803101cfe7558031004fd755803101cfc75580310067c755803101c7c7558031004ff7458031014fe7458031004fd7458031014fc7458031004ff725803100cfe7258031004fd725803100cfc72580310067f52580310067d5258031006bf4258031006bd4258031026df3158031026dd3158031026fb7058031006fa5058031006f95058031006f
  | 8 => 0x40100080f0200140e0120000000000d036008090010000300580501405800003006084000010140040200200000410008038028000180000000501000200001819012004000000000180500000c0300480400e0ac0300001003c0680c00c0080483c0060000501100001c0080e01214000807018018060050000140204302e03409000018018000000020001780002400c0580302c05c0300a00c0400200f044008048010020040302201a0680280a000018008030000380080003800c0f80000000c5080002400c0080103e0500901d0040080a8020080000400100209c040040020040084c00e0000080400a004048000020041d00500600c0000301a00800000000000000000020100080500a00000004000004000170a40340901d03a000018010080200480200209c06000000000060000060080600802c02407800000024038470100a403004000004008050000100600000600004804006000010010040000780200606800003000010008040040180680300c004010010020d4010330040dc000040100400081200a008010080000280880000c098008000000840200001604c040000020000100a02200c0582700c01c05017000000050010040100004f0040300000d004ff755833101cfe7558331004fd755833101cfc7558331004ff7458331014fe7458331004fd7458331014fc7458331024fc7358331004ff725833100cfe7258331004fd725833100cfc72583310067f52583310067d5258331006bf4258331006bd425833104edf3258331006dd325833104efb705833104efb305833104ef83058331006fa2058331006f920583310067f74596310067e74596310067d74596310067c745963113e7f73596312167e73596310067d73596312167c73596310067f43596312167e43596310067d43596312167c43596310067f72596310047f72596310067e72596310067d72596310047d72596310067c72596310067f42596310063f42596310067e42596310067d42596310063d42596310067c42596312167f32596310067e32596310067d32596312167c32596310267f71596310267e71596310267d71596310267c71596310267f41596310267e41596310267d41596310267c41596310267f31596310267e31596310267d31596310267c31596310267f21596310267e21596310267d21596310267c21596310067f70596310067e70596310067d70596310067c70596310067f40596310067e40596310067d40596310067c40596312167f30596312167c30596310067f20596310067e20596310067d20596310067c20596310267f10596310267e10596310267d10596310267c1059631004ff755823101cfe7558231004fd755823101cfc7558231004ff7458231014fe7458231004fd7458231014fc7458231004ff725
  | 9 => 0x798000000000001080002b20000a30002101a506e1f30000179931d41548860000001bca45a618001c626e9d92c9acf9c715fa99800000158a0c19e8000001732af2b70119af2139850fa1ed1bb86a88400d87f22b269ac58ee1208690d31bb0ef8bf84da170160d68e8806a8a99800011a9d31ad18f8429f818d8cf09c22a08f9481c004c0001fa80000028c84c82819e0000b100011e2468000000000000002111de00007b8000c81ae0b4a6590596c14c0002348001ab8459068001110980000008000d81f79d70000a10948000000002b30e70000000cc00010e8002ab1072cb8b28000da1bf00020e8c480f80022d0d7a7a0000dc2742c3a868c185126f80015526328012824e20480624426d9322038002c21b6a7b2191229439c425d28d0001be0310ed1901028000001f395c08d0f910e0792d28002340fe0e202b84d228a2e93589d0000000e6a2315621d2d3a570e60fba9da1a9268b88408d58c609898c8802959d0290a1a0000000000ae8309840002770002308002128368b90000ad2008cb000260800000283a259cc10aaca97b80029f14d2421601aaa669c185d00002e26780000016a0f71e6ac522f216aa313901f114a689c209a198935000008a3c80ca24a8e21f800000000151ad5809800169049a5c28a28c27f1b91189a28562c69090362371e21eca42a6c8071f48c396ea1304b8002388079b093b81d2540489638d000000011b0001d4ad19f1a3a08a1938001dc22780021c1e980019516186f2030000f98f28939422a89ab0140d3a9700004f00000a9eb97980027d8001b59e08e28c6a0988c00000f0f20000000dfa981452662969398608880878658e481c90310f802066292085a929000c2174aac15e96c99d06ba3d018800038aa488c93f0f81218921a68808bb0db99c022a709e41a7a9c8b7a2c9419a9013a4980024727789e0e58e1819a6013e00001908300017c21980b2721dba3e293a5b06302a9ca0d08240120001cea4dacb02c847236a7580000016dabb00e8778000001570000168ca85506b0238000002ab9468000000002460000000001e915a8002592840f09040000000002b38180899250b08300001f111408f04e8002b61c6ad794b00012a1b38010010000200480100600402002004008000080360180280000a00002004002150000010120040001d00003c0e032008098010000000000200200e0000480001803c02000000000018000000040001700400001811000004030050100041c0000020a41c8030040240301a0640040300000002c0000601e018010040520240000300205c08806000004020020040340280400e00c000000040140580600a064018140240180480001e05c000080020040080601a03c0000100000402801000008170020041180300000001c1c001012048038030
  | 10 => 0x9f1a706c1ee0dea871449df0ed937a2e28519d87c116a9e960a8f8001360348001cd0ff9c90668002311752180bd80596b09994ca861cf19b2320689630111590cf8000c71558001a201d8002229cc8f41408f52c026f11da079a485b86ca290108cd201a599af84600000000013b000000000113a2f9709008ba06213280002887427b91c0569718490001d3a0d9fa18e83291c80000000000e20f8c11491838002acacd8299e62c78000001a397c8538271020bc236109abfa89148a1b92396aa06864827a0f0000c90530000001018ec1702a5abb94012306a0002d900024927680000020d04e18d14e26a1ac98980015a00000010c0d1a189c305b0eaa00024aca27e1762b4a7600001e9b28002142ce8000001da82f0000ab03ba748001de90b14b9061fe1b4869a739fd0d981512983a2b9157ad68000000001cb8001b703a8ca13e988981281875a558aa92580015200000017b0a6a6d074a2d973a7a9949340e989680002d99a133a551a61038962050c08eba7f84305eac609fa1c8e81ca9b9abd9c79612c30019f087d0ce0399910970891b19c5ad20a426285d87e0509a98ef0b995002ea12291867ab4145854004800130252a5f8ff1848210000aa1249b302c1f6012a6b04413a949a7800012b85c1db0c40c7803a359261e500000015405cac2a3c1271f88000000ae03b0000000f68002cf0000002070a88001eb1130000000978100000000932cca3781489f0d8a4b1381688000599010000850b800020e0001ea83d9b894a86400c1429bd2d713a16f9e28252888738dd84b0001220000091928ba8ad8000fb07d8fd85f0e90528eca2804f95d298887127a382ba847a912c115c8000001d61e80000000000000000221bc073241800264a4eab5136aa820c88686280b8000548000000002b598f0000411c50709979e7000297a6397927280000021780000006eabe0000000001c09b600024f0002c819c80017e0000f59cb0638a19ef9580002b18ac0a58611211fc12d9b525e92c0ea18a96494788b83921d8a2abd23b2690b325b962930a0b8a09d11100208a023d9d29758422531198001122a921e8001b79ae88aa85a451150cd8c9aa196212014718c04a1960028359a0acd1f690d8919ce12a91ba500be17dab9a71a58872a5199401b03409b9f2a0281a2a998a0a826211a1821ff28f1181d192c9ba94427c05a1e02bca83112aa72878001f99da1d7a3280017201a98023000028d80029b00020b0002b803324881c20880a28110a11f0c88dd2ae8bf1290fd0570ee84019908d99f8b50781529318a4969a880000fea4a8000000828001ef24821e2c707a2d81ec1fda539ac2932cc0b68002268f78000002578000000eb046a7ea5c80017f1e187c8a79411dd87624d1a32260c000000000019980013f9c3800000000000
  | 11 => 0x18b95d9789a5a150002d4000115ac483212e25f0e02949f52a3abe8451f90b225a8a60291a02991fb18b23f00000001b8000002020000d41161311372899c89d52bc1c80849ada788d51e7aa209ea682c40df2438c3186a6512f8bd150a7009523324f97e8b5a29841ac18201729dc97f9dd15b025a9501599212f2148d903e0a991706d83ea012520001cd8dca2b85798093ca7d16f0af8f199a9c9894220a9aaa08b72270d294616bac0a512581eeaae0e422513487e9d812d0d60a708b2b78e39e3a2100005f917861a319388591fe80000007f86822c23991d1711bf9f5858ac90f000020a8ac8382562aa0b02238bb8819f42b68901c114e8230e50af12b2d89ed91e97a95324c26729e06518e00400021199b8000f11650ab9e124c83d02a0000001670001a187a8f383c0001242710000001b42408d113d27caaf8010001ba18805e0000fc00000000003c8000000b41e30e78002b10000000788f629d044a3b9df9b20000600cba47a0615f2752b8ab0a5e104a6c19683f108800055a4b9538000000002d11051d8803083aa2a1585aa9002b26e23a9c49769f21bea058769cfa6bad99b80f48e104aa9f8fa8db099244ad0a1f08eac8907a6a9fbad320a1b10a392e9958f313c2d6088a3e91faa1092959a1601fa79965851a411d09860cc9f029c23914f89daba04816800009b210a6418916e11908210b8001c2a8e8f89b009aaa79a88d71d683710d2a029628b17406d2ad0a90e30bc96607207022216d0318750338b3a0422a8d48582bf2d51430e08c285224029a2200500be8710a52b29829ffa5081303fa430268c5235280a09037991a3f8001a81e4aa508120825680002187b2d497710c966aadaa61642aa82d07180029400000014f0d200000000028280027900525a0000c5a3380006f8002731679d200821b1909d590f17829b93d8000772d0000000181a8218709109c8959d98fc9972ce1e8a6117a0a214d9a11aa1510671f71a400002f9fc977835111ab015b9288b18000b62a41ea28b8001e5a5d94a0000cea8498584380015680022400000002622180001e1109878001bd8daaa68170de13317d08e09095e24a00d1832549
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xaba800c9640400157300192c80800387d525498c1024d2ec2ca53182000a9e8494a630400153b09294c60800393e095298c1024f27902a53182049e4d2054a630408f4bd0a294c608002a7a105298c100054ec20a53182000e1f52d0a6304001c3aa5a14c60800297a164298c100052ec2c853182045a9d8490a6304001d1f04a14c60800387d494298c100070ea92853182044e8f2150a6304089d1a42a14c60800297a144298c100052ec28853182043a9e8410a630400b1bd0fa9ac6080163721d5358c100054f420a6b182000a9d8414d630400b1bd0fa1ac6080163721d4358c100052f42886b182000a5d8510d630400b1bd0f192c60800297a163258c100052ec2c64b182000a9e848c9630400153b09192c6080163721d3258c100052f42864b182000a5d850c9630400153d08192c608002a76103258c100256b40864b182005ada800c9630400153d083aac608002a76107558c100052f428e8b182000a5d851d16304001c3ea92a2c60800297a167258c100052ec2ce4b182000a9e849c9630400153b09392c60800297a147258c100052ec28e4b182000a9e841c9630400153b08392c608012b5a047258c100056ac08e4b182005ada801c963040015b300392c608126976165258c100054f424a4b182000a9d849496304001c9f04a92c60812793c815258c1024f26902a4b182047a5e85149630400153d08292c608002a76105258c100070fa9684b182000e1d52d0963040014bd0b212c608002976164258c1022d4ec2484b182000e8f825096304001c3ea4a12c608003875494258c102274790a84b182044e8d2150963040014bd0a212c608002976144258c1021d4f42084b182000aae84dd5620400155b09baac4081269b61e755881023f33884eab102047e6a109d5620408fcca213aac40812b9a442755881000637c3aeab102049c6f705d562040938dae0baac40812799c41755881024f35082eab102049e65105d56204091cd220baac40811e9ba14755881000557420eab102000aad841d562040014dd0bba2c4080029b617745881022d56c3ce8b102000e2e759d16204001c5aeb3a2c40810fa9c42745881021f55084e8b102043ea5109d1620408dd52213a2c4080032be1d7458810007173aae8b102000e2d755d1620408995ee2ba2c4081132b5c5745881022f53882e8b102045eaa105d1620408bd4a20ba2c408113aa441745881000537428e8b102000a6d851d1620408755d083a2c4080038bd5254588100053742ee6b102000a6d85dcd620400155d09b9ac408002ab613735881000537428e6b102000a6d851cd620400155d0839ac408002ab610735881002573408e6b102006ae5811cd620400b5d50039ac40801aba600735881000557420a6b102000aad8414d62040014dd0a21ac4080029b6144358810
  | 1 => 0x8e5a92c6880021fa1d5258d100043e43aa4b1a2000c3f7454963440a3878e8a92c6880031bdc95258d1000e36392a4b1a20008be87d0963440051790fa12c6880030fdd74258d102861e3ae84b1a2000caf72d096344003958e5a12c6880022fa1d4258d100045e43a84b1a2000c3f75509634409f878eaa12c6880032bdc94258d1000e5639284b1a20008de87cc96344003998e5992c6880063721d3258d1000e6639264b1a2001ce47288563440031e90e90ac688003a95092158d1000e7439440b1a20018f8874816344001cd2a4902c688003b84852058d100046fc3ac631a2000acc8258c6344001878e9b2a628813a2fa1b744c5100061fb2ee898a2000c3c65dd1314409b17d0fb2262880ae2f21f644c5100043fc2aec982200387c855d9304400117f08bb2608800a2f211764c11000477c12ec98220018ec825d930440990fd0dbaa60880030f193754c11025c3f43eca982202e87c87d95304400187eebb2260880030f1d7644c11002c7b436e29822000c3f749d1650400147d0839aca080028f61073594100043f43886b28200087d8710d650408f8ee21b92ca0811f1d443725941024c3ec3ce4b282000a3e849c9650400147b09392ca080031be09725941024e3b882e4b282049c75105c9650408f0fd0e392ca080028fa1072594100051ec20e4b282000c3f72d09650400187ae5a12ca0810f8dc43425941021f1a88684b28200087e8790965040010fb0f212ca081168f612425941000717c1284b282000c3f72509650400187ae4a12ca081138bc8542594102271690a84b282045e3710509650408bc6a20a12ca080021fa1c42594100043ec3884b282043a3e8410965040010fd0f192ca080021f61e32594100051f42464b282000a3d848c965040010fd0e192ca080021f61c32594100051f42064b282000a3d840c965040094ed02192ca080029d604325941002d3d40064b282000a79800c9650400187eeb3aac8080028fa1473590100051ec28e6b2020008be8714d640400117b0e29ac80810f2e84372590102365c886e4b2020458bd879c9640400147d0b392c8080028f616725901000657c12e4b202045cba105c9640408997220b92c80810e2fa1c72590100051f428e4b202000a3d851c9640400187ee5a92c8080030f5cb525901023f1d086a4b20204ae3910d49640400117d0f292c8080022f61e525901024d1ec2ca4b202000e2f82549640400187ee4a92c8080030f5c9525901024f17902a4b202049e2d205496404093c7420a92c8081238e44152590100045f438a4b2020008bd87149640408f47d0a292c8080022fa1e32590100045ec3c64b202000a3e858c9640400147b0b192c8080022fa1c32590100045ec3864b202000a3e850c9640400147b0a192c808012ada0432590100055ac0864b202005
  | 2 => 0x921d91101655c43241b222000ea8624836444001e52a4906c888003e848520d91100054f41eebb222000a9d83dd7644400187aea3aec8880b2ada0475d911015d5ac08ebb222000a3e859cf644400147b0b39ec8880022fa1c53d91100045ec38a7b2220008bd879cb644400147d0b396c8880028f61672d911000657c12e5b2220008be871cb644400147d0a396c8880028f61472d91100054f418e5b222000a9d831cb644405956d02396c8880aead60472d911015d5d400e5b22202cab9801cb644400187ee5a96c8880030f5cb52d91100045f43ca5b2220008bd8794b64440a947b0b296c8880038be0952d91100061fb92a5b222000c3d7254b644400117d0e296c8880022f61c52d911029d1f428a5b2220008be878cb644400117b0f196c8880028fa1632d91100051ec2c65b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b22202cab6810cb644400156b02196c8880aeaea0032d91100055cc0065b22202b8be87d47644400117b0fa8ec8880ae2fa1f21d91100045ec3e43b222000a3e85c87644400147b0b90ec8880032bdcb21d911000657b9243b22202c8be87c83644400117b0f906c8880028fa1720d91100051ec2e41b222000e2d52c836444001c5aa4906c8880afaa08120d91100056ac0865b1a2000ad9800cb6344001d4a8490ec6880039a54920d8d100077090a41b1a2000c3e74d96634400187ce832cc6880030fd957498d100061e32ae931a2000c3e75d92634400187aebb24c6880030f9d46498d100061eba8c931a200387e86dd5634405b0f90dbaac6880021fa1f6558d100061e3a6cab1a2000c6c72d9563440010fd0e32ac6880030f1d06558d1000636390cab1a20028be86dd163440571790dba2c6880030fd977458d100061e32ee8b1a20008be87d91634400187eebb22c6880030f1d76458d1000656396c8b1a20008be87191634400187eea322c6880030f1d46458d1000656390c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d1000656326e4b1a200087d82dd5634400117f08baac68800a2f2117558d1000477c12eab1a20018ec825d5634400187eebba2c6880030f1d77458d100045ec16e8b1a200087f855d163440070f90aba2c6880023be097458d1000c76412e8b1a2000c3f751d16344001878ea3a2c6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031be177258d100063642ee4b1a2000caf84dc9634400195909b92c6880021fe157258d1001c3e42ae4b1a20008bf845c9634400517908b92c68800237e0d7258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a200087e87d4963440070f90fa92c6880030fdd35258d102961e3a6a4b1a2000c6f72d4963440038d
  | 3 => 0xb1c202aa5c8558f31840494b90ab1a6308003271d1634c6100043ec3cc9b2a200087f87593654400147b04326ca880038e60064d95100043f436e5b2a2000c3c64dcb6544001878c8b96ca8800e1fe1f62d951000636b96c5b2a200087d8798b654400147d09316ca880028f61262d95100043fc3ac5b2a2000a3f8458b654400147908b16ca8800297e0d62d95100052e41ac5b2a200c87d8718b654400147d08316ca880028f61062d95100052f418c5b2a2000a5d8318b65440018dae4316ca880028fa1b42d95100051e43685b2a2050c3e76d0b65440014790ca16ca8813f0f9d942d951016d3a43243b2a2000e64624876544001e4a8490eca880038e19240d95101753c43281b2a202ea78864836544001ad6e4906ca88003d848520d95100052f41ee9b2a2000a5d83dd3654400187ae83a6ca880b69ea0074d95101753cc00e9b2a2000a3e849cf654400147b0939eca880021fa1c43d95100043ec3887b2a200087d879cb654400147d09396ca880028f61272d951000637c12e5b2a200087e871cb654400147d08396ca880028f61072d95100052f418e5b2a2000a5d831cb654405d4ed02396ca880b69d60472d951016d3d400e5b2a202ea79801cb654400187ee5a16ca880030f5cb42d95100043f43c85b2a200087d8790b65440ad47b09216ca880038be0942d95100061fb9285b2a2000c3d7250b65440010fd0e216ca880021f61c42d95102ad1f42085b2a200087e878cb65440010fb0f196ca880028fa1232d95100051ec2465b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a202ea76810cb65440014eb02196ca880b69ea0032d95100053cc0065b2a202d87e87c8765440010fb0f90eca880028fa1321d95100051ec2643b2a2000e2d42c876544001c5a8490eca880bb9908521d95101743f43e81b2a200087d87d03654405d0fd0f906ca880021f61f20d95100051f42641b2a2000a3d84c8365440018dee5906ca880031bdc920d95100061f3b6cbb222000a3d82d97644400117b0f32ec8880028fa1665d91100045fc3acbb222000a3e86197644400187cec32ec8880028f60865d91100071ac08cbb2220008be86dcb644400187ecbb96c8880030f19772d91100061fb2ae5b222000c3c655cb644400517f0fb16c8880032b5cb62d91100045ec3cc5b222000a3e8598b644400147b0b316c8880022fe1d62d91100051fc2ac5b222000a3c8558b644400153f06b16c888002a720d62d911005c5ec38c5b222000a3e8518b644400147b0a316c888002a7a0c62d91100054ec18c5b222000cad7218b644400147d0da96c8880028f21b52d91102961f3b6a5b222000a3e8654b64440014790ca96c8881470f9d952d91100071a32ca3b22202bab48654764440575690c90ec88800369dc
  | 4 => 0x54c0010fb0e20eca980ea97a0c41d95300052ec1883b2a6000a6e82107654c0014db0420eca980e69ea0041d95300053cc0083b2a600087e87c87654c0010fb0f90eca980028fa1321d95300051ec2643b2a6000e2d42c87654c001c5a8490eca980021fa1c21d95300043ec3843b2a6000a3e84087654c00147b0810eca980ea97a0c21d95300052ec1843b2a6039a7a80087654c0014f30010eca980ea1fa1f40d95300043ec3e81b2a603a87e87c83654c0010fb0f906ca980028fa1320d95300051ec2641b2a6000c6f72c83654c0018dee4906ca980123720d75d853000657b9285b0a6001cac7250b614c001cd2a4906c29800e1fa1b75585301cc3e436eab0a600087e87d95614c001878e9b2ac2980031b1cb65585300043f438cab0a6000c3c74195614c0018d8e432ac2980030fd9774585300061e32ee8b0a6000c6f65dc9614c0018d8cbb92c29815f175cc65185300047bc3ac230a604ba5e86d97314c0af0f90cbac62980021f61f658c5300061e3a6ca98a6000c3f65dd1314c001878cbba2629809297a1b654c5301ce2e3b6ca98a6000d1c74d95314c02f33d0fba26298103271db744c5300070e32ee898a6000e5465d85314c001caeca30a6298003661d3704c530006cdba0e098a60048dd83dd5610c00117f08baac21800a2f21175584300145f43ee8b0860008bd82dd1610c00155b043a2c2180022fe1172584300145e422e4b0860098dc835c9610c00187ee9a92c21814b0f1d352584300061fba2a4b086051c3c74549610c00117d0fa12c21800a2f21f42584300045f43a84b0860008bc87509610c00395ce4a12c2180032b5c9425843004d6b41ca2b0860058f487545610c005968e920ac2180163d21d415843002c7a43a42b086000ea542485610c00117f08baac78800a2f2117558f100145f43ee8b1e20008bd82dd163c408117d0e3a2c78801237a1f5358f100256b40ea6b1e2000a9d8414d63c4005938e921ac7880123721d4358f100045fc22e4b1e20028bc845c963c400187ee9a92c78814b0f1d35258f100061fba2a4b1e2051c3c7454963c40018dee4a92c7880071b1c95258f100045f43e84b1e20028bc87d0963c400117d0ea12c7880022f21d4258f100246e43a64b1e2000ea54248563c403b53908b1e6188003171d5634c3100bd4e422c6986200387e87dd563840010fb05baac7080e61fa1c7558e100043fc2ae8b1c200387c855d163840078b8eb29ac7080163721d5358e1002c6f43e86b1c2005ada80d0d63840014bb0a21ac7080021fe157258e1001c3e42ae4b1c200087e87d4963840070f90fa92c7080021fa1d5258e100043e43aa4b1c2000c3f75d0963840a1878eba12c7080030fdd54258e1027e1e3aa84b1c2000caf725096384003958e4a12c7080163721d3258e1000734a924
  | 5 => 0x80028f21573592302e55dc02e6b24603be1e53d4d648c08b17b0f392c9180028fa1672592300051ec2ce4b246005aba809c9648c0b757301392c9180032be09725923021c5f438e4b246000a3e851c9648c00147b0a392c9180030fdcb52592300061eb96a4b2460008be87949648c00117b0f292c9181268f616525923000717c12a4b246000c3f72549648c00187ae4a92c9181278bc81525923024f16902a4b2460008be87149648c00117b0e292c91811e8fa1452592300045f43c64b2460008bd878c9648c00147d0b192c9180028f61632592300051f428e2b246000a3d851c5648c07753d0638ac918002a760c715923000557410e2b246000aad821c5648c00b5750038ac91806aae60071592300045f43ea2b2460008bd87d45648c07753d0728ac918002a760e515923002d5d400a2b246000ab980145648c00117d0f90ac9180022f61f21592300051f42e42b246000a3d85c85648c00195ae590ac9180032b5c921592300045f43842b2460008bd87085648c00147d0a10ac9180028f61421592301dd4f41842b246000a9d83085648c00b5750010ac918002ae60021592300056ac1ca2b0c60058f487545618c00b1e90e90ac318003a9509215863000734a9240b0c6000ee121481618c00187cc8bac63180131d985758c6300061f3aac918c6000c3d75592318c00b974e0b2463180031d5d5618c6300065cb22e118c60008bd86dd1318c0b51790eb2263180021f61e64d953000537414c9b2a6000a6d82993654c0010ff0eb26ca980e697a1b43d95300070fb2687b2a6039b5a80d0f654c0012bd0e21eca980038759043d95300043f436e5b2a600387f87d8b654c0018dae5b16ca980021f61e62d95300051f424c5b2a6000a3d8498b654c0010ff0eb16ca980621f61c62d95300051f420c5b2a6000a3d8418b654c0018dae4316ca980029da0462d95300053ac08c5b2a6050c3e76d0b654c09f87ceca16ca980038bd8942d95300071631285b2a6039a5c864cb654c001c98c4996ca980ea9e21920d9530006b5b9241b2a603aa5e83dd3654c0734bb07ba6ca980030f5d074d95301d70e21a87b2a600087d879cb654c00147d09396ca980028f61272d953000637c12e5b2a600087e871cb654c00147d08396ca980028f61072d95301d52f418e5b2a6039a5d831cb654c0014ed02396ca980029d60472d95301cd3d400e5b2a603aa79801cb654c00187ee5a16ca980030f5cb42d95300043f43c85b2a600087d8790b654c0b347b09216ca980038be0942d95300061fb9285b2a6000c3d7250b654c0010fd0e216ca980021f61c42d95302c51f42085b2a603987e878cb654c0010fb0f196ca980028fa1232d95300051ec2465b2a6000a3f845c7654c00147908b8eca980ea97a0c71d95301cd2ec18e3b2a600087e871076
  | 6 => 0x4cf438a7b2262008be86dcb644c40517f0fb16c8988032b5cb62d91310045ec3cc5b226200a3e8598b644c40147b0b316c8988022fe1d62d913111c5ec38c5b226200a3e8518b644c40147b0a316c8988032b5c862d91310055d400c5b226200ab98018b644c4a587ceda96c8989470f9d952d913100717b12a5b226200e2c6254b644c4815390c996c898803a318932d913120d5a43243b226200da772487644c48353d07baec898902a760f75d91310061eba8ebb226241e1e53d4f644c40117b0f396c8988028fa1672d91310051ec2ce5b226200caf825cb644c40117d0e396c8988028fa1472d91310051ec28e5b226241a9e831cb644c48153b06396c898902ada0472d913120d5ac08e5b226200aba801cb644c40157300396c8988030fdcb52d91310061eb96a5b2262008be8794b644c40117b0f296c89897a8f61652d913100717c12a5b226200c3f7254b644c40187ae4a96c8988022fa1c52d91310045ec38a5b22625da3e8514b644c48117d0f196c8988022f61e32d91310051f42c65b226200a3d858cb644c48317d0fa8ec8988022f61f51d91312071b28ea3b2262418be87c87644c40117b0f90ec8988028fa1721d91310051ec2e43b226200caf72c87644c40195ee490ec8988028fe1570d91310051e42ae1b226241a9e831c3644c48153b06386c8988022fa1c50d91310045ec38a1b226241a9e83143644c40153b06286c898802aba0850d913100556c10a1b226240ab681143644c40156b02286c8988022fa1f20d91310045ec3e41b226200a3e85c83644c40147b0b906c8988038b54b20d913100716a9241b2262008be87083644c40117b0e106c8988028fa1420d91310051ec2841b226241a9e83083644c40153b06106c898902ada0420d91310055ac0841b2262058dc835d3604c4018dee4a96c0988071b1c952d813100752a1243b0262028be86dd1604c4811790dba2c0988022fa1f64581310061fbaec8b026200c3c75d91604c401958e5b22c0988022fa1c64581310061fba8c8b026200c3c75191604c401958e4322c0988032bd93725813100656326e4b02625ac9d73190604c4011f70eb00c09880e1fa1f75580310043ec16eab006200a6d821d5600c40b1bb07ba2c0188021fe15745803101c3e42ae8b00620087f855c9600c4070f90ab92c0188021fa1f525803101c3e43ea4b00620087e87549600c4010f90ea92c0188071b9c9525803100636b92a4b006200c3f75d09600c4a1878eba12c0188030fdd5425803127e1e3aa84b006203c7875941600c4091f10ea82c018826b6a0e40580310247c43a80b0062048f887481600c401cd2a4902c0188163720d745873000637b92a4b0e6001c6c7254961cc0031e90e90ac398003a9509215873026ccf43ee898e6000c3f759d5648c00147f0ab9ac91
  | 7 => 0x78060280180081000000001818000024000080020040001a00000801802022008050110000040c8020000000000a00a0240400000003c0080a00403000806006004018030080040380101003c000040000080480000c00000000002068000020080000100001602802806000000020220000481080400e0000a0010040000180002e0080080000401c00000004018050040000540200700000c0000100205003000034008088000080640000b00c0280000002a0000400300c00c010050040440300a02c0040302500602c0000901400801001006004000030020000180c00202c0280100201c008000120280080300e008018000000040181900000400810026014010020080000100701600001011002020008090020040000000200c0600200c00801001000000020020020000d80000403800004048028028030100140000007800c0580300401c028040000440080000600c000020100000180300a0280000b0020280580000601004804018000000020000000100e0040080101e00001c008020000040300200000000005002000010040000180000700c0040e80701c000050090100000400400002400007006038010010040000000201a030048060020740000000c014010010246e41aeab066200caf7250960cc403958e4a12c1988063e21d205833100734a9240b066200c3f749d1658c40147f08b9acb188028f21173596313053bc0ae6b2c624887d879c9658c40147d09392cb188028f61272596310253b40ce4b2c625fa75819c9658c4018df04b92cb1892a1fa1c72596310051f420e4b2c6200a3d841c9658c40187ee5a12cb188030f5cb42596310043f43c84b2c620087d87909658c48947b09212cb188038be0942596310061fb9284b2c6200c3d72509658c489c5e42a12cb189138b48542596310043f43884b2c620087d87109658c48d47d08212cb188021fa1e32596310043ec3c64b2c6200a3e848c9658c40147b09192cb188028fa1070596310051ec20e0b2c6242a5e831c1658c4014bb06382cb188029ba08705963100536c10e0b2c6204a76811c1658c44f4eb02382cb188021fa1f40596310043ec3e80b2c6242a5e83901658c4014bb07202cb188129da0440596310053ac0880b2c620087e87c81658c4010fb0f902cb188028fa1320596310051ec2640b2c6200c6d72c81658c4018dae4902cb188021fa1c20596310043ec3840b2c6200a3e84081658c40147b08102cb1890a97a0c20596310052ec1840b2c6204a7681081658c4014eb02102cb18803a950921582310056cc1c80b0462048f887501608c4091f10e902c1188039a54920582310077090a40b0462008bd87997644c40155d0532ec898802ab60a65d91310045fc3acbb226240a9e86d4f644c401c3ecba9ec898902e5a0753d91310
  | 8 => 0x40a50e11b10423bb2ce0c93251040001a204a2a90001d30e200000009d23b22a40840702900028031137100f0780002a00000000000ff0b21083ca21d29b0770000481fa0001691900000003620000500001ab08d0000000000000700000000760720000003003d70bf0000000001a534b0003060000000000000000d11423720002ea00002000018c1241f41820040b300003e15836f07e2a710a2961be1bd3aa0012822ca3a80471783200fa01b3b507d02a0e81483210112a61de19108500034f02e0000004013790000000f20b600015e0c519404e0000000bd0001c121e4100fb1aa00028d11c1bb14d3b32443991590000832390000001933e70000903412373400000452403cc3f532f1fc29f00034300018b29736338c00000000020802d2601a31d618d2ac00000006700912d3512940002223f90002dd0460940792af0cf0ec10d37f29d1c63a53fd20a35010304c3700000000820003491d100040613500d00000019a10509600019e00033a25f0000000000001110000001171ae0a930f0392700de1ca0001210d71703760000380660000000000001550000000002ba0000003440001800000000003384140000802d500000000000000016d3141092774152be0db10212825d17508f0f60000870002150eb09235240b12b00000008106340d3c52b404d0001600f32250401b805c10b0000af0001bf1c700000000012701a00015a1f227300016340006b3d90000002180c40fe2130003943170000003d125c00011613900007424616623a00026826c1100e40000733e60d92583b20e72663862de24a2cb24330a30e05d1312951db3651672df26a30d0bc2122f61d43230000162d40000003901380000000004160000000000003950000000002f830236000036b0002b926520700000000005818307b00b13726e0e914133523d17a36640c34225a00017100038100036e33700008a0ca3032cf00027f2c231e2ee3923d823f0002101952552fc00019809e3f83fe2010c733222d3683ab3bd38f1d500013c2ae2fe01d0001b311e00000018f1ad0000003342913eb0003c41e23bc0ea0fc00000000032c24c2fa2d332e00003500000014c0253f615b2db2113e409317913a0e62ff38d1722c801c2644120000003460000000000000000000000d20a615c2b239700040411500000005b24d0e311421a0002c510f0000000ee00020c1c01fe01728f1f023432b01e33c0323582e50a72022c323c0f118600000000011900000035e40a0002690f022f3e200025230b1d83890001b920d02f20028b02328a0002bb2cc0000001621ef1b22a33c63091b01e40003912aa1a127b26d13d0002f70002bf3781b629826108b3e92872762283290620ba2e02c926b2d12cd1561e735b10e2213240120000001001700001800000018000020
  | 9 => 0x20916e40331829a3e80570b53190180533750003850001532860690000003f10083f32670f43be00014919b22927938714f39f00c3f021f12a1ed2a81970dd1444133b812f37400008c0331ce2c100031b22e2542192830c12e43ac3f700012300006c00000000027c2992d60640d60a33103830001773ae0102140d51c31c937d17b00040e3c70990001fd1f50752811d935935d1e92f00f705a1812e92f10282c43981882380002a516b30c07c31f00023622c29005524930802b1c83d609b0003270fd2ed2b00003d52f33a600035f17604b12e3e000013e0601df36c14b16c2a43c30000000000001d02921b70b42b50000003570000000002d70000000b71a03b70001e32a21f83932932d22621d20521dc1e10000560000ac09a0003dc0003a91060002200001741333392590050002421641da1523fa2e62b606e31a0003d016f2720000003a100024806836437700000019f2b32273af12211d00000006a2510000000002c63cf00000300038813b2b83b90000000000000003fc12c0000860003e30000c300000027d10c1f619605421724f2c709118e33b24729c2bc1340f524518a0972f23481320951650ed3c102c2fd0002c001400000000000000000002200000000009f0c621600000005118700620b2dc1853fb1b43221b53c23f20593261500341181e817f15f32a3e52333b417c19c1121464020002ef14e34a37a1920000e54092240270240b805e0441891680cc3f41f923e2a100000019d0e000a1a80aa07100008e00037c1c41a62852ec2571c50151072030a03d21843ed2f434d3671e50d00492d817d1eb2750003540be00000017e1513b60000ab0133ff3733ad0000003690000891360000000000000b00263012e33a21540c020f0c825e3a73cd0c237b0881f31e63163040bb13f3a41ea0000000000002ad11f2350000002d00003b01993d32d93610ad3bf0b939e0120b100012607f00021c34c30511300000e2e80301402ab38e0001f140500036a2883b13d410122606f0072da0f82f936d0001e00001cb3550000d41a90d300014a0000ef3820841ec39b3960ce39d35a33e2843a315d12011a38028e3c039a2050210003450f94110000000000df0001730000000dc1f731300003f1a70003a01d71fb41723004f0001001a425b35333f2b100039c2562780003ce0311c200027e00029e0ae00011b3c92f53ba28c0cb40f0363560002060002741571cf2230001ee0002502e103d0651bc0002fb01f00000031200024e26f03c3cb0a400021b0000001470002713ea0003de2eb0003363dd3c82322bd2e70d803709c33d31d2890003db03b0000611300001291251ac0000000000a800000031c33316a0cd2533152b70a201934e05f22b37e0431af24107a3313ee1ba3da3ef2e238b0981dd14532d20406d27a38
  | 10 => 0x21ff24b0003e10a132800030734723120e03a2631cc00035c3df33014300016138a3ec0da1cd041000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1239411088009600000832060018a01c90001a78000001114016299018952d913100529a5b72487644c40706c985c9525803100487e616410f654c0016259118942d95300051aa5b72483654c0050ac985c942584300052925d4248563c4001468975492058e100050b64864dcb65440016249650921d95101769821921483654400142d9219772d91100058a2595248364440576a09648520d91100052925d4248563440038a4875092158d100051a25d524816344003868875492058d10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x1
  | 6 => 0x4b
  | 7 => 0x4d
  | 8 => 0x4e
  | 9 => 0x4
  | 10 => 0x94b
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124b
  | 14 => 0x124d
  | 15 => 0x124e
  | 16 => 0x138b
  | 17 => 0x138d
  | 18 => 0x138e
  | 19 => 0xcb
  | 20 => 0xcd
  | 21 => 0xce
  | 22 => 0x9cb
  | 23 => 0x9cd
  | 24 => 0x9ce
  | 25 => 0x12cb
  | 26 => 0x12cd
  | 27 => 0x12ce
  | 28 => 0x168b
  | 29 => 0x168d
  | 30 => 0x168e
  | 31 => 0x24b
  | 32 => 0x24d
  | 33 => 0x24e
  | 34 => 0xb4b
  | 35 => 0xb4d
  | 36 => 0xb4e
  | 37 => 0x144b
  | 38 => 0x144d
  | 39 => 0x144e
  | 40 => 0x16cb
  | 41 => 0x16cd
  | 42 => 0x16ce
  | 43 => 0x1489
  | 44 => 0x130a
  | 45 => 0x14c9
  | 46 => 0x134a
  | 47 => 0xb49d3
  | 48 => 0x9cb53
  | 49 => 0xb49d5
  | 50 => 0xb49d6
  | 51 => 0x9cb56
  | 52 => 0x16c9d3
  | 53 => 0x9d6d3
  | 54 => 0x16c9d5
  | 55 => 0x16c9d6
  | 56 => 0x9d6d6
  | 57 => 0x17c9
  | 58 => 0x134c
  | 59 => 0xa0c
  | 60 => 0xb5693
  | 61 => 0x168b53
  | 62 => 0xb5695
  | 63 => 0x168b56
  | 64 => 0x178a
  | 65 => 0x148c
  | 66 => 0xbcc
  | 67 => 0x1889
  | 68 => 0xd0a
  | 69 => 0xd09
  | 70 => 0x188a
  | 71 => 0x1a09
  | 72 => 0xd4a
  | 73 => 0xd49
  | 74 => 0x1a0a
  | 75 => 0x14c
  | 76 => 0x14a
  | 77 => 0x28c
  | 78 => 0x289
  | 79 => 0xd0e
  | 80 => 0x188e
  | 81 => 0xd4d
  | 82 => 0x1a0d
  | 83 => 0x95a15
  | 84 => 0x94d55
  | 85 => 0x95896
  | 86 => 0x94d16
  | 87 => 0x5c9
  | 88 => 0x9d896
  | 89 => 0x9cd16
  | 90 => 0x58a
  | 91 => 0x12c995
  | 92 => 0x12d695
  | 93 => 0xb5a15
  | 94 => 0xb4d55
  | 95 => 0x144b16
  | 96 => 0x1456d6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1186
  | 6 => 1460
  | 5 => 1048
  | 4 => 19
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (48227+((h/395+packedAt gbK7 (43882+(h % 395)*11) 11) % 1424)*12) 12
  | 6 => packedAt gbK6 (75426+((h/486+packedAt gbK6 (70080+(h % 486)*11) 11) % 1753)*12) 12
  | 5 => packedAt gbK5 (65671+((h/349+packedAt gbK5 (61832+(h % 349)*11) 11) % 1383)*12) 12
  | 4 => packedAt gbK4 (1360+((h/6+packedAt gbK4 (1330+(h % 6)*5) 5) % 31)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc3fff1e0f0fc3f80c701f83ff14c19e1dc4cf
  | 1 => 0xfc380e00ff0fc3fff801ffc1f2b0e686278f3
  | 2 => 0xffc00fff000ffc00fffe3ffe0cc3071838f3c
  | 3 => 0xf00000ffffff00000ffffc0000f03f81fc0fc0
  | 4 => 0xfffffffffff000000000ffc001fff000
  | 5 => 0xffffff00000000000000000000fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x100486060501404844104480ca0040820cc445
  | 1 => 0x4410820021004122880892814010628201892
  | 2 => 0xaa810489000aa8081250253004c1050830128
  | 3 => 0xa00022b32baa00012e4ad00846b02b81740ec0
  | 4 => 0x822044ddccccf325c003001188fec001dbe000
  | 5 => 0xcf32780180882206000c006210ffbd7c000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeecf8e8feeefeeafeecf8e8feeefeeafeecf8e8feeefeeafeecf8e8feeefeeafeecf8e8feeefeeafeecf8e8feeefeeafeecf8e8feeefeeafeecf8e8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36320
namespace PEqualNP.Outside.L_meta_36320
open PEqualNP.Outside.L_meta_36320.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 4 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 12 := bs0_4_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 4 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 12 := bs1_4_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
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
theorem bs2_4_512 : Interval s2Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 539 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96)) (concat (concat bs2_4_128 bs2_4_160) (concat bs2_4_192 bs2_4_224))) (concat (concat (concat bs2_4_256 bs2_4_288) (concat bs2_4_320 bs2_4_352)) (concat (concat bs2_4_384 bs2_4_416) (concat bs2_4_448 (concat bs2_4_480 bs2_4_512)))))
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
theorem bs2_5_640 : Interval s2Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 664 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 bs2_5_192) (concat bs2_5_224 (concat bs2_5_256 bs2_5_288)))) (concat (concat (concat bs2_5_320 bs2_5_352) (concat bs2_5_384 (concat bs2_5_416 bs2_5_448))) (concat (concat bs2_5_480 (concat bs2_5_512 bs2_5_544)) (concat bs2_5_576 (concat bs2_5_608 bs2_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := (concat bs2_6_0 bs2_6_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 7 := bs3_3_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 15 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 68 := (concat bs5_3_0 (concat bs5_3_32 bs5_3_64))
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
theorem bs5_4_768 : Interval s5Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_800 : Interval s5Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_832 : Interval s5Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 894 := (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)) (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 bs5_4_416)))) (concat (concat (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)) (concat (concat bs5_4_544 bs5_4_576) (concat bs5_4_608 bs5_4_640))) (concat (concat bs5_4_672 (concat bs5_4_704 bs5_4_736)) (concat (concat bs5_4_768 bs5_4_800) (concat bs5_4_832 bs5_4_864)))))
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
theorem bs5_5_800 : Interval s5Atlas 5 800 20 := block_range (n:=20) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 820 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat bs5_5_96 (concat bs5_5_128 bs5_5_160))) (concat (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)) (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 bs5_5_384)))) (concat (concat (concat bs5_5_416 (concat bs5_5_448 bs5_5_480)) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576))) (concat (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)) (concat (concat bs5_5_704 bs5_5_736) (concat bs5_5_768 bs5_5_800)))))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 19 := bgb_4_0
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
theorem bgb_5_1024 : Interval gbAtlas 5 1024 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1048 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))))))
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
theorem bgb_6_1440 : Interval gbAtlas 6 1440 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1460 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 (concat bgb_6_384 bgb_6_416)) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))) (concat (concat bgb_6_544 (concat bgb_6_576 bgb_6_608)) (concat bgb_6_640 (concat bgb_6_672 bgb_6_704))))) (concat (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 (concat bgb_6_832 bgb_6_864))) (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)))) (concat (concat (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)) (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248))) (concat (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440))))))
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
theorem bgb_7_1184 : Interval gbAtlas 7 1184 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1186 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 (concat bgb_7_384 bgb_7_416))) (concat (concat bgb_7_448 bgb_7_480) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))))) (concat (concat (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 (concat bgb_7_832 bgb_7_864)))) (concat (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024))) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeecf8e8feeefeeafeecf8e8feeefeeafeecf8e8feeefeeafeecf8e8feeefeeafeecf8e8feeefeeafeecf8e8feeefeeafeecf8e8feeefeeafeecf8e8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276943080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36320.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.or,[5,6]⟩,⟨.or,[1,3]⟩,⟨.or,[0,6]⟩,⟨.or,[2,4]⟩,⟨.and,[3,5]⟩,⟨.or,[10,11]⟩,⟨.and,[0,7]⟩,⟨.and,[8,12]⟩,⟨.and,[9,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276943080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276943080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36320

open PEqualNP.Outside.L_meta_36320 in
theorem PEqualNP.Outside.L_meta_36320 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276943080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276943080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
