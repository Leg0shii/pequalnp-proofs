import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36364.Model
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


end PEqualNP.Outside.L_meta_36364.Model

namespace PEqualNP.Outside.L_meta_36364
open PEqualNP.Outside.L_meta_36364.Model
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

def SBf (j : Nat) : Nat := [5, 6, 7, 8, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36364

namespace PEqualNP.Outside.L_meta_36364
open PEqualNP.Outside.L_meta_36364.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1ffc1fffff83f83fe0ff83fc3ffff03ec733f3
  | 2 => 0xe0ffe07c1ffc1fc3ff07fc1fc3c0ffc179cd9c
  | 3 => 0xffffff801ffffffc0007fffffc00ffff81fe1f
  | 4 => 0xffffffe0001ffffff8001fffff0001fe0fe0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4244451104250808a849a124065290944310b1
  | 2 => 0xca48c321292129416942a50c4286a584594594
  | 3 => 0x491080a5242129410844a52a8084a2980aa0a
  | 4 => 0x94a2124a034a54e65290421b312c0309ac0f40
  | 5 => 0x18c39c739c739f3b9ce7738222308c31f7f000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36364
namespace PEqualNP.Outside.L_meta_36364
open PEqualNP.Outside.L_meta_36364.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x730025190000090280df43be43bc43dc439c43bf42bd42df32dd32
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x23802030089400aa1805611e5390e5aa421d354843c7290871d5210f1aa421c3548438e29a851c54cca38a8996350932
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x20c6550932
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 11
  | 2 => 1
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
  | 4 => packedAt s1K4 (156+((h/3+packedAt s1K4 (144+(h % 3)*4) 4) % 12)*5) 5
  | 3 => packedAt s1K3 (309+((h/3+packedAt s1K3 (297+(h % 3)*4) 4) % 15)*5) 5
  | 2 => packedAt s1K2 (39+((h/1+packedAt s1K2 (38+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xe0fffe0ffff87f83ff0fe1ff87fe0ffd1cf3cf
  | 2 => 0xff07fff07fff87fc1ff0fe1ff87ff07ee33cf3
  | 3 => 0xfff83fff83fff8ffe000ffe3ff8fff8303cf3c
  | 4 => 0x3ffffc0000ffffff0003fff00003fc0fc0
  | 5 => 0xffffc000000000fffffffffc00000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2810822210908000a5012024809205280c5145
  | 2 => 0x42410441212008140a1042090824a050612492
  | 3 => 0x842228840a4441a94088954255094a03028a28
  | 4 => 0x16b5b129487552ce73aa1103e640631bb40fc0
  | 5 => 0x18c621ce738664f39cccf99044018c63dbf000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfafafaa0faa0faa0fafafaa0faa0faa0fafafaa0faa0faa0fafafaa0faa0faa0fafafaa0faa0faa0fafafaa0faa0faa0fafafaa0faa0faa0fafafaa0faa0faa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36364
namespace PEqualNP.Outside.L_meta_36364
open PEqualNP.Outside.L_meta_36364.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2718a92134480c042a00b80000129446854260a7401b0034f00000162d521c012000000e1664180003c09c00584000c00010120089f04ac01a140000080020068502180010210083ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x714c04000080d000f0242d20016d0c01340010000001488c00e4984800b4c400d801000000ec916060000000540035145800f800000185700000015c65452488c8857478015800005ca168004d8000b8000c000000940000000038006d1000000000bc000109653050ccc0003cd55431400150011c08753ce8a400001c280000000000000000000014a80000fc0000000000000138017c00012c000000b000001904ad28e0dc000000017988000044f49c00000040007d18006820000000040000000a0002000202000202100202060c06000400040202040000000000076e5210edaa421cf943429eaa4855e5390abaa7215ed4142bc28285af5250b76a0a14f14142dc28285385050a7ca8215794c42aea98859f42ccb3a85994f952329eaa4655d538cb5a85196b50932e7a92659f424cb9c84996750932e6a12658d424ca7ca8194f55032af298657a50906f2a120d7d4d41ae29a833f544c678a898cf950319eaa0636e520c6daa418de94031bca80633e54c867aa990d794f21aea9e43cd32c879a6490cf950219eaa0435e53086baa610de94021bca80433d529033e6520674ca409f284813d521033e6420674c8409f28081ba501027ca9984f55330b7296616d52cc27ea8984f151309f2a6413d54c82bca7905754f20dc206413f5488278a910734ca209faa2413c544827ca8104f55020af298415d530839a64105d94420baa8841b8400827ca9884f55310dc204213f5444278a88857d4d10ae29a216f52442d8a4886e10110
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x4830004001ce28014b3490023001084cf1815004450c40d006986050b32aa181428caa86050932a3592424ca986050932b2181424cb8b6050932a3181424cb886050932a2181424ca4d6214d418e18154c870d544cb21c3549321030f544ca20c3551320834532544208e59440083893210020cc54440083285210110
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x500005087055132c8704b2a6420041c04c95110020
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 4 => packedAt s2K4 (2937+((h/33+packedAt s2K4 (2673+(h % 33)*8) 8) % 189)*8) 8
  | 3 => packedAt s2K3 (833+((h/7+packedAt s2K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s2K2 (150+((h/1+packedAt s2K2 (147+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7fff03ff0fc3e1ff87f87fe1fc0e0fd39f793
  | 1 => 0xf81fffc1ffffc3e0ff87f87fe1ffff02c679fc
  | 3 => 0xffe1fffe00ffffff0007ff8ffe00ffff078e1f
  | 4 => 0x1ffffff0003fffff8000fffff0003f80fe0
  | 5 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x50c4118c41284005380980960246225818b391
  | 1 => 0x12402284804004404882882220924a084250b4
  | 3 => 0x210944102a9222aa04445509540894a3050c0a
  | 4 => 0xa5958921281aab339550440d992c0433a80f40
  | 5 => 0xc6190e39cce333dce6676641103018c3f7e000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeee88eeccee00eeeeee88eeccee00eeeeee88eeccee00eeeeee88eeccee00eeeeee88eeccee00eeeeee88eeccee00eeeeee88eeccee00eeeeee88eeccee00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36364
namespace PEqualNP.Outside.L_meta_36364
open PEqualNP.Outside.L_meta_36364.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xa43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40dfa1681bd42d02fca3a05f54740beaa4817e53902faa7206f90e40de21c817e52902faa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a817c53502fea4a07bd4940b7a92817c52503d8a4a05b14940dfa1281bd42502fea2a05f14540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081be421037884205f94440bea8881bf411037a82205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa3185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4987bd4930b7a92617c524c3d8a4985b14930ef99261dd324c2fea2987dd4530bba8a617c514c3e8a2985d14530fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f681907e10320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef42883d885107bcca20f6194417e51882faa3107bc8620f690c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20bfa8a417c51483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf29041ef42083d884107bcc820f6190417e51083eca2105d94420bea8841f551082eaa2107bc8420f6908417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c43dca5885b94b10bea9621ed52c42daa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dcc610fa18c217e50843f461087e4c210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec42887d48510fd18221f930443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f731043e862085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7c87a16f10f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf28885f65110aeca2215f54442faa8885755110afca0215f54042bfaa6657e54ccafaa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cb7ca9194f95232beaa465bd548ca7aa9195f15232bea9c657e528cbbe65197bcca32bf28c65f6518caeca3195f54632faa8c6575518cafca1195f54232bfaa2657e544cafaa8995f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0f7d4d41afa9a837c53507b8a6a0d714d41dfa1a83bd43506fea4a0df14941dfa1283bd42507ee82a0ef90541bfa82837c50506fca820df94c41bea9883be43107788620df94841f7290836e52106faa420fb54841b6a90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131bfa92637c524c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c7dca418db94831bea9063ed520c6daa418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f721643ed42c87dc6590fb4cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621fb20c43f541887ee6310fd0c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f721243ed42487dc6490fb4c921fb20a43f541487ee6290fd0c521fb90
  | 2 => 0x36098c001fe0000006f0004261d0682590000012e86d000000e70000002e00003900062048800000000000000007bc72077000000000002747403e80000000000000000000000000000000016f1780007080006e000e11ba03204c000000000000020a00000000000492718c800010e000001c3464000a180000041400000000888b020333a81c5d8972520012193d0002f40000020800000000000000810002dc000000000000009907f00048cfa13409a000000cb054000001be29e54cd38000003dc318ca2b60012d80015c0000000000000000219000000d400000000000000000000d58000007c9138000000000000000010c380000000d40a00000000000176000704000000003980000000087c00254000478001f941a03c3995230600000000000000c20000006b0f183a000000000c218e0000009027294512a2d250000001a2000000248000000000000017c000000000000000012b00000053a1223200000000416000001f8470000f60000000006407c1b0630c48003aa5040025200040c6197d00069400000000000508000001680000000000000216000000c880000061400000000000000001100008900000000000004000000000a8000468041a60ce0008a0001de28c0000029475c001a13bc15000000000584070da0005ac001f32f86b5208cd2a83e13002d000838000e538e629011ed088000000000000001b1070980000024e000000c78002221d400000000248ae80000000000000156000000000000012588b000000000001280003d0000000780020600000080000000000af00000093c2b0000000000000000000000000000000001cd0000000e9df44c3309f9bb3c000000000000458988001d25dc0000000000000000000000ee0001f67fca38000000000001a4aa874101d93002d80019b450000000000000000005d000000000001d60012c000000000000000008ac000000000006e80000028000000001000000000000060000000000e000030000000140300000000c00801000008010010020300000000e000008000040000000200000000000000000010020060000180000e0040200000200c000040000000000000200c0000100c010000010000000000000600000001012004008000000000080000800c0280100400000000000000000010180100000500200002000004000000030000000000400002400000008000000000020040000000a00401000002014000000020080200000600000000000000038040000000180200e0000080000000000804002004000040000040000000000000800000004000000060040000200000000800000004010000000200000100000401800000014000000000000000000000000001bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x37a00089981000638001080001b0bc2230000000000026000000000000000001a3000000229f71624300000000000118000000000000000000ec3c1a00b800000000000000001db458878000bf3668ec0000013600000000000000000004206d4d50000d400000000152000000000000008c00000049c000ea1a8000000001c467c000000ca000000001800008d80000000000000000000000ee0000007f00043000000000000000000000001180000000000000000000000000830000006c800000000e4800164000aa8002380a0a882e0006580000004e0000000000091400000000000000000007ec37a330000d00017e48c104d2000000000e91720000000000002c000320002b88f5298000000000009809e0f8179da31a0011b1eb138018c90004ae8e90d1930b09209b2662d485090800000000000000000000522a000820e8800000798f10c100065c8725c2e2000db97a0000000e000000000b3209000564001e4000994ca16800042452800000000000004bc0000000000051452000000120630000000005d06903007c000000000008b8113d20008a80000000000247000258d88000000010205f000000001370d63cc001b813e1d80015f0000011a0000e4475260003ca218000070f2000e4000000000fb0004a00000000000000047800000000001f00000cc9014200000000000134714001862c47d400000000000000002e600064800000254000e7188090a7000000084950000960000002c0040000025f000784b180030e000000000000000019e00000000000000730ba000000100001223161f8a49820000000000000000000000000000000002908c4a60002ac000090b30005402983d216001178d7000000000f9000000000000000240280000000000000000000000003fa000000000007746b0000000007f81b0003c4629c41e00005617b104668000000c43d8001d60dc16cbf9b94800000008442e00000000378000000000000000000036c5100004e20c9683408a1da040930000000011c938000000000b000055d2200000000000000000000cc00035c0011b94d0f6000000b4000490000000003f0001751be0000003000098828000000000000000000000009e0000a4f500000000000000000000000001b80004e92e0000002100d35e000b69790002d51e0000000000010d00000000000000000059fa4c205c689ca000000001d40000000003f25a000000000000001591039647d1fa002c824c000000000006921c3ce0000007100052c00000000000caa4d41e5b0001b424a0000000000056125000000000000e00000000002326600000000000338000000000000005e000154238003b0000001a915e000000db16e8f8530001e42040000000000018800000000e9a2911a3d0460890001286780000200040
  | 4 => 0x3f800000000000000cc899380164f40000008b8808002d24bc0013c4369080006610a3a00013b42a3e8000264423548523500000000000144830000000000000000000000000000000880000000000012b0000006c80012c0000000000002a00030860070000000000000300015a11c0000000000000000000000000f70000a29907180026a000000ad000000b28220007c40000000043c000000002e400000000518b38d315499c00000000000a0000000000000000006fc2913e1fa000000001ea671088000000000002500000c00000000000e7800000000000000000000022440a3b1008320ae5c01e000000000
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x7425032c52d0940cb14942502b86050940da14b405032c52901409dd8553102746154c40c754c43102b96010c408f59642102b56110840a718d411023f6550040ab189401027b6550040ba189401026e62d53309b58b54cc23e6494b308f59252cc2766194b309d58652cc27661d52309d587548c23e64946308f592518c26e62946309b58a518c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c32f54d4930cb153524c32f5414930cb150524c34c52cc930cdd53514c33454d4530d9d4b514c36452d4530cdd50514c3345414530d9d48514c3645214530dc580514c26e62150309b588540c27661150309d584540c25f654c0309ed95300c27661153209d58454c823e64d4f208f59353c827661d4f209d58753c823f6454e208f19153882776154e209d18553882e56110a208f992518823d64946208f992544826f62551209ed81544823e65151208f992534823d6494d208fd91534823c6454d209bd8953482776154d209d185534833854c8120cb152204825e63d50209758f540827661d50209d587540823d6595020cb189540833860550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c20d3189530823e6414c208f590530825e6314c209d98453082756114c20cb553420826d6510820b9584420834d53cc8209b59432082e9600c820cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420cb553210834d53c8420ba583210832d5448420d354d21083665148420ce55340083ab42d00209e59440083a842100209bd9520082ac64480209ed9520082b864480209b98b54c426d62d53109b98854c426d62153108f99353c423d64d4f109b98b53c426d62d4f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b10cb95252c432d5494b10d998652c432e5454b10cb55152c423e6414b108f59052c43355488710cd55121c436652487109798f548425d63d52108f993538423d64d4e108f990528423d6414a109798c528425d6314a10bc58031842f0614c21097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d109dd85534423f64549108f191524425f63549109718d524423e64149108f590524427465485109e195304425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b588530427a6014c108f990520423d64148109798c520425d63148109d984520423e64944108f592510426e62944109b58a5104275650c410d554c310427965840109dd95100427b6544010
  | 1 => 0x30901801048040a07030042600088001e11050004801000100000070041a050780404080300c02000482c083e0500808020008406000285400020086c1a010080804000083404090e028900515044220c9d9865290e756194a439b9885150e6d6214543d5d0c5150f364314543d99885150f6562145438fd954310eb46150c4397d954310ed46150c439bd895010e6c62540439dd8553d0a746154f42ab98a4350b3a4314142ce10c5050b6b4214142ce9085050a3f6550842ae1814210a6f6550842ba1814210b374254442d99095110b354254442d95095110a7a60d53329e58354cca7661d52329d587548ca7661152329d584548cb365494632cd552518cb365454632cd551518ca7761551329d185544ca7b60551329e181544ca3e64145328f590514ca7661150329d584540ca7a60150329e580540ca3e64948328f592520ca5f654c8329bd95320ca3f64540328f191500cab46150f41ae18142d066f62543419b18950d063e65d0d41c714f435071c5350d41ad185435071c53d0941c714d42506b86050941d514f415071c53905418f596431072e4354841cb10d521072d52d0441d954a411063f6550441a718d411072d52504419dd9541106d46350441d9549411063e6494b318f59252cc6e562107318fd9150cc63c64543319bd8950cc66c62543319b988548c66d62152318f992544c65f63551319dd85544c63e6515131cd153314c71c548c5319b98b540c66d62d50319e983540c67960d50318f596540c71c6355031cd185540c63e64150319b988540c66d62150319e980540c6796015031c7553430c65d6510c31cb952520c72d5494831d9986520c72e5454831cb551520c73554d0431e5d0f410c6756510431e510c410c6e5621043197d95310c69c644c4319dd95310c6b4644c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c76952540319798f54c865d63d53218f99353c863d64d4f21ba18142c86ad648cb218fd9150c863c64543219e983548867960d52218fd91538863c6454e218f990538863d6414e219e98053886796014e21b518d41886b5640c621d554c31886f1600c62197d8d544865c63551219ed81544867860551218fd91534863c6454d219ed8153486786054d219b19542486e86050921ab59232486e6618c9219b19532486746550521b518d41487a542505219d99731486b5640c521b998831486f1600c5218f596540863e64150219b988540867661150218f993530863d64d4c219d987530863e6414c218f590530866e6214c219e98053086796014c21cb553210873554884219bd95210872d54484219dd9521087355448421ae18142d02b56110a409b98a519026d6294640a718d419033651506409d98452502756114940d9984525036561149408f99
  | 2 => 0x552064383a741c4cd1fe9f8a44a0006792a5a800682980016e622fe238e63e8aa56a0c192ba79b2e159a4c280000074001968f000412108d000273142c000009842419a02936002220d000002c2761a6a8166650f600232001682fa20a9ac4058963f2f871a045d80013148320da001c0a89f24ca70998003babca3b02c59fc16b263fb364e86c08aa85d20e3d04e5e89a2d850990c4a72523822e93000b7800c611c0014ecc1e2aa8e20023e00190c70009626a7aa44ca046808668511e000a04e21e4fa823431a1c97254000b6008790e4bc304ce92ec39d45011a161640e1f6c31aa92a8abe82a001cc0687a779164f17c1a2f49e048a7a08648820b01eab10897b201494636156860240328632a3a5c2a4a21fa35a380a2283095cb509466000ce20a1b8980fa927e0000c0423a0a26f90000000000008b2266721c0bafc318c00025441800803066b18e91a90ad0446c1803c274000ccb8216ad800001b20032461800000801c2ec2e9f0b004a942242195e003120000000014000009b1b44b12634962040b8248004500000242c43080027c98000c88005e1f4000bcba9ee9ead60122a1e120bb9e06b9a2179bc42ab26d94a2a1446e9e81f0066e076352b05b24037a5a8c000c00ae0db3244820298ea84ae4609da938ec0c800ab800a118c2d08c9a1c80029a75a6e098f28daf2000600009e0010cb728c15000a501800000508004c08a98ae69c8dc461ce1a952b2a5622000b1910000ce6a1240014c62862212d0a02e8b4800001ec0005c2b31e00296002cc7080eae2e2560000f00092134728000032c48af6770000021a002beb39022c9d21032a070000007e00000000f8b225cb6a765817e04818000300008060d85c0408000000a190704004010003c02040000c3022018040401038102c09028000008050600c000281c0603018000e160000c042e020100c000480c000900008000
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x59704b4435001cf01300020510634008c54e28048024041800200042290081295c66290d42a54e5218a0a1530705095110ab038284a8885295c86150d41c30a630284a0e0c63549411072231aa4a08838518c6155031a4ae430aa818e8443588410c68a3a2a618c43a118d4250521b40e0a128290e14639454190292b94a2a0c81495c45250940a28e2a9886204a8725804310292b88c4aa0418a1886055020950e8b0064104a87458321082d0b888420041451d1530c410
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x1003240921819ca4314142c04635c86155031c80631c14250521c04635ca5150640a21811886055020
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (18887+((h/205+packedAt s3K5 (16632+(h % 205)*11) 11) % 1439)*11) 11
  | 4 => packedAt s3K4 (16974+((h/138+packedAt s3K4 (15732+(h % 138)*9) 9) % 497)*10) 10
  | 3 => packedAt s3K3 (1273+((h/8+packedAt s3K3 (1225+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s3K2 (303+((h/1+packedAt s3K2 (300+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffff81ffe1ffc1f0f87ffff87e03ff81ff3cf
  | 1 => 0xf01fffe07fff87e00ff8f87ff8fffc04627cfc
  | 2 => 0xffe0ffff801ffffff000ff87ff003fff838f0f
  | 4 => 0xffffffe007ffffff0007ffffc007fc0ff0
  | 5 => 0xffff0000000007fffffffff800000007fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x114408c5102500050381288a812285500cb1c5
  | 1 => 0x24c2914325084ca084c85c51c849a83422545c
  | 2 => 0x428aa20a0d52456a90409545520532a5830e0a
  | 4 => 0xb1444904803125329120006249600c2d40ba0
  | 5 => 0x8c18871c719c679cce64e660401823077be000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefea8a8ececa0a0fefea8a8ececa0a0fefea8a8ececa0a0fefea8a8ececa0a0fefea8a8ececa0a0fefea8a8ececa0a0fefea8a8ececa0a0fefea8a8ececa0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36364
namespace PEqualNP.Outside.L_meta_36364
open PEqualNP.Outside.L_meta_36364.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xac00000003000000f9c08016825801003189971b1a900003a5d2803c20700000039500c14890a5800b00c450000693a20000000024400f30a002a28491802000caf26840000000001010c0438f1c001801604001ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21f621fd21f521fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x12cca1001974ac16468c52e0d51a00009a248b8d22420828c86b29260b47d431c058a01b8784000001b4008a478a0ec9314a592a4434165488100144ae0000064c65e0006c4a5b278f054003c9982e00370007c0f0a1148c042709908993992824360021c7400058000c003c1603e083603124004e000000100241061326860f6151a901040000120b8004a230007416908003f2a000a600001e80a7100000763d03a885e7c001a83a1c2193068302809c4232488e0aa671c83800113117c669f0d1bd3c7e3ba2c008500285127f4726cea2304a20042b2380000614e980e422010003a5808d86000200810101820289800202810b80000202000000910080860700050b05970c8080000402810722800303888d0206104f54b439f28e873e50d0e7aa921ddd4543ba28a879f5350e7ea4a1edd45439e28a87b45150e68a2a1cf141439f2a0873d53d0a7ca3a14f943429eaa485765190aeaa3214fd4d42d7a92853c5150a78a0a14f95042bb28885755110a7ca9994f553329f2a4653d548caeca3195d546329f2a2653d544ca7ca8194f55032bb2886575510caf4a0195e540329ea9c833d529067ca320cf94241b7290836d521067aa620eb948419ea9083ad521065aa420cf94441db288833e501067ca998cf55331da20e633f548c678a918cfd51319e2a2633e540c67aa818db94831b6a9063b4410c6f4a018de540319f2a6433d54c875a8590cfd52219e2a443b641887688310edd5221da2a443b7438876a8710dd54a21dba1443b5428867ea890cf15121d6a1243b641487688290edd5121da2a243b7434876a8690f9d4921dba1243e6424876a8490f950921d2a1243e632487ca6490cf950219eaa0437651086eca3205d546409ea9c813d529027ca3206d946409b28c81b5519036c43206d486409f284813d531027aa4204f94440db10881b5211027ca0206e940409f2a6613d54cc27ea9184f152309faa2613c544c2dea4985b14930bba8a6174514c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c82eca3905d547209faa4413c54883ca43104fd51209e2a2413e540827aa8105794c20aea98417651082eaa21079484209f2a6213d54c42dca5885b54b10da20e213e548427aa9084fd51109e2a221b4414427ea8084f15010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x2805400000000000042b4000006c01800000075e640370078a093e0000000b800056704154804000580199d00010167011b25249889a64ec1a94e3188f04c050b26e40000088000685d1b5001803a1a414001c0000280100070502001850008181004c0148d98650d0e6562145438b5885150ea56214543c99885150e356214543c95885150e2562145438d18553d0a3661943428d18554cca3461551328e181544cb266154841c954a51106a562107318b588548c6356510431a9588410c7255210431cc105500c63a60d5221a958b54886b260d5221a958854886346550e218b19542486a562d0d218d19543486a56490921a999542486a46550921a9d8d42486a46050921a959232486a5644c9219958a519022d6294640a958a519032662946408d58a519032562946408958a519023765886408dd9521902346154c40c9549211023461553308d987548c23661d5220c9d51218823661d5120c955121083455348420a958841c43255210710a9588414423661d50108758c540422d6215010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x4000918087008a609c0a12b94c328687485c26154841a42e420aa018ca27099542486123aac899243281c1644c92184ae430aa6204257218554cc212b94c3aa461095ca61d5010
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
  | 3 => packedAt s4K3 (2420+((h/20+packedAt s4K3 (2280+(h % 20)*7) 7) % 96)*7) 7
  | 2 => packedAt s4K2 (502+((h/3+packedAt s4K2 (490+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffc1f87c3ffc38787fffe1c383ffe0ff13f
  | 1 => 0xf07ffe007fc787c07f8f87fe03fc3c13279cc
  | 2 => 0xff87ffff8007ffff800ff87ffc003ffc38e0f
  | 3 => 0xf0007fffffff807fffff0007fffffc01fc0ff0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x21100445090410008181288a0408985404b115
  | 1 => 0x627148c352a0a4cc42c85c5720938a8d12594c
  | 2 => 0x8423510a40a944554840954549810329430a0a
  | 3 => 0x842210040001221412000092242000a804a0
  | 5 => 0xc8c6439c6732767be764e66103063231ffe000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfea8fea8fea0fea0fea8fea8fea0fea0fea8fea8fea0fea0fea8fea8fea0fea0fea8fea8fea0fea0fea8fea8fea0fea0fea8fea8fea0fea0fea8fea8fea0fea0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36364
namespace PEqualNP.Outside.L_meta_36364
open PEqualNP.Outside.L_meta_36364.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x4078d2a0e98b0e068c08d0050000227c59532601064a0082800109294824e13009d08f0a2158014011003674b8c0004000408300704a000340ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x14400000090990c48ac0454b4d0341c087920e010015028016401313c00ccfce510c424e88514004c0074ec006c38bc1934012c015c1401686095391940c908d4006488003c0040011c00700000015400000000dc30505c0000000000b8a4000124f900c07d489c0000000058000104f4002cf14c200081600ca0a958d868b08c000000452802040c000a0c0c000000080a0a0002080a0804100e1200340200040002013e51d0e7aa921ddd4543ba28a879f5350f6ea2a1cf14543da28a87345150e7ca821dd94642baa8c853e54cca7aa9995ed4132bc282653e540ca7aa8195d94432baa88657a500caf2a0194f54e419f28c835e53106baa620db94841b6a90837a50106f2a020e794c419ea98839d531063aa620eb94841d6a90833e511076ca220ee94041dca80833e54cc67aa998e750f31da20e633f548c678a918cfd51319e2a2639d434c67ca818cf55031b7290636d520c7688218de94031bca80633e54c867aa990ed10621bd2844379508867ea890cf15121da20a437651902eaa3204f953309eaa6616f524c2d8a4984f950309eaa0616e520c2daa4185d94430baa88613e540827aa8105794c20aea98417651082eaa2107a48020b7296216d52c436883884f952109eaa4213f5444278a8886d10510
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2804aa00032402882cc0000258060010020050000000000000000000001eb869807100000003806a200100008201207266214543c95885150f326014543cc5805150e346155332c5185531070d5394841c354d52107195394041c654d50107295254041a518543cc695631073187195434c6356510431c9548410c7304154031a558c41887304154221a558c41486346155330d254d20082956310710c954841c42956310510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x68002041885896014543a0ae430aa620d11701855310688b9882a84438158d5210710
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
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s5K4 (2697+((h/30+packedAt s5K4 (2457+(h % 30)*8) 8) % 133)*8) 8
  | 3 => packedAt s5K3 (998+((h/8+packedAt s5K3 (950+(h % 8)*6) 6) % 57)*6) 6
  | 2 => packedAt s5K2 (248+((h/1+packedAt s5K2 (245+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1fe3c3f1e3fe38e3f8fc0c70e1ffe33c13f
  | 1 => 0xf1fe1fffc01fc71c0fc7f1fff80fe1c04cf9cc
  | 2 => 0x1ffe03fffe007fff007fe00fff001ff8f0e0f
  | 3 => 0xfe00003ffffff81ffff80000fffffe01f00ff0
  | 4 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa42c40448a284200860a824a41024c5411c115
  | 1 => 0x6444c4088644082402419086c824c48c04594c
  | 2 => 0x48808c911404940d10052414926081288e0a0a
  | 3 => 0x1111222010005228900020248910016004a0
  | 4 => 0x891918033899269bcd26493800c11831fba000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeecfea0feecfea0feecfea0feecfea0feecfea0feecfea0feecfea0feecfea0feecfea0feecfea0feecfea0feecfea0feecfea0feecfea0feecfea0feecfea0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36364
namespace PEqualNP.Outside.L_meta_36364
open PEqualNP.Outside.L_meta_36364.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xb004001a1af002100f5724000001300c5500600078000759224c5c03e000001f1c808800000000000000066e82273c0003f4a044a86cedb8036000005a01c2c68706190e8c0166a154b928000005e28a8206ac00624200180a000800006080040000084000c4060004100027fd5007fe54007f55007fc54017fd4c057f53017f94c05fd53015f54c05fc53017fd0c05bf43017f90c05fd43016f50c05fc43027fd4803fe52007f54803fc5201ffd0803fe42007f50803fc42017fcc803fe32017f4c803fc32027fd4401fe51007f54409fc5101ffd0401fe41007f50407fc41017fcc405fe31017f4c405fc3100ffc8401fe21007f48403fc21027fd4001fe50007f54009fc5001ffd0001fe40007f50007fc40017fcc005fe30017f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42000ff50210007f2810801bfc4084017ff9842006ff8c21005ff4610802ffd3084017fc9842006ff0c210087fe410801bfe2084001fe9042006ff0821002ffe2108003f7108400bfd8842000ffd9510005feca8803ffe65440097f32a2000ff59510005faca8803ffc65440097e32a2000ffd9110005fec88803bfe64440077f3222000ff59110005fac88803bfc64440077e322200fffd5110077fca888003fd544401dfe2a2200dffd8d1006dfec688037fe63440057f31a200dff58d1006dfac688037fc63440057e31a200dffd4d1006efea688037fe534401bfea9a200ddf54d1006ff8a688037ff434401bdfa1a200dff90d1006ffa8688037bd434401bfe21a2000ffd8910005fec488033fe62440037f3122000ff58910005fac488033fc62440037e312200fffd4910067fca488003fd5244019fe292200effd0910067fc8488003fd4244019fe212200dffcc910067fc6488037fd3244019fe192200fffd451002ffca288003fd514400bfe28a200effd051002ffc8288003fd414400bfe20a200dffcc51002ffc6288037f6314401bfe98a200dfd4c51002ff86288033ff214400bff10a2000fd88510007fa4288003f5214400bfe10a200fffd4110007fca088003fd504401ffe282200effd0110007fc8088003fa4044001fea022000fe50110077f88088037ff304401bff182200dfe8c11006ffa6088037f9304401bfe182200cffc8110007fc4088003fd2044019fe1022005ffc411002ff62088003fe1044001fb0822006ffd941002dfeca08017fe65040097f3282005ff59410005faca0801bfc650400b7e3282006ffd901002dfec808017fe64040077f3202005ff59010005fac80801bfc640400b7e320200affd501004ffca808003fd5404013fe2a02006ffd8c1002dfec608017fe63040057f3182005ff58c10045fac60801bfc630400b7e3182008ffd4c10046fea608023fe5304011fea982008df54c10047f8a608023ff4304011dfa182008ff90c10047fa8608023bd4304011fe2182006ffd881002dfec408017fe62040037f3102005ff58810005fac40801bfc620400b7e310200affd481003ffca408003fd520400ffe2902009ffd081003ffc8408003fd420400ffe2102008ffcc81003ffc6408023fd320400ffe1902005bf9841002ffea208017fe510400bfea882005ff1441002ffe8208017fe410400bfea082005ff1041002ffe6208017fe310400bfe9882005ff0c41002ffe4208017fe210400bfe9082005ff0841005dfcc00802bff500400dff2802000ff54010037f8a008027ff400400dff2002000ff50010037f88008023ff300400dff1802008ff4c010037f8600801fff200400dff1002000ff48010037f84008017ff100400bfb8802006ff8401002ff42008017fd1004001fa8802005fe44010
  | 1 => 0x3fe4148001fea0a4018ff105200bffe629005ffe314802ffe98a4017ff0c52000ffe4290007fe2148003fe90a4001ff0852000dfec090067ff5048001ff2824000ff541200cff8a090063ff4048001ff2024000ff501200c7f8809005fff304802fff1824017fe8c1200bffa609005ff9304802ffe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f8204800bffb2e2005bfd971002ffccb88012fe65c400bbf32e20049f9971002ffacb88002fd65c400bbeb2e20009f5971002ff8cb88016fc65c400bffb262005bfd931002ffcc98800efe64c400bfeb262000bf5931002ff8c988016fc64c402dffaa62015ff95310007faa988057fc54c400bffb1e2005bfd8f1002ffcc78800afe63c400bfeb1e2014bf58f1002ff8c788016fc63c4029ffa9e2014dfd4f100a7fca788053fd53c4029bea9e2014ff14f100a7fe8788053bf43c4029ff21e2014ff50f100a77a8788053fc43c400bffb162005bfd8b1002ffcc588006fe62c400bf73162001bb98b1002ffac588002fd62c400bf6b162000bb58b1002ff8c588016fc62c402dffa962013ff94b10007faa58804ffc52c402bffa162013ff90b10007fa858804ffc42c4029ff9962013ff8cb100a7fa658804ffc32c400bffa8e2005ff9471002ffaa388017fc51c400bffa0e2005ff9071002ffa8388017fc41c400bff98e2005ff8c71002fec6388017fd31c4029fa98e2005ff0c71002ffe4388017fe21c400bfb10e2005ff48710007ea4388017fc21c402dffa862000ff94310007faa18805bfc50c402bffa062000ff90310007fa8188057fc40c4029ff9862014ff8c3100a7fa6188053fc30c4027ff9062000ff88310007fa418804ffc20c400dffb2c2000bfd9610097fccb08012fe6584001feb2c2000bf59610037f8cb08012fc658400dffb242000bfd921008ffcc90800efe6484001feb242000bf59210037f8c90800efc6484025ffaa42011ff95210007faa908047fc548400dffb1c200bbfd8e1005ffcc70800afe6384017feb1c200bbf58e10037f8c70800afc6384017ffa9c200bdfd4e1005ffca70802ffd5384017bea9c200bff14e1005ffe870802fbf4384017ff21c200bff50e1005f7a870802ffc438400dffb142000bfd8a10087fcc508006fe6284001feb142000bf58a10037f8c508006fc6284025ffa942010ff94a10007faa508043fc5284023ffa142010ff90a10007fa8508043fc4284017ff9942010ff8ca1005ffa6508043fc328401b7eb0c2012ffd461002ffca308003fd518400bfe28c2011ffd061002ffc8308003fd418400bfe20c200bffcc61002ffc630802ffd318400bfe18c2010ffc861002ffc4308003fd218400bfe10c2005bf98210097fea10801bfe5084001fea842006ff1421008ffe810801bfe4084001fd2
  | 2 => 0x400fffea4a0077fe5250001fea92801dff1494001ffe84a000fbf4250007ff2128003ff509400077a84a000ffc425003dff992801dff8c9400f7fa64a0077fc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8005bf185400fffea2a0003fe5150001fea8a801fff1454001ffe82a000ffe4150007fea0a8003ff105400f7fe62a007bfe315003dfe98a801eff0c5400effe42a0003fe2150001fe90a801dff0854001dfec0a007fff5050001ff2828000ff541400fff8a0a000fff4050007fda028003ff901400077c80a000ffc4050007de2028003fe101400f7fe60a007bfe305003dfe982801eff0c1400effe40a0077fc205000dffb2c4000bfd96200e7fccb10012fe6588001feb2c4000bf59620037f8cb10012fc658800dffb244000bfd92200dffcc91000efe6488001feb244000bf59220037f8c91000efc6488039ffaa4401bff95220007faa91006ffc548800dffb1c401abfd8e200d7fcc71000afe6388035feb1c401abf58e20037f8c71000afc6388035ffa9c401adfd4e200d7fca71006bfd5388035bea9c401aff14e200d7fe871006bbf4388035ff21c401aff50e200d77a871006bfc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944006ffd8620007fcc310016fe6188001feb0c4000bf58620037f8c310073ff5188001ff28c4000ff546200e7f8a31006fff4188001ff20c4000ff506200dff8831006bff3188035ff18c401aff4c6200d7f86310007ff2188003f790c4001ff8862000ffa4310003ed2188003fe10c4001bf982200e7fea11001bfe5088001fea844006ff142200dffe811001bfe4088001fea044006ff102200d7fe611001bfe3088035fd184401aff4c2200d7f2611001bfc3088003ff9044001fbc822000ff6411001bfc2088003fc1044000ffd9520005feca900037f65480013fb2a4019ff99520025fcca90003fd65480017eb2a4019ff19520025f8ca900037c65480093e32a4000ffd9120005fec890063fe64480077f3224000ff59120005fac890063fc64480077e3224019ffd51200c7fca890003fd5448031fe2a24017ffd8d200bdfec69005ffe63480057f31a4017ff58d200bdfac69005ffc63480057e31a4017ffd4d200befea69005ffe534802ffea9a4017df54d200bff8a69005fff434802fdfa1a4017ff90d200bffa869005fbd434802ffe21a4001bfd892000ffea490007fe5248003fea924001ff1492000ffe8490007fe4248003fea124001ff1092000ffe6490007fe3248003f71924001ff4c9200bfda6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4005bf185200cffea290003fe5148001fea8a4019ff145200c7fe829000
  | 3 => 0xf322a003bf99150007fac8a8097fc64540077e322a004ffd5150027fca8a8013fd5454009fe2a2a024ffd8d50125fec6a8093fe63540057f31aa024ff58d50125fac6a8093fc63540057e31aa004ffd4d50026fea6a8013fe5354009fea9aa024df54d50027f8a6a8093ff4354049dfa1aa024ff90d50127fa86a8093bd4354049fe21aa000ffd8950005fec4a808ffe62540037f312a000ff5895011ff8c4a8006fc6254009ffa92a004dfd4950027fca4a8013fd5254001bea92a004ff1495012ffe84a808ffe4254001fea12a023ff10950127fe64a808ffe3254049fe992a023ff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a8016fc6154009ffa8aa004ff94550027faa2a8013fc515404bffa0aa000ff90550007fa82a8097fc4154049ff98aa024ff8c550127fa62a8093fc3154047ff90aa000ff88550007fa42a808ffc21540097fb02a004ffd4150027f6a0a8013fe5054001bf282a004ff14150026f8a0a8013f8505404bffa02a025ff10150127fe60a8093fe3054049fe982a024ff0c15011ffe40a808ffc205400dffb2c8000bfd9640117fccb20012fe6590001feb2c8000bf59640037f8cb20012fc65900077eb248003ffd524001ffca92000ffd5490007fe2a48006ffd8e4010dfec720087fe63900057f31c8021ff58e4010dfac72001bfc63900057e31c8021ffd4e4010efea720087fe5390043fea9c8021df54e4010ff8a72000fff4390007dfa1c8003ff90e4001ffa8720087bd4390007fe21c8006ffd8a40107fcc520006fe6290001feb148000bf58a40037f8c520006fc6290045ffa948020ff94a40007faa520083fc5290007ffa148003ff90a4001ffa852000ffc4290043ff9948020ff8ca4010ffa6520083fc329000dffb0c8000ff9864002dfcc320003fd61900017eb0c8006ff18640117fea320003fe5190001fea8c8022ff1464001ffe832000ffe4190007fea0c8003ff1064010ffe6320087fe3190043fe98c8021ff0c640107fe4320003fe2190001fe90c8020ff0864001dfcc12008bff509000dff2848000ff54240037f8a12000fff4090007dfa048003fed0240037f8812000ff84090043ff9848006ff8c24010ffa612001bfc3090041ff9048006ff08240007fecaa0002ff6550001bfb2a80009fd95400fffccaa0012fe6550001feb2a8000bf595400fff8caa0012fc6550001be32a80049f1954001dfec8a000fff5450007ff2a28003ff5514001ff8a8a007bff635003d7fb1a801eff98d40015fcc6a007bfd635003d7eb1a801eff18d40015f8c6a007bff535003dbfa9a801eff94d400f7faa6a007b7d535003dfe29a8003ffd0d4001f7e86a000ffe4350007fea1a801eef50d4001ff886a0003ff62500017fb12801dff9894000dfcc4a0003fd625003bfe3128001bf189
  | 4 => 0x8b3f5318840bfe18c4205ffc862102fde4310807f7218840bfe10c4205fd0862102ffec110817fe60884017f3044205ff58221005fac110817fc608845dffa84422eff1422116ffe81108b7fc4088459ff984422cff8c221167fa61108b3fc3088403ff9044201ff08221007feca90802ff6548457ff32a4204bf99521007faca90802fd6548457fe32a4204bf19521007fec890802ff6448455ff3224203bf99121007fac890802fd6448455fe3224203bf1912115ffea8908abfe5448401feaa2422aff1512114ffec6908a6ff6348453ff31a4202bf98d2114ffac6908a6fd6348453fe31a4202bf18d2114ffea6908a77f5348453ff29a4229ff54d2114efaa6908a7fc5348453ffa1a4229efd0d2114ffc86908a7fd4348453dea1a4229ff10d2102dfec490807ff5248403ff2924201fb9492100ffaa490803ed5248403fe2924201ffd092100ffc8490807ee4248403fea124200fb5092100ff88490807ff3248403ff1924201fb8c92100ffa64908a7ed3248403fe1924201bfd852115ffea290817fe5148401fb28a4200ff54521007eaa290817fc5148455ffa0a422afdd052102ffc8290803fd414840bfe20a422afd1052114ffe6290817fe3148453fb18a4229ff4c52114fea6290817fc3148403ff90a4201fdc852102ffc4290817ee214840bfe10a4205fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc60484017e302422bffd412115ff8a0908abff4048455fe2024229ffcc12114ffc60908a7fd3048453fe1824201ffc812100ff84090807ec20484097eb2ca006ffd9250147fcc92800efe6494001feb24a000bf59250037f8c92800efc6494009ffaa4a004ff95250146fca928013fd5494009fe2a4a004df15250037fec72809eff639404fff31ca002bf98e5013ffac72809efd639400dfe31ca002bf18e50027fea7280137f5394009ff29ca004ff54e5013efaa728013fc539404fffa1ca027efd0e5013ffc872809ffd439404fdea1ca027ff10e50037fec52809bfe62940037f314a000ff58a50005fac52801bfc62940037e314a004ffd4a50027fca52809b7e5294009fea94a004ff14a50026f8a5280a3ff429404dff214a000ff50a50137f8852809fff329404dff194a027ff4ca50137f8652801bff6194001ff30ca005bf98650007fac328002fd619400dfe30ca004ffd4650026fea328013fe5194009fea8ca000df54650027f8a3280a3ff4194001ff20ca000ff50650147f8832809fff319404fff18ca027ff4c65013ff8632809bff2194001ff10ca000ff48650137f84328012fe6094009ffa84a004dfd4250027f6a12801bfc5094009fc284a028ffd0250037f8812809fff309400dff184a027ff4c250037f8612809bff209400dfe104a004bfd9550007fec8a8002ff645404bf
  | 5 => 0x4e4119ffca7208cffd5390467bea9c8233ff14e4101ffe872080fbf4390407ff21c8203ff50e4119f7a872080ffc439040bffb148205ff98a4100dfcc520817fd62904017eb148205ff18a4102df8c5208d3ff5290465ff2948200ff54a41197f8a52080fff4290407ff2148203ff50a4101ff885208cfff3290465ff1948233ff4ca41197f86520816fe619040bffa8c8205ff9464102ffaa320817fc519040bffa0c8205efd064101fee8320817fc419040bfa20c8205ffcc64102ffc6320817fd319040bfe18c8205ffc864102ff84320817ff609040bff3048200bf9824102ffac120802fd609040bfe3048234ffd42411a7f8a12080fff4090407fe2048233ffcc24119ffc61208cffd3090467fe1848232ffc8241197f84120803ff65504017fb2a8200dfd9541004fecaa08c7fe65504097f32a8200ff59541005facaa08c7fc65504097e32a8200df19541024f8caa0816ff6450407ffaa28203ff9514101ffaa8a080ffc5450461ffb1a8230bfd8d41187fcc6a080afe6350461feb1a8230bf58d41187f8c6a080afc6350461ffa9a8230dfd4d41187fca6a08c3fd5350461bea9a8230ff14d4101ffe86a080fbf4350407ff21a8203ff50d411877a86a080ffc4350401ffb128200bfd894117ffcc4a0806fe6250401feb12822fff1894100df8c4a08c7ff525045fff2928200ff5494117ff8a4a080fff4250407ff2128203ff5094101ff884a08c3ff325045fff1928230ff4c94117ff864a080eff6150463ffa8a8205ff94541007faa2a0817fc5150407ffa0a8203fdd054102ffc82a0817be415040bfe20a8205ef1054101fe882a08c3ff315040bff18a8230ff4c54102ff862a08bfff215040bfe10a8200ffd8141005fec0a0803fe6050401feb028200ff18141005f8c0a08c7ff5050463fe2828203ffd014101ff880a08c3ff3050461ff1828230ff4c141187f860a08bfff205045ffe1028205ffd962102dfecb10817fe65884097f32c4205ff59621005facb10817fc658840b7e32c4205ffd922102dfec910817fe64884077f3244205ff59221005fac910817fc648840b7e324422effd522116ffca910803fd548845bfe2a44205ffd8e2102dfec710817fe63884057f31c4205ff58e21165fac710817fc638840b7e31c422cffd4e21166fea7108b3fe5388459fea9c422cdf54e21167f8a7108b3ff4388459dfa1c422cff90e21167fa87108b3bd4388459fe21c4201bf58a2100ffea510807fe5288403fea944201ff14a2100ffe8510807fe4288403fea144201ff10a2100ffe6510807fe3288403fe9944201ff0ca2102dfcc310817ff518840bff28c4205fd9462102ffaa310803f5518840bfe28c4205ffd062116fee8310817fe418840bfea0c4205ff1062102fe88310817ff318840bff18c4205fd8c62102ffa6310
  | 6 => 0x7fe98a843bff0c54200ffe42a1007ef2150803fe10a8400ffd8142005fec0a1003fe6050801feb028400ff18142005f8c0a10f3ff5050879fe2828403ffd014201f7e80a100ffc4050877ff982843bff8c1421dffa60a10effc3050803ff9028401ff08142025facb28817ff649440bff324a203bf9925102ffac928802fd649440bfe324a205bf19251027fea928813fe5494475bf2a4a204ff55251027f8a9288137c549440bffb1ca205bfd8e5102ffcc72880afe639440bfeb1ca239bf58e5102ff8c728816fc6394409ffa9ca204dfd4e51027fca728813fd5394473bea9ca204ff14e511cffe87288e7bf4394473ff21ca239ff50e511cf7a87288e7fc439440bffb14a205ff98a5100dfcc528817fd62944017eb14a205ff18a5102df8c528813ff5294409ff294a204ff54a51027f8a5288ebff4294471ff214a200ff50a511c7f885288e7ff3294471ff194a239ff4ca511c7f86528816fe619440bffa8ca205dfd4651027eea328817fc519440bfa28ca205ffd065102ff88328817ff319440bff18ca205ff4c65102ff86328817ff219440bfe10ca205ffd825102ffcc128802fe609440bfeb04a200bf5825102ff8c128813ff5094409fe284a23affd02511d7f881288e7ff3094473ff184a239ff4c2511cff861288e3ff2094471fe104a205bfd9551007fec8a8802ff6454401dfb22a200afd91511bffcc8a880efe6454401feb22a237ff1915101df8c8a8803bc64544075e322a204ffd5151026fea8a8813fe5454409feaa2a200df55151027f8a8a88dbff635446d7fb1aa236ff98d51015fcc6a88dbfd635446d7eb1aa236ff18d51015f8c6a8813ff5354409bfa9aa204ff94d51027faa6a88db7d5354409fe29aa236ffd0d511b77e86a88dbfe435446dfea1aa236ef50d511b7f886a8803ff62544017fb12a235ff9895100dfcc4a8803fd625446bfe312a201bf18951027fea4a88137f5254409ff292a204ff54951006faa4a8813fc525446fffa12a235ff90951007fa84a88d7fc425446dff992a235ff8c9511b7fa64a88d7fc32544097fb0aa204ffd4551027eea2a8817fe515440bbf28aa205ff1455102ef8a2a8813f4515446fffa0aa205ff105511b7fe62a8817fe315446dfe98aa205ff0c5511affe42a8817fc2154401ffb02a200bfd8151007fcc0a8803fd6054401fe302a200bf18151027fea0a8813fc5054409be282a237ffd01511bff880a88dbff305446dff182a236ff4c1511b7f860a88d7ff205446bfe102a205ffd964102dfecb20817fe65904097f32c8205ff59641005facb20817fc659040b7e32c8203bf5924101ffea9208d3bf5490407ff2a48203ff5524101ff8a92080fbc549040bffb1c8205bfd8e4102ffcc72080afe639040bfeb1c8233bf58e4102ff8c720816fc6390467ffa9c8233dfd
  | 7 => 0xaa013bf5455007ff2a2a803df9515401ff8a8aa00f7c5455007de2a2a840ffd8d54205fec6aa103fe63550057f31aa840ff58d54205fac6aa103fc63550057e31aa804ffd4d54026fea6aa013fe5355009fea9aa840df54d54027f8a6aa00fff4355007dfa1aa803ff90d5401ffa86aa103bd4355007fe21aa800ffd8954005fec4aa0fffe62550037f312a800ff589541fff8c4aa006fc6255009ffa92a804ff94954027f8a4aa00fff4255007ff212a803ff10954207fe64aa0fffe3255081fe992a83fff0c954007fec2aa002ff6155001ff30aa800ff58554007f8c2aa016fc6155009ffa8aa804dfd4554027f8a2aa00fff4155007fe20aa840ffcc554207fc62aa103fd3155081fe18aa83fffc85541fff842aa003ff60550017fb02a800ff98154007fac0aa003fc60550017e302a804ffd4154027f8a0aa00fff4055007fe202a840ffcc154207fc60aa103fd3055081fe182a83fffc81541fff840aa006ff6554801ffb22a400bfd91521f7fcc8a900efe6454801feb22a43eff1915201df8c8a9013ff5454809ff2a2a43edf95152027faa8a9013fc5454809be2a2a43dffd8d521edfec6a90f7fe63548057f31aa43dff58d521edfac6a90f7fc63548057e31aa404ffd4d52026fea6a9013fe5354809fea9aa43ddf54d52027f8a6a90f7ff435487bdfa1aa43dff90d521effa86a90f7bd435487bfe21aa401bfd895200ffea4a9013ef5254803ff292a401df9495200ff8a4a90077c5254803f6292a401ffd095200ffc84a9007fc4254803ff992a401ff8c95200ffa64a9007fc3254801ffb0aa400bfd8552007fcc2a9003fd6154801fe30aa405bf18552027fea2a90137f5154809fe28aa43effd05521f7f882a90f7ff315487bff18aa43dff4c5521eff862a9007ff2154803f790aa401ff08552007fec0a9002ff6054801ff302a400ff58152007f8c0a9002fc6054809ffa82a404dfd4152027f8a0a90fbff405487dfe202a43dffcc1521effc60a90f7fd305487bfe182a401ffc815200ff840a9003ff65508017fb2a843cff99542025fccaa1003fd65508017eb2a843cff19542025f8caa1006ff6450807ffaa28403ff9514201ffaa8a100ffc5450877ffb1a843bbfd8d421dffcc6a100afe6350877feb1a843bbf58d421dff8c6a100afc6350877ffa9a843bdfd4d421dffca6a10effd5350877bea9a843bff14d4201ffe86a100fbf4350807ff21a8403ff50d421df7a86a100ffc43508037fb128401ffd494200ffca4a1007fd5250803fe2928401ffd094201fde84a1007fe4250803df2128401ff1094200f7884a1007ec4250803ff9928401ff8c94200ffa64a1007fc3250801ffb0a8400bfd8542007fcc2a1003fd6150801fe30a8405bf185421e7fea2a10f3fc5150807ffa0a8403ff105421dffe62a10effe315087
  | 8 => 0x1f30008c80001f400005c8000720000310b180000015db2800000032101c80022396da2f00013a9af10fa24a9e009800374070b3b8000000000000af8002b102da2d16cafc2b303ba6d11f80017c00032cb1900033fa821220002122e9a8705bb408000690000002480000e3361b3c283a260e0096950336000000000000c01800000c00001000000002400000800400800001400000000c00000801000000400801800803c01000800000405400000800000000c00000400001c00000000000001c00c00001002000c00400400400400000000000801c00400001c01000001000000001403400000400801800800c01400005400400401003000001400c03000802800807400006406000400400000002c01403400000403c00400002802800400400401000000000800c00400c04800000800400804401001400800404400000002c01400400c02400004800004801800000000400c01c04000400800000000001400004400000c00c01001000000000400000001001800000400400800800c01002000800c00005804814804c01001400400002000001c01c02800800801002804000000405400c00800403003801000000401800000802003800802802401801400000400000000000000003c00400000000400400000000000c00000c00003000c00000400800000801801c00800401000000002c02400401400401800000401000001000000400000c00400401000001400000804c00c00000000400803002000c00001001001400800003001400001400000800405400001c01000402400401000000400005c01000400000800801c00c04c02800000402c00401400000801c00000000802c02005000400400c00003800000800400401400800400001402802001001401400000000400800c01001002402c00000c00000c0380100080000000000100100000000000100200340b803800000800000c02800401800800000000401800001401800000400400c00000400000000000402400c02c00800000c00000801400801c02800000800402002402001403401000000800400000000401c00800001000000000000000000c00401000400c00c08000000000002001c00400800400406400406000000000801804c01000002003800400c00c00400400000c01001000001802800c00000c01000c03400c00000000000400002401401000000800402800002c03000400000000400400000000000401c00401400000400c00400c00400800400002000000c00001000004c00000000400400000800000402c00400400400400400002c03c00802400c0000340000080000040080240000100f800800401000400c000000008024000018000000000034000000014014004000004000008008000004004000018000077fb2aa803bfd915401ffea8
  | 9 => 0x290000000ec8eb8001dc3628bb979a4f0a018480d0e39fdaff2de2350002580cc80000d9db2241359a899080022510a01231f2618e108c8001fb8000001ac8a789b00000000f2c60000001938001d50000000000001411842692680b69ab11c0de80900010400030a97782a11d0000bdb320002180001ca8002c41f390c97607b2c8a19a030a4850a8f82b12d80000014c814293b0300000000000007b8001770002d1130296a3f8d80002a584f0fc14aa5b86409f1619ba00000019780000000b1b9303b088000000000000000000000001c384f80000000000000000780000000028400000000000000000000000016410bafb8000288003600000000003460001551438002e51ad283045a322549480f58f42a90da2be9461f13608cab3a171aee0000000000001e6114808a578ec12aa329c59b005a0003021782a32fb1a991d9db8270d22d806b19a84a0fba31880a088850261ea05aa720d01e295925597212094700000000000000034180019f2161bd0000000000000000001a1a8014900017cb1b99980003d26890f000000000011b248990002ac0bb1331fa81c0000000f380000000000024d21394d800376b1203589390e000000368a649cd9fe8000003649418000918af31809cb1ea0c98e00820f0001cea378733510002389e21488000000000001c234d80021f800211227aa48d78df0000000000000002c38002170000b815f35d8000b91cb0002ef8000000000f10002da0000002d78000000000000001752b90859e40000002a704d8000001a025c2929859cd01a916000346ad3ac927f0000e89758888002f80002148000000000000b40a980028b0001ce1d49f5b43044ad18002c0a4983b2c18000761f68001f90e28001fd0000002d69268000180002620000001aa2d202b8578001258550f032688182199c0753690332390e6a3f29080008b8000b11df9ef0e50000000000a10002158f0b5a0001d200000036c00014c31980011094517d80023c2f41d0a781a3a771eb2bf35e00000000000000000016126cafd1f017eae79458661b417a8e626022b00016380000000024532982d29191821ba5e83a1d18e23590c205d0a400000030f2ad2768002470d28002298408000002778000670b89ee8848000003241088000c60411e3a8e9bea5fa140468000000000000002ac80000000009a8000000000438df8000003008000000001240000000d10042cb00028516a83c1cc05e0002ae0e72ca24eb4c80035480000aaef25a0233722d28001589959d28002c100000014ba9580014fa1d800000000371077a9821aab1a5c9328322a50058000a281d8001a79fc810ad517f0ce8592608000b48e08001e300000000003e2e58000000002cb9a6b2305187cb259b1aec2b4b028a591b8aa039b4298219b26d8002ed028
  | 10 => 0x2ba8b98f296305829d1ff8251698bc16e80008e06780cb0684b0001b79990dd9b58c70000000862b9a05b4f8870000499ae27f80036c8000001c921e0002b00000fd80000000023c92810d80035200000000027900018f80015b80004ab0a0002c80d4026a5a81f2c2212b6391eac4a2094f0792f990b1678000002881388001540258c1904a362f692c21d10280002229118ba1a00025336aa788003698a318803895e8000000000a3a8605200024023993223a8a92e313e80f9ab80025d2be24180000032c0bf0000a601b80028e04800000000e9f287280034a0820940012cca0800000000009e83714208d2ca84b8c280000000029219e22f9c080000018a8000001570000000000000000003388000e7a008002ad800298800112ab21378000000000000002810ed9d300028c2af00005c090074985000311a01b019dd36ea8a8c08000000000a0aa8357b459a730b800162086800226acc00000026a26118286b80000009d30e80000031b0000c10028c9000069a52aab8b327411b28b8000000c78000000000003453750002bd1648001b21578003149a480022bae68c317b179358b7480180000014d0002a992295c245b1e09e27babc24385f9a3228ab38cd285b4c17fb6a180b560002a7919061000273adda8884880023a00035020900020a0002c98001f50000001178001ed2edb6f81133c9249a421e8830491312a3a8c800000000153879af000000029a0000000d6b728000ef0a8970a7e8000000000003318000bf80000011880002c9910000161de93380000034d0000000000e480000000014a0d08003438dc913b138be09d9729051cc9c83410e19bd99e8002f287fb0c80000000000000000026b80a150a2716a151a4a31c8001a52c58002b08002f600030815e00030f80011300022a00012b00011ca30a4db731b2919804b6694e84e1bc1e8903852adb0d588a966adf2cd317a0a837adcb1a24894087d8cc18d2e02a20319002ea8c9a101c107c24a80025918980016c2a0349a0da9ba1c2e91b52332d60b3a65a898622f7a368303328bd18e8b61800000c3b6e32d8ba32f0aea50b309f9819b1080028a2bb1d936787d00013a162800000000000000000335b333239f802780003f9e823e00000031f83081026515685f0003292d71230f834b00000023486c0003610000000001c30002d58001860002df800305b5533494e1a218b3090ff80007a0532bcac2ab8b07299af59879bb95a82102393c09707e0cf8629510023622709a29169d886ab0012eb350ce00032aa343208001948ee8560000000651de0003519bc9710beb3aa9329cb28a4ca8f0440a1a231319171f20ca000000322a7b15f8d300034900000022013480027000031da2d8f78e81298001d99bf00011500000035c842a3126b0003010999d40
  | 11 => 0x147a46b528001a113400014b1a580007a90208122129aad488b3738000000b08b700016080000003c8000000fb2429af89bb1a8000003390f90000000002e08781eb80013e00000011a00030e0000131892e4a0e2a280002c09480006308296b92000016b00000000008d800206b278000001700001520000fd0000001549ee37186e218abb8dd2542bf8000002cf0003102a62a89c896d0000f9b338002d90840000002ea2978000a20193709e58002fe35b16700020b2ce33980018a1950e5a0c1f1a59a2e2010638fa84e80024200025380027a8000c49260000000f89d100000000000000000000000016900012500000015a3098b782413b0000001008000002730d61b30170c58000349401fe0bab110fc8b225f2f90569e180001580013b92b9b13368cf00000007e9a080000036f1658cb0b580008800013d0002e1a47a7dac00a68390599889091b99900000f712199baaa84c9370168000510002d095b219000240afa8001f48a50000340539030002e20001b38002c700001e1739102c3216883854800000000000000000006b370000001c18000002ce9eab630001e10001fa00018c0e92af8500003378001392152f197e00023599436ba3b8139d58960000001f70002460000ea0001352ae84700000001781d000123b448000000dc16f80002e00020b9599083700000001f09c78000001d834ba62b5eb0d000266a118000001ec0001749558000000ed0000000efa179dcaeb068ae7000000279a970001df30d93605b0f6ad407102f83ea58800000000000000000089a641e786680000026eb4f00000026600000000030c00027c2cf80000000000000000026996006a0a826c28d87731c33eb0524b0b2b3da9021332700026e1d7a89263af39f6115aab13f85dac78f534eb2e8418000002940cbb2ba9536718f0001869f88000d91ff1e51b08328000ac85436d1e080010114280b8d98001c4b14101a3d0de1c503601497b9e71213152fda490700db0380001919789c9800350b5592f000287a719a61c69d701521f3569819cba2c8d52eb8f60001c0207abd80009f9058002f2000225aeea55097b680659ad9e6a5b0f21ae91a8000000000000cd9ba8002568000002b682f00009a00022932d1cf0400001e0000000281a0991e2dd35f25011f000130a0fb53b3f2728f30d73222000002048003421c2ae13652220002dc04319d958095047a80a028000000d38000000000000001d6a9f149a84939a4b9730f495c8001bfb312e880029e91214315281a37601e8000003159e48f1a82a513480fe0b000620380000000033b09833400002a86829484d0893300d4b6619727124f80000000031899f800000000168ab2a7a31d0588000000a70001830921edaa0a1b1969fc18d86c90a80000007f0003078c02d980000000000000
  | 12 => 0x233afe8001cf9b480012f80000000000024127d3128000000e400029f8bc9e98000001530c680025d9b70adad89d00000460000002ba3160ac0002da88c00000019831714480000000000013d80019d00000000020d198a0630400012780010c0802a100025e00026f80000013caa1a7e19a29b03a8000000000000ad1118002c510d06090e80000012e32e33d27c992ab78039b80769bb2f70002db82280000000006ea9dab60000001078000000002ecafa26f00009c0000e98001e90ea88780000000000012880708a1290001be0000d18003641d60001da2d30188000aa96f2b73048000002370c880034a99602eb2f8030002f10000ff0000000000ae00000000000001fb5a820a2c000267263192340299000109aa6a072ff976a4e0001b600004c1b6b252f88000000003063260d8906000000060230055b6b000286b6d97d2deab417408fb2023d86da3b00000000012729c33e0128738000001681c400018cab800000020e8000743168000001aa96620434e0788003473572fc93f30b2cd89592d00020232b0759070000eb0fe9eca752f521c9fb00000035d00006180000021080006f8001da89080000032a00c0002f48002e80ee1469ac09312c99caf30001ddae615d1f783f243358091098800024b5f800000274b21a67a381b88ab2520dbb48800365b5b85e8000001110000001efa281650001c7092a2eb599381d397a071b5c0daa6a8350c422a8ab82980e3758002f0936b5306d24c23e9141c603da76221ae42aa0572d025708ea8d020106833a4425188f16e2e2ab50000c500012a0002050002962c69a8000000005000000036800064a560000450000000001838001810b51a90000003442758002b586f3541442e39870000003130001561932a40000000003479ca000222800244b3801b0fa042
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x7714811002df4714811002dfa708411002efb608411002df67684110036f6768411002cf67684110035f7738411021df57384110217775384110217755384110217b74384110217b54384110035f77284110005f57284110035f67084110036f7608411002ff36084110037f24084110007f14084110037f23084110217f13084110034ff75594100367f7559410004ff745941001cfe745941001cfc74594100567f5459410004ff7359410014fe7359410004fd7359410014fc73594100567f53594100067d5359410006bf4359410006bd4359410004ff725941000cfe725941000cfc72594100567f525941002cff715941002cfe715941002cfd715941002cfc715941002e7e515941002e7c5159410024ff7059410034fe7059410024fd7059410034fc70594100367e50594100367c5059410004ff75590100067f75590100047f7559010024fe7559010024fc75590100067c75590100247c7559010034ff7459010036bf745901004ebe5459010004ff7359010014fe7359010004fd7359010014fc73590100067f53590100067d535901004ebf4359010006bd4359010004ff725901000cfe725901000cfc725901004ebf425901002cff715901002cfe715901002cfd715901002cfc715901002ebe415901002ebc415901001cff7059010034fe705901001cfd7059010034fc7059010036be4059010036bc405901002efa105901002ef91059010004ff7655010034fe7655010004fd7655010034fc76550100267e65550100067d655501001ebe6455010006bd6455010004ff7558810024fe7558810024fc7558810004ff745881001cfe745881001cfc7458810004ff7358810014fe7358810004fd7358810014fc73588100067f53588100067d5358810006bf4358810006bd4358810034ff7258810036ef725881003eee525881003eee425881003eee3258810006ed325881002cff715881002cfe715881002cfd715881002cfc715881002eee215881002eec215881000cff7058810034fe705881000cfd7058810034fc7058810036ee2058810036ec205881002ef71058810004ff7654810034fe7654810004fd7654810034fc76548100267e65548100067d655481000eee6254810006ed6254810004ff7650810034fe7650810004fd7650810034fc765081001ebe6450810006bd645081000eee6250810006ed6250810094ff765401008cff76500100057f75500100557c755001008efa6050010084ff76480100057f75480100557c7548010037e82048010035f77644010006f77644010004f77644010036f7634401020ef5634401020f77534401020f75534401020fb7434401020fb54344010036f76244010006f56244010035f7704401002ff37044010036f66044010037f26044010037f2304401020ff13044010
  | 1 => 0x8910006fb7058910006fa3058910006f93058910066ec2058910004ff7654910004fe7654910004fd7654910004fc76549100267e65549100067d6554910005fb7054910005f87054910004ff7650910004fe7650910004fd7650910004fc7650910024fc76545100067f65545100267c6554510005bf7454510075bc745451002f745154510005fb7054510005f8705451001cfc76505100057f755051007d7c7550510006bf645051001ebc645051002fb44150510005fb7050510005f87050510005f6768851002ef67688510006f76588510006f5658851016ef6648851016ef4648851002df7738851025df57388510256f76388510256f56388510257775388510257755388510257b74388510257b54388510065f5728851000ef6628851000ef46288510035f6708851002ef7608851002ff36088510257f23088510257f1308851000cfc7648510006ef624851000eec6248510005fb7048510005f87048510065f4764851000ef4764851000cf47648510006f76548510006f56548510156f66448510156f4644851024df7734851024df57348510246f76348510246f56348510247775348510247755348510247b74348510247b5434851002df7724851002fe77248510007e7624851000ef6624851000ef46248510067e46248510067e65248510007e55248510067e64248510007e54248510067e63248510247e53248510007f37048510035f47048510007f0704851002ef7604851002ff36048510247f23048510247f13048510067e420485100b4fe76941100267e65941100067d6594110024ff765411007cfd765411002cfc76541100067f65541100267c6554110005f7715411002df471541100acfe7690110005fa76901100aefa7690110075f9749011001efa649011001ef8649011023dfb739011023df973901102377b5390110237795390110077bb4390110237b9439011002dfa719011002df87190110036fb6190110237f23190110237f13190110007f22190110007f1219011001cff7650110074fd765011002cfc76501100057f755011007d7c7550110006bf645011001ebc6450110005f7715011002df4715011002df8765011001ef8765011002cf876501100077b7550110007787550110075fb7450110007bb7450110007bb645011001efa645011001ef86450110077b8645011022dfb735011022df973501102277b5350110227795350110077bb4350110227b94350110077bb4250110007b94250110007f3715011002dfa715011002df87150110007f07150110227f23150110227f13150110007f22150110007f1215011009cfe768811000eee6288110006ed6288110007e5218811000cff7648110064fd764811002cfc76481100057f754811007d7c7548110006ef624811000eec6248110005f
  | 2 => 0xcfc72d95100067e52d951007e7c52d951002cfe71d951007cfd71d951002cfc71d951007e7f51d9510034fe70d951002cfd70d9510034fc70d951007e7f50d951007e7c6559510005bf7459510075bc745951007cff75595100067f7559510004ff7459510006bf7459510004bf745951001cfe745951001cfc7459510006bc745951001cbc7459510004ff7359510014fe7359510004fd7359510014fc735951007e7f53595100067d5359510006bf4359510006bd4359510004ff725951000cfe725951000cfc725951007e7f5259510094ff7159510006f771595100b4ff7059510006fb705951007e7c505951001cfe76d9110076be64d9110024fe75d9110004fd75d9110024fc75d9110006bf54d9110076bc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d91100067f53d91100067d53d9110076bf43d9110006bd43d911000cfe72d9110004fd72d911000cfc72d9110006be42d9110076bc42d911002cfe71d9110074fd71d911002cfc71d9110076bf41d9110034fe70d911002cfd70d9110034fc70d9110076bf40d91100057f755911007d7c7559110076bc6459110004ff75591100067f75591100047f7559110024fe7559110024fc75591100067c75591100247c7559110074ff7459110006bf7459110004ff7359110014fe7359110004fd7359110014fc73591100067f53591100067d5359110076bf4359110006bd4359110004ff725911000cfe725911000cfc725911008cff7159110006f771591100acff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc7655110005f7715511002df4715511000cfe76d8910066ee62d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d8910004ff73d8910014fe73d8910004fd73d8910014fc73d89100067f53d89100067d53d8910006bf43d8910006bd43d891002cfe71d8910064fd71d891002cfc71d8910006f631d8910006f531d8910066ef21d8910034fe70d891002cfd70d8910034fc70d8910006fa30d8910006f930d8910066ef20d89100057f755891007d7c7558910005bf7458910075bc7458910005df735891006ddc7358910066ec6258910004ff75589100067f75589100047f7558910024fe7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc73589100067f53589100067d5358910006bf4358910006bd4358910064ff7258910006ef7258910066ee3258910006ed3258910084ff7158910006f77158910006f63158910006f5315891009cff705
  | 3 => 0xd7359210014fc73592100067f53592100067d535921008ebf4359210006bd4359210004ff725921000cfe725921000cfc725921008ebf425921008ebf4159210034fc7059210036be4059210036bc4059210004ff7655210034fe7655210004fd7655210034fc7655210024fe75d8a10004fd75d8a10034fc75d8a1001cfe74d8a10004fd74d8a10034fc74d8a10034ff73d8a10014fe73d8a10004fd73d8a10034fc73d8a100067f53d8a100067d53d8a10006bf43d8a10006bd43d8a10084fd72d8a10036f571d8a10036fa70d8a10036fa30d8a10006f930d8a1000cff7658a10036ec6258a10004ff7558a10024fe7558a10024fc7558a10004ff7458a1001cfe7458a1001cfc7458a10004ff7358a10014fe7358a10004fd7358a10014fc7358a100067f5358a100067d5358a10006bf4358a10006bd4358a10036ef7258a10086ee3258a10006ed3258a10086ef2158a10034fc7058a10006fa3058a10006f93058a10036ee2058a10036ec2058a10004ff7654a10034fe7654a10004fd7654a10034fc7654a100267e6554a100067d6554a10005fb7054a10035f87054a10004ff7650a10034fe7650a10004fd7650a10034fc7650a1001ebe6450a10006bd6450a10024ff7654610034fc76546100267e65546100067d6554610005bf745461008dbc7454610005fb7054610035f8705461001cff7650610034fc76506100057f75506100957c755061001ebe6450610006bd6450610005fb7050610035f8705061000cff7648610034fc764861000eee6248610006ed6248610005fb7048610035f87048610054ff7654210035f97690210036f9769021002cf9769021001efa6490210037ba6490210037b96490210036f86490210035fb7390210285f9739021027f7b539021027f79539021008fbb439021027fb9439021002dfa7190210037f27190210037f17190210035f8719021004cff76502100057f75502100957c7550210005fb765021004efb76502100077b7550210007787550210037bb745021001efa645021001ef86450210275fb7350210275f9735021026f7b535021026f79535021008fbb435021026fb9435021008fbb4250210007b9425021002dfa715021002df8715021003cff76482100057f75482100957c7548210035f576c421002ef576c421002f7675c421002f7575c4210036f763c4210266f563c42102677753c42102677553c4210267b743c4210267b543c421002fe672c421002fe572c4210036f762c4210006f562c4210037f260c4210024fe76d951007e7e65d951001cfe74d9510004fd74d951001cfc74d95100067e54d951007e7c54d9510004ff73d9510014fe73d9510004fd73d9510014fc73d951007e7f53d95100067d53d9510006bf43d9510006bd43d951000cfe72d9510004fd72d9510
  | 4 => 0x4b1002cfe7654b10004fd7654b1002cfc7654b100267e6554b100067d6554b1000eee6254b10006ed6254b10004ff7650b1002cfe7650b10004fd7650b1002cfc7650b101e67e6550b100067d6550b1000eee6250b10006ed6250b1002df7764871003ef7764871002ef7654871002f766548710006f5654871002f756548710006756548710156f6644871002ef46448710295f77348710295f5734871002ef7634871028ef5634871028f77534871028f75534871028fb7434871028fb5434871002fe7724871000ef6624871002fe6624871000ee6624871002fe5624871002ef4624871009fe65248710007e5524871009fe64248710007e5424871009fe6324871028fe53248710035f4704871009fe4204871007cfd76943100267e65943100067d6594310136ee6294310006ed6294310024ff765431002cfc76543100267e65543100067d655431011eee6254310006ed6254310005f7715431002df47154310074fd76903101167e65903100067d6590310106ee6290310006ed629031001cff765031002cfc76503100057f75503100b57c75503100fe7e65503100067d655031001ebe6450310006bd64503100eeee6250310006ed6250310005f7715031002df47150310064fd76883100e67e65883100067d658831000eee6288310006ed6288310035f47188310007e5218831000cff764831002cfc76483100057f75483100b57c75483100ce7e65483100067d654831000eee6248310006ed6248310005f7714831002df4714831009fe82048310094fd75d961001cfe74d9610036be74d961001cbe74d9610004fd74d9610036bd74d9610004bd74d9610034fc74d9610034ff73d9610014fe73d9610004fd73d9610034fc73d96100967f53d96100067d53d9610006bf43d9610006bd43d961000cfe72d9610004fd72d9610034fc72d9610036f571d9610036fa70d9610024ff76596100367c65596100367f7559610004ff745961001cfe745961001cfc74596100067e54596100967c5459610004ff7359610014fe7359610004fd7359610014fc73596100967f53596100067d5359610006bf4359610006bd4359610004ff725961000cfe725961000cfc72596100967f52596100967f5159610034fc70596100367e50596100367c5059610024fe75d92100367e75d92100247e75d9210004fd75d92100367d75d92100047d75d9210034fc75d921008cfd74d9210034ff73d9210014fe73d9210004fd73d9210034fc73d92100067f53d92100067d53d921008ebf43d9210006bd43d921000cfe72d9210004fd72d9210034fc72d9210036f571d9210036fa70d921001cff7659210036bc6459210004ff7559210024fe7559210024fc7559210036bf7459210006bf545921008ebc5459210004ff7359210014fe7359210004f
  | 5 => 0x63f43597100067e43597100067d43597100063d43597100067c43597100067f72597100067e72597100067d72597100067c72597100067f42597100067e42597100067c42597100067f32597100067e32597100067d32597100067c325971002e7f715971002e7e715971002e7d715971002e7c715971002e7f415971002e7e415971002e7d415971002e7c415971002e7f315971002e7e315971002e7d315971002e7c315971002e7f215971002e7e215971002e76215971002e7d215971002e7c21597100067f70597100067d70597100b67c70597100067f40597100067c40597100067f30597100067e30597100067d30597100067c30597100067f20597100067c205971002e7f105971002e7e105971002e7d105971002e7c1059710004ff7559310024fe7559310024fc755931002ebf7459310004ff7359310014fe7359310004fd7359310014fc73593100067f53593100067d53593100aebf4359310006bd4359310004ff725931000cfe725931000cfc725931002cfc715931002ebe415931002ebc41593100aebf405931002efa105931002ef91059310004ff765531002cfe7655310004fd765531002cfc76553100267e65553100067d65553101feee6255310005f7715531002df47155310004ff7558b10024fe7558b10024fc7558b10004ff7458b1001cfe7458b1001cfc7458b10004ff7358b10014fe7358b10004fd7358b10014fc7358b100067f5358b100067d5358b10006bf4358b10006bd4358b1002eef7258b10006ef5258b1009eee5258b1009eec5258b10006ef4258b1009eee4258b1009eec4258b10006ef3258b1009eee3258b10006ed3258b1009eec3258b1002cfc7158b1002ef63158b10006f53158b1002eee2158b1002eec2158b1009eef2058b10006ef7558b10006ee7558b10006ed7558b10006ec7558b10006ef7458b10006ee7458b10006ed7458b10006ec7458b10006ef5458b10006ee5458b10006ed5458b10006ec5458b10006ef7358b10006ee7358b10006ed7358b10006ec7358b10006ef5358b100066f5358b10006ee5358b10006ed5358b100066d5358b10006ec5358b10006ef4358b10006af4358b10006ee4358b10006ed4358b10006ad4358b10006ec4358b1002eef7158b1002eee7158b1002eed7158b1002eec7158b1002eef5158b1002eee5158b1002eed5158b1002eec5158b1002eef4158b1002eee4158b1002eed4158b1002eec4158b1002eef3158b1002eee3158b1002ee63158b1002eed3158b10006e53158b1002eec3158b10006ef7058b10006ed7058b1009eec7058b10006ef5058b10006ec5058b10006ef4058b10006ec4058b10006ef3058b10006ee3058b10006ed3058b10006ec3058b1002eef1058b1002eee1058b1002eed1058b1002eec1058b10004ff765
  | 6 => 0xf7359120014fe7359120004fd7359120014fc73591200067f53591200067d53591200c6bf4359120006bd43591200ecff7259120006ef7259120004ff715912002cfc71591202bcff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc76551200067f65551200267c65551200067f65d85200067c65d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d8520004ff73d8520014fe73d8520004fd73d8520014fc73d85200067f53d85200067d53d8520006bf43d8520006bd43d8520086ee32d8520006ed32d8520086f621d8520086f521d8520034fe70d8520006fa30d8520006f930d8520086ec20d85200cd7e75985200057d75985200067f65985200067c6598520006f76198520065f970985200057f75585200cd7c75585200067f65585200067c6558520005bf74585200c5bc7458520005df73585200bddc735852009dfb70585200067f65185200067c651852002ef66118520006f56118520004fe7694520004fd769452002cfc76945200067f65945200267c6594520004ff7654520004fe7654520004fc76545200067f65545200267c6554520005bf74545200c5bc7454520004fe7690520004fd769052002cfc76905200067f65905201a67c6590520006bf649052001ebc6490520004ff7650520004fe7650520004fc76505200057f75505200cd7c75505200067f655052018e7c65505202b4fe76941201367f65941200267c6594120024ff765412000cfe765412011cfd765412000cfc76541200067f65541200267c6554120005ef725412000dec72541202acfe76901200067f65901201167c6590120037e8209012001cff765012000cfe76501200ecfd765012000cfc76501200057f75501200cd7c75501200067f65501200fe7c6550120006bf645012001ebc6450120005ef725012000dec72501200efe820501200076f65881200076c6588120035ef73881202a5ed738812029f6f538812029f6d538812029faf438812029fad4388120006ef6188120035ee7088120037ea7088120036ef608812000feb6088120037ea308812029fe9308812002e7f7559710004ff745971001cfe745971001cfc74597100b67f54597100067e54597100b67c5459710004ff7359710014fe7359710004fd7359710014fc73597100b67f53597100067e53597100067d53597100b67c5359710006bf4359710006bd4359710004ff725971000cfe725971000cfc72597100b67f52597100067e52597100b67c525971002cfc715971002e7e515971002e7c515971002ef621597100b67f50597100067f74597100067e74597100067d74597100067c74597100067f73597100047f73597100067e73597100067d73597100047d73597100067c73597100067f4359710
  | 7 => 0x9520006bd43d9520034ff72d952000cfe72d9520134fd72d952000cfc72d95201367f52d95201367d52d952002cfe71d9520004fd71d95200ce7f51d95200ce7c51d952000cfd70d95200ce7f50d95202b57e76d95200247e76d95200067e64d95200067c64d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95200073f43d95200073d43d95201376e32d95200076d32d95200077a30d95200077930d95201377b20d95201376c20d95201377820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200063f43d95200067e43d95200067d43d95200063d43d95200067c43d95201367f72d95201367e72d95201367d72d95201367c72d95201367f42d95201367e42d95201367d42d95201367c42d95201367f32d95201367e32d95201367d32d95201367c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95201367f21d95201367e21d95201367d21d95201367c21d95201367f70d95200ce7e70d95201367d70d95200067f40d95200067c40d95200067f30d95200067e30d95200067d30d95200067c30d95201367f20d95201367e20d95201367c20d95200ce7c65595202c5fb7059520134ff75595200067f7559520004ff745952001cfe745952001cfc7459520004ff7359520014fe7359520004fd7359520014fc73595200ce7f53595200067d5359520006bf4359520006bd435952011cff7259520006ef7259520004ff715952002cfc71595202c4ff7059520006fb70595201357e76195200ce7e76195201347e76195200067e64195200067c64195200cd7f73195200057d73195200067f63195200067e63195200067d63195200067c63195200073f43195200073d43195202b67f62195202b76e32195200076d32195202b67f60195200077a30195200077930195202b77b20195202b76c20195202b778201952001cfe76d91200067f65d91200067c65d91200c6be64d9120024fe75d9120004fd75d9120024fc75d9120004ff73d9120014fe73d9120004fd73d9120014fc73d91200067f53d91200067d53d91200c6bf43d9120006bd43d9120034ff72d912000cfe72d9120104fd72d912000cfc72d9120106bf42d9120106bd42d912002cfe71d9120004fd71d91200c6bc41d912000cfd70d91200c6bf40d91200057f75591200cd7c75591200067f65591200067c65591200c6bc64591202bdfb7059120004ff75591200067f75591200047f7559120024fe7559120024fc75591200067c75591200247c7559120104ff7459120006bf7459120004f
  | 8 => 0xe67f53596200067d5359620006bf4359620006bd435962011e7f525962011e7d5259620004ff715962002cfc715962011eef2159620034fe7059620034fc70596200367e50596200367c5059620024fe75d9220004fd75d9220034fc75d92200ecfd74d9220034ff73d9220014fe73d9220004fd73d9220034fc73d92200067f53d92200067d53d92200debf43d9220006bd43d9220036ed72d922002cfe71d9220004fd71d9220106ef21d9220034fe70d9220036fa70d9220036bf40d922001cff76592200057f75592200e57c7559220036bc6459220004ff75592200067f75592200047f7559220024fe7559220024fc75592200067c75592200247c7559220036bf7459220004ff7359220014fe7359220004fd7359220014fc73592200067f53592200067d53592200debf4359220006bd43592200eebf42592200eebd4259220004ff715922002cfc71592200eeef2159220034fe7059220034fc7059220036be4059220036bc4059220004ff7655220034fe7655220004fd7655220034fc76552200e57e75986200057d7598620036f76198620036f46198620036f46158620004ff7558620024fe7558620024fc7558620004ff745862001cfe745862001cfc7458620004ff7358620014fe7358620004fd7358620014fc73586200067f53586200067d5358620006bf4358620006bd4358620006f63158620006f53158620066f62158620066f5215862002cff7058620034fc7058620006fa3058620006f93058620036f61058620036f4105862002cff7694620034fe7694620004fd769462000dee7294620005ed7294620004ff7654620004fd7654620034fc76546200067f65546200267c6554620005bf74546200ddbc745462002cff7690620034fe7690620004fd769062000dee7290620005ed7290620004ff7650620004fd7650620034fc76506200057f75506200e57c755062002cef7648620006ef6548620006ed6548620006ef6448620006ed64486202ceef63486202ceed63486202cf6f53486202cf6d53486202cfaf43486202cfad434862000def714862000fe7714862002eee6148620007e66148620007e5614862002eec6148620007e65148620007e551486202d7e741486202d7e441486202cfe631486202cfe53148620005ef7048620007eb7048620007e8704862000eee604862000fea60486202cfea30486202cfe930486202c4ff76542200367f65542200367c65542202bcff76502200057f75502200e57c7550220036bf6450220036bc6450220024fe76d95200ce7e65d952001cfe74d9520004fd74d952001cfc74d95200ce7f54d95200067e54d95200ce7c54d9520004ff73d9520014fe73d9520004fd73d9520014fc73d95200ce7f53d95200067e53d95200067d53d95200ce7c53d9520006bf43d
  | 9 => 0xd42d8940006ef32d89400eeec32d894002cfe71d8940004fd71d89400eeef21d894001cfd70d89400eeef20d89400057f75589400fd7c75589400067f65589400067c65589400eeec6258940305fb7058940004ff7654940004fe7654940004fc76549400067f65549400267c65549400edbc765094000ebc765094000cbc76509400073f65509400073c65509402fdbf73509402fdbd73509402f6bf63509402f6bd63509402f73f53509402f73d535094001dbf725094001faf7250940007af625094000ebe625094000ebc62509400efac62509400efaf2150940007bb7050940035bc7050940007b8705094001ebf605094001fbb60509400067f65d85400067c65d8540024fe75d8540004fd75d8540024fc75d8540004ff73d8540014fe73d8540004fd73d8540014fc73d85400067f53d85400067d53d854008ebf43d8540006bd43d854000cfe72d8540004fd72d854000cfc72d854008ef641d854008ef541d8540006f731d8540006f431d85400fd7e75985400057d75985400067f65985400067c65985400edee7298540005ed7298540006f76198540075f970985400057f75585400fd7c75585400067f65585400067c65585400adfb70585400067f65185400067c651854002ef66118540006f56118540004fe7694540004fd769454002cfc76945400067f65945400267c6594540005fa7094540005f97094540004ff7654540004fe7654540004fc76545400067f65545400267c6554540005bf745454001dbc7454540004fe7688540004fd768854002cfc76885400067f65885401767c6588540006f7618854002ef46188540005fa7088540005f97088540004ff7648540004fe7648540004fc76485400067f654854015e7c6548540006ef624854000eec6248540007ad4248540006f7614854002ef461485402ecfe76941401467f65941400267c65941400ff7b5094140024ff765414001cfe765414012cfd765414001cfc76541400067f65541400267c6554140005bf745414001dbc74541400073f65901400073c6590140035bf73901402e5bd73901402debf63901402debd63901402df3f53901402df3d5390140005bd7290140035be7090140037ba7090140036bf609014001fbb609014011cfd75d962001cfe74d9620004fd74d9620034fc74d96200067e54d96200e67c54d9620034ff73d9620014fe73d9620004fd73d9620034fc73d96200e67f53d96200067d53d9620006bf43d9620006bd43d9620036ed72d96201367e52d96201367c52d962002cfe71d9620004fd71d96200e67f51d9620136ef21d9620034fe70d9620036fa70d96200367f50d9620024ff76596200367c65596200367f7559620004ff745962001cfe745962001cfc7459620004ff7359620014fe7359620004fd7359620014fc7359620
  | 10 => 0x8640006f56188640035fa7088640005f97088640004ff7648640004fd7648640034fc7648640005bf744864001dbc744864000eec624864002ef66148640006f5614864030cff765424012fbb4054240024fe76d95400fe7e65d9540034ff74d954001cfe74d9540144fd74d954001cfc74d95401467f54d95401467d54d9540004ff73d9540014fe73d9540004fd73d9540014fc73d95400fe7f53d95400067e53d95400067d53d95400fe7c53d9540146bf43d9540006bd43d954000cfe72d9540004fd72d954000cfc72d95400fe7f52d95400067e52d95400fe7c52d954002cfe71d9540004fd71d95400fe7f51d95400fe7c51d954001cfd70d95400fe7f50d95402ed7e76d95400247e76d95400057f73d95400057d73d95400067f63d95400067e63d95400067d63d95400067c63d95401473f43d95400073d43d95400067e62d95400067c62d95401473f42d95401477b40d95401473c40d95401477840d95401467f74d95401467e74d95401467d74d95401467c74d95400067f73d95400047f73d95400067e73d95400067d73d95400047d73d95400067c73d95401467f43d95401463f43d95401467e43d95401467d43d95400063d43d95401467c43d95400067f72d95400067e72d95400067d72d95400067c72d95401467f42d95401467e42d95401467d42d95401467c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95401467f41d95401467e41d95401467d41d95401467c41d95400067f31d95400067e31d95400067d31d95400067c31d95400067f21d95400067c21d95401467f70d95400fe7e70d95401467d70d95401467f40d95401467e40d95401467c40d95400067f30d95400067e30d95400067d30d95400067c30d95400067f20d95400067c20d95400fe7c655954030dfb7059540144ff75595400067f755954012cff7459540006bf7459540004ff7359540014fe7359540004fd7359540014fc73595400fe7f53595400067d535954012ebf4359540006bd4359540004ff725954000cfe725954000cfc7259540004ff715954002cfc715954030cff7059540006fb70595401457e76195400fe7e76195401447e76195402ee7f64195400fd7f73195400057d73195400067f63195400067e63195400067d63195400067c63195402ef3f43195400073d43195400067e62195400067c62195402ef3f42195402ee7f60195402ef7b40195402ef3c40195402ef78401954000cfe76d89400067f65d89400067c65d89400eeee62d8940024fe75d8940004fd75d8940024fc75d894000cfc74d8940004ff73d8940014fe73d8940004fd73d8940014fc73d89400067f53d89400067d53d89400debf43d8940006bd43d89400eeee42d89400dee
  | 11 => 0x967c50d855011dee7298550005ed7298550006f7619855007df97098550005bf745855012dbc74585500b5fb705855002ef66118550006f56118550004fe7690550004fd769055002cfc7690550006bf649055001ebc6490550004ff7650550004fe7650550004fc76505500057f75505500257c7550550004fe7688550004fd768855002cfc768855002ef66188550004ff7648550004fe7648550004fc7648550006ef624855000eec62485500076d52485501467e64941501467c64941500357f739415031d7d73941503167f63941503167d63941503173f43941503173d43941500057d72941501367e62941501367c62941500067f61941500357e70941500377a70941500367f60941500277b609415012cfd75d9640036bd74d96401467e54d96401467c54d9640034ff73d9640014fe73d9640004fd73d9640034fc73d96401167f53d96400067d53d9640146bf43d9640006bd43d964000cfe72d9640004fd72d9640034fc72d964002cfe71d9640036f671d964002cf671d9640004fd71d9640036f571d9640004f571d96401167f51d9640034fe70d9640036fa70d9640024ff76596400367c65596400367f755964012e7f545964012e7d5459640004ff7359640014fe7359640004fd7359640014fc73596401167f53596400067d535964012ebf4359640006bd4359640004ff725964000cfe725964000cfc72596401167f5259640004ff715964002cfc71596401167c5159640034fe7059640034fc70596400367e50596400367c505964000cff7658a40036ec6258a40004ff7558a40024fe7558a40024fc7558a40004ff7358a40014fe7358a40004fd7358a40014fc7358a400067f5358a400067d5358a400c6bf4358a40006bd4358a40106ee4258a400c6ed4258a40106ee3258a40006ed3258a40004ff7158a4002cfc7158a40034fe7058a40034fc7058a400c6bf4058a40036ee2058a40036ec2058a40004ff7654a40004fd7654a40034fc7654a400267e6554a400067d6554a401157e75986400057d7598640105ee7298640005ed7298640036f76198640036f46198640036f46158640004ff7558640024fe7558640024fc7558640004ff7358640014fe7358640004fd7358640014fc73586400067f53586400067d5358640076bf4358640006bd4358640004ff725864000cfe725864000cfc7258640006f75158640006f45158640076f64158640076f54158640006f63158640006f53158640034fc7058640036f61058640036f4105864002cff7694640034fe7694640004fd76946400267e65946400067d6594640035fa7094640005f97094640004ff7654640004fd7654640034fc76546400067f65546400267c6554640005bf745464001dbc745464002cff7688640034fe7688640004fd768864002ef6618
  | 12 => 0xf7358650014fe7358650004fd7358650014fc735865007e7f53586500067d5358650006bf4358650006bd4358650004ff725865000cfe725865000cfc725865007ef6515865007ef55158650006f74158650006f44158650006f63158650006f53158650034fc7058650036f61058650036f4105865002c7f76546500073f74546501457e74546501457c74546500073c74546501453c74546500067d645465034d7f735465034d7d73546503467f63546503467d63546503473f43546503473d43546501357e72546501357c72546500067d62546500257f715465002777715465002e7e615465000776615465002e76615465000775615465002e7c61546500057f70546500077b70546500077870546500267e60546500277a605465002cff7690650034fe7690650004fd76906500257e75906500057d759065001ebe6490650006bd64906501473c5490650004ff7650650004fd7650650034fc76506500057f75506500257c755065002cff7688650034fe7688650004fd76886500257e75886500057d758865002ef66188650006f56188650007755188650004ff7648650004fd7648650034fc76486500057f75486500257c754865000eec62486501376e524865002ef66148650006f5614865000775514865001cfe76d915012ebe64d915001cfc75d915012ebe54d9150116bd54d9150004ff73d9150014fe73d9150004fd73d9150014fc73d91501167f53d91500067d53d915012ebf43d9150006bd43d915000cfe72d9150004fd72d915000cfc72d915002cfe71d9150004fd71d915012ebc41d9150024fd70d915012ebf40d915012ebc645915033dfb705915000cfe76d895011eee62d895000cfc75d895001cfe74d8950004fd74d895001cfc74d8950004ff73d8950014fe73d8950004fd73d8950014fc73d89500e67f53d89500067d53d8950006bf43d8950006bd43d895011eee52d89500e6ed52d8950006ef32d895011eec32d895002cfe71d8950004fd71d895011eef21d8950024fd70d895011eef20d895011eec6258950335fb705895011d7c765495000e7c765495000c7c76549501f67e64549501f67c645495032d7f735495032d7d73549503267f63549503267d63549503273f43549503273d43549500257f72549500276f72549500076f625495000e7e625495000e7c625495011f6c625495011f6f21549500077b70549500357c70549500077870549500267f60549500277b6054950004ff7650950004fe7650950004fc765095001cfe74d8550004fd74d855001cfc74d8550004ff73d8550014fe73d8550004fd73d8550014fc73d85500967f53d85500067d53d8550006bf43d8550006bd43d855000cfe72d8550004fd72d855000cfc72d85500967f52d85500067d52d8550096f651d8550096f551d8550
  | 13 => 0x452102f777554521007776554521026f66554521026f4655452115f746554521007b77454521155f67454521155f47454521007b47454521155b4745452115f775454521007755454521365f77354521365f5735452115f77535452135f75535452135fb7435452135fb54354521007e7725452100df6725452100df472545211afe4725452102ef7625452102fe762545211af7752545211afe652545211af75525452115fe552545210076552545211afe64254521007e542545211afe6325452135fe53254521005f7705452115f7450545211afe4205452101cff765052100cfe765052117cfd765052100cfc76505210057f755052115d7c7550521006bf645052101ebc6450521005ef725052100dec7250521355f7715052102fb44150521024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d8121004ff73d8121014fe73d8121004fd73d8121014fc73d81210067f53d81210067d53d8121006bf43d8121006bd43d812102cfd72d812109eee32d8121006ed32d8121006f631d8121006f531d812109efa20d812109eec20d8121006fb60981210057f755812115d7c7558121005bf7458121155bc7458121005df735812114ddc7358121006f96018121024fe7518121004fd7518121034fc751812101cfe7418121004fd7418121034fc7418121034ff7318121014fe7318121004fd7318121034fc73181210067f53181210067d5318121006bf4318121006bd431812102cfd7218121036f57118121036fa201812103ef9201812101cff76592500257c7559250036bc64592501473e54592501467e5459250146be54592501463e54592500febd54592501467c5459250004ff7359250014fe7359250004fd7359250014fc73592500fe7f53592500067d5359250146bf4359250006bd4359250004ff725925000cfe725925000cfc7259250146bf4259250004ff715925002cfc71592500fe7f5159250146bc4159250034fe7059250034fc7059250036be4059250036bc405925000cff7658a500257c7558a50036ec6258a501376e5258a50004ff7458a5001cfe7458a5001cfc7458a500067e5458a500ce7c5458a50004ff7358a50014fe7358a50004fd7358a50014fc7358a500ce7f5358a500067d5358a50006bf4358a50006bd4358a501367e5258a50136ee5258a500ceed5258a501367c5258a50136ee3258a50006ed3258a50004ff7158a5002cfc7158a500ce7f5158a50034fe7058a50034fc7058a500ce7f5058a50036ee2058a50036ec2058a50004ff7650a50004fd7650a50034fc7650a500057f7550a500257c7550a5001ebe6450a50006bd6450a50135ee7298650005ed7298650036f76198650036f46198650036f46158650004ff745865001cfe745865001cfc7458650004f
  | 14 => 0x2df671d912100df571d9121157b741d9121024fe75d9121004fd75d9121024fc75d9121006bf54d9121156bc54d9121004ff73d9121014fe73d9121004fd73d9121014fc73d91210067f53d91210067d53d9121156bf43d9121006bd43d912102cff72d912102cfd72d9121196bf42d9121196bd42d912100cfd71d9121196f571d912100cf571d9121156bf41d9121156f741d9121156f441d9121034fe70d9121004fd70d9121156bc40d91210057f755912115d7c7559121156bc6459121355f77159121004ff75591210067f75591210047f7559121024fe7559121024fc75591210067c75591210247c7559121194ff7459121006bf7459121004ff7359121014fe7359121004fd7359121014fc73591210067f53591210067d5359121156bf4359121006bd435912117cff7259121006ef7259121354ff7159121006f77159121156f74159121156f44159121004ff7059121034fc7059121004ff7655121004fe7655121004fd7655121004fc765512100dee7255121005f7715512102df4715512102dec7654921026ec765492102cec765492100def755492100f6f75549210076f6554921026ee6554921026ec655492115f6c6554921005ef74549213a76e545492115f6c54549213adef73549213aded735492115f6f535492139f6d535492139faf435492139fad4354921007e7715492102dee715492102dec7154921007e4715492100eef615492100fe7615492115f6f51549213a7e741549213a7e4415492139fe6315492139fe53154921005ec705492115f6f505492102dec765092101eec765092102cec7650921005ef7550921005ed755092100def745092100faf7450921007af645092101eee645092101eec6450921157ac6450921395ef7350921395ed735092138f6f535092138f6d5350921157af435092138fad4350921007e7715092102dee715092102dec7150921007e4715092100eef615092100fe76150921157e74150921157e4415092138fe6315092138fe53150921005ec7050921157af4050921385f6769452102ef676945211adf57594521026f66594521026f46594521155f6749452102df4749452137f76549452115f74549452102df77394521375f5739452115f77539452136f75539452136fb7439452136fb5439452102fe7729452100df6729452102df4729452102fe4729452102ef7629452102fe762945211c7e6529452115fe552945211c7e64294521007e542945211c7e6329452136fe53294521005f570945211c7e42094521024ff765452100cfe76545211acfd765452100cfc76545210067f65545210267c6554521005bf7454521155bc7454521005ef725452100dec72545210076d525452102f74515452102fe4215452100df47654521026f4765452100cf4765452102df7755
  | 15 => 0xf75592210047f7559221024fe7559221024fc75592210067c75592210247c755922102ebf7459221004ff7359221014fe7359221004fd7359221014fc73592210067f53592210067d535922116ebf4359221006bd435922117ebf425922117ebd425922102cfe715922102cfc715922102ef4715922102cf4715922116ef7415922102ebe415922102ebc415922102ef4415922102eef215922102eed2159221004ff7059221034fc7059221004ff765522102cfe7655221004fd765522102cfc76552210267e65552210067d6555221005f7715522102df4715522102df776546213cef7765462102f77755462102f776554621026f6655462102ef4655462102f746554621007b7745462116df6745462116df47454621007b4745462116db474546211777754546210077554546213c5f773546213c5f573546211777753546213bf7553546213bfb743546213bfb5435462100df6725462100df472546211af7752546211af755254621005f77054621177745054621024fe7598221004fd7598221034fc759822101cfe7498221004fd7498221034fc7498221034ff7398221014fe7398221004fd7398221034fc73982210067f53982210067d5398221006bf4398221006bd439822102cfe7198221036f6719822102cf67198221034fc719822102eef219822102eed2198221036fa7098221006fb5098221036f85098221036fa3098221006f93098221036fa2098221086f92098221036f7109822102efb1098221036f81098221004ff7558221024fe7558221024fc7558221004ff745822101cfe745822101cfc7458221004ff7358221014fe7358221004fd7358221014fc73582210067f53582210067d5358221006bf4358221006bd435822102cfc715822102ef63158221006f5315822102efb7058221006fb5058221006f85058221006fa3058221006f93058221066fa205822102efb105822102ef81058221024fe76d952115e7e65d952101cfe74d9521004fd74d952101cfc74d95210067e54d952115e7c54d9521004ff73d9521014fe73d9521004fd73d9521014fc73d952115e7f53d95210067d53d9521006bf43d9521006bd43d952102cff72d952102cfd72d95211c67f52d95211c67d52d952100cfd71d952115e7f51d9521034fe70d9521004fd70d952115e7c50d952115e7c6559521005bf7459521155bc74595213b5f771595211c4ff75595210067f7559521004ff7459521006bf7459521004bf745952101cfe745952101cfc7459521006bc745952101cbc7459521004ff7359521014fe7359521004fd7359521014fc735952115e7f53595210067d5359521006bf4359521006bd43595211acff7259521006ef72595213b4ff7159521006f77159521004ff7059521034fc705952101cfe76d9121156be64d9121
  | 16 => 0x95411d67f40d95411d67e40d95411d67d40d95411d67c40d95410067f30d95410067e30d95410067d30d95410067c30d95410067f20d95410067c20d95413f67f10d95413f67c10d954118e7c65595413edf771595411d4ff75595410067f75595411bcff7459541006bf74595411a4bf7459541004ff7359541014fe7359541004fd7359541014fc735954118e7f53595410067d53595411bebf4359541006bd4359541004ff725954100cfe725954100cfc72595413ecff7159541006f77159541004ff7059541034fc70595411d57e761954118e7e76195411d47e76195413e67f64195413e63f641954118d7f73195410057d73195410067f63195410067e63195410067d63195410067c63195413df3f43195410073d43195410067e62195410067c62195413de7f61195413df7741195413e73e41195413e73c41195413df74411954100cfe76d89410067f65d89410067c65d894117eee62d8941024fe75d8941004fd75d8941024fc75d894102cfd74d8941004ff73d8941014fe73d8941004fd73d8941014fc73d89410067f53d89410067d53d894116ebf43d8941006bd43d894117eee42d894116eed42d894101cfd71d894116ef741d894116ef441d894117eef21d8941034fe70d8941004fd70d89410057f755894118d7c75589410067f65589410067c655894117eec62589413d5f77158941004ff7654941004fe7654941004fc76549410067f65549410267c6554941024ff765454101cfe76545411bcfd765454101cfc76545410067f65545410267c6554541005bf745454101dbc745454102fb441545410067f65d81410067c65d8141024fe75d8141004fd75d8141024fc75d814102cfd74d8141004ff73d8141014fe73d8141004fd73d8141014fc73d81410067f53d81410067d53d81410aebf43d8141006bd43d814100cfe72d8141004fd72d814100cfc72d81410aefa40d814118d7e75981410057d75981410067f65981410067c6598141006fb60981410057f755814118d7c75581410067f65581410067c65581410067f65181410067c6518141006f96018141024fe7518141004fd7518141034fc751814102cfd7418141034ff7318141014fe7318141004fd7318141034fc73181410067f53181410067d531814104ebf4318141006bd431814100cfe7218141004fd7218141034fc7218141036fa401814104ef9401814102e7f7559621004ff745962101cfe745962101cfc74596211767f5459621004ff7359621014fe7359621004fd7359621014fc73596211767f53596210067d5359621006bf4359621006bd43596211ae7f52596211ae7d525962102cfe715962102cfc715962102e7e515962102e7c515962102eef215962102eed2159621004ff7059621034fc70596211767c5059621004ff75592210067
  | 17 => 0x1a67c5059641004ff7558a41024fe7558a41024fc7558a41004ff7358a41014fe7358a41004fd7358a41014fc7358a410067f5358a410067d5358a41156bf4358a41006bd4358a4102eef7258a41196ee5258a41196ee4258a41156ed4258a41196ee3258a41006ed3258a4102cfe7158a4102cfc7158a41156f74158a4102ef44158a4102eee2158a4102eec2158a41004ff7058a41034fc7058a41196ec2058a41004ff7654a41004fd7654a4102cfc7654a410267e6554a410067d6554a41005bf7454a4101dbc7454a411f73c5454a4100eee6254a41006ed6254a41024fe7598241004fd7598241034fc7598241034ff7398241014fe7398241004fd7398241034fc73982410067f53982410067d539824108ebf4398241006bd439824100cfe7298241004fd7298241034fc729824102cfe7198241034fc7198241036fa7098241036fa409824108ef94098241036fa3098241006f9309824102efb1098241036f81098241004ff7558241024fe7558241024fc7558241004ff7358241014fe7358241004fd7358241014fc73582410067f53582410067d5358241076bf4358241006bd4358241004ff725824100cfe725824100cfc725824102cfc715824102efb7058241076fa4058241006fa3058241006f9305824102efb105824102ef81058241024fe76d954118e7e65d954102cff74d954102cfd74d95411d67f54d95411d67d54d9541004ff73d9541014fe73d9541004fd73d9541014fc73d954118e7f53d95410067e53d95410067d53d954118e7c53d95411d6bf43d9541006bd43d954100cfe72d9541004fd72d954100cfc72d954118e7f52d95410067e52d954118e7c52d954101cfd71d954118e7f51d9541034fe70d9541004fd70d954118e7f50d954118e7c50d95413dd7e76d95410247e76d95410057f73d95410057d73d95410067f63d95410067e63d95410067d63d95410067c63d95411d73f43d95410073d43d95410067e62d95410067c62d95411d77741d95413f73e41d95413f73c41d95411d77441d95413f67f74d95411d67e74d95411d67d74d95411d67c74d95410067f73d95410047f73d95410067e73d95410067d73d95410047d73d95410067c73d95411d67f43d95411d63f43d95411d67e43d95411d67d43d95410063d43d95411d67c43d95410067f72d95410067e72d95410067d72d95410067c72d95411d67f42d95411d67e42d95411d67d42d95411d67c42d95410067f32d95410067e32d95410067d32d95410067c32d95411d67f71d95413f67e71d95411d67d71d95413f67c71d95411d67f41d95413f67e41d95413f67c41d95410067f31d95413f67e31d95410067d31d95413f67c31d95410067f21d95413f67e21d95413f67c21d95410067f70d95410067e70d95410067d70d95410067c70d
  | 18 => 0xc62191514273f52191513eebf6119151427b751191513e73e51191513e73c5119151427b451191514273c501915102d7c765515101e7c765515102c7c76551510257f74551510273f74551510073f645515101e7e645515101e7c64551511bf3c645515101e3c645515141d7f735515141d7d73551514167f63551514167d63551511bf3f43551514173d43551510057f725515100777715515102d7e715515102d7c71551510077471551510267f61551510277761551510057c705515100cfe76d8951006bf64d8951006bc64d89511aeee62d895102cfd75d895101cfe74d8951004fd74d895101cfc74d8951004ff73d8951014fe73d8951004fd73d8951014fc73d89511767f53d89510067d53d8951006bf43d8951006bd43d89511aeee52d8951176ed52d8951024fd71d89511aeef21d8951034fe70d8951004fd70d8951005bf74589511bdbc7458951006bf6458951006bc64589511aeec625895140df7715895102d7c765495100e7c765495102c7c76549510057f74549510073f64549511f67e64549511f67c64549510073c64549511f63c64549514057f73549514057d73549513fe7f63549513fe7d63549513ff3f43549513ff3d43549510257f72549510276f72549510076f625495100e7e625495100e7c62549511af6c625495100777715495102d7e715495102d7c71549510077471549510267f61549510277761549511af6f21549510057c7054951004ff7650951004fe7650951004fc76509510257e75509510057d7550951006bf645095101ebc6450951006bf64d8151006bc64d815102cfd75d815101cfe74d8151004fd74d815101cfc74d8151004ff73d8151014fe73d8151004fd73d8151014fc73d81510b67f53d81510067d53d8151006bf43d8151006bd43d815100cfe72d8151004fd72d815100cfc72d81510b67f52d81510067d52d81510b6fa50d81510b67c50d81511bdbe7498151005bd7498151006bf6498151006bc6498151006fb6098151005bf74581511bdbc7458151006bf6458151006bc6458151006bf6418151006bc6418151006f9601815102cfd751815101cfe7418151004fd7418151034fc7418151034ff7318151014fe7318151004fd7318151034fc73181510567f53181510067d5318151006bf4318151006bd431815100cfe7218151004fd7218151034fc7218151036fa5018151056f9501815102e7f75596411a6bf74596411be7f54596411a6bf54596411a63f54596411be7d54596411bebc5459641004ff7359641014fe7359641004fd7359641014fc73596411a67f53596410067d53596411bebf4359641006bd4359641004ff725964100cfe725964100cfc72596411a67f525964102cfe715964102cfc715964102e7e515964102e7c5159641004ff7059641034fc7059641
  | 19 => 0x8251004fd7398251034fc73982510967f53982510067d5398251006bf4398251006bd439825100cfe7298251004fd7298251034fc729825102cfe7198251034fc719825102e7f519825102e7d5198251036fa7098251036fa5098251096f95098251036fa3098251006f93098251006fb2098251036f8209825102efb1098251036f81098251004ff745825101cfe745825101cfc7458251004ff7358251014fe7358251004fd7358251014fc735825107e7f53582510067d5358251006bf4358251006bd4358251004ff725825100cfe725825100cfc725825102cfc715825102ef6215825102efb705825107efa5058251006fa3058251006f93058251006fb2058251006f8205825102efb105825102ef8105825101cfe76d91511bebe64d915102cfd75d91511bebe54d91511a6bd54d9151004ff73d9151014fe73d9151004fd73d9151014fc73d91511a67f53d91510067d53d91511bebf43d9151006be43d9151006bd43d91511bebc43d915100cfe72d9151004fd72d915100cfc72d91511bebf42d9151006be42d91511bebc42d9151024fd71d91511bebf41d9151034fe70d9151004fd70d91511bebf40d91511bebc40d91511bdbe76d915101cbe76d91514373f75d91511a73c75d9151005bf73d9151005bd73d9151006bf63d9151006be63d9151006bd63d9151006bc63d91511a73f53d91510073d53d9151006be62d9151006bc62d91511a73f52d91511a7b751d91514373e51d91514373c51d91511a7b451d91511a73c50d9151436bf75d91511bebe75d91511a6bc75d9151006bf73d9151004bf73d9151006be73d9151006bd73d9151004bd73d9151006bc73d91511a6bf53d91511a63f53d91511a6be53d91511a6bd53d91510063d53d91511a6bc53d9151006bf72d9151006be72d9151006bd72d9151006bc72d91511a6bf52d91511a6be52d91511a6bd52d91511a6bc52d9151006bf32d9151006be32d9151006bd32d9151006bc32d91511a6bf71d9151436be71d91511a6bd71d9151436bc71d91511a6bf51d9151436be51d9151436bc51d9151006bf31d9151436be31d9151006bd31d9151436bc31d9151006bf21d9151436be21d9151436bc21d9151006bf70d9151006be70d9151006bd70d9151006bc70d91511a6bf50d91511a6be50d91511a6bd50d91511a6bc50d9151006bf30d9151006be30d9151006bd30d9151006bc30d9151006bf20d9151006bc20d9151436bf10d9151436bc10d91511bebc645915142df771591511a5be76191511bebe76191511bf3e75191511bf3d75191513e6bf65191513e63f65191511bdbf73191511bf9e7319151005bd73191511bf9d73191510059d7319151006bf6319151006be6319151006bd6319151006bc63191514273f53191510073d5319151006be6219151006b
  | 20 => 0x1cfd72d954244e7f52d954244e7d52d954202cfe71d9542004fd71d95421e67c51d954244eef21d9542034fe70d9542004fd70d95421e67c50d9542024ff76595421e67c6559542445bf7459542455ef725954244cff75595420067f7559542444ff7459542006bf74595421f67e54595421f67c5459542004ff7359542014fe7359542004fd7359542014fc73595421e67f53595420067d53595421f6bf4359542006bd43595421fcff7259542006ef7259542004ff715954202cfc71595421e67f51595421feef2159542004ff7059542034fc705954202cfe76d8542024fe75d8542004fd75d8542024fc75d854200cfd74d8542004ff73d8542014fe73d8542004fd73d8542014fc73d85420067f53d85420067d53d85423d6bf43d8542006bd43d854201cfd72d85423d6f641d8542356f621d8542034fe70d8542004fd70d8542006f761985420057f75585421e57c75585421e57e75185420057d751854202ef66118542006f56118542024fe75d8142004fd75d8142024fc75d814200cfd74d8142004ff73d8142014fe73d8142004fd73d8142014fc73d81420067f53d81420067d53d8142306bf43d8142006bd43d814201cfd72d814202cfe71d8142004fd71d8142306fa40d81422befa20d8142006fb60981420057f75581421e57c7558142006f96018142024fe7518142004fd7518142034fc751814200cfd7418142036bd7418142034ff7318142014fe7318142004fd7318142034fc73181420067f53181420067d531814243ebf4318142006bd431814201cfd721814202cfe7118142004fd71181422aeef2118142036bf4018142036fa401814243ef94018142036fa20181422aef9201814202ebf74592511d67e54592511d6be54592511d63e545925118ebd54592511d67c5459251004ff7359251014fe7359251004fd7359251014fc735925118e7f53592510067d53592511d6bf4359251006bd4359251004ff725925100cfe725925100cfc725925102cfe715925102cfc715925102e7f515925102e7d515925102ebe415925102ebc4159251004ff7059251034fc7059251004ff7458a5101cfe7458a5101cfc7458a510067e5458a5115e7c5458a51004ff7358a51014fe7358a51004fd7358a51014fc7358a5115e7f5358a510067d5358a51006bf4358a51006bd4358a5102eef7258a511c6ee5258a5115eed5258a511c6ee4258a511c6ee3258a51006ed3258a5102cfe7158a5102cfc7158a5102e7f5158a5102e7d5158a5102eee2158a5102eec2158a51004ff7058a51034fc7058a511c6ec2058a51004ff7650a51004fd7650a5102cfc7650a510057f7550a510257c7550a5100eee6250a51006ed6250a5101cfe7498251004fd7498251034fc74982510067e54982510967c5498251034ff7398251014fe739
  | 21 => 0xf64185541fdee7218554005ed721855402ef66118554006f5611855401cfd75d8154024fd74d8154004ff73d8154014fe73d8154004fd73d8154014fc73d815433e7f53d81540067d53d815430ebf43d8154006bd43d815400cfe72d8154004fd72d815400cfc72d815402cfe71d8154004fd71d815433efa50d815430efa40d8154005f67198154005f57198154006fb6098154006f9601815401cfd7518154024fd74181542ee7e54181542ee7c5418154034ff7318154014fe7318154004fd7318154034fc731815447e7f53181540067d53181542eebf4318154006bd431815400cfe7218154004fd7218154034fc721815402cfe7118154004fd711815447e7f5118154036fa501815447ef95018154036fa40181542eef9401815401cfe76d91520257e75d915200d7d75d91521f6be64d91521f73e54d915200cfd75d91524467d75d915200c7d75d91521f67e54d91521f6be54d91521f63e54d9152476bd54d91521f67c54d9152004ff73d9152014fe73d9152004fd73d9152014fc73d91524767f53d91520067d53d91521f6bf43d9152006bd43d9152024fd72d9152446bf42d915202cfe71d9152004fd71d91524767f51d91521f6bc41d9152446ef21d9152034fe70d9152004fd70d91521f6bc645915246def725915202cfe76d855200cfd75d855201cfe74d8552004fd74d855201cfc74d8552004ff73d8552014fe73d8552004fd73d8552014fc73d855240e7f53d85520067d53d8552006bf43d8552006bd43d8552024fd72d855240ef651d85523b6f621d8552034fe70d8552004fd70d8552006f76198552005fa7098552005f97098552005bf74585521f5bc745855202ef66118552006f5611855200cfd75d815201cfe74d8152004fd74d815201cfc74d8152004ff73d8152014fe73d8152004fd73d8152014fc73d81523367f53d81520067d53d8152006bf43d8152006bd43d8152024fd72d815202cfe71d8152004fd71d8152336fa50d8152006fb30d8152006f830d81522c6fa20d8152006fb6098152006f9601815200cfd75181520367d751815201cfe7418152004fd7418152034fc74181520067e54181524667c5418152034ff7318152014fe7318152004fd7318152034fc73181524667f53181520067d5318152006bf4318152006bd4318152024fd72181522b67e52181522b67c521815202cfe7118152004fd71181524667f51181522b6ef21181520367f5018152036fa5018152466f95018152006fb3018152036f83018152036fa20181522b6f92018152024fe76d95421e67e65d95421fcfd75d954200cff74d954200cfd74d954245e7f54d954245e7d54d9542004ff73d9542014fe73d9542004fd73d9542014fc73d95421e67f53d95420067d53d954245ebf43d9542006bd43d954201cff72d9542
  | 22 => 0x100000050004003000000100000060004001000000000040010004000000800000000000000000001400000040000008001000c0000008001000400000040000004000000000000040020004008000000100240000000001000400100000010000003000800200000000000002000400100000000000000001800000000010000000000000000100010020000000800600000000000000000c0000000001000400000000000000003000400100000010004001000000000100000000000000000200000010000001001400100040000004000000400000040000000005000800000000000008000000000000000020008000000000100100000000000001400100000010000003000800100000000000005000800000040000000000000400200000050000002000400200000090000001000400100080010000000000400300040000030000000000000000010000001000000000040040000000001400000000040004001000000000040000004002000800300000010004001000800000000010004000000000000000000018002000000100200000000000000000400180040004004000000000240000004000000c00000040000000001000400c0008004000000000100000004002000000000000000000007000000000040020004003000c00a0000004000800300000020000001001400000380000008000000400000140030000000001000200000030000001000000300080010000001001c0000000001000400000040010014000001c001002000000040060000000000c0070018001000000000000030008000000000500000000000004000000000000000000000000c004000c000000000400180000000001000400000000000000003002000900000000004000000000200080010004004000000000000020000002000000000000000008000000800a0000000000400000040000000000000000000000000008001000c005002000000000030018001001000200000000010003000400500100020004002000000000cfe76d89541feee62d895401cfd75d8954024fd74d89544567e54d89544567c54d8954004ff73d8954014fe73d8954004fd73d8954014fc73d895446e7f53d89540067d53d8954456bf43d8954006bd43d89541feee52d89541feee42d895402cfe71d8954004fd71d895446e7f51d8954034fe70d8954004fd70d89541feec625895402cfe76d855401cfd75d8554024fd74d8554004ff73d8554014fe73d8554004fd73d8554014fc73d855442e7f53d85540067d53d85543eebf43d8554006bd43d855400cfe72d8554004fd72d855400cfc72d855442ef651d85543eef641d8554006f731d8554006f431d8554034fe70d8554004fd70d85543f67f6598554436bf6498554006f761985543f67f6518554436b
  | 23 => 0x8000000000500040050000000000000300180000010000000c00000000030000000001400300300000000001000000000000000004000000000000000000000000000400100000050000000000000400040010000001000c00100040000000001000000000000000008001001000000000000000000000c0000004000001800200000070000006000000000280020000000000000100000000008000000c0000020000000000000080020000000000c0040000006000800500080000000009000400000000010004001001400100040010004000000400200000000008000000800200000000000000000000100040040000002000400000080000010000000000300040000000000000000b00000000008002000400200000000000001000000300000000004003000000200000000000003000000000000000008000000000300240020000000000800000040040004000000c0000000002000c001000c000001400300140000004000000c0000008000000400000040000020000000000200000000000002000400000000000004001000000100000020004005000c00600040010000005000800600000000008002000c00000000000008000000000200000010014005000c0000004000002000000100000010000001c0000000000000000b0000000000000300000000000000000c00000140020000000000400000080000000000000400300080000004000000000000000030008001000000300000000000002000800500040000004000003000000040040000000000800200100010008006000000600080010004002002c001000400200200020004004001400200000000000004000c0000004000000000100000030004000000000000000010000000000000600000050000003000c0000000000000c008000800800000010004001000400f0004000000000100040010000000000000000000000004002001400000000000000000000c000000000000040030008000000000d00080010000001000000100000000008003000c0000004000000c002000400c000400300000000010000000800100080020000001000800300000010000000000400100040010004000000000400000020000001000000400000010000000001800000000040004002000000100080030000001000400000000010000001000c000000000100040000004000000000100040020000004000c0020000001001c0000004002000800000100000010000000000200080010000002000000300000000008002000000200000010004002000400100000010000005000400000180020000001000c00000040000014000000000000000000000000000c00300080000000000000400000040000000000000800200000010008000000400000000040008002000400
  | 24 => 0xb456878000000c8a00017f80000000002bec00007d45e39992580000fe8001a9e0005bd9a28000000000000000000000000004fc8a16988001cf80004e20000ade0005e604e0080000000331525e00005180000006fe14d8000000e6d0d780000004270000000000000000211cefa0000000000000000617a220140cc35ad00000006575a2173400000046b000000000000026540000005f08f4800060e0003b480000004ee80000000002a58000fee0000001f90000000299158c5263c900013e16364cc69406b00000000000a81b9e00006a9cad54e00000000000000000000000000000000244c00007520226640004d20000000000000331800059000021801500000005c381c440650857307a9312287378117c62e000000000000000000000000000002a9800000000000024d8000000000188c0004fc0000000dbe25a00035c000067f57500000000006ba00000000000001d9cdf67d90000000000d300000000000000000000011400000032cc58c59f00000000000001873910124000000000014a00000000000000000000001c3039b08c247401e0000000d3996c0002280000000bf84cf11f8b4400035f000020ab07000000000075a0001e000007f000000000000000000000000adb216b7f80000004761079314e8125d800018c0000000000bf20000000000000000000000000000000000000000001d380000005db2bd06f4afadbb61a00009c4591493800000036335593d4a2c34b61b1ec800000000018302eeecb00000013c600041480019e28640000a3c00066c0000010000400200100000008002000400100000000008000000000000000030000000000000400040000000002000000000040000000003000000000000000000000000400000040020000005000000000000030008001000000000000020010001000000d00000010000000000000000000000014007000000100000020010000000400200040000000000000000300000000010000001000000000010004000000000200000000004000003000200180010008000000000100040010000000000c001000000000040000004000001000100080010000000000400100000010000001000000000040010008000000400000040020000002000000100000010000001000400300080000000000001800000000000030000000c00000080000018000000000700000010000004000000000040010000000000000200040000000001000000100000010004005000c002000000000000000018001000000000040000000008001c000000000500000000004000000c006000000000000000000001000c0010000000000400500040010000001000400000000070004003000000000000030000001000c00000080000004000000000000100010008000000000000
  | 25 => 0x518000181cdbd000108000000020c00000000004200000000000080bad52123ee1a01a71a9a3e869480008242911ff8000000000000000000069348f2b24000496000009c0002504ffb4fcf460ba2260000fc0575752b96cb8e000000274c0a0a650002bf000042c1ff056d786a903ac1edc00060317d96841a897370c800023679f5e000003508a30000001becb9500000000000000000001bb80000ef00007f60000000000dc000000033d82e634d373800000053500033a40000000003b380000c8570a76c1cce620000ff59b60001af85859c80000000000000000442000000000000033a136a0001e9b104e88b701e62905c480000000000000000622000000000000003ec128dc323ab72c0000000e1800108462668d00013860000003b611fc000628000000000000000000001340000000bd44680000000000b273771674000000000346000072160380000000001f8a4b40004a4000000000000000000011e89d03938d70620122000246c000b690000001a32afd00000015b80ae5090388f9c84900000001700005e38000636cc01ad00000007c200000000009bc00015812780000000000c3cec300000000000000000000000000000000000000000000000000006e500000000000000f780005a70000000000eab0df000000000000017ac88e000000000161097100024cc158cde00000009329a600000000000000f699314dec234841ce9ad683500000000000000001770c28000000000142a0004590000000cfd2aa000109e000000000000000009b8d28f340006fb80000000000000000000b8a057800000031d00039b0000a6d00038a51000003c98d6000062400000018ce02a62fa0e82fcc810000000000c4a00000000000000000938e1000000009cc0000006c62e9c00000000000000000000002010b0c0000001b9032a0000000000000000000172c00033b0003018000ab400000003b40000000000000000000217539200059e80000000005e68000c12000000319400031563a00013541996e9800169000030c00000000005fd0000000a7f0000e3152667d00000017923db56023ed2561dd000150800000021d0001c3c0007460ba0a580001338ac4f8800000ea1fc000867000000093000035380000000004a00001c820000001e8800000002b80000007db00000014a6000136000101400000000000000007300000d5c00000000000000000000001caab3300016201da0000003958000000000000000067c00003608c800000007ec8b40000000000ae89b653836587b0a9c65f136c4f6d0d0000000574000000000000000066e2578000ccd00000006a400067f1475b4600000026411d47fa1eb00012b65b401c37a800009511ea914044a5500000000000000002ac14c0b2438f816800000058a8000
  | 26 => 0x4000000000000000000056b800054eda568e9b700005d50000000000026103984800000000021b0000000000148400000000025e80000000198000000000000000000000000000000000741ea00011e00000002b65c9e7b60003a78000cec0000000bd80704a6800126428d0000000000caa0000000000702316000000000039280000003331ca0001b6ac5a0000001c66000000000000047c43a0000ad6231000000000099372e8000bda0000000000000b5430b8aad4d80003a9156400074e05db54c010a7c00023c933a8520000000184000754aeb40006790000000f5a00000038dcb3860400032ed7b0cf870815c1130a040000001cea57866080000004e803980002fa0005ea81a571078900000018f8000000000000060224a1cd5c386b92e32595b0cbe62468000000d26129b7c50f80000001d5c9b41f5000061000000000000000004d62780880116dfb5a7800000000074784b436c72d1de8000000000000000006e000000000000000000000017fe0006a594d000000043c800169a0001d623184da0003848001b5a8ca24900000009da0da800112600032f22d8000e060000000000000000000000000000000018dee210000000000000000000000000000000000000002222cf8a541d80001d2000095c616000070e0001be80000007b50001b844b20000000001d7c8d519809a4bf436b33d265874401c1bda95c7e0000000000066a00000000000004a000000000000000b1b5540f2000000000000000000009dc000000576800000000d0000000000d2b0000944d52a9f2348de80002540000af449200000000000007fd31c800162076d00017c034200000000000000006f28ddd0da75956e8000cf0b0638c86b800000000000004566005ac03c00000000000000000aab22080000000000000de40000003ef80000007ee00000011a20001f61c499bae6912f80000000000000001aa435900000010883df70a00002bab5343880010bc00000000000005380000001a6cbb90002f140000000003720000000000147c000000000000000058a00000003400000003590fbc00000000018ec5e42f88000000000000000000000000000000006f100000000000001cd00000000004340698fae0000001fd4000000328800000000000001396c8000000000000000000000000000000000000000000702800000000016c0000000dd21e0b33c1fa00005f000000000052e07c95a400000021e15bc82500026a535a5d6000000000071d000000000000020780000008bd00000000000000002b3dc7c00000000000000000c50000000000239800000000061e800000000000000002d40000000cc4000d4507f026c000000000000000096a000000000000023a16f98fe85b3e8800047e72e5f800013421d60b72e098780000000000000bf3
  | 27 => 0x400000000000000000000000c13000000000000010a1a0c0004fe000000000000034d8000a00266195202042c35b10d26f895866428a135400094836b250800032d3c820cd40c00000000000000852a4af180000007263a5c0006843152d0110cb2a0002ab80568b10002d64000270000000045e9f00000000000a280001ef129c8ae44e0001930a360003ac4fc611d00d8001d6400000000000000004908000670000343a9dd5c4cc972f000000000000000000000000000000000d051b000000003e32e5253c00000000020318e457600039bc0004de0000000cac00c0000000000a7d1f686cd8ee1f66972f480000005e521500000003a280000000000000000000d2501f2600bbc0000002884000963000000000000000003ad502a6b58980000000006afa9f80000000000000000000000000000000000000000000003381aa800073d0002be800000000000016ac0003b4b28800000074b00008d80000000000a98000000000127c00052200019a2bbc0002171b8c88f7493a4571aea045da6e87ba0001c028d19788003a528bcacc000000000000000070508b58bc01117f00000001152770001d320000003a9000000001b22511da4565c08001742ab914b89780000006e00b4000008060bad8067c53e0002198298b9b00000016ee8482d405e800065860d8000000754000000000000000000000008950ad21844e400000002e577e13100020480000000000000000d240eda54136068c7008d89054b7650e3a1dbbcc5104430b930a45e62180016120d600000000000002d480000000000000000000000526b100438b7300000000007410e100000000001c59b4ceb86071eb800000000000003c940659b000000000000000000016ea3be000000013835143b00000000000000000d10000000127d69420c000000000000000000000005df5351a012060000c4800109a0000000000000000000000074a0000000000000000000000000000000032a5d6600000000c4e6c0000002b301e80000000000000960000000003c6b60000000000bec1ee0000daa77f00015b95ace6b00000016d00000003310000000107307975e71c0000000000b900002298000d4e1e206adab80006248000000c9b0000001c129e40000000528e8e04d399547200019a0190c6878256c1a1400000000000006aa0005be23480009b233f00000007b33fc369c0ce2da18610d40000006e21528000000000000000000000000013aed0600015a0c3e0006f00b38000000000144198e00000000005ea58332130c40002b70002a4800000000000000000000000000d9e000000062c0006de20d0001ae2ad40000001bb20001cc800050c0000fc0001328000696a4800000000000f34e80ea110300000000003b100011b217f037800000000027c94800000000002c9
  | 28 => 0xb884412641e800169c5a30000000000000000000000096f6009cb0000dda00000000000006e80000000e3a11380000000001c780002d625b0001bcc80a80166b800000000000000000a60005910001370000000000000000023e8000000d390000d98a5c10a00008440001b00b780005ba63c0000d3c000a6345780002821fa1cc00001dc4bc3cf10580000000000001bae2e4000000000000000000017260000000001d8870500033d400000000000000008fc000000099ed920003810000000335b24c5d2c0f43b8dc814c1bc00020fc000000000192000073100000010b24bd000260515819815b1f5173800062300000001510000000000000562236c000d323f9800000042600000012a814f0000000f9400000000000000000000000000000000000000098b604000098adb4000000068600000000000008a00d200000000000000000000000566800166e0000000000ce40000002e1800000000000180000005d180000000003c62a0c0008230002528e7699100000015780000000000f98ecc1da800000000000026f59464f767d9fa000015f0002b1cda80000d89024d28000000000022295600000018420000000f1c0007fc3f48b0000000019100017820000000a654220000002ef4000000000000000000053c8000000c54000000000000032d800166a0000000000000c8d3e32d2d3b85e804080f1a1094372132840009c050428346980000000000000a460000000f4c000000300c00000000000007e800071e00000000002e739c00000004820000984d22000000193e7880000000594d560003048000000485800000018e00005340000002fdb184000a720000000000a8742300000000000000001b600000000000bec0000001c3d21815c06630adb40c1621200004f4db22dcb1cc0003760003a8c0000000000001d9e000046800000071700000001a63700002b9c00033969d8ea44080000000000000c1900021c86820216890b2566c0d045b800000098800000000000000cf800000062200000010ae000000000000074c2ca8000000000000267000066d1711dc8cdc9491f7930c000c962b8800181451c00000000000000000000000e7e000304000040c62103a0000a32000000000000041c0055114c5c022012800049a00000019389110001414f74a3d2a19dcd72c3af298864943cead2ca3654016000297b8c00001e153c12e800000000000000000000000000f609a400035e80000000000000d1e0000001f2dc56c9d59d8000000c4800000000000003821ea9b042e600016b00000000000000f580005b380019b09f8546240800000000000000000002718000000b8f0000c6052ce2e1058a61b52e230000000d6a000000000000000000013cc00000000000001b800000035080000820000001c100000000804ac432
  | 29 => 0x1dcb79884a0000000afc00000000000016ae13c000269c00000000000000000000000000000d7f200276575c93500001b5934939000000000000000000008700002b2a1800002362473009ca4d680000000000000654000000000000000001ba00000000000000004f30a7400000002e00000000000878000000611000000090e0000000000000000000238c0001a5291a92d28ca0b3e4928400086e0ac000186a0000000000ccc49e5cba5d11bc44f00000000007b10002fd000049b4db971400000000000000000000000000000d1b000000000000000004acb6a00000026a0df256900000000000000000cf000000000000004d0a7508589580c600000012a400000000000000000002b980000000000000000000d012f9800072c5ee6f680ed5363cf15a000000000000000000000000000000000b4671a80000007431faa27895e000000000000000000000000000000aa8000000373389849c0000001b8800161694c00000018e2da6000000196261500000000000000000001c36af62aa800000000000021400000003c21188000000000399000000000000000004536068d5cd824034378f295a60004408b700000000000000000cb90002bfc62ce9a0000ca53f800000029ec7140000000744bc60000002b7d402000756243c0000000001dd80000003bd80005f0d13000000000000000000000000000f21af4000a386be07bc000b66000000000000000014780000003fa0000000000000000086c0000000000000000000000000067426080018a6d0b2d780000000002dc0000000000000000000000000000011c00005070000000df837d000059a3b700000000000000000f08000000402a888000e405adb87c000ec100029211b4b2c00033a80006ba00000017b800044800015ee4cb51d072483a0004c30000756a420000001124b7d59a0000c9a0000002c380000000000000474000561000010c00010c80009060000000000000e0c0000dd4db259361680000003420002bb800000000000000002f6000000000000000001040008ff000197c9d49fa0000000000a9d000129400000015d80010600004f98000b80000534b39c0006b23a680009b000044c800090800000000000000e33ca800127a0000000bb40000000000000000dd441880000005e5154b664000000000000133e2cb000000071000068b800000000000037e80000000000001cce00000000000000006a8363c00000000000014a40000000000000159296800000000000010380006650000e117c400000000000000005df00000000005da800156a0000000001aa87684aa80000000000000001d7045100027b8000000000065000000000000000000000000000000de800000007a200000000015f0000000000073a0002910000000707000144400000013591
  | 30 => 0x6b15e72ad856a0000000000000000004800073e0000db800000000000000000000000000000f5c0001d4256137200000010557562c30000000000000000119c0000007468e840000003deaedc00000000000000009fb1d3234c000b4121e800103a000000054000000000000000007280000ecc27400069f124c0009e22e900008aea3100002b40000000000000472d9c278a705afc00000000000000000000000fca1a30000000de80000000000d3e3a3000000064e00000000017fa0fc0000000cee33231d92447041471b400000000002c700000000006bbb2e00000000000000000659709000190a1d00000000000000000258843a000000000000000000000010e0d3c0000000000000251000102c00000007b1d36a4c323aa580000000e61805b820b50a000000000000001514000ccb00700016c6000000000000000030680000000003bc800000060b00000e574a3363c92f58d8a000000176800000000000000004b542700000000002f1000097275d02ea0b40000000002374276000258a65db06e0006f046800078600000004e20006db80000000000002ea96de8830471b240000001328000000621531000000000006235100001b40001034f304b200000000000000000000000000000000000075f0001b280002e54b730947ca000054174c00037c5f480000000007280000000ea200000000004ce000000000000000000000007ef0000000000000055a0eca5600000000000005f4000000c000000084aee91cab9f0000000000ca61b2125c00063100000014b60000000001c2e9171fb15f80000000001798000ebb000000000000019d00000000ef0000000000d691a23358000000000000000080e4bc80000000000001f04000000208b34dc70734000000000000000000013846c600012c000000065d0000b20ae363d365c00078e00031f43f800000030e8000000000000000000000008a800000000b000099a00000026b8000a910000000c4e0000000000000000000000000000000000000000000000000bf00000003451448ea80000000000119000000000000000030f8c4039e1490001c1e000000089000000020d8000000000000000081406a35a039400026f67197c8ec2ba9000000000095a0000001cbe00000000000000004eaae78b7e00000019a16f4000000000000000069980000000000001e9c000756000000000055000000000000000000e18000bb80000000000aad000000116a000000000000001009b000159400000037f00000b46e28df80007151778000000cf200000000007060001a582d8055380a34150000026433e841057b3bd33b84f00005b5800147c000000000000000001aa2905a41a90a9b9dc000e9800005c00007ab69000000008a837480009a224100000016220
  | 31 => 0x21c80000009ce0000000dfab71000204000000000034bc0000000f3000000000023800000000005cd09f40000006dd0000000ed4000000076c9e90001f88000000000000000000000018680000000000db860800000030997b400035100014cc000652800000000069e8000000bb24608985812a5a2218001c5a1f7325916522a000000360400062d443800163200000008240000006cf8000000000000000085400017835e176c00065aafa80000003078000000000000132400000041b2a957480004740000000000000000120c83900014284907f96ff8acc41400048d2b54000d605988001a74000000000000000000000000000005c2997400000000000000000000001e6c000383000000000000000013a40000000000000000000000359c0004e70003628000b3c000000000000039800013762f92d900000000000000000000bcb0000000000000000000000000000000000000000000b1014e3f300012dc0000006363088000afe00000000000000003808000000000000000000000000000000003033a9872e1795010f64c140f35eb8000000c47000152000000000026fc00085f000000000000000000012681e5000000000000065680000000006ed800000000000020256f00007649510000e4826bb8b000000000022d01d80000000001b7ebb30000000000c820000000000b052ec91199c00f546618f40004782d82a199685b6356000000077e73b05d4374000000000020caa300000001080000000a0400000039b8000000000000000182a00039fb51c0000003999a8d98c00012c1bdc00000000000000000000d6800000000000000005aaa686e3917583eda176100019b4ed70000f15d000000002dc8000000000122c248d6a00008ec7d65c300006e460c00052f0000ac2000000385807400036380000002f1405a8b807e00049317f064a4860000000000d110000000e0600000000007620000000001446deb4a90000000000000093c00028554698ad2d296c45c95b0db60000cd0fdd7deb6d0002f6c61444a000000000000000000012f81136798000d34000000350000067b00006300000004970000914000000000013cd5e00020bc0001000000000000000000040c144856688165c00000000000000000004bb800165a0005fb9d400000001fd1254000000000000158a000000000000012f0003964000000000000000082100000017687a10300608000000000000002693f000007c00000071931c0000d381b784380000004e6000000000000000013f261921700000000005640000606d843af00006ce000000000000000060280000001d7137135191e5c83f3800011200000000000004130000000000000000000103000006680000000000003a50000d72095227ce7c000000055800099a0000
  | 32 => 0x8000878000000000000000000000000000002650000b7ae2064a000188a710000005c0000000000da4000b6230e80000000006cc23217ba58d24294fc00055f47ba35c00000036180000000001c800005ee14400000000000002d8800000000000035e40001575288d212d00000000000000bee00032f400045c54c350c98c5ba0000000d04000000000000000000036b800000023b8001180af5233053953cae400009306466af0b8800057800014032c800093107f84700000000002b180005d45160000000000000000000000021b8000000000000000015200000000009be97002f0000000000000000068a000000000032c00052b0000000da45c000000004f600019700000005688001cd07a56261ed0000c66524b54400069e00008f8000c8b41f0000000a61000389c0000000000000000000000268800000000000000000002cf17fc0002a200001159f8df9407a5112001813e38001412000000000000000000000013de0005f2000000000000000000000000002bbda6897f0000000fa0a14753800000000050ea19400000027a204d4ba0000001f70000000000000000000000000004ae00000000000003bc05b29cc0000a13ff00905840000e9069d760dd10000000000b5558100000008150002c3400000000000000000000000000000000000000000000000000000000004f6aa3944a6d000000000000005e10000000a95000221400000029e127005e0003e282dc000b790000000a4cd6d3b78001ce494100035bd90ed580001ac0862000000000000000075710045ae0000e9800000089a000000000000076380000ac000000000138e3e60000000c6627560580040000000000001d08d41000000086800036d000000000007480000000001fc0000000d754458000000a3c00029c40000000000000b1e774000054805891c0000000000cff000000000000030da2fc00019e00000003c4000000000000000000000015589ca0002938ab66955198000000820000000150463f00005a4b5a000000000030a0000001e44000000000000042a0004b2309053c9a0000000000071e000335162cc30000000151400000007a400000059cbb2800000017631892b200020e3b35ac400019e800000039c0000000d480000b025455340002a88001b00984413316154429c0000000e52aa413f80000040000000d4c00000038da9616ca8890a52130b4035d2e800000004b4000000000000000000000000000000000b12217000000119a00036b80000000005ae8000bd20d7000387400047b0000e480000002ae0abc3dcdf33c180000300000000674050967065000093a0003471ee0a6000000005b53e281e029000008400000000000000000000000000aa100007100000006ad0000000e5364f000164231372300016dc0000000000000
  | 33 => 0x25d5390d375af1d917ea0722868000ac80003bb800000000000038d061000072c00000003b2000000000000000000000000000000000000000000395000053b000000000000000004311de0000000001064dbe6eb2371dacab70d100000006980f8a494000000000000000000000020a0000442000006935e0000000000000000000214c0000005fc912dd7800000000016023200000000000000000000000090e00000000000000000000250c3f1d000000002d646a0b8400000000000009540000003a1400000000000000000000000000000000276313c000a0c00000017a800014a8001ce61930000000000000000000000000000000000000000000000370000000233c000a6772b81b0000dc90003855cd45c440c8000000e1a00000000007fb7410000000000000000000000008400000000000002b2cb4a0000000000e920000000000000000000000000000000000000009fd000044000005b4980000ab40000002a2065e000000000000018600011c82ceb0c0c8000000000000006a93b08a533a80000000004da00000000000001f540006bb510000044c0000003934d2e6b7000000000075b0000cb1a4e143000000000000000000013ac36c0eaa28825843e6811e8111a0000003678000000366000134a0005f4000163000000030ecf141ca00025f855a0000000001bc200031280000002320700000fd600000007cc00006500009700006a00002450000d466b080800000000002154000000000000143000051b8c007689e81a32231bd80002890000a1e58100012f80000000000000000000000000000000000000003e072a34e8000000000000000000000000000000000000000000000c9103fb47000000000000000d6000554800055479600000000000000000000000000000000053e86200005e00009d12a08000000000219194d8c84c0152b044000000000254c000a17391000000000041200000000005818000f50000156000000000000008b80000000000000000000000000000041044e80011d6751721a3b800000000000000000000003a70c8080d673071838aeb67640a2c0005015b53ae400000000018580000000000000000b2300015000005572c600000008510002b800000b3000000000000026e0001cfe00046f8000000d16184ad4048a00000000014a000000000000000000002af4c92000000000000000064300000000000000000180000000000046e2284b080000000000000000000bed0000000000000000338404698c000000191800000018c800017441a07a0f7e00000000000080000000000000000000363400000000020080000000001eec0000000002c10a0c04f0000000aa48692cb000000041708900000000000000000000000000000000000000000000007231f480008b0000542
  | 34 => 0x1bf08169ec0000000000dee06d286d84018067c800131e0002308f19006000160b7540000000001134000b42055159c0000000002bb00dcb2b00000000000005ef0a8c000c840c180000001c00000000000875000000005c0000000001b6200000000000000000000000000000052036dcfa652000000000000037500008d400000000000000000839e700007d80000001724b995758000000000000000000006822900000000000003328880000367055031a0000000000b4c0000000000000000000000000000000000000000002e60000b08000000032c0000000000000edc0000000000e2c00009281f0000db84920001be4ddd000052400000000000000000003b5000000000048811adacc51b000000000054e00000000001d4269a7dc000a1324608d1c620000001be00002000002abce2200000000013a8e8a4fb0c1c000af45728000550b8e18f0000a2e0b13dc86ec0005aa1013410fa6cce63680000009070000000000c000000000000000000000018e0003e1872100c00000000000000005d000011cc00000000000000000003a7c0000000000000ca800000011d966428e00030dd2306cb141a68c0000000000000000ce562580280000000000000000000000000000000000000000000000000000f5e3d00000001b260d200001240000000003320000000317087c29000000000000000000003454000ca7000000000081f000030c1265720000001152b6c00000000000836d7b8bd9e000000000000000000000000000c33000231c000e5c03d0000000000000000000000000013c8b760000000000000000000260c000000000000032ec80016800000000005e230c5a20006f8000118a0ce03d80010f4000703800000000000022f997e0000001460000000000000000000000005d80000190000000000000000000000e000000211400022c241248c0002220000000e78000000226c000000000000120a00072380000008cb4ff1c2dc1c00000038880000000001e900000001440000000000000000000000000000000000000000cb8000000000000151e00000021f866e0000000000000a97000000000000040a1a24000000000000144c0006ae800176263a6cd3ad000000000000008fe2d3334a6343b200000000000000000e780000000000000000000ec50001918000000000000000000000000019560000000000628966000000000019c55900017ca4290000000000000000000165c000000000000000000000017a0000000000000000000027ac00000008b0000000000000000000000000005981ee0006b60000ada000286099000017b4d59e1c0000002eb8000266abf000000000000031496617764883ce97bc3f20970000000000000000000000046d70585f1d165b732180000ec0000000000e48000099000000
  | 35 => 0x3030000a001e42bc4e4c9e14851f3c0000000000000000000644a1ec00000000000006349e00000f0c00000000000000004e62759fc80000000000000eeaa2d09080000000000003528a0eaf000000000000000000000d0c0000f1990540e000613800000000000000000000001fe000000000032d22b400000000000000000000000001b16dac00000000008f85c6000000000017916b800000000000000000000002e2c00013f00036cc00000000000010940002e48000000ed100012fcc94000048800000000035e000000000000039e400000003b80005be0000000001640000000141049400000018400000000000000000b0010d8000000e3b00000000000000000000a0400060d39280000000002bc80005b30b90094a660000000000480e280000861bbe5e15080000db024400000000000000000d505f4a407698001a545852c5833d59c0000000000000763000000000000000000000000000003914d5a00000000000000004f90000000000145000000000058d149062200000023a400078d0002c9800000000004f9aca0000002ac40000004ef0000e40937000128cb0e0000002734000a940000000000e0d2ec28a43be00000036886c20000000001c9253a515a1acecc0e10000000c0abfe75839c44782210000000a6e000000000030ea5f00023897082430001fa800000048f800000000000000000005fd00000005720000000000000000000000000000035c37d57be13546712040000005e980000000005fdb6f0caa00056d00500005770000000000000000000000021e000000000000000000000000000000000000000000000011844513500010fa00000000000000000000000000cae04f9aa0000000000000000000000000018f000000020f00000f90000000b340006153aa8000b890000001870000000000154c0004abb58c4ba0001931b459e800075e8000ba233f163800000000000020880000001318000000000309a79c00098e000000000000000000000000000000000000000379000157400037a800000042f690800024030200000007f20006ac8000aba0006268000000000000000000031c00000000003e10000001c0631900000000009b10000000000000000370921a000000000000066127d35cc0000005540000000d94000000058a00000000011f40000000a90ee200050fba2000000000037385ce63e000000189c00000000005f8000000000112c000000000000000046c0000da400000000000002b800019c52546bf0001f68000bcf000000053435640d800008e0000000000f9a000470923d45400000000000002385251b94000bc400035d800021300000000002b039c800000000058a00000000000000000000000000316c82809000000000980006500000000000000000000000000
  | 36 => 0xc28000261c39a94b489115000032800000000000000000000fccb911859e5ca8e938000000000000000029500005460001299d80000000000000000000000000000005e40000000000000000000000047ca5ac0000000002aa87128733bc2fc41c800000000014f4000000000096c000002800000000000000012022460001a4800000000000000000001f20001b1c000335393851284b1f38db400000008100000005f500013ec0000001d6800000000075d0000000000000329012c4606c28001a9853600039e000000069a8001a1432b000000000000064a800000000000000000004e545c27d427a000000000000000000000000003bb59c0000000c68000000000000000037f400000000000005c000000012e000000022a888c08600011480011ece360002cc0e8c000000000095a0000001a959a489117a187085059266a800000000000000018f6c832af0000d220002ab000000000000000000000003cc94f4000c1c2a7944c7aa4ae51a94a5852a163b580008328436cdb9ec4c40000001b340000000003165b3a0000000000000000377800172800000000000000000002ba4ea60001dd000000013934c91200005280001c0000000052c800000000000000017c60002d5800000000033380013305f70000ab80000002928b8c0000783f600011fa114000000000000000000008920003e905a05d40006580000000000000000122c0000003308000000293a51c0000006470000000000000131c7b40006758000000000361225c5fe68104c0000000bd90688001c4c1230000de00000005d40000000d900980000000000000000061e030000000000000000000000000002768000000276000000000000000029d80000003b80000000000201000000001200000002c881a253aa6503842140bb40ca3472f0000000000b0f000045c000000000379132400000000000000d900000000000000000000000daa000012c00000000030c8000d0c0001e500000001f5000143227c3ff8001276000167800000032100000000000000000000fda9452030ec0f90000505000000064f00000003d600045500000001bf2b500000000001a48000000bfc0000001d1200000000000000000000000000000182a794000e6e2e1392da4647a0000001aae00002c22380000000003625cc60c9000000031ea740ff00000000004e780000005cf000000000000000000000000000000000000d000000000ecacd93a12d25652000000000000000000000000000000000000000b2832200000000000002814d20000000000000000000033310c60000001b8800063000036d844a0003c287040000004138000000000000000000000000008cc00000020f83e800000000036ad0220005740000000000102a30828cd0e42c000000000000016900
  | 37 => 0x8080000002d4800000035080018d662866fba18000ce26a41e2d9584ab0000000e8ec903d48000000000000000054263500000000005090000e5400000036eadfd1e2210763000028a000000000000000000037d0000000000000000000000000000000005680000000c180000000000000000201c0000000001781c7ab611c280000a20007150000f7c46f52398e00007602a69989576d8800000004e87e1000000000085a741800000030d4e280000000000000001cb40006c39fd80004900240e38000c8800000000000000000001bc62ee6ad8b5196e82c1c082c090093a62eb9e98c6ac30000000000000000364417e8f500000000000003760000ab000000000004f20000000000000a890000d1c00000007b01889ba000000000000000063488348100001df91c510400000000002c40002598000000b120000000000252000379d4dc00001e93112f00000002c7032200007c0000000de20330000000000000000000000063500000000000002cfcca0000000000091200003f293c41e000479ac7c0008412c1000000038d37437609fe00000005092da00000000000000000002fc92ec000000000023e00000009817ec1b2559800000000000000011666e636000008ca0000000000000000712a83c0002de75b9bb51602db08200000000000001f0011e00000000000000ea086af81252000000198000074b0000000000c574e30a98132a840000f8000000000000000000001dc00000000000002dd192474f00000005640004b9257460200000000003e80000000000000000000000057c000000000000014b0003a7400000009480000000000001d5400036514618bc00036a55f000163a0870000f8800000000035f4000000000000000000011a93bd4c800000000000000000000001188b8300000000005155a180000000000000001366000000139000000000000000000002eea57dc260004bd8bac00043f06f800078024d060800000000000015fd932af9000000000000000022e80000000001b8c0007f10001f740000002bc8000000000000000006800061cae98ed83a40001bad14e000000000000000014228fc8f2beb66800003360000000000000000000000000000000019d80000000000a08000e7400000007262f30e700004965190f000000000000000dfc00000000000000000002270000310000000260800000000000000000000000000000000000373400004d49400010d41dc000000133678f6d423251c80000e580013a40002c0000000000051d9b11daa0000000ea8000433000384400000000000000000000000000c1000067680001e20000000000000000000000000057c0000000000000000039d4860001c88001540b1e00012a075c0003eb24889a0000000000000035e0000000000000000091c00050b0
  | 38 => 0x5785b20000ff9a2c000000000000016400006290ac000645749800023c66f38c35eca1c0000000000e700004d63a5400077c68f80018280002cca5f4e1c6f65cc1a349b24633990bf583a71a7309c509c20000002d70000000000179da920000002f9c00000000000016be000000000162e3cb000000000000002c800000000000000000000003868000000000000000000000063716f0000a2709700000009f4000000006400012100000001e738500019ee00071f80000000006dc9e04000b0a0003158000c6000000000000004ef800000000000000000001c70148275bdeed06779b20e1800016600000000000000001758c9700000015e600020388c062400000000017a200000037a40003ce00027a80000000000000000000000000000000027eb4780000000003730876b7e31bad300000000003148000d2c00000000000000000000000c755d139444248e702f80000000003598000000000000000000000000032bcdfe00048c800000000027000000005c1000000008c00000000000000000000fc9d7e00000000006a0e90353000165e9cb41b80000000000b280000000610000000ce62555a3916c000c7905e800000082b6b70a400000000000000000000000140c0000000001938a7200050d20b9582ab8000000151600000018d8000eaf000108dc720000000000000c555a8800173ab3a1ba00000000000000000000d09000000000000000022ac000c7e00000000000000000001a0e31f0000001
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe95434c762440059b0e6986c4880121fa1f75589100043ec1eeab1220038be87dd1624400187eebba2c4880030f1d774589100045ec1ee8b122000c3f751d16244001878ea3a2c48800a37a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fc2ee6b122000c5c85dcd624400193f09b9ac4880032721373589100043fc2ae6b12200487c855cd624400117f08b9ac48800e2f21173589100046f438e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b12200087e87d4d62440090f90fa9ac4880030fdd3535891049e1e3a6a6b122000c5f73d4d62440058b8e7a9ac4880021fa1d53589100043e43aa6b122000c3f7454d6244125878e8a9ac48800317dcd53589100162e39aa6b1220008be87d0d62440071790fa1ac4880030fdd7435891048e1e3ae86b122000c9f73d0d6244005938e7a1ac4880022fa1d43589100045e43a86b122000c3f7550d6244121878eaa1ac48800327dcd43589100164e39a86b122000e1d5350d62440051d90e992c48800b331cd32589100166a39c62b1220028f4874c56244001d2a8698ac48800b361ce30589100147c43a60b122002cd8734c16244001d9264982c4880021fe1576549100045fc22eca9220038bc845d952440011bf06bb2a48800a3720d765491000c3e43acaa92203ea3c84595524400b1f50db82a4880021fe1576509100243e42aeca1220008bf845d942440011bf06bb2848800a3720d76509100061e3a6caa8a2000c3c75d91414405b56908b2c42880039994b654851000c7a43aca90a202aab4845952144001ccacaa924288002f82015248510005724328490a200587f87596504405147908b2ca0880031dd9771541100061e3aec8a022028c7876dd540440bb8f0ec3aa80880173c1da2150110004f843a42a022005cf0764854044001f428490a80880163be1d628811009e733b24310220068f686dc520440050f90bb9aca0801a1f21d53594100062fb9aa6b282002c9e7350d650400193ae6a1aca080038754d43594100243f43eeab20200087d83dd5640400187e87baac8080029760c75590100145e426e6b20200087f855cd64040090f90ab9ac8080163d20573590100043f43ea6b20200487c87d4d64040010fd0ea9ac8080021f21d53590100162f39aa6b202000c5d7354d640400d1790ea1ac8080030fdd543590104861e3aa86b202000c9f7350d6404001c3aa6a1ac808016ad20543590103f43fc2aecaa0200687c87595540400d1790eb22a8080063d60774588100070ea9a86b1020068ec874c9620400d0f90eb2aa40801a3b21d62548100043fc2aeca10200487c855d9420400d1790eb22840801a3b21d62508100063ba9eec8802000c7553dd9100400196e87bb220080032d50f7644010
  | 1 => 0x90eb2aa5880163b21d6254b1002c76416eca1620058ec8758942c40035cd04b2a43880039994965487100053bc1aca90e2000a758359521c4001c6e86b2a43880038d50d654871000733412ca90e2000e658259521c400b8eee4b2a438801799dc9654871000733212ca90e2000e663259521c4001cca64b2a438800399081654871000573c32a490e2000e656554921c40015cf0ca1243880039959542487100063ab2ee2a86200087d86dd540c40018dcc5baa81880a21fa1d65503102ec3e43acaa062000c6f7558940c40018d8eab128188017391c5625031000672b16e2a06200cce57648620c4001ccaca90c41880021f61b754831013637316ea906202687e8759520c40ad0f90eb2a41880031bdd56248310006363aac49062000ce562dc520c400117f06ba6cb080030fd4d74d96100143fc3aa7b2c2092c3e7454f658400187ae8a9ecb08003175cd53d961001c5fc3e87b2c20008bd87d0f658400117f0ea1ecb080022f61d43d96100070ea9a87b2c200687e87951658400187ee92a2cb0801a1f21d53596100062fb9aa6b2c2000e1d5350d65840010ff06baec9080030fd0d75d92100243fc3ea7b24200087d87d4f64840010ff0ea9ec9080021f61d53d92100145fc3a87b242090c3e7550f648400187aeaa1ec908003275cd43d92100070ea9a87b2420068be87d51648400187eebaa2c90801a2f21d43592100064fb9a86b242000e1d5350d6484001c3aa6a1ec5080121fa177458a100043ec2ee8b142000c9f7350d6284005938e6a1ac5080038754d4358a100347643a64b142000ec9324c1628400d1f100bb2a50801a1f21d6554a100345e43ac8a142000c3c745955184001878eab22830801b3a1c162486100061eba4a9b2a2000a798095365440050ff0ea9eca88003175cd53d95100070ea9a87b2a2000a758194b654400717d0fba2ca880022f60f74595100061fa9ee8b2a2000c3f751d1654400117f08b9aca8800e2f211735951000477c12e6b2a20018ec825cd65440050f90ea9aca880030fdd153595104961e3a2a6b2a2000c5f7354d654400117d0fa1aca8800e2f21f43595100045f43a86b2a20008bc8750d6544001c3aa6a1aca880030f5d754d91100145fc3a87b222000c9d7350f6444001c3aa6a1ec8880028fa1642d91100243f43eeab22200087d83dd5644400187e87baac8880030f1d774591100043fc2ae6b22200487c855cd64440011df04b9ac8880063b20973591100047bc0ae6b22200087e87d4d64440090f90fa9ac8880021fa1d53591100043e43aa6b2220028bc8750d644400187eeaa1ac8882430f1d543591100064fb9a86b222000e1d5350d64440010ff0abb2a8880022fe1176551100347b436e2aa2200087f855d362440090f90aba6c4880163d20574d89100070ea9a87b122000
  | 2 => 0x330597100b43f43860b2e200087d870c165c400147d08182cb880028f61030597100053741060b2e2000a6d820c165c400b4ed02182cb880029d60430597100072c98060b2e2005a7681c8165c40014eb03902cb8805a1fa1c20597100043ec3840b2e2000a3e8408165c400147b08102cb8800297a0c20597100052ec1840b2e2005a768108165c40014eb02102cb880162f21d43593100064fb9a86b262000e1d5350d64c400d1e902bb2a9880161f21d655531001d1e422caaa62000c7565dc554c40090fd0bba2c5880021f6177458b100070ea9a86b1620058ee87d4962c400b1dd0fa12c5880163ba1f3258b100053742e64b162000a6d85cc962c400155d09992c588002ab6133258b1002d7340e64b1620058ec874c962c4005998e6992c588003a550d3158b1002d73408eab162013ae5811d562c40014dd0bba2c5880029b6177458b1002d7340ee8b162013ae581dd162c4001c5ea92a2c588002b9e055458b1002d7240aa8b162000ace8315162c400159b062a2c588016b9a045458b1000572c08a8b162000a6e859cd62c40014db0b39ac588002aba127358b1000556c24e6b162005ae6819cd62c40015cb0339ac5880029ba147358b1000536c28e6b162000aae841cd62c400155b0839ac588003335cc7358b1002d73408e6b162013ae5811cd62c40275d50039ac588002ba6007358b104b73318ea6b162097a6d8594d62c400155d0929ac588002ab6125358b1002d7340ca6b162000ae58194d62c4001c9f06a9ac58825f998c55358b104b537428a6b162000aae8414d62c400155b0829ac588016b9a045358b1000572c08a6b162000e2f53d0d62c4001c5aa7a1ac588253a98c74358b100053742c86b162000a6d8590d62c412b55b0921ac5880039354e4358b1002d7340c86b162000ae58190d62c4001c9aa6a1ac588003a3e0d4358b1000717a9a86b162000e8e5350d62c4001c5aa6a1ac588003a354d4358b1000706a9a86b162095e8f3150d62c412bd4c62a1ac588257a34c54358b100053742886b162000a6d8510d62c412955d0821ac588016b9a044358b1000572c0886b162005ae7834c562c400bd8f0698ac58800399d4d3158b1000732a9a62b162000ea7434c562c4001d8c8698ac588003a950d3158b1000762a1a62b162000e85434c562c40014df0ab82c5880029b2157058b1000557c22e0b162000aac845c162c400159f06b82c588002b320d7058b1002d7340ea0b162000ae581d4162c40014dd0b982c5880029b6173058b100055742660b162000aad84cc162c400b5cd03982c588002b96073058b1009c7743860b1620008ed870c162c40014dd0a182c5880029b6143058b100055742060b162000aad840c162c400b5cd02182c588002b96043058b100076498060b16200587c85dd952c400b0f
  | 3 => 0x6b2240008ef825cd64480011ef02b9ac8900163d20573591200043f43ea6b22400487c87d4d64480010fd0ea9ac8900021f21d53591200145e43a86b224000c3f7550d6448121878eaa1ac89000327dcd43591200164e39a86b224000e1d5350d644800b1ed033b2a8900023d60676551200043fc2aecaa2400387e87d95544800193ee6a1ec29000b271cd43d85200070ea9a87b0a4000ec9324c361481318f2e032cc2900021fa1f65585200061e3a6cab0a4000c5c73d9561480010fd0e32ac2900030f1d065585200062e398cab0a4000c3f65dd16148001878cbba2c29000317d9773585200062e32ee6b0a40008f787584614800717d093b2a2900022f61276545200061e3a6caa8a4005a7681d95514800187ecbba2a2900d30f19774545200043fc2aed20a400487c855da41480011bf06bb4829000a3720d76905200243f42eeca0a400087d85dd941480090fd0b3b282900021f61676505200243e428eca0a400087e86dd541480010fd0fb2a82900021f21f655052013636396caa824000c6f65dc950480ad0fd0dbaa80901761fa1f65501201343e43ecaa024026c6e76d9620480098dcec32c40900161fa1e54597100061fba4a8b2e200587e8794d65c400147d0929acb880028f612535971002c3e43aa6b2e2000c5f7354d65c400593ce6a1acb88003275cd43597100070f29a86b2e2000e1d5350d65c400b0fd0f292cb880169da0652597100061fba4e8b2e2005a74815d165c400187ae83a2cb8800297a0c74597100052ec18e8b2e2096c7621dcd65c412f0fb0f39acb880028fa1273597100051ec24e6b2e2005a76819cd65c40014eb0339acb8800317e0d73597104be3b10ae6b2e209687e871cd65c400147d0839acb880028f61073597100061fb9e86b2e2000c3d73d0d65c4129c6c43a1acb880021fa1e43597100043ec3c86b2e2095a3d8490d65c40018bae721acb88003175cd43597100070fc1a86b2e2000c3f7350d65c4001c3ce6a1acb880030f5cd43597100070eb9a86b2e2000c1d7350d65c412bc3e62a1acb88257874c543597104af1b10a86b2e200087e8710d65c40010fb0e21acb882528fa1043597100051f424e4b2e2000a3d849c965c400b4ed03392cb880029d606725971002d3b408e4b2e2016a75811c965c40010fd0f212cb880021f61e425971002d3b40c84b2e2000a758190965c400b4ed02212cb880029d60442597100043f43e64b2e200087d87cc965c400147d09992cb880028f613325971002d3b40c64b2e2000a75818c965c40010fd0e192cb880021f61c32597100051f42064b2e2000a3d840c965c400b4ed02192cb880029d60432597100053d40064b2e2000a79800c965c400147f08b82cb880028f21170597100043f43e60b2e200087d87cc165c400147d09982cb880028f61
  | 4 => 0x54800193ee6a1eca9000b271cd43d95200070f29a87b2a4000e1d5350f65480014bd07326ca900029760e64d95200062eb9ec7b2a4000a3e8498f654800147b0931eca900661f61c63d95200051f420c7b2a4000a3d8418f65480018bae631eca900029da0463d95200053ac08c7b2a4091c3e76d0f654812187ceca1eca9000347dcd43d95200070fb1a87b2a4000e1c6350f6548001c98c6996ca9009a9e21930d95200072c31a61b2a4000f49324c365480014ed03ba6ca900029d60774d95200052f41ce9b2a4000a5d839d3654800187ae83a6ca900021f61e73d95200051f424e7b2a4000a3d849cf65480018bf06b9eca900028fa1073d95200051ec20e7b2a4026a6e821cf65480014db0439eca900029da0473d95200053ac08e7b2a4000a7a801cf654804d4f30039eca900030fdcf43d95200061eb9e87b2a400087e8790f65480010fb0f21eca9000317dce43d95200062fb9a87b2a4000e1f8350f654800187ee6a1eca9000387dcd43d95200060fb9a87b2a4000c3d7350f6548001c38e6a1eca900021fa1c43d95200043ec3887b2a4000a3e84dc7654800147b09b8eca9009a9ba0a71d952000536c14e3b2a4000c77719c765480010fd0e20eca900021f61c41d95200052f41883b2a4000a5d83107654804d4dd0420eca900029b60841d95200053d40083b2a4000a798010765480010fd0f98eca900021f61f31d95200051f42663b2a4000a3d84cc76548001c3a8798eca900038750d31d95200043f43863b2a400087d870c7654800147d0818eca900028f61031d95201353741063b2a4000a6d820c765480014f50018eca900029e60031d95201343f43e61b2a400087d87cc3654800147d09986ca900028f61330d95200043f43861b2a401987d870c3654800147d08186ca900028f61030d95201353741061b2a4000a6d820c365480014ed02186ca900029d60430d95200072c98061b2a400087f855cd65480011df04b9aca900023ee0173595200143e43aa6b2a4000c5f7354d654800193ee6a1aca9000b271cd43595200070ea9a86b2a4000a5e8399065480014bb07320ca900021fe1f63195200062eb9ec632a400087d8798c654800147d09318ca900028f61263195200043fc3ac632a4000a6f8258c65481394f700b18ca900121fa1c63195200043ec38c632a4000a3e8418c654800147b08318ca90003175cc63195200053b408c632a4000a758118c654813787ceda18ca9026b0f9d943195200068eb9a8632a4000e1f6350c6548001c38c6a18ca900029b21932195204cd3d4346032a4056a78864c06548001e9264980ca9000a2fe1d43d91200064eb9a87b224000e1d5350f64480010fd0fb2ac8900021fa1c65591200243f43eeab22400087d83dd5644800187e87baac8900021fe1573591200243e42ae
  | 5 => 0x28f61030d95400053741061b2a8000a6d820c365500014ed02186caa00029d60430d95400072c98061b2a800087e87083655003f0fb0e106caa00a28fa1020d95400052f41841b2a8000a5d8308365500014ed02106caa00029d60420d95400043fc2ae6b2a80008ef825cd65500031d904b9acaa00023de05735954002c7a40ae6b2a800287c8754d65500018bee6a9acaa000a2f21d43595400064fb9a86b2a8000e1d5350d65500010ff0fb18caa0003175cf63195400043ec3cc632a8000a3d8498c65500010ff0eb18caa00029be09631954000536412c632a8000a778158c65500014e902b18caa00121fa1c63195400043ec38c632a805da3e8418c65500018bae6318caa00028f21943195401461f3b28632a8000d1d7350c6550001c3ec6a18caa00029da0662195400053ac0cc432a8000e1d5350f62500010fd0fb2ac4a00021fa1c655894000c3f43ecaa928000c3c76d954250001c58c5b2a84a00030f1d865509400064fb9a87b0a8000e1d5350f6150001d2a8798ec2a0002ad61031d854000572c1063b0a8000af1800c761500018dce5b2cc2a00031b9c8659854000637b2ae530a8000c6c655ca615000b9c8c2b94c2a0003395cb61985400043f43ecab0a800087e8719561500011ef0eb08c2a00031ed96709454002c7c432e128a80038bc841d95150051878e9b2aa2a00030fd9774545401a61e32ee8a8a800087f855da21500090f90abb442a00163d20576885400063c32ce110a80058f8865c221500018f0cab8442a00173c18570885400243f42eec90a800087d85dd921500035590ca1242a00063da1f61485401461e3a6caa828000c3f65dd1505005187cedb2c80a00a38ed8365901400261f3b0cb2028000c3d7495365880050ff0ea9ecb10003175cd53d96200070ea9a87b2c400687c8754d65880018bee6a9acb100038754d43596200145fc3a87b244000c9d7350f6488001c3aa6a1ec9100121fa1f75592200043ec1eeab244000c3f43dd564880018de43baac9100021fe1573592200243e42ae6b2440008f7815cd648800b1e902b9ac9100021fa1f53592200243e43ea6b24400087e8754d64880010f90ea9ac91001a2f21d43592200061fbaa86b244090c3c7550d648800193ee6a1ac9100038754d43592200043fc2aecaa44000e1d5350d618800d1e90e98ac310003a550d31586200166c39a60b0c40008bf845d9518800717908bb2a3100161fa1f65546200061e3a6caa8c4005a7681d9551880010ff0abb283100121f215765062002c7743eca90c40058ee87d9121880014df0ab224310016b92056448620005b2c2cc290c4000e676554521880b574908a8a43100323b61b70486200061eba4a9b2a4000a3e8494f654800147b0929eca900029b60a53d95200143fc3aa7b2a4000c5d7354f6
  | 6 => 0x69a3a4c2a8ca000b6582985519400b4ef0cb0aa3280034d1d1615465007c3ec36e0a8ca000d3b74dc15194001a70e8382a3280030f5d5649065002e3b30aeb10ca005c7776546219413d66908a8c432801a3d21d6148650024ba43aa290ca005a778654521940018eeeca8a4328276cd21151486500062fb9aa7b22a0028bf8750f645400193ae6a1ec8a80038754d43d915000c3e42ae9b12a000e1d5350f62540014db0b996c4a80038754d43d85500047bc3ac230aa00487c851d9415400b1ed033b442a80069b21952485500243e432e5282a026c6c625ca50540050ff0ea9ecb20003175cd53d96404be3b38aa7b2c80028bf8750f659000193ae6a1ecb200038754d43d96404ae5b38a87b2c8000c77535c765900018eaa6b8ecb200032dd0d71d96400065aa1ae3b2c800687c8754d65900018bee6a9acb20003275cd43596400070ea9a86b2c8000e1d5350d629000d1d90e992c52001a1f21d6554a400064eb9a86b0c8000e1d5350d61900018eeeba8ac320002b960851586400347a43a62b0c8000e95434c561900014ef02b2ca3200161fa1f65546401461e3a6caa8c8005a7681d95519000d1e90eb0a43200028f61253d95400143fc3aa7b2a8000c5d7354f655000193ee6a1ecaa00038794d43d95400070ea9a87b2a8000a3d8494b65500018bae7b1ecaa00029be0963d954000536412c7b2a8000a778158f65500014e902b1ecaa007e1f61c63d95400062eb98c7b2a805dc3e7650f6550001a3ee6a1ecaa000387d8d43d95400070e31a87b2a8000a768198b65500014eb03316caa00030fd0f73d95400062f21ee7b2a8000c5d43dcf65500010fb0f39ecaa00a28fa1273d95400051ec24e7b2a8000c5f835cf655000187e86b9ecaa00a28fa1073d95400051ec20e7b2a8028a3f8350f6550051c3f06a1ecaa00030fdcd43d95400070fb9a87b2a8000c1f7350f655000187ae6a1ecaa0003871cd43d95400053b40ce5b2a8000a75819cb655005147d08396caa00028f61072d95400043f43e65b2a800087d87ccb655005147d09996caa00028f61332d95400043f43865b2a800087d870cb655005147d08196caa00028f61032d95400053b40865b2a8000a75810cb65500014f500196caa00029e60032d95400051ec26e3b2a8000a6e829c765500014db0538ecaa00a29e60071d95400043f43e63b2a800087d87cc7655005147d0998ecaa00028f61331d95400070ea1e63b2a8000e1d434c765500010fd0e18ecaa00021f61c31d95401451f42063b2a8000a3d840c765500014dd0418ecaa00029b60831d95400053d40063b2a8000a79800c765500010fd0e10ecaa00021f61c21d95401443f43e61b2a800087d87cc3655005147d09986caa00028f61330d95400043f43861b2a801f87d870c3655005147d08186caa
  | 7 => 0x7c8754d654840187ee8a9aca90a4b0f1d153595210062fb9aa6b2a42008be87d0d65484071790fa1aca908022fa1d43595210045e43a86b2a4200e1d5350d654840187aebaa6c890802ab60b54d91210055ac0ea9b2242018f581dcf64485458eae3a9ec890a871d5c553d91210145fc3a87b224200c9d7350f6448401c3aa6a1ec890a7f2d5c543d91210243f43eeab22420087d83dd5644840187e87baac8908030f1d774591210043fc2ae6b22420487c855cd64484011f700b9ac89081a3e20173591210043f43ea6b22420487c87d4d64484010fd0ea9ac8908021f21d53591210145e43a86b224200c3f7550d6448521878eaa1ac89080327dcd43591210070ea9a86b22420087f855d9544840117f08bb2a8908063da1b715512100cb6c2ee8a924274d2e54dd1524840b3cd03ba2a4909d369107745492102cf3408e0a9242058ec865d542484016cb0a38a849081679a047050921005b3c2a8528a4200de0205c25148401878e9b2aa2908165b21d525452102d36432a4a8a4274d2c74549514840b6c902a92a2908034d1d36554521154db43ee8a8a4234cb476dd15148509968ec3a2a2909f34ddd47454521005cac18e8a8a4205974875515148455a68e8aa2a290803691d3725452102db243aa4a8a4201d6487549514840b6cd0ca92a290816d9219525452102732432a4a8a4204e67765495148403acceca92a290807591d95254521027323b2a4a8a4200b67845495148401e4ee8a92a2909d3599d152545213a6b23a2a4a8a4200f247454951484e9a48e8a92a290a96d9e0d525452152db2c1aa4a8a42a4d67735495148549acae6a92a290a8fc9d0d525452151f92a1aa4a8a4200b648054951484016cb0aa12a2908ab691d1425452100cf3416e0a8a4200d6552dc15148401878ebb2282908038754d43d81210166639a65b024200e95434c7604840b9cae498ec0908023ee1d60181210043fc2ae8302420487c855d060485458eae3a98c09080b179cd53181210062eb9aa630242a1c757154c604854196ae3a18c09080b279cd43181210064eb9a863024200e1d5350c604853f96ae2a18c0908030f95373592500061f2a2e6b24a028a3e8454d64940018bae6a9ac92801a2f21d43592500051fc2a86b24a000c9f7350d6494001c3aa6a1ac9280163da077458a500047ac0ee8b14a000c9f7350d6294005938e6a1ac5280038754d4358a500347643a64b14a0068bc87591429400187eeab2285280038754d43586500053ac2882b0ca000ad58310561940015cb0420ac32801abca0041586500347a43a62b0ca000e95434c5619405127d0fba2a32821b0fddb74546504371b30ee8a8ca07cc3f761d151940f9878ec3a2a328002c760c74546503e71b308e8a8ca07c87c875915194051878e8b22a3280030f1d162546500
  | 8 => 0x8196caa08028f61032d95413f53b40865b2a8200a75810cb65504014f500196caa08029e60032d95411d43f43e63b2a820087d87cc7655047547d0998ecaa08028f61331d95410070ea1e63b2a8200e1d434c765504010fd0f986caa08021f61f30d95411d51f42661b2a8200a3d84cc365504010fd0e186caa08021f61c30d95411d51f42061b2a8200a3d840c365504014dd04186caa08029b60830d95413f53b40861b2a8200a75810c365504010fd0e106caa08021f61c20d95411d51f42041b2a8200a3d8408365504014bd06106caa08029760c20d95413f53b40841b2a8200a758108365504010ff0ab9acaa08022fe1173595410047bc0ae6b2a820287c8754d655046987ee8a9acaa080317dcd53595410045f43a86b2a82028bc8750d655040193ee6a1acaa08038754d43595411a61fb22e632a820087f87d8c65504018bae7b18caa08021f61e63195410051ec24c632a820087f8758c655040147f08b18caa0aa29de0563195410243f438c632a820087d8718c65504f747d08318caa0803175cc63195413e51f4328632a827ca3c8650c655047587ceca18caa0803475cd43195410070fb1a8632a827cb348150c655040147b09310caa0a9e9d60662195410070ea9a87b12820087e87d9562504010fd0e32ac4a08061fa1f65549411d61e3a6caa8a8200c3f65dd15150469878cbba2a2a08038754d43d81415363ab88cb302827e87c86dd560504010fd0fb2ac0a08021fa1c65581410047dc3ac03028202c5e7354c60504018bae6a98c0a08038754d43181410043fc2ae4302820487c855c8605040b0f90ea9acb1080317dcd53596210164f39a86b2c4200c9d7350d6588401c3aa6a1acb108121fa1f75592213f63a38eeab24420087d83dd5648840187e87baac9109fb1bc8775592213f63690eeab24427cc74711d564884010ff0ab9ac9108121f215735922102c7a40ae6b24420087e87d4d64884090f90fa9ac910a5b1d1c753592210043f43aa6b24420087c8754d648852f8e8e2a9ac9108162f21d43592210061fbaa86b244290c3c7550d648840193ee6a1ac9108038754d435922102d5a40a86b244295cb47150d64884fd0ff0abb2a9108163d205765522102c3e43acaaa4427c9b687dd151884f9a6eea3a2a310802e560c745462102cba43aa8a8c422dd3474551518852d8ece3a9cc110a5f1d9c553982214a65b38e873044200e1d5350e608852b96ce2a1cc1108038754d43582210074aa1a62b044205af281d41608840b1f10e982c11080b361cd30582210061eba4a9b2a4200a6d8295365484050ff0ea9eca90803175cd53d95210070ea9a87b2a42038be87dd1654840117b07ba2ca908030fd4f74595210061fba8e8b2a42008bf845cd654840717908b9aca908023ee0173595210347c402e6b2a42028
  | 9 => 0x20d91511d61fb2ae6322a200d1f535cc645440193d0cb98c8a88032721973191510068f42ae6322a200d1d855cc645447593ecab98c8a88eb07d9573191510068fa92e6322a27dc9f615cc6454401b2ea2b98c8a88034794573191510068e28ae6322a200d94515cc6454401a38a0b98c8a8803275cf63191510045ec3cc6322a200a3d8598c645440193ae7318c8a88022fe1d63191510051fc2ac6322a200c9d7358c645455756f02b18c8a880e2fa1c63191510045ec38c6322a293a3e8518c645440193ae6318c8a89f28fa1953191513e51e432a6322a200d1d7354c6454401c3ec6a98c8a88028f61662191510064eb9cc4322a2aaab581988645440193ae6310c8a880e8fa1b64551514361e3b6c8aa2a28ac3c64dc9545450da6ee838aa8a8802d960871551512ee1e320e0aa2a28ac3c75193625440153b06326c4a880b279cd43d89510064eb9a87b12a200e1d5350f625440117d0fb22c4a88022fa1c64589510054ec18c8b12a27c87e86dd1525447d878c9ba2a4a88fa8fa1b64549514361e3b6c8a92a27cc3e7619152544f9878ec322a4a8802c760c645495100716326c4a92a200c3c641c1525440b0f90cbaa84a88fb0f191755095100c5f43ec8a12a200a9d83193605440593ce6a1ec0a8803275cd43d81510070ea9a87b02a25687f8754b605440153b06324c0a8aa72d5c464981514345e436e8b02a2008be87d91605440117d0e322c0a8802a760c64581512ee1e3a8c8302a200a9d8319060544011f70eb00c0a880b279cd43181510064eb9a86302a200e1d5350c605440187ea9b9acb208030fd51735964102c3e43aa6b2c8200a3f8454d65904018bee6a9acb208d28fa1543596410164f39a86b2c8200c9d7350d6590401c3aa6a1acb208038754d4358a4102c7643a64b148202ccc734c9629040b0f90eb2aa5208030f5977454a4102c7643ac4a948200e1d5350e6090401c3aa6a1ac1208163e21d30582410166c39a60b048200a3d8494f65504050ff0ea9ecaa0803175cd53d95410064fb9a87b2a8200e1e5350f6550401c3aa6a1ecaa0803175cf63d954118c3ec38c7b2a8200c5d7318f65504fd4790ca1ecaa09ef0f9d943d95410068fb9a87b2a8200e1f6350f6550401c38c6a1ecaa09facd20543d954137d3ac0cc5b2a8200c3f43dcf65504018bc87b9ecaa08031750f73d95410043ec3ce7b2a823aa3e849cf655040147b0939ecaa080317e0d73d95410061fa1ae7b2a823aa3e841cf65504fd47b0839ecaa08ea8fe0d43d95411d70fc1a87b2a8200c3f7350f6550401c3ee6a1ecaa080307dcd43d95410061eb9a87b2a8200e1c7350f65504fd4ed03396caa09be9d60672d95410043f43e65b2a820087d87ccb655047547d09996caa08028f61332d95410043f43865b2a820087d870cb655047547d
  | 10 => 0x302a4068f8805cc605480d9b060b98c0a92861f61d53181520053dc02a6302a4a0c3d75d0c605493f87aeaa18c0a900b279cd43181520064eb9a86302a400e1d5350c60548014f30b980c0a900a1fe1d53d95420062eb9aa7b2a8400c9f7350f6550801c3aa6a1ecaa12b30fdd774595420047bc0ae6b2a84058f4815cd65508011f700b9acaa101a3e20173595420143e43aa6b2a8400c5f7354d65508051790ea1acaa100327dcd43595420070ea9a86b2a8400c9f7350f6150801c3aa6a1ec2a10021fe1570d85420243e42ae1b0a84008f7875846150801c3aa6a1ec0a10023ee1d60181420064fa1ae630284a2c3d74d4c605094387ae8a98c0a100b179cd53181420062eb9aa6302849f8bd8750c6050801c3aa6a18c0a10030f95373592510061f2a2e6b24a23aa3e8454d64944018bae6a9ac9288162f21d43592510051fc2a86b24a200c9f7350d6494401c3aa6a1ac9288038754d4358a5102c7643a64b14a202ccc734c962944012eb03baa85288163b21d6250a510061e2a2e9304a200e1d5350e6094401c3aa6a1ac1288163e21d30582510166c39a60b04a200a7985081609440157308102c128802b660c205825102d7940840b04a200c5f7354f645440147b0b21ec8a88038754e43d91510145fc3a87b22a202c9e7350f645440193ae6a1ec8a88038754d43d91510051ec2c85b22a200c9d73d8f645440193ee731ec8a880327dcd63d91511bc5ec38c7b22a200c9d7318f645450d4790ca9ec8a8a4b0f9d953d91510068fb9aa7b22a200e1f6354f6454401c38c6a9ec8a88030fd4f73d91510064f29ee7b22a200c9d53dcf645440117b0f39ec8a88de8fa1673d91510051ec2ce7b22a200c9f739cf645440193f06b9ec8a88030fd4d73d91511a51f428e7b22a286a3d851cf645446947f06a9ec8a88d387e0d53d91510061fb9aa7b22a200e1f7354f645440183ee6a9ec8a88030f5cd53d91510070e39aa7b22a234a3e851cb645450d47b0a396c8a8a1aada0472d91511a55ac08e5b22a2008be87ccb645440117b0f996c8a88d28fa1732d91510051ec2e65b22a2008be870cb645440117b0e196c8a88d28fa1432d91510051ec2865b22a286ab6810cb645440156b02196c8a8802aea0032d91510055cc0065b22a2348be87cc7645440117b0f98ec8a88d28fa1731d91510051ec2e63b22a200c9f73cc7645440193ee698ec8a8a1a8f61770d91510045f43e61b22a2008bd87cc3645446947d0b986c8a88028f61730d91510045f43861b22a2008bd870c3645446947d0a186c8a88028f61430d91510055741061b22a200aad820c3645450d56d02186c8a8802ad60430d91510045f43841b22a2008bd87083645446947d0a106c8a88028f61420d91510054f41841b22a200a9d83083645450d56d02106c8a8802ad604
  | 11 => 0x800002401801000401000c00000000000000000400800000000000800c00801000400000000000000000001800001003c01001001800000800000000000000800c00400000000000400800000000000000000800000800803800400800000000000400000400c00000400800400001000c00000000800000400000000800400c00000000400000000800c00803400000800000400400000400000400400000c00000c00000400000000000000400000400400000400400000000c00400400c00400001400400000000000000400001400000000001800001001400000800800400000c00800000801000000800000000400400000000000000801000c00000c00000000000400400400000401000400002400400800800001400000400002800800001400400000c00000000800000c00000800000001802000401400000000000400000800000001000001000001000401400000000000c00c00400000c00800000000400000000000000800400000000000000000401400801000c00000400000000c00001000400000400000802400800400c00c00400000000000000000000c01000800800800000400000000000000000400000c00000000800000801c00001401400000400c00400000c00c00000000000000400c00800000401000002800000000401400400000001c00800000000800400000000000800000001400400000c00800000000400000400400000002000000000000400c00400400000400400000000400000000c00400401c00001000000000c00000800000400000800400000400000000c00000000000400800000000800800801800000c00401000400000800c01400000000000000c00001000400400400001400000400002000000000800c00000400c00400800000000000001c00800401400800000000000001000400000000400000000000000000000000000400000000000000000400001000000000001000000000001400001400000000400800000000000400800000001400401c3aa6a1ec4aa00327dcd43d85540070ea9a87b0aa800a7585cc76155001d2a8798ec2aa0029d61431d85540055ac2063b0aa800ae5820c761550015e30018ec2aa1fb1bd9572185540047bc3ac230aa87ea7785584615510d56f08b08c2aa0038754d43d81543f63bb2ce3302a8008fb87580605515d4f70ab00c0aa0038754d431815400c3ec2ee7b22a400c3e54dcf645480187ca8b9ec8a92861f61d53d91521f51f422a7b22a400c5f7354f645480517f0ea1ec8a90028fe1543d91524fe1ebaa87b22a400c9d7350f6454801c3aa6a1ec8a90038754d43d85520047bc3ac230aa400e1d5350f60548014f30a186c0a9002ba60830d815200578c0861b02a4008fb87580605495b4f70ab00c0a90030f15174181520062fa9ae6
  | 12 => 0x2b58828dc9bc8e525e2850a726ea368002d10000b800000000000000008e17f8000d00000000c680014c0dea080000002651048000000000000fe0001e48000000003090002640000000000000000002c79cd89e03f01b9b291990982210a8c915e8000000002a90000000540b183281c80000000000000000000000000000000000008d00000016c8000538000000000002a68628000e90c507a0001d90002d20000000000000002ae00009c8000000001448b681100000012a00004400022880016200027118784f80000000000028925180028400010d0c21400000001821500002b40988002828cb1ea15a00000015c9d02880d700000000000000024aa700002ad80000029b97f00000000023a00000000000012c280a5080000003d9ad10794b8000000000001068000e180006318c00001380000000000000007100000290b8000000002f485885e80020780020c00c2b626600019780000000000008b99bb0e2f08348000000001b0ad00000362818002140000002f500000000010d83400000000000030120b80e0000000000000003080000f42159e28000000002c88001fd98b8000001e825800019182d00021b83e8b993b0001a60000002d08002e080010c93d80012f9b52150000a11592e9a420230000000e600000000000026f0000000a1800000000267a00a332b39fd07a8002530000000000000000002f39340488400001750000002d2a919c702100028f99ea1309a1120000000000000002aaa520000000001e412680000000000000000000015b05a80011a92d08e800204a9e8410001f81f50000000000000000000000e8000101abea7f8000258001fa8001b58000bd00000000000000006c0e400020700000000000010a0000000002ac0a482780004caed9ca000000000020a2906800001300001b00000019380000026180007d80000000000023294e8000000038d60001fc8000000000001bb8001648000000ba8000000000001468000000c092ea0105180006180000000000020f9022cc8a50000000000000002a9a7d00000030480024f98a8000fe80028d0000000000002fa13f0000001589da00009326c8001ce8000d200000009507300000000008b000301ace80029d1ff80000007180000000000000023c00000000028b0000c4016a4a22e2510b30000000000000002162d530200027322f00030b0d6aa80000000000000d929d80000000004500000000000016c27a96580000006d8c78001a90000000000000000000d814185dac08a6801876a360000000000000000002b90000001af83b17aa5d0439779a01b70ac1408aeab4a460000000000001e3000000000293800000000000000c0000000000100040000040040040000100000040040000000000000100000080000040040000100000
  | 13 => 0x1b79e1152aff80000000000023a80000000000015180027500005b8f3150adf80000000012c8c18001a80000001d300000016716e9a98000d500000000004f21d9caac1000000000000000000000000000000000000000017ad5869089ac38000f200000004e00000000d8000000000000000c48002c40001579260000000002d6abf80000000003ca8a8c98cd10882c00026d2ba0192ef9482c6891982994a689080000001958e33089e0a1aa6b0089728000eb80000000000006084816b00000005c00000006f8000000000478002fd00900026fab180026700000000025000000000003582e1b380000029c21caea0000000001df8000001cd00000000000027800000000000022b2490000d400000000011d83a8f082987f00030093f81291094511b0ce83e0c29681ee1860be8d780006580000015580000000018880000000000000000000000000018e0ea03884704d80000000000004200010fa6300000017cae680000000028e0000000001ed8000000002af2f680000023718f245a3faf70000000431000000000000000002da09e93600000029282a0000ab0001dea90068a740051f48002e1072aa59800000000000000002d180002819fabb12e1762b88001570000001c50000002a4a102208000000001880c700000000030c80000000027880028b80011e8000000000000000000000000000001b400000000000012b1668000000001030000000000001aa000000000000000152000000000189a830000c10bd8000000000001e90000e980024c8000000000000000000000000000000510f9ac480029a9ab94d93c2092a50002ea8000eda2daf023b00009200000000000000000000000025380022200000007d0000000000000000001d711c0002068002120158000000ef80000025f8002259e980000000000012b8000000000000000380000000001542980000000002d90000000fc8000e38a595d85680000000000017c27b800000233800000000000000287a0e000000238254a8700000000000000008c8000000000b10000001619ec00000024e8000000000002968000002762b68000002ee80000015980000000000000021e00000000024800019280022ea6dab293591402b2faaf1a4b0f69a7879a9c9780000002271ce0000000000000000748000000001271320000e89819a48001c10001d58001328000000000000000000001700a80001678000000000140000dc0000000000000000000000248000000000000000000001dd000000000000121a9917b00000000000000000001980005800021b09f80000016880007f9d28000000001740001910b480011e0000000000000000001841a28000300002c900000010e8000000001a100e8000000de0d18000000b019c80000000013c80000000000026e000286800
  | 14 => 0x20c000013a8000d48000000ce15100007087c8002f28002801d0a849fb1370b400000000000017200023480022680020c88182c8000e00000000000000002940000002e30000000000e78000001fa00002680009910f11d0000000000002278001231632e000001f22c0001e600000000000004e95480000014c8000780000002d480014f96f80006d2648058ff08f8ad0c88002139a8abdac00000000bb1f880008009000004b80000001193800006a8000000000000000002ae8000002110000000000000000002cf0000408000000002440002bc0d11769cc9ee8000002200000b0ada8000000cb8621182aa00000026991100000000000000014900000000028623089f2410002028002b30000611db0002a280000000000000000011b8000000000000000c58078da1dc8001c08002fba1f148a3f2a08002c50000000000f01348000000000000458000000001d800000005f0001f10000f38000000000000000000000000000000000000000001158200000000229211b980219002b84a8002728000000000000000002ec09780000000014e0f120d8000f70000002038000000000000000000000000000000000600000000003038000000002a780003a19b0000002b086ea680001b200000baef2c5981303000acb1308000000000000d29552de0002a00001ec80024b87880022f8000001d50cf0000000000000270000000000001248000e70000000868000000000000000000378002a203130a2e91b100015b953214a2c90080000000009800c8000000000000000000002b20000000000f81d88000000000ef04a0000000002552c180000000000000000000023180017d00000000000018d10b0968001c7a8d85597993501a9f68000001852230000001f980000026280000000000000027080000000007004c0000500000000000000001442a70000000000000002fd93d00002f0000001b88000000000000000000ab9bd8000000000000002eb0000000000000000000000000000000000000000000000000000001d601c24781811f8001c40002488000000002bc80000012880000030d80000017a1ab00000000000f8000000001e000000007900000000028a0000000000000001790650d315f23d00000015e16a8001012658000000000f61608d380000000000006c8671d69ac80000f0000000000000000002998000000000000cc0000000000000b580000002a8000000000000002350000002099ff1db80000000011316500000000024e0000001a40000000000002e40000000ff8000000002dc8000000000002e58000000ca0000000000760a60498f28002051e59629e78002ed1330000000001612b827480000000023e0000000002fe01d8000001e728e800000086000000000053000000000000000000271ae60002128
  | 15 => 0x83c0000000000000000000000000000001b80a799a8000000fd0000a880029f9e20b88d0800000000171a5791289280000000030b8002dd8000000000000000000001d180011c9fe8848001479f0ac32e18000000000000fa8000ee17ea79830af115380023e8598000970002e200029303f8000002240000000000000000000000001aa8002eb89c0000fb8000001920002210fa0000002d980025c800000113a342ec80000003b8000000001f60001f18001040d8aee00007200007794a0003079a69432470000000002c700000002610c0000000000000000000000001d98000000001239c88000001dc1c28002f880000000000000000000000000016f00000029f2c28a9887a2606780000000000016a00000000000000017b8000000000000000ec8b385b0001398000000000000001ef0000000000000f500007b00000018a0001962ff09480000000000016ba0aa90a6b8000000000000000000000000000000fb0000000000000000699ba0000001748000000850000000000000000000000000002e48000001ea8000000000001ba8ee8000002060000000000000000001298170000160000000002fc0000000c80000000000000000000000d5aac800000202145a6000012f0000002a88000000000000001738000001e380000000025b84b14225612500000000013b8000000000000000000001188000809cf00000009d0000000001990000002280000000001ed00027c80000001e00000000000025f1208000002758000000000000001839eb80000029e0189a1a5693681000000000000000008224989394aa359bc13882f9730121f01bb1102a41ef8f580019a0001a20000000000000000001e50cc8000000001b30000000000000000000000000571f385500000000000000000000000000006680000000019c0002738000000be00013900016d00015625a0001c015c0000000000a400010e21e8000000000000000000002b100d0449b1a2b99980000000000000006e000169969266a810ca9970000000000000002b780000027e8002b9985afe8000000000000528000000000cf80006f1118000000002000aa88a0002be0000000002b51168000000000000000000000000b900017e0000fc26c25904d23b883adb0ed0000000000000000000001788000000000000000000000000000000000000000003040bf8000001de00000000000012a800087089000000000114a300000000002d88000002cf9b6acba170a200024693e8000002ad00028c0002fc8000c324da2d2018bb94105082eaba9bfa8580001e8000000648000000250002450000000000000000001fe28c80012d92586b9050000000000000af8560000e20ec26a00000000000000019d2438c3800021a5b163a378000e100000018096000000000000000029
  | 16 => 0x1f9930000000000000000150000ad8000000000000002c80000000000098000af13a0840000000000dd05a00008d80000000000009980000000007581f9178000002f400009b80018d9f280018ca4f000000023a5d82d80000027a0000001640418000000000000000000002769302599c20002e88000661f900030e95800000000005c8000e28b280024080000000000000000414f00000000011f17100a2ab0000001170f78740081228241c32089f409b2a10000000000002e50001a300018480000000000000017d80000000000000000000000000000024000022a0000000000000000000000960bc07722480000016600000024c1f70000000002cd2df30d0a39c90ba1291c48000000000000000000000000830000000000000000000001d121197080000000000030630680025c00000000010280000000005900000000025eaca9192f78fd80000000000000000000000000020f0c60000390000000000000000001ae1fc1c9842986a2a85e1b48002428462961ae8000001c830a80000000000000000002900000000000621080000000000000000000019e0000000002448000000000000000000000000000010000000f49cb00000b00030580000001a0000000000000000000000000000000000000000000000000000000000df0df80000000000007e25585d26a9eb00000000000000024d2949c180000000020580000000000000000000014600029b0cd8b72e28000002e70000000002178000000469151bf0000000000000002e80000000000941be0ac8bf0958000000000000000000000000000000000000000f18001c5abf1980068001952d81e6ad79ddad31d201d21d00023c800000000175ac20889b00000002fb0e089da608001060001a70001568002a30002588000338000000000320001be8000000640000000000000002dd20d1c3a399968000000000000ae00000000000023900000000021900000000019f0000000000002298002541498000000000000000002228002620f9000000000000000000000000000000000198a88a7200000000000000000000000000000000000029720a00015a8000002f918f8000000000000000a90000000000000000000000000000eb0000911c6b0c0000001f30000da9e89312a18002cd8522bb9220000001438d99af08127e0bcaf80002e78000070000001a0ae3a3121a00000000000020b0000001f200000006a0579bd00000023d80027d9ac0000000000000002040000000000000000b62168370000000000001cc0aa29a0000000000002031f5a9107b804800000000000252af32c99202b00000e688a8000000002f980005480021c0000000000000000000000000002d727780030280014b0001d380028993182880014280000000000000000000000000016d8002db
  | 17 => 0x1cf80000000008c1b9000000103a838000000000000b789aa23a18a97ad6000177190800000000137a7920e9870000000000000000000db88800000003d21800000000000016e2bd0db00025a800238a989160000002f627c04910586b0109240000001890739941338000000639e18e4800225000295b000000000000000000000000000000a32de947000000000000000000000090a41aaf8b51d78369df0350e58ea8000001f79fb8002f58002a38dd8000001da92800000019d8f88000a01b60002f200005f80000000000000000000000000030700018b00000013e0002b70000000000000000000002770000001d400000314d30980007c0000000a28000148001cb9d4a7b0000001092dc28f00015d0000001070000000318752612690000000332cc1a38001279c60000000858000000000000000002c62d380000000003980011a0000002822321ad95fad400007e800000243000263aa627f00018e9a50002ce2218001832ca0003052950000000001a580021988f0b225700000000000000000000000000a8002ab8000000000000000a08002
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x40181e7660c6454951006071d983191525440160d9319362549510050764c641c152544018957160c64981512ee071d583190605440141d93d5373596411d607a1d43cc7655040181e8754d435954100607a197350c655040181c865cd4319541006452057350c655040141f97d8d431954100507a5d5350d648855fc147154d435922159e45dd5831d1518855fc167154d439822100607a1d5350d6548563c157154d43d912100507a5d5350d644840156195081709452100568650205c251484015c19308170945210050764c74d955148401515931d36554521006251d9831d151485659177560c74545210056164c74dc951484f916697e1152545213a6491d38454951484e952697dd152545213e649a1c745495148401705931d15254521006491d08054951484e99247461542545212b459e6152dc15148563c157154d43181210050764e54dcd649400181f7660c7454650006071d9831d15194001a166160c74546500050764c7458951940f9836811d162546500054564c7498551940019247460a61546503e60de18745855194001515931d161546500054664c741c1519400183484dd9514865057f059c55350f6590001c155350d71d964000607a1d43cc76550001a49824c030d9540006072197350c655000141f97d8d431954000507a5d5350d648800141d931d365546203e60da0474d95518800b46697d955148620006892136554521880016159118d43d952013692219324c36548001615911cd43d95200048764e84dc7654800143694dc671d95200061960b719c7654800181e8750f31d952000692609300c3654800541c9754d4359520006076117318c654800141f97d8d43195200050765c6350c65480016159118d431952000507a5d5350d644800141c9754d43591200050764c74d9551480f9836811d365545200040fe61741d165c40f9434915d07459710006075d1831d165c416141d979cd4359710005856467350d65c415fc16215cd435971000692609300c165c40018c9736007358b10585836565350d62c40016859194d4358b1057f818c55350d62c412b6859490d3158b1000781d4d434c562c4001e055350d3158b100063261d300c162c4001a158350d6548710005896528259521c4001265989096548710004996602059521c40016259408165487100059164c2059521c400181d8754d43d96100050765d5350f648400141d931d1655461000607a1d5350d654400141e9754d435911000607e1784dcd624400141e9754d43589100050725d5350d624400181e8754d43589100060721d5350d62440014949750d31589100162521d434c562440054c8974c930589100163221d324c1624400141d931d365545103a58925165549214400905c985cd535901000507a5d5350d6404001c155350f7644010
  | 1 => 0x232b960003400234961600000a2044a80054520a800020038a18be3334800000027848a6131389400450d0000000000e00000480f8007d239e90800001d800312d00000890008400003513114970000c005c001000000002047e7b2b118c098282383a18358506a411e1bd24390fa4c902b2a0310a0a3b8091642141e01688360001a7013044c67e16250aa650820c00742186cea1e00174f800048006e2d000c00000000384482310706c000b800f2004b01464242200122640001cce8c001380c6147978104d00128b266001cc32721e96cda6e1d0bcd0203f8001e87248ec5c801483800182868042800080c201400000404043c0c240400040810180c1048300c08009c001814241400000c000c34a0100400004c01a158550f31d85540050764e545cf645496b41d9754d43d91520050764c545d0605496b41d9754d431815258e0761d5350c605080141d9395373592510050764c545d2609440109f985cc63d915100607617739cf645440181d85dcf31d915100507a5b535cc645452741e95219731915100507a5a855cc645440141e96615731915100507259855cc645440181e86615731915100545245855cc645440141e96d49731915100507a58515cc645440150d92145731915100525a58515cc6454569c1765145731915100561648515cc645440141e961417319151006076157398c645440181f855cd631915100625e057358c645440709d9361c631915149e07a157318c645440181e865cd5319151006072197354c645440181d855ce62191510062560573988645451581c7560c64d895116e251c5831936254
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2c00003400000043c03053800900070000122880c1446240100022820002414a1259855cc6454401282d1122c2ae6322a200d01d95921457319151005035413b306322a4a8802814a12197350c655040188343b263a2a4a8a4200a4168c74201525452100540b4530b063a2a3280030168164c745895194001482d18e8c14c2a8ca000c05e19931d1615465000502b46426eca8a43280030168164c74d9551880f98134b909b2aa290c4000a8168c84d95514862000482b474a6e338eca900030269460b719c7654800180b40b263a6caa8a4000a052857460c7459710
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x40102030004405b2284966157319151005102b0a1d931d15254521005005b3a5182dc671d9520005005b2a05931d36554520004805b22857460c7459710
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
  | 11 => 0x124c
  | 12 => 0x94b
  | 13 => 0x94c
  | 14 => 0x94d
  | 15 => 0x94e
  | 16 => 0x124b
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
  | 29 => 0xa0b
  | 30 => 0xa0c
  | 31 => 0xa0e
  | 32 => 0x130b
  | 33 => 0x130c
  | 34 => 0x130e
  | 35 => 0xa4b
  | 36 => 0xa4c
  | 37 => 0xa4d
  | 38 => 0x134b
  | 39 => 0x134c
  | 40 => 0x134d
  | 41 => 0xb0c
  | 42 => 0xb0d
  | 43 => 0xb0e
  | 44 => 0x140c
  | 45 => 0x140d
  | 46 => 0x140e
  | 47 => 0xb8b
  | 48 => 0xb8c
  | 49 => 0xb8e
  | 50 => 0x148b
  | 51 => 0x148c
  | 52 => 0x148e
  | 53 => 0xbcb
  | 54 => 0xbcc
  | 55 => 0xbcd
  | 56 => 0x14cb
  | 57 => 0x14cc
  | 58 => 0x14cd
  | 59 => 0xd0c
  | 60 => 0xd0e
  | 61 => 0xd4c
  | 62 => 0xd4d
  | 63 => 0x104b
  | 64 => 0x104c
  | 65 => 0x94054
  | 66 => 0x124954
  | 67 => 0x95254
  | 68 => 0xa0954
  | 69 => 0x94a14
  | 70 => 0x130954
  | 71 => 0x95314
  | 72 => 0xb0954
  | 73 => 0x94b14
  | 74 => 0x140954
  | 75 => 0x95414
  | 76 => 0x139254
  | 77 => 0xa1254
  | 78 => 0x124a14
  | 79 => 0x131254
  | 80 => 0x125314
  | 81 => 0xb1394
  | 82 => 0x138b14
  | 83 => 0x128994
  | 84 => 0x99294
  | 85 => 0x10b
  | 86 => 0x14b
  | 87 => 0x180b
  | 88 => 0x198b
  | 89 => 0xb1294
  | 90 => 0xb1295
  | 91 => 0x130a14
  | 92 => 0xa1314
  | 93 => 0x14d
  | 94 => 0xd0a14
  | 95 => 0xa0d14
  | 96 => 0x150d
  | 97 => 0x198d
  | 98 => 0x134a54
  | 99 => 0xa5354
  | 100 => 0xd4a54
  | 101 => 0xa4d54
  | 102 => 0x150e
  | 103 => 0x180e
  | 104 => 0xbd354
  | 105 => 0x134bd4
  | 106 => 0x184b
  | 107 => 0xbcb14
  | 108 => 0xb0bd4
  | 109 => 0x14cb14
  | 110 => 0xb14d4
  | 111 => 0x14cb15
  | 112 => 0x2cb
  | 113 => 0xd0b14
  | 114 => 0xb0d14
  | 115 => 0xd4b14
  | 116 => 0xd4b15
  | 117 => 0xb0d54
  | 118 => 0x19cb
  | 119 => 0xbd414
  | 120 => 0x140bd4
  | 121 => 0x20e
  | 122 => 0x154d
  | 123 => 0x2cd
  | 124 => 0x74a
  | 125 => 0x19cd
  | 126 => 0x194a
  | 127 => 0xd4bd4
  | 128 => 0xbcd54
  | 129 => 0x154e
  | 130 => 0x104bd4
  | 131 => 0xbd054
  | 132 => 0x28e
  | 133 => 0x184e
  | 134 => 0x1a8a
  | 135 => 0x8d
  | 136 => 0x1a8b
  | 137 => 0x194b
  | 138 => 0x1a0d
  | 139 => 0x164d
  | 140 => 0x8e
  | 141 => 0x188e
  | 142 => 0x160e
  | 143 => 0x10e
  | 144 => 0xe8e
  | 145 => 0x18ce
  | 146 => 0xecd
  | 147 => 0x1a4d
  | 148 => 0x18ca
  | 149 => 0xe8a
  | 150 => 0x1a4a
  | 151 => 0xeca
  | 152 => 0x14953
  | 153 => 0x140d3
  | 154 => 0xe9353
  | 155 => 0x18d353
  | 156 => 0x15693
  | 157 => 0xb1355
  | 158 => 0x141355
  | 159 => 0xe8b
  | 160 => 0x18cb
  | 161 => 0xecb
  | 162 => 0x1a4b
  | 163 => 0xd4bcb1c
  | 164 => 0xd4b0bdc
  | 165 => 0xbcb0d5c
  | 166 => 0x2c955
  | 167 => 0x2cb15
  | 168 => 0x2d6d5
  | 169 => 0x28956
  | 170 => 0x28b16
  | 171 => 0x296d6
  | 172 => 0x1a9953
  | 173 => 0x15353
  | 174 => 0x15355
  | 175 => 0xece92
  | 176 => 0xe8ed2
  | 177 => 0xece93
  | 178 => 0xb14d5
  | 179 => 0x1414d5
  | 180 => 0x2d4d5
  | 181 => 0xe8ed3
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1774
  | 6 => 3801
  | 5 => 1566
  | 4 => 153
  | 3 => 19
  | 2 => 5
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 101)*7) 7
  | 7 => packedAt gbK7 (72730+((h/591+packedAt gbK7 (65638+(h % 591)*12) 12) % 2575)*12) 12
  | 6 => packedAt gbK6 (200186+((h/1267+packedAt gbK6 (182448+(h % 1267)*14) 14) % 8885)*13) 13
  | 5 => packedAt gbK5 (98658+((h/522+packedAt gbK5 (92394+(h % 522)*12) 12) % 3660)*12) 12
  | 4 => packedAt gbK4 (11118+((h/51+packedAt gbK4 (10710+(h % 51)*8) 8) % 202)*9) 9
  | 3 => packedAt gbK3 (1575+((h/6+packedAt gbK3 (1539+(h % 6)*6) 6) % 34)*6) 6
  | 2 => packedAt gbK2 (463+((h/1+packedAt gbK2 (460+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fffc70e1fe1f8061c0e07fffc81c1fe33c13f
  | 1 => 0x87c3f80fe1fe3fffe00ff81e0146264e4cf9cc
  | 2 => 0x7fc3ff001ffc007fff0001ffe7838718f0e0f
  | 3 => 0xf8003ffffe000007ffffffe003803f81f00ff0
  | 4 => 0x3ffffffffff80000000003ffc001fff000
  | 5 => 0xffffc000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x944410602a04852040212c2a800c09611c115
  | 1 => 0x82e28802207212372024b0541842224a04594c
  | 2 => 0x4aa1a10015480a549602019505828608e0a0a
  | 3 => 0x500024a95400010092894500038015016004a0
  | 4 => 0x400037cd998925c000c0418063ad4001fba000
  | 5 => 0x67330081101006010301861183f7bffc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefea8feecfea0fefefea8feecfea0fefefea8feecfea0fefefea8feecfea0fefefea8feecfea0fefefea8feecfea0fefefea8feecfea0fefefea8feecfea0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36364
namespace PEqualNP.Outside.L_meta_36364
open PEqualNP.Outside.L_meta_36364.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 11 := block_range (n:=11) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 11 := bs1_3_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
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
theorem bs2_4_96 : Interval s2Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 99 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96))
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
theorem bs3_2_0 : Interval s3Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 5 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
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
theorem bs3_4_384 : Interval s3Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 414 := (concat (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat bs3_4_96 (concat bs3_4_128 bs3_4_160))) (concat (concat bs3_4_192 (concat bs3_4_224 bs3_4_256)) (concat (concat bs3_4_288 bs3_4_320) (concat bs3_4_352 bs3_4_384))))
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
theorem bs3_5_608 : Interval s3Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 616 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 bs3_5_512) (concat bs3_5_544 (concat bs3_5_576 bs3_5_608)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := (concat bs3_6_0 bs3_6_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 5 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 19 := bgb_3_0
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
theorem bgb_4_128 : Interval gbAtlas 4 128 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 153 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128)))
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
theorem bgb_5_1536 : Interval gbAtlas 5 1536 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1566 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536))))))
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
theorem bgb_6_3776 : Interval gbAtlas 6 3776 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3801 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)) (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)))) (concat (concat (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 bgb_6_1600))) (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856)))))) (concat (concat (concat (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 bgb_6_2080))) (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 bgb_6_2208)) (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336)))) (concat (concat (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)) (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560))) (concat (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 bgb_6_2688)) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816))))) (concat (concat (concat (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)) (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 bgb_6_3040))) (concat (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168)) (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 bgb_6_3296)))) (concat (concat (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520))) (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648)) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 bgb_6_3776)))))))
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
theorem bgb_7_1760 : Interval gbAtlas 7 1760 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1774 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)) (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 bgb_7_416)))) (concat (concat (concat bgb_7_448 (concat bgb_7_480 bgb_7_512)) (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640))) (concat (concat bgb_7_672 (concat bgb_7_704 bgb_7_736)) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864))))) (concat (concat (concat (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312)))) (concat (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536))) (concat (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632)) (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefea8feecfea0fefefea8feecfea0fefefea8feecfea0fefefea8feecfea0fefefea8feecfea0fefefea8feecfea0fefefea8feecfea0fefefea8feecfea0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124200 * 2 ^ 32 + 4276944544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36364.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.and,[4,5]⟩,⟨.and,[1,5]⟩,⟨.or,[2,8]⟩,⟨.or,[3,7]⟩,⟨.or,[9,10]⟩,⟨.and,[6,10]⟩,⟨.and,[0,11]⟩,⟨.and,[1,4]⟩,⟨.or,[12,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4276944544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4276944544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36364

open PEqualNP.Outside.L_meta_36364 in
theorem PEqualNP.Outside.L_meta_36364 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4276944544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4276944544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
