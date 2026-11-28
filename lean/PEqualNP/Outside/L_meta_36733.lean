import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36733.Model
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


end PEqualNP.Outside.L_meta_36733.Model

namespace PEqualNP.Outside.L_meta_36733
open PEqualNP.Outside.L_meta_36733.Model
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

def SBf (j : Nat) : Nat := [6, 2, 7, 7, 7, 8].getD j 0

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

def mirrorSteps : List Move := [swapRows 67]

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

end PEqualNP.Outside.L_meta_36733

namespace PEqualNP.Outside.L_meta_36733
open PEqualNP.Outside.L_meta_36733.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x284c1a40128080018076a1601806bf43bd43bf42bd42be41bc41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x180028810020025aa5a1c754f428ea98832d52107a060087808010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
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
  | 4 => packedAt s0K4 (244+((h/4+packedAt s0K4 (224+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s0K3 (170+((h/2+packedAt s0K3 (162+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfe03fffffffe01fffff80fffffff01fff1fe3f
  | 3 => 0xfffc03fc03fffe01fffff01fc07ffe07fe63c7
  | 4 => 0xfffffc0003fffffe01ffffe0007ffff81f83f8
  | 5 => 0xfffffffffc00000001ffffffff8000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x9604848428a224242450b162d48b628a26acdb
  | 2 => 0x2ba1292a51451d4948ac0ab56955115551562d
  | 3 => 0x4caba2329a69491d913d58198c66b4479a6346
  | 4 => 0x713233a3639191911dce6cd03078d9e11d83b0
  | 5 => 0x81c3c3c383e1e1e1e1f78f1e3e40e1861ff800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36733
namespace PEqualNP.Outside.L_meta_36733
open PEqualNP.Outside.L_meta_36733.Model
def s1K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s1K1 (i*3) 3
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt s1K1 (4+((h/1+packedAt s1K1 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffde73
  | 5 => 0x6f9c
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff8205
  | 2 => 0x2552
  | 5 => 0x1958
  | _ => 0
def s1Atlas : Atlas := ⟨1,rawDecor 37 s1Pos s1Neg, 0xaaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36733
namespace PEqualNP.Outside.L_meta_36733
open PEqualNP.Outside.L_meta_36733.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xa9314008ce042e6860000000244a340000a8569f00591002a9d61252000131c3c398167418000000a01000006120001b04a089920acf00140004080140018008180050210485ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21ee21fd21fc21ec21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x530020005534251719274244085626050064001166740060323816652f180069580f45735a6747335f46636b6e24713f3730003c004900132b70486a0e0b3e6c625b5c00065e514f003a1a2e4b4a222c0d005d21312a4e030029001f0057002d6d5207001d3d10001e004c431b350c54120104233959020000723b406f0009616800362814501c41004d150a000382010003800282800000000280809c800286000180801103800c8e030006808b85020a8285805b94b43b6a96877651d0eeaa3a1d794f42aea9e857651d0aeaa3a15dd4532ba28a65cd320cabca7a0d754f41b7296836d52d06bea6a0d714d41b7a92836c52506f6a0a0de14141b7296636d52cc6bca318dbd4931b6292633e540c67aa818e795031ceaa0635e510c7aca218f590431eaa08635e53c86baa790f50c721b728c43ce31887986310d7d4d21ae29a433e540867aa810f50c421d72a043ad54086dca210f994421f320843e541087ce6210f38c421e618843e431087886210e78c640ce18c81ae219035843204f94240af298815d53102dca4205b54840bb2888175511033ca6206754c40d729081ad521036ca2206d54440cf188819c311035c42206b084409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520af298415d530827ca9884f55310dc206215e53842baa7085b94a10b6a9421d431843c843084fd51109e2a2215f53442b8a6885bd4910b629221d431043c842086e10010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x6a0a10291e6a680040802ca9488058001c612300b8e2010000062b1185320cac46250431b4181410c715540c421b118d41086e06050421b198631086a5640c421e19903108785640c421e19503108785540c421e10c421903155354440c9549511021d650c4408b5942110384310844099185520c2546154c20d194831843465308610e40c440043a02110010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x10c20a0aeb3206210c85769503108682ba86210881815943108440
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 4 => packedAt s2K4 (3471+((h/39+packedAt s2K4 (3159+(h % 39)*8) 8) % 141)*8) 8
  | 3 => packedAt s2K3 (952+((h/8+packedAt s2K3 (912+(h % 8)*5) 5) % 29)*6) 6
  | 2 => packedAt s2K2 (199+((h/1+packedAt s2K2 (196+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 1 => 0x7f01fc07ffffffff83e07c0f80ffffffc933ff
  | 3 => 0x7ffe0007ffe07ffffc007ff000fff83ff1c3c7
  | 4 => 0x80000007ffff81ffffff800000ffffc1fe03f8
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x914284011c104200c628c508e2c425212561b
  | 1 => 0x224c518b224a28c581a8350d12558ca4c930ed
  | 3 => 0x4c289ad54487516ab4125b64249ad23971c346
  | 4 => 0x68b1636689141db35adb024848e36711be03b0
  | 5 => 0x70c183870e1861dc631c638e70038421eda800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36733
namespace PEqualNP.Outside.L_meta_36733
open PEqualNP.Outside.L_meta_36733.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x234c3c00000149842e013995678d080e0d2103a24a00006002150446815200000007c300404800000945953601500388860a04007002c00010008020c140542203ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x54b200820a0000004846a0009a1c0000780036283e889c2672009600007a8c0060700056244ea60c2c3200646886003c5076aeb052aa0802a20442a800000038907e0000941e001006408400744a00006c626a188a0030a4669e440000164c3a2a9298348e580eac2e005e80226e7c1a0000145c12205a0008280140018b026050202001003c84381005838102842820206baa921d794643bba8a87745150f3ea8a1f5d4543ae28a87d45150ea8a2a1d794c43af29e855d53d0b3a87a15d94742baa8e859d4350abca6215754c42bba8a6574514ca7ca8194f55032af29e835d53d073a87a0db94b41b6a96835f53506b8a6a0e750d41af298835d53106bea918d755231af28c633e540c67aa818d7d5031cf2a0635d540c73aa818c755031af28863d6510c7ae8218f5104319f2a6433d54c86bca790d754f21ea18e435f53486b8a690f50c421af29e815d53d033a87205794c40aea98819d43102dca4205b54840bb2888175511027ca9984f55330bb28c6175518c27ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb288417551083a863885794e10aea9c213f5444278a88857d4d10ae29a216f52442d8a488750c510
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x98010058078668092a2944ac308080ba062201c390c00a0c309418582946150f42c550d51d0a946150d42951855310a946150f41c350d52d061d6595031c5185540c71554d0431b198b410c6556510431a559031c8716540c721875905348695640c4219518553d02946150e40a5185431030d4354840c550d5110295640c710875925384295640c510c51503144344520c510
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x290098020c28238a86a96838155262d043182aed2a06390d047150d521020abb0a818a2181590520c510
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
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2640+((h/30+packedAt s3K4 (2430+(h % 30)*7) 7) % 119)*8) 8
  | 3 => packedAt s3K3 (990+((h/8+packedAt s3K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s3K2 (302+((h/2+packedAt s3K2 (294+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe03f07ff81ffc3fc3e0ff8781ff87f034ece7c
  | 2 => 0xffc007fffe0fffffc00fff801fff87ff8f0f8f
  | 4 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x428400230400800046110088c50089281050b5
  | 1 => 0xc98a4a451ca5052c1a8748514b48521946c65c
  | 2 => 0x5129488286a2255810a9502129504d28b0b0a
  | 4 => 0x962ce7125143ab9aeda0c4449ce66063f00de0
  | 5 => 0x1830c61c618c33e331cce66700c44083eda000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36733
namespace PEqualNP.Outside.L_meta_36733
open PEqualNP.Outside.L_meta_36733.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x8000000000018b002474d8000005a24aac01c0030002003930a008c000082138f26a001500695052064198481ca203ca5089007cb911a3120c0004040000240000ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xb2603801c05a78019001387a2081180020009909e0e19a39880000e801b95000000000000000000142b251712018000049800209c861680210005002b9d002403291e800000071a248017a1ac02800000042a00001f00000f800ba28a1da6911b1a88a580000013200f00001000000caa800d808009002716128d0c158014ac8680000001001fa88aa300000029a800c00140400040c0000000004080c0c040400041400040410040004001412baa921d794643bba8a87745150f3ea8a1f5d4543ae28a87d45150ea8a2a1d794c43af29e855d53d0b3a87a15d94742baa8e859d4350abca6215754c42bba8a6574514ca7ca8194f55032af29e835d53d073a87a0db94b41b6a96835f53506b8a6a0e750d41af298835d53106bea918d755231af28c633e540c67aa818d7d5031cf2a0635d540c73aa818c755031af28863d6510c7ae8218f5104319f2a6433d54c86bca790d754f21ea18e435f53486b8a690f50c421af29e815d53d033a87205794c40aea98819d43102dca4205b54840bb2888175511027ca9984f55330bb28c6175518c27ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb288417551083a863885794e10aea9c213f5444278a88857d4d10ae29a216f52442d8a488750c510
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x2e02001e01421239609ca1a106a8a30003098002402c89801000000000204306946150f42c550d51d0a946150d42951855310a946150f41c350d52d061d6595031c5185540c71554d0431b198b410c6556510431a559031c8716540c721875905348695640c4219518553d02946150e40a5185431030d4354840c550d5110295640c710875925384295640c510c51503144344520c510
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x900298020028238a86a96838155262d043182aed2a06390d047150d521020abb0a818a2181590520c510
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 5 => packedAt s4K5 (788+((h/14+packedAt s4K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s4K4 (2670+((h/30+packedAt s4K4 (2430+(h % 30)*8) 8) % 143)*8) 8
  | 3 => packedAt s4K3 (998+((h/8+packedAt s4K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s4K2 (302+((h/2+packedAt s4K2 (294+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe03f07ff81ffc3fc3e0ff8781ff87f034ece7c
  | 2 => 0xffc007fffe0fffffc00fff801fff87ff8f0f8f
  | 3 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x428400230400800046110088c50089281050b5
  | 1 => 0xc98a4a451ca5052c1a8748514b48521946c65c
  | 2 => 0x5129488286a2255810a9502129504d28b0b0a
  | 3 => 0x962ce7125143ab9aeda0c4449ce66063f00de0
  | 5 => 0x1830c61c618c33e331cce66700c44083eda000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeae8a0e8a0eaeaeaeae8a0e8a0eaeaeaeae8a0e8a0eaeaeaeae8a0e8a0eaeaeaeae8a0e8a0eaeaeaeae8a0e8a0eaeaeaeae8a0e8a0eaeaeaeae8a0e8a0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36733
namespace PEqualNP.Outside.L_meta_36733
open PEqualNP.Outside.L_meta_36733.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x40000006346c009540081e260c7941434ea34e98b801c812802200395328890100900211800e16160800010a02805660f80520800c120010928e151001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc81bc41903bc6320770c640bf28481bf40903f681205fd4d40be29a81bf435037a86a05fd4940be29281bf425037a84a05fd4540be28a81be415037882a0778c540ee18a81fb405037c80a05f95040bf29881de53102bca6205f54c40eea98815d53102fca4205f54840bf288817d511037c82206f10440ef18881dc31102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a9987790f30eea1e617e52cc2faa59877ccb30ee996617e51cc2faa3986f90730de20e61de31cc3b863985fd5230bf2a4617d548c2f8a9185f54e30bf294617d528c2fca3185f54630df20c61bc418c3bc6318770c630bf28461df308c3f661185fd5130bf2a2617d544c2f8a8987790d30eea1a617f524c2f8a49877cc930ee992617f514c2f8a2986f90530de20a61de314c3b862987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c2fca4185f54830bf288617d510c37c82186f10430ef18861dc310c2fca01877cc030fd18061dd300c3f260185fd5320bf2a6417d54c82f8a9905fd4f20bf29e417d53c82f8a7905f94720bea8e41be41c83788390778c720ee18e417f54882fca9105f55220be2a4417f53882fca7105f54e20be29c417d52882fca3105f54620df20c41bc41883bc6310770c620f710c41ec21882fca1107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a417f51482f8a2906f90520de20a41de31483b862907ec8120f7102417f54082fca8106f950209f2a0417d540837aa8104f55020be2a0417f53082fca6107794c20af298417d53083baa6105754c20be298417e52082fca2107d94420bb288417d51083eaa2105d54420df20841bc41083bc6210770c420f710841ec21082fca0107bc8020fd10041ed20083f240107a48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10df20e21bc41c43bc6388770c710fb10e21f521c43f641887e08310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10bfa94217e52842faa5085f14a10bea8c21be41843788308778c610ee18c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910df20a21bc41443bc6288770c510fb10a21f521443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821be41043788208778c410ee188217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xc529077e6520ef8ca41de99483bc329067ca320efd4241df28483bd5090778a120dfd4d41efa9a835f53506f8a6a0f714d41ae29a837f52506f8a4a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077e8620ef90c41dea1883bc43106fca420df54841dfa1083be421077a8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020efd4c41df29883bd5310778a620efd4841df29083bd5210778a420efcc841df19083bd32107786420ef944419f28883b6511077ea020ef94041dea8083bc50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc6fca598df54b31fba0e63be41cc7788398fd10731da20e637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31efa1c63de438c7ba8718f710e31bf294637d528c7be6518f78ca31ee99463dc328c6fca318ef90631de20c63df318c7ee6318df94231bea8463df548c7bca918f755231ee2a463df528c7bca518f754a31ee29463df428c7bc8518f750a31ee214635e518c7be8318f790631cf20c63dd418c7b88318e710631efa8463de508c7baa118f714231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131bfa92637c524c77c8298ef10531fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863df430c7bc8618f750c31ee218637e520c6faa418f7cc831ef19063dd320c7b86418df94431fba0863be410c7788218fd10431da20863df310c7ec6218f74c431fa988637e500c6faa018f7d5031ef2a063dd540c7b8a818f7d4831ef29063dd520c7b8a418f7d0831ef21063dd420c7b88418f794431af28863d6510c7be8218f5d0431ef208639e410c7ba8218f710431ce20863d4410c7288218f7d4031ef28063dd500c7b8a018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790ef90721de20e43de31c87b86390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52886fca310ef90621de20c43de31887b86310fbc8621fb90c437e50886faa110dfd5121dfaa2433f54486fca890df55121be2a243bc5448678a890dfd4d21efa9a435f53486fca690df54d21be29a43dc53486b8a690ef90521de20a43de31487b86290fdc8521f710a437f50487f6a090ded4121be28243f850486f0a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821bf28843be41087788210f78c421ee18843ef21087ec4210fb48421fa908437e50086faa010df94f40bea9e81bf43d037a87a05f94b40bea9681bf42d037a85a05f94740bea8e81be41d037883a0778c740ee18e817d54902fca7205f54e40bf294817d52902fca3205f54640df20
  | 2 => 0x704c700002cc20d30004f07fc3d088072b08000005960015f80027c0c17389c4227d11526e17a4d14f114378c24f10f51ec9e83603a58cb38511db322aac972911e23ec392ba1507580004c0f0568ea92b12a000b300580000200400000002000000000800000481a00a01c0000601e0000601b00c0080480900c000000190020080080206a0000180d00401c000160220200180000001002801002000000010200000000602401407819004034008140020040100000600c0000303c00000801012004000010040040800400000800000004000040060100200080000a000210320160000100600404c0100000000003006000000020120000cc0000b000004000010160200000400a000000020000000000101c0440e00000801006006000010018000060080280b00400800002064008010080100080600000e0040080100e0080681303801c01802000034008010040280000001800c0000100c000020020020040300000201c0000b0240040c017002000010000040200400500e004070070060000080000a020008130020040100a054010028110020280100400c0040800000c0200200100001c0800c012014010000000000000304b7e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150feea2a1ddd4543be28a87f45150ee8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621e750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbbc87997750f32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132ef21a65dd434cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cafca2195f54432bf280657d500cafca7a0f794f41af29e837d53d07baa7a0d754f41bf296837d52d06fca1a0df54341beaa4837e53906faa720efd0e41df21c83bd43907788720df94a41bea9483bf429077c8520ef50a41de214837e519077e8320fdd0641bf284837d509077ea720ef94e41dea9c83bc539077ea520ef94a41dea9483b
  | 3 => 0x318c2a8ef2481720006992f0000002da1503cb98bf98c3a89bc451530007f0002e000099d7a1f54f66610412743426c1a0a6292935599b029e9750f1392d038d7d8df11627c5aaf5000001142801781bcf90c400025c3528d3fa6513b85523e98c0000037ec1cf79ad1982c88c980108ae4a584735e564a90174a2901490c00087e4220492ca9f8a60002c40011e80036a000bc0654a8504001610007c483a3023a0014b18819483000186000818820003701048422701e000b480a000135228000000000000046c91c868eb0000000023a58e8505f00032e87c1d9b336e67ce1a7d0be0015a000152b2400272000000e880007823d501014725ec780002aa00000000032001799fa000014f1ad70000000009220ca0c000000004cc000004701014516d02a0003b2d3000004118b85987ec668cb00094c000d10c48b8ee12950c0000fa165646580012554c940ec1c6000a30d62e90002ec16800000bb56a0a0000000001030000000013a00015c7b9bb34059c00203000af4bb8006028cc13a9c18a3b8120371c4284212bc448a903800c0002b8f20582904b0b813c60c000d920d0e22e80012d0000016a80027a51151800600000000590005d40026c45a00000290000624000d7390000920dd46e4c80005d0000000011e3146911599d284001720000000b8002050d20000009a4e8a08242ad3d2a896e8ab000000000000009a487aae3c095c000b640e8a4001f3242089098e16062bc8725f17e89800000488aa8198900000000017c000b0d600b0050b340000058aad40000000092c0000027e01cef8003dc0bcf090026049800000000020c3800214000298f31fa41474075492b58cd9ab41e5f467825168230858000001792a8001d28d0001cc00031c4f000000000002be5d0984002170001b8ec9d05e28245695e2fc3e14d01b1c0000001475ca9d8e9a701229a0002f928a6557f8003ecb6c6f0ed0520d50e81253ea39508933741a05296b1847280e138246000a515824090803173000884e92da59e0c80a0671b02502521937c07400137000001081fe04009970a3f1ca6788d1281f24c43224a00069d1a9a32ac2015802b4b80003a1dd5e4610cd0980000011e1ec0547103c8963d030d0c14d3aeaa0000001a0199498fe5a0000d525a4020006d0363cea14892a72e8ad8d73054e68f8898d93625191895d00058d3300031abbd4a000498bf4f811b6040004e85100004cce2b80004707786d5d40001098f39c0014aaeb44a000ada7908c001271a90c02b0cc8890a46d1059f807a4256f1c90167b4001920005407622213200025aac4e2000bd08d3445e4f3000166bc0692230fabd8418005320002b2970fe2385ba8b482000080003b455d351a559000000000000000000000006f40027500086d57800000918f52e22c0550162d8
  | 4 => 0x14e0007ac0026b000001688000b43048a9810000000000000000000000000458000004dac10308a45d85a89100036ca213f8d50f8880b2172000b70c58d65be00117a2c438a10e3abb4c40006d9820620e000081380a3d7f1cd000000670005f08c87e086614be9322600a081160a985947942195c0221381f087000000e280007e43058a583844452f1900000000000001c9940020200073caf96e50e17000185342461051404240014d9b95c6001620450000691d84f000000738094b25d83b8000003e86e13b4f8b48002b7104000750004a4001219f7000408001710d618cc98855b2a94640a70001ed279350305452d8e40040010016f00045c732fc4ac72c648000a8350002a900000000136286a24c180d2d828c7f8f40001cc000f25624403f28153abdc001a85dc838950
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x7530827561d4c2097596530831e5494c20c7552530825e6194c20c7951530831d5454c2097185530823e6414c208f590530825e6314c209d98453082756114c20cd95251083355494420d594e51083555394420cdd9251083346494420d5d8e510835463944208fd91510823c645442097d8d510825c6354420cd95151083355454420d594d51083555354420cdd9151083346454420d5d8d51083546354420dc181510823f65904208f596410831e5390420c754e41083365190420cd546410823f65104208f594410831e5310420c754c41083365110420cd544410825f658c42097596310831e548c420c75523108356518c420d5546310825f650c42097594310831e540c420c75503108356510c420d55443108394410c420d954621082e96008420ba58a200826f65480209ed9520082eb6548020dad9520083aa5448020ea55120083ca5348020f254d20082e86148020f894520083e15148020ea90520083a84148020f28c520083c831480209798e54c425d63953108f99253c423d6494f108f99252c423d6494b109798e52c425d6394b10e510431c42f06048710dad4820c42f16108310f888420c425e63d52109758f548425e63152109758c548423e64d4e108f593538431e5494e10c7552538431e5454e10c7551538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6414a108f590528425e6314a109758c528431e5390610c754e418431e5310610c754c418431e548c610c7552318431e540c610c75503184394410c6108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f984544423c6115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d1097984534425c6114d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427b60549109b994524432f5414910cb150524434f5314910d314c524436561149108f996414431f5390510c714e414432f5290510cb14a414423e6510510c7d4c414431c5310510cbd48414432c521051097996314431f548c510c7152314434f528c510d314a314425e650c510c7d50314431c540c510d3d48314434c520c510e5104314436452885109d195214436852c41109798c540425d63150109b988540426d62150108f990530423d6414c109b988530426d6214c108f990520423d64148109798c520425d63148109d9845204394410c4108f992500423d64940109798e500425d63940109e594200436952080109e596100427765440109ed9510042e86244010
  | 1 => 0x867b60551219e181544863e6515121c7d53534871c54d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534867b6054d219e181534865e6514d21c7d50534871c5414d218f996414871f5390521c714e414863e6510521c7d4c414871c531052197996314871f548c521c7152314865e650c521c7d50314871c540c521e5104314873b54d4121ce153504875b53d4121d614f504873a41d4121ce107504875a31d4121d60c7504873b5414121ce150504875b5314121d614c504873a4114121ce104504875a3114121d60c4504876a21141219798c540865d63150219e980540867960150218f990530863d6414c219e98053086796014c218f992520863d64948219798e520865d6394821e5104310866f6548421ba18121086776548421ad18543d025f63547409718d51d03365110740e510431d025f63546409718d51903365190640d59443190355510c640e5104319031c5350d40ad185435025e63149409758c525032c5250940ae181425025e63d45409758f51503345190540ae9824150357510c540d51443150394410c54097986531025c6154c4097d8d511025c6354440c794e411031d5390440c794c411031d5310440cd94441102b9601044097d96311025d658c44097d94311025d650c440e5104311031d53d00408fd95401031d53500409ed95401026e62153309b58854cc31c5450f30b518543cc23f64547308f19151cc356510c730e510431cc27661d52309d587548c23f64546308f191518c3365110630cd544418c356518c630e5104318c26f62551309b189544c27761551309d185544c25c6550d30c7151434c2d46150d308f990524c23d6414930d3149324c2d8604c9308f993514c23d64d4530cdd44414c3345110530d5146314c2da608c530e5104314c23d65950308f986540c23c61550308f990540c25e63150308fd91510c23c64544308fd96410c23d65904308fd94410c23d6510430c7952310c31d548c430c7950310c31d540c430d5944310c394410c430b6580310c31d54cc03097d95300c31d544c0309ed95300c25e63153209758c54c823e6414f208f59053c823f64547208f19151c825f63547209718d51c8394410c7209798c548825d63152208f990538823d6414e208fd91518823c645462097d8d518825c6354620e5104318825f63551209718d544827761551209d185544825e63151209758c544823f6454d208f19153482776154d209d185534823e6414d208f590534823e64d45208f593514825e63d45209758f51483375110520cd1444148357510c520d51443148394410c5209798f540825d63d50209d987540827561d50208f596540823e61950208f185540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d98
  | 2 => 0x6550441b518d41106b661d4c41c754c53106ae6214c41ab58853106b66114c41ae98053106b96014c41ad987521069e6314841a758c521072d5214841ad98452106ba6014841ae58052106b6618c841ad58632106b7614c841ad185321063e650c8418f59432107366194441ad98e511069e6314041a758c50106ae6214041ab58850107395014041cdd8554cc7355410731ad59441cc7356510731c7951438c71f5410e318f992528c63d6494a31d3949328c69e640ca31a7590328c69e64cc631a7593318c63e64942318f592508c6d661d5231c7d52548c6d66115231b5987528c69e6494a31a7592528c74f5294a31b5984528c65e6510a3197594428c7966110631a7992508c69d6494231d6d42508c63e64951319758e544c65f63551319dd85544c63e65151318f996414c63e6510531cd153314c71f548c531c7152314c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65d6590c31b5586430c71c5450c31b5d85430c65d6510c31c7550430c69e640c831a7590320c74d520c831b558f410c6b661904319d594410c7974310431e590c410c7954310431e510c410c7366510431cd594410c7966310431e558c410c7365310431e5cc8410c7963210431e54c8410c7943210431a7993310c69d64cc431e5107310c65f654c431a7d91310c69c644c431e5105310c677654c431ad191310c6d661d5031c7550540c6ce6215031b3588540c6d66115031b6980540c6d96015031b5987520c69e6414831a7590520c74d5214831b5984520c6da6014831b6580520c6d66190831b5586420c6d76150831b5185420c65e651083197594420c7566194431b5992510c65d65d0431b5597410c75565d0431b5986410c69e6190431a5986410c71e5190431e5946410c65f6550431e5504410c69e6110431e5984410c71e5110431e5944410c6d76510431b5594410c6d66410431e5990410c7965410431e5550410c7974210431e5908410c7954210431e5108410c7976510431e5994410c7956510431e5194410c7976210431e5988410c7956210431e5188410c7975210431e5948410c7955210431e5148410c7976010431e5980410c7956010431e5180410c79441d4031e5106500c7944154031a7990500c69d6414031b3988500c6cd6214031e5104500c75950140319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f218f99053c863d6414f21c794e41c871d5390721c794c41c871d5310721c795231c871d548c721c795031c871d540c721e510431c865e63952219758e548863e6494e218f5925388794410c6218f992508863d64942219798e508865d63942218f992544865e63951219758e544867a60951219e582544865f63551219718d544
  | 3 => 0xabc9a8f71ae8b03b8000e4b0800049000000002ef21a001500622ee0000021d1a20000303011e8e00206b38e898002e900000000000000140000004b44cc4f800362a042594503e234f39074649b05b03d2ce6694b94a0008ccce17a2763613498156c000da11a0000012980000061d5d80829865400000174000d680000080d672d62628ec000002dc820eb8940006b01b800440430131e42165908ba9235c0d47f0902786d87b2aa57419cec1f50fc9e893a720009708f0f90000004220621e6493289735e710a080603c0b0040d01c1e000010240202c02014010040000001000010000c02c00004030100600814000000000100808018060000d0000701c040040b00412004000000f000020000202019008000000a00c0300c0602800024000280100813004050080804c04000030000c01806014060040c03c15068000000003c0103c0200c0001400000010480101c0100000010010000300425000020080100002014080500001c02000040001700c0307400028380000201c0300801000040000105400010050040702818004030000004c2f01c0003000004030000400400004080040003c00008020700000003008050000200019004080300100018034000040902803000000200e04c03014080101305013000010000002c070600001c00010010000200000000000200401000004300001600000000050000400400cdd905150f576314543d5d0c5150f364314543a75924310e3f6550c43ad1854310e5f6550c43b51854310e9f6550c43c7d954310f976150c43a71854310f946150c43a51854310f1d4354843c750e5110f1d4354043ad18543d0a5f63547429718d51d0a5f63546429718d5190b1c5350d42ad1854350a5e63d45429758f5150a5e63141429758c5050a5e6194c42971855310b1d53d08428fd954210b1d53508429bd954210a5f63544429718d5110a7a60153329e58054ccb1c5450f32b518543cca3f64547328f19151cca7661d52329d587548ca3f64546328f191518ca7761551329d185544ca7b60551329e181544ca5c6550d32c7151434cad46150d328f993514ca3d64d45328f990504ca3d64141328f596540ca3e61950328f185540ca3e64150329798c540cb1d54cc83297d95320cb1d544c8329bd95320ca3f64544328f191510cb576154f41c794d439065e6394a419758e529072e5250a41a798c429069d6310a41a798f419069d63d06419798e509065d6394241ad987539071f5394e41ad98453906b661d4a41a798e529069d6394a41cbd4a52906b66114a418f994329063d650ca41a798e509069d6394241ced42509075453d0541c7d4e415071c5390541ad58743106b76150c41c754c431069e6310841a758c421072d5210841a798f411069d63d04418fd95411069f6350441a718d4110677
  | 4 => 0x86628edad51da7c48a092558778e481b118ab80e00059413c6d275332000241760004293a08955a95c798f146e5588807f40417c05aab57e0010700000000104800000000610000000007193f5d824c0024e000878001a33601540000000000032885328624b60000000012b00050e32cc7a9139eaa0001ef08c97946140000750e905a2028f42924d3c64655988b4681d0001860005bd6d80005c0b42c2191d4000000003c003400000020000000de000000002c30002c10c0001b65a55a0004600000000005486d28ac400000000239446474fa05c19e6947c13833eb194d29945a09cfd88a5524bc571c3288285708004d48a4000001e0544002c83d4000001aa03282c972b75cc3240024034844cfba8f28cad5312a74dcb95711a9424b2cb91ce3ca53cf59281dc704f81654905f8f91582229f93787b0267a4271e10c610c981b918805060818100814f71320000000029800003c000873a269c9b000390000c40220deb49322785382bc00211198150cb0000000009ea4f45e92d41ad0544380748e84a86fc002eb572ac0ac97c0c20012526101280400284000001138000000000027901c810e9a460002d01c245000b4d280250500005681d36e6e00509b05264c870000007715f0c75123842b0aa5e25805e86c4e2754a719b4ce17448898454b7c00163000674c7005000001400451645496ca9f00000167800000ae00003a1901b4600c552ca900000000000023a14022000000001c47e4000531c8a4c830125dc72d530003a096158a8e274799188005b45996a1c25d008c8e0003ba0000004c1a8b80a39ff08829044000284884411180346d4ef8702365a0b88002c4000739ed000610000000004dcaa8b91de7cc001fe32e6cca19780002191e1e8000b14dd800252000d4059000000891c023e6f11714b1760783a92d39a3392e800152000c009e3b400081a9414c3289515442c054761394ccb00000005b0af176a41542640000bf000001062c73f4000002de34c9ec000002429fd3e8000000004e2ea076000ada6b4c0000848002e6b30002d1330000002221784887a800000a949195a5145e4af1912482b07304a2a03c9442771462d45f25f078af44d1d61402cca497f5ba0e47a0df1028e909a5506c2e07d2f0062354ba0005361e9080325ae9311b000000394dd0074881f400000000000d58000669493182f48e55c69a8d0000000028514e000c2a354b21cc0008313a4980002b2da000000000000002b800000000e500030696d210000007e000000000000000001fa1780b1753c43acec8c643e7d903800000ac8002493188f8000000006890a9000c80002d8001f8718b50000d02654f0001621c5518780007f0d012b456b3400a0f398679120000f829560ae74348001228b304144001202ba4953b1be16e535050d92f6
  | 5 => 0x7e05c0018d0000814316144a0009a0d61fe408010004f80d02018b5c68704717015610434ac92583749f15c0001991fa70150834212953d813469000000084d90cd0000f88a9481f6000000000c09cc0017d22c9b4000002be0003b02c4d085c4b0005c800001800018b7148153144a094e879450000fe86a1a0714b58000006f4840001b8410618950dc414d08004
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x354800d8000074dc900d40ac690ca914ec0000b40000c84d3d4cd064fca400c0592d1000207800001c002888000000080000b8103000d400010084bce8188c3ca09498e4f800f045185424cc0061083950502c040081311c7cf40040000001040001289c5d24c53848e1352015446c70b01cd8616281050200301083c10206343850e0c00500001022385d946150c43c2eea30a8621d147150d5210e8a38a8728887451c54354043c28a630a86a15197015143ccb0a2a0c2a1e65851506150d32a2ce3a9ca720e0d635484210706a9ac4298838654d6014c41c1ac6a90a420e2952580521070cb1aa0280838a5895014041a2ce3aa4a918d0d72151430c68cb80a8a186383591520c831c2aca2188218e0d54588540c70caa2c02a063835915214831c92a4b00a418e1565194410c6c3390ca20863615c86510431b24e03288218d9170194410c68b3a8c420863455d46210431d0ac43108218d9270188410c6c8b80c420863259d8521043192aec2908218f0552148410c6c9380a420863645c05210431b0ce43008218d8572180410c748b00c020863a19884114031d0ac4208a018e1964540500c724b12a028063c41055014031e208218ea090f10410c4504870a298c2a1a81451c55310440c32a6b008220617651043110286b90a8a1e61851506150f30c28a830a869851471550310c28bba8821886186551600c4308a8e2b18a89043471590534828b39ea220a41459d3510c520c28c831ca2106146418d510828a38aa620841451cd5110420a28e2aa0621051474544310828bba88218841455d4410c420c2eca2086210615651043108390aa2a290041d054d5148020a52ea20a40106a06110520082a4ba86290041b01843148020f008218a4010514711503144383a908218a21c1148410c510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x140a0b10b190c00340201d210002a11801506150f32c05655c86510431c11655c06510431c05755886210431c81625c06210431c05765485210431d01525c05210431c81725806010431e01621055014031a108154d6010440a05821506150f30a1081551600c430b01851043148020d01751043148020
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 779
  | 4 => 754
  | 3 => 85
  | 2 => 14
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
  | 5 => packedAt s5K5 (23882+((h/259+packedAt s5K5 (21033+(h % 259)*11) 11) % 1028)*11) 11
  | 4 => packedAt s5K4 (31162+((h/251+packedAt s5K4 (28652+(h % 251)*10) 10) % 995)*11) 11
  | 3 => packedAt s5K3 (4361+((h/28+packedAt s5K3 (4165+(h % 28)*7) 7) % 113)*8) 8
  | 2 => packedAt s5K2 (860+((h/4+packedAt s5K2 (840+(h % 4)*5) 5) % 18)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ffff03ffffff81ffc1f0fffc3ffffb81f1ff
  | 1 => 0xf80ffffc07ffc1fe0fffff07ffc1fc04fe7e7c
  | 2 => 0xfff03ffff81ffffff001fff87ffe1fff0f8f8f
  | 3 => 0x3fffffe001fffffe00007fffe007f00ff0
  | 4 => 0xffffc000000001ffffffffff80000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x90a111189104908052d0504c9413255180b0b5
  | 1 => 0x32628228724902160542b1012c40483036565c
  | 2 => 0x4144a44120d2212aa0212a904aa412a60b0b0a
  | 3 => 0x658b38924483b5cd39b408c4733980c7d00de0
  | 4 => 0x860c30e3871c39f1ce39cce602310307ede000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xece8e8a0ece8e8a0ece8e8a0ece8e8a0ece8e8a0ece8e8a0ece8e8a0ece8e8a0ece8e8a0ece8e8a0ece8e8a0ece8e8a0ece8e8a0ece8e8a0ece8e8a0ece8e8a0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36733
namespace PEqualNP.Outside.L_meta_36733
open PEqualNP.Outside.L_meta_36733.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xc49155a003117909a435ce2ca0091003d190121c82a003600bcc57015689414c88174d4ea331158002753098e00f8022347800094fc0500002700576002900000522d1800059218005444002000411002085196400001404048a340007ff53017f94c07fd53017f14c05fe43007f50c05fc4301ffd4803fe5201ff54803fc52017fcc803fe32007f4c803fc3201ffd4407fe5101ff54407fc51017fcc401fe3100778c401fd31017f0c401dc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1c2004f798e10015bcc708013fd63840017eb1c2004f758e10005bac708013fc63840097e31c200effd4e1006ffca70803bfd538401bfe29c200dff90e10007fa8708037fc4384009ffb142004bfd8a10027fcc508006fe6284009feb142000bf58a10027f8c508012fc628401dffa94200cff94a10077faa508033fc528401bff994200cff8ca10007fa6508033fc32840177eb0c200effd4610077fca30803bfd518401dfe28c200dffcc610007fc6308003de3184001fe98c200dff0c610007b86308033ff2184001ff10c2000ff48610067f84308012fe6084009ffa842004ff94210027faa108013fc5084009ff9842004ff8c210027fa6108013fc3084009ff9042004ff88210027fa4108013fc2084009ff8842004fdc4210007f6210802fff65440177fb2a2000dfd9510004feca8802ffe65440077f32a200bff5951005dfaca8802ffc65440077e32a200bdf1951001cf8ca88003ff63440017fb1a2000f7d8d10005bec68802bfe63440057f31a2000ff58d10005fac68802bfc63440057e31a2000f718d10015b8c68802fff5344015ff29a200bff54d10057f8a68802bfe4344001fea1a200aff10d10007fec488002ff6244001f7b122000bbd891004ffcc488006fe6244001feb122000bf5891004ff8c488006fc6244001f63122001bb1891005ffea488027fe5244017fea922009ff14910057fe6488027fe3244001fe9922009ff0c91005ffea28802ffe5144017fb28a200bff5451005feaa28802ffc5144015ff98a2000ff8c510007bc6288003fd3144015fe18a2000f70c51004ffe4288003fe2144001fb10a2000ff48510007ea4288027fc2144017ffa822004ff9411005ffaa088013fc5044015ff9822004ff8c110007fa6088013fc3044013ff9022004ff88110007fa4088013fc2044001ff8822000fec4110027fc2088013f61044009ffb282004bfd9410027fcca0800efe6504009feb282007bf59410027f8ca08012fc6504009ffb182004bfd8c10027fcc60800afe6304009feb182000bf58c10027f8c608012fc630400fffa982006ff94c1003ffaa60801bfc530400dff2182000ff50c10037f88608013ff62040097fb102004ff9881000dfcc408013fd62040017eb102004ff18810025f8c40801fff520400bff2902007ff5481002ff8a40801bff320400bff1902000ff4c81002ff86408022fe610400fffa882007ff9441003ffaa20801ffc510400dff9882000ff8c410007bc6208003fd310400dfe1882000f70c41002ffe4208003fe2104001fe9082005ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0x2ff6588009ff32c4003bf99620027facb10052fd6588009fe32c4004bf19620027fec710012ff6388009ff31c4002bf98e20027fac710002fd6388009fe31c4004bf18e200a7fea71004ffe5388029fea9c4013ff14e2009ffc8710003fd4388027fe21c4001bf58a2000ffea510007fe5288003fea944001ff14a2000ffe6510007fe3288003fe9944001ff0ca20027fec310013fe61880017f30c4004ff58620005fac310013fc6188029ffa8c4014ff946200a7faa310053fc5188027ff98c4000ff8c620007bc6310003fd3188027fe18c4000f70c62000ffe4310007fe2188001f710c4001ff4862000ff84310007ec21880097f3044004ffd4220027fca110013fd5088009fe2844004ffcc220027fc6110013fd3088009fe1844004ffc8220027de4110007fb2088009fe1044004fe08220097feca9004aff6548001bfb2a40009fd9520097fcca9000efe6548025feb2a4012bf59520097f8ca9000efc6548025be32a40039f19520007fec690002ff6348023ff31a4002bf98d20007fac690002fd6348023fe31a4002bf18d20097fea690047fe5348025fea9a4011ff14d2008ffc8690003fd4348023fe21a4004bfd892000ffea490007fe5248003f72924001ff54920097daa490007fc5248003ff9924001ff8c92000ffa6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf18520097fea29004bfe5148025fea8a4012ff1452008ffe6290003fe3148001ef18a4000ff4c52008ff86290003dc3148003ff90a4001ff8852000ffa4290007fc21480037fb024012ffd4120027fca09004bfd5048009fe2824011ffcc120027fc6090003fd3048009fe1824001ffc812000ff64090013fe2048009f71024004ff08120027d84090007f82048011ffb2e2008bfd9710047fccb8800efe65c4011feb2e2008bf59710047f8cb8800efc65c4001ffb1e2000bfd8f10087fcc78800afe63c4001feb1e2000bf58f10087f8c78800afc63c4011ffa9e2010ff94f10047faa788043fc53c4021ff21e2000ff50f10087f88788003ff62c40017fb16200fff98b1000dfcc588003fd62c40017eb16200fff18b1000df8c588023ff52c401fff2962008ff54b1007ff8a588043ff32c401fff1962000ff4cb1007ff86588023ff51c4011ff28e2008fd94710047faa388023f551c4011fe28e2010ffcc710007fc6388003de31c4001fe98e2010ff0c710007b8638803fff21c4001ff10e2000fd88710007fa4388003f521c401ffe10e2008ffd4310027fca188023fd50c4009fe2862010ffcc310027fc6188003fd30c4009fe186200fffc8310027fc4188003fd20c4009fe1062004ffd9610025fecb08013fe65840077f32c2004ff59610075facb08013fc65840097e32c2004ffd8e10025fec708013fe63840057f3
  | 2 => 0x2100ff86490806ff614843bffa8a421dff945210effaa290877fc5148439ff98a4200ff8c521007bc6290803fd3148439fe18a4200f70c52100ffe4290807f72148403ff10a4200fb8852100ff84290807ec2148403fa10a4200ffd8121005fec090803fe6048401feb024200ff18121025f8c090877ff504843bff282421dff541210eff8a090873ff3048439fe1824201ffc812100ff84090813ff658c0097fb2c6004ff9963001dfccb18013fd658c0377eb2c6004ff19630025f8cb18013ff648c0097fb246004ff992300c5fcc918013fd648c0017eb246004ff19230025f8c91806fff548c035ff2a4601bff552300d7f8a91800afd638c005ffa9c6002ff94e30017faa71800bfc538c005ffa1c6002ff90e30017fa871800bfc438c009ffb146004ff98a3000dfcc518013fd628c0017eb146004ff18a30025f8c51806fff528c033ff294601bff54a300cff8a51806bff428c033ff2146000ff50a300cff8851800bff328c005ff1946002ff4ca30017f86518013ff618c009ff30c6000bf98630027fac318002fd618c009fe30c601bffd46300dffca31806ffd518c037fe28c601affd0630007fc8318003be418c001fea0c601aff1063000778831800bff318c005ff18c6000f78c630017fa631800bfc318c005ee18c6019ffc8630007fc4318003fd218c033fe10c6004bf98230027fea118013fe508c009fea846004ff14230027fe8118013fe408c009fe2046004ffcc230027be611800bfb308c009fe1846004fe0c230027fe4118013fc208c02fffb2a6017bfd95300bffcca9800efe654c02ffeb2a6017bf595300bff8ca9800efc654c001ffb226000bfd91300b7fcc898062fe644c001feb226000bf591300b7f8c898062fc644c02fffaa26016ff951300bffaa89805bfc544c0097fb1a6002ffd4d30017fca69800bde534c005fea9a6017f754d30017f8a69800bff434c005ff21a6002f790d30017fa8698003dd434c005fe21a6000ffd8930005fec498057fe624c0037f3126000ff589300aff8c498006fc624c02fffa926015ff949300bffaa498057fc524c02dffa126015ff90930007fa8498057fc424c005ff9926002f7cc930017fc649800bfd324c001ee9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c02fffa8a6017ff945300bffaa29805ffc514c02dffa0a6000ff905300077c8298003fd414c02dfe20a6000ef10530017fe629800bfe314c001ef18a6002ff4c530017f8629800bdc314c02bff90a6000ff88530007fa4298057fc214c0057fb026017ffd4130027fca09805ffd504c009fe2826016ffd0130027fc8098003fd404c009fe2026002ffcc130017f66098013fe304c009ef1826004ff0c130027b8609800bf8304c02bff9026004ff08130027fecb1001
  | 3 => 0xe3226218af19131137fea898897fe544c44dfeaa26225ff15131015fec69880bff534c405ff29a6202ff54d31017f8a69880bff434c405ff21a6202ff50d31017f88698803ff624c4017fb126224ff9893100dfcc498803fd624c449fe3126201bf18931137fea498893fe524c44dfea926224ff1493112ffe8498893fe424c401fea126224ff10931017fe649880bfe324c405fe9926202ff0c931015fec29889bff514c44dff28a6226ff54531137f8a298897ff414c401ff20a6200ef90531007fa8298897fc414c405ff98a6202fdcc531017fc6298803de314c405fe18a6202f70c531017e86298893ff214c449fe10a6200ffd8131005fec098803fe604c401feb026200ff18131025f8c09889bff504c44dff2826226ff54131137f8a098897ff404c44bfe2026202ffcc131017f86098893ff204c449fe1026202f7d9431017bcca1880b5e650c405eeb286202d759431017b8ca1880bdf640c405ef3206202f759031017b8c81888bdf540c443ef2a06222f75503110fb8a81880bdf620c405ef3106202f758831017b8c41888bdf520c441ef2906222f754831107b8a418887df420c441ef2106200f750831107b8841880bde610c4476f3086202f598431117bea21888bde510c445eea886222f71443110fbe8218803de410c401cf2086200f75043110fb882188039c410c441ef9086220f708431017bec01880bde600c405eeb006202f718031117bea01888bde500c445eea806222f71403110fbe8018887dc400c441ef9006220f7080310fffecb1087eff658843fff32c4203bf996210fffacb1087efd658843ffe32c4203bf19621007fec710802ff638843dff31c4202bf98e21007fac710802fd638843dfe31c4202bf18e210fffea71087bfe538843ffea9c421eff14e210f7fc8710803fd438843dfe21c4201bf58a2100ffea510807fe5288403f72944201ff54a210ffdaa510807fc5288403ff9944201ff8ca2100ffa6510807fc32884037f30c421fffd46210fffca31087ffd518843ffe28c421effcc621007fc6310803de3188401fe98c421eff0c621007b86310807ff2188403f790c4201fdc862100ff84310807f42188401ffb044200ff98221025fcc110803fd60884017eb044200ff182210fffea11087ffe508843ffea84421fff142210f7fe611087bfc3088403ff9044201ff0822100fd84110877ff654843b7fb2a421dff9952101dfcca90877fd654843b7eb2a421dff1952101df8ca90803ff63484017fb1a4200f7d8d21005bec690873fe63484057f31a4200ff58d21005fac690873fc63484057e31a4200f718d21015b8c690877ff5348439ff29a421dff54d210e7f8a690873fe4348401fea1a421cff10d2100dfec490807ff5248403ff2924201ff5492100ff8a490807ff3248403ff1924201ff4c9
  | 4 => 0x6ff634c805ffa9a6402ff94d32017bca69900bfd534c855eea9a6402ff14d32017fe869900bfe434c805ef21a6402ff50d32007ba869900bfc434c8037fb126401ffd493200ffca499007fd524c803fe2926401ffd093200ffc8499007fd424c803fe2126401ffcc932017de6499007fe324c803ef1926401ff0c93200fb86499007ec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6400bf18532157fea2990abfe514c855fea8a642aff1453214ffe82990a7fc414c805ff98a6402ff0c532017b86299007ff214c803fe10a6400ffd8132005fec099003fe604c801feb026400ff18132025f8c0990abff504c855ff282642aff54132157f8a0990a7ff404c853fe2026402ffcc132017be609900bfc304c803ff9026401ff0813211ffecb1888eff658c447ff32c6203bf9963111ffacb1888efd658c447fe32c6203bf19631007fec918802ff648c451ff3246218bf99231007fac918802fd648c451fe3246218bf1923111ffea9188a3fe548c447feaa46228ff15231015fac71880bff538c447efa9c6202ff94e31017bca71880bfd538c447eea9c6202ff14e31017b8a71880bff438c451efa1c6202ff90e31017bc871880bfd438c401eea1c6202ff10e31017b88718803ff628c44fff3146201bf98a31007fac518802fd628c44ffe3146201bf18a3111ffea51889ffe528c447fea946227ff14a31147fe851889ffe428c401fea146227ff10a31017fe651880bdf328c405ff1946227f78ca31017fa6518803dd328c405fe1946202f70ca31015fcc31888fff518c447ff28c6223ff5463111ff8a3188a3ff418c401ff20c6228ff10631017fe631880bdf318c405fb98c6202ff0c631017e8631889fff218c44ffe10c6200ffd8231007fcc118812fe608c401feb046200bf58231007f8c11888fff508c447ff2846223ff5423111ff8a1188a3ff408c451fe2046202ffcc231017be611880bfc308c405ee1846227ffc823113ff8411888fdf658c447ef32c6223f75963111fb8cb18803df648c451ef3246200f759231147b8c91888fdf548c451ef2a46223f755231147b8a918803df628c44fef3146200f758a3113fb8c51888fdf528c44fef2946223f754a3113fb8a5188a3df428c44fef2146200f750a3113fb8851880ade618c447efa8c6223f79463111fbaa31888fdc518c451efa0c6200f7906310073c83188a3dc418c44fef90c6227f708631007bec118803de608c401eeb046200f71823111fbea11888fde508c447eea846223f714231147be81188a3dc408c44fef9046227f708231137feca9889aff654c44dff32a6203bf99531137faca9889afd654c44dfe32a6203bf19531007fec898802ff644c401dfb226200afd913112ffcc898862fe644c401feb226200bf5913112ff8c898862fc644c401d
  | 5 => 0x380180a0020a8020010080100200900c0640000900a000078000000000080500000801801028038020000040080000b0100240080200200000000000004018000020040000000801c1880000a00c0080301e00c0000109800803005002010040050040040400500a00001800016000008030140000180500403804000000000000200160100100200e0000180001e0040300001200401010004000008180040000000800200401001004020008000000180180805800801801000004000270000000100901e0000300100a0000000201400400000006004028010000080000703c00c0080501200c0000100404c078020140200500103a060008000000180000700e028018000020200080500000005800000018010010000280600a01c00c0280100c00400002086014000050020000200300c000020000000000000200a0000380c0240000380202e0240f00600e0680b80b0000080200101601001001010014078000040080080d00e0080680000200c000070000100d80300a0000300004e07c0080200a0000000100a05c01802006000038000140200a00d0080040b0020020240101300e000058020040180400700200000002018000018000020000000000a000000030080002280d0000040000001001c020000080500580b00802c030000020580001600a018018000000340e00802207801818000010000100000580080100200000004000008038020020140080100000400800018000008060120000e802004004020000100100001500400c050000020000100b0020000e80000602c0000000401c038000040140500002e00c0800401c008000070000180780c002004048000080100400000201401000000008038000000000100001801059ffb2a862cbfd9543167fccaa180efe6550c59feb2a862cbf59543167f8caa180efc6550c057fb1a8602ffd4d43017fca6a180bfd5350c05fe29a8602ff90d430177c86a180bfc4350c05ee21a8602e710d43007fec4a1802ff6250c57ff3128601bf98943007fac4a18affc6250c037e312862cffd494315ffca4a18b3fd5250c57fe2928602ffcc943017be64a180bfe3250c05fe1928600ffd8543005fec2a1803fe6150c01feb0a8600ff18543005f8c2a18b3ff5150c59ff28a862cff54543167f8a2a180bff3150c05fe18a8602f70c54315ffe42a18affc2150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028604bf18143167fea0a18b3fe5050c59fea82862cff14143017fe60a180bdf3050c05fe182862bffc814315ff840a18abff654c8557fb2a642aff9953201dfcca990abfd654c8557eb2a642aff1953201df8ca99003ff644c8017fb226429ff991320c5fcc899003fd644c8017eb226429ff191320c5f8c8990abff544c853ff2a2642aff5513214ff8a899
  | 6 => 0x8aae4453e80010680007748f18f07e95d8e8a31837e4e80006519800021923f80019b8cfdc01218cb1328000000001e38001bc8002100afd5680006048192916815f623ce50031261869530415fa900a118d3e02a1124c64905c0438078f5979a400b4155c1598c4640620000000002070000000000e60001ae0000000b480000000000000020a8691780ee00000015b91cc000b704425020505e0ac8001450f508e5b092091d0000139562129da0000ed000249887a1a0588b7a2a1e60000249de860867006d8c8000001e30001f724100017697a0845d9000133a508e01ac0002300870000e598e9b98d81464704000001a101d4b30000000001b58000c4a0200000013c0a816780b8b381ce089269898e7938811db30a8a30a1706e85b91b0f19c90d848217b06d57019c07f57641b0510d89439685d786bd2880024bc210549000001041b49ab00008916a80000013595252f8001594001be19d09790700806981a95450a80017c80000000021c24ad371eb9a692015fd2d0000128000090f7cb44f49aa9e81790d8c909178b4df2884e3c83093989ada58a195c80e52518b14a0801c50294bed5757e06b4c6846a16a34cdf0cc908a0801200000000000008680d4df8000810001d51998000000000630028000001e988d8ec19c80010f0458098fb0470000000000000460000831da9df14b80011a8b80de8cd15b07c8058e7d8286d9471bd05188b823048c0888511205b13782580022a9600000a1c000e70678000000000520000b8a469b700000000003f09600a94981d10580013001f4000001c284940021f000000000098a1b9cf1e5a2209400007181c80000017600000000005c43f80001e86696f24a0f30001220000002470a10ac1df917c7f9cb0f01b11d2068c389d04748300c620983c030e4507823ce3c0d0a4817c0c6c00152c0022d00004d8c91348a40001909960000001048a723d8331299429cd08e14c41818656709c43c800060c0002ac2a0c0554c9b84e2489c596d635d4f18791a199175cf41110ea1740001f20000e312d80000000c59e1bb0001118bfa2180000000000011dc001a0800191a3321480006840000021f800005160800179d47db88658060ef80000000003b06e40000000000001111e00018a19f1739e400a00016e00010c8002090228002271baa2c16da019f008c00016181bc7518d09043b9550898269e521793184a87f169dfc00000009c8648001a887587c1db00002b2231c60000001bc000183a36168cc08001061c3a1e04b00000000014cc000251e008fc0016314880000014e810243c000804000241ee9fa0b34001270f780009be408ab1b01aa01ed5f08d4ba1e11521d18380d00ed5611e88fa80010d2448b3c0600600001c0280900200c0080300002c078000000000300102a008058090
  | 7 => 0xc16a0000a48559d38341010000042199931c880d84e8489cd8c980116e52786823e06001f81a00000019680018b8048454000000000569710001a70001e191300000000018480000005bd2100002040017484907880000004f06a80000000005f8000001b800edf5090d6c00008a14685acb153cdad800050000180842c0000024dd729d6800036d25977d3318186c00006ecd552f15d0a9df116e81b55f9e79d41d00001180858530000000000001f3077cda2418560ad83d2244001870cec000000000399d3124a4ba138000889fd2462212048da8d18d951490b2151861eb00001352e02005809281903d8fc1f81b50a2d90242169800000216034915831dc095e04786a1cb9f8c95954883e2c8170c7d3b1ef80000008ec7d1c820d1940d9d1d80017501ac8d00018100000009000000012400000000004800023280000024580000011c8000000bb0001461a980007900000024792b14e0001078000000a3946c000e28e98c88aa4b501600008c8bb884837432a434001109d08000cf4339dba041409e714911507a1de0ad13d63d22b9368000001d2874039059cb080007fcb59fc9d88d10000008d494f8421fe0000840a5800117000222a4d00020d852a399bf10907ee4f0358bd8f20fb9775ce86fca00539309c123f15542f0ca9690aa8ae80005780019f8a6092d53a4b1730400c51f78379ef069476800000159a440000d28a68918798000cf8001e6a4f80000018500022080000000006cc0000016a4700000000c29b78000e68c30d64711be92657e87b9a281dc000fd978c000000e90000ec8f985d91019a82193d9f68a30981b189c18408e891c2a92c8320271744f39c411b80012c1f92339949dd8c80bc8ef1920c00d6e35805c0000021e80c8000000000000b10001fda2622b10f8000e4042849a03a1300005f06ad4d957c0024d846c000e10d5000000053de90fc91691756216ec0019e80005a80000004a00000018900021880020e00019580000004b84753200000000000020024aa251bd923000243a1d05d173c0000000207dc000000000000000d21f600020f18a80009705e95914bd534001a507601f00004c0001f0c770e48000ae15194593f823a2f11f80013e0000278ec5f19ae9a20a29d48c787aa031acd0e1708318af09906b0bc08f44081d8d314202814c81fdf8978869c8dd3f00020b188a3522e1a781400017840c1fb06600cd5102e8a3c0000019b0939979239d80ff60e84485fc00032c43ccd8001198e3ce08000000f900f0001485cc862a3d4d748286f54c001a248c8c000001d10000074e399288b0b060784444511f07b14740017a841dbb8001d5806a4cc00000000228a1c8d440000000005b41890d8001a18000000f280000000000017b80015800013c8d7d8c0000000f706de05883976c16901
  | 8 => 0xdb09212dd1d42a52e80000000006c94a8ba9ed9950000000000bfe0a095011800158944a0c0001939a6c065a80ed80015000000d0d5d4d15414b08553ba268db9c997590b8000a946f16f83664ec260b1e280436521430729b29cf8ce5dd0a09d700fa42cb021824e57942f9419fb9e08419caa3b95a0000000000c58000d424c80014800008fa290000b900009d00008cc0016605a05361b1b90aa0002368af82b9c680000000000013a9f98f80eb93d0b9a2e8c12528371ff24c041020cd38cf0d71ee1ac89e2431c78fa01c43246c4000a353402c9cc1529af967c00000237a0b90295786b8c212a8001628000a98000910f08a25f94368124d795e8c85ed063a2d81503144ca240924ce8e817f1160001391a64000001584001a61b44000000c75658fe8000000001098f686e00008800000009aa278000001dca3709d8f1174c290b544d172215a3493600dc3e00002c1874001c70bea298000000000000c18001128000000b5c0002091923809f8b21dc07217781e0c41508eb06189145982e1479c205a58316b8b240010a13a0de03e9ad0b18b29a48e2012de49400ab85c8430001648001fe8000001af17d8b2e4e0002388d5800000200847d081b6000000155902054d64103a0f80e8540002200dc182148c0022580014100016d0179a90000149ab848623800076c7e00018598e0e84001689910d900001b951d2b8001b3a321380fe0000001ea8f60739881bf80000000023900001096699d8dc8fd01309e8a14cb96b1c1a3c59700000b000186da01310d981983061217f80012803a2068000000c64ee4dd09a16c80011c0221189a385094d57556dc289ec9c485511ea4d49b0000cc2340be0e198f82989f19880002d0ea99a0bf1f4958cff953e2f86f9ca0c383aa3555149323b0000b0cdd842513a3a1351228709e29d61ba1ea1b690309690ea1a96525100e0039770d4db200000712a00021d8000000ee800061045d56c0008623a87d8000a508a95700001e47e57189485440017d1c3156651a0601c0351800001638d62109a41051ce0808000a795c07863e8464000ca00000000006d00002d80016955aa010000000000000002310000000998000000bf5ff80004f9d980000014405f4000779f58bd0d68a90b606a58d8591f09141ec0688361f40f889b4002428a21e21f391bc310ce029da30b68570ede0c8001b40002140ffcff0c7000073000044dcc4001
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xb62c4110007e862c4110025fa71c4110026fb61c4110027f361c41101b7f251c41101b7f151c4110007da31c4110007d831c4110007f221c4110007f121c4110004ff7558c1001cfe7558c10004fd7558c1001cfc7558c10004ff7458c100c4fe7458c100c4fc7458c10026df7358c10036de5358c10006dd5358c10036de4358c10004ff7258c1000cfe7258c1000cfc7258c10036df3258c10014ff7158c10014fd7158c10034fc7158c10036dc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10004ff7650c10024fe7650c10004fd7650c10024fc7650c10016de6350c10006dd6350c100379c4350c10004ff755881001cfe7558810004fd755881001cfc7558810004ff7358810014fe7358810014fc7358810026ef725881002eee5258810006ed525881002eee325881000cff715881000cfd715881002cfc715881002eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026f71058810026f51058810004ff764c810024fe764c810004fd764c810024fc764c810016de634c810006dd634c81000eee624c810006ed624c810005f7714c810005f4714c810084ff768c410024fe768c410014fd768c410024fc768c410016de638c410006dd638c410025fa708c410005f9708c410006df768c410016de768c410016dd768c41018edc768c41018edf658c41011ede658c4101aedd658c41018edc658c41018edf648c410146de648c410006dd648c41018edc648c41018edf628c41013ede628c410006dd628c41018edc628c41017dde718c4101a6de618c4100079e418c41018fda708c410007d9708c41018ede608c41018fd7108c41018fda108c41018fd5108c410084ff764c410005bf744c41019dbc744c410016df760c41017ede760c410036dd760c410016dc760c4100375e750c4100375d750c41017edf650c410116de650c410196dd650c41017edc650c41017edf640c41010ede640c410006dd640c41017edc640c41017edf620c410106de620c410006dd620c41017edc620c41018dde710c410037d6710c410086de610c4100079e410c4100079c410c410187d7210c410187d4210c41017fda700c410037d9700c41017ede600c41017fd7100c41017fda100c41017fd5100c41007cff7688410024fe768841000cfd7688410024fc768841000eee6288410006ed628841007ef66188410025fa7088410005f9708841007cff7648410005df7348410035dc734841007ef66148410025fb7644010006fb7644010004fb76440100077b7544010177787544010007db7344010007d87344010007eb7244010007e87244010025fb7144010027f3714401016efa6144010027f26144010007da3144010007d83144010
  | 1 => 0xc510006df628c510007cf628c510006cf628c51013ede628c510006dd628c51013edc628c510007cc628c51013ecc628c510055de718c510207d6518c510207d5518c5100079e418c51018fd6108c510024fc764c5100067f654c5101367c654c510005bf744c5101fdbc744c510006bf644c51012ebc644c510006df634c510016dc634c510006ef624c510126ec624c510005fb704c510025f8704c510005de760c510056de760c510004de760c5100575e750c5100575d750c5101eedf650c5100075f650c5100065f650c510116de650c5101eedd650c510116dc650c5101ef5c650c5101165c650c510006df640c5100079f640c5100069f640c51010ede640c510006dd640c51010edc640c5100079c640c51010e9c640c510006df620c510007cf620c510006cf620c510106de620c510006dd620c510106dc620c510007cc620c510106cc620c5101f5de710c510057d6710c5101efd6510c5101efd5510c5101e7d7410c5100079e410c5100079c410c5101e7d4410c51000794410c51017fd6100c510064fe76885100067f65885100fe7c6588510006df63885100f6dc6388510006ef628851000eec6288510007d63188510007d43188510005f67688510066f676885101ddf775885101ddf575885100077765885101d7746588510007d76388510007d4638851004df57288510007e7628851000ef6628851000ef4628851004fe4628851000ee4628851004fe652885101d7e55288510025f67088510025f470885101cfe620885101cfe42088510024fc76485100067f65485100ee7c6548510005df7348510055dc7348510006df63485100e6dc6348510006ef624851000eec6248510007d63148510007d43148510005fb7048510025f87048510025f4764851000ef47648510024f476485101c5f775485101c5f575485100077765485101bf746548510007d77348510007d47348510007d76348510007d4634851004df77248510007e77248510007e7624851000ef6624851000ef4624851004fe46248510007f37048510025f67048510025f47048510007f07048510014ff764c110054fd764c110014fc764c1100067f654c1100be7c654c110006bf644c1100b6bc644c110006df634c110016dc634c110006ef624c1100aeec624c110005f7714c110005f4714c11000cff764811004cfd764811000cfc76481100057f754811005d7c75481100067f65481100967c6548110006df634811008edc6348110006ef624811000eec6248110005f77148110005f47148110027e820481100067f65c41100467c65c4110006df63c4110086dc63c4110006ef62c411007eec62c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024fa76c41100077b65c41101b77865c4110007db63c4110007d863c4110007e
  | 2 => 0x4eee52d8910006ed52d891004eec52d8910006ef32d891004eee32d891004eec32d891000cfe71d8910024fd71d891000cfc71d891004eef21d8910024fe70d891004cfd70d8910024fc70d891004eef20d891004dee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89101cfe771d8910007e651d8910007e551d89101cfe610d89101cfe410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ee43d8910006ed43d8910006ec43d89101ceef71d891004eee71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef31d8910006ec31d8910006ef70d89101ceee70d8910006ed70d89101ceec70d8910006ef50d89101ceee50d8910006ed50d89101ceec50d8910006ef30d89101ceee30d89101ceec30d89101ceee10d89101ceec10d89100057f755891005d7c75589100067f65589100067c6558910005df7358910055dc7358910006df6358910006dc635891004eec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc735891004cff7258910006ef7258910064ff7158910006f7715891007cff7058910006fb7058910005ee761891004eee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc631891004fe5711891020eef6118910007e65118910007e5511891020fe6101891020fe41018910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101567c654c910006bf644c91014ebc644c910006df634c910016dc634c910006ef624c91000eec624c91006cfe768c5100067f658c51011e7c658c510006bf648c510146bc648c510006df638c510016de638c510006dd638c510016dc638c510006ef628c51013eec628c510005de768c510006de768c510004de768c510206df658c5100075f658c5100065f658c51011ede658c510206dd658c51011edc658c5102075c658c51011e5c658c510006df648c5100079f648c5100069f648c510146de648c510006dd648c510146dc648c5100079c648c5101469c648
  | 3 => 0xd71d8d10014fc71d8d10056df31d8d10024fe70d8d10054fd70d8d10024fc70d8d10056df30d8d10055de76d8d10014de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dc64d8d10006de62d8d10006dc62d8d10007d651d8d10007d551d8d1018fd610d8d1018fd410d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dc42d8d1018edf71d8d10056de71d8d10014de71d8d10006dd71d8d10014dc71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d1018ede70d8d10006dd70d8d1018edc70d8d10006df50d8d1018ede50d8d10006dd50d8d1018edc50d8d10006df40d8d1018ede40d8d1018edc40d8d10006df20d8d1018ede20d8d1018edc20d8d1018ede10d8d1018edc10d8d100057f7558d1005d7c7558d100067f6558d100067c6558d10005bf7458d101fdbc7458d10006bf6458d10056dc6358d10005ef7258d1004dec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d100c4fe7458d100c4fc7458d10006bc7458d100c4bc7458d10054ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d1006cff7158d10006f77158d10056dc3158d10084ff7058d10006fb7058d10005de7618d10056de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d1017edf6118d10007d65118d10007d55118d1017fd61018d1017fd41018d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d101667c6550d10006df6350d10016dc6350d100579c4350d1015eec6250d10005f77150d10005f47150d1000cfe76d89100067f65d89100067c65d8910006df63d8910006dc63d891004eee62d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910014fe73d8910004fd73d8910014fc73d8910006ef52d8910
  | 4 => 0x8a10024fc7058a10026ee2058a10026ec2058a10026f71058a10026f51058a10004ff764ca10024fe764ca10004fd764ca10024fc764ca1014ebe644ca10006bd644ca10016de634ca10006dd634ca10005f7714ca10005f4714ca10054fd768c610146be648c610006bd648c61018edf638c610016de638c610006dd638c610016dc638c61018ddd768c610006dd768c61018edf658c61011ede658c610236dd658c61018edc658c61018edf648c610146de648c61018f9e648c6101469e648c610006dd648c61018f9d648c6100069d648c61018edc648c61018edf628c61013ede628c610006dd628c61018edc628c6100079e418c61018fd7108c610014ff764c610024fc764c610005bf744c61022dbc744c61012ebe644c610006bd644c610016de634c610006dd634c610005fb704c610025f8704c61017ddd760c61006edd760c61006f5e750c61006f5d750c61017edf650c610116de650c610226dd650c61017edc650c61017edf640c61010ede640c61017f9e640c61010e9e640c610006dd640c61017f9d640c6100069d640c61017edc640c61017edf620c610106de620c610006dd620c61017edc620c61006fd6710c6100079e410c6100079c410c61021fd7210c61021fd4210c61017fd7100c61004cfd76886100f6de6388610006dd63886101ceef628861000eec628861000cff7648610024fc7648610005df734861006ddc73486100e6de6348610006dd634861000eee6248610006ed6248610005fb7048610025f87048610025f976c4210006f976c4210027da63c4210027d963c4210027f271c4210007da31c4210007d831c421005d7e76d951005e7e76d951001c7e76d95100067e63d95100067c63d95100067e62d95100067c62d95102177771d951005f7471d95102177610d95102177410d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067e32d95100067c32d95102167f71d951005e7e71d951005e7d71d951005e7c71d95100067f31d95100067c31d95100067f21d95100067c21d95100067f70d95102167e70d951005e7d70d95102167c70d95100067f30d95102167e30d95102167c30d95100067f20d95102167e20d95102167c20d95102167e10d951005e7d10d95102167c10d9510014fe76d8d100067f65d8d100067c65d8d10056de63d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d100c4fe74d8d10004fd74d8d100c4fc74d8d10006df53d8d10056de53d8d10006dd53d8d10056dc53d8d10006df43d8d10056de43d8d10056dc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10056df32d8d10006de32d8d10056dc32d8d10014fe71d8d10024f
  | 5 => 0x25edd650c710116dc650c710006df640c71010ede640c710006dd640c71010edc640c710006df620c710106de620c710006dd620c710106dc620c710087d6710c71025fd6510c71025fd5510c710257d7410c7100079e410c7100079c410c710257d4410c71000794410c710087da700c710087d9700c710024fd768871000eee6288710006ed6288710007d63188710007d43188710025fa7088710005f97088710025f5768871000ef57688710024f5768871024df7758871024df5758871000ef6628871007fe66288710007e5628871000ef4628871007fe65288710247e55288710025f67088710007f27088710007f17088710025f470887101cfe620887101cfe4208871002cff7648710005df7348710085dc7348710007d63148710007d43148710005f7764871002ef7764871023df7754871023df57548710007d77348710007d47348710007e7724871000ef6624871000ef46248710025f67048710025f47048710014ff764c310014fc764c310016de634c310006dd634c310005f7714c310005f4714c31000cff764831000cfc76483100057f75483100457c754831000eee6248310006ed6248310005f77148310005f47148310004ff7558e1001cfe7558e10004fd7558e1001cfc7558e10004ff7458e100c4fe7458e100c4fc7458e10026df7358e10006df5358e1006ede5358e10006dd5358e1006edc5358e10006df4358e1006ede4358e1006edc4358e10004ff7258e1000cfe7258e1000cfc7258e1006edf3258e10006de3258e1006edc3258e1006edf3158e10024fc7058e10026de3058e10026dc3058e10006df7558e10006de7558e10006dd7558e10006dc7558e10006df7458e10006de7458e10006dd7458e10006dc7458e10006df5458e10006de5458e10006dd5458e10006dc5458e10006df7258e10006de7258e10006dd7258e10006dc7258e10006df5258e10006de5258e10006dd5258e10006dc5258e10006df4258e10006de4258e10006dc4258e10006df7158e10006dd7158e1006edc7158e10006df5158e10006de5158e10006dd5158e10006dc5158e10006df4158e10006dc4158e10006df2158e10006dc2158e10026df7058e10026de7058e10026dd7058e10026dc7058e10026df5058e10026de5058e10026dd5058e10026dc5058e10026df4058e10026de4058e10026dd4058e10026dc4058e10026df2058e10026de2058e10026dd2058e10026dc2058e10026df1058e10026de1058e10026dd1058e10026dc1058e10004ff7650e10024fe7650e10004fd7650e10024fc7650e10016de6350e10006dd6350e1006f9c4350e10004ff7558a1001cfe7558a10004fd7558a1001cfc7558a10004ff7358a10014fe7358a10014fc7358a10026ef7258a10066ee5258a10006ed5258a10066ef215
  | 6 => 0xf744c520275bc744c520016df760c52008ede760c52008edd760c520016dc760c52008f5e750c52008f5d750c52026edf650c5200075f650c5200065f650c520116de650c52026edd650c520116dc650c52026f5c650c5201165c650c520006df640c52010ede640c520006dd640c52010edc640c520107ce720c52008fcd720c52017edf620c520107ce520c52026fcd520c52013dde710c52008fd6710c520006df610c520007d7610c520006d7610c520006dc610c520007d4610c520006d4610c5200079e410c5200079c410c52008fda700c52008fd9700c520106df600c520107db200c52017fce200c52017fcc200c520107d8200c520014ff764c12000cfe764c1200acfd764c12000cfc764c1200067f654c1200be7c654c120006df634c120016dc634c120005ef724c12000dec724c120027e8204c120086de63d8f10004ff75d8f1001cfe75d8f10004fd75d8f1001cfc75d8f100c4fe74d8f10004fd74d8f100c4fc74d8f10084fd73d8f10086de53d8f10006dd53d8f10086de43d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10086df32d8f10006f671d8f10006f970d8f1018ede30d8f1018edc30d8f10014ff7658f10086dc6358f10004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f100c4fe7458f100c4fc7458f10006df7358f10004ff7258f1000cfe7258f1000cfc7258f10024fc7158f10086dc3158f10086df3058f10004ff7650f10004fe7650f10004fd7650f10004fc7650f10006df6350f10016dc6350f100879c4350f10005f77150f10005f47150f100457e75d8b100057d75d8b1007eee62d8b10004ff75d8b1001cfe75d8b100067e75d8b1001c7e75d8b10004fd75d8b100067d75d8b100047d75d8b1001cfc75d8b10014fe73d8b10004fd73d8b10014fc73d8b1007cfd72d8b1007eee52d8b10006ed52d8b10006f671d8b10006f970d8b101ceee20d8b101ceec20d8b1000cff7658b1007eec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7358b10014fe7358b10014fc7358b10006ef7258b10024fc7158b1007eec2158b1007eef2058b10004ff764cb10004fe764cb10004fd764cb10004fc764cb10006df634cb10016dc634cb10024fd768c710016de638c710006dd638c710025fa708c710005f9708c710016de768c710016dd768c7101a6df658c71011ede658c7101a6dd658c71011edc658c710006df648c710146de648c710006dd648c710146dc648c710006df628c71013ede628c710006dd628c71013edc628c7101a7d6518c7101a7d5518c7100079e418c710007da708c710007d9708c710034ff764c710005bf744c710265bc744c710086de760c710086dd760c7100875e750c7100875d750c71025edf650c710116de650c710
  | 7 => 0x9520014fe76d8d200067f65d8d200067c65d8d2008ede63d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d200c4fe74d8d20004fd74d8d200c4fc74d8d20006df43d8d2008edc43d8d20024ff72d8d2000cfe72d8d20024fd72d8d2000cfc72d8d200cedf32d8d200cedd32d8d20004fe71d8d20004fd71d8d2008edc31d8d2000cfd70d8d2008edf30d8d200057f7558d200957c7558d200067f6558d200067c6558d20005bf7458d20275bc7458d2008edc6358d20005f77158d20005f47158d20285fb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d200c4fe7458d200c4fc7458d20006bc7458d200c4bc7458d200ccff7358d20006df7358d2008ede5358d20006dd5358d2008ede4358d200acff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d2008edc3158d20284ff7058d20006fb7058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d201667c6550d20016de6350d20006dd6350d2008f9c4350d200067f65d85200067c65d852008dde73d8520005dd73d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520014fe73d8520006de73d8520014de73d8520004fd73d8520006dd73d8520004dd73d8520014fc73d8520024fd72d8520006f731d8520006f431d8520066f621d8520066f521d85200957e75985200057d75985200067f65985200067c6598520006f7619852004df970985200057f75585200957c75585200067f65585200067c6558520005df735852008ddc735852007dfb70585200067f65185200067c6518520006f56118520004ff751852001cfe7518520004fd751852001cfc7518520014fe7318520004fd7318520014fc7318520024fd721852002eee5218520006ed5218520006f73118520006f4311852002ef6211852002ef52118520024fe7018520024fc701852020eee201852020eec2018520004fe768c520004fd768c520004fc768c5200067f658c52011e7c658c520006df638c520016de638c520006dd638c520016dc638c520006df768c520006de768c520006dd768c520006dc768c52027edf658c5200075f658c5200065f658c52011ede658c52027edd658c52011edc658c52027f5c658c52011e5c658c520006df648c520146de648c520006dd648c520146dc648c52018edf628c52013fce528c52027fcd528c520105de718c520006df618c520006dc618c5200079e418c52013edf608c52013fdb208c52018fce208c52018fcc208c52013fd8208c520004ff764c520004fe764c520004fc764c5200067f654c5201367c654c520005b
  | 8 => 0x24fc7058e20026de3058e20026dc3058e20004ff7650e20024fe7650e20004fd7650e20024fc7650e20016de6350e20006dd6350e2009f9c4350e20004ff759862001cfe7598620004fd759862001cfc7598620014fe7398620004fd7398620014fc7398620026f67198620006f65198620006f5519862007ef6219862007ef52198620024fe7098620026f61098620026f41098620004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff7358620006df7358620004df7358620014fe7358620014fc7358620006dc7358620014dc7358620026f77158620006f65158620006f5515862004ef6215862004ef5215862004eec2158620024fc7058620026f61058620026f41058620004ff768c620024fe768c620004fd768c62018edf638c620016de638c620006dd638c620016dc638c620006df768c62018ede768c620006dd768c62018edc768c62018edf658c62011ede658c6202bedd658c62018edc658c62018edf648c620146de648c620006dd648c62018edc648c620006de618c620006dd618c6200079e418c62013fcc218c62018ede608c62018fcf208c62013fdb208c62018fd8208c620004ff764c620004fd764c620024fc764c620005bf744c6202b5bc744c620005ef724c62000dec724c620016df760c62017ede760c62009edd760c620016dc760c62009f5e750c62009f5d750c62017edf650c620116de650c6202aedd650c62017edc650c62017edf640c62010ede640c620006dd640c62017edc640c62009fd6710c620006de610c620006dd610c6200079e410c6200079c410c620107cc210c62017fda700c62009fd9700c62017ede600c62017fcf200c620107db200c62017fd8200c6201ceef65886202a6ed658862000dee718862000fe671886201cfe66188620006ed61886201cfe56188620007ce3188620007cc31886201cfea70886201cded7088620007e9708862000eee608862000fea608862029d7e76d95200967e76d952001c7e76d95200067e63d95200067c63d952028f6f72d95202976c72d95202977b20d952028f6e20d952028f6c20d95202977820d95200067f73d95200067e73d95200067d73d95200067c73d95200067e43d95200067c43d952028e7f72d95202967e72d95202967d72d95202967c72d95202967f32d95202967e32d95202967d32d95202967c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067c31d95202967f21d95202967e21d95202967d21d95202967c21d95202967f70d952028e7e70d95202967d70d952028e7c70d95200067f30d952028e7e30d952028e7c30d95202967f20d952028e7e20d95202967d20d952028e7c20d952028e7e10d952028e7c10d
  | 9 => 0xc7458530005ef72585300adec7258530085fb7058530006f56118530004ff751853001cfe7518530004fd751853001cfc75185300c4fe7418530004fd74185300c4fc741853017edf7318530024fd7318530036de5318530006dd5318530036de4318530006dd431853000cfe7218530004fd721853000cfc7218530036df3218530006dd3218530036f63118530036f53118530006f72118530006f4211853017ede301853017edc3018530004fe7690530004fd7690530004fc7690530006bf64905300c6be64905300c6bc6490530015dc73905302ef9e43905300079d4390530006bf7690530006be7690530006bd7690530006bc769053031ebf6590530326be659053031ebd6590530326bc65905300079f73905302ef9c739053030ebf63905302ef9e539053031f9d5390530006bf6290530316be6290530316bc62905302ef9f32905300079d32905302ddbe7190530006bf6190530006bc61905302ef9c31905302eebf60905302efbb309053030f9e309053030f9c30905302efb83090530004ff7650530004fe7650530004fc7650530005df7350530015dc73505300c6bf76105300b6be76105300b6bd76105300c6bc76105300b73e75105300b73d75105302febf6510530306be65105302febd6510530306bc65105302df9e73105300b79d73105302e6bf63105302df9e53105302ff9d5310530006bf62105302f6be62105302f6bc62105302df9f32105300079d32105302edbe71105300b7b67110530006bf6110530006bc61105302df9c31105300b7ba70105300b7b970105302debf60105302dfbb30105302e79e30105302e79c30105302dfb83010530024de768c5302d5df758c5302d5dd758c5302cedf658c53011ede658c5302cedd658c53011edc658c530005df748c530005dd748c530006df648c530146de648c530006dd648c530146dc648c530005dd728c530006df628c53013ede628c53013edc628c530015de718c530017d6718c530006df618c530007d7618c530006dc618c530007d4618c530006d4618c5300079e418c5300079c418c530025de708c530007da708c530007d9708c530025dc708c530016df608c530017db608c530004fe7688530004fd7688530004fc7688530005df7388530015dc7388530006ef628853000eec6288530004ff7648530004fe7648530004fc7648530005bf74485300b5bc7448530005df7348530015dc7348530014fe76501302c4fd7650130014fc7650130005df7350130015dc73501300079d4350130004ff7558e2001cfe7558e20004fd7558e2001cfc7558e20004ff7458e200c4fe7458e200c4fc7458e20026df7358e2009ede5358e20006dd5358e2009ede4358e200aedf3258e200aedd3258e20004ff7158e20004fc7158e2009edc3158e20024fe7058e20
  | 10 => 0xc630017da608c630004ff7688630024fe7688630004fd7688630006f66188630006f56188630004ff7648630004fd7648630024fc7648630005bf74486300d5bc7448630005df7348630015dc7348630006f66148630006f561486300c4fe76d91300b6be64d9130004ff75d913001cfe75d9130004fd75d913001cfc75d91300b6be54d9130006bd54d9130024ff73d9130014fe73d9130024fd73d9130014fc73d9130356bf43d9130356bd43d913000cfe72d9130004fd72d913000cfc72d9130006be42d91300b6bc42d9130356df32d9130004fe71d9130004fd71d91300b6bc41d9130356dc31d9130014fd70d91300b6bf40d91300b6bc645913034dfb7059130004ff755913001cfe7559130004fd755913001cfc75591302c4ff7359130006df7359130004ff725913000cfe725913000cfc72591302c6df3259130004ff7159130004fc71591302c6dc315913034cff7059130006fb7059130025dc7650d300c6dc7650d30024dc7650d30345df7550d30345dd7550d30015df7450d300179f7450d300079f6450d300c6de6450d300c6dc6450d300b79c6450d300c69c6450d30005df7250d300b79f4250d30005dc7150d300b79c4150d30007db7050d30025de7050d30025dc7050d30007d87050d30016df6050d30017db6050d300b79f4050d3000cfe76d89300aeee62d8930004ff75d893001cfe75d8930004fd75d893001cfc75d89300c4fe74d8930004fd74d89300c4fc74d8930024fd73d893000cfc73d893009ede53d8930006dd53d893009ede43d8930006dd43d89300aeee32d893009eed32d8930004fe71d8930004fd71d893009edc31d89300aeec21d8930014fd70d89300aeef20d89300057f75589300bd7c7558930005bf74589300b5bc74589300aeec6258930005f77158930005f4715893033dfb7058930004ff7650930004fe7650930004fc76509300c6be6450930015de73509300079d4350930025dc764c93000edc764c930024dc764c930335df754c930335dd754c93032edf654c93032edd654c930005df744c930005dd744c930006df644c930006dd644c930015df724c930017cf724c930007cf624c93000ede624c93000edc624c9300afcc624c93000ecc624c930005dc714c930007db704c930025de704c930025dc704c930007d8704c930016df604c930017db604c9300b5be74d8530005bd74d8530004ff75d853001cfe75d8530004fd75d853001cfc75d85300c4fe74d8530006be74d85300c4be74d8530004fd74d8530006bd74d8530004bd74d85300c4fc74d8530024fd73d853000cfe72d8530004fd72d853000cfc72d853006ef631d853006ef531d853006edc31d8530006f721d8530006f421d8530006f76198530055f970985300057f75585300bd7c7558530005bf74585300b5b
  | 11 => 0x2c6bd4359230004ff725923000cfe725923000cfc72592300d6bf4259230004ff7159230004fc71592300d6bc41592302c6dc3159230024fe7059230024fc7059230026be4059230026bc4059230026df3059230026dd3059230004ff7558a3001cfe7558a30004fd7558a3001cfc7558a30004ff7458a300c4fe7458a300c4fc7458a30026ef7258a300ceee5258a30006ed5258a300ceee3258a3008eed3258a30004ff7158a30004fc7158a3008edc3158a30024fe7058a30024fc7058a30026df3058a30026dd3058a30026ee2058a30026ec2058a30004ff7650a30004fd7650a30024fc7650a300c6be6450a30006bd6450a30005df7350a30015dc7350a30004ff759863001cfe7598630004fd759863001cfc75986300c4fe7498630004fd74986300c4fc7498630006df739863000cfe7298630004fd729863000cfc7298630026f67198630006f65198630006f55198630006f74198630006f44198630086f63198630086f53198630024fe7098630026df3098630026dd3098630026f61098630026f41098630004ff755863001cfe7558630004fd755863001cfc7558630004ff7458630006bf7458630004bf74586300c4fe74586300c4fc7458630006bc74586300c4bc7458630004ff725863000cfe725863000cfc7258630026f77158630006f65158630006f55158630006f74158630006f44158630056f63158630056f53158630056dc3158630024fc7058630026f61058630026f41058630004ff7690630024fe7690630004fd76906300c6be6490630006bd64906300c6bc6490630006bf769063030ebe7690630006bd769063030ebc769063030ebf6590630326be659063036ebd659063030ebc6590630316be6290630006bd629063030ebc6290630006be6190630006bd61906302ef9c319063030ebe609063030f9f30906302efbb309063030fb83090630004ff7650630004fd7650630024fc7650630005df7350630015dc73506300c6bf76106302e6be76106300d6bd76106300c6bc76106300d73e75106300d73d75106302e6bf6510630306be6510630366bd65106302e6bc65106302f6be6210630006bd62106302e6bc62106300d7b67110630006be61106302e7b66110630006b66110630006bd61106302e7b56110630006b561106302df9c31106302e7ba70106300d7b970106302e6be60106302e79f30106302dfbb30106302e7b8301063018edf658c63011ede658c63035edd658c63018edc658c63018edf648c630146de648c630006dd648c63018edc648c63013ede628c630006dd628c63018edc628c630015de718c630017d6718c630006de618c63018fd6618c630006d6618c630006dd618c63018fd5618c6300079e418c6300079c418c63018fda708c63018ddd708c630007d9708c630016de608
  | 12 => 0xf7458d21385bc7458d21006bf6458d210e6dc6358d21395f77158d21004ff7558d2101cfe7558d21004fd7558d2101cfc7558d21004ff7458d21006bf7458d21004bf7458d210c4fe7458d210c4fc7458d21006bc7458d210c4bc7458d2113cff7358d21006df7358d21124ff7258d21006ef7258d21394ff7158d21006f77158d210e6dc3158d21004ff7058d21024fc7058d2113dde7618d210e6de7618d2113cde7618d210e75e7518d210e75d7518d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d210079f6418d210069f6418d21006de6418d21006dd6418d21006dc6418d210079c6418d210069c6418d21106df6218d21106df6118d21107d72118d21107cc2118d21107d42118d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006df6350d21016dc6350d210e79c4350d21104fe768c521006bf648c521146bc648c52113edf638c521016de638c521006dd638c521016dc638c521105de768c521006de768c521104de768c52138edf658c52111ede658c52138edd658c52111edc658c521006df648c5210079f648c5210069f648c521146de648c521006dd648c521146dc648c5210079c648c5211469c648c52113edf628c521105de718c52113edf618c5210079e418c52113fd7218c52113fcc218c52113fd4218c52118edc608c521014ff764c52100cfe764c521124fd764c52100cfc764c521005bf744c521385bc744c521006bf644c52112ebc644c521006df634c521016dc634c521005ef724c52100dec724c52113dde760c5210e6de760c52113cde760c5210e75e750c5210e75d750c52137edf650c521116de650c52137edd650c521116dc650c521006df640c5210079f640c5210069f640c52110ede640c521006dd640c52110edc640c5210079c640c52110e9c640c521106df620c52113dde710c5210e7d6710c521106df610c5210079e410c5210079c410c521107d7210c521107cc210c521107d4210c52117edc600c521376ef6588521376ed6588521007cf6388521007cc638852100dee718852100fe6718852100eef618852100fe76188521007ce3188521007cc3188521006df63d8121006dc63d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121014fe73d8121004fd73d8121014fc73d8121006de31d8121006dc31d8121006fb50d8121006f850d812107efa20d81210e5de7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581210ed7c7558121005df73581210e5dc7358121006df6358121006dc6358121006df6318121006dc63181211ceef6218121026fa6018121006f96018121004ff755923001cfe7559230004fd755923001cfc7559230026bf74592300d6be5459230006bd54592302c6bf4359230
  | 13 => 0xe2100cff768c621014fe768c62100cfd768c621016de638c621006dd638c62100dee728c621005ed728c62113edf768c621016de768c621016dd768c62113edc768c6213aedf658c62111ede658c6213aedd658c62111edc658c621006df648c621146de648c621006dd648c621146dc648c62113fce728c621007cd728c62113fce528c6213afcd528c62113ede618c6210079e418c62113fcf218c62113fd7218c62113fd4218c62118ede608c62113fcc208c621394ff764c621005bf744c6213a5bc744c621016df760c6210f6de760c621106dd760c621016dc760c6210f75e750c6210f75d750c62139edf650c621116de650c62139edd650c621116dc650c621006df640c62110ede640c621006dd640c62110edc640c621107ce720c6210f7cd720c621107ce520c62139fcd520c6210f7d6710c621106de610c6210079e410c6210079c410c621107cf210c621107d7210c621107d4210c62117ede600c621107cc200c6210fd7e75d82210057d75d82210f5de7398221005dd7398221006fb6098221004ff755822101cfe7558221004fd755822101cfc7558221004ff7358221014fe7358221014fc735822104eee5258221006ed5258221006de3158221006dc315822104efa20582211ceec2058221026fa6018221006f96018221014fe76d8d210e6de63d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d210c4fe74d8d21004fd74d8d210c4fc74d8d21006df53d8d210e6de53d8d21006dd53d8d210e6dc53d8d21006df43d8d210e6de43d8d210e6dc43d8d2113cff72d8d2113cfd72d8d2113edf32d8d2113edd32d8d2100cfd71d8d210e6df31d8d21024fe70d8d21004fd70d8d210e6df30d8d210e6dc30d8d21105de76d8d21014de76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d210079f64d8d210069f64d8d21006de64d8d21006dc64d8d2113fd721d8d2113fcc21d8d2113fd421d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d2113edf72d8d2113ede72d8d2113edd72d8d2113edc72d8d2113edf52d8d2113ede52d8d2113edd52d8d2113edc52d8d2113edf42d8d2113ede42d8d2113edd42d8d2113edc42d8d2113edf71d8d210e6de71d8d2113edd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d21006df41d8d21006dc41d8d2113edf21d8d2113ede21d8d2113edc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006dc40d8d2113edf20d8d2113ede20d8d2113edd20d8d2113edc20d8d21005b
  | 14 => 0x10f9f42904313df9e42904310079d429043110f9c42904312ddde7190431146de61904312efd6619043110f9f419043110fd7419043110fd4419043117dde7090431005dd709043110f9f409043110f9c40904312ef9f76904312ef9e76904312ef9d76904312ef9c76904313f79f75904313e79e75904313f79d75904313e79c75904312ef9f65904312ef9e65904312ef1e65904312ef9d65904312ef1d65904312ef9c65904310079f72904313df9e72904310079d72904313df9c72904312ef9f62904312ef9e62904312ef9d62904312ef9c62904313e79f52904313df9e52904313e79d52904313df9c52904312dd9e71904312ef9e61904313ee9e61904312ef9661904313e79f51904313e79e51904313e79d51904313e79c51904313df9f21904313df9c21904310079f70904310079e70904310079d70904310079c70904312ef9f60904312ef9e60904312ef9d60904312ef9c60904313e79f50904313e79e50904313e79d50904313e79c50904313df9f20904313df9c20904313c5df7650431146df7650431144df76504313d5df7550431115de75504313d5dd7550431115dc75504313c75e65504313c75d65504312eddf7450431005df7250431105de7250431105dc72504313cddf7150431146de61504313c7d6615043110fd741504310079e415043110f9c415043110fd4415043110f944150431005df705043117ddc70504312df9e76104312df9d76104312df9c76104312df9f65104312df9e65104312df1e65104312df9d65104312df1d65104312df9c65104312df9f62104312df9e62104312df9d62104312df9c62104313bf9f52104313b79e52104313bf9d52104313b79c52104312df9e61104311469e61104312df9661104313bf9f51104313bf9751104313bf9e51104313bf9d51104313bf9c51104313bf9451104313b79f21104313b79721104313b79c21104313b79421104312df9f60104312df9e60104312df9d60104312df9c60104313bf9f50104313bf9e50104313bf9d50104313bf9c50104313b79f20104313b79c20104310f6de63d8e21105f671d8e21004ff75d8e2101cfe75d8e21004fd75d8e2101cfc75d8e210c4fe74d8e21004fd74d8e210c4fc74d8e21124fd73d8e210f6de53d8e21006dd53d8e210f6de43d8e21006ed72d8e2113ede32d8e2113edc32d8e21104fe71d8e21006f671d8e21024fe70d8e21004fd70d8e210f6df30d8e21014ff7658e210f6dc6358e21004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e210c4fe7458e210c4fc7458e21006df7358e21126df3258e21126dd3258e2100cfc7158e210f6dc3158e21004ff7058e21024fc7058e21004ff7650e21004fe7650e21004fd7650e21004fc7650e21006df6350e21016dc6350e210f79c435
  | 15 => 0xf6319131006be6219131006bc62191312debf61191312dfb731191312df9c31191312dfb4311913100cfe76d8931006bf64d8931006bc64d8931126ee62d8931004ff75d893101cfe75d8931004fd75d893101cfc75d89310c4fe74d8931004fd74d89310c4fc74d8931126ee52d8931006ed52d8931126ee32d89310f6ed32d8931014fd71d89310f6dc31d8931126ef21d8931024fe70d8931004fd70d8931126ec20d8931005bf745893112dbc7458931006bf6458931006bc6458931126ec6258931425f77158931004ff7650931004fe7650931004fc7650931006bf64509310c6bc64509312dcfe76905312eebf64905310c6be64905310c6bc64905312ddbe7690531006be76905312dcbe769053141ebf6590531326be659053141ebd6590531326bc6590531006bf6290531316be6290531316bc62905312eebf61905312efb731905312ef9c31905312efb4319053130ebc6090531014fe76505313c4fd7650531014fc7650531005df7350531015dc7350531416df658c53111ede658c531416dd658c53111edc658c531006df648c5310079f648c5310069f648c531146de648c531006dd648c531146dc648c5310079c648c5311469c648c531006df628c53113ede628c53113edc628c531015de718c531017d6718c531016df618c531017d7618c5310079e418c531006bf64d8131006bc64d8131004ff75d813101cfe75d8131004fd75d813101cfc75d81310c4fe74d8131004fd74d81310c4fc74d813100cfe72d8131004fd72d813100cfc72d8131006be41d8131006de31d8131086dc31d8131086fa30d813112dbe7498131005bd7498131006bf6498131006bc6498131006fb60981310057f75581311357c7558131005bf745813112dbc7458131006bf6458131006bc6458131005ef7258131125ec7258131006bf6418131006bc641813118edf6318131026fa6018131006f960181313fddf7650831015de76508313fddd7650831015dc765083140ddf7550831115de755083140ddd7550831115dc75508313ff5e65508313ff5d6550831105df74508313ff9e64508313ff9d645083110f9e54508314079d5450831105df7250831107ce62508313ffcd625083110fcf42508311079e42508311079c4250831107cc4250831005df7150831007d77150831005d77150831005dc7150831007d47150831005d4715083113ede61508313ffd6615083110f9c4150831005df705083117ddc705083110f9f40508312eddf7690431015de76904312eddd7690431015dc76904313f5df7590431115de75904313f5dd7590431115dc75904312ef5e65904312ef5d65904313c5dd74904312ef9e64904312ef9d64904313e79f549043110f9e54904313e79d549043110f9c5490431105de7290431005dd7290431105dc7290431
  | 16 => 0x8231145de749823118f9e74982311459e7498231005dd749823118f9d74982310059d749823118ddc749823113dde7298231005dd729823118ddc729823117ede619823106fd661982310079e419823118edf6098231007db6098231005df75582310075f75582310055f755823111dde7558231005dd755823111ddc75582310075c755823111d5c7558231006df6558231006dd6558231005df7458231145de7458231145dc7458231006df6458231006dd6458231005df725823113dde725823113ddc7258231006df6258231006dd6258231056de6158231057d661582310079e4158231007db605823118ede605823118ddf751823111dde7518231005dd751823118ddc7518231145de7418231005dd741823118ddc741823113dde7218231005dd721823118ddc721823118fd67118231037d661182310079e411823118dde701823118edf601823118fda601823118edd6018231007d960182310c4fe76d913112ebe64d9131004ff75d913101cfe75d9131004fd75d913101cfc75d9131006bf54d913112ebe54d9131006bd54d913112ebc54d91312ecff73d91312ecfd73d91312eebf43d91312eebd43d913100cfe72d9131004fd72d913100cfc72d913112ebf42d9131006be42d913112ebc42d9131014fd71d913112ebf41d91312eedc31d9131024fe70d9131004fd70d913112ebf40d913112ebc40d91312ddbe76d91310c4be76d9131006bf65d9131006be65d9131006bd65d9131006bc65d9131006be62d9131006bc62d91312efb731d91312ef9c31d91312efb431d9131006bf75d9131006be75d9131006bd75d9131006bc75d91312eebf73d91312eebe73d91312eebd73d91312eebc73d91312eebf53d91312eebe53d91312eebd53d91312eebc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006be52d9131006bd52d9131006bc52d91312eebf32d91312eebe32d91312eebd32d91312eebc32d91312eebf71d913112ebe71d91312eebd71d9131006bf51d9131006be51d9131006bd51d9131006bc51d91312eebf31d91312eebe31d91312eebc31d91312ee9c31d9131006bf21d9131006bc21d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d91312eebf30d91312eebe30d91312eebd30d91312eebc30d9131006bf20d9131006bc20d913112ebc64591313cdf77159131004ff755913101cfe7559131004fd755913101cfc75591313c4ff7359131006df7359131004ff725913100cfe725913100cfc72591313ccff7159131006f771591313c6dc3159131004ff7059131024fc70591312edbe761913112ebe76191312ecbe7619131006bf6519131006be6519131006bd6519131006bc65191312deb
  | 17 => 0x5dd70d92311479f40d9231145df7659231005df755923111dde7559231005dd755923111ddc75592310079f6459231146de6459231146dc64592311479c64592311479e54592310079d5459231005df725923113dde725923113ddc7259231015dc71592313c6de61592313c7d661592311479c4159231005df705923118ddc7059231005df75d8a3111dde75d8a31005dd75d8a3111ddc75d8a31006df65d8a31006dd65d8a31145de74d8a31005dd74d8a31145dc74d8a31006df64d8a31006dd64d8a3113ddd72d8a3113ede62d8a3113fce62d8a3113ece62d8a3113edc62d8a31005de71d8a31007d671d8a31005d671d8a310f7d661d8a3118dde70d8a31005dd70d8a3113ddf7658a31005df7558a3111dde7558a31005dd7558a3111ddc7558a31006df6558a31006dd6558a31005df7458a31145de7458a31145dc7458a31006df6458a31006dd6458a31007cf6258a3113ede6258a3113edc6258a3113fcc6258a31015dc7158a310e6de6158a310e7d66158a3113fcc2158a31005df7058a3118ddc7058a31005df7650a31005de7650a31005dd7650a31005dc7650a31445df7550a3111dde7550a31445dd7550a3111ddc7550a3113ddf7450a310079f6450a311479c6450a311479e5450a3143f9d5450a3113ddf7250a31147cf4250a3113f9e4250a3113f9c4250a3113fcc4250a31005df7150a31005dc7150a31106de6150a311479c4150a31005df7050a3118ddc7050a311479f4050a31015df7690631145de7690631015dd7690631145dc7690631435df759063111dde7590631435dd759063111ddc75906311479e64906310079d64906313ef9f54906311479e54906313ef9d54906311479c549063113dde7290631005dd729063113ddc72906311479f429063142f9e42906310079d42906311479c4290631145de71906311479f4190631147d74190631147d4419063118dde7090631005dd70906311479f40906311479c40906311479e76906310079d76906310079c76906313ef9f65906313ef9e65906313ef9d65906313ef9c65906310079f629063142f9e62906310079d629063142f9c62906313ef9f529063142f9e52906313ef9d529063142f9c52906313ef9f51906313ef9e51906313ef9d51906313ef9c519063142f9f219063142f9c21906313ef9f50906313ef9e50906313ef9d50906313ef9c509063142f9f209063142f9c2090631005df75d823111dde75d8231005dd75d823111ddc75d8231006df65d8231006dd65d8231145de74d8231005dd74d8231145dc74d8231006df64d8231006dd64d823113dde72d8231005dd72d823113ddc72d8231006df62d8231006dd62d8231007d671d8231087d661d82310079e41d8231005dd769823118ddf759823111dde7598231005dd759823118ddc759
  | 18 => 0xd70d92312eedf30d92310c4ff7659231146bc6459231015dc73592311479f4359231004ff755923101cfe7559231004fd755923101cfc7559231006bf7459231146be5459231006bd54592313c6bf4359231146df43592313c6bd43592313c6dc4359231004ff725923100cfe725923100cfc72592313c6df3259231014fc7159231146bc4159231004ff7059231024fc70592313c6df3059231145df7650e310c6df7650e310c4df7650e31465df7550e3111dde7550e31465dd7550e3111ddc7550e31015df7450e310179f7450e310c6de6450e311479e6450e310c69e6450e310079d6450e310c6dc6450e31005df7250e3113dde7250e3113ddc7250e311479f4250e31005df7150e31007d77150e31007d47150e31016de6150e31017d66150e311479c4150e31005df7050e3118ddc7050e311479f4050e3113eee62d8a3145df671d8a3100cff7658a31015dc7358a3113eec6258a3113fce3258a31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a310c4fe7458a310c4fc7458a310e6de5358a31006dd5358a310e6de4358a31006dd4358a3113ede3258a3113eee3258a310e6ed3258a3113edc3258a31014fc7158a3113eec2158a31004ff7058a31024fc7058a310e6df3058a31004ff7650a31004fd7650a31004fc7650a310c6bc6450a31005df7350a31015de7350a31015dc7350a311479f4350a310079d4350a3113ddf764ca3100edf764ca3100cdf764ca31455df754ca3111dde754ca31455dd754ca3111ddc754ca3144edf654ca3144edd654ca31005df744ca31145de744ca31005dd744ca31145dc744ca31006df644ca31006dd644ca31015df724ca31017cf724ca3100ede624ca3113fce624ca3100ece624ca31007cd624ca3100edc624ca31005df714ca31007d7714ca31007d4714ca31016de614ca31017d6614ca31005df704ca3118ddc704ca310c4fe7690631014fd7690631015de7390631005dd73906312ef9e43906310079d43906312ef9c4390631145be7498231005bd7498231006fb60982310057f755823111d7c7558231004ff75582310067f75582310047f755823101cfe7558231004fd755823101cfc75582310067c755823101c7c7558231004ff74582310c4fe74582310c4fc7458231056de5358231006dd5358231056de4358231006dd4358231004ff725823100cfe725823100cfc7258231056df3258231006dd3258231056fa305823118edc3058231026fa6018231006f96018231005df75d923111dde75d9231005dd75d923111ddc75d9231145dd74d9231146de64d92311479e64d92311469e64d9231146dc64d923113dde72d9231005dd72d923113ddc72d92311479f42d9231005de71d9231007d671d9231005d671d92312efd661d923118dde70d9231
  | 19 => 0x9132004fd75d913201cfc75d913215cfd74d913214ebe54d9132006bd54d913200cff73d913200cfd73d9132486bf43d9132486bd43d9132014fd72d913248ebf42d9132004fe71d9132004fd71d913214ebc41d9132486dc31d9132024fe70d9132004fd70d913214ebc40d9132486df30d91320c4ff765913214ebc6459132475df735913247def7259132005f77159132005f47159132004ff755913201cfe7559132004fd755913201cfc7559132474ff7359132006df735913215cff7259132006ef7259132004ff7159132006f77159132004f77159132004fc7159132006f47159132004f471591323fedc3159132004ff7059132024fc70591323fedf305913200ddc7650d320c6dc7650d3200cdc7650d3246ddf7550d3246ddd7550d32015df7450d320179f7450d320079f6450d320c6de6450d320c6dc6450d3214f9c6450d320c69c6450d32007cf7250d3200dde7250d3200ddc7250d3215fcc7250d32016df6250d32017cf6250d3215f9f4250d3215f9d4250d32005dc7150d3214f9c4150d32005df7050d3214f9f4050d3214dbe74d8532005bd74d8532004ff75d853201cfe75d8532004fd75d853201cfc75d85320c4fe74d8532006be74d85320c4be74d8532004fd74d8532006bd74d8532004bd74d85320c4fc74d853200cfd73d8532396dd73d8532014fd72d8532006f651d8532006f551d8532006f741d8532006f441d8532426f631d8532426dc31d8532396f621d8532024fe70d8532004fd70d8532006f76198532005bf745853214dbc7458532006f56118532004ff751853201cfe7518532004fd751853201cfc75185320c4fe7418532004fd74185320c4fc7418532106df731853200cfd731853245ede5318532006dd531853245ede4318532006dd4318532014fd7218532106de3218532106dc3218532006f65118532006f55118532006f74118532006f4411853245ef53118532106dc3118532106f52118532024fe7018532004fd701853245edf3018532024fe76d8132004ff75d813201cfe75d8132004fd75d813201cfc75d81320c4fe74d8132004fd74d81320c4fc74d813200cfd73d813233ede53d8132006dd53d813233ede43d8132006dd43d8132014fd72d8132004fe71d8132004fd71d813233edc31d813233efa30d8132286fa20d8132006fb60981320057f75581321557c7558132005bf745813214dbc7458132005f77158132005f4715813214dbe7418132005bd7418132026fa6018132006f96018132146be64d92312ef9e43d92312ef9c43d92312ddf671d9231004ff75d923101cfe75d9231004fd75d923101cfc75d92312eebe43d92312eedc43d92312ee9c43d923100cfe72d9231004fd72d923100cfc72d92312eedf32d92312dcfe71d9231006f671d9231024fe70d9231004f
  | 20 => 0x800002600700000740000000018008000004003802400400f00d804401800a000801c01000000000000160010000008032019001803406c000000800000200100100040000040008000000004005000400600b00d8000000005017800800200400100000000020000000006003001803c002001002000800c002000800800a000008800000e00500000940020060010028004004000801000c00100080140060020080010000001000000001a00100100040000010020008006003000000801c01300780040140000000014006005000805000200a0060044018004001000400200400600080120000008004000004003800c00c0090050000004000002000c002003002800c0060010028000000003000000c004001000801c00c000000000800000500380000000040010034002001000000c006002000800000c0000010004008001004800400800500000000020060000004018000000000804000a0000000006027006801400a00800000000000040000010000005001801400e00d00300000040040050024006004000001800e001003803400201900cfe76d894347f9c43d894315eee62d8943004ff75d894301cfe75d8943004fd75d894301cfc75d89430c4fd73d894315eee32d8943004fe71d8943004fd71d894347edc31d8943024fe70d8943004fd70d894347edf30d89433ff9c435894315eec6258943005f77158943005f471589433cf9c43d8543004ff75d854301cfe75d8543004fd75d854301cfc75d85430c4fd73d854349edd73d854300cfe72d8543004fd72d854300cfc72d8543006f751d8543006f451d85433cef631d85433cedc31d8543006f721d8543006f421d8543024fe70d8543004fd70d85432ef9c4398543006f761985433c79c43585431657e75185430057d75185432df9c4318543006f56118543004ff751854301cfe75185430067e751854301c7e7518543004fd75185430067d75185430047d751854301cfc751854310edf73185430c4fd73185432debe43185432dedc43185432de9c431854300cfe7218543004fd721854300cfc72185432dedf3218543006f75118543006f451185432def531185432dedc3118543006f72118543006f42118543024fe7018543004fd70185432dedf3018543024fe76d81431657e75d81430057d75d814334f9c43d8143004ff75d814301cfe75d81430067e75d814301c7e75d8143004fd75d81430067d75d81430047d75d814301cfc75d81430c4fd73d814300cfe72d8143004fd72d814300cfc72d814334edf32d8143004fe71d8143004fd71d814334edc31d814334efa30d81433579c4398143005f67198143005f57198143006fb60981432c79c43581434979c4318143026fa6018143006f960181430c4fe76d913214ebe64d9132004ff75d913201cfe75d
  | 21 => 0x800500000040020000018004000009000001c000000001801001c000000001c0000010068000010002001800800000c000004002800c0058010014000000001400400200200080060010010000002004006000c00000a00000180040010018000004005004800400200000000100020020048000004000001000c012000000001c00000d0010000002006002000400200b001800000200400100000020080008008000001003801800c005000800000000400000100000080008000016002001800000602f000002400000000d800400a002006800c002003000000000000000000000000000008008006002001000000000f003801000c00b001000005200000000040000000000000000005000001000000000000040000010000004004000003801400400000100000040060000030000004000800c006003002800800000300e000400002700000000040020000000008002001000001e00000400000120070048010006002000805000200e006800400c002000001800a000001001400000200000000000050038000002007008803c010002005000401c000001800400a00b000800400800b003001400400a000000c0040000010040002012007000c0000020010004000001000000400600c0078000006002001001400000301900180060020008000002004000000402a0020000020002000007000000000200080000040020050064006001001000403200300180040060010030000002001001002800400000100500040110000008000001000004400000100080340000020010008044007000801c0000000058080000004001801400400200000180040010008014000001000000c000001001000001600000480000160010038000000000000800c012001000000002a0020068000002001001000c00000c006800000a000005800800401400180340040010010008014001004800402a001002800002e0020000020002000002000401c0000000004000001005800400000100000340020000000000016004005000000000e004800400400100080200000030008040002000000800c00a004001000000e006000000800000600000000060020020008002019000000000a000003800000000600180340040020000008000000000801400400001e8000002000002800000800a000800001000b001000401e0000008040000000000000002a0000028000006004001000800800100100040140000000000000016000800000c000001801c000000010000402800100200040060150018008000001000800000000300000000000050008000000004009800c000005000001c00000300000140000000008000016003000805c00201000280000000060010024008019000800400600a001000800400d0020020006010000000c004000000
  | 22 => 0x81b40000000000412c0000004e28a9d6020006ea00000000003234c6000144684b000138400000045708880000c096903f800000021927dcc700000002eb4ae82df5fd2548000000226305804b00014700000000000001c1111a19127a91b4aa2ab7641c4e4e040000000000ed1a0041805c94a83514f8c0000000000003596f841f80002844000000068262b1ea7573b3ac80859cf90fb9dd85504f863c649934727a5a735906ce2850ba4000f8c8f86a48000d2a0002100000000000428a7f00005ddcca91280ba47400000003c200000027ed04a1ce8000b0949400000000002df6fe5969b9053f18d6ba1b54c540006bb353228db8c002c00400f000000000000000000000000000018000004001001000c008000003803800c0000000008014001000802000200000300380000010008048006001000001002400000800300000070078138002000001800000e001002800001800600000140000020018000004003003001800c00100400240000090010000000007000800400600000400080000000050004000000000000000000e00000100220010018010000002000000400000100300040040030058010056006000000c01400000000000a600100880340020020028000002008000003401c00000400e8002003002000000200e000000000c008003000000e000013001000e01e001800000200100080000000070090004002003000000c00001b00a00140180040000034002027001800000c00f000003c0420000000004022000000000005c0000000024002002001001000000000080000060130010008000000004000800a002000000000e00900380180080010000000006003000000001c005000001400000000280040020020038024004000000000000a0020008000004006000800800000e0020014018000000001000400300300000120000008008000006000800400a000000800000e0070018054000003000000805800100a000000000100080400180080030008002001001800000000d000000c01600100780000060000008010002002000000400200000000000060010018000010002000000400a0040000050000006008801400c00500180000020000018014000008001804c00600100000000000020038034012002001001800000100080000000020000034000002000800000a0030030000000001002800c00a00900080600060040000000000000001002000a00400000040000050008008000005000003c0020000038040022000000800c0000020040010000000000800c01400200080540140050000014006006000800c00000e0000008002001000009c00001d003002c00800000400100040000098000004000001000000000b00000040000070000014006000000000c0000040028000010001003000400
  | 23 => 0xee00053500019b44ea0000001b5c00048d51e0890000d782bad2bd3ac2d4eb508ba07c43b0000e559608c40001e052020ad640055030a0000002bdd18c1d5e4882400004fa11617e400000f5941d7cce890437ce848f1244c8001e88db423943a31cc0003d1208c000d206544bba3dcff27ce527a114fda110bfc0ee00000000000001030000154c2e496d0000001ea40000000110959a0a119000047fa449962fa970922e7644d0b340af69120f6a080000a1d000332800040f452a900000d40000000000000040434200000001b8a4140004260000000000b694b9000062800000000013b44ed0001dbd30fafa0a9663cb900003a6272800000006ea7d4f4acb2000000156443bb2235c56a01a84e08b5576c000280923e54e0fb0000160e2c0000000b201fa4701109bb8466000000000000000000000000008e519386d42106d65950500b1c000000000000029c1ef80015b81135eca734afe61d25098b2102498800356c35fb7600021e0c402c31df33c894620127f12480005912489a16ae21480001c88e50000431046c091be40001bdc00004ca90807816c00037240004fe6f04b425840000000002ad1aff0005bf0b6cd5c00068c9ba000000000000006664860f02484000581394af7c000cef12daec410ec04e9bf4a4fb0cf524b2fac00000000005e12160005fe80000000002610000dde00006c8c2076ab5269a183d0b2ca300000e4000bd052b9e68000ce900002680000003059c8400000000020098940000001eac0007fb0c9a27024900029e13682c471d0001de140e0000000e250cc2ce000000000067612a1e800000003ad6810fb202e0000000000815839af686cc7a662229909ee0000000000000000000293029d7ff00027955d800056b00000000003cee754ea458040780540000004398001228000688a72b1fc000553800186c5fb00019eca923c019c26a2000bd452700017ac00400000000000000000fbd676a0c0000001524d6280000000000006c112e80004b7d0defa97a480d86fc82a60e4005401345aa4d9e3c79e6f378c3d28629656aed532eb019102a26d3cf0de5686885652b2a68a214c64a9d6c7cc1a719a98b573ea353f384c113e9814a98c3c00096b117e970eb078249b939c00025c0c300010e2000519210200000061c0000fc84bd80015f0000287096df4c49a9940002be550a0000001958000000128800000064c000000000041c033400000008e0000add55aaa436ca8ec7680dc5870f396910000003399290459000075000000000015c000076044580008ba046000000000057508c4000b08a684c207b830fb331acc0014f8c195099d296f2d993108b903a40e6000362cab4cc0000071535d6a30000001692000000023000000000000015cac8a1ed8000000bb343f8b2afde8cb44380011ec28
  | 24 => 0xc991600046f000058561565c29140001bb579936f88e30c2fb0f10392000000229c2e637c00000000002febc533eca48bfe5f7ae0af5a8da0872bf93a033b000000098b00000025452980001b2ac50fff1a1472000195e000500997840300000000015bc000309800014246138b908800021380034a0000d9100000000000003118000afc0000000000310864c31400195822a2048000e0f09847258bc0000000d74000000444000000000000017a8bca0b8ac657d96fd03a3e900016cc6646ba00033e08c643651f02c93436ed00000018a83f3260b6d2254a2b34b88f416200000000000000bc4ae90f7450b3564f940ce86325b3f80000001b02da2228530c98047989968ec55067d68c0002700bf81e0f501961adc00045017742d1f7d5ba9fd3b280000000004be31b085ec328ce00013e966a1f285f200000017ac00000067239000000002af64d800071800034c04d583c0005c3e0e98e2b881716a3d1066dc34d0c712960000000000000294000135c000d1420f1fa8000d5000000000001051124b928107cd1a602089fb2461b9074a2cc0005ba0f2600075458816e904c000245000121a37558885d0e1e4c466124b80006644d227e50bc00011e000124400000016840000000001402834d3d000201870e99d397ab058f44dc4dc367121092d00013bc0aacc903f80000000005b600004c200063ee1da0001b90000000f0c00000000000000003417480e26000549878d8440000000826e4a64800035b8d840004928b679060f1800265c46276a3e213b068a00000000000001aa00001b4d00000000363400000037a000000000000033700000003dd8000000ba4b0b1260ea60f90fd02f41c5cee0c00000bb755f0000b1c0006522a52962cf923700000000000001fcc00137249900000007566834a532f83b614f000185c9543832cc80005578a400000002a048ca7ce3f4000000000000000000000031b80008b700000000000003060344000b7edbe2fc971512c65701d69b000060da7b46840000000000ad0b8900000000002b90000000a04da28e7c0009a599a12c725d7b61a0a3380001c4d6030218002470003562f098ce9e362da4fd45ea1dcb7176aca0d170c92dc58b23c70002608a82c766b90000aa6c7400000000000000911a300001430000a080000000000001920c1427fb14e7325fe49d27a117c8fb05fe5d1724916d7fb1682e027b00000006b5c5f000000000001d65cc00000073f60980000000005348b44000000614000000000061fac6400000000020dc2d60001970ae8d149dd0000000055892000314005d4e25198000000000149201cfea00000017c200000058f800000070539c00013c34bf2d7294489e03b06614cc6e009715f8e014d856de632c2c4a439763913657700be69234b98fc0000ee35
  | 25 => 0x185200002080009a6547672b2cc7e310cbb90ec901d37e4df97d0ec4a6c84b07341d449430405a7a7f77c041b4e00540003cbad7c11ab785f8030d65e3cc316089f77a0000002f55020223353963030200053faee80004ab0000ffc00000000036a981491532cb20a0004ee00032cf9564892c803b8d700711b534610b0d4d6bdb584d6a00022800017549f4345908d4c2bbb5b80b700000940001765780000000143543f24e2b50ec163a08a87d00000001b84682d110a4c7c647c0015c400000000016aa80e0000000c5cd4f212166e2067e9494090c3cc8135e7242a28400005161800000000000000e9656d0000000b121a3c79aae16e622d2da8fb4fee3af21a972823e0004abd614d0c28c1c0800000000013017ad642acb06380a5338b5438a19389ac0001b6874d050b260f100011a80000002a60652000000000172c55c00000010288f122f000040a00000289b000000000025ec00000000014f4000000006b5bc000a5a603a1b88063fe61703c27a0bd317d00ad35e3565d834c000083bc362bd9566000114954e91e97e29a131d2a00000001d2571c5402cc2829b2e5f7152d5b02e25954fd286c0003a33ea16350370000d4800141a0000000000000b25467a94c000430000051c8c80af00000006b45bd8ee800000052000000017080002f1800000089300006780005164531b899480ef58780393f53411ae98285021fe2058a5d69845b386687db3a7952d40000bfa5dc97c205f63811c093850b3d800041f189c0d8a6a2eda8e4140ac700000014b6cbd1c7228466e8d80795d540860006500000000000550ad98000000170800000054d00021590a64762b5b3c109e4a080002b837c0006c828dce15a5200026400cec2b13f26f507f00018d2eae1763443792344d260001649454000b770000000bf8000389341d61b38f00036ac00041961004907825b91eea11004e10d49ca0f68b016a69916f44c40a3800300552c481564000000071a635b06103e2f18084994672000314000131300000000000000006699a24000000000000126a61d800307c0006714ee0b81892a1013c80b0000296000000165f0002228000000a764202090bc200000006980745e65fda0d989a724c4b85f4000c090000b00ab0a364250000cba00000009d02fc5d73ce91361c6a176b100010c100000032500000000a50000c8a0006428000936cd2000020a15683817b8265b5aa6f443112d2cc1a33fa147908c81c9808a8409e0690dd150902c0004560000000000295800035a0000001de801254c000043ef1680bc5440008fa000000096800000000000007d058355f8000000b8615b00009d9000631b3300000006c009d94840006b996c56bc20e02dace14fc12b16d000013c0003659b606de5e250498f40000002870001af85a900028d01d00
  | 26 => 0xc8859a074e00011158a8000282b6e43340000d0000622c0000009670002ce44a9c6a4219bf116a0000000d0cf827b409a40004c8b5a80000000000000000000000b4f62f318157266026300003148eb0000000000c640000a740005af17a0000935478000158400000025c80000002e58001eb00000000a5b33d4c6bec617800000000041e065d05400000000014f20400f5000138400000036b9170a8909f2720ee6636000000000026b00000012de0001240af40006a200000000002a7c8f8001af95cc00000000004ff80001d400071139eb0d69c6a870001970b157d251880600009c60c183600001b2064af3483adb641640000e83c26622b6c000502e3800000001b602980ccd100001f9081c0c0d6b359800113c226a6d80000000000001c700000002c10001a2400031c8e694facdb1940000000000000049e000995ab189b921b00000000017300020002245822651c8d03859187a15e40ff6dec04c0001b7cf5c97153016588aea2a00005e40003c62ceeae9b0252c0002bac0000e460300015403c800033d87b446c0000000e5870820fa53c000d8369ba3287c2a4b120b07416e7350000001b3e7776938000562db3d98b00cc6600000034380001e54ad2e7440c08f9de94f800081080001501db2d7000235c0000004d480004ae0005e29cd0000000000106051643f00000000000000948cac00013600000007e8000000000000000045a04742c7bf45c1000184aa06292857db446a808f347670c5a600004c400032f311361f7e2bcf3b5ab9821754f2bb6f044e2cfe04e1ec83877b64500349b68c69397346c97f4343158fe04bcb9b4e5f069acabe756902320180794901b2990877e6848dad37c34763a882c9aa0003c8aab836e0e90000001b617fd0002f100000df3f9800006a000216d2215aaa9403d87440680280530000b3eb130bd400161254480023b5742210000348670467e2c5d57400080350d4de000000061d800000022f00012115043fa170c0000400d40000ab80005ea00000005e90005be94140002aa00036480000006d02c354ee00000011354da000366a6c92130001ba00007f200000023b199600000004980000005d7b5382ad0000001ecda0800042b9af4918c8d489ac0d1beb8d22314e166400020ad8dc0002f36ba8bb20004feab0330567c000000000000018b000092c1500001f18000136d4135294068b8af557e16ef728ac45018cf49f256427b0aac0d67004448dec04c46236fc000000000072800170e0000002cac00000000000000000000c380000000004ae2508e60123083084b162000000000048ab9000035da7b80000608000a20000000184e93c0892329c0d71e00000036e40008ba00000019680000000000388b024bc16824058985e881e60000000e8c7f20000004088c756da0000000
  | 27 => 0xcb2c2d834933d0b653c42142e035b1256258215dd708dc433079a4388922b22f91750d48b912aab624e4b50810fb1018a61ae557a8590424256290ad509cd5950e5805a008495ad0cf123ad10618c5901971c60fca9e847624a303879ac4835e502a17cbe321663b8562da2310217000465daee4ff923a00081e80023fc0000000520000000000395b1200000001a59c3ae8e8270001c305cc20c0002798fc400041a187c53699d8be26649d70f8000004400047700016f8e6c000000082000017560ba4f8000c7e800141c00080ce819b4c000000000000000001b0000000000a3827d40000004f204863f129200039187602a96341422d70cc2be135332ec000072156800000070a6589ec533ca5f241a07730c00000004cf42a4c93c99fc44a6cfc30483fd68accd00000006be299000000125478e00023c00000002ef40000000000dccd6c000ae12e5800097a000375914816000000000009d42ff9db980c144030399267c00000000015e2f2c0002c400000001a00c10a67018195242903e94e32a28d000000056680012f8000cde65d0000000c00269243e5786b208ab4c46800002dc00006b200009d8868d0900040f0000000497000155930000010480000000001fe83d0000000000000196c000186800000000055d6e1200000045e056c1848a944223580002e76741ba400002f0f9b4acd3a5e76013205b300003bab23a9be00000034945fe5e01b18000000b808000000bca0000000000de6baaa15aedc000bde0000000cd000000021070360000002c588e44390a8a6733612dd000000163c0004938000000000000000000000000032b50fa00047d13787160001d40cfc0000003623098000000000321d06a00009786d007e39800025b051200036a5be53b236e00000018678dd354a0fc0006654442f9800000000000000000001c2afa4d2800040b97740000003ee80010901fd4c1800000000023f8000cd39895444000ea01b11e540483aca9d4d268808ea00048f16b00003d60002a200004a060aac618cc2730002778000887ce28e9c3e29635970068d1edba09682fd4289870ef058a31e0004d8086cd8e3aa5280d34b0e00009e8000000c342b3aff0dbc6870001c2400000043bd848e0e009d408001a9056f8a20bc40008946192a7d3be0910000001444b5813c1aadafe72d2930000faa00028797a1562b1a03b80009a37a41d2a1a833671039bb3551b6107477afe10140e701680000000000000000b9d8d34380001b428c81e50000000000448000000025d35c80000005760000001a7432106b8001230000000000186e5502e21e6c45c40659d14c10e75ad23f00017dc00000000f07240004d56ded4e897f6c72abe74487761180006686bc13909a1862b2080018f9af40cd5b185f79e2af05e600019690ecaadae2d2b2
  | 28 => 0xaa900000000d6c1991aa80004d40000001d580000000000000000000000000008ea6d8a70000000000000000000000027980017c0a494673380ff80000002e89ae000017e890957cc2431480005e0abd20b00015061ac371aca43433fb80013a0371d864fb0a554c4a8d32f994428a000190361a1d80490432b9000078a9f4481000076d5331573b0a54400014d80004b72db07d88e61842ce40007c474bcb53613602b9e1dd27a82683f62f780003b405f11453f00000004cfeaa8d9ca460000000c8ebcb5983350313d84622942cf8a21c5652558e3c632082311ea7e23f0001b147f62fd8000000b484cd30c862488029e5841878212db707b240862273b59f846111e6b10000ff100a20303e9efd0a80f06550c28000000431a9cc7b21563bfae0ed325ec3d397660006c005bc29c0000005d5984a0ca0000001840328bb40f38000000000000068a0000002c534994d60000f2c000000bc32989f98d825f10ec9092fd644700300010fcbbf09f4ce8ce08192e889314aa00054c80016089a54740000598ace6858e580000000000001253d1f00014b804a000481aea45342000a99c1961f51f090c0000000000001d780005efb4700015a68691d6aba92ec9f100012c063100051200008d637f00000017b066e04fa79000000000010159c2000000174cae45c555400005ec0000001d38f3e5d810c922f9427aa43cae901ee3b30dd4000fb67680cfd6750ca04a1678d191000004be8d388142bb20da17037a00051d0000f6a00038db67329ca1e4aa079359a67309434da2247336d6ea88d7e7d9dd4359919200063c00019f41fb80000008270002601aed3540006bf1208d5a78d000278001100000030e80005ba800200486e9ef32c000122b1e400019b00009cd8000c3a0003f500004a69b9a9518286610840002a7000024b0001a5442c9e27bc000265e0000004db9a340009a20000f4600000000025040006239ec241cf1850961500018ae1ef0b6862e752d5868eaa2922200061ab2582b4d421859ef42640006cde2381b4305dee80000009624d8814076c3cd003ac90b9cad73336ef1b607980e8151b01a0004b980000001c300000000007791aa0ba8d425392704001ace0005831fb8000cf400006cc00000000000012ae59e0002d04878d79087895536800000007d40000000002dd5252b953b7283c8de5124849bfd3d2c5d16f2d74a0812e079c69547e0004a2f58d67abca545a0bd7b89600a8590d818316620acd854c1d493ea8b45660ac4280228c940003be818600000019c51a18c43f7ed2b23c00000066385e8dfa000000097c500527000024db4c00000000000001a20620000000000000000000000065e103176acd70000564e900000000001aa80006c392b00000005d900007201f017db3ac00006a3c4c6c7a547dc008
  | 29 => 0xe2c2974600000000000a25a51c20000000000000000000000047180013ae7840000fdc00000000032682b50002e380011763c565ba44178ead800000000003774ea40000002d3e7f85ec032000339dac0b6000049c0bf80000b6edc0000c2880451711e4742c124bd1e1c79f90f52b1a78b6e7ba38952b4ad22c621407123c11c200b9d3524f0de4ab6ef80009a600000000000000002e000000005790001b1e0005b2b628e1ad8583098716b211625671ef9d40001e1b0f964e0006d20000e3e52835f337c609d15db0274497087c1d318af486ae03ef1a158c261b69a80000000001eb90a90a1c0b000119851a00008a0e442b048e05ab68e81a00046620f4b9e79450405340004425c8cc4baaa0001dc8d4c2594955cd2b3c0000002e1b23945216017126e95783136ad1a092aa77003f00016a6000513a208000af42910000faeb642aecbb993ca650fa1fb090007aaaf18eccd64104cc113956a816800226c0005ee41269219724cb1dfb321064c1c0000e34dd8d014001274eb493d38a800038e00010f1bc58f9489afc1894be02342b759985cad5e0dfa6340a48b02de0000fa2014099b3dc00074000014b40008410002ac014a8b3000267a0000000002d20000759800000000081f9e480015524b36a22a1084b00016a104800000058603f06d800000017fd18e0620000001a8e2dbccb400116c00053ac0000000572aa1045a468766738000000186cd18000f920000aa8c6000000000005c705ba4741480003f800000000000004b60000000000c081a529d48d2701000000000021524981bc00000037d0f4200040265a8000000d690001e70acc5d00002bc45d2943e5fb4666a0045243a2133e08868000aa42ce9315cb8000000000000000095dafd00026acd6e54518aa8380000000000d88e88ca900012b80000002fd25611f21520701edc7cf919000000121800046180000000000000b28000000000083c9904c31f600000000003fb20b4e5500000025e4948ac0150203e0000000002130000bed0000000570a9700035a712c9a280011ed3984d460789bc00000019940012583060001734a3865a53db4b6f20a720ade28ca2e5a75fb2c006c55b229d52ec00011769981201082d057400000b22ec39d000d3b07c336a00000000000000248b033b14dd8849576616e16000094aad128a077d6d441715801c0000da85a8b654a360000000000b2e000000033c0004b521624cc00023860200000000002d5000194e6050001390000b8a4874001aa264d0f0d1f35461d6e89f0b5a94b3c5a100006005f7d109db0f7cc433210d3c0480006d980000000000c625100007a334e3586315c57b9e00002f100000023a8e7cb37436800103400000000000007e85ce186a0006356a6279c00000045f8254ecc3cb31e3218c929a015a00001e
  | 30 => 0xc469b0001104dba4fcdb1341935a4b2210b1bc0704ca1f230f0e3bba661096883ae58f46aa2f40005c6189264d28c08564918180003bb09d21ec6b80002eab44c3a100024e0a4d9120000fdb33993ac27218a57c0001af000000168c1ab0519f2d89899b082564c09c8c20d24dd9505ba7800079e00053b1e909dcc740002c3000096800044d00013100000000a8906624700000000002be0000000a3200000018c40000000000a180001d544aafd4000a18000000000000000019f530aa5d52680002004bc1b0c5d8000415196993da7e0003939564fac00022d273d6ac84700027c9ad00000003298000b5b28c1f5afc031f229a7b8cd204d3f813868aacdd03b0ba1a962c1000262d18057829b91e898d6d6ace000139281c504cf5473649f2549e011442670000000b2400041c800115a4e000000004806f5364000000000008500000009430000000000000000316006e0003700000cc41b08000fa8000b075382490ade5da00019dcba4b40000298e0000000af15e6f0685b3a29dd06f4ada40480016f400032b80000008641560001944d7d000000000000000034e4000ac200035140000000000000194c330000000000a13c7900016d600050f4a3c000bac0000000fb40000000828f0a4d00001c8209d0004d700001d691f8c4599d5b24c533e00000000005b90000d86ac500000000008ee00000018b80000ae25d4c730005d28000cc6b834550dcc2401904990fb843a00000000000002831f588d400012138c8000000a865ff80000000000002b2460812b80000010ded1619f276c000c5980002073c210228505bd75cc511a900005e40001010d901e400069f57b40009c7000000000000000000000004e6000000077828a025800000084d0000bf258acec4f9922d43492300000005de0002bc941fa7853a0002710f980000fd45198720000002b40fc60ce0001900000aa600000000000004f1d4220140001280000a46000000096581a91c00000013fc739000000087a000000000000000035000000007c75209b3c3829b185661d526c0103b09e65322324000000000070b0c2c8d80000006c9b574000d418602d28e1c2901870b112ca0002f98000dca000497afe49e01c80001dec0008e100021a03480162efafa00000cb0000000dceb815829cc49349fdd4d2a780003ae4b4aaee3c7a304a681692801652bbebba168d9b11d32bacf2aab0641b490aa00000015e80000000001790c8c39468d00000001bc430b6b1a143260001a480382a35b783157434075b40494eb234840a47ad8fa55b915917c0000003e7915800005e49e1b6cf7013f537202c0009a5a02000000000000000009cacf339326830e48e7288a73253e9642b280000002f932090a40003e0671aee400073880001980000000e517700005436230e7915e00068
  | 31 => 0xa4a70c5990006879051a86443000365143800000032653247fa0000c2e0002cd000022d9c4000000040433eb1700000000008dc2d17158b3463f0000000000d8c1be80005ac0006d3ab9d132000176d62c5b52323a320ec0001ec2240000e84b4b000312c00022600000000000000002738e0d0001b480014ce59417680014bc89d5160000000c0500000002d00000220c52000da34d38001aaca190000001ab80000000000000000591800151ca020000001522000440800075800000002e170a00036600015a82a530718c0ee22d82540000dcc0000000158d2c3026505e481a6d2c00015dc3d03cf51313ed058d020000000944000005870144a2914d980000000004af00006129d42dda7e0c22a019cf800120c2d367200000009b600031ec000d210789f95b5227c000152c64a0634091d742ae54655b0000a9043e09c23998d007c32580012b60000548006962c4e00000018200001ac000063c22543d0000166b7d80024d1a3c00000012984220006d78fc433ad15571abb400000047005b8e54b1b235209e110dbb06aaf8d0ced8822a26b0000266000000000031700017e20005b280017a40000000000000000ac30860000000d360000000ed200000019d54e29d68000000f7200000010e8000a7837094c82c23a000031e44605001c4072d111af81c99418ad96d035532084eb48da38ad346583224e934359ac00038cd432174a9c04033f40105bfc11b314f946c90b48860c340d6200966caa43438706bbd2362e3800155db2c5a00002f5c0007e10002ba46c20003d80001a180abc62867a6ae0001d20c64fa0c4227eae801a300000035180002a0971800000018e00017639b00002670f5066915d5f991f1214000286d180d08bc6000036cd02336455a72d2e0a4435a251400000037d9d3c00000062780000000000000000000000000000142dcd1152355ca520001758e7400000000000018ca5ab46081b8000db260141e9a5511a0c66088c30cc30ffb66839c5730550000000000000196c0000005caea6c00000000000009d6000589217406200000007c80000000001330000adf000000128e000505aab000000000000011640004d42b31314c9348b36c4000b220210f9dadad77101c00174eca82b12dfe13a2634c720b80000000000b2e000a3d00020ac000b7f250f1b47bc000139e4ed1d286b3921a7d81c1cc0882d857322445460d8066043cc802e4c44e5c963f80000004270000000afad2f32a885c39e00000034b4ffc8b9070c0000000000000000738ab480020d6a260003d798089e800056040014e19eb4c4636463676337c000000093000009258600004462d9c0007a3800004cf105679100000000000000336800000064dd0e00003d2a1693a52da00000000f447c1e964e000000000001858345f875126e8e297
  | 32 => 0x109a70026e0001819a3200100000f9c600000ed2ef1d04207000676b4f8d2202169db3657eedb524555b90cb1631f8357d04d0000ae40013f38a803de3880466785961038d8c9d3127878a000000000000170366f0000000c7b0005e480011a40002978000d5e65300000017ca19a1a6d4748260003f926d400026952c1f007a652a47a233506220d26792400000002e0aa942780363e403186629b58
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe4c65d883144001d1ec9b106288003a3193620c510007273aec418a2000e4d75d88314400199ce3b106288003b19c7620c5100046fc3ac418a2000a5f8558831440454b90ab106288002a7e11620c51010d4e422c418a2043ad781588314400159d0c3106288003339d8620c51000727b28c418a2000e4c651883144001d1ec83106288003a3190620c5104c763b08c418a2000a9e86904314400193ced208628800387d96410c5103e70e32c8218a2000e8f6290431440f7d18c5208628825ee5a06410c5100064f3b08218a2000e1f6510431440efc38ca2086288003a3d88410c5103b7463108218a2000d9676104314412dd2cec208628825bc59d4410c5104b78aba88218a2000f176510431440efd2cca20862881dfa5194410c5104af8a3288218a2077e14651043144001f0ec420862881dba5988410c5103b74a3108218a2000f846210431440edd08c4208628809fb118a318851021e6b3b06310a2020ec4620c62144001cc8c5b2c4288003b118b63885100066b3b0c710a2000ec46218e21440035cd0db144288003399db62885100062e39eca90a202f8de86dcd21440018becbb9a42880031719773485100064e326e690a2027ccc62dcd21440411bd0fb1a42880c63721f63485100064fba6c690a2000c9c74d8d214400199ee7b124288003331cf62485101ce74386c490a2031cd4768c5214405f9a8ec18a42880f3651d03148510107623106290a2000c7865dc121440858e8edb2a42880039918b654851013e6a3b6e690a2020cd4761cd2144001b28e839a42880c7351db634851017e6a3b0c690a2000ec46218d21440039c8edb9242880e7391db62485101cef1b90e090a2000ce462dc530440019aec638a608800339188714c1100043f436ea9022000c5c63dd520440a58d8c5baa408814e1fa1f65481102943e43eca9022000c5f75d8d20440018b8ebb1a40880c7b2083634811000637baec49022000c6c75d8920440019a8c7b8a40880033518c714811000673b10e29022042c7a76d9710440639b4edb1e208800b369d863c41101ce753b6c58822001cea7618b1044001cd0ca3162088002b6a1a31c41100166d3b4638822000ada860c710440059b4ec18e2088003e410431c41100246e43aa6b1820048dc8758d430403153908b1a86080123e20175588100247643aa4b102004ae880549620400117f08bb264080622f211764c8100246e43ac699020048ec8758932040011eb0c38a640801ab5a07768c4101856a40ac41882094e966110431040091df0eb1442080133a9c162884100063c3aeec8802000c7b76dd510040019b6edb9a200800336dd8734401000675bb6e48802000ceb761c91004001ad0ea39220080be76a1e31440100066dbb46288020319da870c510040019b6ec18a2008003e49043144010
  | 1 => 0xb02328c488003999c4651891000732b88ca3122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000ec571d8c62440011db0f318c4880029ba16631891000536c2cc63122000aae8498c624400155b09318c488002b3a0e631891000477c3ac63122000a6f8558c62440014d90ab18c488002abe11631891000556422c63122000ace8618c624400199cec318c48800393d94631891000726328c63122000e8f6418c6244001d18c8318c488003b15c463189104df63080c6312209bec41018c6244001cc8cb288c488003b118e511891020d72432a23122000ec46354462440070fd0bbb264880021f617764c9100c45f426ec99220008bd84dd932440010ff0abb2648800e1f215764c9100045fc22ec99220188bc845d932440011bf06bb264880023be09764c9100047bc0aec99220018de87d8d32440051dd0fb12648801237e1d638c5100052fc2ac718a2023a5c8558e314400153f08b1c62880a2a7211638c51000567c12c718a2027acc8258e31440018b8cb3b4628800ab5206768c51011d2f436cb18a2000c5e76d9631441358bce3b2c62880a2a7a1b648c5100064f3b6c918a2000e1f65d923144001c38cbb246288176a7207648c5100046fc3ac918a2000a5f8559231440474b90ab246288002b3e09648c51013d66412c918a2000c9e761923144001c3eca324628800387194648c51013d67436c518a2000cce76d8a3144001c9ecbb14628800393197628c51000747b26c518a2000e8c64d8a31440011bf0eb14628800297e15628c51011d2e42ac518a2000a9f8458a314405153908b146288003339d8628c51000727b28c518a2000e4c6518a3144001d1ec83146288003a3190628c5100064f3b48318a2000e1f6590631440fbc38cb20c6288003a3d8a418c51042f463148318a2000c3c74d9531440b917d0dba262880030fd97744c5100061e32ee898a205dc9c63dd13144001958c5ba2628816e2fa1f644c51030c5e43ec898a2000c9f74d8d3144001938e9b1a62880c7361c3634c51000657ba6c498a2000cac74d8931440018b8cb3b0628800317e16760c5100062e42cec18a2022a5e86d9431440018bcedb28628800297e1f650c5101ed2ec3eca18a203ec5e71d943144001cace3b2862880beb5607640c51010d4f436c818a2000c9e76d903144001c3ecbb20628800387197640c5100070f3aec818a2000e1d75d9031440b753d03b206288267a5a07640c5100074ac0ec818a205da9c81d90314400193ce3b206288003a59c7640c5100046fc3ac818a2000a5f8559031440454b90ab206288002b3e09640c51010566412c818a2099e9441590314400153d0c3206288003279d8640c5100070fb28c818a2000e1c65190314404159d0db106288003339db620c51000727b2ec418a2000
  | 2 => 0x56418d1000567c12c831a2000acc82590634400193cec320c68800387d946418d100070e328c831a2000a5e8598863440014bb0b310c688002a7a126218d100054ec24c431a2000e5465944634405f5a90ca88c68800e1fa177650d100043ec2eeca1a20018ee82dd943440011db05bb286880032710e7650d100043fc2aeca1a200387c855d943440011bf06bb286880023be097650d1000c76412eca1a2000c9c431d94344001c3887b2a868806237a1f6350d100c54f426c6a1a20048f686dc543440018e8cbb8a86880033918b7150d10004bac28e2a1a2000c74651c543440019aec638a868825b6510c7150d1000672310e2a1a2000ae581d4b62440071df0ea96c488002b3a0e65d891000566c1ccbb122000acf83597624400159906b2ec4880039960465d891000727b2ec7b122000e4c65d8f6244001d1ec9b1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec48800393d9463d891000726328c7b122000e8f6418f6244001d18c831ec4880039919651d89101cd72432a3b122000ace839d7624400159b073aec488002b9a0475d89101cd72c08ebb122000a6e859cf62440014db0b39ec488002aba1273d891000556c24e7b122000aae84d4f624400155b09a9ec48800393d4e53d891000746a1887b122000a6f855c762440014d90ab8ec488002b3e0d71d89100056641ae3b1220398ee87d4762440011db0fa8ec488002b3a0f51d891000566c1ea3b122000acf83547624400159906a8ec488002aba1331d891000556c2663b122000a6e850c762440014db0a18ec4880029ba1770d891000536c2ee1b122000a6e85cc362440014db0b986c48800e1fa1b755891000636316eab12200087e87d9562440018b8e7b2ac4880021fa1c65589100062e398cab122000c5f65dcd62440018b8cbb9ac4880033318b73589100046f43ec6b122000c5f75d8d62440018b8ebb1ac48800327dd363589100064e3a6c6b1220008de8718d62440018beea31ac488003171d463589100064fba0c6b122000c9c7418d62440070fd0fbaac48800237e0d75589100146e41aeab1220008ef825d562440011f700baac4880021fa1c75589100146f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100062fba8e6b122000c5c751cd624400193ee839ac488003271d0735891000637baee4b122000c6c75dc9624400199ee7b92c488003331cf72589100066a39ee2b122000c7875dc162440018dcedb28c488003995c7651891000476c3cca3122000a6e85994624400159d07328c488002b360e651891000477c3aca3122000acf83594624400159906b28c488002bae01651891000537430ca3122000c6e761946244001cc
  | 3 => 0xbb1a2000acc825976344001cab0232ec68800387d9764d8d100070e32ec9b1a2000a5e8599363440014bb0b326c688002b3a0a64d8d1000566c14c9b1a2000a5e8598b63440014bb0b316c688002a7a1262d8d100054ec24c5b1a2000e546594763440635a90ca8ec688003175d475d8d100054f420ebb1a2000a9d841d763440015ad023aec6880c6b560475d8d1018d6ac0ee9b1a2000c9f749d363440011bd0faa6c6880023761f54d8d100070faa4a9b1a2000a5e859cb63440014bb0b396c688002a7a1272d8d100054ec24e5b1a2000ad6811cb63440635ab02396c68800237a1c52d8d100046ec38a5b1a2000a9e8414b634400153b08296c68800237a1c42d8d100046ec3885b1a2000a5e8510b63440014bb0a216c688002a7e1171d8d100054e422e3b1a20318de87d4763440011bb0fa8ec688002a7a1351d8d100054ec26a3b1a2000ace82d47634400159b05a8ec68808a37e1d51d8d1018c6e43aa3b1a2000a9f84547634400153908a8ec6880c637a1f41d8d100046ec3e83b1a2000a5e8510763440014bb0a20ec6880c637a1f21d8d100046ec3e43b1a2000a5e85c8763440014bb0b90ec688002a7a1321d8d100054ec2643b1a2000a5f855c363440014b90ab86c68800297a1740d8d100052ec2e81b1a2000c5c63dd563440010fd0fb2ac6880030f1d36558d1000636396cab1a200087e871956344001878e832ac6880031b1c86558d100061fb2ee8b1a2000c3c65dd16344001938c7ba2c6880030fdd76458d100061e3aec8b1a2000cac72d9163440018decbb92c6880031b1977258d1000657b26e4b1a2000ccc63dc963440070fd0fbaac688003170c77558d100045fc22eab1a20188bc845d563440011bf06baac6880023be097558d1000c76412eab1a200087e871d5634403117d0fba2c6880030fdd77458d100061e3aee8b1a2000c9c31dd1634400187eea3a2c6880030f1d47458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1000c7743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000ccf73dc9634400199863b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d1000672396e2b1a2000c5e76d9463440011bb0f328c68800297a166518d100054f424ca31a2000a9d84994634400159d05328c688002b360a6518d100046fc3aca31a2000a9f84594634400153908b28c688002b3e096518d1000566412ca31a2000a5e8619463440018bcec328c688003956046518d100064f3b6c831a2000e1f65d906344001c38cbb20c6880023761e6418d100052f42cc831a2000a5d85990634400153d09320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c6880029721
  | 4 => 0x1c4129f22e020863880c7355da318871017e6abb06310e2030cd7760c521c4095b28e818a43880c335dd87348710006ca3a0e690e20048de87d4d63840018beeba9ac708002a7a135358e100054ec26a6b1c20048dc8754d63840091bd0fa1ac70801237a1e3258e100062fbaceab1c2000a9e849d5638400153b093aac70800297a167458e100052ec2ce8b1c2000c9d741d163840011bd0faa2c7080023761f5458e100070faa4a8b1c2000ad7815c963840014bd0a392c708002976147258e100054f420e4b1c2000a9d841c9638400199ae4392c70800237a1c5258e100046ec38a4b1c2000a9e84149638400153b08292c70800237a1c4258e100046ec3884b1c2000a5e8510963840014bb0a212c708002a7a137158e100054ec26e2b1c2000a5f855c563840014b90ab8ac708002a7e117158e100054e422e2b1c2000acf825c5638400159904b8ac70800237a1f5158e100046ec3ea2b1c2000a9e84d45638400153b09a8ac708002b3a0b5158e1000566c16a2b1c2000e575194563840471bf0ea8ac70808a3721d5158e100054fc22a2b1c2000a9c8454563840011bd0fa0ac7080023761f4158e100052f42882b1c2000a5d8510563840011bd0f90ac7080023761f2158e100052f42e42b1c2000a5d85c85638400153d0990ac708002a76132158e1001c3f42eeca1c200087d85dd9438400193887bb287080032710d7650e100246e43ac6a1c2018a9c8458d43840091d90ea92c5080123720f764ca100246e43ac69942001acc8258d328400196cc9b8a65080032d990714ca100066ab18e29942000a5f855da31840474b90abb463080bf279c5648c6100045ec36e898c205dc9e63dd131840bb17d0eb22630816e2f21d644c6100064fba2c698c2000c9c7458d31840019b2c7b826308003879d5640c6100070ebaac818c2031c9e715903184001d2ce2b2063080023761b73486100064f326e690c20278de8758d21840411b90eb1a430800327dd163486100064e3a2c690c2000a3e8498f654400147b0931eca880029ba0a63d951000536c14c7b2a2000a5e8398b65440014bb07316ca880028fe1173d95100051e422e7b2a2000c5d731cf65440014bd07396ca880029760e72d95101dd3b408e5b2a2042a75811cb65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb654400147d0998eca880028f61331d95100043f43863b2a200b87d870c765440850fd0f90eca880021f61f21d95100052f41e43b2a2000a5d83c87654405d4ed03b86ca880021fa1f30d95100043ec3e61b2a2000c5d75d4f634400153d09a9ec688002a761353d8d100056ac0ea7b1a20038df8754f634400153d0932ec688002a761265d8d1000567414cbb1a2000acd82997634400153f08b2ec688002a721165d8d1000567c12c
  | 5 => 0xa37e1d73d85200064f3a2e7b0a4000c9d745cf61480019af02b9ec290002ada1331d85200066ab9863b0a400387e86dd561480a30f90dbaac2900021fa1f65585200062e39ecab0a400087e8719561480018b8e632ac2902831edc065585200062fb2ee6b0a4000c5c65dcd61480011ef0eb08c290002b520d61185200045fc22e630a40188bc845cc61480835d100a90c290002ada1331185200c45f424ed18a40008bd849da31480010ff0abb4629000e1f215768c5200052fc2ac718a4023a5c8558e314800153f08b1c62900a2a7211638c52011d2f42eed18a4000a5d85dda314805153d09bb46290002a7613768c5200056b40eed18a4028a9e849da314800153b093b46290003359c6768c5200052fc2aed18a4023a5c855da31480015ad023b4629008e97a1b658c5204fe2f38ecb18a40008df8759231480011b90eb24629000297e15648c52011d2e42ac918a4000ad78159231480015a902b2462900a2a7a13618c5200054ec26c318a4000e1f6590631480fbc38cb20c629000e1fa17764c5200043ec2eec98a40188be849d9314800117b093b262900030f1d3654c5200061fb2ee898a4000c3c65dd131480454bd0db28629000297e1f650c5200052ec3eca18a409ec5e71d943148001cace3b28629000237e1d640c5200146e43ac818a4000a5f8559031480454b90ab206290002b5e05640c5200056a40ac818a4021a9e84d84314800153b09b08629000395d97610c5200072a32ec218a4000ad587d8431480019ab0fb086290003959d7610c5200072abaec218a4000e9684d843148001d2b09b08629000395d94610c5200072a328c218a4000ad78718431480015ab0e3086290003959d4610c5200072aba8c218a409dec6721843148001d8ae43086290277b1948610c52000762a90c218a4000ed2701843148001da2e03086290263b1880610c5204c762100c218a4000e1f6590431480f9c38cb2086290003a5d86410c5200074a30c8218a4000e1f6510431480efc38ca2086290003a5d84410c5200074a3088218a40038df8754f63c40070fd0a3b287880021f6147650f100c46f43ec6a1e2018a9e84d8d43c40091eb0c38a87880025d6147150f100066bb18e2a1e2094d94431c543c40010fb0f3aec58800e1fe1d75d8b1001c77c3aa5b162039ae88054b62c403117d09bb265880022f613764cb1001c3f42cec996200087d859d932c403117d093b265880022f612764cb1000c6f43ec69962001ace82d8d32c40635a902b1c638808e97a17628c7100052ec2ec518e202fad48159031c4139d2882b20638808a97a17620c7100052ec2ec418e2094e967610431c4129d2aec2086388253c59d4410c7104a78aba88218e2077e966510431c40efd28ca20863881dba5988410c7103b74a3108218e2094f92701043
  | 6 => 0x246e43aa6b1c40188be84dc5638800117b09b8ac71000e1fa177650e200043ec2eeca1c40048dc8758d438803153908b1a87100123d61e519862001e3b3aca330c400387e87dd561880018d843baac31000237e0d75586200146e41aeab0c40028de87dcd61880018beebb9ac310003171d773586200064fba6e6b0c4000c5f751cd61880018b8ea39ac31000327dd073586200064e3a0e6b0c4003c747594561880091e90ea8ac3100021fe15768c62001c3e42aed18c4000ad681dda31880014bf0abb4631008e97215768c62017c6fc3ac318c4000a5f8558631880474b90ab0c6310002a7e11618c6201454e422c318c400087f855d931880070f90abb263100022fe11764c6200c45e422ec98c40318df8758431880014bf0ab08631008a97215610c6200054fc22c218c4021a9c845843188001d2cc22086310003a5584410c6203b7c21088218c40418ef8758621880014df0ab0c43100028fa1063d95200051ec20c7b2a4000a3f845cf654800147908b9eca900028fa1073d95200051ec20e7b2a4000c5d731cf65480014bd07b8eca900029760f71d95200052fc1ae3b2a4000a5c835c765480014df04b8eca9014a9b20971d95200051f42663b2a4000a3d84cc765480010fd0e18eca900021f61c31d95202943f43e61b2a400087d87cc365480070fd0b38ec6900021f61671d8d200045fc22e3b1a40188bc845c763480010fd0fb2ac6900030f1d36558d200043f438cab1a4000c3c74195634800187ecbba2c6900030f1977458d200063bb2ee2b1a4000c7465dc563480018eeca38ac6900031d1947158d200066a318e2b1a400387e87dd563480018b863baac6900022fe117558d200c45e422eab1a40008f7815d563480011e902baac6900021fa1c7558d200c45f43ee8b1a4000c3f75dd16348001878ebba2c6900022fa077458d200064e18ee8b1a4000c3f751d16348001878ea3a2c690003271d37358d2001c6e43aa6b1a40a1c9c7454d634803117d09b8ac6900022f6137158d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200065b426e2b1a4000cb584dc563480019ad07b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4000cb7841c563480019690838ac69000335e0c7158d200066b298e2b1a4000cd5531c563480019ac8638ac69000e1fa177650d200043ec2eeca1a4000c9c439d943480010ff0abb2869000e1f2157650d200046fc1aeca1a40008f7815d943480011e902bb286900032710c7650d200070e21ecaa1a40188dc8758d434803153908b1a8690002b52056350d200062f39ecbb0a4000c5e7319761480018becab9ec2900031719573d85200146f41eebb0a40008dd83dd7614800193ce939ec29
  | 7 => 0x9c7418d60484879aee231ac0908023ee1d60181210053c42ac030242048bc87551648c0091d90ea92c5180622fa137158a300045ec26e2b146000cd4311c5628c0091790eb2285180beb5a0773986300247ac3ca330c6003c7675946618c00156908a8cc318002b5e0d51986300056ac1e8330c6000a7585106618c00117f08baac3180622f21175586300c45f43ee8b0c6061cb581dd1618c00193863ba2c318087271cc74586300247a43aa2b0c6000ab484545618c0014eb0a20ac3180032ddd041586300055b40eed20c6000cb6715da418c0b917f0eb0c8318002ade1e61106302e55ac3cc220c6000e3675984418c001c6aeb3088318003a5e0e61106302e759384c220c6000eb170984418c0b9d2e613088318173a54c2611063030c5fc3ac220c6000ab787584418c0c396f0eb0883180038d9d561106300071abaac220c6097e9483584418c063da4e130c63180be37e1d618c6300054fc22c318c6028a9c84586318c001d2cc320c6318003a5984418c6300076930ae118c600387e85dda218c0010fb0bbb443180123d61e61886300045fc22ec90c60188bc845d9218c001968e930a431800335dce61486300247a43ac290c6000cb474585218c00717f0eaa6c898003350c671d91300146e41ae3b226000cd4315c7644c0011df04baac8980063b20975591300047bc0aeab2260008f4815d5644c03153d0db228698002576147150d3010e4e320e2a1a6018c9c7450f624c0010ff0ab8ec49800e1f21571d89300045fc22e3b1260188bc845c7624c0031b906b8ec4980033918871589300064e3b286a1260048dc865d1324c0013a902ba264980063721d644c93000d66412c89926001ace86d89324c041998c438a64980622fa1375d85300045ec26ebb0a6021c9e739d3614c03117f0eba6c298003270c574d85300047bc3ac230a6000ae482584614c0051b906ba8c2980be3721d531853001e2f3aaa630a602f8dc8750c614c031938e8a18c2980022fe1172185300c45e422e430a602f8dc874c8614c0015a902990c298002b560f21185300043fc2aed20a600387c855da414c0315390ca1c8298003279d943905300051fc2aed20a6064a3c855da414c00156d023b48298186a7a1b73905300064f3b6e720a6000b9681dce414c0c35390c994829818ba318932905300146e418eca0a605ca9c864c8414c0bdd18c49908298002e520532105300246f436e918a6028c9c64dd2314c0015a902b24629802a3761f618c5301454f426c318a6000a9d84d86314c001d28c320c6298003a5184418c5300076830ce118a6000ed0615c2314c03117d093b442980022f61276885300246f436e710a6027ccc62dce214c03117d093b242980022f61276485300146e418ec90a6004a9c8650d404c005938eca1a8098012e620143501300
  | 8 => 0xb2ec690802b620165d8d210052f428c9b1a4200a5d8519363484018baea3aec690802a7a1075d8d210054ec20ebb1a4200c9f749d363484014bd0a3a6c6908029761474d8d210046f43ea9b1a42008dd87d536348401c3ea92a6c69089e37a1f51d8d210046ec3ea3b1a4200a9e84d47634840153b09a8ec69089eb3a0b51d8d2100566c16a3b1a4200e575194763484451bf0ea8ec69089e3721d51d8d210054fc22a3b1a4200a9c84547634844f1bd0fa0ec6908023761f41d8d210052f42883b1a4200a5d85107634840153d09386c690802a761270d8d210052fc2ae1b1a4200a5c855c3634844f5ab02386c69080237a1c50d8d210046ec38a1b1a4200a9e84143634840153b08286c69089eb3a0850d8d2100566c10a1b1a4200ad68114363484015ab02286c69080297a1740d8d210052ec2e81b1a42008de8710363484011bb0e206c6908032718f7458d210045fc22eab1a42188bc845d563484011bf06baac6908023ee017558d210247c402eab1a42188be87dd1634840193863ba2c69080327dd37358d210064e3a6e6b1a4200cb474dc563484011bb0f328c690802a7a126518d210054ec24ca31a4200acd82994634854d5ab03328c69080237e1d6518d210054fc22ca31a4200a9c8459463484015b700b28c690802b62016518d2142e4f3b6c831a4200e1e75d906348401c3aebb20c6908023761e6418d2151d4f424c831a42008df87590634854b5af02b20c69080297a146418d210052ec28c831a42a2c9e761906348401c3cea320c690803875d46418d213b74b908c831a4276e94211906348401938873b2869080237e0d7650d210047bc0aeca1a420387e851d943484010fb0a3b286908032710c7650d210c46f43ec6a1a4218a9e84d8d43484031bf0eb1c6290802a7e11638c5211454e422c718a4223a5e859da31484014bb0b3b462908a2a7a1b648c5213de4f3b6c918a42008df8759231484ed93cec32462909ef279da418c5212f45f436e898a425dc9c63dd131484b717d0fb22629098a2f21f644c5210064fba6c698a4200c9c74d8d314844f998e5b1a6290886a7a1b640c52142e4f3b6c818a4200e1e75d903148401c3aebb206290a17279c7640c5210074b38ec818a42008df87590314854b5af02b206290a92a7a18640c5215164f3b0c818a4276e9761190314854753d0d2086290a17279da410c5213dfc210c8218a42a2c9e7610431484edd2ec22086290882b3a1a318852113d674306310a4200ae98214360484015e302286c090803279d363981210064eba6c73024200c9e7418e604840193ae831cc09089e3721b73581210046f43ec6b024200c5f75d8d60484018b8ebb1ac09080327dd363581210064e3a6c6b0242008de8718d60484018beea31ac090803171d463581210064fba0c6b024200c
  | 9 => 0x72d91310045f438a5b2262008bd8714b644c4bb53d06296c898802a760c52d91312ec5f43ea3b2262008bd87d47644c4bb53d07a8ec898802a760f51d913100557416a3b226200aad82d47644c401c6ea328ec8989822fe1d51d91312ec5e43aa3b226200a9f83547644c4bb53906a8ec8989762fa1f21d91310045ec3e43b226200a3e85c87644c40147b0b90ec898976a7a0f21d91310054ec1e43b22625da9e839c3644c40153b07386c8988028fe1570d91310051e42ae1b2262008be87143644c40117b0e286c898976a7a0c50d91310054ec18a1b226200aae82143644c40155b04286c898802ada0450d91310055ac08a1b2262008be87083644c40117b0e106c8988028fa1420d91310051ec2841b22625da9e83083644c40153b06106c898802ada0420d91310055ac0841b2262008df835d5644c4011ef02baac8988022f61e65191310054ec1cca3226200aae82994644c40155b05328c8988022fe1d65191310054fc1aca32262abab781594644c40147d0b310c8988028f61662191310054ec1cc432262038ef8754b624c40117d0fb22c4988022fa1c64589315565bb88c8b1262008dd83dd9424c40317d0fb22849880327d9373505311464e326e6a0a625ba9e86d92314c4bb93ce3b246298977a59c7648c5310c46fc3ac918a625da9e86192314c4b753d0d20c62988c727d8d74981314b65ab88c9302625d8bc86dd1604c40117d0fb22c0988030fdd764581310061e3aec8b026200cac72d91604c40117d0e322c0988030fdd464581310061e3a8c8b026200cac72191604c40195ec9b92c0988032b19372581310047dc3ac030262009d586dc5420c4019ab0db8a8418803559977150831006aab2ee2a1062a9d9684dc5420c551b2b09b8a841880275e187150831004eac30e2a106200d56651c5420c401aaaca38a84189db65e10715083151eca420e2a1062a7d96641c5420c401b2ac838a8418a9f659507150831006caaa0e2a106276dc6621c5420c401b8ac438a84189db6590871508313b6ca210e2a1062a7d97401c5420c44133f0ea148218883639c94290431004afc2ae1208622295c855c2410c4f7b1ce5b948218802e5a0772904312ed4f434e12086200a9d869c2410c40163f0ab8482189f2c721570904314cecb38ae12086228c9f76905410c44372d0320a8218a7365107705043101c6fc3aa7b1c420387e85dc163884010fb0bb82c7108023da067650e2101c3f428eca1c420087d851d943884311bd0fb1a8710862a7a136350e2113d6a40ac718c42a3ad681d9031884edd2cc220863108023ee1d60182210062ebaea7b1a4200a9e84d4f634840153b09a9ec69080e37e1d53d8d210043fc2ae1b1a420387c855c3634840153d0932ec690802a761265d8d210054fc22cbb1a4200a9c8459763484015b7
  | 10 => 0xb0264008bf845c7604c83117908b8ec0990023ee1d60181320064e21eebb2462008f681dd7648c40193886baec918ac3a510e71d92310043fc2ae1b24620387c855c3648c4bb938e7ba2c918abeada07745923101c5e43aa8b246218a9f86591438c4f11bb0db8a871896e75a1f7150e312decbba0e2a1c622395e85dc1438c4012bb0bb828718863279d14358a31014ce43a86a146200c9f7650d428c4031bd0fb2265188a3271d3644ca3100d67416c89946201acf86589328c4391bb0db8a65188a267a13714ca31004cec26e2994628b9d687dc5328c4bb3a902b9c8318862a7e1943906310164ebb28720c6200b978150e418c4070fd0fbaac11880317ccb755823101e2e3aaa6b046218c9e7450d608c4018beea992c1188023ee1d60182310064f326ebb2462009d681dd7648c40193cc8baec91888e57a1671d9231004aec2ce3b246221c9e649c7648c55dd2cc938ec91880355a1671d9231006aac2ce3b24625bd97849c7648c4b7b290938ec918abb6599271d9231576cba14e3b2462aed97409c7648c4012bf0ab86c91888e5721570d92311464fbb6c8b246200b9681d91648c4473390eaa2c91880275a0775d8a3113c6ec3ecbb146227ace82d97628c44f1bb0fb26c5188a3279d364d8a3113d67416c9b146220cce629c7628c55bd8cc538ec51880335d9671d8a310066ab2ce3b1462addc6629c7628c44f1b90eb2ac51888f171d56558a311464f3a6c8b1462278dc87591628c44f99eedb12c518802f1a076258a310066b30eeca1462009d6819d9428c4013ad023b2851889e67a1f6450a310064fbb6c8a146227b8e82d91428c40172d03b228518976e5205649063113ccfc3a8520c6227d8e7250a418c4012bf0ab84831888e5721570906312edcb40aed20c625de96615da418c4bb93aec3b48318802e5a04769063156747316c520c6200b9681d8a418c4013ad03baec1188c63761f65d823118d6d406cbb0462318dd87d93608c45193ce9b26c1188c63761f62d823113e67396c5b04625b99c815d2608c45f93cc2ba4c11880365985749823118e4fb02e93046231c9d605d2608c4bb33f0f20cc1188026761e419823111caf43eeab046200c5e61dd5608c401aacc3baac11880257a1c755823111e2e3aecab0462318dc87595608c4478b8eab2ac1188a3279d364582310056b40ec8b0462318dc87591608c4018beebb12c1188c63721d62582310062fbaac4b046200d1f75905608c4fba38eb20ac11880276e1d60182310061ebaea9b226200a9d83d53644c40717f0eaa6c8988021fe1570d913101c3e42ae1b226200aae82997644c40155b0532ec8988028fa1662d91310051ec2cc5b226200c3d751d7644c4bb53d063aec898802a760c75d91310051f42ce5b226200a3d859cb644c4bb53d07396c898802a760e
  | 11 => 0x800001000400401400400c01000000001000000001800000803c00400400400000000001400002401001801400801400000000400000801000800800c00000801000000800000000c00800000002800000400002400000000c00001000002800001000000000000000c01000400400000402800400c00c02000801401400c00001c00000400400400000800003002000400000000000000000000000000001c00000000401000400801000000000801000400000001c00c01400400c05400000000000001000800001804800000000000002000000800c00000400000c00400000400401400000800000c02001001400000000c00001c00003000801400400000000400400403800000002001c00000000400400800800c01000800800000002401c04800400000001b2887b8ac4a18036510c71589430c46ec1eebb0a8600c7575d476150c015ab07a8ec2a1802b9a0b51d85430053b42e43b0a8600d1c435d46150c011ef0eb08c2a1abab5e0d611854357f4a21ac230a8600c9c43dd46150c010fb0f3a8c2a188b171ce75185430070e21cea30a8600c9c435d46150c070ff0eba8c2a180317dcd75185430070e21aea30a8600c5f835d46150c018b906ba8c2a18030f90d75185430062e21aea30a8600c1c435d46150c018be64ba8c2a18031d20575185430062e18aea30a8600c5f305d46150c018eaeba88c2a1802b560f51185435af4a21ea230a8600ae682d446150d69d2886288c2a18029da1721185430056ac1e4230a86b3e9443c846150c015ab06108c2a1acba510c21185430068e21aebb02860087d879d76050c070ff0ebaec0a180317cc975d81430062e18aebb028600d94439c66050c01b2886b8cc0a18023ee1d601814301c5fc3aa9b22640087f855c3644c8070f90ab86c8990032d19071591320047bc0aeab2264008f4815d5644c8011f700baac8990123e20175591320066b41ee2b226400cd7731c5644c8019af0638ac89900335cc071591320c54f436c8a1a640095d851c5434c843938c838a8699002576177050d320c45f426ebb0a64008bd84dd7614c8031bb07baec299087279ce74d85320064eb9ce9b0a64188bf875d3614c80193ae6ba6c2990032de0574d85320064e18ae9b0a64038f787547614c80156908a8ec2990029d61441d85320065aba083b0a64008f787584614c80156908b08c2992b6b5e0d61185321046e43aa630a6403c5e7554c614c8411b90ea18c299063271d143185320056a40a8630a64038f587944614c8078eceb288c299002ad21151185320056bc1aa230a6400e5553544614c8015ab07a08c2990029d614411853258f4b2188230a6400e9543104614c8015cb04208c2990021fe15701853201c3e42ae030a64008bf845c0614c83117908b80c29900f179d553d81320c64e3a287
  | 12 => 0x480001c9af123d052a708cda9209000000009800000000f9cd00000015ea900cca81c00000000000188800156173a31da50000000001c48001ba0000c08000000000958e30000000000000000b480011918e9098000001de80000000000a1d58000002e3c002fd0ae800224000022007a20a220000002c09788001730859fe1ec42884debda7717cda7d6788a00000000000014f0614002d38000000000000002170002a00000000000002f1a2e80000000000000026b2140c600001600027513514213b98585a8400000002a155ba130000000178000002068000002f68003230000000002de29b0860b353580021d80002bc002870000b7800071285c0016997088a8001a28001794bea490000000002a10002ab80020f8080d09dfc000fda009e900000002029b80a80e8d996a922acf80017d8001b6a9408ec0005580013d16600000015d00021240014097bb2666808bb180a025f0e62622fa0000bb4000000000000001e600028d802800c00000003c00800400400400401800404001000400800001001000800c00400001400000000400c00801400800000c01400000000c00400001000400001c00401801000400400800402c00400400403000800000001800400000800c00800800c00800000000001000802000000000000400000000001000000001000800000400400800000002801404000001000400800000400400001000000402c00c02000000000001800803c00000401c01800400000000000c00001401001000000c00000001c01002400800000000001c01401800c01c00400000400800000400400c00c01c00c00c00000400000000800400401400000000800800400000000800c00401800400400400800000000000c04400400000c00801001803800000801800000001002402400c00c01400400800000400000800002800400000800800400000001c00400001800000400801001800000001400c00800001401c00000400800000c00000000c02800000c00400001800001000000000001401800000c00000400401400400000800000001400000c00400000000000000c00400000000400000800001800000000c00800400000400800000000000800000c00c01000001400000801800400000001000c00401401000400000400c00000403001400400000400000401000400001000800400800000000000000000c00000001000000000400400400000c00000002001000002000000001c00c00400001c00004801000400002c02000000c00402002800c00000c01400000400800001000000000400400000c00400c01000400400000001800000000400400c00400000000001800005801001000400400801402400400800400001001800000c00400000c02001c01000400000000000400000000c00004002002c0
  | 13 => 0x11ece9838000002350000000000000be4000000001841c9468000000000000208a830404e1afa9b782380020d80005689089280000000015483c8000000e78002adb22645c2c111202e78d7c71fd1da302939a1d58800281860c6500009330521f8378475701d18e90460790af000320cb58498001b11d64000f40000000000000000ab26e80bb0e9e18e509f80d9998300000002df00008d0fc0000000000001e8800000000000044400271800000144924e30e59a0400001cac88d20001c69ef00017e40000000000017f8780848001418001a2278af2c000a480000000024ad1380027a88d80000000031f32b80000003503dacd7162ef0000000a61f057f0000000bd40018f0a2c0020e80012b800094ddaa060000000000001ed8002be0000ba98d97186b1a00110000471460f68001bf80000000000009551b80480000010d0000000001920c38000ce80027102a3120002d54f78b91e280023e94b8e02628d02679ca1c80000002a80441b71dc2e39240a800023c6448622c38000000000240000001550000c98002f39d78001a986c00008706440000000000000000011806124280023100000025700000000000000000000000018a55fca8c0000020a2ed8a580000014c2daab0978400050c000e80000000000001c78000fb8001068000bbae9b002fb96fb2792a00031404908b05fca69a400000000000008cd54059800032239ad5a8027f80025c10c0000000000000520000000000003110000000e583ec9a30200000000000001a24c21e80004b2668001ff1fc8000f28000000000001d880006a0ce0ef800178d1280000026100000000000029a0000000000000000000000001d322b2cf4002b700018d21f1e41390000000b69f829194e10da07a4fa8f9729e6a776f31ec934899dff8821a89930000158002e209ca76a540002d700000004d0000000000000868000e280024819fc0028a83d2340098002c980024212cb2502ca4ca2ce5a000023061c524000000a1c003098810003008000000002c603580000003f2862bf8000fa000000004c000001b60000000028002aa80000030e43b1b8a1200023700000000007f0acb040000925b8000000201a5a9058001749690002848000002ec4000000000000a321c92a71d9dc6e2a260e999e80000000004c0000000000262b200011f8000cf3191cea1380004a10e00012fae1a9f9ed0000002268000a9ccfc0019c10892f05a2bbadba9600019bc0002f0000000001a30000000000000000da28c9450000504bbc002a50000000bb0000001010000002b680500000007ca7980000006300009740027b000000000000025c0009bd81800044c001d400011d47b4be127a7a0802080f023c191000022b0b8000002dd91200000000000000000010800023d8788001868000002d4c00
  | 14 => 0x1eb811999f1ac002ec80028c1100000708ec00023b800204a4117bc0000000025e3208c803492ce2e400198428c0000000000000000009124389207c26b83b6f095f40d00025329586b8abce889a6510b2c670354000330002bb00019907db25a2a00019c8001820000001e38000000000002f0c6600030ca61a9f116b2b00027c0f90ff00000014d0000000000000000000000000002292fc8c680002199b800000126c000001198002a29430000000f2000039400283a108000000000001aca39c002452d812c000000046ad29bc1480000000000000001f58002a30bcdf40001e12f7b030001628002c00000000000000000000000002a48000000001538faaf41bf001c001e2126903b130000eda804941790001341714cd28582b1658000001a48001dcc7fc604f124880c8000000003200de90c9e085800012d694a690fc80000028e8002485f880024e28a4000a51d2c0028e014c000000000000aa8000ad1f09851b18060d689e4b71bb8d43070649cf80027d00000006a80e00012600024b40003680000031c8000001cb31a84505c13c843000000000177c00066e7b930051048c33c0000031385d0890d480000028080000000004beb300000000014e8000361388000002ba1ada3a67e8000000eea0b0212f80000c900000029c82e9330aa2f280029a80006b4b500000000017dc001a2c000fb2330e40c5b1a11c0001fb800000000279167004189b1981730f8a90002f98318338d28000000000000f580016f0000000a1000000024ddd80014918916080000025c9880001060000000000002298000001c513c0001be868a030000968d103087e2883049c9ead2d52da0b0b21c15054a4f0db2b1a1515821812993b30180026e00000000000015210a0001274b400013ab2c264a7604a80009db2200002a95a0001c1800034447c0000006400000027ec0008c0b632bd56af00000000000002ae00000000000000000000000000000019380000021d0000000000000000eca8b81440000000000000000026c80000000000000023f0778f50540ff8000000002c6b1780030a670250a4b0000002a628b00026f01f91407b9479df800102992ae48a70d300006097e80000030a8ae0001720000001f10001eb0003248000c524e800137ad09b900000004196d00019ac000001291d617e17d0001ef85bae7a600838698b99f7aeb80004786640000000008940012080000031040019b2898998002ea81d2a682980000000000000000032400000f1053234000124ee0d4400177000104aff8578001faa2c0748000840000000f70c71598570000410002ac0000000ba0002b587400000000027d84a4000002b60df8174691cdab48002b80bc0700a21bc8619ab80018a322f171ca40011a0a093180000022e0000002ea19f0000003
  | 15 => 0x2306058b5c0018b00000004f98b8000000000000830000000000000000000000001de40018951f2ac8000380df2a18ed0002fe0000d60d800000019d00000030b1019270000000000000000000000000000000000002f666d8000000001ee0001161440002d4ad00dba0240000000019a8000000de2e6800000203a558310001f00000d72c41f48000001d203f89d01a8fea378002d2dd507b1b499f80000000000000000000000022bf1bc0009c115010b10c29ecd8000208ab9fc31e2020002e124180000024a40000000000011dc0000032aaf22424000000752f90000cc14f8f480021692800000023887f4aa6568e48000000000000000002ff0000002aa0f300000000000019e13e000000050ab3800000161c000001e722a92015ac000001b300000000000020e06d5a542e06bd6bc5da49a6990b17b0001500f6012d5caa8b2100000000022111c8000000000000d90000000000000000001a14000000000000000000000000eb00000000007329326aa8100015dd24ad79db03d6f49fb03b842df1df3498b150c79c222506d9d9139a3aaa41dca3f8b01244a140009616b1639090002c507600000031080000002b899025a4d00000000006c928800000000096c001a26e61fdaec000000202a5f8000001cca1900000000024780000000030f40000000014d816a112d880015d8b380007696ea550000c324d9bb065813130c000000000002c590f25000001f00024bad20000000000018000bfb269f6ab890f9be15706e0ef09cc9a95f240400000019ad18a299d95eeca8dc00021aaa082d0c22cc93f9ab00003892d86f19a26c1642c28000002afa9880000000000009529119700021280000000000000000000028f000000000051c002b1000302b1bafc15e7271380809219961d98001210001070000000000002ce01e8ca000000000000075891dc280003ac3a569eeb034c2457400001c0000000c180000006680000011b17fe782dd168272311443b2605004f1a1000000265acf0000000000000002c3079a2f22b81924a9c906ccd58f3800173e9900000000000000007380000000000030d8000000000000000003158448e21d39fa0000000000a780000000005928a2d6800000000000adb000000000065c5897aa36818051a1b2828dd91e0000e12cc000264013af70000341a0ab29009801e78000002c90f19328a0d14adc09b11588060d2c800000020c8001aa0000bd1040100000002d0f059c70002af0000000000000000000000000001fcc00218918a9d80016888c800000092d30a548000dd1b40000000001baa5190b8679518000a380020f21024a000037c000a40b883700000000000000000032800013704587a9830000002f589e8000000001ca80030e1f9800000187d1a8d500008e00ecb30000001a72460a180
  | 16 => 0x891da2950001a3856018a1e24000716105e1e9a9715b2689e4a560000001ae14b00000022300014a8000000003148000000000000000002e502f94a07192b194000000000318a38e3e17040015b4000000002c49861bd0454d18121668000001321848000002248001410000001871001c6000222acd0000001558000000001e30000002582391e7c0c00000005330680000000009700000000015932ca04c000000002158000001ee8002001978000000001d74000000a8ae58c4b1686380025e8001f21614000002358c100000012eafd9a60001630002ba8b12ee8000c28398000000489903290000001aaa9e8000000000001c300000000026700000015300021980027484cc001ae8001b5888e1c00000008818aa968fc58ae23946a741d800029296c8391a813e4b28ea1798000d88000000000000000000000000002a72b9aca16c0eaa408000e083cc003039a1800188d9808e96e1f71622e329c1b38000000000002cb1d1c002bc1c11e040010e8000000ac2281b50000000002fe800000311a4718c8d78c456b9710002ef9d492a9652b78046b4258a160000002fb11780000006e8000000001b28948000000001e00002e440026d27c80000007e80031f8f0800000000317d7c16fe53b1f440b28800006800232a2c80013a0000c42d92e00000000000003184000000002458000000002070000001032bc800000000000068c001f30000002bf0979c399500000000008f8000000000000000000002e91508000000001618000000010000002c70000252578002431b08000b64f881e000289c0000000000000000031e40006f9e58f81af9de1311f900000000000000032ac000000eb8dc827ade8001ea1600002273090bc8001f280007a0d0c0015788284d4414a96e89364428002219369ce1a3c93ad100000000000020b80016a208400000000175a0c00014717f4000000000000af91331e8000000000adac20001ea8e3800234a88a3b0001020bd82d88840013e80000029e16d8cb07230d27f0000000000000000000000001a6a7e0003101812ed154e878000000000cba60800000000211ad60000002d42318000000000000001ad1c40003218002099a58000c6c9e2c100006a40000300011e95e0000002d980021a1752f880015f8ac4000002010002662d31cf0000000002592851782a3b238002a92758002a58000000000002360550000000000001c09d68000628001a7ae0895e2d0635dd52380011180004b92e0128002be9ec00008e40000030a00000000004e80002921b9eec0014980003eae5c001f18000ceeb9164800191a8200000000025b27303a86840000003dc000000000000001079fd0000088000001b219964412500020500000000000012300028d00000024e40000000000000005b22582706d065522000
  | 17 => 0x1d10d55d7290805af500000000006007286e53f0001e529980000000000000004d80003e0002520000001c587f80000011d1e7587800000c1b273b129f60002178000000038000000020000fd00005f22fa309e800000009f080c0000001483c6ae889a631d01ac15100000015a80013271b2200a9a09000000000026ab000b0002840705908c0cca80025d0000000000000000000002dfaf61a363384217a10a9d08002653244bdd8f8000000000001dec0008d4da8197078002528003284000002288cf80000013d8001df1b014580022f487a3a0282ab0000001f3800000045c0000000000013380000000000023540029800025d80013630f05c80007d00018c180a97800195a384001f508526a2ee29d2e41db9af0249d284b4002e81feb2283c0e70b80000000001948000000000000000002320000000000001bd8000fe17ca8681b9b980051700000000000001d8002b500000000026380015280000003a0c89778002dc8000bf0000000001cb8001c00000e6800125b060000001cac00196a5b80000000000030100012d00fc0000000000008880008f0000000002279c89a923ca77aa98000000000770002e70000001400000d3a468001768f980026f8001428000d4e9940015c0000000000000c00000000001108b180020a9cc01405fb081488092380000000002c180022d800032aa780000000014c9438000000002cb89f58e04e30884c8b56ae491853a1485e87c4002c798280031d31c000272b0c1760000001dd000000000198881b2a32984c49b8000000002a20b22bd2
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x20007948d1780001d80129f870e8880119d169120859b190b04108489014020180f868000060000000500001e930a8115019a0000000280038e14001000001593800019961a9e000800188a1b8c801c8d898b8f1f00008000170000001c120c0303830604100000400400000040440102020c00300507a58435d46150c016169110e751854311417a63735d46150c0141e9710d751854300585a44435d46150c0141e94e0d751854300507a4e435d46150c0141e9810d751854300507260435d46150c0141d9210d751854300507a44435d46150c0141d9010d751854300507253325d46150c01c1443205751854300507250315d46150c0141c94cc175185430070510d75d446150c01a8443a0b51185430068510e85c846150c0181c646147150d32004956548150c614c801a16436144118532006a150d82104614c80189443a0775d92310062599281dd7648c40181e6461671d923100625dda81d91428c4b789576a04769063100705991651c5420c54719498550715083100711595621c5420c401c856458871508313b6619ca81dca410c40105d97a146418d210048766275190634840181d8510c7650d2100523648431d94348401c31755c2611063000607191851c5434c147a846220532105303bd852556110431880014959418c7158d2000427660431d9434800105d989cc65d85202dca5245849da314800145597197610c5200051565c651843148001855875d4610c520007115d57218431481316c090548610c520007145d5701843148001cc1725c0610c5200064510d851c543c400181d8510f7650e100052664043dd943840014999010c7650d100064510d851c54344001075981947150d100070510c651c54344001c84431887150d103bd85a5b6510431440ed68696d88410c51000781197621043144001c8676188410c51000781d94621043144001e0465188410c510
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x6a0e04000c00281000481b444c086ba8c2a1802414a1648435d46150c01206d112818aea30a8600906680940c5751854300481b444a660ba8c2a180300d85648431d94348401488d0086c28e2a1a2000c05660431947150d10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x4e
  | 8 => 0x138e
  | 9 => 0x94b
  | 10 => 0x94c
  | 11 => 0x94e
  | 12 => 0x124b
  | 13 => 0x124c
  | 14 => 0x124e
  | 15 => 0x138b
  | 16 => 0x138c
  | 17 => 0x98c
  | 18 => 0x98e
  | 19 => 0x128c
  | 20 => 0x128e
  | 21 => 0x9cb
  | 22 => 0x9cd
  | 23 => 0x9ce
  | 24 => 0x5
  | 25 => 0x12cb
  | 26 => 0x12cd
  | 27 => 0x12ce
  | 28 => 0xb0c
  | 29 => 0xb0e
  | 30 => 0x140c
  | 31 => 0x140e
  | 32 => 0x24b
  | 33 => 0x24d
  | 34 => 0x24e
  | 35 => 0x144e
  | 36 => 0xb4b
  | 37 => 0xb4d
  | 38 => 0xb4e
  | 39 => 0x144b
  | 40 => 0x144d
  | 41 => 0xccd
  | 42 => 0xcce
  | 43 => 0xe8b
  | 44 => 0xe8e
  | 45 => 0x95396
  | 46 => 0x94056
  | 47 => 0x249
  | 48 => 0x24053
  | 49 => 0x1449
  | 50 => 0x24056
  | 51 => 0x4d
  | 52 => 0x145396
  | 53 => 0x144056
  | 54 => 0x138956
  | 55 => 0xb0956
  | 56 => 0x94b16
  | 57 => 0x1409
  | 58 => 0x140956
  | 59 => 0x95416
  | 60 => 0x24955
  | 61 => 0x24956
  | 62 => 0x95456
  | 63 => 0x94d
  | 64 => 0x144956
  | 65 => 0x209
  | 66 => 0x14c9
  | 67 => 0x25253
  | 68 => 0x25256
  | 69 => 0x124d
  | 70 => 0x145256
  | 71 => 0x138b16
  | 72 => 0x141396
  | 73 => 0x139416
  | 74 => 0x25395
  | 75 => 0x25396
  | 76 => 0x138d
  | 77 => 0x24996
  | 78 => 0x98d
  | 79 => 0x144996
  | 80 => 0x168b
  | 81 => 0x1649
  | 82 => 0x134b
  | 83 => 0x14b
  | 84 => 0x141296
  | 85 => 0x25296
  | 86 => 0x128d
  | 87 => 0x145296
  | 88 => 0xa0c
  | 89 => 0x1449d6
  | 90 => 0x9d456
  | 91 => 0x28c
  | 92 => 0x289
  | 93 => 0x148c
  | 94 => 0x28b
  | 95 => 0x289d6
  | 96 => 0x28e
  | 97 => 0x1489
  | 98 => 0x148b
  | 99 => 0x1489d6
  | 100 => 0x148e
  | 101 => 0xcc9d6
  | 102 => 0x9ccd6
  | 103 => 0x150c
  | 104 => 0x9ce96
  | 105 => 0x180c
  | 106 => 0x130c
  | 107 => 0x1452d6
  | 108 => 0x292d6
  | 109 => 0x1492d6
  | 110 => 0x140b16
  | 111 => 0x24b16
  | 112 => 0xb0d
  | 113 => 0x144b16
  | 114 => 0x16cb
  | 115 => 0x25416
  | 116 => 0x140d
  | 117 => 0x145416
  | 118 => 0x28253
  | 119 => 0x28256
  | 120 => 0xb8c
  | 121 => 0x184c
  | 122 => 0x24b96
  | 123 => 0x148253
  | 124 => 0x148256
  | 125 => 0x149456
  | 126 => 0x25496
  | 127 => 0xd0c
  | 128 => 0xd0256
  | 129 => 0x24d16
  | 130 => 0x144b56
  | 131 => 0x148b56
  | 132 => 0x154c
  | 133 => 0x149453
  | 134 => 0x145496
  | 135 => 0xd1456
  | 136 => 0x144d16
  | 137 => 0xcd456
  | 138 => 0x144cd6
  | 139 => 0x20c
  | 140 => 0x144e96
  | 141 => 0xcce96
  | 142 => 0x18cb
  | 143 => 0x188c
  | 144 => 0x160c
  | 145 => 0x178b
  | 146 => 0x10c
  | 147 => 0x16cd
  | 148 => 0x29394
  | 149 => 0x282495e
  | 150 => 0x28954
  | 151 => 0x94294
  | 152 => 0x20251
  | 153 => 0x94255
  | 154 => 0x94256
  | 155 => 0x24211
  | 156 => 0x138255
  | 157 => 0x4253
  | 158 => 0x135453
  | 159 => 0x134253
  | 160 => 0x15393
  | 161 => 0xecd
  | 162 => 0x29453
  | 163 => 0x24293
  | 164 => 0x25493
  | 165 => 0x25853
  | 166 => 0x24bd3
  | 167 => 0x20255
  | 168 => 0x184253
  | 169 => 0x154255
  | 170 => 0x29554
  | 171 => 0x299d4
  | 172 => 0x145493
  | 173 => 0x25453
  | 174 => 0x25455
  | 175 => 0xb8294
  | 176 => 0x29494
  | 177 => 0x28214
  | 178 => 0x20294
  | 179 => 0x154294
  | 180 => 0x2c294
  | 181 => 0x19c294
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 45
  | 7 => 1190
  | 6 => 3516
  | 5 => 1626
  | 4 => 66
  | 3 => 8
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
  | 8 => packedAt gbK8 (1317+((h/21+packedAt gbK8 (1170+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (49398+((h/488+packedAt gbK7 (44030+(h % 488)*11) 11) % 1934)*12) 12
  | 6 => packedAt gbK6 (186435+((h/1359+packedAt gbK6 (168768+(h % 1359)*13) 13) % 5921)*13) 13
  | 5 => packedAt gbK5 (103590+((h/638+packedAt gbK5 (95934+(h % 638)*12) 12) % 3360)*12) 12
  | 4 => packedAt gbK4 (4774+((h/22+packedAt gbK4 (4620+(h % 22)*7) 7) % 97)*8) 8
  | 3 => packedAt gbK3 (656+((h/2+packedAt gbK3 (648+(h % 2)*4) 4) % 14)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff01ffe01f03fffc0fffffd19e78fb81f1ff
  | 1 => 0x7c03fe07fffffc0ffff03fc02e69a764fe7e7c
  | 2 => 0x8003fff8001ffff07fffc1fff071c7870f8f8f
  | 3 => 0x3ffffffe000007ffffe003f81f807f00ff0
  | 4 => 0x3ffffffffffff800000003ffe0007fff000
  | 5 => 0xfffc000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x84390029610500949402524a8082082980b0b5
  | 1 => 0x68481602ac2b44092d1024818628a36036565c
  | 2 => 0x82ab500212ab204aac8135305145860b0b0a
  | 3 => 0x2113cd9cd740218473cf38063b81f807d00de0
  | 4 => 0x4223f1e71b9cf3ce008610183dfe0007ede000
  | 5 => 0x73c081001c00c208030820203f7df6d0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeaeaece8e8a0eeeaeaeaece8e8a0eeeaeaeaece8e8a0eeeaeaeaece8e8a0eeeaeaeaece8e8a0eeeaeaeaece8e8a0eeeaeaeaece8e8a0eeeaeaeaece8e8a0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36733
namespace PEqualNP.Outside.L_meta_36733
open PEqualNP.Outside.L_meta_36733.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 6 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 14 := bs0_4_0
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
theorem bs1_1_0 : Interval s1Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_1 : Interval s1Atlas 1 0 1 := bs1_1_0
theorem alls1 : ∀ k ≤ 1, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_1 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 24 := bs2_3_0
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
theorem bs2_4_96 : Interval s2Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 117 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96))
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
theorem bs3_2_0 : Interval s3Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 6 := bs3_2_0
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
theorem bs3_4_64 : Interval s3Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 90 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 6 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 90 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
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
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 14 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 85 := (concat bs5_3_0 (concat bs5_3_32 bs5_3_64))
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
theorem bs5_4_736 : Interval s5Atlas 4 736 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 754 := (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat bs5_4_288 (concat bs5_4_320 bs5_4_352)))) (concat (concat (concat bs5_4_384 (concat bs5_4_416 bs5_4_448)) (concat bs5_4_480 (concat bs5_4_512 bs5_4_544))) (concat (concat bs5_4_576 (concat bs5_4_608 bs5_4_640)) (concat bs5_4_672 (concat bs5_4_704 bs5_4_736)))))
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
theorem bs5_5_768 : Interval s5Atlas 5 768 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 779 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat bs5_5_96 (concat bs5_5_128 bs5_5_160))) (concat (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)) (concat bs5_5_288 (concat bs5_5_320 bs5_5_352)))) (concat (concat (concat bs5_5_384 (concat bs5_5_416 bs5_5_448)) (concat bs5_5_480 (concat bs5_5_512 bs5_5_544))) (concat (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)) (concat (concat bs5_5_672 bs5_5_704) (concat bs5_5_736 bs5_5_768)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 8 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 66 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_1600 : Interval gbAtlas 5 1600 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1626 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))))) (concat (concat (concat (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960))) (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184)))) (concat (concat (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280)) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376))) (concat (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 bgb_5_1600))))))
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
theorem bgb_6_3488 : Interval gbAtlas 6 3488 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3516 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608))) (concat (concat bgb_6_640 (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832))))) (concat (concat (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 bgb_6_1056))) (concat (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)) (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)))) (concat (concat (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)))))) (concat (concat (concat (concat (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824)) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920))) (concat (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016)) (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 bgb_6_2144)))) (concat (concat (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368))) (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592))))) (concat (concat (concat (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816))) (concat (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)) (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 bgb_6_3040)))) (concat (concat (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136)) (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 bgb_6_3264))) (concat (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360)) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488)))))))
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
theorem bgb_7_1184 : Interval gbAtlas 7 1184 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1190 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 (concat bgb_7_384 bgb_7_416))) (concat (concat bgb_7_448 bgb_7_480) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))))) (concat (concat (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 (concat bgb_7_832 bgb_7_864)))) (concat (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024))) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 45 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 2 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaeaece8e8a0eeeaeaeaece8e8a0eeeaeaeaece8e8a0eeeaeaeaece8e8a0eeeaeaeaece8e8a0eeeaeaeaece8e8a0eeeaeaeaece8e8a0eeeaeaeaece8e8a0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 26 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372970 * 2 ^ 32 + 3974686880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36733.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.or,[4,6]⟩,⟨.and,[1,7]⟩,⟨.or,[4,5]⟩,⟨.and,[6,9]⟩,⟨.or,[2,5]⟩,⟨.or,[3,10]⟩,⟨.and,[6,11]⟩,⟨.and,[0,13]⟩,⟨.and,[8,12]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 3974686880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 3974686880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36733

open PEqualNP.Outside.L_meta_36733 in
theorem PEqualNP.Outside.L_meta_36733 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 3974686880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 3974686880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
