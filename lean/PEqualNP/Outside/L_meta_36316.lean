import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36316.Model
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


end PEqualNP.Outside.L_meta_36316.Model

namespace PEqualNP.Outside.L_meta_36316
open PEqualNP.Outside.L_meta_36316.Model
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

def SBf (j : Nat) : Nat := [7, 7, 5, 5, 7, 7].getD j 0

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

def mirrorSteps : List Move := [swapRows 50]

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

end PEqualNP.Outside.L_meta_36316

namespace PEqualNP.Outside.L_meta_36316
open PEqualNP.Outside.L_meta_36316.Model
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
end PEqualNP.Outside.L_meta_36316
namespace PEqualNP.Outside.L_meta_36316
open PEqualNP.Outside.L_meta_36316.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x102a08f00246d09650bd1991e34008280000a222d5974a4c380340c006301002a5a8922c029ce003a006201c7c02912b82a600280080002080340040043600ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x24800b25f1709400043401c60003b898002d000f80000268008e0000000b081000cc000000070da14000f0c21d001200031018790800151149e0000000f0670d00050632082400402192c987c00030423f2d800f46a34808ec15149b816853f0d8de0f1395422710d9942e561794c48192f1481c602e0f4885a1c918684a4107c5679009d0fa83330d4e02c100e8ea18000010057068ec00000408c0c510004cd612361380a00280004464050000000310006e0019000e4100005870423d9fc00002a000005d3980400b8000400503408007c040c040408004c000804382c000c54000c182074040808080008003c0814100042baa921d794a43af28c875d5090f3ea8a1d714943ae28a875f5050ebca621d794f42aea9e859d43d0aeca3a15d54742afa9a855c5350b3a86a15794c42aea98855f548cabaa9195794a32af28c655d508ca7ca8194f55032afaa0659e540cabaa81967550328eaa0655e520cb9ca4195794432aea80655e53d06baa7a0e750f41b7296836d52d06bea6a0d714d41cea1a835e53106baa620d7d5231aeaa4635e528c6bca318d7542319f2a0633d540c6bea818e795031aeaa0639d540c63aa818d794831af28863d6510c6baa018cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710d7d4d21ae29a435f53086b8a610f948421af29e815d53d02bca7205754e40cea1c815e53102baa6206750c40b7290816d52102eca2205d544409f2a6613d54cc2bea9986795330aeaa6619d54cc23aa9985794b30af28e615d538c2bea8985755130ae292615c514c3b6a0985794c30afa9e415c53c82bca7105754e209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d54420afa9e215c53c42bca7085754e109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x78089400001a81600810002c00a6009a4000000032330012000a9000001c00e00002e006002000a000000000050000c00c1c550d51d0a8c6250d4295987548ca1d649463287d91508ca1d6595032c350d52d06946150d419398b548c61d6494a3187d91508c61d659503187590534861d6414c2196580530870d4354840c550d511024c625513095185544c21d641493087590514c21d6494c308759053c821d6494e208759053c421d6494e10
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s1K5 (864+((h/16+packedAt s1K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s1K4 (3970+((h/44+packedAt s1K4 (3618+(h % 44)*8) 8) % 177)*9) 9
  | 3 => packedAt s1K3 (1036+((h/8+packedAt s1K3 (988+(h % 8)*6) 6) % 58)*6) 6
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x1fffffc1ffffff81fffe0ffff83ffffe78f1ff
  | 2 => 0xe07e0ffe0ffe1ffe1e0ff0f07fc3f83fa74e73
  | 3 => 0xff800ffff07fe1ffe00fff007ffc3fc1c78f9c
  | 4 => 0xfffff8001fffff000007fffc001f80fe0
  | 5 => 0xfffff000000001ffffffffff80000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x20800440004000022100111100449080810a5
  | 2 => 0x49149488652830960c8690a22a4290b4a34652
  | 3 => 0x85252910a351032ac10b2a044ca82685458b18
  | 4 => 0xd659ce254a1d55cd77a1888977330319f80de0
  | 5 => 0x18618c398c6199f199cdccce06220421f6e000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaa0aaa0faaafaaafaa0aaa0faaafaaafaa0aaa0faaafaaafaa0aaa0faaafaaafaa0aaa0faaafaaafaa0aaa0faaafaaafaa0aaa0faaafaaafaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36316
namespace PEqualNP.Outside.L_meta_36316
open PEqualNP.Outside.L_meta_36316.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1ffffc0ff0f87c3fc3f87fff87f0383e99f793
  | 1 => 0xe0787ff0ffff87c3fc3f8703f87fffc166c9fc
  | 3 => 0xff807fff00fffffc003ff803ff803fff870e1f
  | 4 => 0x7fffff0007ffffc00003ffffc001f80fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4310046201108004c04809198091888c085391
  | 1 => 0x490088a240400881441882288824928422c0b4
  | 3 => 0x842551042aa445582225504255022531850c0a
  | 4 => 0x96566248a835566eaa844093664b0119d80f40
  | 5 => 0x1864438cccc667b3333664e0440c0621f7a000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36316
namespace PEqualNP.Outside.L_meta_36316
open PEqualNP.Outside.L_meta_36316.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1ffffc0ff0f87c3fc3f87fff87f0383e99f793
  | 1 => 0xe0787ff0ffff87c3fc3f8703f87fffc166c9fc
  | 2 => 0xff807fff00fffffc003ff803ff803fff870e1f
  | 4 => 0x7fffff0007ffffc00003ffffc001f80fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4310046201108004c04809198091888c085391
  | 1 => 0x490088a240400881441882288824928422c0b4
  | 2 => 0x842551042aa445582225504255022531850c0a
  | 4 => 0x96566248a835566eaa844093664b0119d80f40
  | 5 => 0x1864438cccc667b3333664e0440c0621f7a000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36316
namespace PEqualNP.Outside.L_meta_36316
open PEqualNP.Outside.L_meta_36316.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x3800d0000000001838a90006ce800000991004800048581883c000a10ea40282860000327c002000000040007844c0128b4e0002300340090a18000000000a4400b800000001000200003000c002000400bff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x58000001d1b00159a00098717800f1c949b900d001400000000000000000013000000000000000000002080021e00000000000000001398801080000c83800003190a00000000000000169d9e80000000091f8000128c0000000012001700000007841c150f80000002800e0e8b000000000d8000001a9f0019800000008000000b85000000110000000011868881849800061608200a8100000000000000000000014000000000004000410000814000c1c00000c0012dca521db54a43af29c855d5390a7ca9994f553329f2a4653d548caeea2995d14532e6990657a50906f2a120cf950319eaa0636e520c6daa418de94031bca80633e540867aa810d794c21aea98437a50086f2a010dd94640baa8c815e53102baa6205b94840b6a90817651102eaa2205d94630baa8c613f544c278a8984f950309eaa0616e520c2daa4185d94430baa88617651882eaa3104fd51209e2a2413e540827aa8105794c20aea98417651082eaa2104f953109eaa621b654c436aa9885d54610f9a8221f340443e080887c8c110f898221f220443e240885d94410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x802a6400039c580514cab264d4110b458c40442e16210110ac19130442b06448110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 42
  | 4 => 66
  | 3 => 6
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
  | 5 => packedAt s4K5 (770+((h/14+packedAt s4K5 (672+(h % 14)*7) 7) % 80)*7) 7
  | 4 => packedAt s4K4 (1958+((h/22+packedAt s4K4 (1782+(h % 22)*8) 8) % 166)*8) 8
  | 3 => packedAt s4K3 (236+((h/2+packedAt s4K3 (228+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3fe1fffc1fe3f8e1c71f8fff8fc1fc1e09f673
  | 1 => 0xc1fe0e3fe1fc7f1e07e3f1c1f1fe1fe036cb9c
  | 2 => 0x1fff03ffe007ffff803fe01fe001fffc70c1f
  | 3 => 0xfe00003fffff801ffffc0001ffffe001f80fe0
  | 5 => 0xffffffc00000001ffffffffe00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x84242004440401000104824482444444005231
  | 1 => 0x9444a048c480a0240321908c9094494412c294
  | 2 => 0x288844910849500ac802241124089298c50c0a
  | 3 => 0x8194922114012535448002149298089680d40
  | 5 => 0x31118c039992649da693493800310311bfa000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaeee0eee0feeafeeaeee0eee0feeafeeaeee0eee0feeafeeaeee0eee0feeafeeaeee0eee0feeafeeaeee0eee0feeafeeaeee0eee0feeafeeaeee0eee0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36316
namespace PEqualNP.Outside.L_meta_36316
open PEqualNP.Outside.L_meta_36316.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x30012381d400165939a1298a2036900001c0009e00840004610a85321949f14006970060003003ce80008898022208024a0000450000430820c244bff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fa10fd10f910fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x6e5600101a1e7a5e2e7664406c3c52002a0482266838002042184830006000580a000234220c4e740600281c62780050162c7232084a00465a4414000e365400007c4c5c70806a3a7e0012243e6600021c0061c082800e00180000048034000a81006dca521db54a43af29c855d5390a7ca9994f553329f2a4653d548caf6a0995e14132e6990657a50906f2a120d794c41aea98836e52106daa420de94041bca80837a508c6f2a118cfd51319e2a2633e540c67aa818db94831b6a90637a500c6f2a018de94221bca84433f5448678a890cf950219eaa0435e53086baa610de94021bca80437651902eaa3204f950309eaa0616e520c2daa4185d94430baa88613e540827aa8105794c20aea98417651082eaa2104f952109eaa421ba5484372a9085e54610f9a8a21f341443e082887c8c510f898a21f221443e242885e94010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x28018a10039c584504cab264d4510b458c41442e16210510ac19131442b06448510
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 42
  | 4 => 66
  | 3 => 6
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
  | 5 => packedAt s5K5 (756+((h/14+packedAt s5K5 (672+(h % 14)*6) 6) % 56)*7) 7
  | 4 => packedAt s5K4 (1936+((h/22+packedAt s5K4 (1782+(h % 22)*7) 7) % 80)*8) 8
  | 3 => packedAt s5K3 (234+((h/2+packedAt s5K3 (228+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1fe0fe3c3fe3f8e3c71f8fc18fc3fc3e1bc673
  | 1 => 0xe1ff0fffc1fc7f1c07e3f1fff1fc1fc024fb9c
  | 2 => 0x1fff03ffe007ffff803fe01fe001fffc70c1f
  | 3 => 0xfe00003fffff801ffffc0001ffffe001f80fe0
  | 4 => 0xffffffc00000001ffffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x442a20448c8421008305824c8249449409c231
  | 1 => 0x44422008840080200120908490884884005294
  | 2 => 0x988444911049500d4802241124109328c60c0a
  | 3 => 0x8814c922214012565448002149328109700d40
  | 4 => 0x11188c033992649ba693493800230231bfa000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeceee0feeceee0feeceee0feeceee0feeceee0feeceee0feeceee0feeceee0feeceee0feeceee0feeceee0feeceee0feeceee0feeceee0feeceee0feeceee0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36316
namespace PEqualNP.Outside.L_meta_36316
open PEqualNP.Outside.L_meta_36316.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x20004a0184800a83143914d0400fa6a0005800012025b83d06347162843a9401b00009c00201380001e321d41b300241d4160044024808461fbc6549a21508d3107ab890000000000000000011070806085010000406140008e0214000000409ff5401ff95001fd5401ff15009ff52007f94801fd52027f14807ff42007f90801fd4201ff10801fe32007f4c801fc32027fd4405fe51007f54405fc5101ffd0405fe41007f50405fc41007fc8405fe21007f48405fc21027fd4003fe50007f54003fc5001ffd0003fe40007f50003fc40007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x8e400bff14720067fe839002ffe41c8001fea0e400bff10720007fe639002ffe31c8001fe98e400bff0c720057fe439002ffe21c8001fe90e400aff0872000dfac190007ff50c8003ff2864001ff5432000ff8a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1864001ff0c32000ffc4190007ee20c8003fd1064001ff0832000fd84190007ff10c8003ff0864001ff04320007feca90002ff6548001bfb2a40009fd952004ffcca90012fe6548001feb2a4000bf5952004ff8ca90012fc6548001be32a40049f19520007fec890002ff6448011ff3224003bf99120007fac890002fd6448011fe3224003bf1912004ffea890023fe5448001feaa24008ff15120007fec690002ff6348001ff31a4000bf98d20007fac690002fd6348001fe31a4000bf18d2004ffea690003fe5348001fea9a4009ff14d20047fe8690003fe4348001fea1a4008ff10d2000dfec490027ff5248001ff2924000fb94920007faa490003ed5248013fe2924008ffd0920007fc8490003fd4248011fe2124000ffcc920007fc6490003ee3248001fe9924000fb4c920007f86490003ff61480017fb0a4007ff98520015fcc290003fd614800ffe30a4002bf1852004ffea29001ffe5148001fea8a4007ff14520047fe829001ffe4148001fea0a4007ff10520007fe629001ffe3148001fe98a4007ff0c520007fe429001ffe2148001fe90a4007ff0852000dfec090007ff5048003ff2824001ff5412000ff8a090007ff4048003ff2024001ff5012000ff88090007ff3048003ff1824001ff4c12000ff86090007ff2048001fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffe2090007fe1048003fd0824001ff04120007feca88002ff654400bff32a2004bf99510007faca88002fd654400bfe32a2004bf19510007fec888002ff644400dff3222003bf99110007fac888002fd644400dfe3222003bf1911002ffea88801bfe5444001feaa22006ff15110007fec488002ff6244001ff3122000bf98910007fac488002fd6244001fe3122000bf1891002ffea488003fe5244001fea922005ff14910037fe8488003fe4244001fea122006ff10910007fc6488003fd3244001fe1922001bfd8510017fea28800bfe5144005fb28a2002ff54510007eaa28800bfc5144005ffa0a2006fdd0510017fc828800bfd4144005fe20a2002fd10510017fe428800bfe2144005fb10a2002ff48510007ea428800bfc21440037fb022001ffd411002ff6a088007fe5044003fea822001ff1411000ff0a088007ff4044003ff2022001fe9011000ffa8088003f94044003fe2022001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3ff60484017fb024212ff9812100dfcc090803fd6048425fe3024201bf181210a7fea09084bfe5048425fe2824213ffd0121097fc809084bfc4048425ff1824212ff0c121097fc409084bfc2048405ff8824202fdc4121017fc209080bfc10484037fb2aa000ffd9150005fec8a8047fe64540077f322a000ff5915008ff8c8a800efc6454009ffaa2a004ff95150027faa8a8013fc5454001ffb12a000bfd8950007fcc4a8003fd6254001fe312a000bf18950027fea4a80137f5254009ff292a004ff54950006faa4a8013fc5254023ffa12a000ff90950007fa84a8047fc4254001ff192a000ff4c950007f864a8003ff61540017fb0aa010ff98550015fcc2a8003fd6154021fe30aa002bf18550027fea2a8013fe5154009fea8aa004ff1455008ffe82a8043fe4154001fea0aa010ff10550007fe42a8043fe2154001fe90aa010ff0855000dfec0a8007ff5054009fda82a001ff9415000efca0a8007fc5054003be282a001fe1415000ffe80a8007fe4054003fe202a001ff8815000ff840a8007ff1054003ff082a001ff04150007fecaa0002ff655001fff32a8004bf99540007facaa0002fd655001ffe32a8004bf1954000dfec8a000fff5450007ff2a28003ef9514001ffaa8a0003bd5450007fe2a28000ffd8940005fec4a0003fe6250001feb128000ff18940005f8c4a003fff5250001ff2928000ff5494007ff8a4a000fff4250007dfa128003ff9094001ffa84a0003bd4250007fe2128000ff8c940007fa64a0003fc3250001ffb0a8000bfd8540077fcc2a000afe6150001feb0a800eff18540015f8c2a003fff515001dff28a8000ff54540077f8a2a000fff4150007ff20a800eef9054001ffa82a000ffc4150007de20a8000ffc8540077fc42a0003fd215001dfe10a8001bfd814000ffea0a0007fe5050003fea828001ff1414000ffe80a000ffb4050003ff2028001ef9014000ff880a0007bc4050003fc2028001ff8814000ff840a0007ff1050003ff0828001fe8414000ff820a002bff65c80017fb2e400dff99720025fccb90003fd65c80017eb2e400aff19720025f8cb9002bff64c80017fb26400cff9932001dfcc990003fd64c80017eb26400aff1932001df8c990037ff54c8019ff2a64000ff55320067f8a99002bff63c8001ff31e4000bf98f20007fac790002fd63c8015fe31e4000bf18f2006ffea790003fe53c8001fea9e400dff14f20067fe8790003fe43c8001fea1e400cff10f2000dfcc590037ff52c8015ff2964000fb94b20007faa590003ed52c8015fe296400cffd0b20057fc8590003fd42c8015fe2164000ffccb20057fc6590003ee32c8001fe9964000fb4cb20057f8659002bff61c8017ff30e4002bf98720007fac390002fd61c8015fe30e4002bf1872006ffea39002ffe51c8001fea
  | 2 => 0x4101ffea8a080ffe5450407feaa28203ff15141007fec4a0802ff6250401ff3128200ff58941007f8c4a0802fc6250433ffa928200ff94941007faa4a0867fc5250407ffa128203efd094101ffc84a080ffd4250401dea128203ff10941007fc64a0803fd3250401fe1928202bfd8541017fea2a080bfe5150405fea8a8202ff14541017fe82a080ff74150405ff20a8202ef90541017f882a080bbc4150405fa20a8202ff88541017f842a0803ff60504017fb028218ff9814100dfcc0a0803fd6050431fe3028201bf181410cffea0a0863fe5050431fe2828203ffd014101ffc80a080ffc4050431ff1028218ff08141017fe20a080bfe1050405fe082820affd9721005fecb9085ffe65c84097f32e4200ff59721005facb9082bfc65c84097e32e420affd9321005fec99085bfe64c84077f3264200ff59321005fac99082bfc64c84077e3264217ffd53210b7fca990803fd54c842dfe2a6420affd8f21007fcc790802fe63c8401feb1e4200bf58f21057f8c790802fc63c842fffa9e4200ff94f21007faa79085ffc53c842dffa1e4200ff90f21007fa879085bfc43c84057f3164217ffd4b21057fca590803fd52c8415fe2964216ffd0b21057fc8590803ee42c8401fea164200fb50b21057f88590803ff32c8415ff1964200fb8cb21007fa6590803ed32c8415fe1964202bf58721017fea39080bfe51c8405fea8e4202ff14721017fe839080bfe41c8405fea0e4202ff10721017fe639080bfe31c8405fe18e4202ff88721017dc439080bf621c8405fe10e4202fb08721057fec190857fe60c84037f3064200ff58321005fac19082bfc60c84037e3064217ffd43210affca190857fc50c842dffa064215ff903210aff88190857fe30c842bfe1864215ff88321057f8419080bff10c8405ff0864202ff04321007feca90802ff6548429ff32a4204bf99521007faca90802fd6548429fe32a4204bf19521007fec890802ff6448401dfb224200afd912109ffcc89080efe6448401feb224200bf5912109ff8c89080efc6448401de3224203af191210a7fea89084ffe5448401feaa24213ff15121007fec690802ff6348401ff31a4200bf98d21007fac690802fd6348401fe31a4200bf18d210a7fea690803fe5348401fea9a4214ff14d2109ffe8690803fe4348401fea1a4213ff10d21015fec490853ff5248401ff2924200ff549210a7f8a49084fff4248401ff2124200fb90921007fa8490803ed4248427fe2124200ffcc921007fc6490803ee3248401fe9924200fb4c921007f8649080aff6148405ffa8a4202ff94521017faa29080bfc5148405ffa0a4202ff90521017fa829080bfc4148405ff98a4202ff8c521017fa629080bfc3148405ff90a4200fdc8521017fc429080bee2148405fe10a4202fb08521017e8429080
  | 3 => 0xeb04640aff1823200df8c11909fff508c849ff2846424ff14232137fe8119093fe408c849fe2046424ff8c232127f86119093fe208c815fe1046425ffc4232127fc2119093fc108c801ffb2a6400bfd953211ffcca99012fe654c801feb2a6400bf5953211ff8ca99012fc654c801ffb226400bfd9132117fcc89900efe644c801feb226400bf59132117f8c89900efc644c847ffaa26422ff95132007faa89908bfc544c847ffa926400ff94932007faa49908ffc524c845ffa126400ff90932007fa849908bfc424c801ff1926400f78c932007fec299002ff614c843ff30a6402bf98532007fac299087fc614c8057e30a6423ffd453210ffca299087fc514c845ffa0a6421ff9053210ff88299087fe214c843fe10a6400ffd8132005fec099083fe604c8037f3026400ff58132107f8c099006fc604c847ffa826420ff94132107f8a09908bff404c841ff2026420ff10132107fc4099083fc204c843ff8826420ff84132107f8209902bff650c8017fb28641fff99432025fcca19003fd650c8017eb28640aff19432025f8ca1902bff640c8017fb20641eff9903201dfcc819003fd640c8017eb20640aff1903201df8c81907fff540c83dff2a06400ff550320f7f8a819002fe620c83fffa90640aff94832007faa41902bfc520c83dffa10640aff90832007fa841902bfc420c815ff1906400fb8c832007fa6419003ed320c801e6990640affd84320effcc21900afe610c801feb086400bf58432057f8c21900afc610c83fffa88641dff944320eff8a21907bff410c83bff208641dff104320effc421902bfc210c815ffb00641cff9803200dfcc019003fd600c8017eb00640aff1803200df8c01907fff500c839ff280641cff140320f7fe8019073fe400c839fe200641cff88032057f84019077ff100c839ff080641cff04032015fecaa8803ff64544017fb22a21bff9915101dfcc8a8803fd6454437fe322a203bf19151027fea8a88137f5454409ff2a2a204ff55151006faa8a8813fc5454401ffb12a200bfd8951007fcc4a8803fd6254401fe312a200bf18951027fea4a88137f5254409ff292a204ff54951006faa4a8813fc5254437ffa12a200ff90951007fa84a886ffc4254401ff192a200ff4c951007f864a880aff6154405ffa8aa204fdd4551017fca2a880b7e5154405fe28aa202df14551017e8a2a880bff4154405ff20aa202ff10551017fc42a880bfc2154401ffb02a200bfd81510d7fcc0a8806fe6054401feb02a21aff1815100df8c0a8813ff5054409ff282a21adf94151027f8a0a88137c5054437ffa02a21aff901510d7f880a886bfe2054435fe102a202ffc4151017ee20a880bfe1054405fe082a200ffd9541005fecaa0867fe65504097f32a8200ff59541005facaa0867fc65504097e32a8202bfd91
  | 4 => 0x2bfc65908097e32c8403bf5924201ffea92100ffe5490807feaa48403ff15242057fec721003fe63908017f31c8400ff58e42005fac72102bfc639085bffa9c8400ff94e42007faa7210b7fc5390807ffa1c8403efd0e4201ffc872100ffc43908077f314842dffd4a42057fca521003fd5290815fe2948403ffd0a4201f7e852100fef4290815fe2148403fb10a42057fec3210b3fe61908057f30c8400ff58642005fac32102bfc61908057e30c842dffd4642167fca3210b3fc5190807ffa0c8403ff906421677c832100ffc4190807de20c842cff8c642167f863210b3fe2190815fe10c840affd824215ffcc121006fe6090801feb048400bf58242057f8c121006fc609085bffa84842bff9424215ff8a12100fff4090807ff2048403ff1024215ffc61210affc3090857ff104840aff08242167fe21210affe1090857fe0848400ffd9542005fecaa10abfe65508097f32a8400ff59542005facaa10abfc65508097e32a8403bfd914201ffea8a100ffe5450807df2a28403ff551420077aa8a100ffc5450801ffb1a8400bfd8d42007fcc6a1003fd6350801fe31a8400bf18d42157fea6a1003fe5350801fea9a842aff14d4201ffe86a100ffe4350801df21a8403ff50d4201ff886a100fbc43508077fb12842affd4942007fca4a1003fd5250855fe2928403ffd094201fde84a100ffe4250801df2128403ff1094201f7884a100fec4250801ffb0a8400bfd854214ffcc2a100afe6150801feb0a8429ff18542015f8c2a10abff5150853ff28a8429ff1454201ffe82a100fbf4150807ff20a8403ff1054214ffc62a10a7fc3150853ff10a8429ff08542007fec0a1002ff6050851ff3028401bf98142007fac0a10a3fc60508037e302842affd4142147fca0a10a3fc5050807ffa028403efd014201ffc80a100ffc4050851ff1828428ff0c142147fc40a10a3fc2050853ff8828428ff84142147f820a102bff658c8017fb2c6427ff99632025fccb190037e658c8093f32c6400ff59632005facb190037d658c8013eb2c640aff19632025f8cb1902bff648c8017fb246426ff9923201dfcc919003be648c8075f3246400ff59232005fac919003bd648c8015eb24640aff1923201df8c91909fff548c84dff2a46400ff55232137f8a919002fd638c84fffa9c6400ff94e32007faa71909ffc538c84dffa1c6400ff90e32007fa871909bfc438c8017f3146427ffd4a32057fca519003fd528c815fe2946426ffd0a32057fc8519003fd428c815fe2146400ffcca32007de651902bff618c84bff30c6402bf98632007fac319002fd618c815fe30c6402bf1863213ffea319097fe518c84bfe28c6426ffd063212ffc8319097fc418c84bff18c6425ff0c63212ffc431902bfc218c815ffb046424ff9823200dfcc119003fd608c8017
  | 5 => 0x800400002800001000401e01400000801000000200000000002800001202000200203bfd955401dfec8aa00fff5455009dfaa2a803ff9515401efca8aa00ffc5455007be2a2a803ef15154007fec4aa002ff6255001ff312a800ff58954007f8c4aa002fc6255009ffa92a804dfd4954027f8a4aa00fff4255007dfa12a803ff10954007fec2aa002ff615506bff30aa802bf98554007fac2aa0d7fc61550057e30aa804ffd4554026fea2aa013fe5155009fe28aa803ffd055401ffc82aa0d7be4155007fe20aa803ef105541affc42aa0d7fc2155001ffb02a800bfd81541a7fcc0aa006fe6055001feb02a834ff1815400df8c0aa013ff5055009ff282a834df94154027f8a0aa0137c5055007ffa02a803efd015401ffc80aa00ffc4055069ff102a834ff081541affe20aa0d3fe1055069fe082a804bf59652057fec9290cffe64948077f324a400ff59252005fac92902bfc64948077e324a404ffd5252027fca929013fd5494809fe2a4a40affd8e52007fcc729002fe6394801feb1ca400bf58e52057f8c729013ff5394809bfa9ca404ff94e52027f8a7290cfff4394867fe21ca404bf98a52027fea5290137f5294809f7a94a40aff14a52027d8a5290cfff4294815fe214a40affd8652197fcc32900afe6194801feb0ca400bf58652057f8c32900afc6194809ffa8ca404ff94652027f8a3290cfff4194865ff20ca432ff10652197fc63290cbfc3194865ff10ca40aff08652057fec1290c7fe60948037f304a400ff58252005fac12902bfc60948037e304a404ffd4252027fca1290c77e5094809fe284a404df1425219ffe81290c7fe4094863fe204a431ff8c25218ff861290c7fe2094815fe104a432ffc425218ffc21290c7fc10948097fb2aa400ffd9152005fec8a90c3fe64548077f322a400ff59152187f8c8a900efc6454809ffaa2a404dfd5152027fca8a9013fd5454801beaa2a404ff15152007fec6a9002ff6354801ff31aa400ff58d52007f8c6a9002fc6354809ffa9aa404ff94d52006fca6a9013fd5354809fe29aa404df14d52187fe86a90c3fc43548097fb12a404ffd4952027dea4a9013fe5254801bf292a404ff14952026f8a4a9013ec5254861ffa12a430ff10952007fec2a9002ff615485fff30aa402bf98552007fac2a90bffc61548057e30aa404ffd4552026fea2a9013fe5154809fe28aa430ffd055217ffc82a90bffc415485fff18aa42fff0c55217ffc42a90bffc2154801ffb02a400bfd8152177fcc0a9006fe6054801feb02a42eff1815200df8c0a9013ff5054809bfa82a404ff94152027f8a0a90c3ff405485dff202a42eff10152177fc60a90bbfc305485dff102a42eff0815217ffe20a90bbfe105485dfe082a40affd9642005fecb210b7fe65908097f32c8400ff59642005facb21
  | 6 => 0xb0dcc90459800111458c0000003a6ce87b52e0000000ffeea80000000000002d82c40012c00000006381d8ba2d59390a743649cc0000000000004284b4e04a3065e00000000015832000074c8fc5340005de368294b4a560000834bb4024708000d0c86c000b887c914501400072caf4001304000208f80000001484000000a700000000002f4724001408001388a26420ef4c2a45806806c03129d16052a00053c0000000007b20d8d7c0000000000000000011407f0fa48c4484000000684000000ed0000000bf0d5cc220000005da0000007348fe0008845c8a1a62051e93c18543d06c9c00000000000008a545a0000000ce00035689c0006fc00099200116c000e2cb2c92800000047e1a40010f400200000c02000600200c00000c00600201400400000a00c00e00600200000200000400200000400800205000800600400200000000400000400000001600001602a00400200200400000001401200200600400200004c00400400001200402200001200200000000000400200000000801800000801200000000400000e01a00800800800e00200000000a00c00e01c01800c00000600200000000800c00202000e01000200600c00c00200400400000000400200e00000000000a01800000000e00600600000600600601200200400001000400a00200400200200000201400200000e00800001600a01000002401e00000000c00000600e00c00e00200002a00600000000400400400200401c00800400000000c00400402c02201200200601a00e00400200001000000400001c00000000000600000400000000400600000200200202400200800800003800400c00400000002a06a00200a00c00000800000000601001002402000000000000a00400400000000a00e00400c00000000000400600e00200804200002400201a00602600200e00400a00000200600e01a00000000800a00000600c00600203a00a00200002001200e01200200400400401a00000000000000002201e00000400600400600400000002600800000c00a00c00000000000e02001000400e00002a00200400c00000400000a00200204200001000000000c00200000600000200800200000c00000400000000200600600201000802400000800602000000600201200000200a00400400200600600400400201200601000c00203600800000600001c00600a00201200000202e00601800200000e00c02002800200001800200200600400600800600c01c00002200200400800400200000400800c00000200a00001400a00200200400402400000a00e00200404400000000a00800600200600000000000000000c00000400c00200004801c00000a00c01800000800000607201000200200400a00600200200601000200000200001c00600000c006006002002
  | 7 => 0x65c7286263f40009acf18000f9800047142d2012424be4ac660a08e90e980384460003fc5e0e7cd54a851740002560013680004ec50c00000095800111c760810da4e4053eb74000004001094632218000ed4000cf0ab0f3cb58c10ca000007a75340f0d50b538000057c8a0000a4ab253e8a94d4c060f0d18cb990e90447046954785ac0000b80006e501e0000000000003a872ee5e001020000000000000000646e551b0c380010c00013f4266f508d93ac00097806e000000000000a3b476b440000008b71e8118af800000000000105c0000000000011fc0000000000000000000000000000013949f0000b8c14518400000000000000025af70fc802a608000e6e948cae71cf147cc2a8e6c4dc0000000012800000009e00004b91c8001329080678000000e7415c64c0004d0fd800072060c000cc0000b48234ea07a1189054bde558bc0212b33278bb843d289494e631a858833ce202f8c1d42469c278ee80987c4d2ab3e7b910f098f286a00700012a01cc5908946014189400008f4864000000000b460004c00000003c40000000001ac858cfc00000000124127129435d340001151154000a46000898eb65bc001254000000668fb0000000c610fceb400000059c00091305863400000000000146c824000000a6c0009380008146b407c00000000000065a5d72640011102b10dc1c8154000000000a5c0001a8020000200000970eec00000000021400000147ecd00000000005684cc3586c8000c68fe80000000012206e8ef8000000000000000000000bec2a49e4338ce52d12fcff92509bc73d3d83a4f786dc0014004d42e0fa00007810ccd4107c000000a54988838cc80000f05847874980884fc0010f04747b010c55d1643905c400003cda07300e6000000000000000f302aa00000084c00000000000141c642b52c4800008ce45260d3600000050511800045cc14a900014a00008b400000064f0351712053b81f40000101048f88ca000000000000000000b2879623854aad416c148000d8854ea007a43844f04081e0996000a4ed2e1b45422828a8caa0008a71300000004820007bc000000000001040fe09a80010e03c937030931cc8c0006666f40002d078acccfd43700000000000004a834461400000130c000000774000000000000a04df4c7cfdcc58b093c602e508dc902ca22e1ca1238c77c000f74a3ed24516adf0281bc9b8000c88de0bc4000434be4000d513e44f4526ce72e547cab87434720584011ec94c9f8b1007600078cd8c868cf44e40012380012442b8b94700c5043087434c7a80b40000000012142840000008ed452a160000000c200000054400000017400000145651a00000011c00000000000000000000078400000000000027400142907400110c0a8190d781d46e146000000000000029cd006
  | 8 => 0x3760007693fcadc0010f8000000d471374800000011000013d506800000004800020e70cf403b88200000000750d8c1a54cfec000fad0ac0db4547d8224c0d38a62f27ca4546a0000000000000000007e8f580001306f023d1acba80000000000fc1709348e059e000000a34fc663e0000000000006d885c82cbe03b4c26538fcc00064a0000014489180e43cd334a4222d1b8000160716000dd030d21813c000064000a68000d0419c0000006252a8000000000000000000984001350000f7c00018080c795464fc05d2870ad046c4660dc5f46707d53a0f0000136d22d084db400115832c0003bc000000c325ec2cca50800bac0010ed2c479ce68a24000000bd0990000554000000a9c00112cd107e400852811418a47d3b4c42b1c194f3426aca471e000e280009c85b06587c64ba220000b2a000e38448fd60001d00011040000000006185fd3e05d801548890cd093a8324000f481000cd4590090c51783329153c12d83b074801d2b84681fc000f5c5cc000000bbc0011f12ece72e7937cd38000072360000e34e18ddc000fca0013000000013300000000002580000008bec45048000198e48000fe4000000000000da85780000000002a115e000b18000000b911c00ecec126cf68268d148c0000dd8a2eb80d703e8b30c78f44000c5d1d0a983291120001403e70300005327ec0000012bca367dce3cdc0000000a3c3f800136000053a000a4132400000000000000000108c6f924805cceb138954b9c818cc51a4000b20222380c4c000aacff0000a80af10a41f126a000c346a40d6d2131880ac64000ea52091e00000000011bc1e6249466b843f673e68c0de0000000000000005a48b076c000001258db800134c000000e30000bfc000f8ca4c0000000009d400063a00087c0007148040008603883d8d743ea124df891d0b0974aa0ec9088150000000000b54828000000b160000ee000000000c0400062c000000000000000000ae068800120cb4c0000008e529800042c7382f0000291468001474550081444652f94f092c8e60230168944000dbc3a2ecd01828000000088c000ee0f8519c71095efd01c547a000b006ccc3ecf8628b2200000041ce70744000000aa43c0001384000000000300000c466400012a40000012dc5a133898c00146e000000acc000b4e240b36354b6813518000000047800027000041479a000e10000450a281f8000000c20eac00075800149c0000005b88880e252c63000085128d234854000000a602c08960003d08bd44c00148c4c2000f91194e513bd148000b5cac4650018000c840001a345d0502ec28c000fa8580abc000efc0004f80000b081c0d026400000000045400000026d10807eb3c000001124d22fc4000000000000000204f108d000093a00000096c000d980000005a80005009d200
  | 9 => 0x400001ec9526746200139ca58880bd839cd2d1dc5641e90110e44b6dfcb6cc400000003e09ed3540000000000004e0ae40000009500002acd284d8552d9c7400009020000000bc570e800002fc001310d90c0806a2c814c37940ac364451c4a894913991e4690f385f11f8ac13489641085d51981280a13a4b60028cad1f4a8d32cd3c4894208ba0947f89fc27cec52d456c00c9203669d04e8464c4a6b8b513780000000000010903220004bc0000000008b800101c440000c2e97c1b10c8178f8800106479000000004cd30000244000ed8db0000cbca14000b9f284000ff4000d9540c5dc3400794305182160acf6002314c63c656032422a9a75d3f86d0dc46ec4b00000000007f40012f00003d483c000000f6c2b400025c00000000124c000c24000bcd320000edc000000cd4ab4000040ffc908ac8e58000000bda97e000c54000000cb40007540007700012305b4b0c000d26ee60000f83ed1d4930be9358000b1a4a42545e48d4e08e2e49925cceca786ac000000000674f240002e40000000010d000000017c0000000000000e0000afc138000c9095c9980000000000000005e8b383e40000000010a848c92c6c5078654fdaa2a76421c0a4d328ccbdcc80bf431039e59439922509c05466ccb800052f2ac8e8000e2400029923e394cd8d80d428301c6000bc80000007e20001c0a6536500ca1854051cbd53c8c74110cdc0351a01e400145e0000003ac1dc6bcde88dc514000e8c460000000fb8490e4c6640000d20007fc848f54000350d604249d8e94000750aec304b712f8eb938cad8374000a11000ef04c436c2d45a2000b3400040c7180000c41cf308fb43dcd44994418a2c0000000000009b4e64d192749681ec000000000530c182d25c01892904801b9450001374d689c4411410b786d5268a1d1ccd8444cb1e9a4b26bf88408909243180c0b4061c78837cce13f133c8c82bce5c3486c113c00062b1693143fa0014392f44a00f6520c9c0d49813c40000000e802cdacba4798c00438000f04d640001d60000004050a00fe0013d00005f92e8000000648c3a192000000f1c000574000d48000000a97135038050000b2ed34ca82e82880c93dcd6c54890080800000112899c67c844210df0b3a7d0746c2c879070494610000000026a0efbcd1d21ce8429691000117c9e82dcb56b140005127789dca380001a0e9c4c8330e0123c000000de47e03a0c28b42adab64f9c12c000f64000000605190000000ee5024000f2d3ccae818c000c3d04c044260a7c5d0000000001120a1ee82ba11b409c6440bf0b81206632280ea49d4709600909a14146980005220000840000000000012b4e0c00031ca208f106115c000524c983b2decc70a48a32000000000228001440d3e0005363f11d8bb07c00cac30b0463600135c6a9004
  | 10 => 0xf4cb00003146809b00f2b7cd3b3454353b020d2110032b0ebc24d3ec0faeb0e880000012cc1640c6e14a0c9f42505463347ac000c6c35edd490e9ce51103c8acf4d0bcf20aa93c34
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc765091001ebe6450910006bd6450910005f77150910015f47150910037b7415091000dfa7050910054ff768c910004fe768c910004fd768c910054fc768c91002d7e758c9100057d758c910035be748c910005bd748c910006df638c910006dc638c910056ee628c910006ed628c910015f6718c910005f5718c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c910006ee624c910006ed624c910015f6714c91000dfa704c910054ff760c910004fe760c910004fd760c910054fc760c910006ef620c910056ec620c910007cd320c910015f6710c910005f5710c91000dfa700c910005f9700c91000df47654510026f4765451000cf47654510015f77554510017777554510007776554510026f66554510026f4655451002f746554510035f67454510035f4745451002f775454510007755454510005f7725451002f775254510007755254510007f3705451000df6705451000df470545100d7f07054510016f76054510017f3605451002ff350545100d77650545100d77450545100d7f050545100d77050545100d7f240545100d7f2205451000df47648510096f4764851000cf47648510005f77548510005f57548510007b77448510035f67448510035f47448510007b47448510035b47448510005f77348510005f57348510015f77248510017e77248510007e76248510056f66248510056f46248510007e46248510007e64248510007e54248510007e63248510007e53248510007f3704851000df6704851000df47048510097f07048510016f76048510017f360485101bff35048510097f05048510097f24048510097f23048510097f22048510015f8765011001ef87650110014f8765011002dfa755011002df8755011000dfb745011000fbb7450110007bb645011001efa645011001ef86450110037b86450110037ba5450110007b95450110005fb7250110037bb4250110007b94250110007f37150110015fa7150110015f87150110077f0715011000efb615011000ff36150110077f25150110007f15150110037f34150110077ba4150110077b84150110077f04150110077b04150110077f22150110007f12150110015f8764811003ef87648110014f876481100077b754811002dfa754811002df8754811000778754811002d787548110005fb7448110005f97448110005fb7348110005f9734811000dfb724811000feb7248110007eb6248110056fa6248110056f86248110007e86248110007ea5248110007e95248110007ea3248110007e93248110007f37148110015fa7148110015f8714811003ff0714811000efb614811000ff3614811003ff25148110007f151481101b7f3414811003ff0414811003ff23148110007f1314811003ff22148110007f12148110
  | 1 => 0x9110006f77159110036f74159110076be4159110076bc4159110076f441591100c4ff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc76551100067f65551100267c6555110006bf645511001ebc6455110005f77155110015f471551101afb44155110005fb705511000df870551101a7785055110024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d89101d4fe73d8910004fd73d891000cff71d891000cfd71d89101e6ef21d89101e6ed21d8910014ff70d8910014fd70d89101deef20d89101deed20d8910094fd7698910006ef6298910095f5719891003df97098910024fe7598910004fd7598910054fc759891001cfe7498910004fd7498910054fc74989101d4fe7398910004fd7398910054fe7298910094fd7198910056f57198910056f621989100acfd7098910056f97098910056fa20989100057f755891002d7c7558910005bf7458910035bc7458910005df7358910005dc73589100adf7715891005dfb7058910004ff75589100067f75589100047f7558910024fe7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df73589101d4fc7358910006dc7358910004dc7358910006ef72589100acff7158910006f77158910094ff7058910006fb70589101dcfe761891002d7e75189100057d7518910035be7418910005bd7418910005de7318910005dd7318910006ed6218910024fe75189100567e75189100247e7518910004fd75189100567d75189100047d7518910054fc751891001cfe7418910056be741891001cbe7418910004fd7418910056bd7418910004bd7418910054fc74189101d4fe7318910056de7318910004de7318910004fd7318910056dd7318910004dd7318910054fe7218910056ee721891000cff7118910014fe711891000cfd7118910056f57118910014fc7118910056ef2118910056f621189101ceed2118910014ff701891000cfe7018910014fd7018910056f9701891000cfc7018910056ef2018910056fa20189101c6ed2018910054ff7694910004fe7694910004fd7694910054fc76949100067f65949100267c6594910015f67194910005f5719491000dfa7094910005f9709491018f785094910004ff7654910004fe7654910004fd7654910004fc76549100267e65549100067d6554910015f67154910005fb705491000df8705491002f7b5054910054ff7690910004fe7690910004fd7690910054fc7690910006bf649091001ebc6490910015f67190910005f57190910167b4419091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004f
  | 2 => 0x4fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d85201d4fe73d8520004fd73d852000cfd72d8520014fc72d8520006ee32d8520006ed32d852003ef621d852000cfe70d852000cfc70d85200aef710d85200057f755852004d7c75585200067f65585200067c6558520005bf7458520045bc7458520005df7358520005dc735852003ef46158520004ff7654520004fe7654520004fc76545200067f65545200267c65545200076d5254520004ff7650520004fe7650520004fc76505200067f65505200ce7c6550520004fe76cc520004fd76cc5201d4fc76cc5200067f65cc5202367c65cc520005ee72cc520005ed72cc520007cd32cc520004ff764c520004fe764c520004fc764c5200067f654c52022e7c654c520005bf744c520045bc744c520007cd324c5201c4fe76c85200067f65c85200be7c65c852000df870c852000cfc76485200067f65485200a67c6548520005bf7448520045bc7448520006f76148520016f46148520005fb704852000df8704852000dfa76c812000efa76c812000cfa76c81200077b65c81200077865c812000dfa72c812000fea72c812000efb62c812000feb62c8120057ea52c8120007e952c8120057ea32c8120007e932c8120005f971c8120024fe76d951002e7e65d951000dfa70d9510015f970d951002f7b50d95100d4fd75d951001cfe74d9510004fd74d951001cfc74d951002e7f54d9510054fe72d9510004fd72d951002e7c52d951000cff71d9510014fe71d951000cfd71d9510014fc71d95102267f51d95102267d51d9510014ff70d951000cfe70d9510014fd70d9510226f970d9510014f970d951000cfc70d95102167f50d951002efb50d95102167d50d9510216f850d9510024ff765951002e7c655951020df7715951021dfb70595100d7785059510214ff75595100067f7559510004ff745951001cfe745951001cfc7459510004ff7259510054fc725951002e7f525951020cff7159510006f771595100d4ff7059510006fb705951002efb50595100d67e50595100d67c50595100d6f8505951001cfe76d9110036be64d9110015f671d911000df571d9110037b741d9110024fe75d9110004fd75d9110024fc75d91100c4fd74d9110036be54d9110054fe72d9110004fd72d9110036bc42d911000cff71d9110014fe71d911000cfd71d91101f6f571d911000cf571d9110014fc71d9110206bf41d9110036f741d9110206bd41d9110206f441d9110014ff70d911000cfe70d9110014fd70d911000cfc70d91101f6bf40d91101f6bd40d911001cff7659110036bc64591101edf77159110077b441591101fdfb7059110004ff7559110024fe7559110024fc75591101f4ff7459110006bf7459110004ff7259110054fc7259110036bf42591101ecff715
  | 3 => 0xf7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d200267c6554d201d4ff7690d20004fe7690d20004fd7690d201d4fc7690d200067f6590d202667c6590d20006df6390d201d6dc6390d20005ee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d2025e7c6550d20006bf6450d2001ebc6450d20006df6350d20006dc6350d20254fe769492018e7f65949200267c6594920255ee769492024eee7694920175ed759492018f6f6594920026ee6594920026ec659492004f6c65949200266c6594920005ed739492004f6f53949200076d539492000dee709492000dec7094920056ef609492018f6e509492018f6c509492018fea1094920024ff765492000cfe7654920174fd765492000cfc76549200067f65549200267c655492004f6c5254920005fb705492000df8705492000dec7654920026ec765492000cec765492018def75549200076f75549200076f6554920026ee6554920026ec655492004f6c655492004f6f54549200076d5454920005ef73549200076e535492004f6c535492004f6f5154920007eb705492000dee705492000dec7054920177e87054920176ef60549201776f50549201776d5054920177ea1054920244fe76909200067f659092016e7c6590920057e8209092001cff765092000cfe7650920144fd765092000cfc76509200067f65509201567c6550920006bf645092001ebc6450920005fb705092000df87050920147e8205092000cfe76cc92000cfc76cc92004d7e75cc9200057d75cc9200067f65cc92023e7c65cc920045be74cc920005bd74cc920006df63cc9201d6dc63cc92000dfa70cc920005f970cc9200e4fe768c92004d7e758c9200057d758c9200067f658c92013e7c658c920045be748c920005bd748c9200e5ee768c920006ee768c920005ef758c9200076e758c920005ed758c9200076d758c9200056d758c9200076f658c9200076c658c920007ae748c920007ad748c920105ed738c9201d6ee638c9201d6ec638c92000dee708c92000dec708c920056ef608c920127ea108c9201d4ff764c92000cfe764c920104fd764c92000cfc764c9200067f654c92011e7c654c920006df634c920006dc634c920005fb704c92000df8704c92000dec764c920106ec764c92000cec764c920005ef754c920005ed754c9200076f654c9200076c654c920007cf734c920007cf634c9201d6ee634c9201d6ec634c920007cc634c920006cc634c920007eb704c92000dee704c92000dec704c920107e8704c920106ef604c920107cf304c920107cd304c920107ea104c920124fe760c9200067f650c9200fe7c650c920125ee720c920007cd320c920014fe76d85200067f65d85200067c65d852003ef661d8520024fe75d8520
  | 4 => 0x952018c7e761952004f3e741952004f3d74195200067e64195200067c64195202576d72195202567f62195200067e61195200067c61195202567f60195202576e20195202576c20195202577820195202577a101952001cfe76d91200067f65d91200067c65d9120046be64d9120024fe75d9120004fd75d9120024fc75d91201d4fe73d9120004fd73d9120046bf43d9120054fe72d912000cfd72d9120054fc72d9120046bf42d9120014fe71d9120004fd71d9120014fc71d9120006be41d9120046bc41d9120054ff70d912015cfd70d912015ebf40d912015ebd40d912015efa10d91200057f755912004d7c75591200067f65591200067c6559120046bc6459120275ef7259120004ff75591200067f75591200047f7559120024fe7559120024fc75591200067c75591200247c755912015cff7459120006bf7459120046be5459120004ff73591201d4fc7359120274ff7259120006ef7259120004ff7159120014fe7159120014fc7159120144ff7059120006fb7059120146fa1059120004ff7655120004fe7655120004fd7655120004fc76551200067f65551200267c655512001ebe6455120006bd64551200067f65d8d200067c65d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20006dc31d8d20126df30d8d20126fa10d8d2004d7e7598d200057d7598d200067f6598d200067c6598d20045be7498d20005bd7498d20006df6398d20105ed7298d20024fe7598d201d67e7598d200247e7598d20004fd7598d201d67d7598d200047d7598d201d4fc7598d2001cfe7498d201d6be7498d2001cbe7498d20004fd7498d201d6bd7498d20004bd7498d201d4fc7498d201d4fe7398d20104fd7298d201d6ed7298d20014fe7198d20004fd7198d20014fc7198d2026cfd7098d201d6f97098d200057f7558d2004d7c7558d200067f6558d200067c6558d2026def7258d20004ff7558d200067f7558d200047f7558d20024fe7558d20024fc7558d200067c7558d200247c7558d20004ff7458d2001cfe7458d2001cfc7458d20006ef7258d20004ff7158d20014fe7158d20014fc7158d20104ff7058d20006fb7058d20106fa1058d20124fe7618d200067f6518d200067c6518d20006dd6318d20024fe7518d20004fd7518d201d4fc7518d2001cfe7418d20004fd7418d201d4fc7418d201d6de7318d20054fe7218d201d6ed7218d20054fc7218d20014fe7118d20004fd7118d20014fc7118d20006de3118d201d6dc3118d20054ff7018d200e4fd7018d201d6df3018d200e6dd3018d201d4ff7694d20004fe7694d20004fd7694d201d4fc7694d200067f6594d200267c6594d20005ee7294d20005ed7294d20004f
  | 5 => 0xdec708cb2026cff764cb20057cc324cb2026def764cb20006ef764cb20005ef754cb20005ed754cb20057cf734cb20057cf634cb201d6ee634cb201d6ec634cb20057cc634cb20006cc634cb2000dee704cb2000dec704cb20107cf304cb20014ff7658720005bf7458720065bc7458720056f46158720004ff7558720024fe7558720024fc7558720004ff7458720006bf7458720004bf745872001cfe745872001cfc7458720006bc745872001cbc7458720004ff73587201d4fc7358720014fd725872000cfc7258720006ee3258720006ed3258720056f72158720056f42158720096fa2058720096f71058720004ff7654720004fd7654720054fc76547200267e65547200067d65547200076d5254720004ff7650720004fd7650720054fc765072001ebe6450720006bd64507201d4ff76cc720054fe76cc720004fd76cc7201d6de63cc720006dd63cc720055ee72cc720005ed72cc720007cd32cc720004ff764c720004fd764c720054fc764c720005bf744c720065bc744c720006de634c720006dd634c720007cd324c7201dcff7648720005bf7448720065bc7448720016f46148720024fe76d952004e7e65d952001cfe74d9520004fd74d952001cfc74d952004e7f54d95200067e54d952004e7c54d95201d4fe73d9520004fd73d952004e7f53d952004e7c53d9520054fe72d952000cfd72d9520054fc72d952004e7f52d9520014fe71d9520004fd71d9520014fc71d952004e7f51d95200067e51d952004e7c51d9520054ff70d952018cfd70d952018e7f50d952018e7d50d95202557e76d95200247e76d95200067e64d95200067c64d952018f6f72d95200067e61d95200067c61d952018f6e20d952018f6c20d952018f7820d952018f7a10d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067c43d952018e7f72d952004e7e72d952018e7d72d95200067f42d95200067c42d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067c41d95200067e31d95200067c31d95200067e21d95200067c21d952018e7f70d952018e7e70d952018e7d70d952018e7c70d952018e7f40d952018e7e40d952018e7d40d952018e7c40d952018e7f30d952018e7e30d952018e7d30d952018e7c30d952018e7f20d952018e7e20d952018e7c20d952018e7f10d952018e7e10d952018e7d10d952018e7c10d952004e7c655952027def725952018cff75595200067f7559520004ff745952001cfe745952001cfc7459520004ff73595201d4fc735952027cff7259520006ef7259520004ff7159520014fe7159520014fc7159520174ff7059520006fb705952018d7e761952004e7e761
  | 6 => 0xf7459320066be5459320004ff73593201d4fc7359320066bc435932001cff725932000cfe725932001cfd725932000cfc7259320056be4259320056bc4259320004ff7159320014fe7159320014fc7159320066bf4159320146bf4059320146bd4059320004ff7655320054fe7655320004fd7655320054fc76553200267e65553200067d655532001ebe6455320006bd645532006d7e7598f200057d7598f20065be7498f20005bd7498f20056df6398f20024fe7598f201d67e7598f200247e7598f20004fd7598f201d67d7598f200047d7598f201d4fc7598f2001cfe7498f201d6be7498f2001cbe7498f20004fd7498f201d6bd7498f20004bd7498f201d4fc7498f2000cfe7298f201d6ee7298f2000cfc7298f20056de3298f20056dc3298f20014fe7198f20004fd7198f20014fc7198f201d6df3098f2026edd3098f20056dc6358f20004ff7558f20024fe7558f20024fc7558f20004ff7458f2001cfe7458f2001cfc7458f20104fd7258f2000cfc7258f20056de3258f20056dc3258f20004ff7158f20014fe7158f20014fc7158f20106df3058f20024fe7518f20004fd7518f20054fc7518f2001cfe7418f20004fd7418f20054fc7418f20054fe7218f20056ee7218f20014fe7118f20004fd7118f20014fc7118f20056f97018f201d4ff7694f20054fe7694f20004fd7694f20054fc7694f200267e6594f200067d6594f20055ee7294f20005ed7294f20004ff7654f20004fd7654f20054fc7654f200067f6554f200267c6554f20005fb7054f2000df87054f201d4ff7690f20054fe7690f20004fd7690f20054fc7690f2001ebe6490f20006bd6490f20055ee7290f20005ed7290f20004ff7650f20004fd7650f20054fc7650f20006bf6450f2001ebc6450f2000ded7694b20056ed7694b2000ced7694b20026ee6594b200576e6594b200576d6594b20056ec6594b20005ed7394b2006f6f5394b200076d5394b2000dee7094b20057ea7094b20057e97094b2000dec7094b2018f6e5094b2018f6c5094b2027cff7654b200567f6554b200567c6554b200576c5254b2027def7654b20286ef7654b200576f7554b200576f6554b20026ee6554b20026ec6554b200576c6554b2006f6f5454b200076d5454b20005ef7354b200076e5354b2006f6c5354b2006f6f5154b2000dee7054b2000dec7054b201776f5054b201776d5054b20274ff7650b20056bf6450b20056bc6450b20104fd76ccb2006d7e75ccb200057d75ccb20065be74ccb20005bd74ccb2000ded768cb20056ed768cb2000ced768cb20055ef758cb200576e758cb20005ed758cb200576d758cb200056d758cb20057ae748cb20057ad748cb201d6ee638cb20057ce638cb20057cd638cb20056ec638cb2000dee708cb20057ea708cb20057e9708cb20
  | 7 => 0x8940004fd7118940014fc7118940006be411894029ebc4118940054ff701894001cfd7018940056ef2018940246ed2018940004fe7694940004fd7694940054fc76949400067f65949400267c659494001dbe7494940005bd7494940004ff7654940004fe7654940004fc76549400267e65549400067d655494001dbe74549400073d545494000dbc7650940146bc765094000cbc7650940005bf7550940005bd7550940006bf6550940006bd6550940005bf7350940006bc635094001dbf725094001faf7250940007af6250940056bc6250940007ac6250940006ac6250940075be7150940075bc7150940007bb705094000dbe705094000dbc7050940147b8705094001ebf605094001fbb6050940147ba1050940004fe768c940004fd768c940054fc768c94007d7e758c9400057d758c94001dbe748c940005bd748c940004ff764c940004fe764c940004fc764c94001dbe744c940005bd744c940004fe760c940004fd760c940054fc760c94001dbe740c940005bd740c940007cd320c94000dfa700c940005f9700c940014fe76d854001dbe74d854000dbd74d8540076f661d8540077b641d8540024fe75d8540004fd75d8540024fc75d854000cfd74d85401eebd74d854000cbd74d8540014fc74d8540054fe72d8540004fd72d8540296bf42d8540006bd42d8540076be41d8540076f641d8540296f541d8540076bc41d854001cfd70d85401eef710d8540076f46158540077b4415854028dfb7058540004ff7654540004fe7654540004fc76545400067f65545400267c6554540005bf745454001dbc74545400073d5454540004fe76c8540004fd76c8540054fc76c854001dbe74c8540005bd74c8540007ad42c8540004ff7648540004fe7648540004fc7648540005bf744854001dbc7448540007ad4248540174fd75d972001cfe74d9720004fd74d9720054fc74d97201d4fe73d9720004fd73d972006e7f53d9720054fe72d9720056ee72d97200567f52d9720014fe71d9720004fd71d9720014fc71d9720056f970d972018e7e50d972018e7c50d9720024ff76597200567c65597200567f7559720004ff745972001cfe745972001cfc745972006e7f5459720004ff73597201d4fc735972006e7c5359720024ff725972000cfe7259720024fd725972000cfc72597200567e52597200567c5259720004ff7159720014fe7159720014fc715972006e7f51597201767f50597201767d5059720024fe75d9320004fd75d9320054fc75d9320144fd74d93201d4fe73d9320004fd73d9320066bf43d9320054fe72d9320056ee72d9320056bf42d9320014fe71d9320004fd71d9320014fc71d9320006be41d9320066bc41d9320056f970d932001cff7659320056bc6459320004ff7559320024fe7559320024fc7559320056b
  | 8 => 0x4fc765095001ebe6450950004fe768c950004fd768c950054fc768c9500257e758c9500057d758c95008dbe748c950005bd748c950004ff764c950004fe764c950004fc764c9500257e754c9500057d754c950004fe760c950004fd760c950054fc760c9500257e750c9500057d750c950007cd320c95000dfa700c950005f9700c950014fe76d855008dbe74d8550005bd74d8550086f661d855000cfd75d8550014fc75d855001cfe74d8550006be74d855001cbe74d8550004fd74d8550006bd74d8550004bd74d855001cfc74d8550054fe72d8550004fd72d85502d67f52d85500067d52d8550086f651d85502d6f551d8550024fd70d85502d6fb50d855020e7e50d855020e7c50d855020ef850d855020ef710d8550086f461585502cdfb7058550004ff7650550004fe7650550004fc7650550004fe76c8550004fd76c8550054fc76c85500257e75c85500057d75c8550004ff7648550004fe7648550004fc7648550005bf744855008dbc7448550024fe76d954007e7e65d95401a4fd75d954000cff74d954001cfe74d954000cfd74d954001cfc74d95402c67f54d95402c67d54d9540054fe72d9540004fd72d954007e7c52d95402c6bf42d9540014fe71d9540004fd71d9540014fc71d954007e7f51d9540006be41d95402c6bc41d954001cff70d954001cfd70d95402b67f50d95402b67d50d9540024ff765954007e7c65595402adbf74595402bdfb70595402b4ff75595400067f75595402acff7459540006bf7459540004ff7259540054fc725954007e7f525954008ebf4259540004ff7159540014fe7159540014fc7159540006be415954008ebc41595401a4ff7059540006fb70595401a67e50595401a67c505954000dbc7655140026bc765514000cbc765514001dbf755514001f3f75551400073f6555140026be6555140026bc655514007f3c6555140005bf725514007f3f5255140075be7155140075bc71551401aebe61551401aebc615514007f3f5155140007bb705514000dbe705514000dbc70551401a7b8705514001ebf605514001fbb60551401a73e50551401a73c50551401a7ba1055140024fe75d8940004fd75d8940024fc75d894000cfd74d89402a6be54d8940006bd54d89401d4fe73d8940004fd73d89402a6ee42d89402a6ed42d8940014fe71d8940004fd71d8940014fc71d894001cfd70d8940276ef20d8940276fa10d8940006ef6298940045f970989400057f755894007d7c7558940065fb705894007d7e75189400057d7518940006ed6218940024fe75189400567e75189400247e7518940004fd75189400567d75189400047d7518940054fc751894000cfd7418940056bd74189401d4fe7318940004fd731894029ebf4318940056bf4218940056ee421894029eed4218940014fe711
  | 9 => 0xd748c921007ad748c921005ad748c921007af648c921007ac648c92110ded738c9211d6ee638c9211d6ec638c921015ee718c921015ec718c921056ef618c92112fe7108c9211d4ff764c921014fe764c92110cfd764c921014fc764c921006bf644c921116bc644c921006df634c921006dc634c921005f7714c921015f4714c921015ec764c92110eec764c921014ec764c921005ef744c921005ed744c921007af644c921007ac644c921007cf734c921007cf634c9211d6ee634c9211d6ec634c921007cc634c921006cc634c921007e7714c921015ee714c921015ec714c92110fe4714c92110eef614c92110fcf314c92110fcd314c92110fe7104c92112cfe760c921006bf640c9210f6bc640c92112dee720c921007cd320c921007b764c8521007b464c8521015f672c8521017e672c8521016f762c8521017e762c8521057e642c8521007e542c8521057e632c8521007e532c8521005f570c852100cfe76d8121006bf64d8121006bc64d8121096fa60d8121024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d81211d4fe73d8121004fd73d8121014fd72d8121006ee32d8121006ed32d812100cfc71d8121096fa20d8121096fa10d81210057f75581210a57c7558121005bf745812109dbc7458121006bf6458121006bc6458121005df7358121005dc7358121096f8605812101cfe76d915008ebe64d915000cfd75d915001cfc75d915008ebe54d91502e6bd54d9150054fe72d9150004fd72d91502e67f52d9150014fe71d9150004fd71d9150014fc71d9150024fd70d91502ae7e50d91502ae7c50d91502aebf40d915008ebc64591502ddfb705915000cfd75d895001cfe74d8950004fd74d895001cfc74d89501d4fe73d8950004fd73d895024eee52d895024eed52d8950014fe71d8950004fd71d8950014fc71d8950024fd70d895027eef20d8950006ef629895004df9709895006dfb705895008dbe7418950005bd7418950006ed621895000cfd75189500567d751895001cfe7418950056be741895001cbe7418950004fd7418950056bd7418950004bd7418950054fc74189501d4fe7318950004fd73189502867f53189500567f5218950056ee5218950286ed5218950014fe7118950004fd7118950014fc7118950054ff7018950024fd70189502567e50189502567c5018950056ef2018950256ed201895000d7c76549501767c765495000c7c76549500067f64549500057f73549500067c63549500257f72549500276f72549500076f62549500567c62549500076c62549500077b705495000d7e705495000d7c70549501777870549500267f60549500277b6054950004fe7690950004fd7690950054fc76909500257e75909500057d7590950004ff7650950004fe7650950
  | 10 => 0x8d2100cfc7098d21005bf7458d2109dbc7458d21006bf6458d21006bc6458d2131def7258d21004ff7558d21024fe7558d21024fc7558d21004ff7458d21006bf7458d21004bf7458d2101cfe7458d2101cfc7458d21006bc7458d2101cbc7458d21006ef7258d2110cff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d2110ef71058d2112cfe7618d21006bf6418d21006bc6418d21006dd6318d21024fe7518d21004fd7518d211d4fc7518d2101cfe7418d21004fd7418d211d4fc7418d211d6de7318d211d6ed7218d21054ff7118d210ecfd7118d211d6df3118d210eedd3118d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d211d6dc3018d211d4ff7694d21004fe7694d21004fd7694d211d4fc7694d21006bf6494d21316bc6494d21006df6394d211d6dc6394d21005ee7294d21005ed7294d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d210267c6554d21006bf6454d2130ebc6454d21006df6354d21006dc6354d211d4ff7690d21004fe7690d21004fd7690d211d4fc7690d21006bf6490d2101ebc6490d21005ee7290d21005ed7290d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2101ebc6450d21304fe7694921006bf649492119ebc6494921057e42194921024ff7654921014fe765492117cfd7654921014fc76549210067f65549210267c6554921006bf6454921186bc6454921005f77154921015f4715492117fe421549212fcfe7690921166bf649092101ebc64909212fdee76909212f6ee769092114ded7490921167af649092101eee649092101eec649092109fac649092101eac6490921005ed739092109faf4390921007ad4390921015ee7190921015ec7190921056ef6190921167ae4190921167ac4190921167e7109092101cff7650921014fe765092114cfd7650921014fc7650921006bf645092101ebc645092109fac4250921005f77150921015f47150921015ec765092101eec7650921014ec7650921165ef7450921007af7450921007af645092101eee645092101eec645092109fac645092109fae5450921007ad5450921005ef7350921007ae435092109fac4350921007e77150921015ee7150921015ec715092114fe4715092114eef615092114faf415092114fad415092109faf405092114fe71050921014fe76cc921014fc76cc9210a57e75cc9210057d75cc92109dbe74cc921005bd74cc921006bf64cc9212eebc64cc921006df63cc9211d6dc63cc921015f671cc921005f571cc9210ecfe768c9210a57e758c9210057d758c92109dbe748c921005bd748c921006bf648c921136bc648c9210edee768c921006ee768c9210076e758c9210076d758c921005ef748c921007ae748c921005e
  | 11 => 0xcfe705952100cfc705952117ef7105952101cfe76d912109ebe64d9121024fe75d9121004fd75d9121024fc75d9121006bf54d912109ebe54d912109ebc54d91211d4fe73d9121004fd73d912109ebf43d912109ebc43d9121014fd72d912109ebf42d9121054ff71d9121164fd71d9121166bf41d9121166bd41d912100cfe70d9121004fd70d912100cfc70d912109ebf40d9121006be40d912109ebc40d91212fdbe76d912101cbe76d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121167af72d9121167ae21d9121167ac21d9121167b421d9121006be60d9121006bc60d9121167b710d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006bc53d9121166bf72d912109ebe72d9121166bd72d9121006bf52d9121006bc52d9121166bf71d9121166be71d9121166bd71d9121166bc71d9121166bf51d9121166be51d9121166bd51d9121166bc51d9121166bf31d9121166be31d9121166bd31d9121166bc31d9121166bf21d9121166be21d9121166bc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bc50d9121006be30d9121006bc30d9121006be20d9121006bc20d9121166bf10d9121166be10d9121166bd10d9121166bc10d912109ebc6459121325ef7259121004ff7559121024fe7559121024fc7559121164ff7459121006bf7459121004ff73591211d4fc7359121324ff7259121006ef725912114cff7159121006f77159121004ff705912100cfe705912100cfc7059121165be761912109ebe7619121164be761912109f3e751912109f3d7519121006bf6519121006be6519121006bd6519121006bc65191212ffad72191212febf62191212febf61191212ffae21191212ffac21191212ffb42119121006be6019121006bc60191212ffb71019121004ff7655121004fe7655121004fd7655121004fc76551210267e65551210067d6555121006bf645512101ebc6455121006bf64d8d21006bc64d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d2112edf31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d2112ef710d8d210a57e7598d210057d7598d2109dbe7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d2110ded7298d21024fe7598d211d67e7598d210247e7598d21004fd7598d211d67d7598d210047d7598d211d4fc7598d2101cfe7498d211d6be7498d2101cbe7498d21004fd7498d211d6bd7498d21004bd7498d211d4fc7498d211d4fe7398d2110cfd7298d211d6ed7298d2131cfd7198d211d6f57198d2100cfe7098d21004fd709
  | 12 => 0xc7018f211d4ff7694f21054fe7694f21004fd7694f21054fc7694f210267e6594f210067d6594f21055ee7294f21005ed7294f21004ff7654f21004fd7654f21054fc7654f210067f6554f210267c6554f211d4ff7690f21054fe7690f21004fd7690f21054fc7690f2101ebe6490f21006bd6490f21055ee7290f21005ed7290f21004ff7650f21004fd7650f21054fc7650f21006bf6450f2101ebc6450f21005f77150f21015f47150f2132cff7654b210567f6554b210567c6554b21015ed7690b21056ed7690b21014ed7690b2101eee6490b21057ae6490b21057ad6490b21056ec6490b21005ed7390b210b7af4390b21007ad4390b21015ee7190b21057e67190b21057e57190b21015ec7190b21167ae4190b21167ac4190b21324ff7650b21056bf6450b21056bc6450b21057ac4250b21325ef7650b21336ef7650b21057af7450b21057af6450b2101eee6450b2101eec6450b21057ac6450b210b7ae5450b21007ad5450b21005ef7350b21007ae4350b210b7ac4350b21015ee7150b21015ec7150b2114faf4150b2114fad4150b210b7af4050b2110cfd76ccb210bd7e75ccb210057d75ccb210b5be74ccb21005bd74ccb21015ed768cb21056ed768cb21014ed768cb210576e758cb210576d758cb21055ef748cb21057ae748cb21005ed748cb21057ad748cb21005ad748cb211d6ee638cb21057ce638cb21057cd638cb21056ec638cb21015ee718cb21057e6718cb21057e5718cb21015ec718cb2131cff764cb21057cc324cb2131def764cb21006ef764cb21005ef744cb21005ed744cb21057cf734cb21057cf634cb211d6ee634cb211d6ec634cb21057cc634cb21006cc634cb21015ee714cb21015ec714cb2110fcf314cb2100cff76583210057f75583210bd7c7558321056f86058321004ff75583210067f75583210047f7558321024fe7558321024fc75583210067c75583210247c7558321004ff745832101cfe745832101cfc7458321004ff73583211d4fc7358321014fc7258321006ee3258321006ed325832103ef62158321056fb2058321056f820583210aefa1058321024fe76d95210a67e65d952101cfe74d9521004fd74d952101cfc74d95211d4fe73d9521004fd73d95210a67f53d9521014fd72d95210a67f52d9521054ff71d9521194fd71d95211967f51d95211967d51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210a67c50d9521196f710d95210a67c6559521005bf745952109dbc745952132def7259521194ff75595210067f7559521004ff7459521006bf7459521004bf745952101cfe745952101cfc7459521006bc745952101cbc74595210a67f5459521004ff73595211d4fc735952132cff7259521006ef725952117cff7159521006f77159521004ff7059521
  | 13 => 0xc941004fc764c94101dbe744c941005bd744c941004fe760c941004fd760c941054fc760c94101dbe740c941005bd740c941007cd320c941015f6710c941005f5710c94100cfe76d81410cd7e75d81410057d75d81410c6fa60d8141024fe75d81410067e75d81410247e75d8141004fd75d81410067d75d81410047d75d8141024fc75d8141014fd74d814100cfc74d8141054fe72d8141004fd72d814128ebf42d8141006bd42d814101cfd71d814128ef741d81411febe41d81411febc41d81411fef441d81410c6fa40d81410c6fa10d81410c6f8605814117cfd75d972101cfe74d9721004fd74d9721054fc74d97211d4fe73d9721004fd73d97210be7f53d9721054fe72d9721056ee72d97210567f52d9721056f571d972100cfe70d9721004fd70d972100cfc70d97210067e50d97210be7c50d9721024ff76597210567c65597210567f7559721004ff745972101cfe745972101cfc74597210be7f5459721004ff73597211d4fc73597210be7c5359721014fe7259721014fc72597210567e52597210567c525972117e7f515972117e7d5159721004ff705972100cfe705972100cfc70597210be7f5059721024fe75d9321004fd75d9321054fc75d932114cfd74d93211d4fe73d9321004fd73d93210b6bf43d9321054fe72d9321056ee72d9321056bf42d9321056f571d9321166be41d9321166bc41d932100cfe70d9321004fd70d932100cfc70d932101cff7659321056bc6459321004ff7559321024fe7559321024fc7559321056bf74593210b6be5459321004ff73593211d4fc73593210b6bc4359321014fe7259321014fc7259321056be4259321056bc425932114ebf415932114ebd4159321004ff705932100cfe705932100cfc70593210b6bf4059321004ff7655321054fe7655321004fd7655321054fc76553210267e65553210067d655532101ebe6455321006bd64553210bd7e7598f210057d7598f210b5be7498f21005bd7498f21056df6398f21024fe7598f211d67e7598f210247e7598f21004fd7598f211d67d7598f210047d7598f211d4fc7598f2101cfe7498f211d6be7498f2101cbe7498f21004fd7498f211d6bd7498f21004bd7498f211d4fc7498f21014fe7298f211d6ee7298f21014fc7298f21056de3298f21056dc3298f211d6df3198f2131edd3198f2100cfe7098f21004fd7098f2100cfc7098f21056dc6358f21004ff7558f21024fe7558f21024fc7558f21004ff7458f2101cfe7458f2101cfc7458f21014fc7258f21056de3258f21056dc3258f2110edf3158f21004ff7058f2100cfe7058f2100cfc7058f21024fe7518f21004fd7518f21054fc7518f2101cfe7418f21004fd7418f21054fc7418f21054fe7218f21056ee7218f21056f57118f2100cfe7018f21004fd7018f2100cf
  | 14 => 0x1ebc6490951004ff7650951004fe7650951004fc76509510257e75509510057d755095101ebe64509510073d5450951004fe768c951004fd768c951054fc768c9510257e758c9510057d758c9510ddbe748c951005bd748c951004ff764c951004fe764c951004fc764c9510257e754c9510057d754c951004fe760c951004fd760c951054fc760c9510257e750c9510057d750c951007cd320c951015f6710c951005f5710c95100cfe76d81510257e75d81510157d75d81510d6fa60d81510d77a50d8151014fd75d81510d67d75d81510147d75d815100cfc75d815101cfe74d8151004fd74d815101cfc74d8151054fe72d8151004fd72d81512ce7f52d81510067d52d8151024fd71d81510d67e50d81510d6fa50d81510d67c50d81510d6fa10d81510d6f860581510d7785058151024fe76d95410ce7e65d95411acfd75d9541014ff74d9541014fd74d95413567f54d95413567d54d9541054fe72d9541004fd72d9541356bf42d954101cff71d954101cfd71d95413467f51d95413467d51d9541346be41d9541346bc41d954100cfe70d9541004fd70d954100cfc70d9541024ff76595410ce7c655954133dbf745954134df77159541344ff75595410067f755954133cff7459541006bf7459541004ff7259541054fc72595410ce7f52595410debf42595411acff7159541006f771595411aebe41595411aebc4159541004ff705954100cfe705954100cfc70595410067e50595410ce7c5059541024fe75d8941004fd75d8941024fc75d8941014fd74d89411d4fe73d8941004fd73d89412f6ee42d89412f6ed42d894101cfd71d8941326ef21d894100cfe70d8941004fd70d894100cfc70d8941006ef629894109df571989410b5f771589410cd7e75189410057d7518941006ed6218941024fe75189410567e75189410247e7518941004fd75189410567d75189410047d7518941054fc7518941014fd7418941056bd74189411d4fe7318941004fd7318941336bf4318941056bf4218941056ee4218941336ed4218941054ff711894101cfd71189412febe41189412febc4118941056ef21189412feed211894100cfe7018941004fd701894100cfc7018941004fe7694941004fd7694941054fc769494101dbe7494941005bd7494941004ff7654941004fe7654941004fc76549410267e65549410067d6554941015bc765094114ebc7650941014bc7650941006bf6550941006bd6550941005bf7350941006bc635094101dbf725094101faf7250941007af6250941056bc6250941007ac6250941007b77150941015be7150941015bc715094114fb4715094101ebf615094101fb76150941004fe768c941004fd768c941054fc768c9410cd7e758c9410057d758c94101dbe748c941005bd748c941004ff764c941004fe764
  | 15 => 0xf7658432005bf74584320f5bc7458432007cd3258432056f46158432004ff7558432024fe7558432024fc7558432004ff7458432006bf7458432004bf745843201cfe745843201cfc7458432006bc745843201cbc7458432006ee3258432006ed3258432006cd32584320eef651584320eef64158432056f72158432056f42158432004ff705843200cfe705843200cfc70584320eef7105843200cff76580320057f75580320fd7c7558032007cd3258032056f86058032004ff75580320067f75580320047f7558032024fe7558032024fc75580320067c75580320247c7558032004ff745803201cfe745803201cfc7458032006ee3258032006ed3258032006cd3258032004ff7158032014fe7158032014fc71580320e6fa50580320e6fa4058032056fb2058032056f820580320e6fa105803201cfe76d91510debe64d9151014fd75d91510debe54d9151376bd54d9151054fe72d9151004fd72d91513767f52d91510debc42d9151024fd71d915133ebf41d915100cfe70d9151004fd70d915100cfc70d91510067e50d91513767c50d91510debf40d91510debc645915136df771591510157c765515101e7c76551510147c76551510257f74551510273f74551510073f645515101e7e645515101e7c64551510df3c64551510057f72551510df3f42551510077771551510157e71551510157c71551511af7471551510267f61551510277761551511af3e41551511af3c41551510d57e70551510d57c70551511a67e60551511a67c60551510df3f40551511af771055151014fd75d895101cfe74d8951004fd74d895101cfc74d89513667f54d89510067d54d89511d4fe73d8951004fd73d8951366ee52d8951366ed52d8951024fd71d895132eef21d895100cfe70d8951004fd70d895100cfc70d895132ef710d8951006ef62989510a5f57198951005bf74589510ddbc74589510bdf771589510ddbe7418951005bd7418951006ed6218951014fd75189510567d751895101cfe7418951056be741895101cbe7418951004fd7418951056bd7418951004bd7418951054fc74189511d4fe7318951004fd731895135e7f53189510567f5218951056ee521895135eed5218951054ff7118951024fd7118951056ef2118951306ed211895100cfe7018951004fd701895100cfc70189510067e501895135e7c50189510157c765495117e7c76549510147c76549510057f74549510067f64549510057f73549510067c63549510257f72549510276f72549510076f62549510567c62549510076c62549510077771549510157e71549510157c715495117f7471549510267f61549510277761549510d57e70549510d57c705495117f771054951004fe7690951004fd7690951054fc76909510257e75909510057d7590951006bf6490951
  | 16 => 0x9432014fc71d943200cfe70d9432004fd70d943200cfc70d94320067e50d94320fe7c50d9432024ff76594320567c6559432054ff75594320567f7559432004ff745943201cfe745943201cfc74594320fe7f5459432054fc72594320567e52594320567c5259432004ff7159432014fe7159432014fc71594320fe7f5159432004ff705943200cfe705943200cfc70594320fe7f5059432024fe75d9032004fd75d9032054fc75d90320f4fd74d9032054fe72d9032056ee72d9032056bf42d9032014fe71d9032004fd71d9032014fc71d9032006be41d90320f6bc41d903200cfe70d9032004fd70d903200cfc70d903201cff7659032056bc6459032004ff7559032024fe7559032024fc7559032054ff7459032056bf74590320f6be5459032054fc7259032056be4259032056bc4259032004ff7159032014fe7159032014fc71590320f6bf4159032004ff705903200cfe705903200cfc70590320f6bf4059032004ff7655032054fe7655032004fd7655032054fc76550320267e65550320067d655503201ebe6455032006bd6455032054ff7598832024fe75988320567e75988320247e759883213cfd75988320567d75988320047d7598832054fc7598832054ff749883201cfe7498832056be749883201cbe7498832134fd7498832056bd7498832004bd7498832054fc7498832014fe719883200cfe709883213cff76548320567f65548320567c6554832134ff7650832056bf6450832056bc64508320576e758c8320576d758c832057ae748c832057ad748c8321d5ed738c832005cd738c8321d6ee638c832057ce638c832004ff764c8321d5ef764c832006ef764c832004ef764c832055ef734c8321d6ee634c8321d7ce634c832397cf534c8321d7ce534c832007cd534c8321d7cc534c83238fcf434c8321d7ce434c832007cd434c8321d7cc434c832387ce314c8321d7cc314c83237fce304c8321d7cc304c832007cf764c832005cf764c832006cf764c832007cf754c832397ce754c832007cd754c832397cc754c832057cf654c832397ce654c832007cd654c832057cc654c832007cf744c83238fce744c832007cd744c83238fcc744c832057cf644c83238fce644c832007cd644c832057cc644c832397cf544c83238fce544c832007cd544c83238fcc544c832007cf714c832387ce714c832007cd714c832387cc714c832057cf614c832387ce614c832057cc614c832397cf514c832387ce514c832387cc514c83238fcf414c832387ce414c832387cc414c832007cf704c83237fce704c832007cd704c83237fcc704c832057cf604c83237fce604c832057cc604c832397cf504c83237fce504c83237fcc504c83238fcf404c83237fce404c83237fcc404c832387cf104c83237fce104c83237fcc104c832014f
  | 17 => 0x4ff7158232014fe7158232014fc7158232126fa3058232056fb2058232056f82058232126fa1058232024fe76d953211e7e65d953201cfe74d9532004fd74d953201cfc74d953211cfd72d953211e7f52d9532014fe71d9532004fd71d9532014fc71d953200cfe70d9532004fd70d953200cfc70d95320067e50d953211e7c50d953211e7c6559532005fb7059532105f8705953211cff75595320067f7559532004ff745953201cfe745953201cfc745953211e7f545953223cff7259532006ef725953211e7c5259532004ff7159532014fe7159532014fc715953211e7f5159532004ff7059532006fb7059532004fb705953200cfe705953200cfc7059532006f8705953200cf8705953211e7f505953201cfe76d9132116be64d9132024fe75d9132004fd75d9132024fc75d9132114fd72d9132116bf42d9132014fe71d9132004fd71d9132014fc71d9132006be41d9132116bc41d913200cfe70d9132004fd70d913200cfc70d9132116bc6459132005f7715913210df47159132004ff7559132024fe7559132024fc7559132114ff7459132006bf7459132116be54591322ecff7259132006ef7259132116bc4259132004ff7159132006f77159132004f77159132014fe7159132014fc7159132006f47159132014f47159132116bf4159132004ff705913200cfe705913200cfc7059132116bf4059132004ff7655132004fe7655132004fd7655132004fc76551320267e65551320067d655513201ebe6455132006bd6455132005ef7255132005ec725513223cfe76949320267e65949320067d659493211f6f5294932024ff765493211cfd7654932024fc76549320067f65549320267c6554932005df7354932005dc73549322ecfe769093201ebe6490932006bd649093201cff7650932114fd765093201cfc7650932006bf645093201ebc6450932005df7350932005dc7350932117ac425093211d7e758c9320057d758c932115be748c932005bd748c9320575e758c9320575d758c9320579e748c9320579d748c932007cf628c932005dd718c932005dd708c932014fe76d853210ef661d8532024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d8532006f741d853210ef441d853210ef621d853200cfe70d8532004fd70d853200cfc70d8532005bf7458532115bc745853210ef4615853200cfe76d8132106fa60d8132024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d8132014fe71d8132004fd71d8132014fc71d8132006fb50d8132106f850d8132106fa20d81320057f755813211d7c7558132106f860581320fcfd75d943201cfe74d9432004fd74d9432054fc74d9432054fe72d9432056ee72d94320567f52d9432014fe71d9432004fd71d
  | 18 => 0xf7459232006bf5459232136be5459232136bc5459232136bf4359232056be4259232056bc4259232004ff7159232014fe7159232014fc7159232136bf4159232006be4159232136bc4159232004ff705923200cfe705923200cfc7059232136bf4059232006be4059232136bc4059232136bf7659232056bf6559232006be65592320573e65592320063e6559232006bd65592320573d65592320063d6559232056bc6559232056bf6159232006be6159232056bc6159232056bf6059232006be6059232056bc6059232006bf7559232006be7559232006bd7559232006bc7559232006bf7359232006bd7359232136bc7359232006bf5359232006bc5359232136bf7259232056be7259232056bc7259232006bf5259232056be5259232056bc5259232056bc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf5159232006be5159232006bc5159232006be3159232006bc3159232056bf2159232006be2159232056bc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bc5059232006be3059232006bc3059232056bf2059232006be2059232056bc2059232006bf1059232006be1059232006bc1059232004ff7655232054fe7655232004fd7655232054fc76552320267e65552320067d655523201ebe6455232006bd6455232005ef7255232055ec725523211cfd7694e320267e6594e320067d6594e32316be6494e32006bd6494e32024ff7654e320267e6554e320067d6554e3230ebe6454e32006bd6454e32005ef7254e32055ec7254e32114fd7690e322667e6590e320067d6590e3201ebe6490e32006bd6490e3201cff7650e3225e7e6550e320067d6550e3201ebe6450e32006bd6450e32005ef7250e32055ec7250e32054fc7598a32054fc7498a320fcff7654a320267e6554a320067d6554a32186be6454a32006bd6454a320f4ff7650a321567e6550a320067d6550a3201ebe6450a32006bd6450a32057ac4250a3223e7e65cca320067d65cca322eebe64cca32006bd64cca32005ed76cca321d6ed76cca321d76e75cca321d76d75cca320076e65cca320076d65cca321d7ae74cca321d7ad74cca32007ae64cca32007ad64cca321d7ce53cca32007cd53cca320067e65586320067d6558632006be6458632006bd6458632056f46158632004ff7558632024fe7558632024fc7558632004ff745863201cfe745863201cfc7458632006df325863212ef63158632056f72158632056f42158632004ff705863200cfe705863200cfc705863212ef710586320067e65582320067d6558232006be6458232006bd6458232056f86058232004ff7558232024fe7558232024fc7558232004ff745823201cfe745823201cfc7458232006df3258232
  | 19 => 0x854214ef661d8542024fe75d8542004fd75d8542024fc75d85421d4fe73d8542004fd73d854201cfd72d854214ef641d854214ef431d854214ef621d854200cfe70d8542004fd70d854200cfc70d854214ef710d854214ef4615854200cfe76d8142146fa60d8142024fe75d8142004fd75d8142024fc75d8142066be54d8142006bd54d81421d4fe73d8142004fd73d814201cfd72d8142014fe71d8142004fd71d8142014fc71d8142146fa40d8142146fa20d81420057f75581421557c7558142146f8605814201cfe74d9632056be74d963201cbe74d9632004fd74d9632056bd74d9632004bd74d9632054fc74d9632056dd73d9632056ee72d9632014fe71d9632004fd71d9632014fc71d963200cfe70d9632004fd70d963200cfc70d96320567f64996320067e64996320567c64996320567e62996320567f61996320067e61996320567c61996320567f60996320067e60996320567c60996320567c65596320567f7559632004ff745963201cfe745963201cfc745963213e7f54596320067e545963213e7c545963213e7f53596320567e52596320567c5259632004ff7159632014fe7159632014fc715963213e7f51596320067e515963213e7c5159632004ff705963200cfe705963200cfc705963213e7f50596320067e505963213e7c505963213e7f76596320567f64596320067e64596320567c64596320567f61596320067e61596320567c61596320567f60596320067e60596320567c60596320067f74596320067e74596320067d74596320067c74596320067f73596320067d735963213e7c73596320067f43596320067c435963213e7f72596320567e72596320567c72596320067f42596320567e42596320567c42596320567c32596320067f71596320067e71596320067d71596320067c71596320067f41596320067e41596320067c41596320067e31596320067c31596320567f21596320067e21596320567c21596320067f70596320067e70596320067d70596320067c70596320067f40596320067e40596320067c40596320067e30596320067c30596320567f20596320067e20596320567c20596320067f10596320067e10596320067c1059632024fe75d92320567e75d92320247e75d9232004fd75d92320567d75d92320047d75d9232054fc75d9232056dd73d9232056ee72d9232014fe71d9232004fd71d9232014fc71d923200cfe70d9232004fd70d923200cfc70d9232056bf6599232006be65992320573e65992320063e6599232006bd65992320573d65992320063d6599232056bc6599232056be6299232056bf6199232006be6199232056bc6199232056bf6099232006be6099232056bc60992320067e65592320067d6559232056bc6459232004ff7559232024fe7559232024fc7559232056b
  | 20 => 0x24fe7558242024fc75582420067c75582420247c7558242004ff73582421d4fc7358242046bf4358242054fc7258242046bf4258242004ff7158242014fe7158242014fc7158242006be4158242046bc415824215efa4058242056fb2058242056f8205824215efa1058242024fe76d95421567e65d9542054ff74d954219cfd74d954219e7f54d954219e7d54d95421d4fe73d9542004fd73d95421567f53d954201cfd72d95421567f52d9542014fe71d9542004fd71d9542014fc71d954200cfe70d9542004fd70d954200cfc70d95420067e50d95421567c50d954219ebf40d95421567c65595423b5ef725954219cff75595420067f7559542184ff7459542006bf7459542004ff73595421d4fc73595423b4ff7259542006ef7259542004ff7159542014fe7159542014fc71595421567f5159542004ff705954200cfe705954200cfc7059542186bf4059542155bc7655142026bc7655142024bc765514201dbf755514201f3f75551420073f6555142026be6555142026bc65551421573c6555142005bc73551421573f5355142007af7255142055bc7255142007ac725514201ebf625514201faf62551421573f5255142005bf71551421aebe61551421aebc61551421573f5155142005bf70551423af3e50551421573c5055142024fe75d8d42004fd75d8d42024fc75d8d42136be54d8d42006bd54d8d42136de43d8d42136bc43d8d42136bc42d8d42014fe71d8d42004fd71d8d42014fc71d8d42136bf41d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42136bf40d8d421557e7598d420057d7598d42006df6398d42115ed7298d422edef7258d42005f77158d4214df47158d42006dd6318d42024fe7518d42004fd7518d421d4fc7518d421d6de4318d420f6dd4318d42014fe7118d42004fd7118d42014fc7118d4200cfe7018d42004fd7018d4200cfc7018d42004fe7694d42004fd7694d421d4fc7694d4201dbc7494d42004ff7654d42004fe7654d42004fc7654d420067f6554d420267c6554d42005bf7454d4201dbc7454d420073d5454d42005bf7590d42005bd7590d4201dbe7390d4201f9e7390d42006bf6390d420079f6390d420079c6390d42055be7290d42007ae7290d42005ae7290d42007ad7290d4201ebf6290d4201faf6290d42005bd7190d423a6be6190d423a6bc6190d42005bd7090d4239cfe7694942055bc74949421576f5294942057ac4294942024ff765494201cfe7654942184fd765494201cfc76549420067f65549420267c6554942005bf745494201dbc74549420073d5454942187ac4254942055bf7590942005bd7590942005be7390942006bf6390942055be7290942057ae7290942056bf629094201faf6290942005bd7190942166be6190942166bc6190942005bd7090942014fe76d
  | 21 => 0xe609495218e7c6094952014fe76d855217ef661d855201cfe74d8552004fd74d855201cfc74d85520be7f54d85520067d54d85521d4fe73d8552004fd73d8552024fd72d855217ef651d855217ef621d855200cfe70d8552004fd70d855200cfc70d8552005bf7458552185bc745855217ef4615855200cfe76d8152176fa60d815201cfe74d8152004fd74d815201cfc74d81521d4fe73d8152004fd73d8152024fd72d8152014fe71d8152004fd71d8152014fc71d8152176fa50d8152176f830d8152176fa20d8152176fa10d8152176f86058152184fd75d9642056bd74d96421d4fe73d9642056de73d9642004de73d9642004fd73d9642056dd73d9642004dd73d964216e7f53d964219ebf43d9642054fe72d9642056ee72d96420567f52d9642056bf42d9642014fe71d9642004fd71d9642014fc71d9642006be41d964219ebc41d964200cfe70d9642004fd70d964200cfc70d96420067e50d964216e7c50d9642024ff76596420567c65596420567f75596421867f54596421867d5459642004ff73596421d4fc735964216e7c5359642186bf4359642054fe7259642054fc72596420567e52596420567c5259642186bf4259642004ff7159642014fe7159642014fc715964216e7f5159642006be4159642186bc4159642004ff705964200cfe705964200cfc705964216e7f505964216d7e7598e420057d7598e42056df6398e42024fe7598e421d67e7598e420247e7598e42004fd7598e421d67d7598e420047d7598e421d4fc7598e42006df5398e421d6dc5398e421d6bf4398e421d6de4398e422eedd4398e42054fe7298e422eebf4298e42056de3298e42056dc3298e42014fe7198e42004fd7198e42014fc7198e42006be4198e422eebc4198e4200cfe7098e42004fd7098e4200cfc7098e42056dc6358e42004ff7558e42024fe7558e42024fc7558e42006df5358e42006dc5358e42116de4358e42054fc7258e42056de3258e42056dc3258e42004ff7158e42014fe7158e42014fc7158e42004ff7058e4200cfe7058e4200cfc7058e421d4ff7694e42054fe7694e42004fd7694e420267e6594e420067d6594e4201dbe7494e42005bd7494e42004ff7654e42004fd7654e42054fc7654e420067f6554e420267c6554e423b4ff7654a420567f6554a420567c6554a42187af4254a42014ff765864201dbc7458642056f46158642167b64158642004ff7558642024fe7558642024fc7558642004ff73586421d4fc735864209ebf4358642054fc725864209ebf4258642166be4158642166f64158642166bc4158642056f72158642056f42158642004ff705864200cfe705864200cfc7058642166f7105864200cff76582420057f755824216d7c7558242056f86058242004ff75582420067f75582420047f7558242
  | 22 => 0x8e5200cfe7098e52004fd7098e5200cfc7098e520067e5098e5223e7c5098e52056dc6358e52004ff7458e5201cfe7458e5201cfc7458e5211ede5358e52006df4358e52006dc4358e52054fc7258e52056de3258e52056dc3258e52004ff7158e52014fe7158e52014fc7158e52004ff7058e5200cfe7058e5200cfc7058e52014ff7658652005bf745865219dbc7458652056f46158652004ff7458652006bf7458652004bf745865201cfe745865201cfc7458652006bc745865201cbc7458652004ff73586521d4fc73586520a67f5358652054fc72586520a67f5258652196f65158652056f72158652056f42158652004ff705865200cfe705865200cfc70586520067e50586520a67c5058652196f7105865200cff76582520257c7558252056f8605825218f7a5058252004ff745825201cfe745825201cfc7458252004ff73582521d4fc735825204e7f5358252054fc725825204e7f5258252004ff7158252014fe7158252014fc715825218e7e505825218efa505825218e7c5058252056fb2058252056f8205825218efa105825201cfe76d9152186be64d9152186be54d915216ebd54d91521d4fe73d9152004fd73d9152186bf43d9152024fd72d9152186bf42d9152014fe71d9152004fd71d9152014fc71d915216e7f51d9152006be41d9152186bc41d915200cfe70d9152004fd70d915200cfc70d9152186bc64591523cdef72591521857c765515201e7c765515201c7c76551520257f74551520273f74551520073f645515201e7e645515201e7c64551521873c64551520057c73551521873f43551520076f72551520557c72551520076c72551520267f62551520276f62551521873f42551520057f71551523c73e41551521873c41551520057f70551521a67e60551521a67c60551521873f405515201cfe74d8d52004fd74d8d5201cfc74d8d5213e7f54d8d520067d54d8d5213ede53d8d5213e7c53d8d5213e7c52d8d52014fe71d8d52004fd71d8d52014fc71d8d5213e7f51d8d5200cfe70d8d52004fd70d8d5200cfc70d8d5213e7f50d8d52185be7498d52005bd7498d52006df6398d5211ded7298d5223def7258d52005fb7058d52175f87058d52006dd6318d5201cfe7418d52004fd7418d521d4fc7418d521d6de5318d520fedd5318d52014fe7118d52004fd7118d52014fc7118d5200cfe7018d52004fd7018d5200cfc7018d520057d7494d520257e7394d520275e7394d520067f6394d520075f6394d520075c6394d520557e7294d520076e7294d520076d7294d520267f6294d520276f6294d520057d7194d520057d7094d523be7e6094d523be7c6094d520057d74949520057e73949520067f63949520557e72949520576e72949520567f62949520276f62949520057d71949520057d709495218e7
  | 23 => 0x1000800400001e002002c00400400200280080030028018002001003800000e002000804c00a0030078000016002002000402a00a004800400a0000030004016011000000000000101f003c00c000000800000a00000180040000300010034018001000000401004000f0040004003000001c00000500d001401a000001000400a0030010004000003003801802401500000040120020010008006000000801400a002000001400000000000000000020018008004001000001c02e001001001c0000030020064000000000800002e001002000003e01f01cfd75d8954024fd74d89541d4fe73d8954004fd73d89543ceee52d89543b6ee42d8954014fe71d8954004fd71d8954014fc71d89543ce7f51d895400cfe70d8954004fd70d895400cfc70d89543b6bf40d8954005de7398954005dd7398954006ef6298954006ed621895401cfd75189540567d7518954024fd7418954056bd74189541d4fe7318954004fd73189543d67f531895439ebf43189540567f5218954056ee52189543d6ed5218954056bf4218954056ee421895439eed4218954014fe7118954004fd7118954014fc7118954006be411895439ebc411895400cfe7018954004fd701895400cfc70189540067e50189543d67c5018954014fe76d855401dbe74d8554025bd74d85541aef661d85541afb641d855401cfd75d8554024fd74d85541aebd74d8554024bd74d8554054fe72d8554004fd72d855436e7f52d855434ebf42d85541aef651d85541aebe41d85541aef641d85541aebc41d855400cfe70d8554004fd70d855400cfc70d85540067e50d855436e7c50d85541aef710d85541aef4615855400cfe76d81540257e75d815401d7d75d81541a6fa60d81541a77a50d815401cfd75d81541a67d75d815401c7d75d8154024fd74d8154054fe72d8154004fd72d81542de7f52d81542bebf42d8154014fe71d8154004fd71d8154014fc71d8154006be41d81542bebc41d81541a67e50d81541a6fa50d81541a67c50d81541a6fa40d81541a6fa10d81541a6f8605815401cff7659252056bc645925219ebe5459252156bd5459252004ff73592521d4fc73592521567f535925219ebc4359252054fe7259252054fc72592521567f5259252056be4259252056bc4259252004ff7159252014fe7159252014fc715925219ebf4159252004ff705925200cfe705925200cfc70592520067e50592521567c505925219ebf405925219dbe7498e52005bd7498e52056df6398e5201cfe7498e521d6be7498e5201cbe7498e52004fd7498e521d6bd7498e52004bd7498e521d4fc7498e521d67f5398e521d6de5398e5223edd5398e52006df4398e521d6dc4398e52054fe7298e5223e7f5298e52056de3298e52056dc3298e52014fe7198e52004fd7198e52014fc719
  | 24 => 0x10002014011800403c00200b0004008017000000000000200d00000060040058004002005001001801c008000000001e0010048034006000001000c016008005001000e0000000000006000000800001402c007000400800200800000040030018008004000000004801400000280000020000000034002004001000000600000000280020030030008008004005000400a007009800004001c000802c004000000800c004001002801001600c000005400000b00000000000030018030008000000007400200100000000400000010018032003000800400c0110048098000001001000400a0000000008004017015002c0000010000024000001008801002e0020000010000000000803401000000180080060050000000000002005804400400000080000000000018014010000000801800000100200100000000000000006000003800404e004000000c0100180018068002005001002402e00000a800001800c0098068004001001007c000000002801c00000d00080080020010000000000003000801400a002000000000000500b800806a0010008018004002002000800e000000000400600d00180240020010068004004001003006c00800b005000000000f00000080060000000000002016000801c002000000000000800000200180020060020004000001000804800c00000380000060100048020004001000800401a001004800000400b00000200000000018000000002000800001c004003800800400000080140160000020014002011005000000000f004800800a00400000100240030018018000009002003c0000010000020012000005000000400100e801401a01300480540220010000000000000001800c0040010070020006000011800001a001000003c03c003001005801000100080400020020030008016000000000800200400180180020010010000000000000000001000c0000014006004002000000000000000000040060068010002001001804400c0040020058000001000801400000100a800000a00000380080000010060004004007006005000400200b800c00200d001800c000004003800403c03f007801000000800180040020000070004000000010001000a0060008004002001000800400c0080048000054004000000000803a000800400a0000020000018002001003c004001001001c00a01900280040000050008000000027000801c008002000001400400b00080480080010020000000000000800401e0040020000000001005001c008004002000401000300000300000070088024000004004003c0040110020000002009000001400000000080000040010030004008003000004801601a0000034000015000000800800400100580560000020004002010004802400000c0058000002
  | 25 => 0x600000c00000040060078018000007000806000a00b003005c008001000803402e001004000800000000500000240000008030000008000001000000c0070008002000000001401600000d000401a005004800c000000002800000801a0000004010000000005000200000280040020020038000032002001000c004024000002800001100480040040040038004004002000800c0060000060000000003000002000200500c000002400a00e80000040000048028010013014801c0080000048004000003001001c00000f0000080018032000003c0000080050020004000000801400000200e000800a0030010000022000001000400000000480040260090198018008007005001c02a00300180080060060008000000008000001401000800380040160020000000000004004801c00002300f00000000170048000002003000000800400100580040000000000000022008000002401c0020048000004000000001000200c00c800401a000003800000200101080200740010030000016006003804c00600900280540000010008028000000008000000a00100100000120000000000000004001002c00601b002000402400000300080000010000000000004003000000e015000004001e03b0000018006006000800002201900080000240030020014002003003001c0160070010018004017000004801200a003000000000c00280000100000010000000007000805c0000000000000000005004803c000000000003000c0010000000000005001801801a00200000180000020060020006006006002400207b001800002e001000004c008004000800400000d0000000024009008001400000400a80100300070070018002006001000c00200a0008000002000000001000c011000000c000004000004c00000a001800401a0040030000000004002001000200301f800000000c002001804400700280000000040010004000008005003804a00d000002800400000180440000030018014006005000000003400e00200240180040010004032002001000800800c00a803401001900000400220010020000002005000000000e000008800400a01800000180080020030074000009003000000000000100080040020048054002000001003800a0120068000000001000000400200100180000040010020004000000002802c0340080010000020003002000800400200000040020060000020002002002800000000100000480100290020000016002008000401a0000040000002021000000c018001000000c006001002000800400300180000000020018010002002005000001e004003801c004000001806800e00a000000000c00e0050018004016000803000a0110000054000007000000c00200300180140000000000000000010002
  | 26 => 0xd6b00e1587bb2f7bf2b100000004bb9a2099200019d00000000004c21ee00007cd49115c8000f515133aebe2c6000003c357b0ce400297a00009755f48000c6c00055c27480004792c0800034ffc957e205840a00016b80010980002170001f440007ea8562b14000219b0100000007d62d48000000000379dd1ac695e88284000690f2014f96ce09d2102cb4312d3a47210b400001a2c4b8d49120003991004000d710001965b303810001e750a285b50e25d1d7c7dd0a720cd2740002dea64c41cd1018b05c4000ec40002f9c29000072b9f7ca944664d5114fd2077e2660ed80ec93925bb5714688c7504b55c46001f35d01e800031a17b244c15c0006b100015e80000002bd8ef200000000002500002323b816a62590002f0129e00025e000164235e0000a9c00000047e800042c2672618bac97246b75d84e40001d35ba94e20003a71053730c06faa00000000000000000a5c0880007ac866d5c990605a5ad40000001241ed59c2f7a0000000610e4400026fc2e897f511140fcea9cc1503eec000e1d68a80005c33fd05a963c3d62ed6888671db644b4e89d118d02cb1a88001290ec548d000000000011002d0ee87581ead0dddacab42288c531b49141022200aae0000000619c8600040c0001b420000c55e31b2e3c2800000075eba80000000d0c00012db8b16388206d306fa000f79743ada9f1d000193800163c78151509e00000000002bb7792a5d3f3800000097c0003544a6ad759cb227178ec9a0ff1a496545fe3027ec9c84cfd41d06394f22be2bca2f533240750c8d909aabab62429541ce107426b018b4400074c0000f3cbf451ebb5d7d8fa6100941c00e8b71b00a0c570f907ab8335c72a8c20b3a08c5a65e2ce85b8bb2cf474a907cc88a7000000016b12726e002882ca3f70e4160dc566ee1bf0001740698be780613d6ad27572d0c0e669170e28c8bb00004188000887bcc691122813c3921ac80005c025028f000185cb7300009787628ac0003e74da8c248001c99742541d84051590200000018700d05a9712891476a1870001914c5422eb07070da2c858178ab79d6f06b7350e08b9688fc6bb5c2548000000136460c5510001b02be6d7257f05615303311cba149e7c5b75e98000000b36617bdd40000000f4b8cc000d1c0002ac80007850a880014a80bd38a68ec9224c423b1611d10553384b560d140003d10026001000000000e00100a007c09401900280040000040008000020013003803800000100480000200040000000046009003004000000100080000020090008080006016002800000000f000004800200100700200080030018004040005000800400800000200000900050008008000000008002000600000280100540380010000000000003001c00e02300380080020020018034012019000000802
  | 27 => 0x795d20002e797d0c019c37d99fb56454cf6a803cc98edd40002c9d76a00000000012800f86660836d8292e00022a800055e4f20000000000585a5b189933614ddecc458000467bea40e496100038f800087a047646109500058c8000000000334000111accb0f938b8718ced19e40018cc8f2282c37089a5c97be94a0288cba0001755096000000176b82a04717d80013fc4da623108c0009e172330c8608cfc00000015d914706d992800000077980006940006111e946c200024a81a453c00024b09900007a300000e19a8b57800000195a70018a2e7b847cbf1881dc1d4ad5f0f338858f0d3432e0384c488a2ad330e1cbcb6845a3e8560ab5b5c8b8ed0feb0d8000f28000000714ad85cc800009036cad92a4c0b511d5b9e0000161cb4000a00bdb00000000001a6121400000000000000000001b1185000000033537146de1837883dbdaffb10189a540000824234877860e188800000115f2850000000000a0025fb748efa0b6091399c43a44f1c48001d2c91b00000000000002b422d8000bc8043d52ca98cc449180008046ed00000016c80001216b14b6400000016907aa94b06a79e59c05ec45419369bed6146eb71c0000000002a05d50ef811ebce5b0093b5df194880c92c375bf3190c3552c71f55644d7f0ea64f95240000000c8582ecf00000000000000767187da6e0f43e700009cc00038b8000000a9aaf585ce0008eb33e162c02e842090bb95c2458717382dd6b843a00eb41c94800007e38bdca2dff787000166b939800000000033c6403b7c0000402263721796f206059608236b9a2b08e284ca3691bd886a0e0c894ef9189af0f1b0003e3c000b4b2f51e7db6a65d00030a5a0a71d3b6159ded6758a7f0f981d80005c7800172ff1400000450585f238680015c8000000000000057f002055081e8cd4e713b94e19b08000ba060a1bc140877000000045995a9a6091e38896217f2436000000070801c3f930b7d260006b40ce00f212b1d321293220004b10001dd30000003c5d84a2ff66317f0000bff0003299f9603b1b2a031b1c7d3141116561e04e927ab387a8f9a2dad96157c039199a0253f218f21e000a7dc3935b4b4644fcdc13c71ad1ee021e4629cdcb94a1a0002e643c80003110d992929c600009a00007920000000bb700028414dc0009a30000001647f4b0fb1fb8d040000000fbda1ec8e4611e100698b92a56b612080004878dc09d4f8d293a79546ecd539c053011f4b45f302ccbc030238c307e000e3d72f90750e00ca800249deb400a7143ca07eb0005e280016662182cb3451e0ae4869190f92126934d22c8d4d2a6c5e80471eaace70b98d140000a394c0ceaa2e0004eaa778b22db25fe3128438e614df0cf5ef0f9703a9b69dcc0001553bf4a1e83215b80019680002180b20000e7e75bbe31c1276
  | 28 => 0x208d93e6e80c0326c3709a869683054222063a3ae3825ef1f2d806917fc51d1c580002b251875cbb34000a08501d9407721bb40181055da664715656812e8287863e013ce0002d0cb6eb8868d6b5a98c8080005390b100000007471740000291110a1900002e9588cead2ac73159c982150600061e0000f9200000000a5c4000000026d1cc69c10f820d05363cc31bb4bde78e6b35506d98575590cb8800d2080b0fd23e18f40155513f58e680000000001de800000000003c600077f055a176b810003b780000004dbbacce54d3f00000016c0b3d6b497c17289db0000001a82000711b13a3caa3e00017e40baa3c13f94d1e605a0153015400000004a8000000d18000000066ad6d1e5e39624e7bd27c000158079a0000000b8eb1a5f950d38e030df008000fee3466a30001c9ea8a0139861f0411256a3965bd4a9d3829440000ca91a21acced25bc2ecc0009081d563d8bf4c4e570785b6316b023c1fab2dd44823a330a5b258e12c5c32325a760c66a40001dc4e6f1153ce8bd293d79480000000cda543ac546a1492cbbd9011ec2800000001600006a900000005330001c713af43b196ae2509b62b40fb6700009947691dfc9eca280b01adc000cb06d529bab280000000000000b7b563b100000a598efa248000000028257c0000005958001e90bda2a3910d5d8de2441184b766a1e3ea2f5c4661ee7c5a78cc2225c17980003a4cc1220323058cb0657f5d352dee546c458a17de4ad49c27d131ac3a3eb35e702ef2700013b0997a076b5018096442f4860240e3c00000002f7a148f6000ac4870e6a000408403542f6c48cab20000004ffb1a86444313bb9c6d29400036200009fa0583d610f5862cb35f200014889012a13c614181460000000c32f4400000000000000000abc000cc031a11380000000001e0e138b7266f00000002d90000b7ca88fae091a25a74000070500018ba42669ab2eca860000000000f7cd3d44ab21c0003c577e36cd1326d83756054b546ae177020005467811430a82843e324f80000003d062a80000000006bd253505a6bea399455cf64ef00000001e00c1d8ead1a00032f686b603a52e373d71cf82c80bc00037c0f96000284b59922a7fc0031b6400039b4c09015d3c29f38b3127b5a023000385d3a60005203078000c606b81450f0049880036480004c65aea9e1c68e601ba824d50472b16c06febae76b4013d70000d2660c3e154faa1409709edf8225a34aae9d4827bf70004c816b0007e329b8f6e23f6f309dd9dc4711f90b040009fa80010000000006750000f40c7d8002e3f080c712898d246320005b6000164cbca62e30f5bda00036b91b9076db40cf9f78952000164e94c186b6e60b2e0018a0003798000000000000000000000000005d566e60f0000eb927974e6e6826e2b83b874d85
  | 29 => 0xb187a45213f7859942eca339a83d5122aa63cd87444c283f04a37bc29a5260d70d05bb24ac43b07244da9ca79bb3352a6b410a9b9b95e7e2452f9853af85646c4920cb6a6df2bbf1fcac0d0c3ab9c50016569262a1f551207e750b4206d400072834ccea4f2e0002a64000000194000000058661814e59166492b58eedabc91265aba2c2aeef771800008c600020d81dd028848000000000000000029342860000adbed80000340720d4000000055cb18cce648f4e3befcfd002100032480009cd5a3000000094101998e557ea874aa3ef4e4df8e1be8001bc885967a915d092000000218ea9e000000000120aba9000000000002d2da00958d600011b94b5d820000f40000000c507c52179aaa9fb4cab16d5f2000000000007ad095090001650a5e00003bc000585000232c00033900000005640003d302a9a70f5d3de2499f0e5ac70b0000a343a80001a597ee7f90002e58000000114ae8a0009b81f280004a40000000000000c6f0000eb2436452f7f80012f0000000364035600045e26f0d8e6b0000093356cfd86ae8de1be46630000000000a9b87517880009fa3a59f280005dcd05a7f0000000117e9ac000d7680022a293cc85775ba294e815a74d3b61fa4e9700015698f8da210880adba6d2e00012180006660dd00012e40000003d1c00000075129891080006690001dc628b0000000000f242f2974c000d4b25aac5154a3f30000000000d1a7742db40000007af00014080007b4ae6639c60d5368585f6e5220505ed1f720f25758121f2c24b507be9c94beb622d28cc8180005ce3e9e0004583a7c7005f48fb6cb319dc6c000621c001edc0d63192ee00000004052aac0009ae8000190e160c85630c3c0001fc35f800096cc1f30d13c10c04b84818001f0cdf52b61679204c910003cfc00008a0eddc0de624170001a7a5c8931318af583facbc67f177969e0000000000e50da41fa05dc0003fa2fc2e75d8460500705c0000000610b768aaaa666bbe1e5e840b26270604000b34373028000000000000003bacd35be3bd530c45c000000192c0003031326d2daae044353cb820005dc42300000005440001e9eef926b35d50ba04e62a31dc3de0000001448706506800383de38f060002b08a02ad3000100e0000000000000000b4e62880016622602e900004f20002e00eb515a6a36ad9fd8c99dd50001e0c3300003d8800008c00000000012a28a41e000000000002dc9a78000be81af9b88000bba3f22ec99505740001c940005243f531900000000001051e2670e00030fc0000000000c8c0001153821d9171039566291b16eb4296fd00e913dd8b96b3b9c5f068014400013740000870d4c000a5ae039bf44dc2f71deea698b281a38939880003c6800000145a03702580002d00003e2a2ec000a29741a4b4e256e70003f3c0000
  | 30 => 0x2228003bb00000006a12d5c0040004c00000ec259803c2010000b1351880000000000002064eaf75a0000ad42bef923b40621da2fa4224bbe90a88d34c4000000061500000015cb7e27918000c4ce8f134bb70d72c1357440002ec45fd1800996a001b2fb186d26a4dc7b9ad13b7c9ad73927882f04884af0f7cdd40000671d44b46e221d80366304be54ae8db9e7a97d74912cc764086328891cb8613f5d30001f405d137b870427a94e41797dc75498c1288000000f1148c820cdfef56365280d2d273b2833d89e32ad06b9c00d2aac9332306cd5f700000a13b4598000345c388000da930994a5c5a00000000009ae000000000000017b4572aec59c000521a8598510004ce14a8000e4946b00008fc6436b3be55cd04d85012459884d541ad3a515908e002a20f40005a1000000175c3be0001c826fe0000000d2041200036e80005466878001b0a0003fe0eb75ec000450796800039b60417c89add027f80001cb04c6d0034d000185aa91423321000020f6b600000000001ee2f55366e3a0d49c21286b0aeebb7407c88f42a907108427fa13a85d28bcb9b15d199599ea4583e8a71c0c8a13e89bc170e2d0292944587c539b3e85a562a9b216dabe88a8399787a1a07100d028f90c9f88e3100000000009cb07f96db11644f8a928b0000cfb20900000000005499d4cf82000776a2200000000003ea262e6d36fe19c45d8000082a5cd32e00010625e94b6234019e394000cd76b180000003fde39000000000019032b00000007679f8c56000010a25180003df8c2079e00047f335aca4e2aa7175e9ee916ad8406b8000e7849a68da1276494976dcafa800037c5d50001e081c7511a938e80e18399b1b5ce600046fbe978920da330085ce6c48c575ca94be23b359f12b8ce07f00000a3c000d6f55e9c321b02421c70d70528862141e5a00001506d407898a66de000107102473d46426593d4fce7652116000bbf557906133c2fc3ac99dcf720927290001314e7a00029e7ddc00031a80000000002bdbdec000da75b7a948ee63ba1f89b3800000000003733607e94f698799f0444000000000000012ea590e1be9d7b18000d869985b580000005770000001f2287522b000132087c0000000000ba1f79361c4c4444a1c0715d9808d1cd1b2dcca6d61f82839605e8c73812e81462f0204aceccfc16b4453840bced7952398fc47619526030d1b3ec0059a9669a408870f6bf5099a80147529e80000000000000000c797cf01313120006aca0ac0001a58000b4800097900008c8000d5357d80000000000bf8001c32e457da80004063cfa7a867400045d12b8da0f1eb3856baa3d1305f51fc3ed1efe000000000078bba462690fd67889600b395543e4ff1dfa49146ccb84281e61afc18d553b091606022126a5c01080ad7c7c000000d024f43
  | 31 => 0xb008000d4742b9240e89c0c6073b4795447c20f31d14e68276f88a3823abf218964c1b7a58c8f3ab3c1d062c37a316943ace34c2800011cd130b13270c2400076d000179e4e72ae0c700005b61689dd87a278d31e83e51ea90e2a6bdb00009a70001ffd2f60001d0a5949b62dd3c50001a800006c511e8000e3f00037d10c39f8b52f8440003563e021140000004b19d670540000003049718881ec9ab8c7fe20823e8001d80beb5561b15f9a29cc4098a40007423a48938ec4000000000138a00000000003ee98b1065c29d1297e31815e9136b705c932adf8a5c5baf3d355fec488000786000e7612608820001b9327021b00e9873509b00c2ec0a43496e9dc888c00016f8c806981e08fad3cc68f265a6a4a92000628c9cc00075626e8af40bf000000000027c00056880005499dd1aa3da12789e97114000000eb200013884046b67951c8d15e6621c325c4bf6d4a73a2bc4aaccc6f2b104ed7072e07d29dd4c0a18201acdac40e4d6e8a7507f51c204c923461803f180000115600005580010100002ce21dcb6fb59f549721b462543d781941c01d58cc800000019a40f07400002e68002c31da60006ef1539f940002d166e5b7eb557a70ca8ab0a103d3b1845c40001388db400017d672800000017e5c8000030aae000022e13e017900000009d000025d94c836e8bf170794dae8c8f3ee0000000da066c1f640000000001e5d5e6156149a6be00051b0000303a3cd2b5e314800000003680000200bfb0002c45cfef980003f68426d4549796e352e929054000000025f6ad2ee40006d200034040003770000001d328a04538001c4edfb03e27b00005a76993289186cf600029d9cb4b2500006957e6000000000000000000000000000004398000000c8d05c000000060c00f00000000000000000f606c648e8000396f09532b6b8a8a4703ae3d0c13ee410000000ade79500000000000001eb994c0005a83611c6400000063116ec0000000001d41aca000068c0009840000001c902eb82e4cd18cc000212155d10800093b9508ea53ec06671e00019de00000008540000002e10cc13ae63b47128ac00000000000018ea0003fda3b03c2a596278001b5e00000000000000006007afc35009143f0324ef486c5b0e2515527450000000000000616105400000000000000009f8000000000000000005b56a2ef07c4360600090a41300000009d6186800152b0002ed04a400037600013e90d400043a3ac00000000000001b560005e666ac000d2720d00000000000001b3581adfd3420001cb60000002ec40008d9006800013600048e00000004486590001a16000017bb0a0000000001aa000000000020d5540a900003004000adb4b50000000b740000001e9213329d5726c4630134c8eb13907076741808daa1921220000000ae52ea02e9038
  | 32 => 0xcb7a734afc0f167e16ee93802e4d855c28000ef0bc12129dab42db0e51f8001ac82e309e0000e829fdc7e1a043940001570170000000007400000000058d80011520002080001ec20000000000000b820000a280c400000032f40002e7bc30ff082689ba8732bd1dc66e0000001d5abd953e00017c60006198000d49000000000185d34f0083474b20bfd00000000000000728000c8252f1849c0552aac312b15d820c0001fca7f40c90004f99a3177300003d80000008470600000562a4f62e4bf80a21b213a0000bbeb3f681a341cd83e200012c000000000013e4000a640003534f118ce00021989e491113e22754b846d251ccc91ccaa308a1dc59aca3a0000090000c44000157c16273de15aacdb02bdb35ea4ac00096bacfd3f169033e0251dbdda0ef10001fccd0e2c00001d290c6843427b6e124af90d961714c424f17dd32b9bd8fd73d595f5528fd144fae61f903b43723228a091a31a000017dc19014d11625206f961b0fb5cf84be6fc15b43e8000356b17887200002bb3687780000002a78c0210801f11a92ce0e678934a931e75f0d333ad2efb8b3ed381d7b84ab58baeb453a0634b4fb509d5c0f5580e501b204317abd317f073f609e84de94f580183074294d9cbff11180009c9584dd6c73ea2502fa88000089a4b6af48000a5019235dc0e24bd0d6b7589387293f28000c7c0006e51575fb2e38269bec4000cee800214ea74ec80001951930000000164df4d2b0ea61b70e3eaf200025100000000000000000bbb5f11930e724eb52d3539d735b82720c60614ebc0000000ac67d75b180019b6f225bfa5b80007d25b8951965c72261380000005652fe800136200024e80015d412d1a1ac1745eec356621b8f549ef5f8b1d8000bb45404cb000065700000000627fd286000000097674f889940c000769400000090b6b717ee00084400006fd48a0cc5ac80000009dc4c1191c0492960078b96000e056748af04480004cf8edc000c096130000000266076a3181f6d9a000000183400045f2d110ce970d9d000000000000000016484d141e000172a00000002e539e00003637e501a0000000000b9c04f0ed2eb07ce2da0000000000efb1ec0f1e94edbc00024fdbca0002aa00000001027813bd988a6ec537ce8c7203e0000380959200000000000000002a000000005369a68000000f3575786f400000000008adcbaaa40001a38000025800121c1510a766428e012c20b4652d1c94ae4c75182fd9d8d311729a2c2180001bd2440848bed7d1bf0840bc370000b24000e1f00038c960eb4511caa581ec0004a626b9d548c1224da7ca7e4a370a91e13062288e7ab54e8c81100021ad7baa9b0001e1a9a876a000360f37a6b8be204600008a555ba5ad10ca424a13e645681c65d2b7a1c8e77b29246f999cb0d0c52712f48eab32f
  | 33 => 0x987de5e859540796bcfea32b5669d9d93c7435458001d793d909c1a5d98e0b8f3bb7cd0ca8a6039c0008c0c2300022791cec3c8578000000ca74778000556c577530000000a8000034193a90006ec000089d0007d4285252a8ff367888ccec3122f3386d21a0000000000000682d4316ac0503c740db9b47ec000000000000005b0000fa988e72731c224c0000000001a94a600003ad400000000035d875e000000533b76c0000000bd07a80000005b303260000000003ee00002893a7b0512b000000016b40000000000afc00007400014b0368c082fd13bf12b01ae7c8001f1bdce000102800060a0003365e3c1175f0145800000000000006680890000344000000208fccc78349357aec2818471e800366cd2328c00000001fce6600000000de05646a8000000db68001e2550800000000000dab6224b400000080627bb5cc5453576ef96b874a276206bd7c0000000000f6c1c611a000041056630350683291eee13560a159f8066f1fd9148fd80000001ac83185501ee800149600000032e40000001e700016fc00000000000000002748000000f770003281a2493a8000425b60b045739f9975e2e6074a598b174c80000f250b8c2038ff850940b8a6208000c12b01077227e62a22215d9ca23a889771503785a6c990ec800106ce8578400016f22925c2000120e0003b707d400000000019c8000a210eb0857e689b1a338350c962dc342804c4d4d78f8e8e784deb1641101789a0b656d28001f08dee2d9a3c000022d5e6baeed3620729700000000a464b8f58078dc424c86bc755000258bdb5bc0a0500006794c2000451001a0a6bbd2c0026ae400005cfb160000000608b510850ae665080012000000002b68f280000fc00017bd0007d789c0dc6134272a9a87bc54152b86585dee0e00020e40009f2756000085400047cb2f8ef885f00026811c69e025500000000000001ea0000f2b000392d4ac0002328e759867d835f3cbd490000000092acda8e7ca3886eaf0000078a56414a36b092b3997ec00062d6f7ebc6c6c000058c0005710000cec00000077660748de0004940000000f3606a800061600000019b0b7e0004db1be8000189aa427644948d4129ad78000dba0000f18ea800070d00006e621f0370001e8200035e3325266155108efe95d06fe355ac811d092a7b01c4c79ef6700000008440ac2228d2d6b44273790000000000690800043455b3b33bbd1060000d12b5848000000000013ab0000002694f422d08000001b8c11000028b8000f934e0000000030e08f000081c4a100029280000000001f0c00083824100002de0000868001dba81060e3e940000000000000594b0ba82b80c5000094128000000cf118eb34144e000000337c6d80006c880008aa544e39b6d89c60004d09a707d2cc200026ec000000000301507
  | 34 => 0xbe62f5bb3e0c0006e9215800041a00033a8c6c00000074e0001de90006922d7c00053600039c45089f7000026000000000000006c60004c73a11e580000000000c9d8fe641a9180000006fba7d7c430001a12a35684000000116d896aa80003ef02ba7c20c88de538861d0002d243f27725be8b0d0a600070f2d29aaccf71562c084b02be88984a8eea86d00033743165c67e3a481e649f17801d75a7cdc32858864d3ac957a804c0ec68ba57099ec3e66f80a0168342a8d86f59ec8db60877b30d614fc000490811400007180001fc48c1b154e2c01596cf34d7ba44d06fbe0e62ba6000c650000428000c0333d2f78748e0b3779b313a000000029fc9282a867d2f10000df6000126c26e9170002ae9b768e10000001a8653c22f800112500035380012640000002420cd26070002225b2af3b0002716bba00000034a0f980004a29d2168b70f50da6980004614e1ee89d6a6a97b919fc46211f410b811b92167067bd6ca7a34e3c41a8836093700010d579c9da6522bbcf227216cf2edc5848ed57ba75b778aaa00010fe00000022f5bd466e4770002c0ef0ede96e580019e4b77438a330df695bc576e797c2bdf7d6ac7d2b8d2c081914ddd4ad916a9fd1e14c1b1568b8446c7d01361a505bc3e800000000002a2088b7f800000012a8000da2f4035780000002871e23dc4340c3efbe15d42620007a98000cb4e4a000000010acff00000015039f50530aa42740004d100000000004e10ca5a2efb029180000000002205d6f7e7000000166c000f07459104566400000000000003da386122c296000000000108200043c3f6c0006250e6820971b00c0002038a0400014d4925b1e00000019efea47c876a8000000ee964a069a05c00017523cc00000000023c45a8c4c2850a186ce00018f111da3e39c7659634a1a8a305f124836a80029d8001b1ab5627a02ae00053fd568000000aa10001b94000d83204000000054989a820552d000000000000008b0001bd8b32b186164001d6d9738abf9e0e20e7d09db4f024862e451c8b800088f7e9ae4e7c23cb6cdee3506084e4308f20e74194505182cbda5660090f35d0c000000310c3aeae27e1902c000f81030b4e4ae6eb46291e58df8afd6d6383468e0d318f80012c00000002cc0f522f21b900000000000000f4db04af02d2b295a9244c87b84656120520003041726a58000037424c0002b700000004ca000179186a0000000001b84000370abb89c270e95559586a48550000001f3804d42d2f2f324c3b0638b140002351e1000077a7c70000000d9027d0000000ce80000003d15d0000057c17306ba0a90003a809a465b00007fc9f617c0003da80000003b00001e4a1fb24088e17a8f262f7b6740d46b1112aac4000bc2402bc8471e3110d382b229e5197062f82196072a532f0ce0c2990c
  | 35 => 0x4de280247dd8ecd14f71f6d1f4de33c83785b2863a7c4bb2510aa6f5d82d31e702410000000a385e10000001f361363c13274858adc4623ae00321ec1cc23490de74c0001e65b320490d62e5dcb84af1928e34e34683b2abd18e604a27808dc4ecadbeacfae8d8ac43413d22c0af8ce22c63c0cf2699d2342d014e30000808001994f657708505c4c7eb321140c2d81cfeee1d554f65385db2d35b0c0d219722c4a623a20000b3d4d0829282090cb9a9d823d8001ee8000326a04c48d6671e1800000000020c80d89820670003960bdc00000008bc7005db11f255d2a4480000177111c10b658876c06a1163789b815eaa5123a0000000d2500000006b6000000000000064f54703106e8aca22517fcd582b9113ab7dfa0d0e6db8000ac44ce00021c8000000010043c13400043d91c926c0006823938e5e0000d0ba9c0007c6324256cf3828d63eb62d36a8c02bf000064c52b02100016a805a0003b65872a49712ce445650000000000000c7e695d7583b01f11fce0dd47270224719e51b67f14cdbc697eaeba53ab24000044124c03acd48abc35336c51d289078ab10ac787ad00035f550a7bb2799859d48d3600000c8000f760000fb00008d1613fead1bc00062f8001aecc825dbe9e20000000f0000067ed8802cb1b91b868970432d9f3e5b107e8b3540261000000019b8000000164856c0000003221f2893456eaad553eb837aa2de166f00000026b00007e060c80d61
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc9c74dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001998e7b92c4880063ea1f705891005667312e631220008ef87588624400159906b10c488003335cd621891005637902ea3122000c6d205d4624401595e42ba0c4880032b485741891005666192e6312200accc825cc624401599e42b98c48800333485731891005667902e63122000ccd205cc624400117f08bb4a48800e2f211769491000c7a432e329220069b4845c6524406fae0a0b8ca48800a3e21970949100043fc2aeca9220008bf845d9524400717908bb2a48800237e0d76549101d46e41aeca92200a87c8759552440051f50db82a4880021fe1576909100243e42aed21220018f4865c642440051f10cb8484880165e21570909101b6d820ae1212200087f855d942440090f90abb284880022fe1176509100046fc1aeca12203a8dc835d942440151790eb22848802aab209645091000c7b436e2a12200a8ee829da324400159b0431c64880eab320d628c91000c7a432e319220028f8865c232440010ff0abb264880121f215764c9100045fc22ec99220038bc845d932440011df04bb264880121fa14764c9100043ec28ec99220038be841d9324400117b083b264880023ba1e624c9101d47643ac4992203aacc8358932440010ff0abb064880121f215760c9100045fc22ec19220038bc845d832440151d904bb064880023b61f620c91000567432641922000acc864c8324401599eec9906488003335d9320c91000c7a432e219220069b4845c43244001b8a64b88648800a3e219700c91002cbc42ae01922000dc9325c032440052e90eaa2a2880131d1d954545100d5b8402a8a8a201ab708054951440356e50bb82a2880067ca0375485101beb8286ea90a20018f4865d5214400d36908baa428817e6da1f74485100065a3b6e890a2000cb4761d12144001ba461b9a42880063d2197348510034da422e690a2000ba584189214400178b06312428801b691d24248510014f243a8490a2000ba5848c92144001b60e9b8242880066e21d545011001e5c3b2a8a02200ebb081551404401d76102a1280881f2eca137150110004f843aa2a022005d7075545404400d76108a8a8088003cc5515150110035d842242a022000fa14248540440952f50fbaa40880031e1db75481100063c3b0ea90220029f281dd1204406db6083ba2408800a3e219744811002cbc42ae89022000dd231dcd20440051f10cb9a40880165e2157348110005b4c28c49022000bc983189204400bad0eb29240880067a21d5248110005b4c2c649022000d7075dc5204400bae0eaa8a4088003d854951481103deb83aa629022036bb0844c52044001f826498a4088006bc2192148110016783b2429022037d7075485204406d7610890a408802bb81892148110
  | 1 => 0xb0818ec690002b360831d8d200056cc0063b1a4000c3e74d96634800187ce832cc6900030fd957498d200061e32ae931a403ac9c635d2634800193ae9b1cc6900021fa1f6558d200043f438cab1a400487e87dd563480018f0ebb82c69000237e1d6318d200045fc22e231a40038bc845c463480018decb394a6900063b2197294d2000637b2ae529a400087f855d953480011f700bb2a6900ea1fa1f6554d200043fc2aed21a400487c855da43480751b906bb486900025b6167290d200063632ce521a40018ec865ca43480018d8cab9486900eb3318d7290d200243f42eeca1a400087d85dd943480010ff0abb286900121f2157650d200047bc0aeca1a40028f4815d9434807517d0fb22869000e37a1f6350d2000536432a72924031c7870d9552480098d8edbaaa4900c75a1c3755492018e363b6caa924004c6c7655152480098d8ed29aa49012a1f21975cc92018c3fc3ecb992400087d87d97324800187ce9b2e64900030fd9574cc9200061e32ae9992403ac9c635d3324800193ae9b1e649009e1f219758c9200043fc3ecb192400987d87d96324800187ce9b2c64900030fd95748c9200061e32ae9192400096d879d632480158dec0bac649002b5ad81758c920006b5082eb192400096f87d9632480012db0e32c64900034b5d6748c920006573b2e91924000d2d755d232480155990431a64900031e197704c92000c76432ea9924031c6c76d9532480958d8ec32a64901beb3a1b734c9201d567436c69924000e4f6518d3248001c98ca31a6490002b3a1c634c9201d667438c69924000acd8118d324801559f0031a64901beb3600634c92000727b2a641924072e4c654c832480958f0e032ec2900063e20175d85200043f43ecab0a4000c3c74d9561480010fd0e32ac2900030f1d065585200061fb2ee8b0a4000c3c65dd161480018becbb9ac2900031719773585200062fb28e6b0a4000c5c651cd61480050fd0fb2aa2900129b21952545200243f42eeca0a400087d85dd941480010ff0abb662900121f21576cc520004b6c2ce598a40018ec865cb3148075998ec99662900121fa17764c5200043ec2eec98a40038be849d9314800117b093b262900030f1d3654c5200061fb2ee898a4000c3c65dd13148001998ec99262900030f1d365485200061fb2ee890a4000c3c65dd121480638f4edb2e40900131e9d865c812000477c12ecaa2200a8ec825d954440070fd0fb2aa8880122fa1f645511000c7b436e2aa2207ed7050dc554440051f50db82a8881f76c10770551100043fc2ae7b12200487c855cf624400117f08b9ec48800e2f21173d89100243f43eeab1220038be87dd1624400187eebba2c4880030f1d774589100061fba8e8b122000c3c751d162440018beebb9ac488003171d773589100064fba6e6b122000
  | 2 => 0x276485500045ec24ec90aa0038bc845c765500ff87eebba2caa00022fa1e41595400043fc2ae7b12800487c855cf62500011df0eb10c4a00030fd0d75189400561fa12ea312800ac3d425d4625000187882ba8c4a002b1bc81751894000636902ea31280008bd87904625000187aeb208c4a00062f21974949400061fb2ae9292800a87c8759552500031790cbaa84a002a2f21d655094005556412caa1280008be8718d425000147b0a31a84a002aaba1b625094006557438c4a12800acae871894250015c5d0a31284a002b8b614625094000556c08c4a12800a8bc849da32500031790cba464a00121fa14764c9400043ec28ec99280018bc865d1325001d36902ba264a00021fe15760c9400243e42aec19280018bc865d032500151f10cb8064a0003724c9700c9400045fc3a85b0a800287e87d95515000317d0dba2a2a00030fd97745454001c9e43aa8a8a8004a3c865515150001878ecaa2a2a00021fe1576c85400243e42aed90a80018bc865d32150015958eca1642a000e2f210764854000c5f436e890a80039ac875092150001958eca1242a00022fe1171d972001c5e422e3b2e400a87c8759554c80151790eb22a9900eb17cc17598f200062e982eb31e403ac9f315d263c800117f08b88c79000e2f2117118f2000c77416eca9e403a87e87d9553c801595ce4b2487900023de057650f200147a40aeca1e403a8be87d9143c807553d07b2287900c6da2015394b2000cf4402ea9964000ace8718d32c801599d0e31a6590002b3604634cb2005764c00c699640038be87dd161c8075998e6992c3900022fe11765472001c5e422eca8e400287c8759551c800117f08bb2839000a2f21d64507200045fc22ec98e40038bc845d931c800153b0931a639000a3721d634c720056663b26498e4000c3d74953654800117f08b8eca9000e2f21171d95200052f41cc9b2a4000a5d83993654800187ae83a6ca900028fa1273d95200051ec24e7b2a4031a6d821cf65480010fd0e21eca900021f61c43d95200043f43885b2a400987d8710b654800147f08b8eca900028f21171d952018d3d400e3b2a4000a79801c765480010fd0e20eca900021f61c41d95200052f41883b2a4000a5d8310765480014dd0420eca900029b60841d952018d3d40083b2a4000a798010765480010fd0e18eca900021f61c31d95200051f42063b2a4000a3d840c765480014dd0418eca900029b60831d952018d3d40063b2a4000a79800c765480010fd0e10eca900261f61c21d95200051f42043b2a4000a3d8408765480014bd0610eca900029760c21d952018d3d40043b2a4000a5e8399065480014bb07320ca900029e60261195200043f43ecab22400087e8719564480090fd0fbaac8900021fe15765512001c3f43ecaaa240048bc87591544800153
  | 3 => 0x1b224200a9e83083644840153b06106c8908b2ada0420d91210045ec3cca3224200a9e83994644840153b07328c8908022fe1d65191210055ac0cc032242008bf845d954484070f90eb2aa8908122fa1f64551210052ec2861b1a4200acd820c363484015ab02186c6908eb1718d7598d210061f3aec931a4200c3d75d92634840187cea324c6908030f5d46498d210062ebaec731a42008be87d91634840117d0e322c69080e2fa1f7458d210065a3a6e2b1a42008df8758c63484010ff0ab80c6908121f2157018d210045fc22ed29a42038bc845da53484751b906bb4a6908026b6127294d2100656324e529a42028ec865ca5348401958c8b94a6908eb3318d7294d2101c5f426eca9a42008bd84dd9534840117f08bb2a69080e2f2117654d210047dc02eca9a42018f8805d953484750fd0fb2aa69081237a1f6354d2100657b24e521a42028ec865ca434840117f08bb286908023de057650d211d45f43ec8a1a423aa9e83d9143484015590ca1c84908b32d1c7645092101e563b6e8a12422cda471dd14248459958edb22849080f2b1d954509210055743486a124203cac7690d4248401878c8bae64908eb1718d75cc9212fc5e432e9992422c8bf87d93324840117b0fb2664908030f9d764cc9210061ebaec99924200c5d75d8f3248401878c8bac649089a2f219748c9210045fc3ec919242138bd87d92324840187cebb2464908030f5d7648c921006373b2eb19242009ad879d23248401a5ceaba464908034b5d5748c92105657b0ae9192420ada7615d23248401b4e20ba464908026be1f648c921004d6c38c91924200cb464dc532484051d90cba264908b32b1db644c9212fe563b0c89924270ace86dcd324847559d0db1a6490803a3d90634c92100746320c69924200ace8718d324847599d0e31a649082ab3e04634c92138566c08c69924200acd8018d3248401d1ec899064909c7a3191320c9212fe5a388c9b0242018f4815d360484591790dba2c0908022fa1f64581210061fbaec8b024200c3c75d91604840117d0e322c0908030fdd464581210061e3a8c8b024200c9f64dcd6048401938c9b9ac09080327d9073581210064e320e6b0242008ef8758862541034df0ab10c4a80030fd4d74189500561fa92e8312a00ac3d525d0625400187ca0ba0c4a80030f14174189504043f436e6a92a00087e8718d525400147b0831aa4a80021fe15769095000c3e432eb212a00a87c859da32540030f90cbac64a800e2fa10764c9500045ec20ec992a00187c865d532540032f100baa64a80021fe15760c95000c3e432ea192a00a8f8865c03254001b9264b8064a800e2fe1d74d85500061fa92e9b0aa000c3e505d36154001878a0ba6c2a80030f5d152d85500043ec2eeca0aa00087f855db21540030f90cbae42a800e2fa1
  | 4 => 0x10c8e1d8c82992c2191c3b1c41325843200666996e0b086400d4f754c9600c8e5a98ea992c0190121fa1f75580321d76598264b006400ccf874c9600c8df9990e992c01900393dd53258032007263aa64b006400ecb804c9600c8dfd9100992c0191bfb2941325803237f6520264b00646feca104c9600c80199a65b8ac01900e1f21570d91510045fc22e7b12a2038bc845cf62544011df0eb10c4a88030fd4d74189510561fa92e8312a20ac3d525d0625441595e42ba0c4a88032b48574189510061e282e8312a20087d87940625440187ae9280c4a88021fa1c63549510051ec20c6a92a20287c865d6425440187aebb2484a880a1f21975509510143e432eb192a2038be841d9325440117b083b264a880a1f219754c9510d4bc402ea992a2008bf845d8325440717908bb064a880a1f219750c9510547a432e2192a200dc5325c432544010ff0ea96c0a8a130fdd7745954100477c3ac43128283aaf84588625040187e86ba8c4a082b0fd0975189410561ea12ea3128200c3e415d4625040187882ba8c4a08022fe1176949410145e432e9292820a87c8759552504154d904b2aa4a082a2f21d65509414145f436e6a1282008be8718d425040147b0a31a84a080a2f219748c9410243f428ec992820087d851d932504051790cba264a080a6d205744c9410045fc22ec19282028bc865d032504151e90cb8864a0803714c9710c9410243fc3aebb028200c3f425d7605040187c82baec0a08030f10575d81410061ebaa85b02820087f855c364c84090f90ab86c99082a1f21d65553210545e43ac8aa6423ac5f305d663c847593e62ba4c790803274c57498f210043fc2ae031e420487c855c063c84011f700bb2a7908063e2017654f211d43f43ecaa9e420acae7259243c84051dd05bb287908ea2fa1f6450f211d54f41ec8a1e422cba48150e42c841555d0d21a859080a79205744cb2100567438c6996420acce8718d32c8415d8b0231a6590802b3600634cb210243f43eeab06423accc734c960c840717d0fba2ca908030f5d754d91210043fc2ae1b22420487c855c3644840153d0732ec890802a760e65d91210061eba8ebb224200a3e859cf644840147b0b39ec89080327dce73d912116556c10e7b2242008be8714f644840117b0e29ec8908022fa1c52d912109c5ec38a5b224200a3f855c364484014790ab86c8908b2ada0470d91210055ac08e1b2242008be87143644840117b0e286c890802a7a0c50d91210054ec18a1b224200aae82143644840155b04286c8908b2ada0450d91210055ac08a1b2242008be870c3644840117b0e186c8908028fa1430d91210051ec2861b224200aae820c3644840155b04186c8908b2ada0430d91210055ac0861b2242008be87083644842717b0e106c8908028fa1420d91210051ec284
  | 5 => 0x9002ad60450592321345f43860b2464008bd870c1648c80147d0a182c9190028f61430592320555741060b246400aad820c1648c80156d02182c919002ad60430592320051f42e20b246400a3d85c41648c81555d05882c919002ab60b10592320045f43c20b2464008bd87841648c81555d04082c919002ab608105923205476412ecaa4640a87c87595548c8151790eb22a9190031b597725523200656b26e4aa46400c6d65dc9538c80195ac9b92871902b8b1096550a3205556412c8a14642787f87597328c80187ce8b2e651909a2fe1d64cca320061f3aac99946400c3d75593328c8018daed32e65190031b5d965cca3200656bb4c99946400cad76593328c801c5acab26651902ba9c8564586320243f42ee0b0c640087d85dc1618c815cd640b2ac11900e2fa1371582320045ec26e2b0464008bf845c7654c80717908b8eca990063ea1f70595320063dba8e0b2a640087f855c3644c8090f90ab86c89900a3da1f71591320065bba0e2b2264008f7815d9544c8051e902bb2a8990023ee01765513200c7c402ecaa2640387c87595544c8694f100b2aa8990122f21d64551321ad5a40ac8aa2643a8ee86dc9544c87539d07b92a8990ea1fe1d659493218d3c402cb292643a8bf87592424c85956902b24849902b530c9758c932056c6192e9192640adc7215c6324c815b9640b8464990023ee0175d853200c7c402ebb0a640087f855c3614c8090f90ab86c2990023de0574d81320147a40ae9b0264008bf845c7604c80717908b8ec0990022fe1171d943201c5e422e3b286400c7970943650c8010ff0ab86c8190121f21570d90320543e43acaaa0640a8bc87591540c8090fd0bbb264190021f617764c83201c5f426ec99064008bd84dd9320c8018dd0bbb264190031b617764c83200657426ec9906400cad84dd9320c87599ca7bb2641900333dd9534c832395a742eec9906400b4d85dd9320c8e371d09bb26419002e3613764c83200666c36ec9906400d4e85dd9320c801a9b0bbb2641902b33d97764c832006c7426ec9906400d8d84dd9320c81599d0fbb2641900393a17764c83200726c2eec9906400e8e84dd9320c801d1b09bb26419002b3607764c83200566c06ec9906400ccf76dd5320c80159f0cbaa641900333dd9754c832005e5c02ea990646fbc8805d5320c80199eecb2a6419002b3e19744c832005e3c0ae89906470bc4815d1320c815d18c8b226419002b3e19544c83205566432a89906400acf865c5320c80171f08b8a64191c6e3211714c83200567c32e09906400b4f855c1320c8e56990ab82641900363dd1325843238ec63a264b0864038be87dd1610c875d8e62992c21900333e1d32584323866643a64b086400e8f744c9610c801d18e8992c219003b1e0532584323876240a64b086470ec6514c96
  | 6 => 0x543f43ca8b2c6400c3f74951658c80717d09b8acb190022f61371596320053d404a2b2c6400a7980945658c8154dd05282cb190030fdd2745963205536412e8b2c6400a7b805cd658c8014f100b9acb1902a9ba0b435963200536c1686b2c642787e8710d658c8010fb0e21acb190028fa1371596320051ec26e2b2c640aa6e829c5658c8014db0538acb190029ea0271596320053cc04e2b2c640087e87105658c8010fb0e20acb1900297a0c41596320052ec1882b2c640aa6e82105658c8014db0420acb190029ea0041596320053cc0082b2c642787e870c5658c8010fb0e18acb190028fa1031596320051ec2062b2c640aa6e820c5658c8014db0418acb190029ea0031596320053cc0062b2c640aa6e829c1658c8014db05382cb190028fa1070596320051ec20e0b2c6427a5e831c1658c8014bb06382cb1902a9ba08705963213d36c10e0b2c6400a76811c1658c8014eb02382cb190021fa1f40596320043ec3e80b2c640aa6e82901658c8014db05202cb190029da0640596320053ac0c80b2c640aa6e82101658c8014db04202cb1902a9ba0a305963200536c1460b2c642787e870c1658c8010fb0e182cb190028fa1030596320051ec2060b2c640aa6e820c1658c8014db04182cb190029da0430596320053ac0860b2c640087e87c41658c8010fb0f882cb190028fa1210596320051ec2420b2c640aa6e82841658c8014db05082cb1902a9ba08105963200536c1020b2c640ae1f32996648c815c3a6532cc91902b8bc81659923205557414c3324640aaae82982648c81517d0faa2c9190030fdd754592320555741482b24640487e85dc1648c8010fb0bb82c919002ada0640592320055ac0c80b24640ae2f21995648c815c5864b2ac91902b8bc85655923205717902cab246400c3f759d5648c81555904baac919002ade0573592320055a40ae6b24640aaae82d4d648c80155b05a9ac91909a2fa1c53592320045ec38a6b24640ae2e52d49648c81555d0538ac919002ab60a71592320051f428e2b246400a3d851c5648c84d53d0638ac919002a760c715923205557410e2b246426aad821c5648c8015750038ac919002ae60071592320045f43ea2b2464008bd87d45648c81555d0528ac919002ab60a51592320055d404a2b246400ab980945648c81555d0428ac919002ab60851592320555741462b246400aad828c5648c84d17d0e18ac9190022f61c31592320051f42862b246400a3d850c5648c81555d0418ac919002ab60831592320055d40062b246400ab9800c5648c80147d0bb82c9190028f617705923205557414e0b246400aad829c1648c80156d03382c919002ad60670592320045f438a0b2464008bd87141648c80153d06282c919002a760c505923205557410a0b246400aad82141648c80156d02282c91
  | 7 => 0x4048060280000100100000005801000000000420020040000104202409056004008008230061b80082d00602c0201700001007809008014018000000040580301c06c000020000080b800048000028030040800201b01400c0f00200a05400000002010138840040200e8010260400000000600c000000201480e001004000010010020083682502401011807000000038060000000402500e00000007000004088050541240800e00400c000000980accc625ce625500199ae7b14c4aa0023be1d62189540045ec3c82312a803c3d7590462550010fb0f280c4aa0130f5d250189540261eba4a1b0aa803c3d75907605507587ea6ba4c7290eb0f54d7498e520061fa92e931ca43ac9f315d26394801878a0ba4c729003275d34398e520043ec3ca131ca400c3d7494263948014bb07284c72902ab3a0b4358e520052ec2886b1ca4038be87dd1619480187ea7ba2c3290030fd4b74586520061e286e8b0ca400c3f74941619480147b0b20ec8a90021fa1873551520249ec26e2aa2a40087e86dc154548011bf0eb18c6a90022fe117118d5201c5e422e231aa42387d87d8e535480127f08b8ca6a90021f2197094d520049ec24e7292a40487d87d8e52548018bce7b1ca4a90024fe1171949520243e432e1292a431c78605c25254815ad640b84a4a900f0f9d154d85520143e42ae1b0aa4008bf845c7605480717908b8ec0a90eb17a1673d96421d64f424e7b2c843ac9d849cf65908158bea539ecb2102b1754a73d96420564fa14e7b2c840ac9d429cf65908019388339ecb210031714273d96420064f39c83b2c8400c5e7394365908758b906bacc7210eb0fd0d7598e421d61ea1aeb31c8400c3f425d6639080187882bacc7210eb17cc17598e420062ebaea731c84008bd87906639080187aeb20cc721002a760e4198e4205567416a6b1c8400a9d8414d639080187acaba4a7210ea1fa1f6554e421d52f41ecaa9c840487e87dd5609080187e87baac1210030fd0b75582420061e20eeab048400c3f75905609080147b09286caa10022fa1873551420045f436e2aa2840393d85dc154508011bf0eb18c6a10021fe157018d420243e42ae031a8400c3f65dd1535081535d05ba2a6a100e4f21d5454d420251e432a8a9a840a8be86dd6435081535d05bac86a108a2f61f6390d420f4d7434e521a840acae869ca4350815a5d0b39486a102b4b6167290d42004d6c0ce521a84008bc865c6435080127f0ab8486a10030fd9774549420549e43aa8a92840aa3c86551525081565904aa2a4a10024f616739094201c5ec3ec72128400c9e73d8e42508071790cb8c84a10b32d1857190942056d390ae3212840093f855c242508010ff0ab86c2a10121f21570d85420261f3aaa9b0284018bc845c760508154dd0530ccb1902a9ba0a60996320
  | 8 => 0x210000f49c81821dc0bc9da1e40620260e803b0a788f0e609b83384a0128c4938022c9f0fb8c51c783d8c7194dee04098d062a1916917898416a17e80f0b906e8029db0b582d81489412f88592c99f85a0cb8e20419a0969a1383a13983520600f878d001459871cb9ad1241ed0a38818ae182a031b50e987d93a8ac86e14197b80690e0ef97a0e414697c05e90a80e8328eb1a187f1d80b991b06f14d0dd1b60370571d41bc10b977a1c0a115f14d83993a1c0102a0d1161d28fe88f99820696d9c406781b9158001288988000000000001b986a9408de84e8f10a80090c4cdf0000120001f78001f615410092e07487a9d09f587604693d1ca8a185081d14107c9580d98360550d71099e80851f80d680c80500603015c04f5dd87500721c9b79ae8e10e51ac1bed1306c9339a41c99520db1ce20a89519d0a8a048d90b792116596312b20f81f1c38478e88a20cf8318189470e302720a0000001758801908610dca051519b39f20130a90578340649e21e51c11cf8f60dd91c80000000009321517386393600014519c13590f0001791218c791d80006b8511eb8f91462038000e01600970798a29cd1880000f58000928001ac86b04495694020d9629ba1a696f18e1f683087b21011205689d10300013310e93684b1078ed1f19261b002ccff14900000020415fa0b0a50870101868718769ec9e00f009109485f84c9a29f313e2170d41e61e30391da8ab8000d20000a09c29df21994286911500006191380819980000007e5a01aa00006a0ae8001e29290505b68e19e689913e80017a9cc1421ef85a9101a3902025d680920e08250a486501402095d1640ad8d31c19ba9b10b68d89c89a597681b1608db9bd21211d0d393514818389604f90d11c02584882f8789b91748b821580000020798a82e0779938518cd8428739e781d9ad8dc01992d80016d1df81680103802c078000300340000a0180141500000400000003000000018000000200100100c0000681401a050110020020241b0190080280a0000060581000803c0081700200e00c010000040080000a0a201400000004018030020a6004190050000000800c002030018020121d40381900000c0000001e0000680007605c010080520000a800028008088030680000081d00c0601400f00400408802008000000000040040280200000c2a80c0020040080800200c0000000000c0000501e034200240080000003900200c000040260000180500208803000000000028000121c8000050160380080202400404003006000020000540f0030340060740a81800e0000101d00a068040010000240580000000c000000040000200400001c0202a0000000000400001c0c81c02800000000000034000000020140100e06a000010000100000580c00000400002010000000030120
  | 9 => 0xf78e700013c84400000007e0c60001d889e8530c900012a89980004206f82b8430000000000f751e1bf00010b0000000001501fc95987f8ad19b99c8001d216498e94b1111fb1761e38a40d085b1c49a903d0c39a611b99d9140ee1b30861a99bf974103873d5917f89387c0049a70359d489a2029548978a68ab167a090bd85c8fb1eb02a12d1ea91f88b1d68279988fa8d0132845a1e886910a0200004f20c9af00007912080003f9700a60231960001a480013c13780015a0000d51e48c08001cc93f98b05f0730000c315b0b38c18481f00290b01058539c91f9890809a0996e00000b854057cca1ea06c0002011b71e11fb9010001dd1f396b00004d8001e91d91ef1720ce1835f280005d0bb0c580002b0ec15519e0be00001102206800e00019e8000b098c0001f90000000000590000000fd9ae0e91fc0b888380003205497e05b82406890fa080179e5df71e98439bc81c8758369900810710001281488001ed9ce8000000000000002018000f41fe00019721b0000000d580008a1f48af8658e5837a1d0bd0be8d11711cd9d599300009a92480002d04c0000001558dad8b80015e8001fa8000f300000017b0000e480001180000000000000015280017f11198606400016c00000000c0000000000000000000001bb05898a1090e780002e900dc70ea95790505d86690a01a0af06318102a9301f407d0000740cd13d9d38ec8229c601f8001d787a0000000ff8000000f080002680010d8000de14480004e15e1de1250fc8001c203f1d50849479798001340000eb8001920001b480009c18d8f184a9b0a1a0000001228001f89048ba1b89f3ccf17d91e9068000001800000000c998914c0a98f69fa03488a8158879de9f10c01191180264771ff91f0171e58000001a30002000000cb00013916113118c88d0da1b299a98483b8c40d249c8bb9b592c05588c04d0609b181e80d95303d4ca9071850d49d993b21a93b8b50840bf1bb8670f201092300018080017d17715392f0b619793220c09e1eec160000001dc8001be80016a95b8f70898000001e08e6a08a130000f38888831f08000c899140002181a9a7802d29a0e1670ba8d3ce38829db94e9fd0078958ce9f504119a21680a0a583a94f0021efd30919a1411a0001c32129621440000000000299858000001060bc15610c80000000002c1781cf1389918001a208d94e00894980021199481689f80d0ea0bf83c9b801814c9d714a8b71d18880ee95a86d98194f828c000000b212a00015716f80019111480000b0a3d2e94b8f80400001c51e70000000000729e18001bda1f00004b8c68da83c04fc8e8b10000000498b280000021d8f51aa8001a113186996ba1e12789b04920b8500980000aa0000fe1269b20cc8200890b64001cb19421b8000708c28001ff0cc1ee9990
  | 10 => 0x581e89878001064001d312b80017083880012011713f1438ed95c80a83309193751a9638ac1089271c68f88f98f28a30900238d7872038158a059b41a800088042c83e90806d19694313cc969650701958000df8000001954000192180039510001a521792213701e01c1128d80b4950a1120e9899258600001688b18000c10c200008203e17320f04616c9c58aa9d60ef104197cd608e218a0099f1ab9ab1fd8000450041750000598000b41ca05280020ecb31950001349ec00003111884718fa108000018000000d181388b94bd660249d11be00007b8c80000fc05c1239669af9fe80000016e80000015d80000017c8a70d28fdd019618fa18f02880002f052135c0100007817188c80000011791697281510c00009d8000808fd0000662148282071d014a0000e285e0561831a887e988a160001928001c080019b0058030a
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xb00000230000f801f246400064b940038e888a04016210d120340861836008070c7098f10000211a78a92084450110000c18d3c21000cb0050764f525d2639480141d931417498e520050b648505d2639480141d9314374586520050b64850dd1619480148d9210673d964200513648509cf659080141d93d097598e420050764c415d6639080142d921057598e420050764c41dd5609080142d9210775582420064361584dd9320c801a0e85a13764c8320050b64b535d0625440141d9314174189510050b648505d0625440141d9310575189410050b648415d4625040142d9210575d81410042b660649ca534840141d9314174189500050b648505d0625400142d9214174d85500050b64b435d4625000141d9310575189400050b648415d4625000106d981967290d2000433261764c832440014c4964c9710c91000532259325c0324401d3309855151501100d54c25d545454044001930875515150110074e8261424854044035560975495148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x94e
  | 6 => 0x94d
  | 7 => 0x98a
  | 8 => 0x98d
  | 9 => 0x98e
  | 10 => 0x3
  | 11 => 0x150a
  | 12 => 0x150d
  | 13 => 0x150e
  | 14 => 0xa0a
  | 15 => 0xa0e
  | 16 => 0xa4a
  | 17 => 0xa4d
  | 18 => 0xb09
  | 19 => 0xb0d
  | 20 => 0xb0e
  | 21 => 0x1549
  | 22 => 0x154d
  | 23 => 0x154e
  | 24 => 0xb89
  | 25 => 0xb8e
  | 26 => 0xbc9
  | 27 => 0xbcd
  | 28 => 0x3c9
  | 29 => 0x3ca
  | 30 => 0x3cd
  | 31 => 0x3ce
  | 32 => 0xcc9
  | 33 => 0xcca
  | 34 => 0xccd
  | 35 => 0xcce
  | 36 => 0x15c9
  | 37 => 0x15ca
  | 38 => 0x15cd
  | 39 => 0x15ce
  | 40 => 0xd09
  | 41 => 0xd0a
  | 42 => 0xd0e
  | 43 => 0x1609
  | 44 => 0x160a
  | 45 => 0x160e
  | 46 => 0xd49
  | 47 => 0xd4a
  | 48 => 0xd4d
  | 49 => 0x1649
  | 50 => 0x164a
  | 51 => 0x164d
  | 52 => 0x1049
  | 53 => 0x104a
  | 54 => 0x98955
  | 55 => 0xb0956
  | 56 => 0x209
  | 57 => 0x8a
  | 58 => 0x4
  | 59 => 0x1409
  | 60 => 0x128a
  | 61 => 0x1849
  | 62 => 0x1489
  | 63 => 0x180a
  | 64 => 0x130a
  | 65 => 0x19c9
  | 66 => 0x14c9
  | 67 => 0x198a
  | 68 => 0x134a
  | 69 => 0xb4e
  | 70 => 0x16ce
  | 71 => 0x170e
  | 72 => 0x409
  | 73 => 0x128e
  | 74 => 0x449
  | 75 => 0xe8e
  | 76 => 0x178e
  | 77 => 0x1709
  | 78 => 0x1889
  | 79 => 0x1a09
  | 80 => 0x8e
  | 81 => 0x138d
  | 82 => 0x124d
  | 83 => 0x8d
  | 84 => 0x128d
  | 85 => 0x1a89
  | 86 => 0x1949
  | 87 => 0x198d
  | 88 => 0x134d
  | 89 => 0x138e
  | 90 => 0x124e
  | 91 => 0x180e
  | 92 => 0x130e
  | 93 => 0x170d
  | 94 => 0x140d
  | 95 => 0x40a
  | 96 => 0x44a
  | 97 => 0xecd
  | 98 => 0x17cd
  | 99 => 0x170a
  | 100 => 0x188a
  | 101 => 0x1a0a
  | 102 => 0x20d
  | 103 => 0x1a8a
  | 104 => 0x194a
  | 105 => 0x19cd
  | 106 => 0x14cd
  | 107 => 0x20e
  | 108 => 0x140e
  | 109 => 0x184e
  | 110 => 0x148e
  | 111 => 0xcc3d1
  | 112 => 0xcc3d2
  | 113 => 0xcc3d5
  | 114 => 0xcc3d6
  | 115 => 0x44d
  | 116 => 0x178a
  | 117 => 0x104d11
  | 118 => 0x1a0d
  | 119 => 0x17c9
  | 120 => 0x104d52
  | 121 => 0x188e
  | 122 => 0x40e
  | 123 => 0xb4956
  | 124 => 0x289
  | 125 => 0x198955
  | 126 => 0x184956
  | 127 => 0x1a9951
  | 128 => 0x5c9
  | 129 => 0x45651
  | 130 => 0x58a
  | 131 => 0x41612
  | 132 => 0x1a9952
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 43
  | 7 => 1321
  | 6 => 4060
  | 5 => 1087
  | 4 => 36
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
  | 8 => packedAt gbK8 (1258+((h/20+packedAt gbK8 (1118+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (55165+((h/524+packedAt gbK7 (48877+(h % 524)*12) 12) % 2282)*12) 12
  | 6 => packedAt gbK6 (214250+((h/1490+packedAt gbK6 (194880+(h % 1490)*13) 13) % 5903)*13) 13
  | 5 => packedAt gbK5 (68258+((h/375+packedAt gbK5 (64133+(h % 375)*11) 11) % 1353)*12) 12
  | 4 => packedAt gbK4 (2598+((h/13+packedAt gbK4 (2520+(h % 13)*6) 6) % 53)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xf0fffc78387f0fe031f81ff03f14c13e1bc673
  | 1 => 0x7f0e03803f87f0fffe3fe07fc02b06d824fb9c
  | 2 => 0x7ff003ffc007ff003fc0007fffcc38e1c70c1f
  | 3 => 0x800003fffff800003fffff8000f03f01f80fe0
  | 4 => 0x3ffffffffffc000000000ffc001fff000
  | 5 => 0xfffffc00000000000000000000fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x90121810180b0121904845108a00400a09c231
  | 1 => 0x31042800088110489212412482010258005294
  | 2 => 0x4aa041aa4004aa022480824b344c18a0c60c0a
  | 3 => 0x82cca550000429259a0104b02d01700d40
  | 4 => 0x88113773666cc9700010c0218fec001bfa000
  | 5 => 0x6cc9e006044088180006100c20ffb7f4000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeceee0feeefeeafeeceee0feeefeeafeeceee0feeefeeafeeceee0feeefeeafeeceee0feeefeeafeeceee0feeefeeafeeceee0feeefeeafeeceee0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36316
namespace PEqualNP.Outside.L_meta_36316
open PEqualNP.Outside.L_meta_36316.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 26 := bs1_3_0
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
theorem bs1_4_128 : Interval s1Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 134 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := (concat bs1_5_0 bs1_5_32)
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
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 6 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 66 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 42 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_3_0 : Interval s5Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 6 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 66 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 42 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 36 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1056 : Interval gbAtlas 5 1056 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1087 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))) (concat (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896)) (concat (concat bgb_5_928 bgb_5_960) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056))))))
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
theorem bgb_6_4032 : Interval gbAtlas 6 4032 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4060 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 bgb_6_576)) (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704))) (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832)) (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960))))) (concat (concat (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216))) (concat (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472)))) (concat (concat (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 bgb_6_1600)) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984)))))) (concat (concat (concat (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 bgb_6_2240))) (concat (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368)) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496)))) (concat (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624)) (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752))) (concat (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880)) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 bgb_6_3008))))) (concat (concat (concat (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 bgb_6_3136)) (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 bgb_6_3264))) (concat (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392)) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)))) (concat (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648)) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 bgb_6_3776))) (concat (concat (concat bgb_6_3808 bgb_6_3840) (concat bgb_6_3872 bgb_6_3904)) (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 bgb_6_4032)))))))
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
theorem bgb_7_1312 : Interval gbAtlas 7 1312 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1321 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat bgb_7_576 (concat bgb_7_608 bgb_7_640))))) (concat (concat (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800))) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)))) (concat (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120))) (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 43 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeceee0feeefeeafeeceee0feeefeeafeeceee0feeefeeafeeceee0feeefeeafeeceee0feeefeeafeeceee0feeefeeafeeceee0feeefeeafeeceee0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276940512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36316.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.or,[2,3]⟩,⟨.or,[4,7]⟩,⟨.or,[1,6]⟩,⟨.and,[8,9]⟩,⟨.or,[1,4]⟩,⟨.or,[5,11]⟩,⟨.or,[5,7]⟩,⟨.and,[10,12]⟩,⟨.and,[0,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276940512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276940512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36316

open PEqualNP.Outside.L_meta_36316 in
theorem PEqualNP.Outside.L_meta_36316 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276940512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276940512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
