import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36737.Model
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


end PEqualNP.Outside.L_meta_36737.Model

namespace PEqualNP.Outside.L_meta_36737
open PEqualNP.Outside.L_meta_36737.Model
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

def SBf (j : Nat) : Nat := [6, 4, 6, 6, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36737

namespace PEqualNP.Outside.L_meta_36737
open PEqualNP.Outside.L_meta_36737.Model
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
end PEqualNP.Outside.L_meta_36737
namespace PEqualNP.Outside.L_meta_36737
open PEqualNP.Outside.L_meta_36737.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xf807f807f80fe03ffc0fc0fc1f80fe07f64cc7
  | 3 => 0x7fff8000ffffffff000ffe000fffff870ff
  | 4 => 0xfff80000000fffc07fffff000000fff81f80f8
  | 5 => 0xfffffffffff000007fffffffffff00001fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8304850508020810430c50c228e164922955b
  | 2 => 0x5552d534a39653aa3e0b54b51b12aac7564cc5
  | 3 => 0x46a4a4a5352a95345ad820db4824cd969870ae
  | 4 => 0x64c6c6c6c6cd1a276f6db6821248f1e31f80f0
  | 5 => 0x87070707070e1c38738e38e39c7081041d6a00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaaaaa00a000aaaaaaaaaa00a000aaaaaaaaaa00a000aaaaaaaaaa00a000aaaaaaaaaa00a000aaaaaaaaaa00a000aaaaaaaaaa00a000aaaaaaaaaa00a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36737
namespace PEqualNP.Outside.L_meta_36737
open PEqualNP.Outside.L_meta_36737.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1804821c25000c200ef32de32dc32ec32cc32bf41bd41be40bc40
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xc20684a0e002a7294658e540cb1aa819630cb41c6192838c329031864204d54440
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xa0180a1586540ca0d650cb418359432103043254440
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | 2 => packedAt s2K2 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (156+((h/3+packedAt s2K4 (144+(h % 3)*4) 4) % 14)*5) 5
  | 3 => packedAt s2K3 (224+((h/2+packedAt s2K3 (216+(h % 2)*4) 4) % 10)*4) 4
  | 2 => packedAt s2K2 (155+((h/1+packedAt s2K2 (152+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffe07fffffc0fffffffffe07fffe3ff1ff
  | 1 => 0x81fc0fff83ffffff0783c1f03ff87fffd24e3f
  | 3 => 0xfe000ffffc0fc1fff803fe003fff8781e38fcc
  | 4 => 0xffffff001fffffc00003ffff801fc0ff0
  | 5 => 0xfffff000000001ffffffffffc0000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8828002300208000188442118a0088940490d5
  | 1 => 0x24519644194530cb032191a214c85568d2462a
  | 3 => 0x149aaa8928ea13556842f484a755060d638b4c
  | 4 => 0x59634d125283a5a6b5e8210939a66031bc0db0
  | 5 => 0x61838e1c630c39f8c67339ce01c44441fb6000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36737
namespace PEqualNP.Outside.L_meta_36737
open PEqualNP.Outside.L_meta_36737.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x28080380605a40050001120c00081de43dd43de32dc32de31dc31ee21ec21df30dd30ef20ed20
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x130400a6292871d540c63aa9985914520
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
  | 4 => packedAt s3K4 (212+((h/4+packedAt s3K4 (192+(h % 4)*5) 5) % 19)*5) 5
  | 3 => packedAt s3K3 (111+((h/1+packedAt s3K3 (108+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7fffffc0fffff03ffff83ffffc0fffe7c7e3f
  | 1 => 0xf81fc0fffffffffc1e07fc1e07ffffff9393ff
  | 2 => 0xffe000fff03f07ffe007ffe007ff0781e3e3cc
  | 4 => 0xffffc007fffff8000007fff801fc03f0
  | 5 => 0xffffff00000007fffffffffff8000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1082880460822100622880a231484c94242615
  | 1 => 0x224511488514822c0c832414429191689190ea
  | 2 => 0x5149aa9123a82d55a125cac094ea460d62e34c
  | 4 => 0xe5963ce24a0eb79ad7b06291273ce431fc03b0
  | 5 => 0x861830c38c30c6e319c67319c0308041db5800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeac8c88888eaeaeaeac8c88888eaeaeaeac8c88888eaeaeaeac8c88888eaeaeaeac8c88888eaeaeaeac8c88888eaeaeaeac8c88888eaeaeaeac8c88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36737
namespace PEqualNP.Outside.L_meta_36737
open PEqualNP.Outside.L_meta_36737.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x90380001f0018015246c00000005804aac01a0430022103930a328c000000000f26a00140861505529019600743a04e5d08900780111a300089004040000040003ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x226783a92249e6c5098742c9688442a00567c725c1a600400085e16b040aa2012aca20c1c18a800588c343e00229c0000007e28527a9a108a3206000e8e70b2862e0a1e4c4600004a6eaea694000084763c3890004800424e6830006462a03600005a005400006a6680a4148204008050210102001001a484828202000023a0020800040052a06baa921d794a43b7a92876c5250f3ea8a1f3d4943ae29287cc5250e98a4a1d794c43af29e855d53d0b3a87a15d94742baa8e855f5350ab8a6a16750d42af298855d5310abea9195755232af294653e540ca7aa81957d5032cf2a0655d540cb3aa8194755032af29065ce520cb9e84197310832af29e835d53d073a87a0db94b41b6a96839d43506bca620d754c41b7a92636c524c67ca818cf550319f2a4433d54886bca710d754e21e6194435f53486b8a690f30c821af29e815d53d033a87205794c40aea98819d43102dca4205b54840bb2888175511027ca9984f55330b7294616d528c39865905794e20aea9c413f5448278a89057d4d20ae29a41cc32482eea2905d145209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xb08a8018002e01810ec1e68052092609602248072831028030380c0168c6250f42c550d51d0a1d6595032c3189540cb0d54d0832b1987420ca4d6510832a318943d070d4354b41a3189435064c6254c41a3590328870e540ca2187590534868d640c8219318953d028c6250e40a3189431030d4354840c550d511028d640cb2087592538828d640c920c315032483443214520
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1802892000028239286a8e858155261d083281aed2a06510d047250d5110206bb0a819241415d03214520
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
  | 4 => packedAt s4K4 (2640+((h/30+packedAt s4K4 (2430+(h % 30)*7) 7) % 109)*8) 8
  | 3 => packedAt s4K3 (990+((h/8+packedAt s4K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s4K2 (302+((h/2+packedAt s4K2 (294+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe07f07ff83fffffc1e0ff8781ff87fff4e4e3f
  | 2 => 0xff8007fffc0fc3ffe00fff801fff87038f8fcc
  | 3 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x420a00230020800062110088c50089281090d5
  | 1 => 0x89144a441945212c0c8648510a4852d146462a
  | 2 => 0x4526948928ea0655a10b95025395041a8b8b4c
  | 3 => 0x9658e7125283ab9ad7a0c4449ce66063f00db0
  | 5 => 0x1860c61c630c33e319cce66700c44083ed6000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36737
namespace PEqualNP.Outside.L_meta_36737
open PEqualNP.Outside.L_meta_36737.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53902faa7205f94a40bea94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea98817e52103dca4205b94840bea9081ed52102daa4205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7185f94a30f7294616e528c2faa5187b54a30b6a94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f721241ed42483de64907b0c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd98621f830c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0x14000160180006006020840000a0100403812115f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250fdea4a1dbd4943be29287ec5250ed8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210fdca421db94843bea9087ed5210edaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855f5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6215f54c42df21885bc4310afca4216fd0842f721085bd4210bda84216b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbdc84997b50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0fb94b41b7296837d52d07daa5a0db54b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131bfa9263ef524c6dea498df14931f6292636c524c7ee6298f78c531bfa8263fb504c6f6a098df14131fc2826378504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9
  | 2 => 0x16f000001010752a21bcc523639a4110a23b28e0ece88000621e10d1553583b1138df092610958cd042000000d10008348b06a3a66c47589d0e49151c8000589551c0c601c0012700008c7e03b9444ac9000000b10e570490004222607f91000000000154174000000001705d86a8d92823a4000a9000470000000006803600014e6c01920b00884d0f0c40ca3d8fb01f21800cd40da4881fc8f83f0e838c260670004dc001864545fcd08000003f8b98f32bc000488a419e9608f1ca04a000ae8162700000023214c7d0f82033867e9118340b601c4103e35e528fa85e0aa1a40002f4a295d0f9503de000a18bb12c4c4f216b000270de8fd0005580000044c58c000001104d000000276890002213724bc0021c1ae000970062360001524200000017000090001171b42a49400018c4a4598950331467112584d1204f4a31c8000688000004128dc368ed4a6664c48f73c679cad9cc1d030c00124482934ef8d40a4774911751ce500398e031a8bcf60803b46546423145a538551712469251d0203f8054d38140446981b9d8078338181aa39c370c1218460480000f144a1389b0bc24e2b48c0a01ea5dce08000000d44618548c00013a2816c000408842d47841ca100b8880a584b0000ac5ca2b0c86e06816e000770479e80005310b96233e0009295f0007f8000a806c2191aa0f16e604bc8db22a740ab8be0023c0000000000000004f000000de10f0827590908a35c0640d0bf2b27942c19e0005f00000022808c0000000093d060f20e2074db1330a06f90d9650383e4000000700008283d0003bc0002d29a0000000001e0a02c8990004f802a2c00006c810003225e90b0171345c00018312a40ce499c3280009d0ea0ec04cf908947a5f80f000000000be92818a4f09a9191641504f9ee0c068c8094f1c432521a041601e45987032042cfc9300f4199198dd0842b0308972e4674a4a29468814121ea10a1751f91a0805b4000000001f47d1ad4780e8311d5400600c58e41264c800000000000002223fe8203e1611f00a4eb8cc1b03052509b3566ec8e9983527f40680c0004348498f31c5b06f19a01081c050470be250049394026d4000f4004020060000401804030080080e0481a00010000080000e06000010020004a00000020000580c0183201800000000c0821106c000000181404808038100000200008018080500000856078000002c0a00c0100a0383800818058000382004800038000b00010814040100109002822038000380401022010220080e020120c8040101803000018040200c000040b000078041586a048060381200002010060100803800028080c8180000000002038240001c010080801c0101c02000010040900a0080c10010080000681a0b8001200c040000180005000038040101400004000020b820000
  | 3 => 0x1070562147645a08b3484a4fb917000520909c73c0438000b53da398e781228a1b89f8003cc92000011000110cb1600d676cb21681846cc6392d222294c400008a400601743f63ece914211c7892397b30e568e31693e270070a1d47c7a4f99060ae6fc5719b34a168a99b20fc3b8bc20a0203580c0021627504f10808644841a4c000000e59eb2ce2889311342a65c29a190a20007e0af000000130ca1a441c4692c2b06dcc92540f632c00063094000ef0680000007280017a34c00206384714c98a13742ac00
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3210866f65484219dd95210866f6254f409b18953d031d5310f40ab58843d029c6350b40ab58b41d026f62546409b18951902ad6210d40a718d425032c52509408f99741502ad62d05408f596411032d5290440cb548411032d52d00408fd95401032d52500409ed95401026e62153309b58854cc2d8604c7309b98b548c26d62d52309b988548c26d6215230cb952528c32d5494a30cb951528c32d5454a309bd89544c26c62551309dd85544c27461551309b988544c26d62151308f990524c23d641493097997314c2d8604c5309b988540c26d62150309d984540c27561150308fd91510c23c64544309bd89510c26c625443097596310c23e64940308f592500c25f654c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59053c832c5450b20b318d42c82ad640cb20d354c32c82ad64c87209798f548825d63d52208f993538823d64d4e208fd91518823c645462097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d209b195424832c5450920b318d424826e65cc920ab590324826e65c8520ab593214823d65950208f990540826e62150208f993530823d64d4c209b98b530823e6414c208f59053082766114c209d584530826d6588420cb552210832d5408420cb553200826f6548020cb551200827b65480209b98a54c426d62953108fd9153c423c6454f109bd8953c426c6254f108f99252c423d6494b109b988548426d62152108f993538423d64d4e109b98b538426d62d4e108f990528423d6414a108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534427b6054d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c524435853c41109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c755153043586054c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520435953cc0109e59430042f1610c0109e596100427765440109ed9510042d86344010
  | 1 => 0x81720040101400000030000d00c04014060080803c03008000980200c0c000000200001005018020000001c030103a00c000000403002004000040200005018000000204c060180000804018090000503c01000000000e00808004000340401c030080000c0a03403028000080400c0101404004050140000c0200800004170080a000080000200400004070100100c0104c010100e028000100400c05008020000103405000089bd895190e6c62546439b98a5090e6d6294243d3d0c5250f2e43149438fd954310eac6250c4397d954310ecc6250c43cbd0d5210f2d4354843ab18943d0aad6210e42d35885350a3e65d0d42c714f4350b1c5350d42ab1894350b4c53d0942c714e4250a3d6590c42ab5884310aad64908428fd954210a9c63508429bd954210acc6350842abd954210b2f6550842e3d8d4210aac6350842e318d4210a8c6350842cb54d4210b2d4294442cb5095010b2f5410b328fd9151cca3c64547328f99250cca3d64943329e980548ca796015232b3588438cb8c4390a32cb151428cacc6350a32e3d0d428ca3e649513297d8d544ca6f62551328f994544cb2d62151329b996424cb2c54909329b195424cb2c5450932b318d424cb2c54cc932c7152324ca3d6595032c718d540cb2c62550328f990540ca6e6215032c7553430ca5d6510c329b597420cb2d54d0832e3d0f420ca6d6510832cb550420cb8c4310832cb552320ca5f654c832a7191320ca6f654c832ab191320cb2d544c832ab588439069c6350a41cb94942906ad62d06419b988505066d62141419bd89531066c6254c41c754c43106ad6210c41a718d42106ad62d04418fd95411067765504419b98854cc66d62153318f99250cc63d64943319b98a50cc66d62943319b98b548c66d62d52319b98a548c66d62952318f992528c63d6494a318f992544c66e62951319b58a544c67a60951319e582544c66f62551319b189544c67b60551319e181544c63e6515131cbd53524c72c54d4931cbd50524c72c5414931ced53504c73854d4131dad4b504c76852d4131ced50504c7385414131dad48504c7685214131d68c4504c66e62150319b588540c67a60150319e580540c65f654c431b6181310c677654c4318f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f219798f548865d63d52218f993538863d64d4e21cb95142886cc6350a21ab59032886ad64c86219b58a544865f63551219718d544867b60551219e181544863f6454d218f191534866f6254d219ed8153486786054d218f990504863d64141219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219e98053086796014c218f992520863d64948219b596420872c5450821b318d420866d650c821ab590320874d530c821ab59
  | 2 => 0x206c5000848006eaf657a647b19e8705200200a381a752e44808e1c0ba3a2b2938f0188f25119c00000c40c6b79b44e27c0012200000000000003e5e00076800b58005e9bca2102ad900299c60192a32a740026ebe1a20022e210000001e2193a75ac8bf00000000001183700045800ab1fc7422c2a0002da72710001b8c01991c001a8001be5d0009ea4c4289a7c80000000002cc540000f25c0d1e80618e9413cb014696aa88a926002842b0bc778b403934220005f312000004a2f4000008a000628008c140002aa0a800418d0001902f9ee000540013000000002bc588009080092000822b40da3e170cc8411ea01e61a0003e2d4001ae001c8003023d15491ac45306a622367d2a4a5a70a60d2139b84481ca7222662ce3102c05aea288debe800c589681004000c2030ee1e0e0af8580091428038000007e2c2700ae000003b00000000002f294800b40229fa0a3aa78000005b000002767c06c0016a0030e61800000d41404688000001ce002020000000000000641c800002c6000904b2867d84a000000023c3589800244000006c148900920017e0029078026002da000007f80000000c180000000001e2a52e217a826a800abb0002000000e600000c2ad26110cba04400000048f613000989b208000201a4002a2168600ba56a321a4c9109a0b2708001d152bf8000000092810000000000000000898000000000000000fc4ba0e5b8324f8fa0018c052e0ae8da600001f1cc850005c1fa272246830c6499a002d81d994bba18000002511a412924d88a952b8978248d1ca85ab033800001423f80a438400a056790006d87e3629e572327a966001600e8b00015876266a6800420b8bc09e00000388aa83124538006b0c800238000009b0000026a5d8420000012000b9a580026000000c108c000000007a8e95a69800592a66080000000b2956c20000000077168a28302080065800b70000000000000390000021e2900052aec7480000000a
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x6141b60160108acab0ba631c288012380932a0003469e002800105182084340191c1aea31a842150c7350a5110a8639a84a80854a5c05450a32c18a831a851948e76d0d428cb062a0c6a12658318c6255032c1acba1e841950d7510c420ca163b2a8990658318e5250a41a18e4a988620e0d5358843107072a0c6a1443435cc5450821a52e02a28410e0c5418d42086863a2a61904383591530c821a18e4a9887a060d5358843d0306318a4a1281435cc5450b20c18a831a859050c7454c32c8306b22a619641831506350920
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x830010a09801506350a32a0980150635082180c87591530c82180c87591530cb20
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 601
  | 4 => 396
  | 3 => 28
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (18227+((h/200+packedAt s5K5 (16227+(h % 200)*10) 10) % 722)*11) 11
  | 4 => packedAt s5K4 (16368+((h/132+packedAt s5K4 (15048+(h % 132)*10) 10) % 575)*10) 10
  | 3 => packedAt s5K3 (1426+((h/9+packedAt s5K3 (1372+(h % 9)*6) 6) % 37)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfc0fff81ffffff81ffc3ff07fc3ffffb1e31ff
  | 1 => 0x7ffffffe07fffffe07fc1fffffc1fffce3fe3f
  | 2 => 0x7ff01ffff80fe1fff8001ff87ffe3c0703cfcc
  | 3 => 0x80001ffffff001ffffffe0007fffc007fc0ff0
  | 4 => 0xffffe000000001ffffffffff80000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x521488c4122508059412544941265510e10d5
  | 1 => 0x84281103244801602840a0928408aa060e62a
  | 2 => 0x50a4da2490e913aaa82313d44eb43037034b4c
  | 3 => 0x42cb14492481c54d34ea4080732900c6b40db0
  | 4 => 0x630c1871c70e19f1c7339ce602302307dbb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeec8e888eec8e888eec8e888eec8e888eec8e888eec8e888eec8e888eec8e888eec8e888eec8e888eec8e888eec8e888eec8e888eec8e888eec8e888eec8e888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36737
namespace PEqualNP.Outside.L_meta_36737
open PEqualNP.Outside.L_meta_36737.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001017fd5003fe54017f55003fc54017fd4c05fe53017f54c05fc5300ffd0c01fe43007f50c03fc43017fd4805fe52017f54805fc5200ffd0801fe42007f50803fc42007fcc801fe32007f4c801fc32017fd4405fe51017f54405fc5100ffd0401fe41007f50403fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc5000ffd0001fe40007f50003fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a2000dfd9510004feca8802bfe65440057f32a200aff59510055faca8802bfc65440057e32a200adf19510014f8ca88003ff64440017fb222000efd91100057ec888027fe64440037f3222000ff59110005fac888027fc64440037e3222000ef1911000d78c88802bff5444013ff2a2200aff5511004ff8a888003ff63440017fb1a2000f7d8d10005bec688003fe63440117f31a2000ff58d10005fac688003fc63440117e31a2000f718d10005b8c68802bff5344015ff29a200aff54d10057f8a688027ff4344001ff21a2000ff50d1004ff88688003ff62440017fb122000fbd8910005dec488003fe624400f7f3122000ff58910005fac488003fc624400f7e3122000fb18910005d8c48802bff5244015ff292200aff54910057f8a488027ff4244001ff2122000ff5091004ff88488003ff3244001ff1922000ff4c910007f8648802bff5144015ff28a200afd94510057faa28802bf55144015fe28a2009ffd0510007fc8288003fd4144013fe20a2000ffcc510007fc6288003fd3144001fe18a2000ffc8510007fc4288003fd2144001fe10a200affd411001ffca08802bfd5044007fe2822009ffd011001ffc8088003fd4044007fe2022000ffcc11001ffc6088003fd3044007fe1822000ffc811001ffc4088003fd2044007fe1022000ffc4110007f6208800ffe1044007fb0822003ffd941001dfeca0800ffe65040057f3282003df99410014fcca0800ffd650400b7eb282003df59410004faca0800ffc65040077e3282003ffd901001dfec80800ffe64040037f3202003ef9901000d7cc80800ffd64040017eb202003ef590100057ac80800ffc64040077e3202005ffd5010027fca808017fd5404009fe2a02003ffd8c1001dfec60800ffe63040117f3182003f798c10005bcc60800ffd63040017eb182003f758c10005bac60800ffc63040077e3182005ffd4c1002ffca608017fd530400bfe2982004ffd0c10007fc8608003fd4304009fe2182003ffd881001dfec40800ffe620400f7f3102003fb98810005dcc40800ffd62040017eb102003fb58810005dac40800ffc62040077e3102005ffd481002ffca408017fd520400bfe2902004ffd0810007fc8408003fd4204009fe2102000ffcc810007fc6408003fd3204001fe1902006bf9841002ffea208017fe510400bfea882005ff14410027fe8208003fe4104001fea082004ff10410007fe6208003fe3104001fe9882000ff0c410007fe4208003fe2104001fe9082000ff0841001dfcc00800fff5004007ff2802003ff5401001ff8a00800fff4004007ff2002003ff5001001ff8800800fff3004007ff1802003ff4c01001ff8600800fff2004007ff1002003ff4801001ff8400800fff1004007fb8802003ff8401001ff4200800ffd1004007fa8802000fe44010
  | 1 => 0xffe510801ffea88400fff14420077fe8210003fe4108001fea08400eff10420007fe6210003fe3108001fe9884000ff0c42003ffe421001ffe2108001f71084007ff4842003ff8421001fec21080077f3004003ffd402001ffca01000ffd5008007fe2804003ffd002001ffc801000ffd4008007fe2004003ffcc02001ffc601000ffd3008007fe1804003ffc802001fde401000ffe2008007fd1004003ff4802001fda401001ff9200800dffb2e2006bfd9710037fccb8800afe65c400dfeb2e2006bf59710037f8cb8800afc65c4001ffb262000bfd931006ffcc988006fe64c4001feb262000bf5931006ff8c988006fc64c400dffaa6200dff95310037faa988037fc54c4001ffb1e2000bfd8f10007fcc788022fe63c4001feb1e2000bf58f10007f8c788022fc63c400dffa9e2006ff94f10037faa78801bfc53c401bffa1e2000ff90f10007fa8788037fc43c4001ffb162000bfd8b10007fcc58801efe62c4001feb162000bf58b10007f8c58801efc62c400dffa962006ff94b10037faa58801bfc52c401bffa162000ff90b10007fa8588037fc42c4001ff9962000ff8cb10007fa6588003fc32c400dffa8e2006ff94710037eca38801bfd51c400dfaa8e2006ff1471006ffe8388003fe41c4001fea0e200dff10710007fe6388003fe31c4001fe98e2000ff0c710007fe4388003fe21c4001fe90e2000ff08710037fea18800ffe50c400dfea862003ff1431006ffe818800ffe40c4001fea062003ff10310007fe618800ffe30c4001fe9862003ff0c310007fe418800ffe20c4001fe9062003ff0831001ffecb0800eff6584007ff32c2002bf9961001ffacb08032fd6584007fe32c2003bf1961001ffec90800eff6484007ff3242001bf9921001ffac908002fd6484007fe3242003bf19210067fea90802ffe5484019feaa4200bff1521001ffec70800eff6384007ff31c2008bf98e1001ffac708002fd6384007fe31c2003bf18e10067fea708033fe5384019fea9c200cff14e1005ffe8708003fe4384001fea1c200bff10e1001ffec50800eff6284007ff3142007bf98a1001ffac508002fd6284007fe3142003bf18a10067fea508033fe5284019fea94200cff14a1005ffe8508003fe4284001fea14200bff10a10007fe6508003fe3284001fe9942000ff0ca10055fac308033ff5184019ff28c200cff54610067f8a30802fff4184001ff20c2000ff5061005ff88308003ff3184001ff18c2000ff4c610007f86308003ff2184001ff10c2000ff48610007f8430800efe6084007ffa842003ff9421001ffaa10800ffc5084007ffa042003ff9021001ffa810800ffc4084007ff9842003ff8c21001ffa610800ffc3084007ff9042003ff8821001ffa410800ffc2084007ff8842003fdc4210007f6210802bff65440157fb
  | 2 => 0x2001ff8c71000efc6388027ffa9c4013ff94e2009ffaa71004ffc5388025ffa1c4000ff90e20007fa871004bfc43880237eb144013ffd4a2003ffca51004ffd528800ffe2944012ffd0a2003ffc8510003fd428800ffe2144000ffcca2003ffc6510003fd328800ffe1944003ffd862001ffcc310002fe6188007feb0c4000bf5862001ff8c31004fff5188027ff28c4013ff5462009ff8a31004bff4188001ff20c4000ff50620097f88310003ff3188001ff18c4000ff4c620007f8631001fff2188001ff10c4000fb88620007fa431001ffc2188001f610c4003bf9822001ffea11000ffe5088007fea844003ff1422001ffe811000ffe4088007fea044003ff1022001ffe611000ffe3088007fe9844003ff0c22001ffe411000fef208800ffd9044011ffd952008dfeca900037f65480013fb2a4011ff99520015fcca90047fd65480237eb2a4011ff19520015f8ca900477c65480053e32a4000ffd9120005fec890043fe64480037f3224000ff59120005fac890043fc64480037e3224011ffd5120087fca890047fd5448021fe2a24000ffd8d20005fec690003fe63480117f31a4000ff58d20005fac690003fc63480117e31a4011ffd4d2008ffca690047fd5348023fe29a4010ffd0d20007fc8690003fd4348021fe21a4011ffd492003ffca490047ee5248023fea924011fb5492003ff8a490043ff424800fff2124000fb90920007fa8490003ed424800ffe2124000ffcc920007de649001ffe3248001fe9924007ff0c920007d86490003ff61480017fb0a4000ff98520007fac290003fc61480017e30a4011ffd452008ffca290047fd5148023fe28a4010ffd0520007fc8290003fd4148021fe20a4000ffcc520007fc6290003fd3148001fe18a4007ffc8520007de4290003fe2148001fe90a4000fb4852003ff84290047ff5048007ff2824011ff5412001ff8a090043ff4048007ff2024000ff5012001ff88090003ff3048007ff1824000ff4c12001ff8609001fff204800ffd9024003ff8812001fdc409000fff65080077fb284003ff99420015fcca1000ffd650801f7eb284003ff1942001df8ca1000fff64080077fb204003ff9902000dfcc81000fbe64080035f3204003ff59020005fac81000fbd64080015eb204003ff1902001df8c81003fff540801dff2a0400fff55020077f8a81000fff63080077fb184003ff98c20045fcc61000ffd63080017eb184003ff18c2001df8c61003fff530801fff298400fff54c2007ff8a61003bff4308001ff2184000ff50c20077f8861001efe620800fffa904007ff9482003ffaa41001ffc520800fffa104007ff9082003ffa841001ffc420800fff9904007ff8c82003ffa641001ffc3208007ffb084003ff98420005fcc21000ffd61080017eb084003ff1842007ffea21003
  | 3 => 0xe98a6000f74c530047f86298003ff214c001ff10a6000ff48530007f84298067ff504c007ff2826019ff5413001ff8a098063ff404c007ff2026000ff5013001ff88098023ff304c011fd9826003ff8c13001fbc609800fff650c0077fb286003ff99430015fcca1800ffd650c02f7eb286003ff1943001df8ca1800fff640c0077fb206003ff9903000dfcc81800ffd640c0017eb206003ff1903001df8c81805fff540c02dff2a06017ff550300b7f8a818022fe630c011ffa986008ff94c30047faa618023fc530c011ffa186008ff90c30047fa8618023fc430c007ffb106003ff9883003dfcc41800ffd620c0017eb106003ff188300bffea41805ffe520c02ffea906017ff148300b7fe8418003fe420c001fea106016ff10830047fe6418023fe320c011fe9906008ff0c83001ffec21800ffe610c0017f3086003ff58430005fac21800ffc610c02fffa886017ff944300bffaa21805ffc510c02dffa086000ff90430007fa821805bfc410c011ff9886008ff8c430007bc6218023fd310c011fe1886008f70c430007fe4218003fe210c001fe9086000ff0843001dfcc01800fff500c007ff2806003ff5403001ff8a01800fff400c007ff2006003ff5003001ff8801800fff300c007ef9806003ff8c03001ff4601800ffd300c007ee9806008fe4c03003ffecb9001eff65c800fff32e4002bf9972003ffacb90056fd65c800ffe32e4007bf1972003ffec99001eff64c800fff3264001bf9932003ffac990002fd64c800ffe3264007bf193200affea990053fe54c802bfeaa64014ff1532003ffec79001eff63c800fff31e4008bf98f2003ffac790002fd63c800ffe31e4007bf18f200affea790057fe53c802bfea9e4015ff14f200a7fe8790003fe43c8001fea1e4014ff10f2003ffea59001ffe52c800ff72964007ff54b200afdaa59001ffc52c800fffa164007ff90b2003fdc859001ffd42c8001f6a164007ff10b2003ffe6590003ef32c800fff1964007ff4cb2003ff8659001fec32c800fffb0e4007ff98720005fcc39001ffd61c80017eb0e4007ff187200affea390057fe51c802bfea8e4015ff147200a7fe8390003fe41c8001fea0e4014ff10720007fe6390003fe31c8001fe98e4000ff0c72003ffe439001fef21c800fff10e4007ff48720007da439001ffc21c802bffa864003ff943200affaa19000ffc50c8029ffa064003ff90320007fa819000ffc40c8001ff9864003ff8c320007fa619000ffc30c8007ffb2c4003bfd962001ffccb1000afe6588007feb2c4013bf5962001ff8cb1000efc6588007ffb244003bfd922001ffcc910006fe6488007feb244000bf5922001ff8c91000efc6488027ffaa44012ff9522009ffaa91004bfc5488007ffb1c4003bfd8e2001ffcc710022fe6388007feb1c4000bf58e
  | 4 => 0x22fc64cc03bffaa6601cff953300effaa998073fc54cc011ffa9e6008ff94f30047bca798023fd53cc03beea9e6008ff14f30047fe8798023fe43cc011fea1e6008ff10f30047fec598023fe62cc00f7f3166008ff58b30005fac598023fc62cc03bffa96601dff94b300effaa598077fc52cc039ffa166000ff90b30007fa8598073fc42cc011ff9966008ff8cb30047fa6598023fc32cc011ffb0e6008ff98730005fcc398023fd61cc0017eb0e6008ff187300effea398077fe51cc03bfea8e601dff147300e7fe8398003fe41cc001fea0e601cff10730047fe6398023df31cc011ff18e6008ff4c730007ba6398023fc31cc001ff90e6000ff88730007fa4398003fc21cc03bffa866003ff943300effaa19800ffc50cc039ffa066003ff90330007fa819800ffc40cc007ffb2c6003bfd963001ffccb1800afe658c007feb2c601bbf5963001ff8cb1800efc658c007ffb246003bfd923001ffcc918006fe648c007df3246001af9923001ffac918002fd648c007deb246000af5923001ff8c91800efc648c037ffaa4601aff952300dffaa91806bfc548c0337eb1c601bffd4e30047fca71806ffd538c011fe29c601affd0e30047fc8718003fd438c011fe21c6003ffd8a3001ffcc51801efe628c007f73146000bb98a3001ffac518002fd628c007f6b146000bb58a3001ff8c51806fff528c037ff294601bff54a300dff8a51806bff428c001ff2146000ff50a300d7f88518023ff328c001ff1946000ff4ca30047f8651800fff618c007ff30c6000bf9863001ffac318002fd618c007fe30c601bffd46300dffca31806ffd518c037fe28c601affd0630007fc8318003fd418c035fe20c6008ffcc630007fc6318003de318c001fe98c6008ff0c630007b86318003ff218c001ff10c6000ff48630007f8431800efe608c007ffa846003ff9423001ffaa11800ffc508c007ffa046003ff9023001ffa811800ffc408c007ff9846003f7cc230047f66118067ff654c0337fb2a6019ff99530015fcca98067fd654c0337eb2a6019ff19530015f8ca98003ff644c0017fb226018ff9913000dfcc898003fd644c0017eb226018ff1913000df8c898067ff544c031ff2a26019ff551300c7f8a898067ff534c011ff29a6019f794d300cffaa698067dd534c011fe29a6018ffd0d30047fc8698003fd434c011fe21a6000ffd8930005fec498003fe624c001feb126000ff1893003df8c498067ff524c033ff2926019ff549300cff8a498063ff424c001ff2126000ff509300c7f88498023ff324c001ff1926000ff4c930047f86498003ff614c0017fb0a6000ff98530007fac298003fc614c0017e30a6019ffd45300cffca298067fd514c033fe28a6018ffd0530007fc8298003fd414c031fe20a6008ffcc530007be6298003fe314c001f
  | 5 => 0xc82103ffc641081ffd320840ffe1904207fb0c821115fcc210887ff5108443ff2884221ff5442110ff8a210883ff4108401ff2084200ff50421107f88210803ff3108401ff1884200ff4c421007f8621081fff210840ff79084207ff8842103fec421081ffd2108401f69084207fd4842103ffec01081ffe60084077f3004207ff58021005fac01081ffc6008443ffa804221ff9402110ffaa010887fc5008441ffa004220ff1002101ffecb2000eff6590007ff32c8002bf9964001ffacb2007efd6590007fe32c8003bf1964000dfac920007ff5490003ff2a48001ff5524000ff8a92000fff6390007ff31c8008bf98e4001ffac720002fd6390007fe31c801fffd4e400fffca72007ffd539003ffe29c8001ffd0e4000ffc8720007fd4390003fe21c8003ffd8a4001ffcc52001efe6290007feb148000bf58a4001ff8c52007fff529003fff294801fff54a400fff8a520007ff4290003ff2148001ff50a4000ff88520003ff3290001ff1948000ff4ca40007f8652000fff6190007ff30c8000bf9864001ffac320002fd6190007fe30c801fffd46400fffca32007ffd519003ffe28c8001ffd064000ffc8320003be4190003fea0c8001ff1064000f788320003ff3190001ff18c8000ff4c640007f86320003ff2190001ff10c8000ff48640007f8432000efe6090007ffa848003ff9424001ffaa12000ffc5090007ffa048003efd024000ff6812000ffc4090007fc204801effd95400f5fecaa007bfe65500057f32a801eff595400f5facaa007bfc65500057e32a8003bfd914000ffea8a0007fe5450003df2a28001ff551400f77aa8a0007fc5450001ffb1a8000bfd8d40007fcc6a0003fd6350001fe31a8008bf18d400f7fea6a007bfe535003dfea9a801eff14d4000ffe86a0007fe4350001df21a8001ff50d4000ff886a0007bc4350001ffb128000bfd8940007fcc4a0003fd6250001fe3128007bf189400f7fea4a007bfe525003dfea92801eff1494000ffe84a0007bf4250003ff2128001ff509400077a84a0007fc4250001ff9928000ff8c940007fa64a0003fc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8000bf185400f7fea2a007bfe515003dfea8a801eff1454000ffe82a0007bf4150003ff20a8001ff505400077a82a0007fc4150001ff98a8000ff8c540007fa62a0003fc3150001ff90a8000ff88540007fa42a0003fc21500037fb02801effd414001ffca0a007bfd5050007fe2828001ffd014000ff680a000ffe4050007df2028003ff1014001f7880a0007f84050011ffb2e6008bfd9730047fccb9800afe65cc011bf32e60029f99730047facb98076fd65cc011beb2e60009f59730047f8cb98022fc65cc011ffb266008bfd9330047fcc998006fe64cc011feb266000bf59330047f8c998
  | 6 => 0x17eb064207ff1832113ffea19089ffe50c844ffea864227ff14321137fe819089bfc40c8445ffb2c4222bfd9621117fccb1080afe6588445bf32c42029f99621117facb1088afd6588401beb2c42009f59621117f8cb1080afc6588401ffb244200bfd922112ffcc910806fe6488401feb244200bf5922112ff8c910806fc6488445ffaa44225ff95221117faa910897fc5488401ffb1c4200bfd8e21007fcc710822fe6388401feb1c4200bf58e21007f8c710822fc6388445ffa9c4222ff94e21117faa71088bfc538844bffa1c4200ff90e21007fa8710897fc43884497eb144222ffd4a2103ffca51088bee5288445fea944222fb54a2103ff8a510897ff428840fff2144200fb90a21007fa8510803ed428840ffe2144200ffcca21007de651081ffe3288401fe9944207ff0ca21007d8651081efe6188445ffa8c4222ff94621117faa31088bfc518844bffa0c4200ff90621007fa8310897fc4188401ff98c4200ff8c621007fa6310803fc318840fff90c4200fbc862103fee4310803ff6088401ff3044203bf98221007fac110802fd6088401fe3044222ffd4221117fca11088bfd5088445fe2844225ffd022112ff88110893ff65484497fb2a4224ff99521015fcca90893fd65484497eb2a4224ff19521015f8ca90803ff64484017fb224223ff9912100dfcc890803fd64484017eb224223ff1912100df8c890893ff5448447ff2a24224ff5512111ff8a890803ff63484017fb1a4200ff98d21045fcc690803fd63484017eb1a4200ff18d21045f8c690893ff5348449ff29a4224ff54d21127f8a69088fff4348401ff21a4200ff50d2111ff88690893ff524840fff2924224ff5492103ff8a49088fff424840fff2124200ff5092103ff88490803ff324840fff1924200ff4c92103ff86490893ff5148449ff28a4224ff54521127f8a29088fff4148401ff20a4200ff5052111ff88290803ff3148401ff18a4200ff4c521007f8629081fff214840ffb90a4200ff88521007dc4290803ff60484017fb024200ff98121007fac090803fc60484077e3024224ffd4121127fca090893fd5048449fe2824223ffd012111ff8809081fff650840f7fb284207ff99421015fcca1081ffd65084437eb284207ff1942103df8ca1081fff640840f7fb204207ff9902100dfcc81081ffd64084017eb204207ff1902103df8c810887ff5408441ff2a04221ff55021107f8a81081fff630840f7fb184207ff98c21045fcc61081ffd63084017eb184207ff18c2103df8c610887ff5308443ff2984221ff54c2110ff8a610883ff4308401ff2184200ff50c21107f8861081efe620840fffa904207ff9482103fdca41081ffd5208443f6a904207ff1482103ffe841081ffe420840ff72104207ff50821007da841081ffc420840fff9904200fbc
  | 7 => 0x988b3fc654c4057e32a6200ffd9131005fec898803bf644c4015fb22622bff9913100dfcc898803fd644c4017eb22622bff1913100df8c898803bc644c4035e322622cffd513115ffca8988b3fd544c457fe2a2622cffd4d31047fca6988b3fd534c411fe29a622bffd0d31047fc8698803fd434c411fe21a6200ffd8931005fec498803ef624c40177b126200ff98931007fac498803fc624c40f7e3126200fb18931005d8c4988b3ff524c459ff292622cff54931167f8a4988afff424c401ff2126200ff5093115ff88498823ff324c401ff1926200ff4c931047f864988b3ff514c459ff28a622cff54531167f8a2988afff414c401ff20a6200ff5053115ff88298823ff314c411fb98a6200ff8c531007bc6298803ff604c4017fb026200ff98131007fac098803fc604c4077e302622cffd4131167fca0988b3fd504c459fe282622bffd013115ff88098823ff650c4117fb286208ff99431015fcca188237e650c4053f3286208ff5943114dfaca188237d650c4013eb286208ff19431045f8ca18823ff640c4117fb206208ff9903100dfcc818823fd640c4017eb206208ff19031045f8c8188a7ff540c451ff2a06229ff55031147f8a818822fe630c411ffa986208ff94c31047bca618823fd530c453eea986208ff14c31047fe8618823fe430c411fea186208ff10c31047fec418823fe620c40f7f3106208ff58831005fac418823fc620c453ffa906229ff9483114ffaa4188a7fc520c451ffa106200ff90831007fa84188a3fc420c411ff9906208ff8c831047fa6418823fc320c4557f3086229ffd443114ffca2188a7fd510c453fe2886228ffd0431007fc8218803fd410c451fe2086208ffcc431047be6218823fe310c411fb1886208ff4c431007ba6218823f5310c411ffb006208ff9803101dfcc018823fd600c4017eb006208ff1803114ffea0188a7fe500c453fea806229ff14031147fe80188a3fc400c40fffb2e4207bfd972103ffccb9080afe65c840ffeb2e4227bf5972103ff8cb9081efc65c840fffb264207bfd932103ffcc990806fe64c840fdf3264201af9932103ffac990802fd64c840fdeb264200af5932103ff8c99081efc64c844fffaa64226ff9532113ffaa99089bfc54c840fffb1e4207bfd8f2103ffcc790822fe63c840ffeb1e4200bf58f2103ff8c79081efc63c844fffa9e4227ff94f2113ffaa79089ffc53c844dffa1e4200ff90f21007fa879089bfc43c840fffa964207ff94b2103ffaa59081ffc52c840fffa164207ff90b2103ffa859081ffc42c840fff9964207ff8cb2103ffa659081ffc32c844fffa8e4227ff9472113ffaa39089ffc51c844dffa0e4200ff90721007fa839089bfc41c8401ff98e4200ff8c721007fa6390803fc31c840fffb064207ff9832101dfcc19081ffd60c840
  | 8 => 0xfd424118ffca1208c7fd5090463fe2848201ffd024100ff88120807bc4090461ffb2a8230bfd9541187fccaa080afe6550461feb2a8230bf59541187f8caa080afc65504037fb228201ffd514100ffca8a0807fd5450403fe2a28200ffd8d41005fec6a0803fe6350401feb1a8200ff18d41045f8c6a08c3ff5350461ff29a8230ff54d41187f8a6a0807ff4350403ff21a8201ff50d4100ff886a0803ff62504017fb128200ff98941007fac4a0803fc625040f7e3128230ffd4941187fca4a08c3fd5250461fe2928201ffd094100ffc84a0807fd4250403fe2128200ffcc941007fc64a0803fd3250401fe1928201bfd8541187fea2a08c3fe5150461fea8a8230ff1454100ffe82a0807f74150403ff20a8200ef9054100ff882a0807bc4150403fa20a8200ffd8141005fec0a0803fe6050401feb028200ff1814101df8c0a08c3ff5050461ff2828230ff54141187f8a0a0807ff4050403dfa028201ff10141047fecb98822ff65cc411ff32e6202bf99731047facb988befd65cc411fe32e6208bf19731047fec998822ff64cc411ff3266201bf99331047fac998802fd64cc411fe3266208bf1933117ffea9988bbfe54cc45ffeaa6622eff15331047fea798823fe53cc411fea9e6208ff14f31047fe8798823fe43cc411fea1e6208ff10f31047fec598823fe62cc40f7f3166208ff58b31005fac598823fc62cc45fffa96622fff94b3117ffaa5988bffc52cc45dffa166200ff90b31007fa85988bbfc42cc411ff9966208ff8cb31047fa6598823fc32cc45fffa8e622fff9473117ffaa3988bffc51cc45dffa0e6200ff90731007fa83988bbfc41cc411ffb066208ff9833101dfcc198823fd60cc4017eb066208ff1833117ffea1988bffe50cc45ffea86622fff14331177fe81988bbfc40cc455ffb2c622abfd9631157fccb1880afe658c455feb2c622abf59631157f8cb1880afc658c401ffb246200bfd923116ffcc918806fe648c401feb246200bf5923116ff8c918806fc648c455ffaa4622dff95231157faa9188b7fc548c4597eb1c622affd4e31047fca7188abde538c455fea9c622af754e31047f8a7188b7ff438c411ff21c6200ff50e31047f88718803ff628c401ff3146207bf98a31007fac518802fd628c401fe314622affd4a31157fca5188abfd528c455fe294622dffd0a31007fc8518803fd428c45bfe2146208ffcca31007fc6518803fd328c411fe1946208bf98631157fea3188abfe518c455fea8c622aff1463116ffe8318803fe418c401fea0c622dff10631047fe6318803df318c411fb98c6200ffd8231007fcc11880efe608c401feb046200bf58231007f8c1188abff508c455ff284622aff54231157f8a1188b7ff408c45bfe204622cffd9531165feca988b3fe654c4057f32a622cff59531165faca
  | 9 => 0x86ffe2846436ffd02321b7f881190d7ff654c86b7fb2a6435ff99532015fcca990d7fd654c86b7eb2a6435ff19532015f8ca99003ff644c8017fb226400efd91320057ec8990d3fe644c8037f3226400ff59132005fac8990d3fc644c8037e3226400ef1913200d78c8990d7ff544c869ff2a26435ff551321a7f8a8990d7ff534c811ff29a6435f794d321affaa6990d7dd534c811fe29a6434ffd0d32047fc8699003fd434c811fe21a6435ffd493203ffca4990d7fd524c80ffe2926434ffd093203ffc8499003ee424c801fea126400fb5093203ff88499023ff324c811f79926407ff8c93203fbc6499003ff614c8017fb0a6400ff98532007fac299003fc614c8017e30a6435ffd45321affca2990d7fd514c86bfe28a6434ffd05321a7f88299003ff604c8017fb026400ff98132007fac099003fc604c8077e3026435ffd41321affca0990d7fd504c86bfe2826434ffd01321a7f8809901fff650c80f7fb286407ff99432015fcca1901f7e650c8053f3286407ff5943219dfaca1901f7d650c8013eb286407ff1943203df8ca1901fff640c80f7fb206407ff9903200dfcc81901fbe640c8035f3206407ff59032005fac81901fbd640c8015eb206407ff1903203df8c8190cfff540c865ff2a06433ff55032197f8a819022fe630c811ffa986408ff94c32047faa619023fc530c811ffa186432f7d0c32047fc8619023fd430c811fe2186408f710c3203dfcc41901fff520c80fff2906407ff5483203ff8a41901fff420c80fff2106407ff5083203ff8841901fff320c80fef9906407ff8c83203fdc641901ffd320c80fee9906408fb4c83203ffec21901ffe610c8017f3086407ff58432005fac21901ffc610c867ffa886433ff9443219ffaa2190cffc510c865ffa086432ff1043203ffec01901ffe600c8077f3006407ff58032005fac01901ffc600c867ffa806433ff9403219ffaa0190cffc500c865ffa006432ff1003218ffecb208c6ff6590463ff32c8202bf9964118ffacb208c6fd6590463fe32c8202bf1964100dfac920807ff5490403ff2a48201ef9524100ffaa9208c7bd5490403fe2a48200ffd8e41007fcc720822fe6390401feb1c8200bf58e41007f8c7208c7ff5390463ff29c8231ff54e4118ff8a720807ff4390403ff21c8200ef90e4100ffa8720807fc4390403de21c8200ffd8a41007fcc52081efe6290401feb148200bf58a41007f8c5208c7ff5290463ff2948231ff54a4118ff8a520807ff4290403dfa148201ff90a4100ffa8520803bd4290403fe2148200ffcca41007fc6520803fd3290401fe1948201bf9864118ffea3208c7fe5190463fea8c8231ff1464100ffe8320807bf4190403fba0c8201ff1064100fe88320803ff6090401ff3048203bf98241007fac120802fd6090401fe3048231f
  | 10 => 0xc32101ffc6190877ffa8c843bff946421dffaa3210effc5190803ffa0c8401ff1064203ffec12101ffe60908077f3048407ff58242005fac12101ffc6090877ffa84843bff942421dffaa1210effc5090803ffa048401ff102421d7fecaa10eaff6550875ff32a8402bf995421d7facaa10eafd6550875fe32a8402bf1954203dfec8a1007ff5450803ff2a28401ef9514200ffaa8a10ebbd5450803fe2a28400ffd8d42005fec6a1003df63508016fb1a8400ff98d42007fac6a1003fc63508117e31a8400f718d42005b8c6a10ebff5350875ff29a843aff54d421d7f8a6a1007ff4350803dfa1a8401ff90d4200ffa86a1003bd4350803fe21a8401bfd89421d7fea4a101ffe5250875fea928407ff1494200ffe84a1007ef425080fff2128407ef9094203ff884a101fbc4250803f62128401eb10942007fec2a1002ff6150801ff30a8400ff58542007f8c2a1002fc6150875ffa8a843aff945421d7faa2a10ebfc5150803ffa0a8401ff1054200f7882a1003ff60508017fb028400ff98142007fac0a1003fc60508077e302843affd41421d7fca0a10ebfd5050875fe2828401ffd014200f7e80a1007fc4050811ffb2e6408bfd9732047fccb9900afe65cc811feb2e6439bf59732047f8cb99022fc65cc811ffb266408bfd9332047fcc999006fe64cc811feb266400bf59332047f8c999022fc64cc873ffaa66438ff953321cffaa9990e3fc54cc811ffa9e6408ff94f32047bca799023fd53cc873eea9e6408ff14f32047fe8799023fe43cc811fea1e6408ff10f321cffea59901ffe52cc873fea966407ff14b321c7fe859901ffe42cc801fea166407ff10b32047fec399023fe61cc8017f30e6408ff58732005fac399023fc61cc873ffa8e6439ff947321cffaa3990e7fc51cc871ffa0e6438ff10732047fec199023fe60cc8077f3066408ff58332005fac199023fc60cc873ffa866439ff943321cffaa1990e7fc50cc871ffa066438ff1033203ffecb1901eff658c80fff32c6402bf9963203ffacb190defd658c80ffe32c6407bf1963203ffec91901eff648c80fff3246401bf9923203ffac919002fd648c80ffe3246407bf192321bffea9190dbfe548c86ffeaa46436ff152321adfac7190dfff538c811ff29c6437ff54e32047f8a7190dbff438c86defa1c6408ff90e32007fa8719023fc438c86dee21c6407bf98a3203ffea51901ffe528c80ffea946407ff14a3203ffe851901ffe428c80ff72146407ff50a32007da851901ffc428c80fff9946407f7cca32047de651901fff618c80fff30c6400bf9863203ffac319002fd618c80ffe30c6437ffd46321bffca3190dffd518c86ffe28c6436ffd06321b7f8831901fff608c80fff3046403bf9823203ffac119002fd608c80ffe3046437ffd42321bffca1190dffd508c
  | 11 => 0x8a02c0000d800e02400200a00400000000200008a00603800600602800201a00000a00206404600000600a01a00200000401200801601005c00000400e02800400000402000001a01800000601000203e0020020000180300000040020120060100140040a002600400004001200200c01200803a0160200b600201801200000a01000a00600400400600601201600e03800000e00003201600002e0240000b800a0a400c00403600600000200600001800401800602200000600000600603e02001e00a00000000402000c00200000c00605200400001601a00a00200e05201c00400000003007a03800e01000008208ffd9643045fecb21823fe6590c057f32c8608ff596431edfacb21823fc6590c117e32c8601bf5924300ffea921807fe5490c03df2a48601ff552431ef7aa921807fc5490c117f31c8608ffd4e43047fca721823fd5390c11fe29c8608ffd0e430477e8721807df4390c11fe21c8608f710e43047fec521823fe6290c0f7f3148608ff58a43005fac521823fc6290c7bffa94863dff94a431effaa5218f7fc5290c03ffa148601ff10a4300f788521823ff6190c11ff30c8600bf98643047fac321802fd6190c11fe30c863dffd46431effca3218f7fd5190c7bfe28c8601ffd064300ff88321807bc4190c11ffb048608ff9824301dfcc121823fd6090c017eb048608ff182431effea1218f7fe5090c7bfea84863dff1424300ffe8121807bf4090c03fe204863cffd95431e5fecaa18f3fe6550c057f32a863cff595431e5facaa18f3fc6550c057e32a8608bfd914300ffea8a1807fe5450c03feaa28601ff1514300dfec6a18f3ff5350c11ff29a863cff54d43047f8a6a1807ff4350c03efa1a8608ff90d430477c86a1823fc4350c11de21a8601f710d43007fec4a1802ff6250c01ff3128600ff58943007f8c4a181efc6250c79ffa92863cff949431e7faa4a18f3fc5250c03ffa128601efd094300ff884a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c017e30a863cffd45431e7fca2a18f3fd5150c79fe28a8601ffd054300ff882a1803ff6050c017fb028600ff98143007fac0a1803fc6050c077e302863cffd41431e7fca0a18f3fd5050c79fe2828601ffd014300ff880a181fff659080f7fb2c8407ff99642015fccb2101ffd65908777eb2c8407ff1964203df8cb21006fd6490803ffaa48401ff9524200ffaa921007fc549080fffb1c8407ff98e42045fcc72101ffd63908017eb1c8407ff18e421dffea7210effe5390877fea9c843bff14e4200ffe8721007fe4390801df21c8401ff50e4200ff88721007bc439080f7f3148407ffd4a4203ffca52101ffd529080ffe2948407ffd0a4203f7e8521007ef429080ffe2148407fb10a4203ffec32101ffe61908017f30c8407ff58642005fa
  | 12 => 0x1401400000600c00a00000e00c01001201200001e00002a00000a00000c00200200c01801601613c00c00202402803200400e00400c00c01e00205803000000600200e04401000001800200001600400601400800604c00e00c01800600200401a01200000000002400400202a0040000120060160080020100280060fe00406800202600c01e06a00e00001400e00400e01002800200c00000000601401800600000004400000601a00c03000000c06800800000600202e00a03000c00002400a00a00203c00e00000001a02403e00601c00002802803c00001601c0020c400200800204000005601600a00200c00400800600000402801002800601a00000a02403a00000000000004a03000600600001005a01000e00001c00c04402204600000c01000a00600400000002201002000604c00a01403202604402c0f000001800000406209800000a0a800000001e00000c00201000a00200001400200e00200000800003003001000c04a00601601c01608c02600605600800801600000000800000001a00800c00000e00200000800201409a02801a01001c00801200401c01c02600001a05a00603601e00600000c00601800800800a00c00200000404200005a01200000800201200400001e00600400001600801400a00a00c00002000a01000000601201008600a0440000000000140140460000220060700020020060000aa00000a00801000407200402801401800c00a00000005600400602200200200000000400000203401201c00000600000400200602801402400001e00001800c0480220100c80c000800800600c00200001400200200000600800000c0340040b603201402c0bc00801003202405000203e01a05000000200200a00001400400000000001401004800000001a03601600c00600602801000603600200606c00a00000000804600000001400000805806000800c02800e01a0c000803600e00000e01600802a01a02e00400000000202200200000200400001e00400000800a01000400001603a00600804e00203c02a07e07200001001001400a00400a00600400001400000000000000c00401000202a01000a00000a00800001001200001405802402e00000000400000200401e07401600200401c01800801601c00800001206000200a08401001000000600605a00000200000002200800000600000800a01600200000000000002200001804e00002600200400000607800a01601800001200404000200000400205c00400000000200400200000203a00601800a00000800800400000000400000e00001201201e00600000000400406e00e01e01801201201202400603800200400c00e00e01e01000000200402600008600003e01400a01400400203000000000402200600800201c00000005e0a0002000004
  | 13 => 0xab3c41e550940004788000f8c1a408f80006460000ae9e752648913fd1f2cc447b12f2a0909782002f999392ea9a403d90c4b083be16aa29807450326c865031c85037d9ac53b814237d1b288f06f12720378d8e2d82d08480cae7130ff9a4cc8468d4dd9e44f541d517f04551b251a26308bca6400002d27e898e8f641983d46ac9082ea07206162132bd0ff45789f91ca95c92860001b7a4300002223811bf89340001fd86c09947b93a2000090e40338592547180001b90ba41da35f4cd992060635926a070400000000016c000000008922206f897900004b80009ec05d0000abe0000002098f8200000022ec93e0000001bf406a0cf47c1abcd124843770ed502007c4741f3827010a1738000c8e7e432d80089328e346284d42860374939a6c23c41650001e4d9250b47918f8bc89f50031ab82800134039144f146ed25212345ba5d512a0c5c7e688443520d81ee48012994100a29441a98b0920c077317832422213e2df1510bce7be4e1877937c44f0bf16752e250102c148c4c88322b41248fdc95430b19346a47dc43e871898a1172ffa2f413c80449a27683240564560e94ca6745046169c6dc55c2960c206a08943a19f511342a124122c43588ca2b785940006cc3751fcc000000168054c3b00680f70d54e7851b0d1a36c0008cf50b80e453e55900000013347e100027a418619e0001ab49b672c15f1a580000924e516485969d03440b783043d92dc0228ed615933a1a94fac1511619e4c9f04dd10e13bc88c0593b49cb50ca9400bd96ed25a82100022cccfe0000b80e880860001e7000000000000010100000002340d2092c55600000011f60000840000c3c00000000000000820f615c01e852d0521b7081e98800011f40006e90cda8a429288f31c12305200ec000174470882c36d1fecc6c67e4259b2c992485000039d0322030000dc4f867e520887510108a332012b00eca1646307a060a10305e86d0ac81523c4822d41296e1f494a027a02840f164c0a04c13b11508fb62511291bcc0002af2180e500000000690da80009422c8a4dcc3675f17880012a43623f521b0000a1e3168af40009b917d17ec0000000000f008022444432458da64254a414e113c8e627b9ca431a99c08e8c9c14c3dc01096141401673dda71931224249d9c9c3384e531311851f85952010e340005a61d09cb800057317919c8bc635828b00000009c000000012b6a1027d80000004cb0001450c6881700009d01b48414bb20441f672f0608dccc8a06700027c400000000017087e40002b600000000000000bbc85c81f00025a8384a1144b000000071500000000005cb2a9927800009a2a69e700000001f3031d34e3000489d1c9fc000000000001600c00205801a00000002600e0220060000040040340040100040000140160220040400060
  | 14 => 0x594c1aa213738d7403a4553ea80000f44942cf09304963f026100000003221831fc800014100000009a41c31b5a48d164a0614f000026077e3aa945d19c0001f212f48be1e300009c00008c40d3a254a3c8e520ba78936850215181353420003f180006300002ce18c91143a61849658d2000000a1bc069c76800017e11f25000000000a6827100000000006c249a837c74896005610843a00b90ff188cd64000000149938492017b0994c3210500000201e47ad1db87eceba0004868000f3601e39a02d12f08971e1073461e2ab0c38c901e05483f48f785580000961998e6a1f836ca1e89563d1436a5a07e23454ef02342ee5cd0d516cce6c9e517a1634f741f35070fd42a81a91541cdce7aa082af00009e600021d80000e00003d912e400029700000000000320000e6d0b850901f8cf40000000000000b308b7115084000029d08c800080e0ae411000068c7101dc2530bbe28a000000000020e1a10f4cdfe68a0001a9800051148f043cdde07815d154426c4834db00012f65a30001c984824b62ee04fcc169214b2a4680e263c43da4b101c84c4d82224e4a0004ca11108508530bd25d086a0e01dda2d0dcc2a24ee871d3dc1ab358115129c12201219bd05202c1c28bec7740413aba6b4f1c7d72e90cdc8908341f296f035e32a25b825ccac2773082114f94a1a507813008a2f91020f3c36e8a03cc857875434a2bc062c5082f32689518bda3dd11611791ba00021516dc14628e4fd9bd00000001bd1b113f0995340a3605246584ab01b8c6298348c0d110841f0000264049a1273a885681b00930000aa804c31107980012060b21078cb10806e50928c4d23e6791469d28a6a30133685d48247604dc093897691214b14705d40ce3e7800017892804f84248260f633d9d900202792e9a55c6283af471246cb7a0fe2e28b5044629c06880002cc0003be9434c029194ff20810ee3330f09b54fd86be21e218884c9851da08b449000f03786a0d6e6d148e0630066422123981c4c274c3258294e2478b3d60cf8b0080635110d0e807e225d0e20c604fd01100ad15c4e019405f4ace5571e516806828374f4098119a3920d6a73c66c28b262090047e56146d15149268eb20f8d806b45362da0db46a88a23ac11e4e0828339d03652aa27524c17c0d722d11d4251495c21528f80d8c4858c09d889138e71f3398758e18a0730925f407054c3a413c91dc2352c516694300f149f20f846212a10d8b24f7839a053a30ce3625850ea1c8f5e81420299a09d475012b91dc26460c00014640960524829a7800022e36407d40007fd00000012bc0000c88000d4667a00028280000e24b600000006c53d3000000088700024752821ae000085c0000b70002350000406000000097006d0000d0c8dc00035e9ad4000964383000000086700002580005
  | 15 => 0x7c40b1998c58e57b2532290da04914e98fb09aa09049484e524a64614097e8d54065438911c7201571a490a41562f82a907acfb047622e15b4d9a49d3e9141804a03b02e01112cc3ab195a5c131e0543fb8618aa063d34a0d8c7622c50360184e9c56931a9378f2c7813faa34505c23632910e93882114c3a58ce426783f025e8c9863b13c00c51845ad2c125ad3a290014895ac6ca000271079ce0058b19e199cce058f171a7dd1c29b70000aec7140001be91089e254141f887c96230c42a267ce8255b14493d400065c1cc8314aa80002a71aa4d7600000000007dc0003a580000000841ce9d8c00000000000012a065f371052c00000036780f43086974231e8015a00044e07e80000001ea15f49ae00000007380c02c62d600009d262c3559a700008003ab01d4b5200000000013f80002dc800000080f0001ae0da837f000000000013c22c8000f4a2da0d28000000000000162461a4893910000c045ba2aa91cc8d400000012390be65e3c39f740005634549b0c0000b61101c2475a2e4487115c6d027d2d107882f28c83e880000000004059a7c0008f40000000dc218a12b0a6497c9eb38b87806ce3b912a8000000a220000e44b029822bca208e2c9920000cb443c000382800117c000269853800007241826cc9c22161bb88ad10018121594905a437b1c4887446808706b83849f29df38f112404e0ee02d9964b621bf035814d3e646b37ba390f342e80000000cc269116d985c00000006680001007850000b3000000d000051c00027a0959e3d0f00bb1880ed86e871149d00000001d141aa75c5d85f10000b944b20000002734000644438129400000012f0000252899000224c6bc00051400004340dc28291e8bde000000000121e83a22087a400017c1c0945481881a4151d342f039700002d47c42ce28980000005e804e87640000003e0287000004e0000000fd07f402f9d7037c164000000011297246800012c43cc45798440000004d196a0fa0000000000000052e10c854000087932a000023400000009f00006ba47b8add04e5100000fe8c3e000485803934a7820000794f6e8b643180010384582f00c487922ff495982853086815b00000000003281a383b600b4820b9800025f00000000009222a000000000d60c8000144c53d502a7bc8ac2ca34606d4dd00000001a653782d9000002400025c00000003e494f000000000048a315a15c0800001569d680005f7000000077e4ec00000012b299d10c211c0009c500026a087294b314a03096a8313900cec84654a3af1eb89462a90181c1d32c1f950090b135251d00fa10cc0a7d924097f5436a031390c94a6627b0fea0a0eb69ac44e80000000002348c6c89c3cb0b7a180b865ea2ca1e1010c000144026d11a6820fb85340aa07f2fa23708400dd07e0d3c28c0000b11
  | 16 => 0x877d25e2a643fa524c4e4152b10000aba26d3ed0c58ece8742501dd03628aa205a8a80247bf36f926c0004cf28502505ae000000000019040900000000000001821f34f8e15b00000005628a7085925c0000002daa2e40004a11eb2730ee00004d784e816298a131a850ab054321c03e8db044c39d890cbac2f0103062426e5313f78698b821740239ca0a7e6f6166949d3e01230178d307ce2eb465a535202936000188483c33a31700000007f0094186833062a3f324fc03857e07c23d4b7e4ed2f71ddd44600029d9db918e95319093605280000d909a00000003bd8a1cc1e72b171000000096d14d0cbc0003801e2289d3823df000288047000000014a44de39e0000ef0d484da000000103672a1b227a800083939222fc9b80004c600000004ee3b6a4e0d8276630e03bc0005f23aa11d400000023d80008c65d800000000002800e596c800000032799d490c82f00011c8ff06fc00019900009b550900003009a23c602381a800028608a01c635b3e48cc82aa49007c9dfcef28ed08a190cdae0171050fb4a780694931e0d2286de23fa4f0b8068b295a6b90aa9d53b99928a5e5252542198c0c436310252856066045818a144a4401c9906ccba2025021580c927b80dc186038a5cf460114cde44713efa240eec01920a00b4ef4000000017862a1cf1fb0ce0fa631d3db0d9821a0110e9800061c9732ec8d000e63cd4c2000072c19900000300001f640a82a8a240002e806e922200011499544ba26b06d8a14000a0234a8bf046e00000004d0ed872305809880008ab278019800000004c13391c0967387a23800045d16785287de2b42f318fc41a708238057c20e16d2d2a1741064b23311618ea46ec27d0000bc449c2bb000c00054b2251398f5203c0311afcbbc85836ea12071c11007f9f2023067c3bc17f913e5c64c31dc90b211c1bc20042665a44ea15d03441164c7000000059b10426e82e640a4d8a0752ba88c454235860e8e921213fc7b63a333b81188104cc0d097690de8440b482881aa34b0e6000000025a0000080f443260000dd400000011c99f400055a253a4c400000000006d90e61011c307108c43c711d0cc45260004f180012485c800000000140001399bac0000004c98000d9c91040503007a41dd3ef15993ce9e1481130c7e80eb0cb23493305dd4971fd90c29ce15a92a52fc03e23a1d942dca1f0de220c0ba4881b619a51f41213388bdc7aa7b434027c904684d1048ac887e225000262c1d47f92ba9d1821c1d71009c353221fc2ed91b0b5e68422923bc0004cd25a0f8c00040d000000086425b0000dd88962f51fc98e41fa5c441c1b590a21064609d082d63b031ba601142000000173810a14c0f69ea00522e124780013b011328704bcd6632023f28b066864104e182019866b04425bcb104e8506a3c029e
  | 17 => 0xb082bd3c823300002a01668ad48ba3a80001880001c742b0172232a68122a27f49990f41ca41835a10cc5be3eb00000005822a50bb1420f6a83d4e900a85a673344c1f9ce647ed28c0cd53328252cb82e00001b90000700ca21d20000c6402a2ae39c06f40009ab30221b92f809515ca84cae2739489a82cd0c6032e61e844a04430ae0ffc88a95a2fb0a0917434730e8cfccca24f40987282082663989e00d1e856021160d27204a29517f00fa4e31ed0bb900a4ad2641cc11bc04f13490bd00607e1970d845fa2c44f30ea46e09772338e2c31e87c3d991b4e9e03447e851478636950a846c7b02e04069a601a690a1f00a3c00273e0f504003b421205093ac78c1442f091982d02462e39c0400a08f38c276517888b14606542188c91228f410921f14fe92cc6ae81635e02640000002302724f8440e00000002ac2bf3538580f8aa1941e1a1c8208ff3b0a2949607eb30720b475850700013010125d73cf0000000000000213c0001e64f0239c0008020001d6400056a00016b800066e1d900000c80d013f235c3b80004a898cc00089b38c9640da49ff216a518ffe6f925f9c290bc41a1d993d8d402a446a95dd27a40042d10dcadc4d02f482a473e97f5061be06f279800c116c0006c60dda65d1fc0ca0170f5c83a46400d8814638221000000000066a45aa34cd063c11fe128884e6f532d1a480008b81601f306729691810c7c6140001f4008c2d89b23dea6344d417f4f6967c0007903d38ca4f0c87500000000007b01d3a4c0cec28616e064d0c823e0cf89b80007ab1190ae0b5400013b1fc53e823d00000011982b300014dc00024a0001c7000000051221f80000000000124000000291000000000000000004920004a388c0c4a59930a8000e2857f20c93f07f075300000000000001538000f24000000213905600035607900006e43a49140a9e00025500000008121c39524000102290137c00043e1d00eb93962261f525853ec20b2e498e8b941712c728ac02c0000000000c260574291b0017e0e800011f00003510000c68ef88762be17d50d27fc1e28680e348df35b17acf4678d47622040000002f6067400000026b1a840005b61ff1dd4f3e885150001c4ce4f4176943ca720631ce05a935437e1de8000f482c849507d06608f305f000091690934d04c40e87972c398240006144de849933c0810001b8c89a19a10385213ac4e71360b58dc095f290849053673f1c1800009076a435a60444e38f41d8a5469a9c811e241cee29a64ed88308b4214387000103060044900007ee66c29f03180005f90e488ec7c276f20e032c36668525783a4e065303ca0614d3a35c0000000db66a806200000083981e4000000000000014e870406a4ae060c25a0e600d26fc8de5474ac00003de000072000063c000061216cffc0000cb
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc744c8101a6be644c810006bd644c810046de634c810006dd634c81003eee624c810006ed624c810005f7714c810005f4714c81003cff760c81001cfe760c810004fd760c81001cfc760c81002d7e750c8100057d750c81019e7e650c8100067d650c810025be740c810005bd740c810196be640c810006bd640c810046de630c810006dd630c81003eee620c810006ed620c81006cff769041001cfe769041000cfd769041001cfc769041018e7e65904100067d659041000ebe6490410006bd6490410006de6390410006dd6390410006ee6290410006ed629041001dfa7090410005f9709041006cff76504101867e65504100067d655041000ebe6450410006bd6450410006de6350410006dd6350410006ee6250410006ed6250410004fd76cc41017e7e65cc4100067d65cc410176be64cc410006bd64cc410046de63cc410006dd63cc410006ee62cc410006ed62cc410004ff768c410044fd768c4101567e658c4100067d658c41016ebe648c410006bd648c410046de638c410006dd638c410006ee628c410006ed628c41001dfa708c410005f9708c410004ff764c4101667e654c4100067d654c410005bf744c410025bc744c41015ebe644c410006bd644c410046de634c410006dd634c410005ef724c410005ec724c410006ee624c410006ed624c410044ff760c41001cfe760c410004fd760c41001cfc760c41002d7e750c4100057d750c41014e7e650c4100067d650c410146be640c410006bd640c410046de630c410006dd630c410006ee620c410006ed620c41001dfa700c410005f9700c410004fd76c841013e7e65c84100067d65c8410025be74c8410005bd74c8410136be64c8410006bd64c8410006de63c8410006dd63c841003eee62c8410006ed62c8410004ff768841003cfd768841002d7e75884100057d75884101167e65884100067d658841012ebe6488410006bd6488410006de6388410006dd638841003eee6288410006ed628841001dfa7088410005f97088410004ff76484101267e65484100067d654841011ebe6448410006bd6448410006de6348410006dd634841003eee6248410006ed624841003cff760841001cfe7608410004fd760841001cfc760841010e7e65084100067d6508410106be6408410006bd6408410006de6308410006dd630841003eee6208410006ed620841001dfa7008410005f9700841001dfb7644010006fb7644010004fb76440100077b75440101ff78754401001f7a654401001f796544010007bb7444010007b8744401001fba644401001fb96444010007db7344010007d8734401001fda634401001fd96344010007eb7244010007e8724401001fea624401001fe9624401001dfb714401001ff371440101f6fa614401001ff26144010007f23144010007f13144010
  | 1 => 0x8810006ed5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec439881003eee719881003eec7198810006ef5198810006ee5198810006ed5198810006ec5198810006ef4198810006ec419881001eef709881001eee709881001eed709881001eec709881001eef509881001eee509881001eed509881001eec509881001eef409881001eee409881001eed409881001eec409881001eef309881001eee309881001eed309881001eec309881001eef109881001eee109881001eed109881001eec1098810004ff7558810014fe7558810004fd7558810014fc7558810004ff745881000cfe745881000cfc7458810004ff7358810044fc735881001eef7258810006ef5258810006ee5258810006ed5258810006ec5258810006ef4258810006ec425881003cff715881003cfd715881001cff705881001cfe705881001cfd705881001cfc705881001eee205881001eec2058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810006ee7158810006ec7158810006ef5158810006ee5158810006ed5158810006ec5158810006ef4158810006ec415881001eef705881001eee705881001eed705881001eec705881001eef505881001eee505881001eed505881001eec505881001eef405881001eee405881001eed405881001eec405881001eef305881001eee305881001eed305881001eec305881001eef105881001eee105881001eed105881001eec105881003cff769081001cfe7690810004fd769081001cfc76908101de7e65908100067d659081000ebe6490810006bd6490810006de6390810006dd639081003eee6290810006ed6290810004ff765081001cfe7650810004fd765081001cfc76508101d67e65508100067d655081000ebe6450810006bd6450810005df7350810005dc7350810006de6350810006dd635081003eee6250810006ed6250810027ac4250810005f77150810005f47150810044ff76cc81001cfe76cc810004fd76cc81001cfc76cc8101ce7e65cc8100067d65cc8101c6be64cc810006bd64cc810046de63cc810006dd63cc81003eee62cc810006ed62cc81003cff768c81001cfe768c810004fd768c81001cfc768c8101be7e658c8100067d658c8101b6be648c810006bd648c810046de638c810006dd638c81003eee628c810006ed628c810004ff764c81001cfe764c810004fd764c81001cfc764c8101ae7e654c8100067d654c810005bf744c810025b
  | 2 => 0x1ebc305901001ebf205901001ebe205901001ebd205901001ebc205901001ebf105901001ebe105901001ebd105901001ebc1059010046df7598c10046de7598c10046dd7598c10046dc7598c10046df7498c10046de7498c10046dd7498c10046dc7498c10006df5498c10006de5498c10006dd5498c10006dc5498c10046df7298c10046de7298c10046dd7298c10046dc7298c10006df5298c10006de5298c10006dd5298c10006dc5298c10006df4298c10006dc4298c10046de7198c10046dc7198c10006df5198c10006de5198c10006dd5198c10006dc5198c10006df4198c10006dc4198c1001edf7098c1001ede7098c1001edd7098c1001edc7098c1001edf5098c1001ede5098c1001edd5098c1001edc5098c1001edf4098c1001ede4098c1001edd4098c1001edc4098c1001edf2098c1001ede2098c1001edd2098c1001edc2098c1001edf1098c1001ede1098c1001edd1098c1001edc1098c10004ff7558c10014fe7558c10004fd7558c10014fc7558c10004ff7458c1000cfe7458c1000cfc7458c1001edf7358c10006df5358c10006de5358c10006dd5358c10006dc5358c10006df4358c10006dc4358c10004ff7258c1003cfc7258c10044ff7158c10044fd7158c1001cff7058c1001cfe7058c1001cfd7058c1001cfc7058c1001ede3058c1001edc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006dc4258c10006de7158c10006dc7158c10006df5158c10006de5158c10006dd5158c10006dc5158c10006df4158c10006dc4158c1001edf7058c1001ede7058c1001edd7058c1001edc7058c1001edf5058c1001ede5058c1001edd5058c1001edc5058c1001edf4058c1001ede4058c1001edd4058c1001edc4058c1001edf2058c1001ede2058c1001edd2058c1001edc2058c1001edf1058c1001ede1058c1001edd1058c1001edc1058c10044ff7690c1001cfe7690c10004fd7690c1001cfc7690c101ee7e6590c100067d6590c1000ebe6490c10006bd6490c10046de6390c10006dd6390c10004ff7650c1001cfe7650c10004fd7650c1001cfc7650c101e67e6550c100067d6550c1000ebe6450c10006bd6450c10046de6350c10006dd6350c1003eef759881003eee759881003eed759881003eec759881003eef749881003eee749881003eed749881003eec7498810006ef5498810006ee5498810006ed5498810006ec549881003eef739881003eee739881003eed739881003eec7398810006ef5398810006ee539
  | 3 => 0xc654c110006bf644c1100c6bc644c110006df634c110046dc634c110006ef624c110006ec624c110005f7714c110005f4714c11001ff0104c110004fe76c81100067f65c81100ae7c65c8110006bf64c81100a6bc64c8110006df63c8110006dc63c8110006ef62c811003eec62c8110005f671c8110005f571c811003cff7648110004fd764811003cfc76481100057f75481100557c75481100067f654811008e7c6548110006bf6448110086bc6448110006df6348110006dc6348110006ef624811003eec6248110005f77148110005f471481100067f65c41100367c65c4110006bf64c411006ebc64c4110006df63c4110006dc63c4110006ef62c4110006ec62c411001df671c411001ef761c411001dfa76c411001efa76c411001cfa76c41100077b65c41102077865c4110007bb64c4110007b864c4110007db63c4110007d863c4110007eb62c4110007e862c411001dfa71c411001efb61c411001ff361c4110207f251c4110207f151c41100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067c425941002e7f71594100067e715941002e7d715941002e7c71594100067f41594100067c415941001e7f705941001e7e705941001e7d705941001e7c705941001e7f405941001e7e405941001e7d405941001e7c405941001e7f305941001e7e305941001e7d305941001e7c305941001e7f205941001e7e205941001e7d205941001e7c205941001e7f105941001e77105941001e7e105941001e7d105941001e75105941001e7c1059410004ff7559010014fe7559010004fd7559010014fc755901001ebf7459010006bf5459010026be5459010006bd5459010026bc5459010004ff7359010044fc7359010026bf4359010026bc4359010004ff725901003cfc7259010026bf4259010026bc425901000cff715901000cfd7159010024fc7159010026bc415901001cff705901001cfe705901001cfd705901001cfc705901001ebe405901001ebc4059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010026bf7159010006be7159010006bc7159010006bf5159010006be5159010006bd5159010006bc515901001ebf705901001ebe705901001ebd705901001ebc705901001ebf505901001ebe505901001ebd505901001ebc505901001ebf305901001ebe305901001ebd3059010
  | 4 => 0xc910005bf744c91004dbc744c910006bf644c9101a6bc644c910006df634c910046dc634c910006ef624c91003eec624c91003cff760c910004fe760c910004fd760c91003cfc760c9100557e750c9100057d750c9100067f650c91019e7c650c91004dbe740c910005bd740c910006bf640c910196bc640c910006df630c910046dc630c910006ef620c91003eec620c910005f6710c910005f5710c91001dfa700c910005f9700c91005cfe76905100067f659051018e7c6590510006bf649051000ebc6490510006df6390510006dc6390510006ef6290510006ec629051001cfc76505100067f65505101867c6550510006bf645051000ebc6450510006df6350510006dc6350510006ef6250510006ec6250510005fb705051001df8705051001cfe76cc51001cfc76cc5100067f65cc51017e7c65cc510006bf64cc510176bc64cc510006df63cc510046dc63cc510006ef62cc510006ec62cc51001dfa70cc510005f970cc510004fe768c5100067f658c5101567c658c510006bf648c51016ebc648c510006df638c510046dc638c510006ef628c510006ec628c51001cfc764c5100067f654c5101667c654c510005bf744c51004dbc744c510006bf644c51015ebc644c510006df634c510046dc634c510005ef724c510005ec724c510006ef624c510006ec624c510005fb704c51001df8704c510004fe760c5100557e750c5100057d750c5100067f650c51014e7c650c510006bf640c510146bc640c510006df630c510046dc630c510006ef620c510006ec620c51001cfe76c851001cfc76c85100067f65c851013e7c65c851004dbe74c8510005bd74c8510006bf64c8510136bc64c8510006df63c8510006dc63c8510006ef62c851003eec62c851001dfa70c8510005f970c8510004fe76885100557e75885100057d75885100067f65885101167c6588510006bf648851012ebc6488510006df6388510006dc6388510006ef628851003eec628851001cfc76485100067f65485101267c6548510006bf644851011ebc6448510006df6348510006dc6348510006ef624851003eec6248510005fb704851001df87048510004fe76085100067f650851010e7c6508510006bf6408510106bc6408510006df6308510006dc6308510006ef620851003eec620851000cff765011004cfd765011000cfc76501100067f65501100f67c6550110006bf645011000ebc6450110006df6350110006dc6350110006ef6250110006ec6250110005f77150110005f47150110004fe76cc1100557e75cc1100057d75cc1100067f65cc1100ee7c65cc110006bf64cc1100e6bc64cc110006df63cc110046dc63cc110006ef62cc110006ec62cc110005f671cc110005f571cc110044ff764c110004fd764c110044fc764c1100067f654c1100ce7
  | 5 => 0x4ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf745891000cfe745891000cfc7458910006bc745891000cbc7458910004ff7358910006df7358910004df7358910044fc7358910006dc7358910044dc7358910006ef7258910004ff7158910006f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc631891003eee6218910006ed6218910005ee7618910006ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910007e65118910007e5511891020fe6101891020fe4101891003eef751891003eee751891003eed751891003eec751891003eef741891003eee741891003eed741891003eec7418910006ef5418910006ee5418910006ed5418910006ec541891003eef731891003eee731891003eed731891003eec7318910006ef5318910006ee5318910006ed5318910006ec5318910006ef4318910006ee4318910006ed4318910006ec431891003eef711891003eed7118910006ef5118910006ee5118910006ed5118910006ec5118910006ef4118910006ec411891003eef701891003eee701891003eed701891003eec7018910006ef501891020eee5018910006ed501891020eec5018910006ef401891020eee401891020eec401891020eee301891020eec301891020eee1018910006ed101891020eec101891003cff7690910004fe7690910004fd769091003cfc76909100067f65909101de7c6590910006bf649091000ebc6490910006df6390910006dc6390910006ef629091003eec6290910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101d67c6550910006bf645091000ebc6450910005df7350910005dc7350910006df6350910006dc6350910006ef625091003eec625091004fac4250910044ff76cc910004fe76cc910004fd76cc910044fc76cc9100067f65cc9101ce7c65cc910006bf64cc9101c6bc64cc910006df63cc910046dc63cc910006ef62cc91003eec62cc91003cff768c910004fe768c910004fd768c91003cfc768c9100067f658c9101be7c658c910006bf648c9101b6bc648c910006df638c910046dc638c910006ef628c91003eec628c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101ae7c654
  | 6 => 0xf7118d10046dd7118d10006df5118d10006de5118d10006dd5118d10006dc5118d10006df4118d10006dc4118d10046df7018d10046de7018d10046dd7018d10046dc7018d10006df5018d1021ede5018d10006dd5018d1021edc5018d10006df4018d1021ede4018d1021edc4018d1021ede2018d1021edc2018d1021ede1018d10006dd1018d1021edc1018d10044ff7690d10004fe7690d10004fd7690d10044fc7690d100067f6590d101ee7c6590d10006bf6490d1000ebc6490d10006df6390d10046dc6390d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d101e67c6550d10006bf6450d1000ebc6450d10006df6350d10046dc6350d1003cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910004ff75d8910014fe75d8910004fd75d8910014fc75d891000cfe74d8910004fd74d891000cfc74d8910044fe73d8910004fd73d8910006ef52d8910006ee52d8910006ed52d8910006ec52d8910006ef42d8910006ec42d891003cfe71d891003cfc71d891001cfe70d891001cfc70d891003cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e651d8910007e551d8910217e610d8910217e410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910216ef71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef41d8910006ec41d8910006ef70d8910216ee70d8910006ed70d8910216ec70d8910006ef50d8910216ee50d8910006ed50d8910216ec50d8910006ef40d8910216ee40d8910216ec40d8910216ee30d8910216ec30d8910216ee10d8910216ec10d89100557e75989100057d75989100067f65989100067c659891004dbe7498910005bd7498910006bf6498910006bc6498910005de7398910005dd7398910006df6398910006dc6398910006ef62989100057f75589100557c75589100067f65589100067c6558910005bf745891004dbc7458910006bf6458910006bc6458910005df7358910005dc7358910006df6358910006dc6358910
  | 7 => 0x8d10004fd72d8d10044fe71d8d10044fc71d8d1001cfe70d8d1001cfc70d8d10044de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10007d651d8d10007d551d8d10227d610d8d10227d410d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006dc42d8d10226df71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df70d8d10226de70d8d10006dd70d8d10226dc70d8d10006df50d8d10226de50d8d10006dd50d8d10226dc50d8d10006df40d8d10226de40d8d10226dc40d8d10226de20d8d10226dc20d8d10226de10d8d10226dc10d8d100557e7598d100057d7598d100067f6598d100067c6598d1004dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10005ee7298d10005ed7298d100057f7558d100557c7558d100067f6558d100067c6558d10005bf7458d1004dbc7458d10006bf6458d10006bc6458d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d1000cfe7458d1000cfc7458d10006bc7458d1000cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d1003cec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10046de6318d10006dd6318d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10007d65118d10007d55118d1021fd61018d1021fd41018d10046df7518d10046de7518d10046dd7518d10046dc7518d10046df7418d10046de7418d10046dd7418d10046dc7418d10006df5418d10006de5418d10006dd5418d10006dc5418d10046df7218d10046de7218d10046dd7218d10046dc7218d10006df5218d10006de5218d10006dd5218d10006dc5218d10006df4218d10006dc4218d10046d
  | 8 => 0x567d71d95100567c71d95100067f41d95100067c41d95100067f70d951023e7e70d95100567d70d951023e7c70d95100067f40d951023e7e40d951023e7c40d951023e7e30d951023e7c30d951023e7e20d951023e7c20d951023e7e10d95100567d10d951023e7c10d951000cfe76d91100067f65d91100067c65d911004ebe64d9110004ff75d9110014fe75d9110004fd75d9110014fc75d9110006bf54d911004ebe54d9110006bd54d911004ebc54d9110044fe73d9110004fd73d911004ebf43d911004ebc43d911003cfe72d9110004fd72d911004ebf42d911004ebc42d911000cfe71d911001cfd71d911000cfc71d911004ebf41d911001cfe70d911004cfd70d911001cfc70d911004ebf40d911004dbe76d911000cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110007b651d9110007b551d9110237b610d9110237b410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110236bf71d911004ebe71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf70d9110236be70d9110006bd70d9110236bc70d9110006bf50d9110236be50d9110006bd50d9110236bc50d9110236be30d9110236bc30d9110236be20d9110236bc20d9110236be10d9110236bc10d91100057f75591100557c75591100067f65591100067c655911004ebc6459110005df7359110005dc7359110005ef7259110005ec7259110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c755911004cff7459110006bf7459110004ff7359110006df7359110004df7359110044fc7359110006dc7359110044dc7359110004ff7259110006ef7259110004ef725911003cfc7259110006ec725911003cec725911005cff7159110006f7715911006cff7059110006fb7059110005be761911004ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c651911022ebf6119110007b65119110007b5511911022fb6101911022fb41019110044fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d1000cfe74d8d10004fd74d8d1000cfc74d8d10006df53d8d10006de53d8d10006dd53d8d10006dc53d8d10006df43d8d10006dc43d8d1003cfe72d
  | 9 => 0xc705921001ebe405921001ebc4059210004ff7558e10014fe7558e10004fd7558e10014fc7558e10004ff7458e1000cfe7458e1000cfc7458e1001edf7358e10006de5358e10006dd5358e10004ff7258e1003cfc7258e1001cfc7058e1001ede3058e1001edc3058e10044ff7690e1001cfe7690e10004fd7690e1001cfc7690e1000ebe6490e10006bd6490e10004ff7650e1001cfe7650e10004fd7650e1001cfc7650e10004ff7558a100067f7558a100047f7558a10014fe7558a10004fd7558a10014fc7558a100067c7558a100147c7558a10004ff7458a1000cfe7458a1000cfc7458a10004ff7358a10044fc7358a1001eef7258a10006ee5258a10006ed5258a1001cfc7058a1001eee2058a1001eec2058a1003cff7690a1001cfe7690a10004fd7690a1001cfc7690a1003eee6290a10006ed6290a10004ff7650a1001cfe7650a10004fd7650a1001cfc7650a1000ebe6450a10006bd6450a10005df7350a10005dc7350a1003eee6250a10006ed6250a1005fac4250a10005f77150a10005f47150a10044ff76cca1001cfe76cca10004fd76cca1001cfc76cca1003eee62cca10006ed62cca1003cff768ca1001cfe768ca10004fd768ca1001cfc768ca10004ff764ca1001cfe764ca10004fd764ca1001cfc764ca10005bf744ca1005dbc744ca10005f7714ca10005f4714ca1003cff760ca1001cfe760ca10004fd760ca1001cfc760ca100657e750ca100057d750ca1005dbe740ca10005bd740ca1003eee620ca10006ed620ca1001dfa700ca10005f9700ca1004cfd7690610236bf649061000ebc649061000cff765061001cfc765061000ebe6450610006bd6450610005fb705061001df87050610046de63cc610006dd63cc61001dfa70cc610005f970cc610226df638c610046dc638c610044ff764c610005bf744c61005dbc744c610046de634c610006dd634c610005ef724c610005ec724c610005fb704c61001df8704c6100657e750c6100057d750c61021edf630c610046dc630c61005dbe74c8610005bd74c861003eee62c8610006ed62c861001dfa70c8610005f970c86100657e75886100057d7588610216ef628861003eec628861003cff764861003eee6248610006ed6248610005fb704861001df8704861020eef620861003eec620861001df976c4210006f976c421001ff271c42100557e76d95100567e76d95100147e76d95100067e64d95100067c64d951023f7771d95100577471d951023f7610d951023f7410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067c42d951023e7f71d95100567e71d9510
  | 10 => 0x8b100057d75d8b10004ff75d8b10014fe75d8b100067e75d8b100147e75d8b10004fd75d8b100067d75d8b100047d75d8b10014fc75d8b1000cfe74d8b10004fd74d8b1000cfc74d8b10044fe73d8b10004fd73d8b10006ee52d8b10006ed52d8b10006f671d8b10006f970d8b10216ee20d8b10216ec20d8b10004fd7698b1006dbe7498b10005bd7498b10006ef6298b1003cff7658b10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b1000cfe7458b1000cfc7458b10004ff7358b10044fc7358b10006ef7258b1003eee6218b10006ed6218b1003cff7690b10004fe7690b10004fd7690b1003cfc7690b10006ef6290b1003eec6290b10004ff7650b10004fe7650b10004fd7650b10004fc7650b10006bf6450b1000ebc6450b10005df7350b10005dc7350b10006ef6250b1003eec6250b1006fac4250b10044ff76ccb10004fe76ccb10004fd76ccb10044fc76ccb10006ef62ccb1003eec62ccb1003cff768cb10004fe768cb10004fd768cb1003cfc768cb10004ff764cb10004fe764cb10004fd764cb10004fc764cb10005bf744cb1006dbc744cb1003cff760cb10004fe760cb10004fd760cb1003cfc760cb100357e750cb100057d750cb1006dbe740cb10005bd740cb10006ef620cb1003eec620cb10005f6710cb10005f5710cb1001cfd769071000ebe6490710006bd649071001dfa7090710005f97090710024ff7650710006bf645071000ebc6450710006df63cc710046dc63cc71001cfd768c710046de638c710006dd638c71001dfa708c710005f9708c710005bf744c71006dbc744c710006df634c710046dc634c710005ef724c710005ec724c71001cfd760c7100357e750c7100057d750c710046de630c710006dd630c71001dfa700c710005f9700c71006dbe74c8710005bd74c8710006ef62c871003eec62c871001cfd76887100357e75887100057d758871003eee6288710006ed628871001dfa7088710005f97088710006ef624871003eec624871001cfd760871003eee6208710006ed620871001dfa7008710005f9700871000cff765031000cfc765031000ebe6450310006bd6450310005f77150310005f471503100357e75cc3100057d75cc310046de63cc310006dd63cc310005f671cc310005f571cc310044ff764c310046de634c310006dd634c310005f7714c310005f4714c31003eee62c8310006ed62c8310005f671c8310005f571c831003cff76483100057f75483100357c754831003eee6248310006ed6248310005f77148310005f47148310004ff7559210014fe7559210004fd7559210014fc755921001ebf745921005ebe5459210006bd5459210004ff7359210044fc735921005ebc4359210004ff725921003cfc725921005ebf425921005ebf415921001cf
  | 11 => 0x4ff745842000cfe745842000cfc7458420004ff7358420044fc735842001ef77158420006f65158420006f5515842003ef7215842003eec215842003ef4215842001eef205842001eed205842001ef6105842001ef41058420004ff769042001cfe7690420004fd769042000ebe6490420006bd6490420004ff7650420004fd765042001cfc765042000ebe6450420006bd6450420005ef725042003dec7250420044ff76cc42001cfe76cc420004fd76cc420176be64cc420006bd64cc420046de63cc420006dd63cc42003dee72cc420005ed72cc420004ff768c42001cfe768c420004fd768c42016ebe648c420006bd648c420006f6618c420006f5618c420004ff764c420004fd764c42001cfc764c420005bf744c420075bc744c42015ebe644c420006bd644c420046de634c420006dd634c420005ef724c42003dec724c420006f6614c420006f5614c420044ff760c42001cfe760c420004fd760c42007d7e750c4200057d750c420146be640c420006bd640c42003ded7688420006ed7688420004ed768842024f6e75884200076d758842003eef658842024eed658842003eef648842003fae6488420006ed648842003fad6488420006ad6488420246ee638842003eec638842003dee718842003fe67188420006ed6188420215ed7088420216ee608842003fea608842006ebe64d9310004ff75d9310014fe75d9310004fd75d9310014fc75d931006cfd74d931006ebe54d9310006bd54d9310044fe73d9310004fd73d931006ebc43d931003cfe72d9310004fd72d931006ebf42d9310006f671d931006ebf41d9310006f970d9310236be40d9310236bc40d931000cff765931006ebc6459310004ff7559310014fe7559310004fd7559310014fc7559310006bf7459310004ff7359310044fc7359310004ff725931003cfc725931001cfc715931006ebc415931006ebf4059310004ff75d8f10014fe75d8f10004fd75d8f10014fc75d8f1000cfe74d8f10004fd74d8f1000cfc74d8f10006de53d8f10006dd53d8f1003cfe72d8f10004fd72d8f10006f671d8f10006f970d8f10226de30d8f10226dc30d8f10004fd7698f10006df6398f10044ff7658f10005bf7458f1006dbc7458f10005ef7258f10005ec7258f10004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f10006bf7458f10004bf7458f1000cfe7458f1000cfc7458f10006bc7458f1000cbc7458f10006df7358f10004ff7258f10006ef7258f10004ef7258f1003cfc7258f10006ec7258f1003cec7258f100357e7518f100057d7518f10046de6318f10006dd6318f10044ff7690f10004fe7690f10004fd7690f10044fc7690f10006bf6490f1000ebc6490f10004ff7650f10004fe7650f10004fd7650f10004fc7650f100357e75d
  | 12 => 0xc6550120006bf645012000ebc6450120005ef725012003dec7250120007ad425012003cfe76cc12003cfc76cc12008d7e75cc1200057d75cc1200067f65cc1200ee7c65cc120006df63cc120046dc63cc12003dee72cc120005ed72cc120044ff764c120004fd764c12003cfc764c1200067f654c1200ce7c654c120006df634c120046dc634c120005ef724c12003dec724c12001fd8304c120004ff7559020014fe7559020004fd7559020014fc755902001cff745902001ebf7459020006bf5459020076be5459020006bd5459020076bc5459020004ff7359020044fc7359020076bf4359020076bc435902003cff725902003cfe725902003cfd725902003cfc725902003ebe425902003ebc4259020004ff7159020004fc7159020076bf4159020076bc415902003eec215902001cfe705902001cfc705902001ebe405902001ebc405902001eef205902001eed2059020006bf7559020006be7559020006bd7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf5359020006be5359020006bd5359020006bc535902003ebf725902003ebe725902003ebd725902003ebc725902003ebf525902003ebe525902003ebd525902003ebc525902003ebf325902003ebe325902003ebd325902003ebc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf5159020006be5159020006bd5159020006bc515902003ebf215902003ebe215902003ebd215902003ebc215902003eac215902001ebf705902001ebe705902001ebd705902001ebc705902001ebf505902001ebe505902001ebd505902001ebc505902001ebf305902001ebe305902001ebd305902001ebc305902001ebf205902001eaf205902001ebe205902001ebd205902001ead205902001ebc205902001ebf105902001ebe105902001ebd105902001ebc1059020004ff7558c20014fe7558c20004fd7558c20014fc7558c20004ff7458c2000cfe7458c2000cfc7458c2001cff7358c2001edf7358c20006de5358c20006dd5358c2003cff7258c2003cfe7258c2003cfd7258c2003cfc7258c2003ede3258c2003edc3258c20004ff7158c20004fc7158c2001cfe7058c2001cfc7058c2001ede3058c2001edc3058c20044ff7690c2001cfe7690c20004fd7690c2001cfc7690c2000ebe6490c20006bd6490c20004ff7650c2001cfe7650c20004fd7650c2001cfc7650c2000ebe6450c20006bd6450c20004ff7598420014fe7598420004fd7598420014fc759842000cfe7498420004fd749842000cfc7498420044fe7398420004fd739842001ef67198420006f65198420006f5519842003ef7219842003ef4219842001ef6109842001ef41098420004ff7558420014fe7558420004fd7558420014fc7558420
  | 13 => 0xc920005ed710c92001dee700c92001dec700c92003eef600c92003feb600c9200067f65d85200067c65d8520004ff75d8520014fe75d8520004fd75d8520014fc75d852000cfe74d8520004fd74d852000cfc74d8520044fe73d8520004fd73d8520006f741d8520006f441d852008d7e75985200057d75985200067f65985200067c6598520006f761985200057f755852008d7c75585200067f65585200067c6558520005bf7458520085bc7458520005df7358520005dc73585200067f65185200067c6518520006f56118520004ff7518520014fe7518520004fd7518520014fc751852000cfe7418520004fd741852000cfc7418520044fe7318520004fd7318520006ee5218520006ed5218520006ee4218520006ed4218520006ef3218520006ec3218520006f74118520006f4411852001cfe701852001cfc701852020eee201852020eec2018520004fe7690520004fd7690520004fc76905200067f659052018e7c6590520006bf649052000ebc649052003dee7290520005ed7290520007ad4290520004ff7650520004fe7650520004fc76505200067f65505201867c6550520004fe76cc520004fd76cc520044fc76cc5200067f65cc52017e7c65cc520006f761cc520006f461cc520004fe768c520004fd768c520004fc768c5200067f658c5201567c658c520006df638c520046dc638c52003dee728c520005ed728c520004ff764c520004fe764c520004fc764c5200067f654c5201667c654c520005bf744c520085bc744c520005ef724c52003dec724c520004fe760c520004fd760c520044fc760c52008d7e750c5200057d750c5200067f650c52014e7c650c520006df630c520046dc630c52003dee720c520005ed720c520006f7610c520006f4610c52001dfa700c520005f9700c520005ee76c852003eee76c8520004ee76c852003def75c8520275ed75c85200076f65c852026f6c65c852003def74c852003fae74c8520005ed74c852003fad74c8520005ad74c8520255ee73c852003dec73c8520006ec61c852001dee70c852001dec70c852003eef60c852003feb60c852001cfe768852008d7e75885200057d75885200067f65885201167c6588520265ed7288520006f76188520006f4618852001dfa7088520005f9708852001cfc76485200067f65485201267c6548520006f76148520006f46148520005fb704852001df8704852001cec7648520265ef7548520265ed75485200076f654852025f6c6548520005ef7448520005ed7448520255ee7348520255ec734852003def714852003fe77148520007e76148520006ec6148520007e46148520007eb704852001dee704852001dec7048520007e8704852003eef604852003feb604852000cff7650120084fd765012003cfc76501200067f65501200f67
  | 14 => 0x4ff7558d200067f7558d200047f7558d20014fe7558d20004fd7558d20014fc7558d200067c7558d200147c7558d20004ff7458d20006bf7458d20004bf7458d2000cfe7458d2000cfc7458d20006bc7458d2000cbc7458d20006df7358d20006de5358d20006dd5358d20004ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d20004ff7058d20006fb7058d20004fe7618d200067f6518d200067c6518d20046de6318d20006dd6318d20044ff7690d20004fe7690d20004fd7690d20044fc7690d200067f6590d201ee7c6590d20006bf6490d2000ebc6490d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d201e67c6550d20005ef7250d2003dec7250d20005ee769092003eee769092003def75909202bded75909200076f65909202b76c6590920085ed749092000eee649092000eec6490920255ee7390920006ef6390920006ed6390920007ae4390920087ac4390920005ed719092001dee709092001dec709092003eef609092003feb609092001cfc76509200067f65509201d67c6550920006bf645092000ebc6450920005df7350920005dc735092003fac4250920005fb705092001df8705092001dec765092000eec765092001cec76509202adef75509202aded75509200076f65509202a76c655092003def745092003faf7450920007af645092000eee645092000eec6450920087ac645092000eac6450920087ae54509202a7ad5450920007cf7350920255ec7350920007cc7350920005cc7350920006ef6350920006ed6350920087af4350920007ad4350920005ef7150920087ac4150920007eb705092001dee705092001dec7050920007e8705092003eef605092003feb6050920087af405092001cfe76cc92001cfc76cc9200067f65cc9201ce7c65cc920006df63cc920046dc63cc92001dfa70cc920005f970cc92001dee76cc920256ee76cc92001cee76cc920255ef75cc92029ded75cc9200076f65cc9202976c65cc920255ef74cc920005ed74cc92003dee73cc920256ef63cc920007cf63cc920256ed63cc920257cc63cc920257ce53cc920297cd53cc920005ed71cc92001dee70cc920257ea70cc920257e970cc92001dec70cc92003eef60cc92003feb60cc92001cfc764c9200067f654c9201ae7c654c920005bf744c920085bc744c920006df634c920046dc634c920005fb704c92001df8704c920005ee760c92003eee760c92003def750c92003f6e750c92028ded750c92003f6d750c9200056d750c9200076f650c9202876c650c92003def740c92003fae740c920005ed740c92003fad740c920005ad740c920255ee730c92003fce730c920256ef630c920256ed630c92027fcf430c920257cc430
  | 15 => 0xf65886202e6ed6588620216ef6488620006ed6488620246ee6388620216ec638862003dee7188620217e66188620006ed6188620217e56188620217ea7088620215ed7088620007e9708862003eee6088620006f66148620006f56148620005fb704862001df8704862020ded760862003eed760862020eef65086202deed650862020eef6408620006ed64086202d6ee630862020eec630862003fe67108620006ed610862003def700862020ded700862003fea600862008d7e76d952008e7e76d95200147e76d95200067e64d95200067c64d95202c76f72d952008f6c72d95202cf7b20d95202c76e20d95202c76c20d95202cf7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067c43d95202c67f72d95202ce7e72d952008e7d72d95202ce7c72d95200067f42d95202ce7e42d95202ce7c42d95202ce7e32d95202ce7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95202ce7f21d95202ce7c21d95202ce7f70d95202c67e70d952008e7d70d95202c67c70d95200067f40d95202c67e40d95202c67c40d95202c67e30d95202c67c30d95202ce7f20d95202c67e20d952008e7d20d95202c67c20d95202c67e10d95202c67c10d952000cfe76d91200067f65d91200067c65d9120086be64d9120004ff75d9120014fe75d9120004fd75d9120014fc75d9120044fe73d9120004fd73d9120086bc43d912003cfe72d912001cfd72d912003cfc72d9120086bf42d9120004fe71d9120004fd71d9120086bc41d912003cfd70d9120086bf40d91200057f755912008d7c75591200067f65591200067c6559120086bc6459120005df7359120005dc7359120005f77159120005f47159120004ff75591200067f75591200047f7559120014fe7559120004fd7559120014fc75591200067c75591200147c7559120084ff7459120006bf7459120086be5459120006bd5459120004ff7359120006df7359120004df7359120044fc7359120006dc7359120044dc7359120094ff7259120006ef7259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f471591200a4ff7059120006fb7059120044fe76d8d200067f65d8d200067c65d8d20004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d2000cfe74d8d20004fd74d8d2000cfc74d8d20006df43d8d20006dc43d8d2003cfe72d8d20006ed72d8d2003cfc72d8d20004fe71d8d20004fd71d8d2008d7e7598d200057d7598d200067f6598d200067c6598d20006df6398d200057f7558d2008d7c7558d200067f6558d200067c6558d20005bf7458d20085bc7458d20005f77158d20005f47158d20
  | 16 => 0x8720006ee614872001dee704872001dec704872000cff765032003cfc765032000ebe6450320006bd6450320005ef725032003dec7250320007ad42503200ad7e75cc3200057d75cc320046de63cc320006dd63cc32003dee72cc320005ed72cc320044ff764c320046de634c320006dd634c320005ef724c32003dec724c320004ff7559220014fe7559220004fd7559220014fc755922001ebf7459220096be5459220006bd5459220004ff7359220044fc7359220096bc4359220096bf4259220004ff7159220004fc7159220096bf415922001cfc705922001ebe405922001ebc405922001eef205922001eed2059220004ff7558e20014fe7558e20004fd7558e20014fc7558e20004ff7458e2000cfe7458e2000cfc7458e2001edf7358e20006de5358e20006dd5358e20006df4358e20006dc4358e20004ff7158e20004fc7158e2001cfc7058e2001ede3058e2001edc3058e20044ff7690e2001cfe7690e20004fd7690e2001cfc7690e2000ebe6490e20006bd6490e20004ff7650e2001cfe7650e20004fd7650e2001cfc7650e2000cff7650a2001cfc7650a2000ebe6450a20006bd6450a20005df7350a20005dc7350a2003fac4250a20005fb7050a2001df87050a20046de63cca20006dd63cca2001dfa70cca20005f970cca20044ff764ca20005bf744ca20095bc744ca20046de634ca20006dd634ca2003fcc324ca20005fb704ca2001df8704ca20004ff7598620014fe7598620004fd7598620014fc759862000cfe7498620004fd749862000cfc7498620044fe7398620004fd739862001ef67198620006f65198620006f5519862001cfe709862001ef6109862001ef41098620004ff7558620014fe7558620004fd7558620014fc7558620004ff7458620006bf7458620004bf745862000cfe745862000cfc7458620006bc745862000cbc7458620004ff7358620044fc735862001ef77158620006f65158620006f5515862001cfc705862001eef205862001eed205862001ef6105862001ef41058620004ff769062001cfe7690620004fd7690620236bf649062000ebc6490620004ff7650620004fd765062001cfc765062000ebe6450620006bd6450620005ef725062003dec7250620044ff76cc62001cfe76cc620004fd76cc620046de63cc620006dd63cc62003dee72cc620005ed72cc620004ff768c62001cfe768c620004fd768c620004ff764c620004fd764c62001cfc764c620005bf744c620095bc744c620046de634c620006dd634c620005ef724c62003dec724c620044ff760c62001cfe760c620004fd760c62009d7e750c6200057d750c62001dfa700c620005f9700c62009d7e75886200057d7588620006f66188620006f5618862001dfa7088620005f970886202e76e75886200076d7588620216e
  | 17 => 0x4ff7558f20014fe7558f20004fd7558f20014fc7558f20004ff7458f20006bf7458f20004bf7458f2000cfe7458f2000cfc7458f20006bc7458f2000cbc7458f2003edf7358f20006de5358f20006dd5358f2001cfc7258f2003eec7258f2001cec7258f2003eee4258f2003ede3258f2003edc3258f2003eec3258f2003ecc3258f20004ff7158f20004fc7158f20044ff7690f2003cfe7690f20004fd7690f2003cfc7690f2031ebf6490f2000ebc6490f20046de6390f20006dd6390f2003dec7290f2031fae4290f20004ff7650f2003cfe7650f20004fd7650f2003cfc7650f2000ebe6450f20006bd6450f20046de6350f20006dd6350f20005ef7250f2003dec7250f2003def7650b20076ef7650b20315ef7550b20315ed7550b2003faf7450b2003faf6450b2000eee6450b2003eec6450b2003fac6450b2003eac6450b200a7ae5450b2030fad5450b20007cf7350b202edec7350b20007cc7350b20005cc7350b2003eef6350b20006ed6350b200a7af4350b20007ad4350b20005ef7150b200a7ac4150b2001dee7050b2001dec7050b200a7af4050b2003ded76ccb202eeed76ccb202edef75ccb20305ed75ccb202edef74ccb20005ed74ccb2003fce73ccb2003eef63ccb202eeed63ccb202efce53ccb202ffcd53ccb20005ed71ccb2001dee70ccb2001dec70ccb20004ff7598720014fe75987200067e75987200147e7598720004fd75987200067d75987200047d7598720014fc759872000cfe7498720004fd749872000cfc7498720044fe7398720004fd739872001cfe729872001cee729872003eee5298720006ed529872003eee4298720006ed4298720006ef329872003eec329872003ef6719872003eef219872003ef7219872003ef42198720216ee209872003eec2098720004ff7558720014fe7558720004fd7558720014fc7558720004ff745872000cfe745872000cfc7458720004ff7358720044fc735872001cfc725872003ef7715872003ef7215872003ef42158720004ff769072003cfe7690720004fd769072000ebe6490720006bd649072003dee7290720005ed7290720007ad4290720004ff7650720004fd765072003cfc765072003dee7250720044ff76cc72003cfe76cc720004fd76cc72003dec72cc720004ff768c72003cfe768c720004fd768c720046de638c720006dd638c72003dee728c720005ed728c720004ff764c720004fd764c72003cfc764c720005bf744c7200a5bc744c720005ef724c72003dec724c720044ff760c72003cfe760c720004fd760c7200ad7e750c7200057d750c720046de630c720006dd630c72003dee720c720005ed720c72003def7648720006ef76487202f5ef75487202f5ed7548720005ef7448720005ed74487202edee73487202edec734872003fe7714
  | 18 => 0xf7559030014fe7559030004fd7559030014fc755903001cff745903001ebf74590300b6be5459030006bd5459030044ff7359030044fe7359030044fd7359030044fc7359030046be4359030046bc4359030004ff725903003cfc72590300b6bf4259030004ff7159030004fc71590300b6bf415903001cfe705903001cfc705903001ebe405903001ebc4059030004ff7558830014fe7558830004fd7558830014fc7558830004ff745883000cfe745883000cfc745883001eef7258830006ee5258830006ed5258830046ef3258830046ec3258830004ff7158830004fc715883001eee205883001eec205883003cff769083001cfe7690830004fd769083003eee6290830006ed6290830004ff7650830004fd765083001cfc765083000ebe6450830006bd6450830005df7350830045dc735083003eee6250830006ed62508300b7ac4250830004ff7598430014fe7598430004fd7598430014fc759843000cfe7498430004fd749843000cfc749843003cfe7298430004fd729843001ef67198430006f65198430006f55198430046f73198430046f4319843001ef6109843001ef41098430004ff7558430014fe7558430004fd7558430014fc7558430004ff7458430006bf7458430004bf745843000cfe745843000cfc7458430006bc745843000cbc7458430004ff7258430006ef7258430004ef725843003cfc7258430006ec725843003cec725843001ef77158430006f65158430006f55158430046f73158430046dc3158430046f4315843001edf305843001edd305843001ef6105843001ef41058430004ff769043001cfe7690430004fd7690430236bf649043000ebc6490430006f66190430006f56190430004ff7650430004fd765043001cfc765043000ebe6450430006bd6450430005df7350430045dc7350430006f66150430006f56150430045dd768c430006dd768c430004dd768c430046df658c430326dd658c430045de718c430047d6718c430006dd618c430225dd708c430226de608c430047da608c43003cff76c843001cfe76c8430004fd76c84300b5be74c8430005bd74c8430045de73c8430005dd73c843003eee62c8430006ed62c8430004ff768843001cfe7688430004fd76884300bd7e75884300057d7588430006f66188430006f56188430004ff7648430004fd764843001cfc7648430005df7348430045dc734843003eee6248430006ed6248430006f66148430006f5614843003cff760843001cfe7608430004fd760843003eec6208430004ff7559320014fe7559320004fd7559320014fc755932003ebf74593200a6be5459320006bd5459320004ff7359320044fc73593200a6bf435932001cfc725932003ebe425932003ebc4259320004ff7159320004fc71593200a6bc41593200a6bf4059320
  | 19 => 0x893000cfc74d8930006de53d8930006dd53d8930004fe71d8930004fd71d8930006ef62989300057f75589300cd7c7558930005bf74589300c5bc7458930005f77158930005f471589300c5be7418930005bd741893003eee6218930006ed6218930004fe7690930004fd769093003cfc7690930006bf649093000ebc649093003eee6290930004ff7650930004fe7650930004fc765093000ebe6450930006bd6450930005df7350930045dc73509300c7ac425093001cfe768c930006ef628c93003eec628c93001dfa708c930005f9708c93001cfc764c930005bf744c9300c5bc744c930006ef624c93003eec624c930005fb704c93001df8704c930047d8304c930004ff75d8530014fe75d8530004fd75d8530014fc75d853000cfe74d8530004fd74d853000cfc74d853003cfe72d8530004fd72d8530006f761985300057f75585300cd7c7558530005bf74585300c5bc7458530005ef7258530005ec72585300cd7e75185300057d7518530006f56118530004ff7518530014fe75185300067e75185300147e7518530004fd75185300067d75185300047d7518530014fc751853000cfe7418530004fd741853000cfc7418530006de5318530006dd531853003cfe7218530004fd721853021ede301853021edc3018530004fe7690530004fd7690530004fc7690530006bf649053000ebc6490530045de7390530005dd7390530004ff7650530004fe7650530004fc7650530005de76cc530046de76cc530004de76cc530045df75cc530335dd75cc530006dc61cc53001dde70cc53001ddc70cc530046df60cc530047db60cc53001cfe768c53032ddd738c530006f7618c530006f4618c53001dfa708c530005f9708c53001cfc764c530005bf744c5300c5bc744c530005ef724c530005ec724c530006f7614c530006f4614c530005fb704c53001df8704c53001cdc764c53032ddf754c53032ddd754c5300079f744c5300079c744c530007cf724c530007cc724c530045df714c530047d7714c530007d7614c530006dc614c530007d4614c530007db704c53001dde704c53001ddc704c530007d8704c530046df604c530047db604c530004fe76c8530004fd76c853003cfc76c85300c5be74c8530005bd74c8530006f761c8530006f461c8530004fe7688530004fd7688530004fc76885300cd7e75885300057d7588530045de7388530005dd7388530006ef628853003eec6288530004ff7648530004fe7648530004fc7648530004fe7608530004fd760853003cfc7608530045de7308530005dd7308530006ef620853003eec6208530006f76108530006f4610853001dfa7008530005f9700853000cff76501300c4fd7650130044fc7650130006bf645013000ebc6450130005df7350130045dc735013001fd83050130004f
  | 20 => 0x1ef41098630004ff7558630014fe7558630004fd7558630014fc7558630004ff745863000cfe745863000cfc7458630004ff725863003cfc725863001ef77158630006f65158630006f5515863001cfc705863001edf305863001edd305863001ef6105863001ef41058630004ff769063001cfe7690630004fd769063000ebe6490630006bd6490630006ee6290630006ed6290630004ff7650630004fd765063001cfc765063000ebe6450630006bd6450630005df7350630045dc7350630006ee6250630006ed625063016ebe648c630006bd648c630006ee628c630006ed628c630006f6618c630006f5618c63001dfa708c630005f9708c630226df658c63034edd658c6302279e648c6302279d648c630227ce628c630227cd628c630045de718c630227d6618c630006dd618c630227d5618c630227da708c630225dd708c630007d9708c630046de608c630005bf744c6300d5bc744c63015ebe644c630006bd644c630005ef724c630005ec724c630006ee624c630006ed624c630006f6614c630006f5614c630005fb704c63001df8704c63021ddd760c630046dd760c6300475e750c6300475d750c63021edf650c630346dd650c63021f9e640c63021f9d640c63021fce620c63021fcd620c630047d6710c630006dd610c630045df700c63021ddd700c630047da600c63003cff76c863001cfe76c8630004fd76c86300d5be74c8630005bd74c8630136be64c8630006bd64c8630045de73c8630005dd73c863003eee62c8630006ed62c8630004ff768863001cfe7688630004fd76886300dd7e75886300057d758863012ebe6488630006bd648863003eee6288630006ed6288630004ff7648630004fd764863001cfc764863011ebe6448630006bd6448630005df7348630045dc734863003eee6248630006ed624863003cff760863001cfe7608630004fd7608630106be6408630006bd640863003eee6208630006ed620863001dfa7008630005f9700863000cfe76d91300c6be64d9130004ff75d9130014fe75d9130004fd75d9130014fc75d91300c6be54d9130006bd54d9130044fe73d913001cfd73d9130044fc73d91300c6bf43d913003cfe72d9130004fd72d91300c6bc42d9130004fe71d9130004fd71d91300c6bc41d9130044fd70d91300c6bf40d91300c6bc6459130004ff7559130014fe7559130004fd7559130014fc75591300c4ff7459130006bf74591300d4ff7359130006df735913033ebe435913033ebc4359130004ff725913003cfc72591300c6bf4259130004ff7159130004fc71591300e4ff7059130006fb705913001cfc7650d30006bf6450d3000ebc6450d30005fb7050d3001df87050d30047d83050d30004ff75d8930014fe75d8930004fd75d8930014fc75d893000cfe74d8930004fd74d
  | 21 => 0xc7598a3003eef7498a3003eee7498a3003eed7498a3003eec7498a30006ef5498a30006ee5498a30006ed5498a30006ec5498a3003eef7398a3003eee7398a3003eec7398a30006ef5398a302eeee5398a30006ed5398a302eeec5398a30006ef4398a302eeee4398a30006ed4398a302eeec4398a3003eef7198a3003eee7198a3003eed7198a3003eec7198a30006ef5198a30006ee5198a30006ed5198a30006ec5198a30006ef4198a30006ec4198a302eeef3198a302eeec3198a3001eef7098a3001eee7098a3001eed7098a3001eec7098a3001eef5098a3001eee5098a3001eed5098a3001eec5098a3001eef4098a3001eee4098a3001eed4098a3001eec4098a3001eef3098a3001eee3098a3001eed3098a3001eec3098a3001eef1098a3001eee1098a3001eed1098a3001eec1098a30004ff7558a30014fe7558a30004fd7558a30014fc7558a30004ff7458a3000cfe7458a3000cfc7458a3001eef7258a30006ef5258a30006ee5258a30006ed5258a30006ec5258a30006ef4258a30006ec4258a30004ff7158a30004fc7158a3001cfc7058a3001eee2058a3001eec2058a30006ef7558a30006ee7558a30006ed7558a30006ec7558a30006ef7458a30006ee7458a30006ed7458a30006ec7458a30006ef5458a30006ee5458a30006ed5458a30006ec5458a30006ed7358a30256ec7358a30006ef5358a30256ee5358a30006ed5358a30256ec5358a30006ef4358a30256ee4358a30006ed4358a30256ec4358a30006ef7158a30006ee7158a30006ed7158a30006ec7158a30006ef5158a30006ee5158a30006ed5158a30006ec5158a30006ef4158a30006ec4158a30256ef3158a30256ec3158a3001eef7058a3001eee7058a3001eec7058a3001eef5058a3001eee5058a3001eed5058a3001eec5058a3001eef4058a3001eee4058a3001eed4058a3001eec4058a3001eef3058a3001eee3058a3001eed3058a3001eec3058a3001eef1058a3001eee1058a3001eed1058a3001eec1058a3003cff7690a3001cfe7690a30004fd7690a3000ebe6490a30006bd6490a3003eee6290a30006ed6290a30004ff7650a30004fd7650a3001cfc7650a3000ebe6450a30006bd6450a30005df7350a30045dc7350a3003eee6250a30006ed6250a300d7ac4250a301b6be648ca30006bd648ca3003eee628ca30006ed628ca3001dfa708ca30005f9708ca3003cff764ca30005bf744ca300d5bc744ca301a6be644ca30006bd644ca3003eee624ca30006ed624ca30047cc324ca30005fb704ca3001df8704ca30004ff7598630014fe7598630004fd7598630014fc759863000cfe7498630004fd749863000cfc749863003cfe7298630004fd729863001ef67198630006f65198630006f5519863001cfe709863001ef61098630
  | 22 => 0x8730046f67198730046df3198730046f73198730046f43198730226de3098730046dc3098730004ff7558730014fe7558730004fd7558730014fc7558730004ff745873000cfe745873000cfc745873001cfc7358730004ff725873003cfc7258730046f77158730046f73158730046f43158730004ff7690730044fe7690730004fd769073018e7e65907300067d659073000ebe6490730006bd6490730045de7390730005dd7390730004ff7650730004fd7650730044fc76507301867e65507300067d6550730045df764c730006df764c730355df754c730355dd754c7300475e654c7300475d654c7300079f744c7300079c744c730007cf724c730007cc724c730047d7714c730006de614c73001dde704c73001ddc704c73003cff76c8730044fe76c8730004fd76c873013e7e65c87300067d65c87300e5be74c8730005bd74c8730004ff7688730044fe7688730004fd76887300ed7e75887300057d75887301167e65887300067d6588730045de7388730005dd738873003eee6288730006ed6288730004ff7648730004fd7648730044fc76487301267e65487300067d654873003cff7608730044fe7608730004fd760873010e7e65087300067d6508730045de7308730005dd730873003eee6208730006ed620873000cff7650330044fc76503300f67e65503300067d655033000ebe6450330006bd6450330005df7350330045dc7350330004ff7559230014fe7559230004fd7559230014fc755923001ebf7459230006bf54592300d6be5459230006bd54592300d6bc54592300d6bf4359230004ff725923003cfc72592300d6bf42592300d6bc4259230004ff7159230004fc71592300d6bf41592300d6bc415923001cfc705923001ebe405923001ebc4059230006bf7559230006be7559230006bd7559230006bc7559230006bf735923033ebe7359230006bd735923033ebc7359230006bf535923033ebe5359230006bd535923033ebc5359230006bf7259230006be7259230006bd7259230006bc7259230006bf5259230006be5259230006bd5259230006bc525923033ebf325923033ebc3259230006bf7159230006be7159230006bd7159230006bc7159230006bf5159230006be5159230006bd5159230006bc515923033ebf315923033ebc315923001ebf705923001ebe705923001ebd705923001ebc705923001ebf505923001ebe505923001ebd505923001ebc505923001ebf305923001ebe305923001ebd305923001ebc305923001ebf205923001ebe205923001ebd205923001ebc205923001ebf105923001ebe105923001ebd105923001ebc105923000cff7650e3001cfc7650e3000ebe6450e30006bd6450e300479c4350e30005fb7050e3001df87050e3003eef7598a3003eee7598a3003eed7598a3003ee
  | 23 => 0x44fc76cc54033dbf74cc54000dbc74cc540004fe768c540004fd768c540004fc768c54000dbe748c540005bd748c540006df638c540046dc638c540004ff764c540004fe764c540004fc764c540005bf744c54000dbc744c540005ef724c540005ec724c540004fe760c540004fd760c540044fc760c5400f57e750c5400057d750c54000dbe740c540005bd740c540006df630c540046dc630c54001dfa700c540005f9700c540004fe76c8540004fd76c854003cfc76c854000dbe74c8540005bd74c8540006f761c8540006f461c8540004fe7688540004fd7688540004fc76885400f57e75885400057d758854000dbe7488540005bd7488540006ef628854003eec6288540007ad4288540004ff7648540004fe7648540004fc764854000dbe7448540005bd7448540004fe7608540004fd760854003cfc760854000dbe7408540005bd7408540006ef620854003eec6208540007ad4208540006f76108540006f4610854001dfa7008540005f970085400067f74597300067e74597300067d74597300067c74597300467f73597300467e73597300467d73597300467c73597300467f43597300467e43597300467d43597300467c43597300067f72597300067e72597300067d72597300067c72597300067f42597300067c42597300467f32597300467e32597300467d32597300467c32597300067f71597300067e71597300067d71597300067c71597300067f41597300067c41597300467f31597300467e31597300467d31597300467c31597300ee7f705973035e7e70597300067d705973035e7c70597300067f405973035e7e405973035e7c40597300467f30597300467e30597300467d30597300467c305973035e7e205973035e7c205973035e7e105973035e7c1059730004ff7559330014fe7559330004fd7559330014fc7559330046bf745933001cfc7359330046be4359330046bc4359330004ff725933003cfc72593300e6bf4259330004ff7159330004fc71593300e6bc41593300e6bf4059330004ff7558b30014fe7558b30004fd7558b30014fc7558b30004ff7458b3000cfe7458b3000cfc7458b3001cfc7358b30046de5358b30006dd5358b30046ef7258b30046ef3258b30046ec3258b30004ff7158b30004fc7158b3003cff7690b30044fe7690b30004fd7690b301de7e6590b300067d6590b3003eee6290b30006ed6290b30004ff7650b30004fd7650b30044fc7650b301d67e6550b300067d6550b3000ebe6450b30006bd6450b30005df7350b30045dc7350b3003eee6250b30006ed6250b300e7ac4250b30004ff7598730014fe7598730004fd7598730014fc759873000cfe7498730004fd749873000cfc749873001cfe739873001cde7398730046de5398730006dd539873003cfe7298730004fd729
  | 24 => 0xe71d8d40004fd71d8d400f57e7598d400057d7598d40006df6398d400c5f97098d400e5fb7058d40046de6318d40006dd6318d4001cbe7690d4033dbf7590d40385bd7590d4037ebf6590d4037ebd6590d4000dbe7390d4000f9e7390d4033ebf6390d400079f6390d4033f9c6390d40005bd7290d4031ebc6290d40005bd7190d4001dbe7090d4033fba7090d4033fb97090d4001dbc7090d4000ebf6090d4000fbb6090d40004ff75d8940014fe75d8940004fd75d8940014fc75d894001cfd74d8940096be54d8940006bd54d8940044fe73d8940004fd73d8940096ee42d8940096ed42d8940004fe71d8940004fd71d8940006ef6298940085f970989400057f75589400f57c7558940005df7358940005dc7358940005f77158940005f471589400a5fb705894003eee6218940006ed621894001cbc7650940375bf7550940375bd755094036ebf655094036ebd65509400079f735094033dbc73509400079c73509400059c7350940006bf635094000dbf725094000faf7250940007af625094003ebe625094003ebc6250940007ac625094003eac6250940005bf7150940007bb705094001dbe705094001dbc7050940007b8705094000ebf605094000fbb6050940004fe76cc940004fd76cc940044fc76cc94033dbf74cc94000dbc74cc940004fe768c940004fd768c94003cfc768c94000dbe748c940005bd748c940006df638c940046dc638c9401b79c438c940007ad428c940004ff764c940004fe764c940004fc764c940005bf744c94000dbc744c940007ad424c940004fe760c940004fd760c94003cfc760c9400f57e750c9400057d750c94000dbe740c940005bd740c940006df630c940046dc630c94033f9c430c940004ff75d8540014fe75d8540004fd75d8540014fc75d854001cfd74d8540044fe73d8540004fd73d854003cfe72d8540004fd72d854005ef641d854005ef541d8540006f7619854004df970985400057f75585400f57c7558540005df7358540005dc7358540005ef7258540005ec725854006dfb70585400f57e75185400057d7518540006f56118540004ff7518540014fe75185400067e75185400147e7518540004fd75185400067d75185400047d7518540014fc751854001cfd7418540026be5418540006bd5418540044fe7318540004fd7318540006be4318540026bc431854003cfe7218540004fd7218540026bf4218540006bd4218540026bf4118540026f64118540026f5411854022ebe401854022ebc401854001cbc7650540365bf7550540365bd755054033dbc7350540005bf725054000dbf715054000fb77150540007b76150540006bc6150540007b46150540007bb705054001dbe705054001dbc7050540007b8705054000ebf605054000fbb6050540004fe76cc540004fd76cc540
  | 25 => 0x8e400c6dd4358e40004ff7258e4003cfc7258e40004ff7158e40004fc7158e4001cfc7058e4001ede3058e4001edc3058e40004ff7558a40014fe7558a40004fd7558a40014fc7558a40004ff7358a40044fc7358a4001eef7258a40006ee5258a40006ed5258a40086ee4258a40086ed4258a40004ff7158a40004fc7158a40086bc4158a4001cfc7058a4001ebf4058a4001ebd4058a4001eee2058a4001eec2058a40044ff76cca4001cfe76cca40004fd76cca4003eee62cca40006ed62cca4003cff768ca4001cfe768ca40004fd768ca40046de638ca40006dd638ca40004ff764ca40004fd764ca4001cfc764ca40005bf744ca4000dbc744ca4003cff760ca4001cfe760ca40004fd760ca400fd7e750ca400057d750ca4000dbe740ca40005bd740ca40046de630ca40006dd630ca4003eee620ca40006ed620ca40004ff7598640014fe7598640004fd7598640014fc7598640044fe7398640004fd739864003cfe7298640004fd729864001ef67198640006f65198640006f5519864006ef6419864006ef5419864001cfe709864001ef6109864001ef41098640004ff7558640014fe7558640004fd7558640014fc7558640004ff7358640044fc7358640004ff7258640006ef7258640004ef725864003cfc7258640006ec725864003cec725864001ef77158640006f65158640006f5515864004ef6415864004ef5415864004ebc415864001cfc705864001ebf405864001ebd405864001ef6105864001ef41058640236bf6590640396bd659064038ebe6390640006bd629064000dbe719064000fb67190640237b66190640006bd6190640237b56190640237ba7090640235bd7090640007b9709064000ebe609064000fba6090640044ff76cc64001cfe76cc640004fd76cc64000dbe74cc640005bd74cc640046de63cc640006dd63cc640004ff768c64001cfe768c640004fd768c640004ff764c640004fd764c64001cfc764c640005bf744c64000dbc744c640046de634c640006dd634c640005ef724c640005ec724c640044ff760c64001cfe760c640004fd760c6400fd7e750c6400057d750c64001dfa700c640005f9700c64003cff76c864001cfe76c8640004fd76c864000dbe74c8640005bd74c864003eee62c8640006ed62c8640004ff768864001cfe7688640004fd76886400fd7e75886400057d7588640004ff7648640004fd764864001cfc7648640005bf744864000dbc744864003eee6248640006ed624864003cff760864001cfe7608640004fd760864003eec620864001dfa7008640005f97008640004ff75d8d40014fe75d8d40004fd75d8d40014fc75d8d4001cfd74d8d40006de53d8d40006dd53d8d400d6de43d8d400d6dd43d8d4033ebc43d8d4003cfe72d8d40004fd72d8d400d6bf42d8d40004f
  | 26 => 0x4fd7558c21014fc7558c21004ff7458c21006bf7458c21004bf7458c2100cfe7458c2100cfc7458c21006bc7458c2100cbc7458c2103edf7358c21006de5358c21006dd5358c2103cfe7258c2103cfc7258c2103eec7258c2103cec7258c2103eee4258c2103ede3258c2103edc3258c2103eec3258c2103ecc3258c21004ff7058c2101cfc7058c21044ff7690c2103cfe7690c21004fd7690c2103cfc7690c2131ebf6490c2100ebc6490c21046de6390c21006dd6390c2103dec7290c2131fae4290c21004ff7650c2103cfe7650c21004fd7650c2103cfc7650c2100ebe6450c21006bd6450c21046de6350c21006dd6350c21005ef7250c2103dec7250c2103def7650821136ef76508213cdef75508213cded755082103def745082103faf745082103faf645082100eee645082103eec645082103fac645082103eac6450821107ae54508213c7ad5450821007cf73508212d5ec7350821007cc7350821005cc735082103eef6350821006ed6350821107af4350821007ad4350821005ef715082112eee615082103fe66150821107ac415082120dec7050821107af405082103ded76cc8212d6ed76cc8212d5ef75cc8213bded75cc8212d5ef74cc821005ed74cc82103dee73cc82103fce73cc82103eef63cc8212d6ed63cc8212d7ce53cc8213b7cd53cc821005ed71cc821246ee61cc82103fe661cc82120dee70cc82112cff769042103cfe769042100cfd769042103cfc769042100ebe6490421006bd649042103dee7290421005ed7290421007ad429042112cff765042103dee7250421004fd76cc42103dec72cc421004ff768c421044fd768c421046de638c421006dd638c42103dee728c421005ed728c421004ff764c421005bf744c421105bc744c421005ef724c42103dec724c421044ff760c42103cfe760c421004fd760c42103cfc760c42110d7e750c4210057d750c421046de630c421006dd630c42103dee720c421005ed720c42103def7648421006ef7648421004ef76484213adef75484213aded7548421005ef7448421005ed74484212d5ee73484212d5ec734842103def714842103fe771484213a6ee614842103fe6614842139fe6514842139fe5514842120dec7048421004ff75580210067f75580210047f7558021014fe7558021004fd7558021014fc75580210067c75580210147c7558021004ff745802100cfe745802100cfc7458021004ff7358021044fc735802103eee5258021006ed525802103eee4258021006ed4258021006ef325802103eec325802103eef2158021006ed215802103efb7058021006fa5058021006f9505802103efb205802103eec205802103ef82058021004ff7558e40014fe7558e40004fd7558e40014fc7558e4001edf7358e40006de5358e40006dd5358e400c6de435
  | 27 => 0xf7359121044fc7359121006dc7359121044dc735912112cff7259121006ef7259121134ff7159121006f7715912111ebc4159121004ff705912101cfc705912111ebf4059121044fe76d8d21004ff75d8d21014fe75d8d21004fd75d8d21014fc75d8d2100cfe74d8d21004fd74d8d2100cfc74d8d21006de53d8d21006dd53d8d21006df43d8d21006dc43d8d2101cfe70d8d21004fd70d8d21006df6398d21005bf7458d2111dbc7458d21004ff7558d21014fe7558d21004fd7558d21014fc7558d21004ff7458d21006bf7458d21004bf7458d2100cfe7458d2100cfc7458d21006bc7458d2100cbc7458d21006df7358d21004ff7258d21006ef7258d21004ef7258d21004ff7158d21006f77158d21004ff7058d2101cfc7058d21004fe7618d211257e7518d210057d7518d21046de6318d21006dd6318d21044ff7690d21004fe7690d21004fd7690d21044fc7690d21006bf6490d2100ebc6490d21004ff7650d21004fe7650d21004fd7650d21004fc7650d2100cfc7650921006bf645092100ebc6450921005df7350921005dc735092103fac4250921005f77150921005f47150921004fe76cc921006df63cc921046dc63cc921005f671cc921005f571cc921044fc764c921005bf744c92111dbc744c921006df634c921046dc634c92103fcc324c921005f7714c921005f4714c921134fe769052100ebe6490521006bd649052100cff765052111cfd765052103cfc7650521006bf645052100ebc6450521005ef725052103dec725052103cfe76cc52103cfc76cc521006df63cc521046dc63cc52103dee72cc521005ed72cc521004fe768c521044ff764c521004fd764c52103cfc764c521005bf744c52111dbc744c521006df634c521046dc634c521005ef724c52103dec724c521004fe760c5211257e750c5210057d750c5211257e75885210057d758852103df6718852103ef761885213d76e75885210076d75885213d6ef65885213d6ed6588521006ef6488521006ed6488521246ee6388521246ec638852103dee718852103eef618852103fe76188521005ed7088521004ff75d8121014fe75d8121004fd75d8121014fc75d812100cfe74d8121004fd74d812100cfc74d8121044fe73d8121004fd73d8121006fb60981210057f75581211257c7558121005bf745812111dbc7458121005df7358121005dc735812111dbe7418121005bd7418121216ef621812101efa6018121006f96018121004ff7559021014fe7559021004fd7559021014fc755902103ebf7459021106be5459021006bd5459021004ff7359021044fc7359021106bf435902103cfe725902103cfc725902103ebe425902103ebc4259021104fc7159021106bc4159021004ff705902101cfc7059021106bf4059021004ff7558c21014fe7558c21
  | 28 => 0xca21006dd63cca21005f671cca21005f571cca21246ed76cca21245ef75cca2140ded75cca214076e65cca210076d65cca21245ef74cca21005ed74cca2103dee73cca21246ef63cca21247ce63cca21246ed63cca21007cd63cca21247ce53cca21407cd53cca21247e671cca21005ed71cca21247e571cca2103eee61cca21215ee70cca21044ff764ca211ae7e654ca210067d654ca21005bf744ca2112dbc744ca21046de634ca21006dd634ca21005f7714ca21005f4714ca21005ed760ca2103eed760ca2103def750ca2103f6e750ca213fded750ca2103f6d750ca210056d750ca213f76e650ca210076d650ca2103def740ca2103fae740ca21005ed740ca2103fad740ca21005ad740ca2103fce730ca21246ef630ca21246ed630ca213efcf430ca21247cc430ca21005ed710ca2103fe6610ca21215ee700ca2100cfe769062103cfd769062118e7e65906210067d659062100ebe6490621006bd649062103dee7290621005ed7290621007ad4290621104ff76506211867e65506210067d655062117e7e65cc6210067d65cc62103cfd768c6211567e658c6210067d658c621046de638c621006dd638c62103dee728c621005ed728c6211667e654c6210067d654c621005bf744c62112dbc744c621005ef724c62103dec724c62103cfd760c6211157e750c6210057d750c62114e7e650c6210067d650c621046de630c621006dd630c62103dee720c621005ed720c621005ed76c862103eed76c862103def75c86213e5ed75c86213df6e65c86210076d65c862103def74c862103fae74c8621005ed74c862103fad74c8621005ad74c8621245ee73c862103dec73c862103fe661c86213dfe651c86213dfe551c8621215ee70c86211157e75d82210057d75d82210067e65d82210067d65d82210067e65982210067d6598221006fb60982210067e65582210067d6558221004ff7558221014fe7558221004fd7558221014fc7558221004ff745822100cfe745822100cfc7458221004ff7358221044fc7358221006ee5258221006ed5258221006ee4258221006ed4258221006ef3258221006ec3258221006ef21582211157e75182210057d75182210067e65182210067d651822112dbe7418221005bd7418221005de7318221005dd731822101efa6018221006f9601822100cfe76d912111ebe64d9121004ff75d9121014fe75d9121004fd75d9121014fc75d912111ebe54d9121006bd54d9121044fe73d9121004fd73d912111ebc43d912111cfd72d912111ebf42d912103cfd71d912111ebf41d912101cfe70d9121004fd70d912111ebc40d912111ebc6459121005df7359121005dc7359121004ff7559121014fe7559121004fd7559121014fc755912111cff7459121006bf7459121004ff7359121006df7359121004d
  | 29 => 0x12ebe64d9221005de73d9221005dd73d9221004ff75d9221014fe75d92210067e75d92210147e75d9221004fd75d92210067d75d92210047d75d9221014fc75d922112cfd74d922112ebe54d9221006bd54d9221044fe73d9221006de73d9221044de73d9221004fd73d9221006dd73d9221004dd73d9221006ed72d9221006f671d922101cfe70d9221004fd70d922100cff76592210067e65592210067d655922112ebc6459221004ff7559221014fe7559221004fd7559221014fc7559221006bf7459221004ff7359221044fc735922112ebc435922112ebf425922103cfc715922112ebc4159221004ff705922101cfc705922112ebf40592211157e75d8e210057d75d8e210067e65d8e210067d65d8e2112dbe74d8e21005bd74d8e21004ff75d8e21014fe75d8e210067e75d8e210147e75d8e21004fd75d8e210067d75d8e210047d75d8e21014fc75d8e2100cfe74d8e21006be74d8e2100cbe74d8e21004fd74d8e21006bd74d8e21004bd74d8e2100cfc74d8e21006de53d8e21006dd53d8e21006ed72d8e21006f671d8e2101cfe70d8e21004fd70d8e21004fd7698e210067e6598e210067d6598e21006df6398e21044ff7658e210067e6558e210067d6558e21004ff7558e21014fe7558e21004fd7558e21014fc7558e21004ff7458e2100cfe7458e2100cfc7458e21006df7358e21006df4358e21006dc4358e21006ef7258e21004ff7058e2101cfc7058e211157e7518e210057d7518e210067e6518e210067d6518e21046de6318e21006dd6318e21044ff7690e21004fe7690e21004fd7690e21044fc7690e211ee7e6590e210067d6590e2100ebe6490e21006bd6490e21004ff7650e21004fe7650e21004fd7650e21004fc7650e211e67e6550e210067d6550e21005ef7250e2103dec7250e21005ed7690a2103eed7690a2103def7590a2142ded7590a214276e6590a210076d6590a2100eee6490a2100eec6490a21245ee7390a21006ef6390a21006ed6390a21007ae4390a2112fac4390a21005ed7190a2103fe66190a21215ee7090a2100cff7650a211d67e6550a210067d6550a2100ebe6450a21006bd6450a21005df7350a21005dc7350a2103fac4250a21005f77150a21005f47150a2112def7650a2100eef7650a2100cef7650a2141def7550a2141ded7550a214176e6550a210076d6550a2103def7450a2103faf7450a2100eee6450a2112fae6450a2100eae6450a21007ad6450a2100eec6450a2112fae5450a21417ad5450a21007cf7350a21245ec7350a21007cc7350a21005cc7350a21006ef6350a21006ed6350a2112faf4350a21007ad4350a21005ef7150a21007e77150a21007e47150a2103eee6150a2112fac4150a21215ec7050a2112faf4050a211ce7e65cca210067d65cca21046de63c
  | 30 => 0xc7059321136bf4059321136bc405932103eef2059321006bf7559321006be7559321006bd7559321006bc7559321006bf7359321006be7359321006bd7359321006bc7359321006bf5359321006be5359321006bd5359321006bc535932103ebf725932103ebe725932103ebd725932103ebc725932103ebf525932103ebe525932103ebd525932103ebc525932103ebf325932103ebe325932103ebd325932103ebc3259321006bf7159321006bd7159321136bc7159321006bf5159321006be5159321006bd5159321006bc515932103ebf215932103ebe215932103ebd215932103ebc215932103eac2159321006bf7059321006be7059321006bd7059321006bc7059321006bf5059321006be5059321006bd5059321006bc505932103ebf205932103eaf205932103ebe205932103ebd205932103ebc2059321004ff7558f21014fe7558f21004fd7558f21014fc7558f21004ff7458f2100cfe7458f2100cfc7458f2103edf7358f21006de5358f21006dd5358f2103cfc7258f2103ede3258f2103edc3258f21004ff7058f2101cfc7058f21044ff7690f2103cfe7690f21004fd7690f2103cfc7690f2100ebe6490f21006bd6490f21004ff7650f2103cfe7650f21004fd7650f2103cfc7650f2100ebe6450f21006bd6450f2111cfd769072100ebe6490721006bd649072100cff765072103cfc765072100ebe6450721006bd6450721005ef725072103dec7250721176be64cc721006bd64cc721046de63cc721006dd63cc72103dee72cc721005ed72cc72116ebe648c721006bd648c721044ff764c721005bf744c721135bc744c72115ebe644c721006bd644c721046de634c721006dd634c721005ef724c72103dec724c72113d7e750c7210057d750c721146be640c721006bd640c721004ff7558321014fe7558321004fd7558321014fc7558321004ff745832100cfe745832100cfc7458321004ff7358321044fc735832103efb705832103efb205832103ef820583211157f76596211167f76596210147f76596210067e64596210067c64596211176e72596210076d72596214377721596214377421596210067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067c43596211167f72596214367e72596210067d72596214367c72596210067f42596214367e42596214367c42596214367e32596214367c32596211167f71596214367e71596211167d71596211167c71596210067f41596210067c41596214367f21596211167e21596214367c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067c40596214367f20596214367c20596211157e75d92210057d75d92210067e65d92210067d65d9221
  | 31 => 0x8131005ef7258131005ec7258131006ef6258131006ec6258131006bf6418131006bc6418131226df6318131006ef6218131006ec621813101efa6018131006f960181310067f74594310067e74594310067d74594310067c74594310467f73594310467e73594310467d73594310467c73594310467f43594310467e43594310467d43594310467c43594310067f72594310067e72594310067d72594310067c72594310067f42594310067c42594310467f32594310467e32594310467d32594310467c325943114e7f71594310067e715943114e7d715943114e7c71594310067f41594310067c41594310467f31594310467e31594310467d31594310467c31594310067f70594310067e70594310067d70594310067c70594310067f40594310067c40594310467f30594310467e30594310467d30594310467c3059431004ff7559031014fe7559031004fd7559031014fc7559031046bf7459031044fe7359031044fc7359031046be4359031046bc4359031004ff725903103cfc7259031146bf4259031144fc7159031146bc4159031004ff705903101cfc7059031146bf4059031004ff7558831014fe7558831004fd7558831014fc7558831004ff745883100cfe745883100cfc7458831046de5358831006dd5358831046ef7258831046ef3258831046ec3258831004ff705883101cfc705883103cff7690831044fe7690831004fd76908311de7e65908310067d659083103eee6290831006ed6290831004ff7650831004fd7650831044fc76508311d67e65508310067d655083100ebe6450831006bd6450831005df7350831045dc735083103eee6250831006ed6250831147ac425083116cff7690431044fe769043100cfd7690431044fc769043118e7e65904310067d659043100ebe6490431006bd6490431045de7390431005dd739043116cff76504311867e65504310067d6550431045df764c431006df764c431004df764c43144ddf754c43144ddd754c4310475e654c4310475d654c4310079f744c4310079c744c431007cf724c431007cc724c431045df714c431047d7714c431446de614c431047d6614c43143fd6514c43143fd5514c43121ddc704c431004ff7558031014fe7558031004fd7558031014fc7558031004ff745803100cfe745803100cfc7458031046de5358031006dd5358031004ff725803103cfc7258031046df3158031006dd3158031046fb7058031046fb3058031046dc3058031046f83058031004ff7559321014fe7559321004fd7559321014fc755932103ebf7459321006bf5459321136be5459321006bd5459321136bc5459321004ff7359321044fc7359321136bf4359321136bc435932103cfc725932103ebe425932103ebc4259321136bf415932103eec2159321004ff705932101cf
  | 32 => 0x6ec40d8931246ef30d8931246ec30d893115dbe7498931005bd7498931006bf6498931006bc6498931006ef6298931005bf745893115dbc7458931006bf6458931006bc6458931006bf6418931006bc641893103eee6218931006ed6218931005ee7618931006ee7618931006ef6518931006ee6518931006ed6518931006ec6518931006ef6418931007af6418931006af6418931006ee6418931006ed6418931006ec6418931007ac6418931006ac64189312d7e731189312d7e4311893103eef751893103eee751893103eed751893103eec751893103eef741893103eee741893103eed741893103eec7418931006ef5418931006ee5418931006ed5418931006ec541893103eef731893103eee731893103eec7318931006ef53189312d6ee5318931006ed53189312d6ec5318931006ef43189312d6ee4318931006ed43189312d6ec431893103eef711893103eed7118931006ef5118931006ee5118931006ed5118931006ec5118931006ef4118931006ec41189312d6ef3118931006ed31189312d6ec311893103eef701893103eee701893103eed701893103eec7018931006ef5018931006ee5018931006ed5018931006ec5018931006ef4018931006ec40189312d6ef30189312d6ec3018931004fe7690931004fd769093103cfc7690931006bf649093100ebc6490931006ef629093103eec6290931004ff7650931004fe7650931004fc7650931006bf645093100ebc6450931005df7350931045dc7350931006ef625093103eec625093115fac4250931006bf648c9311b6bc648c931006ef628c93103eec628c931005f6718c931005f5718c93103cfc764c931005bf744c93115dbc744c931006bf644c9311a6bc644c931006ef624c93103eec624c931047cc324c931005f7714c931005f4714c931174fe7690531006bf649053100ebc6490531006ef6290531006ec629053100cff765053115cfd7650531044fc7650531006bf645053100ebc6450531005df7350531045dc7350531006ef6250531006ec6250531006bf648c53116ebc648c531006ef628c531006ec628c531045f6718c531046f7618c531456df658c531456dd658c5310079f648c5310079c648c531007cf628c531007cc628c531045de718c531046df618c531047d7618c531005dd708c531006bf64d8131006bc64d8131006ef62d8131006ec62d8131004ff75d8131014fe75d8131004fd75d8131014fc75d813100cfe74d8131004fd74d813100cfc74d813103cfe72d8131004fd72d8131006fb50d8131006f850d813115dbe7498131005bd7498131006bf6498131006bc6498131005ee7298131005ed7298131006ef6298131006ec6298131006fb60981310057f75581311657c7558131005bf745813115dbc7458131006bf6458131006bc645
  | 33 => 0xf43d913103cfe72d9131004fd72d913115ebf42d913115ebc42d9131044fd71d913115ebf41d913101cfe70d9131004fd70d913115ebf40d913115ebc40d913115dbe76d913100cbe76d9131006bf65d9131006be65d9131006bd65d9131006bc65d913138fb731d913138fb431d9131006bf75d9131006be75d9131006bd75d9131006bc75d9131006bf73d913138ebe73d9131006bd73d913138ebc73d9131006bf53d913138ebe53d9131006bd53d913138ebc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006be52d9131006bd52d9131006bc52d913138ebf32d913138ebc32d913138ebf71d913115ebe71d9131006bd71d9131006bf51d9131006be51d9131006bd51d9131006bc51d913138ebf31d913138ebc31d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d913138ebf30d913138ebc30d913115ebc6459131005ef7259131005ec7259131004ff7559131014fe7559131004fd7559131014fc755913115cff7459131006bf745913116cff7359131006df7359131004ff7259131006ef7259131004ef725913103cfc7259131006ec725913103cec7259131174ff7159131006f77159131004ff705913101cfc7059131005be761913115ebe7619131004be761913115f3e751913115f3d7519131006bf6519131006be6519131006bd6519131006bc651913145ebf611913145fb7311913145fb4311913100cfc7650d31006bf6450d3100ebc6450d310479c4350d31005f77150d31005f47150d31006bf64d8931006bc64d8931004ff75d8931014fe75d8931004fd75d8931014fc75d893100cfe74d8931004fd74d893100cfc74d8931006ef52d8931006ee52d8931006ed52d8931006ec52d8931006ef42d8931006ec42d893101cfe70d8931004fd70d8931006ef65d8931006ee65d8931006ed65d8931006ec65d8931006ef64d8931007af64d8931006af64d8931006ee64d8931006ed64d8931006ec64d8931007ac64d8931006ac64d8931247e731d8931247e431d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d8931006ee54d8931006ed54d8931006ec54d8931006ef73d8931246ee73d8931006ef53d8931246ee53d8931006ed53d8931246ec53d8931006ef43d8931246ee43d8931006ed43d8931246ec43d8931246ef71d8931006ed71d8931006ef51d8931006ee51d8931006ed51d8931006ec51d8931006ef41d8931006ec41d8931246ef31d8931246ec31d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef50d8931006ee50d8931006ed50d8931006ec50d8931006ef40d8931
  | 34 => 0xb31004fd7690b3103eee6290b31006ed6290b31004ff7650b31004fd7650b31044fc7650b3100ebe6450b31006bd6450b31005df7350b31045dc7350b3103eee6250b31006ed6250b31177ac4250b3115cfd769073138ebf649073100ebc649073100cff7650731044fc765073100ebe6450731006bd6450731005df7350731045dc7350731004ff7558331014fe7558331004fd7558331014fc7558331004ff745833100cfe745833100cfc7458331004ff725833103cfc7258331046fb7058331046fb3058331046f8305833116ebe64d9231004ff75d9231014fe75d9231004fd75d9231014fc75d923116cfd74d9231006dd73d923138ebe43d923138ebc43d923103cfe72d9231004fd72d923116ebf42d9231006f671d923101cfe70d9231004fd70d923100cff765923116ebc6459231004ff7559231014fe7559231004fd7559231014fc7559231006bf745923116ebe5459231006bd545923116ebf4359231004ff725923103cfc725923116ebc4259231044fc715923116ebc4159231004ff705923101cfc705923116ebf405923100cff7650e3100ebe6450e31006bd6450e31005f77150e31005f47150e311557e75d8a310057d75d8a3116dbe74d8a31005bd74d8a3116dbe7498a31005bd7498a31006ef6298a31004ff7558a31014fe7558a31004fd7558a31014fc7558a31004ff7458a3100cfe7458a3100cfc7458a31006de5358a31006dd5358a31004ff7058a3101cfc7058a3103eee6218a31006ed6218a3103cff7690a31004fe7690a31004fd7690a3100ebe6490a31006bd6490a3103eec6290a31004ff7650a31004fd7650a31004fc7650a31006bf6450a3100ebc6450a31005df7350a31045dc7350a3116fac4250a3103eee628ca31006ed628ca31005f6718ca31005f5718ca3103cff764ca31005bf744ca3116dbc744ca3103eee624ca31006ed624ca31005f7714ca31005f4714ca3100cfe7690631044fd769063100ebe6490631006bd6490631045de7390631005dd7390631144ff7650631005dd76cc631046dd76cc631045df75cc63146ddd75cc631047d661cc631467d651cc631467d551cc631225de70cc631006fb60982310057f75582311557c7558231004ff75582310067f75582310047f7558231014fe7558231004fd7558231014fc75582310067c75582310147c7558231004ff745823100cfe745823100cfc7458231006de5358231006dd5358231004ff725823103cfc7258231006df31582311557e75182310057d751823116dbe7418231005bd7418231005ee7218231005ed721823101efa6018231006f9601823100cfe76d913115ebe64d9131004ff75d9131014fe75d9131004fd75d9131014fc75d9131006bf54d913115ebe54d9131006bd54d913115ebc54d913115cfd73d913115eb
  | 35 => 0x4fd760ca4118d7e750ca410057d750ca4100dbe740ca41005bd740ca41046de630ca41006dd630ca4138f9c430ca41006fb60982410057f755824118d7c7558241004ff75582410067f75582410047f7558241014fe7558241004fd7558241014fc75582410067c75582410147c755824104ebe5458241006bd5458241004ff7358241044fc7358241006be435824104ebc4358241004ff725824103cfc725824104ebf4258241006bd425824104ebf415824104efa4058241236bc405824118d7e75182410057d7518241005de7318241005dd7318241005ee7218241005ed721824101efa6018241006f96018241004ff75d8d41014fe75d8d41004fd75d8d41014fc75d8d41006de53d8d41006dd53d8d4116ede43d8d4116edd43d8d4103cfe72d8d41004fd72d8d4101cfe70d8d41004fd70d8d41006df6398d4115df57198d41005ef7258d41005ec7258d41175f77158d411857e7518d410057d7518d41046de6318d41006dd6318d41004ff75d8941014fe75d8941004fd75d8941014fc75d8941044fe73d8941004fd73d8941006ee52d8941006ed52d894112eee42d894112eed42d894112ebc41d894101cfe70d8941004fd70d894112ebf40d8941006ef629894111df57198941005df7358941005dc7358941135f7715894103eee6218941006ed6218941004fe76cc941004fd76cc941044fc76cc941006ef62cc94103eec62cc941004fe768c941004fd768c94103cfc768c941006df638c941046dc638c941004ff764c941004fe764c941004fc764c941005bf744c94100dbc744c941004fe760c941004fd760c94103cfc760c9411857e750c9410057d750c94100dbe740c941005bd740c941006df630c941046dc630c941006ef620c94103eec620c941476bf6590541476bd659054138ebc6390541006bf629054100dbe719054100fb6719054100ebf619054100fb76190541005bd7090541004ff75d8141014fe75d8141004fd75d8141014fc75d8141044fe73d8141004fd73d814103cfe72d8141004fd72d814106efa40d8141006fb60981410057f75581411857c7558141005df7358141005dc7358141005ef7258141005ec7258141236bf6418141005ee7218141005ed721814101efa6018141006f96018141004ff7559331014fe7559331004fd7559331014fc7559331046bf7459331176be5459331006bd5459331044fc7359331046be4359331046bc4359331004ff725933103cfc7259331176bf4259331176bf4159331004ff705933101cfc7059331176bc4059331004ff7558b31014fe7558b31004fd7558b31014fc7558b31004ff7458b3100cfe7458b3100cfc7458b31046ef7258b31006ee5258b31006ed5258b31046ef3258b31046ec3258b31004ff7058b3101cfc7058b3103cff7690b31044fe769
  | 36 => 0xc315903203ebf215903203ebe215903203ebd215903203ebc215903203eac2159032006bf7059032006be7059032006bd7059032006bc7059032006bf5059032006be5059032006bd5059032006bc5059032046bf3059032046be3059032046bd3059032046bc305903203ebf205903203eaf205903203ebe205903203ebd205903203ebc2059032004ff7598432014fe7598432004fd7598432014fc759843200cfe7498432004fd749843200cfc749843203ef67198432046f73198432046f4319843203ef7219843203ef4219843201cfe7098432004fd7098432004ff7558432014fe7558432004fd7558432014fc7558432004ff745843200cfe745843200cfc745843203ef77158432046f73158432046f4315843203ef7215843203eec215843203ef42158432004ff705843201cfc705843203eef2058432004ff7558032014fe7558032004fd7558032014fc7558032004ff745803200cfe745803200cfc7458032004ff7158032004fc715803203efb7058032046fb3058032046f8305803203efb205803203ef82058032145f671d8e41006df6398e41004ff7558e41014fe7558e41004fd7558e41014fc7558e41006de5358e41006dd5358e4115ede4358e4115edd4358e4138ebc4358e41004ff7258e4103cfc7258e4115ebf4258e41004ff7058e4101cfc7058e4118d7e7518e410057d7518e41046de6318e41006dd6318e4116df67118e4138dbf7590e41495bd7590e4148ebf6590e4148ebd6590e4100dbe7390e4100f9e7390e4138f9e6390e4138ebd6390e410079d6390e41005bd7290e4131ebe6290e4138fb67190e41005bd7190e4138fb57190e4100ebe6190e4100fb66190e41235be7090e4118d7e75d8a410057d75d8a41005de73d8a41005dd73d8a41105f671d8a41006ef6298a41004ff7558a41014fe7558a41004fd7558a41014fc7558a4111ebe5458a41006bd5458a41004ff7358a41044fc7358a4111eee4258a4111eed4258a41004ff7058a4101cfc7058a4103eee6218a41006ed6218a4112df67118a4103cbf7650a41485bf7550a41485bd7550a4147ebf6550a4147ebd6550a410079f7350a4138dbc7350a410079c7350a410059c7350a41006bd6350a4100dbf7250a4100faf7250a4103ebe6250a41007ae6250a4103eae6250a41007ad6250a4103ebc6250a41005bf7150a41007b77150a41007b47150a4100ebe6150a4100fb66150a41235bc7050a41044ff76cca41004fe76cca41004fd76cca4138dbf74cca4100dbc74cca4103cff768ca41004fe768ca41004fd768ca4100dbe748ca41005bd748ca41046de638ca41006dd638ca411b79c438ca41007ad428ca41004ff764ca41004fd764ca41004fc764ca41005bf744ca4100dbc744ca41007ad424ca4103cff760ca41004fe760ca41
  | 37 => 0x85322d6ec3218532006f65118532006f5511853201cfe7018532004fd7018532006bf64d8132006bc64d8132004ff75d8132014fe75d8132004fd75d8132014fc75d813200cfe74d8132004fd74d813200cfc74d8132006de53d8132006dd53d8132006ee42d8132006ed42d81322eeef32d81322eeec32d8132004fe71d8132004fd71d81321a5be7498132005bd7498132006bf6498132006bc6498132006fb60981320057f75581321ad7c7558132005bf74581321a5bc7458132006bf6458132006bc6458132005f77158132005f47158132006bf6418132006bc641813201efa6018132006f960181320067f74594320067e74594320067d74594320067c74594320467f73594320467e73594320467d73594320467c73594320467f43594320065f43594320467e43594320467d43594320467c43594320465c435943203e7f725943203e7e725943203e7d725943203e7c725943203e7f425943203e7e425943203e7d425943203e7c425943203e7f325943203e5f325943203e7e325943203e7d325943203e5d325943203e7c32594320067f71594320067e71594320067d71594320067c71594320067f41594320067c41594320467f31594320467e31594320467d31594320467c315943203e7f215943203e7e215943203e7d215943203e7c215943203e6c21594320067f70594320067e70594320067d70594320067c70594320067f40594320067c40594320467f30594320467e30594320467d30594320467c305943203e7f205943203e6f205943203e7e205943203e7d205943203e7c2059432004ff7559032014fe7559032004fd7559032014fc755903203cff745903203ebf7459032006bf5459032196be5459032006bd5459032196bc5459032044fe7359032044fc7359032046dc7359032044dc7359032196df4359032046be4359032046bc4359032046dc435903203cfe725903203cfc725903203ebe425903203ebc425903203eee3259032046ed3259032004ff7159032004fc7159032196bf4159032196bc415903203eec2159032004ff705903201cfc7059032196bf4059032196bc405903203eef2059032006bf7559032006be7559032006bd7559032006bc7559032046bf73590321969f7359032046be7359032046bd7359032046bc73590320469c7359032046bf5359032046be5359032046bd5359032046bc535903203ebf725903203ebe725903203ebd725903203ebc725903203ebf525903203ebe525903203ebd525903203ebc525903203ebf325903203ebe325903203eae325903203ebd3259032046ad325903203ebc3259032006bf7159032006be7159032006bd7159032006bc7159032006bf5159032006be5159032006bd5159032006bc5159032046bf3159032046be3159032046bd3159032046b
  | 38 => 0x6bd75d9132006bc75d913231ebf73d91324a6be73d9132006bd73d91324a6bc73d9132006bf53d91324a6be53d9132006bd53d91324a6bc53d91324a6bf72d913231ebe72d9132006bd72d913231ebc72d9132006bf52d913231ebe52d9132006bd52d913231ebc52d91324a6bf32d913231ebe32d913231ebc32d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006be51d9132006bd51d9132006bc51d91324a6bf31d91324a6bc31d913231ebf21d913231ebc21d9132006bf70d9132006be70d9132006bd70d9132006bc70d9132006bf50d9132006be50d9132006bd50d9132006bc50d91324a6bf30d91324a6bc30d913231ebf20d913231ebc20d91321a6bc6459132004ff7559132014fe7559132004fd7559132014fc75591321a4ff7459132006bf74591321b4ff7359132006df73591321b4df73591321c4ff7259132006ef7259132004ff7159132004fc7159132004ff705913201cfc7059132005be76191321a6be7619132004be7619132006bf6519132006be6519132006bd6519132006bc65191324bebf63191324be9f63191320079e53191320079d53191321a7ad72191324b6bf62191324b7af32191324bf9e32191324bf9c32191324b7ac321913203cfc7650d32006bf6450d3200ebc6450d32005ef7250d3203dec7250d32005ee769093203eee76909321a5ed7490932007af649093200eee649093200eec64909321a7ac649093200eac6490932045ee739093203dec739093203eef639093203fcf63909324afce53909324afcd53909324a7ae43909324a7ac439093200cff76509321a4fd7650932044fc7650932006bf645093200ebc6450932005df7350932045dc735093203fac4250932045ec765093200eec7650932044ec765093203def745093203faf7450932007af645093200eee645093200eec64509321a7ac645093200eac64509321a7ae545093249fad5450932007cf7350932045ee7350932045ec7350932007cc7350932045cc735093203eef635093203fcf635093249fce535093249fcd53509321a7af4350932007ad43509321a7ac41509321a7af4050932006bf64d8532006bc64d8532004ff75d8532014fe75d8532004fd75d8532014fc75d853200cfe74d8532004fd74d853200cfc74d8532006f651d8532006f551d853201cfe70d8532004fd70d85321ad7e75985320057d75985321a5be7498532005bd7498532006bf6498532006bc6498532006f76198532005bf74585321a5bc7458532006bf6458532006bc6458532006bf6418532006bc6418532006f56118532004ff7518532014fe7518532004fd7518532014fc751853200cfe7418532004fd741853200cfc7418532006de5318532006dd5318532006ee4218532006ed42185322d6ef321
  | 39 => 0xc7558732004ff7458732006bf7458732004bf745873200cfe745873200cfc7458732006bc745873200cbc745873203cfc7358732046f77158732046f73158732046f43158732004ff705873201cfc7058732004ff7558332014fe7558332004fd7558332014fc7558332004ff745833200cfe745833200cfc745833203cfc7358332046de5358332006dd5358332004ff7158332004fc7158332046fb7058332046fb3058332046f83058332004ff7559232014fe7559232004fd7559232014fc755923203ebf74592321b6be5459232006bd54592321b6df73592321b6bf43592321b6df43592321b6dc435923203cfc725923203ebe425923203ebc4259232004ff7159232004fc71592321b6bc4159232004ff705923201cfc70592321b6bf405923200cff7650e3203cfc7650e3200ebe6450e32006bd6450e324cddf7350e320479c4350e32005ef7250e3203dec7250e3203def7650a32196ef7650a3203faf7450a3203faf6450a3200eee6450a3203eec6450a3203fac6450a3203eac6450a321b7ae5450a324c7ad5450a321b7cf7350a32045ee7350a32045ec7350a32007cc7350a32045cc7350a321b7af4350a321b7cf4350a321b78f4350a32007ad4350a321b7cc4350a321b7ac4150a321b7af4050a32004ff7598632014fe75986320067e75986320147e7598632004fd75986320067d75986320047d7598632014fc759863200cfe7498632004fd749863200cfc749863203cfe729863203eee4298632006ed4298632246ef329863203eec329863203ef6719863203ef7219863203ef4219863201cfe7098632004fd7098632004ff7558632014fe7558632004fd7558632014fc7558632004ff745863200cfe745863200cfc745863203cfc725863203ef7715863203ef7215863203ef42158632004ff705863201cfc7058632004ff75582320067f75582320047f7558232014fe7558232004fd7558232014fc75582320067c75582320147c7558232004ff745823200cfe745823200cfc745823203cfc725823203eee4258232006ed4258232256ef325823203eec3258232004ff7158232004fc715823203efb705823203efb205823203ef8205823200cfe76d91321a6be64d9132004ff75d9132014fe75d9132004fd75d9132014fc75d9132006bf54d91321a6be54d9132006bd54d91321a6bc54d913203cfd73d91321a6bf43d9132044fd72d91321a6bf42d9132004fe71d9132004fd71d91321a6bf41d91321a6bc41d913201cfe70d9132004fd70d91321a6bf40d91321a6bc40d91321a5be76d913200cbe76d9132006bf65d9132006be65d9132006bd65d9132006bc65d91320079e53d91320079d53d91324a7af72d91324a7af32d913231f9e32d913231f9c32d91324a7ac32d9132006bf75d9132006be75d9132
  | 40 => 0x8d42046dc7118d42006df5118d42006de5118d42006dd5118d42006dc5118d42196df4118d42196de4118d42196dd4118d42196dc4118d421969c4118d424bedf2118d424bedc2118d42046df7018d42046de7018d42046dd7018d42046dc7018d42006df5018d42006de5018d42006dd5018d42006dc5018d42196df4018d421969f4018d42196de4018d42196dd4018d42196dc4018d424bedf2018d424bedc2018d4203cbc7650d424d5bf7550d424d5bd7550d4200dbf7350d4200f9f7350d420079f6350d42046be6350d42046bc6350d420079c6350d420469c6350d42007af7250d4203dbe7250d4203dbc7250d42007ac7250d4203dac7250d4200ebf6250d4200faf6250d42005bc7150d42005bf7050d42006df63d8542006dc63d8542137ac42d8542004ff75d8542014fe75d8542004fd75d8542014fc75d854203cfd74d8542044fe73d8542004fd73d8542136ed72d8542006f651d8542006f551d8542136f641d8542136bc41d854201cfe70d8542004fd70d8542136bf40d85421d57e75985420057d7598542005de7398542005dd7398542006df6398542006dc639854212fac4298542006f76198542005df7358542005dc7358542006df6358542006dc635854211fac4258542006df6318542006dc6318542107ac4218542006f56118542004ff7518542014fe7518542004fd7518542014fc751854203cfd7418542106be5418542006bd5418542044fe7318542004fd7318542006f65118542006f55118542106f5411854201cfe7018542004fd7018542006df63d8142006dc63d81420a7ac42d8142004ff75d8142014fe75d8142004fd75d8142014fc75d814203cfd74d81420a6be54d8142006bd54d8142044fe73d8142004fd73d8142004fe71d8142004fd71d81420a6fa40d8142005de7398142005dd7398142006df6398142006dc6398142097ac4298142006fb60981420057f75581421d57c7558142005df7358142005dc7358142006df6358142006dc6358142087ac4258142005f77158142005f47158142006df6318142006dc6318142077ac421814201efa6018142006f96018142004ff7559332014fe7559332004fd7559332014fc7559332046bf745933203cfc7359332046be4359332046bc43593321c6bf4259332046ee3259332046ed3259332004ff7159332004fc7159332004ff705933201cfc705933200cff7650b32044fc7650b3200ebe6450b32006bd6450b32005df7350b32045dc7350b3203fac4250b32004ff7598732014fe7598732004fd7598732014fc759873200cfe7498732004fd749873200cfc749873203cfe7398732046de5398732006dd5398732046f67198732046f73198732046f4319873201cfe7098732004fd7098732004ff7558732014fe7558732004fd7558732014f
  | 41 => 0x1cfc705864203eef2058642004ff75582420067f75582420047f7558242014fe7558242004fd7558242014fc75582420067c75582420147c7558242004ff7358242044fc7358242006be4358242086bc435824203cfc725824203ebf425824203ebd4258242004ff7158242004fc715824203efb7058242086fa405824203efb205824203ef820582421b7ac42d8d42004ff75d8d42014fe75d8d42004fd75d8d42014fc75d8d4203cfd74d8d42006df53d8d42006de53d8d42006dd53d8d42006dc53d8d421b6de43d8d421b6dd43d8d42004fe71d8d42004fd71d8d4201cfe70d8d42004fd70d8d42006df65d8d42006de65d8d42006dd65d8d42006dc65d8d424cf9f74d8d421b79c74d8d421b79e54d8d420079d54d8d421b7cf72d8d421b7cf42d8d424cf9e42d8d424cf9c42d8d421b7cc42d8d421b78c42d8d421b79c41d8d421b79f40d8d42006df75d8d42006de75d8d42006dd75d8d42006dc75d8d424cedf74d8d421b6de74d8d421b6dc74d8d421b6df54d8d421b6de54d8d421b6dd54d8d421b6dc54d8d421b6df72d8d424cede72d8d421b6dd72d8d424cedc72d8d42006df52d8d424cede52d8d42006dd52d8d424cedc52d8d421b6df42d8d424cede42d8d424cedc42d8d42006df71d8d42006de71d8d42006dd71d8d42006dc71d8d42006df51d8d42006de51d8d42006dd51d8d42006dc51d8d421b6df41d8d421b6de41d8d421b6dd41d8d421b6dc41d8d424cedf21d8d424cedc21d8d42006df70d8d42006de70d8d42006dd70d8d42006dc70d8d42006df50d8d42006de50d8d42006dd50d8d42006dc50d8d421b6df40d8d421b6de40d8d421b6dd40d8d421b6dc40d8d424cedf20d8d424cedc20d8d4231ebf6498d42006df6398d421a5ed7298d421c7ac4298d421c5ef7258d421a7ac4258d421d57e7518d420057d7518d424bebf6418d42046de6318d42006dd6318d42197ac4218d421b5de7618d42006de7618d420075e7518d420075d7518d42006df6518d42006de6518d42006dd6518d42006dc6518d421979e7418d420079d7418d421979e5418d420079d5418d42197cd7218d42197cf4218d424bf9e4218d424bf9c4218d42197cc4218d421978c4218d421979c4118d421979f4018d42046df7518d42046de7518d420465e7518d42046dd7518d420465d7518d42046dc7518d42046df7418d42046de7418d420469e7418d42046dc7418d42196df5418d42196de5418d421969e5418d42196dd5418d420069d5418d42196dc5418d42046df7218d42046de7218d42046dd7218d42046cd7218d42046dc7218d42006df5218d424bede5218d42006dd5218d424bedc5218d42196df4218d424bede4218d424be9e4218d42196dd4218d424bedc4218d424be9c4218d42046df7118d42046de7118d42046dd711
  | 42 => 0xf725864303cfc7258643006ec725864303cec7258643046f7715864315ef6415864315ebc4158643046f73158643046f43158643004ff705864301cfc705864315ebf4058643004ff7558243014fe7558243004fd7558243014fc75582430c6be5458243006bd5458243044fc7358243004ff725824303cfc7258243004ff7158243004fc7158243046fb70582430c6fa4058243046fb3058243046f83058243004ff75d8943014fe75d8943004fd75d8943014fc75d8943044fd74d8943006ef52d8943006ec52d89431c6ee42d8943004fe71d8943004fd71d894301cfe70d8943004fd70d89434cedf6398943006ef629894331ebf64189434cedf631894303eee6218943006ed6218943004ff75d8543014fe75d8543004fd75d8543014fc75d8543044fd74d854303cfe72d8543004fd72d8543176f641d854301cfe70d8543004fd70d8543006f76198543005ef7258543005ec72585431e57e75185430057d7518543006f56118543004ff7518543014fe75185430067e75185430147e7518543004fd75185430067d75185430047d7518543014fc7518543044fd741854345ebe431854345ebc431854303cfe7218543004fd7218543146bf4218543146f5411854301cfe7018543004fd70185431e57e75d81430057d75d8143004ff75d8143014fe75d81430067e75d81430147e75d8143004fd75d81430067d75d81430047d75d8143014fc75d8143044fd74d81434e6be43d81434e6bc43d814303cfe72d8143004fd72d81430e6bf42d8143004fe71d8143004fd71d81430e6fa40d8143005ee7298143005ed7298143006fb609814301efa6018143006f96018143004ff7558e42014fe7558e42004fd7558e42014fc7558e4203edf7358e42006de5358e42006dd5358e421a6de4358e421a6dd4358e424a6bc4358e4203cfc7258e4203ebf4258e4203ebd4258e4203ede3258e4203edc3258e42004ff7158e42004fc7158e42004ff7058e4201cfc7058e4231ebf6590e424debd6590e4200dbe7390e4200f9e7390e4231ebf6390e4231f9e6390e424a6bd6390e4231f9d6390e4231fae7290e4231dbd7290e424a7ad7290e4200ebe6290e4200fae6290e4231fae3290e42004ff7598642014fe75986420067e75986420147e7598642004fd75986420067d75986420047d7598642014fc7598642044fe7398642004fd7398642006be439864212ebc439864203cfe729864203ebf429864203ebd429864203ef6719864212ef5419864203ef7219864203ef4219864201cfe7098642004fd7098642004ff7558642014fe7558642004fd7558642014fc7558642004ff7358642044fc735864203cfc725864203eec725864203cec725864203ef7715864211ef6415864203ef7215864203eec215864203ef42158642004ff7058642
  | 43 => 0x2c00000000000014000002000500000000004000001c0080000001000c0010000001010400b000402e00040040060000003c0030038012002c000000000000140020024000000401f001000300080130000002001c00000040010018009001c00200180040078000000000500000000018003002c037000000a002400000280030134002002c0010000005003001c000c02e00100040008003000800500040000004008000000000240020044001003401400100000040009001c01c000000000100000000010002000000000010008003001800b0028000000403100080060028006000400000100020020006003400900180000010001000800100080000030014001003700100020028006000c00600080000000000006401600640040000009003000700040040010004003c000002401e000000f000800e003c00300340040000000003c00a00180030040017000800a0000007001c0010004006000c0000004013000000000000000000010000001100100110044000002800b000c000000c00a000c02300180030004011002000200080010000006003000100000000030002000000b0000000003c003002000f0004002000800d0014002005000000400050000008001000000040030014050001000800040010010002001c0040074006000c002002400100a00050058002000800e003c0020000005000c004000c002004c000000000100000030000000005c000000000d000400a00180000000001000400000000010000001000000c001c00000140060004000001c00100000010014002000000100280030004000000000000040040004000000000d008c00300080100004000001c004001801900380050024000006c0000078006000000a0050002004000100e800c0004000000000000200120004034000000a002000000140300004017002004700000000014000002c000003800800400000000003000000500100090020000004400000a40020004000005400e003000c00000070004000003000400000000108002000000100080060000001001800e0000007004ff7558a43014fe7558a43004fd7558a43014fc7558a431a6be5458a43006bd5458a43044fc7358a43046bf4358a43046bd4358a43046ef7258a431a6ee4258a4331ebc4258a43046ef3258a43046ec3258a43004ff7158a43004fc7158a431a6bc4158a43004ff7058a4301cfc7058a431a6bf4058a43004ff7598643014fe7598643004fd7598643014fc759864316ebe5498643006bd5498643044fe739864303cfe7298643004fd7298643046f6719864316ef54198643046f73198643046f4319864301cfe7098643004fd7098643004ff7558643014fe7558643004fd7558643014fc7558643044fc7358643004ff7258643006ef7258643004e
  | 44 => 0x6c003000800100000000020000000400b0000002005000100040190000000002c00000340000000000002000600000010004008008c0060000002000800c000000c002c001001c0030000000005000200340150018012000800c000000200040090004005000002200140010000005000c000001c012000000e003c0080004001000000e00080000024001005c0190008000000c0040000011000000a004c01000080080018004000c002003400700540030010001000c0040000000001401a003400f0000001001405d007000100100010004007000400b0000003000400d00040020000033000400500080000010007001000000180190004005001c00a00000070008023000800000140420014001000401700380000038005000000f0048000000400100000020034000005000e002c00300040050014000003c00e0024000000c000000400000040220010003000c005000800100d000f0008016000400200000000004000000800000040000000002000c0350004007000c032000000500000060018011005400400040010018000001801b006000a0020002003800000200000014000000000100040010060005000000a0004002000800c000001700080080014000000001700000030000000000800000080050018018000c000000001a002403400040010020008005800700100070020001000801d000c00b00040010000023001c00c0000007001400600600350004004003000100100070010000001c0000000003003c00d0010014000c001000000900300010008000000800100000030014001000800100100000008007000000a0018000001800f0004003000800100100040018007000800000080000030009001c005003400600040000008007000000300040020028008000800400040000000002004c005001000300100000008002002400900000030010000000c00e0000000000000900140010044000000800000000000000006001c00f0000001005000100140010000004000003d000400600280000000000000c000001c004000c003005c0070000005000400400100010004009000c0010000000000c00e0000007003800900100000008005001c00400040010020002002800400040010008000000400100040090034002002c01e0004001001800d00100080010010000c000002c00b002000f001000000080000008019003c033000000000000010024008003000b0008003000c002000c00900040060000000002c0000000000000c00f0014002003002800180070000017004400400000150004002003001300540020014003002000100000010018001001c01f00280000010001009c001000400300040030014002000800000100080000002000c000000402300000000050002000800100000000020005
  | 45 => 0x9003c0000008001000c000003c000002c0000034000000c001000800000000050014008002801f000c00500440070018000000800b00000350000002000400a0008031000c0110010010002801e00180000054000003400d001c01b0004000000c0000000007000c001001801a000c00000100020000021002000c002800100000040000005001c00100000120014000001c00300180010020000000c0050020002000400500080020014001000000000a0004000000700040040000000002800000400060028000001c0000074002004c0090000002001c0030040000000400200200150000000002400000040050000000000c00200000000008000001000e000c013001c007000c0000024000000000e002000200100020038010000c0180020000001800200000010014004000000400000070028001000400000040030004011000000e0008002000800000040020010008003800000d801000ac00300000050000003001c00000080020020001002c00700140000000013001800000080000000022003800100100000010001001000000000000008007000800900640030000000001000200280010098006000000000040090024001001800000540190000006000c001001c0070000009001c008000c00000080050004006001000100300010010001000800700400000004002001000200000070004008000000300700130004003000c009000402b000000200180070010000000c00200800000018000003c005000c00000340030014001008800200a00170014001006801000040140004001004c001000400b00480030000016009800d004c02d000000300100000064005000400a002c008001c0000168005002800100000060004003002000c000000100200000044000003c025000c000001800800000010008001000001f00000030000000004400800000050018011000c00b0054001001400f00000050000006000000300440000004002002000300140130038005000c00300100050000000000800000780030000003000801c0008001001c0220000006000c000002800000700000040001000c002000001700240040000002003c00500200010070001002c004000000d0008005000400200340060048003004000000240040000000000c0020050000001400500340140004001001000500f800000600120000018000c004000001a00280060024009000001e002c014000800c00540010058023000001200140050004000004c00200340000020012001c00000080030008005000c0060024003000800b006c0000074001000000000140030000004001000000080030008001000000600180020008000003000600ac0060004000003000000300010024000004000400480020028002000000200000040004002003000c002
  | 46 => 0x4003001000100080030000006009c00700000050004000001c00800200030004003003000100280040004000006000500140030000004002000b0004002006800300040010048000000000e001800a000c0010000002000c0050000000001400900000000000001000000100080110004003003800200000000020001003c00100000080004002001400a00180000008001007c004001c00500000380000000001000500140000004000000000a000c0070018002000000a001400300100050014004000000101200150000002000001e000400100040020004001006000f0000000001000300fc00100540000024000001c00600040100020014000000200080010004012000000200240010000003001400a000c0010004003000c0030058004003805d003000a0058004006400100000060018002004002500400000008000000c00d00180010010009000c0080000002003801000000010018000000c0030028001000000f002400900040000040013000000100040060010004000800600440000040000008c0080010000000000b001004800040000024001000c00200080030000001000c001005000001840000000001000000e0014005003800800800050000000001000f019c0030058000007c0100004000007c00500200060028003000c0020004000001c00000080000028000000000300380230018004004c0060048004000000000640000020004005c006001c00d002000400240030004000000800000100000004002000000f000000e0024006000c004000000800140010014001001c002001c00300000030024004000405a00040000000001000400b0008001000001100080030024000000402b000000100240020008004000000500000080000000000800b0008000004800d00000000000007000401b00100010000000000c00000000050054000000000000040000030001000c0000038000000000c0004000000c001007801a00000060010005009c00000200010008004000402500400040000000000400d0010044001000500140010044009001400b008c001002c00e00100020000002000c00000000000020002006800400580030010001000c01700000000038006002c00300040010004000000000600100090000016000c003000000700a80000000002001000900bc00400000080018010000c00200240020064002001000000240030018002001400000140040000000000000200040030018000000000d001402d00d4005003400000480000020000001c0000008002001c0010020009000001e001000200740140010017001000a000000e00000060014000001c007000800100000000004007000c00000000010008000003400000200000048000007000100980000018007000000300000000060004000800
  | 47 => 0x3e5270000a1d0000000000051c05160001cd8294328e6940000000000036b30d80000d00000034811930009e280007b821661b9955600000000588236b04950a8af3092270acc4bf794b03192a547f1829c0d08000ddc101400021d434e00006310fee5ce000000000000000000b518fb20000000655000000000001558090805a4822ef0cd400000000000974c02984800014e8df712c81048182941ac50000077887283f40d6a83ab358fb4cf280009a9ac0800006e21860f2c05b187838e3832cdb08484c03628592811e000349c45e060a7c98000df7af04000374ce06000000038528bf15603eb00b2cfd8c563830a6c46ab8aebb691c2933082e70c0178a33299cb8c8af6e5a02a8b4624da8511b826ab0736c0cb95a6a1800000000000000000a58a248219a64009aab9ab5b800000011dc50d9226313ae443d920d6e091942000259e260000000000000000000000331e5411d9c254a7ae33e040a0000e968ab2eac154094ccb937ecd96ae0cde38af8dcba8badf811526a5254c3e40dbec12000023a215c4d993f0acaa3f0a9a8758d5f24b60ec2fbc4dba484b61000083d9b1c2fd351aaaf252e000000079e2932ab3800091e9c9a000271200002f400929a897c800080528a4453137600027d2aa5a3587119f9ab731c5669f14d44578e300000000657a00612e2772a288ebe7daa15879805b846c9f44000000087a9ac40003104409b76000028ea7c50ab4d6e9de2c8faeb6d36317822d9274a6a8592908b5463d09ca87558326ad2853000180040008000000c0020020012006801200840040010002001c00800400100008006000c000000800200040020000004000c01400140000030002001000500040000004000001c000000800e011000400000030028000002c0010000009000401e0000007003400000000020024004000400e0028009000c0000000015001c00000040010008007001000f00040020010002000400c00000050000000000c00000000100000005000000000800030000002000400300200020008003000c00400880010008001000800b002801d003800100000100010006000c0040020000000c000001c0120000000018400e000c00200500000004067000400b000000a005c0060000001003800000300010000004000c000002c004004401200240110054000003c007000c000003c0000000001013805a0028020001c013000400800780010024005001c003000c002005400200000020034000000800400a40010000003000000f000c0030048000000000000100010000000000c000000002100100320054004001800c001c010000800000000010008013004c0050008000000c00500080000018025000400000040060018014002c001000000000040000000003004800000300140020000000002100
  | 48 => 0x60000dda00005e6157a82d80009568000402a86884b0e4a000014a6fe000000007944670000688182e0000000a1b0000000078000026780001b6c0002cfa0d780009f1b060000188cbb280006ab93e2000098c000273095800009c1a462bad00000002b8a0001e9a0002ebc2ba0000000385cbc21786803877abc6800013cae80540000061394e6273009648b80004452fb2e54ae9400038c6737800003a1c1800001a400000000000000443b2d40001d16d12269c9bb8fd42b39bc8c6ea5fc29f9606d54b3b6c9a0f3eda8242c29e93aa6072a2e0c41e726f4b34489081ec27cb2561d72f5046d8458898a3749e1b34800000005dd8b740000000e45b5c400038bc218227c109af58de492026250b4c7430c6055b88c8c2caa3438d80000001a0e92937e6656a1de4208016cb40000000000000036520000c8600012fe533998c595b2f424a0000a200000d0c990e0000d5ac19910c70101180ef0edade22e28c869d8e919800013b33a4ade2fe82cc06b0ca4212ec62a21800025ca63f80000729146a0e239e327800000000008f6b470000059cd82800000000005e7b100cbe949614e836a5870f8803c89aab6712ee52cb79c4c313faa4e800000039020002a4a000014895520bea7900009490000000363c0680fa48f6046c6afb8843638000849ac00d2e13ae00037187090c2e89d8000000000000016eca60800037426702fe807add00000000223493b90fe8a989941a62f20be180006522f563ae89de01f8dcc6cb05ac77180000000000a51a49635e81ae00007ee86412bc00036fca07207c00032c0a65166aa3d290838b0000da9800657e91f63cbb33084680000c0b42432b334c2d79a3ed05000000011fa0000508c50a10ec7103c48840b2c660a9f800034de680160ead621d200000001b02f7c95c8000697000042a0000789343c00000000001016bb509d864b280881c0984ce702ead3807d46fd20dcd0da056725a5f8d6000008740f14d13aab2dad18be4bc83707809fd898f04a600026d80001f66c0fa37c4ca80000000000aa918aa00022780000638d7000000001f7c4e9b0242f5824e4afb32e95216e6dea0d8c8b5148800033d00299ab4607a3a4372800085e00b800017a29db843800000005d9b3aa0000842c78a9222d1800002d37b000000000000000000000085e873cd6500000003262418203e984800019fb07a000145cdaead8a7b19f50163aeea7ceaee6d10182cd429802c652c4a00023f49640cf63459fbcd2c80000000000000000000020d000035cc000165a33b861635900304e231c086d000052080004fbb5b665e9d9634c89b236d9c880001b4000f9f16117859013783fc01f13ecbd88f380001ac0425871ab149e128b2355ca86000000034dc000196028ea8fa8a614ac0001b46c7d38a296623e4cac99
  | 49 => 0xc702b48000408932c94806c2a832386c7a80000000000000326400000000002df6000052e0003666cb7800028594e20000000a7ea72000033d4c478a4c7353920000151209f00000010000b96800000014161010ee06c28000a271c1a0001daa66d0242000000055fa3c421c32aa00022a26a8000055d00003adada47cc3170a038aeaccfb44a1fc80000001a4814800001a2000000000004660000d80390000002fc000179c4c10682837af4a6ee2742000000005a2f6e0000000000250a000000086aa708c38971c66d99ac9ea20ca5ee9fa625381120b1804452b960202a22a02c30000b552336000378028325d00001b5a3f000000000000ae63528cd61f885c616580002806000100e065ac7c27936ac907278e06e10d8cfe0db200011cae431f046489bc4000046e03700005a40000a0c2e100e0258a0002206c16000042300000002dfe000000000000000000000578000000000007a3b0060001e960c49dd200000000002c8600002b2e6600005518eee000051a21b14d8de78e6a5440000500800058ab94c0001fe6000230cb7b00000001a74508ae9200000000001f0c45400000001a5200013288061d7e2ae00000000c1409980001b38e5aba301028ef8000da71d5492a17bc0388000c5f017200000740001540000240e58b1f3c36780007c2980c4fcb5883bab92cca91d2a44d049e88ca8e257b9d8c3db0b0214c91e07332a84b1185942fc855c9b8959c634944aa7501e4a7b8672a648f9269614c684782e47410bce6cd849a873378c6b2a0f8b579e445c2130e483b43ed21000000000000000000d52800000019a463a00001b51846aea1170aeba8b400000000d2823c07cad5800000000002c944b89c0c00024428e4b1525e48f22000012207303de9dd95de0002632128000068c907ccee17324d68dc4a658070de92cde4b297f20dba42400000003970e5200020220003660158a3402d739a622601b68d88dbc9f01c5c8b40000000000000038480000000738b118000009826e8eac00000002d89c522c9ab3400008ea0003128ad90000c520000140359898000004b18f5a8cc33c4e6a1c981ae0d2c5b78d2273380000000000000000093700009cb0000b2f014088b0000000270c0000d4eabe12e043b12ec27c028444207ae00027660000000000037e8068000a94b230cec373871b1f7e15a398a2af8880000329c07380009d2b4d2c77a294bee2c3e2698c3ed708000a460000bbb8000c12913831796a63408000c559cee000171200011200248c80a4a384c1878a70ab600000980c0411eb0265a1217e4f41a8c7770000c0d80002110b7e0002d92c208000d7c122498b83b626d2516a3388109f6a58000006424de8a980001444c6b8cec00023a0c690000272800070c80004e523968450fe2ba084d20002dd4772a14c4
  | 50 => 0x1c00000427199229d2156000000009500ae9ca8000000041c7bb08a800000005d088949691080b9f000009780000002ed600039647a40a7cd6094347129946c351be2633a54019d1d068daaf2c0f1976cd9f0798e3428e0aef048843b8f0e3b32e0859f8630dca81e669caa5e00027b88219d68b060efa069a8d40002c8e3828000506aa764f98f5ee1d1bfa52993e4757abdc8a2000000000000001008d9880000001b589469aec03580006d72a909f4000000000005878ffe1142d245e9a1fa4e60ae60000fdac6a2f06552aefaabd8690688ab929af80000002148af100002a0959e0c7a5d4701a174b6e240c79c087424b8e181d0131a00000000001074000033483100005d107b4000000000018dc00000000f40000b27ae2642e1336ce8985e46eb8706f986d880100fc0000000b7204626deb4581a3800059780007b8800000000008c025a2d33025046922b8107b802daf00005ab946c9588ef6c6f917466c1e66c2f839a042a59c4a39dce515b28ad772af20000000d531588000000059e8000723125a34738d6d3e8e7057d8a3e2172ca000018920000000b760000cfc108e0000000961b73a568a06000000002f7b2ac0002f3e0002e1800000002080000cad000079000000001e92e1ca7f0bfd210a70229240332fcc6b4935650c3356b828d2000014aa5d1805e93c0e8e44f9d62417800072b80000e702ba000392eccd26e868eae906381188af3b1124ff12acc8290367d3856ce4c013067d31e0e1b1c2acea006a34fb69a686929200014f2e0f33be0002d327b080000000000000000000027708b12bc2dffaca646691c400000100000d40c2ab678be10cd2abd2f5a58500000001f9c0000000aa225ea00010dc2660746b9520983b502d671680000001f1200005b60000000ddc80000000000d5e00008a00e842e880000000000abb9c422e6b184626b1a299d0deab3d000000027e292b8000d6993dc0000000d870e6e0002b8025c1e3e00025c23dfb8c40000000495338e674096a8e206e8a9d1788be99ffc65ab3d8a90ace4ad41106d9e801a6e73810ca5a8142c727460000376adb80008c4a6f49ef8c2638820fec55059ecdd192ea890a44724a39414f20726851c025af83843a18252912831a9358982c89a7aaa152e16ab80850000227247fb252c8930ce00284d806119e485a2076b6380008619dd4a7188d855f000000027c824f80009b2800033a2d3868a8000000000016c000000000000002bd813e00000000000e1618203fdac0290bb3bc530b4127ed1f962e31c3e36206eec5002220002f6c0002622ceca152b9d8000bf3803a9c69df61a336182668304658986c44a8f66dc91e28d171d48c0b2cb400034c6be2000045a09789578c4a864961664a95d8bba1cb85cd2c24e4fb456128ac5c47e2fd4142b338beb2
  | 51 => 0xb4667c00000c9e3490d59317ebd727247e3800076b9698000000084600006160000a6e80006480000000233a37d145800016eac9eaf9800000008ec000070ba6aa00003d4a98a27ab07031c6d8a9763dd0000d4d9b2a32ca9f400000007e880000000b52c012ac0000018a00018da9781f0e0002f10c64179000036b62c39e5c8e423bc9943972dc7aaae7a6324c6c001f82b41a1c44b800000022e43ec28ae82e91420002e9c00021547820f508ca37a2bdd94086d3000000000005b4800083a0b12249238a012081e8390c54337178a74700000000000b7e2a9a00000000b9800000004d40000e9e00015aa2f080009450000000000000000000001a3c7f7237e00021022ca8000db9962ed68177e7bd1598d930ada0000000a4426cc000269a3f40000ce0000000000000001d7200000000000000b4727d80000bfc78b90f200000000000000000000057ca99a32f250eae7808c3e3a3d20000000bbd366c0000eca9e1379a00010be948b2a6d0aaac2d8f8000b0f0000d34027037938567b58aa2000000084004fc000325e8c92e14000198aaae2b3e000395eb5eb4c83b714c8bc9804c1239eceae3a53cdf406d0a8c80009d682640b21ad681e80583cda3aa2e190446c300224aa84d09a911da6a117c28cab5745ea00005b51032dd522ec5b38b5831493c23479b8819800007d582d0c0b8d2e9930d0a0000000000134e30c000000024f60003094209b6aa00000007fc0e3e00019e80f9aec4247800000022f67c92a70000000088f8000d2492d469180000001700000172e4dcac720fa20bc00000000000ef48fda446731b8947c421ac00031d80000000e241da01058ffa6698000000000000006f6d79a56a40c00c6173335e92880005f20000000000015922c0000000045b0f56199946a6f38000e0f94860001f1e379888e0000000a4599c4bbd80002d6aec8667800041e1ad400034e44a3000037700000000000829800009fab40cb2a03ca93241858d0000c451acc3f7ace65fd8000d03a092e223570acea68c810a68a04ba402e4f28da8cd0000944147e43817d800019080001ae6a5127a26c19a8807624c6b6c10242ed800020036ae696a93000015dcb86800049212d6135b20262c800018e88c27a2963ebb7226e000166088205a6000028a5f5b4261d41cf80001af4000000091cad9a09689ea990b4aa000198636d2c8c5f420b8836b3de000039ec430258691205c96c2b70b31a7ba24e0062ab40df82e134343b3800000000004341194a39b054000078293eb5ca0002ec200000000000a040001a8233038be66ab2b858e8ef8245293476f149a8713354c9515e8e190000abe8f340000000db30000d4b9d6e42c2d867d814da00000000000fe87280d04b3a8fec7f68000d58001ca10b7480002256704800000000009cf8e90
  | 52 => 0x6000330c78691260ae2cec000234c0ca03ca56812a8e68060c50b0000000044c00012828a105fcb9a9a42338ac90ac81f86e350caa5c419f2a6fb8ee9b988ac3871cc235a1e3a4a001c212004022c8a7405b8800000038b4b8398762021832000136c75a8000b0baf6a00013c60002f9000002300000b205c0819e25500000001be80fa81fc33c80000002c0e50a872818f8000bca18421040000000002e00028c60002f8a00000007481e7625a00008331f544222caebbc00004070000a89800000000000208000000000000000002150000b97000001b0000a0ba3e000038ca32e2e600000000a61213a6fc3640b2c048291d0ffcc7b1a6290ca866d2a235cc36b6c091f3422009b8faaf228b26e9813e0001760b9b0ff00000000d6b8000e6400008dd8a260001778cb10e8ac2f1c7248c83304e686c600003925ef9c80973a2b414a14faafa333adb51a92000395676ca848a6980008f0084a40eb24a2ee000000032da000000019aa72e2f9277a0000000000220a61f854600000008af8368764800000000008f7103e825b65eb900bcc5c5918600019d800026ba0000000c4d00000001ff4cf69efed4500000000f1e06b0220591b03815cb7581d7b28800036944bc000040a800018800009f800003049526a66122a76230529ff9d46e0e09e602f22eaa870f805973196cd9b72c000398200014d27c600007359aa2dfa8ef2680a45899a950eb130eb2b878d443118a4e80d80a2a82a8b0004ac34d1ca9028d4b530831aa8a33295ecb0daad4d9d1c20a9a3364c21ae882960000af4b9125d5000079fb26e193a2b07959890d958d5e36ab97812b00e06ed0596bc8a8c4acc06269b805340002bea00013b22168000091b2bcda2953a98f9ff80001a18af800004d2200ad94292e00007d20000000000072600000006e628100001508c18948ca6337da9ec9e1e9c506da4d78724000244ee5807f024633ac37f230228638b870998fad23800080829e66de0204e1080007628bfe89a9b942f62b488952d00276800006515e6e61829019506ea4008f1a6ef377ee1891ee8da37b247880005daaf3a73a901a2e3ab8206ca3387390a2483b057c5ac28208b0b1e4b42a5acbd90c7ee303646c4e9c6ebce2ec6ba89386d8507aaa7f0c9ce14225a14095ea88d88ca16ea592d6f1aaa0560180a18969c1aeb1f2458a398000141031a0000a8a12b00000e1671a8a32a308000e5bae640000484000000000037d600000000000000000000071c01140000bf600008d4d4100000000000000104c6470000e078e9c000056e00000006d285c00000c247740a7231d9944dd9858234da13469000000000000830ada68b9a9782f98a942bb00000e39b325f4ad26d9f99567d600000000c827deadb41d280000000000d64b58e2bd106600026eae29000024e
  | 53 => 0x121a88032f09dd0000000079294fb680ca7a6180000ba894e0000000057aba10a34800202a0d895b0000000000035563b7b09c0003018000091ab9fa6260002420bdc94149d328709bb000042a932e3f8351839f13dac9c0bf0074098a261838a921955ae398670a32970c0002dde0000000c75897e61ba1980000d280001ae073c14f447929a444a297477ba82a1af8c4c141b48652d1c0e1e413600902898469adee2341e46046a6de0b492b8083b1ce3d636b8000000000020b274d8000914357a82701268be96000ab2816be896aa6fb14640b8ab621d5ad82271a3a25e8289600001549d3800000000002d80c669950720000152097b90c694d37ac481b396cf18fb800024ea0002e4e7a780000000000a008000b5d896200000001f3000000030a40000000bf70000e38a244c90b1bc000000018a804e5ca00000000000bc700005ee37d200022c62a7800000000006ba285e24401a2ce69edca4fad066c8b4a43de923e287a8aae53aaca8538454729aba4136b2fc2ac84f66449ea2c9aa8ac718809c535828894481b448790ca1bc8c109e2141e5e9292646897ae0b1241285c969e58838a824811d4000229600000008fb9e0ed5a168c8c3b89818cb6eea730658cbdafc69c7aa3c00011803e79e007b1142e238943e4b92de232f8a5a0ea1b520000662a6e00000003946a25034031237be6e782ec9ac27a693a23c8e42362aa248b4e00000008280d82000377a4c21fca000000000033986819564c2826867f0151c113a57803d245ae24a7c2a340000d8d29e257d181aa85930a2d02adaa5cabecdca0c4477f207e28236f8a8e8e1045529b04e2a3d645face0bf2370238a9160049257a0c8971a46791e8ad9a4d008522caa2a1d5c4a427c429a278200033cc8132e045709f8000005860001d3ee308000000193274f2f4663e00003570000c468000e320af056126dca540b9686f349ecdb85c47aa06fc0ef85a4d45814ec67b2ba275b0200002052992aff097000008fe8294da21e1ce070f08e33953443904fa7a100000001b5000030c00002824000249a000325cbd52a300000000a378000647b332446b1b681a874e00036221091d900000000c8580000000000cd480000000000a41886400028f25ec133007c38443e31fbe00000286d7b0d2cc5b70c0df341c00025020360000000391e80709fc744042e35b832a62d800069931b2c6029b20001830a430000473b7b8ce22ee05d3289a00000006bf12a22048896a6b0946754ad3c326b7c6000236693d095c95186444b0a21c657332c22084a4c5a1582d0bb7c45b9277c2401c9e565377842e87720001880d911c54000157800000002c630b8cb7327c93c8fbe5d718a63449ab61be155e8fa826203f9b1025f0fba3ca00145381bda0cf905c8d52416a780000474800093e0b1
  | 54 => 0x1ef22da317364256280000000588748800000000002ccb8da00005ea000022a000266ec941d7c00030500c1abb800036b01719da4df22a785788dc2c9ca5fa089971e2dcaa82b9230c8d3135087072c2c98725280002f486f0ac7e1a8000000039760d70b38000236082a0f4859d1542b918f0c3fc80be037aed0b4e91ccb801c2220f1db433c27641ea000087f8000e1fae56bf6b4b4af6881c6cb8b34b3dab8656003dab7f1a540c2335c12600009fa00008c28000b6f8000b5a11bc349014239080000000000a7227ee8b63302085abccb888884a4011c096f00007a9833c01a0000000000000000008d292c400017ec0001eaa3d38000b33822ea4e1e1000000000410000cadaa0000000003bf800000000000000a92316acd8c5b00000000000dd68000000318e00020280003808509a488dc8b53e0000694d5b129690210340000000000000000000000001130235800082a800084e0000bfb8000000316e00000000002a7a33d29d81bf9d82000000050f15b400017fa3e11f2c5001d2cad3232e59a2550df396dc6fb8000611000000017b20000000813b6d60001856000062279780004512c40713819000014747af000040418980003016812b8fc83b91b82ec9cdad1b0000294ac3a14905fecc4312a47a973e7302f0a85a800049c20e600005d4a991666000000000000721b4b720bf41f72000358a0003008b6400000000b7a1328000e1bb07c0000a5c0000c925f30000b3f1ba2ba980000000000ae3173a06328b8a902f0e00033d24e8847860d2bfacc136faa113208000275e1940a020001a7e54a2fe6c7c073476c177ad72114e85018b8dd095a800005ca5b326f8699ab26b5e2ddc8738436dbaaaa8b80970e7930000b74800020e80003e29afa12c890400003f21769b444ac80006bfb01ead10000e0d0f24e500000ad39902670904a9722940d6682684640000628000091d934c20e29da79b06467f430f6000284c168090e000203a385053e00000ee0000000d6d0000000386a5cb000019b056600031dc2bf800093290a41b78a200001cc89eda70a7d48000000360e18182a600000006ac1d668ee2ae615f95fc00019ae0e8315e00000004c90e1291134a239ea8b622fb22a2da00000000ee6d4d0eec000000016f32b000030e05c900000000000e06ad4e6e69bd6dc033f4c812e866bc1810588a47000034ac0002e3ecb320fa1b309a40000000000303038d00007340f2a46497e2000211c879a53a8690000447811000010400141abc1498000000000000026d0d8b059a1430e4ccb606106e0219aa2f8b6cb0789be57e24920002f9c06f05385d021fc1b1231656d87c068400009c08000000000000000002d280006b8800000000005373922bae20827cb800000014caa70000035c3222000288898b3238000000000
  | 55 => 0x4685a20000b94d7ca02e6d22daaa81ac2688a0cb6491800008e00000eb3506a9f27580002e3cd1e25264f027805c10000000362041582bc1ca809e000346a000056a0000000b308fce0000000d49b7aa559b5540000000d2982b60eb8e1a00000000001b923508000000321c4490e64c2798000000000ac710e86cf9f406700ee2000020c0001df28961b18421898e90a80002292fa0000040c61020300b3a1768020b6474d0000697829a0000000000000067e2756000188265489ceb8e00009300ae421a96f4d1a11d6356000009ba1b628a258c71d25661c100001370000ab580006d0a0ac20d000054b0eae34aadf466f15385092ac80000000000107e0000000426b71a3d83608302359c425000054335e2b98878a252b74469c2f165b08cfa60283647feadba0001de623b939000018ea0afad168a68ec8552199cd3b33864281218bcf150600005ce5f82a947d9292ab1826349361b30bf0161a1778e989a600000e880009f597e600039740000c8412280000000ac070e870a71401501c725becf716f0bb79062bd982027e90c16d8da2b26b6380a291ac54deb8e00da32b1e07239107768000c672b188e12ecc7db1e64bed96e83b12ee22b502d86fab78400000002ce8000b729baabf918125cd8000752800000000000002de6000022400009d2000000000000009029f946daa4a60102af0087b9700000000751290e0000000e67a494000000071799be3dc8c1ca96ac14b8486caa303028287288c00019b80c2a13c000106a00000000000000b01000012c00000a5959a47d0000abb000000000004ee83cc53e115800000000000000d3a80000ac13b8bd023f20000000da08000aaf95320061bae49700000000000185245e07580007bf0000a3b1046000216e00007c4a9399dc000000008d0000a8ab41eb7098e6a5f000073d8ba0000273293905ec513800036e2074d6f89504f4b7f4000062c00000000002e8e68e3992e5aacb66640428193193a60985740002c6a0001c2c8590000b51000000000007be2d2005bb0cc3d30c029da80000001a8e5f6b324e412e722030862000326c00007320002b961a19c144a984460cc8000000a88a00000000000000d5dac6ede0a5d682686ec000377c0000000000097ab8900008030a1a1a485f234d1196db0865a9f79c8499da382000226c0d4afaa1eb0de09fe9782a539c7c0352958c6208e07f087a0ba92ca83ef331a097182ac8636d0000123a2b237a69ae0d7813d0084c8e8c8acb0b0f8d030fb6a81146655aa7a000000008bf96ac00002c06a60a3000035d400000000001910000000065dac38c069e2063c30d67d28000c2200002fe38ba4ad00002560c8eb9e93f63f611c6b5ab80cb7a2e6651da43807f95761a68a102a5a71803e8000c5383f6000219c00000002a2a6c6ba280
  | 56 => 0x252d86975edfe214aafd0a547371b6080e000090696fc1f198bc0001e368d10d1402b269676db7fa918273caf89d74cc51756e4521bac31981858907e830180000000bd20001a0a93f21b01c38000c1cb73e0000000081a952ac0b372488916a8f2a15000036b293536580001478a8f800000000003519d2e4378094e2c000000008bc9ec339ec4986f4349b1daccdab0ca15a75448b2c329fa808e022a75202e80e6d4809f8932215a94b103c83c8000366028008ca624e05b1d484c1f220001fbab718490a4115ae35d905060fa968138a2264a7b4eed50a05800004ce0000000d222b0ecfbaabacc9add6000295e1e980002cd8b0605ea57632d0b0a4c48aca8240e92baea1c874a21e8000000040a00000000000c4c91e692f15c000008da40480007ea143ab422d8078e38cc8c600008c996c49beaca45b436240000000000000097b000000015ce0000000b7804320002de46e325de000087653b1a80dbf8000d7f2b043c4280079d156c7fb0d3cca09664bef9100000000052d800000000007663322abf8000c3780002a4329a767939cde19fe2c6e350c0ed245421c80009b20088dd8a6ce0321e808f092622ec2dd0d92b5863de02cc1052858a1f1a9a73812881da28dc32c322e9af166e57415c6bf2a60e48a209ed3d85d60001f98dbd8000477b37ccda00003659c3c0001b76375905a130000053c0000ac40000000359e9e715b200018168ed193812d00000001104af5ab06377a29017d90ea6288000acf2d4059f253619900085ed2a6c8f5257e7fc9472000382803919743a22666b4da79ede5915adc581be21330a2572045ac51250cada06dc9e92fa42d21cb445e8a629bc83744e0382e00020c86e39d18000285c7b207ce2f41b847eb000007a000055880000be8c3881e1b1e0001dec65b0034c48b69e92ab99cd631b70c580678cbe2c2200037d8000287a74207f8000000083394fc00002a4c7e0000c2d8b9836880000001fe4cc72722bc7a5a6000323cdbb0d1a7852c06af192ae7f7800000016920001f78be006b44962a8e98420100000000a0f8608dfc800000000006ae80003b198de982800049aaf7a42b0000d1692de1ed83ee0003360000129400000000001f4200028fc7542dac87d000000000001b5800087735f600000000003320000000015c1ab2b5b0dfa0000c0e7a086a47ac00007780000cba0000244882400022d653fa55200011828782d2879210bc36298860000000000000000000000002e98c1703e400032ae000000041380009f313e80000000bda2d2a00019c89e589ec00028500000000000239c23c80009fd80003ebb8dc4e49236366ada200030ba29a89880000000000373caf40e785f50f127d72ffeb15a4ec00018d8ab1a920e3a80000000000000000052e8ce06aa000012e925024188a65
  | 57 => 0xe50800000000000001714000000073b0cd6ad480000000000000263665f8efc3942332bbe040693fb91820f80000e5307e557000030a17ead2580006278000026a7168c19a300fb219e5ad25e253100006dc90768db243a5db80000002c5aa218b9200026febf0b6c4b5f8e401f80bae217800043512606a5b7e8d44800000018d454aad1ab2f91beded397e0000c6a0c500009a4b42c435b3084b6ab9c31d002c9389980e61026c462a36e9a5282c5dc1a366fcab7600034f0d2007600000166370232c24c8e4ecbb00002458e6cc6d07061f906aa0b8017608499e0a5807480001d3a618b11c201b6a8bac315ab10a5fe20aa05e4da8c2c51522e26530f4a00018c63e717b610a99fc0001a7a3a038de7bb8a124eb267e1523936439afa82b580008983476e01a9907e2b91a9760bc83ea0f46b028356b4890f0227b3e000019c6c4f1e883e998c2000000000000005a88c000291d6c5df028256493408de15304be9aa66bd9936bee9ef2a12b4507b0003620caff807d03b805327340001484bfa8940061aa9ca848000b191dcc00037946c51d14000095a459298a0002c9613300006be00008f40000995800076e9dc453b865e7ee287896100000003924000000062b8000941176452a30709402e78cb18ac494c91364a90486a5ba43671a1a9c153b5e44a60d189e4235600033c0a88b5aca7a38b2c9225b44012f0c3fa997c1890000ad8000045b80004e580000001cf4368000000038ecc8811acdf09b0ec3d38e0cd888e49a236e0d73a6724870ccc72ea8d85a09b289fb1e94b880c8c9ac9970849348249cb2740750000000228a492ab54c3b35e0a973040d2e8000ce9ac1687880000592658d261c367e10fd64fd2ad2c7fb6a2dfc2c7800013ca59cb7ee3a8968e23d8652be3072c373b1660003406056800017b8000dd2abf295d2b9424c37300a7a55c22331a066510ce50e03d82be95965733044b260e623338fc6e20ae5e0cd805aa0f34044e0b0122f6836ccb8312c6d985e400024c21c5a0fce088000307a0687c20000000000041c802a21180004f52b329680c22452954e250ac88b5c000000001ea865380e0003814000000028a800071da6ae86e0e322300000c8c9a6a00000000000000c669fe87428000000000000008283aa000060180000000000afb800000000000000000160000000026820000000000047400019fe88508b40000000389388e76983c22681dc00200000000000016fa2749f380000000e4684fb0c4ac5844875696321bea1beccf000031bae4a00036d249d95e400028fe3ac0ba400037748ea1a260000000501921640e07fe3a932367d300007e7800059e38f067280201501874b2b069c44cab248d6926ea7c368e00000004e3b61249f35ea8b7843e998b48c0bf815c77f8f3a281881818681340002
  | 58 => 0xaa800016d812580008928000398000020594d0000266c6052d88a5080000e080000000e82000246c000314c0000f20000313000036261e1b994000342006c022c2a9148e26b00001ecb51c7d8a43ee180dfeaec0000000199a46100003da00001088f300000000afd877618139482980000bec153e72ca9cea23b116858112c2c200007e41a285f7b1741f6a3488ed9ac29242cd210b05c21612f9a54905525a6a7381e38f8236730fe36424141b2045c9a8a3643e82f027ad04bed17949837a063493108ba7ffb36a2b836c8a9bb3e4955976863c9808b43225e62c2212e52b2f2c8780007669ab82a7028e3588000424000056912f48b80000000399a0000df07348fdc000281e0000baa383a1dab9400002010b280000000000334a0000000000274400000ce24a8000e3d8a4a3c08d1068900000000000b2884e49b4838cc3b8e742a823ae3a6b4f80001fae15830e47a72df0000000000036e4666256e0001c4888e23720000000000397a00019340000000000000000015d28bc8000b4422e89ff05100002890b4f8156c0aa882114a8360c320260000ac2ce48000000188a0000d524c6000000000000003708c742ffc000015e21f3562c90313e0002bb6233affaa91b4fcaff0cc85032ec01c42f32a7d800000022861a990b6a1ba4569b10b4213ab4945478000b87023a90d1bb23c280004bf0fa2cc3a66468b26e4572800056e0f1c46a160868b8000000000000030fc0000000000001e0000f940000000ad0ae3000000000000000000000000009fe01504e08432660b580000cfead34399b6dc110387a00006f00001968000378a7d7879a051800000005d200030ca000118c000157217a00000002f78b58abd406eb4f46328000be3b79852e000000033c20000000746a8f65d39a0835a979ab2c866ec5a81f6000208a9f9913cdf880006a43402bfb055e49e9b6e0002ef21e70000804a4b809317ce4ff974800022d200014a01cfa5c6adf81a8b8db0907ab29ae4ba040078aa9b4645a31a2d98c9097d94ccc07383a4a100006e9133468316c62a100005ae0000000337e00031c6ced00000002400e5624ceace385ea5302f6d409c0a000000000000005e1000000028a6430222e79492388de82aa397a5b2000225cc418000c3a1c8a00038f44a2a768000000023f800000000008888a866688000a4b000027700000000000c1a8a3cd7d32460001f3404aa2ae174000087c0c728be080e59c0668071000000000009820fcc00021f6b8b8000ca805f80581df4322124c0003790809000000038b695f32ce0000e72b65850e33f99e687c8d0c8790038dd38dd86f60e2625dac0ca060d7c6639838e29828c5a1a17000032d60000d50a028000000376e537aba624720d8428a188a8780008293384000000049b35fe27e80003068000
  | 59 => 0x3d4a8e46129bc088800c2dda8a88b7ab260a089172c9690b212a0b1430dac5ed9b830e0000000111127e6330d0edc1271c00004c4d6e0000cd0800000018eed641364c1e36905aa0274bc5142899f194ae542264000224e3789bd4d493306222246e19e9e340000abaad736025fb8ca07ec8d60744a6c05c1adb6352938ca6da5e68e98a785f11404641a5dabf60000000075a0000b1e2408e087ed8198c2c141cad5b1200000000000295c0002860000000089304ee000149e34200009172c9c0000000000281200000000000000000099eac4ad14000000000037a0b3c000000020020ee8000d300dec1e32a92963852c1308f76aab306405f18ec4de22cc4990338e3a28bc0000000b9baaa264f0bc0d819d76b2a8cd0d000000447352c1a0231c72b1d402fb1caa70000c42ada6a802d897215280000002f9400035663c1268e2998000e11800000000000001df80000000144b1b0000388c0000a38000000077a00004f80000257847299229dca998000c5e80aa00003e05cc00000000000000396600030ac0001c7e6502c200000000c85343a282af9296684928ae9ee400021160b782f00000000c11800097c2a8c78b2e9e87601160001b749d7344c00018a436c1cfc00000002c40d867e482ca0000000da90000b4c1fd2e4d24bee3fa9ea1462e06582a182af0208059d8c964c4140e4b98afc339191a27a218e07716cac1a05d8331a91ce13a48ebdd33186f32b461320ca84488cc24e82f361181ce858da6802f535323c1800087b87144c1b3124260bac39d8000a60227000009e27f30000b3cb57e0000000d76a3ba9460000c2d2f3400002c20000000000246a72f0dba10f304c18b8000adf00002103584acb00009f50000cc280002ee80000003980793b2e600011b4985800024b06ae72515028fb2dc093487427b636e2c262ce85a8306ea9c900c5b22ff2b1d0ed85cf3522c7e9a6c2c929f267b346ebb9152e29bab72e1993b68489be077c12b6000251cc229f1c43f2aa68f98358a568ca6000208e8700e8c0000000000065cc7d80000000000d5a8000000000077a8000000332a2e98000000000000000000ba17c096200004152a020000000bd48000d71b2064c78cdabacb0a8c7b8bea723b47ee4a208c7b323e8d22933a4d0860e2900000000000000008dc000263a18a000023980001ef80005758346811300cd7e95500000000c8300002fa2e68000174a0001d7a339906e000000000000000001dc80000e28b3f8000cd68000acb90f6c632b280000000000265c00000003c580000000788d8305580002fe07b48046928000037213c80000000162800000004b60000000000000000000007da000000000001d980000000000d95000019580000ab85c80d30000d3a29669f28000396256c0001e1600000005a5351023e
  | 60 => 0x1a100002dd9d860000c9822682980fc1322cc01bba58416fa00008c60ad141282d08de25903c0c1391d0d2b8000539282800001fac1d15f0ba594180000ee8000384a0001a4ed4e893418021a08c7b7e4da5a728d4aa15e2839b040c80244dd93460649843400019180001804a0117e88cf3538ad7800054580000000000da127f823488a2000108a1849ea07a196280329b02e0137fcc4e07b0520019c2b3230432926fc5acac489f90b821f0a91e6e8293ce659bc6a09935260a227e000000014700000000000d5602eedf3000000cb1ac23316268bd0b502139f3e8c50000676a3febf4972a0000000d87ad1204800563922370442b24e3289256dc1b010ac693de3b929d048309d05119c1e0000396ab3070859509c84f598f66d5ab7a00003e25752646000254240ba430000205400004e641b2f120000d542a680000001dc2a0c9a601fb34d6685b53ccfab34e96ea0940422d5c0000000a3ba9a00000000302b2d2a3a10c200037b6000000000019ba1e596380000000aeb000026c37560d9800000025f44ef12660000ac62f813d823f1a4a036b03a581000c5b800000000d488c21b3847216b6d1d1bb032b892648430a611080007689a76080000062700008ec80000000000000242865e00000002a600001650d368000000000013180000002a2c27d279a7490000000218c4321bca2bc800000005760003096705a75091480000001554d7e158658600002d5387800000004c8071e69e0100bc90f6a000012c0000a80ce3043aa838554c17a21a3080ad800019504d730ea1b8019a45f2a800002efcd6888ae58c190cb0a99fa8b3b8e43d72132dc280000000000db78000ce4299e00000001809c4000000004c7297e26f0000000000000000007b991fce25b8860000542cde80788c833ae86122820002564395a558b9c0000cf9b39400008b079e9ff6cd0392a5fe13cca4495c400008525a024b2d15196e9b083dc6958754ce285f0aed07de66c83184ea3544bbb14409fd0000e1002481f8aa5026db63888f172052283f8bd3310e6e4302201b84207fb97fcb9484300f5b75c63209ae095a4e0cd1a3108e6811c3531c605af2062d9c93140001b7e00002da6baa620c2038a03f495bcb24b2444121fc42f19d845be000024f0000caa2690497aeaa16a370e7652d2edd7b604c3433a0000067605f98e24d626b6ad69d26653b3e26450cd82ac266872912424c9a6ac450079e00000004b00000aaaa0e0d3f80002688e940000000dc509e0000262ab13a794a1c800000027acdddacc88659a686410996b2ead562aaaed8c440908662329237ba48c85b0b9e8f3876e444ac9a1a7a5682068ddadb6172203c23cc3d51b3ca5b193010636ce064877e3c631aa6c82d4231c0c946c92cd01a58944b06a91ab1b383016bab6a2ed1f7
  | 61 => 0x6a1c60000c8a00004ed03a600007642e71e0c60880005a28000000000084daae2000188e00004ae41a32ea00000003a9a47e17d00000000324d6c00003dc00000002b0a3cf0e44d38ad9e2a32c84db2b868d760c3c92b20c0a19337869b9ede86000000000ebc67db7260002614d7a086e1df1e0ac70b55061833e820b067c3bc31621c886ac8a4a29e1ceb62eb1db1e687e09b8c1b1064c0d1fa062d2afc72d8a649ef0e22cd434caca617e4364915c00000000000a5e756000088080000001cb043d07a40c580000001ed400015aca961bde05d0000bdc2a36ac00ae200019580a8800056331026751efa4e108a0779273604c890a81bb4b0b370eb46c23410c6099ceda19924000000000000000002684000344459b0a76000000000034c20000aa6267000000000007198f407e3169600025b68ad8a3630c840e0432630ab91bd055605147ce244c8aa80005641a1200000000002ade83888eccee86a20000344c9629c2ac2190a00000000001d648420000c998000b228000bf100000000000510800061418e4208adae2a3af960002ab41789eeac618000a9231240000000b8d1eb8aff93460000000000147a000101e148a78c0000000a1a8d724812c68bdf80000001bfe2229b1acca0000000137e30ab45200000006e19dbea9107fc80ca0f061a1b260000aeebe78000000000000000000000000000000025bb96ce5898c01d12cccc838f32d43acda4bdb5960e1a6d677599de7f5186430620462b7a162927832e0ceabcab389fe0828ac584803462c9f84f0000140a0002986d6a0b7000000005132ae8891b6dabaf8c50adb26049ceb1e8b4b00b0983105264a2d8c082b65cd05ad4acffb47cc8b0fc40001b1675e388a4d40000870b7520001f4814a85e60000292a1d800000018f4d02234e46388561780000290b746000000067c1c90000000000000000000000c168000459800074c8c0c0002aea000285a000000000005b2cafb6e800000008d1b4285bfb50000000000002bf800002d41f60000000000000017ac00000002f880001252936c269354dbc80000108dae000000000018fc4ae964c9710d8479a000000039880000000b43a5ae0000000937a112000183ab201ea4a1032126b38c420000000000000075c10424212c622cb8da68079ae423c1c5803a9f3677e800067aaf8238107d05460000d778b8aca32df270e0000c2b8000a4280004f10000a86b2ee484a1061771f06bf8aea00e919ee0001644d991f3200023de00033ce000089c00014a433f1774000061c00007f60000000000395c00018360000000000308e00035d0b301ce63e687c8e1f31764dd1000a7b087a747adce563b7bc0000000ac89b684521e04b7e8000123000000011169539964b6f00001ac800005c047c54d800e00000008d09e3061eb66a00
  | 62 => 0x830c787508b3e980a792981800098a0ed20002bb2a5c185a868909209d8762bd0ad4c7b4046a834b8d2beb80003f226f084aa4b0e63296ab68000000026523310df61eea1289fca80c00005b4a6200000000000625a1ec85f31fcda60b9038f037286bb16483a86364b3827211fa76c0000c3a2de10f800003aa45db670b5f10e26ce9750429ab7495100006fd80002310000000196600033d61cbb800cfc800023d000037535a46ea2120dafa034000000000018526a7b71009e00008a72b900000a56092a9a200000000000beea63800000034bc0b71fb0a8e20487940000a0693ea5fd006600008020148000000000072199a8acda6d46d5000000007dc548b2346b41e267dd063c08a24b4dcd9462034355e68d0000cbfa32246b975abaa364828b346478623804b41612a728000c721bb600036685e033fce20000099ea54a986813a71e068aa27857841638d8c3ea4645a210ae1530ceae49a06c85092dc96a37ca00012f8ca001066e2a69e2d587125d62be46b6b8aa92608aa0000f0000000007dda5b80a19af211d8000e510e2e1f295fe798a71031e945003d800004e0faa021aab62af00007ca00008900000494b2a29a8035032ea42611c1bbeb9d000079295520000b1a44400000000000c4280000000dd207799a0d7b0ec228010206bbb6160000a140002da8a852d6661aa35073f8000000000000030e600003783aa9f02491376c4cf005c0003548a7faf2e076800000025dc0000bdca9f8128d2fac285e58000598a9140ff87380511cfa59484666878000a552bbe147b6f03fe145a0cb10dabd1000047600000000f6e0000b6eb522dda00034f200022dc1c3000007810fa4c587b8000003c7402b84a3580000e614a208625cc46c0000d8c00004ba95be3d8a9d2af9a6b40192778bf59fc87aba5309c000001159cc472faa080000752e16800038081eecf2356e04f12340001b348cfa468d8c963c517886824d93707ba354028896f2c8409f681000c073292d2bab80000003750d758000603a2ee4311ac61928300000225048f34d4c57018e6df023e84135b2c3738260000000b3b8ec03598000c210000743b08c4f383d2dcc8000000000000021c612a80005908000a5597260001ef616a870297481365ae8fc21f99ca2c15adc495c1c4479b8aae17e8d94da4aa200e437348fe0dc644e964e524b67666121a682c1490e4e816a19208b2c0f0000cb89e229dfb8f899133820000d748bc2bf054f00000001c100002bba00038360001fea0439dd8939982425821b25180f44106b146b5496eed0e1f1a1e89eba8e3263839a034e3fd055a5e3284e76b00005b6af5ee5f214638787f4dc49f6e000000051219d200026f61dd3198000089200016a40000000000265a0003376e4c80000000000000000034c12400002ac400007
  | 63 => 0xea000014f650c89c008427483558000c72876c97a08782d1208479aa21e000081471318d07538000b41059800022042c0133214d9c821e101d25eaa7b4a758000c1dac7a9979d388eb2ba07d6902c4b32ba2bcc0e7e73c90708891452e4e241e2241ac812f38f244617c67b6a28c13f9368c3c89a8899800035b08361ada49cd8e9752dfd80006eb037a00020f41dc28a00000000000355ac69ae420002e3a0003876a3e12a06a901c00000000086929c0a80000e04a230bd3af183419e3c60f205ad268fe49c9b27625590cc8a9044a922b1360000000000000037cab14000287ee4288b87531e5a78c9e0684428c847c97dc48295a6a21312e3b4139e912243c7952704d9385043c9b14ad0c1c642c1226847b22a8c30800082235d297907d688a80604fe06bc70d2d641cc0000000156800000005e521a80000000ca1b5aa0003192d39aab062a371cc541ade530109ed7b8e06bbfa38e000340a7ac86e4a5e80006f737c000039060000f963e1800000000005e3924e61704e856e800033780000000000c1080000001b640000000000000000000008f88000000000000000000000000b19858c2cf0c7c000389a7a318acaa7800048c1faadb1800051a1c7a883800000023fc59000000000a2ebcab8540000000000000000000000000000d06af0000028d2000187c993b82a5c28000d53954c2162d9876a259403b00000000000c5ca1d69f72e9a0001a8a3160f7ca95a76263580002efabde0002480681300e4ef80000002064000027a53a8000000090c00000009b68000d5c8000d339c28102218a3952cf80000000c731f82000000000019960000208a3c39a20000adc0002b88b2e00009e61d30434874c02811023b586a800016c0000120800019e2df5382cc3c1a4c0f390b4062000026434a00719f2035f8000000000031030140000830790800096a800051b80008199494e2b00009101338bb4aa9876e134acfb0000a8420ae00029640000000000000000013620002aa0248a216a5288863600076d1189924a69570ab717fe9010948b6cac8249e13b049a0d3ab9330027600fe600000006b70000000258272700007ca8aac4880000a712cca0000e3aca500005dcad721511544e2736108d7b6f488ea8340002596b0414be7ad97628350000b8b187000000002df0000bd8107a00014bcb652852b5400d2b40b90e987988492ea478b3502f230d32007f5b2c8a5227602f299cc1fa9302b5d24063e619d6b56b7ba00009662f1389e1272baa90438200ecb442401a05094780004df3370d479972d0618540f212860e2015223eb98e6d3a9de0d5391c5fc1fce5b59f4679f0da8619804a6223108078a20cb0c03fabed164831889ee62e8eb84558da4aa19420576b9542e209c4d1ea3c6ca1252a03e16f6bfd82f846809d47408c6c5
  | 64 => 0x228e6401d605f2921454525087bc080ac749b962daa9bc3f2aeceb8ab4b62e013447af9be40d82846b111ddee69270eb96000061c9e58c5611f006a93a480b12d8000021c6ff0a481900000613000051f00006c4933e000000011a087e0001eca0002d1e1fe896c0000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xce562dc532040011eb0c38a64080031d594714c8100143f42aec19020018be845d832040010ff0cba864080030f991750c8100462f31aea1902007c6e625d432040010ff0eb2864080021f61d650c8100061f3a2ca19020008bf865d0320400187ccaba064080030f595740c8100464f31ae81902007cae625d0320400117f0eb2064080022f61d640c8100061f3aac81902000c3d7559032040018bceab186408003175d5630c8100064f3a2c61902000c9d7458c32040018dceab1064080031b5d5620c810006573a2c41902000cad745883204001972c8b8482080033658d708c41000c5e426ec98820038dc83dd93104001878e8b2a62080ae2f61b744c4100061f32ee89882000c3d65dd131040e393cc7ba262080022fa1d644c4100245e43ac89882000c9f7458d3104001938e8b1a62080031b997724c41000636b2ee49882000cae64dc9310400195ac9b9262081233398f724c41000666b1ee49882000c6e651c931040018daca39262080032b990724c41000656b20e4988205acce631c9310400199ac639262080023ba1e624c41003c7643cc49882000caf749893104001958e931262080023ba1d624c4100047643ac49882000caf745893104001958e8b12620800a1fa15760c41001c6ec1aec188200087f865d4310400187cc8ba862080231798d750c4100043fc3aca188200087d87594310400187ceab2062080030f5d5640c41001e5d382c81882000c5e7558c31040018baeab1862080031b9d6620c41000636bacc41882000c6e7558831040018daeab10620800f3a9c1620c4100065cb22e01882008cda635c031040019d2c4b8062080062fa1176c84100061f3a2cb90820268bf865d3210400187ccaba642080030f59574c841003e57312e990820048bf87593210400117b0eb264208003279d263c84100064eba4c79082000c9e7458f210400193ae8b1e42080032b9d162c841000656ba2c5908200287e85dda21040010fb0bbb442080021fe1975884100061f322eb1082086c6e625d6210413b0ff0eb2c420821a1f61d65884100061f3aac91082000c3d7559221040018bceb31c4208003175d663884100062f3aac71082000c5d7558e21040071df0eb1442080031b9d5628841000636baac51082000ce9625c221040071d905bb2420800e3b609760841001e3d382ca1082003cba7059021040079b4e0b1842080031e59570084100065cb22e01082000cd9635c0210400f9d4c4b8042080031e1d776440100063dc2eec8802000c7885dd9100400197709bb220080032e21376440100066dc1eec8802000cd883dd910040019d705bb220080033a20b76440100063dbb6ea8802000cbb76dd11004001976ec3a2200800336ddb73440100066dbb0e68802000d58751cd10040019d6edb9220080033add87244010
  | 1 => 0xb09a8ac608002b3a0b5158c1000566c16a2b182000e5751945630400159d05a0ac608002b360b4158c100052f42882b182000a5d8510563040075b50020ac608002b66004158c1001c5fc3ac921820038bc8759143040071b90eb1a8608002b3a0f549881000566c1ea93102000e2f54952620400155d09a9cc408002ab613539881000727a9ca731020078ee8710e62040011db0e21cc4080029ba14439881000536c288731020078ee87d4662040011db0fa8cc408002aba13519881000556c26a33102000ace83d46620400159b07a8cc40801e3ba1f419881000476c3e833102000a6e8510662040014db0a20cc40800e3ba1f525881001c7643aa4b102000aae84149620400155b08292c408002b3a0c525881000566c18a4b1020038ee87d09620400155d083aac408002ab610755881000567418eab102000acd831d5620400159f06ba2c408002b320d74588100057240ae8b102000cad741d1620400159d07aa2c408002b360f545881000717aa4a8b102000aaf845cd620400155908b9ac408002b9205735881000537428e6b102000a6d851cd620400155d0839ac408002ab610735881000557426a6b102000aad84d4d6204001c9ea729ac4080023ba1c435881000476c3886b102000a6e8510d62040014db0a21ac4080029ba16715881000536c2ce2b1020008ee87d4562040011db0fa8ac408002aba13515881000556c26a2b102000ace83d45620400159b07a8ac40800399d46515881001d75400a2b102000ae98014562040011dd0fa0ac4080023b61f41588100053742882b102000a6d8510562040075d50020ac408002ba600415881001c5fc3ac921020038bc84dd9420400195885bb2840800237e0d76508100446e41aeca102000cac425d94204001c5884b2a840800e2f21d645081003d56412c8a1020008dd86dcd42040018bccbb9a84080031759773508101b64f326e6a102000c9d64dcd420413399cc5b9a84080023761873508100062f328e6a102000c5d651cd420406593cc839a84080032759073508104be67310e6a1020008de8798d42040111b90f31a8408003a310a63508100046f43ac6a1020008dc8758d4204001d1884b1a840800e3b21d625081000d56422c4a102000ccf735894204001998e6b1284080031d59771508100065ab26e2a102000ce562dc542040011eb0c38a84080031d594715081001c77c3ac599020038df8758e320400317909bb264080022fe11764c81000c5e422ec9902000c3c74595320400117b0dba264080030f997744c8100061eb2ee89902094c9e63dd132040c795cc5ba264080022fa1d644c8100045e43ac899020038dc8758d320400193ee8b1a6408003271d1634c81001c7643ac49902000caf745893204001958e8b1264080031d597714c8100066ab1ee29902000
  | 2 => 0x176481100046fc1aec90220088dc835d920440010fd0dbaa40880030f19375481102ce36316ea90220a087e87d9520440b30f90fb2a40880030fdd764481100061e3aec89022000c5f75d8d20440018b8ebb1a408800317dd463481100062e3a8c69022000c6f75d8920440018d8ebb1240880032d19371481100066a31ee29022000cb4641c520440019a8c638a408800339d88714811023e3d3b6cb8822046cba76d931044003974ec3262088113369db63c41100466d3b0c78822000e586518f10440859d4edb16208801f3a9d862c41100052f41ee8b282000a5d83dd1650400187ee93a2ca080028fa1373594100051ec26e6b282000c5f739cd650413f4f700b9aca0800e9e20173594100043f43886b28200087d8710d65040014dd0421aca080029b60843594100051f420e4b282000a3d841c965040014bd06392ca080029760c72594104f53cc04e2b282000a6e82d0565040014db05a0aca080021fa1c41594100043ec3882b2820038be87d51640400187eebaa2c808002a7a0f54590100054ec1ea8b2020038bc87551640400187eeb3aac808002a7a0e75590100054ec1ceab202000a3e851cd640400147b0a39ac808002aba08735901000556c10e6b2020008be87d4d640400117b0fa9ac80800387d4e53590100054fc1ae4b202000a9c835c9640400156902b92c8080032b5c872590100045f438a4b2020008bd87149640400153d06292c808002a760c52590100051f428e2b202000a3d851c5640400917d0fa8ac8080022f61f51590100054f41ea2b202000a9d83d45640400155d05a8ac808002ab60b51590100071ba8ca2b2020088de87d5263040011bb0faa4c60800387d525498c100446f438a531820008dd8714a630400153d08294c608002a76105298c100446f43ea331820008dd87d46630400153d09a8cc608002a76135198c1000567416a33182000acd82d46630400159d05a0cc608002b360b4198c100052f428833182000a5d8510663040071f100baac60800e37a1f5358c100062fbaea6b182000a9e84d4d630400153b09a9ac60800b179d65358c1001c6e43aa6b1820038de87d0d63040014bd0a21ac608002976144358c100056741086b182000acd8210d63040018beeb3aac608002a7a127558c100054ec24eab182000adb805d563040075b100baac60800297a147458c100052ec28e8b182000ace821d1630400159b043a2c60800237a1f5458c100046ec3ea8b182000e1f54951630400153f08b92c608002a72117258c100056a40ae4b182000a5e851c963040014bb0a392c608002a7a107258c100054ec20e4b1820008de8714963040011bb0e292c608002a7a105258c100054ec20a4b182000a5e851c563040014bb0a38ac60800237a1f5158c100046ec3ea2b182000a9e84d45630400153
  | 3 => 0xa1922000c3c645d432440118b8c6ba8648801f1b189750c9100043fc3eca192200087d87d94324400187ce9b2864880022f219740c9100061fb2ae81922000c3c655d03244011938c6ba0648801f2b189740c9100045fc3ec819220008bd87d90324400187cebb2064880030f5d7640c9100062f3aec61922000c5d75d8c324400193ce9b186488003275d3630c910006373aec41922000c6d75d88324400195ce9b1064880032b5d3620c9100466a31ce21922007ce4629c432440071e90cb88648801e3e219700c9100466c31ae01922046cb870d914144001878e9b2a62881162fa1b744c5100061fb2ee898a2000c3c65dd131440e3938c7ba2628822e2fa1f644c5102345e43ec898a2000c9f74d8d3144001938e9b1a6288113361c3634c51020c77436e498a2000c6f65dc931440018d8cbb9262880032bd93724c51000656326e498a2000ccf63dc93144091998c7b92628810a3ba18724c51000637b28e498a2000c6c651c9314400195ec839262880032b190724c51000667b18e498a205accc631c931440b51dd0fb12628810a3b21f624c51000657ba6c498a2000cac74d8931440911dd0e312628801e3b21c624c51000657ba0c498a2000cac7418931440018f0cbb82628800a1f216760c51014c3e432ea18a2000c3c645d431440118b8c6ba862880021fe1f650c5100543ec3eca18a2000c3e75d90314400187aebb206288003179d7630c5100062ebaec618a2000c6e75d8831440018daebb1062880031b9d4620c51000636ba8c418a2000c3e74d97214408b1790cba642880030fd9574c85100061e32ae990a2007cac625d3214408d17f0fb2642880022f61f64c85100064f3a6c790a2000c9d74d8f214400193ce831e4288003275d063c8510006573a6c590a2000cad74d8b21440050f90b3b4428808a1f21975885100061e322eb10a2086c6c625d621440010ff0fb2c428802a1f61f65885100061f3aec910a2000c3d75d9221440018bcebb1c4288003175d763885100062f3a8c710a2000c5d7518e21440018dcebb1442880031b5d7628851021674386c490a2000ce462dc540440012eb0a38a80880032dd90715011000672310e2a02200287c859db30440010f90cbae60880030f19175cc1100462e31aeb982200087f87d9730440010fb0fb2e60880030f9d764cc1100061ebaec99822000c5e75d8f30440018baebb1e60880031b9d762cc11000636baec59822000c6e7518b30440018daea31660880233518e71cc1100043fc2aec982200287c855d9304400117f08bb260880062f211764c11000477c12ec98220078ec825d930440019c8c5b8a60880025d614714c1100066bb18e29822000ce4621c530440012eb0b38e408801f3918a71c81100043fc2aec902200287c855d9204400117f08bb240880062f21
  | 4 => 0x24400155d09318c488002ab612631891000477c3ac63122000a6f8558c62440014d90ab18c488002abe11631891000556422c63122000cce7618c6244001c9eca318c48800393194631891000747b20c63122000e8c6418c6244143d8c20318c488287b104063189100073232ca23122000ea4649446244001d88c7288c488106b9219511891000752322a23122000ec463544624400159d07aa0c488002b360f54189100057340ea83122000ae581d506244001c5ea92a0c488002aba13531891000556c26a63122000ae681d4c62440015cb03a98c48800393d4e531891003c774388631220008ed8710c62440014dd0a218c4880029b614431891003c7743ea231220008ed87d44624400155d09a88c488002ab61351189100056741ea23122000acd83d44624400f1dd0fa08c4880023b61f411891000537428823122000a6d8510462440014dd0ba00c4880029b617401891000537c2a203122000a6c85440624400155f08880c488002ab211101891000567c1a203122000acc8344062440010ff0abb4848800a1f21576909100046fc1aed21220088dc835da424400f1d904bb4848800a1fa1776509100043ec2eeca1220088de83dd942440011bb07bb2848802237a0e76509100046ec1ceca122000cac429d942440010ff0abb2848800a1f21576509100046fc1aeca1220088dc835d942440011df04bb284880023de05765091000656210eca122000e2c42d95424400f17d0fb22848801eaba0b64509100046f436e6a122000c5f65dcd42440018b8cbb9a848800327d9373509101b64e326e6a122099ccc62dcd42440011bd0c39a848800317d9473509100062e328e6a122000c9f641cd4244065938c839a848825f3318873509100046f43ec6a1220008dc87d8d4244001d1885b1a848800237a1c63509100446e438c6a122000e8c4218d42440031dd0fb128488006aba13625091000667b9ec4a122000ccc73d8942440010ff0abb6648800a1f21576cc9100045fc22ed99220018bc845db324400f1b906bb664880021fe15768c9100143e42aed19220008bf845da324400317908bb4648801e3b209768c9100143f42eec992200087d85dd9324400317d09bb264880022f613764c91000c5f424ec99220008bd849d932440010ff0abb2648800a1f215764c9100045fc22ec99220018bc845d932440011ef02bb264880062f210764c9100061e3a6ca99220008be86dd1324400187ecbba264880030f197744c9104a64e31ee89922063cac62dd1324400117d0fb2264880022f21f644c91003c6f43ec69922000c9f74d8d3244001938e9b1a64880223ba1f624c91000657ba6c49922000cac74d8932440050f90b3b064880062f212760c9100043fc2aec192200287c855d8324400117f08bb064880062f211760c9100043e432e
  | 5 => 0x80029b61770d89100053742e81b122000a6d85d03624400f8d8c4bacc4880030f9d365989100061f3a0cb3122000c3f655d26244001878caba4c48801f2b18974989100061f3aec93122000c3d75d92624400187cea324c4880030f5d464989100062fb2ce73122000c5c659ce624400193ec939cc48800327192739891003e66314e73122000c5f655ce62440018b8cab9cc48800327d9173989100064e322e73122007ccc625ce62440018bcebb1cc488003175d763989100064f3a6c73122000c9d74d8e62440018bcea31cc488003175d463989100064f3a0c73122000c9d7418e62440018dcebb14c4880031b5d76298910006573a6c53122000cad74d8a624400199ce7b14c488003335cf62989100143f436eab12200087e87d956244001878e9b2ac4880021fa1c65589100061e3a0cab122000c3f65dd16244001878cbba2c4880022fa1f64589100061fbaec8b122000c3c75d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c5f65dcd62440018b8cbb9ac48800327d9373589100064e326e6b122000c5f651cd62440018b8ca39ac48800327d9073589100064e320e6b1220008de87d8d62440018beebb1ac488003171d763589100064fba6c6b122000c9c74d8d62440011bd0e31ac48800317dd463589100062e3a8c6b122000c9f7418d6244001938e831ac4880022fe11755891000c5e422eab1220008df835d562440111b906baac4880023be0975589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fba8e6b122000c5c751cd624400193ee839ac488003271d0735891000637baee4b122000c6c75dc9624400195ee9b92c4880032b1d3725891000667b9ee4b122000ccc73dc96244001968e9b8ac488003351cf715891000477c3ac43122000a6f8558862440014d90ab10c488002abe11621891000556422c43122000acf83588624400159906b10c4880031b9db651891000476c3cca3122000aae84994624400155b09328c488002b3a0e651891000566c1cca31220008ef87594624400155f08b28c488002ab211651891000567c1aca3122000acc8359462440018dcec328c488003996046518910006573b6c83122000e2f65d906244001c58cbb20c4880023b61e64189100053742cc83122000a6d85990624400159d07320c488002b360e641891000477c3ac83122000a6f8559062440014d90ab20c488002b3e0d64189100056641ac83122000cae761906244001c5eca320c4880038b194641891051753080c831220a2ea410190624400199cedb18c48800393d9763189100072632ec63122000e8f64d8c6244001d18c9b18c4880023b61e63189100053742cc63122000a6d8598c6
  | 6 => 0x52ec2cc831a2000ace82990634400159b05320c68800237e1d6418d100052fc2ac831a2000a5c85590634400159f04b20c688002b32096418d100064f3b0c831a2000e1f651906344001c38ca320c688003951965118d1021d6a432a231a20088de87d5063440011bb0faa0c68800387d525418d100056b40ea431a2000ad581d4863440111bd0e290c6880023761c5218d100054f420a431a2000a9d8414863440111bd0fa88c6880023761f5118d100054f426a231a2000a9d84d44634400159d05a88c688002b360b5118d100056dc02a231a2043ad880544634400159d05a08c688002b360b4118d100052f4288231a2000a5d8510463440014bd0ba00c688002976174018d100052fc2a2031a2000a5c85440634400153f08880c688002a72111018d100043fc2aed21a200287c855da43440111b906bb486880023be097690d1003c76412ed21a200287e85dd943440010fb0bbb2868801e3ba0b7650d1000476c16eca1a200087f855d943440050f90abb2868800237e0d7650d1000477c12eca1a20078ec825d9434401117d0fb22868800637a1f6350d1000572c0ea5b1220028ef8754b624400155d08296c488002ab61052d891000567418a5b122000acd8314b624400155d0932ec488002ab61265d89100056741ccbb122000acd83997624400155f08b2ec488002ab21165d891000567c1acbb122000acc835976244001ccb0232ec4880038bd9764d89100071632ec9b122000a6e8599362440014db0b326c488002b3a0e64d891000566c1cc9b122000a6f8559362440014d90ab26c488002b3e0d64d89100056641ac9b122000e2f651936244001c58ca326c48800393d9763d89100072632ec7b122000e8f64d8f6244001d18c9b1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec48800393d9463d891000726328c7b122000e8f6418f6244001d18c831ec4880039919651d891021572432a3b122000aae849d7624400155b093aec488002b3a0e75d891000566c1cebb122000ae6811d762440855cb023aec488002b3a0f74d891000566c1ee9b122000caf749d3624400159d07aa6c488002b360f54d891000717aa4a9b122000aae84dcf624400155b09b9ec4880029ba1673d891000536c2ce7b122000aae849cf624400155b0939ec488002aba1353d891000556c26a7b122000e4f5394f62440011dd0e21ec4880023b61c43d89100053742887b122000a6d8510f624400155f08b8ec488002ab21171d89102147743ea3b1220008ed87d47624400155d09a8ec488002ab61351d89100056741ea3b122000acd83d4762440851dd0fa0ec4880023b61f41d89100053742883b122000a6d8510762440014dd0bb86c48
  | 7 => 0xcf82593634400159904b26c68800387d9464d8d100070e328c9b1a2000e546594763440895a90ca8ec688003175d475d8d100054f420ebb1a2000a9d841d763440015ad023aec688112b560475d8d100052f42ce9b1a2000a5d859d3634400159d053a6c688002b360a74d8d100046f43ea9b1a20008dd87d536344001c3ea92a6c688002a7a1372d8d100054ec26e5b1a2000a5e859cb63440014bb0b396c688002a7a1272d8d100054ec24e5b1a20008de8714b63440011bb0e296c688002a7a1052d8d100054ec20a5b1a20448de87d4763440011bb0fa8ec688002a7a1351d8d100054ec26a3b1a2000ace82d47634400159b05a8ec688002b3a0b41d8d1000566c1683b1a2000a5e8510763440014bb0a20ec68800297e1570d8d100052e42ae1b1a2000a5e85d0363440014bb0ba06c6880231718d7598d100061f3a6cb31a2000c3e74196634400187ecaba4c6880030f1957498d100464e31ae931a2000c3e75d92634400187aebb24c6880030f9d46498d100061eba8c931a2000c5e75d8e63440018baebb1cc688003279d36398d100064eba6c731a2000c6f659ca63440018d8cb394c6880032bd927298d1000656324e531a2000ccf639ca6344011998c7394c6880031bd957298d100063632ae531a2000caf645ca6344001958c8b94c68800333d8d7298d100466631ae531a200087e87d956344001878e9b2ac6880021fa1c6558d100061e3a0cab1a2000c3f65dd16344001878cbba2c6880022fa1f6458d100061fbaec8b1a2000c3c75d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d1000656326e4b1a2000c6f651c963440018d8ca392c6880032bd907258d1000656320e4b1a20008bf845d5634400317908baac68800237e0d7558d1000477c12eab1a20078ec825d563440011f700baac6880030fdd77458d100061e3aee8b1a2000c3f751d16344001878ea3a2c68800317dd77358d100062e3aee6b1a2000c9f74dcd6344001938e9b9ac6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c68800333dcf7258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a2000ce472dc563440018f0ebb82c68800237e1d6318d100052fc2ac631a2000a5c8558c634400153f08b18c688002a72116318d1000567c12c631a2000acc8258c63440018bcedb28c6880023761e6518d100054f424ca31a2000a9d84994634400159d05328c688002b360a6518d100046fc3aca31a2000a9f84594634400153908b28c688002b3e096518d1000566412ca31a2000c5e761946344001cab02328c688003279db6418d100070fb2ec831a2000e1c65d9063440011bb0f320c68800297a166418d100
  | 8 => 0x5a0eca880029b60b41d95100043f43883b2a200a87d87107654407f4ed03b86ca880021fa1f40d95100043ec3e81b2a2000c3d75d53644400153d07aa6c888002a760f54d91100055ac0ea9b2220028bf87553644400153d0732ec888002a760e65d911000557414cbb222000aad82997644400153f06b2ec888002a720d65d911000557c12cbb222000aac825976444001c6b0232ec8880038d19651d91102355a432a3b222000c3d751d7644400153d063aec888002a760c75d91100055b408ebb222046ab5811d7644400147d0b39ec8880028f61673d911000557414e7b222000aad829cf644400117d0fa9ec8880022f61f53d91100070fa9ca7b222000a9e83dcb644400153b07b96c8880032bdca72d91100045f438a5b2220008bd8714b644400153d06296c888002a760c52d911000557c12e3b222000aac825c7644408d17d0fa8ec8880022f61f51d91100054f41ea3b222000a9d83d47644400155d05a8ec888002ab60b51d91100051fc2ae1b222000a3c855c36444001878c9baac8880021fa1f65591100043f438cab222000c5f65dcd64440018b8cbb9ac8880032719373591100062fb28e6b222000c5c651cd6444001938c839ac8880031bd9772591100063632ee4b222000cac64dc964440018deca392c8880031b194725911000656320e4b22200287e87dd5644400117f08baac88800237e0d75591100446e41aeab2220008ef825d5644400f1d904baac8880021fa1c75591100061fbaee8b222000c3c75dd164440111bd0fb9ac88800317dd773591100062e3aee6b222000c9f74dcd64440018beea39ac888003171d473591100064fba0e6b2220078ee87dc964440018deebb92c8880031b1d7725911000657ba6e4b222000ccf73dc96444001998e7b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc725911000672396e2b222000c3e76d94644400117b0f328c8880028fa1665191100054f41cca3222000a9d83994644400155d05328c888002ab60a65191100045fc3aca3222000a9f83594644400153906b28c888002abe09651911000556412ca3222000a3e86194644400187cec328c8880038d60465191100071a32ca23222045ab48654464440018baeba9ec688002a7a1353d8d100054ec26a7b1a2000ad581d4f63440058b8eb29ec68800a37e1d53d8d100052f42887b1a2000a5d8510f634400159d0421ec688002b360843d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100072ac08cbb1a2000e1f65d936344001c38cbb26c68800297a1664d8d100052ec2cc9b1a2000ace82993634400159b05326c68800297e1564d8d100052e42ac9b1a2000a
  | 9 => 0x644c42000657326e49884000cad64dc9310800f9c8e530a62100030f991750c4200061f3aac81884000c3d7559031080018dceabb442100031b5d97588420007173aac91084000e2d75592210800f95ce2b24421001fa99c5648842021657b82c91084042cad70592210800517f0eaa6c98800a37e1d53d8f100045fc22eab1e20018bc845d563c40011df04baac78801e3b2097558f1000c5f43ee8b1e2000caf74dc963c4001958e9b92c7880032bdd07258f10006563a0e4b1e20008df8758c63c40011df04bb4878801e3b2097690f100045fc22eca1e20008ef825d943c400f1d904bb2878800a1fa147650f100043ec28eca1e2002c6e7594b62c40051df0ea96c58801f2b1897498b1000656ba6c531620008ef8758862c40050fd0b3b485880021f6167690b1003c76412ed216200287e859d942c40010fb0b3b2858802237a0e7650b100046ec1ceca1620008df835d942c40111b906bb2858801e2fa1f6450b1003d57416c8a162000c9f641cd42c4065938c839a858825f331887350b1000c7743ec4a162001aae84d8942c4001998e7b1285880022fe1176ccb1000c5e422ed996200287e859da32c40010fb0b3b4658800a1fa16764cb100043ec2cec99620018be849d932c400117b093b265880022fe11764cb1000c5e422ec99620008ef825d932c400f1d904bb0658801f1b189750cb1003e56312e81962000c6d75d8832c400195ae9b10658800e3d61a710cb1001c5f43ec8a0e20008df8758c31c400f958c4ba643880032b5d362c871000477c3ac410e2000975851c540c40891bf0eb1e61880025d614714c31021477c3ac59062000975859c720c40071790eaa2c90800e3721d5358e1001c5fc3ac921c200287e85dd943840010fb0bbb2870800a1fa1f7558a102c43f438eab142002c6c7594962840071d90ea92c5080021fe157690a100143e42aed214200087f855d942840050f90abb2850800237e0d7650a100446e41aeca1420038bc87591428400f55904b2285080cb279907350a100064eb20e6a142097cce621cd42840071d90eb128508006ab2116250a100066639ac4a1420038ef8758b32840010ff0abb4650800a1f215768ca100043fc2aec994200287c855d9328400117f08bb265080062f211764ca1003e37312ea1942007cae625d032840018daeab1065080032b5d1620ca1021c6fc3ac798c2007cae625d321840831df0eb1643080032b5d162c86100052f41cc9b2a2000a5d8399365440014dd05326ca880029b60a64d95100052fc1ae9b2a2000a5c835d3654400187ae83a6ca880028fe1173d95100051e422e7b2a2000c5d731cf65440010fd0e21eca880021f61c43d95100053741087b2a2000a6d8210f654400147d09396ca880028f61272d95100052f41ce5b2a2000a5d839cb65440014dd
  | 10 => 0xb0a40a3c6d7219461480011ef0eb08c290002ad21161185200056a41ac230a40008bf845cc614800317908b98c29000b1b9d6521852000572c0c8430a4001cac74508614800159906a10c290002b9e05421852000536c286430a4000aad840c8614800199ae6190c290002b960b411852000752a108230a4000af18010461480010ff0abb4829000a1f215769052003cd7c3a8520a4001aac8650a414800195ceca148290002e320d42905200143f42eeca0a400087d85dd941480071db053b662900021fe1576cc5200143e42aed98a400087f855da31480050f90abb4629000a1fa17764c5200043ec2eec98a40018be849d9314800117b093b2629001e3b208764c5200061e3a6ca98a4059c6c72d95314800187ecbba262900030f197744c52000637b2ee498a4000c6c65dc931480050f90b3b062900021fe15760c5200143e42aec18a40008bf845d8314800317908bb062900021f219750c5200043fc3eca18a400087d87d943148011998c6b9062900033c185700c5200063632ced90a4000c6e76d972148001a5ecaba642900034b19574c852003e57b02e990a4007dab605d3214800195ae830e429028e1f21975885200043ec3ecb10a4058c6c76d9521480071d90cba2429012a7320d744852000733b28c290a40039ac8750940480075590ca12809001f2b1d94250120005c641a84a024003ba88050940481410f90cbae60901661fe1f65cc1200043ec3ecb9824008ccc635cb30480010ff0abb2609000a1f215764c1200045fc22ec98240018bc845d9304800717d0faa2c8100030fdd754590200054f41ea8b204000a9d83d5164080071790eaa2c8100063b60b71590200143f428e2b20400087d851c5640800187eeb3aac810002a7a0e75590200054ec1ceab204000a3e851cd640800147b0a39ac810003275cc735902003d57410e6b20400eaad821cd640800117d0fa9ac8100022f61f53590200070fa9ca6b204007aae82dc5640801d55b05b8ac810002a7e0d71590200054e41ae2b204007aac825c5640800147d0a38ac8100028f61471590200045f43ea2b2040008bd87d45640800153d07a8ac810002a760f515902003d57416a2b204000aad82d45640800155f04a8ac81001eab209515902001c6e43aa6b18400287e851c563080010fb0a38ac61000e2fe1d6490c2001c5e43ac8a184008a9c83591430800117f08b9cc2100062f211739842001c7ac3ca330840078ec825d561080071e90ea8ac21000e2f21376504200046fc1aeca0840088dc835d9410800f958e4b2282100023b61b725042000656b26e4a084007cae7259331080bb1df0cb9662100032b59172cc42000c5e426ec98840008bf845d9310800317908bb262101223be09764c4200045ec36e898840008be8759131080011790eb22621001f2b1c9
  | 11 => 0x480050fd0b38ec6900021f61671d8d200043f43ecab1a4000c3c74d9563480010fd0e32ac6900030f1d06558d200061fb2ee8b1a4000c3c65dd163480018eecbb8ac6900031d1977158d200063bb28e2b1a4000c74651c5634800117f08baac6900062f2117558d200047bc0aeab1a40008f4815d5634800187eebba2c6900030f1d77458d200061fba8e8b1a4000c3c751d16348001938e9b9ac69000b171d65358d2052e4e3a4a6b1a40028dc8754d6348149938e8a9ac6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4000cd6531c563480019aaa638ac69000339cc87158d2000672190e2b1a40038ed829d863480011bf0eb18c690002a72116318d200056a40ac631a40038ed829da43480010ff0abb4869000a1f2157690d200143f42eeca1a400087d85dd943480010ff0abb2869000a1f2157650d200046fc1aeca1a40008f7815d943480011e902bb2869000e3ba1b7250d200063632ee4a1a404a8ed87d8e4248001d1887b1c8490006ab21163909200057240ac72124059e2c42d95424800f55d05b22849000317d9773509200062e32ee6a124000c5f651cd42480018b8ca39a849000327d9073509201964e320e6a124097d8c421cd42480b18d8edb2a84900038b193655092000d57436c8a124036ccc76dcd424806dd18c9b9a84900cb331d873509204bec7ba0e6a124032e8c641cd424809599d0c39a849012b336187350920256a7428e6a12404ad4d851cd4248001a9eca39a8490003531947350920256c7420e6a124000d8f641cd424809fb18c839a849013f639507350920006c6aa0e6a12404fd8c411cd424812f99ec039a849025f72d80735092027ec7a00e6a124001aac84d8d4248095998e7b1a8490003a3d0f635092000c7643ac6a124001aac8458d4248095998e6b1a8490002b9205635092003cd643a86a124000aac8650d4248095b18e6a1a84901063ba1b7150920006e439ee0a124000dcb731c142480b18dcedb2e649000393d9763cc92020c76432e399240009af845c73248001878e9b2a64900030fd97744c9200061e32ee89924000c9c74d8d32480a32d90cba8649000353d0d750c920256a621aea1924007c6f605d4324800fad6c0ba864900025be1f650c920254e641ae81924000d2f655d03248001a58caba0649013f63e0d740c920256c641ae8192404acaf635d0324809595ac6ba0649001f2bd81740c92003ed5b02e8192400287e86dd561480b10f90dbaac2900021fa1f65585200061e3a6cab0a400087e871956148001878e832ac2900030fd9774585200061e32ee8b0a4000c5f65dcd61480018b8cbb9ac29000317d9473585200062e328e6
  | 12 => 0xe3ba0b75987204ee37394eb30e400287f875d661c810d8dce4bacc3900072b9d142987200056641a8530e400287e85dda41c80010fb0bbb4839002237a0f76907200046ec1eed20e40038ee82dda41c800f95ce4b24839001f2b9d94290720005c641a8520e40038ee82dd941c80071d904bb6639000a1fa17768c7200043ec2eed18e40018be84dda31c800117b09bb4639000e3ba0b768c72003e67392c718e40008bf845d931c800317908bb2639000e3b209764c7200462f31aea18e4000c5d7558c31c80bb39906ba2439001f2b1c9645032001cd643a84a064007cac7650940c800171906a1281900231798d75cc3200062ebaac79864007ccc7258d30c80071790eaa2c91000a1fa1471592200043ec28e2b2440038dc8754d63880071bd0fa1ac710002976144358e2000566c1086b1c400287e851c563880010fb0a38ac71000e2fe1d6490e201964f320e6a144000c9d641cd4288001938e8b1a65100022fe11739862000c5e422e730c40038f58794661880058eceb28cc3100022fe11755862000c5e422eab0c40018be87dd1618808d95e41ba2c31011b2b483745862001c7a43aa2b0c40008bf845d9318800317908bb26310003271d1634c6202466731ee498c4000c757598621880018eaeab0c4310002abe116188620006b4baae110c4000aaf8458421880014bf06ba6ca900029720d74d95200061eba0e9b2a4059a6e821d365480b14db043a6ca901669ba0b73d95202c536c16e7b2a4000a3f845cf654800147908b9eca90003175cc73d95200043f43887b2a400087d8710f65480b34dd0421eca900029b60843d95200051fc22e3b2a4000a3c845c765480014bf06b8eca900029720d71d952000537c12e3b2a4059a6c825c765480b34dd0438eca901629b60871d95202cd3741683b2a4000a6d82d0765480010fd0e20eca900021f61c41d95202cc3f43e81b2a400087d87d0365480050fd0b38ec8900021f61671d912003c76412e3b22400087e87d9564480010fd0e32ac89000317d9773591200062e32ee6b224000c5f651cd64480018b8ca39ac8900032719073591200063bb2ee2b224000c7465dc564480018eeca38ac8900031d19471591200065a320e2b22400287e87dd564480011bf06baac8900223720d75591200047bc0aeab2240008f4815d564480010fd0e3aac89000a2f21d54591205364e39aa8b2240088de87dcd64480018beebb9ac890003171d773591200062fba8e6b224000c5c751cd644800193ee839ac8900031ddd771591200063a3aee2b224000cd773dc564480019a8e7b8ac8900031ddd471591200063a3a8e2b224000cb7741c564480019aee638ac890003351cc715912000673b90e2b224000cb6541c5644800196aa838ac89028f1b5c865d8d2001c76c16ebb1a4000acd8210f63
  | 13 => 0x64f326e690c604accc73589218c007974e0b2043180032e591700863003e75312e010c60028bf87553644c0011df04b8ec89801e3b20971d913000477c12eab2260078ec825d5644c0011ef02baac8980023d20575591300143f428e2b22600087d851c5644c00117f08b8ec4980062f21171d893003e57312e831260008ef87588624c00195ae8b10c498002b9205621893003c77414ed212600087f855da424c0050f90abb484980223720c765093003c5e43ac8a126067c9c73591424c00f55904b22849800e76a03735093025476c3ec51926094d9830dd1324c0010ff0ab96c29800a1f21572d85300047bc3ac230a6000ae482584614c0058bceb298c29800b179d553185300043fc2aed20a600287c855da414c0050fd0a3b482980021f614769053000672396c298a6000ce472185314c001b18e8392629800366dd0704c530006e5b90e098a600287e851da214c0010fb0a3b442980021fe1576085300143e42aec10a60008bf845d8214c00317908bb0429801f33189730853001c5e43aa8b20600287e851c5640c0010fb0a38ac81800e3b21d52588304cc6fc1aeca106008c9c73591420c00f55904b22841800e3b21d625083000d56422c4a106008ccc73589420c0071eb0f28cc2180022fe11755843000c5e422eab0860088dc835d5610c0011df04baac21801e3b209755843000c5f43ee8b086071c9c73dd1610c117938e63a2c2180032bdd37258430006563a6e4b086048ccc73dc9610c00195ee8392c2180032b1d072584302d666398e4b0860038f487545610c0075e100a8ac21800e3d61e619043000d5a422c320860008ef825d9410c00f1d904bb2821800e3d21d615043003e57312e990860418ef8758b210c00195ae8b16421800a1fa1776884300043ec2eed1086000c7575986210c0018eaeab0c421801eb920961884300045fc22ec90860018bc845d9210c00f1790eaa2c9900022fe117558f2000c5e422eab1e40038ec825d563c800317d0fba2c79018f2b1cb7458f2031f46196e8b1e4097cac721d163c812fd18643a2c790297271d25358f2003c6e43aa6b1e40a4c9c7454d63c800f59904a9ac79000e3b2097690f2000d4e422c721e4007ccc7258e43c80c7d1c84b1c879018e2fe117650f2001c76412eca1e40078bc8759143c800f958e4b22879001e3721d6350f2003e66392c6a1e4099e8c64dcd42c812fb1ee839a859025fa31907350b204be67430e6a16405dccd861cd42c80bba9d0a39a8590177536147350b202eec7420e6a164097d8d841cd42c812fb1ec839a859025f631907350b2053ec72a0e6a164000d8d541cd42c814fb188239a859029f63d007350b202ec7643ac6a164001aac8458d42c80bb998e6b1a859001eab2194350b202eec639a86a164000e8d6350d42c800135f08b8e6590
  | 14 => 0xf759d5648c0cf53d073aac918002a760e75592300045f43ea6b2460008bd87d4d648c0cfc3ca7a9ac918002a7e0d725923000656b90e4b2460008be87149648c00117b0e292c91819ea7a0c52592300054ec18a4b246000aae82dc5648c00155b05b8ac918002a7e0d71592300051f428e2b246000a3d851c5648c00117d0fa8ac9180022f61f515923033d4f41ea2b246000a9d83d45648c00155d05a8ac918002ab60b51592300065cb26e0a1c605dace83d52628c00159b07aa4c5180038bd525498a3000557426a73146000aad84d4e628c0bbc9ca7a9cc518177a310d4398a3003c7743ea331460008ed87d46628c00155d09a8cc518002ab6135198a302ed6741ea33146000acd83d46628c00f1dd0fa0cc5180023b61f4198a3000537428833146000a6d85106628c0018deeba92c51800e3b21d5258a3000557420a4b146000aad84149628c00159b06292c5180062fa137158a300045ec26e2b146000c6f759d5628c00155d083aac518002ab6107558a3025567418eab146000acd831d5628c0014dd0b3a2c5180029b6167458a3000567c1ae8b146000cad741d1628c09559d07aa2c518002b360f5458a3000717aa4a8b146000a6f855cd628c0014d90ab9ac518002abe117358a3000556422e6b146000ae7815cd628c0015c902b9ac518002aba135358a3000556c26a6b14604ae4e53d4d628c00155d09b8ac518002ab6137158a300053742ce2b146000a6d859c5628c00159f06b8ac5180023ba1f5158a3000476c3ea2b146000aae84d45628c00155b09a8ac51812ab3a0f5158a3000566c1ea2b1460008ee87d05628c0011db0fa0ac5180029ba144158a3000536c2882b146003aea80105628c0015d30020ac5180032b10b7650a3000656212eca146067c9c73591428c00f55904b2285180db279937350a304ce67316e6a1460038ec87589428c00355908b12851812b331cd6250a3003e75312e119460008bd86dd1328c0c795cc5ba2651825e2f21d644ca3000657ba2c49946000cac74589328c0019d2c5b82651800e3d61e51986300163b3aca330c60038f487545618c00717909bb2831819f271cd645063000667b9cc4a0c605dccc73989418c00117b0dba263180022f21d644c63000476c36e498c6000cae64dc9318c00195ac9b9263180023b618724c63000657320e498c6000cad641c9318c0011dd0f31263180032bdd2624c630006563a4c498c60008ec87589318c00195ee8b1263180032b1d1624c63000c5f422ed90c60008bf865d3218c00f95cc4ba643180022fe1d64c86300045ec3ac990c6000cae7458b218c00195ae8b16431800a1fa1776886300043ec2eed10c6000c3e645d6218c10d8dcc4bac43180030f9d564886300061ebaac910c6000c6e7558a218c0018daeab14431800e3b20b764863000
  | 15 => 0x6a1464a0003a3d8d428c94000c5e420ec99280019ac875093250001958eca1264a019ee320d424c94003c5e424ec1928008c5c635d432500cfa3886ba864a019e6720d740c9400464e31ae81928000c5d75d8c325000193ae9b1864a00021fe1572d85400143e42ae5b0a80008f78758461500015c904b08c2a000a1fe1d75185400061e21aea30a8000c3f425d4615000587ceaaa0c2a00032710d73185400061ebac8630a8000c3d75508615000153906a10c2a0002ade05421854006c5f438c2a0a80038bd849db31500010ff0abb462a000a1f215768c5400143f428ed18a800087d851da315000f1dd053b262a00023b60a764c54000c5e420ec98a8008c5c635d43150011938c6ba062a0003175d7630c5400447c432e018a80078bc849db215000196ae830e42a000a1fa1476885400043ec28ed10a80019af8750a215000f5590ca1442a00032b9d94288540005c641a8510a80038bc865d121500cf33906ba242a00021fe1576085400143e42aec10a80008df835d821500111b906bb042a001f2b189740854003e563b28410a8000b8c835082150001d4a8430842a001e3e2197008540006d4a12e010a8000cf0615c021500114bd07ba2cb980769760f74597300061fba4e8b2e6000a3e841c965cc00147b08392cb9802297a0c72597300ed2ec18e4b2e6000a3e84dc565cc00147b09b8acb9802297a0f71597300ed2ec1ee2b2e6000a6e82dc565cc0014db05b8acb9802297a0e71597303552ec1ce2b2e6000a7b805c565cc0d74f100b8acb980029ba0b415973000536c1682b2e600087e8710565cc0010fb0e20acb982a297e0d70597300043f43e80b2e600087d87d0165cc00f1dd05b8ac9980023b60b71593300143f428e2b26600087d851c564cc0058bceaa9ac5980062fa137158b300045ec26e2b1660038dc835d942cc0118b8e6b2a85980038b1096550b300464e39ac8a166007aac8259142cc0018bccbb9a8598003175977350b300447643ac4a166001aac8458942cc011998e6b12859800e37a0f75987300143f42ee4b0e600087d85dc961cc0071bd07bb48398023179cd65907300464f39ac920e6000c5d655ce41cc00193eedba2639800327dd8744c73000667bb6e498e6000ccf761c931cc001b18e839263980030f9d165c87300061f32ae990e6000c3d655d321cc0050fd0bbb443980021f617768873000c5f426ed10e60008bd84dda21cc0071bd07bb4439800a1fa1576887300043fc32eb10e600087f8759621cc0010fb0eb2c4398023339cd62887300462f39aca10e6000c5d655cc21cc0118b8e6b2a8198023271cd64503300062eb2ee6a0660038be87d51648c00187eebaa2c918002a760f545923001c5e43aa8b2460078ee82dc5648c0011db05b8ac91800a1fa1471592300043ec28e2b246000c3
  | 16 => 0x458c2131f46196e8b184297cac721d1630852fd18643a2c610a97271d25358c2103c6e43aa6b1842a4c9c7454d630840f59904a9ac61081e3b2097690c2100d4e422c72184207ccc7258e43084c7d1c84b1c861098e2fe117650c2103c76412eca1842078bc87591430840f958e4b22861081e3721d6350c2103e66392c6a1842979ce87dcd4208533d18c9b9a8410a5f63dd073508214bf46320e6a104297cce861cd42084b599b0c39a841096b53a1473508212d6a6c28e6a10425ad8e841cd420852fb1b0839a8410a5f63d9073508214bec6320e6a1042a9d8e541cd4208401b1aa839a84109233398473508214bee3308e6a1042a9d8c411cd4208553b1e8039a841096a3b21d635082100d56422c6a10425accc7358d420840f3590ea1a841081eab21943508212d6c639a86a104200e8d6350d420840135f08b8e641081f2b9c9649042103cd7c3a852084207cae7650a410840171906a14821080a1fa17768c4210043ec2eed18842018be84dda310840117b09bb4621081f339c9638c4210462f31aea1884200c5d7558c31084019cca3bb2421080339547764842100477c32e8908425a9cc835d121084050fd0fbaac0109671b1cb755802150636390eab0042418ec8754960084831d90ea12c0108072b1d142580210056641a84b0042418ee87cc960084835d501992c0109063b21d215802120d7440242b004202c787594160084b3cd4a5282c01081e3e21d505802101c6e43aa6b1c800287e851c563900010fb0a38ac72000e3b21d5258a400462f31aea1948007c6e625d4329000f95cc4ba06520003175d5630ca400064eba2c61948000c6d75588329000195ae8b1065200023be09739864003c76412e730c80038f58794661900058eceb28cc3200023be09755864003c76412eab0c8000cac41dc9619008595e81b92c32010b2b503725864001c7a43aa2b0c80458bf87586419000155f04b0c83200023be09764c64003c76412ec98c8071c9e63dd131900b599cc639263200033358c724c64003e57312e990c80418ef8758b219000195ae8b16432000a1fa1776886400043ec2eed10c80028df8754f63500118b8c6bacc6a0003175d76398d400046fc3ac631a80458bc865c6435000135f04b8c86a00023be1d62189400057240ac43128099c9c76dcd4250133d18c5b9a84a025f271d873509404bf46310e6a128067c9e861cd42500cf93b0c39a84a019f47a14735094033e8ec28e6a128000c9f651cd425000193aca39a84a019f6360873509404be4f310e6a128097c9c621cd425013993ec039a84a00cb66d8073509404bc5f43ec6a128067c9c73d8d425000f55d0db1284a01162fa1b7150940006cc39ee0a128000d9b731c1425000717b093b664a00021fe15768c9400143e42aed1928007cac7650a32500cf7190
  | 17 => 0x144248d8e841cd42884fbb1cc839a8510803635907350a213eec72a0e6a144200d8d541cd42884fbb188239a85109f763d007350a2100c7743ec6a144201aae84d8d4288491998e7b1a8510806aba116350a212466639ac6a144200e8f4358d428840f3590ea1a8510802abe194350a21246c639a86a144200dc4731c54288401c9acab1e651096a3be1971cca21004d7c22e39944200c3c74595328840187ccbba265108030f597744ca210064e3a2c69944200c7565dc532884018eaca38a65109fe5be19750ca21006a7a1aea1944248d4c435d4328840f8dcc2ba8651081f59985750ca21004b6c3aca1944200d2e655d03288401a5acaba065109f763e0d740ca21246c641ae81944248caf635d0328849195ac6ba0651081f69985740ca2103cd7c3a8520c4201aaf8650a418840f95aeca148310802e320d4290621005d3c0a8520c4200c3c74595318850d8d8e4b2a63108030f997744c6210061eb2ee898c4200c6e65dc931884018dacbb926310a761fe19750c6210043fc3aca18c428687d87594318841199cc6b9063108031b99576c862100636bb2cb90c4200d2e655d32188401a5acaba6431081f6998574c862100c5f426e6b0442008bd84dcd60884851dd0f292c11080b1b1d652582212147743c84b044201cae74509608840159906a12c11090a3ba1c325822100536c2864b044200aad840c9608840199ee6192c11090a3ba1f215822100556c2642b044242aea80c8560884050ff0cba8c1108021f61e65182210061f3a4ca304420087f87594608840187ce8b28c1108030f99574182210061eb2ae83044200c5e659cc60884018bacb398c1108031799573182210062eb2ae630442008fb87580608840517f0eaa6c8908021fe1570d91210143e42ae1b224200c9c641cd64484011bf06baac8908223720d75591210047dc02eab2242038f8805d564484111bd0fb9ac89080327dd073591210066639ee4b2242028df8754f63484014bb0a21ec690802b360843d8d210043fc2ae1b1a420287c855c3634840117f08baac6908062f2117558d2100477c12eab1a42008fb805d563484071f100baac690803271d37358d2100657ba6e4b1a4200cac74dc963484918dec4ba8c69080237e1d6318d210054e422c631a42488ef825da43484011bf06bb286908023be097650d210064fb20e6a124232c9c641cd4248401938e9b1a649081e2fe1d649052138d4e41ac920a42008bf845d9314840317908bb26290803271d3634c5212466631ee498a4286c6e765d6214850dacce2bac4290922b320d648852103c76432e110a4242ce8605c2214840117f08b9ec0908062f21173d812121657b12e830242008fb87580604840f1790eaa2c8108022fe117558c2100c5e422eab1842078ec825d5630840317d0fba2c61098f2b1cb7
  | 18 => 0x840153b06282c99081eaba08505932100556c10a0b264200ab68114164c840156b02282c99081e3721d5358f210143f42ee0b1e420087d85dc163c840f17f0eb24879081e2f21d6450f210454e41ac8a1e4207cac7259141c840195ac9b92839081f2b9c964cc72100656b22e598e42008bd86dd131c84e317d0eb226390a2e2f21d644c72103e56392c898e4200cae64dc931c840195ac9b9263908030f991750c7210061f3aac818e4200c3d7559031c840317d09b9ac1908022f613735832111537c32e4b2c4200a5e83dd165884014bb07ba2cb108030fdd2745962143537414e8b2c4200a6d829d1658840147d09b9acb108028f61373596210062fb9ce6b2c4200a6f825cd658850d4d904b9acb108021fa1c43596210043ec3886b2c4286a6e8210d65884014db0421acb109f29de0572596214353741682b2c420087e87105658850d0fb0e20acb108029be09705962143536412e0b2c4200a3e841c1658840147b08382cb1080297a0c70596210052ec18e0b2c4286a6e821c165884014db04382cb108029da0470596211153ac08e0b2c420087e87d0165884010fb0fa02cb10a1a9ba08405962100536c1080b2c420087d8799764884010ff0eb2ec9108031799673d92210062eb2ce7b244200c9e649cf64884018bccab9ec9108031759573d92210446f41eebb2442008dd83dd764884010fb0f3aec91080a1fe1d75d92210145fc3aa9b2442a6c9e7355364884018bceb39ec910803175d673d92210446fc3ae7b244200c5e755cf64884018baeab9ec9108031d5d671d92210054f41ee8b24420287e85dc164884010fb0bb82c9108030f9d265d8e210061f3a2cbb1c4200c3e655d3638840187acaba6c7108062fa1375d8e210045ec26ebb1c4200c3e759d3638840187aeb3a6c7108030f9d574d8e210061ebaae9b1c4202c5e7594f638854b93ce929ec71080a37e1d53d8e215264f3a2a7b1c4200c75759c7638840153d09b1cc710802a7a137358e2100566c1086b1c420287e85dc163884010fb0bb82c7108021f61e6518e210043fc3aca31c42008df8758c63884050fd0b3b487108021f6167690e210143f42ceca1c420087d859d943884011bb073b2871080a1fa147650e210043ec28eca1c4200c6e65dc9438840355d09b1c85109223be1d6390a210074621ac72144286e2c4259542884018bccbb9a8510803175977350a210062f328e6a144200c5d651cd428846593cc839a8510803275907350a214bec6210e6a144200c7565dc542884018eaca38a85108031bdd96550a2100717322caa144201aaf86591428846d99eedb9a85108dba39937350a2119667bb0e6a144297d8f741cd4288465d1cc839a851092333a187350a2124666c30e6a144248d4e851cd4288491a9b0a39a8510803539947350a21006a6b28e6a
  | 19 => 0x5e2fa1f644c93100657ba6c49926200cac74d89324c4019cec438a64989c7271cf645053100667b98c4a0a625accc73189414c401d18c8314629882237219708c5312266c302e118a6200ad983143604c4015e302286c0988032bd92729813100656324e53026200caf645ca604c401958c8b94c0988032b9d3629813100656ba6c53026200cae7418a604c40195ae8314c0989c62f21b74581310045f43ec8b026200c3f75d91604c401878ebb22c0988022fa1c64581310061fba8c8b026200c3c75191604c40195ec9b92c0988032b193725813100657b20e4b026200cac641c9604c4011dd0fb12c0988031bdd76258131006363aec4b026200caf74d89604c401958e9b12c0988023ba1c625813100637ba8c4b026200c6c75189604c40195ee8312c0988032b1d062581310047dc3ac03026200a7885580604c4114bd07ba2ca188a69760f74594310061fba4e8b286200a3e841c9650c40147b08392ca1882297a0c725943114d2ec18e4b286289a5d839c5650c4014dd05a0aca188029b60b41594310043f43882b28620087d87105650c4d14bf06b82ca188229720d70594310051f420e0b286200a3d841c1650c4114bd06382ca188a69760c705943100537410e0b286200a6d821c1650c4014ed02382ca188a69d60470594310043f43e80b28620087d87d01650c4014dd04202ca188029b60840594310143f42ee0b20620087d85dc1640c4058bceaa9ac418823171cd655083100716212caa106208c9c73591420c40f55904b2284188031799773508310062eb2ee6a1062088ec87589420c40355908b128418823331cd62508310462f39acb2086208c9e73592410c4018bacab9c821880335947764c4310066aa8eec9886200c9f76dd1310c40193eec3a2621880333ddb724c43100667bb0e49886200d8c741c9310c4871b90ea9ac01890e3721d315803121d6c40262b0062078be87d5164c840187eebaa2c990802a7a0f54593210054ec1ea8b264200ab581d5164c840f1790eaa2c99080a1fa1770593210043ec2ee0b264200c3f759d564c840153d073aac990802a760e75593210055b40ceab264200ab5819d564c840147d0a39ac9908028f61473593210064eb98e6b264207aae821cd64c844d55b0439ac9908022fa1f53593210045ec3ea6b264200e1f5394d64c844d55b05b8ac990802a7e0d71593210054e41ae2b2642008be87d4564c840117b0fa8ac990802a7a0f51593210054ec1ea2b264207aae82d4564c840155b05a8ac990802abe09515932103d56412a2b264200a3e85dc164c840147b0bb82c990802a7a0e70593210054ec1ce0b264207aae829c164c840156f02b82c99081eaba08705932113556c10e0b264207aae8294164c840155b05282c9908022fa1c50593210045ec38a0b264200a9e8314164c
  | 20 => 0x56c14ca32262008bf87594644c40155f04b28c898802ab20965191310055dc02ca3226200ab880594644c40196ec838a86988031b5d752d893101477c3aa5b126200aae8414b624c40155b08296c498802b360c52d893100557424cbb126200aad84997624c40155f08b2ec498802ab21165d893100575c02cbb126200ae880597624c4014dd0a326c4988029b61464d893100717428c9b126200e2d85193624c40155d093aec498802ab61275d89312456741cebb126200acd839d7624c4018daea3aec498802b360f74d893100657ba4e9b126200a6e851d3624c4014db0a3a6c498922b3a0f54d893100566c1ea9b126200e2f54953624c4014dd0bb9ec4988029b61773d893100557426e7b126200aad84dcf624c40155d09a9ec498802ab61353d89312472729ea7b126200aaf845c7624c40155908b8ec4989223ba1f51d893100476c3ea3b126200aae84d47624c40155b09a8ec498922b3a0f51d893100566c1ea3b126200e6751947624c4011db0fa0ec4988029ba1441d893100536c2883b126200a6e85dc3624c4014db0bb86c498802aba1270d893100556c24e1b126200acd831c3624c4011dd0e286c4988023b61c50d893100557420a1b126200aad84143624c49159d06286c498802b360c50d893100573408a1b126200ae581143624c4014dd0ba06c4988029b61740d89310047743881b1262008ed87103624c40f958c4ba4c4988032b9d3629893100656ba6c531262008be87d91624c40117d0e322c4988023be1d621893100557c22c43126200aac84588624c4011db0f328c498802aba12651893100556c24ca31262008ef87594624c40155f08b28c498802ab211651893100575c02ca3126200ae880594624c40195cedb20c4988023b61e641893100477c3ac83126200a6e85190624c4014db0a320c4988032b9d8641893100717428c83126200e2d85190624c4b559d07aa0c498802b360f541893100717aa4a83126200aae84d4c624c40155b09a98c49896b9394f53189310057340ea63126200ae581d4c624c4b5d1886a18c49881e3ba1f511893100476c3ea23126200aae84d44624c40155b09a88c49896ab3a0f511893100566c1ea231262008ed87d04624c4014dd0a208c4988029b614411893100557c22623126200aac844c4624c40f1dd0e280c4988023b61c501893100557420a03126200aad84140624c4b559d06280c498802b360c501893100573408a03126200ae581140624c4014dd0ba00c4988029b617401893103c774388031262008ed87100624c40f1d904bb484988032b10a765093100656210eca126271c9c73d91424c40f55d05b2284988db2719373509314ce66316e6a1262018ee87d89424c40355d09b128498923331cf625093103e72314e319262008be86dd1324c4c7958c5ba26498a
  | 21 => 0x611cd429052f1790eb1a85209c7271cd6350a4103d57c32c4a1482238bd86dc54290401b28e638a852080a1fa16768ca410043ec2ced1948207caf7650a32904e371906a146520803a358d428ca4100cd643a849948200caf7650932904e371906a1265208231798d750ca4138e8e21aea194827199c835d0329041193cc6ba06520803175d5630ca410064eba2c6194820287e87dd5609040187887baac1208030fd0b75582410161e3aaa8b048200c9c43dcd609040187eeb21ac1208030fdd542582410054e41a84b0482008fb8758060904051bf0ea9ec6a08021fe1570d8d410143e42ae1b1a8271c3f645d463504011bf0eb18c6a0802b32096318d4101477c3aa5b1282008ef87588625040159906b10c4a08231718d750c94103e36312ea1928207cac625d032504018baebb1864a0803275d3630c94100636baec41928200cad74d8832504031790cb8482a091b2e181709054100477c12e7b0282078ec825cf605048d95ec8b90c0a08023ee1d60181410445e43aa8b26620287e85dc164cc4010fb0bb82c9988223b21d5258b310464e39ac8a166207aac8259142cc4111d90eb128598806ab2116250b310466639ac4a1662078ee82dd7648c4011db05baec9188021fe1570d92310143e42ae1b2462028bc87551648c40f958c4ba4c5188032b5d36298a3100477c3ac4314620287e859da428c4010fb0b3b4851881e3b2097690a3103c5f43ec8a146271c9c73d91428c40f55d05b2285189223be1d628ca312246f43ca6b046202c5c7594d608c4058b8eaa9ac11891237a1f31582312256d40662b0462008fb87580608c40187aebaa6c898802a760f54d91310145fc3aa9b22620087f855c3644c4050f90ab86c898802aba0a65d913100556c14cbb226200aaf82597644c40155904b2ec898802aee0165d91310055c402cbb226200c3d751d7644c4e353d063aec898802a760c75d91310045f43ea7b2262008bd87d4f644c4e3c3ca7a9ec898802a760f72d913100657b94e5b2262008be8714b644c40117b0e296c8989c6a7a0c52d91310054ec18a5b226200aaf825c7644c40155904b8ec8989c62fa1f51d91310045ec3ea3b226271a9e83d47644c40153b07a8ec898802aba0b51d913100556c16a3b226200e3751947644c40155d05386c898802ab60a70d91310051fc2ae1b226200a3c855c3644c40153b06386c8988022fa1c50d91310045ec38a1b226271a9e83143644c40153b06286c898802aba0850d913100556c10a1b226200ab681143644c40156b02286c8988032b193725913100656320e4b2262008bf845d5644c4011df04baac89881e3b20975591310047dc02eab2262038f8805d5644c40195ee9b92c8988032bdd0725913100667b98e4b2262008bd87994644c40153b07328c898802aba0a6519131005
  | 22 => 0xb22c0990030f1d764581320045f438c8b026400c3f75191604c801878ea322c0990032dd9371581320065a326e2b026400cb7641c5604c801968c838ac0990023ee1d60181320452f41ee8b286433a5d83dd1650c80187ee93a2ca192ab8710e74594325652fc1ae8b286408a5c835d1650c94dc3886ba2ca192ae9be09745943203d36412e8b286408a5e84d0d650c811c3d09a1aca1926697e0b43594324cd2ec1686b286499e1f42d0d650c933c3a85a1aca192679308743594324cf2790686b286400a3e84dc5650c80147b09b8aca1902297a0f715943219d2ec1ee2b286407a6e82dc5650c8674db05b8aca191fa9be09715943203d36412e2b286407a6e82d05650c8014db05a0aca190021fa1c41594320043ec3882b28648be1c43105650c80f4dd05382ca191429b60a70594320051f420e0b286400a3d841c1650c8114bd06382ca190ce9760c705943203d37410e0b286433a6d821c1650c8014ed02382ca190029d60470594320043f43e80b28640087d87d01650c939c3887a02ca1901e9ba08405943200536c1080b2864088dc835d5640c80f1d904baac81901e2fa1f54590320061fbaea8b206408a9e83d51640c80f1790eaa2c81929b271cd545903203d56412a8b20640287e851c5640c8010fb0a38ac81900a1fa1770590320043ec2ee0b2064aac9c73dd5640c80187eeb3aac819022a7a0e75590320054ec1ceab206400a9f835d5640c81153906baac81929b271cd755903200557c12eab206407aac825d5640c80f55d05b8ac8190caab60b71590320454f41ce2b206408a9c835c5640c80f55904b8ac8190028fa1471590320051ec28e2b20648bc9c731c5640c80117d0fa8ac8190022f61f51590320454f41ea2b206400a9d83d45640c80f55d05a8ac819002ab60b515903200557c12a2b206407aac82545640c80147d0bb82c8190028f61770590324e64e39ee0b206408a9e839c1640c80f55d05382c819022a720d705903203d57410e0b206432aad821c1640c80f55d05282c819002ab60a50590320045f438a0b2064008bd87141640c81153d06282c819002a760c505903203d57410a0b206400aad82141640c80156d02282c819002ad60450590320043fc2ae1308640287c855c2610c80117f08b84c2190062f21170984320143f428e2b00640087d851c5600c80317d0838ac0190022f61071580320146e43aa6b1c8208c5e635d463904011bf0eb18c720803175d56318e4145c5fc32e321c82009af825c643904011df0eb10c520a6727ddb7350a414cf47316e6a148297c9f761cd429052fd1cc439a85209c727a187350a4138e4ec30e6a148271d1e851cd42904e3a3b0a39a852080327d947350a410064eb28e6a148271d8d821cd429052f93cc439a8520a5f271887350a4145e4f308e6a148232d96
  | 23 => 0x581420062fba8c6b028400c5c7518d605089fd188431ac0a100335d8f71581420066a31ee2b028400da442dc560508019aec638ac0a10033518c7158142006d2210e2b0284008fb8758060508050fd0a38ac9990021f61471593320143f42ee0b26640087d85dc164cc811938e6b2285990021fe1570987320143e42ae130e64008bf845d561cc80317908baac3990062fa1f74587320143f428e2b06640087d851c560cc80f1790eaa2c91901f2b1c96450e324bec7ba0e6a146497e8c641cd428c80f3590ea1a851901eab2194350a324cdc7c1a86a146408d8c7350d428c8050ff0ebacc3190072b9d142986322456641a8530c640287e87dd5608c803958e8a12c11912ab320d42582320061ebaea9b226400a9d83d53644c80517f0eaa6c89900a1fa1671d91320043ec2ce3b22640087f855c3644c8050f90ab86c899002ada0665d91320055ac0ccbb226463a9c8654f644c94993ceca9ec8990030f5d475d91324a54f418ebb226463a9d831d7644c8c717d0fa9ec8990022f61f53d91324a70f29ea7b226463e2e52d4b644c80147d0b38ec8990028f61671d913200557c12e3b226463aac825c7644c80117d0fa8ec8990022f61f51d91324a54f41ea3b226400a9d83d47644c8c755d05a8ec899002ab60b51d913231d57414e1b226400aad829c3644c80147f0ab86c8990028f21570d91320045f438a1b2264008bd87143644c92953d06286c899002a760c50d913231d57410a1b226400aad82143644c80156d02286c899002ad60450d91320045fc22eab2264008df835d5644c8011df04baac8990022f61e65191320054ec1cca3226400ab681994644c80156b03328c8990022fe1d65191320054fc1aca3226400aaf82594644c92d53d06328c899002a7a1a53191324bd4f432a63226497a9c8654c644c801c3ecaa98c89918f2b1cb6450d3200d57436c92126400cae76d92424c929938e7b2284990db27193735093200d57436c8a126494cac76d91424c929b18e7b22849902273a1f73509321b6663b6e6a126436e8c64dcd424c811998ec39a8499002d361473509324bec7ba0e6a126432e8c641cd424c80f3590ea1a849901eab2194350932046563b286a126408d8c7350d424c8051ef0ea8ec2990030f9d764985320061ebaec930a6400c3e75192614c80187aea324c2990031d5d761985320045f43ec8b0a64008be87191614c8011ef0eb08c29900b179d5531853200e563a28430a645aacc83508614c8051eb0f288c29900b1d9d651185320072aa9aa230a640087f855c0614c8050f90ab80c2990022fe11701853200c5e422e030a6402c5e7554f604c803958e8a16c099176b320d42d81320143f42ce3b02640087d859c7604c80317d0938ec0990022f61271d813231c5e436e8b0264008be87d91604c80187eeb
  | 24 => 0xa8436acd821c363508011bd0e286c6a10023761c50d8d421b54f420a1b1a8400a9d84143635093359d04286c6a1002b360850d8d420056b408a1b1a8400ad58114363508118b8c6ba8c6a10034b1097518d420046fc3ac631a84b1e8c4258c6350811539093b0c6a1022b320a7618d4258746214ec31a8400c5e769d46350929c3ec93a8c6a1003c310a7518d420062f3b2ea31a8400d1e745d46350929c3ec8ba8c6a1003535c97518d4200786212ea31a84008dd87994635095fd1885328c6a1002b5a066518d420056ac0cca31a84008df87594635095d59f04b28c6a12b7a31086518d424bd4e432a831a8400e1f65550635092f71904aa0c6a129aa7e1d5418d425554fc2aa831a8432e1f85550635094dc3ceaaa0c6a129b875d55418d4200747c12a831a8497a9e82550635092f53904aa0c6a1003a32095418d424bd46412a831a84a6e8e72550635094dd1ae4aa0c6a1002a72055418d420054fc02a831a8432a9e84d48635080153b09a90c6a125fa310b5218d420054fc22a431a8432a9c8454863508111bd0fa88c6a10023761f5118d421954f426a231a8400a9d84d446350801c3aa9a88c6a125eb3a0b5118d4200566c16a231a8432a9c84944635080153f08a88c6a10caa72115118d420070eaa2a231a8400acf82544635092f59904a88c6a10caa7a105118d420054ec20a231a8432a9e84d40635080153b09a80c6a10caa7a125018d420054ec24a031a8400e1d54940635092f59d05280c6a1002b360a5018d421954f422a031a84088de8714063508011bb0e280c6a10caa7a105018d420054ec20a031a8400e1d54140635092f59d04280c6a1002b36085018d420056b408a031a8400ad581140635081153d0db1a86a1267271db6350d424cec6396c6a1a8497c9e7618d4350811938ec31a86a125f631c86350d4203cd743ee4a1a8499d8f731c9435080127b0a38a86a122f2718c7150d420049ec2ee0a1a849cc9c63dc143508031db05baec2a100a3de1d51d854200696212eb30a8400d8c429ce6150801b1884b9cc2a1003179d763985420062ebaec730a8400c5e7518e61508018baea31cc2a11f7a310863985420063abaec330a8400d8c42dcd6150801b188439ac2a100237a1f63585420046f438c6b0a847dccf7218d6150953d1884318c2a10023de1d61185420161f3aaa830a84028f58794461508058eceb288c2a10038d55151185420043fc2ae030a840287c855c061508011bf06b80c2a10223720d701854253f46210c7b028402c3e7555360508050fd0b38ec0a10021f61671d81420446f41ce3b0284008dd839c76050801b188539cc0a100363109739814227e66b90c73028400d2c42dd56050801b1885b9ac0a10036310873581420046f43ec6b028400c5f75d8d60508018b8ebb1ac0a100237a1c63
  | 25 => 0x20018002002001000180000008004000001e00000060000000000800000000080008002000000c0008000000000000080000000000000800400280000000004000800c00000000020000005000200000020000002001000600100000000000002800000000020000000000000600000040008000000800000080020000000000800200000000000000000000400200140040002000000200000060000000000800000000020000006000000200200000000000000800400000000000004000000000000000000002000800200080000048000000800000000040000008000000a000000e00000060000000000000000200000000002000000000000000010000000800000080000000008000000000380000008002000000000000000018002000800000000020008006000800000000020028000001000000000000000000001000000000000000000000000400000000008000000000a00000000000002001000600080000000000000000000000000010000001800200000020018004000800000000060018002001800400000020000008001800000000000000000000000200000020010004000000000000040008000000000000000000008000002800000380000008002001000400000020000004000000000080080000014000800000080020008000000800600000040000004000000000080000018000000000a00380000000000000000002c3e755526190c010ff0ab84c32180a1f215709864300477c12eab0c86078ec825d56190c0195883b92c3218032bd0372586430161e3aaa8b04860287e851c56090c010fb0a38ac1218031b5d752d894300556c20a5b128600acd8314b6250c011df0eb10c4a1a66b3e0d62189430047bc3ac230a860287f875d46150c0187c86ba8c2a18030f10d75185430061fa12ea30a860287f875d76050c0187c86baec0a18030f10d75d81430061fa12ebb0286008fb875806050c0f1b90ea9ac72100a1fe1d75986420061e21aeb30c8486c3f425d6619090d87a84bacc3210032710d73986420061ebac8730c84078ec825d561908050fd0fbaac1210030f10f75582422ce1fa16eab048459c3d42dd5609080193887b9ac1210030fdd643582420062ebaea7b1a8400a9d84d4f63508051bf0ea9ec6a100a1fa1671d8d420043ec2ce3b1a840087f855c363508050f90ab86c6a1002b5a0665d8d420056ac0ccbb1a8499a9c86553635093371904aa6c6a1003175d475d8d421b54f420ebb1a8499a9d841d76350933c9ca5a96c6a1266a761371d8d421b566c16e3b1a8400a5e859c763508014bb0b38ec6a100237a1f51d8d420046ec3ea3b1a8436a9e84d47635080153b09a8ec6a1266b3a0b51d8d4200566c16a3b1a8400cdb709c363508014bf0ab86c6a10029721570d8d424cd4ec20e1b1
  | 26 => 0x4000000200000000018002000000800200060028000002000200000020000000000800000000000008000001800200000040000000000000c0008000000000200080060010000000800c002000000080060000000001000000100000018000000000800080000000000000800400000040000002001800000000060008000000000200080020010002000800000000000008002000000000000020008002001800800080040018000000800200000020000000001000000080040000000001000000000080000000002000200180040018002000800e001800600100080000002001000e001000000000000000000000800c00080060000002000800200000020040000000000000100000018000006800200000060000000000000800000040000000000000800100000000002000000200080000000000000000000000000000000000800400000000000000000000200100060000004000000000000000008004000000000100020008000001000600000080000000000000600080000000000000000000000020000000000000600180000028002000000000080020000002001000200180020008002001800000100020008002001000200000060000000000000000100000008000000000400000020000002001000800000060008002000000000000040010006000000600080000000002001000200180000018000000000800000000010004000000000000000000002000000000000040010000000800000000040010002000000600000000000002001000400080000008000000800400300000008000000800400180040000002000000400000000008000000000000000060018000000800000000060000002000000c000000000000000010006000800000000020018000000800000000000008000003000000000000000002001000200100000000000003000800000000018004001000000080020008000000000600000000008002000000000000000010000000000600000000000002000800000000000000004000000600000000008000001000000000040000002001800000000000000000007000000000000000000001800000000000000000000800000080000008004004800000080000000000000800000000000008004000000e00080000010000000800000080020010000000000e0000000000000200000020008002000000000600020008000000000c00080060008008000800400500000018000002800a000000200000040008004000000000000000008000000000400000020030000000000600080020050004000800200000000008006000000000200000000000002000000080060008004001000000080000018010000000a00000000008016000000000000000000000001000000000000000000003000400
  | 27 => 0x7670000ebd1a2302000000000000000009fc00000000000000000000000bd489e0000000000000c0a000000000000000000000000000fd800118e0000000000000000048000000097c0000000000a6352f33640000006c5000000000000000000000000002ec000000000000000000000000204aba0003a6800000000000000004740004188000000000000000044800000000000000000000000000000245000000000029e000045027100026f10ce479000000051422200000018de1b627624740000000000000000000000000000000000025581bebc40000ad400000000000016e000000000000006e200000000001d700000000007074d31c84c3800000000000000000001674332790000000072e00000000000000600000000000000665000000000000000000000000000000000288000000000038a000000066a7490002fe986ac566832c6c00000000023f5b120000000000000000000000000011954e80000000000000001a20000648ae0908c0003108000000d2400000000000b60000000000000000000000000000000013ceaf10000000bf4b3500000014fe1111858500000037000000000033a3b700000000000000000000294000000000000000000000009925af1f155ec0000000000000000000000058a88e06000c400000000032503c4000000000000000046996ac8425cd3038414442456000a0018000000800000100040000002000000c00000000000002000000000180020008000003800000000000000004000000200180040000006000000200000020000004000800000100000018000000000000000060000004000000000100000000002000800200100020000002002800800100080000002002000000080060028006000000000000000008002000800200100000000002000000a0000002000000000000040000008000000200200000010000000000000080020008000000800400000060000004000000400000080000004000000400000000000000000800200180020000000000000000280000000004000800000000060020006000000000080000000006000000800080000000006001800a000000000000040020000000000800000020010002000000000000040000000000000000180040000000000000200080000000004000000200080020030002000800000080000018004000000000080000000000000000000180060030006000000200000000000006000800000000020000002001800600000020008000000000200000000000002000000a0010004000000000100060000000002000600000000000006000000000000040028008000000600080000008006000000200200000000008000800000180000000010000000a00080000000000000000a0000002000800a0008000002000000000
  | 28 => 0x43e00000004020000001f2000000000036480000000000001b3c0000000000000000000000137e34f00000008eec2117328dd316c2a44218f08d467128012f87429f548780008d00000001c380000002f2a31000000048c000000000022b8000836b1400000000000006ac00000000000000000000000000000095000000036bd9f4601000062400000000021609320000001eb8000b5000000002c200000009ccdb00005678000000000000000071800056c8e3810e0000000000000000000000132e3e324d800000055415d196c000401000299c9da00000000000000001c2af4c00000000009015e80004bf800000046700000000000001da83f42f045229c901c81641e63c0e08a5000500026e800000015a368d1060004dc956c00036125500012126755b61ea800000069a862c0003090001f687be0550002dad4ecc5400000000000000fe8000000aec0000001398252000155c00000000000000880004d2b6f4000ae80000000000000202000125c00002f000000020030eaee5ad20000c681c4000000000000000000000000000000005ed00000000000000001b068db0000000000000000000000000708b0000000a7a0002e9051851166d000077400048b8000000d320000d980009d51e1800191c1962ca2a9143800000000011d200043485f8994a0d000163400000000000006200000000000000000000000000000010a9e5000000024e25805b6b5a4b725847bc00008100000004bf5d10f080006600000000000000000000000000054685cc00081f0002f7c00050100000000000000001fc40004000000548000d3b3b1000000000000000000005e00002ab000000000b80000000002a68000a60000396041c00000000034881c83dd0000000000000000367400000000000010e20000000000000000000000000000018400016ccca86b680000000123750680000000000000000000000000011f46536890000000c230000000a12000000000147c50f6c727ad700000277a3056d25550000000000000000000000000000000000000001ed00005860000000000000a7d518000000000000034c0000000000000000061e0000000d70da70002e8400000067600000001691e89dac4f64b836f2e1800000000000000000000000000000d15000000000000000000000003cc3308d30000945000000000043b266aa3c0005fd000000000000000019f51bcd801d8000000007e00000000000000000000000c412e90000b5c00000007e0000a1900000017cc000148221800000000000000006ac10a12c000000000000000000004d380000000004941a200000000002a240000000000000000a535c980015c40000260000000000000002c1a200000000000005b9000000000000000032000000000d392ac000
  | 29 => 0xb543e12084000036000000076600000000007720000002524000000000000000000009d00019a60000001f7cc5c28f6748838bc40000000000a32000000000092a01e000000000000044b800121400011906f00000006d5000000098f0000c34000000000000000000000000000000006a5800000000044911e00005e7000000000094e0002b3948a21f060ad4852cadc000000000030f00000000006a812180004dc00000000000008f9000252c000ba8070800000086343413f800000000031158bcd3900000000000000000000b02bae00000000000000000000000763000189d3460000002ef800000000000009a05a13af000000000021cb47d09600051280000008f15ff0c8800000000025e400000000000004b200000000000005af0000000000000000226000000054880000003cb30780000000000000c940000004cd8000000b2700000000000000000000000000000000000000061ca04400000000000000000000000cdc00000030900000000000000e6c0000003dd80000000000001cd10288a1000000000000000000000000001089df800000000000000000000002f780000000000000000000000000000000000004f09f600063d80000008da00033c40000005b90d8000000000030e0000000186000000000000020a89c60001a800010460004f828c53f80002b580000004ba00000000000000001e200000000000000df0d236598000000000000000000028600010dc000cd700000000008e40002cd04b6b8b00000017c000000000000002e30000000000000000012c000bf9302800000000033f80006880000003060e340000000000392459354a70c000000000000031e00000000011ac6130000001b1800036d80000000000002b55b8400000028103ba00067f800135e000193873c6e00006c315088f815a00000000000000000000000000601000000000067bb54c000c5700015d59742084c400005e8bf765f8000f800005d380000005ed15b800000000000000019ba00000003dceb4c4a0003464000a4000000001140003813208000000000000027e0000000000a6449300008d8fb049e45a00000004414959ed162cada00000000000004ae35284600002971f40de47a60568000434a4a0000d2800078a65ea560862d4f00000002be032000063000000000000009b4000000000050400041e01688407782c58aed2883d700000000009073ed800000058300014780008b8000052c0000001c98000000b1d0000d3400028500000000000006e2800196c000000000000000000000000000a023880000003521ff0000000000000000085a000000000000000004bb05800000000000000000000000001490000000122000000057c9b0400053e1bd000000070367b172500a000000239475ad050000000000405000
  | 30 => 0x4341c000be400007001f200000000000000cd3120000000c361c2000000000000022e400011066f00000005f1000000000000000000000000001e9800082a0001e080000000000000c587f011e63730ad67c104012a204eee12f00000001b462c6d400013007f86340000832af86331338000cb7000000112a000000000000071e00000000000000000000000000000061d7a260b2d5000000000000009240003d25c6800083800054300000000000000fb80000003932ad8924bec0001ced5760c20000001684cab0e68628000000000000000000037f2a4c000000042800173200020c00000000000000001ac47015070000fc800061d0000000000000000000000041100000000001f10000000000333800c00000041b80016ba0004ada2ec000000000000000000000000000000004da80000000000000000000000000102800000031819f03260060001c7c0000000000000000c9e00031a40002d621100000000000000000000c46000000147200000000000a81290002afd0848340cb8000b0493b00000007d200000000000000000000000000000000000000000040e000000000067993a40000a9000321170e000000000000000000000000000000002abc00087c0000d2402cd8f000145000000000011ed5680932b01c3c0000000002ed95780001cd000014e00000000000000000002c2133c0001800000000000666800000080150d800165ab7b40215d94cc00000d1ce87a000000000013c00000000000cb8b7f00009b000096c1899d1c00000000000000007060000000000000000000000068100000000005a36ad1429b081fa1ca80000000000002f0479e00033a0000000d5f0000000000000569a168d6438626f800000000014080000000000000000000a9800000000000000000000000000130000000000000000000000000000000c8ea2c000000000043c000318000099c4450000000b3a37faae863c04800000000000000000000000000000000000000000000000000006e31831612c8747380000007306d2ad3c702db309b0c84000000000000000000030732c8f2600000000000000006d8800000000045f000000000000012349c0a8b00030340000000000000000cb000000000000b50000000000c3147f82980000000002d1d312b560000000000000225094c1ec27a00017100000002b38b9cd800c7085800000000028a8000000a5500000000000000000001634d0f0000000dce000000000000000000025a80000000000000fe600000007d94ba0000001d64f3600069b907cd1a9d148aaf500000000000000b7a17a000000000000000031cce829ac00001612ce33900005fc3f2d60000000000000000000000000000001d940007d3308000000072e62899b800000000000000000000000000c8c0000001c2daa
  | 31 => 0x24000000087800022d34e8000000000000000172ed2653a8000000000000000000056e52d000171800021b2b4527c84a1aa3339284733579242d2e60000000000000000195b17d77800000006ec0000000e209a8dc800000000010520ec000000129000013596dcdc60000000000a76807000000000000068200007a81b73ce95a987e64149e9bf4d2200000029b5b82000000000000000000000000002ff00000012e0000000000000044854d00000004cf0001f246ba00000030c0000000000000000000000000000006c62a980000000000000c49a781480002120b0a00000014580008e219730640002d700000000000000152029aba000441322400000000003a40007f636600016fa000000022c4260000002ec40000000000000000853000165c0001a4000000000000000015f160eda24b8800142c0005d91c500000000000000000000000000000000000000000000002bd80002de00009380000000000000000bd80000000590000708602978c0005460000000000bc71ee0000a5600014d07b40007ec486ac4c0004652e280000008bf00000000001e0000000000000000000000000006d700007f468a00000011780000000000482c813bd9d4c000086000000000000003c95f400000000030c82f80004df02c800000000000000000000000000000ca70000000000000000000000014d0000000000379000000000000000007bc000b635cf000000024a0000000ab851f000000000000000000000000000001700000000000000189600000014b425c00038c800018637c6cca1dd9200ae00013c5620000000000030a000000170c000562000000000000047f00c00000000b5000000093842499e05aa000000008c0005f0000000000000059180000000004938719672798426a9840007a228d0a780007850000f61026000650800000000000000012c858a000000000000000000011a000000000000000000138dbc000616158000039429d000800161c0002690000000000000000000000000026040000000000000f020aa0000000000000286b2ec000000000111ca70954256864400000000000000000000000000000bd7000000000003f00029e40003be20e80f54544d948d2e7c000000000000134200041a80000000001b4800049a4a90000c680000006ab81d8a5800018d800000000049300002d09c82b980000000001270000000000000190000000000000000000000ed00005900000001204afe0006e6308158400000000000000000002bbc1ae50752816e129e5fc15e8000bd41590002b9800000000000000ea0000002c640002eb0000000000000000000140200000031552c40884fa000002000000000000000000002df86d85e966d89d1ba20ba00000014280000002af400000000000018f200000007b8deeb0d41
  | 32 => 0x3899a035a000000000000044d0000000000b9500000000000000002d040001792c824443c800000027650f409f0000fc00000000000000000000000104d5700002d800016e6cb84ab800000000000000019a00cb00000000000000002cacc00333509800000000a0000b6400000020b0000c343ce00014707ee35f62402580008d400029ad4885b600000009ec8801030001664add223230d0c88a60000b40b32000000020c7285371138000f7e13e3c5a5306b800043280000009dd38b8b2d9180005bb16715d6000000000000064c0001d6c000b901d112bc75c7cf68e0000000740629800000009d0001a58c520000000000000809231912d4d4000000000000000024f800000043f3e58facd6e0006dc80000000000000000000000000000111a000000192c0007ef3a2825000000000000000000f1445800000000000026c40000002ed01980003f200000000005d72228001aa2b3b0000000000000000000000061f000338c00000000003611aa0000a3000138078d47a800000000008799a80000000000000000000000000000000000000001ba000000000000000042e1a94000000250800157c1c100000003e88c2000292c0000000002bfc00000000000000000003e6800000000006e047d3ac00036400014f800000000000006863118001040000000000000000027e800000000000012d800000000021b57b21d66bd9dd547a1eb0002d813501b30000284d0e6092f980014b2000000000193e00000000000000000000000000000367000000021d000293800000000010446b4af33a5b1915540000002370000000000000000000000000000002ea0000000000d2e3bc9cfd6b000000000007589360000000000000000268000000000000000000000000814000b9b000000000000000025b4168c580000000000cc800000010dc00000028e00000000000000922000000000000000001a000181284363d28a555602c0001a80000000000000000026544980012ca124000000141200000019bc0000000002540000000000000097a00000000000000000001dd0d7e9470000000fa4ab10002c0c0000000000000e4000000000000000002b480008e400066f800000000000009d4000000000254800000026c00000000000002f0c9f806900000002ec0000000000000000000000000000046b83b8000cac6a0914000092c00011e8000000110000000000000018d80006191d0323400050c57082712369b4000000000000800020c800000000000001da000000000000072b0000000000d6b00000000000004de9910000506133a5a1476000000000000056d00000011e4a28263a5ec0009a9000000066800009e8000f005050000000000000370800000052107300000000000ba000166e000000000000000051080011500f43a20968e
  | 33 => 0xd9400019b000000052f000152d02ab2869f80000000000002898000673000052444c0000000000000000000000193600000e000000000022480007c800021180002a26d625100000002195ae0000fee0000000001a10000000000145a000560000000000000000000000000000cb10740a4000009000000000000009f4ce400000000000000000000000000000227c0000000000000000000000000159400000000004a80000000001ad8c620001d2890800000000000000001bf058c000000000000150a00000000000000003ae800123200040100000000950000238000b48000000094800000000000009e25ee80005320000000000000000000340c10400000001fc37207000034f41ea704000000018c000000000000000000000000000000002e8c00000000000000000000000000000ae700000001606d400000000000004c98000082000000000000066300000004fcd132acaa7105c5bb0780ba40000006490001a9000000000000000000000000000000000000121800067d800000000000000000000000000000dd880e0002a8800067b0000000b4a3ca4c2800077600060727e4000b91513b3a8da2cc600000000009cb000000175400000000000000000000001af25d62dfb3c0000683000310800000062d800000000000000000000000001f38000000000000000036b10c00000000c400000015acd0e000000000016d3158000e5229707fb531b200000000001a220d50000000000689000000000000023630440007f446000000000001c180000000000000000f6a0000003484000d2b0000ac80000001ce8000000000000000000000000000000006be18ab5c505e000000000000000000000000000003dc00013f000009c8001a9a00012800000007dc00002ec000000000000159200000000007cc0000000000000000000000000060d5dd81f0d8e000000000102cd1d2e301b0000bc800000002ac000000000000056c000000000054750f054cf24000000011cabcc1300000000000000000001b56bb40000000052000000000000000051580000004f7172105c0003c731280000000000001aec0000000002250732a7800000000000000000000e1a0000000000c301bd2e50000000000000000179e99624b80010ba00000000015880000000000000cf41ab95840000000000000000000000000000000014c000000000000000008d20006ba000127274c5bc00006d40b966124940000000000000000000571800090ea9f0f63450582851000000000000000007a80000000a200005fc04f4828001b3849d65516e800000000025f8978ac10000cc00002170002f0000000000000000000003eab39404200029380000000000000000f220000000a540000000000b740006f100036ed7988852b29741b2a4b7553000000079a6
  | 34 => 0x1da00000000000001d54a4cce06579dbc00000052180000000000000000000a332c721d000019c00018d519a000000258c0003640000000000000022a7d8000000000000000000000029c80000000000000b52a42000000081e7d40000fbc000000299a89129a0004e9000000000055baa20000c6700007656e80006b903c82b8ba66a713cdb040000000000a360000000000000c750000000000000000000000000005400002e42b33f10000b9c000000000000000000000000000002592fe000000000006a800000000006940004761fa0d9c000b5f0002cfdae600000000000006ef00000b95320005078000000b5154a80000000000000000000000000000078800050519240000000000000000000660272400077268f26ac70e11a00035e098819e000000000000000000000009120000fb15fc00000012187d4000000000187800000007f800000000000000000000000000000d98000000000051d000000000000000000004ae00040800000007ba6aab6d80002910000000000b2500000000000001900000686746000083c00000900000014f60004950f8000000000000000004d63e3ae700000005f5800000000000000001248b70001810000c83000000000000000000000007fb67900000004c82fb9ab8000000000000000000000000000000000002930000000000000000000000009c000000018e0225b5a05f0b380017342310000000000c7e00003147ce4f9369800000000034980008a800000000005a400000000000005a71ac80000000000000000000000000000000000000000000000002ff80000000002a60000000000399000000000000011fcea400000022b000046b134800179c4dd523a1586700000001e1c0000005e496f00000005598000bde2ef58b8000bdc000000051d4ca0006bf30d000000048b00000002ca0000000d446080000000baa00033b0000000000000000000044c0000000000000000000000048c0000ff40000001519c3000000044d0000000a710000000000000446000140653d00000000003190001198000000000229c9fe32d00000000001c20000000000c3e0000b7800000044480000008b653b8efc0000000000000b3c000000117c000a0500000000000000001ac00000000001a300000003780000000000326800000000022e00009963620002794000000000296d66cb8300000000005406bb000000000047790d40000000000d5400015d00000000000000000000fc69fe5f70001b340006bab3d40000000001344ade000000000160000000029bc00000034e2ea50b200000000018a40000000000000000000000000003b00000010323241d58000a104e2000000035269a00018a80001de05ba0ac00000000009a0e5a000000000000000012100000000fb68d8000000000067b6c0
  | 35 => 0x8000438000000000031800000016b6000028000000000000004300000d400027840000006499300f508cf5db9d9000000000004d0ad0715000000000042c1e2867ccc817502c84c978c40c0000000000000570000000000000000011a40000000000000c7c50100000002a13f700000009c40001b5c84a000253922c0005cc16608ac1f40003a1800000000006700000000000000000c500005f1000000000051180000000000000001ab80000000000000000006000000000000000000000000000000000000000000000069200000000006fc000000000000000000016c41650002a840000004ea0000000000000000000086c0000000efe00000017e464c000000000189e79500000000000004d90000000d2f0000000000c0101d0000a8a0000000000000000000000105845b67e8bb8652000000000000000045580000001bf00000000009b8000000000000030a07854e0ae400003289e000067f2970000000000000000086b0000000000000000144c63a77c00018e800022a000000000033c0000000000000000000115a00036a80007100000a1a93c752cb10000000b8e0000000000b2a0152a70bcc5800000000000028afa48029b800000057e8000000000000000000000061e800000000000000011200006079d5167a000000338400000000000009dcd94000000058868b0000001a4e23d4c88bec000000000061000068e5bb800148200000000007f60002bc000113c00054180019168870000000000000603000000058700016980000000000000e500000000d18000000000000000072a00000002cc9c54c60a4cfe042b695000008cd3a6be9c58cb2b445ff8000d2e9e300000018340002c400000000000000ac46640000000001b9a7fe0000001982c2c00000006a623536e0000d7800009631240006d065a8000d560000000000000000000000000000000017c93d000000028744f0000335800143e7c432a00010e6000000000100c00000000000000000000000000000000000172800000000000000000000000000000155000000000000000000000000000000000000000000000000009db0cc000c4000000000000005f7b3e000000000000000000000000000000000000000000000000030bd77e00000015480000006531398000000095026800000060f11cc506000000000021211b1b6897c00000000000005c49083db00000000000000000000c9c000000000000000000000000005e91c9c35e46e0001a1529400000000000002ad00000000007680f480000000000000000000000000000138ed8b68100000000004058000000000334a5d400000000012800000494fb80000002ce0f2800000000030317700000001ea800000000000000000000000d58001930d4921a12246620000001b240005703828000000000
  | 36 => 0xba15969c256a24e800000048332b800038b000065160400000018c59a200000019f87480000001180000453176ac9800010d000000000099546c800000000000000011220004c301455502f200007a009a0000cc000140cbad3ae1068000000150000000024800016240000006478000000000000000000000000000000000000c4000000065800000000000000dd30b5204a5f58aafb54e61a3582800000000036900000000006ac80000000000000000000000000000036800029500000000000000e9c0000000000ee00000003799dcc000c03000361c0000000002a29b940bf0002360000000000074c00000014f80000000000000fcc000731241001000000018bb258000c9a0000000aee0983eea2a80f0000000000060c0000002d556ca0000002b7800086f073b68400014f00006c032a00000000000000001e680000000005f40000000c1f4c50000000000000000000005d0002a50ed200000012b80000000140000b7cc50000000098c00000000e5304000000000124200044780000000000002cc4000000000000000000000000000000000000000000bf30001e7076c903000261c000d65000000000000000006c4000000000318400090e5b880000000004d68000000000000318c000000000000000000000000000000000002f84000430182aa3190a3145e100000000001b9800000006500005800000000000b8400000000034f80000005e6ae14bd0000075000022a00050600000009ed00000000000003d4800127e0002ea351c0000000000000df40000000000000b0b17e8348000000000007d7d245e2480000000860000000168600000000000000000000000000a62000000000053f3f521fc0000000002048424000000000000000000000000005ac0c190a49aa0000002e3955c00007100000000002202f70000a7400000000000005f506a156400054b8000000000333000000000032505305701826bd00005447100002a410300000001fe4000b18328a4dc00000000002bc000c5a00021c814a99a00000012667e700032a400009125180000000000000000f1e15800000019780000000001b7e00003a00000000000001448d20c002c78000000000000000146810e0eaac29492c4c4d706e1796cef2d880000000005b5309400033f57e0000000000000000000000000020cceacd3400000000000000000000af200000000bc00020439e00000000000001d4000054153f07442ee15000000003ee0005fa800000000000000000005a20001e8400000000000013cc00000000017e449a1368000000ac7000000136c0000002bb4000000651000000000000000017f8d67051800000000037a929400000000020c05380003728000000713459800000000000000000009ec0000000000000000073
  | 37 => 0x116ab4d000000000048f00000004c800011e000000084700000000000000002fd948c00000000000c600000012b027000000027b8b245df000000000000000020f436a34e36200000007fd00011b4e9000000000000000005e280000000680000000ac60001be90a9ad45a00000b180004611d900000000006648000888170000000000000000000000007840000c113d2c2237d94080007f500000000000005fa33300001c7582000073e00005e80000003c9602000000000000000000000000000000000dd26132fec22e000000000000000000000000003230e580009e8bb50a100000000006b78000fc20006d480000000000003634000000000000000038d00017040000000000b806d0d0000010e800001300000002400001220000dec0000000000000c0b00017095728ec3cb00011c210139b25180000006c9a68819091f0000e49a2ebf133c80380000003aba3204760000000000000000000000000060300000000000000002db423a0000001a08000af000026ec45200000002f00008031d500000000005b3800165cb8f000000045e9340001eb400038000000000000006e180001080000000ab000021c000000122000000000000000000000000000ceb0000000000dc800000015b60000001a3c0000002b900003240000000b0859a3e500036e00000000202104000000000000000003e29aab1400000013c80007500000699ac4972725000000000000000000000000006bf80013f6acc00000016f80000000000000000000000000000000000000000003743699282a110002f540000000000000000000000000000054a0358000000052000306c00000000001380000005e8000000047042a000000000000000000000003770000c6400000000000000000000b712641c800000000004646da8000000000000156800000008e000000000051900019863c6000000000000000033e40000000001e300000005a4800000000000029900000000000001196c44000000000000000015f918c9c62c9a4d492c480000000000000031d80000000000000000000000000373c000000000000000000000000000000004b480000000001262b6020c000000000000088815580000000e36060e6000037500031b5702000000007400085b00000000000001ed800000000000034300003c00000001146000000000000000000000000f600000000000003900000000b640000000000000c1c0002d180000005040001a52d4626631d800014e59500000000000000000472b9264aad4c000000000092c000000000109000000000000000001ae000097946c00058f8001a700000000000000000291000000003343c00ac0000003110000000378420000000086600000000000000000000bba6020001899b960000002258000742281800019221
  | 38 => 0x5fe800000000000022b80000000000000000000632800011800008a000194004300013d400065e3df2c311e800008034c400082459e1050c5e00009590381ac0006d036b1a6c000000000000000000006000000000000000000ca400000000003a50001a6400028d5b711751be7ca025083000000000000000000000001a980000000002e100002a41fb350c0000000003294000a350000000000000000000000052335aa3d93b400000010a154e0003e88000000000690000000012515f00000008ca077a09cba6053169800000000027c00000000005a717915047bc0001ff02500000f800000000000ee07c47da4f2000182876e00000000000000000002ad40008520000000000000000000000000009680019d00000001e184cc5a4070197575600051000000000000000000000000000000000017d19e80000000001458000c688556a1000000000000000000000000000000000000000000000014100000011d4a2e13b800152400036ca4110ec20d596227000000000000000000002d6800077a0000000000144dc700000006f6000000000000000000000000006a10001cbc000dd00000000f86000195000000000000000006c600066c3614000000000000000000000000007d07240ce8000000cb400020e193a00039c2c3c00000000037384b000058e109c00000031e800000000010d800131c00000000011f000000036e901e0000000000000000000000000022c0000000000410037800000000000000000000006638d2000000000000000000006df00000000000000e7837c000000000000000000000012e85710af09f000000000000000000002d40714000000000000000080035b15448660000000000000c740002bb80004eb5910000000000000000000000045280000000002530c7c00000000004c400000000000000006dd32280000009ca2d9a6dc000000000000000000000001700008dd000000000000000000013a65665408000000000000000000015b2901e25a3400026d800000000000000000000000000000000000000359800000028b8000000000000000000000000000000006df11980000000000000000000000000000000000017c00002e283b0000000a6800012397200002160000001660d704b90d08d544ea626993d0881a237314380007c137000000000000001c8c5e20000ec0000976d2d6de19098fa372130800162200000000000000005e500019b8b380000000ff442f60ba2a400096b0001c24fbc6b41c7800184877a0000cec746000000000000000002b8000000611000000000000000000000007612c6000000007a0000cf80000000370000000000000000000000000000004de53123e80000000000000000000000000000000000000000000000000000974db47b200000013fe00035380
  | 39 => 0x9d095e055a67c9a658601a80000009aa00000001f00000210000000000000000000000004c80000009dc000000000000000000000000000000001ac6a514f534b000000000009f5b369550000914000ac3000000000095a000000011a0b866a80000000000000001a1a443000301c0000006239a540005b54e70000000b884ef00000c400000015246a200000000000000003cfadd400000000002f80000005d98b440009c1000000000000024180018ee9db0000000000000000000000059f0002ba80006c500000000000002ec00012de0000000000000000000217c44600000000000000006db8000b6800000021f40000000002c8400005600000011447b7000077c000000000000000000048e000000000050a800000000000000000000000000cbdaee0000001558000000000000000077d25980000006ad16a00000000000000001192b6447184995be000000199439816e3a88dd16d02f900021c00006c300000000009220001f3045c00049e00000001450000000000af528808f8fca00000000000009f20000000000000000000000045a24a00000000000f3a1f8facaa535e92606ac00000000000000000000000000000000000000047e00000014440000000000000cd20000001b2cac8000000000000049000000000004c69600beac5c1572290f8c0002af8a3800037701680000000004780a98b3673900000000000005269d60000000000000000078e00000013e60000000b3c0000000002ee00000000002ab400000000000000002380000000000d163d7800000029b497a95000000000006851360003b3000000085e2738000000a6800000010a00000001e5c0000000000000000345000000000000050d00000000000308000000000000000000000000000000000000000000000a0b00000000000004bd000000083f000008922673752b00000000000000e45a12a69000000000000000000000000000000000000b4c2929765b9209e0000000ba20004581c70aa00001fc8e5800000000000004683a600000000000000000000000458066000000000000017ec55e66248f19b552c16c6090c0400000000018cc000000000000000000023aa741876000000000000084e00030b898a0b349180000007d900000000000000002dbc000dc4316b10d4d84dc000000000000000000010ae0000000000000d440000000000b9d47300006ec00000000000000005eb1b3501a76a00000344161d00cd0afc0000002ac28017142fc18880000000002ff0000000a58181b3153fa00000000013600000c080006e20006ab000000000017b800020600000000000000d9000000000000000000015f60002728000000000000000084c00000000000000004eb80000000000000000000b330000000000000665800000000000000000000
  | 40 => 0xba0000000000000000000001d00003f02b1800000000000000000000001ec080c00000015900000003cc8000000d9f60a09d977420200023b800000000001cc0001ac0ea322104c5cb09bb0200000006ad800000000000027600000001ff80010f200037c80000000000000000812000000266036400000000000000000000000000000000000000000000000000007e96cb8000e360002820000d30000000046000000000000009c80000000000000c5d0000fd4000b1e2fc1db0cd830715400014a400000011bc00069f000000000000000000000000000000000000000000240400000000000011c083e00025e0000c99000000000000032b1154000000201309cfae000000081c00073e3d200000000005ac80000000000000000ee200000000004ac0000000000f4600000000000000005bc9880f7a00039e9e780da74e0002a1000000035785540000000000000000000000000000000000036456c281b1852f6c000000000000000000023a037800000060e9940000a2f00019497e0845000093c9686a351f80000006771f89b3c0000003912a00000000000000073800000024910f600000000000002b66770000000000000000165200000000000000000000000000b1200003ccb340fc0003138f4e0d0000000000000000000000000004b301c80009e40000000bb64c92fa130830c65760800013080000351108000000000000186e3fc00018e51f807740f24c117a8a03759fb46b000000007d528600f000098c0000000001968000af74d20000000000000000000000000000000000000000000000000000000068200000023ecebe2f60001ba4af450b00000017582c75501dc11d027200000000007761d880000000004e780016020000000428000cb90000000c7e000000000000086210180012526cb69428e80cec8a0000000000ce600012c4a52000000000000000000000018d4c290000d1cf405360000000000ce70088000eda5180000000c2e000000000000099031b8bb02ae68400008dc00000000000000000000001ae80000000000000ffe0000000008c7c7355d780000006ed144990c2d600000017788a20005691a7848c0380002c180000000001490e140000000000000000000000151c2250001ee400000000021859daab000000009bc000000257c0000005cc00013288eb0000001b1000009980000000000000000bc2cad00000000000000000000d7200000000000000006c0a67400000063fa3394ae0000002f940000003c1000000000005880000002620aa1ecca9e0000000000000000000000000000000000000000004fd000000000000000006500006b200000004320000001a14000000026c7b200000000000000000000000000d4500000013067000000000000000075800000000000000000000005de8
  | 41 => 0x273400034006d800000000000000000000000002aa40000002cc000004c000000000003600000019396ae000000000000000000000000000003f300002f6ca300000000000000000c382420000000000f6200026092d43e61223f42330ae800000021d5850ae541b000000000065f064000000000030545b400012a80015ae596153800021000000000000000e50002f60f580000001854c3600000000000000000002d293be000000197d9f80002c2000165e914479aa8ccf400021e800000038900023b400000000000000000000000000a8600000000000000002c88448000000000298000000000000000000000000000ce40000000000c70b4b02da07543000000007f0000000000213cfe4ccf4aeac9059236e4a8b1ac6ca9534989e0c6b60000000001640d0b056000000000012e00000000000000000000000000000047e000000000000000000000000008b14ac866c85c00000020204142846da000000000000000000000000000000000d25412b55105a000000000000000000035f0000000000000000000045900000009770000000000000000000000000001e000000000000000019c40000002b400000000002d14d84db226a0000000da40001c445e02a50e900000000000000dfc0005e642625f40001622a400005006f40000000000680000000000000000000000000000001acc00000064b9fac000a072270a1c0007a500027c400000040b80000000005c48001a0200000c903411e01800000000001351288000000b4000033580000000001d3c000000000070c00000000000000000000f93700986a874cc800174a0000000000000000000000000000000000000000000f3000000000017d0000d3600000000000000005f3800142400040631c800000000034ccf5600000000005ca0000000000000a9b104938400000066a00019882b9000000000089d44c80000000801e40000000c7000028410720000000000000000000076d8b20000000000bec0005f1800000040800000000008c50000000bd6b7a0001a5000000000035a0000718000000153c00040d14e93de123574b2187ac00000035840000003b00000a88000000000000000068c00000000000898001a80b9651e1c7400014a0000d7800000000000000002a900024b480600032400000000001490af0b9e1e30ff80013663e133822e8caa8f709812147784d70000000d48d5224700018d80006af25d834c000000000000000016f800082434b0000000000a1700006385b094023100000c8000000000000000000035b800000000022bc00000007f000000000000000000000000002b3400000003ea1a8040
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x24a0802280251688269a111f8205800994101b1821001e8a00070a9780201b800616000c9282800e8e189f2210a60092090b218d000491869a998f8d8b959e0000041c0324089c8c0394970f19001d0013010001a5802393a31d8515078ba1001c28d007408058090850044000480000106000030050b648435d46150c0142d9210d75d81430050b648435d6619080148d9210d73986420050b64843dd5609080148d9210f73582420054364c425d4635092941e969d17518d424a703d91725d4635080150d971097518d42006a110a81994635092f28e98e095418d420060761d54d44635096760c925535118d421948726154544635096b60c925515118d424bca324984144635092f28c926135018d4219487e6154940635096960c925525018d420060761d54140635096560c925505018d420068555181140635080181c636147150d420060718d85dc14350801c0c429d46398542007031087518d6050801c84631087158142046131d9851cd424c801a0c6461473509320060710d87105650c80181c4361f4059432006071cd851c5640c80181c7361770590324bd23a4b651cd429052f28c9858d428ca410050b64843dd5609040148d9210f735824100607dd483509609040148d93108765093100417662651cd4288567c0c429947350a2100453662651cd4288401c0e649947350a2100523e59541cd428840148e97d0d6350a2100623613730c9608852f48c96550735082103ca32616350d42084b548c9758d435082103e2321d6350d420852f48c9259473509404bca3a636350a325000142d9210d751854000523648435cc615000181d7520d4218540005a124d42184215000f8a88650970085400056224d425c02150001ca14218570085400052364c42dd9428c0018a57420562189304bd23259541cd42c800f28c9858d4350b202ed2325d6350d42c800f88c8758d4350b2000529650321c5634800105d98194735092059703108651cd424800114d98194735092000703190651cd424800148c96550735092000523a5f43d8d42480018c473205635092000623611730c86148001684935084118520006a85098010461480014a9901087650910
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x5020270180311088000c03249875535118d4200601924c3aa8280c6a1002a04a255181140635080180621331328e6a144200c03662649947350a2100590146a10c2b8042a000300c42660651cd4248001806cc0c8328e6a124000aa028d426004118520
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x1
  | 4 => 0x4d
  | 5 => 0x4e
  | 6 => 0x138e
  | 7 => 0x3
  | 8 => 0x4
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x124d
  | 12 => 0x124e
  | 13 => 0x138d
  | 14 => 0x8d
  | 15 => 0x8e
  | 16 => 0x98d
  | 17 => 0x98e
  | 18 => 0x128d
  | 19 => 0x128e
  | 20 => 0x150d
  | 21 => 0x150e
  | 22 => 0xcd
  | 23 => 0xce
  | 24 => 0x9cd
  | 25 => 0x9ce
  | 26 => 0x12cd
  | 27 => 0x12ce
  | 28 => 0x168d
  | 29 => 0x168e
  | 30 => 0xa0e
  | 31 => 0x130e
  | 32 => 0x20d
  | 33 => 0x20e
  | 34 => 0x140e
  | 35 => 0xb0d
  | 36 => 0xb0e
  | 37 => 0x140d
  | 38 => 0x154d
  | 39 => 0x154e
  | 40 => 0x24d
  | 41 => 0x24e
  | 42 => 0x144e
  | 43 => 0xb4d
  | 44 => 0xb4e
  | 45 => 0x144d
  | 46 => 0x16cd
  | 47 => 0x16ce
  | 48 => 0xb8e
  | 49 => 0x148e
  | 50 => 0x3cd
  | 51 => 0x3ce
  | 52 => 0xccd
  | 53 => 0xcce
  | 54 => 0x15cd
  | 55 => 0x15ce
  | 56 => 0x170d
  | 57 => 0x170e
  | 58 => 0xd0e
  | 59 => 0x160e
  | 60 => 0xe8e
  | 61 => 0x178e
  | 62 => 0x95396
  | 63 => 0x94056
  | 64 => 0x138956
  | 65 => 0x209
  | 66 => 0x1409
  | 67 => 0x249
  | 68 => 0x1449
  | 69 => 0x289
  | 70 => 0x1489
  | 71 => 0x14c9
  | 72 => 0x140c
  | 73 => 0x140096
  | 74 => 0x98c
  | 75 => 0xb0996
  | 76 => 0x98b16
  | 77 => 0x154996
  | 78 => 0x99556
  | 79 => 0x3c995
  | 80 => 0x3c996
  | 81 => 0x983d6
  | 82 => 0x170996
  | 83 => 0x99716
  | 84 => 0xd0996
  | 85 => 0x98d16
  | 86 => 0x160996
  | 87 => 0x99616
  | 88 => 0x1649
  | 89 => 0x134b
  | 90 => 0x20c
  | 91 => 0x21296
  | 92 => 0x141296
  | 93 => 0x150c
  | 94 => 0x150b16
  | 95 => 0x171516
  | 96 => 0x151716
  | 97 => 0xd1516
  | 98 => 0x150d16
  | 99 => 0x178b
  | 100 => 0x1440d6
  | 101 => 0x9cb56
  | 102 => 0x9d6d6
  | 103 => 0xa0c
  | 104 => 0x252d6
  | 105 => 0x1452d6
  | 106 => 0x168b56
  | 107 => 0xec9
  | 108 => 0xa0b96
  | 109 => 0xd0a16
  | 110 => 0xa0d16
  | 111 => 0x178a16
  | 112 => 0xa1796
  | 113 => 0x148c
  | 114 => 0x149316
  | 115 => 0xb0216
  | 116 => 0xb1416
  | 117 => 0x20b16
  | 118 => 0x170216
  | 119 => 0x21716
  | 120 => 0xd0216
  | 121 => 0x20d16
  | 122 => 0x140b16
  | 123 => 0x155416
  | 124 => 0x141556
  | 125 => 0x3d415
  | 126 => 0x3d416
  | 127 => 0x1403d6
  | 128 => 0x171416
  | 129 => 0x141716
  | 130 => 0xd1416
  | 131 => 0x140d16
  | 132 => 0x161416
  | 133 => 0x141616
  | 134 => 0xbcb
  | 135 => 0xb4256
  | 136 => 0xb5456
  | 137 => 0x24b56
  | 138 => 0x144b56
  | 139 => 0x28c
  | 140 => 0x16d456
  | 141 => 0x1456d6
  | 142 => 0x148b96
  | 143 => 0xd1496
  | 144 => 0x148d16
  | 145 => 0x179496
  | 146 => 0x149796
  | 147 => 0xd0cd6
  | 148 => 0x160c
  | 149 => 0x160cd6
  | 150 => 0x40c
  | 151 => 0x58b
  | 152 => 0xd15d6
  | 153 => 0x18cb
  | 154 => 0xd0e96
  | 155 => 0x179616
  | 156 => 0x180c
  | 157 => 0x19cb
  | 158 => 0x4956
  | 159 => 0x5696
  | 160 => 0x14b
  | 161 => 0x24211
  | 162 => 0x28211
  | 163 => 0x449
  | 164 => 0xecd
  | 165 => 0x17cd
  | 166 => 0x104c
  | 167 => 0x3d515
  | 168 => 0x1692d6
  | 169 => 0x3c215
  | 170 => 0x194c
  | 171 => 0x3d896
  | 172 => 0x3d8d6
  | 173 => 0x443d5
  | 174 => 0x3da15
  | 175 => 0x1a03d5
  | 176 => 0x15c3d5
  | 177 => 0xcc3d5
  | 178 => 0x14593
  | 179 => 0x19c593
  | 180 => 0x134593
  | 181 => 0xbc593
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2605
  | 6 => 7381
  | 5 => 3539
  | 4 => 78
  | 3 => 9
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (106801+((h/868+packedAt gbK7 (96385+(h % 868)*12) 12) % 3127)*13) 13
  | 6 => packedAt gbK6 (388728+((h/2460+packedAt gbK6 (354288+(h % 2460)*14) 14) % 9743)*14) 14
  | 5 => packedAt gbK5 (225307+((h/1179+packedAt gbK5 (208801+(h % 1179)*14) 14) % 9099)*13) 13
  | 4 => packedAt gbK4 (5642+((h/26+packedAt gbK4 (5460+(h % 26)*7) 7) % 94)*8) 8
  | 3 => packedAt gbK3 (741+((h/3+packedAt gbK3 (729+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff01ffe03ff80ffc0fffffd13e78fb1e31ff
  | 1 => 0x7c03fe03ffc0fffffff03fffeec9a724e3fe3f
  | 2 => 0x8003fffc0000fff07fffc3c030f1c7c703cfcc
  | 3 => 0x3ffffffff00007ffffc003f01f807fc0ff0
  | 4 => 0x3ffffffffffff800000003ffe0007fff000
  | 5 => 0xfffc000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8439002ca00928849402464a801208490e10d5
  | 1 => 0x684016014c405219291028b50648a32060e62a
  | 2 => 0x8bab5402189da44eae8301b0b145c7034b4c
  | 3 => 0x2112cd9a76b2010073cd30063b01f806b40db0
  | 4 => 0x4223f1e39b3ce7ce008602183dfe0007dbb000
  | 5 => 0x73c081001c200608030820203fedf6b0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeaeaeec8e888eeeaeaeaeec8e888eeeaeaeaeec8e888eeeaeaeaeec8e888eeeaeaeaeec8e888eeeaeaeaeec8e888eeeaeaeaeec8e888eeeaeaeaeec8e888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36737
namespace PEqualNP.Outside.L_meta_36737
open PEqualNP.Outside.L_meta_36737.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 9 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 28 := bs5_3_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 396 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384))))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 601 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)))) (concat (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 (concat bs5_5_384 bs5_5_416))) (concat (concat bs5_5_448 bs5_5_480) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 9 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 78 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_3520 : Interval gbAtlas 5 3520 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3539 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608))) (concat (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832))))) (concat (concat (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 bgb_5_1056))) (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)))) (concat (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504))) (concat (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)) (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728)))))) (concat (concat (concat (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 bgb_5_1952))) (concat (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 bgb_5_2176)))) (concat (concat (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)) (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 bgb_5_2400))) (concat (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496)) (concat (concat bgb_5_2528 bgb_5_2560) (concat bgb_5_2592 bgb_5_2624))))) (concat (concat (concat (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)) (concat (concat bgb_5_2752 bgb_5_2784) (concat bgb_5_2816 bgb_5_2848))) (concat (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944)) (concat (concat bgb_5_2976 bgb_5_3008) (concat bgb_5_3040 bgb_5_3072)))) (concat (concat (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168)) (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 bgb_5_3296))) (concat (concat bgb_5_3328 (concat bgb_5_3360 bgb_5_3392)) (concat (concat bgb_5_3424 bgb_5_3456) (concat bgb_5_3488 bgb_5_3520)))))))
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
theorem bgb_6_6176 : Interval gbAtlas 6 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6208 : Interval gbAtlas 6 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6272 : Interval gbAtlas 6 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6304 : Interval gbAtlas 6 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6368 : Interval gbAtlas 6 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6400 : Interval gbAtlas 6 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6464 : Interval gbAtlas 6 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6496 : Interval gbAtlas 6 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6560 : Interval gbAtlas 6 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6592 : Interval gbAtlas 6 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6656 : Interval gbAtlas 6 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6688 : Interval gbAtlas 6 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6752 : Interval gbAtlas 6 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6784 : Interval gbAtlas 6 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6848 : Interval gbAtlas 6 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6880 : Interval gbAtlas 6 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6944 : Interval gbAtlas 6 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6976 : Interval gbAtlas 6 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7008 : Interval gbAtlas 6 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7040 : Interval gbAtlas 6 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7072 : Interval gbAtlas 6 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7104 : Interval gbAtlas 6 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7136 : Interval gbAtlas 6 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7168 : Interval gbAtlas 6 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7200 : Interval gbAtlas 6 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7232 : Interval gbAtlas 6 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7264 : Interval gbAtlas 6 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7296 : Interval gbAtlas 6 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7328 : Interval gbAtlas 6 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7360 : Interval gbAtlas 6 7360 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7381 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792)))))) (concat (concat (concat (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 bgb_6_2016))) (concat (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 bgb_6_2240)))) (concat (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464))) (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 bgb_6_2720))))) (concat (concat (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944))) (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168)))) (concat (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392))) (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)) (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648))))))) (concat (concat (concat (concat (concat (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872))) (concat (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 bgb_6_4096)))) (concat (concat (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)) (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 bgb_6_4320))) (concat (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 bgb_6_4448)) (concat (concat bgb_6_4480 bgb_6_4512) (concat bgb_6_4544 bgb_6_4576))))) (concat (concat (concat (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672)) (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 bgb_6_4800))) (concat (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896)) (concat (concat bgb_6_4928 bgb_6_4960) (concat bgb_6_4992 bgb_6_5024)))) (concat (concat (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120)) (concat (concat bgb_6_5152 bgb_6_5184) (concat bgb_6_5216 bgb_6_5248))) (concat (concat (concat bgb_6_5280 bgb_6_5312) (concat bgb_6_5344 bgb_6_5376)) (concat (concat bgb_6_5408 bgb_6_5440) (concat bgb_6_5472 bgb_6_5504)))))) (concat (concat (concat (concat (concat bgb_6_5536 (concat bgb_6_5568 bgb_6_5600)) (concat (concat bgb_6_5632 bgb_6_5664) (concat bgb_6_5696 bgb_6_5728))) (concat (concat bgb_6_5760 (concat bgb_6_5792 bgb_6_5824)) (concat (concat bgb_6_5856 bgb_6_5888) (concat bgb_6_5920 bgb_6_5952)))) (concat (concat (concat bgb_6_5984 (concat bgb_6_6016 bgb_6_6048)) (concat (concat bgb_6_6080 bgb_6_6112) (concat bgb_6_6144 bgb_6_6176))) (concat (concat (concat bgb_6_6208 bgb_6_6240) (concat bgb_6_6272 bgb_6_6304)) (concat (concat bgb_6_6336 bgb_6_6368) (concat bgb_6_6400 bgb_6_6432))))) (concat (concat (concat (concat bgb_6_6464 (concat bgb_6_6496 bgb_6_6528)) (concat (concat bgb_6_6560 bgb_6_6592) (concat bgb_6_6624 bgb_6_6656))) (concat (concat bgb_6_6688 (concat bgb_6_6720 bgb_6_6752)) (concat (concat bgb_6_6784 bgb_6_6816) (concat bgb_6_6848 bgb_6_6880)))) (concat (concat (concat bgb_6_6912 (concat bgb_6_6944 bgb_6_6976)) (concat (concat bgb_6_7008 bgb_6_7040) (concat bgb_6_7072 bgb_6_7104))) (concat (concat (concat bgb_6_7136 bgb_6_7168) (concat bgb_6_7200 bgb_6_7232)) (concat (concat bgb_6_7264 bgb_6_7296) (concat bgb_6_7328 bgb_6_7360))))))))
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
theorem bgb_7_1920 : Interval gbAtlas 7 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1952 : Interval gbAtlas 7 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1984 : Interval gbAtlas 7 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2048 : Interval gbAtlas 7 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2080 : Interval gbAtlas 7 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2144 : Interval gbAtlas 7 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2176 : Interval gbAtlas 7 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2240 : Interval gbAtlas 7 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2272 : Interval gbAtlas 7 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2336 : Interval gbAtlas 7 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2368 : Interval gbAtlas 7 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2400 : Interval gbAtlas 7 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2432 : Interval gbAtlas 7 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2464 : Interval gbAtlas 7 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2496 : Interval gbAtlas 7 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2528 : Interval gbAtlas 7 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2560 : Interval gbAtlas 7 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2592 : Interval gbAtlas 7 2592 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2605 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)))))) (concat (concat (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600)))) (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 (concat bgb_7_1728 bgb_7_1760))) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 (concat bgb_7_1888 bgb_7_1920))))) (concat (concat (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 (concat bgb_7_2048 bgb_7_2080))) (concat (concat bgb_7_2112 bgb_7_2144) (concat bgb_7_2176 (concat bgb_7_2208 bgb_7_2240)))) (concat (concat (concat bgb_7_2272 bgb_7_2304) (concat bgb_7_2336 (concat bgb_7_2368 bgb_7_2400))) (concat (concat bgb_7_2432 (concat bgb_7_2464 bgb_7_2496)) (concat bgb_7_2528 (concat bgb_7_2560 bgb_7_2592)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := (concat bgb_8_0 bgb_8_32)
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
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaeaeec8e888eeeaeaeaeec8e888eeeaeaeaeec8e888eeeaeaeaeec8e888eeeaeaeaeec8e888eeeaeaeaeec8e888eeeaeaeaeec8e888eeeaeaeaeec8e888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372970 * 2 ^ 32 + 4006144136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36737.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.and,[3,6]⟩,⟨.and,[2,6]⟩,⟨.or,[0,4]⟩,⟨.and,[1,9]⟩,⟨.or,[5,10]⟩,⟨.or,[0,8]⟩,⟨.and,[11,12]⟩,⟨.or,[2,4]⟩,⟨.and,[7,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4006144136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4006144136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36737

open PEqualNP.Outside.L_meta_36737 in
theorem PEqualNP.Outside.L_meta_36737 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4006144136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4006144136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
