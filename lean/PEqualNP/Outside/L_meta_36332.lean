import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36332.Model
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


end PEqualNP.Outside.L_meta_36332.Model

namespace PEqualNP.Outside.L_meta_36332
open PEqualNP.Outside.L_meta_36332.Model
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

def SBf (j : Nat) : Nat := [6, 7, 7, 7, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36332

namespace PEqualNP.Outside.L_meta_36332
open PEqualNP.Outside.L_meta_36332.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x20bf43bd43
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (34+((h/1+packedAt s0K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x80ffffc0fffffe07ffffc0fffe07fffcf8fe3f
  | 2 => 0xff03ffff01fc0ff83e0fff07fff83e034f1fcc
  | 3 => 0xfffc0ffffe000fffc00ffff83fffc0038fe3f0
  | 4 => 0xffffffffffffff000003ffffffff003ff
  | 5 => 0xfffff00000000fffffffffffc0000003fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xa6082046244842014a12c42946214a98186e15
  | 2 => 0xa58c48a1c915658168555259aa92c294b16cc
  | 3 => 0x14316914483a6aaac109a6b12d3588528da370
  | 4 => 0x58a28e2091230d34a5a0308431c63163e001aa
  | 5 => 0x60c30c38e1c38dc739ce38c601842183f6d800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36332
namespace PEqualNP.Outside.L_meta_36332
open PEqualNP.Outside.L_meta_36332.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x60e22a112a4e0001c48000173a0031e3614b1f2635004126918016400000000a80003c9003200000000018152000264200c0000b1288000050700ac00004501830506001000c041000400180ff43bf43fe43de43fd43bd43dd439d43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xc00044070b0a01a1991c7400041d08a1203834ca002f86c04463b9e8a22b129ec9a6805858bc42251888619371b0fa000983c080034800002a3f878c24c0515092093300c3a4f1f018b410299f0b26a108007000001ac0a0c13174f0721b8005e1c3c800fc29000008224000fcb6271400000001d9bc002227160e6390a8c900010c0f428230000000701a0f0006d089544048001585c362e000c8352b99c001f290c400760b8b4c64b3a980807115000200068203808086008501810a0101010001831d0680001d0a828284000c800b8480040002000000034f55243aeaa4871d5490f3ea6a1e7d5143cfa92879e5250f3aa4a1e714943cfa8a879e5150f3aa2a1e714543cfa82879e5050f3aa0a1e7141439f2a0875e5310f3a8621d794f42aea9e859d43d0aeca3a15d54742cea1c859d4350abca6215754c42cea18853e54cca7aa9996750f32bb28e657551ccb3a87196750d329f2a0653d540cb3a86195794f41aea9e839d43d06dca5a0db54b41cea1c839d43506bca620d754c41cea18833e54cc67aa998e750f31b7296636d52cc73a8718e750d319f2a0633d540c73a8618cf953219eaa6435e53c86baa790e750f219f2a4433d54886bca710d754e21cea1c439d434873a8610f948421af29e815d53d033a87a06750e40cea1a815e53102baa6206750c40b7290816d52102eca2205d544409f2a6613d54cc33a87986750e30cea1a613e540c27aa8186750c30b7290616d520c2eca2185d54430cea1e419d438827ea8904f15120afa9a415c534833a86905dd4520ba28a413e540827aa8105794c20aea98419d43082eca2105d54420cea1e219d438427ea8884f15110afa9a215c534433a86885bd4910b6292213e540427aa8085794c10aea98219d43042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xf1e001280000016169a9d9210800882800013061700098820822000011a001c1400001b000000001f8d0d988010048711910f8b00841c8a8000000000218680000e80000ca11b8b9980000a1e98018795138900190e000c0383001585059f00149d17810316000800234080020418000304800008000a59875250e9561d4943a59865250e956194943c35485250e8e62d4543a358b5150e8e6294543a358a5150f155114543a3d895050e8c6254143a5d855050e946154143a39885050e8d6214143a59845050e956114143c550e51d0b154354742c550e51ccb154354732c350e52d070d4354b41c350e52cc70d4354b318758e54c861d6494f2187d9543c861d6550f218758e548861d6494e2187d95438861d6550e21e150d210870d4394840c350d52103154394440c550d511021d6355030c350e520c30d4354830c550e510c31543544308758c544821d6414d2087995434821c6550d20c550f514831543145208758e540821d6494c2087d95430821d6550c20c550e510831543544208758c544421d6414d1087995434421c6550d10c350f524430d43149108758e540421d6494c1087d95430421d6550c10c350e520430d4354810
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
  | 3 => packedAt s1K3 (2738+((h/22+packedAt s1K3 (2584+(h % 22)*7) 7) % 99)*8) 8
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x87ffffc3fffffff03fff07fff07fffff38f1ff
  | 2 => 0xf83e0ffc1f07c3ffc707f8787f87870fd74e93
  | 3 => 0xffc00fffe007fc3ff807ff807ff807f0e78f1c
  | 4 => 0xffffff8003ffff800007ffff800f80fe0
  | 5 => 0xfffff0000000003fffffffff80000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80000040000000000008008800088100001025
  | 2 => 0x128c9488ca4a8612c34348513485122e534692
  | 3 => 0x219529114695206558859502595024e2a58b18
  | 4 => 0x7529ce2294c1aab9add0c4446e667044f80dc0
  | 5 => 0x46318c3b18e6333e36e6e6670c444088fee000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaaaa0faaafaaafaaaaaa0faaafaaafaaaaaa0faaafaaafaaaaaa0faaafaaafaaaaaa0faaafaaafaaaaaa0faaafaaafaaaaaa0faaafaaafaaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36332
namespace PEqualNP.Outside.L_meta_36332
open PEqualNP.Outside.L_meta_36332.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x400a12130c80c002a00080008c00000b11210e7569b1c50f00009400f4e2559200004001a642a9000011c006800a0000010169889606a8017187c38080140018512180010800102ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x562556d16203f10000a1335670d0065690044000000331f6e4000000000024f0060005e5a4300504c262b1d63293400385b7172481c2428465f0b522a4b66043d005c6b112215232e170049084e3e3a58743000001b39064d1e120e54730c5d31143c09016f59003b5718362c2f006c0027210364471961001a3700002d517025076a45564a0f68410032425306968100000d83850683000400011e030003840303010100068004800104038502850b808180004f55243b7294876d5290eeea2a1dd14543cfa9a87b75150f68a2a1cf95043b7290876d5210ebca6215754c42d6a10853e54cca7aa9996750f32b6a9c65af438cb5a87196750d32bba8a6574514cb9ea6996bd0d32e721a65ad434cb9a86996350d32f3a8a65e4514ca7ca8194f55032b7290655e53d06baa7a0db94b41b6a96833e54cc67aa998db94b31b6a96639d438c79a6518cf950319eaa0639d430c6dca418db54831e6990637a500c6f2a018cf953219eaa6435e53c86baa790dd94640baa8c816f52502d8a4a05794c40aea98816e52102daa4205d94440baa88813e54cc27aa9986750f30b7296616d52cc39a65985d94630baa8c619d434c39a64984f950309eaa0616e520c2daa4185d94430baa88617651882eaa3104fd51209e2a2413e540827aa8105794c20aea98417651082eaa2106dd0f10daa1e21e632c43ca65885d546109faa2213c54442bea6885714d10b7a92216c524436ea8886d15110eba9a21d4534436e86886d50d10f3a9221e452443cc6488794c910f9a8221f230443e260885d94410
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xa82796ba690ab00614712a0638000040000031a880108000800080140202103c354d4210b154314532a3592434cac46150d32e1d85434cb846150d32e150f514cb854314532c350d520c70d544c831c650d500c74932540319358c525030d4354b30c355132cc21d6315120e150d32c43145414d108d19543443445314910991953244385434c910e450d30443c1324c110
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xc204000a0cebb0a86994877650f514ca823aa869922181195434c910
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
  | 3 => packedAt s2K3 (960+((h/8+packedAt s2K3 (912+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s2K2 (200+((h/1+packedAt s2K2 (196+(h % 1)*4) 4) % 11)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x87ffff07fe1fff07e1fe1fffc3f81ffe91f33f
  | 1 => 0xf81e1ff83fe1e1f8fe1fe1c1fc3fe1c16ecdcc
  | 3 => 0xffe01fffc001ffff001ffe01ffc001ff8f0e0f
  | 4 => 0x1ffffffe01ffffe00001fffffe01f00ff0
  | 5 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x90400110802000002022024440484444005115
  | 1 => 0x12c4223194028228620e208cc412c48c26c54c
  | 3 => 0x218d54430d55515b11155411aa8189398b0e0a
  | 4 => 0x65119884291055959541102133251811d00aa0
  | 5 => 0x461910e6319999e6d999993822061021fda000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeeeaa00eeeeeeaaeeeeaa00eeeeeeaaeeeeaa00eeeeeeaaeeeeaa00eeeeeeaaeeeeaa00eeeeeeaaeeeeaa00eeeeeeaaeeeeaa00eeeeeeaaeeeeaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36332
namespace PEqualNP.Outside.L_meta_36332
open PEqualNP.Outside.L_meta_36332.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x689320001c02314872450a8200a851d008459722892004c7c020508c025003c0001cb09800000f05002168334ac0000c58da720602000d02001c2000040080100ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x3f0000000000001c002200170072060011425d151400510865260434104e0025531e0073614736194535400d0000000712003c445e320000005800641a6c33003b2e6f00003a70745c0b246a6b2f462c6939215b0a054c163143564d6d09710c3d4a4f1f2b29606e2a0241525f031b680e5001183e4938664b5700370000003063546200005a2d27005513286748000000001d0000002300200f59000300028019028000858b860587000480010180818011010e01018d00008202050080010200014f55243b7294876d5290eeea2a1dd14543cfa9a87b75150f68a2a1cf95043b7290876d5210ebca6215754c42d6a10853e54cca7aa9996750f32b6a9c65af438cb5a87196750d32bba8a6574514cb9ea6996bd0d32e721a65ad434cb9a86996350d32f3a8a65e4514ca7ca8194f55032b7290655e53d06baa7a0db94b41b6a96833e54cc67aa998db94b31b6a96639d438c79a6518cf950319eaa0639d430c6dca418db54831e6990637a500c6f2a018cf953219eaa6435e53c86baa790dd94640baa8c816f52502d8a4a05794c40aea98816e52102daa4205d94440baa88813e54cc27aa9986750f30b7296616d52cc39a65985d94630baa8c619d434c39a64984f950309eaa0616e520c2daa4185d94430baa88617651882eaa3104fd51209e2a2413e540827aa8105794c20aea98417651082eaa2106dd0f10daa1e21e632c43ca65885d546109faa2213c54442bea6885714d10b7a92216c524436ea8886d15110eba9a21d4534436e86886d50d10f3a9221e452443cc6488794c910f9a8221f230443e260885d94410
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1a89600c382006494010aa6b8800081e004a0a62472c3440450421c354d4210b154314532a3592434cac46150d32e1d85434cb846150d32e150f514cb854314532c350d520c70d544c831c650d500c74932540319358c525030d4354b30c355132cc21d6315120e150d32c43145414d108d19543443445314910991953244385434c910e450d30443c1324c110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x100c10a0cebb0a86994877650f514ca823aa869922181195434c910
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s3K5 (826+((h/15+packedAt s3K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s3K4 (3471+((h/39+packedAt s3K4 (3159+(h % 39)*8) 8) % 155)*8) 8
  | 3 => packedAt s3K3 (952+((h/8+packedAt s3K3 (912+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s3K2 (199+((h/1+packedAt s3K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x87ffff07fe1fff07e1fe1fffc3f81ffe91f33f
  | 1 => 0xf81e1ff83fe1e1f8fe1fe1c1fc3fe1c16ecdcc
  | 2 => 0xffe01fffc001ffff001ffe01ffc001ff8f0e0f
  | 4 => 0x1ffffffe01ffffe00001fffffe01f00ff0
  | 5 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x90400110802000002022024440484444005115
  | 1 => 0x12c4223194028228620e208cc412c48c26c54c
  | 2 => 0x218d54430d55515b11155411aa8189398b0e0a
  | 4 => 0x65119884291055959541102133251811d00aa0
  | 5 => 0x461910e6319999e6d999993822061021fda000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeeeea0a0eeeeeaeaeeeea0a0eeeeeaeaeeeea0a0eeeeeaeaeeeea0a0eeeeeaeaeeeea0a0eeeeeaeaeeeea0a0eeeeeaeaeeeea0a0eeeeeaeaeeeea0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36332
namespace PEqualNP.Outside.L_meta_36332
open PEqualNP.Outside.L_meta_36332.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x11200200002800000067c00000015804e3401d3438028484000c389400914994912a802160e19505360001844051970084c8b3c000131e24054100710000400000fff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41f741fe41fd41fc41f441ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x461fb308c2fea8985f95130beaa2617c544c3bc86987750d30bfa92617c524c3be6498774c930bfa8a617c514c3ee82987d10530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861f7410c3e882185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83ee83907d10720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef42883d885105f94620fb28c417651882faa3107d54620baa8c41f741883e883105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc84907b50920f719241ed32482fea2905f14520fba0a41f441483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf29041ef42083d884105f94420fb288417651082faa2107d54420baa8841f741083e882105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fba0e21f641c43ea83887d10710fb98e21f631c43ea63887d0c710fb90e21f621c43ea43887d08710fbaa621f654c42eca9887d55310fa2a6217454c43eea7887d94f10faa9e21f453c43ee87887d90f10faa1e21f443c43eea5887d94b10faa9621f452c43ee85887d90b10faa1621f442c43ee65887d8cb10fa99621f432c43ee81887d90310faa0621f440c43ee61887d8c310fa98621f430c43ee41887d88310fa90621f420c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085d54610fba0c21f441842fca1087dc4210fd884217f54442fca8885f55110be2a2217f53442fca6885f54d10be29a217f52442fca4885f54910be29221f741443ec82887d50510fa20a21f731443ec62887d4c510fa18a21f721443ec42887d48510fa10a21fb10443ec20887dd5110fb2a2217654443eaa8887d15110ba2a221f753443eca6887d54d10fa29a21f743443ec86887d50d10fa21a21f752443eca4887d54910fa29221f742443ec84887d50910fa21221f732443ec64887d4c910fa19221f750443e6a0887dd0110fb20221f540443e880887dcc110fb18221f530443e860887dc8110fb10221f520443e840885fd5010bf2a0217d54042f8a8085fd4c10bf298217d53042f8a6085fd4810bf290217d52042f8a4085f94410bb28821f741043e882085f94010fb88021fa10043ea20087e44010
  | 1 => 0x6519077e8320fdd0641bf284837d50906fea6a0df14d41bfa92837c52507ee82a0ef90541bfa82837c50506fca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50107eca820dd95041db2a083f753107eca620fd54c41fa29883f743107ec8620fd50c41fa21883f752107eca420fd54841fa29083f742107ec8420fd50841fa21083f732107ec6420fd4c841fa19083f750107eca020fd54041baa8083f450106fea998df95331beaa6637c54cc6fca598df54b31ef99663dd32cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea94637e518c7ee8318fd10631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7be6498f74c931fba0a63f4414c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831f7290636e520c6faa418fb54831b6a90637e510c7ee8218fd10431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87dc6590fb4cb21fba0e43f441c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621fba0c43f441887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f719243ed32487ee8290fd10521fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410df94421fba0843f441087ee6210fd0c421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40dfa1e81bd43d02fca5a05f54b40dfa1681bd42d03eea3a05f94740bea8e81f451d03ee83a07d10740beaa4817e53902faa7205f94a40bea94817e51903eca3205d94640bea8c81f551902eaa3207dd0640fa20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a817451503ee82a07d10540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52103dca4205b94840bea9081ed52102daa4205f94440fb288817651102faa2207d54440baa8881f741103e882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730fba0e61f441cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa5185f94630fb28c6176518c2faa3187d54630baa8c61f7418c3e883185f94230ef98
  | 2 => 0x40001201c0000000400200000002002030088000020080080300402c038000060100100300600000003002004010000020180000302a00c0000100201c00800000000080280080080c80c000004018010040000300002002c02802000020088020020000980201c00c0001700e000000020140080000900c0040080903e00403000000008000060180040000000002405002000088018070080080100b00000001801000128000010000700000002200003022016058010070020040000700c008000010060000000f0020140280201a008000020000000200100000016804004018000000060080280000a01401020016050008050140100801401201401000032000040030c0000008020060140700000c0280000000000c0001500c01c0000100e0000400200000000002004030008010140180680400001c0400001202c090000000100180400600c000000280140100100e0380180100401801800008018018000000040080200000007df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290fdca521db94a43bea9487ed5290edaa521df94643fb28c87765190efaa321fd54643baa8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543fba8a87775150ef8a2a1fd14543ba28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e857e51d0afaa3a15f94342bea86857d5490afca7217794e42af29c857d5390bbaa7215754e42bf29485bf4290bde85215f94642fb28c85765190afaa3217d54642baa8c857e5090afaa1215fd4d42be29a85ef4250b7c84a15fd4542fba8a85775150af8a2a17d14542ba28a857f5050af8a0a15f95042bf298857d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ee21e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cafca5197bd0a32f621465df328cbde65195f94632bea8c657e508cafaa1195fd5132bf2a2657d544caf8a89977d0d32ee21a65ef424cbd884997bcc932ef192657f514cbeea2995dd4532be28a65f4514cae8a2995fd4132be282657f540cafca8195f55032be2a0657e530cafca41977cc832f719065dd320cbda6419734c832bf28865f6510caeca2195f54432faa886575510cafca0195f54032bf29e837d53d06fca5a0df54b41bf286837d50d07eea7a0fd94f41faa9e83f453d07ee87a0fd90f41faa1e83f443d07eea5a0fd94b41faa9683f452d07ee85a0fd90b41faa1683f442d07ee65a0fd8cb41fa99683f432d07eea1a0fd94341faa86837550d07e8a1a0df55241bf29c837d53906fca520df54a41bf28c837
  | 3 => 0xa113a5acfa8004fa6316627e000000002e90482d4002f20004bc0018e0006980000037e78d8b9c61e48486a91e00068442826000b78002ea5e641c2603c000000000004ceb80370000000009b8000002583a1091f83e8001f9000000c80004e26ccb000031e000000000007c400000000235148000ca0002d0b600000000000220298000022280000d8000000000008f29852137a525b87c80000051c000951ee0beaf80000009c000000000000018380000000000000346000000005740016080000008c0000034487c0000008e054000d33f8160002df4ba00000000000000b904d000000001fe00010063000072000c6a3b2cea1c0029013e488001de000044000000001180000000088871af70000000006414a895831170205150bab763400000000210088cc318488000001d2000be40000058a53c002eb61600128800000079118270000000017f24c120000825f6c34001f85860005e8430b20000016f0008b45911103a00000000000000000364980013b8000002d0002c92a6000000000000000009261c3280000000000000000000000210005acc4000000000a0d05afc32c0e11ba3900044d3c12c1e0018aa0000004c076800000bd80002a328875860004b8819382d8000980d79973ec898cda9c3f6000000000001ac0000017672cdf0510009680000053c0b0b20c2050000cd2942309e4049ce0da8c50293a5044193e0a7232c2587a97628ab0f30dd0008a0001910ea6d4b318852abe17e97112a5cd4ca7a000854000000003808e8000000007f0d7190a6cc21bb4040000000019e9ec000004584d802000284000001506264e00000005c028f81205a013ca510f3048e8f98780d8b1c000f531236c43000000000001aa250000000000007dc000e9000c142e1a44a6a98c585d62a810bf1b705a000f794b3705b87605b5f4000000d45941c4378635c24a46c9a950000044170000c7c0000000000143068000000000006325e00017b41ea20482302000c0d7218000000001c8000870000000d20000000033c000000000002fc3304a3f46b0002d7000b3d1927300000081ad119c6a1462ab0620013180100058ceb9015080e82f0004ec2f17725b0520002492b0008e03b85544e924000120006c87a2470003315a00000000000265000001450e70a04295a931096000001d30003ac8607938aab40003254857cec8000327100022f392c08c530a2722dccf8f827ca614b06045c5a4f681f1a49a566aa80006d8de24e08a04c56800000560001856084fc1aabc4320000000000000130aef0e03a865ab83804d0bd1811827755c9022ee3fd76800192000a880000088000000606b90dc8f1152bc4d8a2400022c002a754a905488000ec000560001302803513c32a0010f2073a22ad2b0000000012b800000244000000000f400000
  | 4 => 0xb600000000115a485e8000000005265d51980048c4541996812eb08001553e8681640b02169085126c4803789e800324000000f939e000ed0000000006d00051e83000174000388ea0004b2000000005ce510071e258c39039800234264000000005005d2365ca70c0015e0f4000de9431121f8179620002500007218aa8000000000c4406800546484f0aec426600ad95218e30d0d912100435591273560000000033a8d0ac800000aec00093000760208002ae670002d9000a48000004861f4000d600092c000560fe3f41d9a51caabd900873be000ff8000ae001620d03d0000e5000000000159e06360003113b0f6ba033a6b49a5e40028d2ec0d000201000840a71ea6243d86681402cbc082000000a24b29e517c084a49e91b022936800000a2c0017c3607081f0184ea6d08fb1c1cc3bc6025e560b4c472ff4fe0001011b6024705204463a8fc00211554ac4001ba000ad807a5f4e4371310000008200022a0004b47d94d264a846f95c21c771801ec000030ea8e10a88f0b09a70c29516589c566a753420a412094001fd2ba05d00000150af55f93300094057007000a7d350005ea60d229d0000204be800000020e631e0004d50b1e73b6000799c1118568ccae60380151ead22d4bf9571931663b9408833c828d3214649471c918af5c6b511081a46a3a16029a41ca888b0b130ca14000004b0b881f92449e504292ce1363450a0b830e000552552da51d06a3e3d68689709e016b541b80362cc205c88435a9d0929055b47596dadd2ac14d370f74067353309a188aa43e0
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xc52c43365410710d554c31c42e6620c710b958831c42d66308710b558c21c43655208710b598f54c42d563d5310b998b54c42e562d5310bc58354c42f16015310cd99054c43716015310bc58353c43555314f10b998853c42e56214f10bc58053c42766590f109d59643c42e66290f10b958a43c42776550f109d19543c42f160d4b10b598c52c42d56314b10d954852c42f16014b109d99642c42756590b10b598e42c42d56390b109dd9542c42746550b109dd9532c4274654cb109d99432c4275650cb10f14c832c433654d0310cd95140c42d76350310b518d40c42e76250310b918940c42d66310310b558c40c42e66210310b958840c42b6640c310ad59030c42e6620c310b958830c42b66408310ad59020c42d66308310b558c20c425e63152109758c548426e62152109b588548423e6414e108f590538426e6214e109b588538423e6414a108f590528425e6314a109758c528433654d061097d8d544425c63551109bd89544426c62551109dd85544427461151108fd91534423c6454d109bd89534426c6254d109b988534426d6214d108fd91524423c645491097d8d524425c63549109798c524425d63149109d997414433454d05109d996414427465505109d9973144274654c510d514d31442e6620c510b9588314427665c85109d19521443645248510b598c21442d56308510bc582544427664951109d58254443716095110b5d8d54442d46355110b9d8954442e46255110bcd8154443366415110bc58253442b76454d10ad19153442e76254d10b918953442f36054d10d554c53442e66214d10b958853442766590d109d59643443345490d10b998a43442e56290d109dd9543442746550d10cd15043442f26010d10bc58043442f16094910add9152442b46454910b5d8d52442d46354910bcd8152442d66314910b558c524436552149109d99642442756590910cd15242442d66390910b558e424427765509109d19542443345410910bc98042442f160109109dd953244274654c9109d9943244275650c910f14c8324437265d4110cd153404427665901109dd9540442746550110cd15140442d76350110b518d40442e76250110b918940442766510110b598c40442d56310110b998840442e56210110ec5004044276658c1109d99430442b6640c110ad59030442e6620c110b9588304427665881109d99420442b66408110ad59020442d66308110b558c204427661d50109dd85540425e63150109758c540426e62150109b588540427661150109d987530423e6414c108f590530426e6214c109b58853042766114c109d987520423e64148108f590520425e63148109758c520427661148109d992510427565d04109dd9441042756510410cd950410427561940109e596100427765440109ed9510043725144010
  | 1 => 0xc27761552309d185548c26e62152309b588548c27661152309d584548c27664946309d191518c27765d06309d597418c27765106309d594418c2f160106309d987544c27561d513097d8d544c26f62551309b189544c27761551309d185544c25e6590d30b358a434c25c6550d309d984524c2756114930d3149324c3375410530cd150414c2f160105309b98b540c26d62d50309d987540c27561d50308f596540c3376195030cd186540c27761550309d185540c31c6355030cdd85540c33461550308f990540c25e63150309b988540c26d62150309d984540c275611503097597430c31d54d0c3097594430c31d5410c30cb952520c32d5494830cb951520c32d5454830d3d0d520c34c4354830cd952510c3355494430d994a510c36552944309d992510c3365454430cd551510c3665254430d9549510c27464544309dd97410c27565d0430cd953410c33554d0430d994b410c36552d04309dd94410c2756510430cd950410c3355410430d9948410c3655210430c7553300c34d52cc03097d95300c31d544c030d3549300c27b654c0309798f54c825d63d53209d98754c827561d53209dd8554c827461553209dd8553c82746154f209d98453c82756114f20b358e42c834c534cb209d987548827561d522097d8d548825c63552209dd85548827461552209798c548825d63152209d984548827561152209d987538827561d4e208f990538823d6414e209d98453882756114e209d992518827464546209dd97418827565d06209dd9441882756510620bc580418827661d51209d587544825f63551209718d544826f62551209dd85544827461551208fd91534823c6454d209dd8553482746154d209d98453482756114d209b99642482cd63909209b195424826c654c920d314d32483375410520cd15041482f160105209798f540825d63d50209d987540827561d50208f59654083376195020cd186540827761550209d185540832c6255020cdd85540833461550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d584530826d65d0820cb553420834d53d08209b594420832d5410820d354c42083365494420cd55251083565394420d554e51082766494420cd95151083355454420d594d510835553544209d191510827765d04209d597410833654d0420cd553410835653d0420d554f410827765104209d59441083365410420cd55041083565310420d554c410832d54c8020d354f200826f6548020cb551200834d53480209ed95200825e63d53109758f54c426e62d53109b58b54c426e6214f109b58853c425e6314b109758
  | 2 => 0x6394b41d9d4a52d06d66390b41b558e42d0677654cb419d19532d0676650cb419d59432d07c5320cb41b598c50d06d56314341b998850d06e562143418fd9541106776550441cd99254107555314c41b998853106e56214c41bc98053106f16014c419d59643106e66290c41b958a43106776550c41e550c43106d66314841b558c52107655214841bc98052106f160148419d59642106d66390841b558e42106776550841e950842106b664cc841ad59332106b6648c841ad5923210677654c8419d1953210676650c8419d59432107c5320c841b598c50106d56314041b998850106e562140419b98b54cc66d62d5331b518532cc73654d0731cd950418c66e62951319b58a544c6776155131d3149324c67665d0531cd153414c6d663d05319b98b540c66d62d50319d987540c66e62150319b588540c67a60150319e580540c7646154831d994b410c76552d04319d594410c7365410431b558c410c7665210431d9548410c74d52cc431d954a310c65f654c431d3549310c677654c431d9549310c65e63d53219758f54c863e64d4f218f59353c874c534cb21b918532c873654d0721f14cb31c86e5620c721cd950418865e63951219758e544867761551218f992534863d6494d219dd85534866c654c921d314d324867665d0521cd15341486e662d05219d9963148674654c521f14c9314865e63d50219758f540867661d50219798c540865d63150219e980540867960150219759653087546154c219798c530866e6214c219d984530875653d0421d554f41086756510421cd95041087565310421d554c41086e562104219d597310875553cc4219d5943108755530c421b9588310874d53c8421d554e210866f6548421d354d21086776548421d554d210866e6294f409b58a53d02766194f409d58653d02776154f409d18553d025e6394b409758e52d02766194b409d58652d02776154b409d18552d02f160d0740bc58041d031c53d0d40d3d4f525034c53d4940d3d4c525034c5314940cb14b425035753d4540d514f515036752d4540d914b51503575314540d514c51503675214540d9148515027665d0540d5d4f415035453d0540d9d4b415036452d05409d99441503575310540d514c41503675210540d9148415034e5394840d354e521034e5354840d354d52103565394440d554e51103665294440d954a51103565354440d554d51103665254440d9549511035653d0440d554f411036652d0440d954b41102f160d0440d594c41103555310440d994841103655210440bc580411031d53d0040cb54b401023f6550040c754d401032d52500409ed9540103b341500409b98b54cc26d62d53309d98754cc27561d53309dd8554cc2746155330b358a43cc2776154b309d18552cc27661d52309d587548c26f62552309b189548
  | 3 => 0x5718a000000001cd3c4a68001a741200140ac22ce2f5402c51320013b80081000003801002002000010000000000500000603400004000058010000000001180302600401800008000010000260000000700000c0180c00000c02000014040020040120340000500004001008018008028000120000180600a00401000008000008000060580000a00c0140080000000800001004018000060060000280200200008806000004040010000080100200400c0701200401403800004004028030000140080000005c0080300600c000040140040400900000003000062050020000000280000000c0300100102402c000020000000680103e00c0800203c00006000012020000120000040000000400402002000020000070080080002401a01c020060060300200201000404000004064000010040280a0190060140180700a008008050000000200200401c098010040000000002400012002002000000110000100100000000c0000200a0000080306e03801803034000008040000140100301002e766194b439d58652d0e7661943439d58650d0f4f4354a43d994a5190f6552946439d5825190f665254643d95495190e7760546439d9865090e7561942439d5835150e7560145439b9885050e6d62141439d9845050e756114143b358a4310e3f6550c4397d954310e7761548439d1855210e7661940439d5865010e766194f429d58653d0a7661943429d58650d0b4d53d0a42d594e5190b5553946429d5825190b565354642d554d5190a7760546429d9865090a7561942429d5835150a7560145429798c5050a5d63141429d9845050a7561141429dd855310a746154c42b358e4210a3f65508429bd954210a7661940429d5865010a7661d53329d58754cca7761553329d18554ccb1d5410f329d98650cca7561943329d987548ca7561d52329dd85548ca746155232cb550428ca7661942329d586508ca7661d51329d587544ca7661951329d586544ca7761551329d185544ca7b60551329e181544ca5e65d0d32b398b434ca6e65d0932b398f424ca7664d45329d583514ca7664145329d580514ca3e64141328f590504ca7661141329d584504ca5e63d50329b98b540ca7661d50329d587540ca7761550329d185540ca7661150329d584540ca7a60150329e580540cacd638c83297d95320ca6f654c832b3d95320cb4f654c832d3951320cb4c544c832f1d85320cbc4614c832f14ca510ca7664944329d582510cb4d3254432f14c9510ca746454432d5cc9510cb663254432d54c9510cb653254432d14c9510ca7760544329d986500ca756194032d34c9500ca6e6294f419b58a53d065e6394b419758e52d06e662d4f41b958b53d07575394f41b998a53d06e56294f41b998a43d06e56290f41b598f52d06d563d4b41b598e52d06d5
  | 4 => 0x749580022c3cc450000000017c00015a000001972841a8940005085e4869a54a84cd7b9fa0cc744000381500010717a1aeb74af01f0001914e8084402b92f0001ce000000000002e47027e496000532de2401c94600015400000091424174588d10363ecef89054c0297214d25814c801246160a4bd9104781d0d50000000000002219a3d4a59cc0006248d00026c60d289e10008b91616f0a2aac0c8000000012e2c441e001829d35b80000000000004cc98005fca190c9a60b2018f22360249603e08135a1789f805092a346930736646d7a97047a0010e8004d80005784f2ac02cc12b63cc0001b0000005f96c8153404a4a18ff4c42540680031c1100027a00001cd401a4cc285752f40ee871739e82d0ab06521623037c8c9d212c00d2a9ea414224b58f40f496421210072a4c539324b4310a099a5fa140bb171604a592299f030288020852ae9a0d11da06051cc01841101f8dd95c4c22b0810843de61830274520544ef22257e0b4200a3290854261c71b80c82f8001a6a50ee00037095cdb2e8000a1c372912d2000003092220009c000416000000b0390000002e5000489140e12d40018600029e4b5020d0392001200000008c4000001f8808000003c65604ba7b0fa8ad47ad00000041398126eadc0480000000092a7618a7ccac8001c6670b90003f8000e184a11aae8caa1314a1b4000002469e40000000099d1b800000b480003e31a704ae9b70d21bc000001289f40020c0000011fb0839691cd08006087d8980255403f4860bf190588478b82a6b0c908d9000000389e70aa9400029254424cc61733fe614eca8905e3196080027c9497628a5cc000000a4542168f680047400000000042000132065b0a20b1a3258c2ace107000049d122e0000af0001990e62d8d709849e044638d5000420150001d498ce52d757c758ff23b388569240002800000007800097d4b800000000660000000001430100021c8521b40abfd1cace47c7d0000001b4001538623f0bc5231d0134644001013620006107f2c8b248316d0f263d0c01701c305780683569d4a9198614230400860b09740111f17cbd8269f03baabcd92c00000b0000b40007183084e0006d16a9b0090a608a0cb4acac49a06b0009ad152a42fe510df20813641c72155452194000b75f68ccafa6f44c1593e24d2ee00141a53078338a613b038ae48900c000209710a900033c6196e2127c9038bb05cbf1261fd3580017199213e270002344460dd6a0000563ac7bad13b00d0e285b2a80000012f4285b08f0005de000f01395f4001580000000012722f000bad1811c1d8000001bf000598000f8348b31350000ea00000000000000000db00056d4716545a518f8800140000000000000016399000011c828b35ac0004f06c028acc002c84f020cf29350007d42a000000001
  | 5 => 0x8d5668103f6835830000b8c005e0001f40007700000000021800000994001d55e680d5680042e6e800000216b7c9e83b0005f0000005d27a46e8de1b0a64602383dcb3d4e13c03a5f4ca0e502c0f42580f4d280552a6436aa78f592e208498d18ef062000001313b6000e7800000000ea00044a00165a9521e07945a2713a08c711131cc000b02aa568bc819aed000001222b80007005d0004e2af4228f900090876adb0c690c0000027496d24a8529ca7d3916100092939800116ac800103000350c38003368781f80004819c000005dc000290b233c9b50d0e906a1ece71152e80008ba210003d8de18b08c0010f8000000013faca3ee0001024121c8014100000000074260000000eb8000000001d0fe00000000000000000cb1b9000000002da0ec620000005500015d975082000000c91e4000001a9000000a814a2f0aa40014928a001372b51e0a8c5a8f13d800181af911cb4c9529b124b84dea700000002b9af33a358fca110004
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x13004000966000004cb8528000058c060070400b13a5443400f2a4509f2c04000367949a56dd51d6ab5b06281403462c002f405c000640000000000000490019001cc0838491818b044010000140860000009000c30198ae331686994c57198f424caa2b88a899065525c0544c832c8eec992a219644764c9510cb2232264a8865914cb6054432a8ce5a9ca7a0e475358a53d06a339ea5296839158f5294b41a8eea99065a0e46654c832d0722a9ac4298839454d6014c41c8ac6a90a420e61525805210638b80ca9908391595320c84198ae531e8298e4563548410c662b9cc5a0a4391195324c521c8aa6b108210e45535883108728a9ac020881985496010440a8ae2292649863054580414c2a2b88a699641515c4534c920c60a8b0082906455358831c4322b1aa410e218c9916015310c8aa6b10a7886456354852c4322b2a6419621515c8534c510a8ae629242885147454c53442a2392a629a219154d6214d10c48a931486885247454852442a239aa4292219158d5214910c28a931c84884347459432442a23aa641922191595320c910c28a831a8088624541894044348b1a8020221a85894010110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x4a0000000006280000a0684dd9325443284687995320cb41a048454d6214d10c047458d521491084487595320c910a0484595320c910
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 5 => packedAt s4K5 (24564+((h/267+packedAt s4K5 (21627+(h % 267)*11) 11) % 1163)*11) 11
  | 4 => packedAt s4K4 (32538+((h/260+packedAt s4K4 (29678+(h % 260)*11) 11) % 1031)*11) 11
  | 3 => packedAt s4K3 (2870+((h/18+packedAt s4K3 (2744+(h % 18)*7) 7) % 81)*7) 7
  | 2 => packedAt s4K2 (368+((h/2+packedAt s4K2 (360+(h % 2)*4) 4) % 16)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xff83ffffffffff81c3c3f87ffffffffc047fff
  | 1 => 0xffc0f8f03e1f0fe03fc7f8e0f0f07823bb2cc
  | 2 => 0xffff00ffc01fffffc007ff00ff007ffc3c30f
  | 3 => 0xf000000ffffe00ffffff80000ffff803fc03f0
  | 5 => 0xfffffff0000000fffffffffff0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x20882001080000000040881221111088001455
  | 1 => 0x65196312394aa59611d43a84678a351a19b2cc
  | 2 => 0x8620c52450cd44aad41053208aa84672c2c30a
  | 3 => 0xc4728a48a28866cd5a9902010ccce4236c03a0
  | 5 => 0x8430c00c3118871a3226449c0008041b76800
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaaaa0aaa0feeafeeaaaa0aaa0feeafeeaaaa0aaa0feeafeeaaaa0aaa0feeafeeaaaa0aaa0feeafeeaaaa0aaa0feeafeeaaaa0aaa0feeafeeaaaa0aaa0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36332
namespace PEqualNP.Outside.L_meta_36332
open PEqualNP.Outside.L_meta_36332.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x3401900980005000000308401b009002a3a00000003c12200000000000000288cd0000000250c406000000000020100000002a91038f802a00e0000281930e00bab4e000000024000087801600008921600000000000100000808000001010604081ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41f741fe41fd41fc41f441ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x19092a001600002d801d0011081ca8aca080a10a2697a42a9c07a70cab838706201e1b0b9a0a980d1aa5a2929f2308ac2d1ea6001b80001d81098d830029238f92248b189180058014000f0495801510a529801f8e130019820501a82227a1840697000016828c000010148013ab0e8200020040a1404d857874b860400402500008102280001809086b7296876d52d0edca521db54a43bb28c87755190eeea2a1dd14543af29e855d53d0abca7215754e42bb28c85755190aeea2a15d14542e69906576510caeaa2195d54341bb28c835e53106baa620db94841b6a90837a50106f2a020dd95041db2a083d653107aaa620f994841f2a9083f250106eaa020fc54041b8a80836e520c6daa418d794c21aea98437651902eaa32057d4d40ae29a816f52502d8a4a05dd4540ba28a815e53102baa6205b94840b6a90817651102eaa2205d94630baa8c616f524c2d8a4984f950309eaa0616e520c2daa4185d94430baa88617651882eaa31057d4d20ae29a413e540827aa8105794c20aea98417651082eaa2105794f10aea9e216e52c42daa5885d95310ba2a621d653c43aaa7887994b10f2a96217551842eca8885d15110f9a8221f240443e280885d94410
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x600e480000a02c02d14c9510cb455354841d494d50107515354041d894950107615254041d154d52c42706550110
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
  | 5 => packedAt s5K5 (802+((h/14+packedAt s5K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s5K4 (2694+((h/30+packedAt s5K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s5K3 (312+((h/2+packedAt s5K3 (304+(h % 2)*4) 4) % 15)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe0ffc3fffffff070e1f87e07ffffffe04cfff
  | 1 => 0x3ff07fc781e1e1f80fe3f8ff878783c11b72cc
  | 2 => 0x3fff8007fe01fffff003ff0007f803ffe3830f
  | 3 => 0xc0000007fffe01fffffc000007fffc01fc03f0
  | 4 => 0xfffffff8000001fffffffffff8000001fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x82210040840000000204812110888844004455
  | 1 => 0x94631a091c4a4b1846a1a84713c51a8d0952cc
  | 2 => 0x18862a9228cd896b5083320a2554233963830a
  | 3 => 0x11cc53245188cdb56cc8201446667211bc03a0
  | 4 => 0x21086000611110c68912449860004020d6a800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeeaaa0feeeaaa0feeeaaa0feeeaaa0feeeaaa0feeeaaa0feeeaaa0feeeaaa0feeeaaa0feeeaaa0feeeaaa0feeeaaa0feeeaaa0feeeaaa0feeeaaa0feeeaaa0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36332
namespace PEqualNP.Outside.L_meta_36332
open PEqualNP.Outside.L_meta_36332.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x17290230f2649013d3d86d386924c8111c267840635100000002280963eb5000121c76002696b400000800005458ac02e8c94500200289164e9a000109f0000a9c0018020a94800000000000091294141c000010000094001810022000003204108180007ff5401dfd5007fe5401ff550077d5401ff15009ff52017f94801fd52017f14807ff42017f90807fd42017f10805fe32007f4c805fc32027fd4403fe51007f54403fc5101ffd0403fe4101ff50403fc41017fc8403fe21007f48403fc21027fd4001fe50007f54009fc5001ffd0007fe4001ff50007fc40017fc8001fe20007f48005fc2000ffc4001f710007f84001fd10007d44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x96200efdd431002feca188003f550c400bfa286200dfdd031002fec8188037f540c400bfa206200cfdc831002fec4188003f520c400bfa1062005ffd961002dfecb08017fe65840097f32c2005ff59610005facb08017fc658400b7e32c2005ffd921002dfec908017fe64840077f3242005ff5921004dfac908017fc648400b7e3242009ffd521004efea908027fe5484013feaa42009df5521004ff8a908017ff628400b7fb142005ff98a10015fcc508017fd62840017eb142005ff18a1002df8c50802fff5284015ff2942000ff54a10057f8a508027ff4284015ff2142009ff50a10057f8850802bfe3284001fe994200aff0ca1000dfac30801ef56184003ffa8c2001ff9461000ffaa308007fc5184003ffa0c2001ff9061000ffa8308007fc4184003ff90c2001ff8861000ffa4308007fc218400b7f3042005ffd421002ffca108017fd508400bfe2842005ffd021002ffc8108017fa408400bfea042009fe5021002ff88108017ff208400bff1042005ff4821002ff84108017ff108400bfb8842001fec421002ff82108017f81084001ffb2a2000bfd9510047fcca88012fe6544001feb2a2000bf59510047f8ca88012fc654400fffb222007bfd911003ffcc88800efe644400ffeb222007bf5911003ff8c88800efc644400fffaa22007dfd511003ffca88801ffd544400fbeaa22007ff15110007fec488002ff624400dff3122002bf98910007fac488002fd624400dfe3122002bf18910047fea48801bfe5244001fea922006ff1491003ffe848801bfe424400ffea122006ff10910037fc6488003fd324400dfe1922005bfd851000ffea288023f75144003ff28a2001fd9451000ffaa288003f55144003fe28a2001fd1451000ffe828801ff74144003ff20a2001fd9051000ffa828801ff54144003fe20a2001fd1051000ffe428801bf72144003ff10a2001fd8851000ffa4288003f52144003fe10a2001fd0851000dfec088023ff504400bff2822000ff5411002ff8a08801fff404400bff2022007fe9011003ffa808801ff9404400bfe2022006ffc811002ffc4088003fd204400bfe1022001ffc411000ff62088017fe104400bfb0822005ff0411002fe82088007f81044001fbb2a2008fd99510007eaca88023f4654400ffbb222007fd9911003feac88801ff4644400ffbaa22007ddd511003feca88801ff5544400fbaaa22007fd15110007eec48801bf66244001fab122006fd18910047eea48801bf65244001faa922006fd1491003fee848801bf6424400ffaa122006fd10910037ec6488003f5324400dfa1922001fdd811000deec088007f36044011fba822005fd94110007eaa088017f4504400ffba022005fd9011003fe4808801ff5404400ff8a022005fd10110037ee4088017f62044001fa9022005fd08110
  | 1 => 0x7fc658800b7e32c4005ffd922002dfec910017fe64880077f3244005ff592200b5fac910017fc648800b7e3244016ffd52200b6fea91005bfe548802dfeaa44016df552200b7f8a910017ff638800b7fb1c4005ff98e2009dfcc710017fd63880017eb1c4005ff18e2002df8c71005fff538802bff29c4000ff54e200aff8a71005bff438802bff21c4016ff50e200aff8871000afd6288005ffa944002ff94a20017faa51000bfc5288005ffa144002ff90a20017fa851000bfc4288005ff9944002ff8ca20017fa651000bfc328800bffb0c4005ff9862000dfcc310017f661880037b30c4005ff58620005fac310017f561880017ab0c4005ff1862002df8c31005fff5188029ff28c4000ff546200a7f8a31005bff4188029ff20c4016ff506200a7f88310057ff3188029ff18c4000ff4c6200a7f8631000bff2188005ff10c4002ff48620017f84310016fe608800bffa844005ff9422002ffaa110017fc508800bffa044005ff9022002ffa8110017fc408800bff9844005ff8c22002ff86110017ff208800bf79044002fec822002ff84110017f8208800bff8844005ff04220007feca90002ff6548025ff32a4004bf99520007faca90002fd6548025fe32a4004bf1952008ffec890046ff6448023ff3224003bf9912008ffac890046fd6448023fe3224003bf1912008ffea8900477f5448023ff2a24011ff5512008efaa890047fc5448001ffb1a4000bfd8d20087fcc69004efe6348001feb1a4000bf58d20087f8c69004efc6348025ffa9a4010ff94d20007faa690043fc5348023ffa1a4010ff90d2008ffa8690043fc434800b7fb124002ffd4920017fca49000bee5248005fea924000fb54920017f8a49000bff4248005ff2124002fb90920017fa8490047ed4248005fe2124002ffcc920017fc649000bee3248005fe9924000fb4c920017f86490003ff61480017fb0a400fff9852000dfcc290003fd614801ffe30a4001bf18520097fea29003ffe5148001fea8a400fff1452008ffe829003ffe4148023fea0a400fff10520087fe629003ffe3148001fe98a400fff0c520017fe429000bfe2148005fe90a4002ff08520015fec09004bff504800bff2824000ff5412002ff8a090047ff404800bff2024011ff5012002ff88090043ff304800bff1824000ff4c12002ff8609000bff2048005fd9024005ff8812002fdc4090017fc204800bf61024002fe0812007ffe2090017fc1048003fbb2e2001fd9971000feacb88007f465c4003fbb262001fd9931000feac988007f464c401bfbaa6200dddd531006feca988037f554c401bbaaa6200dfd1531000feec588007f662c4003fab162001fd18b10077eea588033f652c4001faa96200cfd14b1006fee8588033f642c401bfaa16200cfd10b10067ec6588003f532c4019fa1
  | 2 => 0x210fff8a890803ff63484017fb1a421eff98d2109dfcc690803fd63484017eb1a421eff18d2109df8c690883ff534843dff29a4200ff54d210f7f8a69087fff434843dff21a421fff50d210f7f88690806ff6248405ffa924202ff94921017faa49080bfc5248405ffa124202ff90921017dc849080bfd424843ff6a124202ff10921017fe649080bfe3248405f71924202ff4c921007da649080bfc32484037fb0a4201ffd452100ffca290807fd5148403fe28a4201ffd052100ffc8290807fd4148403fe20a4201ffcc52100ffc6290807f63148403fe98a4200fd4c52100ff86290807ff2148405fb90a4201ff8852100fdc4290807fc2148403f610a4201fd08521007fec090802ff6048401ff3024200ff58121007f8c090816fc6048441ffa824220ff141210fffe809087ffe404843ffea02421fff101210f7fe609087bfc3048405ff9024202ff0812100ffe2090807f71048403fe0824204bf5965002ffec928016ff649400bff324a003bf9925002ffac928076fd649400bfe324a005bf19250027fea9280137f5494009ff2a4a004ff552500eefaa928013fc549400bffb14a005ff98a50015fcc528017fd62940017eb14a005ff18a5002df8c528013ff5294009ff294a004ff54a50027f8a528077ff4294039ff214a01dff50a500e7f88528073fe3294001fe994a01cff0ca5002ffec328017fe61940037f30ca005fd9865000decc328017fd61940017eb0ca005fd58650005eac328017fc619400b7e30ca004ffd4650027fca328013fd5194009fe28ca01dffd06500dffc8328077fd4194037fe20ca01cffc86500dffc4328003fd2194037fe10ca005bf9825002ffea1280177f5094009fda84a005ff1425002ff0a128017ff409400bff204a005ff5025002ff88128017ff209400bfe104a005ffc425002ff82128016ff6554035ffb22a01abfd91500d7fcc8a800efe6454035feb22a01abf591500d7f8c8a800efc6454009ffaa2a004dfd5150027fca8a8013fd5454035beaa2a004ff15150007fec4a8002ff6254033ff312a002bf98950007fac4a8067fc62540057e312a004ffd4950026fea4a8013fe5254009fea92a000df54950027f8a4a806bff4254033ff212a01aff509500cff884a8067fe3254001fe992a019ff0c950007fec2a8002ff6154031ff30aa001bf98550007fac2a8063fc61540037e30aa004ffd4550027fca2a8013fd5154009fe28aa01affd05500c7fc82a806bfd4154031fe20aa019ffc85500c7fc42a8003fd2154031fe10aa004bfd8150027fea0a8013fb505400bff282a005df9415002ff8a0a80177c5054009fc282a01affd015002ffc80a806bfd405400bfe202a019ffc815002ff840a8063ff105400bfe082a005ffd962002dfecb10017fe65880097f32c4005ff59620005facb1001
  | 3 => 0xe31aa413bf18d52027fea6a9013fe5354809fea9aa404ff14d52147fe86a909ffe4354851fea1aa427ff10d52015fec4a900bff5254809f7a92a402ff94952016fca4a900bfc5254805be292a402fb14952017fe84a900bfe4254805fea12a402ff10952017fe64a900bfe3254805fe192a400ffd8552005fec2a909bfe61548037f30aa400ff58552137f8c2a9006fc6154809ffa8aa404ff94552027f8a2a90a3ff415484dff20aa428ff50552137f882a909fff315484dff18aa426ff0c552017fe42a900bfe2154805fe10aa400ffd8152005fec0a9003fe6054801feb02a400ff1815202df8c0a9013ff5054809bfa82a404ff14152147fe80a90a3fe4054851fea02a428ff1015213ffe60a909ffc3054805ff902a402fbc8152017f840a909bff105484dfe082a400ffd9532005feca99097fe654c8097f32a6400ff59532005faca99097fc654c8097e32a6424ffd9132125fec899093fe644c8077f3226424ff59132125fac899093fc644c8077e3226424ffd5132126fea899093fe544c849feaa26424df55132127f8a89900aff624c805ffa926402ff94932017faa49900bfc524c805ffa126402ff90932017fa849900bfc424c805ff1926402f78c932017f8649900bec324c805e61926400ffd8532005fec29908ffe614c8037f30a6400ff5853211ff8c299006fc614c84bffa8a6423ff9453211ff8a299093ff414c847ff20a6424ff5053211ff8829900bff214c805f790a6402ff88532017f84299003ff604c8017fb026400ff98132007fac099003fc604c80b7e3026425ffd413212ff8a099093ff404c849ff2026424ff50132127f8809900bff204c805f79026402ff0813211ffe209908ffc104c8037fb2aa222ffd9151115fec8a888bfe64544077f322a222ff59151115fac8a888bfc64544077e322a204ffd5151026fea8a8813fe5454409feaa2a222df55151027f8a8a8803ff62544017fb12a221ff98951015fcc4a8803fd6254443fe312a202bf18951027fea4a8813fe5254409fea92a204ff14951117fe84a8887fe4254445fea12a221ff1095110ffc64a8803fd3254443fe192a201bfd855100ffea2a8813f75154403ff28aa201df9455100ff8a2a88077c5154403fa28aa201ffd055100ffc82a8807fd4154403fe20aa201ffc855100ffc42a8807fc2154401ffb02a200bfd8151007fcc0a8803fd6054401fe302a205bf18151027fea0a8813fc5054445ffa02a222ff90151117fa80a888bfc4054443ff902a221ff0815100ffe20a8807f71054403fe082a200ffd9521005feca90883fe65484097f32a4200ff59521005faca90883fc65484097e32a421fffd91210fdfec89087ffe64484077f322421fff591210fdfac89087ffc64484077e322421fffd51210fefea89087ffe544843ffeaa2421fdf551
  | 4 => 0x8d12cbbdaa1ee0d5277a6a07242c60198d417207c703635823af58f0d330638f20ac8e2ab96d4000fe3248c94c19e064002a02946e4d08000ee30cba12e4137490980050c0000006fec2c5e000b2bca8d9b600031ecd5541ee800a2189696412857a8a378711a083b2a0b8b1165800000e24028ef45d2ad3604d70c0008517351cbf0edad419c3cc3e81668474471e2a55200000302800da98ec000000000f33a656aeda6010302be44705b57e5e5ba1d3a2a55dbd0fd00eca0410536be654f500062c3c53e06ba880091a1c9476000058005ac19065b376b2610f40001a728c002514063e4002c66ca0005f1e782bd593919b2c064cebb8444609cbe8e5abab34e0af20cc98c254492aa2d16c4000002ba001345b7c280dc7a5da3f0e8d711dc8051c98c0007c02e9675221a4e7832462b5b02b2214cb388e29a33270f7ea213063c9450c02ee8f7043671b2808821233ee0009e0000004888424a1322e75f19108e9dc46f1200050c761e6a60c99a23198285c00196338662c2f1cd1aa20db1126492b663354e538afe58400256b256e4b4d46cd94f178cbc74102230f0a275698006481a2fb00000c0140140200204c0000481500000c018050000080500200401c0000104601400013046024020730060440080009c08c0180200e01c0100a0000000000000001c0480b0000000081001e02c0000800000000007004008020050060380080600a00c0100400002c080080000080100002c0000101300a004050000000000180909408803800002004000340080300000b0000000480700000c028050280040003400800001000008004048250160040300a00c0240100d0380100300000206402001002000048000100040000303a0240080200200c00001002014000020040040000000a0840f8050000140580602609400001010004000000000000580f0000380182200006c018000060280300d0000600900001e008038070040200381a0040080080c00000400001020010000070080040081500800401002002010050040040000303b0000300001d01a0000a00402600401803020010050050280000080000203801802004014030010000100600a0080280180500a07c0503b0020000000000200c0080505e1940001c01a008100000000080000901a0000881601c00003000004014020060000000c80400e0680481801800c0200000006016000002040048010360340f0020020f00000904a0000681700404c0081805a0282a0030cc004018290100080080000c0540b00201a0005600000000c057fb2aa428ffd9152145fec8a90a3fe64548077f322a428ff59152145fac8a90a3fc64548077e322a404ffd5152026fea8a9013fe5454809feaa2a428df55152027f8a8a9003ff63548017fb1aa427ff98d5209dfcc6a9003fd635484ff
  | 5 => 0x4db4b43011ad91274738409b80917ecc144b2754e3b52d9a0a2b2a9838002bc000000003b49700003a000c62a91113009552002d434e1ca00cd58a9fdb88340c48f8499453982befd9291a9bd0d70005a3b213d06d1d443c5c0003e4a88001f35810000019e5b482cf56442a0c8d8a986110186d883c6a00dc0025600005b6bc40220a2c0032e000001a00005badf5888f40a87b0002f52df7f48f1163602f18d77b002000002903e2006d00000f24c8000b883a5a00004b9c88940320e67819f0b4000002cc0000013c7849232500023b08a946d2b41588003db4bc120a75300009d18523404d8795a6400007d0005e25d80f5d4000000000000003aa000003eb000000890317d4fd22e53ab780433f4a6a32870c62f80e09c0001429b5c08a52dc180e59d60006b5794e61bab888190dc1a450001e06060013a80e15e874d596a2901ccfc0ba5a7939060ca46e2cf561f7ab24b13a0e685434123a319887142ba700423f86f10d000098fa5203e8270ef8f860c0019a34803fa09723090000012e9efeec000ef000000000d235342890831c03800c68c04000002d587000000b28e40754c81309fd6d6dc2a119ce83a52c4bc000136000001f6a6ab579e8290008a0003000002c67192a0002a5601ce000200000000008f20037f5beb84290001980de0031c6bc001728004ec0014232f0b4aa85ae779d677470b7c0cb382946c256c076f1b3136cc4c00370030cf8001622ac000d1aea47e9e098800134a94259d96586f8f128d670c738a17f502400420fb5ccc046e09c87ebe95923d0906e1054d194813c82d0cb3a7a77d8e7574570e318a15cd70b587243207086262175000188001572b1269540e00000013b68ebfc68ae95fc068da8df8227f0d7a734d621cc81e61b6b77bc2b5072a49a30004e587050117616ced84300902ae02322037a000af941618d3cf5d6c38ed6d8c99f3d99181608b82406b2d06a46666859098312001438004fc0b9aa9532a2000729420009bd159b7000c5a1f047b58c5cde0001357e42221763d4b5a92ee0d9c140025924abfe000854becb5521025bd729290aac7105c45aa16cc1616382812e12332a8557289d5e000376be0ad8005e199d7814d23b8d4b2ad2baa7005831d3898b16d8001c48ef4791d6945a55997b4f60008598845a9410b0b70000018ac149c38f0001050397ca0aae326c154282cf05e1f83b062c6b7714993d6ba7ce1b7751a6bc6ff8da6d03a30a8f73b053c35844b041ba5bc365680ed6c2832fcb53bb9bf01a3216e0c20004a00041b57a0000018d4d0590481960e87acc3a794485d58d85f0c9001b91ba43e1b6002178f82b5ad0e7a7e8e9ab9465d68c90780000004e0015adc02280022207a74d53c0c29203d558003e37f96ca2fe66d250d8c5000b312589200044d278005008c176
  | 6 => 0x10036b0001590c4ff27c63ef690900008d30845000de44f8000005c80028c1768db689972b005f684951b0db58f26617a8eb5687b0931640031bd862d9030000008a40009b8c60000000000000000302000000d327d620000f4b835aed615bb4e000a641288f4dc001739944b052c308006e61b9586be8c1c1117a12414d0d90a4552ebdc1805100000167c029ea000000000002da0000020c584002543840660031f10c0004a0000003a48c2b00003d90f2f300034a21147000d9000035ade6946384a0cece4608e28d3d81a08004820013480008b348002261ac671741a81d37a20011b3a96a92b93346517e8fb327101b0270222020d47800a54c000bd1b45aa1046f8434c0688dfc00629bd9219f0cf100000000000080003296fc000000004d40014f8000000009c8d71c99300006f008000510002e1921b7912000001c100060300015a71000232002950002b7a28000ca6a5579a70f00011a48c3de6cc488005a44a6f39920008e0b3000388e01
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x670d891000df570d89100a6f760d89100a7f360d8910007f240d8910007f140d8910037e720d8910005f77558910007777558910005777558910045f67558910045f47558910007747558910045747558910005f77458910007b77458910005b7745891003df67458910005f5745891003df47458910007b4745891003db47458910007775458910007755458910005f77358910007d77358910005d77358910155f67358910155f47358910007d47358910155d47358910006f76358910006f56358910035f77258910007e76258910036f66258910036f46258910037e46258910037e64258910007e54258910037e63258910005f77058910007f37058910005f3705891007ef7605891007ff36058910007f24058910007f14058910005f77654910005f67654910005f57654910005f47654910035f7755491018df7745491003df6745491018df5745491003df47454910047775454910187755454910005f77354910155f67354910155f47354910035f77254910047e75254910037765254910037745254910037e45254910005f7705491002df6705491002df47054910136f76054910137f36054910047775054910187f24054910187f14054910037e72054910005f7764c910005f6764c910005f5764c910005f4764c910005f7754c910045f6754c910005f5754c910045f4754c91017df7744c91003df6744c91017df5744c91003df4744c91017777544c91017775544c910035f7724c910037e6624c910007e5624c910037d6324c910037e4324c910037c4324c910005f7704c91002df6704c91002df4704c91011ef7604c91011ff3604c910177f2404c910177f1404c910037e7204c910045f7765411000df67654110045f5765411000df4765411002df7755411000777655411004774655411016df7745411003df6745411016df5745411003df47454110047775454110167755454110005f77254110035f67254110035f4725411004777525411000775525411002df7705411002ef760541100c7f36054110047f3505411002f76505411002f74505411002ff0505411002f70505411002ff24054110167f1405411002ff22054110035f7764811000df67648110035f5764811000df47648110005f77548110045f67548110005f57548110045f4754811015df7744811003df6744811015df5744811003df4744811014f77544811014f755448110005f77348110155f67348110005f57348110155f4734811002df77248110007e76248110037e46248110037e65248110007e55248110037e6424811014fe54248110037e63248110007e5324811002df7704811002ef7604811007ff3604811002ff25048110007f1504811002ff2404811014ff14048110037f3204811002fe6204811002fe4204811002ff02048110
  | 1 => 0x8910036ee4258910006ed4258910036ee325891007cff7158910006f7715891007ef63158910036f7215891007ef421589101b4ff7058910006fb7058910004ff7654910004fe7654910004fd7654910004fc7654910005f7715491000df6715491000df47154910004ff764c910004fe764c910004fd764c910004fc764c910016ee624c910006ed624c910037cc324c910005f7714c91000df6714c91000df4714c910037e7214c91002df47654510026f4765451002cf4765451000df7755451000f777554510007776554510026f66554510026f465545100477465545101adf7745451003df674545101adf5745451003df474545100477754545101a7755454510005f77254510035f67254510035f47254510007f3705451002df6705451002df47054510007f0705451000ef7605451000ff360545101a7f240545101a7f1405451002df47648510016f4764851002cf47648510005f77548510045f67548510005f57548510045f4754851019df7744851003df6744851019df5744851003df47448510197775448510197755448510005f77348510155f67348510005f57348510155f47348510006f76348510006f5634851000df7724851000fe77248510007e76248510016f66248510016f46248510037e46248510037e64248510197e54248510037e63248510007e53248510007f3704851002df6704851002df47048510007f0704851000ef7604851000ff36048510197f24048510197f14048510024ff765411000cfe76541100c4fd765411000cfc76541100067f65541100267c6554110005f7715411000df4715411002f785054110014ff764811000cfe764811007cfd764811000cfc7648110006ef6248110016ec6248110005f7714811000df47148110045f676d9510046f665d95100477665d9510046f465d9510005f774d951003df674d9510005f574d951003df474d95100477754d95100077554d9510035f672d9510005f572d9510035f472d95100077652d95100477452d951002df670d951000df570d95100def760d95100dff360d95100477750d9510007f240d9510007f140d9510045f77559510007776559510046f66559510046f46559510047746559510005f7745951003df67459510005f5745951003df47459510047775459510007755459510005f77259510035f67259510035f47259510005f77059510007f37059510005f370595100c6f760595100c7f36059510007f24059510007f14059510035f676d8910045f675d8910005f575d8910045f475d8910005f774d891003df674d8910005f574d891003df474d89100077754d89100077554d8910155f673d8910005f573d8910155f473d8910006f763d8910036f662d8910037e662d8910036f462d8910007e732d8910037e432d891002df
  | 2 => 0xc67f51596100c67d515961002cff705961002cfe705961002cfd705961002cfc705961002e7e505961002e7c505961002ef7105961002ef51059610004ff7558a10024fe7558a10024fc7558a10004ff7458a1001cfe7458a10004fd7458a1001cfc7458a100067f5458a100067d5458a10004ff7358a1009cfe7358a1009cfc7358a1002eef7258a10056ee5258a10056ee4258a10006ed4258a10056ee3258a1007eef2158a1007eed2158a1002cff7058a1002cfe7058a1002cfd7058a1002cfc7058a1002eee2058a1002eec2058a1002ef71058a1002ef51058a10004ff7654a1002cfe7654a10004fd7654a1002cfc7654a100267e6554a100067d6554a10016ee6254a10006ed6254a10036f56154a10004ff764ca1002cfe764ca10004fd764ca1002cfc764ca10016ee624ca10006ed624ca10057cc324ca10036f5614ca10024fe76d95100467e65d951000df671d951002df571d95100477751d9510004ff74d951001cfe74d9510004fd74d951001cfc74d95100467f54d95100067d54d9510014fe72d9510004fd72d9510014fc72d95100067e52d95100467c52d951002cff71d951000cfe71d951002cfd71d9510046f571d951002cf571d951000cfc71d95100de7f51d9510046f751d95100de7d51d95100def451d951002cfe70d951000cfd70d951002cfc70d95100467f50d95100467c65595101bdfb70595100dcff75595100067f7559510004ff745951001cfe7459510004fd745951001cfc74595100467f54595100067d5459510004ff7259510014fe7259510014fc72595100c4ff7159510006f77159510046f751595100c6f451595101bcff7059510006fb7059510014fe76d8910036ee62d891000df671d891002df571d8910037e721d8910024fe75d8910004fd75d8910024fc75d8910004ff74d891001cfe74d8910004fd74d891001cfc74d89100067f54d89100067d54d891009cfe73d8910004fd73d891009cfc73d8910006ef32d8910036ec32d891002cff71d891000cfe71d891002cfd71d8910036f571d891002cf571d891000cfc71d89100a6f631d89100a6ef21d8910036f721d89100a6ed21d89100a6f421d891002cfe70d891000cfd70d891002cfc70d8910036ef20d89100057f75589100457c7558910005bf745891003dbc7458910005df7358910155dc7358910036ec62589101b5fb7058910004ff75589100067f75589100047f7558910024fe7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe7458910004fd745891001cfc7458910006bc745891001cbc74589100067f54589100067d5458910004ff7358910006df7358910004df735891009cfe735891009cfc7358910006dc735891009cdc73589100a4ff7258910006ef725
  | 3 => 0xe76d852007ef661d8520024fe75d8520004fd75d8520024fc75d8520004ff74d852001cfe74d8520004fd74d852001cfc74d85200067f54d85200067d54d852009cfe73d8520004fd73d852009cfc73d852002cfd72d852000cfc72d8520056ee42d8520006ed42d8520056ee32d8520006ed32d852007ef621d8520056f521d852002cfe70d8520014fd70d852002cfc70d852007ef710d85200057f75585200957c7558520005bf745852008dbc7458520005df7358520085dc735852007ef46158520065fb7058520004ff7654520004fe7654520004fc7654520004ff764c520004fe764c520004fc764c520007cd324c52000ef6614c520024ff7654120014fe76541200ccfd7654120014fc76541200067f65541200267c6554120005ef7254120015ec72541200076d5254120014fe764c120224fd764c120014fc764c120005ef724c120015ec724c120007cd324c120135f77654b1000df67654b10135f57654b1000df47654b1021df77554b10215f77454b1006df67454b10215f57454b1006df47454b10077775454b1020f755454b10005f77354b101cdf67354b101cdf47354b10205f77254b10077e75254b10067765254b10067745254b10067e45254b10005f77054b1002df67054b1002df47054b10077775054b10067e72054b1011df7764cb1000df6764cb1011df5764cb1000df4764cb10005f7754cb10075f6754cb10005f5754cb10075f4754cb101fdf7744cb1006df6744cb101fdf5744cb1006df4744cb101f777544cb101f775544cb101edf7724cb1011fe6624cb1011fe5624cb10067d6324cb10067e4324cb10067c4324cb10005f7704cb1002df6704cb1002df4704cb10067e7204cb100c5f7765431000df6765431000df4765431002df775543100c77665543100c77565543101e5f7745431006df674543101e5f5745431006df474543100777754543101df755454310005f77254310065f67254310065f4725431007777525431000775525431002df7705431002ef56054310077f3505431002f76505431002f74505431002ff0505431007df7764831000df6764831000df47648310005f77548310075f67548310005f57548310075f475483101d5f7744831006df674483101d5f5744831006df474483101c77754483101c7755448310005f773483101cdf67348310005f573483101cdf4734831002df7724831007fe6624831007fe56248310067e65248310007e55248310067e642483101c7e54248310067e63248310007e5324831002df7704831002ef56048310067f3204831002fe6204831002fe4204831002ff0204831002e7f7559610004ff745961001cfe7459610004fd745961001cfc745961005e7f54596100067d5459610004ff7259610014fe7259610014fc725961005e7f5259610
  | 4 => 0x862002ef7205862002ef6205862002ef5205862002ef42058620004ff7654620004fd765462002cfc765462000ef66154620006f56154620004ff764c620004fd764c62002cfc764c620005ef724c620015ec724c62000ef6614c620006f5614c620024fe76d95200967e65d9520004ff74d952001cfe74d9520004fd74d952001cfc74d95200967f54d95200067d54d952009cfe73d9520004fd73d952009cfc73d95200067e53d95200967c53d952002cff72d9520014fe72d952002cfd72d9520014fc72d95200e67f52d95200e67d52d952000cfe71d9520004fd71d952000cfc71d95200067e51d95200967c51d9520014fd70d95200967f50d95200967c6559520005df7359520085dc735952025dfb70595200e4ff75595200067f7559520004ff745952001cfe7459520004fd745952001cfc74595200967f54595200067d5459520004ff7359520006df7359520004df735952009cfe735952009cfc7359520006dc735952009cdc73595200ccff7259520006ef7259520004ff715952000cfe715952000cfc715952025cff7059520006fb705952009cfe76d8d20086de63d8d20024fe75d8d20004fd75d8d20024fc75d8d20004ff74d8d2001cfe74d8d20004fd74d8d2001cfc74d8d200067f54d8d200067d54d8d20006df53d8d20086dc53d8d20086de43d8d20006dd43d8d2002cff72d8d20014fe72d8d2002cfd72d8d20014fc72d8d20256df32d8d20256dd32d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20006de31d8d20086dc31d8d20014fd70d8d20086df30d8d200057f7558d200957c7558d20086dc6358d2024dfb7058d20004ff7558d200067f7558d200047f7558d20024fe7558d20024fc7558d200067c7558d200247c7558d20004ff7458d2001cfe7458d20004fd7458d2001cfc7458d200067f5458d200067d5458d20224ff7258d20006ef7258d20004ff7158d2000cfe7158d2000cfc7158d2024cff7058d20006fb7058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d20015ee7254d2002dec7654920026ec765492002cec7654920015ef75549200176f75549200076f6554920026ee6554920026ec65549200976c6554920245ef7454920245ed74549200976f545492023f6d5454920005ef7354920007eb705492002dee705492002dec7054920007e87054920016ef6054920017eb60549200976f505492002dec764c92009eec764c92002cec764c920005ef754c920005ed754c920235ef744c920235ed744c92022f6f544c92022f6d544c920015ef734c920017cf734c920007cf634c92009eee634c92009eec634c920087cc634c92009ecc634c920087cf314c920007eb704c92002dee704c92002dec704c920007e8704c920016ef604c920017eb604c920087cf304c92000cf
  | 5 => 0x1cfe74d8550004fd74d855001cfc74d855005e7f54d85500067d54d8550014fe72d8550004fd72d8550014fc72d85500c6f651d855005ef551d8550006f741d85500c6f441d8550024fd70d85500c6f710d85500c6f46158550075fb7058550004ff7648550004fe7648550004fc7648550006ef6248550016ec624855002e7f7559620004ff745962001cfe7459620004fd745962001cfc74596200be7f54596200067d5459620004ff735962009cfe735962009cfc73596200be7f53596200ce7f52596200ce7d5259620004ff715962000cfe715962000cfc715962002cfe705962002cfc705962002e7e505962002e7c505962002eef205962002eed205962002ef7105962002ef51059620004ff7558e20024fe7558e20024fc7558e20004ff7458e2001cfe7458e20004fd7458e2001cfc7458e200067f5458e200067d5458e2002edf7358e200aede5358e200aede4358e20006dd4358e20226df3258e20226dd3258e20004ff7158e2000cfe7158e2000cfc7158e2002cfe7058e2002cfc7058e2002ede3058e2002edc3058e2002eef2058e2002eed2058e2002ef71058e2002ef51058e20004ff7654e2002cfe7654e20004fd7654e2002cfc7654e200267e6554e200067d6554e2009ede6354e20006dd6354e20005ef7254e20015ec7254e20266f66154e20004ff7558620024fe7558620024fc7558620004ff745862001cfe7458620004fd745862001cfc74586200067f54586200067d5458620004ff735862009cfe735862009cfc735862002ef77158620006f751586200a6f651586200a6f45158620006f741586200a6f64158620006f541586200a6f44158620006f731586200a6f631586200a6f431586200a6f62158620036f5215862002cff705862002cfe705862002cfd705862002cfc705862002ef6105862002ef41058620006f77558620006f67558620006f57558620006f47558620006f77458620006f67458620006f57458620006f47458620006f75458620006775458620006f65458620006f55458620006755458620006f45458620006f77358620006f67358620006f57358620006f47358620006f75358620006f65358620006f55358620006f45358620006f74358620006f64358620006f54358620006f44358620036f67258620036f572586200a6f47258620036f75258620036f65258620036f55258620036f45258620036f74258620036f64258620036f54258620036f44258620036f73258620036f63258620036f53258620036f4325862002ef7705862002cf7705862002ef6705862002cf5705862002ef4705862002ef7505862002ef6505862002ef5505862002ef4505862002ef7405862002ef6405862002ef5405862002ef4405862002ef7305862002ef6305862002ef5305862002ef4305
  | 6 => 0xa6018121006f96018121004ff7458a5001cfe7458a50004fd7458a5001cfc7458a500967f5458a500067d5458a50004ff7358a5009cfe7358a5009cfc7358a5002eef7258a500e6ee5258a50096ed5258a500e6ee4258a50006ed4258a500e6ee3258a50004ff7158a5000cfe7158a5000cfc7158a5002cfe7058a5002cfc7058a5002e7f5058a5002e7d5058a5002eee2058a5002eec2058a5002ef71058a5002ef51058a50004ff764ca50004fd764ca5002cfc764ca500057f754ca500257c754ca50016ee624ca50006ed624ca500e7cc324ca5011ef6614ca50004ff745865001cfe7458650004fd745865001cfc74586500467f54586500067d5458650004ff7258650014fe7258650014fc725865002ef771586500def65158650046f55158650006f741586500def64158650006f541586500def44158650006f721586500def621586500def4215865002cfe705865002cfc705865002ef6105865002ef41058650046f67558650046f575586500def47558650006f77458650006f67458650006f57458650006f47458650046f75458650046775458650046f65458650046f55458650006755458650046f45458650006f77258650006f67258650006f57258650006f47258650046f75258650046f65258650046f55258650046f45258650006f74258650006f64258650006f54258650006f44258650006f63258650006f53258650006f4325865002ef7705865002ef6705865002ef4705865002ef7505865002ef6505865002ef5505865002ef4505865002ef7405865002ef6405865002ef5405865002ef4405865002ef7205865002ef6205865002ef5205865002ef42058650004ff7648650004fd764865002cfc76486500057f75486500257c754865000ef66148650006f56148650014fe76d89500ceee62d895002cfd75d8950014fc75d8950004ff74d895001cfe74d8950004fd74d895001cfc74d89500be7f54d89500067d54d895009cfe73d8950004fd73d895009cfc73d89500ceee52d89500beed52d8950006ef42d89500ceec42d8950006ef32d89500ceec32d895000cfe71d8950004fd71d895000cfc71d89500ceef21d8950024fd70d89500ceef20d8950005df7358950285dc73589500ceec625895027dfb705895002d7c76549500167c765495002c7c76549502757f74549502757d745495026e7f645495026e7d64549500057f73549500257f72549500276f72549500076f62549500167e62549500167c62549500cf6c62549500077b705495002d7e705495002d7c70549500077870549500267f60549500277b60549500cf6f2054950004ff764c950004fe764c950004fc764c9500257e754c9500057d754c9500cfcc324c95000cfe76d85500c6f661d855002cfd75d855000cfc75d8550004ff74d8550
  | 7 => 0x952101cfe74d9521004fd74d952101cfc74d95211067f54d95210067d54d952109cfe73d9521004fd73d952109cfc73d95211067f53d952100cff72d952100cfd72d95212ce7f52d95212ce7d52d9521014ff71d9521014fd71d952121e7f51d952121e7d51d952102cfe70d9521004fd70d95211067c50d952121ef710d9521024ff76595211067c6559521205ef72595212c5f7715952121cff75595210067f7559521004ff745952101cfe7459521004fd745952101cfc74595211067f54595210067d5459521004ff735952109cfe735952109cfc7359521204ff7259521006ef7259521134ff7159521006f77159521004ff705952102cfc7059521136f7105952109cfe76d8d210f6de63d8d21024fe75d8d21004fd75d8d21024fc75d8d21004ff74d8d2101cfe74d8d21004fd74d8d2101cfc74d8d210067f54d8d210067d54d8d2111cfd73d8d210f6de53d8d210f6de43d8d21006dd43d8d2100cff72d8d2100cfd72d8d212bedf32d8d212bedd32d8d21014fd71d8d212b6df31d8d2102cfe70d8d21004fd70d8d210f6dc30d8d212b6f710d8d2109cff7658d210f6dc6358d211edef7258d212adf77158d21004ff7558d21024fe7558d21024fc7558d21004ff7458d2101cfe7458d21004fd7458d2101cfc7458d210067f5458d210067d5458d211ecff7258d21006ef7258d2111cff7158d21006f77158d21004ff7058d2102cfc7058d2111ef71058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d210267c6554d21006df6354d2109edc6354d2100dec764c92109eec764c92100cec764c9212a5ef744c9212a5ed744c92129f6f544c92129f6d544c921015ef734c921017cf734c921007cf634c92109eee634c92109eec634c9210f7cc634c92109ecc634c921007e7714c92100dee714c92100dec714c92111fe4714c921016ef614c921017e7614c92111fcf314c92111fe6314c92111fcd314c9210f7cf304c92111fe7104c92109ef4764c521014f4764c52129777544c52129775544c521007e7724c521015f6724c521015f4724c52128fe4724c52100ef7624c52100fe7624c52128fe6424c521297e5424c52128fe6324c5210f7e5324c521007c5324c52102cfe76d8121024fe75d8121004fd75d8121024fc75d8121004ff74d812101cfe74d8121004fd74d812101cfc74d81210067f54d81210067d54d812109cfe73d8121004fd73d812109cfc73d812100cfd72d8121066ee42d8121006ed42d8121066ee32d8121006ed32d8121066f771d8121014fd71d81211b6f631d8121006f531d8121066f721d81211b6f421d8121066fa20d81211b6f710d81211b6fa10d8121006fb60981210057f75581211057c7558121005bf74581210fdbc7458121005df73581210f5dc735812102ef
  | 8 => 0x4fd74d815201cfc74d815227e7f54d81520067d54d815209cfe73d8152004fd73d815209cfc73d8152024fd72d815200cfe71d8152004fd71d815200cfc71d815227efa50d815225efa20d8152135f67198152005f57198152006fb6098152005df735815213ddc7358152145be7418152005bd741815213dde7318152005dd7318152135f67118152005f5711815202efa6018152006f96018152024fe76d953212e7e65d95322f7cc32d95322ecfd75d9532004ff74d953201cfe74d9532004fd74d953201cfc74d953212e7f54d95320067d54d953209cff72d953209cfd72d95322f67f52d95322f67d52d953200cfe71d9532004fd71d953200cfc71d953202cfe70d9532004fd70d953212e7c50d95322f6ef20d9532024ff765953212e7c65595322fdef72595322efcc32595322f4ff75595320067f7559532004ff745953201cfe7459532004fd745953201cfc745953212e7f54595320067d54595322ecff7259532006ef7259532004ff715953200cfe715953200cfc7159532004ff705953202cfc705953212e7f50595322eeef205953200cfe76d85322afcc32d853211ef661d8532024fe75d8532004fd75d8532024fc75d8532004ff74d853201cfe74d8532004fd74d853201cfc74d85320067f54d85320067d54d853209cfd72d8532006f741d853211ef441d853211ef621d853202cfe70d8532004fd70d853211ef710d853228fcc325853211ef4615853202cfe76d813224fcc32d8132024fe75d8132004fd75d8132024fc75d8132004ff74d813201cfe74d8132004fd74d813201cfc74d81320067f54d81320067d54d813209cfd72d813200cfe71d8132004fd71d813200cfc71d813224efa20d8132257cc329813211df67198132005f57198132006fb60981320057f755813212d7c7558132227cc325813212d7e75181320057d7518132125be7418132005bd74181322e7cc321813211df67118132005f5711813202efa6018132006f96018132014fe76d895110eee62d895100cfd75d8951004ff74d895101cfe74d8951004fd74d895101cfc74d89512de7f54d89510067d54d895109cfe73d8951004fd73d895109cfc73d895110eee52d89512deed52d8951024fd71d8951206ef21d895102cfe70d8951004fd70d8951206f710d895110eec62589512d5f77158951004ff764c951004fe764c951004fc764c95110fcc324c95102cfe76d815100cfd75d8151004ff74d815101cfe74d8151004fd74d815101cfc74d81510767f54d81510067d54d8151014fe72d8151004fd72d8151014fc72d8151076f771d8151024fd71d8151076f751d81511bef451d8151076fa50d81511bef710d81511befa10d8151006fb609815102efa6018151006f96018151024fe76d95211067e65d9521134fd75d9521004ff74d
  | 9 => 0x1101100900000e00b01000000600b00a00000900901900000400202000000600400100900c01001d00300000c00000700300000700700700500600400000e01d00a00802d00200000501000c01a00002b00100002d00700500900600100200300c00000000100400000000100b03000200500000000101f00100000401700000100d00f00700b00400300700900100101605400800201100400b01001100c00a00100200300001100401202900200d00a00700b00400800400e00000a03000000000000501600000000b01600100d00001b00000c00100600500900800000300001a00000403b00300000401a00001500100b00301c00300000000400000100000200e00900600300000101900800000300a00301701a00000d00300d00401000000200000000400700800000c01b00001000400600200000100100000600100300800000300400600d00001500100202a00a00400000500000400200500200101400000501200600400500000000000700e00100000000000000200600001500300a00c00500300100100300400100300000105f00400800001000100200001100300100000500000f01602e00000c00000700100200000001f00600800702101c00002701300401700502d01700b00201000100100000b00300801000900400300100001801401a00401e00f01200001000101500100501701800500001301900501400300000300000102000300300001b00000405103600200500200002700a00b01d00001000800900000200001200000000f00200600800000800100a00001301100301600100000b00f00100000300800002400003600601400000702f00800500602a00200000200200300000000000c00200100700900e01d00000000400801100302900000100001204f01100700000500600d00a00400001900800000000000300000000901800400400900100c00201c00100100700b02602602e00200200800b00200800100001100000500601700000001300009cfe76d8d5213ede63d8d52014fd75d8d52004ff74d8d5201cfe74d8d52004fd74d8d5201cfc74d8d523167f54d8d520067d54d8d5213ede53d8d5213ede43d8d52006dd43d8d52024fd72d8d5230edf32d8d5200cfe71d8d52004fd71d8d5200cfc71d8d5202cfe70d8d52004fd70d8d523167f50d8d5213edc30d8d5230eef20d8d5213edc6358d52305ef7258d5200cfe76d8552136f661d8552014fd75d8552004ff74d855201cfe74d8552004fd74d855201cfc74d85522d67f54d85520067d54d855209cfe73d8552004fd73d855209cfc73d8552024fd72d8552136f651d8552006f741d8552136f441d8552136f621d855202cfe70d8552004fd70d8552136f710d8552136f4615855202cfe76d8152014fd75d8152004ff74d815201cfe74d8152
  | 10 => 0x8488eec0495e0001b7ad46e80000006a49041ae1180669d87900000d2aa263a72000075c98888b864c2a5a630a6b46c2886a9c42eb409d56e628278c5ae85c9ba7b201e4d25847f107e2c66e4b9d6323e03106687d2a422b200499c214aca7464065c2a5e1d09523d0824c403d27e0a9052c6be1bc50c6c431261401c7de95879233e288b2a6dc0007ce22237eba3000000000a88a440000005feb966ae0bcbcec1c1e0208780bde91a1084aeaf04a67309fc8beac45922bebdc5d699d7da00019832064a6580d0bca0e68eab244e9088700a1bc16796000a1000031a2f588a67c00046e1ee72c0002fa21eba63568e0000873b4835e89224812a33a000becc0a0000000002062380003d6ac9aa66d6a046a2b8a0eeb2873a0000008e60004525280de044b8787c2f68d44621a64e8a3027a4de6647dc49653849892a37a9281903ec48e83a0009e08b49220a400089c00023c7023778780004da53a99a2ae09d0c491397c6460000008e90006709360007b4778a74a642e2c200ca88d4ea48fb46309000ab88fbb506da204000134bbe09f5ce6d00ac2fe0001ec4e40006b02460007080f37b043e37c3289348f23921c02748e858896c7aa0b4024b1c90a1ceabcb561e62a8870c301c2196888c46278a8a54a9ae6c0086724a074a400049c64200056a45ca1d1101cc20e3f028698c000a78a244010586cebd20cc8ae9327f596aace00000076461a71a62a0540005f041600018291025077069eaee99fb0616eaf848ca3cab407603f85007234c2e6ac0970adabe0b344a02663d88c4686b4e5821b52c094aa00c560524929da3e869caae3d4bc6b1ea6c2738b229c8aa00082828eba4bb3000000b743b884e0b25cc00000013c1da404000b890000000000000000008466004663448ca4e268e4c0c3800021a00089e42ab1ab3e626804a217f0b6622e29a81a61641aae6bcc83820c94e88f5f484480027f8a027d1748a83de7fc9cc40e2104b2c063da1d253226a0949c65e65d04fa0002ca2308a21f66c89bc1f8b140000d8a0e26c0002e8a661220005666c6428b446181c8b763806d4034028270a226fa1d8c44ae42fc4f429eb9829334a38296255284c03ca5833cbacbe44bea024f8bd87fab2609217c8bf61e5eaafa73c5f93905962aa36c82c55a0ce5304d47f349366e36400000000054479e000152000000a05ad63b00006825f89fa39ea8e38a0fea3e00700103300200800100100601d00100100200000400d00100600400400c00c00001600001a00100404d00700000500000102a00a00301700201100e00300000000700d00400000000500002101700201c00000900200200200000600200000d00100800400000a00200601000200301e00200800200300001700d00000f00100300600500f00f00002a00300003001e00100e0
  | 11 => 0x55b0360c0000a7696091483639600065421600078a45808cbe83fe00008a8b9b7a8f68c251699412e00000000050a09b0008ba9c2c188af0007841548940001b600060623e4ac4940002b0bfaa1e00090e6388a40000000000000008840001500004b00000002d4b80a6846a0008300000000009481a80005362d04541361ac72a7be6ea3c03166300e20000004ce000000000090b0cbb42ea3e2b36188c24b929f80007220003be0004105de81e6045241dcbf430c0680a199835a308138968030b0ab323c890069385405e5a42563401a234190851064c8b32640649ea77a9d09be8660006a809e9a94f2b1066c42c9663997c270c1172f10002b670a06049020a51a12602c000000ad86740002e40009f07320003a0000000808712000a80000b790000002c200d7160000003010000000be79c000000a7cb12394b16b595a06128202056a63008f86de8c006787a7486408ad48560e3365b41ca00081c24c9fe0000e800018f972b587a2000a2fbfc00086c2c49246a014a5ac56d7cc0f42f40000000003761946f293a6d80006984d8986000000b5cade6b81a451c7ea50251459a548aa0714ad200001280eab222a568000000ab60000000003ba88e91177400c8ceac6938c3e4690002cc8cc8eb46b0003a28e20fc0003cc0e4000b4c463944000b185fc04e3343f296f0005427f20000009f641c000000a3216a7a45945b644e6844fe5e449e5052ce8b6576786b7e7ca58647c3508bc68c2767894c473488cbb700000000082e8c30002120000000b000027e0000003fa1b90000009162bc10058e8b03cabae69157fb825ca7944ef8f43c58b574c7bc04d57a0f1afe70e38e0008960f24f646c06ead017e114930000a7aa8c17a00058abf0176180000000b9467aa9255d28c442000144000aea57e0000009cdb9e000950148628099398000000882c2c25a0008e425e0a034374006292604811c09876c2513044917ac294000000940590008b9a3485da55c762a6a56e8853a8aba0a260824f200b682335e8761acb3529f48ecc540b86609b675800058c0f6000000b0e1304d05c47dd162a9e0ec7106b225c852c58486000ba8c3a00000000000e76e402af28226bc5f60000321645838686760005644684973185345c5902a3416c1be2f847e73665c4640000009a4bd400018ab724079e843c6720000009a7bbca120a604a19e8dc7fe9a5acc00087e6667440007260ae5ec1726ac4609a843851212800005a000bc40000000007d847a0009a0000a6e54c19c0000009aa0804e77d078e2961b2964000379a2e4b4000000000520370a5c29200008e00094c2910003300aa4e04ee2a0000a283240005a289046775e00062c0960002da000000a061ba000000000000000c320002ee00050b0004d69b43b699e7608d200089a1dea7298256
  | 12 => 0xf08abb04000c3359e9ad1067e445a44b6aa620688484b2218622c0140006f8a566024ba9dc478000776b606ba644a46694b648d01b847262487685a8b850601838661c9901603669ac5f247678223a0dc456bd019a08471e6229d2b9c33f75a86a3a4bb8ae0b542f29ab81610476a2de56301795666a7f6578b2e2b40264052dca382d80009e60b6980c2eb5f4a8b3c2625be0825fa1d400000000000000097ab6abb5400346000272a0c2ec4e687b03a00069015ec340167a60002600741bd0da5623b114c86e14e000bc888932a00021b818000ae23021ea72e48a1b42a69f98da158898495a3a80c9eebe61787ba09c338184000a1aa36bfe2525808bb3dc02a3724c6403511000a162d65ba000508aa8978000b864402201bb290000bc0c1e6782585aac4c2244bc8de77c4484fc050bb205c3c64345c78fc7aeb20aaa97483cc26656000adcb7ca8415c4883b210c1327e65c60007187d65987c09ce040b383b437855e3328bd5373c48261f2c0864875200075623295ac4a3aea184703e621c4c2c4e7b692060a5b8572a4c9a3c5a5b0a40aec97679a7c6af40568e7842228636000000a9496e065bb6912000ac70000000002a45b236a34eb6c8d66cc3ac2f0000bf8996000c288fa8587c40000008ff00050438c18e9920001f02808061129840000002a2bc2874a0a06a5b95509a1a9a0006f4022414a4a1c466d3a61163bc0e0738010c1095c37db429c4b027ec00a000946c60000000000af6ac84181fa75427cbf23ce10a1aac525ee3eaa2030e10e0f84303741b082a354c14326b840faa604ec856444000219000bf607845e40c30642625437b55800023440a98a000000abe44a00086043a000810000000000bda00048209a00090c0008400ba00070639b8a602028aaa42c8704788bd685e7e84209de7b80002361662025e31249b217000057db5aa2a3aa000000000c36500424000000218000102aaca6293ebea7e24ca8b7bbaa4e60ca5265ab8869274e53c0008f09e232e00063e000087000c026eec0c8144230c800000077e432b629a63fc7f8b5e5d257cbee0007a080a11a9c875052204cbb04804c842283e5c000036e41e73e0ea268000766c48b3080213e2ac7a84461d634226e8c8244a989f262e47413a5e2c0e1f49e4000526b00812a8224ebe263c384b90baa0000460696f606b6341fc9181566e26caba23e43606ec7688c698e4f0540c5e32c772063ae80002e02530068326b68c118d3581fe8344365d87f416800035ca501e818cc1a04253e0006fc0003f69067c80d69c066207c64e7d40001200005d40a83c200057467e5a8a7e39cb8e2268b184a284000c5c862000942a860001e444c00050e92cb2fb3a000a9656c3f400071c3143c1a5412c4dcb379a2afc6800002ba52a31e46506cb7074a5c82980006f0
  | 13 => 0x1c66520d4070a14570b4aa70a2c6d2c429b791e11e00018b39a31c00000014600037549ac12000b8c142362ba000092e65e8804ccc3c51e97e6500000c20000c69c519291c1e2742b089ca1a069a0003ab6fe8fda5a000c220000003f852e3ee0002d20006e0000000000000b2c242b6ea080004b607a0009548ac000c004b89ec24000054e0000000006108d89d600269666993c9af9b879824aa4876b5563884a27ee5e0000518554140000ac2ab05bcc505dc32200036803815a01a0000008fe872000000408bb168aa1c2b8a2603eb780000004aa59c00000000002e5464129d49b0000000728450b520
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x9f184dc165440d7ae6a9b82ca880035c5537059510004f943c80b2a20009f287501654400f3e10ea02ca880036cdd1405951003ed83a280b2a2000f31545016544001a6ee8aa6c48801f4d1d154d89100347ac3ec7b122000ec432d8f6244001b66e8a06c48801f6c1d140d891000798aa281b12200897687dd562440012eb09baac4880031dd837558910006b9b06eab1220059f080dd1624400f36d0fba2c4880034ddd774589100069a3aee8b122000d3785dd16244001a690bba2c4880036ce0374589100065bb06e8b122000db360dd162440012ef0aba2c4880225d2157458910004ebc1ae8b12202a9d4835d162440013e700ba2c4880026da1c74589100069bba8e8b122000d34751d162440012ed0faa2c4880225d21f54589100069bba6a8b122007d3474d5162440d5aa8e7aa2c4880025da1d5458910004ba43aa8b122000d3774551624400fa68e8aa2c4881a7551cd5458910154eb43ee6b122000d5775dcd6244001aa8ebb9ac48800365dd37358910006ca3a6e6b122000d5754dcd6244001aaaa9b9ac48800335d837358910006e9b06e6b122000d57751cd6244001aa8ea39ac48800365dd07358910006ca3a0e6b12202acd473d8d6244001d8c65b1ac48801a3d21d6358910006e239ec4b1220079e48750962440015c90ca12c48801f691d1425891000792aa284b122068dc473509624400b1e90db82c4880035cdd77058910006b83aee0b122000db374dc16244001b60e9b82c48800374dcf7058910006e839ee0b1220059f086dc162440013e309b82c4880035cd537058910006b8aa6e0b122000de362dc162440cfbc0c5b82c48819f7890b7058910006f0a16e0b122067de232dc162440013e50f202c4880035cdd64058910336b83ac80b122000db374901624400fb60e9202c48800374dce405891032ee839c80b1220009f287501624400f3e10ea02c4880035cdd54058910326b83aa80b122000db374501624400fb60e8a02c488003cc5514058910006e9b9a80b122063dd0735016244001f4284a02c4880027c6037654910004bbc2aeca9220009b7845d9524400f36908bb2a48800275e0d7654910154ea41aeca9220009f3805d952440013e301bb26488003710ca764c910004bbc2aec9922008974855d9324400136f08bb2648801e6d211764c910004f3c12ec99220009f3805d93244001b88643b264880027ce01754c91002cf8402ea992202a9e487589324405578906b126488003b158d624c910005f1c02c49922005b7280d95504400b2e90ea92a088016dc2015254110004ebc1aea902202a9d4835d520440012ef0ab9a40880225d215734811002cf343ec490220059e487549204400b3c90e99240880ab711cd324811002df04026490220069f0875412044011ae0eaa824088003d85495048110
  | 1 => 0xce8aa2c6900030f5d15458d20006363aee4b1a400087f855d953480011df04bb2a6900163b219754c92009d67436c69924003c3e74553614800187ae8aa6c2900038b55142d852009e6639a65b0a4000ccc764c9314800b2d90ea92a0900169b219525412002db4402a4a824005acc864c93048005998ec9926090016f2201324c12002cba43aa4a8620009d7835d520c40733a906baa41880025de157348310074ba42ae690620059e48754920c400b3c90e99241880e7711cd324831002c3e43aa8b2c2000c3f74551658400787ce8aa2c5080030f5d15458a1002c7643a84b142000e2d54509628400b0f90eb2aa5080163b21d6254a1002c7643ac49942013acc8358932840031ed03ba6ca880163d60774d951001c3fc3aa9b2a2000c3d7455365440e18eae2aa6ca8800e1f217745951000477c12e8b2a20028ec825d165440011ef02ba2ca8800e1f21d54595100061fba2a8b2a2003c3c74551654400b1eb03ba6c4881b31d5c754d89100061fba2a9b122003c3c7455362440e18eae2aa6c4880121fa1f75589100043ec26eab1220038be87dd1624400187eebba2c4880030f1d774589100061fc2ee8b122000c3c85dd162440010ff0aba2c4880121f21574589100046fc1ae8b1220138dc835d1624400117d0e3a2c4880030fdd474589100061e3a8e8b12200087e87d5162440090f90faa2c4880030fdd3545891001e1e3a6a8b12206fc5c73d5162440010fd0eaa2c4880021f21d54589100061fba2a8b122003c3c7455162440dd8b8e6aa2c48804e37a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062faa6e6b122000c5d54dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001998e7b92c48800e3b21d425891001e563a284b122000e2d5450962440db998e6a12c4880021fe1576549100045fc22eca9220038bc845d952440011bf06bb2a48804e3720d765491002c7b436e2a922000ccc329d932440010ff0abb264880121f215764c9100045fc22ec99220038bc845d932440011df04bb26488003330c8764c91009c7643ac49922013acc83589324400b1ed0db8a64880de7ca1c705451002c7a432ea90a20058f4865cd21440559a8e7b1a4288003b18cb63485100147a43ac690a20019e4874c92144055b88e69924288003b158d32485101b4f9438e090a20189f180dc5504400b1ed0db8a408803e7c60371481100047b436e9b2a2007977875536544001a6ae8aa6ca880036cdd140d951003ed83a281b2a2000f315450365440d92e90bba2ca880023de197459510004f3c12e8b2a20069e4825d165440013e700ba2ca8801e5d21d54595100053a432a8b2a2000d3774551654400fa68e8aa2ca880035cd97705951035eb832ee0b2a2000
  | 2 => 0x1764865001c5e422ec90ca0008df835d921940271b906bb243280163d21d61486500463a3aac290ca000c3f7455362540014db0ba16c4a80038b55342d89500056741e85b12a000a6d85ccb6254001998653b264a800e2fa10764c9500045ec20ec992a000ccc321d9325400b0f90cbaa64a800f0f9d154d85500061eba2a9b0aa073e344155361540014eb0ba0ec2a80063ba1f62485500046fc1ae8b2c40138dc835d165880011ef02ba2cb100063d205745962002c3e43aa8b2c4000c3f74551658800787ce8aa2c7100030f5d15458e2002c6e43a86b1c4000e1d5450d638800b0f90eb2aa7100163721d6354e200061fba2a8b0c4003c3c7455161880e5c6c82aa2c3101cb8d10554586200055b426a2b0c4000ab584d4561880014ed0ba0ac3100029d617415862002c7a43a82b0c4000ab6849d5618800156b093aac3100029da1674586200053ac2ce8b0c4000a76851d161880014eb0a3a2c310002b5a0c74586200056ac18e8b0c4014ae6821d161880015cb043a2c310016bca0074586200a578c00e8b0c406cc7770d516188001c6ea92a2c3100023de1d54586200047a43aa8b0c4000c778755161880018e90eaa2c3100038de1154586200071bba2a8b0c4000e347455161880e3c6e84aa2c3101c78d50954586203863bb82a8b0c4070c757055161880e1c6e80aa2c3101c38d50154586200053bc2ae6b0c4000a74855cd618800156f08b9ac310002ad211735862000573c12e6b0c4014ae6821cd61880015cb0439ac31000395d4e53586200055b420a6b0c4000ab58414d618800b5e50029ac310002bc60053586200053b42e86b0c4000a7585d0d6188001c6aa9a1ac31001ab9a0b435862000572c1686b0c4000e355450d61880014ed0a21ac3100029d614435862002d7940086b0c4000af18010d618800b1e90eb0aa3100163d207764c6200043fc2aec98c400487c855d9318800117f08bb2631000e2f211764c62002c7a43ac298c4006ce47258531880031ed03ba6ca900023d60774d952001c3fc3aa9b2a4003c3e74553654800187ae8aa6ca900029d20554d95200062eb9ca7b2a4000a6d8294f654800117f08b8eca9000e2f21171d95200046fc1ae8b2a40138dc835d165480011df04ba2ca900023de05745952000c7a40ae8b2a400387c87551654800187ee8aa2ca901bb171cd545952009c6f43ee6b2a4000c5f54dcd65480018baa9b9aca9000317dd473595200066639ee4b2a4003c3e74553634800187ae8aa6c690003175d753d8d2000566c16a7b1a40038df8750f6348001c3aa8a1ec6900121fa1f7558d200043ec26eab1a4000a3d841d563480010ff0aba2c6900121f2157458d200047bc0ae8b1a40018f4815d163480010fd0faa2c6900121f21f5458d200043f43aa8b1a400087c87551634800787
  | 3 => 0x680204804000000001600814000000000001002058060000000800000080000202806020040180000800020030fdd154d8d5201c6fc3a87b1aa400e1d5450f635480787ce8aa6c2a90030f5d154d85523e71a20aa9b0aa400a7585d0761548011ef02ba6c0a90063d20574d81520061fba2a9b02a4008fb8758060548271db05ba6ca990063da0774d95320047ac0ee9b2a640387f87553654c80787ce8aa6ca990030f5d154d95320052fc1aa9b2a647bc5f73dd5654c8011ef02ba2ca990063d20574595320047dc02e8b2a64058f8805d1654c8070f90eaa2ca990030fdd1545953201e1f3a2a9b0a6400c3d74553614c8f5c6882aa6c2990023de0574d813200c7a40ae9b026403c3e74553604c80187ae8aa6c099003710c97198132006a6196eab026400d4c325d4604c801b1864ba0c099003710c971181320047dc3ac03026400c3f745536254407878e8aa6c4a89e63de0574d81510061fba2a9b02a203c3c7455360544d79e2e3b04c0a88023ee1d60181510147ac0ee9b2a420387f87553654840187ae8aa6ca908023de05745952101c3e43aa8b2a4200c3f745516548407878e8aa2ca908030fdd154d8d2101e1e3a2a9b1a42038df8750f6348401c3aa8a1ec6908023de057458d210061fba2a8b1a4203c3c74551634840717d09bb2a6908022f6137654d2109c3f43ecaa9a42048de87d8d534842759d0db1a6490806f1a19324c52100de24326498a4213ec4864c93148405b8cec992629084fb11d9324c521016623b26498a4278bc7844c931484f178b0899262909dfd1d51324c5213bfa2aa26498a42058f4815d3604840187ee8aa6c09080f0f1d154d812101e563a285b024200e2d5450b6048427998e6996c0908323d21d31d81210076299263b024267cf171d8260484011f70eb00c09080f0f9d15458a500061eba2a8b14a0058ec875096294001c5aa8a12c5280031758f754ca5002c7643ac4994a013acc83589329400187ee8aa2c32800f0f1d154586503b71b20aa8b0ca076e344155161940014eb0ba0ac3280163d21d41586500453b42ce8b0ca000a75859d161940374ed0a3a2c3280029d614745865000573410e8b0ca000ae5821d1619400b5e5003a2c32806ebc60074586503ae3bc3aa8b0ca074c748755161940d94ef08aa2c3280238de1154586500071bba2a8b0ca000e347455161940e1c6e80aa2c3281c38d50154586500053bc2ae4b0ca000ab7845c9619400156908b92c328002b5e0d72586500056a41ae4b0ca000ad6831c961940015ab06392c3280229da1742586500053ac2e84b0ca000e3554d0961940015ad07a12c328002b560f42586500071aaa284b0ca008a768510961940014eb0a212c3280023da1c32586500047ac3864b0ca000ec5320c9619400b1e903bb243280022fe1
  | 4 => 0x7dc000000000005580006e0000000000004cdf8004160f400017a200291180039a618060570a23cc5b214448000460ff000000df52c3a600055c000000000000000085c97839000308000001474a007106944068138002da1589f17c3f68809d0003e6218c50f734c4600f8003d845c009a72b8438000e100000049028000208000000007fd0c9680d8000000000000000016118a000ee8bc4142e43aa0900e0002f9e90003f00021e000000000000004dc001a0000168fb16719400058819000060001a80000a4790c62228841a80f0c425446800000000000f808063800108000000f1c00000394c2000000000030000000000019c0960b4ca8002270c8000140a81c4808d5000000b600000000000072378580100000000008d8000dc3aa509da00005800000110844338230660009e9750000000017a000340000d31c0000000000007000000013e000208ac30478800012000000000ebab4136160003d600055000296000c4000000000000000000000010900064c109710000f0229ac3e821c094e731881800000004000001810aa210a24dd3b02904c12732c508a896300062c000002b6000b51e100a714b590c20c000000000000000000037428000000000000e1000336000000003982f90a8fe1a480c931ca05e54c640440b0530000460001ec000a4afe128a19c321a60ccd166396000f78eb22676506800000174af1240004590e81b28a1e0000ce05c6dd0d8000001640000000000000000000000890e91d0000000000000004f000000000d81650000000f0002388409b0000007783f978242134000971f40e0dc0683c83b86c8003a23e40021832e000dfc00000000001220000400004918232c980002ac524f18e329c564fc892bb84940002a0005e4318660fa1e87e800000000ff00000024400199232270000001270006b80002a3bc0000000042c0014f022294c483b2232e8a202b1be5048f9f20000006b1920006341280037a5880000011c000fa9cf000614000000004a800074114000000002be6b4000d12c8000e49ae1b80005d8e2240282002000845f866907000000000000000000007c0000000000027e678d100000016c1215740a0005b8651e8000a904f136000000430de3c400000376001020000006aa5316f1ec324008020180801008010000080201802000080080a0101a0180e0380e01000020000081200804010340080200802030040000601000010000280600000028020100000006010000480400000008040000e0380c000000001404002018200000e00806008040080a0000a0000802804008000100c0100603800000100000a0000a0000207000010000100400800020100002a00002010080080000004000000080600002018020180e018060200a0000000002018080080c000020480202010068
  | 5 => 0x1691260000016e00000000000000000000000004280002600021400061276000001a78000005680021e000000093be240e800023c7040019015200000000000000ea9c70004685fa080002c80000037268d111b601a1a4001981320010cda40006d4998002b05d8369db352000ca00003a1486200040e178df00043e000000000e02044580028c000180c02560005394d15b4c8d78000000007a83f3ae000f8000000000000000a679835940000268d98360000005800030e000d59b129402c238c33e22d0971fc0f284c1d1d38d4000478000005f4d09ed39c4a48e9fd3003a800000000000f7080388000f0e0f1c8360b92160c8138189232ba1cc3b0de2905ec0409d000804bb8cc0907508006027879c000002e0001060c72687e8fc03e2e8000579e095c13081822000000000ec19e000001e0390398000000004b50d0000008080000000020c00000000000000000000002e0942e61f8a810517a000e9000270450f14da22a28c780001662a0e30172aa36c0000400067c5a99d3ca6d0820d4364838019393d00d0768b826a644000fb03800000147204000c7850424870988893ac7a8aa00034a6a84b07700
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1e0001822bd404000061b0084a802841d803a20c9c48e002d24dc0002cd18801a000263e5ce6c00958000ee47000068f0014019ae65a51002dadd2a00040366ac93a30c24000040100347000001600985000404081060079520001800200100041828b40d0d24574553604c8011c5980c971981320055164432dd5604c801545910c9751813200552640325d4604c801585910c9741813200562640325d0604c8011c5980c971181320663121d324c76048401625921d154586503b58c640745516194001a155460f42586500063161d320c961940014c5910ca764c95000623610321d932540014c5910c8764c95000532640321d93254001615931d15458620005896487455161880e5631901d154586200068955182d0d618800781f8755143d8d200240f261745516348103434915d15458d200050b65075dc9634800142c97551425891001e0b21d545096244101c0c73551425891000531644329d932440010cd980c8764c91000531644321d932440054c49758d324851003d4c25d54501654400193287551405951003e4c21d5450165440016309655140595100064ce1780dd162440014c6978cb6358910004b164c8650962440018c47321942589100054925d54509624400f924875514258910006892195450962440ffd047355142589100074855142dc162440015329755140589100054c25d54501624400193287551405891003e4c21d5450162440fdd107355140589100074455373501624400f5a097509405891003e6821d4250162440016a09650940589103ef601cd4250162440014c5960ca764c91000471660321d932440014c5960c8764c910034b126163589324400b560975495048110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x406050200300100000308584644321d93254001844c2320190ec992a0008316a47321942589100060492e432a8a12c488002a05a3219545096244001c023990caa284b1220009a068c965094058910
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x80060049768c865514258910004805ba1cc865514258910
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x94b
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x124d
  | 10 => 0x124b
  | 11 => 0x124e
  | 12 => 0x138b
  | 13 => 0x138d
  | 14 => 0x138e
  | 15 => 0x98a
  | 16 => 0x98c
  | 17 => 0x98d
  | 18 => 0x98e
  | 19 => 0x4
  | 20 => 0x128a
  | 21 => 0x128c
  | 22 => 0x128d
  | 23 => 0x128e
  | 24 => 0xa4a
  | 25 => 0xa4b
  | 26 => 0xa4d
  | 27 => 0x134a
  | 28 => 0x134b
  | 29 => 0x134d
  | 30 => 0xb0c
  | 31 => 0xb0d
  | 32 => 0xb0e
  | 33 => 0xbcb
  | 34 => 0xbcd
  | 35 => 0xcca
  | 36 => 0xccd
  | 37 => 0xcce
  | 38 => 0xd4a
  | 39 => 0xd4c
  | 40 => 0xd4d
  | 41 => 0x98955
  | 42 => 0x94c
  | 43 => 0x94995
  | 44 => 0xa4955
  | 45 => 0x94a55
  | 46 => 0xcc955
  | 47 => 0x94cd5
  | 48 => 0xd4955
  | 49 => 0x94d55
  | 50 => 0xb0955
  | 51 => 0x94b15
  | 52 => 0xbc955
  | 53 => 0x94bd5
  | 54 => 0x150a
  | 55 => 0x198a
  | 56 => 0x99395
  | 57 => 0x138c
  | 58 => 0x138995
  | 59 => 0xa5395
  | 60 => 0x138a55
  | 61 => 0x170a
  | 62 => 0xcd395
  | 63 => 0x138cd5
  | 64 => 0x1a0a
  | 65 => 0xd5395
  | 66 => 0x138d55
  | 67 => 0x164a
  | 68 => 0x9cb
  | 69 => 0xcc995
  | 70 => 0x98cd5
  | 71 => 0xd4995
  | 72 => 0x98d55
  | 73 => 0x168b
  | 74 => 0x12cb
  | 75 => 0x198b
  | 76 => 0xeca
  | 77 => 0xd4a55
  | 78 => 0xa4d55
  | 79 => 0x150e
  | 80 => 0xa4c
  | 81 => 0xb4b
  | 82 => 0xb4b15
  | 83 => 0xccb15
  | 84 => 0xb0cd5
  | 85 => 0x16cb
  | 86 => 0x15ca
  | 87 => 0x144b
  | 88 => 0x19cb
  | 89 => 0x14cb
  | 90 => 0x154e
  | 91 => 0x140e
  | 92 => 0xcb
  | 93 => 0xecb
  | 94 => 0x17cb
  | 95 => 0x1a0c
  | 96 => 0x170e
  | 97 => 0x1a4b
  | 98 => 0x15ce
  | 99 => 0xa0954
  | 100 => 0xa0956
  | 101 => 0x130954
  | 102 => 0x130956
  | 103 => 0x138953
  | 104 => 0xd0954
  | 105 => 0x104954
  | 106 => 0x1a8954
  | 107 => 0x138956
  | 108 => 0x1a89
  | 109 => 0xd0c
  | 110 => 0x104c
  | 111 => 0x1a8c
  | 112 => 0x1049
  | 113 => 0x104953
  | 114 => 0x105292
  | 115 => 0x104a52
  | 116 => 0x2cd
  | 117 => 0x19cd
  | 118 => 0x105352
  | 119 => 0xccb4b1d
  | 120 => 0xb4b0cdd
  | 121 => 0x184e
  | 122 => 0x104cd2
  | 123 => 0x17da53
  | 124 => 0x104d52
  | 125 => 0xd0a095c
  | 126 => 0x104a095c
  | 127 => 0x104d095c
  | 128 => 0x104d14
  | 129 => 0x104a
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 47
  | 7 => 906
  | 6 => 1585
  | 5 => 549
  | 4 => 60
  | 3 => 7
  | 2 => 2
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
  | 8 => packedAt gbK8 (1369+((h/21+packedAt gbK8 (1222+(h % 21)*7) 7) % 92)*7) 7
  | 7 => packedAt gbK7 (37559+((h/367+packedAt gbK7 (33522+(h % 367)*11) 11) % 1322)*11) 11
  | 6 => packedAt gbK6 (83100+((h/585+packedAt gbK6 (76080+(h % 585)*12) 12) % 2107)*12) 12
  | 5 => packedAt gbK5 (34301+((h/191+packedAt gbK5 (32391+(h % 191)*10) 10) % 919)*11) 11
  | 4 => packedAt gbK4 (4347+((h/21+packedAt gbK4 (4200+(h % 21)*7) 7) % 92)*7) 7
  | 3 => packedAt gbK3 (575+((h/2+packedAt gbK3 (567+(h % 2)*4) 4) % 16)*4) 4
  | 2 => packedAt gbK2 (186+((h/1+packedAt gbK2 (184+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x83fff070383f83f807fffffffc52023e04cfff
  | 1 => 0xfc381f803fc3fc3ff83c3c0f00ad1dd91b72cc
  | 2 => 0xffc01fffc003ffc0003fc00fff31e1e1e3830f
  | 3 => 0x1ffffffc0000003ffff003c1fe01fc03f0
  | 4 => 0x1fffffffffffffc0000003fe0001fffc00
  | 5 => 0xffffe000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8048400008048048108444210800000a004455
  | 1 => 0x9410d18119419412709e286a18050cd90952cc
  | 2 => 0x5a8116b541035a80a12aa08cf131616163830a
  | 3 => 0x10021b59b5a81001423333c822c1b601bc03a0
  | 4 => 0x42040c6e263263258700010043fa0000d6a800
  | 5 => 0x6327800c042042060400020083fedbb4000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeeaaa0feeefeeafeeeaaa0feeefeeafeeeaaa0feeefeeafeeeaaa0feeefeeafeeeaaa0feeefeeafeeeaaa0feeefeeafeeeaaa0feeefeeafeeeaaa0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36332
namespace PEqualNP.Outside.L_meta_36332
open PEqualNP.Outside.L_meta_36332.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 2 := bs0_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 24 := bs3_3_0
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
theorem bs3_4_96 : Interval s3Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 117 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 46 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 56 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_768 : Interval s4Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 781 := (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat bs4_4_288 (concat bs4_4_320 bs4_4_352)))) (concat (concat (concat bs4_4_384 (concat bs4_4_416 bs4_4_448)) (concat bs4_4_480 (concat bs4_4_512 bs4_4_544))) (concat (concat bs4_4_576 (concat bs4_4_608 bs4_4_640)) (concat (concat bs4_4_672 bs4_4_704) (concat bs4_4_736 bs4_4_768)))))
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
theorem bs4_5_800 : Interval s4Atlas 5 800 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 801 := (concat (concat (concat (concat bs4_5_0 (concat bs4_5_32 bs4_5_64)) (concat bs4_5_96 (concat bs4_5_128 bs4_5_160))) (concat (concat bs4_5_192 (concat bs4_5_224 bs4_5_256)) (concat (concat bs4_5_288 bs4_5_320) (concat bs4_5_352 bs4_5_384)))) (concat (concat (concat bs4_5_416 (concat bs4_5_448 bs4_5_480)) (concat bs4_5_512 (concat bs4_5_544 bs4_5_576))) (concat (concat bs4_5_608 (concat bs4_5_640 bs4_5_672)) (concat (concat bs4_5_704 bs4_5_736) (concat bs4_5_768 bs4_5_800)))))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 2 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 7 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 60 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_544 : Interval gbAtlas 5 544 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 549 := (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)))))
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
theorem bgb_6_1568 : Interval gbAtlas 6 1568 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1585 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))) (concat (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344))) (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))))))
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
theorem bgb_7_896 : Interval gbAtlas 7 896 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 906 := (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)) (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 bgb_7_416)))) (concat (concat (concat bgb_7_448 (concat bgb_7_480 bgb_7_512)) (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640))) (concat (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768)) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 47 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 16, 18),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 36, 38),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeeaaa0feeefeeafeeeaaa0feeefeeafeeeaaa0feeefeeafeeeaaa0feeefeeafeeeaaa0feeefeeafeeeaaa0feeefeeafeeeaaa0feeefeeafeeeaaa0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4277054112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36332.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[2,3]⟩,⟨.or,[2,3]⟩,⟨.and,[0,5]⟩,⟨.or,[0,6]⟩,⟨.or,[0,7]⟩,⟨.or,[4,8]⟩,⟨.and,[10,12]⟩,⟨.or,[9,13]⟩,⟨.or,[1,11]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277054112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277054112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36332

open PEqualNP.Outside.L_meta_36332 in
theorem PEqualNP.Outside.L_meta_36332 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277054112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277054112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
