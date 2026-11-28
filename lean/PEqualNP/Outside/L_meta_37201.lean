import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37201.Model
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


end PEqualNP.Outside.L_meta_37201.Model

namespace PEqualNP.Outside.L_meta_37201
open PEqualNP.Outside.L_meta_37201.Model
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

def SBf (j : Nat) : Nat := [8, 7, 6, 4, 5, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37201

namespace PEqualNP.Outside.L_meta_37201
open PEqualNP.Outside.L_meta_37201.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x1200f800c690174a00000101422a26053ab420131944606230008691140d49b2854e9238787875058010009058e001032001d200638a1520c1ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x881be501027ca0206e94040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc2fca3985f54730dfa0e61bd41cc3be6398774c730df20661bc40cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630bea8c61bf418c37a8318778c630ee18c617e508c37c81186f10230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4987bd4930b7a92617c524c3d8a4985b14930bfa8a61f7514c2eea2985f14530fa28a6174514c37e82986f50530ef98a61dd314c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea9061de320c3b864185f94430bea8861bf410c37a8218778c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c837e83906f50720f790e41ed21c837c81906f10320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef32883d865105f94620bea8c41bf418837a83107b88620f610c417e508837c81106f10220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53482fea2907dd4520bba8a417c51483e8a2905d14520dfa0a41bd41483de42907b48520df20241bc40483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef32083d864105f94420bea8841bf410837a82107b88420f6108417e500837c80106f10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21bd41c437c81886f10310bfaa421bf548427ea9085f95210beaa4217c5484378a9084f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21bf418437a83087dcc610fa18c21f721843e843085f94210df20421bc40843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa0a21bd414437c80886f10110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2086fd0410dea0821f731043e862087dc8410fa108217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xe435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0ef94d41dea9a83bc535077ea4a0ef94941dea9283bc525077e64a0ef8c941de99283bc325077ea2a0edd4541dfa8283be505077aa0a0ef141419e282837e541067ca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31ef19663dc32cc77e8398ef50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31f7294636e528c6faa518fb54a31b6a94637e518c77e8318ef50631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7bc6498f70c931dfa0a63bd414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c77e8218ef50431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87de6590fb0cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53887bca710d794e21bea9c43dd53886baa710df14e21bea94437e518877e8310ef50621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f799243ec324877e8290ef50521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53086faa610df14c21bf290437e510877e8210ef50421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40bf296817d52d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c817e509037e81207ed0240dfa9c81be539037aa7206f14e40dfa9481be529037aa5206f14a40df99481be329037a65206f0ca40dfa8c81be519037aa3204f54640de28c81bf319037c63206f4c640de18c81bf219037c43206f48640de10c813e50902fea6a05f14d40bfa92817c52502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53102faa6206fd0c40df21881bd431037886205f94840bea9081bf421037c84206f50840de210817e51102faa2206fd0440df20881bd411037882205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4206f14840df99081be321037a64206f0c840dfa8881be511037aa2204f54440de28881bf311037c62206f4c440de18881bf211037c42206f48440de10
  | 2 => 0x18c000000008000120180080100e00c000010020180100100a0000080300a0000100900c00400800004014008000000000000200a000020050000100580d006008008000020000300700200c01001000000000050080100100100000c018000040200000000200c0180000600000001006000010000000180000101c01c000010020100080b0020300880100000400802006008018110000000080c0020040180000000c010020000480780103200400000002018000020000040300800002c008010200080c001004000000060080040400700c03000800014000048000000000600101602c0000000602803802006000010020040000000100400c01808004004048000060400080000a0041200901001c0b80600a0040300000e0100380100402003008004008008020000000080900c0040100000400000000010054120070000180180000002401000006000000090020000280700200400007004000000040040100080000c0340000500200003df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250fdea4a1dbd4943be29287ec5250ed8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855f5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6215f54c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997bd0b32f6216657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cbbe86197710c32bf29065ef420cbd8841977cc832f719065dd320cbda6419734c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef943419f28683bd50d0778a1a0df552419eaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83b
  | 3 => 0x5c3ce7c52c2bf05a294379795284a87500d5669a451ae84a85854198843c7f16e0bc3a679400000000000000000000000023e0a000059000000001310d8266001480003d29a0001530005c12c8000003e40100053a158e12e9060000000aa59200000000000ae80000058e935362253fe2102a27a162bf84fa632b20f41b91054ebdcf326a08c000000e70fe0004c00000087c000000266b55183b306130e90756308710eb061a63d00000023000000000000488002b025a00000181000001048000000000000000000188a290000003b0005c40016d9eb6006f8002440008b000000000000670001f64903e28b3c2a24a22d327c6388ca28000000000805640002580026e00000000274000d29971e60004ea193c82206a1855c60000008e416000908414be92c00000406000ba0de3ea268001b131e69c7f28059a0000e000000000000c2104bc063b095b443c000000002cc6800020662400000262000001b450c7d06eaa23d0b151a2ea4ac0000015f09cc7c001d01860d0002cf00000110800320000742e50008c8000005a2000000000005152e00029800000270414c15252382102512017f0001340002c00000056a04000bec000000000000013b0000009f9755cc00000000000aa0000004aa010000166260000fad633e000003084e826400223000029662bc000000001f36404d400000000000c20004b60885f80f000000662de4240003d00020024c002413163e02180014e6bd2415e2606e41e00000032c71a6e2e46cd3b8574761100001733c2340d89210286c82a9245c8454e1c90c89e4049cd0000548323f36cb389900040236ccb0001a41ec0031d54a0001c0003e44ac8e00060e000669b84de0000013961a001210000647e4eca08000000002e7000000e62f6000000b78d93b80003a00038a0008711a4ea6343ba36000ab5158ee4dab549e2105f4c1164000522af87ba185a81557628f074000ea00c326b640008c22c4355c821000000000ec000b407912f33811d1c8006246809302442abf0bf2491fa428002f31428580000000002c00000000bac000280002c0000b4344038712641521280003e0d0c702e9bd0008507b0c0000000a12c417c96800000000c6400000174c2c001c3000a78d0806140001501e34a4720ad0513240015c0005c86f0358000005e800000000b040012902400138a504fe33c8100029a524000b645e000000003b61e0ef08f000000f11ae1d600000000000160000004f0504bb15b3de0000000014447c000530000fc24adf1765dd390ca05c3983021352e5cceb9f822e270e39b703c1cc8082f286000001520005b53e8261e283c8591e3522dd46ad83a2000002c62a0918001201b8c305c871604000c6000508000001e04f6c3d700364fc0ac1289b394938d40c50be5a09e8115843c1601c4
  | 4 => 0x8494e54c718d52bb0003e8fd0974ec001770000005ec000000000c54382a000a59690054402151e1342c8594000000000000000057a0009c0c400052000000000574d809e000474b8a2740a8dc001630000001ca2a5103696180816aab02d1124ba7dc3f06e15e69822895554ac516a9a0001218f3162ce3bd651fb2d89440007d49e320b1000532ad91ab1b486888000a43dc5a8000000c60000028c0007d8898271be35d2f16e032381261403e0001471bb00000000180000000000e10002ad77800000000001fe000000310701508c45e9cf1ea1a4918c9000000be12541801c2915444c9cd0d0000003540000000046d2280010c0000d000356a6000001000608a5af42f0ad444800000000003102aaaa4748000808cc33247000000002070004b00029f2a25ac000ed00053c0005e5ba000971a40001b000000116001429d6000000000001ca0814a8290ce0018aaaf1f8818cc1a342e1b4943172acc515b9c0028808bea9b0007f4118c10209f086000000be0002b44c0891789da5ae1a8e723d41c2408aaff30c650001df3ba000d6000000000562fd0b8a2800059030001002a45da000278ff364000ec160122c380194630e4500e8721069acc88962b010882079114a057a9ba3aa7a8f62cb24e001808e436a0000000032a00000169000000000004cebc98d00000066c3285b00000149800000185068b850472ce0aab066ab8002614ae4d8ce835332000a50001a2b8533253460a848398a6142b86b19a2ae29843af9000599819ed4ca000df91128e0011d000000000001
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xc404831c5310120cdd4440483345110120d314e204836451881209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209b594320834d530c8208f992510823d6494420cd94541083355150420ae181410826d6588420b398e210826f6548020b318d20082e461480209ed95200823e64d4f108f59353c426e62d4f109b58b53c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c433561d5210ce98354843356115210ce980548423e6494e108f592538423f6454e108f191538426f6254e109b189538423e6494a108f592528423f6454a108f191528425f6354a109718d52842ba60d0610ae18141842b56190210ad584408423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e60151108f180544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524423e65d0510c7d4f414431c53d0510cbd4b414432c52d0510ae983414423c6550510c7d4d414431c5350510cbd49414432c5250510ae181414423e6590110c7d4e404431c5390110cbd4a404432c52901108f994404431f5310110c714c404432f5210110cb14840443545384110d914a104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d5185530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520423e64944108f592510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410435553cc4109d594310436552c84109d594210423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400427965840109dd9510042d46344010b918910043b040440109ed9510043b34144010
  | 1 => 0x2ba60d4440a798c511029d6314440ab98851102ad6214440ae980511023e658c4408f59631102ae628c440ab58a3110335518c440cd54531102bb604c440ae181311023e650c4408f594311023e65884408f596211029e6388440a758e21103355188440cd54521102bb6048440ae181211023e65084408f594211033a60940408f58654cc23f61553308f99251cc23d64947309b98a51cc26d62947308fd9741cc23d65d07308fd9541cc23d6550730ae18141cc26e62d52309b58b548c23e6494a308f592528c23e64946308f592518c2ce628c6308f587544c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c23d6115130cbd53524c32c54d4930cbd50524c32c5414930cdd53514c33454d4530d9d4b514c36452d4530cdd93514c33464d45308f990514c23d6414530cdd50514c3345414530d9d48514c3645214530cd990514c33564145308f997414c23c65d0530cbd4b414c32c52d0530cdd47414c33451d05308f995414c23c6550530cbd49414c32c5250530cdd45414c334515053097997314c34c52cc530d5147314c34c524c530d5145314c23e6590130cbd4a404c32c5290130cdd46404c33451901308f994404c32f5210130cb148404c3375110130cd144404c34c528c130d5146304c26e62150309b588540c27661150309d584540c23e6494c308f592530c23f64548308f191520c34d520c8308f992510c23d6494430cd945410c3355150430ae181410c25d658c430b398a310c25f654c030b3189300c2d4614c0309ed95300c23d61953208fd8554c823e64d4f208f59353c827661d4f209d58753c823e6414f208f59053c823e64947208f59251c825e63947209758e51c823f65d07208f59741c823f65507208f59541c82b860507209798f548825d63d52208f993538823d64d4e208f992538823d6494e20d3d4c328823e64946208f59251882ce63886208f587544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544823d6115120c7d53534831c54d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f191534826f6254d209dd8553482746154d2097994534831f5414d20c7150534833754d4520cd153514835753d4520d514f514833764d4520cd193514823e64145208f59051483375414520cd15051483575314520d514c51483366414520cd590514823e65d05208f197414831f53d0520c714f414833751d0520cd147414823e65505208f195414831f5350520c714d41483375150520cd145414826e65c8520d314f214836451c8520d314d214836451485208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4
  | 2 => 0x5214941ad98732506b561cc941ad98632506b5618c9418fd95325063c654c9418f994325063d650c941e34c8325069f6354141a718d50506af6254141ab189505063f65504419dd95411073654504419b98854cc66d62153318fd9152cc63c6454b31d354832cc63f64543318f19150cc66e62d52319b58b548c63e60952318f181548c66e62152319b588548c72e5494a31cb552528c72e5454a31cb551528c72e52d0631cb54b418c72e5250631cb549418c74e52cc6318fd91508c63c64542319bd89544c66c62551319ed81544c67860551318f990524c63d6414931b5986324c6ce628c5318f993504c63d64d41318f596540c63e60950318f181540c63e64150318f992510c63d64944318f597410c63f655043197d95310c795414c4319dd95310c63f64540318f191500c66f62540319b189500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c874d530cb218fd9150c863c64543219798f548865d63d52218f982548863c60552219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414e21c794f418871d53d0621c794d418871d5350621d394f218863f64542218f191508865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534863e6414d218f590534866e65cc921b9987324874d530c921b398e214863e64d41218f593504863d65950218f982540863c60550218f990540863e64d4c218f593530866e62d4c218f990530863d6414c219e98053086796014c218f992510863d64944219798e510865d63944218f597410863f65504219bd9521087a541484219dd95210863f64540218f191500865f63540219718d500873551d0740c794d43902af6250e40ab189439029f6350a40a718d429032e5250a40cd54541902ae62d4e40ab58b53902ba60d4e40c7d4e53902ba6014e40a798f529029d63d4a40ae983529032f5294a40ae980529023f654ca408f195329023e650ca408f594329038d320ca40ae983519029e6314640a758c51902ae6214640ab58851902ba60146408f996319023d658c640ab98a31902ad628c6408f994319023d650c6408f996219023d6588640a798e219029d63886408f994219023d65086408f997415033751505409bd89531026c6254c40abd8943102ac6250c40c754c431025f63548409718d521029f6350840a718d421032d5210840cd547411023d65904408fd95401027b6550040ae98353102af6254c40ab189531031d5314c40ab98853102ad6214c40ad98453102b56114c40ae98053102ba60d4840a7d8d521029c6354840a798c521029d6314840cb54852102b66114840ad58452102ba60148408fd95321023c654c8408f994321023d650c840e34c8321
  | 3 => 0x32185100009c23f29e1f0d509031458474229482001128003b87b0002c210eab80022b296001278000002380014a490b3000252000a483ba0b0f01d8000000000503c00064000140b02c0c00c0801c030100700000008010080103415000000000a040060301003400020010400400000028020a0030140001001000040080000801000040540b00409008020040b0880b020000240004c050b8030180b0140501c1500c02004000600d05407000050040000400018020040100c0700006004050042500802000081300c058010000f00c090040100c010201d0081900006014070180e01c0300408004010143c00003044000340e01417064020340100404000000080f00c00004350600e00400048060140000844000000000200800000020700002c010300a0100003c0c00c4405c0007c0600c000080802001004000040c0340400002010090202e0180c0440001c000380300003014040000801c010000009c0b00001000290000a0d0000081803c05020090000e0603002c0308403014000034f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310eac6250f428f9974350b1c53d0d42c714d4350aac6250d42d314f4250b1c53909428f5964310a3f6550842a718d4210a6f6550842b318d4210a7661153329d58454cca3e64947328f59251cca3f64543328f19150cca7661152329d584548ca3e64946328f592518ca3f64542328f191508ca3d61d51328f983544ca3e649513297d8d544ca6f62551328f994544ca3d61151328f980544cb2c54cc932c7152324ca3e64145328f590514ca3e64d41328f593504ca3d65950328f586540ca3e6095032c718d540cb2c62550328fd85540ca3c60550328f990540cb1d54d0c3297594430cacd6210c32cb553420cb8f43d08329b594420cacd6310832e310c420cacd638c83297d95320ca9c644c8329bd95320caac644c832b3d95320cb4f654c832e3d91320cace644c832b3191320cb8c644c832a3191320cb8e544c832e3551320cacf614c832b3181320ca3e64944328f592510ca3f64540328f191500ca7761540329d185500ca6f6254f419b18953d06af6250f41ab18943d071d5310f4197d8d52d065c6354b41a7d8d42d069c6350b41cb54842d06b561d4f41abd8953d06ac6254f41c754c53d06ae6214f41ab58853d06b56114f41ad58752d069f6354b41a718d52d069e6314b41a758c52d072d5214b41ad58452d063f654cb418f19532d063e650cb418f59432d078d320cb41a798f50d069d63d4341ab98b50d06ad62d4341c714d43506af6250d41ab189435069f6350941a718d425072c5250941ad58653506af6254d41ab18953506b76154d41aed8153506b86054d41c754c53506b56194941a7d8d525069c6354941add8552506bb6054941ae181525072d
  | 4 => 0x7d0003a628c4a258000934001e80002c9748053946703ea4e2a66b0970154700bc002f92b60708d97e31277497a430b42c034a285da8d1222264b4000f100042e8754b9220006bc000004329fd59a6e12e00000000000001120fd000000002fc000828b9a04318155862273ac58c7a1a21ce2612ba952e2a601815e5181710f00f08c73c4b2091b8299821a0574b613aa8238a210d18000008086397d02278c001ae0007bc001774c4844002cf3482a96802d0d41246e89f3320211b072374544001331aeb182bb095a40f8de9ea05c1d4130ed4d4028118001a44f92e96a0485b070a165b22780a20c000c1d019f05e419c729f74929c01f8ab024474cd000276001648000007d4319fb5545c80005e56a0cc520002c4100e48001104fceb906298bed5b23215a7347c8ff32caf43da800003a8058002e0a58fe1d035a1097789b4aa13c8c0003f2af00f97c36a284870002de970209f85b44255a000000001810ee06c36000000000bd80022c3a29ec7900022823cc0a600548dd5c86d3005ac001fd2b0408e5a225c8700859bf06abb8d48b848ab4c902f136ea247da4059c6f85983a3fc128c5a7134261d359b21b6c00932a219aa4cd40713f49e0aa1934d077ccf18560c000fa2065fe000001245c0a6d02a51000c143f064282061751000000016200019c000000005aea346b1550c2000000c600098c2e80d5068389802758a698000b9000000a2000484000a1800000515038584bca40000ca50e0388e0df3a80eca02ad2c07a51e86b33a91c000824a85e87227300057d7125920a00c5d14e3980000d13221017c0026930c8ec002f55560011d10c20e000e11f2420b791528426e134001750e6884dc000292000ae000000b841c190008270001d53663093c9c7424639428cb0dcafd4fa725d692888ab11fc201508294de0ac3a28f17a798f88002cc3c460800586224000f851460c451c34eca6852ac01d29f02d93c000164000da1808bc4911a000a988b1b61062a1339ff5ce340d3982576a94001015a805c3f8000ac0017f117428ac1798b553a00130a1a2e85e0cf82c00087d3d1e42b210c3c8101ea38895acd558918fb0d32263cd36934582645169f32b4b7ce92a05ee4a54e1e53c033cec1972f6355578a25b62b845ae32320e4f690f0622a51f1bb00e024908004620002920f00094d4f000000000d80002fe4c4a384c178000378655ac0c87791524a8b8918a03368d4001c10cc9f90096d158110229844eeb20662a90007b85b0f65fa6ace7192616a04ab07010c479819034466c58506c378380821c60009980f050440b990dadc04a001459de5d0030718002c83240b1692ba620cc028134274342a81f849c5f0f01d8a9c5792d51c001040c83906d0a82e504014c003080a269400000284000882dd10a30d4c8484b6000a
  | 5 => 0x428f38000000015f02158e76951ab73729f44a8540000008f9eb2dc2301e80009c870a901d0048f0000bf11a80152250000000488b131e1800009329a9b06c98d2542ec962305700000084b14e2dd6ab0118a000ed847564be800000498710001673c23dcb40d1496958b29571020001e0001a80001100006e0000019526abc1198004e8a191ca654be065068625943989b07a5e80194a00006884d76000000be0002643b206cbcad1168650bb0131bc0009d13d5224a1658c4272000002151323aca410d0000008900000000
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x100a3c6cd2c2ed420046140265030c904a753806e19980000001f62004a200019135e0000b1e0000000394800e04000008550000c0c2e2490a8800440025aac00038341966cd0a0085021c000000450016100000014104c18c6312a81948e74991320ca46b88c899065239c0644c832918ed2a2641948c76551320ca86392a621e83431cd5210b41a18e4a98a7a0e0d5358853d068639aa4296838358d5214b41a18ea99065a0e0d654c832d0706298c4a1a838318c5250941a18e4a98a6a0d187054c535068639aa4292834a1c15214941870e0b2864a0d0c754c832506863a2a419663431d1530cb21a18e8a986490d487054c3248707298c4a1c818318e5250a40a1ce5a9ca72050e73d4a5290287baa6419481431c95310c40a18e6a90842050c7254c5310306a9ac4298818554d6114c40a18e6a90a42060d635485210312a92c2290810d5c4654c840a18ea990642060d654c83210312b12a3188818558d5188440a18e8a90641863151181410c2873a6a619441431d1530c820c62a2302821063161983548430c298c0a0a218a1486050510c2aa6b0880086255258440043483188088021a81884044010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xa0068400202885811da544c83280c87595320cb41a048254d6114c40a04835496114840905811d5320c84080c87595320c840
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
  | 7 => packedAt s0K7 (6+((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s0K6 (788+((h/14+packedAt s0K6 (704+(h % 14)*6) 6) % 53)*7) 7
  | 5 => packedAt s0K5 (24564+((h/267+packedAt s0K5 (21627+(h % 267)*11) 11) % 1163)*11) 11
  | 4 => packedAt s0K4 (32278+((h/260+packedAt s0K4 (29678+(h % 260)*10) 10) % 938)*11) 11
  | 3 => packedAt s0K3 (2870+((h/18+packedAt s0K3 (2744+(h % 18)*7) 7) % 81)*7) 7
  | 2 => packedAt s0K2 (368+((h/2+packedAt s0K2 (360+(h % 2)*4) 4) % 9)*4) 4
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
end PEqualNP.Outside.L_meta_37201
namespace PEqualNP.Outside.L_meta_37201
open PEqualNP.Outside.L_meta_37201.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1a2441000006539b5e0000e28005a52c2088c120150a464cf000e61683081802c1e990a2500400038ac0173e354955c74282480000440c0000381007003242ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1a800ce4f0011c84481f940740007024387a05040967900138760d001b0f6590914c4c6d19060c2221495834392489c5e5f0583c66771b800b841300104a2326044a4623a8c00c40420003e0039814001e01874001b2c1b8007d00000d20000000486a38000002100000004d098b802432f110f86300050002d330d832001f0d0fe5a0b8588a08002142a552e8a8007e1c1280e723b0ace86f1620d02020000104681e9e1005b189945054231907857288801871358083c8040008800640800b0081c00000c0c88080818000000000c180864280424180024f8480c283c2c3c3c467ca721cf54a439ea8c873e5090e7ca621e794c439ea90873d5110e7ca021cf94f429ea8e853e50d0a7aa92157d4d42ae29a859f5350a78a6a16714d428e29a85af5250a7ea2a14f141429f2a0853f54cca78a9994f952329eaa4659c438caeca3195d546329faa2653c544ca7ca8194f55032ce218653e53d067aa5a0cf943419eaa4835f53506b8a6a0e7d4d419e29a839c5350638a6a0cfd4941dba8a833c505067ca820cfd53319e2a6633e548c67aa918e710e31b7294636d528c67ea898cf151319f2a0633d540c7388618cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cf951219eaa2433e540867aa810f948421af29c815d539027ca7206794e408f29c819d539027aa5204f546409f284813e531027aa4204f544409f28081ba501027ca9984f55330ce21e613e548c27aa9184fd51309e2a2619c434c2dea4985b14930bba8a6174514c27ea8184f150309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2e020b2818040039c6a601602a024032794c0048008c02260a2040003890071428718d51d0a1e63943428d58454ccb14439463287594430ca8d6210c328718d52d061e63943418b58854cc70c4394a3187594430c6956110c318718d544863860551218718d540861c63548408718d511030c4314930c510c514c21e63d50308b588540c23561150308718d54c821e63d52208718d54c421e63d5210
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
  | 4 => packedAt s1K4 (3970+((h/44+packedAt s1K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s1K3 (1036+((h/8+packedAt s1K3 (988+(h % 8)*6) 6) % 35)*6) 6
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xc0ffffc0fff83fff07c1e0fffe1fe07fd13e73
  | 3 => 0xff03ffff03ffc1fff801ff07ffe1ff81e1cf9c
  | 4 => 0x3fffffc0001fffffe0007fffe0001fe0fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x44100888209000002942410900222a280650a5
  | 2 => 0x92299106492270cb0290a8d2b2154154d12652
  | 3 => 0xa4aa2121a46135550213a44d5419505618b18
  | 4 => 0x2cb344a49074a5a69cf4108769980619ba0de0
  | 5 => 0x30c38738e38739f8e739dce071111861fdf000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37201
namespace PEqualNP.Outside.L_meta_37201
open PEqualNP.Outside.L_meta_37201.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x20f710f510
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (34+((h/1+packedAt s2K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfe07ffc0fffffe07ff03ff83ff07fffdc78e3f
  | 1 => 0x7ff80fff01fc0ff83ffc0ffc1ff83e02f8f3cc
  | 3 => 0x7fffffffffffffffc0000fffffffffff00ffff
  | 4 => 0x80000ffffe000ffffffff0001fffc003ff03f0
  | 5 => 0xfffff00000000fffffffffffe0000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1290a446244946014b5152a1254272a8c38615
  | 1 => 0x1432648a1c915658155545a50b4a3418d8b2cc
  | 3 => 0x48414910492208aa8082094a5294895300596a
  | 4 => 0x51658a24903a6b34e69a60421ce710636d03b0
  | 5 => 0x61860c38e1c38dc738e38e7380842183b6ec00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeee00ee00aa00eeeeee00ee00aa00eeeeee00ee00aa00eeeeee00ee00aa00eeeeee00ee00aa00eeeeee00ee00aa00eeeeee00ee00aa00eeeeee00ee00aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37201
namespace PEqualNP.Outside.L_meta_37201
open PEqualNP.Outside.L_meta_37201.Model
def s3K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (6+((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc0fff03ffe07fc1ffc0ffc1ff07fe07ee3ce73
  | 1 => 0xff03ffc0fff81fe0fff03fe0ff83ff817c739c
  | 2 => 0xffffffffffffffff00003fffffffffff807fff
  | 4 => 0x3ffff00001fffffffc000fffc0001ff83e0
  | 5 => 0xfffc000000001fffffffffff00000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x5219118a24aa8c052d454d093427212c61c631
  | 1 => 0x8649228648a2aca05555152854a34b046c5294
  | 2 => 0x82244109104114a020822528948945180294a
  | 4 => 0x2cb289241d34d6739a698210ee710619b683e0
  | 5 => 0x30c30e38e1c71b9ce38e3b9c08421861db7c00
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xeeeee0e0e0e0e0e0eeeee0e0e0e0e0e0eeeee0e0e0e0e0e0eeeee0e0e0e0e0e0eeeee0e0e0e0e0e0eeeee0e0e0e0e0e0eeeee0e0e0e0e0e0eeeee0e0e0e0e0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37201
namespace PEqualNP.Outside.L_meta_37201
open PEqualNP.Outside.L_meta_37201.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1ffc1fffff83f83fe0ff83fc3ffff03ec733f3
  | 1 => 0xe0ffe07c1ffc1fc3ff07fc1fc3c0ffc179cd9c
  | 2 => 0xffffff801ffffffc0007fffffc00ffff81fe1f
  | 3 => 0xffffffe0001ffffff8001fffff0001fe0fe0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4244451104250808a849a124065290944310b1
  | 1 => 0xca48c321292129416942a50c4286a584594594
  | 2 => 0x491080a5242129410844a52a8084a2980aa0a
  | 3 => 0x94a2124a034a54e65290421b312c0309ac0f40
  | 5 => 0x18c39c739c739f3b9ce7738222308c31f7f000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37201
namespace PEqualNP.Outside.L_meta_37201
open PEqualNP.Outside.L_meta_37201.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x2600000002cb910a0000012213040e8ce80000000000a0c9f2a000005470c0000016245a8078314012802418a0000000224e3410000000000000d8000840805200d000000000007870c0001596200000205000400004001000414101ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xed5d3d39041000008000dca44c00002c006cc000000000000000bc000168140124c89189603ce488295800000134000050d8003800000000000000000508000000d4003000d0e000000021780000000044000000000120000154016c0000000001457c0000fd8058f5480000950c98751c6571289c24400870014d74cc000164c478a8ac00b8a0000c55108d1800b00000000184015000001c00012c006000010084e9307d401848f8005c34b400000000f000000114006806020000080808020000240e0400060202021800020414000002000000000006013e5390e7aa121cf94c43cf298873d5010ebca7215754e42bba8a85745150b3887994f952329eaa4653f544ca78a8996710d32bba8a6574514caf6a0995e14132bd2808379501067ca918cf55231bd2846379508c67ea898cf151319faa2433c544867ca810cf55021af298435d53086f4a010de540219f29e813d54902eca3205d54640afa9a815c535033ea6a04f14d40ce29a811c5350376a0a04f95040bb2888175511027ea9984f153309f2a4613d548c33887185d94630baa8c613f544c278a8984f950309eaa0619c430c2dca4185b54830bb2886175510c27ca9104f55220bb28c4175518827ca8104f55020af298415d53082eca2105d54420db21e21b443c436e81886d503109f2a4213d54842eaa3086e50210dca0221b6434436886887cd4110dba0221f2404436a80887c50110d8a0221f330443e060887c88110f8902213e540427aa8085d94410
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x28824500c3410d22c64c010000250e1cf4110000071004410e716014542c610c504ca1d6510c30c310d520c21c6355220a518d40c42986350210a618d40442b16010d10ac59240442946350110b418d40443936350110ac18d40443906350110a418d40442b364cc110ac5903044390430c110b858830442b16488110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x102004917610c304434021ac418221241cd6488110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s5K5 (841+((h/15+packedAt s5K5 (736+(h % 15)*7) 7) % 96)*7) 7
  | 4 => packedAt s5K4 (2937+((h/33+packedAt s5K4 (2673+(h % 33)*8) 8) % 189)*8) 8
  | 3 => packedAt s5K3 (833+((h/7+packedAt s5K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s5K2 (150+((h/1+packedAt s5K2 (147+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf03ff07ffffc3e0f1f0ff0fe3fffe07c4733f3
  | 1 => 0xffc1ff81f0ffc3f01ff0ff0fc781ff8079cd9c
  | 2 => 0xfffffffe00ffffffe000fffff801ffff81fe1f
  | 3 => 0x1ffffff0003ffffff000ffffe0003fe0fe0
  | 4 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1485111448226202058938920ca521284310b1
  | 1 => 0x2195230c894a26500b985986450d4b08594594
  | 2 => 0x42084420229000a5200082289010945180aa0a
  | 3 => 0xb288849201889395222000d22580612ac0f40
  | 4 => 0x8c310e71cce333ce9cccecc00461186377f000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfee0eae0fee0eae0fee0eae0fee0eae0fee0eae0fee0eae0fee0eae0fee0eae0fee0eae0fee0eae0fee0eae0fee0eae0fee0eae0fee0eae0fee0eae0fee0eae0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37201
namespace PEqualNP.Outside.L_meta_37201
open PEqualNP.Outside.L_meta_37201.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x38f00904cc1bb1746df0328284975e5490d2611f91568c00040d403804f458066d1b0000e47800000000007401e000192c341400800ec6214a8800054a138032900063e01496000000000b83805a60700000004000005c0060e00180000018c003060001ffd5001fe54007f55007fc5401ffd4c01fe53007f54c07fc53007fd0c01fe43007f50c01fc4301ffd48017f52007f94801fd52005f54807fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc3201ffd4405fe51007f54405fc51007fd0405fe41007f50405fc41007fcc405fe31007f4c405fc31007fc8405fe21007f48405fc2100ffd4003fe5000ff54003fc5000ffd0003fe4000ff50003fc4000ffcc003fe3000ff4c003fc3000ffc8003fe2000ff48003fc2000ffc4003f71000ff84003fd1000fd44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x26209ff9013104ffa8098827fc404c413ff9826209ff8c13104ffa6098827fc304c413ff9026209ff8813104ffa4098827fc204c405ff8826202fdc4131017fc209880bfd104c413fa8826202ff0413102ffecb90816ff65c840bff32e4203bf9972102efccb9080e7e65c840bfeb2e4200bf5972102efacb908027d65c840bfe32e4205bf1972102ffec990816ff64c840bff3264200bf9932102ffac990802fd64c840bfe3264205bf19321047fea990803fe54c8401feaa64208ff1532102ffec790816ff63c840bff31e4200bf98f2102ffac790802fd63c840bfe31e4205bf18f21047fea790803fe53c8401fea9e4208ff14f21007fe8790803fe43c8401fea1e4200ff10f21015fcc590817ff52c840bbfa964205ff94b2102ffaa5908177d52c840bfe2964205ffd0b2102ffc8590817fd42c840bfe2164205ffccb2102ffc6590817fd32c840bfe1964202bf58721017fea39080bfe51c8405fea8e4202ff14721017fe839080bfe41c8405fea0e4202ff10721017fe639080bfe31c8405fe98e4202ff0c721017fc439080bee21c8405fb10e4202ff08721017d84390817ff60c840b7fb064205ff9832100dfcc190817fd60c840f7eb064205ff1832100df8c19081fff50c840fff2864207ff5432103ff8a19081fff40c840fff2064207ff5032103ff8819081fff30c840fff1864207ff4c32103ff86190817ff20c840bff1064205ff4832102ff8419080bff10c8405fb8864202ff84321017fa219081ff510c8405fe0864200ffd9521005feca9081bfe65484077f32a4200ff59521005faca9081bfc65484077e32a4200ffd9121005fec890803fe64484017f3224200ff59121005fac890803fc64484017e3224206ffd5121007fca890803fd544840dfe2a24200ffd8d21005fec690803fe63484017f31a4200ff58d21005fac690803fc63484017e31a4206ffd4d21007fca690803fd534840dfe29a4200ffd0d21007fc8690803fd4348401fe21a4202bfd8921037fea4908037f524840bff2924200ff54921006faa490817fc5248401ffa124205ff90921007fa8490817fc4248401ff9924205ff8c921007fa6490817fc32484057fb0a4202ffd4521017fca29080bfd5148405fe28a4202ffd0521017fc829080bfd4148405fe20a4202ffcc521017fc629080bfd3148405fe18a4202ffc852102fee429080bfe2148405f710a4202ff08521017d8429080bf42148409ffb024204bfd8121027fcc090806fe6048409feb024204bf58121027f8c090806fc6048409ffa824204ff94121027faa090813fc5048409ffa024204ff90121027fa8090813fc4048409ff9824204ff8c121027fa6090813fc304840bff9024204ff88121027fa4090817fc2048405ff8824202fdc4121017fc209080bfd1048409fa8824202ff04121
  | 1 => 0xbfe4150405df20a8202ff105410177882a080bf44150405ff18a8202ff0c541017fc42a080bfc215041bffb02820dbfd814106ffcc0a0806fe605041bfeb02820dbf5814106ff8c0a0806fc605041bffa82820dff9414106ffaa0a0837fc505041bffa02820dff9014106ffa80a0837fc405041bff982820dff8c14106ffa60a0837fc305041bff902820dff8814106ffa40a0837fc2050405ff8828202fdc4141017fc20a080bfd105041bfa8828202ff04141007fecb98802ff65cc419ff32e6203bf99731006fccb9880e7e65cc401feb2e6200bf59731006facb988027d65cc419fe32e6203bf19731007fec998802ff64cc401ff3266200bf99331007fac998802fd64cc401fe3266200bf19331067fea998803fe54cc401feaa6620cff15331015fcc798833ff53cc401ff29e6200ff54f31067f8a798803ff43cc401ff21e6200ff50f31007f88798803ff62cc401ff3166205bf98b31007fac598802fd62cc401fe316620cffd4b31006fea598803fe52cc401fea966200df54b31067f8a598803ff42cc401ff2166200ff50b31007f88598803ff32cc401ef9966200ff8cb31007fa6598803dd32cc401fe1966202bf58731017fea39880bfe51cc405fea8e6202ff14731017fe839880bfe41cc405fea0e6202ff10731017fc639880bde31cc405fb18e6202ff0c731017b8639880bfe21cc405fe10e620bffd833105dfec19882ffe60cc4037f306620bff5833105dfac19882ffc60cc4037e306620bffd433105ffca19882ffd50cc417fe286620bffd033105ffc819882ffd40cc417fe206620bffcc33105ffc619882ffd30cc417fe186620bffc833105ffc419882ffd20cc417fe1066202ffc4331017ee219880bfe10cc405fe886620bfd44331017f82198803ff654c4017fb2a620aff9953101dfcca98803fd654c4017eb2a620aff1953101df8ca98803ff644c4017fb226200ff99131005fcc898803fd644c4017eb226200ff19131005f8c89882bff544c401ff2a26200ff55131057f8a89880aff634c415ffa9a6200ff94d31007faa69882bfc534c401ffa1a6200ff90d31007fa8698803fc434c401ffb126200bfd8931007fcc498803fd624c401fe3126205bf18931057fea4988037f524c401ff2926200ff54931006faa49882bfc524c401ffa126200ff90931007fa8498803fc424c401ff9926200f7cc931007fc6498803fd324c401ee9926200ff0c931015fec29880bff514c405ff28a6202ff54531017f8a29880bff414c405ff20a6202ff50531017f8829880bff314c401fb98a6202ff8c531017bc629880bfc314c405ee18a6202fd0c531017fc429880bfc214c413ffb026209bfd813104ffcc098806fe604c413feb026209bf5813104ff8c098806fc604c413ffa826209ff9413104ffaa098827fc504c413ffa
  | 2 => 0x51007fe86a8803fe4354401fea1aa200ff10d51007fec4a8802ff6254401ff312a200ff58951007f8c4a8816fc6254407ffa92a203dfd495101ffca4a880ffd5254401bea92a203ff14951007fe84a8803fe4254401fea12a200ff10951007fe64a8803fe3254401fe992a200ff0c951015fec2a880bff5154407fba8aa202ff94551016fca2a880bfc5154405be28aa202fd14551017fc82a880bfc4154405ff18aa202ff0c551017fc42a880bfc2154425ffb02a212bfd8151097fcc0a8806fe6054425feb02a212bf58151097f8c0a8806fc6054407ffa82a203ff9415101ffaa0a880ffc5054425ffa02a212ff90151097fa80a884bfc4054425ff982a212ff8c151097fa60a884bfc3054425ff902a212ff88151097fa40a884bfc2054405ff882a202fdc4151017fc20a880bfd1054425fa882a202ff04151087fecba0802ff65d0423ff32e8203bf99741007facba0802fd65d0421fe32e8203bf19741015fcc9a0847ff54d0421ff2a68200ff55341087f8a9a0843ff63d0401ff31e8200bf98f41007fac7a0802fd63d0421fe31e8211ffd4f41007fca7a0803fd53d0423fe29e8210ffd0f41007fc87a0803fd43d0421fe21e8210ffd8b41007fcc5a0816fe62d0401feb168200bf58b41087f8c5a0847ff52d0401bfa968200ff94b41007faa5a08037d52d0423fe2968210ffd0b410077e85a0803fe42d0401fea168200ef50b41087f885a0803ff32d0401ff1968200ff4cb41007f865a080afd61d0405ffa8e8202ff94741017faa3a080bfc51d0405ff20e8202ef90741017ec83a080bfc41d0405de20e8202ff8c741017f863a080bfe21d0405fe10e8210ffd834107dfec1a083ffe60d04037f306820fff5834107dfac1a0843fc60d04037e306820fffd434107ffca1a083ffd50d041ffe2868210ffd034107ffc81a083ffd40d0421fe206820fffcc34107ffc61a083ffd30d041ffe186820fffc834107ffc41a083ffd20d041ffe1068202ffc4341017ee21a080bfe10d0405fe886820ffd44341017f821a0803ff65504017fb2a8200dfd9541004fecaa083bfe65504077f32a8200ff59541005facaa083bfc65504077e32a8200df1954101cf8caa080aff645041dffaa28200ff95141007faa8a083bfc5450401ffb1a8200bfd8d41007fcc6a0803fd6350401fe31a8200bf18d41077fea6a0803fe5350401fea9a820eff14d41007fe86a0803fe4350401fea1a8200ff10d41007fec4a0802ff6250401ff3128200ff58941007f8c4a0816fc625041dffa928200dfd4941007fca4a0803fd5250401bea92820eff14941007fe84a0803bf4250401ff2128200ff509410077a84a0803fc4250401ff9928200ff8c941007fa64a0803fc32504057fb0a8202ffd4541017fca2a080bfd5150405fe28a8202ffd0541007ee82a080
  | 3 => 0xf1046405ff482320d7da4119017fc208c835ff884641afdc42320d7fc211906bfd108c835fa884641aff04232007feca99002ff654c833ff32a6403bf99532007faca99002fd654c833fe32a6403bf19532007fec899002ff644c801ff3226400bf99132007fac899002fd644c801fe3226400bf191320cffea899003fe544c801feaa26419ff151320cffea699003fe534c801fea9a6419ff14d32007fe8699003df434c801ff21a6400ff50d32007f88699003dc434c833ffa926400dfd493202ffca499003fd524c801bea926405ff14932007fe8499017fe424c801fea126405ff10932007fe6499003ef324c80bff1926405f78c932007fec299002ff614c831ff30a6402bf98532007fac299063fc614c8057e30a6419ffd45320c7fca299063fc514c831ff20a6418ff105320c7fc6299063fc314c831ff10a6405ff085320bffec09905eff604c82fff3026401bf981320bffac09905efd604c82ffe3026401bf181320bffea09905ffe504c82ffea826417ff141320bffe809905ffe404c82ffea026417ff101320bffe609905fdf304c82fff1826417ff4c1320bfba609905ffc304c80bff9026417fbc81320bffc409905ffd204c82ff69026405ff081320bffe209905ff7104c82fff0826417ff441320bfea209905ffc104c80bffb286405bfd943202ffcca1900efe650c80bbf32864039f9943202ffaca19002fd650c80bbeb2864009f5943202ff8ca19016fc650c80bffb206405bfd903202ffcc819002fe640c80bfeb206400bf5903202ff8c819016fc640c82bffaa06400ff95032007faa819057fc540c82d7f3186415ffd4c32007fca619003fd530c82bfe2986400ffd0c32007fc8619003fd430c801fe2186405bf9883202ffea4190177f520c80bff2906405ff5483202efaa419017fc520c80bffa106405ff9083202ffa8419017fc420c80bff9906405f7cc83202ffc6419017ee320c80bfe9906405f74c832007da6419017ff610c80bff3086402bf9843202ffac219002fd610c80bfe3086402bf184320affea219053fe510c829fe2886414ff904320a7f88219053fe310c829fe1886405ff8843202ff84219017ff600c80b7fb006405ff9803200dfcc019017fd600c8277eb006405ff1803200df8c01904fff500c827ff2806413ff5403209ff8a01904fff400c827ff2006413ff5003209ff8801904fff300c827ff1806413ff4c03209ff86019017ff200c80bff1006405ff4803202ff8401904fff100c827fb8806413ff8403209ffa201904ff5100c827fe0806402bfd9551007fec8a8802ff6454401ff322a200ff59151007f8c8a8802fc6454407ffaa2a203ff9515101ffaa8a880ffc5454401ffb1aa200bfd8d51007fcc6a8803fd6354401fe31aa200bf18d5101ffea6a880ffe5354407fea9aa203ff14d
  | 4 => 0xafe611080bfeb088400bf5844202ff8c22100afc6110843ffa888420ff94442107f8a221083fe4110821fe2088420ff8c442107f86221017fe211080bfe1088405ffd804202dfec021017fe60108037f3008405ff580420fdfac021017fc60108037e300841fffd40420fffca02107ffd501083ffe2808410ffd00420fffc802107ffd4010821fe200841fffcc0420fffc602107ffd301083ffe1808405ffc804202ffc4021017fd201080bfe100841fffc40420ffee202107ffe101083ffe880841ffd440420fff82021003ff65cc8017fb2e641eff9973201dfccb99003fd65cc8017eb2e641eff1973201df8cb99003ff64cc8017fb266400ff99332005fcc999003fd64cc8017eb266400ff19332005f8c99907bff54cc801ff2a66400ff553320f7f8a99907bff53cc801ff29e6400ff54f320f7f8a799003ff43cc801efa1e6400ff90f32007fa8799003fc43cc801ee21e641effd4b32006fea599017fe52cc801fea966400df54b3202ff8a599003ff42cc80bff2166400ff50b3202ff88599003ff61cc83bff30e6402bf98732007fac399002fd61cc83bfe30e6402bf187320f7fea399077fe51cc83bfe28e641dff907320eff88399077fe31cc83bfe18e641dff8873202ff8439905bff60cc82d7fb066416ff9833200dfcc19905bfd60cc82d7eb066416ff1833200df8c19905bff50cc82dff2866416ff543320b7f8a19905bff40cc82dff2066416ff503320b7f8819905bff30cc82def9866416ff8c3320b7fa619905bdd30cc82dfe1866405ffc83320b7fc419905bfd20cc80bfe1066416ffc43320b7ee219905bfe10cc82dfe8866416fd443320b7f82199017ff658c80b7fb2c6405ff9963201dfccb190177e658c8073f32c6405ff59632005facb190177d658c8013eb2c6405ff1963202df8cb19017ff648c80b7fb246405ff99232005fcc919017be648c8015f3246405ff59232005fac919017bd648c8015eb246405ff1923202df8c919073ff548c801ff2a46400ff552320e7f8a91905efd638c839ffa9c6400ff94e32007faa719073fc538c801ffa1c6400ff90e32007fa8719003fc438c80b7f3146405ffd4a3202efea519017fe528c80bfea946405df54a3202ff8a519017ff428c80bff2146405ff50a3202ff88519017ff328c80bef9946400fbcca3202ffec319017fe618c8057f30c6405ff58632005fac319017fc618c8057e30c641cffd46320dffca31906ffc518c837ff20c641bff106320dffc631906ffc318c80bff10c6405ff0863202ffec119016ff608c80bff3046401bf9823202ffac11906afd608c80bfe3046401bf182320d7fea11906bfe508c835fea84641aff142320d7fe811906bfe408c835fea04641aff102320d7fe611906bfe308c835fe984641aff0c23202ffe4119017ef208c80bf
  | 5 => 0x964201dfccb210177e65908073f32c8405ff59642005facb210177d65908013eb2c8405ff1964202df8cb2108efd6490851ffaa48400ff95242007faa9210a3fc549080bffb1c8405ff98e42005fcc721017de63908016f31c8405ff58e42005fac721017dd63908016eb1c8405ff18e42147fea721003fe5390801fea9c8428ff14e42007fe8721003fe4390801fea1c8400ff10e4202dfcc521017ff529080bbfa948405ff94a4202ffaa5210177d529080bfe2948405ffd0a4202f7e8521003ef429080bffb0c8405ff98642015fcc321017fd61908017eb0c8405ff18642015f8c3210a3ff519084fff28c8427ff1464213ffc832109ffc419084fff18c8427ff0c64202ffc4321017fc219080bffb048405bfd824202ffcc121006fe609080bfeb048426bf5824202ff8c121006fc609084dffa848426ff94242137faa12109bfc509084dffa048426ff90242137fa812109bfc409084dff9848426ff8c242137fa612109bfc309080bff9048405ff8824202ffa4121017fc209084dff8848426fdc4242137fc212109bfd109084dfa8848426ff04242007fecaa1002ff655084bff32a8403bf99542007facaa1002fd655084bfe32a8403bf1954212ffea8a1003fe5450801feaa28425ff15142007fec6a1002ff6350801ff31a8400ff58d42007f8c6a1002fc635084bffa9a8400ff94d42007faa6a1097fc5350801ffa1a8400ff90d420077c86a1003fd4350801fe21a8400ef10d4212ffea4a10037f525080bff2928400ff54942006faa4a1017fc5250801ffa128400fbd094202ffc84a1017be4250801ffb0a8400bfd8542127fcc2a100afe6150801feb0a8424ff18542015f8c2a1097ff5150849ff28a8424ff14542127fc82a1093fc4150849ff18a8424ff0c542127fc42a1017fc2150847ffb028423bfd814211ffcc0a1006fe6050847feb028423bf5814211ff8c0a1006fc6050847ffa828423ff9414211ffaa0a108ffc5050847ffa028423efd014211ffc80a108ffd4050847dea028423ff1014211ffe60a108ffe3050847fe9828423ff0c14202ffe40a108ffe2050847fe9028405ff0814211ffe20a108ff71050847ff0828423ff4414211fea20a108ffc105080bffb288405bfd944202ffcca2100efe651080bbf32884039f9944202ffaca21002fd651080bbeb2884009f5944202ff8ca21016fc65108457f3208421ffd5042087fca821003fd5410821fe2a08405ffd8c4202ffcc621002fe631080bfeb188400bf58c4202ff8c621087ff5310801ff2988400ff54c4210ff8a621043ff4310801ff2188400ff50c42087f88621016fe621080bffa908405dfd484202ffca421017fd521080bbea908405ff1484202ffe8421017bf421080bff2108405fb9084202ffa8421017bd4210801f6a108405ffd844202ffcc221
  | 6 => 0x1feb22a400ff19152005f8c8a900fff5454807bfaa2a403ff95152006fca8a900ffd5454801beaa2a403ff1515201ef8a8a9003ff63548017fb1aa400ff98d52007fac6a9003fc63548017e31aa403ffd4d5201efea6a900ffe5354801bf29aa403ff54d52006faa6a900ffc5354807be29aa400ffd0d52007fc86a9003fd4354801fe21aa403bfd895201ffea4a900fef525480bff292a405df9495202ff8a4a90177c5254807f6292a400ffd8552005fec2a90b3fe61548057f30aa400ff58552167f8c2a900afc6154807ffa8aa403dfd455201ffca2a90b37e5154807fe28aa403df14552167fc82a90b3fc4154859ff18aa42cff0c552167fc42a9017fc2154857ffb02a42bbfd815215ffcc0a9006fe6054857feb02a42bbf5815215ff8c0a9006fc6054807ffa82a403dfd415201ffca0a90af7e5054807fea82a42bdf5415201ff8a0a900f7c5054857ffa02a42bff9015215ffa80a90affc4054857ff982a42bff8c15215ffa60a90affc305480bff902a42bff8815215ffa40a9017fc2054857ff882a42bfdc415215ffc20a90affd1054857fa882a42bff04152006fec8a90037e6454801beb22a400df19152006fec6a90037e6354801beb1aa400df18d52006fe86a90037e4354801bea1aa400df10d5201efec4a900e7f6254807b7b12a400dfd8552166fcc2a90037d6154859be30aa42cdf90552166f882a90b37e3154859be18aa42cdf8855202ef842a90af7f6054857bf302a42bdf5815215ef8c0a90af7f4054857bf202a42bdf5015215ef880a90af7f3054857bf182a42bdf4c15215ef860a90177f2054857bf102a42bdf4815202ef840a90af7f1054857bb882a42bdf8415215efa20a90af751054857be082a410ffd9742005fecba10abfe65d08077f32e8400ff59742005facba1043fc65d08077e32e842affd5342087fca9a1003fd54d0821fe2a68410ffd8f42007fcc7a1002fe63d0801feb1e8400bf58f42087f8c7a10abff53d0801ff29e8400ff54f42157f8a7a1043ff43d0801ff21e8400ef90f42007fa87a1043fc43d0801de21e842affd4b42006fea5a1017fe52d0801fea968400df54b4202ff8a5a1043ff61d0853ff30e8402bf98742007fac3a1002fd61d0821fe30e8402bf18742157fea3a10a7fe51d0853fe28e8429ff90742087f883a10a7fe31d0853fe18e8429ff8874202ff843a1043ff60d08457fb068422ff9834200dfcc1a108bfd60d08457eb068410ff1834200df8c1a108bff50d0845ff2868422ff54342117f8a1a1043ff40d0845dfa068422ff90342117fa81a108bbd40d0821fe2068422ffcc342117fc61a108bfd30d0845fe1868405ffc8342117fc41a108bfd20d080bfe1068422ffc4342117ee21a108bfe10d0845fe8868422fd44342117f821a1017ff659080b7fb2c8405ff9
  | 7 => 0xa18dbff2050c6dff1028636ff481431b7f840a18dbff1050c6dfb8828636ff841431b7fa20a18dbf51050c6dfe0828610ffd9443005feca218cffe6510c077f3288600df9944301cfcca21803fd6510c017eb288600df59443004faca21843fc6510c077e3288635bf9904319ffea8218cfbf5410c21ff2a08600ff55043087f8a8218cfbc5410c697f3188633ffd4c43007fca621803fd5310c67fe2988610ffd0c430077e8621803fe4310c01ef2188600ff50c430077a8621803dd4310c21ffb108600ff9884302dfcc421803fd6210c017eb108610ff1884319ffea4218cffc5210c21ffb088632ff98443015fcc221803fd6110c017eb088610ff18443015f8c2218cfff5110c65ff2888632ff14443197fc8221843fc4110c65ff1888632ff0c443197fc42218cbfc2110c21ffb008631bfd804318ffcc021806fe6010c63feb008631bf58043087f8c021806fc6010c63ffa808631ff9404318ffaa0218c7fc5010c21ffa008631ff9004318ffa8021843fc4010c63ff9808631ff8c04318ffa60218c7fc3010c63ff9008631ff8804318ffa40218c7fc2010c63ff8808631fdc404318ffc20218c7fd1010c63fa8808631ff0404301efec9a900f7e64d4807beb26a403df1935201efec7a900f7e63d4807beb1ea403df18f52006fe87a90037e43d4801bea1ea400df10f5201efec3a900f7e61d4807beb0ea403df18752186fc83a90c37c41d4861bf18ea430df0c752186fc43a90177c21d4807bfb06a403df9835201efac1a900f7c60d485fbfa06a42fdf9035217efa81a90bf7c40d485fbf986a42fdf8c35217efa61a90bf7c30d480bbf906a42fdf8835217efa41a90177c20d485fbf886a42fddc435217efc21a90bf7d10d485fba886a42fdf0435201dfacb290ae7d659480bffb24a405ff99252005fcc929017fd64948017eb24a405ff1925201ffea92900ffe5494807feaa4a403ff1525202ffec729017fe63948017f31ca405ff58e52005fac729017fc6394807ffa9ca403ff94e5201ffaa72900ffc5394801ffa1ca400ff90e52007fa8729003fc439480b7f314a405ffd4a5202efea52900fef529480bfe294a405fb14a5202ffec329017fe61948057f30ca405ff58652005fac329017fc61948057e30ca403ffd465201ffca32900ffc519485dff20ca42eff10652177fc63290bbfc319480bff10ca405ff0865202ffec129016ff609480bff304a401bf9825202ffac1290b6fd609480bfe304a401bf1825201ffea12900ffe5094807fea84a403ff1425216ffe81290b7fe409485bfea04a42dff1025216ffe61290b7fe309485bfe984a42dff0c25202ffe4129017fe209480bfe904a405ff0825216ffe21290b7f7109485bff084a42dff4425216fea21290b7fc109480b7fb2aa400ffd9152005fec8a9003fe645480
  | 8 => 0xf441531efea20a98f7fc1054c21ffb2e8600bfd97431e7fccba180efe65d0c01feb2e8600bf59743087f8cba180efc65d0c79ffaa68610ff95343007faa9a1843fc54d0c79ffa9e8600ff94f43007faa7a18f3fc53d0c21ffb168600ff98b4302dfcc5a1803fd62d0c017eb168610ff18b431e7fea5a18f3fc52d0c21ffb0e863bff98743015fcc3a1803fd61d0c017eb0e8610ff18743015f8c3a18f3ff51d0c77ff28e863bff147431dffc83a1843fc41d0c77ff18e863bff0c7431dffc43a18effc21d0c21ffb068635bfd83431affcc1a1806fe60d0c6bfeb068635bf58343087f8c1a1806fc60d0c6bffa868635ff943431affaa1a18d7fc50d0c21ffa068635efd03431affc81a18d7fd40d0c6bdea068610ff103431affe61a18d7fe30d0c6bfe9868635ff0c3431affe41a18d7fe20d0c6bfe9068635ff083431affe21a18d7f710d0c6bff0868635ff443431afea21a18d7fc10d0c01ffb2c8600bfd96431d7fccb2180efe6590c01feb2c8600bf596431d7f8cb2180efc6590c6d7eb24863affd52431d77ea921803fe5490c01feaa4863aff152431d778a9218c6fe6390c75ffa9c8600ff94e43007faa7218ebfc5390c01ffa1c8600efd0e43007be8721803ff6290c01ff3148605bf98a43007fac521802fd6290c01fe314863affd4a431d7f8a521803ff6190c73ff30c8602bf98643007fac321802fd6190c73fe30c8602bf186431d7fea3218e7fe5190c73fe28c8639ff906431cff883218e7fe3190c73fe18c8639ff886431cff843218d3ff6090c697fb048634ff9824300dfcc1218d3fd6090c697eb048634ff1824300df8c1218d3ff5090c69ff2848634ff542431a7f8a1218d3ff4090c69ff2048634ff502431a7f881218d3ff3090c69ff1848634ff4c2431a7f861218d3ff2090c69ff1048634ff482431a7f841218d3ff1090c69fb8848634ff842431a7fa21218d3f51090c69fe0848600ffd9543005fecaa18037f6550c013fb2a8638ff9954301dfccaa1803fd6550c017eb2a8638ff1954301df8caa18037c6550c073e32a8638ffd5143007fca8a1803fd5450c71fe2a28638ffd4d43007fca6a1803fd5350c71fe29a8600ffd0d43007be86a1803fe4350c01df21a8600ffd8943005fec4a1803fe6250c01feb128600ff1894302df8c4a18e3ff5250c71fe2928600ffd8543005fec2a18dffe6150c057f30a8600ff585431bff8c2a180afc6150c71ffa8a8637ff945431bff8a2a18dffe4150c6ffe20a8637ff8c5431bff862a18dffe2150c6ffe10a8636ffd81431b5fec0a18dbfe6050c037f3028636ff581431b5fac0a18dbfc6050c037e3028636ffd41431b7fca0a18dbfd5050c6dfe2828636ffd01431b77e80a18dbfe4050c6dfea028636ef501431b7f880a18dbff3050c6dff1828636ff4c1431b7f860
  | 9 => 0x7de2a2a800ffd8d54005fec6aa003fe6355001feb1aa800ff18d54005f8c6aa00fff5355007bfa9aa803ff14d54007fec4aa002ff6255001ff312a800ff58954007f8c4aa016fc6255007ffa92a803dfd495401ff8a4aa003ff61550017fb0aa842ff98554015fcc2aa003fd6155085fe30aa802bf1855401ffea2aa00ffe5155007fe28aa842ff90554217f882aa10bfe3155085fe18aa842ff88554217f842aa107ff60550837fb02a841ff9815400dfcc0aa107fd60550837eb02a841ff1815400df8c0aa00fff5055007ff282a803ff5415401ff8a0aa107ff4055083ff202a841ff5015420ff880aa107ff3055083ff182a841ff4c15420ff860aa107ff2055083ff102a841ff4815420ff840aa107ff1055083fb882a841ff8415420ffa20aa107f51055083fe082a803bf59653007fec929803fe6494c017f324a600ff59253005fac929803fc6494c07ffaa4a603ff95253006fca92980ffd5494c07fe2a4a603df1525301dfcc72980fff5394c07bfa9ca603f7d4e5301ebea72980ffc5394c07ee29ca600ffd8a53007fcc529816fe6294c01feb14a600bf58a53007f8c52980fff5294c07bfa94a603ff14a53007fec329903fe6194c057f30ca600ff58653005fac329903fc6194c057e30ca603ffd465301ffca32980ffc5194c81ff20ca640ff10653207fc6329903fc3194c81ff10ca640ff086531fffec1298feff6094c7fff304a601bf982531fffac1298fefd6094c7ffe304a601bf1825301ffea12980ffe5094c07fea84a603ff142531fffe81298fffe4094c7ffea04a63fff102531fffe61298fffe3094c7ffe984a63fff0c2531fffe41298fffe2094c7ffe904a63fff082531fffe21298fff71094c7fff084a63fff442531ffea21298fffc1094c077fb2aa600ffd9153005fec8a9803bf6454c015fb22a600ff99153007fac8a9803fc6454c017e322a600ef1915300578c8a980fff5454c07bfaa2a603ff9515301ffaa8a98037d5454c07fe2a2a603bfd8d5301ffea6a980fdf5354c07ff29aa600df94d5301ff8a6a980f7c5354c07ee29aa600ffd8953005fec4a9803fe6254c01feb12a600ff1895302df8c4a980fff5254c07bfa92a603ff14953007fec2a9802ff6154c7dff30aa602bf98553007fac2a98fbfc6154c057e30aa603ffd455301ffca2a98fb7e5154c07fe28aa603df145531f7fc82a98fbfc4154c7dff18aa63eff0c5531f7fc42a98fbfc2154c7bffb02a63dbfd81531effcc0a9806fe6054c7bfeb02a63dbf581531eff8c0a9806fc6054c07ffa82a603dfd415301ffca0a980ffd5054c7bbea82a603ff141531effe80a98f7fe4054c7bfea02a63dff101531effe60a98f7fe3054c7bfe982a63dff0c1531effe40a98f7fe2054c7bfe902a63dff081531effe20a98f7f71054c7bff082a63df
  | 10 => 0x12c00000803800004c00000800001800801800005000006c00c03400404401000001005806401403400800004400000000000000403400000004c00800c00400000405800001800407001403003805800801c01c00004402001000400000c00c00000001801400000c00800801400001800000401003c0100040200180180200000100300000000a801c00003000800002003c03006800004000000c02000401000401001800006400001c03c04000000803000001802004c03804804400000c00000c08000800000000000c00800c0000340140040040000140080000000040180000b40000180100080300a803000c02000800000000000000000002803c00400002006408400007002000400009c00400001002002000002000000007400803c00000002000400800401402800c00018c00000002001c01c04401000400800000800c0100100040ac0040600a800c00801400000004804c00400400001800000809000402c03c02400000401000803000403001000401402801c00008400c03400c0a401000800400400001c00401802401000c00000000402400403c00c00c10c00400402405c01000400000002c00406800402400001400000400001402804000400800402805000006c00400001800000800004000000400002000001001000000002800002401c00407400c01000400001c01c00404402800001c00400800000400001c0500180040080000000040280000040ac06400002800401c03800800001000802402800400c00002000000000400402c0e00040000200140140100080b001400000c01000000400401400007400001003800000c06c00800808400000000800001800000000807801001000000c008000060004000077eb2ca803bf9925401ffea92a00f7f5495007dfaa4a803cfd5254087f8a92a00fbc5495021ffb1ca800ff98e54005fcc72a003fd63950017eb1ca810ff18e5401ffea72a00ffc5395007be29ca810ffd8a54007fcc52a016fe6295001feb14a800bf58a54087f8c52a00fff5295007bfa94a803ff14a54087fec32a113fe61950057f30ca800ff58654005fac32a043fc61950057e30ca803ffd465401ffca32a1137e5195007fe28ca803df14654227fc832a043fc4195089ff18ca844ff0c654227fc432a113fc2195021ffb04a843bfd825421ffcc12a006fe6095087feb04a843bf58254087f8c12a006fc6095007ffa84a803dfd425401ffca12a00ffd5095087bea84a803ff14254087fe812a10ffe4095087fea04a810ff1025421ffe612a10ffe3095087fe984a843ff0c25421ffe412a10ffe2095087fe904a843ff0825421ffe212a10ff71095087ff084a843ff4425421fea212a10ffc10950077fb2aa803bfd915401ffea8aa00fbf5455007ff2a2a800df9515401ff8a8aa00f7c5455
  | 11 => 0x72900000000007930000000166000100800000049326e850458058e0c780a0b684482960ac91c634f3c1974cf9c8f72798fcc2a230c1098678dec0a60f100000064a206f9ac46f064f35e1f280005a61218f7467e000373027825e56e3ef11f41a20000001bfc5ca0bd2041b44e6e3c5221831888458b0259da8a1082500015786aa00000000000005f5000000000056b1cb8414ab200002e800046a3eb073215800070b0001dc4f1e15e15e99a001400035d0000fde0001f01990c0a48e40602b86986a13bb9c9800031f000214c4ec7472741688f3c6f23a91c0484870d0dc15a4a7459e16a0b690bc2cb06e0000d0a72e10d13d8bdc8632e4989816e30b146a2ec70e81000008c82f684f42f9a54ff03903c51f64b727dd07518300000002640cec00000000005080004c725523840fe5464558390f681344520744a025650522264a6a3a82e787ac8642b9000052858c00013193900000003a480009886922361f3cebc00037683bc0000000000f201b012036488182cc00000000008d4536000000000002900000002184ac36801343460a900018440007783e600006645c41be8000bd059a04198f000075d01f8c80f567a60000000000307169800000000026b8000aa230000004fc1f45d6356a00c9fc4a738a99a517873c1799c24f70072278a340000000000000000080b0001b0400061a25909b4a7a5d00a6800800000000802c02803c09400c01002003800400801c0040040040080301540000b000003003800000001c00001001001400800000001001402c00002402405c00400007401000000403000001800000804001c00c00402c00003001400000803000000001402000000800800000408000007c01c00400000402001801000400c00c01000000000c04800003801c00c00000c02c0000200140380240200000080000140b400001009c00002003402000001c00800c00c02803801803400c00000000000802803403402802006000c0040040a000801000400000400c00001400802400c06000000400405802800c0080000000000d80100000d403400001800402400800000401001001003802000c0000080000140140b003c00800000400800c01c01001802000400402400403400800802400401800c01c08000402000406002c00000001400c0000a80000540000000100000d800001403c00002c00805000800800000000400400000001800409c00800404801004c01803800800001403001004801c0780c001001004800401002000001402406001400805802800000000000400805400000001c00406001000800000001014800400c00408003c01000403800015c00003c0000000100cc08000c01c00c00003c01c00c0700b00140200100bc01c00000002006c00c03400800c00801c048004014000068000018000
  | 12 => 0xf028ce0a7af00002b09f40c131a8a9c36a3f8096160901c01a032a3086143470030e3c1e62eb00006bc0000000000114a1c13943b8b2843646d4598000c2665a00000000001700f99c48000000085800000055a029000105c6ca22f8af00002c52f3047c0000002bd9e387b60003d980000000000300c88fe41f13a41bc44de865088939cf2e0273a8a16000073f000218848a47e34c9f940001e300016740000002c9904800056306d8000660000000000000018d0000000000000340000000035e2a5000117c00000009fc000000000180400081300018b4bb400046680000000002631d28a784f00000c18bde3fc46701e04be7d310e1584a9800000000000000ba00020640d415418e80000000000000000c905ec3bc88080001b900011e46cc6dd3fc83b449c8ba14d900095619f0fb01f02d843b423027072a5053ef86c40000002e190940000001bc800000000000021e000086a17e890000000041115f4cda0003b080003be5390000d7c9ac00040f00000000002b79ab000033834d07a87623420001d3800059809f000000036032e953800000000001d40003ba000000094257a000000000035600019640004cc0059f041700000002360000000042000015a40e32b943c00083f37e95580002e11429b549aa4a30241f500007e832c0074ede367031a1708023e73a280000000001dd80000000002b9a1d445240b2e51efc20214f00000000000001fa8000000646000072000076200000000000710000cd4b668831d015dc63652121580001c60001b094bc85e1800001ee83ae716000000109082f20d8000cdc00031619e061e0b232591ac52e3d60c18000b420003cf8bd8e428d311e125850044c1f10da82522cc1a221c4a448af02b9adc50c11b11180dc1d62953668b7c4f43b7237208ccbc0f607c1cac1261db44e93dc39222a1e8987c75a1c224116c84740bc2029c0893c7ff0c9a31817647300015d43ca0aa3500878c9c6500000e8477c0000ec86f4d680f407f990d1a800047a1b387568201df80002c43924290000e7245c3391e4800053e39aa22c00000038a0f4808858d15f80000000002c4800087825b22900c80002ad2751bd44ac0de1a8a1688b42081470f28070531024869503057245187f851483b3bf0d2411c2653ed88480848ac3020dac10c37601307e433632a3ab120005a374281a2208604d80001b844d651b41881987b25d71179778ee40cc04c85bc2f86320ac87386fe4d0074981c32c76e24b82e46a420d2648e2cb5836e1d2895c2ae2dc0a7188118e48727f9fc42aa1ac150016c00000002a8cf8eb442d2049d1800e1fa3f094809ea1600001d7c1fa18a2339f9000042125aa1980001972b60000b983cb2f521906de0000c293ac6b65c734a0000a4e0000000520d204721958044e7425e00100f000
  | 13 => 0x56a0a99f6800000000007b051600015c132c00078900000000006d800000000007cb00000000008e200000000000000e7938cc626ec118009464200000009b001c1ed05f11280000002ae035c0007b934e0f9400075740915c10de2f403e9a8c74c5af02c80003048bd3d419d0bc04bf28b950023235d17e00008500001381aa8d0e7203b619940001bb000000000067547817e40000000c380000000000001c40d4c00000017548a862417a9f5909819200000000000000000000000000000094807a04e4008000000567000074c11800033fa24800000000016b4fcc5ae0000000d300a200000005c652e13413040006122a11d500000000000000ed055f00016fc0000003cd8000966000000082c0005a03df00000000e231d17f000067006498340007c025f040c3500003991c642748871e092a00003820001f485b685d000161800047a1eb8000cec4a003a11bc8ca47031798a10866b200022540003d3178000000045d00015fc00017a47c0000aaa2a800000000004bc06105b8d960000001d8c9a800024e95046860000f804546581c136f144c49a2e41f680500802aa3d2005ce3848946f8bb8ce666c43e1fc01f800043a13f044400000019080006250000fd85a20000000000a221043298e105d841524220145b245324a985c2264b807b8fa862a25c0c21c1c00071347309600000bf0a39b1c73a6af000000031c00000015980001fb20c87fc8e816400001f84a02923fe8cb4b544813619a3504e2811ac0000f0a1980ce12141283e62019e000002b41b80dd509641f0000bfc788331343118d09227c26f88909185522f91facdac7912e923ccdd0622157834c3865f40601d9c54854f15f0ba01ba3410bb00004920e81ec0000f8e4da11013a4dc650b2eea33c0002360ae8000c728d63441bd0c608060df833801010814407a08d00001c997a40080981349e046483b50b29ae41e412e0000ac095e4db11599ecee84f43f605d000060931700007aa246000056065c000000147c066000372103c41822d0679525050661352083c86861e35c00000000ec41d2310d8c1cc18706a4b8a383460097405e7881d1a1808280002dd8000b5046000000003942b70298000dd61e11fd9388eb62002958da01228ae3e2830c88860b14e16d81681361f90f349e45f73f99c301ac19d0a490740000000910a60c700003b58ddc10e01e047929800007b23a90604b403a39f09f4312015197a39c0001310a002342d2000000025cb9c00028d20000001fd0001930b6e4bb40886687326c211e961114e0001519b5c0c20003cea3a4e143030d504c8b248840ee0dc80006d30048da475c2481481d60032682000079c52272522381dc64a27500010d47108a84660c4ce5a7a2000000043049229d979c7682cf00014dcd4402400012c40000002d
  | 14 => 0x5c9e506ae52d1cb1fe800000023d80c0d362c13119850bda000000149800000010e80010584ec00000000006f7000095432a0004430000f340e002386e8c56000000000072217200005a80001d623887e10342841621510cb867a20e19f11d60002a98000c2a000000089cfaa44647600004f240c000000000036d00017444660000001228e964041b292180000000000718000000000000000039f0001b5000000000000ac00000021c800111a3a90000000000462000000000000038c000068a3bc0f219480003bd010987102c6e90ae10344827754410a585c04503378000a7e0010000b60b960004208000000610000000053c88f25493380000703c3000000077015880d8200000000180c82c782032228056a28935a9d407360000a18750d4e2d711d80009c000026e12700000d4213a0b4156000000167045c0000ed0000dca35300003405ba000000207c39a5e343e8eb093255b1dc21c05fc4b61a808440003460000e9081476400000000004c217d80009fa7a500022601fc00017c15c45a438a19b1ef0cbe799000000113c0003070620e860000000f24a4863413500ec84428f245800036c0f9384010cc5412d0000160b8c7f439183ec23a8d53d90a94f5a73147a904114465b32215611ec6f84151e54b3209a2bf1eb8b7868a21d0b085cc24a18c1ea889c52a3bd0584d9e2941e00c58b0a12427696e03d25094289221070407310800076c3de2bc10b04727110708c4020c3622839aac00032309b8ad8f0e1331508254a681d80a30d282984cd1071fec0008b5000000000065109080008b60002709d98e6c8090250ea8d167b62ef92b85320a737506b42be4a506aa0989de2190db9f111608bf09322c413660808b0150fce31117888f8fdc5fe1599e110aa3ec18111d875e15a05293784841dd044824051869e2f28f30b9a2140bf0984dce43702097203180d228c9450e888401b188d0fc42040941eecb605a52f59a305ee71d4488c6861243f02e0e1888a51e3e1948cf380562c520c83421672a29c88fb83f13ec19dcf422311bd851111256d08e0f7c59c0002de80000008aa44804ac0000460e806440d84f91259590b2e0000000e9c0000000001c1000000045c10cc1e001f00021b000034e3e3000000000000000000ec5f01e304e00ce75904fa1400000003a0a3c400000d000165400000023f800000039800000007fc0c81e39a950fc08b19a00010f65ba2fb0b2422083d342169080c6fc01f0000b3627441a1d3c0d081b1310688000796246800100430540504d400021743b18182ee44d43392c087a6601029a7c0984232be000000004f47781790a8836269979036846922b000098a6913940d7063c2c81c705f46f80002ec8d34000000398000000073d4691ff902a00000021a00000000001644c5206f00019500
  | 15 => 0x43e5db2d582805566e02100f8c48e3732a19aa43cc8c335f10b91ba2730d99da421e4383d800d40002ef0a582142ac42909516d45ce1140df186042c1454120b58a243b32850f0ceaa64a000201c79e0000000a08e3472c22f133cd8022532a96043781302d49dcc0000001d9041c1880001c697700000000000000000163319800000026633580003884b41c290a800000017d0a4c97a0b00001344c7e000000000055825100000000000003cc014515a5fd000113ce3600001700000003e9000236841287f2ae9ce0f7a8e80d3130c62e2544198089164312016008ca6407933f048c00058c2b10be4eca0000c08e000000000000ce40541f701a0000a4a5293a119140003e439990c50785f33920bb4a0856000022d823c6c82cb161c32854b1b6203c3200002830000f623d40f008dc00048f20f23790f2175288044866e84a452800000000000000002d06c400c1ea402435a25d1cd000000028e11dcd6063d369000106a00027716205e440245315e51ae7b70408000ef60002800d0000051533e80c49220001080cf00006b600000010528db00019351c026744d0258b001173419fb4e3c3271a4049c61a12544b8ca079c2ba39d8fbc53a78b42ba0dc88072a3448c647c261d30507f04b26932c7953434e20a44723e40d238127291240be8c1036947518a80d1840ce8a502ea06c9bb82fe69d1438fe48c20002f89dd87f47c22869a382340ca3628664f1a00018a1a0418a1732aa12906e222c46404289205a34181f34000000000000035c00019e872ce5e00045b9c0040e4173eb97e0de02644721a3d0d23a2436843854c1781ee024816247c0001f206a839a37d839c86c760009800016c8b42bb11040000001998ca40007c921f062c9725470d5869000a72716a89c86b24f801ca230db27533c6199d1942cd4752370f4084d2e08910b3e1861bf1c0c42a88a4238aece1c8811fe8e3060838934b198813a3f733881e83644e61370000b4e8a93779fd513e00009e03b84c045503114cc1b40002ea0000aa01f436d90440008800000b1c0000003ae000000000000003951a20000b594091927fc1018000e8006e008198cfa0000000000000000043d0000ae81a032480011267f62ca07c91ca08200000006f44260fa8ba40000200d8205000000000000007e801b0001430000000000000000027e08680000007ac4220000c8e00031b04250dc39c0358c047b40a82691460038458404232d0b249811080305342783351900d5c70f3f18ee4bb00002e100000001c000008fc7a000035e88a00000b541c9aec7286df3be1520d7e000000000038e0003540ffc2a01de42d932827a24f000032cf4e84e43594e00003b024d82280003e83f50d9113800030c800063800044d8000000000000000000000000000000000000001be84ee0004
  | 16 => 0x28b05b400048330b0000e9a00f050a3b43a40002c81c7c00000008c00000008a100020f80005c03b6a1088ae0003f4831c0001d53331be400034b02807b84e200000021c88f05b136d05c4bf600011c00000006b309d9e8c2a4000000205c00000000000005a077d0000000f6a89400018dc0000160001dfc0004fb32b0a7c15e2a900000000006020001c1800082107a800055c00000019e4db800024d104c0002532f0919800060f26c8b790c20001419b8873c5e20000b0c5c446422c92510380cd1f720ac1100732fd0fc0aae0000ad8000c8262711312b4e2e4c008101682f24510001bf849844b078a0100001c534b92dc0000000f78200ad08ee0001f811b200000000000006000000c98bfe00031d927d12c81d000000000000031f1bccc36000000160d10a27b2980f088348730001b30e98000422a3c8f207d11511fdc
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7258d21006ef7258d210c4ff7158d21006f77158d21004ff7058d2100cfe7058d21004fd7058d2100cfc7058d210c6f71058d21006f51058d210dcfe7618d21006dd6318d2101cfe7518d21004fd7518d2101cfc7518d21084fe7418d21004fd7418d21006de7318d2102cfe7218d2102cfc7218d2102cff7118d21014fe7118d2102cfd7118d21014fc7118d210a6df3118d210a6dd3118d21004ff7018d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d21006dc3018d210a6f71018d21006f51018d21004ff7694d21004fe7694d21004fd7694d21004fc7694d210375f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d2101e7c6554d21005bf7454d21005bc7454d21084ff76d0d21004fe76d0d21004fd76d0d21084fc76d0d21006bf64d0d21086bc64d0d21004ff7690d21004fe7690d21004fd7690d21004fc7690d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210357c7550d21006bf6450d21006bc6450d21084ff7610d21004fe7610d21004fd7610d21084fc7610d210357e7510d210057d7510d2102dee7210d21005ed7210d21015f67110d21005f57110d2101e7f76d49211867e76d49210367d76d492101e7c76d49210067f64d49210067e64d49210067d64d49210067c64d49210067f63d49210067e63d49210067d63d49210067c63d492102d7d72d492102e7f62d49211877671d49210377571d492102e7f61d492102f7721d49211876e21d492102f6c21d492102f7421d49212367f60d492117e7e60d49212367d60d492117e7c60d49211877710d49212377510d492101cff7654921014fe7654921164fd7654921014fc76549210067f655492101e7c6554921005f77154921015f4715492101e7f76549211667e76549211667d765492101e7c76549210067f64549210067e64549210067d64549210067c64549210067f63549210067e63549210067d63549210067c635492102d7f72549210376f725492102e7f625492102f6e425492102f6e325492100777715492116774715492102e7f615492102f7721549211676e215492102f6c215492102f74215492122e7f605492115e7e605492122e7d605492115e7c605492116777105492122f751054921014fe76d0921014fc76d0921006bf64d0921086bc64d0921015f671d0921005f571d0921084ff7650921014fe7650921124fd7650921014fc7650921006bf6450921006bc64509210076d5250921005f77150921015f47150921014fe76cc921014fc76cc921006df63cc921006dc63cc921015f671cc921005f571cc9210ecff764c921014fe764c9210c4fd764c921014fc764c921006df634c921006dc634c9210076d524c921005f7714c921015f4714c92102fe4214c921
  | 1 => 0x9521006bf7459521004bf7459521084fc7459521006bc7459521004bc7459521004ff7359521004fc7359521184ff7259521006ef7259521164ff7159521006f771595211667e51595211667c5159521004ff705952100cfe7059521004fd705952100cfc7059521166f71059521006f5105952101cfe75d9121004fd75d912101cfc75d9121006bf54d9121006bc54d9121004fe73d9121004fd73d912102cff71d912102cfd71d912113ebf41d912113ebd41d9121004ff70d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d912113ef710d9121006f510d9121006bf6499121125ed729912101cfe7599121004fd7599121084fc7599121084fe7499121004fe7399121004fd7399121124fd7299121086ed729912114cfd7199121086f57199121084ff709912100cfe7099121004fd709912100cfc709912114ef71099121006f510991210057f75591210357c755912114def7259121004ff75591210067f75591210047f755912101cfe755912101cfc75591210067c755912101c7c7559121006bf7459121004ff7359121004fc735912114cff7259121006ef7259121124ff7159121006f77159121004ff705912100cfe7059121004fd705912100cfc7059121126f71059121006f5105912113cfe7619121006bd641912101cfe7519121004fd7519121084fc7519121086be7419121006bf5419121086bc5419121004fe7319121004fd731912102cfe721912102cfc721912102cff7119121014fe711912102cfd7119121014fc7119121086bf4119121106bd4119121084ff701912100cfe7019121004fd701912100cfc7019121006be4019121086bc4019121106f71019121006f51019121084ff7695121004fe7695121004fd7695121084fc76951210067f659512101e7c65951210373f5495121004ff7655121004fe7655121004fd7655121004fc765512101cfe75d8d21004fd75d8d2101cfc75d8d21084fe74d8d21004fd74d8d2102cff71d8d2102cfd71d8d210dedf31d8d210dedd31d8d21004ff70d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d210def710d8d21006f510d8d210357e7598d210057d7598d21005be7498d21005bd7498d21006df6398d210c5ed7298d2101cfe7598d210067e7598d2101c7e7598d21004fd7598d210067d7598d210047d7598d2101cfc7598d21084fe7498d21006be7498d21004be7498d21004fd7498d21006bd7498d21004bd7498d210a4fe7398d210c4fd7298d21006ed7298d210ecfd7198d21006f57198d21004ff7098d2100cfe7098d21004fd7098d2100cfc7098d210eef71098d21006f51098d210edef7258d21004ff7558d2101cfe7558d2101cfc7558d21004ff7458d21084fc7458d21006df7358d210ecf
  | 2 => 0x4ff7359321004fc735932102cff7259321014fe725932102cfd7259321014fc725932102e7f525932102e7d525932102ebe425932102ebc4259321126bf4159321126bd4159321004ff705932100cfe7059321004fd705932100cfc7059321006bf4059321006bd4059321126f71059321006f51059321084ff769532102cfe7695321004fd769532102cfc769532101e7e65953210067d65953210473f5495321004ff765532102cfe7655321004fd765532102cfc765532101e7e65553210067d6555321005f77155321015f4715532101cfe7598f21004fd7598f2101cfc7598f21084fe7498f21004fd7498f2102ede7398f21014fe7298f21014fc7298f2102e7f5298f2102e7d5298f2102ede3298f2102edc3298f210eedf3198f210eedd3198f21004ff7098f2100cfe7098f21004fd7098f2100cfc7098f21006df3098f21006dd3098f210eef71098f21006f51098f21004ff7558f2101cfe7558f2101cfc7558f21004ff7458f21084fc7458f2102edf7358f2102cff7258f21014fe7258f2102cfd7258f21014fc7258f2102e7f5258f2102e7d5258f2102ede3258f2102edc3258f210c6df3158f210c6dd3158f21004ff7058f2100cfe7058f21004fd7058f2100cfc7058f21006df3058f21006dd3058f210c6f71058f21006f51058f21004ff7694f2102cfe7694f21004fd7694f2102cfc7694f2101e7e6594f210067d6594f210475f5394f21004ff7654f2102cfe7654f21004fd7654f2102cfc7654f2101e7e6554f210067d6554f21005bf7454f21005bc7454f21005f77154f21015f47154f21084ff76d0f2102cfe76d0f21004fd76d0f2102cfc76d0f211e67e65d0f210067d65d0f21006de63d0f21006dd63d0f21004ff7690f2102cfe7690f21004fd7690f2102cfc7690f211d67e6590f210067d6590f21006be6490f21006bd6490f21004ff7650f2102cfe7650f21004fd7650f2102cfc7650f210057f7550f210457c7550f211c67e6550f210067d6550f21005f77150f21015f47150f21084ff7610f2102cfe7610f21004fd7610f2102cfc7610f210457e7510f210057d7510f2119e7e6510f210067d6510f21086be6410f21006bd6410f21006de6310f21006dd6310f2102dee7210f21005ed7210f2101cfe76d95210367e65d9521084fe74d9521004fd74d95210367c54d9521004fe73d9521004fd73d95210367f53d952102cfe72d9521014fd72d952102cfc72d95210367f52d952102cff71d9521014fe71d952102cfd71d9521014fc71d95211767f51d95211767d51d9521004ff70d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210367c50d9521176f710d9521006f510d95210367c6559521005bf7459521005bc7459521185ef7259521174ff75595210067f7559521004ff745
  | 3 => 0xd758c931005be748c931005bd748c9310c5dd738c931006ef628c93102eec628c931015f6718c931005f5718c931014fc764c931006ef624c93102eec624c931005f7714c931015f4714c931015dc764c93102edc764c931014dc764c931006de644c931006dc644c931007cf724c931007cf624c93102ede624c93102edc624c931007cc624c93102ecc624c9310075f524c9310075d524c931007d7714c931015de714c931015dc714c9310c7d4714c9310c6df614c93124edf604c93124edd604c93124fcf204c93124fcd204c9310c7d7104c93124fd5104c9310ecfe760c9310557e750c9310057d750c9310edde730c931015f676cc531016f676cc53100cf676cc5310077675cc5310077575cc531015f673cc531017d673cc531016f763cc531017d763cc5310077752cc5310077552cc531007d732cc531007d532cc531245f770cc531245f570cc53123ef760cc53123ef560cc53102e7f7559721004ff7459721084fc74597210467f54597210467c5459721004ff7359721004fc73597210467f53597210467c535972102cff7259721014fe725972102cfd7259721014fc725972102e7e525972102e7c52597211667f51597211667d5159721004ff705972100cfe7059721004fd705972100cfc70597210467f50597210067e50597210067d50597210467c5059721166f71059721006f510597210067f74597210067e74597210067d74597210067c74597210067f73597210067e73597210067d73597210067c735972102e7f725972102c7f725972102e7e725972102e7d725972102c7d725972102e7c725972102e7f425972102e7e425972102e7d425972102e7c425972102e7f325972102e7e325972102e7d325972102e7c32597211667f71597211667e71597211667d71597211667c71597211667f41597211667e41597211667d41597211667c41597211667f31597211667e31597211667d31597211667c315972102e7f215972102e7e215972102e7d215972102e7c21597210067f70597210067e70597210067d70597210067c70597210067f40597210067e40597210067d40597210067c40597210067f30597210067e30597210067d30597210067c305972102e7f205972102e7e205972102e7d205972102e7c20597211667f10597211667710597211667e10597211667d10597210067510597211667c105972101cfe7599321004fd7599321084fc759932102ebe7499321004fe7399321004fd7399321014fe7299321014fc729932102e7f529932102e7d529932102ebe429932102ebc4299321086bf419932114ebd4199321084ff709932100cfe7099321004fd709932100cfc7099321086bf4099321006bd409932114ef71099321006f51099321004ff755932101cfe755932101cfc755932102ebf7459321
  | 4 => 0x51310067f659513101e7c65951310573f5495131004ff7655131004fe7655131004fd7655131004fc765513126cfe7694d310575f5394d31207d43194d3101cff7654d31014fe7654d311f4fd7654d31014fc7654d310067f6554d3101e7c6554d31005bf7454d31005bc7454d31005f77154d31015f47154d311f7d43154d31014fe76d0d31014fc76d0d31006bf64d0d31086bc64d0d31015f671d0d31005f571d0d31194fe7690d31084ff7650d31014fe7650d311bcfd7650d31014fc7650d310057f7550d310557c7550d31006bf6450d31006bc6450d31005f77150d31015f47150d311ccfe7610d310557e7510d310057d7510d3102cfe76d893101cfe75d8931004fd75d893101cfc75d8931084fe74d8931004fd74d8931014fe71d8931014fc71d89310eeef21d8931004ff70d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d89310eef710d8931006f510d89310557e75989310057d7598931005be7498931005bd7498931006ef62989310557e75189310057d751893102eee6218931006ed621893101e7f76d49310567e76d49310567d76d493101e7c76d49310067f64d49310067e64d49310067d64d49310067c64d49311867f63d49310067f62d493102e7e62d493102e7c62d49311867f61d49311875e31d49311875c31d49311877431d49312667f60d493117e7e60d49312667d60d493117e7c60d49311877710d49312677510d4931004fe7694931004fd769493102cfc76949311657d7594931005de7394931005dd7394931004ff7654931004fe7654931004fc76549310067f655493101e7e65549310067d655493101e7c65549310067f76549310067e76549310067d76549310067c76549310067f64549310067e64549310067d64549310067c64549311667f63549311857f72549310576f72549310067f625493102e7e625493102e7c62549311667f61549311675e31549311675c315493116774315493125e7f605493115e7e605493125e7d605493115e7c605493116777105493125f751054931004fe76d0931004fd76d0931084fc76d0931006bf64d0931086bc64d0931004fe7690931004fd769093102cfc76909310557e75909310057d7590931005de7390931005dd7390931004ff7650931004fe7650931004fc7650931006bf6450931006bc6450931004fe7610931004fd761093102cfc76109310557e75109310057d7510931005de7310931005dd7310931015f67110931005f571109310a4fe76cc9310a5de76cc931006de76cc931006de64cc931006dc64cc93102ede62cc93102edc62cc9310075f52cc9310075d52cc931015de71cc931015dc71cc9310eedf61cc931256df60cc931256dd60cc9310efd710cc931257d510cc931014fe768c9310557e758c9310057
  | 5 => 0x5bd748cb310dcff764cb310ce7e654cb310067d654cb310dddf764cb31006df764cb310075e654cb310075d654cb31006de644cb31006dc644cb31007cf724cb3102ede624cb3102edc624cb310075f524cb310075d524cb31015de714cb31015dc714cb3127edf604cb3127edd604cb3127fcf204cb3127fcd204cb310c7d7104cb3127fd5104cb31014fd760cb310657e750cb310057d750cb310ae7e650cb310067d650cb3102eee620cb31006ed620cb31015f6710cb31005f5710cb3101cfe76d95310567e65d9531084fe74d9531004fd74d95310567c54d953101cfe73d9531014fd73d953101cfc73d95310567f53d953102cfe72d9531004fd72d95310567f52d9531204ff71d9531204fd71d95312067f51d95312067d51d9531004ff70d953100cfe70d9531004fd70d953100cfc70d95310067e50d95310567c50d9531206f710d9531006f510d95310567c6559531005bf7459531005bc7459531275df7359531204ff75595310067f7559531004ff7459531006bf7459531004bf7459531084fc7459531006bc7459531004bc7459531274ff7359531006df7359531004ff725953102cfc72595310567f52595311f4ff7159531006f771595311f67e51595311f67c5159531004ff705953100cfe7059531004fd705953100cfc70595311f6f71059531006f5105953101cfe75d9131004fd75d913101cfc75d9131006bf54d9131006bc54d913102cfe72d9131004fd72d91311ccff71d91311ccfd71d91311cebf41d91311cebd41d9131004ff70d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d91311cef710d9131006f510d9131006bf64991311bddd739913101cfe7599131004fd7599131084fc7599131084fe74991311bcfd7399131086dd739913102cfe7299131004fd72991311dcfd7199131086f57199131084ff709913100cfe7099131004fd709913100cfc70991311def71099131006f510991310057f75591310557c75591311dddf7359131004ff75591310067f75591310047f755913101cfe755913101cfc75591310067c755913101c7c7559131006bf74591311dcff7359131006df7359131004ff725913102cfc72591311bcff7159131006f77159131004ff705913100cfe7059131004fd705913100cfc70591311bef71059131006f510591311ccfe7619131006bd641913101cfe7519131004fd7519131084fc7519131086be7419131006bf5419131086bc54191311a4fe7319131084fc731913102cfe7219131004fd7219131084ff7119131194fd7119131086bf4119131196bd4119131084ff701913100cfe7019131004fd701913100cfc7019131006be4019131086bc4019131196f71019131006f51019131084ff7695131004fe7695131004fd7695131084fc769
  | 6 => 0xf6298b3102cff7658b310067e6558b310067d6558b31004ff7558b3101cfe7558b310067e7558b310067d7558b3101cfc7558b31004ff7458b31084fc7458b310c6ef2158b31004ff7058b3100cfe7058b31004fd7058b3100cfc7058b31006ef2058b31006ed2058b310c6f71058b31006f51058b310657e7518b310057d7518b310067e6518b310067d6518b3102eee6218b31006ed6218b310657f76d4b3101e7f76d4b3101c7f76d4b310667e76d4b310057d76d4b310667d76d4b310047d76d4b3101e7c76d4b310067f64d4b310067e64d4b310067d64d4b310067c64d4b311867e63d4b3102e7e62d4b310067d62d4b3102e7c62d4b311875e31d4b311877631d4b311875c31d4b312967f60d4b3117e7e60d4b312967d60d4b3117e7c60d4b311877710d4b312977510d4b3102cff7694b31004fe7694b31004fd7694b3101e7e6594b310067d6594b31005de7394b31005dd7394b31004ff7654b31004fd7654b31004fc7654b310067f6554b3101e7e6554b310067d6554b3101e7c6554b31005f77154b31015f47154b310057f7654b310067f7654b310047f7654b310067e7654b310057d7654b310067d7654b310047d7654b310067c7654b310067f6454b310067e6454b310067d6454b310067c6454b311667e6354b310676f7254b3102e7e6254b310067d6254b3102e7c6254b31007777154b31167747154b311675e3154b31167763154b311675c3154b3128e7f6054b3115e7e6054b3128e7d6054b3115e7c6054b31167771054b3128f751054b31084ff76d0b31004fe76d0b31004fd76d0b311567e65d0b310067d65d0b31006bf64d0b31086bc64d0b3102eee62d0b31006ed62d0b3102cff7690b31004fe7690b31004fd7690b310657e7590b310057d7590b311467e6590b310067d6590b31006be6490b31006bd6490b31005de7390b31005dd7390b31004ff7650b31004fd7650b31004fc7650b3112e7e6550b310067d6550b31006bf6450b31006bc6450b31005f77150b31015f47150b3102cff7610b31004fe7610b31004fd7610b310657e7510b310057d7510b3110e7e6510b310067d6510b31086be6410b31006bd6410b31005de7310b31005dd7310b3102eee6210b31006ed6210b31014fd76ccb310f67e65ccb310067d65ccb3102eee62ccb31006ed62ccb31015f671ccb31005f571ccb31015dd76ccb3102edd76ccb31014dd76ccb310075e65ccb310075d65ccb31006de64ccb31006dc64ccb3102ede62ccb31007ce62ccb31007cd62ccb3102edc62ccb310075f52ccb310075d52ccb31015de71ccb310efd671ccb31007d571ccb31015dc71ccb31286df60ccb31286dd60ccb310efd710ccb31287d510ccb310c4fd768cb310657e758cb310057d758cb310e67e658cb310067d658cb31005be748cb31
  | 7 => 0x97310067f20597310067e20597310067d20597310067c20597311f67f10597311f67710597311f67e10597311f67d10597310067510597311f67c10597310657e75d93310057d75d93310067e65d93310067d65d9331195de73d9331005ee72d9331005ed72d933101cfe75d93310067e75d933101c7e75d9331004fd75d93310067d75d93310047d75d933101cfc75d9331194fe73d9331006de73d933102cfe72d9331006ee72d933102cee72d9331004fd72d9331006ed72d9331004ed72d9331006f571d9331004ff70d933100cfe70d9331004fd70d933100cfc70d93311cef710d9331006f510d93311bcfd76993310067e65993310067d6599331006bf649933101cfe7599331004fd7599331084fc759933102cfe7299331004fd7299331086bf41993311debd4199331084ff709933100cfe7099331004fd709933100cfc7099331086bf4099331006bd40993311def71099331006f510993310067e65593310067d6559331004ff755933101cfe755933101cfc7559331006bf7459331084ff73593311b4fd7359331004ff725933102cfc72593311bebf41593311bebd4159331004ff705933100cfe7059331004fd705933100cfc7059331006bf4059331006bd40593311bef71059331006f510593310657e75193310057d75193310067e65193310067d6519331006bd64193311cdde731933101cfe75193310867e751933101c7e7519331004fd75193310867d75193310047d7519331084fc7519331084fe7419331086be74193311ccfe7319331086de731933102cfe7219331004fd7219331086f57119331084ff701933100cfe7019331004fd701933100cfc7019331196f71019331006f51019331084ff7695331004fe7695331004fd7695331084fc769533101e7e65953310067d65953310673f5495331004ff7655331004fe7655331004fd7655331004fc765533101e7e65553310067d6555331014ff7694f3101cfe7694f31014fd7694f3101e7e6594f310067d6594f310675f5394f31015f67194f31005f57194f31207d63194f31274ff7654f3101e7e6554f311f67d6554f31005bf7454f31005bc7454f311f7d63154f311bcfd76d0f311e67e65d0f310067d65d0f31014ff7690f31014fd7690f311d67e6590f310067d6590f31006be6490f31006bd6490f31015f67190f31005f57190f311dcff7650f310057f7550f310657c7550f311c67e6550f310067d6550f31014ff7610f31014fd7610f310657e7510f310057d7510f3119e7e6510f310067d6510f31086be6410f31006bd6410f31015f67110f31005f57110f310657e75d8b310057d75d8b310067e65d8b310067d65d8b31005be74d8b31005bd74d8b310657e7598b310057d7598b310067e6598b310067d6598b31005be7498b31005bd7498b31006e
  | 8 => 0x14cfe76109410757e75109410057d75109410067f651094110e7c651094114dbe7410941087b44110941004fe76cc941004fd76cc941004fc76cc9410067f65cc9410f67c65cc941006df63cc941006dc63cc941004fe768c941004fd768c94102cfc768c9410757e758c9410057d758c9410067f658c9410e67c658c941005be748c941005bd748c941006ef628c94102eec628c941004ff764c941004fe764c941004fc764c9410067f654c9410ce7c654c941006df634c941006dc634c941006ef624c94102eec624c941004fe760c941004fd760c94102cfc760c9410757e750c9410057d750c9410067f650c9410ae7c650c941005be740c941005bd740c941015f6710c941005f5710c941015f676d0541016f676d05410077765d05410077465d0541015f674d0541017b674d0541016f764d0541017b764d05410077752d05410077552d0541087b742d0541007b542d0541085f770d05412a5f570d054129ef760d054129ef560d05410667e65d973126dde73d97311f4fd75d9731084fe74d9731004fd74d973126cfe73d9731006de73d973102cfe72d9731004fd72d97310667f52d9731006f571d9731004ff70d973100cfe70d9731004fd70d973100cfc70d9731206f710d9731006f510d97311f47d76997312767e63997310057d72997312767d61997312775e31997312777631997312775c31997310067f60997310067e60997310067d60997310067c609973127777109973100775109973101cff76597310667c65597310067f7559731004ff7459731084fc74597310667f54597310667c545973101cff735973101cfd7359731014fc73597310667c5359731004ff725973102cfc72597310667f52597310667c52597311f67f51597311f67d5159731004ff705973100cfe7059731004fd705973100cfc70597310667f50597310067e50597310067d50597310667c50597311f6f71059731006f510597312757f76597310667f765973101c7f76597310057f72597311f75e31597311f77631597311f75c31597310067f60597310067e60597310067d60597310067c60597311f77710597310077510597310067f74597310067e74597310067d74597310067c74597310667f73597311f67e73597311f67c73597310067f72597310047f72597310067e72597310067d72597310067c72597311f67f71597311f67e71597311f67d71597311f67c71597311f67f41597311f67e41597311f67d41597311f67c41597311f67f31597311f67e31597311f67d31597311f67c31597311f67f21597311f67e21597311f67d21597311f67c21597310067f70597310067e70597310067d70597310067c70597310067f40597310067e40597310067d40597310067c40597310067f30597310067e30597310067d30597310067c305
  | 9 => 0x77150d41015f47150d411bfb44150d411dcfe7610d410757e7510d410057d7510d410067f6510d4119e7c6510d4102cfe76d89410067f65d89410067c65d89410067f75d894101cfe75d8941004fd75d894101cfc75d89410067c75d8941004fe73d8941004fd73d894114eef21d8941004ff70d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d894114ef710d8941006f510d89410757e75989410057d75989410067f65989410067c6598941005de7398941005dd7398941006ef62989410057f75589410757c75589410067f65589410067c65589410757e75189410057d75189410067f65189410067c651894102eee6218941006ed621894101e7f76d49410057e76d49410767e76d49410047e76d49410767d76d49410757c76d494101e7c76d494101c7c76d49411867f64d49410067f63d49410067c63d49410067f62d494102e7e62d494102e7c62d49411867f61d49411873e41d49411873c41d49411877441d49412c67f60d494117e7e60d49412c67d60d494117e7c60d49411877710d49412c77510d4941004fe7694941004fd769494102cfc76949411657d75949410067f659494101e7c6594941005be7494941005bd7494941004ff7654941004fe7654941004fc76549410067f655494101e7e65549410067d655494101e7c65549410067f76549410057e76549410067e76549410047e76549410067d76549410057c76549410067c76549410047c76549411667f64549410067f63549410067c63549411857f72549410776f72549410067f625494102e7e625494102e7c62549411667f61549411673e41549411673c41549411677441549412be7f605494115e7e60549412be7d605494115e7c60549411677710549412bf751054941104fe76d09410067f65d09411567c65d0941105be76d0941006be76d09410073f65d09410073c65d0941006bc63d094102ebe62d094102ebc62d09410073f52d09410073d52d0941015be71d0941015bc71d0941086bf61d09412b6bf60d09412b6bd60d094114fb710d09412b7b510d0941014fe76909410757e75909410057d75909410067f65909411467c6590941125bd7490941005de7390941005dd7390941006ef629094102eec6290941015f67190941005f5719094113fb44190941014fc76509410067f655094112e7c6550941006ef625094102eec6250941005f77150941015f47150941015bc765094102ebc7650941014bc76509410073f65509410073c6550941006bc6350941007af7250941007af625094102ebe625094102ebc6250941007ac62509410073f52509410073d5250941007b77150941015be7150941015bc7150941127b47150941015b47150941126bf61509412aebf60509412aebd6050941127b710509412afb51050941
  | 10 => 0x95410067f73d95410067e73d95410067d73d95410067c73d95410067f72d95410067e72d95410067d72d95410047d72d95410067c72d95412267f71d95412267e71d95412267d71d95412267c71d95412267f41d95412267e41d95412267c41d95412267f31d95412267e31d95412267d31d95412267c31d95412267f21d95412267e21d95412267d21d95412267c21d95410067f70d95410067e70d95410067d70d95410067c70d95410067f40d95410067e40d95410067d40d95410067c40d95410067f30d95410067e30d95410067d30d95410067c30d95410067f20d95410067e20d95410067d20d95410067c20d95412267f10d95412267710d95412267e10d95412267d10d95410067510d95412267c10d95410767c65595412d5bf7459541224ff75595410067f75595412d4ff7459541006bf7459541004ff7359541004fc7359541004ff725954102cfc72595410767f5259541214ff7159541006f77159541004ff705954100cfe7059541004fd705954100cfc7059541216f71059541006f510595412257e76195410767e76195412247e76195412ce7f64195410057d72195412ce7f61195412cf3e41195412cf3c41195412cf7441195410067f60195410067e60195410067d60195410067c60195412cf7710195410077510195412ccfe76951412267f659514101e7c65951410773f5495141087b4419514101cff7655141014fe7655141214fd7655141014fc76551410067f655514101e7c65551410773c5455141005f77155141015f47155141217b441551410067f65d8d410067c65d8d4101cfe75d8d41004fd75d8d4101cfc75d8d4102cfe72d8d41004fd72d8d411dedf31d8d41004ff70d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d411def710d8d41006f510d8d410757e7598d410057d7598d410067f6598d410067c6598d41006df6398d41005ee7298d41005ed7298d410057f7558d410757c7558d410067f6558d410067c6558d410067f6518d410067c6518d41006dd6318d4101cfe7518d41004fd7518d4101cfc7518d4102cfe7218d41004fd7218d41196dd3118d41004ff7018d4100cfe7018d41004fd7018d4100cfc7018d41006de3018d41006dc3018d41196f71018d41006f51018d41004fe7694d41004fd7694d41004fc7694d410067f6594d4101e7c6594d410775f5394d41004ff7654d41004fe7654d41004fc7654d410067f6554d4101e7c6554d41005bf7454d41005bc7454d41194fe76d0d410067f65d0d411e67c65d0d41087b441d0d41014fe7690d410067f6590d411d67c6590d41006df6390d41006dc6390d41015f67190d41005f57190d41014fc7650d410057f7550d410757c7550d410067f6550d411c67c6550d41006df6350d41006dc6350d41005f
  | 11 => 0x1cfc7558b41014fc7458b41004ff7358b41004fc7358b41086ef4258b41086ec4258b41126ef2158b41004ff7058b4100cfe7058b41004fd7058b4100cfc7058b41126f71058b41006f51058b4101e7f76d4b4108e7e76d4b4108e7d76d4b4101e7c76d4b411867e64d4b410067e63d4b410067d63d4b4102e7e62d4b410067d62d4b4102e7c62d4b411873e41d4b411877641d4b411873c41d4b412f67f60d4b4117e7e60d4b412f67d60d4b4117e7c60d4b411877710d4b412f77510d4b4102cff7694b41084fe7694b41004fd7694b41085be7494b41005bd7494b41004ff7654b41004fd7654b41084fc7654b410067f6554b4101e7e6554b410067d6554b4101e7c6554b41005f77154b41015f47154b410067f7654b410067e7654b410067d7654b410067c7654b411667e6454b410067e6354b410067d6354b4108f6f7254b4102e7e6254b410067d6254b4102e7c6254b41007777154b41167747154b411673e4154b41167764154b411673c4154b412ee7f6054b4115e7e6054b412ee7d6054b4115e7c6054b41167771054b412ef751054b41015bd76d0b4102ebd76d0b41014bd76d0b41006be63d0b4102ebe62d0b41087ae62d0b41087ad62d0b4102ebc62d0b410073f52d0b410073d52d0b41015be71d0b41087b671d0b41087b571d0b41015bc71d0b41086bf60d0b412e6bd60d0b4114fb710d0b412e7b510d0b41124fd7690b4108d7e7590b410057d7590b41005de7390b41005dd7390b4113cff7650b4113dbf7650b41006bf7650b41006be6350b41087af7250b4102ebe6250b4102ebc6250b410073f5250b410073d5250b41015be7150b41015bc7150b412debf6050b412debd6050b41127b71050b412dfb51050b41004ff76ccb41084fe76ccb41004fd76ccb4102cff768cb41084fe768cb41004fd768cb4108d7e758cb410057d758cb41085be748cb41005bd748cb41004ff764cb41004fd764cb41084fc764cb41005f7714cb41015f4714cb4102cff760cb41084fe760cb41004fd760cb4108d7e750cb410057d750cb41085be740cb41005bd740cb4101cfe76d95410767e65d9541084fe74d9541014fd74d9541084fc74d95410767f54d9541004fe73d9541004fd73d95410767f53d95410767c53d954102cfe72d9541004fd72d95410767f52d95410767c52d9541084ff71d9541224fd71d95412267f51d95412267d51d9541004ff70d954100cfe70d9541004fd70d954100cfc70d95410767f50d95410067e50d95410067d50d95410767c50d9541226f710d9541006f510d95412cd7e76d954101c7e76d95410057d72d95412273e41d95412273c41d95412277441d95410067f60d95410067e60d95410067d60d95410067c60d95412277710d95410077510d95412267f74d95410767e74d95412267d74d
  | 12 => 0xe6218951006ed62189510157c765495102e7c76549510147c76549510067f64549510067c64549510067f63549510067c635495101d7f725495101f6f72549510067f62549510076f62549510066f625495102e7e625495102e7c62549510076c62549510077771549510157e71549510157c715495116774715495101e7f615495101f7761549512fe7f605495115e7e60549512fe7d605495115e7c60549511677710549512ff751054951004fe76d0951004fd76d0951084fc76d0951004fe7690951004fd769095102cfc769095101d7e75909510057d7590951006bf6490951006bc6490951005de7390951005dd7390951004ff7650951004fe7650951004fc7650951004fe7610951004fd761095102cfc761095101d7e75109510057d7510951006bf6410951086bc6410951004fe76cc951004fd76cc951004fc76cc951004fe768c951004fd768c95102cfc768c95101d7e758c9510057d758c951005be748c951005bd748c951004ff764c951004fe764c951004fc764c951004fe760c951004fd760c95102cfc760c95101d7e750c9510057d750c951214fd75d9741084fe74d9741086be74d9741004fe73d9741004fd73d974102cfe72d9741004fd72d974108e7f52d9741086f571d97412267e51d97412267c51d9741084ff70d974100cfe70d9741004fd70d974100cfc70d9741226f710d9741006f510d974101cff76597410867c65597410867f755974101cff7459741014fe745974101cfd7459741014fc74597410867e54597410867c5459741004ff7359741004fc735974108e7f5359741004ff725974102cfc725974108e7f52597412167f51597412167d5159741004ff705974100cfe7059741004fd705974100cfc70597410067e505974108e7c5059741216f71059741006f510597412d4ff76553410873c5455341217b64155341086df6398f4101cfe7598f41004fd7598f4101cfc7598f41014fe7498f41086df4398f41086dc4398f4102cfe7298f41004fd7298f411cedd3198f41004ff7098f4100cfe7098f41004fd7098f4100cfc7098f411cef71098f41006f51098f41086dc6358f41004ff7558f4101cfe7558f4101cfc7558f41014fc7458f41086df4358f41086dc4358f41004ff7258f4102cfc7258f411bedf3158f41004ff7058f4100cfe7058f41004fd7058f4100cfc7058f411bef71058f41006f51058f41004ff7694f41084fe7694f41004fd7694f4108f5f5394f41004ff7654f41004fd7654f41084fc7654f4101e7e6554f410067d6554f41005bf7454f41085bc7454f411bcfd7690f411ccff7650f410057f7550f4108d7c7550f4108d7e7598b410057d7598b41005de7398b41005dd7398b41086ef6298b4102eec6298b4102cff7658b41086ec6258b41004ff7558b4101cfe7558b41
  | 13 => 0xc832006ef764c832004ef764c83202f6e654c83202f6d654c83202def734c83202fcf734c83233eee634c83202fce634c832007ce534c832007cd534c832007ce434c832007cd434c832337ce314c832337cc314c83202eef604c83232eed604c83232fcf304c83232fcd304c83232fe7104c83232fe5104c832004ff755843201cfe755843201cfc7558432004ff7458432084fc7458432014fd725843202e7f525843202e7d525843202edf325843202edd325843202ef771584320a6f641584320a6f4315843202ef7215843202ef42158432004ff705843200cfe7058432004fd705843200cfc70584320a6f71058432006f51058432014fd75d9151326be54d9151326bd54d9151004fe73d9151004fd73d915102cfe72d9151004fd72d91513267f52d915101cfd71d91512d6bf41d9151004ff70d915100cfe70d9151004fd70d915100cfc70d9151006bf40d9151006bd40d91512d6f710d9151006f510d9151006bf6499151075f5719915108df77159151006bd6419151014fd7519151086be541915131ebd5419151004fe7319151004fd731915102cfe7219151004fd721915131e7f5219151084ff711915101cfd71191512ce7e51191512ce7c5119151086bf41191512cebd4119151084ff701915100cfe7019151004fd701915100cfc7019151086bf4019151006bd40191512cef71019151006f51019151014fd75d8d51084fe74d8d51004fd74d8d51316de53d8d51316dd53d8d5102cfe72d8d51004fd72d8d513167f52d8d5101cfd71d8d512767e51d8d512767c51d8d51276df31d8d51004ff70d8d5100cfe70d8d51004fd70d8d5100cfc70d8d51276f710d8d51006f510d8d51006df6398d51055f57198d51005bf7458d51005bc7458d51065f77158d51006dd6318d51014fd7518d51084fe7418d51004fd7418d5130ede5318d5130edd5318d5102cfe7218d51004fd7218d5130e7f5218d5101cfd7118d5126edd3118d51004ff7018d5100cfe7018d51004fd7018d5100cfc7018d5126ef71018d51006f51018d51004fe76d0d51004fd76d0d51084fc76d0d51004fe7690d51004fd7690d51004fc7690d51006bf6490d51006bc6490d51004ff7650d51004fe7650d51004fc7650d510057f7550d5101d7c7550d51004fe7610d51004fd7610d51084fc7610d5101d7e7510d510057d7510d51006bf6410d51086bc6410d5102cfe76d89511867f75d8951014fd75d8951084fe74d8951004fd74d8951004fe73d8951004fd73d89511867f52d8951306ee52d8951306ed52d895101cfd71d89511867e51d89511867c51d8951186ef21d8951004ff70d895100cfe70d8951004fd70d895100cfc70d8951186f710d8951006f510d8951006ef6298951035f57198951005bf7458951005bc7458951045f7715895102ee
  | 14 => 0x4ff7159432014fe7159432014fc71594320ae7f51594320067e51594320ae7c5159432004ff705943200cfe7059432004fd705943200cfc70594320ae7f50594320067e50594320067d50594320ae7c5059432006f71059432006f510594320067f74594320067e74594320067d74594320067c74594320ae7f73594320067e73594320067c735943202e7f725943202e7e725943202e7d725943202e7c725943202e7f425943202e7e425943202e7d425943202e7c425943202e7f325943202e7e325943202e7d325943202e7c32594320067f71594320067e71594320067d71594320067c71594320067e41594320067c41594320067e31594320067c315943202e7f215943202e7e215943202e7d215943202e7c21594320067f70594320067e70594320067d70594320067c70594320067f40594320067e40594320067d40594320067c40594320067f30594320067e30594320067d30594320067c305943202e7f205943202e7e205943202e7d205943202e7c20594320067f10594320067710594320067e10594320067d10594320067510594320067c105943201cfe7599032004fd7599032084fc759903202ebe749903202cfe729903202cfc729903202e7f529903202e7d529903202ebe429903202ebc429903202edf329903202edd3299032014fe7199032004fd7199032014fc7199032084ff709903200cfe7099032004fd709903200cfc7099032086bf4099032006bd4099032006f71099032006f51099032004ff755903201cfe755903201cfc755903202ebf745903202cfe725903202cfc725903202e7f525903202e7d525903202ebe425903202ebc4259032004ff7159032014fe7159032014fc7159032004ff705903200cfe7059032004fd705903200cfc7059032006bf4059032006bd4059032006f71059032006f51059032084ff769503202cfe7695032004fd769503202cfc769503201e7e65950320067d65950320af3f5495032004ff765503202cfe7655032004fd765503202cfc765503201e7e65550320067d65550320f4ff7694c3202cfe7694c3201cfd7694c3202cfc7694c3201e7e6594c320067d6594c320af5f5394c3202dee7294c32005ed7294c320f4ff7654c3201e7e6554c320067d6554c32005bf7454c32005bc7454c32004fd76d0c321e67e65d0c320067d65d0c3234ede63d0c32004ff7690c32004fd7690c321d67e6590c320067d6590c32006be6490c32006bd6490c3202dee7290c32005ed7290c32004ff7650c320057f7550c320ad7c7550c321c67e6550c320067d6550c32084ff7610c3202cfe7610c32004fd7610c3202cfc7610c320ad7e7510c320057d7510c3219e7e6510c320067d6510c32086be6410c32006bd6410c32346de6310c3202dee7210c32005ed7210c3202def764
  | 15 => 0xe7610d320cd7e7510d320057d7510d32086be6410d32006bd6410d320079d4310d32005de7610d32006de7610d320075e7510d320075d7510d32385de7410d320079e7410d32006df6410d320079e6410d32006dd6410d320079d6410d3237f9f5410d3237f9c5410d3202dde7210d3202ddc7210d32005dd7110d32375df7010d32375dd7010d3236fcf2010d3236fcd2010d3236fd71010d3236fd51010d3201e7f76d49320ce7e76d49320ce7d76d493201e7c76d49320067f64d49320067e64d49320067d64d49320067c64d49320cf5e73d49320cf5d73d493202e7f63d49320075f43d49320075c43d493202d7d72d493202e7f62d493202f5e32d493202f5c32d493202f6c32d49321867e61d49321867c61d49323667f60d493217e7e60d49323667d60d493217e7c60d49323675f30d49323675d30d493202f6f20d49323676d20d49323677710d49323677510d493201cff76549320ccfd765493201cfc76549320067f655493201e7c6554932005df7354932005dc735493202fcc325493201e7f76549320067e76549320067d765493201e7c76549320067f64549320067e64549320067d64549320067c64549320075f73549320075c735493202e7f63549320075f43549320075c435493202d7f72549320cf6f725493202e7f625493202f6c425493202f5e325493202f5c325493202f6c325493202f4c32549321667e61549321667c615493202f6f215493235e7f605493215e7e605493235e7d605493215e7c605493235f5f305493235f5d305493202f6f205493235f6d205493235f77105493235f751054932004fe76d0932006bf64d0932086bc64d0932005de73d0932005dd73d09320079c43d09320076d52d0932084ff7650932004fd7650932004fc7650932006bf6450932006bc6450932005df7350932005dc73509320079c435093202fac425093202fcc325093202dde73cc93202edf63cc9320076f52cc9320076d52cc93202dee73cc93202eef63cc93202fcf63cc932007cf43cc932007cc43cc93233def70cc93233ded70cc932357cf30cc932357cd30cc932357e710cc932357e510cc932014fe76d85320cd7e75d85320057d75d85320c6f661d853201cfe75d85320067e75d853201c7e75d8532004fd75d85320067d75d85320047d75d853201cfc75d8532084fe74d8532004fd74d853202cfd73d8532014fc72d85320067f52d85320067d52d8532006f751d85320c6f451d85320c6f441d85320c6f631d85320c6f621d8532004ff70d853200cfe70d8532004fd70d853200cfc70d85320c6f710d8532006f510d85320c6f4615853202e7f7559432004ff7459432084fc74594320ae7f54594320ae7c54594320acfc73594320ae7c535943202cfe725943202cfc725943202e7e525943202e7c5259432
  | 16 => 0x9532004ff7059532006fb7059532004fb705953200cfe7059532004fd705953200cfc7059532006f8705953200cf870595320ce7f50595320067d5059532006f71059532006f5105953201cfe75d9132004fd75d913201cfc75d9132006bf54d9132006bc54d9132006dd73d9132014fe71d9132004fd71d9132014fc71d9132004ff70d913200cfe70d9132004fd70d913200cfc70d9132006f710d9132006f510d9132006bf649913201cfe7599132004fd7599132084fc7599132084fe7499132004fd7399132086dd7399132004fd7299132086ed7299132014fe7199132004fd7199132014fc7199132084ff709913200cfe7099132004fd709913200cfc7099132086bf4099132006bd4099132006f71099132006f510991320057f75591320cd7c7559132005f771591320c5f47159132005fb70591320bdf87059132004ff75591320067f75591320047f755913201cfe755913201cfc75591320067c755913201c7c7559132006bf7459132004ff7359132006df7359132004ff7259132006ef7259132004ff7159132006f77159132004f77159132014fe7159132014fc7159132006f47159132014f47159132004ff7059132006fb7059132004fb705913200cfe7059132004fd705913200cfc7059132006f8705913200cf87059132006bf4059132006bd4059132006f71059132006f51059132004fe76191320cd7e75191320057d7519132006bd641913201cfe75191320867e751913201c7e7519132004fd75191320867d75191320047d7519132084fc7519132086be7419132006bf5419132086bc5419132014fe7119132004fd7119132014fc7119132084ff701913200cfe7019132004fd701913200cfc7019132006f71019132006f51019132084ff7695132004fe7695132004fd7695132084fc76951320067f659513201e7c65951320cf3f5495132004ff7655132004fe7655132004fd7655132004fc765513201e7e65551320067d6555132005df7355132005dc73551320e4fe7694d3201e7e6594d320067d6594d320cf5f5394d3202cfc7654d320067f6554d3201e7c6554d32005bf7454d32005bc7454d32005ef7254d3202dec7254d3202cfe76d0d32006bf64d0d32086bc64d0d3202dee72d0d32005ed72d0d3202dde76d0d32006de76d0d3202cde76d0d32006df64d0d320079f64d0d32006dd64d0d320079c64d0d3202dde72d0d32007ce72d0d3202dce72d0d32007cd72d0d3202ddc72d0d32005dd71d0d32385df70d0d32385dd70d0d3238f9f40d0d3238f9d40d0d3238fcf20d0d3238fcd20d0d3238fd710d0d3238fd510d0d32004fe7690d32006be6490d32006bd6490d32375de7390d3202cfc7650d320057f7550d320cd7c7550d32006bf6450d32006bc6450d32005ef7250d3202dec7250d32004f
  | 17 => 0x6be7159232006bd7159232006bc7159232006bf5159232006be5159232006bc5159232006be3159232006bc315923202ebf215923202ebe215923202ebd215923202ebc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bd5059232006bc5059232006bf3059232006be3059232006bd3059232006bc305923202ebf205923202ebe205923202ebd205923202ebc2059232006bf1059232006b71059232006be1059232006bd1059232006b51059232006bc1059232084ff769523202cfe7695232004fd769523202cfc769523201e7e65952320067d6595232086be6495232006bd64952320e73f5495232004ff765523202cfe7655232004fd765523202cfc765523201e7e65552320067d6555232006be6455232006bd64552320ccfd7694e3201e7e6594e320067d6594e32006be6494e32006bd6494e320e75f5394e3201cff7654e3202cfc7654e3201e7e6554e320067d6554e32005bf7454e32005bc7454e32006be6454e32006bd6454e32005ef7254e3202dec7254e321e67e65d0e320067d65d0e32086be64d0e32006bd64d0e3202dee72d0e32005ed72d0e321d67e6590e320067d6590e32006be6490e32006bd6490e320057f7550e320e57c7550e321c67e6550e320067d6550e32006be6450e32006bd6450e32005ef7250e3202dec7250e320e57e7510e320057d7510e3219e7e6510e320067d6510e32086be6410e32006bd6410e3202ded76cca32006ed76cca3202f6e65cca3202f6d65cca3202fae64cca3202fad64cca3202fce73cca32007ce53cca32007cd53cca3239def70cca3239ded70cca32397e710cca32397e510cca32004ff755863201cfe755863201cfc7558632004ff7458632084fc745863202e7f525863202e7d525863202edf325863202edd325863202ef771586320def6315863202ef7215863202ef42158632004ff705863200cfe7058632004fd705863200cfc70586320def71058632006f5105863201cfe76d95320ce7e65d9532084fe74d9532004fd74d95320ce7c54d953202cfd73d95320ce7f53d95320ccfd72d95320ce7f52d9532014fe71d9532004fd71d9532014fc71d9532004ff70d953200cfe70d9532004fd70d953200cfc70d9532006f710d9532006f510d95320ce7c6559532005bf7459532005bc7459532005f771595320c5f47159532005fb70595320bdf870595320ccff75595320067f7559532004ff7459532006bf7459532004bf7459532084fc7459532006bc7459532004bc74595320ce7f54595320e4ff7359532006df73595320ce7c53595320f4ff7259532006ef7259532004ff7159532006f77159532004f77159532014fe7159532014fc7159532006f47159532014f471595320067e51595320ce7c515
  | 18 => 0xc32596320067f71596320067e71596320067d71596320067c71596320067e41596320067c41596320067e31596320067c315963202e7f215963202e7e215963202e7d215963202e7c21596320067f70596320067e70596320067d70596320067c70596320067f40596320067e40596320067d40596320067c40596320067f30596320067e30596320067d30596320067c305963202e7f205963202e7e205963202e7d205963202e7c20596320067f10596320067710596320067e10596320067d10596320067510596320067c105963201cfe7599232004fd7599232084fc759923202ebe7499232006bf5499232086bc549923202cfe729923202e7f529923202e7d529923202ebe429923202ebc429923202edf329923202edd3299232014fe7199232004fd7199232014fc7199232006be4199232086bc4199232084ff709923200cfe7099232004fd709923200cfc7099232086bf4099232006be4099232006bd4099232086bc4099232006f71099232006f51099232086bf7599232006be7599232006bd7599232086bc7599232086bf7399232006bd7399232006bf5399232006bc539923202ebf729923202ebe729923202ebd729923202ebc729923202ebf529923202e3f529923202ebe529923202ebd529923202e3d529923202ebc529923202ebf329923202e9f329923202ebe329923202ebd329923202e9d329923202ebc3299232086bf7199232006be7199232006bd7199232086bc7199232006bf5199232006be5199232006bc5199232006be3199232006bc319923202ebf219923202ebe219923202ebd219923202ebc2199232086bf7099232006be7099232006bd7099232086bc7099232006bf5099232006be5099232006bd5099232006bc5099232006bf3099232006be3099232006bd3099232006bc309923202ebf209923202ebe209923202ebd209923202ebc2099232006bf1099232006b71099232006be1099232006bd1099232006b51099232006bc1099232004ff755923201cfe755923201cfc755923202ebf7459232006bf5459232006bc545923202cfc725923202e7f525923202e7d525923202ebe425923202ebc4259232004ff7159232014fe7159232014fc7159232006be4159232006bc4159232004ff705923200cfe7059232004fd705923200cfc7059232006bf4059232006be4059232006bd4059232006bc4059232006f71059232006f51059232006bf7559232006be7559232006bd7559232006bc7559232006bf7359232006bd7359232006bf5359232006bc535923202ebf725923202ebe725923202ebd725923202ebc725923202ebf525923202e3f525923202ebe525923202ebd525923202e3d525923202ebc525923202ebf325923202ebe325923202ebd325923202ebc3259232006bf7159232
  | 19 => 0xf32006be6490f32006bd6490f3202dee7290f32005ed7290f320057f7550f320f57c7550f3202cfd7610f320f57e7510f320057d7510f32086be6410f32006bd6410f320079d4310f3202dee7210f32005ed7210f3202ddd7610f32006dd7610f3202cdd7610f320075e7510f320075d7510f320079e7410f32006df6410f320079e6410f32006dd6410f320079d6410f323bf9f5410f323bf9c5410f3202dde7210f32007ce7210f32007cd7210f3202ddc7210f32005dd7110f323b5df7010f323b5dd7010f32347d71010f32347d51010f320f67e76d4b320f67d76d4b320067f64d4b320067e64d4b320067d64d4b320067c64d4b320f75e73d4b320f75d73d4b3202e7e63d4b320075f43d4b320075c43d4b3202f5e32d4b3202f6e32d4b3202f5c32d4b321867e61d4b321867c61d4b323ae7f60d4b3217e7e60d4b323ae7d60d4b3217e7c60d4b323af5f30d4b323af5d30d4b323af7710d4b323af7510d4b3201cff7654b3201cfc7654b3201e7e6554b320067d6554b32005df7354b32005dc7354b3202fce3254b3201e7f7654b3201e7c7654b320067f6454b320067e6454b320067d6454b320067c6454b320075f7354b320075c7354b3202e7e6354b320075f4354b320075c4354b320f76f7254b3202f6e4254b3202f5e3254b3202f6e3254b3202f4e3254b3202f5c3254b321667e6154b321667c6154b323a67f6054b3215e7e6054b323a67d6054b3215e7c6054b323a75f3054b323a75d3054b323a7771054b323a7751054b32086be64d0b32006bd64d0b32005de73d0b32005dd73d0b320079c43d0b32006be6450b32006bd6450b32005df7350b32005dc7350b320079c4350b320076d5250b320f57e75d87320057d75d8732005be74d8732005bd74d87320eef661d8732014ff76587320eef46158732004ff755873201cfe755873201cfc7558732004ff7458732084fc745873202cfc73587320067f52587320067d52587320eef431587320eef62158732004ff705873200cfe7058732004fd705873200cfc70587320eef71058732006f5105873202e7f7559632004ff7459632084fc74596320e67f54596320e67c54596320e67f535963202cfc725963202e7e525963202e7c5259632004ff7159632014fe7159632014fc71596320e67f51596320067e51596320e67c5159632004ff705963200cfe7059632004fd705963200cfc70596320e67f50596320067e50596320067d50596320e67c5059632006f71059632006f510596320067f74596320067e74596320067d74596320067c74596320067f73596320067d73596320e67c735963202e7f725963202e7e725963202e7d725963202e7c725963202e7f425963202e7e425963202e7d425963202e7c425963202e7f325963202e7e325963202e7d325963202e7
  | 20 => 0x106f6315844202ef7215844202ef42158442004ff705844200cfe7058442004fd705844200cfc7058442106f71058442006f510584420f67e65d97320f4fd75d9732084fe74d9732004fd74d97320f67c54d9732006de73d97320f67f53d9732006ed72d9732014fe71d9732004fd71d9732014fc71d9732004ff70d973200cfe70d9732004fd70d973200cfc70d9732006f710d9732006f510d973201cff76597320f67c65597320067f7559732004ff7459732084fc74597320f67f545973202cfc73597320f67c53597320f67f5259732004ff7159732014fe7159732014fc71597320067e51597320f67c5159732004ff705973200cfe7059732004fd705973200cfc70597320f67f50597320067d5059732006f71059732006f5105973201cfe75d9332004fd75d933201cfc75d9332006de73d9332006ed72d9332014fe71d9332004fd71d9332014fc71d9332004ff70d933200cfe70d9332004fd70d933200cfc70d9332006f710d9332006f510d9332004fd7699332006bf649933201cfe7599332004fd7599332084fc7599332014fe7199332004fd7199332014fc7199332006be4199332086bc4199332084ff709933200cfe7099332004fd709933200cfc7099332086bf4099332006bd4099332006f71099332006f510993320057f75593320f57c7559332004ff75593320067f75593320047f755933201cfe755933201cfc75593320067c755933201c7c7559332006bf7459332006dc7359332004ff7159332014fe7159332014fc7159332006be4159332006bc4159332004ff705933200cfe7059332004fd705933200cfc7059332006bf4059332006bd4059332006f71059332006f510593320f57e75193320057d7519332006bd641933201cfe75193320867e751933201c7e7519332004fd75193320867d75193320047d7519332084fc7519332084fe7419332086be7419332086de7319332086ed7219332014fe7119332004fd7119332014fc7119332084ff701933200cfe7019332004fd701933200cfc7019332006f71019332006f51019332084ff7695332004fe7695332004fd7695332084fc76953320067f659533201e7c6595332086be6495332006bd64953320f73f5495332004ff7655332004fe7655332004fd7655332004fc765533201e7e65553320067d6555332006be6455332006bd6455332005df7355332005dc735533202cfd7694f3201e7e6594f320067d6594f320f75f5394f3202dee7294f32005ed7294f320acff7654f320067f6554f3201e7c6554f32005bf7454f32005bc7454f32005dd76d0f32006dd76d0f32006df64d0f32006dd64d0f3202dde72d0f3202ddc72d0f32005dd71d0f323c5df70d0f323c5dd70d0f3234f9f40d0f3234f9d40d0f3234fd710d0f3234fd510d0f3202cfd769
  | 21 => 0xe525944202e7c5259442004ff7159442014fe7159442014fc715944210e7f51594420067e515944210e7c5159442004ff705944200cfe7059442004fd705944200cfc705944210e7f50594420067e50594420067d505944210e7c5059442006f71059442006f5105944210e7f74594420867e74594420867c74594420067f73594420067e73594420067d73594420067c73594420867f43594420867c435944202e7f725944202e7e725944202e7d725944202e7c725944202e7f425944202e7e425944202e7d425944202e7c425944202e7f325944202e7e325944202e7d325944202e7c32594420067f71594420067e71594420067d71594420067c71594420867f41594420067e41594420867c41594420067e31594420067c315944202e7f215944202e7e215944202e7d215944202e7c21594420067f70594420067e70594420067d70594420067c70594420867f40594420067e40594420067d40594420867c40594420067f30594420067e30594420067d30594420067c305944202e7f205944202e7e205944202e7d205944202e7c20594420067f10594420067710594420067e10594420067d10594420067510594420067c1059442154ff765504201e7e65550420067d65550420873c545504201cfe7598c42004fd7598c4201cfc7598c4202ede7398c42086df4398c42086dc4398c4202e7f5298c4202e7d5298c4202ebf4298c4202ebd4298c4202ede3298c4202edc3298c42014fe7198c42004fd7198c42014fc7198c42004ff7098c4200cfe7098c42004fd7098c4200cfc7098c42006df3098c42006dd3098c42006f71098c42006f51098c42004ff7558c4201cfe7558c4201cfc7558c4202edf7358c42086df4358c42086dc4358c4202e7f5258c4202e7d5258c4202ede3258c4202edc3258c42004ff7158c42014fe7158c42014fc7158c42004ff7058c4200cfe7058c42004fd7058c4200cfc7058c42006df3058c42006dd3058c42006f71058c42006f51058c42004ff7694c4202cfe7694c42004fd7694c4201e7e6594c420067d6594c4210f5f5394c42004ff7654c42004fd7654c4202cfc7654c4201e7e6554c420067d6554c42005bf7454c42085bc7454c42004fd7690c421d67e6590c420067d6590c423d6be6490c42004ff7650c420057f7550c4210d7c7550c421c67e6550c420067d6550c4202def7650842006ef7650842004ef765084202f6e655084202f6d655084202def745084202faf7450842086ee645084202fae6450842087ae5450842007ad5450842087af4350842007ad43508423cfe710508423cfe51050842004ff755844201cfe755844201cfc7558442004ff7358442004fc735844202e7f525844202e7d525844202ebf425844202ebd425844202ef77158442086f74158442086f44158442
  | 22 => 0x4d42005bf7454d42005bc7454d42004fe76d0d4202cfe7690d42006df6390d42006dc6390d4202dee7290d42005ed7290d4202cbe7690d421d6be6590d421d6bc6590d423fdbe7390d42006bf6390d420079f6390d420079c6390d4202dbe7290d42007ae7290d4202dae7290d42007ad7290d4202dbc7290d42005bd7190d42405bf7090d42405bd7090d4240fb71090d4240fb51090d4202cfc7650d420057f7550d4212d7c7550d42006df6350d42006dc6350d42005ef7250d4202dec7250d42004fe7610d4212d7e7510d420057d7510d420079d4310d42005be7610d42006be7610d420073e7510d420073d7510d4219ebe6510d4219ebc6510d42405be7310d420079e7310d42006bf6310d420079e6310d420079d6310d4202dbe7210d4202dbc7210d42086bf6210d42005bd7110d423fdbf7010d423fdbd7010d423f7b71010d423f7b51010d4201e7f76d494212e7e76d494212e7d76d494201e7c76d494212f3e74d494212f3d74d494202e7f64d49420067f63d49420067c63d49420073e43d49420073c43d494202d7d72d494202e7f62d494202f3e42d494202f3c42d494202f6c42d49421867e61d49421867c61d49423ee7f60d494217e7e60d49423ee7d60d494217e7c60d49423ef3f40d49423ef3d40d49423ef7710d49423ef7510d494201cff765494212cfd765494201cfc76549420067f655494201e7c6554942005bf7454942005bc745494202fac425494201e7f76549420067e76549420067d765494201e7c76549420073f74549420073c745494202e7f64549420067f63549420067c63549420073e43549420073c435494202d7f725494212f6f725494202e7f625494202f3e425494202f3c425494202f6c425494202f2c425494202f6c32549421667e61549421667c615494202f6f21549423e67f605494215e7e60549423e67d605494215e7c60549423e73f40549423e73d405494202f6f20549423e76d20549423e77710549423e775105494202dbe74d094202ebf64d09420076f52d09420076d52d094202dee74d094202eef64d094202faf64d0942007ae43d0942087ac43d0942087af40d09423dfad40d09423dfe710d09423dfe510d0942014fe76d8542126f661d854201cfe75d8542004fd75d854201cfc75d854202cfd74d8542004fe73d8542004fd73d85420067f52d85420067d52d8542006f751d8542126f451d8542126f641d8542126f431d8542126f621d8542004ff70d854200cfe70d8542004fd70d854200cfc70d8542126f710d8542006f510d85420057f755854212d7c7558542126f4615854202cff755944202e7f7559442084fe7459442084fc74594420867e54594420867c5459442004ff7359442004fc735944210e7f535944210e7c535944202cfe725944202cfc725944202e7
  | 23 => 0x6dd6394e421475f5394e42004ff7654e42004fd7654e4202cfc7654e4201e7e6554e420067d6554e42005bf7454e42005bc7454e42006de6354e42006dd6354e421e67e65d0e420067d65d0e42006de63d0e421d67e6590e420067d6590e42006de6390e42006dd6390e4202dee7290e42005ed7290e420057f7550e421457c7550e421c67e6550e420067d6550e42006de6350e42006dd6350e42005ef7250e4202dec7250e421457e7510e420057d7510e4219e7e6510e420067d6510e42006dd6310e4202ded76d0a42086ed76d0a4202f6e65d0a4202f6d65d0a4202fae74d0a42087ae54d0a42007ad54d0a4202fce63d0a4202fcd63d0a42417e710d0a42417e510d0a42004ff755864201cfe755864201cfc7558642004ff7358642004fc735864202e7f525864202e7d525864202ebf425864202ebd425864202ef7715864213ef6415864202ef7215864202ef42158642004ff705864200cfe7058642004fd705864200cfc705864213ef71058642006f5105864201cfe76d954212e7e65d954202cfd74d954212e7f54d9542004fe73d9542004fd73d954212e7c53d954212cfd72d954212e7f52d9542014fe71d9542004fd71d9542014fc71d95420067e51d954212e7c51d9542004ff70d954200cfe70d9542004fd70d954200cfc70d954212e7f50d95420067d50d9542006f710d9542006f510d954212e7c6559542005f77159542125f4715954212cff75595420067f7559542144ff7459542006bf745954212e7c5459542004ff7359542004fc735954212e7f5359542154ff7259542006ef7259542004ff7159542006f77159542004f77159542014fe7159542014fc7159542006f47159542014f47159542004ff705954200cfe7059542004fd705954200cfc7059542006f71059542006f51059542144fe769514201e7e65951420067d659514212f3f549514202cfc76551420067f655514201e7c6555142005ef725514202dec725514201cfe75d8d42004fd75d8d4201cfc75d8d42014fe71d8d42004fd71d8d42014fc71d8d42004ff70d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006bf40d8d42006bd40d8d42006f710d8d42006f510d8d42006df6398d420057f7558d4212d7c7558d42005f77158d42125f47158d42005fb7058d4211df87058d4212d7e7518d420057d7518d42006dd6318d4201cfe7518d420067e7518d4201c7e7518d42004fd7518d420067d7518d420047d7518d4201cfc7518d42014fe7118d42004fd7118d42014fc7118d42004ff7018d4200cfe7018d42004fd7018d4200cfc7018d42006f71018d42006f51018d42004fe7694d42004fd7694d42004fc7694d420067f6594d4201e7c6594d4212f5f5394d42004ff7654d42004fe7654d42004fc7654d4201e7e6554d420067d655
  | 24 => 0xe7398e42006df5398e42006dc5398e4202e7f5298e4202e7d5298e4202ebf4298e4202ebd4298e4202ede3298e4202edc3298e42014fe7198e42004fd7198e42014fc7198e42006de3198e42006dc3198e42004ff7098e4200cfe7098e42004fd7098e4200cfc7098e42006df3098e42006de3098e42006dd3098e42006dc3098e42006f71098e42006f51098e42006df7598e42006de7598e42006dd7598e42006dc7598e42006df7498e42006df5498e42006de5498e42006dd5498e42006dc5498e4202ede7298e4202edd7298e4202edc7298e4202edf5298e4202e5f5298e4202ede5298e4202edd5298e4202e5d5298e4202edc5298e4202edf4298e4202e9f4298e4202ede4298e4202edd4298e4202e9d4298e4202edc4298e42006df7198e42006de7198e42006dd7198e42006dc7198e42006df5198e42006de5198e42006dc5198e42006de4198e42006dc4198e4202edf2198e4202ede2198e4202edd2198e4202edc2198e42006df7098e42006de7098e42006dd7098e42006dc7098e42006df5098e42006de5098e42006dd5098e42006dc5098e42006df4098e42006de4098e42006dd4098e42006dc4098e4202edf2098e4202ede2098e4202edd2098e4202edc2098e42006df1098e42006d71098e42006de1098e42006dd1098e42006d51098e42006dc1098e42004ff7558e4201cfe7558e4201cfc7558e4202edf7358e42006df5358e42006dc5358e4202e7f5258e4202e7d5258e4202ede3258e4202edc3258e42004ff7158e42014fe7158e42014fc7158e42006de3158e42006dc3158e42004ff7058e4200cfe7058e42004fd7058e4200cfc7058e42006df3058e42006de3058e42006dd3058e42006dc3058e42006f71058e42006f51058e42006df7558e42006de7558e42006dd7558e42006dc7558e42006dd7458e42006df5458e42006de5458e42006dd5458e42006dc5458e4202edf7258e4202ede7258e4202edc7258e4202edf5258e4202e5f5258e4202ede5258e4202edd5258e4202e5d5258e4202edc5258e4202edf4258e4202ede4258e4202edd4258e4202edc4258e42006df7158e42006de7158e42006dd7158e42006dc7158e42006df5158e42006de5158e42006dc5158e42006de4158e42006dc4158e4202edf2158e4202ede2158e4202edd2158e4202edc2158e42006df7058e42006de7058e42006dd7058e42006dc7058e42006df5058e42006de5058e42006dd5058e42006dc5058e42006df4058e42006de4058e42006dd4058e42006dc4058e4202edf2058e4202ede2058e4202edd2058e4202edc2058e42006df1058e42006d71058e42006de1058e42006dd1058e42006d51058e42006dc1058e42004ff7694e4202cfe7694e42004fd7694e4201e7e6594e420067d6594e42006de6394e42
  | 25 => 0x4b421567d76d4b421573e74d4b421573d74d4b4202e7e64d4b420067e63d4b420067d63d4b420073e43d4b420073c43d4b4202f3e42d4b4202f6e42d4b4202f3c42d4b421867e61d4b421867c61d4b424267f60d4b4217e7e60d4b424267d60d4b4217e7c60d4b424273f40d4b424273d40d4b424277710d4b424277510d4b4201cff7654b42084fc7654b4201e7e6554b420067d6554b42005bf7454b42085bc7454b4202fae4254b4201e7f7654b4201e7c7654b420073f7454b420073c7454b4202e7e6454b420067e6354b420067d6354b420073e4354b420073c4354b421576f7254b4202f3e4254b4202f6e4254b4202f2e4254b4202f3c4254b4202f6e3254b421667e6154b421667c6154b4241e7f6054b4215e7e6054b4241e7d6054b4215e7c6054b4241f3f4054b4241f3d4054b4241f771054b4241f751054b42014ff76587420057f75587421557c7558742086f46158742004ff75587420067f75587420047f755874201cfe755874201cfc75587420067c755874201c7c755874202cfc7458742004ff7358742004fc73587420067f52587420067d5258742086f74158742086f4415874214ef62158742004ff705874200cfe7058742004fd705874200cfc705874214ef71058742006f5105874202e7f75596421467f5459642004ff7359642004fc73596421467f53596421467c535964202cfc725964202e7e525964202e7c5259642004ff7159642014fe7159642014fc71596421467f51596420067e51596421467c5159642004ff705964200cfe7059642004fd705964200cfc70596421467f50596420067e50596420067d50596421467c5059642006f71059642006f510596420067f74596420067d74596421467c74596420067f73596420067e73596420067d73596420067c735964202e7f725964202e7e725964202e7d725964202e7c725964202e7f425964202e7e425964202e7d425964202e7c425964202e7f325964202e7e325964202e7d325964202e7c32596420067f71596420067e71596420067d71596420067c71596420067e41596420067c41596420067e31596420067c315964202e7f215964202e7e215964202e7d215964202e7c21596420067f70596420067e70596420067d70596420067c70596420067f40596420067e40596420067d40596420067c40596420067f30596420067e30596420067d30596420067c305964202e7f205964202e7e205964202e7d205964202e7c20596420067f10596420067710596420067e10596420067d10596420067510596420067c105964212cfd769524201e7e65952420067d65952421473f549524201cff765524202cfc765524201e7e65552420067d65552421473c5455242005ef725524202dec725524201cfe7598e42004fd7598e4201cfc7598e4202ed
  | 26 => 0x2d7e72d855201d7d72d85520467f62d85520476f62d85521667e61d85521677661d85521667661d85521667c61d85521677441d85521677431d85521677621d85520057f70d855215d7e70d85520057d70d855215d7c70d85521677710d85520077510d85520057f74585520073f74585520053f74585520057c74585520073c74585520053c74585520057f73585520057c73585520076f72585520376f62585521657f71585520077761585521667e61585521667c61585521677461585520057f705855215d7e70585520057d705855215d7c7058552167771058552007751058552154fd75d9742086be74d97420867f54d9742004fe73d9742004fd73d97421567c53d9742086ed72d9742014fe71d9742004fd71d9742014fc71d97420067e51d97421567c51d9742084ff70d974200cfe70d9742004fd70d974200cfc70d97421567f50d97420067d50d9742006f710d9742006f510d974201cff76597420867c65597420867f755974202cfc74597420867e54597420867c5459742004ff7359742004fc73597421567f53597421567f5259742004ff7159742014fe7159742014fc7159742004ff705974200cfe7059742004fd705974200cfc7059742006f71059742006f5105974210cff76553420867f65553420867c6555342086df6398f4201cfe7598f42004fd7598f4201cfc7598f4202cfe7498f42086df4398f42086dc4398f42014fe7198f42004fd7198f42014fc7198f42004ff7098f4200cfe7098f42004fd7098f4200cfc7098f42006f71098f42006f51098f420057f7558f421557c7558f42086dc6358f42004ff7558f420067f7558f420047f7558f4201cfe7558f4201cfc7558f420067c7558f4201c7c7558f4202cfc7458f42086df4358f42086dc4358f42004ff7158f42014fe7158f42014fc7158f42004ff7058f4200cfe7058f42004fd7058f4200cfc7058f42006bf4058f42006bd4058f42006f71058f42006f51058f42004ff7694f42084fe7694f42004fd7694f420067f6594f4201e7c6594f42006de6394f42006dd6394f421575f5394f42004ff7654f42004fd7654f42084fc7654f4201e7e6554f420067d6554f42005bf7454f42085bc7454f42006de6354f42006dd6354f42005bd7690f42006bd7690f421d6be6590f421d6bc6590f42006bd6390f4202dbe7290f4202dbc7290f42005bd7190f4243dbf7090f4243dbd7090f423d7b71090f423d7b51090f420057f7550f421557c7550f420879c4350f4202cbd7610f420873e7510f420873d7510f4219ebe6510f42086bc6510f420879e7310f420879e6310f42006bd6310f420879d6310f4202dbe7210f42087ae7210f42087ad7210f4202dbc7210f42005bd7110f42085bf7010f42435bd7010f4242fb71010f4242fb51010f421567e76d
  | 27 => 0xc7098d52007771098d52007751098d520057f7458d520073f7458d520053f7458d520057c7458d520073c7458d520053c7458d520067f6458d520067d6458d520075f6358d520067e6358d520057f7258d520076f7258d520056f7258d520cf6f6258d520057f7158d52007777158d52005777158d521657e7158d521657c7158d52007747158d52165747158d520067e6158d520067c6158d520057f7058d520077b7058d520057b7058d5215d7e7058d520057d7058d5215d7c7058d52007787058d5215d787058d520067f6058d520067d6058d52007771058d52007751058d520057e7618d520057e7418d520057d7418d520067e6418d520067c6418d520067f6318d520075e6318d520067d6318d520075d6318d520ae7f6218d520af6f6218d521657e7118d520057d7118d521657c7118d520057f7018d5215d7e7018d520057d7018d5215d7c7018d52007771018d52007751018d520057f76d0d520057e76d0d520057d76d0d520057c76d0d5202d7e72d0d520076e72d0d5202d6e72d0d520057d72d0d520076d72d0d520056d72d0d5202d7c72d0d521e67f62d0d521e76f62d0d521657e71d0d520057d71d0d521657c71d0d5245d7f70d0d5215d7e70d0d5245d7d70d0d5215d7c70d0d5247f3f40d0d5247f3d40d0d5247f7710d0d5247f7510d0d520057f7690d520057e7690d520057d7690d520057c7690d5246d7d7490d520073f6490d520073c6490d5244d7e7390d520073f4390d520075f4390d5202d7e7290d520076e7290d5202d6e7290d520057d7290d520076d7290d520056d7290d5202d7c7290d521d67f6290d521d76f6290d521657e7190d520057d7190d521657c7190d524557f7090d5215d7e7090d524557d7090d5215d7c7090d52477771090d52477751090d520057f7650d520067f7650d520047f7650d520057e7650d520057d7650d520057c7650d520067c7650d520047c7650d520075f4350d520073e4350d520057f7250d5202d7e7250d5202d7c7250d521c67f6250d521c76f6250d520057f7150d521657e7150d521657c7150d5246d7f7050d5215d7e7050d5246d7d7050d5215d7c7050d524673f4050d524673d4050d52467771050d52467751050d520057f7610d520057e7610d520067e7610d520047e7610d520057d7610d520067d7610d520047d7610d520057c7610d5245d7e7410d520073f6410d520073c6410d524557e7310d520073f4310d520075e4310d520073d4310d520075d4310d5202d7e7210d520057d7210d5202d7c7210d5219e7f6210d5219f6f6210d521657e7110d520057d7110d521657c7110d5244d7f7010d5215d7e7010d5244d7d7010d5215d7c7010d52447771010d52447751010d521657e76d85520057e74d85520057d74d85520057e73d85520057d73d8552
  | 28 => 0xd52004fe7650d52004fc7650d520057f7550d5201d7e7550d520057d7550d5201d7c7550d52004fe7610d52004fd7610d52084fc7610d520057f7510d5201d7e7510d520057d7510d5201d7c7510d52006bf6410d52086bc6410d5219f3f5410d5219f3c5410d52014fe76d855201d7e75d8552166f661d85521677651d855202cfd75d855202c7d75d8552014fc75d8552084fe74d8552004fd74d8552004fe73d8552004fd73d855201cfd72d85521667e51d8552166f651d85521667651d85521667c51d8552166f441d8552166f431d8552166f621d8552004ff70d855200cfe70d8552004fd70d855200cfc70d8552166f710d8552006f510d8552005bf7458552005bc7458552166f461585520057e73d91520057d73d91521467f62d91521476f62d91521657e71d91520057d71d91521657c71d91520073e41d91520073c41d91520057f70d915215d7e70d91520057d70d915215d7c70d91520073f40d91520073d40d91520077710d91520077510d91520057e74991520067f64991520073f64991520063f64991520057e73991520057d73991520057d72991520076d72991520056d72991521576f62991521657e71991520057d71991521657c71991520067e61991520067c61991520057f709915215d7e70991520057d709915215d7c70991520067f60991520067d60991520077710991520077510991520073f64591520067e64591520057f73591520057c73591520057f72591520076f72591520056f725915212f6f62591520057f71591520077771591520057771591521657e71591521657c71591520077471591521657471591520057f705915215d7e70591520057d705915215d7c70591520077710591520077510591520057e76191520067f64191520073e64191520067d64191520073d64191520063d64191520057e73191520057d731915210e7f621915210f6f62191521657e71191520057d71191521657c71191520067e61191520067c61191520073e41191520073c41191520057f701915215d7e70191520057d701915215d7c70191520067f60191520067d60191520073f40191520073d40191520077710191520077510191520057e74d8d520057d74d8d520067f64d8d520067d64d8d520e67f62d8d520e76f62d8d521657e71d8d520057d71d8d521657c71d8d520067e61d8d520067c61d8d520057f70d8d5215d7e70d8d520057d70d8d5215d7c70d8d520067f60d8d520067d60d8d520077710d8d520077510d8d520057e7498d520057d7498d520067e6498d520067c6498d520057e7398d520067f6398d520075f6398d520065f6398d520057d7298d520076d7298d520056d7298d520f76f6298d521657e7198d520057d7198d521657c7198d520057f7098d5215d7e7098d520057d7098d5215d7
  | 29 => 0x2d7e72951520076e72951520076d729515202d7c729515201e7f629515201f6f62951521657e71951520057d71951521657c71951522267e61951522267c61951524bd7f709515215d7e70951524bd7d709515215d7c70951524b67f60951524b67d60951524b77710951524b775109515202c7c765515201d7f745515201f3f74551520073f64551520867c64551520073c64551520063c64551520057f73551520057c73551520076f725515202d7e725515202d7c72551520076c725515201e7f625515201f6f62551520057f71551521657e71551521657c71551524ad7f705515215d7e70551524ad7d705515215d7c70551524a77710551524a775105515202cfd75d8d52084fe74d8d52004fd74d8d520e67f54d8d520067d54d8d520e6de53d8d520e6dd53d8d520e67c53d8d52014fe71d8d52004fd71d8d52014fc71d8d520067e51d8d520e67c51d8d52004ff70d8d5200cfe70d8d52004fd70d8d5200cfc70d8d520e67f50d8d520067d50d8d52006f710d8d52006f510d8d52006df6398d520cded7298d52005bf7458d52005bc7458d520f5ef7258d52005f77158d52165f47158d52005fb7058d5215df87058d52006dd6318d5202cfd7518d52084fe7418d52004fd7418d520067e5418d520ae7c5418d520ae7f5318d520aede5318d520aedd5318d52014fe7118d52004fd7118d52014fc7118d52004ff7018d5200cfe7018d52004fd7018d5200cfc7018d52006f71018d52006f51018d5202c7e7694d520057e7494d520057d7494d520067c6494d5201d7e7394d5201f5e7394d520067f6394d520075f6394d520065f6394d520075c6394d5202d7e7294d520076e7294d520076d7294d5202d7c7294d5201e7f6294d5201f6f6294d521657e7194d520057d7194d521657c7194d5249d7f7094d5215d7e7094d5249d7d7094d5215d7c7094d52497771094d52497751094d5202c7c7654d520057f7454d520073f7454d520053f7454d520057c7454d520073c7454d520053c7454d520067f6454d5201d7f7354d5201f5f7354d520075f6354d520067c6354d520075c6354d520076f7254d5202d7e7254d5202d7c7254d520076c7254d5201e7f6254d5201f6f6254d520057f7154d521657e7154d521657c7154d521f67e6154d521f67c6154d5248d7f7054d5215d7e7054d5248d7d7054d5215d7c7054d524867f6054d524867d6054d52487771054d52487751054d52004fe76d0d52004fd76d0d52084fc76d0d520057f75d0d5201d7e75d0d520057d75d0d5201d7c75d0d5202dee72d0d52005ed72d0d52004fe7690d52004fd7690d52004fc7690d520057f7590d5201d7e7590d520057d7590d5201d7c7590d52006bf6490d52006bc6490d521d73f5490d521d73c5490d5202dee7290d52005ed7290d52004ff765
  | 30 => 0xd4099252006f71099252006f5109925202ebf745925212ebe545925212ebd5459252004ff7359252004fc735925202cfc725925202e7f525925202e7d525925202ebe425925202ebc4259252004ff7159252014fe7159252014fc7159252004ff705925200cfe7059252004fd705925200cfc7059252006bf4059252006bd4059252006f71059252006f51059252084fe7498e52004fd7498e5202ede7398e520f6de5398e520f6dd5398e5202cfe7298e5202e7f5298e5202e7d5298e5202ede3298e5202edc3298e52014fe7198e52004fd7198e52014fc7198e52004ff7098e5200cfe7098e52004fd7098e5200cfc7098e52006df3098e52006dd3098e52006f71098e52006f51098e52004ff7458e52084fc7458e5202edf7358e520cede5358e520cedd5358e5202cfc7258e5202e7f5258e5202e7d5258e5202ede3258e5202edc3258e52004ff7158e52014fe7158e52014fc7158e52004ff7058e5200cfe7058e52004fd7058e5200cfc7058e52006df3058e52006dd3058e52006f71058e52006f51058e52084ff76d0e5202cfe76d0e52004fd76d0e52006de63d0e52006dd63d0e5202dee72d0e52005ed72d0e52004ff7690e5202cfe7690e52004fd7690e52006be6490e52006bd6490e5202dee7290e52005ed7290e52004ff7650e52004fd7650e5202cfc7650e520057f7550e5201d7c7550e52084ff7610e5202cfe7610e52004fd7610e5201d7e7510e520057d7510e52086be6410e52006bd6410e52006de6310e52006dd6310e52004ff7458652084fc7458652004ff7358652004fc735865202cfe725865202cfc725865202e7f525865202e7d525865202ef77158652176f6515865202ef7215865202ef42158652004ff705865200cfe7058652004fd705865200cfc7058652176f71058652006f5105865202cfd75d9152146be54d9152146bd54d91521467c54d9152004fe73d9152004fd73d91521467f53d9152014fe71d9152004fd71d9152014fc71d9152006be41d9152006bc41d9152004ff70d915200cfe70d9152004fd70d915200cfc70d9152006bf40d9152006bd40d9152006f710d9152006f510d9152006bf649915212ded7299152155ef7259152005f77159152165f47159152006bd641915202cfd75191520867f5419152086be541915210ebd5419152004fe7319152004fd731915210e7c5319152014fe7119152004fd7119152014fc71191520067e511915210e7c5119152006be4119152086bc4119152084ff701915200cfe7019152004fd701915200cfc701915210e7f50191520067d5019152086bf4019152006bd4019152006f71019152006f5101915202c7e769515201d7e749515201f3e74951520067f64951520073f64951520063f64951520073c64951520057e73951520057d7395152
  | 31 => 0xc43086de6450c430879e6450c430879e5450c430079d5450c43005df7250c435079e4050c430879c4050c43507d71050c43507d51050c4319d7e75988430057d75988430067e65988430067d6598843086ef629884302eec62988430067e65588430067d6558843086ec6258843004ff755884301cfe75588430067e75588430067d755884301cfc7558843086ef4258843086ec4258843004ff7158843014fe7158843014fc7158843004ff705884300cfe7058843004fd705884300cfc7058843006ef2058843006ed2058843006f71058843006f51058843014ff76584430067e65584430067d6558443086f46158443004ff755844301cfe755844301cfc7558443004ff725844302cfc7258443086f74158443086f44158443196f43158443196f62158443004ff705844300cfe7058443004fd705844300cfc7058443196f71058443006f510584431e57f76d0f5201d7e76d0f521e57d76d0f5201d7c76d0f521e73e64d0f521e73d64d0f5202d7e72d0f520057d72d0f5202d7c72d0f521857e71d0f520057d71d0f521857c71d0f524fd7f70d0f5217d7e70d0f524fd7d70d0f5217d7c70d0f524f73f40d0f524f73d40d0f524f77710d0f524f77510d0f521d57f7690f5201d7e7690f521d57d7690f5201d7c7690f521d73f6490f521d73c6490f521d75e6390f521d75d6390f520073f4390f520075f4390f5202d7e7290f520057d7290f5202d7c7290f521857e7190f520057d7190f521857c7190f524ed7f7090f5217d7e7090f524ed7d7090f5217d7c7090f524e7771090f524e7751090f521c57f7650f520067f7650f520047f7650f5201d7e7650f521c57d7650f5201d7c7650f521c67c7650f5201c7c7650f521c73e6450f521c73d6450f521c75e6350f521c75d6350f520075f4350f520073e4350f520057f7250f5202d7e7250f5202d7c7250f520057f7150f521857e7150f521857c7150f524dd7f7050f5217d7e7050f524dd7d7050f5217d7c7050f524d73f4050f524d73d4050f524d7771050f524d7751050f5219d7f7610f5201d7e7610f5219e7e7610f5201c7e7610f5219d7d7610f520067d7610f520047d7610f5201d7c7610f5219f3f6410f5219f3c6410f520073f4310f520075e4310f520073d4310f520075d4310f5202d7e7210f520057d7210f5202d7c7210f521857e7110f520057d7110f521857c7110f524cd7f7010f5217d7e7010f524cd7d7010f5217d7c7010f524c7771010f524c7751010f5202ebe7499252086be5499252156bd5499252004fe7399252004fd739925202cfe729925202cfc729925202e7f529925202e7d529925202ebe429925202ebc4299252014fe7199252004fd7199252014fc7199252084ff709925200cfe7099252004fd709925200cfc7099252086bf4099252006b
  | 32 => 0x867e54594430867c545944319ebc545944319cfc735944319e7c5359443004ff725944302cfc725944319e7f525944319e7c5259443004ff7159443014fe7159443014fc715944319e7f51594430067e515944319e7c5159443004ff705944300cfe7059443004fd705944300cfc705944319e7f50594430067e50594430067d505944319e7c5059443006f71059443006f510594430857f765944319e7f765944301c7f765944319f3f74594430873c74594430057f72594430867f62594430867c62594430867f61594430067e61594430867c61594430867f60594430067e60594430067d60594430867c605944300777105944300775105944319e7f745944319e3f74594430867e74594430867c74594430063c745944319e7f73594430067e73594430067c73594430867f43594430867c43594430067f72594430047f72594430067e72594430067d72594430067c72594430867f42594430867c42594430067f71594430067e71594430067d71594430067c71594430867f41594430067e41594430867c41594430067e31594430067c31594430067e21594430067c21594430067f70594430067e70594430067d70594430067c70594430867f40594430067e40594430067d40594430867c40594430067f30594430067e30594430067d30594430067c30594430067f20594430067e20594430067d20594430067c20594430067f10594430067710594430067e10594430067d10594430067510594430067c10594431e4ff765504301e7e65550430067d655504319dbf74550430873c54550431d4ff7694c43084fe7694c4301cfd7694c43084fc7694c4301e7e6594c430067d6594c43085be7494c43005bd7494c4319f3c5494c4319f5f5394c431d4ff7654c4301e7e6554c430067d6554c43005bf7454c43085bc7454c4319f3f5454c4319dbe75d0c43085bc75d0c430873e65d0c430873d65d0c43005bd72d0c43086bf60d0c43536bd60d0c43537b710d0c43537b510d0c431d67e6590c430067d6590c4352dbd7490c43526be6490c430875e6590c430875d6590c43085dd7490c43086de6490c430879e6490c4351f9f5490c430879c5490c43005dd7290c43517d71090c43517d51090c43004ff7650c430057f7550c4319d7c7550c431c67e6550c430067d6550c43005bf7650c43006bf7650c43004bf7650c430073f7550c4319dbe7550c4319dbc7550c430073c7550c4319d3c7550c430073e6550c430073d6550c43085bf7350c4350ebe6350c430079e5350c430079d5350c43005bf7250c43506bf6050c43506bd6050c435079e3050c435079c3050c43507b71050c43507b51050c43085df7650c43006df7650c43004df7650c430075f7550c430075c7550c430875e6550c430875d6550c43085df7450c430079f745
  | 33 => 0xc72595431c67f5259543004ff7159543014fe7159543014fc7159543004ff705954300cfe7059543004fd705954300cfc7059543006f71059543006f510595430057e76195431c67e76195430047e76195430057d72195430067e61195430067c61195430067f60195430067e60195430067d60195430067c60195430073f40195430073d40195430077710195430077510195431d4fe76951430067f659514301e7c65951431c73f549514301cfc76551430067f655514301e7c6555143005df7355143005dc73551431e4fe7694d430067f6594d4301e7c6594d431c75f5394d4301cff7654d431c4fd7654d4301cfc7654d430067f6554d4301e7c6554d43005bf7454d43005bc7454d430067f65d0d431e67c65d0d430075f65d0d430075c65d0d430879f40d0d435479d40d0d43547d710d0d43547d510d0d430067f6590d431d67c6590d430073f6590d431d6be6590d431d6bc6590d430073c6590d431d63c6590d430079f6390d4350dbf7090d4350dbd7090d4353fb71090d4353fb51090d430067f65d89430067c65d89430067f75d894301cfe75d8943004fd75d894301cfc75d89430067c75d8943006df43d8943006be43d8943014fe71d8943004fd71d8943014fc71d8943004ff70d894300cfe70d8943004fd70d894300cfc70d8943006bf40d8943006bd40d8943006f710d8943006f510d89431c57e75989430057d75989430067f65989430067c6598943006ef62989430057f75589431c57c75589430067f65589430067c6558943005f771589431bdf47158943005fb70589431b5f870589431c57e75189430057d75189430067f65189430067c651894302eee6218943006ed6218943014fe76d85430067f65d85430067c65d85431bef661d854301cfe75d8543004fd75d854301cfc75d854302cfe72d8543004fd72d85431bef641d85431bef631d85431bef421d8543004ff70d854300cfe70d8543004fd70d854300cfc70d85431bef710d8543006f510d85430057f75585431c57c75585430067f65585430067c65585431bef4615854319cfd75d9443084fe74d9443086be74d944319ebf54d9443086bc54d94431d4fe73d9443086de73d944302cfe72d9443004fd72d944319e7f52d9443014fe71d9443004fd71d9443014fc71d9443084ff70d944300cfe70d9443004fd70d944300cfc70d9443006f710d9443006f510d94430047d769944319f3f74994430873c74994430867e64994430057d72994430867f62994430867c62994430867f61994430067e61994430867c61994430867f60994430067e60994430067d60994430867c609944300777109944300775109944301cff76594430867c65594430873c54594430867f7559443084fe7459443084fc745944319ebc745944319cbc745944319ebf5459443
  | 34 => 0x52431d5bf74552431d73c5455243005df7355243005dc735524301cfe7694e4301cfd7694e4301e7e6594e430067d6594e43005be7494e43005bd7494e431d73c5494e431d75f5394e4319cff7654e430067f6554e4301e7c6554e431d5bf7454e43005bc7454e431d73f5454e43005bd76d0e43006bd76d0e431d5be75d0e431d5bc75d0e430079e53d0e430079d53d0e43005bd72d0e4354ebf60d0e4354ebd60d0e4354fb710d0e4354fb510d0e43005dd76d0e43086dd76d0e430879e54d0e430079d54d0e4354fd710d0e4354fd510d0e431d57e7598a430057d7598a43006ef6298a43004ff7558a4301cfe7558a4301cfc7558a43006df4358a43004ff7158a43014fe7158a43014fc7158a43006ee2158a43006ec2158a43004ff7058a4300cfe7058a43004fd7058a4300cfc7058a43006ef2058a43006ed2058a43006f71058a43006f51058a431d57e7518a430057d7518a4302eee6218a43006ed6218a431d57e75d86430057d75d8643005ee72d8643005ed72d86431cef661d8643014ff76586431cef46158643004ff755864301cfe755864301cfc7558643004ff725864302cfc72586431cef641586431cef43158643004ff705864300cfe7058643004fd705864300cfc70586431cef71058643006f5105864301cfe76d95431c67e65d95431c4fd74d95431c67f54d95431c4fd73d95431c67f53d954302cfe72d9543004fd72d95431c67f52d95431c67c52d9543014fe71d9543004fd71d9543014fc71d95431c67f51d95430067e51d95431c67c51d9543004ff70d954300cfe70d9543004fd70d954300cfc70d95431c67f50d95430067e50d95430067d50d95431c67c50d9543006f710d9543006f510d95431c57e76d954301c7e76d95430057d72d95430067e61d95430067c61d95430067f60d95430067e60d95430067d60d95430067c60d95430073f40d95430073d40d95430077710d95430077510d95430067f74d95431c67e74d95430067d74d95430067f73d95431c67e73d95430067d73d95430067f72d95430067e72d95430067d72d95430047d72d95430067c72d95430067f71d95430067e71d95430067d71d95430067c71d95430067e41d95430067c41d95430067e31d95430067c31d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95430067f40d95430067e40d95430067d40d95430067c40d95430067f30d95430067e30d95430067d30d95430067c30d95430067f20d95430067e20d95430067d20d95430067c20d95430067f10d95430067710d95430067e10d95430067d10d95430067510d95430067c10d95431c67c65595431c4ff75595430067f75595431d4ff7459543006bf74595431d4bf74595431e4ff7359543006df7359543004ff725954302cf
  | 35 => 0x4fd74d855301cfd73d855302cfe72d8553004fd72d85530667f52d85531f67e51d85531f6f651d85531f67c51d85531f6f631d85531f6f421d8553004ff70d855300cfe70d8553004fd70d855300cfc70d85531f6f710d8553006f510d8553005bf7458553005bc7458553006bf6458553006bc64585531f6f461585531e4fd75d9743086be74d97430867f54d9743086dd73d97431e67c53d974302cfe72d9743004fd72d97431e67f52d9743014fe71d9743004fd71d9743014fc71d97430067e51d97431e67c51d9743084ff70d974300cfe70d9743004fd70d974300cfc70d97431e67f50d97430067d50d9743006f710d9743006f510d974301cff76597430867c65597430867f75597430867e54597430867c54597431e67f5359743004ff725974302cfc72597431e67f5259743004ff7159743014fe7159743014fc7159743004ff705974300cfe7059743004fd705974300cfc7059743006f71059743006f5105974319cff76553430867f65553430867c65553431c4fd7694f430067f6594f4301e7c6594f431e75f5394f4301cff7654f43084fc7654f4301e7e6554f430067d6554f43005bf7454f43085bc7454f431e57e7598b430057d7598b43086ef6298b4302eec6298b43086ec6258b43004ff7558b4301cfe7558b4301cfc7558b43086ef4258b43086ec4258b43004ff7158b43014fe7158b43014fc7158b43004ff7058b4300cfe7058b43004fd7058b4300cfc7058b43006bf4058b43006bd4058b43006f71058b43006f51058b43014ff76587430057f75587431e57c7558743086f46158743004ff75587430067f75587430047f755874301cfe755874301cfc75587430067c755874301c7c7558743004ff725874302cfc7258743086f74158743086f441587431def63158743004ff705874300cfe7058743004fd705874300cfc70587431def71058743006f510587431d67e65d96431d73c54d96431d4fd75d9643006bd74d96431d6bf54d96431d67c54d96431d6bc54d9643006de73d96431d67f53d964302cfe72d9643004fd72d96431d67f52d9643014fe71d9643004fd71d9643014fc71d9643004ff70d964300cfe70d9643004fd70d964300cfc70d9643006f710d9643006f510d964301cff76596431d67c65596431d73f54596430067f75596431d6bf74596431d67f54596431d6bf54596431d63f54596431d6bc54596431d67c5359643004ff725964302cfc72596431d67f5259643004ff7159643014fe7159643014fc71596430067e51596431d67c5159643004ff705964300cfe7059643004fd705964300cfc70596431d67f50596430067d5059643006f71059643006f510596431c4fd76952430067f659524301e7c65952431d5be74952431d73f549524301cff765524301e7e65552430067d655
  | 36 => 0xe7019153004fd701915300cfc701915319e7f50191530067d5019153086bf4019153006be4019153006bd4019153086bc4019153006f71019153006f510191531d5be7619153006be761915319f3e75191530073d751915319f9f531915319f3c531915319f9c531915319f3f5219153006be6119153006bc61191530073e511915319f3c5119153006bf6019153006be6019153006bd6019153006bc601915319f3f50191530073d5019153007b71019153007b51019153086bf751915319ebe751915319e3e7519153086bc7519153086bf731915319ebd731915319ebf531915319ebe531915319ebd531915319ebc531915319e3c5319153086bf7219153006be7219153006bd7219153086bc721915319ebf521915319e3f521915319ebe521915319ebd521915319ebc5219153086bf7119153006be7119153006bd7119153086bc711915319ebf511915319ebe51191530063e511915319ebd511915319ebc511915319e3c5119153006be3119153006bc3119153006be2119153006bc2119153086bf7019153006be7019153006bd7019153086bc701915319ebf501915319e3f501915319ebe501915319ebd50191530063d501915319ebc5019153006bf3019153006be3019153006bd3019153006bc3019153006bf2019153006be2019153006bd2019153006bc2019153006bf1019153006b71019153006be1019153006bd1019153006b51019153006bc101915301d7f745515301f3f74551530073f64551530867c64551530073c64551530063c64551530075f73551530057c73551530075c735515301e7f635515301f5f63551530057f72551531f57e71551531f57c715515356d7f705515356d7d70551535677710551535677510551530057d7494d530073f6494d530067c6494d530073c6494d530063c6494d5301d7e7394d5301f5e7394d5301e7f6394d5301f5f6394d5301e5f6394d530057d7294d531f57e7194d531f57c7194d5355d7f7094d5355d7d7094d53557771094d53557751094d53006bf64d8953006bc64d89530067f75d8953084fe74d8953004fd74d89530f67f54d89530067d54d89530067e53d89530f67c53d89530f6ee52d8953014fe71d8953004fd71d8953014fc71d89530067e51d89530f67c51d8953004ff70d895300cfe70d8953004fd70d895300cfc70d89530f67f50d89530067d50d8953006f710d8953006f510d8953005be7498953005bd7498953006bf6498953006bc6498953006ef6298953005bf7458953005bc7458953006bf6458953006bc6458953005f771589531f5f47158953005fb70589531edf87058953006bf6418953006bc641895302eee6218953006ed6218953014fe76d855301d7e75d8553006bf64d8553006bc64d85531f6f661d85531f77651d8553084fe74d8553
  | 37 => 0x525301f3e74952530073e64952530067d64952530073d64952530063d64952530075e73952530057d73952530075d73952530055d739525301e7e639525301f5e63952530057d72952532267e61952532267c61952535767f60952535767d60952535777710952535777510952530f75f53d8a530e75f5398a53006ef6298a530cf5f5358a530067d7558a53004ff7458a53084fc7458a530067e5458a530ce7c5458a530ce7f5358a530ceee5258a53004ff7158a53014fe7158a53014fc7158a53004ff7058a5300cfe7058a53004fd7058a5300cfc7058a53006ef2058a53006ed2058a53006f71058a53006f51058a530af5f5318a5302eee6218a53006ed6218a530675f53d8653206f661d8653014ff76586530575f5358653206f46158653004ff7458653084fc745865301cfc7358653004ff725865302cfc72586530567f5258653206f65158653206f43158653004ff705865300cfe7058653004fd705865300cfc7058653206f71058653006f510586531d6be54d91531d6bd54d915302cfe72d9153004fd72d91531d67f52d9153014fe71d9153004fd71d9153014fc71d9153006be41d9153006bc41d9153004ff70d915300cfe70d9153004fd70d915300cfc70d9153006bf40d9153006be40d9153006bd40d9153006bc40d9153006f710d9153006f510d91530073f75d91531d73c75d91531d79f53d91531d73c53d91531d79c53d91531d73f52d9153006be61d9153006bc61d91530073e51d91531d73c51d9153006bf60d9153006be60d9153006bd60d9153006bc60d91531d73f50d91530073d50d9153007b710d9153007b510d91531d6bf75d91531d6be75d91531d6bc75d91531d6bf73d91531d6bd73d91531d6bf53d91531d6be53d91531d6bc53d9153006bf72d9153006be72d9153006bd72d9153006bc72d91531d6bf52d91531d63f52d91531d6be52d91531d6bd52d91531d6bc52d9153006bf71d9153006be71d9153006bd71d9153006bc71d91531d6bf51d91531d6be51d91531d6bd51d91531d6bc51d9153006be31d9153006bc31d9153006be21d9153006bc21d9153006bf70d9153006be70d9153006bd70d9153006bc70d91531d6bf50d91531d6be50d91531d6bd50d91531d6bc50d9153006bf30d9153006be30d9153006bd30d9153006bc30d9153006bf20d9153006be20d9153006bd20d9153006bc20d9153006bf10d9153006b710d9153006be10d9153006bd10d9153006b510d9153006bc10d9153006bf64991531c5dd73991531e5df7359153006bd64191530867f5419153086be541915319ebd541915319e7c531915302cfe7219153004fd721915319e7f5219153014fe7119153004fd7119153014fc71191530067e511915319e7c5119153006be4119153086bc4119153084ff701915300cf
  | 38 => 0x14fe7158a54014fc7158a540067e5158a5412e7c5158a54004ff7058a5400cfe7058a54004fd7058a5400cfc7058a5412e7f5058a540067d5058a54006f71058a54006f51058a54014ff765865401d7c75586540773f5458654086f46158654227765158654084fc7458654004ff7358654004fc7358654004ff725865402cfc72586540767f52586542267e5158654226f651586542267651586542267c5158654086f74158654086f44158654004ff705865400cfe7058654004fd705865400cfc7058654226f71058654006f510586540857e74951540873e74951540867f649515401f3f649515401e3f64951540057d73951540057d72951542267e61951542267c619515457e7f609515457e7d609515457f77109515457f7510951541e6de53d8d5402cfe72d8d54004fd72d8d541e67f52d8d54014fe71d8d54004fd71d8d54014fc71d8d54004ff70d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54006de30d8d54006dc30d8d54006f710d8d54006f510d8d54006df6398d54006dd6318d5419ebf5418d540067e5418d5419e7c5418d5419ebc5418d5419e7f5318d5419edd5318d5402cfe7218d54004fd7218d5419e7f5218d54014fe7118d54004fd7118d54014fc7118d54004ff7018d5400cfe7018d54004fd7018d5400cfc7018d54006de3018d54006dc3018d54006f71018d54006f51018d540067f75d89540067e54d89541567c54d8954004fe73d8954004fd73d89541567f53d8954156ee52d8954014fe71d8954004fd71d8954014fc71d8954004ff70d895400cfe70d8954004fd70d895400cfc70d8954006f710d8954006f510d8954005de7398954005dd7398954006ef6298954005f77158954215f4715895402eee6218954006ed6218954014fe76d8554216f661d855401cfd74d8554004fe73d8554004fd73d855402cfe72d8554004fd72d855408e7f52d8554216f651d8554216f641d8554216f421d8554004ff70d855400cfe70d8554004fd70d855400cfc70d8554216f710d8554006f510d8554216f461585541d73c54d925319dde73d92531d75f53d9253006bf64992531e75f5399253086be54992531e6bd549925302cfe7299253004fd72992531e67f5299253014fe7199253004fd7199253014fc7199253084ff709925300cfe7099253004fd709925300cfc7099253086bf4099253006bd4099253006f71099253006f510992531c75f53592531c6be54592531c6bd54592531c67c54592531c67f5359253004ff725925302cfc72592531c67f5259253004ff7159253014fe7159253014fc7159253004ff705925300cfe7059253004fd705925300cfc7059253006bf4059253006bd4059253006f71059253006f51059253006bd641925319f3c54192531d5de731925319f5f531925301d7e749
  | 39 => 0x7000400000140010024000000c0070000004000000000200030000000000800b0010002002800b00440000010002001c000001000000000060000000000000c001401300100010024000004c0000050000000400000100020028004001000d00080050004008000c00a000000000000010000000001001700580030000007000801700140010010000000000400000100008001004000c000c0000000005000000b00040000004001001400000040010024002002400e001001b000800e001400300000000000005001400d0004005004000200300070038003001000100240190020000000400000100000000000001c001000000900000000024004000000d000000c0000004007c0010000002000800000000170000000000400000040000010000000c009000800800240030004012001000300040000024003000c0000090002001000a0004000000400200140090000003000001e00000010040001000000600140110000003000c009000000200100090004001002c0090058016000000300300020014002003000300100000018000000400000080040010000000800300000030010003002000b00280000000004000000400000110014000001c00000000000034000002c000000000700040010000000000800200040080018005002800500040000008006002c000005400000000020014001000800500180050018005000000200000040000000000000000000050008000001400d0000000000001a0000000000c006001c00800040060028006001c00000040010000003000c003004800200040000000000000400500000080000000000c00b002c005000000200000010004003000c000000000000140020030004000000000140150038001001000000000020004012001c00300040010004000000800000000041d73f5498e54086df6398e54084fe7498e541d6bf5498e541d6bc5498e541d6dd5398e54086df4398e54086dc4398e5402cfe7298e54004fd7298e541d67f5298e54014fe7198e54004fd7198e54014fc7198e54004ff7098e5400cfe7098e54004fd7098e5400cfc7098e54006f71098e54006f51098e541c73f5458e54086dc6358e54084fc7458e541c67f5458e541c6de5358e541c67c5358e54086df4358e54086dc4358e54004ff7258e5402cfc7258e541c67f5258e54004ff7158e54014fe7158e54014fc7158e540067e5158e541c67c5158e54004ff7058e5400cfe7058e54004fd7058e5400cfc7058e541c67f5058e540067d5058e54006f71058e54006f51058e541473f5498a54086ef6298a5402eec6298a5412f3f5458a54086ec6258a540067d7558a54084fc7458a5412e7f5458a54004ff7358a54004fc7358a5412e7c5358a5412eee5258a54086ef4258a54086ec4258a54004ff7158a54
  | 40 => 0x1c0010010001000000700000030010000000c0000000000000800d001c0090000000000c001000000a00000010008005003802200080020004006001c00900000010014006001c001002c0060000003002001a0000000000800f0000004002400200240030034006003400000080010040003002000800100010018001000400b0014004000400b0004005000c003001400300100030020011000001300180040000000002800f004000500140000020000001c00000000060008000000800b00000090004019000400400540010024000000800100040000000000000400200080010000005000c000002400100540000004002002800b0014004000400000140000004003000000500480050000003000c00000040030004002000c000000000000140010008001001000200040000000009005800000000260000006000000d004800100000010000013000000600180010010001000c0030020016000000000080030000001000c0020004000001400000d400100480060000000000c0050000007000000200300110000001000400100040050004005000000a004000700080010018003000400000080070030023004400000180010048001001c00000080030008000000000600000000004061004400000040000000001001400000040000000001000800b000000a002c00000040000008000003000300000190008001002000d000001000140030014000000c014001000f00000010004001000000000000010000000000000500100030004000001c0010000015001000100100090000008000c00000100010004000000c00400000020038000000400000180070000000001000100000000000006000400300240160010000000000200400000040002000000000080060020000000c00100000020004000003c000002c000003800000000010018011000c00600040030000006000000100040020010007000800500040090034000000401d000c00000d000000400010008000000400700000050000000000800100000000004000000000000140000004001000800600200080000000002c001000000000140000020000001000000040050030000003c01c0008001000000300080000004003000c0000008000000000b000400000040050044002000000100000050028000002c0010004001001000300080000018001000c001006000000000170014001002400f000c0040004004000c00000100040014002001c000004c00100040000000000001c001001c0000018001000c0000008004000400700040010040002000400000000010008003000000300000080004002001c00f001c00b00000010008000000c000001400100240020004002000000c0000002000800a001c000003400000000000008001001c00300040000004
  | 41 => 0x30018003002c014002c00b0000000000000c0010000000000300340040000008000400900040020004000000000a00000030018003001c0000000009001800000040000000005000800300080010044000001c004002800000140010068002002c00b00140020014000000001800840050028002000000000280090008000001801c00000090010002000c001000000a000800200000000068005002800400000000010008000c00000040010000000000000d00080060000003000000f001800a000000000380000000000001800000240000018015006800000c0004000c0000000002000c001000c002000400000080000010000001c000001400000100010000006000000700340020000000000000000100040004000000002200180040004005000c0030004014000400000240020004006007c00c000c00000000090000007000c000000c00400240150010014001000b0000004000c000000800a0030001000c00500100000000003000400a0004000005800000000040024005000000800200090000007000c0020000000000c00100000030018000001400000100000008006000000200000050004001000000900300000004008000000000340010018000000800400180040000002002c00400580020000003001c00000000000004001000c001002400a001c00200000050054002000400500080000014006000400000040000010005000000000040030004015001000d00740010000000003c00d00040160000000000c00400000000000006003800900000020014005001800000040020004026000000000000000004007000c00b0014003009c00700300010014007000800300140000004004003000e0030019000000000000070040005001400700100000000006000c000000c002002801d001800000000000078004008800000040000000000002c009000c001007400100000000000004002c001000000100000010034000002c00d000800a0000003000000200140050024013000c000006c000000000000100000014000000c002000c00200000050000012003000a001000a00040120028001000400a000000000380020020001000000c003c009000800300000020088001001c0020000000000800000000050000004000c00100080180028004000400400080000000000002c0000050013000000f0034003001000500080040000000000c00000040000008001000400000000040008003000c00800000000000004003c0010000000001c0030000006000c00d000000e0004010001000e000000800180000028004000c0070000001000c00f0008000000000000040000000000002800400040050034004000000100040180004000000c000001800d00080040000002001c0000000001000400700000000008002
  | 42 => 0xb000400900200010024002001000600000020010004000c00000200000000004000c000000800d000000000080010004000000c00000380040018008001000000080010018002000800100000030000005002c00800400000008002001000200140000000003006800d000000000080010000002001000100000000004006001c0000004002001c00800100090014002002c0000018019005c000000c0030004006000400100000000010003001000b000000000080000010001000000200000010004003006400000040030010002000c002000c0000000000002c000006c006000400d00200030004025000c0040004000006000c00000000000004000401d00000000014002002400500a001d000800b00140030000003001400100080000000000000c013000800a000401a003000900240010050003000c00a003000600100020020005001400000040090000001000400500040020000000001c00000100020000000000000500300000000000005800000000020018004000000300240040028002001400a000000000000010000000000000000080070004003000800100240000004004000000100080030000002000c00e0000000000000b000001200040030004000002c00000000060004001001800300100050000000000000100000040004000004000f003401300080030010000003400000000090050004000c005000400100280040000004001c0000004001000800000740040024001000c0000008018001c010002400300000310010000000000400300000000000004c0030000001003800100000050014000000800000180030000000000400300000090000004000402200000030000000000c0070018007000c00d000000000140050004002002401200000070000003002400800000010020012002800000040030070001001c0000000000000400100000000004000002c003000c00500040070000003000c00100480030008004000801a0014009003c0010014001000400200080000028002002400400240030008004001c00000040090000001000c000000c0000000004000000000000020000000002400000280010064000002800a0004000003800700080000000003000c00000040080008003000400400080080008001000000400000000000000000800200240010038008000400b0020000001800200200000004001002000d0000000005800300000020040003002000500000000000010001c000000000b00ac00000000000064001002000c000800000000050040000000c000001800100100160008002000c000004000100040000000014000000400080000010001000800c0004000000c026000000200000000054000000000400000060008005000800500080000000006001800700000100048007001
  | 43 => 0x221200032ca00000ae3bfac3800001080000000000073e2f8a46ab260000000000000017767ed904000010b4cef163a9af0000000094400000000818000c9f80008e8000000000000000000811ae50000000078aa5ca0002f560000000000036800031720001fe81d400007b20c824f600000001cd0000320600021fcb9286f0343284053524509f580008ada94800000008841ccc1db2bd200000009ec1b0291c99661cb8eda61921d2bcb8000c4c80000000ba2cb828b0aee00003f81c26a7c003000000007838df4000000000010586f9a738591a428000000085200000000000000000000000002532b04ca9b252000129200000003080000000000000023ac000000000000000002ec600000005d78000a8280000138000bf49c48563254a0d2b07a8250b3c2668c769719cbc000142c0001e9e2e1a854bd308cc46980746e823985892e8800006700001b0cb9f305c2418c960000000038189e3d990f600000007f4a6e631b80000000000843800077c0000000000042a0000610800066f18cc6bb8a4c56a1d160000000b6e931800021f2000066e48728d8c639e809bd01264e685129c128449bb00004c8a7e0934970400000004b480006c00000cfb000044080000acacc00002f9200019560001c7acde000000000009712ace0500000b8198400238000b792cbe00012f62588000c4500000000000000250e00005065b180000002fbc00006e4b4c937c00033220001f1a494175400000008a58000000196e1bc80000000000000000099c9bfa3f112c09c2888c3e4a04c00000008958ac000000dc0dd2d4e000000000000000000f3c065310c0e32c342b98eb24f8a4c086a0000cd0929a56180000771bce0000000892049c656a26200000000000bdecffaeda0f2800098cb21650e31aa5eba3e07dc12349dd0000000000079c80f00000bd08f9800000000000002986c4211ec64519d05a815b0a97a7d44ff8000ae70ef8111a0e691b80008fc2dd2c49ad2868202880001d38a48879600000001f02f3e1518000cbeb22257caaea000000000000000000f2c5ac998e00000005599e9694225cc0c42c1893f80000003136000312c6af21380000da0a1a1c9800004ac0000220000000002a00000001bc423d246c000000066e89520348cb4165014a0000000cc98c5e00033769ef00800020001000000100000010008000002c000000c00700340120004003002000100000000004003000c0000040003002800f0000001004000100140060000004000800300000000004005003c00200000000000002001c0040040000000c0000000005000000000000190008007000c003000000300000000018007000000000000000008000000c00d00000010020003002000800040100040004000c001000c002000c00b00000030040005000400
  | 44 => 0x645c1b27a0000dfabb88000000039cb44a26a75d80005d381ec2fc9986a2819420001ed8cd9232a00019a04c3a9280000d2a672085c000279a97c9f06000298e1522b1c5802c960001144ab18000d081db6b8c9fc24728bd44cda09272a9cd87d9af1ac068ff88e32c123150df8644133823611320001482cce305e5ab1048ab88de49262c700d80000052120a4502af8c391ba67950000c0a999e60a80000003056b322c940002fee00000000002a5892e187c6438c1a7e92e14000000000019502610000000000003db07057785a800015b684ab2b86fb8d287d400000958f4e26e9b9e0000550000259a2e23302c472e9a11b97c26761622d042d4a7bd164478d2a5000000002062dc067585ae41f99b204e26b87e9844ca37a75630100006f29b120000000ccd2bae4ff0de01b100003c9140c000083200033444a700000002f006f9000000000000003184b73b19e0ea0000072800000032900002d3871d061059082cecbd0000c368dd64008000ce8961c00000000001cee0000000ad005b62f39c38216141a9131adc6421e3858a9480c9422eaa470ceccb3097a1fe98702ed000098e80000001192000000010222a6004b23e2aa03e074eab60bb81616155986c869891013f0cde1b59ae600011e8036084c0000672000000000016126480000000000042325de49b084442f0b6e000274800000000000000000000026400000000000000000000000007bc00000000b14000000094812be9f980000000000000271e00000004a8a478000000000000000000000000334c0003202b5e80002100dc22788000b0294dcb6920765e709980003370c0585b454e915200000007fa87e00ad80002dfa3d210f000074a0000000000048104b6a35934a57a01d200000000000eac0001b5200008caa7122707ac8000988a476776af68b760ac6510335632f2b14747919e0f38f3e3ba8a601e3028a5842ff6631969ea05ac4e36482dcc662da0c34148c3b1ae6062a9a1cc0c0ce00b1093676cb46e7eb227c5f402a21eb10da000000002d0000bf2800047195b2c8989160001b1e6671f2e00007700000000a80872a658000000000000002968bfe0000c1f296ab65ab508d72bd80001010acf0bfa7b28000670205a00024ec4c41b84000281e9b3a23005500005dba4220000000a7d00000002a1e0002a3e4dc800024c000023001de00020e4caf0170000000007c00007dca03200006180001a9062c0000000000000000007370000000000072da36070692ca8bd8000a7b87a068024924c19800cc7874a2d50c9c1e90dc0456ae2089a26d0b6a9ff200008f87620000a7088f20000000000090892a80000001b620000ee2c9c96d47c910ca0000000ceb0000000188090bae3e02181aad070000000000012c0000a0116b600000003240000a73242c00
  | 45 => 0x84800000000000001d0e00003069548000000062c00000006159168000000015883cc9ff3464000a34234e000004790720000ecc0001eba000000000000000000000000080a86a80007708000bd92eaeb841cc6b9d24f488380003741b88000248226200bc570a5180000000000018e14580003470000c93800000000000000000b60000000016501161b3621b800000023b8000018875180004350cca00000aab2c288620c075cbfc23a618a0ff00001c700a9b130c3600006e0245cbf30274ccf1c50298abfea55ac5c94aaeea1bf993200017843c48c066551240a34007c3a710ce7fe8000000000000003b80001f8e22cac3c6e32866c7d0f648b8022856d27cc00000002822c3a1582eb06222924b48925428d27b60002d44000000000027003161ca658694587a19eae000110800011480bb8000a5380000000000b36125a4c5800000027ae5782fc81a0ae7a0001d6cadc00002bc80002c78a9e0000000ab8000000000000001c3a4aca5003538000c1614b6bd7000001080000930000000000098b1614000000061e0000ab007424860000c090a8800007eeb3a0000b0300004e2000072c8224ae08f5ac999088244a25abf92ab017f0816855172c2c3996cceda6e41b88f7c44c10fe99e25305bf15fcae400000000000000109066a253400023dcb5c108e7381b46b788000000132a0000d4c63a0000295a0960000a500281c6877b8db21210404a6b991cbee92307e280007800000b0c992c4f8052c23b0fdc3ac0e38a239b18c0d9bcc0001a0e0e2a4326128ae8a42000000002d8b4ba4e00002042640082a905000008c00008f7811a0000000cb3800000000009c8260278795160000cdcce12cee00003c000010f40002d560039e706f223e800000004c003649568a8c000255655100000002e98000000000000000000000c41aad830f975298413a60000598366988e30c1f4678a0000000323c00021ee01880000000000487856e2271eac00008e8a771eec6208b1859e8000a459c8400033da9d6887a82d84a48e211e200000000002d0c0001dd0000054036c000000000000000cf4c5780000b1a8e4c978c2e000033a0002f205bb000039825c84bf041655baf8a19dace21cc0000ca8309ab8e275851d9c106a19448a34a55e89c8964c4085229ad84105250c6ab0414681eaa1f6b772a5c17925eebd2a566c492b1200000009c081c60001052ba0b0f009804cc995056691d0ec8000000028da0069f399e249e0186497288c3d292140002f14c590000c02972686b1c5696f1de2aecaccc58b035a54501fecf622ba000146e6b01da28c4983082809a65600000ba49f7ebfc9a9432198be1cd0000606995ecc829ca6ab80000002fc2000282a00019e00001bc600000000000000000319439f800002b0000ad1056826785cc7e11c
  | 46 => 0x9c64e3ab285520000877ae56944000036ab3e04a6331c7619edc3f3adae00000005e50abe1d90000bc600004b911b60000cc2baa00000002f6a1cb10363132a92a3c2cbc0d7b336123b42624900000a0b41e000319abc0a3a44db0000000141e8eea3d404fae5a9252516820b2140e1930c8010cae97f25a4000133ccbca9fa000000028832461e6000047f98ac7552b424d7a26e0659f0a0002b2e74510625f3800000b00000002e5c0a5800000000000000cd04f3a5e203d13d41f2adbea3980000000000d12000000016ba0000000000000000002d2000125271ca04ac9926be1d303a6a33880200011761dd2b8c9bf0eae96b2c68171abacc4480003c50000b418000000317e00009ec0002358000000057c00004b21352ce80302ce4306ea6b1630988118ecc111de62cadca327946a740152c3f2a9204d800003a200006908000000289600005885060b9e00000009c988be3d60e663f78d74b9e1dbc76480004faa0984df8c8c00000007662a7c0002bf45d90000619836654a003a7af00003eba1ca000144a5fb0faa25384b250aa9588598000c1d87e497603e8a9b807617287da44b0db8318252e5ba800000028580000000000189ac6da186748ac725ff97420000000000000000000c2b2e800069b257e9e8906e32c000065c12ae00000001de9a702c8000050400000002c1a9850b9857baefe63c21140002a660a50d620000000000009800000000001b5c2c0000000000000001a680000000ae21d1a44400004c904360002fa21591dfa2e5abd491692640001188c6e0d5a0000000000081e000070a33c26f00710810aa6800000000000000c8e000000003f000000000004b080004d21daa00016f601b80000001db0079a68c6ff00000001bb805180000002576508800000000009cf0000000315a0000000000000045d0000288ac920000ffc928000070d817e2ed8000000000047d27b498918c400007ae39580000000ed200002ac00024bc00005e8c902ecc7980cf24f91c66ad28eb83390000130a4860000000c8b2a8288a9e4224ea5749832040bb4a19c64f826a7baa6341748bc48a0892e64c2a3c7979be20001030a9e98de949323a5a1800000015227c10714bdb000004e8fac5c08f747ba2d924fb185e0001c182bb80009200254af680000000000000089ab4aa4586d808a000019526f408b66d6b3500d8964074293b40002a12016246600006b023c10768e4971cab5a1ae14633f86628502b8f0e3e45c2ae4000000000006fa01a01580002be67c88868437a7443f500000001a802fa0000000000045c8a165eeb0060c20000b2390b6579000029901320000000000267450d960c699845e09e901c93216cc00028c82b406540000ba648824001b32f1eb1f8e0e00027224198978779b3ba1d6000027d190a0b08aae7
  | 47 => 0x2b46000167e0001d263110000000000000011ce0002af400000004ae32be4b500004050000000064840e0000769006473a97c4c721a0c000143a0001c82553a04e11816e00000000ae38000069000000000005f783dc376270c612000056e075acb90e06bc1a35aab2000063900000000b1a12d000000000009e480000000000a182d605b2ac2a4ec9e48000113c6e3aee60001c5aa3a0e16bb7871a75eb346412811c61c8d7ca5ca4f20001248a600000c2e00004b122ce2222a560cb1018000000000006089df0000d100000cbf80001af800000000000580000000272e0000c5653c28da0002b743f180002da93be5d6000000024f0929ad364962dde000000030da694d0f33246b78000cd513dcc65909200000002a62bd600000000001e8400000000000f3a6fa8c24721800000000000003034caeb0140000000055acf656b15ea06b2ce03519ee6c93249a16c800028f800000000000000000126800074480000002ca6000012246a00006d38000aba237c00028560002d6a067aa60b89165eca8a2c6000000000009e60000000521832a17b9d5ccf981ea1099d2000018fcc11819cb63a8b250f22dca2611aa1f4020066e2a6a589b36a62e8cb200a8f9a5f601742ca82b4a0814fc2a10d9673d2f9c0001660000156a00018fea8c800000000000000472000290c00000000002f2c00014ca00005106b90000c629184730a36aafc0000322800053e0000219260000000000000000c61807a77626480003382000000000000000001552b3b0000000116c00000001fd99e8113800000000000000000000157c2f61de4000000017da73440aaaaec1d0000165adf00000000000000000018240002a10804a9e6bf4292e1f99aa6a8b854c9f7211c0002c2c00000004a50d4a0000000a71995ca59800040a000083080006b40000a0d0e4400000002ef80005400000c3b0000a768efa7013128c8a8000c8128bc6a6b07202c976a8fea7eaa759a2e74186b40000b9a93ba1682a4ab62bf68926392956c5dd146646f13a000012060002e8074aad006ae0000c120b0a53d000000000009b5882000009ce567288a87a2708cb40a521601fe2be215428c922f4302278800000000000ec4110a818000025ebdfb168c562b869a2a67e0001a4c9748000000000000000007349f74532043eace80009190000b5489c8756000000033b8b6c8000669111462e1aac0000000769a31054c8a2a60b83f2045b1be58287d88381dde7db1f620199f8ccb627d81df27e2a172d2052a87ba8a40df27e2070e4069ba4757ae9cca014647a3059a7e0a2a4cdeab5675d2178a191a84d14a78a2e11efea269c62b15975c7cc944e69da41cb1e8e929080b26822a2182871064a4980001f31f1800003be188236879f09142c2290e23bab5255700c6cf12c4a29c1
  | 48 => 0x303e329800000012961d1178606da664c2129b2208800092400001a7060679985ea34b1ea0000000083b9c8037d80000000000000000090c00009b80c7e00000002cbb38ca0f8b6896a13265b20000c5d1d4e00021a2b820000bd78cce62300008d50000a701ff45438000c73a77e0000e1e75a2bcc00009804f98a4000028c443b800000018c831e000000000007c705da8dd803273c02fe0759ba811480000001ce2000024452900000bc343e000000043c2668000236421c99fe0000ad4c96186e3e08c7030d32ec7b8adfa93f00004681fb8539b36c00010d284b98dc0ff11dc594aca2d01199a7de99da6c980003078000129aa909d082b09b10000b2ca554b340a0c3ba1a5607b9a601812fbe0000c1240f800074080007ed162e8d893782ac0000000285e1302ab49ad07e2493ab6634c0d4017c1f90a7cb1d80002e540001a360000d60b1e10d0000000000025d66f502c02068dba0000000a18800016b0fee69780000001c7600031420000000900922400000003030000bd600007b322281c61e32952274cb988000460a06c0001a8e48e0000c482c2255fb1a0268004c000328e9651eb8d0b0bbcb6080006bd80000000000708af38ba88000000069a463098e00013f80ea8000000066000000000000ece207124c664000000006849a180000000000c64a28c5968e74ceaa11e0000418bd88000522161e75580006bd1e8800034349b19c9a000000049f8f702e00baeba1301c2a92a98000000060a2c8407080009ca3282b378aa09eb3408c28000006c225802920b8ccaa910834800020e1aba214abc800032e85518000d0580002c180007390000d0302802632d720000000987884200005a6324a3d88af8e50629998c7422d64000000000000000001c5c36f80000002bb4000000063080000a4805689089968a02d76c2a868603f8000c89174cd0d87008e0000051e99ea80c005e991aa704a400000000d26afe33f01ffa39000028dc270102c6d798bc1169520a031a58595994687584f8632af3c5f50adc5af82a80908000000000000027f80000000135189407e800049b83328b308985a516784c491d4112b1a858106d29de064c3b79af8c9c1ed48198f90448b300865888e3d8b31a61891c404312de994141c000000000000000001c44c671fa05d200000000000033851ab7d86967569596b460000a290000000000000000007f1800000000000001cce6ee80000000000771a4064498000056917ccbf1a6400000007020a7ac142b5e2928000c38a20c4300c0a0e63424b45092c0000808000000083329d8629298c737a8c0c76a99c8b5029c27a306a24a80006748000000266c49c2df2000000000030fa00000000000000c90a3405a0000000025500002328000133400000000002c80000030e000336626e0184
  | 49 => 0x8a22000056f9fc4652aaf25efafa4cf78b285c5ad867be00228c182f4340800020507c2000000074400004be8ddc00000000000000b7aa9aab3f800000000004d500008b98d9caa513d0b112762ccea40e4428dd28d4914a2f905be4fc9c42698800009200000001a38a038000000000000000200cc00008db80005d006023840f7e8e1ab948782b921288e7a0000000ba32a3600006f666d91986df3292713970e5272226a41800010300000000000be6000014c80000002ec23b424debe380000f997f826f94f228c2e2e5e9000084fa9d47a09a300000f380000bb296080000000000b46ac400000000000000037f049496995a66fe000071e000030091fa74c0000000269067512f269fa16000023c40001012ae680000001bfe0000ccc0000a809f100001a62f0e0000f7233593900000000cd4800000011c2000000018c1bb04af0000c080000baf0f1c98f0fb8bce8d8a4f2865215c1c540c3062e00004a852b000014000000000000ae90f50be780000000000000037200031349610b4e3cc913a0000d9400025e670814a66fd28ee9910004ab085309a4b0620001ac83f6ab3800022fe3b9890e7d5230aca686bc8ad222400003e4000010e0001c5800022b8cff189056a8000bd41ae200018e08518000c44066c02531802ab00000000000b329e4e70900009ac80000003396000000045897ac186a2b0277000018780000001816acd95d6ab98000a4c000093629a800000000000298c6c048276a2824807a7da4a3a76a4e119ee5018e261838a109182618000058665113024e0000000023c800014b00000000000000000000000002682c3f000026b237401b00000001b56a53173641080000000000c0b0f0ea790e68000248cd140000499ad7ea4125320000000000000057411381ac8000528000070a80008aaa15600000000000000a6200000000000000000000000004d0800000000000002f7400000000000000000000055400001218000000130400017b200006a6000000000000009a80b4053ba58c3109a0a8b080000002e34000000020d800000000000be80003a9203c0002c04000000000004380002c280fb8000000000034903f04251b6ec0f170c000112800013c82b08fa63071c0c8940ceea85800000000000000000000017a6432e9678b074042984780001d960000000030000000000002c718e200026d200000000001166117263800021845bf9a981a531e4c8305380000e5c34789f227bab0239200000e7a2aeb871f0268e80008d411e40000e58000105c0e59c9c250a3660e218a800029d2c588f860000000ad32d948c9966e8f180005c50a469b50000000000000021dc3b08136b2a9806a3d000010886e0000272a8f280820002de0cd78000b530000a5881f8000000077b00000002be20002e66c28b1b29b7
  | 50 => 0x9a4564ab0c7c0001a28c8e00008400a9000015845f58000ac010cc970aad4122af76000325cba4071e32f9180000000000004be0000000385141606633dc767087026080000248000a6f000050d1f3e04b000000000003e9000000002f89a92e026d0208640d105a1d500000002af6b0d80000001cf89f20c0e134949261500000001000acd04668e70180c2200003bdb3304da0dd4539150a94e8bdcb59aaa4cc4a3da25f800016e8000b83800065200b8b9384340001934000000000032680169e640000000d11250c13a80000f7ac5eb4f8b829212f822d980009bd96b40000000000000000000000000e6c000084a00023c0000314012e0d2268801ba00007f80000000ae633ae5f28000c6300000000000af7aba0b5731a69488f3000017c60002dfe67c84fa3cd80e800002fc000062a83c196404f0000a629b5000000002410d36000000008ca74a68d000000020ce000000063eaa964628000adb8150ad2078247baa5408200006dd2e449a68edc13b0db413d00007871d90000274e08523ce000059e0001768a6080009a0087c00015600002be8bba224c000000086280000002edc0001068000083e9a60b24a5908f659c00006970000bfa979ab960000805000074fa02e00000000001e3600000380002e76bf128a600029fc26b805c0000000000000082c8ffe2a6ac9cc09a65a1ef95541d8b2889eaaa384e3070600013fa0000b524618b4c000305a0000b604132b3e0000000000000060700002b6b1c4cf496f200010966418000a5284447fc27146a8267c0002bbc000070247333c0951a6405798df0704968a1b780000000558a820000c2d9ad86e60000000224018ca7961a91d447e6000062d9a1a58827fa28e800004c00008d5ad6c00022220000000000153040200000000f0099992165e800004c73422b1983140000000b1b000083b0000af0b3100001dcc1e387dc6d50bac83d068c00023364b6adec0000000000286c0001692a0b2cda0001792cb70000d1b2c300002b58000287a628911a782800000000000fd1602000066635595680000000c10000000015183fd80004c68a0a85e9a2c53d80008b88b0400000000002cc287980004d686c60002ed805da6368bea97e000337200013a280a00000001c9e9fc800020f00000768000c358528000241a131af701370680bc59daea78aa5200002ec204848c39913e803280005f6a85069d0ae4000333200000001ab911e0002e460000000001a5ae7da060a0000ab45dc0328000000000000000001b1a8e8853630c9154c8d9be8bea16368b2b13c5d5895ccc21e040000bc00000780523800053b0de80000bf63722a306d08000c70985a0150000b8daf6044bb0920000000439800000000009b0a1189600c18d0384e200028a28cc861626a961835b0234cac0ee0662077
  | 51 => 0xea9e50000cdd17461fb00ea8370554cd3af5a16e33ca8fd15cc64e0e9abb399164bb80001bb81b2c7e1bbc00020d00000000b5a12fe65d9120bbc8000b920d82bc4000000029ce14701a60002f24d0280004b1aaa2ba3b398000109e5278e08c7b059c8c1338e0000000000000000000000bd8a321a40000281997c000094672d000000009a4c53a9c88a280005e62914823800035c00003d00000378a382c2f000000000006b4ae5e3000d7600003fab71af66cb20ba0aaf8000627052085b082810b800000022d05768000321000000000000000000000000000011d600000003e300005f48190c748000a5baa725a39f422fd0000000210cbae800093690205c78abc4768f940a181284ef0c40556018a00026ea3618456a200aa6000150800000001200000a3b0b6232da4ce17899ae00004aa730000021d80003e6053c000320ac6208bc000000006baf9a000311635fa5baba90240c0a209e4d32f4602d80000000000000000000000000001426012253c3d7800052124dc0000000a12802458a19e6000000079f922e0e10000175000000000727cd000000003228a793c062610703120d5cb5e185271306fc5c820d80002d3a4581f800000000c9b00001711a5000015d4ada80009c7000000000008fb00004ae80008500000560a2341770000afb0000a5e8a0e0001c7e00009da5a61f9cd1691b474b137a76300005f930ac729213000000c4583b0ca6eb923a25a04d0000008ca5097e83b5a5029510000000177c8b6192423981c877d3086a89a56c21e344e905aaa8000286e4fd2fd63e800005f71b6a3d22d5aa1f00000cd800000000000000bc6caa0f527860440a0a0f0c4cf9f1487e037811434388aa00000000000000000065e3328526b3fa09e1d52aa290c66d90902000165400021ba5720000000000019eaec81508fe447f24a4b798cf84088000240000092b8d0e9fd9732ce7a9fe0002bf60000000a2b8d6670288c6b64042400030ea7f5a4b428b2f0800000000001de842e00009e6170a99aa63e000233800000009e090f8a8500007aa15407500a6a00020be0000000ad531e214a80000d514b27eeb07e2faab64ac8a0ba2802642c4e9f380aea558ac2a2acbf519f60000cfa0002fceac624e424d181400019a6c71820acf380000000000000000026701bc535b1d604929363948eb43aa0d64220a67a0d08a1a774958a484a4d0046041e000306410808e48268f2009baee42bd92e050c30c059a000019900007a8b17c700857478c139407f00003a515ec23f9d4890200000000000bfd2c886eda20691221162f4aa8c000056c9db000016f08d61049968b90a7c2b338d2e71b2cfa95928f2a6c1b9609c9efc558a6f2c87a1d8c1e238a086ae640001994000239ab2280008c09f7c8cf87d608a800000021280000d109d
  | 52 => 0xb5aa20a5d0ab800004325d82eb20000f1a4d910321f20ebc8448000000000046ca5900000000000000029f0000000149052fabc44d9932031b000000029d08fb8624723af363a980005378fbe00020c600029940d4abaa4d02ec00000000000342e5c61822000000030e0000000000011eab260440000000183eb8300003260000993800072ea1627be87389429b942d90920b62882e0000c2660200001610000cf90d484b310c40000000c5e00007de064a0000d20ab4800000029460002ea60000eee0d38e8000003c622c000017980000000000390241868c97c0000042c80aa1c467c1bac00034000000000000000070a110600007762cd150cc0080006258b6c08b0646393a0ac785906a1b615067758000000034c0000ba80001a1eacc97f4904138698c1024000040e00000009c5acf0cd685a43c18000be58bcc4b98ab238820a871bb1ba2a8b15227e90a4b4224962278544997261647e2a068fcb36295e1df200027f00000dc400001340e80000000139e0002d26386801073f278c3c20fd0803adb405a284c03ca832bcd2c1c26287c6a9390ba71801005e0819a000304c6e728b46952a78b4d2a2a6f700005c223480000000693b286000312a00024acc8cac9e2d280003a8800000004cea7a89a20002fe643f0000b5d2d840000000000000000002e20002c0000015743d080000000000000000000000000000000707800023f00009b7aba20000000b4f08848a8000000016e86d6000088810ec000320e0002b1003e800000021e2abf9402812039a0001ca0000058ec9289749e985aaaa00a72c4013c696a978abd500007f2a1365080ba40002050000000000013da0002a4a8c5000000000009c927be48f000076eb1e839c8e1c60d0e5ecf21a2277e0e225920000bd0000000032da5289e8e0fb292a6ac076e6cc8000782000086c91940000000a5c00000003468000063cac7831c48b000000009d684b228e9030a2e00000009ee064e3ef336085d09b050133c27002540788956479717807669cfe000221ea5f16340918000000295200006dac9d00000760000b732bea43708660000000707009600015720000000319a36c3bc2a64a09aac4170000000000000000000000284e00012740000000000000000000000002f900000000000234444700000000000000097611880006900a445260454cc195384aa0ac82bc000000012e26c389f01fd000000020700000000000000070180003738000000000095aafae000136a17421f4000293479d00004ac0000331000082400003f20a96c9100004540c4e0000ea062d00000000000000000051100000000000b70a5b26dfa76804114707942b0e438aaf073da3cc4f4a1ceabb31caa56800000000009be93cc9a59bf20002e004b714d07d78716c843406ada3470032031267d12
  | 53 => 0x9f2a46200000005f300000002cc655e939800000006351e98c138000000224a4ee978e000267600006a20001ed0000028c96d997a000000000000007f900000002a0e000093cb218000000000000009cc000092200000008bc022e000316a0000000000000044600009d480000000000a6103ae0001c16aaf000000012680000000835a5921d980007bb800000000008df8000000104651800003508000000243883f800095f0d68000190200020640000da652f25ec1850000261a1067d2114c65029020001ab60000284000337c53627500001f3c3d5a19e0000000cdf800000026cc00000000ef343a7d00000633a58a5022dac01c17000000000a93181066b0d32000184e4809b2a00008de59ca264879112a0001f92000104e00030c45b0800076114c088d9fce1b2800083512b45a586c00000c46000000000007726141a12bd10000b16b1fc00006340003392000000019a80e2a0513924e08000000000039c342800011a4000000000024f82ec000000018c00f11a2a000000000000001ceb45e7ea9e4457e1f9a71f208871a8000000000089e800076280400000a780003068a4f9f0c0002a3a0000000a503082941317a712b0a6000000098382de0001b0a4491e4068580006f02284bfa14fe393008aba2a378cf1a6ca84427700001d9440f00000001f581df800003324c43db03c2773a1fa2fba1cc679273003ba2d68c38358511b2280dd927a97d8e187c3a3723e2a80000000000001a9622b8fcc00005a2000065c000000073e8000000223c0000ac400008a89d900007248ab600000000000000000221c5dcae6a4cb09486c8057a92700008488eec0000000000000081a1a48000145a0751f4466d173000000000e92036c08a01a6a330e60450dbc6b5a4b23140000c772c48d19a01694b0000000000000027801ca0000998ac524c2000058cad88c5da8fe396af2839aa67000029384098000000180e75f9f2c03680006e2800082d000086316da9c418eebde06c218e800000004880ae00006f60000000000000000000358000549800000000000000a3c0ce034638b24e2000079279b20e850b89b44f10b4463980000c811f07fe0000aa2050ea9d2688000000000017780000cfc5f817b400008a6000338a5d6a06e939b212000295c00019a26e412b68ea0760c75310e1c7243c760a2bcc25a4365a984ba00027a4000000000000004f5b1f0ae9a0346f8114e000012082b93a878fa44600020801fa86f40000feaae292a6000000000000002a520581779242000065e53e800047ca7e40001376c7d8e988f8b170c8011368bb84da000146c8ec8000ac22ffe84980001c210f2ccb8046a1d055c0002180ac5b25a0000f10cab2b727c7a4520000000468b28447407f2caaa17c0001b282d70b4600018040002bf2000262a7
  | 54 => 0x72300004c7b2e61d580000fe0cc600031c045e8000000280a09a05081909208bbe85148bb2c506a280000002e40842827e000093800000005b4b0ee85497c860c80000002dc41ba0000341800075328a800020e2000000000000003830fc28e52fa041100000d1233c5229bb27958000c33b3f4d150000000033444100008a634189be20b03dd8dde5960886cb1800052e8000be00000000088a355084e356261c772aef0000106c6710000000000040e8f447d914b80e4000036300000000000000000000025b4345855e18e2db005333ea8eb84f000030f815e1d70195a62ea1a96e4b1da8c628a1876b6884e665f8992546a604aa98000135800000023f84ca09d8000000000011ea00029a6cbe1fc83e22b2470c1e3ac3200000000000b85951200000000002134297b1b49332932132b230b4904c48850c3a540ac0695b828e86400009ec8da250291f642b03ea6840000000188a0000bc2ba180003d700005ea800041ea47c037800000000000000000000000030b00be2728000cd28d7a54f800000000001e68b5e86d09fe22929e8bbd31e6941814ea402d3012400002ff80282bd258e334a87232922662eea30816091e0414183a81e07207321116c2723209d78a26214110c00030be4bc16e6cbab0107ac000012800000c6abee1d4a132ccf83000f5a3344d3976200016666060000830301226527861ed9a88b191fbc4270be6c6b80000001d34c9b80006b1000000000005d28000000139cbc99812a1fafe2b9a3462aed9826a9d8000178119cc581db875ca2c000033cc4e913967e5afdcb6daa8e76809fc608224e70f338049a847c76d023c4449a825fb800081f1b304aaa08400000000002c900001ddcb9c80003462f4eb0bae1e9028a667a400000000106b3a800000000009b2037ca5422c85ef00006d20b3e48300005528bca012a43aa278e0031925f83bf15880000000d158000aa112f4cbb88fa60b01a85a88fe249cb0b29c6a3b61c495c0ac681b823a8e3046e2a6267f076a00030ae53833e28d2a99242c0000107165c6ba895e32e0000781abe468f147e6d9a8942909c907a2822685680000002c245a921085d4041464ea3c29e3800000000000c7859283f0dcc0002e04b72046c000000000013323e0232e0e00000beb14280000ff28741a9200000000000000000000063b00000000000211808826d8fb40001260cadb05268981ccb35af040689dfe2e4100a37b9e5ac5b928c5bc000033dab0c36100007c9a5e8ab79d6a80e15bac53329e6d30000bf60e7c0af000000000000000e6e000000026cacb6000266e0002188000114256602d080b05ec7358ce8ca61ec29a71536b8b000000019220588000adea2f217204bc81e9556417a31e00000000002468b4383b6000000025800000000000000000000000000000
  | 55 => 0x2adc000326a000000054aa41200000007dd8b2c08d80000960000000000024300000000000242a5fa8b48000426000015fb11ac518000000276e00000000000b9c000000081780004a92f94173b00800025e08fa89f6c0e0000000257aa8904748ff194e957000000034600000ef20002ec4407865a72c000000000083c88000a9095fe09380000000dca3d51c4600003f698980000001e621b38da80db8000b8c001683c9936ae78000b7e12007f3000069a8c4a5cab0e0ce199c25d114ea8512d505e3185ca119c9425c3276cbd9456070063e7d8049800d00005130000aea1d622bf832683282642cea7c00001d7c46b000000000000001aa850c8000247ab7e00017eabc4b4720001fe6cda1724947b262bc2a8129dda59c5f8800000000181ae8000af70000000025000018365478000000000000032487ea0adeb9300000001ef252b9a3e65d036c0001e141ff31fa7cc199619e147208e18a08913080c6b07b85b60000ce7003e56528704d7186089e000000000000000b7c00006740a900001ec80000001d1c7b79c3e38ab0908a6a1c800005900b80476b2933f648c80367751086bf02cf47d598da63d2cf25a71ebe1c88a1881d0f84baaa6b000004f20a69e4cb7b8a7489daca8aa196764f0966a099a15079a9d240000a86000000000012d82b38d9e000160605aac600001e2e5330a5a7540d8e00008067f406c800019dcc109f28a80206a127825ad0c8af800000006811d600000000000177a64a0000000295e79eb45823233d483107de82f00d0287867cbb400008fdb2d2ae023964392c4c3c98000568ad9a21f8662344b1a46dd81120001f9480400008c000008d78000a3f00008ff957632b000000022c434297b60000dec000000049105d60a7800086c16bc0ba8468bec80006890b1000008ce5038000bc8a04400031bc3b5000000030ba13fa83014f8000451b2ae00032180000b22966039400021b80000000279033c00000002b899aa5149abe252926214300000000000154800000009560000000000000061a07908c581b4a1e1c3260e13f0b1b80002e500009a898020ed0aea00024ca6bb164e635a3e400014e26ac860cbfb16ee1628dea0000000275000000026282fe000078f207eade18d052a34421cf2586b2b89e0d13313e02711ae2892f8641d00e486f0000791a3309703166536a92c35bb0c60f40166ca5a56045792f80002ebe0000000000000000000006cb800093d80003411918000340200019841569164cc30000401093200000000c100006b090e842824bea7b21765a400000b5800088e000000000005988dda05f00000000000a9195bc000000038bade8000042839d800007d86ea4c2b29432eb0d460791b0234a0fac950eb6000242687c00008088262c27aafc00031ee9178f16000259e3bd2d1e
  | 56 => 0xa00019988c880002d406aabdb8c22541200c00008c2897342a6ce8e0a3f000000000000000000000030c2500000088c80001c9b13800000007462e9e8000000000015ec000000216aab643e800000000000001caea0704ee12599cec3cad581cc894009d8ae0bbb80006530fb270b8f6e000096c19f80003ec038e4cb80002b6000093e80001d2000018da47000000001e9a51a55e223e25a9b4453380001bb000057d16e26fd8ca20b98000531800077d853420d0d80cfa184c00021c07c00000cbc00000878000a870000578a61aa9f915c9471766318abcad1180008b92c829621af279b94b42971ea4c8b9fc0ced0a12b3f237acc391585b4107801e047040581821f5058c3e89f5c320278442aada888127de510aa4823433a4c3a21a4cd7247a6ad119a340293c5ec00b0a5e214213d9c8a4fd83fe3ca0e02bdf01f24f78a6c8ba027ccb1217200003b2c5700149a10400002a5da000264aa2e80e600000002bf000015ca9e02c080000001ff685b8aca7350000000329c00009bc910a01c0000ee438e837a5a6a1ec4cc2e7e61614545642ab21a80ff4cc604300001474137812e0002b7c10680000000000000080e00015a45db275c0000000000000060302220001ada1a48d5eb18800074c80001898b1200000000002dd00000000bf80e429012c585a323bc08f8000ce52a0400000000000000b660000a86001ac078000a6619040001d9ecf5823a0000000b8880007b80000000000000029be4eb1f3629d9688880304493a800000000006b180000872ce66cf0000b9c2db8000000000022fc9dc8b0c8a180005e41cf2b1d19de2288218b63000063aa21a000000000031d033680008529c5e45f800067e25f400025feb150000000242400008569c620601ed23b4530925e93a0202acb0d140002e6c000071046fb0a88158e900b2ac6a0001de08570ffa1fa0000000289200031cc75b803c00000000000000000000000008c41ef26da00000008609a7c000000000031e094f8000a040704c37800000011d80000c16a6d2a9c0001b2400016aa36b089600028ca907852e656129e403971a3fa32b425682529ba1c96968abc68378000b82800002780008b79afa8321a18a08acd45e580000002ed40681c52c8700000001f4aae1000000033b2000000058e01e80000000000082600009a8bca80000000c9a96e000000000000000000750b03a3a1af0c0000aec00016dc8ec157021a8e36c128000bcc2ab800030fe7b0000019009f80000000000239ea2403923aeae12000000042f936200000000000000000010aaef973c1e5069ebed000000000000000000564800000000005ac0bb80002d1633200000c601ce6ba01022960f68a6e12d6492ad020001178aab21fe5cf9280a2080000000000870951000000004748402c250144362
  | 57 => 0xb2609ccb3ee9828a8a8a5000000000000848000cc28b78a6928f8bf7aa220d0228800002be428a3d000000005fd9236b51854a8a7000056b8000000191e63e000001f80009ea28b61ae191a000000000030a400025389aa1fd8000149600000000000000000046a83e0000124aa44809ad9c00025be000043a00000000000000000209c0000000bab2b063c10d780001b0600003480002d04566a4b00000f2e0001b7a3a31a4a6a91ae05c881e4cd0280600000000000d0800026528ce8c7200019fa5e794d212ba8363b016ce6732b6c3718e127aa808496589286b51dc81ec08e085c18f25a0800000027120001534ab3032e9100b5aa5d99ec2740e960f4800088217f2a8d1cca78091960b5065848a800033f9d3cbb29ca2ad3a5cebbd9f8605c80000002260000000021b00004a100006c8a9a038a2164c6427e86ed27ee65893588c700000000e2400000001e200005990000c031d78a8a108400009d200000008292a5a000000059d18d80002bd00000000000000000013aa13911e6bae1dea7d3152e556ac260000caa22b17fa2fb32de93530b45ff01e09279a78259aeb4bec1e0c8c3219a72208e25531c347960958808110022d2254806219414e922288b0a025ee1b4a30a10d841f21b6401800045bac02760051e0b900008d30e8e79e006085380906cf8b58a68a6acc23a54e39e306654715c4ccb0ca07100000b7f000000000006b2a6120002cd29821f6aa7e075ea2a80005a100000000000a1483ba69b800000017a8000102e00000009960c68083800000000009a98000000078a0000000997b08a000000000010d63f6000000000000001fa200022020000bc8188a8f62952a40b081f087412aba4ee1a062e48448379b46a58fa9f6316ad42c26146274da5625bd14500789a4687180000000000660264c61d2434403284200020f6a1d9d2eca28000170b31657e8000000000059328cc5b100008a480004838b7290f9e1000006e637fafa63a09b08572801e339aef8b2b1fdea273220c3d28e2201050a014173a8481fee0ab83da0841eb68efa70ebcc80000003150863966c4640000000217eb69934600025706c7279e7a500000590000cf42b5c48680000000000000191200015d820e85fa79295242552f4291f80000000b8c2b58000b1080a24200000cac86acc7ca8081ad8000000142484680004bb171087680007c427a03f482040031acc2a3a0545e8b2c09cd8a48b6f29de4d5a77a000172800018920002cdc92a000060f00000002c165ab89500000000c5593ee3ca800000019ca935a104b5506440000746000000000025728189fbe6a883e200000006949276829800057d98860001a9cb67b45c65c8f0ac86a03eaa7800027a96fa000000000000004d40000b8a000000000006649f523dea8e000000000000ea
  | 58 => 0x4a197a65be000042ba5360001aaa2251e769ff91562d2291a7d6b16c15f32a464985fe00031a23cd2bb0c012ddaa2100007fb00000000bd62f8274051e2bfc4721846bdc8b56bd22cf83c780002eab06c2cc0000882a74600033580001e2000017f0092800000000000000000000086292e9b140000000c0c8000000000000000006da0b32ca300008ac9ece0741a5a05b8000bd4879e0001eda0d5a73e73b0000ba806d45f9800025c9fae743296cd04ad1c168314a0002d489a7806acc5334820012e81f4a10287a89c27052c0e9111b869fd09de61e82c8c4b8a820bca8be6eaa5b0857ad5ebe300006e6893e00025d40001b920000000c5500004ed8fec1d39b6cb1f0000a641bec69c80008be00007a6a002430a8b848f8000000040600031229ee8afa49f25d02241fda00021240000e460002e940e08000000285a0000000b75a1d43a280002aa800064f0000000026c69130184d106dc46e80000002ffa7b4880c33aa2a20001246571b39a72f9ffcbf199820002c1e94a0ebe000000036ba42ac23082470b047e6c5a4b600000001761f2a0001afecea0f600f52216000248ec41116a00032d65b010ea00000005aa0000000000000004e0915299a3388000000000000000009aaabfa00000ec00000000000000322091c8c60a0489184e80000000b5f00000ec2df430f0000c9e16d60001bc2369000000030b0c51155e1f3a8fa0000000563800083a82a00000000c8200000001af000000000000cd44180c7a89f9c0e8022efc00000008ea977e00000000000000000186a0001b726c131ea6211e2435a896e0000000a6e80003170a4e0000000000254231d0f02000068e65a80005cd232c5822c9a00026d86e08a7e000244a30500002dd80006bf01bea12167c9d82afa0002f7a9c1a4a200000005cb8000000000072a203a634a5a06a78e3c8090d3aa6580001e8a38401480000002ce4035000000026ba00005f23f9a8ea0000000000000000026aeb0f800032a009a6e8afaa9d50000000000000000009cb000051f0f6a2e280000000bda000213c3300316c1508dc981945e02e800035c8000979180a0002b960000000000000000027d2000178800000001a2af1c000000000000008f58000573801c27192889f1800000006880000c5266f93b02e386f864a830a48a318207d2c0800000004b380000000000000033e00000000eb0000913acc40002514d06a6c00002a2cd0c113ecb8ad0a00018f61b42ad0000000089b00005310000aaaa158a0f2370215000030aabe000000000000db63512ffc000000021d1cb87369b387a9a91222e832461f800022e000000025dc6c41fb2050800000000001aa0000a6780003542eecc0b8000be131182b48918a581a7a8648ed8c42acb43a7a1a0420a4c236625f0c3dab203f58e32a0
  | 59 => 0x1ace3a13388b282918786800082a8000000061c395000000000004320000ad680004228a6e0000b38b231cc43ea1b2c9ce80000000000000219834f92a0ab28000931800000002904a084640000000a3500000df83c8b8e800000033be1492ed63b2a25e4151210bee0b740000a38b4b0b3600007a873a1d664c5000053a16de0002bced1d0000b9b85760001dc00000000000000088b800059280006cd10b29498e34853073676b2b3066c22da05b138a0000f4c0daaeb60002e2a789800028520a200000a6cb50000000000000996b8011000000028c2c8d248a0aa8000752ad621f1000000000007b11f120002b760b69f6ecec000095a1dfc0e895dca55000064b943e000290a79a0000000056a4dd000000000001848000b869f4e00018ae00027d0ab680002ae8cd858f0000000200ac37020cb052656c95a68e3e5a08c4a295d2346ae52c7f800054f00000000a687a704c88e385f422488480001bd247027ec9980d3c42695a02dc11342fc0d90abb9a02b751cac3e7b0cc6f59d8e4b40f4643820523e718447ad133a000035c00000000002488c18223a0002bc00001e5284e88da00000008948e0476f891a1c9097c0000000a9b1fdc05e00003549ee43eeb1de7c5ab2acb0aa1ab5000008d18c94000110ec0380000001dc41499bbe00003700000000000002e6fc000000002e800000000d4065085a89c40f61f200001ef69532c4600008aa50480007592838398b0d206485b00b30c1000000009e42fb6000000022000007e7a9440000000000054e6dc173803e05f80631bdaa9a3414c521bde000145ca479f3a1e18f8e41594148d3800081c80000002a0c5c480000000000000122621800009e70000000000009c2bbac9f1b781e70000a2b0000000293a000025c2350000ce9a5127f5282ec4787f07a4a05c1029a140000acc00000005678000000283a86f86008c68a9c4959ec6a6d80009bf8bfcaa80f18d12885ea068000000042ab440000000000000026ee0000000b8980000001fb000000001da000000000001410b421360000cdb812a00000000858b16000000000000007f80f7800026e2000078489d000000025ea00000000001ffe4db8d348368000000070c4dc00004eb8fb619a2d6e054b3f2000000000000000000b7ab861ce6000082c05700000000000b2e000000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8f487441654840196ee8882ca908032d1d1105952100679b8220b2a4200c3d75d5364484070fd0b39ec8908021f61673d91210051f42c81b224200ab581903644840156b02206c8908033cdc110d91210075920221b2242018f78744264484039e4e0884c8908033c5c1109912101c3f43eeab224200c7710dd56448401878ebba2c8908031d1d771591210043fc2ae0b22420387c855c1644840117f08b82c89080237e0d70591210046e41ae0b2242008ef825c164484031e90e882c8908031ddd5105912158e3a3aa20b224200cf370441644840117f0eb20c8908028f21564191210845e422ea32242108bc845c0644840147d0b200c890802ad606401912100e79382203224200cf1704406448401d6480880c8908028f61365951210043fc2aecaa242008bf845d954484011ef02bb2a890802b360830d8d210056ac0861b1a4201cf27044363484019e2e0886c690803b40c110d8d2101c3fc3aeb31a4200c77105d6634840187ceb3a4c6908030f5d67498d210065b884e931a4200c3e755d2634840187aeaba4c6908032dc417498d21006573a2e531a420387e85dc263484010fb0bb84c6908422fa137098d210045ec26e131a42018f78744263485638ecea884c6908031d5d51098d210065b3a22131a4200cb57444263484019e2e0884c6908063d2077058d210043fc2ae0b1a420387c855c1634840117f08b82c6908422f2117058d210046fc1ae0b1a42008ef825c163484031e90e882c6908033cdc11058d2100e7838220b1a42008df8758c634840117f08ba8c6908422f2117518d210043fc2ae831a420387c855d0634856159b05398c690802b56063018d210046ec386031a4200acd820c063484019e6e0880c690803b40c11018d210845f426ed29a42008bd84dda534842117d093b2a6908022f6127654d210045fc22eca9a42108bc845d953484011ef02bb2a6908023ee017654d2100c7c402eca9a420087e87d95534840187eca3a2a6908cf0f1947454d210043fc2aeda1a420387c855db434842117908bb6869080e1fa177690d210043ec2eed21a42008ed82dda43484070fd0b3b286908021f6167650d210043fc2aeca1a420387c855d943484011ef02bb286908023ee017650d2100c7c402eca1a42008be87d914348401878ebb2286908030f1d46450d2101476432e421a42058f4865c443484010ff0eb26a49080e1f21d64d492101c3f43cc7a92420087d8798f524840147d0931ea4908028f61263d492116536c16caa924200c7765dc552484010ff0eb22a49080e1f21d645492101c3f43cc6a92420087d8798d524840147d0931aa4908028f612635492102d3b436e2a92422cc7676dc55248421968c8b8e84908b31b1d9525092100716322a4a12422cc6c765493248401c98c6a9264908063da1b714c921
  | 1 => 0x8eda9264988179318b524c93102e2e3b2a49926205e4c62549324c4078eced3ae62988fb1d9d975cc5311f6ab39aeb98a6205c7676d4b314c40b0fd0f282cb908028fa1250597210051ec24a0b2e4200a758194165c84018f6e1282cb908061f21d505972100e7938220b2e4200cf17044165c8401ce4a0882cb908039c54110597210061fba4e8b2e4200a77815d165c840187ae83a2cb9080317dce73597210051fc22e6b2e4200a3c845cd65c84014ef02b9acb908029ee0173597210053c402e6b2e4200a3e849c165c840147b09382cb908b29da0670597210053ac0ce0b2e4200c7b709c165c84594ed02382cb908029d60470597210043f43c80b2e420087d8790165c84594ed03202cb908029d60640597211653b40880b2e4200a758110165c84594ed03182cb908029d60630597210043f43860b2e420087d870c165c840147d08182cb908028f610305972102d3741060b2e4200a6d820c165c84594ed02182cb908029d60430597215a63bc3a20b2e42b3c748744165c845f8eee4882cb908af1d5c910597211653bc0220b2e422ce738044165c8401ce4e0882cb908039c5c110597210073920220b2e4200e714044165c8401ce660882cb908039c0c110597215973910220b2e42b2e712044165c84010ff0ab9cc99080e1f215739932102c5e422e73264201cf27044264c84019e2e0884c990803ac501109932101c3f428e6b26420087d851cd64c84031790ea02c9908073c9c1105932100678b8220b264200eb14044164c840b0ff0eb2ca9908028fe11659532102c3e43acaaa64210a3c8459554c84598e8e2b2aa9908021fe157498f2101c3e42ae931e42018dd87cc263c84019e6e0884c7908073c1c11098f21007699822131e42018dc874c163c84019e6e0882c7908073c1c11058f210076998220b1e420587f8759653c84014bf06b2ca7908161f2177654f210045fc22eca9e42108bc845d953c84011f700bb2a7908063e2017654f2102c3e43acaa9e422cc747159553c847587ccbba2a7908030f5977454f2119e1f328e8a9e4200c3d651d153c840b1bf0eb1e87908162fe1d6490f2101c3e42eeca1e420087f855d943c84070f90abb287908023ee017650f2100c7c402eca1e420087d86dd543c84010fd0eb2a87908021f21d6550f2101c3f42aec21e420087f865d443c84010ff0eb2887908021f61d6510f2102c6ec3cc621e4200a3e8494365484014eb03286ca908033cdc110d95210073928221b2a4200c3c651d1654840187ea5ba2ca908030f54b74595210065b886e8b2a4200c3f751d1654840187ea43a2ca908030f54874595210061f288e8b2a4200c3c511d1654840196e203a2ca908032d1d371595210043fc2ae0b2a42008bf845c1654842117908b82ca9080237e0d70595210046e41ae0b2a4201
  | 2 => 0xb6450b310045f438c8a166200c7665dc542cc4070fd0b3b085988021f6167610b3102c77414ec216620387e855d842cc4010ff0cba885988021fe1d6510b310043ec3aca21662008bf8759042cc4051bb0d398859893b175da65ccb311f62ebb2cb99662058dd8719332cc401c9acb31665988029761b52ccb3102e2ebb6a59966200a5f8654b32cc40b8baeca9665988179398952ccb310e43fc32eb196620c87f8759632cc4010fb0eb2c65988030f996748cb310061eb2ce91966200c3e655d232cc40187acaba46598802d360a654cb3102d67414c89966200a5d86d4932cc4014bf0ca92659881793189524cb312743fc32ea196620087f8759432cc47d0fb0eb28659881739989710cb310051f424a1b2a6200a7581943654c4018f2e1286ca988033cdc110d953100e7838221b2a6200e7250443654c401878ca3a2ca988030fd4b74595310065b886e8b2a6200c3f751d1654c40187ea43a2ca988030f94474595310061e288e8b2a6200cb7101d1654c56b8beebb9aca988021fe1570595310045fc22e0b2a62108bc845c1654c4011df04b82ca988163b209705953100c7a43a20b2a6200cb774441654c401968e8882ca988033cdc1105953100e7838220b2a6200c3d75d53644c40147d0b206c898802ad60640d91310055ac0881b226200cf370443644c4039e0e0886c898803ac90110d913100c7bc3a213226201cf270442644c4019e2e0884c89880e1fa1f75591310043ec16eab226200c7710dd5644c401878ebba2c8988021fe15705913101c3e42ae0b2262008bf845c1644c4011bf06b82c8988023be09705913102c76412e0b2262018f487441644c4018eeea882c898ac71d1d5105913100679b8220b226201cf070441644c40117f0eb20c8988028f21564191310845e422ea32262108bc845c0644c40147d0b200c898802ad606401913100e79382203226200cf170440644c401d6480880c8988028f61365951310043fc2aecaa262008bf845d9544c40187eca3a2a6988cf0f1947454d310061e3aec8a1a6200c3c75191434c4010ff0aba6c49880e1f21574d89310043fc2ae1b12620387c855c3624c40159b06106c498802b960420d893100679b8221b126201cf070443624c401dc440886c4988023be1d62189310043fc3ac9a92620387c87593524c4051b90cb9ca4988161f21d65549310051fc22caa926200a3c84595524c4014db053b2a4988028fe1176549310051e422eca926200a6f825d9524c4014ef02bb2a4988029ee01765493115d3c402eca926205a6e82991524c4014db05322a4988021fe1d64549310043e43ac8a92620087f855db424c4070f90abb684988163720e76909310146e432e721262028dc865cc424c40b1bd0f3226498816b3a0a644c93133567436e49926205ace86d89324c40b8b
  | 3 => 0xbb266200c77105d764cc4018dceb396c9988031b5d672d9331006373aae5b266200c6d755cb64cc40199ce6b96c9988031ba1572d933100636c2ae5b266200ce7105cb64cc4070fd0bb86c9988021f61770d93310046f41ee1b2662058ee82dc364cc4011db05b86c9988063de1d10d933158e3b3aa21b266200c757544364cc5659cce4886c998803395c910d933100678b8221b266200aae82d9264cc4039e4e0884c9988033c5c1109933100758a02213266200aae82dd164cc4031790ea02c9988033c5c1105933100758a0220b26620087d8799464cc4010ff0eb28c9988022fe1d64193310043fc12ea3266200c77105d464cc4031ef0e880c998ac71d9d510193310063abaa203266201cf27044064cc4019e2e0880c9988028fe1165953310043ec2cecaa662058ee829d954cc4011db053b2a9988421f21d65553310851e422caaa66203a5f8359653cc47d8ece2b2ca7988031d5957194f311d61f32ee8a9e6200c3d65dd153cc46787cca3a2a7988030f5947454f311c43ec36eaa1e620087e8759543cc4190f90eb2a879893a1fe197510f310043fc3aca21e623e87d8759443cc42196cc8b8887988030f99674d8b310061eb2ce9b166200c3e655d362cc40187acaba6c5988029b60a6598b310643fc3acb3166200a6f8259662cc40187ccb3a4c5988030f5967498b310061f32ae93166200c3d655d262cc40155d09b14c5988029b60a7558b3100537c12eab16620387e85dd162cc4010fb0bba2c59880e1fa177058b310043ec2ee0b1662018ec8748162cc5638ecea882c5988033c5c11058b310077090220b16620087d8799462cc4010ff0eb28c5988023be1d6218b310063b882eda966200c75105db52cc4070fd0fb26a5988021f61f64d4b3102d37416c9a966200a6d82d9352cc4070fd0e326a5988021f61c64d4b310146ec34e72966200c5d655ce52cc40b0fd0fb2aa5988fb1d1c56554b310063ab2ee2a966200c7710dd952cc4018ea21bb2a5988028fa127654b310051ec24eca966200a6d829d952cc4014df04bb2a5988031be097654b310063bc0aeca966200c74815d952cc4018ee20bb2a5988031d4417654b310043f438eca96620087e87d9152cc4010fb0fb22a5988169ba0b6454b3100536c16c8a966205a6e8299152cc4014db05322a5988021fa1c6454b310043ec38c8a966200c7576dc552cc4070fd0b3b685988021f61676d0b3102c5e422eda166205aae82d9342cc4070fd0b3b485988021f6167690b3101c3f42aed21662058dd835da42cc4010ff0cbac85988021fe1d6590b310043ec3acb21662028dd869ce42cc4018bccb39c8598803175967390b310064f324e72166200c9d649ce42cc4018bccab9c8598803175957390b3101c3f428eca16620087d851d942cc40b17d0fb228598816aba0
  | 4 => 0x25040b998c4b9c84a080365105739094100666b9ec52128200c7465dc54250489878edb2a84a09134d1c765509412ce1e3b0caa128259d34711954250401c5eca31284a08028fa1b525094102e1e3b6a4a128230d3471d4942504014790ca9284a08170f1d9525094102f16312a4a12822cd3471549425040536d0fb8a84a08861f21975109410869a20aea212820087f87d94425041d0fb0fb2884a08021fe1576cc94101c3e42aed992820387c859da325040b179093b464a08021fe15768c94101c3e42aed192820087c865d632504010ff0fb2c64a08021f61f658c9410061fb2ce91928200c3c659d232504051790cba464a08030fd95748c9410061e32ae919282029b4815d2325040195ae9b1464a080e1fa17764c9410043ec2eec992820387c859d832504010ff0abb064a080e1f215760c9410043e432ea192820087f87d9432504010fb0fb2864a080a2f219740c9412263b3b6cba0a8244e3764d9741504078ecec32e82a08029d21952d054113cdbc3a85a0a82018f78744365cc4019e2e0886cb9893a9da0560997310051f420c132e6200a3d8418265cc4014dd04304cb988029b60860997310053ac08c132e6200a778644265cc47d8eaec884cb988039c58110997310043f43ca0b2e6200a3e8494165cc40147b09282cb988029d606505973100c3e43aa0b2e6200cf17044165cc401ce4a0882cb988039c54110597310043f43ec0b2e620087e8718165cc40147d08302cb988028f610605973100537410c0b2e6200a6d8218165cc49d8eeec882cb988039c981105973100738b0220b2e6200c3f749d165cc40187ae83a2cb988031dc4372597310051f424e4b2e6200a3d849c965cc47d4bd07392cb988029de0572597310051f424e0b2e6200a3d849c165cc47d4ed03382cb988029d60670597311f53b408e0b2e6200a75811c165cc4010fd0f202cb988021f61e40597311f53b40c80b2e6200a758190165cc47d4ed02202cb988029d60440597311f53b40c60b2e6200a75818c165cc4010fd0e182cb988fa1f61c30597310051f42060b2e6200a3d840c165cc4014dd04182cb988029b60830597311f53b40860b2e6200a75810c165cc4010fd0f902cb988021f61f20597311f53b40c40b2e6200a758188165cc4010fd0e102cb988021f61c20597310051f42040b2e6200a3d8408165cc4014bd06102cb988029760c20597311f53b40840b2e6200a758108165cc5698ef0e882cb98acf1d21d10597310063bb9220b2e623ea778044165cc47dce700882cb988039c9c1105973100738b8220b2e6200e724044165cc401ce280882cb988039ccc110597310073818220b2e6200e722044165cc401ce240882cb988031b99672d933100636b2ce5b266200c6e655cb64cc4018dacab96c99880e1fe1d75d93310043fc12e
  | 5 => 0x9129da0430d95410053ac0861b2a820087e87c8365504010fb0f906caa09129da0620d95410053ac0c41b2a820087e8708365504010fb0e106caa08028fa1020d95410051ec2041b2a8200a5e8308365504014bb06106caa09129da0420d95410053ac0841b2a82b3c778744365505698e90e886caa08031d5c910d95412253bc0221b2a8244e73804436550401ce6e0886caa08039c1c110d95410073920221b2a8200e71404436550401ce660886caa08039c0c110d95410073910221b2a8200e7120443655057587eebba2caa08021fe1570595410046fc1ae0b2a82008dc835c165504011df04b82caa08163b209705954100c7a43a20b2a8200cf37044165504010fb0f300caa0ae68f61260195410053ac0cc032a820087f8758065504014bf06b00caa08029720d601954100537c12c032a8200a6c8258065504b34ed02300caa08029d21910195412263b3b22032a8200e736044065504898e8e3b2aa8a0802a761030d8d4100566c1061b1a8200ad5810c363504039e4e0886c6a08033c5c110d8d410076818221b1a8200c6f659ca63504018d8cb394c6a08031bd957298d410063632ae531a8200ccf635ca63504010fd0fb2ac6a08021fa1c6558d415c61fba0cab1a82008df8758c63504015ab03180c6a0802b36083018d4100679b822031a8200ed03044063504014bb07b2ca6a08422f2107654d410145f436e8a9a8200c3f65dd15350475878cbba2a6a080a6da077454d410061fb28e8a9a8233c3c651d153504b30fd0dbaa86a08034d1077550d410043f43ecaa1a824487c87d9543504670f90cba886a08021fe1f6510d410743ec3eca21a8200a6d82dd762504014db043aec4a080e1fa1673d89410043ec2ce7b12820087f855cf62504070f90ab9ec4a08021fe1570d894101c3e42ae1b128200aad84083625040159b06106c4a0802b960420d894158e3a3aa21b128200cf3704436250401dc440886c4a080317d9673989410062e32ce73128200c5f655ce62504018b8cab9cc4a081733189739894100666b9ec5312820087e87d9562504010fd0e32ac4a0adf0fdd065589410743ec3eca3128200a6d82d9462504014db04328c4a08023be1d62189410063b884eda928200c75109db525040187ecb3a4a4a080a2f21974949410061fb2ae929282029b4815d2525040b0f90eb2aa4a08021fa1a765494100536c14eca928200c6d829d952504018ee213b2a4a08031d442765494100537c12eca928200a77815d9525040187c823b2a4a08030f10476549410063a208eca928200c77101d952504018ea203b2a4a0adb0f9d865d09410051f436a5a128200a3c8654b42504b30f90cbac84a08034d10575909412243fc3ecb212820087d87d9642504018becb39c84a08031719673909410062fb2ae72128200c5c655ce4
  | 6 => 0x672886ec9906400ccf7694d320c80199eeca9a6419002e3e11534c83200567c32869906400b4f8550d320c8010ff0ab82c21900e1f21570584320045fc22e0b0864108bc845c1610c80b1d904b82c2190063d21d105843202d7241220b086400cf370441610c80317f0ea06c8a88033cdc110d915100758a0221b22a2008bf87590645457d47f0ab20c8a88073c9c1101915100678b8220322a200eb14044064544039e4e0886c6a88033c5c110d8d515ee2ebaec731aa2008df8758c63544019e6e0880c6a88021fe1576d0d5101c3e428eca1aa20287e86dd543544210f90b3b086a880a1f2197510d510061ebaec821aa2008bf845cf625442117908b9ec4a8af21fe1570d895102c3e42ae1b12a200cf37044362545778daebb14c4a88023be1d621895102d3643ec4a92a2bbe6471d895254577cce21b12a4a880399443625495130537430c4a92a200e6762dc552544010ff0abb684a88161f21676909510143e432eb212a200c3d75d92425440187aea32484a880327d9273909510064e324e7212a20587c859d842544050f90cba884a88030f5d7641095102c3e42ced192a20287c865d632544010fb0bbb264a88161f216760c9510045fc22ec192a2108bc845d832544050f90cba864a88063de1d10d974100e7938221b2e8200cf17044365d04210fd0f282cba08428fa1250597410053ac0ca0b2e8201cf27044165d04019e2e0882cba08039c941105974100679b822131e8201cf07044263d04019e6e0882c7a08073c1c11058f411d45fc22eca9e82028bc845d953d0421878e8b2aa7a080e1fa147358b410043ec28e6b16820387e85dc162d04010fb0bb82c5a08073c9c11058b4100678b8220b16820587e87d9552d04018eacbb8aa5a08029b60a7654b4100537c12eca968205a6e8298d52d04014db0531aa5a08031d5db7154b4102e1ebb6a5a168205c3d7654b42d040bc5cc4a9685a0816aba0a6350b4102f16312a4a1682058bd845da32d04011f700bb265a08063e201764cb410051ec24a1b2a8200a758194365504018f2e1286caa08061fe1d50d954100679b8221b2a8200e72504436550401ce2a0886caa080297e0d60d95410052e41ac1b2a8200a6f8258365504014d904b06caa09671d9d910d954100739b0221b2a8200e7060443655048947b09b9ecaa0803175cc73d95410063b882e5b2a8244a3d841cb65504894ed03386caa08029d60670d95410051f420e1b2a8244a3d841c365504894ed02386caa08029d60470d95410063cb80e1b2a824487e8790365504010fb0f206caa09129da0640d95410053ac0c81b2a8244a768110365504014eb02206caa09129da0630d95410053ac0c61b2a820087e870c365504010fb0e186caa08028fa1030d95410051ec2061b2a8200a6e820c365504014db04186caa
  | 7 => 0x6d829d9524c80147f08bb2a4990028f21176549320f537c12eca92642ca74815d9524c8014f700bb2a4990ae9e201765493200536c14c8a92640087f87591524c8070f90eb22a4990029de0564549321653a40ac8a926400a7b80591524c8574f100b22a4990a21fa1c64549320062f3b6e6a926405a5e86d0d524c80b69d05a1aa49900257a1c435493202da641086a92640599d8710f424c8018dceca9684990038bd9152d0932006a739aa5a126400f0c4354b424c8010ff0abb2849900e1f21576509320147a40aeca1264008fb805d9424c8031f100bb2849900e1fa1476509320043ec28eca126405b8c8210d424c80ba9ce6a96649901793d8d52cc93201c3fc3aebb0a6400c77815d7614c8018e902baec2990031dc4175d85320043ec3ea5b0a64c087f8754b614c8070fd0bb86c2990021f61770d853200c7bc3a21b0a6400a7485443614c9638ecea886c2990031d5d510d853200678b8221b0a640587e87941650c80147d09282ca190028f61250594320053b40ca0b286400a7581941650c8030f90ea82ca190073c9c1105943200678b8220b286400e7250441650c801ce2a0882ca190030fdd274594320061eba0e8b286400a3f845c5650c80147908b8aca190029ea0071594320053cc00e2b286400a7a80105650c8014f30020aca190029ea0231594320053cc0462b286405a6e820c5650c8014db0418aca190028fa1270594320051ec24e0b286400a76819c1650c8014eb03382ca190029da0470594320053ac08e0b28640087e87901650c8010fb0f202ca190029da0640594320053ac0c80b286400a7681101650c8014eb02202ca190029da0630594320053ac0c60b28640087e870c1650c8010fb0e182ca190028fa1030594320051ec2060b286405a6e820c1650c8014db04182ca190029da0430594320053ac0860b28642fc7772c41650c8578eae5882ca192ca9d60610594320043fc3a20b28640087c87441650c8018ef0e882ca190031d21d105943200739c0220b286400e7270441650c801ce2e0882ca190039c901105943200738a0220b286400e7330441650c801ce060882ca192cb9c88110594325973890220b2864bfa7681041650c8010ff0ab8cc81900e1f215719903200e79382213206400cf170442640c801d6280884c8190062f21d405903200e7938220b206400cf170441640c801d6280882c8190161fe1d65950320051fc22cb2a0640587c87595540c82147908b2aa8190031b5957294c321d61f32ee8a986400c3d65dd1530c86787cca3a2a6190030f5947454c3202e37392cb2186405cae72592430c8018dacab94861900e1f2177650c321c43ec36eaa18640087e87595430c82b0f90eb2a861900e1fa157610c320043fc32ea218640087f87594430c8010fb0eb28861900339c43764c8320
  | 8 => 0xe3b82ca990031ed4b705953200679c0ee0b2a6400cf081dc1654c80117f08b82ca990422f21170595320047bc0ae0b2a64028f4815c1654c8011f50e382ca990032edd070595320065c3a0e0b2a6400cf3711c1654c8019e0e2382ca990061f21d50595320061e3a2a0b2a6401c7870541654c8011ed0f882ca9900a3d21f10595320065bba620b2a6400cb474c41654c8019e6e1882ca990073c1c310595320047b43a20b2a64008f487441654c80196ee8882ca990032d1d1105953200679b8220b2a6401cf070441654c801ce2a0882ca990030f5d754d91320054ec1ea9b226400aad82d53644c80b1bb07b86c8992ff355cf10d91325966ab9a21b226400cf370443644c8039e0e0886c8990021fe15739913201c3e42ae7322640087f855c6644c8070f90ab8cc8990073c9c1109913200678b82213226400eb140442644c801878ebba2c8990031ddd771591320063a3aee2b2264008f580dc5644c8018eeea38ac8990031d1d471591320063dbaee0b226400c7875dc1644c8019e6e3b82c8990033c1c7705913200679c0ee0b226400cf081dc1644c8010ff0ab82c89900e1f21570591320047bc0ae0b2264028f4815c1644c8018f6ea382c8990031e1d4705913200679b88e0b226400cf0711c1644c987878eba02c8990072e1c3405913200c5e43a80b2264c2c3c75501644c80153906a02c8990072e1c140591320047b43e20b2264028f487c41644c8018eeeb882c8993071d1d7105913200679b8620b226401cf070c41644c8011ed0e882c8990023d21d10591320063bbaa20b2264b1c7475441644c8019e6e0882c8990073c1c1105913200758a0220b2264008bf87590644c8014790ab20c8990422f21175191320861e422ea322640087f825d4644c80187aebaa0c8993071d9d710191320063abae2032264b1c7675440644c8018eaea880c8990073c9c1101913200678b82203226400a3d84d96544c80117f08bb2a8990023de0576551320147a40aecaa264008fb805d9544c8031f100bb2a8990421f21d65551320851e422caaa264058de86dcd544c80b39d05b9aa8990161fe1d6594d320051e422cb29a641ca5f83596534c80187eca3a2a6990cf0f1947454d3202ce7c3ae5a1a640387e859da434c8010fb0b3b486990ea8f2156490d320061e3aec8a1a64008be87191434c801878ea32286990022fe1d6410d3219d1e42ac821a646fb1c8550c434c80169b053a88699003179d97510d32005c6c14c821a64008df87590434c80133f0eb2086991bec72156410d32005c7c12c821a64059cc825c4434c8010ff0eb26a49900e1f21d64d49320053bc0ac9a926430a7481593524c8014f700b26a4990be9e20164d49320043ec38c9a926405a5e86d0f524c80b69d05a1ea4990025761c43d49320062fb2ee6a926419a
  | 9 => 0x405923200c5e43a80b246400ab681101648c80156b02202c9190073c9c1105923200678b8220b246400eb240441648c801d6280882c9190030fdd6755923202d57414eab246400aad829d5648c80147f0ab9ac9190028f21573592320055bc0ae6b246400ab4815cd648c80157700b9ac919002ae201735923202d57416a6b246400aad82d4d648c80147f0ab8ac9190028f215715923202d56412e2b246400cb5711c5648c8015750038ac919002ae600715923202d57410a2b246400aad82145648c8015750028ac919002ae60051592320055d40462b246400ab9808c5648c80147d0b382c9190028f616705923202d57414e0b246400aad829c1648c80156d03382c919002ad60670592320055b408e0b246400ab5811c1648c80117d0f282c9190022f61e50592320055b40ca0b246400ab581941648c80b55d04282c919002ab60850592320055b408a0b246400ab581141648c80156d03182c919002ad60630592320045f43860b2464008bd870c1648c80147d0a182c9190028f614305923202d5741060b246400aad820c1648c80156d02182c919002ad60430592325ff1ba9620b2464bfe3552c41648c96556b03082c9190028fe1510592320051e42a20b246400e3785441648c801c690a882c9192cb8dd4910592325971aa9220b246400eb380441648c801d64e0882c919003ac5c110592320075928220b246400eb150441648c801d6660882c919003ac0c110592325975910220b2464b2eb120441648c97f56d02082c9190030fd51769523202c3fc3acb2a46400a3f84596548c80747d0ab24a9190161f21d655523202c5e43ac8aa46400e1f53992538c801c3ea6b24a7190022f61b7454e321d61f32ee8a9c6400c3d65dd1538c80117b0c3a2a7190cf0f9947454e320061eb28e8a9c643a8be87991538c8211790f322a7190ea2fa1d6454e3219c5e43ac8a9c6400c6d65dc9538c80b8dce4b2e87190031b59572d0e3208657322e5a1c640087d86dd5438c8010f90eb2a87190030fdd66450e320061e3acc8a1c6400c3f75591438c801878eab2287190032b5937250e3219c3fc32ea21c6410c3e645d4438c8390ff0eb2887190030f9d56410e320061ebaac821c640087f855c1618c8070f90ab82c3190063d21d105863200679b8220b0c6400cf370443654c8039e0e0886ca990030f19474595320061fa96e8b2a6400c3f751d1654c82187d0a3a2ca990030f14c74595320061fa90e8b2a6400c3c511d1654c80187ea03a2ca9900a3da1f71595320065bba6e2b2a6400cb474dc5654c8018ed0bb8aca990031dd4b71595320047ac06e2b2a6400cb7741c5654c801968e838aca990030f1d251595320063bb8ca2b2a64b4c7870945654c8031f50fb82ca990032edd370595320065c3a6e0b2a6400cf371dc1654c8019e0
  | 10 => 0xb2c6400c3f749d1658c80147f08b9acb190028f21173596320053bc0ae6b2c6400a74815cd658c8014f700b9acb190029e20173596320063bb8ce2b2c6400a7a801c5658c8014f30038acb190169ba08415963200536c1082b2c6400a7a80105658c8014f30020acb190029ea0231596320053cc0462b2c6400a3e849c1658c80147b09382cb190169ba0a705963200536c14e0b2c6400a76819c1658c8014eb03382cb190031edc270596320053b408e0b2c6400a75811c1658c8010fd0f202cb190021f61e40596320053b40c80b2c6400a7581901658c80b4dd04202cb190029b60840596320053b40880b2c6400a7581101658c8014ed03182cb190029d60630596320e43f43860b2c640087d870c1658c80147d08182cb190028f610305963202d3741060b2c6400a6d820c1658c8014ed02182cb190029d60430596325953ac0c20b2c640087f87441658c8010f90e882cb190031de1d10596320063a43a20b2c6400e7380441658c801ce4e0882cb190039c5c110596320073920220b2c6400e7140441658c801ce660882cb190039c0c110596325973910220b2c64b2e7120441658c97f4ed02082cb190162f21175992320861fbaea9324640087f855c6648c8070f90ab8cc9190432d105719923202c5e422e13246400a3e85902648c80147b0b204c919002ada0640992320055ac0c813246401cf270442648c8019e2e0884c919003ac901109923200758a02213246410c3f759d6648c80147f0ab9cc9190028f21573992320051fc2ae33246400a3c855c6648c821968e2b8cc919002aea0051992320055cc00a33246400aba808c6648c8015730118cc9190028fa1670992320051ec2ce13246400ab6819c2648c80156b03384c9190422fa1e50992320045ec3ca13246400ab681942648c80156b03284c919002ada0450992320055ac08a13246400ab6818c2648c80156b03184c9190422fa1c30992320045ec38613246400a3e850c2648c80147b0a184c919016aba08309923200556c10613246400ab6810c2648c80156b02184c9192ff8dd4b10992325ff1aa962132464bfe9732c42648c97fd2a65884c9192caad60610992320051fc2a213246400a3c85442648c80153f06884c919002a720d10992320071bc2a213246400e3485442648c801d2f06884c919003a520d10992325971ba922132464b2e3552442648c965d2e64884c9192cba54c9109923200759c02213246400eb270442648c801d62e0884c919003ac941109923200758a82213246400eb330442648c801d6060884c9192cbac8811099232597589022132464bfab681042648c80b17d0faa2c9190030fdd7545923202d57416a8b246400aba80105648c8015730020ac9190162fa1e40592320051f42c80b246400a3d85901648c80156d03202c919002ad606
  | 11 => 0x10801ce480882ca210039c50110594420073998220b288400e70304416510965ce440882ca212cb9c48110594425fd3b40820b288410a3c8459554108031bb0f984c6210033cdc11098c4200e78382213188400ed33044263108070fd0bb8ac6210021f6177158c4200c6e43a60b188400cf37044163108039e0e0882c621003b4cc11058c420052fc1acb2988410c3c74595531087587ccbba2a6210030f5977454c4201c3e42eeca18843887d86dd543108010fd0eb2a86210861f21d6550c42086572a6eca108400ce710dd942108019ca21bb284210032bdd9545084200557c3286a108400b2f8550d42108010ff0ab82c22100e1f21570584420046fc1ae0b0884008dc835c1611080b1d904b82c2210063d21d105844202d7241220b088400cf37044161108019e6e0886cb990073c1c110d973200c3e43aa0b2e6400cf37044165cc8039e0e0882cb990039c541105973200679b8221b266401cf07044364cc8010ff0ab8cc99900e1f215719933200e79382213266400cf17044264cc801d6280884c99900e1fa1f75593320062fba8e6b266400c5c751cd64cc8015730020ac9990021fe15705933201c3e42ae0b2664058dc835c164cc987878eba02c9990062f21d40593326161e3aa80b266400a9c8350164cc8018eeeb882c9993071d1d710593325fe6a39e20b266400c777544164cc9638e8ea882c9992cb351cd105933200679b8220b266401cf07044164cc801d6280882c9990430f99175193320045fc3ac83266400c3d7559064cc9838eceb880c9990031d5d7101933258e3b3aa203266400c757544064cc8039e4e0880c9990033c5c110193320845f424ed2a66400a3d84d9654cc8074790ab24a99900a3da0676553320047ac0cecaa6640087f855d954cc8210f90eb2aa99900e2f21d645533202c6ec30e6aa66400c6d655ca53cc80b0fd0fb2aa7990030fd947454f3219e1e328e8a9e643aa3c8559243cc82187cc8ba887990ce8f2156410f320061ebaac821e6477b1c8550c43cc82195cc8b908799003175da7510f320062ebb2ea21e64008df8759043cc8ef6390ab208799003535d67210f320043fc3ac9a96640095d8710f52cc80b4bb0c21ea5990861f21d6454b3201c3f438c8a966405b4e82d0d52cc8012bd0e21aa599016976184354b3202da741086a96640599d8710f42cc80b53b0c21e8599016e3a0843d0b3202d4ec3086a166400e2e6454942cc801a9ee6a928599003c310d5250b320043fc2ae0b0e640387c855c161cc8031e90e882c3990033cdc1105873200e7838220b0e6400c7771945658c80b0fd0f282cb190028fa1250596320051ec24a0b2c6400a7681941658c8014eb03282cb190031edc2505963200c3e43aa0b2c6401cf270441658c8019e2e0882cb190039c941105963200738a8220
  | 12 => 0x31b5957290e420066731ae521c840087d86dd543908010f90eb2a872100317dd66350e420062e3acc6a1c8400c5f7558d43908018b8eab1a87210033358f7250e4219c3fc32ea21c842887f8759443908018bceab188721003175d56310e420043fc2ae0b0c840387c855c161908031e90e882c3210033cdc110586420051ec24a3b2a840187f8754365508039e4e0886caa10033c5c110d954200738a8221b2a84028f687dc565508018eea5b8acaa10023d60371595420063bba8e2b2a8400cb7741c565508015e30038acaa100237e0d70595420046e41ae0b2a84008f7815c165508051e902b82caa10023da1f10595420147a43e20b2a84008f68744165508011e90e882caa10073c9c1105954200678b8220b2a840587f87596545085147f08b2ca8a11129d20565951420043fc2ae3b1a840387c855c763508039e4e0886c6a10033c5c110d8d4200758a0221b1a84008df8758c635080187f08ba8c6a10030f2117518d4201c3f42ee031a840087d85dc063509838eceb880c6a10031d5d71018d4258e3b3aa2031a8400c757544063508039e4e0880c6a10033c5c11018d420052ec1ecb29a843ea7481595535080b35d05ba2a6a10cf0f9947454d420061eb28e8a9a840387e859db43508010fb0b3b686a10166be1d7290d4200596c14ea21a8400c3e765d4435080171b0531886a100267e1d6310d42005c7c12c621a840087d8718f525080b47d0d21ea4a1016cba0a43d49420049ec3887a928400c3f65dd1525084b4db053b2a4a10aa9be0976549421653a40aeca928400c3e76dd1525080187aec3a2a4a10721fa1c635494202d1f43486a928405b2e8290d525080127d0e21aa4a1016cb208435494202e973a2a5a128405e2f6454b42508011f700b9ec2a10063e20173d854201c3f42ee1b0a840087d85dc361508031ef0e886c2a10029d21510d854200e7938221b0a8400cf170443615080b0fd0f282ca210428fa1250594420053b40ca0b288400a758194165108030f90ea82ca210073c9c1105944200678b8220b288400e72504416510801ce2a0882ca2100317dce73594420851e422e6b288410a3c845c565108014f50038aca210029e60071594420053d40462b288400a79808c5651082147d09382ca210028f61270594420053b40ce0b288400a75819c165108014ed02382ca210029d604705944210c3f43c80b28840087d8790165108014ed03202ca210029d60640594420053b40c60b288400a75818c165108010fd0e182ca210021f61c30594420851f42060b288400a3d840c1651080b4dd04182ca210029b60830594420053b40860b288400a75810c165109654eb03082ca210021fe1d10594420043e43a20b288400c778744165108018e90e882ca210039ce0110594420073938220b288400e717044165
  | 13 => 0x56b408e131c8400ad5811c2639080153d09284c721002a76125098e420056b40ca131c8400ad58194263908015ad02284c721002b56045098e420052f42c8131c8400a5d8590263908015ad03204c721002b56064098e420056b4088131c8400ad581102639097fcaea5884c7212ff9554b1098e425ff4ba162131c84bfe9542c4263908014bf0a884c721002972151098e420054fc222131c8400a9c844426390801caf0a884c721003952151098e420074bc222131c8400e94844426390965caea4884c7212cb955491098e425974ba122131c84b2e95424426390801da700884c721003b4dc11098e42007683822131c8400ed2504426390801da2a0884c721003b49011098e4200768a022131c84b2ed2204426390965da240884c72100317dd75358e4202d67416a6b1c840387e85dc563908010fb0bb8ac721002b6a023158e420056cc0462b1c8400ad6818c163908015ab03182c7210063721d3058e420052f42860b1c8400a5d850c1639080153b08182c721016b3a083058e420056b40860b1c8400ad5810c163908019e6e0882c7210073c1c11058e420076998220b1c8400ed03044163908018beeb3aac721016b3a0a7558e4200566c14eab1c8400a9f845d563908014bf0aba2c721002972157458e420056bc0ae8b1c8400ad4815d163908015b700ba2c721002b62017458e4202d67416a8b1c8400acd82d516390801c3ea92a2c72100297a177158e420052ec2ee2b1c8400ada809c563908015b30138ac721016b3a085158e4200566c10a2b1c8400ada8014563908015b30028ac721002b6a004158e420056cc0082b1c8400ad6819c163908015ab03382c72100297a147058e420052ec28e0b1c8400a9e841c1639080153b08382c721016b3a087058e4200566c10e0b1c8400ad6811c163908015ab02382c721002a7a125058e420054ec24a0b1c8400ad68194163908015ab03282c721016b3a085058e4200566c10a0b1c8400ad68114163908015ab02282c72100297a164058e420052ec2c80b1c8405ace82901639080159b05202c721002b5a064058e420056ac0c80b1c8400ad68110163908015ab02202c7212ff95d4b1058e425ff2aa9620b1c8400a5f8544163908014b90a882c72100395e151058e420072a42a20b1c84b2e57524416390965caaa4882c721003b4e011058e4200769b8220b1c8400ed0704416390801da4a0882c721003b45411058e420076920220b1c8400ed1404416390965da440882c7212cbb44811058e420062fa9eed29c8400c5f535da53908014bf06b2ca7210163761e6394e4201d2f42cc729c8403a5e8558e539087587ccbba2a7210030f5977454e4219e1f328e8a9c8400c3d651d1539080193ee931aa721003271d26354e4202c6e43ac6a9c8400c9c7458d539080b8dce4b2c8721
  | 14 => 0x475c4163d08018eeea882c7a12c71d1d51058f4200679b8220b1e8401cf07044163d0801d6280882c7a10029760f6594f420846ec3cc729e8403a5e8598e53d08074b90ab1ca7a10430f1d16554f420864e3a4c6a9e84108dc8758d53d08754790abb487a10ea8f2156390f4219d1e42ac621e840087f8758f52d080127b0e21ea5a10168f61843d4b420861e3a2caa96841587c8758d52d080b65d0521aa5a10024fa1c4354b4202d1ec3086a968405b2e8210d52d08070fd0fbaac3a10031dc4375587420043f43ea4b0e84c087c8754961d08010ff0ab82c3a100e1f215705874200c7a43a20b0e8400c777544161d09638e8ea882c3a10033cdc110587420063bb8ca2b2c840587e87941659080147b09282cb210029da0650596420053ac0ca0b2c8400c7b7094165908030f90ea82cb210073c9c1105964200678b8220b2c8400e72504416590801ce2a0882cb210029de0574596420053a40ae8b2c8400c5f739cd659080147f08b9acb210031ddc671596420051fc22e2b2c8400a7a801c565908014f30038acb210029ea0041596420053cc0082b2c8400a7a808c565908014f30118acb210169ba08315964200536c1062b2c8400a3e849c1659080147b09382cb210029da0670596420053ac0ce0b2c8400c7b709c165908014ed02382cb210029d60470596420043f43c80b2c840087d8790165908014ed03202cb210029d60640596420053b40880b2c8400a758110165908014ed03182cb210029d60630596420043f43860b2c840087d870c1659080147d08182cb210028f610305964202d3741060b2c8400a6d820c165908014ed02182cb210029d60430596425953ac0c20b2c840087f8744165908010f90e882cb210031de1d10596420063a43a20b2c8400e73804416590801ce4e0882cb210039c5c110596420073920220b2c8400e71404416590801ce660882cb210039c0c110596425973910220b2c84b2e7120441659097f4ed02082cb210031b59772552420054ec20a731c8400ada808c663908015b30118cc7210063761f3098e420056b40c6131c8400ad5818c263908014bd0a184c721002976143098e420054ec206131c8400ad6810c263908015ab02184c7210033cdc11098e4200e783822131c8400ed3304426390801da060884c72100317dd67598e420054fc22eb31c8400a9e841d6639080153b083acc72100387d525498e420070eaa0a931c8400a5e85dc663908014bb0bb8cc721002a76137198e420056d404e331c8400ad9809c6639080b59d0438cc721002b36087198e420056d400a331c8400ad98014663908015b50020cc721002b66004198e420056b40ce131c8400ad5819c263908014bd0a384c721002976147098e420054f420e131c8400a9d841c2639080b59d04384c721002b36087098e4200
  | 15 => 0xf882c6a90b25d21f1058d520069bba620b1aa400d3474c416354801acee5882c6a90035cdc31058d5215eb838620b1aa4009768744163548012e90e882c6a90034ddd11058d520069a3a220b1aa400d67724416354801ae6e0882c6a90af5c1c11058d5200738b0220b1aa42596d829d063548010fb0f320c6a90030f5d06418d520052ec18c831aa400b4d8298c63548010ff0eb18c6a90028f2116318d52004afc3ac631aa400b4f8258c6354857ae4e0880c6a90035c5c11018d52004b6c16eda1aa42c97681ddb43548012eb03bb686a90ae5ea0376d0d52004bcc06eda1aa40096f825db435480b2df0eb9686a900e5ba1972d0d5201cb6432e5a1aa400d2f405cb4354801a5a80b9686a900359c4172d0d52006b2882e5a1aa40087f865c743548010f90cb8e86a90025b60b7690d52164bb40eed21aa40097581dda43548012df04bb486a90030f5db6490d520061fbb0c921aa400b2d82d0e435480b2df0eb9486a900e5ba197290d5201cb6432e521aa400d2f645ca4354801a58c8b9486a900353d0d7290d52006b3882e521aa400d65105ca43548012db05bb286a90031b60b7650d520063b886eca1aa400c7510dd943548010fd0d3b286a90025be097650d52004bbc0aeca1aa42c974815d943548012f700bb286a90ae5e2017650d520061fa00eca1aa400c3d401d943548018ee203b286a90031d4407650d520061e3b486a1aa40096d82dd843548018ee213b086a90031d4427610d52004b7c12ec21aa400977815d843548592e902bb086a90030f2117610d5200637c12ec21aa400c77815d843548018e902bb086a90031dc417610d520063a882ec21aa40087e861d8435480187aedb2086a90030f5d86410d520058ec18c821aa400b2d82d0c435480169b0521886a90024fe1d4310d520051e4328621aa40095f8750c435480b2dd053a6c2a90965b60a74d855202cb7414e7b0aa41996d829cf61548012f700b9ec2a90ae5e20173d85520043f436e1b0aa42b9778744361548014ef0c886c2a90af5c9c110d8552006b8b8221b0aa400d2f62dd16154801a6e21ba2c2a90034bd8874585520061f308e8b0aa400c3c611d16154801a68c23a2c2a90034dc40745855200697ba6e4b0aa400d2c74dc96154801a68e9b0ac2a90021fe1970585520049fc22e0b0aa40093c845c161548012bf06b82c2a90025720d7058552004b7c12e0b0aa42b974874416154801a6ee8882c2a90034d1d11058552006b9b8220b0aa400a3d8494765d08018eae328ecba10061fe1d50d974200e7938221b2e8400cf17044365d0801ce2a0886cba10073c9c1105974200678b8220b2e8400cf37044263d08039e0e0884c7a10021fe157058f4201c3e42ae0b1e84c3c3c75d0163d0985878eaa02c7a1002a720d4058f420063bbae20b1e84c1c7
  | 16 => 0x99152006b2b9221322a42bd72704426454801ae2e0884c8a90039c581109915200697b26e4b22a400d6772dc56454801acec5b8ac8a90025d60371591520063bbb0e2b22a400d37741c56454801acee438ac8a9002dc6007159152004afc1ae0b22a40095c835c164548012df04b82c8a90025de057059152164ba40ae0b22a40097687c4164548592e90f882c8a900359dcb1059152004bb43a20b22a400974874416454801acee4882c8a90af5c9c11059152006b8b8220b22a400b2d8299064548010ff0eb20c8a90029d20564191520049fc3ac8322a400b2f82590645480166902b20c8a90028fe1d64191520061fc3ac8322a40083f87590645480147906b20c8a90028fe09641915200717c12c8322a400e3781590645480147902b20c8a90038d20564191520051a40ac8322a400a3f8059064548332db05398c8a90028f61061191520053cc00c2322a400a3f86904645480147b0c208c8a9002cb60841191520071a30882322a400b398010464548570fb0fb00c8a90028f613601915215e3d386c0322a42b93d87d00645480147b0da00c8a90028f61940191520071ab2620322a400e35644406454857ae4e0880c8a90035c5c1101915200738b0220322a400f314044064548552df04ba6c6a90030f9d364d8d520052f41ec9b1aa400a748159363548014bd0630ec6a90031d5c461d8d520053cc00c3b1aa42b87d87d8363548014bd07b06c6a90af1e9c360d8d5215eb938221b1aa400d71704436354801ce2c0886c6a90030f5d26498d520052ec1cc931aa400a5d87d8e63548018bb0fb1cc6a900317d8d7298d5200727b1ae531aa400d4f635ca63548012db05b84c6a900395d8f1098d52006b2b962131aa400e57634426354801acae4884c6a90035cdc11098d5215eb83822131aa400d2f62dd16354801a5ec43a2c6a90021fa1f6458d520061e3a6c8b1aa400c3c7459163548014e902b22c6a90030f1d26358d5200697ba6e4b1aa400d2c74dc96354801a9ec7b92c6a90034ddd37158d520069a3a6e2b1aa400d6772dc56354801acec5b8ac6a90025d6037158d520069bba0e2b1aa400d34741c56354801acee438ac6a90030f1d26158d520063bb8cc2b1aa400c78709856354801878e830ac6a90031ddc46158d520053cc00c2b1aa400c78701856354801a76e9b82c6a90034e1d37058d52006b5b96e0b1aa400d7371dc16354801ae0e3b82c6a90035ad8b7058d52006b9c0ee0b1aa400d7081dc1635480127f08b82c6a90024f2117058d52004b7c12e0b1aa400977815c163548592e902b82c6a90034edd07058d520069c3a0e0b1aa400d6b721c16354801ae6e2382c6a90035c1c47058d520061e3a6c0b1aa42bc7870d8163548570f90eb02c6a90030f1d16058d520052e41ac0b1aa42bc787058163548012ed0
  | 17 => 0x1ea400c3d7650c43d48012bf0ea1887a9003175d94310f5200e7938221324a400cf1704426494801d6280884c9290062f21d405925200e7938220b24a400cf1704416494801d6280882c9290063761f3098e5200679b822131ca401cf0704426394801da660884c7290063721d3058e5200679b8220b1ca401cf0704416394801da660882c729017339c963d0e5202c77416ed21ca405cae7259243948012db05baa87290030f5d56410e520062ebaac621ca4018f48744161948019e6e0882c32900317d4e73d91520051ec2c83b22a400ab980107645480317f0ea06c8a90028fe1540d915200e7938221b22a400cf1704436454801d6280886c8a90022fe1d64191520055a40ac8322a410c9c435cc64548039e4e0880c8a90033c5c1101915200738a8220322a400eb140440645484b0fb0fb24a8a90968f61f64951520061ec3ec92a2a400e3710d925454801c6a21b24a8a90aa8fa1c64551520861f438c8aa2a400c3e711915454801878e2322a8a90030fdc064551520061eb80c8aa2a400e37101915454801c6a20322a8a90030f19073551520043fc3aa9b1aa401cf27044363548019e2e0886c6a90039c54110d8d520046fc3ac631aa40087d8795063548039e4e0880c6a90033c5c11018d520043ec38c929aa41987d87d8e53548334bb0fb1ca6a90031761f6394d520072b886c729aa400e5510d8e535487587ec5ba2a6a90eb4bd8b7454d520069b886e8a9aa400d3510dd1535480187d0c3a2a6a90030f6187454d5219e1fb10e8a9aa433d2f621d1535480187cc23a2a6a90030f1847454d520061fb00e8a9aa400c3d601d15354801a6e203a2a6a90034d4407454d520043f43ec8a9aa400c3c74d91535483d0fd0e31aa6a90030f1d06354d5200697ba6e4a9aa400d2c74dc95354801a5ee8392a6a90fb1d1877154d5202c3f436eba1aa40596e82dd743548211d90cb9686a90161fa1b7590d5202cb7416eb21aa400c3d75d92435480187eea32486a900e3b2197290d5202c3e432eaa1aa43a93f845d543548011ef02bb086a900a3d2057610d5202c3f436ea21aa43393c845d44354821878c8ba886a90030f5d76410d520047dc02e7b0aa4018f8805cf61548070fd0bb86c2a90063de1d10d85520053bc2a21b0aa42cc757544361548039e4e0886c2a90033c5c110d85520065a308e8b0aa41e96f825cf645480147b0d20ec8a9002cb60841d91520059cc0083b22a42b93f87503645480147f0ca06c8a90af5c9c110d9152006b8b8221b22a400f3140443645480147b0fb24c8a90030f61f64991520061fb22e5322a400e2f645ca6454801a5ec8b94c8a90028f61261991520063ab8cc3322a400a798018664548012db05b84c8a90ae1fe1d60991520051fc22c1322a400e3764c426454801acae5884c8a90038dd911
  | 18 => 0xc2147d0810aca218028f61021594430052f41842b288600a5d830856510c014f50010aca218029e60021594430061e3a6e0b288610a3e849c16510c0147b09382ca218029da0670594430053ac0ce0b288600a3f845c16510c2147908b82ca218030f1d170594430052fc1ae0b288600a5c835c16510c014ed02382ca218029d604705944319c3f43c80b28860087d879016510c014ed03202ca218029d60640594430053b40c60b288600a75818c16510c010fd0e182ca218021f61c30594430851f42060b288600a3d840c16510c014dd04182ca218029b60830594430053b40860b288600a75810c16510c010fd0f902ca218021f61f20594430053b40c40b288600a75818816510c010fd0e102ca218021f61c20594430851f42040b288600a3d840816510c014bd06102ca218029760c20594430053b40840b288600a75810816510d8bc6ee9882ca218038d1d310594430063bb9620b288600a75818416510c010ff0e882ca218021f21d10594430063bc3a20b288600c74874416510d89c6ee8882ca218038d1d110594430063bb9220b288600e73804416510c01ce4e0882ca218039c5c110594430073920220b288600e71404416510c01ce660882ca218039c0c110594430073910220b288600e71204416510c014ed02082ca218428f211655504319e1fba2caaa08633a3c845965310c0187acaba4a6218430f1d16554c431d61f32ee8a988600c3d65dd15310c21c3e86b2c862180e1f2177650c431c43ec36eaa18860087e875954310c670f90eb2a86218030fe177650c430061e42eeca188600cb710dd94310c0196a21bb286218ce4fa1f7550c430061fbb6eaa188600c3f761d54310c672790f32a86218030fdda6550c4319c9e43acaa188600c3f765954310c0193eed29a86218cf471d65350c43084ce43aa6a188600c9f7654d4310c018bf0bbb28621803172177650c430864f2a6eca188600cd710dd94310c019aa21bb2862180317ddb7550c430062fbb0eaa1886a3d1c75dd14310c0193eecaa286218430f9d2659884300536c14cb310863387f875966210c014df04b2cc4218438bd09659884300536c14eab108600a6f825d56210c070fd0bb8ac4218021f617715884301c3f42ee0b10860087d85dc16210c031d90e902c421b071d9d7105884358e3b3aa20b108601cf2704416210c019e2e0882c421803b848110588430043fc2ae0b08860387c855c16110c011df04b82c2218163b209705844300c7a43a20b088610ab4844416110c015a906882c2218033cdc110584430043fc32e3a1ea40387c865c743d48018ee21bb287a90031d4437650f521d61e3b486a1ea433c3f845d843d486787908bb087a90031dc417610f520063a882ec21ea400c3d76d0c43d48018baed21887a90024fe1d4310f5219d1e432862
  | 19 => 0x31d21d10d95430063ab9221b2a8600e73804436550c01ce6e0886caa18039c1c110d95430073920221b2a8600e71404436550c01ce660886caa18039c0c110d95430073910221b2a8600e71204436550c010ff0ab82caa18022fe1170595430046fc1ae0b2a86c7cb774c416550d8d96ee8882caa18033cdc1105954300e7838220b2a863ac3f645c86550c0147b09308caa18029ea0261195430053cc04c232a860087d879806550c0147b09300caa18029da0660195430053ac0cc032a860087f875806550c0147f08b00caa180297e0d601954361d1f420c032a8600a76811806550c014eb02300caa18028fa1b40195430051f4328032a8600a3c865006550c0163906a00caa18038ed8140195430063b3b62032a86c7e3764c406550c018ecec880caa1b1b8dd91101954300739b022032a8600e70604406550c01e6280880caa18e28f61365951430062fb2ee6aa28600c5f651cd5450c714bb07b2ca6a18030fd977454d431d61e32ee8a9a8600c3f651d15350c67878ca3a2a6a18ea8fa1b6590d430070fb2ec721a8600a6d82dd76250c014db043aec4a18021fe1571d894301c3e42ae3b12860087f855c36250c070f90ab86c4a1b0f0f1d740d89436161e3aa81b128600a9c835036250d838e8eb886c4a1ac71d1d510d894300679b8221b128601cf0704436250c01d6280886c4a18021fa1f65589430063a38ecab128600c7870d956250c010fd0e32ac4a18031d1c465589430063c380cab128600c7765dc56250c018e8cbb8ac4a18031ed9770589430063c32ee0b12863887d87d946250c014db05b28c4a18029b608651894300477c3ac4312860387e85dc36150c010fb0bb86c2a18063de1d10d854300678b8221b0a863887c86dd56150c010fd0fb2ac2a18021fa1c655854300e7938221b288600cf1704436510c014ed03304ca218029d606609944300739302213288600e71604426510c2147d0928aca218cf0f1d251594430845e422e0b2886008dc835c16510c210fd0f282ca218428fa1250594430053b40ca0b288600a75819416510c030f90ea82ca218cf0f1d1505944362e5a3a620b2886c4cb4744416510c039e4e0882ca218033c5c110594430073928220b288600e71504416510c014ed03302ca218029d606605944360e3bbb620b2886b1c77764416510c01ce4c0882ca218039c58110594430861f438e8b288600c3c749cd6510c67878e839aca218030f1d372594430851f424e4b288600a5e839c96510c2147908b92ca218029de0572594430053a40ae4b288610a3e849c56510c0147b0938aca218030f1d271594430851e422e2b288600c3c741c56510c014f50038aca218029e60071594430053d40462b288600a79808c56510c2147d0818aca218028f61031594430043f43842b28860087d87085651
  | 20 => 0x78b8221b0aa6008be87d916154c0117d0e322c2a98031d5c651d974300c3fc3aa1b2e8601cf27044365d0c019e2e0886cba18039c54110d974300e7938220b2e8600cf17044165d0c21878e8b2aa7a18073c9c11058b4300678b8220b168600eb14044162d0c070fd0fbaac3a18021f60b75587430063b886eab0e860087f855c161d0c070f90ab82c3a18063d21d10587430063bbaa20b0e86b1c747544161d0c019e6e0882c3a18033cdc110d964300e7838221b2c8600a3d849456590c030f90ea82cb218028fe11505964363f1baa620b2c86c6e37544416590c019e6e0882cb218073c1c1105964300738a8220b2c863ac3f745955490d91a38a839aa9218030f5957494e430843f43ecaa9c8633c3c651d15390c752790abb687218eb471d653d0e431d4cfc3aa7a1c86a399f875534390c070fd0bb8ac5218021f6177158a4300536c2842b148600aad840856290c0159d0610ac521802ba6002158a4300536c2e40b1486018ec874816290c019e6e0882c5218073c1c11058a430077090220b148605c6e625d46290c011df0eb10c5218031b5d56218a430043fc2ae0b0c860387c855c16190c031e90e882c3218033cdc1105864300e7838220b0c8600c75719476550c0147b09286caa18029da0650d95430053ac0ca1b2a8600c79709436550c030ff0ea86caa18033cdc110d954300e7838221b2a8600e72504436550c01ce2a0886caa18029ea0261d95430053cc04c3b2a8600a76819836550c014eb03306caa18029da0460d95430053ac08c1b2a86c2c3e765036550c0163906a06caa1b071d9db10d954358e3b3b221b2a8600e73604436550c01ce0c0886caa1803cc50110d954300636b90e5b2a8600a7a809c76550c014f30138ecaa18031d5c471d95430053d40083b2a8600a79801076550c014f50118ecaa18029e60231d95430043f43843b2a860087d870876550c0147d0810ecaa18028f61021d95430052f41843b2a8600a5d830876550c014f50010ecaa18029e60021d95430053b40ce1b2a8600a75819c36550c0147d08386caa18028f61070d95430053b408e1b2a8600a75811c36550c018f2e0386caa18021fa1e40d95430043ec3c81b2a8600a76819036550c014eb03206caa18029da0440d95430053ac0881b2a8600a76818c36550c014eb03186caa18021fa1c30d95431c43ec3861b2a8600a3e840c36550c0147b08186caa18029ba0830d954300536c1061b2a8600a76810c36550c014eb02186caa18021fa1f20d95430043ec3e41b2a8600a76818836550c014eb03106caa18021fa1c20d95430043ec3841b2a8600a3e840836550c0147b08106caa180297a0c20d95430052ec1841b2a8600a76810836550c014eb02106caa18031d5cb10d95430043fc3a21b2a860087c874436550c018ef0e886caa18
  | 21 => 0x858c46454c0157501188c8a9802ae602311915319d1e42862322a633a3c858846454c2117d0e108c8a98022f61c211915319d1f42842322a600a3d850846454c0153d06108c8a9802a760c21191530055d40042322a600ab9800846454c6747d0b380c8a98028f61670191530055b40ce0322a600ab5819c06454c6747d0ab80c8a98028fe1d50191530070fc1aa0322a600a3c835406454c01c3906a80c8a98028fe0950191530051e40aa0322a633a3f805406454c67c7700a80c8a98ce8f217301915319d1f42c60322a600a3d858c06454c0156d03180c8a9802ad60630191530051fc2a60322a633a3c854c06454c2117d0e180c8a98022f61c301915319d1f42860322a600a3d850c06454c0155d04180c8a9802ab60830191530055b40860322a600ab5810c06454c6747d0b900c8a98028f617201915319d1f42c40322a600a3d858806454c0156d03100c8a9802ad606201915319d1f42a40322a6108be870806454c0117b0e100c8a98ce8fa1420191530051ec2840322a600a9e830806454c0153b06100c8a9802ada0420191530055ac0840322a600a3f85c406454c674790b880c8a98038d947101915362f1a28e20322a600e3785c406454d8bc690b880c8a9b178d9d7101915362f1a29e20322a6c5e3752c406454d8bc6ea1880c8a98038d543101915319d1f42c20322a600a3d858406454c01c72a1080c8a98028fe15101915319d1e42a20322a600e36514406454d89c68a2880c8a98038e54110191530071bc2a20322a6c4e34854406454d89c6cea880c8a9b138d14d10191536271ba9220322a600eb3804406454c01d64e0880c8a9803ac5c110191536271ba8220322a6c4eb2504406454c01c6aa0880c8a9b13ac541101915300718a8220322a600eb3304406454c01d6060880c8a9803ac88110191530075890220322a633a3e850406454c0147b0a080c8a98f28fa1c64551530861f438c8aa2a600c3e711915454c01878e2322a8a98030fdc064551530061eb80c8aa2a600e37101915454c01c6a20322a8a98ea1fa18735515319e8fba0e6aa2a600c3c64dc95454c75c3ec7b24a6a980e1f61c6494d530061eba0c929aa633e1f631925354c6787b0e324a6a98cf0f9cc6494d5319f0f398c929aa600c3e711925354c01878e2324a6a98030fdc06494d530061eb80c929aa600e37101925354c01c6a20324a6a98030f1917294d5300536c14a7b12a62f87c875436254c019e6e0886c4a98073c1c110d895300738a8221b12a66fc9d731926254c0117d0fb22c4a98032d1c764589530065c386c8b12a6008be871916254c01968e2322c4a98032e1c064589530065bb26e2b12a600cb464dc56254c01976c9b82c4a98032e193705895300477c3ac4312a600e3651d936154c6787cea326c2a98063de1d10d8553006
  | 22 => 0x39ca9298f21fe1973952531e4afc32e72a4a600c5f865ce5494c01aae20b9ca9298035544173952530051e422eab14a600c3c54dd16294c014db0b902c5298063b21d2058a5300679b8220b14a601cf0704416294c01dc240882c5298023be1d6218a5300c7a43a20b0ca600a77854416194c019e6e0882c3298073c1c110586530055d40083b22a600ab9801076454c0147b0b206c8a9802ada0640d91530055ac0c81b22a6018bf875036454c0156d02206c8a9802ad60440d915300679b8221b22a601cf0704436454c01d6480886c8a9803ac50110d91530055d404c3b22a600ab9809876454c0156d03306c8a9802ad60660d91530055b408c1b22a600ab5811836454c01d66c0886c8a9803ac18110d915300798a8221b22a600a3d859cb6454c0195ee5396c8a98028f61472d91531d54ec18e5b22a600a3d85dc76454c0196ee338ec8a9802aea0271d91530055cc04e3b22a600aba808c76454c015730118ec8a98022fa1c21d91530045ec3843b22a63aa3e850876454c0147b0a10ec8a9802a7a0c21d91530054ec1843b22a600aba800876454c015730010ec8a9802ada0670d91530055ac0ce1b22a63aa3e851c36454c0147b0a386c8a9802ada0470d91530055ac08e1b22a600ab6818c36454c0156b03186c8a98022fa1c30d91530045ec3861b22a63aa3e850c36454c0147b0a186c8a9802aba0830d915300556c1061b22a600ab6810c36454c0156b02186c8a98ea8fa1720d91530051ec2e41b22a600ab6818836454c0156b03106c8a98022fa1c20d91530045ec3841b22a63aa3e850836454c0147b0a106c8a9802a7a0c20d91530054ec1841b22a600ab6810836454c0156b02106c8a9b1f8dd4b10d91530051fc2a21b22a63aa3c854436454c01c6f0a886c8a9b1b8d21510d91536371ba9221b22a600eb3804436454c01d66e0886c8a9803ac1c110d91536375928221b22a6c6eb1504436454c01d6660886c8a9803ac0c110d91530075910221b22a600eb1204436454c0117f0eb20c8a98432b10972191530865a20ae2322a600a3d849446454c0147f08a80c8a98028f61640191530055b40c80322a600ab5819006454c039e4e0880c8a98033c5c1101915300738a8220322a600eb2404406454c01d6280880c8a9802aea0261191530055cc04c2322a600e34619446454c0117b0f300c8a9802ada0660191530055ac0cc0322a6008bf875806454d9353f06b00c8a9802ada0460191530055ac08c0322a600e3b605406454c01d66c0880c8a9803ac181101915300798a8220322a600a3d859c86454cdf53b07390c8a98432b1c9721915319d1e42ce2322a600a3f855c46454c21968e2b88c8a98028f61e51191530051f41ca2322a600a3d829446454c67c6d03288c8a98028f602511915319d1f42c62322a600a3d
  | 23 => 0x1802a002009008c0080010000000004002000000800e008000000000200300000a800400200000080000020020040018001000000c0060020008030002000001800000000000000080000010028004008000000000000c0010000000002005000000c00a002003807800001b0000040004001002000402e000005800000200100000000020030008004002010005800000a00d0000028000006000000400a00100400100040060000018016003000008400e000000002c01e00d000000000200b001001800200300000180020010000000000000001000001400000180040360040020010000000002805800200000300380160010000000002013000800c0000080048004000002005802c00000d003801401000700d800800200000000000120030010090008000002805400000000180080080040048024002000001802c0000080000014002002002800c0100000000008006000000000000000400080080020000000000006000005800c002002003000000e003006000401c001002001c010001000000001a001001006c002000006800400a001004002c00200700480180080000008034028001002801000800500200080020020000028002002003001400600100100340000000018070000004000800000200d006800400000e003000000e003000800000200300100000000080048030000006000001c0020000008004014005000000401800a000000801600a0000018000003001806000600700080500040000078008012000004800c0000030018010002000000000000a002000000801400d002003000000800080040000000018008004001001001c00a001004001c0000040040008004005000000400c0000000008016002002801000a009001001400000100679b822131ca801cf07044263950019e6e0882c72a0073c1c11058e5400738a8220b1ca800a74815d5629500147b0928ac52a0be1fe1d5058a5400e7938220b14a800cf1704416295001ce2a0882c52a0063d21d10586540053bc2a20b0ca800cf37044161950014bb0a186c6aa002a761030d8d5400566c1061b1aa801cf27044363550019e2e0886c6aa003b40c110d8d540046fc3ac631aa8c8a9f8458c63550070fb0f2a0c6aa0029760e5418d5400566c106031aa801cf27044063550019e2e0880c6aa003b40c11018d5400536c14a9b12a801cf27044362550019e2e0886c4aa0023be1d621895400c7bc3a21b0aa801cf27044361550019e2e0886c2aa0073c9c1109925300678b8221324a600eb1404426494c031790ea02c9298028fe15405925300679b8220b24a601cf0704416494c01d6280882c9298022fe1d64192531d43fc3ac92a4a63a93f875925494c7547f0eb24a9298030fe1d64952530071b882c92a4a600e35105925494c75a3ce9
  | 24 => 0x801c002000000800801a00500000000000000000030008000000807c01e00000180040020000020008002000000000801400200180000080080068000000005000800800c00b000002401400200200000100070028024002011003000c00400b00800000080010040000000000000800000c001004802000600000000000020090018018004000002001000200000280040040010010004006000000000000000c001002c016001004000001e00300200080000020038000002000000800400800201d800000200100000dc00c0000000004000014000801801c00100080000000030008000000004001001002c002003800c0140040000020000000000800000a001000000000000000380000260120000000000003000000000a009000001001e004000000004600000380140020000028000002005006002001400300c80340000030008000002000001005002800200000000000080010000004002000800000800000a80040100020078000010000000000c000002000000c0120040028000002003001801802400100200000020010000000012000005801801000000180000080000010010002006002000400e00b001000400e00400a800400800400000000000190010048008009003000000c006000003c0040050000004004000001800c002001000004c006001000000000200000b000402c00900700200020020010004008000000000c002002000000c0000020000000002007001800000601d000000c000001000000800e0000008004002003000801400e00500180140060000010034012000001801001200e0030004010000004001801c0080000080008006001800800c000002000800a0000008000000007000000c000003000001c0400000030000004001001801000200500a0000002000000000400000000c8000000010002000001e004000800c000000002002c00a000004000400a00500300340420020008004018000003800c000002001000c01c007000001400000f0000000008003000000000000c003800800c001000009c000002003000400200100380100260010000030020000001800c012000001000001e00000980000000040000000000004002002001200000000140120010040000008004003800c010006000800000400800280000060030020024008005001000800e0090010020002006017001000000e001000001c00900080000060020000000000018000000400a00000180100020000000028000000000002c000000001800000e001000001000000900100100000020000000000005000002800a00000000200040010000020000001005000800400f000000001a0060040000012001000001400c0130010000002000003002801000300200000000000038000004000000800800e001000800000a
  | 25 => 0x185800016523c18d2000196942c72c8681058000d361220000000000c1a000204069a0000000000e4e0ad2f1adb47e22a6344843d728bd2010a408fb400049816417c800045a0000ffe0000001ef07143dc0ad80011120000002c48f9abc73f80000000402390a9040005ef0000df80da00000031f01e4000000226947e0003e80000bf6921305151c000b2428d00006600000000000dba6eb1f700000000000000000a0c0004458000000b0640e80000000005860fd8e1a49e1af00017ea0003f88000000000000000000000032880000000a80000a8c0000000002a4c0700000000b00000b6b3298e955846842ba00003b27c72ba9b7d2341990299aec3f26b1086a0f409879e40d2744b30c4f0e68ff800033e0d1b22443800059480454785d75582e44ade3df299166c3c8c252019850bf244b6268001398be918600017d4ac900000017c00000000348000a6000030d4b2e0000002fb40002ae0001b20e040000002aa8dfc0005fda6089044a644c80000003200e78e8d46846f00029c915800009908b0e8e10b3d0a46cfceb9821021041f6b21000089167e034044800182400000000000007a8000180c48c48445680a04c2000000000141aa3d0001a31266c711098000000a9d00000000000003a680000006b300000000005ba55b00e400080727591cc7da7f6393094c73e9fa4cf0fac6b00000001b846cc79a1d09231922c1e1438a68be44ce139891d26a7142df87f003e525297ac956101520c19c3852665f4ba16d43ac71e00000015f432f0001ca8000abe3008f4413e5cd0002c546ee2993fa12191060000712f4d5fc9f25f7a7b0a046e2000062800059a00032a11b84530a484a4ad07ef4a126fcea47ac62f01d4000b6a00026f42ceaa90a432552fcb4945a80008428c754c06b512279233c14dcb568a90292c04000bf363a8470000000077000176e282162800000049c15694f006625a34ba148c7ea6e0272df052e0003741d08350bca619a2804049fc5a704482a6000072095921c00030282391e80000000000000000470000000067a0c5995cfd600034a8e389b02bf4a022c89f20006089fb40000001550000cb43bc64626391606f8009a91d8e000031e810c1f400000001598805e84049a59008000000162400099a0002bcc6a00000002aec00047c0101c30dde5a10000dc80005b363c9d401b67a2640027939e71a655918d34cbfa3e300f0bee000243a12cf2eb9e0001b6ca480002912ba400008c437a1c0b7230f2340fd515ec5b62b961c2ca0003890d4827e00016d000000091100000dc298000000320c00200000040140000000008002004002800000a000000000800000c00580400020000048000008005000001400e002000001400a001000000400a005000000400000400300240100230000024000003000
  | 26 => 0x300021808ca5dd488129445a2cd4760564e7412c00000000000000000000d20b230de95240000000000001536a7f09d190950400042f80016e20002d4000109a00053c8000000aae000000000000000018554b4ab30001bb0bf80003ab00000000000000e6c62eb9f1369f807081765bc1858f12c9a1e0283161c3221d403f814895c01b0ce400000000000015182de5db001c06a6583072e28eda6ba269977d3841b222d800079e0000000ec8000c092c711f47f2bb23bd99a80361623219c14140ba82fc102515c16956a14c40005c71b68ff4e7c15e09594e111c0005880000ab60003f331e00005082250b20ce600027080010b4bbf4d48b38cba000000157000000028b305031c5bc32d80003c47f25aa30a033c00044a0f413fc8650002b55016004099a40449ca5800012896e43020001c54da607807b8000000268153b28cdb2000544107d88cc920001ecc1f20000002b6cc904ea0002c4d7324723c80624000a2a4dba63cb1e4da60113e00000000b200000000000000000b6c00004587d0ff852a1e5000146ea8f000000000000005496c8268b5a10689bd07476b0000000e7600000000012aa67d04080016f6285000000000000000000009be2cc515b18400019544b800062a68b5a60660676a5d5aca37434c00000000004f610316100016fc23434d25a0bd21790002e912cc919000011cc4888447f2fd96a202722fab5c734348007acf1316b5b3fc1398e6e03b0d11988802b4d00000012c4c7a20400007605a314784f422e84a2070df467837b5a0064d0a262800486453fe28633a0000000b5300017887067613c701fca6c6a412695f932a58a56f1e980003763a28a58af492d00000413ca6463098000e626b74c9a7b4c6c252000186ca26a3800002841ea12d41a0300b8415510180017742e019600016e81f70cd0000f76000000286000080e1152b00e268213c123593f04f25b8305d72e16c30c8000e5a69f000310d372be748a2538000a870000000888063000244c000594000000000000000024b986400036185040000c900000000f45dc0000ae4b3217208e8d2c0000003b12a54d4a00033300000006a20dba7e4e4a0003f480005b62d53feac000005d147e81709c4000000324cb52000000204d6a48db000314846223336a96214c810c4d9986126851d3d8322ceb40000000000f064f424e9728000546067a45c21c000561b019436903000000098ea003622ce174a0000001c7c3f678c00000000002921fd000104c23b64a03704f04ef5360e7400009d5c6922d7541af05e80013b600040427dcaf21740000000ada0000001568aee43753b199000045d4779e04ddaa193428ad40001fe4a4a3b400093c00021707fec4a56580005142950002bf40004c91d623100d231f07c314c07e803415154477aba0000000
  | 27 => 0x13bca8116b2cac0004f15a3800186202d3041d5451834f0000b5171097a0000c217d800038786c400043345b1e355e42dd00000515c6000000000000047a45d84ed70c26000007c04a2ae600023d8c12000000296c000aa055b8000c42000353000121200018f1e8d0e6835485000170e3a42ff000105a74900008f838600000031740000f0000137087200013c99b0a500000edaa7c28c1660000c04000be300026300008cc1f490a892249600000000000000000fb00004454680c703800bb18700000000003eb989934ea325cd915000061e00000014fa00000010480000000002cb00000001fe00000009f6000297d26400000022a90ae3c437308452b654427aa71c8dc00031a80010c60002c60000eb80002ca80005d07fb38409b92ac0004b62bd4000bb50003080bca0001df800131000000000017620260002a5c00000011cb12068635d00025744d856a0001f0400000034180000000000002da05fca894272ca8d5c701000306c0003cd000119c1aa9065b318400008765e328440003b800000013a08e80e480000001c80001b616dc69800005ad2e078f0001e212400000000bd4000557000000184e0000002ef4db4b3b0a8b0a437c83b00020810d409315d000000057f04301b03e27675d0a1f8e98aff20a25ccf6ea4b45c0da44d69f3314a1e56882493a9a6d80000002478a0d6ba03a52818d08d8a6660514380c07432f3a8c46525ff02599b8a208fa20e88f10360004c2af0c000c2b1261a0146c92a4c180006483040000b0c1e80005ea252d3c02df00000597ba000307857c7120002918000000395000000036677700011c0722bf8000000107200029a800000016800023ec00000000010c000068f0478d0800067764cb1615729a50a00d18fc4c660d099a49ce0240f42f7d5e07b23c20de928e2b81a38f24b269a41e98bfc6360005d1000181a4f60001cd88625642db80010f487b00000019081c4000000151c0000f309f0000c3759b048d57e00000000014a84bd0001b7928c559000147800000060fa84141c3925620570d7c0005cd00000000aa280800000000049d15800002f00c31bc00005800001b9c40eb0b000111c0000004e2872cc161314e9902906c7ba61d9eb4bac44c62fb17177600025b92c00008e449b1d650783f861197c40000000001e180007042a686d8000328000000064c00000018b400054f000173000000039e0001772b2200000009caa1412b80000009ad00000000000004a884280004cc00411640001cc16b80015ee000000000000000051f00651cc52600002acbea4f33748b4d03800055d0000000b433d5837c00000065114703ec62b0e127180000000001c60044948000170cfc800043e00009260004cc800135c7b10a18000ee25b400000004440000001f3000000060180000003f
  | 28 => 0x28aa78c7a40e70518000bfa1b525d0cf45582b723c086c16614412c1dd4000ad1076000144400022b000188a3a6000203ca4000050f16f519e00018022e418e1a700003440000003788e716640000002f2c70a4ee00020e00008e30000000000738120aee05d4000168a77470200000000000000005d5979800000000000000000000001b28000394581800074000020aa1986660004ec31bd5d85eb516932019c000113256517e0000001cbc6262ef29d958c0004dd37e8878000af12968b84000abd3a729e09da0c400023490580004752c3c000c070000038000000394280c3180d81db83d81ac3165ab2e48bb2604061285887c3d50c6aed18e8885293a828982000000066c508aa159a0fbc4aabcf451000185e0873d52de89661d409e00017c43d83cc926c622bf123c9f64000ac652e00017b400000000000000005200000c780005ec80000007b800008e0000b6738b000191e0000000000fc20001eda0c4212000000000045e1d8197000000000000000000003804ac0f315a01d20002b380000170b69ae4d380000a700000000000f71a794120001bc000042eb374c680000000000000000000170000000154e00005f80005485ec00013c0000be64a18774b0aa30000272d0024000002a10000b9c075205d88e0000001f7891c00000000012c20000000bb4000485566000000017500000000000000001b480a0779173000192c00002788c800000046100009a40001e180000005711b02cb8fb82256521b512c814b377113d23a96f5739ab4c9224b26a0d04000b810a68000d04000154800000000037b2220000ada2a2939026a8a100000000007570000000c440000000000d10691000000087829c2bc067443e00000001f8a584a7056235122485d599800000000000004b80003c61f284443e638d24c098924e7480002f118927a7159932ce3638c49b991d8da07b2b296485009c44f78000c548da446800000004d45220149f853031c9904e8879864407189140005c580007b268a0d5181c00000018e92b98ec4350000000e44bc20dd158962c5de00604840000003378000000a1f00018c400000000000010000001dd8000a1440f15da27c73c91e62103ac4eea39251800000000000029585c806b00000000000000210001378aa50001978000242480000000018863e80007721fd12f82440000000251780000000138000124a7af000000018617b4159a040000001c400000003700000e080000001a60c358a01001f427a8ea20000000e88d40000076890c0002271a703340002f300001ccb4c00039c800125e00000000009ae00020306b8cecc4c52200f40000000001bfc000b7f300318026018f0002540b8a5581cb80000004c0053a5040bc0005a115ec000b693f628703480002060f98f5c79f57280016eebd722700
  | 29 => 0xd8000000024ec00010700aaba1938a250002c684ca5d5000000000000049206714f60004311d900001601ab800000000000008152100000000b1d35e373000185d3580003b49c8c6b800025496c03a26a11608000000000000000180a48d575a7c44245f43ea1314dd400000000007a8000424a73817800000000000540000000cd8d9a656318110c0000000002a900000000001fb800000048a904c8480002a181680006381679f58ed079c2320001514000000008d56400006582bc4e237f0002d3c000b630ed000000021500001840000004e6ac6d12c00005d2b28000040428106812a0002af00000000000000000000000244a2543f4aaf1149d78b0c94c0001c700000001eb17684ce4182500804ee0bce00032158020620002a880000f100026418602fd0001f1412c34a10d0001162b2d12007143d409700000000009042be000000051700014140000305629df8c5e000000252800020900023e44e4af80001ad800081922d00009b6259000000089a0700000f9c46e0005481f2477c6a83329cb0cc089d1850018000b640001b2488047e14401f56c40003e980000000000f581b83ae0003ec1ac80000000bba83d7f26c218cabd98544ec5250000cb878b284adcc4b8000000000080a000000000000000048f800125689c51780b83c05845f40000dc606a00000000000000001dfc91061d39e800000000000011d87f600007097214a246053093a565000021a06480000b74c32328a22a99654917064e0584bfa6259302cb1118bf0e8c54e08f200911e4361eb80003700675488740520bd82d118e84c6b55228216c0583405a5000000000000000014de84800000005d6000000229c00013950387e00000002059cd594c2353e20fc03fe7c237d0001244882577a3340001632dd8001394a3a0000000ca85835e298ecc985400000000000c1303e06ec2ba91c3139dc8c9e99c000279164e0000329900a289c942c00011ce000000294c6be00007430d8000000000000000000000000000007b64f5aad584c21d44d9748f96518000278544c0002d787387ee81f00029a4ae05ea1aa2110a94a7c2c585600006b4000051d46aa6a12790443587fe0002dd80000000001844000b5c08d000079c16e49300007e8bbc213800026cb8f4da0190d5842c513abe50c269d190ad410ce85e2b480018b40006508ed504a00000014d15da29b0001fdc6c233741f02d51be0000001ccc00041e3b70000e960000d4a7ec78203200000012e43da18d067c10400006ca1b17fc8590002fd0000700000192ca5699b0c100000000410bd3104ed438719c0000000a46000000000022000000016900c64608c1c93e000646a9b48563683ce8000f7c108000000000000000000010a88d100026a00004de0490f842a05660002a5800050f2b3a324d560
  | 30 => 0x7b5000235549a0000de2ce8000bae0001b580001de2e0a6a8000b173be0000000c8a48681d00008d7000224992e60d2d7150805200000009a92f065558e0f151264260002c6400036a5678a04f0eb3e00017256040760002e0800000019885f800025d0482930a420004f13194f94a6b0660e40578aea000000087600d0000000ee8185319000185a5cf2ea000190e3231f21148aba97c0000b243c2694331b0e8f80b7d000281800012f27d88b80008f108980009864321da0f8c2e200000024c53400004279340000000000000095894f61700005623af59ea9c000093e30922786c459e00010a0000a2400026c108cb3058a1188ff40003062dd575881400004040004d12a800004fec9b49400000001044fa2c340002fa605ac60f4800000001180006bf0000b110f00005458c24e600000001e00eb60000001fe400000053400780006371ad974c0008c641f85502304b517880000007d200020b866a0000000000b809ba58496f918a000000083d8388a63bb000166200035ea70155a96b3a523ccbda9d5570b0f4c5850762b1b81270461000075400000052aa0350140005d4a0611fe47458e820ce2200026201758c67a556e14311c4b110d02c989ac0005a59de8000000000275cdca0b441bab895c80000002f0000017d42182f82840006108ec4000b5f1a294018a2aac07e8a858202751c7a658fca000000034000000000008a05a09ee5ee1aa41284c64bb284908000063d8000000a084c9092022c85632c8be029495200025140004bc1691c19476b610a280017a200023d800093416a51008846b4000286a08c10ac6e41800f8000994639af0400053900000012c60002a99a9c85e3180000e6484a21837996958d4000000000000028907980014bc28d0000000000a4e3d011198fe3e016c0bdd16e4aa3a79f7465400000008203720005a295ccc049ab235a22818a847147232ce569054b3ab7400000039a00009729e9519800000000000020a5562ac724000000000000928000000000317074c000caa50e9364b5a00054a0378eca77d5b286514aea924b50bb80009dc4192ffd93e70b38807700240455d9a219712003266908c94227a12a1c25556b0702890e00ee47f2c0b038ee678513203801622665e61f8ca7e3441eea7c000000002f80014160000000000d0e00000000bd4c46f75d1800049400000000000004492348110cd0a21240a90c00000045e0bd099e72914f800000000000000000aa8d94b700000001153252b582400001be00010e28152e22e0c6c8b803552190000bcd63380000000004fe847d0d273215b1d7cdf8a1500031c90eabaf002a65c1cc6d72b085bcf3600033daae046c08000000009940002c8800000000028200000000000fa92c4b0400046c00010aa0000002b650222e5635800003084c2f08
  | 31 => 0xadc00000029cc2209e76311a353225520da211415c86b093257c27cb0a00000001b400027f99c4a068ba11d16c492e3744121818d243321d385cc47a53d0052f596b00b230f80000005ce1c58000e327db00000007269294c200009701c1000000175a0004861e550dab1f47ab1a17ee3714b6afc8b3a6ce1a8ace58089e6000000055e0001d580013a829d0000694eb00000bc2facaec1e3000000139029400013e892800018813805309b23bc000184412730d2a998320e917c82d95a41871b580001348870000dd56400002d000005440000000000cfc2e2000000078488064f25d40008ce19d15f4ed854156c00019404924c391050845290001934cf832556406fd5004a461a0234a5c0004ad2810f2631243b93dc000b41224032060ac4400009a40021244771af03946865f097b8e4029e4b895b01c64bb07e0350984c394ef969c0de9183e18f894c6bfc472800000000041118f95dc2d94cf80000002ec0000000000bb000024fd8780003f41e58fa20004aa00000005d81d6800142e42e12f2b3404a8fc0002fb87305b8522884189c20400000014023ae529299d7204162ed80000aec8e0a780000001ef00019414b2000381800000000b0001c1cfe60003ef8000cce00000002200000001d999c0cc20002f80dbc41800000024580004a80000000a9612a00009f800028b2d6000096800020d800194a01c60b029478e9be2aa800096cc184640d9c0000004a200018aa0004e1a07949200037910fc000bf05cb2e9c0001380000bd800024511f8de45569e8501000000000000019d400000053280002c2000000000000000000000000004bf0002674ecc0003f50d591187173b7871d2fa45813e99e41a62dc3852a7070cb3504db090e80b46514155826e75422100004006f537200c4a24a1a55a2f957181df5e49658844ae03fa8828a907bd05c9634f28623312af40b4800000000001de00031026c40008be185826445642900023000000000002e140002e30000fa80001b023a90350e44100000000d8e0002af80013b40000000941130000233000127a82715a00004b68e94c528b800098000000003024904698000d8c66d39212554843c85df15c82fe92c0d59914000b5e0000000b3e1e91500c0c5222fb1a4b1b000000046f00009c600000012f80000000000ba400000057a174000055421ea3c8000000560b03114617c597a1d14264d519f879c2ae94d3498a9551ab6024c97e80006f431996700004ab179327572ab932b5aff413851f3e70000000197000107117a000000000140a000000293c00000006b87957b6000257a2cd94e8c3000000150c98113b224153c7b40cb028820c7cf4b29e28000483000000170897939f839430800000015310661ec1958000cd697755e13f40000000001a8c0000000000600000
  | 32 => 0x3630001d048a200000000002ac9a20389efc232a2300000000000004141b2cd8a88106ea058db88a85ef0568df696000021b800053355188c100cad300019c80000000158f7877487f37c91780000ca0000001342000360a1f40001286408000000000000307400000047b800000045549cb1900b6000000081921e0003580cd000000005c0ac91563653ea96a93a45190000af5920bc8000022950a61c082905d90c00000e97cc00000041780016de0000001abc3e4a9a0390000000000406000000000053f00007e465253b80008da75d0580001490b0560aa6d40cc53a45282109d0a2c0001010000000000172c00099839700687548eb00004080004ad10b312cd1c0003dc92c91c211b18a30fc8ee7c8173a7587520004dc0000000000235091000000000000018b20540002c796086cf29f000800036e28d9d800006b800007b40000004b4800000035500013f98ee36c4d180017aac000003020c8800000000014f4aa85cead5c0000004838000000000491800000000057da76457c0000000000d6a0004fa8000000000154000000000053a00008e20000000000000000000000076cba60530000b8c000060ab7c0009574a9800009200034c8d640006d118300000f2b8e4af29c400020e0002de5376407000000000067f57e214d382c0f4091b40f22a294bd8ac18a80002169b3187c2c63d499380001900000000e3a11410c9064428000000000000035353aadb0bc827461c31f87965f664101a08ae8f807f8260090059541a42cec600021d
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8012719020574596420058c6527044165908014719790110596420051c65c304416590801631940c1105964200598648304416590801651950c11098e42005a465030442639080121f985505498e4200594654704426390801691941c11098e42005b0648704426390801691949411098e4200594656404426390801651950c11058e42005a465030441639080124d922151058e4200591648854416390801651951c11058e42005a46507044163908016c1921c11058e42005a4652504416390801651959011058e42005b064a40441639080144d929d56310e4200d1ce5d5044365508018737560071595420062cdd1801c565508050f0985c110595420053424d704416550801434915947454d420040fe61761d15250801434915d874549420058c6527044165108014719790110594420051c65c304416510801631940c1105944200598648304416510803470975411059732006071d48350164cc8034b09750110593326570c1d54044164cc80169093501105933219c0f2617559043cc8016319494110596320058c65270441658c801661929c110596320051c65e40441658c801471970c110596320058c65030441658c801661920c110596320058c65640442648c801631959c110992320052c65e50442648c8014b1970c110992320058c65430442648c8016a1920c110992320058c65640441648c80122d9221510592320058964885441648c801631959c11059232005a864a70441648c8014b19794110592320052c65c30441648c801631950c11059232005a864830441648c80142d929d56410e320050e640511d1654c8034709754110595320061c21d50441654c801c30745411059532006071d483501644c8034b09750110591320062c21d40441644c995c30755011059132005a424d40441644c8014719020575d85320058c65250441650c80103f985d074594320058c65270441650c8014719790110594320051c65c30441650c801631940c110594320059864830441650c8016319494110d95412258c6507044365504894729790110d95410051ca5c304436550401631940c110d954100598648304436550401691940c110d8d41005b06483044363504016c1920c11018d410050b648411d952504014719010476549410060d1c48654942504016319494110597310040fe61741d165cc401631949c110597310051c65e4044165cc47d471970c110597310058c6503044165cc401661920c110597310050b64a655d262cc401471902057654b310051364a655ce42cc40142d92995748cb310058c6525044165c840103f985d074597210058c6527044165c84014719790110597210051c65c3044165c8401631940c11059721005986483044165c84016c1920c110d8d21005b064830440634840142d921d46450d21
  | 1 => 0x30052c65c304406454c01631950c11019153005a8648304406454c016319588110191530050e640711915454c01c317044064551530050e642711925354c01c33704406494d5317d1c25d504436254c034739754110d974300d1c25d504416590c0163394541105964300d3825d204416290c016319494110d95436570c9d9404436550c017109350110d95430058c650704436550c014729790110d95430051ca5c304436550c01631940c110d954300598648304436550c0121c9321940195430058ca59404406550c01630965011019543005c424d404406550c0181c7520d40d89436570c1d5404436250c016909350110d89430053424d704416510d89c307454110594430049c640815c96510c0183874600715944319c0f25d840c56510c0181c7420d70594430058c652704416510c01633945c110594430070c1d1704416510c01650935c110594430051c65e404416510c01471970c110594430058c650304416510c01661920c110594430050b64885dd94310c0144d922177650c4319c0f2617650c43d48034b39750110d91520058ce554044364548012b19020564191520050e64071191545480141c935c064551520070c5c1101915454801434916187454d520050e640611d1535480141c935807454d520070c581101d153548014b190184745855215d4ce5d4044364548016339650110d915215d1ce5d6044264548016339458110991520061cdd9801c5645480193374600715915200658dc9801c56454859170985c110591520055424d704416454801563925c110591520049c6408159064548013319020564191520060de1f8159064548012399020564191520060de1c8159064548016319020564191520068ca408159064548012359020564191520068c6408159064548012319020564191520040f65f869046454801a258218441191520058c640611046454801a306160041191520048d24584d8064548012349161b40191520040fe5d86500645480121c9361940191520048d2458650064548012349859310191520050de5d64c4064548012349859110191520050de5d6444064548016319650110191520049c64081593635480156192dc11098d520060d1d0815916354801271902056458d520060e1d1801856354801079981c06158d52006071d0835816354857470975811058d520061c21d604416354801c30745811058d520059424d604416354801d214044172d0d520040f66376192435480143691dd86490d520050724d401d94354801c31404407650d520060d210815d84354801471902057610d520041d261105d84354801434915d86410d520054c640611d1615480103f9761251d974200d1ce5d5044365d080181c7520d4058f426570c1d54044163d0801690935011058f420058c652504416590
  | 2 => 0x530000400000280c00b0882dc9d33cf0000302b08e05ce619c271388c2c07d12800000980004500094000e029d0335c002f06827c0b0b4e91f050210001344229060040001bc5d0880c094863acd517000000a23f45a0504b37c9a334310601d0a8001b03c000fa1d805320b200072000bd0009200000000123b41b0002e001043646d3f857000de00000000000000f3447f0000039cba00c1a00000001020d03a0f8003b105308002b8000ec6a00099000000000000056000dd0008334c000d800000d4284001840000000000583e00000000000da2e000000003844f00089000e536c00118b11308b28c212b4c43a8f5000003cc0015400000002bc060e07340008190971ecc523cc92cc1610066204ab104c717847054000e4851e02421c690000025901278620d4c1318230000e07c802403d164d2044e2064ce1dc9c004a62a40217c6b3c8001200015000390f60bc00034dc01c1e1f8f7000ca00000000933a02b2a0f42f8cc1d42612400244000005b2e40018ccb2ec432a865254b6000001e8d6000c3000f13b8131c02000000000ff00000294f92fcfc000711e4002345238c001d00a000fb3601c0248a00000000000cc440a49b00037340000c800208ef0005100000000000003f0006e0a000000b52d0000000000000010203802000082c00040080804170001842010008c0c04040040400018540c01000080600048100000098002a000000c08030180002010000c000005004120800810000b0080004000180000160182c10050000832010703c080100800101a0049c640815d5629505f473975411058a5400594654304436355001691940c110d8d54005b06483044363550016c1920c11018d5400d2c25d404416494c0163395501105925300d3825d204416294c016319590110d91530058c654704436454c014b2970c110d91530058c654304436454c016a1920c110d91530058ce51504406454c0163195901101915300487a4f85c406454c0161693e1710191530058c64385c406454c672389854110191530058c656704406454c016329854110191536258c261504406454c0163397541101915300784e4d504406454c016309354110191530078424d504406454c0163392541101915
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x3480001902810d12405d314f10b1d631261408001500e0000b060150800984a8e985411019153004c21464b280880caa180201da91d4835036250c01a083a926a0221b128600d041d0935c1105944300582146b8220322a8a9002431a0245861d1535480160851ac0880e8a9aa400c0ce1d9020564191520048674ecb280880c8a9002610a365940440645480103853b2040ac8b1aa400c0c1d1902056458d520060a10e49ac0882c6a90034107424d604416354801218d0523bb0c921aa400b0428d404407650d5200606108c8102bb086a9002431a0245761904354801a083a926a0220b1e840090c680915947454d420048634048aec3a2a4a10034107524d4044164cc80184843926a0220b226400d041d4935011059132
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x4411ba1d49350110d8943
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x6
  | 4 => 0xb09
  | 5 => 0x3
  | 6 => 0xb0e
  | 7 => 0x1549
  | 8 => 0x154e
  | 9 => 0xb49
  | 10 => 0xb4e
  | 11 => 0x16c9
  | 12 => 0x16ce
  | 13 => 0xb89
  | 14 => 0xb8e
  | 15 => 0x1849
  | 16 => 0x5
  | 17 => 0x184e
  | 18 => 0xbc9
  | 19 => 0x3c9
  | 20 => 0x3ca
  | 21 => 0x3ce
  | 22 => 0x1709
  | 23 => 0xcc9
  | 24 => 0xcca
  | 25 => 0xcce
  | 26 => 0x15c9
  | 27 => 0x15ca
  | 28 => 0x15ce
  | 29 => 0x170a
  | 30 => 0x170e
  | 31 => 0x409
  | 32 => 0x40a
  | 33 => 0x40e
  | 34 => 0x1889
  | 35 => 0xd09
  | 36 => 0xd0a
  | 37 => 0xd0e
  | 38 => 0x1609
  | 39 => 0x160a
  | 40 => 0x160e
  | 41 => 0x188a
  | 42 => 0x188e
  | 43 => 0xd49
  | 44 => 0xd4a
  | 45 => 0x1649
  | 46 => 0x164a
  | 47 => 0x1a09
  | 48 => 0x1a0a
  | 49 => 0x589
  | 50 => 0x58a
  | 51 => 0x58e
  | 52 => 0x1789
  | 53 => 0x18c9
  | 54 => 0xe89
  | 55 => 0xe8a
  | 56 => 0xe8e
  | 57 => 0x178a
  | 58 => 0x178e
  | 59 => 0x18ca
  | 60 => 0x18ce
  | 61 => 0xec9
  | 62 => 0xeca
  | 63 => 0x17c9
  | 64 => 0x17ca
  | 65 => 0x1049
  | 66 => 0x104a
  | 67 => 0x1949
  | 68 => 0x194a
  | 69 => 0xd4b11
  | 70 => 0x1a0b11
  | 71 => 0x16cb51
  | 72 => 0xb56d1
  | 73 => 0xccb51
  | 74 => 0x170b51
  | 75 => 0xd4b51
  | 76 => 0x1a0b51
  | 77 => 0x5ca
  | 78 => 0x1a4a
  | 79 => 0xcd6d1
  | 80 => 0x1716d1
  | 81 => 0xd56d1
  | 82 => 0x1a16d1
  | 83 => 0x184b91
  | 84 => 0xb9851
  | 85 => 0xd0b91
  | 86 => 0x188b91
  | 87 => 0xd4b91
  | 88 => 0x1a0b91
  | 89 => 0x74a
  | 90 => 0x1a8a
  | 91 => 0xd1851
  | 92 => 0x189851
  | 93 => 0xd5851
  | 94 => 0x1a1851
  | 95 => 0xd4bd1
  | 96 => 0x140e
  | 97 => 0x24e
  | 98 => 0x144e
  | 99 => 0x28e
  | 100 => 0x148e
  | 101 => 0xcc3d1
  | 102 => 0xcc3d2
  | 103 => 0xcd711
  | 104 => 0x59711
  | 105 => 0x18d711
  | 106 => 0x170cd1
  | 107 => 0xd4cd1
  | 108 => 0x1a0cd1
  | 109 => 0x58cd1
  | 110 => 0xcc591
  | 111 => 0x58cd6
  | 112 => 0xcd8d1
  | 113 => 0x18ccd1
  | 114 => 0x1715d1
  | 115 => 0x15d711
  | 116 => 0xd5711
  | 117 => 0x1a1711
  | 118 => 0x170591
  | 119 => 0x59716
  | 120 => 0x1718d1
  | 121 => 0xd0411
  | 122 => 0x179891
  | 123 => 0x188d11
  | 124 => 0xd4d11
  | 125 => 0x1a0d11
  | 126 => 0x58d11
  | 127 => 0xd0591
  | 128 => 0xd1791
  | 129 => 0x178d11
  | 130 => 0x189611
  | 131 => 0xd5891
  | 132 => 0x1a1891
  | 133 => 0x59891
  | 134 => 0x188591
  | 135 => 0x189791
  | 136 => 0x58d51
  | 137 => 0xd4591
  | 138 => 0xd5791
  | 139 => 0xd58d1
  | 140 => 0xe8d51
  | 141 => 0xd4e91
  | 142 => 0x178d51
  | 143 => 0x18cd51
  | 144 => 0xecd51
  | 145 => 0xd4ed1
  | 146 => 0x17cd51
  | 147 => 0xd57d1
  | 148 => 0x104d51
  | 149 => 0xd5051
  | 150 => 0x194d51
  | 151 => 0xd5951
  | 152 => 0x59a11
  | 153 => 0x1a0591
  | 154 => 0xe9a11
  | 155 => 0x1a0e91
  | 156 => 0x179a11
  | 157 => 0x1a1791
  | 158 => 0x18da11
  | 159 => 0x1a18d1
  | 160 => 0xe8591
  | 161 => 0xe9791
  | 162 => 0x178591
  | 163 => 0x178596
  | 164 => 0x1798d1
  | 165 => 0x58e91
  | 166 => 0x18c591
  | 167 => 0x178e91
  | 168 => 0x18ce91
  | 169 => 0x18d791
  | 170 => 0x17ced1
  | 171 => 0xed7d1
  | 172 => 0x104ed1
  | 173 => 0xed051
  | 174 => 0x1957d1
  | 175 => 0x195051
  | 176 => 0x3ccd2
  | 177 => 0x94e
  | 178 => 0x94b
  | 179 => 0x2c9
  | 180 => 0x14c9
  | 181 => 0x1a57d2
  | 182 => 0x74412
  | 183 => 0x75612
  | 184 => 0x75792
  | 185 => 0x74a12
  | 186 => 0x1a9952
  | 187 => 0x1a0d52
  | 188 => 0x134a
  | 189 => 0x1a4ed2
  | 190 => 0x75952
  | 191 => 0x138b
  | 192 => 0x20e
  | 193 => 0x138e
  | 194 => 0xa0e
  | 195 => 0x180e
  | 196 => 0x94596
  | 197 => 0x138596
  | 198 => 0x95796
  | 199 => 0x139796
  | 200 => 0x59796
  | 201 => 0x592d6
  | 202 => 0xa0956
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 2298
  | 6 => 6715
  | 5 => 3244
  | 4 => 262
  | 3 => 25
  | 2 => 1
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 92)*7) 7
  | 7 => packedAt gbK7 (94218+((h/766+packedAt gbK7 (85026+(h % 766)*12) 12) % 3033)*13) 13
  | 6 => packedAt gbK6 (353652+((h/2238+packedAt gbK6 (322320+(h % 2238)*14) 14) % 9750)*14) 14
  | 5 => packedAt gbK5 (205449+((h/1081+packedAt gbK5 (191396+(h % 1081)*13) 13) % 4710)*13) 13
  | 4 => packedAt gbK4 (19123+((h/87+packedAt gbK4 (18340+(h % 87)*9) 9) % 380)*10) 10
  | 3 => packedAt gbK3 (2065+((h/8+packedAt gbK3 (2025+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt gbK2 (93+((h/1+packedAt gbK2 (92+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1fc1e07c1ff07f87ffffe01fc2e3b1cc4733f3
  | 1 => 0xe07e007fe0ff83f87c03ffe0057c5e7079cd9c
  | 2 => 0xffffff8000ffffff8003fffff980607f81fe1f
  | 3 => 0x7fffffff0003fffffc00003e007f83fe0fe0
  | 4 => 0x7ffffffffffc00000000003fff8003fff000
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4c0401509342480e54b204a806190c44310b1
  | 1 => 0x244a002d2854a188681b4ac0806c1650594594
  | 2 => 0x5914ac8000894a55002095151980602980aa0a
  | 3 => 0x827354a5200036612b001812e006b02ac0f40
  | 4 => 0x1079da739cee700020c1060637b6800377f000
  | 5 => 0x9e001c0210084044430218183fdb7dfc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeee0fee0eae0feeeeee0fee0eae0feeeeee0fee0eae0feeeeee0fee0eae0feeeeee0fee0eae0feeeeee0fee0eae0feeeeee0fee0eae0feeeeee0fee0eae0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37201
namespace PEqualNP.Outside.L_meta_37201
open PEqualNP.Outside.L_meta_37201.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 6 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 24 := block_range (n:=24) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 56 := (concat bs0_3_0 bs0_3_32)
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
theorem bs0_4_128 : Interval s0Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_160 : Interval s0Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_224 : Interval s0Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_256 : Interval s0Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_320 : Interval s0Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_352 : Interval s0Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_416 : Interval s0Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_448 : Interval s0Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_512 : Interval s0Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_544 : Interval s0Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_608 : Interval s0Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_640 : Interval s0Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_704 : Interval s0Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_736 : Interval s0Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_768 : Interval s0Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 781 := (concat (concat (concat (concat bs0_4_0 (concat bs0_4_32 bs0_4_64)) (concat bs0_4_96 (concat bs0_4_128 bs0_4_160))) (concat (concat bs0_4_192 (concat bs0_4_224 bs0_4_256)) (concat bs0_4_288 (concat bs0_4_320 bs0_4_352)))) (concat (concat (concat bs0_4_384 (concat bs0_4_416 bs0_4_448)) (concat bs0_4_480 (concat bs0_4_512 bs0_4_544))) (concat (concat bs0_4_576 (concat bs0_4_608 bs0_4_640)) (concat (concat bs0_4_672 bs0_4_704) (concat bs0_4_736 bs0_4_768)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_64 : Interval s0Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_128 : Interval s0Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_160 : Interval s0Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_224 : Interval s0Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_256 : Interval s0Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_320 : Interval s0Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_352 : Interval s0Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_416 : Interval s0Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_448 : Interval s0Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_512 : Interval s0Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_544 : Interval s0Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_608 : Interval s0Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_640 : Interval s0Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_704 : Interval s0Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_736 : Interval s0Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_768 : Interval s0Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_800 : Interval s0Atlas 5 800 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 801 := (concat (concat (concat (concat bs0_5_0 (concat bs0_5_32 bs0_5_64)) (concat bs0_5_96 (concat bs0_5_128 bs0_5_160))) (concat (concat bs0_5_192 (concat bs0_5_224 bs0_5_256)) (concat (concat bs0_5_288 bs0_5_320) (concat bs0_5_352 bs0_5_384)))) (concat (concat (concat bs0_5_416 (concat bs0_5_448 bs0_5_480)) (concat bs0_5_512 (concat bs0_5_544 bs0_5_576))) (concat (concat bs0_5_608 (concat bs0_5_640 bs0_5_672)) (concat (concat bs0_5_704 bs0_5_736) (concat bs0_5_768 bs0_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_32 : Interval s0Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 44 := (concat bs0_6_0 bs0_6_32)
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
theorem bs2_4_0 : Interval s2Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 2 := bs2_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
theorem alls3 : ∀ k ≤ 3, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 99 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 1 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 25 := bgb_3_0
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
theorem bgb_4_256 : Interval gbAtlas 4 256 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 262 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256))))
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
theorem bgb_5_3232 : Interval gbAtlas 5 3232 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3244 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))))) (concat (concat (concat (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960))) (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184)))) (concat (concat (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280)) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376))) (concat (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 bgb_5_1600)))))) (concat (concat (concat (concat (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696)) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))) (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)))) (concat (concat (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176))) (concat (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)) (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 bgb_5_2400))))) (concat (concat (concat (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496)) (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592))) (concat (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)) (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816)))) (concat (concat (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912)) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))) (concat (concat bgb_5_3040 (concat bgb_5_3072 bgb_5_3104)) (concat (concat bgb_5_3136 bgb_5_3168) (concat bgb_5_3200 bgb_5_3232)))))))
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
theorem bgb_6_6688 : Interval gbAtlas 6 6688 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6715 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408))) (concat (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504)) (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632)))))) (concat (concat (concat (concat (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728)) (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824))) (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048)))) (concat (concat (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464))))) (concat (concat (concat (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656))) (concat (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880)))) (concat (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104))) (concat (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)) (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 bgb_6_3328))))))) (concat (concat (concat (concat (concat (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520))) (concat (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616)) (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)))) (concat (concat (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840)) (concat bgb_6_3872 (concat bgb_6_3904 bgb_6_3936))) (concat (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032)) (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 bgb_6_4160))))) (concat (concat (concat (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352))) (concat (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448)) (concat (concat bgb_6_4480 bgb_6_4512) (concat bgb_6_4544 bgb_6_4576)))) (concat (concat (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672)) (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768))) (concat (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)) (concat (concat bgb_6_4896 bgb_6_4928) (concat bgb_6_4960 bgb_6_4992)))))) (concat (concat (concat (concat (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088)) (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184))) (concat (concat bgb_6_5216 (concat bgb_6_5248 bgb_6_5280)) (concat (concat bgb_6_5312 bgb_6_5344) (concat bgb_6_5376 bgb_6_5408)))) (concat (concat (concat bgb_6_5440 (concat bgb_6_5472 bgb_6_5504)) (concat bgb_6_5536 (concat bgb_6_5568 bgb_6_5600))) (concat (concat bgb_6_5632 (concat bgb_6_5664 bgb_6_5696)) (concat (concat bgb_6_5728 bgb_6_5760) (concat bgb_6_5792 bgb_6_5824))))) (concat (concat (concat (concat bgb_6_5856 (concat bgb_6_5888 bgb_6_5920)) (concat bgb_6_5952 (concat bgb_6_5984 bgb_6_6016))) (concat (concat bgb_6_6048 (concat bgb_6_6080 bgb_6_6112)) (concat (concat bgb_6_6144 bgb_6_6176) (concat bgb_6_6208 bgb_6_6240)))) (concat (concat (concat bgb_6_6272 (concat bgb_6_6304 bgb_6_6336)) (concat (concat bgb_6_6368 bgb_6_6400) (concat bgb_6_6432 bgb_6_6464))) (concat (concat bgb_6_6496 (concat bgb_6_6528 bgb_6_6560)) (concat (concat bgb_6_6592 bgb_6_6624) (concat bgb_6_6656 bgb_6_6688))))))))
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
theorem bgb_7_2272 : Interval gbAtlas 7 2272 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2298 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))))) (concat (concat (concat (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248)) (concat (concat bgb_7_1280 bgb_7_1312) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)))) (concat (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536)) (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 (concat bgb_7_1664 bgb_7_1696))))) (concat (concat (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824)) (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 (concat bgb_7_1952 bgb_7_1984)))) (concat (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 bgb_7_2112)) (concat (concat bgb_7_2144 bgb_7_2176) (concat bgb_7_2208 (concat bgb_7_2240 bgb_7_2272)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeee0fee0eae0feeeeee0fee0eae0feeeeee0fee0eae0feeeeee0fee0eae0feeeeee0fee0eae0feeeeee0fee0eae0feeeeee0fee0eae0feeeeee0fee0eae0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071584 * 2 ^ 32 + 4276153056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37201.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[4,5]⟩,⟨.or,[2,3]⟩,⟨.or,[1,6]⟩,⟨.and,[1,7]⟩,⟨.and,[2,9]⟩,⟨.and,[4,5]⟩,⟨.or,[0,10]⟩,⟨.or,[11,13]⟩,⟨.or,[8,12]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4276153056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4276153056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37201

open PEqualNP.Outside.L_meta_37201 in
theorem PEqualNP.Outside.L_meta_37201 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4276153056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4276153056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
