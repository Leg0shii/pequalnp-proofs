import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36987.Model
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


end PEqualNP.Outside.L_meta_36987.Model

namespace PEqualNP.Outside.L_meta_36987
open PEqualNP.Outside.L_meta_36987.Model
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

def SBf (j : Nat) : Nat := [7, 7, 5, 6, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36987

namespace PEqualNP.Outside.L_meta_36987
open PEqualNP.Outside.L_meta_36987.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x160c080119334046a62c0c0213018800622151e1e00a1514480242ebc880040000000883b0009c02d3a145a836b9000129401f327000052015801c002c4800c2010116000062600000ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x12590f00000000000092001c801400000000ee20090204c722a1ac8403000fc4a6d3d288c89e1f14c8c8d0c12814003f290c0653f8012a5f24275269f001343a5003a58f8000b0005c340003cb47b0d115040015111146a261a51c9044031363346200568314938ec13030002e002005142571e8d4e000190b4c43c4e198f227000452e023a870b85d059c4326f11a1c8e31279d0a2910692c5e5b448151e28218003e3620810d0844d20470860d9781c551d94874241b96130993c0000000318002aa3458000010371f4002c491580021308050a304a00000730019c446c000e010380060207801203800002800006020001840c80078102848d80050d04028c830088850280000a82840208850181070081018484cf54b439f28e873e50d0e7aa921ddd4543ba28a879f5350e7ea4a1edd45439e28a87b45150e68a2a1cf141439f2a0875e53d0abaa7a16794f429ea9e859d53d0a3aa7a14f947429f286853d5490a7ea6a16bd49429e28a853c5050a7ca8214f953329eaa6653e548ca7aa9196750e32bb28c6575518ca7ca8994f551329f2a0653d540cb3a86195794f41aea9e833d539067aa520cf946419f284835f53506b8a6a0cf54c419ea90833e511076ca220cf940419f2a6633d54cc7688398cfd52319e2a4639f438c73a8718e7d5231ce2a4639f428c73a8518d794631cf20c639c418c67ea898cf151319f2a0633d540c73e8618e750c31da208639e540c73aa818e7d0831cea10635e510c7aca218f5d0431cf208639c410c7a88218e5104319f2a6433d54c86bca790d754f219faa4433c54887a86310cfd51219e2a2435f53486b8a690f50c521bda824378504867ca810cf550219ea9c813d529027ca320678c640ce18c813e50902bca6205754c40cf298813d531033aa6204754c409ea90813e511033c6220670c4409f28081ba501027ca9984f55330cea1e613f548c278a9184fd51309e2a2619d434c2dea4985b14930bba8a6174514c27ca8184f550309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ca9084f55210af29c215d53843a863084fd51109e2a2215f53442b8a6885bd4910b6292213f5404278a808750c410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x75c9500840294a00f2d000170000000200000000701c59700e80940028037008db2700bc0001200000004960c4c4d58662ed9181a0120000002000a88c801ca801a0640d803e440006a599a80021a00043d800380c140000e00080140040000001820004004c5d4c5150f1763145439518553d0a346154f42a518553d0b176154f428718553d0b146154f428518553d0a1d6314142a5185438cb1543946328758e544ca3461551328e181544ca946150c3287d8d529061d63942418b588548c69661d5231a3588548c696611523187997428c635651043187597420c6946150831a5986410c6976510431a5594410c6956210431a5980410c61d6315221c51503188714540c521d40c4504861d639502187d8d5290316510c6409518553102346154c40a518553103176154c408718553103146154c4085185531021f658c4408759431102946150f308d987548c21c6550d30a5185434c30d4314930c550c514c21d63953208758c548821d6395310c5950318421d63150108b5885404314540c410
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x60800810c00000050000449c300283396c628a87051c5631414290ae5b288218c147158e540860b38ec6a9481411c54314930828e2b1ca9904147158c548820abb0a818821415c8540c410
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | 2 => packedAt s0K2 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (912+((h/16+packedAt s0K5 (800+(h % 16)*7) 7) % 67)*7) 7
  | 4 => packedAt s0K4 (4895+((h/55+packedAt s0K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s0K3 (2420+((h/20+packedAt s0K3 (2280+(h % 20)*7) 7) % 96)*7) 7
  | 2 => packedAt s0K2 (505+((h/3+packedAt s0K2 (490+(h % 3)*5) 5) % 22)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xf01ffffe03ffe07fe0ffe07fffc1ff01ce7e7c
  | 3 => 0xffe07ffffc0fffffff03ff81fffe0ffff38f8f
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x1142108c48824810052ca8a25012915414b0b5
  | 2 => 0x24c52914392484a960556454b6412a0cca565c
  | 3 => 0x42894a209069144aaa0255112aa40ca9630b0a
  | 4 => 0xb1674492241d974d3981861cd39c031bc0de0
  | 5 => 0x8c187871c38e1e7f1ce39e780e3188c1ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36987
namespace PEqualNP.Outside.L_meta_36987
open PEqualNP.Outside.L_meta_36987.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x14d005a0000720000000000e22282871b324940c26c509f465d5ac000000000012801e0002708053003c18aaf10594805c0180348348aa0080000302c4823a00000001c00105020c0810218014ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xf11487290782071091bc003800000000005944ac894889034a4471b4061f40a0c6e002283c3831001780013041e0766500108b6231f858547333000dc00312140000469353c01149ad0400000886800000005c692f95c001b3a818000518174e47a3e855180036138b0003da40560003a60d4000027c002f4d950b821500342e183194c92681f0cd429a1e99c969601169164a4a288fe111aa18867e490e88239190281c2627a4c080c001011e4c3800110140000108804a800c0270ea64c2003211c0000168a088002a89490503b025469d4e1648c973c9dce87c100b0323601000104830005030480090c890111800600018200038101000583800e81870000828209000000828000038000818092880800000509045b94b43b6a9687ae52d0e7aa5a1eb54b4396a96873e51d0e7ca1a1cf55243cfa9a873f5250e78a2a1cf141439f2a0873d53d0a7ca3a14f943429eaa485775150ae8a2a14fd4d42d7a9285b75150a78a2a16d145429a28a853c5050a7ca8214f953329eaa665ad42ccaeca3995d547329f2a4653d548ca7ca8994f551329f2a0653d540cb5a84195b94b41b6a96833d539067aa520cf946419f284836f52506d8a4a0cf54c419ea90833e511076ca220cf940419f2a6633d54cc6dca598db54b319faa4633c548c67ea898cf15131b7a92636c524c6f6a098de141319f2a0633d540c67ca990cf55321da20e433f5488678a910ebd0a21d6a1443af5488758a910ebd0e21d6a1c436e518875c8310eb106219faa2433c544867ca810cf55021d7a1043ad42087688210eb95021d6aa043af430875a8610db94421f328843e7410875c8210eb10421f220843a441087cc6210f94c4219ea9c813d529027ca3206b88640d610c813e50902dca4205b548409ea9881ae521027aa4206b5484096a90813e511035c42206b084409f28081ba501027ca9984f553309faa4613c548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320d6a16413f5488278a9104fd51209e2a2415f53482b8a6906b50920bba8a4174514827ca8104f550209f2a6213d54c427ca9084f55210b7294216d52843c843084fd51109e2a2215f53442b8a6885bd4910b6292213f5404278a8087908410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x789140003722d4f806000a80008548530016002cec0000098027045001c64017ba5669180401150b1c004005000c92180001e3600000009403348e58ad4401c135c7401768d83030e008011a000010104002810014280021460002000849918552d0e346154b43a918552d0f276154b438b18552d0f246154b438918552d0e2d6214143c9d485150b276214542a918542ccb2542947328b58a544ca3461551328e181544caa461508328bd89539062d62942418b588548c62d62950318758c54886a661d5221a358c54886a661152218b997438863565104218b59743086a46150c21a998641086a76510421a959441086a56310421a998041086a4648c421a919131086e0604c4218bd89539032651086409918552102346154840a9185521032761548408b1855210324615484089185521022f65884408b594211022d62953308b588548c2a46150b208d987548822c6550920c314d42482a46150920c9508514822d6295310c9950218421d63150108b58854043245408410
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x40804601c0040c09280021238ac428287419cf621454290ae7b288210c2575192310861338ec4a9c81091c56295330848e2b10a918604531854248212bb0a810821415cc5408410
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | 2 => packedAt s1K2 (i*49) 49
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (912+((h/16+packedAt s1K5 (800+(h % 16)*7) 7) % 73)*7) 7
  | 4 => packedAt s1K4 (4895+((h/55+packedAt s1K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s1K3 (2420+((h/20+packedAt s1K3 (2280+(h % 20)*7) 7) % 88)*7) 7
  | 2 => packedAt s1K2 (502+((h/3+packedAt s1K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0x7fffffe03f81fffe0f81fffffc1e03fc9fe67
  | 3 => 0x7e07ffffc001fffff001f81fffe003ff18f87
  | 4 => 0xf8007fffffffe07fffffe001ffffffc1fe0ff8
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x3021088c48910408052925923012299212b0ab
  | 2 => 0x5246311439222931605a0ae4d64142a4c95665
  | 3 => 0xa48b5a289075525aab0513316ab40539718b86
  | 4 => 0xc614644122460364d29640418d299601ac0d50
  | 5 => 0x7187871c3879c7f1ce79c780e311831ffe000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36987
namespace PEqualNP.Outside.L_meta_36987
open PEqualNP.Outside.L_meta_36987.Model
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
  | 0 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 1 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 3 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc22231451041240529272126048a690c26315c
  | 1 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 3 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 4 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36987
namespace PEqualNP.Outside.L_meta_36987
open PEqualNP.Outside.L_meta_36987.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x20bf43bd43
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (34+((h/1+packedAt s3K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x80ffffc0fffffe07ffffc0fffe07fffcf8fe3f
  | 1 => 0xff03ffff01fc0ff83e0fff07fff83e034f1fcc
  | 2 => 0xfffc0ffffe000fffc00ffff83fffc0038fe3f0
  | 4 => 0xffffffffffffff000003ffffffff003ff
  | 5 => 0xfffff00000000fffffffffffc0000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xa6082046244842014a12c42946214a98186e15
  | 1 => 0xa58c48a1c915658168555259aa92c294b16cc
  | 2 => 0x14316914483a6aaac109a6b12d3588528da370
  | 4 => 0x58a28e2091230d34a5a0308431c63163e001aa
  | 5 => 0x60c30c38e1c38dc739ce38c601842183f6d800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaea0000eaeae8e8eaea0000eaeae8e8eaea0000eaeae8e8eaea0000eaeae8e8eaea0000eaeae8e8eaea0000eaeae8e8eaea0000eaeae8e8eaea0000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36987
namespace PEqualNP.Outside.L_meta_36987
open PEqualNP.Outside.L_meta_36987.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x8bf43bd43
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (34+((h/1+packedAt s4K4 (32+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x81ffffc07ffc0e0ffe0fc1fffe0ffe01c8fe7c
  | 1 => 0xfe03ffff81fffff03ffffe07fff03ffe7f1f8f
  | 2 => 0xfffc0ffffe000fffc00ffff83fffc0038fe3f0
  | 3 => 0xffffffffffffff000003ffffffff003ff
  | 5 => 0xfffff00000000fffffffffffc0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xac28a44714495602ce82c8ad56456a28c86e3c
  | 1 => 0x49840890c90425012154a218a510c981b1685
  | 2 => 0x18516912283a6ab54109ad312d6988530da3d0
  | 3 => 0x51628e2441230d29a5a02184318e3163e0016a
  | 5 => 0x61830c3871c38dce39ce31c6010c2183f6d800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xece8ece8ec00ec00ece8ece8ec00ec00ece8ece8ec00ec00ece8ece8ec00ec00ece8ece8ec00ec00ece8ece8ec00ec00ece8ece8ec00ec00ece8ece8ec00ec00, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36987
namespace PEqualNP.Outside.L_meta_36987
open PEqualNP.Outside.L_meta_36987.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x8437e53086faa610df14c21bf29043ef32087d86410df94421fb98843f431087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c817e52902faa5206f90a40de214817e51902faa3205f94240dfa0481fb40902fea6a05f14d40bfa9281ef52502dea4a05f14940f6292816c52502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52103dca4205b94840bea9081ed52102daa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c617e528c3dca5185b94a30bea9461ed528c2daa5185f94630fb28c6176518c2faa3187d54630baa8c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bd0a20f6214417e51882faa3105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea6905f94d20bea9a417c53483dc84907b50920f799241ec32482fea2905f14520f790a41ed21483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef42083d884105f94420fb288417651082faa2107d54420baa88417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fda0421f840843f461087e4c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443ee62887d0c510fb10a21f521443f680887e10110fd18221f930443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350bde84a16f90942bfa8a857c5150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0995f14132bfaa0657e540cafaa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d06fca1a0df54341beaa4837e53906faa720df94a41f7294836e52906faa520fb54a41b6a94837e519077e8320fdd0641bf28483fa50906f4a120df54241fca84837950906fea6a0df14d41dfa1a83bd43506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa9263ef524c6dea498df14931f6292636c524c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831f7290636e520c6faa418fb54831b6a9063de320c7b86418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f7a1643ec42c87dc6590fb4cb21fb98e43f431c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f7a1243ec42487dc6490fb4c921fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa9
  | 2 => 0x1760011c0001c21308a0530e60012c8000006a4e78001420ec178b706822c000000003b0920f211e4c0000000005245b0000005780000410e0d400177132170769ed0e40001509b3ec098cc9ec0ba104c61c025038c6080040c0c08c1d72f846ca420017e945040581984990aa641ec9512095b1264e85a0001ca70c591962a47e4001e7000750000002e26252b1463fe628648002783e50c0000b40189b95d01c424291572c67ec0017a3e671c4c000000088000a54405bca20f4426000f48000786086519f000140c080019e98097a313f800000000000748bb000000830688440005a4f89981f44e4639c9376864ef9ae0fa8a0252491ae3587a9121d60404a99b114298ce1d91042e80d0003466a80887426a96c218cd08424404800206000d324807206c000000008240b8000000a05109642e054091150001d80020f4ca00069a57394001108fb0181dc538970001c4ab25232a3a4000003c8644c78004146dc3c96a3422a52a80015c01c409e33ba858000c507e028c58864247785622b2342743a96435a090148d827a0010d87a4721ac02a610001e056a662a84f84e0d92aa768a58a44088d0491ba31a7712802e0dc8f07514a37e94cd40de0005d4898003e88904fa140000f8dc0000da688b29c13c4648330dc21a42c5198426c000ed8003fc81c0000015e3f04d0002420004f0564ba4c9009531c06b0000942b41ec0414c2007340009000043d029d306c7a86904d3fa444001b90000051916e000714c000006e0c8eb17025802cb60c325c08c000002b28740000000080c7100011c3501285100036cac0020000003e0000668bc10800000968e580000091c588544960000000047a00000000390341270e831c6c0b39412088dd0d19303c6f4000000006f06100020c00cd288c0004812f06f3d04791b1c434811413908096000d015f0005e1168e72684092f84f44c51cd596d47c5352300043e0008c80000020c4404922c000582451aa580ca0ef00088c601c647e5450121043c5a016003014000040f0081400800000000000000c00000020080101c19020150643301016000000141e0000601406000060040000806000040040600017000030140100c200100005c000380500009000000300300c010240603400000180100300406010000000400400024010140e00400064000200900001004030081801c040680900000010000100204c130100000002000000080e070030080102c00000010040200c010201404c150000202c0004c01000080200201c01000000040e0002600000000040040000c30024040000108403000150000400000014010000003c100040400000044020040700002004220040701c0100c000140000809000010241cbf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x1e12760011a81329c731338bc000118000000000011d16600061c0e2422a00005012d000640000002b8000000e42f61f8001d103a06000125362034000ff3de0000000036637c5c23334e000000002180000001400060c0b08444e0009391d000000000190004e0001b50002340003a1fa2f908a620d0184fb8382465840024f0c87406d2633b047c8700024400114800000930000000004400000f2c48a82f22e0d200000133000000cb87f3643751803d0000000f988486000958000b20c4000002847e8000571965d0f817d39c180a185f49a18cce862494000000000ce0000000041c8885e80035e970f286510a3201019a0003cc6705529e318f31b420e0009f8000d882c7b985000000000a84764c40006a33c2e4f7140000000001eb458200239b60b64705500000045c620b328a0002700037c000bf8001fc000ea8f12e65f8771c22d6000001052e42ad22000000100bca2516a224001e00000b4382401cc9607c12941a000fa8f00006190e1f22547e080848056000850
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x553d026e62947409b58a51d036852d0140cb14a40503586054c40d394e521034d5394840d394d521034d5354840da181521032d5290840d594e51103555394440d994a51103655294440dc98251103565354440d554d51103665254440d9549511023f6550040ab189401027b6550040ba189401026e62d53309b58b54cc2d86050f30b658c40cc26e62d52309b58b548c27661d52309d587548c26e62152309b588548c27661152309d584548c3665294630d954a518c3726094630d9949518c36552546309bd89544c26c62551309dd85544c27461551309ed81544c25c6550d309b988514c26d62145309bd89540c26c62550309798c540c26e62150309b588540c27661150309d584540c2796510030ce550400c25f654c0309ed95300c2776154f209d18553c82e86050b20b318d21c82e96210320ea90840c825e63152209758c548827661152209d584548827661d4e209d587538823e64951209bd89544827b60551208f994544832d62151208f992534823d6494d208fd91534823c6454d209dd8553482746154d209b996424832c54909209b195424832c5450920ba181424826e65cc920cb15332482ea60cc920cb150324832c54c8520cb15121482cc6348520ce153204832c54881209d987540827561d50209798c540825d63150209b988540827661150209d584540826e62d4c209d987530827561d4c208f990530823d6414c209d98453082756114c209b597420826d6510820d9d0951083644254420dc54740082796510020ea10840083715110020d9547200837151880209bd9520082ac6448020d9545200827b6548020ae191200837151480209b98b54c426d62d53109bd8953c426c6254f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b10b958a41c42b5640c710d554c31c42e5620c710b518d21c426f62552109b189548425e63152109758c548426e62152109b588548426e62d4e109b58b538425e63d4a109758f52843395410210b658c40842e96210210ba58a30842b8644821097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d108fd91524423c645491097d8d524425c6354910b958a41442f260905109d195414427665cc510ad59031442e5620c510bc98031442746548510b518d214427a65d0110b658c40442e96210110bc98440442e9628c110bc9863044278654c1109e19520442b86448110f8485204426e62d50109b58b540427a60d50109798c540425d63150109b988540426d62150109d984540426e62d4c109b58b530427661d4c108f990530423d6414c109b988530426d6214c109e980530426d65948109b988520427661148109e980520436552c40109e596100436952840109dd95100436552440109ed9510043695244010
  | 1 => 0x2800140200008020509810040a09830060007064000f068440409081340a26000001c00088082000000000e190180c0005020080c160001c0404030101a100e00c220a0084c081d0002c0c020580802119b98a51d0e6d62947439e98251d0e7960947439b98a5090e6d62942439d9865090e756194243d9d4b5150f6452d4543d9d485150f645214543dad4b5050f6852d4143dcd475050f7051d4143dad485050f685214143dcd445050f7051141438fd954310e5f6550c439e98251d0a7960947429d9845050a756114142dad085050b3a4214142dc9845050b7161141429dd855310a746154c428fd954210ab860508429bd954210ae860508429e98354cca7960d53329d98650cca7561943329d987548ca7561d52329e983548ca7960d52329d986544ca7561951329bd89544ca7761551329d185544ca7b60551329e181544ca7a60145329e580514cb673214532d58c8514cb726014532dc580514ca7b60550329e181540ca7661150329d584540ca7a60150329e580540ca6d6510832cb550420cacd631083297d95320cad4614c8329bd95320cae4614c832ad18543d076a5294241da54a509076a5254241da549509066e62141419b588505066f6254c419b189531063f65504419dd95411066f62553319b18954cc67b60553319e18154cc66e62943319b58a50cc66e62d52319b58b548c67a60d52319e583548c66e62951319b58a544c66f62551319b189544c67761551319ed81544c6786055131d914b314c74c528c5319b98b540c66d62d50319e983540c67960d50318f596540c73461550318f990540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c72e5454831cb551520c7646154831d354a320c73554d04319d594410c6d5631043197d95310c6cc624c4319dd95310c6e4624c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c76952540319ed8154c86786055321b918532c86e5620c721f18c831c867a60d52219e583548863e6414e218f590538867a6014e219e580538865e63951219758e544865f63551219718d544867b60551219e181544865e6394d219bd8953486776154d2197994534874d6214d219b997424874c53d0921b9987424874c53109219b996324874c538c9219b195324874c534c921b9185324875453c8521d314e214866e62d50219e983540867960d50219798c540865d63150219e980540867960150219e983530867960d4c218f990530863d6414c219b988530867a6014c219e580530866d65cc8219b5943208675650c421f10c8310866f6548421b318d21086776548421b518d210876b3254021da0c950087733154021dc0c5500876b2154021dc88550087692154021dc485500866f6254f409b18953d02776154f409d18
  | 2 => 0x5b3329f1b252aea21adea5a42ba0d046abc8180097acc7914e14000a20ee8ea0e040a442b2c1104e0000c6d97a898307f87e0008a70000000b0ad81e3a01a0003a001649ea50352a0098c8cc020c10b2ab2be01800270ec2882e001a4b49425784c9a90e000f0782360026e118008f946152e0250009d280b03140d000ce8007e1c878856000aa4980083000a084aa79229990ca280010000cd0003497c0007040b1e0002cca9808f0b45f95a982ecc8a8e240a0c823477a707bac2bf974ca1ec389ca4d0f6a48d88530a4a800598de1b80000000000007a0024b9ce091fc052e62a29800000249d8769b4319d6ac14c54000aa8daa112c002ca60a4e5ca522580082184989bab70003f0667509e0a1ea420007e8fa4922045074212da0c8fe0022c6618e0029a559be462d0beaf8002a44f0684a11e8720408a7e8a15870afc868163ab106690400000718000003c3e0000000033100849409b278209dc93000002e400000bb86c0019674948c0848892869d8005e05a0000087b08c7116ad338000000020000000000e041858c31ac710f24c1f4aa0b60031a8418c5d80000132a51f68c990b22182e1925a1aaae24669b243d038a8a54200a62200a0032600052000dc9289a7c0e6b50128b8647c95488920aba644e99e309383580e5c22aa72ba6a1860a9a2bc1941cb162f29085b066ba72b8800c4988c600096878b10000000044818b586a002b22f8ba6e05c002680016e00000260aec02301083e588c0b3a5682b36b601c9718a020ac0108ec3aa66f144cba8c1f11c5807ab1af4002f6570000003680a44001b0392f28e0000019c311369006044000681521893e3396a921cc7405e1da58329e62300201098041a06010000202040040001010083e010201c0a030580000110001408020100012080601008060803006030302c000f000340a010682002060081002091400c02090000c020
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xd00000901200000000000000055050001100700000020000638000000000f0022802c00000000000185840cc0001570004c004000800000380014a1c15410832988e2b18841956170185520c662392c6208639114e61d09219c2e130e8490e44531853248670b80c299243d00c83154021a90e690aa010d507348550086b0b88c0a90814a1c95410030c50a830284904e17118142483142a4c199241385c660cc920c18a831a4290720425444008312322a2900418c1915148020a88e4a9863885287255040843503224290221701cd2148110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x64008000020c40535c261d0921c40535c0614c921c20545c46050920c20545c660cc920c80641cd2148110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s5K5 (18682+((h/205+packedAt s5K5 (16632+(h % 205)*10) 10) % 814)*11) 11
  | 4 => packedAt s5K4 (16974+((h/138+packedAt s5K4 (15732+(h % 138)*9) 9) % 497)*10) 10
  | 3 => packedAt s5K3 (1281+((h/8+packedAt s5K3 (1225+(h % 8)*7) 7) % 68)*6) 6
  | 2 => packedAt s5K2 (304+((h/1+packedAt s5K2 (300+(h % 1)*4) 4) % 10)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf83ffffe03ff841f1e3fc3ffffc3fc0038fe7c
  | 1 => 0x7fc07e1ffc1fffe01fc7fc3c07fc3ff8cf338f
  | 2 => 0x7fff801fffe007ffe007ffc007ffc0070fc3f0
  | 3 => 0x8000001ffffffffffff8000007fffffff003ff
  | 4 => 0xffffffe0000007fffffffffff8000007fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x985148238412c030608d15472d1545018563c
  | 1 => 0x109308a448ca24a00a435518915519304b3285
  | 2 => 0x230a2cc89187356d20059991259990a30dc3d0
  | 3 => 0x62c51112214025654900002462222c5b0016a
  | 4 => 0x44306001c31843989926222380000306e6a800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaec00feeaec00feeaec00feeaec00feeaec00feeaec00feeaec00feeaec00feeaec00feeaec00feeaec00feeaec00feeaec00feeaec00feeaec00feeaec00, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36987
namespace PEqualNP.Outside.L_meta_36987
open PEqualNP.Outside.L_meta_36987.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x3c6470900ec6244e8159d0000a020c00b3800fd12a50016004c41eb624cc50578207977468f846e00d8760354804a00a91028df0026bd90000c401c72010800001a0b5ad40035c00018070008001041808c14543030004c100e00a0001ffd50077f5401ff95007fd54005f55007fc5401ffd4c077f5301ff94c07fd53005f54c07fc53007fd0c01fe43007f50c01fc4301ffd4807fe5201ff54807fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc3201ffd4405fe5101ff54405fc51007fd0405fe41007f50405fc41007fcc405fe31007f4c405fc31007fc8405fe21007f48405fc2101ffd4003fe5001ff54003fc50007fd0003fe40007f50003fc40007fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a4008ff9952001dfcca90023fd65480117eb2a4008ff1952001df8ca900237c65480073e32a4000ffd9120005fec890003bf64480015fb224000ff99120035fcc890003fd64480017eb224000ff19120035f8c890003bc64480015e3224008ffd5120046fea890023fe5448011feaa24000df55120047f8a890003ff63480017fb1a4000ff98d2002dfcc690003fd63480017eb1a4000ff18d2002df8c690023ff5348011bfa9a4008ff94d20047faa6900037d5348011fe29a4000ffd0d20007fc8690003fd4348001fe21a4001bfd8920047fea490023fe5248011fea924008ff14920007fe8490003fe4248001f72124000ff50920007da8490003fc4248001ff9924000ff8c920007fa6490003fc3248001ffb0a4000bfd852003ffcc29000afe6148001feb0a4007ff18520015f8c290023ff514800fff28a4008ff5452003ff8a290003ff414800fff20a4000ff5052003ff88290003ff314800fff18a4000ff4c52003ff86290003ff2148001f790a4007ff88520007fa4290003ed214800ffe10a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe4090003fb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fa1048003fe0824004ffd9510025feca880037f65440013fb2a2004ff9951001dfcca88013fd65440097eb2a2004ff1951001df8ca880137c65440073e32a2000ffd9110005fec888003fe644400d7f3222000ff59110005fac888003fc644400d7e3222004ffd5110026fea888013fe5444009feaa22000df55110027f8a888003ff63440017fb1a2000ff98d1002dfcc688003fd63440017eb1a2000ff18d1002df8c688013ff5344009bfa9a2004ff94d10027faa6880037d5344009fe29a2000ffd0d10007fc8688003fd4344001fe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e3122004ffd4910027fca488013fd5244009fe2922000ffd0910007fc8488003fd4244001fe2122000ffcc910007fc6488003fd3244001fe1922001bfd8510017fea28800bfe5144005fea8a2002ff14510017fe828800bfe4144005fb20a2002ff50510007ea828800bfc4144005ff98a2002ff8c510017fa628800bfc3144005ff90a2002ff88510017ec428800bfd2144001fa90a2002ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003ff2022001ff5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x7fd50cc003fe2866001ffd033000ffc8198007fd40cc003fe2066001ff8c33000fbc6198007fa30cc003fe1866001f70c33000ffc4198007fc20cc003ff8866001ff8433000ff82198037ff654c01b7fb2a600dff9953001dfcca98037fd654c01b7eb2a600dff1953001df8ca98003ff644c0017fb226000ff99130035fcc898003fd644c0017eb226000ff19130035f8c898037ff544c01bbfaa2600dff9513006ffaa8980037d544c01bfe2a26001bfd8d3006ffea6980377f534c00bff29a600df794d3006ffaa6980037d534c01beea9a6000d754d3002ff8a698003ff434c00bff21a6000f790d30007fa8698003dd434c00bfe21a6000ffd8930005fec498003fe624c001feb126000ff18930005f8c498037ff524c01bff292600dff5493006ff8a498003ff424c001ff2126000ff50930007f88498017ff324c001ff1926000ff4c93002ff86498003ff614c0017fb0a600cff98530015fcc298003fd614c019fe30a6002bf1853006ffea298033fe514c01bfea8a600cff14530007fe8298033fe414c001fea0a600cff1053002ffe6298033fe314c001fe98a6005ff0c530007fe4298033fe214c001fe90a600cff0853000dfec098007ff504c003ff2826001ff5413000ff8a098007ff404c003ff2026001ff5013000ff88098007ff304c00bfd9826001ff8c13000fbc6098007fc304c003ee1826001fe0c13000ffc4098007fc204c003ff8826001ff8413000ff42098007fc104c013ffb2e400bbfd972005ffccb9000efe65c8017feb2e400bbf5972004ff8cb9000efc65c8013ffb264000bfd9320007fcc99001afe64c8001feb264000bf5932004ff8c99001afc64c8017ffaa6400bdfd532005ffca99002ffd54c8001beaa6400bff1532004ffec790002ff63c8001ff31e4005bf98f20007fac790002fd63c8013fe31e4005bf18f2005ffea79002f7f53c8017ff29e400bff54f20006faa79002ffc53c8001ffa1e4000ff90f20007fa8790003fc43c80037f316400bffd4b2004ffca59002ffd52c8013fe2964000ffd0b2004ffc8590003ee42c8001fea164000fb50b2004ff88590003ff32c8013ff1964000ff4cb2004ff86590027ff61c8015ff30e4002bf98720007fac390002fd61c8013fe30e4002bf1872005ffea39002bfe51c8017fea8e400aff14720007fe839002bfe41c8001fea0e400aff10720007fe639002bfe31c8001fe98e400aff0c72004ffe4390003ef21c8015ff10e4000ff48720007da4390027fc21c80037eb064001ffd432000ffca190007fd50c8003fe2864001ffd032000ffc8190007fd40c8003fe2064001ffcc32000ffc6190007fd30c8003fe1864001ff8832000fdc4190007fa20c8003fe1064001fb0832000ffe2190007fe10c8003fe0864008ffd9520045feca900037f65480013fb
  | 2 => 0x40007fe65a0003fe32d0001fe9968000ff0cb40037fec3a001bfe61d00057f30e8006ff58740005fac3a001bfc61d00057e30e8013ffd4740097fca3a004ffd51d0025fe28e8006ffd0740037fc83a001bfd41d000dfe20e8000ffcc740097fc63a0003fd31d0025fe18e8000ffc8740097fc43a0003fd21d0025fe10e8001bf5834000ffea1a0007fe50d0003fea868001ff1434000ffc81a0007be40d0003fd2068001ff1034000f7881a0007fe30d0003fe1868001ff8834000ff841a0007ff10d0003ff0868001ff0434008ffecaa0046ff6550023ff32a8003bf9954008ffacaa0046fd6550023fe32a8003bf1954000dfec8a0047ff5450023bfaa28006ff9514008ffaa8a00037d545000dfe2a28000ffd8d40005fec6a0003fe6350001feb1a8000ff18d4002df8c6a0047ff5350023bfa9a8011ff94d4008ffaa6a00037d5350023fe29a8006ffd0d40007fc86a0003fd435000dfe21a8000ffd8940005fec4a0003fe6250001feb128000ff18940005f8c4a0047ff5250023ff2928011ff5494008ff8a4a001bff4250001ff2128000ff50940037f884a0003ff3250001ff1928000ff4c940007f864a0003ff61500017fb0a8010ff98540015fcc2a0003fd6150021fe30a8002bf1854008ffea2a0043fe5150023fea8a8010ff14540037fe82a0043fe4150001fea0a8006ff10540007fe62a0043fe3150001fe98a8010ff0c540007fe42a0043fe2150001fe90a8010ff0854000dfec0a0007ff5050003ff2828001ff5414000ff8a0a0007ff405000dfda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffc60a0007fc3050003ff1028001ff0814000ffe20a0007fe1050003fe0828005ffd973002dfecb98017fe65cc0077f32e6005df9973001cfccb98017fd65cc01f7eb2e6005df59730004facb98017fc65cc00b7e32e6005ffd933002dfec998017fe64cc00d7f3266005ff59330005fac998017fc64cc00b7e326600fffd533007efea99803ffe54cc01ffeaa66000df5533007ff8a998006fe63cc00bffa9e6005dfd4f3002ffca798017de53cc00bfea9e6005df54f3007fbaa7980035d53cc00bfe29e6005ffd0f3002ffc8798017de43cc00bfea1e6000f750f3002ff88798017ff62cc00bff3166000bf98b3002ffac598002fd62cc00bfe316600fffd4b3007ffca59803ffd52cc01ffe2966000ffd0b30007fc8598003fd42cc001fe2166005ffccb3002ffc6598017fd32cc00bfe1966005ffd873002ffcc39800afe61cc00bfeb0e6000bf5873002ff8c39800afc61cc01fffa8e600eff9473007ffaa39803bfc51cc001ffa0e600eff90730007fa839803bfc41cc00bff98e6005ff8c73002ffa6398017fc31cc001ff90e600eff88730007fa439803bfc21cc0037eb066001ffd433000ffca19800
  | 3 => 0xf31e4205bf98f21007fac790802fd63c8413fe31e4205bf18f210bffea79085f7f53c842fff29e4217ff54f21006faa79085ffc53c8401ffa1e4200ff90f21007fa8790803fc43c84057f3164217ffd4b2104ffca59085ffd52c8413fe2964200ffd0b2104ffc8590803fd42c8413fe2164200ffccb2104ffc6590803ee32c8401fe9964200fb4cb2104ff8659080afd61c8405ffa8e4202ff94721017faa39080bfc51c8405ffa0e4202ff90721017fa839080bfc41c8405ff98e4202ff8c721017fa639080bfc31c8405ff10e4202fb88721017ec439080bfc21c8405f610e4209ffd83210b7fcc190806fe60c8401feb064200bf5832104ff8c190806fc60c842fffa864216ff943210bffaa19085bfc50c842dff2064216ff103210b7fc619085bfc30c842dff1064209ff08321017fe219080bfe10c8405fe0864215ffd95210adfeca908037f65484013fb2a4215ff9952101dfcca90857fd654842b7eb2a4215ff1952101df8ca908577c65484073e32a4200ffd9121005fec890803fe644840d7f3224200ff59121005fac890803fc644840d7e3224215ffd51210aefea890857fe544842bfeaa24200df551210aff8a890803ff63484017fb1a4200f7d8d21005bec690803fe634840b7f31a4200ff58d21005fac690803fc634840b7e31a4200f718d21005b8c690857ff534842bbfa9a4215ff94d210affaa6908037d534842bfe29a4200ffd0d21007fc8690803fd4348401fe21a4202bfd89210affea490857fe524842bfea924215ff14921007fe8490803fe4248401fea124200ff10921007fe6490803fe3248401f71924200ff4c921007da6490803fc32484057fb0a4202ffd4521017fca29080bfd5148405fe28a4202ffd0521017fc829080bfd4148405fe20a4202ffcc521017fc629080bfd3148405fe18a4202ffc8521007ee429080bfe2148405f710a4202ff08521017d8429080bf42148401ffb024200bfd81210a7fcc090806fe6048401feb024214ff1812100df8c090857ff5048429ff2824215ff541210a7f8a090853fe4048429fe2024214ff8c1210a7f86090853fe2048429fe1024202ffc4121017ee209080bfe1048405fe0824206ffd9740035fecba001bfe65d00077f32e8006df9974001cfccba001bfd65d00277eb2e8006df59740004facba001bfc65d000d7e32e8001bf99340037fea9a001b7f54d000dff2a68006ff55340036faa9a001bfc54d000dffb1e8006ff98f4002dfcc7a001bfd63d00017eb1e8006ff18f4009ffea7a004f7f53d0027ff29e8013ff54f40006faa7a004ffc53d000dffa1e8006ff90f40037fa87a001bfc43d000dffb168006ff98b40005fcc5a001bfd62d00017eb168006ff18b4009ffea5a004ffe52d0027fea968013ff14b40037fe85a001bfe42d000dfea168006ff10b
  | 4 => 0x803fd6050439fe3028201bf181410effea0a0873fe505043bfea82821cff141410e7fc80a081bfc4050439ff182821cff0c1410e7fc40a0873fc2050405ff8828202fdc4141017fc20a080bfc105040bffb2e6205bfd973102ffccb9880efe65cc40bbf32e62039f9973102ffacb9886efd65cc40bbeb2e62009f5973102ff8cb98816fc65cc40bffb266205bfd933102ffcc99881afe64cc40bfeb266200bf5933102ff8c998816fc64cc437ffaa6621bdfd53310dffca99886ffd54cc401beaa6621bff15331015fcc798817ff53cc40bbfa9e6205ff94f3102ffaa7988177d53cc40bfe29e6205ffd0f3102ffc8798817fd43cc40bfe21e6205ffd8b3102ffcc598802fe62cc40bfeb166200bf58b3102ff8c59886fff52cc437ff296621bff54b310dff8a598803ff42cc401ff2166200ff50b31007f88598817ff32cc40bff1966205ff4cb3102ff8659880afd61cc405ffa8e6202ff94731017faa39880bfc51cc405ffa0e6202ff90731017fa839880bfc41cc405ff18e6202f78c731017ec639880bfc31cc405ee18e6202ff88731017f84398817ff60cc40bff3066201bf9833102ffac198802fd60cc40bfe3066201bf183310dffea19886bfe50cc437fea86621aff143310d7fc819886bfc40cc40bff1866205ff0c3310d7fc419886bfc20cc405ff8866202ff84331017f82198867ff654c4337fb2a6219ff9953101dfcca98867fd654c4337eb2a6219ff1953101df8ca98803ff644c4017fb226200ff99131035fcc898803fd644c4017eb226200ff19131035f8c898867ff544c433bfaa26219ff951310cffaa8988037d544c433fe2a26202bfd8d310cffea6988677f534c40bff29a6219ff54d31006faa698817fc534c401ffa1a6205ff90d31007fa8698817fc434c401ffb126200bfd8931007fcc498803fd624c401fe3126200bf189310cffea498867fe524c433fea926219ff14931007fe8498803fe424c401fea126200ff1093102ffe6498803fe324c401fe9926205ff0c931015fec29880bff514c405ff28a6202ff54531017f8a29880bff414c405ff20a6202ff50531017f8829880bff314c40bfb98a6202ff8c531017bc629880bfc314c405ee18a6202fd0c531017fc429880bfc214c401ffb026200bfd81310c7fcc098806fe604c401feb026218ff1813100df8c098867ff504c431ff2826219ff541310c7f8a098863fe404c431fe2026218ff8c13102ff86098863fe204c431fe1026202ffc4131017fc209880bfc104c413ffb2e4217bfd97210bffccb9080efe65c842ffeb2e4217bf5972104ff8cb9080efc65c8413ffb264200bfd9321007fcc99081afe64c8401feb264200bf5932104ff8c99081afc64c842fffaa64217dfd53210bffca99085ffd54c8401beaa64217ff1532104ffec790802ff63c8401f
  | 5 => 0xc3211dfcc41908bff520c813ff2906422ff5483204ff8a419003ff420c813ff2106400ff5083204ff88419017ff320c80bef9906409ff8c83202fdc6419017fd320c801ee9906405fb4c83204ffec219017fe610c8057f3086405ff58432005fac219027fc610c8057e3086422ffd443210ffca21908bfd510c843fe2886421ff9043210ff88219017fe310c843ef1886405ff0c43202fb86219087fe210c813fe1086409ffd803202ffcc019006fe600c80bfeb006400bf5803204ff8c019006fc600c845ffa806420ff94032117faa019083fc500c841ff2006420ff1003202ffc6019017fc300c841ff1006409ff0803210ffe2019083fe100c841fe0806406ffd9741035fecba081bfe65d04077f32e8206df9974101cfccba081bfd65d043f7eb2e8206df59741004facba081bfc65d040d7e32e8202bf99341037fea9a081b7f54d040dff2a68206ef95341037faa9a081b7d54d043fdeaa68200cf55341037f8a9a081bff63d040dff31e8205bf98f41037fac7a0802fd63d040dfe31e821fffd4f410fefea7a087ffe53d043ffea9e8200df54f410fff8a7a081bff43d040ddfa1e8206ff90f41037fa87a0803bd43d040dfe21e8206ffd8b41037fcc5a0802fe62d040dfeb168200bf58b41037f8c5a087fff52d043fff296821fff54b410fff8a5a081bff42d040dff2168206ff50b41037f885a0803ff32d0401ff1968200ff4cb41007f865a080afd61d0405ffa8e8202ff94741017faa3a080bfc51d0405ff20e8202ef90741017ec83a080bfc41d0405de20e8202ff8c741017f863a080bfe21d0405fe10e8206ffd8341037fcc1a0806fe60d040dfeb068200bf58341037f8c1a0806fc60d043fffa86821eff943410fffaa1a087bfc50d040dff2068206ff103410f7fc61a087bfc30d043dff106821eff08341017fe21a080bfe10d0405fe086821dffd95410edfecaa0877fe65504077f32a821dff595410edfacaa0877fc65504077e32a8202bfd91410effea8a08777f545040dff2a2821def951410effaa8a08037d545043bdeaa28200cf55141037f8a8a0803ff63504017fb1a8200ff98d41007fac6a0803fc635040b7e31a821dffd4d410eefea6a0877fe535043bfea9a8200df54d410eff8a6a081bff4350401dfa1a8200ff90d41007fa86a0803bd435040dfe21a8200ffd8941005fec4a0803fe6250401feb128200ff18941005f8c4a0877ff525043bff292821dff549410eff8a4a081bff4250401ff2128200ff50941037f884a0803ff3250401ff1928200ff4c941007f864a080aff6150405ffa8a8202ff94541017faa2a080bfc5150405ffa0a8206fdd0541017fc82a080bbe4150405fe20a8202ef10541017e882a080bfe3150405fe18a8202ff88541017f842a0803ff60504017fb02821cff9814100dfcc0a0
  | 6 => 0xbffb066405ff9833200dfcc199017fd60cc8017eb066405ff1833200df8c1990afff50cc853ff286642bff5433214ff8a1990a7fe40cc853fe2066405ff8c33202ff861990a7fe20cc853fe106642affc433214ffc21990a7fc10cc813ffb2c6423bfd963211ffccb1900efe658c847feb2c6423bf5963204ff8cb1900efc658c813ffb246400bfd9232007fcc91901afe648c801feb246400bf5923204ff8c91901afc648c847ffaa46423dfd523211ffca91908ffd548c801beaa46423ff15232135fac71908fff538c847bfa9c6405ff94e3211ffaa7190037d538c80bfe29c6400ffd0e3202ffc8719003fd438c80bfe21c6405bf98a3211ffea519027fe528c847fea946409ff14a32007fe8519027fe428c801fea146409ff10a3202ffe6519003df328c80bf79946409ffd8632147fcc31900afe618c801feb0c6400bf5863204ff8c31900afc618c847ffa8c6428ff9463211ffaa3190a3fc518c851ff20c6428ff10632147fc63190a3de318c80bfe18c6428f70c632147fc4319027fc218c813ffb046427ff9823200dfcc119003fd608c8017eb046409ff1823200df8c11908fff508c84fff2846423ff5423213ff8a11909ffe408c84ffe2046427ff8c23202ff8611909ffe208c813fe1046428ffc423213ffc211909ffc108c84dffb2a6426bfd9532137fcca9900efe654c84dfeb2a6426bf59532137f8ca9900efc654c801ffb226400bfd9132007fcc89901afe644c801feb226400bf59132007f8c89901afc644c84dffaa26426dfd5132137fca89909bfd544c801beaa26426ff15132137fea69909b7f534c80bff29a6426ff54d32006faa699017fc534c801ffa1a6405ff90d32007fa8699017fc434c84dffa926426ff94932137faa49909bfc524c801ffa126400ff90932007fa8499003fc424c80bff9926405fbcc932007fc6499003de324c801ffb0a6400bfd853212ffcc29900afe614c801feb0a6425ff18532015f8c29909bff514c84bff28a6426ff5453212ff8a299097fe414c84bfe20a6425ff8c53202ff86299097fe214c84bfe10a6400ffd8132005fec099093fe604c8037f3026400ff58132127f8c099006fc604c84dffa826424ff94132137faa099093fc504c849ff2026424ff10132127fc6099017fc304c849ff1026424ff0813212ffe2099093fe104c849fe0826409ffd943202dfeca19017fe650c8077f3286405df9943201cfcca19017fd650c8457eb286405df59432004faca19027fc650c80b7e3286409ffd903202dfec819017fe640c80d7f3206405ff59032005fac819027fc640c80b7e3206422ffd5032116fea81908bfe540c845feaa06400df55032117f8a819016fe630c80bffa986405dfd4c3202ffca619017fd530c80bbea986405ff14c3202ffe8619017fe430c80bfea186405ff1
  | 7 => 0xa10caff6550865ff32a8403bf99542197facaa10cafd6550865fe32a8403bf19542197fea8a10cb7f545080dff2a28432ff55142006faa8a101bfc5450801ffb1a8400bfd8d42007fcc6a1003fd6350801fe31a8405bf18d42197fea6a10cb7f5350865ff29a8432ff54d42006faa6a10cbfc535080dffa1a8400ff90d42007fa86a101bfc4350865ffa928432ff94942197faa4a10cbfc525080dffa128406fbd0942007fc84a1003be4250801ffb0a8400bfd854218ffcc2a100afe6150801feb0a8431ff18542015f8c2a10cbff5150863ff28a8432ff5454218ff8a2a10c7fe415080dfe20a8431ff8c54218ff862a10c7fe2150863fe10a8400ffd8142005fec0a10c3fe60508037f3028400ff58142187f8c0a1006fc6050865ffa828430ff94142197faa0a10c3fc5050861ff2028406ff10142187fc60a10c3fc3050861ff1028430ff0814218ffe20a10c3fe1050861fe0828409ffd9442035feca2101bfe65108077f3288406df9944201cfcca2101bfd651085d7eb288406df59442004faca21027fc651080d7e3288406bf99042037fea82101b7f541080dff2a08406ff55042036faa82101bfc5410813ffb188406ff98c4202dfcc62101bfd63108017eb188409ff18c42177fea6210bb7f531085dff298842eff54c42006faa6210bbfc531080dffa188406ff90c42037fa862101bfc431085f7f310842effd484204ffca4210bbfd5210813fe2908406ffd08420377e8421027fe421080df72108406ff508420077a842101bed4210813ffb088406ff98442015fcc22101bfd61108017eb088409ff18442015f8c2210bbff511085bff288842eff5444216ff8a22101bfe411080dfe208842dff8c44216ff862210b7fe2110813fe1088409ffd8042037fcc021006fe601080dfeb008400bf5804204ff8c021006fc601085dffa80842cff94042177faa0210b3fc501080dff200842cef90042037f8802101bbc4010859ff180842cff0c042167fc4021027fc201085bff880842cff84042167f82021017ff65cc80b7fb2e6405ff9973201dfccb990177e65cc8073f32e6405ff5973215dfacb990177d65cc8013eb2e6405ff1973202df8cb99017ff64cc80b7fb266405ff99332035fcc999017fd64cc8017eb266405ff1933202df8c9990afff54cc857bfaa6642bff9533215ffaa9990037d54cc857fe2a66405ffd4f3202efea799017fe53cc80bfea9e6405df54f3202ff8a799017ff43cc80bff21e6405ff50f3202ff887990afff52cc857ff296642bff54b3215ff8a599003ff42cc801ff2166400ff50b32007f88599017ff61cc80bff30e6402bf9873202ffac399002fd61cc80bfe30e6402bf1873215ffea3990abfe51cc857fea8e642aff14732157fc83990abfc41cc80bff18e6405ff0c732157fc43990abfc21cc80
  | 8 => 0xf99043037fea82181b7f5410c0dff2a08606ff55043036faa82181bfc5410c0b7f3188605ffd4c4302efea621817fe5310c0bfea988605df54c4302ff8a621817ff4310c0bdfa188605ff90c4302fbc8621817fd4310c0bdea188606f750c4302ffec421817fe6210c017f3108605ff58843005fac421817fc6210c75ffa90863aff948431d7faa4218ebfc5210c0bffb088605ff98443015fcc221817fd6110c017eb088605ff18443015f8c2218ebff5110c73ff288863aff544431cff8a22181bfe4110c0dfe2088605ff8c44302ff862218e7fe2110c73fe1088605ffd804302ffcc021806fe6010c0bfeb008600bf5804302ff8c021806fc6010c75ffa808638ff940431d7faa0218e3fc5010c0dff2008606ff1004302ffc6021817fc3010c71ff1008638ff080431cffe20218e3fe1010c71fe0808606ffd9742035fecba101bfe65d08077f32e8406df9974201cfccba101bfd65d086f7eb2e8406df59742004facba101bfc65d080d7e32e8406ffd5342036fea9a101bfe54d080dfeaa68406df55342037f8a9a101bff63d080dff31e8405bf98f42037fac7a1002fd63d080dfe31e8437ffd4f421befea7a10dffe53d086ffea9e8400df54f421bff8a7a101bff43d080dff21e8406ff50f42037f887a10dfff52d086fff2968437ff54b421bff8a5a101bff61d080dff30e8402bf98742037fac3a1002fd61d080dfe30e8402bf187421bffea3a10dbfe51d086ffea8e8436ff14742037fc83a101bfc41d086dff18e8436ff0c7421b7fc43a10dbfc21d080dffb068406ff9834200dfcc1a101bfd60d08017eb068406ff1834200df8c1a10dfff50d086bff2868437ff543421aff8a1a101bfe40d080dfe2068435ff8c3421aff861a10d7fe20d086bfe1068436ffc43421affc21a10d7fc10d0813ffb2c842fbfd964217ffccb2100efe659085ffeb2c842fbf5964204ff8cb2100efc65908657eb24842fffd524217efea92101bfe549085ffeaa48400df55242037f8a921027ff6390801ff31c8405bf98e42007fac721002fd6390813fe31c842fffd4e4217efea7210bffe539085ffea9c8400df54e4217ff8a72101bff4390801ff21c8400ff50e42037f8872101afe629085fffa948409ff94a4217ffaa521027fc529080dffa148400efd0a42037de8521027ff6190869ff30c8402bf98642007fac321002fd6190813fe30c8402bf1864217ffea3210d3fe519085ffea8c8434ff146421a7fc832101bfc4190869ff18c8434ff0c6421a7fc4321027fc2190813ffb048433ff9824200dfcc121003fd60908017eb048409ff1824200df8c1210bfff5090867ff284842fff5424219ff8a1210cffe4090867df2048406ff1024219f7881210cffe3090867fe1848433ff8824204ff841210d3ff1090867ff0848433ff04242197feca
  | 9 => 0xc0dbfaa68606ff95343037faa9a181b7d54d0c0dfe2a68643ffd4f4321efea7a1817fe53d0c87fea9e8600df54f4302ff8a7a181bff62d0c0dff3168600bf98b43037fac5a1802fd62d0c0dfe3168643ffd4b4321ffca5a190ffd52d0c87fe2968606ffd8743037fcc3a180afe61d0c0dfeb0e8600bf58743037f8c3a180afc61d0c87ffa8e8642ff9474321ffaa3a190bfc51d0c0dff20e8606ff10743217fc63a1817fc31d0c85ff10e8642ff08743037fec1a181bfe60d0c037f3068606ff58343005fac1a181bfc60d0c037e3068643ffd434320ffca1a190ffd50d0c83fe2868606ff90343037f881a1907fe30d0c0bfe1868641ff8834320ff841a190bff10d0c83ff0868641ff0434302ffecb21816ff6590c0bff32c8603bf9964302efccb2180e7e6590c0bfeb2c8640bf5964302efacb218027d6590c0bfe32c8605bf196431edfac921903ff5490c81bfaa48606ff95243207faa9218037d5490c0dfe2a48605bf98e4302ffea7218177f5390c0bff29c8605ff54e4302efaa721817fc5390c0bffa1c8605efd0e43037be8721817ff6290c0bff3148600bf98a4302ffac521802fd6290c0bfe3148640ffd4a43207fca521903fd5290c81fe2948605ffd864302ffcc32180afe6190c0bfeb0c8600bf5864302ff8c32180afc6190c81ffa8c863fff94643207faa3218fffc5190c7fff20c8606ff1064302ffc6321817fc3190c7fff10c863fff0864302ffec121817fe6090c037f3048605ff58243005fac121817fc6090c037e3048640ffd42431f7fca121903fd5090c7dfe284863eff90243037f88121817fe3090c0bfe184863eff882431f7f841218ffff1090c7dff084863eff042431effecaa18f6ff6550c7bff32a8603bf995431eefccaa180e7e6550c7bfeb2a863dbf59543006facaa18027d6550c7bfe32a8603bf195431effea8a18f77f5450c0dff2a2863dff55143006faa8a181bfc5450c7bffa9a863ddfd4d4302ffca6a18f7fd5350c01bea9a8605ff14d43037fe86a181bdf4350c0bff21a8605ef90d43007fec4a1802ff6250c01ff3128600ff58943007f8c4a1802fc6250c7bffa92863dff949431effaa4a18f7fc5250c01ffb0a8600bfd85431e7fcc2a180afe6150c01feb0a863cff18543015f8c2a18f7ff5150c79ff28a863dff545431e7f8a2a18f3fe4150c0dfe20a863cff8c54302ff862a18f3fe2150c79fe10a8600ffd8143005fec0a18effe6050c037f3028600ff581431dff8c0a1806fc6050c7bffa82863bff941431effaa0a18effc5050c77ff2028606ff101431dffc60a1817fc3050c77ff102863bff081431e7fe20a18effe1050c77fe0828605ffd944302dfeca21817fe6510c077f3288605df9944301cfcca21817fd6510c757eb288605df59443004faca21817fc6510c0b7e3288606b
  | 10 => 0x1007400200401400e00003602400000400200008a00000601a00202a00400200001200200000400000600c00200201800800a00000c01404e00600400400a00001200003c00000601a00002a00600002406600c00a03400800c01a01a00000001c04c00200c00802600401600401400200002000604600600002e00000600000000000c00206a00a02200000600a00400e01001000806c00a00e01000a00008800000c00000200a00002200200a00000400401004a00400203001400e00c00002a00a01400401800a00000400000401800000800e00600c00e03400000a01201c00600008600002600000a00000000000a00600400400e00807c00001c00200a00601a00200000201c00002c00c05e02200000a01000200000a02200400000600200600200006a02200004a00a02600808800a00800200e00200c00200203a00000208600200c00200000a00400c00000600805603e01600604200a00002800000400402a00200200c02c00000000200e00004000a03600200003800215800c02000003600a00003000400c00401206200800400000001201400a00003001600003200400400000e00002c00204c01400000000000007c00001600202401e00200000000001600002800800000e01000600201a02e00000000000600000600001200400000801800000600800200201e00a00802001c00800200201401800000401e00c00602600205e00001400a00200200e00a00402200800000200801800803205400005400201c00800601c00600601600a02600000800003200000202e00000001601002201000404800000000000003400000000001a0020020020040140040000080000000020a603a00800601e00002000400803e01405e00002c03dfd915401cfec8aa00f3f6455001bfb1aa8009fd8d54006fcc6aa0037d6355001be31aa800dfd8954006fcc4aa0037d6255001be312a800dfd855423efcc2aa0037d615508fbe30aa847df90554036f882aa11f7e315508fbe18aa847df8855423ef842aa0037f605508dbf302a800df58154236f8c0aa11b7e405500dbe202a846df8c154236f860aa11b7e205508dbe102a847dfc4154236fc20aa11b7c1055001bfb22a6009fd9153006fcc8a98037d6454c01be322a603dfd8d5301cfec6a980f5f6354c01bfb12a600df98953006fac4a98037c6254c01bfb0aa645df98553006fac2a99177c6154c8bbf20aa645df1055322efc62a98177c3154c8bbf10aa645df08553006fec0a99137e6054c01beb02a644df18153226fc80a99137c4054c89bf182a605df0c153226fc40a99137c2054c8bbf882a644df84153226f820a981bff65d0c0d7fb2e8606ff9974301dfccba181b7e65d0c073f32e8606ff5974321dfacba181b7d65d0c013eb2e8606ff19743035f8cba181bff54d0
  | 11 => 0x1ec1b60fc80001a8845c4540e23bd8da09628ec3dc80000005ed00000ecca28533018bc001425a077063cb2a20d16a88cce0e66e1029cf11204541b09edc15c10c38296f0dc02e74260000ca622e26e0bc40121982950300af435300d107073e00007796bc1a400000010446583190000000000000000000096000031680006da85712f90400001ed0000578cc20003520000fea5a531a04d40005a30308fa06a484f174065459a35d3bf1bf813674310a1bbc0005ca341800000056d0e1977c00022b00011f01b26871c5000000000000000005ea00000023940001a50c080008c260f0000000e961cc15198c4bce310237942cd903ef34c99dcd983940000664b7671304f85fc06c769039918cb7c4be0540000d345962b41ab45fc08b2fc8874e303e11ca80108800aa3e600005ac48201b8560bc86fa00f0da848a0003bb00000000000001e6c028000216914c10220c11109d4b0c1000a098d435e00030e000000046b0dc00000003a20000178a9e4623a78d14f5a5c700a800000074d2a6a2081047730f48d2c000272302067915c6080d39eac0003cb2c88d500c058900000000c80000000c48eb032826a00004147db3639e4000089706597a0b6027400021140004c718a955d128555134a1ac00000e41d84781907f302e23d0d4440244900009307a23e080005f42f92331e78fb85991e791fc9761a913e87d0f380004351bb400000e00202600005600802c00001801e00000600800000800002802a00600005400200400000600a03e01c00001c00600600200600000601c00201600a00000400800200a02800400000c00200e00600a00000600a01002808004800a01200c00a00e03609600c00400203c00000600803a01400e00601e02003201201c00001800400201800001000801400000000800e02000800c00809e01000400000c00002001a00a01800e02e00404600204800e00002601a09000803201e0060000d800e03400804c00202200602e00a00200000001600600600c00402000800602202400000c00203e03a00000200c00600201a01200000000200800a00000400402000802600406604401201a0000240000180000e200a00000002800006e00400000e03200a01200206e03e00000000003805000000a00401800402e05400000e00401400c01a01400e00a00000000e00000006401a00000000e00600e00000800800c02202800001201200000202e00000205c00601402a00000001001800000000000404400000c00000000400200200202e00c00402602801002c0c400601000001600001c00002400401200002c00406000201e00000803000408c01401401601c00207200000600200004007004400801001002e00a00c00004a03202a00200000002400004600000200200800400000000000400404800c012
  | 12 => 0xcc1859d15f94580001453631160000027000000002000041497b00000003069e9c9164a62708b8ca6e0001c09ba4a4e64d312a3a8088816038122006872a44d997878c0a53031048dd473d3250f8c5605d624e0000a2a85402815089c06413be800050a7a1000060c1ac0000000f480007120000f80c8800044400000000e700000009b265f37a9fb414803324900000001a12d900008720001e4a0b8d4c3a432b11342f021b42e0001092325399800000000000013a4f1200041a9d84bee38e33908d049082d0aa052054c2cf2d005e42ba03805585b4c3c3c33789d190b25342590e40a8e21636184f061c68400000004000001e299d49c60000001880f605f82b58c0000014d3db00003a68da15b8100a0e5fb2bc84e013a8440aaa1c0ba26212c280007682f723c0aa4cc400023d10cc0000bd00008f8d224360001e504305f328ba01c1425830da0a840cc80f0000bd800049b21a0e9422028e47488f50ba5a739b17491be26c0679f3865c6020cd0000b8c7bf27c20a89d43721f21a387ba1b52e703f029856e1cb9f54d9226e400150c94e0002b001e00004872b90000b5c20e27b9cece2a10b27e95f07ee89f36d88185f611c1d48b00aa28f716c15b052863612117ac2861be00000000007d70000468d248b012d899838205300014747003cc2c922e4a621f030c8000c0e88c00023b8ae85e94021b945b20003a113488183371b880000000003d200000006c51ea195cbde16413c041c7fc5b30000674a120003af116c00041840b8e9cb801024769560000338079958c0007de0000c501fc47700007d40003a33bc10591740000000000a7061200000000003d100000002640000699de482800000000000000000000ab00000001a3000000000000015d47b20a34388089180584405071d0601851fa023d02270c26f8dacf6678a07fa2640003de4258ae41ca6273b89024ac23f2019000069051a00011248540ad0000e6015e23920222b08026fb46d80011a244a1eb86584fe03c06e13783147524450f5456c82f1b7800117c8f600023840000003f5000071603a468182917887e073000000000040700010941462a6000000043c1528a880004a30000e7917a63208d98a81e85d922b8b6c01834f43f81ec88842f12c1b340003ea35b96009dc02f3e78268bb864501221e4bf472d44d025429264801507ac9001dd0430064cb48c704887480002f42bf8ae8bca1c93b19a743fe17309489e49fc82632110549da0c538215180dc2e502c95582b683f15e16984505cc11e068848c0bb409196c39677438c9e4cecc7df36597f0aba19417e87bc25a8d4242088504e83e17f8094d581f32930dc02ae0921220610e2e4a41f981dc00e3da1b283e0e1669e1a39ae8d705241759be4e745a808a821c3b266d3a51360a941ca06fa1350686be
  | 13 => 0xd20780000001cf00010910c65620000d083fc3bd3d8807c1984dd0e311b4ae23bf03696ac2ea0002360014d2a4a92648e1c05612205980006fa88b023946cc1682c2219f4000040632702580002ea3f710b858200000000000720000560c3c00000004c000045a76d0001fdc00017a1ac0000c864ac2e7912d0f473f00000010c40bf00003d405a8a71e083f4c9228132c95650302950688a407640000f38a7c20c0b815a01300000d81d681588a40003111e2cbec67b1cc9fac7507e60000000b0e6ca05304a087669600000d400002c44710849883d31a7025cda00fa14ea1c83f01ec31f1dc89268c43fd8c58ffa000121800099a0001939f4c90a0000000ea81d078c2e991d4f328dc38e8c0c62240841089a03560f03848d98cfa49e469a06c5182ec262893cd783910962318b1c71628f9a2c45e0b51439ef0be473136a8bf04f428308f85b03108dd107a1cc9987c03f00bb8fe409e3fc80c105038d0248d585621ad3c00fac0005ea15c09f10bc3313f6129477c68c18408c4e446740f1238c3aa6bb1e1186d10036900002409fe64c22e93406f206812a2040cec24c02e8be0660263275a2700461261420c2c4de7081cd064013272817680b80be71000008fc00026b095800000037700008c00c600000006e4aee41e32a9f60e1e0001908fe400012f2800d100008b33e480000000000001d200000000000e180002c306f2280bdc000346867058400023c8000b480000001b4811a71f199800116a6bf30c14340f232a0f88a78aa64f01ab8c14ab400b13d8c7cf2c4250418058ff816000005f8a6a8d541c0000e6a4b60ba1a4c4a248e00000008fc7701dc92282f839b35882c808c5a23f087e80000001dd000000081935e800000006c308194800038f19d13bc8360c20e70b980002ef09f89943fa000221070064870a2be8b7c45214029c93b000062400020c80000520fb80005b82321eb000009a4ab2cf800088a6262cd99949a20ea05c88788ac5661cb0564bea7503dc16f41d200000005ac6d88b109d95ec2cc567352800053246711b9b3d06200042d01a863a7aa0b100009cc6af1369eb87183492eb8dec59c37836e1bc10a260514d232cbaa27e3d0044832e85824492a8e3858110a87ecc2e55021813580006133b10000c127d630898e8f7c14a0dd224460444c0ea0424a9c8cc4799d2449c7380000fb0564820088a3042c62773e40f7c00067e24e97151e08873b018cc00079f0c300007380002e0800000000036b2278dce82243d9f7487c5b12071f44b7e5a934084dcc8e49f393120451a3730000000e465981848460d1e37615d9d5ca6400016217980825fd06680f910c00012a9c0097e0001d59d44ea600f2e6806c9223c43a285f4a5637c16f1ad102677525b83248aa07c03e9e984e65d819d992c01a15a2069ee
  | 14 => 0x8018e6291298e74e028b245585c80b65543610f3838405439709c02d21f600c06f410a62e0c698dcca813a11a9308d6c2082a2892861a1913dd0980dbc00043e8b200ea7d924b000c54e69f31196783ac70318b8fd45c422600e9cacc2a7c332800000004af0bb9230bb64c60ef1304a7419f0b40974000000000144cab67d21c1878000004300021948fa0d500023bc09e5d40001668e6e7e825a9a80000785000228855c76506a0cb421056530f94bc3a05492ae1780d565c343380200006141c4800095c6e200003b10d8202000073501887c4320b503ca84e3af95a4f0e3643ac86ec3887a846b2008e5e6f818d89847405304331a503161363aa97403905c216b8d286ea0eb1ac8810b168c23bf800000076a0b088802e02670000000b708d82db21b800063d40f98ac34843846689703f243d1f299801da33f27114cca7800033c00fd1d67923aa00010a00001b11e38fc639300013540004e423a05a900200024a800103a00012c8434dc81c50a213e47b60a01bf81940000f60d7163c000000000172476e0000f400000000fb1aa97744ec0001f681c800087519e1b102460003a3800082e3504629ef4c2c50a37e000000000027d8c4c69800022c98680001df386965c00000000011a0ede3ee461852cb387670ab148476c0000001f140000001388de800047200000000000002e2000030e43244e81fc0241270f308e80007da3c106f0f964901d09e688e03fb420908840e5fe00002f069a2b53e1143ca0429703f0eec0223430f0a29066884300021000008e43ab0000f2a8b60000a446b40000b7038000029608080008ca38231416a89668a1000000058a0801f3220402666f00000005b445f12b86488e644e3c791680000004210fd8bb475b15000000003dc24794d8f8c83619f14f811c42614d96209e419b0008d8c11201c2fa229498062f1c4060804273e0ed19c06e833d2652120806578278960816c1ac0250840c787e52b815210067f646922b49d05b9213876c51e6a72f1a1191907640df94440004cb22300009901b62c691043c68961599438d5000002704285a06f243b0270bc206233594ec1b66f40a1048036e8e04468000cc60da10b82e80001b036c98e420683d2bf0b44ade4bd1bf1ad4eba8393da853d06e4f408ca068cf482b4198f009504b917219b000076b17019f08e221a25a02203c8201082997000035e113951005044f47a82510b61fc36980009287f83c21c089e64e709280000005030a888907a03320a70d7c40667129f800000032b2a922d0000000390197400051e1830e98c8011320f80002085f112922a4cd44054118000b142e119ca11c9402cb33300000000002b9800082618c12b0000cb066436b8000e281761da8b1834000024317fcc7000045d8ecc6146fd00012b40002922039a40e4811
  | 15 => 0x1ddc48085522f04c4a444da1650cd4e888e80720a00f888b735485c42420e11090aacd00889120944044a0933f4800098646441d0b480aa3ac1a0a214cf23672da12e90128e61f121dca5c24b246a20c0008bf00022a861821c37b035c83a0263c41ed0e5210e3d90a4c00026a21888d8e348a33340c88a580000000000a8232f157a1491928690001b8cabc6c03429cc000000000016d40000e338890a45480000001de8b6e2861b71c3863880d210051ca30000087935d1b20000001ea50de6c140306cd0d0688333941088e00013100000002bd28a1eb00000003d294480004bc3ff16306524b80589bcc6405c80000f9c08a49717991ecf2243f00010e80001b22d08f20b202193b714f4c8c0f11d7224ca0c15234100000004fc2c982d10f083c0d89ac8f024e539a0fa47780c435c902c2de07602c099034604803385400008f236f800090600008a2328e0c56a0921a6c8140001d80ba40000004540c8c6021ee1e68ffc3b081416e8e14a4622c0a9914422c69c43080081ee0710001b740003fd18f18000847d41f804cd11e78609e959019c8241dc0ebca382a814400181ba4a10eb9b3800075a3008c600e86694028cd83a215c296934c9341390650a70fe803114503e42be71b430028831c130282882cb587fa0ee000044686d46b82c000055f2ca22e049a304357000068068a01498380006d121196b44708e242b0b1ce802ad39c9fc0f5e72c38f14310be42b2dd01acf1a35c34480007f000004211d879462c14c193c51201740589404bc7e70c99d70d428cf2ef1c9c9b60c11ada378a1040021b8698d6021100004d0dd82c933f9b681e47ca3a09fbcef805147898ec7f800000005950e80a70259a8c8503b13e3a2544921800000824c607cd1b023389f444805b914025452815f1d3815208a34ba2bcddc4354530000598000034a07800021309700000002aa3432020a522f247c0168f067682e58318dcc79720d1ffc476000267978800000035987a8dd60002350000dfe000000146472400000000000006aa0461a600007e2010126400000000010b00f45012670b4c0ae7980618fc43502820c49bdc9ec3fa0001e8cf3a0002349db103828b0000000000000000087caec5f00002260ce60003a60f1ca4a0d00f9000017c54b1c2117000052036a13d504a6e83f895000000000000c9902a4a230ea39c2ce7210bd86a910813e2370c6883230701e9cc800006f3708000c7e24739291
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd75cc9100067f65cc91015e7c65cc910006ef62cc910006ec62cc91000dfa70cc910005f970cc91004cff768c910004fe768c910004fd768c91004cfc768c9100067f658c91011e7c658c910006df638c91002edc638c910015f6718c910005f5718c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101367c654c91000dfa704c91004cff760c910004fe760c910004fd760c91004cfc760c9100257e750c9100057d750c9100067f650c9101167c650c910006df630c91002edc630c910006ef620c91004eec620c910015f6710c910005f5710c91000dfa700c910005f9700c91000df47650510036f4765051000cf4765051000777655051025f746550510015f77450510017b77450510007b76450510036f66450510036f46450510007b4645051025f77545051025fb6545051000775545051025fb5545051000735545051025f775350510007755350510007b74350510007b54350510005f77250510007f3705051000df6705051000df470505100e7f07050510016f76050510017f360505100e7f230505100e7f2205051000df476485100a6f4764851000cf47648510007777548510257747548510007776548510257746548510005f77448510005f57448510257775448510007755448510007d77348510007d47348510257775348510007755348510015f77248510017e77248510007e7624851004ef6624851004ef46248510007e46248510007e63248510007e53248510007f3704851000df6704851000df470485100a7f07048510016f76048510017f360485100a7f230485100a7e720485100a7f220485100a7e52048510015f8764c11002ef8764c110014f8764c1100077b654c11024f78654c11024f7b544c11000779544c11000dfb734c11000fdb734c110007db634c11002efa634c11002ef8634c110007d8634c11024f7b534c11024fda534c11000779534c11024fd9534c11000759534c110007da434c110007d9434c110005fb724c110007f3714c110015fa714c110015f8714c110067f0714c11000efb614c11000ff3614c110067f2414c110007f1414c110067f2214c110007f1214c110015f8764811003ef87648110014f876481100077b75481102477875481100077b6548110247786548110007bb7448110007b874481102477b5448110007795448110005fb7348110005f973481102477b534811000779534811000dfb724811000feb7248110007eb624811004efa624811004ef86248110007e86248110007ea4248110007e94248110007f37148110015fa7148110015f8714811003ff0714811000efb614811000ff3614811003ff24148110007f1414811003feb214811003ff2214811003fe92148110007f12148110007e12148110
  | 1 => 0x89100067f54d89100067d54d891002cfe73d8910004fd73d89100067f53d89100067d53d891000cff71d891000cfd71d891027eef21d891027eed21d8910014ff70d8910014fd70d8910276ef20d8910276ed20d89100a4fd76989100257e75989100057d75989100067f65989100067c6598910006ef62989100a5f5719891003df9709891004cff759891001cfe759891004e7e759891001c7e7598910004fd759891004e7d75989100047d759891004cfc7598910034fe7498910004fd74989100067f54989100067d549891002cfe7398910004fd73989100067f53989100067d539891004cfe72989100a4fd719891004ef5719891004ef621989100b4fd709891004ef9709891004efa20989100057f75589100257c75589100067f65589100067c6558910005bf7458910005bc7458910005df7358910005dc73589100b5f77158910055fb7058910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910034fc7458910006bc7458910034bc74589100067f54589100067d5458910004ff7358910006df7358910004df735891002cfc7358910006dc735891002cdc73589100067f53589100067d5358910006ef72589100b4ff7158910006f771589100a4ff7058910006fb7058910274fe76189100067f65189100067c6518910006ed621891004cff751891001cfe7518910004fd751891004cfc7518910034fe7418910004fd74189100067f54189100067d541891002cfe7318910004fd73189100067f53189100067d531891004cfe721891004eee721891000cff7118910014fe711891000cfd711891004ef57118910014fc711891004eef211891004ef6211891026eed2118910014ff701891000cfe7018910014fd701891004ef9701891000cfc701891004eef201891004efa2018910266ed2018910034ff76d0910004fe76d0910004fd76d0910034fc76d09100257e75d09100057d75d09100067f65d09101be7c65d0910006ef62d0910006ec62d0910015f671d0910005f571d091004cff7690910004fe7690910004fd769091004cfc76909100067f659091017e7c6590910006bf6490910036bc6490910015f67190910005f5719091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101967c6550910015f6715091004cff7610910004fe7610910004fd761091004cfc76109100257e75109100057d75109100067f65109101767c6510910006bf6410910036bc6410910006ef621091004eec6210910015f67110910005f5711091000dfa7010910005f9701091002cff76cc910004fe76cc910004fd76cc91002cfc76cc9100257e75cc9100057
  | 2 => 0x67f65d8d100067c65d8d10004ff75d8d100067f75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d100067c75d8d1001c7c75d8d10034fe74d8d10004fd74d8d100067f54d8d100067d54d8d100067f53d8d1004cfe72d8d10004fd72d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d1029edf31d8d1029edd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d10296df30d8d10296dd30d8d100c4fd7698d100257e7598d100057d7598d100067f6598d100067c6598d10006df6398d100c5f57198d10065f97098d1002cff7658d100057f7558d100257c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10005ef7258d10005ec7258d100d5f77158d10075fb7058d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10034fc7458d10006bc7458d10034bc7458d100067f5458d100067d5458d10006df7358d100067f5358d10004ff7258d10006ef7258d10004ef7258d1004cfc7258d10006ec7258d10004ec7258d100d4ff7158d10006f77158d100c4ff7058d10006fb7058d10294fe7618d100257e7518d100057d7518d100067f6518d100067c6518d1002ede6318d10006dd6318d100067f7654d100057e7654d100067e7654d100047e7654d100067d7654d100057c7654d100067c7654d100047c7654d100057f7454d100067f6454d1028e7e6454d100067d6454d1028e7c6454d102857f7354d100275f7354d100067f6354d1002e7e6354d100067d6354d1002e7c6354d10007777154d1022f747154d102267f6154d1022f764154d1022f762154d102267f6054d102275f3054d102277a3054d102275d3054d102277a2054d1022f7b1054d10227761054d10227741054d10227781054d10034ff76d0d10004fe76d0d10004fd76d0d10034fc76d0d100257e75d0d100057d75d0d100067f65d0d1021e7c65d0d10006df63d0d1002edc63d0d10015f671d0d10005f571d0d1002cff7690d10004fe7690d10004fd7690d1002cfc7690d100257e7590d100057d7590d100067f6590d102067c6590d10006bf6490d10036bc6490d1000dfa7090d10005f97090d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100257e7550d100057d7550d100067f6550d101ee7c6550d1002cff7610d10004fe7610d10004fd7610d1002cfc7610d100257e7510d100057d7510d100067f6510d101d67c6510d10006bf6410d10036bc6410d10006df6310d1002edc6310d10015f67110d10005f57110d1000dfa7010d10005f97010d100067f65d89100067c65d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910034fe74d8910004fd74d
  | 3 => 0xa30d95102c77a20d95102cf7b10d95102c77610d95102c77410d95102c77810d95100067f74d95100067e74d95100067d74d95100047d74d95100067c74d95100067f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f72d95100067e72d95100067d72d95100067c72d95102c67f71d95102ce7e71d95102c67d71d95102c67c71d95102ce7f41d95102ce7e41d95102ce7d41d95102ce7c41d95102ce7f31d95102ce7e31d95102ce7d31d95102ce7c31d95102ce7f21d95102ce7e21d95102ce7d21d95102ce7c21d95102c67f70d95102c67e70d95102c67d70d95102c67c70d95102c67f40d95102c67e40d95102c67d40d95102c67c40d95102c67f30d95102c67e30d95102c67d30d95102c67c30d95102c67f20d95102c67e20d95102c67d20d95102c67c20d95102c67f10d95102c67e10d95102c67d10d95102c67c10d9510034fe76d91100257c75d91100067f65d91100067c65d9110004ff75d91100067f75d911001cfe75d9110004fd75d911001cfc75d91100067c75d911001c7c75d91100067f54d911002cfe73d9110004fd73d91100067f53d911004cfe72d9110004fd72d911000cff71d9110014fe71d911000cfd71d9110014fc71d91102bebf41d91102bebd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d91102b6bf40d91102b6bd40d91100e4fd76991100257e75991100057d75991100067f65991100067c6599110006bf64991100e5f57199110085f97099110034ff76591100057f75591100257c75591100067f65591100067c6559110005df7359110005dc7359110005ef7259110005ec72591100f5f77159110095fb7059110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110006bf74591100067f5459110004ff7359110006df7359110004df735911002cfc7359110006dc735911002cdc73591100067f5359110004ff7259110006ef7259110004ef725911004cfc7259110006ec7259110004ec72591100f4ff7159110006f771591100e4ff7059110006fb70591102b4fe76191100257e75191100057d75191100067f65191100067c6519110036be6419110006bd64191100067f76551100057e76551100067e76551100047e76551100067d76551100057c76551100067c76551100047c76551102ad7f74551100273f74551100067f64551100367e64551100067d64551100367c64551100057f73551102a67e63551102a67c63551102367f615511023f3f415511023f76415511023f3d415511023f7621551100077b70551102377870551102367f60551102377a30551102377a205511023f7b105511023776105511023774105511023778105511002cfe76d8d100257c75d8d10
  | 4 => 0x8520004fd75d852001cfc75d8520034fe74d8520004fd74d85200067f54d85200067d54d852002cfe73d8520004fd73d85200067f53d85200067d53d852000cfd72d8520014fc72d852003ef431d852003ef621d852000cfe70d852000cfc70d85200b6f710d85200057f75585200457c75585200067f65585200067c6558520005bf7458520005bc7458520006bf6458520006bc6458520005df7358520005dc735852003ef46158520004fe76d0520004fd76d0520034fc76d05200457e75d05200057d75d05200067f65d05200fe7c65d0520006bf64d0520036bc64d05200073d54d0520005ee72d0520005ed72d0520004ff7650520004fe7650520004fc76505200067f65505200ee7c6550520006bf6450520036bc64505200073d5450520004fe76cc520004fd76cc52002cfc76cc5200457e75cc5200057d75cc5200067f65cc5200de7c65cc520006bf64cc520006bc64cc520006f761cc520016f461cc520004ff764c520004fe764c520004fc764c5200067f654c5200ce7c654c520006bf644c520006bc644c520264fe76c85200067f65c85200be7c65c8520006bf64c8520006bc64c852000df870c852004fe820c8520265ee76c852027eee76c85200076f65c85202ef6c65c8520005ef74c8520005ed74c8520007af64c8520007ac64c85202ef6f54c85200076d54c8520006ef63c8520006ed63c85202ef6f53c85200076d53c85200a5ed71c8520016ee61c8520016ec61c852004feb70c852000dee70c852000dec70c852004fe870c852004eef60c85200b7ea10c852000cfc76485200057f75485200457c75485200067f65485200ae7c6548520006bf6448520006bc6448520005df7348520005dc7348520006f76148520016f4614852003fe42148520005fb704852000df870485200a7e8204852000dec7648520016ec764852000cec76485200076f75485202e76c75485200076f65485202e76c6548520005ef7448520005ed7448520007af6448520007ac64485202e76f54485200076d5448520007cf7348520007cc7348520006ef6348520006ed63485202e76f53485200076d53485200b5ef7148520007e77148520007e76148520016ee6148520016ec614852003fe46148520007eb704852000dee704852000dec70485200a7e870485200a6ef60485200a7e710485200a7ea104852000dfa76c812000efa76c812000cfa76c81200077b65c81202df7865c8120007bb64c8120007b864c81202df7b54c81200077954c81202df7b53c81200077953c812000dfa72c812000fea72c812000efb62c812000feb62c812004fea42c8120007e942c8120005f971c812004feb21c8120007e921c81202d57e76d95100267e76d951001c7e76d95100057d74d95100057d73d95102cf7641d95102cf7621d95102c77
  | 5 => 0x34ff76d0d20004fe76d0d20004fd76d0d20034fc76d0d200457e75d0d200057d75d0d200067f65d0d2021e7c65d0d20006bf64d0d20036bc64d0d20005ee72d0d20005ed72d0d2002cff7690d20004fe7690d20004fd7690d2002cfc7690d200457e7590d200057d7590d200067f6590d202067c6590d20006bf6490d20036bc6490d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200457e7550d200057d7550d200067f6550d201ee7c6550d20006bf6450d20036bc6450d2002cff7610d20004fe7610d20004fd7610d2002cfc7610d200457e7510d200057d7510d200067f6510d201d67c6510d20006bf6410d20036bc6410d20005ee7210d20005ed7210d2000dfa7010d20005f97010d2000cfe76d092000cfc76d09200457e75d09200057d75d09200067f65d09201be7c65d0920006bf64d0920036bc64d092000dfa70d0920005f970d09201afe820d0920164fe76909200067f659092017e7c659092019ebf6490920036bc6490920165ee7690920006ee76909200076f65909202ff6c6590920185ed749092019faf6490920036ee6490920036ec6490920007ac6490920036ac64909202ff6f54909200076d54909202ff6f53909200076d5390920005ed719092000dee709092000dec709092004eef609092019fae409092019fac409092019fea1090920034ff765092000cfe7650920184fd765092000cfc76509200067f65509201967c6550920006bf6450920036bc6450920005fb705092000df8705092000dec7650920036ec765092000cec76509200076f65509202f76c6550920007af7450920007af6450920036ee6450920036ec6450920007ac6450920036ac64509202f76f54509200076d54509202f76f53509200076d5350920005ef7150920007eb705092000dee705092000dec7050920187e8705092000de87050920186ef6050920187ea105092019cfe76109200457e75109200057d75109200067f65109201767c6510920006bf6410920036bc641092019dee721092004fe8201092000cfe76cc92000cfc76cc9200457e75cc9200057d75cc9200067f65cc92015e7c65cc920006bf64cc920006bc64cc920006df63cc92002edc63cc92000dfa70cc920005f970cc920104fe768c9200067f658c92011e7c658c920006bf648c920006bc648c92004fe8208c92002cff764c92000cfe764c920124fd764c92000cfc764c9200067f654c9201367c654c920006bf644c920006bc644c920006df634c92002edc634c920005fb704c92000df8704c920127e8204c92013cfe760c9200457e750c9200057d750c9200067f650c9201167c650c920006bf640c920006bc640c920014fe76d85200067f65d85200067c65d8520006bf64d8520006bc64d852003ef661d8520004ff75d852001cfe75d
  | 6 => 0xc7019120166bf5019120166be5019120166bd5019120166bc5019120166bf3019120166be3019120166bd3019120166bc3019120166bf2019120166be2019120166bd2019120166bc2019120166bf1019120166be1019120166bd1019120166bc10191200067f76551200057e76551200067e76551200047e76551200067d76551200057c76551200067c76551200047c76551202ad7f74551200473f74551200067f64551200073f64551200063f64551200367e64551200067d64551200367c64551200073c64551200363c64551200057f73551202a67e63551202a67c63551202367f625512023e7e615512023e7c61551202367f60551202376e20551202376c20551202377820551202377a105512002cfe76d8d200457c75d8d200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d20004ff75d8d200067f75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d200067c75d8d2001c7c75d8d20034fe74d8d20004fd74d8d200067f54d8d200067d54d8d200067f53d8d2004cfe72d8d2004cfc72d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20006dc31d8d2004cff70d8d2013cfd70d8d2013edf30d8d2013edd30d8d2013efa10d8d200457e7598d200057d7598d200067f6598d200067c6598d20005be7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d20125ed7298d200057f7558d200457c7558d200067f6558d200067c6558d20005bf7458d20005bc7458d20006bf6458d20006bc6458d2014def7258d20005f77158d2003df47158d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20034fc7458d20006bc7458d20034bc7458d200067f5458d200067d5458d20006df7358d200067f5358d2014cff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20014fe7158d20014fc7158d20006f47158d20014f47158d20124ff7058d20006fb7058d20126fa1058d2013cfe7618d200457e7518d200057d7518d200067f6518d200067c6518d20006bf6418d20006bc6418d2002ede6318d20006dd6318d200067f7654d200057e7654d200067e7654d200047e7654d200067d7654d200057c7654d200067c7654d200047c7654d200057f7454d200067f6454d200073f6454d200063f6454d2028e7e6454d200067d6454d2028e7c6454d200073c6454d200063c6454d202857f7354d200475f7354d200067f6354d2002e7e6354d200067d6354d2002e7c6354d200076f7254d200076c7254d202267f6254d2022e7e6154d2022e7c6154d202267f6054d202275f3054d202275d3054d202276e2054d202276c2054d20227782054d202277a1054d20
  | 7 => 0x912019ebf40d912019ebd40d9120034be76d91200073f75d91200073c75d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d91200073f53d912019faf72d9120006be61d9120006bc61d912019fae20d912019fac20d912019fb820d912019fba10d9120006bf75d91200063f75d9120006be75d9120006bd75d9120006bc75d91200063c75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d91200063f53d9120006be53d9120006bd53d9120006bc53d912019ebf72d912019ebd72d9120006bf52d9120006be52d9120006bd52d9120006bc52d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006be31d9120006bc31d9120006be21d9120006bc21d912019ebf70d912019ebe70d912019ebd70d912019ebc70d912019ebf50d912019ebe50d912019ebd50d912019ebc50d912019ebf30d912019ebe30d912019ebd30d912019ebc30d912019ebf20d912019ebe20d912019ebc20d912019ebf10d912019ebe10d912019ebd10d912019ebc10d91200457e75991200057d75991200067f65991200067c6599120006bf6499120185ed72991200057f75591200457c75591200067f65591200067c65591201adef7259120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c7559120006bf74591200067f5459120004ff735912002cfc73591200067f53591201acff7259120006ef7259120004ff7159120014fe7159120014fc7159120184ff7059120006fb705912019cfe76191200457e75191200057d75191200067f65191200067c6519120036be6419120006bd64191200073f541912019dbe7619120006be761912019cbe76191200073e75191200073d7519120006bf65191200073f65191200063f6519120006be6519120006bd6519120006bc65191200073c65191200063c65191200073f5319120167ad7219120006be6119120006bc6119120167ae2019120167ac2019120167b82019120167ba1019120036bf7519120036be75191200363e7519120036bd75191200363d7519120036bc7519120036bf7319120036be7319120036bd7319120036bc7319120006bf53191200063f5319120006be5319120006bd5319120006bc5319120036bf7219120036bd7219120036ad7219120006bf5219120006be5219120006bd5219120006bc5219120036bf7119120036be7119120036bd7119120036bc7119120006bf5119120006be5119120006bd5119120006bc5119120006be3119120006bc3119120006be2119120006bc2119120036bf7019120036be7019120036bd7019120036b
  | 8 => 0x4fd755872001cfc7558720004ff7458720034fc74587200067f54587200067d5458720004ff735872002cfc73587200067f53587200067d5358720014fd725872000cfc725872004ef7215872004ef421587200a6fa20587200a6f71058720034ff76d072004cfe76d0720004fd76d072005d7e75d07200057d75d07200073d54d072004dee72d0720005ed72d0720004ff7650720004fd765072004cfc76507200073d5450720005fb705072000df8705072002cff76cc72004cfe76cc720004fd76cc72005d7e75cc7200057d75cc720004ff764c720004fd764c72004cfc764c72000ded76c8720016ed76c872000ced76c872004def74c8720005ed74c872031f6f54c87200076d54c872004eef63c8720006ed63c872031f6f53c87200076d53c8720016ee61c872004fe661c872004fe561c8720016ec61c872000dee70c872004fea70c872004fe970c872000dec70c8720274ff76487200057f754872005d7c7548720005df7348720005dc7348720016f4614872004fe42148720275ef764872026eef76487200076f75487203176c7548720005ef7448720005ed74487203176f54487200076d5448720007cf7348720007cc7348720006ef6348720006ed63487203176f53487200076d534872004fe7714872004fe76148720016ee6148720016ec614872004fe4614872000dee704872000dec70487200a7e7104872030d7e76d95200467e76d952001c7e76d95200057d74d95200057d73d95200067e61d95200067c61d95203076e20d95203076c20d95203077820d95203077a10d95200067f74d95200067e74d95200067d74d95200047d74d95200067c74d95200067f73d95200067e73d95200067d73d95200047d73d95200067c73d95203067f72d95200467e72d95203067d72d95203067c72d95200067f71d95200067e71d95200067d71d95200067c71d95200067e41d95200067c41d95200067e31d95200067c31d95200067e21d95200067c21d95203067f70d95203067e70d95203067d70d95203067c70d95203067f40d95203067e40d95203067d40d95203067c40d95203067f30d95203067e30d95203067d30d95203067c30d95203067f20d95203067e20d95203067d20d95203067c20d95203067f10d95203067e10d95203067d10d95203067c10d9520034fe76d91200457c75d91200067f65d91200067c65d91200073f54d9120004ff75d91200067f75d912001cfe75d9120004fd75d912001cfc75d91200067c75d912001c7c75d91200067f54d9120006bf54d91200063f54d9120006be54d9120006bd54d9120006bc54d912002cfe73d9120004fd73d91200067f53d912004cfe72d912004cfc72d9120014fe71d9120004fd71d9120014fc71d9120006be41d9120006bc41d912004cff70d912019cfd70d
  | 9 => 0xc725932004ebe425932004ebc4259320004ff7159320014fe7159320014fc7159320186bf4059320186bd40593200067f76553200067e76553200067d76553200067c76553202ad7f745532005f3f74553200067f64553200367e64553200067d64553200367c64553200057f73553202a67e63553202a67c63553202367e625532023e7e615532023e7c61553200077b70553202377870553202367d60553202376e20553202377a20553202376c205532004cff75d8f2001cfe75d8f20004fd75d8f2004cfc75d8f20034fe74d8f20004fd74d8f200067f54d8f200067d54d8f200067f53d8f2004cfe72d8f2004eee72d8f20014fe71d8f20004fd71d8f20014fc71d8f2004ef970d8f20124fd7698f2005d7e7598f200057d7598f2004edf6398f2004edc6398f2002cff7658f2004edc6358f20004ff7558f2001cfe7558f20004fd7558f2001cfc7558f20004ff7458f20034fc7458f200067f5458f200067d5458f2004edf7358f200067f5358f2002cff7258f2000cfe7258f2002cfd7258f2000cfc7258f2004ede3258f2004edc3258f20004ff7158f20014fe7158f20014fc7158f20126df3058f20126dd3058f200067f7654f200067e7654f200067d7654f200067c7654f200057f7454f200067f6454f2028e7e6454f200067d6454f2028e7c6454f202857f7354f2005f5f7354f200067f6354f2002e7e6354f200067d6354f2002e7c6354f200076f7254f200076c7254f202267e6254f2022e7e6154f2022e7c6154f202267d6054f202275f3054f202275d3054f202276e2054f202277a2054f202276c2054f20034ff76d0f2004cfe76d0f20004fd76d0f2004cfc76d0f2005d7e75d0f200057d75d0f2004dee72d0f20005ed72d0f2002cff7690f2004cfe7690f20004fd7690f2004cfc7690f2005d7e7590f200057d7590f2000dfa7090f20005f97090f20004ff7650f2004cfe7650f20004fd7650f2004cfc7650f2005d7e7550f200057d7550f2002cff7610f2004cfe7610f20004fd7610f2004cfc7610f2005d7e7510f200057d7510f2004dee7210f20005ed7210f20184fd76d0b2005d7e75d0b200057d75d0b2000ded7690b2004eed7690b2000ced7690b20036ee6490b2004fae6490b2004fad6490b2004eec6490b2032f6f5490b200076d5490b2032f6f5390b200076d5390b20005ed7190b2000dee7090b2004fea7090b2004fe97090b2000dec7090b2019fae4090b2019fac4090b201acff7650b201adef7650b20006ef7650b2004faf7450b20036ee6450b20036ec6450b203276f5450b200076d5450b203276f5350b200076d5350b20005ef7150b2000dee7050b2000dec7050b20124fd76ccb2005d7e75ccb200057d75ccb2014cff764cb20014ff765872004ef46158720004ff755872001cfe7558720
  | 10 => 0x8930005bf7458930005bc74589300075d5358930005f77158930065f471589300075d5318930006ed621893004cff751893001cfe7518930004fd751893004cfc7518930034fe7418930004fd74189300067f54189300067d54189300067f53189300067d5318930014fe7118930004fd7118930014fc7118930006ee211893004eec211893004cff701893002cfd701893004eef2018930106ed2018930004fe76d0930004fd76d0930034fc76d093006d7e75d09300057d75d093002dde73d0930005dd73d09300075d53d0930004fe7690930004fd769093004cfc7690930006bf6490930036bc64909300075d5390930004ff7650930004fe7650930004fc76509300075d5350930005fb705093000df87050930004fe7610930004fd761093004cfc761093006d7e75109300057d7510930006bf6410930036bc641093002dde7310930005dd73109300075d531093000dfa7010930005f9701093000cfe768c9300075d538c930006ef628c93004eec628c93000dfa708c930005f9708c93000cfc764c9300075d534c930006ef624c930006ec624c930005fb704c93000df8704c930014fe76d85300075d53d8530066f661d8530004ff75d853001cfe75d8530004fd75d853001cfc75d8530034fe74d8530004fd74d85300067f54d85300067d54d853000cfd73d8530014fc73d85300067f53d85300067d53d853004cfe72d8530004fd72d8530066f631d8530066f421d853002cfd70d85300d6f710d85300057f755853006d7c7558530005bf7458530005bc74585300075d5358530005ef7258530005ec7258530066f46158530004fe76d0530004fd76d0530034fc76d053006d7e75d05300057d75d05300073d54d053002dde73d0530005dd73d05300075d53d05300079d43d0530004ff7650530004fe7650530004fc76505300073d54505300075d53505300079d435053000cfc764c5300075d534c530006f7614c530016f4614c530005fb704c53000df8704c530004fe76c8530004fd76c853004cfc76c85300075d53c8530006f761c8530016f461c8530004ff7648530004fe7648530004fc76485300057f754853006d7c7548530005df734853002ddc73485300075d534853004cff75d932001cfe75d9320004fd75d932004cfc75d93200067f54d932002cfe73d9320004fd73d93200067f53d932004cfe72d932004eee72d9320014fe71d9320004fd71d9320014fc71d932004ef970d932019ebe40d932019ebc40d9320184fd769932005d7e75993200057d759932004ebf649932004ebc6499320034ff765932004ebc6459320004ff755932001cfe7559320004fd755932001cfc755932004ebf74593200067f5459320004ff735932002cfc73593200067f5359320034ff725932000cfe7259320034fd725932000cf
  | 11 => 0x75e73551300075d73551302367f635513023e7e615513023e7c61551302367f60551302a77b30551302375e30551302375c30551302377830551302377a105513001e7f7654d302267e7654d302267d7654d3001e7c7654d300057f7454d300067f6454d3028e7e6454d300067d6454d3028e7c6454d3002d7f7354d3006f5f7354d3002e7f6354d3002f5e4354d3002f5c4354d3002f5f3254d3002f5c3254d3022e7e6154d3022e7c6154d3002f5f3154d303575e3154d3002f5c3154d300077b7054d30227787054d3002e7f6054d3002f7b3054d302275e3054d3002f5c3054d3002f783054d3002f583054d302277a1054d3006f5f7654d3001e5f7654d302275c7654d3001e5c7654d300075f7454d300055f7454d300075e7454d300075d7454d300075c7454d300075f6454d300075e6454d300075d6454d300075c6454d300075f7254d300075e7254d300075d7254d300075c7254d300075f7154d303575e7154d300075d7154d303575c7154d303575e6154d303575c6154d303575e4154d303575c4154d303575e2154d303575c2154d302275f7054d300075b7054d302275e7054d302275d7054d302275c7054d30227587054d3002f5f6054d3002e5f6054d3002f5b6054d302275f4054d302275e4054d302275d4054d302275c4054d302275e2054d302275c2054d302275f1054d302275e1054d302275a1054d302275c1054d3000cfe76d0d3000cfc76d0d3006d7e75d0d300057d75d0d30006bf64d0d30036bc64d0d300075d53d0d3000dfa70d0d30005f970d0d301c5de7690d3002ede7690d3002ddf7590d3002f5e7590d3034ddd7590d3002f5d7590d300055d7590d301dddd7490d30036de6490d30036dc6490d303475f5490d300075d5490d3000dde7090d3000ddc7090d3002edf6090d3002fdb6090d301f7da1090d30034ff7650d3000cfe7650d301dcfd7650d3000cfc7650d3006d7e7550d300057d7550d30006bf6450d30036bc6450d303375f5350d300075d5350d30005fb7050d3000df87050d3000ddc7650d30036dc7650d3000cdc7650d3033ddf7550d303375e7550d3033ddd7550d300075d7550d300055d7550d3002ddf7450d3002f9f7450d300079f6450d30036de6450d30036dc6450d300079c6450d303375f5450d300075d5450d30007db7050d3000dde7050d3000ddc7050d301dfd87050d3002edf6050d3002fdb6050d301dfda1050d300075d53d8930004ff75d893001cfe75d8930004fd75d893001cfc75d8930034fe74d8930004fd74d89300067f54d89300067d54d89300067f53d89300067d53d8930014fe71d8930004fd71d8930014fc71d8930006ee21d8930006ec21d893002cfd70d893014eef20d893014efa10d89300075d5398930006ef62989300057f755893006d7c755
  | 12 => 0xe7158b30014fc7158b30126ef2058b30034ff76d0b3002cfe76d0b30004fd76d0b3007d7e75d0b300057d75d0b301be7e65d0b300067d65d0b3002dde73d0b30005dd73d0b300075d53d0b30006ee62d0b30006ed62d0b3004cff7690b3002cfe7690b30004fd7690b3017e7e6590b300067d6590b30036be6490b30006bd6490b300075d5390b30004ff7650b30004fd7650b3002cfc7650b301967e6550b300067d6550b300075d5350b3004cff7610b3002cfe7610b30004fd7610b3007d7e7510b300057d7510b301767e6510b300067d6510b30036be6410b30006bd6410b3002dde7310b30005dd7310b300075d5310b3004eee6210b30006ed6210b30004ff755873001cfe7558730004fd755873001cfc7558730004ff7458730034fc74587300067f54587300067d545873000cfe7358730014fd735873000cfc735873002e7f535873002e7d5358730004ff725873004cfc725873002ef7715873002ef7315873002ef4315873002efa305873002ef930587300c6f71058730034ff76d073002cfe76d0730004fd76d073007d7e75d07300057d75d07300fe7e65d07300067d65d0730036be64d0730006bd64d07300073d54d073002dde73d0730005dd73d07300075d53d07300079d43d0730004ff7650730004fd765073002cfc76507300ee7e65507300067d6550730036be6450730006bd64507300073d54507300075d53507300079d435073004cff76c873002cfe76c8730004fd76c87300be7e65c87300067d65c87300075d53c873004eee62c8730006ed62c8730004ff7648730004fd764873002cfc76487300057f754873007d7c75487300ae7e65487300067d6548730005df734873002ddc73487300075d5348730006ee6248730006ed6248730034fe76d9130004ff75d913001cfe75d9130004fd75d913001cfc75d91300067f54d9130006be54d9130006bd54d913002cfe73d913002cfc73d91300067f53d913004cfe72d9130004fd72d9130014fe71d9130004fd71d9130014fc71d9130006be41d9130006bc41d913002cff70d913002cfd70d91301f6bf40d91301f6bd40d913006d7e75991300057d7599130006bf64991301dddd739913020ddf7359130004ff755913001cfe7559130004fd755913001cfc7559130006bf74591300067f545913020cff7359130006df73591300067f5359130004ff725913004cfc7259130004ff7159130014fe7159130014fc71591301dcff7059130006fb70591301f4fe761913006d7e75191300057d7519130036be6419130006bd64191300067f76551300067e76551300067d76551300067c76551302ad7f745513006f3f74551300067f64551300073f64551300063f64551300367e64551300067d64551300367c64551300073c64551300363c64551300057f7355130
  | 13 => 0x97300067c21597302267f70597302267e70597302267d70597302267c70597302267f40597302267e40597302267d40597302267c405973002e7f305973002e7e305973002e7d305973002e7c30597302267f20597302267e20597302267d20597302267c20597302267f10597302267e10597302267d10597302267c1059730004ff755933001cfe75593300067e755933001c7e7559330004fd75593300067d755933001cfc755933002ebf74593300067f545933002cff735933000cfe735933002cfd735933000cfc735933002e7f535933002e7d535933002ebe435933002ebc4359330004ff725933004cfc7259330004ff7159330014fe7159330014fc71593301debf40593301debd40593302a57f76553300067f76553300047f76553302a67e76553302a57d76553300067d76553300047d76553302a67c76553302ad7f745533007f3f74553302a67f64553300367e64553300067d64553300367c64553302a57f73553302a75e73553302a57d73553300075d73553302367e63553302a75e435533023e7e615533023e7c61553300077b70553302377870553302367d60553302375e30553302377a30553302375c305533002f5f7654f3002d5f7654f303765f7654f300075f7454f300055f7454f300075e7454f300075d7454f300075c7454f3002f5f6454f3002f5e6454f3002f5d6454f3002f5c6454f300075f7254f300075e7254f300075d7254f300075c7254f3002f5f6254f3002f5e6254f3002f5d6254f3002f5c6254f300075f7154f3036f5e7154f300075d7154f3036f5c7154f3002f5f6154f3002f5e6154f3002f5d6154f3002f5c6154f3036f5e4154f3036f5c4154f3036f5e2154f3036f5c2154f302275f7054f302275e7054f302275d7054f302275c7054f302265d6054f302275f4054f302275e4054f302275d4054f302275c4054f302275e2054f302275c2054f302275f1054f302275e1054f302275c1054f3002ddf7650f30006df7650f30365df7550f3035f5e7550f30365dd7550f300075d7550f300055d7550f3002f5e6550f3002f5d6550f3002f9f7450f30036de6450f3002edc6450f3035f5f5450f300075d5450f3000dde7050f3000ddc7050f3004cff7598b3001cfe7598b30004fd7598b3004cfc7598b30034fe7498b30004fd7498b300067f5498b300067d5498b3000cfe7398b3000cfc7398b3002e7f5398b3002e7d5398b3004eee7298b3002eef3298b3004eec3298b30014fe7198b30004fd7198b30014fc7198b3004eef2098b3013eed2098b30004ff7558b3001cfe7558b30004fd7558b3001cfc7558b30004ff7458b30034fc7458b300067f5458b300067d5458b3000cfc7358b3002e7f5358b3002e7d5358b3002eef7258b3002eef3258b3002eec3258b30004ff7158b30014f
  | 14 => 0x2edc6350d40005fb7050d4000df87050d40037b84050d40004ff75d894001cfe75d8940004fd75d894001cfc75d89400067f54d89400067d54d894002cfe73d8940004fd73d89400067f53d89400067d53d8940006ef52d8940006ec52d8940014fe71d8940004fd71d8940014fc71d8940006ee21d8940006ec21d8940034fd70d89401aeef20d8940006ef62989400057f755894008d7c7558940006ed621894004cff751894001cfe7518940004fd751894004cfc75189400067f54189400067d541894002cfe7318940004fd73189400067f53189400067d5318940006ef521894004eec5218940014fe7118940004fd7118940014fc7118940006ee211894004eec211894004cff7018940034fd7018940166be4018940166bc401894004eef2018940166ed201894000cfe769094019ebf6490940006ef629094004eec629094000dfa7090940005f97090940037b8409094000cfc76509400073d5450940006ef6250940006ec6250940005fb705094000df87050940004fe76cc940004fd76cc94002cfc76cc94008d7e75cc9400057d75cc940004fe768c940004fd768c94004cfc768c940006ef628c94004eec628c940004ff764c940004fe764c940004fc764c940006ef624c940006ec624c940004fe760c940004fd760c94004cfc760c94008d7e750c9400057d750c940035be740c940005bd740c94000dfa700c940005f9700c940014fe76d8540086f661d8540004ff75d854001cfe75d8540004fd75d854001cfc75d854000cfd74d8540014fc74d85400067f54d85400067d54d854002cfe73d8540004fd73d85400067f53d85400067d53d854004cfe72d8540004fd72d8540086f641d8540034fd70d85400f6f710d85400057f755854008d7c7558540005df7358540005dc7358540005ef7258540005ec7258540086f4615854000cfc76505400073d5450540006f76150540016f46150540005fb705054000df87050540004fe76cc540004fd76cc54002cfc76cc54008d7e75cc5400057d75cc540004ff764c540004fe764c540004fc764c540004fe76c8540004fd76c854004cfc76c8540004ff7648540004fe7648540004fc76485400057f754854008d7c7548540005df7348540005dc73485400067f74597300047f74597300067e74597300067d74597300067c745973002e7f735973002c7f735973002e7e735973002e7d735973002c7d735973002e7c735973002e7f435973002e7e435973002e7d435973002e7c43597300067f72597300067e72597300067d72597300067c725973002e7f325973002e7e325973002e7d325973002e7c32597300067f71597300067e71597300067d71597300067c71597300067e41597300067c415973002e7f315973002e7e315973002e7d315973002e7c31597300067e215
  | 15 => 0xf2098b4019eed2098b40004ff7558b4001cfe7558b40004fd7558b4001cfc7558b4000cfc7458b400367f5458b400367d5458b40004ff7358b4002cfc7358b400067f5358b400067d5358b40036ef7258b40036ef4258b40036ec4258b40004ff7158b40014fe7158b40014fc7158b40186ef2058b4002cff76ccb40034fe76ccb40004fd76ccb4009d7e75ccb400057d75ccb4015e7e65ccb400067d65ccb4000dfa70ccb40005f970ccb4004cff768cb40034fe768cb40004fd768cb4011e7e658cb400067d658cb40004ff764cb40004fd764cb40034fc764cb401367e654cb400067d654cb4004cff760cb40034fe760cb40004fd760cb4009d7e750cb400057d750cb401167e650cb400067d650cb40035be740cb40005bd740cb40004ff755874001cfe7558740004fd755874001cfc755874000cfe7458740014fd745874000cfc74587400367f54587400367d5458740004ff735874002cfc73587400067f53587400067d5358740004ff725874004cfc7258740036f77158740036f74158740036f441587400e6f7105874002cff76cc740034fe76cc740004fd76cc74009d7e75cc7400057d75cc7400de7e65cc7400067d65cc740004ff764c740004fd764c740034fc764c7400ce7e654c7400067d654c74004cff76c8740034fe76c8740004fd76c87400be7e65c87400067d65c8740004ff7648740004fd7648740034fc76487400057f754874009d7c75487400ae7e65487400067d6548740005df7348740005dc7348740005fb704874000df8704874001e7f76551402367e76551402367d765514001e7c76551400357f745514008f3f74551400367f64551400057f73551402a67c63551400373f425514023e7e615514023e7c61551400373f41551400077b70551402377870551400367f60551400377b40551402373e40551400373c405514003778405514003738405514002cfe76d8d40004ff75d8d4001cfe75d8d40004fd75d8d4001cfc75d8d400067f54d8d400067d54d8d400067f53d8d4004cfe72d8d40004fd72d8d40014fe71d8d40004fd71d8d40014fc71d8d40006de31d8d40006dc31d8d40034fd70d8d4020edf30d8d4008d7e7598d400057d7598d40006df6398d40005ee7298d40005ed7298d4008d7e7518d400057d7518d4002ede6318d40006dd6318d400067f7654d400067e7654d400067d7654d400067c7654d400057f7454d402267f6454d402857f7354d4008f5f7354d400067f6354d4002e7e6354d4002e7c6354d4022e7e6154d4022e7c6154d402267f6054d4028f7b4054d402273e4054d402273c4054d40227784054d4000cfe7690d4008d7e7590d400057d7590d40006df6390d4002edc6390d4000dfa7090d40005f97090d4000cfc7650d4008d7e7550d400057d7550d40006df6350d40
  | 16 => 0xc921145ee720c92104fe4210c9210077765c852137f7465c852137f7754c85210077554c8521007d763c8521007d463c852137f7753c85210077553c8521015f672c8521017e672c8521016f762c8521017e762c852104fe632c8521007e532c8521005f570c852100cfe76d81210067f65d81210067c65d8121006df63d8121006dc63d81210a6fa60d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121034fe74d8121004fd74d81210067f54d81210067d54d812102cfe73d8121004fd73d81210067f53d81210067d53d8121014fd72d812100cfc71d81210a6f840d81210a6fa20d81210a6fa10d81210057f75581210ad7c75581210067f65581210067c6558121005bf7458121005bc7458121005df7358121005dc7358121006df6358121006dc63581210a6f860581210367f74597400347f74597400367e74597400367d74597400347d74597400367c74597400067f73597400047f73597400067e73597400067d73597400067c73597400367f43597400367e43597400367d43597400367c43597400067f72597400067e72597400067d72597400067c72597400367f42597400367e42597400367d42597400367c42597400067f71597400067e71597400067d71597400067c71597400367f41597400367e41597400367d41597400367c41597400067e31597400067c31597400067e21597400067c21597402367f70597402367e70597402367d70597402367c70597400367f40597400367e40597400367d40597400367c40597402367f30597402367e30597402367d30597402367c30597402367f20597402367e20597402367d20597402367c20597402367f10597402367e10597402367d10597402367c1059740004ff7558f4001cfe7558f400067e7558f4001c7e7558f40004fd7558f400067d7558f4001cfc7558f4000cfc7458f400367f5458f400367d5458f40036df7358f400067f5358f40036df4358f40036dc4358f40004ff7258f4004cfc7258f40004ff7158f40014fe7158f40014fc7158f401dedf3058f4028d7f7654f400067f7654f400047f7654f4028e7e7654f4028d7d7654f400067d7654f400047d7654f4028e7c7654f4028d7f7454f4028d7d7454f402267e6454f402857f7354f4009f5f7354f4002e7e6354f400067d6354f4002e7c6354f4022e7e6154f4022e7c6154f400077b7054f40227787054f402267d6054f402273e4054f402277a4054f402273c4054f4004cff7598b4001cfe7598b40004fd7598b4004cfc7598b4000cfe7498b4000cfc7498b400367f5498b400367d5498b4002cfe7398b40004fd7398b400067f5398b400067d5398b4004eee7298b40036ef4298b4004eec4298b40014fe7198b40004fd7198b40014fc7198b4019ebe4098b40036bc4098b4004ee
  | 17 => 0x75c6354d2102e5c6354d2122e7f6254d2122e7f6154d2122f6e2154d2122f6c2154d2122f742154d212267e6054d212267c6054d2122f771054d21034ff76d0d21004fe76d0d21004fd76d0d21034fc76d0d210ad7e75d0d210057d75d0d210067f65d0d2121e7c65d0d21006df63d0d2102edc63d0d2102cff7690d21004fe7690d21004fd7690d2102cfc7690d210ad7e7590d210057d7590d210067f6590d212067c6590d21006df6390d2102edc6390d21005ee7290d21005ed7290d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210ad7e7550d210057d7550d210067f6550d211ee7c6550d21006df6350d2102edc6350d2102cff7610d21004fe7610d21004fd7610d2102cfc7610d210ad7e7510d210057d7510d210067f6510d211d67c6510d21006df6310d2102edc6310d21005ee7210d21005ed7210d21015f67110d21005f57110d21014fe76d0921014fc76d09210ad7e75d09210057d75d09210067f65d09211be7c65d0921006bf64d0921036bc64d0921006df63d0921006dc63d0921015f671d0921005f571d092116cfe76909210067f659092117e7c6590921006df6390921006dc639092104fe42190921034ff7650921014fe765092118cfd7650921014fc76509210067f65509211967c6550921006bf6450921036bc6450921006df6350921006dc6350921005f77150921015f4715092118fe421509211a4fe76109210ad7e75109210057d75109210067f65109211767c6510921006df6310921006dc6310921014fe76cc921014fc76cc9210ad7e75cc9210057d75cc9210067f65cc92115e7c65cc921006df63cc92102edc63cc921015f671cc921005f571cc921157e421cc92110cfe768c9210067f658c92111e7c658c921146df638c92102edc638c92110dee768c921006ee768c9210076f658c92138f6c658c92138f6f548c9210076d548c92112ded738c921147cf638c92102eee638c92102eec638c921007cc638c92102ecc638c92138f6f538c9210076d538c921015ee718c921015ec718c92104eef618c921147ce318c921147cc318c921005ed708c921147e7108c92102cff764c921014fe764c92112cfd764c921014fc764c9210067f654c9211367c654c921006df634c92102edc634c921005f7714c921015f4714c921015ec764c92102eec764c921014ec764c9210076f654c9213876c654c9213876f544c9210076d544c921007cf734c921007cf634c92102eee634c92102eec634c921007cc634c92102ecc634c9213876f534c9210076d534c921007e7714c921015ee714c921015ec714c92112fe4714c921015e4714c92112eef614c921005ef704c92112fe7104c921144fe760c9210ad7e750c9210057d750c9210067f650c9211167c650c921006df630c92102edc630
  | 18 => 0xd71d8d21146dc71d8d21146df51d8d21146de51d8d21146dd51d8d21146dc51d8d21146df41d8d21146de41d8d21146dd41d8d21146dc41d8d21146df21d8d21146de21d8d21146dc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006de40d8d21006dc40d8d21006de20d8d21006dc20d8d21146df10d8d21146de10d8d21146dd10d8d21146dc10d8d210ad7e7598d210057d7598d210067f6598d210067c6598d21006df6398d2112ded7298d210057f7558d210ad7c7558d210067f6558d210067c6558d21155ef7258d21004ff7558d210067f7558d210047f7558d2101cfe7558d21004fd7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d21034fc7458d210067f5458d210067d5458d21006df7358d210067f5358d21154ff7258d21006ef7258d2112cff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21144fe7618d210ad7e7518d210057d7518d210067f6518d210067c6518d2102ede6318d21006dd6318d210075f5318d21145de7618d21006de7618d21144de7618d210075e7518d210075d7518d21006df6518d210075f6518d210065f6518d21006de6518d21006dd6518d21006dc6518d210075c6518d210065c6518d21006df6418d21006de6418d21006dd6418d21006dc6418d210075f5418d210075d5418d2110fcd7218d2110fce2118d2110fcc2118d2110fd42118d21006de6018d21006dc6018d2110fd71018d2102edf7518d2102ede7518d2102e5e7518d2102edd7518d2102e5d7518d2102edc7518d2102edf7418d2102ede7418d2102edd7418d2102edc7418d21006df5418d210065f5418d21006de5418d21006dd5418d210065d5418d21006dc5418d2102edf7218d2102edd7218d2102ecd7218d21006df5218d21006de5218d21006dd5218d21006dc5218d2102edf7118d2102ede7118d2102edd7118d2102edc7118d2110edf5118d2110ede5118d2110edd5118d2110edc5118d2110edf4118d2110ede4118d2110edd4118d2110edc4118d2110edf2118d2110ede2118d2110edd2118d2110edc2118d2102edf7018d2102ede7018d2102edd7018d2102edc7018d21006df5018d21006de5018d21006dd5018d21006dc5018d21006de4018d21006dc4018d21006de2018d21006dc2018d2110edf1018d2110ede1018d2110edd1018d2110edc1018d210067f7654d210057e7654d210067e7654d210047e7654d210067d7654d210057c7654d210067c7654d210047c7654d210057f7454d210067f6454d2128e7e6454d210067d6454d2128e7c6454d213957f7354d210af5f7354d210067f6354d210075f6354d210065f6354d2102e7e6354d210067d6354d2102e7c6354d21
  | 19 => 0x91211a4fd71d91211a6bf41d91211a6bd41d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d91211a6f710d91210ad7e75991210057d75991210067f65991210067c6599121006bf6499121005de7399121005dd739912118ded72991210057f75591210ad7c75591210067f65591210067c6559121005df7359121005dc73591211b5ef7259121005fb70591210a5f87059121004ff75591210067f75591210047f755912101cfe7559121004fd755912101cfc75591210067c755912101c7c7559121006bf74591210067f5459121004ff7359121006df7359121004df735912102cfc7359121006dc735912102cdc73591210067f53591211b4ff7259121006ef725912118cff7159121006f77159121004ff7059121006fb7059121004fb705912100cfe705912100cfc7059121006f8705912100cf8705912118ef710591211a4fe76191210ad7e75191210057d75191210067f65191210067c6519121036be6419121006bd64191210067f76551210057e76551210067e76551210047e76551210067d76551210057c76551210067c76551210047c765512139d7f74551210af3f74551210067f64551210367e64551210067d64551210367c64551210057f73551212a67e63551212a67c63551210076f72551210076c725512123e7f625512123e7f615512123f3f415512123f3d415512123f6e215512123f6c215512123f7421551212367e60551212367c605512123f77105512102cfe76d8d210ad7c75d8d210067f65d8d210067c65d8d210075f53d8d21004ff75d8d210067f75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d210067c75d8d2101c7c75d8d21034fe74d8d21004fd74d8d210067f54d8d210067d54d8d210067f53d8d21006df53d8d210065f53d8d21006de53d8d21006dd53d8d21006dc53d8d2104cff71d8d21144fd71d8d21146df31d8d21146dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d2102cde76d8d210075f75d8d210075c75d8d21006df65d8d210075f65d8d210065f65d8d21006de65d8d21006dd65d8d21006dc65d8d210075c65d8d210065c65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d210075f54d8d210075d54d8d21147cf72d8d21147ce21d8d21147cc21d8d21147d421d8d21006de60d8d21006dc60d8d21147d710d8d21006df75d8d210065f75d8d21006de75d8d21006dd75d8d21006dc75d8d210065c75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d210065f54d8d21006de54d8d21006dd54d8d210065d54d8d21006dc54d8d21146df72d8d21146dd72d8d21006df52d8d21006de52d8d21006dd52d8d21006dc52d8d21146df71d8d21146de71d8d21146d
  | 20 => 0x67f6354f2102e7e6354f210067d6354f2102e7c6354f2122e7e6254f21007777154f2122f747154f2122e7d6154f2122f6e2154f2122f762154f2122f6c2154f212267e6054f212267c6054f21034ff76d0f2104cfe76d0f21004fd76d0f2104cfc76d0f210bd7e75d0f210057d75d0f21015f671d0f21005f571d0f2102cff7690f2104cfe7690f21004fd7690f2104cfc7690f210bd7e7590f210057d7590f2104dee7290f21005ed7290f21004ff7650f2104cfe7650f21004fd7650f2104cfc7650f210bd7e7550f210057d7550f2102cff7610f2104cfe7610f21004fd7610f2104cfc7610f210bd7e7510f210057d7510f2104dee7210f21005ed7210f2118cfd76d0b210bd7e75d0b210057d75d0b211b4ff7650b2112cfd76ccb210bd7e75ccb210057d75ccb21015ed768cb2104eed768cb21014ed768cb213bf6f548cb210076d548cb2102eee638cb2104fce638cb2104fcd638cb2104eec638cb213bf6f538cb210076d538cb21015ee718cb2104fe6718cb2104fe5718cb21015ec718cb21147ce318cb21147cc318cb21005ed708cb21154ff764cb21155ef764cb21006ef764cb213b76f544cb210076d544cb2104fcf734cb2102eee634cb2102eec634cb213b76f534cb210076d534cb21015ee714cb21015ec714cb21005ef704cb2100cff765832104ef86058321004ff755832101cfe7558321004fd755832101cfc7558321004ff7458321034fc74583210067f54583210067d5458321004ff735832102cfc73583210067f53583210067d5358321014fc725832103ef6215832104efb205832104ef820583210b6fa10583213ad7e76d95210ae7e76d952101c7e76d95210057d74d95210057d73d95213a76e21d95213a76c21d95213a77421d95210067e60d95210067c60d95213a77710d95210067f74d95210067e74d95210067d74d95210047d74d95210067c74d95210067f73d95210067e73d95210067d73d95210047d73d95210067c73d95213a67f72d95210ae7e72d95213a67d72d95213a67c72d95213a67f71d95213a67e71d95213a67d71d95213a67c71d95213a67f41d95213a67e41d95213a67d41d95213a67c41d95213a67f31d95213a67e31d95213a67d31d95213a67c31d95213a67f21d95213a67e21d95213a67d21d95213a67c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067e40d95210067c40d95210067e30d95210067c30d95210067e20d95210067c20d95213a67f10d95213a67e10d95213a67d10d95213a67c10d9521034fe76d91210ad7c75d91210067f65d91210067c65d9121004ff75d91210067f75d912101cfe75d9121004fd75d912101cfc75d91210067c75d912101c7c75d91210067f54d912102cfe73d9121004fd73d91210067f53d912104cff71d
  | 21 => 0xf629093104eec6290931004ff7650931004fe7650931004fc7650931006ef6250931006ec6250931004fe7610931004fd761093104cfc76109310cd7e75109310057d751093102dde7310931005dd7310931015f67110931005f57110931014fe768c931146df638c931006ef628c93104eec628c931015f6718c931005f5718c931014fc764c9310075d534c931006ef624c931006ec624c931005f7714c931015f4714c93100cfe76d81310c6fa60d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131034fe74d8131004fd74d81310067f54d81310067d54d8131014fd73d813100cfc73d81310067f53d81310067d53d813104cfe72d8131004fd72d813102cfd71d81310c6fa30d81310c6fa10d81310057f75581310cd7c7558131005bf7458131005bc7458131005ef7258131005ec72581310c6f8605813104cff75d932101cfe75d9321004fd75d932104cfc75d93210067f54d932102cfe73d9321004fd73d93210067f53d932104cfe72d932104eee72d932104ef571d932100cfe70d9321004fd70d932100cfc70d932118cfd76993210bd7e75993210057d759932104ebf649932104ebc6499321034ff765932104ebc6459321004ff755932101cfe7559321004fd755932101cfc755932104ebf74593210067f5459321004ff735932102cfc73593210067f5359321014fe7259321014fc725932104ebe425932104ebc425932118ebf415932118ebd4159321004ff705932100cfe705932100cfc70593210067f76553210067e76553210067d76553210067c765532139d7f74553210bf3f74553210067f64553210367e64553210067d64553210367c64553210057f73553212a67e63553212a67c63553210076f72553210076c725532123e7e625532123e7d615532123f3f415532123f3d415532123f6e215532123f76215532123f6c21553212367e60553212367c605532104cff75d8f2101cfe75d8f21004fd75d8f2104cfc75d8f21034fe74d8f21004fd74d8f210067f54d8f210067d54d8f210067f53d8f2104cfe72d8f2104eee72d8f2104ef571d8f21146de31d8f21146dc31d8f2100cfe70d8f21004fd70d8f2100cfc70d8f2112cfd7698f210bd7e7598f210057d7598f2104edf6398f2104edc6398f2102cff7658f2104edc6358f21004ff7558f2101cfe7558f21004fd7558f2101cfc7558f21004ff7458f21034fc7458f210067f5458f210067d5458f2104edf7358f210067f5358f21014fe7258f21014fc7258f2104ede3258f2104edc3258f2112edf3158f2112edd3158f21004ff7058f2100cfe7058f2100cfc7058f210067f7654f210067e7654f210067d7654f210067c7654f210057f7454f210067f6454f2128e7e6454f210067d6454f2128e7c6454f213957f7354f210bf5f7354f21
  | 22 => 0x833102e7d5358331004ff725833104cfc725833102efb705833102efb305833102ef830583310d6fa1058331034fe76d9131004ff75d913101cfe75d9131004fd75d913101cfc75d91310067f54d91310067f53d913104cfe72d9131004fd72d913102cff71d913102cfd71d91311febf41d91311febd41d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d91310cd7e75991310057d7599131006bf64991311e5dd7399131005ee7299131005ed7299131215df7359131004ff755913101cfe7559131004fd755913101cfc7559131006bf74591310067f5459131214ff7359131006df73591310067f5359131004ff725913104cfc72591311e4ff7159131006f77159131004ff705913100cfe705913100cfc70591311fcfe76191310cd7e75191310057d7519131036be6419131006bd64191310067f76551310067e76551310067d76551310067c765513139d7f74551310cf3f74551310067f64551310367e64551310067d64551310367c64551310057f735513123e7f635513123e7f615513123f3f415513123f3d41551312a777315513123f5e315513123f5c315513123f7431551312367e60551312367c605513101e7f7654d3122e7e7654d3122e7d7654d3101e7c7654d310057f7454d310067f6454d3128e7e6454d310067d6454d3128e7c6454d3102d7f7354d310cf5f7354d3102e7f6354d3102f5f3254d31007777154d3122f747154d3102e7f6154d3102f773154d3122f5e3154d3102f5c3154d3102f743154d312267e6054d312267c6054d3102f5f3054d31014fe76d0d31014fc76d0d310cd7e75d0d310057d75d0d31006bf64d0d31036bc64d0d31015f671d0d31005f571d0d31034ff7650d31014fe7650d311e4fd7650d31014fc7650d310cd7e7550d310057d7550d31006bf6450d31036bc6450d31005f77150d31015f47150d3102fd43150d31004ff75d893101cfe75d8931004fd75d893101cfc75d8931034fe74d8931004fd74d89310067f54d89310067d54d89310067f53d89310067d53d8931006ef52d8931006ec52d893102cfd71d8931156ef21d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d8931006ef62989310057f75589310cd7c7558931006ed621893104cff751893101cfe7518931004fd751893104cfc7518931034fe7418931004fd74189310067f54189310067d54189310067f53189310067d5318931006ef521893104eec521893104cff711893102cfd711893110ede311893110edc311893104eef211893110eed211893100cfe7018931004fd701893100cfc7018931006ee201893104eec2018931004fe76d0931004fd76d0931034fc76d09310cd7e75d09310057d75d0931004fe7690931004fd769093104cfc7690931006e
  | 23 => 0x2e7d435973102e7c43597310067f72597310067e72597310067d72597310067c725973102e7f325973102e7e325973102e7d325973102e7c325973122e7f715973122e7e715973122e7d715973122e7c715973122e7f415973122e7e415973122e7d415973122e7c415973102e7f315973102e7e315973102e7d315973102e7c315973122e7f215973122e7e215973122e7d215973122e7c21597310067f70597310067e70597310067d70597310067c70597310067e40597310067c405973102e7f305973102e7e305973102e7d305973102e7c30597310067e20597310067c205973122e7f105973122e7e105973122e7d105973122e7c1059731004ff755933101cfe75593310067e755933101c7e7559331004fd75593310067d755933101cfc755933102ebf74593310067f5459331014fe7359331014fc735933102e7f535933102e7d535933102ebe435933102ebc4359331004ff725933104cfc72593311e6bf41593311e6bd4159331004ff705933100cfe705933100cfc70593312a57f76553310067f76553310047f76553312a67e76553312a57d76553310067d76553310047d76553312a67c765533139d7f74553310df3f74553312a67f64553310367e64553310067d64553310367c64553312a57f73553312a57d735533123e7e635533100777715533123f74715533123e7d615533123f3f415533123f3d415533123f5e315533123f76315533123f5c31553312367e60553312367c605533104cff7598b3101cfe7598b31004fd7598b3104cfc7598b31034fe7498b31004fd7498b310067f5498b310067d5498b31014fe7398b31014fc7398b3102e7f5398b3102e7d5398b3104eee7298b3102eef3298b3104eec3298b31146de3198b3102edc3198b3104eef2198b31146ed2198b3100cfe7098b31004fd7098b3100cfc7098b31004ff7558b3101cfe7558b31004fd7558b3101cfc7558b31004ff7458b31034fc7458b310067f5458b310067d5458b31014fc7358b3102e7f5358b3102e7d5358b3102eef7258b3102eef3258b3102eec3258b3112eef2158b31004ff7058b3100cfe7058b3100cfc7058b31034ff76d0b3102cfe76d0b31004fd76d0b310dd7e75d0b310057d75d0b311be7e65d0b310067d65d0b31015f671d0b31005f571d0b3104cff7690b3102cfe7690b31004fd7690b3117e7e6590b310067d6590b31004ff7650b31004fd7650b3102cfc7650b311967e6550b310067d6550b3104cff7610b3102cfe7610b31004fd7610b310dd7e7510b310057d7510b311767e6510b310067d6510b3102dde7310b31005dd7310b31004ff755833101cfe7558331004fd755833101cfc7558331004ff7458331034fc74583310067f54583310067d5458331014fe735833100cfd7358331014fc735833102e7f535
  | 24 => 0xd7490d410073d5490d41006df6390d4102edc6390d41015f67190d41005f57190d41014fc7650d410ed7e7550d410057d7550d413c73f5450d410073d5450d41006df6350d4102edc6350d41005f77150d41015f47150d41015bc7650d4102ebc7650d41014bc7650d413cdbf7550d413c73e7550d413cdbd7550d410073d7550d410053d7550d41035bf7350d410379f7350d410079f6350d4102ebe6350d4102ebc6350d410079c6350d413c73f5350d410073d5350d41007b77150d41015be7150d41015bc7150d411e7b47150d41036bf6150d41037b76150d411e7b71050d410073d54d8941004ff75d894101cfe75d8941004fd75d894101cfc75d89410067f54d89410067d54d894102cfe73d8941004fd73d89410067f53d89410067d53d8941034fd71d89411b6ef21d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d89411b6f710d89410073d5498941006ef62989410057f75589410ed7c75589410073d5458941005df7358941005dc7358941005fb70589410e5f870589410073d5418941006ed621894104cff751894101cfe7518941004fd751894104cfc75189410067f54189410067d541894102cfe7318941004fd73189410067f53189410067d531894104cff7118941034fd711894104eef211894116eed211894100cfe7018941004fd701894100cfc7018941006ee201894104eec2018941014fe76909410073d5490941006ef629094104eec6290941015f67190941005f57190941014fc76509410073d5450941006ef6250941006ec6250941005f77150941015f47150941004fe76cc941004fd76cc94102cfc76cc9410ed7e75cc9410057d75cc941035be74cc941005bd74cc9410073d54cc941004fe768c941004fd768c94104cfc768c9410073d548c941006df638c94102edc638c941004ff764c941004fe764c941004fc764c9410073d544c941005f7714c941015f4714c941004fe760c941004fd760c94104cfc760c9410ed7e750c9410057d750c941035be740c941005bd740c9410073d540c941006df630c94102edc630c941015f6710c941005f5710c94100cfe76d81410073d54d81410e6fa60d8141004ff75d814101cfe75d8141004fd75d814101cfc75d8141014fd74d814100cfc74d81410067f54d81410067d54d814102cfe73d8141004fd73d81410067f53d81410067d53d814104cfe72d8141004fd72d8141034fd71d81410e6fa40d81410e6f820d81410e6fa10d81410057f75581410ed7c75581410073d5458141005df7358141005dc7358141005ef7258141005ec72581410e6f860581410067f74597310047f74597310067e74597310067d74597310067c745973102e7f735973102e7e735973102e7d735973102e7c735973102e7f435973102e7e4359731
  | 25 => 0xcb410067d650cb41035be740cb41005bd740cb410073d540cb4102ede630cb41006dd630cb4104eee620cb41006ed620cb41004ff755834101cfe7558341004fd755834101cfc7558341014fe745834100cfd7458341014fc74583410367f54583410367d5458341004ff735834102cfc73583410067f53583410067d5358341004ff725834104cfc7258341036f64158341036f54158341036fb7058341036fb4058341036f840583410f6fa105834101e7f765514123e7e765514123e7d765514101e7c76551410357f74551410ef3f74551410367f64551410057f73551412a67c63551410373f43551410373c43551410373f42551410373c425514100777715514123f7471551410367f615514103777415514123f3e41551410373c41551410377441551410373441551412367e60551412367c60551410373f40551413e73e40551410373c405514123f7710551410ef3f765514101e3f765514123f3c765514101e3c76551410073f73551410053f73551410073e73551410073d73551410073c73551410073f72551410073e72551410073d72551410073c725514123f3f715514100737715514123f3e715514123f3d715514123f3c715514123f3471551410373f61551410363f615514103737615514123f3e315514123f3c315514123f3e215514123f3c21551410073f70551413e73e70551410073d70551413e73c70551413e73e60551413e73c60551413e73e30551413e73c30551413e73e20551413e73c205514123f3f105514123f37105514123f3e105514123f3c105514102cfe76d8d410073d54d8d41004ff75d8d4101cfe75d8d41004fd75d8d4101cfc75d8d410067f54d8d410067d54d8d410067f53d8d41006de53d8d41006dd53d8d4104cfe72d8d41004fd72d8d41034fd71d8d41216df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d410ed7e7598d410057d7598d410073d5498d41006df6398d410073d5458d410ed7e7518d410057d7518d410073d5418d4102ede6318d41006dd6318d410067f7654d410067e7654d410067d7654d410067c7654d410057f7454d410073e7454d410073d7454d4122e7f6454d413957f7354d410ef5f7354d410067f6354d410075f6354d410065f6354d4102e7e6354d4102e7c6354d410075c6354d4102e5c6354d4122e7f6154d4128f774154d4122f3e4154d4122f3c4154d4122f744154d412267e6054d412267c6054d4122f771054d411cdbe76d0d41036be76d0d41035bf75d0d410373e75d0d413ddbd75d0d410373d75d0d410053d75d0d4102ebe63d0d4102ebc63d0d413d73f53d0d410073d53d0d41015be71d0d41015bc71d0d41036bf61d0d41037b761d0d41217b710d0d41014fe7690d410ed7e7590d410057d7590d411e5b
  | 26 => 0x73d73553410073c73553410373f63553410373e63553410373d63553410373c63553410073f72553410073e72553410073d72553410073c72553410373f62553410373e62553410373d62553410373c625534123f3f715534123f3e715534123f3d715534123f3c715534123e3d615534123f3e315534123f3c315534123f3e215534123f3c21553410073f70553413ff3e70553410073d70553413ff3c70553410373f60553410373e60553410373d60553410373c60553413ff3e30553413ff3c30553413ff3e20553413ff3c205534123f3f105534123f3e105534123f3c1055341004ff7558f4101cfe7558f410067e7558f4101c7e7558f41004fd7558f410067d7558f4101cfc7558f41014fc7458f410367f5458f410367d5458f41036df7358f410067f5358f41036df4358f41036dc4358f41004ff7258f4104cfc7258f411e6df3158f41004ff7058f4100cfe7058f4100cfc7058f4128d7f7654f410067f7654f410047f7654f4128e7e7654f4128d7d7654f410067d7654f410047d7654f4128e7c7654f4128d7f7454f4128f3e7454f4128d7d7454f410073d7454f4122e7e6454f413957f7354f410ff5f7354f4102e7e6354f410067d6354f4102e7c6354f4128f3f4354f41007777154f4122f747154f4122e7d6154f4122f3e4154f4122f764154f4122f3c4154f412267e6054f412267c6054f41035bf7650f41006bf7650f413f5bf7550f413ef3e7550f413f5bd7550f410073d7550f410053d7550f410373e6550f410373d6550f410379f7350f4102ebe6350f4102ebc6350f413ef3f5350f410073d5350f41015be7150f41015bc7150f4104cff7598b4101cfe7598b41004fd7598b4104cfc7598b41014fe7498b41014fc7498b410367f5498b410367d5498b4102cfe7398b41004fd7398b410067f5398b410067d5398b4104eee7298b41036ef4298b4104eec4298b4104eef2198b411a6ed2198b4100cfe7098b41004fd7098b4100cfc7098b41004ff7558b4101cfe7558b41004fd7558b4101cfc7558b41014fc7458b410367f5458b410367d5458b41004ff7358b4102cfc7358b410067f5358b410067d5358b41036ef7258b41036ef4258b41036ec4258b4118eef2158b41004ff7058b4100cfe7058b4100cfc7058b4102cff76ccb41034fe76ccb41004fd76ccb410fd7e75ccb410057d75ccb4115e7e65ccb410067d65ccb41035be74ccb41005bd74ccb410073d54ccb41006ee62ccb41006ed62ccb4104cff768cb41034fe768cb41004fd768cb4111e7e658cb410067d658cb410073d548cb4102ede638cb41006dd638cb41004ff764cb41004fd764cb41034fc764cb411367e654cb410067d654cb410073d544cb4104cff760cb41034fe760cb41004fd760cb410fd7e750cb410057d750cb411167e650
  | 27 => 0xe435903202ebc435903204cfe725903204cfc725903204ebe425903204ebc4259032004ff7159032014fe7159032014fc7159032004ff705903200cfe705903200cfc70590322a57f76550320067f76550320047f76550322a67e76550322a57d76550320067d76550320047d76550322a67c76550324257f74550321173f74550322a67f64550320367e64550320067d64550320367c64550322a57f73550322a57d73550322a67e63550320076f72550320076c725503211e7e62550322a75f32550322a76e32550322a76d325503223e7e615503223e7c615503241f5e31550322a75c31550322367e60550322367c6055032004fd76d08321157e75d08320057d75d08321be7e65d08320067d65d0832004ff76508321967e65508320067d655083204ddf764c832006df764c832004df764c83204f5e654c83204f5d654c8324175f544c8320075d544c83204ddf724c83202fcf724c83204ede624c83204fce624c83204fce524c832417cd524c83204fce424c832007cd424c83210dde714c83210ddc714c83240fce214c83204fcc214c832004ff755843201cfe7558432004fd755843201cfc7558432004ff7458432034fc74584320067f54584320067d545843202e7f535843202e7d535843202eee325843202eed325843204ef7715843210ef6415843202ef7315843210ede315843202edc315843202ef4315843204ef7215843204ef42158432004ff705843200cfe705843200cfc705843210ef71058432004ff755803201cfe7558032004fd755803201cfc7558032004ff7458032034fc74580320067f54580320067d545803202e7f535803202e7d5358032004ff7158032014fe7158032014fc715803204efb7058032106fa405803202efb305803202ef8305803204efb205803204ef82058032106fa10580320367f74597410367e74597410367d74597410367c74597410067f73597410047f73597410067e73597410067d73597410067c73597410367f43597410367e43597410367d43597410367c43597410067f72597410067e72597410067d72597410067c72597410367f42597410367e42597410367d42597410367c425974123e7f715974123e7e715974123e7d715974123e7c71597410367f41597410367e41597410367d41597410367c415974123e7f315974123e7e315974123e7d315974123e7c315974123e7f215974123e7e215974123e7d215974123e7c21597410067f70597410067e70597410067d70597410067c70597410367f40597410367e40597410367d40597410367c40597410067e30597410067c30597410067e20597410067c205974123e7f105974123e7e105974123e7d105974123e7c10597410373f76553410353f76553414063f76553410073f73553410053f73553410073e7355341
  | 28 => 0x4d3202f5f3154d322267e6054d322267c6054d3202f5f3054d32004fe76d0d3204cfc76d0d321357e75d0d320057d75d0d32006bf64d0d32036bc64d0d320075d53d0d32005ee72d0d32005ed72d0d32034fc7650d321357e7550d320057d7550d32006bf6450d32036bc6450d3202f9c4350d32005ef7250d32005ec7250d3202fcc3250d3202cfe76d093202cfc76d09321357e75d09320057d75d0932006bf64d0932036bc64d093202dde73d0932005dd73d0932004fe7690932034ff7650932004fd765093202cfc7650932006bf6450932036bc6450932005df735093202ddc7350932004fe76109321357e75109320057d7510932007ad421093242f5f538c9320075d538c93202dee728c93202eef628c93242f5f548c9320075d548c93204dde728c93204edf628c93202fcf628c932146de618c932146dc618c932014fe76d853212ef661d8532004ff75d853201cfe75d8532004fd75d853201cfc75d8532034fe74d8532004fd74d85320067f54d85320067d54d85320067f53d85320067d53d853202cfd72d8532006f751d853212ef451d853212ef641d853212ef631d853212ef621d853200cfe70d8532004fd70d853200cfc70d8532006f610d853212ef410d85320057f75585321357c755853212ef4615853200cfe76d8132126fa60d8132004ff75d813201cfe75d8132004fd75d813201cfc75d8132034fe74d8132004fd74d81320067f54d81320067d54d81320067f53d81320067d53d813202cfd72d8132014fe71d8132004fd71d8132014fc71d8132126fa30d8132126fa20d81320057f75581321357c7558132005bf7458132005bc7458132005f7715813212df47158132126f860581320067f74594320047f74594320067e74594320067d74594320067c745943202e7f735943202e7e735943202e7d735943202e7c735943202e7f435943202e7e435943202e7d435943202e7c43594321167f725943204e7e72594321167d725943204e7c725943204e7e425943204e7c425943202e7f325943204e7e325943202e7d325943204e7c32594320067f71594320067e71594320067d71594320067c71594320067e41594320067c415943202e7f315943202e7e315943202e7d315943202e7c315943204e7f21594320067e215943204e7c21594320067f70594320067e70594320067d70594320067c70594320067e40594320067c405943202e7f305943202e7e305943202e7d305943202e7c305943204e7f20594320067e205943204e7c20594320067f10594320067e10594320067c1059432004ff755903201cfe75590320067e755903201c7e7559032004fd75590320067d755903201cfc755903204cff745903204ebf74590320067f545903202cfe735903202cfc735903202e7f535903202e7d535903202eb
  | 29 => 0x2f6c3254e3222e7e6154e3222e7c6154e3243f5e3154e3202f5c3154e322267e6054e322267c6054e3202f5f3054e3211d7e75d0e320057d75d0e32036be64d0e32006bd64d0e3204dee72d0e32005ed72d0e32034ff7650e3211d7e7550e320057d7550e32036be6450e32006bd6450e32005ef7250e3204dec7250e3211d7e75d0a320057d75d0a3204fac4250a3204ddd76cca3202edd76cca3202f5e75cca3202f5d75cca324375f54cca320075d54cca3204fce62cca3204fce52cca32437cd52cca32145de71cca3202ddc71cca32014ff76586320057f755863211d7c755863202ddc735863204ef46158632147d63158632004ff75586320067f75586320047f755863201cfe7558632004fd755863201cfc75586320067c755863201c7c7558632004ff7458632034fc74586320067f54586320067d54586320067f53586320067d535863204cfc7258632146de3158632146f63158632146dc315863204ef7215863204ef42158632004ff705863200cfe705863200cfc7058632146f7105863200cff76582320057f755823211d7c755823204ef86058232004ff75582320067f75582320047f755823201cfe7558232004fd755823201cfc75582320067c755823201c7c7558232004ff7458232034fc74582320067f54582320067d54582320067f53582320067d535823204cfc7258232004ff7158232014fe7158232014fc715823213efa305823204efb205823204ef8205823213efa1058232034fe76d9132004ff75d913201cfe75d9132004fd75d913201cfc75d91320067f54d91320067f53d9132014fe71d9132004fd71d9132014fc71d913200cfe70d9132004fd70d913200cfc70d9132006be40d9132006bc40d91321357e75991320057d7599132006bf649913212df67199132005f57199132004ff755913201cfe7559132004fd755913201cfc7559132006bf74591320067f5459132004ff7359132006df73591320067f5359132004ff7259132006ef7259132004ff7159132014fe7159132014fc7159132004ff705913200cfe705913200cfc7059132004fe76191321357e75191320057d7519132036be6419132006bd64191320067f76551320067e76551320067d76551320067c76551321357f74551321373f74551320067f64551320367e64551320067d64551320367c64551320057f73551322a76f325513223e7e615513223e7c61551322367e60551322367c605513201e7f7654d3211e7e7654d321367d7654d3201e7c7654d320057f7454d320067f6454d3228e7e6454d320067d6454d3228e7c6454d3202d7f7354d321375f7354d3202e7f6354d3202f5c4354d320076f7254d320076c7254d3202e7f6254d3202f6f3254d3202f5c3254d3202f6c3254d3202f4c3254d3222e7e6154d3222e7c615
  | 30 => 0xd535933202ebe435933202ebc4359332004ff7159332014fe7159332014fc7159332004ff705933200cfe705933200cfc7059332006be4059332006bc40593322a57f76553320067f76553320047f76553322a67e76553322a57d76553320067d76553320047d76553322a67c76553324257f745533215f3f74553322a67f64553320367e64553320067d64553320367c64553322a57f73553322a57d73553320076f72553320076c725533223e7e615533223e7c61553322367e60553322367c605533215d7e75d0b320057d75d0b321be7e65d0b320067d65d0b32036be64d0b32006bd64d0b3202dde73d0b32005dd73d0b3217e7e6590b320067d6590b32034ff7650b321967e6550b320067d6550b32036be6450b32006bd6450b32005df7350b3202ddc7350b3215d7e7510b320057d7510b321767e6510b320067d6510b32004ff755873201cfe7558732004fd755873201cfc7558732004ff7458732034fc74587320067f54587320067d545873202e7f535873202e7d535873202eee325873202eed325873202ef7715873202ef7315873202ef43158732156f62158732004ff705873200cfe705873200cfc7058732004ff755833201cfe7558332004fd755833201cfc7558332004ff7458332034fc74583320067f54583320067d545833202e7f535833202e7d5358332004ff7158332014fe7158332014fc715833202efb705833214ef8405833202efb305833202ef8305833214efa205833214efa105833204cff75d923201cfe75d9232004fd75d923204cfc75d92320067f54d923204edd73d92320067f53d923204eee72d9232014fe71d9232004fd71d9232014fc71d923200cfe70d9232004fd70d923200cfc70d9232004fd769923211d7e75992320057d759923204ebf649923204ebc6499232034ff765923204ebc6459232004ff755923201cfe7559232004fd755923201cfc755923204ebf74592320067f5459232006be5459232006bd54592320067f535923204cfc725923204ebe425923204ebc4259232004ff7159232014fe7159232014fc7159232004ff705923200cfe705923200cfc70592320067f76552320067e76552320067d76552320067c765523211d7f745523211f3f74552320067f64552320367e64552320073e64552320363e64552320067d64552320073d64552320063d64552320367c64552320057f73552321367d63552322a67e62552322a76f325523223e7e615523223e7c61552324475e31552324475c31552322367e60552322367c605523201e7f7654e3201e7c7654e320057f7454e320067f6454e3228e7e6454e320067d6454e3228e7c6454e3202d7f7354e3211f5f7354e3202e7d6354e320076f7254e320076c7254e3202e7e6254e3202f5f3254e3202f6f3254e3202f4f3254e32
  | 31 => 0x94420067c1059442004ff7558c4201cfe7558c420067e7558c4201c7e7558c42004fd7558c420067d7558c4201cfc7558c420367f5458c420367d5458c4204edf7358c420067f5358c42036df4358c42036dc4358c4204ede3258c4204edc3258c42004ff7158c42014fe7158c42014fc7158c42004ff7058c4200cfe7058c4200cfc7058c4228d7f7654c420067f7654c420047f7654c4228e7e7654c4228d7d7654c420067d7654c420047d7654c4228e7c7654c4228d7f7454c4228d7d7454c4228e7e6454c424657f7354c421775f7354c4202e7e6354c420067d6354c4202e7c6354c420076f7254c420076c7254c4217e7e6254c4228f3f4254c4228f6e4254c4228f6d4254c4222e7e6154c4222e7c6154c422267e6054c422267c6054c4245f3e4054c4228f3c4054c4204dbf7650842006bf7650842004bf765084204f3e655084204f3d65508424573f53508420073d535084204dbf7250842037af725084204ebe625084204fae625084204fae5250842457ad5250842165be7050842165bc705084244fae205084204fac2050842004ff755844201cfe7558442004fd755844201cfc75584420367f54584420367d5458442004ff735844202cfc73584420067f53584420067d535844204ef77158442036f74158442036f4415844216ef6315844204ef7215844204ef42158442004ff705844200cfe705844200cfc705844216ef71058442004ff755804201cfe7558042004fd755804201cfc75580420367f54580420367d5458042004ff735804202cfc73580420067f53580420067d5358042036ee4258042036ed4258042004ff7158042014fe7158042014fc715804204efb7058042036fb4058042166be4058042036bc4058042036f84058042166fa305804204efb205804204ef82058042166fa10580420067f74597320047f74597320067e74597320067d74597320067c745973202e7f735973202e7e735973202e7d735973202e7c735973202e7f435973202e7e435973202e7d435973202e7c435973215e7f725973215e7e72597320067d725973215e7c725973202e7f325973202e7e325973202e7d325973202e7c32597320067f71597320067e71597320067d71597320067c71597320067e41597320067c415973202e7f315973202e7e315973202e7d315973202e7c31597320067e21597320067c21597320067f70597320067e70597320067d70597320067c70597320067e40597320067c405973202e7f305973202e7e305973202e7d305973202e7c30597320067e20597320067c20597320067f10597320067e10597320067c1059732004ff755933201cfe75593320067e755933201c7e7559332004fd75593320067d755933201cfc755933202ebf74593320067f545933202cfc735933202e7f535933202e7
  | 32 => 0x2367e60551422367c60551420373f4055142004ff75d8d4201cfe75d8d42004fd75d8d4201cfc75d8d420067f54d8d420067d54d8d420067f53d8d42014fe71d8d42004fd71d8d42014fc71d8d42006de31d8d42006dc31d8d4200cfe70d8d42004fd70d8d4200cfc70d8d421957e7598d420057d7598d42006df6398d42185fa7098d42005f97098d421957e7518d420057d7518d4202ede6318d42006dd6318d420067f7654d420067e7654d420067d7654d420067c7654d420057f7454d421957f7354d421975f7354d420067f6354d4202e7e6354d4202e7c6354d4228f6f4254d4222e7e6154d4222e7c6154d422267e6054d422267c6054d421957e7590d420057d7590d420073d5490d42006df6390d4202edc6390d42005ee7290d42005ed7290d4202cfc7650d421957e7550d420057d7550d42006df6350d4202edc6350d420379c4350d42005ef7250d42005ec7250d42037ac4250d4246f3f54909420073d5490942035ee7290942036ef629094246f3f53909420073d539094204dbe729094204ebf6290942037af629094219ebe609094219ebc6090942014fe76d854218ef661d8542004ff75d854201cfe75d8542004fd75d854201cfc75d85420067f54d85420067d54d854202cfe73d8542004fd73d85420067f53d85420067d53d8542034fd72d854218ef641d854218ef621d854200cfe70d8542004fd70d854200cfc70d85420057f75585421957c7558542005df7358542005dc735854218ef46158542005fb7058542185f8705854200cfe76d8142186fa60d8142004ff75d814201cfe75d8142004fd75d814201cfc75d81420067f54d81420067d54d814202cfe73d8142004fd73d81420067f53d81420067d53d8142034fd72d8142014fe71d8142004fd71d8142014fc71d8142006fb50d8142186f850d8142186fa40d8142186fa30d8142186fa20d8142006fb10d8142186f810d81420057f75581421957c7558142186f860581420367f74594420367e74594420367d74594420367c74594420067f73594420047f73594420067e73594420067d73594420067c73594420367f43594420367e43594420367d43594420367c43594421767f725944204e7e72594421767d725944204e7c72594420367f425944204e7e42594420367d425944204e7c425944204e7e325944204e7c32594420067f71594420067e71594420067d71594420067c71594420367f41594420367e41594420367d41594420367c41594420067e31594420067c315944204e7f21594420067e215944204e7c21594420067f70594420067e70594420067d70594420067c70594420367f40594420367e40594420367d40594420367c40594420067e30594420067c305944204e7f20594420067e205944204e7c20594420067f10594420067e105
  | 33 => 0xb7058342036fb4058342036f840583421aefa205834201e7f765524201e7c76552420357f745524217f3f74552420367d64552420057f73552422a67e63552420076f72552420076c72552420367e62552420373f42552420376f42552420372f42552420376c425524223e7e615524223e7c61552420373f41552422367e60552422367c60552424873e40552420373c405524217d7e7598e420057d7598e4204edf6398e4204edc6398e4204edc6358e42004ff7558e4201cfe7558e42004fd7558e4201cfc7558e420067f5458e420067d5458e420067f5358e42006de5358e42006dd5358e4204cfc7258e4204ede3258e4204edc3258e42004ff7158e42014fe7158e42014fc7158e42004ff7058e4200cfe7058e4200cfc7058e420067f7654e420067e7654e420067d7654e420067c7654e420057f7454e421967d6454e4217d7f7354e4217f5f7354e4202e7e6354e420075e6354e4202e5e6354e420067d6354e420075d6354e420065d6354e4202e7c6354e4228e7e6254e4228f6f4254e4222e7e6154e4222e7c6154e422267e6054e422267c6054e4247f3e4054e4247f3c4054e4217d7e7590e420057d7590e4202ede6390e42006dd6390e4204dee7290e42005ed7290e4202cff7650e4217d7e7550e420057d7550e4202ede6350e42006dd6350e42005ef7250e4204dec7250e4204dbd76d0a42036bd76d0a420373e75d0a420373d75d0a424773f53d0a420073d53d0a4204fae62d0a4204fae52d0a42477ad52d0a4219dbe70d0a42035bc70d0a42014ff76586420057f755864217d7c755864204ef46158642004ff75586420067f75586420047f755864201cfe7558642004fd755864201cfc75586420067c755864201c7c75586420067f54586420067d5458642004ff735864202cfc73586420067f53586420067d535864204cfc72586421a6f6415864204ef7215864204ef42158642004ff705864200cfe705864200cfc70586421a6f7105864200cff76582420057f755824217d7c7558242035bc745824204ef8605824219fba4058242004ff75582420067f75582420047f755824201cfe7558242004fd755824201cfc75582420067c755824201c7c75582420067f54582420067d5458242004ff735824202cfc73582420067f53582420067d535824204cfc7258242004ff7158242014fe7158242014fc715824219ebe405824219efa405824219ebc405824204efb205824204ef8205824219efa105824201e7f765514217e7e76551421967d765514201e7c76551420357f74551421973f74551420367f64551420057f73551422a67c63551420373c43551420076f72551420076c72551420367f62551420376f42551420373c42551420376c42551420372c425514223e7e615514223e7c61551420373f4155142
  | 34 => 0x8843004ff755844301cfe7558443004fd755844301cfc75584430367f54584430367d545844302e7f535844302e7d535844302ebf435844302ebd4358443004ff725844304cfc725844302cff715844302ef77158443036f74158443036f4415844302ef7315844302ef431584431cef62158443004ff705844300cfe705844300cfc70584431cef71058443004ff755804301cfe7558043004fd755804301cfc75580430367f54580430367d545804302e7f535804302e7d535804302ede4358043036dd4358043004ff725804304cfc7258043004ff7158043014fe7158043014fc715804302cff705804302efb7058043036fb4058043036f8405804302efb305804302ef830580431c6fa20580431c6fa10580430367f74597420367e74597420367d74597420367c74597420067f73597420047f73597420067e73597420067d73597420067c73597420367f43597420367e43597420367d43597420367c43597421be7f72597421be7e72597420067d72597421be7c72597420367f42597420367e42597420367d42597420367c42597420067f71597420067e71597420067d71597420067c71597420367f41597420367e41597420367d41597420367c41597420067e31597420067c31597420067e21597420067c21597420067f70597420067e70597420067d70597420067c70597420367f40597420367e40597420367d40597420367c40597420067e30597420067c30597420067e20597420067c20597420067f10597420067e10597420067c1059742004ff7558f4201cfe7558f420067e7558f4201c7e7558f42004fd7558f420067d7558f4201cfc7558f420367f5458f420367d5458f42036df7358f420067f5358f42036df4358f42036dc4358f42004ff7158f42014fe7158f42014fc7158f42006de3158f42006dc3158f42004ff7058f4200cfe7058f4200cfc7058f4228d7f7654f420067f7654f420047f7654f4228e7e7654f4228d7d7654f420067d7654f420047d7654f4228e7c7654f4228d7f7454f4228d7d7454f424657f7354f421bf5f7354f4202e7e6354f420067d6354f4202e7c6354f420076f7254f420076c7254f4222e7e6154f4222e7c6154f422267e6054f422267c6054f42004ff755874201cfe7558742004fd755874201cfc75587420367f54587420367d5458742004ff735874202cfc73587420067f53587420067d5358742036f77158742036f74158742036f441587421b6f431587421b6f62158742004ff705874200cfe705874200cfc70587421b6f71058742004ff755834201cfe7558342004fd755834201cfc75583420367f54583420367d5458342004ff735834202cfc73583420067f53583420067d5358342036ee4258342036ed4258342004ff7158342014fe7158342014fc7158342036f
  | 35 => 0x4cfc75189430067f54189430067d54189430067f53189430067d5318943006ef521894304eec5218943014fe7118943004fd7118943014fc711894300cfe7018943004fd701894300cfc7018943014fe76d85431ed7e75d85430057d75d85430067e65d85430067d65d85431e6f661d8543004ff75d854301cfe75d85430067e75d854301c7e75d8543004fd75d85430067d75d85430047d75d854301cfc75d854302cfd74d85430067f54d85430067d54d8543034fd73d85430067f53d85430067d53d854304cfe72d8543004fd72d8543006f751d85431e6f451d85431e6f641d85431e6f631d854300cfe70d8543004fd70d854300cfc70d85430067e65585430067d65585431e6f4615854300cfe76d81431ed7e75d81430057d75d81430067e65d81430067d65d81431defa60d8143004ff75d814301cfe75d81430067e75d814301c7e75d8143004fd75d81430067d75d81430047d75d814301cfc75d814302cfd74d81430067f54d81430067d54d8143034fd73d81430067f53d81430067d53d814304cfe72d8143004fd72d8143014fe71d8143004fd71d8143014fc71d8143006fb50d81431def850d81431defa40d81431defa30d81430067e65581430067d65581431def860581430367f74594430367e74594430367d74594430367c745944302e7f735944302e7e735944302e7d735944302e7c735944302e7f435944302e7e435944302e7d435944302e7c43594430067f72594430067e72594430067d72594430067c72594430367f42594430367e42594430367d42594430367c425944302e7f325944302e7e325944302e7d325944302e7c32594430067f71594430067e71594430067d71594430067c71594430367f41594430367e41594430367d41594430367c415944302e7f315944302e7e315944302e7d315944302e7c31594430067e21594430067c21594430067f70594430067e70594430067d70594430067c70594430367f40594430367e40594430367d40594430367c405944302e7f305944302e7e305944302e7d305944302e7c30594430067e20594430067c20594430067f10594430067e10594430067c105944304cff759884301cfe7598843004fd759884304cfc75988430367f54988430367d549884302e7f539884302e7d539884304cfe729884304eee7298843036ef429884304eec429884302eef329884304eec3298843014fe7198843004fd7198843014fc719884300cfe7098843004fd709884300cfc7098843004ff755884301cfe7558843004fd755884301cfc75588430367f54588430367d545884302e7f535884302e7d535884302eef7258843036ef4258843036ec425884302eef325884302eec3258843004ff7158843014fe7158843014fc7158843004ff705884300cfe705884300cfc705
  | 36 => 0xf705864300cfe705864300cfc7058643004ff755824301cfe7558243004fd755824301cfc75582430067f54582430067d545824302cfc735824302e7f535824302e7d5358243004ff725824304cfc7258243004ff7158243014fe7158243014fc715824302efb70582431f6fa405824302efb305824302ef830582431f6f820582431f6fa10582431ee7f76595430073f74595430075f735954328f5f43595432a73e43595432a73c435954328f5c43595430076f72595430076c72595430077771595430077471595430067e61595430067c61595430077b70595430077870595430067e60595430067c60595430067f74595432047f74595430063f74595430067f735954321c7f73595430065f735954328e7f43595432a67e43595432a67c43595430067f72595430066f72595430067e72595430067d72595430067c72595430066c72595430067f71595430067771595430067e71595430067d71595430067c71595430067471595430067e415954328e7c41595430067e31595432a67c31595430067e21595430067c21595430067f70595430067b70595430067e70595430067d70595430067c70595430067870595430067e405954328e7c40595430067e30595432a67c30595430067e20595430067c20595430067f10595430067e10595430067c105954301e7f76551432a67e76551431ee7d765514301e7c76551430357f74551431ef3f74551430367f64551430057f73551430075f73551430055f73551430075c73551430367f63551430375f43551432a73e43551430373c43551430375c43551430371c435514323e7e615514323e7c61551430373f41551432367e60551432367c60551431ed7f7654d4301e7f7654d4301c7f7654d4328e7e7654d431ee7d7654d431ec7d7654d4301e7c7654d430057f7454d430073f7454d430053f7454d431ed7d7454d430073c7454d4302e7f6454d4302d7f7354d431ef5f7354d4302e7f6354d4328f5f4354d4302f3e4354d4302f3c4354d4302f5c4354d4302f1c4354d4322e7e6154d4322e7c6154d432267e6054d432267c6054d4302f5f3054d431ed7e75d89430057d75d89430067e65d89430067d65d8943004ff75d894301cfe75d89430067e75d894301c7e75d8943004fd75d89430067d75d89430047d75d894301cfc75d89430067f54d89430067d54d89430067f53d89430067d53d8943006ef52d8943006ec52d8943014fe71d8943004fd71d8943014fc71d894300cfe70d8943004fd70d894300cfc70d89430067e65989430067d6598943006ef62989430067e65589430067d65589431ed7e75189430057d75189430067e65189430067d6518943006ed621894304cff751894301cfe751894304e7e751894301c7e7518943004fd751894304e7d75189430047d7518943
  | 37 => 0x874301cfc755874302cfc74587430367f54587430367d54587430067f53587430067d5358743004ff725874304cfc7258743036f77158743036f74158743036f44158743216f63158743216f42158743004ff705874300cfe705874300cfc7058743216f71058743004ff755834301cfe7558343004fd755834301cfc755834302cfc74583430367f54583430367d54583430067f53583430067d5358343036de4358343036dd4358343004ff725834304cfc7258343004ff7158343014fe7158343014fc7158343036fb7058343036fb4058343036f8405834320efa30583432067f745964328e7e74596430067d745964328e7c745964302e7f735964302e7e735964302e7d735964302e7c735964302e7f435964302e7e435964302e7d435964302e7c43596430067f72596430067e72596430067d72596430067c725964328e7f425964328e7c425964302e7f325964302e7e325964302e7d325964302e7c32596430067f71596430067e71596430067d71596430067c715964328e7f41596430067e415964328e7c415964302e7f315964302e7e315964302e7d315964302e7c31596430067e21596430067c21596430067f70596430067e70596430067d70596430067c705964328e7f40596430067e405964328e7c405964302e7f305964302e5f305964302e7e305964302e7d305964302e7c30596430067e20596430067c20596430067f10596430067e10596430067c10596432a57f765524301e7f765524301c7f765524301e7c76552430357f74552432073f74552430367d64552432a57f73552430075f73552430055f73552432a75c73552430367e63552430373f43552430375f43552430371f43552430375c43552430373f425524323e7e615524323e7c61552430373f41552432367e60552432367c605524348f3e40552430373c405524304cff7598a4301cfe7598a43004fd7598a4304cfc7598a430067f5498a430067d5498a4302cfe7398a4302e7f5398a4302e7d5398a4304eee7298a4302eef3298a4304eec3298a43014fe7198a43004fd7198a43014fc7198a4300cfe7098a43004fd7098a4300cfc7098a43006ee2098a4304eec2098a43004ff7558a4301cfe7558a43004fd7558a4301cfc7558a430067f5458a430067d5458a4302cfc7358a4302e7f5358a4302e7d5358a4302eef7258a4302eef3258a4302eec3258a43004ff7158a43014fe7158a43014fc7158a43004ff7058a4300cfe7058a4300cfc7058a43006ee2058a43006ec2058a43004ff755864301cfe7558643004fd755864301cfc75586430067f54586430067d545864302cfc735864302e7f535864302e7d535864302ebf435864302ebd4358643004ff725864304cfc725864302ef771586431fef6415864302ef7315864302ef43158643004f
  | 38 => 0x76f72585530056f72585530057c72585530076c72585530056c725855322d7f715855300777615855322e7e615855322e7c615855322f7461585530057f70585532257e70585532257c70585532257e76d815328d7e74d81530057d74d81530067f64d81530067d64d815307f5f73d815302d7e73d815301d7d73d815307e7f63d815307f5f63d81530057e72d81530057d72d815322d7e71d81530057d71d815322d7c71d81532267e60d81532277a60d81532267c60d81532277840d81532277a30d81530057f745815328d7c74581530067f64581530067d645815349d7f73581530075f735815349d5f735815306e7f635815306f5f63581530057f72581530057c72581530057f715815322d7e715815322d7c71581532257f70581530077b60581532267e60581532267c60581532277860581530367f74597430367e74597430367d74597430367c745974321e7f73597432a67e73597430067d73597432a67c73597430367f43597430367e43597430367d43597430367c43597430067f72597430067e72597430067d72597430067c72597430367f42597430367e42597430367d42597430367c42597432a67f32597432a67c32597430067f71597430067e71597430067d71597430067c71597430367f41597430363f41597430367e41597430367d41597430367c41597432a67f31597430067e31597432a67c31597430067e21597430067c21597430067f70597430067e70597430067d70597430067c70597430367f40597430367e40597430367d40597430367c40597432a67f30597430067e30597432a67c30597430067e20597430067c20597430067f10597430067e10597430067c105974328d7f7654f4301e7f7654f4301c7f7654f4301e7c7654f4328d7f7454f430073f7454f430053f7454f4328f3c7454f4302e7e6454f4302d7f7354f4321f5f7354f4302e7d6354f4302f3e4354f4302f5e4354f4302f1e4354f4302f3c4354f4302f5f3254f4322e7e6154f4322e7c6154f434975e3154f4302f5c3154f432267e6054f432267c6054f4302f5f3054f4304cff7598b4301cfe7598b43004fd7598b4304cfc7598b4302cfe7498b430367f5498b430367d5498b430067f5398b430067d5398b4304eee7298b43036ef4298b4304eec4298b43014fe7198b43004fd7198b43014fc7198b43006ee2198b4304eec2198b4300cfe7098b43004fd7098b4300cfc7098b43004ff7558b4301cfe7558b43004fd7558b4301cfc7558b4302cfc7458b430367f5458b430367d5458b430067f5358b430067d5358b43036ef7258b43036ef4258b43036ec4258b43004ff7158b43014fe7158b43014fc7158b43006ee2158b43006ec2158b43004ff7058b4300cfe7058b4300cfc7058b43004ff755874301cfe7558743004fd755
  | 39 => 0xd739915328f5d73991531ed5d73991534667f639915321f5f63991530057e72991530057d729915322d7e71991530057d719915322d7c71991532257e70991530057d70991532257c70991530073f645915328e7e645915321d7f73591530075f735915321d5f73591531ee7f63591531ef5f63591530057f72591530076f72591530056f72591530057c72591530076c72591530056c72591530057f715915300777715915300577715915322d7e715915322d7c715915300774715915322d7471591530067e61591530067c61591530057f70591530077b70591530057b70591532257e70591532257c70591530077870591532257870591530067e60591530067c60591532057e761915328e7f641915328f3e641915328e7d64191530073d64191534667f63191531d75f63191530057e72191530057d721915322d7e71191530057d711915322d7c71191532257e70191530057d70191532257c701915328d7e74d89530057d74d89530067f64d89530067d64d895315e7f63d895315f5f63d895322d7e71d89530057d71d895322d7c71d89530076e21d89530076c21d89532257e70d89530057d70d89532257c70d895328d7e74989530057d74989530067f64989530067d64989531357d73989530075d73989531355d739895311e7f639895311f5f63989531157e72989530067f62989530076f62989530066f629895322d7e71989530057d719895322d7c71989530067e61989530067c61989532257e70989530057d70989532257c70989530067e60989530067c60989530057f745895328d7c74589530067f64589530067d645895311d7f73589530075f735895311d5f73589531367f63589531375f63589530076f62589530067e62589530057f715895300777715895300577715895322d7e715895322d7c715895300774715895322d7471589530057f70589532257e70589532257c705895315d7e761895328d7e74189530057d74189530067f64189530067d64189531167f63189531175f63189530067f62189530076e62189530067d62189530076d621895322d7e71189530057d711895322d7c71189530067e61189530067c61189530076e21189530076c21189532257e70189530057d70189532257c70189530067e60189530067c601895322d7e76d855328d7e74d85530057d74d85530067f64d85530067d64d855302d7e73d855301d7d73d85530de7f63d85530df5f63d85530057e72d85530057d72d855322e7e61d855322f7661d855322e7c61d855322f7441d855322f7631d855322f7421d85532257e70d85530057d70d85532257c70d855322f7710d85530057f745855328d7c74585530067f64585530067d64585534a57f73585530075f73585534a55f73585530ce7f63585530cf5f63585530057f7258553
  | 40 => 0x89540067e62589540057f715895423d7e715895423d7c71589540057f70589540077b70589540057b70589542357e70589542357c70589540077870589542357870589541bd7e76189541767f64189541773f64189542a57e73189540057d73189540067f63189540067d63189540067f62189540076e62189540067d62189540076d621895423d7e71189540057d711895423d7c71189540067e61189540067c61189542357e70189540057d70189542357c70189540067e60189540067c60189540076e20189540076c201895423d7e76d85540ff3f74d85540357e74d855401d7d74d85540fe7f64d85540ff3f64d85542a57e73d85540057d73d85540067f63d85540067d63d85540057e72d85540057d72d855423e7e61d855423f7661d855423e7c61d855423f7641d855423f7431d85542357e70d85540057d70d85542357c70d85544b57f74585540073f74585544b53f74585540ee7f64585540ef3f64585540057f73585542a57c73585540067f63585540067d63585540057f72585540057c725855423d7f715855400777615855423e7e615855423e7c615855423f7461585540057f70585542357e70585542357c70585542357e76d81540357e74d815401d7d74d815409e7f64d815409f3f64d81542a57e73d81540057d73d81540067f63d81540067d63d81540057e72d81540057d72d815423d7e71d81540057d71d815423d7c71d81542367e60d81542377a60d81542367c60d81542377a40d81542377830d81542377820d81542377a10d81544ad7f74581540073f74581544ad3f745815408e7f645815408f3f64581540057f73581542a57c73581540067f63581540067d63581540057f72581540076f72581540056f72581540057c72581540076c72581540056c72581540057f715815423d7e715815423d7c71581542357f70581540077b60581542367e60581542367c60581542377860581542067f63d91532075f63d91530057e72d91530057d72d915322d7e71d91530057d71d915322d7c71d91530067e61d91530067c61d91532257e70d91530057d70d91532257c70d91530067e60d91530067c60d91532067f73d91532067d73d91534267e43d91534267c43d91530067f72d91530067e72d91530067d72d91530067c72d91534267f32d91534267c32d91530067f71d91530067e71d91530067d71d91530067c71d91530067e41d915328e7c41d91534267f31d91530067e31d91534267c31d91530067e21d91530067c21d91530067f70d91530067e70d91530067d70d91530067c70d91530067e40d915328e7c40d91534267f30d91530067e30d91534267c30d91530067e20d91530067c20d91530067f10d91530067e10d91530067c10d915328d7e749915328e7f64991530073f64991530063f64991531ed7
  | 41 => 0x140000000000000c00300000020004004000c0000014000000000300000030004001004c0030004003000000700000000000000000000000000010024001000000021e7f64d8d5421f3f64d8d540057e72d8d540057d72d8d5423d7e71d8d540057d71d8d5423d7c71d8d540067e61d8d540067c61d8d542357e70d8d540057d70d8d542357c70d8d540067e60d8d540067c60d8d5421e7f74d8d5421e7d74d8d544667f43d8d542a67c43d8d540067f72d8d540067e72d8d540067d72d8d540067c72d8d544667f42d8d544667c42d8d540067f71d8d540067e71d8d540067d71d8d540067c71d8d544667f41d8d540067e41d8d544667c41d8d540067e31d8d542a67c31d8d540067e21d8d540067c21d8d540067f70d8d540067e70d8d540067d70d8d540067c70d8d544667f40d8d540067e40d8d544667c40d8d540067e30d8d542a67c30d8d540067e20d8d540067c20d8d540067f10d8d540067e10d8d540067c10d8d541ed7d7498d542a73d7498d541ed3d7498d544267f6498d542073f6498d542a57e7398d542a67f6398d540075f6398d540065f6398d540057e7298d540057d7298d5423d7e7198d540057d7198d5423d7c7198d542357e7098d540057d7098d542357c7098d542057f7458d540073f7458d542053f7458d541ee7f6458d541ef3f6458d540075f6358d542a67e6358d540057f7258d540076f7258d540056f7258d540057c7258d540076c7258d540056c7258d540057f7158d54007777158d54005777158d5423d7e7158d5423d7c7158d54007747158d5423d747158d540067e6158d540067c6158d540057f7058d540077b7058d540057b7058d542357e7058d542357c7058d54007787058d54235787058d540067e6058d540067c6058d5421d7e7618d544267f6418d541d73f6418d542a67f6318d542a75e6318d542a67d6318d540075d6318d540057e7218d540057d7218d5423d7e7118d540057d7118d5423d7c7118d542357e7018d540057d7018d542357c7018d541be7f64d89541bf3f64d89542a57e73d89540057d73d89540067f63d89540067d63d895423d7e71d89540057d71d895423d7c71d89542357e70d89540057d70d89542357c70d89540076e20d89540076c20d89541957d74989540073d74989541953d749895417e7f649895417f3f64989542a57e73989540057d73989540067f63989540067d63989541757e72989540067f62989540076f62989540066f629895423d7e71989540057d719895423d7c71989540067e61989540067c61989542357e70989540057d70989542357c70989540067e60989540067c609895417d7f74589540073f745895417d3f74589541967f64589541973f64589540057f73589542a57c73589540067f63589540067d63589540076f625
  | 42 => 0x100000010020001000000100340000010000000400100240010000000000c0020008004001800000000010000003000000500100020014000000c0000004000000000000040000000002000000300080010010000000800700040000010001001800200000000000000000000f0004001000400100040030004000000000000000010008000001c0000004007001c0040000001000000100180000000001006c0010004001001c002002c004002800100040000024001000000100000010000000001000000000000010003000000000080000008001000000300000000004003000400300280010008003001c0100000000002400100000030000005000c002001c0000000000001c001001000400180000008004000800100000000018001002c007000c00a0010000000000200000050000000000400e0000004002c001001800000280040008001000c0000004000000c0050000000000c0010004000000000000080000014000000c003000400100000020000000007400c000800400080020000002000000300200000004000002c00000000000030000000000d000400300040010004005001400100040000010000000c0040000001000c00100000000000002000000000000000000007000001b002000200080020014003000c00100000000018000000c005000000300000010014002000000200040000004005001000600100000010000000400000080000018000000000200080000004000000400000080060000003004c000000000000000020000007000c001000400000040000000000000000000040040000003000000100000010000000000000000040000008001000000b000c0000010007000400500240020004007000800100040030000000000800100240000000000000000400080020000000001400500000060000001000000b0000000000c0050004001001c0020004001000c005003800100080000034009000c004001c000000400b00000020004003000c003000000000040030000001000000000000000000000000c001000c00f00040000000000000000000000030004000000c0020048002003c0000004000000c0010008001000c000000c0000008000001c0000000000000c00200140000020000001000200000040018001003400000340000000004000000000000080010000000000900040030000000000000900000010044003001000000000080000009001400200080000000003000c0070008000000800000100000000002004400300200020008000000000a0000000000800300080020004000000800800040010000007000400000200010000001000800000040070000001002000100000030000000000c00100000030004000000000100180000004001000000000580040004000003
  | 43 => 0x80000000000001400200200010010004000000200000010018001001c0010020000000400000040040008003000c00000000000000001000400000000000004006001c000000800000140020000002000000600140000000006000000200280030004000001000000040050004001000000800000000014002000000800000000000002000c00100000000004000000000300040000000000000000000040010028000002400000000000004000002c0010000000000c000001c00000080020000000000c0000000002000400300000000008000000800b0060000000c001003c009002000500000090004000000c006000400900000000000000001c000000800400240020004002000c0000000007000000100100000004001001c00100080020010003001c000002000000000000000000000400100000000008000001c008001000a003c003000400000040040000002000c0010000002000c002000000000080000000000000c000000400600000020004009000800700100010004000001000000000050008001000000400040010004002000000500000020004000000400200040000008008000c002000800300140070000004000400f0004000000c004002c0000004000000400100040010008002000400d003c00b00040000000001000c0000008002001800500300020008001000c00600000010000001001c0000000000002000100000060030000000400c00000070004000000800000100000004004001400000040010000005000c00800000010008000000400000040060020003001000100040010000001002c00300000000008018000400000000060000003000000200000000000002000c0040040005000800a001800000000070004003000800100000000000002000400200040000008014000000100080000004000000000000040000000001002000000040010010001000400a00080030004000001c0000000001000400100040060010001003000100100010000000000000000540060000001000800300000000000000000000000000010000000000800000000050004002000c00000000010000007000c00000100010010000000400600140040000010001000400080000000002000800400040000000004000c000000c0020000002000000b00000010000000000400c00080030008001000c004001c000000800000200000018001001800100000000000000000800200040020000003001000000000000000001001000000000000010000000c005001400200000040010001002c001000c0000010001000000100080010000000000000c001c00000040060000003000c00500040020004000001c0010000000002800a000c0000010000000c00300000020008005000400500000020004003000c003000000
  | 44 => 0x600000000000000000400100000010000004003c0010000002000800000100070000007000000c003c002000400d0008001004400200180150008000000000b0000002000c002000400000100000008000000000200080050000001000c0000000000000c00500000020000000000400400000000008000000000400000040000002000000000040080000000000400000040010030000000400000000000000000000000200040010000000000000000040010000000001000100080020008000000c002001400100000010030002000000300180060010000003c00000080010010003000400000000000004000000000100000020024002001c0000008006001c000000c0000004000004c0020000004000c0000008000001000b0020000000000700000000000001000c000001c000000800300000070000000002c000000400100000000000002003800400140060000007000000500080010000000000000100140050004000001000300080000038001001c00a0008003000000200040010024001000400c000000400000010010001000000200080030000000000000000000040004002000000000000000000000001c00000040000000000000c01b0020002000000000080010008002000800000140000000001000800200200010000006000401a00000030010000001400b003000000040040000002003400100040020000001000000700080000000001004000300000060000006000400a001400100300020000002000000000040030020011000c0000014000000000700000070000000000400000100160000000000400100040020000001000800100040000000001000000300100040010001001000100000000000003000400400040000004000000000200080000004000000c0000030001000c0040000000000000100000030000001000000000200020004007000c00e0000001000c00000100000000001000800000000000008002004c0000004000000c001000800400000000000000001c0000000000000000400080000000006000800900000000004000001400b0004001000000000000020004001001000a0034000000800200000000008000001c0020014001000400200000030008000000000000000030020002000000000000070008001000000b00040020000002000400200040000014003002400000000010000000000000400240000000000001c002000400000140000000002000000000100010004010000000100140030004003000400000040000004000000400300040010000001002c00100080020024001000c000000400100080000000001000000100040000000006001000700000010010002000c0000000001000000100000010004000000001c0018000000000200080000000000000000000
  | 45 => 0x80000000008000800300040000038000000400300200010000000001000000040000000004000000100040000008000000400000080050010008000400300040000000002000000000000000004002000000000140040014001000400500040000030002000c0010000000000000200000010004007000000000080000004002000000100000030008000000800400000010000000000401100140020000000000000100040080000009002c002000000100080000000003003400a0000000000c00e0014004000000000000000004002000800200140000008000001c00400240000004003000c000000800200140030000000005400100000020004000000400b0028001000000000080010008000000000d002000d001000100080030008000002400200080010004000000c00c0000001000000200000000000001000000300400070028003001c0000000004001c000000000e0000000002000400000040000000001c00a00040040000003001c00100000010040000002000200100000010000000c001000000100080090014005000c00600040000008001000400000040000004000001400c000400400040020028000000000b000400000080000004000000400400080010000007000800000380030000000000c000000000300000090010002002000200040010000003000400300000010008002000000100040000010002000400100000050000000000800000040090000000000c000001c000003c0040000002000400200000000000000000000100040020010001000000e0014003000000200000000010003000000200040010000000001400100000010010002000c0000000003000000a00280010004000000000d0008009000800000000000000009000c0000000000000000800100050024004000800300080080008004000c000000c0000000002000c0020024001000000a0034002000c00300000050000000000400400100000008004000000200040000000000000000e001400300000000028000001c00100140090008002000800000000010008001000c002001800100140000004001001c00e0000002000c00100040000028002004c00600040040010000000400200000020028002000000000000000004003002c0010038000000000200080000000000000c0020004007000800100000030008002000c0030028001000000c00080000004000000000000000000000000000000100080010004001003400000380000000000002400000040000030003004c00000040030004001000c000000000500040080000000000000300100030010002001000200040030000005000c0000000001000400c0008000000800100280030034004000800f0008009000400a000c0000010000000800300040
  | 46 => 0x5622e63bb1d90d62a800a238000000187ea28800000000000001e801de0000d1a80007d536f634c0a801d98000000000000021d800025366b13392b2081dc38f80004be817a000000014a800000009305b6000000000000000000686ac06000196e9369230000000000016bc000305000000001a100000000000000000052800008600a40d6e00004fc800001f8e48a4b94d00000000000000000000000000000d8a80000000000d7900003c480000000000000000000000000000000097117c19295f8000000049400000001bda0002d1400037c60000000b5a93826980000000175050392da388a5140001790bee86b693e016aa39972e0da25fc00032f047a1252741000000024ce0000000b2d966ec8c0fee3290d700002b6cbe9000000000008e913066a8800000005e257d80b4d928b8e00017eac1c21aca4f342478f0000339800000009640001db600000000003178000000054a12f00000c3212c800076b9ce25010be60000000000000000000000001efc90f2b2a83b80000001a46466b00252780ca0000000d94832e9e62902000000000022bc2ff0d6200001ba000000026481c2af524ee000226000009961f90c506e0234a6499bce5329bde2af10648eb9d4000000007a7017017520982c7259ec058850000028c0000de2d848a640002a32000190a00000004b30b0a00027ac1c0aa7c000118ebf9000000016ec00000000002c840001cb69a323a21cf8000000000000020904ea80000000000b6d80000d5238401e8dae000103a0000000c30b6ecc53229600000000001ca6cad8000000000000034a843b05fa9b98b98000060a1d90e10000152e22980008598000000000000032e66ca2e5a0000000000000047506c288d93084480f9c00011f4620810c00018ba8cdaf6872eb61c3ba800064a0000000000000000000000b2a8608000924859ea5200009970fdc4ab8d76531930e6cd98a865e15e63088d8c00030acb598000093b5261110c0eb381a9ad730000000000055a00000001fb6a7a80000002f8a0002ae400035c817c80007e71dc450d800000016c4c41000005c80003659916af70000c69000012202a600000000000dc071c85e80310000af909a47fb800000009f80002a6400032b200000000000000000000016095020000d782a59a380001bba10194503a08cb08ff80009a7204a0000b3c00001122bdad94c1b284c00000000000000000238e0131cd222caba200023d0d428030723051a00000000000000000132a219ae203fa8b7819724f47f0273c8742c480231ab0b142a3601bb66033f8e7c4ff9b8841e9f9a733168641c1a10cf3a1cc9db9f48000000000000000000000a00b1300002ae0c431b9ecba8706dc29e669c7849c6dfb584d460000d1b00000000000000052c2d1800100300000
  | 47 => 0xd3d1d8c8aab5e68679dac1cc80005201c4438dac248ef368e00026ccd0687708838ae00002bee00000000000000a933362c38000000036820cb00000002cde79600000000000ccf2a100001fa8322908200033ee1052538c9db7a27a1000000000f800007ea08c84f6c4ea2b6c7536145460198b0f100ec2600009e936f00000d1e0b88000a9a80000000abe00000001e323f00d80000000182200002525e732d062c072e00018d22f8958e8d78b722109c38d5b9ecc3c981a000000003128000705800000000000000c720002f0e85080009d2af9e34e9b5411ab454564aa3e123000000000000000000000000005380003bd80003cc15e40000a740dc80000002b1000030d6000232866e80000001a5ca3b00000001274000115c79cae820001d66d4186106a6000058c0000a6d80004eb000042d0e041b30000000343e54780000002de6d3280009b4134c00000001c5000098424240000000bd8000074019720002b7e553800025134e0d6b14b400000007cfaa5a4dc1f32bf00cf400002629e180000000dd0000000039d1c3a74d0482d0b80fa4f300a40000000000045658b37c42bd12b20003190ac000000000000ba800002472e1400000000262e7e6b781500002cd40d88000acb32380000000ab7858a00013bcb050d6a0000fc86eb80000000000ca9a75626a0000000000000000000002988cee2ef208e24580000fc4000314672b000082e9732aec888ad5792229268000a9c251e0000000000000000036160000a4c000000000000000000f4adbe029400000009cc00000000000000128a00000000000000554b3da000000063380004da87f2cc4226400020fea2f00000000000000000000023b402e8000cfc849e58200005e3800000004dc0000000827800032c96f600000000000000000337400000000002dd000000000000000a3d08084bdb382000141215523ca15da3761890ddcb1eb0dc00035e80000000000127e0000000000000027f189e00030beb1585d6000247a0000000a1380000000000000000035580000001580bf3000005480006bd9dca000105a00012bc75f80005c22fb2dc5a21c00000000001b780002d16cc32a8c1ba000000000000002aca000105857480002e200ea194800000016789db000000000008b880000002828000000043e147416ab71200000000002c4a4ed911ec8a0886b4927d601f2d3212d80009e0000077ca1c8da200003369b129b1000004ca9e426b800063400000001eb20000000830000000000000000474a638000c6f80000002aa400000bccf08000000000071780008b0000000000000001f8acdeb344a5b8e142cc98dc254a9c48d180000000e524ba00000000022a2b17dc00008061c680000000000000000000000000000000000000000000000001d1a1bd9e7a45b00000000
  | 48 => 0x1f760000000000186a00000001481a263e1800058b8eda33480006e68000ace02965a384c40000000ac5b45cd48177034f24ca000018885b1644000000000007ecba50000b2e219add31cfa0000000000274699a00000000000000351031897ae5be00002973084a480000000148600000002120000b368000c5c80000000000b9a96b800000009cf8000bcd80006e52f9800005fc8da00002e00000000342a2e08592000208aa1d8a5039c8bfa00000000002fb0a490c98000000006f000000000000000000cb5000000022b400000000002ff600003ee000000000025a0089805a000000062c9d44b91202c28b1b4e000104a79300008d3800092e1fba0002bd0ac3241e1d60000000000000016c20002f2c1932070a0718e411980003d315fe05180006b28000c851220000294a0fd00007302a06d34b0929089d1600000000000d4c00036040000000000000000000000002db80002f067b78a1e0d5af7864a8000905b3000000000a5aa85e0000000760800000000004349b0c2d6a87411380000001ffe000000000027f20002e0600000002fba7dad2f87200141a9cb1f8dd6000091000022b84f600000000000000000000022660000000a8b00000001328bdaa04c66f000010e000027d0000000000026f35000000b0e820855a1a1a304d5210100000000bfa0000000196a00030b0000000000013b4a6c0000000321c21fb3707480000c0f800012e800097300006fc80000000fc6a671da2000090c676a9d2767085aa20851036eab9e00022281b398fabe535a200010a800000009070000000199400021a2d760000603167c000221838080000000000b2500000002d989d780005898000b8b0000000181001080000001940000204200033566579f846ef1fc223c00009af95b448e1dea70400ee000000000000000000000c58800000000000000000000190c0000000000215e00000000000254ca780000002884732000000000000000000000296000006dc000000000000009da077c1428f880001dfc82706b0000000000000000000000000000000002d87b8000002e0000c16961e94905cc4500000000000000000000000000b048000870000000023b0a1907b2cfe800000005dc000187800000000000000a06000000017f62a300000002f04000000079b0b5e99427ceddd93f06148000c948000000000000000000000000d08000000008e2baf800050c1478cfa8000a70800000000009fda58a4d380007a335721a800005c8336c0001fd200016203a909080000000841af425b7a8786c29f0890335f00c4959c00000009f7328a0000004000000051f83f6d9a25d0c572f503891a1c212b54e6f72fb6d5d2d7e8c4b56600031d6a0c0000792094c37e8000000000000000000001bd85a30000000000000006580000000
  | 49 => 0x8000088c000376234b848a0002f8c92382cc09d800060d899c730970a345000009f919e00007cc3e78052d1c11e6ad69952173800000013905cf802e13000000002bf6abb217e000000099080005c10ce000009ca68117c850529a6000279e00013c8c99266c000239e4ee145800000000001c7e0000000c688000de80100580a3c200000006890bcc00000006f500007030290000000000008c2a83263e53000009f615da7e092b4692800000000000000000000000084a8e8c0002f887b900000001c1c401b6e8cec9ec600037ce0000000000339c00000000000000000176471e2548476285c0000000b9500000000000000317400000000000000000040c70917a20000f7c00000000001b2e2e907acd54ae8600000000000a5ede79a94aab80000000000877000000000000000b120000ba6c0719ae10a06cab7fb4d65ab117a43100007cdaa7223c86c6d161e0e00000007f62d00c7a01a48338aea5a580000003262000000000000000000000000000034100008d880000002e02844a4cc0001c46000182a68eb5dab3193840002c6c66b2ba67479e5631700000002fae0000000b7d80000000000000000000000001e5800000000009b60dd4000000053d341200000000000174c6ba95000000000001510be8800000019480000000cbd0a900001d0c99da998c2f3516ac6825e0000000000000066e336e00012e09750000bd200007523316271898e42480000c2800000010226a98e6000036e0cda00003b30000000000066fad26adca7a6000222a000000000000002f6800031e000000001e8000288c0000000000263c0002ac62dd87687b2005e000009a0d19fec76a08006db10500000d90d48a20433b27c628822de0002dfc4149db04bd044600028806adad4a91d8000b6680009a10574000000000000000002e1c13d350ebe10acc4388000000000023a05c600014a60003116000211600000004150000000000000017fa0000cae82a000000022f8d8e250e6219d280000c06114959e000013a00013e46b500002ee0000000130200009de00000000001fe229a8000a4f8000abd000036b1baa8a832cebcf80000000000a6b1fbcba48000bad09d66feb7c000016f00000000892800000009560002daa0000a1a25980000e180005bd00000c3040440100000002e7a42580003939ca298680000000000df800002458000000000000000000002cac0000572abfa168000331ada400000000000000312cd0400000000412d6534c8444800099d1e860001e18250af22005a2da00000004d58000000112a36480006f5a406000271c0000448de996940001adad02800000015700000000a7c80006f3000000000008df0000de20da00000000000000000014f6000000005b8f14874adeed939542aab000001c0000000000000016ce6eb
  | 50 => 0x7a0f800008b424900000000000000356a768000000000000000df600034823191b682b89680d2c2d6e7048000000250800000003079d56bae80000000000121a8900001ed8c15af7c3abb25602c00000000000dc033480000000000056a75623c078c25645f58d0a4d6a44a46f810e1e634983710f280002f0200027767371100000000000000000000000a8580000000000a63000000014fe8d10a62a67b11c65529f40000c0c8e082f60000000000246849e8ede00000002a882e47c280008cd081e00000001869ff2c3e2dbc000257a2742dc600000000000c2a00000000ef80000000000000171600029a02c800008fe80001430000652b37c00025e44e1b42c754000096b800090837b032880000af246a510b6a656a0000d099e5eca700008a00000bb817e0937800031a96e20000000000155e000347e0082b6209000000000000000120c00000009ea266474fa13cb43082e2a780003ea21ea0003292a84a38671c00000000000000000000000003458c5a0000994d3a00004f8b278b200000b0f80009e3808000031e400000002cc0000000000091c0000939000087f8000851000000025868a180000000000000121e000000000009da31c264a4d200006f08000000000000000006cc80007a62bcebad80000000000000000000000000000000bac0000a6f000003a2bf80000fe00001880a27936835031ce00000000000eb2c7b0000000000000028de7b483c04562c1a00000007f92a8090c962a0000000a0d0000c7a800082235ce0000000000000097680000000000b4f000000028ce37600c20001cc60002324cc48000b3b000072e2762d21a2ee19eafc6bb1000087827e4c828000a15800000000f292e9986d1a10320003076000000000000000000eca0000d74ce831969199f340000000c1180000003626b4b29be0000bce45900000000000000000000000000000000000000000001b818a05b80000000a462edc1439490000308a000000000030fcc7f06900b287da99a92eea910c3cacb80000003554a94b694da90f1ea82113600000007ea800000011ee000000000000000000000ca5af3c6d61d4a000149cc392572000110a00009768a7800082f0000000000000000008f88c240ae8000000148a25b92e486aa0e89ff000060d00000000000000000000000000000000bbb0000000332855d997cddc8000000049097d2402000333a000000000031586ce80000000000bfd3570000000000000000001f1c00016ea00000000003416402000000024085d1800046e00002ec32d8000213a4341f70446820011296905ed000000000000003298418854e000110666c02ac609095c000098615e0478468800000000000000000a7210d444d00000000000d7700008d300003ce2b088ba00740001b52d01b00a278a89cde11e3
  | 51 => 0x80f80006fd131200000003940000000186e0002f302d405f60d32e28d622b04bae00008a9322000001ca5f8af28864929a70a2d5e000334eb0c00007b288280002e362df20c600030d0132800067d089400000000000bdca8f0000b9980006a1000001b00000848000335129ed2e8000000165a0d4915aa0c8000b78800000031f40000000000000076e2bdecff8000cd2928c3d80000aa100009c51f66c718000513135032808fe00004840002c8e00013f46f900000000000a0f27f40000c52000124a1f511e04911060b1e0f64b5f12c200029543fca9ee66280001c4925cc520000000000000022a804226023248000a5a0a6e3d70da4b0304b814e9c98834b13c7a504b400000000000000aa7000066d80000002dba000252653c9ae4675068000034487622ede00017bcaf59bc878eabfe00023580000000389800048b1c301bb2e0094a0000000242600023540000000963950e72380005dd31eea02800000012980000e5e934000000000000002d8e00028d000000000002d9e910862a16fa9520002d3a5ec81c874e8f108d0b0f4ac78000000063a3210000000241a37c8c900001b5a17f80000000000d8300000000000000000000000000000000a9b00000000f5e000043201500003662e48af8b0ca3328000000000000000000002394000000010eaff80002ae80000000000000070d000000027b49f51e2837a250200020ea00015d400037ac050000044b0000c0c8000145999c91582502f600000000000161000000000003e8800000035805709fb80002054ce1951a5e829f6b149d94272117213aa0ca6e900000000000761b7661351a8e0000000000000000000000d68000360800000000001a30000b8c00000000bf677780007d72a50227a54c00000006b7000000000008f6000096f0000ce995ce00032082a2b2b800025062cb000000000004c68358cfd9e2c86237d20002f164a8995800000008bd0000000000000000000000000000000000000000002ca24a02b58000103e000000000027ca533a2400000000000000000023100000000638800000034a0c9b8000b91b0c841b9cfe69daaa03330bf854521f42581f1244f8f70a0b9b1c9dd335cd4b323e00008f63eeac5842835500000000ca68e0adc728e0a570f52d70a51824e0000000000000007d02d13590000000092a279cd5300007a0a06c7fd368600000001d3154a0000000000193200016fc0000dda00023f80000ec600000000000000a2d1098ad982928893540861a028894032a46407e60001aec6c1a2a2714a8105cd8000000000086d209470791d00002d8c6380000dcf00000000ffa4920000ca80d544398000218804e0001c26000235200000004e7000000000000000000a9824500000000000000088f171cb17237a0000d1200031fe000316091
  | 52 => 0x20c414f00006c000001c6057e000207a000055eb848000039800000000005f383de54f2f4e00007a6dd600004bb000006190ac00000000002a7831a00007c300000000e5cdbb800000015aa1080674361800000002fc4e0311e5e58000d5700003c38bba3b41ec267bac6618f258899ca5f6a9b8000ae00000aa6909edf60000448a3ea3bf8000c6f00004e200000001b7c718820c7be1c5c5b18c86c16057c91137048e23624d2db4d4b4a353893b37a42dfa0200000000c0c0000000000000036d4000348cc981944440aa000000db800014285d2a146d0a137c390aba8000000012a00000fe0fb24ae000000022ec0b2297c16983205c6800000015a451b0000def15bcbea1aa41100b5200000000002fec89d20020000000a1100000002d6c9fa24fed75800009e0000000000000009a60000000000040e000000065a0000000151284f8744218267a13593c00579af20778000b8f2742367a970c4a2a0ebb225967310ac69472eaa8cc0000283800000000000000000c38a9de0ee03a600007ce00000004430000bb38000c678000621000000000000000000d3300000000ebea4735ae00000000002fe6000038c0001cca82893589580000d64976e407ae1a00018f6b00ad68cd411560000e96ce32c54000000094f80000000000b7e80005eb32bcd8080000001f501561fde93f0000c84800065fa54a59b06ea05f14f8a320000d4da2d62ef376e0001df00000000000000089c80008a633e60001304000000000000b20002b1c00000001d380000000aa4c593472000223a1e900000000000d47afdc0000000a95b4340d9a0dc0000dcc0000000329847c45f97ee00016b038e07422f935fe61d96987568000ae3804aac39026000116ea1fa7967018d3499000008210000983000000027d08eb02f2a0d800000007fc00000008c5a6b29c62ed23d00bca47f886a54a8c58d9ab6501b80f900000000000000000000000000000000160a00000000000000000000000016d0632b53cb23137e5900c005ed98380000338000118c4b280002312cbe000121a0000000de6a0248e81afc9a4a25206a000022a27b60001e500000260ce00000d69800001e00000001ad8000000037e327e00000000000000000000022715fa000071e7a800000000000b6a18120000f9a000244c9fa98e600015040000c0476d0000bd5000068c8000aedb06e9a900003da076a00017280002ba4b6d187c0f29076a74011897a087a000000000000002c600008fd992c000000000000009912b9c00000000000000000119c00012580000000000000000027229ca10c6ac191b00001fa400000002db8e6c00002248a382f431318a60000000cb1b5ba0002438c4e00000000aca996a12e8bea484534aa68c3123a82c19a48dbf800083c00004f99a6a30c18507f380
  | 53 => 0x7060000000dd100003bc80001aa80000001b100000f2cb5c91500000f1863d27c0dad1f7a00000002d8125e00003165b00868284129c72ca838841000000000000001336000000000000000000c6e96b0000000000085c80000000000000013000000000001828bd2934400000001a78000000000000014ec1488c9a0001c88a118ac20000c76000000000005346698f625e6b7521559fcc000000033c136039e80002aba61866a800000018c820f32a4b341c7a71830eadca1b30b4aa418b2d00004600000315a11c204173a0001a08000000043a276a77d0000141a9ca8e400001a49dc28ab35fad528f96000000060620e0524800000000000002a920001daa00034880001cec96080009fc23e400000000001a6cd5180000003332bfa8000000094e3528000cd526ac3ec289437200005d127260003460acf158c00000006808d06c3d9c6e0f509c05a123aa42721002428000333907ca1f29460000000bb9229c1000fa4c331074091b5422da800045a80c000016000000000211000000023cc0000000000097000a0df01cb1712b3aa0a40000000b5d0b70d869f10123abd200000000000000a430000619a60836c32a88500ad600036de0001426c9b09501df84aad07b0de17b239a2cfb48423595bacf58000641136c00009727ff05a200000000000000ca1a3260000000000000000034a40000000c6980000000000508a01622889b4d74b6987192e840001b020000e9e8560000887a25e000000039e0f94ce631b4000190eb4c0b10c6ea056b4426120002282000000000011300000000a86ab4600016a2d4c800014980001b7a22e00014389150000000327c98e283e000000029a0000b1180008038000000000000000000000000000000000000000000c1600023e80002972000000000000000003122000347400011de00019de0000000daf1b6a3370ab24e6223eba780000001f0667e2a1c5b5b64200018c027d96aa84b00007980000000256600000003aa892e00000000002f1a0000000871194cbc488726f9a580cbe922ac510000000000000000460000a82a7000000dd0000000000000000002fca542d3f98bebb416cc0000000c89000000000000001b6459335684800d468cc8000000102a2e18000409000096d815422583800002c703198d5ed8c9dbe83f22dcb9d09689cd1a201968d48000236461601e2000000004ab17a280a5c200016325e51f3c24100000000000b3c36ae8ef800000034ce7341a5e9c1a4bcad036960000000cf50c880002e24b7a0dca30b1b22000107e0cf000000030d4c400038d2780000000000000000000007dc000245aacd8cb67af8000503305447e9c76c2d0b8c00000005f900001bca85800031980001d7c5f6b6ea6ec9a16663895a184ae8ebe5800000031b033101781d5089000037080
  | 54 => 0x7ec0000d24800000000008a51538406108c00007b84b034563ad9bc6693895e584086e691034800000000f5800000008f4000000076780008c1b3947f2a6fabea80000001342b7600000e8076e0001b48695103400000000000000c6b1d602ecb6d80f333782191a8a878934ab9b0142000000090f8fca0000b347492b7ac77013479080000000000000212400002282a80d38c7080000a280000000000000000043232900bc2d4c55ba17a00020040002b7800029f00001e12000000007d8000d0e0a9a50180008c080000001294000336000020e20000eee4fbb4de071800006d00008c20b7a3b59c808fb32c8610000077588c60002df80000c140002dae00022563bd30241910eb470b800000018a4374a46400012320000000000090200017340000e64000000000031d20e200003ed80000002022cd9b5d40000000ce9348a476b2ec000293a73e0000464964e000000051f000000000006d08a5632e8000000000000000000000000000081a00026e801a00007ba8984bf78000de2a20c0001b9200000000000000000318600000000000000000228468b111000000f059f8e205720eb000030942f500000002c5a04f1dd000025220f81dc014f8e4685c10ea67f2c9a00000aec2680000000000000000035b2b4c00000000f1000000000004c880002e8800018200000001a7c9ac00000000000000000000003000be9b26c10800011533260000000ce69040d36365ea5582b200000000001eb8000097e000000000000004b78000998aa0400000006b58000109af1e0000b2800000000001eaea5137d600000000002ca893814980000e7ebbe9dc800031b20000000c8b967a0000a0a00000000000ed4000003e00000000000000616a42e5fa06060d017a44d79e0a1b1234035a1148b1f205809b8000d0c0ce88232398a6eb07a302277e0000ab87faaef0823b2ba4a48000c53a69eab6b52836da5b4ce10000a640000000256c0002ffc65712680000000c970b9668b800000013b200009b665ea1a40000000000013e00036fa46d0000000047a9998000c46000009d00000000000000000000000000000000000000044b8306000280e39502e8000350400029e66ea2212a733034000000000012d275a000097caad200000000002f62967000000000a27929a92d370000338a1f85d01446000034e8d20000843b006d309a4c6f4000035cb4ec39699cc495178064f2f9a7489da400001a6000000000000000f8a91a000099a07e2910ac507600002b260000000a3531c80000f0a9222b22000000015080008c880000002aa693da74c00000000000ad41b88e400ea9f446abb2c233d80001a394eecb490fe12c1586000300e0001df6929231831510ca00000000000000b2906e4411282600000003831c8200000000001898a8e00000003
  | 55 => 0x257e000000010baab874ab718000114e710800000000000002a2a00015d8b228f202bb90da1200aa6a1b02fe605a78a04a01946a000000002dbe3dc80000001b6600026b493581f40000282000251269e984c89e000000007e87578b8a9f7a964930245c45d89fa04b8aa8bfc9c9a00017c60000000079059c000067e0000000d88800051e837c00000000000422000000000020de288b50c000000000018741a200000000000000000000032e80002e1600002be00003e471391a0025a1749d100000002a240000000000178482aa122000000000011261b515c02ba00000000090000000082c3110000372a0000000000000000000000002080000360a00000000002f14a3591d65f79674bb2983a6ca80000001634c07a5e03d20000000000000000000a12814ab0975c0000802bf2000097e8eb854f8000c968cde4e680002db0912c761c7c0360000039238c398a694a021c3291e12766e0800000000000000000000000000034f200000000000a3a0002aa872a8c9e000000080c94ba000000055c84a215bb57a000000073a00005f0a00000000000000000228000081429940002b82083ab48d2588e6000096a636a60648f32f671d1f881341e6400022682d507564b9800000034a68f499e08b391b20002cbcdeea56284295ec6009aaa00ab2581cd30900d7945e78401026be30da01121c243620f2aa8aea8db00d4e780b41875b0d5216a0000000008400021da00000003180abac8980004178000000000068f80000000000c59b4d09c6a6ae67c1d4c4f70d260001d7600000001020c7c7d322a61bf9a74af115dc764a6325fc8000bff80000a1989c000313600000000000000000000000000004d90d7c0000c4806d8000000322c0000000000000044395603861556a75900c000277000034442bf31e00f60b2442b80006831a86cb70000000378c0000c120000000000000096c8000be08000a269788b6904a4d672d3ed4e80c60000bac655a7c20001d0acbc8000dcc0a180002e7cddc15c600000000000e3abf68bd60000c42000192099c00009b1ae4292d16140000000c3192b02bb2bca0b5000060100000000000dde205a0000000000000014480007dd36a20000000d23b17e000000071a000000000000000000000000000000000001cf000000007a6a0e40000000a05a72c06a96a0000042400000000001bd200027c43f08000000000040b0000a9ea8fa0001e68c5ab6b605136cc0000000000253200013fad6d81c03d4000000000007f1891e000000072ba4620fc14dc62b8c7a000063000008d4000082c000247e1dc94180000122ae40a7298a09a0ac8000097a800000000004eb80001b6a2d40000000b47000085e319cbd48000000066e59da0d626002c21c90000000157ebed000042002687f5000080d94a80df9ae8
  | 56 => 0x80a9068252b0000a4a9714c0e00004548000df880000000000000000000000009de9fe8382000000029160001a002d600000000396d141d10acc0000c7e0000688afb8c3a069ac7100003ed00000000000d69132600024a6dec800061705c018b14b627c2200b9614c400020140000000dce894a6e8a72ac0a80000000000496b0ce1b400005da80000002e50bca80000648a0cd179ae60d4375e19cb7800412e34df930d2af18000d2b9f5e0000f0c0003702000000000000000000000075b44e000000056cb68a2e10000107a93400000004228000000040211080000000000000000000000d0d5f893a00035a07bf9da600017003cd80000000000166800000000004c8000000035602a6249c1cea70c0000000a180000a8e8000000123e0000bde00019c6a900000000000086b800000000009ee80008f580005e48000000000035600000000000d7d00000000000d8a0000076133862800008ed80000b5b096588ae5639590023082dda00000000000a925f600000000888b500d5059481489b20000a16805c00028f00000822360344a411800000021b2000000000025e600000007868e1e00000000001d52000000000000000000000000000043c8000847800000000000000076000000051d80005e7aa98000000000000005ac85c200027ec00000000001ee8635355ac1f18c6cf813ca0869b56c2000005b90000000000000000007a480000001e2eb0b0cd847000003ef02b023ba6bc00032500000000c3980002ed800030b80000000ffe0000000000000000000000001c500a785ca6fb2c42478b1ca6150d44add0436ba5921c4f50000384800000016246228000b2c800087d899e10f806000022ca7210b3a000023e0c512c64f837420000000000031c0002374c9c8204000161c000000000008800002cf200011f8000000054c8000000000000000000001c08236a2d000030100002bbea578000b19000084200003e10594658b5448c72aba3eb943e03391a48dc94707e78fcc94d25dc78a987a0000000c6200000002482000000000000000002abe0002314cc80e2c954abc8183124e000000000019c48d71bb6cf48000000228a0000d7a90b000022c000080c00000002472313aab04f08000ca013de0000ac8392800000026aaa2900000000000bf100000000000c0237742e680000000000000079a00000004988000000000000000008d695de000000099600004af8000c651a669d6335e000000000026f60000000000343600000000002fc2746000000000000228c18046aaf200018680000000742000000018f200009d2000000000014bc000000023400daddf000016e800000015ca946a9dc000000000011700002e3a00007f8068998049836fca8d0ec01181d72000000000000000bb2cf40000000000000007e8000aff
  | 57 => 0x1b7e630db1020000000000000000027100001e7400000006b38000918000029e32f800000000000000000000053a00cc0002c1c28d8ed22ada766000000076c800066401b02d2186cc0800007790000000358e5860d108840000285b048000000000019e20000000cf721d6c9c000074cadac106968a000000072d0000511000000000000002f580001d7a0000000000000015880002f224e800000005192b52db100004e513b03eb1974a6580a000000005d3800039a9ff0537a37e0001ce6000133c00025d22b1192ecdaa290696800098a80005ee000047c0000000038400008309fbb5d00d90000a60800000000008ec984a4380fe4db180006e3b3640001f260822bf23a1b41c9a20000000000082e0750cbf800013b80007bd00001e38000000194600000000000000d901224db58bea3c92dde35f990013213141e5225c6988b2ec6280000000000b18861e00015588b1000000029d8a1ab04e000000029697ba8539550179101c1422d1a000000000009b0b9b800000029fa0000000000000064c00005bca24884d2ed882d00000000000000000040282060002d12000000000031345040000000108825f000000000000658000dd38000d200000b3e149400004e800025de7d8b2cc0000000000000043900001858000000321023e14b2000204022d80006d705a06ae0000000033e4d9825800003ec3438000c800f06a421668b0e00003672b56877800062e37d49be272e24f0590000000029eb3521de98bc27c9e62a479bb80eb2b02159ac4e30d021684a0db27f8179885531f06b1b620000008e00030a400032368f38f6c000000095f00000002d7a9878000dcc92a044f00002438000000000000000006d11d149feb24490d0000d67941a0001d124529760b1c898a000087000000000002cc8a95000000000000002410000000000000000000000000000087a1d54a0b288ac7400005609ea80002c9624d8000dd00ee4706000042c88ac0000b94000000000011e4000320c000000000025f0000000000000000000000000204400000008440000a568670bce994e9718000d6d0000000000000000000000f5400026302938000000270ab3eb072ddf80000002d02b720000000107800000000000fe200000004ba8cc800011c20000000761000000000000a700007d0b6ac00008167bcae0c000000000000000002f9210c0ada2fd00007ca800000000000000bd217c00007100000000000041583d0000000013f1e3436130a05b20230b062d5634f98486e59e8eba0287a62200001b58000000000052e000000000000000000000000083e80000000000000000082b00000000000000000000000000001f2000000004a400008179a5200000000ca2f66595800006fa0ec9a0000053537c26ef800013b079e3d1927225e9fa027a86b
  | 58 => 0x707158000dcb800081f000000000000de06204e806bc4470000dc3800095a000026089d8000000000036d0157000061c80000000000000312a00000000000000618800000012064cd0c82000154c00013ce37d0000b8e1f3a0000000000126621f2eb2d24000008800000000c1c000182e0001264000135c000305e00017c06dc8000424000000000000000000000000000006ee9b48000000000000002d0d5d963e0002d364109f864422b341989500ca08000daa00003a80ff800000004652d8a0000f3e00022065908000a300a2a0000000a2f80004132d8018d89bed3c11ac22908240baac0449f096c8309fd00928000000023ad0880000000000d020000c3c800048b9a5643700000000092bd180004c7ae644288fde000228c6729e5a6dc0aac5620b36c20816c000000088d12128172c3a20705186e6000000037b66909aacd1d93a43911658cb1001e000073682f80001540000000000007b1a0a00529aab590d320001218b648000c2d8000b7122c227918080001e000000a14cf2000000035e000024b60001ff6879800015e80005f283e89d680000000000aba80000000000000000000025a67e6302e16233a20000000db29cf2000000000000000000000000000000000000002c28765aaf8000000000025ba00000002f130121ab81f05c606783a695cc777053698e8000df6800000000000000000000000000026fea88b4620002a46896a8d800003ae55197020003108000128e0001c20dce155400036b2000301400033c00000000955a8628ac8b4a4ef81ac000000000000000000b68bb9a006000062616d9e1e000000000026e249b2072000046e11d80006af027038b92ce561000000000000001f6c4faa1480000c96964ab8ad6a0000000021e000000000000000000000530a03400000000000ad8737b12e00000000a8941e59c84d863f80003a6000028a000096aad5ab840dce955090000000004b58000000369cd6a84e451888123c12abc00027844822df0000000078d80009412dd21f8b4f8000216016d0dfe3a9b5e256d802c63a800020d80000000000d010000000266e8bf0000116afe2a03078606b80002eb8920ba9265e6aa0a043d10b900aaae8800026221f0af1c3859f005781b7a53a8000000000000000002d7142000006540ec31685f4063e195a0a0d368000d9e8f02aee80004dd376c6afab0a891000000000000000fa604b2dc077a000000000000001998000339e000000000000000000c5e0000000000000000000005c990b0000092800027e01280000a71959800035964f680000e3b0641e08c94000000092a800056e0000000133223b216e0002a82000163a97000006c6953a93c0000310213800000008880d662bc000018d1548ab3000000000000000000d8e823c6bb80000000000a2b856c37
  | 59 => 0x822e78df4267c951062e0000000ccd80008fd000000000000002bda95b8e348829afe978b204b1780004de03224e59c9cb680000000051cd2aae5e00000000000000000302600021ec75c00000000000000000000030289ef800092b80000000bc0b1a00006a58b9ea0803442ed1524a150000cb79be07a40d6427fb1f2dc80000db9acc496300000000000ad082d281d08bc2d02906a5d16ca75180000001f8e512a986d8d000000005bc000324a00000000001984d1e00e23e280000002a62000030e490a8aa0000182deaa44051a1dc6000000013c0000000000000029a40000000c2a80000003692000000064e8b0c9a98000000000000000003fd9ca00000000d7c882000016e8396346600034c40000be893200006b0aae60000000136800000019b20ed8000000268276680005c78000b0b800018e00007d48000677202a5f491ae8b900003b7000038c0000010000068480000002cca4fd995000021504f1800000000000a025168680000000297e7858c1085723f20000e3c1520000000000000021b8000000000000003ba24c60000000000000000032a2ab400004dcb20e00024942a11eaca06a87055e000000011aa0001a7070680000002a940000000b6c0000cbf0000000093e33eaf7e9219f6e1e201d442eab3200025983b88d94000277817aa2b00048000c23800000017c4ce422c67c087c40610000000000095d000000000000003630607800000000000000000a10800067f80000002cae7a2a00800003a46b8abbc0000a60a9f89aa0000000000134000000000000000cc112a8000149600030744e38000ceea90e00000008bc000086108c000000000000000000169c000000000000007939e5c24893f80c6b25e3582cee00000007c3870c6ed333e07f2936a093266ced00000000000735882ac2e0000912000000000005a2209a3de13c40002ae200001903a000004252da200000006f2800004e000000001cc77b03fc6420000000000000000001748000dd90000000296c082800087b98fc00000008d435cabbd0000000333400000000003756202874a8988202c7d8a4400010ce0002010d4c0000000157a1058000284ad0e000000001920a60000000000106c00019f2a860000c1100000000000a53b586ded0000114000000000000000000ab6327a0b78000000000000000000002c4400002a000007920db2d0654300000002ab60001aa000000003ab0000cc201e61661318addb524c9180000000000000001ab07923436992d02f8000000000007d19fa2000000000000005090000885000000000000000000000039c0001f2c0000248a3d81fe000000064f87160002b2805580009c080000000000bfbac90000371e00000000002b3e000191400000000990000b6980003f3a646c1280000000000d8b97520ffb6
  | 60 => 0x36360000000a3f0000000000000000000000000000000000000000000000000000098da6c2c3eb16e09590865a780000000000000202e00000000000000b78364c0000602d4f9de040e00000000000bd1000000010fc0001f04da68a8886391ea3cc9214c888000afb2c2200000005b729660001c4c0000000617ab6e13804a66fa9a405b99e46d9c8000c60b75a000367e000029a648a55c0001a34000000000000001260000000000000003700e8972a000242a000227a00036d2d83800000000000002e04b3087fadcf80000002a486dd15fc0000e687af026600000000000000d9b88849c5a3ee0001d74c77a65208d2292000000089fac86000000027380000000000b860c8e000000000028ee733800000016e0000000000280008a6800000000000002efe000000072f22021db0000a26042a0f70000c4c88faa0495ae32faa58dd2870e64180007efa16a000201a00000007c59776ce3868aa5880006cb0000000214a00000d489b33183db800000033ca00032340000e1a0003736ae504cc00000009ec0eba5c38000bd6aec058194e6611800068180004ab2f5cc4180000000000339000036f800098ba300000000000000007ec8000b08215200000004fb1284a308000000115e00023c80b38000000357c5570000ba60000000000000000000000000000000000028483af0a8e43029ce0001c2c8cea3e000000003f0000000024b2a5633ae5bea7bc00000000001118133a1a6c8aa9fe0002e8a50f0f566c108387901f2e30e23d40000000d1bb63ed3d905c00023e6c81800028d1afa00004e233c80002c59730000000000000000000000a7880000002e72000000000000000000000536142e0001d3c1be000000031cc0000000c4386a20000000bba0000000000000000000000000774800000000000001324000000040c00000580000232800000000000000000000000000000000001b8455d00003ce8fda0002a880a386be1e433b0773089ad0e800000014842338f34b0d0ac000600000002a8a00026906d7aa28000330e0000000000000081a80000002d18000000070f85d000037140000fa000035c6000000000000000000f4e000000000037488d58000d3f00000008000000000047b000000036b879f00dc8b22ce232aa48acdda5d8be9a30c6d30000719800000008ba55b0000000000000000000000000d9880000000876bbd97f819919b400006040000000000000000036c87d925c4c270000bfc00000000000bc2000000000000001c2a0000ea200000005458000000036e00000000001cbed3033f81d6affa00032d600000ec00000000000000000000000010206378a4600000007aa80000000000cdf8000794b1aa0000000000000000030fe1a50e8800000000002380000000000000003f636180002efcd
  | 61 => 0x8a228880000000b9d8fb80000000000000000000000000000c5db610a218000aed00a6a92a980b2ab2b47c680009688024d7b091a00000000000000000319a5d3011e0aa1c142a7180ac012a1e000199a7e42d2052205860002bae19aa1a84588000000000000020d000022ea0000f920000000bb59ff8482a2542b9acd8000000000020766e31c0ade6000069923c44e280009b39842c3c00000002d8611a0000c700a52350a6987cc0000000000000000000000000a780000de3acd60000000000000000000000002f5eafe80000000000000000000018e8de0800059880008ab8632000000046606ac3cb977e6ba8000000000040b800037998aa00026e0cdc80f600eabf40000d0230a00000001724000317c0002c3619194e2000000007c97820000000473b1da0002dccdb7174277f81641920e70bf586fa0f200000000000000000000032aa00011dc92f8ee07b11b9c49bb02c90a12c86ad0000bc81f2400000001aca9ae80e00005640000b42b3e20000ef800000000000000000000075a8000000000000033beb67000000000004ff37940000000000000000000000000000d2d0000cf7800000005de0000000000000000000007ac1f606289924000000004800000000000ca2000069a2c080001890000212600036a04808000262000078100009ae8000c9a80000000c2684da0b2b5500009a18000000000083200000000000000000000010be0cc8000d001eec8db1ab222fa0aea0a8000000117800006f400000000000f1c6309068ce2284a97e08e467425eed70000000f2dce0daa5a4b8fa806213000060f0bc267900000002fac00033cc00007c828b800000000000002bc2000000051aa53a412191ed00ac9e89c000062502e00002068aad0000cfc000099e19ea1ce09a200000000000000000000000000000000564a4287e06158000cc88000000275c000332e00000000001dba00018f8ad7b15ea2c00000000ec200000000000000000092c631000041a8462000351487f13a24e31fb40000700d71218aa371400b8c81803e60000de1aac497b022c000183e70f0ffc9c48b263f48000000000000024f2a1a09c27df875ccb88e840002bd87b400000000000c1322420000000000000000000002b48000c448036b708000349264edf312d48f6800020504de9561a1e802a2be0001efa8120000a2e1ce4a7f000000000000000000000369e3ef800090c203c9f4ab985152fe0cb90272000142cbcb8000c101e088ca80008e5a2f2000000032b00007eb8392542a9ec0000000000056056599603f400000000d1800007b600000007bbb49c000000000000000c400000001be285880000e680000000a7e716000063c003475387ba0000000289a498000009cdc880000000000000254689b825a0000000340323c0c100008198
  | 62 => 0xc2b800000014b0d958000cac000099fa9a264611320000000b9700000002d2200024d4c3b23ba00025ca1ad2b4e000000000000000000000c50800000024123d992a4d6f8642bc9299a000000092309ba49e0f7e000219608d800088980006d1a8f800000000c985e00000000806000037800003790000def80000001c0234680000d28000b4798060000000d0f33c4900281e00000007629e96bdd8000a4123c693080000001eb48b800009ad8000aac800074d800000036f24eea8f222e0000429922800000000000000000297a0003018b37041c1a7000000000009e42bb003f87b481e0974000140a0000000b5830365122f8e52300003a280000000b1a000000000000001a980007d2884e0002b6400016b62c7847e57c349498517aa0000000000260000000005992b840000000cf41d0e000000027700000000000000073c000000061380000f495a0000000000000aa57d1cd8c80aafcb65b4e60000e06000217c98d27ccce59ed65da00000ad8000000131c5b684642e815e2baf0a3c3e3af74000000000007748939df8000164800012fc7a980000b9a6ea00000000002d380001b8a00000009e4800029226d4d108cb494f000044e15080000000000000000000000000000000000000021302c0000000036e2cea0000a9d0000000000042e000067000008bd8ea86c585b00000e283fd00004e983ce8189dcebd036487ca375422499a43f991842c121d40000a243e080d6052aa768da800000000000000000000000068a02c6ab5000009f00009370af200000000000000000356c0000000000006600000000000000d9b0000000000057b99a20000d2200022320000000b8b95642b42ee25aa1eb6104224c0000000000000000006d8d4ba97800027001cc000081b90c27e00000bdeb512000000004400009d4a5b06c21d6e66490f00ae00009cdb562000000000000000001452b7b0242aa5800000000001fb80003628000000000056b2a2600000000002f800000000ad10cea1532a14000274800000000000000db38000000114cd80000058397fe00016364d4a3b8000000000000000002cf60002900d6c9fd62bf80009958000df2800036200007f1308820f800000000000000000cd629b41510000d99051e00000000000000d19000000000000000000778800000012f20000000c8580000000000b2c2fbc66234ac46e8000000000000000000000000000000026400000001dda46217ec000000023622d252916a45bf991000000000000cd00000000000064e00003020000000000139e27a0f740002e0e00000002ef8000000053229528e400023dc0be000000015d6000000000000000001d427e48000c6307f40002e520000804000375c00000000000000130b23a000000000016ee00000000002c320000000
  | 63 => 0xe09ab606ba405a43308000a3480007830f084519c96000000000016be04d85460002fd4abc09401d48000d8f34ea9579982d38a07e214b24e00003b400024960000000481254e1b200000000000266148e0001a786e81ea4de597107890e6e17e00000002930000000039d86d2bf60000000000000000000000000c3bb3c63d0adf2000081800024526fa000000032c00001c0ebe827e60ea0000000000024a80000000000c6a038a3420efc64d000000980006d887d200030d8000000000000001ca2f182d90000ac62de40000000ab200000fe80006708000000000018511c82780000b2602440002118dc9221a5c89e1cb60a1be61904d2335800059c074625500002330c469bb000000000000000000855aa20000000088200000349a6e47300006068000dd18000000231e000000000012fe0000d2c1a936e400019f640680000001d9800011c48642bf00000000a2a0000423817e35b80000000000b34b2687228000000000094ba41413980007218000c612404ceb1b20176a49e0003170939a6a21fc1354bb6800038707ca000000027b2a90d14af6e4be0a58000000000000000000000902ae08000000000013e80000000000000085da94000000006b4000000000000e0800000000000000000d26800040580001d78000cc92a42ba682186b200005fc0000000000023490289d40000000000017d00003f59c368719d1c9951fda281845c00000000000000000240e79d9edcb770000cf611c65b4b13e00000000000000abd9a148738000659000086c0000299a7380002c1649c00000000a3e00028cc9b5858cd11800008a80006110000bd90f800002ce8000000000006504b109340002cc037f2c4c00028529c9000083d0000775306a4c5920ed55800036f28ea0188cfc0002e6800000000000000c9d00006d42788dda8072203800019025505d6aec200000000000000ae68000cb280005471a880002720d662c0e38c80000000000000000000022cc96500001fda1ca000214c2b7175e61828a012581d245835ee0a200000001ba63932c6a000000000000006cf233c00026269ceadb2a649f5a8ce2d589ec9ee237b0914676035c7da98d63a4233e5f300007dc80007762c260001b1e6050000000376848980000001c9e00000005170c3a0000000003800000000de0000000000000000000000002ea2b5db53400009d400015a600000000000000000000000011d2b22146ec55888200010f400003360000000000121646f000094c04bc71287ae0000000a08aca034aaeea0ad0000000232e00000a8672000082da6a06361bfe9e6b5fc856964a81931b6a29b6660000d1cb330e2ad03201e7b534e4dc6b56443310365139e704ea2ecc0000000daea9262aa8000000169a936362c19b00000000000abb80004ad80008cb19e6000
  | 64 => 0xf00000000000c2983349b7301a6331912088800069f9fe669c80000001cee000016858a259000000000000000000000000026fc0001b9094825b81503710ab380000000000331800000000009e3368cd2e080caaa8af8000000000000000000000000365a15a000000000000000000bb50000c6800005cb000046087806f100f4568ad4400000006c9000027b94e0000000000000005c30cbcb0a85acd1326ca26e111665b03bab040f1648e8000000332a6e18000462878aa4caa9e0002bc00001a36000000000010a4cb8306000037ae0001536b8aad5246d9eba54187c69bd14827e52a5e09b0ed8b7597f400000009d90600de4ae2226ca0ccc923066000000091b000000001620002c00000000000034b200000003a48000515ad4e96a000057c800000018701bc149ad288000000000000000000000000533000026b3150cab80000000000a8c361e063800059720520000000306b38ad5e00003a70000c52ab8c76f19d2df700000d081e0bab9936280177a6a0800052a8088020b68400000000000000000218c8d98a420002fd00001612cff0000a1ca4367368e0e00001d07b68000b7d0000afa10842d8ad880e7963c042ab70b248000779a500b1d067665d8a082870708368aa6671b0000004049a8d80000a199b0e2c0800079f80000000000000000000016b40bba6eeaa180000000000b5400001e835ea000000006789261ea1b6e725113a00000000de9f40cc19786cb6b440724000060c0000000000043e965e891977207baf6c7a7b41404901dacd697b000014ae0002b5c00007b000001ea0000000000000046588aa00009e600001b2ca383dabd58000aa388400000000000000000029a8000367c000106683517e656f845e4ce8fe80f9b644000000000000000001c48c0eb02259a800087e9cb0000308600012aa34db1920000000000000000013d022b92ba000005800000000000000000000000000008e48000140000000014fc1f780000001000b9010d60001f18000000000000000002b12bcd330a6b4942a0000000000000000006221ea8000000124614115443dea4800000b2249a8000000107265c11fc000000099827f80000000db097062f199a8565104e13c8bd06fe0000cef00000002d42000000000013d200000006c60000000351c0000a705ae80000002e4a2b7800000001060000000c2880000000000000199600034fa88e01266962b88000021c00000000002914791158a000308c0000000000000095aa76031d26c055aa5c88e9b1146b32f4c00017a60000000a8b8696a80800000031e6701000000014600000000000000000036540000fecb298000a2c818ad4aac40ad805b24cc1f5847d8000d7e0ec4102800000000000001bf0888a60e9e080000002cce0572baa37080004b71ef6928237014c04f
  | 65 => 0x58e000175600000007001ae00000ff000000000ec800005335020000c3e0000000000291200000b61c4000000008560001b4a0000000000347a21b0000a7e0000000000050091f200000000000000000000021d181c0000000038000084080003e3310a000000046a0ca8ccc000000008266fd80000002eee0000000000159a0000000154a942000243a0000000d31932e00000007b3800000000000000000bf4800000030ba2c50000c03000011c000040f0b4c1251f141860000a3a2be002789c44de80006dda578c6e0000626a51053c14fa0b00000716861c94a9cea51687229d50f007e311ca3779bee9a2800025e07760ab800000000000001d2eda008781838b9c7f715260000000000000000000008c6b6aa000305c000000000036da9e800003b3866800000009240000667ad848430d9a548a5ce67b0000000370c8662d34623800000008c853680000c2000000000000000f3c000000000000000001e327f20c9c00200000000000000031e000000c6a780007248000000011660810aac3000009a580000003120b4100000000000dd40000583000000037c823819ce5d20000000000000000005cf000000006c04842dd400015ead562b4ac54ae4ecc79a50000315a0001800000193862b00003a39d5c9ae2afa000169275e1408000000062480000000000000000087c000000000000000000dcb2164740909acbbb508d9da0d800025d6b5880000001310000230aba9a5fe0000000000000000000000000000000000086eae8c000000062580000002892000000000024d200000005998000000244e00000002be800068f06669d00d8ea4e2b8611c8ba84a98ee602b1e14000000000017d45df00000002bea89f0000000044ca259638cfb000000000002c2083a00000006ce0000a010000000000000000000002c6000037b88790aceb1b80009ee00004491a3096fa2160000faa86d9654789800020ca794a1bb2be3dd8d5c216000021733b6152924cad50bf00000000000230e0002e1eb02800063b0000c0f000089db0b20158000d6080000000000000270492b0000b98800000000000000a6c00000000000000000213200013620001af0dc985c44cfa584dea246e29f1b3498816ae83999e846187d65ef88541c99f56226239c000183254d00000002f26938800050d0d201aa0000749b5f601a998c0000000d3b93d600001660001f68032238a000000000000000001b407c88daaa971012000053800000000000000000309eb4b98268118efa0001e2020d000057a000029da5768139d2c0000000c86aeacb5e0000000000024180000000000be1b31473d8cb80002be67588b380000000000000000033e80000000de72dea7d3956610d2d4681829e80000000197a976000182c273000000015b000000005869aba10
  | 66 => 0xcc1a90a0e80000002e0a23f3790000098cbc280000000000ace83bc1bf000600020965d60e66df790f6c490c80071277c0001f78000252c000328cd9e0000000066000000000000000000203a0000a38000000005d8a3200000009f20d2800009481d8acba0002230000285006694a27088000000057000036bea4a0000bf388dc00000002a50000c18800000016d41c7000000002da4a20000656b47c0000000000000000000005a9b180c931540ada0000a2dace40000ec81a600001ef98ee7bc0032dde8000000000036d00000000000000364677b80000001bc0000307ea751ca80000000a53000089a978c11b0000000000000000003d6980e0c600008b60000507259ac1e340e00012e20000000ca5316c0000000000000000000008048000000137600000000000000000000000026f0000000000019fa0001e064a0800030084f8237800000000000000000510334ca61188c3c880008ff00000002ba000010bc000079c00000003f52378000000000000006682b968f78000bbe14d686500009c3800034328ba22380000000932763811c8bfb76011617383ca90ee0e503240671bfc83680001720deed46b2ac1d233aa52fa4a20003232cc080000000000cd0a4b00000ef00b71300b398a4a1ca82989b900869bc8b660000000000000000000004c31a0e000211a5de30688248000cd1a61c845000000000000001af480700fc000141674c07d800011145ff00007b002c45a0800000000000000c0ad960000cce27aa0002d70a100000000000000000be0001e3e8c8190289609469aa2b7c00000000000000000000000000000000000000311a000000000000002ad00000000000000000000000009a6ab50d2f000000000000002fbe0000000160152c5392922b898918000052e86f021498b33f451c9b14741878445d2604b57358c179aa0ac638000000084600000001f0000093a8000000000091d21206b02cfe00000000000502a6e1b602179a8c80980000000c8c42d90140000000715015a9931e6a00000004512fca74e00008ae80000000000ba700000001296cd00c6c10b166023a8000000000079bb126000321e00021f268a95d059180000000000b4200000000000000001c00000000002bacae49cfcc500000c7e8000b521e781ff80940002e7000036f4c550b423daaadc9a38000ca100000002732d16b0a84d18000759000016b928600000000000000585a22c0000000000024c33baec69ff8376dac03f27e5800000018b677ea0f61248000000000071a9b3e0000da8000176c8218000bdc93920000000c00000000000002a18f1a659b65c000116600035bc44a0958106033a000176200000000000f58d6c07040000000145115462d165065080000002b24c14800000000005810000000000019f000000024fa00000
  | 67 => 0x9920000d77870acc7000064700000000000d66957c00026da000000000000002ff80000003254c90a7ae4c29236a93800054c1f380001754675a98a7df000031f8b923300000000000000003c65199d8000000001658000000000000006e6063000000000005320000000000000000000001ce0000000072912400000000000321800004c60002ad62588becb642b6a91f00000000e947e9822ea3881146ec2c9c9f88b56646827abe4000000000005d9a446000000000007a200000000000210943255a0000000b1d8baabc30000982800000000000000000000219c000000000028c400005ee0000000b9300000000000c9000009e885d83111a1800012d800010de0000000bc400000002f00000000050ea00c0e4000037a800000026de7eb1168b3f292c5569104a329e54aee1f1ebcca772495b3e4149274ea3f8e004cb01ce788abcc1ef000000004fa0000d5a5e283eab9815c414a000054800008db800012f80000000cf800025700003734bce29b2a31a61600000002d38000000000000031e298900005ea0b740122540000143228c000012b1e881ae9cf4942800073500002b90000be700000f0800055880000002f701d011427b9800000000000002dcad9d1ffa0002ac0d0c9ea212bb32c9c229da00028da0e6000000011a6000000093100000000000000136e2ac000000000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8f8865c232440070fd0bbb264880021f617764c9100043fc2aec992200387c855d9324400117f08bb2648801a2f211764c9100046fc1aec99220008ef825d932440011ef02bb2648800e1f216760c9100043fc2aec192200387c855d8324400117f08bb0648801a2f211760c91002c6e41aec19220098ec825d832440010f90cba864880021fe1f650c9100043ec3eca19220018f4865c4324400b9a8c6b88648800a3e219700c91002e6c31ae01922009ce8625c032440b18e8edb2a8288002cd61464505100071bb28c8a0a2000a7486551414400d8e8ecaa2828801b8d19154505100071bc32a8a0a2000b368655141440016690caa282880038d21954505100371bbb2a8a0a2006e3476551414400166f06aa28288003cce0154505103e798402a8a0a207cf3070551414408fc6ec0aa2828811fccd8154505103e799182a8a0a207cf322055141440898e8eca9a8288002cd61743505100055a43286a0a2000b358550d4144001bc441b928288003cc55370505100063a3b6ea90a2000d7070dd521440b18e8edb2a42880063d21974485102363a3b2a890a2000cd476dcd21440019a8ec39a4288003551d47348510004ba43aa690a2044c747654d2144001cceca3124288002f86023248510005724326490a2059c7876d95304408f8f0ecaa26088002d6614634c1100072db28c69822000a788654d304400b8f0eca9a60880179618d534c1100072dc32a69822000b5a8654d30440016b10ca9a608800396219534c11002f2dbb2a69822005e587654d30440016b708a9a6088003d4e05534c110357a840aa6982206af507154d3044089cb6c2a9a6088113d4d85534c110357a920aa6982206af522154d30440016b30b21a6088002b6219434c110005acc2a869822000de221dc93044001ea2a7b8a60880027c21d414c11000798aa2829822000f51535053044001f2286a0a6088003d454d214c1100063c3b6ea9022000d7071dd520440b38f0edb2a40880032e1db74481100065c3b0e89022000d38751d120440012f10eaa2408811f1e1d954481100147c432e69022045c787654d2044001cd6ca3124088002f8606424811000574432849022000f315450520440035e10c90a408800b3c1d9214811004f70312429022001be0874852044005bc10e90a4088006f8a19214811000df0432429022014ee0864852044013dc6ec90a408800b789d92148110016f03b2429022007ee0764852044001ec70a90a408825fd82152148110007b1baa429022097f60754852044001ec6ca90a408825fd81952148110005f1c22429022000be1844852044001f46e890a4088003e81d121481104bfb1aa2429022000f61544852044001f870690a4088003f020d2148110006f1b9a429022000de173485204412fec6a690a4088003d854d2148110
  | 1 => 0xf0fb2886880021f61f6510d1000c7a432e221a2005cd4635c443440051f10cb80868801b2e1917010d100043fc22eb312200087f835d662440070ff0faa4c4880021f61f54989100043fc3aa9312200087d8755262440070ff0fa9cc4880021f61f53989100043fc3aa7312200087d8754e62440070fd0dbaac4881621f21b75589100043f43ecab12200087e87195624400187ecbba2c4880030f19774589100061fb28e8b122000c3c651d162440018becbb9ac4880031719773589100062fb28e6b122000c5c651cd62440070fd0fbaac4880021f61375589100043ec1eeab1220008bf845d5624400d17908baac48800237e0d755891002c6e41aeab12200087e871d5624400187eebba2c4880030f1d774589100061fc2ee8b122000c3c85dd1624400187eea3a2c4880030f1d474589100043f43ea8b12200387c87d51624400187ee9aa2c48801b0f1d354589104262e39ea8b12200087e8755162440010f90eaa2c4880030fdd154589100361e3a2a8b122054c5c7355162440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018bf0bb9ac4880031721773589100062faa6e6b122000c5d54dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd62440010fd0fa9ac48800e1f21f53589100061fba6a6b12208cc3c74d4d62440018bee7a9ac488017171cf53589100043f43aa6b12200087c8754d624400187ee8a9ac4881470f1d153589100062fb9aa6b122005c5c7354d6244001958e9b92c488003331cf72589100066a39ee2b1220018fa87dc16244001970e9b82c48816b1d5c465189104c63cb80ca31220008ef87588624400155908b10c488002b320d62189102ae3ab8ea83122073c7970d50624400d87ce8aa0c4880030f5d154189102863ab8ea63122072c7970d4c624400b8bce6a98c488003175cd531891001c3e42ceda12200087f855db42440070f90abb684880021f21975d09100043fc3ecba12200087d87d9742440031e90cb8e84880021fe15769091001c3e42aed21220018f4865c642440051f10cb84848800e1fa1776509100043ec2eeca12200087f855d942440070f90abb284880022fe1176509100046fc1aeca1220058dc835d942440011df04bb284880023ee01765091001c3e42cec212200087f855d842440070f90abb0848801a2f21176109100046fc1aec21220058dc835d842440131d904bb084880021f21975109100043fc3eca212200087d87d9442440031e90cb88848801b2d191711091004e72312e221220028f8865c0424400d970c8b80848800e1f21676cc9100043fc2aed992200387c855db32440010f90cbae64880021fe1f65cc9100043ec3ecb99220028f8865c332440010ff0abb4648800e1f215768c91000c7a432e31922002
  | 2 => 0xc75d8d100043fc2ae9b1a200387c855d363440010fd0faa6c6880029760f54d8d100043e43aa9b1a2000a5f8355363440010ff0ab96c68800e1f21572d8d100043f43ecab1a200087e87195634400187ecbba2c6880030f1977458d100061fb28e8b1a2000c3c651d163440018decbb92c6880031b1977258d1000637b28e4b1a2000c6c651c963440070fd0fbaac6880021f6137558d100045fc22eab1a20068bc845d563440011df04baac6880263b2097558d100043f438eab1a2000c3f75dd16344001878ebba2c6880030fe177458d100061e42ee8b1a2000c3f751d16344001878ea3a2c6880021fa1f5458d1001c3e43ea8b1a2000c3f74d51634400d878e9aa2c6880021fa1d5458d100043e43aa8b1a2000c3f74551634400d878e8aa2c688003271d37358d100061fba6a6b1a208cc3c74d4d63440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc963440018dea9b92c6880031b5537258d1000637a9ee4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440018dea8392c6880031b5507258d1000637a98e4b1a2000ce472dc563440090fb0fb28c6880029760f6518d100052ec18ca31a2098c797019463440011bf0eb18c688002a72116318d1000566412c631a200087e869d953440014bb073b2a6880021f6127654d100043ec1ceca9a2000c5d839d953440018ed033b2a6880031d6067654d100062f984eca9a2000c5d309d9534400147f08bb2a6881468f2117654d100052fc1aeca9a2000a6f825d953440014d904bb2a6880021f6107654d100062f980eca9a2000c7a301d953440018ba603b2a6880021fa1b7454d1028e1e326e8a9a200087c87d91534400187ee9b22a6880021fe1d6454d100043e43ac8a9a2000a5f83591534400b4b906b22a6880029be096454d1000536412c8a9a200387c87d8d53440010ff0eb1aa68800e1f21d6354d100051fc22c6a9a2051a3c8458d53440014df04b1aa6880029b2096354d102253b436e2a9a2000c7676dc553440070f90b3b686880021fe1576d0d1001c3e42aeda1a200087c865d743440010ff0fb2e86880021f61f65d0d1000c7a432e3a1a200387c859da43440010ff0abb4868800e1f2157690d100043e432eb21a200087f87d9643440010fb0fb2c868800a3e2197090d1001c3f42eeca1a200087d85dd943440070f90b3b286880021fe157650d1001c3e42aeca1a20008bf845d943440011bf06bb286880023be097650d1004c76412eca1a200387e851d943440010fb0a3b286880021f2197550d100043fc3ecaa1a200087d87d9543440070f90b3b086880021fe157610d1001c3e42aec21a20068bc845d8434400b1b906bb086880023be097610d1004c76412ec21a200087c865d443440010f
  | 3 => 0x90a4074c6c76dd52148001ad0e1baa42901831b1db65485200073230eca90a40018ec865d121480033d100ba242900cf2b1db64485200075230ec890a402ccac761912148001c58ca32242900029b2195448520236363b2a890a4028ccc76dcd2148001b90e1b9a4290087331d87348520006a63a8e690a40028ec8758d21480055c902b1a42900025b21d5348520226363b2a690a4060c7a76d9720480c1cd6c5b2e40900cf2e9db64c81200365d3b0c99024000e386519320480014f10caa6409001b1e9d954c812002e3d3b2a790240359eb8750b2048013bc642b8e40901629ea0374d95102cd3cc06e9b2a200087f835d3654400187ae83a6ca881669da0474d95102c53ac08e9b2a2059a7681dcf65440b14eb03b9eca880021fe1173d95100062eb98e7b2a2058a7a801cf65440b34f30039eca880031b5c872d95102cd3b408e5b2a2058a75811cb65440b14f500396ca881669e60072d95100147cc06ebb222000a3d84dd7644400147b083aec8880021fe1573d911001c3e42ae7b22200087e87d4f644400147b09a9ec8880021fe1572d911001c3e42ae5b22200087e87d9564440010fd0e32ac88800317d9773591100062e32ee6b222000c5f651cd64440018b8ca39ac8880031bd9772591100063632ee4b222000c6f651c964440018d8ca392c88800e1fa1f75591100043ec1eeab2220008df835d5644400b1b906baac8880023be09755911004c76412eab22200087e871d564441098b8e7aa2c88800317dd773591100062e3aee6b222000c5f85dcd64440018b90bb9ac88800317d5373591100062fba8e6b222000c5c751cd644400193ee839ac8880021fa1f535911001c3e43ea6b222000c5f73d4d644400b8b8e7a9ac8880031bdd77259110006363aee4b222000ccf73dc96444001998e7b92c8880031bd53725911000637a9ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c964440018dea8392c8880031bd4c725911000674396e0b22200487d87d94644400147b09b28c8880028f61065191102d63ab88ca32220008bf87590644400153906b20c888002ab20964191100043f434ecaa22000a3d849d954440010fb093b2a8880030f61276551100043ec1cecaa22000c3f419d9544400187a833b2a8880031ea0276551100063cc04ecaa22000a3f845d954440014bf06bb2a8881529720d765511000537c12ecaa22000a6c825d954440010fb063b2a8880030fd0476551100063b208ecaa22000c3d411d954440070f90fb22a8880021fe1d645511001c3e43ac8aa22000a5f8359154440a94b906b22a8880029be09645511000536412c8aa2200087e86dcd54440a98b8c7b9aa88811e9ea1b70551100063d3b6e0aa220018f581dd763440014bb07baec6880029760
  | 4 => 0x2480018f0cbb8284901831b1db6550920306b4386caa124089aae86dd1424800d958edba284900cf6a1c3745092003557436c8a124033cac76d914248067b50e1b22849001b2b1d8645092000717b28c8a124000e2c651914248059b50e032284900029b2195450920036363b2a8a124006e2c64551424808dad0e0aa284901131b1d9535092028f16322a6a124044d687054d42480033d101b8a84900067aa1f70509201743e432ea2124006c3c645d44248013ad040ba884900021fe1f65109200443ec3eca2124000c3e75d90424800187aebb2084901861f21975cc9203043fc3ecb992400087d87d97324800187cebb2664900030f5d764cc9200061f3a8c99924000c3d751933248059974e032664900032e19170cc9201143e432ea192400087f87d9432480110fb0fb2864900030f9d7640c9200061ebaec81924000c3e75190324800187aea320649000e1fa1b75585200043f43ecab0a400087e87195614800187ecbba2c2900030f19774585200061fb28e8b0a4000c3c651d1614800117d0fb22c2900030fdd764585200061e3aec8b0a40008be87191614800187eea322c2900030f1d464585204d657b90c8b0a4000c5f65dcd61480018b8cbb9ac29000327d9373585200064e326e6b0a4000c5f651cd61480018b8ca39ac29000327d9073585200064e320e6b0a4000cd4611cd61480070f90b3b682900021fe1576d052001c3e42aeda0a40028bc845db41480010f90cbae829001b0f19175d05200043fc3ecba0a400087d87d97414800187cebb2682900030f5d764d05200051f432a9a0a4000a3c86553414800187cecaa6829001b0f1d954d052003656324e5a0a40018ec865cb414800d958c8b9682900067a20172d052001c3f42eeca0a400087d85dd9414800517d0fb2282900028fa1954505200051e432a8a0a4000c3e765514148001878ecaa2829000e1f21676cc5200043fc2aed98a400387c855db314800117f08bb6629001a2f21176cc5200043e432eb98a400087f87d9731480010fb0fb2e62900030f9d764cc5200061ebaec998a4000c3e75193314800187aea326629000e1fa17764c5200043ec2eec98a40068be84dd9314800117b09bb262900023ba1b74c852000cf4402e990a4099cae761932148001c58ca32642900029b21954c852000477c3ac790a4002ae48158f21480c30fd0dbaa42900035a08375485203ac3f43eca90a406087c87d952148001cc843b2a42900030fdd764485200061e3aec890a4000ea421d91214800187eea32242900030f1d464485201665c380c890a4000c5f65dcd21480018b8cbb9a429000327d9373485200064e326e690a4000dc820dcd21480018beca39a42900031719473485200064fb20e690a4000c9c641cd21480439a8c239a4290003351cf61485200065c326e
  | 5 => 0x221f61f6518d200052ec1eca31a4000a5d83194634800187cebb20c6900030f5d76418d200061f3a8c831a4000c3d7519063480011bf0eb18c690002b52056318d2028d1f426eca9a4000a3d84dd953480010fd0d3b2a6900029760e7654d200043ec24eca9a400087d839d953480018bb073b2a6900031b60a7654d200062f984eca9a4000c5d309d9534800147f08bb2a6901468f2117654d200052fc1aeca9a4000a77815d9534808b4e902bb2a6900021f6107654d200062f980eca9a4000c5d301d953480010fd0dba2a6901470f1937454d200043e43ec8a9a4000c3f74d91534800b4bd07b22a6900029760f6454d2028d1f436c8a9a4000c3e76d915348001878edb22a6900030fe1f6454d200061e43ec8a9a4000e1e83d915348001c3b07b22a6902770fdcf6454d200070fb9ec8a9a409ce1f30d915348139c3a61b22a6900021fe1d6454d200043e43ac8a9a408fa3e86191534800187cec322a6900030f1d86454d2028e1f438c8a9a4051c3d87191534811987ee6322a69000387dcc6454d2028f16c10c8a9a409be1f301915348137c3a60322a69000e1f21f6354d200043fc3ac6a9a400387c8758d534800147f08b1aa6901468f2116354d200053bc0ac6a9a4045a748158d53480894dd0db92a6900031b9db7254d2000716326e4a9a4044b6a80dc953480018dcec392a6900038b1907254d2001c3e42ceda1a400087f855db43480070f90abb686900162f21176d0d200043e432eba1a4006c3c645d743480010ff0fb2e86900021f61f65d0d200061f3aec9a1a4000c3d75d93434800d958c939686900063b21972d0d2003656322e5a1a40019e8805cb43480070f90b3b486900021fe157690d2001c3e42aed21a400087c865d643480a3878c8bac86900021fe1f6590d200043ec3ecb21a4000c3e75d92434800187aebb24869000e1fa177650d200043ec2eeca1a400387c859d943480010ff0abb2869000e1f2157650d200045fc22eca1a40008f7815d943480051e902bb2869000e1fa147650d200043ec28eca1a400087c865d543480a3878c8baa86900021fe1f6550d200043ec3ecaa1a40058be87d91434800187cebb2286900030f5d76450d2001c3e42cec21a400087f855d843480070f90abb0869001a2f2117610d200043e432ea21a4006c3c645d443480010ff0fb2886900021f61f6510d200061f3aec821a4000c3d75d90434800d958c939086900063b2197210d2003656322e421a40098f8865c0434800d970c8b8086901861f21975d09200361e322eba124000d68205d742480c10ff0fb2e84900021f61f65d09200061f3aec9a124000c3d75d93424800d970c8b86849001aab212769092000717b28c92124000e2c6519242480014d90caa4849001b8b191549092028f16322a72124033cb870d914
  | 6 => 0x6717396a6322408ce2d72d4c6448001c3ea7298c890002abe09531912000556412a63224000e2f52948644800157700a90c8900b2ae201521912000557414a23224000aad82944644805957501288c890002ae60251191200345f438a232240008bd87144644800d17d0e188c8900022f61c31191200051f428623224000a3d850c4644800155d04188c890002ab60831191201655d400623224000ab9800c4644805957500108c8900021fa1a76551200051ec24ecaa24000c3f749d954480010fb093b2a8900030f61276551200043ec1cecaa24000a3f845d954480014df04bb2a8900029ee0176551200061fba0ecaa24000c3f841d954480010fb063b2a8900031b880765512000636100ecaa24000c78201d954480018f4203b2a89000e1f21f64551204fe1fba6c8aa24006a3e86d915448001878edb22a8900030fe1f645512001d1f43ec8aa24003a3c87d9154480018790fb22a8900028f60764551200043fc3ac8aa2400387c87591544812147d0c322a8900030f9d864551200061e3b0c8aa2400087e86dcd544800187ec9b9aa8902330f19373551200061e3aec9b1a4000c3c7519363480031db05baec6900029760f75d8d200052ec18ebb1a400087f855d363480070f90aba6c6900021fa1f54d8d200043e43aa9b1a400087f855c763480070f90ab8ec690002b360831d8d200056cc0063b1a4000c3f659d26348001878cb3a4c6900030fd957498d200061e32ae931a4000c3e75d92634800187aebb24c6900030f9d46498d200061eba8c931a409ecad7219263480010fd0fb2ac6900031d1c76558d200043f438cab1a4000c7471195634800187ecbba2c6900030f1977458d200061fb28e8b1a4000c3c651d1634800117d0fb22c6900030fdd76458d200061e3aec8b1a4000cb471d91634800117d0e322c6900030fdd46458d200061e3a8c8b1a4000cb47119163480018eecbb8ac6900031d1977158d200065bb26e2b1a4000cb464dc563480070fd0fbaac6900021f6137558d200045fc22eab1a40068bc845d563480011ef02baac69000a3d2057558d200043f438eab1a4000c3f75dd16348001878ebba2c6900030fe177458d200061e42ee8b1a4000c3f751d16348001878ea3a2c6900021fa1f5458d2001c3e43ea8b1a4000c3f74d51634800d878e9aa2c6900029760f5458d2039e3a38ea8b1a400087e8755163480010f90eaa2c6900030fdd15458d200361e3a2a8b1a4047c7471551634800187ee9a9ac6902330f1d35358d203963a38ea6b1a40028f687dc563480018eeebb8ac6900031d1d77158d200065bba6e2b1a4000cb474dc563480018eea9b8ac6900031d5537158d200063ba9ee2b1a4000c77751c563480018e8ea38ac6900032ddd07158d200065a3a0e2b1a4000cd7731c563480019cee438ac69
  | 7 => 0x7f835d3654800187ae83a6ca902aa9ba0874d952030536c10e9b2a40a9a6e82dcf65480c14db05b9eca900021fe1173d95200062eb98e7b2a4000a3e849c7654800147b0938eca902a29ba0871d952030536c10e3b2a4060a7a801c765480014f30038eca900021fa1c41d95200043ec3883b2a400087e870c765480010fb0e18eca900028fa1031d95200051ec2063b2a4000a6e820c765480014db0418eca901829ea0031d95200053cc0063b2a4060a7a80087654800d87cedaa6c8900028f61375d91200051ec20ebb224000a5d831d7644800187aebaa6c8900030f61f54d91200051ec1ea9b224003c3c75953644800717f0eaa6c8900021fe1573d912001c3e42ae7b22400087e87d4f644800147b09a9ec8900021fe1571d912001c3e42ae3b224000a3e85107644800147b0a20ec8900028fa1875d91200058ec18ebb224000a3d83d97644800147b0632ec8900028fa1b53d91200051f42cc3b224000a3d85987644800147b07baec8900030f5d475d91200054f418ebb224000a9d831d7644800187d0e3aec89000387a0c75d91200051ec18ebb224000e1d831d7644800143b063aec8900028fa1673d91200051ec2ce7b224000a3f855cf64480014790ab9ec8900028fa1473d91200051ec28e7b224000a3e87d4f64480014790fa9ec89000387d4e53d912000717a94a5b224000c3f75dc7644800147d0b38ec8900028f61671d91200051fc2ae3b224000a3c855c7644800187eeab8ec890002aba0871d912019d56c10e3b224033aba801c764480015730038ec8900022fa1c51d91200045ec38a3b2240008be870c7644800117b0e18ec8900028fa1431d91200051ec2863b224000aae820c7644800155b0418ec8900ceaea0031d91200055cc0063b224033aba80087644800d878c8bacc8900030f9d764991200061ebaec9322400087e87d9564480010fd0e32ac89029f1bdc8655912001c3f43eeab22400087d83dd5644800117f08baac8900023be0975591200047dc02eab22400087e871d5644800187eebba2c8900030f1d774591200043f43ea6b22400387c87d4d64480018d8ebb92c8900031e1d770591200361e322ea322400887d87d94644800147b09b28c8900028f610651912030e36b90ca32240008bf87590644800147f0ab20c8900028f21564191200061f3b4ea3224000c3e765d4644814d87cedb28c8900028f61f65191200051ec1eca32240a5e2d72d94644800117b0f328c8902928fa1665191200045fc3aca32240a3aaf82594644814547d0c328c8902870f9d865191200051fc38ca3224000a3d831946448141c5ae4328c8902838b880651912050716100ca32240a0e38201946448141c7420328c8900028fa1b53191200051f42cc23224000a3d85984644811947f0fa98c8902328f61f53191204
  | 8 => 0xa7b828698147171d97550d300058fc22eaa1a6000d58705d5434c0018bf0cbaa8698003172197550d3034cafc22eaa1a6000d1f845d5434c001a9f04baa8698003532097550d30006abc0aeaa1a6000d54815d5434c001ab700baa8698003562017550d302a62fb02eaa1a6054d5b605d5434c001ab420baa8698003475d76450d300068eba8c8a1a606795d87551434c00d8b8ecaa2869801b871915450d30006acbaee0a1a6000a5d83d53624c0015d30010ec4980039354f629893006cae43aa6b126000d1f7454d624c001a38e8a9ac4981ab551c55358930006aaa9ee2b1260008ef87588624c001c9aa6b10c498002b920562189300043fc2ae2312600387c855c4624c0031b90cb9e849800257e1d53d0930004aec3aa7a12600087f855da424c0070f90abb48498003179d953909300062ebb2a72126044d587054d424c001ab2a7b82849801b0f19175109300061ebaec821260018dc865cc424c00d938c8b98849800257e1d5310930004aec3aa62126044d5a7054c424c001ab2a6b808498113179d9538c930226ad382a71926000e4d53d8a324c001ab2a6b846498113171d9534c930226ac382a69926000e4d53189324c001ab2a7b8264981ab9598553d85302262eb9aa7b0a606ae563154f614c01b2b90ea9ac29800347dd153585300068e3a2a6b0a606ae546154d614c001a9aa7b92c2980035354c725853000672308e4b0a6000c3e76553414c00d878ecaa682980063721973d0530004afc3aa7a0a600095d8754f414c00163b0aa1e82980030f9d954505300061e3b2a8a0a6000c5f7654d414c0018b8eca9a8298003271d943505300058ec2a86a0a6044c5c7654d314c08bca8c2a9a6298113561c1534c530006aca9ee098a60028ee829db214c0070fd0b3b242980021f616764853002c6e418ec90a60018de86dcd214c0012bd0ea9a42980025721d53485300062fbb2a690a6000c5c7654d214c00147b09a9ac99000e1fa1771593200043ec2ee2b264000a3d849d954c80014dd053b2a9900028fe1176553200063cbb6e0aa64006c3e7455363c800187ae8aa6c7900063b2097558f200047bc0aeab1e40028f4815d563c80014bb07aa2c79000e1fa177158f200043ec2ee2b1e4000a5d839d953c80014bf06bb2a7900029de057654f2022d3a40aeca9e4005a5e83d9153c80014bb07b22a7901129b6187254f2002c7dc32e121e400387e85dd943c80010fb0bbb2879001b1b5d95490b2003717322a92164044c6d7654e42c800dc58c8aa2859000317dcd535872002e2e39aa6b0e40018ee82dd941c808d8daecaa643901131b5d953c872000477c32e890e40019e8805d121c815799eec39a4390003531d473487200047743ec690e4002ae48158d21c80012d90ea9a43900028fa1261d95200051ec24c3b2a40008
  | 9 => 0x6510b30004afc3aa6216600095d8754c42cc0070fd0abb683980021fe1975d07300043fc3acba0e600087d8759741cc00147f0caa683980028f61954d0730004afc3aa7a0e600095d8754f41cc00163b0aa1e839800a2f21d64507300051fc32a8a0e6000a3d8655141cc0018beeca9a8398017171d953507300058ec2a86a0e600387c85dd921cc0010ff0abb2439800e1f21576487301446fc1aec90e60018dc835d921cc0010fb0dbaa43980021fa1d65487300043e43aca90e6005c5c7359521cc0018bccbb9a4398003175977348730004af43aa690e600095c8754d21cc0018beeca9a4398017171d9534873002e6639cc490e60028ec8758921cc00b998e6b12439800ab920562487300052ec1ea9b2260038bf87553644c00147b09a9ec8980021fe1572d913001c3e42ae5b22600087f855c7644c0070f90ab8ec8980028f61441d91300361e322eb3226000c3d75d92644c0011df04baac8980263b20975591300047bc0aeab2260028f4815d5644c0011f700baac8980029760f54591300045fc3ac83226000a3d849d9544c00147f08bb2a8980029be09765513000536412ecaa26000a77815d9544c08f4e902bb2a8980029ee0176551300351f436c8aa26003a3e87d91544c0074790fb22a8980028f607645513048d1f430c8aa26000c3f64dcd544c119878c9b9aa89819ec761273551302352e432e6aa26069b1f845cd544c00b6b507b82a698103171db7454d304262fb06e8a9a6084d5b60dd1534c001ab421ba2a69811297a1a7454d300052ec34e8a9a6044b5a809d1534c0016b3013a2a69800297e197454d302252e432e8a9a603dc5c765d1534c00169f04ba2a698002d32097454d30005abc0ae8a9a606ab54815d1534c0016b700ba2a698112d62017454d3006caf43cc8a9a600095d87991534c001c3ec9322a6981a657a1c6454d30224aec38c8a9a6000e1d64191534c0894bd0d392a6980029761a7254d3011e2e3b4e4a9a6044b5a809c9534c0016b301392a69800297e197254d302252e432e4a9a6000b57815c9534c0d56a902b92a698002d6e017254d30225ac402e4a9a6022c5c761c9534c0896b101b8aa69800297e197154d302252e432e2a9a6000b4f825c5534c00169904b8aa698002d6e017154d30225ac402e2a9a6044b5a87dc1534c089ab50fb82a698016d6a1b7054d3002dac436e0a9a6044d5a76dc1534c089ab0edb82a69800356dd37054d30006acba6e0a9a6000b5981dc1534c00d878c8bae86980030f5d764d0d3006cafc3aa7a1a6044c5e7654f434c001c3ec8a9e8698113569c153d0d30006aca9ae1a1a6005c5f605d6434c00bab6c0bac8698003568417590d300370e322a921a6051c3c645d5434c00187aebb228698113171d95350d3028f0e322a6a1a6044d587054d434c001ab2
  | 10 => 0x90e8000c5d65dcd21d00018bcca39a43a00031759473487404669c206e6aa28006b3a84dc154500010ff0ab96c6a000e1f21572d8d400043fc2ae3b1a800387c855c7635000153b0818ec6a0002b660031d8d400046fc3ac631a8000a5d839d953500014bf06bb2a6a00029be097654d4000536412eca9a8000a77815d9535008b4e902bb2a6a00029ee017654d4028e9c202eaa1a8000c6d75d4b62500015d30010ec4a00023be1d62189400053642ac431280adaaf8458862500131d904ba8c4a00021fe15711894001c3e42ae231280008df835c4625000b1b906b88c4a002739085711894004e74312e12128046c3c76551425008da70e0aa284a00038b55062509400043fc2aed192800387c855da32500031790cba064a001b0f1d154d85402361e3b2a8a0a8047e3461551415008da70e0aa282a00038d553615054001c3f42cec90a800087d859d9215000b1bd073b242a00023760e764854001c3fc1ee8b2e600387d83dd165cc00187ee93a2cb9801697a0e74597303652ec1ce8b2e6000a7b805d165cc0894f100ba2cb980031bdca72597300051f420e2b2e6000a3d841c565cc0010fd0e20acb980021f61c41597302253d40042b2e6000a798008565cc0a947b093aac9982128fe1175593300052ec1ea8b26600387e85dc964cc0010fb0bb92c99800e1fa1771593300043ec2ee2b266046a5e83dd954cc0a98bce7bb2a99800e1f61376553302a62f41eecaa66054c5e43dd954cc00147f08bb2a9982121fe1176553300061fc22ecaa6605487f835d954cc0a90fb06bb2a9980031ee0176553300063c402ecaa6600387e8759154cc0a90fb0eb22a99800317dd973553305658fc22e6aa66046b58805cd54cc001ab0e0b9aa9980031e5db7055330006acb9ee0aa6608495f86dd153cc1092bb0dba2a798213479937454f304268eb26e8a9e6000a5d869d153cc0014bf0cba2a798002d3e097454f30005a6412e8a9e6000b57815d153cc0db6a902ba2a798002d6e017454f30225ac402e8a9e6000a5d869c953cc0014bf0cb92a798002d5e057254f3036daa40ae4a9e6000a5f865c553cc00169f04b8aa798002d32097154f300052fc32eaa1e6084b1f845d543cc0a92bf0cbaa879800317e197550f300068fc22eaa1e6000d4f825d543cc001a9904baa879800355e057550f30006aa40aeaa1e6000d5b805d543cc001ab100baa879800297e195450f3004c76412e93166006c3e7455262cc00187ae8aa4c5980021fe157198b3001c3e42ae33166000a5d83d5162cc0070fd0abb685980021fe1975d0b300043fc3acba16600087d8759742cc0012bf0ea9e85980025761d53d0b3002c77c3ac5a166005cce7358b42cc00b8bceca9c8598003175d95390b3001c3f42aec216600087f865d442cc0010ff0eb2885980021f61d
  | 11 => 0x4850359d0db9a6490817331db734c921146e238ee69924205ace86d8d3248451998edb1a64908a3711c7634c92102e663b0c69924200e4f6518d3248401c98ca31a6490887711c4634c92100536432a69924205c6c7654d324840bc98c6a9a6490917591c5534c921014f343ee299242029e481dc132484450f90cba864908171718d750c92104eb210aea192420087f87d94324842b0fb0fb286490803179d7630c9210062ebaec61924274e6762d972148401ca8ca31e42908029d21953c8521154f3c3a6590a4209de3205c321484070fd0dbaac0909d21f21b75581210043f43ecab02420087e87195604840187ecbba2c0908030f19774581210061fb28e8b024200c3c651d16048401970c03a2c09080317d9773581210062e32ee6b024200c5f651cd60484018b8ca39ac09080237a1f63581210062fbaec6b024200c5c75d8d604840193ee9b1ac090803271d363581210046f438c6b024200c5f7518d60484018b8ea31ac09080327dd063581210064e3a0c6b0242aeccf7218d60484070fb09b9acba02331790f73597404662ea1ee6b2e8000c5f739cd65d00014df04b9acba00029b20973597400053bc0ae6b2e8000a74815cd65d00014f700b9acba011a9e201735974000637b94e4b2e8000a7b805c965d008d4f100b92cba00029ba0a715974000536c14e2b2e8046a7a809c565d00014f30138acba001a8fa10715974009d1ec20e2b2e800087e870c565d00010fb0e18acba001a8fa1031597400051ec2062b2e8000a6e820c565d00014db0418acba011a9ea0031597400053cc0062b2e8046a7a8008565d00014f30010acba01469760e7558f4000477c12eab1e80098ec825d563d00011ef02baac7a000a3d2057558f404652fc1aeab1e800387e85dc963d00010fb0bb92c7a000e1fa177158f400043ec2ee2b1e800387d83dd953d00018be61bb2a7a0003174c37654f400052fc1aeca9e8000a6f825d953d00014d904bb2a7a00029de057654f4022d3a40aeca9e808487f845d953d01190ff06bb2a7a000317e0d7654f4000637c12eca9e8000c6c825d953d00018ef02bb2a7a00031d2057654f400063dc02eca9e8000c78805d953d00018be60bb2a7a000e1fa1d6354f4028c3ec3ac6a9e8000c7976dc153d000b8bce6a9cc5a0003175cd5398b400043fc2ae3316800387c855c662d00070fd0abb665a00021fe1975ccb400043fc3acb996800087d8759732d00070fd0abb065a00021fe19750cb400043fc3aca196800087d8759432d00018bee6a9ac3a0017171cd535874001c3f42aed98e800087f865d731d00010ff0eb2e63a00021f61d65cc74001c3e42eec90e800087f855d921d00070f90abb243a000237e0d764874002c6e41aec90e800087d86dd521d00010fd0eb2a43a00021f21d65487400062f32ee6
  | 12 => 0x8023761c4018d210052f4288031a4200a5d85100634840159d04200c690802b36084018d2110d6b4088031a4200ad58110063484435ad02100c6908021fa1a7654d210052ec1ceca9a4200c5f739d953484010fb093b2a6908021f60e7654d210062ec1ceca9a4200a5f835d953484014df04bb2a6908029de057654d210062fb98eca9a420087d841d953484018bf063b2a6908031b8847654d2100636108eca9a4200c74211d953484018ee203b2a6908021fa1b7454d214262e31ee8a9a420087c87d9153484010ff0eb22a6908021f21d6454d210052fc1ac8a9a4205a5c8359153484014f700b22a6909129e2016454d2101c3e43ec6a9a42afc5f73d8d534840b4bd0db1aa690803171db6354d210062fc3ec6a9a4203a5e87d8d53484074b90fb1aa6908031721f6354d210062fba6c6a9a4200a5d80d8d53484010ff0eb1aa69080e1f21d6354d2143d2f430c6a9a4200c5e7618d53484018b8ec31aa69080e1f21676d0d210043fc2aeda1a420387c855db43484010f90cbae86909531718d75d0d210043fc3ecba1a420087d87d9743484018bcebb1e8690803175d763d0d2101c3e42ced21a420087f855da43484070f90abb486908163720d7690d210043e432eb21a4205c5c635d643484010ff0fb2c86908021f61f6590d210062f3aec721a4200c5d75d8e434840b998c7394869080a3b2197290d2102e6631ae521a42029e4815ca43484070fd0bbb286908021f6177650d2101c3e42ceca1a420087f855d943484070f90abb2869080237e0d7650d210047dc02eca1a42018f8805d943484070fd0a3b286908021f6147650d210043e432eaa1a4254c5c635d543484010ff0fb2a86908021f61f6550d210346f43ec6a1a4200c5e75d8d43484018baebb1a869080e1f2167610d210043fc2aec21a420387c855d8434840b1b906bb086908021f2197510d2102e2e31aea21a420087f87d9443484010fb0fb288690803179d76310d210062ebaec621a4205ccc639c843484051d90cb9086908173318d7210d2104c7a432e221a4205cd4635c443484eb0f90cbae84909d21fe1f65d09210043ec3ecba124200c5e75d8f42484018baebb1e8490803179d463d09210062eba8c7a124221cd67118f42484019a8c6b8e84908ba1f21975109210043fc3eca212421587d87d9442484018bcebb188490803175d763109210062f3a8c62124200c5d7518c42484eb0f90cbae64908171718d75cc921006b210aeb992427487f87d9732484010fb0fb2e6490803179d763cc9210062ebaec79924205acc839da32484a9c98c6aa4649080393d94638c92100726328c71924200a6c8654e324840bc98c6a9c64908a3351c7634c9210063a32ee29924274c6c76d9532484e9ac8e3b2a649091f1b1d9544c9212a72631aa89924247d647155132
  | 13 => 0x62eba8ebb1a4200a9e841d7634840153b083aec69080317a1c75d8d210070f420ebb1a4200a5d841d76348401c3b083aec6908028761075d8d210052f42ce9b1a4200a5d859d363484014bf0aba6c6908029721574d8d210052f428e9b1a4200a5d851d363484014bd0faa6c6908029721f54d8d210070faa4a9b1a4200a5e8755363484014b90eaa6c69080387e1154d8d210070f3a2a9b1a4200e1d745536348511c3e82aa6c690a238750554d8d2100727a94a5b1a4200c5f75dc363484014bd0b386c6908029761670d8d210052fc2ae1b1a4200a5c855c363484018beeab86c690802b3a0870d8d2114566c10e1b1a4228ad6811c363484015ab02386c69080237a1c50d8d210046ec38a1b1a42008de8710363484011bb0e206c69080297a1440d8d210052ec2881b1a4200ace82103634840159b04206c6908a2b5a0440d8d210056ac0881b1a4228ad681083634840b8b8c6bacc690803179d76398d210062ebaec731a420087e87d9563484010fd0e32ac690ae71bdc86558d2101c3f43eeab1a420087d84dd563484011bf06baac6908023be097558d210047bc0aeab1a420087e871d563484010fd0faa2c69080e1f21f5458d210043f43aa8b1a420087c8755163484018beebb9ac690803171d77358d21006363aee4b1a4200c7475dc5634840b8b8c6ba8c6908561f61f6518d210052ec1eca31a4200a5d8319463484eb8dae4328c69080237e1d6318d210052fc2ac631a4200a5c8558c63484018bced3a8c690803179d97518d215c62f3b6ca31a4200a5d87d9463484014bb09b28c690adf935cb6518d210046ec3cca31a42b6a5e8599463484011bf0eb28c690ad6b3e096518d215a52f430ca31a42b3c5e7619463484014bf0e328c690802976106518d2159726b90ca31a42b2e4e211946348565c9842328c690acb950846518d215972b880ca31a42008dd8799063484014bd0b320c690802976166418d2158d66c14c831a42008df8759063484014bf0ab20c690802972156418d210056dc02c831a4200ad88059063484014bd0a320c690802976146418d210052f436a831a4200a5c86d5063485618bcedaa0c69080297a195418d210052e432a831a4288c5e7655063484014bd0b300c690802976166018d214252fc3ea831a4284a5d87d506348509c9ce5aa0c690a13935cb5418d212a52ec2ca831a4200e1f54950634840159f04aa0c690802b32095418d212a52fc3aa831a4254a5d875506348401c3f08aa0c69080393e095418d2100726412a831a4254e4d725506348507c3e82aa0c690a0f875055418d214252f428a831a4200e4f5294863484015af02a90c690886b52055218d2100567414a031a4200acd8294063484435ad03280c690802b56065018d2102c6f438a031a42008dd87140634840b1bd0e200c690
  | 14 => 0x58110365484010fd0e186ca908021f61c30d95213a53b40841b2a42028ed82dd7644840147b09baec8908028f61075d91210043fc2ae7b22420387c855cf64484010fd0fa9ec8908021fe1570d912101c3e42ae1b224200aad82103644840156b02206c89080317d9673991210062e32ce73224200c5f655ce64484018b8cab9cc8908021fa1f65591210063c386cab22420087e8719564484018f0e032ac89080317d9773591210062e32ee6b224200c5f651cd64484018b8ca39ac8908031ed9770591210063c32ee0b22420387e87dd564484010fb07baac89080237e0d755912102c6e41aeab2242008fb805d564484031f100baac8908021fa1c75591214262e39ea8b224255c7870d5164484018beebb9ac890803171d773591210062fc2ee6b224200c5c85dcd64484018bea9b9ac89080317dd473591210062e3a8e6b22420087e87d4d64484070f90fa9ac8908028f61353591210062fb9ea6b224205c5c73d4d64484a18f0e1a9ac8908063ea1f70591210063dbaee0b224200c7875dc164484019b6e7b82c890803361cf70591210063daa6e0b224200c7b53dc164484018f6ea382c8908031e1d470591210065dba0e0b224200cdb731c164484019b0e6382c8908033adc870591210ac3ec3eca3224200a3d84d94644840147b08328c8908022fe1d64191210055c402c83224254a5e83dd954484014bb07bb2a8908021fa1a76551210051ec24ecaa2420087d849d9544840187b093b2a8908021f60e765512100636c14ecaa24200c3f419d9544840187a833b2a8908028fe1176551210052fc1aecaa24254a5c835d954484014f700bb2a89091a9e20176551210043ec18ecaa24200c3f411d9544840187a823b2a89080e1f21f64551210043fc3ac8aa2420387c8759154484014bf06b22a8909529720d64551210053dc02c8aa24246a788059154484010fd0db9aa8909531718f735512123d37436e4aa24200c6e76dc9544848f6cd03b92a8908031b9d8725512102e2f3b6a7b1a4200a5d83dd7634840147b083aec6908029760c75d8d210043fc2ae9b1a420387c855d363484010fd0faa6c6908029760f54d8d210043e43aa9b1a4206c3e74553634840187ae8aa6c69080297e0d54d8d210062ebaea7b1a4200c5d87d4f63484014bb09a9ec69080f171d653d8d2101c6fc3aa7b1a420087f855c363484070f90ab86c69080297a1430d8d210052ec2861b1a4200a5e861d7634840163b083aec6908029761365d8d210052ec20cbb1a4200a5e8599363484014bb0b326c69080297e1564d8d210052e42ac9b1a4200adb8059363484015b100b26c69080297a1464d8d210052ec28c9b1a4200a5e86d5363484014b90daa6c69080297a1954d8d210052e432a9b1a4200a5e8598363484014bb0b306c6908029761375d8d2100
  | 15 => 0x4baac9988263b20975593310047dc02eab2662018f8805d564cc50947f08baac99880e1fa1772593310043ec2ee4b26620387e85dc164cc4010fb0bb82c99880e1f61376553310061fa0eecaa66200c3d41dd954cc40147f08bb2a9988029be09765533100536412ecaa66200a7b805d954cc48d4f100bb2a998a121fe1176553310061fc22ecaa66200c6f825d954cc4018d904bb2a9988031de0576553310063a40aecaa66200c3f415d954cc40187a82bb2a9988031ee0176553310063c402ecaa6620387e8759154cc4a90fb0eb22a9988031d5db71553310361f3a2a93166200c3d7455262cc4010ff0ab84c59880e1f2157098b3101c3f42aeda16620087f865d742cc4010ff0eb2e85988021f61d65d0b3101c3f42aec216620087f865d442cc4010ff0eb2885988021f61d6510b310061fba2a8b066206c3c7455160cc4010ff0ab96c89880e1f21572d91310043fc2ae1b22620387c855c3644c40153b06206c898802ad60440d913100477c12eab2262098ec825d5644c4011ef02baac8988023ee01755913100c7c402eab226200a3d84d4d644c40117f0eb20c8988028f61276551310051fc22ecaa26200a6f825d9544c4014d904bb2a8988029de0576551310053dc02ecaa26246a78805d9544c5254bf06b22a6988031b5d752d893100572c0841b1262008ef87588624c4014d90ab10c498af2b3e0d621893104c76412ea312620087f855c0624c4070f90ab80c4988022fe1170189310345e422e03126209ce8205c0624c4010ff0abb4849880e1f215769093104c76412ed21262068ee87d89424c4051b90cb98849882739189718c93122e2e3b2a69926200e4d53189324c40b8b8e6a9ec09880a3b20975593210047dc02eab2642018f8805d564c840147b09a9ac99080e1fa1770593210043ec2ee0b264200a3d849d954c840147f08bb2a9908029ee0176553212353c402ecaa64247a6d861c954c840d87ce8aa6c7908030f5d154d8f210052ec1ea8b1e420387e85dc163c84010fb0bb82c7908029760e7654f2100537414eca9e4200a5f835d953c840b4bd07b22a7908029760f6454f210063abb6e2a9e42068f7865c743c84070fd0bbb287908021f6177650f2123e36bb2a91964205c6d7654e32c840bc9cc6a9c65908179318d534cb210061fba2a8b064206c3c7455160c84014bd07306ca908029760e60d95215dd37416e9b2a4274a6d82dd365484010ff06ba6ca908030f5d074d95210043fc22e7b2a4200c5d731cf65485754dd0439eca909d29b60873d95210052f41ce1b2a4200a5d839c365484c54dd04386ca909d29b60870d95213a53b408e1b2a4200a75811c365484010fd0e206ca908021f61c40d95210052f41881b2a4200a5d8310365484014dd04206ca908029b60840d95213a53b40881b2a4200a7
  | 16 => 0x498d410062ebaec731a8200e1d54d8e63504f727f0eaa0c6a091e4f61d5418d410046fc3ac631a8200e1d5458c63504014bb073b2a6a080297e0d7654d4100537c12eca9a8200a6c825d953504014ef02bb2a6a08029ee017654d412253c402eca9a8284c5c63dd153504f363b073a2a6a09168f2197454d413dd8fc1ae8a9a8205a5e86d8d53504074bd0fb1aa6a080e9721f6354d410062fba6c6a9a8200a5d80d8d535040d87ec2bae86a081b4dd8575d0d410069b882eba1a8205e1c6354f435040b8b8c6bac86a08764fe1d5490d4123e1f3b2a921a8247d367155243504018baebb1c86a0803875536390d410069aaa2e321a8254c5c635d5435048f878ecaa286a09538718d5450d4123e9a38aa8a1a8200c5d75d8d4350401a6aa9b8a86a09530f1d97550d410058fc1aeaa1a8200d34715d5435040187f0cbaa86a08030f2197550d413dc9fc1aeaa1a8200d1f835d54350401a5f04baa86a08034b2097550d410069bc0aeaa1a8200d34815d543504a387ec2baa86a09474dd857550d410069dc02eaa1a8200d38805d54350401a6e20baa86a0803475d76350d410068eba8c6a1a827993d8754d435040b878eca9a86a08178718d5350d410069abaee2a1a8200a3d84d4f62504015cb02106c4a08038b55362989410ec9e43aa8b12827cd38705516250401a3aa9b9ac4a08034755073589410069caa6e0b1282008ef875886250401c5aa8b10c4a0802ba20162189410043fc2ae0312820387c855c0625048f87cecaa484a091f4d9c5549094100716aa6c52128200d35545c6425048f878ecaa284a091f4d1c5545094100716aa0c4a128200d3554dc542504051790cba664a08024fe1d54cc9410049ec3aa9992820087f855da32504070f90abb464a08030f9d9548c9410061ebb2a91928247d34715513250401a6aa9b8a64a08171718d750c9410145e432e81928205c9c635d0325040127f0eaa064a08024f61d540c94123e9b38aa81928200c5d75d8c3250401a6aa8b8864a09f38e98154d814123e1eba2a9b02827ce3a40553605043b2790eaa2c0a09f38e18154581410068eaa6e6b028200d1d541cd6050401a5aa9b92c0a08034b550725814100674300e4b028284c3f43dd165cc50987a87ba2cb988030fdd2745973100537c12e8b2e6200a6c825d165cc4014ef02ba2cb989169d20574597310053dc02e8b2e6200a78805d165cc4018dee5392cb988029de05725973122d3a40ae4b2e6200a6e829c165cc4014db05382cb989169da0670597310053ac0ce0b2e6205a5e831c165cc4374bb06382cb988021fa1c40597310043ec3880b2e6205a5e8310165cc4014bb06202cb988029ba08405973100536c1080b2e6245a768110165cc4014eb02202cb989169da0420597310053ac0840b2e6254a3d849d564cc4011df0
  | 17 => 0x2e8200c6f729c965d04014bd06382cba08029760c70597410043f43860b2e820087d870c165d048f4ed02102cba08029d60420597414649fc36e6aa6828c93d86dcd54d0519a3cc7b9aa9a0a334758f73553410051ec34e6aa68200a3f865cd54d040165f04b9aa9a0802cb20973553410059bc0ae6aa68247b34815cd54d040167700b9aa9a09fece20173553410051ec34e4aa68200a3f865c954d040167700b92a9a09fece20172553410051fc32e0aa68200b2f825c154d040165904b82a9a09469760e7558f414652fc1aeab1e8200a3d84d4d63d04070fd0bb92c7a08021f6177258f4101c3f42ee0b1e820087d85dc163d048b47d09bb2a7a09470f9d37654f4128e1f426eca9e820387d83dd953d04a387e87bb2a7a080297e0d7654f414643fc1aeca9e8200c5f835d953d04018ef02bb2a7a08031d2057654f410061fbb2e8a9e82bdb1f835d153d048b66902ba2a7a08034d1c57454f4101c3f43ac6a9e825187d8758d53d04018eaedb8aa7a08034d5d37154f410051fc32eaa1e828cb1f835d543d04a327f0cbaa87a08030fe197550f410068fc1aeaa1e8200d2f825d543d0401a5904baa87a08034de057550f410069a40aeaa1e8200d3b805d543d0401a7100baa87a08028fe195350f4102e2f39aa73168200c5d7354e62d04010ff0ab84c5a080e1f2157098b410051ec26a6b16820387e855db32d04010ff0cbae65a08021fe1d65ccb410043ec3acb996820093f8755332d040127b0eaa665a081b2b9d162ccb410361f3b2a91968200c3d7655232d04070fd0abb065a08021fe19750cb410043fc3aca196820087d8759432d040127f0eaa065a08024f61d540cb410359b426e2aa28243c3c76dcd545051987ec3b9aa8a0a334dd8773551410069b886e6aa28247a3e869cd545040147b0d39aa8a091ecda0673551410059ac0ce6aa28200a3f865cd545048f4790cb9aa8a08f70f1d9735514100597c12e6aa28200b2c825cd545040166f02b9aa8a091ecd20573551410059dc02e6aa2827cb38805cd545048f47d0d392a8a08028f61a725514117e1e3b4e4aa28247b36819c9545040166b03392a8a08028fe19725514123d1e432e4aa28200b37815c9545048f66902b92a8a0802cee0172551413e59c402e4aa2822ec3c761c9545048f66d0fb8aa8a091f4da1f71551410359b436e2aa28206b3486dc5545048fa6cedb8aa8a091f4d1db71551410069bb9ee2aa28200d3573dc5545040166b01b8aa8a091ecd20770551410051fc32e0aa28247a3c865c1545040165f04b82a8a0802cb20970551410059bc0ae0aa28247b34815c154504014bb07aa6c6a08028f61353d8d4101c6fc3aa7b1a820087f855cb63504070f90ab96c6a08021fe1570d8d4101c3e42ae1b1a8200a5d850c3635040b8b8c6bacc6a08764fe1d5
  | 18 => 0xc80147b0d322a91901a8fe19645523201d1f43ac8aa46403a3c87591548c80147f02b22a9192330f99373552320061eb26e6aa46406c3e645d7438c80187aeab2687191470f9917550e320061ebaac8a1c640387e87dd5618c8018bee7baac3190021f61375586320043f438eab0c6400a3d841d5618c8018bee63aac3190021fa1f545863201c3e43ea8b0c640087e87551618c8010f90eaa2c3190021fa1f53586326143e43aa6b0c6487e563154d618c8070fd0fbaac1190021f61375582320043f438eab046400a5d831d5608c8010fd0faa2c11900e1f21f54582320043f43aa8b04640087c87551608c8010fd0fa9ac1191ba1f21d53582320052ec1ea9b22640087f855c7644c8070f90ab8ec8990021fe1570d913201c3e42ae1b226400a9d83103644c80155b04206c8990023be0975591320047bc0aeab2264028f4815d5644c8011f700baac8990063e20175591320052ec1ea8b226400a3d84d4d644c8070fd0bb92c8990021f61772591320045fc3ac83226400a3d849d9544c80147f08bb2a8990029be0976551320053bc0aecaa26447a74815d9544c8014f700bb2a89911a9e2017655132426a6196e8a9a6486c6e76dc9534c84d2bf0ea9e8699003179d953d0d320070fb22a7a1a6400d4d539cb434c8a9a9864baa869900e1fa1676909320043ec2ced2126405d4e7254e324c80bc9ec4a9c64990031d5d751d85320052ec1ea9b026400c3f749d1650c9834df04ba2ca190269b20974594320053dc02e8b286400a78805d1650c9814bf06b8aca190169720d71594325fd37c12e2b286409a6c825c5650c80147d0838aca190028f61071594320043f43882b28640087d87105650c8134dd05382ca192fa9b60a705943202d2f418e0b286422a5d831c1650c8010fd0e202ca190021f61c405943202d2f41880b286400a5d83101650c8134dd04202ca190029b60840594320053b40880b286400a7581101650c80b4bd07082ca190029760e105943204d3741020b286400a6d82041650c8a947b093aac8190263b20975590320047dc02eab2064018f8805d5640c90947f08baac81900e1fa1771590320043ec2ee2b20640387e85dc1640c8010fb0bb82c81900e1f61376550320051fc22ecaa06400a7b805d9540c88d4f100bb2a8192121fe1176550320061fc22ecaa06400c6c825d9540c8018f700bb2a8190031e201765503201c3f43ac8aa0645487d87591540c8018daedb92a8190029b6187255032005a6c18e4aa0640387e855db420c86f0ff0cbae841908a1fe1d65d08320043ec3acba106400c5f54dd9320c81399ca5bb264190033354b764c8320062fbb2a899064058dc835d5610c80187ee8aa2c01901b0f1d154580320351f424e6b2e827ea3d849cd65d04018bee739acba08029de05735974123d3a40ae6b
  | 19 => 0x169d2057654d420053dc02eca9a8444a78805d9535086527f0eaa486a1003875536390d4200696aa4e521a8451d2c425d5435080da5ce4aa484a101b8bd8954909420051ec26a7b0a8400c7975d4360508018bee739aca213269be09735944204d36412e6b288400a77815cd65108014e902b9aca210269ba0a715944264536c14e2b288406a3e841c5651085d47b0838aca210021fa1c31594420043ec3862b288406a3e840c5651080147b0818aca210269ba08315944200536c1062b288400a7a800c565108014f30018aca2131e8fe1170594420351e422e0b2884c6a6f825c165108134d904b82ca2100297a0c70594420052ec18e0b28840087e870c165108010fb0e182ca2101a8fa1310594420051ec2620b288409a6e8204165108014db04082ca211469760e7558c420047bc0aeab1884028f4815d563109194bf06baac62100e1fa177158c420043ec2ee2b18840387e85dc163108010fb0bb82c62100e1f60f7654c420052fc1aeca988400a77815d9531088b4e902bb2a6212321fe0d7654c420062fc1aeca988400c6c825d953108018ef02bb2a6210031d2057654c4201c3f43ac6a98845187d8758d53108018daedb92a6210029b6187254c4200596c20e4a988400c3f53dd9421081395ca5bb284210032b54b76508420061fbb2a6a108400c5f7354d611080b8b8e6a9ac22101a2f21175580420061fba4e8b2e6400a6f825d165cc98b4d904ba2cb9921a97e0d72597320053bc0ae4b2e6400a74815c965cc8014df04b8acb993129b20971597320051f420e2b2e6400a3d841c565cc8010fd0e20acb990021f61c41597320053d40042b2e6400a798008565cc9874dd05382cb990029b60a70597320053b40ce0b2e6400a75819c165cc80b4bd06382cb990ae9760c70597320043f43880b2e640087d8710165cc80b4bd06202cb990029760c40597320053741080b2e6400a6d8210165cc8014ed02202cb990029d604405973202d2f41c40b2e6400a5d8388165cc8014ed02102cb990029d60420597320053741020b2e6400a6d8204165cc8a947b093aac9992128fe1175593320052ec1ea8b26640387e85dc564cc8010fb0bb8ac99900e1fa1770593320043ec2ee0b266405a9e8310164cc80155b04202c999002ad604405933201c3ec26ecaa66400a3f845d954cc9090ff08bb2a9990030fe11765533200637c12ecaa6640387e8759154cc8a90fb0eb22a9990031b5db725533200636bb0e4aa6640087f865d742cc8010ff0eb2e85990ba1fe197510b3215c3fc3aca2166400a5d83d5160cc8010ff0ab8ec91900e1f21571d92320043fc2ae1b24640387c855c3648c8131790eaa2c9190028f61353592320051ec24ecaa46447a76819d9548c8014eb033b2a91911a9ea0276552320053cc04ecaa46400a3f845d9548
  | 20 => 0x3fc3aa7b0a8600c7575d476150c010fb0f32ec0a18021fe1d65d81430043ec3cebb028600a5d839d76050c070ff0ebaec0a18031ee0175d81430063c402ebb02860087d87d536050c014bb07aa6c0a1b2a1fe1d54d81430043ec3ea7b02866e87f8754f6050c018f2eba86c0a18031bdca72594430351f420e2b28863aa3d841c56510c014f50010aca218029e600215944302d2f418e0b28863aa5d831c16510c014ed02102ca218029d60420594430053741020b288600a6d820416510c010ff0ab8cc42180e1f21571988430043fc2ae1310860387c855c26210c018bee739acba10029be09735974266d36412e6b2e848ea3f845c965d08014f700b92cba10029e201725974266537414e2b2e8400a6d829c565d08014f50138acba10029e60271597420351f420e2b2e8437a3d841c565d08010fd0e18acba10021f61c31597420351f42062b2e8400a3d840c565d08014dd0418acba10029b60831597420053d40062b2e8400a79800c565d080d47d0910acba10028f61221597420053d40042b2e8400a798008565d08014df04b82cba132e9b20970597420052f418e0b2e8400a5d831c165d08010fd0e182cba10021f61c30597420053b40840b2e8400a758108165d08014dd04082cba10029b608105974228d2ec1ceab1e848ca5f835d563d080147b09a9ac7a100e1fa177158f420043ec2ee2b1e8406a9e840c563d080159b0418ac7a1002b66003158f4201c3f42ee0b1e840087d85dc163d08070fb07bb2a7a100297e0d7654f424643fc1aeca9e8400c5f835d953d08018df04bb2a7a100e1fa1d6354f4228c3ec3ac6a9e8400c6d76dc953d08018daec392a7a10028f61353587420052ec1ea8b1c84098dc8754d63908014bb073b2a7211169da067654e420053ac0ceca9c8444a7a809d953908014f3013b2a72100297e0d7654e424262f31ee8a9c8405a5f8658d53908074bd0eb1aa72100e9721d6354e420062fba2c6a9c8400a5f8058d539080b8bcc6bac8721003175d56390e422a62f31aeaa1c8400c5d7558d43908070fd0fbaac3210021f60f75586420043f438eab0c8400a3d841d561908010fd0faa2c3212021f21d54586420043f43ea6b0c840387c87d4d61908010fd0ea9ac3210021f21d535864201c3f43eeab048400c3f74dd560908010fb07baac1210021fa1c75582420061fba0eab048400a5d831d560908010fd0faa2c12132a1f21d54582424871d202a8b04840087e87d4d60908070f90fa9ac1210021fa1d53582420043e43aa6b04848cd2c42dcd545091d8dcedb92a8a10028f61353d8d420043fc2ae3b1a840387c855c7635080153b0818ec6a1002b360831d8d420043fc2ae1b1a840387c855c363508011bf0eb18c6a10029760e7654d420052fc1aeca9a8400a6f825d953508014ef02bb2a6a11
  | 21 => 0x825c56550c014d904b8acaa18029ee0171595430053c402e2b2a8600c6c721c56550c018eae238acaa18029da1c71595430063b438e2b2a8600e35841c56550c018eee838acaa18038ddd071595430063bb98e2b2a8600e57731c56550c01ccee438acaa18031d9c871595430063a390e2b2a8600e64721c56550c018c8e438acaa19468fa1231595430051ec2462b2a8651a3e848856550c0147b0910acaa19468fa1021595430051ec2042b2a8654a5e830856550c014bb0610acaa18029ea0021595430053cc0042b2a8600c7b74dc16550c01c76e9b82caa180396e0f70595430063db9ee0b2a8600e5b73dc16550c01cd6e5b82caa18039a1cb705954300739b8ee0b2a8600e7071dc16550c0147b09382caa18029760e705954300537414e0b2a8600a6d829c16550c018d8e5382caa18029da0670595430053ac0ce0b2a8600c74719c16550c014f501382caa18028fe1170595430052fc1ae0b2a8600a6f825c16550c014d904b82caa18029de0570595430053a40ae0b2a8600c6c721c16550c018e8e2382caa18031e5c070595430053d438e0b2a8600c7a871c16550c018f6e8382caa18038edd070595430072cc18e0b2a8600c7b731c16550c01cb6e6382caa18039adc870595430063d390e0b2a8600c78721c16550c01cd0e4382caa18031a1c8705954300739b88e0b2a8600c7a711c16550c018f0e2382caa18039c1c4705954300638388e0b2a8654a5e839016550c014bb07202caa195297a0e20595430052ec1c40b2a8651a3e840816550c0147b08102caa195297a0c20595430052ec1840b2a8600a76810816550c014eb02102caa19468fa1310595430051ec2620b2a8654a5e838416550c014bb07082caa19468fa1010595430051ec2020b2a8654a5e830416550c014bb06082caa18029ba08105954300536c1020b2a865493d84dcd5450ca98bcedb9aa8a1b3f1761b73551432a68f426e6aa286cfd1d84dcd5450ca98bec9b9aa8a195347d937355143464af438e6aa28606b1c841cd5450ca32bb07ba2a6a19470f9db7454d436761ec36e8a9a8684d1e83dd15350d9da3b07ba2a6a1a130fd8f7454d4328e8fb1ee8a9a868493e871d15350c0b639063a2a6a18031be0975d89430043ec3ea9b128600a5d83d536250c5d0ff0eaa6c4a18021f61f53d89430051ec26a7b12862287f8754f6250c018daeba96c4a18031b5d452d89430043ec3cca312860087f875946250c011df0eb10c4a18271b20975189430043ec3ea8312863787f875506250c010fb0fa98c4a18ae1fe1d531894300636baea4312860087d879976150c010ff0eb2ec2a18021f61e75d85430051ec24ebb0a860387f875d76150c018ef02baec2a18031d20575d85430043ec3ea9b0a868087f875536150c010fb0fa9ec2a18028f61353d8543614
  | 22 => 0x10acba195297a0c70597430052ec18e0b2e8606a3e8408165d0c0147b08102cba18029da0420597430053ac0840b2e8606a3e84c4165d0c0147b09882cba181a8fa1010597430051ec2020b2e8600a6e8204165d0c014db04082cba1816c720f7454f432a49ec36e8a9e8600c3d86dd153d0c010ff0ab8cc5a180e1f2157198b430043fc2ae1316860387c855c262d0c0147b09a9ac5a1802ba6002158b430051ec26a6b0e8692e563154d61d0da34bf06ba2cb218029be09745964300536412e8b2c8600a77815d16590c014e902ba2cb218029ee0174596430053c402e8b2c8600c6f729c96590ca347d0838acb218028f610715964302d2f41842b2c8600a5d830856590c014f50010acb218029e600215964302d2f41ce0b2c8668a5d839c16590c014dd05382cb218029b60a70596430053b40ce0b2c8600a75819c16590c0b4bd06382cb219029760c705964302d2f41c80b2c8600a5d839016590c0b4bd07102cb218029760e205964302d2f41840b2c8600a5d830816590c014ed02102cb218029d604205964302d2f41c20b2c8600a5d838416590c0b4bd06082cb218029760c10596430053741020b2c8600a6d820416590c0d63909b9aa9219525761b73552430062ec36e6aa4860087f855c66290c070f90ab8cc5218021fe157098a4301c3e42ae13148600a5d83d516290c015cb02102c5218029760f545824348f1d202a8b048600d1f74dcd6550c018deedb92caa18034bdd37259543006a7b9ee4b2a8600c6f761c96550c01a5ee8392caa180353dcc72595430063bbb6e2b2a8600d3774dc56550c01aaee7b8acaa18031ddd871595430069bba0e2b2a8600d57731c56550c01ac8e438acaa18031eddb70595430069dba6e0b2a8600d5b73dc16550c018f6ec382caa18034edd07059543006adb98e0b2a8600d68721c16550c01ae0e2382caa18028f60774595436861fba6e6b2a86d0c5f74dcd6550c01c3ee9b9acaa180297603735954300637ba6e4b2a8600e2f74dc96550c018dee7b92caa180393dcf72595430051ec24e4b2a8600a5d839c96550c014dd05392caa18031bdca72595430053b40ce4b2a8600a75819c96550c014f501392caa18029e60272595430051fc22e4b2a8600a5f835c96550c014ef02b92caa18029d20572595430053dc02e4b2a8600a78805c96550c014dd0e392caa18031ba1c725954300637ba0e4b2a8600e2f741c96550c018dee6392caa180393dcc72595430071bc26e2b2a8600c7774dc56550c01c6ee9b8acaa18031ddcf71595430072bb9ee2b2a8600e6772dc56550c01cc8e5b8acaa18028f61271595430052ec1ce2b2a8600a6e829c56550c014db0538acaa18031b1ca71595430053b40ce2b2a8600a7a809c56550c014f30138acaa18028fe1171595430052fc1ae2b2a8600a6f
  | 23 => 0x591530063db1ee0b22a600d5b63dc16454c01ab6e6382c8a98035adc87059153006b4390e0b22a600d73711c16454c01ae0e2382c8a999a9760e605915300537414c0b22a600a6d829816454c018d8e5302c8a98029da0660591530053ac0cc0b22a600c74719816454c018d8e4302c8a98031d1c460591530063db80c0b22a60093f875906454daf63f06b20c8a989a5760e72191534a4afc1ae2322a64395f835d36254ca30fb0fb26c4a99470f9d364d89530061eba6c9b12a600a6e82d936254c014d904b26c4a98029b61a21d8953005a6c1843b12a600b69800876254ca387ce8b24c4a98029be0964989530053a40ac9312a600a78805926254dada9ae7b14c4a98029b61f629895300636c3ec5312a6d6c6d73d8a6254c01c9ae7b14c4a98029b60a61989530063ab8cc3312a600a3d841866254c014db05304c4a98029da0660989530063cb84c1312a600c7471d916254c018e8e2b22c4a9a1b53dcf625895322cbb43ee2b12a600d5773dc56254c018eec9b8ac4a98031d59371589530063bb1ee2b12a600d5763dc56254c018eeec38ac4a980355dcc7158953006b3b90e2b12a65187d87d906254ca387ce9b20c4a98030f5d3641895300537c12c8312a600a74815906254c014f100b20c4a9b56d360e62189530043fc3ac4312a600a74815886254c012df0eb10c4a9b52d3e0d6218953005b240ac4312a69495f835c46254c0147b08308c4a9802d360c21189530073230842312a600b69800846254c014db05300c4a98029da06601895322c3ec3ec9b0aa651c3e74d936154c0187ae9b26c2a99169d20564d855302caf41ce5b0aa62695d839cb6154c8b0f90eb22c2a99169d2056458553006a7b9ee4b0aa600c6f64dc96154c018dac9b92c2a98031bd8f7258553006a7b1ee4b0aa600d4f731c96154c018dec8392c2a98031b590725855300637b18e4b0aa600d4f631c96154c018dcc2392c2a98031b1847258553006b2308e4b0aa6d3d5773d856154c01ac8e5b0ac2a990e57e0d74d815302cae41ae9b02a64487d87d936054ca387ce9b26c0a98030f5d364d81532253c402c9b02a60595e839cb6054c4d2bb07396c0a988e57e0d72d815302cae41ae5b02a69495f835c76054c0b2b906b8ec0a99121f21d645815328e1e3a2c8b02a644a78805916054da5ab6e7b02c0a9b428fe11735974300537c12e6b2e8600a6c825cd65d0c014ef02b9acba18029d20573597430053dc02e6b2e8600a78805cd65d0c018dee5392cba181a8fa1271597433d51ec24e2b2e8600a6e829c565d0c014db0538acba18029ea0271597430053cc04e2b2e8606a3e841c565d0c8747b0838acba181a8fa1231597430051ec2462b2e8606a3e8488565d0c0147b0910acba181a8fa1021597430051ec2042b2e8600a7a8008565d0c014f300
  | 24 => 0x2a800d3b741c16255001ad6e4382c4aa1521f61f63189542a62f39ec6312a800c5d73d8c62550014df04b18c4aa0029d20563189540053c402c6312a8dbb2d8498862550010ff0eb10c4aa0029e2016218954004b7c3ac4312a8dab2f8458862550016d100b10c4aa0029b60a61189540053d404c2312a89593f845c062550014bb06300c4aa002cb6102018954005b2c0840312a800e6860080625508127f08b9ec2aa01a4f21173d855423c3ec3ec7b0aa854c5e73d8f61550018bae7b1ec2aa11e9d20563d85540349f424e5b0aa83293d849cb615505f27f08b96c2aa01a4f21172d85544ac9fc22e1b0aa80693c845c3615508f0f90eb1ac2aa153171cd635855423d3a40ac6b0aa8d9d3774d85615508d0fb0fb1ec0aa153179cf63d81540062eb9ec7b02a846a788058f605500d27d09396c0aa0ca4f61272d81542343e43ac6b02a846a788058d6055001a5ee9b92c0aa0031bd93725815400697b26e4b02a800c6f63dc960550018dac7b92c0aa0034bdd0725815400637b20e4b02a800d2f641c960550018dec6392c0aa0031b58c725815400637300e4b02a800c6c601c96055001ad0c0392c0aa3634edd36058154006b4396c0b02a85187d871876454ca347d0830ec8a98031d5c461d91533452ec1cc1b22a600a6e829836454c014db05306c8a98029da0660d91530053ac0cc1b22a65187d871836454ca347d08306c8a98031e5c060d915300637b94e5b22a640a5d831cb6454c814bb07b8ec8a98028f61071d91530063ab88e3b22a694c5d738c76454d094bd0610ec8a98029760c21d91530053d40043b22a600a79800876454d094bd07386c8a99a29760e70d915300537414e1b22a600a6d829c36454c014ed03386c8a98029d60670d91530051ec20e1b22a640a5d831c36454c018f2e0386c8a9a1297a0e40d91530052ec1c81b22a684a5e838836454c014bb07106c8a9a1297a0c20d91530052ec1841b22a600a76810836454c014eb02106c8a9a1297a0e10d91530052ec1c21b22a684a5e830436454c014bb06086c8a98029ba0810d915300536c1021b22a6ced1d73d926454ca347b0fb24c8a98030f61f64991536761eb9ec9322a651e1d73d926454da1a3ee9b9ac8a980353dcf725915300637b1ee4b22a600d4f63dc96454c01a9ee6392c8a98031bd8c7259153006a7b18e4b22a64597687dc56454c01aaee7b8ac8a980359dcb7159153006b2396e2b22a600c7763dc56454c01aaec7b8ac8a980355dcc7159153006b3b90e2b22a600d64721c56454ca347d0930ac8a98031b1ca61591530063c384c2b22a651a3e841856454c018d8e430ac8a98031ddc461591530063c380c2b22a64497a87dc16454c01ab6e7b82c8a98035adcb7059153006b4396e0b22a600d7371dc16454c01ae0e3b82c8a980356e0f70
  | 25 => 0x400800a0010002008009800802607600100000000180048040008001000005c02c0090021ea8f61261d8d5400537414c3b1aa800a6d8298763550014f50130ec6aa0029e60261d8d542a43ec38c3b1aa854a5e8318763550018eae230ec6aa1521f61c60d8d542a52f418c1b1aa800c797018363550018dee5396c6aa10e8f61072d8d542a51f424e3b1aa87aa3d849c763550014dd0538ec6aa0029b60a71d8d540053d404e3b1aa800a79809c7635508747b0838ec6aa0029760c71d8d540063ab88e3b1aa88ca3e848c7635500147b0918ec6aa2328fa1221d8d540051ec2443b1aa88ca3e84087635500147b0810ec6aa0029ea0021d8d540053cc0043b1aa843a3d84dc363550014bb06386c6aa0031e5c070d8d544ae1eba481b1aa88ca3e84083635500147b08106c6aa0029da0420d8d540053ac0841b1aa88ca3e84c43635500147b09886c6aa2328fa1010d8d540051ec2021b1aa800a6e8204363550014db04086c6aa33f475d36398d542a52ec3ec731aa800c5d87d8e635519f8bae9b1cc6aa153875d36398d546868fba6c6b1aa800d2f74dc963550018dec9b92c6aa0034bd937258d5400697ba0e4b1aa800c6f641c96355001a5ec8392c6aa11e5da1f7158d540069bba6e2b1aa800d6772dc56355001ac8e5b8ac6aa0034de137158d540063bb26e2b1aa800d3764dc56355001a6ee838ac6aa00359dc87158d54006b2390e2b1aa878a3d8498563550014dd0530ac6aa0029b60a6158d5400636394c2b1aa800a7a8098563550014f30130ac6aa0031e1c26158d5400636390c2b1aa800c777118563550018f0e030ac6aa11a5ea1f7058d540069dba6e0b1aa800d6b72dc16355001ad0e5b82c6aa0035cdc77058d54006b838ee0b1aa800c7b64dc16355001a76c9b82c6aa0034edd07058d54006b5b90e0b1aa800d68721c16355001ae6e2382c6aa0035c1c47058d542a52f41cc0b1aa800c6c7298163550018e8e3302c6aa15297a0c6058d5400636390c0b1aa800c747118163550018f6e0302c6aa00257e1d6318d546ed8fc22c631aa83293d849c8635512b27f08b80c6aa1024fe1173d89542a43ec3ec7b12a854c5e73d8f62550018bae7b1ec4aa0029ba0b63d895400536412c7b12a800a6d86883625500165b08106c4aa002d960420d89542a62f39ac7312a800a6f8258e62550014e902b1cc4aa0029e20163989546e696ba6c5312a800a6d87d8a62550018db0fb14c4aa3731b5d3629895400716ba6c5312a800a6d8298662550018eae330cc4aa0029ea02619895400536c14c1312a800c797098262550014bb06304c4aa0031e1c363589540063c382c6b12a88ed2f74d89625508d2f50fb82c4aa0034edd370589540063db26e0b12a800d3b64dc162550018f6c7b82c4aa0031e58f70589540063dbb0e0b1
  | 26 => 0x500000440000038020002001000002c00000d0048054068003004801400a00100600b401400b00e00000040550000014014012005000003400300001580000560038000000009001002004c0110008080026000009002000e001000002401e009003801c000003000800800400900680700180030048000018000000800000800700080000000380060008000007001800800000000a80240060030030028000002000800005c00000000180bc0090000020006003000009c0000000080008002007000003800c0040050010002007007001001a004003001000a0060070000008000005009c00a01f00080000d4005004001c00200002c800001e00300000500140240130014012000000001001a002000000000000c000002800801500380300000010000004000000000002800602a021800c01e00000000300800040008010016002000808c00000100a8018024013001001800c048004000c000000000801800600300480080040030048010018004000804c01c00a009800400800100100240240280020030006011000016402400d00000000020010098000000016004004002200100300200040030010004012002008000c0020070000014004001003800400203a000001000a00d0038038002001000000400a014001800c0000000000020000002004001000400c01a8000006003000801808201b015801c008003004000400400200080340000170048004012000000000c0ac01500782e8002008003001402c00c01a80100060000010000000006001005000c00c035804801e00000600180940020108004010003000009c002001000003800000d00580040000020028010000003001000001c000000804402e0000030038002005002000000a00000e00140ea046004805c0040030058000016004004801402a00000000000020060000088022000001001400000d000803001c0000048028008003000000800400200a000001003b00f000800200000e00000040430010068004026000000c00200700000580000030010138058006000003c006009002801805e0060000028016009002801c0000010000020004000003001400200200580280000230048008006014028800c02c0000078004028051001801402400100480400260250040000010008004000001200300000f402c0050008008000002002006000a00100000240260040058024002007000004c0080000008004000004001803800200700000080080000008024008004000001000c0010000024004000003800004207200000040760070018028002005003004807000600100240040030010008000014003800007c0060090020002002001801800a004000800000a0020038008000000000000005800b001006c004012032801003200300281c400400400b004c
  | 27 => 0xa7d43265c02db1ad8a583b34fd31d904ea3e3de263c54200000014e99ba0007008d9400000028ca0887c243006e2cbd50a06e0a48638fe4d9567c0000e923cf47034fd84cdea4af04791047806f300016509bc010b2786d8dd158caf255949e3000169415ebf1001b7b1b8c4733d514bd0305e40938ca5ba68a24d9a12ca6229c58a06c8a82004800400a000000001800c0150058004000027003001c0100070090008000000000000804c007002000400a001000800400000000000b801a001008803000a0010038008004002008007400a005001000c002000006804002400c003001000c0400000058008004005805000c000004000000001a01d0008000001007801801a00001c000403801c000801000001e000805c0080010048134000010002005c0020060060010000011000001c000000005007805a002003001002000100c0004000001000002400600100a801c00000001d8024008001003000005201000180040060000020058014000000000400401a0000004018002000800000e001000001800000900d001000a000038800000603900080000000070060000002010003800001200100c0030000007000000802400b00e0004000002000008803a004009800804e000001801000a02d001801800a003001800c02400200d802800200300f00000180010000000002005000800c00a000000800c00400a0020004006003002000400c00900400f4000007001000006a004009000c046004001801801a0000008014008017000800800800300c80200000010100000002006004800000a000000802000200000280040040000000000000014003000000e0010010020004000009800c02c034003000000800d001800c008003001804400c00c002802801c00500a000000800700300140a00000090004010000000002000000800100000020110000004014010002801800403d0048008000002001000401e001000802000600f00500300000050008008032000000808002600c012002c004004005800400a064006800c02800100d000c03e000006805c006014000003001800000100100040000020008002011004000800000300200440040030058004018004000001000e00000b00040000100000020002002000800400a00000580300020010000014012007003000402e00100000080000000050000006000003000c01c0000090000006004000800802c003009000401600a003003c028000008000800200c00e000800000100800080000260040000016000000800001400100f00080080000038018022009000002c008000007800000a0060000000012007002001c0100020168018006034001801005e00500b000c004009004000001601500a80180600010068024008001001805401c00100080040020020020048000009
  | 28 => 0x17f000108931cdb42ceae6d89eb330a7b581830a822ab0d08e0209e1c00fc00000727060000a288843e6b82886e9c312cab3554c3b6562b7ac6be38d43883c04f40005032a39a7c23e000000000a0000001ffc8f81822a221bc5466ab17213480000000001f112a66d94ae1c858708c0614a99063a49224b2b61a82c5d42a200000082829ab5680002333a2b50000009d3d3170cabc0006230c383bc25244080a0e7600000000000005a93c7a56000000040ab145122bab069999c91611313407e52609546fd99c13303b24e5a6d19dad5f5bb925da129f606f9d8c22e26a13cb76413027247492e025e71c27183300009a11021808ec2b1e3dd0b6c610a9f3c1a72186c9825d3238cc82bf8150201850aad053d8990000c724be10002ee7e2000000043e8930d383b4fe00f308290f9ba00000528509bded23000163cb3e8df0003070000281095252851a1f24fe9ff4d76c2b1cb31ac3369e828b31b00009854b0a83cf4057100029954960003a79970000ceb28e83a17d605824e0000ece2545d98e3d716a43000369d4880006570a95a081120000000d8444b0520c5c000dc33e335c99be00054b29540007e100018e03505b426d00000000000000a113a870c6d08001452d3a00036285e6af73cc1d553ca96c315363c4ca69e27a9560dd20006b19cf400014a527a871b507bb273a3c8fccd674ee000071c02f4262bb0ff8b716481b5d4cc3680c902d90f6aeb0000000ad47c7000083400000000029d80000b33290d8d45ea4a4160ad5bf86f60000b24b8e3431790e1093232d35199854100384d31e905c455060f2554bbec0d3700ef83fedb738b9060000d4a6790b7c43c3723f6af042a810a484a5e026c16e49d04ed5688190e11ad4e748166a72a2d29eca91a00fc80b88722f49ce14ba90e000261c97e16238a9d505b00000ea87f18289ed41f00013be2bf48f00008da22505c986800000052d9a4d160d534ec800186633f308974d4920000002cd8030000382104c8d2afb1aa2f70b2c38300014409969ac3e71d61ad47050820138f42c491918104f1800010e92880c80003d1af3c0004e04cf800000000038e8a3c98e0003528001b64b831878c840001036cb127999ab7f6740cd068e68760fab1c72e0561088e511ea470630080db3267613fae240b62e64251145acc8c75290c007620863d10f204247296421c40f0e1d900015908ea98d65e91b8e7ea1e05f95e9a76614378061557236f0a8a4d8000d6b0003094532dbe0002fccf729ad03f8001a0cb011b699608ca00059198386b60006dd81415e6b9f1a832580005bc59d0fcc00078d28327ec9da5f03131f1425ac953028c612f285968e85381e8243144a8dcd4c0f7360987090c27800017b15faae3373383459a8430cb27ac3c6c212149f7051c9be1aaa97168e3776f9
  | 29 => 0x11dc1d65b4a3ad3165286c32f2978cd47049a87cb9e36700e3604d2a44a3f780018220006c703ec8b00005bc1650000caa567220ceba5f46bd1fed818ab60c5115cf1072348c800019a3e94108000abe09f0001fd5a9825540e0001baaab500016d43d64e860927543449220be05cc1e2000000204cbcee100001fa01749286ca057cca87ae5b7892419e74207516ac00091d65331a94e60006732af9c1613f36d0000cfe00052fa170e9a2861850000000c5e0000000f5200031100000003a9000000095e4206f700c400044e074afb8000b6645700ad9ce9736c2a9080005a8000225400000062400013e68fe3f70000000b6c61627b875e83542e922563ab9064287f507e03f31b0fb1a4a56f0bf22e88804b3389916482e0001e517d400069701811dd98e4116619de0ff4bb9000343c1624fa000000003a16400023b508c4e90ae379174a000211930946a0537011014b388660c416980006de4660000fc634c24700016201ba0000d040000001c32730d9e00045a800183600024d80007bc00028ba45c4d217435f1f64000a72000326981e0006a495349740001d0822c6badb95360000000cfc342000185c635047ae65860cac009243c00086c1169dc13f0572000000000035c1b9a5387aa0005d693751ec8cd24500018963950001e403d49b10003819688856264207db880162d635645a67af08e0001a16c680002d78000c8202e8000210cd14b135c0b0c68100023ccb5c9ef0a28695bb0cd51c287a1abc0003548001a6400000004dc0280002f000015cc0651900a2c4b43d700019b47be77b627059508a1ec4710905156990222800069e84909a9a6c88e9c9555a13ca721ac4c42e9c9f0dff4d3a705c22301279b36c6c8000000305c400aa16cbb2040a40004cf16b4000000000186547a00048128a167e00017e927c08e9ff00015206f867800007883c242700027c00003c75d8aa300000001838661776ca72eb8b68cd2bcd69309bc4264e644f0441420b296c80c0cf169b741025d8c8a53e298223cc0653703d80000d667d00017f896243161b8598bc66aa4402c1c6c4d7f2c8aa697bc0bd003000156e00000015a4af802e3a406f52cc1be4a11e7812c6796f1299cd945591820000ee87b60000000bcc2c8506a4498f459725d8de8a9e43a0302760eeab86277ab04744c5b0259064efa39c4ddb324624db549a8a1c1c06cd1a4a0e857a70f2048388000b45000061c58a06933613440000004e1000000056526e00017c441e1930001ab6000587a47dbe4864158316450087a37700a832e98c49e999912cb2e3b7a2a522cadb69728946b2905060205c2128980001b197d0b2751a26001a290615228ccb440006038e68f264160f98e8c0004c02650f2506200014ab41c07c8786e7910c0000002278179746000000118400
  | 30 => 0x80ff2a29f9015c0220b3a4e51b20c4567942044ecce063b2cce96d316d89068a446dc40a33c56426214a80d14ea4b434c330f800018165e3365a90bdd1c38cec7fa3915e5929570485b050a6b80da9111212f6806ad5c6bb8bb8ecc2b14840435a3c45a3a500b4da4c006eda1fd6ba4d31dd0069784a5e38c2734d386ac11bad5115854b0d496c97feac86b082f91aec783cb998cd4800000016f4972d462b58fa16966946b70000000dac60226a53446f71ce90a8bfa30b1230474102b3e0002d6c24800017a1adc0000000860000b9200026caa0000061e0e00000dba000650ab54c981cd00028b904c00029d800113e9aa0000e3092625113387ed09a9f73f033505a000029c1b4c0004e2647b17da2647e6a80e2c00013044a02293f26106331708474d344ff0d20000494662901976e5d5000000042800000003e1214c650001040000dc937e83515480001e20f34c7a5dd582ab31664623235b1a40005eb544802d97c0000e733b000090d33730583a61a4342a6f516845b1fa00ec0004a165885b0f8422200000006a615229910840009314bf8001a442d9281ad299a400010298580186b100000001228f00a41c900002e30001dac7325dc306a104252a740000000000b8841a2da833872b38f91f59ca8420000f6800030269c0001aac0001cdab4422251800007518403922428aa4412c6100000018447091d6848cd4200021b29b80aa599000118c0000002fe312800000036494119946255579d6854e58105a83e93a48331abae44f909e967a08080b2803157b6b88d8000126333d08e22b01b310882880236da3155281f44f03714000d354ab2bc8aa6b94021b3182c05f14c0a3a92a400063e05b400000004d280c000000000013c3726c35daaa5c03c96e14d0bbc816c871c12fb4af2cea37180013c8c521480a990d00000000000490c2468f843c00061f1ff95f82c6b9800013c80007d254880017d8bc01e58001be854e4b8800019c7d10501eb029a2e100019e84c279122ea8e1444092332800046800000000018f2b612f402c0cc44c600fb2e0000c7400017e5bf000015d8000000b675f480016b026000011ec5fcae74afb7013123cc47e984cd5c7f44b5b09c41c3a563f85bced80e365798045dac5a3459c650eabf9000000033e000000000140000022f0f44aa84390000000e5c00059ea4012e4583065a8587a0b933873484ee403a68632ec7ca0331780dc0eda19926600000003f650d00289a04c961a1d1daca26d378af5c3ea00030e800195644c535830420400000000001c20754058fbc00000063aaf94572000000000187a0002e62308a16487006800052400000013c127600019b2875a5eaa93f497a80009af15d28a8000000531183000081d00014157f61e900000011fe000422088c000daf06d80019ae90700
  | 31 => 0x6a2f98000ab3000300cb9a95b000281479c42d38d9090000000126b4590d280523fb5602d2c91433a2710fc00023c14800000001a90001af20000d00000362a4537292dc0005d2047120c008aad3fc02ad48cd5d66028387260000d9800055a1f86050eed5a405a00000000000002f101300002d711723e843265d25300001f23e300031108c8000000377d0704723160bd59261345382d7d864bc85e634dc35a00029f95b4aa2c891311f2d75c73960a956cf5087c033232c9a80465bb1b556f600000026684bc6af450b738a7a85e66112a569c82533aaba8d706246451eb400044953e8001c08a0c42b80000000004529f9418400053c00013367770000000fee0880002af4458d184438000ba230612f8054c8ccfd36a1cc514cc1a6c4a5dc0006ad50db4ccf4ed7b6f18d2d7be9c651d91480e26a26ba12108102e00f70a449f27ec45e1d9442c41511eaa10ab40831a694d0356bb46219f5c42a9032752d253803b94f3a140fb0b12701aee82a01f75f79dcced2bce5518e293e802c3df10715bc83b6a7817d22a9c731b8cc59ac5fa16a99a146c79912022e10e83bd5cb03ad2e811f1d58fc46bcc0864025ed4587d36872d312d450a695a7410c477f42aa01078a01b10630e55b26fc5d1036885046f3f990e07503744070ce42ecbf218e20f592e20670703f9ad049147a277891813a19799dd1a82880b5140031857b4a2385198212e26b0f515acb4057c8ee18b853c14fad181503903ad98c163629424d189d01acda2ae36e92982b712e144c5f2baa2872514636ada39f082cc1edf74e51b2d2d2b8f32b0ba4c083ee2282f4018a7111f51821918a195cbb608a1aa7908c2d04aa431a4ad1cd5aec63b6b61bac000be442900007f2ac610e35a424c6400989a615c06ba3ea13d139e6646fd1ad1be08070000a281c82070001de8f38a7a00037280000000991469510543000023427a42e05618bd2e0a3c21e0001bc2b066fea168dd4a092bc06848140004b2a29c87e0005c2800000063228a8000e4c23f0000000a66bac2f7b440d1800057785e8e9c7620b8a0d940475758a969c000c883992d9404a73416023b00d80612241a48982b0b0ff000000000018b1b14f7a00011b2a9c000bbf2a11ecd1b66720e2992545a02600033dc000b3c00037c5018af12950b592802c20c696cc0002dc0000001854de061f8200000892184a84c28c00031f9bd42827220041ccc0004ae491b6c03ba4562cd903c10a5614999b44c940bc0000000b080005e229bdbcec946d580017b2ce92908ec0b00b9d188800003200000006693709375c0800000000000000000000001052a040004a70fb32dd3acda90de343525419d39bb40059c2733ef37d81de235416abb59740005ff17e0000b9a32aa225a86d4556fb2c823242f25b1e7c3b86e46ce16fd2
  | 32 => 0x86a0003792504b141862ed9fc4450be75fa000142e2d11a23065448a8d34d2c7d4fe5236ebaba0f640950e0a22837e1e615e2b2d28664d16900009ee0003af35881321da43996c484a5da0e78868000727000149568437b61d2c1068c9492b3a8500000005f0194c0000000ec2c0000049825687305664016c18d5800050968e10cc656a930ebb27508039f2bb83f1a5844410782086fc3fa327a8612c81834a882b5034c0b000076cc00b8440d9ac00001b515c1d19bacbb22299d9107200058b308c0007ea0002cec000b3969b00016d000000003c8f6800038f0231ade8850db327c4967c103a25f578a0f5344a344b0490c7049dc45caa544e23288b76a3f57705c0670b4f3400a312b258d0dc0554b7c14b1bf9f559bccfe33580010ec2c3267a0adb0e99107b0cb9372bd419810c8144bbd45cac4c4ba6282d1ac457a4547090a81c9e226e6ff130c454cf64958495a723f7377b18c7f800000017b8b8c9010002804000100000000027c00000005c8e4a8a4528b6b4c142560000d455f000052c28c836e7680902520632a982f68000e060000000000daca834cc8da898a3350dd8000ad000000018f800019400000000000000000fac6488bb0d50c540000002469680eec7f937127c845280f1bcadb8e16ccc4f32f8c6500090000ac834c4126e3963158824754a95d5a2a4543451ec481844618f14d82faad3592ac880000000229d6400062e572289c7f00002352e54ea206a05911880008af000010800000024aae29b7e93c0002c5d4e2b0a13a2e8000000016780005944d7404342891000000018e8e9800036f886db10d9b4caadc878455d4c20000000024665a8995f8c6717c310519063165b3551328040456a774004378490b5cd8e264b2e2992191a33e07e8ce9324d20000079da50657000350855800047d99c534ac77028a46c7f6ba919ea1ad48204d00000002a600003b072897a40d305ac909c25af4240ad896810b4ce0000b8872d14db3d5b7010731a00017fa6152b80e602b478a0001f68806b7a3481390c780736a92ed80000000002e71c261220000001b3a8a00001e9400067b00013b0000dcb23a30400000005fbb3e8b48bf50548000b160002eb1d80f70b2a428a76899c43b000000113254a0e19cbd4b41ed0a380000000000e8951823652b043aa1c856af500017049f8abc42992c177800000019d0afa4fb08080000007ca0c4891153a6ce11c0041a344a40423751a2278416f12a117a71a461acdd5fc8e509e0915a4e03d17b985d1927db3903130d7eb62000000159200052716680000000001da8e006430ca92c95c4c2d1a705e053a8f90f225f8a5c7d606b01bcb72e005ba2e1db9a6f43cd2dc0f2c70a0002d4d1b052d08b26800ce659447161422a7df0001af53b6620000089105e589000233883a2711
  | 33 => 0x54e0574b24abf1b5a714da06e102229580008650002c246440000e5ae00f3a02039800001cc0000000c940000001f1239c0000005058000aae00000000000000003a08e98000bd15869bb40002f651813103a0dd200000010c263348e035409295d3ff000171a9ec5f52b707a474313829dd906c310000000000a8f6aa800000000037d37794da1ae220a6a038e8326e4000000075054caec14a0b1a6b20db8b961d22ec8a5cb741ef25e2cb00006b239525bd25292f03197d97a600027eb83c000b9e3e03680530b083c28000fd69635ec26c88f40ee0002f5800000013f36612266a70af0d80168bdb47c1ec14d2bd520f8cf078cddd37f8250b606f8182800055c1843642a480000005ae000194697500004a06fa000000000099a00043014a49dcd911ba98e5af08e1061b38d8dc00002b9de5134bb80000001b080005be0e24ce63ed45b0001270ae51d017cc14caac1f323a1b345ce00022c58aa079000067853c502289363474e27c00035c4000b7e03d0b1d618c705d0906db460000001a65a065402a496406b40d8251aaa800000017585849ca5f728e27c41543d30e233fdb16482632000400007d0001cd8d0400000000000003d65502a6d110d2a26f0001bb85e128886457c2706373b36118cb556a88998d0c2ec0001660000811316800000015800018ad32ecbf656a7f0eac097186b5b58b01060b4217c13800f669a9801a03884b68bfc582c6d00007c4778a57467a8c40c48d66431a7c954bfc00007180006bc6d108edaae84e64926e98f62770d7b07400015b0002b740f8d1b44ba4f87b2df56d336d8ae66884789200e048580b5800000000055c0000e240005e389d9bda0b72ef2370c8ec981d51d7106eae12ffaa795647920fd029c7c02582132c808ced010872c09afa67c163093ccfc59e17d32a10124d813587c0fcea535619bcd7ec3dd12519a92f46c468412ac01c2e82f296204f682e100a0f065400000022c81ca4660001e54a4840451d2cd53a2a861da0321afc034096284991cd1253180014eace15a923414569e1303b101166b570000c507b8cfb47e0da5c0a0002500cdc49c0d73fb16a9660afa63109d445e51f44d800096aa0a00000a40000a30abac98000baf601223588e9240088600d0686d00019bc89a0541da8fd5a48d932b01c1c000b5100000e45e248f6a5a0403600000000000f9e0000000001668000431aaa10d4000552ad80e10daa5b6aac44728dd6de3141b18e12248252d230bbe2860721968a3968a33204409264da9968ebe09b5a4249426692d6ed1d10658b9251188211ee79425f0000272d3c56bb4b48ec22103b8000cbc4ff3bf01c0adc51b1d716dc000aba629a91ce789100449008958d805988000aaace00003280c12cf30003648064a206722920d988a8000000163000009c2b08
  | 34 => 0x6098129b3c64250895d124e9141d6274c93a68f01bb1bc0902183be0ad19e05d400000008d00003a00000be437600023788f200046d25a1a888c42dc10d11aa6d8374000155c0000340000000a610000dc41d82fc4d5aaec7b000065280000003270000b305f631f128077d36c02367ca5346cc8794091d4d27e6b943e9ca0748c546e122300000ca510adf4e1a6a044818608580005d431147fc3c361409f55ec69d3221818556de553e251800e000400a6fd8ae6fb45ba1c15e8b646f49c58f6a7ab3488f9d8ac78906ca3bc07815600032e5314df919908f0ba0bfa65aaa880005270691f7400000000001e165600014990f52c0593000000000050f411a8552342cb1e0b4a429847100005d40000130ac839d9b8c4d54507801bc000314a7a9268cc43e82c3850665b1f21639b48dc13cd8aa0b908d3230381cac400064dab516ac3330bdb0ed8fa80a6d9a0918e6ab045f9944d50de86980aa925c0b86682e916b40c63599db8f98c09600a0c0f1c5fb000000073c9a4415259d7e0ae9000329062031300024c92580001131a597868d2000000000000000000019dccef460800031edcc0649cb0ac612b26fade580c0274ce800012068e50232c000000000000008b8e085a8251c4d892010834f51542961621154000b4d3dfb01503c0000000000e2861247317603ca282443260cf6e114000062d6d6d7c12d8b9d8fc68d68bad8d4d46c700000014b200026d99804a68776bab67cb427c32caa9a00fc51e00b8000d80c991db9be552000011888c8ad8000445a42c81c78610bb5342349d70a1a901052b384c9b4095803db000172917c00032f80000000005baa274000aff27b00000009ce27580003683610000e056b2da54ab901c8beaf000030f0b0e2632bf993857c0003c08ba8f0486e4d830bd60625726aa93428000058e36f4a0e9a33e49bf88842a21ac0efcc364fe0001bb181c30c1e034643922dd0c8228c2f2a4c64e29f8288b2d5b9a3906941a34f11404acc99629334141764812bb037446054c645a328000b8e6712e30ca0c35
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc01466929c871595430051ca42721c56550c01c47731c8715954300709610721c56550c01078976002159543007181c871dc16550c0186472a06705954300619a08719c16550c01468925c070595430051c245701c16550c0146a929c870595430051ca46721c16550c01c2b741c870595430071260c721c16550c01c6072dc470595430051aa4a711c16550c01472919c470595430070cdd0711c16550c01c53731c4705954300718dc8711c16550c01c60721c470595430070c650711c16550c01c51831c470595430041d25d810816550c0106c97608105954300607dd1831d56090801864822057654c4200607613731d5618c8018688220176550320060de1b815d543d0401924822057550f410060ee18805d543d0401928822017550f410064c204805d543d040182c7620973551410060d1db815cd545048f434965cf715514100607e1d5458c635040182c862097550d410060d21b815d54350401838862017550d410064a208805d54350401930812017550d410060be1d545886250401a2954201621894101c0f261765523250401c295418072581410061a208805d954cc40141d9421773591210060e1c184d4d644840181d84dcf535912101c0f26174553634840121d94e1c6518d210051364c211d95348401469900847654d210051c640211d9534840141d9421f6354d2100558640215d73248565c4471194634c921006191c48654d3248401864822057654f4000615e18815d543cc001944822057550f3000616e1b805d543cc001948822017550f3000654204805d543cc00184c762097454d30006161db805d1534c00121f985906454d302251625974dc1534c00184c862097550d3000615218815d5434c001944822057550d300061621b805d5434c001950812017550d3000613e1d53588624c001a4553205621893001c172617654e424c001c45531847258530006071d98550d414c00121d93e1c65191200050b650201d954480014659108076551200051c644201d9544800141d932177458d2000607dd183d5163480018547160f5458d2001c1725d83d91534800141c9760f6454d2000558644205d74248141c287019464509200061a1c0865514248001835716106519110006165c1831946344001234966154350510004962598550d304400193087551414c1100065421d5350530440019908750d414c110005a42594350530440017119550d414c110004d42615348530440015309755141481103a65821f854852044001a6086e1521481103065821f754852044001c6076dd521481102c69821b6548520440b3c6076d95214811000cb8259844852044001ca076dd12148110007481d4744852044001560975512148110006b021b834852044001b408520d2148110015382597348520440013609854d2148110
  | 1 => 0x1901d0027000005000121ac9c043e0f49881289fc3400000ac0c5c22870001b000003c490112ca46c201090818391f8160d310e4b27841800886d32888240024020cc3718a14764a209602a0000000a85b338003e142b000ae87299cc8c001d004e02002844c00005000006e1f0a46a3f34800bc251a0b8701023974865a431a86c031086466553a18c267a321a060261688c127107001045f27934c20c0003c78003a800de7d3b8742e003d858ec2c001e4a02a000005e00091e0c0a00040012000c120203090111001400091006120300040f010202030700010b00030200030a150f000061660d701c3635500186872a026158d540061aa08709856355001839841c06158d540068a610600806255001a618118020189540051a241631c9605500144d9318072581540060d611711c76454c0186472a06605915300619a08719816454c01855831c460591530069160c610846254c01a6061600211895300519245641c96154c0142d9418472585530061a1ca809c56550c01464925c471595430051c241711c56550
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x260800050c3403890ca9a6490802861a11c086551424800188843b2aa1a8298220009842999550d414c110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x6010872999550d414c110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x6
  | 4 => 0x94e
  | 5 => 0x4
  | 6 => 0x5
  | 7 => 0x98a
  | 8 => 0x98e
  | 9 => 0x3
  | 10 => 0x150a
  | 11 => 0x150e
  | 12 => 0x9ca
  | 13 => 0x9ce
  | 14 => 0x168a
  | 15 => 0x168e
  | 16 => 0xa0a
  | 17 => 0xa0e
  | 18 => 0x180a
  | 19 => 0x180e
  | 20 => 0xb09
  | 21 => 0xb0e
  | 22 => 0x1549
  | 23 => 0x154e
  | 24 => 0xb49
  | 25 => 0xb4e
  | 26 => 0x16c9
  | 27 => 0x16ce
  | 28 => 0xb89
  | 29 => 0xb8e
  | 30 => 0x1849
  | 31 => 0x184e
  | 32 => 0x3c9
  | 33 => 0x3ca
  | 34 => 0x3ce
  | 35 => 0x15ce
  | 36 => 0xcc9
  | 37 => 0xcca
  | 38 => 0xcce
  | 39 => 0x15c9
  | 40 => 0x15ca
  | 41 => 0x1709
  | 42 => 0x170a
  | 43 => 0x170e
  | 44 => 0x409
  | 45 => 0x40a
  | 46 => 0x40e
  | 47 => 0x160e
  | 48 => 0xd09
  | 49 => 0xd0a
  | 50 => 0xd0e
  | 51 => 0x1609
  | 52 => 0x160a
  | 53 => 0x1889
  | 54 => 0x188a
  | 55 => 0x188e
  | 56 => 0x589
  | 57 => 0x58a
  | 58 => 0x58e
  | 59 => 0xe89
  | 60 => 0xe8a
  | 61 => 0xe8e
  | 62 => 0x1789
  | 63 => 0x178a
  | 64 => 0x178e
  | 65 => 0x18c9
  | 66 => 0x18ca
  | 67 => 0x18ce
  | 68 => 0xec9
  | 69 => 0xeca
  | 70 => 0x1049
  | 71 => 0x104a
  | 72 => 0x98956
  | 73 => 0x9c956
  | 74 => 0xb0956
  | 75 => 0xb8956
  | 76 => 0x209
  | 77 => 0x8a
  | 78 => 0x1409
  | 79 => 0x128a
  | 80 => 0x1a49
  | 81 => 0xecd
  | 82 => 0x1449
  | 83 => 0x12ca
  | 84 => 0x104c
  | 85 => 0x1a89
  | 86 => 0x1489
  | 87 => 0x130a
  | 88 => 0x14c9
  | 89 => 0x134a
  | 90 => 0x2c9
  | 91 => 0x150996
  | 92 => 0xb0996
  | 93 => 0x154996
  | 94 => 0xd0996
  | 95 => 0x160996
  | 96 => 0x1649
  | 97 => 0x449
  | 98 => 0xb1516
  | 99 => 0x155516
  | 100 => 0xd1516
  | 101 => 0x161516
  | 102 => 0xe89d6
  | 103 => 0x9ce96
  | 104 => 0x1789d6
  | 105 => 0x9d796
  | 106 => 0xec9d2
  | 107 => 0xe9696
  | 108 => 0x168e96
  | 109 => 0xed692
  | 110 => 0xce
  | 111 => 0x154b16
  | 112 => 0xccb16
  | 113 => 0x15cb16
  | 114 => 0x1a4a
  | 115 => 0x1a8a
  | 116 => 0x164a
  | 117 => 0x44a
  | 118 => 0xcd556
  | 119 => 0x15d556
  | 120 => 0xe8b96
  | 121 => 0xb8e96
  | 122 => 0x18cb96
  | 123 => 0xb98d6
  | 124 => 0x104b91
  | 125 => 0xe9856
  | 126 => 0x184e96
  | 127 => 0x105851
  | 128 => 0x28e
  | 129 => 0xcc3d2
  | 130 => 0xcc3d6
  | 131 => 0x1043d2
  | 132 => 0x1a8c
  | 133 => 0x15ccd6
  | 134 => 0x1715d6
  | 135 => 0xed5d2
  | 136 => 0x1055d2
  | 137 => 0xd0411
  | 138 => 0xd0416
  | 139 => 0xec411
  | 140 => 0x1a4d
  | 141 => 0x160d16
  | 142 => 0x189616
  | 143 => 0xed611
  | 144 => 0x105611
  | 145 => 0x105791
  | 146 => 0xed8d2
  | 147 => 0x12ce
  | 148 => 0x144e
  | 149 => 0x130e
  | 150 => 0x148e
  | 151 => 0xb09895e
  | 152 => 0x14a
  | 153 => 0x40211
  | 154 => 0x41411
  | 155 => 0x40ed1
  | 156 => 0x160ed1
  | 157 => 0x161a51
  | 158 => 0x40cd1
  | 159 => 0x161a91
  | 160 => 0x44411
  | 161 => 0x45611
  | 162 => 0x41651
  | 163 => 0x41a11
  | 164 => 0x40451
  | 165 => 0x164411
  | 166 => 0x165611
  | 167 => 0x45891
  | 168 => 0x99556
  | 169 => 0x983d6
  | 170 => 0x99616
  | 171 => 0x3c092
  | 172 => 0x169796
  | 173 => 0x41611
  | 174 => 0x3d292
  | 175 => 0x15da52
  | 176 => 0x1a95d2
  | 177 => 0x3cd12
  | 178 => 0x443d2
  | 179 => 0x455d2
  | 180 => 0x3d652
  | 181 => 0x3da12
  | 182 => 0x3c452
  | 183 => 0x1643d2
  | 184 => 0x1655d2
  | 185 => 0x45712
  | 186 => 0xb15d6
  | 187 => 0xb0416
  | 188 => 0x3d5d2
  | 189 => 0x1858d6
  | 190 => 0x3c996
  | 191 => 0x3d416
  | 192 => 0x3d456
  | 193 => 0x3d896
  | 194 => 0x24e
  | 195 => 0x171516
  | 196 => 0x170216
  | 197 => 0x170416
  | 198 => 0x41296
  | 199 => 0x41316
  | 200 => 0x40b16
  | 201 => 0x41716
  | 202 => 0x10e
  | 203 => 0x188096
  | 204 => 0x189556
  | 205 => 0x1883d6
  | 206 => 0x178e96
  | 207 => 0x18ce96
  | 208 => 0x18d796
  | 209 => 0x1798d6
  | 210 => 0x1692d6
  | 211 => 0x16d456
  | 212 => 0x3d5d6
  | 213 => 0x3ccd6
  | 214 => 0x170cd6
  | 215 => 0x598d6
  | 216 => 0x181316
  | 217 => 0x185496
  | 218 => 0x41616
  | 219 => 0x40d16
  | 220 => 0x188d16
  | 221 => 0x59796
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 2297
  | 6 => 7156
  | 5 => 3605
  | 4 => 136
  | 3 => 4
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (94169+((h/765+packedAt gbK7 (84989+(h % 765)*12) 12) % 2757)*13) 13
  | 6 => packedAt gbK6 (376878+((h/2385+packedAt gbK6 (343488+(h % 2385)*14) 14) % 12571)*14) 14
  | 5 => packedAt gbK5 (228308+((h/1201+packedAt gbK5 (212695+(h % 1201)*13) 13) % 4327)*13) 13
  | 4 => packedAt gbK4 (9880+((h/45+packedAt gbK4 (9520+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt gbK3 (327+((h/1+packedAt gbK3 (324+(h % 1)*3) 3) % 6)*3) 3
  | 2 => packedAt gbK2 (93+((h/1+packedAt gbK2 (92+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc1f03c1ff81fffffe0ffe00067b91f838fe7c
  | 1 => 0xffe003fe0ffe0f803ff03fff19a4fe38cf338f
  | 2 => 0x7fffc000ffff0003fffc000e1c71fc70fc3f0
  | 3 => 0x7fffffff00000003ffffffffe07e007f003ff
  | 4 => 0x7ffffffffffffffc0000000fff80007fffc00
  | 5 => 0xf80000000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xac0300c0918852a396456a0a020990d818563c
  | 1 => 0x34a0015206aa4b048a510ca608a036284b3285
  | 2 => 0x256d64000b4d62092d69881461461b430dc3d0
  | 3 => 0x8256aaa5a0000012318e3158b607c005b0016a
  | 4 => 0x398d3394c718c5c00000060ddf00006e6a800
  | 5 => 0xc000e03180610860010c2180ffffedb0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaece8feeaec00feeaece8feeaec00feeaece8feeaec00feeaece8feeaec00feeaece8feeaec00feeaece8feeaec00feeaece8feeaec00feeaece8feeaec00, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36987
namespace PEqualNP.Outside.L_meta_36987
open PEqualNP.Outside.L_meta_36987.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 60 := (concat bs0_3_0 bs0_3_32)
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
theorem bs0_4_160 : Interval s0Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 165 := (concat (concat bs0_4_0 (concat bs0_4_32 bs0_4_64)) (concat bs0_4_96 (concat bs0_4_128 bs0_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 50 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 10 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 60 := (concat bs1_3_0 bs1_3_32)
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
theorem bs1_4_128 : Interval s1Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_160 : Interval s1Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 165 := (concat (concat bs1_4_0 (concat bs1_4_32 bs1_4_64)) (concat bs1_4_96 (concat bs1_4_128 bs1_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 50 := (concat bs1_5_0 bs1_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
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
theorem bs3_4_0 : Interval s3Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 2 := bs3_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 2 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 1 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 4 := bgb_3_0
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
theorem bgb_4_128 : Interval gbAtlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 136 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128)))
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
theorem bgb_5_3584 : Interval gbAtlas 5 3584 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3605 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat bgb_5_672 (concat bgb_5_704 bgb_5_736)) (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864))))) (concat (concat (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)))) (concat (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536))) (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)))))) (concat (concat (concat (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat (concat bgb_5_1888 bgb_5_1920) (concat bgb_5_1952 bgb_5_1984))) (concat (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)) (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 bgb_5_2656))))) (concat (concat (concat (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)) (concat (concat bgb_5_2784 bgb_5_2816) (concat bgb_5_2848 bgb_5_2880))) (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104)))) (concat (concat (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200)) (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328))) (concat (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456)) (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 bgb_5_3584)))))))
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
theorem bgb_6_7136 : Interval gbAtlas 6 7136 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7156 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)))))) (concat (concat (concat (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984))) (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)) (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432))) (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 bgb_6_2656))))) (concat (concat (concat (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)))) (concat (concat (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)) (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 bgb_6_3328))) (concat (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)) (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552))))))) (concat (concat (concat (concat (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 bgb_6_3776))) (concat (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)) (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000)))) (concat (concat (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)) (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 bgb_6_4224))) (concat (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320)) (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 bgb_6_4448))))) (concat (concat (concat (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544)) (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 bgb_6_4672))) (concat (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768)) (concat (concat bgb_6_4800 bgb_6_4832) (concat bgb_6_4864 bgb_6_4896)))) (concat (concat (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)) (concat (concat bgb_6_5024 bgb_6_5056) (concat bgb_6_5088 bgb_6_5120))) (concat (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)) (concat (concat bgb_6_5248 bgb_6_5280) (concat bgb_6_5312 bgb_6_5344)))))) (concat (concat (concat (concat (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)) (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568))) (concat (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)) (concat (concat bgb_6_5696 bgb_6_5728) (concat bgb_6_5760 bgb_6_5792)))) (concat (concat (concat bgb_6_5824 (concat bgb_6_5856 bgb_6_5888)) (concat (concat bgb_6_5920 bgb_6_5952) (concat bgb_6_5984 bgb_6_6016))) (concat (concat bgb_6_6048 (concat bgb_6_6080 bgb_6_6112)) (concat (concat bgb_6_6144 bgb_6_6176) (concat bgb_6_6208 bgb_6_6240))))) (concat (concat (concat (concat bgb_6_6272 (concat bgb_6_6304 bgb_6_6336)) (concat (concat bgb_6_6368 bgb_6_6400) (concat bgb_6_6432 bgb_6_6464))) (concat (concat bgb_6_6496 (concat bgb_6_6528 bgb_6_6560)) (concat (concat bgb_6_6592 bgb_6_6624) (concat bgb_6_6656 bgb_6_6688)))) (concat (concat (concat bgb_6_6720 (concat bgb_6_6752 bgb_6_6784)) (concat (concat bgb_6_6816 bgb_6_6848) (concat bgb_6_6880 bgb_6_6912))) (concat (concat bgb_6_6944 (concat bgb_6_6976 bgb_6_7008)) (concat (concat bgb_6_7040 bgb_6_7072) (concat bgb_6_7104 bgb_6_7136))))))))
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
theorem bgb_7_2272 : Interval gbAtlas 7 2272 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2297 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))))) (concat (concat (concat (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248)) (concat (concat bgb_7_1280 bgb_7_1312) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)))) (concat (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536)) (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 (concat bgb_7_1664 bgb_7_1696))))) (concat (concat (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824)) (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 (concat bgb_7_1952 bgb_7_1984)))) (concat (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 bgb_7_2112)) (concat (concat bgb_7_2144 bgb_7_2176) (concat bgb_7_2208 (concat bgb_7_2240 bgb_7_2272)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaece8feeaec00feeaece8feeaec00feeaece8feeaec00feeaece8feeaec00feeaece8feeaec00feeaece8feeaec00feeaece8feeaec00feeaece8feeaec00
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808936 * 2 ^ 32 + 4276808704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36987.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,2]⟩,⟨.or,[0,2]⟩,⟨.and,[4,7]⟩,⟨.or,[3,8]⟩,⟨.or,[1,6]⟩,⟨.and,[5,7]⟩,⟨.or,[9,11]⟩,⟨.or,[0,3]⟩,⟨.and,[8,13]⟩,⟨.or,[10,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4276808704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4276808704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36987

open PEqualNP.Outside.L_meta_36987 in
theorem PEqualNP.Outside.L_meta_36987 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4276808704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4276808704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
