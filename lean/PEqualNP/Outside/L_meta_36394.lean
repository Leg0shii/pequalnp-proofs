import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36394.Model
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


end PEqualNP.Outside.L_meta_36394.Model

namespace PEqualNP.Outside.L_meta_36394
open PEqualNP.Outside.L_meta_36394.Model
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

def SBf (j : Nat) : Nat := [7, 6, 5, 8, 6, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36394

namespace PEqualNP.Outside.L_meta_36394
open PEqualNP.Outside.L_meta_36394.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x16ab081868f300462c005ce1f200c02300215146200915140002f2cc088000010070064002006d2805015724009cf21122c01d0068000524d3221c00586000c04704060000f1e00300ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4d28750c0c0001e001e920000000080000001c66530004800004b80000930002c0000110d800004c80000003b280000000000005e2500000000000000201d0440000240004e5646800fa1b390ac420000000182800000000000138d60030134000000000005700269300000000ba004b020e200178001a4700000b00000000aa000000000001e9bd00003f0012a0000000003b51a89385f0021c02040b164e80000000000000150f8001f0000000000000000000000a9b440006e243420400001e104001d0000118004100000000000084a400000007b2e0008c0045000cc890005400790a0c800521c96c000000000004b00000d8000000000000000000000000000730000034a1308986a0028000009100000006e32800c60000000005a0000000310000116000000124003c040000000144006700000700035000120000000002a00000000a278000000000fcfe290000000001600000000000000000019068840011400000010c061f00274006d010000c00000011e83000004a86000000019000000000118710a2e3b8001e2d0000000002600000000000200000000200018000200000000400000000200000000205008000200000000003000000000000240000010000001008040200008000002004f94e439ea94873e5190e7aa121db94843b6a90873e5310f3ca621eb948439ea9087ad5210e5aa421cf944439ea80873e53d0a7ca3a14f543429eaa4855e5390abaa7214f14d42d7a92853c5150a7ea0a14f95042af298855d5310a7ea9994f15332cf21e659c43ccb3ea9996715332cfa16659d42cca7ca9194f55232aea9c65ad428ca7ea8994f15132cf21a659c434cb5a849967d5132ce2a265cf524cb3e84997390932cea1265cd424cb1a84994f950329eaa0655e530cabca720d754e419f29c839e539063ca720e754e419ea94839f329073a6520cf946419ea84833e531067aa420e7cc841ce990833e511076ca220cf540419f2a6633d54cc7388798db94b31b6a96633e548c67aa918cfd51319e2a2639c434c67ea818cf150319f2a6433d54c86bca790d754f219faa4433c548879a6510cfd51219e2a2433e540867aa810d794c21aea9843cd32086f4a010de540219f29e813d52d033e65a0674cb409f28e813d54902bea6a05714d40cfa9a813c5350338a6a04714d409fa92819f325033a64a04f14540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f20e6996413e548827aa9104f951209eaa241cd324827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | 1 => 0x18800690000092004f238880e0000000700b800009f00
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x3800000292802a655b500a458d30e5b330a98411045d18c002401d08bddb8060001f001800036dc82c38c401254b80000051013000110042000272c01d003c01a01601d400003c01a48b4032000008081144838104240010020005000c100c394d5210f0e63548438798e51d0a1c63543428d98754cca8d62d5332a598754cca8d62153328b195424ca8d6490932a3995424ca8c6550932a3185424ca8f60509329358a539062d6294e41a358a539070e6294e418758a539070d6294e418358a539061f65cca4187d95329070d524c8418718d501068d6210f31c310d52cc68d6210d318798f540c62d62150318e580540c61e63d5221c3d51328861e63d5121c355132087493254021c354932d021e639474093588535022d6214d40a3588535030e6214d4087588535030d6214d4083588535021c65cc94087195325022d6215330a3588438c21d6510c30a3588430c30c4354830c510d510c30d544cb208718d548821c63551208d185544830d544c9208798f54c421c6355210
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x120080c428000180e242c0a82b8cc6a9087219c6655093281ae431aa020c0d7298f5448606b94c728e81415c84354430818ecaa26490504715513248206b94c7aa621035c86355210
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
  | 4 => packedAt s0K4 (4950+((h/55+packedAt s0K4 (4455+(h % 55)*9) 9) % 381)*9) 9
  | 3 => packedAt s0K3 (2420+((h/20+packedAt s0K3 (2280+(h % 20)*7) 7) % 88)*7) 7
  | 2 => packedAt s0K2 (502+((h/3+packedAt s0K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 2 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 3 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 4 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x14000408402040004402404802504088045045
  | 2 => 0x212108848148040a0a20841220849414312512
  | 3 => 0x421251102a9220d4a1112a8554092941828a28
  | 4 => 0xb556225281aa96733542207992c0c45d80f80
  | 5 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36394
namespace PEqualNP.Outside.L_meta_36394
open PEqualNP.Outside.L_meta_36394.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x8ee21ec21
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (34+((h/1+packedAt s1K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffe07ffff083fc3fc3fffe1fffe0113f3fc
  | 2 => 0xf07c3ff83e1fffc3fc3fc381fe1c0ffeeccccf
  | 3 => 0xff803fffc01ffffc003ffc01ffe00fff0f0f0f
  | 4 => 0x3fffffe00fffffc00001fffff003f00ff0
  | 5 => 0xffffc00000000ffffffffffe00000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x6108023084001004404c048c6024621801515c
  | 2 => 0xa5104451902a0141c4144114a208a4a864c4c5
  | 3 => 0x422aa8a20d548a9c222aa829554149530b0b0a
  | 4 => 0x8a5331052906aceaaa82204199938063b00ea0
  | 5 => 0xc6221c63198cf333333327011020183dea000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36394
namespace PEqualNP.Outside.L_meta_36394
open PEqualNP.Outside.L_meta_36394.Model
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
  | 0 => 0xffffc0ff87f843f87f87fff87f07f8093f73c
  | 1 => 0xf0787ff0ff87ffc3f87f8703f87f83ff6cc9cf
  | 3 => 0xff807fff0007fffc007ff803ff8003ff8f0e0f
  | 4 => 0x7ffffff807ffff800003fffffc01f00ff0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x6110046210800804809809198091188c01531c
  | 1 => 0x250088a2400a0081882882288825092424c145
  | 3 => 0xc23551443555455c44555053550232598b0e0a
  | 4 => 0x8a466208a441566a55044082664a6011d00ca0
  | 5 => 0xc64438cc66667b3666664e0440c4061fea000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeeecc00eeeeeeaaeeeecc00eeeeeeaaeeeecc00eeeeeeaaeeeecc00eeeeeeaaeeeecc00eeeeeeaaeeeecc00eeeeeeaaeeeecc00eeeeeeaaeeeecc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36394
namespace PEqualNP.Outside.L_meta_36394
open PEqualNP.Outside.L_meta_36394.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d02fca3a05f54740beaa4817e53902faa7206f90e40de21c817e52902faa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c52502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881bf411037a82205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c617e528c2faa5185f94630bea8c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930bfa8a617c514c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83dc43907b08720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51883eca3105d94620bea8c41f551882eaa3105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea6905f94d20bea9a417c53483dc84907b50920f719241ed32482fea2905f14520f710a41ec21483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb90e21f421c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10f7294216e52842faa5087b54a10b6a94217c52842faa3085f94210fda0421f840843f461087e4c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443ec62887d4c510fb90a21f421443f680887e10110fd18221f930443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc5150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885bf4310b7a86215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbde85197b10a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde84997b10932f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120fe94241bd284837d50907f2a120de54241bfa9a837c535077e86a0ef50d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498fbd4931b7a92637c524c7d8a498db14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831f7290636e520c6faa418fb54831b6a90637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f719643ed32c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f719243ed32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410fbd0821f621043ef32087d86410df94421fb98843f431087de4210fd88421f690
  | 2 => 0x5e4028902e6648c287c17c000001a7000000de8004069b4141d0000000000000007952705a4569a49c0f733a9492c0af2fa2e06922749a6b9040ff31415ce709b10c63cda8e31f666009a4c022870000000048988ea490643a83d1831b21a516145138530bb25d000001359c10007691d9b245e18c790001c8684bf8001788152200046e494bf16b0006444f8003d4238000122a866c000da01400050153058000639e02ce9789c9f22da444000551e00005b800000000000000000011e8001188d4001744340003618c20457c7e8e949e3c4238000000002c00001a998000004ec6dccc9243ea9cc5719f0860000000036229c0000013a7ac001bf0e698c4408f286328358d72c849c509cc42a0f50505d096484000a94701912a12b4746f8531d8358671351a24b871cca1d73a43b4001c847c7a46f25a29e65812a640483085d0162a4770fd0cc2382950b8cf2104511886d1048fcf790e3947d90a0001f84d41e17c07252449a4323e9a1171d40000011e0773460013826f35221d1c8bb43642c6991e0fc7a06413022e9d4f82511c2654240001ca504130dd2ae4fc00000196565190d01c06e47d0302123249486e3aa8340d03a45a0dcb906535a1d90806a3fa000000623200000000012a4648b1e10026d8e28ef1029880581d1461d0148720004889a000000620f18002e0128bc0000007b1371fe172928078001d63140024b4ce500a80cd0004bc280004b2000900000000000010a0000000015b06a618100003b20009693a3ee72cf880015000067027000000c69652ee460a7123000000c71fb4ae984270bf0fe62caf1a82ea1a1391b33786bd210a20820212f87b3ac41c1102301c91d091692aa1081080426465c4289628e0f87624626e6112082d3be9d03c8d4294718fca0000000112a0213c22c000750007905513c1b01347702b25c030050100804c09050020000a01004014100080000005010010000400403038020300101c0709008020060180e0140f05c000401a000000041b020030004802c0307812000000080100001038000000902c0000c310041004c0203c0507c0a0480504c0003c0307c1502818070010000006c00020000180007800004120580502c030000500c07020010000f004010040201000000050100303c060d003000030040801c010c4210080b01c0001c380040700022038110202b00037080090a0220040501c090041600011004000540000806008020000415411020120002e0040801813000090440c0502b03c0a01c0b000070901f0000300c00028040200904c030200a02c28bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521fb94a43b7294877d5290fdaa521db54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877
  | 3 => 0x20100013114800106371021bb4506e1389c02c0414ad00022a6a8b30004161803c099300000fc1f40123d4fe1c90e2888f30512f45887f20c11217c29a6008a5c4491003a63983314227c5a00d8003da0001f8f81084980c8141865a89e80043e698000150a805ce78000b6604b78ad000585360b24ee000940001aa0000000000081c00000000000000000000000015141c5ecdd00039a778290074662cc1d81f07088c710670620cc809c333c2b01501005c9006f87d1e60bd150b53e688104a484424408680000c34400000290290002561d08784c2304aa46c4a25043a110a58914b66d073a1621e8647a10c384608ae01c2b0788d290648a119031db326680999e7134844d20f6276510ae9033fe468b18b62621c0600491621010c1464266c01a0c646c2f5299122d82d07c9d100000d07a240b8234ab14d0b20011a05e25844d3296e0184101b0563561bc9b0d61882005599a00025cc38003ba2c06088a3dc13c0f12a1b6624e2061030
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x951cc39943d0330b658c40cc39a43103309b988548c26d62152309d984548c27561152308fd91528c23c6454a308f992518c23d64946308f992544c27b60551308f994544c31d6315130c7152434c25c6550d30ce153304c26e62d50309b58b540c27661d50309d587540c23d6595030ce181540c23e64150309798c540c26e62150309b588540c27661150309d584540c32e5494830cb552520c32e5454830cb551520c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c33954d0030dc547400c2796510030dc544400c31d54cc030dc546300c25f654c030c7551300c27b654c030ae191300c371514c0309798f54c825d63d53208f99353c823d64d4f208f99253c823d6494f20b918532c82ad6408720b358c21c827661d52209d587548825e63152209758c548827661152209d584548827661d4e209d587538823e6414e208f59053882766114e209d584538823e64946208f59251883366494620cd59251883726094620d9947208823e64951208f994544832d62151208f992534823d6494d208fd91534823c6454d209dd8553482746154d20cb152424826c6550920cb152324826c654c920cb151324834c534c920b9185324832c5488520ab590214832c5408520b358c21482ea6008520b9986204825e63150209758c540826e62150209d984540827561150208f990530823d6414c209b98853082766114c209d584530826f65480209ed95200833661953108f99353c423d64d4f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b108f99052c423d6414b109798c52c425d6314b10cd95141c42e46250710b918931c42b56408710b558c21c426e62d52109b58b548425e63152109758c548426e62152109b588548426e62d4e109b58b538423e6414e108f590538426e6214e109b588538436a6094a10b658c40842e96210210ae19130842b86448210da949208436652c4210ae993108425f63551109718d544426f62551109b189544423f6454d108f191534426f6254d109b189534423e6414d108f590534426e6214d109b588534423f64549108f191524425f63549109718d52442f260905109d19541442e462505109d19531442e4624c5109d99721442b56408510b558c21442f260085109e99740442d96310110ba58840442f26110110ec5044044278654c110ae19130442f261881109e19520442b86448110f808520442ba64c4110b998a104427a60d50109798c540425d63150109b988540426d62150109d984540423e6414c108f590530426e6214c109b58853042766114c109e980530427661d48108f990520423d64148109798c520425d63148109e980520423e64944108f592510426e62940109b58a500427965840109dd95100427b6544010
  | 1 => 0xca3d64145329e980514ca796014532cd990514cb356414532d9d08514cb644214532d9cc8514cb726014532dc580514ca6e62d50329d984540ca7561150329e980540ca7960150328f992530ca3d6494c3297d95320ca6f654c832b9185320ca3f64540328f191500ca6e6294f419b58a53d06b86050f419b98a509066d6294241da98a50907696294241ced06509071c5350d41ae181435072f4314941cb50c525072c52d0941ae982415063f65504419dd95411066e62d53319b58b54cc67b60553319e18154cc6d4614cb318fd9150cc63c64543319e983548c67960d52319bd89548c66c62552319b98a508c66d62942319b98a544c66d62951319bd89544c66c62551319ed81544c6786055131d314b324c76452cc5319b98b540c66d62d50319e983540c67960d50318f596540c63e64150319b988540c66d62150319e980540c6796015031cb952520c72d5494831cb951520c72d5454831d9185520c74d52cc43197d95310c74d524c4319dd95310c6e4624c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c7695254031dc8c5500c77131540318f99253c863d6494f21b918532c87c532cc721b958831c86f1600c7218fd9150c863c64543219e983548867960d52218f990538863d6414e219e98053886796014e21ab993328865e63951219758e544866f62551218f992534863d6494d219bd8953486776154d219b996324866c654c921b9185324865e63d50219758f540867a60d50219e583540863d6595021cb189540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530874c6254c21d5185530863e6414c218f590530865e6314c219b988530867a6014c219e580530872d54d0821d354f420866d6510821d354c42086e561108219b59732086ae64cc821d354f320866d650c821d354c320875553cc421f1ccb3108675650c421bc580310874d53c84219bd95210874d53484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500866e6294f409b58a53d02b86050f409bd8951d026c6254740ab98a43902ac62506408f99743502b86050d40d6181531023d6590c40c754e43102ae6290c40c754c431034e5394840d354e521034e5354840d354d521031d5390840cb54a421031d5310840ae58042103565394440d554e51103665294440d954a51103726094440d594d51103555354440d994951103655254440c754f411032d52d0440c754d41102ac6250440cb54941103365150440c754f401023f6550040c754d401027b65500409b98b54cc26d62d5330b618143cc2776154b309d18552cc26f62547309b18
  | 2 => 0xa86000485e0b27835ad6000bba587f946550a6e51ae5b01600242498380026800000ba0a036b4a4b8006180018940000007892a00000d09a04fa6e0026600118d837e453283226ab41b0c22780d156dd20aa0b02191bce110a58984b210035ac66e276cb8001c800112a241800522ec00022d4ac022334adb06c61aa003b02f3962e800b580000000b30c400350b7a62641e400152d5a8ed7a4c530000024600000b987adc3262431a4731e5bb76391e8cf800880f80022cb61d07e800000000000000000c909800000a48d23a800d100037994b89801a2360036e0000000000a4094e7132cf234309340193a168f0a6a28ea0e6c8ad2061b29f1381837c31a2e0fb6c5c28a9215a73800b280435000eaaa6aa3a0482bad5000d71ba2280000000002e440800000008aa50bf280208000009e1a8002e3620008cbe800c81300001000000af0b4492dc6997c0016400096049c223b1c982888c800000008687c3cb82a102859800bab86b3884e602ceb00084b384219c62b9a718007505c00104859ea33af2e406e0682e0281ca521c8391e749ec529d62f8000007e3fa8c85030160dc002d46da4a63252488523eb803b274d02b8001f25da989ea64331c81b0004a0003d97a38968950d8e4ae0430000023c563666fb64001c0768742b1ca003a6002c4469a4002c2002f0118eea93045710e97b2ccdabe0019e83238030e80029c889368799a1538a0f2f8c31a8090788015e19826970fc902960ab46001f88c1f4000144b37226800620002c020d20008f856e33306884a2ab3ae217463a049c8c0328a400316002b0a81929b27e21832abada508d0a79109136a7b808c384c8223ad3870543a2de1f06b2265fb7a3816080ab2014090480002c0400006008070081d000020081106011014010180f02c06008010080005800000160000c0e801008020080905800000010b843000040001e01c040780100c0300000024290500106c0d0041c0040a1bc000040501c09018000440000000018002600701801000020ac04000100000200807000000280000c020ec02018000200301001074000040300019014000000b01463008000200300c0000033004010040200000008060f0050001300c000a8150b4070080808406000001881103a7a60947439e58251d0f2f4394a43ab98a4350e6e62141439b5885050e7661141439d5845050f3a4314143da9885050f696214143dc9845050f7161141438fd954310eb86050c4397d954310e6f62544439b1895110e7a60947429e58251d0b1e5350e42ae1814390a7661942429d5865090ab86050c428fd954210a6f65508429e983548ca7960d5232ab993328ca7661942329d586508ca7661951329d586544ca7761551329d185544ca7b60551329e181544ca6e65d0932b398f424caae64cc9328f990514
  | 3 => 0x95ba40daac1d98253a18840505aa06272f6aa89203afe289962d8f42032abd03aeba24662b4731b4cc84e2b9d844b1477b12c0310009c4da040178425ca707db0a7981e4593c93b4ce79dc969fc2a144e3
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xe2867044933183d50000056c001a0420003540000110c000901764840000058b0070030e2020000854a9ca4314143cc2c4b08a0a1e1a531814390aa339e8428a65499d33214532c62c8b00a2996185318143506943828629283581c93154031aa2e030aa610e45535844208707322a799043515d732cc421aa2e2302a62060d5398a431030ca9ac0210818354c6250440932ed218819863064545300c3122a0c2992419114c614c92085aec2a0429060c5458c2148348b1a8220221681c94110110d42c4a0880885a17408520443503204290221705cc2148110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x14000c81631c941101108a1871902148110c80645cc2148110
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 5 => packedAt s3K5 (19164+((h/210+packedAt s3K5 (17064+(h % 210)*10) 10) % 759)*11) 11
  | 4 => packedAt s3K4 (19544+((h/157+packedAt s3K4 (17974+(h % 157)*10) 10) % 568)*10) 10
  | 3 => packedAt s3K3 (1475+((h/9+packedAt s3K3 (1421+(h % 9)*6) 6) % 45)*6) 6
  | 2 => packedAt s3K2 (183+((h/1+packedAt s3K2 (180+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfe0ffff03fe3f80f1c7f1fffc7e0ff0013f73c
  | 1 => 0x1ff078ffc3fc7ff01f8fe381f8ff07fc6cc9cf
  | 2 => 0x1fff80fffc007fffe00ffc01ff0007ff8f0e0f
  | 4 => 0xe00000ffffff80fffff00001fffff803f00ff0
  | 5 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc2611011884401010413048cc122311801531c
  | 1 => 0x442501228900a0200c852114484a124824c145
  | 2 => 0x88c2324510c95057200a4829920464b18b0e0a
  | 4 => 0x18a44882280129a512000412494c022d00ca0
  | 5 => 0x110c600e331264ec9a4c9270001880c37ea000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefeeaeaeeeec0c0fefeeaeaeeeec0c0fefeeaeaeeeec0c0fefeeaeaeeeec0c0fefeeaeaeeeec0c0fefeeaeaeeeec0c0fefeeaeaeeeec0c0fefeeaeaeeeec0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36394
namespace PEqualNP.Outside.L_meta_36394
open PEqualNP.Outside.L_meta_36394.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x486200000000fb40be40bc40f840b840
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xc041900814013a5090334a6206654c40d529081a95210364a2206c54440
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x143095354840c454d51103215254440
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 5
  | 3 => 7
  | 2 => 3
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | 2 => packedAt s4K2 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (84+((h/1+packedAt s4K4 (80+(h % 1)*4) 4) % 13)*4) 4
  | 3 => packedAt s4K3 (197+((h/2+packedAt s4K3 (189+(h % 2)*4) 4) % 10)*4) 4
  | 2 => packedAt s4K2 (116+((h/1+packedAt s4K2 (114+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe1ffff01e3c781e3c7f1fffe383838033fccc
  | 1 => 0x1fe0f8ffe03fffe03f8fe380fc03fffcccc0ff
  | 2 => 0x1fff00ffffc07fffc00ffc00fffc03ff0f0f0f
  | 3 => 0xe00000ffffff80fffff00000fffffc03f00ff0
  | 5 => 0xffffff00000000ffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xc2c63011c44891060c13048ee0989898115ccc
  | 1 => 0x444a012244902020148521122401292844c055
  | 2 => 0x888052448809404a400a4824492802510b050a
  | 3 => 0x114a48910201294a920004892525002b00aa0
  | 5 => 0x1118c00e193264f9324c927000606063eea000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafcc0fcc0feeafeeafcc0fcc0feeafeeafcc0fcc0feeafeeafcc0fcc0feeafeeafcc0fcc0feeafeeafcc0fcc0feeafeeafcc0fcc0feeafeeafcc0fcc0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36394
namespace PEqualNP.Outside.L_meta_36394
open PEqualNP.Outside.L_meta_36394.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x560c000002150b4a1c0142e702801840026008d3933a00a893c60da024451022c047a43284680003802800000043e69486140021530820cc085100001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fb40fe40fd40fc40f840ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fa10fd10f910fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x30040000003700510028001d00551a3d09030e000000000a0000075a3c360000004200264145182c32333e4b2d4e3b19590f103a1125273f4d002a124a2e0b491f470c0100002054231b39382b52401c00133505161e0631000017084f2948570000022244340056000046145358004c000d002415502f43210608e4e12080800102080030408005000400100050460234205096e52d0edaa5a1de94243bca84877b5050ef0a0a1d794f42aea9e857a5090af2a1215ed4142bc282853e540ca7aa819734c832bb2886575510caf4a0195e54032bd284837950906f6a0a0de14141af298835d53106dca420db54841bd280837950106f4a118de54231b7a92636c524c67ca818cf55031b7290636d520c6f4a018de54031bd284437950886bea690d714d219f2a0433d54086bca610d754c21bd280437950086f2a3a05e94240af298815d53102dca4205b54840bb288817551102f4a8206e95040ed29881d9531037686206e50c40f529081e9521037684206e50840f9288817951103e2a2205c54440dd20881b8411027ca9984f553309f2a6413d54c82f4a9085e15210bca8c213f5444278a8886ed5110bd2a221785444370a8884e15110f9a8a21f241443e282885e94010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x49a400000786b0010200c030a94000b8ea1829c216800922980382000000074532544328e191508c6386454221aa58b43103495354840a658f42103525354440d454d51103625254440d854951103334354440cc50d51103334254440cc50951103315190440a658c41102a962104408e992544431a6315110c658c544432a6215110ca58854443316115110cc15241442706550510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x410000c081485cb4354440a22e7a12a220609635885444308b1ac22a221885896115110
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
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 58)*7) 7
  | 4 => packedAt s5K4 (2667+((h/30+packedAt s5K4 (2457+(h % 30)*7) 7) % 121)*8) 8
  | 3 => packedAt s5K3 (998+((h/8+packedAt s5K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (249+((h/1+packedAt s5K2 (245+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1fe1ff1fc0f1c7078e3f1f87fc7070e0373ccc
  | 1 => 0xe1fe1fe3ff01fff80fc7e3f81f807ffe49c0ff
  | 2 => 0x1ffe003fffe07fff007fc001fff80ff8e0f0f
  | 3 => 0xfe000003fffff81ffff800001fffff01f00ff0
  | 4 => 0xfffffffc0000001fffffffffe0000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xcc2cc6204e228a21860b0491dc13162c131ccc
  | 1 => 0x44444004822400000241211044802244014055
  | 2 => 0x18880a491440940a90064822892500988e050a
  | 3 => 0x80119492288102552c900045124a4c01700aa0
  | 4 => 0x1111180030c9249e49249266000c0811eca000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeefcc0feeefcc0feeefcc0feeefcc0feeefcc0feeefcc0feeefcc0feeefcc0feeefcc0feeefcc0feeefcc0feeefcc0feeefcc0feeefcc0feeefcc0feeefcc0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36394
namespace PEqualNP.Outside.L_meta_36394
open PEqualNP.Outside.L_meta_36394.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5001fe54007f55007fc54017fd4c05fe53017f54c05fc53017fd0c05fe43017f50c05fc4301ffd4801fe52007f54807fc52007fd0801fe42007f50801fc42017fcc805fe32017f4c805fc3201ffd4401fe51007f54407fc51007fd0401fe41007f50401fc41017fcc405fe31017f4c405fc31007fc8401fe21007f48401fc2101ffd4003fe50007f54003fc50007fd0003fe40007f50003fc40017fcc003fe30017f4c003fc30007fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24000fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007fe1048003fd0824001ff04120027fecb88012ff65c4009ff32e2003bf99710026fccb8800e7e65c4009feb2e2000bf59710026facb880027d65c4009fe32e2004bf19710027fec988012ff64c4009ff3262007bf99310027fac988002fd64c4009fe3262004bf1931004ffea988003fe54c4001feaa62009ff15310027fec788012ff63c4009ff31e2002bf98f10027fac788022fd63c4009fe31e2004bf18f10047fea788023fe53c4011fea9e2008ff14f10047fe8788023fe43c4011fea1e2008ff10f10027fec588012ff62c4009ff3162000bf98b10027fac588002fd62c4009fe3162004bf18b1004ffea588003fe52c4001fea962009ff14b10007fe8588003fe42c4001fea162000ff10b10047fe6588023fe32c4011fe9962008ff0cb1000dfcc388013ff51c4009ff28e2004fd94710027faa388003f551c4009fe28e2004ffd0710027fc8388013f641c4009fea0e2000fd50710027f88388013ff31c4009ff18e2004ff4c710027f86388013ff21c4009ff10e2004ff48710027f84388006fd60c4003ffa862001ff9431000ffaa188007fc50c4003ffa062001ff9031000ffa8188007fc40c4003ff9862001ff8c31000ffa6188007fc30c4003ff9062001ff8831000ffa4188007fc20c4003ff0862001fd8431000ff42188007fc10c4003fa0862000ffd9510005feca8801bfe65440077f32a2000ff59510005faca8801bfc65440077e32a2000ffd9110005fec888003fe644400f7f3222000ff59110005fac888003fc644400f7e3222006ffd5110007fca888003fd544400dfe2a22005ffd8d1002dfec688017fe63440057f31a2005ff58d1002dfac688017fc63440057e31a2005ffd4d1002ffca688017fd534400bfe29a2005ffd0d1002ffc8688017fd434400bfe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e3122006ffd4910007fca488003fd524400dfe2922000ffd0910007fc8488003fd4244001fe2122005ffcc91002ffc6488017fd324400bfe1922001bfd8510037fea288013fe5144001fb28a2000ff54510007eaa288013fc5144001ffa0a2004ff90510007ec8288003fd4144001faa0a2004ff1051002ffe6288013fe314400bfe98a2004ff0c510007fe4288013fe2144001fe90a2004ff0851000dfec088007ff504400dfda822001ff9411000ffaa088007fc5044003fc2822001ffd011000ffc8088007fa4044003fea022000fe5011000ff88088007ff3044003ff1822001fe8c11000ffa6088017f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044009fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fe4150001fea0a8007ff1054007ffe62a003ffe315001ffe98a800fff0c540007fe42a0003fe2150001fe90a8000ff0854000dfec0a0007ff5050003ff2828001ff5414000ff8a0a0007ff405000ffda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffe60a0007fe3050003fe9828001ff0c14000ffc40a0007fc2050003ff0828001fe8414000ff820a0033ff65c80017fb2e400eff9972001dfccb90003fd65c80017eb2e400cff1972001df8cb90033ff64c80017fb264000ff9932003dfcc990003fd64c80017eb26400cff1932003df8c99003bff54c8001ff2a64000ff55320077f8a990033ff63c801b7fb1e400dff98f20015fcc790037fd63c801b7eb1e400cff18f20015f8c790037ff53c801bff29e400dff54f2006ff8a790037ff43c801bff21e400dff50f2006ff88790006fe62c801dffa96400cff94b20007dca590003fd52c8001f6a96400cff14b20007fe8590033fe42c8001f72164000ff50b20007da8590033fc42c801bff996400cff8cb2006ffa6590033fc32c8019ffb0e4000ff98720025fcc390003fd61c80017eb0e400cff18720077fea390003fe51c8001fea8e400eff14720007fe8390003fe41c8001fea0e4000ff1072006ffe6390037fe31c801bfe98e400dff0c720067fe4390003fe21c8001fe90e400cff0872000dfac190007ff50c8003ff2864001ff5432000ff8a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1864001ff4c32000ff86190007fe20c8003f71064001fe8832000ff84190007ec20c8003ff0864001ff04320007feca90002ff6548001bfb2a40009fd952005ffcca9000efe6548001feb2a4000bf5952005ff8ca9000efc6548001be32a40039f19520007fec890002ff6448001ff3224007bf99120007fac890002fd6448001fe3224007bf1912005ffea890003fe5448001feaa2400bff15120057fec69002aff6348015ff31a4002bf98d20057fac69002afd6348015fe31a4002bf18d20057fea69002bfe5348015fea9a400aff14d20057fe869002bfe4348015fea1a400aff10d2000dfec49002fff5248001ff2924000fb94920007faa490003ed5248017fe2924000ffd0920007fc8490003ee4248001fea124000fb50920007f8849002bff3248015ff192400aff4c920057f86490003ff61480017fb0a4000ff98520007fac290003fc61480097e30a400bffd4520007fca290003fd5148017fe28a4000ffd0520007fc8290003fd4148001fe20a400affcc520057fc629002bfd3148015fe18a4000ffc8520007fc4290003fd2148001fe10a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fd1824001ff4c120057f26090007fc3048003ff9
  | 2 => 0x5001ffea6a800ffe5354007fea9aa003ff14d5009ffe86a804ffe4354027fea1aa013ff10d50007fec4a8002ff6254001ff312a000ff58950007f8c4a8002fc6254007ffa92a003ff9495001ffaa4a800ffc5254001ffa12a000ff90950007fa84a8003fc4254027ff992a013ff8c95009ffa64a804ffc3254001ffb0aa000bfd8550007fcc2a8003fd6154001fe30aa004bf1855001ffea2a800ffe5154007fea8aa003ff14550007fe82a8003fe4154001fea0aa000ff1055009ffe62a804ffe3154027fe98aa013ff0c550007fe42a8003fe2154001fe90aa000ff0855000dfec0a8007ff5054007fda82a001ff9415000efca0a8007fc5054003be282a001fe1415000ffc80a8007fc4054003ff982a001ff8c15000ffa60a8007fc3054003ff102a001ff0815000ffc20a8007fc105400fffb2e8007bfd974003ffccba000efe65d000ffeb2e8000bf5974003ff8cba001efc65d00037f3268007ffd534003ffca9a001fbe54d000ffeaa68000ef5534003ff8a9a001fff63d000f7fb1e8007ff98f40015fcc7a001ffd63d00257eb1e8007ff18f40015f8c7a004bff53d0025ff29e8012ff54f40097f8a7a001fff43d000fff21e8007ff50f4003ff887a001fff62d000fff3168000bf98b4003ffac5a0002fd62d000ffe3168011ffd4b40007fca5a0003fd52d0023fe2968007ffd0b4003ffc85a001ffd42d000ffe2168012ffccb40097fc65a004bfd32d0025fe1968007ffd874003ffcc3a0012fe61d000ffeb0e8000bf5874003ff8c3a0047ff51d0001ff28e8000ff5474008ff8a3a001fff41d000fff20e8007ff5074003ff883a004bff31d0025ff18e8012ff4c740097f863a0003ff21d0001ff10e8000ff48740007f843a0006fd60d0003ffa868011fed434000ffca1a0007fd50d0003fe2868001fe1434000ffc81a0007be40d0003fd2068001ff1034000f7881a0007ff30d0003ff1868001ff4c34000ff861a0007fe20d0003fe1068001ff8434000ff821a0003ff65500017fb2a8000dfd9540004fecaa0043fe65500077f32a8000ff59540005facaa0043fc65500077e32a8000df1954001cf8caa0006ff6450021ffaa28007ff951400077ca8a0003fd5450001deaa28007ff1514007ffec6a003eff635001fff31a8002bf98d4007ffac6a003efd635001ffe31a8002bf18d4007ffea6a003ffe535001ffea9a800fff14d4003ffe86a003ffe435001ffea1a8007ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0002fc6250021ffa928000ff94940007faa4a0043fc525000fffa128000ff90940007fa84a001ffc425001fff992800fff8c94007ffa64a003ffc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8004bf18540087fea2a0003fe5150001fea8a8010ff1454003ffe82a000
  | 3 => 0xf0844204ff04221007feca90802ff6548435ff32a4203bf99521007faca90802fd6548435fe32a4203bf19521007fec890802ff6448401ff3224207bf99121007fac890802fd6448401fe3224207bf191210d7fea890803fe5448401feaa2421aff151210cffec690866ff6348401efb1a4200b7d8d210cffcc69080afe6348433feb1a4219bf58d210cff8c69080afc6348433ee31a4202b718d210cffea690867fe5348433fea9a4219ff14d210cffe8690867fe4348433fea1a4219ff10d210d7fea490803fe5248401fea92421aff14921007fe8490803fe4248401f72124200ff50921007da8490803fc4248433ff9924219ff8c9210cfdc6490867fd3248433f69924219ff0c9210d7fea290813fe5148401fea8a4204ff14521007fe8290813fe4148401fea0a4204ff105210cffe6290813fe3148433fb18a4219ff4c5210cfea6290813fc3148401ff90a4200fdc8521027fc4290813ee2148401ffb024200bfd81210c7fcc090806fe6048401feb024218ff1812100df8c09086bff5048431ff2824218ff141210c7fc8090863fc4048433ff9824218ff8c1210cffa6090863fc3048431ff1024218ff081210c7fc2090813fc1048409ffb284204bfd9421027fcca1080efe6508409bf32842039f99421027faca10802fd6508409beb2842009f59421027f8ca10812fc6508409ffb204204bfd9021027fcc81081efe6408409df3204200af99021027fac810802fd6408409deb204200af59021027f8c810812fc640842dffaa04200ff95021007faa81085bfc5408409ffb184204bfd8c21027fcc61080afe6308409ef3184202b798c21027fac610856fd6308409eeb184200b758c21027f8c610812fc630842bffa984215ff94c210affaa610857fc530842bffa184215ff90c210affa8610857fc430842f7f3104216ffd4821067fca410803fd5208419fe2904200ffd0821067fc8410803fd4208419fe2104215ffcc821067fc6410857fd3208419fe1904204bf98421027fea210813fe5108409fea884204ff14421027fe8210813fe4108409fea084204ff10421027fe6210813fe3108409fe9884204ff0c421027fe4210813ef2108409ff1084204fd88421027fa4210813ed2108401fa9084204ffd8021027fcc010806fe6008409fd3004201be98021027fac010802fd6008409fcb004200be58021027f8c010806fc600842dffa804214ff940210a7f8a010853fe4008429fe2004215ffcc0210a7fc6010857fd3008429fe1804214ff88021067f84010813fe1008409fe0804201bfd9550007fec8a8002ff6454001ff322a000ff59150007f8c8a801efc6454007ffaa2a003dfd515001ffca8a800ffd5454001beaa2a003ff1515009ffec6a804eff6354027ff31aa002bf98d5009ffac6a804efd6354027fe31aa002bf18d
  | 4 => 0x88bff5210401ff2908200ff54841117f8a42081fff421040fff2108207ff5084103ff88420887ff3210443ff1908221ff4c84110ff86420812fe6110409ffa888204ff94441027faa220813fc5110409ffa088204efd0441027fc8220813f64110409fea088204ef5044103fea8220813ff3110409ff1888204ff4c441027f86220813ff6010409ff3008201bf98041027f4c020806fa6010409feb008200bf58041027f2c020802f96010409fe3008201bf18041117fea020883fe5010441fe2808207ff9004103ff88020887ff3010441ff1808221ff4c041107f86020883fe2010441fe1008204ff84041027f82020833ff65c84017fb2e421fff9972101dfccb90803fd65c84017eb2e420cff1972101df8cb90833ff64c84017fb264200ff9932103dfcc990803fd64c84017eb26420cff1932103df8c99087fff54c8401ff2a64200ff553210fff8a990833ff63c842f7fb1e4217ff98f21015fcc79085ffd63c842f7eb1e420cff18f21015f8c79085fff53c842fff29e4217ff54f210bff8a79085fff43c842fff21e4217ff50f210bff8879087fff52c8419ff2964200ff54b21067f8a590803ff42c8419ff2164200fb90b21007fa8590803ed42c8419fe2164217ffccb21067fc659085fee32c842ffe9964217fb4cb21067f8659087fff51c8409ff28e4200ff54721027f8a390803ff41c8409ff20e4200ff50721027f8839085fff31c8409ff18e4217ff4c721027f86390833ff60c843dff3064201bf98321007fac190802fd60c8419fe3064201bf183210fffea19087bfe50c843dfe286421eff903210f7f8819085fff30c843dff1864217ff4c3210f7f8619087bfe20c8419fe106421eff84321027f82190813ff65884097fb2c4204ff9962101dfccb10813fd65884017eb2c4204ff19621025f8cb10813ff64884097fb244204ff9922103dfcc910813fd64884017eb244204ff19221025f8c910877ff5488401ff2a44200ff552210eff8a910813ff63884097fb1c4204ff98e21015fcc710813fd63884397eb1c4204ff18e21025f8c710873ff5388439ff29c421cff54e210e7f8a710873ff4388439ff21c421cff50e210e7f88710866fd628843bffa944200ff94a21007faa510877fc5288401ffa144200ff90a21007fa8510803fc4288439ff994421cff8ca210e7fa6510873fc32884097f30c4204ffd4621027fca310813fd5188409fe28c4204ffd0621027fc8310813fd4188409fe20c4204ffcc621027fc6310813f63188409fe98c421cfd4c621027f86310813ff2188409f790c4200fdc8621027fec110813fe60884037f3044204ff58221005fac110813fc60884037e304421dffd42210dffca11086ffc5088437ff204421bff102210e7fe611086ffe3088439fe984421bff0c2210dffc411086ffc2088409f
  | 5 => 0x834115ffea1a08a7fe50d0453fe2868207ff9034103ff881a08abff30d0453ff186822aff4c34114ff861a08a7fe20d0453fe1068229ff84341027f821a0813ff65904097fb2c8204ff9964101dfccb20813fd65904017eb2c8204ff19641025f8cb20892fd6490451ffaa48207ff95241007faa92081ffc5490409ffb1c8204bfd8e41027fcc72080afe6390409feb1c8227bf58e41027f8c720812fc639044fffa9c8227ff94e4113ffaa72089ffc539040fffa1c8227ff90e4113ffa872081ffc4390409ffb148204ff98a41005fcc520813fd62904017eb148204ff18a41147fea520803fe5290401fea948228ff14a4103ffe8520803fe4290401fea148207ff10a4113ffe652089ffe329044ffe9948227ff0ca41025fcc320813ff5190409ff28c8204ff54641027f8a320813ff4190409dfa0c8207fdd0641027fe6320813fe3190409fe98c8204ff0c641027fec120813fe60904037f3048204ff58241005fac120813fc60904037e3048228ffd4241137fca12089bfc509044dff2048207ff1024113ffe612089bfe309044ffe9848226ff0c241137fc412089bfc2090409ff0848204ff04241007fecaa0802ff655044bff32a8203bf99541007facaa0802fd655044bfe32a8203bf1954112ffea8a081ffe5450401feaa28207ff15141127fec6a0892ff6350449ff31a8202bf98d41127fac6a0892fd6350449fe31a8202bf18d41127fea6a0893fe5350449fea9a8224ff14d4103ffe86a0893bf4350449ff21a8224ff50d411277a86a081ffc4350401ffb128200bfd8941007fcc4a0803fd6250401fe3128200bf1894112ffea4a0803fe5250401fea928225ff1494103ffe84a0803bf4250401ff2128200ff509410077a84a081ffc4250449ff9928224ff8c941127fa64a0893fc325044bffa8a8204ff94541007faa2a0813fc515040fffa0a8207fdd0541027fc82a0813be4150449ff98a8204ff8c541127fa62a0813fc3150401ffb028200bfd814111ffcc0a0806fe6050401feb028223ff1814100df8c0a0897ff5050447ff2828223ff1414111ffc80a081ffc4050449ff9828223ff8c141127fa60a088ffc3050447ff1028223ff0814111ffc20a0813fc1050409ffb288204bfd9441027fcca2080efe6510409bf32882039f99441027faca20802fd6510409beb2882009f59441027f8ca20812fc651040f7f3208207ffd504103ffca82081ffd541040ffe2a08204ffd8c41025fec620813fe63104057f3188204f798c41015bcc620813fd63104437eb188204f758c41005bac620813fc63104097e3188221ffd4c4110ffca620887fd5310443fe2988207ffd0c4103ffc862081ffd431040ffe2188204ffd8841027fcc420802fe6210409f73108200bb98841027fac420802fd6210409f6b108200bb58841027f8c420
  | 6 => 0x7ffaa4a203ff9525101ffaa92880ffc5494409ffb1ca204bfd8e51027fcc72880afe6394409feb1ca22fbf58e51027f8c728812fc6394407ffa9ca203ff94e5101ffaa72880ffc539445fffa1ca22fff90e5117ffa87288bffc4394409ffb14a204ff98a51005fcc528813fd62944017eb14a204ff18a5101ffea52880ffe5294407fea94a203ff14a51007fe8528803fe4294401fea14a200ff10a5117ffe65288bffe329445ffe994a22fff0ca51025fcc328813ff5194409bfa8ca203fdd4651027f8a328813f45194409ff98ca204ff8c651027fa6328813fc3194409ffb04a204ff9825100dfcc128813fa60944037d304a204ff58251005fac128813f960944017cb04a204ff1825100df8c12880fff5094407ff284a203ff14251177fc81288bbfc409445fff984a22eff8c25117ffa61288bbfc309445dff104a22eff08251027fc2128813fc10944097fb2aa200ffd9151005fec8a8803fe6454401feb22a200ff1915103df8c8a880fff5454407bfaa2a203ff9515101ffaa8a88037d5454407fe2a2a22dffd8d5116dfec6a88b7fe63544057f31aa22dff58d5116dfac6a88b7fc63544057e31aa203ffd4d5101efea6a880ffe5354407fea9aa22ddf54d5101ff8a6a88b7ff435445bff21aa22dff50d5116ff886a8803ff62544017fb12a200ff98951007fac4a8803fc62544017e312a203ffd495101efea4a880ffe5254407fea92a200df5495101ff8a4a8803ff4254401ff212a200ff50951007f884a88b7ff325445bff192a22dff4c95116ff864a880eff6154407ffa8aa203fdd4551027fca2a88137e5154409fe28aa204df1455101fe8a2a88b7ff3154409ff18aa22dff4c551027f862a8803ff60544017fb02a22cff9815100dfcc0a8803fd6054459fe302a201bf1815101ffea0a880ffe5054459bf282a203ff1415101ef8a0a88b3fe4054459fe202a22dffcc151167fc60a88b7fd3054459fe182a22cff88151167f840a88b3fe1054409fe082a207ffd974103dfecba081ffe65d04077f32e8207ff59741005facba081ffc65d040f7e32e8207ffd534103ffca9a081ffd54d040ffe2a68207ffd8f4103dfec7a081ffe63d04057f31e8207ff58f41155fac7a081ffc63d04057e31e822affd4f41157fca7a08abfd53d0455fe29e8207ffd0f4103f7e87a081ffe43d040ffea1e822aef50f4103ff887a081fff62d040fff3168200bf98b4103ffac5a0802fd62d040ffe316822bffd4b41007fca5a0803fd52d0457fe2968207ffd0b4103f7e85a081ffe42d040ffea168200ef50b4103ff885a08abff32d0455ff196822aff4cb41157f865a08afff51d0409ff28e8200ff54741027f8a3a08abff31d0409ff18e822aff4c741027f863a081fff60d040fff3068201bf9834103ffac1a0802fd60d040ffe3068201bf1
  | 7 => 0x2101ffe5490801feaa48407ff15242067fec7210ceff6390867ff31c8402bf98e4219ffac7210cefd6390819fe31c8402bf18e4219ffea7210cffe5390867fea9c8433ff14e4203ffe87210cffe4390867fea1c8407ff10e4203dfcc5210e3ff5290819ff2948400ff54a42067f8a52101fff4290801dfa148407fbd0a4219ffe6521033fe3290867fe994840cff0ca42067fec321003fe61908097f30c8400ff58642005fac321033fc6190871ffa8c8438ff1464219ffe63210cffe3190867fe98c8433ff0c642067fec1210dffe60908037f3048400ff58242005fac121033fc60908037e3048438ffd42421bffca1210dffc509086fff2048407ff1024219ffe61210dffe3090867fe9848437ff0c2421bffc4121033fc209086fff0848437ff04242007fecaa1002ff655086dff32a8403bf99542007facaa1002fd655086dfe32a8403bf195421b7fea8a101ffe5450801feaa28407ff151421affec6a10d6ff635086bff31a8402bf98d421affac6a10d6fd635086bfe31a8402bf18d421affea6a10d7fe535086bfea9a8435ff14d4203ffe86a10d7bf435086bff21a8435ff50d421af7a86a101ffc435086dffa928400ff94942007faa4a10dbfc525080fffa128407fbd0942007fc84a1003be425086bff9928435ff8c9421affa64a10d7fc3250801ffb0a8400bfd8542007fcc2a1003fd6150801fe30a8404bf185421b7fea2a10dbfc515086bff98a8435ff8c5421affa62a10d7fc3150801ffb028400bfd81421a7fcc0a1006fe6050801feb028434ff1814200df8c0a10dbff5050869ff2828434ff141421a7fc80a101ffc405086bff9828434ff8c1421affa60a10d3fc3050869ff1028434ff081421a7fc20a10d3fc1050819ffb288407bfd944203ffcca2100efe651080ffeb288400bf59442067f8ca2101efc651080f7f3208407ffd504203ffca82101ffd541080ffe2a0840cffd8c4203dfec62101ffe63108057f3188407ff58c4218dfac621033fc63108057e3188431ffd4c4218ffca6210c7fd5310863fe2988407ffd0c4203ffc862101ffd431080ffe2188433bf98842197fea421033fe5210801fea90840cff1484203ffe842101fbf4210819ff2108407fb9084203ffa8421003bd421080ff6a108431ffcc842067fc64210c7fd3210819fe190840cffd844203ffcc221012fe611080ffeb088400bf58442067f8c2210cbff5110865fe2888431ffcc44218ffc62210c7fd3110863fe188840cffd804203ffcc021006fe601080ffeb008400bf58042067f8c021006fc6010865ffa808430ff94042187f8a02101ffe401080ffe2008431ffcc042187fc60210c7fd3010861fe1808430ff88042067f840210c3fe1010861fe0808403bf59651027fec928813fe649440f7f324a204ff59251005fac928813fc649440
  | 8 => 0xfd8e521fdfec7290fffe63948057f31ca43fff58e521fdfac729033fc63948057e31ca403ffd4e5201ffca72900ffd5394807fe29ca43fffd0e521fffc87290fffd439487ffe21ca403bf98a5201ffea52900f7f5294807f7a94a40cff14a5201fd8a5290ffff3294819ff194a43fff4ca52067f86529033ff6194801ff30ca404bf98652007fac329002fd6194819fe30ca403ffd465201ff8a3290ffff319487fff18ca43fff4c6521fff86329033ff609487dff304a401bf98252007fac129002fd6094819fe304a401bf1825201ffea12900ffe509487dbf284a403ff1425201ef8a1290fbfe409487dfe204a43fffcc2521f7fc61290fffd309487dfe184a43eff88252067f841290fbfe109487dfe084a403bfd9552007fec8a9002ff6454801ff322a400ff59152007f8c8a901efc6454807ffaa2a403ff9515201ffaa8a900ffc545487bffb1aa43dbfd8d521effcc6a900afe635487bfeb1aa43dbf58d521eff8c6a900afc6354807ffa9aa403dfd4d5201ffca6a900ffd535487bbea9aa403ff14d521effe86a90f7fe435487bfea1aa43dff10d5201dfec4a900fff5254807f7a92a403ff94952006fca4a900ffc5254807be292a403fb149521effe64a90f7fe325487bfe992a43dff0c952007fec2a9002ff6154801ff30aa400ff58552007f8c2a9012fc6154807ffa8aa403dfd455201ff8a2a90f7ff315487bff18aa43dff4c5521eff862a9003ff60548017fb02a43cff9815200dfcc0a9003fd6054879fe302a401bf1815201ffea0a900ffe5054807fe282a43cff901521e7f880a90f7ff3054879ff182a43dff4c1521e7f860a90f3fe2054879fe102a43cff841521e7f820a901fff65d080f7fb2e8407ff9974201dfccba101f7e65d08073f32e8407ff59742005facba101f7d65d08013eb2e8407ff1974203df8cba101fff54d080fff2a68407ff5534203ff8a9a101fff63d080f7fb1e8407ff98f42015fcc7a101fde63d08056f31e8407ff58f421d5fac7a101fdd63d08016eb1e8407ff18f42015f8c7a10ebff53d0875ff29e843aff54f421d7f8a7a101fff43d080fdfa1e8407ff90f4203ffa87a10ebbd43d080ffe21e843bffd4b42007fca5a1003fd52d0877fe296843affccb421d7fc65a10ebfd32d0875fe1968407ffd874203ffcc3a1012fe61d080ffeb0e8400bf5874203ff8c3a10efff51d0877fe28e843affcc7421d7fc63a10ebfd31d0875fe18e8407ffd834203ffcc1a1006fe60d080ffeb068400bf5834203ff8c1a1006fc60d0877ffa868439ff943421cff8a1a101ffe40d080ffe206843affcc3421cffc61a10ebfd30d0873fe1868439ff883421cff841a10e7fe10d0873fe086840cffd9642005fecb210e3fe65908077f32c8400ff59642005facb21033fc65908077e32c8435bf592421c7fea9
  | 9 => 0xa00140000200140000380140240140040040000040280400040500000140300000000a000800401004c00003000006801400000c06c00006001800000000001c12000000c00800006800c00007c00002c04400001800800000400401400000400000004c09c00c0400080100140180b82180cc02c01400c0a803800800004400417401403400005c00400800408400c01400c06c00400000402400002c00c0040080000000140041d40180000080480040200c40380100040480000200300040f000c02c02000009400401007004400000c00801000800803c0a400000001008401400800000c1f803000001400c0000000c402c020118000040000004090004010008077eb2ca807bf9925403ffea92a01f7f5495007dfaa4a803cfd525403ff8a92a01fbc549500fffb1ca807bfd8e5403ffcc72a00afe639500ffeb1ca843bf58e5403ff8c72a00afc6395007ffa9ca803ff94e5401ffaa72a00ffc539500fffa1ca807efd0e5403ffc872a01ffd4395087dea1ca807ff10e5403ffec52a01ffe62950017f314a807ff58a54005fac52a01ffc6295007ffa94a803ff14a5421ffe652a10ffe3295087fe994a843ff0ca5403ffec32a01ffe61950097f30ca807ff58654005fac32a01ffc6195007ffa8ca803ff1465421ffe632a10ffe3195087fe98ca843ff0c65403ffec12a01ffe60950037f304a807ff58254005fac12a01ffc60950037e304a803ffd425401ffca12a10b7e5095007fe284a803df1425403ffc812a01ffc4095087ff984a842ff8c25421ffa612a10bfc3095085ff104a842ff08254217fc212a10bfc109500f7fb2aa803bfd915401ffea8aa00fbf545500fff2a2a807df9515403ff8a8aa01f7c5455007de2a2a841ffd8d5420dfec6aa107fe63550057f31aa841ff58d5420dfac6aa107fc63550057e31aa803ffd4d5401efea6aa00ffe5355007fea9aa841df54d5401ff8a6aa01fff4355083dfa1aa841ff90d5420ffa86aa107bd435500ffe21aa800ffd8954005fec4aa003fe6255001feb12a800ff18954005f8c4aa00fff5255007fe292a803df1495420ffe64aa107fe3255083fe992a841ff0c954007fec2aa002ff6155001ff30aa800ff58554007f8c2aa012fc6155007ffa8aa803dfd455401ff8a2aa107ff3155083ff18aa841ff4c55420ff862aa003ff60550017fb02a800fed8154005f6c0aa103fe60550037f302a800ff58154207f8c0aa006fc6055001fc302a801be1815401ffea0aa00f7f5055007ff282a803ff14154207fc80aa01ffc4055083ff982a840ff8c15420ffa60aa103fc3055081ff102a840ff08154207fc20aa103fc10550077eb2ca40cffd9252007fcc92901efe6494801feb24a400bf59252067f8c92900fff5494807bfaa4a403ff9525201ffaa9290037d5494807fe2a4a40cf
  | 10 => 0x84f00016a800025435613483d807621f907d0a849f000000084a0002a18148f9061e35901108a617108f80f8f482c9014955d0844e42b781dcd724d82f8911cd986541510f2855e0002fb82785b40000458c9800014c0d000010768240001a2ccf67dd195a1404121a126c96304ae7aa000000028c00024093e851c49618c0e9450006e0000cf908e21b0000c18cf84f40000730c1065636c1d790d006420398583708641ae1d482d43b723d2034aa277928893501302a6198a1ac00045d07787cce4e078257180000005331b800006409004001000001000000400000005006801000c01000c00000c11000000001004000400404c01802801817000400004800002400000406400400c00000000c02400009804400800c00001c00803c00c0e80001d00240080200040200000180080140fc01003004000800801800007006000006800c0000000300000100080000040040140040080100000000180140000340400000200180bc0040200000080341c002c07c0080000300140040dc00001c02c02c00000800001800000c00401400001c00006401000400802000800800010400c00001802802800000400400809802401c0040580100000100000080580a400c04002002001c00412408c01c05801400c00801000000000001400400001c04803001001c00402400000006c00800000000c05c02807004c00800000c04c02c06400403800000400407000002800c00000001803402800800001000803803400001c00800400400c0000e414402802004c04000001805412c02400001002400800000c0280f802001402400400c0080180001180080180dc01000000c0000040a000000405001400000c00003003007c00000c06000000003c00400800c03400000c02c00009800001800000800000000000000000004403402007003403000c06c13402001413c02c00c05001000004000803000402802c00003402400800004002803c00000022c01402400001005005c0000000b400001c03c00401c03c00c09001001800001400c0000080140002040680000000040000080000640300f40200d00a80180180080001a80380380780000100fc00002c00000000404401002400404c01400013811402408001000000001401800400002000401001802c03800800013800004001000001c03405401400000000001002c0e800403400806409c04801001401c03c0940380000000180340a405c0100180c80080000000a802c01400409c06800400400400c00c0000140080ac0080540080041200000041f405c04802c00802001801400801001800c00402c0580dc00000003c0380241a400805000001400804c02c00002401c03400002800400001801800412402001c03808801c01401801400401c2cc00000400400002006c01c01c00000001c
  | 11 => 0xdd06a65ef3ff8000dc67110b49a9003c03000000000002e81db17480000c63d60000cd400034499cc38a1ee00007c08b60854108a58b1e39a23e8000e0837a1ec99b8f1027731701c0e805440ff8d380d20312cc04d4d3a5b808c194c7fe7e436889f41320723d304c8ea63931d3975cd3667602410082362001b51f40c9622b0cf204cace82f2e09058c202eb012085ce463543cd0b9c3a64d63a68500bbc26d27a86c8e0c0002620af8e4c77b1979e850da3fd24288c81d81c708b14103f652001a117000000018516ac80879d0000d442e60b629380fca0275b2d80d340005f200000000007ee3271afc0000000cb9cec000428390089425a0a71009ce0d1852803e800000054635a80003125a111aa09c0003812d498a8b200ca2208b8800000041a800023218335d80010946c70000864fb47083b080f4dc865f2181a287741152000fe0be05631778a4c7f81aa2918c9469212a2391c7ccc02080a19944c9016242599c0edc7db03594fc9ce0c713888dd06c144182869468a7bd2aa1c906de0ce244a0f8dd209039901f0c685293e019e42dc1580329d40612241395197094c782205095404e84e2d693746ee2ec07f9ab4fac1d52d41080ec46ce18013b861e4490878bc8e601c300012e8bc213c2a99eec3760d703a98a035010a3a59848bb82d70230fd0e3404100e1b200001e400000004f25b62e88d480007fc00000002cc66d12610e4fb80bd1e41af028a0003a79f0ce846c24050d9c0000000001f9cda033b2ce945c0e200021882dcb645d422500c8c0a00004d1ef80000000b587e42b46cf164168c0004f600015c059a8320f500e8ff64b013093540008252f6846891e5020a41ee8fda4010001244626810000202419643e37296f41f819d0e005dc91856800000003fc1c81f50000eae0891351c9500829b19804ec0da41b0db00006ac000000000000037b000096000000000009fc83416127193a813604d24f00000002bd000088ce1c20c2c880000005fe1c416b8c8876c30b833c0000501cf14d400076a09719d49ee63600018049e66970001a18d281c90ea00010547d44118b440000000790f007c008e0001cf400018a00000005d2000381149800004b000179012e82b0000000bf827a15580010580000000000e143351051ba8f0e0002398bf8a205b31da800069e4050001f34d2200011a000095e7e828a0000404371000000000001f42880000000000000f700005884130508fcc4100000d68f7e4c81eda06857600006e108c77c6b02ff88a4fb244618a80003ca75a3d40354e5804e07b0f910901960000ed07fc8520251fd041c37e05f18f8ff46b112f80004e648e212045c9145fb0001894a6244d19212acc448551109a54fd40da00007e872a5180000ec0d2074e295070400072224000010060000000000000
  | 12 => 0x2741379800000000028518a4c1a2c40c2800000038e2ac00006dc8690001c4c00045e05710d4a1a46717717e07aa8441c28a203b80e83c20000480462000017058e3040001eb85426dd0ef9e50db22e442980000000002b5818c0000f918415f0ed06ef4300f9cc126ff2628308d4600026480000006330001d2050c80e0ac990861c49232699f4e1a74717d21a89481da2c9120c42217a1a59bd0d3e3603be0d985964c223c15740a80ed0fe8938da814100408985824652e490604f80b12c68f188d84e12ee86302743bc00590ec8a05840569de00003c107700010b84983200cb483200015a8b800c20002858000224000000141c0003fa332a01cbca3c342097885720003a19294f1401d28780004de1dd0b211a063c2d51a38e506fa11d0c700000001d938e000000040b0920000e9200014c989ca4a7801911d90a806c63aa899026e0a10460c48f300003e383c0672861000000000000000018b03207c600000008ac7fd1019cccbaa5a01951b789fa4661661a008c63b813b073c7a601b1fb11e507a0e43d38914dfa10c0091cacc405b912184fcd8a5cd0f311147ae2bc19e854881e0eb1ed00002ce7753ec181850677019700007d00fa1ba8b8c7380c332f151cde020733480e4fa600010d14680000000000000af200023697b0f3e701000000071238228000000003ec059129c00059a1b818ec00043817a9b0469457f3f60b3c00042e06c000012c69200020741e24b1286000071e1941ef93280007b71b4862c5c229400d124000000023486a42624f214b9b98f0a1de42c9c249c47c914600bc4923651ce800029400000004784f023315d2078a5850522b8d206466490df9930d4e3f9088858c3f80b40f79218ebe587000089c31a000000121c0002923bf0c500c00000001aac0000880e20000cb60003ca88fcb0c52423b1504ba07a238d80000ba0000c9063c9521b5000000087a3f733d13a4acc4603cd9c50fc465010a991cb4a46e08699b0db62b83a300b8fbe5f62cf1f0429233300000002b65e32dd1aa090400032300000004a20e90b60eb846a14d00004500004180404bf229538c80002ec29142f0000bb43210100c0cfca6e700011f011a00016b10bc0de1283711220968000000166c7725030000b780000000801ce80007a305797000ae45a208947c1e864a010926c6743e225b8aa83101e742fa0a0a726314249fac6f21930dc819c67e19c1b98100fae1212f994247ac3de1a21ff827a0ea02c9c302d05420ed959050e4771211a3496c1913010bdc14c7ca1bc1d280000002c50000c141af0cc00009966411780b0c6d80094000ba804670023a9a8016a4d343313187dc72e1f483ecfe224b01e0bb48901841d00e4477615627618900aa3f331e1ed02126ae2bf10840003c50098d40d9a2a40000000d306132e7
  | 13 => 0xb901805a2d920e06acd3415736b1f844a46a50858f3d0684ef29e9fc81bc27b2c708ec0d46f118b0e3086466b0de011c25e0a52de004000a5c72a282f08e24be22703501c00b81e80fd429a1300b28fac9640842ec17a8df25851f18b481ea56a1d41a10d1031c1328e8c9264c32509860ab21b011c95d46b66d202d1be88b001400620f07960a339f1f10c6433635a0ec8c1678c40a109c3a26850c0857868657607283302102f400200dc2060c535c10acd425993fc0f44362236422910c2d834c33195708806f50711c0ceca0732b702190366fb4101340b5e3642df8fc8a2c0d02729f309c04dc3790000e8a51e3379ee0f0c71512e944c4788462b88f941ee0000f401e804c5563d988e013e0810000000bc071e00016d00024330d985ec0003861411b007ba80f39c93ecb262fd21b8fec92803833c1e44aee61c08a024ca441cd4261bb4bd63270bf030034c6710001e4860e1e322c93b400062636a800000009405520dc6c64f000000000001bd00002a00d83ad2289c7435c00000005e400080c00008b870602b0331b800002ac0d3956853039830884806ba1e12aa96b008a00004392ecb4e3c23c6800017200002120e05600003969e8000079c000002907e00018680000000002ed90389d01271811b4c89e00037600007885d31c90208f5e1b430218305167932e28288e201f518c8dc906600000000004c417c2040e350220cd0000000e6c1e92e11d3000005b2a51270d9280b00013f8ac42742ce00002f06ee000000099c00011e8ca400000000010d83ee5be000000000061f0e8000014018010f0a7c49e2c521d0000c5a5b7000036cd860003941ee479c00035100009cc00033a0c44dc22b421500004d04fc3c183440000002ad95b0ea81390640034df06b711220e45841721ec17b84d276d2e50d6439c56d06086180007660b684d090873f32d19985ba2143a200ec01e2054030a750440ab2e591105122f618e95d0050415054800075476b04500010b4000251a0e8ad200029f199cabc7ce087217454068739b8000000000000048cb1644c1a113ac000002000020065840326603a40005360001718eb200000012d4c9e6431358a34258000331091006a2460db8f48fea85726fa048f560e304a97a0ece76932a80448c800621a05f483c00012f03f80005cc1f880b035a2851188000d9400030e94e0d042b7334057c20e6fc3b19b708c221804e80004cc4f10002020b886cb26388e8f206df000005437c2752da9a3ca1c4aa0bf9ca4af04f939790500323b10fb0000c7e6303988d7c0000000001584b480493a898390b672131080000005fa0f58b5039646b1901b688be54d42b16c45f2000204965cd1c7f02c0a10c4d800005803240000000aa8dd80861f8000130093a7d500002cc9160000000e6c0005080000ce00a
  | 14 => 0x5342bd8e007141d63ba066c09e26e34b083cf780d91e6844ca2a10226d0bc456c08f1f683482083a12969bdcbcc5a6019865425251b18613445028050e30df0ae669e000068842086520901ec0c42221b688c0d7467e31584e095877229d8e58e2c8160000ca01580003758000fee4741e3800037482940c998400067f0001948a0c638000091c0000002ca00005a60000000000fd2000000000066e0250ec1f800000ba000005800000000000002962123d4a008bbe0e700004888f631f000197400000040c0e900007f321100006b038b0001dd8cee46f000057083a4992eb098c62054c06f9e5cac06d73b890b040822c05f8000b866aa00014c0616582246960000020d1631f081fa59f3578afc000000103128000051917d8000e1e56510e05406d600000005807a88621df9a04f603613038a8ca9e78f07c0f9855c0e6000000000002a16d8d5505a1ed00018e800004c0000000000000000054482644b2a4094c92a6fe1650384744000110034c26631710997f495052b1a005d4cae7053c481d049025a349935c0000001670000ec0858431a07ca5e6a6000061ca665520fa000000053c26795e800040c06e8ef4e243af12d95403e21253db0958a3881516e09c05081533fb0d7833e61925e0f3066422f0a39cd00be6b335e83584a24260000a2820a77a17c0fbcbea5f43ef02ec70e34123810b434819a30d0000f5a4bf0b79fe487863d1c81ddc9725e70a70e10fc65373838f84efa6f602f199076627e38ba05c45a5bb179960c9660000ae89703ae37f3ae81fc000595000136c53c572079985506200022a18bcf8a5a203c80000007961cc80006024cd2a59e2c2561063cf17647e000315489c908002231a9cf000070b0521c6072e5c809f001cfde4173e9186c13821f00015243580360aa11f873e1a32c48980bd23c90001aa4000290000000042c00027c126874c75831c80000b00000001a0cfa255f1b11d580007810000bf0d7c0000001ad8ede4bd14e0728b2c11c3e5800097000000010a4f6a174105988c00069900004d80001820620000c8a78e4360000c062b104900000000680001ec4a2451d10e8eacd8814f172953875281c00011080004ad42680600002c01d700008aa000000130422053a400800001c07e1268c6854a24a1ab9cd42e02b20f1219c33269c14788a855a31b32c8b405be5cf2909ba081a1263d287c875852e15399c80ac2673b9a0b8efe5322be925c8fe7991598cd09fe2e63e78000c284de1b4196068c7b20f002441061c217f8aa067825011f09648a460f00
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x4765451000cf47654510025f7755451002777755451000777655451001ef6655451001ef46554510037746554510005f7745451003777545451000775545451003777535451025f755354510037775254510007755254510007f3705451000df6705451000df47054510167f07054510026f76054510027f36054510037f35054510167765054510167745054510167f05054510167705054510167f24054510167f2305451025ff13054510167f2205451000cfe76d051000cfc76d0510006bf64d051003ebc64d051000dfa70d0510005f970d0510105f67690510026f67690510025f77590510005f5759051011df5749051003ef6649051003ef46490510027f3709051000df6709051000df47090510027f07090510026f76090510027f36090510257f35090510137f05090510137f24090510137f2309051024ff13090510137f2209051003cff765051000cfe765051011cfd765051000cfc7650510006bf645051003ebc6450510005fb705051000df87050510027f0105051000df4765051003ef4765051000cf47650510005f77550510005f57550510025f77450510027b77450510007b7645051003ef6645051003ef46450510007b4645051023fb7435051023fb54350510007b74250510007b54250510007f3705051000df6705051000df4705051011ff07050510026f76050510027f36050510247f3505051011ff0505051011ff2405051011ff2305051023ff1305051011ff2205051000cfe76c851000cfc76c8510006ef62c8510066ec62c851000dfa70c8510005f970c8510064ff764851000cfe76485100c4fd764851000cfc7648510005df734851002ddc7348510006ef6248510006ec6248510027e42148510005fb704851000df87048510025f8765011003ef87650110024f876501100077b7550110035fa7550110035f8755011000778755011003578755011000dfb745011000fbb7450110007bb645011003efa645011003ef86450110007b86450110007ba5450110007b95450110235fb7350110235f97350110005fb7250110007f37150110025fa7150110025f87150110007f0715011000efb615011000ff36150110007f25150110007f15150110007f24150110007f14150110025f87648110006f87648110024f876481100077b7548110035fa7548110035f87548110007787548110035787548110005fb7448110005f9744811022dfb734811022df97348110226fb6348110226f9634811000dfb724811000feb7248110007eb6248110066fa6248110066f86248110007e86248110007ea5248110007e95248110007ea4248110007e94248110007f37148110025fa7148110025f87148110007f0714811000efb614811000ff36148110007f25148110007f15148110007f24148110007f14148110
  | 1 => 0x891001cfc75d891003cfe74d8910004fd74d8910004ff73d8910014fe73d8910004fd73d8910014fc73d8910024ff70d8910024fd70d89100defa30d8910006f930d89100deef20d89100deed20d8910006ef62989100c5f5719891001cfe7598910004fd7598910064fc759891003cfe7498910004fd7498910064ff7398910014fe7398910004fd7398910064fc7398910064fe72989100c4fd7198910066f571989100f4fd7098910066f97098910066fa20989100057f75589100357c7558910005bf7458910005bc7458910005df735891002ddc73589100f5f77158910004ff75589100067f75589100047f755891001cfe755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf745891003cfc7458910006bc745891003cbc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc7358910006ef72589100f4ff7158910006f771589100c4ff7058910006fb70589100c6fa3058910006f930589100dcfe7618910006ed621891001cfe7518910004fd7518910064fc751891003cfe7418910004fd7418910064ff7318910014fe7318910004fd7318910064fc7318910066ee7218910024fe7118910024fc7118910024ff701891000cfe7018910024fd7018910066f9701891000cfc7018910066ef2018910066fa20189100a6ed2018910064ff7694910004fe7694910004fd7694910064fc76949100067f659491001e7c659491000dfa7094910005f970949101f7785094910004ff7654910004fe7654910004fd7654910004fc7654910005fb705491000df8705491003cff76d0910004fe76d0910004fd76d091003cfc76d09100357e75d09100057d75d091002dde73d0910005dd73d0910025f671d0910005f571d091000dfa70d0910005f970d0910064ff7690910004fe7690910004fd7690910064fc7690910006bf649091003ebc6490910066ee6290910006ed629091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc7650910006ee6250910006ed625091000dfa7050910064ff7610910004fe7610910004fd7610910064fc7610910006bf641091003ebc6410910025f67110910005f5711091000dfa7010910005f9701091026df67694510026f67694510165f5759451001ef6659451001ef46594510005f5749451000df67094510027f2709451000df27094510027f1709451000df47094510026f76094510027f36094510037f35094510177f05094510177f24094510177f23094510267f13094510177f2209451001cff765451000cfe7654510164fd765451000cfc76545100067f655451001e7c6554510005fb705451000df8705451016778505451000df4765451001ef
  | 2 => 0x5f57110b10025f7765471028ef7765471002777755471001ef6655471002776655471001e766554710027756554710026f46554710005f7745471004f77545471000775545471004f77535471028775535471004f77525471000775525471000df6705471000df47054710167765054710167745054710025f77650710006f77650710005f77550710005f57550710027766550710027756550710027b7745071003ef66450710026f4645071027fb7435071027fb54350710007b74250710007b5425071000df6705071000df4705071001cfe76d95100367e65d951000dfa70d9510025f970d95100377b50d951003cfe74d9510004fd74d95100367c54d9510004ff73d9510014fe73d9510004fd73d9510014fc73d95100367f53d95100067d53d9510064fe72d9510004fd72d95100367c52d9510024fe71d951000cfd71d9510024fc71d95100367f51d9510024ff70d951000cfe70d9510024fd70d9510036f970d9510024f970d951000cfc70d95101767f50d9510036fb50d95101767d50d9510176f850d95100367c6559510005bf7459510005bc7459510275f77159510167785059510174ff75595100067f7559510004ff7459510006bf7459510004bf745951003cfc7459510006bc745951003cbc74595100367f5459510004ff7359510014fe7359510004fd7359510014fc7359510004ff7259510064fc7259510274ff7159510006f77159510164ff7059510006fb7059510036fb50595101667e50595101667c5059510166f8505951003cfe76d911001cfe75d9110004fd75d911001cfc75d9110006bf54d9110006bc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d9110006bf43d9110006bd43d9110064fe72d9110004fd72d9110024fe71d9110024fc71d9110024ff70d911000cfe70d9110024fd70d911000cfc70d9110136bf40d9110136bd40d9110006bf649911011df571991100057f75591100357c755911014df77159110004ff75591100067f75591100047f755911001cfe755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110014fe7359110004fd7359110014fc7359110004ff7259110064fc725911014cff7159110006f7715911011cff7059110006fb7059110134fe76191100357e75191100057d751911003ebe6419110006bd641911002dde7319110005dd7319110005ee7219110005ed721911003cff7695110004fe7695110004fd769511003cfc76951100067f659511001e7c65951100373f5495110025f67195110005f5719511000dfa7095110005f97095110217785095110004ff7655110004fe7655110004fd7655110004fc765511001e7e65551100067d6555110005fb705511000df870551100377b505511001cfe75d8910004fd75d
  | 3 => 0xf32597100067e32597100067d32597100067c32597100267f71597100267e71597100267d71597100267c71597100267f41597100267e41597100267d41597100267c41597100267f31597100267e31597100267d31597100267c31597100267f21597100267e21597100267d21597100267c21597101667f70597101667e70597101667d70597101667c70597101667f40597101667e40597101667d40597101667c40597101667f30597101667e30597101667d30597101667c30597101667f20597101667e20597101667d20597101667c20597100267f10597100267e10597100267d10597100267c1059710004ff755931001cfe755931001cfc7559310026bf7459310004ff7359310014fe7359310004fd7359310014fc7359310006bf4359310006bd4359310004ff7259310064fc7259310024ff715931000cfe7159310024fd715931000cfc7159310026be4159310026bc415931011ebf405931011ebd4059310026fa1059310026f9105931003cff7695310024fe7695310004fd7695310024fc769531001e7e65953100067d659531004f3f5495310025f67195310005f57195310004ff7655310024fe7655310004fd7655310024fc765531001e7e65553100067d6555310025f67155310005fb705531000df8705531001cfe7598b10004fd7598b10064fc7598b1003cfe7498b10004fd7498b10064ff7398b10014fe7398b10004fd7398b10064fc7398b10026ee7298b10066ee3298b10006ed3298b1000cfe7198b1000cfc7198b10026ee2198b10026ec2198b10066ef2098b100f6ed2098b10004ff7558b1001cfe7558b1001cfc7558b10004ff7458b1003cfc7458b10004ff7358b10014fe7358b10004fd7358b10014fc7358b10026ef7258b10006ee3258b10006ed3258b10024ff7158b1000cfe7158b10024fd7158b1000cfc7158b10026ee2158b10026ec2158b100c6ef2058b100c6ed2058b10026fa1058b10026f91058b10064ff7694b10024fe7694b10004fd7694b10024fc7694b1001e7e6594b100067d6594b10004ff7654b10024fe7654b10004fd7654b10024fc7654b1001e7e6554b100067d6554b1003cff76d0b10024fe76d0b10004fd76d0b10024fc76d0b1004d7e75d0b100057d75d0b101de7e65d0b100067d65d0b1003ebe64d0b10006bd64d0b10045de73d0b10005dd73d0b10025f671d0b10005f571d0b10064ff7690b10024fe7690b10004fd7690b10024fc7690b101c67e6590b100067d6590b10066ee6290b10006ed6290b10004ff7650b10024fe7650b10004fd7650b10024fc7650b101b67e6550b100067d6550b1003ebe6450b10006bd6450b10006ee6250b10006ed6250b10064ff7610b10024fe7610b10004fd7610b10024fc7610b101967e6510b100067d6510b10025f67110b10
  | 4 => 0x852001cfc75d852003cfe74d8520004fd74d8520004ff73d8520014fe73d8520004fd73d8520014fc73d8520006ee42d8520006ed42d852000cfe70d852000cfc70d85200f6fa30d8520006f930d85200f6f710d852005d7e75985200057d75985200067f65985200067c6598520006f761985200057f755852005d7c75585200067f65585200067c6558520005bf7458520005bc7458520005df7358520055dc73585200067f65185200067c6518520026f66118520006f56118520004fe7694520004fd7694520024fc76945200067f659452001e7c659452000dfa7094520005f97094520004ff7654520004fe7654520004fc76545200067f655452001e7c65545200076d5254520004fe76d0520004fd76d052003cfc76d05200067f65d052015e7c65d0520005ee72d0520005ed72d0520007ad42d0520004fe7690520004fd7690520024fc76905200067f65905201467c6590520006bf649052003ebc649052000dfa7090520005f97090520004ff7650520004fe7650520004fc76505200067f655052012e7c6550520007ad4250520004fe7610520004fd7610520024fc761052005d7e75105200057d75105200067f65105201167c6510520006bf641052003ebc6410520055de7310520005dd7310520005ee7210520005ed721052000dfa7010520005f970105200a4fe76c85200067f65c85200fe7c65c852000df870c852000cfe76885200067f65885200ee7c6588520006f76188520026f4618852000dfa7088520005f9708852000cfc76485200067f65485200d67c6548520005df7348520055dc7348520006f76148520026f46148520005fb704852000df870485200f4fe760852005d7e75085200057d75085200067f65085200b67c6508520005be7408520005bd7408520055de7308520005dd7308520007e5210852000dfa700852000dfa76c812000efa76c812000cfa76c81200077b65c81200077865c8120065fb73c8120295f973c812000dfa72c812000fea72c812000efb62c812000feb62c8120067ea52c8120007e952c8120067ea42c8120007e942c8120005f971c81200267f7559710004ff745971003cfc745971004e7f545971004e7c5459710004ff7359710014fe7359710004fd7359710014fc735971004e7f53597100067e53597100067d535971004e7c5359710004ff7259710064fc725971004e7f525971004e7c5259710024ff715971000cfe7159710024fd715971000cfc71597100267e51597100267c51597101667f50597101667d50597100067f74597100067e74597100067d74597100067c74597100067f73597100067e73597100067d73597100067c73597100067f43597100067e43597100067d43597100067c43597100067f72597100067e72597100067d72597100067c72597100067
  | 5 => 0x55de7399120005dd73991201a5ed72991200057f755912005d7c75591200067f65591200067c65591201cdef7259120004ff75591200067f75591200047f755912001cfe755912001cfc75591200067c755912001c7c7559120006bf7459120004ff7359120014fe7359120004fd7359120014fc73591201ccff7259120006ef7259120004ff7159120024fc71591201a4ff7059120006fb70591201a6fa10591201bcfe76191200067f65191200067c651912003ebe6419120006bd641912003cff7695120004fe7695120004fd769512003cfc76951200067f659512001e7c659512005f3f5495120005ee7295120005ed7295120004ff7655120004fe7655120004fd7655120004fc76551200067f655512001e7c6555120005fb705512000df870551202c4fe76949201f67f659492001e7c65949202c5ee76949202beee76949201e5ed75949201f76f659492001eee659492001eec659492005f6c659492001e6c6594920005ed749492005f6f54949200076d549492000dee709492000dec7094920066ef60949201f76e50949201f76c50949201f7ea30949202b7e930949201f7ea109492001cff765492000cfe76549201e4fd765492000cfc76549200067f655492001e7c6554920005fb705492000df8705492000dec765492001eec765492000cec76549201f5ef75549200076f75549200076f655492001eee655492001eec655492005f6c6554920005ef745492005f6f53549202af6d535492005f6f5154920007eb705492000dee705492000dec70549201e7e870549201e6ef60549201e7ea30549202afe930549201e7ea105492000cfe76d092000cfc76d092005d7e75d09200057d75d09200067f65d09201de7c65d0920006bf64d092003ebc64d0920055de73d0920005dd73d092000dfa70d0920005f970d0920184fe76909200067f65909201c67c6590920185ee7690920006ee7690920005ef7590920005ed75909200076f65909200076c65909201a5ed749092003eee649092003eec649092000dee709092000dec7090920066ef60909201bfea30909202a7e930909201bfea109092003cff765092000cfe76509201a4fd765092000cfc76509200067f65509201b67c6550920006bf645092003ebc6450920005fb705092000df8705092000dec765092003eec765092000cec7650920005ef7550920005ed75509200076f65509200076c6550920007af7450920007af645092003eee645092003eec6450920007ac645092029faf435092029fad4350920007eb705092000dee705092000dec70509201a7e870509201a6ef60509201a7ea305092029fe930509201a7ea10509201bcfe76109200067f65109201967c65109201bdee7210920024fe76d85200067f65d85200067c65d852001cfe75d8520004fd75d
  | 6 => 0xe72d0720005ed72d0720007ad42d0720024ff7690720064fe7690720004fd7690720004ff7650720004fd7650720064fc765072003ebe6450720006bd6450720007ad4250720024ff7610720064fe7610720004fd76107200757e75107200057d751072006dde7310720005dd7310720065ee7210720005ed721072000dfa7010720005f970107200c4fd76887200dcff7648720005df734872006ddc7348720067e4214872001cfe76d952005e7e65d952003cfe74d9520004fd74d952005e7f54d952005e7c54d9520004ff73d9520014fe73d9520004fd73d9520014fc73d952005e7f53d95200067e53d95200067d53d952005e7c53d9520064fe72d952000cfd72d9520064fc72d952005e7f52d9520024fe71d9520004fd71d952005e7f51d952005e7c51d9520064ff70d95201f4fd70d95201f67f50d95201f67d50d95202c57e76d952001c7e76d95200067f63d95200067e63d95200067d63d95200067c63d95201f76f72d95201f77a30d95200077930d95201f76e20d95201f76c20d95201f77820d95201f77a10d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95201f67f72d952005e7e72d95201f67d72d95200067f32d95200067e32d95200067d32d95200067c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067e31d95200067d31d95200067c31d95201f67f70d95201f67e70d95201f67d70d95201f67c70d95201f67f40d95201f67e40d95201f67d40d95201f67c40d95201f67f30d95201f67e30d95201f67d30d95201f67c30d95201f67f20d95201f67e20d95201f67c20d95201f67f10d95201f67e10d95201f67d10d95201f67c10d952005e7c65595202cdef72595201f4ff75595200067f7559520004ff745952003cfc7459520004ff7359520014fe7359520004fd7359520014fc73595202ccff7259520006ef7259520004ff7159520024fc71595201e4ff7059520006fb70595201f57e761952005e7e76195201f47e76195200067f63195200067e63195200067d63195200067c63195202c76d72195202c67f62195202c67f60195202c77a30195200077930195202c76e20195202c76c20195202c77820195202c77a101952003cfe76d91200067f65d91200067c65d912001cfe75d9120004fd75d912001cfc75d9120004ff73d9120014fe73d9120004fd73d9120014fc73d9120006bf43d9120006bd43d9120064fe72d9120064fc72d9120024fe71d9120004fd71d9120064ff70d91201bcfd70d91201bebf40d91201bebd40d91201befa10d912005d7e75991200057d75991200067f65991200067c6599120006bf6499120
  | 7 => 0x972000cfe725972001cfd725972000cfc72597200667e52597200667c5259720004ff7159720024fc71597200767f51597201e67f50597201e67d505972001cfe75d93200667e75d932001c7e75d9320004fd75d93200667d75d93200047d75d9320064fc75d9320064ff73d9320014fe73d9320004fd73d9320064fc73d9320064fe72d9320066ee72d9320024fe71d9320004fd71d9320066f970d93201a4fd76993200757e75993200057d7599320066bf6499320066bc649932006dde7399320005dd739932003cff7659320066bc6459320004ff755932001cfe755932001cfc7559320066bf7459320006bf5459320006bc5459320004ff7359320014fe7359320004fd7359320014fc7359320006bf4359320006bd435932003cff725932000cfe725932003cfd725932000cfc7259320066be4259320066bc4259320004ff7159320024fc71593201a6bf40593201a6bd405932003cff7695320064fe7695320004fd7695320064fc769532001e7e65953200067d65953200773f5495320065ee7295320005ed7295320004ff7655320064fe7655320004fd7655320064fc76553200067f655532001e7c6555320005fb705532000df8705532000ded7694b20066ed7694b2000ced7694b2001eee6594b200676e6594b200676d6594b20066ec6594b20005ed7494b200776f5494b200076d5494b2000dee7094b20067ea7094b20067e97094b2000dec7094b201f76e5094b201f76c5094b202ccff7654b202cdef7654b202e6ef7654b200676f7554b2001eee6554b2001eec6554b20005ef7454b200776f5354b202df6d5354b200776f5154b2000dee7054b2000dec7054b201a4fd76d0b200757e75d0b200057d75d0b2006dde73d0b20005dd73d0b2000ded7690b20066ed7690b2000ced7690b20065ef7590b20005ed7590b2003eee6490b20067ae6490b20067ad6490b20066ec6490b2000dee7090b20067ea7090b20067e97090b2000dec7090b201ccff7650b201cdef7650b20006ef7650b20005ef7550b20005ed7550b20067af7450b2003eee6450b2003eec6450b202d7af4350b202d7ad4350b2000dee7050b2000dec7050b20066f76198720026f46198720024ff7658720066f46158720004ff755872001cfe755872001cfc7558720004ff745872003cfc7458720004ff7358720014fe7358720004fd7358720014fc735872000cfc7258720006ee4258720006ed4258720006f63158720006f53158720066f72158720066f421587200c6fa20587200c6f71058720024ff7694720064fe7694720004fd769472000dfa7094720005f97094720004ff7654720004fd7654720064fc765472001e7e65547200067d65547200076d525472003cff76d0720064fe76d0720004fd76d072003ebe64d0720006bd64d0720065e
  | 8 => 0x1ceef20d89401cefa10d89400857e75989400057d75989400067f65989400067c6598940006ef62989400057f75589400857c75589400067f65589400067c65589400067f65189400067c6518940006ed621894001cfe7518940004fd7518940064fc7518940064ff7318940014fe7318940004fd7318940064fc7318940024fe7118940004fd7118940064ff701894003cfd7018940066ef2018940186ed2018940004fe7694940004fd7694940064fc76949400067f659494001e7c65949400073d5494940004ff7654940004fe7654940004fc76549400067f655494001e7c655494000cfe76909400067f65909401c67c6590940006ef6290940066ec629094000dfa7090940005f9709094000cfc76509400067f65509401b67c6550940006ef6250940006ec6250940005fb705094000df8705094003fb84050940024fe76d85400067f65d85400067c65d854001cfe75d8540004fd75d854001cfc75d8540004ff73d8540014fe73d8540004fd73d8540014fc73d8540064fe72d8540004fd72d854003cfd70d854014ef710d85400857e75985400057d75985400067f65985400067c6598540006f761985400057f75585400857c75585400067f65585400067c65585400067f65185400067c6518540026f66118540006f56118540004fe7694540004fd7694540024fc76945400067f659454001e7c659454000dfa7094540005f97094540004ff7654540004fe7654540004fc76545400067f655454001e7c65545400073d545454000cfe76905400067f65905401467c6590540006f76190540026f4619054000dfa7090540005f9709054000cfc76505400067f655054012e7c6550540006f76150540026f46150540005fb705054000df87050540004fe76c8540004fd76c8540064fc76c85400067f65c85400fe7c65c8540004fe7688540004fd7688540024fc76885400067f65885400ee7c658854000dfa7088540005f97088540004ff7648540004fe7648540004fc76485400067f65485400d67c6548540005df734854007ddc7348540004fe7608540004fd7608540024fc76085400857e75085400057d75085400067f65085400b67c650854003dbe7408540005bd740854007dde7308540005dd730854000dfa7008540005f970085401e4fd75d972003cfe74d9720066be74d972003cbe74d9720004fd74d9720066bd74d9720004bd74d97200767f54d9720064ff73d9720014fe73d9720004fd73d9720064fc73d9720064fe72d9720066ee72d9720024fe71d9720004fd71d9720066f970d97201f67e50d97201f67c50d972001cff76597200667c65597200667f7559720004ff745972003cfc74597200767c5459720004ff7359720014fe7359720004fd7359720014fc73597200767f53597200067d535972001cff725
  | 9 => 0xd72d95400867f52d95400867c52d9540024fe71d9540004fd71d95400867f51d95400867c51d954003cff70d954003cfd70d95402167f50d95402167d50d95402fd7e76d954001c7e76d95402173f74d95400067f63d95400067e63d95400067d63d95400067c63d95403177b40d95402173e40d95402173c40d95402177840d95402177a10d95402167f74d95403167e74d95402167d74d95402167c74d95400067f73d95400067e73d95400067d73d95400067c73d95403167f43d95400067e43d95400067d43d95403167c43d95400067f72d95400067e72d95400067d72d95400067c72d95403167f42d95403167c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95403167f41d95403167c41d95400067f31d95400067e31d95400067d31d95400067c31d95402167f70d95402167e70d95402167d70d95402167c70d95402167f40d95402167e40d95402167c40d95402167f30d95402167e30d95402167d30d95402167c30d95402167f20d95402167e20d95402167d20d95402167c20d95402167f10d95402167e10d95402167d10d95402167c10d95400867c655954030dbf7459540214ff75595400067f755954030cff7459540006bf7459540004ff7359540014fe7359540004fd7359540014fc7359540004ff7259540064fc7259540004ff7159540024fc7159540204ff7059540006fb705954008cfb70595402157e76195400867e76195402147e76195402ff3d74195402fe7f64195400875e73195400875d73195400067f63195400067e63195400067d63195400067c63195402fe7f60195403067b60195403077b40195402ff3e40195402ff3c40195402ff7840195402ff7a10195402fdbe769514003ebe7695140205bd75951402173f659514001ebe659514001ebc65951400873c659514001e3c65951402f6bf63951402f6bd639514000dbe709514000dbc709514003ebf609514003fbb60951402173e50951402173c5095140217ba109514001cff765514000cfe7655140204fd765514000cfc76551400067f655514001e7c655514003f3c5455140005fb705514000df8705514000dbc765514001ebc765514000cbc765514003dbf755514003f3f75551400073f655514001ebe655514001ebc65551400873c65551402eebf63551402eebd63551400873f53551402ef3d53551400873c52551400873f5155140007bb705514000dbe705514000dbc7055140207b8705514003ebf605514003fbb60551402073f50551402073d5055140207ba10551400067f65d89400067c65d894001cfe75d8940004fd75d894001cfc75d8940004ff73d8940014fe73d8940004fd73d8940014fc73d8940024fe71d8940004fd71d894003cfd70d8940
  | 10 => 0x8550005bd740855009dde7308550005dd730855000dfa7008550005f9700855003e7f755974003cff745974000cfe745974003cfd745974000cfc745974003e7e545974003e7c5459740004ff7359740014fe7359740004fd7359740014fc735974008e7f53597400067d5359740004ff7259740064fc725974008e7c5259740004ff7159740024fc715974008e7f515974008efb70597402067f505974008efb505974008e7b50597402067d5059740206f8505974003dbf7655340326bf765534003f3f755534003f3f655534001ebe655534003ebc655534003f3c655534003ebf635534031ebd635534008f3f535534031f3d535534008f3c525534008f3f515534008fbb705534000dbe705534000dbc7055340207b8705534000db870553402073f505534008fbb505534008f3b50553402073d5055340207b8505534001cfe7598b40004fd7598b40064fc7598b4000cfe7498b4000cfc7498b40064ff7398b40014fe7398b40004fd7398b40064fc7398b40066ee7298b4003eef4298b40066ec4298b40024fe7198b40004fd7198b40066ef2098b401beed2098b40004ff7558b4001cfe7558b4001cfc7558b4000cfc7458b40004ff7358b40014fe7358b40004fd7358b40014fc7358b4003eef7258b4003eef4258b4003eec4258b40004ff7158b40024fc7158b401a6ef2058b40064ff7694b4003cfe7694b40004fd7694b4001e7e6594b400067d6594b400073d5494b4000dfa7094b40005f97094b401f7785094b40004ff7654b40004fd7654b4003cfc7654b40005fb7054b4000df87054b40004ff755874001cfe755874001cfc755874000cfc7458740004ff7358740014fe7358740004fd7358740014fc7358740004ff7258740064fc725874003ef7715874003ef7415874003ef44158740006fb505874011ef8505874003efa405874003ef9405874011ef71058740024ff769474003cfe7694740004fd769474000dfa7094740005f97094740004ff7654740004fd765474003cfc765474001e7e65547400067d65547400073d5454740005fb705474000df87054740167785054740064ff76c874003cfe76c8740004fd76c8740066ee62c8740006ed62c8740024ff768874003cfe7688740004fd7688740004ff7648740004fd764874003cfc7648740005df7348740095dc7348740006ee6248740006ed6248740024ff760874003cfe7608740004fd760874008d7e75087400057d750874003dbe7408740005bd7408740095de7308740005dd730874000dfa7008740005f9700874001cfe76d95400867e65d954003cfe74d954000cfd74d954003cfc74d95400867f54d9540004ff73d9540014fe73d9540004fd73d9540014fc73d95400867f53d95400067e53d95400067d53d95400867c53d9540064fe72d9540004f
  | 11 => 0x6bf43d9150006bd43d9150064fe72d9150004fd72d9150024fe71d9150004fd71d915001cfd70d915030ebf40d91502167f6599150006bf6499150085f9709915033efb609915008dfb70591502fe7f651915003ebe6419150006bd641915009dde7319150005dd731915033efb601915000d7c765515003e7c765515000c7c765515001d7f745515001f3f74551500073f645515003e7e645515003e7c64551500073c64551503367f63551503367d63551503373f43551503373d43551500077b705515000d7e705515000d7c705515020778705515000d78705515001e7f605515001f7b605515000cfd75d895003cfe74d8950004fd74d8950004ff73d8950014fe73d8950004fd73d8950014fc73d89502beee52d89502beed52d8950024fe71d8950004fd71d895001cfd70d89502ceef20d8950005be7498950005bd7498950006ef629895005df97098950075fb7058950006ed621895000cfd751895003cfe7418950004fd74189502e67f54189500067d5418950064ff7318950014fe7318950004fd7318950064fc7318950066ee52189502e6ed5218950024fe7118950004fd7118950064ff701895001cfd70189502c67e50189502c67c5018950066ef20189502c6ed2018950004fe76d0950004fd76d095003cfc76d095001d7e75d09500057d75d0950006bf64d095003ebc64d095009dde73d0950005dd73d0950004fe7690950004fd7690950064fc7690950004ff7650950004fe7650950004fc7650950006bf645095003ebc6450950004fe7610950004fd7610950064fc761095001d7e75109500057d751095000dfa7010950005f97010950024fe76d855000cfd75d855003cfe74d8550004fd74d855032e7f54d85500067d54d8550004ff73d8550014fe73d8550004fd73d8550014fc73d8550064fe72d8550004fd72d855032ef651d855032ef551d855001cfd70d855032efb50d85502767e50d85502767c50d8550276f850d8550276f710d8550006f76198550035f97098550005bf7458550005bc745855004dfb7058550026f66118550006f56118550004fe76d0550004fd76d055003cfc76d055001d7e75d05500057d75d0550004fe7690550004fd7690550024fc7690550006bf649055003ebc6490550004ff7650550004fe7650550004fc7650550004fe7610550004fd7610550024fc761055001d7e75105500057d7510550006bf641055003ebc641055009dde7310550005dd7310550005ee7210550005ed721055000dfa7010550005f97010550004fe76c8550004fd76c8550064fc76c8550004fe7688550004fd7688550024fc7688550004ff7648550004fe7648550004fc7648550005df734855009ddc7348550004fe7608550004fd7608550024fc760855001d7e75085500057d7508550005be740
  | 12 => 0xf4158c21026de4158c21026dd4158c21026dc4158c21026df2158c21026cf2158c21026de2158c21026d62158c21026dd2158c21026cd2158c21026dc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dc5058c21006de4058c21006dc4058c21066df2058c21006de2058c21066dc2058c21026df1058c21026de1058c21026dd1058c21026dc1058c210fcff765482101e7e65548210067d6554821006be6454821006bd64548211eede6354821006dd63548211e6fa6054821004fd76d08210b57e75d08210057d75d08211de7e65d08210067d65d082103ebe64d0821006bd64d08210adde73d0821005dd73d08211d6de63d0821006dd63d08211cefa60d0821004ff76508211b67e65508210067d655082103ebe6450821006bd64508211aede6350821006dd6350821356ee62508211a6fa6050821025f77648421006f77648421004f77648421027766548421027756548421027b66448421027b56448421007d7734842134fd47348421026f76348421027d6634842134ef56348421027d56348421006d56348421025f77248421027e77248421066f66248421027e66248421067e65248421007e55248421007e74248421067e44248421067e6324842134fe53248421027f26048421027f16048421004ff755802101cfe755802101cfc7558021004ff745802103cfc7458021004ff7358021014fe7358021004fd7358021014fc735802100cfd7158021026fb7058021006fb50580210a6fa50580210a6f850580210a6fa40580210a6f84058021006fb30580210a6fa3058021006f930580210a6f83058021066fb2058021066f82058021026fb1058021026f81058021006fb7558021006fa7558021006f97558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb5458021006fa5458021006f95458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f843580210a6fb7258021066fa7258021006fb5258021066fa5258021006f95258021066f85258021006fb4258021066fa4258021006f94258021066f84258021006fb3258021066fa3258021006f93258021066f83258021026fb7158021026fa7158021026f87158021026fb5158021026fa5158021026f95158021026f85158021026fb4158021026fa4158021026f94158021026f84158021026fb3158021026fa3158021026f93158021026f83158021026fb2158021026fa2158021026f92158021026f8215802103cfe76d915000cfd75d9150346be54d9150346bd54d9150004ff73d9150014fe73d9150004fd73d9150014fc73d9150
  | 13 => 0x9021026bc7199021026bf5199021026be5199021026bd5199021026bc5199021026bf3199021026be3199021026bd3199021026bc3199021026bf2199021026be2199021026bd2199021026bc219902103ebf709902103ebe709902103ebd709902103ebc7099021006bf5099021006be5099021006bc5099021006bf3099021006be3099021006bd3099021006bc3099021066bf2099021006be2099021066bc2099021026bf1099021026be1099021026bd1099021026bc1099021004ff755902101cfe755902101cfc7559021024ff7459021026bf7459021006bf5459021006bc5459021004ff7359021014fe7359021004fd7359021014fc7359021006bf4359021006be4359021006bd4359021006bc4359021064fe7259021064fc7259021066be4259021066bc4259021024fe7159021024fc7159021026be4159021026bc4159021026ef2159021026ed2159021004ff705902100cfe705902100cfc7059021006be4059021006bc4059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006be5359021006bd5359021006bc5359021066be7259021066bc7259021006bf5259021066be5259021066bc5259021006bf3259021066be3259021006bd3259021066bc3259021026bf7159021026be7159021026bd7159021026bc7159021026bf5159021026be5159021026bd5159021026bc5159021026bf3159021026be3159021026bd3159021026bc3159021026bf2159021026af2159021026be2159021026bd2159021026ad2159021026bc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf5059021006be5059021006bc5059021006bf3059021006be3059021006bd3059021006bc3059021066bf2059021006be2059021066bc2059021026bf1059021026be1059021026bd1059021026bc105902103cff7695021024fe7695021004fd7695021024fc769502101e7e65950210067d659502103ebe6495021006bd64950210b73f549502121ede6395021216fa6095021004ff7655021024fe7655021004fd7655021024fc765502101e7e65550210067d655502103ebe6455021006bd645502120ede6355021005fb70550210a5f87055021206fa6055021006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c210aedf7258c21066de7258c210aedd7258c21066dc7258c21006df5258c21066de5258c21066dc5258c21066de4258c21066dc4258c21026df7158c21026de7158c21026dd7158c21026dc7158c21026df5158c21026de5158c21026dd5158c21026dc5158c21026d
  | 14 => 0x5ec7254521027e42154521004fe76d0521064fc76d0521006bf64d052103ebc64d0521006df63d0521156dc63d0521005ee72d0521005ed72d0521007ad42d0521027e421d052103cff7650521004fd765052103cfc7650521006bf645052103ebc6450521006df6350521126dc6350521005ef7250521005ec7250521007ad4250521006df63c85210bedc63c8521025ee72c8521026ef62c8521065f773c8521365f573c8521007d763c852135fd463c8521025f672c8521026f762c8521027e762c8521067e642c8521007e542c8521067e632c852135fe532c852100cfe76d8121006df63d8121006dc63d81210c6fa60d812101cfe75d8121004fd75d812101cfc75d812103cfe74d8121004fd74d8121004ff73d8121014fe73d8121004fd73d8121014fc73d8121024fd72d8121006ee42d8121006ed42d812100cfc71d81210c6fa20d81210c6fa10d81210057f75581210d57c7558121005bf7458121005bc7458121005df73581210cddc7358121006df6358121006dc63581210c6f86058121024ff75594210267f7559421004ff745942103cfc74594210b67f54594210b67c5459421004ff7359421014fe7359421004fd7359421014fc73594210b67f53594210067e53594210067d53594210b67c5359421064fe7259421064fc72594210667e52594210667c5259421024fe7159421024fc71594210267e51594210267c5159421004ff705942100cfe705942100cfc70594210b67f50594210067e50594210b67c50594210067f74594210067e74594210067d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067f43594210067e43594210067d43594210067c43594210b67f72594210667e72594210667c72594210667e42594210667c42594210067f32594210667e32594210067d32594210667c32594210267f71594210267e71594210267d71594210267c71594210267f41594210267e41594210267d41594210267c41594210267f31594210267e31594210267d31594210267c31594210267f21594210267e21594210267d21594210267c21594210067f70594210067e70594210067d70594210067c70594210067e40594210067c40594210067f30594210067e30594210067d30594210067c30594210667f20594210067e20594210667c20594210267f10594210267e10594210267d10594210267c105942103ebf759902103ebe759902103ebd759902103ebc759902103ebf739902103ebe739902103ebd739902103ebc7399021006bf5399021006be5399021006bd5399021006bc5399021066be7299021066bc7299021006bf5299021066be5299021066bc5299021006bf3299021066be3299021006bd3299021066bc3299021026bf7199021026be7199021026bd719
  | 15 => 0xf705912100cfe705912100cfc7059121004fe761912103ebe6419121006bd6419121006dc631912103cff7695121004fe7695121004fd769512103cfc7695121006bf649512103ebc64951210d73f549512121edc6395121005ee7295121005ed7295121004ff7655121004fe7655121004fd7655121004fc76551210067f655512101e7c6555121006bf645512103ebc645512120edc6355121005fb70551210c5f870551210cdde76d8d210cede76d8d21014de76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d2138fcf72d8d210cfcc72d8d21007d771d8d210cfd471d8d2138fce21d8d2138fcc21d8d21006de60d8d21006dc60d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d2138edf72d8d210cede72d8d210cedd72d8d210cedc72d8d21006df52d8d21006dc52d8d21006df71d8d2138ede71d8d210cedd71d8d2138edc71d8d21006df51d8d2138ede51d8d2138edc51d8d2138ede41d8d2138edc41d8d2138ede21d8d210cedd21d8d2138edc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dc50d8d21006de40d8d21006dc40d8d21006de20d8d21006dc20d8d2138edf10d8d21006de10d8d2138edc10d8d210ecfe7694921006df63949211fedc6394921024fc76549210067f655492101e7c6554921006df63549211eedc6354921005f77154921025f47154921024fe76d0921024fc76d09210d57e75d09210057d75d0921006bf64d092103ebc64d09210cdde73d0921005dd73d0921006df63d09211d6dc63d0921025f671d0921005f571d0921004fe7690921006df639092119edc6390921005ee7690921006ee769092137ded749092103eee649092103eec649092136def739092136ded7390921007cf6390921387cc6390921025ee7190921025ec7190921066ef6190921387e63190921387e53190921024fc7650921006bf645092103ebc6450921006df63509211aedc6350921005f77150921025f47150921025ec765092103eec7650921024ec7650921007af7450921007af645092103eee645092103eec6450921007ac645092137def735092137ded7350921007cf6350921377cc6350921377af4350921377ad4350921007e77150921025ee7150921025ec7150921007e47150921025e47150921377e63150921377e53150921004fe7610921006df631092118edc631092136dee7210921007ad421092101cff76545210d4fd765452101cfc76545210067f655452101e7c6554521006df635452116edc6354521005ef7254521
  | 16 => 0x96210ee7f53596210067d53596210ee7f5259621024fc71596210267e51596210267c5159621004ff705962100cfe705962100cfc70596210067e50596210ee7c5059621004ff755922101cfe755922101cfc7559221026bf7459221004ff7359221014fe7359221004fd7359221014fc7359221006bf4359221006bd4359221024fc7159221026be4159221026bc4159221026ef2159221026ed2159221004ff705922100cfe705922100cfc705922103cff7695221024fe7695221004fd7695221024fc76952210ef3f5495221004ff7655221024fe7655221004fd7655221024fc765522101e7e65552210067d6555221005fb70552210ddf870552210d4fd7694a2101cff7654a21024fc7654a2101e7e6554a210067d6554a21005f77154a21025f47154a210ed7e75d0a210057d75d0a2103ebe64d0a21006bd64d0a210e5de73d0a21005dd73d0a21025f671d0a21005f571d0a2103cff7650a2103ebe6450a21006bd6450a21005f77150a21025f47150a21025f576c8621066f576c8621065f773c8621395f573c8621027e672c8621004ff755822101cfe755822101cfc7558221004ff745822103cfc7458221004ff7358221014fe7358221004fd7358221014fc7358221026fb7058221006fb50582210def850582210defa40582210defa3058221006f930582210defa2058221026fb1058221026f8105822101cfe76d95210d67e65d9521006dc63d952103cfe74d9521004fd74d95210d67f54d9521004ff73d9521014fe73d9521004fd73d9521014fc73d9521024fd72d95210d67f52d95210d4fd71d95210d67f51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210d67c50d95210d67c6559521005df73595210cddc7359521006dc63595210d4ff75595210067f7559521004ff745952103cfc7459521004ff7359521006df7359521004df7359521014fe7359521004fd7359521014fc7359521006dc7359521014dc73595210d67f53595210067d53595210ecff7259521006ef72595210fcff7159521006f77159521004ff705952100cfe705952100cfc705952103cfe76d9121006dc63d912101cfe75d9121004fd75d912101cfc75d9121004ff73d9121014fe73d9121004fd73d9121014fc73d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d91210d57e75991210057d7599121006bf64991210cdde7399121005dd7399121006dc6399121005df73591210cddc7359121006dc6359121004ff755912101cfe755912101cfc7559121006bf7459121004ff7359121006df7359121004df7359121014fe7359121004fd7359121014fc7359121006dc7359121014dc7359121006bf4359121006bd4359121004ff7259121006ef7259121004ff7159121006f77159121004f
  | 17 => 0xfe7f54d9721064ff73d9721014fe73d9721004fd73d9721064fc73d9721066ee72d97210667f52d9721066f571d972100cfe70d9721004fd70d972100cfc70d97210067e50d97210fe7c50d972101cff76597210667c65597210667f7559721004ff745972103cfc7459721004ff7359721014fe7359721004fd7359721014fc73597210fe7f53597210067d5359721024fc72597210667e52597210667c52597210fe7f5159721004ff705972100cfe705972100cfc705972101cfe75d9321004fd75d9321064fc75d9321064ff73d9321014fe73d9321004fd73d9321064fc73d9321066ee72d9321066f571d932100cfe70d9321004fd70d932100cfc70d9321004fd76993210fd7e75993210057d7599321066bf6499321066bc64993210bdde7399321005dd739932103cff7659321066bc6459321004ff755932101cfe755932101cfc7559321066bf7459321004ff7359321014fe7359321004fd7359321014fc7359321006bf4359321006bd4359321024fc7259321066be4259321066bc4259321004ff705932100cfe705932100cfc705932103cff7695321064fe7695321004fd7695321064fc76953210ff3f5495321065ee7295321005ed7295321004ff7655321064fe7655321004fd7655321064fc76553210067f655532101e7c6555321005fb70553210f5f870553210b4ff7654b210667f6554b210667c6554b210fd7e75d0b210057d75d0b21066bf64d0b21066bc64d0b210bdde73d0b21005dd73d0b21025ed7690b21066ed7690b21024ed7690b2103eee6490b21067ae6490b21067ad6490b21066ec6490b21065ef7390b213a5ed7390b21025ee7190b21067e67190b21067e57190b21025ec7190b21066bf6450b21066bc6450b21067ac4250b21005ef7650b21006ef7650b21067af7450b21067af6450b2103eee6450b2103eec6450b21067ac6450b2139def7350b2139ded7350b21357af4350b21357ad4350b21025ee7150b21025ec7150b2101cff7654721064fc765472101e7e65547210067d6554721005ef7254721065ec725472103ebe64d0721006bd64d0721065ee72d0721005ed72d0721007ad42d072103cff765072103ebe6450721006bd6450721005ef7250721065ec7250721007ad425072100cff76583210057f75583210fd7c7558321066f86058321004ff75583210067f75583210047f755832101cfe755832101cfc75583210067c755832101c7c7558321004ff745832103cfc7458321004ff7358321014fe7358321004fd7358321014fc7358321024fc7258321006ee4258321006ed42583210f6fa3058321006f93058321066fb2058321066f820583210f6fa10583210267f7559621004ff745962103cfc74596210ee7f5459621004ff7359621014fe7359621004fd7359621014fc735
  | 18 => 0xe2058841006ec2058841006ef7558841006ee7558841006ed7558841006ec755884103eef745884103eee745884103eec745884103eef545884103eee545884103eed545884103eec5458841006ef7358841006ee7358841006ed7358841006ec7358841006ef5358841006ee5358841006ed5358841006ec535884103eef435884103eee435884103eed435884103eec4358841026ef7158841026ee7158841026ec7158841026ef5158841026ee5158841026ed5158841026ec5158841026ef4158841026af4158841026ee4158841026ed4158841026ad4158841026ec4158841026ef3158841026ee3158841026ed3158841026ec3158841006ef7058841006ee7058841006ed7058841006ec7058841006ef5058841006ee5058841006ec505884103eef405884103eee405884103eed405884103eec4058841006ef3058841006ee3058841006ed3058841006ec3058841026ef1058841026ee1058841026ed1058841026ec1058841064ff7694841024fe7694841004fd769484101e7e65948410067d65948411fede6394841006dd6394841066ee6294841006ed62948411f6fa6094841004ff7654841004fd7654841024fc765484101e7e65548410067d65548411eede6354841006dd6354841006ee6254841006ed62548411e6fa6054841004ff755804101cfe755804101cfc755804100cfd7458041004ff7358041014fe7358041004fd7358041014fc7358041004ff7258041064fc7258041026f6415804103ef54158041024ff7058041026fb7058041006fb5058041106fa5058041106f8505804103efb405804103ef84058041006fb3058041106fa3058041006f93058041106f83058041106fa2058041106f82058041026fb1058041026f81058041006fb7558041006fa7558041006f97558041006f8755804103efb745804103efa745804103ef8745804103efb545804103efa545804103ef9545804103ef85458041006fb7358041006fa7358041006f97358041006f87358041006fb5358041006fa5358041006f95358041006f8535804103efb435804103efa435804103ef9435804103ef84358041006fb7258041006fa7258041006f97258041006f87258041006fb5258041006fa5258041006f95258041006f8525804103efb425804103efa425804103ef9425804103ef84258041006fb3258041006fa3258041006f93258041006f83258041026fb7158041026fa7158041026f87158041026fb5158041026fa5158041026f95158041026f85158041026fb4158041026fa4158041026f24158041026f9415804103ef14158041026f84158041026fb3158041026fa3158041026f93158041026f83158041026fb2158041026fa2158041026f92158041026f821580410fcfd75d972103cfe74d9721004fd74d9721
  | 19 => 0x94410067e30594410067d30594410067c30594410067e20594410067c20594410267f10594410267e10594410267d10594410267c1059441006df7558c41006de7558c41006dd7558c41006dc7558c4103edf7458c4103ede7458c4103edd7458c4103edc7458c4103edf5458c4103ede5458c4103edd5458c4103edc5458c41006df7258c41006de7258c41006dd7258c41006dc7258c41006df5258c41006dc5258c4103edf4258c4103ede4258c4103edd4258c4103edc4258c41026df7158c41026de7158c41026dd7158c41026dc7158c41026df5158c41026de5158c41026dd5158c41026dc5158c41026df4158c410269f4158c41026de4158c41026dd4158c410269d4158c41026dc4158c41026df2158c41026de2158c41026dd2158c41026dc2158c41006df7058c41006de7058c41006dd7058c41006dc7058c41006df5058c41006de5058c41006dc5058c4103edf4058c4103ede4058c4103edd4058c4103edc4058c41006de2058c41006dc2058c41026df1058c41026de1058c41026dd1058c41026dc1058c4101cfe7598841004fd7598841064fc7598841064ff7398841014fe7398841004fd7398841064fc7398841024fe7298841026ee7298841006ef5298841066ec529884103eef4298841066ec4298841006ef3298841066ee3298841006ed3298841066ec3298841026ee2198841026ec219884100cfe7098841004fd709884100cfc7098841006ee2098841066ec2098841066ef7598841006ee7598841006ed7598841066ec759884103eee749884103eed7498841066ec749884103eef549884103eee549884103eed549884103eec5498841066ef7398841006ee7398841006ed7398841066ec7398841006ef5398841006ee5398841006ed5398841006ec539884103eef439884103eee439884103eed439884103eec4398841026ee7198841026ed7198841026ec7198841026ef5198841026ee5198841026ed5198841026ec5198841026ef4198841026ee4198841026ed4198841026ec4198841026ef3198841026ee3198841026ed3198841026ec3198841066ef7098841006ee7098841006ed7098841066ec7098841006ef5098841006ee5098841006ec509884103eef409884103eee409884103eed409884103eec4098841006ef3098841006ee3098841006ed3098841006ec3098841026ef1098841026ee1098841026ed1098841026ec1098841004ff755884101cfe755884101cfc7558841004ff7358841014fe7358841004fd7358841014fc7358841026ef7258841006ef5258841006ec525884103eef425884103eec4258841006ef3258841006ee3258841006ed3258841006ec3258841026bf4158841026bd4158841026ee2158841026ec2158841004ff705884100cfe705884100cfc7058841006e
  | 20 => 0x6ed621894101cfe7518941004fd7518941064fc7518941064ff7318941014fe7318941004fd7318941064fc7318941006ef3218941066ec321894100cfe7018941004fd701894100cfc7018941004fe7694941004fd7694941064fc769494103dbe7494941005bd7494941004ff7654941004fe7654941004fc7654941005be76d094103ebe76d094103f3e75d094103f3d75d094103dbf73d094103f9e73d09413c5bd73d094103f9d73d09410059d73d09413bebf63d09413bebd63d0941066bc62d0941025be71d0941025bc71d094103ebf61d094103fb761d0941024fe76909413b5bd7490941006ef6290941066ec6290941025f67190941005f57190941024fc7650941006ef6250941006ec625094103fac4250941005f77150941025f47150941024bc76509413b5bf73509413b5bd73509413aebf63509413aebd635094103dbf725094103faf7250941007af6250941066bc6250941007ac6250941007b77150941025be7150941025bc7150941007b4715094103ebf615094103fb7615094101cff765454112cfd765454103cfc76545410067f655454101e7c6554541005bf745454103dbc7454541027b4415454100cfe76d814111efa60d814101cfe75d8141004fd75d814101cfc75d8141024fd74d814100cfc74d8141004ff73d8141014fe73d8141004fd73d8141014fc73d8141064fe72d8141004fd72d814103cfd71d8141006fb50d814111ef850d814111efa40d814111efa10d81410057f755814112d7c755814111ef86058141024ff75594410267f755944103cfe745944103cfc745944103e7e545944103e7c5459441004ff7359441014fe7359441004fd7359441014fc73594411167f53594410067e53594410067d53594411167c5359441004ff7259441064fc72594411167f52594411167c5259441024fe7159441024fc71594410267e51594410267c5159441004ff705944100cfe705944100cfc70594411167f50594410067e50594411167c505944103e7f745944103e7e745944103e7d745944103e7c74594410067f73594410067e73594410067d73594410067c735944103e7f435944103e7e435944103e7d435944103e7c43594410067f72594410067e72594410067d72594410067c725944103e7f425944103e7e425944103e7d425944103e7c42594410067f32594410067e32594410067d32594410067c32594410267f71594410267e71594410267d71594410267c71594410267f41594410267e41594410267d41594410267c41594410267f31594410267e31594410267d31594410267c31594410267f21594410267e21594410267d21594410267c21594410067f70594410067e70594410067d70594410067c705944103e7f405944103e7e405944103e7d405944103e7c40594410067f305
  | 21 => 0xf7359641014fe7359641004fd7359641014fc73596411467f53596410067d5359641004ff7259641064fc72596411467f5259641024fc71596410267e51596410267c5159641004ff705964100cfe705964100cfc70596410067e50596411467c5059641026f7105964101cff7655241024fc765524101e7e65552410067d655524103f3c5455241005f77155241025f4715524103fb74155241005fb7055241135f8705524101cfe7598a41004fd7598a41064fc7598a41064ff7398a41014fe7398a41004fd7398a41064fc7398a41026ee7298a41066ee3298a41006ed3298a41024fe7198a41026ee2198a41026ec2198a4100cfe7098a41004fd7098a4100cfc7098a41004ff7558a4101cfe7558a4101cfc7558a41004ff7358a41006df7358a41004df7358a41014fe7358a41004fd7358a41014fc7358a41006dc7358a41014dc7358a41026ef7258a41006ee3258a41006ed3258a41024fc7158a41026bf4158a41026bd4158a41026ee2158a41026ec2158a41004ff7058a4100cfe7058a4100cfc7058a41064ff7694a41024fe7694a41004fd7694a41004ff7654a41004fd7654a41024fc7654a4101e7e6554a410067d6554a41066ee6290a41006ed6290a41025f67190a41005f57190a41006ee6250a41006ed6250a41005f77150a41025f47150a41004ff755824101cfe755824101cfc7558241004ff7358241014fe7358241004fd7358241014fc7358241004ff7258241064fc7258241024fc7158241026fb7058241006fb5058241136f85058241136fa4058241136fa3058241006f93058241136fa2058241026fb1058241026f8105824101cfe76d954112e7e65d9541024fd74d954112e7f54d9541004ff73d9541014fe73d9541004fd73d9541014fc73d9541006bf43d9541006bd43d9541064fe72d9541004fd72d954103cfd71d954112e7f51d954100cfe70d9541004fd70d954100cfc70d95410067e50d954112e7c50d954112e7c6559541005fb705954111df8705954112cff75595410067f7559541144ff7459541006bf7459541004ff7359541014fe7359541004fd7359541014fc735954112e7f53595410067d5359541006bf4359541006bd4359541004ff7259541064fc725954115cff7159541006f77159541004ff7059541006fb7059541004fb705954100cfe705954100cfc7059541006f8705954100cf87059541024fc76551410067f655514101e7c6555141005f77155141025f4715514103fb44155141005fb705514111df8705514101cfe75d8941004fd75d894101cfc75d8941004ff73d8941014fe73d8941004fd73d8941014fc73d8941006bf43d8941006bd43d8941006ef32d8941006ec32d894100cfe70d8941004fd70d894100cfc70d8941006ef6298941005df7358941125dc7358941
  | 22 => 0x495101f6f72549510076f62549510667c62549510076c62549510077771549510257e71549510257c715495100774715495101e7f615495101f7761549511657e70549511657c7054951004fe76d0951004fd76d095103cfc76d095101d7e75d09510057d75d095116dde73d0951005dd73d0951004fe7690951004fd7690951064fc769095101d7e75909510057d7590951004ff7650951004fe7650951004fc765095101d7e75509510057d7550951004fe7610951004fd7610951064fc761095101d7e75109510057d7510951025f67110951005f5711095100cfe76d815101d7e75d8151166fa60d81511677a50d8151024fd75d81510247d75d815100cfc75d815103cfe74d8151004fd74d815104e7f54d81510067d54d8151004ff73d8151014fe73d8151004fd73d8151014fc73d8151064fe72d8151004fd72d815101cfd71d81511667e50d8151166fa50d81511667c50d8151166f840d8151166fa10d8151005bf7458151005bc7458151166f8605815116778505815103e7f7559741024fc745974103e7e545974103e7c5459741004ff7359741014fe7359741004fd7359741014fc735974115e7f53597410067d535974103ebf4359741006bd4359741004ff7259741064fc725974115e7c525974115e7f5159741004ff7059741006fb7059741004fb705974100cfe705974100cfc7059741006f8705974100cf8705974115e7f505974101cfe7598b41004fd7598b41064fc7598b41024fe7498b41024be7498b41064ff7398b41014fe7398b41004fd7398b41064fc7398b41066ee7298b41066bf4298b4103eef4298b41066ec4298b4100cfe7098b41004fd7098b4100cfc7098b41004ff7558b4101cfe7558b4101cfc7558b41024fc7458b41004ff7358b41014fe7358b41004fd7358b41014fc7358b4103ebf4358b41006bd4358b4103eef7258b4103eef4258b4103eec4258b41004ff7058b4100cfe7058b4100cfc7058b41064ff7694b4103cfe7694b41004fd7694b4101e7e6594b410067d6594b4103dbe7494b41005bd7494b41004ff7654b41004fd7654b4103cfc7654b4103dbf7650b41006bf7650b413d5bf7350b413d5bd7350b4103ebf6350b413cebd6350b4103faf7250b4103faf6250b41066be6250b4103fac6250b41025be7150b41025bc7150b4101cff765474103cfc765474101e7e65547410067d6554741005bf745474103dbc7454741027b64154741004ff75583410067f75583410047f755834101cfe755834101cfc75583410067c755834101c7c7558341024fc7458341004ff7358341014fe7358341004fd7358341014fc7358341004ff7258341064fc725834103ef6415834103ef5415834103efb705834103efb405834103ef8405834114efa10583410267f75596411467f5459641004f
  | 23 => 0x24fe7158251024fc7158251026fb7058251176fa5058251176fa4058251176f84058251006fb3058251176fa3058251006f93058251176f83058251176fa2058251176f82058251026fb1058251026f81058251036fa7558251036f97558251176f87558251006fb7458251006fa7458251006f97458251006f87458251036fb5458251036fa5458251036f95458251036f85458251006fb7358251006fa7358251006f97358251006f87358251036fb5358251036fa5358251036f95358251036f85358251006fb4358251006fa4358251006f94358251006f84358251006fb7258251006fa7258251006f97258251006f87258251036fb5258251036fa5258251036f95258251036f85258251006fb4258251006fa4258251006f94258251006f84258251006fb3258251006fa3258251006f93258251006f83258251026fb7158251026fa7158251026f87158251026fb5158251026fa5158251026f95158251026f85158251026fb4158251026fa4158251026f94158251026f84158251026fb3158251026fa3158251026f93158251026f83158251026fb2158251026fa2158251026f92158251026f82158251024fd75d9151146be54d9151146bd54d9151004ff73d9151014fe73d9151004fd73d9151014fc73d91511467f53d91510067d53d9151064fe72d9151004fd72d915100cfe70d9151004fd70d915100cfc70d9151006be40d9151006bc40d9151006bf649915112df5719915115df77159151005fb7059151165f8705915103ebe6419151006bd641915116dde7319151005dd73191510247c765515101d7f745515101f3f74551510073f645515103e7e645515103e7c64551510073c645515103e3c64551513f57f73551513f57d73551513ee7f63551513ee7d63551513ef3f43551513ef3d43551510057f72551510077771551510257e71551510257c715515100774715515101e7f615515101f7761551510077b70551511657e70551511657c7055151007787055151165787055151024fd75d895103cfe74d8951004fd74d8951004ff73d8951014fe73d8951004fd73d8951014fc73d89510ee7f53d89510067d53d89510eeee52d89510eeed52d8951006ef32d8951006ec32d895100cfe70d8951004fd70d895100cfc70d8951006ef62989510d5f57198951005df735895116ddc73589510fdf77158951006ed6218951024fd751895103cfe7418951004fd74189510b67f54189510067d5418951064ff7318951014fe7318951004fd7318951064fc73189510667f5218951066ee52189510b6ed5218951006ef3218951066ec321895100cfe7018951004fd701895100cfc70189510067e50189510b67c50189510247c76549510057f74549513e57f73549513e57d73549513de7f63549513de7d635495101d7f725
  | 24 => 0xe545944203e7c5459442004ff7359442014fe7359442004fd7359442014fc73594421967f53594420067d5359442064fe7259442064fc72594420667e52594420667c5259442004ff7159442024fc71594421967f5159442004ff705944200cfe705944200cfc70594421967f50594421c4ff7654842065bf7650842006bf7650842004bf7650842066bf63508423febd6350842065bf725084203faf7250842066be6250842067ae6250842067ae5250842007ad5250842004ff755844201cfe755844201cfc7558442004ff7358442014fe7358442004fd7358442014fc735844203ebf425844203eee4258442006bd425844203eed4258442066f7715844203ef7415844203ef44158442006f63158442006f53158442066f72158442066f42158442004ff705844200cfe705844200cfc7058442004ff75580420067f75580420047f755804201cfe755804201cfc75580420067c755804201c7c7558042004ff7358042014fe7358042004fd7358042014fc735804203eee425804203eed4258042004ff7158042024fc7158042066fb7058042186fa505804203efb405804203ef84058042186fa3058042006f93058042066fb2058042066f82058042186fa1058042026bf745925112ebe545925112ebd5459251004ff7359251014fe7359251004fd7359251014fc7359251006bf4359251006bd4359251004ff7259251064fc7259251024fc71592510267f51592510267d5159251026be4159251026bc4159251004ff705925100cfe705925100cfc7059251026f7105925103cfe7498a51004fd7498a51064ff7398a51014fe7398a51004fd7398a51064fc7398a51026ee7298a51066ee5298a510feed5298a51066ee3298a51006ed3298a51024fe7198a51024fc7198a51026ee2198a51026ec2198a5100cfe7098a51004fd7098a5100cfc7098a51004ff7458a5103cfc7458a51004ff7358a51014fe7358a51004fd7358a51014fc7358a51026ef7258a510d6ee5258a510d6ed5258a51006ee3258a51006ed3258a51024fc7158a510267f5158a510267d5158a51026ee2158a51026ec2158a51004ff7058a5100cfe7058a5100cfc7058a5103cff76d0a51024fe76d0a51004fd76d0a5101d7e75d0a510057d75d0a5103ebe64d0a51006bd64d0a5117dde73d0a51005dd73d0a511cefa60d0a51064ff7690a51024fe7690a51004fd7690a51066ee6290a51006ed6290a511befa6090a51004ff7650a51004fd7650a51024fc7650a5103ebe6450a51006bd6450a51006ee6250a51006ed6250a511a6fa6050a51064ff7610a51024fe7610a51004fd7610a51025f67110a51005f57110a51186fa6010a51004ff745825103cfc7458251004ff7358251014fe7358251004fd7358251014fc7358251004ff7258251064fc7258251
  | 25 => 0xa4203f3d75d0a4203f9e73d0a4203f9d73d0a42066bf63d0a4240ebd63d0a42067ae62d0a42067ae52d0a42007ad52d0a42066f76198642026f46198642066f46158642004ff755864201cfe755864201cfc7558642004ff7358642014fe7358642004fd7358642014fc7358642064fc7258642006bf4258642006f63158642006f53158642066f72158642066f42158642004ff705864200cfe705864200cfc705864200cff7658242066f86058242004ff755824201cfe755824201cfc7558242004ff7358242014fe7358242004fd7358242014fc7358242064fc7258242004ff7158242024fc7158242006fb50582421bef850582421befa40582421befa3058242006f93058242066fb2058242066f820582421befa105824201cfe76d95421b67e65d95421b4fd74d95421b67f54d9542004ff73d9542014fe73d9542004fd73d9542014fc73d9542006bf43d9542006bd43d954203cfd72d95421b67f52d9542024fe71d9542004fd71d954200cfe70d9542004fd70d954200cfc70d95420067e50d95421b67c50d95421b67c6559542005fb70595421a5f870595421b4ff75595420067f75595421c4ff7459542006bf7459542004ff7359542014fe7359542004fd7359542014fc73595421b67f53595420067d5359542006bf4359542006bd43595421dcff7259542006ef72595421b67c5259542004ff7159542024fc71595421b67f5159542004ff7059542006fb7059542004fb705954200cfe705954200cfc7059542006f8705954200cf8705954201cfc76551420067f655514201e7c655514203f3c5455142005ef7255142005ec725514203fac4255142005fb70551421a5f870551421dcfe769494201e7e65949420067d65949421b76f529494201cff76549421b4fd765494203cfc76549420067f655494201e7c6554942005bf745494203dbc745494203dee729094203eef6290942065bf7390942405bd7390942065be7290942066bf629094203faf6290942005bd719094201cfe75d8542004fd75d854201cfc75d8542004ff73d8542014fe73d8542004fd73d8542014fc73d8542006bf43d8542006bd43d8542006f731d8542006f431d854200cfe70d8542004fd70d854200cfc70d8542006f76198542005df73585421addc73585421b57e75185420057d75185421adde7318542005dd7318542026f66118542006f561185421a5fa7018542005f9701854200cfe76d81421a6fa60d814201cfe75d8142004fd75d814201cfc75d8142004ff73d8142014fe73d8142004fd73d8142014fc73d814203cfd72d8142024fe71d8142004fd71d8142006fb50d81421a6f850d81421a6fa40d81421a6fa20d81420057f75581421b57c75581421a6f86058142064ff75594420667f755944203cfe745944203cfc745944203e7
  | 26 => 0x67e71597420067d71597420067c715974203e7f415974203e7e415974203e7d415974203e7c41597420067f31597420067e31597420067d31597420067c31597420067f70597420067e70597420067d70597420067c705974203e7f405974203e7e405974203e7d405974203e7c40597420067f30597420067e30597420067d30597420067c30597420067e20597420067c20597420067e10597420067c1059742006df7558f42006de7558f42006dd7558f42006dc7558f4203edf7458f4203ede7458f4203edd7458f4203edc7458f4203edf5458f4203ede5458f4203edd5458f4203edc5458f421d6df7258f421d6de7258f42006dd7258f421d6dc7258f42006df5258f42006dc5258f4203edf4258f4203ede4258f4203edd4258f4203edc4258f42006df7158f42006de7158f42006dd7158f42006dc7158f42006df5158f42006dc5158f4203edf4158f4203e9f4158f4203ede4158f4203edd4158f4203edc4158f42006df7058f42006de7058f42006dd7058f42006dc7058f42006df5058f42006de5058f42006dc5058f4203edf4058f4203ede4058f4203edd4058f4203edc4058f42006de2058f42006dc2058f42006de1058f42006dc1058f421b4fd7694b4201e7e6594b420067d6594b421fede6394b42006dd6394b4201cff7654b4203cfc7654b4201e7e6554b420067d6554b42005bf7454b4203dbc7454b421eede6354b42006dd6354b42004ff755874201cfe755874201cfc7558742004ff7358742014fe7358742004fd7358742014fc735874203ebf4358742006bd435874203eee425874203eed425874203ef7715874203ef7415874203ef44158742004ff705874200cfe705874200cfc7058742004ff755834201cfe755834201cfc7558342004ff7358342014fe7358342004fd7358342014fc735834203eee425834203eed4258342004ff7158342024fc715834203efb705834203efb405834203ef840583421cefa20583421cefa10583421c4fd75d9642066bd74d9642064ff73d9642014fe73d9642004fd73d9642064fc73d9642066ee72d9642024fe71d9642004fd71d964200cfe70d9642066fa70d964200cfa70d9642004fd70d9642066f970d9642004f970d964200cfc70d964201cff76596420667c65596420667f75596421c67f5459642004ff7359642014fe7359642004fd7359642014fc73596421c67f53596420067d5359642064fc72596420667e52596420667c5259642004ff7159642024fc71596421c67f5159642004ff705964200cfe705964200cfc70596420067e50596421c67c505964201cff7655242064fc765524201e7e65552420067d6555242005ef7255242065ec725524203faf4255242005fb70552421bdf87055242194ff7654a42065bd76d0a4203ebd76d0a4203f3e75d
  | 27 => 0xe70552521f57c70552520077870552521f5787055252066f76198652026f46198652066f46158652004ff745865203cfc74586520d67f54586520067d5458652004ff7358652014fe7358652004fd7358652014fc7358652064fc72586520d67f52586520d6f65158652006f63158652006f53158652066f72158652066f42158652004ff705865200cfe705865200cfc70586520067e50586520d67c505865200cff765825201d7c7558252066f860582521f77a5058252004ff745825203cfc745825205e7f54582520067d5458252004ff7358252014fe7358252004fd7358252014fc7358252064fc7258252004ff7158252024fc71582521f67e50582521f6fa50582521f67c50582521f6f840582521f6fa3058252006f93058252066fb2058252066f820582521f6fa10582521c6be54d91521c6bd54d9152004ff73d9152014fe73d9152004fd73d9152014fc73d91521c67f53d91520067d53d91521c67c52d9152024fe71d9152004fd71d91521c67f51d915200cfe70d9152004fd70d915200cfc70d9152006bf64991521edde7399152005dd73991521b5ed72991521ddef7259152005fb70591521e5f8705915203ebe6419152006bd64191520067f64949520657f73949524157d73949520657e72949520676e72949520667f629495201f6f62949520057d71949521f67e60949521f67c609495203cfe74d8552004fd74d8552004ff73d8552014fe73d8552004fd73d8552014fc73d85520fe7f53d85520067d53d85520fef651d855200cfe70d8552004fd70d855200cfc70d8552006f761985521e5fa7098552005f97098552005df73585521eddc7358552026f66118552006f5611855200cfe76d81521e6fa60d815203cfe74d8152004fd74d8152004ff73d8152014fe73d8152004fd73d8152014fc73d815201cfd72d8152024fe71d8152004fd71d81521e6fa50d81521e6f840d81521e6fa20d81521e6fa10d81521e6f8605815203e7f755974203cfc745974203e7e545974203e7c5459742004ff7359742014fe7359742004fd7359742014fc73597421de7f53597420067e53597420067d53597421de7c535974203ebf4359742006bd43597421de7f5259742004ff7159742024fc71597421de7f51597421de7c5159742004ff705974200cfe705974200cfc70597421de7f50597420067e50597421de7c505974203e7f745974203e7e745974203e7d745974203e7c74597420067f73597420067e73597420067d73597420067c735974203e7f435974203e3f435974203e7e435974203e7d43597420063d435974203e7c43597420067f72597420067d72597421de7c725974203e7f425974203e7e425974203e7d425974203e7c42597420067f32597420067e32597420067d32597420067c32597420067f7159742
  | 28 => 0x8154014fc73d8154064fe72d8154004fd72d8154024fe71d8154004fd71d8154206fa50d8154206fa40d8154006fb30d8154206fa30d8154006f930d8154206f830d8154206fa20d8154206f820d8154206fa10d8154206f810d8154205fa76d815400cfa76d815433f7b75d815408f7875d815408fbb74d815408fbb54d815433f7a54d815433f7854d815408fb854d8154006fb63d8154006fa63d8154006f963d8154006f863d815408f7b53d81540077953d8154007bb43d8154007b943d8154006fb62d8154006fa62d8154006f962d8154006f862d815408f7852d8154006fb61d8154006fa61d8154006f961d8154006f861d815408f7b51d815433efb75d8154206fa75d815408ef875d815408efb74d8154206fa74d815408ef974d815433ef874d815408efb54d815433efa54d815433ef854d8154006fb73d8154006fa73d8154006f973d8154006f873d815408efb53d815408efa53d815408ef953d815408ef853d815433efb43d8154006fa43d8154006f943d815433ef843d8154006fb72d8154006fa72d8154006f972d8154006f872d815408efb52d815408efa52d815408ef952d815408ef852d815433efb42d815433ef842d8154006fb32d8154006fa32d8154006f932d8154006f832d8154006fb71d8154006fa71d8154006f971d8154006f871d815408efb51d815408efa51d815408ef951d815408ef851d815433efb41d815433ef841d8154006fb31d8154006fa31d8154006f931d8154006f831d8154206f8605815408dfa7618154206fa76181542077a7518154207797518154216fb65181542167b6518154207b9741815430efb6418154327bb54181543077a5418154307785418154327b85418154207da7318154207d97318154006fb6318154006fa6318154006f96318154006f863181543277b5318154007795318154007bb4318154007b94318154207ea7218154207e97218154006fb6218154006fa6218154006f96218154006f86218154327785218154207f27118154207f17118154006fb6118154006fa6118154006f96118154006f861181543277b5118154066bf6499252066bc64992521fdde7399252005dd7399252066bc64592521b6be54592521b6bd5459252004ff7359252014fe7359252004fd7359252014fc7359252006bf4359252006bd4359252064fc7259252066be4259252066bc4259252004ff7159252024fc7159252004ff705925200cfe705925200cfc7059252006be4059252006bc405925203c7f765525201d7f745525201f3f745525203e7e64552520073e645525203e3e64552520073d645525203e7c645525241e7f635525241e7d635525241f3f435525241f3d43552520057f72552520076f72552520076c725525201e7e625525201f6e62552520077b70552521f57
  | 29 => 0x6000400200600280040000090030004008001002800c004001000000000800600980100120000000048008004003000800a00a0030000000007001000400c00c0010014002009001001800600100080000040030008014004000001800000000700000140020050000004006002005000400400b000001400000d0058004006000001001c00400400080240080000000014002001000000400c002000000800600703cfe7498a54064fc7498a5403e7f5498a5403e7d5498a54064ff7398a54014fe7398a54004fd7398a54064fc7398a54066ee7298a54066ee5298a541c6ed5298a5403eef4298a54066ec4298a54006ef3298a54066ec3298a54024fe7198a54004fd7198a5400cfe7098a54004fd7098a5400cfc7098a540067e5098a541c67c5098a5403cfc7458a54004ff7358a54014fe7358a54004fd7358a54014fc7358a5403ebf4358a54006bd4358a5403eef7258a541b6ee5258a5403eef4258a5403eec4258a54006ef3258a54006ec3258a54004ff7158a54024fc7158a54004ff7058a5400cfe7058a5400cfc7058a5403cfc745865403e7f545865403e7d5458654004ff7358654014fe7358654004fd7358654014fc735865403ebf4358654006bd4358654004ff7258654064fc725865403ef7715865412ef6515865403ef7415865403ef44158654004ff705865400cfe705865400cfc70586540067e505865412e7c505865403cfe745825403cfc745825403e7f545825403e7d5458254004ff7358254014fe7358254004fd7358254014fc7358254004ff7258254064fc7258254004ff7158254024fc715825403efb70582542167e5058254216fa50582542167a50582542167c505825403efb405825403ef84058254216fa105825403cfd75d8954004ff73d8954014fe73d8954004fd73d8954014fc73d89541de7f53d89540067d53d8954006bf43d8954006bd43d89541deee52d89541de7c52d8954024fe71d8954004fd71d89541de7f51d895400cfe70d8954004fd70d895400cfc70d8954006ef6298954205fa7098954005f97098954005fb7058954205f87058954006ed621895403cfd7518954064ff7318954014fe7318954004fd7318954064fc7318954066ee5218954196ed5218954024fe7118954004fd711895400cfe7018954004fd701895400cfc701895403cfd75d8554004ff73d8554014fe73d8554004fd73d8554014fc73d855415e7f53d85540067d53d8554006bf43d8554006bd43d8554064fe72d8554004fd72d855415ef651d855400cfe70d8554004fd70d855400cfc70d8554006f76198554205fa7098554005f97098554005fb7058554205f87058554026f66118554006f5611855400cfe76d8154206fa60d815403cfd75d815401cfd74d8154004ff73d8154014fe73d8154004fd73d
  | 30 => 0xa0040010020002000000000001c003000000000a0050010004000000004001c00a0000030044004005002006c008000001000000000000700040040050050018002007000000800001200300280020080000000000003001800001200000a801800400e002001400c000000000001a0000060018000003000800000a006005000c0120000000018018001000000000000300680000020040008038012000001801800600b000801400c0020010008000002000000c0000010010070002000000000001c0000010000000001002000000e001000005800000b001801400a0030008008000000000001000200900080080060050020014000001001800000000100480040040060028008000000002000400000400080000020010028008000000000000004400c000802c022000000000c00000100000080060030000030018021006800000a00b002000000200200300040040010020004000004000800400001b003003c004004000000000400e000002c002000001802000200400080140040000008040000004001000000c006005800400600600280500200050000004024006000800c000006002000000a002000801800a0070020000006002002803000000100000040020020020000008004002801400a0040008000004000000004c000000000000000000000b8018000000000000c010000000000c00000100780000100000000028000000000800400200000400040020000000018000000003002c008000000001001600600100200040000028000000000002001000000f0008000004006001000000000300080000040040000004004003000000800c00200000000100050020000002000000000402a00100100100040060130000002001002000800a00c0028010010000000000000200000100000100070020058000000000006002e000001000000000f000000c00000d000003c0000130008010008000000000400a000000800800200500200000060010000000000001000000001000d0000000004000001001000800300280080100030008014002003003000000600200c801c026035005003400800b00000200000010018000006004002000c00200000000340020030008020004005000800002e002000801400c0000008010004008003002001600100000040000010000000000002003800000200100100300000020018000006001000001002e00000000100020060030000026013006001800c0000000000014009000000000c0090010000006000000000000400000080040020010040008008016000802c014000003000400e005000800400000500f80080000000038008006002000801000e006000000004e000005000001600c004800800a000003000400200000100100020000000004000001001800002e0020
  | 31 => 0x4004002000002800e0000000020006000005800c004000000800c07a00500180080020010040000000001000001000400600100100100140000008000007000800000600100380000020050088000008004000000c00000200f801800400a00180000000030038004006004001000c00c003000000000202e000801000600100980000040040008000000002001800400e002004000c016016002801401200000000000000000020008000000000800000400100100080120000018004002000000801000000c00b800000800b00000040040000018004004007000800800000200700200040010000010000001003000400c0100058008000002000000c00000200380140060050000000002000005800801c000004002c000002001000000400b0000020010004000000c00800f001000400c001001001c000000000802801e00100180500000010038000002000002000800e005002000000200b0000010026005000002000000000000000080060000004016005000004400800200100140020080018000002002000002c006000003800400600000080000000010010004000000000000c000003000802c0080010000014014001000000000000000300180020040000000004008004000c00400400000000000000058000002001004000c002008003000c00400b004009c00200d000000800600000380080000050008000004001000004c0040010040048000000006000400400d0000000000006001802c000000002800000c001000001c00200c00000080020080000004004003000002000200100080140080030028010000004001804000200000080000100030028014000006001800800a000000800c000001001001800a002000801802a0070018000002000001000000400100a800801e0000010000014004003001c00000200000180060050028004038001003001c00400300680100000060018000002001003000401c0010018000000002003000000a00500880000020000000004006004002000000e00400180380000010010018004002001001000c00000000180000000008018000005000000000a0080030004002003000800403c0000008028000004000000001c002000000000001200480240060050058000000006000000401c00100800040040000010054002000001000000200e004000000000200180000080160008010016008003003c006002007801c000005004000c0000100000048000003002800c000000002000000000a000003400e001002000c00200000480100080020008008000000000000c0020030030000012001000000401800b0060000004000003000800000000000040000110008008000001006803c000000000000c00800000480080060170028034000000000000001000400c8000
  | 32 => 0x13e339f8000000000000010ec1bc43bb000000024d0000362920a4cf847a0e180003ba01591c78e02071494a32fc0000000b65095400000000003ff86ee4c1c7d848dc441421000038400da40f41a60c540002af041711c04e720887894298000000126b3d1c1e14cdc8d0388c3c23a90000404c2122f80000238c80504080003ce89420000e2e09b400000000004d687440254a3d000000000009d13b9123a020c000348c1f42ba800001380000a9800049a8ed7288025700006383a5d3010bf028b2aa87a800000004c7cd4502a4636350047823a0f9e0001216000069925380004f5489f02a810f2de43520000f5c0224000000000015fc0074aa081e000000000006682bfc5ff0000fff4b34d6b1794c5518b47da4300a8414ac9730990ff1193c75038d4e08000066f1fac00000011de01883ce0001248000057d476506000000002ae0000280c00015f86db00006c01d70000000053e34a44eb38a41851b0405a03b8fb600000003a2010b00000000cb46c2023c8f70000000000000000006b3000034d2d9830413f0bad273c0000000a3700000001cc4e1b253c17c418ce5e2e7d02743985b821b013a0000a413fd04f21500ab3000066e00000000000bf727100004a510470284de24c5d11a207030c33a0d161b243eb161c0000000008006008000801400e00000b800801400200400000020000048000008000000000400c00200080240020080000000000003000000000000200100180100060020000006004000800000400100080040020000000028004003000805c00400101a0020006001004800401a0010000018000004007800001c000000000800000b0000004008004000001000001d000001c02200c0088000000008000000401e00401c000c0000000040014012006001001801e00000b800000000300000040200000010000000002003001402c0010000004006009001002000001200f000000a0000008010016001000801c002000000000c00800200480500080000008018000002003000000c000000000c0000000010034000000002801800400000080000000030040010000001000002c00800200080000020040000000002000000801800c00f007800000200c000002c000004001001c004003003000801400000900000060000000004006007001000400400f0028008000000000004c020000001001000e000003000401800f00200140020000008008024002000800c01a0050038004000001000000000000100000040000000010000000001001802000a00c0030000012000000000400600000200180000000020018010000002000000c001007801c004003002800400c00000000040040060060004014000001802c0000010010010000001005000000800f00b803000000100080880000000000004022010
  | 33 => 0xb000000000000001c607e700005fd000000000000001f913264c2c4f82bcc00026ad007452800030ac0002e54000000054d000090930893aa00011641ad125148200003200e174b6d16f2e68000000072f4768b9b0000f2426e8bcd0fa4f0b0000000000000000000000000000000060200000000000000000000000000000000f4e12646ea1b400ef249800e2a7cd4f0000fbf00000004dc42b9379901230c4713229c0f642a8000239d36900000001f88bab1b2c0004f18000175c19304fcc9c4c180002748c9e021c3b804eceea16380002d0854700e109a48102460000c93419c0000000545000023b3b10c900000bf9000041900004370000ef3000000000c842715042050000000000000043747ae2e883ff00007791604000000108536b8e96325c6a526343450cac000000066900000002d786ec000124e4bfc3370bbd135000109b0238fd44b742964cc0d7d3ec400031a497421480080f509c336d8c864b78c584648c7e4ddd3553cb0f2b2fd4ed04188fd625189e4481483e275d2b64b9ca7b2d852401b9400046980000b4c65400000000000cf24490b19243c0e2000000000000ec000000000009493608d1d0a912024dfc000000000000000000adc00025000000000536397000012e80001388dbf291415d0ce8e0343411e5253400019648570d7c3e547b42e83fdc36604300001becd3a28bd3094be01402fd8c714e546d10000d2a0000feb2768e33091cf64415000019183dc00000003b143ad3a1d1bd37a000000005582aec6cc00004d5000000030740000e440002e5800000000000bd41ae1c5c000000000000000002dfca9e000098a39d01d3377c0004cc80004a8400005ac000000000016711d3000000000012ca0000000471433f4608b502c693330d08451000000200000000c708d500005213ae133a1e54000000000000000000000376000136a00013870000c9531940002bb104b09ac000000061d00001b600000000000a8d00005c500006780000d2c000000000008963f8874d0000000000000000005072d68000050c986000065135fc00015dc2e2251d22038846bc0000f29079c0000000e4b4bb4f6a0000000315800041541580000fd9000128736c00003aa0b3b00000000cbc00027880000000f463dbd1c708b000009c882d1228f6800011c22a1c000000122330ecd73451c023171d25c2e611344b9034f323c000338c00000012a43aed15346900c52c9d15020bce81100517c21a81da1fb8cff0000d152ee40004430bfb0000000136889837a8ae50bfc00015c06d9000037e378008c00000000b405e749a4c5a06380001dd4f20022c91c02b120344843670000c1500f0a354e147a4000000014dc00000012ea00006c4373000044500002bc4f06360404c348807700008ec0000b1312f11b64c48c12000
  | 34 => 0x1cb6d00008ac0b3c0000e706103c580004d80b6b000000000002c02f8d3540154b0c0f885a3351cde410a13a30b9c0000000b990000000000056242602d10d5073241681242844d861d086d718002c81ac0df009040000000d11278c21e0000000000080c17440002fbc00040fc0002f285cf00000001d7487937f40000200000000000900011c300000000000bda478000029a0cba21e800036407b921653d24f34ad500002540c8527d359c2712b5843d4164df30210fb9000005c0000df53bb086b4f58832067ceae000139218fc00049300001e4c00021583fc4cb0ff939b8d270000350000000037d800005040000000b1615d000007d882801486e23ef48c100005c83f08f9a305cb82032400001187232e90000078c2864ca8ed923700a61c880664dc8fb700006340dc892c0000a5412c445f094c9e50b7c7d714b93502854531403c5b54e3122d1b34d2405583c517d0afa309c6124010237287131900003cd40e0b4e04c0b602ff477e3340799000112600000001c9c333011c6f54b640000000000000000000010804a08000000136824f0000000131b000000028d12c248f457a16d916e000000000000000000b4000008000000cec31e81ef21fc0004a29272214c28100006bf2df921e369118528acb0b2d1864d4dac8401dc90ae3ad42b2197846f33ec07208b45340e0c61e23d05b32b10beb374c00028b00003d6c8bf352ca4832e0f6e00006cf3c9cc39321d26d2ea86df0000000000000000000000908d4e00005a513900001d7c000000042000000001d380000140c292bc8c341f6c806262c8eb35b0eda168868c1184b2f4e0409e33213700000000425c00041ccf0f00009d416740002f7d00e00000003e749fc00000003c2800034292802084f432c4800049840004c30be74140fed3af8d3f0000f3230b47450000000000000039e8a383b013af27d0ee00000c7f4eac5940c5c00023e519d000000049280003a600004530371000000009240000000c2500003e643a8f140000c890d00656000036a005c0000001066000122e00003a91f3ccd50420b4f09bc00022b8000000110a0294bf4228400035102700000afb118d09000012270c4930a4e342c23438a740348000000053003386153ee903e0000cfe153800000008c82ddc3341ca88372ed80004a187f323e8000272cdec0db4df44b0442c000122935ec0003a78000446437904540003670a7229e000000011033cf0c4008c0d2d46200000000d3e3dd0ffc1920cfc3ac459f4694b4108fcc700000eab000000002f0b913a8c13905e800012487ce2c500003e40370365400000000003ba4b6c46ac0000000000000000000006fe00012330b500000000f480000aba4bac1fc082cd410ee8dda41f88684c20f69000000000000004d180000bcd1c816180f53ef888
  | 35 => 0xd24000137d1c90000776000000000000004d44000230cb6a00008f024640244184ea5000079c0000000000019b396904932500c00000e1844888b60000cd72e044fa000118300011f5000023e0000000000106529fc000000108711f85df00013e000010024bcc44b1a493673c1cbe92718bc500012f206607151a2491600006fc00008300000e5b41143630000ef714143d90b551d7266135726e40eb2c943ef156c4b624b915a27a90c939a433e39e400039d81c81168d9e0c5036402405a92b9c0001ab4c5347846dd15293d815200510060cd808d0fa70000293063002047a018d01789b21a74b8032441610000b5b114ca69452d23f0000763000125e3040dc7037092100002f400000000000000004895f2a0c0000000dd500003f0000000002800002b0000000000002e305da42382c3000000042587002378b552aac2a013504681218bbf000000000002ab439c16d0000cae00000003fec00030d400000000004c880003b7c551000000000000000000000000000000000002a380fa3170b3101a000000010a100e48390ef0a062b74d120d84bb146b416319900414a9800000006ca00003af2f54037342400000000004ded15125c00000000000254cf710000acd089893d0ce469800003ca18bc0000000fc8040c00000000000000e371408a1200010a4000000000000000000000000111f00009a00000000249c0001c50000087048800000003664ace000020030983a10000d692fb503b0000a9700000000000fab0000cc71dbc88a000000021d53b000006f00000000000043c000087141a8000000000000000004e380000000000458cd141a2cb18000052317840002c7000041a52071438000494018339bc00026b8f2326680003090d83000017610910f800005e600000000000850002c0000000000000000049dce0c00000002a50c61180c00000012544aecf783a511b1048c56b3f24bfa24c8000017c2851d880000000000000063500000002ef024c2af40003b1c54f0b780000ab884d2448f500001375039cf371fb11930000000366c09300000004730000000000000011d509b05b933ac8b829644950000d300208ae8000000014c89d800012300000ced2ee93b90d60f12312400000000063cc431e00000001f1853f01c41143f6c00000003901f580002810000000004d45a40000ae8de700005fa2684000270874b36a0fb040c48432de83060000c0d23cc39928510af0ec0a533d5c489308045d2ce901d3c3104c00111070000b013228ad44b1139044b08e90000000000000000006e9000072e00001ad0000c5700012bd069c8f81904000000089e00007c80000920211c13e000000043452d512080cc4c0c00000012b00000f6c13b8000000030b0b84c9f429479e068863b00005ca00008613d640000ac003007
  | 36 => 0x7b419a351829a21785c6075d38b108c0d300007601fd40000dbd0a814f00a82d7c0050000acb0e992c5000113939a8000000000009e8e44051424a00009d921f000000000000e283de279873a1dd00001ce501a0a5ccac029ccb444f4ab50000a3900000d903740003b481e000000004478adb48a80000000000000003136c40000000000000000000013bb304c0003c1400000000004f08b3344e0db3000049f16100001a580000000000488800000005443e2c0001540b6e3a68f4d00003590994fc73bbc39839cc0001d187fd000000008b800020280003fd90323388d3900000003cd490b3f600ab4b387df1680cfa0000b6443945ee4e589db21e075145f4f672e3932839940002248ab934f0a602d0c0000000cc90000d4d290cb08000000013640002a980ba177434a35b918c3ea400021306e1247c00000010103df8cd60000c014ec8000336c204000041147483c7363d0b20b18000000135d19c800000000000000dd9296085b1240f800000e25160844a268c0001a6c438314400006e0c2a06f40001c2c000217534844443783e387c44474bd63de46c74de476a4538210203831f26a00001aa0dbd3cec0000000d8d000000016692a029bc6a63b300b00000fa12dc8fee4a709ad06053a7261ca66000135c00002d232b40003bc800000000004d30430438452a31a0c4c443cf611654afc43c8000000067a23100002d5c000000124700000b700000000e247aa0000b68000118b0e081191c18000291c0000c940d800009f50824000000034409a4f4104d800000001bc2d8850f01cc18900000000000000000023d4368a05048080f12b48bc13fc5dc05c8e82051cc064dbd3cc34d8a3232f4d130608de90000fc01cf4ef91adc0002e70f760600c6f18985ae34640004be4000070000032c86e80f4800000002d8000000024880000000000000070300000000000eac00000000000e3b07fc2a24e6c0000000000254521c1088d7c0000000300c000185c20c473c0000000aa500000002c451b50000215209072c2ed4000000000000000000000e4746e46132e3c39535f81100000b060c4000000007284d249dc2a282160cf50fb097848e3dd458b32343a0292447320986872fa80004658f1d198cade0ff80004e28d100308000000117942193d90000a6b02d47f22c3cf9c479d06c4edc96f0000000000032a00002442394f2d134cef103404c14b184f915e4000340412530c889321700000fc80000000d610ef855c00012900e68d2e0da52f127280001af8b23000119c000084600000004564000437000047ac7050000a36000058f0458000000115605e47be42fc3c119ed0c8333c000146cb0d37dc00015581214f5c8d112711a1357807a288cb6925f4bd70000a3a00a05de000104f00440000000777496c000000021a00000
  | 37 => 0x6071fe4a16080cc470000000487cd714ed01d50000a5d4a350511d1c000000000000000000000b8600010f14a5c000476c00000002430078000000076e4b4811b169d07f0000faa0000053129400000000002474ac7378c1cf49086453738f58438c0fe000000010d80004f10c640000b541b5907847740004bf000000000000e2c4771c20a8823f000000007cd0000000164400005cc0002714f4909a8a0e16f8e262b31271183d2a51a7c000000098100011901e98aa12a54000000064400000002c88000000009b18180000000cfd3d8806339f135308e400012fd0bd0000000125cd6f32dc6b6000000000000002e943e020a457c0000d7213b48aa46288692830ccb3df417f3530c1100009b04c38000486cf4025f8ccd00000000000d5600000000000000343c2760dd402626fc43b0534770000000042280690000ec2115531002b4000000064b000000008bc3573e48f7f375c00022005d9000000025887841db4f263a188bd32d4ca22a591f7000076c0288cd31c3c71f0000d3d3e580003c050111d3018a3810ec82df48c5147c000244539c299d08c012cccc00001c33e5d19a1da0dc33ff40000a1096b1e189b615e078d1af534b04347800290f980a9c3322f001503f1411c26b0c1a0ed4788455cf1041202313e3000002d8000173899b00000004ed40000000000375879a00000000f3c0d103e400040a40000554f4f2910e5700004a800003e72de1279000000000005c4000027816c4a9d411802d188c2ac387d1654848000363049d47e056a1f2867d0000e392a1809a24e49e700002fe00002be34c80004e74cb33e080000000279000000009145f8000000005980000000809000000031b927c000000032d8b2432a051c39612460690a5f0968aed14748480000000000131c31d80000000f81000000004452a324c0639000000048f00002fb8e7d3140e4c20353431c24c4e2048105000000036005420001003000000046b0d341a44a7d4a24a7637004cf154903911780000000a6245f90d43a5518e0000d70489000000002dd2a8cb384d6c000179095d3f9400c492c3d00000000000106d000000000000000000e931fdd052000c0000000000000000042d52982654f1c0000e1919e48033e1cf020000000410c8990f58ac3083d359420cefa0000000000000026244e02ffc00000000000000fa30718ebf0ac4572088c60a0000e8a1b7017700008b5129c3d300011ea39046d812e12b50f312530c9cce43a312ba23f88ce18a08a800008e644700783890f2f0c04000322c000000040a3d2c4804f7c8f209d0fb3197cb8b233cb5818587d0130083b25b07f836e02c529e80001600e1411c872b00000000000fea39a099c145ca5a3e4c34837acc0e37087dc11f02560bac03e2a14b36194913e06741ee16b498c306121d3
  | 38 => 0x47c8912d348e20db018b087cfe009f80004ce484f37e48010acd0f926401963f9ccf306e4810116000007c00004020fec45811a22f88915427800031f4000067000011d4dfe2c38e2b2e98a6111a92b346dc38046192c90000cf414900004b001f137ec3430c90ae0000085a00000000000000000034e2b8400000000e600005fe164cea9417862b2a400fc0000000000104a4c952fa3cf4c3e22b422a0fb800020cc09600002aa408134d1448122000092a0a0834c4e010140f4400007246b224200003e2135604dca2449582bb24d4eb648309543db4e9000000000000000000079000007c917c0000000000000000000000e8b38684561c40000000000033b8b90402d02f197513230f0ce00000e6c3750a08244c0003348000331835c2d2c00010e93be00000000000ff300004450000000140400030b083f00001cc000077c03b40000964ddd484c000000012b00000001e1c0002d440000478129444cc2e0000ac900008ff00000000000000000096a000000029d42a80000d1800000004ef4afd326c00002c400000011ff00007653b2800010510fe000052d28342010a0d07b4ac89de00003fa0001056000000000000000000a7c000028f07cc0002c800000000aeb00010f335a80001d24c300dd000000001fd18e830e40151b800000000000b2b00006ef1a9d2ee016046b000025f3d989413f784d1376c7433f8ceaa3f54000000051541e88a30000000259cdfc3660465065c5eb0fb0ea036893781989000368ce781444d5b31344d2131467e33d80000000844146527b2ff896e00013b3257095511e53ac2908b280000000365098e3680f99307c8a62ce4a8c2e140002e9c5750000000000107547b07b105d06d247d8a130000000124400000000e82dcc6ba1a4cd96031c23c1b200df280400043580cb47ec58307440003b6c00045cc1b516b000000010ab10c91c12c84cd900000853e0c5331ee8000456c0001a3887700010c10af40000e5000044b88a000000000000b26000000026a812a4f140000c4c00000007640000c1b0df0000000010600004fb34e078f0000b2c235133f2d4845708447b621284c73b2441239ed1552aa059624c40000000766407900a000000003191df2958000000027b0d743114aa456516340000000000372c00049a00000000e85000000000000130000000000000027208700ec4bc94d3c41a4c9d2e1000109900011d100013c3000038800000000000000000125235d400014790572a882a90001234000000013bd1673e440000001195315000003100000000ea70000000325800000886fd0000000000002e3698d424becc191a289b516f52321ff09381cf888708cd28e10140004ee00000000e06390c000000000000009c032602b400009993070c3f3f411974f4067c2b7c3382918f9f0000
  | 39 => 0x51d44f748ee269c34b225c79f103490739804cc14e800000004de3544cc100000001b50e720000000000037f00011040640000000000041dc43133d4c744d04000033c144455083d000007d4ce01694a3054b0000db20000fe400002fb0248000000000002447a0086400014302e52f1878a2fcc0994cbcc1e00013b60000f2500000002f84e2a13840001a0c00000007480000625000137d4c90ce111c4566000000000408830000ad70dec000417135e39882e445ac0252a040001750884057ca221a8917a289816c16d00612adc3b93ccc0000000e6b0bdc6b12b1400032045f33d747bb00007ff00001eb000005d2cd4fd31ec92aa0000000270400021d8fef0000160000000000002a500008ab122d19839653ca13a000000003a70000681252d2620000000285c0004ab40000000c364d38834072c000197000026440002a6000000000004b2c6a00590ab2201c30702e01fe1318fc111b80000000000252023509200002cb87560000bc70000000000000001bc6b9000075732a85b20000838186c69e13cd0b11fa4ee223844d848ecb3735d00494bd49b800012f43c5c64a000000029cd2af1ead1684ea44e60000415169006a13404a10c010bc03fd0de1ec00be0e48d9a4f680270fec0000000000440000040f017e000000000000002e84000000042607dc042000067f3c2000036d400000000001e9cf60431000033780000eb885500011053e80000263c0001a0829436a50d519840002d1ce2d13b1284000000027f42ea00000003d1400026f466d264800025b400000001d42874cf825e000000000004ba0af00c8c000417d1ee00010e8367416f0b3097c1fb435a000000047c04812f90467000113b07b4e9f0001363442c8170000000211450a15c459242892bf48005391b6902e42b43fd0000f3800008db1574a654d0901c0fa0483000030f3d48b3c17d891b00000000000a4d0fa8e073f280002e3492f41bc16838346710e307b342dc35e2ff00bd3000f953d94e3024a003302cc1e41a3474032900f71c94a5c04cc0000b1caf618a87361e8d1ef240462107a422b04380001e882c9050931500004101f30000166d3a648c4ee14b9802a3dc071600011330000000000090d07106e600003f70fd40003c846a43b4c0ca000071d000139f0000b17347d33b119918400000003eb800009cc00000004f500009a90000000000000000001b100003b60000000000000000000000000d5a1938bbd00000002a3c00043d4653000000000004dd13940000e5c0000000f18000086500006ce08211fe48e00000000000000003544540000f1800000003d80f10957000099e32812b146fd0db00000004024694286909c3a3d09d3a3462010bc00049fcd17166065839900001dec00018c415e3f704af1a010262c013522ba4c60233459e
  | 40 => 0x4adc69a00000000000000000000000009df0a6c0001074c7345a86c500000004e68000000000000000000000fbb015843f1020dd800000004e64000000000003f53e2000042d0000000061cca643b43a245dc0000001293000110e000000033c02b533940002f4c362408cac2093937a1be4fb814bc8c0374000000003c002c886300002020000000000056000000000bc4000000095a485000000013022dc13c033a4000000070a4d287b7382c000000028900012be437c0004058ec1000079200010bb0e78b8a0000c593c7d1990000c4b000076b36389334a884ce410400000000000000000000133400000000000f73246800049e80003ebc1ea39c0dca428119e0d046f447cd3e41c64c9900012181be8f8d29e46a32a2487412d4cf736e524f3bac000000000047583852a6c1ca2c287330c6d1060efd1251dc49eb16f112d3bd82b62a9c30543fd14f3abcd2608e074119083d51358707310513645d800000000000000da100012cc4e9000040d40004864686000099d2e5c00036f8cc50498462000000000010fc420928306949cc0e389020e1cf3e2a0056900000000000a1e29dc00f3114d1e0888000148800025ec000208000000000000000000449c42a2f10b1e00000000400000446103714b02f24efce281780831223ce3f289415c000027d000052600008cc391465a00000000000d880000000000000000009ed0000000314889c440855e0000c9a23483a439c53830000e3437bc16a4a207f43c4d12a46f82134854dba0000400000127331b0dc41230a990000000301cce71fec00031980002ad12fd28b487d28c12210204b5d2930b92010032e006c10a000000002211b336d000047a485f0000e8000003db000104d04c80f035403351b180000000000149400035e40000000a8b0b2c32c000106804f10eb2294dff10e4000047400041d8bb006205cd482c00000001d839583510000f04006493741d0b0936b48883550d3518f136d15911af00000002560fc307481b00001393000131e43380000000000000004f0000c4200008bb099c08a195ca2700000001468000049cb4c0be80001ff800000000002b4c05b1c712d0169800019cc00015cc0001d48355383cc02129073f0000fe80000e8445b400038b00000000000000095205d40004b943ed12b0d2040cc01f0000c7c4e190b318341aa0000b8319252d83918ecf22bc6ac1c850cc317450b0304abf358800033e400003c40002054000127862426c40000000f7a400400000e800000000001ab800034ec0002808000000000000000b4000027c000007b3ec86290000559000000026cc8ea3bf05270000148000017b0d9400022e43ab0000f533e94000452400046a13ba00005d006bce9d2af93d34998ca90cc48903b749be22cd27e000090006541b32b2000047e
  | 41 => 0x8400003549761c080003d78429000000021600000000818335000019008cb17b092b4df8dde0b293981518b76258c0f417c93a10350c0c092c7b4000000000010be158c00043091800000c0a478c9f0427c112361c0004ae13444980bde1bfcf221844000470000000007d118c013100008e0121c00017bc7260000ae3000081a48e507922d106b00006740a2000045086220000000000000000004ab0e74903429cdb710309823e1400000012b90000eb20270a510000bbe00000003bb8d641efc2f92f2c09d4dd11ae00009e0083886e49250b8039015248947a14a2cb711c8051806fcc212c1d376000027521bc9e800000000000b6f0000a0f0000346000064715a04060e3d20d4d88e5100010e400011d8308cf30101c8820e6c6671c488fd1748da512ec00001f00001450b8825c800000008641664000104c91722f81db3338f0900000c82d640430000caf4a14fac00000003d5000000d82ee1164ede3e503df1ad46500ab4d651850b75499479808a4000000061f388000000004331cd0729256d20634200003110dc9135c8dd1a70cda4c7400000004694c0077300007c70000000000000031ec14e0000c383ddc1dd463400a2ca536e4db0396000000000001d93bf800044dc83500000002c1082a06e80002c540003f2c00000003f40000755472d16c44a4925219ca7011b515e32ac000028c00007e0f03466c60411d8ea1317c36b2fa0567424c0000000000000000000009ef20b91012010d5d0000000422c0000000c832a80e22364400004a0929292800000000000000e773b2c000000000021c809f1fe80001870000398c0c3423c0704ec400000011e2085c0003f1821d000056c00007111e3800045ec5161fa00003c68000000041c0000c2f3625236490c000256400017602bc10f8ec349b00000000000000001518312f0150c19940b45c200004c8175826624d8d53055c1e54c103c930589933d8c03b41013ad2eec0002ca800000000004898c840c0cb890588000461cae23494b484840d7719540004b6904e452044323d800000010442108fb52ecc2202c080002cfca003dc8f5140d04350a1c0000000cc40000329294800032f000012800000000d334e50d2b4dcd0a90000000000000000012bc44c0f9b00007d5000000000000001a4000018b835b00008f149d0a3e1f08ece17a849b0f5c00000005cc3d103c34e10000316ccb9428c28d3950fdd1aac9b72be47b800b05080b04ad03b98000000053b2364ac100000001f0d1ce11351c63f9875927e08da3b60dc64a04d9728ccbe613d8000209400020b10174c8cf000000000000000000011620001364000053516a12ae0000b870fe4fd741c400009809500a8c9f727c4a4e0c353ce00000d600012df28240000000ef009441a02a44de500000002ebc000000000
  | 42 => 0xb22698d7a3a9906e3f4907200000002cf80001be025b0000e7f16410703cfc00040c0dac43d8ebc4ef127500006052d100001334065000017d4c684cb0000eba00000602ad8bec11fc1182fc0e4d0000f4c4574904301000000013d400000002e8c00047984490000bb81c3139e1d3c3cb025c8df05c079b248cba94d0081315ecb63311829946a881928c4c63445c2dc1f84ed42460b9e00008c20f68d2845d400030210cf303cefd15689f91abc9bb0000b56000000000000003f380000000df11e582582ac518105b851000009b40000d76113ca9a00012a73400836226c6660000000469c2954b4c17800587853b705ba03948860000bcc40640003ca860e0000a713c380000bb11c40c689940fe000000007ea000021418cc25c15bc0003f680001c900000000000056ce4a0e8d14007ec2ed00001493dac04a02ec0790000ba007e400034305fb409515249600000a000000a745f90000393000106400002d90000000225000000000004e5cd7832484503e3d29a0001267357c0004c14000000000004d4101000000000012592df0fcc0ef4a1b364ce991a5c4c223ecb34355400008283a52c0c00000006ed48bc9fb0000d63483901f3f3cff20000a7e11b00004c60d683b54d844c3c00000003840dccffa000026800000cd4ab000000012dc000000006ac48f038001400000001f643222cc80000a787c548a0113231cbdd086000021380000ea03e1153132000000003274000000071b2a4c07625103b400001b73528000000097a190d38f0000daf2188d0b000000027fc0000000f340000576241508d0afc13d11f41de1f750e21dfc9d31aec00006787044e940001f4c4b44f1c5bb00000003a0c00000000000000000392001d00005cb0000000000000000004f40000000000004434708660000ca327846e317249c700002271ce0e0e3ed099f01f90ee000030a212c7a54420bd907d489d1a54cd11e452b44b3c4250b1022111084981d84e5f054ca6d34682cd295c2363014ca70be02d63f10aa9394ca21214400000004162f9400001b07e50ca0a4f025103a3bfc302208c4ae22546a14cc481131d46270cc0ddc3370cef23bcf8428650c720e879729a92d1269410400009ee178cf2832087582f20c4a3220000405400000004ea000032000005c3000028c00003ac3af510d46e80001d9ca1017dcda700000001b900743c340000000e1546f00000000cf10000000000000000000004e8006700000000000000346c0000000000199445b48449cd3d6901b46c8ad127e8e1d30240003f349710000000000078c2b680000000484193000014f4956000000d38700003acc2ce3e9020612a800038c800043bc00000000000e0403f000000016c0000142414c4644000052c66b015000000000002a48d60000000046ec000000000025
  | 43 => 0x44019400004be00011411bc80001328e2f11508161cdc1cd141045c24e841f384406d27b0000000000037200002bdc3f31754a641525276468c0002bf84940fc40000e7ca4b0ddcbf2000059748ac0002b708b236ed0c540d919400f40001868eb00000f4247f0af400004604bd8000000136600004bd40a000031207b53c4493f12c0b842758dd237e00000c21314000105d198000000000000abc00044a040300000001bdcc852f04ed600013913a6c000000074a0000c6a1cf0bcf0000000231921744f0a82000000000005d3144c0004ca400000005031f8c000000000030e800000004e9000002b00001fa000112f22240b928f0000000000000000000d4c58c42550ba281c2523924bd20000000000082b422055317a10c322dc9804c3494c1434000362cdf2384918f0000000093c0004b5000027540002b90000000129b15553c92450735448c0004b2086d23b400016bc0f20000b1f2724608126867038786371ae13cf02b8000000000044ac00000000003d54aad269000048d4d572a90000446ce4f00001e635651442edc02913f82f63e290f700bc00000000003ea0f15000075b136cbf128600001c6893b2430dd12cc0000111000000005e913c12d749b833c00010060000dab19d8000000044e26113652be01a10da0bf8202c31d0000000000000000000001401158038d0fa00000d724380752d4c00031888d6350c00040a8e36330c7a927a40000a600002b3c000000000000000ea3a44d583940d02397415a49c06f300013a83fc000044fd2d60a381a84cac0000000e4e16ace40108429c000100d20207300770c330c601be0c980db0000e6100011610a8410900000002978dbc390908106a44dc00006774770000357000000013cb28291702e4c00000000af000121a4a743b73df098542500004d1d09200000003a88cdf0000f4a2738d0d2ed013816dd32e1f9812c4a3c4fd1f8124418612c3432c49618c8e6740888ba0b984021cb41d647e9053000000000005c1130c6190cd90f4482488131dcc281e5019112e4d311f009af3f7d1743a702e3176d15f4380000059cc790000000000000011480000000262128c70d00008f517c40000000e55000000000012ef01fc960000025009dd32d22350ca3f8449309b80013bd11f1102400000006a9063c88e00000000000b9d0000b100000e381fbd1ca0000e6626583dd31ac0000000f563add255196cf361550000000000046a478b10d0000241901813c4b453bd4c7806ece1637840004a442b800000001d6800028a04c432ec4181d5000000013111fc114521500000000000155d3ae33993a249342db19a8000089014a00000002b28561000125f000097512cc7d22b9838d00006011c0400008c81ac47f400013240004c840e14c58eb94f7000032942fd068c8d800004
  | 44 => 0xe05015c58800000f3000000047900000de8c67000000000000000000cb100000004b80000023514600000003ef000000000002c6c00005509f33a390b6000000000012632bd41d03dec3b3000093e00000001cec0002288bb215b8ed1000000000000000000d071038c1441608ca000102b31b48d3310c23a3300b9416249103800e090b80e2742e44b71e0856d0000d2114e08144d603c82cb49d046c046422c0945361400016a806b37b80000000efb22a400043646de4990a6313dc01c1de004800004a63fd40002b1933d000001a4cd400006488272ab8000367c0002774a3b3a480bf01b8fa24904d050000a4000000000000bce1f507bd000068f24905e204b8000483cb5c00010e9000000000006882f6c00000000001700b050000000000099721f8bc239b40003a240001da40004d7c14f39482f00000000434d1a0000000000009643ce4000000081d182c7af00003b20ced17f000000020f0000000040b0000000373c4400000f1b38e89bc1bd85fc00012992cf40fb29b0aef4f04ad900008732ab022835b51f22eb024d2dec4460ba4ab01ef04484b8cd521a141461b547f63b3425d000013440313d110112e92f4400049688d725981df1fc437d2ea000039d40004598000000000000000000000d0335240001b0c7cb00009f200000001d4c0000001189138ce3c424538818f428a0000ca14d14d060000cc200000000000261000000042b0098384c00000000003328c0b07a029017d40001df4117000047b0ea847434dce0a0a48885081c0593e18529103c4474459178000000000000000000fd100013130c6442b200858a24286d30000a2e453400000006e000000de4f78000000000045709650d1c000000077a07040000000000000097f00d058500013db0c24aee16fccb042c0b4a0f904a244c400031791d00db92fe000000014a10d81e047c14cd8c3d19b133c491422500007830000291000000000009773be027f3b9c0004df00f80000675098c5a10000a5b0000b490000a3f229107d0000dcd1d789830000f8900000000000a2a2620c8e31c81074bdd0b42f0d257450c00000000003e98fe949bccdd27f80004a7c0000000dc11a107ad3bb400047350fd1bad2780000ead05940003b8c7ac01912963c7889a35982d744e93c82c74fad07c800047d00003d7c44c1c381c22f5063e25a0000000000018b000038c400000010890084000000052014192c705c4000000110940b00000d58000206d3613ad09f643c0000000000000009a222c53e14a480000000000250c00000000450000000000024000000002b48daa046800029b800000000004a54000000041b3cb800038f50cd448000007380004e2491e0000000000000000007de341000034bc000435c00000000000000dfa0000d4845c40000fd8ec64e080004
  | 45 => 0x218055f25e4bd81234dc543480e9121523e210412f232442e0f8d19f207c84906184a92dd12ab480400033a808621ecff80d8012d30dc8e40c581b44a781840000a50000122c282c00000010c600000000b68bd0223000000006e738f86aa295420d0788f194448aaf287d2ec32f800000000004090a9c416cad82d9c1514b885ed45c829f497421b00006093230c4f2578e01000107c36481ec25a4ee51078bdc1e7504206c91b44084a29000092d2eb8
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xd38501d1654400f17d0fba2ca880030fdd474595100045fc22e6b2a20078bc845cd65440011df04b9aca880323b20973595100065c3a6e0b2a2000c3d75d53644400156b03aa6c888002a760c54d91100145fc3a87b22200087f855cb64440070f90ab96c88800237e0d72d91100146e41ae5b22200387e87dd56444001878ebba2c8880021fe15735911001c3e42ae6b2220008ef825cd64440191d904b9ac8880031e1d770591100045fc3ac83222000a3c85590644400147b09b2ca8880063d21971951100063bb2ae32a22048d70505c654440091f10cb84a8880031ed9570951100043fc2aecaa220008bf845d954440011f700bb2a8880063e20076551100063da80ecaa2200787c87595544400f47908b2aa8880b31e1c165551100247d436e0aa220018f581dcf62440070fd0fbaac4880030fdd774589100061e3aee8b122000c3f751d16244001878ea3a2c48800a37a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100043fc2ae6b12200387c855cd624400117f08b9ac48801e2f21173589100046f438e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b1220028f8874c162440011df0eb10c4880123e21970949100043fc2aeca9220008bf845d9524400f17908bb2a48800237e0d76549100146e41aeca9220048fa86dc152440031e90cb8e84880123e21970d091006477414ed2122007aac8458a42440091f10cb8484880021fe15765091001c3e42aeca1220008bf845d942440011bf06bb2848800a3720d765091003c7643ac4a12200087f855d842440070f90abb0848801e2f211761091000c7a432e221220048f8865c0424400d2f10ab80848801f2e191701091000cf9402e928a2000db240dd151440596e100aa2a2880b2dc2015254510165b942ee0a8a2006978855c34144095ae0a0bac82880067ca037550510246b8286eaa0a20018f4865d5414400172b063228288002e96086450510005cac1e84a0a2006978855c321440031f50db82428817e5ea1f75501103163c3b6eaa022060c7b761d540440c18f0ec3aa80880034e1d764501100059cc28c8a022000d3875191404400da70eb2a280880066e21d54501100055c432a8a022000d7075dc540440013e50f28a808801b5c1d65150110036b83aaa2a022000f315454540440099e0ed20a808812b5c1d6415011000d7843282a022004cf0765054044091ae0eaa0a808801fac19141501102c4bd43eea9022000c7876dd520440018f0ec3aa40880123e2197448110034bc42ae89022006d687594920440033d10ea9240880035c1d77148110004f943ca29022006d7075945204400dae0eaa8a4088003d85495148110256b83ac829022000db3749052044091ae0eaa0a4088003e85094148110
  | 1 => 0x8cab9e849000327d9173d092003e4e322e7a1240019ea80dd642480018f0cbb8284900063b21975509201f6363b6caa124058c6c761954248001c5eca32284900063b60b73d85200043f43ecab0a4000c5c73d9561480010fd0e32ac290003171cc65585200061fb2ee8b0a4000c3c65dd1614800187eca3a2c2900030f19474585200062fb2ee6b0a4000c5c65dcd61480b18f4e0328c2900023de1d611852000c7c404ed28a403ec7a70d96514800d8f0cab84a29000e9b21952545200043fc2aeda0a400387c855db41480031d90cb9682900021fe15769052001c3e42aed20a40008df835da41480051b906bb482900031e195709052001c3f42eeca0a400087d85dd941480070f90b3b082900123b20a761052000c7c404ec20a400087f855d841480070f90abb082900021f21975105200043fc3eca20a400087d87d9441480018bce7b2882900fb1e9c365105200062fb2ae620a4000c5c655cc414800193ec8b98829001f27191731052000637b2ce420a4000c6c659c841480031d90cb9082900031bd9572105200063632ae420a4000caf645c8414800f958c8b9082900031ed9570105200063c32ae020a4000cbb645c041480018f0cab844290003171cf65485200062fb2ee690a4000c5c65dcd214802d0f90cba842900021fe1f650852005c3ec3eca10a4000c5e73d94214807d8f4e1b2842900030fd9674085200061e32ce810a4000c3f655d02148001878caba0429000317d9573085200062e32ae610a4000e67654842148001b8ae690842900fb1e9db65c812001e3d3b0cb902400487e8794d65c40090f90ea9acb880030fdd274597100253b40ce8b2e2000a7b805d165c400187ae83a2cb8800297a0c74597100052ec18e8b2e2000a3e841cd65c400147b0839acb880021fa1c43597100043ec3886b2e200087e870c965c40010fb0e192cb880028fa1032597100051ec2064b2e2000e4d320c965c40094ed02192cb880029d60432597101653d40064b2e2000a79800c965c40091790ea1ac98800e1fa1772593100043ec2ee4b26200487f8759654c400147f08b2ca9880031d595719531000c7b40eecaa6200487c8759554c400f47908b2aa9880b31e1c1655531008e3d32ee0aa6200cccc734ca62c40031e902b9ac5880123b21d3258b100166639a64b16200487f8759652c40090f90bbb2a5880121f21d6554b1001c3f42aeda16200087f865d742c40010ff0eb2e85880021f61d65d0b100062f39acba162000c5e655cf42c40018bacab9e858801f2799173d0b100064eb22e7a1620048bc8759142c40091d90eb1285880131d9c56510b100063ab2ae22162000a778655151c40596e100aa2a3880029de19525471000cf8402eaa0e2000b9583d0941c40091f301b9eca8800a1fe1d53d95100061e328e8b2a2000
  | 2 => 0x7705094033c7dc02ebb0a804287c86dd561500010fd0fb2ac2a00021fa1c65585404261fba0cab0a805fc7a7019461500011ef0eb08c2a010b1e9c365945400363c32ae128a800387c851d951500074790caa2a2a00030f1d954545400063c32ae120a8000c7865dc141500010ff0abb642a000e1f21576c85400043fc2aed10a800387c855da21500018f0cab8442a000e1fa1776485400043ec2eec90a80028de839d921500011bb073b242a0003171cf65485400062fb2ee690a8000c5c65dcd21500070f90b3b042a00122f212760854000c7c404ec10a800087f855d821500070f90abb042a00021f21975085400043fc3eca10a800087d87d9421500c587ce9b2842a0003179cf65085402163d386ca10a80018bc865d0215000187ecaba042a00030f19574085400062fb2ae610a8000c5c655cc21500018f6cab8042a00031e19570085400643e43aa6b2e400c8be87d5164c800187eebaa2c990032aba0b54593200054ec18a8b26400c8bc8750d64c80190ff0eb2ca9900028fe11659532000c77416ecaa6400787e87d9554c800f47d09b2aa9900fb1e1c365553201f5b4402a929640019e8805d542c80031d904b9ac3900323d21d315872002476c12ec20e400287f8754f654800147d0931eca900028f61263d95200053cc06e9b2a4000c3f749d365480014bd073a6ca900029760e74d95200061eba0e9b2a403ea6d821d3654800147d0939eca900028f61273d95201f53d400e7b2a4000a79801cf65480010fd0e21eca900021f61c43d95200043f43865b2a400b87d870cb654800147d08196ca900028f61032d95200072699065b2a4000a76810cb65480014eb02196ca900fa9ea0032d95200053cc0065b2a4000a79801c765480010fd0e18eca900021f61c31d95200051f42063b2a4000a3d840c765480014dd0418eca900029b60831d95201f53d40063b2a4000a79800c765480010ff0ab9aca900021f61e63195200051f424c632a4000a3d8498c65480010ff0eb18ca900029e21930195200145fc3a87b224000c5e73d9664480018bce632cc89000317d9573991200062e32ae73224000c9f645ce644800f938c8b9cc8900021fa1f65591200043f438cab22400387e87dd564480010ff0ab9ac89000e1f21573591200047bc0ae6b2240048f4815cd64480018f0ebb82c8900022fe1d64191200051ec26cb2a24000c6f659ca54480031d90cb94a8900031bd9572951200043fc2aecaa240008fb805d9544800f0fd0fb2aa89001e8fa1365551201f63c386caaa2400c8fa86dc154480238f0cbb82a8900029b21954949201f5b4402a9292403ec7870d9552480078d8edbaaa4900fb5a1c375549201f6363b6caa92405887c865d7424807d0ff0fb2e84900021f61f65d09200062f39ecba124000c5f655cf42480018b
  | 3 => 0xab004204af2811d560084295e3023aac0108029ee1574580210053c42ae8b004200a7a851d160084014f30a3a2c010802b6a0c74580210056cc18e8b00420caea821d160084295d3043a2c010812bca0474580210a578c08e8b004200e3b5495160084011f70eaa2c0108023e21d54580210056d418a8b004200ad98315160084014f50b39ac0108029e61673580210055d424e6b004200ab9849cd60084015750829ac010802ae61053580210053d42886b004200a798510d60084014f50ba12c0108029e61742580210056d41e84b004200ad983d096008419d9064992c01080a2fe1d43d91500045fc3ac8322a062a3f8559064540cf57700b20c8a818b17d9573191500058ec18c8aa2a067e3b6019154540032f50fb82a8a81031e1db70551503161fb2ce9312a0008ef8758862541174df0ab10c4a81629e201541895003c3e42ceda12a00c8bc845db42540030f90cbae84a80065e20175d09500061ebaec9a12a000c9f645cf425400f938c8b9e84a818a1fe15761095000c3e432ea212a00c8f8865c0425409d4f100aa6c2a822b1d5d7619855044e78b86c330aa062c3f651d161540cf976c03a2c2a80023de1d61185503143fc2aeda0aa00187c865d741540032f100bae82a80121f216761055000c3e432ea20aa000c3d75d90415400193ec8b9882a801f27191731055000657b22e420aa007cac645c841540091f10cb8082a80032ed9170105500043fc2aed90aa0008bf845da215400f17908bb442a800a37a0e76485500046ec1cec90aa00487c859d821540030f90cba842a80123e21970085500143e43aa6b2e8000a7b8054d65d00011ef02b9ac5a00123d2057358b4003e1f3b2a9296803eb388055252d00018f2cab84a5a00034e5517094b4000477c12e6b0e800c8ec825cd61d000f878ecaa2a3a00b2ce20154547400063cb2ee0a8e8000d3954dc151d00011bf06bb243a000a3720d76487400257240ac490e80048bd845d821d00050ff0ea9ecaa02228f61263d95403151f424e7b2a8088a3d849cf65500010fd0e196caa00021f61c32d95403151f42065b2a8000a3d840cb6550001c9a64196caa00029da0432d95400053ac0865b2a8042a7a800cb65500014f300196caa018a9e60071d95400043f43863b2a800087d870c765500c547d0818ecaa00028f61031d95400053741063b2a8000a6d820c765500854f50018ecaa00029e60031d954043e1fbaee8b2a800087f855cd65500011f700b9acaa00021f61e63195404351ec24c632a8000a798098c65500010ff0eb18caa00029ee0163195402163c386caaa28011c7865dc15450085878edb2aa8a01032e1db705514042e1eba0cb312800087e87d9562500010fd0e32ac4a00023be1d621894001d1e432a92928000c3e7655252500018f0cab8484a00031e19
  | 4 => 0x40840155f04a9ac810832ab20953590210045f438a6b2042008bd8714d6408419d1864992c8108028fe1570590210051e42ae0b204200a3e851c1640840147b0a382c810802a7a0c70590210054ec18e0b20420caae821c1640840155b04382c810812ada0470590210055ac08e0b2042008be87141640840117b0e282c810802a7a0c50590210054ec18a0b20420caae82141640840155b04282c810812ada0450590210055ac08a0b2042008be87cc1640840117b0f982c8108028fa1730590210051ec2e60b20420caae828c1640840155b05182c810812ada0630590210055ac0c60b204200c3f545da54084090ff0eb2ca8108028fe11659502101d1f42ac92a042018f880dd954084011f700bb2a8108063e20176550210243e43acaaa04200c787059554084091790eb22a8108032e1c164550210047cc36e0aa04211c7a65dc154084018f2cbb82a81099f2e99370550210065cb26e0aa04200cda63dc1540852359f04baac610832b32097558c210054f420eab184200a9d841d5630852159f04ba2c610832b32097458c2147d6bc0ae8b184204ad4815d163084014bd0a3a2c610802976147458c210070faa4a8b184200adb8055163084015b100aa2c61080237a1c5458c210046ec38a8b184200a5e85dc163084014bb0bb82c610802a7a137058c210054ec26e0b18420cace829c1630851d59b05382c610812b5a067058c2146d6ac0ce0b1842008de8714163084011bb0e282c610802a7a105058c210054ec20a0b18420cace82141630840159b04282c610812b5a045058c210056ac08a0b1842008de8710163084011bb0e202c61080297a144058c210052ec2880b18420cace82101630840159b04202c610812b5a044058c210056ac0880b18420387e855db42084051bd06bb684108ee1fe1975d082103e1f322eba104200c5e635d742084018f4c0bae841085a1fe1d65d08210043ec3acba104200c5e73597420840187ceab2684108030f5d564d08210064f39ac9a10423a8df865cf42084018bccab9e84108031759573d082103e4f322e7a104200c9d645cf42084019b4c0b9e841085637e1d63d08210046ec3ac7a104200c5e7558f42084018baeab1e8410803351cf76484210066bc1eec9084200cd483dd921084019aeedb9a4210802b5a1d634842134d6a43ac6908420cec68258d2108519d8b04b1a421081335dc9634842102763b92c6908420cec65258d2108419d8884b1a4210833b1c81634842100762b1aa49084200ae586d0921084016cb0ba124210802f160f424842100762b1e8490842048fa87cc160084014f50b982c0108029e61730580210055d42660b004200ab984cc160084091f10e982c010802aea1075580210055cc20eab004200ada831d560084015b3063aac010832baa0875580210a574c10e
  | 5 => 0x80297e1570d8d210052e42ae1b1a4200a9f845c3634840153908b86c69080237a1c50d8d210046ec38a1b1a4200a9e84143634840153b08286c690802b3a0850d8d2100566c10a1b1a4271ad68114363484015ab02286c69080237a1c40d8d210046ec3881b1a4200a5e8510363484014bb0a206c690802b3a0840d8d2100566c1081b1a4271ad68110363484015ab02206c69081f0f19175d09210062e31aeba124200c3d75d9342485251b90cb9e84909c637e1f63d09210046ec3ec7a124200c5e75d8f42484018baebb1e84908033318e76909210066a31ee2a124271ccc76d8d42484e3b88e3b1a849081279a1f7150921005e2c18e2a124200ccc63dc95148401998c6392a290812ab21942d0521025d240a85a0a42008df835d941484051b906bb282908033318f725052100666318e4a0a42049ac8750941484095590ca128290812e920542505210146f436e6b0242718dc86dcd60484011bd0fb1ac09080317dd763581210062e3aec6b024200c9f74d8d6048401938e9b1ac09080237a1c63581210062fba8c6b024200c5c7518d604840193ee831ac090803271d0635812106476412e6b28420487e8794d65084090f90ea9aca108030fdd274594210053dc02e8b284200a78805d165084014bd063a2ca108029760c745942100537c12e6b28420ca6c825cd650840147d0839aca108028f61073594210043f43886b28420087d8710d6508419c9864992ca108028fa1070594210051ec20e0b284200a5e831c165084014bb06382ca108329ba0870594210b536c10e0b284204a76811c1650842d4eb02382ca108021fa1c40594210043ec3880b284200a5e8310165084014bb06202ca108329ba08405942100536c1080b284204a768110165084014eb02202ca108021fa1f30594210043ec3e60b284200a3e84cc1650840147b09982ca108329ba0a305942100536c1460b284204a76818c165084014eb03182ca1081e2fa1c53990210045ec38a7320420ce8c324ca640840f17d0e284c8108022f61c50990210054f418a13204200a9d83142640841955d04284c810802ab60850990210255b408a13204200ab581142640840f17d0f984c8108022f61f30990210051f42e613204200a3d85cc2640840917d0faa2c8108030fdd754590210054f418a8b204200a9d8315164084191d904b9ac8108123d20573590210245f43c86b2042048bc8750d640841955904a1ac8108028fa1443590210051ec2886b204200a3e85101640840147b0a202c810802a7a0c40590210054ec1880b20420caae82101640840956d02202c8108030fdd675590210055dc02eab204200ab8805d5640840153d063aac810802a760c755902100557c12e6b20420caac825cd640840156f02b9ac810812ad20573590210051f428e6b204200a3d851cd6
  | 6 => 0x556c20a6b108200a6f855c162104014d90ab82c42081eab211705884100477438a0b1082008ed87141621040f55d08282c420802ab610505884100567418a0b108200acd8314162104095cd02282c420802b960450588410053742e60b108200a6d85cc1621040f55d09982c420802ab61330588410247643ac4a9082048fa87cc160104014f50b982c0208029e617305804103d5d42660b0082048f8874c1601040f57108baac02081eaea1075580411055cc20eab008200ada831d560104015b3063aac020802baa08755804100574c10eab008204af2811d560104415e3023aac0208029ea1673580410053cc2ce6b008207aba849cd60104015730939ac02081eaea1053580410055cc20a6b008200a7b855c960104014f10ab92c02081eae211725804103d5d426a4b008200ab984d4960104015e702992c020812bc20532580410047d43864b0082008f9870c960104014f50a192c0208029e614325804103d5d42064b008200ab9840c96010401d9264192c020812bca04325804100578c0864b00820c87c8754d65c84191790ea1ac9908023ee01765532100c7c402ecaa6420787e87d9554c840f47d09b2aa9908031e1c36555321004e6c1eeca1642049ac8750941c84070fd0fbaac1908021fe15735832101c3e42ae6b06420c8f8874c160c84090f90ea9acb108122f21d43592210047dc02ecaa442018f8805d954884090f90eb2aa91081e8f21165552210063c382caaa44207c9e645cf428840193ac8b9e85108123e21d30582210146f43ee6b2a42008ef825cd65484011bd0e39aca9080a1f21d53595210066639ee4b2a4200a3d85103644840155b04206c890802ad60440d912103e1e322eb3224200c3d75d9264484018bcea31cc890803175d4639912100477c12e6b2242008f7815cd6448405938e7a1ac89080a2f21d43591210066639ee4b224200cd473dc5644840117f0eb20c890a4b335c8631912103c5e422ed2a242008df835da54484051b906bb4a8908033318e729512102476432e52a24200ccc635ca54484093c902b94a89080a37a0f76551210046ec1eecaa242018fa809d954484011f3013b2a89080237e0d76551210146e41aecaa242008fb805d954484031f100bb2a89081e1fa1f65551210063c386caaa242038be87d915448401970e1b22a8908033618f70551210046ec3ccbb1a4200a9e84997634840153b0932ec69080237e1d65d8d210046ec3cc9b1a4200a5e8599363484014bb0b326c69080237e1d64d8d210cd6b436e3b1a4271dc772dc7634840153d093aec690802a761275d8d210062eba8ebb1a4200a5e859d363484014bb0b3a6c6909b6b3a0874d8d2138d66c10e9b1a4200e1f5495363484015b700aa6c690802b620154d8d210046f438a9b1a42008dd8715363484d359d05b8ec69
  | 7 => 0x9d41dcd6290405998e7192c5208123b21d3258a410166639a64b1482008df835d952904051b906bb2a520813391c56250a410247c43a60b0482008ef825cd65504191d904b9acaa08023ee01735954100c7c402e6b2a820287c8754d655052d8f0e0a9acaa0a572e1c343595410145e43a86b2a8200e1d5350d6550529970e0a1acaa08063ea1f70595410063dba8e0b2a8200cbb741c165504018f0e1b2aa8a080b279cd43d894100556c2065b128200ccf730cb6250401d1a86196c4a0802b960432d894100477c3ac43128200acc83588625041999864b98c4a08021fe15701894101c3e42ae03128207c9f615cf425040fb2ec2b9e84a0833391897190941005d8c00e2a128200c3f65dd151504090fd0f29aca208121f21d535944103d1f420e6b288222a3d841cd65104010fd0e192ca208021f61c325944103d1f42064b288200a3d840c96510401c9a64192ca208129da0432594410053ac0864b288200a7a800c965104014f300192ca2081e8f211705944103d1f420e0b288222a3d841c165104014bd06382ca208029760c705944100537410e0b288200a6d821c165104094ed02382ca2088a9d60470594410043f43e60b28820087d87cc1651040f47d09982ca208028f613305944103d4f420eab188221a9d841d563105275af02b92c620812b52057258c410052f428e4b188200a5d851c9631040f53d08392c620886a76107258c4100666b90e4b188204ad6811c963104435ab02392c620802b6a007258c410056cc00e4b188207a9e84d49631040153b09a92c62080297a177058c410052ec2ee0b188207a9e84dc1631044353b09b82c62080237a1c5058c410046ec38a0b188207a9e84141631040153b08282c620802b3a085058c4100566c10a0b188204ad68114163104015ab02282c6208123b209759884102476412e7310820cccc325ce6210419998e6994c4208021fe15709884101c3e42ae131082048ec825c26210419998e6b9cc42081eaba10539884100556c20a73108200a6f855c262104014d90ab84c4208323ba1c509884100476c38a13108207aae84142621040155b08284c420802b3a0c509884100566c18a13108204ae68114262104015cb02284c4208029ba17309884100536c2e613108207aae84cc2621040155b09984c42081eaba1352588410247743e64b1082048ec874c96210405998e6992c4208029ba14325884100536c2864b108207aae840c9621040199ae6192c420812b9a0432588410057540064b108200ae9800c9621040f55d093aac420802ab612755884100573c0ae6b108204ae4815cd62104014dd0a39ac4208029b614735884103d57420e6b108200aad841cd621040199ae639ac420812b9a04735884100572c08e6b108200aea801cd62104015d30039ac42081eaba1053588410
  | 8 => 0xb9acaa10063e20173595420143e43aa6b2a8496c787054d655092b970e1a1acaa100a2f21d43595420070ea9a86b2a8494cb87050d65508031f50fb82caa10031edd470595420063c386caaa2840787f87596525087d4f100b2ca4a10030fd977454942066d390ae321284008fb805d761508031f100baec2a1003a550f31d85420055ac2063b0a8400ae5820c761508010ff0ab86c2a100e1f21570d85420047bc3ac230a8400ad48358461508190f90ea9aca210332b94b765084200657bb2a4a10840cea72150961108191e90e98ac22100e1fa1f75580420043fc2ae6b00840387c855cd60108191f10e982c0210122f21d43592510666639a65314a2048ec874c96294405998e6992c5288031e98175d0a510061ebaac9a14a207c9e645cf429440193ac8b9e85288033698173d0a510053cc2e60b04a200aba84cc1609440157309982c1288123e21d30582510053dc2ae8b04a22ea7a851d160944014f30a3a2c128802b6a0c74582510056cc18e8b04a200aea821d160944015d3043a2c128812bca04745825117578c08e8b04a206a7a859cd60944014f30b39ac128802aea1273582510055cc24e6b04a206a7a8510d60944014f30a21ac1288029ee1572582510353d42e84b04a200a7985d0960944015b507a12c128802b660f42582510257940884b04a200af18110960944011f50e192c1288023e61c32582510353d42864b04a200a79850c9609440157508192c128802ae61032582510076499064b04a204af2810c960944015e302192c12880237e0d72d91510146e41ae5b22a200a3d85103645440156b02206c8a88022fe1d64191510055c402c8322a207c9e645cc645440193ac8b98c8a881e8fa1b64551510069c386c8aa2a200b1d831915454401a70e0322a8a88b25ea1f705515133e3c3b6e0aa2a267e3864dc154544c18f6ec382a8a89831e1d870551513071c320e0aa2a200d73711c154544014db0b996c4a88029b61432d895100667b9865b12a200ae5810cb62544011df0eb10c4a8802b320d62189510053c402a8312a20cccc325cc62544018f0a0b80c4a88121f2197550951164bc402eaa12a20c8f4865c442544c10ff0eaa6c0a88b29e20154d81510065c300e8b02a200d38501d160544011f700b9acba08063e20173597410143e43aa6b2e8296c787054d65d0401c3aa6a1acba0a532e1c1435974100c7d43ee0b2e8260c7b751c165d040f87ce8b2ca5a08fa9e2016594b410047dc02eca9682018f8805d952d040f878e8b2aa3a08b29e201655474101c3f43eeab068260c7b701d560d04010ff0ab9ac1a080e1f215735834100477c12e6b2c820c8ec825cd65904090f90ea9acb208031e1c165552410666639a65314820087f855c262904070f90ab84c52080a37a1f7358a4138e4fa0ee6b148271c
  | 9 => 0x64552520069c384c8aa4a407a3f865915494801a70e0b22a9290da1f61b72552521f4bd43ee0aa4a467c7b76dc154948cfc74c9b82a9291831edd870552523063c3b0e0aa4a460e3a641c15494801ad0e4382a9290029e20154586520647a43a62b0ca46087c87551609487d4f100aa2c1290323e21d30582520045fc3ac8322a4008f787584615480f0fd0f29acba101e8fa1253597420143e43aa6b2e8402c9e7350d65d0801c3ca6a1acba10038754d435974203d1f424e6b2e8400a3d849cd65d08014f50139acba10029e602735974203d1f420e6b2e843ba3d841cd65d080f47f06a1acba101f87e0d43597420070f39a86b2e8400e1d7350d65d08014f700b92cba10029e201725974203d1f42664b2e8400a3d84cc965d0801c3a87192cba10ee1fa1c32597420043ec3864b2e8407a3e840c965d080147b08192cba10038750c32597420072699064b2e8400a76810c965d08014eb02192cba10029ea0032597420053cc0064b2e8407a3e849c565d08014f50138acba10029e602715974203d1f42662b2e8400a3d84cc565d0801c3a8798acba10038750d31597420043f43862b2e840087d870c565d080f47d0818acba10028f61031597420053741062b2e8400a6d820c565d08014f50018acba10029e600315974203d1e422e0b2e8407a3e841c165d087747b08382cba100297a0c70597420052ec18e0b2e843ba6e821c165d08014db04382cba10029da0470597420053ac08e0b2e8400c79701c165d08010fd0f982cba10021f61f305974203d1f42660b2e8400a3d84cc165d0801c3a87982cba10038750d305974203d1f42060b2e8400a3d840c165d080f47d09102cba10028f612205974203d1f42020b2e8400a3d8404165d080f53d083aac7a10eaa76107558f4240d4fc22e4b1e8400ad7815c963d08015a902b92c7a101ea7a135258f420054ec26a4b1e8407a9e849c563d08ef53b0938ac7a1002b3e097158f424bd66412e2b1e8400a5e851c563d08014bb0a38ac7a101ea7a107158f421d54ec20e2b1e843aace821c563d080159b0438ac7a1003355c47158f420056d400e2b1e8400ad9801c563d080f53d0828ac7a1002a76105158f420052f42ee0b1e8400a5d85dc163d080f53d09b82c7a10eaa76137058f420046f438a0b1e84008dd8714163d080f53d08282c7a1002a76105058f4200567410a0b1e8400acd8214163d08015ad02282c7a1002b56045058f4203d4f42020b1e8400a9d8404163d080187acbba2a5a100b279cd435874201c3f42ee0b0e840087d85dc161d08191d904b9acb210321f21d53596420063c382caaa484018fa80dd561908011f301baac3210323d21d315864201c3f42ee0b0c840087d85dc161908191f10e982c12101e3b60b73d95420047bc0ae6b2a84048f4815cd65508011f7
  | 10 => 0x4004020000440000040400100a00c000110000040a003000000138070220000080800200800002002088000060020000400800a018010000140000000003e0040d04700a02000005006040020000000040380000200000002008020020030000000000300000400001002014018050000100300200600000802006018010000060000b80500002c0000a00e00000802000018018020040100000100603c00800006000050300080100000100e014040210000000301b004004000010000200101000c00c0980100c00012800000008098050020000080400a0140200300c0000000302a01c01000002000000040100300280202a0000800400200400001026018098100020040c8160020000100300000000803018004158020020140080100a00c0000100e00c00000000004010050080000081406200401000000014030050100080a80200600c0180101a00c0080001401005814000004008090060080080f01200c0500300a00c0002000a0041e00000600000002030024028090080400500100000c0300601001c0002c0020600701d00600c008080000580900a006008240090060080280102200c0001a0180000080000800006800002000010000000000000000400408007004098018010020100000201c004020090240000100004600c0000000603000033330c97398a540063c282e1314a800a6d850c9629500f55d08192c52a003335cc3258a5400746a1864b14a800ae5810c962950015d300192c52a01f0f5d543d89540164f39a87b12a800e1d5350f62550011df0eb10c4aa0038754d43d85542047c436e0b0aa8008f78758461550051f70e986c0aa19e9e21953d81544b63d3b2a7b02a811ab88650f6055129974eca1ec0aa003c654d43d815408d3d428e7b02a867a79851cf60550cf5750839ec0aa046ae61073d815433d3cc2ee5b02a8008fa870cb60550011f30e196c0aa0469ea1432d81540053cc2865b02a867aba840cb605500157308196c0aa003b24c832d81540057940865b02a800af1810cb60550cf4f30a38ec0aa0023ea1c31d81540047cc3863b02a811a7a850c760550014f30a18ec0aa19eaea1031d81540055cc2063b02a800aea820c760550015d30418ec0aa0023e61e63181540053cc2cc6302a89bab98498c60550011f70eb18c0aa0029ee1563181544d53d428c6302a895aba8418c60550c14f50ca98c0aa1829e21953181540072db1aa6302a860e3b65d0c60550c95710ca18c0aa1838ed9543181540074db1a86302a800f195350c60550011f30f310c0aa266ae61262181540047dc3ac4302a858a788518860550011f30f308c0aa0023ee1d61181544c55dc22c2302a84ea7a8518460550191790ea1ac9290028f61440592520054ec1880b24a40caae82101649480156b02202c929002c760e
  | 11 => 0x424b4072c000a7a7540002d09f21d41100006145941400005d81f634caae000406b0e22e3e20fa5a00003625720009c652080ea1c9f06c07687f21840107c6a665b2a3490c9103340840b44743e881a0da6dc55a26211a71e77466063883e278b120002f81fe22200000000069a1ae0009d06b85c030c1544b4ae06ee5fe25a14e3e450e45c0002827147066ec4d42744bc0fe6885e855c990000b0a59c3ae5fa51c73e060000a0a1d8a6425480a9c295000044e6d88363c67dcad800003c0007eea8800000000053e0007da3be5c400000000065200058a73cb3800030600000000000033e7cc9463ba2cc6c200082823281621e61e0004480000004227b01200000000962862480009f628c70800000000039a2e43362ba0000001caa268ce8441723526d63385605e678e31a78c8b22849a69b0732ae24f60e42a0114a36840b2eb225a88f06dea8031e3925763cc0481f88329aa738a960007ae17eadc10e5a4ae473603420466e86a842568130af21be12e0a492c4baa5278649e8b47c8238556af02b60c89ba7ea404b2cb282a62d81f2634a4a8a297a810af4152952a3e43483a1828aa2606d02886449066e042c0001da4fc7942a40005841d2a382d22f013c19c4909825240009b60000009860000f4000ad08ba00056ca4200079c45256a2e29ae484a0c0bc020000518ace42a5307f49604a293e00000020275c46c8828046660e24548626925986ba09248e68600095a0000ca0003d6000802a12b600000001ac63a9b8000b1e4acb04470298782000000af83fa0120d445015c74a0ec3a02720004e448c4287eca008d84cc07c126a30000000ab200000000075227a00000013ab1c00072e000000710b6801825877e0000000000ac6c4000a8a0007a49e202400021800009454c1fc7708743da2d692248a8642ca32e5c600021c998a086060005f60de91eabe1a62124f029eaa870420086e86069ca4ea247c4b240d25420a08d64d84f803001c67e2e812a00023a31878404c12273a00065e2fa1a80000009140003ea1b40004d671600053ca4647e1808d25289f43b666c0005d62a201e0004b61d61a21b267c36e0006fc1e05b80000160a800088a0007e42660002c2504000aac372a5e5e0866506b64000b302ee50c0ee5da3c0592000b58000b62000000000a6203e00c0380000200001016024000008240120200000400400c080010020180080903600400005048004028000020200900800403c050150020000480100c00c010040200180880400a0100180300003000807000010000060060001300002201c008000040000200000400007800000008188000080100000501401400801010018008030000140001a0000040500001600c0000b0020080180d0220000480100200c0080003003c0b8020000000001400c01c040
  | 12 => 0x198b262ec3c887617c00085a672750b429489001126ae8a00005dc0000000000000004f2000536ab0aea00015800050a0007fe292000570000af6000000a40696ac440800040a02e1942ae1ee00083c7265cc8967aaa505f400000030e32c19066400009800074e2e676a8125587a09bea2c64a0d09fc6ea3447240006427d409032845e13451a3eea6a00000000049c8b062cb0ca329720000786b216e70c6e67407d003e6025b000006c08e06481e0002bc4b81de00000000000040c43caecab40002145783d098a8e80005542b089400057ab4485e82a04e96a2807d60c2000000aa21b892a87c3b803800004236a1cc0003704640008ae4d20000000000004583b28d0a60854000a5a18800036896eafc00081400082e6a60000000000008da000a869d80000008fc46826a000000a685ba8ca1e63840003c20c420a354970a581e221a29cb562be5642dc146a445885b6626000008000968936a825ee0000a260000027c19e0000000009a40009e60006a40001c294018c6c64108e00000001667180009040a634625241c5ec31427036c0002c660a5167f83de2f4000758b206bc0366c8000ab8a5c000b088261e89d22f20c000019652a0001e48869800227fc3e058c33249a9d63b008a000a069ee4a8b0271a06e38c1763a40ba8fa89a984b3207676200084c9de0008909768783e6b1000a0000008c00004ca00000097c00016c0000001440008200004e818e684000a9800002aa9a54a0cc4e2abc37c6b074426400052c5e40000000000000000000000005aeafa75ea780006104ec89c0000006240001dc00042e000a3a170aaa7e23f81086d40004d0858550000728790378a049bc9a85a62b21024c2522116b1a5963301f40b000085269821076465c7b896c7427006ce92464cb06000a488b89782de5d46b62949fe47c4661b60000006fe2460f03400009642eaa14a2e8569f88f62969445aa3827809c80007466f28e6000a02000000412250a7e4207f60004820728bc84644474c3ce1d02085b4000000926798242386000230a840802f6b5a000938a2291a1625fc06a00000060c5006a8b4658e4de00012497e4b20008f2000000a4c4be00000000010400000068aa5400087a0000000005be1ea000000b5461a0000000000003229660004388e25d026e2289187caaeea9479616890a61851259aafe8c66b424e9c44ea1ba53ab500040004dc00043000088c2360000000007c20006620020000001b00006f000030014266a608000000a16ae662a5a277200095e7ce0003949c06e29120008300005e234e0001060001c035855e2b473484e2068086a01780000005825ea6cc800160b160aa7b400031263e0007760f62ac0fc3240000009a28ee3901320004aab2a93c10001437e5bc818088026b3e00094a868ac6000a3c00000
  | 13 => 0x7a388000492000000000000000b663c40007120000009d41860006aa7b629098c4a62d49924c87a6000a9231693a00047254819a22000065a88826cab68f805a33c0000660000006e84ee0008de8be9e89168e43ec5c20005d29ac8340503f4872000000640086646658000000a10654000aa40000004569200000003ac0004b099a00015a0006487667200dc16a92857eb3c00058015663c66800000053214803a00000099600034835e000a2a00000029a00000000000076e00035a0828709cc0000000004000000007de824a28ade9e00468ea616000138b5c18a3505ce7be6fa22600076c00059e0445523b47bc7e090e8500d69746764400b668e05c0627d29420008a8460a6c4188fe54000eb3a7e82aaacc51e2560001fa00060447638041e5861281f020e9623761a43d43a853801a31c6a200c000ada8800007a200022c12ca7083834aa7c9da0000008a42b810c0009fa0000007b2000000898028000000a7463000000000000027e0000000009a00000ce00089eaa67e61920ea57400027695c36652ea183080003aa38e5f200048654e70a38aac288e0000000003f60000f80000003200003bc6700528225468a600000000000000000002c6200000000be85c8f40007920009582400006be00000071c00023e0e01ec44241686c63277879e52684809c1c6a564361508dcad40004c099e1642da6f60e80006ac81c94eb5ea9098825ca9c06800046e00095424c9028c200077c00000010a00061200046a7ac0000d849448859004a0c66500ae9ec93000068c3020004e044a0000008d457c3743ca00005e3d2b527fa7f06da80c90835c000b4a5f80b262839c4fe84a7ba7c050800072a0005108cc34224a1bc17a1aa622b488ec956a1eb340006e40000002680003fe35611e70e09a0546d243eb145c837a99c47a69e14a0b88062e079aae8ac851462eaca30aaa0b185de5ac4f4480a760403dc5ca60e0004da00082c63600039e562ac00000583643f2000a6e1c800000000089200000049600000020c3d88b646208c0004ce4c6690a7223c22a0e600000000056e15e00043a5440009dc244a1a0700000000006caa2000094cb4e00644661c4e668000098e4fa9940005669e40000000004265f00000002241ce0000000f200078a65687e0001180000004a400070269475640e0004020004a03a2b367607888846827226f83100000009b400000000000000000011cb4c1360000000008c80002c43986f450209e00067a3f033a0004782c877aad6748a8c44c9ca2fe9ce396a9e000432aba1c47d821673067845a3a62c092e91c0000001741a000007e4c43fc64e03200093436030405653441aa0ead27a814c2349ea2fc28aa8e9b2b009320742ce0006744984ae0002a825e8c400013e0004140000008ac28e32632a75a
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2c00000172c0011c00015000844a80424142b1e7d2134a006800000da960797271228000006101a00051830c14ca63a1c5945e21112180190e5ac40001f040820d04245000e440060c1801439941417098a5400683615430c962950018c5736043258a54006a150d810c96295001a89436003258a544e7069d95350f6055001ac13260432d815430586a595350c6055001919831c264552523060ee18705915494801619909cd43597420060761d430c965d0801a15436043259742006914c9810c965d0801a194360032597423050e251701c165d080181d8750f305974200631609711c563d0939c187054d4359542006b04c9810c960944014989059173191513060ea1870d915454401919831c0645515100631dcd810cb62544014399414170189514e7061c15350d65d0539c187054d435954100631dcd810cb6250401a854360432d8941006914c9810c965104018c5736047358841006b04c9810c960104c183a841c365553213060e2107059554884012c59858f42484210069161563d0921084c1138985517094b403044ee6154dc151d0001a453260432d95403050ea43749d3654800181f7460e74d95200040fe61741d36548001a453260432d952000711d9573484214800103f985d074597103050e241741d165c400181d7460c7459710006914c9810c965c4001139981d464501101654c25d545454044059560975495148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x80c140d506e8c1ce9b2a4060a062817460c7459710
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x94c
  | 6 => 0x94e
  | 7 => 0x5
  | 8 => 0x138c
  | 9 => 0x138e
  | 10 => 0x98c
  | 11 => 0x98e
  | 12 => 0x3
  | 13 => 0x150c
  | 14 => 0x150e
  | 15 => 0xa0c
  | 16 => 0xa0e
  | 17 => 0x180e
  | 18 => 0x180c
  | 19 => 0xa4c
  | 20 => 0x209
  | 21 => 0x20c
  | 22 => 0x20e
  | 23 => 0x154c
  | 24 => 0xb09
  | 25 => 0xb0c
  | 26 => 0xb0e
  | 27 => 0x1409
  | 28 => 0x140c
  | 29 => 0x140e
  | 30 => 0x1549
  | 31 => 0x154e
  | 32 => 0x289
  | 33 => 0x28c
  | 34 => 0x28e
  | 35 => 0xb89
  | 36 => 0xb8c
  | 37 => 0xb8e
  | 38 => 0x1489
  | 39 => 0x148c
  | 40 => 0x148e
  | 41 => 0x1849
  | 42 => 0x184c
  | 43 => 0x184e
  | 44 => 0xbc9
  | 45 => 0xbcc
  | 46 => 0x14c9
  | 47 => 0x14cc
  | 48 => 0x409
  | 49 => 0x40c
  | 50 => 0x40e
  | 51 => 0x160c
  | 52 => 0xd09
  | 53 => 0xd0c
  | 54 => 0xd0e
  | 55 => 0x1609
  | 56 => 0x160e
  | 57 => 0x1889
  | 58 => 0x188c
  | 59 => 0x188e
  | 60 => 0xd49
  | 61 => 0xd4c
  | 62 => 0x1649
  | 63 => 0x164c
  | 64 => 0x1049
  | 65 => 0x104c
  | 66 => 0x1949
  | 67 => 0x194c
  | 68 => 0x98954
  | 69 => 0x94994
  | 70 => 0x94a14
  | 71 => 0xb8954
  | 72 => 0xb8956
  | 73 => 0x148954
  | 74 => 0x148956
  | 75 => 0xbc954
  | 76 => 0x14c954
  | 77 => 0x2c9
  | 78 => 0x19c9
  | 79 => 0xb9394
  | 80 => 0xbd394
  | 81 => 0x4e
  | 82 => 0x99514
  | 83 => 0xd0994
  | 84 => 0x160994
  | 85 => 0xd4994
  | 86 => 0x164994
  | 87 => 0x128e
  | 88 => 0x449
  | 89 => 0x1a09
  | 90 => 0xd1514
  | 91 => 0xd5514
  | 92 => 0x8e
  | 93 => 0x104a14
  | 94 => 0x194a14
  | 95 => 0x749
  | 96 => 0x14d
  | 97 => 0x1a89
  | 98 => 0x134d
  | 99 => 0x105814
  | 100 => 0x10e
  | 101 => 0x124e
  | 102 => 0x104a54
  | 103 => 0x198d
  | 104 => 0x130e
  | 105 => 0xb0214
  | 106 => 0xd1554
  | 107 => 0x154b14
  | 108 => 0xb1554
  | 109 => 0xb1614
  | 110 => 0xd0b14
  | 111 => 0xb0d14
  | 112 => 0x160b14
  | 113 => 0x15ca
  | 114 => 0x141554
  | 115 => 0x154d14
  | 116 => 0x155614
  | 117 => 0xd0b94
  | 118 => 0xb8d14
  | 119 => 0x188b94
  | 120 => 0xb9894
  | 121 => 0xd1854
  | 122 => 0x184d14
  | 123 => 0xd4bd4
  | 124 => 0xbcd54
  | 125 => 0x104bd4
  | 126 => 0xbd054
  | 127 => 0xd0414
  | 128 => 0xd1614
  | 129 => 0x189614
  | 130 => 0xd5654
  | 131 => 0x105654
  | 132 => 0x75491
  | 133 => 0x74d11
  | 134 => 0x74e91
  | 135 => 0x1a9951
  | 136 => 0x194e91
  | 137 => 0x124956
  | 138 => 0x19cbd1
  | 139 => 0x45651
  | 140 => 0x20b14
  | 141 => 0x20954
  | 142 => 0x20994
  | 143 => 0x21854
  | 144 => 0x21894
  | 145 => 0x21a14
  | 146 => 0x3ca
  | 147 => 0x29554
  | 148 => 0xe89
  | 149 => 0x18c9
  | 150 => 0xec9
  | 151 => 0x188214
  | 152 => 0x11496
  | 153 => 0x10d16
  | 154 => 0x1a49
  | 155 => 0x10e96
  | 156 => 0xece91
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2158
  | 6 => 5093
  | 5 => 1461
  | 4 => 51
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (88474+((h/719+packedAt gbK7 (79846+(h % 719)*12) 12) % 2590)*13) 13
  | 6 => packedAt gbK6 (266525+((h/1697+packedAt gbK6 (244464+(h % 1697)*13) 13) % 7395)*14) 14
  | 5 => packedAt gbK5 (91556+((h/487+packedAt gbK5 (86199+(h % 487)*11) 11) % 1929)*12) 12
  | 4 => packedAt gbK4 (3689+((h/17+packedAt gbK4 (3570+(h % 17)*7) 7) % 68)*7) 7
  | 3 => packedAt gbK3 (164+((h/1+packedAt gbK3 (162+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe3fff3c387f1f81ff8e0381c020867e373ccc
  | 1 => 0x1fc700c03f87e3fe03f003ffff43199849c0ff
  | 2 => 0x1ff800ffc007fc0003fffc01ff9c61e18e0f0f
  | 3 => 0xe00000fffff8000003fffffe00e07e01f00ff0
  | 4 => 0xfffffffffffc00000000ff8001fff000
  | 5 => 0xffffff00000000000000000000fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x26090e0c180b04843b82188c4600022a131ccc
  | 1 => 0xa421200088121240890012492010898014055
  | 2 => 0x14902454400648085124a8012c0c21608e050a
  | 3 => 0x400048aab5500010a249525800e05601700aa0
  | 4 => 0x80f326649259c000601008f68001eca000
  | 5 => 0x9924f002044000610001806030fbfdd4000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeeafeeefcc0fefefeeafeeefcc0fefefeeafeeefcc0fefefeeafeeefcc0fefefeeafeeefcc0fefefeeafeeefcc0fefefeeafeeefcc0fefefeeafeeefcc0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36394
namespace PEqualNP.Outside.L_meta_36394
open PEqualNP.Outside.L_meta_36394.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_4_0 : Interval s1Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 2 := bs1_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
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
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 29 := bs3_3_0
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
theorem bs3_4_384 : Interval s3Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_416 : Interval s3Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_448 : Interval s3Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 473 := (concat (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat (concat bs3_4_96 bs3_4_128) (concat bs3_4_160 bs3_4_192))) (concat (concat (concat bs3_4_224 bs3_4_256) (concat bs3_4_288 bs3_4_320)) (concat (concat bs3_4_352 bs3_4_384) (concat bs3_4_416 bs3_4_448))))
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
theorem bs3_5_608 : Interval s3Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 632 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 bs3_5_512) (concat bs3_5_544 (concat bs3_5_576 bs3_5_608)))))
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 7 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 5 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
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
theorem bgb_3_0 : Interval gbAtlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 2 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 51 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1440 : Interval gbAtlas 5 1440 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1461 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864))) (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))) (concat (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))) (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440))))))
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
theorem bgb_6_5088 : Interval gbAtlas 6 5088 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5093 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)))))) (concat (concat (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408))) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))))) (concat (concat (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368))) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528))))))) (concat (concat (concat (concat (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688))) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)))) (concat (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008))) (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168))))) (concat (concat (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328))) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488)))) (concat (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648))) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)))))) (concat (concat (concat (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968))) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)))) (concat (concat (concat bgb_6_4160 bgb_6_4192) (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288))) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448))))) (concat (concat (concat (concat bgb_6_4480 bgb_6_4512) (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608))) (concat (concat bgb_6_4640 bgb_6_4672) (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768)))) (concat (concat (concat bgb_6_4800 bgb_6_4832) (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928))) (concat (concat bgb_6_4960 bgb_6_4992) (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088))))))))
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
theorem bgb_7_2144 : Interval gbAtlas 7 2144 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2158 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))) (concat (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)) (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))))) (concat (concat (concat (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312))) (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))))) (concat (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728)) (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 bgb_7_1856))) (concat (concat (concat bgb_7_1888 bgb_7_1920) (concat bgb_7_1952 bgb_7_1984)) (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 (concat bgb_7_2112 bgb_7_2144)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 32, 33),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeafeeefcc0fefefeeafeeefcc0fefefeeafeeefcc0fefefeeafeeefcc0fefefeeafeeefcc0fefefeeafeeefcc0fefefeeafeeefcc0fefefeeafeeefcc0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124266 * 2 ^ 32 + 4277075136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36394.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.and,[1,2]⟩,⟨.or,[4,7]⟩,⟨.or,[1,5]⟩,⟨.or,[5,8]⟩,⟨.and,[3,6]⟩,⟨.and,[6,9]⟩,⟨.and,[0,10]⟩,⟨.or,[11,13]⟩,⟨.and,[8,12]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277075136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277075136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36394

open PEqualNP.Outside.L_meta_36394 in
theorem PEqualNP.Outside.L_meta_36394 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277075136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277075136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
