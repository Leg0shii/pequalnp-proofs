import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40972.Model
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
noncomputable def anyEq2 (m c d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || (eqF (masked d v) c || ih)) l
theorem anyEq2_eq (m c d : Sig) (l : List Sig) : anyEq2 m c d l = (anyEq m d l || anyEq c d l) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || (eqF (masked d v) c || anyEq2 m c d vs)) =
      ((eqF (masked d v) m || anyEq m d vs) || (eqF (masked d v) c || anyEq c d vs))
    rw [ih]
    cases eqF (masked d v) m <;> cases eqF (masked d v) c <;> cases anyEq m d vs <;> cases anyEq c d vs <;> rfl
noncomputable def availF (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  eqF (masked d a) zero || eqF (masked d a) d ||
    cond u (anyEq2 (masked d a) (masked d (neg a)) d pool) (anyEq (masked d a) d pool)
theorem availF_eq (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :
    availF u d pool a = availableB u d pool a := by
  cases u
  · simp only [availF,cond_false,availableB,eqF_eq,anyEq_eq,Bool.false_and,Bool.or_false]
  · simp only [availF,cond_true,anyEq2_eq,availableB,eqF_eq,anyEq_eq,Bool.true_and,Bool.or_assoc]
noncomputable def memF (x : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF x v || ih) l
theorem memF_eq (x : Sig) (l : List Sig) : memF x l = l.contains x := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF x v || memF x vs) = _
    rw [ih,eqF_eq,List.contains_cons]
noncomputable def subF (a b : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => memF v b && ih) a
theorem subF_eq (a b : List Sig) : subF a b = a.all (fun x => b.contains x) := by
  induction a with
  | nil => rfl
  | cons v vs ih =>
    change (memF v b && subF vs b) = _
    rw [ih,memF_eq,List.all_cons]
noncomputable def sameWordsF (a b : List Sig) : Bool := subF a b && subF b a
theorem sameWordsF_eq (a b : List Sig) : sameWordsF a b = sameWords a b := by
  simp only [sameWordsF,sameWords,subF_eq]
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
    (links (keySet (choiceVal op::rest))).any (sameWordsF (choiceVal op::rest))

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,anyP_eq,sameWordsF_eq,Bool.or_eq_true,List.any_eq_true] at h
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
def M152 : Nat := 2^152-1
theorem not152 (x : Bits) : (~~~x).toNat = x.toNat ^^^ M152 := by
  rw [BitVec.not_def,BitVec.toNat_xor,BitVec.toNat_allOnes,Nat.xor_comm]
  rfl
def natBv (d x y : Nat) : Nat :=
  cond (Nat.beq d 0) (x &&& y) (cond (Nat.beq d 1) (x ||| y)
    (cond (Nat.beq d 2) (x &&& (y ^^^ M152)) ((x ^^^ M152) &&& y)))
theorem natBv_eq (d : Nat) (a b : Bits) : (bv d a b).toNat = natBv d a.toNat b.toNat := by
  match d with
  | 0 => simp [bv,natBv]
  | 1 => simp [bv,natBv]
  | 2 =>
    rw [show bv 2 a b = a &&& ~~~b from rfl,BitVec.toNat_and,not152]
    rfl
  | n+3 =>
    have e : bv (n+3) a b = ~~~a &&& b := by
      unfold bv
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    rw [e,BitVec.toNat_and,not152]
    rfl
def natCol (d : Bool) (x y : Nat) : Nat := cond d (x &&& (y ^^^ M152)) (x ^^^ y)
theorem natCol_eq (d : Bool) (s : Bits × Bits) : (column d s).toNat = natCol d s.1.toNat s.2.toNat := by
  cases d
  · rw [show column false s = s.1 ^^^ s.2 from rfl,BitVec.toNat_xor]
    rfl
  · rw [show column true s = s.1 &&& ~~~s.2 from rfl,BitVec.toNat_and,not152]
    rfl
def covFail (d : Bool) (t : Bits) (op : Nat) (a b : Decor) : Bool :=
  !(Nat.beq (t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat)) M152)
theorem covFail_eq (d : Bool) (t : Bits) (op : Nat) (a b : Decor) :
    covFail d t op a b = ((t ||| column d (dbin op a b).2) != BitVec.allOnes 152) := by
  have e : (t ||| column d (dbin op a b).2).toNat =
      t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat) := by
    rw [BitVec.toNat_or,natCol_eq]
    simp only [dbin,natBv_eq]
  unfold covFail
  rw [←e]
  generalize (t ||| column d (dbin op a b).2) = X
  by_cases h : X = BitVec.allOnes 152
  · subst h
    decide
  · have h3 : X.toNat ≠ M152 := fun q => h (BitVec.eq_of_toNat_eq (by rw [q,BitVec.toNat_allOnes]; rfl))
    have h4 : Nat.beq X.toNat M152 = false := by
      cases hb : Nat.beq X.toNat M152
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h3
    rw [bne_iff_ne.mpr h,h4]
    rfl
noncomputable def allD (f : Decor → Bool) (l : List Decor) : Bool :=
  @List.rec Decor (fun _ => Bool) true (fun v _ ih => f v && ih) l
theorem allD_eq (f : Decor → Bool) (l : List Decor) : allD f l = l.all f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v && allD f vs) = _
    rw [ih,List.all_cons]
def opsAll (u : Bool) (f : Nat → Bool) : Bool := f 0 && (f 1 && cond u (f 2 && f 3) true)
theorem opsAll_eq (u : Bool) (f : Nat → Bool) : opsAll u f = (opsOf u).all f := by
  cases u <;> simp [opsAll,opsOf]
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
def quickPairN (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    covFail (!c.2.2.2.1.2) (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2)) op a b
  else Nat.blt c.1 (c.2.1+1) &&
    (covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2)) op a b &&
     covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2)) op a b)
theorem quickPairN_eq (c : NodeContext) (a b : Decor) (op : Nat) :
    quickPairN c a b op = quickPair c a b op := by
  simp only [quickPairN,quickPair,covFail_eq]
noncomputable def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    allD (fun b => opsAll ctx.2.2.2.1.2 (fun op => quickPairN ctx a b op || testPair ctx a b op)) bs
noncomputable def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,allD_eq,opsAll_eq,quickPairN_eq,List.all_eq_true] at h
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


end PEqualNP.Outside.L_meta_40972.Model

namespace PEqualNP.Outside.L_meta_40972
open PEqualNP.Outside.L_meta_40972.Model
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

def SBf (j : Nat) : Nat := [6, 5, 7, 6, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_40972

namespace PEqualNP.Outside.L_meta_40972
open PEqualNP.Outside.L_meta_40972.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1110000081cc32be40ef32de32ec32bc41be41bc40dc32
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1180080005394a329b28c818d540ca74a120e30ca40c72a0658c32907186420e30c840
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xc00c10ca51902886055032c20ca50906846155032
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 9
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
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/10+packedAt s0K4 (144+(h % 10)*4) 4) % 9)
  | 3 => 2*((h/10+packedAt s0K3 (243+(h % 10)*4) 4) % 9)
  | 2 => 2*((h/8+packedAt s0K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xf807fffffffff80fffc0ffffffff807f8fffc7
  | 2 => 0xfff807fffffffff01fff03ffffffff8071fff8
  | 3 => 0xfffff807f80ffffffffffc0fc01ffffffe38ff
  | 4 => 0xfffffff8000ffffffffffff0001fffffffc0ff
  | 5 => 0xfffffffffff000001fffffffffe000007fff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x5ea0a92948a288e245c02cb2d5a58a3a86dbc3
  | 2 => 0xa8aea23251451121cacb015569caba8a316dd8
  | 3 => 0x323237242269a244935554098c9353535a386d
  | 4 => 0xc4c4c447458e44891ca69a60311c6c6c6dc0b6
  | 5 => 0x7070787860f870e1f38e38e3e0070707fb600
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0c0c0fc000000fcc0c0c0fc000000fcc0c0c0fc000000fcc0c0c0fc000000fcc0c0c0fc000000fcc0c0c0fc000000fcc0c0c0fc000000fcc0c0c0fc000000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40972
namespace PEqualNP.Outside.L_meta_40972
open PEqualNP.Outside.L_meta_40972.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xe421
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | 3 => packedAt s1K3 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffe03ff81fffffffffffc03f1fffc7
  | 2 => 0x3fc07f00fffffffe0f80f81f80fffffe64cff
  | 3 => 0x3fff8000fffffffff000ffe000ffffff870ff
  | 4 => 0xfc0000000fffc0fffffff000000fffc0ff80f8
  | 5 => 0xfffffffff00000fffffffffffff00000ffff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x186450a1802382180318d18a28e2c6190a95c3
  | 2 => 0xa929314696449469606a46a1b1255a6a664c5d
  | 3 => 0x5250a26b2a8928b2ad048b6c8249acb4b870ae
  | 4 => 0x6362c58dcd120edcd6b6e049248e3718df80f0
  | 5 => 0x8383060e0e1c30e718c70c71c7003820f56a00
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40972
namespace PEqualNP.Outside.L_meta_40972
open PEqualNP.Outside.L_meta_40972.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xc02c000600004008000000f00000008100b00020e208200000104fe43fe32fc41ff42ff32ff20fe42be40fe10fe40fc21fe21ff40fd10fc10fc43ff30fc20fd41fd30fc40fc32fd21bc40fc31fd31ec21fd32fe20fd43fd20dc31ff41fe31fc30fe30fc42ff31ee21ff10de31ff43fe41ff21fd40fd42
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x410000cc1831000000201c0030c0030100000040000000c640002020c40000000030038000060002100140009c000011a0c4810600103020400202240012a040000000000080010100041820400006140005b14930baa8e856d52d067ca818e78c440cf2a0636e52d06bea6885754f429e2a2416e520c2eca3a14f15130b7288435e53842d8a4885d14520ae29a83cc31886f6a0a0cfd5130baa8e87ac21903386220750c4219f28481ba501027aa810dbd4931afa9a436f52506e8a2985b54a10f3208437651102bca790f908610f2188436f524c3cca210db14931b629283ae21102f0a0a0f50c721f2108216e52cc73c63204f55031f2a0843d6510c79c6210db54840ae29a216f52442baa7a0db54830baa88816e52d0f5ca810ed94440ceaa0635e530827ca0205dd4530b6a9663d6410c6bca7a0d754c40b7290819c31902bea6a0d794c40e2188435c53482dca310d794f429f2a6613d54c83a863085794431d710c81d5410c7986210f50c410aea98415d538437081884f15110ae29a43b5511027ca810cf55330d6a90819d53102eea2905d14532d7290816d52d0eeca3a1ee10010cf298816e52843ce6210cfd5110d610881ad54086bea6904f95320e6990655d53c879c6310cf55310af28c633e54c42eea2994fd5120
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x208050000400200480138481b1185320cb15540c421e1990310861d650c440e155031087843108440e10c421902546154c2099185520c2a5640c421e19503108746520c610e40c440043255254440b118d41087155354440b1189410c7a02110010d194c2184385640c421b198631086d06050431b8181410862d6508440
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x4040a0aeb3206210d05750c42110242bb4a818843815943108440
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
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/36+packedAt s2K5 (736+(h % 36)*6) 6) % 46)
  | 4 => 2*((h/95+packedAt s2K4 (3159+(h % 95)*7) 7) % 117)
  | 3 => 2*((h/22+packedAt s2K3 (912+(h % 22)*5) 5) % 24)
  | 2 => 2*((h/8+packedAt s2K2 (196+(h % 8)*2) 2) % 4)
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
end PEqualNP.Outside.L_meta_40972
namespace PEqualNP.Outside.L_meta_40972
open PEqualNP.Outside.L_meta_40972.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x23106101dc31de30de43ec42ef20ef42de31ed20dc30ee21dd43ec21
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2006029585050ec8a2904b15120aa28a8756518c2cca3a1710c421
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
  | 5 => 2*((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s3K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/9+packedAt s3K3 (189+(h % 9)*3) 3) % 7)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffe07ffffffffe07ffffc07fffffff1f8fff
  | 1 => 0xf01fff80fe03fffff83e07ff81f01fffe4f33f
  | 2 => 0x1fffff0003f03fffc007fffe001f80f8fc38
  | 4 => 0xffe000000003fffffffff80000001fffff003f
  | 5 => 0xfffffffffffc003fffffffffffffe000ffffc0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x50c1230a1450108600c628c21a51c59509855b
  | 1 => 0x654a45262895251a581a835689624ae664b32d
  | 2 => 0x4a938a144d5a43aeab4125a75c449334b8dc38
  | 4 => 0x831b1c58b1e38a3d35adb03451091c78ff0036
  | 5 => 0xc1c1060c1830c31c631c638618e0040d66a80
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaeaea88880000eaeaeaea88880000eaeaeaea88880000eaeaeaea88880000eaeaeaea88880000eaeaeaea88880000eaeaeaea88880000eaeaeaea88880000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40972
namespace PEqualNP.Outside.L_meta_40972
open PEqualNP.Outside.L_meta_40972.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x128300214400014a001240083200042048040005fd43fc30fc21fe41ff43fc40fd42fd30ff10fe43fe30fc32fd31ff40fd32dc30ff21fc43dd43fe31fe32fe42fc10ff31ff30de43fd10ff41de30fc41fe10fd20fd21fc31ff20fc42fd40ff32fd41fe21fc20ff42fe40fe20
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x8a0808042000e05981601c00d5418004000e8001429884000038114001801e00d810400203000c0080000582b6292815f540c2e8a2a1d7d4d40afaa4615c53487b0a0a1d794f20afa9a215d540c2eaa3a15754c41b6a9081cd528c2baa7905754f42b72946175518c3aca3185b14943b7a92815d53d02bca621d714d40baa8c85db5050fa8a2a1ddd4532bba8a416e521033ea8a1db14931ac282875e508c2d8a4885755230aea9e83cc5250eb8a6907394a30eaa8c616e52906bca7a0d794f42b6a90215d5490eeca3215bd4943af29881d8400c2dea498dd54420ba28a415e5310a7ea8885ed4143e7a92873c54482baa7885b54a41aea98813c54442bca0185bd49109faa241da500c2bca7a05754c42afa9a435e53c42b8a6887948421eda00615e53106bea6905d94420ba28a816e52042e8a2995dd4543b6a96836e52d06eca2205dd4540bc282877551102daa5185d94630af28487d75150eb8a0a1dd94742
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x48028d2d485050e596510030d4d445050f505114143b118d21087465294630d21485050f445214543
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
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s4K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/51+packedAt s4K4 (2484+(h % 51)*7) 7) % 92)
  | 3 => 2*((h/9+packedAt s4K3 (304+(h % 9)*3) 3) % 8)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffe07fffffffffe07ffff80ffffffffe3e3fff
  | 1 => 0xfff80fe07e07fff83e0fff07c07e07fd3ccc7
  | 2 => 0xfffff0007ff81fffc00ffff8007ff81e3f0f8
  | 3 => 0xf000000007ffffffffff00000007fffffc00ff
  | 5 => 0xfffffffff80001fffffffffffff80001ffff00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x60230a14202104200c6118429471628a06155b
  | 1 => 0xa5452628aa4728e581a86ad25892aa6cd2ccc5
  | 2 => 0x498a144d348a1d6ab410b4eb1124db296370e8
  | 3 => 0x8d1c58b1c71451d35ada068842471c71fc00b6
  | 5 => 0xe1060c18618619c631cc70c63801041b9aa00
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeaa800a800eaeaeaeaa800a800eaeaeaeaa800a800eaeaeaeaa800a800eaeaeaeaa800a800eaeaeaeaa800a800eaeaeaeaa800a800eaeaeaeaa800a800, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40972
namespace PEqualNP.Outside.L_meta_40972
open PEqualNP.Outside.L_meta_40972.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x300520300000000000708004a085100048041340005000044007fd10ff31ff32fc42fc32fe42fc43ef32fd41ff20fd32ff41fe41ff21ff10ff42fd40fd30ff30fe20fd42fe10ec32fe32fe31fe43ef21ff40fe21fd20ff43fd43fd21fc40fc10fc20fc30fc41ed21fe40fd31fe30fc31fc21
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2080a0c007004000700240850c040261a882060620200020c29008243810058301021c00014004940004080296e52042e8a2a05b54a21b729e43ce530cadca420db54a41b6292876f5250ee8a2985b94b43f2a88656d528c2dca5885e54341ae29a813c544c2dca690db94831bc28263755190ad8a4985dd4530d7aa243cf53486dca5195b54432dca008175510cb58a890f9d0521bba8a873f544c6d8a690de94341e6190636d52106d8a4a07910521bba8a8176510cbd6a090f98c521bc282876e530cad8a790db54a31f290c213d54842dca410f30ca319faa261e850487ca42085314d21b7294636d52c4398a690dbd4930f298a433f54486bea6a057d4d21b6292637a5010edea4a05d94642b7a92637b504c6daa39959544329e2a2437b50486dca520db54b439eaa061e6510caf6a0a1de54043b7294617651c82e8a2a1cf15131ae29a436d520c67ca9085e141219f2a0617551c82daa40879d4521
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xb403b08237808001f4453d0521d8181510cb0f5414d21d8d81510cae0604c521b1584328c7276454432d114c41486c463484109398e5348664654c521d214f504870c5414d21b898341486656194a30d114e31487246454432d158453486986350040ca15050487265448610b118d218434853141219958652d0ea4644c521
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1800019014e60d0521a08e8b08a690d40705845348710320c0a8865819506348610
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
  | 6 => 2*((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/35+packedAt s5K5 (704+(h % 35)*6) 6) % 44)
  | 4 => 2*((h/51+packedAt s5K4 (2457+(h % 51)*7) 7) % 91)
  | 3 => 2*((h/15+packedAt s5K3 (950+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s5K2 (245+(h % 8)*3) 3) % 5)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe03fc07fffffffff03f01f81fffffffe623fff
  | 1 => 0x3ffffffff80ffffc001fffffffc07f83ffc7
  | 2 => 0xffc0007e03fff01fffffe001f80fff81fc38f8
  | 3 => 0xffffff8003fffffffffffffe000fffffffc0ff
  | 4 => 0xfffffffffc00001ffffffffffff00001ffff00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xaa9155422a89225500ba05c05d52f2ca621b5b
  | 1 => 0x952583145110e48b2c048aaaaa654a2d80edc5
  | 2 => 0xc1b52a1899a241cf5556a02933499b29ac38e8
  | 3 => 0x6060c51624489129a68d34c040e2c70d740b6
  | 4 => 0x1838306183870e1ce38f1c71c78030417bb600
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfc88a800fc88a800fc88a800fc88a800fc88a800fc88a800fc88a800fc88a800fc88a800fc88a800fc88a800fc88a800fc88a800fc88a800fc88a800fc88a800, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40972
namespace PEqualNP.Outside.L_meta_40972
open PEqualNP.Outside.L_meta_40972.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa28214004000008904001ffd5001fd3101ff14003fe52007f04001fd21007f88403ff21007f4c007ff5300ffc8005fc4000ff90801fe4100ff8c803fc42007f94001fe5300ff08401fe43007f54803fc52017f10401fd5100ff08005ff4101ff14c01fe20007f90001fc30007fcc407ff51007f50801fd41007fcc805fc43007f44001fd50007fc4005fc54007f84001fe51007f8c401fd40017fd0c01fd2001ffd4807fc5101ffd4001fd43017fd0001fd54017fd0801fc31017f95003fc32007f4c801ff30007f54c01fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x9aa002ff50640007fa8398807fd218800bffb162009ff58b31007faa310003fe510c095ff32a8600bf58610007faa088027fc4394c01ff29a8004ffc4210007facb1082ffc43440077f3282005ff18e4104ffc86a1807ff42cc801fea022002f7d0e4301dfacb29802bf644c403fe2924209ff90e3001df8ca88013fe618c001fe994a202bf19120027fca198003fd4388001ff9948204ff4c03000dfec4a9002fd6090c49ffa928000ff9855200ffca510002ff61508017fb2c4204ff8c22004ffca798003ff6448401feb04a202ff10640025f8cb08003fd53500097e3286000ffcc110007faa8908e7fc41cc407ffa82a402ff50d4201ff8a4a8803fd648c409feb10200dff10a1001ef8a2a8837fe3284045ffa966000ff98d4100ff864a9007ff2188401ff21a4002ef1064301ffaa8a8817fc658c401fe98aa004ff19640017faa8a180bff4350803fea144204ffd864001ffea328806fe6244005dfa1a8003bf99431026fea128013fe620c001be32a4001bf98831015fcc92800bff4290009ff1024003ff9495404ff886a9803fe2194001feaa46002ffd0641007faa890013ff658405dff32c4203ff151521cffe8598923fc40548017eb1c622affd0e5004ff88698813fc2084001fe9926026ff14e40007fa62a00077c52548017eb046200ff5441002ffec418802fc6154c097e3206000ffd895404ffe8729803fd210408bfe20e6400ff58542007fcc0a100efe6548001ffb226243ff9913205ffe8688127fc5250c0dff2902033ff9913102ffecb20807fd52cc807fea9aa009ff4c7300eff8a518006fe62cc001fea182009fecc23000ffe40a105fff210c0137e31a8004bfd903004ffac321807ff214c809ff1802000ff54a40007f8c6a0027ff6094c9bfe312a600ff8c550007faa598826ff65cc8137fb266404bf98231005fcc218827fe62cc08dffaa6641cffd4530015f8c988027fd43cc813fe29e6201ff0833204ff88718803fe5388407ffaa2a005ff94641007fc62a000afe6494405ffa0a8200bf5925100ff8a490017ff608c413ff32e6400ff88510007fa8418003fe6094413fea9e6009ff58732007fa8298012fe6094c09fe9002012ffd431004ffc861880bff54500017eb0c8001ffd4a2104ffc6398027fe530c013ffb166200bf59231007fec0a090bfc4094401ff28a8205ff1923119ffe8698843fc32c4009ff2806005ffd9621005fac51889ffc2154009fb8802003bfd9551015f8c8a88b3ef5248407ffaa2a200ff0c62000fde4290007fd424c809fe30c8000ff18d4211ff842a000fff52544057f3266212ffd4f1000dfcc310847fc54c400bffb1ca203bf9953101ffea329827ff61cc813feb106205ff1065102ffec7208efff2150405ff2a28009ffd865304fee6298813fc40c407bff90c8204ff58a50
  | 1 => 0x2ff654c4017fb024203ff14a53207fcc8a880efe6548489ffa9a6404ff8c120007fa6310013fd648c003f610e6409fe4c03001ff8a0a9003fd64c4015fe2922005ff19431047fea4080c3fe540c401faa8e2000ffd954104ffac598003fd4348001ffb1a2043ff1013200df8c52883bfc418408ffe32a8409ff90e31016fca8aa087ff41cc0a1ffa04a600ff98e21027fc8018002ff65508017eb2e6413ff99120017be86a1827fe60cc813ff3206204ff98640025f8cb1000ffc5155001ff31ca205ff14710015fcc929802fd6188013bfa9ca600bf58e51007faa71007bdf438c091ffa02a405ff1822104ffe6218003fe51cc013fe29ca601bf18953025f8c0a8802ff6154c01feb2c6223ffc8540007faa898803fe6154c017fb02a61bffd0d30007f86290803fd3290009ffb242009ff4cb31077fe8508003fe3188009ff3242002bf5924304f7e8721802fe61cc805ffa028601ffcca21005fac718003fd504c021ff2162000ff58d21005fec4a0012ff655407bfe1948242ffd0e51007fec4a000afc6454c2dffaa44001bf98830007fa6208002ff6548413fe21a6032ff14931007fa809800efe65cc001feaa4622fff9483125ff84321802fd658840176b14a203ff551531f7fea120807ff324c805ffaa48600ff54a101d7fea398827fd430c401fea886209ff99730005fec498843ff20c40137f31c4002bf9913200f7c84a100efc654844dffa8c8000bfd9231005faca90813f610440017eb2a8201ff086200177e80a1803fe614c04fff90aa009ffcc130007faa60803ffc5384009fe2862000fbd89311e7fea0a080bfe5490c07fe292a600ffd854004fb8a7298effc325047dffa9c8200bfd9520017f8a92080efe6550413fe18c6002ff10143027fac7280b7ff41884037fb0a4209ffcc830017f8a8a0813fe658c0057f3202035ff14a31027fec5080f3ff5350413ffb2e6251ff085540affca91000fff5254005fe204821cff19530007feca9900bfe545500bff1882000fbcc920005fec4a0923fe645480bff28c4200ff58930007f8629000fdc5354c017eb1a2000bfd915301dfcca98003fd4254001fe31aa409ff19331027fca0a8002ff61500017eb2a4003bf9962108ffe8188003fd42cc007fa28aa220ffc873000dfcc4a0827fe6494c05fe2028200ff90d21017fa84a0017ff64c40097f3006224ff99540007fec6a1002ff6355005ffaa2a800bbd8953007fac2a000bfc4350801ff20e6200bf59110017fc8320003fd62540017eb162009f710e43027fac908002ff6550c137fb2aa609ff9833103ffca80812ffe5290c01feb1c8205ff0841001dfccaa0063ff410c08dffa8e6400ff88530005fec2aa06ffe644c087ffa0a6408ffd5010015fcc8a9003be4390401ff21aa22bff19121157f88728013fe5050007ff2
  | 2 => 0x1001578c8988d7fe528c4077fb1aa604ff4c220027f880a8093ff5350029ff32a4009ffd0f31017f8a8a0013fe63880137f3186200ff0c51002ffca208027fe530c413fe1966000ff886401e7f8a2a0812fe6090003fe102a402ff90a41007faa69000ffc5154801ff31aa404ff0c21000dfcc598927fc2150c7ffe10aa209fecc130007fa6508027ff62cc009fea848031ffd483104ffea798013ff500c059ffaa24201ff50a2000ffe431012fff2190c3fffaa4603dffc8241017fc84a0827fc65cc801ff18a4009bf18d20017f8872011bef52cc809fe2066004ff996100277e8120087fc54cc001ffb0aa400ffcc550087f88588002fd644c07dfe2848200bfd953200dfcc4a8012ff645003bfe10c6009ff10f31027fc80a0002ff6254007ff2a2a202ffd514315ffca890803ff31500137e32e603bffc8141007facb88133ff5290c01feb22641eff95230005fec4a1803fd6155013fe9886204bfd922007ffea308027fd530c401ffb22a009ff99431017fc86a106bfc524c005ff2a28609ff1973000ff84290003ff62540017fb22a000ff50d5119ff8c898802fd63904097e3026204ef99030025f8c0aa013fd3004003ff2924200ff58d4104ffe6398003fe6350801ffb226009ff58a5304dfec8188c7ff540c401fea0c2002ffd024104ffacb988f3fc65504a3ff90aa809ff58730007fac6a0003fe43940097e3142000ff54521037fe4208003fe5150009feb142005ffd82410057ec890813df308c05dffa844200ff5922104dfec998803fd218c0057e322a409ff94e4309ffca890053ff5448003fe1944204ff992301fff8c4a8817ff65c40097fb102004ff9422004ff88799003fe4344001ff9928002ffd014100f7884a1027fd6090c017eb2e6000bfd8d21027faca18013ef2088001fe30a6002ff55142177fea710813fe6404001ff29c4000ff589530177886aa00bff4390009fe106202dff10221007f62108003bd5450009ff1022001ff90952017b886a187bdc438c00bff1886209bf1903100ffea510107fe6294401ffb222009ff59730087fc6588007ec32480017eb2c8000bf5833124ffca4a1803ff6155001ffb1aa805ff1964101ffaa92800ffe5254401ff20c2042ff10e5100ffca490027ff32cc003bf292a400ff5463001ef8a328003fd6290403fe2928404ff99410027f88018007de32cc807ff28aa000bf58e20147fe82a8007ff20548057f322a609bf1964304ff86418003fd4204003fe90a4000ffcc621007fca608113ff504c8015fb226002bfd854102ff84218827ff530c001feaa22003ffd4954007fa8718007fc324c801ffb026400bf58c10005fec098827fd5390c0bffb286209ff90d31005fac520012fc658c0017eb166018ff15030027fa2008013fe5004001fe3028609ffd0f32007faa29000
  | 3 => 0xfa066009ffd933200ffe651000efc6590407fea8ca044ff145321c7f8a598827fe5350c13ff30e6000ef55243007fac518802ff62c4013fe304a609ff90f32027f88008003bd4350001fea0e2003ff14d5203ff8a808003ff62440137e3266447ff9954204ffec321817fe510c403ff2144204ff94230005fac398002fd64940017fb1aa033ff9513100ffe4290002fd618c003ff2126409ef10d43025fcc008002fd600c409ff31c2004ff1862004ffac99903bfc4384009fea042000ff1815104fb887298d3ff544c407ff29aa201ffc822104ff8c529803fd428c009fe31ca004ff5865012ff8a520027fc6590c01ff3046200ffd9520007f8c0aa00ffe5294c07ff294a000ff48510027fc8008013ff3084001ff9882000ff985420cff8a218003fe5348401ff3048200ffd951002ff88388003ff6550c017fb2a8200ff54510017f884a0827de53cc02fff2106001ffd4921005faca9880fff5454c097fb2c4002bf19251177f8a110806fe629000bfe10c6201fbc81211eff84120807fd4248007fba8aa202af19130005faca18827fd6494c05ffa0c860aff94910007fac8a9003fd43440097e324a009ff9883104ff86298047ff42c40097fb182037ffd5231027fc6088027fc6090c09ff2066004ff59030257fea4a1813ff200c05bffa044201fb1495204ffac199003fd544c001feb2a401fffd4a30027ba6018013fe5048001ffb02a436ff95231007feca98043fe62c40097e3148000ff90e510affe8310017fc648847bff1948203d7d4e5301fe8a328803fe534800bfe3162004bf18121027fcc508007ff5248001fe9022000ff98554027f8a018007ff204c809ffb102009bf1973101ef8a128807fc52cc827fe3224004ffd843001dfccb98803fd624c477ff1928200ff4c52017ffe421884bfc53c4089fe282640effd0e10007faa298943df4394c097e3242003ffd4d52005fac899003fd3148401ff28c4009ff90d30007fe6408003fd52c4001ff31a203cff14141005faca18002fe6194c055f3206000f718d4002ffec1108cbfe524c4017fb22a404ffd0030027f8cb1006bfc624c09dee21aa600ff50d31025f8c910003fd318c05bfe2a44227ff9895004df8c690803fd63c4045ffa866002ffd0554005facaa1813fd6304001fea9c6003ffd4150007fc4308013fd6188007fea9aa200ff54d43005fec09909ffc3254049ffa828000ff54d2104ffcc018802fc6150c07feaa4a201bf98f32007fa841890fff404c8097e3028404ffd9250007baa798003fd518c407ff292a604ff18a50007f22008077fe528c003fe212a400ff8c52100ff8429080fff53540137f31a4002af1912101ff8a52810ffc544c813be29aa600ff0c65001ff8a8a8013fc4050001ff18c604ef7d0d5301ff8a528802fd6488407feaa4a607ffd04
  | 4 => 0x803ff6454c01f6a92400aff9891004ffe6518002fd64c4001fe31a824dffc85531dff840a080bf840500017eb266204ff08030007fa849880bff545086bff90c6200ff54a410d7f84298027fe32cc00176b146000bfd964100fb8649906bfe524c0017e30a8404ff1922001df8ca9000bfc4150405dfa0c8202bf9933000dfcc498006ee6294401f7b12a60dff14a10007faa6880d3ff524c4017fb12a623ff1894013ffc84a8007ff3248009ff0802002ffd0a41007fa87288b3fe6548481ffa0aa22bffd05210e7fea898006ff6048001fea9a8401bf189100b7fea71006ffe544c04fff902a004ff8c13000fe84310803fd3144001fea146201ff10a2104ffcc998006fe6294c05ffa128224ff1454001ffca2a8803bf644c401fe18c8004ff0c310007fca290827ff310c405ffa0a8603bf986510dff8c898027fe5354c6fffa946200ff98141025f8c0a987bff418c0017e30a4000ff5952100dfcc518933ff5090c05fe2048603ff54e50027fecb20027fe538c4037fb228403ff94a510bff88418007fc2088401fe99620009fd951004ff86521802fe6190c09ff324a000ffd8121025f8c708003fd5250403773146000ff8c65001df8caa1813ff6304001ff28c6022ff1473000ff86510013ff620c0097fb1c2002ff1524302ff8c78804fff4148005ff2128000ff8c510005fac818027ff5390c09ffa844012ffd471002ff8c120827fc6194c23ff3262015ff1522000ff842a1006ec6254c03ff1944200ff5453004dfcc728013fc658c001ffb0a6000ff98e41007fac6aa00ffb50540017eb1c2001bb98810027f881100f3fc53504017eb206200bfd9310007fac4a8803fd214c001ff28a4029ff08650007fa8698083fe42cc0a3fe192a802ff95142007fac4a0807fc204c809fe282a000bf59131005fec8a8813fd6388001ffb1aa000ffd9521015f8c8a80a3fc6454005df2a28000fd94710027faa108027ff320c407ffaa4a00aff08510107fe419813ffc2194c09fe2828000ffd8553007fac8a88d3fe654c491fe20aa400ff9854000ffca4a1017fc640c40bfe28c4202ff90e40007f8c2a98a3ff40540017eb202009ff18b31015fec0a0027fe43cc401fe30a6409ff94e3001ffca928013fe40880137fb2c8603ff95253007faa698833ff5444003ff1926403ffd4d54007fcc2a180bfc4055017fe3222001ffd0952017f8a8aa013fc50cc013ff1906001bb18931017fe80a000efc6550401ff18a6201bf1894004ff8c321813ff5004003ff90a4200ffcc620007fac118823ff5304017ff2a22000ff4c12004ff8c39901bfc32040057e3244200ff18132005fec0a082ffe644409dfe322a600bf58a41027d84090013ff64880017f30e6000ff54e3102ffc8388077ff218c065fe10a6200bf5891000ffa8490937fc2154c43f
  | 5 => 0x8f1004ffaa799003fd424c009fd0802003fdd465104ff864a1802dc6350005ffaa4804affd4d4302ffec52880bfe54900073e32a2004bf18a30007fec098813ff208800dff2102000bfd9631007fe64a0813fd65840017fb0aa02bff101211cffca99880fff5054401fe30a8604ff94130007f8c6a8002fd6294491ffa1aa400bfd8142007fa82180fffc3254413feb006204ffd42300177ca92188ffc32500017fb02a400ffd855000ff88499027fe534c0017eb2c6000ff0c610257fea0a1807ff52508097fb202003ff14154007feca9880fff535449dff322a601ffd0a21017fc84aa0e3fe52cc405fe2a28603fe14150167fea690803fe514c401fe9822003dfd46510c7f88218006fe62500137f31a4209ff0ca300e7fea498003fd659047dffa8c8203ff15151027f8a110047fc43c4001fea862000bf58253007fc6298017fc5104007fea9ca200ff50310017fe8121807fc21cc801ff31aa800ffcc310277fe82a987fff538c003fea944201ff0c920005fcc208012ff6504029ffa824051ffc8154005fac9080a7ff2194007dfaa2a809ffd9643177f8a71080bf74150409fe204601eff1523000ffe84990dbff418c401fea8c803cffd4541025f8c099053ff53480057f3246200bfd8d2027ffe4329803fd2190001ee9886209ff0c831027fe8110012ff658c0017fb028605ffd8f10057fe4288017fe518c401ff31a4000ffcc521027fcca18063ff420c013fe2986023ff98940017f88520812fe6088001fea14a027ff1095009ff8a890097fe5290009f73102004ffc8010027fc811800bfd4390001feb1a2009ff50f31025f8c710027ff318c001de3224204ff10120107f88598003fd314c005fe2128000ffcc52001ffea528003fd54840017fb126000ff94d42007fec498813fe4048009fe102a000ffd89430277ac90800afe64cc801feb028609ef90d43007fc8708003fd6444005ffa02a804bfd9610007f8c690003fd4244005fda028000bf59710187fe8218813fc5004009ff31c8000ff54d30027fc4108027fe534c4097fb246000ff54830027f840a0017fc21944017e30a6401ff54932007fcc2a8026fc64cc04fff192a003ffd495301ffca728013fd6404001ffb0a8432ffc853100dfec699003ff6354803ff9924204ff9411001ffea529927ff2150c09fe1066000ffcc95108ffe8788027fc534c8017fb2e2002ffd0540005fec2a9027ff60cc463ffa806203ffd5251027fe8008003bf64484137f31c4200ff94d10005fec0a8802fd6194c037e3146209ff19330007fac098806ff624c847ff1928000ff58940067f8ca880c3fc400c407ffa8aa40cffd4910027fecb10002fd644800bfe20c8205ffd923102ff8c728813fd63900097e3202023ffc8140007fa6328003fd219400bff10e2009ffd4c31187f8a818
  | 6 => 0x1ef18a6202bfd9141007fe632812bfc5050c097f3048600ff94e40007fac7288d3ff534c405ffa0a8400bf58a43027fe8118003bf644c005fe21c8201ffc873204ff86498806fc620c403ff9024009ff94f31025fcc198807de324c875ffa966204ff90110027f8a09000bfc4350401fea0aa001ff4ca21007fe6288003fd4348407f7a92a41bffd0530015fcc89080fff5494c01feaa62026ffd4a40027fec808017ff6388427ffa024033ff1013104dfcc720803fd6454c09fe31c4002ff5054000778c89880efe658c4137f3182000ff5812100ff885100dbfc408c413fe1946236ff15231267f8a121813ed628c051fe20aa000ff94530007fa8728003ed6294401ffb1a8212ff9971019ff8a898893fc5350003fea166404df94150087f8a588013ff6504001fea0e6004ff08220007faa308013ff10040017f30ca037ffd4231007fac6a8803fd6354001ff2086000ff98132177fea310893fc655000bfe2886209ff8ca43007fcc29900bfc41500077e32a8002ffd0e41005faca0800afe6190407ffa9aa600bf5953020ffe4328887fc41cc0017eb2c8600ffcca50007fa4308027fd320c007fe2a2a600ff1815204ffe6298812fe6094001feaa6644eff10153227fcca99003fd3190051ff322a004bf1941004ffca799002ff6055001fea1c2000ff18552027fac3180bffe420c41bff2942000bf5873201dfccb99007fe3288051ffa12a048ff10d52007fac29000afe6454001ff9922004ff8c21004ffcc321812fc659000bfe20c4219ffd4430025fec90800afe648405fff9006251ff0815400dfec4a1007ff52cc801fe9928200ff98520007fec299003fe319000dfe2102000ff1813100dfcc588013fc63900037e3162009ff59031007faa720027fd53cc403f79066402ffd0d41007fa85288abff4194007ff2a2a603bf99430187fe8018813fc610c089ffa8a6409bf1925302ffc8310827ff318c443ffa166004ff18630027fa4108027ff328c405ff2148600ffcc95018ff8a018803fd6550c07fe28aa000bfd895101ffaa4a8147fe3255001ffb2a8400ff54940004feca90026fc6354417ffa0a2004ff0801001dfec0a800ffc53540a1ffa0ca604fdc421004ffe6498826fe6394c01fea0c421affc853001ffca328117fe54cc801fea966000ff18121027fac320007ff2150809ff32c804cff1464300ffca599073fe654c007ff2a4a200ffd8151007fac298012ff6284001feb128609bf18d501a7f8ca98803fd3290405fba0c8202ff552400b7f8a310003fe5144003ff2144004ef9921000fd884a101bfe320404bfe10c8009bf18d1000ff864908e3fc21cc4016e31a4209ff14f3015ff8a890827fe64cc4017eb2a8400ff18d21005fac89080fff5294401ffb02a604ff1901000fee4310803fe6054897ff9048600bf5
  | 7 => 0x980effc525049dffa02a61cffd413000dfec490813fd620c001ffb1a4000f7d8d2124ff840a1813ff648c001f63126209ffd0f30007fcc0a180ffc5054c09deb206001fb8cb32017fe852180efc65884037e3148200ff885401bff8a11880afe644c009ffb0c6001ff109200177e8120813fc6494009fea80603fff8c951007fc4398027f5310c401feb1a8401bf1893104ffac99811fff5350813ffb2e6000bf9864021ff88299073ff534c003ffa144000ff58241027fc809800bfc4155001fea082000ff98f1004df8c6a1002fd6294013feb286200bb5881004ff8a72180bfe4250c13ff98a6004ff10130027fcc608127fe3250c07fe282a204ff081201b7fe8118806fe6254c59ffa824205ff18a41005fac598877fe328c001ff21aa400ff5481001dfcca99003fd3254001fe98c2000ff4c94000df8c4a8006fd62cc801feb12a800bf1855400dfcc4aa013fc65840097fb1c4000ffd815404fbe6218813fd400c00bfe18e2000bfd8e2102ff88208012fe608c003fea944004ff59410027fe6018027fc430c019ffa822007ffd0810027fcc328013be4050003ff2124201bf1895422ffe839900bff4250013fe21a6402ff1514213ff8c4a8143fc4094c03ff1924000ff907300b7f8a7100b3fc5148401feb224004ff1941021ffe8699003ff329448fffa828403bf9961000ff864a10afff40484077f32c4000bfd8d5204ffa65980f7be4290401fe3028404ffd862004ff8c398013fc4094001fea9c2000ff5953101ff8a2a88a7fc3294013feb2e6424ffd454016ffe871080eff6154407feaa2a400bf5825104df8c7880d3ff504c413ff30e6402bf9931017ff84018813ff5094013ff30ca600ff8c61017ff88418813bc4050005fe2028414ff1952001ffea2a8003fd644c001f710a4203ff14d5425ff84121802fd6590413ff9926025ffc864004ffea72987ffc518c007ffa84a601bf189431fffc84a88e3ff21cc413fe194a601ffc812100dfcc52182bfc3244095fe32a8601ff14952007fac2a983fff5484007ffa9ca022ffd47301fffe40a880afd6490481ffa02a242ffd0651067fea688017fc608c409fa8802005ff1962100dfcc528002fd6284009fe2022004fb98a30025f8c608003fd42cc401feb0aa005ff18a5100ffc64a9077fe428c007fe2a4a60dff08610047f8a608006fc6290c29fe28a4009ffd0c3004dfecb98803ff6454409ef1826000ff90f10017fa8520127ff2050c09ff9046003df14a50017de84a1003fd6494401feb026400ff9055002ff8cb8802ffc54440137e3266202ff10a4301ffea0a98b3fc5048407ff29ca200bf59510005bec69080efe6544009ff2848000ff18520007fc4218013fe20c4005ff20a8009ff0c953077fca90800bfc4255009fe2846001ff9092000ff64110003fd6150c0
  | 8 => 0xfd9120167f8a690803fe5184005fe2a48026ffd4e4000ffe8490027ff53cc403fe2944235ff10a31057f8c48800ffc51940015eb206003ff14d5102ffc8218803fc615005bff3244200bf58830067f8a288013fe6588003fc1024009ff98a5300ffca4a9027fe62cc401fea086212ffd53101f7fccb20802ff6150c0bfe314624fffc825327ffc8529853fc534800bfe3106204fb8812004ff8a6a1802fc6154809fe3106000f718d2108ffca988133ff5190c13ff3148600ff59121017788121803fc6155001feaa06051ff1895400fde4310813ed62040037f314a201ff8c92126ffc64a98a77e5294007ffa82a800bfd8520007bca69800fff5155009ff904a002bf19231006feca90013fd3084005fe21a8016ffd4620007fe6320003fd544c809ff31ca046ffd4332007fa84a8807fd524808ffe282840aff90910027f86008026fc6354801feaa66209ff18a4302ff8c928803fd505002ffe2906003ff1525000ff86599027ff60cc815ff9022035ff8ca310077c872000afe648800bfe2086228ff10d50027f8a128013fc6290003fe2926434ff1453101ff6a128003fd21c4009ffb148009bf98e4304dfcc70800aff6350c017fb1a8209ffd4f3204ffcc1218cfff404c4057eb248002ffd014204dfcc728827fd6290c8bfe2a66400ff54330007fa6408117fc40cc805de2a2a809bf1973201ff8a12980bbc4390001ffb12a604ff58a40027f8a0880d7fe628c401ff20c4005ff1463100778c898027ff32cc4137f3186002ff90e41007fcc690802ff63c4009fe3146000ff54710027fe8128027fc43cc01bff90c2030ffd0831005fec898803fd40cc095fe28a8604ff58430087fca588013fe30c40017fb1a8000ffd8d4004ff8a618827ff64cc401ff10aa000bfd8d42027facb1800fff5094405ffa0c8000ff94640017fc86a0803fd43c405bfe21c420bffd0110217fcc92886ffc544c013feb066200ffcca40047fea208013f82088001feb226203bf1953004ffacb21813fd6494001fe302a601bf98a30007fcc098937ff2054c83fe194a200ff50620197fe409880ffc5494405ffa1a8000ff9473100ff84090803fd4284013fe1926004ff18c10027facb20003fd6354813ee1906204bf19230007faa418803ff6050c037f3142002ef10a41005fac690137fe4254c03fa10a4204ffd9630007fac4880a3ff4354007ffa9ca201bf9881000dfcc4a880bfc4190c01fe9062004ff9421000ff64090013fe1044069fe2826200bf59620007baa698012fe60cc801ff302a244ff195321affc851880bfc4250c09fe1046039ffd0731007fca70803fff5284001ff31aa01dff10a30007fec89900bfd5450409ffb14a03fff081511eff8a520826ff65cc0017eb146035ffc82310aff88310147fe62550017fb1aa205ff90410005fac9
  | 9 => 0x6dffa146200ff54641027fa811000efc65c403fffa8c6001ff1092104ff8a69880bfd5450013ff21e6004bfd8920027fcc910013ff63940017eb2c6203ff54d5217fbc641886bfe324c001ff31aa205ff0c621007fac299117ff40cc80bfe28ca200bf59540007fca788003fd62c4001ff8822000bfd9121005fac41891bfc50cc813fe29aa604ff18650027fcc818003fe6350009ff9844009bfd9330007fc8290813fd6588007feaa2a000bf583321effca520813fe4084003fe2128404bf188100a7fea290027ff64cc001bf28aa200ffcc610007fac8a8017fc63884017fb222000fbcca21007faa51880bfc4355025ffa96202bff105210077c82a0813f85094035ff3126023ff14940005fec898013fe6290083ff214a204bf1883004ff8a71880bbf4055001ff20a4029ff10a5027ff84129807fc2050809fea002004bf9821001dfccb8800bfd4390407fe292a000ff55330005f8c2a813ffc4294c13fb1886209df94d530affe8710027fc310c013ffa1c8600ff18550007fa8290803fe418c009fea802041ffc8251027f8c50801ffc4304013ffb14a602ff50d41027f84088013ff61940017eb244002bf9922104fde6499002ff6344015fe2122003ff1425100ff842a90affe6448401ff21c421cff1453004ffa6418883fc52cc077ff2928204ff082501afb8651880ffc5194c01feb1c4201ff8c94204ff8c999002fe618c007efa9aa600ff4c710207f8c8a8803fd418c001feb2a6405ff18031027fe6008003fd6050803fb90a4200ff50520005fac120903fc415440bffb006200bbd893101ffea8a90137c5054001ff3024229ff90a50007d8c4a980bff4355085ffa04a21aff90930007fe6508003fc6050413ff32e6202ff10543016f8a8aa027fd6194c03ffa124200bf5843004ff8a7180a7fe32940137e31a8200f7cc6311fff884a880afe644c43dfe20c6002ef1054104ffac129817fc64c4003ff10c4009ff1973118ffea2188f7fe6290435ff9026009ff8ca53007fec4a8803fd53c400bffb2c620effd0610005fac72800efc6550813ff21a640aff8c91004ffc86180cbfc424c481ffa12a205ffd8a41005fcc310002fc614c0017fb0a6405ff8c710007f8c6a8897fc3290001fe30a8401ff4ca20005facb988e7fc40cc465fe1026200ff98153027f8a0980dbfe648c43dffa146003bf59650027fcc408013ff50900017e30a8003bf19532025f8c0a90d7fc208c4077f32c8602ffd094326ff884a984ffc4148001feaa44232ff9093100ffc84a1002ff644c8137e31aa83affd433123ff8a2a101fff4304013fe1966200dfd9510027f881200cbfe324c403f62924204ffd8e2026ff840a980efc658c401fea946001ff5492102ffc4208006fe6250c37ffa026000fd5451001ffaa4a8813fc308800bfe10e2000b
  | 10 => 0x871085ffc210c003fe2166441ff8ca51007fc8298827fd64cc409ff1002005ff94710015f8c899003fd615487fff312a22bffd0d21007fa86a9003fd60884017f308602aff106500cffea818047ff41c4001feb02a800ffcc120025f8c0a1806fe629047dfe29c8201ff8cb3200ff84299003ff635440bfe28c8237ffd4631207fe86a8812fe6090409fe3246000bfd922120ff8852880abe6484031ff2a06009ffd8730287f88329807ff4250877fe3128200ff5454100ffe42a902ffc41440077f32c8044ffd513204ffecb99013fc6204007fe292a800ff5501002ffec928807fe528840bfe304a200ff58d20017fc82a08ebff54cc40bff20c622affd0a5021ffca89907bff438c003ff10a4239ff15331005fac720002fd65840017eb1a423aff14731137f8a320003fd5188413fe2186204ffc8240025fcc110803fd51cc401fea0a6200bf5864304fb88618026fe63c4013fe324a637ffd4e31007faa72080ffc53940a1ffa14a600ff88630017fea92080bf44150475fe2866206ff14810017fc8520003fc315408ffe29a8404ff98620007facaa002fff4244005ff2a28203bf19531007faa6a0803fd438c427ffa1a4009ff99332007f862a0007ec32884037f3126200bf58e2104dfcc31880efe658c0057e3226204bf18a5001ff8a2a9803fd6294413fea186000ff4c310007fac0a9002fd654c871ff2166200ff54910027fac518012ff6590007fea94a002ffd095401dfccb20807fe21480097f304a203ff94d5220ff841288e3ff20cc401ff21aa033ff10531005feca98006fc6250467ffa0a6204ffd9430027f8c908003fd418c413fe18e6005ffd9031007faa218013df300c001fe9086000ff58153027f8a120013ff5084007ff2a2a405ffd825101dfccaa18dffe658c401fea1a6400ff59542017e88320827fc60cc421ff90e2009bf18e21027fec518007ff5254819fe29a2000ff4c95104ffc641885ffe520c003fe9924200fb98a5102ff84320803fc6355001f690a4004ff8c030007fec0a1003fe608849dfe20aa601fb0c9320d7f884980cfff424c477fe10a8246ff14732007fa6518006fc624c059fe32a4201ff94932007f8c68800afc6448401ffb1a4201fbc815202ffec9108e7ff40cc40bfe20c6204ff08130167fea29080bfe5490409fe1824004ffd024000ffc8599002fd6294c1bfe1942043ff19132007fec4980037c6544003f7292400fffd4e100c7be8618007ff20cc807ffa8aa200ff50b10027f08120027fc4390c017eb266409ffd0c31277fe84a9803fd6054407efa9ca609ffd925301cf8ca90006fc62cc409ff2862004ff54220005fecaa0026ff6450c05ff21a800eff15210017fea8a0807fd3248001ffb2a8004ff10210007faa498813fe610c0015eb242049ff18943257fea2a1857fc4388
  | 11 => 0xba0030572d000000002704000600000206140c0986830000310000340010240000030150250a305f0830125c700302100000a00200201000a9d300a01c69100d00000600500201500c00e00901200000400000a02101c02a03c00900807802302900301101508200a0020010020000040040bd00405e00801407c2670021ec2eb09500f03601b02600000000101d1a600102100700000500000d0ff5be03802a06700612e0050000ba18f01ffca8a8007fd5250801ff20a6002bfd91541c7f84198803fd329401ffe28c2000ff5503104df8ca18813fc30440137fb286238ff10b3104ffca69900aff6555041fe10e6000ff4c621015fcc888067ff520c08fffa8a8400ff48730007fa6488002ff6244013fe29e644effd0d531b7fe8718923fc64548057e3222000ffcc710197f8c498803fd4354009ffb1c8004ff14210007fc871008bff54cc001ff20a2004ff90310027f8ca18017fe3188401ff20ca000ff9815410ffca998007ff524c805fea12821bff1053004ffcc12980ffd5154013ff32c862fff14831007faa710837fe4284085ffa14a204ff58e1004fee631880afe648c007ffa8ca000ff595411afbc6518803ff6150c01feb2a6004ffc8210005fac110833ff5144009ffb1c2005ff0c410247fe82a9013fc6384003f610a4200ffd915200fb86599002fd6204009fd1806000ffd912004ffa621806fff424c077ff3128200ffd894104ffec52180efd6594409ff314a003ff54a5104ff886a180efe6550893ff3128601fb14b32007fe6588006fc6254401ff29c8200f7d8d401e7fccaa080afe640c405fea148203ff14e51007fa6498803fd2154001fb28a2002ff10a40027f8c81800bfd4350001fe90a802bff10d210177882a0013fd508c0017fb2a2000ef9054000df8c59800bbc4390413ffb048640ff10d51007faa2a0006fd6288407ff292a000bf59253025feca18006ff6554805fda048000ffd8520005fac328002ff614c047ff2928009ff14d30006fca328006fc6294c016fb1a8005ff0862104ff88718033fe6544005feaa48609ff54c30027fec818013fd408c009fe104804dff9895304ffc6218013ff4084001feb028200ff54d32007faa398012fe600c001feb2a204bff14a4312ffc6520027fc62cc0057f3224002bf99030107fca598027fd43cc009feb24402effd5221025f8c0a08ffff2154479ffa928209ff18332007faa91000bff4350c7dffa948234ffd4531007faa090007fc528805bff2a44200ff50120015f8c898013ff308c001fe9946200ff50650005fac918026fe6390027fe21a4000ff5493004ffc6598802ff6255001ff2182001bf58a2002ffec51880bfc4150881fe202a203ffd4553197fcc498803fe5350405feaa48202bf99151027fcc518003fb1044001fea0a2009bf98d10007fa
  | 12 => 0x101d0002b400300100006101d0000107960030003a603100304100f0000240051f500000d0000100080090000320270020021f62a500100300100d00500601500002000003f0060670000010010011f100b0130080050000020180af00000000200701100205242f00001200100001600105807d00308603500002700501600100a01263000302d08400e00049c00003a00100500a00000200000d18c01000c0120270290060140040000140290030111f900a00000128109810d0051a405d01401925603f00000e0080000070060100a400500000001449e05a00000600000313c00c0082140300a400700001d01e00101004f07700000303700101a00001400400100000d0310d20720050260095d300004301c47501a00600100401c00300801200600200602c0010313fc06d00700000500100372a01100001f00000f03700400003100b0060310280010040d304503d00f02200000203900002201601800100114300f0aa00801500000212504903d0c100000a01400000701100602700702700f0031c500e00e00d01705b00100002e00301d02400000000b00d01704706d00500700407900101003400200101d00000802c08c00203d00c00200d03800903000001005d00603600b0010400005160120000070500040110000191e900400413002d00a03c00f0061e54a000000000000a0150889ab00b00001604a0030096c600201100f02c03902308600600400652f00400c2a800b01c00200800104f01f00600111704500007a00000003c05b24702f01300200c05a00060a00101e3de02400300201403900100100201100e00004336200a01b00f00103d00500000300100505300700700a03e6160020110040820030050050000010000002b902000e03600801f0050130270280030a600115704700b07c0000000400a200000900001e11e01f00925b0060050030008d300900100331203300103927a0130180d20190000007f82f201400000501d2ca19600005201b14503000500600000004000300200001400300e05100804700307100100a04600700800501f00300000000b01669200506112500000e00a02b0390080020110d900200800800000100b00002000000a00a24600400100a45502a00000f00142300902806901900300500100306901600001a0027d801500172a00100801200400d01e02900100200300000700003002b00111101d09200510000d00403504c4d310d38f01502f00b00001600600b00300701a00900000700f0090c200b00000600600000000000600a00000302a00100904101000000f00100700b0070010050000180000e80330070000040010d400001a00304000b06002202a02d0004a800000000a00503100400008019a05e01b0060000164cf0490240070000180810e001500e0030320490
  | 13 => 0x436501b03402900b03703200000400c00000507a03400300302300047e0000000d00071cc0210010018b400305d2f800e08d00002101500f0090000000360de03200201b01501b01100200b00102706200001600100300a00005604c01e00401417700002f08c0020d800600800000a01908804c00200301000400a00000305726900300400100000201101002800900806b00004f01500241218758105c01a4a30646bf01
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc4355030024fc7158f10235ee761895304ede7694d30006f47159132005ed7294520006f56188640054ff7258910006bf7459130004fd70d9132014fd75d895400cfe72d8151006bf640c521014fc74d891000fe76188521004fd74d951000cfe72185300057d75cc650006bf649053102cfc7158a5004cdc735911008ef54198640276be6454e1001cff7654140026ee4058a30024fe765523004cfe73d8941006ef74d893126cfd7654d320067c42d9510024fe768c65004cfe7688730004ff7458910004ff7654e211eebf72d912109ebc6459120026bf1059030024fc764c62004efb3058e30025f976c4210054fd768861024eee62d8943014fe745963102ef62118532004ff764c540004fe769452001cff765413000cfd73d953204cfc7358653024ff725883004e7e5359430004ff7458810006f7610c520004ff7654e2002cfe765522121ebc644c9301a67c654c510006bc64d853001f776194551004fc764c9100e67c654c1201767c658851004cff7694e20007f370545101267f50d9540006bd64905100067e73d951001cfe7518520004ef725954001cfe755931002ef64118542006df6390521004ff7558e2104cfe73d8954004bf7458e51006bc70d9121014fe74987320e67f50d95301ccff7159131006bd6494610136bd54d9150005bf74589100067f75589101ffe42154521024fe7655220004ff7654a40024fd71d891001ebe65551400f6de42d8d40025dc7094d3020eef2058a5104ebe73590303deef75d895301cfc75d8131024fc705954200cfc7259710006df6518d40005f4714c93124cfd7650d3202eef6498a51004ff725971004cfc76cc550005f870585520067f43d9510014fc745863002edf6398e5104edc634c510026ec2058a300067f65cc12015ebe71d912102eed72d9641024fc7648650005dd7398121006ec7259530006dd75d8d2117edf5218d2101cfe75d9132006f441d85202d67c40d952004cff7694e400079f6418d2104cfe7358a5302f766594710007797094650006bc50d913100cfe7218540006bf21d9131006bf70d9131004ff725951000cfe725913104cfc7359710024fc705933209dbc7458d20006ed7158a301fcfd7654521286df435925302cfc715973211eef20d894001cfd7218552004ff72593310657c7548110296bc70d9130006bf6450931014fd70d8940007eb70549200067d74d9510106fa20d8132026ed30588100067f65d8910005f77159540004ff7650b1001cfd70d91500067c6558520006ed62cc81004cdc73590302debc43d923104dde7390430005df735473128eee62d8954004ff7358a10026be4059230007eb7048520004ff715833202e7e5159631305df7350e30005ef7255332007ac7448520006bf71592100d5f97098d20006dc50d8d21004ff7059253
  | 1 => 0x8931014fe7498620006ee7058a5101cfc7558031006df50d8d40005f8705952102eee72d9631006dd6394e10026fa6018132006ef50d89310067e32d951017fcf2018d21004ff7650a3104cfe73d812101ef6655451002cfc71597300ecfe7618d20014fe7458b300c6dd5418d4004ebf7459331296bc4058243004ff7654d400069f64d8d21007bb7050d40306dc20d8d40014fd70d9540024fe7058a50005bf7454540006ef64d8953004ff7654d41004fd74d8550005fb7054730005f471589400079d5418d40005ef724c520005bd7190e411167f50597301a4ff7559531206be64d9151004fd75d9221005f471581541a67c6559531006de75d8d4001e7c6554140006f421d8543004ff765053024eec52d894304eec3258b3004cff76cc64000cfd74d81423f6bd54d9152005f4714ca101b6bc648c521025f4709471004ef77158730004fd768863002cfe7655031024fc7654a10014fc74d895004cfe769473000cfc7259230004fd75d8d2026eec52597320067d6554c101a67f53d95310debe7619130006df6398d42004fe7690530014ff715901000cfc725954104cfe73d8b102167d54d954104edd7118d4000dec7254d3202cfc7158a40004fd7650d2002cfc7418552004fd70d8943005f7714c931004fd73d8950004ff72594300067f6559120144ff7459540006df6354d4108dbc744c3100a57e7598d2004df6718c5311c6f621d8532004fc764c951024fc7358730004ff764ca41006fb6098141024fc765443026e7d525973202cfc764cb10004ff7458a100067f40d9520005fb7050510004fd72d8d50006f77158d1002cfc7654b10024fc705953100cfc7259131007b46190540006bf7458c1004ebe535903002eef62487102567c6559543004ff7650d21014bc7458e51024fc705933100dec7254e2004cfe73d951001cfc7558910026bf40596401afd721d8d21166ef5259521006f74198630005f47150d3101e746594510004fd74d8520004ff7655110006bc65d9130014be76d9131024fc705925304ebe435933102ef970d971002cfe7158a51016bc645052100cfe72d9120005f7715912000cfe72d91100057f755891002eef2118520007d551cc631016bc6490d21014fe74d8910004fe760c54004ede7018d40005ef7548520024fe70d8953024fc76552301d67f525973102ef431987321ecbe7619121006bd6450731035ec7254c10166ef5058a51356ef321853220eec3258a51006de72d8d4012eee4258a4004cff7359030026bf205921002cfe76cca51006ed6258251006ef72595420067f6554910016bc6450d2104cfc7690d51014fe74d8d51004fd73d8940006f5618c63002edc3158f100067f41d9510004fd76885402567e65d9543276bc41d9153024fe70d8943076bc4359210004fc7654d412e79
  | 2 => 0x67c6518d10024fe70d8d21004ff765493102cfe71d8d40016bc645512100cfc725931004efb305833202cfc7159410065f9709855002cfe71d8910014fc76541401a4fd7654531014fe7458251004ff7650e5100dec725512104cfc7358241004fd72d964102ef65198410006ec4058a51004ff7650830005df735483102cfc75d9310006dd6318d5202ef860582310067f6554d2000eec62cc950006dd634c61004e7c5359730005bf7448540006bf645453026eef21d8953006bf54d9130005df7350a3101cfe75d8d2024eee6250e51015bc744c540006bf645493102cfc715925302fe45158a51024fc7058a4304cfc7654130006df43596302257c7558132014fe745973004ebc6350d402d67f6518152004fd7498630006bf7458d20004fd72d8d4004cff7690e20004ff7558331007cf7254f30005f7714ca100067f6548510004fe760c510006bf651912100cfc72d8d2019ebf41d9131306de40d8d40024fe70d91532c76c20195201167c5159730004fd75d8121006ed625463001cfe7558630004bf7459531004fd7418550004bf7458d21014ff7650120006dc6394540004fe7694d2013dec724c550004fd71d952001cff76595420067e74d951002eec4158810014bc745891000cee76d89310267e505943001e7c6554130024fe70d8553014bc7459521006bf6454130026ec2058a40006fb7058910006f9601813204cfc7650531005ef7250120005ef7259540006bf65d9131005ef7254d422dfb431d91311a67f51d9531006f850d8143004ff7158a500f79c439063004cfe735943102ede614c431024fc7059640026ec2058a5001d7e7194650004fd764c810004fd74d9531236ee65cca21006ed7058a51024fe70d9151016be6455010016be6450a1002ef45118540005bf7448630004ff7558640006df41d8d21005dc7358540006f77159530006bc6458121004ff764c95000cfd71d95210a67e7619520004ff7258e411667c50d9521006ef62181311debd4259221056f5215862002fe42148410004ff705962100cfe729864000fce73cc92013eec62589500067f755952102cfc7159132026de3058e4002eec6458a5102cfe71d922119ebc42d9131026f61058640006f6615462000cfe725864004cfc73593100067c21d951002cff7598431006bd6488430025f870544301aedc42d8d2100dee720c520006f7411855041ede53d8d5402cff7694640004fd751854302cfc7598431006df735954304cff76cca50014fe7458b31006dd6394e4101cfe75d8540004fe7690d10006fb705911015ebc64591212febd6390e4000cfe7258f1019ebf43d913102f6e7294551004ff745873204ebd31590303b4ff7459542004ff7654d10004fd7690d212a67f61195100173f755514000cfc72d8d10004fd7688650196ee73d
  | 3 => 0xc755891001c7e76d9520006bf64d8530195ec7254d3102ebe4159310024fc7059250026f41098620297ba7090e40005ed7294730006bf7459521024fe70d913100cfe7298430006ef5458a3017edf4218d2100cff7658a41336f52118542006ec40d8931004fb7059521215bc7458e51006bf644c930006bd65d9131276de6454d30024fe70d8d10206bc43d915102cfc7690520024fe70d855410ebf40593300edec724c630006dc64d8d21004fc765511001cfc7558a4300cfc72d9540006df7359130004ff7654b103aedd43d8d420267c5059410004ff7650d52216bc6494531006ee65d8931024fe7694c1026eee6254c10006bc621913100dec7254e21006df63cc1201ddee7294541005ef7254e41006bf641812105ebf40d9110296be20d9130005f471551211aedc21d8d21006f850d813101e7e6554e30006bf649452104ddc7354130025bc705514000cfe725943104cfe73d8152006dd6318d5104edc7518d2102ef4610c520017bb6050d40006bd7559030006bc3259210004ff7459710016be6490610006dc62d8d4001cfd72d8d52006de5418d2127eef651895302cfe7650f10024fe76d8152006be32d9131024fe7650810006bf525903041ebd74d8d5402cfc7418553004fe7655130004fd7655210005f4715533104cfe76d8d2025eee6290e5101cfe7558831007777554510026bf50592100f5bc744c630024fe7018542026ed5058a3019ebc644c530005ed7298131004ff735901002ebe4159221004ff7654d21014fe74d951002cfc715962004ede6318d5400dec724c120004fd75d8943025f8704c630006de70d8d2121ded7298d4202edc6398e51014fc74d8d50004ff7650e2100cfe76d8953026bd2059210014fe7654140296bc10d913000cfd715881004edc7418d4024dec7258543024fe7655210007787544010005bd7090e4100cfc72d8543006dc65d8d40024ec7648520006ec725973117ede5218d21004fd74d8f100ce7f5259430026be10590300267f7559630026ec2058a1000cfe72d8d54005bd7498530004fe7694d42006bf7459542004bf7458c1004ede6318d51014fe76d9121005fb7048510024fc7058a40024fc705922004ef830582530067c6598d20004fd701855304cfd72d853202ef8605825100cfc7654d3204ede7018d2102eec315881004cfd74d854329e7c30d9510026be7059210236ec50d8953005bf7458e510d6dd3258e2001cfc75d893104edc638c521004fd7598643005dc7358121004ef7259531014fe74d8d52006ed641895305dbc744851002ef44118520085ec7254f10026be5059030006df2018d401afce3258a31004ff7655310004ff7158a30004fc764c94102cfe71d895002ebe415901001e7e65546100c6dd4018d40004ff755922100cfc72d91510c69c4118d40
  | 4 => 0x91311be7c658c510006ef40d8931197e4214c5211ecfd72d912106dec7254e1000eee6248650005df7348430146bc6459150014fc745833220e7d52d952104cfd75d8553006fb705952004cfe73d915201ede6554d3002fe67188521006ee70d895304cfc7694d4013eec32d895002cfc715922104cff7158c10004ff7650930025ee7054920024fe70d8532026ed4058810006de6418d21014fe74d953004cfc7690d52005f47159120005bf744c310014bc7458d21004fd74d89501e75f5394d4104cfc7359620005bf744c52101e7c655452101cfd741855402cfc7159631004ff7458a5004edd7518d4020eef7658a5102cfc7159332004fd72d9150006bc6458131006be651912116eed42d894102cff7688650015bc7454d4302cfc7298640006bd6490650004ff7558b313aede43d8d42006dd6394e20104ff7058d2028dec7258154014fc74d895326eee6254e30006ef7258f1001cff7654e300077865c41101eebc42d922104edc6394d41006ee629825114e7d42d9520004ff74588302febf70d913004edc6350d21006f77159120014fc74596311eebc6290541006ec625813100cfe76cc521006ee7358a51014fe7458630006ee6458a51026fa601815114e7f21d95201adde7618d210067c74d951002ebe415903102cff76887301edbe7290e41006ee70d89310079f648c53101cfc7558630026ee3058810006bc75d9121004fe7654931006dc4358f100c79c4118d4002cfc729864304ebf4358243024fc7058643006fb609815300eee6248310004ff7654a10014fe745822100cfc7259410026ec1058a30004fc76545401efac21d9121005fb7054e301aeef2058a31004bf7458910007cf6388521024fe7690630006bd65191300267c5059640006ef7259532007cc73485201ddec7258d410067f6554d320067f65cc51017eef2058831004ff7058a53005f67194d2101cfc75d814203ebf4359010006df635454017eec3218532014fe7458a5304cfe7655332196f62158732006f960181311eebf20d9121024fe7198430007db7054d30004ff7558620006dc75d8d40005bd749825113eef21d8950014fc745823102cfc7158830024fe7694e20007e87054920004fd71d9543286bf405925304edc435943004ddc7350831004fd75d8d10007ac6418931024fc765464016ebc6488530004ff73596200d6ef20d8930014fe74d855000cfe7298650006f4614855000cfe72592301eebd71d912100cfe725825302edc6358f10006ec7259543004ff7650e20006df43d8d10014fe74d9710015be74cc94011dec724c54000cfc7259430004fc765093115ebc43d91210ddbc744853000cfe7259251006bf6190540006be621913014f6c72d9520014fe7459510024fd73d913018e7c650c52032eef30d8931006df63985400067
  | 5 => 0x6ef629855302ef4411855329e7f71d951004cfe7318542004ff765523100eee6250a30005bf7458552004fd7694e21004ff7654f10006be62d9130004fd70d9121004fd74d8d5000cee72d964102eee5158810004fd7650d1004cff7658e21156bf4359250004ff7650a5102ef6610c64001cfc7654d310079c6418d21026ec7058810005f7714ca31014fe7458653004fd768c52004cfe7358a4302ef4319843101cfe76d951002cfc75d9231006de32d8d412debf31d913129e7c50d9710025f8704c9302867f54d95430f6df54d8d4002eef7258b10196ef2058732246be6454a1004fd43154d310267e5059620027b8405013002eec7158a5101cfc7558e4102cff768863004ede6394e20014fe745952004cfc73590302debc30d913114e7d70d9520005bc7155140004ff7158d20004fd7694640006ee64189530067f65905202e6bc6355140004fd70d9151006dc6350521004fe7690d51026ef1058a30004f47159540006ed70d8931006df63cc52132eee63885210667e71d951004ddc73547311b6bf40d9231004ed72d9710006bd6590e41006de32d8d1004ede6354e10026bf3059210004ff7458d201d4ff7159531024fe70d962104cfe7318540025f6709451029f756194650004ff7458f1004edc6390d2104ede7118d40006ef7259120166ed5358a512e5bf765524304cff764c521004ff71593301deef21d8941006f741d85531aedd71d8d21006f451d8543006ed624ca301b6f54198643006f461cc55004fdb6054d30006ef325822101cfd74d8954006ef41d8953005f47150b31055ee72945100067c6419520026bc405921004ddc7350531005f9708c530004fe7654d40004fd7650a300067d6554310006be7159030004fb705953100eee6254a40004fd74d8930005dc7350120004fd74d89532febe53d9130276df6354d431267c655012001cfc7558241024fc7650610024fe70d915204cff76cca103079f74d8d4002cff7398410024fe768c6200667c54d9510006ef43d895302cfc75d8b10004ff7258031004ff7259250014fc74d95101afd421d8d21005f67694510006df635414002eee2158a4104edc63cc12002cff7559431024fc7058a50026ee2058a3001cfe751854226eec42d895307ef551d855000eee62508100667e761951004cfe73d85540067f6554d30024fe70d963120eec62945311a7775194531006be70d913101e7e6554430016be645083001cfe75185320179e7390e40006bc72d9130024fc7650e100067d61946500657c7558910016bc64905202d67e70d9520004ff764ca1002df47150e31006ec6258153006ed7558a30014fe74d813217fcc320c52014d6e7294650246bc41d915202eed72d9710004ff764854004cfe76553310047f7558910006ec7158a300057f7550650006ec725
  | 6 => 0xb6098132004f77159543006df6518d21004ff7259610024fd72d8d20006df6398d40006f751d854004ede634c310026ee2058a4019ebc54d9131014be76d9121004ff7559121006bd7259210044ff76547102be7f60195200e67c655953002df4714c31002cfc769453001ef6659471004eec3258831005f571cc31001f7a6094650004ff7359641006f75118543026ee2058a5004cfc73592210667c5158650004fd73d9120005ed720c520024fc764c510004ff7058a43006f77159531006ef5258a4104edc634c521004fd73984100067f43d9520014fe7418553004fd751852000cfc725961001cfe7559331006dc6358121024fc7690e20006ef6258553306de20d8d40006dc54d8d21004fd765491026eec21d8953005ed728c520005f671981431aede32d8e2119df57198d4109dbc744c52001e7c6594520004fd74d8910015be748c64002ef6219862013eec42d8950186bc640c521004ff7059732004fd72d81511eebc32d9121004fd75d813104ddc73552302267c50d9532004ff7459530026bf7059210004fd768843037ef651d855224eef20d8943006bf50d912101cfe75d8142004fd70d8d5204ddf7554d30006df634c940004fd7650c10005df735413004cfe73d953001cff76543301eebd20d912102cfc7688530014fc7458a53026ef70588102aeee5358a3004ef77158643006bc715903002ebe415925102eec6248710006ef42d891000cfe7258d10374ff765464104ef7319865302cfe715922102cfc751853204cff7694f1004cfc7359110006be5259030005ef724c12013e7f5259620006f9601814226eee32d8953006ed53d893101cfe7558a4102ebe41592312567c6550d1004ebe3159030144fd7654140296be6090e41004bd74d8f10017bb6055140004ff7650951004fd765523101cfc755931002cfe71d9510024fe7059410004fd73d9520015bf7350d4002cfc741853002cfc7158253006dd6418d2107f775194610006f66154430004fc7650d1004fd7618c531024fe709865302cfc7690e21024fc7058e40005bf745414002cff760c650004fd7688640006ec4358810006ef73d893102ef6719865306fe42148610276df43d9153004fd74987300d5ee72945300f6df735923000cfc72d814101cfe75d8d10296bf6390e4002cfc7158332014fd72d854204ddc7350a30236ec65cc920005fb7055030004fd74d815200eee62cca51004fe768853002eec61485201feec625895100cfe72d9543005bf7458930006df6398d21006bf644c530004fd75d854202cfe76cca41006bd71590300675f5394d10306dc10d8d4004cfc765533000dec7250d20026ef7258a10006bf6488530004ff7159620006ef7259731004ff7655210014fe76d9153014fe74d9540005fb70591530667c53d9510004ff7459731
  | 7 => 0x8154026f61098620014fe7458d20084fd729841000cec725954002cfc7159430004fd764c65001cff7654d4302cfc760c520006bd6454e1002cfc74d8e2109dbc745852001cfe755883001cfe7598431366bc431855400dec724c520076f541d8540004ff7158a43006df63cc51002e7d75d8b10015bc7454a41004ff7655331024fc7159710004ff7158e50005ef7259530006ef625494100cfc72d912004ddf7654f30004ff765481004ebd735903001cfe7558430025ec70485203079e40d8d400ce7f515943002cfe7650b1004e7c5359732026ee2058a1014e7d52d9520014fe7458a3002edc3158e51006f44158630006fb7644010235ef7258d52196ee62d8931006df72d8d40146bc43d915000cfe7259031024fc7058650006bf64d8d210067f65d8d20005f471595301eeee6290630166ec5058a512f79e301913004cfe73d95213deec30d895302cfc7218554004ff7654d20006dd6394c1000cfc76cc120016be64904300067f755953200cfc7359732004fd7694d201e67c6550510396df32d8d4200cfc72d8554166ed7558a51015be7390e41296be10d9130006ec74d8931005f671cc11001cfd74d8d54026f510594100076e7294650005bf7459521004fd765513004edd76cc6310069c64d8d21004ff7259543004ff7459732004df73592502debc53d913102cfc7158251005ef72581310c6be5459030186f54118543004fd7694e10014ff7650310006ed6288630006f56118552006fb7058d2002ff27094710026bc4059220004ff73595212667c6590d10006ef7259543004fd7694d41015bc7454541004ff7459431006bd735921004ddc735033004ebf535903001e7e6555330005dc734851002ede3158e41005df7350310006f47159120005f9700c540005ef7254d21004fd73185401b6bc648c530014ff765922100cfe72d913001ebf7655243025f87050610006bc51d9131004fc764c5401b6bf4359231006ee755881000cfc72d8d410067f41d952020eef7158a5102cfc7598630005f77154310005f47159540006dc53d8d21296be50d9130006ef71d8953084ff76484102f6dc4018d40004fd7018552006bf71590300b6ed52d8950004ff7258d10014fe7458e51005f77158142004ff764c62017edc5218d210c6bf425903026eee7618953006f56118554005bf7459530006ed624c6300067e42d9510016bc6490d5101cfe76d954301cfc75d853204eec325883002ef671d9310006ed6250a51024fe7059030005df7350430006dd5418d21024fc70596212c76e201952000eee624864015ebe644861021ebc40d913201cfc75d8121006bc6418131006ec64d8931014fe74d8d20004fd7218553004ff7059121006f76198553006bd65d9130006dc51d8d21025f4765451014e7c42d9520016bc6450d32006f
  | 8 => 0x6bd72d9130004ff7259010276bc40d915301e7e6094650006dd75d8d40024fd72d912001e7c655511004ddc7348530006f76188550376f641d8554006bd645043001cfc7559030005ef7250d20006f960181520067f6598d10024fd72d9520036ec3258810025dc7654d30014fe74d8931024fe709864302efb7058031006ef5258a3014e7c21d9520004ff7059631004ff765463000cfe7650521206bf40d915104cfc735822119edd4358e41006be6519131006ef6248550006be42d913139cff73595321feec32d895128eec32d89543deef31d89530667c6559510026ef5058810006df634c540026ef7258810006df63885400d5ec7259530024fe7654e10005df7354531006fb70595400067d655433001eec765492004ebe4359030004fd74d8931006df7359250004fd7418532016bc6450d300067c6558910004fd73d9152004fd72d954300cfe7218543026ed7058810024fc765481001ede6554f3001cfe75591201cebe64cc610006dd63cc310204fd7654541004fd75d9130006ef7458a30006be75d912129f765094510006bc725903004e7c535964302ef66194640026df3059430014fe7458a3102eef6098a51014fc74d95310aeed42d89403fddf735954301c7c755891000cfe72d815429e7c20d95100c6df4018d40005bf7448730014fe7458810006f561484300e67e65d953000cfc7258251004ff715933204cff7690e5014e7e5258a5000eec624811000dec724c62102eee4158a5100cfe72d8143024fc7058e4102eee2158b1004ede6318d5002edc6398e21004fd7654b101fdec7258d511667c655952101ebe6555243004df7359521014fc7458f1015ebe64d912114e7e32d952000cfe72d8d40006dc6358940015bc7448540004fd75d85430067e64d9520006bf745912100eee6254810024fc7059210006dd6354e40074fe7690510026ee1058a30006f56118543006df43d8d211aedc72d8d210057d7598d20006ec6218131005bd74cc5401676f52d9521004ff74597300067f755954300cfe7259130246be64548300067d71d9520014fe7458e2001cfe7558d2104cfe73d8520014fc7458831006df5118d2117edd2118d2104cfc7690d21004fe7688550025f8705464001cfe75d8943006bf515903002ff251c41101aedd52d8d21006fb60981521adec7254e31007cf52d8d21014ff7650531006df6394d4001cfe7598730006f4614c530004fc76549411adde72cc631026ee5058a30006bf52d9130005df735073104edc4359030014fe74594311bede53d8d51024fc7694e10005ed71cc920196ef21d89310076f65cc92005df97098540004fd721854005ef541586401feec525952100cfe72d92310f5bc7448630004ff7654a31005dc735895102cfc7158a4314f6c5248650026f41098430004fd73d
  | 9 => 0xf5258b10024fd75d8950306de10d8d4002edf6398e2104cfc7358a430e67c654c11001e7e6554310014fe76d913202cfe71d962100eee624841002ebe74d8f10025fa700c6400067c6559110004ff7159130014fe74986501aedc20d8d21026f83058e30006ec6218553024fc70d911001e7e6554e2104ede6394c102367c65cc910014fc7458a50014fc74d8d52306de50d8d4015ebe64484301dcfd74d9221004fd75d8e21026f86098221026de3058e50004ff7654620006bc641812100cfe72d8d1000dee72cc52102cfe71d9540014ff7650e31024fd72d8520006df5018d400067e62d951001cfe7559130006ee6518931004fc7654d4001e7c655453102e7c6559621006dd638c620014fc7458e21014fc74d8d21006ec64d89532afe970cc920006bf2159210004fe76551203fede43d8d54004ff7458e1002ebc6459221004fd74d8532005bf7458520006ec50d8931004fd74d8e2104ebc4359331066f6515865024dec7254d4315ebf40d9121006ed74d895300cfe725923120eec4258a51026f7715864004cff764c110016bc645513202ef6719873202cff769063004edc634c11002eee7158a51006ec70d8931004ff7158e20006ef62d8553004fc7654d2105ebf41d9110005f97094e40216bc649452108dfb7058540024fc7654e4001cfe75d8532006bc75d913004cdc73592531767c505962104edf7518d2102eef72588311aedc32d8e21016be6490f10024fe70d9543004ff71592531ffe72154621026bd4058e40006bd6450a10006ef4358a5102fe4218c521005f7715011011dec7259540004fd76cc6201aede42d8d2104cff7694e21004fd70d9532004ff7059731005ef7250521196ec3258e21014ff72d9542024fe768c640004ff7650831004fe7654d41004ff7655221024fc705901001cfc755911002cfc7218553004fd7398650024ff7559430024fc764c6500f6be5459230006bc6458930005f47150d10004ff7654e4104fdb3054e300067f6518d2001cfc7558332024fe70d8910004bf7458d202bd7e76d9520024fc7058e21004ff7458b3002ef6511855302cfc72d8f100657e76d951005ebc42d911001cfe75d8940004ff735941000cef7658a51004fd76486302e73e65552431167f545973001cfd74d8554006ef629053129e7e40d951027e7d52d953239eef6318953014fe76d915101cfe75d8d400067d73d951002cfc7654e21006ef62509311267e65d95400067d6554e310079f7355243006ef725891000cfe725963119ebe64d913114e7d21d95200067d6554e2104cfc735824332eef63cca2100eee6254a30006ec74d8953004ff7158e40006de6518d21004fd73d9521004fd71d8943004fd731855008cff765041004cfc7648730006df7359121007b87055140004fd7650e21196dd3258e21
  | 10 => 0x49100067f655451004edc630c521014fe745891000dee73cc9202067d545964120eee3258a51004fe764c520004fc7650910026df7358e2000cfc72d954102cff7690650004fd768c6402f69c4018d4025ebd42d9132014fc74d85520f6dc435923002eec6258b1002df47150310005df7358910006f5619463002ef43198643026f77158620006ef41d8931004f47159530006ed6498a512779c4354e4132fe431d8931004fd7098732014fe7458732004ff7650d202f69f631913011dee729454002e7c5159410236ec65cca2102cfc7650e2104ede638c620024f47654510026bd105903000cfe725963004cfe73d815404cfc73594100067c7558d200067f65cc520005fb704c93002ef8605822104cfd72d9532004ff7458730006ef65d8931026ef3058810374ff7159541006bd649061004cfc7694d2001cfc75d8542004fd74d963100cfe72d8d50005de7694d3002ef661884302febc4358e40014fe7459531024f87059531426f55118554006ef62cc91002dde718c53124dec725954301cfe76d95402d76f72d95201ddec7254d4102cfe764cb102779f4354d40006f840d8153004fd70d8d4114f7b20d9520006dc631854004efb3058331004fe764c951004fc7650550026bf7459030026ec4058810015be7494d40004fd76cc64002eec6098a51006df43d8d20014fe74d8953004ed72d9631006ac64d893100eee6254a10006be52d9130196ec42d893101cfe7558221016bc6490d50004fd72d8141004ff7259130006f56154620006dc74d8d21006bf648c530014fc7458430005f47158142055f9709852000cff7648110006dc4118d2103cff765071004cfc7694d420057f7558520006bf725903001cfc7558810006bc52590303deec53d8953004bf7459530016bc645053004ef73158430004ef72595300cedf7654f3004edd7118d21005f77159530005f9708c630004ff7158253006ef43d8931026df7358e5001ebc655514001cff765412002cfc715954201d7c75486501fe7d525962100cfc7259253005f87058951005dc735815401cfc7558d20006bd6450e3000dec725452100cfe72d954101cfe7559010004ff715912004cfe73d9121004fe7650d51005df7350831004ff735865000cfc7259431006fb6098143004ff7654c10007cf43d8953004ff7654d42337ac2119121006f77159110004ff7458331006df735891001cfe75d922117ede3258831004fd72d8554004fd74d9521026bc505921002cfe71d8943004fe768c54002cfc7158e5104cfe76d8d42006ef4158a511a6f6515865304edc6354d4004cfc7655332014fe7458d2100cfc7650d32004ff715883019ede4358e41275bc745855300cec7259131025f8704ca302d67c30d952004cff76cc810014fe7458a50006f47159543004fd73d9510006e
  | 11 => 0x4ff7158b30004ff7655131005bf744ca41006af6418931014fe74d8131006bf645893029e7c505825100cec7259530006fb40d8153004ff764c940006ee5458a30004fd765483115ebc40d912100cfc72d9530076bf4359210296bf6590e40004fd72d9231004fd70d95210067f6554110006bf6450d30006bf6454d2101cfe7598620004fd7690430004fd72d953102ef671d96412aeef63cc92002cfc7498650006dd6350e2004cfe731852026eee42d89530e5f97098d5004efb3058243026ef405881000eee62508310a67c54d9520004fd760c640004fd7418552004ff725833101cfd7159410014fe745873001cfc75d8d40005bf745813102e7f755943100cfe721855402def7658a51025f47094510165ed7294521014fe74595210067d6554e3004ede6394e41004fd768c650024fc76cc510006bf64d812104f9c4350d3104ebf7459332007cf628c531005f4715813201cfe7559131024dc7654d30004ff7654b31004fe7650520014fe74d8520014fe76d9130004fb7644010006df2118d4033ef52118552024fe7655030005df7350a30006cc638852111ebd4259220004ff745865000dec7254120006df6398d50004ff7259210006ed628c630006df735954004ebe6350d400c6dd4218d40005ed7298554006bf645893107ef676945100eeee5258a3005dbc744c110016be6450e300067e64d9510004ff755883002cfc72d9631006df52d8d40014fc74d9520194fd764c5210edee729463004cfe73d85400079f744c43101cfe76d95301c6ee62cc410004fd7518530004fd74d8131014fc7459510025fb71440100067f73d951000cfe76d894004ebf3259030016bc6455330014fc7458e10026f71059610024fc7654830024fc70596201275f5394d40004fd7694730014fe749841023e7c50d954201cbf7655243064fd769461004cfc76507311167c65cc12002cff7498410006ef70d8953276bc6454d3102eef6358a5100eec6288540344ff7159121014fe74d8d50005df735814102fb44150431016bc64551302979e30d91300debf42d91301eebe42d9221026bd305903002eec2158a51006df7358d2104cfc735864000cfe7258630004fe7690d50004ff7648630006f721d8530014fe76d915002ef43198730006bf6590e41004ff7648640007cf63cc9200debe54d913004cde76d8d21004fd76cc9511e57c7558141005df73486400057d75cc951006bd6455030004ff755912002ef8605824100eee624863004cfe76d8d54004ff7650a3002eed72d8e2101cfc755873202fe57294710236ec54d895304ef83058332005fb705443002cfc75d8e21004fd75d912104ede7518d2102f745154621006f66154630004ff7359510014fe749865301cfe75d8931024fc7650430006ef62549310dcfd7650130004fc765
  | 12 => 0xe20d9510026fa109841002ef4618c5302afcc63cc920026be4059010006dd6318d41004fe7694d10024fe764c810345f7715912102e7c5159431004fd70d895101cfe7558d10024fc7058831014fc75d9150406be43d954302cfc76ccb102febc73d9130025b87055140006bf75590301a57c7558131025de7094d300057f7558131004ff7655220014fe74d85300657c7559110006bd649062004ef83058243006ed4358a3018e7c650c5101afcc52d8d21026f41058620006bd64552301eebf21d9121006dc43d8d5000cfe7259710004fd71d8d5411eec21d894004cdc7359250065f77554510366bf401855402ede3158c1001cfc7559210024fc7650c10195ec725953100cfc7259110016bc6450931006bf75d912102cfe7654f1029e7c10d9510005dc73485401eebd42d9121004fd764ca50006df639812101cfc7558831006ed6250831005f771551210c6de4118d4030efa40d814201cdd73d9153026ef7258a30004ff7458a31276dc4359543004fd7654a31006bf6454531076bf4159210004fd7650b30004fe760c520006bd6454a10025ee70cc920005ef724c5211bef55198653005ef7258f10006df6398d10004ff7650630004ff7650a10005bf744c640006bf745913225eee4258a43005de73981212debc32d9131006bc21d9131026f6109843026eec6254d310beef2158830004fd70d8532006ef5358a3000eee61cca21004ff7458653006fb50d81212f79c4018d40024fd7059410005ed7294430005bf7458553006be621913101cfe7558a43055ec7254d10006df6398d520067c6419510004fd7654a3004edd7218d21006dc72d8d4002cfe71d8d52004fd769454004ddc734863004e7e535973001e7e6554b31006ef4258a30006ef7259131006df6354521046f55118550085fb7058520004fd7650d21006be41d81414176c531895304cfe73d81510ddbe76d91300a67c53d9520004fd7650620004fe7654530004ff7648430006bc20d913104cfc7650330006ed65d893100cfc72d855302cfc7158243004ff745953201cfe75d81212779c4358d5404cfc7359430005f4715095100eee6248610006be70d9121026fa601815202e7f7559631316fa40d8154196ee71d8931006bf53d913000dee72d9521004fd729864001cfe7558e2001cfc75d894104ede6350e20006ec75d893104cff76cc62002e7c65596310067c6559120025be7050d400667f54d95102f6dc5018d40004ff7058a41196ee32d8931004fe7654d10026f6719864002ef44118532014ff7650110016bf609054002df471550100077765945100a67c51d9520004fd7498650076bc4259210006dd6390e20004fd7648730016be6490620014fc745873004cff7690e210067d73d9520014fe745962104eef3258b31024fe705881014e7c5258a50
  | 13 => 0x952002cfc7418520024fe7694e40004fd7694630004ff7059643016bc649053102fb44194541006bd755921002cfc7158a3002df4715081004ede7518d40004ff7059132006ec7258f100a57c755852002cfc7159120006dc7359250005f771553310f6de54d8d40004ff7650910006ed6250630004ff7158d1000cfd735883002cfe7690f1004ede7418d4032fe571cca21004fd72d8553024ff74d954000cfc7258d10006ed7358a30006ec6418931004fe76945401bcff7654431006bc71d913012eee5258a401eebf6490521024fe70d8d4202cfc715923002ef46594710006ef75d89312aeee4358a30006df735952124eec625894300dec72cc62104e7c5359431006f5610c6401a4fd73d9531006fb609815114eee5258a50014fe745963001e7c6554d20006df73591103be7d52d9542024fc70d8910024fc764ca5001cff7659641006bc2159210004fd74d96210c6bc4159030006dc63945211eeec5258a41006dc6318121005ef7259543004df7359121006de6518d40025be7090540006bf51d913001cfe7558c10024fc7654a4005cfd7690610006ee6398a51004fd768c550014fc7458e20004ff7258f10184ff765063100cfe765452114e7e42d9520004fd768c620005f77150f100067c7559110005f77158d4202cff7298410006df54d8d21024fe7058c10004ff765493000cfe7259430004ff7358b1028dec7258d54004ff7359250016be6455230004ff755873204fd7714c43100dec7294d20006df6398d5400cfe72d9631004fc764c940006ef5158a30005bf744c5501e777519454110efa40d8143005ef72585530067e5259710006be3259210024fe71984102e6be4359543004ff7655120004fc7655120004ff7458e211efae4258a41004fe7650d21146bf40d915040fcf53189532adec73549202366c65cc920004fd71d9150004fd7690e51006cf5218d21006bc621913001cfe7559030014fe745961032eec30d8931006bc50d9121004ff735822104ede63cc6100067f654c91002f6f5198a5114d7c729465000cfe725803102cff74d9541004ff75584303e6dd53d8d5200dec725522024ebf425933221ebf43d9132006ed5358810006f441d8532014fe74d8553295bd7090e40024fd74d8d4000cfc76cc521004ff7159540014fe74d853200cfc7259731004fd70d964102cfc72d9231014fe7458830006de52d8d40005df7348550024fc7058620006bd65d912104ede6390e2002edc6398f10004fd73d814204efb3058031006df638c540005df7359110004fd7690650004fd71d8d4201e7e6555010004ff764c94101c7e76d951001e7c6554d3226eec20d89530d5ec7254d30006bf6450530024fe7650a10004fd73d8141004ff7558831005bd7590540026f4109863002e7e75d8b10026bc705903029e7
  | 14 => 0x4ff7559310005f77150d31036ef7158810026fa76c4110006df4358f100067c73d9510004ff764c640004ff705964102ebf7459310166ec5358a51056ec32582212d67c20d95202adef75cc92001cfe755803104e7e5359732006df51d8d40004fd70d855301cff765473104cfc7358a4000cfc7258031056f621586201deee62d8941005bf744c620006ec7058a51006ec7458810026fa6018143004fd70d9131006df4359430006ed625081004cfc735925302e7c515962104cfc7359640005bd748c640026bc30592102767f5459643005bf744c110004fd74d971004ebe4359332014fc74d8550005bf7458d2002cfc7654a31006dd6318d10325fb705915000feb60cc920025f87050510006dc63549401feef21d895101cff765461001cfe7598732006ee625825101cfe755922000cfd75d815200dee7294520004df73589100067f6594d100067f6554521024fc7654e10206bf41d9151004fd75d85303c5ef7259542026fa601814117fcc2118d2134cff7654621006ec71d8953145bc7458d500e57c7558930004fd7498653004ff735881014e7d72d95201aedd32d8d21004fd72185541267c655011006eee5258a1002cff768c620004ff70587320f6dd43d8d4004cfe7359030004bf74587300d6df3258e20206bc42d9151006bc745952102ef671987302567f53d9543004fd70d85540267c505963032eef71d8931006bc52d9130006fb7059130006bf72d9131005f77150b3102cfc7694f1001cfe76d9521005bf7454e41004ff7558a311efb721d912123e7e65d9542024bc7650d4000eec6250931005f4715913200cfc7258e51006bf64551301aede20d8d21015bc7454540026ef7258830004fd765523010dbc744873004cdc73595400c6df4118d40005bf744c410166ec5458a51004fd75d8f1001e766594710006f75118530004fd75d923104edc7018d21006ee74d89530f6df42d8d4002efb6098231006be7259030024fd73d9530027b84050120004fd74d8530014fe745943004ebc315903038eef32d8132195ec7258131004fd7650b10004fd73d912100cfc7654120206bc4359641005ef7254e40215be7498251006dd6350c1004edc6354d42006bc64d8d21004fc76549402cdfb7059520006bd6448610004fd7654a40004f7715953032eef31d8931024fc76546100e67c51d95300067f65c4110004fd72d8143004fd74d815304edc7359253094fd7598410024fe70d8542005df734841002eec6358a51004ff755881001cfe759843004ddc735433000cfe7259640014fe74d8152004ff76546401267c51d9540004fe7655132006df53d8d400c6dc4218d400aebf43592200067f755954000cff764ca3102cfc7690f1000cfe7258730006bf54d9131006df74d8d2101cfe75986402e6bf64553302bf6e721
  | 15 => 0xc6454f3002cfc7498431004fd7598732024fc7650810004fd75d8d40026bd7059030004ff7258241006f5619464000cfc7259531024fe70d8941014fd71d9541004ff7059531004ff764ca50005dc7359540276dc6454d30006dc65d8d211a67e65d953100cfc72d9153004ff7458e20004fd72d815332eec53d8931004ff745822100cfe725921001ef46554510016bc6490c10004fd7694620004fd73d8552005bf7458951004fd7218550004fd75d8b1001cfc7558e21006be42d911000cfe7259730246bc64549310f6dd41d8d40004ff765081000cfe72d915104cfe73d9221004fd701855404cfe7398410014fe7458b10006ec621815302cfc7598430026be3059030005bf744c710006ed6254830006ec51d8931024fe7018553006dc2118d40276bf43d9153006bd64cc6100067f74d951000cfe764c120014fc74d95211deee42d89411eebd52d912102cfe71d89301d5f77158d51236ed51d89531deec20d894100cfe72d9530004ed72d964104edc329873201cfc7558a4001cff76543100eeec5258a30026be4059250006de62d8d40025f8705461002ede3158e2127eee5258a5302cfc75185422d67e40d952000eec625494104cfc7694d1015ebf43d912101edc6554d301aeec32d8e21024fc7058e5035fb43119131014ff7650731006df71d8d4001e7c659451002cfc73986530f6de43d8d40004ff7259251026ec5058810004fd76cc4100067f654c510004fd76cc55015ebf41d912104cfc73d9530206be6454610004ff7459410014fc7650110005df7348710026df7358c1002cff7694630014be76d9130006fb7059521006f6614c630006ed5458a300fcff7359530024fc7059230006bd70d913115dbc7458d2100cfe7259540274fd7654d4304cff7694e41004ff76553300067f6588510006f96018141306df63981431eeec629053100cfe76d895404edd7018d21004fd7654e4002df4714ca51005be7619130006ec54d8931006f7715913204cfc7358a5002df4715431001d7c754c6502febf32d913004cfc735864304cfd72d8132006bc745953106cff7158910005fb70585531cebf405933101cfe7558243004ff7058e51006bf6498131006f741d8520237cc53d895302cfc73986431eebe72d9121015be74cca41004ff7654e1028eef21d8954004fe764c9400a75f5394d2002eec5158a5104cfc7358620025fa7094e40006ef725952100cfe72d81410067f74d95201feef2059521005fb704ca30004fd72d913100cfe72d855400cfc72d9130006dd6390c1019dbe76d913104cde73d931004cfc735901002eec6498a51006f421d8530024fc7059031025f8705533022def7258d4202edc3158e41006bf644c93101e7e659473002df471552210067c6558d10026dc3058e40014fc74582510dcff7459130
  | 16 => 0x8520006f5615443002df67194e2100cfe7259610004fd7298643004fd76cca4000eee62cca5002cfe71d9530004fd768c5400667f52d951000cfe7258e50006bd651913104cfc76cc95006ef521d852002eec2158831004fd72d8d54046f7765471029e7e10d9510076bc54592100067e5259730004fd764ca51006df634c52104ddc735453104cfe7398643024fc764c6401aede21d8d21004ff705903104cfe76d8d21005f571cc110357e4311893104cfc7359520026f77158430004df7359110006f771595101eebc21d912100cfc72d9531006ef74588100d6ec21d893004cfd74d8943005f4714c11002ef62118542014fc7458830276bc6454d211aeee3258a31006ef7259132056ef20d891002cfc7518520005ef72585302ffb97090e40014fc7654d43005dd7390630236ef54d895304edc7218d21024fc76cc810004ff764c65002ef46188550024fc7359330004fd7694c100267f755962029e7c70d9510015be7390e40014fe7498730004fd73d815114f6c32d952004edc7018d40006ac641893104cfc7654b30105ee729473017edd2018d21024fc7059532006fb6098154024fc765051002cfc7159220005de7398540006f87059543004fd71d912017edf2018d2102cfc7650f1002eec2158a41006bc62d9130024fc7650a502f6bf6319130005f4715954301c7c7559110006f820d81511eebe32d91211f67c6590520024fe70d8e210079c6454d30006bc64d89302267c65595320d6ee32d8930005f7714ca51005df73552300079c648c531006dc6348540027ba64c4210014bc74587302b6fa20d8142004fd70d8d21004fd70d854200cfc7259130004ff764c9100069c6390540014fc7650d3100cfc764811002fe45198a51004ff7259310006bf651913102e7c515963104ede6350c102debe53d9131004fe7655110026ef2058620004ff7654a41006df7359532004fd76cc6500067f7559541005f47155210026ed3058a300f6bc4159230006f77159521236ed50d8953026de3058e100057f75581322aeee76cc920284ff7559543024fe7694630004fd75d9132004fd74d8d21014fc74d852004ede6318d4120eee4258a51004fd73d8550026bf4058e4004cfc7694d41005ef7258d54004fe76cc91002cfc71d891002cfe71d915002cff768c650005f771591530a76d721952000cee76d8953016be6450310004fd70d8941005df7358941026ed1058a3004cfd7158c10004ff7258643207b441545410067c6219510005ef7258d10006bf72d9130006bf6519130026f61058620025f576947101d67f5159731004ff7258c10394ff7359132024fc7059731006df6394d21024fc7058b31005ed729473102df4714ca3102cfc7158a3136ef641d854229e7f659461002eee415881004ddc72cc6310a67e65d952004ed
  | 17 => 0x5f77158132024fc7694c1000cfc72d8151024fc7059521005df7348610005f47150a100079c63905401a6dd5358e51004fd7694d21006de75d8d2115ebe7619121014fc7458b31005df7348650004fe76cc951006df63cc940006ed6254810004ff7654831004fd7655030004fd7690e5002cfc721854002cfc7518540006bc7458e50004fd76cc941006dc7359121024fc7655210006bf7458e50005df735952101cfe75d8e21004fe7654930006bc70d913104edf6094d3001cfe75d8930216bc6494530006ef415881002fd661cc63102cff768843011dec7254d40006f77159540007cc628c531006dc75d8d21006ee64d893111eee42d8940004fd75d8930005bf74484300067f6518d103edef72591520debc41d9130005ef7254d32006ec629815300cec7259543004fd76cca10006dd6318d421e67c50d954102cff760c620004ff755823104edf7518d400e6fa50582530047f755912020eec2058a51015bc745414000eef6054920006dd630c620004fd731855201cfe751854004edc63cc540005df735915004cfd75d8153006dd74d8d2104ebc435903021ebe644ca1000cfd70d9120024fc76552200edec7254e30004ff7359541024fe764ca1002eec2158a3104e9e7418d40026bf205903000cfe7258430004ff7458a30006de7618d21006f7715954104ede63cc310024fc705941002edd73d9310006f7619853004e7e53596432df9c4390430005ed7548520005df7350110005f77154c101aef5219873202cfe715962100cfc764c12002ff17094710004ff725973104ede6390c10004fd7688530004fe7654d20006bc64d81212867d54d95430067f6554520004fd7650e5115dbc744c521006ec7558a301676c5058a51004fd75d89310967c525971002eed72d9221006bc5359210006bc64585300067c65d911001cfc75d8d211aedc628c531005f7715411002e7e515964100cfc72d8d51006df5018d21024ff7158610024fc7654d3001c7c7558d200467f5459410005dc7358941005fb705464001cfc7558243006bc5159210007cc7254d30014fe74185201edbe7619121005df735433004cfc765013004cfc7359621014fe7459732005ef7254c1026e7f5259732086ec5258b1002cfc7694e210067c74d952032eec6388521024fc70d951000cfe72d8d410e4fd7654130006ef435881000dec72505210057d75cca503b5bf7459542006fb6098131006dc52d8d40006bd64944300067c73d9520004fd72d9530196ee42d8931005be7619131014fd75d8d5400eec6254931004fd71d9152004ff71591320267c5059610024fc7058a53006dd70d8d21245bc7458552014fe7418552004fd7654630004ff7650430004fd75d8142006ed624843000eee624ca3104cfe7318550024fe7018543014fe745823100def714
  | 18 => 0x7319873201cfe75185300267f755964024eee32d8943205be749815102cfc759862003ef541185401273c6555140025ec70cc920006ec4158a3021dbc7458132015bf7555243006bd6519121005bf7458d2135ebf61191311feee6254630004ff7259131004fc7654d102debd6390e410f79e54d8d40024fe76cc810025fa71c4110026bf74592501eebd72d912101cfe7598410006ee74d8931004fd7694e4000cfe7298431024fe7690c10006ef725953101cfe7559231006bf70d9121004ff7258251006df764c431006df6394d4101cfe7598630014fc74d9530005bf744c62102e7c6559710007af648852102cfc72984100defa40582430c6dc5418d4002ef64198640006bf64cc521004fd71d9530006f96018143006ed7358810006ed62cca50016be6450e31036ee32588100076c65cc92000fe77148520004ff7558221167e75158a5100dec724c52101cfc7558b310a67f54d952015dbc745952104cfd70d9530006be425921015dbc745812101cfe75d8d2104cfe735964304ede630c620026ed2058620005ef7254f1004ddc7348730004fd75d8143004fd7690d500067f6554d3100cfe7218550004ff7358a40026f41058430006ed62cca402afea70cc92034cff715952102ebd74d9641004be76191300e6dd5358e50004fc7650d20004ff7654941006f451d853004fcc324ca310067c65d8d2012ebf42d9120006be43986400f6dd54d8d40004fd73d8b10196ec20d8931004fd70d9231336bf6119121004fc7650d211efb421d912101cfc7559230005bf7454a41004fd759873004cfe76d8d10006dc4018d21006f761cc520005bf75905400067f655412001cfd71d895117cfe768c521196ec2158732004fd72d9130004fd73d95410a67c6548110004fd768873002cfc71596211aedf52d8d21005df7358540005bf744c610024fc7690c10004ff715925001cfd73d9153016be6450e50006f75118540005ef7254e20004fd76553302febc31d913004cff76cca40004ff7558d1002cfc749873200cfc75d8950026f6109863000cfc72d9543006df63d89401feee6254410026ef7258a40016bc6450130005ed729464004cff7694e10006bf745953101cfc7558e20004ff72594100c7d84018d401257c7558540006ee6498a51206be645443000cfe725964300cfc72d8540024fe7690e5002cfc72185430077b754401000cfc72d9131024fe70d95210079f64d8d21005bf744c650014fe7654d43006bd70d9130026df7358e4001cfc7558d10005fb7058552004fd7650910024fe7058a4002cfc7158810006ef651893100cfe7259250036ec425881001cfe75d8d4202ebf6190541006df63585401467f5459640004fd7418553004ff7654430006bd70d9121006f74118520096f5519865002ef67198643005df7350130
  | 19 => 0x8141275be7418153166ed5258a51006ed6458a51006ef7259540004fd731855404ebc3259030006ee7458a51006ee75d8931004ff72597302e5bf7355243026bf505903017ecc5218d21005f776547101afcf20d8d2119ebe644c61001cfc7559221006ef7358a51004ff7459631004ef7258d102779f43d9153006bf64d8930005ef7254e21006ef7258d21004fd765065004edc7518d40004fd73d81210067e52d951001d7e75cc95122ebc41593320079f6350d40206bf405964104ef8305833102ef6618c630216bc43d9641014fc74d8532005ef72506200067f658c51001cfc7558e10036f5211852024dee7298143004ff755921002cfe765523104cff72d9132006ef4058a5114e7d32d9520004ff7359121095fb7058550004fd74d812104cfc735825101cfc7559120014fc74d8951006f47158d20296be30d913002efb1058251006df4018d21006bc72d913104edf7218d21004fd7654b3100cfc73583320fedd53d8d502769c6454d300c6df435903004cfe73d9151176ed52d89510e75c6554d30024fe70d89512d67c10d9520204fd75d964102cff7690430026f41098650004ff72591100079f6454d30024fe709863002cfc7159030004fd765043002cfe71d964101cfc75d9130006ed6248410005ef7259131007cf724c4312aeec3158a3000cfe7259410005bf7550d40004ff735961000cfc7258253326fa50d815401cfe76d9531024ee76cc920006ef7558a30004ff73582512067f5459641005f77150e31005fb705952102cfc7655221004ff75590100067e6419520006f850d8121004ff7058a51025f670547100077b65c4110014fc74594102d67e20d9520004fd74d8d5204cfc7359641006ed62cca1001cfc75d8543014fc745973018e7f545943100cfd75d915204ef73158e31005df7350531024fc7059132025be7055140004ff7058e410067f6598520005ef7255121105fb7058d20024fe705925024eec21d8943004fd7654d10025dc7054d3002cfc7398732024fe768863000cfc725964102ef671d923100eec6248510005ef725452100cfe72582410c7db4018d4002cfe71d8d42004fe765055000eef604852006774655451004cfc7358a533deee53d8953006dd6518d400057f7558940006ed64d8953026bc7059210007af52d9121015bc7458a41056ec32d891004cfc7359250006bf6498d21006bf65d913000f6f7554920005ef724c640006ed74d8931006dc5118d4002edf7358f10006df634c510286be6494e10004fe76cc950024fc7098640006bc74595300c79e7418d40006ef624811000cfc7258430006bf52d913101cfc7558a4101cfd72d915215eed4258a4104ddc7350630006ed6518931006bc73d9121005f47158d54026de3058e2002eec21588102979d6390e400057d750c55004ef
  | 20 => 0x4fd7694e41006ef6254531006df630c540006bf64945300067d71d95102a7741019510007cd63cca21025fa70cc610006bd7259030006ed62cc41004ddc73508300067f65d8520006be42d9151006f7610c55000cfc72583311e67c655954119cfd73d91310d6fa205833209dbc744c120026de3058e30005f471501100667f53d9510024fc7159310004ff7259640406bc43d9543166ed5058a51014fe7498630005f47158153024fc7059131004ff765095002cfe71d8143004fd76486401cebc42593311eeef2058a41026f51059610005bf745815315dbe7498d21024fe768c530024fc7059543004fd7654e4104cfd75d8953006ef6258153005f870585532779c4354e4002cfc71d8d10004fd765531004eec3258b31004fd74d8951004ff7159543006de64d8d210067d6555330004ff7655121385f7715915120e7f52d952104cfc7358810026be4059210026ee3058a3000cfd751855202cfe7158e21064ff755951001cfe75d8b10006dc3258e10006f761985500c6de4218d403d6f551185521c6ef611893102edc3158c10004fd7655221005bd7550d40024fc7648630014fd72d8142004fd7498620006dd71d8d400067f42d951004edc435964300cfc7259210146be64d9150196df3258e211167c65cc11004cfe73d9310004fd73d9221004fd759862000cfc72d9520006df6354d4218cff765463100eee624c810006bf645853037eef52d855202fd651cc631005bf7458121004ff735954204edc3298431006f441d8550004ff7458251006bc53d91210057f7548310014ff765052104ef43158730014fc7459532004ff7558e1000cfe73987320067f6554130004ff7058d2102cff7690620024fe7098732004fd729865000cfe725933004cfd72d913201e7c65945400eeec32d8d20006df63d8540004ff7358910004fd74d855304eef3258a53024fc7650e3034df77159521004f77159132004fd765462004cfe73185520067e54d9510005f77154d31004fe768c5202dfb731d9131005ef7258153004fe764c94104cfe739862004ede7218d40056ef2158221006bf6490d2000cfe7654d32014fc74d8d20004fd71d9540004fd71d8d52004ff7458d10006bc51d912101cfe75d8132005bf7458132004ff735925102efa61440104176e531895304cff7690e5104edc63cc110004ff7159640005bf7458d100057f7548650337b7211912102cfe7690e51004ff7359621005df7358520004fd765081015ebc54d912102fe421945210067f655414004cfc735954000cfc72d814302cfc715954005ebe64d9110236ee65cc920004ff7259643026bc2059210004ff7258e100067c6518d20004ff715824302cfc7650e51005ed7298553026ec3058810026bd205903016ebe648861004ef43158732336bc42185421ddec725
  | 21 => 0xc4359543005bf744ca40014fe74d895104cfe731855402cfe71d95421167c525973019ebe54d91311aedf42d8d21004fd71d814226dec72581530d4fd764c120006ed6358a5104cfc7358b1002cfc751853004e7e535943100cfd74d854227eee6294c102367f5159732006bf648c531006ef7258d10024ff72d8d20024fe70d923114e7e21d952001cfe7518543004fd760c620026bf3059030024fc705963000eee6250a51004fd73d9710055ec7259110085ec7258f10165ee7588521004ff7258e401dcff72591211cdf77158d4100cfe72d9310024fe70d913201cff765454102cfe76ccb10004fd7655332005ef724c550006bc64185301eebc72d912104ebf7459330025ec7054920006dc63d8121014fc7458221024fc7690e102dfb67190e410f6df43592300267e505941001cfe7559330024fc705963102ef671d96310067c65d8d1002cfc7298653004fe764854001cfc7558c10366f54118554006de54d8d21006f56118540014fe74597102bf7b2019520004ff7159430014fe749843104cff7690e10004fd75d8940024fd71d951000dec7254d20314ff705954001edc7654d30006be52d91310667f51d9510004fd7654e20236ec75d895302ef6619462001ef66594510006bf20d9130007d5514c43102eef6458a51004fd72d85300657c7558d102a67c50185503fcff7359543004fd70d9542014fe7458620004fd7690d1002cfe71d81321d67c65cc52001d7e750c550004fe760c55001cfc76541102febe73d913002edd73d9231006df6418d2113dee729855004cff7359430005bd749815100eee624ca30014fe74d8d2104ede6354e400057f7558d1002cff72d95210179e6355243006ee7558a300f4df735913000cfc74d8940005bf745853002e7f755971001cfc75d852004cfc76cc54000dee7294d2100cfe7218553004fd76ccb10024fc7648510006f5618843013cff725952000cff764ca301767f5459621004ff7650d51016be645523104edc6354d21004ff7159030006f461cc52023f5f5394d42005ef7254e10004fe76cc520005f7715095102cfc7159431166ef5458a51014fc74d95400067f6550d10006dc70d8d2101e7c659453001cfe7558b101aede52d8d21006bf6450130005f77154e10024fc7059121015bc748c5400057f7558121025de7054d301aedf638c5211a67c50d953100cfc72d8d40007e57294510004fe7654520006f751d854301cfc75d8d1000cfe72d8553026ef7258a501cebf4159331006bc65d9131006f741185531567f54d95400f6dc41d8d401a4fd76947310067f6594d20005fb704c610004ff7058653236ee50d8953006bf7458730005bd741815302cfc721855002cfc7655310006fb7059531016bc6490521026ed4058a3000cfc725925102ebc645923104cfc7690d50
  | 22 => 0x810006bf7459541006bd73d9131006df51d8d21026bf7059030335be76d912102cfe71d89542f6de4018d4001e7c6554d10025f87054510004fe7690d21014fc74d8d100047d75d8b102dfb57190e4102ef431984300eedd32d8d20005ef724c62002cfe71d9153026ec2058830004fc765493000cfe725953002cfc751854300cfc7258f10055ec7258d10006ec535881002edd73d9631005df7358552017bb609054004cfe735903104cfc73d9130024fe76cc51000cfc765452117edf2118d21004fd7694e20026be4059220006ef629813100cfe72d8d510a57c7558d2004ddc7354a3104cdc7359121006df6350d2117edd4218d21236ef525973200cfe76d8951006f741586302eebf601913014f6f21d9520196ee624c410004fd7650f10006df53d8d21006dc71d8d400f5de7618d40026bc4059030006bd6454610006bc7458d2102cfc7159630004ff7258e5000cfe76501201eebc4258a41026ef7058a30004fd71d953201ddd73d915300cfe72d8f1000cfe72d9150005ef724c41002eec515881006cfe7688510006f76198554004ff755933216ebe648843002ef671d8e21014fc745943000cfc725925002cfc7158b30006f5611853000cfe72d813100cfc7259030006be75d9130286df43d9543024fe7690e20006ec7259110014fe74d8153024fc765065000cfd75d8d5200cfe7258251006bf53d91311f75f5394e41024fc7648610004ff735911000cfe76cc12004cff76cc650026f61058430006f56118553005f771550102debc6390540004fd73d8554024fe70d9221006ef54d8931006f77159131006f96018151004fd75d91312aeec4358a3004ef8305803101cfe75592301b4ff7650431006bf7259210014fe745803104cfc7358a51006bc745873001cfc755913100cfc72d8d54006ed624ca51014fc745973202cfc7498630306dc70d8d400079d54d8d40004fd75d814123e7c655954201cff71594100067f6590d10004fd7690f1019ebf42d913104cff7694d2100cfe7258e51006ec545881000dee7290520026f671986300067f654c52002edc6358e41014fe7458e21024fc7058e20007cf73485200067f655051000eec624855017eee4258831006f66148640025f87054c100267e5059640006ed6294630004fe7654540004fd70d96312f6dc2018d40004fd7655131024fc7655010005bd74cc940004fd74d815104cfe7398640004fd741852001cfc7558b10004ff7558a430e57c755853001cfd74d8154286de6494d3004cfd735903000cfe7359332004fd75d8d42006ee64d8953005ed7294620026de3058c10004fd75d854004ddc735503004cfd71d95312b4ff705912002cfe71d8154004ff745952012cff7459120006bd71d9130014ff7650d3202cfc760c5400057f755853029f7450947102e6b
  | 23 => 0x6dc6218d4002ef6419864302cfc7159643006bf64d8131007b9709054001eec6554920005bf744c120006bf50d9130004fd7598430036ee425881001cfe75d9310006df6394540005ef724c710015bc744c640006bf6450531004fd76cca41014fe7459530004bf7458d1001cfc7558f10024fe70d8954004fe765095001e7c659461001e7c6554541024fc7654e20166ee5358a51006dc6390521086ef2058b10004ff7650e100067f6555110006f7619853204edc735903002e7e515971004edc7418d21006bf7459540024fc70596100067f6518520004ff7650f102debc73d9131004fd72987300667c52d9510005bf744864000cfe72d9131006dc7358910014fe7459532005f77150d1004ef7319843101cfe75d814304ebc4359332004ff7558d203a6f541185420c5bc744843019cfd7650531006f661cc64002cfc769053000cfc725903102cfc7694540006bf5459210007ac6488521004ff7258640024fc70586301dcfd7650521006dc6398540024fd73d893001cfe759864304f5f7554d3007ef651d8550006df635052100cfe72d853004cff7690d21004fd72d8f10006df7359132006bf7459543006df6390d21276dd73d91530067f755951002cfe7158a4104cfc7358a10024fc7654620006bd75d9131004fd75d8d41027b964c4210006bf6450d31006dd6518d2102cfe76553101fdee721815100cfc7259543014fd73d894307cfe7694510025f87054f10026f61098650004ff764c951004fd765511002cfc721853004cfc73590311ccfe7690531004fd764ca41005f77158153004ff7559331007cc4318953006ee6418931006bc755921001e7e6554731014fd75d8554004fd70d915204fdb6094d30006dc6518d4001cfe755864014e7f52d9520196ee624c630026f86098241005f77159150004ff7459510004fd7690550004fd76cca50024ff72d912002cfc74d9631014fc745865300eee628863004cfd75d91530067f6558910015be7454d40006de74d8d21026bd50592101eebc20d912104efb7058243004ff705953202eec1058a51004fd7690630006bf51d9131006dc5018d212adee734852002cfc715925004cfc7654b310067f73d952001cfe7558b3102cfc759864001cfe75d8d41006ef62ccb10004ff7058d1001ede6594d30004fd75d891004cfc7654330024fe76cc65002ddd76cc631004ff7650d50004fd72d91512d67c70d952004cfc7359610004ff7259630024fc705922102cfc7418550005f87059543004f47159543106ec32d81322f79c3019130005f4715893010cff7059130006df65d8d40014fd71590101eebf71d9121005ed7290520004fe764c5400057f7559120006ec62d81532d67e10d9520015bc7454e41024ff7358c10005f4715894304cfe73986500c69f7359030005f7715
  | 24 => 0xf7254d31007af521912102cfe7654e21004fd70d8d42025ee76cc920004ff7558c10024fe7018532004fd75d9110026ef5058a30004ff7650e50005ed7298153194ff7258d21014fe74185502a7761019510004fd71d89530067f6559110005bd7498d2102cfc72d9310006be71d9130004fd76cca51004fe7690d520079c64d8d21006ef624c931004fd764ca40006dc635454000dec7255332004fe7650d2032eee53d893113cfd765412023e7c65509101debf4259221005ed7088521004ff7558e41006bc6498d21004ff74594301657c7558121004fd7398640004ff764c5500067f7559530006f56118550004ff76545403ce7f54d954204ebe435903102fe67294710006df635812101cfc75d81430067f654c110024fd7098410005fb705461027e7f52d953201cfe75d853019dbc7458131096f6615441000eec624c930006bd644ca10096fa50d8151024fe705901004edf7018d4000cfc72d911017fd72118d2104eef7258a43005ed7294531006be72d9131024fe70d9532004ff7259031005f77154e31004ff72584300067f65cc910006ee7458810027da3054330024fe76cc620236ef72597322debf71d9131014fc745862004ef77158653004ff745823104ede634c61004ebd5359030005dc7358910004fc76509511cebc64cc52101cfc755864001cfc755903102ef62118552026be2059210004ff7259030004ff755922000cfe72d9520004ff705954104eef3258b30024fc7358b3004cdc735952124eee42d894326cff7259532005ef7254e3102cfe71d9132006bf6458d21004fd71d91532e73d6555243024fe7688640026f6719862002eee2158a51027f271c4210017ba6090e401b6be648c610005bf7454e4000cfc72d8550014fc74d81530067f755953126eee52d895302cfe71d9543006dd64d8d21006bd6590e4001cfe7558e410067f7558d20006ec7458a30005bd74982310079c744c43101e7c6554d43004fd70d9543025f87055030286bf40d954302ebd74d8f100debe5458243017b66190e41004ff7258e51064fd7654110004fd765512101cfe75d894101cfe75d9231026bc1059210004fe765494002cfe7694f10276df4359543006df20d8d40006f5611854200cfd75d855219cfd769073100cfe72d97100057f754ca50337b4211912102eef6398a5129e7e50d97101d67c50597310d5ec72585300f6de74d8d400057e7619510026fa60181210267f7559610026bc4059230004fd7654810006dd6318d40166ed5158a51024fe765501020cfd72d952128eee42d895402fb67190541005f57194d2101cfc75d8530205bc7458d5101cfe755823104ede6394e10054fd764811003ebe54590102e79c4398d54006df43d8d5004f9c4350e302febc32d913002eef1058a51006be73d9121004fd70d9153
  | 25 => 0x8151016be6450e100057d7598d10004ff70591310467f53594100267c505943002dbe7190541006f77158d20006ef62885401675f5394d2121dbc745853204dde7390630006bf7458d10004fd73d8540006bf649812101cfc7558d2102edc6358e51006df6398d41006bd645083000cfe7650d322febf30d9130016bc6490d10006f9601815300cfd74d9542196ec62589311b6be545923102cfc71582311b6dd43d8d41004fd760c520026ef205962000dee72cc120014fd71d894128dee729855419cff745913104cfc76cc91001cfc755843002eec6258a51156be545925000cfc725973004edd7218d4019ef6415864300dee72945211aede3298732005ed7294610024fe70d8d41004ff7648650296be70d9130004fd72d815417edd5218d2102cfc75984101f67c65905100076f6554920005ef7254d43005bf744c51002ef66194430206bc6454531004ff725925304ef7315865302cfc7655031007cc724c43111cff7259120346f621d85420f79c41d8d4004ef43158653005df7358542166ec654852000cfc7650521024fc7650d3001cfe7558e4004cfc73582530c6df5418d4004edd7518d21004fd73d8520276bc6459153004ff7558e40004ff7558b1000cec7259731006bf645452104efb70583313df6e53d895300cec725911000cff74d9542166ee5058a51006ef74d8953006ef6218553236ee54d895302cfc715923100fce73cca21026bf1059210006ee71d8953004fd7498430004ff7458b10024fe70986401eebe62905410f6dd70d8d40024fc705964302cfc7159530026ec2058810005f771552211667f51d9521005df734851001c7c7558d10006bf6455131006bf6418530004ff715922004cfe73d8542027ea624401005cfd7650110216bf40d96410047f7558d1000cfc73d893000cfc72d9150004fc7654530005f47154110024fd7058c1002cfc760c550005ef724c62100cfe725925317edc4218d21236ef53d8953014fe7458331026dc3058e50056ef21d8910006ed7358a51024fe76cca10276bc6454d3004ebd435824302cfc7654831014fc74d8121004fd72d8131006dd6354e41006dc6354140024fc7654510236ec51d8953004ff755933002cfc7158221004ef7259543006ef42d89530173f755524304cfc735954112dec724c6401aedc52d8d2117ddc724c43141ddf73591530069f6418d21006bd6450c1004cff7694c10006df65d8d21006dd54d8d2120cff755952101d7e75cca5009ebc41d9120024ff7459030004fd7648650005ef725854304ef43158643004ff765503100cec7259531296bf6418143006dd6354e1002eed72d963101e7e6554e31004ff7558a10004ff7650b31006bd75d9121006fb7059543006bf7459131006f721d8540006f47159540286dc43d95430eeec7358a30005e
  | 26 => 0x16bc6450930004ff735931004cff7694d20004ff755903017edc2118d21026ef3058a30006ef6418953006bd6488610005f77150a10014fe745865002e7c6559641006bd644c610005f7714c310205bc7458951006bf54d912100cfc72d813100fe661cca2101c7c7559120006be7259210006bd6490f1004cfc7694d211c5ee729473101cfc75d8d4100eec628853001cfe75d8542004ff7458a530067f71d9520006bc7458d20004ff7059431006f96018154004fd73986201c6ef2158b3101cfc7559332006fb60981420967f5059710004ff7458253006bc6458931005ef7254d4102cfc7498430004ff7655132024fc764864000cfc7258730014fe74d8151005ef724c650006dc32d8d40004ff7459620004fc764853004cfe73d9120026ec4058a303deee43d89530067e54d9520016be6450610006bd6450e50026ec7058a30024fe7018554005ef724c610024fe7650e2004edc634c940006dc32d8d5104ede7218d2100cec7258d10005ee7618931004ff764853004e7f75597300067c65d8910006ec755881000cfe76d893028eec6258954006f8705953114e7c72d9520006ed75d89310f79c435523004cfc7690d20004fe7650930005df73501202767d5459643005ef7258d4101cff76545211deee52d8941336be421854204cfd70d8930016be6490e10094ff7059510006dd6394e40004ef7258f10145bc744c550026bc50590302f6de2018d4001cfc7558a3026dee76d89532f69e4018d40004ff7159643024fc70592311b6de43d8d41004fd7690e1004cff74d9543014fc7458a5104cfc7359210026f410984100079d6390e41004f47158d20005f77158d540067f7559120004fd71d895402ef970d8f10005f77155210007af64d8931004fc7654d20024fd75d91502debf32d9131006bd6494e10005bf7448550004ff7654b3000cfe765412000cfc7258243076f641d8540005bf744c530015bc744ca410057d7588650004fe7694d41004ff7458031026f7715865028eec20d895400cfe725931001cfe7559221216be5459251004fd7598640166ef52d9521024fd75185502779c43591532f6dc1018d40016be6190e4100cee72d96311aedf32d8d2102cff7688640005bd7390540005df7348530016bc64505100067f658c520024fe7694640015bf755514013eee52d89500bdee729443002cfc7158e40004fd75d9120004fd7690530024fc76cca1004cfe73d81411fe7f525962105ef64158640005bf7355140006bc52d913102ef6411854300cfc72593301aede628c531026ee405881004cfe7655330006ee7358810005ef7259150004fd72d9310004ff7058b31006bf215903000cff7648310004fd70d962128cfd75d9542006bf7458d211efac52d9121005f87058d54004fd7690c10166ee7558a51014fc74d
  | 27 => 0x74154641016bc6490d20026be5059210004fd71d8d4001d7e75cc65000cfc7258e50004ff7159530007cc7254f30014fe76d91100067d6554b3108efa40d8141006bf73d912121ebc644c931024fd7418540024fe7654e20004fd73d964104fd73154e31007cc638852102cfc7298430014fc745962101cfe7559210246be64d9152024fd71d9110024fc764c530004fe768854004edc6354d41006ef624c93002cff759841001cfe755873001c7e75d8b1002cfe71d91100047e761951000cfe72d9510004ff7558a4104ddc7348430006ed625441000cfe7258243006ef7058a51004fd7690520006bd54582430067f65d9120004fd7650a5004cfe73d911000dec7254d42005fb705895102edc3158e21004fd76550310057f7558930074ff71591102debc4358e41004fd7218530006bc7458e51016bc6490731006dd6354e20006bd71d91311aeee628c6300067f6558d20004fd74d9520006ef3218520006ec70d89530067f650c510056ec42d8910004ff71595420076f654852001e7c6554910004fd71d8d2000cfe729841000cfe7259543006df73591311eebe20d9121004fc7655121014fe74d9631004fd74d8b10006bd6455010276bf4059543005ef7258d5101cfc75d9132006ef52d894002cfc72d9710005dc735031002cfc7159031026dd30596301feec625453101cfc755933003dbc744c41002cfc7650a31006ec7259540004fd765443000dec725062001cfc75583312bf6c321952000cfe72d9540004fd7298630004fd7650a3104cff76cca41014fd73d954302cfc765083104cfd71d913111dec725854004edc6554f30005bd7498131004fc76509300067c64d9510006df4118d2100cfc735873204cfe73d8552004fc7650d52006ef52d8931005bf7448410026ee205883017edc321853202ef441986302979c30d91301bcff735953134eec52d855212eec3258a4000cfe7258e10006df70d8d21004ff7258231006bc64981311acfe760c521004fd760c65014cff7559520006bf64501200067c7558d1002cfe71d8e210f4ff73591302d67f6598152024fc705903000dec7250d320067f7558d1004ede6318d401eebc629054014eec3258a50006bd6450e3104e9c735903008ebc439864004e7f755973102eec6398a51024fe7694e10004fe768c510006f7411853226dec72591530a67f53d9520004fd72d8540004fd76cc91004eef7258b300067f70d9510344ff7650621005df7350830006ed6248310024f87059521014fc7459530006bd6490430005bf7458d510067c41d9510006dc6418d21006de65d8d21004ff735921001cfe7558f100067e525943100cfe72d9531006f7619852017ecf2018d210067e72d9510004ff705954201e7e6554c1021ebc6459132006bf64d893102df4715503114e7f42d9520
  | 28 => 0x854302eee3158a51014fd721854201cfc7559132006bd6454830024fc705943122ebf405933202ef42118543006ed71d895317ef52118532025f87048610024fc70986202879f4394d4004edf7418d21004ff7558a4001ef66554710004fd7694d4200cfe729873008cfd749841002cfc768c54000eee62cca40004fc765493120eee5258a51004fd70d8552004ff7358a512e6bc43d8d5404cdc73591201edec7254e4108dbc744c71000cfc7258c10014fd72d8d420067d655483004edc63cc5210079d7418d4001cfd70d895002cfe71d8d100067f6590d20005bf7448710004ff764c520014fe74d8d1009ebc43d9120004fd73d9110006ef42d8950005f7715913229f7771d951001cfc75d894319ebe71d9131024fc765503004ede6354e20004fd7598630035ec724c41002cfc7650a5104ef73198643024fe7398730004fd764c620006ec7258d100067f72d9510004ff7359221004fd70185430057d75985200067f6550520004fd70d8953004fd7654830004fe76cc550306dc40d8d40005df7350330004ff7258243004ff7654530006be651913032fe731d893100cfe7259010026ed5058810024fc7058e10004ff764ca5101cfe7559132005ef725911000cfc7258650004ff7558a30005ef7254d10006ed624ca31024fa76c411004cdc7358910236ed54d8953006dc41d8d21004fe7650d5205efa405824102cff72d9121005fb7050d30016be6490510004ff7458a51014fc7458650006be425933101e7c6554d302267f53d9532006bf525921002eee6198a51004fc765053001cfe75d814119dbc7459531005fb704c510004fc765513105ebc645911024eee6250c1000cfc72d815400cfc7259231005f9700c64026eee75d8953004ff7458e50025fa70cc5100067e52d9530014fc7458e5027cff75595321c4ff7158d21006bc65d912102ef44118550006f7614c530006df634c11005ebc4159110004fd72d8d51014fe7458d10026ed205962004ebf7359030024ff72d95203df6c53d895300cfe7259030004ff7258730014fe7458e5002cfe7694e21005f7714831001e7c6554520016bc6490730026fa601813100cfc764c93102cff7690730024fc7058a3100eec62ccb10004fd74d8d10004fd71d8153004fd7518532016be64552100adbc744c6200067e52d9540004ff7059543004ff7559231236ef51d8953026ef4058a30026ee705881004edc6394d4019dbc745893135ebe4318543004ff7159532026be105921006eec3258a10115fb7058d5002ef81058251004fd7650a51024fc705943002cff769473004cfc76cc940014fc7459431004ff70593310ddbc745953002edf6398f100067f6550d2000cfc764c52104cfd74185430a67f51d9520006bf71d91302f79e4018d4004cff764c120016bc6490530207b
  | 29 => 0x85ec724c710024ff755941001cfc75d9131014fc7458331004fd72d9110004fd760c54004cfe73d814202ef671d8b101767f535962102cfe7690e2104eef3258a43006ef6288530004be761913101cfc75d8540006dc5418d21006df638c52004ef73158643014fd75d815404efb705825314f6c52cca501467d5459640006f561946200067d72d951006ef621d8520005df735912104ebe325903029d7d7094650024fe7654c101fcfd75d9621024fc7654a30025dc7054f30166ef5358a511acfd72d8d211b4fd749843102cfc7158241026ee2058810006ec7358a51004ff7654e40006be75d913102ebc4159031006ef62485101e6bd5459251024f57694710196ee52d89310067c72d951004cfd721853224eee6250e30024fc70d8d10004ff7655230006ef628c531024f87059543004fd74d8552004fe7654d4202ef6511855401cfc755823104cfe7398653024fd74d9540004df735912001cfc7558b30006ef4258a5104edc3258831005ef72552201c4ff764c62102eee7158810014fe74d8f10026ec1058810004fd70d8954016be6450430006bd64906300d4ff7258d20025f67054510006f56148640016be6490630024fe70d8552014fe74d9520004ff7558f10014fc7458d2002ef671d96210d6ee62d8930006df635894000cfe76d894104eec3258a531feee62d895104edc634c54014f7820d95203be7f52d9542006ec65d893100cfd73d913202ef970d931004edd7418d21006ed5358a30005f77158930004fe765491037df7715895102cfe71d89401257c7558940004fd765083100dec7250e21286be54592531667e65d952104cff7694d100e4ff7559530024fe7694430154ff755954004cfc76cc951005bf745853225eee6290c100067f65501100067d65546100debf40d9130014fc7458a1001d7c7550650006bd6455231194fd7698e2101cfc7559231005cc73485202efbb3019130004ff7654940004fd7098643166ee5458a51014fe74597312debc31d9131006bf6494d210e67f53d953002ef43198653126bd545925001cfe75d9131006ef725911004e7f755964302df47150831007cf5218d2100eec624c9311eebe4258a41006f741d85320267c505962002ef671d9221004f471591321acde7618d21004ff74595211eebd32d91210c6bf415903002fd6614c4313deec73d89531667c65485100057f7558142005ef7254d30004ef7259731005fb7054c10004ff7259431024fe70d8d5200cfc725963100cfc725824129e7e30d95101cfb4415073101e7c655412000cfe76d894302cff760c64001cfe755911000dec724c620006df630c5212df9c4394e41005fb704c53004ef731987300057f7550a5000cfe725865304ede6318d2102ef4610c550006dc638854033cfe769452122ebe64cca10006f7211
  | 30 => 0xc72cc5200ddbc745893014e7f32d952001cfc75d8d200067d65550310067f7559520004fd75d8532166ef5158a5104cfc7359643004ff7158a53005ed7298550005f471591500067c62d95102debf6490730006bf6450510014fc7458732005fb705954302ebc4159010006bf6490d10005f97094d4001cfe75583320067f20d9510006ef7358810004ff70592511eebe21d9121006bd73d9121024fc7058e51004fd7690d200debe64d9130004ff7650c100f6bf43592300ddbe7498530106ef2058b30006bf6418d21005df735812101cfe755864302efb6098221026ef10588100069c6418d2102cff768c6400067c43d9510004fd7654730004fd741853001cfe7558732006dd6354c10005df7348540025fa700c5401deee6250410004fd75d852004cfe735943004ddc73548311d67c65cc51001d7e7588650004fe765091002e7f7559621005bf744c63004edc4359253006ef62cc950006ef7558810025f8705454004cfc765473000cfe72d8540006bf7458e51004fe769052002ef6219873200cfe7259541006bf6454d30014fe7459620004fd7218543006bd6448430025f47054710006bf7559210076bc41d854002cfc74d8f10004fd72d951026eec625895302f6d7294551004fd764c110004fd7655220006ec62981310067f65585201aedd72d8d2104cfd751855300cfc72d9510006ee54d8931006ef7259121006f661546400057f7548110006ef42d893100cfd71d91211deee6250630004ff7459630006de3258e10014fd751855404cfc735933104cfc76cc520005df7348630014fe76d912001cfe75d854301cfe7558a30006df5218d40004fe768c55000cfc72d853000cfe72596410c6bc425903004edc63cc510014fc7459620004fd71d8132006dc5118d211aecc628c5310067f6594510005ef725915301cff7654e31004ff7650931034ff7648710014fe7459410005fb7054f10026f6109841000cfc7259640006bc6458d21015bc7448640004fd74d8d2017fd42118d2102ef66194630004ff7650620024fe76d8142006bf6450930237cf53d8953006ed4358a5104ebe43593302c67f62195201aede32984310067d655501016dbc744c621004ff7259540004fc765095002cfc75d9221004fc7650520214fd74d954102eee2158a31005ef7250d3214e7e72d9520004fd7650e20025ee70485200067f65551201c5f77158d21024fc7058640006bf644c521006bc215903019ebc4158643024fe769062002eee215883102cfc7598730006bf21d9130007f151c4110005dc7358940005fb7058d51006ef725952002cfc7158a412f6de1018d40006ed624c810024fd7059010006bc75d9131024fe70594300067f655454104edd7018d400067f6558d1000cfe7258231246bc645493039ddf7359532014fe7654541
  | 31 => 0x5140006bf649453102ef65118550005df735894002e7f6194551027f26144010375f7715954104cfe7690730024fe76904302ffbb30d913001e7c6594d20024fe7688430006ef621815302ef8105803102ebc4159310005fb705451000dee725452002ef65198653024fc7648430005dd7390430026dc3058e1002edc6358e21066fa5058251086ec32d8b1001cff7654d3202cfc764ca41025de7054f30005ed7294541024fd721852002cfc7158e2004cfc7358650005df735503004cfc735952102dee7188521014fc7458031006fb6098121337ac52191211fcff725952102eed72d9621076be545921002cfc76552310067c65d85202979e6390e40004ff705864302df47150a5104cfe73d97101eebf52d9121006df6354d4028eee6255230006df631812102ebf7459221004ef7259131066f55158650006df639452102edc6398e4113e7d5259620296bf6490c10006f441d8553026ec5058a30004fe764c910024fe7654810006ee535881004cfc7650b3013eee62d895000cfe76d8910056fa2058221006bc6498121004ff7258630005f47158d20004ff7259531005ed71cca2102cfe71d8d54024ff7058810014fc74d953202cfc71d951001ebc7655140005ed72cc521004ff7058e21006ef51d89312aeed63cc92000cfc72d8153276df43596431be7f535963102cfc74984100f6df40d8d4002cfc739841001f767194650006ef52d893002cfc7654a41016be635524301cfe7558331004fc7648540195ee76d893102cfc7159130004fd73d954004cfe73d913015ebc6448530004ff764c410206bc64545211bcfd7598431005bf744861004cfe73d964102cfc7598732006ef53d8931006fb7059510006ef62cc94100cfc7258e40004fd7655132006bc72592100067f6554d4304e7c5359731006be525921002ef970d8b10017b6719054001cfd72d8152006f421d854029f7a7094650075bc744c610004fd7654f1004cfd71d893102ef671d97100957c754831004ebe43592530eeef2158a30006bd648c61002dec7588521014fe745883129e7f65181511aedc3258a3102ef810582212167f54d9541016be645503002ebc4159221024fc7058810024fe760c6500debc41582433e6de53d8d52016be6450731006ec6298553004df764c431155bc744c65002cfe7654b10006ee4358a5102cfc7498730006bf649053002ddf764c431004fe7650951007b7619054018e7c5259431004ff7559110006ed43d8931004ff735864001cfe755912102df4714831002cfc7650b10006f561cc64000cfe72597312f6de5018d40006df7358d200067f654c12004edc638c52001cfc7558a31026bc30590301bedd53d8d51005bf7448650006ef545881028eee625501002cfc75d8f1000cfe76d8931006ed6250a3001cfc75d813200de
  | 32 => 0x1cfc75d8d4206775711951004f9c4354d43006ed70d8953146bc435964000cfe72d815304edf7018d21005bf7458931004ff74588310debf41d9130007f0705451000cfc72590100067d655522101cfd72d855202df47154c10005bd749812102cfe71d8d50195f57198d2104ede6354c1005cff745911002cfc7654f101567d54d9540005fb7050e30014fe76d9152024fc7059641116fa50d8153006df21d8d40276de6454f301a67c654c5202debe43d9231166ed5458a51005bc7150d40006f561546300067c6598520004fd73d815202cfc759864302efb6098251026bf4098640004ff7650520004fd76551201666c6548520006ef5258a31007af6418931004fd72d8d410d6ec6258930026bd4059640005df73589510057f7558141006dd63cc610296bc50d9130004fd70d9531004bf7459521006bd6450e10004ff7654520166ed72d9521004fd74d8d5102ebc4159231006f7618c530024fe76cca500f6dd42d8d4004cfc7359121004df7359540234ef725953206dec724c610006e46148520014fe749843000dec72501200debc42d9130006bf20d913102efb1058221156bc4159250014fe74d9531004f77158d2001cfe7558e10006fb7059530025fa7094d4011eee62d8940004ff7358241004ff7559132006dd6318d2001cfe7558810005bf744c5402debe73d913136df77158941004fd75d894112dee72946400667e65d951018ef5511855304cff7690f1002ef6211852004edc6394d4200cfc72596431375f5394e401aedf20d8d2101cfe75d9130024fe76cca4002edf319843137fe75198a510e67c52d9530004ef7259110315fb7059540006f451d854004cfc735973132eee43d8931016bc6490e51006ed6290630004fd72d8d10006df63185400debf43d9130005df7358154025bc7050d40005ef7250e21006be735921000dec7254d21006bc62d9131026f4109864002ef5769471000feb6054920004fe76509310a57c7559120006ef62d813102ef8105824104cfd74d814314e7f70d9520026f86098231006ed624c410006be65d9130004fe7650d10025f8704c610006ec41d8953006bf535921000eee62cc81000cfe7258e40015bc7454e40006ef52588312f6bf6418d4002eee72d964104cfc7358a41004fd75d813202ef45118543006ed629825129f74509451002eee215881000eec62cc951006f72118530006dc43d8d213deec31d8953004bf7458e500267e5059630006bf6458131186be640c610004fc764855037f6c5098a51004ff725933002cfe7694e4101cfc75d91210067f65d91101267c52d9540145bc7448550076bf4259210004fd71d913011eec625894004cfe73d9520014bc7458e5024cff72591321a5f57198d51005ef725953128cff7259542005bd740c54024ebd4259332007bb705
  | 33 => 0xf7650330006bf6450d32004ff7258253004fd73d8542064fd70d9510014fc74d8530246bc6459152006ef4158a3000eee62cca100aebe54592200dede4358e4004cfc735891002cfe71d915202e7c5159641006dc7359540005dc7359120005ef7254d4017ede4218d2117dde724c431024ff7258810005ef725854001cfe7558a31004ff7654a30006be32d9130024fd705881001e7e6555031005dc7348640006ef629815302cfc7158e5004cfd74d95430f6de41d8d4000feb604852001edc6594d30024fc7058d210ddbc74585300067f6598d20004ff76548301feed6598a51005dc7358520256bd545925304cfe73d9542005bf7459531006bd645061004ebc5359030016be6090e4001cfe75d891002cfe71d8153006ef525881000cfe72d91530c6de5418d40024fc764c930005ed7294530196ec52d893104edf7118d402d67f72d9520306dc50d8d40006f77159121006ed54d8931024ff745901005dbc7458d10004fe7648550005ef7254e30006bd6490e103bcff75595423079c40d8d400667f50d951000cfe729865304cff7690d10006ed64d8931006f76198543024fe7059220006dd6318d54024fc7058a4102cfe71d8142024fc7058653004fd71d8d50006bf51592102bf6f2119520024fc7158b10014fc7458a3004ebc7359030004ff7058a310067d70d951001cfe76d9541006df7358d10086fa20d81210f6df70d8d400eeec4258a300067c32d951004ef431584300067c41d9520005fb7058d54006ef4358a30004ff755833204ebc43590310067d74d9520006bc6519131007cf7254d30024fc70595410a57e759852012eef2158a4004cff76ccb1002edf7358e21005fb704c630026f4105865000cfe729863009eed4258a4002efb105824110dfb7058d4002ebc415925125ebf42d9132006de5218d4002efb1058031004ff7159732004ff7059332004fd73d954204cfe73d9621004fd76cc940025f87050d30004fd73d891014eef2158a50014be74d8f10014fc7458d10014fc745952000cfc72d8d50007e87048520004fd751854004cfc765473104edc638c540014bc7458d20026ee50588100dedd4358e40004fe7694d40005ed729451003dbc7448410024fe7654a100c6bc545903002cfc7298650004fd76cc54004e7c5359430004fd70d954101cff76541100067f654811017edc2018d2113dec72591501efaf20d9121016bc645011002cfc71596410067f6554531006ef525873202cfc715925101cfe75d8520005bd74cca41024fc7650e502d76c20d952019ebf4058e413febf40d8d54006bf645493034ef621d855200eee6254830014fe7458c1021ebe54d91320047f7558d2004eef7258b31015be7190540005f471591531afcc21d8d2114dec724c65019dbe749813129f76619465001d7c754ca50
  | 34 => 0x8d40024fe76946202adec73485200eeee3258a3002ef6618864000cfe7258c10014fc7458b3000cfe725865004cfc735954202cfc7158c10004ff7359710005ed7218151006ef7158a3002cfc71593301d6f651d8553006ec641895304ebf7459253027e96244010007e67294510005fb70548100079c6494d301acfe7618d21005bf744c5200267e505961002cfc7688550004fd7648430004ff7650b30004ff7159230006bc515903002cfe71d9532236ee51d8953006bd6450e2004edc7118d40006de65d8d400eedf32d8d20014fc74d855302eec6258a31004fe7654941004fd749873220eec7558a5104eef7258a5302cff7498431276be64d9153004fc76551321aede72d8d2100cfe72d9641065f57594510216be6494610006ec65189310067c6518520024ff705941032eed76cca21005dc7358542006f751d8530006bf6448530005ed729814302cfe7159641006df50d8d2101cfe7558d2035fb73119131357e7311893104ede6354e41014fc7654541004fd731854204ef771587320057f7559110006dc4359630004ff7558e2030dfb705894002f7775547101b6bc648c531006ec62d8553286dc6494d30026f4105863002ef8105823100cfe76d895034eef20d8552026f7715863002cff76944301aedd20d8d21004fe76cc540026ee1058810005f970cc610016be6450e20006ec7458a5102cfe71d952002f7671945510267f7559410006dd6318d21206bc6459151006dc43d8d10026fa6018142025fa708c530004fd7654e1021ebe64d9132027f37144010026dc3058e20006f7715954309ebf40d9120024fe760c64004ddc7350430024fe70185521eebe52d9121006bf648c52104ef7315873200dee73cca21004fd7654b30004fd701853211eec52d894000cfe725864302ede3158f10005df7350630026f86098251004fe7694530006df634c120004ff7259541024fc705925102cfc72d9641006bc6519121004fd70d8d5408dbc7448710004fd760c55004cfc7359120004fd72d8550026fa6018154007cf4318953006bf75d9130025f87054730024fc7058c10005fb705953106eef2158a1004f5f7554f30006fb7058d1014c7e76195200beee5258830026be7059030006bc21d913000cfc7258640024fe709862011ebf425922035ebc4318543005df7359540004ff7459610016bc6490e5002eec7158810006bd6450310006ed72d8d20206be54d9151014fc745971000eee6248430167775194521006ef52d89430c6df4218d40024fc7650630016bf6050d40006ed6254a30016be6450330006bf745912014d7e7294650005ef724c51020eec52d95210067f650c52001cfe75d8131024fe70d854300cfe72d8d20004fd74d8132006bf7459110007776554510006bc649853001cff7659621004fd72d9710014f
  | 35 => 0x6dc63981210475f5394c10005f57198143004ff7159520024fc764ca40004fd73d895401cfe755862001cfc755883000cfe729864329f7410d9510016bc6450d3104edc634c120024ff7058c10024fd74d854015dbe7498121006dd72d8d40004fd70d8e21006bf6490d510067c64d9520006dc6354521006ef7258d20026bd4098640027f361c411000cfc7258e41007b87050d40004ff755913031dfb7058950004ff7359520004fd7690730004fd71d815200cec7258f1001cff7654531005df7359120024fe70d91101aeec628c531005ef7258141004ff7558243004fd70d854302cfc74986200067f7559110006bf6450d210067f6550120004fd70d9221006bc525921019ebc644c521006df635494001cfc755933107cff7159510024fc7058a3000cfc765012004dde73d915301ef465547100c6dd4118d4000dee7294620006bf73d9131236ef73d8953004fe7648530336bf6219121004ff7655010005f47154d312cefa20d8152016be649065004cfc76cc9410f6dc42d8d4000cfc7259510006ed624863002cfc764ca51006ed6398a51004ff7558b30005ef7258d50004fd7650e5002cfc7418532005bf7458d50004fd7318520024ec7654920004ff755903108ebc435931002ebc6459310026bd1059210004ff745843002cff745903102e7e515941001cfe7558a400f6df41d8d402d67e30d9520026bf7459210094ff7654410004fd73d8951004ff7059221005ed72cc120026ee7058a30006de6218d40006f741d8550004fd71d89302df9e6390e41007ba7090540276be54d9153024bc76551400067c6598d10007af7448520004dd73d931001ef4765451026eef20d8953024fe70d9541004ff7458630004ff7059521006bd73d913000cfc7258e10004ff765065001ef465945100067c75591200067e74d952002cfc769452000cfc7359332005f7715815401cfe75d9110006bf53d91213deec43d8953004fd7694520006ec6258553306df63181430067f65cc11004cff764c31004efb3058253004ff7359120016bc6450120004fd72d9541005fb7050610014fc7459731006bd6455210014fe7458253006bf641813129e7c40d9510006bf50d9131286bc6494d21004ff7654910086f521986200076d729465027eef2158a53296bc30d9130004ff7258650004fc764c520004fd73d9621014fc7458c1004efb70583321eebf42d9121024fe7688650004ff7650d1001cfc75591300eeec2158a3004cfc735943102cfe71d8d20004fd764ca1004ede6318d1004cff764c610004fc764c550004ff7358a4126dec7258553006df5118d40014fc7458a3101cfc75d8940007e76148520005f87058d51006be4259030114ff705953001cfc75d8910006ef64d8931004fd765083002cfe71d913002edf6398e410f6dc74d
  | 36 => 0xc645053100cfc725863000dee728c52000cee72d971013eef20d8950006de71d8d400067d6594730024fc7359730024fe70d89311267c65595400e6de5358e5004cfe73d9540075bc7448610005f7714c110004ff7358a50006be65d91312debf30d9131004fd7694f10025f67094710006df7359531006dc21d8d4004cfc735951001e7e655433002f756594710026bf7459230056ee62d89100b75f5394e20155bc744865004ede6318d42024fc7654c100067f659452002cfc7298730005f47154e10006bf6450521025bc765514004cfc7359251026dc3058e3004edf7118d2102eec6258a4119ebc40d9131006ec7358810006df5418d21004fd701854202cff7258831005dd7398540006ef6250531004ff7650550014ff7650610026bf7459010005ef7154920014bc7459530025f8704851001cfe75d9121006bf6490d2102eec3158a51016bf6055140006ef7458a51024fc7058a10004fd7654c10005f7715894304cfe76d8d52004ff764ca40004ff765473002eec2158b10026bc205903004ddc73507312b5fb7059120015be74cc540036ee5258810005df7348730006bf6455132016be64552200179e7390e4101cfe7558241276dc43d91530067f65d8d1002eee315881004cfe73d855001e7e655483000cfe7359732006bc6418d2104fcc3254d32006de32d8d4001e7c6554d310a76c6554920036ec32185200067d6554731006bc7458c10004ff7159730005dc7358141006de32d8d51025f671c4110006dc735952101cfd73d895300cfd7418542006dc40d8d21014ff7650e3004cfd70d9130005f57194e21005dc734855002cfc7158e21004fc7655130005df7354a3117fcc5218d21014fc74d8d5100cfc7259540006bf6498530005bf7454d43004fd7690620006ed6254a4004cff76cca510e5dd7594d3002eee72d9710004fd765533101cfc7559010006f56194430334fe769052102ef42118530004ff7258653025f87054d303ce7d54d9542006bd715921000cfd74d8d42015bc744ca400057f7558d20004ff75591310a6ed5258a50006df6398d51004fd71d8940006bf51d9121005bf7454541006f561185320067e621951002cfc768c550006f72118540005f47158d50005fb7054b1002eef6058a51026bf7459220006ed7458810024fe705964001cfc7558e40026f671986502febf31d9130004ff7158a4026dee7298553026bd3059210026ec3058a30026f6109864002efb105823101cfe7558910006bc755903002eec4158a51005ef724c530004ff764cb10006bd64cca10004fd71d815404ebf3159030004fd7654d2100eee624ca5101cfe75d8f101a6de5358e5115ebe54d9121024fd75d8d5002cfc768c520014fc74d81320fe7f535963002cfc7159640024fe760c620006f960181210267f7559430
  | 37 => 0x9130014fe74584300fede53d8d50006df735912019ebf40d9131007e46148520005ef725815417dcc724c431004fd7690e2002d7e7194551004fe7654d21006ee7158a3002eef21d8b1002cfe7650e21204ff74595410067e64195101feee52d895104cff7690d20006bf6458121005f77158d2001cfe76d9520006f56154640024fc709865026eee73d8953005ef7254d200067e73d9520306de70d8d40005fb7054540006bf73592100067f755954202ebf7459031006ed6248650024fc7650620236ef50d89532febc53d91300079f6494d30014fc7458b10006f7619854204cfc764c11002cfc7159520004fd7655010014fc7459630004fd76cc810024fd74d894004cfc7359220006df75d8d210067f6554d10006df6348540025fb764401019ebc6459131295bc7055243004fd7694430006fb50d8131006df40d8d21006f77158d21004fd764cb1017ede2018d21006ef53588101be7c658c520004fd7654640004ff7359220004fd7650e10014fe7458f10014ff765925125cff745913200cfe7259331004fd7654e21025f87050e30014fc745953102cfc715954302e7e5159431004fd764c640026df305963001cfc75d8930006f7715891002cfc7159532006bd64503302d76e20d952032eec31d893104ddc7350a3128eee52d895401cfc7558643004fd70d89311f6bd54d9151024fe7058e20005dc7350110216be6494430026dc3058c10004ff7655332006bd645522001cfc75d9110004fc7650d500c69e5418d401b4ff735913101e7c655451011cfd7650120004ff7650a5017ede321853202cfc729863001cfc7558a10004ff7558730004fb7059543005f7715503104edf7418d4001eee6554920014fc7458d21026f61058650004fd72d8543024fc7058732014fe74d8950005dc7348410006df630c520006ef4258810006ed7458a51014fe74d812104cfe73d8940004fc7654d42005f4714c9510073f6555140014fc7458253006dc5218d4014e7f20d952008cff7059110006f5614c63000cfc7258653006dc32d8d410975f5394f10024fe7690e10006f7614855000cfe72591100debc54d913002ef6411854024eec6250d31014fe74d95210067c43d9520006fb50d81431d4fe769453101cfe76d953200cfe72d855013dec7258d50004fe7618d1002ef65198650054fd70d8910006ed6254a1000cfe7258331014fc74d8152004f7715912012ebd42d912001e7e655522102cfc74d96212aeef3158a30004ff7655030395df7359132006ec41d8931006bc64d8131024fe70d8d51006df6398d20004fd7298653005fb704861026eef205973202cfe71d9120004fd7694d10006bc7359210006ee54588102366f5259732006dc32d8d10006dc7359120014fe7418532014bc7458d10024ff7059010004fd73d8941016b
  | 38 => 0x4cfc765533104edc630c520014fc7458e51005ed75cc920024fc7654e3002df671cc3101afcc328c520186bf4059031025f87054810005ef724c630166ee6548520014fe76d9131006f761cc550006dc7359110006bd645443002cfe71d8152004ff7558643006df63cc110004fc7654520006ee4358810006ed6418931025bc7090540026fa601815332eed63cca21005dc7359121016bc64551310067f6594530337af2019121025fa708c630004ff725953026dee72981530067c6558d2004cfd73594302aeec5358a30014fe7458a51006fb20d8151004fd73d91501ecff745912101cfc7558221006df63cc54005dbc744c51001ebc6555243006be7559210014fd72d9542024fc764ca10004fd7654d2000def7554920006af64d893101cfe7558b300067f40d951004eec3258a43006ec5158a30006ed624861031efa50d815202cfc7690550024fe70d8d54024fc7694e20195ee7294531067746594510004fe7655131024fc764c810195ee72981311775f5394e21004fd7690e21005dc7348710005bf74485100067f6594540005f7715894017eec52588311aeec5258a31006ef5158810026be4059030004fd709865301cfc75587300067c65d9120076bc7159210005bd7494d4004ede6318d20014bc7458c10004fc7650d51194fd76cc621025f87054e30006ef7258e210076c6548520006bf6490520026f610586302567c6550d2000cfe725951004cfe73d8951004fd7298430005f7715083101cfe76d9542005dc73591103deef6218d5204cfe73d954101cfd71d9151006dc63d894002ede73d9310024fe7650c10024fe70986502869c6494d30014fe74d8930004ff7459621006dc6518d2102ef671d8f100d6ec52d89301eebc52d9121006ec62d8131007d87054d3023d7c7558142146be54d91500067d6554430006bf645512104e9c6350d4002cff7694620004fd7650a10024fc76546300047f7559110004ef7258d21004ff76507301eeee4258a4102cff72d8d2104e7f7559732005f7714811004ef7315873001e7c6554110004fd7694d401edbc7290e41006ec5458a30005fb70553301deec6250531004ff7655130006f76198552004ff745833220eee6294630004fd72d9540004ff7458e5101d7c7550a5004edc7218d40014fe7418530296bf73d9130024fc7650e201deec625894105cfd70d9110004fd71d954202eec6058a51006dc635854004edc63cc940225ed7298d52004fd71d9132004ff7648550164ed72d9521006ef70d893104ddc7350130006dd6318d5001cfe7558a10006ed624864004cfc7654531005ed7294630006f76198540004fd74d9530004fd76cc950004fe7650530004ff7259641024fe70d9531004fd71d8143006bc51d9130014fe74d9621006bf6450110006ed43588102efb8301
  | 39 => 0xe2118d2104ede7418d210657e7598d10236ed73d8953196ec5258732005dc735814216774515452129e7e70d9510004ff7359640014fc74d8930006bf65d9121004ff715963004cfc7650b31005bf748c5400179f7350d4007f5f5394e1002cfc76885400f6dc54d8d40006ef6258131024fe70d912102ef641185540057f755854001cfc75d8141004fe76cc940024fe70d964121ebc41d913229f76509471004eef3258830206bc6454530004fd76507303b6bf42d91522debc639054104edc6394d21006ec4358a512667c6590d2032fe671cca2128eec625513100cfc7259331006df63d812100cfe764c52101cfe75590311b5be7498231004fd76cc52014e7c32d9520024fe76d81543deef30d895340fcc5318953005ed7294d21214ff7559541186bf4018543005f7714c951004ff7058831026bd50590302267e65d9532025f8704c5102267c654c91029f7610d951002cfc7158a5102ebc6459251024fc7650a30024fe7690650004fe7694d21005bc7155243006fb705912002ef45118530005f8705915302ebf745923102fd6514c431006ec40d8953004fe764c550006de7618d40005dc7359150006bf75d9131005f8705953114d7e7619520006df735953004cfe73d891005ebc43d911002cfc74d8b1004eef3258831005f77158d5002e7e5159621004ff7359540007cc43d8953004ff7558241026f67198430014fe7458332266bd54d91531e67c65505200067f21d9510004ff7259231017b76190541026bc4059010195ec7259131014fc7459610246be54d915204cff72d9532024fc7059732006bc7458d102ff9c4394e40007ac64d8931006df64d8d21004f77159540004fe7650d50006bc65191300ddbc744c530014fe74d8e21006bd72d913102ef6511855202eee5158a51006ed62cca51026dd3059430024be7690540014fc74d8131024fc7650a10274ff7459543006df75d8d400057f754c650004fd72d9631006f87059521006dd634c310006bc7458910006ed7458a30005ef724c54006dee7294610004fd73d91511aedf72d8d21004ff7558031005ef72541200067f6550910006f6614843002df4714c810004ff755891004cfe7359253006bd640c6101eebe629054000cfe7258e41024fe7650e101eebf32d9121004fd751854204ebc43593302debf649073112dec7254e400c79e5418d4004ede6394e40006ef62d81530f7d840d8d4001cfc7559121014fe7458a1000cff7658a51004ff7458b31006bc64d8931006df6354d21006be42d9130084ff70589100ddf97098d40005dc7358552004ff7259631004ff735862002cfc715901000eec62cc941024fe76cc640004fd7654a410079f639054002ef976c421004cff7690c10024fd75d8550006f721d8543006be72d9130006bd75d9130006ed6250410
  | 40 => 0xc810014fe74d85520967c65c4110196ef20d8931004fd7688550005fb7054d30005ed7294540006ed545881000cff7648610006ec7259531006df6394d422a67e5018550006be7559030004fd75d9310005f77159543014ff7650130024fc7058830006dc43d8d200069d5418d40026be2059030306df74d8d40024fc765083017ecc2118d21026bd7059210296bc20d9130004fd73d931002cfc7158d20006ef40d8953004fd74d9532026ed1058810004fe7690550004fe7690d201aedf21d8d21014bc745953101cfe7558e210aebc415922018e7f5059431004fd72d9153004fd75d8d2104ef7319843002e7f7559641006ee6358a5102cfc74986531e67e65d954104cfc765073002df47150f10036ec5258810005f970cc510296bf6498d4002cfe7159251006dc51d8d40004fe764c950005f771503102e79c73552431e67f51d954132eec43d8931004ff7559230024fe70d95101b6bc4059231004fd76506300d5ec724c53001cfc75d912000cfe72d8543006f471595301aedd42d8d21026bc1059030026bc405925002cfe71d8953275bc7458153005f77150a51014fc74d8931025f47054510004fd7654a10005f47158d42004fd7690d52014fe74d9532146bc64541300c6dc4118d4002eef6188521006dc53d8d4004cff76cc910026be3059210014fe74d8b10025f8704c5301aedf71d8d21004fe76cc1100067f659051000cfc725953004cfe73d9150004ff705923101cfe755933202cfc7654e4119ebe76191311deec32d89410debc645913004edf7218d4008ebc41d8141006dc63d854000cfe725953102e7c5159710006ed71d8931006f5611852004cfe73d89500f79c74d8d40005bf7448530026f61058610006ef62945310067e71d952000cfc725963004edf6054d3004cfc7690d10196ee761893102ddf714c431004fe76cc941004fd70d8d512bf782019520004ff7259230004f4715912002f6f5158a51024fe70d9542026f41058640006dd65d8d40006be65d912100cfc72582310d6ec3258d20014fc7459521004fc764c95032fce63cca21006bf7459530025f87054b10006ed7558810015be740c5401cef641d854304ede6318d52026f710594101aede3258a3102ef42118540004ff7458d21004fd764c91004e7e535973120eef20d9521014fc7458910004ff7648730006bf6490d503deef6298d520079c6350d4004ebc4359253006ef725953000cff7158810024fe7059620004ff74595312367c5059732005f7714c8100eeee4258a30056ec6258910004fe7655121004ff745862001cfc7558620004ff7558d21014fc745881026eee62d8953055ec724c510364fe7694541386f651d8554006bf5459030006ee7458a30006bf6454d3102df47154e3100cfc725864305dbc745891007e7f515961017ed
  | 41 => 0x1e0597f2000017c02d00700a8010012440000000006b00000bc0500de9208006038018068000000a036004014000000002f801c02603f00200b0028072007800000000200f000400000003683a800000200480000022b7012000004e0c501189c800000b015802c3be01a014800c0a65ab003801c00a00100a801001405101d00040b200506a8000136003020809401600a00080000dc00c00007dc042b44008011c02c00d000805c0000070cc800c12819500a04d401002a000000403600d0009d5c0054d206000d0004031000409800003c001810186e014002008c1ec036015802400002b006801800407b002001c130000000001001000c01981440400002ac00a002a0dc2d3003403c004025b0a007600207a800007a000002001802400000080809f0000000000000e007006801c00a01c04e839c000000085800801a0000040095b9000f000000400047700900100000150300000002022011800400001a33a80001dc00700b8048028000003800424a90255880f00085cb0190028000000004000800200a006016c00000007b807c002001021802806c015002800c00400a008800c00000b003000000600d000004002e0f50000000030691031803004e08a40900100f203201c000c00400e00001440e00370008008004005006802002c0000010000000000002000404c07e000018c01802700382186f010022e017800c00a002000004224e00400000860c2049284c00811c0053ce016c0000040094012029003001000a015002000000004a01181b009000e010800404002501400d002400f8bd005000400000f0000006000014001400205400001ac00c01603402d00700600058020008006000005c00000000d00b402e0000000b7c04800200e801000c00100f04fc0000a60000008020000005004401801b021800806200100500100d6000005000800c01f16f94e800536d02601c00000e000f804c0420090094cc00080000018240002048000000000003302604f8002359004000400201500cfd70d95202ffb830d913000eef60cc920015bc7494540004fd71d89500a67c65595200067c71d9520005dc7348610006dd65d8d2101e7c655512001cfe75d9120004fd7650b31024fc7058a5102efb609824139edf32d8d5202cfc71d9110006ef62cc95100eec62cc910005dc734865001e7c6594d10026df7358e1002ede3158e5109ebe64d91200075f6554d30005f4714811001cfc755922004edc630c5400a67f50d952004ebd325903008ebf4059310025ec7654920006ef6418931004fd7690d51006bf7458910016be6450c102ccff705952002cfc74d9710006be62d91310f7db40d8d40005dc735952102cfc7158a53004ff7458c10004ff755863002cfc7158e41005df7358142004fd7694530014fe7458e10004ff764
  | 42 => 0x1003800000204974d8000012019013002c00000506d80140480020090034000000000800803e00303200040ac027233000c01e0006218388054ccd0009df8008000000007400a95700000080020010008e2810800000700640020010000988002011003c0440564c7002000c01200100802500080021fd801000a00800b800401a00300a82c000000301c001c0f000005e0038014003006800424a0a9000005000406000000d402800400283200300fd030001000008d009004c0001d500000328b4005002813c0000d303d01b4036000000000800201903a804801800c0000018000219119802c13e00800c801005e000000067400e000001800801c000022800029a0000038000002000006043c0926c30038198030037014800020400005700002200e0000bb340180080000004182017012806006200300681f8040000071011820200102580180040c5000019c0b5035053800400000700080dc0e401600080a800c001121804000e01f000000c05e00203f000002200300300c400202500a802c00400000000500040f8000006c01e00000300400000270000268016001001806400c0c90190018066020019800000001c006807c02000000209f00240c00c0001802e00f00080a801c04300d001cdb4010005000039600409d003c00200900000340100010010180ffc00c021119000800e003000000002706d801400000b005812004c00c036003800609f01203f4016003003000c0000ae00700021c400301c825c08e00501c01140040090862da401202400100140063ba010804801a0150000078036000001000000c01a00080d025207e01c009404a0040048110b3207a0048385ada00000e800400c01e78800180bc01c0078004026001001800004002e00b00c0000010042056802a02e00300940e8024024000414800210608640160028f7001800400a0010010012014000805401e00001084154e000003303ac00a0010180080002165001801a74e00503d00a40000110a6007c000134011801c018000001006c00b512000830009af2e00000000160090f380a403400e003808c02400706c80500b20010100024056000002805000a00b000000400600a00087b806000c000000008800201580140300dc01136bc010009006803400000b00a800800246a005000802012d00000d4002002009001401000d091013c00c00200b000c05a01e0b4801001606e002800000004ca3e814005e00d0248158042003012802400200503700100fe00601380001e4002000800c06a01600f002c0a600103c000801228850680000040ae02600080080070090abc00c006037002800c0a3011833c018004000000c0120040030054012000303800402200500180e4000000000046c00400200080100000800218c5000002100600000ec0010f7015
  | 43 => 0xe80ca00082b3c4004001a005800409c0010b384b429e01300e800001000200e00140023f5004800403000400180a00523cd00702c4002000004801007a00002a000002a0a1001804001401e003809403c000000809c01c008000000011400200f80a40000c803b8010028000001000000400000681040088f00001174104042002808404e0250ba805800201c000121005000a03081e803a00b009802401603d02b80840f6000007803400e0940038034004000000012c0e800300a01bc034004000026c0ba00900001800000070d58014574000000800800401200a001800a00e0008014002055000000800803f00280900bc016005800001400a04c035449c01d0058040002006004800409a0db007806000201908d80c800c00d01380d0ad206800180d007000b067817400002900112fc4100d900282f000004d001810012600403001e003a00203681c801c0cf010001c02601401381380020060098018000018002800001a01800e001001e008002803800c00b85c001c01e03b003801c00a02202b808001c00201b800031a08a000000001601100000ac14800a003022d968011000800400400b000004c00a031000027c034000021805000600000e00000281bf025002c00a00000200000000000010130148000078c0080b63d0004020400001d003805006200e00700144ce01800000100020000000018022032029008c00e002000800000c1350330194000002000801000a10305b0028032007bab800574c00f008001c004012012801c0000a5006800c04c051008000000204300e802000c0110070048006001007801c43a00000715a000c00a0e2800000e01304a00189020000000000f6201401980a405209f001000000204800b001801429c009005000a0300020014022001003013400e0010058000000000006801911617004f0050018018001002409400d060002401258601a829803606805a811404601600101a80060240078038004000004847804606dd0c801c01a00600780940c000001b000003c07000d00040020010270000014001032006003800103121a826f7540000008032006003800469200b00f80040620132c780d8074005007801000000a02c1190034053000026405003f00f00040aa05b0bd225c00200b000003422c025009801000a04300580ec11c00000d802c0bc0121af005c02c00700e0078008000885800c00e19a01b80800d40135b280540e2005000000001c0080028010000000006809c0080000110310018019000412000003b002035c00a00205c005c032002014812c07a01400a800436a021001000c01003d0170070046061001032c10809701201d00180000028010032001001840801c0030128004016000005000002200572f80000960110000084156006003009800805000304f400000
  | 44 => 0x3023401e00001080a800e72b0000059e1a00000600c400a00000981a00e200300b001400000d004006400003205ca5a818800400b003000a034050000c0022d8000070c0f401900701b003a0b1001000c00200100e803000402e058000800200000980d4000007012005401e04e003001405400000380500b89ae000800400e000007018804c00000681a414ad6200c807400e004009003aa340480070000004041007800000200038780c800e0050f4000009e00000900e4006003000000009e02d0108000d0600800400a0052a9200a014002e07000000043c8014000814c00c0d20d99b0800000c00200000080030010008030042000022005400c006801800a000001000c000044000000812404a014806800200d03d8014022004001009800a019001800000000a00c804001e01b00380980480100018008004002002004c01a01b00681041b00000b780b801c00b002812800600100700040e878400281540880220008005b261310038000006000048801002c002000000001200b01200000a800403602880380020000078000007047007808801200f00040062bb001d42800000000802e000a0000258000026070000002405c01c004806002c00606200a800003e009801003001f00000a804882a00700a0000000001b4dc094aba002000002204d03d895080e005002034c01a0f4005002437e03d01c002428a03300780000b002b002003400200101d801800601203f801800a000000005800a08000000a000201830b00040e205b00204d821e008007002002405c00080bc0a2056000007c0020000008000022250002006400001600b802c00600100000700022df000000061e0310090238000021001005c01e04d002802c03a014006800000c00000d8008040000004808c0000170030004040039013806c006004025013c004001026804c00a0a100c000000a007007800c004000024015801a04800a816400600000000000020020100044080009003004402502e00480100007b601e054963002592300300000b0008002c00e0100e7002809e023000002001200100d80240ac01a0198000024c8a00634c0012018004803001a00500180bc0300000000208008016003007c09e10801a000400e00100000ec00251a0b0801001200000f000400800202680004ee12700604e020603900480fd15a03211f8150000009008803c0561dd04a006010c00b0008004192000092001c01c0020b6807c04400d0038008010003005000017a0060c08018000002066014c00003b3fe86a400600400700040d8002015892405200c00000a8018016065000000a17500a0008016010000000401200000480793be02478e016007c005000018c0040020290028000007000802001e01b0000054000000000003800000d00082340f202200c80
  | 45 => 0x400000180
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xdcb601cd21480015c902b9ac5180033a58b704ca3000656396c8b0a6000c7475dc5644800193ac9b9a43080023be097654f1000477c12eca9a2000aaf82597644c0018eeebb8ac8900032d1d37158d20006c63a0e690a40098de83dd165c400187aea3aec890802b960450d893101c3f42eec99220018ec825d93044001958e4322c098802ab612651893100717aa4a8b146000ace82dd7635010b59904288c690802ae20165191210065a3a0c290aa000cad64dc931840b7938c7ba462a000a2f21176947300045fc22eca982000ce4621c5434c413938e6b22421815f1b1c86518d200066db98e0b2a4200c3c74d9521440011bf0eb20c69098237e0d74d95300045ec3ea7b2242098be87d91434840b1790eb22a91891b1b1977254d2000637b2ee4a9a207bcce63dc9538800193ee9b9ac4880030f5d254d95100c64e320e6a024000c5d75d4f634840193ee831a42a000aa72116390c100043ec2eec98a4000ad9831436050c0517d0fba2ca9080e2fa1f64551210145e422eca982000aaf84597624c401cd0ca38242900263720d765491000476c16ecaa26200ceb72dc16550c091f100bb2a898802ab60870d912100477c12eca9a4035ccc72d8d3148401970c8382c8a980e1f215764c9100062fb2ee6b2240008bf845d9434840b9c8c2b94c2aa002aee0165d912102c3e43acaaa06200c5c651cd4048013938c6ba4a6a00030f1d3654c51000477c12e630aa865e4e53d4f624c40117f08bb284880032d1d371589100061eba8ebb226200ce8721c1654c4532d904bae63280063b20973d81544b65bb88c8b1a42008bf845c8614c00153b07328c8908033a18870585530145f43ee8b1820008df875946350001c38ca322a698003711cf61485202f5cc402a831a8085dc4211cd21040091df0eb1665080028fe1571592102f64f3b0c8a9a60028bc841d931500018eeca38ac6900021fa1c6558d100062fb28e6b222000cd473985219000517908b98c2a8002a760f54d91313064f3b6c720a8000c3f65dd13144001998e5b1ac2a000e1f215760c52000c77414eca9a2000a7485584614c0014e90ab08c2a011ab3a1b43d895300667bb0e498862048bc87591420c00195ee9b92ca980023be0973d81540045ec3cca3226200c6f65dc9504800199ce431ca2a00032719073591210043fc2aec9922065ace83d53624c40517908bb263100032b9cb649453142f62108c728a4200c6f751c9644400517908bb243280031bd977258d100045ec3ea7b226200e9b80550635000155f08b9ac518002b360b75d8d4000556412eab206000e375159251840131bd0fb9ac48800317d94735011000637ba8e4b2a60098dc835da53508091f100bb2a818002ab61070d895300575c02c8312a6008de87d8d604840199ec7b92c2a00032b5d16298251
  | 1 => 0xee638ac8990023ee1d60181211ee57316e890c8000a6e82dcf6544001878cbba260900023be097654e100066a318e2b1280048ec87589428c00195ae9b14c0989521fe1d619465000c77416e6b04a200c9d64dcd410c00153b063aec8908022fe1171d815204d4f436c6a1a8000c74751c563480051bd0fb1a8690802aba0850d91310045f43ec8b026200c9c435ce61900131b906bb28528803175d475d8d4017d674168231a42048dc8758d53840011df0eb28c49880327d9373581210065dba6e0b2a6200c5f75dcd64440131b906bb2a89014b8e94350d913002c7a40aeca106000c9f7518e41500bd9b0e031aa2a00023760e76485402de4e31ae720a8000acd82950634847b958e5b22a8908023be0973185501c477c32e399442008be87d91604840153b07b86c890982a761371d8d400065b326e2a9c2000a9d839c9640c001938e839ac48800327593735503002c6e43ac6a9c823d8bc86dd160484011ef02bb2a99900e1f21476545200056c41ac0302a85ec9e7618d43500b58d8edb2aa490002a7a0f545921000657396c928a6000cb964dc1540c00153b09b86c69086327990735031000666392c698c20028bc845cf654800517908bb44298002abe0965d91310056bc0aca31a80008f787584615400b5c902b1243280163d20576550300043fc2ae130e6400acc8259463500019c8e630a42900032b9d362181530045fc22eca8e6000ce4621c5624c10b998c439a43880126ea1f70551400061fbaec8b126000e1f54953634849d53908b1aa6080030fd97744c11000556412e2b206000c6c75dc9634800117b09bb2a49880317d9773589102347643aa7b126200e2f54953624c40195ec9b92a6908035a5c970946500145e422e53086000a9d83d53644c0018f2eba86c0a180237e0d765512000477c3aa6b102000e8c64d4863484014bf06ba6ca8800339cc87158d2000657316e898c6080c9c63dd5435000b1d9053b4a290002ab2117358a300247743ea4b102000c9e76192534c001938c839ac0908023760f76545400046ec3ea9b1a4200cac74d89604c40b1e902bb286900021fe157654d2017ce743ee690a40008ee87189604c4018b8ebb1ac0908263720d7694d410065c3a0e0b2a42028bc845d9329400153b063aec8988023be09739865000c76412e630aa000ad4835846150801958e9b12c2a98123e2017654810024dd406eb20a8000c9c74dcd62440070fd0bbb286880030f1d36558d200047743ec4b026200acf835d1628c00156908b08c2a994f1e9db65c41100061e3aee8b1a40028be84dcd658400193ee839ac48800a2f211764873000762398c290a4000c6f75d89604c4031ed0db8aa890802b360c50d89310145f43ee8b122000a9d84d48635001359906b12652880e1fa1776505202965bb24e3302862f
  | 2 => 0x87158d202de4e39ec8a0a6200c6e72d965144001d18c8392a698002a72116318d500145f426ec90a6000dc873dc12148001878ea322c098802abe11735881000c6e41aed9928060cdb631c16550c0195ee8392c8988030fdd754592100047dc3ac03026200cae645ca51840011bb0f328c6a00023de0576551200145e422ed28a60008ed86dc953040018b8cbb9a4288002ade05725903000566c16a231a4200cac74d896054c018becbb9aa0980163e219700c54001c6ec1ee8b28600387e85dd9424407b56b03baec8908031dd9471541100047bc0aecaa06000aac82597644c40195ec8b94a2988030f1d7645813101d3b436cb28a2000acd821436348401958c8b94a2988123e2017654d210054f418ebb224200acd83994624c40193ac839a430800327d0c7654d400061fbaceab242000ae880597624c40159906ba2c4080031edd875440100043fc2aed20a4000c6c65dc931440011df04bb2a6908031d1977150d1000477c12ebb0a60008ed829d95344001c58cbba242900023de0576551100065c3a6e0b2a60008fb8758060550011f70eb00c0a98022fe117298430006363aee4b1a2000ccc635ca515000117f0eb28c8908030f19774585200046fc1aeca14a05ba9c83592419405f99cc439a43080036610c70591530065bba0e2b1a4000aac825d5648400155d09b8ec4a9802abe117158a304cf52188c831262018ee87dc96550001878ea322c2980063ba0976946300074c402a831a8000c9d7418e604840b1e902bb4a6a10030f1d47458d200145e422ec90c6018e967118e41500031dd053b2a6a08123b20b76486300054fc1acbb224255e4e53d4d628c0018b8cbb9ac29000a2f21171d813200657ba2c49882000c3f751d1634400b1e902bb285280022fe1173d951000557c22ca3126200c6c72d95634400b1d90eb12852880317194735852004c6e41aeca14a000cac645ca514c00155904b8ac90817aa72015418d400064fb20e6b024200c3c65dd131480bd53100aa0c6a0233b10846354521005d340ea43224200c3c65dd1634413956f08b08c2a10d73398b73484100145e422e3b02a400c5f7518d625000117d0fb22c2980030f5d074d95200062e32ee6a0220008ee875893104001968c9b8aa6988032719073591200062e3a8c6b1280008ef875906254c0117d0fb22c69080339dc871595430061fb2ee8b122055ccc73589218c0011bd0e31ac2a000317d9473589100062e328e6b224000aaf825c564841378beebb9aca990039a19770485200062e3a8c6b024200cb474d8521540018deea312c098802b9e0564189310054ec20a231a8092ad781590634840156d02286c8908032b1c9644c6100054ec1cca32260018ec825d941940015d700b28c49880387d4d6494e100145f43ee8b2a6200acd80d4863484019a
  | 3 => 0xca9a400087f855db314800147f08b9eca880031b19772591103054ec20ebb1a805ea9e8055063500a5976c8382caa1802a7e0d71592100061e3aec8b0a6000cb474985318c0010ff0abb062900036610c7058d540043fc2aeca1a2000ab781594644c00155b09382c5288032b1d3624851000574402ca3126200c9c64dcd6448401968e838ac69000333dcc725911000477c12ec98c8000c3f75d51640c0010fb0bbb282900163d205765512000c7743ee4b2a6204cb870591540c0011df04bb2a998816b92057458a510063c328e0b2a62058de87d0d63c400187ecbba24288002ab20965191300145e422eca9a4000cb7741c56550c8d59b07ba6c4a9802ad60450d913100556422e6b14a2008df8758c63544bb53d0db24a698002b3e096518d4001c7b436e2992a200acd821c363484011df04bb283280023761c50d8d210f64e326e6a0260048f487585519000195ec8b94a298003931975218d210066639ac490c805787e87d95204407b95ce5b24a2908023de0576cc9500063c328e0b2a4200ce472185314c0b953f0eaa0c6a00031d1947150d100047dc3ac0302a200cd4731c5644805fc9d0ba90c6908032bdd0625815301c3e42aec9822000c7575d476150c011df04baec2a000339dc671d89530046fc3ac631aa800caf74dc963440011f700bb2a89900335d8f715894002e7330ae528860048dc8758d43040ab39906baa429000335dd9514c431006c7ba0e690a4000a9d8399764484011bf06bb2a488017399c562982510045fc22e630aa0098dc835d9540c0019b0c7b82a2a000327dd073591210045fc22e3b02a6008ed87990624c4010ff0abb2a890002aba1b521912100573c0aa8b102000cc4731852148001958e8b124208002a76135018d4000666316e6a0a62028be87dd1654c00b0fd0f292cb88002b9e0564189530070faa4a831a4200ab88059764484031d904bb2a7200163d20576508100247a43ac29086088c7b7019561480131b906bb48690802ab20965191310045fc22eca9a4200ccc73dc964484019aee7b8acaa0003331cf624855001c3f43eeab224000a9d83d53644840153b07b86c8988063b20973d81510145f426eca9a4200c3c74d9530480011bf0eb18c6a90bf339db52d8d2102c7a40aec994a2008de8718d6250001878e832ac2900022fe117648730006573a4c5304a200c7765dc56448001968c9b8ac4980023ba1b7254d3100672396e2b1a2000cf071dc16550c0195ae8314c09880a2f21172185302f64f380c720a80008ef825d943440011bf0eb18c6a0a67a9cc464189310061e3a6cab12209dc3f75dd16550801958e8b1262080272718d74cc9402e64e31aeaa1a80008bf845d931880011dd0fb12c2a98032b1d062581310065ba00e2b2a86008fb87580604c80199ee6392caa000339dc
  | 4 => 0x244001878ea322c4980030f1d3654c52000746320c518a6285cce7118e214840199ec7b92a6a0002a7a1265d8d2100477c12ecaa24000ce872dc16550c011ef02bb2a68819a2fa1b744c52100673b10e2b02a600a9d84d4463500b54db05b9eca900023be09739864004c6f41eecaa242008df835d942040018beea39ac88800e1f21576cc5200070e32aa831a805ca9c83591540c0031d904bb2a6880063b20b764c41000c7743ee4b2e6253c7870d955144031938e831aa2a00031b1d47258d1000636baea5b1286028be87dd1639440117d0fb22c4988032bdd1624c6304064e39eeab2060008ed82dd5618c001c6ea3b24a2988f72b98b74486300065a3a2c298c60008df835d95444001ad4e1394a32800237e1d6318d4000636390cab222000ce4721c56550c01878e832ac6880021fa1f65591102dd4f418a1b226200c5f7518d615000117d0fb22629823fa30846418d2100537416e1b2a2000c5f751cd624400117d0dba242980033958b714c8100046f430e690a80008ef8758a518c0dfcc8cb394a288003335cc7358a5100574402c8312a6058f4815da21540018beebb9ac4881af279c463905400054e422c631a40008df835d36548031938e831ca2a00123b60a7694d200056a40ac631a4000aaf825d564840031d904baec2a1802b36085018d2102e7238ac4a14a200acc835d1629440117f08bb4a29800a2fa1f7458d2101c6f43ec6a9a8400c6f65dc9534800153d09328c690803a3d90628c531006563a6e4b2a60049b8805d5435000117f08bb260880021fe1576549104776210e8231a4200e4c63197324800117b09b9acb880032719373485300064eb22e720860668bc87591218400199ee7b92c888003171d4735912004c6e41aed29a8000aae84997624c4131bd07ba2cb980029b60b73d95100066639ee4b12205bc9d8718e41500011db053b2a6a08031b1d562483100043fc2aed21a4000aad84d4d62040a5970e1b2286980033958b714ca510246e43ac6a9820048be87d516484001958e5b22a698002e9a0752d912100637396cb28a80008bd84dd9514c0018beca39a80900030fd97744c5200045fc22ec90860098de83dd951500011ef02bb265280122f21d64550100061eba4a9b2a40008ed8758a518c0011bf06bb2869094a2fe117650c1000c7743ee4b226200ab481594644c05f998e431a82908063b20976553310045ec24ec90aa000ce762dc56054c019a8e6b0a43200033318b735453100c76412ecaa26005ce47158942040bd1790cb9c82a00021fa1f65585200063bb2ee2a82200087e87d9564480011f700bb486a88023de1d61185400055ac26a3b0a8000c7875dc1634400317d0fb2284980063b20975d853017e67310e6908207bccf621cd61548018ecedb2ca28800353194734852000c76410e
  | 5 => 0x8002b52056318d420055bc0acbb2260028bc845cf654840117b0f328c898002b360b71d8d4000656326e498a4200c5f651cd644800196ec9b8ac498002ae61050d81430062e32ee6b222000c9e64dcd21840031d904bb2a888003271d3634c521456a6290e690ca000cb7641c5544840117b09bb2a6908023be0976504300043fc2aecaa22000cb7641c5434c40b1e902bb2a8990122fa1e42592100065a320e2b226400c74651c530440131b906bb4a690803391cb71595403046fc1aec18a8058c6c7619521480c15390caa6c6a000317dd4735912000636396caa9a20008de86dcd2150001968c838a6498803a61907054d300055a40acbb226000cb6641c5328400117d0e322c4980033c1c7705953000566c1ce0b14a200caf74589210400195cec320c49882637a0e764855000657ba0e4b1a20008ef87590624c40517d09b9acb88216b3a1b628c5310061fba8e8b122000cbb741c1654c40187ecbba260900031bdd472595400047dc3ac030284028bc845cf655000187eea322c0908032bdd072595300063cb2ee0aa66000a7985d036054c0117f08b8ec09900327dd8744c4310045fc22ed29a425a87c86dd56148001968c838ac8900032b1d162486300046fc3ac631a8400cad72d9251484598d8cab94a29000327dd3634c52100557424ca3126200ad48159463500131bd0faa0c6908f62f21f644c52100476c3cca312620087e87d95634403d938e9b1a42a000a2f2117654d210062fb2ee6b0a40008ef865ca518c001998e5b1a62880030f5d074d951017d67416a231a4200cac64dc9314c001968e9b8ac6908123b60a76cc5200047bc0aec99220018be87d91424c4831d90cb94a2988163d2057654c10006673a8c710a420087f855db324400b5c902b12420807b271d3634c54000747b26a431a4200adb8059763484018b8ebb1ac2a00023ba1c62581530063a328e2b22403daae821436448401958e9b92ca988028fe1173d9520006563a2c498c6000a9e8399464484015e302286c09880e2f6137655330006573b6c831262818ef8754f624c4031dd053b262a811ab360c70d8953006573a2c5304a2048f686dc543440131b906ba6ca90002b360f5458810006563a6e4b122087dc4211cd218400153f08b2ec6908030fdd464585300065a3a6e2b2a627b8ef825d952cc4011bd0fb1a42a0012ba20175588100045ec36e898c2009a9c835c5640c0018b8ca39a4288027271cd645033000566412c631a200087e871956348001d48e830a429000327ddb744c4310047dc02eca9a4200aad84dc76254c0b1b906bb662a0062a7a135218d400065bba6e2b2a6000cb7741c5654c0cb998c7b926290802a72055418d4004d4e424ec31a80008dd87140634840117b09bb2a4980031bd95729451004e4e3b0c6a1a8000c3f75dd16
  | 6 => 0x54fc22ca31a4200c9f64dcd214c0018e8ca38acaa017ba61035018d400063a3a8e2b224005ae6819c162944019aee7b8ac8900031ddd77158d203dd36c2ee1b12a600ccc635c2214840159b07320c4988022fa1c64589311673232ae528a205e8be86dcd54500010fb0bbb286900032b9d062181531ac6fc1aec9086000c77751c5644800b1dd0fa92c588002aba12641893100657ba6c4b0aa6008f7815d9544c83153d09900c6a000e2fa1f64551310055dc02cbb22626bc9c631c543500011ef02bb2a898003331c863585400066639ee4b2220048bc84dd9410c00187ecbba2c290002ab20965d91300061fba8c8b0262028be849d921540cb998c7b9262a000237a1c50d8d210064fb20e6a024000aad84d4d628c0f7998c7b92a6a10031b19772501200247c402ecaa242058f4815d954040091b90eb1aa710003351cf715954000573408a1b126200ab7815c9648400159b05baec6908033318f725854000556422c7314a200a9c8459763484011df04b9cc2080122f21d6450e2000567c1ae2b146000cae72d92604c41353906b92c81827f17dd7735954300c76412ed29a82008f7875846150c011bf06bb28528802b360b4118d210045e43ec890a6000ad68114363484015e302286c090812ae2017559030006563a0c4b0aa6008bd87143644c4091d90cbaa42900023be09765513204c6e41aecaa24253c7476d955144001c98cbb9a4290003b1a075218d2101c5f43ec8aa26400c9f7418d50500019cee5b8aca98002a761050d8d2100666398e4b2a8000cac741c9654c4011bf06bb2832800327dd3735912100c7743ee4b2a600387c855c0615085f998c439a428800333dcf725954000657ba0e4b2220008bd84dcd658400517d09bb2a4980032ddd071591320047bc0aeca9a40008bd86dd1210c0031dd053b262a00123721d6350e2000637baee4b1a200387c855db32440010ff0abb284880023ee0176551210061fb2ee8a9a8600e8d6410c6254c0b1d90eb1284188ca3b21b725813100556c20a1b1262008de87d53634840117d0fb2242980030fdd764581310145f424ec98aa000cb4641c5624c10359d0da18c4a982637a0f76485400061fb2ee8b1a2050a9c8458e530407b958e5b22a690802ab61352d894002e7238ac4a1062008bf845d9524400517d0fba2c398003271937354130436733b2e528a2003c7476dd55144001c3eca322a698243279d86418d212dd4f418ebb22623daac8259241441195ab03328c69080237e1d6318d1001c6f43ec6a9a4200c7475dc563440019d6e4382caa180a2fa1f7458e500064e3a6e6b1a20008bf845d932940070fd0bbb2629000317d94735852000656396c8a9a6209ccc635ca53484bd938ec322a6980272718d74cc5400054ec20ebb1a4200cae64dc931840010fb0bbb2868
  | 7 => 0x7b76dd51004001958e8312c0a98023be09765513000c7743ee4b222000a9e8399764484c1cb4a1a86c6a0182e620154d8d4000656396c898a6000acd83d53624c45f59d052a0c690a26b6e016518d403dd67c12c631aa400ce472dc564440014df0ab82c5288122fe1d649051000476c3cc8312a600aad84d496290401c6ea3b24a29080e37a1f6354d40006573a6c53026200c9e74d8e604840195ce4b24a2180029b61770d89313dd36c28e3b12a600ae581994624c4018b8ea39ac48800a2f211760c5200046fc1ae9b2a4200acc8258c63504018b8ebb9ac4880132e181749815100537c2ae6b14600387c855da414800117f08bb2a68800a2fa1376549310047dc3ac03028200cce72d8e51500019cee5b8acaa19ae2f21d644c61000c76410ec98a40008bf845da214c0011bb07bb2a8908023b60a7654d4002d7240aa8b102000a9d84997634841393ce6b248218042b9a1c614852000c76412eca9820018ec825d953c4001cc8ca30a4290062a7a105118d4000566c1ea8b1460048dc835d921cc001d4ee830a429000327dd37358d2100477c12eca122000c6c655c831480031d904bb2a818003275907350310006363a8e4b222000c9e641cd21840011ef0eb08c2900022fe117650d200043f436ea9022005c7471595540c40153b073aac81800e1f215768c5200045ec3cca3224200c5f65dcd404400b3cd03b92a69080e1f21570987322fd4f418ebb226000aad82994644c4019c86438ac6900038bd9752d91210064fba6c6b024200aad84d4f624c4031d904bb2878802637a1f73591214a74610ec831a4200caf74dc963484f7998c7b92a6908031d1977158d200054ec26a7b1a4200a9d83143644c401958e9b92c688016b9a075258b100043f43ecab1220008bf845d9544c4019e6e3b82caa180a2f2117654d100045fc3aca3226046ccc76dc9534c0019aee638acaa0002b920564d89530145f424ec90a6000c9c649ce604840153b09386c6908030f1d764589300046ec3cc831a4200a9d84c8063500b54db0438eca900122f2197550d400056741ce0b14a287cd77118d604840153d08286c6908021fe15764c1100045ec26e2b066400acf82550634851bc98a4280c6908031b1d772591100063a328e2b2a6000c3f75d9160484131b906bb4a2a00022fe1176947300247c402ecaa26400d4f651cd21480131b906ba6ca9800e1fa1f755891001c3f43eeab1a4000c3c75191604840b5c902ba2c4080032b5937254e100054e41ae2b242000aad82997644c4015b700b28c690802aba1050d89310045f438c8b026200ab58114364484011df04bb2a8180032b9c864981312f64f3b0c720a8000ce7721c5654c013938c6ba062a00030f1d365585200054ec26a7b1a8000c3d75d53644c401998e6392c8880022f612764c5500
  | 8 => 0x8280c6908023760f745971000567c1ae8b1020008bd87d4d64840010fb0bbb264880031b9cb65945300145f426e2b066400c77651c564480018d8cbb92c688002ab2117158a302bd37436cb99240008fb805d9544c4131b906bb28328002bc20161185530046fc3ac631a42008f7815d9434840196ac838a8508003395c9619443029eb9ba8e0a8a2000c7875dc162440019cce630a4290002b320965d8d400062eba8ebb1a4200ccc73dc965500011df04bb2a8880063b2097654e410053742ce2b146029c6c72d9550480091f100bb486a880339dc871591200065cba6c1302a2008bf845d932440051dd0fb1284988063ba0b75586300245f436e918a8000c3c751d1624400117d0fa9ec8988032dd9071589300054ec20a431a800987e87d95534400157100b2ec8988033c1c470595430062e328e6a022018c9c7418d50500019aee638ac690002b5e055418d210054f420ebb1a4200c3c65dd1314403153d09a88c6a0002ab60850d9131006573a0c53026200c3c75dd163440011bf06bb28690002ab2116358a510055a40ae4b2060048ec87589528400195ec9b926298027351ce614843000637baceab146000ad983143604c4bf938e7b224298002aee01651913100536c16e1b2a2000cb4641c56454c0117b0e286c89097f8794f53d91300064eba6c731a4200caf64dc931484018deea392c6880022fe1176486500051e42ae2b242000a9e83dc3644840b1e902bb2a81894b271db6454d300063632ee498a4035cce72d8e51484031dd053b2a6a0002a76105018d210053c42ac03024205ce4615ca615400517908bb26088002ab60a65191210062fb2ee6a8a6200cad74d886054c131b906bb2432800a1fa1f65551200066a39ee2b224200c9d731cd648405f59904aa0c6908122f21d6450e100064fba0e6b2240058f4815d9320400193ee9b1a42a00263720c76485300047dc02ecaa26000c3f75d91614c0015ad02280c69080e3ba1f62549312de4e31ee898a428fe8f2019063484011bf06bb243200023de1d61185420062e32ee6a0240008fb805d953440011bf0eb28c6908bf3398873486400066631ee4a8a4200e4c651cd21480130fd0fb2aa6900023721f634854000c76412ecaa26285ace81d4863484018d8cab9482900022fa1c6458d210062fb2ee690a2000e1f65550635000195ee8b124318002b620165d8d21006363aee4b2240008be87d91624c001878ebba2c48824ea7a126418d2100575c02c9b12a600c9c74d8d604840147908b9eca900031bd97724c5100061ebaea9b224258c6e7619732480091dd0db9286900063b209765521004c6e41aed10a80068ec875893104001958e9b1242a8002a7a0c50d91210055a40aeab206000cae62dd131040019cee5b8acaa017b27dcc7458e5000673b90e2b226400c
  | 9 => 0x76552100062e32ee6b122000c9c645ce604840917d0dbac82a0002b62016518d210064eb26e6a106000c7465dc540440018beca39a42880063b209731855400c76412ed98aa018e1f85550635001353906b2287280023760e764855000657392c928c20098dc835d954440019a8e630a42a8202a7e155418d400063dba8e0b2a6209a9e839c5640c001938e831ac090a16b3a1b638852114e36396caa9a4000cad645ca510c00193ec939cc0908031b1cb65591100066db98e0b2a86048f8805d953040019c8c438ac0a98029e60264195100247a43ac2a886000cb4431c56550c011df04bb2a72000f1e9d865c411004d4e41ac8a1c2000c3c65dd163480010ff0abb48688003395c47158a3000667b1ae528a80008be8714364484091790eb22a908002aba1353588100245e43ac8aa46035cce62dcd218c001976e8382caa1803395cb619855047f4a108c831a4200ccc73589219407b958e5b22629095f1b1d662582510047bc0aeca10602fcce621cd219400117f0eb28c89880327dd073595210062fbaec6b128000a9c8459463484014f10ab00c09880e2fa1f6455130006563a0e4b1a2000c77751c5655000155d0c320c498802a760f545921000746320c710a42028bc84dd9210c0011bf0eb18c6900163d20576553322f64fba0e6b24a000cce651cd214800187eebba2c6900163d20576552200054f41ceab242000ce462dc56054c01b88e630a42900163d20576cc9500046fc1aeca1a2009cd4639c653484010fd0e32ac88800237e1d6318d500145f43ee8b1a4000c6f65dc9644408d8dccbb92a71080335d8c71589402d6363b6ca90a4000ad48358461480031d904bb28218002ad21161185200061e3aec8b024200a7581988654400153b09328c690802a7e116318d2119476c36e49882000cd873dc165484015b100b18c6aa0bf331c863545210046fc1aed28a8005ce6615ca51900010fd0e32ac8900123d21d61546200055c402ca3226200c6c655ca31480014bb07b2ca6880023de057650a5004e4e31ae931a42028fa86dc1515000117d0e322c2980123d21d614864000636396ca98a20018ec825ce6190001998e6b1243080a71b9cb659452000c3e43acaa9662008be87d4d648408d1df0ea9ac5180123b20b764c81004d4f41ce4b206000cac62dd1624c40117f08bb062900163d2057654d2001c7b436e2a12a2098dc835d942440030fd0fb2aa4880033ad88705855300c7a432e329a4200c5c75dcd644400155908b2ec49880317194735911017e67b00e690a4000c9c74dcd634800917f0eb2487080063b209764c6500064e3a6c698220028bc845d9320400193886b98c2aa0063b20973986500065a3a0e2b2a6046c6c65dc9534409d53b0db9aa921802a760e621913000672396e2b2a86018ec825d9538400153d
  | 10 => 0xb1a2000ceb62dc16154cc1b36e638286a00123b21d6254a400247a40aeca1e2000ce472d85314c00517908bb4a6908161f21d65552212dd4e41ac920a2000ce472dc5644c401c3ea7b24a690a17b10844118d210074a31ec320a80028bc845c76054c011df0fb14a2988022f613764853000637baea4b146000c3f65dd1505001353d073aac81800a3ba1b7254d420065c326e0a9a600387c855da43480018bae639eca9000237e0d72185400062e32ee6b224000bc681d486348401c9ecba96c6908030f197745891002c77436e4aa24200c9f7418d515005f59905a80c6908023b60b735825100c6f43ec6992800587c875955388401958c9b92a6980032e59370506100045fc22ec98ca000aae849c162944015c904b08c2980beb3a175218d210064e3a0e6b2a4218a9e84148635000117d0eb2242180030f5d754d913000657322e528860008f7815da53508019a8e638acaa00022fe1173185200064fba0e6b222000ad78159763500031d904baec2a00031b5977254e210047bc3ac230a6000ce8721c16550c091df0eb16640800a2f211764c91004c6e41ae9b2a20008de87d8d615000195ee9b92ca9880333dcd62484100245e43ac8aa4405ba9c83592410c001998e7b92ca9094a2fa1f53d913000672b92c328c8000c9c74d8d314400187eea3a2c6900036510c715915304c6f43ee6b2a42098de87140634840b9c8e2b1241880031b1d762581311ad67410a1b1a4200ccd72d8e514840193ec839a8088246a7a186418d2100567c1ae8b14a200c5c651cd624400117d0e286c898802ade0575590300143f43ecaaa220008ef825d76150c01958e8392ca9816e2fa1d644c6100064fba0c6b0242048f487585518c0014bf06ba6ca900023de1d611853200672390e2b2a8000ccc72d8d5350001998c439ac4a0802a760c50d91212df0f29ea7b22622987c87d9520440090f90eb2aa6080032e593705443000656326e4b0a6005ae681d49620c4091bd0f192c708002b920961185400065bba4c290c80008dd87d50634840193ce831cc0908032d1d3715953000557420e1b12a600c7865dc131440011db0e286c4988023de05765522000637b2ae528a400387c855d943480bd938e031c82a00a65be1d72946500054f426e1b1a4200aaf845cd629440153906b28c8908023de1d61185540061e32ee89822000c5c75d8d62500018daebb1664a88273318d72cc52104d4e41aeab20602fcce7218e514840bccca3a8ac4080023b61b724c63002c7a40aecaa442028bc841d9214c0071bd0fb1aa6a091a9ba1762ccb1000c7b43ec290aa000aac84594624c4018eeea38ac6900033518f715894000c76416eca982000c6d75d4b624c401878e9b2ac6880022fe1176486300063632ee49824000a9d839d56484009970e0b22a2180023be09
  | 11 => 0x4c80195cc9b92a7080032bd9372581312d6373b6cb992406b8be87d9131484019cee438acaa0217331d463885210065b218e2b2a8600cac64dc9534c4011ef0eb08c2a98beb3a085018d212e64e31ee6aa28000cad645ca518400155d0532ec8988032bdd0625855300556c10a1b224200ce4621c562500018b8ea31ac2a000317d9773501200056ac08a1b1a42018ec825cf605040195ae9314c12895f1b9c865185204ae4f3b6c831a42018ec825d943440091790eb228608003a518c619054000656326e4b02620087f855c0614c8011df04bb28788002b32096318d510145e422eca9220018ec825ce61040019c8e438aca9816f2718f744c54000477c12ecaa26200acd83d49628c40195ee9b12c0988263720d74d952101c3e42aeca1a2000ae7815cd628c00117f08b9eca908f72b1cb64505210056ac1ea3b0a6000cd473dc56448001976e9b82ca90803a61937054d300064fba0e6b2a8000ae7815936254c018d8e5b2aa6980031b1d4625813142e67b10e690e2085ec67118e21484011f70eb00c0a900393d4e53588100065bba0e2b224000ce572d866155001938e9b9ac6908033318873589511ec5f43ac890c20008bd86dd121840010ff0ab80c2a10023761e6518d212de4e39ce2b2060058bf8759243c40f7998c7b92a6a00032bd937254d3100477c12eca9c82008ef825db3154001970e9b82ca988022fa1c645812100746326e4a9a6000c7865dc121440131b906bb243200261f21d65553301ed5ac08e1b224200c6c65dc9434810b39f0eb1e65108163d205764ca500055a422c230a64008df835d9424407b95cc5ba24208002b920961185430046fc1aecaa24200ce562dc5429450b998c239a42900031b5d562cca500045ec24ec90a6000ae982143604840155f04b8ac8180032b1d37258d210061e3a0cab122052a9d831d7644c009970e0b22a30800e1f21576509100145f426eca8a60028bc841d9414c0019cac5b8a840800399d94614852017d674108031a426b8bf865c64390401938e9b1a60900023be097694d410061fb2ee8a8a8200c5f65dcd6444131b88e4a8a62188023b60a764c5400063dba8e0b2a4200acf8259763500019d6e5b82ca98802b3a0f54588100054ec1cca3226200aaf82594644c51fd18a4320c690802bae0165d89310062fbaec6b024200a5c835d3654800178d03a96c690803351cf61485500063bb2ee2b1a4000a9e83d53644840117b0fa9ec898002abe116398a510055bc0aeab2420008f7815d9424406b998e5b1aa6908063ba1f72595430066631ee4a0a42048dc8758d5390001898ca39a4290182b6e0d60181430061e3a0cab1a4000c74651c563480018e8ca38a808800a2f21176484304bd5ac0cca3224200ccc651cd214811fd2e42320c690a53a3c836418d2100636390ca
  | 12 => 0x31d1d771591100064eb26e69086094e8c52d9063484015a902b2ec6a0003391cb71595300066c39ee0b2a80008df835d921940011df04bb28690a038710f6554d4301c3f43eeab222000caf64dc9534c031938e831a42a00122f2137650a102363632aeb99240008dd83dd9525000155f04baac818003275d363981210045fc22ec9902000a9c8458c634400155f08b1ac52891b1b1977254d320065cb26e0a8c20008bf845d953480010ff0abb28690003361cc70595210062fba8c6b0242008ed86dc9538c00153906b2ec8908033cdc4705953100556422e6b1020098dc835c861500cb59d06286c4988031d1d77158d2000566c108031a4200c3d751d7644c0010fd0fb2ac6900163d2057650a512f45f436e898a60098de87dcd644400153d09a9ec6908023ba1c62585530057840ac0302a65fc9c73d91404c0099b0e0b1aa60800395d4763945210063632ae39924000caf74dc9644c401c5ea92a2c4080032e1d370595210064fb22e730242048ee86dc95348001958c9b92c8988030fdd6755903000763b98c290a4000ce862dc16154c3d53d083aec6a00032e1d070595310057240ac8312a64d8ec86dc96054c0b5c902b9ac4080032d9907154e1000567416e3b1a8000aae84d4f624c43153d09a80c6a00023be097654c100061e3a8e8b1a20008ef825d9304400156d02286c8988032b1c86458530006e4390e0a9a605aa7b85580605480117f08b9eca9000399d4762945310056a40aa831a424ea9e86d91534c0018b8ebb9ac8900123ba1f42588100046fc1aed10a80008f7815d9544c401cc8cbb0a42900032b1c96454e100052e41ae9b2a2000ccc73589210400199ee6392c6880263720d765081001c3f42eeca1a4000e4f65d8f324800155d05328c89882637a0e764854000657ba6c4b02a600ce872dc1654c4b5ad6ea382a490183271db6350d400054f424e1b1a42098dc831d9315000517908b9eca880031d197714c1100061fbaee8b1a2000cd7731c564480d7938e638ac81816e2f21b74581310047dc02eca9220008ed829d931540019b6e7b82ca9080237a1f6358940004da40aeaa1a80008de8718d21500014dd0bb86c498803175d753d8d4000637b2ee498a40008ee87143624c401998c439ac4880021fe15768c5200043f438cab1220048ec87589520400117f08bb26528816b9205624863002c7a40aeca106200c5c751cd644400199ae431ca290802aba135358a300065ab20e2aa420098de83dd9525011796ee2322c090803a3d90638852102e7338cc5304a2008ec87589318c00117f08bb2a890803331c96354e1000477c12e7b02a200c9c74dcd654c0011ef02bb2869000a2f21173185200145e422ec98ca000cad741886054c01968c838aa6988032bdd072595310061e32ee890a200387c855c061
  | 13 => 0xc5ec3ec320a80008df835d9544c00147908b9eca880123b21d6254a3002e5a38ac8a1c62008ef825d9319400153b09908c6a00063ba0b765513104c6f43ee6b2240048ec8758932040015ab02280c6908031bdd772591100054fc1aca3224200ce962dc15204001976e8382ca90a8333dcc625855323566c1ee3b12a6008de8718d60484014db0b38ac5182063b21d5358a3000667b98e4b226200c9e64dcd210c00517908bb265288022f612764c52000666396c698a8000ac681d4863484091f100bb2a320027271cd645083042ce743ee49886200c9c7458d30c400117d0fa9ec89081739185720c5202945e436e8b0a6000cb464dc5324c401998e5b1aa6a0957331cd6250a300047643aa6b102009cd8635c253500598d8cab94a288156b3a0f5458a3000556c24cbb126200c5d731cf6544001958c8b94c0988033918871589434f672b96c330aa40387c855da434401353d07aa2c8180023ba1f62581530065b326e29942000ab8845806054c010fd0e32ac29000237e0d74d95100047bc3ac230aa4028be849d9314800b5c902b9ac528a6ab5e0d611853200762c0ea431a4200ceb721c1654c40199eedb9262188032bdd0625813100656396c8b026200abb8059464484011f70eb00c0a180327190735911004c6e438c690a80008df835d932440598d8cbbaa429000363dd0724c4310243e43acaa9060098f8865c253500010fb0bbb284880031b9c965947300247b436e29022000c3f65dd1634800b1e902bb2a898003279d36398d210053642ae6b146018c9c641cd4044001958c9b92a6908123b21d625483000673b10e29926200caf64dc9614c0071dd0fb12a4a08163ba1b7254d210064eba8c720a8029c6c72d95314800196ee9b8ac69015e9ba1b65485200c54f4264231a8000aad82dd7644840155f04b28c898027331cd624843040e663b0e4a9a6000c9f74dcd65484018e8cbb8ac89000317dd773591200052ec1ecb29a4000a9c8458c63484091790eb22a8180032719373581210045e43ac890860058ec865ca534840b9cd0e30a42900063b209764c64000716328e890a40008dd83dd921500bd5390caa0c6a000327190735915000574402c9b12a600c9c74dcd654840199cc5b9a83180032bd91729813102e6b28eec9886200c77751c5654c0651db0fb14a298802b360f52d89300247643ac4a10202fccc621cd21540019cae4b0ca31000333d8f724c54000477c12e7b028200cf3711c16550c0117f08bb2a8980031b5d475d89310245e43ac8a1420048be87d51640c0019a8e7b8ac48800333dcc72595310145e422eca8e6009ace83d49620c405179083b242a00030f1d3654c1102e64e39aeab20600487c875955404001b18e8392621880237e0d7654d210061fba8c8b126000ccc73d8921440018beebb1ac2a0
  | 14 => 0x8cc0140980300201c890060b417c0e0110b6890201ef02e18802810002004020080d975c06143006014014f600ae381808c05a0340180e0040980800000c0000180d00c200158040000d80281400e038010040140304390002601007001000088040000340780d80d022018470060120a0000010040140000b29c0d000000000290160020163640283c02e0382624e07a040518603660480280f0000182183601200000004008078148060020042aaf00102c807030032038200130100001f8210020000004c00001c00010006008270040160040a8010b40b072824a1e001e201608a11406001010008000180220089b0091440005292100000c08852002094088ec0aa03c0000904204c018530c40481c8311ac2e03001601e0c84b00083400002801134004b781b0020a00000f00a00c7b80104606c008170c60082f8311500340080e264124548090f806c8e8020e80080080015015c0580000a0080080900002c048670742740180907a000008000080500e0e0000040238090082280000002a14007003232048000850a8120070020766c8508000da00445802056004228010c6020038720002bc008090020000000303a3d80b0060ee02c050130540ac150021041980c80608001c010000120540282b0b80009709e026104020090040002b00000414c6b00a0401146f8020bc00c2400400a0dc080000004080383301e000008000007000301b05801c0200005e0040201012e02c9284e0000006400300406c010000ec0100084000e0acd70930240dc0a8360001680f8170b0000000ff002064018fc004118070060001900000206024c25a2103e0600e0050105d4220e2006020000202b60e80080006a234010690000281a8010281981a0090040a01082800200c2901501003c0080600800c00001000004bb869000c8c028030b801c0c00100000c9182308c00c0009501e0001b82310a684040c91140140500200623c0d8080040ac00001000088000080121782200326e28c0800e0040780e0fd1ae000028c8094054003c30741400200502204000010014040008340060100001f148081488051340540100000a0000300000e0343d80000a008040003880240780d00e015fe00e08009813103053630130050da00418816000034088070040f80c0220001c00b8150080050100e00002c128080080140000401c434448000040103c80200c060078010e626c0b80006e078038130976903180005
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x100020006000820300080042000827000100010b4c693dc671d895300721086641cd218400168890590431895342d3124d711c5628c00184c5261c5018d21006251cc815d5640c001c47651cc614852000722190721c1534c10b2c49160a5418d2150d13a56651cd2148001c44651cc61485200071219473dc12148001c0c65dd073485202f526a437518e415010b4c6919947348520006a1d9281d48634840168491590431895300703194741cd214810b2c4916084018d2100721dd073185214810b4c4915c8639452142e31204735892104001a8464a075218d212f4a6a63805506350001c84741cc61485200062518c815d5435010b8c4811cd624865042d31245731cd6294401c44651cf6148520
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x2
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
  | 19 => 0x98d
  | 20 => 0x98e
  | 21 => 0x128d
  | 22 => 0x128e
  | 23 => 0xcb
  | 24 => 0xcd
  | 25 => 0xce
  | 26 => 0x9cb
  | 27 => 0x9cd
  | 28 => 0x9ce
  | 29 => 0x12cb
  | 30 => 0x12cd
  | 31 => 0x12ce
  | 32 => 0x168b
  | 33 => 0x168d
  | 34 => 0x168e
  | 35 => 0xa0b
  | 36 => 0xa0e
  | 37 => 0x130b
  | 38 => 0x130e
  | 39 => 0xa4b
  | 40 => 0xa4d
  | 41 => 0x134b
  | 42 => 0x134d
  | 43 => 0xb0d
  | 44 => 0xb0e
  | 45 => 0x140d
  | 46 => 0x140e
  | 47 => 0x24b
  | 48 => 0x24d
  | 49 => 0x24e
  | 50 => 0xb4b
  | 51 => 0xb4d
  | 52 => 0xb4e
  | 53 => 0x144b
  | 54 => 0x144d
  | 55 => 0x144e
  | 56 => 0x16cb
  | 57 => 0x16cd
  | 58 => 0x16ce
  | 59 => 0xb8b
  | 60 => 0xb8e
  | 61 => 0x148b
  | 62 => 0x148e
  | 63 => 0xbcb
  | 64 => 0xbcd
  | 65 => 0x14cb
  | 66 => 0x14cd
  | 67 => 0xccd
  | 68 => 0xcce
  | 69 => 0x170d
  | 70 => 0x170e
  | 71 => 0xd0e
  | 72 => 0xd4d
  | 73 => 0xe8b
  | 74 => 0xe8e
  | 75 => 0x178b
  | 76 => 0x178e
  | 77 => 0xecb
  | 78 => 0xecd
  | 79 => 0x17cb
  | 80 => 0x17cd
  | 81 => 0x104b
  | 82 => 0x1789
  | 83 => 0x14c9
  | 84 => 0x2c9
  | 85 => 0x98c
  | 86 => 0x180b
  | 87 => 0x14b
  | 88 => 0x449
  | 89 => 0x198b
  | 90 => 0x1649
  | 91 => 0x148c
  | 92 => 0x104c
  | 93 => 0x10c
  | 94 => 0x589
  | 95 => 0x130c
  | 96 => 0x18c9
  | 97 => 0x150d
  | 98 => 0x198d
  | 99 => 0x150e
  | 100 => 0x180e
  | 101 => 0x140c
  | 102 => 0x28b
  | 103 => 0x2cb
  | 104 => 0x184b
  | 105 => 0x19cb
  | 106 => 0x20c
  | 107 => 0x28c
  | 108 => 0x2cd
  | 109 => 0x154d
  | 110 => 0x19cd
  | 111 => 0x154e
  | 112 => 0x184e
  | 113 => 0x150c
  | 114 => 0x18cb
  | 115 => 0x1a4b
  | 116 => 0x20d
  | 117 => 0x15cd
  | 118 => 0x1a8b
  | 119 => 0x194b
  | 120 => 0x1a0d
  | 121 => 0x164d
  | 122 => 0x20e
  | 123 => 0x1a0c
  | 124 => 0x15ce
  | 125 => 0x188e
  | 126 => 0x160e
  | 127 => 0x1a4d
  | 128 => 0x194c
  | 129 => 0x3ce
  | 130 => 0x44c
  | 131 => 0x18ce
  | 132 => 0x28e
  | 133 => 0x3ca
  | 134 => 0xb1256
  | 135 => 0x25253
  | 136 => 0x15393
  | 137 => 0xd995
  | 138 => 0x25353
  | 139 => 0x29253
  | 140 => 0x24bd3
  | 141 => 0x14253
  | 142 => 0x184253
  | 143 => 0x28253
  | 144 => 0x29453
  | 145 => 0x25493
  | 146 => 0x25853
  | 147 => 0x24293
  | 148 => 0x148253
  | 149 => 0x149453
  | 150 => 0x296d3
  | 151 => 0x28bd3
  | 152 => 0xbc253
  | 153 => 0x28214
  | 154 => 0x25453
  | 155 => 0x1a57d3
  | 156 => 0x29493
  | 157 => 0x1a9953
  | 158 => 0x154b16
  | 159 => 0x1a57d5
  | 160 => 0x3d456
  | 161 => 0x24153
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2620
  | 6 => 7045
  | 5 => 1944
  | 4 => 29
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/34+packedAt gbK8 (1560+(h % 34)*6) 6) % 60)
  | 7 => 2*((h/908+packedAt gbK7 (96940+(h % 908)*12) 12) % 2620)
  | 6 => 2*((h/2348+packedAt gbK6 (338160+(h % 2348)*13) 13) % 7045)
  | 5 => 2*((h/648+packedAt gbK5 (114696+(h % 648)*11) 11) % 1944)
  | 4 => 2*((h/30+packedAt gbK4 (2030+(h % 30)*5) 5) % 29)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffc0fc00fc01ffffffffc0c7c7c7e623fff
  | 1 => 0x3f007ff0000ffffffffe01fc7393a79983ffc7
  | 2 => 0xc0007ffffff0001f807ffe0383e3c7e1fc38f8
  | 3 => 0x7fffffffffe0007ffffffc03f801ffc0ff
  | 4 => 0x7fffffffffffff800003fffc0001ffff00
  | 5 => 0xffff80000000000000000003fffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x450f5402c502c405aa96ca9404240c2a621b5b
  | 1 => 0x36112cb002455aaad32a29583191a59980edc5
  | 2 => 0x84223d555b5002931a4d6c5182e2c6e1ac38e8
  | 3 => 0x10444a69ac69acc02071b1e2dc03f800d740b6
  | 4 => 0x2088738e378e371c7c00c0836ffc00017bb600
  | 5 => 0x38f000003800380040010103fb5b7354000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeaeafc88a800feeaeaeafc88a800feeaeaeafc88a800feeaeaeafc88a800feeaeaeafc88a800feeaeaeafc88a800feeaeaeafc88a800feeaeaeafc88a800, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40972
namespace PEqualNP.Outside.L_meta_40972
open PEqualNP.Outside.L_meta_40972.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 9 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 9 := bs0_4_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
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
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 117 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 46 := bs2_5_0
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
theorem bs4_3_0 : Interval s4Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 8 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 92 := block_range (n:=92) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 92 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := bs4_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 91 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := bs5_5_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 29 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1944 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 bgb_5_576) (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)))) (concat (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 (concat bgb_5_1248 bgb_5_1344))) (concat (concat bgb_5_1440 (concat bgb_5_1536 bgb_5_1632)) (concat bgb_5_1728 (concat bgb_5_1824 bgb_5_1920)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7008 : Interval gbAtlas 6 7008 37 := block_range (n:=37) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7045 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)))) (concat (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152)) (concat (concat bgb_6_1248 bgb_6_1344) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632))))) (concat (concat (concat (concat bgb_6_1728 bgb_6_1824) (concat bgb_6_1920 bgb_6_2016)) (concat (concat bgb_6_2112 bgb_6_2208) (concat bgb_6_2304 (concat bgb_6_2400 bgb_6_2496)))) (concat (concat (concat bgb_6_2592 bgb_6_2688) (concat bgb_6_2784 (concat bgb_6_2880 bgb_6_2976))) (concat (concat bgb_6_3072 bgb_6_3168) (concat bgb_6_3264 (concat bgb_6_3360 bgb_6_3456)))))) (concat (concat (concat (concat (concat bgb_6_3552 bgb_6_3648) (concat bgb_6_3744 bgb_6_3840)) (concat (concat bgb_6_3936 bgb_6_4032) (concat bgb_6_4128 (concat bgb_6_4224 bgb_6_4320)))) (concat (concat (concat bgb_6_4416 bgb_6_4512) (concat bgb_6_4608 bgb_6_4704)) (concat (concat bgb_6_4800 bgb_6_4896) (concat bgb_6_4992 (concat bgb_6_5088 bgb_6_5184))))) (concat (concat (concat (concat bgb_6_5280 bgb_6_5376) (concat bgb_6_5472 bgb_6_5568)) (concat (concat bgb_6_5664 bgb_6_5760) (concat bgb_6_5856 (concat bgb_6_5952 bgb_6_6048)))) (concat (concat (concat bgb_6_6144 bgb_6_6240) (concat bgb_6_6336 (concat bgb_6_6432 bgb_6_6528))) (concat (concat bgb_6_6624 bgb_6_6720) (concat bgb_6_6816 (concat bgb_6_6912 bgb_6_7008)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2400 : Interval gbAtlas 7 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2496 : Interval gbAtlas 7 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2592 : Interval gbAtlas 7 2592 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2620 := (concat (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat (concat bgb_7_288 bgb_7_384) (concat bgb_7_480 bgb_7_576))) (concat (concat bgb_7_672 (concat bgb_7_768 bgb_7_864)) (concat (concat bgb_7_960 bgb_7_1056) (concat bgb_7_1152 bgb_7_1248)))) (concat (concat (concat bgb_7_1344 (concat bgb_7_1440 bgb_7_1536)) (concat (concat bgb_7_1632 bgb_7_1728) (concat bgb_7_1824 bgb_7_1920))) (concat (concat bgb_7_2016 (concat bgb_7_2112 bgb_7_2208)) (concat (concat bgb_7_2304 bgb_7_2400) (concat bgb_7_2496 bgb_7_2592)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := bgb_8_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 24, 26),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 34, 38),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeaeafc88a800feeaeaeafc88a800feeaeaeafc88a800feeaeaeafc88a800feeaeaeafc88a800feeaeaeafc88a800feeaeaeafc88a800feeaeaeafc88a800
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808426 * 2 ^ 32 + 4236814336) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40972.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,4]⟩,⟨.or,[0,4]⟩,⟨.and,[2,5]⟩,⟨.or,[6,8]⟩,⟨.and,[0,5]⟩,⟨.and,[1,9]⟩,⟨.or,[1,2]⟩,⟨.and,[7,12]⟩,⟨.and,[3,13]⟩,⟨.or,[11,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4236814336) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4236814336) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40972

open PEqualNP.Outside.L_meta_40972 in
theorem PEqualNP.Outside.L_meta_40972 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4236814336) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4236814336) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
