import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40539.Model
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


end PEqualNP.Outside.L_meta_40539.Model

namespace PEqualNP.Outside.L_meta_40539
open PEqualNP.Outside.L_meta_40539.Model
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

def SB : Nat := 7

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

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

end PEqualNP.Outside.L_meta_40539

namespace PEqualNP.Outside.L_meta_40539
open PEqualNP.Outside.L_meta_40539.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x421fe43ccbf8a3a1ff10521fc98221fc41887fc82187fd4a43f699643ff42c87f883a07f08720fe99221fc51103f88598ffd0520fda0221bf41907fa84207f90510bfa9843fd53087f081087f14d20ffa0c81ff424cbfe83187fd4810ff980617c524c3fe8598ff94d10fe21281fc514c3f8a9107f48520fea0221fd5150af8a0a15f14d20bea9e43fe31083fe80905e94241ff190417f544cbfe6210fdcc631fea1c65fc51d03f8a418ff10a41fea1c41fe52907fc64987f0c931fea8e87ff434c7f86418ff14321ff10041df310c7fa43207f88640ff18a61ff50d0ff887907f15130bf28843fd320c3f8a0217ed0030fe98441ff21087f8a7207fd4f42fe216617f5050ffc82a0ff94321bea94437e53887fc84207f14b10bf2a081ed4210afca898ff88630ffa16617f540c3f2a120ffd4b10bf29c857d548837e8721dfd5031be29221bd54087f882207f48630beaa663fc528c7fa6218ff14e20fea9661fc424cbf8a710ff14632fe28083fe43082fea090ff90d30ffaa0217c51502fea2987f90d43fea82877e53103fca1a17bd0a42ff28e85fc215037c80a07f8c921fe28283fc50087fea9087f14031ff99021ff418c6fea4987fd4d42bfa9221fe41087f8a7a05f14810ff19683fe4250bfa64a0ff14043bf28e87ff41883f861885f94910ff994217e51883f863906f50040ff29e43fe31887fe20887f10f31fea9a83fc520c2f8a2a1df94f40fe10e617d54487fc6290df54b43fe2a421fc40483fc63a07f50841ff19681fc5050efea9905fd5121ff29e83fe42107faa0215f15010be29e41bf4210b7aa818ff48620fe28865ff40883f8a910ff94b10ff2a063ff53c83f885887f10e41be2a665fc43503fc43107f50710fc200617e50903fa6410ff10f30ee98061fc41903faa6907fd0b10ffa1865fd504c7f881187f94c41fe980217d53482fca5085f14132fea1821ef20083faa9107f94432beaa4857d51c827ca818ff94740beaa065fc52d0efea6107e10110fe28487fd50107f882907e48210ff2a443ff53486faa7087f50a40bfa9a81fe43887fea6907f50920ff21481fc434cbfc8490774c931ff21e81fc20043f86390ff90d21ffa9c21ff21c827aa9885f95030ee99065fa30842fea6a15b54831bf29085fc5190efea6907f94730fe10e21ff310c7f841087f14940fea8663fe51882fea6a0ff50e10fea90877d508cbf8a5187f54343fea1461f85050ffaa6886fd0941ffa9c81fd30843fe87907f90a30ffa1e63bf54483fc62205fd5230ff28443fc52907fe64185f54a20ff19081ff548c2bca610df54443bf28c83fe5050778a8907f14841bf29883fd50d0bfea020ff10220ff218817d50107fe83087f90a32ff28861ff32443fe84987f0c540bfa9e433c54483fc8218ff142329f2a043fc42ccbf883187f95330
  | 1 => 0xc43087fa63085f54b10fe90621ff404c3fea8907f8cb30fe90a61fe50907fc42987f94132ffa8485fd53903fca7087fd4642fe28a87fe43cc77a8220df14931ffa1063fc53043ee8320ffd0c31ff98441ff43507fea0a1fd44010fe188437e51043fea2987fd4740ffaa663fc54c43f2a018ff50b32ef99465fd328c7fea5205f14c20ff19265fe5350bfea7a0ff90d40fb08221fe30c43fe40087ec4110ffa9261fe43907fea2195f14532bea86437f5150bfa65107fd4443ff29081fd41502fea9107f50431fd200817d50d0bfc4290ff14420fea9063ff20843fe8310ffd4840ffa9463bd41903fe83a05f14d41bfa9287ff53043fca710efd0f41fe20041fc53106fea710df54840fea0e43fe434cbfe6420ffd0c30feaa6617e53c82faa3987d8c431ff90821ff54087fea3a17fd4d40ff18e21fe528c2fca5187e4c210ffa9841fe32886fca010ff14f10ef182617c540c7fe86215f54021ff2a461fd5350afaa9187f14e10ffa1a217d51083f880987f54742fe90e81fe21d03faa39977cc030ff19621fe54043fca9887f0c830bea9a21ff21842fca1a17fd0f42ffa8c81fe20c43baa610ff14640fe988617e50d0ffaa9187f54930fe28e41fc424c7dc40905fd4810ffa8243fc544c7fe62085fd5210fea94217f54042fea990ff50820ff99241fd424c3f864887f90930fe21863fd4350afaa018ff10b20ff210417e540cbfa62885f94c32ff99461ff31843fe85907f50730fe28861ff420cafca3187fd5220fea04217f54ccafca2187f90410ff28287fd500cbfa80087f90610bf2a641ff41103fea6217f94f40feaa021ed320cbfc87887f14732be2a421fd53107faa890de94031de21c81fb5050afaa6107fd0931bf284637e52cc7f8a790ff10420ffa0461fc30c82faa8997f15121ff98021fe52cc3fa8298dfd4532ffaa243ff5050afaa710ff14c21fe98843ff30843fa64087f48440bc28287fc414c3f8a098ffc8110ff28c61fd43483fc42205f14941ff90861ff40103f8a0a15f54231fe29663fe54cc6f8a990ff95021ff18261fc43c87fca221df94840fe28c41fd41c82f8a890ffd0240ff90a81ff510c2faa9995f94f10ff99463ff328cadca418ff15030be2a441ff50ccbfa65087f0c821fe90041ff41106fea7087f90b41bfaa621fe40083f8a9905f55110bf2a083fe5210ffa87205f94220ffa1281fe21483f681087f50a21ffa1887ff32883fca6205f55030beaa487ef4250bfa85a07d90441fe98241fd42487fc80987fd4630f721085ff30443f260187f90b40ff18041fa50087fe42887f54231fea1c61fe42887f88698df94431ff212437d538c3fe62185f95110ff28085fd510c3fea6887f90040f690843fc42c86f8a7107f54910ff88021fe508c6f6a0a17fcc510fea88657e500cbfa8718ff50030ff88
  | 2 => 0xcbf843087f55332bf2a465fd53d07ba6218ffd4321fea1e65fe314c7fca418ff14c42fea9083fd519037a84215fd5231fea9881fc328c2fca818df15232ff21863fd410c3fc80a07bc8421fe29081fd41cc7fa63187f90440faa0883fd51083f881987fd4c40df21c81fe42cc7f860885f94720fea8a61fe5090bf8a5987fd5231ef98461fc43043fe8718df94820fe21061fd5090ef8a6087f94b40ef98c637a50087fca2a17f50b31bea8c41ff4390efaa3207f94c10be29a81fd21c43fc43887f90320fea9885ff32082fca198ffc8120ffa1c41ff420c2fca020ff55031fe20e437e52086faa598ffcc930fe21221ff53c87f886215f54241fe21861fd42503fea010df54440fea0a21fd5110afea498ff50a41bea9083fd53083fa64207f90940ffaa065f920083fe84217fd0910ff19065fc42507fc61906f50c43bf29687fe42907f88398cf55031ffa8c41fe324c7f8a1997f10730dea12837d53d07faa0997fc8520be29c21fe54c87f8a9197f4c620bfa98217e53487faa9907f50932ffa9c85ff51482faa690ffc8640ff21e43ff53886fca618ff90441f7192437d510c3f88410df94042fe20a817d54c43f8a1217f54943fe28c617c540c2fea2907fd0941feaa241ff43087bc64997f08510ff19641fd43082fca8086f10a40ff98241ff31483fe65a0df55120fe18821fe430cbf8a421ff15120ff21265ff50d0af8a9185f54a10fea8c41fc40c43faa2907f90d31ff18e41ff218c2fca1217f0c941be2a2413d54087f863087f15230bfa9a21fe41902faa4885f94441ff2a463fc50d07f886887f8c730ff99681fd32903f8a110dfd5221ff99443ff20883fa80907fcc921fe99083ff318c3fa60107f90520ff29a817d53103fc6390ef10840fea1a61fd540cbfa8210ff14231fea9263fe53906fca1994fd5130be2a265fe40c43f621086f10c40bf2a265fc420c7fc81985f94c30beaa021fe418c2fca810dfd5131fea16217d53c83fea9985e14142bfa9283fe32c87fea2a15f15020fea0461fe43c82fea9196f50440fe29683fe42c437aa9887f14542ff21e83fe43cc3f886197f54840fe294817f54083fc62a07f50f41fe2a0657e548c6faa7207fd0530ffa1821ff308c3fa64907fc8620bf284837d52907fe82107f10d41fda0481ff52cc3fc42107e88020ff98c637e51d0b9a64197f8cb31be282837d538cbf883885f94d10ffa1c21fc524c3fa62087f15330fe19021ff40083fe63107f54e21beaa263fd43886fca5a07f4ca30bfaa2417d54886f8a4a1df54042dfa1485ff52843fea098ff94142be28a85fe418c7fea1a0ffcc840fe194217d5210ffc83107f8c940ff19483fc53443fea2a07f48420fea1e81fc51cc3f862187fd0521fea1a43fc31442fca9187fd5232fea0441ff52503fa86207fd4440beaa643f
  | 3 => 0x62887f14742be29421ff414c7fe8410fe54021ff10221fe42ccbf88518ff15021ff99481fd5090afaa1a1ff4c640ffa1881fd52c43fe65987f08620fe2a643fe42cc3f842187f94121ffa1463fe10043faa3185f54630fe21441fc218c37ca818ff54740bf2a041fc43483f865a07f0ca21bea9c83ed520c7fe85197f4c621ff908417d53c43fa63a07f4c521fe21c81ff41c83fa8318df95332fea1e43fe53d0bfc64a0ff14d40bca8063ff42883fa8418ffcc932fea98217e5090ff883907f54b43ff90a61fd41883fc82105f54432ff28e87fc52507f641105f94c10be29a437c50487fc86885f94e43ff98841fd5010ffca2a07f8c821bf28865fd43cc7faa4087f54540ff21885fd21c837c85207f50020fba0a83fd5150ffc87a17fd0d42ff296837d5090ffca2217f10e30ff29843fd43cc3fe62987f10e20fb108437e51cc3fc6210ff95210fe18421ff50907fe6290ff50130fea1c83ff40c83f88218ff50d40fe28a41ff514cbdc4290ff90d41fe90e61fd544cafca2207fd4032fea9e857d5090bfca6a0df15231bf28841fd53c87f661187f94031fe2a041ff30083fc82985f94a43bf29e43fe5250efca318ffccb10ffa0e43fc32882f8a6887f0c840be29281df4390ff860085f14520fe18c61fd31103fca690dfd5021ffa1c657f53c43f88298ff10e31beaa465ff54083fe60987fd0e42fea1a65ff40cc3fa8590ff15231fe18c81fc438cbfc43987f4c820fe29287ff41cc6faa198ff0c520be29a857d54903fc8610ffc8740ff90c43ff21487fa62905f95130fe29e41ff43106baa610ff4c930fea8c87fb40083fc6418ffcc740df21881f521087bc6298ff50832bf28e65fd10042fca9987f54121fe19241ff54c83fc83a07f54142ffa0a81fd424c7fe8320ffd5221ff212637d50887fe6310ffd4831bea9c637e528c7f884087f4ca21fe20641fe420cafea7907f94f10ff18863fa50907fc20887ed4143bea9683fc42843faa4187f48540bea8e877d518cbfe83987d4c431ff21887ff54c43fa65a0ffd0810ff29463fe21503fea018ff54440ffa0281fe52107fc8310ff50410ffa1c81fc20c43f863107f55232fe19083fd54cc6fca221fb48020fe29c83fd43c43fe85087fd5132fe298417d51d0bfa83087fd4231ffa0e21fd51c82fca821efd5130ff29263ff51c83fa61887f50b20fb90c43ff43483fea0215f94a32fea9c857f504cbfa85a0ff50b30feaa043f840082f8a610df54b40fe99243ff319037280207f90b20bf29083ff21103f86518ff08410bf29087fc51503fca521df55130ffa0621fd40103faa910ff4cb40bea86657e53843faa9087fd4943bfa9421ff438c3f865206fd0b41fe29421fc53103fe62205e540219f2a621fe5390bfca020df54740fe21c21f85050b7a86a0cf15130ff29281fd518
  | 4 => 0x6fd0d41ffa9681fe41cc7fe43987fd0421ff98a81fe548cbfca3997fd4043f799465fe438c7fc4210df55021ffa8465fe438caf8a898ff14132fe29487bf41103f660987fd4730fe20061fc50487fca2107fd4a41be28287fd430cbfa40087fcc730ff21c41fe51903fca021ff4cb21ff20021fc21d03faa520df15331ff20a817d54cc3fe84207f55321fe90843fd430c6fca5987f14f41fd28063fc40443dca418ffc8310ff286877e50843fc81087f48210fea8643fc420cbf862107f90730dfa0081fd40cc3faa4a0ff10f41ffaa643fc42103f2200877ccb31bea9e817e50043fe87a07f95132fc20641fe30043fca1196f50b41bfa82637e53882faa521ffd4331ff2a0617e5190efaa6087f90830f7190657d5190bfaa2997f94530ffa9683fd50ccbfc61087f50440ff29221fc43487f8a8995f94b41fe99483fd32503faa9887f10f40fe21c43fe42443faa720ff95130fea1221fc5350bfe43887f94f20dfa1887fd32cc3f680a06fd0441ffa8c87fe540cbfa84215f54810ff29c81fd508877c86a1ffd0a41ffa12857d528c3fc84a0ff94520ffa8283fe524c3f882187f15110ffa9883fd544c2fca7207f8c810ff210857c53c86fca6105f54c41ff188217c52c42faa4187f10510fda0661ff31c43fca3217f90c30fea0621fd42506faa321ff08440bf286837f52c43fe85217f0c921ff18c21de53087fc65087f88010ffa1841fd43107fc43907f0c740ffa9a837d528c7f8a998ff10841ff98621f940102fca3197fd0841bda8287fe20843fca9907f50d31f719643ef20883fc83887f90e10fe98841fe53883fe65907fd0d43bf2a421ff434c3f860907f90030fe29a43bf41903fc8418df55020fe18c43fe42087fa8220ff0c521fe188817e508c3f885207e10330fe21881fe504c7fea421efd0240fea10437f544c3faa5187f90c10ffa9e81fe5310bfea3997f48110ff202217d5310bfc8590ffd5110bea8c21fc32082fca890ffd0a40ff18061ff540c6fea4a06f15130fe996217e54cc7f884907f94543ff28c87fd53487f8a2215f94b10fe20843fe41487fe84907dc8521bf28643fc324c3fa82906f90541bf294837e5290b7c84207f10a30bfa8a87fd314c3fe6590ff8c110bea98437e5410bfa83207ec8120ff28881fd5290efaa2217f95121ff28065ff43d07f886a15f15320ff28c65ff20082faa5987dcc531fea8e61fc514caf2a120ffd0e21bf2a2417d54907f887215f94f42ff2a241fe544c7fe6598df54831bf28c85fe520c3fe85187f54b41fea94637c504c7fc64887f8c430ff99483fc32d06fca310ff50f20ff19061fc21903f8a120ff50630bea80657d50d07fca121ff0c220ffa1a43fe514cbfaa5a07fcc940df2a043fc21483fca1997f10a32fe986417d54843fca598ff10c41ffa8e87de4310ffc
  | 5 => 0x156064098000080640100201c0000101a01a018030230b20008b80a0bc4e01688e0000280a00b0027ec0d806176088188160420240b05c04a02c008002500000003000800c0019103008bfca5a1ff4c030fe19641fd320c7fa63907f94720ff98e41fc31cc2fca6217f4c832fe20c417e54882f8a8887f8c920bfa82837e52043f887887f54f10ffa1665ff41043de64997f50a31be2a261fa20843fca4a0ff50a32ff20241ff43c87fea4185f94040be2a621fd50086faa3997f55110fea9a81fe428c7fc81185f95321beaa463ff32507fa85107fd0f30fe29c857e500c6fea9987fd0210be28a61fd21043fc85105fd5110eea18877e53907f8a6a0df15021ff10821ff40042faa021ff8c841fe98e43fc32c87faa5207f8c120fea9e81fe32903fea498ffd4841bf28061f920443f88318ffd0431feaa061fe21843fa43087f0c020feaa0417c53887fe86a07e8c030ffa8c65ff5110bfa86187e8c110ffa1c83bd43d06fca4187fcc821ff29841fc50d0ffa62a07f90d42fea1a21fe50087f884107f95110fe19663fc31c43faa1197fd4b43fe102217e520c7fea8987f95220ff98a63fe4390bf8a1a15f54e20be2a661ff434cafea0a17f8c640fea1a83f710043fea7885fd5032f699243ff504cbfea110ff94341fea1885fe20483fa60887f90531ff18a41fc32503fca6907f0ca41ff2a665ff53907fe84107f90c41ffa92837d52903faa0a0ff10930ff20441fd43d0bde4310ff10f32fe288877e54c43ba6598df94d20be29e21fd41082fca4197f55231fe200217c54886fea2a07f0cb30fe29021fd420c3fa82985f94020fb884217f53883fa63987f15010fe99663fe318c27ea8907fd0430ff19461fe50cc7faa598ffd0030beaa641fe54083fea8187fd4543ffa9461fc40843fea598fe88110bf298877e53087faa70877cc832ffaa263fe30883fa8610ff54443ff29421fd42842fca2217fd4420ef99263ff41443f842107f90e40fe992637e51d03fc83907f90d20fea06417d53d0bfea121ff48430fe28663fa10043fc42187f08530fe21683fd50907fe61907f55131fea9e41fd53882fea690ff0c530bf2a443fd42043fc85087f8ca31bf29481fc42487fc42887fd4e20ff29481ff43c43fe85a0ffd0110fea1887fd21443fc840877d0d43ff21c61fc524c7fe6390df94f41bf28087fd41d03fa65907fd0541fe29221fc42887f885a07f15031bfaa663fd5190bf887a17f54031ff18c417e50887fa8290ef95310ff194417d5390afaa818ffd0b40ffa1443ff320c7f886107fd0921ffa9843fc32c43faa1a0ff14b40fe20821fe41c87f8a7a17f50e42fda06417c540cbf8a0197f4c710bf28465fd52503f8a3217f10d30fea0c43fe520437c84a17fd5332ffa9221fc41843fe64197fcc931fe2a6657e51903fe8799
  | 6 => 0x60100a80b02401817830004050000000020013d002016024002486f400c1400100804803876016380be0180700140782600a5d4008180080103002e01e0000500b2ea1480204a00a000089d204c01410870008015fba440301965c0065620000181c01a0080b00000c018078013cc0140384817e0000000d01a024068080020181f80100202000003006070138161ea0080e000000004090170080b40480005202009d060000680100205201c000000020d8378000b62f40400500099008007007378278050081da228143640e02c0022a4186cf81800e0cda7802000004000020000040112004a39c0c008000000038040020040380f002024210000180502280314005cce8010180800200201a000130130ca02031aac0001440005100000009801038010038000000a00480e0ca000ad0080020000900f1580001880401a211228130000180000b12e0040480000207c3700000006c2c80002a01c0d8430043700028d09a0540382207a0040204211f23c1a00100002c0504400e364658000000c016039006b90018100100580180a0000000b8c006e000001d10560140000a02a3f44a0080023f0000231b03402a8080ba26c070060000200100a000000018010000541d95303c0200180c0240040880200000043094000034050510040080807728e0d402074000038008080ac0a8f08020000000193206a070268150020000200005e04800007000858048000680d04316385a0080801202e000010190103380000103c1f81d0bb0264c4088000000001f0425da2005d8000240240780d0040085180101407012001034edc0000003c009b684704800005a5e00a00090813000001be80001800000809066000008de0240440400a0260859e0211f60300000600e0500000000c52c3f8070220082183206205e9a01a00c0081406b01a0000000d00800800800054018288b1016070000250620015a0033280e80080000c15400819000000018030a6000ce84a0020080080000001c308030be028028010000000380005e004020050160a403002046000008990120004883901a0000080000a00c00010030024180040060040000200000c0981109402400
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x25190b3d61d5130b798c428ca7d6194e40d758c548cb7551146409f59641cc33d6414f109f191508c76e528c840bed81425067e658c7209fd8154442cf654c832ded5340442f7614c9219fd95321027d6510e10be98221c42f96014841bd987424867f654c110db94a420c73c54501209f997420c6ee618cb21d754b318c67f6054b31be181430cb785454031de540500cbac52509419f997420427d63d51209fd97430837b5214143bb58e214877765440109f195325077b6054b40bed8121103cd324c7219f99543843766115010cf55131086ee6214031de50a509075d534c8409f195311037954940219f9875050a7e6094b31d754f310873d54150319f18154ccadd63d0b329fd96438427f65440109e983548caf5610c9109f98b538433e5490b30afd90321037a65141429f58650042bd6110840bb98a438827e63942419fd91534867e62d4d109f99643842fb6050a21ee10840c83cd538cb219f18d54c827c6255331be98021c433c6454910bed81439076d52c8730db14e32c87cd52cc431bb98841c827e658c521d754c538436d6215030bb58b30c827c65d0e21be58031842bd64d4031dbd4a21502fa600c620f3585320caf561cc921bb98b5090e7d60948419ed81544c33d54d0c209f99252082bd6110e40af59031842be6290e40dd584540ca7d6094732be18530442ed6214e419fd9541086dd63108329f18550cca7e6494730be583214427c6550e109f596215027f6550521cf58e54c433d6414e21db54a320433d54508219f98c515033c5490d30de58a50906f76044010be18142906fa60c8420be58331cc27f6454e20d794f31c827d650c7409f194424433d5350441bd98454083cd320ca41e750c43d027d6414f10af59031902bf6448310cf953430c6f8648c030be58031902be6414c219f185500cb3e54483109f994324867d62944109f58a53c427e6510930bbd8943086f561140429f19543c86f56110a31e794c431027d6548430dbd49324c3ba21500409f995325077853540219fd855010b5e6314b109f997438827e658c841d758f548ca7e60d4d219e583548cb3c54d04109f582544cbb94150040bed81544ca7d60d5331af19121902fb6050d409f195404427e6510910d79524310f6f5290941afd8141102ed620c5209fd9543103794394021d754f320867d63944429f597418c2be6494530ddd4651ccbf26188210f5d8d310c75d53484219fd97410c36f65508429f594320433e62953109f994204427c6550d20de544400c2796510020de544400836e5490842d714b324c6cd638c832be98231482f860509409f18154c867f6550c20be58c400c3765188440f34c8325035d5314c40de58d500867f6454b30cf951438c37b5454021ded95300c35d65cca32d754f43d0afa608c740bd984308427c65d0f10
  | 1 => 0xcb6c5248110be99230842dd63087209f990504867e6194e40db54842102f5638c4319f996434cabe61d0d419f195414873f5495332de506500867f6510c31af59051c82f864c4210bed81434833e5450f10cfd0d5190efa6090f30cf552430c6dd6314b10cfd52544c2f86050e40af990325027d6314142d794d210877964540219f59442cc3b85150040dd945410836d4354831bb58a430833f5450d30de985500873e5450c21db54932c433d540c310f34c8324827d6590d219f587540833d60950319f987544c27f60547329f58e548867f65d0810db94a42042fb60551319f997315027e6014d21de54a509076d62152209f582540867e63947429f98e50d06b96010c409f587524c27d61153329f994534867e61d49309fd91520c75e530c621ee185401027d6494232bbd894350a7d6510c20f34c832d037965d0330de55340cc37852102109fd95414c6ee6215030de1445050b5e53cc8219f996404c26f6550842d794d320c73e5490431cf10a501027e64d4c219fd9443482ed65c8220de94c400c35d6314810be98043cc33c5490d219f59740042f66190c31be18142d03755114730ee8c5401027e6294010be982321027f65500309f98454482bd648ca409f994434c27d6394020fad814210afb63c4210dd5445110a7e650c910be98232c836e5210b40cf95252c437851d41439fd954310e7e6590e21db582520c6b86050b419fd9632d02fa6010630d714e325067c65d0931ee55250086fa6014442de886500867d65080109f58354c873d54d08219d984540caf561109109f994438427d658ca40bb988310433d5415232dbd4a52c433a5494021dd946311035e53cc3109f195204435e534c420d754f210867e6494c31af193311027e62952109f996410827c65885309f19643442bd648c6408f990540c67d64d4c10af99031502de63d4242be580540876d6054831de1532088375510c730be58720482fa6014643db588540c73f6355310be582318833f5450520bed8b10442dd638c431cf15241483775194643bbd9532c867f6590910cf592518837a60150319f59743883cd544c8329f596320827c654cb109f997320427d658c540d794c431027c6354840b798c414c27c6454f209f995314833c5414520b758e525033f5488520cf55230c433e5490a329fd91534433f5495230cfd81540c7ad52108409b189534427d6194843bd58732cc7b654484218f992544827e650c9419f992518825d63d5320de54740c827d65d05309f992528427e6094f21cfd5254cc73d54cc310be18132882f960cc430ee10c404427d65c8440bed8d20843d5310c5109fd94434876e528ca31be98042442fa6014e219f19743442de6314042f554e21086bd64909419f986500cb3c6115130cf55042c437965c8220b798c424c3d9300c2209f98
  | 2 => 0x6395020af99031d033d5454c21cfd8f544c33d5450e30afd8d4310edd6315021fa94a500c7b954540319f98e52042bf6454910b758c52106786055321af98b409033c5414930de8c650086be640cb40bd98743d067e65907309fd9543c83b94010110bd98743106bc644c440f6cc9300c27f6590c329fd9642cc67d65d0d10cf951410873f54953309f982530867c6355020ed54741103af5290942dbd51520c73c548c130d7597318c67f61552309f189510c33c6454d209f98a508c6f960108409f59052c43bb4110330af992311027c654ca10bb98b54cc2f96014642dd987530427f6255310dd546410c27c6510930cf55240443795454031b718d525075d6494c21cf945419027d6094b31db94a320427c6590f219f986540c3775148520bb98a434867f65107209f993504876e62d5232be582410427e65d0f21be58042c827b60551329fd91500c6ed620c710af580429035e65cc9319f994414c67d60d5132cfd5231482f960d5031dd587538427e65c81109f99250cc76d6214f109f993504c73e54140319fd9443c43755114520bb98a43cca7d6494c10bed8152506bc6454d10b5185324c73c5410930de18b5050e7e6514910be980314867a60d5221bb189438ca7c6590931cfd8c54482dd6390832de10d50087d65388421af990510827d60d5221af98842103795410110ed58743d06f9600cb30cf95341cc6f960d06109f19152c433e64944109f181544c6bc6050d41be580540ca7f65508429f984540427d6215110cf58d54c437b5094032cf95341c82fb604c920cfd52524c3795014342f9d85324867d6295330cf55042c867d6114930cf552408435f534c510db94b421076e6054831decca500c75f5394c41cf153404835f5394f218f990514cb3f4254442be98231c436d5290a419f593530836d6294d21db54b42cc27f6508630de550408435e53cca20bb988410875f63551109f595420427960d53328f99353c837a4254241b798c500873e6494d20afd9130c427d62150109f18153d0a7e64d4b10be982414c73d5415330db94b42d073e5490820b758c21102ed62d4031bdd85425067f650cb40bd185524c2f860509209f994420c67e60d5020d794f43102fa6010c30de9445050af76150a21bed8132d02fb604c420af58a415067d6015232db4c9510ca7e65108329f98a51d027d6394820ded8950906fa64880209f58254c86be64087109b58853042b8644c2109f58e50886f56114c40be982400c27d6195130be181438427d6588440cfd95540873e6295031db54f21886fa6090c30de90d500c6bf64549309f997438875e5350c10dbd4a520c67f65cca40cf189540867d6395320bb988314c27f6548421ee950400c3b86090c40cf58154c427c650c9409fd94410827f6054e419f98a531027d6550c21f394e320
  | 3 => 0xb30bb98a43c867d65c85409f99252cc3ba54d0320d754c41086bd6408420d714c325075e53c84219f185540833d63d5120de18c5050af96014c429fd8553d0b5d53d0c42d7192530877964940319fd954310bce52ccb31bb588408827d63153209fd895190f3e54102209f58e544c33f5450530be1815350b7943141429f997415027e61150309f592500876d6214e20bd586100427f654c941bdd9510042be640c520de55040c82f86148110be18131d027c62546439f99742cc67f63548409f582520c67e654cb109f59643106fb6050540cfd9154c427f60550329fd9642cc2bf6448110d754f420867e62942439f987540c3796014910be59610042dc6354121dd544510c27e61d4c109fd96400827e6495131ded8f5050f6d5290a409f59421d027b6544010f350d320cb5c534c5109f191518ca7d6194b40afd91524c67e6394b40be98332482fa6514143db14a425067e6195330eed8142506bd64d40219fd8154cc7e92008310bb18940483785314142b798c420ca7f6550020de989500867f6590730b798c21102f96010d209fd8d501073d5415131cf94741102be60d0941be583428839e54cc431cfd53524c37565cc6319f9865390a7d63d4941bed814310b5c2154c21bd58740c42ee6210c42de191500c6bd6090e40de9875050b3e54507109f59443c827d658ca10bd984424c67e64944319f98354c867e6414d109f980548873d5250640dbd4a529033d54d0e219f988540436f6254810de991500c77551d0440cfd52548c7755110440db549410c6ec6250e429f189539077a4314143be98332d027f65c84309fd9542102f96015031db58853042de61ccb31be58043d037a6254031dd946318c33d6494630af98742506f96090530be58243c82ed628c220af191300c36f520c941bed8142442f661cc921cf952210867e6215120eed04400c36e5290a40cf95242c86de63144409f980544cb6d528ca41de98d509076e5208210ddd47314827f6354b109fd89534875e53cc421de8c9509077551904209f595218c27c65509309f99632c42f66114032be980418833f5454d20d754c310867d65880109f58252d075f5350d429fd895090776518c420cf950408433e5488710ded81534433e63151209f59642443eb6248210de58352c427e65d0b309f593528427c654c8419fd9521cc2f76154943decc6500c77b4354021be98352906f561cc831d798c54cc33d20151209f5805250f3c54cc130be58840c82bd6414632bb588318867e6494032cfd52214c2de63d50219f596420c27e60d5231eb94b42d067d658c910be99620442fa6010e209dd85534833d5488310db59632c873c6295031be181524c67d6294e10cf5974290b7a52880209fd81529067f6454720dbd4a52906f9600c830bed81428c6f6610ca41ded92509067d
  | 4 => 0xe587308c3e95288210cf55143082f8604c840ded425050e7d6295331af19120c435d5310f41d754d30c827d65c8430cf95231c427f65d0b31de98252842ed65cca329f197328427f6054841cfd5341882bd6090a40af98b41102fb604cb10be980424c37a60d5221afd8943d07bb6050f419f59431c82fa6094943da149204435e538c410bd18532486bd640c430f54c4314c35d538cb209f99250083cd320ca21bdd85534835f5394c109f594424c73e5450c31be181428873f6455230dd94610043cf604c8329f5865010e7d6594c209f590524c3e96210020fa94a200827d6094c21be580310c35c534cb21bb988430ca7f61551219f996314427e60151319fd9151082f7614cb41bd98742d076e6194831d794f32c42f7614c8419f98b5150e7d6094632bb5885110f6d528c431cfd52314c33d5490621cfd5254c82f661d08419f588514c33f60953109fd94418c2f661ccb31f58c9310c67f65908329fd9743c82f96010520be58242c827e6214d209fd95304835f53cc621ee945401033d5448710d794c310867d63d51109f594218c27e6590930d714e4350be6618cb21b718532cc75e5310f41be5835390b7b65540219fd8153442de6314041be98241083f23194031e7d8d435073f54549309f99743c82bf6454131de983530427c6454c10cf55043ccaf963c4110be980311036d5214a309f587535035c538c5209e195204427f650c4219f195428c2ef624c4209f581530433d54ccb109f98252d06b86050d41de109500c66f62551319f9845350a7f6454a30cf953428c67e6094643db948320c77a4154021be58041d027f658c8419f18d51903796014520eb19120083766114b10cf151434827d6494810ee593108427e65d0f109fd895010e7c6254043be98031c827e6510f10be583530875d53cc3109f98253d0a7c6454720af59031cc33e5490842dd54451c827d6494f21d754c534837b51d4143cf55054082bc644c2209fd89544cbea2148020cf952310867e6510920ded8154cc27e65cc930be580318c27e6114810de4ca50906bd640c630be58031cc2fb6050f109f98650d0b5d5314c109fd97420c3f0614c1109fd94329027c65509329f597300437551506409f9944350abe63d06409fd8550d0afa64c4210be18142c42ee6215031f34c832c436f524c931bbd894390bba6410110cf982540873f6454321cf5095110a7e6195132cf18654c439d5310c40be58232082f960085409f596320c67f65cc6209f992500427c65484309f9865090afb6050d429f58e52086fa6008510cfd9154487e64148421ee9085050a7e65cc440cf550420c6fa600c721af993530875d53d0421db58b540c6de6308720bb587328ca7e61d4d40ded8c5050b765188620db58b548827e658c620cfd52548ca7e60944439f592530836d5214
  | 5 => 0x5090f7a42d4142db549211037b50940319f98f515036c5494831cf58c544c27e61952209f195430867d63d4940cf151414833f65508429fd8d51c82fa600c421cf99053c435f534c920de94b408427e65c85309f18d544867e6550c20ee90c40083d8314c030d754d32106f860485209f59732106f7654c431de5845050a7d62d4f10af993104433d5350640b7d8d428c6df654c431be18121d027e65d0d41de0c9509073d544c821bb98b438caf9600c6209e983548c67c6055331bd58643cc73d54c8710dd58654442bf6550f41de19520442ed620c5109f1895090f3c5488520d754d420867d65d0d20f9484214833e64153219fd96430c2be648ca40d754f431026f62551109f59642086f86050e30ee50040042ee6290621af19321103b8644c110be583529077a54cc230bbd8951502ee620c6109f587504cabf644c110be18143cc27f6510431dbd4a520433d5414c219f59253886be6494630d794f410871c5350d41cf95342882f96014732ddd44314823d64d4f209f988514c27c6454430bd984400427d61149439f988538427e6294730d754f43d07b664c4010cf552400c27c654ca419f994425033854cc130af59031882f965d0030be1814310b3e5454b10be181425076f52909409f996311027f6454221db58a544875e5310421af590530837b5094321fcd85304439c548c1309fd855090e7f6590a30de94b40cc27f6254630db59720882f96094543d794f420873d5490f20cf15042883db4314143de50c5050f3c5410d10bb98831902f960d0d30d718a5308778538c110cfd52540c7b86050c43bb5885010f7a53d41429f59642cc2be64085109f996424867e64944209f583514cb6f6254b10ee909401027d62943439f197438827e658c8109fd8951d0e3d6414c109f988530436e5248310af99031c427c6510d21de189500c6dc6348430dd984540c6be64d40319e181544c67e6590b30cf990548ca5f6550c43cfd5040cc33e54d06109f18554c835e6315031cf550430ca7f6154c429f58e50d06fa60909409f580544875c534c9409f99630442f96288110be582311027d65d04209f996304833d54cc710cf550428caef6250d329f597324439d4310e31cf553530876c528c931d754b310c77551146429fd8152d0f7a53d0110b758c42cc37954100309f98b530827c6254e40ee98242902fb6050e21bed8143506bf644ca409f1855210e7e6510921d794f43d06de6314c21f34c832506ee6214643de9845050f6d528ca31bb98853106f661d0d31be990404435e6314f20d754e4390a7e61948409f99053c43776155110d7d4f32c86f96014c419f58e52d073d5494c21edd85425075e6314d21bb58b314876d52ccb31cf153414c75d5310c40b718d218c27d6294f409f181530873d5415320be991208427c6454a31b
  | 6 => 0x73c5450110db90e520c75f6354d10dbd91520c7795214143bed81428cb3d6055021bd58740442ee628c020be980431027e6314c109f188534827f6255330ded95500c67e658c840cf59053043d953940219f597410427e64d4e21be58041c435d530c2109f597424c67c65104219f59643842f96088740af590325027e65cc1209f1815110e7d65cc941cf552430c27d6195110bd986300433e52d0b419f59631482dc6354540cfd8b544827d6395210afd91200427d6214f10cf153314c35d538cb21db54b211027d65900109e58354887cd32544329f590514ca7e61d53209f98752042fa6090f209f997430427d6494c31edd8541903785294241bb18930c833e54540219718d544427d6194a43d798f540c3775194540bd98432c435f5350d409f98c5150abf6448440cf951410c67d6510e20cf153418c76c520c941fc501100437a42940219f99632502dd63d01309f590528427b60550329f596325027e65d0510afd91514ca7d62d4530dbd4a52d0f7841940319f98b535033c5490e30cf98d54086fa60d4e41af191500cabd65d0641bed81438c6fa60104409b588540c33d54c8310d754d439073d5450420dd545311027e6510b109f58454c827d61950209f98252d0ef86055121ee15040cc36f528c940d7d8d524433e64d4f20cf55040c43746155132cf54e431027e61951309ed8154cc67f6510f209fd8d521067d6094b43b758a314c73f64553319f18152d0ef86448210f34c8328c76c5288540ded9550907cd604c832d754d31086fa600c820be583548cabe640c621af19032902fa6510110af990325073f5490920cb951520c67f61552209fd94420875d5350c10cf58254086ee6214c40ded06500c73e5450a31d754e30842fb60508109f597410c77860551219f58c54483e751885219f58c52c43b94010130d794d31c827e6394d209f98a548c6f86054532bed8e20842f96510030d754e31886be6390840bd987320c7ba32500408fd9541106ed62cc7219f98c540877b50941429f988540863e6414b109fd97438827f654c841de583548ca7d6294d20e7191300c2bc6454530d714e435063e6414e21ded0a500c67e650c440de980548436f5294830bed815250e7f61552329fd8953d067d65d0d21cf153324c2bd6190d43af597419033c5448530de98b5050f7a6014e20cf9494210a7c6454732de9885050eb8644c0309e98251d0e7f650cb419f597320827e61d52209f588515027f63540219f59721d03766114c209f988534439e53d0f41af19150486be6414032be992300c37a52482109f98254c86fa60d5021af587401027e6510430be58021d02be64cca40f3549310c6f6618ca31dd147214c27661150209f984540ca7d65501209f19531d027c6454f219fd94300433f6315130d7191530873f64552219f986
  | 7 => 0x550b31af59032d03cf534cb21cf55021c423d6494d209f980544423e64148109f582510cafb6050d109f18d508873d5414f109fd81544c67d6550830ced5040cc2dd6390830cf550430873f54d0921af19150c86f56110e21dd947310c2f8614c2109f590538437965cc2309fd8553902fb654c030cf990530867e60150329fd8d544cb3d6215130db148214c2f9600cb20af592518833d5410010f948421c427e61d5330ee181425067c6510d10be597308c33e5490030dd545410c27e6214d41ddd46519033c63953109f994324c3755150420f3149324c6ef6254543d794d328877b6055032de8ca500867e6494c21d794c31c427c6454232d754f32c433f544c1209f996434c6ed6210520b758e428c27c65cc810afd93319027f6590830cf95243cca7d6314540cfd81540876c6255110be980214c35d5314e40d794e439077a5144010be58321843b94110110de597108427d61151309f189518c27e62d4d41bd984325073f548c9209f99353082ef624c120be580314873e6195310cf952310c67c650c5409f992500c73d5410b209f98e540833f54d0d31af59031486f86050a319f994544877a6015220de50d50086ef654c832decc9500c67e6494a309f98352507ba6350040cfd52534837a5294031d7951530867d65cc8219f597218c37a6014e21db94a20082f86050910cf95142883cd320c910d754e32083ae5210840d354d210867f6510832cf596431033d54cc831cf153214c33d540c710bb58b404827e6394a419f582534827c6510f21be983548867d6114d409fd91518833f6455021be583421027f650cb10b798f424cafb60509309f58e520427d64d4d219f98e500427d61d50329f997321075d530cb20be181544caf661080109f594410823f6454321de5405090f5d5314e419fd89511027e65885409f19443c42fa60884109f98454c837751c8530cf987544c33c54d0b21fc485500867f6054c21db548520427d64944109f594311033e54900109fd8951902f56110f10ded475050a7e65080109f9835250ebe644c941ded8153483d4324c4319f5835250e7e60d50109f597325027d60d5231cf152314833c5454d20af5924310eee62d0320d794d42087e4614c9219fd96324427f654c910cf55054486f860505109fd95418c27e6494810e754f43d067d65900309f987530873f5410d10be98021043755188430dd58454c86f960906409fd91510c36e524ca30d7d4e5310a7e6315121be181438827c658c5209f596410827f65cca10cf548421037a52100209f996310837b64940319f194438877960d52219f59621cc2f96090610dd945210c27f61551329fd9643886dd638c931be99130443e5524c431fc905100433c6255031cf95240083da538c0309f98b504c67e6550910d798f540ca7f65d0a319fd944108
  | 8 => 0x419f995424c2fb604c7409fd94420827d60d4542cf95232086fa608c8209f99621cc27d650ca10ee551500873f5495210ee0c9401033e5410b309f99543086bc6454d21de18153102be63d02409f992534867c6590c21d714f31486dd6314440de58c5050abe64c4010f694e50086fb624c110af59031c87ba42d41429fd9643c827d63944219f992544c2ed620c4109f98a548c27f65107309f98a530427c64549109f98c5050b7a2154021cf95242c434d53c84219f597424c27e6394910db552520c7766115020de59250086f86054543cfd50438c27d65950109f993538833a5454021be98231043ce538cb219f58e5190af4614c841af99031443786454021eb50842c83e54148421ae993104435e5310f40afd9130042de65cc931bd18532d06be60d0a429e18154cc67c65d0f219f592520873f5450110bed8b108437b6055321de58353c43e840c8020af98c431037b6055120be980521075d5314d109f586548c27e6194843be192200827f6548430ed98742d067c6550520cf551438873d5290a40af19132902ef6254131bd587438c73c54103209f98e54c82de6310730de540501067e6494f109f98e54486f960d4831cf99053082ec6254d10b718d418c27d650c9419f994211037931940319f99543c43b84310210cf94942d073d54d0710cfd52424c2de6310b30ee181435067c6154e209f597430c2f565c4210de10e50906f56114840db54a420c73c54d0110dd584540c2f962d0110cfd8d540873f41942419fd94329067e65d0720be980428427f60550319f58e544867e63948419f595424435c6254c21de90d509067f6355120bb58e320cafb6548020b7987324c73d5410710af990210436e5288710db94842102f66114830d798c53c427e61d5232af992211023e6414c10dbd4a524c67c65d0f209f59743c427c6510431af19120442fa6015021af98343d07bb64481109fd8553d035e5350e42cfd88544c27c6590e10de551500876f5294840ee10e401033f54d0521de94c400827d6194e20cf55342c427d654cb10de596100427d65d0831dd144214c35d5314d42cf55341cc79e5454c219f984544c2fa6014031decc5500c67f6054c41bb98a4350bcf544c8329f195320427e6414930dbd89544833d54cc4319fd94210437650440109f58e52c42fa6088530d714f324867f6354a41cf1534188775514c630be980514ca7d62d5310be58021c427f65486309f58a50cc7745148520eed0440c827c6548530db94932106fa60144329f185531027e6588640ee58940102bc64549309fd9621902de6314420cf552500c76f6094831bd586430c7794294031d7d95310c7ad5494831cf95243cc36f5294a30ee108400833c54101309fd9621cc27f6354a40cf55043cc33e5490821af19130c82bf6550040be582214827f6
  | 9 => 0x19150cc7b664c42109fd95320873e5410a32bd984408427c650c910bd587428873f540c920de982518827e6550e21bd18542cc67e63151309f595204433c63950319f992524433d5410410bd98730c42dc614c9319f18553d0bcc534c9219f98b544c3d6434c431eed91401027c6354442d7d4d435075d5314c42db54a420c33d54904219f18554cc27f6510c10be58353906de6390a32ded4d100437751085309f58b54cc33d54d0721cf59353c837b54d0330cf153424c27c63552219f9835150a7f650c4208f596540867f6510a109f185548c36e6294f21e795253087ea4248020be18143cc67c654c510ce552500c67e61d4d209f5825110aee620c4309f58c525073f5450921d7d8253086f56190010f994a210867d6590440cfd52540cbea52882109f582548c7b960905419f98e529033f548c930bd586429067c61552209fd8d50d06bd62d0d419fd815310b3d54151309f18553d027e6510810db98852042bd6110c40d7d4d318866d62150109f18553902ed6490842af592534833d54d0810d7d8d53042f9600c440cf150214c37a5314142cf99053042be64d4b30cf95232c427c6510c21bbd89418833c5450b219f59053c836d6214e21be58221c427960d5231d7d4c434433c53d0d419f99543c82fb60508329f59731882dd6308420af590215027d650ca40b758c5010bf231540319f580540873e544c3109f98854842f9600c7209f98a53842bd640c4409f986548ca7c64543219f992510873e6415332af59031c833d5450330b758e418c67d6295031cfd50534826f6548421af98a43102ed620c530ded425010b3e64d4c21af994544c27d63d5320d794f43d033e5490c30db54a320c6fa6094543d754c32c86fa60cc910bb988318c27e6590630cfd91544cb6d5248310ddd85534827e6295330d7d4e315036f5294843be580434437551145429f99631d033c53901409f58e544cb5c524c931db54a20042dd65d0e439f99640442fa60d0a20be982314c27c6590c20cfd9154483785444010cf58954c42f863500409f58c51482ef6254d41bb98831cc27f65cc640d798c53482dd6310b31be18143486dc6350430d754e310427f6510c209f588535076d52d08409f597310427f6154332afd8d42d067e6395321b798c51c8375518c420af191211035f654c8329f58253d0a7f6550040d754d320875e5494c21cf150314c35c534c1209f181520c6dd63140219f98f52c435e534c4219f988540c76e62152329f994215027f6454332af990214c27e6314121cfd9153442fa6014843cfd06501027e6550c10af594439035f5394d42e7951310c67f6550831de505500867e6014d42ded8c5050e7e6014c20dbd4a52442f86050f32ee950404427d6550c109fd9631c837451cc5209f181534876f654cb21ddd95310c67c63540
  | 10 => 0x48427e6194b30bb58b438caee6210220af586429037561152109f98e5010a7e65d09319f98b51503ea6210020fc582411077a60d4810af990520c33c54d0921de54740902f4614c931de58053c43bb5410320be980540c73d54d0330d754f431067d6314121cf950420835f5454c219fd81524435c5310d10fa54a500c75f5394e42d758153086bb6550040d798c54087ce424c8329f99431d037b6054f40cf55131c43ea5254031cf0c5540c77a60d5220ded4f5050a7d61d41439f19632c4374514c530bed81430427c64548109f595328427e61943329f99421443ad4210841d794b32cc6f66188010fc945100439e5490c43bed8142842bd648c840cf553430876e52d0b40af98843902ee620c620d754c31c433e5150441dd586544c7785310110bdd85324c6f96090c20dbd4a214c2f960906309f58f514827f6510a309b98854042fa60d4e42b798f500875d524c431bbd89505075f6354c21fa8c9200837a52942419fd9153c827f654c440fa4c120082fa60d50319f194434827e6550a10ded4b5050e7e60145329f58253c875e63d50219f595434839c5350d41af59053087cd320c810be58b10443786194021de98354ccaf86050810de0c5500c67e62d5210bd584434427f658c840eb9514210afb6050a409f9845050e7e650c720de109509077b5094041af59231103b76150d41b758c50107e762484219f59643c873f60d5130d754f318427c6055132bb58841886fb6050e42be58d204427e63152219f195414c6bd63d0b41bed89200827c65d0e109f1855010b7b5410030d7d4e538863f6454032be18143c877a3154021de982511067c65505309fd85534827f6254e10de14c40c83795354241de9085050af86054d41cf98a540875f6554c219f583525073d5415310be588400827e63944209f58e5090b6f6254d21cf950418867d65950319f98254cc75f6354e10bd185424877853d0210de54440cc3ad42108219f19430083b65150640af990435075f5394f10dd98753c42be6414b10de983540c35f53d0d109f59631902f8604c5109f98054ccb7a60947439f99632843b5548c431b758f540867e650c5109f982548c6ee62cc120de0ca500877854940219f195214433e61550319f98b540cabd6414810cf98454482bd64148319f18953c433f54d0110dbd4a524c2dc6350b329fd9620042f46150f21bd984324435d530c8209fd95424c73c54d0530cf55353c427a60d5010cf19150cc67e6114930be580420833e54d0a21be58251d0a7f6355221ee500408437b6354241cfd9154882fa6090540cf55142c427e6495121cf98d540c776510c430de181540c2f960d52219fd89534427e654c5409f996214c27f63546429f984530875f5394f42fa480200427e62943439fd8554cc27c63552209f586544c67d6494830af
  | 11 => 0x7f6454021be582420837962940319fd95434833c544c1209f98c524433c6055031cf951428877b5410320cf152324837a5114143eed06509067c6548640d794f321067d650c8209fd8d54c42fa6090520de192500867f65100209f194215033f5490320cfd50324c35d538c220db14a425037960150329e580540867e6590d20db94921103755114540d714f43442786054d21cf18654087756115331cfd51410427e6395120b7d8d218c3756195121be58e204427d65cc8109f58a548427f6508010af990310427f6588430cf550404423e6414c21be181424c2f960ccb40af580421027e6014d10d7d8d544867d62d45409f983530835e6154c219f59631d02fa600c420bd984208427e6395310cf95043c835f3254632af98b401027e6494630de5445050e7f6054c10de983548cb3e62550319fd9621103f14144010de94f408427f6510e20f698c400c27f65d0e10cf151424c27d65c8010bbd8941486fa60907409f583540c73f6454331b718d505067e61152309fd8954cc6f86048510de983540427c6454d219f18d5010afa60d5232afd9150cc76d5214b41cf551420427d64d4f10db94a200433d54908209f592520ca7e658ca40cf55040842bd60d0640de591509073e540c821d754c538867e6414a10cf99054086f960144329f58a53102f661d0310f34c8324c2f865481109f994438867e65d0b10ded42500877932940319f98a544c3775194530ded445050b784154031be98343d033c60550219f997434c67f6154242ee90d40102f960d0440be58241cc2f96588210d794d328827d6494d109f58754c827d65cc5409f597329077960d4c219f592510c77a52d4143d754c53c427c65484409f191500c67f6510c32af19120043ba54900409f596430867e62151109f582529067c650c520bd98642c867d6594c109fd9520083795014321be58232d037964540319f594420c6fb6050d30dd5445150e7e64d41329f98b548c36f5248110be98021903f161d01109f19432c43ea62d0320ded09500c6bd6408520be582410c27e6510c21bed81320427f6254e40af185435076d5214943cf553420c6f86148210be98341d033f6455231bd98630842b86448110cf581540c6fb6050510cf985540873f6550441ded9510042bd6414732f9484214427d658c620cf553500c6dd63d4242afd91208433c54d0521ee980421033e5410b21bb58a21086f86050a328f59053082be6414e21af592518c2bd640c421db94a429067e60149439fd8d509067d62d5131f3d8d320cb5d5314c21dd144314827c65080109f595319033c6155021cfd52404827e6294031cf981540867c60544329fd9732106bd64cc941cf952408c27e60d5121b798c210833c6295021db996324867e6295010de594400c3f34154241cf15242482f86050f209f98f5
  | 12 => 0x90220cf550544ca7f6454f219f987544cbba4210110de5405050a7d6115120bb98843cca7f6255230cf18954c427e6014f219f994414867d6294730bb18941883b86448110b798c42cc6f661cc1109fd85521027f658c440ce55250086ef6250721cf990548437a53103209f98e50d0b5e5310f209f185540cb7565d06419f59741086dd6390b319fd9530042f5610c0109f59631043e85248110bb988314873f6454d21ed55121086ed6214c10be983530867e6494732af990218433c54903309f99441cc2bd648cb419f98e520867e65905219f596420837a4394021ded50408427e658c941bb58843483ba64c4110bbd85210867e64d4c10be59440c83f120841109f59632d067c6550831f98cb214873f54545209fd95411026e6214c109f19643882fa6110110db988540c27f650c910d798c530873d65d0e439f99732482bd6090c40bd98443cc77b5094043de941200427f61551209fd89531077a5254031dd94721c827d62d41439f580534867e6510520cf95140c83b843100309f195404833d54948319f98753083b960d04408f992518827d60150319f990534833d53d0641db94b320c67e6494d108f59053c42f960d0e30d354b310c73c54d0620be18143086be6408640b718d41cc67e64d4d10cf953520c6bf6250842db148424c6f765504419f195418c2fa6090910cfd5243483796510320b798e420cabc62506408fd91534867f65485309f19532103f34084110cf550418c67c6590e21d7d5253086f561148439f58653d0a7f654c640db548320c67c6254c109fd9431c827f65c8730de943400427f6590d109f593524c27d6494010be98a40102f963c42109f9875350b3e6255021b7d8d544867f654c7409f98f525076e52908309f18d52c42be640c530cf95043cc6f461508319f590530876f52cc941afd95411033e548c831de5405050ef661150329f18d540427d64149319f59742c437960d5320b7d8d210c33d54d0a319f196325037960d53329f98054c876f6255121cfd51434c67c6550b319fd9540042f86050c31bb189514c2fa60d5231af185425076f6254d20f6103300c2f46150c21ee990408427e6214143d7d4e530867c6014d10d754f30c83786054d21b9185324877a5490040cf151314c33c6155310ced06509073e6055031d754c308827c658ca10cf99352c427d6015321d794f43d0aee6214730d314d32c877561d5321be980531073f6454910cf1525348377514c5309f58253886fb6050e329f58654486bf6550c43ee10c40cc37a43d4142be582418837b6550040bd984434876e528ca41be1815150a7c64543319f59532d02df6354121f54c431cc3d9324c030fad42204835e6314e10bdd91411075e6194c21dd952411073d5454031db94a500c67c65d0a109f59743843795014242bb98a43082
  | 13 => 0xcf150534823f6550c43be580414c36e6214c109f195428433f62d5130bb98831c873d6315120cf14d435067c6354740ed951310c67d6195332de95320482ec624c6209f189548c2bd6090840cfd84544c27d6494820be980325027d63d4910ee10940103765288421cf55020c42f66190e419fd8d511036c520c9109fd81548c77960d4f209f99741883e642484219f189538435f5394f40d794d32c425d63150219fd9732d02fb6050c329f590538873e65151309f988515035e538c4319f98b54cc2bd6490d41be181420cb7931540318f993530873c6195031bb588540c67c6155130cfd51414427d658c010cfd80544c35d5310c219f997321036e534cb219fd95328427f65d0910bb98b540c7b940102309f5825110e7d6550720af59021c435e6054c21ee50040cc2f9600c421be5805110f3f54901309e980514caed6214c41cf953500877b52942419f994214c27f64543319f98a544c73e43141439798c520435e53d0f209f995324427d6094f419f58a540c3775194532d7d92530867e6014910ee952500c6fb6055321d794d430833e5490832de18a500c77661d5310bed81324c27d63d5210dd54721c833d544cb109f988540c27f654c5409f99632443f161882109fd95428c27c6354440bd5845010f3d54d06109fd81520c67e6115020de98354086ed6290220eed8d40102f66190821cf152514c37b4394241d754e430827860551329f98653c837b50943329f58f540827d6508640dd98752043785294031db94b310c75f6354f109f997404c27c6154a40be983214436c5454831db94d324876c524c930db548320c27e6195320cf95052c42ed620c610af992524c27f658c620be181314c33c6095021cfd51414c7bb52500408fd91534427f6254c10d7989530867c6054b41d7cc9510cb7a6154031ee95340cc2fa60d0840be58041042be64d42329f18d54483794254031de58354c42f561080109f993524c2be64c42109fd9153042fa6010a309fd96218c37a60d4e209fd9442c437a6015030de58053442f960cc920cf151414427d62d51109f595320437a5494031cf990544435f5394e20bbd89544427d6590430b798c521027f6354620de58251d033f65553109f188544827e65109319fd9531082f86050c41de597409027f6510d109f58e510827c65509209f588538427d65109109f595404427e6590f10ddd4651cc36f6254d10bdd8543c873c54d0f31de58053c835d5314c209f595424caf561150209f99353c42ee62d0c42afd91308433d5450831f5ccb314c75e6315032bbd9520083ba5350040db14e324873e5490310db94b211027d65ccb40cf15142486ee6210d219f181518cabd64145329f996428435d6314b10be18143d067e63d5120cf551430867c65d0c20eed9540102ed620c640ee19130842ee62
  | 14 => 0x8941486f66110c3197d95300c25d6594c218f59052c425f654c832cf950320c6de63d5320d794e32c867e6195120cfd5330482de6310431bd185434c67c6550d309f586530835e5310f42dd94421c82be648c8409f58e544c67f6154f20d794c43086f66110b10de1485050f3954540319f58e528433c54d0d31b798c52906f86050640db948420c73e62d51309f98c54c42f96008410cfd52304836c52cc941b758c51082fb6050e40ed98743d06fa60906219f189500c6f96014e41db548525067a6015032cf55141cc27f6454732bb588400827e60d5021de94d304427f6550e10d794f32906f960907319fd8d544c7cd320ca40dd94e310c6b960108409f997329027d60d4d42ddd85544c76d5208410bb988311027e65d0120be181429037b53141429f18d500867e6494720dd984520435e5390c10db94a32c433f6455032cfd50424827f658c740b758c424c7d953540219fd9541cc27f6154032ce55040442f86050d42db549321027d654ca41cf95243c427e65d0c20cf551428c67c62550319f595410c36e4354831ded905050e7f654c521be181418427e654c940cf15032483e6528c431ce550408427d6590a10bb98831c83d561ccb31dd54451d0e5e63d5021cf550400c3e921940219f59432d027e6014c109fd95420ca7e6015121de547400835d5314d419f997214835e63153319f181540cb3d5450421de54050ccb5e504c0309f982528c6fa644c210ddd465150f6d52149409f994300827e65c8630bb9885110efa6390040bb58a300835c5350d409f99432103b94010030d798f54cc73c6355021de582544833f5490d30af5924210a3e64d4b10bed8142cc36e6215032de980520427d65507309f593538836c6054831bed81428c33d54940219fd9641042dd63d0330b758c52102be64d4332de58251d0afa6090020af59032506bd644cb419d584540cb5f5394f41d714d314867d65d0c32cf55221086bc6050941ded4250d0e7e62d5331bb98843c873d64d4f10be982430833d5490220cf55054482fb60508428fd954210b796094743cf54b411033c6095031de14f40082be63d04409f596430c7785394241bdd85524c27f6154c40bd987404436d5214b43db14a32502f46154d42cb548421036d524ca30fa901200827e60d4d42eed814310f5f534cb219f986520c2f963d01109b58853c42fa6090710de909500867e6515132ded50400833e54d0320dbd4a52d02f56190210b718d544427d6590410cf552408c2f96090521cf952430867e654c810b7d8d404c27f6454830db54a21c42fb6054543d754f43086ed65c86219f986528c2bf644c8409f98e50086fb6544010ed952411067e6590a31bd58632c867f6054443de547400c33d544c431af593520c6fa618c1109f587544caf961840109f990524427b654802
  | 15 => 0x827d62d5030cf952418c6f762484219f596431033e54100209f587548c27d62d4d41be58241c82fa608cb409f99731082be640c640ee950400827f6550b30e7d914310e7f6454d20d7d4f31486f66110f419f58e52102f66110c41bb189314867f654cb41be582210437b5094341de54050d0fad4210932be583548c67e6494d20d754d31842f962d02109f582534427e61151329f59053482ef6250e21af590530427d6315310d7d4e4350a7e6494832db54d210873e64d4f10cf950418c67e6314520edd8541102fb6050a20db58b538837b6548020af586421037843940319fd85530439f5390d43de545200827d6550f10af191208427960d4c219f994329027f6154343cf95032c437b64d41439fd8953907bb64482109f993514c33e54140219f993524c7ba64100309f992538433f6455332db948320c35d530c0209fd9630042f66188210bd58432c876d65cca329fd95410c37a6314142ee506401033f5450621ce90c5050e7f6054632de14a204427d6215031de54f5050afa6008730fa549500c6fa658c110bed81420c27e650ca41bed81438427d658c4409f996218c3ad5454831d7d4f324867d6014941af190321025e6315010be58e304427d6494a10be18143d0b755114530cf15240483bb4110020b798c5110b7a6588110bed81535067e6494c30af997425077a52881109f59352c435f5394d409f59351483b961500409f597300827d61d4d429fd96418c27960d50319f593504877551087209f98b540c36e52d0840f658c400c35d5394021bed8121482f661150309f99643c876d6215010cf553410c7775194420d754e41086f96090721de153204827d6095131af191300827e65d0730be982218c27e6094f41db551520c67e62d4f10ee50040882ee62105209fd9621d02796015031ddd4651483796214143bb98a310867f6354b409f996424427f65c8630dd94641902dd638c0309f596540c27c6454830cfd53424ca7d60d50329fd95310867e6294241cfd5030482bf644c841ee99040cc27f6054b419f995328436d5214a439f994418c27e65cc1109f59621d03cd320ca10fcd42104427d654ca40bed81534867f65100309f59631c833c544c930af99332102dd6308540be58032082ed62cc120be181434c67d61548109f19632042fb6048740bed81314427f65c87409f59430082f96008530af596431027c65cc520d754c53d067d6214131be99220443784294021de8c950086fa60086309f59642c427f6354442af191524c77862940219d584540c3756114e10cfd52544427f654c820cfd51418c3795294031ee504408427f6254c20bb98843c827c6254740cf55341c82fa6090541da94a500c7b95250040d794e4390b5d538c020d754f32882f5610cb319f18d544427d6294243de94610042f86050a10bb1
  | 16 => 0xf6454b10d794e300427e6294043de98e509067c6054642af59021442f66114c42cf950400c35f6454c21af9834210a7d62153309fd96418833e548c310af990210c3b95350040be98620443cd3294432de4c9500c6ed6294d40be58042d027e60d5030cf548429027e65904309fd91538433e54cc310d754d32c427d6215130b758c21482bf64cc440af592524c33d548c421bb588318c2bd640c420d794e410865f654c431db54942042dd6390931dbd92520c76e5450842cf151514c2ec6250c219fd9632042f860549439f980540867e6415020be98332843cf534c921f54c431c873d5490832d3d95320cb6d62d5332af59053c42fa6088620cf95042c43cd3214032de15210043776154d109f992500873e6395310be98251d0b7a6494021ded4d509067e6015010db548420c67c62552319f18d50d0b3f54951319fd95420c37954d0210bb98843d0aed638c9219f19732442bd64d4232cfd80544827f6155020de980514cb7b6055320be58321c836d5214910cf551320c67e650c120ee153304c27e65d05219f597420427d650ca419f58a534436d528c841dd987538867e65cc640db94b410c67e650cb109f592500c6de63085409f99621d036e534c8329f194420cb3f5410930db189544c74c524c9319f587538825e6314c21ddd9521087eb2194021de59740843775194740be990400c27f65087409f584548cb7661d50109f990530827e6094843de59620842bd6408740fc586308427f6154810cf990540c76c6394831cf553410c27f65cc4409f986508cb5c53cc120cf950400427f658c640b758c21d035c6094c21ded0e500c67c6254f419f98a50cc6fa6090631de90f5050e7f65c8640af990218c36e6215010d754f31c836d5214830cf95341cc2be6408730db94b420c6fa60084309f9865290e7d6395321ee985401027d61d49409f58e52903785248210bed8930842f96090d40de90c5050a7e6194c409f592530875f5394e419fd9731d033f5488120b798e410c6be62908409f582544873e54108219ed95401027f65904309f191538427d6550a30f390d320ca7f6154a439f98652d0e7e6294630cf553420c27d65d08329f58a534877b65482109fd8d544c3775194620bd58632087ae5448421e750c434c27c65105309f58a539073d6414532ae993108433c54d06309b988540c73c54105309f994415027e6315030bb98831086be640c610de14b408427d63153219f593504c7d6534c4319f98453c833d54900209f98251d0eed6214643af992514827d6114e20cf54f411027d6494620ddd8553486fa60d4a43f34ca500ca7d61940429f58f5150a7e6494c32cf151410437963542419f996418827f65106209f987544833e63d5120db94b500c6bd6510a40de94f400c2f96090440f694d50086f56114c20de55040
  | 17 => 0xb41de5475050af9600c420b718d414c67e64d4e109f99743842fb6050b32ded05509073d60d5120cf95341082be63d0040cf952430ca7c63547429f994324c73c54145309f58a531067d61942439fd94430867d6014e21bdd85434c73f6455030d794d32086f960d0c40cf18c544827f6355320af191514cafb6050921b798c424c7bb3150040b798e420c27e6415030af990218827d64942219f595428427d6510d209fd91520427d6194f209f98854c42fa6014a419fd97434867e65905209fd96410c75e538c832fa1814210bd9404c030dd59721887b654504419d584530827c65d0c10ded0950906f46155132cf550548833d5410f10de98e500875c538c5409f195434439d4310f30de15150086ee62140439f18954442f960cc9109fd8d52d06de6390a309fd91528c77a4194031d794c32c873e54d0b32edd0b41506f56108210af9834310efa6090510ee582429027f6590c31ba588400827d64d4c219fd9732d067e65d0d20cf95141c835f6354c20dd987540c67f6590420be980421027d6494f209f996314833c6454032de5875050e7a60d5021d758f54086ed6290421f61814310e7d6590e21cfd095190a7f65505209f594428c73e61d5120cf549411067c6454032be982318c27d6315220d794e308427d6510f21be582410867d6095120ded49100433d54540219f191510835f538c9419fd95430427e6315220cf15143cc73e5490c31cfd9154842ed6290e42eecc940103d661ccb31cf997435075e530c010de553404427e65105309f98b544427e6394321be582214c33f5410d21cf59741903ba6010c409f98853502bd64d4c21afd9150486fa600c540ee10c40c827e60d5131ded4e100433e540c310cfd51424cb3d5494f10be98042c83e43248421ee55340c83794394241cf15151482bd6190e409e98053043395410030bd584320c73d62950319f18d54842786055032be58d208433d6414810db94821042ed620c4309f197424c27f65506209fd815190f7551886209f98f514835c534c921cfd53304c27e6415010bb18931c867c6550720cf55043cc67e6015030ded8d500866d62d5330af99232d06f9608c9108f99053c427f6054a31bd584308436f52509419f99252087765450441afd91300c27d6494630db949500c6b860509419f596414c27d6510a30ee48540102be64ccb41db948410c6f66110a31bdd8d310c6f56110b21cf55352c42f8604c610ee191300c36d53c8421d794e500867f60548109f58c54886f261d0110dbd4a324c31d5310c40cf15243482ed620c730cf152424433d5390e40be983414437651484409f982538873f548c1309f180544433f54149309f59251cca7d6215310eed4d401033f6550c439f98a540c2f96090431bd58730c42bc644c8409f59731d03ae54c8421db98d520c67
  | 18 => 0xaf592219027e60d5031de58052c433d60d5130be98051ccb3e54d0430bdd85430867e650c5219f197215035d53cc420af59052c433d61151209f98653d0aec6250d42cfd53418c67e6550530be580218427f6254343be59740cc3ba4310110cf953420c27f654c0208f590514ca7d65d04309f594430427c64542219fd94319027e62d5231be181428c27f6508730f3109320ca7f63550209fd9152cc6f5618c931cf990538867d65948109f594428433f54cc5209bd9520082de63087409f592528c75f5394d10cfd5242443775194630db949310c73e5450b32be98031d036e6214c20be58021902ef6048020b7d9532cc6dd63106319f997434867d65cca109f19432842be6414c109f992508cb5f5394f20ee50440cc3b854d01109d584540827e658cb41db54a32c42fa60148319f1855090e7f6590720be181410c2f860508429dd95310c67d62d4e109fd89540c27d6590c30db98853c437a6014c10af99352c427c6154a30de583540c75c53cc6219f99642cc67d654c620bed81314c2fb6050610db148424427e6494f21ae19120842f86050b30db98852c427d63946409f595414c67c6114910be991300c3ba5454031de149500c67e6510a31be18141cc3786055321dbd81520c67e6510a309f590534867d6295010f34c8328c37921940219f18154486f960d4a43af18d401027f6055232f34c832cc3bb2150040cfd52424c65c63549109fd9431043755114742fc987404433e54d0721d754f31c86f86050c209f59543883786055032af99052042f66190d41cf55343c427d6094742cf18a54c433e54104109f584544caf965c4210bed8141902fb6050b319f595404c33e5450731decca500867c65105209f18153c867c6590520cfd95540c67d65d0a309f9875250f7a54540319f98c53082ee62d4031db94832cc7756114f21db949420c67e64d4d209f98b540c73e60950319f586540c33e5488310d654e500867e65cca10be98251d0e7e65d0a309f584534827d6294341db8c9510ca7f63552109fd95434427f6550e21bb58b4310b3f5448520bd984424433c6454321be58241107755114443bb58831883786294241b798c214827e64d4810cf990548c27f6550f10cf58d540873e54d0810af990411037954d03209f58654c82ed6214f10cfd82540c77b6214142d7d8d534836f53484219f99253c835f538c5209f184534427e650ca10fa8c120082f86050d32cfd53324837a54cc1309fd9632c43f25184010eed814210abf644c220be982318833d6414c21cf550548873e6355310cfd9154c827d60d4d21cf551420c35e530c210de0c950086f5610c821ded95308427e65d06309f98251ccaf960d50219f580548866f6254d109f98e548436e524c821be580438427e61940439f19530482f962c4210d3549310c7af625
  | 19 => 0x4210c33e50500409f99053883ba42900409f197315035e5350c21bd58442d072d54948319f59543c873d54d0c10dd945419027f654c620f34c8328837952d4143b7d8d515035e538c621de985509079f644c030ded8154cc6fa6090a10d754d410873e5150440de14d308427f6354042d794932cc67e6510a10cf950420ca7e6215330cf150304827e6095232de181521033d5490710cf98954c435e53d0c219f9845050b7a60d4c21d798f54c835d5390c10f594d210875d5454c21bdd8542cc75c53cc9209f181540c67f6548640be982429027e6395220be582314827c6454d10cfd4640502be640c6309f584504cb6d5250a41dbd4a52cc27e65cc620dec86500867d6548730af99031cc35d5350c21d794d439033d5490b30bd58442106be6210c40be982435033e54cc82197d8d544437942542419fd895110e7e63d4141bed81421027e6494e219f58054cc73f5495310be59740c827a6015021de58b5050fb96050440bed85401027d62d5130be181324833e5410831bb588308831e5454c21de553400c33d54908219f597319027c654c110af5864250afb60551219fd94320436d5294031eed9130443785210110f554d210867c6590d219f59253c427e65c8510ed50b415067c6055232bb18532486f9608c7409f58f5050b3d6510a409f5865310b7a5210110b718d544867e6514d10f64c030482f961c8220db14b424c6ed65d0a42cfd5321482df6354542bbd8940c827e61d4f209f99732503eb6248020ddd85544ca7f65509109f59431503795014141e7d52304c27c654c910f3d4a324cbcf634c921cf9085050b6f53c8421de540508867d6494430de580514c23d6494410be18132d037b60551219f98b530867d6294e40cf152304833c54cc120cfd9543d06fa600c910db54842d073d54503109b988540c3d963d0330bb58a310867e6215020d718d544873c5450d31cf592534827e6495132fc886500877a60944409f594430c2f56110821d754e43906dc63509329f99643082fb6050b21cf150424835e514c431bbd8e214876d6215221d7d8d544cb7b31940219f99732c42f76150921be58e208433c54d45309fd96434867d65d0f21bed81328c35f5390d40db94942043b941100309f58b548c6fa600c5209fd9443c867f65908319f59432d067f65d0f10be191304427e6550f21db54852106fb6050c30fc58440843755188440be181420c3776155121f34c8320c27e65d05209f99721102be64d42219f18d520427c6115110cf951438c73c54d0932f354b32cc67f6255121cfd88544827d61d49439f98353c867e65d0d40bed81438c37b62d41439fd89540827f6155010ee90c5050f7b5094232d754c53d0af860486109f98f54486dd63087109f995438827f650c821ee50040c83d5310c421eb98842902bc644c841
  | 20 => 0x877661d5021d7d4e539033f65500409fd94410435d5314f209f59353442ed6290c329f597400c2fa60cc830bd587328867e6394d108f191524433e54cc710de54050d076e524ca31cf988544c33c5450932dbd89528433f54506209f58254cc67e63944429fd96329036d52cc4319f987540c6ef6250420cf98554c43ba5410210be98221102f8604c630cf550430c67c62544439f58652902fa60c8610ded845050aec614cb21dd944411033d54d0310db949321027e6214543d754d43903784354031dbd4821503bb42500409f196424c33d5415030cf152204827e6414f20ebd0d4210a7e6115021cf151414c73e5450830eed8143507b651d0440cfd53314c27e65ccb40dd54631102bf6454d109f589540835d5494c219f59353483b65488421af58341102bf6250d419f58353086de6315020e750c43ccb5e6454c219f596428c75c6154c219fd9543882fa6014c21af590214c27e6114943be98332cc3cf634cb219fd8151d0e7e6494b10dd544510833e5490c43bed8132883b82150040f6cc6500c67e6510f21bd58643907795254241d694e500873e54d0e219fd96310433e6415330b798c21c43ba6410320cf10e501033c54d0d309f18d521076d5208010be98241042f66114c20be98021c827f650c8209f982544867e6215032dbd4f218876c5250941db949429027d63151219f99250cca7f6054742dd586534433f5448530de54c5050b3c5410d21cfd52540c27d62951319f5845350a7d6510f10eed5340443b831500409758c52042f661d0a21ce55150086ed620c521cf95121c42f7614ca21cf953310876c534cb219f19150ccb755114440cfd06501073f54cc930be980211027f60544429f98a53d076d524c8109f58a5190e7d6194d10bb98b43d0bb86448210b7d89320cb3d5454f10d794f32042f561cc1109f597214c27d650c640cf551520c7b963500409fd95430c67e6095032de90d500867d64947209fd9521d037952540319f18151d0efb6055032bd984531033d65908409f586548835d53884219f988530867d6550e10af990310c36d52cc8319fd94321067f658ca109f58a509073d6015120dbd95200833d5410820cf95332c42f661d0e31be984408427c6550f10ee993108427e650c6409f58251d0fba4210210cf950408c27f6548010afd8541106ee62106219f195420427d6550b109fd9152442dc6354520cf150434c33f5410120ded4250d0b9d5454c21bb189544c67c6550d31dbd4a52d067c65cc940d798c534427e6195230cfd53204827d6510b31cf951420427e6514d20bed8143882ed6215010dd94721082be6414a319f98e508867e63149419f987540833d6255031de5405010b3e5448421be18142883cd644c832dd544514caf76548421be592401035f530c941af590210427e60150319fd9
  | 21 => 0x6394421f64c030c42f96014a31bd185504cb795014021bb988310833c5410330cf58854483796114143bed95308435d63d52309e983540c6dd6314a41be982324426e62d5330be98050086f56110931cf55232087e92154021db949320c6ee658c921f3181320ca7f65908209f58754482f9600c940be58242502fb6050b41afd91504caf96010f30cfd5342483795114142d794e300c3766115032f394d320cb5d5310c429fd89548c73e5450841de58253482f960d0b40fc901100436d52cc8309fd94318827e65151209f58c528433d54d0c31be58043882de6310230d754d31c82de63100309f98254cca7c65505109f594434427d6494b10fcd85100435e53cc610cf152414c2de63d01309e58053887783194021cfd9154cc27d654c420be192204427e6494231bdd8520c42be6408440bb98b40482be6408720be98354cca7c65507309f191510ca7d6394b409f997424867e65d0a31cf95241886fb6050841af189411033f54085209758f540873f43544439f18d54c86ed62d07219f18d529073c6395021b758c51c82b863500409f58654482fa64480209fd9431d036e6494831be980434833f540c520db549210c37a5248020cf187544837b4354031c7952530867d6095110ee1814210a7f6590e209f59641882f96010c30fad49204425d63150109f59632d033f54c8530de54d100437b42d4142bb58831c873e54c8421ded8a500c75c5310d21d7d4e538427c6590f20b7d8d40cc3ba5250040cf952401035e5350421ded52500c7b86350040de94b400835e6314e20d754c53c86fb6144010b7586324cb756114a10be98630842f960106309f189544c77a5210030de94d30842fa600c7109f58e524427f6154843e7552530867f6510810d754e300433d53d04419f19152cc27e60d4c219e181544867e6510b30be98043d027960947429f5885050f3c5450130b7d8d42ccaec624c120b798e42cc63f65500409fd89544c35f534c5219f585530427c65d0b10af99053c43786114143cf550548c27c6154343f650d300c2fb60549319f597311035e5388421d798c540427f6550810be18940103765148620bed8142086fa60105209f980525076d5214b40cf99052c427d65100309f594318837a3294241bb98854042fa60144439fd9631082fb6048510be982414c2dd6315020d794d321076d5250a40cf552410433c52901409fd8d54c87bb4150040de540504867c654c640be983520c6ee6294d409f584548827e65100309f988520427f6454730be98041d02fa60d0d308f992544c33e5450610d794e320833d5448310bb98840082ed62144309fd95424c27e650c810cf550548427f6550b10cfd5040c82f9608c9309f191530867f6254f40ee108404436f528c9319f185508cb7661d4b10de983528437651d04409f58e540
  | 22 => 0x4219f1815390a7e6115332bdd85420c67d6508430d7d4e534827d6394620b798c521067c6590f10be58a304436f52949439f191520c67d6590f109fd8d520435d53540219f18553c82f96010910be59440cc2bf64c8640bed8143cc67e6214f10bd98632c875f534c1209e980540c67e63d5021db948200427e6094632de905500c6f860487309f994544c36f5250940db54b210c27f654c030b758c414c33d5450f109f196430433e54d08419f195318835c530c520cf54b419073c5448520cf95242c827f65900109fd94430c37b64540219f197414c33c54cc9209f59432502bd64cca409f594321027d6590c10be59740083794194031cf552430ca7e63d5310cf552410c6f96010620de994404436d5214a10ddd4641503775194742bed81410c27d6510530be580530867e6494030be580520c67e6590120cf553438cabc644c120db94932043b94250040bd586200427f6454f10be58021cc27c6454d209f185530837a53d0020f34c832486ec6250d32af997435067f61550329f98a5110f756115020af191514833d54d0e31cf151418c67d6015032de98251d0a7c6154b30be18142cc77a6254241be18132c435f5390d419f590504c7cd320cb31db54852c42f960086309f18d50d073e5490831b798c54086bd640c540ee550400837963d4142be58251d0f3e5494031af18143d067c6054a31be580315027e62d50209f996430436a5254031be98053907784194021cf95321c427d65108219e195304435d3254432cfd53414833c54d01309f584540c27f62542438f596540c7695294031be992208433d5494b10db98b530873d65d0240b758c214437842540219f9805150f5e534ca419f58a530427d6550f20af98743d067e62152319f98f54c86f963d02109f98c520437b4194021bb58831102df604c0309f987540427d6194a30be1814310f3f64550109f99732d067d62d5210cf95040c427f6550f21fc4c210443786214143ce9085050b3d5490f32d7d4e324427d6094d219f995215035f534c110d798a53086dc63501309fd95320c3775188520bb58831c82fb604c610cf95320c427c6550910dd946410c27d6115330eb508429077651084209f185548cb3e63950319fd9632d067e65c8640f54cb314c67e6414e10be983328837a538c1109f58c540876e50480209f994420c36c52485109f584540cabf644c320ddd4651d0f6e520cb309f596430cb7b4294021be58231c427d6394041cfd87544c37b61d41429fd9541042fb6050d219f5805150afa608c4409798c52c43ad4210940be98030442f86050b32cfd5041482fa600c621be58342482fb6050f32ee550404427d62d4141cf99054cc75d530c010de941300433f5410130db14b32442be640c620bbd89438caee620c220be18142486f7614ca318f590530867e
  | 23 => 0xfd91500cb5d6315231db14b20442796510030cf95342c427d6590841cfd50414c27f63550109f995434827f6055321bb587324caf86050d40db54b420c77751944429fd85534863d64d4f10ee90840cc27e6315010ced5040c82f96088630ee989401036d5210841de0ca509067e63d5110cfd53424c3796510020be5805210ef565d0641af59031d027f65d0a30de8c6500c67c6454a30be18142c83cd320c8409f98a50106f960905319fd96430427e6510d40cf953310c76d5210b40f34c832c827e65cc921cf550408c3bb6090c409f59731082f661cca21cfd50214c3795014031cf55141cc73d5490631bb58831087b951500409f58f54c867c6255030cf95021c42f96090d108f19153486fa6090b30cfd51424835d53cca21db952520c6f86050720cf550500c67e650c9409f189508c76e6214c219f59521d037b63d4142cfd9154c873e54d0421bd18530c42fa6010710d794c320827e6294640de186500c73e5414f10eb952520c67d6414530fad085050b3e51d06409f596530867e65907209f58054ccb7853d0140d714d304427f65d0b309f5805150e7c62553109f58c505067c62540419f99053c867e6510d41cf59251042b960d0440db54b500c67e6494831d7d4e534876e528ca309d185544cb3e54d08219f99250c867f6454c209f983544ca776550441b7597318c6dd6490c43be980204427c6454b31cf95031c435d6454c21d754c534873d5410220db14b214427d65109309f990540867d6194d219f58a511036e62d4f209f194400c35c53d0d219f98b530427f65cc9109fd95434867d6590930bed8143c87ad4210920de54440c833c54cc520bb58b41486796094743be582410836d524ca419f594320873c52d09419f9835150f7b5410110e754e439027e64145309f596400836f5294b319f59532103ad4210b40be588404427d6550521be9945050b5e530c4109f98e51d03ea52480209f58b535036d5214840cf990540c27d6494432d798f54cc33f6455130dbd48324427f654c832b758f5008775518c630e794e439027e6294c41dd544518c27c654cb41fac85500867d6588420af99054086f86050b219f584548c27e6508730dd984530427c65c8530cfd52544cabe640c521f3151320cbb93150040cf953320c73c5490d10fad0320082f86048430db0c5520c73d5415021ded81544cb3f5495020ded8154442ee6214c109fd9532d027f63547429f596410873f54d4d20d754e31087eb42d4142cf950310867e6115220de4c950906f96008430be191200836c6094831cfd52548867d65d0b31bed8141cc2be6414c20af191504c73f540c5309f99632906bf644c640ee582439027f6054f429f997314c27e6494410dd945311026d62150319f997424827d64141329f997424427f65484209f98e520835e538c
  | 24 => 0x318875d53cc8109f195314833f60d5120db949210c2f76148110cf50650102be6414632cf587544827c6510e10bd58643506bf6350941be594408436d5214a419fd9731c837b5284010de149509067d65d0c21dd984540867f6590f21be181420c6f56110010dd547310c27f61549109f18d52d037851141439f19732507e821480209f19741482df6350630cf550420caed62900209f9825390a7f6255120dd945310827e6314c219f994214837a60d4e10af590500867d6254c20bbd8953443795410330d754c318875f530c910ee10c400827d6590931be58b40c837951d0330dbd95320ca7e6494830af590500cbcd32540329f5875050b755114632be980420836c52885309f58f544879d54cc4319f59051482ed62d5031f6cc5500c67e65d0a10de9475050f7951d41439f597428436d5254031cf15141886bd64086109f58e54882fb604c8409fd95430c2df63541419f996315027e6315110f3191320cb3e6415032ded0c5050f3e54107108f59251882f66114042e750c43107bb54c8120db94a321063e6494630db548529027d65c84109f592500c2de63146429f997329067e65cc520cf58b544c27c61553329f18d52902fa6188210ded885050ef9600c5209f595321077931940219f98f540c3bb6050b41cf990544c33e5410421bd185429067d65d09109f98b514c37a6014a10bed8143c82f9608ca10af98342d075f5394c40be983418435e5354021cf153214835c538c910cf55350086ec6250420db54b42d067d6094a31af99031c875d534c420cf550320867f65d0d209f180524439d4310f42cf55043c82be6090541be181218833d64d4c21bd185328876f5294940be98740442f46150e41cfd8e54c427f65d0a10bb588430ca7e6314940dd945318c33d54507109fd89510c2bf64545309f98a50d077551484309f59743c827e65100209f99731442bd65d0a42cf55221c427d6414810ee908400c27d6294231cfd5141486bd6414430eed4240502f86050e41cf55143042ee6290020d79514310ebe60d0d41de94a208433f544c5209f99421d035f534c9219f592500827e6494b31bed81514ca7e6115232ced9540102bd64086409f995424c67d6590832bd597318c73d5415332cf95341c437b5094331d754d31c867d650c910be983314433d52d06409f98e5090abe61d0b41db548410c67e65101308f19150cc6bd640c520b798c52043b941103209f583544876e52cc8309fd95420867d65cc520f68c5300c36d52d04319f992518ca7f6550120dd5445190efb6050c40cfd53414c36e62d5020de545300c33e6415131db54a208433c6454d21f654e30842f960086209f19443c82f9600c740be583210827d62d53319f58a544c2fa6090830de50a50086f960d53329fd8d51d02fb60509319f1855090ade6308510a
  | 25 => 0x35d538c8219f987540cbbb54103309f196420427e63152109f98e501063d6414e21bed8143d067e6094c41decc9500875f654c030dbd8952442dc63549109f5973290374518c530de94d300c27d6510430f64c6500c67d6094643d794f431067e6415031cf152424c67d65ccb10cf551430c6fb604c630cfd51424c2fa608c9309f997324c67e6194c20cf184544827d658c430cf95142c427f65d0b10ddd4651c827d6494632be58341d027c654cb409fd9153886f860508419f595304433e6414810f34cb510cb7b50942319f592538433d548c710db14b42442dd6310030cfd52514c27d6314542cf550430c33e53d0f41bed8143d0b6d5250831cf55141c86f960cca10cf95353c433c540c520be983321033d6395021cf152214c3795014132d794f4310afa600c510cf95043cc2f56110f31be181434827c60548439f58e51d0af96010c40be58f400c27e650c421be58c404426e62d5031db149324c76f5294a10cf55243cc3756194910ded085050b7950142319f595324427d6394321cf18b544c35e534c320be580514ca7d61d5330f3d09320ca7a60d4c21de18d500867f6254c409fd95310c77960150219f997434c35e53cc840d794e32c827d65d00209f98354cc76d52149309f586534827d654c440db94b210c27c6454e21f6d8d304427f658c0209f596310867e6495120bb588540c27d65908319f99431502f8648c110bb18940c827d6215231b7d8d410c27e6194f40ebd5220482796015032bb58b43d0af66190010de589500c67f65504319f597438867f6054432b758c210433d64d4b109f986534833d5310c409f59732102f86050f40de14f40c827e6195032be181420877960d5021cf18d54c433a5494031f34c832086be64144329f982544cab86050f419fd8d50c87b85350040dbd95520c79f6350f41d7d8d53882f963d0330d754e42086f96088620cf951420875e5310c42cf150424436d524ca31d794f311035d534ca208f99353c427c6254331af98c429033c5250941cf150404827f6548540ded81544c33d5410020de980540437551d0740cf15320483ad52d0b41dd54441d02f66190a41d794c43106f96014e219f588534434c534c921be582424427d6494231ded875050ef6618c821cf55342882dd6310230eb50d4210af6610cb319f191530827d65ccb419f59632906be640c4409f997410c2ec624c4209b189544435e6314e21cfd5243442bc6350640ded935050afb6050c31afd9542d077b54d0030de14f404427f6054f41af19130c427e60947429fd9741883b6548c431bb189515027d6294043de597400c27e65909319f59621902be640c720cf94d4310e7c658c540dbd8954442fb6054542d7d4f32502dc63545429f593504ca7e6094c42bd58443486fa6090640bdd8530c42dd63d5320d714d
  | 26 => 0x394241bd1855250f3c54105209fd9643086de6308410eed9130843e942480209fd8950107b940100209fd97438867d650c410bb988539067e6590e209f98c54c86f960146329fd95424caed6214031db94b32cc67e65d0d429f992510cb3e64151329f997430873e54d0e32f9949210867d6414f219f99353c8379539402197d8d524435e524c832cf54f41903765150430db94842cc37a52d0240cf953420c67d6550b31d754c531067e6294f40d7181530867c6550830cfd9542d06bd64c4110cf99251882fb60509329ed8154c873d60953109fd855010ff22154021de980530867c6354910d7d9532cc65f63551219fd96310867c6154e42b798e424c73f5410931af586431027d63947409758c540835e53908219f58252443765188430cfd52438c2f761503109fd89548427c6154b439f583540877b62d41429f98e5190b3c54d0520be980328427f6054a43be191308427f654cb10f6d03300c37561d4f21bd587424877a61141429f58f52042f960104409f59053882be640c4219f1855290f7b3154021af59031c42bf644ca41dbd0e520c73f6455031ded51500c77661150309fd8554c83b564c40109f58a51d0f7551c84209fd9440043ba5494021bb98b314873e544c710cf150214833e54d40319f592510837a4394241ee90e401027d65d0620cf550540427e64150329fd95414c27e65c8730be18152506f9600c710cfd53434cabd6010e40e750c4350b3e5410f329fd815190b7a658c110eb508428873d5454b109f994314c35e53cc721be980329033c54d09209f98e51882f860553219fd89508c758534c110cf951310867d658c420d794e430825e6315020d7982530876d5214a319f58854842ee62d0d32af59352cc27c6155120cf55054442f6610cb21af58f425067d6590b319f194310867c6354a109fd91508c6be64d4f20dbd4932503755114732bb98a41087ba4310210cf153524c27e6414532be59740903796094d109f982539067d6510b10dd544518836d524c431cf952404433c5450530e798c439027d6115020cfd51314c33e6415310db549218427d6588630f9cc5210867f6590a109f584525027d65d0b309fd9543106f9638c030cf55243087b93250040bed8143086de63150109fd97310836e62153219f980535067f6454630bd185328c77b54d03209f996428c2f7614c8109fd95320c6766114c209f59654083766115231de48550086f960cc510f9cc9210875c530c910b798c52c42dd6308530af990540c73d62d5120be18142d073f54951219f594434867d62951109f99740442f8604c720be18131103ba6090e40de952500875c63551109f982510cb794354031cf50d5110e7d6294031cfd5242882fb6050c419fd9732043f13194031b7597328cb5e538c710db10e520c73d54503209f98e5210
  | 27 => 0x209f98054cc6bd64087309f59352042de6394940be181211033e54d0c209f594310875d6094c219f58a544867e63d4a109f994410833d54108219fd9531042f56110c319f592500cb3e5454c21cf990548c6f960084409f195424c67f65084409f59421cc27d63d4b109f58a519027a60947429f195315027d6214d409f592528c2746154d209fd9643082f96008720be9805190a7e6014c21db94a410c73854c81209f59250cc63e6494d209f98e500837852d4143be980310437a5210330cf590530827c654c921bb98b31c877a6094630d754c310435c6194c21be983424827d6194342cf55042cc27d65085409f191518c27f65884109f59252cc7775194642af59353c435d63d5231bbd954210b5953540218fd91534827e60150208f59352c427c6255210bd584540caf6618c931afd9120082bc6050842af191504ca7e63d45429f58f548833e6195021afd81419035e538c821dd146214827f6354342cf19153442be6414430bb98a4390afb6050720cf951500c7794214142b798c214c3cd320cb41cfd8154c427d658cb109fd94328437a4294031f3d4932cc67e61d4143db94b20c43ba60905419fd96428c67e65cc7409f983538867d64d4532af98e431027d658c840de951100436952540319b98853086fb6050820db58b538867d6494910bd984320c67d6315210cb551520c6ee620c540de4ca500867f654c940f948421c833d5450431de94c40443786254241cf55340c83cd424c832cf55054cc67c6054c42de5875050af96010930f34cb500cb786354241d758c540867e65d09409fd94438867e6510d209f597420867e65cc941bd58630043775150540db98852843794154031db98b540cafa6010d10eb551210873d5414021d694d500876e5148421cf152314c27d6550d219f997414c67c6054643dbd4a5290ef9600c6219f59521102fa6090110db54b218427c6154c42be9825350b3c5454930dbd4a5210778538c2109f18d518827c6550c10cf151434c37b54d0210af99032d067e65084309f593538867c6254743dd54451d0375510c4309f987525037b21540219f98e540433d54d04209fd815488777518c530cfd52548827d6414910d714e435033f544c920d758c540427f6054d21db988540877a53d03209fd8154cca7e62d50109f98e52c42ba60905419f58652cc2fa6090d109f59442043b84150040af590318867d62952319f194438833c54505219f99642c433e5410431de1875050e7f6255010b7d8d54442f46148310cfd8f54482f76154d42cf551438cb3f5495120d754c53d033f5410910db148215033e5450e219f58f54c433e54d0431eed89401027e650c520cf551428833d6015130bd58620842ed6290e20e7d4d43506f76150e41bd185304435e534c610cf551438c67e65508109f992538837b6
  | 28 => 0x18954cc2f8604c9309f997324427f6154a40de1845050b7561d4a10d794c300836e5208710f34c832c873e5490f209e99740442f962880209f99441086f86050d419f597430433f6255310d75974390eef634c832de54e100437a3154031db991520c6fa6090630de0c5500867d62d5010cf95340cc2bf6150040b7d8d41cc6bf640ca40bd58443d06fa6090730db58854ccb3e544c821d754c43c833c544c520de94f409036e52140319fd9632087f341942419f984525036d520cb30db94a20843f260904419f982534867d63940429f1855010f7561d52109b189544c6de63d0330dbd89544c63d64d4c219f596321067d6590810cfd89540c73d548c4319f58c520433e5450831be181438877a60d5230be58332cc27e65086309fd9643c43b54110540de94e30842fa6410020eb55321086ef6254530cf95140cc27f6550c21cf150438c2bd6408630b7d95320ca7f6355021cf152524c2bc64cc6409f583548ca7d65085309fd855390b7960d5330f90c5210873e6515120cf151424823e6414c209f98e54086df6354520cf95343042fb6048610d715153086bd6390541ee10840843b86050f41d794e300827e62d53109f98f548867f6154232ded53400827e6590830be582310427c6354241eed45401027d6510e21bd185435076d52508309f18950907775194440ded4a500c67d6550d10be983438c2d963100309ed95300c37a6014c209f19531c836e52884219fd8d548827c6315130eed04404427f65d0c21cf952520c67e65d0930ddd95411067f6550841d7d4c434867e6294f10af191304433c5450620cf99054c837a5210210db94942907784294241be18132042fa600c5309f994418827d60946429f19542c435d53cc840ded89500c67e65cc720af191524436d6294d20de8ca500c6de63d07319f9825290e7d6114143d758c548c27d6094c42f34c8324c6f7614c110dbd48424c7784354241eb988421027d60951309798f54c835f63551309f9805150af9600c910de59440cc33e5410c30dd54421083d9300c010db982520c7b84290040b7d954310f7953942419fd85534427d650cb10d798c530827e6194042ded0d50906fa6008420ee990400827f6510a319f990504c76c64548319f584530827d6550831af592211027d60145329f195329027f63551109f98854cc67e64d4532cfd5351482f9608ca30bed81434c75e530cb20be98342d027f6354a109f196434827c6550c20ce550400837651cc730cf18d540c6be644cb419f996210c27f60550219f582548867e6114d20cfd91544427c6255010af58442902f561d0f41af99051ccb6f5210910be181424c73c54d4d20de9945050f5f530c5409f996414427e6394410bd587431067e6510510ded445050ef86050f109f98754ccadd6390431bd984320867e650c4
  | 29 => 0x2482fa6010410ded05500867d6055010db98b540c6ef624c620d798c53c867c6154830bed815350bba43103309f191528427c61548409f988544c2f46150a21af59332103ae5290a40be59740842bd640c510ded0950087ae54908429f994404835d53d4021b758c219027f6510430eb15220483cf614c8329f19531082f8654c1109f5964310af96014a41bd185438c6f661909419fd8154482bd64c40109f99353c867d6315010de10550086f66190210ded42504c67d6590e20cf59052c43786055131b758c218433f5450d329f58053c879d4310d32bdd8540442fa60c87209f189511027c6054a419f58754ccaec6250721af5974390e3c6454032bd984521027e6510d21be58031c873f6550440af59350ccaf960905409f595430827e6510c208f19150c867f6155110cf952410427e61950209f58f548867d6590630dd987548873d5415032d754f43c827d63151109f996434c35d63d5320de949509067e6588510cfd8e54087766114e21cfd82540875d5350e429f98a524435f53cc110d754c32086f96094d428fd9150cc76e6215020ded4e500873e5490f319fd815210ebf6454d20bb588310833e5408310be98232843796094441bb988434827e63141419f99432d067d63d4121d758c540827e6414d21cf95253086f46154d20cf59443902bd64086209f99620443f36148110de181548427c654c940fc8c210442be6494d20de942300427d6094e419fd95204433d5450610f5d85324c67f6154830de14e50087745190540b758e320ca7e65d0830cf55242c427e61d4e209f59353842dc63503309e583540867e6114c109f58b540c7782154021dd98454886bd64d4f20d794d320427c6454f10be58221102ef64508429f996324863d6494630afd9130082ed6210720db14942502fb6548210de983548437965d0020d7d4f434867d61d4d20d794f320c73e544cb109f58a544cabd6494520ee55040842ed62d0320de980538437b5494021ddd46510ca7d60151319f984538827f65d0f21db19532486f56110210af99353c42f960cc830dbd4a52507b764504419f592510867d6508440edd46415067f6550a10bb5884310aee620c520d714d4350b796254241af590210c36d62d53309f59731c83b854c8120de549100427d6590720cf99054486f9608c530cf153434ca7e6294e409fd8d540c27e60d4931bb98831d035d538c7109f19443082bd6490040ee18142d06f86488210cfd51324c27e6414132d7d8153086f461509419f195324827e6494c10ee90840c835d53cc4409f19642442ed6290f32d798c54082be64084209f586500caec6254131be9805310a7c6510a109f594418827c65d0c21be98242c83796094910be982410c27f65d04209f19541082ed6290d21db98b53c86dd63d07319f59251cc35c534c9209f
  | 30 => 0xf86050932cfd8a54c436d4394831ed545419037b5094121cf95042c82f860550329f58e510427d6395120ed59310842f66110f109f593514c27e6414e21f34cb314875c53cc110fc882104427d64d4910be582439035e534c310d754d328867c65d0d21de540508cb6d5288410b758c520427c6155132be18141083d6414c4319f58c525033d5490b21db58b54886fb63c41109f99052c427f6550441d7d8d544c76f62551329f58a54c433f5494520de94220042fa600c8309f98a540c6ed620c020bb588410877a53940219fd9541c827e6395110af58b43d076e5248610cf9524084375514c420cfd51514c35f5394d41cf950530867e60d48109f984544435d5310f40be588408435e534c440cf55342886f46148110f3d8932cc6f960905209f996324827e60948319e980530877954d00209f592530cb786394021ee98141102f96014643dd98453c427d64141219f19521502f76155132af59051082f8644c030afd81401027d60d49319f99643487796095110eed53304c26f654c832db94e32c867c6254d109f594210435f53cc120bdd85328433f5495021be980414c27e658c6409f194214c2f96010a109f196414c27d6094e42de58054c437b52542419f994438827c6510931ae1814210a7e6314b10ce951500c67c6550e20db94921cc27c65504309f994321067f6590b109f185540c27f654ca409f98052042bf64543219f59743082fa6014a31bd58742107796015031de983548c7bb4154241cf55130c427d6014d429f58e50907db6050c43fa4c9200827d6590520d7d8d534877950142419fd91518cbba4310030cf55232c427d6195132de997404427e62d5021cf550418867e6550d219f98e548876e538c921af189401027f6154b409f582540c6f9628c2109f99741083b843500409f595314867d64d49319f596325076e62d5320bb588531036e52ccb30d794c320867f6590810db98853c86fa600cb309f58e521073e54d4c21dd94431cc33e5350f419f59353c82f661c8310be181438c6dd6310730bb58a43c879d544c431af992319035c5350d41de192500c77854cc1309b98853c42f561d0d319f18950d0e7e6314a109f596410c6f960144429f982548873e54d0c419f987548c2f561c8310af590500c76e5250830cf550410c7b54110740be583328827e6215131f64c5500c67e6014e219f99643c834d32544329dd95100427d6294740cf54941102f4614c8109f58c524437b6054910d715253086bd64d4231be9825150a7f65cc840f954a310c6ef624c3209f59443086be6414720cf90a501027e6194e20af59132506fa60906209ed81534867e6494221af590520c37a63540319f98652903794394031ded05500c67d63d50219f590530437863940319f189531027965840109f58e500867e63153209f9943
  | 31 => 0x14831afd9321102fa6090521bb988520c7ae5454831ee90f5050e7f65d0831ded425090ef66110e219f98f50486dd63150109f996420c6df63508319f195434cb3d54cc821b718d420c76e6154831decca509073f54145309f98454cc27d6014931be98042d036e5210841bed81420c67f6510b30f34c8320c63c6454d10db949329067f64542329f98a54c435f6354f21d794d31c876d5210b30b758f424cb6e52c87309f98654ccbaf6450842be98740842f960d05109f58e50d0a7e63d5020bd58630842dd6314642de980548c33c544c920de10e500867d60548109f181540873f62950319dd95210873d5450a21cf990544827f6054e21db988540c6df63549419f98e51c82bb61500409f997434427e6114d409fd85544c27f6155332ded0f5050a7e64d49109fd85530835d53d0f40f950921087796014e21cf55342cca7e6510010cf990540827e6315120bdd8543507ce52cc431af59352c435e5350e419f992544437b6054d21de58053086ee62144309f98f548827c65d0d209fd96410867d65950329f994219027d6510421bb98831c42bc6050c439f59521902be64d40219f996414c36d528c8409fd94438427e65909209fd81544875e63153329f988530827d6494b309fd9421902be64d42319f994424ca7e6588440cf551210877b6454031ee181419027d6214c109f99442507794254021dd949210867f6055010de98253842f561140329f19742042bd6414730af191300433e5490441ed58742d06fa60cc610cf952408836f52485109f596214c2ee628c621db54b20c437960153309f98e534873f5410d20d798c52042dc6350a31d794f50087795014331db94842d06f86055331be18143443b941100209f595438867c650c0109f196324433d63d51309f98e528437b5094221bed81430837a6494031b798c218436f52cc910af191329077843d4142db54a328c27c6054e41ae191304433c6215130de953208833e5450e329f594418c36c6494831be992304427d65108209f594410c7796015320f594e310c67d6014c21c7551530876f52085309f18953d02fb604c440fc4c5500c6f864c4110eb54a42903cd320c820be594400835e6494c21dbd95210875f5394c209f58a518c27d6590d20db548520c77b5094241be58243842de6308640bb98a430cb7b6114143bed8131c827c6354642cfd52540435d5390c219f98252907db43d4143db14a324c3bb644c030cf951310c67d61d4f20cf152424c27e6550520af590538876d52d08419f996420427d6214543f3d95320cafb6050d32ed551310c6fb63481109f58e51103783294031db951520c73c63d5120ded905050b79518c030db54b42d03bb43500409f58353c876d52149319fd94420c2796014532de1875050a7f65cca41af993520c73d54507209fd9431102
  | 32 => 0x9fd91510ca7e60152319f9865310b6c534c921d794f30c836d5208710d754c500867c65486309f58e500427d6194c409fd97430433e54d4b109f587548827d650c520ee580421035d65cc230af98b419037951880209f58254ccaf9600c410de181540837b62942419fd94424427d61953309f597420827e6414c10af590310427f6510831cf953438c71d5494c21de181544cb5c53cc940cf95143042ed62d0d329fd9642086ef624c5219f994404436f5294a31ded42504ca7f65d0630f354d210876f52c85109f982544c67e63d48109f19642c433f54d0621bb588434867d60d51319fd8d508873c54d0510ed50441c42fb60484309f19440083ad4210a329f983540cb5d6395131d794e43086bd64ccb419f18152cc6f8648c210be58c40843785310210bb58843ccb3d54c8421dd94441d02bc6150b41db591520c67b6055131cfd5341042be64145329f59353c867d654c7409f99542c427b60551209fd8950cc6fb6050940d794f31083f2618c2109f987540867c6054841cb149425076e62d5321db14932503da404c0309f990524c67e6194343be582429027c65108109f59253482f66114043cf153514833f6455020f6d4d30442f96090a10db597218867d6550420bbd89544c67e6510d319fd9152843cf524c9319f990520427d6194e42afd954210b7a4254031cf552420c67e6214131de983540c7eb62481109f99632d027f6454321bb189544436e5250431cf551410c3e532c8521af990310837b5410330af992518827c65885409f58854cc67e6114132de50d509075e5390e40bd984300427c6548740d798f540c6f56114c429f594420c3e5618cb21bb98a30883ba4150040cf95143083785494031ded0e500875c53ccb21bb988318867c650c810bb98b30c827f62547409f19543c82bd640cb41af593508867d6194332cfd84544827e62d5131b758c5110b3e5450730bb18950506bf65504419f19151cc33f54903309f992530827d65884308fd91524427c6354321b7d85310c6f960d0f409f980548ca7d650c420dbd52520c77960d51109f587544c27e60950319fd9153087b554884219f59441482fb60487309f98a53907b543d0541f3981320ca7d65d0730afd9131102ec6254543cf953438c3b954d0330cf951320c73e61950319f580544ca7e65c8430cf185540c7db634c210be58b40082f9658c210e750c430c67e62d4141de98a509073f5495321be980319033f54d0d20de4c5500877661d4c21cf54d411036c61548319f983530427c6550a31f34cb31c87796014532cd945419033c5450630ee10840cc27d61d5030ded8e50086bc6448020af18543d076c6194831cf553310873d3015130cf152324c2b96490040ed185425076e52c8610de5405010e7d6395310cf59741907bb6448020eed85401033d54
  | 33 => 0x85320caf965c8220ded49500c67d65100209798c54086be6390a40db94a310c6f76154132bb58843c86bf64545209f58b548c37651904209f997434cadd6308430bd586328c6f86055131db5485210f7852d01109fd89544c6f96090541bb189438877761549109f99543442fa6090720bbd8940483af6250941be58241887796510210d7d4f314437a60150329f996434433e54504209f98f525027d65d0830de94b40443d8534c1109f98f5050ade63d05319f19542cc2f66114843f3185320cb5d534c810d754c5390aed62906219f196428433e54d0c219fd95310c2df654c030cf506501067e63d49109f98354cca7d6194840be181534873f54d0b21de195304427d63d4a109f98a54cc7b964c4110cf15242883786394241bb189535075d534c3109f59542cc27d6114f20ee500404833d5490a329f99353486f661c81109f997414c3756194d21b758c218c37a4194021bb58851102ee620c9219f98652d02ed6288020db98b540876c6254d10d794d32103e962d03209f59440042fb6048620cf95043c435f6550c43cf553520c67d6588410af587409027d6294010db58a544ca7e64145209fd9432102f561c8110d7d8d538876d64948319f597428c6f960cc6109f597310877a3254031db54832cc7d4614c931d7d4f324827c6454620d754f321067d6194b439f195434867d61949109f58e54042bd640c5309f984530827f6550130be181310836e538c832cf151434ca7d6510c32cf552320c67d63947209f18d5090afa60d04409f181548c67f6354420be582321036c4354831ee95140102f96190040db98b54cc27d65d0c31be58232c837651d0740de58e500867d6095232b758c21cc33f5490520cfd53514c2fa60085409e980520427d63d4141cfd50434c27e6515110ded42505075d5390e40cfd50514833f5450f31de951500867e6215230cf95253c42f56110c41af59021102bd6408720be99310442be64140219f982521067f6548410dbd4b204427d6494d21bd58432c435d5310821db94a210437a60150219f18151ccabc644c640f34c832106fa6090721bd592411073e6395021be982328c27661150309f59721cc37561d5331bed8154cc7b86250040bb98830082f96094542ae189401027d6195032bb58b5090e7f6154e20de18154cc73f54d0f31bd58a210876d5214b31cf55032c435e6315030bbd8931c86bc64c86409f58653d027f654ca41b798c418c67e6510b31bd18540c42be64140319f996430863e6515120f3951320caf76150e31be98241cc77661d5231bed8142907da63d03309f586520c27f6154a308f191534833f5450120af993325077853542419f98a5190f7a6015020cfd91544c6be648c9419f98a510427e6515131bb58851cc37a538c0309e98053886dd65cc230cf95043086f9609071
  | 34 => 0x8cab86448020db5974290b6f4354831de14d30442de63086309f58f540433f5450631cfd51404c2ee62d0521bb98831442ed6290d42b798c21cc27f6454032be98021d027f6154b43be982410c67e650c1109f18d540867d6295120ded92500875c6354910fc185204437a50100109f195424867c63544209f5835150ede63d0b329fd9721102df6350531cf08554087b85410320cfd91548cadd6308620f314932cc67f6054f219f596421035e5310821de540504c67f6550820bbd95210876e528c821fc102104427d60d4e219f18151d0a7c60544429f58a501067c62546409f586548cabd6494530af990215027d62d4131bd58442c437960951309fd95428c6be65151209f595428c67c650c941af19153482f96090f309f98452443b852500409f983535077852882109fd8950d06f96094943b798e408c2f561909419f595418835f6354f209f181538879e5450c43b798c324c63e6415021ee983411027f65484409f19150086f561908219758c52c427e61d4132cf150324c35e63d53329fd81534827e6510c10ddd46510c2fa6090e10be983431027d654c720bb58843c827f6510b31de552500c7b95494031b758f414c67c65506209f98a54442dd6310930bb988511027c6510b10cfd5340482fb6450040bd185328436e524cb10d754d31102f86050c10dd58453082b86050c43b798e418c6dd6310a329f58a5110f7b50942429f98c540833f54d05109f19632506bd648c9419f994434ca7d6550630cfd87544827c6550e21dd98454c43b743d0541bed8d300c35d5310c419f596430833d540c421f54c431c425c6355121bdd85429067e60d5232de9875050f5e5314021afd91534867e62947439f99721d02f86050e42bed81424827b6055121bd584540c27e6548530afd91219037a51d4142bd98443443ce5348421f5d46314c67e65c8540be982439027d6214141f550d310c77a4394031af98c42102fa6448110cf55052c433e6494630b7d8d52442bc63504409f98a511033d5415321de951401036e52d0b30cf95141c87755148620ee108400c2bd64c4210d7d4d325033f5410a209f984540c73d5490310bb98853c427f650c020de1475050af5610c941cf95343c427d61942429e580530877852481109fd96320833f54d0531ebd49425067d6355030ee95150086f96010a309f992510c33f6454d20cf950520c6f961cc1309f596540877565c4210cf150424c67d6494c309f994410c77965d0320dd18553482f66110b21af59241103745150540d754c538837953540219f59741483cd53c84219fd81544c2f960cc840cfd53434c35d534ca419f59441cc27d658c8219f99431883da434c030de949204427f6155131de98d500877565c4010db98b530837960d5231af596421037b51d0140de94c40843bb6090840f39
  | 35 => 0x66190f31cf150434827d62150309f580535073f54d0630af590528c67c65ccb10cf54c439037b4314142af9834390ef5610ca41e750c43907cf434c8329f596320c37a5394241cf984544c33e64152219f993514827f658ca41af99221903bb4110210af990425067e6510d10b798e400c27c60552219f980524c67d658c020be983310c3bb4190040ded06509067e63d50109f59250c86bc644c210cf55243c427c6550130be9824110779658c210f3991320ca7f6590d209f98e52d067d61d4c209f194430436e6214f20cf951520c77963942419f5845050b5d6395130d714c315035e538c220f6d42304c27d6215131cf95250086fa600c730de94b400c27d6414d10cf15240c827c6510010de90a509067d6414c209f59250ccb3d54152319f99432d027c6354720bb588315039d4310d40de98353082de63084309f596428c2fb6388110bd58642c867f6354242be580210833f5450b219f58f51503775194542de94d50086f9600ca10de10a500c7ce53c8421cf99054882dd6390230ded0a50906be6414730db98854c833c5490130af590510cb7a52141439f98b5050e7d6590f20de94d509067c6255130cb952520c6bd65d0240be98032c827f65d0d10cf187544c27d6395110de18650906fb6550040decc9509077551cc730be58032903766114c21dbd4b424c77751944439f582531073d54900109f580548c67e6394440bb58a318867d6590d109f58650d0f3e54907109f594321073e6414532eed81419027e6510f209f98a510c36d5248730ee50d401027c6454e209f58353506fa60904219fd8953483d5414c431db54b32cc37852d0140cf950404435e53cca21db54a410c67c6154b40cfd52434873d52908409f59632042ed62d5330ee90c40c833c5494520cf55041087b46150d41cf55341086fb6050c43bb588501067e65107209f59532d067d62944309f19521cc3cc534cb21be982214836d5208210ded4e509067c6254c41be582430c27d62952309f99352843ce524c431cfd52414c2f960906319f997425073d54d0e30f694e308433e5450c41cf584544c27e60d45329f185534827f6550420af18142d073d54d07309f98e51902fa6014632cfd91500ca7f6354910bed8141083cc434c832be98221d027f65900309f594430c73e54504309fd89500c63e6494410de10c5050b6f52d09109f58b534427c6054c419f98c540c67f62547309f59441c82fa6010e10cf95140c423e6515130d714f314427f65ccb109f59253882bd6010c40cf990540437a64540219fd89544426c654c921de98a500c67f63551219f588548c2fa60cc7309f58554042f86050d30be181438cb3e5490421ded81544c77932540219f586508cb7a54840109f58c540827d6294f419f98c540cafa60085209f997314867d6094843ddd4651
  | 36 => 0xc4009000009406005e003801814c00100580cc004005027800800603300100440000d900180b803400705c00c400200c0b7001401202e05b801c5f801c000003c012043000019c0020053e500403680030018034000000000800802800400180080d800603480400ee004809800c0024a700c81a401a006089a5480080050000000046003000800000000000280dc00a02f000805c0000050010040020053007026c040007003650801c01e000800807401f00101a0000043000003800415200c8000000028021800002406f005806c1040030000098514051003000002c00300a805402a0b6002009000000300a8214000001008816425600f2979adc02a008005006c1aa04500100400b800a00e8134128001000000801a019012001acee02502e80ff7854cc230d754d430833c54d0d20fa50120082fb6050b10afd91304827d6095032be582420c3ba4210020bd584520c3b86090840b758e428caf661108419b58b540c67c654c521cf95340c427f63546409fd85540c2dd63104319e98354ccbb954100309fd8552cc27d6094a43bb98850107b864480209fd9741c827e63d50319f997424caf66110b41af990520c77853100209f59741c835f530c520be582318c27f65d0730cf950430cb3f5450d20fc984408435e6314c10de54a10042ed620c7409f984534436e6214910ebd91200836d6214d21bd18540442f860505409f996414c7f12194021ded4d50086776155132af99021d0376534c431db58a544837a63d41429f594300427f6055132ed504414427d6510410cf950430c6bd6490441cfd53404c2ee62d07219f18951cc27c6054a43db548500c67f654c8109f983548867f6254f10be181328c2de6308620db54932106fa65d0110de18f5050a7f6054e42bb986324867e6414c219f99430042df6350932d794c30882be64085209f98f54c833e43940409f59530483755148440dd546419027f654c520bb58843d0a7c6354b41f6d8d300c2df6450c439f58b5150e7c6254341be980310c3cd324c521cf55142cca7e63d5032f9949310c67d62d4c109f982540863d64148109f59721903da534c030be980540ca7f65501109f988505077b43d41439fd95430cb6d5290810f3d89324c6f96310330be982420827d6510832de0c9500c73d5490f31f3d91320cbcd3214432dd544510cbb96010c409fd9531c833d62953109f9825110a7e65909329f587548caf66110821cf95153c42f86448110de50f5050add6390030cf997425075d6395132bd597218877a60d5020e798c431033d5490b20cf550320c67e6294d10de14f5050af96090b309f58354cca7c6355310cf54b411067c6054f419f197424435d5314d40ee50040c427c61543429fd89540c75d5310f42bd58742d067d64948319f58e529075d53cca419f992528c6f
  | 37 => 0x4ac0001002b80c0a2000ce8002000bc4f009801400001600b800413e000000001400a02d00000c002000a006000000203d04e801002e000002000003a0040000000098003002801808a07215a8000000000000000400003c044801409e0050008004008c7f0000000002004003804400417200b00680060180008198000009006800c0020a20000004028021850805400c0020110054000000009804401000b000800290200c006000c5d60000000030062001004804403e06800382d4022008008a55807800500900000b6002000000000158d0010032ee414a038800800c02d014009400000a00000b800a013006811c0b400f00080b000c00000a002800601200002340140a7073800400c0dc01d80c018200200501eebd400c0171f1818a00d00580240aa0022a8005c08200200600000120c10060194000003000001001601900b000003a000005807000a00500500c400a0b90b88154150015023803000200c01b000001f13e0198004000009022000817800d02300140140000030384088029002000c00000100000000080680dd826c0b60aa000019803a00300687d40120010000028040000001000002601dc4d00040460000de800006c00500081ec2a401000001180420280000160006015001002c66e22900680b800000d015010001a00e002800c01401300089ac02a0000010008086fcb00580000140050000200534023000004800000602b009001400b01c000800600501f80080000400d1000400e04c00300042ba001000800000000500004bc028010871000401c00700302e402c00600880343b002400300bc0060000010008018000012000c01a06405100bc0020380208020000021008800800a01200f00842b200d002000801c00300000000ac05c00b00200080b80028018002026042806401c003001800408c00d00600000760000070080050072001802036c0b7024003002801a00100c09ae00306f02d801200902680a40040030dd63601c400e00080480020024b400040be05905500080bc03e000004802000e1200064000001008800404800d01080441ae019002806404e35800081f40000010010000a62068000002c00200b00c0070170010011015000600001380073e000f011807404200201e868403200000380040300000051de003c39900a81d804e017009803800600000000c80ba00001800500060520210070062001003001002800101d80000100040018024008000002001000003f000035803600301200042be0110038b0012600800c0018000020007009800400300d001001400000003ac0f400c03e80140003aa001000c0560010008ea408000b0148020000007000000000601601000b000226503101700380500e4000c020001003002400002c0098014004022015805c0a400700580081
  | 38 => 0xe00601e80002aa013000807806e005003005000001101e802802200102080602e800101200000020331468000024003000013000a00301a001402e001002015c00e09f00d0058000000000000001409213d80702fe01d2f3b479f80000202806c182006013801400e03300281fc00000708300100060050040f7400800a02f0004000002c2d801827400205e000401201700080bc01c000015016400001e021800009a01200b001401a01700480100b000000583800e201d00502bc020100001001007a03f001031c000002000804800000e003004000c0394b4808800000100c803a5be3c60399dd00e600e006803400601a004813801600000080f402c00200500000060a100a000000e0ba0040008090084018de4c0ec00502800000000030000010042005001000006a0110000008132006000009811c08b001800000400f00a012805401900d02b402c009005001800000904300cc00c007006801000a0030b8807420c005000000001600b04c8004028dec000052005407602080040be00d01f00080be00b001800443206126c0204138004010802c04c02a0048010216005001800400002702b012c138000013800001600f010800002802f00100000fc016011035801cb56001807001404d00dcc2010276300080000020000028004000008000027400a05038e80180062a3012008401000004f000400c00700c800c02c00000c803c432002042801800200e0060004160002008824815800103d002c032000022000001600c0000030002908012026008c0090168054a8606e06f80141fc7930008000000019000006400000e00700a002206501e80a8008019003800415c0120002e0801600301703f000406b000002c03e00d122001c0000000218000024008001804c00000d015800400803406d02b401002f0003d11408028029802800001c007041800a01201f0b9003400300f0030018066009805c008094005803003c1e3002895002425601200cc0f8009000802400c02100180058d0001015000400001d00a000000801d2bb80e000c000003801801200306000080020131a0810c27a0010169f80d44006000be7c00e027012127800a00700600000000100608bd81040030860138042002022adc4002070000027a4a400a001005039c00e822000021e01c0048058024009000802400c003005800c0500c500018b802e00700780092b800d00d800000a001000001c03001e0000038166014000005004400601b8004ddc00b002000004200500e015000204a00980b43ea01d055800803c00b00002fc004598005000c000087027801431e005001826000800b051003c070046002001400ece3aa10068000000009000c32003401c002800c00b004803800000405f898c49a0820258004000033000804c03a00800400f80000fd0
  | 39 => 0x1999000e00200380080044180018034016009023801c4be2120208000c2a00400980c000010109b801408800000080085e529c00000380221213f0801000c01200d000800800800000c805e018000002c22811b1d40c9c006011000000c0200db00a8030004001001002005c0b100300300000070270000006001004001400402102c000007402c00081d403601f000002408204a00080040160000030b0401a000038000005e01500382c8000f2201b000001600100000940000370048b440140030458148026006004014000801200102180240e20090004048026004833c006011001000244a0bc05e80c000016c18b002c00203300a005e3240090bf00f404600100f80000040000018010074000006001002800001d805c00c0000029908002000a1c806800000006c00080040c602080d800000200d800400001400000dc030000003001800c0cc0d200a8002000017000000201000100740ac91900280780c4001010806003a09f001018005803200581e400e004008811400e01d00800c4002b6a019800405c053002000019c02101880a80cc038012819c00a0381b68044000070005003c000001006818400000a006000000a03000100000060010040048166000157800405e01a005000002a000001002c12404300100480880061258a3000202e02880b00fc0100020068004700001806802c001000006c076006268007447c004004005c0ca044008bd4000000200031ac02c00102e001c11401613b84bc01000802c001c04c035001833803c127005004001407e001801800000c0002c8007605100380a4000001003803005c00000b801000002500280180fc007003000005801801080b40380c000785e4a28028000800000e040001016800000b012037c00004c03c8000036000015000000000d00282fc0080d0014000687e003766800c060002000802000000500200100c000309e8004074008001008401c000008003001001100f00a4138009041b72400e114001865400200600100d8000000004004003431c00c001690e000023000015a0080358bbd480007001003002a0000000004092091006008401802c0480004000090000001833200603c80ec00c0010018004000008002001800c00000a0024018000001001000606900000b001e002000000002a00c000004400a0050008000018019010800001a01300a000800000400200ac004001007000001a00f00100d401c13d02700000800000078004000000001000001d0ee0340008080043006800001a0030008010000000010806403a0a0017002400000203306941a6013004805401c007004005c0a611b00d015810a000037002003e05905100000b8000024000801805300b0024000021003800004402100d8a180240a0001000c00000000000c0aea03b0230000
  | 40 => 0x400000b002000400401100b802400600001107280000840100004002001001001400800901283cc02601001e000800400f01080d8018000017800010200400d0210006077000002c0940aa01e801c634029001002400007500081dc32a00901285bc01401102f82540c2000000000402c00900d809801a0000008038636029027000017205d056008804a00300700000980d60058028028000000007000a0100b9c9fc01a004004814400200200d808007400406f811c028009000020800e00500a000000000e008800000a01f0008080300fc8000003011000011c8018000013002000000801b0028e4803604b00c000401009a11a01d8006053012800000c00600002940169fa003800c000016189006015000a005801c02e008000021801e6ef0108030002003006007000202b003009804c00100e002c00809d0008164000056004800402c00402002580e80110020030000000004800000a002000001005c00300a0000014003004800002604800a000c01400002581e89f80000000020546001004826c002002015002000c001000000400000385b8040006006000810802804401f0e44086020014809c202001000002c00004102581181ba0000100018036066002b65805000200100000c0006000800400c00000080d0004000001809000001600a002c02824e66a802400200100280000040cb02a000c5e4002000805c01c02a01a80140ae00401c006400006c00000341422510040018000007001005003201700181a400002119a0014000000588000c00c60102200101a4018006001002801601b01ac028002050000c0ac01c00000c800401000802a800229a0000c14024032026000408c03100000b000002701082d002e004005129400400200000000ee003002057808e00004c015c04401301380c01f403700881b49f000b3240f6c00000b000030401c00c0128024000027001000000e057020813800400701e005c06c00000e001008801b3a900cc0c6060dc50d18018003007800000200909f000002a00100180002e40110020000000077001006000200303780d400000500680080ba01b0088139376008002800c00000c00c003402c00a008019411ec900400004e0c017000803000c0be003801000a025000009402200100100cc032009000878c02a00000000624a80050098048014001001001c01c04900080240c00010010098002009003000800e00430483c007402500000e800a00004700082ec01700080cc00402d2a005000020cc000003400400b00b08c0008006002160800012c06400480000ac223800000205a0c2000001600000006d004402000c80d80e2014004025029004a004004c090003001800800388700d8050000000001805000e0fc007805c078009008806c00a033006802002801a009005419a000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1047576946100421f3acc8992831e5da5184010a74e9a9ca010c6e72194400435431042a0081535c8530c941ec2a518aa018d3b7590c40083172a2c418e2117dd95314d41c5ca9310a418e365458442c425d3a6c5884218d9516110f108f4e132c8610e8e644c8510ca9c382a921e630f9d265ccb10970e0b2064a0e65625445110335312c02a0654b9d35294b308f6e0b2a84885587054c5348739b08c0aa2651bdd95214b31c74edb2a80205387055141cc6e3388a8990658e1506050920c74a83028718e3954982418c72cb18c6a84835a1c152149318f2e132a8498e6a62583540c734b12c1aa0631edc16315121b96e0aa2641947970d9151ccb59b20c2982219654d6014c21ab4e02a4a610d2d72150424c23dbb2a0282850fdd954106218dcec29a6490e7151982410832db1cc7a82851e9c06510810a5ce5b06a89853a74985500872c298c0a1a839314d62cc521a5ce5aa4a818d6a72d5340cc2a7baac0990652e5d2608c440a98e6a92640862e64588540c31caa4c010e211e9d83154021a70e0b14a818e3a54181420863d380caa10639958a6115031cd2c5300a818e5953582410870eaa2c7208635a5c35294831cd4c5306a818cb970992211026d3b480980612e9d95150040e30e6aa0808865563d44214c26c39ac120a611edd94294241c72a9b028410d1d73d91540862eb98ca908814e1d162540318deeca90a018e7161580540ca3c382c929021661c14310f3087ce9b2c650847b70595324432a29ac3992431b9ca63d4540c74a8b00838856970186520c63d380c2a90878e5954110030b50e0a10851955a73d5040c823dbb2a820041c3551320c821c5ca9316a018ce47158a434871daa2c010a614e5c64214142ce4eb30e808854e76149324c69d3a6a128463875915314021c58a9310869062e64588538869db82c72a0438e5506050c218deeca90a420e6852d81425029d39ea8206419398d5210431c74a9b02658855a70d4e5390a9cba0a728043cadc95410110cb2a7300a010e3854980424c2d838285a0a830f9d3650c720ab2e62a4200863a6458052c42b4382c8a90638e552601483187cebb22609047970d964348334a96c0a10638d552610c831d50c8992401047a70d9151cca5c3b064a00811e5c06510e2187ce930ea60871a73d5040c831c298c0a1a836c1d13084110cb2a6b006210e4d6354a410c63d3b0a4a84838e9926094630ce2c2a80a01946f72595434423dbb2a0282430fdd165085308ece232a841863a54982410c794aa642a80431b1c965501108f4e030aa62161c5458c214c31caa2c1208639654d6014c428dae431aa2205aa72d5040cc297396c8aa6618e5926014c21ccac4b08a81862e64548520c69cb8c8628287595c44354831c74c9304a31063a54982418c63ab88cba1841b1584614c832
  | 1 => 0x52c42ad398a8a80431e1d943940318daed290a018daa7215040c821fba2c0a98211b9c86510d10c70c9292401061d6454c3104316b22a410821531c95314d1087aed2a4802063754d85524c23bbb2a2288810f9d26194032c70a9b02629863954181428c6acb86c6a98430fdd16094d10c74a9300a610e1c64d8d524421fbb2a82a6650fdd95415320c3cc929ea010cb974980311031aaa4c2190438b95162d4031b96e0a1264195a87258141102a639aa499621c3951320cb10cb4c6a80a010c3f74595304831cb2e82200610f9d36508410d32e6322601847b76540500ca3c382caa1a436a1c95410110e52a8a92a018d4c725815308726b1aa429021539d7634c9218f2e0312a221c6d72195410c31c328c8982214edd15110320c76eab06822047a76151500871bb26c2a9a414e9c36455021c5aa9310a818e3a5498231c431cb22c0296218e19252482108eeeca88a3a047b765445050f35314c0298214b9cb5490330cb6ca3028621d6a75d89204423cb84c7a8a855cdc553d4142c6ac8a88a21065a53181420868f3a6c6a98431edd943d414287ce9b2c631045d731944004237390ca180215a5ca43141428f4e032c86084bb764c5401021e3a2ca982214e1c954101108f4e031aa22164d53588539073830ec0aa2654e1c15415321caaa6b0c6410e996390c400c21eba4c7a8a411e1c06550910972ec18a802045e73d964208274b94c1208411e1c164d4532cd0a430284a0d39740c5500870fb2ec8980611e5c261d4943a72ea21881085397414c4044326a98c4a1843669cf6090840c74c8b06a79047970d91518ca96392c6aa0439a94b6050831c3aa8b18438853970986540869d386a9a0c430fdd954151308f0eca12a018c5f7654c530430e2a0c6a8a418ed506050d32c9aa6b10a6205a97214d401025c3b2a4a00818e1526090530cb4c6b00a8196396419250086e2b88a8990654e5c06115130e32a629a80206a8648c9200821e3a2ca18a41179d8534cb218f6eca80a1a0e6952181210c23bbb2a228a874e9c2615503187aed2a0a78863a6458353c423a3aac221a438d99161150208f6e0b1ca810c7571194424c316320a4902212e5c0644c440a72e1aa4a818cba749913044398aa262a80631b1c9654c4408deeca90a5a0d687050d520c794290c0a12831e1d94294021ad6e0a1aa418d397494c40c823d3b6a4a80634d9c46295310c9ac62908498cb97098e421031d2a4c120c43595d43148421b94e030a64194ba72d954010316a92c2210810f5db5408530a72e930aa018c5e73d94211031d2a6c0a16212e1d160cc430c3ac8a98a610e3865d912044334b10c5284830f9da5450a2087eeab206210e3b651814310f17b2aa890843551c56454c21a74e1aa4a99956a72186509070c298c0a1a83ca9525294031c74a830286
  | 2 => 0xc22a6638e95360508318f4ec292408853a70986540865d390c6a00812e9db5150040ad6e4b22a120cf27199120442ac39ac8a80639354e621042187ae9b28431843f7615031482b4b90a8a80631e1c16414d218f6e0b2a8710c7a70194320432d31cc1aa0430f5d6640c421c5ca8b10a018e3964580530863dbb2852806317dd95314021aa8e6a88a29047b765405090b0f324c6296218e9926014c10972e0312822043e74194300430f2a2c620461d454d2154021a5ae4308a89052e740c5520c71baa6c2a9a4117dd95314d10cb4c7300a610e5a6358054086b9baa63280634e5c75410330c3ea9318429043f76550544cb1caa4c1a906317dd95314e408bce732a850843e76151514c21f3a0c2a9841d1549414c4318eaed2a48220ec5624c4314429c382a9216430fdd16054810c3cc9318a810d5a7394d304428e39aa8a1c431e9da4154021c3ac8a98a60847571d97434822f39eca10c81721c1544c832e92a790ca010c5f73595404423cbb4a718061175cc6254440e30e0a98862066552d85420c69d3a884206610f1d16394021c72cb210801043d76150314c25cb80c8194812e1d160c842087ce830aa7905387454050c871aaa2c2190638e1506050b21878e8b00a690d3b75500400421eba0cb990219a5895014043c6ca8b0881084797614c40c829cb84c32a0639a5895110020cccc4b08a81053870550544c61ebb4a818e211d9c46510c10970e0b2065a0c5e7319642c425d3b464a0081561cd64542418dce5b2c868846f76548520429dba2c4a84839958a61d4e21cacc6b08a81943f76550540cb1daa4c018a6193595320c8108f6eca80a118cba7498620442b2bae64908431e5c261952328bee6b2c42a052c72581540869cb86c7aa2419a58960150318daed29c64195387590c40c831baa0c2a9261479cc6195310c74a8302658847970996420c717b2ec8900419318f6255110a76e0b1ca98853872550408432a31ec2a92212e1d1600c910a72e8298801045d731954108399b8aa8202210f9d3658c820c9ac629042986e170185324871cb24c028a651e9d664481108bae6328801043e74d96218c31caa6c0a1863aa18a525004087ce9b2c4208569721521004332a90c2990218dd906154d20c70a9b0242904d973181420c25d384c3a1a831e5da511414399eec996a0194787058c544861e3a2cb90a61c69515354021c76cbb0284216555358453082a6392a629a831e1c162151318f4edaa2a010c5c73595204421e3b2a898621721c1434c832c6cc8b08a6106665258420843a4a9a43280433c9d661d01108f2e1b2e65a0d9a7310840cc362b126218e211e5c065d0c21cb6c6302a898c757694e310c63b388ca190214e5d26114142c74c9300a818d2e72d91540c71d2a0c0a1e210f9d36054732c3ea9318429861e5458c
  | 3 => 0x526014031cb6a6b00629072870548421029cbaa82200618e5506050830c70a430284a0e2c5458b304832ab1cc229021ac5854190040c74a930443886c56348421c4316b10c4aa6211e5db5284010a3ae6308a89046c7558a43487162a2c5a0a432e5d260cc840c74a83028618e555318532106acb80a8a98434e5d35254031c72c9300a60862d5498a430ca1f3a4cb98e419ad8860551318f4e130ea6a15a87050842c83162a6c4a8a615a5cb5494031970e8b06430847b76509500870e2a2c610a414e5db541032087ae932e658851c7358154c425d384c3a1e831e9c265d0810a72e030ea89856a72949204423dbb2a0286432e5c06350440c76ecaa0808845d73194414834c32264980611e9d854540318f0e0b14a818d1e74085530863dbb2a0282630f9d3658c9108f4e1b2c8690d3974d4e50087162a0c4a8a6117dd95314e42e1ca89906418c79701953290636b90caa18210fdd95415330c5ea9310629863954583520c61fbb2a82a2411e9d8534c110c9cc6a948218e5953d81430861eba6cb10c615a1c95114143ccecb2926218e3a5458042c832629ac418a814e1c154153318dae4328870861f6418d54486ad398c2282854e5d44310110a70e8a80a090c6d72194400422f398ca208439598d611503087aed2a0a610e395458031c431c324a6984211edd95014143c6ca8b088618d3875500404c335290c0a1063171cd6550420cd4a4302840853a74d42500c63dbb2a0280858e9916015032cacc7308a81066462d85534432bb18c2aa265a95d0614c921a5ce5aa4a99853874540504c697b92c0aa62156dcd51d4142b54e531a802047776544514c2a73aa64192214b1c95450b1087ce9b2862085387055043cc65b38cc1a12838e55260150218f0e0b2864a0f2a5454a500c74c298c0a1a831e5d460508108deeca90a4a043d74194300828f3b0a6a1a830f9d06154b30ad4e4308a0a1c777654451502a63aa6598a434a9cb5410330ce0c2302a89945d73194420430eb24a7a80430f5d06254430ad0e0a90a4a0e3a5458231c429db8aa820061939d8534cb21ad4e030aa418c3d7499532c421eba6ca108211e9c0650c9418f6eca80a120e2c5498b404821ebb0a810a614edd64210210ab0e6a8ea0a145e73194200429cba0a4a80639c5855014042c6aa9b0a8610e3854980214831caa4c120e211d1d56110d1087ae8308a68863a54980500870e322a6988815a9c35494831e34a929ca010d387055141c863dbb2a02844387592530c421972ed99280204b970193311021e3a2ca990211edd95014232d50c9a92408862f64189544421f3a6ca108611e1d94394021e30a7b0286a0d4c73591520c63a38aca990818dd506154d20a76eab0a802063a54181438cb94320a490221565cc2154021c74c8b06a58853a70d52548c72b31a
  | 4 => 0xf6eab048218c7671995438825c3a2c010a819a9896015031e32a998aa018c6e7219443c42aa38ac0a98430fdd95415310c70a8b00429853970d91540c63cba8c0a10638b99252d4031a72e130aa818cba7614540102673b0a4996634edc162550318f2ebb028418ea8649492008334a90c0a10638ed906054d218deeca90a5185387454050cc71aaa2c3210434e5d74154241970e8b00641053875500404830e326c6a9a21661c14310d32caecaa9a4210d4c754c8324430f2a4c6280430f5d6640c710e2ea8988629843f76d503148326b1aa4296214e1d16094d10c9eca99064086396458053c432a31aa2a08619cd456008530c9ac6a908218e4d63d48214c21f3a4c3286659658e60d5021caaa630a6510c7870595430863dbb2a0282838e15160d0920974ed10a802043d74d96320829d386c8aa443ca5525294031c9cc6b16a99866962980540c21eba0ca18021179cc65d0810c6aa8b08a8184b97099232102ad39ea1280431d1c56550d20a70e0aa68390e2e6458a5348334b10a4204210fdd8540c5308f4ebb1c408847a76149500c735b28c0a10858b5526214831c74c8a80a010e4f764c9510ca2eb98c2292211e5c06590c21cacc6b08a81065963540501074c31e64a00818e5506050821ce2a3300621843c76d5130482cd39842a00810fdd1639402187eecaa0a9194b971d95401032d29cc0280431e1c1654c841c74a430285a0ec563484214423cba8c0a1483725c0614c83287ce830aa41874552905310c6b9b8aa5a82878b99252140318deeca90a5a1e1d6318d54c423c3b286a8043569c36354c2187eed2a06210f4553505210868eba6c6a98432e1d16348110c5cc9310a78864d5398a410863cbaec0a1c834e5db5410330878e8b10a098d3870589540c6a6392a6990831e9c06154e4287ce930ea69064c63549210c29cb82a8200218e1516090530c70a9300829063854181434cab5386a5294878ed946050f41cd4c5300a610cba76d09401034c326a6982216c1d12084110c9ac7a9042a063564944310c327b2a64194831e5da5314142a74e9a84a11963554584540822eb98c2a90814e5c2611513087aed2a06210e1d6498c52c4317aa4c418a410fdd165c853099eec990a21963b64181544c734316c0a9a210f5d3650c6208bae7b2c850851d73151410429cbacc820061531d5320c941c72a8302821863964192500c63cb84cb218432e9cc6250040ce6a2b0482a047776544518829b3b4a2a0c81591c9511454387ee8b10a098e3b54980314830c320a6982210f5da5414021d30c921a60185aa72d82431028e3a2c0a98430fdd95414b108dce432a622062d5498b500c70eb2a862186393595320c840e92a598ca018cba76085401031ab24a2108418e5954110020d50a430284a0e3954181430823cba8c0a18218e5
  | 5 => 0xe5a6358054cc2aa38aa629a41ca5485250040ae2e2298801062e6458853c423d3aec0a12215c5c43254241ab2e6308a0a147875582424421ebb6a8206410f5d36054632a72e0310a89851d7318654c431db20c0aa0659a58a60d5332cb4a6302872153a70986540c727b2a64190836a9c83150040d36c83028621e3b65191208423ab88caa10611ddd95114630c74a830285884797694a200825cba0c0990815c5c43254031b90e0a12641966462545410829dbb2a8204218e59150140218f6e0b2a8610d3975108408421eba6cb18821535c7654c8328ece3b2e869043c7655120c431c2a2c119261b14c9610c941ad4e418ca010cba768c5401026dbaac6200619654e600c421ab2e030aa610ec532584324431aaa6c2a06218b5886295310ca8c7b0aa890d5b754c5500c68eb98a9a0821179cc65108108eee2b2a8690c3f74595314863dbb286a8063ac1936148110c70a9304829043e74d97328423d386cba1a438e59664c4210c70a8b0e609862864149204431db20c0aa6631b9cb650c740c76a83028490ce87650920082a639ac0a9063695d031484219d4e5b02869043e76951438c31caa4c02a0638e9526090421c38c9b1aa690cba74991204430f322c62a0411d5c46510f20ce2a2b00a21966765549310c71cb2e82200414e1cd5410110ca8a6b088690c3c7458053c872d298c0a18415a9c85394241c5ea8b10629843f7559021c42b5390a8a80630fdd95415110ccaa530c400863854d81434c22eb9eca10e818e192504c010972ec10a80205557114c315023d384cb210634b5c8611513087ce9328658861d5498c5008732292c2212219354d620c621e54a4210819864e63988540421ebb6a8206610f5d261d48108dce432a821862d64948500c62ebb4a719065d1dc53254432970ec90a802043d7695021c438caa2a6a80431bdc96550430b30e6a08801843e76151524c23bbb2a2288658d59664c4210c9ac7310a58843d74195210c29db82c52a0630fdd1654c91087eecaa0a910f2754484214829db82c6aa621acd466090541c5aa8b16a018d2e7218654c431caa0c0a1c430fdd95415331a72eaa08808866562544510c22fbb2a618c431e5c265d0c21a5eeca908420749524c5500c6e4b90629806199589510c4308dae532e839843c745825244354b1084206410f9d06508530c76ca322401063b54181424ca1ebb6a810a410f9d85450f31c70c8a8a401053974148404429cb86a92a0431b9cb650c440e62a228a802067361181534861eba0c2a9061569cf64d414287ce931ea2906c53258432c431db28c0a1683cc54541100308bae632842a06b361945401023cb84caa1c435a9c3545483187ee8b00a498e39549805308754b90c89004172dc1614c8328f0eca14a018e3564984530431c320c0a9a430fdd954106318
  | 6 => 0x34825dbaac0218811e9c265d0c218f6e0b26a29952c74548524423cb80c2a94875c1c552d41438beeca98a720c3d741943244333314c22a0619694d609042187eedaa04298539741875050a3cb82cb208211edc16550b31c5ac829064a0e2f54189418835431442a0081475d02154c21a76e8b18a0a143c74595314863cba8c0a1c839358f5294940c38c6a9a822066852580424429dba2c4a80638b99152d403199cec29a6590c5f7654c53d0a2f39cc5a8a8187d95544c431c72e0322a01963a64980530865c3b2a6a00810f1d16094a31e50a4210808847970594310429b388c72a621561c15314d418ece232a64205647154921cc21eba0ca196218e5d765500409b4e7b02849866462d85544c67838ac6902211e9c065d0c21c72a8b00438846f72595404432aa9cc2210431e9db5354021ac8e2a90a4a1e3960181540c66c3b2869806163dd1604c8328f6eab048210d2c74548524c70fb28c898061c55515348421a74ea18a80206a864909200830faa6c6a8a418e5536050831c5aa8b148210e3a54181428821f3a0ca180411e9d85354021c5aa8b10a018e3b651814210a9cba88420221871526308530c9aa6312621064d639482104326a9ac4208439354d6214f10ce2c2a80a021c3c74597314821e3a2c0a98219694e6090421a5ae5b06a89852d72151410422eb98ca216218d191514c440a72e9b16a0a1eaa6290a4010296ba062a90631e5d85484010c76a830286984787558032442b5390a6a84830f9d85450621976eab06822065963980520421ebaec8906210fdd95414021a72e829aa010c7875580434421eba6ca982418edd95410020a70e0aa08590e3454d85524c2d5ba26090041d194d524c431e1ea8990649866462545310823cbacc8900412e9c261d09418f6eab04620843e74195210c21ebaec8986218bd506250120974e930c410861e6458c52c43a8a9c42a80431b5c86510f10e8aa720a4210f195494e500872ca98c098881479d76350d41cd2a5300a418c6f76548528c70eaa4c62a0431e5c06590e21ab2e6308a0a1e2e645885304237bb2a4290870f5d262d4530cd2c5300a91064d63988540831caa2c02a0658bd51620c520d8a65308a0194b9701913210326a9cc4188438e5526014021a3ce9b1aa79047a701855290e3bbb2a228a851bdd95214b4087ce8328400863a54582410871c2a2c120a411e9c26195332a72e9280800861e6494c500865c3a2c0194211e5d853d0020cb6eab18801846e7218d511031cb20c8a80430f1d160d4532c74a8b006210c7b7059053c8716b22a429061879516310a3287ae932e63906715158031cc31c2a2c018a412e1c16408540878e8b00a498c7b70595321072ab1cc22a041561cd541011087cec2a2a6904b974181211023cbb48328043565cc5494021ab2e1aa4a61
  | 7 => 0x6298430f9da5450330c3cc8a98a610e4e53588308823dbb2a0286654e5d26114143a98ea9926290e6a52982410c65d39ecaa0081acd846050d4187ce9b28621063a5458043cc25d384c3a16831e9c26550d21878e8b2c429865675185324c61f3a4c5a8a619a9896014f10a72e8310a0a1d357118c544829d386a92a063cc5454110020b52e418a802056970152520c70e2a4c6212618b95262140318f0eca12a120e4d5358831c431c326c0a92214b5c863151208f2ed288a0a143f7655053c422fb9acaa1221561cd5114142a70e6aa0801063554986400434c32462980610f9d4644c1208f6eca80a1a1d2d721534104354b1484200419654c604c420c9ac7316a91956972152500c6e238a6598a431b1d56210d2187ce930ea40845e73189511023d380ca218418d1506154930c3ac8b18a5886385458043442973a0c2a90631e5c06550c21c3ec731ea89043e76d51514823d384ca210630fdd16314121ce4c2b00a9886e27018532486cd39ea820661569cf5494021c74a83028418d5873540504863dbb28628285d15c4534cb21cd4a4302841863954181430c71caa4c1210411e5c26550d218f6e0b10a898f0f544c8324832cb18a62022199989611503087aec2a062904f271991304431d322c1a98430fdd1654c420ce6a2b00629043c761513048394aa2a5280631d5c46590c208deeca90a50853671188544c29dba2c4282874e1c16355021e1aa89906418c7571995438823cba8c0a1841475cc5410d20c5ac8b10a60847975d81430861ebb6a8214411e5c365d0d2187ae930ea6906ab641814210b4aa1ac2218634edd954100208f6eab006210c6f76548524c70f2a2c6208631bdc9654c440c3ac9298a010e355458432c431d2a2c02984396d8f6055121972ed10a802043d74194200431db28c8984215a5c83194021c70c82924108731548c5500c71c2a2c110a618e5506050b32a72eba08801863965108400823cb84ca21063175cf65086408dce5b2e868863b64181544863cbacc1218414e9d0539402187eecaa0a91862d64548500c6b4392c6a8043c65cf541032087cec2a2808845c73595404432ab2a62188431edd943940218bae7b2c841066b6298b5050f34b12a0280839594d610c2108dce432862a057071589500c72c31ec0aa2431b5cb65d0d108f4eda92a120c7b70594325071daa0c0a1a418e192534c0308f6eab00820863854980314c334a90c0a10618719063549108eae232a64206c932980510ca37390cba182193d4d620c5408e8eab08648843f745952044236b90cb218219658d5014042972edaa0819865a535803108739b0ec0aa2659558d61150208f0e0b24a418c3d74986500ca3d384cb194834e1c954100308eae232887104ba761494010296392a8202218d5915114432c9aca9906410e38549804
  | 8 => 0x961d4f21c70a8b00848863554d85420c63d384cba1463565c35394c21c70a930684907194310d500c71caa0c0a0841179cc651052087ae930ca19961f5418d404c316326c4a9a431b5cb650c440ab2e7aa4a010e5963580540872629ac418a418e5506050e30b52e531a802061e5458c21c43872a2a69084395d8c6154d20b30e0a188718daa7214d40102b9baa43280431d9c46510d20a70e8b1aa010d4d73148324422f398ca216210fddb5408520a3ae830ca610c7b7650d500870f322c62a0439a18b6055110ad0e0b24a418d737550110042cd398a2a00818e5516014c2187ae9b02a3996a96210840443273b0a4992634b1c95450a318f6eca88a0a164d53588310863d3a8c0a1a858e5506050a20974e9322601866562984548868e39aa82a2431b1c9654c110c72a93048210c3d74194310874c3206298061aa1893250040c9eca9906410e65525845210e9d3a6a1284439c98560150318eae2328869059873550404428f3a6a7298430f9d365cc910e92a790aa010c777654451c821eba6ca188431edc16550d1087ce93286210c3c75590214c2cc39ac0a0881471cd5450f108f6eca12a018e3964583530869db82c42a2618e152608c930a5ce4308a8985367118c544830eaa4c610e218e9526008710b1ce830a641947a70195329061fba2c1294638e1c16414c20d8ac49886390e5453584434428f398c22a2411e5d76050a41cd4a4b048218c7975181430871d298c0a1e830f5d3658ca10a72e830ea0a1c7a75d814344316326a4902211e9c26510c21e92a690aa010e6b62d81544c72629ac421a4393d4d6294d40a68e8a88a29945e76151530872ca9cc1190412e1cd60d0440ad4e418aa018d727118c5050ab539082a80439558e61152318beeca986590e395498031c430eaa4c7200612e9d2644802087aebb20642064d5398a310869cba0c2282870f9d0650c810a5ae430ca98853970d91540870f322c629021565cf5094021a3ce7aa081906d170185324c69d3a6a6a80439614d6010d10c6acab26200853970985540868f3a6a729e41569d7634c110c9ac7310a810c5d7399741c832ca9ec0a10432e5c2640c440a76eb21880885387058e54087a499065280430f9d0654cb10c9ac629042a063854181314c3162a4c418a619354f6250c2187ae9b28621053970984544825ab88c8190819a5886254241c6ac8a88421055973151500872631ec4aa2434edd16354241970e8b0065984b874580315021ebaec899083aa58941100209acea30a6498d3b7058d540863d384caa18439a9896014c21a72e8294a018e3a5458353087a4a9263280638e1506050932ab6e6a88a0a15b271149401025d39ec2a00819558d5114420c9cc6b10a80868d644c8500cb2aa9ac2210431edc164149318dae432a622074553cc5210870eb24c
  | 9 => 0x2e130ca819573715485050f5830ec0a12838e9916015021c58a8b10629846d721944304334a92c0290634b5cb5495031ab4ec29a608843e741953108359b08c0a12831edd560884108f6e0b2a8690e1d6414c32507c499064a00818e9916014c21c70a9b02869045d73194428422f398caa08410f5d0654c810c3ea831a83186a962d044008334310c0aa26387191534c320a58e4aa4808866b52181425063cb84ca218438b552620c7108eeeca88a32063464d85534830eb22c6290219658e60d5232c72ca218801847b765405010f2db18c0aa24387d906355110a76e8994a120e386494120042363aac421a41a658d41100308dee4b2a608847a709954304333312c22a0651e5da4194031c6ecb2a26218c7970194430865c3a2c0190611e9c265d0e2187ae832a621053974d4d50086e8b8482988634e5d66350040b30e0a188618e3954580310871c320a6982215a1c95014141ccaa4b08a418671515805110e9d386c8aa465569cf5094242a72eba08801064e6358853042a6bacc2990651ddd9511473087ae83286290479760c650086d8b8ca8202218b5926214c20c72a8302860847870594434861e3a2ca982411e5c36590f21d50c5192802046f7558a310872729ac4188218b19152c8440970e0b2062a063854580414c23c382c92982193d8c6255110a5cebb1284a0c3d76950500c7872a2a5988638b5926214c2187aed2a48220cb870591325063b388ca212613a1c9608c5208deeca90a418cd973982410c236b90ca21a21785c24148421c70a9b0264986715118131102ad398a5284831edd95014243e4aa8a926218e3960182540861fbb2a8208218b59262148108f4ec29aa120e55639845404237396ca18c81471cd62550318f4e130ca899555758c9310c726b1aa4294838e5516090421c9ac7310a80861d5458c54082f0b8062908438b1486050941e1ca8a9e4210e1c531814350716aa4c429e21591c55214930c70ca322408861c64d4d30442d93a6a1082215a9cb64d4143c9cc6b10a81853974d4a500c762992c2196631edd9541011087ce9b28631063a54181430423db82c9298435a9cb5410330e34a929aa010c787058e540863d384caa1e431e9d854440108f4e1b2c8790e6a62580540872ca98c0990812edd560108408bce630aa42062c54988414831caa0c0a14434e5d6625004087ae9b28639063a54980520c69cb86c5aa261ca9cb54103308bae632e840861d5498c52c429d3a4c2a80638e5916014e2187ae832c65884b87458d208423bbb2a228a65715c7534cb21c9cc6b10a78854e72d4d32502e2b8ea499663a3d913254032ab0e0b24a610c3d74d9732842b8b8864a80439698d60d5021e328621aa120e696258053c4236b90c2a98811e5c2650ca41a70e0a1aa221dc9730852008362992c2194839998
  | 10 => 0xcb9768c5401031d324c028a654b9d8525094187ee8b2e629056b75486500861f3b4a8906219594d610c821a74e928a200853974148408423c3aac0212218e5964310030ab2e02a4a610ea86408520082ad39882a80639358d5208410c3ec9b1aa48853a740c6500863c3aac021a41471d16094c2187ee8b04a710c3d76d50438c2ad398c3284838e9526090710c70a930062907255448421c432d29ac019641871526308520972e9300422043e74196320423cba8c099021931d93254432e18a8990649873054505100431d2a0c0a1c430f1d16054810cd6a4b0042a065a6358052c431d2a4c0188439398d62d5031c3cc8a986210f49320ca50906a639aa4994831e1d5608c910c68a9b0aa69055973d935050b26b1cc5aa6412d5c4640ca4087ce8308a48847a7098f5150a1f3b4a898621595c45208540c58c4a92822064e5358831c423d3b0a4904215cdd521540218dee4b28868858c74585320cb1c2a0c0a1243d11c5524c431ad4e42a4a018c7a70d9642cc69dbaac4a00811e9d8534c210cb4a630286084cf764cb510ca2ebb4a7188631bdd95214930a74e1aa4a910cba74d8f104432d29ec0a18431e9c26195232c9aa63126390d6a72d52500c69dba2c7284838b5516214f108f6e0b2a860843c745825308734a92c1208631e9c26550c208dae432882984777159543482a6392c8a9843539d7624c931968e2b2264a0c7a7098b5150f17b28c8900418e15160d0d308beeca98a61053a74d49500c62eb9ccaa14218e5806095031ad4e5a84a121e586414d30442d9b8aa8202219654e600c410878e8b28429869574185324c727b1aa4a1063569cc52542418f4ed20aa018d5a70d51530878d29886206415c1c563540218d8e4b28868862f64d89534428ebacc62188193595320c841c70a83028798c3e76151410423cb80ca1928393d95320cb10cd2c4a80a018e6b52580214c32db18c0a9a434edd642100308bee6b2a82104ba760c5401034c31aa6a00819a54a60084108beeca98a79043e7499532843b0a8842900414d1c56355021cd0a4b0642885387458252442b4b9062a80635adc951d414387ced2a2819043e76d51524c31daa0c0a1261569cf54d0320ae2e221aa018c787059542cc696ba6a5290631b9c86510c21e2aa8a9c4210f19544c5500c69d386c8aa4632d5d0614cb418eae232864a052e74186520c637bb2a429621871526310530c9aa7b0a4210d54735445150ab4392a9a02216c5c45250040a72e0318a890729421095090726b2a64194839518d5148430ce2c3300a81058f74585320cba2a9ca4908438e1536050930ad4ec29240884797059421042d438284210438bd906254d108f6eca1ca120c797614c404429cb80c22a2419694c6050e40aa8e2a98a6a16346418553482cd398a8206610fdd5640c7108f
  | 11 => 0xd065c3b662a00811e5c26550c21974ec20a802051e73d5254c823b388ca218418e15161c8120c6ced28a832061d5458c540861eba6ca98a412edc56010c40c6ecaaa26218d5973149509071daa0c0a12418bd8a62d5130cb2a6302630855a70d4e530872bb2ca6908434e1c15490c32cb0c7b02a4884bb76550404423ab88caa18410fdd95408710a74eba08819043e76151418c637bb2a4296618758c6395310d66c2a8a802064e6358b54ccb2ab1cc22a0434edd56050440c6ac8a88621843d76d50314c34632264a8065565cc5294241c6ca8b0e8188479701855390a2f398c2292219694e600c421c70a9304629853a72d5040cc316aa2c418e210f9d0650c91087ee8b28629054e7614d32c871db20c0aa6436a1c961500408bce7b2e848847b76540504ca1eba4ca188439a1905248110c6ecb2a24210d397494840cc21ebb0a810a411ddd95114430c5ac8b10a78846f765485250726b1aa4290831e9c06590c218f4ed28a200853671d51418c30eb24c6298418b5954210821b32e818a60185397418c5050b35320a4902211e5db538401087ceb32064a071b6414d3044334b10a4202218e1516088520e9264192a120c79709963290759b0a82a00811b9c86510e10a76eb2108010478705925308735b10c0aa24347dd16054c2187ae9328658863a5458031c4316b22a4290631e9c265cca41c9ec6312a68863b7558043102b838aa7a82858b5516215030c3ca931ea010c6d7298f5150327b2aa690843669cc5250040c74a83028418477715953244354b1084200418ed97644c0308f6ecaa0801866762185544caa639aa4292211e5c3658cb41c70a8302649847a70196320423cb86cb216639358d5208710c72a83028418ec532584500ca1e3a2c1290638b5926214f10ac8e2b22a418e2e64988530421f3b0a8a8a411e9d76050d20ccac5308a80846f725954348678b80c2994214a1c95410110c70a8b00849854c7254d3210236bb4a5100411e9db54540318dae5b2c868847a709875250e963a2c1290638e55160d4c21c68a830aa69047a76d49100421fbb2a818e21475d35394c218dce432c860863a5458241c42e4382c8990651e1c16494a31e36a8980609043d7519120c4335baac420041b14c9610cb21ab4e030aa610f15544c431c43a499064a80631d9c46510e208f2e130ea6a16715158021c8333b10c2a9a414e1c15410c32970e0b2064a04e972181430821eba6cb18c419698e6015021a76e8a8881984f2719923044236b90cba18218e1506050d30ccac4a88a221c6f76548524423d380cb990214b1c95415110c38c8a9a642047970997428c63cbacc12086393195324c521970e0b2265a0d1e73d5240c829cbaec1218819654c6050c20ce4c3300a81961e5498c530868f39ec1aa241a39913214032a74e810aa010
  | 12 => 0xaa66587192534c320c70c9b02a690d3a740c5500c72c318c0aa2439354d628c421e34a721880104b874580329029d386a8a0c635c1c55214143a72e12a0808863964980538871db26c0a9a439c9856015021cb2c6a88801854c7354932106a739ca6992438b5526290020b88e29926390c3d741943284316b22a5a80631e1c1655083187ce8312a21843e7499532c431d2a0c0a10219c9856014c21c3aa8b18a5886986414d304421eba6cb992218e5506050f10972e132664205aa7290c40083172a2c4208430f9d2658cb10cd2a4b00a420cbb70586431025cba4c1190810fdd1654c110a5ae830ca418e3b5418142c8727b2a6419081665cc5150040cd4c5300a818d1a73d5040c831daa4c010a61ca5512008310c6ac8a88a2184ba74d8f10842b5396a1280638edd95410210ac8e4a88a29843e7599031482cd39cc4a00818e9516014831c6ac9308a61065a6358354c82b5386a529063aa58842102108f0eab1a408846e72d96438425cbb464a00811e5da52141438bce632a840845e73d964244386aa264196211e5c06510931c5ac9310a60843e74d953148296bacc4210812edd93250040ad4e030ca418c7970195321061fba2c1290631b9cb650c410a74e9a84a010e2d62188544c22f39ecb2142117dcd654844087ee8b2a421869963d04400c25c3b4a4a00816a9c851500408f6eca80a198d4d7594d2108734a94c1208639398d6215031c9ea6b1062904777654451d0ab4392a02826317dd95314d42c70c829a610853b7458a509071c326c0a9a41c355153c8421c9aca99065884b97118d401029cba042a80434e1c15415121c70c929a608863665504415021f3a0ca99021aad4860509418f2e132e8710c3e74987524c22f39eca108211e5da54900408f2ed296808862c54988314823c382ca212631e5da53d01108bae7b28422043d74d96324431c2a2c118a615c9c442540218f4e1b2c65a0e4d6394821c431cb24c029841a618e4350040a76eb218810866962983540c7172a4c4188438e15260cc9208dae5b2c870852d7295042c432632a641928171dc5644c832a76eb21880185c471591320ca37394caa1c218758c6315120d4ce830a6490c7b76540501072aa9ec2a18439658d5014021ab6e0b24a610f0d5454d210871db20c0aa2659358d62150108f0e0b20a498d6a720c55008733292c2190631e1d560cc910c58a8b108690c3d74d94210c31daa0c0a1e63569c05454c218ece232e861061f5418d51483172a2c421e65565c06194c21a72e829e801043d7519130c42b5b8287290631b9c86154c40a72eb2a0801873154485500871cb24c1a98432e1d160cc510a72ea10a802063664584540cb27b2ca4988639a9896014f20b94e02a264194757518532042b4b90c228285ca1c95410110970e8b0064a04b47159132
  | 13 => 0x32500408b8e6b2a848846d72d94319023ab88ca218410f1d1658c520a72e9a84a010e3954980310871caa4c121861471cd541011087aecaa06210c5e731944244326a9ac4188210f5d06114910c9ecaa926218e4d5358853042753b480900411b9c86114d10ccaa4b0e6418c797098654cca1eba6ca10e618e1516010520c76cbb028621e98634c9401032d31cc0290210f1d1654c91087ce9b2c620861d5458c5404237b92cb18a815a5cb5094031ad0e4b22a120dab7050d4210b69380c2992631e9db5344010d32c6218808843c74594324422e39acb10a811e5c265d0831e88e2992a21965a63580540c61eba4c3a98211b5cb650c410cd4ec292408845d73194200423db82c929c435cdc55314142a5ae5b22a818e2852181425063bbb2a228c8517dd95314f10b36e6b0a802061e6458c540428f39ea92a0434e1c15410832a74e1aa6820861f5458c214c29d386a8a08215c9c46294241ae2e2212a010c6e72194414c334a90c0908814e9d350943328f6e0b24a518e1d5418d41cc61fbb2a8216431ddd95114732c70a9b0264905b27114d401038c298c0a1a838b9d8525094187ae9b28620843d74986508caccb98a4a00818e9506050b32a76eab1a802054e73d49325031d2a4c1a98430fdd95410f31ae0e0a88a29953870550544cb0eb26a618a814e5d7419424187eec2a0429847970997329063d384caa1c431d5da5288421c72a9306a610d69720c5500871cb20c8a80639a98960d5330cd0a4b006488655635445110b94a1084a80434e9d05354021c70a9304429862d64d4821502b4b90c22828774dc1434c4318bce632a422043d74185530822fbb2a629a431ddd9511442087ae9b2c420851d741855308717322a4280638ed526008520c3cc8a9ea010c787558243442a7baac8990658b9516210220c72a8302840865963980540422fbb2a629a415c9c43254031ec2a498aa018d72710c95090764992c028865ca9cb5410320a58e8b02a418d3a750854010338a88c0908818e9506050a3187ce832e640853974d8f5050a9d3a0a4a80632e9d2618c110d50c4a92802065563944210825c392c1a08811edd563100308f6e0b2a8418e666258453082b938886a8063471d15314d10c5ac8b10a710f0d5454b310c7333a8c2992439a94a60140318f4e130ca8195387458e500871d322c02a0634e1d13294241ab4e7aa2a010c3d7599021c4395b20a4902219c5c06154d208f6e0b2a869046f76548520c23bbb2a228c878e9516090431c6cc8b08a81863954d8143086373b0a8a90639654c6050c21e32a929aa010e5553185320425cb84c5218818edd954100308f6e0b24a418c6e7299741cc22eb98cb216218d551610c821c9aa6312619068d644c8510ca1fba2ca990211b1c96550430cb2a63028410e6952181321029d386c8
  | 14 => 0xe9b2a609056970d52520c69d386c8aa0638e152608c520b60e0a1e82a0f2852d814250717322c42a021879926314c2187eecaa0a818e3a54d8143c432cb1cc02a0418e1506050d31a3ae6308a8985397414c4084316322a499081175cf659091087ce83286210c7671194430861eba0ca996211b5d66290c20c6aa8b08a8195cb7050d320ca3d3acc8982210f9d85450b21c72c8a80a01945e7614d31886acb98c3284835c5d7419424199cec2a2641963854181424c33830ec0a9a418b951620c42187aed2a48621d4c7254d329063db82c829a411d9c46550c20e34a8a9ca010c3e74d81518cb35290c0a1481ca5cb5410330c74c9300a710e1d5498f500865c3a2c190e414e1c154d0731ab2e62a2200843d7499721cc2d4b90a2a00814e5d03194021a72e9a84a018e9864cc9300c30e2a6c6a8a412e5c064c8440c9cedb2a641963764185544ca1fbb2a82a2435a5c05454831970e6b0084206566358453082d8b86c8a08832e5d0604c4408bce73288210e666258454c86b5b82c929063535cc520c941caaa6b08a6215aa72d5040c831aaa4c219621ca95252540318f6eab10801046f76548521032cb1ac0296214e1d15014032cd2c5300a710c3d74987524c31d2a0c0a14432edc16190840a6ae2310a89863a54181438c21eba0ca190211edd95214143a74e928c200854f75585320ca2eb98cb210214e5d661500408f2eb32260186b064d85304429d3a886206412e1c96010c408beeca98a790e6862d81544c65cbb6a8206418e9536050821c3ac8a986210c5e73196420431c2a6c0a12418e95160087108dce432c878863a5498041c4354320a4902214e1c15415032e36e6aa0808853874540504ca1f3b6a8a8a618e5806055021a72e930aa010f49320c950086ad398a928043c3951524c4318f2e030aa62147a70194430431d322c028a658b151620c5208f4ebb0286a1539755044008338a8ac02888596d4c6050d4187eecaa0a898c797019443c871c2a2c021a419a5886214143cb2c6298810865553584531021f3b6a8982418d5926114c219e0e2b1a410865953580531061ebb6a818a419654e6014c21b62e229a8020638641492044237bb2a4292870f5d2658cb1087ee8b04a48867261580540ca36bb4a9210850fdd160d4532a74e1aa68318c797018d5110b1b2a2c2210439398d6215332a76e0b18a8904ba76945401022fb9aca212215c5c46314142a9cec29a6490d2f74582520c63bbb2a2288850f9d6640853087ae831aa21064c63189544431caa4c120c439ad886054d21e1aa6a108410e2d64548520428e3a2a629a433c9c66488110c38a8b18849861f5458c214831bb2aa8908434b1d5421092087ee8b2c629063954580540863d384ca19483875526314c21c58c9b12a48845e7399741c82c63a2c0990654e9d4
  | 15 => 0xa870508428871db28c8980618edd56010840c70a8b06649063b54982414830eb24a618821665cc2150040c74a930063884767119643083a499065280638e197644c110ae6ea98aa018e3564984520423cbb6a820661535c9530c820c5ac929042085a872504400825dbb242a00810f5da5414831c6acb326200864d6398b540865c3a2c198c21c614c431011087ce8328658855873553404429a38aa82a2658d5516190c31970ed29a80205c771581320caac39ac4a80634e9c35495232c9ec6312a898c787059543c8726a9ac4298834e5d43150040a72ea218801056b725445050eb8b88a7a00419354d62904218f6eca80a1a164d63988520431c324a4902219c5866015032a3ae7aa4a810e4d75d95320ca1e3a2ca988412e9db5250040ae4e2310a0a1c7975982410870ea9ac221881175cc6510910970ec98a8020559731885050eb9388c7284830f9d265c8730c9ac7310a91964d5398a300828f3a0c2a98430f1d16548430e62a910aa010c3e74d9421cc28eb98c42a2614edc55410110a72e8308a0a166452584424c6b5baa42a8043339db544c832c70a830264904ba76cc94010338a8cc120c811bdd95214a4387eecaa0a90866962980540431cbb6a82066117dd95314f40a72ea192802047a70995420423b388ca21e41669ce4210030cd2c4b00a710e71619805484316aa2c42a0210f9db5454d20878eab20629063b65d91200825d3a6c5882218b552620c4218eeeca88a3a1e59531814390aa6392a6990219c54660904308f2e03288690c3f76550500c69d3a6a5280638e5506050e32a72e030ea89070d54151320ca2fbb2a6298432e5c46250040c70c9b02a68847a70195430871cb22c028a65175da538c030cd4c4b00a99063471590514ca9c3a2c5280638e1506050d2087ee8b28648847976d5040c825cb80c8908815c5d74154241c6cc9308a61063b54982414c22ebb4a9218871ddc5654c840c38a8b1e8298c3d74987538821f3a6ca188431bdd95214a40a3ce830ca610c3e74194328426c39ac110a611b5c8650c01087ae830aa5984767119442042e4b80a8990659a9895014031c74a83028610e5a7614d304431c322a2980614edd163940218f0e0b20a790d2c7258154c429d3a0a528063c3951320c821cb4a7b028410c7b70595420429cba884200611e5d85210110cd2c5300a60866562d4431482e4382c2990655a5cb64d4143878e8b14a018f0c544c8324830f2a2c7a8043179db5454c21d32c6218810861d5498e420cb1cbb6a8206414edd16294031a9aeb302641965963980548c21f3b0a8982419a54a60140318f2e130ca89952f74581520c75431484a00812e9cb6150040c5aa83128390c3d7419732c421fba2c5280631ddd951146328dae4308a68847a70194424c62eb98caa10212e1c1640cb4087c
  | 16 => 0x863aba8c2a1843a6d4c6050d41d50c910a401063464545211021f3a0ca18a411b5c86590f10a6ce3aa2831063a54d81430869cba886200618e9916094d20e92a598aa018e98630c5401029dba2c6a80430f9d065ccb10878e8b04a710e3854582314823d380ca218438719153cc440ad2e1aa2a418e1d6454c530822eb98ca20843875926314c10c9ca6b106210e3a64980520423db82caa1e431e9c36454632e88e2a9a4210e695218121842b838aa0282654e5d654100208eeeca88a221e1d54d8d420c6b4b90c62828517dd95314e21c3ca9318a58861d6454f50086b4b9082a804387dd95310c40ea26218aa010d2e74d4a520c78aaa262188438e9536050c31ab4e610aa010e4c63549420c72cb18c7284834d9c75450410a74e1aa4a810c3d74d95214c30f2a2c628043875516314021a9aeb32264194797614c40082b4b90a8880219c5466008420c74a8b044388539740c5500c61fbb2a818843475cf60d5120a38e6aa48088476711943250332a92c2290816c5c4431011087aed2a4842143d74194214c21eba0cb190212e5d26088440c98a6b16609043d7695052c429cba884200416c5c44210110ad0e4a8ea0a1e5b65d814310e9d3a062a80438e5506050b10ad4e02a4a418e3954181438c6b938864a80434e1cd5410210c76a83028698e3954181418422e39aca908818e9915014031878e8b2a408847975d81320428e3aa8621a611e5c06154843c70a8302429047970195420c7952a2a4a80638b9926214c21ab0e6a80a0a0c797098b5150e97396a8a12618e592609462087ae830aa79055a701865308759b20c2902219a58a6014e20a98e6a92642054c7254d32c4317324c42a0632e9db4350040a72e3aa0819051d7395043c4334a92c010e218e5516014831c3cc9318a408635655931084317b2ca8908431d1d56110910cb0a6b00648866562944310c23d386cb996830fdd95415231a72ebb0484205c471581320ca37390ca218219958a6114c10c72c9304a31856970185520c71caa4c120863c9551528c431ab6e6b22a120e3b54580314830f3b0a6a1a831e9c06590e21ccaa430a6420e7161980530830f2a4c610e21591c56054831cb0c7b02a88865563544511030eaa0c6a08611b5c8650c540a58e4aa0a898d1f7458253086b838aa6282859694c6050c218dae532a870843f74582530863dbb2a0280431b5cb6590d20c72cab26210874932540500cacc3828621e650f9d36508630c72a8b00a818c5e73194400429dbb2a8202213a1c9609052087eec2a0429062f7654842102ac382c8a984317dd95314c418f0e032a868861f6418d5244327b1ec4aa221c6190534c110cb4c6b00a610c5f73595204423d3b6a6a84831b9c86510c2087eecaa0a80853b7058954c422eb9eca10821a618e3150040a76e0b14a9885
  | 17 => 0x9083179cc6510a10e1aa8a926218c7a70997430421f3a0c6a88419654d600c710970e8b06639843d74995328429c3a2c029e4147dcd6055310a74e130aa810e595398241087162a2c421a411e1c16550e21c38a8b188498c7870595428c62e39acaa0a43171cd651091087eecaa0a81862f64189544c7a8a8862980614e1c15490832cb0a6b06628859a73d5040c823dbb2a6282856adc96150040c5aa8312821066562984540c21f3a0c229a212d9c660d0d41c9ca6b106310cd47158e424c716322a4908814d1c56255031c74a930482086986494d300c30f324a6188434e1c1425444287ee8b2c4298571759051004352a12c2210431edc16510d2187ee8b00a690c7970d96434865cb80c8190818bd536254530c6ac8b08a6105a870508424ca5d3b0a6a00819ad976050842cd2a4b00a421de370509210863d380ca21a43ca94a4210030ad0e0a1ca418c6d7518943086b4392c8a8043939d8534c9218daed2944210ce675185324878caa2a72804387d96544c431972e1324622069a6390e401023db82c829a431b1c96550d10ad4e02a2a418e7161980540c236b96ca18e811e5da52d021087eecaa0a990e2e5498831c423db82caa14631e1d94354241970ed90a802062d54588540c69d3ae822066193995320c940ad2e429aa120d667110d520c72c29ec0a1a818bd5062545308beeca98a6216555398630042d53908620641879915314021ab4e1aa4a610db17494510042e5b82c8990658b9916215031ab2e1aa2a610d39759904008394aa242a8043179cc65085408f4e132a8498e3964540500c63db82c52a063a618e5350040ad0e4aa0808852d74185520c716aa2c41884317dd95314d40ad2e5aa2a018ceb75588400823d380cb210219658c6314142cb2c6b06a810d1e73d91540871d2a4c1a90634edc55410020c3ac9318a40855973d515008716aa6c4a1843175ce6510421970ec992802063854980214c28f39ea8a1a411b9db54548318dceda9a4210e5b53580315038ca1887a82859558d51084208beeca98a70847975980310865d3b6a6a00819358d5214840e32a8980618843c7458c504871c2a4c110a419658e601502187ce930ea71070d4310d520c61e3a2c129a2193d965348421e34e7aa0819852e72d5040cc29dbac84202218e9916014f10c70a9306869846f765485290637390caa18210f9d0658cb10d32c621881984cf764c8500cb0e2a4c7a026156dc16454c21c58c8312a68843f7655040442b5394862828517dd95314f41c5ca9310a78846e7614d32c865d3a4c3184210fdd95415021c70a8b06828845d73d9742442b5b82c8a90631edd95410210a9ae4298648845d7398b515021f3a4c3284658e99260d4c2187eecaa0a610c797694f408425c3a2c019641471cd6055031ad2e429ca120c6e72196430
  | 18 => 0x80101340040080000540bc07403c11401002401000000c0002b410811804c0040140f17dc1984b80066f807801c00c0506700100000140fc2500300380800047b0104d8c03801804015802804400402c0000d401400004000c03c0041bc00406078800434013c03c08973c0500941900040040040040142640040000000300400301e00000701e884401000c00801800801800007400133800030c24454051401c0a02c000800005006c03004c00c02000408400001404c0000017f4ae80415d861000c00000c0681dc03c00414800400808c0481d8088000e980440280001240000d98e01f800c00099801003050808c039a800000100700040000080105d00180100000004c04c80140000280a006400403000400c9a80080980642a80000000041800280000007f803c01001004800820800818c0000200740000243dcbe800118c1e008827e53ca6001c000004d4400c00000409c01000800c00028c03002c008054008964000000074f6803000000404800861002c0800680140a46e42e40cc02000408c09804019c0040000040180dc0012f804800c3400f800002c02ca7812403c46803c4dc01012c01165802416804c0180e802ca703e80354880300197a974001c01cc6db74008c3c0b83e01401e49e402402c02c0586c011003c14401401c0940000380001100e81b426cbac004018048004008034010004080598000a700380480080048ec07c07c0140480fc0340000000040880400740100e4d145100090ad06007400c0385840cc01400c0700040200280c0000fb40054c000401800403821c008e080001740000ec03803800011401411c1780000140002582900640458a400022434c04c03405400c00400b4b3a0c299263479cf64553208f0e0b24a710da974085200831caa4c1208211edc16510931c68c9b0aa690d8d74185320cb162a4c5982418b59252d4031aa8e2a9a639055b754c6500c65c3a2c190a21665ce6250040a74e1aa28310d3b76550400c28c39aa8202210f9d36548530e52a9292a018e3a6498054086b5396a8a80638755163d4021976e2b00842059873585401021fbb2a82a4418e1526010530c74a8b06a418d5973105500c6a639aa4292831edd95014031a3eeca98862047a70997420c72d320a698221179cc6510020972e1320422045f73595414861fbb6a818a611e9c0654c810c5aa9310a018e1c6414d304435830ec0a1a83539d5320c9418beeca98a62047776544514821fbb2a8290631b1c9658c5408beeca98a71063964980520421fba2c029e43175da5314021c5ca8b10a7884797099543c872631ec4a92215a5c86194241c58c9b12a68863a54980500c68e39aa82a2210fdd95415020ae2e2310a0a1c7a7019443c862f39eca10e818e9916014e218f4e03288710c7a701895110e3d380ca9
  | 19 => 0x9f19d40242640f412605400404c0280a10d004801008800001982c0980180080380e00283441f806000000016001802a37eb3802400553807004400400009009001837403402401c00006c014014018024c8801c08c0480000001ad78c00283c0301a801c00014407c00400407406474405001c02000404007c0dc0000100000080680780b803803c0341e80080040008200500150d00f01840000040000bc02800000000c1740144fc010068044000a280140348d8024cb801803000406c00c000015af8b8800021010404801129404000802802002c2586a0a440200000380000b81580092d01a00000080000900440e852445c0280c802001c0412b00700b80103540011e800004400c0100140000b82301c403001006c03c008000004db403cd140a400800800800428009002007804400418404c0040240867080280040d00193bc00004805800dee40044300e001006c000000268dd40000041f80440700a400000400c00401d6e4014c3c0040400880040001cc0d80141741ec19c0180a00040000780080250bc014f6cd000040a00000500ac0040000380280d401c1f80200da22c4f45e4044008d3c0080001780080ec0100040343b015833017c0e00005400040000040040087400001c01540200140000580c80080b20b80181b80380040001b404415c01405d1040042dc0e801c08000800035c00800001d14c0c801807001c0340540080540f42a022807002400405c05800004401c0040200000480001c800c01400c00000001062d7c8014c08000c4576000530806402c00c8e43941ac1fc068038160010564021ca40980080041b00101ac0600000080280292e001c00000c00000003001c0341e400402c0740380000000dc16006001468805c04000406400048c0002600200dc00001c16406801000004cb540002240340081809ec1600000583d81b800aa680180b00311302f80002ec8100188fc0081655ec0000180000d80a000014400800001d7400100209340000000380080280100040000800704e007c03800c0200001080240580080000200002ec0100480080000000380280080245300181fc0540140000240e006c06c13c0240fc18c00007c00800933001803c02400039c00c2240640040246040300500000040e805ce88004da807011003400400401400c00001800c02d20400c1041ec0f40140fc01c00044000000ce2c02917400000003000007003803c00808c74c00000014002007c00800401c00402001000005c00c00002800001c00001002884c19802802407945881800807c00400c00002c33c0140000000001cc0
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x55348421a18835506050f10b088050c4354831d08731c95410110c18541cd6088530b11831514144010918835d54110020ca1625c44210110b05841c532544328a8825da3150040a4581195320c940c28549cb6050d20c28749896014f2089a839cb6550040a188650c4354241c187414d600c910a18805506350731c25625c462151308b1811d83250040aa0805096110821d41735442148020a8484584614c832a458114d620c540c30745855014032c91635c44310110d41535c24148421e1064544314c030a30805516115032d21745442148020c15635c46315120e05544c9610cb1092a82dd64310210d10735454110030d05545c4544c832a198614c4310110d08744c95014032a28825506050b10a28825506050a31d09735485250040a28825806055021b41801c532544328aa86dc14350842a28805526290c32b05841c5524c431e4132585501403292a829d74110330e11635454110030a1a83d506050d20ca1745c0614c92192a82dd64310110d0a735cb5410330a18805526390832c91745c0614c931c18549cf60509308aa829cf6150040918835d54110110a908050d6110c31c88645c8314c03089987190314c030d41325c43254241c197518c3150040d21525c45250040d21725445150040838865d43250040d10535c44310110e0554589310c710928825d5411011091a83dd64210020a2a82d506050930a44854c9610c910a1b8650c43d4142e05535096110821b41801c5524c431c88635c83150040d09531c14210821b05841c55348421c51635c46314142a2880590520c941c29751882150040c28541c96090520c28541c9608c520c29769cb5410320d1174544314c030d09535c85350040c2874149600c910c287414960c8510d41525c2414c431c29651c941100208aa86dd1304802089a839cb6150040928825d44310110ac080584614c832d09754c83250040d11735445150040a28825906454021928825d54110030d0b731c95410110a2a84990524811091a87d51300c120c18541cd6090530b0880550544c832d20725454110020d11535c45350040a28865084254241a1883580605503191a83dd642102108aa829cf6550040e21625454110020c187414d60cc510a28805506250721b21821514144010d0873dc95410110d05435c4435483191a839d74110320c187494d600cb20c89731882150040d09545c0544c832d21425c44254021929859ca4310020a1880590530c941c88645cc214802091887551300c310a29861484210110d11435c44354031918835d44210110928875512008310c19651cd4110030c61625c46214143a918118c3150040d20525c44210110d4172544314c030aa1811882150040a18835506050e21d09739cb5410320a1a84990534c110c88764c8325004091a83dd64210110
  | 1 => 0x7d0204003500492b053302000e1d070b30310002090000120705050000000e1d04270119170702000000000806000214001002420f051600030062161f00000000611ac45635c45208540e055458d2108710a18835906454031e09644c950140328a9871902148020898835da2150040e20645442148020b41801c
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x210036015d40c40b9b0231042a0081c00645cd51085200828432c292e221080887001d1325855014032a40c88c6b9062a00814219719151085200828232c29ae221880886085d5811882150040a8048286b8886a9063a01532014258442086903223b2641928020540241545c4544c832a044b2ea99064a008181175604630c5401028232e322a218a601870019172544314c030
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1798
  | 5 => 7915
  | 4 => 3074
  | 3 => 144
  | 2 => 16
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | 2 => packedAt gbK2 (i*71) 71
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => 2*((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 1)
  | 7 => 2*((h/27+packedAt gbK7 (640+(h % 27)*6) 6) % 40)
  | 6 => 2*((h/634+packedAt gbK6 (48546+(h % 634)*11) 11) % 1798)
  | 5 => 2*((h/2701+packedAt gbK5 (300770+(h % 2701)*13) 13) % 7915)
  | 4 => 2*((h/1052+packedAt gbK4 (150626+(h % 1052)*12) 12) % 3074)
  | 3 => 2*((h/69+packedAt gbK3 (8640+(h % 69)*8) 8) % 144)
  | 2 => 2*((h/12+packedAt gbK2 (1136+(h % 12)*4) 4) % 16)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe07fff01ffc7e03f1f1fe3ff1f81c0073f7cc
  | 1 => 0x1ff81fffe0fffffc01fe3fc7fe3ffff18c78ff
  | 2 => 0x1fffe0ffff007ffffe003ff8ffc01ffe0f8f0f
  | 3 => 0xe00000ffffff803fffffc000ffffe00ff00ff0
  | 4 => 0xffffff000000003fffffffff0000000ffff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xc2b0c611c6289440b0704e097048c46031b3cc
  | 1 => 0x44124022424020080092124212124920845055
  | 2 => 0x88610a448819481552002490a48112c60a8d0a
  | 3 => 0x145948910900ca665248000c925808b500ea0
  | 4 => 0x1186180e1ce2713b89c939240006030def6000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_40539
namespace PEqualNP.Outside.L_meta_40539
open PEqualNP.Outside.L_meta_40539.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 16 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 48 := block_range (n:=48) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 144 := (concat bgb_3_0 bgb_3_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3074 := (concat (concat (concat (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 bgb_4_288)) (concat (concat bgb_4_384 bgb_4_480) (concat bgb_4_576 bgb_4_672))) (concat (concat (concat bgb_4_768 bgb_4_864) (concat bgb_4_960 bgb_4_1056)) (concat (concat bgb_4_1152 bgb_4_1248) (concat bgb_4_1344 bgb_4_1440)))) (concat (concat (concat (concat bgb_4_1536 bgb_4_1632) (concat bgb_4_1728 bgb_4_1824)) (concat (concat bgb_4_1920 bgb_4_2016) (concat bgb_4_2112 bgb_4_2208))) (concat (concat (concat bgb_4_2304 bgb_4_2400) (concat bgb_4_2496 bgb_4_2592)) (concat (concat bgb_4_2688 bgb_4_2784) (concat bgb_4_2880 (concat bgb_4_2976 bgb_4_3072))))))
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
theorem bgb_5_1920 : Interval gbAtlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6144 : Interval gbAtlas 5 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6240 : Interval gbAtlas 5 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6336 : Interval gbAtlas 5 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6432 : Interval gbAtlas 5 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6528 : Interval gbAtlas 5 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6624 : Interval gbAtlas 5 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6720 : Interval gbAtlas 5 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6816 : Interval gbAtlas 5 6816 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6912 : Interval gbAtlas 5 6912 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7008 : Interval gbAtlas 5 7008 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7104 : Interval gbAtlas 5 7104 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7200 : Interval gbAtlas 5 7200 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7296 : Interval gbAtlas 5 7296 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7392 : Interval gbAtlas 5 7392 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7488 : Interval gbAtlas 5 7488 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7584 : Interval gbAtlas 5 7584 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7680 : Interval gbAtlas 5 7680 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7776 : Interval gbAtlas 5 7776 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7872 : Interval gbAtlas 5 7872 43 := block_range (n:=43) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 7915 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 bgb_5_576) (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)))) (concat (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 (concat bgb_5_1248 bgb_5_1344))) (concat (concat bgb_5_1440 bgb_5_1536) (concat bgb_5_1632 (concat bgb_5_1728 bgb_5_1824))))) (concat (concat (concat (concat bgb_5_1920 bgb_5_2016) (concat bgb_5_2112 (concat bgb_5_2208 bgb_5_2304))) (concat (concat bgb_5_2400 bgb_5_2496) (concat bgb_5_2592 (concat bgb_5_2688 bgb_5_2784)))) (concat (concat (concat bgb_5_2880 bgb_5_2976) (concat bgb_5_3072 (concat bgb_5_3168 bgb_5_3264))) (concat (concat bgb_5_3360 (concat bgb_5_3456 bgb_5_3552)) (concat bgb_5_3648 (concat bgb_5_3744 bgb_5_3840)))))) (concat (concat (concat (concat (concat bgb_5_3936 bgb_5_4032) (concat bgb_5_4128 (concat bgb_5_4224 bgb_5_4320))) (concat (concat bgb_5_4416 bgb_5_4512) (concat bgb_5_4608 (concat bgb_5_4704 bgb_5_4800)))) (concat (concat (concat bgb_5_4896 bgb_5_4992) (concat bgb_5_5088 (concat bgb_5_5184 bgb_5_5280))) (concat (concat bgb_5_5376 (concat bgb_5_5472 bgb_5_5568)) (concat bgb_5_5664 (concat bgb_5_5760 bgb_5_5856))))) (concat (concat (concat (concat bgb_5_5952 bgb_5_6048) (concat bgb_5_6144 (concat bgb_5_6240 bgb_5_6336))) (concat (concat bgb_5_6432 bgb_5_6528) (concat bgb_5_6624 (concat bgb_5_6720 bgb_5_6816)))) (concat (concat (concat bgb_5_6912 bgb_5_7008) (concat bgb_5_7104 (concat bgb_5_7200 bgb_5_7296))) (concat (concat bgb_5_7392 (concat bgb_5_7488 bgb_5_7584)) (concat bgb_5_7680 (concat bgb_5_7776 bgb_5_7872)))))))
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
theorem bgb_6_1728 : Interval gbAtlas 6 1728 70 := block_range (n:=70) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1798 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)))) (concat (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 (concat bgb_6_1152 bgb_6_1248))) (concat (concat bgb_6_1344 bgb_6_1440) (concat bgb_6_1536 (concat bgb_6_1632 bgb_6_1728)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 40 := block_range (n:=40) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 40 := bgb_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem boundgb (cert : Complete gbAtlas) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafee8ecc0feeaeeeafee8ecc0feeaeeeafee8ecc0feeaeeeafee8ecc0feeaeeeafee8ecc0feeaeeeafee8ecc0feeaeeeafee8ecc0feeaeeeafee8ecc0
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276677824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40539.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[2,3]⟩,⟨.and,[4,7]⟩,⟨.or,[5,7]⟩,⟨.or,[1,6]⟩,⟨.and,[1,6]⟩,⟨.or,[8,11]⟩,⟨.and,[4,10]⟩,⟨.or,[9,13]⟩,⟨.and,[0,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276677824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276677824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40539

open PEqualNP.Outside.L_meta_40539 in
theorem PEqualNP.Outside.L_meta_40539 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276677824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276677824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
