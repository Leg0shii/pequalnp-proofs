import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36348.Model
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


end PEqualNP.Outside.L_meta_36348.Model

namespace PEqualNP.Outside.L_meta_36348
open PEqualNP.Outside.L_meta_36348.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 5, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36348

namespace PEqualNP.Outside.L_meta_36348
open PEqualNP.Outside.L_meta_36348.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x8c40480e0520a031160143bf43bd43be42bc42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x4c000108ea98852c525065ca5205554430
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => packedAt s0K4 (208+((h/4+packedAt s0K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s0K3 (111+((h/1+packedAt s0K3 (108+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 2 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 3 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x8040888500808002904c02240229109408d131
  | 2 => 0x10891048252442502a11214921422528a22486
  | 3 => 0x895229034a480ca58426541654054a85454b18
  | 4 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0fcccfcc0fcccf0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36348
namespace PEqualNP.Outside.L_meta_36348
open PEqualNP.Outside.L_meta_36348.Model
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
  | 0 => 0xfffff03ffffc183fffe0ffffc1ffff0073f3fc
  | 2 => 0xf83ffc1f07fffc3c1ff0f03fe1e07ffaccccf
  | 3 => 0xf003fffe007ffffc01fff003ffe007ffcf0f0f
  | 4 => 0x3ffffff801ffffe000003fffff801f00ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x210011842000200442601118c022310c01515c
  | 2 => 0xa225228c84a90941d0a90a2952145254a4c4c5
  | 3 => 0x454a45106952129c2152a052a540a4a94b0b0a
  | 4 => 0x4a7388294c1b5ceab41888833999c031f00ea0
  | 5 => 0x8c630e318e639f33399ccce0311100c1fea000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36348
namespace PEqualNP.Outside.L_meta_36348
open PEqualNP.Outside.L_meta_36348.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xb0011124007401012ad695383d496264462636000000048f821a1c425425c01a323852730a83003ca02a028b0001068c0110032408c32d300004a052ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x917d354ca41000c521249504295c00310114c93d584ccc010850002c0068ecac0000e000d0700c9cdc0130004400a00058014000b94800000001192971600000000154e4480000a800c00024000098d9781c008c4019740080007c00e80000010c014460000000000000f800f400006c0039511d2c1400b400000000003c01102001880000000001685c0835800000d4796cbc0455840088b0000164f00000fc007538008464000000040000140802000000000a020006042600021c060400000a1804000006020206073d5490edca521db54a43cfa9a873e5410edca421db54843af298855d5310a7ca9994f55332cea1e656d538cb5e87196b50e32b728c659d434caeea2995d14532e7a9a65af434cb9c86996b50d32e6a1a658d434cbcea2995b14532f228a6564514ca7ca8194f55032b7290655e53d06baa7a0db94b41b6a96836f52506d8a4a0cf953319eaa6636e52cc6daa598e750e31b7a92636c524c67ca818cf55031cea18636e520c6daa418de94031bca80636f53886daa710ebd0e21d6a1c436e51886dea610db54c21d7a1843ad43086dca210f994421f398843e431086dea4a05b14940af298815d53102dca4205b54840bb2888175511027ca9984f55330cea1e616e52cc2daa5986750d309f2a0613d540c2dca4185b54830bb2886175510c2eca3105d546209faa2413c54483c843885b94a10b6a94213f5444278a88857d4d10ae29a216f52442d8a4887908510
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xe4820140050131c93c334100b40420600a00044c00608065287154314532a3592434cb8543d4532c350c514cb854314532c9d0c514cb464314532c950c514cb454314532c150c514cb0d4354831c650d500c70f5350e21c354d4308665650c421e150c31086e1600c421c350d52cc2646154b308758c54483445308510
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x880006056550c3108740a1ac0188438150c6154b30
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
  | 5 => packedAt s2K5 (826+((h/15+packedAt s2K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s2K4 (2937+((h/33+packedAt s2K4 (2673+(h % 33)*8) 8) % 172)*8) 8
  | 3 => packedAt s2K3 (833+((h/7+packedAt s2K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s2K2 (150+((h/1+packedAt s2K2 (147+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7ffff81ffc3fe0fe1ff0ffff87f03fd23f39f
  | 1 => 0xf81f0ffe0ffc3ff0fe1ff0e07f87fc1edccce7
  | 3 => 0xffe00ffff0003fff001fff007ff8001f1f0f07
  | 4 => 0xfffffffc3ffffe000007fffffe3e00ff8
  | 5 => 0xfffff000000003ffffffffff80000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x3042008c2084000120230123180908c401518b
  | 1 => 0x12c4111465005050620d1045288258484cc4a5
  | 3 => 0x618eaa28c3aaaab71116aa0a75503193170f06
  | 4 => 0xc510cc410a220b2a954088104664a303a00a50
  | 5 => 0x861888718c3333ccd998cc9c0440c203faa000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeee8800eeeeeeaaeeee8800eeeeeeaaeeee8800eeeeeeaaeeee8800eeeeeeaaeeee8800eeeeeeaaeeee8800eeeeeeaaeeee8800eeeeeeaaeeee8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36348
namespace PEqualNP.Outside.L_meta_36348
open PEqualNP.Outside.L_meta_36348.Model
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
  | 0 => 0xffffc0ff87f843f87f87fff87f07f8093f73c
  | 1 => 0xf0787ff0ff87ffc3f87f8703f87f83ff6cc9cf
  | 2 => 0xff807fff0007fffc007ff803ff8003ff8f0e0f
  | 4 => 0x7ffffff807ffff800003fffffc01f00ff0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x6110046210800804809809198091188c01531c
  | 1 => 0x250088a2400a0081882882288825092424c145
  | 2 => 0xc23551443555455c44555053550232598b0e0a
  | 4 => 0x8a466208a441566a55044082664a6011d00ca0
  | 5 => 0xc64438cc66667b3666664e0440c4061fea000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36348
namespace PEqualNP.Outside.L_meta_36348
open PEqualNP.Outside.L_meta_36348.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xa437d53486f8a690f714d21ae29a43f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821f799043ec32086fca210fdcc421fa18843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e817e52d02faa5a05f94740bea8e817d54902fca7205f54e40df21c81bc43902fca5205f54a40dfa1481bd42902fca3205f54640df20c81bc41902fca1206fd0240fda04817f53502f8a6a05fd4940be292817f51502f8a2a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40df21881bc43102fca4207b94840b7290817d52103daa4205b54840dfa1081bd42102fca2207d94440bb288817d51103eaa2205d54440df20881bc41102fca0206fd0040fd20081bd40103f280206e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c617e528c2faa5185f94630bea8c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220fda0441f840883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc84907b50920bfa8a417c51483f680907e10120fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf288217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0x4010201b03c5f0340a0000c01810014030000a008040a40200800014000040001007014270300802c04000000040100c0e0102212c0b00002000290445f00403014010080000afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa8287fb5050ef6a0a1df14143fc28287785050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1217e94242bd284857d5090bf2a1215e54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cafca2197d94432bb288657d510cbeaa2195d54432bf28065fa500caf4a0195f54032fca806579500cafca7a0df54f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0df14941dfa1283bd42507ee82a0ef90541bfa8283fb50506f6a0a0df14141fc282837850506fca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498fbd4931b7a92637c524c7d8a498db14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea9063de320c7b86418df94431ef98863f6310c7ba6218fd4c431ea988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fdcc721fa18e437e50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21f799443ec32886fca310fd8c621fa98c43ef21887ee4310df94221bea84437f54486fca890df55121be2a2437f53487bea690d7d4d21bf29
  | 2 => 0x18a72ea350f21514825ac241dc266448001d1032048f00000000d92209b000000129ff0b2600f386c0e08b40621d2b2888131532d22ccd9808098438299df406848c222042822c011421ee4983b9a50000347180000057800000000058cd89f0cc518dd9c03562f4659ea20883cf59de44c1f1159cf19e000c90f412e764309fd0e4000ca08d00062c1e0320a800000000124000001034540000012d2a80a44400042e000431d229c000000000000c00012f00000103000000000b218d486000f68000005c4218001b223c7008c242000000b622655c0019a23600118105360089010784088a4e416d1ba69d1185d38a2a4de8001ac0000e03327053cdb8ec28a108f89913aa71823a1c00000110a19000000b3000470000001e60286d0350a621e334b91520fa1388d0d5000124848640747301a0960a02f84123400e39cfa8003ae1bc550fd02a2141f01704024cb791640a3942b2162ce1cc000ef0002106d95a0005d89a8c41f40a02e0132387740006b00c010002492c2854a590d41a0007d99f000000000003f20001e8000f4000d00ae000478f61c300030c4c9af3a86f0fba250009000008a27c2709e18806e8dc2d8e20f22d0481e11ae4e8f106d26e9146983f03a000a18004022c0000f90005608608110042c9e8522726d4cf06e0ce004058d128e0002f8ed15e00117031014704250893c6534319e50000004d000140734bc8da1922511d076000450638003f0000b280027e4c4f42282b88bc808f03e8688951f24200b0c11f02dc2e05b93b05c3c89123320c304b01283b0275139150d0000560000d27408c0fc04e510c79fa3fc2acdb19800057c5d0414120008e925000540000001c86586c248000000000872fe5240299d000000000834266f8f7a0e0008d8001d30ca8fcc18000124a44c0000c4684079ba1d4728508fe2fc45ca50f146a06cc29302005ecd49da18a664d6a003ac618bd16c1943cc529a83d20ac59207076428c3a470207ccdc8451c2520971cb2583ac3888e0b047c6301e4845cc6f246346301041a60342a0740df3ec5dc518240fe8b0ad84612a87c0021803e000000000b41781aa2405a3d4690a2000000001230703083d9684363e0e2170054038be0bf472000c70002aa0003a956178629088000008c4ca981354000221db000420000741723fc7b20b24e004000301c010200180b01007008020780600c04004040241802404008060300201017010050240104005000060000d0243900005068080080d044050000003c00018060200704800000080680b0140100c040400100400008090081b00005004010000d00005000030081d0002a008000041400001010080001f03c05008020000f0000101c5001c0d0642100c00008000000807001000140040a0d4010000c0880102c1600000010010000302
  | 3 => 0x6910523c0228c8e39b20c0134488003924442aa3e2824402592b09e0611d9360060bc810001488300021a3122d41c9fb2683206e1b832e5d02898c358330589bf1cc340921630fc7f05695d35c64c8c8ee1d25e0e110747a15c9921e240338f70bb39c640b117d000084a60002805a8d889e0806701
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1530874c6254c21d5185530863e6414c218f590530865e6314c219d984530867a6014c219e580530874d53cc8219b594320867565cc421d554f31087c732cc4219d5943108755530c421f10c8310875553884219bd9521086cc63484219dd9521086d46348421d554d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50087586054c40c754e43102b96010c40d394e521034d5394840da982521034e5354840d354d521031d53d0840ae583421031d5350840cb94942103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103374254440cd50951103706054440cd54641102b96010440ae592401023f65500409ed9540102bb6550040ced9540102b86350040e694d40103995350040aed8940103aa5250040ea54940102b86150040ec94540103b151500409d98754cc27561d5330b618143cc33b5410330b658c40cc39a43103309b988548c26d62152309d984548c27561152308f992528c23d6494a308f992544c27b60551308f994544c31d6315130c7152434c25c6550d30ce153304c25e63150309b988540c26d62150309d984540c27561150309e594400c339541003097d95300c27b654c030ae191300c32e62953208f99353c823d64d4f208f99053c823d6414f209d98453c82756114f20cb95142c825e63152209758c548827661152209d584548827661d4e209d58753883395410220b658c40882f16110220ae19130882ba64c822097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d20ba982424826c65509209e99740483395410120b658c40482ea6210120ea50840482f161101209e19530482b8644c120ae993204827a60d50209798c540825d63150209b988540827661150209d584540823e6414c208f59053082766114c209d584530827a6014c208f992520823d64948209bd95200827b65480209798f54c425d63d53108f99353c423d64d4f108f99052c423d6414b109798c52c425d6314b10bc18141c433b5410310bc58440c43b241103109798c548425d63152109b988548426d62152109b98b538426d62d4e109798f528425d63d4a108f992528423d6494a108f992544427b60551108f994544433561151108f992534423d6494d108fd91534423c6454d109bd89534426c6254d108f992524423d64949108fd91524423c645491097d8d524425c6354910cd15241442746550510ce15220442786548110ce151204433854c41109798c540425d63150109b988540426d62150109d984540423e6414c108f590530426e6214c109b588530423e64148108f590520425e63148109758c520427a60148109e594400433954100109e596100427765440109ed9510042b86444010
  | 1 => 0xa9ead25aaf1bcb89269088a000000004a0028ab7000269dc438004680039ab03daeca9a140a800a59f65a0000023661a885897a002f0479be000465199c222ce00238832e4bb80000260151ee92836000000522a109ea260000000000001000000080400c0500400000000000000c0000400014080240000400004000000001c060680600406008060000804c02054000000202c040140100c000000904404000030000300002018000141601801000100000003c0c008000000400002008020000100c090180205c01004080040000800004010080b0080800006018000180f000060000200800004040040d0240300001010010200001e7a6094b439e58252d0f3a43141438fd954310eb86050c4397d954310eb86050f42ced0a5090ab86050d42ae9824250a3f65508429bd954210a7b60553329e18154cca3f64543328f19150cca7a60d52329e583548ca7661951329d586544ca7761551329d185544ca7b60551329e181544cb673214532d58c8514ca7661d50329d587540ca7a60d50329e583540ca3d65950328f990540ca7661150329d584540ca7a60150329e580540ca5f654c832b5185320ca6f654c832b9185320cb365494432cd552510cb365454432cd551510cb573254432d54c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500ca7a6094b419e58252d073b4214141ce508505073a41141418fd9541106b860504419dd95411067a60d53319e58354cc6d4614cb319e983548c67960d5231b5584328c66e62951319b58a544c66f62551319b189544c67b60551319e181544c63e64149318f590524c67a60149319e580524c72e6414931cb590524c7656114931da980524c769601493197997324c74c52cc931d3149324c6d4614c931d914b314c74c528c5319ed81540c67860550319b988540c66d62150319e980540c679601503197596320c6d5610c831b558e310c65f654c431b3189310c677654c431b9189310c6d7654c431d5d95310c7c7624c431b5189310c7c4624c431b1189310c755524c4318fd91500c63c64540319e98354c867960d53218f99053c863d6414f219e98053c86796014f21d5d4c31c867b60552219e18154886e5610ca21f10ca3188754534c621b918931887c7324c6218fd91508863c64542219798e544865d639512197d8d544865c63551219ed81544867860551219798e534866f6254d219dd85534865e6514d21d55845348676658c521d514e3148674654c521d514d31486e4624c521d514f214874c53885219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c755
  | 2 => 0x91800000000016a001125980000172000c4000d8000006e000590000000000000ae9f4a38006c114ae00005a9a0022000086000ac1c12c4aacc4ea669c2a85321c018a28414ab681000102000088621e1318ea52307a2862e9ec002d8690fa0883c1a000b080007800248000020e000283195e300aa0013c2f00073800000000c92e442023e000790564a0120027494800728020703ea8ade9f0003080064a7a192087400000284ab90c6090a6ca8c69a7e68aaa0023e910b8000000000006800810040024e001448a03a8b2a0990200013400000b200000000b50eabc8e8a622200078780a425a800b8902098a3405e768dc0000086800920009b800000d26b232031302d0b050184550f05b1d41ba2458136760528f00009000538005f170000003508c8180054800000000000013a900024cab17e7f02c7100056974899f24200085a78002caad8444c9d6002d6b98fe000509895097000458000008e720000000000000002c40025600000002d00006602800000006d018a720a49000000d600148ac8ee6eae85d8000000041a507e000001380006a32a1280000630002b89e7c00016000388da6a000b49e6950007ea68a91423d0a6700e01000e210386d874002824002600072332769a80039000000000007a77a5800118000000011c3b0001b00025000000005585c2d848baa407f8006522e00000730001800000034af800bd0005b8fc9b09c000c8000de28076a49c26b8002c92057180560009c8002f9aa8e998000006686297ae000000620ceb19044f9e220190168000007c67830748a8719225e0f28d196002c0001a01f
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x3440000060000004c92cf1c045408154e14830a4120c004ca002714b22c029263915d4624c431d0ce83126218e8574189310c761380c498863b05c0624c431c88a63126310cc676cc93188722298c498a43911886154c21c8acb9966210d45750c8310862a3b2a690843c254d5250040e22a6a8a802072152545401029938ea820661461cd5410120a60e2aa08090689635084048350a12c220241469cf5410310
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x10100c05755d0624c431c41755c0624c431c81745c0624c431
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 586
  | 4 => 379
  | 3 => 22
  | 2 => 3
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
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (17772+((h/195+packedAt s4K5 (15822+(h % 195)*10) 10) % 704)*11) 11
  | 4 => packedAt s4K4 (15662+((h/126+packedAt s4K4 (14402+(h % 126)*10) 10) % 550)*10) 10
  | 3 => packedAt s4K3 (1113+((h/7+packedAt s4K3 (1078+(h % 7)*5) 5) % 29)*6) 6
  | 2 => packedAt s4K2 (183+((h/1+packedAt s4K2 (180+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf83ffff01f1ff01e3e3f8ffff8e07e0033f67c
  | 1 => 0x7fc1f8ffe01fffe03fc7f1c07f007ff9ccc87f
  | 2 => 0x7ffe00ffffe1ffffc007fe007fff8ffe0f0f8f
  | 3 => 0x800000fffffe01fffff800007ffff007f00ff0
  | 5 => 0xffffff00000001ffffffffff80000007fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x98c3011c2242206060982473823123011563c
  | 1 => 0x129441224648c0601a429089490424d0c4c855
  | 2 => 0x210092448805008a40052412124909220b028a
  | 3 => 0x629648914106534ac90002464964045700d60
  | 5 => 0x4431800e189989d93126493800180187aea000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaf8c0f8c0feeafeeaf8c0f8c0feeafeeaf8c0f8c0feeafeeaf8c0f8c0feeafeeaf8c0f8c0feeafeeaf8c0f8c0feeafeeaf8c0f8c0feeafeeaf8c0f8c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36348
namespace PEqualNP.Outside.L_meta_36348
open PEqualNP.Outside.L_meta_36348.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410fbcc821f6190437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940bfa8a817c51503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6205f94840f7290816e52102faa4207b54840b6a9081bf421037a84205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c617e528c2faa518778ca30ee194617e518c2faa31877cc630ee98c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa418778c830ee190617e510c2faa21877cc430ee988617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220fda0441f840883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483dc84907b50920bfa8a417c51483f680907e10120fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f481087e50210fd98421f830843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fd20221f940443f660887e0c110fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf288217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xc5150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e85de53d0abca7a15f54f42eea9e855d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf28485fa5090af4a1215f54242fca8485795090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f721665ed42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7197790e32eea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6197790c32eea18657e520cbdc84197b50832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d06fca5a0df54b41dfa1683bd42d06fca1a0df54341beaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53107bca620d794c41bea9883dd53106baa620df94841f7290836e52106faa420fb54841b6a90837e511077e8220fd90441dea0883f541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf28463fa508c6f4a118df54231fca846379508c6fea898df95131beaa2637c544c7bc8698f750d31bfa9263ef524c6dea498df14931f6292636c524c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f721643ed42c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ef32887d86510df94621fb18c43f531887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487dc8490fb50921fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021df2a
  | 2 => 0x6a0002690741a4f48390001800007e1b40012e1dc4c4134a82640f68289d1d32fc96c230850e482ce19734be90c82a472380009422026244451a4d0da680fca194ae4bc15271496400e58832c0440600fe0685887916c3c80011c8653a440c6ba4f28e6e0639150007d8b407a0ec57c5919a32e8d4571b72bc338f298a412074292440225bcdb1781ea1c04c8014382dcda0770003f5379a423c5242f1934545745f1423ba288b900000046c5aa6724e8cc00054000000001220004c1358001886501b8a01ac0788c9894069a00200025430d10a530000b53a138338000441292ae6c8e81852a6000000973fa1291e8000003c40021a00010c928264527550c1de000000ec9963ee2240500e3cc2e52ea3c38a07c4800000001800104088000201b004008400107318000a582f20c80928a72264914cc16d1e877c498004a84682e12c3c48b01e18700002c2494e1a62f0240050fe98443a1037e6100022b1a88c04f0511a05207025846e1f03e9ac2242ac0022400063cac14d248000521544709550a1f00cc16cb09a61b09642b86f26e6188985525c590228000009a84221d02c56ce40411f63480b9ce2cc6b4450e505606d0692d1623b12900031653c001ef498000001142a24240020f4e6000f013c490390540563782ccfd1a107a898580a51c269cf1a3a0ea3450399f0e629c5503131a7000483521e274a016e06033062867302854a19db3b488c77a3f4243fc658923c2020531264923b49aa631b85acbb17401e5052510133c2fc6aa41038548139cd3063c12d10a42e5186314c0f00fcd717c3827d4569fe2aa13cf599527636cf71080c4744758503ac270371ed0846d4b487437a39c5c1ff23a22c1b1803327312023608e8ec858001f0160c41a20065dca51e83722d0ad05a2300010da1138c4cc860cf256645370073246e8770c81c401c000045501801134000040e018200880300849000000180000400000030d41909c03080110049d0001a19c00000080500300407018000102a00c0a00401000020201a0082e0ec050140300400020040002405c0a038010040c00810008050200201c150d80000407010280184900c03020000040c0381704c080440000423000020001e00004018000206c0000200c0000804000060081405c33000020000402002028100000101c1d0000204002084110000a0700d0080600401040110040700011000020100d0040100805080000000a0000d0000000404004010181e01c0b018180100000c0b0140f0000000428000010100201c1001805000020280c0100b0000200c1fbf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877
  | 3 => 0xb399d0003a07ca771d2258430e322c174488fc3366ed0f1a53628000908d2f458c6504b39e6f81c17f2f28b43c80000000119123000000000000005c00020135218c0006b3a80f800265192000810002402bd3a80038e8140a8a90c247c160810987c8d98251b20080000013e0010409535e0013817d0004d06106a47c9390b0000482609e9d83e6000400000006ac2f8534ac0010725e000998d50f33d43dc271652b2304001ec0282380c96a2e22f4080000000b8000000000000022e0005140c2220000000000000000000121000000000004620007b000000000000001182d9280002b8034002420009b4fd8131428183422527c030fc10d1cc89ceb82306679c5d871158980ba89b40837c001820008d13b0000000c8ab0000007d09b20c00023c00059000638000641bc640bd83b0007243600022e208001fc39400075000000000e12130000000010e000001361c400068c9f9f10525107d2280004e5178dd1280a04d0ba04487c0d24619a
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xd521034d5354840c754f421031d5350840cb94942103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103374254440cd50951103706054440cd54641102ad6210440dc546401023f65500409ed95401037151500409d98754cc27561d53309b98a54cc26d6295330b618143cc2d96310330bc58440cc26e62152309b588548c27661152309d584548c23e6494a308f592528c2d5610ca30b6580328c2cc624c630d5945318c26e62951309b58a544c27b605513097195434c25e63150309b988540c26d62150309d984540c2756115030d3548320c2d5610c830b3189310c2796510030ce550400c2f1611003097d95300c27b654c0309798e54c825d6395320c798e54c831d6395320cb98a54c823e64d4f208f59353c823e6414f208f59053c82766114f209d58453c832e5450b209798c548825d63152209d984548827561152209d987538827561d4e209798e518825d6394620b658c40882f16110220ae993208825e63951209758e544825f63551209718d544827761551209d185544825e6394d209799453483596014d20d314e42482ea60909209b195424834c53509209e997404835853d0120b658c40483585310120ba98840483a94210120bc5844048358538c1209e19530482ba64c81209e983540825e63150209758c540826e62150209d984540827561150208f990530823d6414c209d98453082756114c209e980530823e64948208f592520826f65480209ed95200825e63d53109758f54c425e63153109758c54c426e62153109b58854c425e63d4b109758f52c423e6414b108f59052c425e6314b109758c52c42f06050710d694f40c435a5310310bc58440c43b241103109798c548425d63152109b988548426d62152109b98b538426d62d4e109798f528425d63d4a108f992528423d6494a10b618d20842da63c42108f992544427b60551109798c544425d63151109b988544426d62151108f994544431e6315110c758c544432e6215110cb58854443356115110ce580544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524433454905109d195414427a6590110ce15240443b241901109e195404433854501109e997304433854cc110bc9873044338540c110ce15220442786548110ce15120442d86348110bc185204433854c4110b698f104425e63150109758c540426e62150109b588540427661150109e980540427a60d4c108f990530423d6414c109b988530426d6214c1097d8d520425c63548108f990520423d64148109798c520425d63148109e980520425e63944109758e510427965d00109e59440042f161100109e596100427765440109ed9510042b86444010
  | 1 => 0xcb1e6395032cb98a540ca3e64150329d984540ca7561150329e980540ca79601503297596430cb1e5450c32b6181430ca6d6590832cb951420cb8d435083297d95320ca6f654c832cd952510cb355494432cd951510cb355454432d590d510cb554354432d9909510cb654254432d5cc9510cb553254432ce952500cb395494032dc946500cb715194032ce951500cb395454032dc945500cb715154032d690d500cb594354032da909500cb6942540329ed8153d06786054f419e98252d06796094b419bd89539066c6254e4197d8d529065c6354a41ced0850507394214141ce904505074e5394841d354e521074e5354841d354d521072d52d04418fd95411072d5250441ae18141106776550441d694e50107595394041da94a50107695294041d694d50107595354041da94950107695254041dc905501077141540419e98354cc67960d53319b98a54cc66d6295331b618143cc67a60d52319e583548c66e62152319b588548c67a60152319e580548c6d5610ca31d68ca508c7583294231d6cc6508c66e62951319b58a544c66f62551319b189544c67b60551319e181544c65c6550d31b5185434c6d86050d318f990524c63d64149319e980524c6796014931cb990524c72d6414931d390c524c74d4314931d9584524c76a6014931da580524c65e65cc931d314b324c74c524c931d314a314c6da608c5319ed81540c67860550319798c540c66e62150319b588540c67a60150319e580540c65d658c831b5584320c65f654c431b3189310c677654c4319e98354c867960d53219798e54c865d63953218f99053c863d6414f219e98053c86796014f2197d8d50c865c63543219ed81548867860552219798c548865d63152219e980548867960152219e983538867960d4e21b958432887c4328c621b918931887c7324c6218fd91508863c64542219798e544865d639512197d8d544865c63551219ed81544867860551219798e534866f6254d219799453487556114d21d314e424866c6550921d314d4248754538c5219d195314874c53885219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219b988540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c21d3189530863e6414c218f590530865e6314c219d984530867a6014c219e580530872d54cc821d354f320866d650c821cb550320872d54c8421d554e210866f6548421cb55121086cc63484219dd9521087555348421ce95250087395494021d694e50087595394021ce95150087395454021d694d5008759535402197d8d529025c6354a409798e519025d6394640ab58841902b96010640d6181531034e5394840d354e521036a6094840d394
  | 2 => 0x29876af60f0e08fa6a3a0a65a2c4a2922e8a424c000b52cc078dc5d1a6cf8009d8a0c503494800148ea00000218820032c97b4400126941b005b8c002b458b38340008d0000007aaea449c0141817600204bab748500065800000060032a6d13e8a000003240d80080800003a00005c1316eb211e00002e28e2e41b200286aa36c39a063d1c69503aaa80055b16502e8062e6000007398ce3888a4310681587909c19b0806b480933600000000de000000000000170002b26515a6fb7a7f2a2c2a100302836118c09ba6a3a47208444842742120039a4902c003944225c9d24c7c876bb8bcaf2b0968aa5cb6ae0960258007d02a0724e9f266308747baa4e60543234e2fae4e709400000a51668c00051000dd954a31e8712685f2c668a38d596400038b3b5e4812e69350b0af0730502da7ac7ab689198290fc8eaec33a1a5494c26262cb8e4468ca9c80e570002403e7a9d63e12aa7180238802e000c82600015000000001f80000031048419c0000b000000001e6d8a18000008f18a9b33a520308d8567b0ee8b3b09b90ee137c318b2dca56099fe3b0688980a459de9fb4c0c8f6c6b344e07e64ada8308c1a9ca003a82b020b8b42428fe43300a68009936041132b0072b61f0e499c0485ad02e05fb6ecf30e74b46cc040a119a08acad2bac002de000f000008010000000024b26002ae3696a3492c3e900da000269b61785892328d49c20002edc0004d2206f1dc6121644000eb846ae3a62d306bf06278208042786b2324a388c48f2c316c112fe8298e4721cd613c001ae92800e1800af8008b8a8c71788a8c013a1e60800a9936cca8ebcafab7000888007514ac11e2b587c00070a806c1b8d6c895eeab961e2f47e99e01c0400000008010041f0280700c021100400018008010101b008040080e008030500e0480002804000000081c020030b03d0040f0281101007034000040b0040d0801f088020080305c000480100c0500c0e014020141b020060400000c01008090400e000000280904c1800810018040100005c0301001004000003f07c010000102402000050002801c0e00c0100802034000240207c020180003c060002604410004040000000c0000405000020100105007000050340605c050180c06c04014100027a6094b439e58252d0f6a6094b43da58252d0ece62d0e439e9825190e796094643b398b4350e3f6550c4397d954310f1e5350f42ae18143d0ace63d0a42ced0a5090aae62d0d42ae1814350ace63d0942ae9824250a5e63145429758c5150a7a60145429e5805150a3f65508429bd954210a7b60553329e18154cca7a60947329e58251cca7a60d52329e583548cad86050e329758e544ca6d62951329dd85544ca7461551329ed81544ca7860551329d987540ca7561d50329e983540ca7960d50328f596540
  | 3 => 0x7620000000a0000b4000350ba450ae538640025828a88e7b5a91a82e01460029e331865ea96d7364be08a0013ad50000004ade1b8409f6a4a0eb4aac620006ab1800000d989e00000001420037e0019090
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2466c041c2950015004d12d760000249a10339664520d3c700c0c0ba08800020d621c14350832aa0e0a1aa21970543509510cb84a1a84a80658a5486050441aa2e2194a118d447150c524c6a43828629263895916114931c52c8b00a498e4852982314c6633b66498c43835506348421c88c528a631864552584320c318aa2c220061165d85310120d12c6a10809070853508404832829ac220241a85096110120ca4a6b08818860d635885444312b12c22a2218c9964190110c60a930e60886185418d20443182a0c2902218615263c4110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x210b008050d4254432a098614d4210120e00535096110120
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 5 => packedAt s5K5 (19164+((h/210+packedAt s5K5 (17064+(h % 210)*10) 10) % 759)*11) 11
  | 4 => packedAt s5K4 (19544+((h/157+packedAt s5K4 (17974+(h % 157)*10) 10) % 568)*10) 10
  | 3 => packedAt s5K3 (1475+((h/9+packedAt s5K3 (1421+(h % 9)*6) 6) % 35)*6) 6
  | 2 => packedAt s5K2 (182+((h/1+packedAt s5K2 (180+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe0ffc7f03e3f81e3c7e3f07fe381f8037367c
  | 1 => 0x1ff0ff8ffc03ffe03f8fc7f81fc01ffcc9c87f
  | 2 => 0x1fff000ffffc7fffc00ff8001fffe3ff0e0f8f
  | 3 => 0xe000000fffff80fffff000001ffffc03f00ff0
  | 4 => 0xfffffff0000000ffffffffffe0000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xc2661881384511060c160911ce08c49813163c
  | 1 => 0x44a2201208c820201482423052410928414855
  | 2 => 0x884049245101404a400c9042849242510e028a
  | 3 => 0x18cb248a28232b4b92000a519259022f00d60
  | 4 => 0x1108c000c31244d9224924c600060043aca000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeef8c0feeef8c0feeef8c0feeef8c0feeef8c0feeef8c0feeef8c0feeef8c0feeef8c0feeef8c0feeef8c0feeef8c0feeef8c0feeef8c0feeef8c0feeef8c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36348
namespace PEqualNP.Outside.L_meta_36348
open PEqualNP.Outside.L_meta_36348.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x111500028d763169d5401b0000ccd1e00817b91285b801e0400a586402600183ae6a219343689480487c5ba0601c302a0022b289493c6240b964660e002639e804e181810110040002a004801008700263c180017fd50057f54017f95005fd54015f55005fc5401ffd4c07fe5301ff54c07fc53017fd0c05fe43017f50c05fc4301ffd4803fe5201ff54803fc52017fd0803fe42017f50803fc42007fcc803fe32007f4c803fc3201ffd4407fe5101ff54407fc51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842004ff8c210027fa6108013fc3084009ff9042004ff88210027f44108013fd2084001fc9042004ff08210027fe2108013f71084001fd884200bffd951005dfeca880037f65440013fb2a200bff9951001dfcca8802ffd65440177eb2a200bff1951001df8ca8802f7c65440073e32a200affd9110055fec888003bf64440015fb22200aff99110015fcc88802bfd64440157eb22200aff19110015f8c88802bbc64440055e322200affd5110056fea88802bfe5444015feaa2200adf55110057f8a888003ff63440017fb1a2000ff98d10005fcc688003fd63440017eb1a2000ff18d10005f8c68802fff5344017ff29a200bff54d1005ff8a68802bff4344015ff21a200aff50d10057f88688003ff62440017fb122009ff9891000dfcc488003fd62440017eb122009ff1891000df8c48802fff5244013ff292200bff5491004ff8a48802bff4244013ff212200aff5091004ff88488003ff3244013ff1922000ff4c91004ff8648802fff5144017ff28a200bfd9451005ffaa28802ff55144017fe28a200affd0510057fc828802bf64144015fea0a200afd50510057f88288003ff3144001ff18a2000ff4c510007f86288027ff2144001ff10a2000ff4851004ff8428802fff5044009ff282200bff54110027f8a08802bff4044009ff202200afe90110057fa808802bf94044009fe2022000ffcc110027fc6088003fd3044009fe1822009ffc8110027fc4088003fa2044001fe9022000fe48110027f84088003ff1044001fd8822004ff84110027ec2088013ff65040097fb282004ff9941001dfcca08013fd650400f7eb282004ff19410025f8ca08013ff64040097fb202004ff99010015fcc808013fd640400d7eb202004ff19010025f8c80801bff540400dbfaa02006ff95010037faa80801b7d540400dfe2a02004ffd8c10025fec608013fe63040017f3182004ff58c10005fac608013fc63040097e3182007ffd4c1003ffca60801ffd530400ffe2982006ffd0c10037fc860801bfd430400dfe2182004ffd8810025fec408013fe62040037f3102004ff58810005fac408013fc62040097e3102007ffd481002ffca40801ffd520400bfe2902006ffd081002ffc840801bfd420400bfe2102000ffcc81002ffc6408003fd320400bfe1902008bf9841003ffea20801ffe510400ffea882007ff14410037fe820801bfe410400dfea082006ff10410007fe6208003fe3104001fe9882000ff0c41002ffe4208003fe2104001fe9082005ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0x3fd6148001fe30a4000bf18520097fea29004bfe5148025fea8a4012ff1452008ffe8290047fe4148023fea0a4011ff10520007fe6290003fe3148001fe98a4000ff0c52000ffe4290007fe2148003fe90a4001ff0852000dfec09004bff5048009ff2824012ff54120027f8a090047ff4048009ff2024011ff50120027f88090003ff3048009ff1824000fe8c120007fa6090003f93048009fe1824001ffc812000ff64090013fe2048009f71024004ff08120027d84090007f82048021ffb2e2010bfd9710087fccb8800efe65c4021feb2e2010bf59710087f8cb8800efc65c4011ffb262008bfd9310047fcc98800afe64c4011feb262008bf59310047f8c98800afc64c4011ffaa62008dfd5310047fca988023fd54c4011beaa62008ff15310007fec788002ff63c4001ff31e2000bf98f10007fac788002fd63c4001fe31e2000bf18f10087fea788043fe53c4021fea9e2010ff14f10047fe8788023fe43c4011fea1e2008ff10f10007fec588002ff62c401fff3162001bf98b10007fac588002fd62c401ffe3162001bf18b10087fea58803ffe52c4021fea96200fff14b10047fe858803ffe42c4011fea16200fff10b10007fe658803ffe32c4001fe996200fff0cb10087fea388043fe51c4021fb28e2010ff54710087eaa388043fc51c4011ffa0e2008ff90710047ec8388023fd41c4011faa0e2008ff10710007fe6388003fe31c4001fe98e2000ff0c71007ffe4388003fe21c4001fe90e200fff08710087fea188013fe50c4021fea862004ff14310047fe8188013fe40c4011fea062004ff10310007fe6188013fe30c4001fe9862004ff0c31007ffe4188013fe20c4001fe9062004ff08310027fecb08012ff6584009ff32c2003bf99610027facb0803afd6584009fe32c2004bf19610027fec908012ff6484009ff3242002bf99210027fac908032fd6484009fe3242004bf19210067fea9080337f5484019ff2a4200cff55210066faa908033fc5484009ffb1c2004bfd8e10027fcc708002fe6384009feb1c2000bf58e10027f8c708012fc638401dffa9c200eff94e10077faa70803bfc5384019ffa1c200cff90e10067fa8708033fc4384009ffb142004bfd8a10027fcc508006fe6284009feb142000bf58a10027f8c508012fc628401dffa94200dff94a10077faa508037fc5284019ffa14200dff90a10067fa8508037fc4284001ff994200dff8ca10007fa6508037fc32840157eb0c200effd4610077fca30803bfd518401dfe28c200cffd0610067fc8308033fd4184019fe20c2000ffcc610007fc6308003fd3184001fe18c200dffc8610007fc4308003fd218401bfe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe8108013fe4084009fd2042004ff50210067f28108013fc4084009ff9
  | 2 => 0x300befaa81805ffc540c0337f3186018ffd4c300b7fca618063fd530c02dfe2986017ffd0c300b7fc861805ffd430c02dfe2186004ffd8830027fcc418006fe620c009feb106000bf58830027f8c418012fc620c031ffa906015ff948300c7faa418057fc520c02fffa106015ff908300bffa8418057fc420c02dff9906015ff8c830007fa641805bfc320c009ffb086004ff98430005fcc218013fd610c0017eb086004ff184300c7fea218063fe510c031fea886018ff144300bffe821805ffe410c02ffea086017ff104300b7fe6218003fe310c001fe9886016ff0c4300affe4218003fe210c001fe9086015ff08430025fcc018013ff500c009ff2806004ff54030027f8a018013ff400c009ff2006004ff50030027f88018013ff300c009ef9806004ff8c030027f46018013fd300c009ee9806000fe4c030027fe4018013fc200c009ffb2c4004bfd9620027fccb1000efe6588009feb2c4014bf59620027f8cb10012fc6588009ffb244004bfd9220027fcc91000afe6488009feb244013bf59220027f8c910012fc6488027ffaa44013dfd522009ffca91004ffd5488027beaa44013ff15220027fec710012ff6388009ff31c4000bf98e20027fac710002fd6388009fe31c4004bf18e200a7fea710053fe5388029fea9c4014ff14e2009ffe871004ffe4388027fea1c4013ff10e2000dfac510007ff5288003ff2944001ff54a2000ff8a510007ff4288003ff2144001ff50a2000ff88510007ff3288003ff1944001ff4ca2000ff86510013ff6188009ff30c4000bf98620027fac310002fd6188009fe30c4014ffd46200a7fca310053fd5188029fe28c4013ffd062009ffc831004ffd4188027fe20c4000ffcc620007fc6310003fd3188001fe18c4001ffc862000ffc4310007fd2188003fe10c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009fd1844004ff4c220007f26110013fc3088009ff9044004fbc822000ff64110013fc2088009fc1044012ffd9520095feca9004bfe65480077f32a4012ff59520095faca9004bfc65480077e32a4011ffd912008dfec890047fe64480057f3224011ff5912008dfac890047fc64480057e3224011ffd512008efea890047fe5448023feaa24011df5512008ff8a890003ff63480017fb1a4000ff98d20005fcc690003fd63480017eb1a4000ff18d20005f8c69004bff5348025ff29a4012ff54d20097f8a690047ff4348023ff21a4011ff50d2008ff88690012ff6248003ffa924001ff9492000fdca490007fd5248025f6a924001ff1492000ffe8490007fe4248003f72124001ff5092008fda8490007fc4248003ff9924001ff8c92000ffa6490007fc3248001ffb0a4000bfd8520007fcc29000
  | 3 => 0xe28e6019ffd07300cffc8398067fd41cc033fe20e6016ffcc730007fc6398003fd31cc02dfe18e6020ffc8730007fc4398003fd21cc041fe10e6021ffd4330027fca198087fd50cc009fe2866019ffd0330027fc8198067fd40cc009fe2066020ffc8330027f84198013ff658c0097fb2c6004ff9963001dfccb18013fd658c03f7eb2c6004ff19630025f8cb18013ff648c0097fb246004ff99230015fcc918013fd648c03d7eb246004ff19230025f8c91807bff548c03dbfaa4601eff952300f7faa91807b7d548c03dfe2a4601bbf58e300fffea71807ffe538c03ffea9c601fff14e300f7fe871807bfe438c03dfea1c601eff10e30027fec518013fe628c0037f3146004ff58a30005fac518013fc628c0097e314601fffd4a300effca51807ffd528c03bfe294601effd0a300effc851807bfd428c03bfe2146000ffcca300effc6518003fd328c03bfe1946004ffd8630027fcc318002fe618c009feb0c6000bf58630027f8c31807fff518c03fff28c601fff546300fff8a31807bff418c03dff20c601eff506300f7f88318003ff318c001ff18c6000ff4c630007f86318077ff218c001ff10c6000ff486300eff84318012fe608c009ffa846004ff94230027faa118013fc508c009ffa046004ff90230027fa8118013fc408c009ff9846004f7cc230007f66118013ff208c009fe104601cffd95300e5feca980037f654c0013fb2a601cff9953001dfcca98073fd654c0397eb2a601cff1953001df8ca980737c654c0073e32a601bffd91300ddfec89806ffe644c0057f322601bff591300ddfac89806ffc644c0057e322601bffd51300defea89806ffe544c037feaa2601bdf551300dff8a898073ff534c039ff29a601cf794d300e7faa698073dd534c039fe29a601bffd0d300dffc869806fde434c037fea1a601bf750d300dff88698003ff624c0017fb12601aff9893000dfcc498003fd624c035fe3126001bf189300e7fea49806bfe524c039fea92601aff149300dffe849806bfe424c037fea12601aff10930007fe649806bfe324c001fe992601aff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c039ffa8a601cff945300e7faa298073fc514c037ffa0a601bff905300dffa829806ffc414c001ff98a6000ff8c530007fa6298003fc314c035ff90a6000ff88530007fa429806bfc214c039ffa826004ff941300e7faa098013fc504c037ffa026004ff901300dffa8098013fc404c001ff9826000fecc130027fc6098013de304c035ff9026004ff08130027feca18012ff650c009ff3286003bf99430027faca18062fd650c009fe3286004bf19430027fec818012ff640c009ff3206002bf99030027fac81805efd640c009fe3206004bf190300bffea81805f7f540c02fff2a06017ff550
  | 4 => 0x802fe6388401feb1c4200bf58e21007f8c710802fc638844bffa9c4225ff94e2112ffaa710897fc5388449ffa1c4224ff90e21127fa8710893fc43884037eb144201ffd4a2100ffca510807fd5288403fe2944201ffd0a2100ffc8510807fd4288403fe2144201ffcca21007de6510807fe3288403fe9944201ff0ca2100fd86510806fe618844bffa8c4225ff9462112ffaa310897fc5188449ffa0c4224ff90621127fa8310893fc4188401ff98c4200ff8c621007ec6310803fd3188401fa98c4200ff0c62100ffe4310807ef2188403fb90c4201ff0862100fe84310803ff6088401ff3044204bf98221007fac110802fd6088401fe3044225ffd422112ffca110897fd508844bfe2844224ffd0221127fc8110893fd4088449fe2044201ffc822100ff8411088fff65484477fb2a4223ff9952101dfcca9088ffd65484477eb2a4223ff1952101df8ca9088bff64484457fb224222ff99121015fcc89088bfd64484457eb224222ff19121015f8c89088bff5448445bfaa24222ff95121117faa89088b7d5448445fe2a24200ffd8d21005fec690803df63484016fb1a4200ff98d21005fcc690803fd63484017eb1a4200ff18d21005f8c690803dc63484016e31a4223ffd4d2111ffca69088ffd5348447fe29a4222ffd0d21117fc869088bfd4348445fe21a4201bfd892100ffea490807fe5248403fea924201ff1492100ffe8490807fe4248403f72124201ff50921117da8490807fc4248403ff9924201ff8c92100ffa6490807fc32484037fb0a4223ffd452111ffca29088ffd5148447fe28a4222ffd0521117fc829088bfd4148445fe20a4200ffcc521007fc6290803f63148401fe98a4200fd4c521007f86290807ff2148403fb90a4201ff88521007dc4290807fc2148403f610a4201fd08521007fec090802ff6048401ff3024200ff58121007f8c090812fc6048447ffa824223ff9412111ffaa09088ffc5048445ffa024222ff90121117fa809088bfc4048403ff9024201ff081210b7fecb98086ff65cc043ff32e6003bf9973010ffacb98086fd65cc02dfe32e6003bf197300b7fec998066ff64cc033ff3266002bf993300cffac998066fd64cc02dfe3266002bf193300cffea9980677f54cc033ff2a66019ff553300cefaa998067fc54cc043ffa9e6016ff94f3010fbca798087fd53cc043eea9e6016ff14f300cffe879805bfe43cc033ef21e6019ff50f300cfba879805bfc43cc02dffb166020ff98b3000dfcc598003fd62cc0017eb166016ff18b3000df8c598087ff52cc041ff2966021ff54b30107f8a598067ff42cc041ff2166019ff50b30107f8859805bff32cc041ff1966000ff4cb300b7f8659805bff61cc001ff30e6000bf98730007fac398002fd61cc02dfe30e6021ffd473010ffca398087fd51cc043f
  | 5 => 0x63114ffa83188a7fc418c401ff98c6200f7cc631007ee63188bbff218c45dfe10c6200ffd8231007fcc118812fe608c401feb046200bf58231007f8c1188bfff508c45fff284622fff5423117ff8a1188a7ff408c453ff2046229ff5023114ff881188bbff208c45dfe104622dffd953116dfeca988b7fe654c4077f32a622dff5953116dfaca988b7fc654c4077e32a622cffd9131165fec8988b3fe644c4057f322622cff59131165fac8988b3fc644c4057e322622cffd5131166fea8988b3fe544c459feaa2622cdf55131167f8a8988b7ff534c45bff29a622dff54d3116ff8a6988b3ff434c459ff21a622cf790d31167fa86988b3dd434c459fe21a6200ffd8931005fec498803ef624c40177b12622bff9893100dfcc498803fd624c457fe3126201bf18931007d8c498806ec624c45bffa92622bff9493116ffaa4988affc524c459ffa12622bff90931167fa84988affc424c401ff9926200f7cc93115ffc6498803fd324c401ee992622bff0c93116ffea2988b7fe514c45bfea8a622dff14531167fe82988b3fe414c459fea0a622cff10531007fe6298803f7314c401ff18a6200f78c53115ffe42988affc214c401ffb026200bfd8131007fcc098803fd604c401fe3026204bf1813116ffea0988b7fe504c45bfea82622dff14131167fe80988b3fe404c459fea02622cff1013115ffe40988affc204c42dffb286228bfd9431147fcca1880efe650c451feb286228bf594310b7f8ca1880efc650c42dffb206227bfd903113ffcc81880afe640c44ffeb206227bf590310b7f8c81880afc640c44fffaa06227dfd503113ffca81889ffd540c44fbeaa06227ff15031155fcc6188a3ff530c42dff2986228ff54c310b7f8a61889fff430c42dff2186227ff50c310b7f8861885bff620c44dff3106201bf98831007fac418802fd620c42dfe3106201bf18831147fea41889bfe520c451fea906226ff1483113ffe841889bfe420c44ffea106226ff108310b7fe641889bfe320c44def1906200ff4c8310b7f8641889bdc320c4537f3086228ffd4431147fca2188a3fd510c451fe2886227ffd043113ffc821889ffd410c44ffe2086216ffcc431007be6218803fe310c401fb1886200ff4c431007ba6218803f5310c44dff9086226ff084310b7fec018803fe600c4097f3006200ff58031005fac01885bfc600c451ffa806228ff94031147faa0188a3fc500c44fffa006227ff9003113ffa801889ffc400c44dff9006226ff0803112ffecb10896ff658844bff32c4203bf9962112ffacb10896fd658844bfe32c4203bf19621127fec910892ff6488449ff3244202bf99221127fac910892fd6488449fe3244202bf19221127fea9108937f5488449ff2a44224ff55221126faa910893fc5488401ffb1c4200bfd8e21007fcc710
  | 6 => 0x9ff2066434ff503321a7f88199007ff20cc803fe1066433ffd953219dfeca990cffe654c8077f32a6433ff5953219dfaca990cffc654c8077e32a6432ffd9132195fec8990cbfe644c8057f3226432ff59132195fac8990cbfc644c8057e3226432ffd5132196fea8990cbfe544c865feaa26432df55132197f8a899006ff634c867ffa9a6433ff94d3219ffaa6990cffc534c865ffa1a6432ff90d32197fa86990cbfc434c8037fb126401ffd493200ffca499007fd524c803fe2926401ffd093200ffc8499007fd424c803fe2126401ffcc932007de6499007fe324c803ef1926401ff0c93200fb86499007ec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6400bf1853219ffea2990cffe514c867fea8a6433ff14532197fe82990cbfe414c865fea0a6432ff1053200ffe4299007fc214c801ffb026400bfd8132007fcc099003fd604c801fe3026404bf1813219ffea0990cffe504c867fea826433ff14132197fe80990cbfe404c865fea026432ff1013200ffe4099007fc204c82dffb2e6231bfd973118ffccb9880efe65cc463feb2e6231bf597310b7f8cb9880efc65cc42dffb26622abfd9331157fcc99880afe64cc455feb26622abf593310b7f8c99880afc64cc455ffaa6622adfd5331157fca9988abfd54cc455beaa6622aff1533118ffea79885bfe53cc463fea9e6216ff14f31157fe879885bfe43cc455ef21e622aff50f31157ba879885bfc43cc42dffb166230ff98b3100dfcc598803fd62cc4017eb166216ff18b3100df8c5988c7ff52cc461ff2966231ff54b31187f8a5988abff42cc461ff216622aff50b31187f8859885bff32cc401ef9966230ff8cb31007fa6598803dd32cc42dfe1966231ffd473118ffca3988c7fd51cc463fe28e622affd0731157fc83988abfd41cc455fe20e6230ffc8731187f8439885bff60cc401ff3066204bf98331007fac198802fd60cc42dfe3066231ffd433118ffca1988c7fd50cc463fe286622affd0331157fc81988abfd40cc455fe2066230ffc8331187f841988bfff658c45f7fb2c622fff9963101dfccb188bffd658c45f7eb2c622fff1963101df8cb188a7ff648c4537fb246229ff99231015fcc9188a7fd648c4537eb246229ff19231015f8c9188a7ff548c453bfaa46229ff9523114ffaa9188a77d548c453fe2a4622cbf58e3117ffea7188bffe538c45ffea9c622fff14e3114ffe87188a7fe438c453fea1c6229ff10e31007fec5188bbfe628c4037f3146200ff58a31005fac5188bbfc628c4037e314622fffd4a31177fca5188bffd528c45dfe2946229ffd0a31177fc85188a7fd428c45dfe2146200ffcca31177fc65188bbde328c401fe994622eff0ca31177b8651889efe618c45fffa8c622fff9463117ffaa3188bffc518c453ffa0c6229ff9
  | 7 => 0x200000601000001e02003001406a00201c00e02400a00000000000a00000400002000001e02a00000000600a00c00002400002000000200001200400000000000600000200200402000001c00600001400a06401601001200400000801800600202000200000801000202800800000802e00a00801600800000000601600800200200000200600000600400400201200000e00a01200a00000600200000200200c01200000c00e00601201400200000200000000001000000e00203c00200600800002e00000200201e00803c02600a00a00002800201601001600000000400602200203001a01c00400403c02000000a02e00000a02600000000200200a00200a01200400a01800805200400002002200400002000200801000600400600600400a00400403c00400402004e00000400400601800000000000000602000000600400000602400000804001601800600000000002001600000000a01a01200e02800e01c01000200400c00200001200000000402400001803000600000400000000c00200000200000001200201400200e02000001200601403400000000201c00001800800e00200000002800000000200e00600000800000600001800200800000400000000800200401400000800000001c00000202000200800800a00200200201000000000200800600001400200200200800400200200c00402602602c02400000401a01202a00200400600000200000001a01001400e00202e00201003800000400600200001800a00800600000000000200600201200200000400600e00000a00400000003600601200400600000000200800001400000200001800000000802e01600400200a01400000000000200201601200400400200200000001001601201801a00000001a00201600000c00600401400000201a00400400a03602000e16ffd97321adfecb990d7fe65cc8077f32e6435ff597321adfacb9905bfc65cc8077e32e6416ffd93321a5fec9990d3fe64cc8057f3266434ff593321a5fac99905bfc64cc8057e3266434ffd53321a6fea9990d3fe54cc869feaa66434df553321a7f8a999006fe63cc86bffa9e6416ff94f321affaa79905bfc53cc869ffa1e6416ff90f321a7fa879905bfc43cc8037eb166401ffd4b3200ffca599007fd52cc803fe2966401ffd0b3200ffc8599007ee42cc803fea166434fb50b3200ff88599007fe32cc803ef1966401fb8cb3200ff86599007dc32cc82dffb0e6400ff98732005fcc399003fd61cc8017eb0e6416ff187321affea3990d7fe51cc86bfea8e6435ff147321a7fe83990d3fe41cc869fea0e6434ff1073200ffe4399007fc21cc803f610e6416ffd8332007fcc199012fe60cc801feb066400bf583320b7f8c1990d7ff50cc86bff2866435ff543321aff8a1990d3ff40cc86
  | 8 => 0x9039000116000022d32800171c0018680006a1030000000be485c01526d74955800001d30c000354688e6d1ad6001c8000f8c001678e940000000003481dd83879c41c35134c000000000000f5c0000005800015540000017892d40008908dc00193c45cd885196d8000000e250d41a0c0c7a054cb0d4c5538000b08a552000d80014e800105400109419c00000102c001518dd5940f80000000a000010c0000f0c6792a00008e8d005c963d1d53f8218814b98000001704e500000000000009dd754f30000000000000000d38e090b4a8cce84240011715a80bc000648a1471cb40000eecbdc8c05100000017b950541c6d94418d03450287cc4fc400c51265688000ac087915d14c340d50ad0f090b00d18885d0c296c80008d8fb4e800015c00000007a4000000b447f0414710ea575091d3387d15ec000c680015489a41942547a915800140951c8650dc001274000f04a30a4842c8853d8fe8aec001778f718c57650c5344989025398bd53dc0e007558cc9c001120c6c268000000de02bc2844ac4ed4780000014a4bb06900003b8d8400005800017c124c08001419140d0c00010800000120cacc39cdcd84000000057c0016dc000d2189ca0c000000001374ec400044cb6855843074c000dc0000000fe4f1c2e4200000d34000d70cf80018f91040c9450000b3c8b16391909180017a80012fc17440c2780ec66c1e87017c9320b94ca58a0b197602a0591218338000fa4b4c5d4000574000e7c0012155e07f560d5d8904dbc0000000017e1655584960000000f14000001130000000818000aa000130970831c7e40000000002618b9008000e795000016ecd1c03507923c5051e0cc4b80ef0ec80000e5444dd16310614d16cc001090bc4830000000000e5972c370aa952545c2c4000ed5178d300012f4a985c09154910ec0011c135876c000f280000000000000000004b17b4000000001384c914f80008340000015c8ce52400017f13d01841bc9b473c8bc0012dd944770b24000f2c4e44c55e80003249b00000000858e8000ac9860000e30c485a0790e1d6800000015213a0000000fb1590150b1069d480568080000a183c8594001864d4cdac3c594893c6717dc900695920f64460000c24000b340013b40000010049e8000b04660001845540910e71719100314e980000000011bd2680012cc001828f7c9740000003106ac2150d00a420d6214d93357c42317f83e97ecebcb0012c00000c00c00401a00200000c00000800000600802a02c00000400e00000000801000400c00000a00000200800003000004600e00800c00c00c00401600200401c00005000200e00200001400200a00a00a00200000000200c00000000004c00400800200002400400200003400a00000000201200400600801400000003201a00200e006018000
  | 9 => 0x98540b9508d94ba1428c856b5248d3c2340006f88a480400179d098cad6f4738e392f00009811103fc0018e40018ac0000012d816c62d6bc00192cc74000000684c78d7d834bccf98000edc85411c050a80a44b7911465952c0008b53a97406fd7ac000000000470ef8250888f74000714f54394fa8d28644e91780154180538128d698110a98c99301046a4530554000c20c040006080015713c84a0958b3128c4487ec001404d4400000107000000000000000112c15cab9578d241e16609095f54b17d48f8bb80000309f12c564c28800063cc88d08cecb515f836c2c13480012c8560434730000b381780f0bc829c5e40acbf11d0624ffc000680001108b1ce151b57a48acaa50216d131c2e90884f8bf98dd830eac3f04d96741b95811546308614bd820ad974c6d16f046856580d1f4800e294b8a2161400142d08c00074000000092c000001738f6188084caac7051fccd4a9d5bc2445158ec0e8000d58a34b7c000f24d60000000000ed800000101d61cdf4001808c64000000000ea0724f4c0008400006680000f40014e0c191a8db860cf40e4c95c321298a6c000000000ab1018000784000000d1800043800181d474000984da118c8f54e5725914a1d3a41484b4588e6883c4f57d018894c0000000a19347dc000c440000012c0055378ff82c800128048c32c000c5c00176899cf3c6dc28c9297ccec00288f10bd01456c398ca84d588c54973c8b8e215b85b485164593867c1142e006d8043656510b85e97b063421000139c000ff40009a12ac0006c982d2e44657743280003b00013b80002ac000000f501e41b0001878000000000b592a8a4086c070fac0000016700016046bd6d413114947150d7212513243b40000005f92356290e13e12bc000304d641001f9758c353fd05cb6c000000490a9000089c780a68000001795910444b84318a70e401fd818000cd14c86b88e522953400000065c00082ccfd2794250e42fc1440002ec0014f0f90c94000b7087569855c000afc00151400077c0004cc4f0000000f204882985d91c80008c8b900000017c190c0006ccdec540934868fd8000fbc0004bca5074400000187d30555cae48255a4cc802d38c2dcdc977c5ecbac38452d8f02718b49f91b0655610dc4369728000000000a6435d0101a8110d5480d5b56fc0015fcb2910c000000c4c4540b5238d5d05875c9d4f19814fa0b64720e2ce552ec0109c48e03f8dfcee41d0141448fd45f54d40000005281b51e80000010c887194c2b9924484a7c76049946d8d4000000d100000946a800097d46111c0000014c02a80085f01693e4d8c000930e000000010f03d80014b472c24c000001288544eb99507fd204abc1916947554a10d900c2d800004c5b800000125800037d900cbc949421690a2cda88ec5dd9282809e47d48997
  | 10 => 0x95121c27c5bd4858bc708bf4ed19050e8bb4e100b03596e19543d4c5426443d4681cc1647c09647883e4de4000a611d80009440000003f40012100000000019180014a944c000000a786002240000006d4ae800046c00000000000167c0001a4fec13c001884000290ad507d4380013c4cd8480000fc4001350d992b424936520889595917d361301118c14598e3468c4e148cbe89cca2800082153cdf841800000183ce606f16a07e18b12b178c00096d7e95a0d7845800127c0000009b800000009cf385cc0000192e92215986502d516d3f0940570f886f52948a803d06c0897a118034c3e11e5565824c109d16a9244ac49ac0005fc0d4379380f9c000000b5c00000000000131833c3cd8a90513cc11800000104000000109c55113800168ce0400000000007c000000238000000000199858000a5c1c562c838b200009a80013883c000000042033000126154c000000a9400169c0017e48d421c500f3481d70d0a16e413903d7bca598014f48c4078ea8be133c47cc7ca89891608208954a74b54c8119c718000ecd85c9bcf00fb83bcef459c001560a3c0011242b04d01358cc0010852a40012d000042949ce442d0e480008a0df133008d5c57987340004794cc00000053c0004940fd95c4a8add8e07951f04402043093b13143d1168000000bd8000f940dd550000000cb4000e8cc2c00175cd411a42cd5ac7991c4c402f147d370d80d9cba40015d4a097fc2740018948d00009d83346b5960f10fe03013ec2200013940007f80000009986982956c0000cb80000000c4000000000001464db00006e8000000001454750c618491354309240685780007b440800184d6186198fce9ca4c0000014dd0f5898000000004cb0b485a96ac0000000000003ac000000db54150cc18cfdc77516458c00000010c7b8729150000990e5ce654ac49d8d825c000d756b17146ec00127000125c451634000d480009786102296b884800122c0001f4779734cdceb4060000c3c00000000098c84531000000000156d730cf137c00c0496485258a4e883a40010640000014fc000f480002a525438c5c4000000e3d1ecb8c920f44c8c675574d046e050d189368fd087c0000000000015d13c0628000000cc000000000151000000104c4c17700000001ed1f87ac0006e4968000de935cbd000166d2f96254341d8c3080965d1cd3bd710000ae16f8ab4a04f6858535461c000e749e157c03800064030cd2c0008805ac14c001684000e0d039410ee0001184fcc0009c80003746c48296c47b0000af529c0c0e84000000000f6c00064c6c00000018742f40000018500001c1488000098f84dd840400140c61564113d5440000004e90ac0006380000009fcc998719083dc000af936c0000005e10fc000efc0011dc6213f5664000c3890c000c00259034ba
  | 11 => 0x7e8bc186c9ed1995dc0451742f8388bbd5e53e959cda46b0d90604b8802532d0809945b1658bfd2250f88cd290eb0a840000000013900a80014ec88d594170d6c3ed58924c7483604c97848fd0a4121400cf4b7493823cb14000534fc026c06543c000b9d7d80000007c58f4000001745000f791a01d4764508ccc3a84b88585a5068001668474ca12b945800015824000078c0004dc1ad3ac0010497f47c8a10f58970c1c0000012e170076991cce070cc5800051c0002b40011280013d56a51440001608101f15280415300cc0018c00014943a0000e18b615cc4a4b2d3415b06640009c12307bc000520a380003814984107d8ff0000ee89f4c70af0020ddc05d76d1b80f8759045569284d156e9074090fc8bed5f1194a24
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x251481101e7f151481101dff241481101dff141481100067f65c41100867c65c4110006bf64c4110046bc64c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024fa76c41100077b65c41101d77865c41101bdfb74c41101bdf974c4110007bb64c41101cfb864c41101cf7b54c41101cf7954c4110005fb72c4110005f972c4110025fa71c4110026fb61c4110027f361c41101d7f251c41101d7f151c41101cff241c41101cff141c41100b4ff7598c1001cfe7598c10004fd7598c100b4fc7598c100b4ff7498c10014fe7498c10004fd7498c100b4fc7498c100067f5498c100067d5498c10026de7398c100b6de5398c10006dd5398c100b6de4398c10006dd4398c1000cfe7298c10004fd7298c1000cfc7298c10024fe7098c10024fc7098c10026de3098c10026dc3098c10004ff7558c1001cfe7558c10004fd7558c1001cfc7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c100067f5458c100067d5458c10026df7358c10006de5358c10006dd5358c10006de4358c10006dd4358c10004ff7258c1000cfe7258c1000cfc7258c100b4ff7158c1015cfd7158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10004ff755881001cfe7558810004fd755881001cfc7558810004ff7458810014fe7458810004fd7458810014fc74588100067f54588100067d5458810004ff73588100b4fc7358810026ef725881002eee5258810006ed525881002eee4258810006ed425881002eee325881000cff715881000cfd715881002cfc715881002eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026fa10588100b4ff76cc810024fe76cc810004fd76cc810024fc76cc8100b6de63cc810006dd63cc810004ff764c810024fe764c810004fd764c810024fc764c810006de634c810006dd634c81000eee624c810006ed624c810004fd76cc410004ff768c410004fd768c410006de638c410006dd638c410025fa708c410005f9708c410004ff764c410005ef724c41002dec724c4100b4ff760c410024fe760c410004fd760c410024fc760c4100b6de630c410006dd630c410025fa700c410005f9700c41007cff7688410024fe768841000cfd7688410024fc768841000eee6288410006ed6288410025fa7088410005f9708841007cff7648410005df7348410005dc7348410025fb7644010006fb7644010004fb76440100077b75440101c7787544010007bb74440101b7b87444010026fb64440101b6f964440101b77b54440101b7795444010026fb6244010006f96244010025fb7144010027f371440101befa6144010027f261440101b7f241440101b7f14144010007f23144010007f13144010
  | 1 => 0x8910014bc74589100067f54589100067d5458910004ff7358910006df7358910004df73589100b4fc7358910006dc7358910004dc735891004cff7258910006ef725891004eee4258910006ed425891006cff7158910006f7715891007cff7058910006fb70589100b4ff76cc910004fe76cc910004fd76cc9100b4fc76cc9100067f65cc9101ae7c65cc910006bf64cc9101a6bc64cc910006ef62cc91000eec62cc910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91019e7c654c910006bf644c910196bc644c910005f7714c910005f4714c910024fe76cc5100067f65cc51018e7c65cc510006bf64cc510156bc64cc510006df63cc5100b6dc63cc510025fa70cc510005f970cc510004fe768c5100067f658c51017e7c658c510006bf648c51014ebc648c510024fc764c5100067f654c51016e7c654c510006bf644c510166bc644c510006df634c510006dc634c510005ef724c51004dec724c510005fb704c510025f8704c510004fe760c5100067f650c5101467c650c510006bf640c51013ebc640c510007d5310c51006cfe76885100067f658851012e7c6588510006bf6488510126bc6488510024fc76485100067f654851011e7c6548510006bf6448510116bc6448510005df7348510005dc7348510006ef624851000eec624851004fe42148510005fb7048510025f87048510004fe76cc1100067f65cc11010e7c65cc110006bf64cc1100cebc64cc110006df63cc1100b6dc63cc110005f671cc110005f571cc1100b4ff764c110004fd764c110004fc764c1100057f754c11005d7c754c1100067f654c1100e67c654c110006bf644c1100debc644c110006df634c110006dc634c110005f7714c110005f4714c110027d8304c110027f0104c110005fa7688110026fa76881100077b65881101ff786588110025fb7488110205f97488110007bb64881101f7b864881101f77b54881101f7795488110006fb6388110006f9638811004df9728811000efa628811000ef86288110005fa7188110026fb6188110027f361881101fff251881101fff151881101f7f241881101f7f1418811000cff764811004cfd764811000cfc76481100067f65481100967c6548110006bf644811008ebc6448110006ef624811000eec6248110005f77148110005f4714811004df8764811000ef8764811000cf876481100077b65481101e77865481101edfb74481101edf97448110007bb64481101dfb864481101df7b54481101df795448110006fb6348110006f96348110025fb7248110027eb7248110007eb624811000efa624811000ef8624811004fe8624811004fea52481101e7e9524811004fea42481101dfe94248110007f37148110005f87148110007f07148110026fb6148110027f361481101e7f
  | 2 => 0x4fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d100067f54d8d100067d54d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006de32d8d10006dc32d8d1005d7e7598d100057d7598d100067f6598d100067c6598d10055be7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d100b4ff7598d1001cfe7598d100b67e7598d1001c7e7598d10004fd7598d100b67d7598d100047d7598d100b4fc7598d100b4ff7498d10014fe7498d100b6be7498d10014be7498d10004fd7498d100b6bd7498d10004bd7498d100b4fc7498d100067f5498d100067d5498d100b4fe7398d100b6de4398d10006dd4398d1000cfe7298d10004fd7298d1000cfc7298d10004fd7198d100b6f57198d10004fd7098d100b6f97098d100057f7558d1005d7c7558d100067f6558d100067c6558d10005bf7458d10055bc7458d10006bf6458d10006bc6458d10005ef7258d1004dec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d100067f5458d100067d5458d10006df7358d10006de4358d10006dd4358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10006dd6318d100b4ff7518d1001cfe7518d10004fd7518d100b4fc7518d100b4ff7418d10014fe7418d10004fd7418d100b4fc7418d100067f5418d100067d5418d100b6de7318d1000cfe7218d10004fd7218d1000cfc7218d10006de3218d100b6dc3218d10174fe7118d100b4fc7118d10024fe7018d10024fc7018d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d891004eee62d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d89100067f54d89100067d54d89100b4fe73d8910004fd73d891004eec32d891000cfe71d8910024fd71d891000cfc71d891004eef21d8910024fe70d891004cfd70d8910024fc70d891004eef20d89100057f755891005d7c75589100067f65589100067c6558910005bf7458910055bc7458910006bf6458910006bc6458910005df7358910005dc735891004eec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc745
  | 3 => 0xb544821022f795448210026fb6348210006f96348210027eb724821000efa6248210026f8624821006fea5248210237e9524821006fea424821022fe94248210005f87148210025f976c4210006f976c4210225fb74c4210225f974c421021f7b54c421021f7954c4210005fb72c4210005f972c4210027f271c421005d7e76d951005e7e76d951001c7e76d95100057f74d95100057d74d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067e62d95100067c62d95102177771d951005f7471d95100077641d95100077541d95100077a40d95100077940d95102177610d95102177410d95100067f74d95100047f74d95100067e74d95100067d74d95100047d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067e32d95100067c32d95102167f71d951005e7e71d951005e7d71d951005e7c71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f21d95100067c21d95100067f70d95102167e70d951005e7d70d95102167c70d95100067f40d95102167e40d95100067d40d95102167c40d95102167e30d95102167c30d95100067f20d95102167e20d95102167c20d95102167e10d951005e7d10d95102167c10d9510055be76d9110056be76d9110014be76d91100073f75d91100073c75d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be62d9110006bc62d911020fb771d9110057b471d9110007b651d9110007b551d9110007bb70d9110057b870d911020fb610d911020fb410d9110006bf75d91100063f75d9110006be75d9110006bd75d9110006bc75d91100063c75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006be32d9110006bc32d911020ebf71d9110056be71d9110056bd71d9110056bc71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf21d9110006bc21d9110006bf70d911020ebe70d9110056bd70d911020ebc70d9110006bf50d911020ebe50d9110006bd50d911020ebc50d911020ebe30d911020ebc30d9110006bf20d911020ebe20d911020ebc20d911020ebe10d9110056bd10d911020ebc10d91100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10004ff75d8d1001cfe75d8d10
  | 4 => 0x8b1001cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b100067f5458b100067d5458b10004ff7358b100b4fc7358b10006ef7258b1007eee4258b10006ed4258b10024fc7158b1007eec2158b1007eef2058b100b4ff76ccb10004fe76ccb10004fd76ccb100b4fc76ccb100b6de63ccb10006dd63ccb10004ff764cb10004fe764cb10004fd764cb10004fc764cb10006de634cb10006dd634cb10005f7714cb10005f4714cb10024fd768c710006de638c710006dd638c710025fa708c710005f9708c710005ef724c71007dec724c710024fd760c7100b6de630c710006dd630c710007d5310c710025fa700c710005f9700c710024fd768871000eee6288710006ed6288710025fa7088710005f9708871002cff7648710005df7348710005dc734871007fe421487100b6de63cc310006dd63cc310005f671cc310005f571cc3100057f754c3100857c754c310006de634c310006dd634c310005f7714c310005f4714c31000cff764831000cfc764831000eee6248310006ed6248310005f77148310005f471483100b4ff7598e1001cfe7598e10004fd7598e100b4fc7598e100b4ff7498e10014fe7498e10004fd7498e100b4fc7498e100067f5498e100067d5498e10026de7398e100b6de5398e10006dd5398e100b6de4398e10006dd4398e1000cfe7298e10004fd7298e1000cfc7298e10006de3298e100b6dc3298e10024fe7098e10026de3098e10026dc3098e10004ff7558e1001cfe7558e10004fd7558e1001cfc7558e10004ff7458e10014fe7458e10004fd7458e10014fc7458e100067f5458e100067d5458e10026df7358e10006de5358e10006dd5358e10006de4358e10006dd4358e10004ff7258e1000cfe7258e1000cfc7258e10006de3258e10006dc3258e10024fc7058e10026de3058e10026dc3058e10026fa2058e10004ff7558a1001cfe7558a10004fd7558a1001cfc7558a10004ff7458a10014fe7458a10004fd7458a10014fc7458a100067f5458a100067d5458a10004ff7358a100b4fc7358a10026ef7258a1006eee5258a10006ed5258a1006eee4258a10006ed4258a1006eec3258a1006eef2158a10024fc7058a10026ee2058a10026ec2058a100b4ff76cca10024fe76cca10004fd76cca10024fc76cca1000eee62cca10006ed62cca10004ff764ca10024fe764ca10004fd764ca10024fc764ca100b6de63cc610006dd63cc610025fa70cc610005f970cc610006de634c610006dd634c610005ef724c61006dec724c610005fb704c610025f8704c61004cfd7688610025f8708861000cff7648610024fc7648610005df7348610005dc734861000eee6248610006ed6248610005fb7048610025f87048610025fb764821002efb764821023dfb744821023df9744821022f7
  | 5 => 0x4ff764c520004fe764c520004fc764c520005ef724c52000dec724c520004fe760c520004fd760c5200b4fc760c520006df630c5200b6dc630c52000dee720c520005ed720c520025fa700c520005f9700c52000cfe76cc12000cfc76cc120006df63cc1200b6dc63cc12000dee72cc120005ed72cc1200adfa768c120026fa768c1202577b548c12025779548c1200d5f9738c1200b6fa638c1200b6f8638c12000dfa728c120025f8728c120026fb628c120027eb628c1200efea528c12025fe9528c1200efea428c120257e9428c120005f9718c1200b4ff764c12000cfe764c1200d4fd764c12000cfc764c1200057f754c1200957c754c120006df634c120006dc634c120005ef724c12000dec724c12000df8764c1200d6f8764c12000cf8764c1200077b754c12024f78754c1202477b544c12024779544c120025fb734c120027db734c120007db634c1200b6fa634c1200b6f8634c120007d8634c12024fda534c12024fd9534c120247da434c120247d9434c120007eb724c12000dfa724c12000df8724c1200d7e8724c120026fb624c120027eb624c1200d7ea524c12024fe9524c1200d7ea424c120247e9424c120005fb714c1200857e75d8f100057d75d8f10004ff75d8f1001cfe75d8f100067e75d8f1001c7e75d8f10004fd75d8f100067d75d8f100047d75d8f1001cfc75d8f10004ff74d8f10014fe74d8f10004fd74d8f10014fc74d8f100067f54d8f100067d54d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10006f671d8f10006f970d8f10004fd7698f10006df6398f100b4ff7598f1001cfe7598f10004fd7598f100b4fc7598f100b4ff7498f10014fe7498f10004fd7498f100b4fc7498f100067f5498f100067d5498f10006df5398f100b6dc5398f100b6de4398f10006dd4398f1000cfe7298f10004fd7298f1000cfc7298f10004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f100067f5458f100067d5458f10006df7358f10006df5358f10006dc5358f10006de4358f10006dd4358f10004ff7258f1000cfe7258f1000cfc7258f10006dd6318f100b4ff7518f1001cfe7518f10004fd7518f100b4fc7518f100b4ff7418f10014fe7418f10004fd7418f100b4fc7418f100067f5418f100067d5418f100b4fe7318f100b6de7318f1000cfe7218f10004fd7218f1000cfc7218f100b6f67118f100b6f97018f1007eee62d8b10004ff75d8b1001cfe75d8b10004fd75d8b1001cfc75d8b10004ff74d8b10014fe74d8b10004fd74d8b10014fc74d8b100067f54d8b100067d54d8b100b4fe73d8b10004fd73d8b1007cfd72d8b10006f671d8b10006f970d8b1000cff7658b1007eec6258b10004ff7558b1001cfe7558b10004fd755
  | 6 => 0xd630c620006f6610c620006f5610c620025fa700c620005f9700c620025fb764c220006fb764c2200077b754c22026f78754c2202677b544c22026779544c220027db734c2200b6fa634c220026f8634c22026fda534c22026fd9534c220267da434c220267d9434c22000dfa724c22000df8724c220005fb714c220004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d200067f54d8d200067d54d8d20006df53d8d20006dc53d8d20006de43d8d20006dd43d8d20024ff72d8d20024fd72d8d200eedf32d8d200eedd32d8d20004fe71d8d20004fd71d8d20006df6398d200d5f97098d200b4ff7598d2001cfe7598d20004fd7598d200b4fc7598d200b4ff7498d20014fe7498d20004fd7498d200b4fc7498d200067f5498d200067d5498d200b4fe7398d20104fd7298d200b6ed7298d20106ee4298d20006ed4298d20004fe7198d20004fd7198d200d4fd7098d200b6f97098d200057f7558d200957c7558d20105fb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20014fe7458d20004fd7458d20014fc7458d200067f5458d200067d5458d20006df7358d200d4ff7258d20006ef7258d20004ff7158d20004fc7158d20104ff7058d20006fb7058d200ecfe7618d20006dd6318d200b4ff7518d2001cfe7518d20004fd7518d200b4fc7518d200b4ff7418d20014fe7418d20004fd7418d200b4fc7418d200067f5418d200067d5418d200b6de7318d20006df5318d200b6dc5318d200b6de4318d20006dd4318d20024ff7218d2000cfe7218d20024fd7218d2000cfc7218d200aeee4218d20006ed4218d200b6df3218d200aedd3218d20004fe7118d20004fd7118d200b6f97018d20004ff75d852001cfe75d8520004fd75d852001cfc75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d85200067f54d85200067d54d85200b4fe73d8520004fd73d8520024fd72d852006eee42d8520006ed42d852006ef621d852006ef521d8520006f7619852004df970985200057f75585200957c7558520005bf745852008dbc7458520005df7358520005dc735852007dfb7058520006f56118520004ff751852001cfe7518520004fd751852001cfc7518520004ff7418520014fe7418520004fd7418520014fc74185200067f54185200067d54185200b4fe7318520004fd7318520024fd721852002ef6211852002ef52118520024fe701852002ef97018520024fc7018520004fe76cc520004fd76cc5200b4fc76cc520025fa70cc520005f970cc520004fe768c520004fd768c520004fc768c520006df638c520006dc638c520025fa708c520005f9708c520
  | 7 => 0x8430004ff7458430014fe7458430004fd7458430014fc74584300067f54584300067d5458430004ff725843000cfe725843000cfc7258430026f77158430006f65158430006f55158430006f64158430006f541584300b6f731584300b6f43158430026f61058430026f41058430004fd768c430004ff764c430005ef724c4300adec724c430004ff7688430024fe7688430004fd7688430006f66188430006f56188430004ff7648430004fd7648430024fc7648430005df73484300b5dc734843000eee6248430006ed6248430006f66148430006f56148430025fb764c030006fb764c030004fb764c0300077b754c03027f78754c0302777b544c03027779544c030025fb734c030027db734c0300b6fa634c030027da634c030006f9624c0300b7db314c030007d9314c0300b4ff7598e2001cfe7598e20004fd7598e200b4fc7598e200b4ff7498e20014fe7498e20004fd7498e200b4fc7498e200067f5498e200067d5498e20026de7398e200b6de5398e20006dd5398e200b6de4398e20006dd4398e200b6df3298e20106dd3298e20004fe7198e20004fd7198e20024fe7098e20026fa7098e20024fa7098e20024fc7098e20026de3098e20026fa3098e20026dc3098e20004ff7558e2001cfe7558e20004fd7558e2001cfc7558e20004ff7458e20014fe7458e20004fd7458e20014fc7458e200067f5458e200067d5458e20026df7358e20006de5358e20006dd5358e20006de4358e20006dd4358e200d6df3258e200d6dd3258e20004ff7158e20004fc7158e20024fe7058e20024fc7058e20026de3058e20026dc3058e20004ff759862001cfe7598620004fd759862001cfc7598620004ff7498620014fe7498620004fd7498620014fc74986200067f54986200067d54986200b4fe7398620004fd7398620026f67198620006f65198620006f55198620006f64198620006f5419862007ef6219862007ef52198620024fe7098620026fa7098620024fa7098620026f61098620026fa1098620026f41098620004ff755862001cfe7558620004fd755862001cfc7558620004ff7458620014fe7458620004fd7458620014fc74586200067f54586200067d5458620004ff73586200b4fc7358620026f77158620006f65158620006f55158620006f64158620006f5415862004ef6215862004ef52158620024fc7058620026f61058620026f410586200b4ff76cc620024fe76cc620004fd76cc620006f661cc620006f561cc620025fa70cc620005f970cc620004ff768c620024fe768c620004fd768c620006de638c620006dd638c620025fa708c620005f9708c620004ff764c620004fd764c620024fc764c620005ef724c62000dec724c620025fa704c6200b4ff760c620024fe760c620004fd760c6200b6de630c620006d
  | 8 => 0x4fe71d8930004fd71d89300d6ec21d89300d6ef20d89300057f75589300e57c75589300067f65589300067c65589300d6ec62589300ecfe76cc9300067f65cc9301ae7c65cc930024fc764c9300067f654c93019e7c654c930006ef624c93000eec624c9300d7cc324c930005fb704c930025f8704c9300067f65d85300067c65d8530004ff75d853001cfe75d8530004fd75d853001cfc75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d85300067f54d85300067d54d8530006de43d8530006dd43d853000cfe72d8530004fd72d853000cfc72d85300e57e75985300057d75985300067f65985300067c6598530006f761985300057f75585300e57c75585300067f65585300067c6558530005bf74585300ddbc7458530005ef72585300d5ec72585300067f65185300067c6518530006f56118530004ff751853001cfe7518530004fd751853001cfc7518530004ff7418530014fe7418530004fd7418530014fc74185300067f54185300067d541853000cfe7218530004fd721853000cfc7218530004fe76cc5300067f65cc53018e7c65cc530024fe768c5300067f658c53017e7c658c530006f7618c530006f4618c530025fa708c530005f9708c530024fc764c5300067f654c53016e7c654c530005ef724c5300d5ec724c530006f7614c530006f4614c530005fb704c530025f8704c530004fe760c5300067f650c5301467c650c530007d5310c530004fe7688530004fd7688530004fc76885300067f658853012e7c6588530006ef628853000eec6288530004ff7648530004fe7648530004fc76485300067f654853011e7c6548530005df7348530005dc73485300067f65cc13010e7c65cc130025de73cc130026df63cc1300077b65cc13028f7865cc1302877b54cc1302877954cc130025fa73cc130026fb63cc130027db63cc1300b7da53cc13028fd953cc1300b7da43cc130287d943cc130005f972cc130004ff755883001cfe7558830004fd755883001cfc7558830004ff7458830014fe7458830004fd7458830014fc74588300067f54588300067d545883000cfd7358830026ef72588300aeee5258830006ed52588300aeee4258830006ed42588300b6ef32588300b6ec3258830004ff7158830004fc71588300aeef2158830024fc7058830026fa3058830026ee2058830026ec2058830104ff764c830004ff759843001cfe7598430004fd759843001cfc7598430004ff7498430014fe7498430004fd7498430014fc74984300067f54984300067d549843000cfe7298430004fd729843000cfc7298430026f67198430006f65198430006f55198430006f64198430006f541984300b6f731984300b6f43198430026f61098430026f41098430004ff755843001cfe7558430004fd755843001cfc755
  | 9 => 0xc7158a300eeec2158a30024fc7058a30026ee2058a30026ec2058a300d4fd76cca30025f870cca3000cff764ca3000eee624ca30006ed624ca30005fb704ca30025f8704ca30004ff759863001cfe7598630004fd759863001cfc7598630004ff7498630014fe7498630004fd7498630014fc74986300067f54986300067d549863000cfe7298630004fd729863000cfc7298630026f67198630006f65198630006f55198630006f64198630006f54198630006f72198630006f42198630026f61098630026f41098630004ff755863001cfe7558630004fd755863001cfc7558630004ff7458630014fe7458630004fd7458630014fc74586300067f54586300067d5458630004ff725863000cfe725863000cfc7258630026f77158630006f65158630006f55158630006f64158630006f54158630006f72158630006f42158630026fa2058630026f61058630026f41058630006f6618c630006f5618c630025fa708c630005f9708c630005ef724c6300edec724c630006f6614c630006f5614c630005fb704c630025f8704c630004ff7688630024fe7688630004fd768863000eee6288630006ed6288630004ff7648630004fd7648630024fc7648630005df7348630005dc7348630025f976cc2300b6f976cc2302a77b54cc2302a77954cc230027da73cc2300b7da53cc23029fd953cc230005f972cc2300e57e76d95300e67e76d953001c7e76d95300057f74d95300057d74d95300067f64d95300067e64d95300067d64d95300067c64d95302975f73d95300e75c73d95300075e43d95300075d43d95300067e62d95300067c62d95302975e30d95302975c30d95300067f74d95300047f74d95300067e74d95300067d74d95300047d74d95300067c74d95302967f73d95300e67e73d95300e67d73d95300e67c73d95300067f43d95300067e43d95300067d43d95300067c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95300067e32d95300067c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95300067f21d95300067c21d95300067f70d95302967e70d95300e67d70d95302967c70d95300067f40d95302967e40d95300067d40d95302967c40d95302967e30d95300e67d30d95302967c30d95300067f20d95302967e20d95302967c20d95302967e10d95302967c10d953000cfe76d89300067f65d89300067c65d89300d6ee62d8930004ff75d893001cfe75d8930004fd75d893001cfc75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d89300067f54d89300067d54d8930024fd73d893000cfc73d89300d6ee42d8930006ed42d89300d6ee32d8930
  | 10 => 0xc52100cfe764c52115cfd764c52100cfc764c521006df634c521006dc634c521005ef724c52100dec724c52100df4764c52115ef4764c52100cf4764c5212bf77544c5212bf75544c521007d7734c521007d7634c5210b6f6634c5210b6f4634c521007d4634c5212bfd6434c5212bfd5434c521007e7724c52100df6724c52100df4724c52115fe4724c52115ef7624c52115fe6424c5212bfe5424c52115fd7324c52115fd5324c521174fe760c521006df630c5210b6dc630c521175f6710c521007d5310c5212b5ef74885212b5ed74885212af6f54885212af6d5488521007cf6388521006ee6388521006ec6388521007cc6388521006cc638852100dee718852100fe6718852100eef618852100fe76188521007e63188521007e53188521006df63d8121006dc63d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d81210067f54d81210067d54d81210b4fe73d8121004fd73d812107eee42d8121006ed42d812107efa20d8121005de7398121005dd7398121006df6398121006dc6398121006fb60981210057f755812111d7c7558121005bf7458121115bc7458121005df7358121005dc7358121006df6358121006dc6358121006df6318121006dc6318121026fa6018121006f9601812100cff7658b300b6ec6258b30004ff7558b3001cfe7558b30004fd7558b3001cfc7558b30004ff7458b30014fe7458b30004fd7458b30014fc7458b300067f5458b300067d5458b30024fc7358b300b6ef3258b300b6ec3258b30004ff7158b30004fc7158b30106ef2058b300acff764cb300b7cc324cb300b6f76198730004ff759873001cfe7598730004fd759873001cfc7598730004ff7498730014fe7498730004fd7498730014fc74987300067f54987300067d5498730024fe739873000cfe7298730004fd729873000cfc72987300b6f731987300b6f431987300b6f46158730004ff755873001cfe7558730004fd755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc74587300067f54587300067d5458730024fc7358730006de4358730006dd4358730004ff725873000cfe725873000cfc72587300b6f731587300b6f43158730005ef724c730105ec724c7300b7d4314c730004ff76887300b4fe7688730004fd7688730006f66188730006f56188730004ff7648730004fd76487300b4fc7648730005df73487300b5dc7348730006f66148730006f56148730004ff7558a3001cfe7558a30004fd7558a3001cfc7558a30004ff7458a30014fe7458a30004fd7458a30014fc7458a300067f5458a300067d5458a30026ef7258a300eeee5258a30006ed5258a300eeee4258a30006ed4258a300eeee3258a30004ff7158a30004f
  | 11 => 0x4fd7498d210b4fc7498d210067f5498d210067d5498d210b4fe7398d21134de7398d21184fd7298d210b6ed7298d21186ee4298d21006ed4298d2115cfd7198d210b6f57198d21186ec2198d21024fe7098d21004fd7098d21185f77158d21004ff7558d2101cfe7558d21004fd7558d2101cfc7558d21004ff7458d21014fe7458d21004fd7458d21014fc7458d210067f5458d210067d5458d21006df7358d2115cff7258d21006ef7258d21004ef7258d21184ff7158d21006f77158d21004ff7058d21024fc7058d21174fe7618d21006dd6318d210b4ff7518d2101cfe7518d21004fd7518d210b4fc7518d210b4ff7418d21014fe7418d21004fd7418d210b4fc7418d210067f5418d210067d5418d210b6de7318d21006df5318d210b6de5318d21006dd5318d210b6dc5318d21006df4318d210b6de4318d21006dd4318d210b6dc4318d210b4ff7218d21134fd7218d21136ee4218d21006ed4218d210b6df3218d21136dd3218d210b6f57118d21136ec2118d21024fe7018d21004fd7018d21175de7618d21006de7618d21174de7618d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d21006de6418d21006dd6418d21006dc6418d210075f5418d210075d5418d21137ce4218d21007cd4218d21137d57118d21137d72118d21137cc2118d21137d42118d210b6df7518d21006de7518d21006dd7518d210b6dc7518d210b6df7418d21006de7418d21006dd7418d210b6dc7418d21006df5418d210065f5418d21006de5418d21006dd5418d210065d5418d21006dc5418d210b6df7218d21136de7218d21136dd7218d210b6dc7218d21136df5218d21136de5218d21136dd5218d21136dc5218d21136df4218d21136de4218d21136ce4218d21136dd4218d21006cd4218d21136dc4218d210b6df7118d21136dd7118d21136d57118d21006df5118d21006de5118d21006dd5118d21006dc5118d21006df4118d21006de4118d21006dd4118d21006dc4118d21136df2118d21136de2118d21136dd2118d21136dc2118d21136cc2118d210b6df7018d21006de7018d21006dd7018d210b6dc7018d21006df5018d21006de5018d21006dd5018d21006dc5018d21006df4018d21006de4018d21006dd4018d21006dc4018d21136df2018d21136de2018d21136dd2018d21136dc2018d2100cfe76cc52100cfc76cc521006df63cc5210b6dc63cc52100dee72cc521005ed72cc521134fe768c521176df638c521006dc638c521135f6768c521006f6768c5212c777548c5212c775548c52115df5738c521177d7638c5210b6f6638c5210b6f4638c521007d4638c521006d4638c52100df6728c52100df4728c521176f7628c521177e6428c5212c7e5428c521177d6328c521177d4328c5210b4ff764
  | 12 => 0x4328c621177e4328c621177c4328c621184ff764c621006df634c621006dc634c621005ef724c62100dec724c621007cf324c621185f7764c621006f7764c6212cf77544c6212cf75544c621007d7734c621007d7634c6210b6f6634c6210b6f4634c621007d4634c6212cfd6434c6212cfd5434c621007e7724c62100df6724c62100df4724c62115fe4724c62100de4724c62115fd7324c621007e7324c621007c7324c62115fd5324c62115fe4324c62100cff760c62100cfd760c6210b6de630c621006dd630c62100dee720c621005ed720c621137cc320c621007d5310c621006fb60982210057f755822112d7c7558221005bf7458221125bc7458221004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7458221006bf7458221004bf7458221014fe7458221004fd7458221014fc7458221006bc7458221014bc74582210067f54582210067d5458221004ff73582210b4fc7358221006fa4058221006f9405822104efa2058221026fa6018221006f96018221004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d210067f54d8d210067d54d8d21006df53d8d21006de53d8d21006dd53d8d21006dc53d8d21006df43d8d21006de43d8d21006dd43d8d21006dc43d8d21174ff72d8d21174fd72d8d21176df32d8d21176dd32d8d21024fe70d8d21004fd70d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d210075f54d8d210075d54d8d21177ce42d8d21007cd42d8d21177d771d8d21177d721d8d21177cc21d8d21177d421d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d210065f54d8d21006de54d8d21006dd54d8d210065d54d8d21006dc54d8d21176df72d8d21176de72d8d21176dd72d8d21176dc72d8d21176df52d8d21176de52d8d21176dd52d8d21176dc52d8d21176df42d8d21176de42d8d21176dd42d8d21176dc42d8d21176df71d8d21176dd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d21006df41d8d21006de41d8d21006dd41d8d21006dc41d8d21176df21d8d21176de21d8d21176dc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d21176df20d8d21176de20d8d21176dd20d8d21176dc20d8d21006df6398d2115df57198d210b4ff7598d2101cfe7598d21004fd7598d210b4fc7598d210b4ff7498d21014fe7498d21
  | 13 => 0xc4312e7d4414c4310b5f7764c431006f7764c431004f7764c4312e777544c4312e775544c4310b5f7734c431007d7734c4310b6f6634c4310b7d6634c4310b7d6534c4312efd5534c4312e7d7434c4310b7d4434c431007e7724c431007e4724c431006f5624c4310b7d7324c431007d5324c4310b6fb6098031026f860980310057f75580311457c75580310b6f86058031004ff75580310067f75580310047f755803101cfe7558031004fd755803101cfc75580310067c755803101c7c7558031004ff7458031014fe7458031004fd7458031014fc74580310067f54580310067d5458031004ff725803100cfe725803100cfc7258031006fa5058031006f95058031006fa4058031006f940580310b6fb30580310b6f83058031177cc32d8e21135f671d8e21004ff75d8e2101cfe75d8e21004fd75d8e2101cfc75d8e21004ff74d8e21014fe74d8e21004fd74d8e21014fc74d8e210067f54d8e210067d54d8e21006ed72d8e21176de32d8e21176dc32d8e21176ec32d8e21134fe71d8e21006f671d8e21024fe70d8e21004fd70d8e2115cfd7698e21006df6398e210b4ff7598e2101cfe7598e21004fd7598e210b4fc7598e210b4ff7498e21014fe7498e21004fd7498e210b4fc7498e210067f5498e210067d5498e210b6de4398e21006dd4398e210b6df3298e21186dd3298e210b6f67198e21024fe7098e21004fd7098e21004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e21014fe7458e21004fd7458e21014fc7458e210067f5458e210067d5458e21006df7358e21006de4358e21006dd4358e21006ef7258e2115edf3258e2115edd3258e2115eec3258e21004ff7058e21024fc7058e21006dd6318e21137cc3218e21175f67118e210b4ff7518e2101cfe7518e21004fd7518e210b4fc7518e210b4ff7418e21014fe7418e21004fd7418e210b4fc7418e210067f5418e210067d5418e210b4fe7318e210b6de7318e210b6ed7218e21136de3218e210b6dc3218e21174fe7118e210b6f67118e21024fe7018e21004fd7018e21006ed76cca212deef64cca212deed64cca212df6f54cca212df6d54cca2100dee73cca2100fce73cca21006ef63cca21007ce63cca21006ed63cca21007cd63cca21007e671cca21005ed71cca21007e571cca2100eee61cca2100fe661cca2115cfd76cc621006df63cc6210b6dc63cc62100dec72cc621007cf32cc62100cff768c62100cfd768c621006de638c621006dd638c62100dee728c621005ed728c621177cc328c62100df5768c621176f5768c62100cf5768c6212d777548c6212d775548c6210b6f6638c621007d6638c621007d5638c6210b6f4638c62100df6728c621177e6728c621007e5728c62100df4728c621007e7328c621177d6328c621177d
  | 14 => 0x15fea701893115fe97018931174fe76cc93100eec62cc931005de76cc931176de76cc931174de76cc93134ddf74cc93134ddd74cc9313475f54cc9313475d54cc93115ddd72cc931007cf62cc93100ede62cc93100edc62cc93115fcc62cc93100ecc62cc93115fce42cc931347cd42cc9310b7d771cc931005de71cc9310b7d471cc9310b6df61cc93115fcc21cc93100cfc764c931006ef624c93100eec624c931005f7714c931005f4714c93115ddc764c93100edc764c93100cdc764c93133ddf744c93133ddd744c9313375f544c9313375d544c93115ddf724c931007cf724c931007cf624c93100ede624c93100edc624c93115fcc624c93100ecc624c931007d7714c931005dc714c931007d4714c931006ef62cc531186ec62cc53132f7754cc53132f7554cc5310b7d643cc53132fd543cc531005f572cc531007e762cc531007e462cc5310b7d732cc531007d532cc531006ef628c531176ec628c5312f5df748c5312f5dd748c5313275f548c5313275d548c531005dd728c531007cf628c531176de628c531176dc628c531007cc628c531176cc628c531007d7618c531006ef62d8131006ec62d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d81310067f54d81310067d54d8131006de43d8131006dd43d813100cfe72d8131004fd72d813100cfc72d813115dee7298131005ed7298131006ef6298131006ec6298131006fb60981310057f755813116d7c7558131005bf7458131165bc7458131005ef725813115dec7258131006ef6258131006ec6258131006ef6218131006ec6218131026fa6018131006f9601813100cff76588310b6ec62588310b7cc3258831004ff755883101cfe7558831004fd755883101cfc7558831004ff7458831014fe7458831004fd7458831014fc74588310067f54588310067d5458831136ee5258831006ed5258831136ee4258831006ed42588310b6ef3258831136de3258831136dc32588310b6ec3258831136ec2158831004ff7058831024fc7058831136ef2058831184ff764c831135df734c831186de634c8310b7cc324c8310b6df64cc43131edd64cc43131f5f54cc43131f5d54cc431135de72cc4310b5dc72cc431006dd62cc431315dd738c43130ede638c43130777548c43130775548c4310b5f5738c4310b6f6638c4310b7d6638c431006f5628c4312ffd6328c4310b7d4328c431004ff764c431005ef724c431135ec724c431005df764c431006df764c431004df764c4312e6df644c4312e6dd644c4312e75f544c4312e75d544c431007cf724c431135de724c431135dc724c431007cc724c431135cc724c431006dd624c4310b5df714c4312f6de614c4312efd6514c4312efd5514c4312e7d7414
  | 15 => 0xc7458a310067f5458a310067d5458a31176ee4258a31006ed4258a31176de3258a31176ee3258a31176dc3258a31176ec2158a31004ff7058a31024fc7058a3115cfd76cca31175de73cca3100eec62cca3100cff764ca31175df734ca3100eee624ca31006ed624ca31177cc324ca31005f7714ca31005f4714ca31005dd76cc631006dd76cc63135edf64cc63135edd64cc63135f5f54cc63135f5d54cc631175de72cc631175dc72cc631006dd62cc631357d651cc631357d551cc631005f576cc6310b6f576cc63135f7754cc63135f7554cc6310b7d653cc631357d553cc631005f572cc63117d7e75d82310057d75d8231006fb6098231004ff755823101cfe7558231004fd755823101cfc7558231004ff7458231014fe7458231004fd7458231014fc74582310067f54582310067d5458231004ff725823100cfe725823100cfc7258231006fb5058231006f85058231006fa4058231006f94058231026fa6018231006f9601823100cfe76d893115eee62d8931004ff75d893101cfe75d8931004fd75d893101cfc75d8931004ff74d8931014fe74d8931004fd74d8931014fc74d89310067f54d89310067d54d8931006ef52d893115eee52d8931006ed52d893115eec52d8931006ef42d893115eee42d8931006ed42d893115eec42d893115eee32d893115eef21d8931024fe70d8931004fd70d893115eef20d893115eec20d893115dee76d893100cee76d8931006ef65d8931006ee65d8931006ed65d8931006ec65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d89310076f54d89310076d54d8931007cf73d8931007ce43d8931007cd43d8931007e771d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d89310066f54d8931006ee54d8931006ed54d89310066d54d8931006ec54d8931006ef73d893115eee73d8931006ef53d8931006ee53d8931006ed53d8931006ec53d8931006ef43d8931006ee43d8931006ed43d8931006ec43d8931006ef71d893115eee71d8931006ed71d8931006ef51d8931006ee51d8931006ed51d8931006ec51d8931006ef41d8931006ee41d8931006ed41d8931006ec41d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef50d8931006ee50d8931006ed50d8931006ec50d8931006ef40d8931006ee40d8931006ed40d8931006ec40d893115eec6258931005ee761893115eee761893115f6e751893115f6d7518931006ef6518931006ee6518931006ed6518931006ec651893115fae741893115fad7418931006ef6418931006ee6418931006ed6418931006ec64189310076f54189310076d541893115fcd7318931007ce4318931007cd431893115fe57118931
  | 16 => 0x87320b6fb6098332026f860983320057f75583321ad7c75583320b6f86058332004ff75583320067f75583320047f755833201cfe7558332004fd755833201cfc75583320067c755833201c7c7558332004ff7458332014fe7458332004fd7458332014fc74583320067f54583320067d545833200cfc73583320d6ee4258332006ed4258332004ff7158332004fc71583320b6fb30583320b6f830583320d6fa2058332386ef64cc932386ed64cc9323876f54cc9323876d54cc93200dee73cc93200fce73cc93200eef63cc93200fcf63cc932004ff75d853201cfe75d8532004fd75d853201cfc75d8532004ff74d8532014fe74d8532004fd74d8532014fc74d85320067f54d85320067d54d8532006f741d8532006f441d8532186f621d8532024fe70d8532004fd70d8532006f76198532006f56118532004ff751853201cfe7518532004fd751853201cfc7518532004ff7418532014fe7418532004fd7418532014fc74185320067f54185320067d5418532136dd7318532006ef3218532136de3218532136dc3218532136ec3218532006f74118532006f44118532136f52118532024fe7018532004fd7018532004ff75d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d81320067f54d81320067d54d8132004fe71d8132004fd71d8132106fa20d8132005f67198132005f57198132006fb60981320057f755813219d7c7558132026fa6018132006f9601813200cff7658b310b6ec6258b31004ff7558b3101cfe7558b31004fd7558b3101cfc7558b31004ff7458b31014fe7458b31004fd7458b31014fc7458b310067f5458b310067d5458b310b6ef3258b310b6ec3258b31186ef2158b31004ff7058b31024fc7058b310b5dd76ccb3100edd76ccb3100cdd76ccb310b5df74ccb3137ddd74ccb313775f54ccb313775d54ccb3100ede62ccb310b7ce62ccb310b7cd62ccb3100edc62ccb31187ce42ccb31377cd42ccb31005de71ccb310b7d671ccb310b7d571ccb31187cc21ccb31134ff764cb31005df764cb31136df764cb31134df764cb3136ddf744cb3136ddd744cb313675f544cb313675d544cb310b7cf724cb3100ede624cb3100edc624cb31005dc714cb310b6fb6098331026f860983310b6f86058331004ff755833101cfe7558331004fd755833101cfc7558331004ff7458331014fe7458331004fd7458331014fc74583310067f54583310067d5458331006de4358331006dd4358331004ff725833100cfe725833100cfc72583310b6fb30583310b6f83058331176ee62d8a31177cc32d8a3100cff7658a31176ec6258a31177ce3258a31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31014fe7458a31004fd7458a31014f
  | 17 => 0x6800000400000000100040010020000002007000800403c00000000100020000000030000004000000000c0000000000002004000001c00400000180000020020018004006001000001800400000180000000000010000000000006000800000e000800c00e00300000080040000010004000005004000c0000010000004006000003000000200b0000010000000000801c0020000010008002000000000000a000000000000000000900040020010000010004009000800800e003005003c00000000000180000060038014004000007802c004001000001401000000100000120050000004006000001802c008000001800400000400280000140000000014000003000000c002000001800800800000b00040000020000008000002001800000200000000140000020020000008000000800400000000080000020010018004000000000000800600100600080000070060004002000000800c0020060038000000007003000c004004005000800c00e001800c0180000040028000008002800c0020000018004004000002800400000600080000000040000004002004001000000c001002802401200100080040000020010000004006000800c010001000000800a00000200200000030018004002002002800000c0010008010004000000005000000a0008000006006000800c00c0040010000000000001000400000100080000060000000000000002001800800a00000000000000000000000002000000000000a00000100300000000000008000000000000000a0010028008004004000000c0020000018008006003000000400c001005800000a00400000080000020030000004004000001000800000080000060000028008012009001000c01a00100100040000010008000000000000000000c0000010000004000000001c002000001800801a000000801400800800580080040050020004002000000800c01c0000010000002001000800401800000080380000000008000000002000000400000000100000000010000008004000001000000000200200000000000010004008000002000401000200100080000040b6f76198732004ff759873201cfe7598732004fd759873201cfc7598732004ff7498732014fe7498732004fd7498732014fc74987320067f54987320067d549873200cfe7398732176de7398732176de3298732176dc32987320b6f731987320b6f43198732176f52198732024fe7098732004fd70987320b6f46158732004ff755873201cfe7558732004fd755873201cfc7558732004ff7458732014fe7458732004fd7458732014fc74587320067f54587320067d545873200cfc735873215eee4258732006ed42587320b6f731587320b6f4315873215ef6215873215eec2158732004ff7058732024fc705
  | 18 => 0xb8516c102476063d58e781000145c00000002281acb3a48a0000000000298000000000000000016b8000af2000166805289f00819211642da51097589260ae0b006c80002801f6000000000020680006f81f000000002340000000000f16a3c4eb80009289905489ea40004aa00000000000000000a283c093514222640009d80dd981000000054a26380001b10000000aa631700003200004c44be02e46a287c15080000000000000b20e28246000000121000000000000f40000001a84f306bf3f3890000000000013cc9e8000331a20c0d800007a00007e8000000000600100000080020000048004000000000000c00c004000801c000001000000400200000680080000000000000002007001801000c000001001000000000080140060010000004002005000000c000001007800c00c0000020000016000001000c0080010000000002000002000c00400a000000800000100100000000010020018000002000001400c001000000001400000080000000000018000012007000800002e001000000000200100080040000030000024002001000803000800200080000060000000004020001000000c0260000000004002009002801400400000100040000010000000010001000000400400000200040060000078004002003000003c020000000001c00400300380000040000000018000000000000400a00000180080000000000000006004001800000a00000a801400200000000040020020018000014002000800400600c007003800200000000080040000008000000000001801000000000080000000020008004002000001000000000000280140000000020018006004000800400000d00100280060020000000000001000800000a00000000000000040010014004013000800003a000002000401600200200000000000000000002000000803000e002001002400200000100000040030000000000001003000c00601b000800c00a0010000008000001000002c00200000000000020000000000000001000801c000000000000800400200200000100010030000004001002800c000000000000800400000000000040080020004006002000000c00800d004000801a008000000400000800000000020000058028002000000000400e000006800400400000000040000000000000004000000000c008000001000400000c002000000001b00300040000010008008002000001800000200100180300020010008008002001002000000000000280080000000008000006000001801c0000020020014012000000000401a000000000000000a0010004000000000801400e00000180200040050000000004002003000000a0000000004002001000000001600100000000000010000014006001000000000000100180000100000
  | 19 => 0x7f11301dfd66000000000010ce6b000001e50bc00000000000000001038000d0410a0000000000000000000000000010026dc00000000000000000000001e380004720a729fc0000004a4867d53e0000ac800083646000011b525000000000000000003ad82a40000e354380000003d60000c84708035519000066e26800000000009ae0000001382000000000109a83b222000016458700000014c69b24e70000fe00000001e90aee6852f2178c00062618a81280000000000b4800000034f1a5c934000490a2750241e657300000920af21185acbc085500000000000001b2239c000000470800000000054780009b69ff07492a0810000125800128a25a06920506440003c4800000c0002239b60a981f441f80000000001f90000b743db00024608f80000002ab56b20000000000c30000000176c0001a60000000000000586000144c8d900002706640520000000a0000040000015fc00052202d807c2ae1ef0b9562a0004152b4000000006fa590000000000000007e1001c80000d5801c28f0000c8231300000003346b94b61b8451230509180000000000000000000b1d388a44cac4944482ace5260000020800058a00037fa8c093811e47e94fc5aa37f0bf07380001d90de02f000048944580000009ac1b100006ac00035d000143815400000000003b400027300000000000000c000004080000a9240f11a0000000000000000000000000000009a600000000000003b80001e9856a4560000000000000000177800088f00000000000005a58ea4c8a0000002a4d2ae189000000079438200000000002aa01080000e0afc00010880b40003da00000000000000000bfe0002a080000007ce0d4129400000039cabb13c24500a41420cea63c0758000ace25b00000004386b317aa4f40004a234909cc000729291a1d432e0004449af000013c000000000000000027e54ae75d3f6000122253d40b00006a62935038304cf45f54249f213cca4937000000000000002b855f2772000229000000021900000000001b890bc0001580000be54b80000000f9c96c0000000000c0ca0d2912890556863484800000000000026740005150000000b7606905b8001202000214800000000000008f42f673710ba8093500cd00017080000002091f747920000000000000000000000000005f00004200000005508370eec8ce4fe0000a9e000449000028617f0000000cc000000000b8000000000000000000000005e0c1000000000000000000001580cbe0001fa800000053a000000126800023d800000000000009ec00029c00006e855a0003c9000169a0000a6883c4bab550000000000000000000000079b00000000000003f2000000000000000e00000004b58000000a0a00000000006204990394000000000000076a00000000000005b755c0
  | 20 => 0xfc003077345400000006e74b4ac9d17a8582bf19c561a4c621d99dcb2ea7800000000003a700005d00006ee0001cf80008dc00000011ac0e433588b141879931b12c40003b7000000100c1ad575800114a00007a81713b20bf000000000031e0000000000000000209400044d0000000000299000000000086551e9bf09b000000000000003f850e8000d00000555800000000000002307c00004560000ed06320ab80000000000f7adf169e1f74172284b887310001b74e3a7d1163a4e8dbc24f2899d4512092738b00e8c5a26150b9691590000561290c00000036380012c60002aea7c0d9c0aa00000004a00000000000000000307800000000000000000000000000290432000000198835c00000000000004140001a3800000003fa96c00049b2c327f800069b13e800000000000000000000004c48ae4c184a3593143cacc11419297253fa40517d8ee84044101538214ebe00000000000005c725491c122c5d4000000000000039788a8262000515182526e40c556211141e2723a296080000000002771658b5659f00000001c50000000000000050250c000000095800009ca64108a07428a0cf282971400068c3c300000000000000000dee6d32de000131a000000000111ca2748e00000000000000001262000000000096e00000009d80003990002b3400058f17911dca582a60000000d865ce000261052ca9a0c3800000050e00000000008bc000000000000013b8204000b733538c2843e0910001d30000a6054ca2ec4d60000c1800000024429aa0686f29b1000146000000000024d954eab14cb0fac0009d01702da01e046a21b8a904bc7be4cc88c424a63826b000000098b00020d800000000000002b40145840000a9429207402d4e2600c00000000000000000480c8400000000000000003f500002660000000000026527000000021aa154d38b0000003d0000000000000000000000000003300000008ca0ce831d0f481139c014c54032f0e3aae4f54a7e2c71f600005a500000001faa973cf00000003861192c106e000014824f80000004ba08755688680000000c2e9e405a1d5c7b2b230c69b40d5a8f925d0fa46c21360001d0d0a63fd55e89e40f600000000012e6b141a3203c8923d8590800000099f305018c0000000000000000000000076c45e03007fa6e46d200000000000009bf000000123e6a93248cb00007f8520898d39424807b93a800000028b1330000319035000145c601000000000000000000011ec0000da2d5000079f52cad4516e39803380009ee01e470000000007400000000008e400000000000003828000000a800000000e5074d4501f1025e3cc4c017f459c00000025051d60000000a8c0000000002bf4000000000000000049600000006360000001efc000b01103055443c65300006dc50e
  | 21 => 0x80e204da53d42820a0eb0c9c0002753b8ac3c0008204660c9000000000000008f40002b6900400016500009a862200000000000008380000000c807e80001614aa000019b0000000000000000146c0000000f500006e800021c800096d17b80000004d12bf85e4a283543af0cb822028304aaa982123c733e93f40000ba0f12b952dc0681d0137c7a439f3d0292ce881a5109252d0b212950094b42ce9580002530000588185a7e070e9c020b80014d281300000000006142b08fb80003a856011447d497d5511ce925644f0001a80000442000130c000000000000071e0005279a540000000d380005fc000000000116838c000000016200000028dc0000000002cd148c0000000000000000000000119e09817d14341ac32644da3bc71a00055500003b81b300000001868d50000da000021600013d800000000000000004e5000000000000000000000003081428000e3e0000000000d5600000021b00002bb0000000c0eb36000000000000000000f00008d119f03114f20000400000bdaa4218d0000000000000000098492000008682a00000000d3000000046a1e540000000002144000b6040c8000000a7500000000000000ce000000000000009703d08270000000d020003cd06080000003d2a0788e656c1458b086960db0000298000000000179483e0c51122b38ab800053d00000000000000000cd00000000000f7073f4609eec00032041e9eb85b60000002b7000000000010ac0000000000000000aef0001d000000000002dd4fa400000000000006f023f00009de000000000000000059000000000000000000000000461129c67261c512906024e84c00022ac428b0a000078d59400046680008e28983951a24c8e7604d28098e3423b35116a0a7824c2570f8400091e000000013e0000001240e8c00015e90106066a54c79990ef800043000000005ab000000073c1e726a27c5638b6d32d800000076c40286f800000032227ac0000004f529c00000d800000000000004f9000000049827c2a9169200001b800000000000027a400001914a051c1960001e7800004e8ff05680590361c12f48000c2000000027787ae3662810000000000000000108c95b33f01f020c97502e8750ba0000284800000072400029480000000000c50b980005811db800005000000000006502b800000000000000884e120004818000776b1200023b47a27ca09a8000b24000090932456e9c3087a6a4000000000053c90a00000000004da400000000000000032a8a747ba00013200000000000000db80000000e586ac0003fb0a09e30000b44000000000013b00022b46243965072ca000006f0002b9c8de000000000000000000000000000940fe970c000a314b30000000000000155c00000017310852c245d0072aa47b85633e82c94000000000
  | 22 => 0x900000000e0348000019400000029b10d25b10e18000ae87fe4440d40f5660b44883748942ed4e88dbc00000029982cc0005d757685895648153398ba118c39340c1994284adb0e610a9078ae00f20000000000000000000000000000000001eb0b49df8b4c1aa5392dbcee07a200023140007dc47e00009ae0000000000000abc45382484727420000e280000005578f1537627156ba084000000435800151c0003cb00010ee0002a707cc000aba1a700000009170000000e02b3a5881f5800000007c0000000000489000000000000028b40004a012984c0dd454600000000000000000fb43881d30000640d620001b384f4ab482b14d9c8011c86e0aeaaec00000016c28a022400000000003f0000000265c00049500000000008010be24685de0481db0000a085a900000009b20002312da80000000000fc40000770000a540007b25bb25dc0ac3850001bcc67600033daa2000000044a0ff946600000026bd40c2594e12a5539e6860002954d2645f1b2a75112a80c564aa245ae6d90001d9400000044385c000061a000000156600000025940009884fa14c08d6a610952824a840000002310000b42383a6d4b36a0330897844d887e00005dd2ce000479a99430a93c483000056647425907440000000cd95ac00000000000c800000000013280000002460000b9a9a200d000000000046d8134cdc433000000062c3c200000008ae25f00000000006fb0000000e1800000005441dc16153599b1220a2b49187ec9320000000000000000000000067e00010c000014e1e91af1864000af6000000145200000000010ae07300028816cc00054b000000000038c09940000000002b5505a00039080000009f73f590fc000aff0001f1c000646000278d5b0000000000133c0004b124ec0000003c6800084a3d01139e4c00000034200000008a907d96d156a0bd1ba213c2ec5e82ea8b24e564b409225180008640001a50b3000000007d511a92a5848b4407641100016bd3f64b3441000423e0000000570000000000155967000000017880000000001e9d58a7151e20de80000000000001444000000000000084a3ec9ed40006da0002410fd2b6951fa4385d2000000000000000000012e40005190002dec00006d3b3281000048812b8fe87ec0002bd800000000042d933c00000000000008ea93f3fe03011004243648000eeaa840000000522000348822c00e6151618dcc0000003d0ad78d46b484b500013964c73478bd0aa4893327000027414427d800000070b00000007f25400c70ac04568fb3fd0000000000000122d08600042100000000005ac00000000002fe1b58486ab01e68f995c400000010c00006292a38f912e000055713886e43450000000000000001800000042d0000000000000119800000000035e800000016f42014e032
  | 23 => 0xf43bd0001da80005e70000000f5800000000003ae9824b7acec00032b000000077e000000000000000000014a80986c63120954000000000000020e5be000000000000000000000000000932698f2e1ff4cc054800059c2138658110a1e5338000000000000147c0000002208000b548e25a500000000473ef141921e0000000000000000177119c10400000000000005101b5000095e000000000117271021f2ca400040200000000000004f000000005b60000000000000000114c00000051ca8580000404c5149012c5fa000000036a000000000000021b00016b437018a00000000003a200011b000074e0001e4400077800000000005f119800000000003f100000005a2439a50000000000000000000ec508969cf840000000000ba40001cd800092e4f91168000f002ea000013ce1420b30f020d410722000207d60c000000000000000049c0ca400072d1af8774534000000156c0004eb0001b48f8c8fe34e80005040000000000000000000000044a2cd1250308c860000000ff00000000001f68000a500000000d9000058b06e41f25dc08ba75436c05900000cc75a58b53a0779598b6317e148029401b00000000000000e90c7c000000000000124413f00000000000003db00003da33857980001120000000000000461000165866a00000000000004550000000000a381c9196000000020a80000007360000de0e8200025d98fc0009924dd000149c00000000000001c854d80000008ee1c180016d80004da0000cc27fb0000dd46d60a503a8cf461c0001ac8ac954a5c80fd15cc00000027180001704bc000000000048e000132c0080000002d4c7869510218000000603000056c00038e00011f4e1e9dd00000000000000790f3800000000001f800056415d197908e00000000740006352aa06800006f8597012cda800000000000007562c699bc00085a0000000d809f3000000000000000010188900000000000c3e0005350000000b1300000009486370000ca80000000b51d496eeaf500000000000001a200000000000000000000a5d38e06f50fa2670940ecce2e02049c80000000000000000ec680a36d8000e644d537200000000000000000dda0005a800000000000000000160b173a4800146860d55f00000009c42ccac900000000f926316e2a512862b4d1ee6c400016d568e80417e9f50e3c8fa0f2800000020c18080016f29244cd00000000000000000000000000102d61ca100000000b260000002c440009b300000000008b84d20001180000000155501c00000522049d03b00d4800000023519e01500000000000000d169a05658e8cfde13400000000006be000131400010e328a4940007e1000000000000000000007a60002700f6800044351a93f14249f50ab0000c4282649696e00001ca0000000fda5f856
  | 24 => 0xd68000147a6ac48e51a2ff01b840243646380000000000001a1c0005fb00000000001d82680c60beea0542e0000000024405a794ffa3e2172228cf5e56e1862ba0e065453fc921c6200000e10000518b5f1579ad8000000000000000000037f0000bdc000396000040a1ea4ce000000044c2201958f6277d4160000faa0002991934a020005430000000000000000000000000006640007873868000b6043a223000055215f13c0b780000001d91f7c00000000000000006d509725c40000000000d7072e000371000100e0710fe00013600000002d000001f10001ac93a49531de254032a00000000000000000002c8800000027d0000d50000377984c00024e329189400000002a85c4a2200046400000008b13b780012ba83952403cc3460000000df4d9495e00029b4ba28542c49c4800049f1b69e1019800000018151347542ec9b34b004de54594dcf044825b5ad9112c95932b800000068d43100005a800000010c40000643d1acc411400052380ac3aa0000c909d02f400000000000000000000000b8200000000a0000164000073455800000006100ae2d60000000000ab70000000b802364a39de400000008c90f00000002371a58bd488a0000c3567a00000000000000003f1800000037b56b2378702a541fba8e8d38000000000160a00000020706860000000000b960005ae9adc8a800000005984a88aa1f280000000000002978b186c1000167c00000000018e80000001c580000000ed0001190b28b1f0000c2400000000000000007771d28000000b33000000000000f5000000000b3700000000008d200000000000ab000000165400000000000008b500018bd48a08700014d8000000000000000072e21a8e68000000091039c0008cb00000000007f72c0a2785b200000000000000000000000b728c95ae04e40000fa00017e481441608e80000000000230000aeaa900000f180005510000000b6400000000000000001bf139000000000000000000005b81760000000000000113833a00000000000000000b2c00000000000007aa22000000000000000a0000000007d297000014222e0001f4d38e24d0002ad8fcc16314fa4750620000f08000cd24ab5968b180440001ae83a938a2bc36600012b891937b268c0000002d98ae00004cd1d097691b02130210eb00000000ba9e746c6a5345985183261b000000003447550478000000af443d8c711e000000000000000d751f00007de92e00000000000002859ee8fea00002f21840000001f980007fe57a00000011c6000101989c000ae900000009e4438000098800000000012b40008321a6a61c01277a28ea9012187bd3530000f92ac600024b0000000000000112e15e0000000000aea0000000a880004a71c182580d306480000001bf42929f4b5895a00000015
  | 25 => 0x5b72604000b180c32afd2fe0003a50000000000270800000000000121b400000004e800000000000000008cc0001431398ade3df23c0bc48ec639438ad9cb200004048000000b0026700000007004578000000000000000000062e0682dd01de5eb00006616e4654339103917e2df06ca2b8000000274800000000017b04580000000002d050d4528000002c970833000000143e02d3e1a3a82dc761478a3a4000783000000048a9b80000000f287f64de00006d8000533000073a4be11c1e213929f63a380005826d100000016b663400280000006980000000958a9d4a41798ae20fc1dc9a7caec0000001248000b5a0000000000ada00009c00a28e63f9ad894d00001622bb80000001ce13716ae65900000000008d72b4a66cc765ef2ac808d5a2a1b0b980002165a023180000000005162c0ce960001441b8c17c64a04d10982087b9562156000000041f00004b03e800002ec03e48141b80002da00000000000000004a68000896000000000053c08617611a49ea6bb4c28b700c200013f000000041e46d01e000034f22700010e811b5490824fae00052b17b000000000000000000000000000000000250800000068800000d80000000001be8000a5f2bc94980002221d200011ea82858f0000d54a8c437800000000000000000008df0000000cba00024007e400082f000028c00056a00a91492367854fd26d80006122760000ce00ce3610c7479613e0002d1820a0000161ecc000ade4bc000000000036e1c9800072342723d0d707593350b40000000325a10400084b00006b00004c0000000000009e42e8000e4a2b150c91141a8b2b39e2de800000053d9534ed200000000000000005372bdc00000000007f89ba76b1998769186b45000160c6b66cf5a18000c7a00031600007560000000000d486ec20e14bc75e907411800066200000000011ca521000000000000000020c054a483022000091a000000000000057c000177400058400019f0000000000209000083a15f05a00000003b692f56168dd3fa2988a726224bd08213b40002532288a3875c33c13f80223774f70001326b520fb00008321373e61bd4594735539800045099147900bccb80000000000f5027f39a1d894943c800000000ec3c000024548f2000505800039e9e716629f093a0004bd80000240993f700001b400013d00007827900000bcc00000011f000110c00010aa9347542a20000000000b35000000000000009920091a01df3e28e012d010c00024a502e0001371d9d35a0002f913fc0001810000d050ac6af2d199d8d067c1318932060e9cd06f2b3c6907270e30000a680933a800004d28662af13b4c5000042fa61865070e38d8000ba628d1a500a800000041100000005df307024018c66d43f8404ffe9db0002a0459e92f0
  | 26 => 0x35710f4000a76000000000027c0002528a860000f718f822a000000072400000000003d9118b1a032a4080000000000000000000000000000000056a000000000000000000000d1560921000037624880002fa60242817c12003042d09d60484774333934922869900018a80000000001bf545ea9c17f9ba56642562340d090ec9943a41b7ce7600000000000000005718000000adf4bc800085c8350002020fca00005600011a60000000bac00000000000000000000d788113a600000000014b47194f10000dcc18c414aa600000000a625583100001c48001174000000000090c32d10800000000000000bc000063300027190f0434000257d3be4f0474185849212d32d19300004bf29580000e400000000000006661148020de8a1308182a100648f0c58afc2a69ed1a003c400008d561a434f960000002de0000000315ad94840000000000000000000000000000003ce116860c0000000d5d39005b0002d3000000023f8000d14000550000000084525a8be0cf222300021c000000000000002969e828900949601a41409874000000541089806800059e00009b40971ac00008340000000b4c00000000027581fc3e32c8a6544cc0000000000de49a10002428550a9e00015e0b9e98311e0eb827000000016f55466eb3180180a14000384000000000033a0000000b1b000000000000015a0000f6e28e0e8288c72a08400029c4000b2f1a48000000000000083800030000000006a400000000015f6360000000000046500000000007cf2af988c30003922e16795500004b002880000000000385160a8a5a700000009424a9249877c5c60000d1c0000e653b8948e046b50311d680000001d3000000000000000000002dd0002bc110a8a60000e209ce9bd28180c4f6064f39e90b093c95552c04708126cb11b97cd63200027880012ec9be2a58678b2a2970f60000a9074f0000000000af800000340009723eda8ec000a8d57213b8000241000221023000011d00001aa69a33f80000000003e0130447e0003629f803807ad0c89cc00000002140000a0e000191a9300000001812cfcf1458a0000d5461e0002b400000001725379178e0875302c15c8e66a1a0002d8487233445f00000000000000000000000000000000000042417d083a2e300015f48b0000089900d26600000026a88b60001c880013d8000378916400000030dab64000af129880000004132e50000000000000101c2927cd4858ad901aa182fb09bc5c452937c800000000000000000005650000000ef600000020d04600000002a0c2d8017106868560e00000000010f200000000000002513c780000006d72df8000a4a95428da3e0f7853b1738e500000000002a14fe497e1ad1d907620000001b953de00000014f80001110002b74
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc9c64dcd62440018beca39ac4880031719473589100064fb20e6b122000c9c641cd6244001998c439ac48800e1fa1f75589100043ec26eab1220008bf845d5624400517908baac48800237e0d75589100b46e41aeab12200087e871d5624400517d0fba2c4880030fdd774589100061e3aee8b122000c3f85dd162440018790bba2c4880021fe15745891001c3e42ae8b1220008df835d1624402d1b906ba2c4880022fa1c74589100061fba8e8b122000c3c751d162440010fd0faa2c48800e1f21f54589100061fba6a8b122002c3c74d5162440010fd0eaa2c4880021f21d54589100061fba2a8b122002c3c74551624402d1bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317d5373589100062eaa6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000c5f541cd62440018baa839ac4880033390873589100066639ee4b1220028ec875096244001c5aa8a12c488003331cd42589100043fc2aed992200387c855db324400117f08bb6648800a2f21176cc91001c3f42eec992200087d85dd9324400517d09bb264880022f613764c9100043fc2aec992200387c855d9324400117f08bb2648800a2f211764c9100046fc1aec99220048f686dc53244001968c9b8a64880032d190714c91000636396ca98a2000cac72d913144001998e5b1a6288003331c8634c51000637b2ee498a2000c6c65dc9314400195ec9b9262880032b193724c5100072bb2a6218a205ce94644c431440e37890498862880039908765485100062fb2ee690a2000c5c65dcd214400193ec9b9a42880032719373485100062fb28e690a2000c5c651cd214400193ec839a428800327190734851013666310e690a2071dc4211cd2144001998e7b1242880021fe15764c11001c3e42aec98220008bf845d9304400517908bb260880023be09764c11000c76412ec982200387c851d930440010fd0dbaa60880030f193754c1100043f43eca982200087c87d95304400187eebb2260880030f1d7644c11000d74412c710220048fa869c620440018f0edb2a40880032e1db644811000c7c43ac69022042c7a76d971044083974edb2620880063ea1b72c41100161f3a2a93182000c3d745526304001c3aa8a1cc60800b0f9d15458c100061eba2a8b1820048dc8754d63040091b90ea1ac608003875514358c100046fc1aeab1020168dc835d5620400587ce8aa2c4080030f5d154588100247643aa4b1020048ec875096204001c5aa8a12c4080123721d634c8100247643ac4990200387e85dda31040010fb0bbb46208013369c1638c41002477c3ac510820008fb865c221040018f0ebbb220080032e1d376440100063daa6ec8802000c7954dd910040018f6edbaa20080032eddb7444010
  | 1 => 0xf06b96c888002a720d72d911020d5d400e5b222000ab9801cb644400117d0e296c8880022f61c52d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91100055b40865b222000ab5810cb644408357500196c888002ae60032d911020c5f43ea3b2220008bd87d47644400117d0e10ec88802a2f61c21d91100051f42843b222000a3d85087644400153d0610ec888002a760c21d911020d5d40043b222000c3f75dc3644406d56d03b86c8880022fa1f20d91100045ec3e41b222000a3e85c83644400147b0b906c8880023e60375d8d100061fba2a9b1a2002c3c7455363440015ab02196c688002b660032d8d100061f3a6cb31a2000c3e74196634400187ecaba4c6880030f1957498d100061f3aec931a2000c3d75d92634400187cea324c6880030f5d46498d100043fc22eb31a2000c3e855d2634400187b0aba4c68800e1fe1f5498d100043ec3ea931a2002c3e74d52634400187ae9aa4c6880021fe1d5498d100043ec3aa931a2002c3e74552634400187ae8aa4c68800b279d14398d100070eaa28731a200087e87d956344001878e9b2ac6880031b1cb6558d100043f438cab1a2000c3c7419563440018d8e432ac6880030fd977458d100061e32ee8b1a20008be87d91634400187eebb22c6880030f1d76458d1000656396c8b1a20008be87191634400187eea322c6880030f1d46458d1000656390c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d1000656326e4b1a200087d84dd5634400117f08baac68800a2f2117558d1000477c12eab1a20018ec825d5634400187eebba2c6880030f1d77458d100061fc2ee8b1a2000c3c85dd163440010ff0aba2c68800e1f2157458d1000477c12e8b1a20018ec825d1634400187eea3a2c6880030f1d47458d100043f43ea8b1a200387c87d51634400187ee9aa2c68800b0f1d35458d103ae36396a8b1a200087e8755163440010f90eaa2c6880030fdd15458d100161e3a2a8b1a2074c6c725516344005938e921ac6881cf331ca4358d100146e43a86b1a2000e1d5450d63440e5998e4a1ac6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031bd537258d1000636aa6e4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440011bf0eb18c688002b32096318d100161f3a2a831a2000c3d74550634400187ee8aa6c48800b0f1d154d891001c3f436eab12200087e87d956244001878e9b2ac4880021fa1c65589100061e3a0cab1220028be86dd1624400187ecbba2c4880030f19774589100045f43ec8b122000c3f75d916244001878ebb22c4880022fa1c64589100061fba8c8b122000c3c7519162440018becbb9ac4880031719773589100064fb26e6b122000
  | 2 => 0xc64d95100061eba0c9b2a2000a5e8319365440014bb06326ca880029ba0864d951000536c10c9b2a2000c3d871936544001c3d06326ca880038760c64d951000717410c9b2a2000e2d821936544001c6b02326ca880038e60064d95100051f424c5b2a2000a3d8498b6544001c68c920eca8810a9d21941d95100071c32481b2a2000f32419036544001a76e8a06ca880021f61e74d95100061fc22e9b2a200087e871d3654400187ae83a6ca8800297a0c74d95100052ec18e9b2a2000a6e821d365440014db043a6ca881de9da0474d95102153ac08e9b2a2042a7a801d365440014f3003a6ca8810a9ea0373d95100053cc06e7b2a2000a3e849cf654400147b0939eca88003175cc73d95100043f43e87b2a200087d87d0f654400187ee9a1eca880029ba0b43d951000536c1687b2a2000c3f7450f65440010fd0e21eca880021f61c43d95100051f424e5b2a2000a3d849cb65440854f500396ca880029e60072d95100043f43e85b2a200087d87d0b654400187ee9a16ca8800297a0f42d95100052ec1e85b2a2000c3f7450b65440010fd0e216ca880021f61c42d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95100053b40865b2a2000a75810cb65440854f500196ca880029e60032d95102143f43e83b2a200087d87d0765440010fd0e20eca8802e1f61c41d95100052f41883b2a2000a5d8310765440014dd0420eca880029b60841d95102153d40083b2a2000a798010765440010fd0e10eca8802e1f61c21d95100051f42043b2a2000a3d8408765440014bd0610eca880029760c21d95102153d40043b2a2000a5e83dc365440014bb07b86ca880e29da0770d95100043f43e81b2a200087d87d03654400187ee9a06ca880030fdd140d95100043f43e41b2a200087d87c83654400147d09906ca880028f61320d95100051f436ebb222000c3e76dd76444001a68e3baec8880028fa1875d91100061f3b0ebb222000c3e76d97644400117b0f32ec8880028fa1665d91100045fc3acbb222000a3e86197644400187cec32ec8880038d60465d91100051f42cc5b222000a3d8598b6444001c68cb28ec888106ad21951d91100555d436e1b222000d3b75dc3644400187ce3baec8880030f1c775d91100061eb86ebb222000a3e859d7644400187aea3aec8881daada0475d911020d5ac08ebb222000a3e871d7644400187d0e3aec8880038da0475d91100071ac08ebb222000c3f75dcf644400147d0b39ec8880028f61673d91100051fc2ae7b222000a3c855cf644400187eeab9ec888002abe0973d911000556412e7b222000e1f5394f644400117d0e29ec8880022f61c53d91100061fbaee5b222000a3e859cb644400147b0b396c8880028fe1572d91100051e42ae5b222000c3f755cb644400153
  | 3 => 0x9b1a4000c5d75d4f634800159b05a9ec690002a761053d8d200146fc3a87b1a4000e1d5450f634800587ce8aa4c6900030f5d15498d2001477c3a8531a4000e2d5450a63480070fd0fbaac6900021f6137558d200046fc1aeab1a400087e871d5634800147b083aac6900021fe157458d2001c3e42ae8b1a40008f7815d163480011e902ba2c6900021fa1f5458d2001c3e43ea8b1a400087e8755163480010f90eaa2c69000b0f9d15458d200061eba2a8b1a4000c5c75dcd63480011bf0eb18c690002972156318d200b46e41aea31a4075c7970d50634800587ce8aa0c6900030f5d15418d203a63cb82a831a4000e1d5450c63480e59b2e0a18c69000b2b9d14218d2000716aa28431a4000e8d4350863480039d2e0a10c69005b350c57118d200161f3a2a9b0a4000c3d745536148001c5aa8a16c2900023de1d611852000c7cc06ea30a40018f980dd061480eb8f2e1aa0c29000b0f9d154185200061eba2a830a4074c797055061480031f10cb8662900063e219708c52000c76410ec98a400087f855d831480070f90abb062900063e219700c5200b66c31ae018a4000c5c75d8d30480018b8ea31a60900031e1db754c1200051ec24ebb1e200087f845d763c40070fd0bba6c7880021f61774d8f1001c3fc3ea9b1e200087d87d5363c40010ff0eaa6c7880021f61d54d8f100061fba2a9b1e2002c3c7455363c40018f4eab86c78800297a176398f100b46e41aeb31e2002c3e7455263c400187ae8aa4c788003875514398f100061fba2a8b1e2002c3c7455163c40014bd0bb9ac78800237a1f5358f100062fbaea6b1e2000ad681d4d63c400153b0829ac78800a3721d4358f100070eaa286b1e20008df8758c63c400587ce8aa0c7880030f5d15418f100b46f41eebb1620008dd83dd762c400187ee8aa6c58800b0f1d154d8b100061fba2a8b162002c3c7455162c40051d90ea12c5880038b5514258b1001c3f42ced996200087d859db32c40031bd073b6658800e1fa16764cb100043ec2cec99620018dc8758d32c400359904b1a65880123d618714cb103c5e24126218e2016cda635c031c40f1b884239a4388003171d6634c3100062e3aac69862002c3e74552638400187ae8aa4c708003875514398e100246e41ae531c20048f8805d5638400587ce8aa2c7080030f5d15458e100246e43aa6b1c20048dc8750d6384001c3aa8a1ac70801237a1e3258e100052ec2864b1c2000a9d840c963840015ab02192c708012b6a003258e100161f3a2a8b142000c3d7455162840091d90ea92c5080123b21d4258a1000716aa284b1420048ef8758b3284001998e531a6308003331c9634c61013667310e690c2000ccc7358921840010fd0dba6ca8800e1fe1f64d95100061eba6c9b2a200087d8799365440010ff0eb26ca8802e1f61
  | 4 => 0x54c0014bd0620eca980029760c41d95300053741083b2a6000a6d82107654c0a54f50020eca980029e60041d95300043f43843b2a600087d87087654c00147d0810eca980028f61021d95300052f41843b2a6000a5d83087654c0a54f50010eca980029e60021d953027d2f41ee1b2a600087e87d03654c0010fb0fa06ca980030fdd340d95300061fba281b2a600087e87c83654c0010fb0f906ca980028fa1320d95300051ec2641b2a6000a3d84197624c00587ce8aa6c4980030f5d154d893001477c3a85b126000e2d5450b624c0070fd0b38ec4980021f61671d893000c6f41ce3b12600087e87d95624c0010fd0e32ac4980028f610655893000726196ca9926000a3d84197614c00587ce8aa6c2980030f5d154d85300070eaa287b0a6000a3d84196614c0070fd0dbaac2980021fa1f65585300061e3a6cab0a6000c6c72d95614c0010fd0e32ac2980028f61065585300061e3a0cab0a6000c6c72195614c00187ecbba2c2980030f197745853000637b2ee4b0a6000c6c65dc9614c00147b08328c2980023de1d61185300161f3a2a830a6000c3d74550614c0018f0cab8462980031b1cb654c53000637b2ee498a6000c6c65dc9314c001caeca98862980021fe15768853001c3e42aed10a60008bf845da214c00517908bb4429800e1fa1776485300043ec2eec90a60168dc831d9214c0018becbb9a42980031719773485300062fb28e690a6000c5c651cd214c0a58f4edb2e609814b96d8f65cc1300161f3a2a8b106000c3d74551620c0091d90ea92c41805ab320d52588300247643a84b106000e2d54509620c0070fd0a38ac4180021f61471588300145f420e2b1060008bd841c5620c0031bb0638ac4180030fdd154984300161e3a2a930860048f587946610c0091eb0f20cc2180038d55241984300061fba2a8b086002c3c74551610c0091e90ea8ac2180038d55241584300247a43a82b0860048f587986210c05d1bf06bb2421805b331cd62484300b66a39cc290860048f487585210c02d9a8e6b0a42180031e1d7764c0300063daa6ec9806000c7954dd9300c0018f6edbaa60181eb1e9c35498e200161f3a2a931c4000c3d7455263880f38f4e0aa4c710003875514398e200161f3a2a8b1c4000c3d7455163880091b90ea9ac7100123721d4358e200070eaa286b1c40168de83dd661880011bb07bacc3100123ea0375986200247d406e930c407ac7a70d52618800187ee8aa4c31000b0f1d154986203ce3d382a930c40048f58794661880091eb0f20cc3100038d55241986200061fba2a8b0c4002c3c7455161880091e90ea8ac3100038d55241586200247a43a82b0c4004cf27058731880070fd0bbb463100021f617768c6200247d406ed18c4004cda7058e31880091f501bb2631000b0f9d154d8d200061eba2a
  | 5 => 0x803a35084018d210056b4088031a4200ad581100634842d998c6b96629085ab520e768c5210072baa0c718a4200e555418e31484f9d8c8431c6290803b1508638c52117666396c698a4226ccc7218d3148401998c7b9262908bb351db734c521176e2396e698a422ecd476d8d314842d9a8ec31a62908af391db724c5210b56a4326218a422b8ed8798e214844d59d0731c429080333dd0638852100666ba0c710a4200e4f5418e2148401c9aa831c429089bb1604638852113667388c710a4226ec67118e2148401d88c718c4290806b921931885210076231a6310a4200c3f745536048405878e8aa6c09080b2b9d142d812100716aa285b024271cd57118e60484011bd0fb1ac09080317dd763581210062e3aec6b024200c9f74d8d6048401938e9b1ac09080237a1c63581210062fba8c6b024200c5c7518d604840193ee831ac090803271d063581210047dc3ac03024202c3e7455162cc00187ae8aa2c5980030fdd154987300161e3a2a930e6000c3f7455161cc005878e8aa2c39800387551435873000c7ac3cc310e6016cd47398521cc0031e90eb0a439800b0f9d15458a300061eba2a8b1460048ec87549628c0091d90ea12c5180038b5514258a300061fba2a930c6002c3c74552618c0091eb0f28cc318002b560e51986300247ac3c8330c6000e3554906618c0014eb0a10cc318002ad61021986300056ac184330c6000c3f74551618c005878e8aa2c3180123d21d51586300071aaa482b0c60048f487505618c0014eb0a10ac318002ad61021586300056ac1842b0c6004af280085618c0019c8e530a6318003391c9614c6300043f436e9b2a600387f87d93654c00187ae9b26ca980021f61e64d95300061fba4c9b2a6000a6e82993654c0014db05326ca980021fe1d64d95300061fba2c9b2a601c87d87193654c00187ae8326ca9814a9721943d95300068fba287b2a6000e1c6450f654c00147d09316ca980028f61262d95300043ec3ce9b2a6000c3f749d3654c00187f08ba6ca980021fa1c74d95300061eba0e9b2a607ba5e831d3654c0a54bb063a6ca9814a1fa1f43d95300043ec3e87b2a6000c3f74d0f654c0014dd05a1eca980029b60b43d95300061fba287b2a600087e8710f654c0390fb0e21eca980028fa1272d95300051ec24e5b2a6052a7a801cb654c0014f300396ca980021fa1f42d95300043ec3e85b2a6000c3f74d0b654c0014bd07a16ca980029760f42d95300061fba285b2a600087e8710b654c0010fb0e216ca980021fa1c32d95300e43ec3865b2a6000a3e840cb654c00147b08196ca980029da0432d95300053ac0865b2a6052a7a800cb654c00147f08b8eca980028f21171d95300043f43e83b2a600087d87d07654c00187ee920eca980021fa1c41d95300043ec3883b2a6000c3f741076
  | 6 => 0x566c1081b1a4200ad68110363484015ab02206c69080b0f9d15498d210061eba2a931a42028ef8750a6348401c5aa8a14c69089b339cd4298d210046fc1aeab1a42008ef825d563484011bf06ba2c6908023be097458d210047bc0ae8b1a4200c3f745516348405878e8aa2c6908031bd537258d2100636aa6e4b1a42008df8758c634842d1b906ba8c69085a3720d7418d213ae3ab8ea831a4202c3e74550634840187ae8aa0c6909d31d5c55418d210052f42e8631a4200a5d85d0c6348401c3aa9a18c690802b360b4318d210070eaa28631a4272cd57150c634840595ce8a10c6908038b5514218d2100747a1a8431a4200e8d4350863484039cae2a10c6908021fe157018d2101c3e42ae031a42008dd87994634840153d09328c690802a76126518d210046fc3aca31a42008dd8799063484014bd0b320c690802976166418d210046fc3ac831a4283ad78159063484014bd0a320c690802976146418d214162f3b6a831a4281c5e765506348401c3ec8aa0c690803871915418d2100747b228431a4200f0d54508634842d8beeb3a8c69080297a167418d210052ec2ce831a4226ace829d0634840159b053a0c690803355c57418d2140727216a831a4280e5571d506348501c9843aa0c6909fe976165418d210070faa4a831a4226ace82950634840159b052a0c69080387e115418d210070f3a2a831a4200e1d7455063484fdc3e84aa0c6909fb939095418d213f70ea12a831a427ee557155063484fdc9842aa0c6909f697a145418d2113567410a831a4200acd82150634844d59f08a10c69089ba3e114218d21007473a28431a4200e8d745086348401c9ea8a10c690803a39514218d2100726aa28431a4200e8d545086348401c1aa8a10c690803b1e054218d210056640a8431a4200ec481508634844dd8ae2a10c690802a7a135118d210054ec26a231a4226ace82d44634840159b05a88c690802b3e095118d2113566412a231a4200a5e85d0463484014bb0ba08c69089ab3a0b4118d2100566c168231a4200e8d42d046348401c3aa9208c69089ab320a4118d2100567c128231a4226acc825046348401d1a84a08c69085a37a1c4118d210046ec388231a4200a5e8510463484014bb0a208c690803875504118d21135674108231a4200acd8210463484015b500208c690802b66004118d210052fc2ae031a4200a5c855c0634842d1bd0e280c6908023761c5018d210054f420a031a4200a9d84140634844d59d04280c690802b36085018d210056b408a031a4200ad58114063484014bd0ba00c690802976174018d210070eaa68031a4226ace82d00634840159b05a00c690803a350a4018d210070eaa28031a42168de8710063484011bb0e200c69080297a144018d210052ec288031a4226ace82100634840159b04200c69
  | 7 => 0x3d7455263884e98ece2aa4c710803875514398e210061fba2a8b1c4202c3c7455163884051b90ea1ac710803875514358e210046fc3ac631c4202c3e74550638840187ae8aa0c7108021fe157018e2101c3e42ae031c422e8ef8758f328845d39f0eb1e65108bb719ce71cca2118477c32e3994422bccd76ccb31884573cb0f99463108baf1a0f328c62117666396c698c42008de8718d318844d998e431a63108ba73a1f324c62118667bb66498c422edc472dcd31884033ad0fb1a6310802f160b634c621176e2396c698c42009d68718d318844db88e431a631080679a1f724c62100673bb6e498c422bbc483dc9318845d3cd0f9926310802f1a1f324c621176e343e6498c422e9c687cc93188461b8eed9926310803b1ddb324c621427a3aa66498c4284f4554cc931884011bf0eb18631089af1209310c621006e2b926218c420387e87dd560884010fb09baac1108022fe1175582210145e422eab0442028be87dd1608840187eebba2c1108030f1d774582210061fc2ee8b044200c3c85dd160884010ff0aba2c11080e1f21574582210061fba8e8b044200c3c751d160884010fd0faa2c11080e1f21f54582210061fba6a8b044202c3c74d5160884010fd0eaa2c1108021f21d54582210061fba2a8b044202c3c745516088405970e9202c11080a3e21d40582210071caa280b0442008fb87580608840187ee8aa6c69080b0f1d154d8d210062ebaea7b1a42038df8754f634840153d0829ec690802a761053d8d210052f42e87b1a4200a5d85d0f6348401c3aa9a1ec69080a37e1d43d8d210070eaa287b1a4200a5e8510f63484014bb0a21ec690802a7a1265d8d210054ec24cbb1a4200a5e8599363484014bb0b326c69080297a1464d8d210052ec28c9b1a4200e1f645536348401c38c8aa6c690803c355142d8d210054f424ebb1a4200a9d849d763484018baea3aec69080297a1674d8d210052ec2ce9b1a4200a5e851d363484014bb0a3a6c6908bab3a0874d8d2100566c10e9b1a4200e1f549536348401c3f08aa6c69080387dd154d8d210070e3a2a9b1a4281e1f425536348503c3a84aa6c690802a7a1351d8d210054ec26a3b1a4200a5e85d0763484014bb0ba0ec6908038755241d8d210046f43883b1a42008dd8710763484014bd0a20ec6908029761441d8d210070eaa083b1a422eace82107634840159b0420ec690802b6a0041d8d210056cc0083b1a4200a5e85dc363484014bb0bb86c69080237a1c50d8d210046ec38a1b1a4200a9e84143634840153b08286c6908bab3a0850d8d2100566c10a1b1a4200ad68114363484015ab02286c69080297a1740d8d210052ec2e81b1a4200e1d54d036348401c3aa8a06c69080237a1c40d8d210046ec3881b1a4200a5e8510363484014bb0a206c6908bab3a0840d8d210
  | 8 => 0x9a8ec498802ab61351d89310053742e83b126200a6d85d07624c401c5aa920ec4988023ba1c41d893115c76c3883b126200a6e85107624c4014db0a20ec4988038b55041d89310056741883b126200acd83107624c4015d50020ec498802ba60041d893100537c2ae1b126200a6c855c3624c40155f08b86c498802ab21170d893100477438a1b1262008ed87143624c40155d08286c498802ab61050d893100567418a1b126200acd83143624c4015cd02286c498802b960450d89310053742e81b126200a6d85d03624c401c5aa9a06c4988038b55140d89310047743881b1262008ed87103624c4014dd0a206c4988029b61440d89310056741881b126200acd83103624c4015cd02206c498802b960440d893100476c3cca3126200aae84994624c40155b09328c498802b360e651893100477c3aca3126200acf83594624c4011db0f320c4988029ba16641893100536c2cc83126200acd83990624c4011df0eb20c498802b3e0d641893100573c0ac83126200a6e85190624c4014db0a320c4989ceb3a0c641893141727b1ea83126200e2f64550624c401c58c8aa0c498a0793d8d541893100567434863126200ace8650c624c4015990ca18c498803a3d91431893100786aa2863126200bc48150c624c45d998c53b66498806b3a1b62cc931006673b6c5992622eccc629c7324c4019cec438a64988bab3a1b724c93100e663b6e49926201ace86d89324c457998edb12649889b33188714c931006e3b90e29926216dc7325cb314c45d1b90cb9462988bb33189728c53117567436c518a6200c3f74553604c405878e8aa6c0988038755143d81310047743ec4b026200c6f75d89604c4018d8ebb12c0988032bdd36258131006563a6c4b0262008ee87189604c4018deea312c0988031b1d4625813100657ba0c4b026200cac74189604c4011f70eb00c09880b0f9d154588310061eba2a8b1062168ec87549620c42d1d90ea12c4188038b55142588311346fc3ac59886226cce7258b310c42dd8864b14621880317d53764c4310062eaa6ec9886200cd651dd9310c4019aaa3bb2621889a73a1f724c43100667bb6e49886200ccf761c9310c44d1b90eb12621889b331c9624c4310063baa6ec9886200c7554dd9310c42d9aca7bb262188033554f764c43100673bb6e49886200ce7761c9310c4f9b8ee6392621885bb1cc9624c4310043ec26eab006200a3d841d5600c4010ff0aba2c01880e1f21574580310043f43ea8b00620387c87d51600c4010fd0eaa2c0188021f21d54580310161f3a2a8b006200c3d74551600c4078f0eb282c01885a3e21d50580310b47c43a80b006200e3954501600c4091f501baec7108023e60375d8e210047b40ee9b1c4200c3f745536388405878e8aa6c7109d71d9c75498e210161f3a2a931c4200c
  | 9 => 0x10020240000401803800806002010010090000000200403200c0280000401803805002008040000200700000c00000c0100c02200000818008050010120000a80002d0000380100103602004006002000028140000100200400002c000000220000080103800c080010000041280202c01000802000004000000040200701002c018de83dd661cc8091f501bacc3990023e603759873200c6f41ee930e6475c5e73d5261cc80187ee8aa4c39900b0f1d154987323a62f39aa930e6400c3f7455161cc805878e8aa2c3990038b551425873201c3f43eeab06640087d84dd560cc80147b083aac1990021fe15745833201c3e42ae8b06640087e87d5160cc8070f90faa2c1990021fa1d54583320043e43aa8b066402c3e7455160cc80187ae8aa2c19900b2b1d1425833200716aa284b066402c3e74553614c80187ae8aa6c2990038d55041d85320056ac1883b0a6400ae582107614c8015e30020ec2990023de1d61185323e56bc1ac230a64018dd83dd4614c8031bb07ba0c2991d7175cf54185320161f3a2a830a6400c3d74550614c8e98bae6aa0c2990038d550411853200578c008230a640087f855c0614c8070f90ab80c29900b0f9d154d81320061eba2a9b0264008fb87580604c80587ce8aa2c5988030f5d15458b3101c3f42ee0b16620087d85dc162cc40517d09b82c5988022f6137058b310161f3a2a8b066200c3d7455160cc401c3aa8a1ac1988030fdd15458a310161e3a2a8b1462028ec87509628c401c5aa8a12c51880e1fa177058a310043ec2ee0b14627cdc4321c5328c45d1bf0eb1663188bb339c962cc6310053d42ec13046200c3f74551608c405878e8aa2c118802ae61050582310056cc18a0b046200ae982141608c4015e502282c11880a3e21d40582310071caa280b0462008fb87580608c40187ee8aa6c49880b0f1d154d893101c77c3aa5b126200a6e85d0b624c4014db0ba16c4988038b55342d893101477c3a85b126200e2d5450b624c4010ff0ab86c49880e1f21570d89310045fc22e1b1262028bc845c3624c40155d0932ec498802ab61265d89310053742cc9b126200a6d85993624c4014dd0a326c4988029b61464d89313ae373b6a9b126274c6e76553624c401c5ec8aa6c4988038b19154d8931396673b287b126200f0d5450f624c40178902a1ec498802aba1275d893100556c24ebb126200a6e859d3624c4014db0b3a6c4988029ba1474d893100536c28e9b126200ace831d3624c40159b063a6c4988038bd5254d893100717c22a9b126200e2f74553624c401c58e8aa6c49880393d4e53d893100557420a7b126200aad8414f624c4011dd0fa1ec4988023b61f43d89310053742e87b126200a6d85d0f624c401c5aa9a1ec4988038b55143d89310053742887b126200a6d8510f624c40155d
  | 10 => 0xb688487031e0c059a3a438673696e9ec8025007ee1807be4b2766000a26000a560f48e065866c1389f0a64a862ae8d60c25e211c1c200033a37e3002181e430e84029695a00005815e0001b80008621982948744786920006742f419c0560002de8389bc95e1a600038e36e01e88280a3804c45941f418673200026400000000000000000098876a0d60001d2a0a000a6aa1243e4e85a46d60003828c80000003ea39e45863e0a0000000a3e8f6000000a7a3546be0002b05b47e09100005de6b28be00073a97a0001d80008721664204985d00000002e41ee0d80e00aa4da00041c9b888809a04a9a45b83ba2e6900a209224685c2812000000a6e55a5b60000000000003c87f00b85d80000000001ae5660009b400000000000027256c70c54427a0005081100000000000000007d85c46d03768c682ea580b280e000000000a1463455c0000004140000268487b61e61766b435e7cc8d88f40005a0536a403105248341568cc40273068c3629be63614a4de0003340000000004880003fa4d8a029440003cc6020000001620000001025eeaac32a0000007a000000059800054600026c0008fe98a70274a8e820a714000a3c0000000000000000001b644000000094c21a7d62145705860000000000009ac0000001e8a620000002c400092c00a0000000000002ba4f224c8046129ba000000000000940000a4400000077e00086800002441082800010e0080400000c000000058010000000700100c010088050040040180701c00018000002004050010000000101000a000008040060400000a00801802800014094000000320140800800c0100a00005c0440000c03806c00000054014038060180040a00d01000c000010020080580000a0000000200a0200100300a0740280301a004028000000280280100800c0080200001c1480500e01804003000008000000000140000e012038008000040000302500c004000010040300100100c02c0082000a068010100080040d01300a0580083f000004008000220040600100000000005006020000030020d80082100e00c0e00a0000000100e0000300f0000020380000d0000000100c00a0000280500c0040300700600400001018004058030000180080e00c0200100301e02c0081a0180081c0010080100001703a0a000003002020030000260000880002e0280000400000000003000014038010000640080001e000010050020080400000a0000280a00004c000030000300c00200000c0001300a0080180200400001803016080008040020100100000000000001008000060070020000300000006c0380000e07c0101103200c038200000080100a01400c010020340040002500400006004000000040600040040000002c008008070020340803500a0040080800601000821002008048
  | 11 => 0xa67838a000000000a920005909920360081e24d610a374a6670400058c00000070e9fe57c0e800012a42a78c3e06c282622c2a04c25e042814022020059c9388a212295067a6649726304ec51e04e0e46cc5a80000000000008aa61479a10886461ca5a4769089700000000000000008b40a41ba05a93a7a832e91a3943f83c27ea7626540007e693c3dea7254e87a0000009ce0000008b6ab29461f207045e610a8a0049125680000007dc534a1e9ee23e16c5f662a6e03f249c48264a6e675e6260cc09e8fa3a83b88f088e43460e0522f253029a4726ceaaaa361f88ac55681c0222762842a4a382fa3fe2e05500000005400ce5f223015000062c1dc5101a446416e00089c5a244e84a9ae7ba1003d25323eca902dc5280000002ec0000008582786dc7343b400092a0000000b61d05dc1fa64e9aa000136a9408a00048c00012e0007904123d44c04181589f22320003726de7c67f414c30400000000051a0925aa2560486ec5f8000a5e0000000000001844c60008d20002d80000322ea742000962000560a2e1786fc8e67d200000000000000000000000064c38c7de42411e3402be8ec8ae0008780c428000075aa4a9a66c820c0f09946ba3207522524dc0ac90c4907f236c6fa7ce35834a000a9c2867a20000004c86080000008f2118a229da72c31634c6041cc06c2d04f614449244c000416a549d43b6000a4e8d072a00000013a00027e0000144560008806c02ce00061e0b0a800000009607100000000000007948de000a9e3dc67c32221c91e00075033e404a4603a0000000a28109760e213c21e4a20fa6a63c66f600c00e13203c6d8a306e246c29c5be0002749680002587ca94290200062215220479658276ea884f000028e82c000146ab400099883c0000007f63d6000a842b2000000a6c2a6886a744460000000007da84eaa65c86286880004a62060007560001f60f2000780000806172554a0c3f46846f022a5fa98006e7d48d465e0bc2f84266386ae73c7a466024469884432899ca1a8b20962a86a25164e478a0280ca7541167ec876a044ac06a53c89a11a3ae5f023660c04600078455e18a7644be00071ca525ec3784ba1a277081e9566b698e22e5ba3e44d24009183c05f46c40805cc10685c0000004ae0946ee1265e40005c047c8b019aa183507206f8000222000aae8921b207e7d014250c50405e00085a43a68a1ea6180001a80000ae00001c0000000002e85587164229fa0000004947761c800017e3020000060000001fc7589527aa69e4ce96a0000003ee4066a013e49e4800000002383d80b400008c9a208e5203365fe0008a600000043083a78e00099600041a0000000002bc36825a36648a33c59243800007865a4600008a47e800061a5b2738a7e0100004cc4a49b040a48487e72681a5782fc8ea2
  | 12 => 0x51c4528ba0006e4a341fe45a7780d41ce69a56272e39c9a80000004964500009d68546485c67923c41140000689ea1c67b454aa4818c8e270a5060005482089d890687c00000096c38400051486a9f43a200000000000200000031200000000000091c00080c00002a0000160009c48983420006aa00000039057203e090356538a4c2da54277c39674400000079c18894803067626e00007c90419082056445454c1a033802c1ca73e5bc0180003084080007187a66f40c60003a079865063200046e0000009f69646b84aa7b090e40ca700760720de0661202b898496674e8140ee5e64361be0000007c49ca00032c8464fe0004fc8f801244400000000024833200000088c6ea00052235c09c0000000003141bc00068e1d60009321705aea24254a109c82ca3b264689422624e9542aa9c23fc97c58a93625e5ce83626286036003422407a0005d29e86d29345187e46209e215490a17a000a68a4223a1488ee6408c49fc19459e2347ae88a8ca7ac00015a3ac40e02019e1ec1960000006ac3304ea624a9a9162700001822d618e0000000000000000000005e86521040004b092037c4862c057e000ab021021217400067e00043c2c27fe0000fc8c0a82896474a3a06413022800004c0009c08fc0e62908da000000000000000000a760001ac1242e28a044800000000052a00000058871a2cc00052606200068295850a82481683e6bca9800066e00005066886e14e16400074c8500002eea069285ac17c84c52e0fe9745d470678634846a25ca502b46fe9b24b80f63da32625098693e3445a602e4704fa1927fc2466d453e3e642e8bc16a58024a0387282a22023ce084318000040a600423f61c0346aa89e44f471e1f062e3aa0d02fe8c269083028a0002d47488564bc48e34e5da2683a65529de0005767c031a69600086680000045c5745960000006c668063a4a80002f60008327605b046631c47e890a1600064200029899a9786e86da5fc2d285299e0dca1c86c1600008e49243887886ca53a6721d42f02924625ca0a83ca7742aca9675caa24ee7c29dc26600049a63c1e077a1c49c66440006667bc00000000023c5ea71269c0000004ca65600000000095c3923e80004320009820001283f00000000000000eaa280000000007fa0000004e28b8a8ca320002609d000006041e00098c9f80001da2401aa65c52c7249d281810c2420000000000000000820869140001b400000094a9cc50260650e8080000883be0c876c00013400076800000036400074657a70092e0007400000006b000000000058400000000000000000030630c0000007b869400000000009820e30a00000044a6169e600039a6a844236a0009a0000822168000000512000000a2a0002c80ba37a0009307b20009e0a2ca7c00056e000000000772000a0066
  | 13 => 0x79e000a8e6a44a000005c72285e1de3986f21b00be00027c0d212ca5c3248ce7081124f899000000000000000028c0007c8000000aa40000da05435a00094e0000ec4d40f8000a785d67f807426aa0e8dc3bc0a62829b658e60a82aaa03b028866201a4e03e28426007e237097e68678256a67021692629e8a82c64b64d03d015c89e42c04447aa084e64b4352
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x801a315460041d85320068c55180104614c80582c875514258a310048e65285d82608c40583887551405823142f039d95450f624c401b055420543d89310058364c74553624c40182e8755343d89310060ba1d54107624c401a0d5460c41d89310068a55180107624c4012c491219431893100683a195450c624c401a0c865514318931006c15508150c624c4f94c696dc8714c93101c0f26174551600c40143691dd154d8e210160721d5450d638845d1c49760b634c62113471261724c431884014389755140582210160e21d54501608840160d921d154d8d2100607a1d541076348401a0d5460841d8d210068655180107634840121d94a1770d8d210160be1d5450a6348401a0d5460b4318d2142f055c55450c63484e9c25715514218d21005836574350863484e5c857150d4218d210058364a745506348401c15715d15418d2100583656745086348401c85715d14218d213fd836565450863484fde05715514218d2100781553815086348401a0d542054218d210053165c815086348401e05542054218d210068361542d04634844d28c985094118d210060761d541046348401a0d546084118d210068655180104634840121d942157018d210068355182d00634840188d875084018d2100683615421006348401a85426044018d21007815514218e3148401c0f7455063885210060bdd182993654c00703e98dd164d95300040fe6174193654c00103f985d074d95300060bdd182d0f654c00181f7460f42d953000607dd183107654c00182f7460841d95300060edd180107654c00582f8755142d89300040f65287d95624c00103d981d065585300060b61072195614c00103e9819774585300050b65065dc9614c00143994195708c5300050b65065dc9314c00141d94197734853000507650651cd214c001439941d7764c03001607e1d5450f634800582f875514298d2001c0f261745516348001434915d15458d200050765075dcd634800121d942156318d2042f065c15450c63480e9c29705514218d20397225c143508634800141d941d7634c120005076507518d304800703e98dd154d8f100050e652755c363c400121d94a176398f100048765285dcd63c400581c875514358f100160b21d5450962c400141d941d6634c310005076507558d30c4001a0d8360864d95100068960981193654400143a96dd140d95100060bdd182d0f654400181f7460f42d95100050764e76dd7644400142d929db75d91100060da1871dd7644400143a96dd770d91100050764e71dd7644400142d929c775d91100050e64271dd7644400182f75e0973d911000607dd7835cb644400141f975514398d100160721d5450d634410bc0c725514358d100160b21d545096244001c0d541cd42589100040f65287d95304400103e981d7644c110
  | 1 => 0x202c00002293970035000f3783af0320800ea22a00001500003700000a000610242c881b27a8a31d309f000aa4a7002d8680a100238000002e00001984a6b4002d0425003a2b0d0db9001fb32931001c00398532328b96bb899a00000fb495b5b6baa580000000118000010000281901b882b39280298000001d961100141b800700079c800b00182f803b00000017a6089eb82b9a892ab014b6319885931092000000218e1e002e8c0000003c0c800200c400004001c3014240c1438005400043800003c002c0818000c0c30000070000010280c0c2418180703c985d154583320050b25d5450960cc801a155460c41d85320068955182107614c
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1400002a04a12195450c624c401442542e2ba28431a4200d0165d542054218d21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4d
  | 7 => 0x4e
  | 8 => 0x138d
  | 9 => 0x94b
  | 10 => 0x94d
  | 11 => 0x94e
  | 12 => 0x124d
  | 13 => 0x124b
  | 14 => 0x124e
  | 15 => 0x138b
  | 16 => 0x138e
  | 17 => 0x98d
  | 18 => 0x98e
  | 19 => 0x128d
  | 20 => 0x128e
  | 21 => 0xcb
  | 22 => 0x4
  | 23 => 0xcd
  | 24 => 0xce
  | 25 => 0x168d
  | 26 => 0x9cb
  | 27 => 0x9cd
  | 28 => 0x9ce
  | 29 => 0x12cb
  | 30 => 0x12cd
  | 31 => 0x12ce
  | 32 => 0x168b
  | 33 => 0x168e
  | 34 => 0xb0d
  | 35 => 0xb0e
  | 36 => 0x140d
  | 37 => 0x140e
  | 38 => 0x24b
  | 39 => 0x24d
  | 40 => 0x24e
  | 41 => 0x144d
  | 42 => 0x16cd
  | 43 => 0xb4b
  | 44 => 0xb4d
  | 45 => 0xb4e
  | 46 => 0x144b
  | 47 => 0x144e
  | 48 => 0x16cb
  | 49 => 0x16ce
  | 50 => 0xccd
  | 51 => 0xcce
  | 52 => 0x170d
  | 53 => 0x170e
  | 54 => 0x94055
  | 55 => 0x95395
  | 56 => 0x94056
  | 57 => 0x138955
  | 58 => 0x138956
  | 59 => 0x98955
  | 60 => 0x98956
  | 61 => 0x94995
  | 62 => 0x128955
  | 63 => 0x128956
  | 64 => 0x95295
  | 65 => 0x1489
  | 66 => 0x14c9
  | 67 => 0x139255
  | 68 => 0x125395
  | 69 => 0x99255
  | 70 => 0x99256
  | 71 => 0x124995
  | 72 => 0x9c995
  | 73 => 0x9c996
  | 74 => 0x12c995
  | 75 => 0x12c996
  | 76 => 0x9d295
  | 77 => 0x9d296
  | 78 => 0x9c0d5
  | 79 => 0x9c0d6
  | 80 => 0x1689d5
  | 81 => 0x1689d6
  | 82 => 0x17c9
  | 83 => 0x1692d6
  | 84 => 0x1692d5
  | 85 => 0x140b15
  | 86 => 0xb1415
  | 87 => 0xb4b15
  | 88 => 0x144b15
  | 89 => 0xb5415
  | 90 => 0x145415
  | 91 => 0x171415
  | 92 => 0xb4255
  | 93 => 0xb4256
  | 94 => 0xb5455
  | 95 => 0x144253
  | 96 => 0x144255
  | 97 => 0x1456d5
  | 98 => 0x24b55
  | 99 => 0x16c255
  | 100 => 0x144b55
  | 101 => 0x16cb55
  | 102 => 0xccb55
  | 103 => 0xb4cd5
  | 104 => 0x170b55
  | 105 => 0xb5715
  | 106 => 0x16d456
  | 107 => 0x16d455
  | 108 => 0xcd6d5
  | 109 => 0x16ccd5
  | 110 => 0x1716d5
  | 111 => 0x16d715
  | 112 => 0x170cd5
  | 113 => 0x24953
  | 114 => 0xe8b
  | 115 => 0x178b
  | 116 => 0x104b
  | 117 => 0x1a8b
  | 118 => 0x954d5
  | 119 => 0x95496
  | 120 => 0x25393
  | 121 => 0x1049
  | 122 => 0x1a89
  | 123 => 0x9d796
  | 124 => 0x25453
  | 125 => 0x25a93
  | 126 => 0x104253
  | 127 => 0x25053
  | 128 => 0x1a8253
  | 129 => 0x105453
  | 130 => 0x1a9453
  | 131 => 0x25853
  | 132 => 0x170b541d
  | 133 => 0x104e93
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1625
  | 6 => 2941
  | 5 => 1371
  | 4 => 121
  | 3 => 3
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (66617+((h/541+packedAt gbK7 (60125+(h % 541)*12) 12) % 2146)*12) 12
  | 6 => packedAt gbK6 (153908+((h/980+packedAt gbK6 (141168+(h % 980)*13) 13) % 5167)*13) 13
  | 5 => packedAt gbK5 (85916+((h/457+packedAt gbK5 (80889+(h % 457)*11) 11) % 1810)*12) 12
  | 4 => packedAt gbK4 (8790+((h/40+packedAt gbK4 (8470+(h % 40)*8) 8) % 176)*8) 8
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe3c1e1fc3f80ffe3807e00520cfc37367c
  | 1 => 0xf0e01c01fe1fc3ff01fc007ffcac7330c9c87f
  | 2 => 0xff001ffe001ffc0001ffff8fff3183c30e0f8f
  | 3 => 0x1fffffe0000001fffff003c1fc03f00ff0
  | 4 => 0x1ffffffffffffe00000003fe0003fff000
  | 5 => 0xffffe000000000000000000003fffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x121c0c0602c04821ce083121800045413163c
  | 1 => 0x10424400a204412605240424a8043130414855
  | 2 => 0xaa048952001aa80828492909513082c10e028a
  | 3 => 0x916a5d54000145192564022c15c02f00d60
  | 4 => 0x88101b3919933258e000180043fa0003aca000
  | 5 => 0xcc9e0030110220608000600183ffeba8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeef8c0feeefeeafeeef8c0feeefeeafeeef8c0feeefeeafeeef8c0feeefeeafeeef8c0feeefeeafeeef8c0feeefeeafeeef8c0feeefeeafeeef8c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36348
namespace PEqualNP.Outside.L_meta_36348
open PEqualNP.Outside.L_meta_36348.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 4 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 12 := bs0_4_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 22 := block_range (n:=22) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 22 := bs4_3_0
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
theorem bs4_4_352 : Interval s4Atlas 4 352 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 379 := (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat bs4_4_288 (concat bs4_4_320 bs4_4_352))))
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
theorem bs4_5_576 : Interval s4Atlas 5 576 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 586 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 bs4_5_96)) (concat (concat bs4_5_128 bs4_5_160) (concat bs4_5_192 (concat bs4_5_224 bs4_5_256)))) (concat (concat (concat bs4_5_288 bs4_5_320) (concat bs4_5_352 (concat bs4_5_384 bs4_5_416))) (concat (concat bs4_5_448 bs4_5_480) (concat bs4_5_512 (concat bs4_5_544 bs4_5_576)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 29 := bs5_3_0
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
theorem bs5_4_448 : Interval s5Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 473 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 632 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
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
theorem bgb_4_96 : Interval gbAtlas 4 96 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 121 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_1344 : Interval gbAtlas 5 1344 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1371 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)))) (concat (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152))) (concat (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)) (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344))))))
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
theorem bgb_6_2912 : Interval gbAtlas 6 2912 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2941 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 (concat bgb_6_384 bgb_6_416)) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))) (concat (concat bgb_6_544 (concat bgb_6_576 bgb_6_608)) (concat bgb_6_640 (concat bgb_6_672 bgb_6_704))))) (concat (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 (concat bgb_6_832 bgb_6_864))) (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)))) (concat (concat (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)) (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248))) (concat (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)))))) (concat (concat (concat (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))) (concat (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696)) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792)))) (concat (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984))) (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176))))) (concat (concat (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336))) (concat (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)) (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)))) (concat (concat (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))) (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)))))))
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
theorem bgb_7_1600 : Interval gbAtlas 7 1600 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1625 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))))) (concat (concat (concat (concat bgb_7_800 (concat bgb_7_832 bgb_7_864)) (concat bgb_7_896 (concat bgb_7_928 bgb_7_960))) (concat (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)) (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)))) (concat (concat (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)) (concat bgb_7_1312 (concat bgb_7_1344 bgb_7_1376))) (concat (concat bgb_7_1408 (concat bgb_7_1440 bgb_7_1472)) (concat (concat bgb_7_1504 bgb_7_1536) (concat bgb_7_1568 bgb_7_1600))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeef8c0feeefeeafeeef8c0feeefeeafeeef8c0feeefeeafeeef8c0feeefeeafeeef8c0feeefeeafeeef8c0feeefeeafeeef8c0feeefeeafeeef8c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4277074112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36348.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[2,3]⟩,⟨.or,[0,2]⟩,⟨.or,[2,4]⟩,⟨.and,[0,6]⟩,⟨.or,[3,9]⟩,⟨.or,[6,8]⟩,⟨.and,[1,11]⟩,⟨.or,[7,13]⟩,⟨.or,[10,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277074112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277074112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36348

open PEqualNP.Outside.L_meta_36348 in
theorem PEqualNP.Outside.L_meta_36348 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277074112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277074112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
