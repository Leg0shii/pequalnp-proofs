import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36260.Model
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


end PEqualNP.Outside.L_meta_36260.Model

namespace PEqualNP.Outside.L_meta_36260
open PEqualNP.Outside.L_meta_36260.Model
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

def SBf (j : Nat) : Nat := [7, 4, 7, 6, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36260

namespace PEqualNP.Outside.L_meta_36260
open PEqualNP.Outside.L_meta_36260.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x59297220000042348091601180444d5001000d0724000a650a4215480100e5ab0d94387c29e0c9c11d0628c0f323158600200259201e004000207ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4800200000000000002800ad3068ec017c6ce8018800e400000000900108751934dc24001d2d40940cb87158cc453d390ca8a12060d80001789d7584c81801602c000000300014f8e0d040840050bc01697000011d0400b0f054c0391000640879810000015c007cd40010009925480000000080000000a545148804015000016400b400000128c55400014d6c00344c0000005cfcf4003c00008c5800180c00000e00140004020e26000004040002000e020204000000000400000a00077b5050ef0a0a1cf943429eaa485af5250a78a0a14f950429f2a4653d548caf4a1195e542329f2a0653d540cadca5a0db54b41af298835d531067ea898cf15131b7a92636c524c6f6a098de141319f2a0633d540c67ca990cf55321d6a14433e540867aa810d794c21aea9843ad42086f4a010de54021af29e815d53d027aa5204f94240afa9a815c53502dca4205b54840d7290813d521035aa4204b548409f28081ba501027ca9984f55330dc206619f428c33a85185794230cf204619c408c27ea8984f15130dc200619f420c33a84185794030ed28061db400c33c80186710030ec2006198400c27ca9904f55320af29e415d53c835a85904fd52209e2a441d8308827ea8904f15120afa9a415c534835a84905dd4520ba28a41d8304827ca8104f550209f2a6213d54c42bca7885754f10ec186213f5444278a88857d4d10ae29a216f52442d8a488760c010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x905044500000738f34c0920142c34c000a2040001971840001a586054c41ca50950086a96210330a3588408c2a96210030a6181420c29a6090030a3588400c2c96210030e2988400c2996210030e2588400c2896210030c6150308822c6550920c95085148318540c120e25083048350510c1208b58a54c431a540c310
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x50508755083048380a10a218241425ca540c310
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s0K5 (826+((h/15+packedAt s0K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s0K4 (2937+((h/33+packedAt s0K4 (2673+(h % 33)*8) 8) % 157)*8) 8
  | 3 => packedAt s0K3 (833+((h/7+packedAt s0K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s0K2 (150+((h/1+packedAt s0K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xc07ffc07ffff0383fffff81ff83ffe00fe73fc
  | 2 => 0xfffffff81ffffffc0fc0ffffffc1ffff23fc7f
  | 3 => 0xff81ffffe07ffffff000ffe0fffe1fffc38f8f
  | 4 => 0x1ffffff8003ffffff0000ffffe003fc0ff0
  | 5 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x530c447145122480b2c93909381232184e31bc
  | 2 => 0x85108890c824411405504a324a4144a920d455
  | 3 => 0xa2551220348a2a95028954894b41952c30a8a
  | 4 => 0x2c59a244920ecb4e69b20610e7298063b40f60
  | 5 => 0x3061c3871c70f3f38e3ce79c06311183fbe000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fcc0f000fcccf0c0fcc0f000fcccf0c0fcc0f000fcccf0c0fcc0f000fcccf0c0fcc0f000fcccf0c0fcc0f000fcccf0c0fcc0f000fcccf0c0fcc0f000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36260
namespace PEqualNP.Outside.L_meta_36260
open PEqualNP.Outside.L_meta_36260.Model
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
end PEqualNP.Outside.L_meta_36260
namespace PEqualNP.Outside.L_meta_36260
open PEqualNP.Outside.L_meta_36260.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xa0098d0200c29000000000800123a7c0070058027007000c04a8d8e4484006005c004480058f5044d19000d30a56511883c248252a0812430020020800ce141ff43fe43fd43fc43ff42fe42ee42fd42ed42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x248b170f1d0012000e19800000000000270a29228c8022041c8003801929ab159a87182180000d00000005800493891da08010949a068da7ab829c0000241112802a100600000f80001188079b261f189305168ea1200aa39bac2326800009a880001400001e022c9e8116000000002500000000088c17a58095018328001faa8b80c00002010000000040828140008000c1000040c102400040414000c1002dca5a1db54b43bb28e877551d0edca421db54843b6aa4856e5190aeea2a15d14542d7aa285af4350b5a86a179d4542b628a85e45150ac8a2a15b94842bba8a6574514ca7ca8194f55032af29e835d53d06dca5a0db54b41d6a16836f52506d8a4a0eb50941b7290836d521067ca998cf55331b7296636d52cc6dea498db14931b7aa4436d54886dca310cf950219eaa0436f540875ca810db55021d6aa0432d54086dca210f994421f3a0843e441087ce6210f90c421b7296816d52d035a85205794c40aea98816e52102daa4206b50840bb2888175511027ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320bb28c417551883c843885b94a10b6a94213f5444278a88857d4d10ae29a216f52442d8a4887908510
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x24000b94218a9230e09a9862840000000280005a2700810b307800000c008006646154843a95874350b274314542c950c5150b0d5350b41a918542d062d64149318b59654087246155021c955341086c663d04219959441086a664cc421c95533108725540c4219918552d02a46150a40c354d42102a46150840c950951102a564087108b59252842a56408510c915021443445308510
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x42800a600302a98c2a16838155263d042184eecaa66210e05531854210212bb0a810a21815905308510
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 5 => packedAt s2K5 (788+((h/14+packedAt s2K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s2K4 (2670+((h/30+packedAt s2K4 (2430+(h % 30)*8) 8) % 130)*8) 8
  | 3 => packedAt s2K3 (998+((h/8+packedAt s2K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s2K2 (300+((h/2+packedAt s2K2 (294+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffe07fffff03fc1fffffff07fffc8ff1ff
  | 1 => 0xf03f07ff81f87ffc3fe1f0781ff8703f74ce67
  | 3 => 0xffc007fffe007fffc001ff801fff803f870f87
  | 4 => 0x7ffffff83fffffe00001fffffc3f80ff8
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x108200230410000044023088c30091840150ab
  | 1 => 0x258c4a451ca0a92c1d20d4514d4822a934c665
  | 3 => 0x4316d68a28755355c3116d4296d50533870b86
  | 4 => 0xa28a51051441a9aaa54080418a64e02d80d50
  | 5 => 0x8c30c61c618663e333998e6700c40823eea000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeaaaaeeaa8800eeeeaaaaeeaa8800eeeeaaaaeeaa8800eeeeaaaaeeaa8800eeeeaaaaeeaa8800eeeeaaaaeeaa8800eeeeaaaaeeaa8800eeeeaaaaeeaa8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36260
namespace PEqualNP.Outside.L_meta_36260
open PEqualNP.Outside.L_meta_36260.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1200289800ee21ec21ef20ed20f710f510
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x82d2a010f848110
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
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
  | 4 => packedAt s3K4 (102+((h/2+packedAt s3K4 (96+(h % 2)*3) 3) % 8)*4) 4
  | 3 => packedAt s3K3 (56+((h/1+packedAt s3K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x81fffff81ffffc0ff0ff83ffffc1fffd18fe3f
  | 1 => 0xfe07e0ffe07e0ff0ff0ffc1e07fe0f02ef33cc
  | 2 => 0xfff800ffff800fff000fffe007fff0030fc3f0
  | 4 => 0xfffffffffffff0000007fffffff003ff
  | 5 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8c104408c1044401101190aa30c85518085615
  | 1 => 0x14b18511472854b07106948c534a46286b32cc
  | 2 => 0x2862d6a28a1d6d57088b5ac8a5ad64530dc370
  | 4 => 0x714518c414510a6aaaa04201063188e3b001aa
  | 5 => 0x4186108718618b8ccccc6311c0210083d6a800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeaea0000eeeeeaeaeaea0000eeeeeaeaeaea0000eeeeeaeaeaea0000eeeeeaeaeaea0000eeeeeaeaeaea0000eeeeeaeaeaea0000eeeeeaeaeaea0000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36260
namespace PEqualNP.Outside.L_meta_36260
open PEqualNP.Outside.L_meta_36260.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x7e25a210035abc70b8db60000b0a003dd00002d885283922002002003c991866600180205df3b187deb25ee52ac0000e8722c00190021b800000e1500ac0224e4c128000151a52496980f00080090e0c0021e0000904005060a04001b7a92876c5250eeea2a1dd14543bda8287785050eeca221dd54443af29e855d53d0aeca3a15d54742bb28c85755190af4a1215e54242bba8a6574514ca7ca8194f55032bb2886575510caf4a0195e54032bda82837850506bca620d754c41b7a92636c524c67ca818cf55031afa9a435c53486f4a010de54021bba8a817451502bca6205754c40b7290816d52102eca2205d544409f2a6613d54cc2eca3985d54730b7294616d528c2eca3185d546309faa2413c54482bea6905714d20bba8a417451482eca2105d544209faa2213c54442dca4085b54810
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (731+((h/13+packedAt s4K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s4K4 (1875+((h/21+packedAt s4K4 (1728+(h % 21)*7) 7) % 84)*7) 7
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffe03f07f0787ffe0fffff83c07c78fe67
  | 1 => 0xf03f83ffc007ff807c3ff0f80ffc007e4f3387
  | 2 => 0xffc003fffff83fff803fff000fffff838fc3f8
  | 3 => 0x3ffffffffffffc000000ffffffff003ff
  | 5 => 0xfffffc0000003ffffffffffff0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x62851023822890180c464528e5914514185663
  | 1 => 0xa58a56448eb33384361b54b12ad50a5a4b3385
  | 2 => 0x41131889142194a8802c6622431993108dc2a8
  | 3 => 0x8a2c6312288429555a8100848c622c63700156
  | 5 => 0xc30421c30c62e66633188c700403043e6a800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfaeafaeaf800f800faeafaeaf800f800faeafaeaf800f800faeafaeaf800f800faeafaeaf800f800faeafaeaf800f800faeafaeaf800f800faeafaeaf800f800, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36260
namespace PEqualNP.Outside.L_meta_36260
open PEqualNP.Outside.L_meta_36260.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x8437e53086faa610df14c21bf29043ef32087d86410df94421fb98843f431087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c817e52902faa5205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a05f14d40bfa92817c52502fea2a07dd4540bba8a817c51503e8a2a05d14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52103dca4205b94840bea9081ed52102daa4205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c617e528c3dca5185b94a30bea9461ed528c2daa5185f94630fb28c6176518c2faa3187d54630baa8c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220fda0441f840883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc84907b50920f799241ec32482fea2905f14520f790a41ed21483f680907e10120fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21f741843e883085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443ee62887d0c510fb10a21f521443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dd0410fa208217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3217d94642bb28c857d5190beaa3215d54642bf28485fa5090af4a1215f54242fca8485795090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0df14941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa9263ef524c6dea498df14931f6292636c524c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea9063de320c7b86418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fb98e43f431c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ef32887d86510df94621fba0c43f441887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21fba0a43f441487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa9
  | 2 => 0x800000000a1a54228098c987c16a540ee8000001bc0016d0000002e0003a42d88017411e0384ca3b35a4e4142300000000000542a7680009d172000728001c400000000444000e7a6716800000000094000bb0004065b8000980000001c80000000000103000034e613b3e4000410000008346f0004b022c2b0001f068c000002981ac00000000000000c700057c00000000000000db4a6658532560ca0010d8f42045e4868c30a482cfb883000000a124e11a000f70004488dc000002d600000000128220470000c86fc0015b000001228000001cc851a6000000bf8000007800001c000000a2105000174188000001684d20a04641c97a662a81043c0c919049c0022028e0000021000000000000000000000000003fc00000000280000000000000000041e91828800000000898ba3fc668331f843c0f42c23302a69d2686d45a0002184f15a898da03e17c000001d1000420c1a2f2188d403000318000ea24405c88cc30003743b0a51b618a000059cd000000101380dc06914000000614900ef06466cee1ce3623dc4fa5b15000088800000000000000007e4e31d733c72c3c9f50008a807800442000b60fc00025400252278214ca80000043c4e03f35e93c0000000000000035000000b2800098000ec9d3000000ac0a7000491308004ae2780006c0000011c0003784581d1492de0010c98b2f419c00000000000578001840000023c000000002133f6000e81591c00000000000000000000000000750a40000000000038a7f12881223a000000000001d40000011800000000000724c923d0009906b0c043000000172302000000b8000000000000000bc000004824dc0000000000000000000000000000000001a1ec36e000dc0eb0001c86e00028a090b096309000000101056988df0000140000000000000120013000000000003e2000be000000000770000004180006a000000001f40009400000000017c000000000000000000100c014040050060080280000600000002002004000040020000200400002403813002008008000000080000300403c00000002000018040000100400300001000000002008020000000080000001e00c0100300001c0600000000000801010004000020020040080200600005001000000008000000040000200c0340280100e0040280000a02003800002004010000000000000200c00004003002000000010000100280100c00002000000030030000080040580600000000000000008010010000000180000000c0000000200c000010100000380a0000040100001a000010010060040100102a018000040040040000000001401000010000000060020080180d00201409002000004018000080000000100400001000bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x57000000000e1a2e00063c821220009200011b1b089c001980000010e94b0000000007026a0300004000001c85a012d41547687f000548002601c68ac000000008200003b0a6000000001aa0000020500000800004000868b38d426c000f50001e000000000000001248000000006f8e90b2728a09702e2808001c408e0000000042c00000050052000000c100024c000001b4024ad22906e26caa88a33e000f3a47000000001c82d20608b8d23c8700ab8a225a688509d53562f4679df310000000fe0000005800000000000000000600000000002accb921000188000003520000014e0005892e0001660000000035c25c160001e4398001ff146640000000006c07d800428000000001e6000ba8814968d08f8912660012f95e00000000061000000000e4358000f48dd0600e0d0800042000129fd10c000000000002c80000024a4252d2390002fcb40000021109a0001080002b800372000988774b2628d40a52546245618e41298c4001b30e180f307b0bc3e4001f00002407e9bb38e114f791e09a440211234007889305405a7d8000c4176328a30763040cc31a4a006664001bd12c4f903212152000e09eb000544002040003346811c36a0000419102e000000d30005f9070002f63a0110000000005e1280008700024216e000001de0000500025e2f0464e113a3b0000990002cc7a00000000000043800000000000000780007880000032c7d01f22a00066148474000000001120000023f4180012604e3e635cab0d10003380022c000000081e327a000000000000006317329a974001b3224000c680003a0a8002070000001b0000e80008c0000000002d80000012d218000001a0000000fc894001b20004680000000065000000000000000002ee000a7800000000000000008c88713f000000a000034a3d4230002ba2c4ce0490009540012b3c21a4be80042e570000001c2610b20f6000000b01302587e8ed8194621f47399d0006a80b00025c001088000000000000047c0010f8002520000000034854c001ed0000000007a0e22a813800022000d026500036400236000000491d603c000f2
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x553d02766194b409d58652d037051d0140cd14640503586054c40d394e521034d5394840da982521034e5354840d354d52103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103706054440cd546411023f6550040ad185401027b6550040bc185401027661d53309d58754cc2d86050f30b658c40cc26e62d52309b58b548c27661d52309d587548c26e62152309b588548c27661152309d584548c36a6094a30d994a518c3655294630d9949518c36552546309bd89544c26c62551309dd85544c27461551309ed81544c25c6550d309d984524c27561149309dd85540c27461550309798c540c26e62150309b588540c27661150309d584540c2796510030ce550400c25f654c0309ed95300c27661d53209d58754c82776154f209d18553c823e6414f208f59053c82766114f209d58453c82e56190b20ab59032c834d530cb20b958432c82cc63487209dd85548827461552209798c548825d63152209d984548827561152209d987538827561d4e20ce55040882d96310220bc58440882f1618c22097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d20b958642482ea60909209b195424826e65cc920ab59032482e5610c920ba98032482cc63485209e99740482d96310120ba98840482f16110120ba98a30482f1618c1209e195304827661d50209d587540827a60d50209798c540825d63150209b988540827661150209d584540826e62d4c209d987530827561d4c208f990530823d6414c209d98453082756114c209e980530836551c8020dc546200826f6548020d9545200827b6548020dc545200826f6254f109b18953c42f06050710b518d21c42f16110310ec90440c425e63152109758c548426e62152109b588548426e62d4e109b58b538425e63d4a109758f528423e64951109dd85544427b60551108f994544433561151108f992534423d6494d108fd91534423c6454d109bd89534426c6254d108f992524423d64949108fd91524423c645491097d8d524425c63549109d996414433454905109d19541443345450510bc181414427665cc510cd15331442f260cc510cd150314433454885109d19521443345448510b518d214433854881109e19520443385448110f8485204433854c4110cd152104426e62d50109b58b540425e63150109758c540426e62150109b588540427661150109b98b530426d62d4c109d987530423e6414c108f590530426e6214c109b588530426d65948109b988520427661148109e980520427565d0410d954b41042756510410d9548410436952d00109e59440043695210010ec104400436552c40109e596100436952840109dd9510042b46444010d9549100427b6544010ae19110043695244010
  | 1 => 0xb80408000a002260003800040280000000009412100180808030580c120c020b434000700006050000804010d0100240008000205000080400010141611038083c3001860080300000200201038020c9d98652d0e756194b439e98252d0e796094b439b98a5090e6d62942439d9865090e756194243d9d4b5150f6452d4543d9d485150f645214543dad4b5050f6852d4143dcd475050f7051d4143dad485050f685214143dcd445050f7051141438fd954310e5f6550c43ab18943d0b725194242dc5465090b725154242dc5455090a7661141429d5845050a776154c429d1855310a3f65508429bd954210a7761553329d18554cca7b60553329e18154cca7661943329d58650cca7661d52329d587548ca7a60d52329e583548ca7661951329d586544ca6f62551329dd85544ca7461551329ed81544ca786055132d9cc8514cb5632145329d987540ca7561d50329e983540ca7960d50328f596540cb2c62550328f990540ca7661150329d584540ca7a60150329e580540cb2d54d08329b594420cacd631083297d95320cad4614c8329bd95320cae4614c832cd952510cb355494432cd951510cb355454432ce952500cb395494032dc946500cb715194032ce951500cb395454032dc945500cb7151540329e98252d06796094b419b988505066d6214141da98850507696214141dcd04505073a41141419bd89531066c6254c418fd9541106b860504419dd9541106f060504419e98354cc67960d53319b98a50cc66d62943319b98b548c66d62d52319e983548c67960d5231b5584328c66e62951319b58a544c66f62551319b189544c67761551319ed81544c67860551319e980524c6796014931d9584524c76a6014931da580524c76452cc531d314a314c67b60550319e181540c66e62150319b588540c67a60150319e580540c6756510431cd550410c6d5631043197d95310c6cc624c4319dd95310c6e4624c4319e98354c867960d53218f99053c863d6414f219e98053c86796014f219ed8154886786055221b958432887c4328c621b9189318865e63951219758e544865f63551219718d544867b60551219e181544865e6394d219bd8953486776154d219799453487556114d219d997414875453d0521b998b414875453105219d9963148754538c5219d1953148754534c521b9189314875453c8521d314e214867661d50219e983540867960d50219798c540865d63150219e980540867960150219e983530867960d4c218f990530863d6414c219d984530867a6014c219e580530866d650c8219d5973108675650c421f10c8310866f6548421b318d21086776548421b518d210876b3254021da0c950087733154021dc0c5500876b2154021dc88550087692154021dc485500866f6254f409b18953d02776154f409d18
  | 2 => 0x5ab32982a4aea202e09c1c2ecb1af4b8126ba9b2469b6c2108b326ecc0322682480896002f6cb0f60012883abe2a94a0433a589c040014ad8005f8300b046978d20028c2f0580e286b20d8138163708e7f00a2805aa28001024e781ac3e94269000158e47200000146a133600000450609e2e29915ea522eaab141107476852b01e23c066000f277a002a20c72800609100032299876ca8de00304c78009c3002b0007b03e600ee4a8009d2442eaee212ac568f831b2038338b08ca5d1d667aa63a1d8ca0ea4c0c07b80085000000001730e59ae829ad2470040d8007a01c0a2ceac1ce6d00007a6a9e8a24ca408a950000000000030a969a000490004800039a7e6117291ade5313ca887a0ea4a000ec00000141ba7a80000000b70000004200094001be45afeb98d68715600000bf112022920011e0d10c48a620008a86800699c2b5b103507c5ea54000007d80071a3c000005625c0022c00188000925026c00298001dca71c406198bc2123d1a85e0009425a750000006ac08000000033800002ae4b9f2ad1fe2197c8a12cc90da7d28842902af1762b8c884090c70008620464990819189f25600236262b8008623430a27a905500e3123e1300065232c33268e84894b16c4a24618544e10e3f0beb2a080f248bc99cbe13a5a0260898c230b27e970179a2629d26a9ae7c07865a76b910485b1ac6282001b8000003fac40007e0000019000b60b0290b4aca580016e001060a800639347e0000014858222a7800b6a4c829bc0802e0321eaa00006a2653806cba722dad05128e5906c572fab5000129b090800200008c012c1a3438936000cc7407266952793344f882a82801a06e8e1cc68088a696c79824100a800660800800020b050080a000c80026050282814110b00800260200c002d0005c1c04000040000000382e000200c3c050201400301502406130f804160b01020040209030100
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x918050d5c32046003c754100a4823852d340058000c01100010582100623311c56310832cc2c2b00a498d3070550410c662392c6208639114e62d05219c2e13168290e44531893148670b80c498a43d00c83154021a90e690aa010d507348550086b0b90c0a88814c1c55410030a88e2a9865905307155040883182a0c0a0a21385c86050510c60a930662884e172983314430a2a0c690a21c81512148110b80e690a4088721521044004312322a4880218a1915244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2600008400c40535c262d0521c40535c0624c521c20545c86050510c20545ca60cc510d00541cd2148110
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
  | 5 => packedAt s5K5 (18887+((h/205+packedAt s5K5 (16632+(h % 205)*11) 11) % 1082)*11) 11
  | 4 => packedAt s5K4 (16974+((h/138+packedAt s5K4 (15732+(h % 138)*9) 9) % 497)*10) 10
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (304+((h/1+packedAt s5K2 (300+(h % 1)*4) 4) % 13)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf83ffffe03f0fc1e3e3fc3ffffc3c07838fe67
  | 1 => 0x7fc0fe1ffc00ffe03fc7fc3c07fc0079cf3387
  | 2 => 0x7fff001fffff07ffc007ffc007ffff860fc3f8
  | 3 => 0x8000001ffffffffffff8000007fffffff003ff
  | 4 => 0xffffffe0000007fffffffffff8000007fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x98a1482382514060608d15472d14528185663
  | 1 => 0x129628a448e664e01a43551895550a30cb3385
  | 2 => 0x21044cc89144352a40059991219993220dc2a8
  | 3 => 0x628b11122808254ac90000246222c45700156
  | 4 => 0x4430c001c308c3993126222380003007a6a800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaf800feeaf800feeaf800feeaf800feeaf800feeaf800feeaf800feeaf800feeaf800feeaf800feeaf800feeaf800feeaf800feeaf800feeaf800feeaf800, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36260
namespace PEqualNP.Outside.L_meta_36260
open PEqualNP.Outside.L_meta_36260.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001027fd5007fe54027f55007fc54027fd4c09fe53027f54c09fc5301ffd0c01fe43007f50c07fc43027fd4805fe52027f54805fc5201ffd0805fe42007f50805fc42007fcc805fe32007f4c805fc32027fd4409fe51027f54409fc5101ffd0401fe41007f50407fc41007fcc401fe31007f4c401fc31017fc8401fe21007f48405fc21027fd4003fe50027f54003fc5001ffd0003fe40007f50003fc40007fcc003fe30007f4c003fc30017fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24001ff8412000ff42090007fc1048017ffb2e200bbfd971005ffccb88012fe65c4017feb2e200bbf5971005ff8cb88012fc65c4001ffb262000bfd9310057fcc98800efe64c4001feb262000bf59310057f8c98800efc64c4017ffaa6200aff9531005ffaa98802bfc54c4001ffb1e2000bfd8f10007fcc788022fe63c4001feb1e2000bf58f10007f8c788022fc63c4017ffa9e200bff94f1005ffaa78802ffc53c4015ffa1e2000ff90f10007fa878802bfc43c4001ffb162000bfd8b1004ffcc58800afe62c4001feb162000bf58b1004ff8c58800afc62c4017ffa962009ff94b1005ffaa588027fc52c4015ffa162009ff90b10007fa8588027fc42c4001ff9962009ff8cb10007fa6588027fc32c40037f30e200bffd471005ffca38802ff651c4017fea8e200bfd5471005ff8a38802bff41c4001ff20e2000fd90710007fa8388003f541c4015fe20e2000ffcc710007ee6388003fe31c4001fe98e2000ff0c710007e86388027ff21c4001ff10e2000fd88710007fa4388003f521c4013fe10e2001bf5831000ffea188007fe50c4003fea862001ff1431000ffe8188007fe40c4003fea062001ff1031000ffe6188007fe30c4003fe9862001ff0c31000ffe4188007fe20c4003fe9062001ff0831000ffc2188007f610c4003fd0862001ff0431000fe8218801fff654400f7fb2a2000dfd9510004feca8801ffe65440097f32a2007ff5951003dfaca8801ffc65440097e32a2007df19510024f8ca88003ff64440017fb222000efd91100057ec88801bfe64440077f3222000ff59110005fac88801bfc64440077e3222000ef1911001d78c88801fff544400dff2a22007ff55110037f8a888003ff63440017fb1a2000ff98d10045fcc688003fd63440017eb1a2000ff18d10045f8c68801fff534400fff29a2007ff54d1003ff8a68801bff4344001ff21a2000ff50d10037f88688003ff62440017fb122005ff98910015fcc488003fd62440017eb122005ff18910015f8c48801fff524400bff2922007ff5491002ff8a48801bff424400bff2122000ff5091002ff88488003ff324400bff1922000ff4c91002ff86488006ff614400fffa8a2007ff9451003feca28801ffd514400ffaa8a2007ff14510037fe8288003fe4144001fb20a2000ff50510007ea828801bfc4144001ff98a2000fdcc510007fc6288003fd3144001fe18a2000fd0c51002ffe4288003fe2144001fb10a2000ff48510007ea4288017fc21440037fb022001ffd411000ffca088007fd5044003fe2822001ffd011000ffc8088007fd4044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044001fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fd31cc011fe18e6011ffc8730007fc4398003fd21cc023fe10e6001bf5833000ffea198007fe50cc003fea866001ff1433000ffe8198007fe40cc003fea066001ff1033000ffc6198007de30cc003fd1866001ff0c33000fb86198007ff20cc003ff1066001ff0833000ffc2198007fc10cc021ffb2a6010bfd9530087fcca98012fe654c021feb2a6010bf59530087f8ca98012fc654c001ffb226000bfd913007ffcc89800efe644c001feb226000bf5913007ff8c89800efc644c021ffaa2600fff95130087faa89803ffc544c0037fb1a6010ffd4d30047fca698043de534c021fea9a6010f754d30047f8a69803fff434c011ff21a6000f790d30007fa8698003dd434c011fe21a6000ffd8930005fec49803bfe624c0057f3126000ff58930077f8c49800afc624c021ffa92600eff94930087faa49803bfc524c01fffa12600eff90930007fa849803bfc424c011ff992600eff8c930007fa6498023fc324c001ffb0a6000bfd8530007fcc298003fd614c001fe30a6000bf18530087fea298043fe514c021fea8a6010ff1453007ffe8298003fe414c001fea0a600fff10530047fe6298003fe314c001fe98a6008ff0c530077fe4298003fe214c001fe90a600eff0853000dfec098007ff504c003ff2826001ff5413000ff8a098007ff404c003ff2026001ff5013000ff88098007ff304c011fd9826001ff8c13000fbc6098007fc304c003ee1826001fe0c13000ffe4098007fe204c003fd1026001ff0813000ffc2098007fc104c01bffb2a400dbfd952006ffcca90012fe654801bfeb2a400dbf5952006ff8ca90012fc6548001ffb224000bfd9120067fcc89000efe6448001feb224000bf59120067f8c89000efc644801bffaa2400cff9512006ffaa890033fc5448001ffb1a4000bfd8d20007fcc690022fe6348001feb1a4000bf58d20007f8c690022fc634801bffa9a400dff94d2006ffaa690037fc5348019ffa1a4000ff90d20007fa8690033fc43480037fb124002ffd4920017fca49000bee5248005fea92400dfb54920017f8a49000bff4248005ff2124002fb90920017fa8490003ed4248005fe2124002ffcc920007de649000bfe3248005fe9924002ff0c920017d86490003ff61480017fb0a4000ff98520007fac290003fc61480017e30a400dffd452006ffca290037fd514801bfe28a400cffd0520007fc8290003fd4148019fe20a4000ffcc520007fc6290003fd3148001fe18a4002ffc8520017de429000bfe2148005fe90a4000fb48520017f84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001ff9012000ffa8090007fc4048003ff9824001ff8c12000ff46090007fd3048001fc9824001ff0c12000ffe409000bfb2048003ff1024001fb8812000ff84090007ec2048003fc1
  | 2 => 0x21007fc8690803fd434842ffe21a4202bfd8921017fea49080bfe5248405fea924202ff14921017fe849080bfe4248405fea124202ff10921017fe649080bfe3248405fe9924202ff0c921015fec290863ff5148431ff28a4218ff545210c7f8a29085fff4148401ff20a4200ff505210bff88290803ff3148401ff18a4200fd8c521007fa6290803f53148401fe18a4202ffc8521017ee429080bfe2148401f710a4202ff08521017d8429080bf42148401ffb024200bfd81210b7fcc090806fe6048401feb024216ff1812100df8c090863ff504842dff2824218ff541210b7f8a09085fff404842dff2024216ff101210b7fc609085bfc3048405ff9024202fbc8121017fc409080bfc204842dff0824216ff041210affecaa0056ff655002bff32a8004bf995400affacaa0056fd655002bfe32a8004bf1954000dfec8a000fff5450007ff2a28003ef9514001ffaa8a0057bd5450007fe2a28000ffd8d40005fec6a0003fe6350001feb1a8000ff18d40045f8c6a0057ff535002bff29a8015ff54d400aff8a6a000fff4350007ff21a8003ff50d4001ff886a0003ff62500017fb128014ff98940015fcc4a0003fd6250029fe3128002bf189400affea4a0053fe525002bfea928014ff1494001ffe84a000ffe4250007fea128003ff10940007fe64a0053fe3250001fe9928014ff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0002fc615002bffa8a8015ff945400affaa2a0057fc5150007ffa0a8003ff9054001ffa82a000ffc4150001ff98a8000ff8c540007fa62a0003fc3150029ff90a8000ff88540007fa42a0053fc21500037fb028001ffd414000ffca0a0007fd5050003fe2828001ffd014001ff680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff1828001ff0c14000ffe40a0007fe2050003fe1028001ff8414000ff820a0023ff65cc0117fb2e6008ff99730025fccb980237e65cc0093f32e6008ff5973009dfacb980237d65cc0013eb2e6008ff19730045f8cb98023ff64cc0117fb266008ff9933001dfcc998023fd64cc0017eb266008ff19330045f8c99804fff54cc025ff2a66013ff55330097f8a998006fe63cc011ffa9e6008ff94f30047bca798023fd53cc027eea9e6008ff14f30047fe8798023fe43cc011ef21e6008ff50f30007ba8798023fc43cc011ffb166008ff98b30015fcc598023fd62cc0017eb166008ff18b30015f8c59804fff52cc023ff2966013ff54b3008ff8a59804bff42cc023ff2166000ff50b3008ff88598023ff32cc011ff1966008ff4cb30047f86598023ff61cc011ff30e6000bf98730047fac398002fd61cc011fe30e6013ffd473009ffca39804ffd51cc027fe28e6012ffd0730007fc8398003fd41cc025fe20e6008ffcc730047fc639802
  | 3 => 0xfb286208bfd9431047fcca18812fe650c411bf32862049f99431047faca1887efd650c411beb2862009f59431047f8ca18822fc650c411ffb206208bfd9031047fcc81880efe640c411feb206200bf59031047f8c818822fc640c43fffaa0621eff950310fffaa81887bfc540c4117f3186208ffd4c31047fca618823fd530c411fe2986208ffd0c31047fc8618823fd430c411fe2186208ffd8831047fcc41880afe620c411feb106200bf58831047f8c41880afc620c43fffa90621dff948310fffaa418877fc520c43dffa10621dff90831007fa8418877fc420c411ff9906208ff8c8310efbc6418823fd320c411fe1906208f70c831105fcc21887fff510c43fff288621fff544310fff8a21887bff410c401ff2086200ff504310f7f88218823ff310c411ef9886208ff8c431047ec6218823fd310c401ee9886208fd4c4310effe4218877fc210c411ffb006208ff9803100dfcc018823fd600c4017eb006208ff1803100df8c01887fff500c439ff280621fff540310e7f8a01887bff400c439ff200621cff10031047fc6018823fc300c43bff900621cff880310e7f84018873fe100c439fe080621bffd96210ddfecb1086ffe65884097f32c421bff596210ddfacb1086ffc65884097e32c4200ffd9221005fec91086bfe64884077f3244200ff59221005fac91086bfc64884077e324421bffd52210d7fca91086ffd5488435fe2a44200ffd8e21005fec710803fe63884117f31c4200ff58e21005fac710803fc63884117e31c421bffd4e210dffca71086ffd5388437fe29c421affd0e21007fc8710803fd4388435fe21c4202bf58a21017fea51080bfe5288405fea944202ff14a21017fe851080bfe4288405fea144202ff10a21017fe6510803ef3288405ff1944202ff4ca21017f8651080bec32884057f30c421bffd46210dffca31086ffd5188437fe28c421affd0621007fc8310803fd4188435fe20c4200ffcc621007fc6310803f63188401fe98c4200fd4c621007f8631080bff2188405f790c4202fdc8621017f8431080bf42188401ffb044219ff9822100dfcc110803fd60884017eb044219ff1822100df8c11086fff5088433ff284421bff542210cff8a11086bff4088433ff2044219ff102210cffc6110867fc3088405ff9044202ff88221017f84110867fe1088433fe0844218ffd95210c5feca90863fe65484097f32a4218ff595210c5faca90863fc65484097e32a4200ffd9121005fec89085ffe64484077f3224200ff59121005fac89085ffc64484077e3224218ffd51210bffca890863fd544842ffe2a24200ffd8d21005fec690803df63484016fb1a4200ff98d21045fcc690803fd63484017eb1a4200ff18d21045f8c690803dc63484016e31a4218ffd4d210c7fca690863fd5348431fe29a4217ffd0d
  | 4 => 0x80afe62cc411feb166200bf58b31047f8c59880afc62cc457ffa966229ff94b3115ffaa5988a7fc52cc455ffa166229ff90b31007fa85988a7fc42cc411ff9966208ff8cb31047fa6598823fc32cc457ffa8e622bff9473115ffaa3988affc51cc455ffa0e6200ff90731007fa83988abfc41cc453ff90e6229ff08731047fec198823fe60cc4037f3066208ff58331005fac198823fc60cc4037e306622bffd4331147fca1988affd50cc451fe286622affd0331147fc81988a3fc40cc411ff1866208ff0c33114ffe41988a3fe20cc451fe1066228ff84331147f82198883ff658c4417fb2c6220ff99631025fccb18883fd658c4417eb2c6220ff19631025f8cb18803ff648c4017fb246227ff9923101dfcc918803fd648c4017eb246227ff1923101df8c918883ff548c44fff2a46220ff5523113ff8a918892fd638c441ffa9c6208ff94e31107faa718823fc538c44fffa1c6208ff90e31007fa8718823fc438c401ffb146226ff98a31015fcc518803fd628c4017eb146226ff18a31015f8c518883ff528c44dff2946220ff54a31137f8a51889fff428c44dff2146200ff50a31137f88518823ff328c44dff1946226f78ca31007fa6518823fc328c44dee1946208bf98631107fea318883fe518c441fea8c6220ff1463113ffe8318803fe418c401fea0c6227ff10631047fe6318803df318c411fb98c6226ffc8631137f84318803ff608c44bff3046201bf98231007fac118802fd608c44bfe3046201bf18231107fea118897fe508c441fea846225ff1423113ffe8118897fe408c44bfe2046225ff8c231047f8611889bff208c44bff1046225ff0823112ffc2118897fc108c449ffb2a6224bfd9531127fcca98812fe654c449feb2a6224bf59531127f8ca98812fc654c401ffb226200bfd913111ffcc89880efe644c401feb226200bf5913111ff8c89880efc644c449ffaa26223ff95131127faa89888ffc544c449ffa9a6208ff94d31127bca698893fd534c449eea9a6208ff14d3111ffe8698823fe434c401fea1a6208ff10d31007fec498802ff624c401f7b126200bbd8931117fcc49880afe624c401feb126222ff18931015f8c498803ec624c405763126224ffd4931117fca498893fd524c445fe2926223ffd0931117fc8498803fd424c445fe2126208ffcc931117fc6498803fd324c411fe1926224ffd4531127fca298893fd514c449fe28a6223ffd0531007fc8298803fd414c447fe20a6208ffcc531047ee6298803fe314c401ef18a6222ffc8531117f84298803ff604c4017fb026221ff9813100dfcc098803fd604c443fe3026201bf18131127fea098887fe504c449fea826221ff1413111ffe8098887fe404c443fe2026221ff8c131047f8609888bff204c443ff1026221ff0813110ffc2098887fc104c411f
  | 5 => 0x453219ffe82990cffc414c805ff90a6402ff08532007fec099002ff604c865ff3026401bf98132007fac0990cbfc604c8037e3026434ffd4132197fca0990d3fd504c865fe2826433ffd0132197fc80990cbfc404c865ff1826408ff0c132017fe409900bfe204c805fe1026432ff84132197f820990c7ff65904637fb2c8231ff99641025fccb208c7fd65904637eb2c8231ff19641025f8cb2080efd6490407ffaa48203ff9524101f7ca92080ffd5490463deaa48203ff15241007fec720803fe63904117f31c8200ff58e41005fac720803fc6390463ffa9c8231ff94e4118ffaa7208c7fc5390407ffa1c8203ff90e4101ffa872080ffc4390401ffb148230ff98a41015fcc520803fd62904017eb148230ff18a41015f8c5208c7ff5290461ff2948231ff54a41187f8a52080fff4290407ff2148203ff50a4101ff88520803ff3290461ff1948200ff4ca41187f8652080efe6190463ffa8c8231ff9464118ffaa3208c7fc5190407ffa0c8203efd064101fee832080ffc4190407fa20c8230ffc8641187f84320803ff609045fff3048201bf98241007fac120802fd609045ffe3048201bf1824118ffea1208bffe5090463fea84822fff1424101ffe812080ffe409045fdf2048203ff1024101f7881208bffe309045ffe1848230ffc824117ffc41208bffc209045fff084822fff04241177fecaa08baff655045dff32a8204bf99541177facaa08bafd655045dfe32a8204bf1954101dfec8a080fff5450407ff2a28203ff5514101ff8a8a0803ff63504017fb1a8200ff98d41007fac6a0803fc63504117e31a822effd4d41177fca6a08bbfd535045dfe29a8203ffd0d4101ffc86a080ffd4350407fe21a8200ffd8941005fec4a08b7fe62504057f3128200ff5894116ff8c4a080afc625045dffa92822dff94941177faa4a08b7fc5250407ffa128203ff9094101ffa84a080ffc4250401ff992822dff8c941007fa64a08b7fc32504077fb0a822effd4541177fca2a08bbfd515045dfe28a8203ffd054101fee82a080ffe4150401df20a8203ff1054101f7882a080ff4415045bff90a822dff08541007fec0a0802ff6050459ff3028201bf98141007fac0a08b3fc60504037e302822effd4141167fca0a08bbfd5050459fe2828203ffd014101ffc80a080ffc4050459ff182822cff0c14116ffe40a08b3fe2050459fe102822cff84141167f820a0823ff65cc4117fb2e6208ff99731025fccb98823fd65cc4577eb2e6208ff19731045f8cb98823ff64cc4117fb266208ff9933101dfcc998823fd64cc4017eb266208ff19331045f8c9988afff54cc455ff2a6622bff55331157f8a998823ff53cc411ff29e6208f794f31047faa7988afdd53cc411fe29e6208ffd0f31047fc8798823fd43cc411fe21e6208ffd8b31047fcc598
  | 6 => 0x1fe182863bffc81431d7fc40a18ebfc2050c75ff082863aff041431cffecaa10e6ff6550873ff32a8404bf995421cffacaa10e6fd6550873fe32a8404bf19542015fec8a100fff5450807ff2a28403ef9514201ffaa8a10e7bd5450807fe2a28400ffd8d42005fec6a1003fe6350801feb1a8400ff18d42045f8c6a10e7ff5350873ff29a8439ff54d421cff8a6a100fff4350807dfa1a8403ff90d4201ffa86a1003bd4350807fe21a8402bfd8942017fea4a100bfe5250805fea928402ff14942017fe84a100fef4250805ff2128402ef90942017f884a100bbc4250805f62128402ff8c942017f864a1003ff61508017fb0a8400ff98542007fac2a1003fc61508017e30a8439ffd45421cffca2a10e7fd5150873fe28a8403ffd054201ff882a100bff2150805fe10a8400ffd8142005fec0a10e3fe60508037f3028400ff581421c7f8c0a1006fc6050873ffa828438ff941421cffaa0a10e3fc5050807ffa028403ff9014201ff880a10e3fe3050871fe1828402ffc8142017de40a100bfe2050805fe1028438ff841421c7f820a1023ff65cc8117fb2e6408ff99732025fccb99023fd65cc86f7eb2e6408ff19732045f8cb99023ff64cc8117fb266408ff9933201dfcc999023fd64cc8017eb266408ff19332045f8c9990dfff54cc86dff2a66437ff553321b7f8a99900afe63cc811ffa9e6408ff94f32047faa799023fc53cc811ffa1e6408ff90f32047fa8799023fc43cc8057eb166402ffd4b32017fca59900bfd52cc805fe2966402ffd0b32017fc859900bfd42cc805fe2166402ff8cb32017bc659900bee32cc805fe1966402f70cb32047fec399023fe61cc8017f30e6408ff58732005fac399023fc61cc86fffa8e6437ff947321bffaa3990dffc51cc86dffa0e6436ff10732017fe439900bfc21cc805f610e6408ffd8332047fcc199006fe60cc811feb066400bf58332047f8c199006fc60cc86fffa866435ff943321bffaa1990d7fc50cc86dffa066435ff903321aff88199023fe30cc811fe1866402ffc8332017de419900bfe20cc805fe1066435ff843321aff821990d3ff654c8697fb2a6434ff99532025fcca990d3fd654c8697eb2a6434ff19532025f8ca99003ff644c8017fb226433ff9913201dfcc899003fd644c8017eb226433ff1913201df8c8990d3ff544c867ff2a26434ff5513219ff8a89900aff634c869ffa9a6408ff94d321a7faa699023fc534c867ffa1a6408ff90d32007fa8699023fc434c8057fb126402ffd4932017fca49900bfd524c805fe2926402ffd0932017fc849900bfd424c805fe2126402ffcc932047de649900bfe324c805ef1926402ff0c932017b8649900bec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6400bf185321a7fea2990d3fe514c869fea8a6434ff1
  | 7 => 0x10028130000000a0000060000004f006028008070380080100901e0240280000a03c00010008070090090020000180204c0040180000200400803000008000000fe0b4000070020fc0980300a0280480106a0040200b02a030000110420000000e0ac0180000002800009005000004070030080000e80400200000800006030100060060000083d0000c803800000004000010000000000400000000801004010000180000380c00500800c0003c0580000002b00a02006803014000000010460000001105c0240000200203c1a82100c01c0080c02a00002811050008108020000500200800c09c0082600c0000880002201400805024010018030200000080000a00c018050180b00000300600c00819002008008030000200080b018000000290020140c010000008010010300340080600a088080090020080583f02c00c0000201002401800000014028010540b40001900606c0680601601401023ff6590c117fb2c8608ff99643025fccb21823fd6590c7f7eb2c8608ff19643045f8cb2180efd6490c07ffaa48603ff9524301ffaa92180ffc5490c117f31c8608ffd4e43047fca721823fd5390c11fe29c8608ffd0e430477e872180fdf4390c11fe21c8608f710e43047fec521823fe6290c057f3148608ff58a43005fac521823fc6290c057e314863fffd4a431f7fca5218fffd5290c7dfe2948603ffd0a4301ffc852180ffc4290c11ff1948608ff0ca43047fec321823fe6190c017f30c8608ff58643005fac321823fc6190c7fffa8c863fff946431fffaa3218fffc5190c07ffa0c8603ff106431f7fe43218fbfc2190c11ffb048608ff9824300dfcc121823fd6090c017eb048608ff1824300df8c1218ffff5090c7bff284863fff542431eff8a12180fff4090c07ff2048603ff10243047fc6121823fc3090c7dff904863dff882431eff841218f7fe1090c7bfe084863cffd95431e5fecaa18f3fe6550c097f32a863cff595431e5facaa18f3fc6550c097e32a8608bfd914301ffea8a180ffe5450c07feaa28603ff1514301dfec6a18f3ff5350c11ff29a863cff54d43047f8a6a180fff4350c07efa1a8608ff90d430477c86a1823fc4350c11de21a8603f710d43007fec4a1802ff6250c77ff3128602bf98943007fac4a18effc6250c057e312863cffd49431dffca4a18f3fd5250c77fe2928603ffd094301f7e84a180ffe4250c07fe212863bff8c943047f864a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c017e30a863cffd45431e7fca2a18f3fd5150c79fe28a8603ffd054301ff882a18efff2150c77fe10a8600ffd8143005fec0a18ebfe6050c037f3028600ff581431d7f8c0a1806fc6050c79ffa82863aff941431e7faa0a18ebfc5050c07ffa028603ff9014301ff880a18ebfe3050c1
  | 8 => 0xbda378fc1029cf14b8002dfac2a7aa1000021e2270eb154a77a02a3833d8001490621feaaf12528490901e8dda35a8097eb33918a009fa80032d0dc248a5c9f02de236109a6608817b25d9aca58a4786620c91d2ab1e39e2a2799d25a0081598b7a0a2549df01a8ed2570b00000e88ac2ad8000ab1c980016b13787ba232f28b29df9ce9771501799cc0eb80016d8d40448712d19b69c4abd04aa61b2e8db00f2022c605188b9453442640360438001e41c50a31e4ab3a2ea3f030b1a1dc00023a80008a04eacb80000018c2f711029916126b83d30f1b99f223fb3987513b07a196918220817ae0a780d70450619e2024000203ace2ad00000009286a2dc2fd80020f07e07d00000019812d24d8c131700018622f80000030680032a00023692d8b180024200f922a6280028b2aa94b1628c3a982370719e98cf34f1a0a851ff2df01f2a514984d01191286d92a30b9fc98a850b152dd8e71b28e513eac827ea67b3eb1b158a472a792593c21185d01c8759bb00006c30da910f280008c800006a4d0a4884308313b4580000000e0000738878ff1759dd2113330000001470002592653260281d922b89ba0f80006b0000e99b180000034809cb2e28c80013127c2579eb2a933180016a80018190186e1238002e6b3b12aa52a261372a11d180994f97800024a2cd9262919a48001938908769e109785f8000ab80032c87f0dd126a09b1e2702e78be9e18f48000de2e2883a389d58002220d61329209cd8f934d00013aabfae900030080023900000019a94a00030233f2cc271a018b71fb0358742da0002dd01b11b19897e2428d31d531896e0ff96c8018010060300000200a01c000010120140c8000000001502e0000080580100000c00813000100008000000080400c04c0ac008030060000380100a0ec0000a000018000000020180b83b002000018000400000000200c000000020020300f01300208001010000020008020000040000001a05402800002074008080240100080600e000000050040001280200c0300200000000c070070040040700000000400046006008028000180041180000200c0e0040060000982800a014088000000240080002203c10027008038098040320000083701a01c010000000a4018010540000000300000c0100a01602c0002000000c01000012008010090000100305e01005000800008048058190000f8070000000040100a0040100180000013c0100f04801817002010040000000020040e803012018000030180a8078050000380000b0000bc008050000000281800206c0f0020060440b80c0160040082a02c0080102e01e0500000f0020440204905c050078010060080280002a154030000000000600005a0000081300205c0180600000c070000020980300f0020480000704a088008000000200
  | 9 => 0x1109d69a4000121abe27b000096a8ea9a80000000018f23b0002d6a758d531e80009a84693c8000a40000002ea000078000169283abc0e1802b4a1ec00a82f9508fc8002bb0000000c18000000899d4b3b80000032580000015d344b208000001718000000002ca25f0bc8003470000000002801b21b5990800000000328a9604f133ad10000ad8cc8000691c78e0a7287f8ee0f685b82ea480f30000000af2920ef256b2ba0902d2211cc8950071580000c0000000170b118652db8470003300ceaf52fc91412b08880009e0ba2971b10000000001838002948000a51a29c305684915615329e8003308033010ac97a892000298800000000016b34b1b82893917d00028d0be2f62f42ac1a7a249d00540d20388d89163108002ee83e2ecaee2620a89f70180002f30000458000823250000cd2b90000000002840000001641a50d903811eaf992bb1f208b342952f015f8fb06f2c42510003220e80598600002418000b480014295d9f8205994964a7e33d1a89199f62d318681601f8410f9a4b20300002c80025faa71ae058836913278800000297b0299b176999089188190026000023a000b88001b83053098d01b380000000000000006d000000141b478c400015595c8df85294d28891f27480014a8e79762ea98ead42b0b0a09729c823000000000180b3889013600017f0ec2c3a16af59c000033a00025a9e80c98039ec90d00b15780baae8bb16f8001ba00004c0000f41a5ae70000002c20001138ae8af80000000008da66a4e9ed0000000003428002e48001528e20000002f380012f1fc1340550000da01c00000000000000017da31074a9b1de8c60870a78001ef90880027d8000002f087b0cbb16ac1134b2a9721a9b142d298d2de9280002d3a8128800c9ac19c1f114699134931f88498fa6e1af85e8042e3848acd04a1f08a384000001500029e2cfb22ab9a790000ca9f50000001c203789f1fbad920d01b9b7a769290a82202518d11e52d603aa798bd3120f10bb9c2ae033f9cb83db322d88678f5aacab48002648b68ea80000020100008f94095e82680023ea0615a00014618b1e58000000000000408558398000999f78310c505a8ed8680c333c81880025b2a225207c2ba21f1de1828000002349ca80023523080007dac934891108e0a094d9ff804ad5912135a671d817b8002898a922aa65a610000a18000c7a5d08aa2db040001db1430b0b0e29588d0001930e6af21793031959e3072022b24204282afb87a85c9289998949a10418011f898224519bac303b8639bc2170a601007611499704bb2011f8db8961a1a12a751748001e71223199c099e0c22c88fa800000282100219af689a00000005780033921a207824afd03f02b8a2a49a17ad018e3359c1000316290a23af929d187ab10463401ef15924692e0f02
  | 10 => 0x8d980a2c58251eb9f49e7a81938a229ce20800202c250a43a601b012eb2c0142298001159059a71ee0210e629f0da8dea2d21b9da864b4e9aa83ea5e96a0c915418502aa4e14c1330e12b61179550001ea23c00015b0079961d0b019a800016ea739400a596d174000225136af180000e969b36b128320000d28001650000000000002ed20c0000b30002cb17100033280004e13198d9050bd992259967000346800000151a070e4b3a91c1aea3d9dc8f8992adb0ef80516007016822a22f30a8cb1f42a580004fb0f9b316600030e9c80002fa2153059be8e02770b23110000001a391a0000c81f6930000086296b268792ce8f215baa40672eb2a19aa2b88ca1f9ab41270c08131bd213895ad234ca4f0c48aa24c9f184d81a30c93b80c06886400d1539ed99c9fa11c97017c89ea6b13510e92310da6085a34381705b2afae12258000219060a228e2b71d105dada94f1e88d389c20a93e09b1449a313a13f80dafe0000348059382eb88b22e2b5a938000000b610398014231c0e2907a890b9ab18aab101dba8f8f792481915ab21ae51a903c0333280b58341ad90ab3c323842a0526820da8a92faff2930c687ca2c212285b408fd1d991a99f2872f12160159bf820a3ba301ddab29bb84325821a80021d82e1c91f5a3d34b80031d00002580021b0538001b7057000253b4d9d38003179570001d400029a000072ac1aa000027b8e5800000141214862ae99be0e32c7831989ac00b1286abaabf20b9210ee8b914cb3e00009d16c1080000002c510208580007700012780018c8003419a017390fa6e8000001888000668002faa7324f80004c8000000000000000002b50000c585300022180000000027a1009af000000104aa28fd9398002e88e90000000001d7afe8000000002713290b38002721f28002409d7184af48121abb1583005e098aef172af81cd14e8930731f92d81cb26a2cc994245977a3e2560501a632fa1c1a20851c1a3a2a8a5c2c4a1d3038fa2abac09c8acf2180001c5a8f16692c00015129428600003ca8da6d21f819a328000dc967a2800002f00006aa7f8612dc88eae1a6fa332543000000a10a6a3ca7d21313d3180000c71bcaa311d80000022889f86e8478328818e41872762e216b8339440000cf80010b233ae411690f1569d2800082b4a9d31fd00010a2ec0d82342d792c83a165800111ab202d89829f8293430c281d268abe8002b00bc2631da2d734526c24a839063080aa68002e58000000001031ca11e1ab2bc86c963a1e88f17326918122ca8328a05c0001c6a4106bb27afc2f88000000b81478919b60f70139b48001a68002900a72441f319785617f8bf27caefaaa28c33800180000000024b8000000522b32460ad19a2bba400109d6000077b0906fac69b900029c33702003718424903f95e05f00
  | 11 => 0x3410b50000002188499622ae239a6f00019527402a2c9b1309d8ea17526a9eeab685125301480026d8698d6aa08fba69945917307a1925bb4c16082b34b1d89e6124346106b230ec8d49b888c1fd81d99fa2b2a80cdb2f065ac732b09910c299a708ba9b4349991943a63a558f39c72e8178b270a02878941c62f79e6ad9a500d1b062b81688270cc21c9482e61d22430128440001f38f80bf87ea06b4e32d854a268ce29d886a0eb0c0f18d79ea8110788f62ff879b298938088000f51baa5e18b8001200810df2d50000ae24c1522241cf97a3191b0ae313da14027a1097c1bd95f30b14e1e913f27f16f00607096331493210cb420590d5b1a9831858e3b2130d03b29291bb1c80006090e1c384b15c0482fb304a318000092321b528b8000001e00009299fe13081e000215b088580001618000a98d09190001e09040222a99bf0000001150000b41488002ca80032480019eb362552a3aa610b80026c80030719d8800351ad1c420b31dad4ab78910420f0b3520480033118a1010298fe0000832eda0e2d0aa4a9bb37a291891072448fe8c8
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x8704c51010ff0104c51012cfe760c51003d7e750c5100057d750c5100067f650c5100fe7c650c510006bf640c5100f6bc640c51012df6760c510216f6760c510215f7750c51021776750c51025df5750c51021775750c51000575750c51000777650c51025774650c510215f7740c510005f5740c510007b7640c510007b4640c510145f6730c510217d6730c510216f7630c510216f5630c510005f5720c51024fd6320c510217d4320c51000df6700c51000df4700c5100e6f7600c5100e7f2200c510244fe76885100067f65885100de7c6588510006bf64885100d6bc648851000df870885100cff01088510245f6768851023ef67688510235f77588510235f5758851000777658851022f746588510005f77488510005f57488510007b76488510007b46488510215f67388510215f47388510006f76388510006f563885100b5f57288510016f66288510016f46288510007e7328851002fe43288510007f3708851000df6708851000df470885100cff070885100cef760885100cff22088510014ff764851000cfe76485100b4fd764851000cfc76485100067f65485100c67c6548510006bf64485100bebc6448510005df7348510005dc7348510006ef6248510016ec624851002fe42148510005fb704851000df870485100b7f0104851000df47648510016f4764851000cf47648510225f77548510225f5754851000777654851021f746548510005f77448510005f57448510007b76448510007b46448510007d77348510215f67348510215f47348510007d47348510005d47348510006f76348510006f563485100cdf77248510007e77248510007e76248510016f66248510016f4624851002fe46248510007f3704851000df6704851000df470485100b7f070485100b6f760485100b7e720485100b7f220485100b7e5204851002df87648110016f87648110014f876481100077b654811020f786548110007bb6448110007b86448110006fb6348110006f9634811000dfb724811000feb7248110007eb6248110016fa6248110016f8624811002fe8624811002fea524811020fe9524811002fea4248110007e94248110007eb324811002fe83248110007f37148110005f87148110007f0714811000efb614811000ff3614811020ff2514811020ff15148110007f24148110007f14148110007f33148110007f0314811002feb214811002ff22148110007e9214811002ff12148110007e1214811000dfa76c411000efa76c411000cfa76c41100077b65c41102077865c4110007bb64c4110007b864c4110005fb72c4110005f972c411000dfa71c411000ff271c411000efb61c411000ff361c4110207f251c4110207f151c4110007f241c4110007f141c4110007f331c4110007f031c4110007f221c4110007f121c4110
  | 1 => 0x89102a5f77158910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910044fc7358910006dc7358910044dc73589100ccff7258910006ef72589102a4ff7158910006f771589100b4ff7058910006fb7058910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101ce7c6550910006bf645091001ebc6450910044ff76cc910004fe76cc910004fd76cc910044fc76cc9100067f65cc9101be7c65cc910006bf64cc9101b6bc64cc910006ef62cc910016ec62cc910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101a67c654c910006bf644c91019ebc644c910005f7714c910005f4714c91029cfe76905100067f659051018e7c659051017ebf649051001ebc649051029df67690510296f6769051028df7759051028df57590510007776590510287746590510165f5749051017fb7649051001ef6649051001ef46490510037b4649051001eb46490510037b65490510287b55490510215f67390510005f5729051000df6709051000df4709051017ef7609051017fb6409051017fb4409051017ff2209051001cff765051000cfe7650510164fd765051000cfc76505100067f65505101767c6550510006bf645051001ebc6450510005fb705051000df8705051000df4765051001ef4765051000cf4765051027df7755051027df5755051000777655051027774655051017df77450510007b77450510007b7645051001ef6645051001ef46450510037b4645051001eb46450510215f47350510005f77250510007f3705051000df6705051000df47050510167f07050510166f76050510167f2205051000cfe76cc51000cfc76cc5100067f65cc51015e7c65cc510006bf64cc510156bc64cc510006df63cc510046dc63cc51000dfa70cc510005f970cc51000df676cc510146f676cc51000cf676cc510215f775cc51026df575cc5100077765cc5102677465cc510215f774cc510005f574cc510007b764cc510007b464cc510216f763cc510007d763cc510216f563cc510217d463cc510217d653cc510267d553cc510005f572cc51000df670cc510147f270cc51000df270cc510217f170cc51000df470cc510146f760cc510147f220cc5100e4fe768c5100067f658c5101067c658c510006bf648c51013ebc648c5100e5f6718c51012ff0108c510044ff764c51000cfe764c51010cfd764c51000cfc764c5100067f654c5101267c654c510006bf644c51011ebc644c510006df634c510046dc634c510005ef724c51002dec724c510005fb704c51000df
  | 2 => 0x4ff7359110044fc7359110004ff7259110014fe7259110014fc72591102acff7159110006f77159110164ff7059110006fb705911017dbe7619110036be761911017cbe7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6219110006bc621911029fb5711911029ebf6119110007b65119110007b5511911029ebf601911029fba201911029fb6101911029fb4101911029fb81019110044fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10004ff75d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10014fe72d8d10004fd72d8d10014fc72d8d10006de32d8d10006dc32d8d10044fe71d8d1012ef571d8d10044fc71d8d1012cff70d8d1000cfe70d8d1012cfd70d8d1000cfc70d8d1012edf30d8d1012edd30d8d1012efa20d8d1003d7e7598d100057d7598d100067f6598d100067c6598d10035be7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d1010df57198d100057f7558d1003d7c7558d100067f6558d100067c6558d10005bf7458d10035bc7458d10006bf6458d10006bc6458d10005ef7258d1002dec7258d10145f77158d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d1001cfc7458d10006bc7458d1001cbc7458d10006df7358d10006de5358d10006dd5358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d10144ff7158d10006f77158d1010cff7058d10006fb7058d1010efa2058d1012cfe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10046de6318d10006dd6318d10044ff7690d10004fe7690d10004fd7690d10044fc7690d100067f6590d101fe7c6590d10006bf6490d1001ebc6490d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d101e67c6550d10006bf6450d1001ebc6450d10005f77150d10005f47150d10014fe76d89100067f65d89100067c65d8910006bf64d8910006bc64d891002eee62d8910004ff75d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d8910044fe73d8910004fd73d891002eec32d8910014fe71d891000cfd71d8910014fc71d891002eef21d89100ccff70d891000cfe70d89100ccfd70d891000cfc70d89100ceef20d89100ceed20d89100057f755891003d7c75589100067f65589100067c6558910005bf7458910035bc7458910006bf6458910006bc6458910005df7358910005dc735891002eec625
  | 3 => 0xc62d95102b77771d95102b77471d95102b77a20d95102b77610d95102b77410d95102b77810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067c42d95100067e32d95100067c32d95102b67f71d951003e7e71d95102b67d71d95102b67c71d95100067f41d95100067c41d95100067f21d95100067c21d95102b67f70d95102b67e70d95102b67d70d95102b67c70d95102b67f40d95102b67e40d95102b67d40d95102b67c40d95102b67f30d95102b67e30d95102b67d30d95102b67c30d95102b67f20d95102b67e20d95102b67d20d95102b67c20d95102b67f10d95102b67e10d95102b67d10d95102b67c10d951001cfe76d91100067f65d91100067c65d9110036be64d9110004ff75d9110024fe75d9110004fd75d9110024fc75d9110006bf54d9110036be54d9110006bd54d9110036bc54d9110044fe73d9110004fd73d9110036bf43d9110036bc43d9110014fe72d9110004fd72d9110014fc72d9110036bf42d9110006be42d9110036bc42d911001cfe71d911000cfd71d911001cfc71d9110036bf41d911017cff70d911000cfe70d911017cfd70d911000cfc70d911017ebf40d911017ebd40d911029dbe76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be62d9110006bc62d911017fb771d9110007b651d9110007b551d911017fba20d911017fb610d911017fb410d911017fb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006be32d9110006bc32d911017ebf71d9110036be71d911017ebd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf21d9110006bc21d911017ebf70d911017ebe70d911017ebd70d911017ebc70d911017ebf50d911017ebe50d911017ebd50d911017ebc50d911017ebf30d911017ebe30d911017ebd30d911017ebc30d911017ebf20d911017ebe20d911017ebd20d911017ebc20d911017ebf10d911017ebe10d911017ebc10d91100057f755911003d7c75591100067f65591100067c6559110036bc64591102adf77159110004ff75591100067f75591100047f7559110024fe7559110004fd7559110024fc75591100067c75591100247c755911017cff7459110006bf7459110
  | 4 => 0x8b10004ff7650b10004fe7650b10004fd7650b10004fc7650b10044ff76ccb10004fe76ccb10004fd76ccb10044fc76ccb10006ef62ccb10016ec62ccb10004ff764cb10004fe764cb10004fd764cb10004fc764cb10005f7714cb10005f4714cb1000cff769071001cfe769071000cfd769071001ebe6490710006bd649071000dfa7090710005f9709071000df5769071001ef5769071000cf5769071031df7759071031df5759071001ef66490710057b66490710007b5649071001ef46490710057b65490710317b554907102c5f67390710005f5729071000df6709071017ff27090710007f1709071000df4709071017fb6409071017fb440907102acff76507102adf7765071030ef77650710305f77550710305f57550710007b7745071001ef6645071001ef464507102c5f47350710005f7725071000df6705071000df4705071010cfd76cc71010df576cc7102c6f576cc7102c5f775cc7102fdf575cc7102c5f774cc710005f574cc7102c6f763cc7102c6f563cc7102c7d653cc7102f7d553cc710005f572cc71000df670cc71000df470cc71000cff768c71000cfd768c710046de638c710006dd638c71000dfa708c710005f9708c710144ff764c710005ef724c71004dec724c71000cff760c71000cfd760c710044fc760c71005d7e750c7100057d750c710046de630c710006dd630c71000dfa700c710005f9700c71000df5760c7100e6f5760c71000cf5760c7102c5f7750c7102c776750c7102edf5750c7102c775750c71000575750c7102c5f7740c710005f5740c7102c7d6730c7102c6f7630c7102c7d6630c7102c6f5630c710007d5630c710005f5720c7102e7d6320c7102c7d4320c71000df6700c7100e7f2700c7102c7f1700c71000df4700c71000cff7688710014fe768871000cfd7688710016ee6288710006ed628871000dfa7088710005f9708871000df57688710016f5768871000cf576887102ddf775887102ddf57588710005f77488710005f574887102c5f673887102c5f47388710006f76388710006f56388710016f6628871004fe66288710007e56288710016f46288710007e7328871004fe4328871000df670887100cff27088710007f1708871000df470887102a4ff7648710005df7348710005dc7348710006ef6248710016ec624871004fe421487102a5f776487102d6f776487102cdf775487102cdf57548710005f77448710005f57448710007d773487102c5f673487102c5f47348710007d47348710005d47348710006f76348710006f56348710007e77248710007e76248710016f66248710016f4624871004fe4624871000df6704871000df470487100b7e720487100b7e520487102bd7e76d951003e7e76d95100247e76d95100067e64d95100067c64d95100067e62d95100067
  | 5 => 0x7e76148520006ec6148520007e46148520007e63148520007e53148520007eb704852000dee704852000dec70485200b7e87048520016ef6048520017eb60485200b7ea30485200b7ea1048520015f8764c120046f8764c120014f8764c12000dfb734c12000fdb734c120007db634c120046fa634c120046f8634c120007d8634c12032fda534c12032fd9534c120007da434c120007d9434c120007eb724c120015fa724c120015f8724c120077e8724c12000efb624c12000feb624c120077ea524c12032fe9524c120077ea424c120007e9424c120327eb324c120077e8324c120005fb714c120077eb214c120007e9214c120056be64d931029df671d9310004ff75d9310024fe75d9310004fd75d9310024fc75d9310164fd74d9310056be54d9310006bd54d9310044fe73d9310004fd73d9310014fe72d9310004fd72d9310014fc72d931029cfe71d9310006f671d9310006f970d931017ebe40d931017ebc40d931001cff7659310056bc6459310004ff7559310024fe7559310004fd7559310024fc7559310006bf7459310004ff7359310044fc7359310004ff7259310014fe7259310014fc725931001cff715931001cfd715931000cfc7159310056bc4159310166bf4059310166bd40593100e5f671d8f10004ff75d8f10024fe75d8f10004fd75d8f10024fc75d8f1001cfe74d8f10004fd74d8f1001cfc74d8f10014fe72d8f10004fd72d8f10014fc72d8f100e4fe71d8f10006f671d8f10006f970d8f1010cfd7698f10006df6398f10044ff7658f10005ef7258f1004dec7258f10004ff7558f10024fe7558f10004fd7558f10024fc7558f10004ff7458f1001cfe7458f1001cfc7458f10006df7358f10006de5358f10006dd5358f10004ff7258f10006ef7258f10004ef7258f10014fe7258f10014fc7258f10006ec7258f10014ec7258f10044ff7158f10044fd7158f1010ef47158f1010edf3058f1010edd3058f1005d7e7518f100057d7518f10046de6318f10006dd6318f1012df67118f10044ff7690f10004fe7690f10004fd7690f10044fc7690f10004ff7650f10004fe7650f10004fd7650f10004fc7650f10005f77150f10005f47150f1004eee62d8b10245f671d8b10004ff75d8b10024fe75d8b10004fd75d8b10024fc75d8b1001cfe74d8b10004fd74d8b1001cfc74d8b10044fe73d8b10004fd73d8b100b4fd72d8b1004eec32d8b10244fe71d8b10006f671d8b1004eef21d8b10006f970d8b100cefa10d8b10014ff7658b1004eec6258b10004ff7558b10024fe7558b10004fd7558b10024fc7558b10004ff7458b1001cfe7458b1001cfc7458b10004ff7358b10044fc7358b10006ef7258b10014ff7158b10014fd7158b1000cfc7158b1004eec2158b100b6ef2058b100b6ed2058b100b6fa105
  | 6 => 0xf7690d20004fe7690d20004fd7690d20044fc7690d20015ec7290d2000dfa7090d20005f97090d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20005ef7250d20015ec7250d2000dec765092001eec765092000cec765092034def755092034ded7550920015ef7450920017af7450920007af645092001eee645092001eec6450920067ac6450920067ae5450920347ad5450920325ec7350920067af4350920007ad4350920005ef7150920007eb705092000dee705092000dec70509201c7e87050920016ef6050920017eb60509201c7ea30509201c7ea105092000dee76cc9201aeee76cc92000cee76cc920325ef75cc92033ded75cc920325ef74cc920005ed74cc920015ee73cc920017ce73cc920326ef63cc920007cf63cc920326ed63cc920327cc63cc920005ed71cc92000dee70cc9201afea70cc920327e970cc92000dec70cc920016ef60cc920017eb60cc9201afea30cc9201afea10cc920004ff75d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d8520044fe73d8520004fd73d852000cfd72d8520006f741d8520006f441d852023ef621d852023ef521d8520014fd70d85202a6f710d8520006f7619852002df970985200057f755852006d7c7558520005bf7458520065bc7458520005df7358520005dc735852004dfb7058520006f56118520004ff7518520024fe7518520004fd7518520024fc751852001cfe7418520004fd741852001cfc7418520044fe7318520004fd731852000cfd7218520246ed7218520006ef32185202d6ec3218520006f74118520006f441185202d6ef21185202d6f621185202d6f5211852000cfe7018520014fd70185202d6f9701852000cfc7018520246fa1018520246f51018520004fe7690520004fd7690520004fc7690520006bf649052001ebc6490520015ee7290520005ed729052000dfa7090520005f97090520004ff7650520004fe7650520004fc7650520015ee7250520004fe76cc520004fd76cc520044fc76cc520015ec72cc52000dfa70cc520005f970cc520004fe768c520004fd768c520004fc768c520006df638c520046dc638c520015ee728c520005ed728c520137cc328c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c520005ef724c520015ec724c52000dfa704c520004fe760c520004fd760c520044fc760c52006d7e750c5200057d750c520006df630c520046dc630c520015ee720c520005ed720c5200efcc320c52000dfa700c520005f9700c52000dec76485200b6ec764852000cec7648520335ef7548520335ed7548520005ef7448520005ed7448520007cf7348520325ee7348520325ec7348520007cc7348520005cc7348520015ef7148520017e77148520
  | 7 => 0x8530006dd53d8530014fe72d8530004fd72d8530014fc72d8530044fd70d8530146fa20d8530146f710d8530006f761985300057f75585300857c7558530005bf745853007dbc7458530005ef7258530075ec7258530006f56118530004ff7518530024fe7518530004fd7518530024fc751853001cfe7418530004fd741853001cfc7418530014fe7218530004fd7218530014fc7218530044fd70185300e6f51018530004fe7690530004fd7690530004fc7690530006bf649053001ebc6490530004ff7650530004fe7650530004fc765053000cfe768c530006f7618c530006f4618c53000dfa708c530005f9708c53000cfc764c530005ef724c530075ec724c530006f7614c530006f4614c530005fb704c53000df8704c530004fe7688530004fd7688530004fc7688530006ef6288530016ec6288530004ff7648530004fe7648530004fc7648530005df7348530045dc734853001cfe76d9120066be64d9120004ff75d9120024fe75d9120004fd75d9120024fc75d91201c4fd74d9120044fe73d9120004fd73d912000cff72d9120014fe72d912000cfd72d9120014fc72d912037ebf42d912037ebd42d9120004fe71d9120004fd71d9120066bc41d9120014ff70d9120014fd70d912036ebf40d912036ebd40d912001cff76591200057f755912006d7c7559120066bc6459120005df7359120005dc7359120365ef7259120005f77159120005f47159120375fb7059120004ff75591200067f75591200047f7559120024fe7559120004fd7559120024fc75591200067c75591200247c755912036cff7459120006bf7459120066be5459120006bd5459120004ff7359120006df7359120004df7359120044fc7359120006dc7359120044dc7359120364ff7259120006ef7259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f471591201c4ff7059120006fb7059120044fe76d8d20004ff75d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20006de53d8d20006dd53d8d20006df43d8d20006dc43d8d2000cff72d8d20014fe72d8d2000cfd72d8d20356ed72d8d20014fc72d8d2035edf32d8d2035edd32d8d2035eec32d8d20004fe71d8d20004fd71d8d20014ff70d8d20014fd70d8d20356df30d8d20356dd30d8d20194fd7698d2006d7e7598d200057d7598d20006df6398d20195ed7298d20075f97098d20044ff7658d201adef7258d2008dfb7058d20004ff7558d20024fe7558d20004fd7558d20024fc7558d20004ff7458d2001cfe7458d2001cfc7458d20006df7358d201acff7258d20006ef7258d20076ec3258d20004ff7158d20004fc7158d20194ff7058d20006fb7058d20354fe7618d20046de6318d20006dd6318d20044f
  | 8 => 0x1cfe7498730004fd749873001cfc749873000cfe7398730014fe7298730004fd7298730014fc7298730046f67198730006f74198730006f44198730046f73198730046f4319873012ef51098730004ff7558730024fe7558730004fd7558730024fc7558730004ff745873001cfe745873001cfc745873000cfc7358730046de5358730006dd5358730004ff7258730014fe7258730014fc7258730046f77158730006f74158730006f44158730046f73158730046f4315873010ef71058730004ff7690730044fe7690730004fd769073018e7e65907300067d659073001ebe6490730006bd6490730004ff7650730004fd7650730044fc76507301767e65507300067d6550730004ff7688730044fe7688730004fd76887300de7e65887300067d6588730006f66188730006f56188730004ff7648730004fd7648730044fc76487300c67e65487300067d6548730005df7348730045dc7348730006f66148730006f5614873001cfe76d913007ebe64d9130004ff75d9130024fe75d9130004fd75d9130024fc75d9130044fe73d913000cfd73d9130044fc73d913007ebf43d9130014fe72d9130004fd72d9130014fc72d9130004fe71d9130004fd71d913007ebc41d9130044ff70d9130044fd70d91301eebf40d91301eebd40d913007ebc645913039ddf7359130004ff7559130024fe7559130004fd7559130024fc75591301ecff7459130006bf745913039cff7359130006df7359130004ff7259130014fe7259130014fc7259130004ff7159130004fc71591301d4ff7059130006fb7059130395de7690d30046de7690d30045df7590d3038ddd7590d301d5dd7490d3001ede6490d3001edc6490d3000dde7090d3000ddc7090d30046df6090d30047db6090d301efda2090d3001cff7650d3000cfe7650d301d4fd7650d3000cfc7650d30006bf6450d3001ebc6450d30005fb7050d3000df87050d3000ddc7650d3001edc7650d3000cdc7650d30385df7550d30385dd7550d30045df7450d300479f7450d300079f6450d3001ede6450d3001edc6450d3007f9c6450d3007f9f4250d30007db7050d3000dde7050d3000ddc7050d301d7d87050d30046df6050d30047db6050d301d7da2050d30014fe76d8930076ee62d8930004ff75d8930024fe75d8930004fd75d8930024fc75d893001cfe74d8930004fd74d893001cfc74d893000cfd73d8930014fc73d8930076ee32d8930004fe71d8930004fd71d8930076ec21d8930044fd70d89301aeef20d8930076ec6258930004ff7650930004fe7650930004fc76509300079d435093000cfc764c930006ef624c930016ec624c930005fb704c93000df8704c930004ff75d8530024fe75d8530004fd75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d8530006de53d
  | 9 => 0xf7518540024fe7518540004fd7518540024fc751854000cfd741854030ebe5418540006bd5418540044fe7318540004fd7318540014fe7218540004fd7218540014fc7218540006f75118540006f4511854030ef6411854030ef54118540006f72118540006f4211854001cfd701854029ebe401854029ebc401854029ef51018540004fe76cc540004fd76cc540044fc76cc540004fe768c540004fd768c540004fc768c540006f7618c540006f4618c540004ff764c540004fe764c540004fc764c540005ef724c5400a5ec724c540006f7614c540006f4614c540004fe760c540004fd760c540044fc760c5400ad7e750c5400057d750c54001dbe740c540005bd740c54000dfa700c540005f9700c540004fe7688540004fd7688540004fc7688540004ff7648540004fe7648540004fc7648540005df7348540005dc73485400067f74597300067e74597300067d74597300067c74597300467f73597300467e73597300467d73597300467c73597300467f43597300467e43597300467d43597300467c43597300067f72597300067e72597300067d72597300067c72597300067f42597300067e42597300067c42597300467f32597300467e32597300467d32597300467c32597300067f71597300067e71597300067d71597300067c71597300067f41597300067c41597300467f31597300467e31597300467d31597300467c31597300067f21597300067c21597303b67f70597303b67e70597303b67d70597303b67c70597303b67f40597303b67e40597303b67d40597303b67c40597300467f30597300467e30597300467d30597300467c30597303b67f20597303b67e20597303b67d20597303b67c20597303b67f10597303b67e10597303b67d10597303b67c1059730004ff7559330024fe7559330004fd7559330024fc7559330046bf7459330044ff735933000cfe7359330044fd735933000cfc7359330046be4359330046bc4359330004ff7259330014fe7259330014fc7259330096bf4259330004ff7159330004fc7159330096bc41593301d6bf40593301d6bd4059330045df7650f303aedf7650f303a5df7550f303a5dd7550f300475e6550f300475d6550f300479f7450f3001ede6450f30046dc6450f300979f4250f3000dde7050f3000ddc7050f30004ff7558b30024fe7558b30004fd7558b30024fc7558b30004ff7458b3001cfe7458b3001cfc7458b3000cfe7358b30014fd7358b3000cfc7358b30046ef7258b30046ef3258b30046ec3258b30004ff7158b30004fc7158b30046fa3058b30046f93058b30196ef2058b30004ff7650b30004fd7650b30044fc7650b301ce7e6550b300067d6550b3001ebe6450b30006bd6450b300079d4350b30004ff7598730024fe7598730004fd7598730024fc7598730
  | 10 => 0xc521046dc638c5210edf6768c521006f6768c521115f5738c521137d7638c521046f6638c521046f4638c521007d4638c521046d4638c521015f6728c521015f4728c521136f7628c521137d6328c521137d4328c521005f5708c521137e7208c521044ff764c521014fe764c521114fd764c521014fc764c521006df634c521046dc634c521005ef724c521015ec724c521015f4764c521046f4764c521014f4764c521007d7734c521007d7634c521046f6634c521046f4634c521007d4634c521046d4634c5213dfd6534c5213dfd5534c521007e7724c521015f6724c521015f4724c521117e4724c521015e4724c521116f7624c521005f7704c521117e7204c521134fe760c5210c57e750c5210057d750c521006df630c521046dc630c521135f6710c5210efe4210c521007cf63885213d6ee63885213d6ec6388521007cc6388521006cc6388521015ee7188521017e67188521016ef6188521017e76188521007e63188521007e53188521005ed708852100cfe76d8121006df63d8121006dc63d81210b6fa60d8121004ff75d8121024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d8121044fe73d8121004fd73d812100cfc72d8121014fd71d81210b6fa20d81210b6fa10d81210057f75581210c57c7558121005bf74581210bdbc7458121005df7358121005dc7358121006df6358121006dc63581210b6f86058121044fe76d8d40004ff75d8d40024fe75d8d40004fd75d8d40024fc75d8d4000cfd74d8d403cede43d8d403cedd43d8d40014fe72d8d40004fd72d8d40014fc72d8d40006de32d8d40006dc32d8d40004fe71d8d40004fd71d8d4001cfd70d8d4039edf30d8d400ad7e7598d400057d7598d40006df6398d40005f67198d40005f57198d4007df97098d40095fb7058d40046de6318d40006dd6318d40014fe76d89400a6ee62d8940004ff75d8940024fe75d8940004fd75d8940024fc75d894000cfd74d8940014fc74d89403c6be54d8940006bd54d8940044fe73d8940004fd73d89400a6ee42d89403c6ed42d8940004fe71d8940004fd71d894001cfd70d8940366ef20d89400057f75589400ad7c7558940005df7358940005dc73589400a6ec6258940005f77158940005f471589403bdfb7058940004fe76cc940004fd76cc940044fc76cc940004ff764c940004fe764c940004fc764c940004ff75d8540024fe75d8540004fd75d8540024fc75d854000cfd74d8540044fe73d8540004fd73d8540014fe72d8540004fd72d8540014fc72d8540006f751d8540006f451d8540296f641d8540296f541d8540006f721d8540006f421d854001cfd70d85402aef710d8540006f76198540035f970985400057f75585400ad7c7558540055fb7058540006f56118540004f
  | 11 => 0x136de42d8d21136dd42d8d21136dc42d8d21136df71d8d21136dd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d21006df41d8d21006dc41d8d21136df21d8d21136de21d8d21136dc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dc40d8d21136df20d8d21136de20d8d21136dd20d8d21136dc20d8d21006de10d8d21006dc10d8d21006df6398d21115f57198d2114df77158d21004ff7558d21024fe7558d21004fd7558d21024fc7558d21004ff7458d2101cfe7458d2101cfc7458d21006df7358d21114ff7258d21006ef7258d21004ef7258d2114cff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21134fe7618d210c57e7518d210057d7518d21046de6318d21006dd6318d21135de7618d21006de7618d21134de7618d210075e7518d210075d7518d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d21006de6418d21006dd6418d21006dc6418d210efd57118d210efd72118d210efcc2118d210efd42118d21006de6018d21006dc6018d210efcf2018d21046df7518d21046de7518d210465e7518d21046dd7518d210465d7518d21046dc7518d21046df7418d21046de7418d21046dd7418d21046dc7418d21006df5418d21006de5418d21006dd5418d21006dc5418d21046df7218d21046de7218d21046dd7218d21046dc7218d210eedf5218d210eede5218d210eedd5218d210eedc5218d210eedf4218d210eede4218d210eedd4218d210eedc4218d21046df7118d21046dd7118d21046d57118d21006df5118d21006de5118d21006dd5118d21006dc5118d21006df4118d21006dc4118d210eedf2118d210eede2118d210eedd2118d210eedc2118d210eecc2118d21046df7018d21046de7018d21046dd7018d21046dc7018d21006df5018d21006de5018d21006dd5018d21006dc5018d21006df4018d21006de4018d21006dc4018d210eedf2018d210eecf2018d210eede2018d210eedd2018d210eedc2018d21006de1018d21006dc1018d21044ff7690d21004fe7690d21004fd7690d21044fc7690d21006df6390d21046dc6390d21005f67190d21005f57190d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006df6350d21046dc6350d213e4fe7690521006df6390521006dc6390521187e4219052101cff7650521014fe765052116cfd7650521014fc7650521006bf645052101ebc6450521006df6350521006dc6350521005ef7250521015ec725052116fe42150521014fe76cc521014fc76cc521006df63cc521046dc63cc521015ee72cc521005ed72cc52114fe421cc5210ecfe768c521136df638
  | 12 => 0xd728c621137cc328c621015f5768c621046f5768c621014f5768c621046f6638c621007d6638c621007d5638c621046f4638c621015f6728c621137e6728c621007e5728c621015f4728c6213d7e7328c621137d6328c621137d4328c621137e4328c621137c4328c621005f5708c62114cff764c621005ef724c621015ec724c62114df7764c621006f7764c621007d7734c621046f6634c621046f4634c6213f7d6534c6213f7d5534c621007e7724c621015f6724c621015f4724c621117e4724c621015e4724c6213d7e7324c621117e4324c621005f7704c621014ff760c621014fd760c621044fc760c6210dd7e750c6210057d750c621046de630c621006dd630c621015ee720c621005ed720c6210efcc320c6210cefa60d822100cff76582210cef86058221004ff7558221024fe7558221004fd7558221024fc7558221004ff745822101cfe745822101cfc7458221004ff7358221044fc7358221006ef325822102eec3258221014fc715822102eef21582210cefa20582210cef8105822101cfe76d91210bebe64d9121004ff75d9121024fe75d9121004fd75d9121024fc75d91210bebe54d9121006bd54d9121044fe73d9121004fd73d9121184ff72d9121184fd72d9121186bf42d9121186bd42d9121014fd71d91210bebf41d912100cfe70d9121004fd70d912100cfc70d9121006be40d91210bebc40d9121186ef20d91210bebc6459121005df7359121005dc73591213edf77159121004ff7559121024fe7559121004fd7559121024fc7559121184ff7459121006bf7459121004ff7359121006df7359121004df7359121044fc7359121006dc7359121044dc735912116cff7259121006ef72591213ecff7159121006f77159121004ff705912100cfe705912100cfc705912116eef2059121044fe76d8d21004ff75d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d21006df53d8d21006de53d8d21006dd53d8d21006dc53d8d21006df43d8d21006dc43d8d21134ff72d8d21134fd72d8d21136df32d8d21136dd32d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d21044de76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d21137d771d8d21137d721d8d21137cc21d8d21137d421d8d21006de60d8d21006dc60d8d21137cf20d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d21136df72d8d21136de72d8d21136dd72d8d21136dc72d8d21136df52d8d21136de52d8d21136dd52d8d21136dc52d8d21136df42d8d21
  | 13 => 0x831005f4715083113cff7690431044fe769043101cfd7690431044fc769043118e7e65904310067d659043101ebe6490431006bd6490431045de7390431005dd739043113cff76504311767e65504310067d6550431045df764c431006df764c431004df764c431046df654c4310475e654c431406dd654c4310475d654c4310065d654c431007cf724c4310edde724c4310eddc724c431007cc724c4310edcc724c431045df714c431047d7714c43140ede614c431047d6614c431407d6514c431407d5514c431007d6414c431007d5414c4313ffd7214c4313ffd4214c431004ff7558031024fe7558031004fd7558031024fc7558031004ff745803101cfe745803101cfc745803100cfd7358031004ff7258031014fe7258031014fc7258031046fb70580310e6fa4058031046fb3058031046f830580310e6fa20580310e6f810580310d6be64d92213e5f671d9221004ff75d9221024fe75d9221004fd75d9221024fc75d922116cfd74d92210d6be54d9221006bd54d9221044fe73d9221004fd73d9221006ed72d92213e4fe71d9221006f671d922100cfe70d9221004fd70d922100cfc70d922101cff76592210d6bc6459221004ff7559221024fe7559221004fd7559221024fc7559221006bf7459221004ff7359221044fc735922116ebf425922116ebd4259221014fc71592210d6bc4159221004ff705922100cfe705922100cfc7059221137cc32d8e210edf671d8e21004ff75d8e21024fe75d8e21004fd75d8e21024fc75d8e2101cfe74d8e21004fd74d8e2101cfc74d8e21006ed72d8e21136de32d8e21136dc32d8e21136ec32d8e210ecfe71d8e21006f671d8e2100cfe70d8e21004fd70d8e2100cfc70d8e21114fd7698e21006df6398e21044ff7658e21004ff7558e21024fe7558e21004fd7558e21024fc7558e21004ff7458e2101cfe7458e2101cfc7458e21006df7358e21006de5358e21006dd5358e21006ef7258e21116df3258e21116dd3258e21116ec3258e21004ff7058e2100cfe7058e2100cfc7058e210dd7e7518e210057d7518e21046de6318e21006dd6318e210efcc3218e21135f67118e21044ff7690e21004fe7690e21004fd7690e21044fc7690e21005f67190e21005f57190e21004ff7650e21004fe7650e21004fd7650e21004fc7650e21005ef7250e21015ec7250e213d6ed76cca21015ee73cca21017ce73cca213d6ef63cca213d7ce63cca213d6ed63cca21007cd63cca213d7e671cca21005ed71cca213d7e571cca21016ee61cca21017e661cca21014ff769062101cfe7690621014fd769062101ebe6490621006bd6490621015ee7290621005ed72906213ecff7650621114fd76cc621015ec72cc621014ff768c621014fd768c621046de638c621006dd638c621015ee728c621005e
  | 14 => 0x4fc7650931006ef6250931016ec6250931014fc764c931006ef624c931016ec624c931005f7714c931005f4714c931154fe7690531006ef6290531186ec629053101cff765053111cfd7650531044fc7650531006bf645053101ebc6450531005df7350531045dc7350531006ef625053116eec625053111fb44150531006ef628c531136ec628c531045f6718c531046f7618c53140ddf758c53140ddd758c531007cf628c531136de628c531136dc628c531007cc628c531136cc628c531045de718c531046df618c531047d7618c53100cfe76d8131006ef62d8131006ec62d813110efa60d8131004ff75d8131024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d813100cfc73d8131006de53d8131006dd53d8131014fe72d8131004fd72d8131014fc72d8131044fd71d81312c6f731d81312c6f431d813110efa30d813110efa10d81310057f75581311257c7558131005bf745813111dbc7458131005ef7258131115ec7258131006ef6258131006ec625813110ef860581310067f74594310067e74594310067d74594310067c74594310467f73594310467e73594310467d73594310467c73594310467f43594310467e43594310467d43594310467c43594310067f72594310067e72594310067d72594310067c72594310067f42594310067e42594310067c42594310467f32594310467e32594310065e32594310467d32594310467c32594310465c32594310fe7f71594310067e71594310fe7d71594310fe7c71594310067f41594310067c41594310467f31594310465f31594310467e31594310467d31594310467c31594310067f21594310067c21594310067f70594310067e70594310067d70594310067c70594310067f40594310067e40594310067c40594310467f30594310467e30594310467d30594310467c30594310067f20594310067e20594310067c20594310067e10594310067c1059431004ff7559031024fe7559031004fd7559031024fc7559031046bf7459031044fe7359031044fc7359031046be4359031046bc4359031004ff7259031014fe7259031014fc72590310f6bf42590310f4fc71590310f6bc4159031004ff705903100cfe705903100cfc70590310f6bf4059031004ff7558831024fe7558831004fd7558831024fc7558831004ff745883101cfe745883101cfc7458831046ef72588310eeee4258831046ef32588310eede3258831046dc3258831046ec3258831046f63158831046f531588310eeec2158831004ff705883100cfe705883100cfc70588310eeef2058831004ff7650831004fd7650831044fc76508311ce7e65508310067d655083101ebe6450831006bd6450831005df7350831045dc7350831016ee6250831006ed6250831005f7715
  | 15 => 0xc7158231216f73158231216f4315823112efa305823112efa205823112ef8105823101cfe76d913111ebe64d9131004ff75d9131024fe75d9131004fd75d9131024fc75d913111ebe54d9131006bd54d913111cfd73d913111ebf43d9131014fe72d9131004fd72d9131014fc72d9131044fd71d913111ebf41d913100cfe70d9131004fd70d913100cfc70d9131006be40d913111ebc40d913111ebc6459131005ef7259131115ec7259131004ff7559131024fe7559131004fd7559131024fc755913111cff7459131006bf745913113cff7359131006df7359131004ff7259131006ef7259131004ef7259131014fe7259131014fc7259131006ec7259131014ec7259131154ff7159131006f77159131004ff705913100cfe705913100cfc705913101cfc7650d31006bf6450d3101ebc6450d310479c4350d311deec6250d31005f77150d31005f47150d31047d43150d31014fe76d8931116ee62d8931004ff75d8931024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d8931006ef52d8931116ee52d8931006ed52d8931116ec52d8931006ef42d8931116ee42d8931116ec42d8931116ee32d8931044fd71d8931116ef21d893100cfe70d8931004fd70d893100cfc70d8931116ef20d8931006ee20d8931116ec20d8931115ee76d8931014ee76d8931006ef65d8931006ee65d8931006ed65d8931006ec65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d8931007ce53d8931007cd53d89313d7e771d89313d7e731d89313d7e431d8931006ee60d8931006ec60d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d8931006ee54d8931006ed54d8931006ec54d8931006ef73d8931116ee73d8931006ef53d89313d6ee53d8931006ed53d89313d6ec53d8931006ef43d89313d6ee43d8931006ed43d89313d6ec43d89313d6ef71d8931116ee71d8931006ed71d8931006ef51d8931006ee51d8931006ed51d8931006ec51d8931006ef41d8931006ec41d89313d6ef31d89313d6ec31d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef50d8931006ee50d8931006ed50d8931006ec50d8931006ef40d8931006ee40d8931006ec40d89313d6ef30d8931006ee30d89313d6ec30d8931006ee10d8931006ec10d8931116ec6258931005ee7618931116ee7618931006ef6518931006ee6518931006ed6518931006ec6518931006ef6418931006ee6418931006ed6418931006ec6418931007ce5318931007cd5318931117e5711893114eef6118931417e73118931417e43118931117ea7018931117e97018931006ee6018931006ec6018931004ff7650931004fe7650931
  | 16 => 0x9331004fd7559331024fc7559331046bf7459331156be5459331006bd5459331044fc7359331046be4359331046bc4359331004ff7259331014fe7259331014fc7259331156bf4259331156bf4159331004ff705933100cfe705933100cfc7059331006be4059331156bc4059331004ff7558b31024fe7558b31004fd7558b31024fc7558b31004ff7458b3101cfe7458b3101cfc7458b31046ef7258b31046ef3258b31046ec3258b31046f63158b31046f53158b3114eef2158b31004ff7058b3100cfe7058b3100cfc7058b31004ff7650b31004fd7650b31044fc7650b3101ebe6450b31006bd6450b31005f77150b31005f47150b3111cfd769073101cff7650731044fc765073101ebe6450731006bd6450731005df7350731045dc7350731004ff7558331024fe7558331004fd7558331024fc7558331004ff745833101cfe745833101cfc7458331046de5358331006dd5358331004ff7258331014fe7258331014fc7258331046fb7058331046fb3058331046f83058331146fa2058331146fa105833113ebe64d9231004ff75d9231024fe75d9231004fd75d9231024fc75d923113cfd74d9231006dd73d9231014fe72d9231004fd72d9231014fc72d9231006f671d923100cfe70d9231004fd70d923100cfc70d923101cff765923113ebc6459231004ff7559231024fe7559231004fd7559231024fc7559231006bf745923113ebf4359231004ff7259231014fe7259231014fc7259231044fc715923113ebc4159231004ff705923100cfe705923100cfc705923101cff7650e3101ebe6450e31006bd6450e31005f77150e31005f47150e31136ee62d8a31137cc32d8a31014ff7658a31045dc7358a31136ec6258a31137ce3258a31004ff7558a31024fe7558a31004fd7558a31024fc7558a31004ff7458a3101cfe7458a3101cfc7458a31136de3258a31136ee3258a31136dc3258a31044fc7158a31136ec2158a31004ff7058a3100cfe7058a3100cfc7058a31136ef2058a31004ff7650a31004fd7650a31004fc7650a31005df7350a31045dc7350a31014ff764ca31135df734ca31016ee624ca31006ed624ca31047cc324ca31005f7714ca31005f4714ca3101cfe7690631044fd769063101ebe6490631006bd6490631045de7390631005dd73906310f4ff765063113fb44150631005dd76cc631046dd76cc63141edf65cc63141edd65cc631135de72cc631045dc72cc631047d661cc63141fd651cc63141fd551cc63112efa60d823100cff76582310057f75582311057c755823112ef86058231004ff75582310067f75582310047f7558231024fe7558231004fd7558231024fc75582310067c75582310247c7558231004ff745823101cfe745823101cfc7458231004ff7258231014fe7258231014fc7258231044f
  | 17 => 0xcfe7018532004fd701853200cfc701853200cfe76d8132196fa60d8132004ff75d8132024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d8132014fd73d8132044fd72d813243eef32d813208eec32d8132004fe71d8132004fd71d8132196fa30d8132196fa20d8132196f860581320f5f671d8e41006df6398e41004ff7558e41024fe7558e41004fd7558e41024fc7558e41006de5358e41006dd5358e4111ede4358e4111edd4358e41004ff7258e41014fe7258e41014fc7258e41004ff7058e4100cfe7058e4100cfc7058e4118d7e7518e410057d7518e41046de6318e41006dd6318e4113df67118e41186ee62d8a41435f671d8a41014ff7658a41186ec6258a41004ff7558a41024fe7558a41004fd7558a41024fc7558a410bebe5458a41006bd5458a41004ff7358a41044fc7358a41186ee4258a410beed4258a4101cfc7158a41186ec2158a41004ff7058a4100cfe7058a4100cfc7058a41186ef2058a41044ff76cca41004fe76cca41004fd76cca41004ff764ca41004fd764ca41004fc764ca4117efa60d824100cff765824101dbc745824117ef8605824117fba4058241004ff7558241024fe7558241004fd7558241024fc7558241036be5458241006bd5458241004ff7358241044fc7358241004ff7258241014fe7258241014fc725824101cfc715824117ebe405824117efa405824117ebc405824117efa205824117ef81058241004ff75d8d41024fe75d8d41004fd75d8d41024fc75d8d4113ede43d8d4113edd43d8d41014fe72d8d41004fd72d8d41014fc72d8d41006de32d8d41006dc32d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006df6398d4111df57198d41005ef7258d4116dec7258d41155f77158d411757e7518d410057d7518d41046de6318d41006dd6318d41014fe76d894116eee62d8941004ff75d8941024fe75d8941004fd75d8941024fc75d8941044fe73d8941004fd73d894116eee42d89410d6ed42d894116eec32d894101cfd71d894116eef21d894100cfe70d8941004fd70d894100cfc70d8941005df7358941005dc735894116eec625894142df77158941004fe76cc941004fd76cc941044fc76cc941006ef62cc941016ec62cc941004ff764c941004fe764c941004fc764c941426bf6590541426bd659054101dbe719054101fb6719054101ebf619054101fb7619054117ebe609054117ebc609054100cfe76d8141166fa60d8141004ff75d8141024fe75d8141004fd75d8141024fc75d814100cfc74d8141044fe73d8141004fd73d8141014fe72d8141004fd72d8141014fc72d814101cfd71d8141006fb50d8141166f850d8141166fa40d8141166fa10d81410057f75581411757c7558141166f86058141004ff7559331024fe755
  | 18 => 0xf75d8142024fe75d8142004fd75d8142024fc75d8142014fd74d81423bebe54d8142006bd54d8142044fe73d8142004fd73d814201cfd72d8142004fe71d8142004fd71d81421c6fa40d81421c6fa20d81420057f75581421cd7c7558142005df7358142005dc7358142005f77158142005f471581421c6f86058142004ff7559332024fe7559332004fd7559332024fc7559332046bf7459332014fe7359332014fc7359332046be4359332046bc43593321debf42593321debd4259332004ff7159332004fc7159332004ff705933200cfe705933200cfc70593321deef2059332004ff7598732024fe7598732004fd7598732024fc759873201cfe7498732004fd749873201cfc7498732014fe7398732136de3298732046dc3298732046f67198732046f73198732046f43198732136f5219873200cfe7098732004fd709873200cfc7098732004ff7558732024fe7558732004fd7558732024fc7558732004ff745873201cfe745873201cfc7458732014fc7358732046f77158732046f73158732046f43158732116f62158732116ec2158732004ff705873200cfe705873200cfc7058732116ef2058732004ff7558332024fe7558332004fd7558332024fc7558332004ff745833201cfe745833201cfc7458332014fe7358332014fc7358332004ff7158332004fc7158332046fb7058332046fb3058332046f830583321aefa205833201cfe76d913219ebe64d9132004ff75d9132024fe75d9132004fd75d9132024fc75d9132014fd73d913219ebf43d9132044ff72d9132044fd72d91321f6bf42d91321f6bd42d9132004fe71d9132004fd71d913200cfe70d9132004fd70d913200cfc70d913219ebc6459132445df7359132005f77159132005f47159132004ff7559132024fe7559132004fd7559132024fc75591321f4ff7459132006bf7459132444ff7359132006df73591321dcff7259132006ef7259132004ff7159132006f77159132004f77159132004fc7159132006f47159132004f47159132004ff705913200cfe705913200cfc705913201cff7650d32014fe7650d321dcfd7650d32014fc7650d32006bf6450d3201ebc6450d32005ef7250d32015ec7250d32047cc3250d32004ff75d8532024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d8532044fd72d8532006f751d8532006f451d8532006f741d8532006f441d853214ef621d853200cfe70d8532004fd70d853200cfc70d8532006f76198532006f56118532004ff7518532024fe7518532004fd7518532024fc751853201cfe7418532004fd741853201cfc7418532044fd7218532416ef32185320eede32185320eedc32185320eeec3218532006f75118532006f45118532006f74118532006f441185320eef52118532
  | 19 => 0x8243046fb70582431eefa4058243046fb3058243046f830582431eefa2058243014fe76d89431deee62d8943004ff75d8943024fe75d8943004fd75d8943024fc75d8943044fd74d894301cfd73d8943006ef52d89431deec52d89431deee42d89431deee32d8943004fe71d8943004fd71d89431deec21d894300cfe70d8943004fd70d894300cfc70d89431deef20d89431deec6258943005f77158943005f47158943004ff75d8543024fe75d8543004fd75d8543024fc75d8543044fd74d8543014fe72d8543004fd72d8543014fc72d8543006f751d8543006f451d8543156f641d8543006f721d8543006f421d854300cfe70d8543004fd70d854300cfc70d8543006f76198543005ef72585431ddec7258543006f56118543004ff7518543024fe7518543004fd7518543024fc7518543044fd7418543014fe7218543004fd7218543014fc7218543006f75118543006f451185430f6f54118543006f72118543006f4211854300cfe7018543004fd701854300cfc701854300cfe76d81431d6fa60d8143004ff75d8143024fe75d8143004fd75d8143024fc75d8143044fd74d814301cfd73d8143014fe72d8143004fd72d8143014fc72d8143004fe71d8143004fd71d8143006fb50d81431d6f850d81431d6fa40d81431d6fa30d81431d6f86058143044fe76d8d42004ff75d8d42024fe75d8d42004fd75d8d42024fc75d8d42014fd74d8d42006de53d8d42006dd53d8d42456de43d8d42456dd43d8d4201cfd72d8d42446df32d8d42004fe71d8d42004fd71d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006de30d8d42006dc30d8d42006df6398d4219ded7298d421b5ef7258d42005f77158d42005f47158d421cd7e7518d420057d7518d42046de6318d42006dd6318d42015bc7650d42046bc7650d42014bc7650d4244dbf7550d4244dbd7550d4201dbf7350d4201f9f7350d420079f6350d42046be6350d42046bc6350d420079c6350d42007af7250d42015be7250d42015bc7250d421dfac7250d4201ebf6250d4201faf6250d421dfaf2050d42004ff75d8542024fe75d8542004fd75d8542024fc75d8542014fd74d8542044fe73d8542004fd73d854201cfd72d8542006f651d8542006f551d854242ef641d85423eef621d854200cfe70d8542004fd70d854200cfc70d85423eeef20d8542006f610d8542006f410d8542006f76198542005df7358542005dc7358542006f56118542004ff7518542024fe7518542004fd7518542024fc7518542014fd7418542436be5418542006bd5418542044fe7318542004fd731854201cfd7218542006f65118542006f55118542436f541185423e6f5211854200cfe7018542004fd701854200cfc7018542006f61018542006f4101854200cfe76d81421c6fa60d8142004f
  | 20 => 0x8004000000000800400400200080000020040010000008001003000000000000000100180010000000000000000000c00c000000800c000002000000000c0000000000004001002800000600200000080020000020004008000000000c00200000280000000010018004002001000800800e001000000400800d00080000000020008008002001003000000600200100000020050008008000009000000800000000000040000010058008000000001000400a00000200040040000010020002000001000400c0010048000006000000800c00c0030000008012004000000400000b001000400000400080000000040010010012001000000400000100000200060030038000006004000800000200000000040000000000004002003000800000000700000000000100000004002000000800400600100000080000000018000000007002000000800000080000000010010000006000001800c00800000000080040010010000000000001801c000001000800800a0070010000002004001000c0000000020000036000006800000a00000000040000020018000004002000000800e000000002400400300280100020000020000000001000000c000000000000000400000000000060000010010004001000000800200300600080000000038028006000000001c0000000008000000004002801c00000700200040060000000004004000000000c006001000800400a001002001400600200000000020000008000002002004000c00800300000000040000008004000000000000800000000100000000000000018006002000000c00000300180000000020000008006000000000400600300080040000020010004000000004ff7558a43024fe7558a43004fd7558a43024fc7558a43044fe7358a43044fc7358a43046bf4358a43046bd4358a43046ef7258a431f6ee4258a43046ef3258a43046ec3258a43004ff7158a43004fc7158a43004ff7058a4300cfe7058a4300cfc7058a43004ff7598643024fe7598643004fd7598643024fc7598643044fe7398643014fe7298643004fd7298643014fc7298643046f67198643006f65198643006f5519864313ef54198643046f73198643046f4319864300cfe7098643004fd709864300cfc7098643006f61098643006f41098643004ff7558643024fe7558643004fd7558643024fc7558643044fc7358643004ff7258643014fe7258643014fc7258643046f77158643006f65158643006f5515864311ef64158643046f73158643046f43158643004ff705864300cfe705864300cfc7058643006f61058643006f41058643004ff7558243024fe7558243004fd7558243024fc7558243044fe7358243044fc7358243004ff7258243014fe7258243014fc7258243004ff7158243004fc715
  | 21 => 0x8004000002000801c00000d000800400000000000000000010058000006001001800000600600000140040000010008000008003806001a0010000014004000000801001000200280040000000010010002000000002401200100000000000040008004002002000000000200000100280000000000000000000000800000000000280000000000010000000005000000400000000080000040090000000000001002000c00000600000000040020000000004005001801c0000010018008002000000000c0000010040000004000001800c002006003001400000400080000040050000000000001001000000400000080000000020000024002000000000000e0000010004010008000000400c0000000008000005000001c00000100000000040030020000000001000000800600200200000000000008008002003001000c0060030000000004000001800000e004002800c0000010078004002000001000000000200280040000000020004000003001000c00600100180140060010000000000000001000000600200200000040020018004002000000800400c001000800000000200000000000010000000006001003000800c001000800000000400080000040000020000004000004001c004001000800c02c009000000c0000010010000008000000000800000300000040020010018004002000000000400000300000200060000038000002002001801400200000080080000000000000006001000000400000a0008008000000000000800000000000000020020000000002000000000400000000100000020010000004000000000000400000500180000020050008000000000000800c00800400200100020000008000000000000800400000300200100060050000014002000000000400c0020010010002001001000400600100000000000080010000000003000800400600400600040020010000000000000000000000000100400000020010000000000000002000000400300000000040000028000004000000800000400300400080060000000000002003000800400e000000000c0020000000008002005000000000a000000000c002008000000000200100380040160040050004006000000800400200a0008004000000000003400a00800000180080020008000004001000000000200200100100000030000008000001002800400400b0018000006003007800c00e000001801c0000020018004000003000000c004000000800c000000006000c0020030000038002001000000400000000200000000010000000000000001001001a00000000000040010000008002000000800000000600000040000010020000006000000800800000600400080040010008000000000001800000000100000080060000
  | 22 => 0x47800000030a98daa440be0000000000000263cdae00000000003f000000000000000d44ef8000000cda03a131909e0004308c980000001ad93f80006dc5c98cf50183211fe0001a4ec650000b4803c0000002a107fcbc900fb0b8000415000000000000000000000001014af0000000af20ad289102205f18f04ec0000000c6000073c990120015c7fe01c0000001a800003c833a40008cd000000000083b4cb219c00012f00000002201e76242b4400049d68298e0304bd560a07980004281960b404a61b10000000000ab401180013845024938e44000000000160400094e0000000000000000060d410c8f55580011b083507590001844115f2ae6400046900021e54fe024000000000000000012258e80000002c054d800000011a99cc5d200034b8000000000000000000000010780000000000000000000074ab1000000000000000000000001cf94e600000000000000000002e30000d36013a400e109834662a9c10a2aa00000002a014e33700008969ff000000000000058c31e0000c3703f297597e0510000001056c4200000000003bf00000000004d43d3011000038930c800000000059400011ea000210183595cbed00026d8e666be26500000000000001c856149cf59780011d200023d932167a00007a8000000ce50003130eb652355700013c625b0000000df800000000000624bd29a00010887140000000000a4f0000a40000000000000000000010c9830cea000000000000000000035ecf2a50c00caed5a902a46be1e58b865470000000eae00000012f0000c590002ad400000054a154168c35a510a645b28d7a6c49a44ec217f2a088508ac3af2781b800001b400000000003f329aaeb00007b43d9000000079c63480000000995d888680009d90000000000000000164d9003de0001d5145e20168e9ae449c85642321e10701d82b100000000000000000f0a0000002b800009772c1b61800042f041000047042d0000001aae6c300000007548d50002b90f780006239360bfa38008c80019e8d6818b21bc2a20005da0000000a306b4865d110000000193cc5227c5dd800000074f27b309400090e502000000000000000040020038014006001002000400c0000000000010002002800000000100a800000c007000000400e0010000008002002000000000800300300100000170008008002002000000c01a000000000000000f0000018000003007000800000d00080080080080000000000000000000000a000001000401a0010008000002002001000800a001000001c00200000000100020000040004002006000000800800100080040020020000000000000000001800200100100000000060040008000000000800000600300100200000020008000006001000000000400000000080120080020000
  | 23 => 0x182c0004b048100019e200000000013ba000405802c81200000010e813e32b213800000000000000017ee00000000005d897b3b0000000000000000000000000000000c6c15b00000010960000002af00000000002fe174858b01f1624000000000000000000001b01f0000d3f55617040ee00000030900000001bb00009188dd0000000000c5b0000000c20896355000000000000014018600000001b6400000000000016521553072df00005e100000010daced35c000000051e0000000000000000000000065a4f083183e48bc543284102a0e66322b0cfa400000001cc0000000001c2580a3870db34f80000000000b1800088f00019514ac3c817ba3d00000120000e28e9019b000000000000058e00018ea00006196200000002ba000102c0006551fe9550bce00004e1174d8e0158444000cba0001800000acd58fae6d33a52644200000000000000e5800000000000000003a00000000000000000251400000000000000000000489594000cd4000309c86a0003ff83bc0000000000000440c2339125613808420000001570a364d5000000000066900000000000b397dcd301542d00000d5e00000012c8000000000033814296a125800000058f5b5155000000000000000000000250d385d00002fc800000000000000000000004cf27553969182df893d7fc78c000000000067d42a86c0fa2bdf2122c807ae8733020c9cd123c05b59af11ee00000020f800000000028b00000000000000000000648a8b400000000000012d68b51a794280008995848d5037e84d0000e7088a9c66568e0400026c000000000000000027b400004569111380001ca00034f00004e40450000000b194ff00002cc234026000117000067da3e0bd07db000000000000047d00000009ea21e08396f4000000000029037e563a17cc6037a50f92bc16a893016000000036944180007f000034b00004ce000050000000000000000000000003a8000000001842c35500000000000000b780000000000000000000000000033800000014e089a0000000000000000168400000009d1feceb2c1b21f0001a8200059a800020000000000000000005a52e3527c1ea1a992697c8add0a50f8932a00024c206cdb4373416000153e4b403c9eb4000a5f6c1800000076d4928001a220000000000f7e5b55b6000000000054100000000001db0000000000000000000000000011cc8941ba00000000000000002068000000000177c0000002b70eb000000000007814244100951214b52507018110c0000000e6b10400000012901e000000051a80000002992108e0800000000000000008e03d100000008b40000000000000000000155a2e6000258c5525910000000a6c606434878573813c00000000000a806e9e0424638b000268000074300014480000000000001048
  | 24 => 0x901200d46c9e162a0fcce43832558dd000095063fabe9100a8800000006101dd00007ac00000000000000000000000000b4a0005de80011c600000000000000000002270ae200000000000000000001f080000006010001a163cd30980001900001990744000a815e007dc00044f00000000000cc5951b2000000000000000000003c316bce886cf3b82fb800000046396e099c56c11917a40188360bc2b8978c2c80331f0c0d000035f8dac00000000000004ac89d56710c0dfc0000000000d620000000000000000000100c0000001892d882be000000000020c7760002e7c7e80000002a5c00000034288e900400064d8cb97a81f908a00000000000002b65a0000000027e84ec4c3525b4d052a00016580012dc00000024544be54b4d2000000000008d0000000c87378000000000000000008dc9a13e4972400000062200000000001f38f84000b854b000000007f5000000000000000000000000000cf800000028f46880000000000002f3cb2800069d8b1c7e0000000000101400023a05610a048100000002e6ba24b9afc800053a0001f3c0000000002ee00009ac50300000000000e08000000000000000188ca40000000000032a000000000050500002c40003583ab0000c1400000000000000005c1800000000000000000000002d200015e80006090000748000000000000000039d83f8000000415000000000000033cc000000052800000000013580cc0a40005c119017740000000001918d240000000c88c6f000000139c00000030c8000000000000000070400025b00000003699f3838a4a7507081400030200000000000006ab0000904cee00000008ae0004671d1c20a00000026c4000000000000000000015580000000004108000000000252934c00009e00000000000000002bac0000002d70001532000000312823ccb90001b50000a2600030fc00000000015600004903f48000000c9d5348f94000919591b578d2a5160000458000a580000000000000222000000055342000012f8000000000062e5ca5d78000000d2300015ec000c5500000000008106a7000071cc1954a8a7c0000000b08000688d7d1ee0000f4e3313fea5a400000000008a09fe63a34eb02c0000004f30001466b310000000e5a0000002d1d8fcaff00000000000005501d7c2f24e600034780000000000a8c0003ec2f8000000056160e8000000000098011daba6870b280000000000728001a328d00db9f6800000000000000004c76b19f294061e9036a1680000000d280000005f500035440002600001edd4d000000005480f642c0de0000c5e41f3a0114814e2066412a480003a6000242cde200000000000004d700000408b0bc5593a2f94b615d00000007b0af9000000000000000000007607d35970000c7e0000001990000000000
  | 25 => 0xb2920218c90000000141866600035d18a04043be00016e0bc814d1dfd664000624adcc00000000034c1928d150000eb400000000000019ec9f72da0000cbc00065080017120000000e152527c800011e14a40000000c3000086b00001a40000000002310000d843529b585fc02e000008442e5d0000288000000000000000000000e10a5d68028325880000000000002cc0000a5c409000000000000000000000000000001990000296000117600000000017c00000000000000a960000001994388000000000000066300015f69c10000000000a8f00005303d061c6b0a6d000000000010340001db00000011468dc1ba800000000000013105de0000000a98000000000000000072a000000000c0003508e5c0349dc0039f500003030000000a88c3809280010a400000000000000000001370a9427057f00001b200061f0f1c000c8d0000000fd80044cf8ae922809d000000000000000000000000004ebad8c0004590002fc0dc2000131aa240008d33dd8000000000000000000000025b17e012a0000000000f1076514c000000019d00035dc4266b35050000000000000051d03a00044d991c0005b138b955c61400000032800000000339c600000004cbb30c00000000000003a0b3900000000003ab09580000002390000abd03c5062d400000002e95cb81801305853cf1bb0fe43190eb800196000053f0001658433243000134e7ef5ab80018c018948b80006766c500000005aa0006b695fc0000ec00035b05dc00006f0000dcc4e82c380000000003a130ac06e9852eaa4f4f28c07286aae400000000033dd9980003d705d40000004753334c10000026b1d80008a92571180000000000000111204027a0c2d04a059000035800000000000017a678b42400000000005bd8000000194000000000000000015240003182ff8000fe20000000000c7c000000264c0008700000950000c080001f7000000000000013ca0001aa932d76c000000346c00000000018cc000000000165830a66064304dc0000006bc29e43fe00039288bd896cff4640448000000000000000000000000009720000002bc4000a3c25d128c7d6ad754880006a44d910919a48ee5454d5800000086600024fc000000203800038e00013ba5f400000000000004f65405ee272800000000000000000000000800454b264bf800000000051b997400000000000000000c06290000000000000000000000000028c400064c000000159026a00000008f200000000000000004868000b3e68a3f1800000000000000000000000000454000d326b293ada8e6e84b332c4aac02d68d028962c000000000000000064280001ee0000002acd3368332cc800157a55d0b6826916cbc100034f477a57800007f58a21070000ad8d1e559558000000000000000000000004ed10c400
  | 26 => 0xb252d1e60d100005b4810458605016f00010e80000001ab16fe43d2f2000000000000000004480004fc0000d38a7b5a29de00005254c231ec0000004dc00000000000001c9c00000000000004e29ec0000000c22994000216d2702f0217196509253900000000000004fe80000000004a22e3c00000018d25d000000028d20c05ba0004f48b5dae600032400000006803bd87ec00000013310588f81a811e8000000c0c00020e400031c00000016b814f3008000000000579800000017200000000000003d2b3790d4d0f699909457091c321800000000000000008d671542991c52fc0000001ad4000418266aad8000c9600000000006763249f412b6ae600013f40007113fc11082c40000001fe5276a3b2eca0180003a9008a188000000347253c0000001ae00008b40000002cf800000000000000000000001a48b2ac3c00027bcec42910003484000abe000000035c0000002afdac05db000000000062e3ff1e0c00014b6c597bc0004fc000188144400000000000000003aa989c54ac041a48dc178444d00033599a20003b625300000003a51fa93a00003af000000000000033ac0000006a10000cb8b3326882e4f5800000000000000004b920700000000000000d680004388cd000020935d02b4d48d4d5321ff00540002808000dfa0005b6800025a0000000fdd3308c6156000000000000000004da00000000000000000d200019d800000000000000000271191ac80000000000000bd10002df8000a42416a8acfe831419f8000b9800003800000403114598db4000cc200018c40c6c345c3aadcbce4db0000ac86d851f00000000008940002e2107a00028200000008c11c82f68000d804c68000e780000001b000001740001f1c27cca80b70f41958bd90e434040009654808d895bc72f25f20bc0000002119745adc2b30f18d5c000000000305400000000033740000000ec89f8000000000000000000032500009421020000e10680ca9639a89c4ba000000291d01cc7c00004d9a0400000000500007a15611b6c000c79000000035e4556c4000161a02f1280000bec2b91fe80000000000000000000ac60001ebc00000000000007240000000b4c00000048980000005245f112fc0004aa5880000000a6b0000000000b5e4148000000afd000000043a0000001ddcfaa73d000236466e000172122d266000000000149c0002010000000000000000000005623280007a291605f0088002000511b4391400000f70bb55760004362628aa20003530000074ad3603000049810f0000000000429000172c0000000002c088023c513a985000086367d24a800000000000002f60000000000000c2600000005f09b900004f400000000004980005fb14900018d419c0e7a9bd9c80d1000088c00000000035d940a00043
  | 27 => 0x3d00000000710000000000d915518d307f200000031389c60006b384610fa03938d3384000ba600000002fa00041a00000000002d5adc800000000000000001134208000000000000000000000033a00000000000001698000000000000000000000000000008ee00011d80008ac0001381486c702f28711756000000247c20875155900000dc00050ba5e8ec60000000000000000000157c4620001d424a0c3a0000000000c5000053b80000000006c900000003e02c51e080008601242984000cfe570800000000010b00000002bd000336c00000044f000048c6cb00007d153cb1d689091d258000537000000000027700000004755d49304000a3239d000053c000340800151a5130128a1800084c4d121dd75a18607714a40000000001d2d9aaad55768000b0483a00025b54ea9783b78000000000582000176e6bb00000000000000000aed71cc98425251c000923000000000000000028740003b54dd096995e0004b380012b8000000000187600027d000051840f50016d9a2c92e1a2a6719c408643411c80000002dd19cc41855521f85343b40002a9000000000000000017ce6e513f80000000000000bd00000000002bf0000c01065800000045c000000099e49c1df2ae8824d7f0000000000000000000111600000000000000002a68001a9453c2f71a8000027a69b80014aeccf2e284d4cc20000000000000d25000000000095600000000009402de80009c2280000341000000000017880008651e5800068481f3869db8f3e84362d2664f460e70000001a400000001ec4940d07090800037a0006a5800000000030c00017423a75aa80000000000b88778cae00068a2d4d6e200000000004ae739678000000011b3621a0c00000053d000036a000000000046c00000000000008955548000b2400011d80007ccaea00020112349b500000000000000000000ae487a0002ecc0001ce338800161800000015e48767c00072a00afa7e600034e8772b1137d25880000ca000000000000000000009be0000000000f8ca6711580000000000000000000000000000142663b00009540000000000001a30000000000044c00002d8f1000022704b8000000c180000000000000576000000000000000000001e20002fc4000cea33680011aed49000000000000000003ec00033300000013608b261b0b3c0000000001678000ae331a86b026462d5a494e031e0005c92bdcb38be900002ecba60005bc891400073537780000007cd3f980006469bf0000000ac6c2f000000167451c2ae086cc4800000008217f8ba70002d7c7840000000000000408000211c0000000002b513e00000000000000b1200012d400000005f80000009e70000001ab828100000000000000001c713c000067e13dc0000db0000000000000000000000000050c24800
  | 28 => 0x2690000000950c221d1800056e00015f0000000000000000121e0000000000a300003eb0000000d703cc9b54ac000000033140000006a80000000000387ab4959489f167195400000058d15c00002376bcb0684b875a0000000000cb2000080c6ee00045080000005ea0000000d3c4a20002e2c00000057b00017c200037a109800000016c00000000640000000e260005cd0000dbc00000000007660000000001b2000050e1768000c67301800000009b6000001a9e0000000000000d4400022416ce2720000000252000000000000000000000003e600000000000000005d18001a2000000000000008fd000094400076400000000008f1000271c00085e4bb23899d0adc455b2880000001f890290b800000000001b8b370001638000d660000000000c5f2242ffc012d170000000000d2f0d0270c00036f2e730e8d9a2da069000000000064480013988ff4538000df60003bc85a975400000000018c2000000000000000046f000000000000000000000002ec0000000000000007400069f00000009764fb00000003320000000001668c71000315c61e29626a9cad72087248632640007b824b00014a08920000000a1c00007a0964000cc0000070d60c8e80578c6cb44907000332407a0020002590000af500006cc000a9c000225c0000000000000bdab0821b84340000000000000000000404a3d8000d591868001926000000000177200000000017f600000001b00000003319cd147436e53290ac000000000187d24cbfd4d998485f8000000000000000028c87552de6f60e300000000000001c0000035054ea0c42f4af85ca985cf267b92490d1d91047f000000139a00000015380008b10000000000000472b1b8fc08eb0000000000b4d00000000000001ca000000000040ba15c40880f00012640000005aa0000000cb73338b9c0000000000000000d1c4819eac00087c00000000009f336e9d14e6c3e80af000000000027289b800077e05580016885eb4c60b300000494de8c895de1fc1f7a824e24b9800000000005c66c500000000003748000000000000000000061b0000001a3e00022e80000009555038000000000000000000000026e84b00000000002c940005ad3710b0556200000013484920000000001b1859a2f8800000000024d800000000019200017ac00003d32e0ed419e000000000060f25c159800000000000012b200038c8000e629610d580000000df00023500005ac0000000000000000220400000000014ac0000001ef800088000000000014fa450000355400000000000000000000000000a6200000000000000000002714e0200057480004e80000002c880000000000000b1a00056483900001ef0000000000000000049cb8000024ba9180000f31e303a173c8912d80000000b0f1211014000cbe2
  | 29 => 0x172b3700000003e5a3e4c8479d00000000008080000000000000000042400000056fa6ec00070c5e38be8ad20006c7a4e8000bca00009280000000002c514283461f9233c508a2800000000008af58a800000067000000017ae9080000f54ac867a00024c16427b300012b00000002d18000fda0000000000414000000000182e0c500034d40000000002748a4e0002238000000949000244537c6ab0000000000c135f180000002932f60d78000ba800000008a600000022e400000000033100000001cd86e06a20000000f3c00040c030afd86f81534001adcb6e0000002c0110c0001e6000119213f1cc80000009bc0001e34000000000153d5cab8430495b4c429ee00003248de06b0002a1c00063400000000005e665a074996a2411af9fc194e4132ad86b490831f02e9d34e827f70000001946000166afe91be20700000006860000001780e045176268b6d4e2233335b1dc71a0b30000c1000000065980000000000000cbc000a0b10e000000000000003104d0d530002758000641316000194ac58000178d3000fc58285046e400000006340006d11c3075173a00009c856478270b099800000000000000003200000000fe8dd600000000001785de17d80000000000000000cb06393d20000e4c000472000000012e00000018140002941ee92e2170567800000000000000002c0000000000159826f00016a92f200024528085b85be66995d97de00003b00005b20001c7ab000000d8000165c0000f0054b5199140000000001648034391800000000029bad0d21200000026dc92600051500000000000002138fbe6025a78f586900530000000868142000283c0000006068e88ae6d5b1898000000000000197d434000190000000049400014200360000000000000000256a4b40000002bd000000000000030f40003d200000000000000002a303f488d0002e4474a0000001038f548a620e0000d8e000000000000000065e08d40002e31ed22c01c6108000274c6ba2f137c80012440004af8001436000013075800000031583340000000f600000000084fc80000000005a08510c440003e212cc0000000001994c9a00000000000003253430000d1656f52a13a83e000051c00005c2a166940000bf82945d7000076882248826b81b40000001cc93ec1bb4f1117d3bc00000036356de00045425d40006ae000000076e00038e8af000094600010740007eb5f5800094c000551000037c0000000000000000231afe40001c900000018a8000000000104600000019899ae00000000016b200037fadb9ad4000000058c00000061880000000000001018ca272c0379a10000000000000000049100000009d80004e2040c000000000000000016b000000197ad7e14702357bc31d5578000000198541aa840009d141380000000000000000
  | 30 => 0xe635681da0000c2000056a0004f20ad00006ad53a0000ddc77200000012a2a534a5000000000007000000000000000000000b3600000000000001dd80007ec00000000003ca0001b327600000003f400016a400055300016b00000000000000000075000179a00000014f530c0000d50a2000074e0001150000cdf2e200000007280000000416ce061c9e691a442200000000000001ed9c580001930000001262bec0000d8d8500000000000120000000000069aaaa43f921c000a2500000000005c800000017b00000001b198bc0a668680000009ad00000012560004850000b3048f00000000000000190844e8c0002a61c1d6ea5a73831f04d7a3c310aad305d60000000000070000287b1c8000000684000000070300002b85fa00019489e46ca78400024dd93e0000000000b0c00059e0fa9906048281847d6c0699000000000033a46d8d0400000030b32549ac0000001b900000000ee0000000000000000000033c6988000f12000000000000046d6330000000000000307802a0006848cc18d00003cd81f41f0c6323300000008a45260001078c7a04b02100000003d822941a008c000000000000000000000005f21790000000000000000000000046500006f26500000dfc32c99a5b42978898d2c0000000000000401823d9a000011f0001482000000000000000000002d000000069500006fa5091b21f6062a000000357c000000000000000068c2eb2d68a4200000027c400000000000000000000000001a4c30045b800000003b3611c90e7e00000000000005d745e8f3800000000000000000cf3ac23cc9520000000c18000000000120cca4000000000030e0003ae85d800017e00016e443c000230800065a88e0001ea4bf40000000000000000000000000000000000006727304098000000000000000147e6e30000000e20c8113c1cdc8fc0000000ee8000000000000045200000007d800049f46100019240002360171b0a39538514c01020001308000a2aa5500008345166a2000139c3020006048000c8c4490140000000ca412c00014d47e200000000000003f282c00000000000a740000000000000778ae800000000000003378ab800057c04a04a00001fe0000894000000000232c7620006c080000000005470000f6a6770000b58a84000000000000041a0000000a760f10000000cf600000000018fab8a00000000000000002a6cfb216c647311523c0d500018c800000000500015b400000000000000002a42d755347970910000f6c34a48e80000003f5000364c000000373800174000000002dc5841df000000000000000000000000006169ca4000000043800000000053b06000000a35a400000000ac18380013040000000990000ae747e134178683707c800118a71f00000000000004b80000000000
  | 31 => 0xd454a9b22c00000000013080000003de8000000000000000093c00000015786b20000000000536000234226000000006980007c600026280000fe1f1000055c0007be63613d4b7600047680013240000d10c4000075304927ec32a4673c713b4380075000010886cbf401ab1ac0000000001238000b2d66c30459f085d10c062834e013587000129662661980000000005ab0000d36a720000000000000681aefc6d43dd00000015a00004288000000d6f55283fcab400012f0000000000000000000000034699f0828acb0f6ad0800000000000007349a330d000181e000000000000000008e00009f2000525344c000d06694800000000000000000002df00016cc00000056d959c9d22c4277a878df0bcb400a01c000bf30000000f8a00037919a00000003151b49b2c000375000056263700000000000003412a61616222000000000000000000000000000000001a14000000361c9104cc00000019b23681bdad980d46250001d24e5c6150002fa0000a620001a68c96210000000000052a00025206ac10b00000000001925819d7000000030280005c0a51382add12ba140578350cd9444141019fc45a168387118800000000014880000000002a4cba88aa27c00000006a944622140001b23768194f000000000000000000303af3018e0433eeadd84040c132b068cd92265695800000000013135c8efa0004f4000000003c00009cd6f0c975df2f6d1ce84532700012b490453e2490000000406ad90000a15000000000039300000000009eb0000014980000000000000002900000000003010002508000d625ee887c0003ae0000000000590151000007e18862b1ce00000003b8a8f90b286e36710c800012448d9878e3c8a200014758865f32889a4110e5430d0afd40003610000000000ad600000008fa0001f20178000000000000000065300000000b49f40000000000000000000000004612232ec0002c92cd80016ee00000013cd15cb3817986a59344da38d800149228520b80019560006070000948cf917c8ec8d600000000000000a7800026251c20006792751316c62000338cda059d087354902800033610e4286d820000000000000000000000000000000000005dc00030847180e20001a4ce40000182800000000d00002380000000001dd4000000542866800000000000000007a0000000185200000000000003d45a5ad6c81698764e23ec7925846082720fbcccb3f0a8b99082895b08b292685f42b52b045ec0006299bd40009350001b60000b650000ee0138000126916d3e4000000000135e48d00000000008f2402b3f57d40003c900012640000000b8800000000000018400000001d300000000000000000d58577000046000005b00007f69430a29ea0000000000000057e82e00024d84fa000531800
  | 32 => 0x15489a515400000003354778a80000b3b025906572c0fa0000000000000354206000000000000000005140000000f2213100005180000f20c722280000000bb9a5d7289210f200000002f505d2b1400041b6862d39302a190000000de600047600000000000000000aee000299800000000000000587da0aa00029350fc000000000000000000000016560005c0000170200000000014c0a8a000000000076615814f915a0884a0b07cc7a9a60002844000c5c0390000000000000062c0000000000e74000000000000023a0000001fd800000000000013ea00040c9da000004f000000120abd20000000650169000035c742000049ad400000003eb800000082633c00000000002ff20a000000069c800000000000000000000000000000000c0300015d402e0f60001d489e400000000004426cc616000000000037ba8052d07e42bf2190000cce5be80019ce00032d8000000b131bc1fb800050b6b5a398a5c000660aec00000004a680007dc5c7000072cd6c000041a5500000000000001516d9552c9ac948a44600000000000000000000a2000005200000000000dc9b04a4063c43a94fd778bd0000000198e00033f000106400042a00000007cc0b780000005dd1751254000a390000cd8ed6000696800000000000000000004f10000000112c352b580000000000000000000000000000000000000000000003710002ec800000000000000000000000000000000000000000098e000000050439f1509dd07d26a734a2b617cc769000151800028d3b3b100cd4000583800000023f000000120cc16000045cf1ed710002c6c000b1e2c00d9d7882d40000000c460004ab8558ad000000000001fa000000000170c00000000011ac00f000000034c00009a19e40000004600000000d4c0b2064485410a4d429b454e8bf05e88b8000b3f43db3bc45833e48914c80009fc58b8000000a904e4800041e58c1438000000000000000000000051a0d2c006000264a76c0b0000497a998c8a8da3c5090c000000187000000008b0000000000000000146c0008fe5d2b0700005c24780bfc00000000000006125b200000000007734c41b7c8e00621b011780001d3000313c00000027124e41c293c3bd14bc000ca61cc000096e0543f3a8348703d93c38f29452d750a497345809a962e8a283ea0000000001104000000230c0000550400000000cb614e0b440000b851e94b455a00022880002b80000000001a700000000001364cf51e9ad449bc5cf000254800000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xcb676d93314405fb64e1b26628814f2d9d864cc5100071a328c998a2053db2701933144001caecbb1e62880067ca0172cc51000636396ca98a2000cac72d913144001998e5b1a62880031bd97724c5100063632ee498a2000caf64dc93144001958c9b92628800378043724c5100fc3e432ea18a2000c3c645d43144085aae62ba862880021fe1f650c51003c3ec3eca18a2000c3e75d90314400187aebb20628812e5d219750c510006ab192ea18a2042d54325d431440b18eec0ba862880035c881750c510004bbc3eca18a2000d3575d90314411f96cec32062880034d5d4640c5100071a328c818a20008f686dd2214411d96cec32442880038d19464885102147ac3ec710a2000ec432d8e21440055c904b1c428800abca1b70885100073210eca90a2000ea421d9121440018becbb9a42880031719773485100064fb26e690a2000c9c64dcd2144001ba021b9a428800317d9473485100062e328e690a2000c9f641cd2144001938c839a428807733188734851024ee2108e690a2000ccc73d8921440031f50db82428815b1d1db654851000732316ca90a20018f4865d121440853a906ba242880bf2d1db644851000752316c890a2053cb4761912144001c68ca322428810a75a1f73485101366a3b6e690a2000dd070dcd214403b9a8ec39a428810b35a1873485102166ac30e690a2042d56851cd2144085aab0a39a428800355d947348510006aa328e690a2000d97641cd2144001b28c839a42881277118873485102c66bb00e690a2049dc7201cd2144093ba44039a428800371480734851024ee8900e690a2042cd473d8d21440051e90eb1a428810b351cd634851001572412c690a2000dc473dc92144001b88e7b124288003741cf70485100063c3b6ca9022000cb876d912044001970ec32240880038e194644811001575416c69022000ec832d8d20440051f10eb1a408800b3a1db32481100cc7d430e29022000be18290520440013e50f98a4088006bca1b3148110005b8c28629022000be1820c52044093f806418a40880067a21d2148110016743b2429022000bc8834852044001bc0e290a4088006f821d21481100b6f043a429022001be28648520440037c10c90a408800bb8219214811001771bb2429022005de0764852044005dc0ec90a4088236f8e15214811046df0c2a429022000f63654852044119ec0ca90a4088002f8e112148110005f0c22429022000fa3644852044001f40c890a4088003f0e0d214811045df141a42902208bbe0834852044001f810690a4088002f020d214811000771b1a429022000ee16348520440ad8f4edb2e20880bf2e9db64c411001e5d3b0c98822000e386519310440051f50db9620880867c61f31c4110005b8c28638822000de17288710440017a10690e208800378dc921c4110
  | 1 => 0x8ebb22c6880032b1cb6458d100045f438c8b1a2000c3f751916344001878ea322c6880032b1c86458d1000637b2ee4b1a2000c6c65dc9634400195ec9b92c6880032b1937258d100243f43eeab1a20008bf845d5634400717908baac6880023be097558d1001476412eab1a200087e871d5634400717d0fba2c6880030fdd77458d100061e3aee8b1a2000c3f751d16344001878ea3a2c688013171d65358d1049666394a6b1a20048dc8754d6344123998e4a9ac68800a3ba1f7258d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a20008df8758c634400159904b18c6880063d6067690d100043fc2aed21a200487c855da43440090fd0bbb286880021f6177650d100043fc2aeca1a200487c855d9434400117f08bb286880023be097650d1001476412eca1a20088be87d9143440031ed0db8a86880031d1977150d100063a328e2a1a2000cb7641c543440090fd0dbaac4880021fa1f65589100061e3a6cab12200087e871956244001878e832ac4880030fd9774589100061e32ee8b1220008be87d91624400187eebb22c4880030f1d764589100045f438c8b122000c3f751916244001878ea322c4882432ddc464589100062fb2ee6b122000c5c65dcd624400193ec9b9ac4880032719373589100062fb28e6b122000c5c651cd624400193ec839ac48800327190735891000666310e6b12200487e87dd5624400117f08baac48800e2f21175589100046fc1aeab1220088dc835d562440010fd0e3aac48800e2fa1f74589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100446f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000ccc73dc96244001968e9b8ac4880121fa1776509100043ec2eeca12200087f855d942440090f90abb284880022fe1176509100046fc1aeca1220088dc835d942440011ef02bb2848800a2fa1f645091000c7ac0ced992200087f855db32440090f90abb664880022fe1176cc91001c5e422ed992200487e85dd932440010fb0bbb2648800e2fa13764c9100045ec26ec992200087f855d932440090f90abb264880022fe11764c91001c5e422ec99220008df835d932440011df04bb264880063da1b714c9100063a32ee29922000cb464dc532440033e501b8a64880031d194714c9100065a320e29922000e3464d96414405f970e1b2282880031e19770505102b63a3b6caa0a2000e3464d9541440a556d0dba2828800f2d1db745051017ed8386e8a0a2003ab686d91414405f968edb22828815b1d9db65cc5102b6b9386cb98a202f
  | 2 => 0xf6248710005f0c06c490e2000a3e8498b654400147b09316ca880030f5d074d951028d3b408e9b2a2056a75811d365440974ed03b9eca8815a9d60773d95100062eb98e7b2a200087e8710f65440010fb0e21eca880028fa1272d95100051ec24e5b2a2000a5f835cb65440014b906b96ca8811a9da0472d95102b53ac08e5b2a2056a7a801cb65440014f300396ca880021fa1c42d95100043ec3885b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a2000a76810cb65440014eb02196ca8815a9ea0032d95100053cc0065b2a205687e87d0765440010fb0fa0eca8815a9ea0021d95100061ebaea9b222000ab581d53644400917f0eaa6c888002a7a0c65d91100054ec18cbb222000e1e831976444001c3b0632ec88825b8d60465d91100051f42cc5b222000a3d8598b6444001c68cb28ec8880bead21951d91100061eba8ebb222000a9e831d7644400153b063aec888002ada0475d911017d5ac08ebb22202fab581dcf644400147d0b39ec8880028f61673d91100070fa9ca7b222000a3e859cb644400147b0b396c888002ada0472d911017d5ac08e5b22202faba801cb644400157300396c888002a7a0f52d91100054ec1ea5b2220008be8714b644400117b0e296c8880022fa1c32d91100045ec3865b222000a3e850cb644400147b0a196c888002ada0432d91100055ac0865b22202faba800cb644400157300196c8880be2fa1f51d91100045ec3ea3b222000a9e83147644400153b0628ec8880beaea0021d91100061e326eab22200087e87d9564440010fd0e32ac88826f1ddc465591100243f43eeab2220008bf845d564440011ef02baac8880023ee0175591100043f438eab222000c3f75dd16444001878ebba2c8880031d1d771591100063c3aee0b22209ac3e76d946444133c6ae3b28c8880022f61e65191104a51f42cca32220008bf87594644413156f02b28c888002aee0165191100054f418ca3222000a9d83194644412f47d0c328c88825b0f9d865191100070f418ca3222000e1d83194644412bc6b02328c8880038d9c465191104af1ab88ca3222095e3a20194644412bc6c20328c8882578d04065191104af1c080ca3222000a3e85988644400147b0b310c888252ada1a51191100071a32ca23222053ab4865446444001c68caa88c88815f1d5c465d8d1000c7ac0eebb1a2000ad5810cb63440015b300196c6880030f9d36598d100061f3a0cb31a2000c3f655d26344001878caba4c6880030f9d76498d100061ebaec931a2000c3e75192634400187aea324c68824f2d5c46498d100043f43ecab1a2000c3c74d9563440018d8e5b2ac6880021fa1c6558d100061e3a0cab1a2000c6c72195634400187ecbba2c6880030f1977458d100045f43ec8b1a2000c3f75d91634400187
  | 3 => 0x6b224000c5c751cd64480018eeebb8ac8900031d1d771591200066bb9ee2b224000cd473dc564480018eeea38ac8900031d1d471591200065bba0e2b224000cd7731c564480019a8e638ac8900032d95071591200065aaa0e2b2240018ed82dd763480091bf0ea9ec6900029761443d8d200462e31aeb31a4000c5d75d8e634800117f08baac69000e2f2117558d200047bc0aeab1a40008f4815d563480011bf0eb18c6900063b60a7690d200147c432e121a400087f855d943480090f90abb2869000237e0d7650d200047bc0aeca1a40008f4815d943480031dd0db92869000a6b21d43509200055643286a124000de210dc542480011ef0eb08c290002ad211611852000c76c16ea30a40028f980dd461480015cb04208c2900063b21972905200147c432e120a40018ed829db31480051f10cb8662900021fe15768c5200243e42aed18a40018ec865ca31480051f10cb84629000a3b208764c52000c77436e498a4008c5c635d431480c9a9864ba86290003175d7630c52000c76432e418a4008ccc635c831480051f10cb8062900063b2197448520324e641ae890a401d9ce87dcd2148001998edb9a4290003331d87348520326a7428e690a4064d4d851cd214803bb8b0239a429019372a007348520326e4c00e690a401dccf601cd214803bb96c039a429000372840734852004c77438c290a4000ccc7318521480c9b88e718a4290002f86023148520014f243a6290a4000ae4864c521480c9b88e698a4290003721cf7048520007c4a1a849824064bc88348530480011ed03baec9880122fe1d54d93104e55b40ee8b2620008ef825d563c40051d904baac7880063d2057558f1049666394a6b1e20048dc8754d63c4123998e4a9ac78800a3ba1f7258f100067238ee4b1e2000ce4711c963c40118bcc6ba8c78800237e1d6318f100062ebaac631e20018f4815da43c40011df04bb2878800a3b2097650f1000c7ac30e2a1e200487e859d942c40010fb0b3b2858802237a0e7650b100046ec1ceca1620008f6819d942c40031e902bb665880023be09764cb1000c7ac30e29962026acc8258e31c40118bcc6ba8638816355cc5750c7100062ebaac618e201dacc8258c31c40b1aacc6ba86388003558c9750c7102c6aa192ea18e2042c75605d431c4001aaaeab186388172f1209630c71000c7ac36e910e20028f587d8e21c40055c904b1c43880773318873487102e6e2108e690e20018ee87d8921c4001998e7b1243880023de1974487102c4ea41ae890e2058cd5861cd21c40b1aad0a39a43881635561473487102e6e2310e690e2058dd2801cd21c40b1ba30039a438817371c807348710006e2900e690e2058cd473d8d21c40b11e90eb1a4388163351cd634871001572412c690e2000dc473dc921c40033cd0fb124388003711c
  | 4 => 0x1484f5998c7b9262909feb5a1b734c5210466a3b6e698a4226dc472dcd31484115ad0db1a629089b351db634c521136e2396c698a4208cd47618d31484016ab0a31a6290877711c8634c521014f343ee498a4222ce476dc931484f5d88c7b9262909633518f704c521014f2416e098a4208c5c635d43148401ac842ba86290803179d7630c5210062ebaec618a421dace86d8e21484f5c9d0a31c42909eb9361463885210ef62c08c710a421dcce7118e214843bd8ce231c42909ebb118e318852114cf3c3a6310a4202ae4864c621484f5d88c698c42908033318d708852100c76412e7b0242018f4815cf60484011bd0fb1ac09080317dd763581210062e3aec6b024200c9f74d8d6048401938e9b1ac09080237a1c63581210062fba8c6b024200c5c7518d604840193ee831ac090803271d063581210054ec2065b1a8000ad9800cb63500011bf0eb18c6a0002ad61351d85400056ac18a3b0a8000af18008761500011ef0eb08c2a00029d21561185404ed5bc22c230a80008df835c861500111b906b90c2a0002ad61351185400055ac20a230a8000e355414461500015ab06288c2a0003395c8211854000578c004230a800087f855da31500090f90abb462a000a3ba0a764c54000476c14ec98a8000ce472d8531500019c8e430a62a00062f219740c5400447c432e018a80088de839d921500011bb073b242a00030fdd274597300452f41ce8b2e6074a5d839d165cc0014f700ba2cb981da9e20174597300061eba0e8b2e6008a5e83dc965cc0274bb07b92cb980028fa1072597300051ec20e4b2e6008a5e83d0965cc0014bb07a12cb980021fa1c42597300043ec3884b2e6000a3e84dc565cc00147b09b8acb9802297a0c715973009d2ec18e2b2e600087e87d0565cc0010fb0fa0acb9802297a0c41597300052ec1882b2e6076a7a8008565cc0014f30010acb980121fa1771593300043ec2ee2b2660028bc8759142cc0111eb0e20cc398013179d553587300447b43e82b0e6008ad683d0561cc0051eb0f30c439809a37e0d764873000c6e41aec90e6008c5c7359521cc0018bccbb9a43980031759773487300466a39cc290e60028f48758521cc0119a8e6b0a439800ab920961487300043fc2ae3b22600487c855c7644c0011df04baac89800a3b20975591300047bc0aeab2260008f4815d5644c0011f700baac8980063ea0271d89300064e3b286a1260008f787584614c0851eb0fb0c62981623da1c614c5300446e418ec90a60018de86dcd214c0051f301baec8900021fe1571d91200243e42ae3b224000cb4641c564480090fd0fbaac89000237e0d75591200446e41aeab2240008f7815d564480011e902baac8900021fa1c75591200245e43aa8b2240088de87dcd64480018beebb9ac890003171d773591200062fba8e
  | 5 => 0x89b711cb734c621014f343ee498c4200ce776dc931884118bcc6ba863109eb530c9750c6210062ebaac618c4200ccc32dcd60884031eb03b9ac11080a3d60775d91210245fc3aa9b2242008df835d564484111b906baac8908023ee01755912100c7c402eab2242088de87dcd6448401998e7b92c890803351cf71591210062ebaea7b1a42048df8754f63484014bd0a21ec6908029761443d8d210043fc2ae1b1a420487c855c3634840153d0932ec690802a761265d8d210052f42cc9b1a4200a5d8599363484018baea3aec69080297a1674d8d210052ec2ce9b1a4200e1f54953634840153d09a8ec690802a761351d8d210072ba8ca3b1a42008de8714763484011bb0e28ec69080297a1741d8d210052ec2e83b1a4200a5f855c363484014b90ab86c69089ab3a0870d8d2100566c10e1b1a4200ad6811c3634844d5ab02386c69080237a1c50d8d210046ec38a1b1a4200a9e84143634840153b08286c69089ab3a0850d8d2100566c10a1b1a4200ad68114363484015ab02286c69080237a1c40d8d210046ec3881b1a4200a5e8510363484014bb0a206c69089ab3a0840d8d2100566c1081b1a4200ad68110363484015ab02206c69089ab3a0810d8d210046fc1aeab1a42008ef825d563484011ef02baac6908231718d7518d210046fc3ac631a4200c5e769d463484018bcecba8c690803555c57518d210046ec3cca31a4200a9e84994634840153b09328c69080237e1d6518d214fd6bc0aca31a42008dd8799063484014bd0b320c690802976166418d210046fc3ac831a429ead78159063484935ab03300c69080387d525418d210056bc0aa831a4200ad481550634843b59d042a0c690802b36085418d210054f426a231a4200a9d84d44634843b59d05a88c690802b360b5118d2100567c12a231a421dacc8254463484111bd0e288c6908023761c5118d210052f42e8231a4200a5d85d04634843b59d05a08c690802b360b4118d210ed67414a031a4200acd8294063484015ad03280c690802b56065018d210446f438a031a42008dd87140634840153d08280c690802a76105018d210ed67410a031a4200acd8214063484015ad02280c690802b56045018d210ed674148031a4200acd8290063484015ad03200c690802b56064018d210446f4388031a42008dd8710063484014bd0a200c690802976144018d210ed674108031a4200acd8210063484015ad02200c690802b56044018d210ed674142031a4200acd82840634843b59d04080c6908223720d7690d210466a31ce321a42028f4865c643484119a8c6b8c869080a792097190d210046fc1aeca1a42008ef825d943484011ef02bb2869080e37a1f6350d210ee66390c6a0a4200ccc63dc94148411998c6b966290822b520e768c5212166a31ae118a4226ccc72d8d3
  | 6 => 0x477c3aca3126200acf83594624c4015cf02b28c498a4ab3a0c651893100476c3cc83126200a6e85990624c4014db0b320c498802b360e641893100477c3ac83126200ae781590624c40159d0d298c498802b3a19531893100566432a63126200e4f6554c624c40159b07300c498802b9606601893101c7743ec4a126200ce7621c5324c401998c5b9a829889ab3a1b628c5310262f3aaa7b0262228ec86dc9604c4011dd0fb12c0988031bdd76258131006363aec4b026200caf74d89604c401958e9b12c0988023ba1c625813100637ba8c4b026200c6c75189604c40195ee8312c0988032b1d062581310061fba4e8b2862a3a77815d1650c4014e902ba2ca188029ee0174594310053c402e8b286200c3d741d1650c4114bd07b92ca1887e9760f72594315152fc1ae4b286208a5c835c9650c5434ef02b92ca188029d20572594310051f420e4b286200a3d841c9650c4114bd07a12ca188029760f42594310043f43884b28620087d87109650c4114bd05192ca1882393a0a32594310052ec0c64b2862a0a5d839c5650c43f0fd0fa0aca188021f61f41594310452f41882b286200a5d83105650c4114b90790aca1882297a0c21594310052ec1842b286282e4c32085650c4014f50010aca188029e60021594310053b40ce0b28624aa75819c1650c40147d08382ca188028f61070594310452f418e0b28621fa5d831c1650c4014dd04382ca188029b60870594310053b408e0b28621fa75811c1650c4014ed03202ca188029d60640594310043f43880b28620087d87101650c4114bd06202ca188029760c40594310053741080b286200a6d82101650c4014ed02202ca188029d604405943143f2619640b286208a5e83881650c4014bb07102ca188029da0620594310053ac0c40b286200a7681081650c4014eb02102ca1882297a0c10594310052ec1820b286200a6e82041650c4014db04082ca188023d20575590310047dc02eab2062018f8805d5640c4111b906baac418823171cd65508310145e43ac8a106208c9c73591420c4018bacbb9a84188223b21d62508310063ab2ee2a106200c75651c5420c40196ac838a8418823179cd65904310464f39ac92086200c5d655ce410c4019aca3bb2621880335547764c4310062f392ca9886200c5c72595310c401898e4b2a621882317dc5654c4310472bb8aca988621d9ce87dc9310c40199eedb92621880393597724c43100667bb0e49886200e4d651c9310c40917f0eaa6c91080a3d20575592210047dc02eab2442018f8805d564884011ed03baec710803395ca71d8e213fd6b40ee6b1c42048dc8754d63884118bcc6ba8c7109eb530c97518e210046fc3ac631c4200c5d7558c63884051eb0d38c87108023da067650e21134e7c3ac799442298ef865c7328844d78906b94631
  | 7 => 0x6d75d4b6250c0159b07a96c4a18033918871589430063abaea3b0a8600ab584d476150c015ab0628ec2a1802bc60021d85430047bc3ac230a8600ae4825846150c0156b09a88c2a1802b560c511854300578c004230a8600c7975d436050c091bf0ea9ec6a10021fe1570d8d420243e42ae1b1a8400ad6818c363508011bf0eb18c6a1002b52056318d420247bc3aa3b0a8400ae58204361508011ef0eb08c2a1002b520d61185420247ac3ca230a8404c76759446150801c6aa9288c2a10021fe1570185420243e42ae030a8400ae58204061508011ef02b9ec0a10023d20573d81420047bc0aeab2664008f4815d564cc8011f700baac9990063e20175593320043fc2ae130e640487c855c261cc8011df04baac8990023de0575591320047a40aeab2264008fb805d5644c8031f100baac89900335dcc715913200673b90e2b226400c7575d47614c80156d09a8ec299002b560c51d85320053b42e83b0a64008f787584614c9495af06b08c299002ada1351185320056ac18a230a6400a7685d04614c8015ab06208c299002b9608411853200c77414e3b0264048dc8754d63904118bcc6ba8c72080237e1d6318e410062ebaac631c8200a9d840cb63504015ab02196c6a08021fe1570d8d410243e42ae1b1a82008df8758c635040159904b18c6a080333188735894100477c12e7b0282028ec825cf60504111790eaa2c99880a2f21d6450b3101477416ebb2462008ed82dd7648c4031f501baec9188023e60375d9231416e2190e2994620487e87dd5608c4010fd0e3aac1188122fe1d54d913100477c12eab2262028ec825d5644c4011ef02baac8988023ee01755913100c7c402eab2262028ee87dc9644c40199ee6392c898803391cb715913100672310e2a1a6200c6d75d4b624c40159b07a96c4988123be1d52d893100557424cbb126200aad84997624c4014dd0b326c4988029b61664d893148e673b2a7b126200aae849d7624c40155b093aec4988031b5d475d89313d567418ebb126200acd831d7624c4014dd0b3a6c4988029b61674d893100717aa4a9b12627ae4e53d4f624c40155d09a8ec498802ab61351d893100733a8ca3b12627aace83147624c40159b0628ec4988029ba1741d893100536c2e83b126222ae6819c3624c4015cb03386c4988023ba1c50d893100476c38a1b126200aae84143624c40155b08286c4989eab3a0c50d893100566c18a1b126200ae681143624c4015cb02286c4988023ba1c40d893100476c3881b126200a6e85103624c4014db0a206c4989eab3a0c40d893100566c1881b126200ae681103624c4015cb02206c4988023b61e30d89310057340c61b126200ae5818c3624c4011dd0e086c49888a3b61c10d893100476c3cca3126200aae84994624c40155b09328c498802b360e65189310
  | 8 => 0x7b40000004fc1f83724d20362ac0000000000000000000000000000005ca44c0004e240271a4260000000000000000000000004684b06b835c3ea3e00ec2a00003101906f00000000000000006265e66a000000027c43200022422200017c00000000085a2cc0000000000000000148725cc0006e60001360004c21006386fa33659055e2b444000072c0007640de00028c4787ce83a7e27140000000005680000000005a40002640000000005ac00041a0000000006302900000005e20008bc0000784b43845366d40000003284867800000000000003381540004301642005b86f400000070e0000007240000000ee06a19a3bc6d000082a4384da30268e0a600020e46a7bc74602676c78c56e1080003c209a00000065600000005800001000000077e0000005941bc73400039a10400063e0f05fe0006968905662d80005bc00014c00059e00052a00000000078a00008800000000000000027a0006b63e400800026000000000039c6f678e7a67ea0006461b800059a0742b872681200015e0000004b600081a00080c7a20000006ac0000000001c802462e3746183180000ac0000000000000000000e059600032c0006dc00034e7ac00079c0001985c00040080000500000402806006000008030000040000700800000000006058020020060000200100a03400801014010048010000040100000000000002000034010040020340180001a00000001002008028070060000000000c000018080000000081c00000000002024000020000040040180200a004010080040000800300000402000018004058010000000080d014014068070080040080100c0000000000c018000060040380100800006400003000000018030000100000000000c0100600400802004000010028000000000300000202c00001004004020000080080280100c0080000000200c0000200c01400801000018028000000180480800c0140000b00600c01800010004018100060040280000000c000010020040081101200000800012004030000020000100100000802800000000000010000200880201a00c0000000403c0f0060060000180001400804803008014008000080000000300e0080000000200c00800002008000000000180000000000000000002000018070000040e80000000401800002008008000000000000101001c008020240400280400000801801004008010010000000180100800000000002008010000220040000100e000010040000000000000a00c0000000a0000000002405400802000024008020060040200300000c018010000000200000a0080100200200c00000004088f5879466190c010ff0ab84c3218121f21570986432147ac3c2130c8600ae5820426190c111e90ea8ac3219623da1c105864300572c1020b0c8600c
  | 9 => 0x60200000075000076239e4ec2c27d00006206ae00000000000000018c66e7400004c80000000006800000000000004d60000000000000000006e20000000003500b64d800079e0003ac0006c21fa0003b26fe5c20000006445d80003860000001740000000004600002680a22e400055c2546b00000000000000003782964923000006546820000008ba36e7c000000070018a00009284a49a2a28822e63a00000000007301262120001d03f68560001da46c1a42520008263805b200000072a7ae0000000900000007d600000075615a0000000005a00000000000006043647520000000006340000be34a00000000000000000048800077000000000048e0004fe00000070a00053a0000004200006ee5782e073a66464e4800006be18206420650831c7e43427c88480ae2080001c60000000000008a80006e021c4f22264e464000016a8aa57486248200072000035e2580004f480800000000000000036800068433a8660000000000000004ee0000007600000000008060007da36077c0004e80003d839878466c73c0000001fc59c65c7360445c67868b22f06ea0005ce3565586a800005e21681e20c4ae3e80d425a75e0bc75c7120005124dc08e00069c0004cc6de0002462504244a861a5240008ae1dc00000000000053c02e0000040000003be0000005426983c450e6220001580001240620000005725800f84a26f800065e7b20000003085461de4c679816633e7fa4a62e200016c5fc3466a60943662fa6cc1ae5dc23285058600014669200041829a0000002c60e871624c1d60000000000000000605260000008322727180000005103ba0000000000000002362941c00003dc00034c0000001ee0001ec3880001b203e58e4f067e00019e53800000000000000011c67a0001f00000002426ce4500000000000000000000000008ac1e200076a3d200008083e0124c000000000600049803a2f41cc4141061d25c857e46e53069e75a30e0d228800042287e00008a3a60000000008308b80403c823e81645800021435400071c0002ec0000000000022a864a0004b27aa3344f60f65d613489c1206bc17e00030c00000000000033253e11a44a6c43ce7960000006c638202c0c06fc62a0006064722a615c0ca00039600003c0aa38a0001be7b01ac0000002be8580008a20163f800056074800028a5f43aa1860000000003220000001a80000005e40c60b084237a1e05f232076609600076823a1520001ea2f622c00089657622a07260027600000000059866880e00000003262452c16e00000000000000072257a00000000041083654e4568a412c00000042837e00043600000000026200000077a44418887a3580000000000000006e80002ee4ce50200000000051e0008026aa5f82da0006c02de6da47e7d40000000002ba00
  | 10 => 0xaa6281942486120000000005b47ec7903f200000045c0e24744765a600050c26a0000000000702ea77400000084647010200087c6320006761420000000000000007fc6c82207cc8b000032600000000000000040e7f25284d030400066a0004ba2c007e00047c0000000002307d21d40000000e400024a12a0000fc1802aa8b40006f230a00000000040813c11821e1e454a4ea2fc01a0001f27f000070614e4460306702020002043a85183e20000a800000088c00000000c00000041c19c8527d84aa46614449413e5920001fe6b43060540287542440000000000007284847dc25e0000000000001e67f61c25040000007e01226d62d660a00052000080000009e5f60005820483a40dc12e00069a0000000340007fe2fe61e8148685de13a0001765ae00016201c0007b86727321568764060000000007780004482667422f263c6b20001324120fa0000000840003904bc0000007940005f058c2e87ba74e22e29e02a85c8867f44000005e05be0003761ba39404a76e0d60000000008a000060e5ee0006e47c20005523b631273e00023c00026e0007e667c0000004a41ca0000003ee88419240a2340000002c80000000000ea87850a87481801e5ba0ce32a6d80460423b800036285482e04e3ec6604045d04540d858488042e3b400045e8923d60005d200013856a7a00521127e81b06ec1680002706148605b62744520b40000000000008280002a477200008234086a07683447a06c3de5480005880002d26100000006580000000000000005ea41e20a14a00042a71000025c00000083889400075800045a5560004be0005d489e1501b400086c4fa4c486e2800002b083c0005060385320000008880c80006080c252e3f02c41a264c00000013000008c2d47be0f482c0186360000000000000000000000003242f86487043c07a84ac68a0004f844e8a610c0007383ca33c0664d41ce5440fe7441aa44231e74a5003d021080438e1400d00000000b28982785a80000000000001848b67c60000000000005541c451a37c0000007a400000067400005a18e7f81287ca4a02b665a61c70200021a1e806e5b03440682ca11456c7760000000000000000000000000a07880003b000054c0000001a074c05c0007c43706ca14800082233055a27e2b289a00000a72e3525a22923da07c0008406166940005504ca36c31a3fc28417866651c00062c0000003a200063a48a88e3cc28e0006ba00000002000000035a0e60000004166900000000007ee0862dc43c4de2ae52248c7b634828629c00049e00000085e79260c0000000004e61b626c31600000004c0da84470c00057c0f221868843e5705345da49c2d010e0a400017a82405025688a1106782406a23ae00000051432e3e609c28219640c0003d40006a449600000000042c000000
  | 11 => 0x70884e8640000000000000001708200000000008704905160000c400009843a0002280003fe64200e00038c00000007a0000000000002381f658a1f40b81160561600004645e800084c2988107825ec0000000000000000005c479a0004e011e4b80cc1d82ce2bc00010a6d25620005400000000000000000006520006627de31436a68681c3f44340000003fa17271e24e00000065000000068c0220000ba4620000000000003c65645fa80a1a63925
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x502cda600b0b22405c7801c0181c00010951a2440054a4c0732141ad0000a0c14100004a000003e18002268c00022680ae24bd59e0040000489ce810122301800808181100408400040103f985d07459431006920c980085650c401c4a901c9654c4310071264072595310c50584e87597724c4313d711d89715d4634841185476614634c521006511c98518d314840156190085750c521006855518314461500018e17260021185400040fe61741d165cc00143595190715912052e701cd808c5214800184c825d5630c710006512097558c31c40019c073603624871000685605831976444001a158160c65191100058564c65544644412bc327019464cc51000478a6010dc9314400143597194640c51000417660651cd214400115598194734851000705194641cd21440016c1910cb634811000c7864a87cc52044117b403261431481100ee321d8834852044001c6076d95214811045cf024d844852044001ca076d9121481100078819464485204414d3c298e0d21481100067021f834852044117ac29620d214811024eb06588348520440939c07620d214811045ed0a54834852044117b419520d2148110006d0d94834852044001b406520d2148110006e0d90834852044001b806420d214811052eb020f6348520440054e09758d214811052eb020d6348520440019c083dc921c4110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x32100005283403930a31a6290802815a8194641cd21440011a0d48ca41a429022000e801946420d2148110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x5201b91946420d2148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x94b
  | 6 => 0x94d
  | 7 => 0x94e
  | 8 => 0x4
  | 9 => 0x138b
  | 10 => 0x138d
  | 11 => 0x138e
  | 12 => 0x98d
  | 13 => 0x98e
  | 14 => 0x9cb
  | 15 => 0x9cd
  | 16 => 0x9ce
  | 17 => 0x168b
  | 18 => 0x168d
  | 19 => 0x168e
  | 20 => 0xa0b
  | 21 => 0xa0e
  | 22 => 0xb09
  | 23 => 0xb0d
  | 24 => 0xb0e
  | 25 => 0x1409
  | 26 => 0x140d
  | 27 => 0x140e
  | 28 => 0x249
  | 29 => 0x24b
  | 30 => 0x24d
  | 31 => 0x24e
  | 32 => 0x144e
  | 33 => 0xb49
  | 34 => 0xb4b
  | 35 => 0xb4d
  | 36 => 0xb4e
  | 37 => 0x1449
  | 38 => 0x144b
  | 39 => 0x144d
  | 40 => 0x16c9
  | 41 => 0x16cb
  | 42 => 0x16cd
  | 43 => 0x16ce
  | 44 => 0xb89
  | 45 => 0xb8b
  | 46 => 0xb8e
  | 47 => 0x1489
  | 48 => 0x148b
  | 49 => 0x148e
  | 50 => 0xcc9
  | 51 => 0xccd
  | 52 => 0xcce
  | 53 => 0x1709
  | 54 => 0x170d
  | 55 => 0x170e
  | 56 => 0xd09
  | 57 => 0xd0e
  | 58 => 0xe89
  | 59 => 0xe8b
  | 60 => 0xe8e
  | 61 => 0x1789
  | 62 => 0x178b
  | 63 => 0x178e
  | 64 => 0x138956
  | 65 => 0x98956
  | 66 => 0x94c
  | 67 => 0xb0956
  | 68 => 0x94b16
  | 69 => 0x140956
  | 70 => 0x95416
  | 71 => 0x124b
  | 72 => 0x209
  | 73 => 0x24953
  | 74 => 0x24956
  | 75 => 0x94256
  | 76 => 0x16c956
  | 77 => 0x956d6
  | 78 => 0xb8956
  | 79 => 0x94b96
  | 80 => 0x148956
  | 81 => 0x95496
  | 82 => 0x124d
  | 83 => 0x289
  | 84 => 0x1549
  | 85 => 0x1849
  | 86 => 0x14c9
  | 87 => 0x2c9
  | 88 => 0x138c
  | 89 => 0x138b16
  | 90 => 0x4b
  | 91 => 0x139416
  | 92 => 0x25393
  | 93 => 0x138256
  | 94 => 0x16d396
  | 95 => 0x1396d6
  | 96 => 0x138b96
  | 97 => 0x4d
  | 98 => 0x149396
  | 99 => 0x139496
  | 100 => 0x98c
  | 101 => 0x9c996
  | 102 => 0x98b16
  | 103 => 0x99716
  | 104 => 0xd0996
  | 105 => 0x98d16
  | 106 => 0x15c9
  | 107 => 0x12cb
  | 108 => 0x1889
  | 109 => 0x1609
  | 110 => 0x180b
  | 111 => 0x130b
  | 112 => 0x9ce96
  | 113 => 0x9d796
  | 114 => 0x589
  | 115 => 0x18c9
  | 116 => 0x168e96
  | 117 => 0xcd
  | 118 => 0xec9
  | 119 => 0x150d
  | 120 => 0x128d
  | 121 => 0x12cd
  | 122 => 0x140c
  | 123 => 0xb4b16
  | 124 => 0x28b
  | 125 => 0x184b
  | 126 => 0xb5416
  | 127 => 0xb4253
  | 128 => 0xb4256
  | 129 => 0xb5456
  | 130 => 0x20c
  | 131 => 0x16d456
  | 132 => 0x148b96
  | 133 => 0x154d
  | 134 => 0x20d
  | 135 => 0x150c
  | 136 => 0x18cb
  | 137 => 0xd0e96
  | 138 => 0x15cd
  | 139 => 0x98954
  | 140 => 0xb09895e
  | 141 => 0x9894b1e
  | 142 => 0x28211
  | 143 => 0x29451
  | 144 => 0x29551
  | 145 => 0xecb
  | 146 => 0x17cb
  | 147 => 0x28b51
  | 148 => 0x282d1
  | 149 => 0x2c291
  | 150 => 0x2d491
  | 151 => 0x294d1
  | 152 => 0x299d1
  | 153 => 0x14c291
  | 154 => 0x14d491
  | 155 => 0x2d851
  | 156 => 0xb8291
  | 157 => 0x29491
  | 158 => 0x25853
  | 159 => 0x259d3
  | 160 => 0x24b56
  | 161 => 0x25556
  | 162 => 0x255d6
  | 163 => 0x25856
  | 164 => 0x25453
  | 165 => 0x94994
  | 166 => 0x94253
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1695
  | 6 => 3479
  | 5 => 1119
  | 4 => 49
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (68930+((h/565+packedAt gbK7 (62715+(h % 565)*11) 11) % 2035)*12) 12
  | 6 => packedAt gbK6 (182059+((h/1159+packedAt gbK6 (166992+(h % 1159)*13) 13) % 6722)*13) 13
  | 5 => packedAt gbK5 (70124+((h/373+packedAt gbK5 (66021+(h % 373)*11) 11) % 1786)*12) 12
  | 4 => packedAt gbK4 (3542+((h/16+packedAt gbK4 (3430+(h % 16)*7) 7) % 70)*7) 7
  | 3 => packedAt gbK3 (327+((h/1+packedAt gbK3 (324+(h % 1)*3) 3) % 6)*3) 3
  | 2 => packedAt gbK2 (93+((h/1+packedAt gbK2 (92+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe0f07c1ff07ffffe0f007c288f1f838fe67
  | 1 => 0x7c03f007fe1ff83c03ff0007cd749e61cf3387
  | 2 => 0x8003fff8001fffc003fffff831871f860fc3f8
  | 3 => 0x3ffffffe0000003fffffffe07e007f003ff
  | 4 => 0x3fffffffffffffc0000003ff80007fffc00
  | 5 => 0xfffc000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x943a0300c023215439645051400030a8185663
  | 1 => 0x584a7003520d29184ab540a584349660cb3385
  | 2 => 0x109295480016b59090c6653111811b820dc2a8
  | 3 => 0x41212a95b540000123188ac62e06e005700156
  | 4 => 0x201cce62998c623c00003003bd80007a6a800
  | 5 => 0x63c000c03100840200100c043fefcd50000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefaeafeeaf800feeefaeafeeaf800feeefaeafeeaf800feeefaeafeeaf800feeefaeafeeaf800feeefaeafeeaf800feeefaeafeeaf800feeefaeafeeaf800, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36260
namespace PEqualNP.Outside.L_meta_36260
open PEqualNP.Outside.L_meta_36260.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 3 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 21 := bs0_3_0
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
theorem bs0_4_96 : Interval s0Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 99 := (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 bs0_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 46 := (concat bs0_5_0 bs0_5_32)
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
theorem bs2_2_0 : Interval s2Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 6 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 90 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 2 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 6 := bs3_4_0
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
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 64 := (concat bs4_4_0 bs4_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 40 := (concat bs4_5_0 bs4_5_32)
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
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bgb_4_32 : Interval gbAtlas 4 32 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 49 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1088 : Interval gbAtlas 5 1088 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1119 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)))) (concat (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))))))
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
theorem bgb_6_3456 : Interval gbAtlas 6 3456 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3479 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608))) (concat (concat bgb_6_640 (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832))))) (concat (concat (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024))) (concat (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)))) (concat (concat (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472))) (concat (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)) (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)))))) (concat (concat (concat (concat (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792)) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112)))) (concat (concat (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)) (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336))) (concat (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)) (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560))))) (concat (concat (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 bgb_6_2784))) (concat (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880)) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 bgb_6_3008)))) (concat (concat (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232))) (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456)))))))
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
theorem bgb_7_1664 : Interval gbAtlas 7 1664 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1695 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))) (concat (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800))))) (concat (concat (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)))) (concat (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 (concat bgb_7_1504 bgb_7_1536)) (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefaeafeeaf800feeefaeafeeaf800feeefaeafeeaf800feeefaeafeeaf800feeefaeafeeaf800feeefaeafeeaf800feeefaeafeeaf800feeefaeafeeaf800
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074666 * 2 ^ 32 + 4276811776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36260.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.and,[4,8]⟩,⟨.or,[5,9]⟩,⟨.and,[7,10]⟩,⟨.or,[3,11]⟩,⟨.and,[6,12]⟩,⟨.or,[4,8]⟩,⟨.or,[11,13]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276811776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276811776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36260

open PEqualNP.Outside.L_meta_36260 in
theorem PEqualNP.Outside.L_meta_36260 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276811776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276811776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
