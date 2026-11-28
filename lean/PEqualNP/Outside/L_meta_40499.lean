import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40499.Model
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


end PEqualNP.Outside.L_meta_40499.Model

namespace PEqualNP.Outside.L_meta_40499
open PEqualNP.Outside.L_meta_40499.Model
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

def SBf (j : Nat) : Nat := [7, 4, 7, 5, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40499

namespace PEqualNP.Outside.L_meta_40499
open PEqualNP.Outside.L_meta_40499.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x14f8060020004400000800900c2200300009380000001fe10ff42fd41fd40fd30fe42ff32bf41fe20dc32bc40fe32ff41fe40de32fc40fe41fe31fc41fe21ff20fe30fd42fc32be40bc42fc21ff30fc42fd43fd31fd20fd10bf43ff31fc10fd21fc43ff43bd41fd32fc20fc30bd43ff10fe43ff21be42fc31ff40
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1030000000300000200002d0501848d00000000000181808181028000830300080000060080000200010003808000079d8a800080010100028000808f858100ba008001020517838081030000030015840084821b001d980000071cb00080014f94840ae29a855c534827aa2216750c319faa2413e540cb3a87195b94a319e2a2413c544427aa918db14943b7290213d5390abea6884fd5020aea98813e509027aa898e7550329e2a6435e538827ca1a0cf953319eaa4433e548833884194f14941bba8a413e544c67aa998cf552439e2a4216c524c27ea990cfd51219e2a4653f548427aa8185b149109eaa6659f5350e7ca1a1cf141439ea9e83cc32486e8a290678ca40ce190813f5150e7ea6a0cf940429f2a063cc32c8678a4a1e750d309e2a2653f548c278a8985754f42af29e839f430ca7ca5204f95010cea1865cf420cb6ea2a0cf55310e6190419e53102bca419678cb419f296833e54c827aa6215714d109f2808178504867aa810dbd49309e282835e53d0b3c64a0d714d21d621065cc328831884194754f419e2a0413d5490774a0204f5532096292873e54cca78a890d754c10cea98813e548c67aa3204fd51309ea88815f534867ca820ddd45309faa2213d5190a7ca5a1e7d5232aea9c419e428cb3865204f950219f2a6613d531023aa6205794e21d621665ac5250e7aa818ded4121afa9a419e53d067ca910e7908329f284853d51d0f3a8798670cb41af29465af5250edaa518d7d4d42cea1c639c428ca7ca4214f54e40b6a90213c548c27aa9105bd4943aea9c433f544ca7ca821dd145309faa4659c3250738a9194f55032af298813d540433ca8194f95310e6210653d54cc39ca419678c8409f2a0615e53042dea4885754f41cea9e839f438cb5ca4214f94a42
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40a005410000000440020800c010102108408800000e04010016400301200201d011c318953d068c6250d30a3189438c68e6010832c3150320820c6254c40a398b548ca1d6395310c3d8c5250f0c520c941c550c514c30f6254f4187189531030d4394a318758e5090a1d650c8408b189531021f6354642a5584548cb0e520ca40c3189531028d61108328758e540868e6290832a3988548cb0f53149438e181544c62d6510832a3d94420cb4832141218b18953d070c540c9218758c540824c6254f41c3950328828c6254f418758c54c861d63141418b189544c70c540cb21a3189430c61f658c8408758e54c823561152328318953d070f6254c4093189531028c6250f30a3594420ca2e62d523087195434c21d6315210a3189531021f658cb418759432d063561150208758e544c70d43149308718953d061f6354640
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x814400228338ec629287215c7651083281aec2a064105047250c514c282b88a819041031c96314141818e4b18a90840c7258e54c4206392c72a043039cb6354640
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
  | 6 => 2*((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s0K5 (800+(h % 30)*6) 6) % 50)
  | 4 => 2*((h/97+packedAt s0K4 (4455+(h % 97)*8) 8) % 165)
  | 3 => 2*((h/48+packedAt s0K3 (2280+(h % 48)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s0K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xf03ffffe07ffffffe07fe07fffc1ffffce3e3f
  | 3 => 0xffc07ffff80fe07fff83ff81fffe0f01f3cfcc
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x1105108c412248100594a8a25012915414d0d5
  | 2 => 0x248a29103244942960294454a6412aa8ca262a
  | 3 => 0x42934a2490e904caaa8275113aa40c0d634b4c
  | 4 => 0xb2c74492481d974d34c1861cd39c031bc0db0
  | 5 => 0x8c307871c70e1e7f1c739e780e3188c1ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40499
namespace PEqualNP.Outside.L_meta_40499
open PEqualNP.Outside.L_meta_40499.Model
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
  | 3 => 2*((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffffffff01f81ffffffffffff000ffff8
  | 2 => 0xfe03fc07f007fffffe0f80f80fe03ffff3333f
  | 3 => 0x3fff80007fffffff000fff0003ffffc3c3f
  | 4 => 0xfffc00000007ffffffffff0000003fffffc03f
  | 5 => 0xfffffffffff8001fffffffffffffc0007fffc0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2a186450a1a011c380318d18d1a38b1a055578
  | 2 => 0x8ca9293146ab224d9606a46a4dc4956ab3331b
  | 3 => 0xa95250a26b354496aad048b6e48926b35c3c2d
  | 4 => 0x306362c58dc6891b4d6b6e04891238dc6fc036
  | 5 => 0xc18383060e070e1c718c70c70e1c00e07aaa80
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf0000000faaaaaaaf0000000faaaaaaaf0000000faaaaaaaf0000000faaaaaaaf0000000faaaaaaaf0000000faaaaaaaf0000000faaaaaaaf0000000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40499
namespace PEqualNP.Outside.L_meta_40499
open PEqualNP.Outside.L_meta_40499.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1800800070011424c30010007d6984300ff21ff30dc31ff41ff42ff31de43fd42ff10ff20fe40de31fe30fc32fd30fe21fd40fe20fe42fc30fc41ee21fc43ff43fc21fe43fd21fd43dd43fc40fd41fd31fc10ff40fd32fc31fe32fc20fe31fe10fe41fd10fc42ff32ec21fd20
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x51808202a80820532000007c7000c0001b840000900000210106780050054002000070300000042c000840c0470201cc31886d8a4885794431b6a94215f53486baa6105714d20f3208435f53506baa918dbd4941b6a90819e540c67ea89057d5031af298833c544823aa818d7d5231f2a0843d6510c6eea2905794f40e7188439d43102dca598f10c421af28c876e528433ea8a1e750e40bb288815d540c6e8a29957946319f2a6615d53842b8a2a1f908610e618843d4310867ca818d794f41b7288436c52506dca4205794c439e2a2216d52d07cca210d754c41aea9e857551d0abca790d794c42e7218436f52442dea498d794c40aea98859d540c6bca6105794f42b729061cd43886dca5a0cfd5110b728c433d54cc3ce6210de14141b6292635c53487a86390dd14520e721c437551103c84208790c421cea1a836d52cc6b8a6885755243aea9e815d53c86baa6206750f41bb28e85cd43086bca7084f55031bda82835f53442baa7a0ddd4532afa9a41ce31886daa4185714d41
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x14050140119020102c46150c21a359031086c5640c42187592538421d6595031b1d90310868d640c621a959031086646154830b19863108685640c421c650c50506c46350421e159031087854350421a559031c8695640c421e199031087154354440b818141087465308610
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x681431814108682ba4a610c21215da640c421
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
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/22+packedAt s2K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/54+packedAt s2K4 (2673+(h % 54)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt s2K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/15+packedAt s2K2 (147+(h % 15)*2) 2) % 3)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe07fffffe03fff81fffff07ffffe07fcf8fe3f
  | 1 => 0xff80fe07fffffffe0f81ff83c07fffff2733ff
  | 3 => 0xffff0007ffc0fffff001fffc007ff83fc7c3c7
  | 4 => 0x7ffff03fffffe0000007fffc3f803f8
  | 5 => 0xfffffff8000003ffffffffffff800003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x230a144023820880318a30144716426448561b
  | 1 => 0x4526288a4494511606a0d482892a8c892330ed
  | 3 => 0x8a144d54890ea2aad0496958124d5232c5c346
  | 4 => 0x1c58b1e712283bcd6b6c0c522471e723f803b0
  | 5 => 0x1060c1861c30c3718c718e6338018403b6a800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40499
namespace PEqualNP.Outside.L_meta_40499
open PEqualNP.Outside.L_meta_40499.Model
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
  | 4 => 2*((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fffffe03ff81c1ffffe0fffff81ff007cfe7c
  | 1 => 0xe07e07ffffffffe0f81ff0780fffffff9333ff
  | 2 => 0xff8007ffc1ffffff001fff800ffe0fffe3c38f
  | 4 => 0x7fffe001fffffe000000ffff001fc03f0
  | 5 => 0xfffff80000001ffffffffffff0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc30c40238410a40318a60288e390990c24563c
  | 1 => 0x49108a4490a208a06a0a905124a322549130d5
  | 2 => 0x842554890d44954d04952b0249548ca962c30a
  | 4 => 0x1659e7122876de76b6c18a448e79c831fc03e0
  | 5 => 0x1861861c31871b98c719cc67006100c1dba800
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeac8c8c0c0eaeaeaeac8c8c0c0eaeaeaeac8c8c0c0eaeaeaeac8c8c0c0eaeaeaeac8c8c0c0eaeaeaeac8c8c0c0eaeaeaeac8c8c0c0eaeaeaeac8c8c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40499
namespace PEqualNP.Outside.L_meta_40499
open PEqualNP.Outside.L_meta_40499.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1003dd32ee21ec21de31df32dc31
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x3886210d514532
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/9+packedAt s4K4 (96+(h % 9)*3) 3) % 6)
  | 3 => 2*((h/7+packedAt s4K3 (54+(h % 7)*1) 1) % 2)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x81fffff80ffe0c1ff87fc3ffffc1fe018cfe7c
  | 1 => 0xfe07e0ffffffffe0ff83fc1c07fffffe7333ff
  | 2 => 0xfff800fff07fffff0003ffe007fe1fff83c38f
  | 3 => 0xffff800ffffffc000007ffe003fc03f0
  | 5 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8c30c808e10454031814c0a471d1321884563c
  | 1 => 0x14910111242800a068814408924244a83130d5
  | 2 => 0x28425aa243514d4d0452aac124b5195382c30a
  | 3 => 0x71659cc48a1d6e76b558228247399063dc03e0
  | 5 => 0x418610870c618b98c6633313802001836ba800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeac8c0c8c0eeeaeeeac8c0c8c0eeeaeeeac8c0c8c0eeeaeeeac8c0c8c0eeeaeeeac8c0c8c0eeeaeeeac8c0c8c0eeeaeeeac8c0c8c0eeeaeeeac8c0c8c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40499
namespace PEqualNP.Outside.L_meta_40499
open PEqualNP.Outside.L_meta_40499.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x4000010010010000090c00050021000000000000000400001c60000020c41400800000c0000041000000021000ff30fe43fe31fe41fc10ff43fd10fc40fe30fc20fe20ff10fd43ff41fd41fc30fd42fc42fc21fc31ff40fd32fe42fc43f920fc41ff32fd40fe32fc32fe21fd31fe40ff21f810ff42fe10fd21fd20ff31ff20fd30fa20fb10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x217c5250ef8a2a07e4c310fd280657d5290f788720df94021bf298817f53042faa9215f54e42fc20a413f54486fca5a06fd0040fc28287fb50486faa3215f94243f790c43fb43c42faa5a0df94410fd90a417f54843788520df54e41fda82637e54cc2fea9905f94430bf29e41795010ff281107bcca21fda00617d53487f2a1a0fe54232ae29a81fa42882faa8107ed4141fda0241eb524837aa9195f14910bfa9841f853042f6a5887e95010bf2a421fb54042faa91977d4d40fc21a417c52043b886187e10920fc90a417d53482fca7a0df94d21bfa92617e54106fca59877d0f32be29263f840883da64195fd5031fc106217e520cafaa6205f54a30bea90837e530cafea4087b0c821ee21a657d53d03f6a6905f94c43fd20c417f5348778a890df94431bfaa2437e508cbf2a021fe0c520fd210213e548ca7ca810df54b10fca8663fa210437a84217bd0821beaa243fa53882fca198f7cc030beaa441dd4310ef8a6a17e10010bf29c43f521087f261105f54630fd98241f940042faa6085f94730bea8e873c544c37c8520df94242be2a4437e520c2fca9997e94341f7908437f53882fca998df94910fd28087fa30882fca5887ed0e20bf29c85f9500cb7a80207e50b10bf284617e53042fea2a05f15231fd20821795090bf481885f54830bf296877e50083f2a3105f15232bf29a417e52082bea6a0f70c831bf298857c50507d88410df94010bf28c657f53502fca9887dc8521f690843bf544c6fca9185f54332fc980217e53086fca5a0efd5130bfa9843bf42d07f4a3105fd5110fda0e21fa30042fca518fe54321bca8683fa20083f484905f14d21beaa4837e51d0afca1085f54632fd10a41bc4350b7e8220fe14d20be28a65fb43042f8a8186f10e40fd28a417a518837e81207ed5220fba0a833d54086fca4205f94c31bf29087df4390efca0197e90220bea9c63df438c6faa990df94343bea94217c53c82fea6a15fd4d10be2a4617e51d03bea6a0df54c21fda06617e54087f2a5885f55330fd996217e51082fea4887dc4210bf29e81f940482fca9105fd5230dea08837f5150afea2a1fe15120fc28243f840483f4a9885fd5030bf2a4437f54cc2fea898df94321df2a4657e50887f080185f94a40fca1441fa300c3f040085fd4940bf280637d52042faa9997e90520fd884217a50d07f4a5885f55230fb108435d5390afca8907e90010fc980617c51483de40107bd0a21bf286857f52506fca8985f54342fd106217a50086f8a0995fd4e10fda98217c544c3ba60185f95232beaa0217e5010afca2215f54e20bea9483f930482f8a6105f54f41fc2a0217a51043f641887ed0d20dfaa2437d52443be86185fd5132fca1021fb41882fca6887e8c120df2a043bf42506f2a5885f94640fca80857d50086faa3905f54a20
  | 1 => 0xe544c6faa898de94321bfaa065de5390af8a610fe0cb10bea80637e508c6f8a4a05f14f21fc18441fb20483f681885f15321f928821f841c42faa121fb88120be2a2217d5110ff685885fd5020fd98821f941043ec20887e54e20bf2a641bf4390ff2a4085fd4f10bf294837c514c37a8621dfd4132bfaa6657f504c7f643885f54730be29c417d52902fea7905e54a20bea8443ef4250bf486087ed4920bea9c43f7318c7f462085e94042fcaa021fa32043f2802077cc631fd10221df320cafaa0215f54c42bca90217950086faa321fe48710fcaa621fa53482f8a6085f54a31bca86437e540437e84217e50130bf28883f920843f681205f94421de21e85f931483f287105f94f10dea16837f54043788420fe10f10be29a81ef324cbf085886f10c41fca84857f514c2f8a6907e10620bda8243f932883b887997e480109e2a263de328c6faa021df95032bfa92877f52c437c86207d44010f6a1085f821882faa198fe50230fc18021bc544c6fca420df55130fda14417c54482faa9207e0ca20be28a85de53087f063885f95020be28a87785050f7c8720f754e42fc88021fa52043f4a1217e4c810fd192417e50103bea690de94043bf28481f842882fea710fecc520ae29a83f941483f661885bd4941ee992637d5344278a890fe90d20fc10821fa54482f8a810fe8c520bf29841fb53c42faa3996f151309faa2637850487f643105f94440ef18261f943042d8a4a0df94041bea96617d540cafaa5a05f54420bca84657c54c43baa610dfd4f21ee996637e53d0afaa1217e14520fc190217d51d02fca7106f90e40bf2a2437d53d0af2a198f7d0e30bfaa4417d538c3b8a6a0df95043be29261bf4290afaa7905f95231fda1021f831882dea498fe54520fda8a417c53443f243107e0c120ef19265ef52506fca0187ed4b10fc21c41fb40883f0a9105f55030fc10a41f841043f485885fd5321fda8c417c5050afea6a0f70ca31be2a2637e51d0ff642087e94f10ef988637d51d0afaa1a0df54620bf29883dc53486f8a9907e88710bf29c817d5210efaa020fd50441bca8065be42107f281885f54432be2a243ec52507f081885f15032fd20081f831042f0a098df95132fc908217e51883f240885f14e10fc210217b5050fee8320fecc220be2a421f932482fca818fed0010fd20261fa50c86fea9195f95110fc218217e52cc77a84a0fd8c431f7190653d548cbf2a010e750c43bf28441fb5050efea8907e8c310ee21863f943482faa1a1fe14e20ef21887fa5010bf483885f55210ee21c637c538877c86a17e88620fc28443ef524c7f0a098fe0c920bf28887bc43103ea6218f78c831ee988637e538437e8621fe15310bea90637d54483f481185ed4141ee990657d51902fca1a0de54042be2a6657c54043f684905ed4131fd98
  | 2 => 0x2070000188200000000000080001032278060007c6382a058000703a018b41f8000007a0b0de0100600012098060480001802010040c82a0103201016a28000400e24800008040280211392060540000a09066000000a0020f0142f81e0d01a00874060120780259006200445617a108421b038048000202e0f83000008028780880a258520700001002138800582c018240100248876000000806e0001a048300380280800278000112a0c048060340181c0d0024f8140000000000758001c8ca0001e128080d8002d80e0282c0c0b040062090000602a0396c0586011008048180000407092168000001e098020300401028038000484e9b8000100a610500a87a290020000e1781e0d2200101c31000000260400610018039740180a4501002002178060c01c180080000e0b8480d000000000002c05000020060282e0081c0000810aaa0a04a7a8000184e010000d002020080280a9d807400621a1fc108021400800808075f94241bea8463be4350efca8187dc8621bf29e43fb20882f8a7885f14b10fc28c417d54087ee20085f54840f619443fb32882faa7085f55320fd98e21be4250afaa910dfd4520fd288217e528c2fea090df54610bd284657a50082bea690f7d0d32fc98e217e52042f8a4a0df54e32efa1a87f954882fca3995ed4810f7a1485f641107f0a4086f90140be2a6637e5190f7c82a0dfd4532bfa82837e5410afaa921fed0410bf28665fb53882f8a0a1fe50710bfaa6217d50906f4a0197ed5120fc900417f548877c87a15f54f10beaa0637e5290efca5195b14931bf28c437a5090afca021ef90c41bf29c83fb40503f6a4085f94e43bd28663fa43c42faa190fb88521beaa221fa31c43be6498df14d41fd196215e5390bf664085fd4142be28243f954482bca610df15031f690041f953043d88510fb90842bfaa043bd54086bea6a077ccb31fd104217f524c7f284905f94641beaa6637850506fea998fb14931bea88617e520c7be8618df94a42fc186217e5210bf480905f94821ee21c617c52843f440087dcc531ae29a43fa508cbf4a6085f15020dfa0c83f850506fca990df15132fd2a4417d52cc6faa918df94630bf28e417e5190bf081987e48310ef99465fa50cc7f682905f55310fc98c417d53107de6410df54232bd28421de314c7b8a6a07bc8220bfaa261fb318827ea8985f14131aea98437d53083f420085f55132fd98461fb10442fca6185f54a21fd90021f953482fca8205f54032fca0c417d53903f287887e14b10bea8885fa50086fca5085f15330be2a4417f548c6fea5087ecc920fd98261fb54c42faa790fbcca32bea9687df308c3f265887e90e20bfa9a41f953c43f0a7887e8c620bfa82877d51103f6a110fe8ca20bc28a417e518c7f043885f94432fc988217
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x954086ba6414b109e18153d0b1d5410c31d694e500867b6055332b318d210863f6454e21aed9121882d963909209e588504c6b8644c7109758f54c427a60148109e983530826f65480209e980530827a65d0520aed9131c423f6454d10e650c430429e6390942c795253086f26114c109e983540cb395454021a7992328c6b9648cb108f59252cc6db63486209e58253886d86350710bcd85544833b54141219e5835150a5d63150109e58354cc63e65151309d185544827b65884109e597200427b6550620ae590218836960149419e99442482796094b419ed815190e9e648c9329ed9543c427a60d45429b594320867860546429e5885050e786550e208f593538427a6588110ae99232c42786550d20c794f4290a9f6550c439e59443882796094b439e580540c63e64150219e195414826e6215031d6d4e53c439b6050c439e58252442da63148109e58353c871f5414d21d6d4c50486786054e219e195318827b60546429e99443882986050c438fd954210ab864484108f992534876860d4941aed9130883994310d20ae59353c425d63d53209e18153106d86350220bc987530433a54540219798f54c426f6255131d314f525065d6510c319e195314827965cc520f8484210435953540219b58854042d86350130ba189318834c53149419e195418827a60d4543da54a21c423d64d4f20ce152404c2f261d4b108f191538825d6594c21ae99021882776550441cb14b425063e6414e20ce951508ca7b6550d20b658c218833954542329b58b5384279601533297d8d5488679650c0109e596400432c5290541ae191300423e64951319718d544823c6454c109e982548867960150218f994544c677654c431c754c43102f261d53109e181510ca7b6254043ba58841482ea6290d20ae19153882b864485209e58a5010e3d64948329e994434827a65cc5209758f54086bb6448410da183524c76a50480209e99632c426c6255131ae580439023e6414b10ae99053882db6348410ae59021042da63087109e98054cc77165944108f992520cb2d54d08219e1815190e9e6390a41d654c53482eb62507109e9825210e796095131bcd8553482746155132ae592328826f654c832ae191318827965c84109e5805350a7962944109e596200427960d52319ed81544867a6014c219e9865010a7a60149319bd89544867a6015332bc987520427a65d01209e58b505065d63d50209798c54882f3614c8109dd9510042b8644c1209b98b548427a6014d42cb153524c67960152329e58053086bb644c620ba18941c425f63551108f99052042786154232b618d418827a6508410dad48504c6bb6448520ae992328823d64d4f109e597400c31c53901409e58354c867960150329e59632c42bb644c0109798e52d06d963150109ed95310423d6414c21
  | 1 => 0x435a534c310ae593518827960d52328f593530874c6254c219e1855090a7a60d4f219e98053c863f6454c109ed95100426d6214c109ed8154443705188520a7191310c67960149319b1895110e7965108109e594400436b52141419e582520c75b43141439e181540c71d5454c21b698f518827860551329e582528c76852d4141b698e424827a60149419e596320427a60150219ed9521043986050c43a75924310ed86348410cb152214867965cc410b6d8d40042db63504108f596421071c53509419e982529065e6395121da98052506d863502309e594210427b6054e219e98254487685214141ae19130c433854141319e58254886eb624c5209e185500cb5953940219e19543042bb6448710dc145214827965d05209e99432c429e648c831ba98b434825e63d53209e195304827b6054743ab18941106b86454d209798f54c871e5454c219ed81544c67b6055221b6d8d404833954100109e983530867a60d5231ce952508ca7b60551309e5825290ed963d5310ce552508cae962d0d20a7d894310e7a6510b109e997418823e6495121b618d21482786055131b6d8d21c427a60952319718d548876852141319ed815110b7051d05209e98354c86b96408710bc98753c432c5414931c7550430c2db6350520da54a210431d5494c21cb149425067b6054d109798c520433b54953109e195404c27a60150309e5944348359530c010dad4920442e96294d20e650c438823c6454d10cbd50524c63f6454d21c7150534867860544439798c540867b6054f429e982539074c528c531a798e421067a6015032c754c431065d63150219e583540cab864486209758c548831f5410e309ed8950d06796510c109e98252d0ebb644c3108f993530835853d4121d6d4f50506d963152209e596520426f62544438f59353082776154d209ed81531074c524c931dc987520427b6550c109e980548cae8624c710ba988530431c544c931b618d40c431d5310f429e596300427a65085208f191510ca7a6590810ba98854042bb6454520ae99021c427a6590130da980524c63f64544329e9865010ed963908109ed8152442eb6255120b658c21c427a6194032b6d8d514835b5314141aed91530423e6495130f8484218823e65151219e994324831c53d0941dc98752c42e962152209e58053c86d96314810d354f32086796095110ae590530431c53905419718d54442da63d53109ed95318833b5414131ce150504863e64d4e10ce55040882d86354520dc14431482e96214c10dc986510425d6510c30ae19151482796590b109ed95438836b60d4941da54942042796294341ba988314823c6454e218f59353c87395415120dad4b504c63d659502197994534873954152209b98b53843695248310ae191308827b65505209e5825210ee96290d20cb18
  | 2 => 0x6314b109798f540ca3d6494d21dad83524c67965d04109e99442043385450130bc98452042ba648c810d694e5090b3a4314143b618d414827a60d5232dc946218831c54cc9319e9825290eba64148108fd954310fc9320c9209e996424831c54d4d21b698e42882b8644c0309e58054c867b60550318f99353c42796508010a71814310e796510b10bcd854204279650c8109e58b504c63c6454d20ced53504866d62d5331ae592324835853d014097d8d544c2f061508108f19153486d86050c43b618d21882d863551209718d54882786055221bc185320427a61d4810b6d8d54882d863552209e59443c42da63150109e9805250e7a6194232dc945218831f5410e31ae992324827761551208f99252cc63e65d0941c7953328ca7a658c8109ed8151d0a7965d06209e98054c875953942428f59052c425e6394d21ba58b548827a658c9209e982528c63e6414c2197d8d544c6eb624c6209ed95410427a60d453297997324c67960951219e181544867a60150209ed95200825f654c431b658e42c433960151309e98354cc71f54d4d219e582539075853d4141d3d4c525076852d41319ed81510ca5f654c030c7152304c2f26115310a718d401026d62150319758f52842796214141ba58b53882b86050c43ce55250086786054742b658f51882eb62504109798c52c42ea62105209bd954210ab964148109e58054cc6796294331b698c210423f6454e209798f540827960151329b58b540c2bb6454e209ed8151ccadb63502209e195404835853141418fd9152442db6350620e610c400c27960d4543b6580438c25d6395121bad8941482e9620c5209ed95300c27960d45329e982538865d6394b419e59642042f16594410ba588538827a6114143c7d954310ee862504108fd9541106796094b31ba58a54483585314121b618d401029c63504419e181518cb595314c109e982544c65d6314b10ae990530435953542429e98252cc6db6355010dc147314826d62d521097d8d52442cc624c4319e1855010e7b6054443ce95140c427962d4143b618d54042786154042e650c43c43695288210bc1855348359530c2209798f528425c6354442b698c214827965cc6208f19152442f261d50109b988548c2eb6254d20ce153504c7596014d409ed95401025c63549109b18953442d96390a20bc98452c426c62551109ed8950cc67960548109e18151d0edb6355120b698e420425d6314810a71854310f7051105209b9885304279650cb10ced53504c67860544429798f54842756115032aed91534827a65c85209b988540425e65d0d32da54821c42786550f10ce15140482e862505208f593528426e6295131bc98453c43695290810bad8931042796095231ae19121c427a650c810dad4b505065f63551218f590530425e63d5021ce550540
  | 3 => 0x4000010040440f00001034400801b044440600000019044110301517e3e000071f8010a8011140920000030040000808c29044010480c00000000db00c49065b85cc000505643c030000d0100900c0008420008290623a0a41b0a407024000d000018480201101c0600404000020000e008010100000019014721d41407404000040200b01405008360481104400054030dc110041316001031070245120c074fc000a4040b819090131f805810015d0000040800070088000c40200c2a35c2b1b80701007014040040311d4b00c1c0f074014000100a0000c0040009c010dc050080a0f41b00405074040040904012004042f81b004580141f0300b014000000338c0100000010091e40000400048062982606c130081404c05004240040f0100b030010041c030270400002c00008e310c04068000480100014010690301701c1f050910101600c12064040540102cc4004290640301c8f2380012861000010401000c000bd1c02d6601c07104490265e63150109e9875050f1d5410d32b698e42c436b6254810cbd53524c67a6194242e650e5010eda63152209bd89534427a60d5021ea50842482766115032d6d4f504865c6355121ae59021482db63485209e98252d067860547329e58252906d86350010ba18931042796014941b618d404831d5410f329e582534427a60948419ed81534865d658c831c7152314c6ba64084109dd85544ca6e62d53318f99353c86ac64484219e582534866f6254d21aed91304827a6094d219ed9531482ce62d0d328f59052042eb624c710ce15350486746154d20ae99353c427a65cc120ce952500873854cc130b6d8d41c434f53d49419e18154cca7965100309e980540c63f6454d209798c5308769524c81097d8d544823d6414e209e5805250f6b6254b109ed81544ca3e64d4a10d654c538835a5354242bc18554482e96215010bc984540434c52cc9319e583540867b60546329758f54c86d963084109e99731882e8624c52097d954310e6d62951318f993530865f654c832a7191300c27a6094831b618d21c427a6510f10b6d8d40c427965840109e18153486b96414e20d694d50086ba64085209e983540827960d4c21d614d304826d65108218f99053042b86454c109e58252106b8644c4109e994430439943540439e99642c425f63550109758f54842b96414b1097d8d5110a6f6548421da580524c6da63086209e19520443984390230bad8941883695208410ae59232042bb644c4109718d54042ae6290d42ae99351882b8644c5209e980544ca6f62551108fd9540102d86350410b698c52c425f6355220b658c214827a6014910ba189418836952880108f99353c826e62d5030da54a32042776548421d314e214866d6215230aed9131482d9
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x10d0001c60490173c12861cb0a204a24110cc30a831a80905187550c434828dbaa8621e21589c76254b10a30e6aa081105c073484210428c382a621883461d15314e20a30e8a98a6085507154c5348324b1aa521021865944310030c30c929a618851471550434ca4cb90c0a1887461d1530c010c52c8a94640851870550430c730b10a218a41865915314c10a34e7aa4a988649535885304318320a290a41261d943940438d2e432a86085187550c4388330b10a220a419418c5148520a30e0aa0869951a70d50438c70c2a0c6a0261461cd5415220c30c829a60905187454c534828c39aa82a021865954310e20c32c8a98a71053071550544830caa2c62a441869506350310c32a8b18a8085187055043cca8c382a621e85261d94354043c52c8a9042085187550c4304314aa2c42a0211c1c56510d20c92c6a90420851873550544824d388c0a1887681d12108410c32caa18860851a74d4e53c428c39aa820021461d1530c220
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x8889821d94394043909821d54310c10a088454d6214c10818875954310e20a08835516215010818875954310c10
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/63+packedAt s5K6 (704+(h % 63)*6) 6) % 44)
  | 5 => 2*((h/288+packedAt s5K5 (21627+(h % 288)*10) 10) % 801)
  | 4 => 2*((h/295+packedAt s5K4 (29678+(h % 295)*10) 10) % 781)
  | 3 => 2*((h/25+packedAt s5K3 (2744+(h % 25)*6) 6) % 56)
  | 2 => 2*((h/2+packedAt s5K2 (360+(h % 2)*3) 3) % 6)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3f01ffe03ffe0e0fc0fc3e1ff87fe03889e7c
  | 1 => 0xffffffffffffffff000ffffffffffffc0fffff
  | 2 => 0x3ffe07ffc0ffffffff003fe0ff83ffff0e38f
  | 3 => 0xfc00007ffff000fffffffc000fffc003ff03f0
  | 4 => 0xffffff80000000fffffffffff0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x5a94c36238a255e02f42e0f193c6721b888e3c
  | 1 => 0x82144044904800500054522248884a80334d5
  | 2 => 0xa0c289289069146a5550025489523951b0c30a
  | 3 => 0x328b16512241c6b39a69a8010e671062dd03e0
  | 4 => 0xc30c1861c38e18dce38e3399c00421836ef800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfcc8c8c0fcc8c8c0fcc8c8c0fcc8c8c0fcc8c8c0fcc8c8c0fcc8c8c0fcc8c8c0fcc8c8c0fcc8c8c0fcc8c8c0fcc8c8c0fcc8c8c0fcc8c8c0fcc8c8c0fcc8c8c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40499
namespace PEqualNP.Outside.L_meta_40499
open PEqualNP.Outside.L_meta_40499.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa28214004000008904001ffd5001fd3100ff14005fe5200ff04001fd21007f88405ff21007f4c007ff53017fc8003fc40017f90801fe41017f8c805fc4200ff94007fe53017f08401fe4301ff54805fc52007f10407fd5100ff08001ff4101ff14c03fe2000ff90003fc30007fcc407ff51007f50801fd41007fcc801fc43007f44007fd50007fc4007fc5400ff84007fe51007f8c401fd40007fd0c01fd2001ffd4807fc5101ffd4001fd43007fd0007fd54007fd0801fc3101ff95005fc32007f4c801ff3001ff54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x846202ff10942007fc86a10c7fe50cc81bff21e601effd4d3100dfec288017fd6544037fea966202ff149211b7fca7a100bfe5248003ff1862000bf58043017fe851080efc6548079ff2928635ff14342037f8cba101bff54d04057f3168001bf18043005fec890003fd644804fff2028201ff84340017fe4099003ff644840dff3168019ff54431007fec0a189ffe3050401feb166206ff10e410eff8a4988cafd65cc801ff3206205ff54d10015f8c49801bfc62d0c077f3288217ff8c03101dfccba1003ff43cc829ffa9a4200bf98d21017f84099093fc521040ddfa08820aff9093013ff840a081bfd6110c1bfe1866200bf98d1006ff8c39806bff538c41bffb2c8601bf1813203ffccb88002fd63d0475fea948639ff5404300dfcc0a1802fd628c4017f30e8600ff10f1014dfecaa0833fc42cc0017eb0e8401fe8c3300077c86a181bff651040dfba0c820dff10c31007fc831880bfc5250801ffb262000bf18d41007fcc6a101aff6510c5fff2826406ffd0d40007fcc398002fd63c401bffb10620bff5513005ff8a898013fe4244069fe28a8400ff8c531037fa842086ffd51cc401ff994622bff94a41015fcc5218fbfc1090c09ff1922000ffd8d4014ffaa6a0803df32cc417ffa8a6006ffd064104ffea890003fc418c401ffa1a6402bf58b320377ca9a009ffe505043dfe32a6200efd913110ffc619887bfe534c401ffa1a6200f78c53115f78852086bff508c4057e3106202bfd893202ffea288023fe52c4081ff1068603bf9954318ffc819904ffc304847bffaa2861cff1013112ffaa420803fd4348031ff2906219ffd503100dfcc018837fc300c401ffa0e2000ff58b101d7faa321817fc5444001ff9968000ff5933002ffaa888003fe6390403ffa86800eff1473006ff8ca188bbfd50d047dff184860dffd84430e7f86098803fe644c403de2028023ff04041007fc62a001bff4350401ffa086203bf99621007fe8498002fd644c069ffa9a8400ff10730087fca6a0037fe53cc81bfe21e6206ff10b41017fea510803fd418c44ffe282821bff54331217fea5a182bfc624c003ffa028002bf189430a7faca90803fd328c401ffa122000ff50e41067f8a598007fe4050003ef1866000ff99110037f88421806fd60d0063fe2866441ffc8743007fc8290002fe6190c01feb066402ffcca21137fea92085bff5088401fe30a8623ff8c041007fac099007fe1044069feb2a8401ff48310007fe8398802fd644c4017f31e8002fb1094200ffc209801bfe63d000fffaa6203aff99643107b86518807fe20d000dfe2068400ff4cb40007fac518897fd511040dfe31e821fff88231007ba659881bfd61d0c0d7f3266401fd84110005fac48800bff2048445ff2966200bf5933217ffc8099007fd50480077f32a8236ff94742
  | 1 => 0x7fc515042dff28c4203bf1953006ff8ca21863de320c40dfaa088202ff083421a7fea8a1003fe434c401fe990820fff1894011ffc4020803fd31c400dfea08820dff1803107ff8a4a0043ff53500077e32e6201fe0c130017faa490037fc65cc83dfea826200bfd8542035f8c898807fa10c4053ffa9a8202bf188430077e8320803f7314c413fda82400dff90c43007fac4a190bff51d0c1bfe2986208ff98b10177faa3a0803fd310c40dfe2a68606ff55343167fc61a08d3fd5050871ff2908602ef90b42107fc851886ffd65cc41bfe29c8602ff8cb4208ffc65a0037fc62cc041ff1946206ff594411effaa4a1802fd6210443fe086620effd5330017f884908dbfd51d08017eb1e8000ffd8d42017f8a499003fd60cc437ff2a66200ff50f30147f8a4a080efe65cc801fea148225ffd48411d7facb21807ff3048067ff282842dff94b41005fec0a0807fd304404dff32c8201ff0c140007fe6290807fc10480057f3166230bf59532037fe87a10c3ff534c801ee21a6402bfd914200df8c110837fc30cc805f71966400f7d0e310d7faa918803fc644c80dff2168026ff54a41037f887a086bfc548c41bfe32e6016ff54e21037fec1a1003fe43484016fb1a4240ff84343007fac398002fd634840dff2a48600ffd854001dfccba006ffe65cc401ff98a6209ff54520015fec4a1007fa40d0017feb2a6006ff99740007fcc999037fc53cc401fea162007ff54b1000f7c80a006bff518c41bffb108600ff5083100fb86098077fc424c415fe1926006ff58f40007fc8398002ff6250417ff28a600fff9894000ffc6090002fe61cc8013eb288201fb881200cffaa4188bbff53d047bffb2a8602ff90a21037f8a9a001bfd54d000ffda862001ff10130137faa32084bff51d002dffa8c4206ff98b41005fec0a100bfe328847b7eb2a860aff08530035fecba1817f65144029ffb2a4206ffd0b401dffc60a181bfe6110c59fe186822aff0424103dfecb88007f410c400dffa1c8206bf99110007fe851881bfe5410409fe1922006ffd87400b7f8a91081ff551c400dff206842fff0c132015fcc42181bff5410c037f3048242ffd4343017fe419901bfd60d0403fe2022002ff0833205ff8ca98003fc434800bff28a2001ffcc31006ff86398057fc60884077e32a6404ff0851000ff8218805bfd5488401ff21a8627ff0c141135facb20803fc4148403fea866000ffd8241037fa87a0803fe6350441fe3146206ef10c410a7f8a290837ff31cc001fea166200ef90e411a7f8caa105ffc100c453feb2a820bff54d3000ffca0a001ffd51c40057e3148200ff1053100ffe40a007aff654c451ff9028201ff081400affc211080afc628c46d7eb2e841eff14531007fe82900f3fe6250c4bfe2988200ffd8141035fcc98802bfe324c03fff0
  | 2 => 0x421effaa2a181bff65d0477fe1828606ef95043007fe8698003ff644c43ffe304623dff19543005fac9880c3fd504c8077f32a801dff94931017f8a5a101afc648c405ff2924200ff0c540007fc82a08bbfc53d0447ff0808206ff95241007fac2a1802fc6350001feb1c823dffd4943007fe82908c3fc514c801fe9962000f74c93100ffc41880abfc6090401feb0a8400fd4c431037f8c1a1807fc10cc00dfe21282039f99441007fcc899003ff32104037e3046225ffd4041007fe8298803ff434400dfe21a8400ff9864306ffe65988dbff53d0805fe216641aff54e31037fcca20803fd41c4057ff90c8212ef553401cffaa22181bfc40d0c2d7fb2c4242ff94743005fec099037fc64cc001fe9906201bf983310a7fcca9085bff658842fff1006226ffd4a41007fac49806bfe518c453fea82820dff1833220ff865a1823ff21c4001ff98a8010ffd9540007fa821880efe654c803ffa026006ffd974304ffca890002fd6190c01ff18a600eff547301d7fea12182f7c654c003ff1866006ff109401cffaa421853ff54484057f3168200ffd8a31217faa7a1863dc320c401ff18a2002ff08621037fca8a1807fe404c0017fb266000bf185401aff861a1006fd60cc001fe98a4002ff48520007fc8699003fc614c0017fb1c4206ffd97420f7fea898863ff210c403ff2022000bfd8543107f8431881fff52c4001fe3224200ff50d21127fe4220803ff6250c177eb2a6006ff90b430cffea4188cffc605080dff32e8200ff90d4000df8c1a181bfd42d04017fb024200bf583320077ec8908abfe3090413ffb2a4000ff4cb3104ff8a690087fe20cc401f63126202ff9494201df8cb20807fa1048001fea1a6209bf5952000dfac188007ff4044001ffb246200ef50c4306ff8879800bfc424c87bfe29a860bff94d30007fc4298003be4350801ffb1c4237ff0404300ff8a098037ff64cc801fea0e6202ff0ca21037f882a007ffc408c40dff3008601bf98131097faa7a0047fc21d0005fa10c4205ff94d10167f821a0807fc40d0001feb028400ff18d2000dfcc9a000afe63cc80fff2a62002ef109421f7fc41218bbfd52d04737eb288626ff14e41097fca3a0047fc32d0045ff90e621bffd4b31007fc86a0803fe64cc001ff31a4002bf98621007fc8290842fd655006fff180860dffd8043007fc4288067fd650c421fe28a8001ff14110007fc8298857fc4088405fe2966400bfd9132005fec69000afc62c4001de21c8241ff8cb43007fac0188cbff53cc819ff2966001bf18243007b8c69080efc65c4001ffb1a8200bfd813102dfaca880affe6290401feb106200ff0c521007fe839801ffc53c400dffb16823fffc8643005fec9188ebff5290c33ff2a06200ff487100cffcca18803dc43cc829fea824202ff50920017fe41a10a
  | 3 => 0xeb2e8600bfd8d21037fec7a100bfd4248401feb0a8003bf9954214ff8caa08dbfd50d0835ff29c6202ff08221005fac020807fc304c03dfea926200ffd0e31037de84a1007fd4048085ff29e8601fd843100f7faca98803fd424c401ff9948200bfd8d4000778c890803ff420c4077f32e600eff953301fffc852181afe6410c37feaa66213ff041211a7f8a6a1006fe601040dff206863fff8ca43007fac0a0803ff6244005fea92421bffd4731017fca49901bff43d000d7f322402bff18a41147fca4a08e3ff2110c0dfe2a48615ff9422112ffaa62081bff62d0001ff30a6002ffcc92000ffc21880f7ff5050c0dfba0a822cff88341037faa820807ff5048001fe9968206ff150411d7fea32181bdf4390c67fe0828441ff94b43035f8cba0003fe64c400dfe32e8032ffd5332077facb98003fd6250003ff2068000ff48730037fac4218e7ff5210c75feaa4861fff902310bffc2018803ff4388401feb224241ff08743207f821a1803fd31cc003fe1822000ffd8532005fac690003bd42d044d7fb2c8200ff50f32037fe82a0873fc104c47dff0848606bf19310037fc8420803ff42cc401feb1e200dff14f30127fc64208cbfc51cc877ff30286039f19530037f8c3a00fffe6290c05fe216843eff98243087fea8a0003df318c401f63128206df5944109ffc609086afe610c401ff3224201bf982430a7faa2908f7fe6550c037fb228033ff9814200ffe409800bec4288401ff18e802dffc8741007fa86a0007bc40d000dff21e8426ffd4241035f8ca2081bfd6210401fd8822002bfd8d32007fa829001bfe6510c01feb16600aff98930037f8c3a1803ff624c005fe9924000bf18530007fac6a1006ff6050043ff0866206ff950430f7faa2988bbff52d0401ff9962001ffc81100e7fc6098897ff5110437ffa866201ff08130187fea899007fe2048001feb0a4006ff58b4100ffea188037fc620c401fea1a6402ff549421dffc40a187ffc508c4017e30a8400ff10d21007fc43a0003fc635080dfeb06843dbfd9543107fcc5188a7ff5450401ff18c4212ff94f4006ffec598003fc614c875df2a48603bf19531005bec6a0803fc434c41bff21e640dffcc831175facba0857fe4088401ff20a8000ff50b30015fcc518837ff60cc403ff2826032ff54332015fec490807fc204401bffb166201ff14340037fe842080bff2148033ffa806200ff50d4101cfccba0003fd435080dbf32e8001ff5414000578c89881bfd4310c01dea088236ff147421e7fe42a181bfd63d08617fb2a6400fbd893106ff8a62181afc6448001fe324622aff88241017fea490083fc328c403fea062027ff18141037fcc1a085bfe538841dfea966000bf98f4119ffc60a1003fd329040d7e32e8401ff941100aff8a11081bfe54d04077e32c8634ff545
  | 4 => 0x3fd4250005ffa924206ffd8c41007fe62980fffc2190c33ff2886202ff5093200ff02088003fd6190c4dfea9c823aef55243137f8cb20823fc62c4013feaa24007ff19710017f8a51080afc62d042dfe32c4202ff94b42007fac09888bfe32cc41bff9966001ffd4330037fe85a0803fe434c079ff2128634bf595421277c8420877fe624c42dffa9c4200bfd8910007fac8988f3fe3250c63fe0866427ff98141007fe6288002ff624c003ff1828002ef10b42007fa84a0827ff51480037e302862cff8434100ffa81980cbfd51cc80bffb2a2009ff15120007fcc91880bfe2050803fc282402bff90a41037f8c7a1002ff63c403ffe1846206ff151431effea2a188bfc21cc40d7fb2e8406f7d0d43027f8848800bff2150801ffb046200bfd9331007fac899007be40d000d7f3246207ff54f100cffaa618807fc1050027fe3024200bfd922100ff861a0037ff6510c0dfe30e8400ff4cb3010ff8819886ffe51cc47bfeaa28606bfd97400a7fca890803fe434400d7f3226201f78c13015ffc652082fff654c063ff1866400bf58b43075fecb9800afe6250005ffa124010ff54540005fac8188a7fd515040dffa0a8001bf183410f7fca8988a6fd655040ffe2a62029ff5494100ffc4198002fe63104057f3106220ffc823105ff8a298057fc3088427ff302422fff04132177fea1a0803fc414c00dffaa68400bf59331037fca8a1037fc3290c11ff2162006ff597431d7fca321827fc6548001f79926406bf19031047fc6588103fe50d0c05ffa928400ffd9221057f8a49800efe6548001fe98a4200ff507301cffea02189bff519040dffb2e8001bfd81200a7f8a69089bfd549044ffe082820dff10f32005fac12083ffe5250049fe1908234ffd95420fff8411881bfc4350031ff1906200ff105100077c82a080efc655084dfeb2c8206df99441187faa299017fc514403dfe29a6200ffd853000ffc209001efd65c4033fe2a06207ff55310007f8c69086bff658c4017fb162006ef95341067fe4398003df430c4057f3126000ffccb4117ffc609901fff51c4037fe2a6620dff19731007f240880f3fc6250c37fea9e621fff94231157fcc120802fd6388433feaa06201ffc834005ffea69806aff658c40dfe2008200f718d4106ff8c3990effe1050c4bff2888204ff14910077fea598007f850c4003fe1068019ffd4431007fec890006fc604c40fffb2e2000ff58941017fca599093fc2110401fe21a6400ff58732015fcc5a1803df324c403ff286800dff18243117fc859881bfd63d04057f3166000ffd8221117fcc5988abfe1090401feb1c4200bf58c411affca1a1077fc624c401de21a8406bf19741207f8a1a18ebfd5390c51ff3128205ffd4d10017fe41108dffe2010c01ffa16200ef754f30037f886a0803fe61500857
  | 5 => 0x81310077a84a083bfc54cc0217fb2a8001ff4c120037f881a0837fe530c41dffa8e6002ffd0942005fec6a101bfd6310409fe312202eff94741007fe6318802fc63c4017ffaa26006ff58041017fe4299003fc318842ffe280623eef1024315f7c8520802fe61cc085fe28e8600ffd0b3010ffc8198807f820480017fb1a8229ffd4941035f8c9988cbfe54cc81bfe3108602bf18a43005fac52080bfd52d0841fe2146200ffcc740037f885a0002ff644840bffaa22028ffc85411cffaa621807fd204406bfe0868400ff50d30007f8c89801bff431040dff3108233ff84142087faa4a0016ff6544013feb2a4000ff98543015f8c42080afe64d080dff3008214ffd41210b7f8a310803fe438c4037e3066406ff90041017f6409000bff3248401feb1a8206ff58043007fac09082eff654c005fe10a4000ffcc931007fec888002fd6290c7dff204863abf98c430f7fea09881bfe545000dfe2a68206ff90843207f861a181bff60d040dff2168206ff90f40007fa868806bfc518c45fff302640dff94f31007fe6310887fc50cc483fe296860dff14f321e7f864a181bff6010403fe2024009ff9452006ffca721837ff60cc801feb028606ff10143017d842908a3fc6250403fea826003bf19732217fea7a1803fd215000dffb0e8435ff8c342017f8851081bfc41d0001ee21c622eff54f41005fec8188bbff51d04017eb1e8416ff99621187fca899003ff63480297fb2a4200ff4c5401effca2a1807fc40c401bfe1906200ffd8e41037faa82181afc644c87dfe2848600ff90e21087f8a6a001bfc5410c03f6102403cff08543005fac998007fd30c402ffe2006200bfd93320effe4298803fd4148431fe1086200ff9051020ffe41a181bfe5450405ef1926406bf986410c7fc841880bfd524c805fe992422dff8cb41005fec2a001bfe63d0805ff1024200ff0c530097f8a3a001bfe62d0c1bfe32c8606ff18342077bca7980affc329044dff28c8201ff5411011ff8a02086eff65cc401f7b128206ff988430a7f8ca90837ff61cc001fe9926200ffd9130187f8a699003fe644c00dfe2048201ffc4110107f8a51880bf721484017fb0a6007ff94710087f8caa001ff651c407bfeb2a8603bf19621017fa859901bfd54d040dfe21e8406ff50f42007fec4988affc2190401fd982601effd4931005fac3a00a7fc5350401fea0a6200ff1062104ffaa690006fe63cc023fe2968002bf1894012ffca620803fc3144043ff306621eff995310077c87a1023fc32c4005ff90a4205ff9951006ffec121802ff614800dfe2048614bf59521037fac5a182bfc424c005fea966406ffd8743037fe852080bfe3248025ffa9e8040ff083431effaa6a1823fc21c400dfe2a48202ff9092000df8c020802fc614801bfe3008637ff8404306ff8c999
  | 6 => 0x3fa0822002ffd4b42017f842a100afc6244005f790c4200ff58d20015d8c4a0843be5450001ffa0c4202ff8c92105ffaa298003fc63884017eb224000f7d8d2100ffe6088037fc3090c1bfe1966006bf192210effc8498807fe50c400dfeb2e820dffd8643167f8a1a0803fc648845ffe3026400ff58d21037f8c020877fe324c401ff18a4021ff9433100ff82088003fc31d00017eb044201ffd414000ffc8090007fe304c02fff280621affd523102feaa288003fe6388401feb1a8000ffd8d10007fac498807dc30cc003fe206601eff15131135fcc2208dbfc53d083dffb2a620eff947300f7fea29881bfe63d0477ff2028614ffd4521007fec2a1003fd438c453ffb2a8200ffcc940017d84399007ff404800d7e3224206ffd5340117fe4198803ff430c403fc202800eff553300077ec898003ff43c4019fe10e601eff5513100ff44088002fc614c80bfea8a2000bfd911010ff841988f6fd6490c077e32e6000ff58221035f8c89810bfd50d0c7dff2848601ff8c110037fa87a008ffc301040d7f3266216ffd522109ffc2090806fc6050469fea9a8400bf58730037f8a8a1007fc5048001fe21a6026ffd964104ffca69000bff424847bff29a8600ff19310187fea09900bfe20cc8017f3088602ffcc932017fc42900ffff2090c0dff30e8400ff5933206ff8642181bbc43d080dff32e8600ff50e210ddfcc6188a7ff50504017eb048601ff90310037fec1a1806fe608840dfe2168600bf58b40007f8c890003ff424c477fe2828600ff10d101f7f8412180bfe4250801ff9928200ff18d41157fc8120807fe10cc0017e30a8602ff8c942007fc638801bfd62d0005ee1966400fb885210affcc110803fd3250005ffa926406ff90740057fca498003fd41500037fb022002fb0c932007fe87988037f654400dfeb288601ff88140017fea599013fe5244001ffb128000bf584430cdfeca1881bbf42d040bfe32a200eff54f30017fe439900afc62cc035fea846239ff94443015d8c498803ff414c001ff20c4200ff9053000ffe818803fff2150005fe192402dff0cb41035fcc8990e3fc2110c03fea868000dfd9530037fcc620803fe310c4057e316862aff142410fffcc1188d3fd5450849ff9008206ff18c41137fca720803df310c439ff0826217ff900310cdfcc3188e7ff5110c05ef196640cff90b3011ff8402080bfe204c8016e31a423bff04143007fe8288037fc32cc40dffa1c8600bf58231007fa64a08d3ff5050801feb22202dff08741037fec7a0033fe32cc047ff2808200ff59310007ee6318803fd608c401ff31a4200ff88710005fec89809ffe2050463ff3066429ff99541007fec0a101afe644c00fff29e2001ff143100b7faa11080bdc324c8077f32a2010ffd4940007fec2a1802fe63c4071ff190861cff8
  | 7 => 0x988d3fe53508015e322420fff8c940017fa8510802ef624c461feb2a640dff18643187faa6990cbfd54cc80bbe32a2001ff90330087faa8a001fff53c4001feb244218ff148310bff84018802bc644c001fe3222000bf98f42037f8842081bfe61d0003fe0868000ff48530037f680a0006fe61c400bff2a22006ffd0c4305ffcca9806fff53cc401fe20e6200f710c31005fec688006fe6010c45fe2966205ff14d10007fa629800bfd528843fff1846201bfd8d30007fec09080bfe424c81bffb2e620bff14d30007fac5218a3fe4250403ff9024019ffd4c310dff8a398843ff5150035fea8c6202ff8c93206ffecb990b3fe50d0401fe98a2000ff88730035fcc890803fd214400d7e32e8606bf990311d7f8a321807fc50cc005df2128400ff58532037fac1a180bff42cc8017eb22420dff94f30157f8612081bfe40d0401ffb148206ff90c41007fac91881afc6510c25fea8e8015ff04221017e842908a3fe3250401ff30a4006ff983420e7fcc09887bfe514c413ff32a4000bf5923118ffc2199007fc30c401bffb148630ff55132017f86490806fc60d0801f79944201ff08120187fea299002dc6350461fe2a26406ff18f40007fec788037ff61cc80dffa1e821aff1963101dfccb88077fc324c405ffa126406bf99330037fe84a000efe6590c09ff3122029ff55141007f8871880efe65d0c0d7e3266006ff983431e7fe40a180efc65504257eb2e8006ff597400b7faa31081bfc5450453ffa8a8206ff19741007fcc89001bfe4010c77fe1028602fb087420eff8429881afe6390c077e32c6203bf996410affc611080efc650c47ffe2948600ff58241007fec4a08c3fc654c803ff282400dff94c4300dfcc11881bff42504057f3128625ff14441007fec098863fe620c401fea126000efd0e43007ec621881afe64884015fb22602aff0824101df8ca88002ff614c805ff10684009fd951017ffc209900afe62504017fb226206f790c431d7fea721807fe105000dfe2008600bf58343037fea9a18effe5050c23ff2968001bf18142007fcc39901bfc6510457ff9048220ff94a31017fe43a1097ff53104017fb262006ffd8b43007f8871080efe654846ffe280860bff54930007fe8318837ff64cc401fea122000ffd0d20005f8c710803ff62c40017eb222000bf98e4100778c89800bfc3250801feb206214ff55121035fcc82081ffd65c4029fea9a4200bf58b10037f880a1007fc104c005ff294422eef55341037fe86a1803fe6488403ff9062000ff1913113ffc20a08caff65cc8037e3066202bf98841004feca98002fd60d0403ff9826001bf983431a7fea2a107bfd534c403fe1062006ff9534202ffaa488053fc5448401feb266232ff59732005fcc71081afc64cc805ff212423eef90243177fca7a0837fc640c40
  | 8 => 0xfd5243017fc85a1073fe404c40dff2a68000ff18520037788420802ff6250c33fea806201ff5013000ffea088083de328c4037e3048209ff1452001cf8ca88003fc4148001ff9922001bf18121035fecba081afc64440337eb286200ff99331037fec42080bfc32cc801ff30a6402ff0873206ffe6218802fd60cc401ff31e2002bf18b4016ff8a5a080efe654c06dffa8e8416bf596210ddfacb9881bff5410401ff20e6201bf98341007fa64980d3fe6550801ff31a8018ff10831037f88520803fd6090c0177b128206ff18b4000ffe4198002fd620c465ff28e6402bf58a21007fec0990c7fc40cc861ff32a640ebf5973000ffa808806bfc538c4017f30e800dff0c043037f8a9a101bfd54d0803ff1026001ff083301bf7c8021803fd21d001ffe1928006ff9874306ffec01880bfe32cc801fe31e201ebf58e31037fac3a000bee42d0813ffa9a4006ff50c41007fa63a003ffc215002dff2a44203bf99731087fca2a000afe6290403fe202800affc853015ff8a520826ff6548001fea0a6016ff59621047f88588043fd6550001dfa12820cff98b30007f8c2a1002fe61d082dfe29c4200afd9131007fe879806bfd658c4017e31a4202bf98910007fac48800afe62c4003ff1022014ff94d2100ffca19800bfe2148401f7a144206ffd0740007fc878804ffc504840dfe3068236ffd4342017f8a49001bf641104077e32a8000ffd8520017f84299003fc41c401bff218621abf596311d7faa121867fc510c4017eb166001bf98121007fa82880bffc404c839fe2826232ff54f321e7f8a4a1837ff64cc005fe1926430ff945321cf7aa821803bc644c4077f32e8202fb94920037fc822081bfd65d08017e31a400bffd4930015f8c498802ff6050c4dfe28c8200ff5853000dfcc0a081bfc405040d7fb28822aff942410c7fe40188f7ff5350c017f31a4006ff997421affc21a1013ff2144051fe1928229ff94541007f8c72081bdd4310c1bfe3266200ff50a311a7fca2a103bfe65cc0057eb168428ff085411c7fe4021903fe30d0c4dffa9c8206ff1974303ff8a3880cffe4050825fea968006ff50b40017fc859904ffc4048401feb1a2037ff08043005fac399017ff5244059fe1068201bf981420d7faa5188cbff50cc803ffa066022ff10b31217faa3a1897fd50104017eb244206ff18841087faa6a00eaff6590c65ff32e640bf754d3000dfec09805ffe600c403fe1824001ff8c340005fac899037fc6290c017e31a8432ffd473206ff8c221803fc410c40dfe2a2800dff90f3114f7ca8a0803ff644c81bffb206200ff8c73007ffc84a00dffe5010c037f3066400ff18d101dff8c0a187ffc108c465fe2a6642dffc8341037f8852181bfd61d0867fe282840bff95130047f8a58807afd654c4057e3166200f7d0d32005fac5
  | 9 => 0x80080080501100100000000000680c00580c8160018008110000fd00480600080900a80a00f80400080102a80181283b82780300000600980280600400300491f86400080080680180000585100200b005845003a3700e00100081980380000000100c02680283500c80080080200f00380000180001c0b600100c80280d82401881980600081f8a280680000380180083909680986300000000381680800000201183580000384f1160528578f600c00080000001180080381200c80c00902b02e80000000201a3b200100328b80b81780180000403580000180b00300480c018000003a7900000f80900000000701004280008b80002b81804500800a82400e00080000000c87200401602000000c00491009e86c80000800900080080000d00f80001e80480300180081100b80684e00002002a80000680796901900002b80188480081e01280482e80380201580702206c81000700215a82080b02800083e00f80900e852a3f80380000080001380381528980d80480501280800300d8008210490128488be80b00000080480700403b80000300a80510e0020050a209e80004f00bfc32d0805fe1024201ff141400073a862183bff53cc0037fb12401aff9963106ff8c198802ff6250001ff10a800bf794d30007fa878800bfc21d08017eb108606ffd8f410057ec890877ff204c44b7eb28820dff18b31007f86290003fe6150867fe1828400bfd89310e7f840988a6fd649047fff2948602fb0ca211effaa0a180bfc2148401ff21c8220ffc8631037fa83a001bfe43d04077f32a6206ff18b410e7fca09881bfc4310425ffa968013ff9012101df8ca9081bfc4250c01fea186230ff94d3209ffca0908e7fc5110c057fb0a4230ffd953204fdaa49001bfc43d0073ffa988602ff88221017fa65108bffc504c8077f32c6200bf58e4108ffe43a00d2ff65508077e32a8601bf18031037fca9a1803df6350435ffa946200bf58342007fec690803fe6344029ff28a4200ff18d40007fc8388002fd6344053ff29a821bffd5331007fa831090bfd52d0c077f3286200bf587431eff8a2a1843bd5450071fe2908602fdc8621007fe869081bbf4310c4dfea848202bf98931007fe6290073fc604c401fe98c4201ffd4130007be879900bff2188401ee9886201ff0c330097f8a7a00a7bd5450421ff32a8036ff54f42007fc8218802fc63440037f3068400ff90d20127fca42080afc62504017eb00622eff14741004facba0002fd62d0405fe2124006df59740007fe6498003fc31c4001fea1e6206ffd044100ffaa188003ff31c400dde2008642ff14f43017fe40a1006fe604c81bffb28620dffd97300077c8620803fc6150001fe9922000ff591301d5facb21803fe31484077f3288606ffd0d42007fac52080bfc2050835ff2a4623af
  | 10 => 0x168041b308c8098091bf80100780101a80000101116b00280000380080080582f0c38b100001000280000200381580001100080000200200400280285480001300680681782081500807500780280b80b03d81b0199a100f05f00c80100080b81b81502080700100500003f80281483580881e80781580100a80003880401600380580600000c06700780101900000401000780000180b00000000002c80001080883b81c0058038098038da00100900000080100580b08b80400c806a378030138020000030049968069ee03a00181203880d00000000000000081080085780600700c0030d701485c00100080300204301482680688122105080000880b80080a80503b00180000307280500480080000300000b81080102a80400104301614600201500a9fd80b00003e80f80280802400000b00401320680380900000a80580500300980386e88184b02a8b580000187480180000080001180a00003284500f0029a306581880380080000a00005486000c80002c80200280624184e80000080180000100080401102180180280000800280300280380182a83002101c80580000906e002047000001003005002820b7481101200f00b00109200600b80580380200c00f80a8048178ac00002c80002a00f80600080019b05280680204780a80280000181781e00901481588203100180280000d00580700582a8068000080568049fd0000018020018198578018000160000038030cc02282201880200211801007400000480a02d8000020e000c86881802100020480381000500f80004980480100800802f0000010078cd01580201281700480500300003005500001204480100e00b80e80602100701c81d00600702980202100000a801808003aba80b81100e0030170570
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x7714c931014fe72d8d41006df2118d41004ff7058f413bf9c7550c43034fd7690631106de72d8d21005f771509410057f7558d200067f655913006cfc75d9330006bc64d893106ef43198643004fd74d85300059c735044104d7c75585200067e72d953000cfe70586430047d75d8f1006ddc735073006edc63cc521014fc74d89400079e6310d420eeec21587320069d5418d4101cfc75d8b10006bf7459130034fd7018d4001cfe75d853200dfa76c4110036be645073116cff7159121006df6398e21107cc328c621006be54d854006ede630c6210379d6550c430a67c6548510006ee10d8941007ae43d0a2119efa40d8142005df7348710006df70d8d210067f74d951006eec3258b310373e6590c411b67c65d0910034ff7650731006bd645073113efa60d8141006bd54d91300067f73d951006cfe7318542004f77158d202457e76d9510004fd71d933006ef97098d20006fb5058331004fd76cc841006bd64d0a31014fe725864306cff7518d102afe741d8941006fb50583410069f64d8d21005dc73505210067d65ccb40006dc20d8d410067f7558910004fd7610d20034fc764cb402aeef41d8941006bf64505303c5bd7550c43004fd75583431f6be6090c4106ef46158643036bc4358c41004ff75d9121014fd7158b102967c70d9530156f86058241004fd75d8543007b57190e41004fc764cb10006f7610c52015dbe72d0641145ec7258d41106de21d8d2106cfe76d083101cfc7558043007af62d09410067f6550530036df4358f40306de64cc931015ee720c621056ec6258930006ec601894101cfe7598f40005dc7350510006dd75d8d412c6df4218d412967c10d9530166f710d854001cfc7518530014fe7258341004ff735911000cfc7358730036be64106313079c43cc8410c5dc724c431036be6410d32005f47158d420079c4350a31005ef725043106edc3018d212afaf42d0621005bc7458d200c6ee5258831036f4415874301cfe7558f40014ff764851023e7d71d9510106ee3258a3101cfe75d8d41034ff7659221006df6310d2105d7c7559130004fe76105300ecfd76cca31004fd75d933013cfd7699310006bc4358a4101cfc7558b303a6bd6590f42006bf6450510034fe749873000df87088510004fd73d8142006bf64991311f6be50d9130006de70d8d210fcfd70d8d1006eef3258831006ec6518941006bc7458d1018def7258d20006bc64cc521005dd7610e310067c7559110036df7358f420067f65105301f6bc4058243046ec6258b10006dd51d8d211e6ee62d894301cfe75591300067d7059441036fb7058343006bc301912100cfe7058b431f6bc10d913006cfe7398742014fc7298730006bf6490731034fe76d91301f6bd73d913006cfc7518e21126bc4218542036fb40583433b79c5250c43
  | 1 => 0xe21004ff7558831004fd764873000cfc7018532004fd7610f1006edc3218d10014fc7298c41004df764c431005f9708871006ebf74593312aeec648852101cfe7558f1000cfc764c530004fd7559131006f77159110006df7359110035bc7458a41036ec4258b4306cff7158f10004bf7458d20006bd54d93300067f6518530006ed624ca3101cfc7559121004ff7358342007b864cc130006dc5118d21004fd75587320367e42597401e7cc3250d3209efa1058b1000cfc7018d10014fc7258043004fe7690531106ec2158a31006f671d8b1000efb61c4110006f55118532006ef628c5310079f6418d2106ede73d9031005ed7290d42014fc7258f41106ee62d8a310057f75585401febf42d9132006ef74d89310a67c6548530034ff76590312fedd6410d320de7c65cc510005ef7250530005de7390631006bf53d9121004ff7650520004fe7690d200c6dd4218d2101cfc7558c410067d65cc841006be321913006cfc73590310067f7159740006bf641853001cfe755903106ebe435903106cff7598c410057f7558143006ed52d8941014fe7258f10004ff725903101cfe7518d202c6dd76d0c31004ff7358341006bc5119121036be6410431106df20d8d211def850d8143006bc5019121006ee53d8941005dd76d0c31005df7350540006de32d8d41014ff7158b10006bc51d913106cff76ccb102967d20d9530005bd7190c41005bc744c431005ef725911000cfc7058732004fd70d8532014fe76cc521006fb705911000efa76cc130005bd74d8f10004ff7059121007b4744c4310c6df2118d21005dd739043106ddc7350731006bc53d9121006ed74d8931036bc7458f42006de638c7102efd571d0e31006dc6350d4006edc3018d4106ede63cc841004fd7610d10005bc74585302a67d7059740006ee65d8931006bd72d9130006ed53d8941004fd72d8d400367f7459740004ff7558f41034ff76d0e21005be76d0941006ef624c941006dd65d8d41004ff7058e41006df4358a31004fd7559110146ee71d894100cff7688710016dc624c931036be7610d42007cf43cca21004fd7598f420c4fe768c521005dc7358941006ef71d8931147ac625094106cff7598f100c6ee4258831006bf7458910004fd764cb4000cfe70d9131004ff755823115ebc62905410063f6519130327b65150441107d421d8d21006ef74d894138f9d5410f3200cfd72d8d20006bc50d9131014ec7258443007e4724c431006f7614c530006ed72d8e2101cfe75d813100cfe7059221006bd54586432ef9e64d0e310067c651913001cfc75d85431bebc2019130006ee43d8941104fe760c5210079f744c431004fd7558043015ee7290d202adec74cca21034fe74d81321f6bd70d913006ef83058043006bf64509311e6ec6258943006dd6390e41005f
  | 2 => 0x67f71d9530006bf75d9121014fc72d8141004fd76d0b3106edc630c5202edde74cc631014dd76ccb310373d6550441006dc5018d4106ede7398f40004ff7688730006dd53d8d41006dd634ca413179e4010e310067c7558d10006ed50d8931006dc5118d41036be64d0731007cf6388521006dc21d8d4106cff76cc7402975c30d9530004ff7258f10036be7498742104fe7618d21006be5459221006f72118530034bc7458d211e4fd7650d32116dd3298e210079d4310d3106ef76198730005bf7448730005dd73d0731034fe74185320067c7059441004f47158d20006bc648c52102d7e7598d10036bc6490d300c5de72cc431006bf64d8d21004fd7558e21006dc5018d21014fc7258d10014fe7258331006be20d9131006dc635094113ebd4059310005ed720c621105de72d0e31126ac2119121034fc74582311f79c30d9130004ff75d812135fb551d06413bf9e5150c43005f97010710004fd7558d20034fe760c740004ff75591300067d75185420f57e75105310367e42594412efd741d8d41006fb50d8141006bd6450a3115ebf52d912101cfc75d8d2100cfe70d9231006dc63d0e21004fd7559031036bc64d0530126ec6210531004fd7518530005ee73d0a21006bf51d91210057d7599110006be52d9131007e7724c43100cfe7058841006df50d8d2100cfe7058a41004fe7610e21014fe7298740035be7390c41006bd51d9131016ee624ca310367f745944106cfe7398d1000cfc7058a41006ec60d8941004fd7318520006bd3119131005f671d0d31126be42588410bef510185303079e5410f32004fc7159130006be5458643005bc7350441004ff7558332006dd74d8d21006df6390d41006bf6390d42005ed7298d410067c6518d10006bf648c531035bc72d0641026ec62589100067c7558910006ec65d8941025f87648110004fd73d81410067e72d9510006bc640c530034ff76505310067c62d95101bef85058043006f95058031004fd7098732006df7358d210367c4359740006bc52d9130014fd70d912001cfe7598443006be621913006ebf6499331004fd73d81210067c7558031004fe760c52001cfc7558f40015ec7250d4206cff75d93310079f63d0941004ff75591320067c325974006cfc735884106eec6258b311b67c65d093000cfd74d8940006be54d9130004fe76885400079f644c931036f84058343006df73591212eedf41d8d4119efa60d81420069f7650c43006df43185320069e5418d4106edc6310d10035bc744c74005d7e7598530396bd6510d42006ee10d8931015ee72d0d32006f721d85431bebe1019130016cc624c931005dc7359110006bd5498f40004ff7059331004fc715884300cfe7359330005df7350431006bc64585301f6bd20d9130004ff7650b31014fe7690d4206cfc769
  | 3 => 0xf6510510004fd76d0e21004fc7159120005fb7050940266dd3218d2006f9c6150c43036bc6450d3115ebf21d912100cfe705873227cfe7619120004fc7159330014fe72987300067c42d953006efb3058331006dc70d8d41006dc65d8d410379c4350e41006dc6418d21006bf71d913001cfc75d8131004fd72d9231006bd641043101cfe75d8d401defa40d814320edf62d0d320057f755833200cfc70d92211febd42d91320057d7510710006bf64d0d31006dd638c710036bf6290d42004ff7258f41036bf7019121004ff71591320047f755913000dfb724811000cfc70d903106e7d7598d10036bc64d0b31006ef63cca2106ede73d933035ebf65d064106cfc7518d20004fd70d933201cfc75d893117efa60d8132006dd6518d21014ff7658831006bc42d9130004fe7650d10034ff76d0730004fd75d8e2135fb651d064117ded7298d20037b761d0941036be649071012e7d715944121ff151c4110034fe7418f10006de7518d21004fd75591323cebf6590d431bebd301913000df87050d400069c64cc931006bd5219130006bd6519130004fd70d9221006be40d91310067e75d8142004fd76d0d21006be53191300057d7599120004fd73d8941006ed75d8931006bf6499221006f421185431bfb83019130006bc75d913106eed72d93320367c4059441004fd7558221036bc6490531006be6019131006bc64d8131014bc765094106edc63cc940014fd7018520006bc4259331006ef7258e21006bd6519121004fd73d8540006bc65191310367c43594410379e7390f42004fe71d913201cfe7558241014fe72d8540036be5498f40006dd6318d4206eec3258831004ff7058b43004fe71d8940005bf7448510006dd70d8d41005f87148110004ff735824106edc4398c410057d75d8f1015ebf42d91210c6de2018d21006bd531913001cfc7558031006de53d8d41006be54d9330004ff7559231005ed7210520004ff7558e41014fc7258231006bc2119130105f67118e21006bc644c93006cff7610e21006bd5418d41036bc4358841006bc42d9110006df634c62106efb7058043004fd7098c41004fc7650a31006dd52d8d41006f56118532005df7350530014fd7458b40016ef63cc932015ee7210520005dd7399121014fc72d91100067c7558243006bd6490f102ef9e7410e3117cfd7698d200fefa2058231014fe76d0521006de30d8d2133ebd6590c412a67f1059740006bc601913106cfe73d8520006dd7518d21036bf731913023f7810d9510327b55150441006ec54d89312c79c43d0831126be2019121004fd7558f420067f65d8d10006dc638c52100dfa70907101a67c6550910146ec6250531007af62509410067d65887400c5f671d8e210c6cc2118d2115dbe7619121004ff7358841004fd70d93310de7c65cc530
  | 4 => 0x913101cfc755834101cfc7558f420057d75d81422aeee648852101cfe7558d10006bd5459332004fe76cca412aeec54d89412ffcd72d0d32006dd6418d21036f74198740005bf74581310079d7150c430067e75d8f10036bf6590c410efcc62cc931004fd7598740014fe7650d32006df53d8d2100cfc7058d21006ef7258d1002d7c755911000cfc70d891000cfe7098e210073c6519130006ee50d8931005bf7458931004fe7619131006cf6318941004ff7558910007af6418931006df4398732036be6419221306df43d8943005f77150e31006bf7650c43036df4398f400067f6599130007ad7290d42006dc63d0d210e7d8304c530004fd76d0931005f571d0d310fcff764c730016ee61cca2106cff7518f10004fe764c941006ec7258443004ff7558a31145ee76d8941004fd764cb41006bd54590310f67e654c740004fd76cc910004fe7118d422967f40d9530006df6518d41004fd70d9132004fd7650910004ff7558243014fe768871006edf6410f322dddd738c431004ff7650d2000cfe7458b40006dc53d8d21005f970d0510105de73cca31007f07148110006ed50d89410063d6590c41004fd71d8943005f970cc510006df6390d40004fd7518d21006bf649913006cff7218d420fcfe7118d101e5dd76d0f32005be71d0941014fe725874000dfa700c71006fcc43cc932156bf40d911006cff7018d40006be5418d4105d7c755853022cfe71d8b100067f65505100d67c658c510004fd70d85431c79f4210d32036bc4158443004ff7058e21006f46190540005be7498d210067c6558930006ee63885210077b65481100c6dd7218d21006bf644c5300067f654c530006bc30d9121006bd6419131014fc7218d400379f6390d432c6df64d0c31004fd7650b30036bc64d0d210079c64d8d211a67c65509300363f4159441004ff72580411bebe4018d40006bf64cc5211c7cc2110f32015ec724c520006ef621053123e7c70d9510004fd741853006cfc7359120006de4018d21004fe764c940006bd6310e41126f5211854225edd3018d2016cff7650621106de3258a31007b764cc53101cfc75d8940004fe7610f101fcfe7610d320eddd72cc931017ce73cc9320067c7359441006be51d913023e7c10d9510357e4411894106cfe739864301cfe7558d21006df630c540036bf61d09412eede6110c31006bf6499110004ff7650e21015ae7290d42005bd74cc8410057d7510621006ee75d893101cfe7558a310befa50580310379f7650c43006dc60d8d410c6ef2058831036fb70580412fede7610d32005dc7350631004ff735912006eed72d933100cfc7648510036bf7219131004fe7650d2001c7c7558031036bf70191311e6ee32d894306fd571ccb31006f7619852006cfc7358041005f970907102a67f20597400067
  | 5 => 0x47f755891022ef85018520004fd7558d21006ee63189411e4fd76d0f3213ef8605814100cfe7498f40106de3298732006bf7459132006be5459031006f4618c530036bf6150941006bf6490530006bc50d91210047f75582430e5f57198d10035be740c7402167c65d0d10107cc32d8e210379e7310d422967d70d9530006bc51d9121004fd70d8931034fe74d853027ebd40d9120004fd7298443005ef724c5202a67e305974006cfc7358a430eeee761893106ef6719844332dbf7590541005df7348730034be76d9131006de6418d210067e735974015ebd42d912104ef86548110004fd7198d2000cfc70d9110014fe7258d10006bc64d8930014fe72d9331004fe76d05200c7cc320c621005f47150b3111efa3058041006ef72591200d67c658c53006cfc7598e21004fd72d8f10034fd70d8540014fc72d8d402c6de7418d41106df52d8d2106ede73d9332005ef7250d32006de10d8d4106cfc735931010cfd7098d1006fd6638c43106cfe7318520004fd7610520014fc7298e41004fd76d0b10014fc7218d10004fe764c520015de72d0d32004fd709844306cfe73d9330006dc435883106ef83058331015ec725052007eee62d89400079c435083101cfe75d8b10034fc7648740016de62cc93100cfe7018d4106fd732cc531006de7018d41006de2018d41036be6419121006ef65d894123e7d20d9510007cf63d8941036ef7258b41205df7359130006ee70d8941006be62d913116eef611894106ef43198730014ec72591100c6de3218e21014fe7298f41004fd75587421adef7259120106ec32d8e21004fd70d8d210c6dc3258831014fe72185430057f755813100cfc7058742036ec4258841146ee62d89410057f75582410079f63509410c6ec2118d2100df87050d30005f9700c520006be5119131006df634c941005bd729054100cfc7098f42034fe76d9121004ff7558a41025ec7258d10004fd75d8141006bd5459110016de624cb310edf57198d21144fd76d06211dddd739913000cfc7098e21005dc7350a31014fe7258c41007cc6318941004ff764c431004fd7558231004fd7558a313af9e7050c4300cff76583320067c755913006fce7210f320067f2059441036bd72191310079d6410d3201cfc75d913106cfe7690730006be4059231006bd545844301cfe7518d21006ec10d8931006ef62505310c6de3218532036bf7319131114fd7298d212c5dc744c431006ed54d89312eedf64d0e31006de74d8d21006bd649062113cfd76d0710004ff75d8931124bf7650b410c5de72d0c3100cfc7359330006df634c9401febe7690d421befa2058043006bd6419132006bd6490d322fedc644c93106edf3298f42004ff725803106cff7598d101f6bf40d91300bef81058031006bd641912106cff72d91320edec725
  | 6 => 0xe10d91312c5de74cc4312c6dd64d0c31004fd72d9110014fc7298740046ec2158b1015cbe76d0941037ac4250d4206ebc6499031005df735852001cfe75987320067f655891001cfc7558831004bf7458e2106fcd62ccb310c6dc2018d21005bf744c540036be64904310079c6390d42006ec725913106fd653cc631004bf74589100067e3059441006bf64d0d32006dc6358941004fe7610d1000dfa708c7102967c40d9530036bf7219130014fc725844306eed7298d20004fd75d91201f6be70d913006f9c4350f32005f67190d410047d7518542006bf6499120034fc76d0e210eeec52d8931007f371481100067c72d9510004ff7558031006bf6490d20004fc76509300067c3259441005ee7618941006bd72d9131006bc4318542004bf7650c43126be4218542036bd75191211bf9e3019130036be6450e311967e65cc841005f57110e21006be32d913100cfc70d89430067e7159441234ff7158910004fd769073006dde73904311c79d4210d32005df7359110004fd7518d423b79e5250c431bebd5019130005df7348510004ff7059221004ff7558d20007af64d8931034fc74580310373e6550441006be5459110007cf62cc931006bc64cc9312eedc54d8d41004fd76d0431014fc7650d3201cfc7558910004fd76d0b30004fe7650910006be40d913200dfa701053006cfc7610f10006ee50d894106dde73d0731004ff755824115df67119221004fd7699231005ef7258530014fe7258e41004fd71d8d42006bf6450d30014fe7258041005f77150a41004fd7298643007af4250621006bc6498530036be54584431dcfd76d0f30004fe71d9031006ee54d89310bcfe76cc530144fd7650521126bc2019121015ee73cc93206cfe73d9221005dd7110e3106cff764c510036be649063106ede630c710006ec10d894100dfa7010d10036bc6450b310067e7259740006df51d8d21004ff7518520006df6398d200359f7650c4306ef6634c431034fd70d89401e6ec21d894301cfc75d9132005bd7190e4101cfc7558b410359e7390d43016ac62d0941006f551d8532006dd50d8d411fdbe7310d42006be54593320067c6598d1006cff7518d2001cfc75984432adee74cca21036be7319121005fb705051006ef731587320067f755803101cfc75d8d41105de7618d21004fd75d8d21007cc63d89410067e7059441034fe74987322aeec41d89410067f6550d30004fd7558730006be5219131004fd751854234dbd75d0941006de4018d41105dc72cc6311e5ec725854306ede7318d21006bc6498d21006bd64d0e3100cfe705903106ebc64993320379d6250c432eedd6410e31037b76150941004fd7558341006bc20d9131034ff73593300067f65905300c4fd7218d21004fd701854206cfc73587420069c639054124ef97018520
  | 7 => 0x8241004fd7690d100067c6519110005bc74585202fede644cb31005ef7250520006df63cc521036bc4098f400047f7558d20004ff745873200cfe7058843036bc6410d31004fe71d8132016ec62cc910004fd7498732004fd7118d42004ff7598740034fe76d9110036bc64d0521036bd76d0641014fc7258743004ff755873006cfc7598f42006ec6418931106f5219873201cfe7558243004fd7598f41006be7619121004fd7018d4110ef710d853006cff7598e21004fd72d9031004fd75d8d412eedc43986430367e74594412eedc41d8d41004fd7298730006bf6490d3101c7c7558910006bc640c521034fc761052001cfe75d85301fcfe761913206edc64ccb31004ff764c841035bf75d0e4306cff764c521004fd7498f10006dc2018d4100cfd760c710014ff760c6210edee76d89310067f65d9130015be7210d42006bc3219131006de634ca412ff9c4010d32015be7290f42006de1018d21004fd7558f4015dbf7450a4100dfa70887101357c755824110edd3098f100067c42d9510005dc7348540004fd72d9131006bc6519121004ff751854301cfe7558b40004fd7518d10014fe764c52106cff7610f10006dd7018d41006ed62d0b31015ec7210e21004fd75d8d42006f651d853201cfe7558b41006df6398e41036bc6090f420379e7310e41004fd7298c41006bf64d053101cfc755923106ede63cca4123e7d70d951006f9f6550c4315ebd71d9121004fd70d894106cfc765083102d7e7599110004fd75d9331014fc7298f40006dc30d8d21016ec624c9300067f72d95100079e7150c43006be10191210079f7250c4315ebe20d9121005bf744c43101cfc75d891007eec625894006ef970d9330015bc7210d42004fc764c910004ff7558732037ac4250a410c6de7218d21005bf744ca41006dc63d81412b7d6514c4312afe441d8941004fe71d9120006de634cb1001cfc7558a4130fd553cc631034ff7650521036bc4198f412fedf6410d32106df21d8d21006bc7458d21034fe768c74013cff7059110006cf63d8941035bc7448540004fd74d8d20396bf6510d4219eef2058b401f6bf73d91300079f6310e41005f47159132006ef6318941005ed72cc52100cff72d9120034bc7458d20004fd73d8940005fb7050d4006fd671ccb312167c65d0d30006bf6458131036f74158740006ec6018931014fe745834206ef73158730014fe725931000cfe76d814206cfc7518f10106df42d8d21116f621d8532106dd71d8d21166f8505834106ede6390e41004ff7558b41006f561185203079c4010f32006de62d8d4106eec6258b300079c6310e41004fd768873010ef85058331126be3219121006bf648c52111cfe7690510014fd71d8121006ed54d8941006df735922104e786548110165f771591100c6f52118532006b
  | 8 => 0x1feec2158a430079d4310e21206fa3058343005ef724c740016cc62cc93135ebd65d0641004fd73d8520006be53191210c6dc2118d2106f9e63d0e4306cff7518e212a67d1059740004fd7298d10005f47150d41004fe71d814300cfd72d8520006bf7459121006ec60d89311bebe5019130004fe7610520037af6290d4206dbe7390d43005fb7050d30014ff7690621034fc745822100cfc7058e21034fc76d091000cfc7058c41034ff7659332006af6418931005bf744c53006ef97018f10126ec421854200cfc70d8d21004fd76104311f6bf70d9130006dd630c710006ee6018931037af7250b410b57e7510621005ee761893101cfe7598f10036bd7219130004bf7458d210aef860582211e6ec6250d31006bd531912113ef850d814101cfc7558241004ff7558342006ee51d8931004ff7650730006de1018d41126bc2119121126bd32191210079d4310f100079f64d8d21004ff755933000cfc7058643036bc645053006cff7690d100067d654874023e7f40d9510015dc7210f32004fd75d894003d7e751071015eec6290531006dd54d8d41034fe7498d10014fc7218530016ac6250941006bd6410710006be52d9130004fd72d8d100edec72505310067f65cc9301bebc1019130004df7359221006f7764c431006bf64d0d21004fd7559221005bd740c740006f77158d21204ff7650f3006cfc7598d20036be6419231006bc6390541005bc744c621006bf64cc93006edc6390d21004fd75987420067f6599110006df7358910006ec62d813101cfe75987300057f755814101cfe75d894001cfe7558031007cd63cca212c6dc43185430067f654c510015ee72d0d20006be75d913115eee4258a41006de3218d412a67f3059740036bd7519131004fd7558b40006dd6518d4106e7e7598d1006ebf6499332006ec6518931004fe7690530006bd53d9131037b66110e4123e7c71d9510006bd65d9121014ec7259131006bf644c93100cfe7098443014fe72d8131006be40d9121006df634c510004fd71d9130015bc7290f42006dc75d8d21005de7618d41116ef2158b31004fd764c84106edf3018d102aeee54d8941146ec52d89411f4be7619130004fd76cc940004fd76d083100cfe70d891001cfe7558f42004fd7098f41014fc72d8143005bc744c71008dec724c740036bc6490d21036bc6410530006bc65d913006f9c3250c43004fd75d8943004ff7558d10006df735913200cfe7058f4106f9e7410c311f6bc40d93301befa1058043014fc72185432fedf4358a43154fe7610510006de50d8d41006fb50d8b102e79e4010c31006dc10d8d4106cfc7518d4001cfe75185302efd441d8d41006bd5498f41036be6410f10016be62d0941006bd5119131014fc729874306ef76198643114ff764c831004ff75593310047f755
  | 9 => 0xc7558241006bf7459310034ff7659120005ed72906211a57e75d814206cfc73d91300067f659051006cfc76d0531006bc641853017efa30d813206ebc6459031006be72d91310eeec3258e21006ee74d8931005dc735854006cff76ccb402eede54d8d4106edf7518d41006df6398d421bebc6010e41014fc7259310006bd64904310fcfe760c510014fe72d8543006dc52d8d41036be6410621036bf7219121006ec64d8931006bf64992311d67c6590d10004fd7098d21004ff7558b31006bf6499121036be64193100057d7510521005f9708c5300efcd731893106edc63cc510036bd7119131006be6019121036be5498f410069f6410e31004fd7558443146ee74d8941036bc64d0d32004ff7650b10005ef72585400063c65d9130004fd7118d40034ff7159310006dd634cb10006bc21d91311bdbe7050c4301cfe7558742035bf72509410067f2159740036be7119130006ef628853006edf7118d4100cfe7018d42006be53d913101cfe7559332006de6018d21036be701913101cfc755933006cfc7690d1020cff7650f32004fd75d854006ef73158643004ff75d8543005f7715894300cfc709874200cff7610710006be42d911006edc7518d411767c65d0510017ae74d0a210067e42d9530004fe76d0910004fd764cb101f6bc6090d42004ff715884306cfc7118d1015cfe7619121146f62158742006ed641893106edc6390d41006ef7258b100c6dd3218d21006bc7458910015ec7250d32036bc7519130004fd76ccb41005df7350a31006be42d9130004ff764cb10006bd5459310014ff70d8d20006ed75d8941006be4259331006ec7259110004ff72591300ce7c650c510006ef63d894101cfc755824300cfe7059332006bd65d9131006fb50d812112e7f715944111df671d9310005ed72d0e21006ed5258a4300cfe7018520004ff70591320acfd70d89100047f7558d10004ff7518532006df6310e210c6dd5218d210e4fd764c510005dc73485302c6df4118d41005df7350520114ff764c62100cfd7610710004ff7598643006f771589101967e65ccb40004fd7558b3000ff361481101aefa20583420e6fa60d8131006de7418d21005dc7350540006bd641913006cfc760c520006dd7418d21004ff7259331326bd6550441034fe76d9120006dc50d8d21004fd7558243006dd5318d21146ee761894106dde731073006ef7319873206dde74d0c31006bf54d91301f6dd3098f401e6df3258f42004ff7058b412afe671d0a21004dc73591213bf9e7550c432ff9e7410d32006ee63d8941006dc51d8d21336bd6590e4100cfc764c93006ddc7350431006df6418d21014fc73583322967f70d95300367f425974023f7771d95101f6bf6490d40005bc7448530014fe7218d20126bd5219121106dc32d8e2106ebf6390d43
  | 10 => 0x8d101bf9c3019130004fd74987300063d6550441004fd7418f100057d7599130006bf648853002e7e76d9510006df735913006cfe73d9120006df6398f10036bf6550441036dc4358f4200cfc70d9132034fd72d8142015ee7290e210067e7359441004fd7598e2100df87050510006f5611854000dfa76cc130036bc6490d10006dd5318d41006dc64d8d211767c65d0530007d4714c931106de20d8d21006bf6498d21004ff7158043034fe7498d212aeef40d89411def86058143006ec74d8931006dc62d8d41014fc7498f42016ee6288710006f421d8543004fd764c910004ff745823100dfa73cc130004fd75587430067f2159441006ee60d8931016be625094123e7c40d951006eef3258b30004fd70d8d4118eef20d8930014ff7658b30004fd7418d21006df5318d402967f10d9530014fe7259031004fd7318540005dd71d0e31006dd70d8d210ce7c650c530036df7358c41006be5459310034fc715824101cfe7559110005f67110e2101cfe75d812106edc6390d4201cfe75d913106cfc7690f100067c71d9530006f561185301867c654c910006dd6318e211f6bf10d9130005ef7250531036bc64d05100067f6550d10005bd7110e4106ebc4359331004bd7498d21004ff75d8940004fd760c520006ec65d893100cfc70d8931005bd74ccb400c4df764cb31004fe71d9330006af64d8931034fc7458e21006ee51d8941014fd7358b303af9c7050c4301cfc75d8d40034fd7018540014fe71d891000cfc7058831006bf6410d100079c43cca41004ff735874000cff76582411ed7c755814306ddc72cc431004ff75d8142107ce3258a31004ff7558b100057d751923106dbf7650c4306cff7518d410067f6510d30014fc7258f1015cff72d9121006bf72d9131004fc7650d10006dd5218d41005bc7458131014fe725844300cfc70d9131005dc735053006ede5318d21036df4398f41004ff70587320057d7510730004fd7558e4106ede5318d4120dbe7610d42036f44198740006bc6458931004ed72d9331004bf7458d101f6be6090d42036bd7319121004ff7559310006bf20191310367f42594410067d73d9510006bf6410d301e6ec6250d41106df638c521027ea5248110004fd7558b1001cfe7518d4006ddc7350831006ef62d8131004fd72d93301c5de7390d32035be7390e41006be65d913100cfc70d8543034fe74d8d1006edc5318d40006dc634c941016ee62508310067d65cc74006ef97098d100057d75105100379d6150c43004fd72d853005e7e76d9530006bc32d9130104ff72d8d211debf4059330036bc6410e31004ff75d92310067c7558d2015eec6290541036bc439874306cfc7518d41276df32d8d200e6dd3058f1006cff76cc8412a67c30597403b79f2050c43015be7290d42006bd545804301c7
  | 11 => 0x117cc21ccb31006bf6410e310079c648c531006bd52d913129d7e76d953000cfd7458041006bf745911000fdb63cc130006cc6318941004fd76cc740016ee62ccb41005dd7110d322d6de638c431006f970d8f1001cfc75d8d10004ff75d9132004fd751852000cfc7058a31006dc6518d21006f42118530004ff75d9310006dc63d0521006bc65d912122efa101852006edc630c52106cff7518d42006be10d9121006ec40d8931006bd75d9130004f77159132035be74cc940014ee76d89310067c32d9530014fc721854008dfb7059120006bc6019121034fe76d9132014fc72d9130006dd75d8d210079e53d9130006dc6018d21006dd76cc6313bf9d5150c43004ff7458b310eedf3258e21004fd7498d10004fd765083101cfc75d912015ebc20d9121146ec4259221004ff75d8d10004fe76d053006ebf6499031004fd7098f42006bd51d91301867c654c93006cfc7359121006bc52191301bebd2019130034fc7458f10006df63d0d212975c73d9530014fc7458742006bd50d9131106dd42d8d2106ebe7498d210079c6350941004fd7498e2101cfc7558740006f56118542005bf7448540004ff75d89300c7cc2118d21004fe71d8142005bd74d82310fcfe7118f103af9e3050c43034fc76d0d2001cfc75d931001cfc75588430067c6558530006bc70d9131005bf7458e21006bf65191310067f65d9110006df70d8d4106ef57198d100073f65d9130034fe74d813128f7865cc1300079c63d094106dde73d0b30005dd7110c31014fc725911006cfc7650b31006de40d8d210367d4259740004fc71580430b67e6588740007b7744c431004ff7648730016dc624cb312a67c7059740004fd7690520154fd70d9110004fd7098e2115ebe32d9121034fe76cc7402eedc42d8d4100cfd721852001cfc755913000cfc70d8d41006dc72d8d41015bc7290d4201cfe75586430067d72d953006edf3018d4001cfe7558740034fd73d89430079d53d9130006f77158d20036be54580430057d7510731006bf64d0b311c6dd3218d420047f75580310067c62d9530004ff7650d21005df7358941006ed64d8931004ff7258f40016ec62cc93100cfe70d8941005df7359221006dc6018d41006ed71d8931005bc7458d21006be3019131034fe74d8f10014de76d0d3200cfe7648510014fe7258031006bc62d913013efa40d81413b79c7250c43004fd7558c41006dd65d8d210067f65885301d67c6590d30004ff7650f1026cff764cb300067c3059441034fe7418d21004ff7058a4122cfe7688510306dd64d0f320379e6550c43127ac2119121006ed6318941036bd70191313bf9f5050c43004fd70d9121006df6398d4100cfc76d0d30005f4714ca31006dc2118d41006ed62508310079f6390d42005dd73d0531004ff75d85400067c655
  | 12 => 0xf725922101cfe75d9120004ff755834115ebd32d91212a67e205974000cfe7058a4318cff7258d20006bf7458d20006de64d8d2106eec6258a43014fe72185301f6bf50d9130166fa1058341006bf53191311c6ec6210d312aeec40d8941004ff755884116ef621d85421a57e7518542036bd7119121036f4415874006ebf7459031014fc7359332005f47150d31036be6419130015ee718852106ebe4359332005ed7210621006dc63d81210c4ff764cb31004fd7098e411e6bd4259332004ff759873006edd7610f3200cfc7058f41015dc72d0f32004fd7558841006dc5418d212c7d74118d4106cfc76ccb10015de7210f32006dc6518d41014fe7259131007ad64d0a210eef62158732036ec42588430067c73597400047f75583320367d42594412cfd6328c43101c7c755913001c7c7558332006bc53191311f6bf20d913000cfe7018542004ef7258d213779e4010d320067d658c740016dc764c931006f77159132034fd72d8d42004fd755891000dfa7010520004fd7690e21006dd6350e41016ec62cc94100cfe7058742006bc644c530014fe7258231004fc7159132015dc72d0d322afe571d0a21036bc6090c41014fd73d8132005bd74cca41004fe7650931006bc64d8121015ee721062101cfc75582310067f65cc910006dd63cc8412ef9c4310631115f77158d21006ee75d894101cfe7598e41006be5119130004fd70d923106cff76ccb4106efb305833201cfe75d9130006bd5019121006bf6490d212eedf40d8d41006dd5018d2100cfe76d8141004fd70d8d4201cfc7558b4001cfe755933100cff7658031006de70d8d41014ee76d894106fcf724cb31034fe74d853206eec3258b30006fb7059120005f671d0e31005be74d8231005f57110d2101cfc7558e2101cfe7559131006be4318543006bf501913101cfe75d8943004f7764c4310067c75582212eede648c531004fd75d852006f9d6410f32004fc76885300aefa2058221006ed43d894100cfd73d8930004ff7058a43006ed43d8931004fd70d8542004fc76509312967f73d9530036bc6490d20006de51d8d41005df735053112e7c7159441006bf64d0521006ef6290541004ff7650831006ef629053100df870485100067f755822126cfe7618d20007d7438c431004ff7359221036ef4258b40004ff7458031036be64191200069d6410f32006bf6410520007ce63cca21014bc7458f42006dd64d8d21004fe76d0b10004ff7598443004fe7690d21014fe725933000cfe70d8e2100cfe7018e21004ff75d911000cfc76d0510005f67190e41014fe72d91310069d6410c312967f20d9530006ed63cca21034fc761062115ef52198742145bd72d094106ef57198d21005bf7250c43005fb72c4110006bd75d9131006bf640c521004fd74d893106fcc324cb30
  | 13 => 0x93001cfe7558d203bf9d5250c4315fac42d8a410059c7150c4300cfe76cc510006dc32d8d1001cfc7558a43004fd74d8f10006dc631052100cfc70d933206ede7318e2100cff7218d20004fd7598f40014fe7258343036ef425884300df87050940006bf765044106cfc7598f400079f7050c430eeee42d89310ecfd7698e2106ef43158732016be6250b41004ff765043101cfe7598f410057d7510631006ec70d89410fef81058231014fe7498742006bf5219131006bf6499132106dc20d8d21004df7358910006bf6450531004ff75d8b10014ff7658a43005bc744c730014fd768c621006be60d9121006bc101912101cfe75d8f102fedd64d0d32015ee7210d21004ff7558f1000cfc7650540015ec724c621007ad5418941006f47158d2006ef73158443006ec7258d102c6dc5418d41004fd71d8930014fe76d8910146ec215874210df77158d1000cfe7098f4200cfc7018e21004fe7118d20004ff755913115ebe42987420fcff70d8d100067e42d95100077b65c4110036f4415844306edc4398f42006dd5018d412967e30d9530005de731063101cfc75d913006df5738c43101cfe75d9031004fd7558a41006bd70d9121036bc641052101cfc755864320fce72d0d3206ebf7459330006ef54d8931034ff76d0f10034fd70d8d40005be73d0641006be65d91300363c4259441006df6398d210f57c7558131004ff7558b40004ff7518542006be50d9131005de7399121016bc62d0941004ff7259231014fc7298f41034fc7650d31006bf6450b31004fc7158a4300cfc7058743004fd7418d1013ebf40593102b7d5514c431006df7358f10035bf7650441014fe76d0d32006bf6490e2131f9d5410e3106ede7318d20004fc768c52006cfc7598d21007eb6248110006bc10d9131005bf744853009eed2058b10004fd7650b1000cfe76d8121005fb7048510004ff75d813201cfc7558b4315ebd52d912100cfe7690d400057d75d82311f6be6090e413bf9f5350c43045ec724c71010efa1058331004fd75d81320067f65d8530005f47150831004ff75d8d4200cfd7690710006be53d9121004ff7598732004fd7018e21006dd62cc431006bf6410531016ee61d0a2101cfe75d9221006bf7458d21106df71d8d21004fc7159332034fd71d8141014fe72d8143007ac7250441006de3298f4106cfe73d8b1015cfd72d912107eee42d89402aeef64d0a21004fd7298740036dc4358c41036bc4298742036f74198742006ed63d89410857c755854006cfc7610d1000cfe7059131004fe71d8d42006df63d8941006bf64d8530004ff7358a4106f9c5350c430acff70d8910004fd75d8542006bf64d06210eeee52d893100cfc764c51011efa205804100cfc701854215ebc21d9121006bd53d9121006bd54d912015ebf72d9121006e
  | 14 => 0x3ef865c4110006ed76cca21006dd63cca41007ae5418941004fd71d8d2006ef761987320379d6050c4332dbd7590541004fd75d8931004fd7558b41004fd7198f40036bc7019130036bc721913006efb3058243034bc7458910004fc764c52006cfc7358b102c6dc4118d41006bd54583410067e2059441006ed51d8931036be64d0b10036be6490621006df6390d4206cfc7598f10014fc7458342146ee52d894100cfe7058b4122df671d8b1001cfc75d8d42005df7348540006de10d8d21006ec73d8941004fe7610531004fd7558f10004ff7598742006ec43d8931045ec7250710014fc76d0d32036df7358f40034fc764c841037af7250941006bd5418d4002d7e7510510014fe7258043006dd5418d210057f7558910006df73591313c79f7550c43036fb7058342006ef62cc941016dc62cc931005bf744c5203bf9f5250c43005bd7610e410067c32d9510014fc725824101cfe75d8141006bd64907100079d4310d21016bc6250941014fc7650521014fe72d9310016bc7650941004fd7558a43034ff76d08312ef9e5410e3113efa10d8141005bf745812101cfc75d9121036bc6490e2106ef43158730014fe72d9130006ec75d8941005f9700c7101f6be30d9130004fd7098643004ff7648740004fd7558031036bc64d0931004fd75d92310367e405974023f7610d9510005bc744c51006ebc4359332025ec7259110014fc7258031106dc72d8d2100dfa71c411006eed7298d210aef850d8b1006ede7318d10014fe7359332004fc7650910005dd76cc631004fd74d8d100a57e751052101cfc75d92310aeed20d8910014fc72d9310036bc4398742005df735083117cff7058d20006bf72d9130005f47150e41006dc70d8d21036dc4358f410067f6510d1001cfe75592310367f4359740014fc725913109cff7058910004fc7158243006dc6350521007cf324c6210067c65d8d10036bc6450d30006f721d853000cfe70d9031006dc3258f41006bd6390f42004ff764ca4100cfc70d8d42036bc649053006ebc4359031034bc7458d1006f9c4350f30007af74d894106ebf6499330006bf745912006ede7398f41004fd76cc941006fb7059130156fa2058241006bc54d9131006dc1018d2101cfe7559121005bc744c521004ff72580430067f74d9530006de5018d21126ef2058841014ff7650a41004fd75d9131034ff7650d3200cfe70d9121004fd71d8940015ee7290621006f671d9221006be501912100cff76582310067c65d8930006bf75d91300379e6150c43006df6310d1006ef83058332006dc63d0d10004fd759873201cfc7559332005dc7358520004fd74d8b10036bc64505210059f7250c4306cfe76d07300e4fd768c730006bd54d9131006cc63d8941004ff7159120014ff7658b10006df6390541034fc76d
  | 15 => 0xd7598e4101cfe75d8931004fd7650730007d7618c531004fd76905300c6dc5218d21036bc64d062100dfa70cc510036bc7519121006de5418d21036bc4058043005dc714c931006ef7258910004fd76885400067e7159740147ad7418941006dd6318e41006be76191300fcfe7618d10004ff7558740005f97010d2001cfc755884101cfc755844306cfc7650b30005de73d0a310067f65d8910006de7518d4100cfe70d85431aeef20d89400069c648c531016fa62481100eeec42d8931004ef72591210dd7e7510731004fd70d8e21007ad54d8941007b47150941016bc6250b413bf9f5150c43006bd62d0641004fd7650e210067d7359740006dd5418d4109ef850d8121004ff75588430057f7558121006dc638c540004ff7358b400eeee73d89310067c659853014e7c65505100c6dd2018d21015ee74d0a212eedc40d8d4100cfe70d8d4201cfe7558743036bd7319130227786548110006fb7058d20366bf6510e41006f61018532004fd75185320eeec6258931036bc721913115ebd72d9121014fe72d933000cfe76d0d30006bd54592311f4fe7610d30005fb7050540034fe7498d20005ef72581313b79f2150c43006ee601894104efa6548110004ff7159130006bc64cc53106edf3298e21036be76d094100cfc701852006eec6258831004fc7158b40006ee6518941006dc7358910035bc70d0e43017e76188521004fe7610d2111ef5101854000cff7658221036f74198743006bc3019131004fc76905300067f7259740107cc32d8a3101cfe75d912115fac21d9121036ef4258b430079f64cc931006f671d8f1020ddf7359132005ed7290d200079d6390e4118cfd7098d20006be54d9131004fd75d9332034fe71d9110006ef54d8941017e661cca213ddbd75d0e430067e7518542006f56118543005ef724c621036f76190541004fd70d89430367c7459740006ef6288540006df63d0521004ff71582430079d4310d100367f4359441004fd7650b31055ec72585301f6be4058243006bf53d9130004fd74d8132006bf5119131006bc62d913100cfc705903112e7c65105101bdbc7050c43005df73585400757e7510730014ff7610621004fd72d8540005dd728c531106df72d8d2101c7e75d8f101f5be70d0e43145f57199121005f9708c52006cff76cc91001cfe7558a4105e7e73d953024ef62118520004ff7648540006bd73d9131004fd7518e21006df630c521005be7498530005bf7458910036bd7219121126bd2019121006dc65d8d21006bf2119131006bf71d913117eef2058b30007af725044106ef671d903123e7f10d95100067f65885100367e40594412c7d44118d41004ff755911000cfc7058b4306ebc4359330036df4398c41006bc53d9130005ef724c710004ff7458b30004ff75d8943034ff7650e31
  | 16 => 0x8d412967d10d953006ddf714c43101cfe7518e21006ef6518931006bf64d09301f6bd10d913001cfc75d854200cfc7058b31006bf64d8121014fe7298f10006bc5019131006bc7458e21005dd73d0b30005de71cc93100cfc7098732004fd76d0730004fe764c54006ede73d9331035f67190541004ff75d8e2101cfe7518f10005ef7250710154ff70d91100ecfd76cc621006be521913001cfc75d8f10036bc6450931006df63cc621014fc725834306ef43198732006bd54d9132014fc72d85400067f6548530006dc63581210a67e6548740007d7714c9310e6fa30d813100cfe7098d2115ebf71d9121006bc42d9131004fd7598d21004ff7458d20006bc64cc930006ed51d894100cfc7498f40036bc6450510006be70d9121005dc7358141006de53d8d21014fe7650521006de60d8d21006ec6318941004ff75d8f100067e725944101cfc7558f41005f67110d21004fd7558331006dc75d8d41004ff765093101cfc75d8540004fe76cc910034fd7218542006bc54d9121005bf744c8410079d64d0e3100fda73cc1300067c74d9530034fc745883106ef86058243006bf6448530016ec6288540004fd721854000cfc7058e41005ed729913110cff764c710005dc735052001cfe75d8d421f4fd70d9130107cc324ca31034be76d9130006bc64581212aeec43d8941004ff7458a3106ef83058243026ec42d8910006bf64d89310067d7259740306df64d0f32014fe72d9231006bc6519130106dd52d8d21006ef32185323cebd6590d43016ec62d0910014fe72d91100067c71597400047f7559110015ec72d0621004ff7358b1002d7c7558910006ec63d89410067c72597400eeef20d893100cfc7158b10006dd73d92310067f6559110006bd6390c41004ff7558d21146ec32d8941006dc634c621004ff7650a31006ec62581411dcfd7650d302967f30d9530006be54d91200079d7250c43036be6419131004fd72d93312a67c20597400c7d72118d21036bc70191312afac43d0a2106cfc76cc91006f9c3050c43004fd7598d20004fd721853006cfe76d0b31034fd71593102ff9e6410d32016ec6248510004fd75d9110006fb50d8131006dc7359221007cf43cc93203e7865c41101f6bf30d9130004ff735891006cfc735874020fcc21d0f32036bf7119130006dd4118d41036bf7519131006bf51d9130006bf52d913001cfc7558d10006dd53d8d210a57c7558121004df7359131006df6350d40036be545834101cfe7518d412eede61d0c31106dd32d8d21106dc21d8d2130fd651cc631005f77150d4106f9c4350f31036be6490d32036be641913223e7f20d9510006df6390d21004fc7648530004ff7159131006f671d8e21006be4358a41146bf42592210067f6519130127b72119121006be5418d40006be71d9130004f
  | 17 => 0x4fc768854039ebd6590d42006de6218d41036bf7119121004fd75591210379e7390c4100cfe7058e212eedd64d0e31004ff7359310004fd75d91322eedf4398643034fc7458d211f6bc30d9130015ee72d0e2126edf30d8d20006dc6218d41004fe764cb10006bc72d9131006be5119121006bd54d8141006bc60d9131005f7714ca310067d650c740004dc73592212a67f705974006cff7690e21006ef70d893136dbd7550b41006ef50d89310079c644c93100cfe7058e41004fd7098742006be74d8f100367f415974006edc7018d41004ff75d8d2105d7c7558930116de634c831004fe7198d20005ed728c62100cfc70d9121004fd764ca41004fd7558b43004fd75d9121005bd749853001cfe75593300067c2059441006be54d814101cfc75d8142006df6350d41004fc7650b10156fa405824100cfe7098743005dd71d0d320063c6519130006bf70d9121006be51d913101cfe7558b432c5de744c4310067f21d9530006ee60d894106ef7319844323e7e30d951001cfe75d8941035be74cc8410367d4059740005be76191312c79c4310431004fd768c74006eef3258843014fe72d8f100067d71d9530106de628c531014ff7658a410079d54d8d41004ff75d8141006bf21d9130006ee65d89411ffac2190f4201cfe75d8930036bc641052019cfd76991200067c655913000cfe70987420c6dc4218d21004fd7498d200367e7459740005bf7458d103bf9c5150c4300dfa709054017efa20d81321857c755813206edf7418d2101cfc75d8e211c79f4210f32006f7618c5303af9c5050c4300cfc7059132004fc7650d21036be64d0a3103d7e75d8f10004ef7258443005bd7190f4206cfe73d814101c7c7558d10256f621d852006edf3218d20004fd74d8e21004ff715933012e7c6510530005ef7258d41004ff7518540005df73485302a67e1059740004ff755804109efa20d8121004fd7298f41036df4398f42036f77158740006de42d8d4101cfe7598743007ae54d8941004ff725834306ef43158643014ff70d912006cfe7359031006ef75d8941004ff7258c41126bf7650b4117cfd7298d20004fd76d0c3106fcd7210f32006be545923101cfc7518520036bc721912106ede7318f10005ef725062127ebf40d912001cfe75d931016df77159121006dd6318d10004fd760c740006ef7258d21004fc7158b43004ff71583420067e325974006ef67118f10006df54d8d4100cff765833118efa2058332036be6450b100069c63d09410067f65d09300bcfe71d8f10014fe7218f10006bc75d9121005bf7458d2101cfe7518520004fd72d9130015ec7250621236f710d852001cfc75d85202c6de5418d41036bd7519130007cc628c531006bc5119131036ec4258b4114e7c6550530006de3218d10004fd75d8930006de501
  | 18 => 0xc70d8542035bd7690f420367f41594413af9e2050c43005f7715893006cfc7690d21036fb4058043065ec724c730014fd74d8142014fe72d912006cfe73d8542014ff7018d202a67d3059740006bd6410f10006cc6388521015ee7290d42006df75d8d4100df870505401bebf1019130006bd6410631035bf7150441004fd76d05200c7cc3218e21105df734ca31004ff7258740006df6398d40005df7350621006bc52d9131004fe76d0d31036f77158743007cf628c53100cfc7650d400057d751043123e7f70d95100067e1059441004ff75d89100067f7558d2000cfc7358b30014fe76d89310eddf724c931005dd71d0c3106cfc7598d10006bd51191300bedd3018d1000cfe7059121006de5118d2106fcc32588312fede644c931004ff7458831015ee728c6210079c744c431036bf7519121006bc644c52106cfe7318e21006f671d9231146bd4259221005ed71cca210079d4310e310067d654cb40006de6350e41006bc60d91210079c4390631004fd75d8941006ac64885210c6ec215883101cfe75583420ecff7258d21004ff75d8530006df63cc9400067c215974000cfe70d913206dde7310431005f771581322c6dc4218d41014fc725903101cfe75d8d2100cfe7058f42004fd7690f10004fc7650e2101cfe7518d42036bc6410d30004ff7359131107cc21d8d21006dd51d8d4101cfe7558b30005dc7348740006bd50d9121005df7350710006be7619131004fd7418e210d57e75106310367d4059441006bf645052106f9f6050c4300ff361c41100057d751854206f9f6250c43005ef7258141005f9709054001cfe755834101cfe7518542006bc32191300069d6410d32014fe76d8941004fc7158b30014fc7650941014fc72d8d10035bc744874000cfe7098f4101cfe75d8542004fd7298e41035bc744c841036be6190e41006df4358831005dc7359121016f8764811009cfd76485102967d73d9530006dc634c5212f79d5410c31004fd75d81310067c65185302eede74d8d41036bc6410731006be50d9121004ff7559121006ed6250a410067e3259441005f47158943004fe7688530126bc5219121146ef20d8941037b77150441006be75d9121014fc7258c410367e43597400057f7558d10006bc7458d20006bc648c5311feec2198f420067c655891006ede7398f42006df64d8d21006bf6310d420de7e65cc7401acff7259120006bf6490520034fe74d8e2100cfc705912106cfe73d9110006bf641052106cff7690f10006ee30d8931036be64d083101cfc75d8141006be54d9132004fd71d9332006df63cc941005bf744c740004fd7118d2006fd830cc530006de7618d4106cfc7610d20006bc10d9121006ef7258d202967c30d953001cfc75d91100067f65cc53000cfe7058a31004fc7648540006bf64cc530
  | 19 => 0x9131006dc6350d21005de76cc931006de60d8d41006dc54d8d2115ebc52d91210fef86058231034fc7458b30116ec2198d21006be54d91210067d654c84106cfe7318d20006ef65d8931005de731053000cfc7018d41014fe7218d10004ff7558743034ff765051014d7c75581410073f651913001cfe7558a43004fd7598d10006dc5218d41004ff7258643014be7690d42004fe764854006edc7018d21006de634c8410079e5319130006dc6390521004fd71d9132004fe7118d40006ee30d8941025ec724c510034fc7458b31004fc71583430e4fd7158f100067c215944101c7e7518542227f251481100079d531913006cff7690d21004ff725834106ef86058031036be6450a31004fd7650d201c79d4210f32004fe76d093000cfc7018d42036bc6450d210067c6599110006df6518d21006ef53d8931006bd6419120036bc64d0d310067f735944100cfc7458f40036bf4158841005bd7190d420f67c654c510016ec62d093100cfe70185430057d7519221006bc63d0941014fd760c621006be20191310057d759853006cfc760c540014fe76d8940007b464cc531006dd6318f102c79e5410c31036bf6210d42004fc768c540006ed52588312c6df4018d410edee729913106cfe7398d20036bc6490521006dc1018d41006ec53d89310067f6550930014fc7259231006bd54d9121146ee42d89410069c6350941005dc7350531014fc72d8d4101cfc75987402ff9c434c841004ff7058843124fe71d92212967e70d95301f6bc50d9130306dc64cc931006be60d9131006bc6219130006dd50d8d21006bc51d913006edf7018d41006bf6519121004fd7598730015ec724c5211bcfe7690d30004fd75d81212ef9c4010e310063e4259441005df764c43115ebd20d9121004ef7258d10006bc6488530006ee73d89410c6ec32185320067f6558930006bf6450d31014ff7658b3100df8704c510006ef6258141004fd7558831004fc7158f4200dfa700c54006f9c6550c430367e4359441006bf645893037f9d5410d323c5bf7550c4306cfc7598c41006bf6450930004fe76d0e21006ef50d89410079f7350441015de72d0f32014fd7018d20006de5118d41006bf6450621004fd768874000cfc7098e41005f77150b31006dc60d8d21006dc32d8d41006de65d8d41006bf6490531004fe76cc540006bd7690c412fedf64d0d32034fe7498f10004ff7558e21017cf63cc932016de62ccb31036be721913015fac42d9221004df7359121006ee70d89310067c7558332004ff765053010cfe760c530006be4358841005dd7310730004fd764c740005bd7498d21036bd7119130006bf64d8131036bd7610e41006bc65d9131006dd7018d21007ac6290541005f97010530004fe76505303b79e7250c4301cfc7558331014fc725913000cf
  | 20 => 0x6dc4018d2100cfd71d89102c5de7410c31004fd76ccb40036f44198743006bd6450e31036be751913006fd57110c31034fe74d8931034ff765931006fd6634c431036bc4358b43004ff7158b43006bd64d0831006dc6390541036be751912120eef2058b4306edc630c540006df50d8d41004ff7598743004fd751854306fce62ccb31005bd72d0e43004fd74d893006dde73d0831014fe7498f42004ff70593320059c744c43124ef52118520004fe7650d21006bf6458121006df7358d2006cfe7610730006bd64906311defa60d8143006bd6410d32015ec7250521004fd768c54000cfe70986432ef9c6410e3106ede63ccb10006bd64193100e4fd7198d10006f970d8b1000cfc7098643036be6419110204ff73591300aefa10d8b100067f658c53000cfe7098e41036bc71191300057f7558d400067f65485101bebc4018d40006bf648c530004fd7558643144ff725912106eec32588430067c73d9510014fe72d9031007ac6418931005ef724c73000cff7658243036bd76d0e4301c7c75582431bebf2019130006ef52d893100cfc76cc510116ec62cc531004fd755824101cfc7558743014fc7258643014fc7258331106dc3258a31006bd74d8f10004fd75587402ff9e5410d32065ec7250730034fd73d81432c6df4318543005bf745893006cff7598f42014fc7258243036be751913100cfe7058c4106cff7018d1015fb721d9121005dc7359221004fd7018d210067e62d9510036bc6450621005bd76d06410067d7359441004f47159132014fe76d89430069c6418d2100cfe70d8943004fd72987431fdde7610d3206edf7518d211f6fa4058243014fc72d8543006dc63d894101cfe75d813206cfc7650730004fd7298f10005ef7258543004fd701854306cfc7518d42036be6450831034fe7418d200379c4350d42034ff7650d3000cfc7059221004ff71593321e6ee42d8943306dd76d0f3223e7f30d9510036ef42588410067f725944101cfc7518532034fc745833200cfe76d8132127ac4219221005f4714cb41004fd7650f10007b67190e410c6de32588310079e54d8d41006bf74591310057d751053006cfe76d0b300067f7559110017ce73cca21005bf74581320379f7350c43006bd75d912100cfe70d8d410363c4359441006bc70d9121005df764cb31005f77150d31005fb704c510036dc4358f4006cfc7359221006df74d8d4106efb3058031005dc7358542006bd6390e41034ff76d0b310ecfd7198d21006df20d8d41006dd72d8d4106cfc7598e41006de52d8d41004fd75d8b10015ee72d052100cfc74d81410fedf30d8d102eddc74cc631006df635814106cfc7358342004fe7650b1006cfc7610e2100cfe76d8131004ff7650c31006bc40d9131014fc76d0521004ff75d8520006df63d8121014fc72d
  | 21 => 0xc7458d201bedd3018d40007cc724c431006df63105210eeef21d89310069c644c931016ec6250931004ff735912120dde7410d320fdf67118f102967e40d9530006bc2019131006dd7518d41034be76d9121005df7358141006be651913000cfc7098443004ff75d9221035be7390d421fedd3298f42034fc76d0931007d532cc531005f4714c8411f6bc70d91301ffae7290d42014fe7258743004ff7558331016dd76ccb3101cfc75d89431bebe3019130006dd54d8d210eddc764c93106fcc3290d32004fe7690d1006cfc7358b41006bc63509412efd671d0e31004ff7458e21015ee72cc521006df63cc51006cfe739874006ef77158443035be74ccb4025cfe76cc930006bc73d912100cfc7650510004bf765044109efa10d8121004fd7558041034ff76d0b10014fe7218540014fc72583410c6dc321853206fcc324c831014ff7658a3100cfc7058f42005bc7458532005f7714cb41004ff7158b302c6dc4018d4100cfe70d9221006df63d0e210067f21d9510036ef7258b40034fe741852015ebe72d9121004be7619131006dc634c940005f47158930005f77150e41007af6290541004ff7558b43005ef7250e21164ff7159110005f47158132034fd7359330006bc4059231004ff7058c410067d74d9530006ef53d894101cfc75d8d20006ef62cc910006dc10d8d21036f74158443006ef51d8931006bc64d853007df97099120004fe7690d31006df6350521004ff725833106cfc7610431004fd7558342036df6390d43105dc7210e31004ff7558a43006ef62d09310cd7c755803100cfe764c510004fd71d8d40306de64ccb31006de30d8d41006ec638852117ef86058132105de7210e31014fc7258740036bf4258443004ff75d81431ee7c6550d10005ef724c510006be6519121034fc71d911001cfe7558221006bd71d913100cfc7018d2122ef51018520034fd7690431004fd760c540005dd73d0a3101cfc7558732005f47150941004fd75d8530006de50d8d21034fe74d893000cff768c71000dfa70d0d301e6bf42593320047d7598d10004fd71d81430067c6599130004fe76d0d101367c65905100e4ff7058d10006ef7258443034fe7418530006ed71d89410f67c654c53001cfc7558d21006f4614c53000cfc7059331014fe7298d1006cfe73d8121006ee6418931034fc76d0b10106de7398732014fe7258f4101cfe75d9110005ef724c521004ff7458910014fc7298f1006cff7518d21006dc4358a310d67e658c740014fe72d8530025ec7250510036f840580431f6be20d9130106cc628c531006fb5058b10104fd72d8d210067f65d091006edc6390d4001cfc75986430057d7519310004fd7688530005ef72591312967e20d953023e7d10d95102eedd7610e31004dc7358910004fd75d8143155f67119310
  | 22 => 0xc910004fd7650d2101cfe75d8520006bf64cc931014fc7218f10034ff76d09103b79e3250c43034fc7458730004fe71d8d20035de7390d430efcc624c931006ec53d8941005bc7458d1006cfe7318f10006dc53d8d410c5de724c431035bf7650b41154fe7619110006be4318542004ff755874200cff72d8d20006bc6458131006be1019131006f76198540004ff7059031004fd7559331005ef725052100cfc7650d3000cfc70d9231006bc40d9132005f77158d42006ed6288710106dc329873201cfc7598743125bc7290c4123f7410d951006cff7598d200067c65d9110006ef51d89411feee5258a430079e6390e411f6be6090f4223e7c30d9510004fd7559120035bc744c540014fc7298d1000cff769071001cfe7558041014fe72d8141004ff75d853236dbf7550b41006be42d9131006bf73d91312afae64d0a21006ec30d89310067f6518d101ee7c6550d3006cff7218d21006dc4398732057cc324c93015fae4258a41036df7358f41006dc6350d420e6f850d8131006f610d8532014fe725824106f9e7410f32005bf7448740005ef725073000cfe7650d300079f64d0d320079f6390541006bf644c521034ff7610730036be64d0e3100feb7248110006f771591310c6de5218d21125be725044101cfc75d8530004ff7058d21106dd20d8d21006be3219131015ee720c5201367c65905300c4de7398d21006bf54d913106eef3258a4306cff7518d4006edf3218d2106ef6638c4310057f7559130016ee6250a41006ef52d8941005df735891006ef83058031006f461cc520036f671987400067c72d9530004fd7518d4100dfa7010d20004fd75d8d4006edc6310e21034fe74d85203879e4010f32007ac64d893101cfc7558b100067d75d8f10006ef62cc53107dec7258540034ff76d0d10356ef4218542004fd72d8143006bd5458740004ff7158f42106ec6258a310c4fe71d8e2100cfe768c530006dc4318532004fd7650531015ee73cca2106cfc75d9331034fc764c74006edf7218d2119ef8605814230fd551cc631126be5219121004fd76cc520125ac7250441126bf321912100cfe70588310067f65d0d30016ee62d0b31004fd76d05301bebf501913006cfe73d9310006df638c5200079f6410e3106edc3218e210067f65cc510004fd71d8142035bd7690c41144fd7699221005bc7150b4100dfa7010710125be7290c41005df735812101cfc75d9221005de73d0930004fd7598c41014fe725873000cfe70d9110006bf64d0d30115ec725073101cfe755884301cfe7558043004ff7558643006f77158d100067d725944106ef576cc6310bcfd7018d1006ef43158443006f41018532006f76150540006df75d8d21147ac21d094101cfe7559221006be6219131036f771587420379e6050c43006ed62ccb41034f
  | 23 => 0x34fc76d0d10036bf6590f42017e661d0a21014fc7259331006ef70d8941006de5218d4106edf6410c31106de32d8e21007cf724c43101cfe7558343006df6358121014fe72987430057f755824301cfc7598730005bf744c71016eec3258b41014fc73d8930036be6490f1015ebf649052109eef2058b1001cfc75d894106edf7418d41004fd76d0a31006ec51d89312a67e705974001cfe75d923105d7e7599130005bd7110d4215eec6258a410c5df734c831006ec50d8931006de75d8d41005bc7458910146ef21d89410079c7350441037b661d064101cfc755912004d7c7558d201967c65cc91001cfe75d8d10006bf65d912100cfc705923123e7e70d9510007cf73d893101c7e76d951001cfe75d8d20034ff7610431056ee32d893011ef81058041016de624c93100cfa76c4110006ef6250931005f97090d4013ef71058740004ff7458d1002e7e71d9510006ef641893100cfc70d9331004fc765053006edf6210d32036be5458740017e671885211f6be40d9330004ff7158d20004ff7458d2103d7e7519310005f57190d41036bf7119131007d7734c43123e7f71d9510014fc72d9031034ff765933109efa60d8121034ff7659231004ff7158b400079c7150c43006bf70d9131145ee7298d41006bf5319130006bc6418d2106cfe7688730034fe7418d10004ff7258443035be74cca41036bc6490520004fd73d9110006de6518d21006f421d85300367c4159740005fb704c930016ec625094106edf7218d410cd7e7510431124fe7690521034fd7218d4206edc63cc941107d721d8d21005dd731063100cfc7458740004ff7558221006bc32d9131006dc7359121006bf65d91301f7ba4058243006bd6450831014fe72591100067f65509100c6de4218d21004ff7259330034fc76d0530016ec62885301c4fe7690d3220eee3258b43036bc64d053100dfa708c530235f7715891015cfe7610521106ec628c531004fd7398740006bc5319130004ff75d9120004fc7158f403af9e1050c43004fe76d0a3106cfc7358910004ff75d8d40004dd7610c31004fd74d8520256f521d8520004ff7458f10006be51d9121006df53d8d41006dc6350d4106cfe73d903101cfe7558b310379c4350d402aeed76d0a21006bf73d9121004fd7690d21005bc7458121005ef72505101f6be4098f40005f970d0d300bcfe768c510026ec32d8910006dd63ccb10036f6719874201cfc75591323af9c2050c4301cfe7558c41034fe76d9131006ee64d8931004fd76993311f4fe7619130006bd641923101cfe7598d21006df5418d21006de54d8d2101cfc75d8121006f77159121104fe7118e2106cfe73d9121004fe7648530006ef6250940036df4358f42004fd7198f42006bf6410d2039ebf6590d42004ff76907300aef81058221004ff764
  | 24 => 0xc6310d21007e571cca2120eec2158b433bf9d5350c4301c7e76d95300c6de2118d21005ed72d0d32004ef72591310067c1059441006bd6250441006ef73d8941005ed7290e2106fd67110c31006be32d9130004ff7258e4121f7865c4110014fc72d9120036df4358c41005df7350510036bc7519131014fc7298443006de7018d2106f9e5350c4300ff271c4110004fe76905202eedf42d8d41004ff7690431016dc62ccb3106cff7690d20105ec7250631005f77158d2006edf3218d42036bf75191300079d5418d41004fd73d922120eec62d0d3100cfe70d9331007e462cc531105dc72d0e3100cfc765094006cfe73d891003efa65c4110006dd5118d210067f658c510004fd72d8131004fc7158332004fd721854306dbf7350c43005f576cc6313b79c2150c43006dd71d8d4106cff70d9130004ff7558f42007cf624c93101cfc7598732016ec62509400063f65d9130037af6210d4206ebc64593320367c4159441004ff7650930106dc42d8d2106dbd76d0e430079d4310d320047f7558221004ff764c941004fd755833206cfe7398d21126be211912123f7a20d9510006ac64189312eedf6410e31004dc7359110034fe74d8b10036bf731912106cfc735824300cfc70d8532004ef7259110036bc6490d31036bc6450d3206f9c4350c3106cfe7610431004fd7018d42037b76190541306dc43d89431bebf301913001cfe7558b10006bf5119130006be5319131006bd521913101cfe75d8143036be7219131004fe76d0d2006ebe6350c43005bc744c5301867e654c8410edec72581310079c434ca41006bf5219130006de4218d4106cfc75d933201cfe7598d10006df52d8d41036fb40583421f6bc20d9130036bf4298f412967c20d9530005f9708c710004fd76d0d100067c65d913001cfc7559331004fd7610730006f761cc52006ef860583310367d7459740035bc744ca41004fc7650f10036bc6490731025f97098520036bc7019121005bc7448710036be7219121006bc2119131004ff7158332004fe76cc940006bf7459231005be71d0e43056ee62d8930036fb7058341006bd5119121034fe7418e21006ef72591310c6dd7318532006bd5319131005bf744c62100efb6148110006ec75d8931005ef7250731036bf6190541006bc644c93100cfc7058443004ff764cb41015ec72cc621014fe7258243014fd7610621006df5418d4106ef73198643104de76cc931006de75d8d21004fe76d0531004fd75d814206eec3258a43005df735073006cfc76cc94106f9e6350c43004fd75d9310014fe72d8d1006edc7218d21006bd71d9130127ac421062106f9f6150c43006dd638c621106de76cc93100cfe7059331006df51d8d41006bf6450d2106edc4398f40014fe7398732037b66190c4101cfe755823101cfc7558730
  | 25 => 0x9332004ff75185300069f6418d210b57e751922106ebc6499330004ff7458221004ff764c7401feef2058a4301cfe75d854301cfc75d813223e7e40d951006cfc76cc94000cfd7688710006bd64d0b1006cfc7358b402fedc644cb311bebe6010d42006bf6490d10036bc6490e310067f65d0530036f84058341004fe76cc520006ed73d894101cfc7558742056ec21d8930006bd64d0731006df21d8d410079e5418d41006bf64d053006edf7118d21014fc72d8131006bf2119130006dc30d8d41004fe7690f1000cfc7098c41006bf6458530006be651913106ddc7210c311f6be6090d43005ed7210d21004ff7258743006ec51d894100cfd72d91200367d745944100cfe7058743014dc764c931004ff7058a31006bd54582431f6bc6090e41004ff764c54000dfa7090d40004fe76d0d2106ddc74cc4310067e71d953015dbe7210e410067f650c530005dc7350710004ff7358041004fe7650520004fd72d931001c7e7598d10006ec50d89410067e62d9530006ef6250941004fd74d85320067f7558332127b42119121034fe76cc841004ff725824300cfe7059231006bf640c5303d79d53d0e43014fc7218d201ce7c6510d10006bf64d0510006ef75d8931004ff70584430057f75580310379e6250c43006dd5118d41006bf745922106edc7518d2100cfc7059332034fc76d0d2100cfe7398730006be62d9130036bd70191210047d75d8142036f7419844305d7e75105301f6be10d9130006df53d8d40004ff705884106cff7598e41005f970105202c79c4010c310067f6558530156bd40d9110005dd7110f32006df634c521034fc76d0520034fe7688740036bc6410d21006ef64d8931006bc644853006ef46158730015ec7250e2101cfc75582212967e10d953006edd7610c31004fc764c94101cfe75d9331004ff7258d1006ef4319844306cfc735822106fda53cc1300e4fd7698f10006de51d8d21006bf20d9131006ef624c9300c7d42118d2100dfa7090520007bb64cc1301bebc6010d4206f9e6410f32036bd7019130004fd72d8d4123f7471d9510006ef6518941016ec62cca31036bc64d09302967d40d95300077b65cc130004fd7558843156fa60d82410367d41594410057f7559110005f47150a41006be73d9121014fc72d93301bebd1019130006bd70d9131004fd7558b31035be7190541006f7619854301cfe7598f42005df73505211f6bd40d9130006bc40d912106ef571d9331004fe7650f1006ebc6459330006dc53d8d40366bd6510e41035bc745824300cfd7218d202aeed64d0a211967c65cc930005ed720c5202ff9c64d0d3228fd953cc130004fd76ccb100067e32d953015ebc4258a4123e7e20d9510004fe760c540005f972c4110036f741587420d57e75192310befa20580310aeef20d891006ed
  | 26 => 0x20ebd74d8d42306dd6410f320067c21d953006ebd7498d212967d30d9530006df6390521004ff755922106cfc7359110006bf50d91310057f755893000cfe70185321ce7c6510d30014fd7690621006bd65d9130014fc7458f42006df5018d21106dc628c53100cfc7018543014fe72592310079d4310d3000cfe765051000dfa700c5201f5be76191300067f7359740126ee325884101cfe7558841034fe7498e210067f7558241006bf5019121004ff764c9401f7b830d9130006be30d913106cfe73d93321867e654cb40005de73d053101cfe755883115eac629054101cfe7598d200067f6590d300c6df2018d2106cfe73d9130125bc7250441015dc7210d322c6dd6410c31014fe72984431fedd73d9132146ec6258941004ff7648530006bc72d91300067f72d95300067f654c930005bc7458132004fe7198f40006df74d8d21006ec30d8941004fd71d9120004fd7298f40034bc7458e21034fc764cb41106dd72d8d21014fe76d8930006dc735903120ede76d0d32005bf7458d20004ff755804300cfe7690540126bf2019121004fe76d0f10006bd53d913001c7c7558221004fd75d91300067f6598d1001cfe7558910006be6350b412eedf71d8d41006ef43d893115ebe52d9121006bf644c93000cfe70d8d21036df4358f41005dc7348710006bc21d913001cfc7559110004ff75d8d41004fe71d894301cfe7558732036f84058342006bc64cc530004fd74d81210b67c658851006ebc649933100cfe7018d21004fc7690520004ff7458730006bd54d933109cfd72d8b10006bc6458d21005dd73d08310befa405803106edc7418d21007e762cc531206df30d8d400067f7558d10006de6018d41014fc71d8910156f81058241006df6398d10004fd71d813201cfc75d8532006ed70d8931006be65d9121006fb50d8143004fd72d81410c5de7210c31004ff72587300c6dd7118d21004fd7558d10015dd7610f32006f6511853201cfe75d9330006de6518d41104fe76cc931006ee40d8931004fc7158d20014fc7650d42004fd7518d2006f9e6410c31014fc72d8530004ff75d8941005f97090520004fe71d8d4006cfe73d81420057d751052015cbe7619121005f77150831014fd70d8d20004fe7650e2106ef8605833206cfc76cc5401bebc3019130036f74158743035be740c540006f970d9310004fd76487400057f755813202d7c7558d101dedf3058f40006bf6410731036bc7319121006f7211854306cfc7598f410067e74d9530014dd7610f3206f9e53d0e43004fe7610d20014fc725804106cff7610d1000efa76c41101f6bf6490d30037ac4250940004fd7559130006bd651913106ebe435933101cfc7559221035bc7210e41227f15148110345bd755094106ebc6459331006bf645893101cfe7558332004fd755
  | 27 => 0xf65d0d10006dc40d8d21006df5018d410369c4358f420057f7558530006bd7690f42004fe76cc941006bd6450b1000cfe7098c4100cfe76d814300cfc72d8121007cf32cc6213bf9d5050c430067d654c74006edf7018d21005f7714c84101cfc7598742034fd72d8542004fe7610d31034be74d8f10116ec4258b31036bc6410d2001cfe7559132006be43d8943036bd73191311dcfd769933001cfe7558331006df63d0d10034fc76105300067d74d9510006bf75d913101cfe7518d10006bf6490e3101cfc7518542006dc50d8d410373d6590c41036bc6410d10004fe7690e21007cc43cca2101c7c7559110015de7210d32006be54d9331004fd70d9131004fd75d8910006dc634c510006bc51191300079c439043115ebf32d912113cfd76505103c79d7550c430aefa60d82210c5cc724c431004ff705883101cfe75587301bebc5019130006bd5019131005dd73d09300fefa3058231014ff764ca31036ef7258b43005bf74585320079f648c531036bc6450930006ee20d89311feee4258a4306edc3218d412977830d9530004fd7218d41114ff7158d21006de3018d21005df7359121004ff7058b3101cfc755833206cff7598d21004fd7498d2101cfe7559310004fd76d09100069c64d8d21034fc7650531005f4714c9310367d415974009ef85058b10005bc7150c43005bf74585300d57e75d8231005dc73506210067c6559110034be7498d21004fd73d8b10006df65d8d21004fc7158342006be30191210bdf671d8f10034fc7610710006df72d8d41014fe72d8d40005f47158d200057f7558221006f410d853201cfc75583420067e74d9510034ff76d0b3015ebc72d9121006de638c621006dc51d8d41006dd6318d40014fc7259330006fb5058043004fe71d93321e4fd769933201cfc75d8143004fd7558f4106cfc7518d21006df6350d420acff7258910145bc765094106cfe73d894000cfe7058d210e6f86058131004ff7158343156f51098740007cc6388521006bf65d9131006df6350941036be7019121004ff7559031036f44198742034fc7158a4100efb63cc1301e5dd73991320367c7459441006ee20d89410fefa60d823100cfc7098f41014f87648110006f76190540006f76198542004ff7650910006dc6358141005ef7250631006df6350d212a67c1059740006df630c520004ff7688740006dd7218d41005dd7390631005ed71d0a2101cfe75d854006eee72d933101cfc7559131004fd76990310367c4259740007ac6488521006bf6418d2100cfc70588410067c65d891000cfe70d853201cfc7518540006dd7118d41004ff7558b3006f9c6250c4306ef46158732006de72d8d411c6ef2158843006ac64d8931006f76198530004fd7218f10006dd6318d2101cfe7598742006bd64192211defa30d8143
  | 28 => 0x8d411bebe6010e41006bc531912106cfe73d854021ff251c411000dfa708c5200e4fd76cc710034ff76d0a31005f571d0e31006bc648c53015dbe7290e4106cfe7318540006bf6410d31006dd630c621004fd7650d10345bf7550941004fd74185201957c755833200cfc70d8941004ff764c5200067c74d951000df8704c530006df65d8d41006de65d8d21004ff72582310e6fa10d813115dbc7290e41006ed624c841004fd741853200cfc7058843006ef7259132006de7218d4115eec2158a41006bc645893020edf32d8d42006de32d8d10016f8624811006cfe73d89410079c6418d210c6df764cb31014fc7358732004ff7358b41006bd51d9121006be5458243006ef7259121004fc76505202fedc4358a431feec6290d3106cfc7610d2106cff7598f40004ff7558443336be6190c41006ec62581310067d715974001cfe75d9132034ff7659330007b77150941006f76198532006dd62cc631006bf7458e210067e73d9510036bf701913006cfc735824106ebf7459332006bd6419110004fd739874210cff7158d10006fb7058d1001cfe7598c41004ff7158a43006bf53d9131004fd76d0930034fc76d0f10005bf7448710036f6719874301cfe75d8910005df7350631006bf6450d3200cfe70d854215ebe6290541004fd7218d40006de3018d41006be75d913006edf3098f102967c73d9530227e95248110006dc7359110014fc764c931004fe7198f42004ff7558c41004fc764c94026edd30d8d20034ff76d0d2116eec62d05310367f4059740006be53d91300ecfd764c521006bd52d913019cff7059120005bc7150941004ff705864306cff7610d2006cff75d9031034fe74d8910004fe71d8930005dd731043100cfc7458b4023e7c20d9510004fd7559310006ef725911015ebe42d92212aeef43d8941014fc72d8f10006ee40d894100cfc7098d21004fd74d8d21004fd74d813119ded7299120006dd6318d2006cff7598f41004ff75583432975f73d9530006bc53d91310c5ec724c431014fe7298c41004fd755923107dec724c540004ff7558f40005bc7458930004fd73d93100367c4259441006bf6410d21036fb40580411d57c75582430fef5109873001cfe7598e2115ebc32d9121016ee624c8411fcfd72d913201cfc7558f10014ec7258d10004fd7610530004ff7458332276dd32d8d20014fc764c521005df735073101cfc7558e410067f65191100eeee62d89310b67c658853006edf3018d20014fc7258730007e671cca21034ff76d0d2001cfe7558e4101cfe759874006cff760c7400073c65d9130014fc76cc521005ef7258d1001cfe75d8e2106cfc7358341004fd76cca41036bc425884106cfc76cc520004fd7518f100067f7559130006bf7458d10004fc764ca411e4ff7259132004ff75593320067
  | 29 => 0x36bc4358f4201cfe75d933206edc63cc621004fd7650a31034fc7458a310c5ec7250431065fb7058d20004fe7650930004fd75d8532005bc74487302975e30d9530036bf419874206df7734c431006bc64d8d21004ff70587421debd4059330005bf744c52106edc3298f410367d43597401e6dc73593321f6bd50d9130045fb70585200067f65d051009ef8605812101cfe751853206cfc7358a41004ff7258241014fc7158221035bf75d0941037b66150441034fe74d8d202bede614c4310057d7598d1006fd6534c4310067f659853006df7764c4311f79e30d91303af9e5050c43006ef62581312ef9c43d0a31004fd76cc540004fd75986430067c65d8530006de40d8d41106de52d8d21005dc7358910034fe76ccb403af9c1050c4315eee62d8a41006bf64985300857c7558d40006bc75d913001cfe75185400067f650c510005dd7310530034fc7458910004ff7650d10006bf54d91212aeef71d8941004fd70d9031286bf42d91200067d72d9510006ef6248510014fc72d9231004ff7058743004ff75d9130004fd73d9121036ef7258841006ef62d814101cfe7558443006df764c431055ec724c530006dc638c520005ef724c540034fc745873206eef725884301cfe7558e21004df7359110106df32d8d21004fd75d9031005dc714cb31005bf744c73006fd4438c431005f57190e41026ee62d891000cfc7058b41036bc6450531005bc7458e21005bd74cc9400079d6310d4207dec7250540004fd7690d200eeee32d893106cfc764873006cff75d9330006dd6318d41006bf51d9131004ff7058f42006ed651893106fd4328c43123e7d40d951006cfc75d90310067f6558d1023e7e10d9510004fd7559330014fe7218d41004fd701853201cfc7558d20104de7618d21105de72cc63115fb421d9121015de76d0d32014fe7298e41004ff7059231014fe7298f401bebe2019130004ff764cb40006be5019131004ff75d8542126bc3219121014fe7298643005dc7358121036be6410710106dc52d8d21006ed6518941004fd73d854201cfc7518543126ec21588412a67d2059740016ec624c9310057d7510531006df7358d10006df5318d2106cff7610d2101cfc75d8930006bc1019131014fc7258f400067f65d893006f9d6410c3100cfe74987400ce7e650c740004fd75d922101cfe75d8142145ec7258141005f9700c540005f47150e31055f97098d2000df8704c930034fc7458d1000cfc70d8e21004fd7610e21005bd740c540007cf6318941005df7348740046ee62d8b10006de3258f41006bf6410e2100cfe7018d10004ff7358221006bd73d912106edc5318d210067c75582410067e32d9510034fe74d8121036bc6410531006ed70d8941006bf5319121006bf64d893015ebe21d9121006df7358e21006de20d
  | 30 => 0xd30d9510015be7690d4206edc4398f4120cff735913201cfc7559031006df7359231004fd7418d2015ebe4258a41004fd768c520004ff75591201f6bc6090d43126bd2119121005bf7458520004ff72591310c6df4218d210367e4159740146ec20d8941006ee65189310367d4359441004fd731854200cfe7058b3104d7e7510520005dc7348510034fc7458b100fedd30d8d1001cfc7558a31164ff76507100057f7558520126bd7418542106de42d8d2106efb3058043004ff7059131004ff7650b30004fe76d093106ebe435933006f9c6050c43014fe7259130006bd54d8540006fb705891006ef73198730016ec624c9410067f6590d10004fd7518d400c5dc72d0c31006ec70d893101c7c7558d202eedc648c531006bf6499310014fc72d9331004fd7598443006df638c54001cfe75591200067f654c910006bf6458d21004fd73d8910004fd76d0d200367e41594410eeec20d89310c6dd2118d21036bc6410e21004bd74d8f10004ff75d8d2001cfe75986430067f7059441005ed72d052106cff76cca410067f755824306ede7398c4106eed7218e21004fd7610d21014be749874200cfd768c710005bc7448510026ef21d8910004fd7518540004fc7650d20004fd7598f10006bc62191310067d75d8142006be70d9131006bd6410621004fd7218d10005bc744c520006ee43d8931004fd75d8d10036ef4258b41147ac62d0941036be7019130014fc7258e4101cfe7558f4101cfc7558b310079d7050c43006bf511912107eec21d8940005de71ccb310379c4350d411feec6290d4132ebe6150441034fd71d894101c7e75d8142006df635894100cfe7059132004fe764c91006cfc7358643006f47159132004fc764c540004fe768c540036bc64d0d3011cfe71d9310006df2018d410079c6390541004fe76ccb10004ff7259110006ef62d0910004ff7158f4000cfe70d893106cfc7690d20006df5118d21005fb704c53000cfc7058a4300cfe7058443036f840580410b57c7558221005bf744c510004fd73d9120006f4610c520036ec4258b40005be74d8f10006bf64d0931034fe76ccb410367c4059740006df54d8d2100cfe7098732006be43987420eedd3258e21006ef62d0531006bc54d91300c6df5218d21034fc745833106ddc734873013df5719911001cfc7558041006bf52d9131126bf5219121007cf724c93106edc5318d41125f671d92212b7d5534c43101cfc7558343005f771591320369c4358c41004fd74d8910004fd75987432eedd76d0e310079f7150c43005ef7250d42004fd72d8543357e7411894100cfc705913106edf3098f40006dd634c84115ebf20d9121036f44158742006ef73d893106cfc7518d1015fac429062106ef67118e21005dd71d0f32005ef724c431004ff75d9131004ff7259310
  | 31 => 0x60006000002812c00b00005d800c002282000804600800d80f4026026136000002000239280100020210000004e08001241007000a00300b801800e12b015817401c00003380680a000000b80000380010038000342009008802c1fc00300a807c0020000000e640020b6222805800e0900004dcc00002f00c800088600000380000d8002015000003c0010000030004000000089c05000000080481ec0020048510028000000000c000007000004803e00a000815802600000d8054002007006012c3820190cf001c0e203d046000401401b00301a800600009a805801400100005f000002d0058384016005001800c06210900400001a400256b00f000402903b812800002a01b022008013b012004403806f00b80580160f004980000004c704702cc00202000f8088106003008000800400100c0120000144003800003c00b002010400001100a000006a004028805c40e02c011800000a002002803c04e11500000c801802a01580380400000010010008006040000c002005000007407c42300901a400803d00000100d602e00500b009000000280540000000028e0c00001a0008000016016006000000000000090c000200702e828403602100580042a40ad014fe7259331004fd75d8d20286bd42d912000cfe70d93320067c7259441036f44198443004fe71d9130006f671d931000cfe76d051019efa20d8142006be30d9121006f46150540006bf21d9131014fc7298643336bf6590e41126bf211912106ddd76ccb31004fd7098743006ed52d8931004ff7358742006bf6519130006bf641053000cfc7098743027e86248110015ce72d0d32005ef7250540005ed72d0d20014fc7218d41006bf64cc531146ee32d8941014ee72d93311dcff7059130014fe7218d40005ef724c530006bc30d9131005bc7458931006bc71d9130006bd5459221005f97010d10004ff7458b1001cfe7518543007af6488521004ff768c740006ec62d8141036fb4058341014fe7258f4006edc7218d4116eef2158b4115eec42d922106cff75d9332006ee53d89310079c64cc93106edf61cc931004ff75d81310079d4310d20006df63d8141005df7358542006ed65d8931006ed72d92211bebe4058043004fd75d8f1001cfc7559310006dc74d8d21006dd624c43115ebc42d9221006df5218d4100cff760c710006bf50d9121004fd76d0f10006df5118d41006ed65d894100dfa70d0510034fe74d8d21004ff74583310e6f71058730006be72d9130006df5318d410e6df3058f10004fe768c520014fd70d8520006bc52191310367f4059441055ec7250530006de7618d21234ff764871006eef3258b3104d7e7599120016ef61885210067c21d9510006ef624c931014ff768c621006ed53d89310eeee71d8931006fb50185200efcc21cc93123e7
  | 32 => 0x3005802c4ee231001800000001b01281140180021e9800001201d017800800203f0780000000009023001400000c002803000013d008801c00202d005847c042002013801c01002c00201580b62d002180000fa00800701083dc0060138f940000000a80000000003007002847001300480284a205c000000400c018010000400601f00b01480362a803c8008028002001986c00600600102000020000000068000003009801816600000480140b0004000017c4dc00b36b01080e61a400a0090134005040800002200102b0af400a06d005065001607a001000803003e01b83f800001e03080042223d86d180080000c906f00510500020088b100cc00409d012001200100402cc448001011801c00400000a835800000100100040020070db800002600036f000c00e00000b01e404002d000102c00000500780f00360080018000018009002800805201b16b83400240000000000004058051801000e00600f021005803d000001000ade7000000c0006d802a804c000023001800003000000080ec04400b000001408808107c82d0008088017001000e02a0458000012002021000c00c09f000801c0b2009006006000003f00780841ac07250e9e7000c00f00080104b00b000080401160070000000a269080000010034014002800000408103a000000000400a0000054000004008400400c000800000400400100141ee0056df84341ba00000200000040c6001804400004f122006800804500380380da00900582f808c00000680601e000f00e0001f3c12000a00002f4031000814807693e000000004000200088700000710010000000009016800800000f002000000e05b001800001600101c006001002e000031026e13b07080980da000004802012e00e004801426c03800000240002fa01501000720000068010048000000000815c007002000800001810380143c80010320000002001000025407e000000004c008182000828400e02f047009c0220081d7001800c00a00387c40660150028001542015001802802201403782a418e00000080a405c017030012c030002002802c1fe06900303b400a07200004ac000005061006063a0020a7803c07c0cc09785d00ea07200080b51ee000014000804e0160058044008001002803c1340080010b2c00800100c000000000000a00600160030078014016000007802c01a003000000001000000301e0004000028001000201b000003c00000d05100580ac00000680000960310002dac00600102b000c00000b000000c008004000001800202c00a038000200001c80140000361858ae800008d000935801a00c0000014000000001806002a0b500301703584f400a838000201e03a001813e00100100000180170ef80000ac3e9007006400a03b000805c0000030060008bd601f005800
  | 33 => 0x4042014800001800d116801c10804e00780383660cb02200f400205500c052000001d01f80182a4014004801400e147004005400e00000980ccd320030f2841000400f00000b456607e13f00d40322d9008800403a00000a029c03400107101f803c00301600742a000e031001813a000006001001c001060803406e00500080a80ba01b0470ef400a00a0000120000000001000800400d09480000340020018000000148000800803e007016005824613401e0000016013001800000032c008000000200100d000008a02801c8000002071006806c19c021003007000602200996fc002000001802050c0000178000000003001b3ac0001fa0d1800004e16c00001005fa04400200500980ba00180080186120008064002007001000003e00708f802810e07c02c810408e00400380040aa02700f83e000201b009000402c001008803c00a0000838018002017003014c0600020030010014004001001120400005e03cc0142652be00c000600f099800003e02513185fc0100000312d2c02404301f80080000a0014005c0020be00304280060cc00c803c00600d00981e013809c0048090020017031803000003d00180000180a10a3802803200000204900008970cc001400602e008812400400300080481480460b68a4c00c00100a817c09e004003800800600100a800000844e028000802605e01880180080030190001c42000006802403a005001800000a008000017403a005030002c000001000000400005901500000860020000000fce01100000282c803c007007403802b032802001200301500283d600400080dc048001033800000e001017800800803902b013049c00002181bc0641cd01095c400008c002881409800201f005804c10e0080080000000003800c00206000605805ae00e000800001a0080710014252006025800003800600080f007404506a8074000055034001c41000900503785c8001001000000001c006001001a00f120805810e00100002f808c006010801800a026004000800e0010058020006006000001c00600000003a40000d4002000c00001400080fc010034012001801a000000093c4c400000c002400a000146000809e052016801816800100000e400000002001f401454907900183ba00d001000021c01b006000000000e00101b805e0e500006d009c00a00b000002e004058001106802b0158008520028053006c02621b00b80204e4007169010000000a004008412a00701480ac00802b00181c405200c0060048002016001800006e09e00b00c85e2037005801c01e00700c80c808200300000280020010020038012105038143c23a00617a804805c00400581e016e01a0c8005401800502c80f000008900283dc02000000d007437000c0000a8402a0280070014000008011886400600
  | 34 => 0x18c00207e001001400000f017001421602904480000020100dd809401e0042c3813c02c03e009807800600000182a0010016000000400801e06b8004020000009000000800100500200e20090370000076048005000c0000170030004074002000000c006043002256800608e0cb01e40c400505300105ea008007800013c02701880a40100a40a007c002200000e12e000e0b0002000c26a00000980000020070a9802c064156a4080480780080c0000405c005002001c15c1b3002800800800a1251a5c00406a00fa7f800000100280080000050038128000208000801400011503200740040040a8941825e00102981b8002004004003802a06d051009c0040b2000000426a005000004800e00600300403de007000000004800b0200010516000002002c0002ba002007c024004006037c01c008000800000e1650ba000400002600083b4002005002804007c005012000800600000c08f0000020002000803c00b000000001403e02cbbfc00601e000004401003800e80040020480a0000c0fe003000000018600001a800400002a00583e03020000078e3000c00700305900009680000024008c04000809034814900401f000a00000f8984002270009000000c00200002e180000900d8008000a6700100002dc000028800400800114700b000200000080205880080030000bf407e004860c00e00200b805000000c00800080080037d186b800001201d800001a10f32900000040030000eac02800b00300e801206200380
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa9e8650c438840d47d09b92cba0003631cf42506210345f438423226000aeb80597624c40117b093b262900028f61271d953000636390cab22200087f855c3625040193aebbb2862196237a1e6350e410063c3aee0b222000c3d749d461508018b8ea39ac4880030fdd774591300062fb2ee6a0a200387c855db414c0010fd0e32ac4980023be097558d100064e3a0c698a4200d94211c54310c01878cbba26298062b3a0b5118d210345f43ea63224200a9d83d44644c0010ff0ab86c498803a3188644c9313e656392a8b222000a3c845cb654c00d878c8ba88290802b3e096518d4100656392c8a0e6200c9f64dcd41484018d8cbb92c888083719ce71cca2112656390c898a42008df835d563484070f90ab86c89080317dce73594410043f438cab1a2000c3d75192614c0031d90cb968690002a72117018d210045ec38a3b2260018f8805d56190c018dccbb9263a0003279d36398d210064eba8c720a8200c7875dc162440051d904bb08688002aee0151d913000556c16e3b226200c9c64dcd214c0031f50038ac421976a7a1075d8d410070f41c84b288206cb4649c7434c4f995ce4aa6c9988021fe1576d05300074bc0ac821a640dc5f759d463484015ad02286c69081b0f1d1654c84100673b90e2b226400cb7741c5644c80195ec9b92629800a2fa1271d89400043f438cab122000a9f865c94310c311bf0eb16621881b2719173d09300053cc0042b2882008f980dd562d04051dd0fb92c6880030f1947458d100061fbaec8b02420d8f980dd7614c0015750010ec8988023be097118d4000667b9ee4b226200e8d5418c62504b1938c839a8288036a720d545933201c3f43eeab22608ce9721190634840d1bd0fb1a8690803331cb635814100575c02a3b1282068bc845c0634840d179083b262a000327d90735053006c6f438a031a4200ccc621cd624400d53d09194c7a0802b620165d8d2101557436c4a128200a9e83084644c00153d09196c6880023e600715884300c5e432e818a8006c9c645cf414c4018f0cab86628826f8e1415458341006673b0c63128206c3e645d441c4001938e831ac0908023ee0175984430043fc3eca20a6000a9d83d44644c4011df04bb28398003331cf725912100667b1ee4b028200aad84980624c40193eea31a84a08030f595740c74000573408a1b126200a6c855c3625040171f04b20869900335947764c43100673b90e2b1a402b8bc87d9131484a5cb6c7b2e6098003179d7631052100656316e8b126200c77751c5634800d17908b98c290002a76126518d21006363aec4b026206a3e8290965104abd1886a1ec4a0802a76105018d410061eba8ebb226200e8c43589420c401c3aa9280c6a0803271d1624c43106c6e41aeab244200ab980948644c041998c538e6498802a72056410f32
  | 1 => 0xd083aec4a0a6bb1104631894101c3e42ae030a6458a9e84c846350401958e9b1242880031799473487400043f43843b2a2006c9c649cf414c40117d0e10ec8980022fe1d65191210061ebace9b1e203ecba76d93304c0014bd0b906c6a0803275d463d094100556c10a03224202acc8258d32c4001878ebba2c488002ab61353d89413046f43864b1e8200a9e8314064484010fd0fb2ac488002b5a0450d8d410070eaa2a231a82008f980dd76150c31998c439a42880023ee017558d210054ec26e1b1a429de38505516010c0117d0c3a242980038dd4651d91210054f40ca831a825d8df865c4430c401998c7b9282908031bdd7625814101c3f42eec9922060b8f8258c435080d17908baac0218030f5d7649853006e4f31ae99948200c5c75d8d60484b1a3886ba88218802e321163cca212c54e41ac9a106258b9681d8c439040d87cc8ba8c918802ab60a10191210056c402ca31a425da9e841cb635041b9a8c73888690802b3a1863189412c6ca20ae2218620dcd8635c0314800199ec7b92829080f0f1d554582431245f436e898a42008dd87990634840193cedb1e84a0803a318f62509410065bbb6e8988620587d8708765440070fd0bb82c421802ab61051d89410c4e743ee4988625db968118c439040d93cc8b988318802a7a0e65191210045ec38a3b226200acd82d44634840193ec9b9a4298002a760e60d91210147743ee4b088600aba80084644c45735904b8887208033554f764c4310062eba8ebb1a8200a9d84d48635040117b0fb20871880317d97735053014476436e4b028224cac621c542504018f2eba86c0a180a2fa1f645093101c3e42ae1b226207978855c221c400d878c8ba88398802a52056410d324d763a08c63128206c3e645d4410c401b288638a841880395d4651d8d410047bc3ac230a6400e2f54953624c4015b700b28c6a08029761421d8d410061e32ee890a2058a9e8414863504018b8ea31ac0a080327190734853000556c26a5b12620087e871d560cc84935d0fb92822080e1f2157650d100ee663b6c49926200c5e65dcd21d00014bf0ab80c6a0802a760c521913100567410a1b1a8200c6c65dc9614c00117d0e322c090802aba1954189410046f438c698c420387c855db4244001938c738e84a0802ad60450d912100657ba6c4b02620087d87c8165104011bd0fb1ac0908021fe157018d410055cc04a5b22602bcae72d92438840156902b2086990031b189751053101c3f43eeab1a200387e851c56210c0117b09baec78800237e0d75589100045fc22eab226000c5d75d4f635040153b08286c6908032d54776504410054f41843b2260008fb805d5644c81b53f0eb208618802ba20151d89310047b40ceca1c4258e1e54d506350401938c9b9ac09080a2f21176d09302c6cab08e2a188600
  | 2 => 0x274d8d21006c63a66498c4200e2d65dc9411040195eec39282208028f61671d913000566c108031a420387c855d942440015b301290c6a08faaea0021d91300061e32ee898a200093d851c542504011bf0eb28c6a0803a395063189414e55bc22c230a8400c5d75d4f63500018f0edb2a40880032b1d0625813100477c12eab0886008f980dd562cc40153d07216c8880031b1c9654c7400052e42ac631a80028be849db42c405b95eeda1283108021f61471588430045ec38423226200ab581143644c40117f08baac7108023ee017558443146563b6c4a128224cae71192214840199ee7b12c0a080e1fa1f755911000746a1887b126200a6d821c1651040159906b28c4a08022fe1d6410d320056c402a231a4200c3c651d1314c001938c8b9462988023de1d611854203656322e5a0a42028f980dd7614801b938e6b228398802abe0965d91313164fb98c8b0a6000cb7761d1310c40117b0e108c89816237a1f635052106c5e43aa8b266400c7765dc5624c0019c8e430a629800e1f21576cc9400146ec18e2b166080e1c30194644c00117b0f190c89881e5e2157090710004cf40ee4a18860387e87dd563480ff47d0b328c89801b0f1d165487400345e422ed10a6000a3f845cb654c00d17d0938ec4980021f617705884300476c3cca31262008bf845d943440010ff0ab80c6908030f9d464985302ad57420a3b128200a9d849d4635040117d0e28ec89881a8fa1373594410043fc2aed21a4000cd7731c5634800117b093b665880021fa1f65591300062e3a8c6b024200cce76d8b324c4015cf02b18c4a0802b620151d8d210043f43e40b288200ad88054463504018f2e0382ca208030f1d77458d2000566c1cc0312825fd8c435cb434c83159904a88c69080237e0d75592210062e328e6b222000e8c64d8b324c401938e6b12822080e1fa1f75589100043f43ecab1260008ef825d5644840187eea3a2c4880021fe157610d1010667392c598c620387c855d8314801b53f0eb208799002a76132118d410345f424ec21e200387c855db424c0011f700baac6880031bdd462581310062eba8ebb1a4200ccf731c96344001c3ea92a6c690892aba08501912100566c14c031a8200c9f641cd214c0070f90ab86c8990030fd9574985300046f438a1b1a8200aae82997644c50b8bee632ac89801b2e9d864cc1300045ec26ec90a6000a798008565d00311b90cb8e86990032755073591100046fc3ac631a8400a9d83143644852f47f08b92ca20802ad2056490d320064e3a6c698a2000a9d84140634840153b06290c8980028fe1173d95100053cc04e4b2e8037aba80084644c0bf53b0ca188699003a35cf641893100636390cab0a6055aae841436250401878ea3a2c6900022fe1d6419310004cfc3ac821a647dc9c7395164cc8ab55
  | 3 => 0xbb22425dc9c439db428c40d17d0e280c89880a3720d76cc94000557414c1b22622b9af8759342884011bf06ba6c488002a76105118d4100476c3cc631282068be84dcd62c400155d05300c898802b6e0151d8d2100c76432e418a400387c855d93244001d18c631482a0802a72116318d210062e3aee6b222000c3c659d2614c0018eeca38ac4980022fe1d65191300061fb28e890a600087e871d5609040153b06286c898802b52056318d2000c7d406ebb24620087d859db32c400555904b2285880063ba1b725052006c6e41aeab2240068be84dd9214c0411b90fb1a8290802ae61350d81410043fc2ae030a8660c9f72191324c40187eea3a2c6880022fa1c64589300054f41e423226200aaf82594644c40187c84ba8c2a101b279cd7690f420351e42064b28820d8dc835d5624400193aca39a82208022fa1c64589311046e432e518a6200ccc73dc964884010fb0bb82c5a180a3e60375d8d200064fb26e6b024206c9d83dd94310c0155b05306c898802ab60a65191310064fc3ac821e6400c3e759d363c40070f90ab80c71098237a1c6350d420045fc22e630a405da9e84087635051bd1842326c6908030f5d44318542004cec3ec621c82008bd84dcd62c400187aeab208318802b3a0a65d8d410361f3a2ca18e8000a79801cb654400d878c8ba88290003631cf72504410061fba6eab048600e1c6594c644c0014f30010eca9800aab2096450a310146e41aeab266400ae8805946250401c6ea328ec89880327dd4639054100c7c402ea30a4081c3e76194644c0018d8e5b2a6288002a7a1370d8d214aee3b98e49886206c9e645cf428c40117d0dba242980030f19474589102ee4e326e6a0a6258e1f8555063504ab958e9b92c2218ae6761c43cca410061ebaec820a4200cce72d8e6350401938e9b9ac690803a318b63509410063632ee4b1a20008dd871406350457958e5b22629080a3721d634ca410056741cc1b1282008df8758c63500b1938c839a8310802aba0a65191313e6573b2a9b12820da9c841cd640c401d1aa831ec4a080e1fe1d75d814201477414ec98a80018f8805d561d080187eca3a242880022f61c501912100567414c1b1a8200a9d84d40635040187cebb24c2980023d20575591320054f41cc03224200aeb80547624c4018d8cbb928298002ab61353d893100556c24ca3126200b1f855c14310c01938c838a64989f72b1ca54591100043fc2ae1b128600ccc73d89414c4fb95ce52a6c998802a76135318d4100746b98c8312620da9c83551640c40535904b8886a108273a1f324c6210047dc02eab2220028bd84dd46150919d1842320c690802b320965d8d4100746ba6c63128206c9c649cf424c001c3ea92a0c69080365c847150c430046fc3ac631a8200a5f855c063484015b501296c6a080327dd
  | 4 => 0x150c0187aebb2083988030f5d7641053100572c08a1b1282008bf87590644840153f08b2ec69081a2f2117610d200054ec26a631a4200aae86190624c40117b0fa9ec89800e1fa1776509100056dc02a231a8258a9e84d48635045755d04286c8908032bdd072591310056d4004231a8200aad841d7624c40155d08286c49888237e197110f320070e32ca7b2260029cc825c443cc8bba3886ba8831880327e1d6410c3106c6e41aec21a42028bc8759142c40070fd0b38ec498002a760c50191310053dc02e6b2e80068bc845d5634800d5390ca188698002a760b6410e310046fc1aeca1220068be849d931480051bd0738ec498002a720d65191210ec76c3cc710a42008fb805d5624400147d0a10ec898802e320d64d0a210046ec3cca31a4280e3830194644c00155b09b8ec4988030f5d564106210056dc02a231a4220ace86d8a314c40155d09a96c498802a761353d8d210045f438c8b0a6000c3d75d9264480011bf06bb28690863331c8634c6210045ec3cca322600087e87d95614c01b93886bb686189aa3ba1f62505310043f438cab0a6000ab980087644c46f57100a98c8980023ba1c62581410045f43ec8b0a6000c9e541cd6444001958e9b92c6908023ee0175591210345e422e231a4000cce76d8c62504b153d08280c6a08063e20175984430061e328e898a200087e871d5644c0011bf0eb18c71081a3e60375d854000574402ca312628aec42154463484011f700ba8c2a1837279cd64904310066631ee498a4200cd473dc5624403159d0421ac41880a3b209764c74000557c22e7b128200c3d741d365440011e902baac690002ab60850d912100c7c402eab244200a9e8314364484018d8e5b2a6298002abe0951191210064eb988630a8400a9d8414363504015b700b2ec690802ad60450191311046f43886b146206a3e848c9651041b1b906baac888002ada04501912101476412eca0e6000a9d84d44635040187aea3aec89803637a1f73589100052f41c85b2a2000c3d75d92644c0011bb0e280c69080f0f1d654582430361e322eb3226000a9d83080644c511d8842080c69080e1f2157690d100045fc3ac83226200a3d819096510405998edb9264988022fe1d64192310ee66bb66598c420087f855c3644c83159d04200c6908022fe117558d100364e324e620a600da9e83d91434c0018d8e432ac688002bae0175d89310054ec246431a82028f8865c031480051bd07bacc399002ab61051d893106c6e418eca0a6000c5f65dcd6244001878cbba2c29800363dcc725044100657ba0e4b22200087d85dc16210401878e4b2c862080317dd463581410064ea9eeca18862baae82d9241cc401b48e839262189772719373505300043fc2aed10a600387c855da214c00193ee839ac48801a2f21c64485300054f41cc
  | 5 => 0x2aba1264189310064f3b0879948200adb805976350401d28c9b8a64988023ee0175d891006c6e418ec90a6000a9e8414363484071bf0ea9ec69081a2fa1f531913043e6bb88c6b024255da7425c443884010fb0bbb24298002b360c50d89410063ab28e299082008ef825d843440051bd0fb1a64a080e1fa167690f10007472a0c7b128200a7a809c965104010fb0f3aec7880021f6177058b4100477438a1b1262068be87084644c40195eedb92822080237e0d768854000c6e41aeca0e60008ef87594624c4010fd0fb2ac8880031b197724c5300053c402e6b288200a9e831cb644c40153b09a96c6a0802b620151d8d410064e3a6e6b122000af180087614c00d87cc8ba8c910802b3e0965d8d4148f4610ec831a423ea9d83dc7644c001d2902b208699083339cb63d0e213bf0e32a8621a600387c855da414c00147d0a108c8989778795354d8d410145ec26e6b16800d8de8714063504014bb0bb86c690802a76184350831006c63a6e498862028dc8758d32104018b8ebb1ac0a0802a7a0e60d91210146ec1ee8b1660008fb805d7624c401ccea328ec4a09f6aba1065189410064eba6c731a42008be87d91624c0018b8ca39a82980023be1d64189310045ec3ea63224200acd8399462504010fd0e3aac8880022fe1d64191101bd4e432a63226000aad82980644c40187ce4b2c8620802a7e116518d2101c3f428e2b1686018fa86dc1214400193ee831ac0908022fe1176885300055cc00423226200acd83983625040117b0f196c8980023d205755912000c7c402eab1a4200a5e8390b654c0b153d08288c6a081a2fa1c501912100567c1aca3126200a9f845c0635041b93d0fbb286218028fe1570d91210051ec2460b288224cae7219331484b193886bb6841880327d08735922100636396cab222000a79801cb654c0031f501baac5a08030fd947458d1006e6631ae531a8200aad82997644c4914f50db2a4088003271d863509410056dc02ca31a42008bf845d943480010fb0b3b48788002b3e0d651894100575c02ebb12820387e851d942c400117f08baac89081b8ba0a425944100637b2ee4b222000a3d85087644c4011f700baac3a180327dd0735911000557420a3b126258a9e84d4063504f9958e4aa2c221862b3a0e63885214354fc22c631a80208df835d921cc00d17908b90c2980022fe1176509100065a326e2b126058a9e84d4463504014f3003a6ca980032b1cb64505100054ec20a3b1a4206c9e7358e43d08018d8cbb92828800a2fa1f645093000666390c698a2000aaf84594625040153b07080c89880327dd3635812101e1f3aaa9b028200c9c649c7324c4b153908b1863108021fa1f6558d100ac7d430e29022000c3d65dd121d000187aeab20c98800e1fa167650f100047743ec4b0262008f7875846
  | 6 => 0x1c3fc3aebb1e2000a9e84983634852996ee2322c69080e2fe1d54d93312ae67b14e7322420387e85dc1628c40153908b2ec690892ab20951191212ae56326e4a0a4200a3d85084644c0018beca39ac8880023e60375588430063c328e29022000c7865dcb104400153d08288c69081b2d1927110d210145ec20e2b168000a3d848816510401958e9b92c6880363be197290e21304cfc36e4a1886008df835d9434400159b05306c6a081a2f2117558e210063a3aee2b1a4000c3f75d91624c00156d02286c890802a7a0c52191310351f42464b2e8000c5c65dcd214c0018bee739acba00031b1cb65505100051f42465b2a2000c6c75189604c401958e9b92c48800237a1f63581410043fc2aec18a40008fb805d56310401c9865b2a64980032718c71509410043ec2eec99220008bf845d921cc00117d0fa9ec8908030f19774589300361e322ea20a600087d851c562d0c070f90abb08688003395c8610c5200061eb2ee898e8000cac72191314c0011df04baac8880af2b1cb645062100637baee4b1a20008de87d8d62504b133d0fba262188063ea0271d89303064e21ee4b188200c9f87590434c80153908b18c68800e1f2157690d200046ec3c85b1a82068bc845d563484011ef0eb08c2980022f61f52d91310056ac1843b0a8600ccf73dc96488401878ca3a2c498002ab60b71d913000556c10a1b226200c3f65dd1214c12d47b0938aca208021f6177058a310065a320e2b1260008fb805d564cc81b9b4c6b80638800339ddb724c4310045ec3843b22620087f855c263d08011bb0e286c6a08022f61c51191210051ec2e41b226200ccc731c964440031f100baac8988023ee0175586432c54e41ac82086200a3d85084644c40d938c8b9cc89081aaea1350580430070fa9ca6322420087d859c7644c00187eea322c498002e3e094310e210051f42842322603ea9c8654f644c031d8ce231c42908023ee017558742306c7316e4a188624aae8214c644840187ecbba242880ae2fa18744c5210064fbaeeca188600ccf761c9310c41b938c6ba4c69081a2fa1c51191210061fb28e8b0a6006a3e84085651040187eebb22c098802a7a1051d8d210063ab2ee299082008bd87d48644c4411bd0c39a82908030f1977458d100043fc2aed21a2000c3e75d9041484bfc3886b2a6420802a7e0d65191210066639ee4b222000ab980084644c00517d09bacc3a10030f5957190c410056641acbb1282008de87087635043159d05a1ac4188031e197704c53015d57436c520a82008bf87590644c8019c8e5b0a62980021f617765093000556c16a23224200a9d8414463484015d100b2ec4a0802ab209641913101567436c49926206c3c645d4414c40195ec8b94c898802a7a0c50d913106c5f43ec8a1a4200cb764dc5624c01b1b906bb243a
  | 7 => 0x9f865c14310c010fd0e10acba00023ba1b72505310061fba8c8b0a602099c845cf428c503c3b0632ec89800a3d2197110d210055c402a23224203c7675944614c8070fd0a3b285188028f61421d91300351f42042b2e8000aaf82590644c41b1d90ea92c5218023761e6518d410061fb28e8b12200387e859d932c400153b09a9ec6a08038760e42594410045f43ea5b22620dcd4639c643504015c904b08c29801b0f1d1654c7402ae96212ea3244200a3d84041651040187cebb2082988022f61e65191310063632ee498a2077e1c6550c43440011ef0eb08c2a0003651d3734c4310c4e6412e22186200c3f75dd1624400117f08bb26488227b10861018d210046f438c6b028200c5f75d8d604840155908b2ec49880e1fa17764853006e6631ae598a420d8dc835da43484018b8ca39a82880022fe1d641912000666398c4b028200c7865dc121440015cb02286c4988023ee017558f4200c7c402eab226400c3d75d90414c001958e8392c6880063e20175587322ff4621ac49908200acd83997625040153b08100c6a0802b520d611852016c77c32e3a144200a9d83c84644c4018b8ca39a4298002a76132018d410056cc04a5b1a8200c7865dc1414400153d06290c8980031b5d475d893100c5e422ec90e8000cac72d91314c001878ea322c09080e1f2157098f420047bc3ac230a4000c9d545d8430c40147b0b900c898802b56045018d4100637ba8e4b1a20008df8758c634400155d04280c89881b879cd6590c410070eb28e6a088200ab980087644c00d1790e32262908031b1cb65505300061fb2ee898a2000a1e8390965104011f700baec4a1802a7a105018d210046ec3c8431a8200a3e85087644c0018f0cbb8286980063e2017558f422a53d404e4b2e802b8bf8758b419040117b0f196c898802a720d65d912100557416e3b226000a3e848cb654c0031f100baac8908030fdd464581310361f322ea3262009978855c0314800153b07290c898802a7a0c50191313f57340ee4b16200387c855c362504031f501baac5988028fe1570d91310052f42ee1b1a4200a79809c9651041b93886ba0c71080a3b2097558d1000557416e3b226200ccf73d89414c44955d05a88c89081a2f21175588414070ec18ca3226024aae8290d62104010fb0e10aca2080317dd773591100045f438a1b22420387c855c364cc80153906b20c910802ab608501913101c3f42eeca1a2000acf825c4635040d17d093b2429816327dd463d09410043ec2cec9962024cac621d1214400195ee9b92c7108022f61c50d912100477c12eca1a200387e86dd5614c00117f0eb20c910982a7e096410d320051f41c84b288206cac645ca644c4018beea39ac48800237a1c50d8d210055a40ac83226400ab88059464484014d90ab86c498803a318f62905410
  | 8 => 0xe32ac8980028f61662191300062e32ee690a200387c855c261d0c7d17d0f196c898002ae20165d91210045ec3ec820e62558ef825d8434840153d093a8c690802b3a0e65189410056a40ac631a840087d859c7624c01b9aca7bb262188032bdd37258d210056dc02a3b1a8200aae869506250401878ea3a2c688002b520d61185420045f43ec898a4200a3e85c83644c401878cbba2c488002a7e0d65d91210045fc22e7b122000c3d755d363c400187eebb22c29800a3ba0a765053015e56314e3a128200acd83143624c4015ab02286c69080e1f21576105300053cc06e3b2a6000c78655c3414400153b0828ec6a094a9ea0072d95300047dc02eab0e645d8df835d941cc0070f90abb686880022f61f52d91300146e41aed9928200e8f7418f625040117f08baac898802a720d511913100c6f436e690a6000a3e8408765440070fd0bbb282980038e19464cc1300054fc22e031a4200c5f75d8d60504051f10cb8482900922f2197190d420061ebaea9b224200ce4621c56250c018d8e5b2ac688002ab60830191210052ec1842b288206c3e645d4418c4031f100baac99917ee360a6310d420056c402ca31a82008bf845d943884011f301baec29900335d8c7150d410061eba2ea30a8400c5f7518d6048401d18c9b14629880327dd8735044101e1e3aca8b222000cac72d91414c4015d100baec498803a318b64cc93115e56312e520a8200c3f651d131440010ff0abb2848800e1fa1770593310043fc2aed992800087f87d9441440010fb0a38ac5a00968f61372594410066a31ee2a128206a9c8650c434c40156d02286c8988021fe1570d903100637b2ee4b0a6000e6751947624c4051790eb228518802a7a0c72d913001c3e42ae1b20620d8dc835d843884018e8ea38ac6900022fe117018d210043ec3843b2a60038bc87551644400153d09190c688002a7e095418d4100c7c402eab1c4200c6d75d4b625040d17908bb0869080335547764c4310062e328e6b1220008ed829d9315000187aeb218c2a1002a7a126018d2100557424c1b1262008bd8714764484031b90cb988298037271d17418d210045fc3ac820c4200a9e831d7644c0015390ca1886880032bdd0625813100556c24c0312825da9c8458e318840159d06286c4a080327d9173991214aee2190e2994620d8de83dd764c40010fd0e3aac12180237e1d6318e410045fc3aca3226258a9e84c80635040187ecbba262980021fa1c75589100066a39ee2b224200a9c8458c638840155b083aec4a0863339c863d05210043fc2aec18a800387c855d9434800117b0e280c898802bae01651893123d3d400e5b2a2000c6f65dc963440019ae8638ac899003a395363189410062e3aee6b122000c7865dc1314400196ec838ac498002a76135318d4001c3e42aed10a8000a
  | 9 => 0x7650d210045f43ea7b226200c6c75dc964440070f90abb062a0003271db635094106c7c43aa0b0062028dc835db32d040199ec6b94c6a0802aba1075d893100746326c710a4200a9c845946348457958e5b2282909dba31894310d310364e3a2c69908206a3e841c565d000193ceca18869080317194734851000c7d406eab1086018ee86dc931480010ff0ab80c710976a7a1051d8d412c46fc32e3a1c620587d87d94414401b938c6ba664a001a8fa13725944101557414c6a16820dc5f759d4635040193eedba26218802aee0151191212a53c402e2b2e8000a9e8650c4344001938c839ac09081a8fa12205944100c7d406ebb0a64008bd878c8644c00147d0b38ec8980028f21173d95104151f430ca3226020ccc629db324c4451df0cb8e65108032b193724c5210043fc2ae1b266400ab681140644c41b53d07b228690a0ea7e0d65191300064fba6e6b1a4200ccc621cd414c401c5ecaaa0c4a08030f99774487402c6cb308e2a188600e8c64d89324c4011ef02bb26488002b6a0021d8d410046fc1aeab226000c6f65dc9414400147d09316ca98002aea0252d913100c5e422ec98e8000a9d841cb63504b193eca39a82208021f61e75d81420055c402ca3226200e8c62193324c4014bd0a108c6a0802a7a0f51191310064e3a0c698c42008bd87d48644c0071df0ea96c49880e1f21570d89310045f438a3b226000c3f75dd163440015ab02280c69081a2f21c644c5300046ec1cec90a8000cb651dd941104018f0cab808688002b32096318d410056741ccbb128258c9c641cd41484010fd0e3aac11080637a1b735053000556412c83222000cd7731c5644c80193a8439ac91080a37a0e76cca4101c3f43eeab066400a9c83590644840195ec9b92c098956aba1353d89410065a3a6e2b1a4000a3e84087654c00117b093b265880022f61f531913000746108c7a128200ae8805d7625040196ee9b8ac690002a72055418d410046ec3843b1a8200e575194763484011df04baac690976a7a1352d8d4100c7d406ebb0a8400aae821d7644c001958c43a2c498883331cb634c6210061ebaea9b226000a3d8598b644c0018d8e5b2ac298002b3e0d74d89310052f418e0b288258a9c84544635041b1bd073b242a00021f6167650f100049ec28e2a168200e1f5394f644840117b0fa9ec89080e1fa1b75589100c5674168630a64008bd849d943c40bb53d08286c6a080e1fa1770592310345f426ebb1e20068bc845d5631041b998c6b9086908032761f6410e310351f420e0b2882008f7815d5644c80187eca3a262980023ee0175d894100746aa6c63128200a9f8359064484031f100baac3a1802ab61260d89310043f438eab0062008de8718d62504011ef02baac8900af2b18a76d094100477438a1b1282008df8759063484010fd
  | 10 => 0x9962000c5d75d8c414840517d0fb228598802b9209611854301c5fc3aa9b226400aae82143644c4bf93886bb264208028f215641913000657ba6e4b226200c6d75d4b624c40159b07328c498863331c9624c4310065a320e2992620099d87d90438c401d28c638a84a0802b3a0c50d89310054e41ac832220209cc825c4438c401878caba4c29800297a0c215944106c6e41aed10a8000cac72d91414c00193eec3a26218802a761843904310045ec3ea63226220ccc72d8d3148401878ebb22c0988022fa1c50d91310052f42ee1b1a8284c3e76d94644c0053c904b8887108022fe1172185300052ec1843b2a20008ef825d931d00011bf0eb18c78800a3e60375d91200043f438cab22200da9e8390964cc40187aeab20c918802b36085018d410046fc1aec90e800387e851c562d000156b0810ec2a1802aba1265d89310061fb2ee8b1a20018f8805d56110c7939b0fa1e649900a3b2097650d100ed6641ae9b126200a9c81590434c85155908b9ec4a08030f9d574d8f100051e42ae1b2242038ef8754b625051b93cec320c690802abe1165d89310047dc02eab206200ae681143625040117d0fb22c498803a319063885210046fc1aeca1c4200cb4741c5634800187eea3a2c6900031719773591100062e3aee6b226000abb8054c644c00559d05b1a64a0062b3a0a1018d210064fba086b146200e1f5394f644c44b47b09b9aca208029ee0171597400064fb20e6a0a2000c3e75d90414c00117d0e28ec89080e2fe1d54d91300043f438eab1a4000ab88054764484031f100ba8c2a1802a7e116318d2100656326e4b026200b97815c94310c01998c4b9e82988021fe1570987433064e21aed990820d8dc835d463500bb93cc23a262188032b9db62d09411bc5f436e898a6000c6d75d88414c44955d0db2442908023b61c50d893147d6bc0ac831a4200a9f83544644c40147d0b900c898803a5190714c9310054f4328621a42008ed829d9414c001d48c831662988063e20175d89313b5c6412e2a18860d8dc835d5640c43133908b9e841880a6be1d7290d4200746196c89926000acc8258c63440b153d08100c6a0802aee01651912100c5f436e898a8000c3c75d9160484071790eaa2c9188031bd977250530306c6b16e4a188600c9c7418d314407d17d0c3a26298002a7a0f511913000747c12c821a64008be87d91214c0018b8cbb9a8298003a518f71509410345f43ea63226200cac72d91604c40187eebba2c690002b360a6518d41006363a8e4b222000a9e83c80644c4918f0e032ec4880029760c70594410043fc2aed20a4000a9c8359041884015b300108c6a0892aba0830191212c64f2a2ec2186212a3d84dc965d0001858e4b2a822080371dc8714c9310046fc3aca31a4200a5d8308565d00011bb073b282900022fe11
  | 11 => 0x884bb1bf0eb1c87208031b1d47258d100070eaa6a231a82028bc845db42cc4018daea3aec4a08022f61c511913100673b10e2a128200abb80597644c4071bf0ea9ec6a080a2f2117558f420951ec26e6b2e8000e8f6318a415040172902b20869901a8f21321594410043fc2aeca1a4000c6c75189605040159b04286c6908030f597744c84100656390c8b0a6000c3c75dd1644c0ff53d0d298c8980021f6177058b310045f438c8b0262028dd83dd932d0401878ea322c0988023de057650d210046fc1aeab226200a78855c362c400159f06b2ec4a0802a76127518d210066a218e2b22640087f855d8414c00517b09baec6a10029da04705944100567410a031a825f8dd878ca63d04019a8c638a84a081a2fa12764cb100064fba6e6b224200e1f5394c644c44599eed992631080327dd073591210061fba0eab048600cac621d162440011df0eb18c4a08039a197624811006e4e31ae818a8000b8f825c54310c0153b07328c8908031b597724c7401046fc3ac598c62008be87d4b644c0018b8ea39ac88800a2f21d64508310061eb2ae999082028f8865c231480d5c588410aca2080363dd0724c43101c3f43eeab00620387c855c06150c4955d05218c2a1002ae20165d91310061e212ea30a8400acf8258c63504018baea3188290803331c863581410361e322eb3224090a9e84990634840193aea31a84a08023760f75d93100345e420ec90a80028fa86dcb10440010ff0abb48298002a76125218d4101476410ec98a4037aba80948644c049d4ce23244290962a7a121018d410051ec2464b2882008df835d9324401b93ca7bb2862180237e1d630c6210061f3aec93226000ccc63dc96050401878e4b2a822081a2f2117558d1001557416c9a166200a5d83087654c0010ff0abb442a00030f997744c74000746108c99926206c3e73596431040193ee621ac5208032b1d362581310c46f43e86b106200c3f65dd1614c0070f90ab86c4a18022f61c51191300147cc06ea30a4000ce472dc5634400155b04298c8908030f5d475d912101c5e43aa8b2620008f7815d9434800d17d0f190c898003391887150d31005e2c0887994420387c855c263d0401c3ecaaa0c6a08031d19771589300351f42020b288200caf64dc9414c401958e4322c0988032d193714c9312953d406e3b2a60248be8790d62104018d8ebb92c6880031e19572c41100064fba6e6b1220008be87d91604c401998e7b92c4880022fa1c644c5210146ec1eebb226409978855c2414800193aa839ac9108031bdd7625813100556412cbb226200a3c855c3644c40187ae83a6ca980023b61e64189310043fc2aeda126025a3d841c1651040153f08a88c6a08030fd9674985300065bba0e2b1a4052a7a801d3654c001958c9b92c29800a3b20976505310047b40cec
  | 12 => 0x80387d954310d300062ebaea7b1a42008ef825d94244001998e5b1a6288062b3a085018d212c4cfc30e2a18860387c855c263104018beca39a829801a8f21172594412c54f424e431a8200c9f76dcd411041b1d90ea92c41880a3b209755844300637b2ee498a6000a6f855c362504014dd04382ca208063b21972105200951ec20e2b2e8000ccc629cf414c4014bd0610eca8801b8ddc565504412fd4fc3ac821a6400c9e7618f42504015e100a88c2990038759773504410043fc2aeca1a200087f855db43440ab958c9b928298162a7a125218d414674a108c831a4200c9c74dcd63884bf1bb0fb1c86a1002aee0165d91210045ec3843b2260018ec865ca43480014b90ab80c690802b560450d8d4100727a9ca7b128206c3e645d44188401878ca3a2429803637a1c2118d410043fc2aec9922058a9e849d46350449958e4b128220882b3a1b724c9310066639ec4b028200e8c64dc9324c40155d09328c49880e1fa1776509302c68eb28e6a088200a3d84085651040117b0f328c8908021f219751053000657ba6e4b1a2000c74651c5624c00117f08b88c690002a76126018d210351f42460b288200acd821406348401c3ea7298c8980033318b73589410066639ec490a2000a7b805cd65104311b90eb1262188021fe1570d91210062eb2ee690e80008fb805d563884011bf06baac8880021fa1c7558d1000c5f436e890a805da9d87d90438c401878ea322c29800a3721d634cb100062fb28e6a0a2000c5f651cd624400153b052a0c6a08031719773505104c51fc22e6b288200a3c845cb654400153f0cb8a8621802b360a1018d210052ec2e4031a8248a7a86d97104400153b09306c690803271db644c9311f65c386c8a1a60068be849db32c40c133b0db928621a4eb56066518d2100477c12eab226200c9f641cd60484010fb0a3b28518802a761370d8d410061ebaec820a4000e1f6550c434404159d04286c6908031bd97724c5102ee8e21aea324620d8fa87d416010c011ef02baac690002ab60875d913001c3e42ae031a4200c9f641cd414840153d07290c898803631d0724c4310045fc22ec18a4002aae86d8b425040555d05b2284980faaea0252d91300064ebb086a1062068ef865cb438840117d0e32262980030f1d474589100055c402a3b226200caf64dc9314840153b09390c6a080a3d61a7110e210053d40042b28823e8bc87d91314c04b0f90cba882880373618d700c54000746310c7a128200a5e8308565d00010fb0fb288298002aba1353d89311f45f43ea7b2260028be849db428c40539904b88869901a2fa1c511913000657b26e4b0a6000e1c6554c644c0051f10cb8082900021f61776505300146e41ae9b126018ccc7218d31484010ff0abb68488002a7e096410c3115c5f43886b148200c9f641cd41
  | 13 => 0x45f438c8b1a4200c9d7410c614c80d87ce8b2e642080317d9473485100345e422eab122000abb80547644c4311bd0db9a82908deae20151191300052f42843b1a820387c855c3648845795ce4b16832081a2f21173d89100062fb2ee690a6018ccc621c5324c4bf53d0db22649880a6761e6310d420354f42464b1e823e8be879516090c0187ecbba2c4980022fe117558d200051ec2465b2a20018bc865d332500a94f50010acba00063e2017558c412c64e21aec20862008df8758c634800195ec9b9282980030f9c96550441006573b6c831262008ee87189604c45735d0fa128310802a760e65d91210064e31ae520a8200c3d75d53644c40153d09a98c6908023ee01755922100574402cbb126220ccc625ca314c40159b0532ec6a080a3760f75185320061fb28e8b1260008be87d91634840117d0fb2262980030fdd4645812100637ba8e4b222000c9c76191324c48f8f4edb2e20880028f61262d95300045ec3ec9a166200ad583087614c00187aeab20c9108022fe1175589100054e4328621a4200c9f641cd414c40117b0938ec4980030f1d764585300055dc02ca322620387e859c7644c00153b09080c6a080ab3209634ca410052f41843b2a60038f587944614c85717f08bb243a00033318d72d052101c5fc3aa9b224000e8c63d8b4250407878eb2a6c89800e1fa177058b4100672310e2b126000c9e541cd64884011bd0e31ac0908021fe1570d913100673bb0e49886200ad88059763504010fd0e10eca98063339c463885210043fc2aed9922000a3f845cb654400153d0932ec6908032bdd07258d10006563a6e4b1c4200cac72d91614c0018dcebb10829880e1fa177058b310056741cc63128200a9d83d53644c0b133b0c38a8621802a761075d8d410364e324e7322426ada7721c542504011df04bb286908063e20175d89410351f426e6b2e8000c3f65dd162440018becbb9a428824b279db6418d2100666310e6b128200a5d850846350517d8843288c690802a760c72d913100575c02ca3128258e8f7218d42504015e100a8ec29901a2f21176487300047cc06ebb246206a9e84d8d43484071790eaa2c91081a2f2117610d1006e4e21ae831a4200c5d651cd21d000155904b28c89880a3b20975591310051f424e3b2a6000e8f6418e214840117b0fa9ec89897727dd8439043100c6e41aec90e60008ee87d896050401d2d03b208718803a319373d89310047dc02eab226000a5e85c80635040157100a88c898837271cd64508310056b408a031a8200a9e84d4f634840d87ee2b2a822080a3ba1f725911006c76432e421a4200aad84143625040147b09192cba00922f21d62504411f54ec18ebb226055cac64dc9414c4018deebb92c88800237e0d755912100656322e598a4200c3d655d332d00070f90ab84c221
  | 14 => 0xf74d8d314847d53b06396c8980032b9d864189310055dc02a23226255d2c425d441884d5b488438a85208030f1d764589300054ec24cbb1a420099d821c54310c010ff0ab84c3a1002ab612651894101c3f42ee0b1082378bc875516010c1b1bd073b28290063331c8635052100556422ca3126200c3d651cd411041b1b90e31a8290962a7a102118d4106e4e21ae831a2000ace83980625040d17d0fa90c89880f0f9d554587400055dc02a3b224200c3d7559041c400147d0b310c89801a8f21173594412ad57424c710a4200a9d8398064484015590caa0c4a08028f61232d953001557416c8a166276d8c21dc94310c0199ee6392c8880969d60470594410064e3a0e6b122000c5f651cd214c00117b0e286c898802bae0165d894100667bb6e49886260e1c43597321040d17908bb087108023b61c50d89410345f438a23226207978855c031c4001d18c431a84a0a678e14154d81410070eaa0a031a8252c7a76d97304c0018eeebb8ac69000317dd473591100061e328e890a2002ace86d8b324c4010fb0e10acba0002ad604501912123d3d40043b2a200d8dc835d843440010fb0a3b285880031bdd4625814101476410eca0a4000c9c74dcd63440019cec438a64988823be1d63cca210054f41843b2262008f980dd7615080159f04a88c690802a7a0e10191310345e432e520a820d8dc835d3624400153906b248310802ab61352d894100672310e2a1a8200ada80948635040133f0eb1886a100a2f21173d8940124ce41ae999082028f8865c0434800159d05300c6a08063ea0375d85430065a3a6e2b1a4200d94431c5321040517908bb684989578b95354d894101476412eab222000c3c651d1614c00155f08b28c4988021fe157018532006363aec4b0282008ef87594625040117d0e3224298003a3d90628c5310062f3a8c620a4200a3d8408565d001b1790eaa2c818803a35d063189410064e3a6c698c4206c9e735da431040193cec326649880333dcf72591104070f180ca3226000b948158c43508010ff0ab86c910802ad211611853200567414ca31a8200e1f5394f644c001998c5b9a8298802ba20151d89410045f43ec8b024200a5d8390b654c0014b90ab80c6a0802b32096518d4101c3f43eeab044200c3c75191624c0070fd0b3b665880021f6177650d100054f434a831a8200ab98094b644c40d958c8b90869080e1fa1f755824300557426e3b126277b1c855c14310c010ff0ab84c620802ab61265d893110666396c6a0a4200aba80948644c4010ff0ab84c221a3aa7a186418d210054f424ca31a4200caf729cb644c0014bb07216ca8800a3b2097118d4000667b98e4b226200c5f75dcd624400153b08290c6a097727193735052101c3e42cec20a6000a9d83084644c001878ebba2c68801b2e1917010d2000
  | 15 => 0x211a01e10a0000880000120440000120000020040123880000160000040660020160029440be02600201e00002000201800a00802200003800418a00039400201409804c00204a00a05a0060800c40c20d003e0003904ee03000008603c06206400000204000c03400001200c9c74d8d314840147f0ab20c8980063e20175d894306c7c432e021a2000ccf7318960504015cb03328c4988063e20175d89100045fc3ac83226000acd83980624c41b938c73a4c6908031e1d77058d1000716b28e4a088295ad783584614c8dd53b07310c89816365984735044100566412e231a8200aad84143624c4011bb0e108c6a081a2fa1f74589100062eb98e7b2a2000c3c65dd1214c0051bd073b66588003a318b644c9310052ec2e41b1a8200c9f649ce64484014bb0bb86c6a0802a7a1075d8d21104e7c3ac799442008ed87994625040193ee839ac910892aba0a10191210054ec34e2a188600c9f739cf644843199ce4b16621881a2f211760c52012557416c820e62028de87d8d325000157700a88c8980063721973d0930006c6398e4a088200a3d84087654c0010fb0bbb28488002a7a0c211913100667b9ee4b224200a3e8598b644c0071ef0ea8ec2990362f21176d0d2100477c12ec992200087e8708565104010fb0bb82c9188063e20175590310054ec26a7b1a8000cac64dc9314c00d938c8b98829801b0f9d165ccb402ec6f438c6a0a420387c855c0635040193ee831a6290802e52057250c430045ec24ec90a60008dd87143634840153d06100c89880e2fe1d54d913101c5fc3aa9b224200c1d651cd411040153b06280c890802b360850d8d410345f43ea432260008df835d56448001d18c831462989f3271cd54593322a53c402e6b2e806acac741c96110c01d18c5b1e84a08023ee01755913101c3f42ee0b168600e4f5394f624c40187aeab2082188021fe157098f4106c6e41aeab224258c9c641cd414c0070fd0fbaac1208faae20151d913001c3e42ae130e84008df8758c63484015b30010ec6a08031e1d770591300064e3a6c6b024200aae84980624c4011790fb224298037271d94310d2101c3e42aed20a400387f875d4615080157301290c8988023d2057650d200054ec20ebb1a4200ae781590624c4a54f50010eca980032b9cb649913106c6e41aeca1220008bf845d931d000717f0eaa6c9980032dd907150d310054ec1e40322620387c855db32440014df0ab86c4988022fe117558d2106c6e41aea31a4200a9c8650c438840117d0e10ec8988031719773589100051ec2043b2a2058d1e651cd41104010fb0bb82c9989776510e71d0e312c64e218e2b1e8400ad681140634840153b0610ec898003391cb71591310064f3b6c99926258c9c641cd414c40172d03b20871880317d9773591100345e422ec9922000c9
  | 16 => 0x20160000043a24b80520002c200007a09c0363b046607608c35c04200000600a00000204600005000418600200000200612a02600400003e0e406402400008009c052020fc000401600800000400014e19c0000240240160060380000040540240b403e06400003206c00219615200000802001c05c01601e02e00c0000340380c400200000201000800400400000207600000e02600200c00220205c00e09400000403e11c0000204ee00801600e00200001a01200a00000015a01404800000000004600801000a04207a85400c01803a01400600400c00001005c00200000a00601a02a02e0a802c00600000c1a60005e800003000200200600a00200220602433e00005a0100ac00c0020ac00001400000002c02201006203401203c0200080721b401200200005c0180e606a05e01809e0300020e204600000600001a28c00001c00800000e1142ec01204e0340000d00120920b804e0ee04801800403202e0000e40000121b001c02e04213e48c01c0306e800200400002a02601603001a0160aa5241c401a00009833628e00c3ec00c00208600a07c02e16400000402a05604e0460e80b20061500c403a02800a00000003000000800010800c00c00600204e00200403402e0720020240000f000400018802e00200a00402601000401c07808003800001814a01ad9803200000400038813c00400215e06005000000201e2701e002253410c00402c01425401e0280cc00000200000c00800003401807c00000003603a03c02a06a04a00a002000004096002d145500280020003240340bc00c0023c800026600a03200200401e00006401600600201a00000004600047e03c00c00000600000002004a1563ac00200203400001600800800600003201609600a03800408200400c0245c00003260740ea00201800c06401600803001403cb8403c05600006e000000000006000020b2a00601e06c1b806209200406804406a20c01400400400001a02600a0000aa0e200804001c00000000c01208e14a16600e07a01601001417e00e04400201e06c02629ad3005a0b40060320420000020000ca00000003000003c05201a02603202e5b435e04001000409601e00000e02202e00e008ba001c04c00e0680000162560020460580000322f801204408800059430200003e06200a01604200600800008403600205601c0720060ae0580400000102e027000006000200000e00000004200203c01c0040440289e007606e0b617200203447603416a14c0ba00602a00a0d600e02400400000c00801603000c0001280000680100020020000261240b401806e00600e0000000f40020000000400b006a7fc02e00400000e00000004c03808023400002059c00c00011201400801a00a02002612c2be0
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x88025b40300063dba004d721dc8631c54250401a15546045018d4100607614631c5425040141e939097518542004a5a468650c43884d582e87597725044100507a4e725954110401a19542015118d4100703594731c9411040182e825d643185420060b189851c5425040181d7520d641062100625e1c81590434c8c181c8359574cc84100525658211c54310c0188f87e096410d324ad31a5b721c5324c401c0d651cf7250441006b0084805446348401c0d65dcc72504412c60720d75590410c40181d7520d641922100705594431c53210401c8464dc8714c9310060ba0975d9041cc4411c79760443cca21006a1e0881590434c80189587a076410e31
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x6
  | 4 => 0x94b
  | 5 => 0x94e
  | 6 => 0x5
  | 7 => 0x138e
  | 8 => 0x138b
  | 9 => 0x98e
  | 10 => 0x9cb
  | 11 => 0x9ce
  | 12 => 0x168b
  | 13 => 0x4
  | 14 => 0x168e
  | 15 => 0xa0b
  | 16 => 0xa0e
  | 17 => 0x180b
  | 18 => 0x180e
  | 19 => 0xb09
  | 20 => 0xb0e
  | 21 => 0x1409
  | 22 => 0x140e
  | 23 => 0x249
  | 24 => 0x24b
  | 25 => 0x24e
  | 26 => 0x144e
  | 27 => 0x16ce
  | 28 => 0xb49
  | 29 => 0xb4b
  | 30 => 0xb4e
  | 31 => 0x1449
  | 32 => 0x144b
  | 33 => 0x16c9
  | 34 => 0x16cb
  | 35 => 0x289
  | 36 => 0x28b
  | 37 => 0x28e
  | 38 => 0x148e
  | 39 => 0xb89
  | 40 => 0xb8b
  | 41 => 0xb8e
  | 42 => 0x1489
  | 43 => 0x148b
  | 44 => 0x1849
  | 45 => 0x184b
  | 46 => 0x184e
  | 47 => 0xcc9
  | 48 => 0xcce
  | 49 => 0x1709
  | 50 => 0x170e
  | 51 => 0xd09
  | 52 => 0xd0e
  | 53 => 0x1889
  | 54 => 0x188e
  | 55 => 0x589
  | 56 => 0x58b
  | 57 => 0x58e
  | 58 => 0x178e
  | 59 => 0xe89
  | 60 => 0xe8b
  | 61 => 0xe8e
  | 62 => 0x1789
  | 63 => 0x178b
  | 64 => 0x18c9
  | 65 => 0x18cb
  | 66 => 0x18ce
  | 67 => 0x138956
  | 68 => 0x98956
  | 69 => 0x209
  | 70 => 0x1549
  | 71 => 0x14c9
  | 72 => 0x2c9
  | 73 => 0x4b
  | 74 => 0x124b
  | 75 => 0x3c9
  | 76 => 0xcb
  | 77 => 0x15c9
  | 78 => 0x12cb
  | 79 => 0x1609
  | 80 => 0x130b
  | 81 => 0x1689d6
  | 82 => 0x17c9
  | 83 => 0x5c9
  | 84 => 0x1049
  | 85 => 0x140d
  | 86 => 0xb4256
  | 87 => 0xb5456
  | 88 => 0x24d
  | 89 => 0x144253
  | 90 => 0x1456d6
  | 91 => 0x24b56
  | 92 => 0x58251
  | 93 => 0x144d
  | 94 => 0x58256
  | 95 => 0xccd
  | 96 => 0x170d
  | 97 => 0x16d456
  | 98 => 0x59451
  | 99 => 0x59456
  | 100 => 0xb8296
  | 101 => 0xb9496
  | 102 => 0x179496
  | 103 => 0x178296
  | 104 => 0xb8d16
  | 105 => 0xb9896
  | 106 => 0x20d
  | 107 => 0x185496
  | 108 => 0x59496
  | 109 => 0x184d16
  | 110 => 0x58cd1
  | 111 => 0x58cd6
  | 112 => 0x59711
  | 113 => 0x59716
  | 114 => 0x58d16
  | 115 => 0x178d16
  | 116 => 0x179896
  | 117 => 0xe8591
  | 118 => 0xe8593
  | 119 => 0xe8596
  | 120 => 0x58e96
  | 121 => 0x178e96
  | 122 => 0x18d796
  | 123 => 0x1798d6
  | 124 => 0x104b
  | 125 => 0x194b
  | 126 => 0xb0211
  | 127 => 0x585d1
  | 128 => 0x5c591
  | 129 => 0x5d791
  | 130 => 0x597d1
  | 131 => 0x59a51
  | 132 => 0x17d791
  | 133 => 0x5d8d1
  | 134 => 0x59791
  | 135 => 0x25253
  | 136 => 0x4253
  | 137 => 0x124253
  | 138 => 0xbc253
  | 139 => 0x14c253
  | 140 => 0x28253
  | 141 => 0x29453
  | 142 => 0x25493
  | 143 => 0x25853
  | 144 => 0x24293
  | 145 => 0x148253
  | 146 => 0x149453
  | 147 => 0x24bd3
  | 148 => 0x296d3
  | 149 => 0x25453
  | 150 => 0x28b96
  | 151 => 0x29616
  | 152 => 0x29796
  | 153 => 0x104b91
  | 154 => 0x24215
  | 155 => 0x105851
  | 156 => 0x29493
  | 157 => 0x104591
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2123
  | 6 => 5386
  | 5 => 2207
  | 4 => 28
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
  | 7 => 2*((h/714+packedAt gbK7 (78551+(h % 714)*12) 12) % 2123)
  | 6 => 2*((h/1879+packedAt gbK6 (258528+(h % 1879)*13) 13) % 5386)
  | 5 => 2*((h/742+packedAt gbK5 (130213+(h % 742)*12) 12) % 2207)
  | 4 => 2*((h/16+packedAt gbK4 (1960+(h % 16)*5) 5) % 28)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffffc1f803f03e07ff07fe00067d8cff889e7c
  | 1 => 0x3c01fe0003ffffffffffffff199273300fffff
  | 2 => 0xc001fffffc003ff81ff83fffe1e383c3f0e38f
  | 3 => 0x1ffffffffc0001fffc000fe03fc03ff03f0
  | 4 => 0x1ffffffffffffe0000000fffc0003fffc00
  | 5 => 0xfffe00000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x443dc058d0b20e432746720602248457888e3c
  | 1 => 0x28440a000154528c490884aa089031300334d5
  | 2 => 0x8088d4ab5400255112d23954616382c1b0c30a
  | 3 => 0x11167359a6a80021ce71018b603dc02dd03e0
  | 4 => 0x2221b9c6e38f39e780042060dffc00036ef800
  | 5 => 0x33c00007000c018400800180fddb6ba8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafcc8c8c0feeaeeeafcc8c8c0feeaeeeafcc8c8c0feeaeeeafcc8c8c0feeaeeeafcc8c8c0feeaeeeafcc8c8c0feeaeeeafcc8c8c0feeaeeeafcc8c8c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40499
namespace PEqualNP.Outside.L_meta_40499
open PEqualNP.Outside.L_meta_40499.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 60 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 165 := (concat bs0_4_0 bs0_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 50 := bs0_5_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 99 := (concat bs2_4_0 bs2_4_96)
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
theorem bs4_3_0 : Interval s4Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 2 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 6 := bs4_4_0
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
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 6 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 56 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 781 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 (concat bs5_4_672 bs5_4_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 801 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 (concat bs5_5_672 bs5_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := bs5_6_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 28 := bgb_4_0
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
theorem bgb_5_2112 : Interval gbAtlas 5 2112 95 := block_range (n:=95) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2207 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960)))) (concat (concat (concat bgb_5_1056 (concat bgb_5_1152 bgb_5_1248)) (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536))) (concat (concat bgb_5_1632 (concat bgb_5_1728 bgb_5_1824)) (concat bgb_5_1920 (concat bgb_5_2016 bgb_5_2112)))))
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
theorem bgb_6_5376 : Interval gbAtlas 6 5376 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5386 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576))) (concat (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)) (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 bgb_6_1248)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1440 bgb_6_1536)) (concat (concat bgb_6_1632 bgb_6_1728) (concat bgb_6_1824 bgb_6_1920))) (concat (concat bgb_6_2016 (concat bgb_6_2112 bgb_6_2208)) (concat (concat bgb_6_2304 bgb_6_2400) (concat bgb_6_2496 bgb_6_2592))))) (concat (concat (concat (concat bgb_6_2688 (concat bgb_6_2784 bgb_6_2880)) (concat (concat bgb_6_2976 bgb_6_3072) (concat bgb_6_3168 bgb_6_3264))) (concat (concat bgb_6_3360 (concat bgb_6_3456 bgb_6_3552)) (concat (concat bgb_6_3648 bgb_6_3744) (concat bgb_6_3840 bgb_6_3936)))) (concat (concat (concat bgb_6_4032 (concat bgb_6_4128 bgb_6_4224)) (concat (concat bgb_6_4320 bgb_6_4416) (concat bgb_6_4512 bgb_6_4608))) (concat (concat (concat bgb_6_4704 bgb_6_4800) (concat bgb_6_4896 bgb_6_4992)) (concat (concat bgb_6_5088 bgb_6_5184) (concat bgb_6_5280 bgb_6_5376))))))
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
theorem bgb_7_2112 : Interval gbAtlas 7 2112 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2123 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 (concat bgb_7_576 bgb_7_672)) (concat bgb_7_768 (concat bgb_7_864 bgb_7_960)))) (concat (concat (concat bgb_7_1056 (concat bgb_7_1152 bgb_7_1248)) (concat bgb_7_1344 (concat bgb_7_1440 bgb_7_1536))) (concat (concat bgb_7_1632 (concat bgb_7_1728 bgb_7_1824)) (concat bgb_7_1920 (concat bgb_7_2016 bgb_7_2112)))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 32, 33),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafcc8c8c0feeaeeeafcc8c8c0feeaeeeafcc8c8c0feeaeeeafcc8c8c0feeaeeeafcc8c8c0feeaeeeafcc8c8c0feeaeeeafcc8c8c0feeaeeeafcc8c8c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4241017024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40499.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,4]⟩,⟨.and,[1,3]⟩,⟨.and,[3,4]⟩,⟨.and,[0,7]⟩,⟨.or,[5,6]⟩,⟨.or,[1,8]⟩,⟨.and,[2,11]⟩,⟨.or,[0,7]⟩,⟨.or,[9,12]⟩,⟨.and,[10,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4241017024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4241017024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40499

open PEqualNP.Outside.L_meta_40499 in
theorem PEqualNP.Outside.L_meta_40499 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4241017024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4241017024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
