import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36400.Model
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


end PEqualNP.Outside.L_meta_36400.Model

namespace PEqualNP.Outside.L_meta_36400
open PEqualNP.Outside.L_meta_36400.Model
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

def SBf (j : Nat) : Nat := [7, 7, 6, 8, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36400

namespace PEqualNP.Outside.L_meta_36400
open PEqualNP.Outside.L_meta_36400.Model
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
end PEqualNP.Outside.L_meta_36400
namespace PEqualNP.Outside.L_meta_36400
open PEqualNP.Outside.L_meta_36400.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x38008802c000004a00b803c000000000c80181c0000a4d2263ea04004208500000158000000010011180006ce80200000352000150001380003470600a8000002400000680004000900005000f0060022000000016000000000002000608000000c000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1e2a299e928009800c00100c88961ca12180048e00080e8418a3a71aa41f821094181b990000292817139480a880118000028013261d87a79c12000a998f8ba083a301002295858026a5a22b1b0d890b2aad1d2bac801f000024802c0006818525032007168d17951a0a112d860f000682002438400000000004180001c00806000031e9c180040c482cea18876e5210edaa421d794c42aea98853e540ca7aa8195794f41aea9e836e52d06daa5a0d794e41aea9c836f52506d8a4a0cf953319eaa6636e52cc6daa598cf952319eaa4636f524c6d8a498db94621b6a84433e540867aa810d794c21aea98437a50086f2a010eb95021d6aa043ce530879aa610db94421f328843ea50086daa010fa54021b4a80436e52902daa52057d4d40ae29a815e53102baa6205b94840b6a90817651102eaa2205b94a30b6a94613f544c278a8984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9905794f20aea9e41ae54c835aa9907394f20e6a9e416e51c82daa5105b14520f5a82416e52082dea5885b14b10b7294216d52843d241084fd51109e2a2215f53442b8a6885bd4910b629221e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x60a0008ec020004030c350d5210f0d5454c21ca95150087295454021d294d50087495354021c355153c82686548110
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 5 => packedAt s1K5 (802+((h/14+packedAt s1K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s1K4 (2694+((h/30+packedAt s1K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s1K3 (312+((h/2+packedAt s1K3 (304+(h % 2)*4) 4) % 16)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xc1ffff83ffff0f07f0fe1fffc3fff81e89f3f3
  | 2 => 0xfe1f0ffc3e1ffff87f0fe1c1fc383fff764c9f
  | 3 => 0xffe00fffc01ff1ff800ffe01ffc03fe1878f1c
  | 4 => 0xfffffe001fffff00001ffffc001f80fe0
  | 5 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x44020088040010008012024440488844009131
  | 2 => 0x88841110902a00283104208884111298324486
  | 3 => 0x144aaa290d548353888b54156a82a545858b18
  | 4 => 0x3954cc42a906a59d5aa11021b3270189d80ec0
  | 5 => 0x219888733198c9e66ccd993822040611ef6000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaaaf0a0fafafaaafaaaf0a0fafafaaafaaaf0a0fafafaaafaaaf0a0fafafaaafaaaf0a0fafafaaafaaaf0a0fafafaaafaaaf0a0fafafaaafaaaf0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36400
namespace PEqualNP.Outside.L_meta_36400
open PEqualNP.Outside.L_meta_36400.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x49c805000b414061046310dbf43bd43ee32ed32bf41bd41ee21ec21be40bc40ef20ed20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xd841009400058d434ca3aa7a0d354c21b4a80431d531026aa2205354f20
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (208+((h/4+packedAt s2K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s2K3 (197+((h/2+packedAt s2K3 (189+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf87fffc1fe1fe1e1f87f0fffc3f87f0749f673
  | 1 => 0xff8787fe3fe1fffe1f87f0e0fc3f87ffb6499f
  | 3 => 0xfff807ffc001fe3fe007ff00ffc007f8c78e1c
  | 4 => 0x7fffffe003ffff80000fffff800f80fe0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x9010044042002002009012240481112009231
  | 1 => 0x10200888100280040882104404120244124086
  | 3 => 0xa31355148d55506ae445aa0aea8134b2c58e18
  | 4 => 0x86546621291054b355508810b3256020e80d40
  | 5 => 0xc4664439b199993d9e66cc9c220640c4ff6000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36400
namespace PEqualNP.Outside.L_meta_36400
open PEqualNP.Outside.L_meta_36400.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x20e800000d803e8c029004020300014003c686130c980212e70c98220128b002848f1c480160a9d20d0200a072a890000400a00018a05c040000003ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2206fd0440dea08817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3bc87987750f30bf296617d52cc3be6598774cb30bf28e617d51cc37e83986f50730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa3186fd0630dea0c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930ef99261dd324c2fea2985f14530dfa0a61bd414c3be6298774c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6185f94830f7290616e520c2faa4187b54830b6a90617e510c3eca2185d94430bea8861f5510c2eaa2186fd0430dea08617e500c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c83dc85907b50b20f719641ed32c82fca3905f54720dfa0e41bd41c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3106fd0620dea0c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42483dc64907b4c920bfa8a417c514837e82906f50520f790a41ed21483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2106fd0420dea08417e50083de40107e88020f690041f920082fea9885f95310df2a6213e54c42faa9886f553109eaa6217c54c42fea7885f94f10bea9e217c53c42fea5885f94b10bea96217c52c437e83887d90710dea0e21f541c436a83887d8c710fa98e21f621c43ea43885fd5210bf2a4217d54842f8a9085fd4e10bf29c217d53842f8a7085fd4a10bf294217d52842f8a5085f54610dfa0c21bd41842fca1087e8c210fc98421fa20843f241087dc4210fd884217f54442fca8885f55110be2a2217f53442fca6885f54d10be29a217f52442fca4885f54910be29221bf41443ec82886f50510faa0a21b541443ec62887d4c510fb10a21f521443f460887e4c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821bf410437a82085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a0657d540caf8a8195f94c32bf29065df320cbdc6419774c832f699065cd320cafca2195f54432bf280657d500cafca7a0df54f41dfa1e83be43d077a87a0ef10f41bf296837d52d077e85a0ef90b41dea1683bc42d06fca1a0df54341dfa9e83be53d077aa7a0ef14f41dfa9683be52d077aa5a0ef14b41df99683be32d077a65a0ef0cb41dfa8683be50d077aa1a0ef14341beaa4833d54906fca720df54e41bf294837d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077c86a0ef50d41de21a837f52506f8a4a0efd0941df21283bd425077884a0fdd0541df20a837f50506f8a0a0efd4d41df29a83bd5350778a6a0efd4941df29283bd5250778a4a0efcc941df19283bd325077864a0efd4541dba8a83bf505077ca0a0ef54141de282837e541067ca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31ef99663dd32cc77e8398ef50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31bea94637e518c77e8318ef50631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7be6498f74c931dfa0a63bd414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831f7290636e520c6faa418fb54831b6a90637e510c77e8218ef50431ef98863f6310c7ba6218fd4c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87dc6590fb4cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53886faa710df14e21bea94437e518877e8310ef50621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f719243ed324877e8290ef50521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e510877e8210ef50421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40dfa1e81bd43d02fca5a05f54b40dfa1681bd42d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40bea9481be429037885205f94640bea8c81bf419037a83205f94240dfa0481fb40902fea6a05f14d40dfa1a81bd43502fea4a05f14940dfa1281bd42502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a
  | 2 => 0xbb07300c808840000002e8f40bf000000000004967b16d1eb0b2001008004421bd2482c000000001100e248d2f9514a2000a3800142a10ea97a00081c7b0000003f4d9a6c0720a8a700000000000000000a9517000032000669b80007c02f000000a749fa913fc4281fad948e0005591a30a82d1c891242235300000001ad118ed3c8aace48004bc350000c357a000f69c31f8184042574d40a0b9000528068001014ca9501211f0f257d431cb2e20014b16a1f2000e807d2305dc19827218000c21693262f40000000003c690b95123c0ad98d38e291571da18e6c8000000fe8804a8e906c568710bb3d4844d621500039c15800000a7d2180026a0000d80000000154a5d2b2810002793b6514d00004140000000000075c8124202c05804010040001600008050000000401000018000286c0180a0000412054058040080e01000038000000c06824000060801000002038060200004814008240502800820000000500200002000060500c018000080001800028000183c01834010000c00c0200401004000140180800000018040300000000010000880a000000f00a0300a04802010000500400002000000080e0f826020020280802834000080080001004000060781600802000100000c1982e04800010080580402000000080180801800018000001c00000038000080c0900002022008240000c010040b802010020081c0381202004020000080800802000080000605000000160a8040000200004038040000201002018100601a008000184c0b80201822000000400000806000040701e0381a01000000000601b7e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43f7294876e5290efaa521fb54a43b6a94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a16f90f42de21e857e51d0afaa3a15f94342bea86857d5490afca7217794e42af29c857d5390bbaa7215754e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16f90d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d5310b7e86216f50c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665df43ccbb887995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32bf29465ef428cbd8851977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265df434cbb886997bd0932f621265e
  | 3 => 0x4b63c81a8004309a11b8003f4000bc8b00161250405b0f0b14b9a1a15000000000310000000002729fc6100000000000163000488471b726600141a7042c198da24059c2d00a27a596840000980127fd2209758e040000004940016a8003b8414000000007e4429d414c0009b80038c4ace1000000748732a4000000002b30000005999e3dca655ca0c1b00550a08022819cdb0ae04c560cd0fe4e4b50c700a0be2486700026c3a0000f54eaa046d92e3f0a5c228ac278a6ce98003605f43681300000142a461fe33127a270702dc608ca34c5b80005a5302a5491120005fc342d220e87c0000040c6bc0000009a080c00004982095a28d1166642089a0ea9bd6c0005b6ab00000000001c4c8000002742a0342687104480200000000000000000000430003b11e85d076628002710b0968ec00000044568a9c2c862c001e92a80013a090450aa85a87034e0007522a4ee84c000e4000300ee8001f60b85001f4000840c1fb54629c1d2c2178afc0000021eaec868003568c8019001e80000014f350000cd8000000f400000000000000d059e0015d00000a81533a4841a0015aa1c328a1c2b8461e2500002804a46ed1691e0441540e00013e54cf3a9500042c352192cc9704f0720dc9356e00000000000000000954000ee2c41a43e000000a793c23a0000001f11c000381159523bc9644a1f117040c0021e59a074c880057c258f010e1187d80013a2d052c8b2a60005712b27e0a6894a40c81c608c72a2f3be318af1865900003623e000990000d7318574b7800540b1158800080000e50a51ba7002912922e000261d11e69b4e680e4cc1e92c14d34632cbd8ef03c73d478000c4a38ce8a315e368c48de16212cd8aa73784ed04856482b0012a505aea30649a4354899198d527c00150aad0000009309b41e4b1649f24dca08bf0000600000880c0007d5358002826551f9130006b8901b549c2d8bc084526784001ba2aa5b47b800000220628ad0000011b0000645b09387b248364d29312c01dc318000005ac0018f000474090d101a98960a63000838001060008d49904a000000c180051400018ad61b885c0000039867d0d961564000001305989f0a32b80009f469ad327041000000000ac0d08171d64243b149544001110cf18819000175000000ab1ef5504a08d8000080015b14410c6fc4092a2e82709ea310b80dc3a1bd00065c49800424144001c5000000e4000000000eb0445168a42804e164120a194a0525f16f06543a9cc510161544656e92d4a67d0279d95949d82380039c000002c64700006fa3b25e3e8ce00005a594001874f60005f1e3586384f112510e55cfe9ad4480bc00000000a681e1961acb40001a20000011e181000914d48003e65c045269468109182af3cc5304799000079400115002a40e0a2c1066493080000
  | 4 => 0x15b950510000a11823306e4001f74067f0df07e2ce1807c2bc
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x5414823c65505209798f540825d63d50209d987540827561d50208f596540823d61950208fd85540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c530826e6214c209d98453082756114c208f992510823d6494420cd95251083355494420d594e51083555394420cd99251083356494420cd95151083355454420d594d51083555354420cd991510833564544208fd97410823d65d0420c794f410831d53d0420cd947410833551d04208fd95410823d6550420c794d410831d5350420cd94541083355150420cb553200834d53c8020d9547200837151880209bd95200832d5448020d354d200836551480209ed9520083715148020cd98654c423e64d4f108f59353c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c423e6414b108f59052c425e6314b109758c52c43365450710add9541c43376550710ad59231c42b564887109798c548425d63152109b988548426d62152108fd91538423c6454e108f990538423d6414e109b988538426d6214e108fd91528423c6454a108f990528423d6414a109798c528425d6314a1097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d108f990534423d6414d109b988534426d6214d108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d6314910ad59241442746550510bc18141443376550510cd19541443b36050510ec18141442b5648c5109d19531442b564885109d19521443b1418c1109e19530443b1414c110f44c530443b141881109e19520443b14148110f848520443b141c41109798f540425d63d50109b98b540426d62d50108f596540423f61550108f585540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c109e980530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520427661148109e980520423e64944108f592510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb54941043365150410cd553100435553c4010d954b10042796584010d654e100436952840109dd9510043355444010d554d100436552440109ed9510043595344010da54910043b34144010
  | 1 => 0x87395494021d694e50087595394021ced0650087394194021ce95150087395454021d694d50087595354021ced0550087394154021dac8550087722154021da485500877121540219b98a53d026d6294f409798e52d025d6394b40cd54741d02ae6290e40a798e42903365150640cd545419023e65d0d408f997425033751505408f596431031d5390c40ab98a431031d5310c40d394e521034d5394840d394d521034d5354840cb90d521032c43548408f596421029e6390840c754e421032d5290840c754c421032d5210840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cd99151103364354440cd10d51103364254440cd109511031e53d0440c754f411032e52d0440cb54b411033551d0440c794d411031d5350440cb949411032d5250440cd945411031d53d0040cb54b401033551d00408fd95401031d5350040cb549401033551500409ed95401026e62d53309b58b54cc2cd6290f308f99252cc23d6494b30a759332cc23e64947308f59251cc26e62152309b588548c27661152309d584548c23f6454a308f191528c23e64946308f592518c3365150630cd545418c23d61d51308f992544c23e6515130c758c544c23d6115130c7152434c2cd6290d3097195434c29d64cc930c7153324c31c544c930d3149324c23e64145308f590514c26e62145309b588514c23e65d05308f197414c23e65505308f195414c26e62d50309b58b540c27661d50309d587540c23d65950308f586540c23f61550308f990540c25e63150309b988540c26d62150309d984540c2756115030cb952520c32d5494830cb951520c32d54548308f992510c23d6494430cd952510c3355494430d994a510c3655294430cd992510c3356494430cd951510c3355454430d9949510c3655254430cd991510c33564544308fd97410c23d65d0430cb94b410c32d52d0430cd947410c33551d04308fd95410c23d6550430cb949410c32d5250430cd945410c3355150430c7553300c34d52cc030d5547300c371518c03097d95300c31d544c030d3549300c355514c0309ed95300c371514c0309798f54c825d63d53208f99353c823d64d4f208f99253c823d6494f20b358e42c82ad648cb20d314d32c823e64947208f59251c825e63152209758c548827661152209d584548823f6454e208f191538823e6414e208f59053882766114e209d584538823e64946208f59251883365150620cd545418823d61d51208f992544823e6515120cb588544823d61151208f992534823d6494d208fd91534823c6454d209dd8553482746154d20cb15242482cd63909209b19542482ad648c920cb152324826c654c920cb151324834c534c9208f990514823d64145209798c514825d63145208f997414823c65d05208f99
  | 2 => 0x6494c328f992520ca3d6494832b358e320ca5f654c8329bd95320cacf654c832d3d95320cb4e544c832d3151320ca3e64944328f592510cb4d32544328fd91500ca3c6454032d34c9500ca6e6294f419b58a53d06ae6290f41ab58a43d071d5310f419798e52d065d6394b41a798e42d069d6390b41cb54842d06ae62d4f41ab58b53d06b561d4f41ab98a53d06ad6294f41c754c53d06b56114f41a798f52d069d63d4b41ad58752d069e6394b41a758e52d072d5214b41ad58452d063e65ccb418f59732d063e658cb418f59632d078d320cb41a798c50d069d6314341ab98850d06ad6214341ab98a43506ad6290d41c714d435069e6390941a758e425072c52509419798c505065d63141419b988505066d6214141ab98a53506ad6294d41ad58653506b76154d41c754c535069e6394941a758e52506b56194941add85525072d52149418f997325063d65cc9418f996325063d658c941add8532506b4614c941e34c832506b6610c941ad58432506b560d4541a7d8d505069c6354141abd8950506ac6254141a798c505069d6314141ab98850506ad62141418fd9541106776550441cd951411066e62d53319b58b54cc63e6494b318f59252cc63f64543318f19150cc66e62951319b58a544c63e64d49318f593524c74c524c931b5185324c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f990540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c72e5454831cb551520c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc43197d95310c74d524c431e5505310c677654c431ce952500c7395494031da94a500c7695294031ced06500c7394194031ce951500c7395454031da949500c7695254031ced05500c7394154031d6cc5500c7723154031d64c5500c77131540319798f54c865d63d53218f99353c863d64d4f218f99253c863d6494f21d314d32c863f64543218f19150c863e64d4e218f593538863e6414e218f590538867a6014e219e580538865e63951219758e544863e64d4d218f593534863e6494d218f592534866c654c921d314d32486e4614c9218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219b988530867a6014c219e580530863e64944218f592510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410874d53c84219bd95210874d5348421e950521086776548421ce952500
  | 3 => 0x5f1a84040488c1ca000000004b40003100053e744e60af1d2a403d80c3ae8954916307e194978aa360a70cb04c1f66b947116026078cd2a00dc5112582d55e9e4052b217a8d83ea180aa050d884425a9f85e0a232479060a7c0fc0480d8992c05a4eaabf094000002ad0003892380042053c6d82202a500281e14d20011499b37221000000000000db800488001230410000000016e41c000000002d80992909e0009c0810732bca3107ab33ea87c750ff42aa3cd29555328700000050e0009080045c20443933000354001c2402620159ea2583700011001c0000007c16400084a934949b8a39dc000761520a157c2dc8598a4347a02e8000f40d0330471dc735270004a065ce0aa23dc1682f0003460000029a476000f1a1227c2d0c19e221c8e059a414001b11a00028c7b4aa00201e00139aab56cb113590843c0bce90fe1f07bc4a20d28a430c0a97404660108fd1526781018b33a33008023388981178d636c4d8320493045907d27b2861813ba2252a018de06f1d835c992113f613962a200a819c38a5704e32d5babd56a298948303bc434242803d86fcd30c62923c81d800000010540200002090070100600c0700c0904419018030300a090000080000015020000000101420014000000101c1401400000000084a0000900c0101c010343804c3301c0800009018000140100023024040a80200800000050141c000020981d0005e0000000404084020000101c0200406038000040104000060000400f00010020270080100403064140d80507c050300303c0101001018000000300404004050682b004030300d00802004000440000023004000440001416094000080500006000060e4020000107402000271880006402010320082c010020bc2f0300200c0500002000021780300800000270000601411010190f01e064040b4010282a0000200c070180001c0100c30000040500102804004050100009c010380300c0801c0502404cbd0e5290f4f4354a43ab98a4350e6e62141439b5885050e7661141439d5845050ecd6290c438fd954310e5f6550c43ab98a43d0b1e53d0e42c794d4390b1e53d0a42d354f4290aae6290d428f9944350a9e63909429798c5050a5d63141429d9845050a7561141428fd954310acd63908428fd954210a6f65508428f58654ccb1c63553328fd8554ccb1d54d0f328f99251cca3d64947328f586548cb2c62552328fd85548cb2d54d0a32c7953328caae64cca328f992518ca3d64946329d986544ca75619513297997434cace62d0d329b997424cace63d0932e310f424cb8f4310932ab993324ca9e648c9328f990514ca3d64145329e980514ca7960145328f990504ca3d64141329d984504ca7561141329798f540ca6e62d50329d984540ca7561150329e980540ca7960150328f992530ca3d
  | 4 => 0x1e0474e99ab4cc0c423095340944ff13918e49c2c07949a55ca59520581d15426306e9911fa98000654d2008412460fa1fa074b049816b0da39d1e0820002953a17f49e268401610165e06e8534c218cc493a4d444cae8005280007780000064d5496624c3900d20c4a812d5e2210009c86021d0ae0f491977222001050d2000a280009c19a0005f19f2700015700013e00000000376000000de00040cbea48386000029f0568930708005585b4a715631e41c3b0b13fe61c001ac454365580a02e47f5518c338e4dc1b21408aae52a8cf47a5f8519f8354060f009800044911a6517076c1e0ce05c720e59041a045cf289003e9c4491b20ac650018192624646d0754582b9410b62d05d90d8e000020c699e62786f41c89d190a10198c43326144994d1726cc001be0008e4ba1800e48dc6f80000081558a7a3be0008d80031c000ea191416000648002b00d482aa62f63c47e0003e4004351f11747190b0002ea1dc2fa2d34e26c002c0586594718001e80016120702c9d5469480007e42c8002540c8200000006e8002580007dc001e94649580011e484898002a70002d40000011016c000000d2000ad249408229158002e20000001c00043c4b11a0701e0002430007f08500054a000d49060c2001369e7000000000001120003588d4bc000aca7f000000902833ac0005605c04a96d298f939247d44070052490152272845f0e29d9338a78a61510866e0b79ca2f2455140072565292e0a427e8640e8bf480700d680046a001041b40005c0470861ea9d8d10ad01aae0c328127a25d5d928462000000ab5421fd5d000000000001eb4c43dcb380002247133a5939e540002c631aa58542c74066106c0e802e23cd4134554010fb25d2a60007b10009a001198854f08e83413535e314610001600000004f000000121d044800097141536818002131a20f8bd0ca2280002915c3e63ac458283202ecb9842000a2492a6f0009a0489a1318a454e92250aa1879a3e48a000ed2302b6000001623ba0000000036a4ed0b8002be1453628b14e000b50ed1cc7393ea
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x326a9a41ed0a008724c804968baa02000606b2e000e20c000143b61014012444410192e873a6ca99065515c4544c832a92e02a2641943571191500cb0632264a80652c5c0614c941d0a64b0864a0cd170185324c782a928298863c450531540319c2e030a6490f05535052108790a0a42a80438354e6290c40c1cc6a9484205267290d511028b39c84a8881831516290d3083aec2a6649860c5458e4248216bb0a919241345cc60505109c2e430282885917318141442d0b90c0a0a212c1d9414c110960eca0a408853175d051004388a9e8288021c854b4144010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x8905819d3654c832a05811913254032
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 735
  | 4 => 712
  | 3 => 30
  | 2 => 2
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
  | 6 => packedAt s3K6 (756+((h/14+packedAt s3K6 (672+(h % 14)*6) 6) % 56)*7) 7
  | 5 => packedAt s3K5 (22295+((h/245+packedAt s3K5 (19845+(h % 245)*10) 10) % 971)*11) 11
  | 4 => packedAt s3K4 (29426+((h/237+packedAt s3K4 (27056+(h % 237)*10) 10) % 855)*11) 11
  | 3 => packedAt s3K3 (1530+((h/10+packedAt s3K3 (1470+(h % 10)*6) 6) % 37)*6) 6
  | 2 => packedAt s3K2 (122+((h/1+packedAt s3K2 (120+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xcf1fe3fff0fe3f8fc38c7c7ff1f87e1f04f4cf
  | 1 => 0xfe1fc38ff1fc7f1fc0f8f8e1e3f8fe31b4b33
  | 2 => 0xf001ffc0ffe007fe3ff00ff01fc00ffce38c3c
  | 4 => 0xfffe0000fffff8003ffff0001ffff000fc0fc0
  | 5 => 0xffffffff000000003fffffffe0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x41002000100040100000101200480200001045
  | 1 => 0x2208410122080a020804848442120482094112
  | 2 => 0x80d48892444495005590092094812958628c28
  | 4 => 0x4441aa488940124a6a9200119256048b40e80
  | 5 => 0x289913300ed926493b4e4e49c0064192dfe000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefeeaeaeeeee8e8fefeeaeaeeeee8e8fefeeaeaeeeee8e8fefeeaeaeeeee8e8fefeeaeaeeeee8e8fefeeaeaeeeee8e8fefeeaeaeeeee8e8fefeeaeaeeeee8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36400
namespace PEqualNP.Outside.L_meta_36400
open PEqualNP.Outside.L_meta_36400.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe8052200001245400000001b005469038380000000000000001616796af4c2801200b010500015145c0078744682000000000005d0253e000a33064180000000000ad3804800000000000c260000042000060000000800200081080c0060000001ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x50208ec003e001200058258681c6d0f8c0001311888007037978540f170004083000000000261f50000000010a5a3e00010821e8100069090700064000000e361c00000002c8003234229e83000001a8a23c049c82e151589c6e0b0621800321c8008e3121000003a339d4886500210c426141fc1a6c19890cc00340b0a84d0300c1460169849200000002216010d4ba5c2514c0073271c4be00001b8aa004387800253a0007e21001e0001b358745263081e4ae052d80102403b13cac5200000867e3b918022f3d8500001000000000610000406010206001713020f0200000202050600010102020103000b04040b050001010d000b0cbd28487795090e7aa3a14f943429eaa485af5250a7ea2a14f141429f2a0853e548ca7aa9194f950329eaa06576510caeaa2195e94032bca80653d52d067ca1a0cf552419fa9283b75150678a0a0cf950419f2a4633d548c67ca818cf55031b7290636d520c6f4a018de540319f2a6433d54c867ca910cf552219f2a2433d54486bea690d714d219f2a0433d54086bca610d754c21f2908437a50086f2a010d794e40aea9c819e539033aa7204f54a409ea8c813e50902bca6205754c40b7290816d52102eca2205d54440cf298819d531035ca4204f54840d6a90812d521036ca2204f54440daa888135511027ca0206e940409f2a6613d54cc33ca9986755330cfa16619d42cc33e83986750730cf206619c40cc2baa7186e102309faa2613c544c370809867d5130ce2a2619f424c33a849867d0530cea0a61db504c3b680986790130ce20261d8404c33080985794c309f2a6413d54c835a85904fd52209e2a4415e53882baa710764c2209faa2413c544835a8490764c1209f2a0413d54082bca6105754c20bb2884175510827ca9884f55310daa0e213f5484278a9085794e10aea9c21d9308427ea8884f15110daa0a21d9304427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x4380131ec142a00b4a804874c874c790120268b2b007018000517915284d905c1068a46202803e5cc2c123002700c4006002c0224a40a0020140002430400401478d5845050a2d62141418e18154486596014d21d154d21087612154021c394d521030d5354840c954a51103165354440c554d51103265254440c954951102996394040a358840cc2956110330aa588408c2b16110230aa588404c2b16110130a6181424c2986050530a6993504c21e6590130a6982404c21e6510130a3588404c2956110130b2588404c2d16110130a6994404c31a6510130e2988404c2996210130e2588404c2896210130e4984404c2996110130e4584404c29161101308d5845488318544c2208b1954248318544c120e2509304822d6215210c615130842346550510c61513044391414c110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x2200000314000006441c005245c46050930912e4302829868162984404c341312c220261a05896110130a22e22a26110508755093048284b90a898421441d5414c110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => packedAt s4K5 (880+((h/16+packedAt s4K5 (768+(h % 16)*7) 7) % 99)*7) 7
  | 4 => packedAt s4K4 (4032+((h/45+packedAt s4K4 (3672+(h % 45)*8) 8) % 180)*9) 9
  | 3 => packedAt s4K3 (1996+((h/16+packedAt s4K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s4K2 (453+((h/3+packedAt s4K2 (441+(h % 3)*4) 4) % 16)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1e3f9fffc1c71e3f1c71f1ffe3870e3f0cf90f
  | 1 => 0x1fc7e1e3fe07ffc7e07e3e383c07ffc73341f3
  | 2 => 0xe007fe03fff81ff8ff803fc03ff80ff8c38e3c
  | 3 => 0xfff80003ffffe000ffffc0003ffff000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x428084404408244004104048a0912212041905
  | 1 => 0x84110804881208082022121104024484114052
  | 2 => 0x1220089108050014880248209200920428228
  | 3 => 0x488055522504049295548004b254a012ac0d80
  | 5 => 0x9134598039a69924fa6939270060c1a4fbe000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafce8fce8feeafeeafce8fce8feeafeeafce8fce8feeafeeafce8fce8feeafeeafce8fce8feeafeeafce8fce8feeafeeafce8fce8feeafeeafce8fce8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36400
namespace PEqualNP.Outside.L_meta_36400
open PEqualNP.Outside.L_meta_36400.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x41098006000028a54011922a9089a163c1a14e9401e2070600266c016321ca01008901f1c000021a00b8900a15800060e80520800ce2800c600e003001ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc800000260bad210009ac00118513000015ad80001a8016802a80280b1d802097002b9e80181214801c01001e0002a9038d94221f05888029a7069a2880020c239500219b24092580000003002c8013989101a32790a0268700000486000e1c8d1987a51d129f8022aa0f0f978a8e9b8419008010160a0824ab010302304042c0c00010102800600285121420402004050000208b7296876d52d0ef4a121de54243af29e855d53d0b3ca7a16754f429eaa485af5250a7ca8216b50b329f2a4653d548ca7ca8194f55032d6a106576510caeaa2195e94032bca80655e53106baa620db94841b6a90837a50106f2a020cf950319eaa0636e520c6daa418de94031bca80633e54c867aa990eb50b21afa9a435c534875a8490cf950219eaa0435e53086baa610de94021bca80435e53902baa7205794c40aea98816e52102daa4205d94440baa88813e54cc27aa9986795330ceaa6619f42cc33a85985754e30cfa12619d424c3b6a09876d0130ec202615e530c27ca9904f55320d6a16415e53882baa710764c220d6a1241d9304827ca8104f55020af298415d53082eca2105d54420af29c215d53843b261084fd51109e2a221d9304427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x903880514c00200f0300208ced5803088049658253d0a996094f42a398f5250b254254432ca509500ca596014d21c314d424862d6295330a358a54cc21d65d0b30a6993504c2c96210130b4584404c389424c1208b5885444318544c110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x6810912e131ea4a15097014d4248644b94c9a8261425c8544c110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 16
  | 2 => 4
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
  | 4 => packedAt s5K4 (2694+((h/30+packedAt s5K4 (2484+(h % 30)*7) 7) % 122)*8) 8
  | 3 => packedAt s5K3 (633+((h/5+packedAt s5K3 (608+(h % 5)*5) 5) % 24)*5) 5
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf3c7e7f1fc38c71f9c63c7e3e3871cf8d390f
  | 1 => 0xf03f9f8fe3fc0ffe3e07c78fc3c07ff192c1f3
  | 2 => 0xffc01ff003fff07fc7f807f003ff81fe630e3c
  | 3 => 0xffffe00003ffff8007fff80003fffe007c0fc0
  | 4 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1850222204810a2004208120a091445041905
  | 1 => 0x10080400048020004000408400402080004052
  | 2 => 0x22024804491101400a88052090920128230228
  | 3 => 0x4491016a922a0824955690012b254c055c0d80
  | 4 => 0x8822514c00334a4927a52649b00608287ba000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeefce8feeefce8feeefce8feeefce8feeefce8feeefce8feeefce8feeefce8feeefce8feeefce8feeefce8feeefce8feeefce8feeefce8feeefce8feeefce8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36400
namespace PEqualNP.Outside.L_meta_36400
open PEqualNP.Outside.L_meta_36400.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x280083200287283e895805e98b2440b1f8600611ae02a92806049f0272dc5a1182089978d028474000173a3c3ad000149300f4009009db3300d401e76c4e000001c0d0000d80065401a030008001001008b0601e800020d800a80d8002ffd5009fe54007f55009fc5401ffd4c07fe5301ff54c07fc5301ffd0c07fe4301ff50c07fc4302ffd4801fe52007f5480bfc52027fd0801fe42007f50809fc4201ffcc807fe3201ff4c807fc3202ffd44017f51017f94401fd51005f54405fc51027fd0405fe41007f50405fc4101ffcc405fe3101ff4c405fc31007fc8405fe21007f48405fc2102ffd4003fe50007f54003fc50027fd0003fe40007f50003fc4001ffcc007df3000ff8c007fd3000774c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a4000bf5952006ff8ca90016fc6548001be32a40059f19520007fec890002ff6448019ff3224004bf99120007fac890002fd6448019fe3224004bf1912006ffea890033fe5448001feaa2400cff15120057fec69002aff6348015ff31a4003bf98d20057fac69002afd6348015fe31a4003bf18d20057fea69002bfe5348015fea9a400aff14d20057fe869002bfe4348015fea1a400aff10d2000dfec490037ff5248013ff2924000fb94920007faa490003ed5248013fe292400cffd092004ffc8490003ee4248001fea124000fb5092004ff8849002bff3248013ff192400aff4c92004ff86490003ff61480017fb0a400bff98520015fcc290003fd6148017fe30a4002bf1852006ffea2900037f5148017ff28a4000ff54520006faa29002ffc5148019ffa0a400bff90520007fa829002ffc4148015ff98a400bff8c520057fa629002ffc3148013ff90a4000fbc852005ffc4290003fd2148001f690a4009ff0852000dfec090007ff5048003ff2824001ff5412000ff8a090007ff4048003ff2024001ff5012000ff88090007ff3048003ef9824001ff8c12000ff46090007fd3048003ee982400afe4c120007b26090007fc3048003ff9024009fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007ff1048003ff0824001fe8412000ff82090003ff65440017fb2a2008ff9951002dfcca88003fd65440017eb2a2008ff1951002df8ca88003ff64440017fb222007ff99110025fcc888003fd64440017eb222007ff19110025f8c888023ff544400fff2a22000ff5511003ff8a88801bff634400d7fb1a2006ff98d1001dfcc68801bfd634400d7eb1a2006ff18d1001df8c68801bff534400dff29a2006ff54d10037f8a68801bff434400dff21a2006ff50d10037f88688003ff62440017fb122000ff9891004dfcc488003fd62440017eb122000ff1891004df8c488023ff5244001ff2922000ff54910047f8a48801fff4244001ff2122000ff5091003ff8848801bff324400dff1922006ff4c910037f86488006ff6144005ffa8a2002dfd4510017fca28800bf65144005fea8a2002df54510007eaa288003755144005fe28a2002ffd0510017fc828800bf64144005fea0a2000fd50510017f8828800bff3144005ff18a2002ff4c510017f8628800bff2144005ff10a2002fd88510017fa4288003f52144005fe10a2001bfd811000ffea088007fe5044003fea822001ff1411000ffe8088007fe4044003fd2022001ff50110007f28088007fc4044003ff9822001f7cc11000ffc6088007fa3044003fe9822001f74c110037f26088003d93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0xbfd325002dfe1928000ffd8540005fec2a0057fe61500057f30a8000ff585400aff8c2a000afc615002fffa8a8000dfd45400affca2a0003fd5150001bea8a8015ff14540027fe82a0013bf4150009ff20a8004ff505400077a82a0013fc415002dff98a8015ff8c5400b7fa62a0057fc3150001ff90a8015ff88540007fa42a0057fc21500037fb028001ffd414000ffca0a0007fd5050003fe2828001ffd0140027f680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff9828001f7cc14000ffc60a0007fd3050003fe1828001ff8814000ff840a0007ff1050003ff0828001fe8414000ff820a0003df654c029ef32a6000f7595300a7b8ca98003df644c027ef3226000f75913009fb8c898053df544c027ef2a26000f75513009fb8a898003df624c001ef3126000f758930007b8c498053df524c001ef2926000f7549300a7b8a49804fdf424c001ef2126000f75093009fb88498003df614c025ef30a6000f758530097b8c298053df514c001afa8a6012f794530007baa2980035d514c025ee28a6013f7d0530097bc8298003dd414c025ee20a6000f7c8530097bc4298003dd214c025ee10a6001f7d813000dbec09800fdb604c003efa826001f79413000fbaa098007dc504c003efa026001f79013000fba8098007dc404c003ef1026001f68813000fb84098007df104c003ef0826001f68413000fb82098027ff65c80137fb2e4009ff9972002dfccb90027fd65c80017eb2e4009ff1972004df8cb90027ff64c80137fb264009ff99320025fcc990027fd64c80017eb264009ff1932004df8c990047ff54c8021ff2a64000ff55320087f8a990027ff63c80137fb1e4009ff98f2001dfcc790027fd63c801f7eb1e4009ff18f2004df8c79003fff53c801fff29e400fff54f2007ff8a79003fff43c801fff21e400fff50f2007ff88790006fe62c8013ffa964009ff94b2004fdca590027fd52c8001f6a964009ff14b2004ffe8590027fe42c8013f72164009ff50b20007da8590027fc42c8013ff9964009ff8cb2004ffa6590027fc32c8013ffb0e4009ff98720015fcc390027fd61c80017eb0e4009ff18720015f8c390047ff51c8001bfa8e400eff94720007faa3900037d51c801dfe28e4010ffd0720077fc8390003fd41c801dfe20e400fffcc720077fc639003ffd31c801dfe18e4009ffc872004fde4390027fe21c8013fe90e4000fb4872004ff84390006fd60c8003ffa864001ff9432000ffaa190007fc50c8003ffa064001ff9032000ffa8190007fc40c8003ff9864001f7cc32000ffc6190007fd30c8003ee9864001ff0c32000ffc4190007ee20c8003fd1064001ff0832000fd84190007ff10c8003ff0864001ff04320007feca90002ff6548001bfb2a40009fd952006ffcca90016fe6548001feb
  | 2 => 0x210e7fca690873fd5348439fe29a421cffd0d210e7fc8690873fd4348439fe21a4202bfd89210f7fea490827fe5248401fea924209ff149210effe8490827fe4248401f72124200ff50921007da8490827fc4248439ff9924209ff8c9210e7dc6490873fd3248439f69924209ff0c921015fec29080bff5148405bfa8a4202ff94521017faa29080b7d5148405fe28a4202ffd0521017fc829080bfd4148405fe20a4202ffcc521017fc629080bf63148405fe98a421cfd4c521017f8629080bff2148413fb90a4202ff88521017dc429080bfc2148405f610a4202fd08521007fec090802ff6048437ff3024201bf98121007fac09086ffc60484037e302421effd41210dffca09086ffc504843bffa02421bff901210dff88090873ff3048439ef982421bff8c1210e7fa609086ffc3048437ff1024209ff08121017fe209080bf71048405ff0824202ff0412100dfecaa8003ff64540017fb22a01aff99150025fcc8a8003fd6454035fe322a004bf1915002ffea8a80177f545400bff2a2a005ff55150006faa8a8017fc5454033ffb1aa019bfd8d500cffcc6a800efe6354033feb1aa019bf58d500cff8c6a800efc635400bffa9aa005ff94d5002ffaa6a8017fc5354033ffa1aa019ff90d500cffa86a8067fc4354001ffb12a000bfd8950007fcc4a8003fd6254001fe312a009bf1895002ffea4a80177f525400bff292a005ff54950006faa4a8017fc5254035ffa12a000ff90950007fa84a806bfc4254033ff992a019ff8c9500cffa64a8067fc3254001ffb0aa000bfd85500c7fcc2a800afe6154001feb0aa018ff18550015f8c2a8017ff515400bbfa8aa005ff9455002ffaa2a80037d515400bfe28aa01affd05500c7fc82a8003fd4154031fe20aa019ffcc5500c7fc62a8067fd3154031fe18aa000ffc85500c7fc42a8003fd2154031fe10aa001bfd815000ffea0a8017fb5054003ff282a001df9415000ff8a0a80077c5054003fc282a001ffd015000ffc80a8007fc4054003ff982a001f7cc15000ffc60a8007fd3054003fe182a001ff8815000ff840a8007ff1054003ff082a001ff04150007fecaa0002ff6550001bfb2a80009fd95400bffccaa0016fe6550001feb2a8000bf595400bff8caa0016fc6550001be32a80059f1954000dfec8a0013ff5450009ff2a28004ef95140027faa8a0003bd5450009fe2a28016ffd8d400b5fec6a005bfe63500077f31a8016ff58d400b5fac6a005bfc63500077e31a8016ffd4d400b7fca6a005bfd535002dfe29a8004ffd0d40027fc86a0013fd4350009fe21a8000ffd8940005fec4a0003fe6250001feb128000ff1894004df8c4a005fff5250001ff2928000ff549400bff8a4a0013ff4250009dfa128004ff90940027fa84a0003bd4250009fe2128016ffcc9400b7fc64a005
  | 3 => 0xf32a8200ff59541005facaa0897fc655040b7e32a8202bfd9141027fea8a0813fe5450409feaa28204ff15141127fec6a0892ff6350449ff31a8203bf98d41127fac6a0892fd6350449fe31a8203bf18d41127fea6a0893fe5350449fea9a8224ff14d41027fe86a0813bf4350409ff21a8204ff50d411277a86a0813fc4350401ffb128200bfd8941007fcc4a0803fd6250401fe3128209bf1894112ffea4a0803fe5250401fea928225ff14941027fe84a0813bf4250409ff2128204ff509410077a84a0813fc4250449ff9928224ff8c941127fa64a0893fc32504057fb0a8202ffd4541016fea2a080bfe5150405fea8a8202df54541017f8a2a080bff4150409fba0a8202ff905410177c82a080bfc4150405de20a8202fd10541017fe62a080bfe3150405fe98a8202ff0c541017fc42a080bfc2150401ffb028200bfd814111ffcc0a0806fe6050401feb028223ff1814100df8c0a0897ff5050447ff2828223ff14141027fe80a0813bf4050409ff2028204ff10141127fe60a0893df3050447ff1828224ff4c14111ff860a088ffe2050447fe1028202ffc4141017ee20a080bfe1050405fe0828209ffd972104dfecb90827fe65c840b7f32e4209ff59721005facb90827fc65c84137e32e4209ffd932104dfec990827fe64c84097f3264209ff59321005fac990827fc64c84137e3264222ffd532110ffca990803fd54c8443fe2a64209ffd8f2104dfec790827fe63c84077f31e4209ff58f21105fac790827fc63c84137e31e4220ffd4f21107fca790883fd53c8441fe29e4220ffd0f21107fc8790883fd43c8441fe21e4202bf98b2104ffea590827fe52c8413fea964209ff14b2104ffe8590827fe42c8413f72164209ff50b21007da8590827fc42c8413ff9964209ff8cb2104fdc6590827fd32c8441f69964209ff0cb21015fac39080bff51c8405bfa8e4202ff94721017faa39080b7d51c8405fe28e4202ffd0721017fc839080bfd41c8405fe20e4202ffcc721017fc639080bfd31c8405fe18e4202ff88721017dc439080bf621c8405fe10e4202fb0872104ffec190827fe60c84037f3064209ff58321005fac190827fc60c84037e3064222ffd43210fffca19087ffc50c8443ffa06421fff903210fff88190883ff30c8441ef986421fff8c321107fa619087ffc30c8413ff1064209ff08321017fe219080bfe10c8405fe0864200ffd9521005feca9087bfe654840b7f32a4200ff59521005faca9087bfc654840b7e32a4200ffd9121005fec890877fe64484097f3224200ff59121005fac890877fc64484097e322421effd51210effca890803fd544843bfe2a2421cffd8d210e5fec690803df63484016fb1a421cff98d2101dfcc690873fd63484397eb1a421cff18d2101df8c690873dc63484076e31a421cffd4d
  | 4 => 0x13fc405085dff982842ef7cc142167fc60a10bbfd3050859fe182842cff8814204ff840a10b7ff1050859ff082842cff0414202efec9a88177e64d440bbeb26a205df1935102efec7a88177e63d440bbeb1ea205df18f51156fe87a88ab7e43d4455bea1ea22adf10f5102efec5a88177e62d440bbeb16a205df18b5115efe85a88037e42d4401bea16a22bdf10b51156fe65a88ab7e32d4455be996a22adf0cb51014fac3a880b7f41d4405bf20ea202df10751016fe63a880b7e31d4405be98ea202df0c751016fc43a880b7c21d440bbfb06a205df9835102efac1a88177c60d4457bfa06a229df9035114ef881a88ab7f30d4455af986a229df8c351156fa61a88a77c30d4453bf106a229df08351016fe21a880b7e10d4405be086a202bfd9551007fec8a8802ff6454451ff322a204bf99151007fac8a88a3fc64544097e322a205ffd515102efea8a8817fe5454451bf2a2a205ff55151006faa8a8817fc545440bbe2a2a227ffd8d5113dfec6a889ffe63544077f31aa227ff58d5113dfac6a889ffc63544077e31aa205ffd4d5102efea6a8817fe535444fbf29aa205ff54d5113efaa6a8817fc535440bbe29aa227ffd0d5113ffc86a889ffd435444ffe21aa200ffd8951005fec4a8803fe6254401feb12a200ff1895104df8c4a8817ff525440bbfa92a205ff94951006fca4a8817fd5254401bea92a205ff1495102ef8a4a88a3ff4254401ff212a200ff50951147f884a889fff325444fff192a227ff4c95113ff864a880aff6154405ffa8aa205fdd4551017fca2a880b7e5154405fe28aa202df14551017e8a2a880bff4154405ff20aa202ff10551017fe62a880bfe3154405fe98aa202ff0c551017fc42a880bfc2154401ffb02a200bfd8151137fcc0a8806fe6054401feb02a226ff1815100df8c0a8817ff505440bbfa82a205ff94151136fca0a8817fc505440bbe282a228ffd0151137fc80a889bfc405444fff982a227f7cc151137fc60a889ffd305444dfe182a226ff88151137f840a880bff1054405fb882a202ff84151017f820a88037f6454451bf322a200df59151146f8c8a889f7f635444fbf31aa227df58d5113ef8c6a889f7f435444fbf21aa227df50d5113ef886a88037f6254401bf312a200df58951006f8c4a88a37f4254401bf212a200df50951146f884a889f7f325444fbf192a227df4c95113ef864a880b7f61544053fb0aa205ddd8551016fe82a880b7e4154405be20aa202dfcc551016fc62a880b7d3154405be18aa202df88551016f842a88037f605444dbf302a200df58151136f8c0a88a37f405444dbf202a226df1015113efe60a889f5f305444dbf182a227df4c151136f860a889b7e205444dbe102a202dfc4151016ee20a880b7e1054405be082a200ffd9541005fecaa0897fe655040b7
  | 5 => 0x49521bffe84a9027fc425486dff992a409ff8c9521b7fa64a9027fc3254801ffb0aa400bfd85521affcc2a900afe6154801feb0aa435ff18552015f8c2a9017ff515480bbfa8aa405ff9455202ff8a2a90dfff415486bff20aa435ff105521b7fe62a90d7fe315486dfe98aa435ff0c5521affc42a9027fc2154801ffb02a400bfd81521a7fcc0a9006fe6054801feb02a434ff1815200df8c0a9017ff505480bbfa82a405ff9415202ff8a0a90dfff4054869ff202a434ff101521b7fe60a90dbdf3054869ff182a436ff4c1521a7f860a90d3fe2054813fe102a435ffc41521a7fc20a90d3fc1054813ffb2c8409bfd964204ffccb21016fe6590813bf32c84059f9964204ffacb21002fd6590813beb2c84009f5964204ff8cb21026fc65908097eb248404ffd5242027fca921013fd5490809fe2a48409ffd8e4204dfec721027fe63908077f31c8409ff58e42195fac721027fc63908137e31c8432ffd4e42197fca7210cbfd5390865fe29c8404ffd0e42027fc8721013fd4390809fe21c8409bf98a4204ffea521027fe5290813fea948409ff14a4204ffe8521027bf4290809f7a148409ff10a4204fd88521027ff3290813ff1948409ff4ca4204ff86521027ff6190813ff30c8402bf9864204ffac321002fd6190813fe30c8402bf1864219ffea3210c7fe5190863fe28c8404ffd0642027fc8321013fc4190865ff98c8431ff8c642197fa63210c7fc3190813ff10c8409ff0864204ffec121027fe60908037f3048409ff58242005fac121027fc60908037e3048433ffd4242187fca1210c3fc5090809ffa048404ff90242027f881210cbff3090865ef9848430ff8c242197fa61210c3fc3090813ff1048409ff0824218ffe21210c3fe1090861fe0848400ffd9542005fecaa10bffe655080b7f32a8400ff59542005facaa10bffc655080b7e32a8409bfd9142027fea8a10bfbf5450809ff2a28404ff55142027f8a8a1013bc545085dffb1a842ebfd8d42177fcc6a100efe635085dfeb1a842ebf58d42177f8c6a100efc635085dffa9a842eff94d42177faa6a10bbfc5350809ffa1a8404efd0d42027fc86a1013fd435085ddea1a8404ff10d42025fec4a10bfff5250813ff2928400ff5494204ff8a4a1013ff4250809f7a128409ff9094204f7c84a1027fc4250813de2128404fb10942177fe64a1027fe325085dfe9928409ff0c942007fec2a1002ff615085bff30a8402bf98542007fac2a10b7fc61508057e30a842fffd454216ffca2a10b7fc5150809ffa0a8404efd0542027fc82a1013fc415085dff98a842dff8c542177fa62a10b7fc315085bff10a8409ff08542007fec0a1002ff6050859ff3028401bf98142007fac0a10b3fc60508037e302842fffd4142167fca0a10b3fc5050809ffa028404efd0142027fc80a1
  | 6 => 0x4020000500080c002025fecaaa012ff6455009ffaa2a805efd5154027fca8aa0137e5455009fe2a2a804df1515402778a8aa0fbff635507d7fb1aa83eff98d5401dfcc6aa0fbfd635507d7eb1aa83eff18d5401df8c6aa017ff535500bbfa9aa805ff94d5402ffaa6aa0fb7d535500bfe29aa804ffd0d540277e86aa013fe4355009fea1aa83eef50d54027f886aa003ff62550017fb12a800ff98954007fac4aa003fc62550137e312a805ffd495402ff8a4aa0177c5255009ffa12a804ff109541f7fe64aa0fbfe325507dfe992a83eff0c954007fec2aa002ff615507bff30aa802bf98554007fac2aa0f7fc61550057e30aa805ffd455402efea2aa017fe515500bfe28aa804ffd0554027fc82aa013fc415507dff98aa83dff8c5541f7fa62aa0f7fc315507bff10aa83dff08554007fec0aa002ff6055079ff302a801bf98154007fac0aa0f3fc60550037e302a805ffd415402efea0aa017fe505500bfe282a804ffd01540277e80aa013fe4055009fe202a83effcc1541f7be60aa0f3fe305507dfe982a83cff0c1541e7fc40aa0f3fc205507bff882a83cff841541e7f820aa016fd6594813ffb24a409ff99252025fcc929027be64948095f324a409ff59252005fac929027bd64948015eb24a409ff1925204df8c929017ff549480bbfaa4a405ff9525202ffaa9290037d549480bfe2a4a409ffd8e5204dfec729027fe63948077f31ca409ff58e521d5fac729027fc63948137e31ca405ffd4e5202ffca729017fd539480bfe29ca43affd0e521d7fc87290ebfd4394875fe21ca409bf98a5204ffea5290277f529480bf7a94a409ff14a5204fd8a529027ff4294813fe214a409ffcca5204ffc6529027fd3294813fe194a409ffd865204ffcc32900afe6194813feb0ca400bf5865204ff8c32900afc619480bffa8ca405dfd465202ffca329017fc5194877ffa0ca439ff906521cff883290ebff3194873ff18ca43aff4c6521cff86329027fe2194813fe10ca409ffd825204ffcc129006fe6094813feb04a400bf5825204ff8c129006fc609480bffa84a405ff942521c6fca129017fc509480bbe284a43bffd02521c7fc81290e3fc4094875ff984a43af7cc2521c7fc61290ebfd3094871fe184a409ff8825204ff841290e7ff1094871ff084a438ff0425204dfecaa9003ff64548017fb22a437ff99152025fcc8a9003fd645486ffe322a404bf1915202ffea8a9017fe545486fbf2a2a405ff5515202ff8a8a90177c545486dffb1aa436bfd8d521b7fcc6a900efe635486dfeb1aa436bf58d521b7f8c6a900efc635480bffa9aa405dfd4d5202ffca6a9017fd535486dbea9aa405ff14d521b7fe86a90dbfe435486dfea1aa436ff10d5202dfec4a9017ff525480bf7a92a409ff9495204efca4a9027fc5254813be292a405fb1
  | 7 => 0xfa0001b4a8caa60000000000006300005461c80ca38866a0000008f6a2073e56a8daa2c3489bc46cb008204ee016660acc5548521821645d6bea0000007d4132bbc5ac7440000001a898c758bc243e00078e000a0a9ee20ca7638439a96800095414c02821a000af02a25da6ce00081a9ce454a1800037c7d839c0006c20001266d62000000009b06fc66e0000000000000000000009700008a20008568f85f40001d489200035e50c6ec2ee0000005b00007e091056e70400000031abd604e3386660000ec88e000000000bb281ebd000021c9e645600000050a000b12252926000a5038684e7686f04c40008485560001dc0005a8000000000000064b3e00020a47a00000037e0004a8b108c027295c5a000071a50004663800077000053869c912a6a4f29fc16e3ca8b657693a00000094c00082e2b433a1300009d4b3a00000002800c0081700400c00803012084028000040480400200e0180380b0080200080a0000300080700200c0000100a018020000080040080000200802028000008018000040000000400000c0000a00e028040090400000880000e010020040140080f81000005c0280f00201404800010008040040000200080402c0180300201003c058030080540080300e0000100000e0100080000000c00001002004018040000240080000000c0080b01e004048000020000380a010000080030020200200400001800806026028070060000500400401000400801024000000090140000280e0000480c0020040100000302c030008030000080080000605002805000008078100160040e8100000180280805a0200102800a014078040000040000001200c02803008018168000000000003701a00c01000010004000030040140980b002008050080000300581200005c0180600a02000834000014060000180080280000200c0080102c0100100300404c0080000400000809004014000090200000300101c00402818000010020080300000580200c018010050000000080001c00c088000020140780000002803800006028000010000281000100002c00801006000000070060140080100201803800024004000010280000001100a0080080a00000c1500300200c0080000406c008140000180180500c0040100700a004038090000540301b000000010000040100080d01a00c000020020000980400000402800024008050060020080600200000400821004004000000020440300700002c0c80b0080f8008000080200300600a004018030000080100600a0000f0030000280280b002000008080060280180a0120140000700000002806000040008000020340380b00400c190010200000600a00000000800002018038000000100400900402c0202600c018010130040180d00a0020080c8060040280180200002
  | 8 => 0x7c82b891a9da096676b708dc2e2ada172b1aab04ec7c011653ebcc00036600029a706030be2466000a120003584c873a3724fab5c99c000bac1d20420e23166a43ea4dc4286f4a3c000a1400013823a000b88bf82580c80004062903ba0002084920006500009c60a42a672835a9909c8716a8a2ba106af85e444c1fcb62bce93e53c58c0267725ce8ec7c203c4fc18a678000b50a6e59676078c6d20d24468a85268de7d6930000aaa8d0000000a6043000036865885a4ae3a61ba4ea4785b63aa9d69d02b015e74c0000000000000008823a800054eafa000b2600000000000070200077e3bc7b01cc928b607de35cb38000794abc00047e9a2000000a3215c93c000aeeb4aa7a000b78a283f26940006e6b4886855a9dc4480004b6192c02be68a628a3e2b687e8a4e0000b08aa5500001760128fa8d215676e5622783765d488c6080046922444587802f2000000bda13c0f21b2206000000000a7c4825d200032a8662b6b4ca261021982684001543bea3633435467a63a324b98ac429640a23e13e05a24e68c03200000052a25096000000049800043407067e5046f29622248602dc000988a2e0006d89aa5c846a04cbe85401b683074e0005780002c4b84b2a226402b745ba4ca8c67403eeb0c18421800000018600000068060a2d20000000002c032c75e1d86ae1f229299a3d20005bc00000033000014038e1aa70eb1c000072356a000005940000a200065a1000006202405c67da0006c400000000051e6c60000220000000560003b22380000001fe0000006826620000000c20002d40005f6000a8674a72c7fc0000005f80008760009168e0b1e8e6aae7880000000008ca97e00015a9462c20005bea340000000002fa00070046000000011819a000000000b667223e000000036c3d61e20c46e03ae8120006d0a5e000a1aa708c25a655223c55c22000002c0da000a62000bd26900005d03467b21ca9c47e665641c4aa64c6da16ca72564864bae00027c2fc0000009828ba0002a4a4000000018876cbd800042aa067a06ac0a681641089460ca1c4b2ab800009881449a1e67081b80000781121f69b83a400091e13a1143700d697a5a480619690a000c0c000000364000a64254000ac034a1de2627140e40442f088a63642cc10bb04c2a90468be43b600064a9ca90064eb723407ea00a4de8188c894ebb828267c1f00003ec85c73077460600041a8405888429ac190ba448c000286908000c0e30600058a48a0000005b80005368fc00000060008cae624c0000d41b043a00000000000000000000000000000000030a90c9b2a0e25e0007927ec05c7b8ae000015227e160314aca9fe2ec85e3820008d698012eaa25922f4a48b94000c1226c48e0008fe9ea89a00051c4bcb7a7d23f47120008248b05069420003089ba9ae61e00
  | 9 => 0xe60000000008280000000002aebf27329ec0002feb96a0452c00009abf64e8adcafc4084901ec53280e00000000000000024881c6ca0ba9c20003de4c6b200006321360003c4034000a0c9e29a04d8000000b2c3a2940aec32847014457200003682a060bf009090496e12a880472bf420eb047ba42e0006f60000000004ce000bbe4d23c80001a0ad44268105fc2a89e4000000000b520000f48f02c82aaa30672ae42d668647c99248670a70c5601347264a65b417c3746040de00014692a0000009380005c200014e21e19c542b320001040000000000009b66180000003cc000a6662c00051ab7e4d0234ab461cbb40740009d2000488bc4440aa068876227a59c0002849240009a66ba8989d80002327760002644e6480a46b567a477805087c00067400064006c4960005c400000038c14a5ee5e81bea1e0008a06dc83600000019e000288a680f8522516742858a1657e0c65b210eaea1ae00001822c30260e6220000000001a40140001222123ac1d095252400071c2800006e2b220000a8000a3ab142600549943f826e6de49e3964f83f6b7c1da8c4420648b24b8eb804942a0ba84ac1804c07dc83e6a895a09418e0006102146145340000001580001700000006b00000b8000af60001c000004a5185860007ee79a318000000000afe0007208b2872000a22aba6c0ad2ade0b425aa5c25c510000000000000000b8c000000bfc00097c3200002be68eb92006000b1800026a2d80002165f200c000000750000a5a7188629029720008e200059e8ac5cc6c87f09481f4b06a920ae1c4a94000ad8000c0017479e844000b5a00000041429c8f24b4ad60d0544b9ebecb544da3040000005148ce344000390602a545fa0885666f86a60004a20000529b4000a3e000a02230476000796a96b340007fa8009f0000000ac28880002700001eea8000072a0007862e800096409e9f8616ab24fe0840005e662a0007ca000bee33e46e61a000310ba20004188464d4a8259800000000076459a8f4ace71e0a00f69209863b4528aa80000000002e48bc10a9f4b58a8e24292c38a0f053a09c06eb9a73cb4ea7e3327b463cae26e874600040e00000001a0bc4b08ee03eb5e4be1eab361e8000c163d821075257a0007cc000000000748b282d000008696a35279c8e80004388320000003b0000b6a50200044e2b20009a8abead07ac6443e40800000000000020007e27820000007c46fe8960008d412c83a1bc0000002e614892e000000612582be03dc8040000000009a40009cc2e0a58c147c67e40001ac976000000000000000000058000a9800037a7ae450ba073800000041600066800094499e02a000a520000820e00007841245aa76a4a00e898a3fa850008790950000236204918000bde4643b844a00037800001c568b86bca39418c000
  | 10 => 0x54a00089eab6b0a8ae2bc6b60663c665e08a038bb62983d068aa4a17802e3e808e2741681945fe322af40000006a2b6e4f466cc0430c3807a67981e4a42000000978b76b429c03ce2ea3f095817a31205e5e2404a882ac1f84f68b48546b899872445a5ae0240dc7ce52e6286b454869ea9a142b8a86e53077a11cbdcbfa0008783d40fc4e056c966256b9069622a2c633c0000002463005ea5de22e000b3000000000000062eb2ea74000a4436a43616a684b0287a996000bfe4123a077c710b9c0d85ec78a39216263e7d0a084d6a3807e1286540000008900000005c000000000000031ea9c83400033645e0000000000006a0b4450800000057c0003fc59047457007c1a23980002de24a7a2000000b0e00036e11ea4c54c69840c5580000ee0000007365e010c1509740100007548e46cc86a0006d4a10a2428e076a9e1665d800000000000094a34e000000b4606200000e0000004520000ea7340923feb827bc90e7be0fe6ea69a86c9f20beb404a492229e0b6520020ba65dc8746464625748be4ba82c2da93412083c06828c7fe8d82ca80841e9fa6bc72e84aa784b81107a863430e4326fa5842f64f0a560b20000004cc00089c9320008b81d60aa6eebd48cc000000000ac60cc80ab3c0000000002cc1a655e0401ce00000017e0000ac886000af2350ac86649f61e011a7b61084e400032e45c88400075c3c006a36091c84c4440ce9be98e766670342a8465cbc87aa01e000000aa45a29562760006e4b64c069366be96c9de87080c7f2a6c8a46522ce9847f6bc687e49c6246421c275a442000c08000aac0006262022285f050e2669e8baabba00058e8380006aa00036282639e4e258000090600007a000326b16b082946b280234c7560c08ea03abc043c3da31c2223c29149e0b6c7f44243e67f8422000000ae8a2a5ca95e0008221fac0a0004841c60480002f80000005120
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x77248510017e77248510007e7624851004ef6624851004ef46248510007e46248510007e64248510007e54248510227e63248510227e53248510007f3704851000df6704851000df470485100dff07048510016f76048510017f360485100dff240485100dfd730485100dff230485100dfd53048510227f130485100dfe720485100dff220485100dfe52048510015f87650110026f87650110014f876501100077b755011000778755011000dfb745011000fbb7450110007bb6450110026fa6450110026f8645011003fb8645011003fba5450110007b9545011021dfb735011021df97350110005fb725011003fbb4250110007b94250110007f37150110015fa7150110015f871501100aff0715011000efb615011000ff361501100af7b51501100aff251501100af795150110007f151501100077151501100afbb41501100aff241501100afb9415011003ff14150110007b141501100aff22150110007f12150110037db764c11001edb764c110097d8764c11001ed8764c110007db754c110217da754c110007d9754c110217d8754c110007db654c110217da654c110007d9654c110217d8654c110007db744c11020fda744c110007d9744c11020fd8744c110007db644c11020fda644c110007d9644c11020fd8644c110217db544c11020fda544c110007d9544c11020fd8544c110007db724c110007da724c110007d9724c110007d8724c110007db624c110006db624c110007da624c110007d9624c110006d9624c110007d8624c110217db524c110007da524c110007d9524c110217d8524c11020fdb424c110007da424c110007d9424c11020fd8424c110097db714c110007d3714c110097da714c110097d9714c110097d8714c110097d0714c11000fdb614c11000edb614c11000fd3614c110097db514c1100975b514c110097da514c110097d2514c110097d9514c11009759514c110007d1514c11000751514c110097d8514c110097db414c110097da414c110097d2414c110097d9414c110007d1414c110097d8414c110097db214c110097da214c110097d2214c110097d9214c110007d1214c110097d8214c110015f8764811004ef87648110014f876481100077b7548110007787548110005fb7448110005f97448110205fb7348110205f973481101fefb63481101fef9634811000dfb724811000feb7248110007eb624811004efa624811004ef86248110007e86248110007ea5248110007e95248110007ea4248110007e94248110007f37148110015fa7148110015f8714811005ff0714811000efb614811000ff3614811005f7b514811005ff2514811005f795148110007f1514811000771514811005ff24148110007f1414811005feb214811005ff2214811005fe92148110007f12148110007e12148110
  | 1 => 0x910004fe7690910004fd769091004cfc76909100457e75909100057d7590910006bf6490910026bc649091004eee6290910006ed6290910015f67190910005f5719091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc7650910026be6450910006bd645091004eee6250910006ed6250910015f6715091000dfa705091000df4765451002ef4765451000cf47654510015f7755451001777755451000777655451002ef6655451002ef46554510047746554510005f7745451004777545451023f765454510007755454510047745454510047775354510237765354510237755354510047745354510005f77254510047775254510007765254510007755254510047745254510007f3705451000df6705451000df47054510137f07054510016f76054510017f36054510137775054510137765054510137755054510137745054510137f24054510137d73054510137f23054510137d53054510237f13054510137f2205451004777765451002e77765451013774765451002e74765451000777745451023f76745451000775745451023f74745451000777645451023f76645451000775645451023f74645451024777735451023776735451024775735451023774735451023777635451023776635451023775635451023774635451023777435451023776435451023775435451023774435451000777725451000776725451000775725451000774725451000777625451000776625451000775625451000774625451023f77425451000776425451000775425451023f74425451023777325451023776325451023775325451023774325451013777705451000773705451013776705451013775705451013774705451013770705451001777605451001677605451001773605451013777405451013776405451013772405451013775405451013774405451013777305451013757305451013776305451013772305451013775305451013755305451023771305451013774305451013777205451013776205451013772205451013775205451013774205451000df47650510026f4765051000cf47650510005f77550510005f57550510015f77450510017b77450510007b76450510026f66450510026f4645051003fb4645051003fb7435051022fb54350510005f7725051003fb74250510007b54250510007f3705051000df6705051000df4705051011ff07050510016f76050510017f3605051011fb7405051011ff2405051011fb5405051011fd7305051011ff2305051011fd5305051022ff1305051011ff2205051000df4764851004ef4764851000cf47648510005f77548510005f57548510005f77448510005f57448510007d77348510227d47348510226f76348510226f56348510015f
  | 2 => 0x4fd75d911002cfc75d911011cfd74d9110006bf54d911003ebc54d9110004ff73d911001cfe73d9110004fd73d911001cfc73d911003ebf43d9110006bd43d911004cfe72d9110004fd72d911003ebc42d911000cff71d9110014fe71d911000cfd71d9110014fc71d91102767f51d91102767d51d9110276bf41d9110276bd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110266bf40d9110266bd40d9110266df30d9110266dd30d9110024ff76591100057f75591100457c755911003ebc645911025df7715911026dfb7059110004ff75591100067f75591100047f755911002cfe755911002cfc75591100067c755911002c7c7559110264ff7459110006bf7459110004ff735911001cfe7359110004fd735911001cfc7359110004ff725911004cfc725911003ebf425911025cff7159110006f771591100ae7f51591100ae7d515911011cff7059110006fb705911011edf305911011edd3059110004ff7655110004fe7655110004fd7655110004fc765511002e7e65551100067d6555110015f6715511004cfe76d891002cfe75d8910004fd75d891002cfc75d8910024fe74d8910004fd74d8910024fc74d8910004ff73d891001cfe73d8910004fd73d891001cfc73d891000cff71d8910014fe71d891000cfd71d8910014fc71d89102567f51d89102567d51d8910256ef21d8910256ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d891024edf30d891024efa30d891024edd30d8910006f930d891024eef20d891024eed20d89100dcfd7698910006ef62989100ddf5719891005df9709891004cff76589100057f75589100457c7558910005bf745891003dbc7458910005df7358910035dc73589100fdf77158910075fb7058910004ff75589100067f75589100047f755891002cfe755891002cfc75589100067c755891002c7c7558910004ff7458910006bf7458910004bf7458910024fe7458910024fc7458910006bc7458910024bc7458910004ff7358910006df7358910004df735891001cfe7358910004fd735891001cfc7358910006dc735891001cdc7358910006ef72589100fcff7158910006f7715891005e7f515891005e7d51589100dcff7058910006fb70589100dedf30589100defa30589100dedd3058910006f9305891024cfe76189100457e75189100057d751891003dbe7418910005bd7418910035de7318910005dd731891004eee6218910006ed621891004cff7694910004fe7694910004fd769491004cfc76949100067f659491002e7c659491003dbe7494910005bd7494910015f67194910005f5719491000dfa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc765491002e7e65549100067d6554910015f6715491004cff769
  | 3 => 0xf65485200076c6548520005ef7448520005ed7448520006ef6448520006ed6448520007cf73485202b7cc73485202b6ef63485202b6ed634852004def714852004fe77148520007e76148520016ee6148520016ec614852005fe4614852005f6f514852005f6d514852005fe631485202b7e53148520007eb704852000dee704852000dec70485200dfe8704852004eef604852004feb60485200dfcf30485200dfea30485200dfcd30485202b7e930485200dfe710485200dfea1048520057db764c12001edb764c120057d8764c12001ed8764c120007db754c1202afda754c120007d9754c1202afd8754c120007db654c1200075b654c1202afda654c120007d9654c1202afd8654c12000758654c120007db744c1202a7da744c120007d9744c1202a7d8744c120007db644c1202a7da644c120007d9644c1202a7d8644c1202afdb544c1202a7da544c120007d9544c1202a7d8544c120007db724c120007cb724c120297da724c120057d9724c120297d8724c120007c8724c12000fdb624c12000edb624c12000fcb624c1202afdb524c120297da524c120007ca524c120007d9524c120007c9524c120297d8524c1202a7db424c120297da424c120007ca424c120007d9424c120007c9424c120297d8424c120007db714c12029fda714c120007d9714c12029fd8714c120007db614c120006db614c12029fda614c120007d9614c12029fd8614c1202afdb514c1200075b514c12029fda514c120007d9514c12000759514c12029fd8514c1202a7db414c12029fda414c120007d9414c12029fd8414c120297db214c120007cb214c12029fda214c120007d9214c120007c9214c120297d8214c12002cfe76d95100467e65d9510134fd75d9510024fe74d9510004fd74d9510024fc74d95100067e54d95100467c54d9510004ff73d951001cfe73d9510004fd73d951001cfc73d95100467f53d95100067d53d951004cfe72d9510004fd72d95100467c52d951000cff71d9510014fe71d951000cfd71d9510014fc71d951028e7f51d951028e7d51d9510014ff70d951000cfe70d9510014fd70d951000cfc70d951027e7f50d951027e7d50d951027edf30d951027edd30d951002cff76595100467c6559510005bf745951003dbc745951014df77159510285fb705951027cff75595100067f7559510004ff7459510006bf7459510004bf7459510024fe7459510024fc7459510006bc7459510024bc74595100467f5459510004ff735951001cfe7359510004fd735951001cfc7359510004ff725951004cfc72595100467f525951014cff7159510006f771595100c67f51595101367d5159510134ff7059510006fb70595101367e50595101367c5059510136df3059510136dd3059510024fe76d911003ebe64d911002cfe75d9110
  | 4 => 0x85200067f65d85200067c65d852005ef661d85200067f75d852002cfe75d8520004fd75d852002cfc75d85200067c75d8520024fe74d8520004fd74d8520024fc74d8520004ff73d852001cfe73d8520004fd73d852001cfc73d852000cfd72d8520014fc72d8520006ee42d8520006ed42d852005ef621d852000cfe70d852004cfd70d852000cfc70d85200fedf30d85200fefa30d85200fedd30d8520006f930d85200fef710d85200057f755852006d7c75585200067f65585200067c6558520005bf7458520065bc7458520005df7358520055dc735852005ef4615852002e7f76d45200057e76d452006e7e76d45200047e76d452006e7d76d452006d7c76d452002e7c76d452002c7c76d45200067f64d452015e7e64d45200067d64d452015e7c64d45202e67f63d45201567e63d45202e67d63d45201567c63d452006f6e72d452006f6d72d452014e7f62d45200076e42d45200076d42d45201357d71d452005e7f61d45200167e61d45200167c61d452014e7f60d452014f5f30d452014f7a30d452014f5d30d45202e77930d45202df7b20d452014f6e20d452014f6c20d452014f7820d452014f7a10d4520004ff7654520004fe7654520004fc76545200067f655452002e7e65545200067d655452002e7c65545200076e52545200076d52545200067f76545200057e76545200067e76545200047e76545200067d76545200057c76545200067c76545200047c76545200067f64545201467e64545200067d64545201467c64545202d67f635452013e7e63545202d67d635452013e7c63545200076e72545200076d72545201367f62545200076e42545200076d425452014d7f715452006f77715452005e7f61545200167e61545200167c61545201367f60545201375f30545201377a30545201375d30545202d77930545202cf7b20545201376e20545201376c20545201377820545201377710545201377a1054520004ff7650520004fe7650520004fc76505200067f655052012e7c6550520026be6450520006bd6450520007ad42505202c5ee76c852004eee76c852004def75c8520005ed75c85200076f65c85200076c65c852004def74c8520005ed74c8520006ef64c8520006ed64c85202beef63c85202beed63c85200dded71c8520016ee61c8520016ec61c852005f6f51c852005f6d51c852004feb70c852000dee70c852000dec70c852004fe870c852004eef60c852004feb60c85200ffcf30c85200ffea30c85200ffcd30c85202bfe930c85200ffea10c852000cfc76485200067f65485200f67c6548520005df7348520055dc7348520006f76148520016f4614852004fe42148520005fb704852000df8704852004fe8204852000dec7648520016ec764852000cec7648520005ef7548520005ed75485200076
  | 5 => 0x186bd40d9120186df30d9120186dd30d9120186fa10d91200057f755912006d7c75591200067f65591200067c6559120066bc645912032def7259120004ff75591200067f75591200047f755912002cfe755912002cfc75591200067c755912002c7c7559120184ff7459120006bf7459120004ff735912001cfe7359120004fd735912001cfc735912032cff7259120006ef7259120004ff7159120014fe7159120014fc7159120066bf4159120164ff7059120006fb7059120166df3059120166dd3059120166fa1059120004ff7655120004fe7655120004fd7655120004fc76551200067f655512002e7c6555120325ee769492004eee76949201a5ed75949201c76f659492002eee659492002eec659492006f6c659492002e6c659492004fae7494920005ed749492004fad7494920005ad749492006f6f54949200076d5494920005ed719492006f6f519492000dee709492000dec709492004eef609492004feb60949201c76e50949201c76c50949201c7cf30949201c7ea30949201c7cd309492031fe930949201c7ea109492002cff765492000cfe76549201a4fd765492000cfc76549200067f655492002e7c655492004f6c5254920005fb705492000df8705492000dec765492002eec765492000cec765492004def755492004f6f75549200076f655492002eee655492002eec655492006f6c6554920005ef74549203176e545492006f6c545492006f6f535492030f6d5354920005ef715492006f6f5154920007eb705492000dee705492000dec70549201a7e8705492004eef605492004feb60549201a76f50549201a76d50549201a7cf30549201a7ea30549201a7cd305492030fe930549201a7ea1054920305ee769092004eee769092004def759092004f6e7590920005ed759092004f6d75909200056d75909200076f65909200076c6590920165ed7490920026ee6490920026ec6490920005ed719092000dee709092000dec709092004eef609092004feb6090920187cf3090920187ea3090920187cd30909202ffe93090920187ea1090920024ff765092000cfe7650920164fd765092000cfc76509200067f655092017e7c6550920006bf6450920026bc645092004fac4250920005fb705092000df8705092000dec7650920026ec765092000cec7650920005ef7550920005ed75509200076f65509200076c655092004def745092004faf7450920007af6450920026ee6450920026ec6450920067ac64509202f7af5450920067ac5450920067af43509202efad4350920005ef7150920067af4150920007eb705092000dee705092000dec7050920167e8705092004eef605092004feb6050920167af4050920167ad4050920167cf3050920167ea3050920167cd30509202efe93050920167ea1050920014fe76d
  | 6 => 0xc73d952006e7f53d95200067e53d95200067d53d952006e7c53d952004cfe72d952000cfd72d952004cfc72d952006e7f52d9520014fe71d9520004fd71d9520014fc71d952006e7f51d95200067e51d952006e7c51d952004cff70d952004cfd70d95201c67f50d95201c67d50d95201c6df30d95201c6dd30d95203257e76d952002c7e76d95200067e64d95200067c64d95200067f63d95200067e63d95200067d63d95200067c63d95201c76f72d95200057d71d95200067e61d95200067c61d95201c75f30d95201c77a30d95201c75d30d95200077930d95203477b20d95201c76e20d95201c76c20d95201c77820d95201c77a10d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95201c67f72d95203467e72d95201c67d72d95201c67c72d95200067f42d95203467e42d95203467c42d95200067f32d95203467e32d95200067d32d95203467c32d95200067f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200067e41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95203467f21d95200067e21d95203467c21d95201c67f70d95201c67e70d95201c67d70d95201c67c70d95201c67f40d95201c67e40d95201c67d40d95201c67c40d95201c67f30d95201c65f30d95201c67e30d95201c67d30d95201c65d30d95201c67c30d95201c67f20d95201c67e20d95201c67c20d95201c67f10d95201c67e10d95201c67d10d95201c67c10d952006e7c655952033def72595201c4ff75595200067f7559520004ff7459520024fe7459520024fc7459520004ff735952001cfe7359520004fd735952001cfc735952033cff7259520006ef7259520004ff7159520014fe7159520014fc715952006e7f51595201a4ff7059520006fb70595201a6df30595201a6dd30595201c57e761952006e7e76195201c47e76195200067e64195200067c64195200067f63195200067e63195200067d63195200067c63195203276d72195203267f62195200057d71195200067e61195200067c61195203267f60195203275f30195203277a30195203275d30195200077930195203377b20195203276e20195203276c20195203277820195203277a1019520024fe76d91200067f65d91200067c65d9120066be64d912002cfe75d9120004fd75d912002cfc75d9120004ff73d912001cfe73d9120004fd73d912001cfc73d9120066bf43d9120006bd43d912004cfe72d912000cfd72d912004cfc72d9120066bf42d9120014fe71d9120004fd71d9120014fc71d9120006be41d9120066bc41d912004cff70d912004cfd70d9120186bf40d9120
  | 7 => 0x4b2008f6f5354b203876d5354b20005ef7154b2008f6f5154b2000dee7054b2000dec7054b201a76f5054b201a76d5054b201a7cf3054b201a7cd3054b2004def7650b2037eef7650b20005ef7550b20005ed7550b2004faf7450b2004faf6450b20026ee6450b2004eec6450b2004fac6450b20377af5450b20087ac5450b20087af4350b2036fad4350b20005ef7150b20087af4150b2000dee7050b2000dec7050b20167af4050b20167ad4050b20167cf3050b20167cd3050b20004ff755872002cfe755872002cfc7558720004ff7458720024fe7458720024fc7458720004ff7358720006df7358720004df735872001cfe7358720004fd735872001cfc7358720006dc735872001cdc735872000cfe7258720014fd725872000cfc725872004eee4258720006ed425872004ef77158720076f63158720006f5315872004ef7215872004ef421587200dedf30587200dedd305872004efa205872004ef920587200def7105872002e7f76d47202de7e76d472008e7d76d472002e7c76d47202de7f64d472015e7e64d47200067d64d47202de7c64d47202de7f63d47201567e63d47203667d63d47202de7c63d47202df6e72d472008f6d72d472014e7e62d47202df6e42d47200076d42d47200767f61d47200167e61d47200767d61d47200167c61d47200776f21d472014f5f30d472014f5d30d472014f6e20d472014f7a20d472014f6c20d4720004ff7654720004fd765472004cfc76547202ce7f655472002e7e65547200067d655472002e7c655472004dee72547202cf6e52547200076d52547200067f76547202ce7e76547200067d76547202ce7c76547202ce7f64547201467e64547200067d64547202ce7c64547202ce7f635472013e7e635472035e7d63547202ce7c63547202cf6e72547200076d72547201367e62547202cf6e42547200076d425472008f7771547200767f61547200167e61547200767d61547200167c61547200776f21547201375f30547201375d30547201376e20547201377a20547201376c2054720137771054720004ff7650720004fd765072004cfc7650720026be6450720006bd645072004dee7250720007ad425072004def7648720356ef7648720005ef7548720005ed7548720005ef7448720005ed744872004eef6448720006ed6448720007cf734872034fcc734872004eef634872034eed634872004fe7714872004fe76148720016ee6148720016ec614872004fe461487200776f51487200776d5148720077e6314872034fe5314872000dee704872000dec70487200dfcf30487200dfcd30487200dfe7104872002cfe76d952006e7e65d9520024fe74d9520004fd74d9520024fc74d952006e7f54d95200067e54d952006e7c54d9520004ff73d952001cfe73d9520004fd73d952001cf
  | 8 => 0x9f9e64505300079d6450530005df7250530295dc725053009f9f42505300079d425053025ddf71505300975f51505300975d515053009fd741505300979e41505300979c4150530097d4415053011ddf705053000dde705053000ddc705053011edf6050530127db605053011f9f405053011f9d405053011fda205053011fd7105053011fda1050530295df76c8530005de76c8530005dd76c8530295dc76c8530295df75c85300a5de75c8530005dd75c8530295dc75c8530295df74c853009dde74c8530005dd74c8530295dc74c85302c5de72c8530297ce62c8530007cd62c8530297ce42c8530007cd42c85300dddd71c85300975f51c85300975d51c8530097ce21c8530097d621c8530097cc21c85300fddf70c853000dde70c85300ffda70c853000dda70c85300fddd70c8530297d970c8530005d970c853000ddc70c85300fedf60c8530107db60c85300ffcf20c85300ffda20c85300ffda10c8530005df7648530006df7648530004df7648530005de7648530005dd7648530005dc7648530006dc7648530004dc7648530005df75485300a5de7548530005dd75485300a5dc7548530005df744853009dde7448530005dd744853009ddc744853024ddf7248530007ce6248530007cd6248530007ce4248530007cd42485300fddf7148530097d66148530007d561485300975f51485300975d5148530297d72148530097ce2148530097cc2148530097d421485300dddf704853000dde70485300dfda704853000dda7048530007d9704853000ddc70485300dedf60485300e7db60485300dfda20485300dfd710485300dfda104853004e7f7559720004ff7459720024fe7459720024fc74597200067e545972008e7c5459720004ff735972001cfe7359720004fd735972001cfc735972008e7f53597200067d535972004cff725972000cfe725972004cfd725972000cfc725972004e7e525972004e7c5259720004ff7159720014fe7159720014fc715972008e7f51597201a67f50597201a67d50597201a6df30597201a6dd3059720004ff755932002cfe755932002cfc755932004ebf7459320006bf5459320086bc5459320004ff735932001cfe7359320004fd735932001cfc7359320086bf4359320006bd435932004cff725932000cfe725932004cfd725932000cfc725932004ebe425932004ebc4259320004ff7159320014fe7159320014fc7159320086bf415932004eef2159320166bf4059320166bd4059320166df3059320166dd3059320004ff765532004cfe7655320004fd765532004cfc765532039e7f655532002e7c655532004dee725532039f6e525532004def7654b20396ef7654b2004f6f7554b2004f6f6554b2002eee6554b2004eec6554b2004f6c6554b20005ef7454b2038f6e5454b2008f6c545
  | 9 => 0xd62585303c5df7158530007d76158530096de6158530096dc6158530097d46158530097d621585303b5df7058530007db70585303bddb70585303b6df6058530037db60585303b7da20585303b7da10585300a75f76d45300a75e76d45300a75d76d45300a75c76d45300a75f74d45300a75e74d45300a75d74d45300a75c74d45300075f64d45303af5e64d45300075d64d45303af5c64d45300a75f72d45300a75e72d45300a75d72d45300a75c72d45300075f62d45300075e62d45300075d62d45300075c62d45303af5f42d45300075e42d45300075d42d45303af5c42d45301355d71d45300975f61d45300975e61d45300975d61d45300975c61d45300975f41d45300975e41d45300975c41d45300975e21d45300975c21d453014f5f70d453014f5e70d453014f5d70d453014f5c70d453014f5f60d453014e5f60d45301575b60d453014f5f40d453014f5e40d453014f5d40d453014f5c40d453014f5e20d453014f5a20d453014f5c20d453014f5f10d453014f5e10d453014f5a10d453014f5d10d453014f5c10d4530005df7654530005de7654530005dd7654530005dc765453027ddf75545300075f65545300a75e65545300075d65545300a75c6554530005df745453009dde745453009ddc74545300a75f54545303a75e54545300075d54545300a75c5454530005df7254530295dc72545300a75f52545300075e52545300075d52545300a75c525453014ddf71545300a7d751545300975e51545300975c5154530097d45154530135df705453000dde705453000ddc7054530136df605453013fdb60545301375f50545301375e50545301375d50545301375c5054530137da2054530137d71054530137da10545300075f76545300075e76545300075d76545300075c76545300075f74545303a75e74545300075d74545303a75c74545300075f64545303a75e64545300075d64545303a75c64545300075f72545300075e72545300075d72545300075c72545300075f62545300075e62545300075d62545300075c62545303a75f42545300075e42545300075d42545303a75c42545300975f715453014d5f71545300a75771545300975f61545300975e61545300975d61545300975c61545300975f41545300975e41545300975c41545300975e21545300975c21545301375f70545301375e70545301375d70545301375c70545301375f60545301365f605453013f5b60545301375f40545301375e40545301375d40545301375c40545301375e20545301375a20545301375c20545301375f10545301375710545301375e10545301375a10545301375d10545301375c1054530005df7650530005de7650530005dd7650530005dc7650530005df75505300a5de7550530005dd75505300a5dc7550530265df7450530
  | 10 => 0x4930295dc76949301a5dd75949300075f65949300a75c659493009dde74949302979e749493009d9e7494930005dd74949302979d74949300059d7494930295dc74949300a75f54949300075d5494930325de72949302975f52949300a7cf5294930297cc5294930095de7194930005dd7194930095dc71949300a75f51949301c5df709493000dde70949301c7da709493000dda70949301c5dd7094930297d97094930005d9709493000ddc70949301c6df60949301d7db60949301c75e50949301c75c50949301c7cf20949301c7da20949301c7da1094930005df7654930005de7654930005dd7654930005dc76549301c5df75549300a75e65549300075d6554930005df745493009dde745493009ddc74549303ef5e54549300a75c545493033ddf72549300a7cf52549302975e52549302975c52549300a7cc5254930005df7154930095de7154930095dc71549300a75f51549301a5df705493000dde705493000ddc70549301a6df60549301b7db60549301a75f50549301a75d50549301a7da20549301a7da1054930295df7690930005de7690930005dd7690930295dc7690930295df75909300a5de75909302975e75909300a55e7590930005dd75909302975d75909300055d7590930295dc7590930165dd7490930305de72909302979f429093009fcf4290930297cc4290930095de7190930005dd7190930095dc7190930185df709093000dde7090930187da709093000dda7090930185dd7090930297d97090930005d9709093000ddc7090930186df6090930197db6090930187cf2090930187da2090930187da1090930005df7650930005de7650930005dd7650930005dc7650930005df75509300a5de7550930005dd75509300a5dc7550930185df745093009f9e64509300079d64509303e79f545093009f9c545093032ddf725093009fcf42509302979e42509302979c425093009fcc4250930005df7150930095de7150930095dc715093009f9f4150930165df705093000dde705093000ddc7050930166df6050930177db60509301679f40509301679d4050930167da2050930167da10509303ddde76d85300a5de75d8530005dd75d85300a5dc75d853009dde74d8530005dd74d853009ddc74d8530006df64d8530006dd64d8530295de72d8530005dd72d8530006df62d8530006dd62d85303b5dd71d8530096de61d8530097d661d8530096dc61d853001ddf70d85303d7db70d853000dde70d853001ddd70d853000ddc70d85303c6df60d85303d7db60d85303c7da20d85303c7d710d85303c7da10d85303c7d510d85303cddf7658530005df75585300a5de75585300a5dc7558530005df745853009dde745853009ddc7458530006df6458530006dd6458530005df7258530295dc7258530006df6258530006d
  | 11 => 0x6df6559130006dd6559130445df74591300079f645913009ede645913009edc645913009f9c645913009f9e5459130005df7259130295dc725913009f9f4259130005df7159130095de7159130095dc715913009f9f4159130435df7059130007db705913043ddb7059130436df60591300b7db60591304379e40591304379c4059130437da2059130437da1059130005df7655130005de7655130005dd7655130005dc765513042ddf75551300a75e65551300075d6555130425df745513009f9e64551300079d64551300a79f545513009f5e545513009f5c545513009f9c5455130005df7255130295dc72551300a75c5255130005df7155130095de7155130095dc71551300a75f51551301e5df7055130007db7055130005db705513000dde70551301e5dd705513000ddc70551301e7d8705513000dd870551301e6df60551301f7db60551301e75f50551301e75d50551301e79f40551301e79d40551301e7da20551301e7da10551300a5de75d8930005dd75d89300a5dc75d893009dde74d8930005dd74d893009ddc74d8930095de71d8930005dd71d8930095dc71d893001ddf70d893041fdb70d893001ddd70d893040edf60d893041fdb60d893040fcf20d893040fda20d893040fcd20d893040fda10d8930415dd76989300a5de7598930005dd7598930295dc759893009dde7498930005dd7498930295dc7498930006df6498930006dd64989303f5de7298930296df6298930007cf6298930095de7198930005dd7198930095dc7198930006de6198930006dc6198930405dd7098930297d97098930055d97098930406df609893007fdb6098930407da2098930407da1098930005df75589300075f75589300055f75589300a5de75589300a5dc75589300075c75589300a55c7558930005df745893009dde745893009ddc7458930007cf6258930296de6258930005df7158930095de7158930095dc7158930415df7058930007db705893007ddb7058930416df6058930057db6058930417da2058930417da105893040dde76189300a5de75189302975e75189300a55e7518930005dd75189302975d75189300055d7518930295dc751893009dde74189302979e741893009d9e7418930005dd74189302979d74189300059d7418930295dc7418930006df6418930006dd6418930405de7218930296df6218930297ce6218930296dd6218930007cd6218930006cd6218930095de7118930297d67118930095d67118930005dd7118930297d57118930005d57118930095dc7118930006de6118930006dc611893001ddf701893000dde701893001ddd7018930297d9701893000ddc70189303f6df60189303ffdb60189303f7cf20189303f7da20189303f7cd20189303f7da1018930295df7694930005de7694930005dd769
  | 12 => 0xd655454002e7c6554540025be74545401473e54545400073d54545400067f76545400057e76545400067e76545400047e76545400067d76545400057c76545400067c76545400047c76545401473e74545400073d74545401367f645454049e7f635454013e7e635454049e7d635454013e7c63545400067f62545402ce7c62545401473f42545400073d425454014d7f71545400bf7771545400ae7f61545400167e61545400167c61545400af3f41545401367f60545401477b40545401373e40545401373c40545401377840545401375f30545401377710545401377a105454000dbc7650540016bc765054000cbc7650540005bf7550540005bd75505400073f65505400073c6550540496bf6350540496bd6350540005bf7250540006bf6250540025bf7150540027b77150540007b76150540016be6150540016bc61505400afb461505400af3f51505400af3d5150540007bb705054000dbe705054000dbc705054011fb87050540026bf6050540027bb605054011f9f305054011fb7105054011fba1050540004fe76c8540004fd76c854004cfc76c85400067f65c85401167c65c8540025be74c8540005bd74c854004eee62c8540007ad42c8540004ff7648540004fe7648540004fc76485400067f65485400f67c6548540025be7448540005bd7448540005df73485400b5dc7348540007ad424854048dde76d9530465dd75d95300a6de65d95300a75e65d95300a6dc65d953009dde74d9530005dd74d953009ddc74d95300075e54d95300a75c54d9530295de72d9530005dd72d95300a75c52d9530095de71d9530005dd71d9530095dc71d95300a75f51d953001ddf70d953000dde70d953001ddd70d953000ddc70d9530476df60d9530487db60d95304775f50d95304775d50d9530477da20d9530477da10d953047ddf7659530475df75595300075f65595300a6de65595300a6dc65595300a75c6559530005df745953009dde745953009ddc74595300a75f5459530005df7259530295dc72595300a75f5259530005df7159530095de7159530095dc71595300a75f5159530465df7059530007db705953046ddb7059530466df60595300cfdb60595304675e50595304675c5059530467da2059530467da105953045dde76d91300a5de75d9130005dd75d91300a5dc75d9130006df65d9130006dd65d9130435dd74d913009ede64d913009f9e64d913009edc64d9130295de72d9130005dd72d9130095de71d9130005dd71d9130095dc71d913001ddf70d913000dde70d913001ddd70d913000ddc70d9130446df60d9130457db60d91304479f40d91304479d40d9130447da20d9130447da10d913044ddf7659130005df75591300075f75591300055f75591300a5de75591300a5dc75591300075c75591300a55c7559130
  | 13 => 0x51404cebf63551404cebd63551400bf3f53551404cf3d5355140005bf72551400bf3c5255140005bf71551400bf3f5155140007bb705514000dbe705514000dbc70551401e7b87055140026bf6055140027bb60551401e73f50551401e73d50551401e79f30551401e7ba105514004cfe76d89400067f65d89400067c65d89400b5de73d8940005dd73d894002cfe75d8940004fd75d894002cfc75d894000cfd74d8940004ff73d894001cfe73d8940006de73d894001cde73d8940004fd73d8940006dd73d8940004dd73d894001cfc73d89404c6ee42d89404c6ed42d8940014fe71d8940004fd71d8940014fc71d89404c6bf41d8940024fd70d894032edf30d894032edd30d894032eef20d894032efa10d89400bd7e75989400057d75989400067f65989400067c6598940006ef6298940065f970989400057f75589400bd7c75589400067f65589400067c6558940085fb70589400067f65189400067c651894004eee6218940006ed6218940004fe7694940004fd769494004cfc76949400067f659494002e7c6594940025be7494940005bd74949400073d5494940004ff7654940004fe7654940004fc76549400067f655494002e7c6554940025be74549401bf3e545494000dbc765094004ebc765094000cbc7650940005bf7550940005bd75509400073f655094017ebe655094017ebc65509400073c655094017e3c65509404bebf63509404bebd6350940025bf7250940027af7250940007af625094004ebe625094004ebc6250940007ac6250940005bf7150940007bb705094000dbe705094000dbc7050940167b87050940026bf6050940027bb60509401679f3050940167ba1050940014fe76d85400067f65d85400067c65d85400aef661d85400067f75d854002cfe75d8540004fd75d854002cfc75d85400067c75d854000cfd74d8540014fc74d8540004ff73d854001cfe73d8540004fd73d854001cfc73d854004cfe72d8540004fd72d85404b6bf42d8540006bd42d85400aef641d85404b6f541d8540024fd70d854025edf30d854025edd30d854025ef710d85400057f75585400bd7c75585400067f65585400067c65585400aef461585404adfb705854002e7f76d45400057e76d45400be7e76d45400047e76d45400be7d76d45400bd7c76d454002e7c76d454002c7c76d454015f3e74d45400bf3d74d454014e7f64d45404a67f63d45401567e63d45404a67d63d45401567c63d45400067f62d45402de7c62d454015f3f42d45400073d42d45401357d71d45400ae7f61d45400167e61d45400167c61d45400af3f41d454014e7f60d454015f7b40d454014f3e40d454014f3c40d454014f7840d454014f5f30d454014f7a10d4540004ff7654540004fe7654540004fc76545400067f655454002e7e65545400067
  | 14 => 0x57d7548550005df73485500cddc734855002cfe76d95400be7e65d95401e4fd75d954000cff74d9540024fe74d954000cfd74d9540024fc74d95404ee7f54d95404ee7d54d9540004ff73d954001cfe73d9540004fd73d954001cfc73d95400be7f53d95400067e53d95400067d53d95400be7c53d954004cfe72d9540004fd72d95400be7f52d95400be7c52d9540014fe71d9540004fd71d9540014fc71d95400be7f51d95400067e51d95400be7c51d9540024ff70d9540024fd70d954042e7f50d954042e7d50d954042edf30d954042edd30d95404d57e76d954002c7e76d954042f3f74d954042f3c74d95400067f63d95400067e63d95400067d63d95400067c63d95404ef3f42d95400057d71d95400067e61d95400067c61d95404ef3f41d95404ef7b40d954042f3e40d954042f3c40d954042f7840d954042f5f30d954042f5d30d954042f7a10d954042e7f74d95404ee7e74d954042e7d74d954042e7c74d95400067f73d95400067e73d95400067d73d95400067c73d95404ee7f43d95404ee7e43d95404ee7d43d95404ee7c43d95400067f72d95400067e72d95400067d72d95400067c72d95404ee7f42d95404ee7e42d95404ee7d42d95404ee7c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400047d71d95400067c71d95404ee7f41d95404ee7e41d95404ee7d41d95404ee7c41d95400067f31d95400067e31d95400067d31d95400067c31d95400067e21d95400067c21d954042e7f70d954042e7e70d954042e7d70d954042e7c70d954042e7f40d954042e7e40d954042e7c40d954042e7f30d954042e5f30d954042e7e30d954042e7d30d954042e5d30d954042e7c30d954042e7f20d954042e7e20d954042e7d20d954042e7c20d954042e7f10d954042e7e10d954042e7d10d954042e7c10d954002cff76595400be7c6559540425bf74595404e5fb705954042cff75595400067f7559540424ff7459540006bf7459540004ff735954001cfe7359540004fd735954001cfc7359540004ff725954004cfc7259540004ff7159540014fe7159540014fc71595400be7f51595401e4ff7059540006fb70595401e6df305954042d7e76195400be7e761954042c7e76195404df3e74195404d73d74195404d67f64195400bf5e73195400bf5d73195400067f63195400067e63195400067d63195400067c63195404df3f42195400057d71195400067e61195400067c61195404df3f41195404d67f60195404df7b40195404d73e40195404d73c40195404d77840195404d75f30195404d75d30195404d77a101954000dbc765514002ebc765514000cbc7655140025bf75551400273f75551400073f655514002ebe655514002ebc65551400bf3c655
  | 15 => 0xc41d915002cfd70d9150426bf40d9150426df30d9150426dd30d91500d6bc6459150525fb705915000d7c76551500267c765515000c7c765515002d7f745515002f3f74551500073f64551500267e64551500267c64551500d73c645515051e7f635515051e7d63551500d73f435515051f3d43551500057f725515039e7c62551500057f71551500077b705515000d7e705515000d7c70551501e778705515002e7f605515002f7b60551501e73f40551501e75f305515004cfe76d895000cfd75d8950024fe74d8950004fd74d8950024fc74d8950004ff73d895001cfe73d8950004fd73d895001cfc73d8950516ee52d8950516ed52d8950014fe71d8950004fd71d8950014fc71d89505167f51d895002cfd70d895033edf30d895033edd30d895033eef20d89501c67f65989500d5be7498950005bd7498950006ef629895006df9709895008dfb70589503267f651895004eee6218950006ed621895000d7c765495004e7c765495000c7c76549500057f74549501be7e64549501be7c645495050e7f635495050e7d635495002d7f725495002f6f72549500076f625495004e7e625495004e7c62549500076c62549500057f71549500077b705495000d7e705495000d7c70549501a778705495002e7f605495002f7b60549501a75f3054950004fe7690950004fd769095004cfc769095002d7e75909500057d7590950004ff7650950004fe7650950004fc765095002d7e75509500057d7550950006bf6450950026bc645095017f3f5450950014fe76d85500c6f661d855014e7f75d855000cfd75d8550014fc75d85500147c75d8550024fe74d8550004fd74d8550024fc74d85505067f54d85500067d54d8550004ff73d855001cfe73d8550004fd73d855001cfc73d855004cfe72d8550004fd72d85505067f52d85500067d52d855014e7f51d85500c6f651d8550506f551d855002cfd70d855014e7e50d855014e7c50d855014edf30d855014edd30d855014ef710d8550005bf74585500d5bc74585500c6f461585504fdfb70585501367e765455000d7c76545500167c765455000c7c76545500057f74545500067f64545501467e64545501467c64545504f67f635455013e7e63545504f67d635455013e7c63545500057f72545500067f62545502ce7c625455002d7f715455002f7771545500c67f61545500077761545500067761545500167e61545500167c61545500c77461545500077b705455000d7e705455000d7c705455013778705455002e7f605455002f7b60545501375f3054550137771054550004ff7650550004fe7650550004fc765055002d7e75505500057d7550550004fe76c8550004fd76c855004cfc76c855002d7e75c85500057d75c8550004ff7648550004fe7648550004fc764855002d7e7548550
  | 16 => 0x8d21566dd71d8d21566dc71d8d21566df51d8d215665f51d8d21566de51d8d21566dd51d8d215665d51d8d21566dc51d8d21566df41d8d21566de41d8d21566dd41d8d21566dc41d8d21566df21d8d21566de21d8d21566dd21d8d21566dc21d8d21006df70d8d21006de70d8d21006dd70d8d21004dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dc50d8d21006df40d8d21006de40d8d21006dc40d8d2156edf20d8d21006de20d8d2156edc20d8d21566df10d8d21566de10d8d21566dd10d8d21566dc10d8d2102cff7654921014fe76549211acfd7654921014fc76549210067f655492102e7c6554921006df63549211b6dc6354921005f77154921015f4715492104fe4215492155dee769092104eee769092104f6e759092104f6d759092116ded7490921026ee6490921026ec649092104def7390921555ed7390921007cf639092154fcc6390921015ee7190921015ec719092104eef619092104fe7619092118f6f519092118f6d519092118fe6319092154fe53190921005ed709092154fcf309092118fe71090921024ff7650921014fe765092116cfd7650921014fc7650921006bf6450921026bc6450921006df6350921176dc635092104fac4250921005f77150921015f47150921015ec7650921026ec7650921014ec765092104def745092104faf7450921007af6450921026ee6450921026ec64509210efac6450921547af54509210efac545092153def735092153ded7350921007cf6350921537cc63509210efaf4350921537ad4350921007e77150921015ee7150921015ec715092116fe47150921015e4715092104eef615092104fe7615092116f6f515092116f6d515092116faf415092116fad415092116fe63150921537e53150921005ef70509210efaf4050921537cf305092116fe7105092100cfe76d81210e5dc73d8121006df63d8121006dc63d81210defa60d812102cfe75d8121004fd75d812102cfc75d8121024fe74d8121004fd74d8121024fc74d8121004ff73d8121006df73d812101cfe73d8121004fd73d812101cfc73d8121006dc73d812101cdc73d8121014fd72d812100cfc72d8121006ee42d8121006ed42d812104cfd71d812100cfc71d81210767f51d81210767d51d81210dedf30d81210defa20d81210defa10d81210057f75581210f57c7558121005bf74581210edbc7458121005df73581210e5dc7358121006df6358121006dc63581210def86058121024fe76d91500d6be64d915000cfd75d9150024fc75d91500d6be54d915052ebd54d9150004ff73d915001cfe73d9150004fd73d915001cfc73d91500d6bf43d9150006bd43d915004cfe72d9150004fd72d91500d6bf42d9150014fe71d9150004fd71d9150014fc71d915052e7f51d9150006be41d91500d6b
  | 17 => 0x14fd72d95210f67f52d952104cff71d952104cfd71d95211ce7f51d95211ce7d51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210f67c50d9521006df30d95211cef710d95210f67c6559521005df73595210e5dc7359521006dc6359521585ef72595211ccff75595210067f7559521004ff7459521024fe7459521024fc74595210067e54595210f67c5459521004ff7359521006df7359521004df735952101cfe7359521004fd735952101cfc7359521006dc735952101cdc73595210f67f53595210067d5359521584ff7259521006ef72595212ce7e52595212ce7c52595211acff7159521006f771595211ae7f51595211ae7d5159521004ff705952100cfe705952100cfc70595210f67f5059521006df30595211aef71059521024fe76d91210f57e75d91210057d75d91210eebe64d9121006dc63d912102cfe75d91210067e75d912102c7e75d9121004fd75d91210067d75d91210047d75d912102cfc75d91210eebe54d9121004ff73d912101cfe73d9121004fd73d912101cfc73d9121014fd72d91210eebf42d912104cff71d912104cfd71d912118e7f51d912118e7d51d912118ebf41d912118ebd41d912100cfe70d9121004fd70d912100cfc70d9121006be40d91210eebc40d9121006df30d912118ef710d91210eebc6459121005df73591210e5dc7359121006dc635912157def7259121004ff755912102cfe755912102cfc755912118cff7459121006bf7459121004ff7359121006df7359121004df735912101cfe7359121004fd735912101cfc7359121006dc735912101cdc73591210eebf4359121006bd435912157cff7259121006ef725912116cff7159121006f7715912116e7f515912116e7d5159121004ff705912100cfe705912100cfc70591210eebf4059121006df305912116ef71059121004ff7655121004fe7655121004fd7655121004fc76551210067f655512102e7c6555121006bf6455121026bc64551211f6dc6355121575de76d8d210e6de76d8d2101cde76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d21567cf72d8d21567cc72d8d2156fd771d8d21567d471d8d215675f51d8d215675d51d8d2156fd721d8d21567ce21d8d21567cc21d8d21567d421d8d21005dd70d8d21006de60d8d21006dc60d8d21567d710d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d21566df72d8d2156ede72d8d21566dd72d8d21566dc72d8d21006df52d8d2156ede52d8d2156edc52d8d21006df42d8d2156ede42d8d2156edc42d8d21566df71d8d21566de71d
  | 18 => 0xf655494102e7c6554941015bc765094104ebc7650941014bc765094117ebe655094117ebc65509415b5bf73509415b5bd73509415aebf63509415aebd6350941025bf7250941027af7250941007af625094104ebe625094104ebc6250941007ac6250941007b77150941015be7150941015bc715094116fb47150941026bf6150941027b7615094116f3f515094116f3d5150941005bf70509415af9f305094116fb7105094100cfe76d814111efa60d814102cfe75d8141004fd75d814102cfc75d8141014fd74d814100cfc74d8141004ff73d814101cfe73d8141004fd73d814101cfc73d814104cfe72d8141004fd72d81414aebf42d8141006bd42d8141024fd71d814126e7f51d814126e7d51d814111efa40d814111edf30d814111efa10d81410057f755814112d7c755814111ef8605814104e7f7559721004ff7459721024fe7459721024fc74597210067e54597211167c5459721004ff735972101cfe7359721004fd735972101cfc73597211167f53597210067d5359721014fe7259721014fc725972104e7e525972104e7c52597211ae7f51597211ae7d5159721004ff705972100cfe705972100cfc70597211167f5059721006df305972104eef2059721004ff755932102cfe755932102cfc755932104ebf7459321006bf545932110ebc5459321004ff735932101cfe7359321004fd735932101cfc735932110ebf4359321006bd4359321014fe7259321014fc725932104ebe425932104ebc425932116e7f515932116e7d515932116ebf415932116ebd4159321004ff705932100cfe705932100cfc705932110ebf4059321006df305932104eef2059321004ff765532104cfe7655321004fd765532104cfc765532139e7f655532102e7c655532104def7650b215a6ef7650b2104faf7450b2104faf6450b21026ee6450b2104eec6450b2104fac6450b2159faf5450b2110fac5450b21595ef7350b21595ed7350b2110faf4350b2158fad4350b21015ee7150b21015ec7150b2116f6f5150b2116f6d5150b2116faf4150b2116fad4150b21005ef7050b2110faf4050b2158fcf3050b21004ff75583210067f75583210047f755832102cfe755832102cfc75583210067c755832102c7c7558321004ff7458321024fe7458321024fc7458321004ff735832101cfe7358321004fd735832101cfc7358321014fe725832100cfd7258321014fc725832104eee4258321006ed425832105e7f515832105e7d515832104ef6215832104ef5215832104efb70583210fedf30583210fefa3058321006f9305832104efb205832104ef820583210fefa105832102cfe76d95210f67e65d9521006dc63d9521024fe74d9521004fd74d9521024fc74d95210f67f54d9521004ff73d952101cfe73d9521004fd73d952101cfc73d9521
  | 19 => 0x95117f77615095116f3f41509510057f70509511357e70509511357c70509511473f40509515df5f305095116f7710509511357e76d81511457e74d81510057d74d81511457c74d81510067f64d81510067d64d81510057f73d815113d7e73d81510057d73d815113d7c73d81512cd7e72d81510057d72d81510067f62d81510067d62d815102d7f71d81514ff7771d81510157e71d815102d7d71d81510157c71d81512867f61d81514ff7761d81511367e60d81511377a60d81511367c60d81511375f30d81511377710d81511377a10d81512877910d81510057f74581510073f74581510053f74581511457e74581511457c74581510073c74581511453c74581510067f64581510067d64581510057f735815113d7e73581510057d735815113d7c73581510057f72581512cd7c72581510067f62581510067d62581510077771581510477761581511357f70581510077b60581511367e60581511367c60581511377860581511375f305815113777105815102cfe76d954112e7e65d95411ecfd75d9541014ff74d9541014fd74d95415d67f54d95415d67d54d9541004ff73d954101cfe73d9541004fd73d954101cfc73d95415d6bf43d9541006bd43d954104cfe72d9541004fd72d954112e7f52d9541024ff71d9541024fd71d95415ce7f51d95415ce7d51d954100cfe70d9541004fd70d954100cfc70d95410067e50d954112e7c50d95415d6bf40d9541006df30d95415cef710d954102cff765954112e7c65595415c5bf745954115df771595415ccff75595410067f75595415c4ff7459541006bf74595411467e54595411467c5459541004ff735954101cfe7359541004fd735954101cfc735954112e7f53595410067d5359541146bf4359541006bd4359541004ff725954104cfc725954112e7c52595411ecff7159541006f771595411ee7f51595411ee7d5159541004ff705954100cfe705954100cfc705954112e7f5059541146bf4059541006df30595411eef7105954104cfe76d894112d7e75d89410057d75d894102cfe75d89410067e75d894102c7e75d8941004fd75d89410067d75d89410047d75d894102cfc75d8941014fd74d8941004ff73d894101cfe73d8941004fd73d894101cfc73d89415bebf43d8941006bd43d89415beee42d89415beed42d8941024fd71d894157e7f51d894157e7d51d894157eef21d894100cfe70d8941004fd70d894100cfc70d89415bebf40d8941006df30d894157ef710d894112d7e75989410057d7598941006ef62989410edf57198941005df7358941125dc735894110df7715894104eee6218941006ed6218941004fe7694941004fd769494104cfc769494102e7e65949410067d6594941025be7494941005bd7494941004ff7654941004fe7654941004fc76549410067
  | 20 => 0x1473f43591510073d43591510057f72591512cd7c72591511ed7f715915100777715915100577715915112f7761591510057f70591511357e70591511357c70591511473f40591510075f30591511ef7710591511457e74d89510057d74d89511457c74d89510067e64d89510067c64d89510057f73d895113d7e73d89510057d73d895113d7c73d89510067f63d89510067d63d895102d7f71d895102d7d71d89515867f61d895160f7761d89515876f21d89515876d21d89511357e70d89510057d70d89511357c70d89510075f30d89515877710d89511457e74989512cf3e74989511453e74989510057d74989512cf3d74989510053d74989512cd7c74989510067f64989510067d64989512cd7f739895113d7e73989510057d73989512cd7c73989515fd7e72989512ce7f62989510076f62989511cd7d71989512cf7571989510057571989511ce7f61989511177761989511357e70989510057d70989511357c70989510067e60989510067c60989510075f30989511cf7710989510057f74589511457e74589511457c74589510067e64589510067c64589510057f73589510075f73589510055f735895113d7e73589510057d735895113d7c73589510075c735895113d5c73589510067f63589510067d63589510076f62589512ce7e62589511ad7f71589510077771589510057771589510f77761589510057f70589511357e70589511357c70589510075f30589511af7710589515857e76189511457e74189510057d74189512cd7c74189510067f64189510067d64189512cd7f731895113d7e73189510057d73189512cd7c73189511cd7e72189512ce7f62189512cf6e62189512ce7d62189510076d621895102d7f71189510157e711895102d7d71189510157c71189515fe7f61189516077761189515ff6f21189515ff6d21189511357e70189510057d70189511357c70189510067e60189510067c60189510075f30189515ff7710189512cd7f76909510057e76909512ce7e76909510047e76909510057d76909512ce7d76909510047d76909512cd7c769095116d7d74909512cd7f739095113d7e73909515f57d73909512cd7c739095155d7e72909512cf3f42909511476f42909512cf6c429095118d7f71909510157e719095118d7d71909510157c719095118e7f619095119f77619095118f6f21909511357e70909510057d70909511357c70909515ef5f309095118f7710909510057f76509510057e76509510057d76509510057c765095118d7f74509510073f64509511473c64509515e57f735095113d7e73509515e57d735095113d7c73509511473f43509515df3d435095157d7f72509511476f42509512cf3e42509512cf3c42509511476c425095116d7f71509510157e71509510157c715095116e7f615
  | 21 => 0xf21d895100cfe70d8951004fd70d895100cfc70d895160e7f50d8951006df30d8951586f710d8951145be7498951005bd7498951006ef62989510f5f57198951005df735895113ddc7358951115f7715895104eee6218951006ed62189510157e76949511ce7e76949510147e76949511457e74949512cf3e74949511453e74949510057d74949512cf3d74949510053d74949512cd7c74949510067f64949512cd7f739495113d7e739495163d7d73949512cd7c739495102d7e729495102f6e72949512ce7f62949510076f62949512cf6c62949510157e71949511cf7671949512cf7571949510157c719495102e7f619495102f7761949511357e70949510057d70949511357c70949511c67e60949511c67c60949516375f30949511cf7710949510157c765495104e7c76549510147c76549510057f74549511457e74549511457c74549511be7e64549511be7c645495162d7f735495113d7e735495162d7d735495113d7c73549516267f63549516267d635495102d7f725495102f6f72549510076f625495104e7e625495104e7c62549510076c62549510077771549510157e71549510157c71549511af74715495102e7f615495102f7761549510057f70549511357e70549511357c70549516275f30549511af771054951004fe7690951004fd769095104cfc76909512cd7f759095102d7e75909510057d759095102d7c7590951004ff7650951004fe7650951004fc76509510057f755095102d7e75509510057d755095102d7c7550951006bf6450951026bc645095117f3f54509511473c545095100cfe76d815102d7e75d81510157d75d8151136fa60d81511377a50d8151014fd75d81511367d75d81510147d75d815100cfc75d8151024fe74d8151004fd74d8151024fc74d81514fe7f54d81510067d54d8151004ff73d815101cfe73d8151004fd73d815101cfc73d815104cfe72d8151004fd72d81514fe7f52d81510067d52d815102cfd71d81511367e50d8151136fa50d81511367c50d8151136df30d8151136fa10d8151005bf7458151145bc7458151136f8605815161d7e76d91511467e64d91511473e64d91511463e64d91511467c64d91510057f73d915113d7e73d91510057d73d915113d7c73d91510067f63d91510067d63d91512cd7e72d91510057d72d91511473f42d915102d7f71d91510157e71d915102d7d71d91510157c71d91515c67f61d91516177761d91515c73f41d91515c73d41d91511357e70d91510057d70d91511357c70d91510073e40d91511473c40d91510075f30d91515c77710d91515cd7f76591515c57f74591510073f64591511467e64591511467c64591511473c64591511463c64591510057f735915113d7e73591510057d735915113d7c73591510067f63591510067d6359151
  | 22 => 0x854216ef641d854216ef621d854200cfe70d8542004fd70d854200cfc70d854210ebf40d8542006df30d8542005df7358542175dc735854216ef4615854200cfe76d8142166fa60d814202cfe75d8142004fd75d814202cfc75d814204cfd74d8142004ff73d814201cfe73d8142004fd73d814201cfc73d8142024fd72d8142014fe71d8142004fd71d8142014fc71d8142086bf41d8142166fa40d8142166df30d8142166fa20d81420057f755814217d7c7558142166f860581422dd7f7690b5102d7e7690b512de7e7690b5102c7e7690b5119d7d7690b512de7d7690b510047d7690b5102d7c7690b5115f3e6490b5119f3d6490b512dd7f7390b511557e7390b516757d7390b512dd7c7390b5155d7e7290b512df3f4290b5115f6f4290b512df6c4290b5118d7f7190b510157e7190b5118d7d7190b510157c7190b5118f6f2190b5114d7e7090b510057d7090b5114d7c7090b5166f5f3090b5117d7f7650b5102d7e7650b5117d7d7650b5102d7c7650b5117f3f6450b5115f3c6450b516657f7350b511557e7350b516657d7350b511557c7350b5115f3f4350b5165f3d4350b5157d7f7250b5115f6f4250b512df3e4250b512df3c4250b5115f6c4250b5116d7f7150b510157e7150b510157c7150b5116f3f4150b510057f7050b5114d7e7050b5114d7c7050b5115f3f4050b5165f5f3050b51024fe76d915102d7e75d91510157d75d9151146be64d91511473e54d9151014fd75d91515c67d75d91510147d75d91511467e54d9151146be54d91511463e54d9151616bd54d91511467c54d9151004ff73d915101cfe73d9151004fd73d915101cfc73d91516167f53d91510067d53d915104cfe72d9151004fd72d91516167c52d9151146bf42d915102cfd71d91515c6bf41d915100cfe70d9151004fd70d915100cfc70d91516167f50d9151006be40d9151146bc40d9151006df30d91515c6f710d9151146bc6459151655f771591510157c76551510267c76551510147c765515102d7f745515102f3f74551510073f64551510267e64551510267c64551511473c64551510263c645515164d7f735515113d7e735515164d7d735515113d7c73551516467f63551516467d63551511473f43551516473d43551510057f72551512cd7c725515139e7c62551510077771551510157e71551510157c71551511ef74715515102e7f615515102f7761551510057f70551511357e70551511357c70551511473f40551516475f30551511ef77105515104cfe76d8951014fd75d89515867d75d8951024fe74d8951004fd74d8951024fc74d89510067e54d895160e7c54d8951004ff73d895101cfe73d8951004fd73d895101cfc73d895160e7f53d89510067d53d895160eee52d895160eed52d89512ce7c52d895102cfd71d8951586e
  | 23 => 0x67d71596420067c71596421be7f41596421be7e41596421be7d41596421be7c41596420067f31596420067e31596420067d31596420067c315964204e7f215964204e7e215964204e7d215964204e7c21596420067f70596420067e70596420067d70596420067c70596421be7f40596421be7e40596421be7d40596421be7c40596420067f30596420065f30596420067e30596420067d30596420067c305964204e7f205964204e6f205964204e7e205964204e7d205964204e7c20596420067f10596420067e10596420067c1059642004ff755864202cfe75586420067e75586420067d755864202cfc7558642004ff735864201cfe7358642004fd735864201cfc735864204cfe725864204cfc725864204ebf425864204ebd425864204ef7715864218ef6415864218ef63158642006f5315864204ef7215864204ef42158642004ff705864200cfe705864200cfc7058642006df305864204eef205864218ef71058642004ff755824202cfe755824202cfc7558242004ff735824201cfe7358242004fd735824201cfc735824204cfe725824204cfc725824204ebf425824204ebd4258242004ff7158242014fe7158242014fc715824204eef215824204efb7058242186fa4058242186df3058242186fa3058242006f9305824204efb205824204ef82058242186fa105824202cfe76d954217e7e65d9542025be74d954204dbd74d954217f3f54d954204cff74d954204cfd74d954217ebd74d954204cbd74d95421de7f54d954217ebf54d954217e3f54d95421de7d54d95421debc54d9542004ff73d954201cfe73d9542004fd73d954201cfc73d95421debf43d9542006bd43d9542024fd72d954217e7f52d9542014fe71d9542004fd71d9542014fc71d954217e7f51d954200cfe70d9542004fd70d954200cfc70d95420067e50d954217e7c50d95421debf40d9542006df30d954217e7c65595421bf3c545954267def72595421dcff75595420067f75595421bcff7459542006bf745954217ebf54595421be7e54595421be7c54595421bebc5459542004ff735954201cfe7359542004fd735954201cfc735954217e7f53595420067d53595421bebf4359542006bd435954267cff7259542006ef725954239e7e525954239e7c5259542004ff7159542014fe7159542014fc715954217e7f5159542004ff705954200cfe705954200cfc705954217e7f50595421bebf4059542006df305954202cff7654942024fe76549421bcfd7654942024fc76549420067f655494202e7c6554942005bf7454942025bc74549421bf3c5454942014fe76d854216ef661d854202cfe75d8542004fd75d854202cfc75d854204cfd74d8542004ff73d854201cfe73d8542004fd73d854201cfc73d854210ebf43d8542006bd43d8542024fd72d
  | 24 => 0xe705865200cfc70586520067e50586520f67c5058652006df305865204eef20586521cef71058652004ff7458252024fe7458252024fc745825206e7f54582520067d5458252004ff735825201cfe7358252004fd735825201cfc735825204cfe725825204cfc725825204e7f525825204e7d5258252004ff7158252014fe7158252014fc715825206e7f515825204efb70582521c67e50582521c6fa50582521c67c50582521c6df30582521c6fa3058252006f9305825204efb205825204ef820582521c6fa1058252024fe76d915202d7e75d91521bebe64d91521bf3e54d915204cfd75d915204c7d75d91521be7e54d91521bebe54d91521be3e54d915219ebd54d91521be7c54d9152004ff73d915201cfe73d9152004fd73d915201cfc73d915219e7f53d91520067d53d915202cfd72d915268e7e52d915268e7c52d91521bebf42d9152014fe71d9152004fd71d9152014fc71d915219e7f51d915200cfe70d9152004fd70d915200cfc70d915219e7f50d9152006df30d91521bebc64591521bf3c5459152685ef7259152014fe76d85521aef661d85522de7f75d855204cfd75d8552024fe74d8552004fd74d8552024fc74d85520067e54d85521167c54d8552004ff73d855201cfe73d8552004fd73d855201cfc73d85521167f53d85520067d53d855202cfd72d85522de7e52d85522de7c52d85521ae7f51d85521aef651d85521aef621d855200cfe70d8552004fd70d855200cfc70d85521167f50d8552006df30d8552005df73585521b5dc73585521aef4615855200cfe76d81521a6fa60d815204cfd75d8152024fe74d8152004fd74d8152024fc74d8152004ff73d815201cfe73d8152004fd73d815201cfc73d815202cfd72d8152014fe71d8152004fd71d8152014fc71d815208e7f51d81521a6fa50d81521a6df30d81521a6fa20d81521a6f8605815204e7f75596421be7f54596421be7d5459642004ff735964201cfe7359642004fd735964201cfc735964219e7f53596420067e53596420067d535964219e7c535964204cfe725964204cfc725964204e7e525964204e7c5259642004ff7159642014fe7159642014fc715964219e7f51596420067e515964219e7c5159642004ff705964200cfe705964200cfc705964219e7f50596420067e505964219e7c5059642006df305964204eef20596421be7f74596421be7e74596421be7d74596421be7c74596420067f73596420067e73596420067d73596420067c73596421be7f43596421be7e43596421be7d43596421be7c435964204e7f725964204e7e725964204e7d725964204e7c725964204e7f425964204e7e425964204e7d425964204e7c425964204e7f325964204e7e325964204e7d325964204e7c32596420067f71596420047f71596420067e7159642
  | 25 => 0x8554006bd43d855404cfe72d8554004fd72d85546567c52d85541ee7f51d85541eef651d85541eef641d855400cfe70d8554004fd70d855400cfc70d85546567f50d855415ebf40d8554006df30d85541eef4615855400cfe76d81541e6fa60d8154024fd75d815402cfd74d8154004ff73d815401cfe73d8154004fd73d815401cfc73d815404cfe72d8154004fd72d8154014fe71d8154004fd71d8154014fc71d81545267f51d81541e6fa50d81541e6fa40d81541e6df30d81541e6fa30d8154006f930d81541e6f8605815404ebf74592521debe545925217ebd5459252004ff735925201cfe7359252004fd735925201cfc73592521debf4359252006be4359252006bd43592521debc435925204cfe725925204cfc725925204ebe425925204ebc4259252004ff7159252014fe7159252014fc715925217e7f51592521debf4159252006be41592521debc4159252004ff705925200cfe705925200cfc70592521debf4059252006be40592521debc4059252006df305925204eef205925217ebe755925217ebd75592521debc7559252006bf7359252006be7359252006bd7359252006bc735925217ebf535925217ebe535925217ebd535925217ebc535925204ebf725925204ebe725925204ebc725925204ebf525925204ebe525925204ebd525925204ebc525925204ebf325925204ebe325925204ebd325925204ebc3259252006bf7159252006be7159252006bd7159252006bc715925217ebf515925217e3f515925217ebe515925217ebd515925217ebc5159252006bf3159252006be3159252006bd3159252006bc315925204ebf215925204ebe215925204ebd215925204ebc2159252006bf7059252006be7059252006bd7059252006bc705925217ebf505925217ebe505925217ebd505925217ebc5059252006bf30592520069f3059252006be3059252006bd3059252006bc305925204ebf205925204eaf205925204ebe205925204ebd205925204ebc2059252006bf1059252006be1059252006bc105925239d7f76552520267f76552520247f765525202d7f745525202f3f74552520267e645525239f3e64552520263e645525239f3d64552520267c645525239e7f63552526967d63552521df3f43552526973d435525239d7f72552520076f725525239f6c725525202e7e625525202f6e62552520057f71552521c57e70552521c57c70552521df3f40552526975f30552520067d7558652004ff7458652024fe7458652024fc74586520f67f54586520067d5458652004ff735865201cfe7358652004fd735865201cfc735865204cfe725865204cfc725865204e7f525865204e7d525865204ef771586521ce7f51586521cef651586521cef63158652006f5315865204ef7215865204ef42158652004ff705865200cf
  | 26 => 0x40010098004000003000000c00c008020801403800701680000140010150000026019001000c01600a001000003a01f001802c00600000000ac000004003803c01a007006803800400700b800400800300780040160030058000004000014002800000901180040080000018010012006000001803c0ab000005c00a00000000000180070008040000000000800003a01e00500040000010008000000005003000400000000481040000010000000010000000800c00000100200040060000020008004000003001000a00900a802c002001003001800c0250020008002002001800c00000400080000020010008000004000001006400200c00380280020040120000032000005800c00800400000000000020080064002018007002400000000380fc00000000b0010008008000000800600400000280020040008018000003000001000e003000804007c00001a8028002081002800402c007001001800600f001002800200f004806c010000000801000200000f800000001a005800800c0150228020004019000001c00400800c800800800b000000001600a0010018000000014000800a000009001803c044002808c00200b00480000340030040010000001000002400a00d0158010002000002000c01c012004001401a007000801400601800a00040100000040010020005000000800000700c0004048005014000000200500500000020010008024000004000005001200d00f000000600a0000030000009004005401600300480140000080040000038000001000c07201300280100000000128064000020005006401a002005803005e0030008004002000006000c03003800680000000050140008012003010000000e004003003407e00001f802c00601300080380000050000004008032001803001a0050008008042029002800005e00c0018030018004000000c00401d0068038004021003800000400e000000805c0050060004008009000800803a022002800c02e002001803c000001000002400206b003800400200404cfe76d8954024fd75d895467e7d75d895402cfd74d8954686bf54d895467e7e54d895467e7c54d895467ebc54d8954004ff73d895401cfe73d8954004fd73d895401cfc73d89546867f53d89540067d53d895467ebf43d8954006bd43d8954686ee52d895439e7c52d895467eee42d8954014fe71d8954004fd71d8954014fc71d89546867f51d895400cfe70d8954004fd70d895400cfc70d89546867f50d895467ebf40d8954006df30d8954006ef629895404eee6218954006ed6218954014fe76d85541eef661d855415e7f75d8554024fd75d855402cfd74d855415e7e54d855415e7c54d8554004ff73d855401cfe73d8554004fd73d855401cfc73d85546567f53d85540067d53d855415ebf43d
  | 27 => 0x2a007000200e002800000600601a800001200a004000000403600e800c0020010108004032011005800002601b007009000a001001002400000d00300b000001b0000004000002012004c008003002000c00e0010000004000001003003c000001000000000000200900000040050008058004001003800400000d000000800c003003801000200700480340060000000004028000000001000000a00081280000050018030000003000002c00201e0000008002004000000001e000001805400600f0038060000000000804c006001000803400600300900c000001000280dc00a01800980040040000020074000004000000c0ac00c00000100000000148008006001004000c01401d00280300000000000004010001002000400200200c0060012000000801000e00000282900000020040000000005005000400000b0020004006028002001002001800d800000800c003003400000b000001000e000000000000e001000800400a008000001801e0000008024006003000002000201d00c00580080090140004000003004805000000001000080020020068048000003000000c002005009800c01602300880600100180038098006004001800409a00000180000000010028010000000019000000400e00380080180100008004018028000804c00e00e007002c00000600a80c40080000030008002008005006003000b00200100340010000080012000015802c0020000220000000009001004400a001019000000e013000000c000007000801400a000003000c02c025003804800a000001009800800a00380cc03000b003015c012007000000000000300300000020010300024010008003002400200900100700020090000038000001006804c024003002000806801900000000140170140000004006002000000200b00080340060170028000016003000800c00e0090060000000009004815403200000f8000022001000003800000200080c800c002000005c00200000300040080010070000000000000800000a0040028004014039004006802a00b0028004000006000805401e00000000200020040020008016000001003400400e0048018062001008802000200101280a00180010010014004000005801003001200080cc00402500001e400201c001000400604a00300300000070020008014025000000c00a00800000140220110028004004008001000400000100700fc0000000018004002004000000003201b0000020002013000801c00400500600140100030158004000001008805400c00000600000260080028004000001002800800000000000000180280010000006000001003c00a00000c81cc002001007005800c00b0068004002084000801c01e02300400000040000018024000001008000000000000580240
  | 28 => 0x7222900843b39250095124a5638ac26cb1d6c34122665589ae80e688763e28f9e711845031d80e60250ce800004dc000076c7f70c0a07910e638e079813c8fde79c80a80d30d14260141e1479d2c559902c67a8b447cd014e0c2800000010684ff920e17d1b3c3da919616000001ea9f901bd831459318ca00380008748000178000000000000c90000000000059695e4650004233c19001f7a09e41f8ecc47a98aa45489327bb00006478000193800000000006b200006d0800000000005c38000000176e4c2a0746121f0e62284de189872e000145c45211dc26396fc00000000e7923200000000e203326249a7e6a4940e2b1067a4c420ba0f31fac20e9f745839dbe08a93a830719b232e86d685b0e588731e7630997ea5d1916c8458f44023811883e1de442d86c822c9f3e45a0fbe2b9066a5dd1ebc648937835201567bd1f7e65d02d63768870861010009f85b00b7114e86e0d0e6b7800014a0000633a0c883a1a686fa1e647ad1a9826a070066a0036001002801800a00c011001c00e0060020008000022004800000000a00a801400a00101e000000400400980000080060000030000000009800000202a006007801e0010000008012009006805001000a000000c004007001005000400000e000800e008004003c000001010004c00600300100b009a001000000000e002001001000e009002800000003e0000038004004003802402a00400100000000060010074002003001817002c01400a001800a006000803c00c002000000800c00000a000c000013005003400001f004800800600a018801c00e0030028000000002000001800002a002802400400401f001800a0090000000000015000000000000200d80000000040000000020002006805c006020000802000400200f800401401f008001403e0000000004012000002000000800500b000001c045000014402800d000802c0080000020044012000000800c032004000000000a007003000400c005002800800a001001000000200700000080020040010038000000008802801600f000000002600a006805c004000000800c0980120000034012001000005c0040020000238022000007003800a000000000000e0040020008002004001807c01c012001800c00200c007000404e0200030000002005000000000400d006800c00800301400080060040008008002003000800800a00a00b00000260000028000002006001000800000a00680bc016051002800000400000000000180000030000006001000801c0180010098004034001000000801603b005000400000d00180180020010008030000004005800001c004000000008400100000240000100000000002025014800401c018013800002e00500280000000040140004000001003800000000c000000c0060040
  | 29 => 0x5a16182f0a1004ed98de6528ad27a11c145dc07205441f12359a19c2e3087a7a999bc78184140a78e00141897a5108b5a00020348b880c665893e06e199a080f99aa0430770000129a47483c630c933e3a799be744187c247a2f47bc000020a0bc454e00007b29ec64c80be84af042e026179a1c18d360bb1da40fa13ee75418601d00c1a1b81cd01a322d40dc856a2d490dc62814dc10c0d2e2569c3a7d581d079b99ce2940b3086e979231f9786798982c6e81ad4000000062316c207110702c90f903661a520001aca17c000088d8dd008500004e114602fc8000000060e1de22922180000000184c80ea144000000000000008850000000000000587305a08bcc00004a228b094c18796c6168067e1f31bb067980006f916a808980000e481505d300002379af2149030c7f016c889280005ce8000138190c2fb1a127f78f464d69dde30380005059dbc03c1d5c08c80007410c3a88b000037e80000000c940001ac22409b7e1b519fa0649b7a50119a6897050c2901bfa17097a200000000001f2683900000000986000000046b0ccc00017400001c98000181629a147c77600003f29244000164e2450f7826214be00013c65cb8fec14c882627a0b6a000000000012a472993ac30188306a6a1801dd1a4e042800043f0000000006e4f58c50000000000000000000000461800037b9ef66f00000714012e66d0c0c397969c08780000000dd81c11d2036b02765f58000000000058b800000019b68bc000035600000000000000000000000000000e4e31f000017c80f600002860000542255000077e000078c9ace7b8833a812210442b9c343481aa44490b4c549800050c9b4c2ee13c024413bc0000ec42bc81f68141704674185c6ac97d24258b586c5005231e13a286f8d646e383300c11530488218821b800005f113861915721eb9d8600020fc000181e5db1f64039047a4580000519073e387165e42605946138ad483592ca083042602483b889f92c60f38c9a42f087207807846bd18fc08c0c242141a4c32889c83a3216e30d228a4a611ba3dd0000754839c28284b28a714aa69b0b366ee9fb2426941252b9c401fb80005569b466220284063000078d13e674c81a6853000014f8cca00001860000a60000181400000000001606731986a01505e228085165cca1780000b48000076a000000000000001f10466449a1ea0000afc5781bb45e792ac64d124618206fc1ba8b2a3c4800038181ca79493ca82c05382db81762308f8e78621e03ea812c6ec806229e8cbc19f163278083e0722910054f8cfc54017201f091a022e00d266307a45b111fc5d919446a392cc49a1d6a09a9dee712a0ce429944e1fa9ef87cda212659a1ca40822841a207bc22d081636c9b2444d870e8750b0a75284061090ca80001ca2703a0c600c88e045009
  | 30 => 0xb9a1071ab403e8b7081a22d28b108ac7aa069867f096e000011a661a1e80548172000118864918d62ae00004a497840000f8858f82d26351d9237a9a5462d8c92025a2c674f11be41188c05341d2e6c38f1444700001030e804db000088108105ff1f865811e4200000ca0359ebe05e1db417b90186919dfc7ff215e8259fc25c615cc883076000020f66330cf46f5800012f97543d7a19a193000026e0000000002600000004a086e43f89b0825106383e0997821d0000000000081697e074f80001a980000000b982ed9946000078c21883ae0730000737800023680006ce92f20001a1c64580ec2d004722fe00003820a5c000024837ca01200011304fc22dc2a300001de8000000027a6c080001d3825a00006582e8180c17f90c600000002d90000000000000013ec88883ba7da000067d89f0000106029b800033603e66218e40113000000013f678f156e338800055d9ee617b1e980fb855a24f8df630611da847948a2de97e2759a1fc3d71aa2043832c107890c77d869601a86e2702842a0a498ee313054c4bf0c3e4959ccc619952872e068a663800000000003860b7e0ba21ee6070000000000066692ee68918d814700000000c520000b9e5fd03848a20a963b189aa62b1f1e000227000011740000000311075e1a68000000106418c00006ce149e0000000000207059a1cdc1849bf02fb80204aa8baa51e1cba4d714e00b783566d717224a702246a99b546fb9d401e01e3836d8b140ad1bae2dc9bac6cd805005695c27771f2c2d88c22890a09015885d0323124084395788649e046b1109c6b6209a1bf8474358843e246981254e80001280f0c6a084ae89a9bce86b07be7e821de5d68dc0872099211f971c82e1fc60708d7a84a186c67801d650b9522292057238c134c8261a340859d980c9821a2289c9a2ec02cc84d95988ac8a1a7ac0fce6aa00008819e9223d86da30a21424d119c203097da349a26e4408da4000156846895e82a516160970e0a48086b400016663cc0de823998d035c92260978be6875986e51c933282b02fe526a2102219608276136e0000b5e00019584871afc36a92945ec21c05ea1e5035a192a7fc971038ea2387130ad68251cd47a7139c0de995e5b7826800014fc0180ec26be9dba42097fa765800000000006d5832e72b10ea86b88984dc9bea664800057000007fa051a64a15820c180001cc9c6a41a88e45a689fc6e91a581688b8a4b700002f480000001bf8086170888f1f5837b103e0001bbe3c814982688f0e2a19090696991a5c0201420e1fd200000008c0154c0889fa84ef88c623ea0dc3f50bd65970c426e31574495025279290de0388a4464481de70b861013f000046d9cf860a1f5e4a890f84068a2a21e03b025986a22bd022c86390e00ed9f7848d901c8b98000339a2083cb97ee0
  | 31 => 0x1184c833f8fc689e9e5e60a9d30074880844f139e316923a4ae87187a2003a54598f62fd17946ef1faa0ce03de87f9ec24ff0a8a3a81cbc2030b960df214e5dc861628e83700001f4a514a01c263000025f052e6c480007ffa12e238800023500000000fc00000000000000000000000d900000930000110030069c0000803000027598c8753000043100002b00d748469b3e00000001f2000000000000000e6a0b90efa000000021022980000000000196a1c48ae03d00000407800065f8000269066e28c00005041d648a98c904578614000162a3fb80008b200004321cd80e611440001a8600019b0000103421f000076a064800011581b61d9a34c1bd2000000086d948821a877c0000000000000086580008bb11cc130112817a000039d00004888b046ff0c66889920075383b47a38d080788892000000039287760b29bb87b004f84f887101ae0f723be2148793012622a00000b681e60000f4e0000b9c0001fe074a8aa65318fd076ba2681299d142cf80f476896803478db44359a960139caa00000007ec02fa0000e4c33d9b587ad80005909f406711330000061c42e0a747890000000081c7a79e2a7208c160df8b786ba9552052123047d9d624909cee86512e215d01ae2f21e585c7823e2a884884c3854671b9da06af13d0674831e24b0004511002227a9ac61ff05345bb807668e192e38f81bc5ff88d01ca11f8000001436e0eb08b09f160638cb2366961a1eb0fd2292869e38c80006f1139600014d85a89a785681fd00000000867907a1811f6a7f9800075220e200000006bf9c7e000000000000000b81326000000000022b6000163a85f9db2308163084f000046a00004be80000001e0a4c3000000022e8673210c785205270c96d43bd044e010105607200008420000375156a0001d9e1928000000000057a8a120001a287c29902000135200011ee7b38eb40001d1801e80006178e5c00000002b61c08474105e51185fc2ff12647e600000000fae8a512be0f296f42c480000001f0000000001bc80007f200001e297aa819160a5071a7a65d961075508826590a901720ce06911e4e032139865580ba02d926e10382f089112e61d30e2e76303f264d80004ec96e439186721a010ba3c28048123121851a9b1c386988e134a2005101dac296000074186c07fe000050280368bd9ad02b990b280a91785871eba3e188d6815863a0d88fb25c5927c0000aa80408d2a68291d65910000207800077480000001c5e182954a00a100c13180000a5000000000001d20000548000015a082e5208000699a2fc0000d840a01d841ae943e11816aa05b0000130a0186a013223f599de0000000000000000017b27a8033e85d01d400019f22438fc477f9b1a0de223241615586c785b889682285980a8e4a993d8000000000007ba02e0
  | 32 => 0x95082321c1289c81227071f4240c158a00000004ed1a404bd8ba80001400519a21c1438c14669060c7858eee5230f2668e93700000000000000000000004c78ffc643992600000006af90ac000000000019d400000004bb00005cf148661f8e9000022865c69a30212978813389ac00015183b8832a7972278064071617021a403f0d3c200003e410127631d11705ef058800000005a398a442f9b0019183d2799800080690668aa000069904647f58582000047c000139081d800060e9de807e9a0684c0a0481c80006e121a815c043a0d60b205ac891855c0fa20000a707ef80002d707464ee14ee49a80007cc1ad60000cc01c99d803cca03060f000063a801c00009168a881080000c1261180000001dc270098dc0000af02611df046099ca25a8000000000010201b87249842335841000006786e60a6a0001b78163100677d08fc31500005ed016468511b805622160a700000b100003a70b0c72205124059f28000017067ba1dc30114d20000e8809f1d0e21100003df85c6191094e59f9c5a3b29aee38508b62c604284a20c9c50a19684ac805a725007c72c1822347026c3cd02622038d9473d849e8101e080000cfa82c8000319000060421580e199ec2978e0287d1ae03c7859642a02e2899000000015d4000000059e97f63998bac40103ac276808a3ed1f8a7be8080351800010081ac3429bc6340000073f8d7e00001ba0000afe0000f7c6b000002fc0058017893c1a707e400018be0131fb88a3112e19a046e7d500005be00000be10fe82a978a00000000001c10783000016e85406d68cde34e0e0c69b9d423ee9c601229b482d293620bf1b906f2838a6d9062a5c19c667899e8c312800052390421fa0000279958c1db87ce43b0a34000085200000000fc0aec270800059b9c3876986de000000044384c440c800000001c600006b634682aa00004007120e6e6d0191c2b795ae7499088532a22e15d9e3636987d8509036858d031c7c609762c880063390fa886a9e2c80013382dd03a63bc8fbc3f9053a32c03e281f16da5471ee81a91f467a28762411093439e88a66ea170c7e0939a80202e64671954469940c28894845d7092a573811c886143c05b85908ba800047e86027b59e7a6ab04963a0800047b0acc0a0820016b0cb47958e544d29c5841f0ede76217ae7951d0847d1f0683600d84920a724931d560d20cb67b1221a1428000254228036a208c3549f040d989fa00016f21df80000001b761c50b16762a1121ed9dd45a820ae3bc095220c8d4c0cda13282d11d450d1de68b613d266094f40581fda1e78b8661e8a6404a83f416994fe8828d706cc05fa15f02d46f5000012d212045294386e88fa43848000367902637094707db93662118ee431b11b04d000003f99ff02418ec036404da62e006419500000f20502
  | 33 => 0x57f1f4c63c00c034900005de20883eb13ce61486e63ff86566ae84cc66216403260000000167200002200001b6a84d0000000000000011164b78000000119060020ee00018a200009e2299800019d006c3d5800000000007e0196c3fc9d4623c9b2829680000001b500000cc800000006a310aa3180bde2e480004f6800017980005a58ee03ca8750083843443d1342000035c76400000000eec7c5090460600006dd000073b00a6472217283d0d120d79cc02880c0800000006b70bb47eb8e2a43d83e40d1942200011de0000cc400020021d495881b0873607a19a218f80004389e7c442055441480006f880000001b960f500002bb800024d96587f900001670000000065e44a917a000000015617903e693c837298846278aea067983e2f413d47c69e8200018ae55380005f08b822c9810488d1ae28238078817074a3ba8b0019909f8470801015e829606d064067587e2176a1467238c4e671800062586c65d2909207e01ee5e9223a2ca0f845ca97cc1d0882416a0dcc81287f284b1f8c86d09ca29389c001f8e046f60f048af118a83a8cd4290a06e3a49c7407c18e22ec82047911f0c2f80890357005c880833c473a1f864b1c80231154215b9e285cd88d81ff9d0a09b89966d2a24841c88dc532195c4308af820b000039d98c05da080252e9b608789d7200097f82f898e41c299722b3813e53a86a07f8a0d060c1e5a1a41e1e3d8a1d020f928422e93345fb16dc84a8dce21f8d4258507a041da08a16d80b05bc16b054292ce00014ce6a2a1bc7ed9dec8098fa653100000001e302d19ed83118afa4ac0f7a7d6938e85683441f988ae618889654d8abc5718f1815908662e88b501151e7e55700f24f7161e1ee15f453b016204e85606aa97524961e2e1d68cdc0911712098075c13d97ba64f21c64f795ca5d210a44051cbe1760000756000000017b85929fd400014b061117f244c8ff43d9954449fa0846941a104b608a0000145e3ca000008d8f500d403d671a026426b8000000053c00005780000000250000088c026600300000c8193e50690782b294b84f911a429880008a391ae5ed98f2817978051218fe5f78f023a608145eb013875a0dba22a90d840f066667602f20000e8a8181c7239b009c56022e000016e2188a16662602b8000000000006840000de20a293601fd13cc00015d02ae80003629228465224c00004f000002881540c5e2e01f620001c0c1528ebe46481320001a0e00006be830a19824980004d78c6a7ce000000000006600d4a41721184869bfe1c7911e21a04ca00a9ae620f14a6062000060b879000020801dc89ba55800000bd800034e845c000000000000007d99894116014256510a061d1cb663b0ac85df94fa88f86ec4eb800000008f46fd8e3474009b4815197a3fc00003e820066581ee47e8
  | 34 => 0xf80006f706bc39e1eda2748dc825d0ba60000522893855e28006e84ad8000334908c5f2000000009e00bd20a600011120000d504e19d12000155e51400000001b0449c00008a8157c10f01a0801165200000003221b9269c922c7cea0a004495a287d9f22275011456d97380001f763e51e204b00b9424805ea6e511bc000000000006fa631923c41509b23339c064fd1fa400005de8be0df886989984d597246420e520001524000131c638094884080004d3a3046508b103dc0f3e2588c6812a8c1e4d91cc44139a080f710b4443167807f928a37d12b818d0000819957a1c900004b90e842f722cc73200a25849f7c10e16488be863c295835a6a421644da097e5438b90433800003421da000000066b9c244b486ca1790000267021007c90ca0a99a2c6ac00005a993501189f4857597446f406d20608c843e5891233411fe4799b6e3cb048619480008028d0c8328b1a7ef14f22171ff44219760002008c4c90b6c538846c44e933a8b79acc27d85444a5848e16f8000000120616395be00000005ae018460821c44e9200e51599dc5da8000000097044b09e4641071a14a9e48327975800d14d41341eac7fd80006140ebc188073c5368cae8ab932e7fa80660e3146c000089e3c4000017512ae48788222028bc61b1099e1290536268033402682782fda2c060c9e3e80f0208598a27c00008fe8131fc435b96e05cc171482d89a638b226000011800001336773212600003d81ec86ac3e602ba1bb809e61ca10a2ce82c839c8a24000083615596ea18181800ec804478898c413e852632291c000015020001826219154836897e40001f9c000176649800007f39f60204800079c0482389000026f000081e8d8e626800038d915028c98801739022862801a6f81bda482800065b80007e995c8000008856183ea45880006549b108bf8d060001db600015b019d89f20000cc65f1816600008f87f61ce25a7820287607d04558a0e0b400004ba82984a383101aa870c5af000056b147e28b80006cd000000009ce00014a0472924e57c888857612d4000119e25a0b340001d2834c8aaa0ea000000018a68aa8c384d5170202b800000006b24c2000082a0a7600010cc7a8884e00009ee65f0f4a2ef946e0000c107a001160dd178e14812145df0f6e2860a981c886184e48aac75c1b9e50b099a1bc02ce52ca156783800002c8f165559a5e53e05ae000222031e9c3e37f9b206fc80e05a313b060d0cbe02d218649992100001eb848200004711e6a2e3a1684c59db85469c847fe8ac68bb81b66caa0fe5a2225246d000040e89c458980008379ab82a916b46101a1606c8322112000029e10d400010d04761e74000108e0000a9e23b00005ba000027d07c036709ec39f09247d4127200000000000000000187800008841e18ea8000000061c000
  | 35 => 0xe80001ad275e00004660000446000000017c04dda1c204803400b097ce7ab87387b802d80ad83943908e96069000057990842061f7a28d8c02105866283c1e1c4450c56601889a2471f8e5e801fc3a9888e85e9506227204e06a1b8874d8eac16d0a5245a8f600af97d00000000739000053a06ce5a180746c30000000122e8a080007191e8616a82ea1ac05303dd80003b98ef6000084c0000de00000c70718800000000004b6800058b00ac5f287dc1e5900a41418f83461a604cb19ac37c07567aaa16273590d23899d0273814a88418f0627782b26c1a0e060118da38f00001b407823ce80d40e88d7800013126aba2f2481108a2a4815e49e80000a40f5864e9ba60001ca45ada13a78e84ec87e83ec00021b2000111a3958dbe85c14086090f9200014f60001aec6440b0e1fe117c0d399fe51a16be72d1e9a095944c6c59f524fa088c854a26c52580001cb20cc7158e1609c9fcc75795a846a800037490482cc95b879a06f854c92d01211cce38a03c012498a806293807720bba2d080006568000868800026280005d585ca6480f082df172c2fa8f5a70784b00908ffa0a8a1ec028016a645218c8ac1122283110603b8000494885a12e04361caa09215700002010adc81a8b1e0001cb22a1066c24e00004c1023c5f6071c12404940000ea237900000e00aa000003f60000000012918c8959bc828510081f680004e283c4509962088780000001776000102859b10101da128c42c088000004d400015da09c1b52021890a4f090f209d08061ab90942af9e903ada2e47b708f00ca1c22580814404d8d565b4046883c9b5e0378ca070683f862c829a2bd80000000b2c848981a6129ec847821903f68b4e02085923ba0bbc5189a2e1e687a643c1a0034080003799c441028cee505225e6e080006d998543609a486cc8d60000125c7710b066f307a80771c262cb800030b901228f2246000000062d130030f1b7c00014a269aa0787e69d0c0000ed8690858a58e137a84e22d612b15ec18c960c00017a6713800057d9f72745a04200016ca00000008890e607511dc04dd09c6436955046120ec8218c586dc0eba6fd1d1e3a6a036444000030c0000212095c82f9b1813b9a622771eee52010ee04797e83a90d7c47c17be0dd9d603511ca80ea9dca8c0a2623b680002488a165919b22827000060201f42f3944a46685d211a9d7c24ba2283d3202003a0a7c25787446e2a0a27b791544fe9a1e7491de268689cc83008ca4cf16643458c80535896053900aa8350c8e3ac943a33c842052900be293187674e0dc6524923e7738d225778a887651d747e780fe68a945839f980e2da17d445c9c3056c849865422ac41b20c4790079401a03bc5b6065c64c1b0a77c8a0600009584b59cf477e9f1c11680000af19c82528000000000020a83fc4b
  | 36 => 0xe00d8000000007a90000287000000000007a51f9417104805150000004849c52514300f4000054b01340e4000056d079214515a40000000000000051d15120000dae4da931810103c2661129e3b4100071d9d5a21b18ba7011166000011087c9a8853c00002b6868e6f793f23c894b65b99c1816904d81ec00000ab0b6673096560001ca0000003c79b0a1e19421b037f090839216366fb20280870fe045181941909a7c00001967ac956c27f800012e802476a92a00001c2873f0bfe15385847dc0000000000018d98824568000336928614113c40000d40000000080416985d39fba8491036688001809188b04410dbc748999875d8000000021244d00008a580000000d881f59f8400014e656ea0160001f2449d215004f00007cc8bc0082a29e0669c3c15b04566a105dc00003fa73a80000001a941460fc23630318894000068d802c4df800057b80000001a745ab1b6c784800071c0694676905a1d9073a3f309465b48ff835d88ea45d800075ba0460001a0c5271c8c479000a7270000000190a7cf02ae000000000000003f200006b900007c4142a000000067000001869c4200004460000b5673c80007081514000115c5d09ecc75f99f02c721e462c03163aa8000697035400016f680b1a0289d878801c914254f08bc0418ca400020244429584589001e45f8ba4739a18263ea0bc29f862e3ce0bda3fa04e40571ef20000000000168461a076626f80006f98efc00020324b216c02d820584e3085871b15f8000036e1f50000630836a0ef888a0001ed20f696ce00000002348d967ba834271f03a468113ea5f119e24bc09b684f9c52530147a4ee9efc776959a48a95c44e215043209d3a5a29c860a30e5a6520b8456a8b7635680001a19ed02a69c2a2821a3257e93a06be16ec73e87ca771945a5e08e68767014007b1ab62919de07ed0834180189c2eb81c0140123805f80006628628310202e036a1141d617500001a9c000123400b8cc2667126c10c80cc11c0a8066e0b880aa10246ea897807680f86158c363a3800000016a483e838e2640a6c7a582b05518fd8166817480e0eae653159c2d5206c3a199e42ce09420ff8ec815496544ea9c2c4a41b9c31222b40e0a2543219b4e0001b2e3838fb6000078e56f10e43e706608798a8230b02a479805f8890000068f8ca6090199405508ee81f88e85c98eb83b700000001b68664140254a88be3170a3e63d01984131d1a00000008b3a1a0857157e000118e69d80000001a3c7150fb80000000000000003386cc0000b3c77410a2000000000004ea3ec00007328c0064c800000016fa49e000036c04fe1f4800017d87f00001b725cd1e003d51cda000167441d00a48b282063fa90fa63a1e1a377023a0000e207e2000073c10c049780000000ed617304d635b00005b3000032592
  | 37 => 0x141839c00000001476641980a0310fdc355185800009001b7139434a1f4488a8a28353912076c10381e8865a7e5956400005085e6089400013f83988f486e007021a09c96574847655001ce85505d62338e5065c1e101660d8680787f65478f0034d07ec3a511c649692c202f13064d18dde70d96505e31ada569800006f80000001b9a12f09563fd9c9e1cd2176896044a3c900006a7a20e03a800011e1e468ae08cc35a8a548a6983645b9f020db13144ad000066e97f08a41ce834f95548b41c0000000706ed8dd67fb17e6695824e60e049a49880000001f5c1bd0e64111122405e8000000000071e92c48ae9c5c52d09d02aca1f02ad1a187240e440370bd46c995fe19c15963bf9c7831c8566167862411085483649f0824e99964d608566f08be42c21d7a77a86a80e596280518e1e31b800010692f85cf800000001b04c0800000004a8000000000000004b8179c50d8a3863480008580f4200010e8000031a57c0f8c72b8000318800000016704859af60d499f42ac0692820896485f034a508000067e163c46c80003da0ae800000005bf80000e80f1a8af9e784788d5e1c2159e14b1ed4624137c1e7185a6888aae4d2000012d800005280001f18000000138287380008440982577042c7e489b016c830e6928030000166a3cd906200020d23711692000000000005105ae950c852893000002c053081d80c4a0a40d808542fe82ee85a84526d8881a32e000008b84e247a17dc5ab857e6bc05bc4201d8e52f1728015900e0b18cf85c29c1633a92125e582503b5000065394de00000000000ab6808800010600007bf8f3c47c96905a51aa0368012444f9fee40089944278f6c30a99380001f4e32b0a1002417624e9959008d106e66796d6000041213993283440f520c214904530f1c33b0bd859f04e8734a2a4217819c00e0ae27cb8a26483132a4c6952e2c0902e04a18023b49534760830208e227462f116440a81a22b4211c00020e64bd000058000006d108208369f20108800018b204406a80002108f644a0024a7db0e22850092800000006899dd61fe9406000028e0000d2c7470caa64605868188000000177a2a715e22f28258000000000014cc63981307caa2da5d780004aa000013d159267a096c3841676000000005302a01ed1fca000045e74d14ac588875441281ea1f800003
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf51545453044085ea0a8a8a6088002f4e09514c110217a9a92a29822000f52525453044001ea2a4a8a608810bd4149514c110007a9c3aa29822000f52875453044001ea30ea8a6088003d421d514c110217a9c32a29822026f5286545304404dea30ca8a608809bd4219514c110237a9bb2a29822012f52765453044025ea2eca8a608804bd41d9514c110007a9c22a298220d6f52845453044001ea308a8a608835bd4211514c110007a9ba2a298220d6f52745453044001ea2e8a8a608835bd41d1514c110007a9b22a298220d6f52645453044001ea2c8a8a608835bd4191514c110007a9c12a29822000f52825453044001ea304a8a6088003d4209514c110007a9b92a29822000f52725453044001ea2e4a8a6088003d41c9514c110007a9b12a29822000f52625453044001ea2c4a8a6088003d4189514c1106b7a9a12a29822000f52425453044001ea284a8a608835bd4109514c110005e943a829822000bd08750530440037a50ca0a6088006f4219414c110005e9c2a829822000bd18550530440997a708a0a608804be4e11414c11020fc93a2829822000f91745053044001f26c8a0a6088107e4191414c110005e9c12829822041f93425053044001f2284a0a608800374e1d214c110005e943a429822000bd0874853044001ba10e90a6088006f4a19214c11000de8432429822000bd38548530440017a30a90a6088002f4e11214c110005e8c22429822049bd3824853044025f870490a6088003f09c9214c110007e0b92429822000fc3624853044001f80c490a6088003f0909214c110007e0a12429822068c7876dd520440cd8f0ec3aa4088002dc6047548110006d920ee890220028f8865d120440016d30a3124088002ea6106248110005d4c24a49022000be18194920440016d30b2124088002f86064248110007b1292a29022000f61525452044001ae70ea8a4088002dca1d5148110005b843aa29022000d70875452044005ae4eca8a408800b5c1d95148110006b9ba2a29022000d717454520441abae6e6a8a40883575c5cd5148110007b1412a29022000f6182545204404dae6e4a8a408809bd8dc95148110007b1b12a29022000f60625452044001ec484a8a4088003d85095148110006d8ba2829022000fa14250520440035e10c90a408800b3c1d9214811004f70312429022001be0874852044005bc10e90a4088006f8a19214811000df0432429022009ee0864852044013dc6ec90a408800b789d92148110016f03b2429022009ee07648520440017c70a90a4088002f86152148110007b1baa429022000f607548520440017c70890a4088002f86112148110006f1ba2429022000de1744852044001f870690a408834ff020d21481106a6f1b9a4290220d4de17348520441a7dc6c690a408834fb858d2148110
  | 1 => 0x6eca0a808800b6c9d94150110016d83b282a022004eb07650540440017670aa0a8088002ec615415011000799baa82a022000f307550540441b7b66e6a0a808836f6c5cd4150110005d9c1282a022000db37250540440017630890a8088003e85092150110095e840eea9822000adb865d530440255b10cbaa6088002f4e05754c110095e840aea9822000b9b84595304408373108b2a60880a6f4e05654c110095e840ee89822000adb865d130440255b10cba26088002d6e15744c110215ac42ae89822000bd3815d130440257a102ba26088002d6e15644c110215ac42ac8982204bbd38159130440015b70caa26088002b6219544c110095e940aa89822012bd081dc930440255b50d3926088002b661a724c11007e6c3b4e49822012bd2819c930440017a3033926088002b6e19724c1100956c432e49822000b5b855c930440856b10ab926088002f4e05724c110095e840ae498220daada861c9304400d5b30c39260881ff361d8724c110215ad428e49822000b59851c93044083735083926088002e6610724c110006e4b90e49822012bd2811c930440017a30239260881feb6a1f624c11041d6c43ec49822001adb81d8930440035b303b12608836796d47624c1106cf2ca8ec498220d9ecb21d8930441b3d9243b12608806eb661a624c1100dde8c0cc498220009db87589304400d3b10eb126088002d6e15624c110215ac42ac49822000b9b84589304408373108b12608807ef4e05624c1100066dc3ac49822003ada8758930440075b10eb1260880033621d624c11001c6c43ac49822000e5b855893044001cb10ab126088003a6e11624c1100074c422c49822000ecb82589304403f5b702b126088003b4e05624c1106c72da8ac498220d8e595158930441af3b50e312608804a7661c624c11024d6d430c49822042b5a8518930440016b30a3126088106e6a10624c110005ccc20c49822000ada8694930440015b30d2926088106e6a12524c110005ccc24a49822012bd28194930440017a303292608804af4a05524c1100056d434849822000ad98690930440856b50b2126088002d6616424c11000764b14849822012bd28190930440017a3032126088003b2589424c110095e940a84982207bbd287dc53044025ba50fb8a6088006f4a1b714c11000de8436e29822012dd276dc53044025ba0edb8a6088002f4617714c110005e8c26e29822000dd374dc53044001ba2e9b8a6088002f460b714c110006e9b96e29822000dd172dc530440017a50ea8a6088002f421d514c11000de9432a29822001bd086545304409f7a70aa8a608804bd4e15514c110007a9baaa29822042f52755453044001ea2eaa8a608810bd41d5514c110007a9b2aa29822042f506554530440017a708a8a608810bd4d51514c1106b7a92a2a29822000
  | 2 => 0xd621891000656ba2c43122000c3e74d9652440031e90cb8ca48800a3e21970949100043fc2aeca9220008bf845d9524400917908bb2a48800237e0d765491001c6e41aeca92200987c87595524406f47908b2aa4880263ba0a76909100061f3aec92122004aac8458a42440031e90cb8c848800a3e21970909100043fc2aeca12200587c855d9424400117f08bb2848800237e0d765091001c6e41aeca12200587e851d942440010fb0a3b2848800e37a0c76509100046ec18eca1220098bc87591424405f4790ab2284880123b21d6250910014bac2ee8a8a2047d3654dd15144001b6481ba2a28800a5da1e525451002e3a3b4a4a8a2047b3684949514400166b09292a28809adca025254510005b8c04a4a8a2026b7080dd15144001e6481ba2a2880029de1974545101353a432e8a8a2047d34745d151440016e700ba2a28809adc20174545106ef1b326c8a8a20009778759151440112e90eb22a288136dce016454510135b8406e4a8a2026a76869c951440014eb0d392a28808b1d1da725451023d9b424e4a8a2000b35849c9514404d6e501392a288002dc60272545100053bc32e4a8a2026a74865c951440016af06b92a28811ad520d7254510005b9c02e4a8a2026b70805c951441818e8ec392a28809adca007254510005b8c00e4a8a200bb718098951440012ef0eb12a2880225d21d62545100059bc22c4a8a2047b348458951440016af06b12a28811ad520d6254510075b9c02c4a8a200097687189514404d2eb0e312a28811ecda1062545100059ac20c4a8a2046b568318951440016ab06312a288003995886254510004bb43c84a8a200097587909514404d6e501212a288002dc6024254510135b940284a8a2026b7287dc1514404dae50fb82a28800adca1b7054510015b8436e0a8a2026d7276dc1514404dae0edb82a288002dc6137054510006b9ba6e0a8a2000d7174dc151440016e707b82a288002dc60f7054510005b8c16e0a8a2000d7372dc15144001ae2e5b82a2880063d2197550510004bac2ee4a0a20018f4865d521440012eb0bba242880036c903744851000c7a432e890a20adcd476dcd214400174b083124288002f160c6248510005f0c048490a2000ae486509214413b8f0edbaa808826f1e1d87550110005b8c08eaa0220009d983dc9404408fe64a8a8a8088003cc5515150110006b9c3aa2a022000b728754540440016e10ea8a80880035c21d5150110016b93b2a2a022002d7076545404408fe6508a8a8088003cc6115150110136b9ba2a2a022026f33745454044001e66c8a8a808811fcc19151501106e6b9b9aa2a0220dcd71735454044001ae6e4a8a808811fccd09515011000798a12a2a022001bb0875054044005b610ea0a8088006eca19415011000dd843282a022004eb0865054044009d6
  | 3 => 0x29824000f4872d453048053cb6c5a8a60900a7d2d8b514c120007a5216a29824000f4942d45304804d6b303a8a609014f96d87514c120007a5292a29824000f495254530480016b50ca8a6090002d6219514c12013f2dbb2a29824027e58765453048001e9504a8a6090003d2609514c120007a5b92a29824000f4872545304804dcb6c4a8a609009bd2d89514c120007a5212a29824000f494254530480536b702a8a6090157d4e05514c12029f2db0aa29824000f894250530480017950f90a609014af221f214c1202c5e5436429824052eca86c8530480a57970b90a6090002f2617214c120007a5b2e429824000f4865c8530480a57970990a6090002f2613214c1200dde4c0e429824053f4b51c8530480a7e92a390a609000276e1d214c120004ec43a429824000ed36148530480a5f804290a609000372e1d214c120005e543a429824000bc8874853048001b910e90a6090006f2a19214c12000de4432429824000bcb8548530480017930a90a6090003d2d95214c120007a432a429824000bcb8448530480017930890a609007ef2e05214c120297e1c0a429824053fc2714853048001f82e290a6090003f0d85214c12029fe030a429824053f4b5148530480a7e92a290a60900030f5d254d95100053ac0ca9b2a2000a798095365440070ff0ea9eca880034d54774595100245f43ee8b2a2000c3f51dd1654400187aa3ba2ca8800327cc374595100064e986e8b2a2000c3f751d1654400117f08b9aca880122f211735951000477c12e6b2a20098ec825cd654400187aebaa6c888002ad60754d911001c5fc3a87b22200087f855cb644400b0f90ab96c88800237e0d72d911001c6e41ae5b22200587e87dd564440010ff03baac8880021f60775591100062f986eab222000c5d30dd56444001878ebba2c8880021fe15735911002c3e42ae6b2220008ef825cd64440131d904b9ac8880021fe1576551100045fc22ecaa2200487c87595544400947908b2aa8880022fe1175d89100245e422ebb12200087f855d3624400b0f90aba6c48800f369cd30d891002c3f43eeab12200087f81dd562440010fb03baac48800317cc375589100062e986eab1220048be87dd1624400187eebba2c4880030f1d774589100061fa8ee8b122000c3d51dd1624400193e61ba2c488003274c374589100061fba8e8b122000c3c751d162440071bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317d4773589100062ea8ee6b1220008df80dcd62440011bb01b9ac4880021fe15735891002c3e42ae6b1220008bf845cd624400917908b9ac48800237a1c73589100062fba8e6b122000c5c751cd624400193ee839ac488003271d0735891000c7d43ee0b1220038f8874c1624401395cc4ba0c4880023be1
  | 4 => 0x480015b70cba2609014ab6219744c1200b66c3b2e89824000b5b855d130480ab6b10aba26090002f2e09744c120295e4412e89824000b5b8559130480ab6b10ab226090196f2e09644c1200056dc32a89824000ad88655130480075b70db926090006b621b724c1202966c3b6e4982407ebca87dc930480037950db926090006f221b724c120296e53b6e498240e1dc876dc930480017930bb926090003d2d97724c120007a432ee49824000bc984dc9304800179303b926090206f2a1c724c120296e5438e49824080bca861c930480a5d950c392609014bd2a14724c120005e4c28e49824052f49851c930480016930a3926090003d2d94724c120007a4328e49824052f8a841c9304800179308392609014be2610724c120005c4c20e49824052fc2811c9304800179302392609014bf0604724c120005e0c08e49824000bca8794930480a57910f2926090192f2a1a524c12029765434a49824034bc9859493048001e96eb2926090157d21d6524c1201c7a5b2ca49824055f486594930480a5f15092926090002f2612524c120297c4c24a49824000b898494930480abe96a92926090003d2552524c120005e4c0ca49824055f4b5194930480a5e90a4a926090002f2a1d524c120005e443aa49824001bca8654930480037910ca9260900e2f2e15524c120297a5c2aa49824055f4a755493048001e92eaa926090003d2d95524c1202afa432aa49824000bcb8454930481c1e94a8a926090157d2151524c120005e5c0aa49824055f4b5154930480017950f212609014af221e424c120305e5434849824052eca8690930480a57970b212609014bd2a16424c120005e4c2c849824052f498590930480016930b2126090003d2d96424c120007a432c84982402cbc984909304800179303212609014be2109424c120005e543a849824000bc88750930480037950ca126090006f2219424c120005e5c2a849824000bc9855093048001e96caa126090003d2195424c120185e5c22849824052f8b8450930480a9f14e8a126090003e25d1424c120007c5b22849824054f886450930481bff16a8a126090153e2151424c120005e5c0a849824054f8b415093048001b96e5b8a6090002b6e19714c1202956c432e29824000bcb825c530480a579104b8a609000372dc9714c1200072db2ec29824000e5865d8530481bd5b50fb0a60901eab621f614c1200072dc2ec29824000e5885d8530480035b305b0a6090003b290b614c12000764a16c298240d8ed221d8530480153b10eb0a6090002d6e15614c1202adac42ac29824000e5b655853048001cb0cab0a6090002e6e11614c1202a5cc422c29824049bcb8258530480016b50da8a6090156d621b514c1201572dbb6a2982402ae5876d4530480abe9505a8a6090157d260b514c120007a5b96a
  | 5 => 0xa3d20573591200043fc2aecaa2400487e87d95544800947d09b2aa8900034bd9574949202f69632ae9292405ed2f515d2524801395ec0ba4a4900276ad817494920006c7982e92924000daa305d25248001b1a60ba4a4900036a4c17494920006d5082e92924000a6c8655252480718f0e1b2aa4900e31b1db655492004cb6c2ee8a924062d2e54dd152480012df02bac84900271bd81759092004eb5b02eb2124000d4f305d64248001ad460bac8490003534c17590920006b4982eb2124000d6a105d642480012df0fb2c84900025b61c659092004cd6c26eaa12405ed2f54dd542480031d90cbaa84900e31b1db6550920326363b0caa124000a7581dd761480014eb023aec2900021fe1574d852002c3e42ae9b0a400087f855cf614800b0f90ab9ec29000f369cd30d85201c43e436eab0a400087e87d956148001878e9b2ac290003171cf65585200043f438cab0a4000c3c7419561480018b8e632ac2900030fd9774585200061e32ee8b0a4000c5f65dcd61480018b8cbb9ac2900031bc8676d45200063690ceda8a4000c5f309db51480018ba613b6a2900031e84276d45200063c884eda8a400087f87593514800b0f90eb26a2900025b61e42d452014d3643285a8a400587c851d951480050fd0fb2aa29000a1f21d6554520006363b4a4a8a4000b2d84949514800b4d90ca92a2900021fa1a76545200053ac0ceca8a4000c75819d951480018be613b2a290003174c276545200063b884eca8a4000a3f845d9514805147908bb2a29000297e0d765452013d2e41aeca8a4000a77815d951480018db043b2a2900161fe04765452002c3ec08eca8a4000c6f211d951480018da423b2a29000317cc076545200062e980eca8a4000c77101d951480018f4203b2a2900031d44076545200063c880eca8a400087f8759151480010f90eb22a2900031b1da725452000596c24e4a8a4000b65819c9514804d4d90cb92a290002d9e057254520004b6c3c84a8a4026a6c86509514800b0fd0bbb282900021f61776505200145e43ac8a0a4000b658119721480018b8e7b2a42901a39908765485200062fb2ee690a4000c5c65dcd21480031d90cbaa42900e31b1db65485200073230eca90a4064c6c7619521480012db0bba242900063b21974485200147643ac890a4002ae4815912148159998edb9a4290002b6e19754c1202956c432ea9824000bcb825d530480a579104baa6090192d6a1b654c1200072dbb6ca9824000e5876d953048071e9705b2a60900e396d8b654c1201c7a5b16ca9824000b5981d9530480cf79704b2a60900e2d6a18654c1202af2d430ca9824000e5b761953048001cb0ec32a609000396990654c1200072c320ca9824064f498219530480c9cb6c432a6090193d2d88654c120005acc08ca982408acd876dd13
  | 6 => 0x46e432e890a6000ccc76989214c001d8cc3312429815af26026248530094e643ac490a6000ccc76589214c0d379700b124298002f26024248530094e643a8490a6012bc481509214c0a53a90eb0a4298003b15896148530715e9c02c290a601cad8865c1214c0019b0ecb8242980261fa1e54597200061fba4a8b2e400987c8754d65c801317d0faa2c9900030fdd7545932004c5e43a86b26400487d85dd954c80031dd05bb2a9901c74b9537454b2037697aa6eaa16400587e85dd161c80010fb0bba2c39000e37a1f73587200062fa8ee6b0e4000c5d51dcd61c815b9b441b9ac3902b736483735872056c6f438e6b0e4000ad9801cd61c80131e90e98ac39000a1f617765472000c77416eca8e40008df835d951c80071b906bb2a39000a1f21d655472013537416eca8e4000a5f835d951c804f4b906bb2a3900029de057654720005b3c0ae4a8e400587e85dd941c80010fb0bbb283900063ba0b76507200046fc1aeca0e40038dc835d941c80051790eb2283900025b61774487200157240ac890e4000c3d7495365480014db052a6ca9000e1fe1d53d95200052f41cc9b2a4000a5d83993654800147d0931eca900028f61263d952006c3ec38c3b2a4000a3e84187654800147b0830eca9000297a0c61d95200052ec18c3b2a4000c757118765480d14f10c986ca900030fdd274d95200052f41ce9b2a4000a5d839d3654800187ae83a6ca901a29ba0874d95201c536c10e9b2a4000a3e849cf654800147b0939eca900e29ea0073d95203453cc00e7b2a400087e8710f65480010fb0e21eca900e21fa1f42d95200043ec3e85b2a4000a5e83d0b65480014bb07a16ca9000317cc171d95200062e982e3b2a4000a3e841c7654800147b0838eca9000297a0c71d95200052ec18e3b2a4068a6e821c765480714db0438eca900e29ea0071d95203453cc00e3b2a400087e8790765480010fb0f20eca900021fa1c41d95200043ec3883b2a4000a5e8310765480014bb0620eca901a29ba0841d952000536c1083b2a4038a7a8010765480014f30020eca900021fa1e31d95200043ec3c63b2a400087e870c765480010fb0e18eca900028fa1031d95200051ec2063b2a4068a6e820c765480014db0418eca900e29ea0031d95200053cc0063b2a403887e8788765480010fb0f10eca900021fe1573595200143e42ee2b2a4000a5e8399065480014bb07320ca900021f61e63195200051f424c632a4000a3d8498c65480010ff0eb18ca900028fa1061195200051ec20c232a4000a5e8318465480014bb06308ca900031d5c461195203353c4326032a40038bf8750f64480010fd0fb2ac8900021fa1c655912002c3f43eeab22400087d81dd564480018be61baac890003174c375591200043fc2ae6b22400587c855cd64480011ef02b9ac89
  | 7 => 0xdb805d9514c02733d083b2a298002676107654530094af43ecaa8a601295c87595514c1cd6b700b2aa29804a5761774545303a68f2a6e8a8a601295c87551514c027a38e8aa2a298002d6e015454530135ac402a8a8a601295e87949514c0e963d09292a298002c76125254530135ad404a4a8a6000b5980949514c0252b90ea92a298002d66037654530005aac0ceca8a6000b1f845d9514c0e963908bb2a298002d3e097654530005a6412eca8a6000b57815d9514c0016b700bb2a2981d2c7a1076545300058ec20eca8a6074d1e74dd1514c0e9a38e8ba2a298002d5e057454530005adc02e8a8a6026b58805d1514c0012bf0eb22a2980025721d645453072dadc02c8a8a6074b1e849c9514c00163b09392a298002d56067254530135ad404e4a8a6000b59809c9514c0014bf0cb92a298002972197254530005abc0ae4a8a6026b5a801c9514c0016b300392a29816ad66026254530004afc3ac4a8a600095c87589514c0d76b700b12a29800257a1c6254530004aec38c4a8a6074b1e84189514c00163b08312a298003935886254530095ab408c4a8a6000b5581189514c0012bd0f212a2980025761e4254530135ad40484a8a6000b5980909514c0013b301bb2829800257e1576505300a4ae42aeca0a60009cf825d9414c0a539904bb2829800276e0176505300a4af428eca0a600095d851d9414c0013b700baa8298006762017550530094ce43ac8a0a60e4b9b80591414c0292bd0bb928298002576177250530094ce43a84a0a60129ce829db214c0033b1013b6429800257e1576c85300a4ae42aed90a60009db805db214c0a5998ecb16429838ef2e0162c853001ced432e190a60039d8865c3214c001ab70ab8642980035621570c8530296e5212e190a6000dc9425c3214c1b1ab6a2b8642983635654570c8530296e910ae190a6052dd1215c3214c0013b301bb24298003369c376485300062fa8eec90a6000c5d51dd9214c0019b301bb242980033688376485300066d086ec90a60008de869d9214c0012bf0abb24298052572157648530004cfc22ec90a601399c845d9214c0013b700bb2429805257a147648530004aec28ec90a601399e841d9214c00133b083b2429800317a1476485300062ec28ec90a6000c9e841d9214c00193b083b242980033360876485300066b408ec90a6000cd5811d9214c0018bea23b2429800317544764853001c6fc00ec90a6000cda801d9214c0071bb003b2429800336600764853000667900ec90a6000cda201d9214c00199a403b2429800335c4076485300066d080ec90a6000cd5101d9214c0019b2203b2429800676a037548530004ecc06ea90a60008df865d5214c0011b90cbaa429805257a177448530004aec2ee890a60019da80dd1214c0013b301ba2429800237e1974485300
  | 8 => 0xe0b10c4983b7b2841621893000666b12e23126000dd2105c4624c001aad0ab88c4980035561571189300066bb22e23126000cd5645c4624c0a59aec4b88c49814b7198971189302966ab12e23126000dc5625c4624c00198ac4b88c49800374a017118930006e8c02e231260eacd7605c4624c001ba6c0b88c49814b71c817118930296e9102e23126000dc5205c4624c0a5ba240b88c498003355c661189303be6cb84c23126000a9d84184624c00159b04308c498003355c461189306f66cb80c231260019d8809da524c0013b700bb4a498003479d365949303e68fa8ae929260eac9f605d2524c001b36c0ba4a49814b63c817494930296cd102e92926052d99205d2524c001b3420ba4a49804e57e1d549493009e8f3a2a92926038b5880552524c0033b500b8ca49800e76a19709493001cec432e12926038d5b855c2524c071ab10ab84a49800356d957094930766ac32ae129260ecd5b545c2524c001ab2a8b84a49814b56d497094930296aca92e129260009db815c2524c1d9ab6a2b84a498002766037654930004afc2aeca9260009db805d9524c02733d083b2a498002676107654930294ae43acaa9260ebb5b80595524c0a52bb0bba2a4981f747953745493014cae42ee2a9260019d8809da424c0013b700bb4849800257e0575909307562fb02eb2126000d5b605d6424c0a5a9e40bac849814b568817590930296ac902eb2126000d5a105d6424c0033b500b8c849800e76a19709093001cec432e12126052d9b425c2424c0a5b3284b84849800276e057090930296e590ae121260009d980dd9424c0012bf0abb28498052572157650930004ebc0aeca1260129d4815d9424c0013b700bb2849805257a147650930004aec28eca12605299d84dd5424c0f9a3ea9baa849800276e01755093000cec402eaa12605299c87591424c001938ecb2284981f2c72156450930295c6412c8a1260e9b9b80591424c11b3b700baec2980067620175d8530004afc2ae9b0a601495c855d3614c10f3b700ba6c2980067620174d85300946ec3ec9b0a600095f855cb614c0292b90ab96c29803e76e0172d853000cec402e5b0a60128dd87d8b614c0011bf0eb16c29804a3721d64585300956a40ac8b0a60008de87d89614c0251b90eb12c29814b331c9625853000ced43ee0b0a60e8dd371dc1614c0012bf0eb26a2980525721d64d453073dadc02c9a8a605cb598098b514c0012bf0eb16a2980525721d62d4530365adc02c5a8a601495e8718b514c0012bb0e316a2981d6c7a1062d45300058ec20c5a8a6000e4d6218b514c0256ad02316a298002d560462d45300a4af43c85a8a600095d8790b514c0536b501216a298002d660242d4530004ecc06eca8a600099f845d9514c02733908bb2a29800273e097654530294e6412eca8a60009
  | 9 => 0x76545400061f420eca8a8000c3d841d951500018bd063b2a2a00031760c76545400061fa10eca8a800587f811d9515000b0fb023b2a2a00030fd0476545400061ea08eca8a8000c3e401d95150001878803b2a2a000317cc076545400062e980eca8a8000c77101d951500018f4203b2a2a00031d44076545400063c880eca8a8026a3c865d15150001878ecba2a2a0002cde05745454013d2f41ec4a8a8000a5d83d89515004d4790ca12a2a00030f1d9425454000c5e432eaa0a8085c3c76d954150135878ec32a82a00024f61772505400054ec1ec4a0a80038de839db21500011bb073b642a000a3ba0a76c85400043fc2aed90a800587c855db21500031790cba642a00030f19574c854059f1632a8590a800587e85dd921500010fb0bbb242a000e37a0e76485400046ec1cec90a8000c5c73d9521500031790cba242a000317d9773485400062e32ee690a80a8e2c6550921500014bb0d2a6ca98003475d254d95307a6adbaee0b2a60138dd87d97644c0012bf0ab96c8980525721572d91300a4af43eeab22600095d81dd5644c0018bec1baac89800356d837559130006ad106eab226000d5a10dd5644c0298b8ebb2ac89800387953655913009c6e43acab226000d5b75dc1644c001ab0ebb82c8983cf66dd37059130004ecc06ecaa2600095f855d9544c0013b700bb2a89804e5721d6555130795adc02caaa2608cd5870595544c0293390eb22a89800387595645513078dcdc02c8aa26086d9870591544c0033b101b92a89800676203715513000ced43ee0aa260039da86dc1544c0073b10db82a8980027660b7055130004ecc0ee0aa260f0d5b51dc1544c11b3b700baec49800257e1574d89300a4ae42ae9b1260879db805d3624c0ef3b700b8ec49804e37e1d649893070ee4b86c53126000a9d84186624c00159b0430cc49805257a1f7558930004aec0eeab126000c5f60dd5624c001ab6c1baac498003568837558930006ac906eab126000d5a10dd5624c0a559d0db12c498006762037158930006adbaee0b126000d5875dc1624c1dfb96e5b82c49800257e0575189307562fb02ea3126000d5b605d4624c0a5a9e40ba8c49814b568817518930006a6902ea3126052d59205d4624c001ab420ba8c4983ab27d817418930006cdb02e83126052d8f205d0624c0a5b3440ba0c498003634817418930296cc902e83126000d9a105d0624c0271bb0fb20c498003175d7641893000566c16c83126000c5d75590624c02793ce8b20c49800273e1d6218930775e5c02c43126052acf87588624c00199f0eb10c49800393e1562189300072642ac43126052e4e75588624c0a5c9aeab10c49814ba39d1621893029746ba2c43126052ec671588624c0a5d8ae2b10c4983aab3e01621893000765c02c43126052eca70588624c0a5d92
  | 10 => 0x90aa0008dd839d921540030f90cbaa42a800e1fe1d53d95400051ec24a3b2a80fca3d8498f655002f0fb0e30ecaa000297a0c61d95400052ec18c3b2a8000a6e8218765500014db0430ecaa00031d5c461d95404ed1f424e7b2a80fca3d849cf65500014bd07b96caa00029760f72d954042d1ec20e5b2a800087e870cb65500010fb0e196caa02768fa1032d95400051ec2065b2a8000a76810cb65500014eb02196caa02169ea0032d95400053cc0065b2a8000c5f305c765500018ba60b8ecaa02768fa1071d954042d1ec20e3b2a8000a5e831c765500014bb0638ecaa00029ba0871d954000536c10e3b2a8085a7a801c7655013b4f30038ecaa00021fa1e31d95400043ec3c63b2a800087e870c765500010fb0e18ecaa02768fa1031d95400051ec2063b2a8000a6e820c765500014db0418ecaa02169ea0031d95400053cc0063b2a800087e8788765500010fb0f10ecaa00021fa1c21d95400043ec3843b2a809da3e84087655000147b0810ecaa000297a0c21d95400052ec1843b2a8085a7a8008765500014f30010ecaa03ef0fdd774595400043fc2ae6b2a800087d8798c65501f547b09318caa03e69e60263195400043fc3ac632a8000d37415c465500014bd06308caa00029760c611954000537410c232a8000a6d8218465500018eae2308caa02170f1db65551400062f39ecbb128000c5e7319762500018becab9ec4a00031719573d89400046ec3ce7b1280f8ad9809cf62500071bf0eb9ec4a000327d0573d89407bc6fc02e7b128000cda105cf62501ed87ae832cc4a00021fa1f65589400043f438cab12809bc3e7419462500011df0eb10c4a00262f212769494001c6f41ced29280008dd839da525013b87ce9b2ca4a00062f21974949400061fb2ae9292802fc3c655d2525000927f0eaa4a4a00168f21954949400061f3b2a929280038de839d952500011bb073b2a4a00030f950765494017e1e32eeaa1280018bc865d5425000337100baa84a026e8fa1b655094042e1e3b6caa12809ac3c761954250001c58cbb1284a00029d60775d85400053ac08ebb0a800087f855cf615000b0f90ab9ec2a00021fe1572d854002c3e42ae5b0a808587c86dd561500010fd0fb2ac2a00021fa1c65585407ae1fba0cab0a8000c3f419db515000187a833b6a2a000317cc276d45400062e984eda8a8000c7a109db51500018f2213b6a2a00aa97a0f62d45400052ec1ec5a8a8029a3c8650b515005f878eca16a2a00161f21476545400061f2a0eca8a80038de831d951500011bb063b2a2a000a1fa1f65545400143e43acaa8a8005a3c865515150001878ecaa2a2a00021fa1a76545400053ac0ceca8a8000c75819d951500018be613b2a2a0003174c276545400063b884eca8a8000a77815d9515004f4bd063b2a2a00029760c
  | 11 => 0x484011bd0f982c89080e3721f305912101c6f41eecaa242008dd83dd954484010fb0b3b2a89080237e0d765512101c6e41aecaa242008fb805d954484031f100bb2a8908121fa1f655512102c5f43ec8aa242008dd87997634840153d0932ec690802a761265d8d210046fc3acbb1a4200a5e85d9363484014bb0bb26c6908023761e64d8d210052f42cc9b1a4200a5d8599363484011bf0eb26c6908723761c60d8d210052f428c1b1a4200a5d85183634840153d08306c690802a761060d8d210066cb80c1b1a4200a9e849d7634840153b093aec69080297a1774d8d210052ec2ee9b1a4200a5e859d363484014bb0b3a6c690ab6b3a0874d8d2156566c10e9b1a4200e1f5495363484011bd0e2a6c6908023761c54d8d215646f43e85b1a42008dd87d0b63484014bd0ba16c6908029761742d8d210066db84e1b1a4200a5f855c363484014b90ab86c690802a7e1170d8d210054e422e1b1a4200c5f855c363484018b90ab86c69080327e1170d8d210064e422e1b1a4200c5f515c363484018baa2b86c69080297a1470d8d210052ec28e1b1a4200a9e841c3634840153b08386c690ab6b3a0870d8d2156566c10e1b1a42acad6811c3634855b5ab02386c69080237a1e50d8d210046ec3ca1b1a42008de8714363484011bb0e286c690802a7a1050d8d210054ec20a1b1a42adace82143634840159b04286c690ab2b5a0450d8d210056ac08a1b1a42008de8790363484011bb0f206c69080237a1c40d8d210046ec3881b1a4200a5e8510363484014bb0a206c690ab6b3a0840d8d2100566c1081b1a42acad68110363484015ab02206c690ab237a1e20d8d210046ec3c41b1a422fa3e85d91424855165d0bb228490ab3331db6350921566e238ec6a1242029e687dc542484053c903b82849080237e0d75d812101c6e41aebb0242008df835d360484071b906ba6c090802b660373d81210056cc00e7b0242038de86dcd60485591b90db9ac09080237a1f63581210062fbaec6b024200c5c75d8d604840193ee9b1ac090803271d363581210046f438c6b024200c5f7518d60484018b8ea31ac09080327dd063581210064e3a0c6b0242038bf8750f64540090f90ab96c8a80028f61641d91503243f436e4aa2a08587f855d362540011df0eb10c4a81a29be1562189504d43f436e8a92a00987c859da42540030f90cbac84a80061f219755095042c3fc2ae9b0aa00287c855d361540530f90eaa6c2a800a1f21573d85500143e42ae5b0aa02987c8754b61541350fd0dba2a2a80a30f19374545503243f436e4a8aa002a7487d85515400b4ef01b0aa2a80169d60361545507ef38386c2a8aa0fde5730d8551541fbcaa61b0aa2a800a9ea1b705455000739b0ee0a8aa00187c865d541540d10ff0abb642a80061f21975c855001c6f41cec
  | 12 => 0x803551cf7158951006b3b16e2b12a20097580dc562544052e903b82c4a880257a1f305895113cae43e60b12a200d5771cc162544510fb0fb20c4a88a30f9d364189510043fc3ac8312a20096f8758862544016cf02b10c4a88028f610601895100536c10c0312a259c3f429da42544b387a853b484a88161fe06769095102c3ec0ced212a259c6f219da42544018da433b484a880317cc276909510063b884ed212a200977815da42544018ef02bb484a880317cc176909512ce37902ed212a200c77105da42544012eb03bb284a88030f1917650951004afc1aeca12a22795c835d942544012ef02bb284a88025ee017650951134bc402eca12a25993e87d91425440187eedb2284a8b2a5de0574d8151014ba40ae9b02a22687d87d93605445187ce9b26c0a88021fe1d64d81511461e3a2c9b02a300977815cf60544052e902b9ec0a880257e0d72d815113cae41ae5b02a222977815cb60544052e902b96c0a889a1f61f62d81510043fc3ac5b02a22893e87dd16054401a6ec3ba2c0a880347cc374581510068e986e8b02a200d3710dd1605440187eec3a2c0a88021fa1f64581511461e3a6c8b02a22687c875916054451878e8b22c0a88024fe1173581511449e422e6b02a20096f825cd60544b32d904b9ac0a88025de0573581510043f43ec4b02a200c3c74d89605444d0f90eb12c0a88030f1d162581510069bba6e2b02a200d3474dc5605440147b09286caa0bff0fdd7745954101c3e43aa6b2a82038bc8750d6550401c3aa6a1acaa08161fe1d75d89410061fc22ebb128200c3c845d7625040187e86baec4a08ae1fe0575d89411443ec0aebb128200c3f405d762504018ee20baec4a08161fa1773d89410043ec2ee7b128200c3d7550f625040793ce6a1ec4a0bfb179d730d89410062ebae61b1282008ef87588625045187ce8b2ca4a080a2f21974949410043ec2ceca9282008df835cb60504071b906b96c0a08261fa1e54597210061fba4a8b2e420987c8754d65c841317d0faa2c9908030fdd7545932104c5e43a86b26420487d85dd954c840b0fd0fbaac19080317cc375583210062e986eab064200a75811d560c84010ff0ab9ac1908161f215735832104c7c43a60b064200ad98018f65484015b30031aca908030fdd2545952101c6f43ee6b2a4200c5f51dcd65484018baa3b9aca908023760373595210046f438e6b2a420387c8754d65484011bd0f982ca9080e3721f30595210062f3a8c7b224200c5d7518f64484015b30031ec8908161fe1d75d91212dc3fc0aebb22425987d815d764484018ee20baec8908161fa1773d91210043ec2ee7b2242fec5e75cc364484018baeb986c890802b6600635912101c6f43ee6b224200c5f51dcd64484018baa3b9ac8908023760373591210046f438e6b2242038bc8750d64
  | 13 => 0xf0f42660b2c8400e1d84cc165908018bee3982cb213ab93c83305964204d3741460b2c8400a6d828c165908134dd04182cb210029b60830596420043f43e20b2c840087d87c4165908014bd07082cb210029760e105964204d3741420b2c8400a6d8284165908010fd0e082cb210021f61c10596421bd1f42020b2c8400a3d8404165908014bd06082cb210029760c105964204d3741020b2c8400a6d8204165908b34eb033aac32116e9de05755864202c3f42ee6b0c840087d85dcd61908131e90e98ac3210161fa1770586420043ec2ee0b0c84fec5e75cc161908131f10e982c1210262f61373d954202476c16e7b2a8400a3d849436550a09c3ea9986caa100e1f21d535954201c5e43a86b2a8400e1d5350d655080187ecbba2a4a10021fe1570d854202c3e42ae1b0a84008df835c760508071b906b8ec0a116f1bc857690b510063690aed216a200c5f305da42d44b78de40bb485a880a1f61773d91510046fc1ae5b22a2038dc835cb645440147b0b206c8a8c0f175d730d915180f0f2a661b22a204a3e86d91545459f878c9b92a8a88021f61e54d89510143ec2ee7b12a303c5d75cc362544011df0eb10c4a896f0fd85749495117e9bb0ae9292a200d1f305d252544b3a5e40ba4a4a88034dc4174949510043ec3ec9292a228c3e74d9252544050fb0b3b484a880a1f21975909510143f436eaa12a25993d84dd542544050f90cbaa84a88df0f19175509510061fbaec8a12a29b87f875536054409878e8aa6c0a880a1f61773d81510046fc1ae5b02a2038dc835cb60544cd0ff0ea96c0a889e1f61f63d91511451f426c7b22a20095f835cb645444f2b906b96c8a88028f61a40d91510059ac0c81b22a301e1e64cc3645445147d0db22c8a88a30fddb6459151004bbc0ae6b22a228a3c84d8d645444f0f90eb1ac8a88a28f211635915113c9e43a86b22a200a3c8650d6454401c3ac6a1ac8a88030f19372591518171a326e2b22a200d3764dc56454605a68c9b8ac8a8c0b4dd0f71591510069aa1ee2b22a20097580dc56454605a6e81b8ac8a8c07871933059151006abb8e60b22a25987d87193625440187ae8326c4a88029760c64d89512cd37410c9b12a25987d87d8f62544b787ec2ba4c4a88034dd8574989512ce97902e9312a200d37105d2625445187ce9b24c4a88a30f9d16498951006b3b12e3312a259d64625c662544012ef00b8cc4a896759c8171989510061f3a4c1312a200a3d84182625440187ce8304c4a88029b608609895180e8f3a661312a200d1d74cc26254401aaae3984c4a88030fdd264589510043f438c8b12a200a5d83191625444f2bd0fb9ac4a880355d877358951004aec06e6b12a200d5710dcd62544012ef02b9ac4a889f171cf63589512cc3e43ac6b12a259a6c8258d6254401aaee7b8ac4a8
  | 14 => 0x40010010010000010010010000020020243ec2ee7b12a804c3d7550f625500793ce6a1ec4aa0038754d43d89547be2ebae61b12a907c6d75d8a625520d95ae9b14c4aa0023be1d62189541543e43aa7b0aa800e1d5350f615513b0ff0ab86c2aa00e3ee1d30d815404c5e43a86b24a400a3d85905649480153d07202c929002a760e405925204d5741480b24a43ba3e851cd649480147b0a39ac9290be8fa1671592520051ec2ce2b24a43ba3e851c5649480147b0a38ac929002a7a0c71592520054ec18e2b24a409aae821c5649487755b0438ac929002aea0071592520055cc00e2b24a42fa3e858c5649480147b0b18ac9290022fa1c31592520045ec3862b24a42fa3e850c5649480147b0a18ac929026aba08315925200556c1062b24a400aba800c564948015730018ac929002a7a0e70592520054ec1ce0b24a409aae829c1649480155b05382c9290028fe1570592521dd1f428e0b24a400a3d851c1649480153d06382c929002a760c705925204d57410e0b24a43baad821c1649480156d02382c929002ad60470592520045f43e60b24a4008bd87cc1649485f47d0b982c9290028f61730592520064f43e60b24a400c9d87cc16494a09c3d0b982c9290038761730592528270fa8e60b24a4eae8f20cc1649481355d05182c929002ab60a305925204d5741060b24a400aad820c1649485f47d0b882c9290028f61710592520054f41c20b24a400a9d83841649481355d05082c929002ab60a10592520045f43820b24a4008bd87041649485f47d0a082c9290028f61410592520054f41820b24a400a9d83041649481355d04082c929002ab608105925268697ba6e4aa4a42bc3e64dc554948b74ef02baac3290263d21d31586520053ac0ca0b0ca49b87c87551609480987ce8aa2c1290263e21d305825282f0f2a661b22a400c3c545d361548b70f90ea9ec2a900a1f21570d855214e2e3ae61b0aa4008df835c760548071b906b8ec0a90263b209735964204c3f43ca6b2c840987c8754d65908014bd07282cb210029760e505964204d37414a0b2c8400a6f825cd65908134d904b9acb210de8fa1073596420051ec20e6b2c845bc6f20dc565908134dd0538acb210029b60a71596420043f43c62b2c840087d878c565908010fd0e18acb210021f61c31596421bd1f42062b2c8400a3d840c565908134dd0418acb210029b60831596420053d40062b2c8400a79800c565908014bd07382cb210029760e705964204d37414e0b2c8400a6d829c1659086f47d08382cb210028f61070596420052f418e0b2c8400a5d831c165908134dd04382cb210ce9b60870596420053b408e0b2c8400a75811c165908010fd0f982cb210021f61f30596421bd1f42660b2c8400a3d84cc165908018bd0f982cb210031761f305964282
  | 15 => 0x598000c0e00600000700300100b00800000800300200600100100100100000100000100000000000000400200000000200000b00000100100200400100a00000100000100000000000000000200300000000000c00300700100100700100000200000000000700400000500200000000300100100000800000100400000000000000d00000700000400000200000000800300500100300900200000100400200000400200000100000000000200100e00000000100200000300100100100300600000600300400000200000c00000100200100100200200400500900100200100400200100000000000000000000600e00000000200b00000000000400600200000300a00300000200b00000000000100000700000100000300100200100000300100000000300000200200300000600800100300100000000000000700300800200100000000400f00400000100500300300000200000000400100000300600200000100300000200100000300000300000000100500100300000d00201100300000000400800000000000500100000000000000300300300400900000000200200100500f00000500000000100000000300700000800100400500200100200100300000200000000000100300000400000000100000200900100200000000000000000000000000200100100200700000800100100000000100100300200200000300100000000300000000000000000200f00500000000000100000000300200000100000100000100100400000000000000100100100000200000000a00000100200100000000100100000100000400000100600400000000600700000000100100200000100000000000000000100700400300000400200000200000300000300100000100000000400000100300300100100000500000100500400000e00000500000700000200000000100100200300200300100100300400000100400300200000f00000100100100300100600500000100300300300100000000100100000500200000200100000100000000500000000200200000100000000200100200300000400100500000400800000000800800000000000000200200200000400100000200100500000000100000000000100000000200000000100100700000000000101000500100100500000000100000500400100c00300000100000000300000300000d00a00000000000200000001100100800000000001000000e00500b00000000100300000d00000100100000000200000400500200000200000200300100200000000400100300700100100200400100100100000100000600000000000200800001900000000c00000600700000000000800000100000400000100700500000100200000100200000100000000c00200000100000800000000
  | 16 => 0xbd6000205156c2ca2cf000000000000026f17a0a1800000000000007252b59e500000001ae0a900000000000da877e40100000000000002f6162027c7f517e86700006f800010c800009e0000000ba207022585a026881408707844d20002180000d3411b2818e745c22950ef00003183db2ff963c0000000000000c84142000128c000758000000000038d00000000000003ed98248c42e72aa17e8a600bc22980000004a6000000000000000000000001612650fac53c1111a0105819600000000000003e800000000000000000000dac0d000009e0fac00020f09900000000001f94bbc0000000000c08000000195cc2000000000009821fe000145c7ba0ad0d09c28aa400020d80006b400000000000000000001b540004ef00002480006ef1b000500002e60000bdc0007e223502d0f4c4a939c88881d844c26911f460840c13e8e8501251340903e8516000000000011608437a0a8c2a20ae3c707b0cfe37218f80008744f12b7047400000027c800000000000015b4000000000000033c00035e951cc6c58715800000004f40000000c9000038f80000000000000eb81b866e0000dfcc8662510c8e64fb87950001dac0007a500000000000000000f7c00000000000000000000001c480b873a01e8000b0609a00d0000000241165800000077c0b50000000000000195481e0000000480c56439000180cc1a0000000e680003b8236926cb5a0000000f0000045b00000000001cc0000000000000256000000063030a10107fc30319782d4cee7292059ba0d0e49700000000000000b105f80000000001e900000002130000322110000000021800015e115400006a00000000003b622b0afc6124db1de97cc27e3810000c64430000325053c15e0580001adc0000003df000000041700000000000000000000000000000118cd6000000000003700003f6050400000000000008a06d000000000000001ca80000a86cd0001a6c0001c80001d202bc000000000039605500000010382f1000018000000022a000081a0fb000000101c0470a5831c8ce74b00000000002812490d9c00000038d800091210b00000000002801421414000719000000000000000019f4fc80003788330000000005800097c00000000000000000b680000007c30000000b86000000000000080b0000decc8e0002b48000e883a83c480006460002ec8b1c0006be10200001e039424200000000000000000000000000179400000017d80000007d70000000000000000000000065e0000000000000063000000000000000340005c711e07184aa72632d916429c6ad000000031000001f00000001011e5000064c000000000000000000016f0d2e66c0000000cb200000009c80007682fc000000000026b80008de5bd3de0f98e1c1f23bc14245a21e207116883aa4b63
  | 17 => 0x3ec9c200000000000000000000232920812a0001b61fdc0000000209ae0000000000000006c0000fe000000000018b8000d043323450484ed86fc00018a4682000000000000000000000000b600000000000000000000000db842d02705fc00006b3b68964e1a2af3ea0d100006fe3e800004c40002cf80200006280000000eb45480000000e42000244036485653b216167015812629b8000f5c26c03a800080e07800014d00002a92a49828000000000000000063700000006e000000008a03947232b51510af00000000d340006d83459b9c5800001a811d4b8c212000148401200028a0000386431001000049a0000000000cda25e2cd19f807013900016740003470000774c3a000000000070e000000162c000000000000000052b3ab0d500000000000be40000000001e8800000004d800000e0002aa870000000000000000003dc000000000044907c05104f80c30001700a5e6343420000000000000000000049d000000000000000000006aa0000000000c0436300000000000000b3800000068520e8d1800000005b000000000011b800000000032300000000002b280000007f1253800088000015680004d04e9059800000079b0770130b603f1374800000000000000000000001fe0e4c0000342d58000f540000d214b800000028b0770000172000000000000006901f400002400018600003d33b1000000000028f800000000000000002040000000b5400000000001b8e2221424b14700007962df8000bba5c200002e0c9e1f8000008800000000000000000001b7000004e4a831788f80007ad0000000000000000188400079d00000004a20000001ab03b44c900008f44800940000000a707040000000000000000000000060104f80008304ff000000078200026000002065c400009d400000000000000000002be93943f46c8000000000024f2c019000004a220c907000067c00000000007433b985f40be79222700e8d1a5f52be1c781bc28615917b89ba5f00000000000000000205c9400000001fc87545cd24c9b947203a50000000000164085000053a7f9147087c00000000000000000000001d703d00000000000762000000000000057a000016868a0002150cec9fa2100aa0acc0000e41e61c3c0000000000000000706000000102a38c26c8858c441be0978eac0002a80000cb81460000000420ac200026700002ba049271079893000013f9ff0000000000109c00078d0000000000000116073400000000001e80001b400000000000000000000da640838d0000ade0002230f5478e4dc0000000000000000000000000000012a80000000000c5800000000008fc00000000000000000f900019cc00025724f135831400000003940000000001f80000233092800005672a19d000000000000000000000002d08000
  | 18 => 0xa61da879e0001fe977c00000032280000006eb0e099d400046c000000000000006780000000002b20a442000000000000b9433500500000000001a50b340004f72b60000a800000000e6c0000001088000ee205d16083fc4ce00000000000000003dc00000000001270da00000000cb800048a2be0001fecbb0000000000044a000000041c000000000154c00000000005182120000000000d4c4e600000001d060800000000ae00018e000000020b1ad803800000012a146101e5db1258b08d8c80d3fc168079c4050000098cf0000309805c5ea00035d000000000000000000000002b800002564ae0000000e1600000012f4d6a000000000000049f00000000000000000984a0062a390000000079f3f700000000001af00000000001238a0c7e60000000000000000000000000000010e000000000000006c445e54200019a000000000000007e40000000000fde4941b3000000000000000001f80000000000000786000168c31200000000003440000000b707a07673e000c0000000000000000022600006145406aa18d800000000000016ecac600000000006ea3cd1da8000d2a00000000000000713c781fc58c5740c9074c8905810179b88d3826e09b8b605b61ed21a9cfc474811000051c8d20000000ca86960003d992b40000000e49e700d80893af933c00001900017b50000001fb189c0000004008f48000000000012800073c04418ec1026d73e200000000002b400005ac11328786807f200026100000003d92fc96546c827e31f9b7846c1ab0000f449c800017e0214262056169966c00000023880000000a8183800023e0003bb8ec00002ba1b080000000001a980005f00000000c180000001c3079052e4d30df80000005d20669090000000000000000000024680000000000000000f7400000000000000000000f180000000000000ca826f0000b240003ad0000cacf0a0000001a240006d209700005e60420d500006280003c59f3800000000006a47ae41f000000102c00034f0000ab47c826a83146202ac0000880000040000000009e47b0000cdc0006fb30a9fd0704000150800000000000000000000000001180a483120ab15cc5720000000000ec05200000000d065ef00000000000002ae8000c16000009188c1cc3fa22e9a04f0400000000001b41ff22c000103c0002d7000000070c094978c00000021700000004af0000928a7426a248800098e00000000000000000d300002b400000014681c23ba0000000bae7c517680002241d70718000dcc00039595c43787500001cc47c000000000000000001490d087660d3000000053000000000000006d400000000000001f496240002e93a300002ea00c0ca00000007d319c000075e00003108a40000001929bd8d4400000000005ba00015c0000b66066
  | 19 => 0x1a88e3c36a00000007b8a0835238280000000000000d30dfe0000001a4400072836d800039e5fd0001d8c0002e80378000b180000f78cd87ee18d00000000005da3349d4400000000000000500000be00008f0000102953cdea04b1a70aac00000020a80000001182599e3000000000016bcc7c00000000000006c02e80000000000208897400066b000000000000025a80000005112f90a88b6a62629916dc00000000011d08d007e2dc800046271d00000000000003648f680001ea3031ff4a1a0001118280000000000067c0000000119b14b2638a00018cc0000000001a4c0002340000000c3e0001800c040000000000000b044bc0000f600000000511d941fc4c40000fa8f963e41ac9dd881c20f000005882600023080002f20b229600000007722a70000594000000199cf06000024086c00000022b8c2ca3c7d51cf91683c00003d080009d001e31a917869047600008787965190099e5cc227072af13a83a20ef000000000011600000000003221de00000000000001f68510000000068c0000150939cec61000009600000000000000000e4e72c23e19346da0000001dec69e48e0000000000000000000000000000015d4000000000000010e67900000000000000000000a6a0000000000000000000000000004d30d06dc17c0001f08ffcaf210626a0ba80000003969e440007b500016a8000799000060000000037e800000000000000005dc7bf0b4979000000025c93ec5a87c723b800006e6c409e8f9c54a30e00000000000000000000000000049800000000000000000000002528d60ea6000000000000000000000001ea0003e68000aee01b3a78000fd61822cb05b8bf60000000000fa216f0001d5c000000074890c0000000000664a964730001958f682ff2a288ec1d60000dd0000c620000000000000000000000000069f00000000000000c3000000000000000000007e300000000000000000dcc0000322ab00003160000000000d9800021b9544e9a5fe0d980003f213234b0ad8ca20002890000cc4000258142c0005e90000000de02c500000000000000e904d86d600000000009981331ba00000007df0000c14bec0000a18000bcc3280b8000000000021a00000006e100000000000000000000cc201f0000148000000000000000000039b00000002603d600ec0002ef25085e0000000000000000051d25a1970de616c354014091428a3b780d4afc5ba1af861040e2520fa8000388000000000000000021985c4a5042224180001066cf000023c00044214a00002e80000d7206c5f47b61bd125487e5660230e580000003769b2c0001e300007a40004b83430018000781000000093447e33213b400000000017f003007607a00000001f60001f28efe10d00e9c5c0000000000c84916000000000056e000000000
  | 20 => 0x90000383000000041c30f0000000bc42e504715ec3a00000fd800017e00019c84c0baa0000002030a20033000000072e5e1000000074400018e9a383e04eb13b1e800007180000658000000036904024415800013c80008190000354000000000000000000002980000006f9000150400015b0000000bd400000000000000003478000ac4331021800000000000009cc67800016708b44a6000000124019000040e80000000003d3800000000035e03280003341ef00001480001cc00004ca00000000000004cd0001d28d5c00000006ec5540df0000000000000000000000008d1680a980002873e100000000003c51ccc0885910001128b700003ad843c63c5c92df15fc00000008b80000000000000da40000002178000f6e00000000005be45f000000091e00000000000006a11e185700003e526d000000000000013b8a467020ed80000000000001b646046da00004f0000445000158000000000001cc00032d06b8000e6e000000000089e0000000230000000000000000000007519d08fe0003cc00000000001d60000000000000000000000000000005c831a000000053600024e000000002c0000000fec000000000000000000016a4000148028991000025a00007cc4f61af235919007e135000100088600000896c87403ec3521f24b0c60c05b800025026617600000007130001f18f207e83170b203e87b100000000005c10000d5c0006ab1e200000000002381f60000000050884c00000008c8c600d019d2a6800000074e35f8d74000487000000000074c00003102c60000349c50c980001468000b3c000000121439c0000000000000000000025c00000000000000000003400000ce200013a0edcf504f01230b68eb2000015000000000040800000005900e39c8896400000000000003d40000000ab050636191b80000000001698c921d621b051400000000000000000000c0800000000010a8000bce320000000034a0721711e8c0003ed25f838000021709c019400029c357852800044d0001cf4b581530000d58000000000000000076e00000000000000001fa85207403ef0fd02be0001949a7400052a20d0450e2026334a138473c6c70000000000000000071414e17a0001b7c00000000000000000001eb01dc47221a0481cd401e6c21c007dcc5a00000006b503058500000000003760918000000000000173000000034912900005f10790000000000000000000000000000001ec00030b1ff8e120000000350ba800000000000000000001d040000000001570a7200000013e8c240a600005dc0000001008000aec0003af0000f823be1ce19bcd1000015380004907551bc9de841077914d0970000000000000000000000000000007cc01c949cce400035380007c400000000000000000001e1c0000002618000a6c00
  | 21 => 0x600e1066c0003fb0d8131400067a138200825453d31d0ed0c000000001ad0cc61734031340d766a923c80000005dc2ca0bf8fe6000000000000061e3ba98380007e100000000003e30321dc000009c1120540c726e320312ec0b20000000000b9c3c812f8e9c5120db00000000000c004b207c000000142800057637d16c8c5429a441162000090c64b12d969000000000000008120002498000b320002a300009ce02e34c9e104423bb03d80b400050a149800047000024602604b000409d04eca440000000000000000000000000065d0c7000000000000010803fa0000001ebc000000000077cf520003fd00000005262719df81e64c61bb9e6828000000019d80006b10000d0c6f8000000200cd825f42d38000000000000000032a0000000084000000000089cdc80001e48000c321b60a9000000063d00000000000c20000000e7c000000000000000031c1cbc00000000000008b811c3c000000002c327c0000000000000000000034908290a0e8a0001b780002ec22a29f000041a4c804500005ec6243ee8000a86365054959c00000035900000000000000000000507104969453200017a00000021870000000000000000020800000028100000000000000000fa457233309c44142b52e282181a200000000000003f50000e981ee52d0000000a1c18f0001ce000000005580000000001359da40000203a48000f7a51b19f800000047a3f390a478400000015289ec7883ff9c0c00066a29f800000000035b00003063c51c580000001b20000000000000000000017a38e141019c00036235011c8000000000000000058e0001bb8000000376032400058d000174cc1e5b1000000000000016f000000600000000000005330001ae400000037500000000002019f3c000000008134400033e1031870e005f700000002aa0002af876000000000012c400029f0000ab80000000000454000701000202074620c000104800037100016a057a07c00000000000001588e4856831300000000004211c282e80000003be80003e20001701d7400079e0000cb07f027a27a800032668c055079c06200000002ec0e800000009dc0005970401a8ce5c0000b31eec0003882798fc000009d00000000002eb24084690340ed21280000000003190000d9c00027e1b280008130000a3ccbe000000000046a44717186b000000032c00000002f20000000000000000000000058a0d403384564d8000000004a0000001b44000000000000064e00010100000000001170000c2e7b20148000d3000000019400000000001d1c0001d40002028cca4141f784109746530000de00000001f71fa4618061060895800080700013f900a5b62a812dc3b221d0000c44ec264e12208c825a00028a8000a78045000000000000000000000000000000000c0a5d60001c
  | 22 => 0x17800000f2000000000000043813c800000000014b17804da7420b0069c7525291249f9800059200003c40002cc3aa1ec0b9e45200000008cc0fd000000000000037b80000380b100006f41ac7343991c70000000000000000000000018f00006700000000888384000155cdf400001e0000000000000039c90000000000000005250001fb40000001bf05ec0005840488000d200003b30000f263300001cc0cb4000000049046000025588007480000cd000000000021e86600c62d2280800023c30d21e13b071261b3a9000032000000016d01ba598228956413254c00000000000001998000b9064100000001600a50000000e2c8040000000c406521460cf417200016b932c8460002011fc04062420001c54000000000000000062c06c0c280000000a48794000159128000000000000010f800000000010ec2d677400000140007ab0001b8072253100007ac0003240000000f721b9000000000000012600007726a526f8000ec86dd3790178b963b20ab94209c000033d80000006
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1bf708955d1424c1200059464785d85304800165191217614c1200061621f65585304800185887195614c12000686210655853048001349981cb514c120005c265072d453048001741911cb514c120004d266242d45304800170994949514c120005c265282545304800174191a09514c120005d0e45825453048001349981c9514c120005c2650725453048001741911c9514c120004d266242545304800174191197214c120004d26548748530480013899421d214c120004d26578448530480a53c0985c5214c120006896116218951440013539360b7054510004b164c8650921440018707660475501100064cdd08754540440015519321d51501101354c25d8454540440019308761151501100055464f72545404400133195e0941501100056464f725054044001b1151e11654c110006341d9811c930440019c172604724c11001c36a6387589304400185887e15624c1100061621c85589304400189887e11624c1100062621c845893044001a1885211624c110004d4e5584dc530440013539560b714c110004e4650875453044025350985d5514c110094d46578454530441adb1254e11514c110094d4a625254530441ad71294949514c110005c46525254530440016539661d514c110005c4e518754530441ad7109461d514c110005d0e498754530440017409261d514c1106b5c4a508754530440017119421d514c11000594e5984545304404d65096611514c1106b6c4211845453044001353985d1514c110004d426174545304400135398591514c110214d426164545304404d65296a09514c1100059465a8254530441ad71294a09514c110005c465282545304400155397609514c1100055425d825453044001353985c9514c110004d4261725453044001352981c9514c110004d46607254530441b5652961c9514c110235946587254530441ad712941c9514c110005c4650725453044001d41721c9514c110004d4e6162545304408535098589514c11000554e5d62545304408d55097589514c110005c4e516254530441ad71094589514c110004d4a6062545304404d35198189514c11084554a5c62545304402555197189514c1106b5c4a5062545304400171194189514c110004d4a6242545304400135198909514c110004d46548750530440032d096615414c110094e426174505304400135195e09414c110004d46548748530440013919421d214c1100047425d85485304400135195e11214c110094f02617248530440019c0875c9214c1100957065c62485304400178194189214c1100061c1d9811d52044001721949495148110005c865282545204404d560976095148110134d8660625452044001721941895148110004d86624254520440d1c6076dd52148110004d86578448520440054e0965d12148110
  | 1 => 0x1144872616350d645440141d931937259151006075d1831936254401835819d060989510060b9d182182625440141d9319176509510060e200645d9425440103d98ddb64509510050764c845d7625040105d989d463d9121006169d58018f64484018597560063d912100607e17845c36348401865825c46119540004176627319762501f3459909cc65d89404dc0f26276552525000141d939d954949400070c505109db515000141d931d9545454000607611831d9515000103d98d0876545400050d646401d9515000103d9810076545400050b648401d9515000143591100765454000417663301d95150001c533044076545400070c505101d9515000141d931d974545400040f25985dc94150001459901cf6548540857061c165591544c0015499284175189300056264a105d0624c001cc16284171189300053164b645c4624c0015c390589711893000711e55625c4624c001c4495589711893000711a15625c4624c001c4585589711893075531e41625c4624c001cc39058971189300057064a805c4624c001cc162a01711893000654615805c4624c001cc16260171189300057064b605c4624c001899706106118930006325c182184624c001895845c461189300056264a105d2524c2131589855170949300055264a105d6424c00141d951d96450930006915898118b514c00144c9758862545300069158981189514c0015519121570c853000607615841d9214c00189584604764853000631609811d9214c05585980d44764853013e16601511d9214c00185a85600764853000616615801d9214c00189a84600764853000626611801d9214c0018c982600764853000634605801d9214c001cc120440764853000714d45101d9214c0a58c487589614853000436a60765c1214c00181f7460e74d95200040fe61741d36548001835845c461195200061560d7118465480015899384174949200055264e105d64248001c612144276d452000714cc1101d95148001c612144076545200059164c61d95214800161a94dd8654c12000516a5e64195304800134b95613724c120004d2e45851c9304800134b98d94724c120004d2660651c93048001b0b65610724c120006c2195841c93048001b4295604724c120006d0655811c93048001b4365604724c120006d0195811c93048001b0b65612524c1206fec21958494930481bfb0b51612524c120005922595494930480013899421d524c120294d2261755493048071a4886d95524c120294d26578454930481c1b0a54e11524c120004d2e4585909304800134b98d96424c120004d26606590930480013499521d424c120294e26538550930481bfb0b54e15424c12000cb22598550930480c9a4886195424c120294e2261745093048001988875d1424c120295a2259745093048
  | 2 => 0x17a92360750eed301683212702c1ca750002c00e30029c70d071001cc0c0005c780064a6414dd1ab4400aa0a0004e004ba0c001a61b90b2cc56000f4006100030c602ad93400512797c723e0d9aadf2621004165d800008574000b00059800529b39949d898000000000000f4004e62bad9c0e2999844a56db0400ad4798dc225258dc002c10800b66e66a855e39150f810b55001d188645001cea66b934808e2f9c5b4d22e99046b2231781a77030fd3a6507adcb81c0aa24cec06a2f0008d679d92c54641d022ae04b59d2004580094346593d52003c10c00d9289ac40ba16800001f3f0ac64822b8000030283a8007000001720000188004562185229f698bc824934091387d00001564402001025524378663a3f91c20bf3caa006a30f2c5003b09800f695480b9101b5c1b5b0ca6e1bc02931410968942b290d4691331c6200000000e0500c0005058001e0b0080806080101c000007000040a038140a031a82c1a07000200a000580c12090d81804000401c0e0b0200406030607c2e1a0d8040001010000609060041c0b0101402080081020021081012040060761d85cc1649480141d9315174d85520060761d84cc1659080103f9761a40d915
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x6ec0040a280500603326400c8bb284a8802851a8cc1101d9515000122254b0ab12e23126000e106156260171189300050894eb1302312a298002909a521d745093048001488d190ec22a2a022000a502a1721c9514c110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x4840ba615626017118930
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x94c
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x3
  | 10 => 0x98c
  | 11 => 0x98a
  | 12 => 0x98d
  | 13 => 0x98e
  | 14 => 0x150a
  | 15 => 0x150c
  | 16 => 0x150d
  | 17 => 0x150e
  | 18 => 0x9ca
  | 19 => 0x9cd
  | 20 => 0x9ce
  | 21 => 0xa0a
  | 22 => 0xa0c
  | 23 => 0xa0e
  | 24 => 0xa4a
  | 25 => 0xa4c
  | 26 => 0xa4d
  | 27 => 0xb09
  | 28 => 0xb0c
  | 29 => 0xb0d
  | 30 => 0xb0e
  | 31 => 0x1549
  | 32 => 0x154c
  | 33 => 0x154d
  | 34 => 0x154e
  | 35 => 0xb89
  | 36 => 0xb8c
  | 37 => 0xb8e
  | 38 => 0xbc9
  | 39 => 0xbcc
  | 40 => 0xbcd
  | 41 => 0x19c9
  | 42 => 0x19cc
  | 43 => 0x19cd
  | 44 => 0xd09
  | 45 => 0xd0a
  | 46 => 0xd0c
  | 47 => 0xd0e
  | 48 => 0x1609
  | 49 => 0x160a
  | 50 => 0x160c
  | 51 => 0x160e
  | 52 => 0xd49
  | 53 => 0xd4a
  | 54 => 0xd4c
  | 55 => 0xd4d
  | 56 => 0x1649
  | 57 => 0x164a
  | 58 => 0x164c
  | 59 => 0x164d
  | 60 => 0x1049
  | 61 => 0x104a
  | 62 => 0x104c
  | 63 => 0x98954
  | 64 => 0x94994
  | 65 => 0x9c955
  | 66 => 0x9c956
  | 67 => 0x94a14
  | 68 => 0xb0954
  | 69 => 0xb8954
  | 70 => 0xbc954
  | 71 => 0xbc955
  | 72 => 0x94bd4
  | 73 => 0x1409
  | 74 => 0x128a
  | 75 => 0x1849
  | 76 => 0x1489
  | 77 => 0x180a
  | 78 => 0x130a
  | 79 => 0x14c9
  | 80 => 0x198a
  | 81 => 0x134a
  | 82 => 0x9cb
  | 83 => 0x9c992
  | 84 => 0x9c995
  | 85 => 0x9c996
  | 86 => 0xb0994
  | 87 => 0x154994
  | 88 => 0x209
  | 89 => 0xbcb
  | 90 => 0xbc994
  | 91 => 0x19cb
  | 92 => 0x19c994
  | 93 => 0xd0994
  | 94 => 0xd0996
  | 95 => 0x160994
  | 96 => 0x409
  | 97 => 0xd4994
  | 98 => 0xd4995
  | 99 => 0x164994
  | 100 => 0x449
  | 101 => 0x1889
  | 102 => 0x14b
  | 103 => 0x1a09
  | 104 => 0x134b
  | 105 => 0xb1514
  | 106 => 0x8a
  | 107 => 0xbd514
  | 108 => 0x19d514
  | 109 => 0xd1514
  | 110 => 0xd1516
  | 111 => 0x8d
  | 112 => 0xd5514
  | 113 => 0xd5515
  | 114 => 0x8e
  | 115 => 0x104b
  | 116 => 0xbc9d5
  | 117 => 0x19c9d5
  | 118 => 0xb49
  | 119 => 0x138c
  | 120 => 0x16c9
  | 121 => 0x1449
  | 122 => 0x124c
  | 123 => 0x249
  | 124 => 0xd09d6
  | 125 => 0xd49d5
  | 126 => 0x3c9
  | 127 => 0x8c
  | 128 => 0x15c9
  | 129 => 0x1709
  | 130 => 0xcc9
  | 131 => 0x128c
  | 132 => 0x1a89
  | 133 => 0x1949
  | 134 => 0xe89
  | 135 => 0x180c
  | 136 => 0x1789
  | 137 => 0x18c9
  | 138 => 0x130c
  | 139 => 0x589
  | 140 => 0xec9
  | 141 => 0x198c
  | 142 => 0x17c9
  | 143 => 0x1a49
  | 144 => 0x134c
  | 145 => 0x5c9
  | 146 => 0xb8a14
  | 147 => 0xbca14
  | 148 => 0x19ca14
  | 149 => 0x138d
  | 150 => 0x124d
  | 151 => 0xd0a14
  | 152 => 0x128d
  | 153 => 0x104a14
  | 154 => 0x749
  | 155 => 0x14d
  | 156 => 0x198d
  | 157 => 0x134d
  | 158 => 0xbca54
  | 159 => 0x138e
  | 160 => 0x124e
  | 161 => 0xd4a54
  | 162 => 0x128e
  | 163 => 0x104a54
  | 164 => 0x180e
  | 165 => 0x130e
  | 166 => 0xd0b14
  | 167 => 0xb0d14
  | 168 => 0xd0b16
  | 169 => 0x160b14
  | 170 => 0xb1614
  | 171 => 0x40a
  | 172 => 0x15ca
  | 173 => 0x144b
  | 174 => 0x3ca
  | 175 => 0x188a
  | 176 => 0x1a0a
  | 177 => 0xd1554
  | 178 => 0x154d14
  | 179 => 0xd1556
  | 180 => 0x20d
  | 181 => 0xd0b94
  | 182 => 0xb8d14
  | 183 => 0x140d
  | 184 => 0x1a8a
  | 185 => 0x194a
  | 186 => 0x14cd
  | 187 => 0xd0bd4
  | 188 => 0xbcd14
  | 189 => 0x160bd4
  | 190 => 0xbd614
  | 191 => 0x44a
  | 192 => 0x20e
  | 193 => 0x140e
  | 194 => 0x148e
  | 195 => 0x74a
  | 196 => 0xd4bd4
  | 197 => 0xbcd54
  | 198 => 0x164bd4
  | 199 => 0xbd654
  | 200 => 0x104bd4
  | 201 => 0xbd054
  | 202 => 0x184e
  | 203 => 0xd19d4
  | 204 => 0x19cd14
  | 205 => 0x1619d4
  | 206 => 0x19d614
  | 207 => 0x1a0d
  | 208 => 0x188e
  | 209 => 0x1a8b
  | 210 => 0x105654
  | 211 => 0xb09895c
  | 212 => 0xb09499c
  | 213 => 0xbc9499c
  | 214 => 0xbc9c95d
  | 215 => 0x95294
  | 216 => 0x989d2
  | 217 => 0x1289d2
  | 218 => 0x9d292
  | 219 => 0xb894a1c
  | 220 => 0xbc94a1c
  | 221 => 0x94bd5
  | 222 => 0x4c
  | 223 => 0xd09c99e
  | 224 => 0xd49c99d
  | 225 => 0x128994
  | 226 => 0xb1394
  | 227 => 0x155514
  | 228 => 0xb9814
  | 229 => 0xbd814
  | 230 => 0xbd994
  | 231 => 0x19d814
  | 232 => 0x139254
  | 233 => 0xd1814
  | 234 => 0x168b
  | 235 => 0xd5994
  | 236 => 0x989d6
  | 237 => 0xcc3d1
  | 238 => 0x9514
  | 239 => 0x151294
  | 240 => 0x1809d6
  | 241 => 0x105814
  | 242 => 0x105994
  | 243 => 0x181314
  | 244 => 0x199354
  | 245 => 0x75491
  | 246 => 0x74d11
  | 247 => 0x168d
  | 248 => 0x1289d5
  | 249 => 0x149d5
  | 250 => 0x74e91
  | 251 => 0x1a9951
  | 252 => 0x194e91
  | 253 => 0x19cbd1
  | 254 => 0x168e
  | 255 => 0x1a9952
  | 256 => 0x16ce
  | 257 => 0x168bd5
  | 258 => 0x19cbd5
  | 259 => 0x168a
  | 260 => 0x168d16
  | 261 => 0x168d55
  | 262 => 0x188d16
  | 263 => 0x1a0d55
  | 264 => 0xbc9529c
  | 265 => 0x9c155
  | 266 => 0xece91
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1548
  | 6 => 4483
  | 5 => 2080
  | 4 => 238
  | 3 => 8
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
  | 7 => packedAt gbK7 (62952+((h/516+packedAt gbK7 (57276+(h % 516)*11) 11) % 2043)*12) 12
  | 6 => packedAt gbK6 (234606+((h/1494+packedAt gbK6 (215184+(h % 1494)*13) 13) % 5380)*14) 14
  | 5 => packedAt gbK5 (131036+((h/693+packedAt gbK5 (122720+(h % 693)*12) 12) % 4019)*13) 13
  | 4 => packedAt gbK4 (17371+((h/79+packedAt gbK4 (16660+(h % 79)*9) 9) % 286)*9) 9
  | 3 => packedAt gbK3 (656+((h/2+packedAt gbK3 (648+(h % 2)*4) 4) % 11)*4) 4
  | 2 => packedAt gbK2 (93+((h/1+packedAt gbK2 (92+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc387e3ffce187c7e0fc7038387f208678d390f
  | 1 => 0x3f87c70301f878ff07803fff874319a12c1f3
  | 2 => 0xfc007f803fe007f0007ffc03ff89c61c630e3c
  | 3 => 0xffff80003ffff800007ffffc000e07e07c0fc0
  | 4 => 0x3fffffffff800000000ff8007ff000
  | 5 => 0xffffffffc000000000000000000fffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x40808090820808120141088881200020841905
  | 1 => 0x108242100008084800801212040108a004052
  | 2 => 0x8400490214200520221250025600c214230228
  | 3 => 0x6ad50004ab5d50004564aa58012e05605c0d80
  | 4 => 0x204400083d9666496e003010120f68007ba000
  | 5 => 0xb366724f010440018800c060644fbfdf000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeeafeeefce8fefefeeafeeefce8fefefeeafeeefce8fefefeeafeeefce8fefefeeafeeefce8fefefeeafeeefce8fefefeeafeeefce8fefefeeafeeefce8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36400
namespace PEqualNP.Outside.L_meta_36400
open PEqualNP.Outside.L_meta_36400.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 92 := (concat bs1_4_0 (concat bs1_4_32 bs1_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 44 := (concat bs1_5_0 bs1_5_32)
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
theorem bs2_3_0 : Interval s2Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 7 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
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
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 2 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 30 := block_range (n:=30) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 30 := bs3_3_0
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
theorem bs3_4_448 : Interval s3Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_512 : Interval s3Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_544 : Interval s3Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_608 : Interval s3Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_640 : Interval s3Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_704 : Interval s3Atlas 4 704 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 712 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128))) (concat (concat bs3_4_160 (concat bs3_4_192 bs3_4_224)) (concat bs3_4_256 (concat bs3_4_288 bs3_4_320)))) (concat (concat (concat bs3_4_352 (concat bs3_4_384 bs3_4_416)) (concat bs3_4_448 (concat bs3_4_480 bs3_4_512))) (concat (concat bs3_4_544 (concat bs3_4_576 bs3_4_608)) (concat bs3_4_640 (concat bs3_4_672 bs3_4_704)))))
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
theorem bs3_5_608 : Interval s3Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_640 : Interval s3Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_704 : Interval s3Atlas 5 704 31 := block_range (n:=31) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 735 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 (concat bs3_5_192 bs3_5_224)) (concat bs3_5_256 (concat bs3_5_288 bs3_5_320)))) (concat (concat (concat bs3_5_352 (concat bs3_5_384 bs3_5_416)) (concat bs3_5_448 (concat bs3_5_480 bs3_5_512))) (concat (concat bs3_5_544 (concat bs3_5_576 bs3_5_608)) (concat bs3_5_640 (concat bs3_5_672 bs3_5_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 42 := (concat bs3_6_0 bs3_6_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 9 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 50 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_128 : Interval s4Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 136 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 48 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_3_0 : Interval s5Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 16 := bs5_3_0
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
theorem bgb_3_0 : Interval gbAtlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 8 := bgb_3_0
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
theorem bgb_4_224 : Interval gbAtlas 4 224 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 238 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224)))
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
theorem allgb_5 : Interval gbAtlas 5 0 2080 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 bgb_5_992))))) (concat (concat (concat (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120)) (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248))) (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504)))) (concat (concat (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632)) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760))) (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)))))))
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
theorem bgb_6_4480 : Interval gbAtlas 6 4480 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4483 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)))))) (concat (concat (concat (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344))) (concat (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472)) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632))))) (concat (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)) (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)))) (concat (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048)) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208))))))) (concat (concat (concat (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464))) (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752))))) (concat (concat (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880)) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)))) (concat (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168)) (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)))))) (concat (concat (concat (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456)) (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616)))) (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904))))) (concat (concat (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 bgb_6_4032)) (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)))) (concat (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 bgb_6_4320)) (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480))))))))
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
theorem bgb_7_1536 : Interval gbAtlas 7 1536 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1548 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat bgb_7_672 (concat bgb_7_704 bgb_7_736))))) (concat (concat (concat (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928))) (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))) (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeafeeefce8fefefeeafeeefce8fefefeeafeeefce8fefefeeafeeefce8fefefeeafeeefce8fefefeeafeeefce8fefefeeafeeefce8fefefeeafeeefce8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124266 * 2 ^ 32 + 4277075176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36400.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,3]⟩,⟨.or,[2,4]⟩,⟨.or,[4,5]⟩,⟨.and,[1,7]⟩,⟨.and,[0,8]⟩,⟨.or,[1,2]⟩,⟨.and,[4,5]⟩,⟨.or,[9,12]⟩,⟨.or,[10,11]⟩,⟨.or,[6,13]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277075176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277075176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36400

open PEqualNP.Outside.L_meta_36400 in
theorem PEqualNP.Outside.L_meta_36400 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277075176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277075176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
