import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40483.Model
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


end PEqualNP.Outside.L_meta_40483.Model

namespace PEqualNP.Outside.L_meta_40483
open PEqualNP.Outside.L_meta_40483.Model
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

def SBf (j : Nat) : Nat := [6, 6, 6, 4, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40483

namespace PEqualNP.Outside.L_meta_40483
open PEqualNP.Outside.L_meta_40483.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x404dc31be40bc40de31
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/8+packedAt s0K4 (64+(h % 8)*2) 2) % 4)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1fffffffffff01fff03fffffffff807f1fffc7
  | 2 => 0xe03fffc07fffffffffc0fff00fffffffe3c7ff
  | 3 => 0xffc03fff80fffe03ffff03fff01fff80fcf8f8
  | 4 => 0xffffc00000fffffffffffc00001fffffff00ff
  | 5 => 0xffffffffff000003ffffffffffe00000ffff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x81454a450a211c48b00b2cb4d4a58a350d5bc3
  | 2 => 0xb91190931452249152c055524acab2c662c55d
  | 3 => 0xc9b5230a2694483a7555026ae2935b14b4e8e8
  | 4 => 0x12263a2c58e89123a9a6980c8c1c6c78df00b6
  | 5 => 0x1c383c3060f0e1c3ce38e38f0f007060fbb600
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0f0c00000fcc0ccc0f0c00000fcc0ccc0f0c00000fcc0ccc0f0c00000fcc0ccc0f0c00000fcc0ccc0f0c00000fcc0ccc0f0c00000fcc0ccc0f0c00000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40483
namespace PEqualNP.Outside.L_meta_40483
open PEqualNP.Outside.L_meta_40483.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x2400510010bc40f421bf43be40bd43f721ee21e421ec21
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x10011d2a1843a7430874ca810e9550218ea988166518874842206908640
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x8a158e540862565d0c21c154c21102256508440
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/10+packedAt s1K4 (144+(h % 10)*4) 4) % 9)
  | 3 => 2*((h/9+packedAt s1K3 (216+(h % 9)*3) 3) % 8)
  | 2 => 2*((h/8+packedAt s1K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffe07fffffc0fffffffffe07fffe3ff1ff
  | 2 => 0xc0fc0fff81f83fff0f07c1f03ff8781fd4ce67
  | 3 => 0xff000ffffe003ffff007fe003fff801fe70f87
  | 4 => 0xfffffffc1fffff800003fffffe1f80ff8
  | 5 => 0xfffff000000001ffffffffffc0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x42080023041000001108c211860088c20150ab
  | 2 => 0x963196451ca254cb074351a29ac85154d4c665
  | 3 => 0xc5aaa8a2874a9557085b4852d550299670b86
  | 4 => 0x28a34d1051460da6aad0210831a66701b80d50
  | 5 => 0x30c38e1c618731f8cce639ce01c44411fea000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaaaa000faaaaaaafaaaa000faaaaaaafaaaa000faaaaaaafaaaa000faaaaaaafaaaa000faaaaaaafaaaa000faaaaaaafaaaa000faaaaaaafaaaa000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40483
namespace PEqualNP.Outside.L_meta_40483
open PEqualNP.Outside.L_meta_40483.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x130000004dc30dd43f421e421f721de30ee21ec21de43
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x218e2a9843c4210c38c8610d994621e329843c4218c23aa8187150c21
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x6915964308705540843091594210c2856494c21
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | 2 => packedAt s2K2 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/10+packedAt s2K4 (144+(h % 10)*4) 4) % 9)
  | 3 => 2*((h/9+packedAt s2K3 (216+(h % 9)*3) 3) % 8)
  | 2 => 2*((h/8+packedAt s2K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe07fffffffffffc0ffffc0fffffffffe38ffff
  | 1 => 0xff81f83f03f03fff0f07ff0f03e0f81fd73267
  | 3 => 0xfffe003ffc003ffff007fff003ff001fe7c387
  | 4 => 0x3fffffc1fffff8000003ffffe1f803f8
  | 5 => 0xffffffc0000001fffffffffffc000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x23041001082000001108c011186108c20054ab
  | 1 => 0x452c6252394554cb0743550a29a8d154d33265
  | 3 => 0x8a18b4a450e9a9557085a6a052da429965c386
  | 4 => 0x1c514738a28d0de6aad03488831ce711f80350
  | 5 => 0x10618630c30e31b8cce638cce0108401bea800
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaaaaa8800eeaaeeaaaaaa8800eeaaeeaaaaaa8800eeaaeeaaaaaa8800eeaaeeaaaaaa8800eeaaeeaaaaaa8800eeaaeeaaaaaa8800eeaaeeaaaaaa8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40483
namespace PEqualNP.Outside.L_meta_40483
open PEqualNP.Outside.L_meta_40483.Model
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
  | 3 => 2*((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fffffe07ffffc0ffffc0fffff81fffe78fe3f
  | 1 => 0xe07e07ff81f81ff0f07ff07c0ffe0f81af33cc
  | 2 => 0xff8007fffe001fff007fff800ffff001cfc3f0
  | 4 => 0x7ffffffffffff8000000ffffffff003ff
  | 5 => 0xfffff80000001ffffffffffff0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc104202304108401108c42946188528c085615
  | 1 => 0x4b18aa451ca2acb074355258a6aa4b14ab32cc
  | 2 => 0x862d348a2874d557085a6b114b4d62294dc370
  | 4 => 0x1451c71051461a6aad0308420c718c71f001aa
  | 5 => 0x1861861c61871b8cce638c6380610841f6a800
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeaeaea0000eaeaeaeaeaea0000eaeaeaeaeaea0000eaeaeaeaeaea0000eaeaeaeaeaea0000eaeaeaeaeaea0000eaeaeaeaeaea0000eaeaeaeaeaea0000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40483
namespace PEqualNP.Outside.L_meta_40483
open PEqualNP.Outside.L_meta_40483.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2d80410000001802000801c9001000000240082ff42ff32ff31fe31ff41fe30fd30fc43fc41ff43fd40fe42fc30fc32fc31ff20fd21ff40fc42fe32fc10fd10fd42fe21fd20fe10fe41fc20fd31fd43ff10ff21fc40ff30fd41fc21fe20fe40fd32fe43
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x643ed424cbf620885f94642df21a875d53c82faa6085d14543beaa441ef52442fea098fec8120bf28663ee52d07ea4210f70ca31f790843f4514caf8a7905f55130bea86657d52883da84217710e30bf2a0837c52502fea4a0df94f40bf28e41ed42087dca421db94b41f7a16657e544cabaa6215f94e41bea9e817d529077e8220df54041bfaa2435c53487e88218df54a31bf29843ef21886fca7205f54742efa1c87ed32486fca1197d14540fb28881f6518c37e84215f54843bea8063ec32483de85105f54042be2a241ef32c82f8a6105f55331eea98816f52502fea690df94732bf298657e52d0efaa5205f94c42bf28e61de53c83e863885794c40bf284617651083e862885f54730bf296617d50d0bda8510f78c130dfa18876c5250efca9105f14e10ae29a217f54443eaa3186fd0e43f7190417d5190bdca4207754f41eea9e41f441cc6fca521d7d4d40dfaa2216d520c6faa8087b90920beaa263df438c2fca318dfd5210bfa82657d50906f8a5887dd0410bfa8a875d53d07de43906fd0040f690a41fb308c3f080185fd5232be2a265ef5250efaa7196f90942ae29a81dc430c2e8a2a05f94430bf28481ee528c2eca3185f15020bea84857e52103bc87997e44010f6a16417e508c678a8887750d30bfa94217e52086fca3105f94c20bf28c437e52443f0a0a1df54f21f6292217e54103f680a05f94043f6a9461ed320cbbe86185f15310ef99465f441886faa6107d88710bf288637d5490afca9905d54630bf29883dd5310bd884197d14543bba8a81fb400c2fca818df54b41bf29e21f621442f8a4985f55232ef218637e53483d86410df54331fca0081de434caeaa2105f54643bf294217c53482faa718df94242fd100417e51086f8a2a15f55243bfa8a656c524c6fea810df94432beaa4817c52843bc6418df94f21afa9a21765190af8a990f78c932be28263ec32886faa9086f90440bfa92876e520c7eaa2205b54840fd98261ef52503de8590fd54642f6a94837c54c82fca8195ed4143bf2a621f920083daa5987b48020bf2a2417d54c82f8a7885fd4b10bfa8285df328c3ee63885fd4930b6a94617e54cc7daa4087b14943bea8887ed21087d88490f7cc030bf29041f731443bc8718df55032f7290216f52442dca520df94c31f721265ef4250afaa1a0f7d4d40bea94217d53486fca8105fd4e21eea18877c54cc2fca8985b94a30ee98061ee4210afca5a0dfd5032ef19463dd328c2fea7905f55332bea98817d50887dc65105f54232f7210437e528c7b8a6a07b94831ee18c61f710842f8a9995f54e40bf29e837f54042f8a7106f50c43beaa041de53102fca018ef10440bea88857e53c83ba87985f94e43bfa9281df4350efea990fdd0431f6a9087ec32c82fca110fd84110be2a243ee21486bea690fd10610
  | 1 => 0x641443da43904fd5110fb208837d54483ea82885b54810faa08837c54842fca918df14532fb98e43ee21082fca121df54e42bea9443ee52cc2faa7087750c31b6292217f54cc7bca7a0df95221fba0c43dc53486f8a0995f14810be2a4657e5190efca220df54243bf28881ee42c83dc40905f54021f7a1065f721886f8a0a15f54b31bf28c65fb5050efaa021fbcc920bf290857e50102fea6105dd4532bf29083df320c2faa5a05f55031fa18e437d510cafaa4187d0c421dfa04817d54086fea8995f54743b7296617c548c6dea498fb8cb21ee188617c51502fea9905f14931bf28c817f544c2f8a6a07d8c431beaa443bd41106faa3a05f94641be2a4417f540c2fca418dfd4520f6a90817c544c6fca421df94032b629281ed428cafca120fe4c030ee99061f741cc6faa4205f55330bfa9e437d53c83bca6215fd4530f7a1243f5310c6fca8885f54a30bf29483ef20083eea2995f55231bfa92217d53482f8a2a1df94410bea8e417e50086eea2a1df54610bfa82877e50882fea7105fd5230bf2a661f621086f8a8185f14d21bea9c437d51102fea9995fd4810be2a6636d5210efea610fbd0a42bea8c81f840cc2fea918fb08620bf29a437e528c3ba6218df94c43eea1a65dc53443bc62187b4ca20bea9687bc54442fea0a0fec4210bea98857e53102faa5885f54831fba0c21be41903d885107dd0641fd180615e53c82baa6207d94420be29a217e520caeaa3215f54343be28283bd4210af8a8885fd4d40bf2a4217c54042fea7085f95332bf29021ed32c87f480205f54732f7990437d53442faa720db54a41af29e837c50486faa019778c531fa208217d53d06daa5a0df94c30beaa0617e51d02fca3a17bd4931fba0a437d53c43ee20085f55310bf29c857e51082e8a2995f14530bea9487f731087ea20087bc8520bf28685ef42083be6218dfd5120be2a461f65190af8a810dfd4d20f799265dd438c7be64195f15130f710c41ed42483d885995f94332bf29481f741507daa5a0db94840bfa82437d538c3f681207790c43fda06617e52c42fea818dfd4d41bea96617e50c86eca2205f94042bf28c61ee320cafca1085f15032bea9021bc41902fca1a0df94442beaa2657f54c42f8a818df95321be292837d53086fca7a15f55110f629281dc320c6fea498dd54440bf286877d52106f8a4887dcc531dea00817f544c6fea910f7d4d21bfaa0417e53843ba64195fd4540fba8a877d518c3be6318dfd4d10bfa8a857c53506faa990f7d4d10ef21e61de434c2fca3a1fec8220bf28061bf41907de6510fbc8220bf2a465f551082faa3197dc8521b7a92877e52d02faa2107b8c921beaa4617e54042fca821df94020fd080217c51482f8a710dfd5220bfa98217d508c7dc851977cc230bea98837e53042fea7885fd4d42f621
  | 2 => 0x8940001e0f8140301601c08020230040007c1c01c080001c000000040004c024b414020000180f004100ccb9000070fc00000840b06001c0904c01008018b80501c0502c0501c19088cd00c4900021088020000012c0000230018010041705027208040015301c00184010707700005004000580406c0d13c0000c0d0500a07800004dc0001d054023b01e040160209300643038320000e05c0f0200101c52004210000302059018e3120160040000092080570000439c49008042c803114030001a26c011b40e68c0c0000005c01254000040301802000030000001800000000a00102c0001c050002a008020000007803028020740c054000080001c0401401268050fc990301774800000000080301c94010000000d038b22b4ca01ced0b40026c870040005c010f8030000006c000980001006000410100538409078fd02c121fc0301000000280000f000033b460be28287ee42886f8a610ef90140be2a4437e528cafca4185f94e21bfaa6617c5250efaa2185f95030bea86437c53c86f0a0a1df95121f6990416e5210efca221fdd4540bea9e857e52cc6fca810efd0a42bea8c417e50042faa890df14c10bf294857e53883ea43887b10820ef18c617c5350bd842105f94d10b7290216d52cc37c82a0fd10521bea9c417d52443ea42887b54831f629263f641c42bca6217750f32bf2a2637d54907ee6318fd50710f7994657e5410afca9187b94a41bf28083f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xc54882cd6210c309b18954cc65f6355120d58c8514ca7561951328fd954310f6551480209d984530827b6055121d554e511025d6394a40d354e52d072c54d49109798c54c866d62d52319d185544c27561152309d984540c3655254440b5185320cb4c53d09219b18954442746548510d9949518c2d4614c830d9109510826e6215020d390d520c6d96310330d594d511027661d4e209dd85544ca5d6315010d6d0c5050e6d62947439d587538825f654c0309e596100423e6494d10d9584524425f63551219d185548835543145329798e52903345190140d354f32c83645288510d314a314c6cd62cc2309b18950d0f5753d45409b98a524423d6414c209758f54c426f6254c41b6181434ca7b654c0309d99641442776154f409d987540ca5c6550d329758e524426f6254d2197d8d508867461550309d987548ca6e6215331b358c424867665cc5109b988548c26d65d0820d594e51102e562904419bd89510c2e56190932d954a511023d6414f218f592524426e62d53108f191524426f62552109798e54486d563d0431d354f21c826d62953109b58a544436552d0641b618143cc25f63543429b997214826d62d50319b996424cb7051141439b98a544425e63153209ed81544c6756114c20d590c514ca6e62150109b189534434d5350b209bd89540c3655244010c7d5053443735114143d958652d077351d41439798c540865f654c8328f191534427661141429b997424871f54d4d109d58754c8334545051097d954310f4f53149409718d50d0a6e6514910b6181430c7546154f20d394a318c35763546428fd91524427860551329dd95411074d53948409dd85544c2746155120d954b100434d530cb209798e524427565d0410d9d485150f4f53d494097195434c34c538c921d394d52d066f62540419b588548426c62544309b98b5384357530c5109b596320834d5354b419b189501065c63542219798c54843576154f209e583548cae56190a329b588535067661150209b18953106e4614ca209b98b548c66c62542319b988540c66f6548020d94c951082b464440109b189548427960d4c219ed81544c26e62947409798c540425e63948209bd95420866d62d533097d8d524425d63951109b189544c66d6215230d354e42c825e63d5320b9185320cae4624c431dc1475050f5453c8521d954a518c27561152209718d519023f6550441d5d8d51082e662d0621d9d095190a6d62d4c10d394e521036752d4543f10c8310866d621533197d8d5108334540c5109b58853042d86050f329b98a53842756194b409718d524427765440109b596420866c65509209b58853c427b60551329dd95310c66f654c820d390d5210ecc63487209798c540c27761551109798f528426d6294d109b58a5090e6c62546409e583548c7545314540
  | 1 => 0x42776548421d514c41486e5620c510d618153102cd6310b219bd89519026e62151309b98853c427a60150219b58a544866d6294d20d9908514cb4c6254f209b594420ca7661d53309b98850506776154f20d518d510827661d4c109d58754cc26f62546439b98b530432f54d49109b597420cb4d5348720b358c42cca5d639522197d8d519023c6454d209d185544cacc624c431b958831c426e62d503197d95310c65d6315021b358b300c26e62943319718d510827a60d52329b189544c26c6550932dad4b5050e6f6255131d350d52cc34e53548409d98652d025d6590c31b618d401036551c8020d514f414874d5350842b6181438c75753145409dd85540c26e658c921d914b314423e64949109bd89544423f6454d209758e52082cc63485209b588505065f6355130da14b5050e6f62553319758e544c76652544409bd95320ca6d65cc8219ed95401025e6315120b958642086e56190a21d31895310a7a60d5231d3948318c27465505109ed95100434c53109219b98a51d0e7a60d4c21b518d210865e6394d219b99432483665294440b3189438c65e6394d109758c54c867561d50328f990530436552104319b997324825d6315320d314c524425e6395310b5d85430c75453d45409b588540c65e63d53109b98a539027565104319e580540c65e6514d10d390d52cc27561d5232cd546411034d53908429b189540c25d63d4a10b95864210a6e6295131d518d5190b345490510dad485050e6c6254f40d3d4c524427461553329b98a548c67661942439b18953c426d62951319d984540426e62d50219ed95200826e6295310d9549518c36552d04319d986544cae662d04319b98854cc26d62d4e109b594320876752d45409b988520425e6315032d9185520c67860551219b98b54cc34d4354843b958642483345488510d914b515026e62150308f992544435561d4d109718d544826f6254d109799453486776154c42d9546210826e62942439b994424865d6395121cd152104425d65d0c30d9544210834d528c8319dd8553483546154c42cb150524427665d05219b195324866f6550842d3d4f524434e52cca30d350d520c65d6314b109b98b548c34c53149409718d5190b5553544409b588544c26d62d53109d98754c825e6590d30b3588310c34c53d49109e58054086e562905109d587548c26f62543439d594310875853d01409758e54c42b461500409b58a538426d62952319b98b54042e4614c9219b988530433454485109798c52c4355510c6309dd8554482776155131b958a41c434c53d4940b358f200825d63d53209b59621082e662d07319718d544426e62d4c20da1485050ecd63c82209d98650ccb4e5394b41f18c831c867561943329d594410425d63151209b1895190f576154c42d314d324866f6254f409798
  | 2 => 0x10940006404020090c00800005074052080609c202643f0040f09445008000000d02c22024040000000802018030007e000000000100003004000040d01c5d00001010060e00e038590580000005198040803c000040480000000000040240d0040b0180015c32024010300902c1b00c0d0285a034002a81c008020281b004540000405405058060040002c030740500c0e0280000804014000180700c2e000000b802000030580c1a0000240106004118000000000801280ae00003008000001101c160f001014010a80003877000060200c05c020100f0240400000000000200202000004000803d0141306800000ec008000d40a0000016c090080a000020740001c000000f0100000c411b0010400406c08000083c8070044002c07010000681d005950245e00003000000a4420000400c00003655210410b9185320826d6215330d354d521026d62d523097d8d5190acd6210e309798c540827965100309d98754083645214543d954b41043576154f41b3588318c26d62150109d18553d023e6414f21b918532c863f655084297d8d544426d62150309dd85534866d65108209b58b54042766115230b6580310c2d86050c439d984548836452cc5318fd95401026f654842197594430c2cc6250c31d914851502cd6310a20b518d214427561150209d587540836732145329b988530876752145409798e548866d6214530cd153314423e65151109b596520425e63951109d987540866f62551329b58a53902e5620c721b518d21c426d62947408f99053082786055131b358c420ca7561150309d587530832f5414910d914831442e56190b209b58a50cc65d6315020d9508514ca756194243d9d0951082d86050d30c7150534426e65909209d5845050b6452d45439718d54486cc6250f329b988535063f6454d10cd58454443665294630d314e214866f62551209bd89508c6d4614ca30d98c9510825f63540419bd89544c23d6414c109b98a53442746154d209758c548426e62150329b988514c25c6354041cd550410c67761553329bd8953c427a60150319758c54882cd63108208f592534434d6214d219d1855310acc63484219d18553c827661d5230c7153534427661d4c209dd85548826e62152109d984520
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x2c020102b080c000100000426801511c5530cb20c88c430aa6216446218553c8322a9ac321641511cd51084208caec29062885487050d520c6a239ac229221891915244010a88e6b0ca5a0d487050d5210f0a2a0c690a219154d619084289aec2988490cc47358642087122a2c418a21541c14314532a8ae6212a21064453185324866238ac6210658915162905108ceeca968218e456354720082a438286a9661131d95348720
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x10008448754d6190b20844865cc42544208448758d51c80208448754d6190842
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 7 => 2*((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s4K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/270+packedAt s4K5 (17928+(h % 270)*10) 10) % 664)
  | 4 => 2*((h/249+packedAt s4K4 (20482+(h % 249)*10) 10) % 539)
  | 3 => 2*((h/22+packedAt s4K3 (1225+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s4K2 (240+(h % 8)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfff03fffffffff81ff83fe07fffffffc8e3fff
  | 1 => 0x3ffc07f07c0fffe0ffc3ff83c07e07f73ccc7
  | 2 => 0x3ffff8007ff03fff0003fffc007ff8383f0f8
  | 3 => 0xfc00000007ffffffffffc0000007fffffc00ff
  | 5 => 0xfffffffff80003fffffffffffff80003ffff00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1811850a20420880318046215471629406155b
  | 1 => 0xa8a29314288e519606941a691892aa5932ccc5
  | 2 => 0x52c50a26b5143baad0522d759124db538370e8
  | 3 => 0x628e2c58c628a34d6b5a814402471c63dc00b6
  | 5 => 0x830830608430c2718c63318623801002e9aa00
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaa800a800eeeaeeeaa800a800eeeaeeeaa800a800eeeaeeeaa800a800eeeaeeeaa800a800eeeaeeeaa800a800eeeaeeeaa800a800eeeaeeeaa800a800, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40483
namespace PEqualNP.Outside.L_meta_40483
open PEqualNP.Outside.L_meta_40483.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x483ed320cbbc6298df54e31bf280857d53d03ea42887ec4210bea90817e5190ff280205f54841bf28e877e50c86fca8197ed0330fa88021fb5050efca7a0df94630df214817c53886faa0195f15031bea86857e54c42f8a9887d0c710bea8e41ed528c2fea8187dcc721de210817d5490bda85905f94b30de2a2417e510c2fea690df94331bfa9c437c53482fea8107d94642bea96837c54cc7dc40905fd5232bf284637f54442f8a098df14143bea9421df4350fec83885f94a42faa0a63de434c2fca1214fd5120bfa9c417e530c7be65195f55243bea92217e5210fdaa4207d8c610bb28e617d520c6fca2085d14532bfaa241ee21487ee8398ddd4520fd90441f521086fca7a077cc832f7a12436e528c2fea2997d54432f7212415e53d0afaa020fed0030faa8c85f421042dca4205f55130bea84637e544c2faa5a1dd54420bfa8a61f541c42fea8085f94640bf29041be40502fca9987b48020bfa9e417e50ccafca721df94d10aea98817c544c6faa1a1d7d4d40bea9c41f441486fea810fdcc510fa18e43f621c43da4210df55332fc980617e53103bea6905f55121fc200617f52042faa1a0df94631f790e417c54886faa2195f54743ef98c637c52503eca3185f94b40bf296217e530c2eaa3185d54443bf29843f7410c6fca5185f14c10bf28e817d53082fea818fd90721bea8861f441cc6f8a2986f50842bf298217f504cadea498df94441bea9a41dd53d0afca4207d54440fba0c83de434c6eaa3a15f94821be29a437e50d06fca5195f94832bf2a0617e53483de84a15f94e20bf2a241745150efea7885f14d40fb988437d51842bca620dfd5230ee980617e5410afaa6087b54810fa18a21f6414437a8621df15030bfa94217e54107be87185fd4931b729483f441043ee4310fb0cb20ee98861f451502faa3995f54e40bf29e21ed21482faa710df14930ba28a416d52102fea9905f95031bf2a2637e500c2fca3995f94421bea8e817c544cbea8390df14532bf296837d54083bea690fd14543ef21e637f53482fea6105f14121bea9883f651102f8a790f78ca31be290217d53c42fca7205f54e10fba0c43f531842fea998df94720beaa4837c54c86faa2107b10b21bf28081ee320cafea898dfd4520eea1a61f741507baa620df14e10f7294617e52843de84195f15210b6a902176510cbe86210df54f41f621065f840cc2faa720df95331b629287f541442eca321770ca31beaa0637651102fca8887d54630bea9663ec5250efca598de14143ae29a41f621442faa521f714d40ef21e61de53103bca7a17d8c521bea8c417d5110eeaa32177cc430bea8c81f55110fde4310fecc130fb188217551103ec8210df54630afa9a43ed42482faa9087750d31f7a1643f651082faa8196fd0641bf28c437e52907d86510df54a31
  | 1 => 0xc42902fea6887b94a41bf28e615d53d0be88218df94021beaa2417f52442fea0a1df54742df212857c52842fea81977cc030eea1c655e53103de4210df15120be29e21ef324cbbe6218dfd52219e2a2417d52902f8a8197dcc631be2a043ef328cbde6510fe44010bf28c83de304c2f8a8887dc8610fb208837e5190afaa198fdd4520bf288657d51103d885997d50441beaa663de320c2faa018df94010fd180617e5410efea8985b54a41ee218617751502eca3a15f95010bfa82637d50886faa5987b94810fba0c21f551cc3de4290770c830bf284437c52442faa2215714d21bea8c857c548c37e80207d94432b7a9281f920082b8a6a0774c630bf2a0437d5090afea9085f54b10fa98a43dd43cc2faa7905f14d42f7904417e508caf8a8107b0c920fb08221f441886f8a9907d4c410dea00817e50082faa7197d8c431bea8e617e5310aeaa2197d94443be28a85ef42ccafca890df54d21fba8a657c54cc2eca2105f95220bf2a0417e53c82f8a7905794f10eea1887ec524c6f8a2a05f54843bfaa6617d52906f8a8085f55330bf288817c53087dc859057d4d20eea18656e52043ec8318df94f42bfaa4417e500cafca4215754f10bea80857f53042fca121df15130beaa4437d5090eeea2a1df55132bf2a265fb10443be63185fd5121dfa08837e510c6fea610fd48710bf290637e5290efea4a07d14532bfa9a817d54086fca3195f94e42bfa92836d528c2fea4985f54d10bf28685f5418c7ee20085fd4142bf2a643ec42883e8a2905f55310ef190635d53107baa7885f14141bf2a4437e54843daa520df94910dfa1887de53c43e843085f94e10f799043fa20083ee6298dfd5231fb18c437e53c87f661185f95230bf28441ef524c6fca408770c831bf28c417e54102faa9907bc8020fba8a87ee4210afea7087d90531ef298837e548c6faa9205f95320beaa021fa10042dea4a1f7d0e43dea08837f544cafaa5a05fd4542b6292637d53c86fca018df55321bf29c437f5250efca690f7cc230bf298837c53082fca518fb10921ee19461dc438c3de64905ed4143f7a14417e50902fca621dfd5321bea94617f50486faa510df54c40df21a87dc53482faa918dfd4540f7a928777514cafca3a17dc8521beaa4417e51082faa321df55232ef19461ec52502fea5887dc8410bfa9e43f551082faa9187b48720bea9c6176518c3de85215f14941fa98863f731c43d884105f94210be282657d520c2fca420fdd0521bf29687ee521037e81205f15220fda02817f50506faa610df14931fba08217e50907bea6a077d0c30bea9c857e520c2faa3197d10610bfa8a87fb20482f8a890df54332fa98c43ed4210beca3a15b14940bfa9a837c53506fca9195f94442bf29c83bf4290afaa6217754c40bfaa6657e508c3de84105f94c20bea8
  | 2 => 0x5b0200000c040002e024000700936c38058150641205003000010640b010001682d0083101c05008290140d0185f1304a00c36016580380700c1a0004801802044050040f0006a0300f010260181400c60020100001c00000006330042c0000900012008090b0000000600002024b30050f0141d0240105c05008ac0280b04c2b04c130b89801400009ac0040000c0008809000040a40f048001d07a05c05388003480c3502b098610041f0a0160103a0080105c01000090080000001a20460100005c13190010000901c1b00014004040040414c0901400000000000000000010471e52105cf2018050080103c0805408004550147f0201400000004220080400800074000001b018020082f000050002202c0a0fc2e00c14000060001f0001001c02004020e8040340009c00000dc0002c0000a02c00004290063f094724140c004260f8001202ebe29c41f710842fca5207d94730baa8e617c53443bc64995f95332df20a837d508cb7e8721f74c832be296217c548c6fca020df54810bea80437c5150efea9885d14540f7a9281765110fbc87197dd4540fda04817e530caf8a0a15f55110ef218877c54ccaf8a4a1fbccb20bf28887bf54482fca021f714d21fd200817c51483ba8798fd50421ef21865ec32087eaa3a16fd0842beaa2637e50d0efea6a17d88421beaa0617d52882faa021f74c431df210817c548cafaa190df54f42fc28287b
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x538863f6454d20b3189310c67661d5230d514f515025d6394640d554e41c426e62943319dd8554cca5e63d4b109bd89544c75543544329b58b540c65f654c4319e580540ca7565084109d986534836551c80209dd85544c25e631531097d8d50c867b60551219b189540c35453d05219d98653902cc6348520cb15142482746155130d318d52042776154910b6580320c2766194243d9109510832c54485209bd95320cb555394440b6181430ca6e6215010b3189310c25e6590d308f191524425c6354042d5d4c515027461551328fd954310e7761548309ed9510042d463484219bd89540c25e6394d219758c548426e6294740b5587308c27a60d4c219758e544866c6254c41d3d4c324826d6215210b558c410426e65cc9209b58b54cc26f62551109d18554882756194e20b9584328865c6355120b998742c874d520ca309d58652d036742544209758c548823d64d4b10d5d4f514835b43141438f99254482e56290721cdd50514825d631522197d8d529073754d4520b618143cc6d56310431b9189314867661d50209758f528435553947429b18953c436552546309b58b53842746154a4397596430ca7b65480209b594320866e62d5021cb15242482e4624c6219d9943144274615503097d8d544866d6294740d3d8d520426f6254c41b6181438cb646154a419b988520432d52908409d584524c2796510030b9189318435753145209b988548c3645214543b5584438c26e62d5310f10ca318866f6254d1097994534867960d52319d587548c25d63953209b189544c67761542329d984540c755535474297d8d544c26c65509209d58654483735114143b358f420ca7761550309d98654482756510410b558f10042776154d209718d50c86756194b43d3d4c525036452145408f990530434f6254f10d358b534826d62152309d98454882e5610c9209d597410c7675214540d9549511025d6314b109b98b548c23f65500409d584540827561152209d987540ca3d6414c209758f54c8274654c5219b988530426f6255331b958a41106d563107318fd91524434e5354840d554c31c431c54d4d209d98453c827a6015032d550d51cc2d86050d31d318953106d86050d309b58a544c66e62d4c20d9d095190a6d62150309bd89534867661953209d586548cb645290531b5584320c27665d05219d185520c23d6414e218f99352c43665254630d554d41107655148020d3d4f52502756194332d58c8514ca5d63951209d59431086766114c2097d8d544425c6354a418f992534826e62d53309d984548c34e4314931b998742cca766194b439d98650cca766510521dad485050ed4614c8329ed81544c26d62d5230d518553c42756114d429b594420826d62d50109b18953d035553cc710b958642c827465485109e58054086e56290510
  | 1 => 0xe7661153309d586534834d53548409dd8552902766194b40b9189310433454145209b98b538426d62d52319bd9520082766590510b518543cc6d56110c30d318d52906746154f409bd8954842cf6250c328fd95411065c63543419718d520427561d5032b958a418c677654c4109d597410426d62d4c109798e54c825f6550c43b958a41086786055131b5185430ca5f6354910c7d5353482776155220dad4b5050f2c540c9209bd89544ca746154232d914b515026e62d5010b5185438cb655294630b9586424835453105219b99742486756510431d594d51d0b7051d41439798c548435453c852197195434c66d6214c109d984540cb4c53109219d9845404277654c4319d18554482d563106109718d524427765440109758e544ca7661d5021d590d51cc274615404297597430c25f6354a40d9d4b5150e6f6550842d314c525026e6215210b318d21c825d6510c309dd85544426d62141419e983548ca3d6414c109d185529036852141439d597310865e63d4a1097d8d50d06776154042f10c8310863f65508429b98b540c67561953209e583530863d6494d2097d8d520436552d0410b558c41486776550421d314f525026c62551309d58653902776154d21d954a310425e631522097195434c2756114142cd15351482776154c42d554d511036452cc53197d8d5010a6f6548421d994a51102746154c429b988540c35553904419798e53482d463485109798e54487555388710d354e521026d65948109d5865090e5d63944109718d54487673214532d9548210436752145439d9845050a776154a43b558f108436452505319d584540c36752d4540d590d5110f54534c521d314f424866d62943319758f54c427661153329b597420827561d4c20b518d21c425d63150219dd8553d02d5610ca309d587540827761551209798c54442e5610cb209d185534827661951329718d544425e63150219d98754cc26e65909209e980540866e62d52319d984524c23e6414c209d996314867b6550040b9185320ca5e6395120d3d8953d0a7565904219d984540c31f5414d208fd91534434c5388521d554d21c435651cc6309bd8953c426c62552109e983548c76561149319798c54886746154f209d58453c827761551329d586544876852d41439758c540827661d4c209d584544c27561153329dd9541106cc6348421cb550420ca7661d52329d984520426d65108329d987530425e6315031d5185531074d4314931b618143cc36742544329dd8553c827765484219758c54c43563294630cb588544825d63d4b109798e519027b6055131d5584534865d63151109b98b530425e6315020d514e314865d63150109798f54c836452d4543d9109510cb5432946309798c540427561d53309d587548ca766114d428f191534426d62942438f99
  | 2 => 0xf000000080003d9000c03048081000409c06024000080107409004000000f000010002701c2300c0003000000000802c000000000216c0502819044530000e014000000012c070344d020000080c01c0f0080c018050c8000a0000300f1381100003020030440a02406038040e0010000200001028030280502c270340001c03030040000100c010800004c3139c0b0a4010e86800801000170b00100000008000140002c01014000140000000004000001a0200802401000000700002c0022c02030050185a0086f0005500c4b004020000301c0400818200010000100000000320082a01c020003905c340206102800014000480e0040409400000010000901c002782500000088030a4001517d0000220000014150040d0000500c3208c050000008800000030040505c000140100004150001de7561d4e20d550d5110e7661d4e20cb1522048279658401097d95300c26c62551109798c52c427960d52329e181544ca6d6215010d514c514836552c84109d58754c827565c84109d584540cb6552104109bd89544c2e562907109b98850507565394742b95864210b5453d4520b9987420cae56290531b618d401034f6254c41d9185520427465505109d18554cca6f6254f40d3d8d529066e62951319ed95300c2776155131d554d41c437351d4143d314a314c7565354440d394e521036451c8520dc1445050e5e63150309e181544867561951329798e510427665cc510d590d510ca5c6354a40d9cc8514826f62551209ed81544ca3c6454d20cb14a40502746550531b9189310c71c5414d208f994544835653944409d984544c26e6215020b3189318c2ac644802097d8d544826c6254d10d954a51102766114c219d58453082d563106219d596310426c62553319758e54c86756194d10d954910043586054c409d18550d0e766588510d514c515025f654c832d9949511027661150209d996414c6756115330d90c8514835853d0140ab18940102d963103309d986538826d62d5310d318953c425e6514d20d954b419067761543439d584548c2d561cc030d9549310425e63d5310cb153214836552c40109d98754c835753d4540d994a518c2d5610ca319b98a5090f2c54cc9209798e54c86766195232b6181431
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x58400000025848030c59158d5210410aa0e0a1aa3985447354821043122a2c321241541c14354432c8aa6b148388644631855290722318c2a9021541c14354443c8ac6a9620084557614c4148722310c2a9e21311c96310431a88e4a986388644621855310712322a290041195d85290531a90e0a18a498e4453189314866239ac5208438315063485208c8eca9262086455358a41107122a2c219241151d95348710
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x8448754d62907108448758d52c40108448754d62904418448758d5210410
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 6 => 2*((h/27+packedAt s5K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/263+packedAt s5K5 (17928+(h % 263)*10) 10) % 664)
  | 4 => 2*((h/249+packedAt s5K4 (20482+(h % 249)*10) 10) % 539)
  | 3 => 2*((h/15+packedAt s5K3 (1225+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s5K2 (240+(h % 8)*2) 2) % 4)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfff03fffffffff81f07ffe07fffffffc1e3fff
  | 1 => 0x3ffc07f07c0fffe007c3ff87c07e0ff13ccc7
  | 2 => 0x3ffff8007ff03ffff803fff8007ff03e3f0f8
  | 3 => 0xfc00000007ffffffffffc0000007fffffc00ff
  | 4 => 0xfffffffff80003fffffffffffff80003ffff00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1811850a20420880300c46229471651406155b
  | 1 => 0xaaa29314ac8e53960a361b6a5892b4db12ccc5
  | 2 => 0x50c50a26311439aad2802c731124d6516370e8
  | 3 => 0x628e2c58c628a34d6b5a8140424718e3bc00b6
  | 4 => 0x830830608430c2718c63318463800082d9aa00
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfaeaa800faeaa800faeaa800faeaa800faeaa800faeaa800faeaa800faeaa800faeaa800faeaa800faeaa800faeaa800faeaa800faeaa800faeaa800faeaa800, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40483
namespace PEqualNP.Outside.L_meta_40483
open PEqualNP.Outside.L_meta_40483.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa28214004000008904000ffd5001fd31017f14005fe52007f04001fd21007f88401ff21007f4c005ff53007fc8003fc4000ff90803fe41007f8c803fc42017f94005fe53007f08403fe43017f54805fc5200ff10405fd51007f08003ff41017f14c01fe2000ff90001fc30007fcc405ff5100ff50803fd41007fcc803fc43007f44005fd50007fc4003fc54007f84005fe51007f8c403fd4000ffd0c01fd20017fd4805fc51017fd4003fd4300ffd0003fd5400ffd0801fc3100ff95001fc32007f4c801ff30017f54c01fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2c4000fbc852001ffaa388003fc6348007ff3006204ff0c0100f7fc8010867fd434c03bffa9e602aff5413103ffca510813fc50480057e32e6404ff0c210007f86488003fc320c037ffaa46011ffd4920007dec4988d7fc53cc817ffa8c2004ffd9410007fcc298003dc320c40ffea904200fb48720117f8a91080fff4104001fe9886027ffd4c3101ffca310823fc6444067ffa046403bf9862003dfcc5190a3ff54cc45bfe29e6221ff14d21027fca1100c3ff54cc801ffb1a4030bfd933217ffaa01902bff418400ffe3246401bf1911003ff8a419003fb304c0637fb226408bf5861004ffaa08800eff6508409ffb1c4010ff591200a7fe819000ffe41084037f3244228ff59331007de651900fff608c4097f3046204ff9022003fde4390073fe538c013fe292200aff15210147fa879886ffd438c001ff10a6004ffd402008fdaa490003ff6148001feb126201bf99330025f8c908003de328c409fe3106004fb98a3018ff8c89900fff648c465ff29a6407ff10920007f862900b3ff528c441fea1a4200bf58c200effaa3980a7ff644c461fea1e6434ff14232127fa879080ffc518840bfeaa02013ff54a20087fa80900abff514c40177b126200fbccb20027fcca10003fc604c85fffa886404bf98230027f8c91803bfd4108007fe31e2017bf59430007ec42880aafd654c4017fb026400ffd8331005fac5080b7fe52cc415feaa42000bf58e20007f8c39800ffc640c453ffa0a6212ff90620087fa8490002f56108009fe182201aff94d3018dfac71900ffe6408407fe3004200ffd853001ffcc1108bbff410c8017eb0e6406ff94810027f8c508003fe218c009fe2864004bf18c10027faa01800ffd608c445fe21c4203ff9461001fec8388003fd328400fff31e4004ff19020007fac598013fc6584013ffa8a2000ff4c8100f7fe86108c2fd64cc811fe2a22003ff9441005ffca508013fd2008067fea04640dffd4310007fe651080fff600c40ffe2146434ffd4e32005fac69080ffd608840bfe2a02007ff0862003ffea519023ff4144001fe1966204ff98e2010ffca690813f5618c0077f30c6403ff4841001ffc4290812ff650404fffa806204f7cc03003ffa641900ffe3104061fe3266421ff995210bff8a418043fe544801f7eb284011bf5952003ffeca190a7fd544c447fea9c421dffd433001ffa838801ffe64c84037f3224204bf1961003ffa8519013fd6584007fea086210ffd0920027fa600801ffc63c806bff32e6404ff4c21003ffec99000ffc65c4055fe2826214ff5032017ffca21901fff52c800ffe2164012ffd0e20077fc8610013ff6484007ff18c2035ff94f32027f8c218097fe53c8407fe2882008ff55110177faa81901ffe320805bff29e6203fd0c42101ff8c588013fc650800f7fb286404ffc8020
  | 1 => 0xffd50884037f3202004ff9433001dfec78800ffe410c40fff1926403ff592210b7fa86180c3fd41cc8017ab0c6007bf18931007fc421807bfc40084077f3084204fb588101a7fca319013fe2008009ff3242003ff99710007fac198813ff650c001ffb126207ffd082103ff8a510803ff314800ffa9084200bf58f21127fa839080ffe41c4021fe21a4000bf5881003ffca59001fff21480057f3282004ff5863001ffcc610813fc6108057ff21c6229bf59131005fac7900a3fd41cc401ff1926011fb9492000dfcc990802fd610c013ff29a2003ff19231107fa829081ffe4208401ff1946207ffd9321097fca910002fe63c4009ff1824007ff4cb20027fac70809ffd520c407feb206203ff087100cffc8698013fc6588007fe9882004ff98a3010dfaca90806fc644c82bff28e4028ff90f3103df8cb90857fc51c801fffa984001bf19332097fe851001ffc618c8017eb004204bfd9630007fa6190003ff3248023fea9a4004bfd9610007fa6518063ff43cc001fe98c2007bf19720047fac888003ec624c467fe21c6400bf582310d7feca9800afe65cc401fe1902003ff99310007fc6390077de53cc009fea80201dff54b30007f86508003ec3288413be32a200cffd0f100c7fec99800ffc3108407ffa8c4204ff18620007fa6510813de304c065fe29a6407fec812015ffa87188c7ff544c807ee9886230ff90f32027fcc610013fd1004001fe98c6020ff90d210edfacb9806ffe438c009fe204401aff14d3003ffccb90013fd648c009ff1062004bfd901003dfec919047fc65480097e3206006ff14810027fc2088002fd63c4007ef98c6200f718d21025fcc10801fff328c869fea9c6403ff9943110ff8ca90813fd610c00fff1964224ff90f2103ffec390006fe6484007fe2084204ff54230025f8c09901ffe428801ffea88401af754d30027f8c908003fe32cc425fe20c4004fb58a30025fcc008093ff54c8401763126207bf98831027fec31809bff430c4117eb222003ffd931003ffc649085ffe530c009fea842014ff10f20027fc619002ffc52840017eb0c6400ff5853203ff8c019002ff624c40176b102000ff98520087fe8090003fc3188007fea886200fecc23001fe86388006fe648c833ffaa26004ffd8c2003ffe439001fff32c8033fe2a2601aff145300d7faa098002fd62c400f7e3264003ff8c62103ffaa59000a7c6544001ff3126007fb94b20007fec099013fc6304045feaa44202bf99521025f8c61000afe650c007feb2c620dffd4f10007fe6390003ff63440017eb1c202aff14931007fa628807ffe50084337eb226004ffcc22001ffac81081ffd21c804bfe29e4215ff54f2001ffea20801ffe42c8039fe29c6000fb48520005fec6880a6fd638c409ffb246018ff19330027f8c818003ef3248009ff3
  | 2 => 0x3106dfacb880d3fd508c8097fb284007ff0cb2004feaa28801ffc528c847ff29c4207bf1903201ffac41881ffc64c8009ff9804003ff58031007fe408803bfc4108009fe182401effd0021007e8639086efd648c031ef21e6003ffd922101ff8638801ffc52c800176b14601cffd4e30057fa870801efe628c0097fb1c201fff14021157f8a698802fd600c44dffa106233ff15232007d86490013fe6584007ff3246203fbc8421025fcc010813dd300c019ff2162021ffd4d21027fc2008063fe54cc00f7f310401cff5463008ffaca900a7ff544c44bffa9e4210ffd052001ffaca10857fd50c80077e3204203ff9963116ffea798802fe63c84077e3162025ffd4721027fcc808003fe60cc45ffe2986403ffd8e21007f8c59800fff418846bfea8e6416ff90c30005fcc61086aff654c007ff1082025ff5472101ffe6310803fc624c009ff2004018ffd0b30197fea099003fe320c0097fb246004bf1922001ffe43108bbff540c85bfea8e6209ff14d1016ff8cb98813fe5008069ffa8c6400bf5822101ff8cb18887fd5148409fe2066007ff98632027f8c51809bfe420c40ff71906422ffd022114ffa869880ffe2184001ffb1a4214bf59320107fea890823ff5444001fb9884203bfd962101ff88388006fe64c8009ff3282003bf19431007fe6188003fc624c40ffea90401eff50021087faa8900cfff418c841ffb224203fec4110027fac4080d7ff65cc807fe98c4228bf5933101ffcc5188c7fd414c801fe10e6004ff90310167fea118813fc638800fffa904202bf19730177fa861901bfe530400f7fb1e401affd413003ff88410863fe42cc0016e31a4215ffd472001fdc429080ffe6508435fe32a6004ff99020027f86190023fd4344043ffb2a422cbf59631015fccb1000fff6408401ff31a4031ff50d3209ffea51000eff6308417ff29c201dff9973003fd86590012ff65880017fb0a6000ff5893001ff8821880ffd418c41bfea962007ff949200a7fe8390063fe41cc0077fb2e2007ff50821025f8cb18012ff650c01dff2084031ff90d320cffa8298003fd324800ffeb2c640effd0c20027fca188053fc54c8067feaa46403bf98730005dcc518043fc5448009ffb202004ffd9610027fea118047fe514800f7f3162019ff1913003ff84210003ff604840ffe1944200ff98d10015fcca10003fe31480237fb2a4000ff4cb310bff8a618063fc41cc009fea044007ff10a200c7ba8798012fc648c043ffa824201bf992200dffa831809bfe400c411faa0a2011ff14520007fcc399013fe40cc001fe9824004ff58a30005fac210003fd21480677eb24641eff950211affea199002fe634404bffa864216ffd503001ffc428800afe6584025fea14402aff94d31025fec910053fd54c800fff2946403ff9922113ffca01888
  | 3 => 0xe3224004ff500201affca19908bfd438844bff2864207ff5903201df8c81881fff520800fef9906421ff94121187fc8199013fd208402ffea886007bf18930005fac39006ffe418c05bff2866213ff94620025fcc01880fff6588409fe2862028ff90331027fac818093fe40c8419ffa162003ff8c421047ec82880bfff500c80fff3286426ffd0031007f8429801ffe5288053fea0a6203bf19421015fcca19057fe53c8039fea946007ff50820005fac318003fd3288047fe29c422eff5043210ffaa490813f6610805d7eb206400fd4871004ffea088003fc604c407fe2884203ffd903103ffaa590856fd65c8001ff1902022ffd522106ffea58807bfc4308455fe32a6205ff90c1001ffaa3188d7fd52cc85bfea966203fd8c43101df8cb18802fd60cc433ffa1a6007bf98a3115ffe871880ff651c4011fea0a200eff9502001ffec61081ffd618c809ffb204007ff19321007fc6508033fd40c40057e32a6000ff8c620057fc8708003fd3148009ffb206030ff9073201ffac988013fd6488069fe28c6407ffd8f21067f885880bffe530c801ee1946207bf98b30007f84318013fd3088009fe1062007ffd0820005fac69000ffe41484077f30e6403ff90731027fe4008003ef32084097e3026204ff14220025f8c80807ffd530840fff9904200bf58a3003fba641900efc648c407feb184204ffd8e10127fe8790813ff2084027fe28c4004ff1433001ffe4210876ff65cc0037e3226007ff0c92003dfec990803fe328c009fe2004018ff5033003ffcc919003fd60cc819fea162003bf1971001ffe621080fff620c40bffaa02004ffd86200effea59800afc654c425fe21c4000ff48110015fccb1086bff534c0037e3226232ffd95320dffe871809bfc420c44dfea006204bf1902016ffacb9886bfd514c001ff1926220ffd0d210b7fa82180a7fe434c44fffa906230ffd0f32027fc6110003fc60cc451ffa1e6200ff18121085fac510013ff500c00dfe2982000bf98e21197faa29901fff218800fff2104001bf99032177f8a819047fd504805dfe200640bff14e10007fcc0988bbfe430c857ffaa46207ff19432007fe65100b3ff538c401ef1906207ff8c832067fca9880b3fc538c44dfea106203bfd94310c7f88598063fd42cc027fea9c4003fb4842114dfec8988a7fc644c453feb226200ff58132027f88188003ff3188001fe98e4002bf1952114ff8a89880efc6588453ffa126207bf19432007fc648802bff54840077f308642dffd4331007fa4310003f731c4011ff21a2007fec8220027fe8110003fc3108001fe1926200ffcc531137f8801881eff658c807fd8842026ff95031015fccb18803f4614c8037f3206205ff50c1003ffcc21901efe620c8097e3284007ff1903201df8c290047ff5148041fe322422cff94e
  | 4 => 0x813fe620c001fbb0a6410ff50d20007fec59802ffd5184057ff2146201bf9931001ff8c988093fe54c841ffea984017ff54830027fc408801eff65c800ffe294401bffd0a3001df8c910877fe52cc009fea844034ff14e32027fc8098006fc6448441ff2a24200fd4c43101ff883908c7fc414c8037f3204200ff0c5300b7fc821800ffd4188461ffa166401bf1933001ffe4388033fc43c40097f3004007ff5932003ffe859080ffe310c407ffa084233ffd523201ffea210812fc6204055ffa9a6204ff1023003fee4290867fc414c0077fb262018ff15330027fc618801fff608c823ffb2a4024ff10321147fe8598813fc3088065ff2826400ff58b31005fac31001fff63c802bfe29e4003ff1443103ffcc9900abfd514c401fe108601bff90a3003ffecb19003f43144051fe2066230ff10332007fe658800ffc418c401ff10a4018ff10f30007fc639801ffe65c840ff6190422fff5443209ffea310022ff6444001ffb126004ff58e20007fe6098037fd53c4001feb024203ffcc710007f863180cbfd524c83bfe28e6014ffd532019ffa8719083fc40484057f32e6400ff98132015fccb19003fc614c80fff2166403ff48710027fcc50801ffe42c846bfeb2e6420ff5912109dfacb1000ffc620c4017f3184003ff0c721137f88618827ff534400ffeb246407ff90921007fcc5988a3fe42cc4077f30e4004ffd00200b7fe8618013f6618c001ff3066431ff9013201ffcc71080ffd650c40fff304641dff54f30025fcc199013ff5004065ffa9a6400ffcc831195feca99027fd514400ffeb1e4004bf18e1017dfaca19002ee6204029fea1e4003ff19621157fea09886ffc418c023ff29a4003f78c53103ffec8190b3fe508c44ffe2806204ffcc230007fe6598002fe6384009ff2826004ffd4210105fec89080ffc31484017fb1a4200ffc873001ff8839884bff418802d7eb20601eff5502113ffaa618813fc500800fff194422bff90231187f88399006fe64480437fb2a4204ff19010117fc8710803fd21cc0037f3246203ff50410047fcc888083fe4048407fe20a4204bf98331005fec090867fe414c007fe9084200fe4c030025fec610003ff31cc063ff20a6403ffd8b1001ffc8318803fc31cc0017eb0e6007ff4c82118ffcc899013ff628c06b7fb2e642cff54a31057fa8308002fd62cc009fd1806028ff99331067fe818801ffc4208035ef29a6007ff94821005e8c299012ff640c00fff10e4001bf99110015f8cb98863ff40cc007ff2884212ff152200d7faa49800ffe41c8409ff2846000bf5833201ff8c61080efc63c400fffb246404ff1863003ff8a4900d3fe538c80f7f3142007ff197200bffea618013fd2004025feaa4401eff15021027fc8118013ff610c00ffeb2e4218ff5933000d78c8900c7ff434c8037
  | 5 => 0x8b3101ff8420808efd6588455ff2826202bf99730197fea499077ff51cc051fea066233ff5063218ffa84990c7fd404c8097fb182000bf18d10007fcc299002ff624c00fffb2e4207ff109320c5fcc618002f6618c00ffeb2e4004ff0c310187fe8199077fc52cc027ff29c401dff5433001ffea218803fc6344009fe9804029ff90131005fec29000ffc2184033fea026003bfd9021027fcc408093ff40c8409ff3246016ff90830007fcc49881ffe5208007fe300622fff94032087fc8690012fc650c065feb2a6404ff8801001ffe83880a3ff40cc4017eb1c4207bf1932100dfcc998803ff62cc447ffa9c4204ff996300c5fec998083ff404840bffa182025ff143210cff884980bbfe400c80fef1926404ff9411016ff8a19881ffe63c8435ffa926000ffd873203ffa64100abfd524c409fb8802004bfd8e20027fec210063fe64cc0137eb2a2003ff592310a7fa8390003fc310c061ff3266407ff8c92001ffca2188d7fc50cc80ffe190420fff94420027fc808809ffe520c4077e30a640eff1502001ffaa31082bff4384001ff31a4207ff5872001ffc8298893fd40c8401fe306642bff50a31027f8c408073ff528c019feaa62009ff549100cffa84980c7fe544c80ffea906421ff14121147fca99881ffc424840f7f3106031ffd0932027fc4108067de434c01bff2962007ffc8120027ee21080cffe438c8017eb086404ffcc030137faa81880ffd3108407fe3046200ff8c42016ffea598887ff5248401fe30a4032ff19532027fa81180bbfe410c833ff2a26031ff5913215ff88118867dd434c001fe30e6407fe48020007ee6318806fe640800fffa964207ff14821007fa6588063ff41cc03d7eb204203fd88421135fac81880ffe4144057ff2a46229ffd0d31187fa8199083fd404841ffe2884000ff4cb3003ff885990d7ff53cc80ffe2164207ff5832105ffea70800afe65c406bffa966428ff10b3101dfcc31081eff640c863fe2026404ff590200dffa8518013fe618800fff3064207bfd8f21005fcc71001ffc61c8009ff1804004ff94030027f8ca18003fc6348407ff28e2008ffd9110067f8a98800fff6508407fe10a202bffd0a31027fcc708013fd658c007fea882011ff14d20007fa631001bff5304061fea166407ff8cb2003ffa8590813ee620401dfe2184004ff18e10005fac418883fd424840fff2126407ff484200a7fc8790013fc404c041ffa124207ffc8420147fa8598803f731c843ffea804200ff4c3100c7faa99801ffc3288037ff2a46010ffd5120177fe861900ffe31c400f7f3102007ffcc82003fbe6519012fc604845b7eb2e6202bf994310d7fcca98006fe644c861ff2a66400ffcc42003ffaca19023ff4344001fe9906200afd912001ff8a388077fe51cc033ff2126003ff9962111ffea110
  | 6 => 0x9fe2042007ff9492108ffaa29000ffd63c406bff28e6403ff94721057fc85080a7fe544c409ff884201dff94f3003ff86410017fe420403dffaa04203bfd8e2101ffca398823fd4244007ff98c6200ff8c630087fcc890003fd3248447ff284422bffd0231107f8a89080ffc650c42bf6a964019ff10d30025fcc1100a3fc64cc4657eb2a6404ff14030007fe6498013fc6488009f71024000bd9842001ffc6290873fc518c05bffb2e622abfd9531007fe651880ffc3104007ff18e4200fdcc53101ffac588013fc2044001ff90a602eff95032027eac210043fd414800fffb2e4013ff14e2003ffec019003ff314c007fe2082002bf99421047fca888023ff4244007fe28e4200ff4853011ffaa51080ffc31840077fb244200bf589101a7faa31907bfd4308451ffb26621cbf59630055fac908013ff3084053fe2026203ff98831025fec810077fd65cc009ff980201aff54d30187f8879900ffc5148425ffaa44003ff14731087f8c89000ffd31c4001f79926404ff58c2003df8c79000ff9100402fffa906000bf5832101ff88308003f7314400fff30e4004bf1962003ffcc01900afe65c8409fea006007ffc85210affea790003ff218c02dfe2106003ff8842101ffc8310803f521440097fb102029ff9093101ffa621881ffd64c8401ff3024200ff48630007fec299093fc43c8409ffb2c4003ffc4110007f8658803bff410800ffe3046404fbc82200affaa39004bfd4388063ffa02642fffd4c32007fe631805bfd420c033ffa026028ff10f311affaa7990affd408c45dfe2086404ff1011003ffe6590882fd6448409fe1804020ff10d21197f8a09901fff60c8409ffb182009ffd951003ffc841900fff658c4137fb2a2000ffccb3100dfcc898003ff31c8409ff2802007ff58432005fac59881afd6504001ff98a4211ffd4120015fcca9803fff5108001ff9924203bf98410025fcc019043bc6448001ffb122008ff90910007fac488097fd53c841bfea862000ff0c831027fc800809ffd500c41bfe2962004ff9421001ff88298813fd6508001efb1a4200ff4c7300b7fca818002fe6304009ffb2c602dff54f3103df8cb19013fe4084001fe1966000bfd891001ff86288013fe6488009ffb244021ff54d21117fe8710827fd6544007ff988621fff94c210cffcc898003fd634801dfeaa04000ff8862001ffec51880ffe4184059fe2846203ff19221027f88018013fe618c00dfea902019ffd913001ffac01080afe6548007ffa086216ffd0830007fac298013fc508c007ffa8e2003bf9863103dfcc59880ff621c4007ff2082027ff14831005fac019002f7614c869ffa846404ff98420085fec89009bfc540c433ffa126003ff105100affea19001ffc63c8417fea942000ffcc1100b7f88218013ff408c037fe2146000ff1
  | 7 => 0x9086bfe514c069ff284642dff14b3118ffaa899043ff64480417eb144222ff95221147f8a99880fff418c467ff2046417ff14430007fe4218073fe518c04dffaa06200ff4c930047fe8088067ff414c021ff20a400cff50f1007ffca6100c3fc54cc80b7eb202007ff08520197fcca99043ff4348009ffa844020ff99121157faca9880ffe518c4057e32a4034bf5963203ffec219077dd53cc035feb2a6011ffd4d2003fee4310877fc53cc00fff3206429ffd0131027f8a098013fe50c80037f3206018ffd533003ffca590893ff41c840ff72164000bf58d10027f8c61006fff418c057fe2a46207bf18f21147fe839881bff5204039ffa8c6016ff10c30117fe85108bbff400c807ffb2e2007ff54a32027fa80080cbfe514c80bfe2102000ffcc83001ff8c1108c3fd64cc809fe3282019ff5513005ffea508003bf644800fffb0c641dff197301affea3990affd548c419faa0e2026ff50c3103ffea41901ffe524c809fea042004ff984300c5fac9980cffe418c807ffb1e200aff10a10117f881108b7ff51cc401ffb0e6029ff99131005f8c69000eff62c4007ff10e2000ff58d210a7fe8790002ff614c809ff1826000ff4843002ffa8408002fe6348443ffa8a4230ffd073218ff8a89900afc654c807ff3162017ff54c3003ffc64108bffc500c80fff2144203ff1902103df8c9190c7fc434c831fea1e602cff94a31085fac890003fd63440017eb046404ff881200f7fc861082bfd428406b7eb2e6420ffd0521007fc439801ffc5208029ff20e4004ff08010127faa99086bfe524c0337fb226003ff98f10027faa01000eff640c409fe2822003bf98630007f8c298003fe61cc007fe28c6207bfd972101ffacb1080afe658c00ffe10e400dff94f100dffaa91807efd6508407fe18c4205ff95010027f841080abfe654c4197eb262004ff59210025fcc1190cfff438c801feb0e6429ff5013114ff884988cbfc514c837fe2a4602affd4931097fc87100cbfd534c807ff3004200bf98f20187faa999012fc638800bffa102003ffd80210e7fca51802bfe54840017fb1a4001bf99230027fec418006fe64cc80fff1944003ff1062115ff88718827fe6544013fb28a2028ff55331027fe411001ffd32c8401ffb066400ff8c53014ffa84988abff654c4037f322622eff50032027f42008013fe640c0017e31a4220ff5512104ffea488013ff62040057f32a2004bf1941013ffca61881fff420c8097f306420affd0a10047fa808800ffe5148401fe9884004ff59410127f8a990813fe6304009fe2002008ff1091001df8c710813ff400c007feb1c4207ff9963203ffca59900ffd628c409ff8802002bf995310fff8a61088bfe408840ffe306422bbf59231007fe649901ffd420c807fe3146207bfd9320167faa718813fa200800
  | 8 => 0xfd923110ffaca9081ffc65c8409ffb142000ff4c931007fa4188077ff65cc009fe202401bff10e30007fe6308013f61044053fe21a6202bf9953201ffca288013fe3004009feb286003bf98431027fac31007fff5308407ffa8c6205ff10c1003ffca41901ffe424800ffe2106409ff94910115fac91085fff510c007ffb04420aff10e1003ffe8519096fd65c84357eb2a6000ff58520087da8490003fe62cc00ffeb046400ff0c9300bffca418003fd3244031fea0e6003ff54421007fe6408013fe3084007ff18a6203ffc8410007fa6298013fd63040017eb106016ffd0430005fcc69004bfd4188029ff2a64013ff5462017ff8a21900fff3104009feb2c401cff54e3001dfecb18803fd3148455fea9a6203fbc8621007de65108cbfd504c801ff9942004fb48020007fe43080cffc408c801ff1962006ff54c10025f8c50800ffc514c46bfe32e6410ff105201aff8a399033fe43c4001fe194620bff54e1003ffac79080efc614c00fffa164000ff4861001ffacb8801ffc524c801fe9822000ffcc43009ffea710006fc64cc401ffb026203ff8c51007ff8a610063fe43cc047fe2844207ff1963203ffc8519003fd328c4057f32e402cff5423108ffcca90003ff30480177eb2c202dbfd973101df8c61080efe6108001ff9864003ff9823116ffccb98837f551c401dffaa04000ffcca30004feca8800efc64c40257eb244016ff55030027f88190003ff20c400f7e3122003ff14510005fac6108037f6544009ff1822019bf58e30007f8c488003fe320c41d7eb204004ff8c03001ffeca18803fc31c804dff2186204bfd9210167f8a518803fd604c4517fb26621aff14930007fe6498812fe600c001fe98e4204ff590100a7da8590002ff604c401ff1966004ff14210007f8651801ffc610c809fe32c601fffd4021007fe42880bbfc430c833feb226004ff9003011ffea510813ff4084009ff2824004bfd8a10027fac50803bfd4308067fe20c6400ff4c83015ff88518802fd6304045fea044200ff98910087dc849001fff320c82fff2886007ff10a21047f88688013fd620c04ffe2986207ff0cb21197fea299013ff4004061ffb266404bf982210e7f8a518037fc53c40017eb146224bf59321027de40100c7ff414c801ff1886009ff19510007da6419013fe4048001ff9922016ff15030027f8a00800efe610c00ffeb006407ff0c92101ffcc81881efe624400f7f3104227bf59431145fcc6188bffd530c819ffaa62004f7cc230117fa851080afc6544001ff98a2025ff543210a7f8839001ffe2108001fe90a2030bf98c320d7fea298013fd300c00ffe2964203f7cc431027fac21000ffd41084637eb226435ff5433204ffaa688087fd5048407fe3284207ff14b32027fc8190002df6348423fea92402dff5433103ff8a4
  | 9 => 0x40941780602e0342b00a0020080082c4a8008038260060001600000804c02000038080330070623c00000001404c7780e00c00019002000038010320020781180900c0140005a05268c020160023051a80f0161c0010040020093d8030100754301e00a0500000a002264060010000001901001c0400002600626c1884d0020042782d0a035c0080d00800c0104b0920984306002e02419000014004380300100040c01a002d201006e00a0004708b1f40b40002300e02810812000604050010000101a00802c07052800000cdc0001900a0147282829a01c04801004004038010580480a8180040c40e80200000c018100020900000103a0003a80c0d4000058000020d8003190001200180200001405827068024098000020007819b3ec0040005c04a0000e1b711e0740004b01ec801b00008e0177384d0000500030a0002d5b78001f20081000c08800c3100a004034ce0722060000804d0140240b800000551108180000000202101c074018970180000008100214400800038004000010220502586908c0106a01d079bb8000032b600d6380f0024840e00700c0d55c0100720183980003e0681e000052030028077c410c0103903a01406816950040018060140800006a0b40201b0010000180080a0080000082266c00c000740080000b80005670000006068018258014181800d008a0608c0000115a0dc068000000000300401c18000001006020e10110a20100101300c0141f07c01001c030033880000004500001c0080303016a0480c0002bc0880000008c008060162b8000000060e0021024f21cd5a31801a080028010180cc0600000806c008001d6008002860001a82a20746a11c030a402800c5404305a0b0010000080000780201e08000ad50300207280100a4518900c02a0544e0000001080305401404c0002007a004000910700040139801c078040000080401620f08a040000020280081980b0040a4028020a2018d800602a1240000c004020043543200000d80100000c0d80000a0000300032e00800005010048030070164dc528050042680000103e0b8030060005fc1505e00c094d387900403c188010862b006f720ca6bc07803350015a804b75c0e00381000e060340120160fc058ba0080000789a0040181002701e3c0000000061003300700000414000000000090000080741c00d01c1e8000930220a00b0171aa0d8120410da0c00000f0c2034c89a702201c0700013a0380282100a0040006b006a440801302a0281e0b413e0700a89619ffca919013f51004009ff3286004ffd9420157fca4988c7ff644c807fe31c4207ff50b20007fac39800ffe514c407fe28c2003b
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x56188630006df635812103cfc7298c20004fd7458331004ff764c521006de4398e20006f5610c620255dd710ca311557c7558131006bd50d912001df673cc421004fd764c91004e7e76d951001eed715881001eef3158810006dd4358e2001eed3158810026f45058420006f56118520024fc764c420006f5611853003dde73cc93224df775cc710006ed6248430006f7610c520004ff7558e1003eef63ccb200067d64d9510004ff7518d10026df7358e10004fd75d8930006df7018d21256ee2118d2103eee624c810006ed7298d20006bc64d8d20007d463cc51003cfe7298c20006bf644c120005f572cc710006ed5458a3001edc3158c10005bd7498520024fe764c81003eef60c8520004fd7558b31006ee7458a300057f7558d20006f465d8532004fd74d8d100067f72d9510006de63cc721014fc7558c10006dd630c62025edc10d8d212eede72d8d2103ef43298420026de3098c1001ede3158f1001ed43158f1001efb7058031004fd75589101e6dd620c831004ff7458d21006de634c72103ede3258c20006bc6498520004f77158d2103cfc7258f10007e4724c431024fc76c851003ede3298f2103cff76c86300067f650c910006ef620c931007e521c831003cec7258d10004ff75d893100cfe7498e21006f553185322d6bf20d91200057f7558910014fe7558c210057f7558d10005ef724c32003eef7598810006ed6208630004fd7098c212267c10d951025edf628ca3103eec624c930005bf744831001cf47158f20005f57198332266ec10d8931006ee5358a30004ff7458e21006ed620ca100067f655891000cfc745842003ef72158420267e431cc82101eed519881001ef42198e21024fe7688630257ce310ca21006ec7258d1003fce634c832005f5720c510004ff7558e21006f77648710004bf7458d10026ee409881001ef662cc72103eee62ccb30026ec3058810007776588510014fe7598f10007e732d8532024fd760cb30006de5358e20006dd72d8d21006dc4018d21006df63d8121266ee41d8931006f551d853203dee728c520005ed72cc721004ff76cc91001ef47158c21026dc3058c2001fd4314c6100057d7518b31006ed74d8931006f55398630024fe7058c20006df65d8d21014fc7558830006bf7458d10006f75458420006ed7558a3000cfe7458730004ff755803120ef462cc510004fd76cc72000cfc7458e21004fc73583210067c755891001ef67498630004fd7498f2001cff76086301e6de4218d21006ed5498a30007d4320c510004ff725803125ddd768c831086be76d9120026ee505881001ef6610c62000cfc7458a31116bc648852003ef4624851000cfe74d8530004fc7358810006f7764c431006f576cc631006ed7358810006f5630c721024fd7058c10006ec5398a30006dc6318121
  | 1 => 0x8620004fd760c420004ff7598e10007e76148520026f54058420006ec62d8131004fd7608730026ee205881003eee76c852001ef4729842003ef44258420006de5398c10024fc764c920014fc7558720257cc3118931006f461d8132004fd7648730005ec724c730026ef725883003dec724c420026de3058e10006ee70d893103fe42148520024fc764852001fe77248510005cc7348720026f52058420004ff7458a10006f574d8532004fd7418d2001df6718c910004fd7198f20025f8704ca20014fc7558332026de3058c10005f5718c931025ee704872000cfe7458c21004fd768cb10006dc63cc92103ef72158632004dc7358910026ee7058a30006dc634c521024fc7058f21006f5610c430006f44158420006f542986300067c43d951003ef82058032006f753d853201ef67418532006df7518d21026f57098420006f44398420004fc7358620014fe75d853201df7748851000cfe74d8132006de7018d211e6f4620c510004ff7558a31004ff7458830006dc43d8d21085be749852003eee760c920004fd7458f20005df7348510004ff7258f10004ff7458620006ed62cc83003cfe7258c21004fd7458c20006f74158630014fc7558321004fd7498c2001ef66188430007cd320c83103cff76c873000cfc74d8d21004fd7298d21026ee4098a30005f5710cb31005dc7348430006ed63cc82131fda53cc230257cd620c83101df7764c43101df471481100c6bc64cc12004e7d10d951000cfc7498d20026f67058420006de5018d2103eec759881003cfe7258c202cfac20d9120004ff7648530014fc7558021006f74358420005ef724c51003eec3258f20006f75258630006dd2118d21004ff7458d20014fc7558d101e6de7218d2100cfe7458d20006f56148430014fe7598f2004d7e7598d1001ef47018532004fd7558321257d6610c831004fc7358b10006f64358630085be7498d20006fa4058021014fe7558e10007e431c8520004ff7558f20026f63058420006ed4358a30006df634c120006ee5158a30005f970cc610025f47088510006bc7458d20004ff7358810006f563cc710006df634c110006ef5398810004fd768c430014fe7518d21006ed62cc810024fc7098c10004fd7098d10006dd6518d2101edf7358f10004fd7298e1004d7c75589102cebe10d9120006ed4158a30004fd7558732006dd63cca21006f77258630014fc75d8131006dd6318d2103ef6725842022f7b10d95101e6f43218532005f6761853201fe662cc42101ef47418532006ed76ccb20006f43298630004ff735872001cfe7198f20024fc7058c21006ed628c81001df4714c810004fc735872008d7c7558d20004ff7558232006dd7518d2103cfc725833100cfe7458d102dded74487200067c6518d10004fd75d8520006ef4118931006f
  | 2 => 0x6f54258630006df4018d2116e7c65cc5101e6d6321853201eef71588101567c654c510026ef2058620026ed2098e20004ff75d8530014fe7558e2103cfc7218d20006f554584201a67c658c91000cfe7458810024fe70d8520005f7714ca21004fd745802110e7c65485101e5f5760c721006dd63ccb1025edf628c831004fd7598d1025edc71d8d2101df6710cb31014fc7558b10006f57558630065bc744831003eec6288530006ef50d8931004fd755823100cfc7498c2001ef6618c420006ed628ca31006ec541893103eee7118931006dd6318d1003cfc7258c10004fd7458e20014fc7518d2025edc51d8d212eedd760ca31005f9700c730006ed5118931004fd74d8931006bd53d912001ef7105883125ddd718c83103fce730ca21014fc7598f21006ef5398a3022e7e31d951001df671cc1100067f6518d10004ff764c420006ec641893103eec3258021085bc7458d2001df7724851003dee72cc72101ef5760c721024fe7198f10004ff74d8930255ed710ca2101ef77298630006dc65d8d21266ee31d8931006df51d8d21004fe764c520006ef5458810006ee4258a1003ef42158420006ef7648720004fd7198d21005f6734871001cfe76cc92103eef7598a30006dc63cc521006ef4258b30025fa708ca301e7d7718c831025f470cc710005f970cc83000cfc7498c21025fa700cb30005dc7348620005fb7048610005f9700cb30004fd7498f1022e7e71d95100057d75d8331004ff7158d10006f7745842000cfe7458232026ef405881001eec3158810014fe75d8d20004ff7358021006f7315832101eef7258a31026f73058630026f77158620024ec7258f20004ff7458b31006de4358c21004ff7258730006ee5398a30005bf7458520004fd74d893001ef6759863003eee624ca30026f42058630006f67618532266ec51d8931006f65358420014fe755862003ef52158321004ff7648630006ec43d893101ff36088510004ff7058910006f541584201e5f4724c431006ec5358a3032fd5534c431006f96018331026f57098630004ff745873201edc3158e21006ef4398a3003eed7198a30005bf7458132006ec7558a30006ed5198a30006ee4318931006ec6518931004bf7458d201e6f72118d21005fb704c510014fc7558a10006ef6288530007e73288510014fc7558632006f571d8d1003def734c832024fe76cc510006f44318532025f8704c530006dd70d8d21025f8704c610006ef6298930006ed76cc821007ad52d9120006f74258630006df64d8d211e6d42118d21086bd70d912001cfc7158e20004fd74d813201cfc764c931004fd7598f1001df4714c910026ef205842001fe6620c721024fc7058c10006f44398630014fe7558021006df73589102fdef75ccb20026ee205883001cfc7158232005f9708
  | 3 => 0xa7008430004fd760853000cfc7458c1001eee2158831006de4398e10004fd7498e20026df7358c10026f7205863003cfe72d813101edf7358e2100cfe7498c212267c30d9510026ee4058a3003eec620ca3103cfe76cc12001df671cca211e6f64218532006ef4358810024fd7058420006dc5018d21006ee50d8931026f65098420347ce534c83203efb20582320067c72d951001fd763cc531006df7358d21006fb6098132006be73d9120004ff7558d10006ec7158a30006dc40d8d21006f44018532004fd760c620004fd7458d211e7d7630c721006de50d8d2103eec62ccb10004fd760ca10006f65458630004ff7558c1000cfc7458d10026f44098630004fd7458032005ec73487201cdf57488510006f475d8532004ff7058d2103dee720c720004ff7058a3100cfc7458e20004ff7418d10006f543584202267c40d951003eec62c8110006bf6458520004fe764c9102267c70d9510026f67098420006f5415843001ef77398630006f7501853200cfe7418d212277610d9510004ff7158032006f76518532255df710ca31004fd768843003dec724c720005f67198132006f46198132317d953cc1300057f755812101eef4198810014fc75584301f5f5740c510004fd768c8100057f755813101df7720c721006ef7258d21006dd6418d21026ee3058810005ed71cc92000cfe7498f202b5ed750c92003cfc764c12000cfe7458b302efcc328c720005ee76c8520006ef3258232006f47258630006f752d8532004ff755833201cfc7158032026f7105881003ef47258420025fa70cc830006f741d853203cfc7258031014fc7558810026f75098630006f6515842003ef7215843203eef2098f211e6df2118d21026f44098420267e671cca21004fe76cc520014fc7558221025f8704ca3003dee72cc120006f563cc51001cff768c720006f4545863001df4714ca31004fd7558f1001eec6148720256ef1018931026ec505881003efb2058032004ff7058632006ee439881001cfe7118d201ae7c65cc9100cebc644c12003ef64298420007d47348710004fd755803100cfe7498d21024fc764c810006bf51d91202eede42d8d212fded75ccb20007d4324c43101ef6618c630024fc760ca10006dd75d8d21014fc7558730006ee5418931004fd7648110004fd74d8520006f9601813200cfc7458021006ec40d8931025ec70c8520006df5418d210067e42d951000cfe7458032006de5358e10006de6418d21026f7509842003efb705832101ef43158f10004ff75d8910006f643d8532006df6318121006f564d8532006f55258630005f6719833201cfc7158f20004fd7558730006ee42d8931006dd4398c10006de5358c1001df6718ca31004fd7598e10256dc7118d21005f5710c831005df7358910024fe7098f21006df50d8d21
  | 4 => 0xc910007e521c8110004ff7558830004ff764c9102eedc72d8d21014fe7558c20006bc7458d10014fe7518d100067f654851001ede3198f100067f65cc51001df6718c931004fc76cc520024fe7398c20255dd760ca31004ef7258d10024fe760c620004ff74d8910006ef5358a3012e7c65c8510006ed76cca2101fe46248710006dd4018d2101ef4739842001cfe71d8132005dc7348520014fc7558910014fe7598d10004fd7458810014fe7598e1001eed415881001efb1058231006dc638c52000cfe74d81211e6dd628c831026de3058c20006bd75d9120006ee5358810006ef7258d10004fe76cc53001ef661cc420004fd7458b30256dc4118d21006ee4398a30256ee411893103def710ca21257cc2118d21005bf7448110006df634c52101ef6614c420026ed7058810006dc639812103eec7018931006f65158430006f950580312cebf72d9120014fe7558b31006f67258630004fd7458f21004ff705843203ef63298420004fd768ca10006de4398c2001ef461cc520004ff75d8930006f56118730025fb764c030004ff7558c200067f654c51003cff76c8430006f4535842003eee6288630024fc7058b3120ef420d8532024ee76cc920006ed624ca3001cfc764c110024fe70d893101cfc7158c10006ef62cc53101cff768863022f7810d95100067f658c910025fa70cca20005f4714c830026ef3098810014fc7518d21026f5505863016d7e75d8331006ed62cca10004ff74d8121026f43098630005ef724c521006ef628c93103fcf63cc932026fa6018332006f65158620004ff7458321006df630c910024fd76ccb30004fd7298f10006bc71d9120005ed72cc3200077641d9510006dd5398c2103efb705803203def764c832004ff7418d20006f742d8532024fe7098c21005f7714cb30026ed405881000cfc7498e10005f7714c310004fd760c810007d9324c030255dd710c831005f970cca20004ff7058f21004fd760863001df6710c83101ef57598420265ef71cc821005ef724c43000cfc7498c10026f61058630006ec42588101e6f42118d21026f53058630024fe7098e20026f6509863001cfc76c8110006df74d8d2100cfe7458c20265ed71cc82101eec4158810006ed630c920006f57198d21004fc7358910006f56118532007cc7348520005df7348430025f8704c920004ff7558b10006f96018332005f97088520006dd4358c1023df77548710006de7318d10004fd70d8d2120ef662cc710006f67358420006dd4358e10004fd764ca10004ff7158d21026f43098420007d6320c5102f5ed74ccb2001efb1058031005dc7348630004ff755891003ef42158632006f43158321006ed5158a30006dc70d8d21005f9708c93003ef662487102cebc10d91202d6bc32d9120026ee7058810005f9708ca10025f
  | 5 => 0x3eef205843203ded76cc821027f261cc2301957c755813203dec724c320006bf648c520005bf7458530006f7329863001eee515881020ef720d8532026f6405842000cbe7498d20006dd5418d21004ff7598d1000cfc74587320147c7558d20006ed63ccb20006de634ca2101cff768c62001eec2158a31005ee7298131006ed64d8931006ed4358810006ed531893101ef47518532006ec621813103eec7258c21006dd65d8d21005f97008730004fd764c81000cfe7498d200057f75581321e7d4320c721006dc7018d21024ff7358c20006ee5498810006f47158d2000cfc74d8910005ef724c620006ed62c8430026f62098420005df7348620004ff745891001cfc7158b3003ef82058021014fe7558810014fc75d8121006f6329863003eee6218b31004fd7558a10024fc760c810006f77358420256dc2118d210067c65989102267e20d9510014fc7558231006df63cc521006ed6218b30004fd7458c21005ec724c530006bc51d9120006ee5258a30006f64298630014fe7558e2003ef4215843225fce628ca3101df4714cb31185be741873220ef452d853203fce73ccb2003eee620ca10006f654d85320047f7558d20004fd73d8910024fd760c730006f7321853203cfe7298d1003dee73cc920004ff7258d2101cfe7158c10004fd75d8d21006f576cc71016d7e7518b3103eee624ca3100cfc7418d2001ef66148630257cf630ca21024fc7058810006dd4358c20006f552d85321e5f5720c721006f4735842003cfd76cc830006de5358c20025f87048610006f774d853203efb7058232005ee7348520026f71098e10005ed728c520006dd634ca20005fb704c93001edc3158f10004ff75d8121024fe7688520256ef630ca21006bc73d912003feb600c920025fa708c620006ed5458810004fd7558e2101cfe76ccb10004fd76cca10005f9708c530006f54158432014fe7558d20006de5318d21006dd4118d2125fd6618c83101ef6614c630006fb70589101e6f6321853201cfe76cc11001cfe7198c21006ec74d8931006f454d8532004ff76ccb10006dc43d8d10267e471cc82101df77588510005f970cc510006f64158630004fd76c8730004ff7158a30014fe7558630006ef629813101df4714c921004ff7558e2001ef4614852000cbc7458d1000cfe7458420005de7618d21026f67058630005ec724c610005f572cc51001ef661cc630026ee2058a10004fd7598c1000cfc7458a30006ef4198a30014fc75d8d20006f57198d10004fd7218d1001cfe7118d1021df775cc510006f542d853201eec2158810004fd74d8d20005bd74d833203ef6525842027def7548520004fe7398d1003fe4614872003fe6610ca21006df63cc9211e6dc4218d2103ef73298420006f5630c51000cfc7458810024fc768ca100067f65c
  | 6 => 0x7619813201cfd7158c10006ee5258810006dd64d8d21006ee4358a3000cfc74d8121006ec5358810005ed720c720004ff745883101fd6730c5102cebe50d912000cfe7498e20014fc7558032004fd7518d2103cfe7218d2020ef662cc631014fc7558630014fe75d8520006ed6218910006f75498630006ec50d8931026ed2098c20025f470cc510006f75418532006f464d8532026ec7058a30006de63cc320004fd7098d212277771d9510025ee700c920004fd7558b3000cfc7458c20004ff7058d201e7cc320c720256ce3118931006f55358630025fa70cc920006de64d8d21004fd7198d10006ed628863001df4714c93103eec620c93100cfc7458331024fe760c81003ef532584200067d74d9510006ec5498810275ef7448520006ef7258f10004ff7498e2001df4714c831006f75158630026f74098630024f47648510025fa73cc130006de4358e2001ef6610c630006df40d8d2101cff764862001ef7701853201eed21580212eedf21d8d21006dc63cc110004fd7598d21004ff74d8d21014fc7558a30014fe755823201ef4610c520005f7714cb10024fe76c8430005ec725853003eee6218931004fd7558720005f970cc9202277410d9510014fe7558321006f77158d20026f71058a1003eef63cc932024fe7608630004ff7598e200067f65c8510256de5118d21006dd4318d21025fa70c861003cff7648610024fe768c93000cfc74586202cebe70d9120026ed5098810004fc7648730026ed3098810007ea70cc920006f57558420014fc75d813225edf6318532005ef724c721006f75498420026f47098630025fa708c63008e7c6548110006ed630ca21004fd760cb10004fd760c520004fd764c620006dd5398e20004fd7498d1001ef62158021007af640c920024fc7058620005fb70485102d6bc72d9120006ed70d8931026ee1098810024fc7018d1001ef6610c420257cc310ca21005f7714c930005f4714ca20026f62098630006ef54d8931007d7734871003cfc725823100cfc7498f2025ede71d8d2122e7c31d9510026f7409842000cfc7458f20006ef40d893100cfe74d8d1001df4714c310006ee7558a30004fd76c8530026ef1098810006f55158420266ec31d8931006ef5118931005f7714ca10006df75d8d2103eef7518931006bc645852000cfc7458d200067f40d951003eee620c8300067f64d951001cfc76ccb1001fd7734c43100cfe7418d10006ed525883103def75c8520004ff74d8132006ef4258831006fb6098131006ed501893101ef67598420025f8704c510006ec7258f10026ef3098a30007e970cc920006ef62c811001ede7398e21005df7358121024fc7058a10026ef709881003eef7498a3001ef661cc73003cfe768c720006df638c520235f77448710006ed62c861000cfc74d8d20
  | 7 => 0x8a300067f6548110006ef4258a3003eee7398810026de7398e100067c42d951025fcc21d8d2122e7c41d9510256df7218d2125edf72d8d21026fb63cc130006f675d8532006ec42d8931005ef724c52000cbc7458d20005fb704c630014fe7558331024fc7058632006bc7458910026f51058810006bf64cc52020ef773d85320067e72d9510006bf644c520006f550d8532006dd63cc320004ff7558632266ec41d8931004ff7458c100067c6518910006bf6448520006df43d8d21005f4714ca30004fe760c91003eed701893100cfe74d852020fe672cc721026f63098630006f95058021005bf745893000cfe7418d2003dec72cc72033fd653cc63100cfc7458b10266ef73d893103efb2058021006ec4318931004fd7458321024fe7058c10004ff7558720006f66418532006f74398420006df6398121006ef628c930006be7498d2003eee62c8310026ef7098a3000cfe7458331004ff76cc720255df710c831006ef32d8132006f55158620006f7401853203dee73cc821006dc50d8d211e6de5218d2101ef57298420005f77158d20004fc735802118dbc7458132267ce63cca210067f43d9510014fe7558720004ff755873000cfc7498f10026f45098630006df7418d21007d5310c430006f4501853201cfc764811000cfe7458b1020fe472cc421024fe7018d21006dd5358c2100cfc74d8931006f731d813101ef42158831006ef43d893122e7f70d951003cff768ca1001ef8105803101cfe764cb10006f7755842003eee62189301e7d63218532014fc7598e21257d4210c831007d4734851000cfe7458630006ef74d89310067f6598910006bf50d912001ef6610c730005f47158d20026ef1098a30006ed6248610014fc75d8910006f77158b3101eee4198810006e462cc53101cff760c4202267e70d9510026f63098420004fd7598f2101fd6634c431005df734863023df5754871003cff7258c20006ef4158a30005f67348510006f45258630006ef42d891003eed7598a30006f43258630004ff745863020fd432d8532004bf7458910006f772d8532006ed6218b31007d6324c431006ef5258a30045bc74481102267e30d9510026f45098420006f763cc510006ee5498a30007cf7348520004ff7498c212cebc30d9120007e46148520006f7535842001efb105802101ef77518532004fd7458720006ef3258021006f46158132005ef724c630025ec700c920006de63ccb10014fc755823203eec620c91000cfc7458b30007f270cc510025fa708c52001cfd71588100057f755852001ef6721853203cff764ca3024df575cc710026ef7258a10006dc63cc920006ec5498a30006f641d853201ef661c8630006ee5258830004fd75d8910026ec709881001cff7158c1003eee620c831024fc7648630025f47048710006f
  | 8 => 0x6de638c62001cff715881003ef772584200067c7558d10004ff74d8131006f6539863000cfe74d8532025ee70ccb20014fe7598d2001fd673cc63100cfe7458432004fd768c831004ef7258f10087ac72d9120026f54098630005e4714c832256ee3118931025ee70c85202cebe20d9120006ed63cc920004fe760c52001eef2158021256ec1018931005e4724c4312a7ac640c920006ed5258a30024fc764ca10005f7704c431004fe760c930004fd7498f21005bd7498d2001eef5198810004fd71d8d2001cff7358c2103cfe72d8530006de53d8d21006de4398c10006ed72d8d2022e7c21d9510006f653984202cfaf72d9120006ee4198a30004fd75d8530006f54018532004ff7558732006dc630c520006ef7258e21006f751d8532005f4714c920006dc5358f1001eed5158810006dd6318d20004ff7498d1001ef760cc510266ee71d893100cfc74d8132006de634c320026ee405881003eee7598a3003edc3258c21004ff7558432257cc630ca21004ff7258d202d6be32d9120007e4714c8321c5f7754851003eee7498810256ec511893100cfc745823101cff760c72001ef76048510006dd41d8d210067d41d9510004fd7458a30005f7714c110024fd76cc73008d7c7558520006ed40d8931004ff75d8532026f5209863001cfc7118d10006f7630c510006dc634c1101e6f44218532006ed76cca32004ff745803103ef66288510005df734852015ebc648c520006ef7558a3003cfc768c910004ff75d8d2101cfc764cb10004fd7458a31004fd7688630004fd745873003eec7198a30004fd764cb10006fb609833100cfe7458720006df63cc51000cfe7458910006ed41d8931006f44358630006ed5398810005f970cc43001edc3198f10004ff75586302efd5718ca31006df54d8d21004fe760c5302f5ef74ccb20006dd7118d21006df634c510005f571cc310024fe768843003eef63cc8210067c74d9510004fd7558d21024fe7398c10006df63cc920006f55158430024fe768ca1027ded754852000cfe74d8d20004ff7058c21026f4105863003eef7198a30026ef3058a3000cfe7458321006df638c91001ef81058231006bf64cc920006f553d8532025f676cc510006f76198732004ff7558b31025ec7048520004f7764c431026ec2058a30026f54098420025f976cc230005ec724c510024fe7098d21024fe76cca10005f571c8310014fe7518d20006dd40d8d212eedc42d8d21024fe76cc420006f77158f20004ff7058b31024fc70d8910026f5209842001cfd760cb31006f74398630004fd745843003ef44298420005f9708c910006f54158620004fd76cc810024fc7098c2025edc41d8d2103eee7018931026ee1098a3003cec7258f10004fd7458d20027da634c0300067d40d9510026ed5098a30026ed309
  | 9 => 0x761d8132005f571ccb31006f56188620004fe768c910006de4358e10014fe7558a31026f44058630006f55418532275ed7288520014fe7558d21006f4429863003eee62cca10006ef6298b30004fd7648630004ff7518d21006df7358d20006de4358c10005f571cc921007d5310c630006ed6218931004fd7558831004fd7458831004fd70d8931004fc764c910006dc634c92103fe77148720006f76188520006ed43d89312d6bf21d912003cfe7298f10014fe75d8930006ed5398a30006f642586300c5be74d8b30026f75058630026ef7058a3025ede51d8d21006f7618c530004ff7598c2003ede7398f20004fd7098e21006ef5358810025de73cc130006dd7218d21004fd7558e20024fe76c8630006dd634c32003ede7398f21004ff7598c10006f5549863003cff7648110004ff7458c20025fa700c730006dd43d8d2103feb60cc920006dd5398c20295ed75c8520026f51098e10006ec5258a30006ec32582211e7d5710c83101ef71098e2101ef67518532026ef1058a3003cfe760c72022e7c71d9510004ff7158e20006f7415842003eee6248610004ff7458b10006de7618d21024fc764c53001cfc760c52001ef67498420024fe768c5300067d43d9510014fc7598f20004fd74d8910026f67098630006df630c520005df735852025ede6398b31266ee61ccb20266ee51d8931004ff764c831006f67558630006dc5318d2101fd6730c7210067f6518910007e572cc721004fd7558620006ee5458a3003cfc7258430025f87048510006df4318d21006ec40189312d7b820d9120006ef620c91003ef7525842003eee620c810006f5618c63003ede3298c2101cfe71d893003cfe72d8d10006dd71d8d21006bf640c520006f576cc421004ff7458432005dd739812110d7c755812101ef66188620006bd65d912003edc3298c2103def740c920014fe7598e201e7d6320c72103eef7398a3001ef47218532026ec1098810004fd7598e2001ef66108630006ef725891003feb60485201bf746548510006dd5118d21004fd768c910014fe7558830004fd745803101ede3198c21006ed6248310026e52058420006ed624c81020ef432d8532004fd764c521006f45158630006de4018d2125edc21d8d2101fd4314c721006f55498420006ec5458a30006dd54d8d21005f7714c810006ee761893100cfe7458430024ec7648520006f6435842001cfe7198e2001ef57598630006ee65d8931045bc745891000cfe7458632005ee7298331006f743185320147c7558d10004ff7458231026f77058630005de7308430006f96018121006ef5018931006ed65d8931006f65318532006dd634ca21006f57458420004fd764c1202177465cc510006ed54d893125fd4718c831005ee760c920006ed4258a302eedd620ca31006dd5398e10
  | 10 => 0x8510005fb7048620025fa700c830005f9700c430266ee2198d21004de7398d2103fe76148720006ef5198a30026f51058a10267cd63cca2120ef763cc72103ef4525842001ef67018532004ff74d8931006dd634cb10006bf6458d20004ff764c620004fd7198e2001efb7058231004ff76cc62001cfc768cb1003ef65298420004ff7258c1003eee620ca30007cf63cc92003edc3298c20026e71058810004ff75d852020fd563cc721026df7358e2003eec751893101ef77498420026f73058420006ec62cc531006ed31189312eede52d8d2100cfc7458430004ff74d8d20235f57448710004ff74d852000cfe7458e21006dc53d8d2120fe721cc72001eec7198810004ff764c430006de70d8d2103eec628c931007af64cc9200047d7598d10006bc65d91200077765cc510005ef725853003ef4628851001ef47498420007d77348510186bc64cc920006ed63cca21004ff7498f10026f430586302efce720ca31006fa5058031006ec53d8931007cc63cc92001df4714c11001ede3158c2103eee61cca21245f774cc71001ef81058021006ee52d8931026f42058420024fe764ca10257d6710c831014fc7598e10007776548510006f7619852003fcc324ca21004ff7458c21004ff74583311ff74650c51001cfe7158c212cebe30d912029dee730c92003eee62cc830265ed71cca21025ec70cc920014fc7558c21004fd76c8430024fd705881001cfc768c520004ff7558032014fc7598e20006bf65d912001ef7739842000cfe7498c10024fc725872003dee728c720004fe7648530025fa70c8510006de6518d21006ef65d8931024fc76cc81003ef7715843214ebc644c52001cfc760cb10026f65058630007af64485201e6df7118d21004fd768c7201b5f77448510006ec4398810004fe76c8730146bc64cc520006ee74d893100cfc7498f21006dc7358910004ff7458b30006f67558420014fc7558e21106bc6448520006ef7258d20014fe75d8121006f56188430026ed1098810024fc7158b1003eef7498810024fc764851025fcd628ca3101ef7600c51003eee624843001eec71588100067c65d8910026ed5058a30026ee1058a30004fd7298c10006f764185322cebc50d9120004ff7458a3120df572cc721026dc3098e2025edf6398931005f7714c910006f54398630006ee5258a10256cc3118931006f7619853000cfe7458b31006f54318532005ec724c43003cff764ca31006ef745881003eee7518931006df5318d21026f71098c1003ef74258420006de630ca10026ef7258a30026ed3058a30006ef7458a30024fe7058810004ff7558f21005ec7258d10006ed624ca31014fe7598e21024fe7018d10026fa6018131026ef725881003eec7498810005bf7458d1001eec2158b10014fe7558732005f9700c830006f
  | 11 => 0x3cfc764c720007eb7048520105bc7458121025f670885101e6f6521853201cfe7298f210067d7598d1001fd673cc42101ef7759863000cfe7458c10006dd7018d210067f65d8910006ef5258810026f7705842003eed7398810006bf64d8520275ed7448520006ef6208530006f732586300047f7558910266ef63cca21136bc640c52001efb7058221004fe7398d21005dd730843001ef66148430006dd5358e20006f67458630014fe7558031006ec4398a30025f8704c63001ef661cc430357cd53cca320047f7558d1003cfc7258e10026ed1098a3020ef642d853201eee6148720026de7398e20006f7614c530256de610c831004ff764c720024ff7358c101c5f5754851003cfe7218d10005f571cc83103edc3298f2001cff7688430006f65458420014fe75d813120fd663cc721006be53d9120004ff735822101df671c8310004fd7498d20026ef509881003cff760c810006dc7418d21024fc764c93001ef574986300067e73d9510006f45398630006ee435881003cfc7258c21024fc7058d21006bf71d912003cfe76cc521006bf73d9120006ec62981311967c654c91001eee3198810004fd7518d20006f765d8532006ef6298b3101eee2158810006f750d8532256de63987320067f7558d10024fc764c5101e7e7210c720006dc630c910004fe76cc910006f47558630006f451d85320d57c755893021df575cc510025f4704851001edc3198c2103def7148520256ec610c920006f4545842000cfc7458b31004fd70d8532006ed620cb302cfae20d912001eec5198810006f47158f20014fe7598c10004ff7358a10024fe7098e1003eee62cc831005f7714ca31006f676cc51000cfe7458a3032fd6534c43103eec62cc910006f54398420004ff745833203cff760cb10004fd7498d21005d47348710006f4755842025fd4218c831006de4358c20006f5614c63003feb60c85200147e76d9510026df63cc1300057f7558930005dc7358910006f563cc421007e52148310027db63cc130006df43d8d10006f63258630006ee501893100cfe74d8931086bd20d9120006f56148630006f75158730006f45398420006f7745863001cfe71d8910006f66518532006f65298630006df5358f10006f453185322d6be72d9120014fe7558430024fe76c851001ef57298630004ff745842001ef47158f10006f565185322d7bb20d9120005ef724c1200067d73d9510004ff7558a10006ed755881003ef55258420006dd74d8d2103edf7358f2003eec62cc93101cfc7158221006de63cca2020fd632d8532257ce2118d2103dec724c52103cfd76cc831006ee4158a30026ec1098a30004ff71589100067c6558d10025fa70cc73000cfe7458830024fe7298f2003eec6248510004fd7558a3003ef542584200cdbc74585301ddf5758
  | 12 => 0xc724c72103eec628c9301b5f5728851000cfe7458831006f47458420004ff725833103eec62c8510006e73218532006be51d9120004fd73d8520026f61058420005f571cc110006f5610c630024fe70d8d21005f771581320067f654c91000cfe745862003cfe7298c1003dee73cca2101ef43158c21026ec2058810006dc5398f10006ef6418931006fb7058d20005fb7048520006ef624c93103fce73cca32004ff76cca1026fac6448520004fd75d853203cfc76c8530004fd76cc520025fa70cc610026ec3098810014fc7558732006ec5198a30024fe76cc620004ef7258d2103cff760c910005f77148310004fc764853003edc3258f20004fd764c720006f46118132026ee709881001cff768c420006f640185320147e7598d1000cfc7458730006dc5318d20006f46518532025ee7048520006f77558630006dc4398f2001ff360cc5100067f6558d10024fe7098c10004ff7498e2101ef77318532006dd51d8d2101ef66118532006ef42588100147c7558910004ff76cc420004ff745822101ff36048510006ef6258131004fd7298d20005f7714c83003cff768c810004ff7458f20006dc4318d10004fd7458830026ec7098a30004fd755833101cfe768c931014fc7518d10006ef5158a30026ee5098810317da53cc13003eef7318931005f571c8110006df4118d2120df572cc421006ef4018931004ff75d813100cfe7498f10006ef5418931014fc755862003dee73cc9320067c6598d1001ef77218532004f77158d20006df5218d21026f6205863003ede3258c21257cc620ca31006f6501853203eee62c861000cfc7458032004ff7158b30026f55058420006f650d8532014fe7598c210067d72d9510006f77158d21024fc768c810006bc6458d2000cfe7458231026f6409842003ef82058321007af64c8520004ff7258231256ec3118931006ef64d8931006ed51d8931006ee53d893128ded74c8520006de40d8d21005cc73485201e6f7630c721005ee7618931005f6760c510026de7398c20026f5305842001eee2158a31004fe760c931006ed620c831004fd7558f21327d5434c43101ef66118530255ec714c832006ed5358a30014fc7558f21006f5735842001eef4158810024fc7648430027f161cc230005de730863003eee62c843000777650c510026ee7098a3003cfe76d8910004fd76cc42000cfc74d8520026f72058420005fb704ca2000cfc7458321005f471581322267e40d9510006ed641893101ef4618c5302d6bc21d9120006f440d8532014fc7558e20256de2118d21026ec409881000cfc74d8930006ed62ccb30004fd7498e1001cf47158d2001eee715881003fe661cc821006ee40d8931025f67048710006dc6418d2120ef72198d21004ff764ca1003dec724c620014fc7558d2101efb7058021
  | 13 => 0x8d102c5ef75cc920026ee5098a3001ef67298420026ed20586200067e7598d10004fd74d8d211e6dc5218d21026f45058630006dd5398c1003efb2058321257cf620ca31026f63058630006dc53d8d20004ff7598d21026f64098630025fa708c930004ff7558620004fc735842000cfc7458f10256ef620cb10006fb6098121026ed2058420007e771cc82103eee62cc810006f75398630006bc53d9120005fb704ca30026f47098420004fd7458231014fc7558f20005f9708ca30006ec5458810006ef62cc91001df7764871025ddf718c831006ed5258810006be65d9120006ef4318931006fa5058021004ff7158c20005f7714c93103eee6218910006de5398c21014fc7558a31085be76d9120007e762cc53103dee72cc32001ef4759863003eee620cb3101ef4614c53001ef67688510026ec4098a3020ef632d8532006ef70d8931006dc4358f20006de65d8d21014fc7598d21026fa6018331006ed4258810005ee7348720006de74d8d21014fe755822130fd943cc130006f532986302bfac64cc920005ee73c8520006f761c853001eed215822101eef3198810006bc75d912000cfc7458632004fd7198d20006f732d8532006ed4258830025f87048620004fc764c520006ed5258830006f53218532026f61058430006ec5258810005f47348710006ef630c920004fb764c030024fc76cca10004fe76c8530005ec7258131004ff7458430004ff7158332006df53d8d2101df576cc42101cf47158c21005dc7348730006fb7058d10006ef624851001eed3198810004ff7558f10005ec724c63003cfc764c521006f75398420007e772cc421026de3098e20005f5718cb1001eed7198810006ec75d8931005f9708c620006fb6098332024f47158f1001cfc7198c2101cfc7688530026f6105862000cfc74d8532024fe76cc810024fe7098e2101ef462cc71003eee628c81001ef6610c430006ef53d893100cfe7458d21255ed760ca2131fd953cc230006f6415842001ef47158831006bf75d9120025fa708ca1001ef46248710006f97098d20004fd7458910006de4318d21004fd755802103ef62158321006f561c863003eed7498810026f74058630026ef5098a30004ff7598f21006ec50189310cdbc7458930004ff75d813201cfe760cb10006df634c921026ef2098e20006df4218d21006dd7418d21026ef3058810006ed620ca30006ef7558810024fc7058e20006ed7298d21005bf7458131026f77158420006de630c6201e7d72118d21004ff7648730024fe70d85322eedd628ca3101cff764c630256cc2118d2103ef53298420024fc7058432006ee628c630006f754586301edf6730c510004fc7358221024fe7608430014fc7558b30004ff7418d21004bd7498d20007e73218532004fd760c720004de7618d2103de
  | 14 => 0x255de728c83103eee628ca30006dd5358c10004fd76c8630006ee624c6300ee7c65cc110006ed75d8931026ef409881034eee634c832006dd5358e10256ec411893101eec31988100d57c7558530004fd76cc910005f5710cb10026ed505881000cfc745822101ef4610c7201edf774cc510004ff745873025fd6718ca310067c65d8d10026f54058630006de75d8d21004fd75580320067e74d951003eee624863001ef67298630256df1018d21004fd7518d10287ac64c8520014fe7558a10026f5205863003eec2198f21006ec7358810005f7714c831257c4210c831004fd71d8132026ed305881003ede3298c2000cfc7458432004fe7688530006de5418d21006f44258630006ed4118931026ee1058810004fd7198c20025f8704c930006f75158420006bd7498d2001ef763cc710006de5398e20006ed62cc831014fe7598f2100cfc7458031004fd7558332045bc7458d10006ee5318931006ee7158a30006f44158630026fa601813203eee6218b30006ed401893101df673cc510004fd7558a31026f51098c10014fe7558432014fe7558831024fe768c81000cfe7458021024fc7058c2001ef57398420006f57258630006dd63cc310005f7714c921004ff7498d210077541d9510026ec1058a3003eec7418931007f170cc510006dd4398c2101cfc7158a3003dee720c5200057d75d8730006ef3258221026ec2058830004df735891001cfe76c8110005ec7348520004fd7098f2103ded76ccb20026ef7058810026f77158430005ef7258d10006ee7358810006ef7158a30004fe768c52003eec6248110257e6210cb10006dc5418d21004fd7458b31006f6415843025fce21d8d21006bc64d8520005fb704c920005f970c8610007d763cc51020df772cc42101cfe768cb1001cfe7198e21006f73158231025f4700c5101e6dc2018d21005dc7358121025f670cc710006f45158730006ee64d8931006ee5458810006f74358630005f7714ca20026ef105881001df671cc92101df671ccb3103dec724c52001ef763cc531026ec3098a30004fd75d813201edf7358c21006dd5218d21004fe7618910004ff764cb10006f55358420026ed1058a30025fa708862001ff3600c51003eec7258f20007cc328c52001cff76084300067f74d9510005ed71ccb20026f7715863003cff7648310006de634c61001efb10582211e7ce720c831004fe73d8910004ff7358420006de63cc610007cc7348720004ff7558331026dc3098c200067f6598d102aded740c9202d6be52d9120005f6738851000cfe7458031024fe760c420006f94058032006ec4358a30006f64158620006de638ca10006dd4218d21005f9700843001edc3158c21004ff7558221024fc70587322c5ed75cc920026dc3098e1003eee741893103cfc7258c2003cfc725
  | 15 => 0xd760843001df6710cb1001ef66118520006de63cc72001ef4315823100cfe7458e20025f8704852000cfc74d81310057d7598910004ff7158d20014fc7598c211e6df2018d21004ff7598e2103cfc7298c21004fd7498c21006dd4398e20004fd75d8d20006f64318532006f76108530256ee511893100cfc74586300067f41d9510004fd7458630347cd534c832266ec61cc92001cfc725832101df671cc831006de634c720005ed710c92020df576cc721026ec4058a30004ff7648430014fe7558231004fd75d8131024fc7258f20006f5545863001df7734c431027ea62cc2302efd721d8d21014fc75d8931006ef6518931006f664d8532006df52d8d2103eef7018931005d47348510006ee62cc630006ef41d893103ef75298420006bd51d9120085bc745852001df4714ca2100cfe74d8d21006bf7458910006de43d8d21006f450d853203ede3298f2001eef215822101edf63cc531004fd71d8930006ee4258a30014fc75d893001ef6618863001cfe7398c21006f5641853204f7471d9510006df5398f1001cfc7158d20006df5318d20006f751d852001eee4158810004fd7458d10006f5610863025ede618c831006f6535863001df7750c510004fd7558830006dc63cc510006dc638c910006dc634c510004ff7458720006ef52d8931007e52148110026fa601812101eec614852003eec7118931004fe76087302cebc70d9120006ee43d893103ef7715863201ef66118730004fd745862020fe432cc42101ef47498630006ef62c8510025fa70ccb30006f64398420007f37048510006dd5018d2100cfe7458a10006ee6518931026f41058420006f740d8532004ff7498e10005dd7308630006dd638c62001eef7198810006f775d8532004ff755823101ef4618852003cfd7258c20006ed628c63003ef43258420006f76198730024fe768c4200067e43d9510004fd7418d10005ed728c720006dc6518d21006f674d8532005dc7348530006ed6518931005dc7348610005f970ccb30006ed5418931004f77158f2025ede21d8d21006ec7458a30006f76158132006f54158630024fa76cc13001ef77298420005ed72cc120007e7724c43103eee62cca30004ff7458021004fd7118d20026e5105881001cff7688730006ef5498810256ec2118d21006de634cb10004fe7618d2104e7d70d9510006ee75d8931006ed620cb3101cfc764c92122e7e21d9510004ff7558430006ec4258b30006dc634c920006f443d8532006dc64d8d21006f470d85321b5f57448510006f770d85321e7d43218532006ec5158a30006dc75d8d21004fd7558420004fd764c110006f75318532265ed76cca21257cc210ca3101df471ccb1000cfe7458221004fd7558232004ff7058732267ce31d8931004fd75d8d10007e87048520005f9708c630
  | 16 => 0x8630004fd7098d20026f47058630014fe75d8d21004ff764c12000cfe74d8930006dd63cc720024fc7158f10006f6415843201cfc7158c21004ff7558d2101ef6760c510004fd7458e1003eee7598810004fd7558e10005df7348730004ff70588310d67c654c110025fa70cc510004ff7598f10014fe7558a3000cfe7458e1000cfc7458d2103cfc7258730006dd634c720006f7421853203ede3258f2020ef442d853203eee62c863003ef74298420006ef6248110026ed409881001cfc7198c10006f540d853201ede3198e21006df53d8d2001eec4198810026ed709881001ef47598420006ef764c832006ec42d8910006de7318d20014fe75d8d1000cfe7498d10026ef4098a30005bf7458910006ed53588100ed7e75d8730026de3098e10026f73098420007e7714c832006ef5498a302eedc20d8d21006ed5258a1001cfc7158e21006bf53d9120006ed4258a10014fc7558432025fa7008730256df620ca3103def750c920004ef764c832004fd7598e210ae7c65c811003ef5215802103eec2158432006be71d9120004fe7688730257d4310cb1000cfe7498f21004fd7558c2100cfe7458332026f4105843003edc3258f21006f441d8532006de7518d21004ff73589102267c20d9510006f77158f2103eed7598810004fd73d8121006ec65d8931005ef724c73003fce730c920006f76198532006f46418532004ff764c110007ae52d9120025fa7088520004fd74d8532005ed729833101ede7398f1003dec724c120006dd634c310005ef724c42001ef77498630006df7358d1001eee7198810006f5611873200cfc7458332006ef4398810006f54358630266ef621853203edf7358f2103eee7498a3000cfc7498e20006f561cc73001eee2158b10004ff7558c21004ff7458810026f4105862003ded76cca32006f6439863001cfc7158810006df634c9200067f65d8d10006dd5358c20006f65158630004ff745863200cfe7498e10026dc3058e20006de7318d21014fc7558c2001fe42148510004fe76cc930006f743d8532006ef624c930245f574cc710006f7521853201ef6610c530006f44358420006f77158910006ef42d8931026ee5058a30025f47648510004ff7458f21014fc7558331025fb734c030006ef629891000cfc7458232006f576cc721336f6634c431004ff7558420266ee61cca32004ff764c52003ef82058232024ff7258810006dd630ca10014fe755863201ef461c853000cfc7498e21256de4118d21006f75298630004fd7598f2029ded74cc920006f754d8532026ee3098810026ef5058a30006ef735881001df671c8110004fd7558c102e5ef754872003eee7198a30025f6704851004e7d71d9510005f7714ca30026ec2058a10026ec5098810004fd7558c20004fd76cc620004ff7258e10004f
  | 17 => 0x24fe76cc92022e7f10d95100067c64d9510006de5398e10006df6398d20026f44058420004fd7558432004ff7158830006f65498420004fd7458a1001ef763cc421266ef10d8931006de54d8d2101ef4610853001df7740c510005f47348510006df6518d2103eee628ca31006ed620c83001eec61c852003eee62ccb3103eed7498a30006ed5498810005dc7358520004ff7258630004fe73d8520026f470584201e6f45218532006f97098d1003ef64258420006ef63cc92003eec7498a30006df6398d10006f5521853200cfe7458732004ff7498f21006bf6498d20006ed620c81001ef57418532027da73cc230006ee7458810006f54218532014fe7558730006f55298630266ef62ccb10006df5118d21006f45498420006ee54d893103edf63cc932006ec4258831006dc63d8121026ec105881001cfe7198c1001df673cc531014fe75d813201ef57518532005ed720c520004fd7458420005f47158930004fd72d8530005ef7258131014fe75d8931005f5718c910006f45298630026f75058420006dc54d8d21006f6745842020ef672d8532026de3098c20025fa708c53003eef600c92001ef81058221007cc320c52000cfc7458a1003ef7215872003edc3298f21007cf7348720006bf644c92001cfc71d8910004ff7498f20006ed42d8931006ed52d8931006dd4358c21004fd760c910004fd7018d2100cfc7458830024fc7058e10006dd5318d2101eee6148520006f5610c730025f6700c51000cfe74d8910006ee76cc920004ff7598d20004fd74d8131006f5618c42004d7e759891001cfe7198d20006ec54d893103ef5429842003edc3258c20026ef2098c2003cfe7298e10006f65258630014fc75d8d21004fd755881003eee620c930004ff7358b100057f755853000cfc7458831006dd52d8d2101cfd76cc43003ef55298420006f96018131004fd75d893103fce73cc821006f45358630006dd42d8d2103eee620cb30006ed624c63000cfe7458f10004ff764c830025fa708c910007db324c03001eed41988102eedc52d8d21004fd7458732006ee539881003eec6208530006f976cc230014fe7558f20004fe76cc931006dd63cca20004fd7458332006bf641852000cfc7418d211e6f4201853201eef5158810006ed62cc6300067d42d9510005f4714cb30004fe7398d20024fe7098c20014fe7558c1001eef7258b10267cc31d8931006ec70d89310067f42d951000cfc7458e10006f541d8532006ec64d8931006de5358c21006ed628ca30004fd7458f10257e4210c831005f77148110014fe7598c2001ede3198c10005f7714c920026f4209863000cfc7498d10006df41d8d21266ee61cc8210067f65cc110006ec52d89310067f73d951003eed7118931004fe73d8121006ef62d81312ddef7448720006f7429
  | 18 => 0x4714ca10024fe70d8910006ef75d893101df576cc631006ed431893120ef662cc51029def74cc920026f53098630006de63cca21026f43058420004fd75d8121004fe7618d1003cff768c9101e7d42118d21185be74d8332006ed4198a30014fc7558d20006ef5458a302e5ed754872003eef7398810005f5718ca31267e621ccb1001fe76248710004fd768c620006de63cc31000cfc7458910026f55098420006dd50d8d21006bf52d9120026f73098630006f75158432004ff7598f20004ff74d853003ef66248510004fd7558430014fe7558420004ff7498c10006ed7458a30004fd7598c21006df4398f20004ff7158f2003def74c8520006ed620c630014fc7558b3100cfc7498d21014fc7598d20006ec43588101e6f72018532006dc63cc120026ef4058a30025f670cc510004fd7458c10026ed1058810007e432885101e7d4630c721004ff7498d2018ebc644c920026f72098630006f653d8532005df7348610024fc7058a3104d7c7558d10006de5398c20007e46248510004fd74d8530006f554d853201cfc7258f21004ff7558d20005df7348530006ed6248630004fd7418d2103dec73c8520026ee3098a30026f53098420004ff75d8d2003cff760ca10004fd7458232006ed50d8931024fe768c620004fe7618d20006df4318d10086bd72d91200067f654c11000cfc74d85302267e10d9510026f77098630006ed6218930007f0704851014dbc7458131005ef724c610006f543d853201eee51988101e6dc7218d2103cfe7298c21026f6505842001ef43158021006bf6488520004ff74d853203eee6248310004fd745822103ef77158720026ec5098a30004ff7258d10006ed4398810006dc6358121026ed4098a30005ef724c530024fc7058e21026ed7098a300067f65c811000cfe7498c20026f7209842020ef662cc421014fc75d8532006f65498630004ff764c810006ee4018931257cc210c831026dc3098c10006f651d8532004ff735832103eed7518931256dc1018d212eedf20d8d21014fc75d8d1001cfe71d8d20004fd7558f2001fe77248710004fd7298d10006ec7558810006f764d8532006bd73d912003def7648720006ec4198a30005f970c8510014fe7558910005bf7458d2000cfe7458f20026ee2058a30004ff755883101ede3158c10004fd7498c10006fa4058032005f9708c520006bd71d912003dee72cc521006bf6418d20025fa700c430006f4515842001ede7398c21006f9405802101cfe715881025edf10d8d21006f45418532026f77098420025ec7048720006ee620c63001df4714831003eec3258c21005ef724c72003eec7398810014fe7558b30005f77158930005bd74d8b30004fd768c830027e962cc230006f45498630327d6434c431005de73981212efd421d8d21004fd7558b10
  | 19 => 0xcb31006df4358f20007e462cc53100cfc7458720006dd638ca10006f7535863000cfc7458c2100cfe7458f21026de3058e2001cff7608730026ec3058a30006ee5198a30004ff7558b30006df63cc120006f6541853201eee3158810005ef704c832006ec5318931006dc7518d2103ef4215872017e7c650c910004fd768853000cfe7458a311e6d43218532006ed62c831003fe421cc921006bf64cc120014fc7598c10005f57198132006f77158d10026ee3058a302cebc20d912001ef57018532256df620c831007e732cc421006f7315802103ef73258420006ec7458810006f53258630005bf7458121004fc76cc910004ff7458d10014fc755803133fd553cc631025ee70cc92003eef7118931014fe7598d2103eef60485201d774658851000cfc7418d101e6dd768c831006df6398d210067c6558910004ff7598c21006bc6418520004fc7358a10004ff74d8d10004ff75d8d10004fd768c42003eec7598a30024fc764c620014fc755842000cfe74d8131024f676cc51001df4718c83101eec5158810024ff7058c1001df673cc721006f474d8532027db734c030004fd7558630026f64058630006f55018532005fb704c53001ef77418532006ed745881001eec2158831004fe760853001cff760c62001ef661cc620014fc7558e10004fd764843001cfc7608530014fc7598c20006ed62ccb31004fd7458e21026dc3058c1025ede41d8d21006df6418d2101eee61c8520014fe7558f21004fd76ccb10014fe7558f10007e76248510014fe755833201df4738851001fe421cc5210067c73d9510004fd7598c20006ec5398810256ce2118d21026e7205842030fda43cc130257ce3118931006f57358630026dc3058e1001ef66148620006f5614c42020ef652d8532006ef71d8931004fd74d8121006ec6258131004ff7498c2001dde73cc531006f665d853220ef72198e2103eed760ca2103ef47648510006ed71d8931006dc4318d2100cfc74d8d1022e7e41d9510006f453d853203ef63258420004fd755863203cec7258c21004ff7558a30005f5710c910006f565d8532004ff7558321004ff7518d20005dc734851001df576cc710006dd4398e10006f5515863001df671cc310006de634ca20004fd768c520006bf64d8d20306fa634c030014fe755803201ef76088510026f55098630025fa70cc43001cfe7198c2003eec624c931006ed7358a3001ef4729863025dde720c831006bf6498520257ce620c831005ed72cc521005ed7298131006f575d8532005f4714c93003eee6208630004ff7458e202d6bf70d9120006ed62c8630006dc74d8d2100cfc7458f21004ff7558810014fc75d8520004ff7058d10004fd72d8131007cd320ca31004fd7558221004fd7688730006f570d8532006de7418d2101cfc7158c2001df
  | 20 => 0x4c00000500200e04c00200700f00e00102602800f00c00d0020920a601500003000000201000e304009000ab607f05802152e00000001200001a04500200800100801f0030000e50001960112240100020000060020040a01cf0ea1d3001355014fe75d891020ef462cc531006f640d853203cfc760c9101e6f6620c510026f7405842003fcf734c832014fe75d8530006f5610c420024fc70d8520006de634c310006f5539842004d7e76d9510006f670d8532006f76118132006bc6418d20006ef51d89311e6d72118d21014fc7598f10004ff7458a3000cbe76d9120024fc705883101ef7759842003fe77148520005f67688510004fd7458632357ce53cca3201fd673cc710004ff7058e21025ec70ccb20266ee2198f2101eef7258831006be75d912025ddd718ca31007e731c8520025ee76cc920006bf7458d2001ef66118732006f561cc430006df5018d21006f451d8520006dd53d8d21024ff7058420004ff7358620004fd7558d1025fd4318cb10004ff7558021026ed4058a30006dd63cc721006dd634c721026de7398c1003cff768cb100067e64d9510004fd7558d2001df6710c91001cfc7158332004ff7258430004fd7498e21006ee7558810006dc634c120024ff705881003ede3258f21005f571cca210067c7558d20006ee64189311edf574cc510014fe7558b10004ff7458032004ff76cc810006ec4258a3001edc3198c10014fe7558d10256de7118d21006ef621813103cfe76cc720006ec4158a30026ec4058810006bd52d9120004ff7458232004fd7458432006f561cc620014fc7598d10006ee4258830006ed53d893101ef673984202eedf71d8d21027d8304c120005f970cc7302267f71d9510026f620584202d6bc52d91200067f7558910004ff7458e10006ee5258831004fd7598d20006dd4398c2001ef57498420006ef4358a30006f761cc520004fd72d8d1000cbc7458910006ee4258810006df63cc110006bc6498d20004fd764c42003ef45298420005bd7418732006f451584320057d7598d10026f42098420026df7358c20006f561cc420006f56148620014fc7558f10004ff7458f100067f7558d20004fd7458b10256df6318931006de4398c21006f47458630026ec705881003eec620cb10026ec5058a3001df6718cb1003eec3258232006f7614852001ede3158e2101edc3198e21256dc5118d21006f563cc721006df42d8d2101df4714cb10007e571cca21006ed7158a30006f57458630014fc7558831014fc75d8530006df70d8d21026ef505881003eed741893103cfc7258630006dd63cc610205f5750c510024fe760ca10006ef5318931005fb704c610006dd634c610004ff715823203eef60cc920006ef629893101cfc7158830006ed4398a3003eef7418931006fb764c03001cfd76c
  | 21 => 0x1804f01202500a08600000300000000200110c00005301900107d0d402407300000000200600301100204801607b57609a00f3d850e00000001100d00101201302400a21000400500900203100005002e04c0000180070000c200801a00803e0140532a802201f00000d02003000604800100900029c00100500600300303000211509200100100001412200301d23633421100002500000229c00e34e06900003401800300f08001500700b00000001104800304e01b0040050010290010080013491b500403701b26000d0020db01000e010012008000004c3e01300000700302101700200211d00400000000a00000400001700a0000dc00800800917401000e17401b05b00c0010090360bf01817700420d07c00049902b00900000500510803800100f00400101c01900800a00002201100001a03b00a00408400600101d00236000000201101600006d01b0d901902000005100707602500b00000401300f15903207000900b00d06d01200000202c00900900600700809d63202a00300013e01001300e00000701802c01401b01a0010220010010030310000001c50b400000000000202000130a00401900600003c02d44f08002b0010050070000060020060191ac2b301221300a00500902a14b01500000200702400102900301702100400000700d0050070010450381f00000000000f507903400100006807e01602513601400400000002d0180411460ee0000b600100e04c03100b01602200c00600323c0000b601900800000801601c0010210230c202225c00001c07202e00100600102902800400100e0090010160290110db0040140610030000000a500005500b01502b02500200000200900500800111d00000301900101202627e02200c00311800000900500304903700120e00700500200900e00000145800500300003e00900800008104700000c00109300001809301000700200100143c00000214d00600c00400300000000006300600200000600500b00015d03d08c0011db20700700000800300000400203c02e1542a200402201600201100900a11002300b0000220281470080000270010111e901b03a01e00000000000146101b0160550001fc00001504300400e00100500f0920030092eb00411c0192401bd00e00607300501d0000170310070a001202110e3de00400203006900615b01500100000300107c00600001b00002201900300807100102a0230013ab04e09a01c00a00000503700001a00201a01211502a01001a14c00000300b00200002001f00200103d00500000301500200006f00700003501001000200b00000b00102000001500100500002000100a08700001200309c00304312401122300700200400600000000f00d00200100c00300100002300f00000000000c0000ab000007003039002
  | 22 => 0x80a50010710040ec10800000000000200c00a02500002902400803900010400757d01400602601a00b0620090010ba05102201500101304000100a01d01601300f05006703a0110130120c401b15d20100b00000001b00200700300001802300600300002f04207438400600203d02e15d01000a00701900d00001000400100e00c01100b00700c00301701300800000201a00000f08b00700d01403701000507401c01303f04b00100d00000202101a0180000ed01100700004905b01600e01c05c00c00e02200500108500200000400701100006e00300309601f01100109e0000050b800c02d00a00b00000300000916d02c01000f0010020040002b800106f0b50cb00701c00b00001300834c02f00000000400400101305500300000102400100200109d00701800609e04602e00300000200000e01700a01100100000900000406c00e02601b00100701000201300b0040290c326a00c00115902a00100108805b01300002e00000003738900200200c02501603502e01803d0140180010000010040070370090105ae1c60602cd03b00400b00007700c10100000004500400200e0230e506800b00005e01200500000424d0050b50120000061a001208f02800800301a01100002100a22000e00600920b00501800400506b2082d60190df00000000800c04f01002b05200802000100200001f0fd0e005500000100c00700000636d2f800600d0080520b40003d700102004b00f02900c16700300000100100100635b00000f0277d901e00c01500f0121a70110120000050000020140010030000200000910010110010240020050bb00100300302b0070010060446f100805403d02a0030000000da02800700900000011d00202e00000000707805200a05403d00001b00701807301a00095d00c00300001501800217c03100136001210200600000800003a00400200500e00a00103b04300204f00e00300300e01c00200403404d01e0f30020000080000000030180b504719e02304a00709600d00200f01500000000c00012900000101300201d05900800b01400012d0120
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xcac645c831480091b90ea9ac71001eb920973584200056ac1ea830a6400a74855cd618c0071ed0e280c299002976144018d211e566412a231a4200c74751c56348001958e9b92c688002b360f51189310045f438a3b224000ae781540624c4839ccc5b8a6518002ad61051d85320055ac20eab0c60028dd8794c634840156d08280c29912eb5a0450d8d2100727a9ca731020008f581dd663880014bd0ba0ec69080363d9073485200046fc3ac631a4200af1808c9618c001878ebb22c6900f3711ca324c4310053ac2e87b0a6400a76851d3614c8097c10090a40880123d2057458f1000572c10a1b0a6400a7685dc3614c8019a8c7b8a6490802976166418d210056bc1aa530c60008df835d920440019a8c6b8e64908029b6147458a3000672b16e29946000acd82d04634840193ee839ac4881129d60773d95102cc5e436e8b0a4000ce776dc9310c40156f02b2ec8900023720d745822100556c26a6b10204acd4611cd21480019a8e7b0a429012b35d8073485100056ac18a030a6400c5f65dcd6244001c6ea92a4c318002a7a1353d8d210054f424ca31a423cace82900634840117f08baac6880029ba14401893100573c0aa63126200a6c8259365440071e902baac7900123d219718c91000557c22e6b146044a75811d365440011b906ba2c48801f391c9614c4202556b4088031a42008de8710063484091d904bb6639000a1f21576481100045ec26ec98a40048ec87509628c00f1d904ba2c7880031dd97714c91003e66392c698e4000a7685d07614c8015cf02a18c4988023ba1c40d89310062e3aee6b1a404ace4711c963c4001caea729cc2100032b19276c85200047bc3ac230a40008f587143614c80159d06200c498802b3e095118d211e66a310e690a20038f681dd663480991df0cb9663908029761741d8d2101c7643aa4b10623ccce621cd218c0015cb05aa0c29901e3b2097558f100056b41ea2b0e603cec432548614c80156d0828ec2990123d60774d8d1003c77416e931a2000ccf761cd21c80014bd0a3a6c6909169da0773d951000556c26e1b1262048ec87549628c00317908bb062900123b21d624c81036656b90c9b1a4000a75859d1618c0015af02aa0c6908123be1d62cca101e5674168231a42008dd87994634840156b09a92c3180029ba16641893100556c26a73146000a7685d0c614c8014ed0ba1ac2100028f21573d91200047ac0eeb31a4041ae48258f31c4095d88c2190629001e3b20974584200046f43ec6b0242078ee82dd26384079b8ee638a64190032dd937158d200051e42ae3b22404ace6611c9318c0011bf06ba2c2100021fe15764c1100066631ae598a4200a6d85103624c40153b09a98c6908f339188714c93000567418a031262008ee87143624c4014eb0b326c299003351cd6148620
  | 1 => 0xcc3b9262100023de057558d210162f3aca631a4200c9c64dcd61480011f70eb00c09881e3b209764c11000556c26a6b1460008bf845d920440079a8e331a6510802b320d501893100557420a1b126200ae58194d62040955cd02280c4989af1d5c465189100064e326e690a40078ec825d832c40011bf06baac4880021fe15760853000566c1ca83126200e2f54953624c4018deebb92c6880031bd94724c51003d7241282b08643cec421548634840f5cd05a8ac2190023de057458d2101c7b40eeb31c42008ee87d89604c4019d2c5b82651812b350c5760cb100056641a8331460048dd8794e630800f1d9043b26290002aba1353189310061e3a8e8b12205dcce62dcd218c00f5c904aa2c2100033518d710c91025762188e4b1e2000a9d849d4634840117b0f32ec8900031ddd77158d20254f343ee498862048f4865c432440795cd04200c2990123721d4358e100055ac26a530c6000d54651cd21440011db0db926318002b9604401893100566c10a631a4000c5f751cd624400117d0e322c6900031719473589101e6e5b00e690a4000a9e831d764480071bd0fa9ac7880062f2117558d200056ac0ca631a4200c74659da21440018beeb3a8c6908022fe1176cc5200043fc2aec19220038f4815d93204001998e6b124218002b560440d8d2100566412c631a2000ec6624c4318c0014db0ba08c49892b39184724c53025c6fc1aec9086000c9f641cd21480b355b0438ec8900032d1d07158d200054fc1acbb224000caf64dc93148095b8ee439a438800eb5a075358f10006363a8e4b1a20008dd871036348401998e7b1242880038dd5254584200065a326e299240008df835d56204001878ea322c29000317d9773485102ce573b6c99924003ad68114e63c400117b09bacc690002b9607531893100566c10a1b1a4200a75859c9618c00156b093aec29912b71d88734871000477c12eab1a20048f581dd7634400159f04a08c6908030f5d475d91202ed67410a1b1a424aacd821d463484075c902a92c408002b3e0d7158a300046fc3aca31a42008df835d560c8401d48c830a429000395d4e53586300053742ce9b12624a8ec87589318c0015af06a10c2990030fdd77458d100063bba8c2b026400aad849c5628c00187ecbba240880029d616745842000746326c79924000acd83143624c4011df0eb10c498002b9e0554588100246e43a86b184000c74659d831440019cac5b8a640801eb9a0a43584200046fc1ae8b1220008bf845d56244001998c639262880031b1947258d100247643a84b106000ab684d49618c00317908bb064880029ba1442d89312556a40aa431a42008ef825d1610c0093c90e90a418800a1fa1776cc6200056741ca831262038f4815d16308401c6ea92a0c2990023b60b7498d1000566c16a231a4200
  | 2 => 0x57358a30256e2188e498c204aacd82dd06348499d8863b92c78800a1fa1b75589102566b308e690c40008ed87100624c4015cb0db8e64108123761e4398e1003c76412e8b18420087f855d920440015cb05386c299002ab61352d89312667238ee4b1e2000cd5731cd6108001c5ea92a2c5181169da0474d95100061fb2ee8b122000e1f5495063484014dd0ba08c4988029da1672586300061fba8e8b1a4000cd553dd9310c4019ceedb8a64190030fdd47458d100072ba9ca630a6400a6d85990624c401938e9b9ac4880123761e5398e200063632ee498a20078ec825d1608c4015c902b9ac518002ad61353d853201c6e43a86b184200c6f651c9634400153d08280c69080327dd0635812100572c168630a64008ed82dd263480010fb0bbb264880031bdd67558a3001d7240ae6b102003cd47158d32c40014ed0ba0ac3180f371dc4734872001c6ec3c873184200acf835d562040014bd0b3a0c690802b5a0c50185320143e42aed992203cad5811c0634849759b04386c6908029b61743189312556b40c8031a4200a5e85990634840156b08286c2990033394f764c8320047bc0aeab1a4000a7585109618c0995c902b1e6490002b36084018d210143e42aed192204aec421d0463484831ef0cb966388002a76126518d210055b426a530c6000ad58110c634400155d093aac408002ab612651893102476416ec99020038f887541600c4898ecedb2e62880029ba174358a300056641aa2312620087d85ddb31880014bf06b26ca8800395d4e53584200053742884b10204accc7218d314840155d09a9cc4080123761e5398c100055b420a2b0c60008dd8714363484018eaeba8ec2990037190c724c4312556b40ca031a4200ad581900634840156d083aac2100029ba1743588101e667390c798a42008ef825d16244001958e9b92c488002b520d74584202576218aa231262018ef8750b624c40117b0fa96c890012bca0042586300045ec26ec98240008df835d16344097998edb9a42900123d61f630c5100053742884b1460008ef8758862cc4091e903bb2621012bb10c541189310045f43ec8b1a4059aac8654b64480010ff0abb26090002ada1353586300055b426a7308403cae48258c31440091bb0f21cc71012b7198c724c4310056ac1881b0a6400a6e85d0e628c00155d0938ac5181672b1db64485200056ac08a1b1a420087d87d07654400156902b2ec8900029da1761987300247643aa4b1020048dc8754d63840014dd0ba1ec49880339dc9614c6300055ac26a430a6400a5e85d0c63484971bd0f31a651080e3e219708c910006563a6c49022004af2808c9618c0018b8ea31ac090802b3a0f511893125566c10e031a42028df8754f63484015c904b08c298002a76107018d210051fc2ae7b224000a5d85d0f63484999c
  | 3 => 0x1b1262048dc8754d63040015e300212c318133391c7624c931004eb41ce690a2000cd7731c563480995c902b1e6590002976147018d210062e3aee6b122000a9d84d4863484095c90c90a40880030fdd274d95100062e3aec6b02420287c855d930440011b906bb24088002ab6135258a300056ac1e8430a64048f78758f31c40010fb0fa1eca88002b3a0c40d89311e47a43a64b0c60018bc845d5624400159f06a0cc518002ada1265d85320162f3aca731c2000ad683100614c8018b8ca39a42880021fe15760c5200056a41a8430a6400ad683d08614c8015ab02218c690802b360c401893125d6b40881b1a4200c3f751916348099ccca3a8ec498802ada13539863003e72312e31926200acd829c06348495d8842a88c6908029d61440d85320056b41ea430a6400cb4641c563480791ef0eb1e639081e3d6077518d2101d6a40ac798e4000c6c75d89604c40117b0fa9ec8901079994b52d853202675382c518c6000ae78254c614c8959acc239a42180023da1c50d8532256e23906498862008ef8758862440018beea31ac0908031d1d46158132005e24126218c60048ec8750962040999ccc3b9263180f2b9a0b43185320053ac2e86b0c600087e871956344095b8f0639262189063de1971cca2125f2b28ea3b1a423cace82100634840159d06286c49892af1205320c831256e2108e690a2000a9d8414363484011b906ba2c210002b9e09431853200572c16a3b0a4004aea80145628c00196ee9b0ac0990123b21d5258a102d557416e7b2240018df8750f6348495998c239a4390002ade11735863001c7c43aa0b004200a6e85993624c4019cee438ac6900031b1d4625813101c7a40aec18e40008f586dc5328c00155b08280c49892af1a0f72cc42100536c2e873102000e4f5394f624c40195ee8312c098802b5a0f515843201c6e43aa6b1842048ee87d49620407959d043a8c69096aaba0875d912025d6bc1a6430a64008dc835d5624400153b09a9ec6908031d1d771589101e567416e831a4200bc48348720c40014e90ab08c290002a720d65d912001c7b40eeb3182000cd473585218c0014df04b26ca880029da16641853200717aa4a8b10203cacc82550634840156b0828ac318002b960b531853200572c08a0312624aacf8248463484795af02908c6908032bdd07258d102657240aed9964000a7685100614c8014eb0ba0ac3180f2b3a0a5018d21256e3c18e299064008f787584614c8010ff0abb46488002ad61265185320046ec38a031a42018bc845d9324400f5c904a0ac21000395d4e53986300054ec20a031a4200c7775d45618c0017890690a4088002ada1352185320055ac20a2b086400ad58114063484011bf06ba2c6908038bd525498a3001c76c16e831a4200a7585d0e61080091e90ea0ac3100029be1
  | 4 => 0x1080091b90ea1ac71012b35188734871000557426a7b126200cac649d832480831ef0e994c31800237e0d74582210066a39ac29086003cd6619cc218c0014db0ba0ec4988021fa1f65589100064fb26e6b0a4000ad581d0863484955cd02200c4988127aa0273485200056ac18a1b0a64038f4815d5634800f1bd0fa1ac7900030f1d065589100065bba0e2b1a4000ad48158c634807959904a08c69080393d4e5398a301e56ac0eea31a42008bf8759764480019e2c3b826318002aba1352d89310054f426a431a4201cac74509628c0014ed0ba1ec2990f33598873485100143e42aec992204a8ef8758f32884018d8cbb92c68801f331ca634c72000c5e422eab1a20008bf845d932440955c902a80c49880e3e21d40580210046ec388031a4200cac741c963440011ef02bb2648800327d9373485200064e3a6c6b0242008f78758c3144001c9ea729ac408002ba6005158a3000476c38a031262008f78758461cc8091db05ba6c6900037150c724c4310061e3a8e8b1a40048dc8754d63080014eb0ba1cc3180029da1741584202ed6ac08e1b1a42048ed82dd76348001878cbba2c6881662fa1f52d91202676210cc7994424acd6611cd218c0011eb0c38a65180f333988734843022e3a38eca9922000cb474dc5634800147908b96ca880023de1d64185321e573410a030a6400ccd631c931840991df04bb265880029d61741584202556a40a8431a4200dd073dc121440010ff0eb26ca88002a7a1075d8d21006563a0c4b0262038f4815d5608c80187eea3a2c4880029720d64d95100247b43e82b0840008f7815d163c80011ef02baac7900023ee1d601812100c5e422ec10a6000ae7825cd618c00155b09a98c49892ab5a075218d210247a43aa2b0860008ef825d563c40011db05ba4c708002b96065418931024f243a4290220008f787584614c00317908bb66290002b960840d853200556c26a4b102044c7476d95214409599cc239a43900022fa1c64585200052f428e031a4200ab68414561080955c902b10641880339dc9614c4200063bbaceab0c603cce4721c563c8001c9ea729ac5180033354f764c8322ef27296a5b1a4200acd82900634840187eea322c2900030f1d7645852025667398c598a62038f4811d932440091eb02bb062100f3b10874218d212566b388c79924200cb764dc532480014bb0a206c69080a1fa177498d100063a3aee2b1a40008dd8710c6344001938e9b9ac688002ada1353584200047bc0aeab106003cd47158d30c400153d0932ec69080355d94734851000477c3ac4316604adc7721cd21440091e90ea8ac2100023be097458d210162f3aca731c40048f4815d932c40014eb0a214c31800317d94735891001e6b39ac798e20008ef825d1634400f9d4c4b8465180032d1d06158132005374288
  | 5 => 0x802b520d614c4200247643aa4b106000a9e84d4c63484014bb0ba08c690802b5a0c50d853200556422e6b146000a6d85d0f624c4014ef0ab9ac318002aba135358a300053ac2cc830a643cace8214063484015af06a90c2990029b6174158a300047dc3ac030662078ee87100624c4011df0eb20c49896b2b1cb644c5200066631ee498a4200cb4641c532480071bb0f29cc6108022fa1f64585200063bbaec2b026400c9c741cd6244001b90e7b824290002b320d41189310053ac2e86b08404cec42198f31c84011bb0e218c6908023da1f61581320065bb20e2b1a4000a9d8499763484014db0a200c49880e3721d634cb1001e7930ae118c600287c855d832440799ccc438a65180031b1d77258d100066b29eec988625dccc72d8d3148401938c839ac2900062fa1376cc9100056ac0ca031a42008ef87594624c401878e832ac6880038dd5254d85320051fc2ae3b22400287c855d8214c0011eb0e206c2990031bdd47258d100052ec2cc9b1a4203ce47158932040050f90abb2609000237e1d6318d2000476c3881b126200c3f75dd163480955c902a98c498803711cc62485100045f43ea7b224000ae581d0c624c40317908bb46290002b320d62189100247a43a82b084002c5e7594e6304079b8cc638a641901f331ca634c72100557426a4b14600287e85dd930440015cf02b9ac5180028fe1173d951000637b2ee498a2000a75851d3614c80153b083aec690802ada1050d85320052f42e87b1a42008f587140614c8091d90ea12c5080021fa1c655891000556c20ebb126200acf83540624c4014dd0ba0ec4989129d21941d95100061e3aee8b1a20048f487545618c0011db0c39263180023be1d630c9201e667310e690c2000ad48354a618c00117f08baac69001e3b2097558c21006e3298e29906400ae582140614c801878ebba2c488132b9a0450d893100536c2885b126200aad84d4e620400f998e4b1a639080e3d2057558c210052f42cc9b1a42038f687100614c8011ef0eb08c39800237a1c40d8d210247b436e2902204aad683cc8614c8011ef02baac4881121fa1f41d95100071a32283b2a203cae682d4c614c8011ed0e206c29900297a0c74d95100055b426a630a644c8ef825d931080011b906baac408002b520d521853203c76412eab1a2000ab584d4d618c0011db0e286c498802aba1352588101e66a3b0e690a2000ce5621c5328c00139d0739a42901073918b714c93102476412e8b1e40008bd84ddb32840995c902b1e6410803175d753d8d200055ac20a2b084000ae581103624c40156b083aac2100023de057458d2000567c1aa231262048dd8798c328400317908bb260900029d61743185320043fc2ae8b1a2000ab4845cd618c0014bd0a200c69092b351c4634c9212556b408e831a4200ab584d4e6
  | 6 => 0x556c20a2b146003ce471589328c40f1f10ea02c01900b179d65398c2103c6ec388731e4041ce472dc563c80014bb0ba18c6908031bdd462581311e47a432e418a2000ccc73589218c00317908bb2408800372dcc704852000567c1aeab1460008bd84ddb324400155b08286c498802b961b72cc4210043fc2aec9922000acc835d5628c0795cd05aa0c299012b921921c81100062fbaec6b024200aae84d8a62cc0014dd0a3a2c518002aba1370d89310061e3a6ca9022000ad5811006348495b8ee639262188029b6174198a300053742e82b1460038f4815d56204001968c9b8ac690176b3a0840d8d2100c6ec3c8631a424adc4621cd21c400f1e90ea0ac219002b520d401853201c6ec38a731e2000c3f65dd1634400317d09bacc6900062fa1b745852001e6b39aed98e2000a6d8510962040835c904bb66388002f120d21c81100055ac26a5b0a6400c9f74d8d604840159b07a08c498802b3a0f411893100673bb0e29906400c3c751d163440015cf04aa2c2100123d20576ccb1000476c3cca3126200acd82d4f634800117f08bb462900123b609760c810006e2a98e29906400ccf631c931440014ed0b3a2c318002ad61353986300247a43a82b0c6000a6e85d06628c0795c904a98c29901eb320963ccb102cf1d286a1b224000a6d85109628c08bcc843b2a428800297a174118d210056641aeab102000ce7621c5324c0015a906ba2c318002ab612755881000557420ebb126200acd83140624c4014db0a3a2c4080021f617764c1100046ec38a631a4200ad583100614c80155b093aac5180029ba1743189310045fc22ec98220008f587100614c80317d09bb665080021f61e64d951000557420a331460078ee87140624c4014db0b3a6c498802b5e0d725863020d7341081b0a644aad68114063484018deeba92c518002aba13535881000c5f426ec9824000cd5631c532880951b9063b242980123b2097558f2020e73316e29902000c7465dc520440014eb0bb86c29901237e1d638ca100046fc3ac831a4200a6d85993624c4010ff0aba2c69000b179d65398c200056ac1ea430a64008de87143634840117b0e28ec8900123b61f630c9200046f438a031a4200c5f651cd214400153d08380c6908021f61776cc91000657ba6c4b026200a76859d161080015c902b10c498002ad61050185320061e3a8c8b1a40018f787507614c801c3ea92a6c690802b5e0d401853200556c24cbb12624aae681d0c624c4050fd0bbb264880031d19571cc1101e6e2108e690a40008df835d563480091dd0fa12c408002aba135398a3000557420a2b146000aae84994624c4890f90dbaac4880029b2157358a300247b436e29922000c9f74dcd62440831ef02bb26390002b360840d8d210055b424ebb0a64008f7815d5608c80153d08286c69
  | 7 => 0xcd8214c6348401c6ea92a2c31801eb920974584200247b434e690a2004cda7058e32840011bf0eb18c6880f371dc4734852001d7240aeab102000cd6631c532880091b90ea1ac608002b56075218d2125e6b30ee690c6000a6d85109620c4015c904b9ac318002f1209310c4300053ac288030a6400dc6531c9310c4079a8e331a65880032b9d17298d2003c77416e9318403cdc7611cd21c80014dd0a3a2c4081b32b5c864185200071baa4a93084000a7685993614c8015cf02baac4080029da1440d853200536c2e86b146000ce9625c2318c001958e9b12c098802a7a127518d2100673bb0e4988623cec4620c8314400f1d904ba2c688002b960670d89312d557410e3b224003cd47158d32884019aee618ac190802a72116318d100070fa9ca7b22400087f855d16244079998c439a42880123761e4398c200064e3a0c6b024200ab584997614c8011dd0e312c0988021fa1c42d95100056bc1ae8b084000cce631c93184001938c839a42900029760c74d95101e5e341ee39904200c6f65dc963440011bf06baac6908123b209764c72000c5f426ec98a404aae48150c624c4015ad06206c2990030fdd76458d200053742e8731020008ef825d563484795c904a00c2990032ddd061581320055b426a5b0a6400acd83103624c4019a8c638a64900f2b56047418d2102477c3ac599020038dd8798f32c40050f90aba2c48812b350867398d2100672392c298c60008fb8758060cc8019aec638a64900023720d755832100672396e2b1a2000ae581143624c40156d083aac31812af1205320ca3100567c1a82312620087f855db32440015af02a90c690966ab60875d91200051e422e7b2a20048ef8758f32c80051df0ea96c4988021fa1f43d95100062e3a8e6b1220078ec825d1610c0018eeea38ac690003331cd62486100056a41ac230a4000a5d859d0634840117f08bb064880023be09764c1100061e32ee89022000a9d84d4b634849599cc239a42900029b6174358810006c6320e690a404aacf834c4624c4019a8e7b8ac488003175cc73d95100043f43ecab1a2000e2f54950624c4050f90aba2c68800e3ba0b7498f21256663b0e690a400087d85dd263440018beebb9ac488002b960a435842000536c2e8731460008f587994614c80155b0828cc5180030f1d365589100053b42884b0c6000acd8214063484050fd0bbb66488002b360a5018d210047ac0eeb31a2000c7465dc53244001958c9b926290002ad61353584200053b42e873084000a7685d0d618c00155d08280c49881f3398a73086300072ba9ca7b0a644aae48158c32480015ad07aa0c2990123761e4398c100051fc22e5b2a2000c5c65dcd214400187eebb22c29012e37e1d63cc7210062e32ee6b122000cd7761cd21c400156b09a98c29900333dcc7258d100
  | 8 => 0xa0e000c1a466000002920120000002e0580141802f000394040ab0005000024802e004478040c800c0700d07600c00017452000050a81242b02282b00c100ae8100d4008960010000000080000809c018040662240b01c01001c0110601403003040012000028470001600082702801c0a8960e20000400002200c05811002044490010004480081f0c6034030010000c40100501a0180003f02a0e01c8a10047ac3cc830a6400c5f75d4d63c40018e8cab8864881af1d5c465d8d100147bc3aa3b0a64048f487545618808b4ed02396ca88002ada1353d853220d73410a1b0a64418f7815d932040951bf0eb1e651080e3d2057458d2001d7240aa8b10200087d8710b6544001968e9b0ac099002b9e0940185320056bc0a8431a423cccf601cd21480011bb0f320c69092a37a1e634c72100637baec4b02624a8ec865c432480014eb0ba0ec299002f120d21483100052e42ac631a4000e4f5394c624c4018baea3aec690906b920963cc5100066a31ae39822000a768510a618c0091bb0f29cc708003711cc61485200061eba0e9b2a20008fb87580604c879b88c239a43900029da1743986300045fc22ec98240008f787594614c80155908b10c4880030f197745891000477c3ac43126200ae582100614c80155d0932ec49892ab5a074218d212cd56c16e7b224000e676518921440011db0f320c498803711cf61485200062ebaea7b1a42008bf845d8214c0011df04ba2c11880a1f215760c52000566c148631a42038f4815d5620c0995cd02206c49892b74d8073485100045fc22ec18a404accc219ce634840187eebba2c48812ab52055418d210065bb20e29924000dc5531c9310c4894eb02396ca8800395d9763cc5100052f42881b1a4200acf8255063484018eceab8cc6881323ba1e624c63000477c12e8b1e2000c75751d7614c8011bd0e31ac0908023761c5318d200063a3aec2b026400cac645cb30480091e90ea0ac218106b920963cc42125666308e690a40048f4815d563c40011ed0e30ac09900a1f2157458d202ee6a3b6e690a20038f4815d163c80015af06ba2c31812f351c7634c92100657ba6e4b1a2000ad5819c063484014bb0a3a6c6908123da1f51584200054ec18ebb224000c6c651c931440991df0cb8e65900123ba1a734852000717aa4a93102000dc473d8921440955cd03a98c4988062f211764c11000672396c298a6000c9f641cd61480075cd0329ac408003331cf72589100065bba6e2b1a403cace82d4463484071ed03bacc710002ada1265185320061e3a6cab1a2000c6d75d4b624c4955cd032a0c4988f2b9209431853200556c26a7b12624aad681dd4634840153d09a96c6908032b5d07458a3000573c12e8b084000aae849d5628c001878ebba2c6900031b5d475d89311e66b310e690e2000a
  | 9 => 0x1b0141740104500802400003044010000000581680080000e0000508a00800c380020461580102c0100ac01000006000128060003b80280500e0042c80002a0282e80d00e1a0000010060180f02707c0300000203c0800100007000d3a015008020038013a80140300307e018038910000fc118160001c800039026000000150000d83a002002048050090027480185a0062bc4e0000300003a8040000a41e81257c0240b8170260700100b006004b686402e0180581200e0accd06c3780400d89c130000038020000000505200c0181506a0040140006f0080002e0011860080300011201c0101100e18000b8502615c72002002024318010000443f8000880000000a05c0b42300000400000ad20006f00200900c07c46b370ec0000086d04c00c098300100100380204c04c2d01e00002c0281709e17000062000004020790021b80fa5203a02c0400b0a803c46826026228008021a40240b80706a0103c80c0c201c4283602e074068252682b007048038050090020080802287d02a000000350160741f000010a2c0f8c500e06816848
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1810001000401c84641cc6148520254b1262624c4318c0794c4925cc735842000711d9473189214400103f985d074d95101e4b12498110c63484798c47220d614c42037721084641cd21480dfa44216174118d2136f11087651cd21440792c4926065318d21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4d
  | 6 => 0x4e
  | 7 => 0x3
  | 8 => 0x94d
  | 9 => 0x94e
  | 10 => 0x124d
  | 11 => 0x124e
  | 12 => 0x138d
  | 13 => 0x138e
  | 14 => 0x8d
  | 15 => 0x8e
  | 16 => 0x98d
  | 17 => 0x98e
  | 18 => 0x128d
  | 19 => 0x128e
  | 20 => 0x150d
  | 21 => 0x150e
  | 22 => 0xcd
  | 23 => 0xce
  | 24 => 0x168d
  | 25 => 0x9cd
  | 26 => 0x9ce
  | 27 => 0x12cd
  | 28 => 0x12ce
  | 29 => 0x168e
  | 30 => 0x20d
  | 31 => 0x20e
  | 32 => 0xb0d
  | 33 => 0xb0e
  | 34 => 0x140d
  | 35 => 0x140e
  | 36 => 0x154d
  | 37 => 0x154e
  | 38 => 0x24d
  | 39 => 0x24e
  | 40 => 0x16cd
  | 41 => 0xb4d
  | 42 => 0xb4e
  | 43 => 0x144d
  | 44 => 0x144e
  | 45 => 0x16ce
  | 46 => 0x3cd
  | 47 => 0x3ce
  | 48 => 0x170d
  | 49 => 0xccd
  | 50 => 0xcce
  | 51 => 0x15cd
  | 52 => 0x15ce
  | 53 => 0x170e
  | 54 => 0x94b15
  | 55 => 0xb0956
  | 56 => 0x94b16
  | 57 => 0x95415
  | 58 => 0x140956
  | 59 => 0x95416
  | 60 => 0x24b
  | 61 => 0x956d5
  | 62 => 0x94255
  | 63 => 0x24956
  | 64 => 0x94256
  | 65 => 0x16cb
  | 66 => 0x16c956
  | 67 => 0x956d6
  | 68 => 0x14c9
  | 69 => 0x134a
  | 70 => 0x138b15
  | 71 => 0x138b16
  | 72 => 0x1396d5
  | 73 => 0x1396d6
  | 74 => 0x3ca
  | 75 => 0x15ca
  | 76 => 0x170a
  | 77 => 0xb0995
  | 78 => 0x98b15
  | 79 => 0x98b16
  | 80 => 0x154995
  | 81 => 0x99555
  | 82 => 0x99556
  | 83 => 0x99715
  | 84 => 0x3c995
  | 85 => 0x983d5
  | 86 => 0x983d6
  | 87 => 0x170995
  | 88 => 0x99716
  | 89 => 0x1609
  | 90 => 0x130b
  | 91 => 0x150b15
  | 92 => 0x150b16
  | 93 => 0x144b
  | 94 => 0x151715
  | 95 => 0x151716
  | 96 => 0x9d695
  | 97 => 0x1689d5
  | 98 => 0x1689d6
  | 99 => 0x1692d6
  | 100 => 0xb4255
  | 101 => 0xb4256
  | 102 => 0xb56d5
  | 103 => 0x16d456
  | 104 => 0xcc3d6
  | 105 => 0xcd715
  | 106 => 0x1715d6
  | 107 => 0x2c9
  | 108 => 0x409
  | 109 => 0x1343d2
  | 110 => 0x10253
  | 111 => 0x1043d2
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2004
  | 6 => 3568
  | 5 => 1228
  | 4 => 11
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
  | 7 => 2*((h/668+packedAt gbK7 (74148+(h % 668)*11) 11) % 2004)
  | 6 => 2*((h/1259+packedAt gbK6 (171264+(h % 1259)*12) 12) % 3568)
  | 5 => 2*((h/409+packedAt gbK5 (72452+(h % 409)*11) 11) % 1228)
  | 4 => 2*((h/10+packedAt gbK4 (770+(h % 10)*4) 4) % 11)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff81f00fffe01fffffffff027238fc1e3fff
  | 1 => 0x7c03fe000f83ffe0fc03f03f1dadcf3313ccc7
  | 2 => 0x8003fffff003ffff0003ffc0e1ce0fc3e3f0f8
  | 3 => 0x3fffffffc00000003fffffe0ff003fc00ff
  | 4 => 0x3fffffffffffffffc0000fff00003ffff00
  | 5 => 0xfffc00000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x94388030018460851438b1450000185406155b
  | 1 => 0x584b960146a1ada4d84955360ca4cb3312ccc5
  | 2 => 0x1091aad65002d1d610926d94614e0dc16370e8
  | 3 => 0x1234d6b6b68050041238e38b60f7003bc00b6
  | 4 => 0x4202718d8c731e18e3c00020dff00002d9aa00
  | 5 => 0x63c0000e0040181082000800fbfba6a8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafaeaa800feeaeeeafaeaa800feeaeeeafaeaa800feeaeeeafaeaa800feeaeeeafaeaa800feeaeeeafaeaa800feeaeeeafaeaa800feeaeeeafaeaa800, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40483
namespace PEqualNP.Outside.L_meta_40483
open PEqualNP.Outside.L_meta_40483.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 4 := bs0_4_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 9 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 9 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 59 := block_range (n:=59) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 539 := (concat (concat bs4_4_0 (concat bs4_4_96 bs4_4_192)) (concat bs4_4_288 (concat bs4_4_384 bs4_4_480)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 88 := block_range (n:=88) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 664 := (concat (concat bs4_5_0 (concat bs4_5_96 bs4_5_192)) (concat (concat bs4_5_288 bs4_5_384) (concat bs4_5_480 bs4_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := bs4_6_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
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
theorem bs5_4_480 : Interval s5Atlas 4 480 59 := block_range (n:=59) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 539 := (concat (concat bs5_4_0 (concat bs5_4_96 bs5_4_192)) (concat bs5_4_288 (concat bs5_4_384 bs5_4_480)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 88 := block_range (n:=88) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 664 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := bs5_6_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 11 := bgb_4_0
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
theorem bgb_5_1152 : Interval gbAtlas 5 1152 76 := block_range (n:=76) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1228 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat (concat bgb_5_864 bgb_5_960) (concat bgb_5_1056 bgb_5_1152))))
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
theorem bgb_6_3552 : Interval gbAtlas 6 3552 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3568 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)))) (concat (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 (concat bgb_6_1152 bgb_6_1248))) (concat (concat bgb_6_1344 bgb_6_1440) (concat bgb_6_1536 (concat bgb_6_1632 bgb_6_1728))))) (concat (concat (concat (concat bgb_6_1824 bgb_6_1920) (concat bgb_6_2016 bgb_6_2112)) (concat (concat bgb_6_2208 bgb_6_2304) (concat bgb_6_2400 (concat bgb_6_2496 bgb_6_2592)))) (concat (concat (concat bgb_6_2688 bgb_6_2784) (concat bgb_6_2880 (concat bgb_6_2976 bgb_6_3072))) (concat (concat bgb_6_3168 bgb_6_3264) (concat bgb_6_3360 (concat bgb_6_3456 bgb_6_3552))))))
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
theorem bgb_7_1920 : Interval gbAtlas 7 1920 84 := block_range (n:=84) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2004 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 bgb_7_576) (concat bgb_7_672 (concat bgb_7_768 bgb_7_864)))) (concat (concat (concat bgb_7_960 bgb_7_1056) (concat bgb_7_1152 (concat bgb_7_1248 bgb_7_1344))) (concat (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632)) (concat bgb_7_1728 (concat bgb_7_1824 bgb_7_1920)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafaeaa800feeaeeeafaeaa800feeaeeeafaeaa800feeaeeeafaeaa800feeaeeeafaeaa800feeaeeeafaeaa800feeaeeeafaeaa800feeaeeeafaeaa800
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4209682432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40483.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,2]⟩,⟨.or,[0,4]⟩,⟨.and,[2,7]⟩,⟨.or,[0,6]⟩,⟨.or,[0,5]⟩,⟨.and,[1,10]⟩,⟨.or,[8,11]⟩,⟨.and,[3,12]⟩,⟨.or,[4,5]⟩,⟨.and,[9,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4209682432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4209682432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40483

open PEqualNP.Outside.L_meta_40483 in
theorem PEqualNP.Outside.L_meta_40483 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4209682432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4209682432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
