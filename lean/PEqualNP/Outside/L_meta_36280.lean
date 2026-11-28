import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36280.Model
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


end PEqualNP.Outside.L_meta_36280.Model

namespace PEqualNP.Outside.L_meta_36280
open PEqualNP.Outside.L_meta_36280.Model
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

def SBf (j : Nat) : Nat := [6, 7, 6, 5, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36280

namespace PEqualNP.Outside.L_meta_36280
open PEqualNP.Outside.L_meta_36280.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xbd43bf43
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/1+packedAt s0K4 (32+(h % 1)*1) 1) % 2)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x80ffffc0fffffe07ffffc0fffe07fffcf8fe3f
  | 2 => 0xff03ffff01fc0ff83e0fff07fff83e034f1fcc
  | 3 => 0xfffc0ffffe000fffc00ffff83fffc0038fe3f0
  | 4 => 0xffffffffffffff000003ffffffff003ff
  | 5 => 0xfffff00000000fffffffffffc0000003fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xa6082046244842014a12c42946214a98186e15
  | 2 => 0xa58c48a1c915658168555259aa92c294b16cc
  | 3 => 0x14316914483a6aaac109a6b12d3588528da370
  | 4 => 0x58a28e2091230d34a5a0308431c63163e001aa
  | 5 => 0x60c30c38e1c38dc739ce38c601842183f6d800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36280
namespace PEqualNP.Outside.L_meta_36280
open PEqualNP.Outside.L_meta_36280.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1952011814801c03000001c00000002c2094411118fd43fe10ff41fd42fe31ff42fe43fc31ff43bd43bc42fd20ff31fe42fc21fe20fd21ff40ff32fd31fc42ff20be42fe21fe41fc32fe40fc43fd40fc20ff30ff10fd41fc40fd10fe30fc41fd30bf43ff21fc10fd32fc30fe32
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x44080122878f10081cd3c080190884f053600aac061008118000820408a8f12c6dea4885d944309f29085af5250f5885906b108219eaa4433d5390a7ca818e750e30cf298859d5310a7ca52167d4d43b7a92835d538873a8698d794f409e2a2433d54042daa5204f553329f2a6657651ccadea4a1e750c30bba8a41ac420cadca5204f953319faa4653e54cc278a4a1c754c429f2a0613e5410e7ca8085b948109f2a4436d52cc73a86995d54430ae29a413d540c35885994f950329faa2433c548ca7aa9985b14910cea1e655d530427aa998d794c419e2a2415c53442eaa3996b1092096292876c525067ca9105b548109e2a2216e52cc758a4a1db14943aea98853d540ca7aa921eb94842cea1e635e530427ca5a1cf55031afa9a413c544ca7aa6214fd5132af29c433f54442bea6886b10a21aea98837451482dca4185b54830af298855d53d027aa9104fd5120
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x3004220000100040580000000a0000000800000c0000020100000000000000000000000000001021d6315121a318943cc68d6310b328b18954cc28d6310a21a3189438c30e5310a2187195434ca8d6310821c314c42483244294732c550d51ccb0d4354830c9108514822c6255031a358c424830c6254c428b594420ca8c6250c30c550d510c21d6395220a358c42c828c6250d31c350d52cc68c6250f32
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xe06bb4a621443035d85310920a0ae6210a2905057310a51cca8239286a8861411c94354732
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s1K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/37+packedAt s1K4 (2430+(h % 37)*7) 7) % 90)
  | 3 => 2*((h/64+packedAt s1K3 (950+(h % 64)*5) 5) % 25)
  | 2 => 2*((h/16+packedAt s1K2 (294+(h % 16)*3) 3) % 6)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 2 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 3 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 4 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2004088824020000a41280444022914810d095
  | 2 => 0x451891064894a12c0a852429921422b146264a
  | 3 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 4 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faaaa0a0faaafaa0faaaa0a0faaafaa0faaaa0a0faaafaa0faaaa0a0faaafaa0faaaa0a0faaafaa0faaaa0a0faaafaa0faaaa0a0faaafaa0faaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36280
namespace PEqualNP.Outside.L_meta_36280
open PEqualNP.Outside.L_meta_36280.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x400000ed32be42bd43bf43bc42ee32
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x31a86994754c42
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/16+packedAt s2K4 (96+(h % 16)*3) 3) % 6)
  | 3 => 2*((h/7+packedAt s2K3 (54+(h % 7)*1) 1) % 2)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3ffc0fff83ffc1ff07ff07fc3fc0ffd9c739f
  | 1 => 0xfc0fff03ffc1ffe0ff83ff83fc3ff03ee78ce7
  | 3 => 0xfffffffc0001ffff0003ffffffc0003f07ff07
  | 4 => 0xffffffffe0ffffffc0003ffffffc3f80ff8
  | 5 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x58244628925044053424b424c06425a48c318b
  | 1 => 0x9648a19221284a054a154a1442960a8a584a5
  | 3 => 0x30c9145074a5296b0842694baa80c31302df06
  | 4 => 0xa28a208244202a528948084233128a03500a50
  | 5 => 0xc30c38e38739cf9cee738e7022230c23ff6000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeee00eeee8800eeeeee00eeee8800eeeeee00eeee8800eeeeee00eeee8800eeeeee00eeee8800eeeeee00eeee8800eeeeee00eeee8800eeeeee00eeee8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36280
namespace PEqualNP.Outside.L_meta_36280
open PEqualNP.Outside.L_meta_36280.Model
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
  | 0 => 0x3ffc1ffe0ffff83fc1ff83fc3fc0fffece333f
  | 1 => 0xc0ffe07ff07c1fc3fe0ffc1fc3ff078173cdcc
  | 2 => 0xffffff80007ffffc000ffffffc0007ff83fe0f
  | 4 => 0xffffffff801ffffff0001ffffff801fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8244451094110808d092a124064254a4461115
  | 1 => 0x9648c32484a129415285a50c4296150c52c54c
  | 2 => 0xc910a0d294a12d421094a5aa80c2259816e0a
  | 4 => 0x28a21049080a54a6252042133128a011a80aa0
  | 5 => 0x30c39c71ce739f3bb9ce73822230c461ffb000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeee0e0eeeea0a0eeeee0e0eeeea0a0eeeee0e0eeeea0a0eeeee0e0eeeea0a0eeeee0e0eeeea0a0eeeee0e0eeeea0a0eeeee0e0eeeea0a0eeeee0e0eeeea0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36280
namespace PEqualNP.Outside.L_meta_36280
open PEqualNP.Outside.L_meta_36280.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2d80410000001802000801c9001000000240082ff42ff32ff31fe31ff41fe30fd30fc43fc41ff43fd40fe42fc30fc32fc31ff20fd21ff40fc42fe32fc10fd10fd42fe21fd20fe10fe41fc20fd31fd43ff10ff21fc40ff30fd41fc21fe20fe40fd32fe43
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xc21dc43ccafaa8085f94032bfaa6637d51842b8a6a05f14941eea98417e51087b88718dfd5330bca80837d51d0b7c84a15f94241bea9083f6310c6fca2215f14540fc282657c5050afca6905f95120b7a92817d500877aa9185fd5010bea9e81f5518c2e8a2a07d88710bfaa0637c52842fea7885f95131bf29c217e53102fca4197e84010be2a0437e54107ea6290df15210bea9c417e548877ca8105f54f10fca02217e534437c8620ef55020bfaa2637d50cc6faa610df14943bea8083ef20083de4310df55021bea98817f53083bc6298df54a31bf290437f54ccb7c87217d48510bf28861de324cafaa8107d94630b6a9063df438c7f641107e90110dfaa2637e531077e80206f50441bfa82637e518c7ea8220df54630dfa0e81f7410c7e863885fd5032beaa4837f51502eea2a077d4d40bea9a43ec42082eca3215f54341bea96217e53d06fea498df54732bf2a0417c51483ee6210fb14940bf2a4637e5290fdc6590d794c20bfa9c4375518c37e8721df94f21eea98437e50086fea9107d50710fb082217f504877a84214f15131bfaa061f7214877a82a05f94643bea9c657d50907f660105f94640efa1a87dc430c2faa9885f94331be2a065f741907ee6318dfd4542df21e817f54082fea7105f94b41bea84877e530c2fca5085f14c21ef21887775150efea8985f14530fba0821bf4210afca720df94441bf284637e500c2fea0a0df94210bf28c85bc43906f8a8184f55230bf294837e51886f8a9105f14131bea96637c52503ba65987bd0a42dea1681f641c42fea0995f14543be29c43f741486faa7217b4cb21bf290637c50486fca3985794e42bf28083df310c6f8a6107dc4010faa8c857d54cc2fca218f794e42df2a4617f51482faa4185f15110bf290837e54cc6fea4087ec4210bea8c6576518c2faa7185fd4d21bf2a4217d51082f8a7105d54420bf290417e518c2fca7a15f95220fb28881ef21086fca618dfd5132bf2a0217e508cafaa5205f94440fba0e63fa50107be61187d48421bf2a0437c54886faa221df94242ee99261df324c6fea8885f55220bea8463df53506fea6a15f54332bf29485755190afca610df95232fa20c43f950106faa6105fd4142bfa9a837d5210eeca2205754c21fd902417d528c2fca5a07d8c521de218857c548c6fca2105f54a43ef18261f731c42f8a990f7d0c31deaa0217651082f8a8906fd0441ee996637d520c7ea6310df15121bf290857f54c82fea6a07714d41ba28a877c54cc77e82a05f54c41fc880217e52102fca1205f14d41dfa14857e51d0fec8220dfd5230fb90c43ee520c77a80205f15320bea9e83f830083ba64197bd0a20fa28a817f52c43dea4a05f94b30bea9c817e530cbbe65195f95110fba8a877d5110bde84a15f94343bf28665de53082f8a0a1df95310
  | 1 => 0xd5390afea918fe50040ef298437e52cc6fca621cf95230f7190657f53c86fca7885f94843ef98c63bc544cbeea2995fd4d10f710a437d52042fea6905f55131df20a83fa40102fca8205fd5321bea8c81f621443e88218df14c10efa1a65bc43d02faa510df14f20bf2a2657e524437e85a07dd0610bea8e417e5090efca8187750c43bf28683df300c2fea4a1df54620bfa8287f751502f8a898ef90d40fd100417e51c83e882085754e42bf29a437f52503de84107d54420bfaa465df438c3ea43887d54432bf29687ed20082fca0105f55331beaa2437e54ccbf680a05f54031bea94837d548c2fca890dfd4910f799465bf40902faa5a1cf55010bea9c437e528c2faa2195d54432bf280217d52442fca021df15031fda04817d5490afaa6085f55120fda82657d5190fbe65985f54430dea12817c50506fea7907b4c832be2a4617c504cbba60185f94c10bfa94217c53842faa8997ecc230fb884217f514c2bea6a0fd4c431fd88221f940842faa9195f94342beaa4637d5310b78a898df14910faa0a21f4514cafaa5084fd5131beaa2215d53082faa818df14d40beaa643ed32486fea9885f94732bf28e85df324c2faa5a0ef95010af298437d52d02fca7105fd4e10be29a217c53c86dca418fd94420fa18a216c52502f8a5887d10731f799265fb304c2fca018fe90210be29261fb30c82bea6a05f14542bf294637e52042b8a6a0df54730bf29e417c54ccbeaa2204f55020df21a877d51103be6598fb90842bfa8a877d53c877e8621dfd5210bf284413e54082f8a7884f15132f690843f45150fec82886f50c43bfa98437f514cafaa910ddd4532fa18e437551102faa1217d44010f6a90637e5110efaa1a1fd88421bea86857d52102fca7a05f95031de218837d5010ef8a8105f94830bf2a6437d51d02fea810df14d21be2a6217f524c2fca320ef50740dfa0c837c524c6f8a9985f55030bea8085df430c37887215f54d20fb28c857d5190bf240105f14d42bf2a085df4390efca6105fd5120fb18c437e5390efaa921df94c42ef990657d53442fca0215f15232bf28c41f7314c6faa7085f94e21beaa0657e528cafca3197710c31bea8465bf544cafca9985f55240bea94417e548c3be87996f90c42bf286437f52506faa7a16f90e419faa2657d54ccbb886995f15132de21a817c54042f6a0997dcc510bc28265bf42502fca2195d94432fa20a437d500cbf460187bc8220bf29c85f6510cafca0205fd5121bf294817d54842fca110df54321ee21c61ec428837c80a05f14d20beaa6417d53c82fca5885f145329f2a021ed4210ae8a2997dcc721beaa2617e51d02fca8195f15130bea9c63f431086fca720774c431be29021dd324c7ee82a0df54743bea9661f9300c2fea910de94041bea9c837e54c83f061907dd0621fa20
  | 2 => 0x10006e0d81d0000208410024160094600000010050040d0180b014000183c2d44f5b802890000680006c05034000c4030000700400014000049f0680019c2402000084000850601c1005c15008000a40000c020057301c0000405048df1341b00c050180600800008000040001806020040100109c0d0240004443364000002600c010a0010001508c18000000414c024010080000004000071c0ea02c3201c04000190040000843000ea8080a034000049a00c040101800c01008000700377c000d803004000009b16401004090100704c24028000040700509018033b00616009090050141301c0001400008002887a00000028015bc06000020040071c0a00c0200c0000c0006c000c45400c00000001840105400008007b4000142438c0000c010549f01412000070d4000003f018050003270020008001d807000030000503c4e05010484000080100000008eb014160000d1200900c13158340600000c01000000040100004bea8443dc53503dc6490dfd4c10bf2a2617e5410efca1187b88120bf28821d
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x45050a5d6394b409d594410423d65950209d19521442d4614cb31d9185520c67561943328fd91530863f6454f109d984524c35453145409798c528435443145329e982544cb6452145409ed81544ca7b654c0309e580548c63f64549108f593520423f6454f209d18553c82756510431a718d411067561d52309d18553d025d63150208fd9541107584314132ce150504ca3e64d48109d986544ca3e64951328f19153c832c4314940c7951530827761551209bd954210a3c6454c21d518553086f160107319bd89544834c53d49409798f548426c6254d108f592500c25c63551109d98652d032e43149408f19152442766194b439dd8553c825e6394b419e980540876632544329798e52d031c6454c21b51854310e7561150208f596540425f654c4319d584524c35753d4540d554d5190a7960150329e181534867661d52309d185540c31d63d51329d586544cb56535442097d8d54486f160104108f593538865f654c030d9d48515027461551328f593530827661150329dd85544c71d5410e30cd550418872c6255020a7191310c6d8604cb309d18553483346155010c7552530825e63148108f99250cca766115230cd551100434c524c9308f19153c42f06150210d3d0d520c66e6215030d3549310c63d64d4f219d58753082776544010dc144504cb3643145409d58754c834d53c84218fd954210a6d62d53308f19153443c532cc7219d584548835553cc4219b58853c431c544c9319b98853042796015031cd10c51503365494420d954a310c67561d50209d997314425f63551319b98b54c425d63d53219b58b540c73454cc5318f993530435553946429dd85544c2746154c429e580540873554d0410dc505501073643145438f990530425c6355010ad1854310e3d64d4e209dd8553d025f63550109d185548829c63505409718d54887574394630d554e510823e6515132b958831c42776154d219dd855310a7665d0521d9149214425e63d53209d185544c33654946309bd89544434d53484219d98650ccb655210431ced05501067661d4c209798c540867b6054d20b518d411069c63507408f994544c63e6494030d914b515025e63d50209b98853086d46350710b9588310867a6015032bc580418425e63150209718d54487553254432d94c9510ca776548421dc54540103355454420c7d50434cb395484010ae982435033551d0040bc18121442756194b408f99054082776155110cd150514ca7561d53309758f54c435653546429b98b54cc25d631481097d8d54882766115010ced50504ca6e6214f109758f540871c53905418f990520437351141329d9845050a3d6414a10c7952530827960d4e21d514f515027561d52329e980548866e62d5031bc580410c63e64d4e2097596530823e6414c2097d8d544427661d5021
  | 1 => 0xd0004462000c820120a01038000e00800020900a480029088f420977182800016786c9c1606804181b1c0ec2800000181c0c0e00c00080382824030080002006184c5606081100b4f281f488010d8b8000297d8d524427960152219d5865090e7661150209758f540825c63549109d98754082786055121dcd47504ca3c6454d21cd153514ca5d63d5320cd551518c25f6550c438fd91534423f6550c438f19153482766590510d654f300826c62551309e9805404276658c521d5d0c514ca3e64d4e21ae181425023e6494331ce551100425e63d5321d554c31c427565d04109d9865090e5e63d5032dc90550107586054c20b918532c874f5314940d9d4b515033654544209b588540c65f63551309d98754c835653946428fd9153482f160105219e195404433854d41329758c54086776550441d6d0c504ca5d6314b108f993538423d6494332cdd50514cae5620c7219dd95310c67960951329d584530827565cc4219758c5244365524c431bc580418871c6355010cd553100426c6255110d554c3108674615512097997434cb1f6355010cd545401023e6414a109d987540ca7661d4c109d984530827661148109798f54c423f6550040d5d0c5150e5c6355120ad191310c72c52d0940d514f41507b141501108f590504863d6494331c7152314c65d6510c31d594e510837051d4132cd550410435753145408f593538431c54cc931dc546401027561150309d984548827b65440109798c52c427561d50329b58b54c423d64d4c10d554d210865d6594c2197d95320cb364394642cd10e5190b716014540d510e518c25d6314a10d554d510825d6394b419bd95320cb3451d05408f590530833a4354041e510c410c74d52cc4318f992544c65d63d52109d58652d0e6d65108209d987538827a60150319d18554cca5e6314c219798c524426c654c921c755153083c5324c5218f990540426f65484218fd91534867761552208f99353c873754d45329798f540871f63552309ed95401026d6214c10b9588314434f53d49409e596100427860551329d98754cc23e64d4c209d584540ca7b6548020c7d4c435034c53149409d984530865d6510c309dd85544ca776154d20b518d414433b54d4132ce10d50106b4644c521d5cc9510ca5e6314c20cd55251083555388421d310d520c63d64148109bd89534426f654802097d8d544827a601523197d8d54887355494630c754c4390a6f6255130c7d9153086776155030cd951518c27a60d4e21ad191318867b6054d219d594310867661150309dd8554ccb6552d04319d195314865c63552209b588540c26e62150319d98453c827465505109ed8154487b341502109d987548cace62d0d329d587538833941540419e594300832d54d08208f990504867561152309d58453c823d6414c109d58
  | 2 => 0x1078085e020400000950d000946e0081026051b05800060081c440002009405b06000f20c320552c01070fd7c02051e050290381444023984c96000004caa023c0b40000028000044458140014000b00a3
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x212ab310800000000000000018518c6155010c48c8a926218e4553588310868c39a82a8083315c662d0d32d2086b008218e6152580410c68a3a2a618e21641cd4150110c18c8a926218d147355041042a2b88a499261451cd5410621c62a8b00820870443548410c70a320c2a9843515cc5248510962e230284a04b1741812144258b8cc121a81a1191324c521c62a8b008310e455358831c428a3a2a618843541cd4154041
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x280a048454d620c710a10835516010410e00435496010431a10835516010621a048454d620c421
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 5 => 2*((h/289+packedAt s4K5 (16632+(h % 289)*10) 10) % 616)
  | 4 => 2*((h/145+packedAt s4K4 (15732+(h % 145)*9) 9) % 414)
  | 3 => 2*((h/22+packedAt s4K3 (1225+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s4K2 (300+(h % 8)*3) 3) % 5)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffc0fffffffffe07c3f07fc1fffffff8478fff
  | 1 => 0x7ff01f01fff07f803ff87fe1f0ffc0478f27c
  | 2 => 0x7ffffffe07ffffffc0007fffff07fff80ff8f
  | 3 => 0xf80001ffff8007fffffff8001fff8007ff03f0
  | 5 => 0xfffffe00000007ffffffffffe0000007fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x105215124412840140b849612518c5504384b5
  | 1 => 0xb2864d21c924ae58115ac2eb0b8d683458b25c
  | 2 => 0x43082844834822aa9402048c52a432a5805b0a
  | 3 => 0x622cb089120e3334da6310081cc620c6ad03e0
  | 5 => 0x8430c10e1c70c5c7238c67318008430376ec00
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfee0fee0a8a0a8a0fee0fee0a8a0a8a0fee0fee0a8a0a8a0fee0fee0a8a0a8a0fee0fee0a8a0a8a0fee0fee0a8a0a8a0fee0fee0a8a0a8a0fee0fee0a8a0a8a0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36280
namespace PEqualNP.Outside.L_meta_36280
open PEqualNP.Outside.L_meta_36280.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc65ed420cafca0217bcc932bea86857e51d0fea42887e90110be29c43ef42083f621087794c21dfa148575510cafaa420df95032fa88021de314c2fca190df95310bea8e417e5290bdc6490df54032f799441dd324c2f8a6a0fd0c710eea9c857e53d06f8a9887e54041bea96837e52cc3da859077ccb30bf288617d5490afea690df94331bfaa0416c52503ec83885f15331bfa9c43f5510cb7e85a05f14d20bf28463ee20482f8a098dfd5030bf29863df4350efea8885f55243bf28c617f548cafca1217d94642faa8c857d52842fca8985f54831bea9221df328cafea7105f94043bf288216e52c42baa6205fd5120f710a43dc43ccaf8a0a1fdd0731fd90441bf42503be64197b14930f721241f521086fea2997754c40bea8083ed4210abca7a16f55020bea84637d544c3da4210db14930df202816e52102fca9985d54420ef21a617d50d0efea8085f94820bea9687ed520c7da8590fb54840bf28665f731442fea2985f94d10f7296217c544c7be8618d7d4d40bfa9e41f621c42bca7217bcc820ef298417e54483e88290df94c40bea8683dd53086fca320774cb31ef21a63f541c42fca318df94b10bf296815e53843eca3185fd4810be292815e53107da401077cc631be2a443f7410c7bea6905f94c30baa8c617e53d02e8a2a1df94c21bea98417f540c7f26018774c931bea9c417f504cafca5185f54430bf288837e5390efca6085f54743bea88657d53482fca4207754f42bf28e817e53482f8a690df94821f7a1285bd4210af8a6085f94832ee98861f451503ee4310fdd0641ee980617e5410afca71077d0e30be29a817f54086faa8105fd5230faa8881fa40842fca8185f54c10fa18a217f528437a8621df95041be2a0617c50486fca5195f94421f7290835d5390afea7885f94732bea9c43f641443e882085f94f10bea8e657e544c7baa7085f94040b6a9081df53486f8a8995f95031be2a2437e500c2faa720778c730bea8e817f53482faa3a17d94440bea9c217f524c6fea6105f14810ef21e637e52d067aa8105f15321be28a657f54c82f8a790df94341bea8c217d53c42fca7205f54420fa28a87f741886fca3905f94643beaa483ee32c87ee82a0d7d4d41ef194637d53106f8a2985fd4520bea9843f441cc6fca5085f14e10ee21c637c524c3baa620df15210f6a9083ee320cafea898f750d30bea8c817d53906f2a020df54b31bb28c855e53082faa318770ca31afa9a4376510cbbaa6105f54840bf2a221ed42ccbbe62187794c40bea9e857e52cc7da43105fd5331fb10a21f631487de4310f790f30bf28c43de53d0bba65987b94b43bea8c417d5110fb862987d50510fd982617551102f8a7107b50920baa8c85f7318c6fca520df54a43ee29a81fa50106faa9087d94420beaa065de324cafca5205f54a31
  | 1 => 0xd50c87f48020774c431bea80877e51cc2baa7a17794e42b6a96217f53442fca6217b94831beaa241ee42ccaf8a9195f94021ef980617c540cbde4210f78c130bfaa4435e53102faa010df15110fc88021ed52c42faa5205f94221be2a0435c53507de65195f54331be2a2417c53c42faa898df94641fb208837d5210f7e8220fb48420bf2a0877d500c6bca610f710c30dea0081de320c3f460185f94010bf28c857c548c2fca2195f54440aea9841dd438cafca8086f90942ae29a43df310c6fea4a0fd84110fba0c21dc320c2fea8985fd5210be292213e54082f8a9985f54b10b729063ed32486f8a6a15f54642dfa0081f6510cafaa5985714d40bf2a043f920082faa121774c630fa98a43dd43cc2fea098df95220bea88856f52502faa7905f15020bf28685ee420caeea2a06f50b40fa20c436f524c2faa110fd8c431bfaa6617e50083dc859077d4d41bf29e41df438c6fca890fbc8220bb28841df434caf8a2a05f54d21bf2a0417e508caf8a7905fd4943faa08837c53086bca7885f54730be2a6417d52906f8a8087750c43bf28881dc430c6faa9987d48710eea18657e544cabea6905f94f42bf290857f54486baa7085754f10bf280657f53042fea910770c730fca04217c5150bb8a6a0df55221bea84877d544cbbe63185f94632fd882217e510c6fea610df94831bba8a877e5290fbca7085f94e42bfa9a817d54087be64985fd4940bea9c65ec42882fea4987b4cb21aea98835d53087eea2a1fdc4010fb98a637f5050bde4310778c831bfaa4637d5010afaa9887794f10bf2a421dd53c42f8a8985f94910bea9a21bf4310ff420085f94e10f6194417e50882fca910fe88020bf290217e53c87f661185f95230fb18c43ef20082fca990f70c831bf28c417e548c6fca8207b50921f7210856d52d0fdc8590db94b43ef298836e52106fea7085f95320ef99263bd42502faa8085f55240ef18a637f544cbbe8721df54e30bfaa6437d528c2faa5a05f55320beaa643df308c3de85105f94c41fb98e217f5150afca690fd4c431ee21c617c53082faa790df55331bd280837e50902fca621dfd4121bfa96217d548cafaa321df94a31beaa463f721486fea2a05f54c40ef996637d54882fca3a16f50441f7a1485f551082fca710fb14940ef194617e51082fea790dd94630bf290837d528877c86a1db54841bea90617e52d0ef8a4a0fbc8420be2a0637e50842fca018f714d20f6210417c504caf8a498fdd0521bf290617c54883b865185f14141fda02817f50507e883087d4c621fba08217e50906faa890df54e42f6190417e53906fea9997e50040fd90241ee521037e81205fd4543efa9a817d5310afaa7a07b4c832efa18617f53506faa1995f55230bf288857e5210efca9195b54831bf284617d538c6faa120df94c20bea8
  | 2 => 0x8100c0000c010043c0040010c1d0900516400004090640d000030102703806178490080c00c0200406170000083a11cac0180f0045d0280002c1a00003078090780004027000000042314c0a0040900013010000000518402000aa0001500005000050240a0000d09400010000948308c0c008110740c0500700c95008000c804000130903801c0002c8e00400004000600a0002d0002c03c002583c01404000003200b000020440900c2001006188a40040c17c010000600c04038019f4170003005409020051f80300023018010b804000050b80904c070015f0000000000000071a40f00400030000380300410024040401f0081b024ac0200f00c3502c0a0080100c068e00a00c00038370040e00035074410001a008110000406c05010130980f028002200b000ce0200e000010001b0001203002004040024802c47410020380812c0037400fb88421bf41907ba8698df14d10efa1e657f54c42fca9996f95020bb288815c53483eea2a0774c832beaa2217c52c42faa4087710d32f7a9281ed52d0ee8a2a05f15231bea8465bf4390fbc87195f15332fda04817e530cbdc8490fd54630ef218877c5050bf280885f14943bf2a6637c5150efaa9997bd4930bfaa0657d540c6fca121ef90541ee29a437c51482f8a5085f54f41ef218657e50d0efea6a17d88421beaa0617d52882fca020efd0842bfa8287f4410c6fea4885f94443eea1e637
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x754cc2d5610ca309b58b53c425e63150209b98853c4355534842197d954310e6d629464097597430c65e6314b108fd954310e5f63550109d597410425e63940109bd954210a7565104109b988548c65d6394b419718d548867b6055132cd55151082776155130d3149324c25f63543219798f54c866e62152109b996424827960152218f990520426e6215110d354d210826d6295132d350c524c2756194243c7551530826d62d53109e580540c75653946429d984540827465505109b189544435453d4540b3189300c27661d50219798e534827a60d4e2197596320c26d6215231d3588534865e6395121d554d5190a5e6314c21cb55032082d46150c32d5947308c277654842197d95310c25d639512097596430ca6e62944109718d544866e629513097594430c6756194332d9909510ca5f654c8329d9865090f4c6254e42d354f320825d6510c30b9584320831d5494c20d354d210866f6254d209b9885150e776155110d394e52c42756194b409718d51d02d463485109798f540834c5390921d354e52c42cc63484209b98a54cc66e62946409798f54c42776155030bc58041cc67461553329dd85544834f53d4940d314e204825e6395321cd55251083665148420d590d510cb5632946309d9845050a5d658c831d514c414865e63d50329d984524c25e65cc9319dd8554cca5d63d4b109798c548423d6414c109e596100426d621454397d8d5488354538c521b9588314427561150329e580540867661150309798e544826e6294630d314d424835653d06108f99054082ce62d0d3297997324c25f6354910b398f428825e6394410b398b430c25d63152219758e544872c52d0940d954a310c65c635491097d8d50d067561150209718d50d065f63548109758e510427561d4e209b588548426d650c8209d984548825d63d5021bc185408434e53548419d185548827661d53309718d54442d46150f31cb55120083c6328c5219758c54442756114930d3189530825f63551209d984530825d63152109d19521442ce62d0d439758f540825e63153109d584548825d6394620b5185434c27665905109b58a544c7365454420b398f4250a6d6214c10b9988414865c635512097596530834e5394841d50ca518c36552104319b58a54cc65d63942419b58a518c25d65d0c309b195424871e5454c20b358831cc3666194b10b5185434c75532544329e980548867661d4c20d9584524c25e639424197d95310c66f625404397996434c74d53948419b98b54cc31e5494c209798f548425e6314a10d314f525026d65d08209b189534425d63148109798c53083554354432d9984524c26e6215030b5584320c27b6548020d9d4b515025e631522197596530865d6314910d354e521025e6510d329758c540432d54c8420d354a320c63c6454d10
  | 1 => 0x87666194841d594e510827b65440109798e519025f654c030dc905501065e63151109bd8950cc74d52cc431d314e32487595354041d914b515026c6254e40d314c52502e5610ca209798f54c82766114f209758e519023f6550441d654e501074d53548409dd8554882d463505109d987540823d64d4c20b398f4290a6d6510820d954a511023d64d4f219b18950cc74c53909209d984540ca766194b40b318d218826d62944109798e54c82cc63480209d587548c2f160106219758f54842786055121d958a518c3715150040d554e511026e6215310d9509510cb4c4354831d94c9510cad463504419b195324865d6314b109bd8950d072d5448420d3148314c27561d4c20d994921c432d54c80209b988540874c528c130d394d52c427b654c030b358e42cca6e6215020b3588314c35553946429b58b54cc32d54d0820d5cc9510ca5e6394b408f99353c874d5354b10d314d42487575314540d314a314c2ce63d08209d587540835743946309b18950d063d6414c209bd95200823e64d4c20d314b324c23e6414a10d394d521034d524c431d354f21082756114c209ed95401034d5354841cb549401026d62150108fd91524427761551329d984540425e63148109798c540c6f160104109e980540c67661d50329b189544c34e4314930d554d51102766115230d98c9510ca5e63141429718d540425c63547209b98a54cc35453d054197994534826f65484219d987548cb5753d45409b588540c7565394440cb55332083716014540d958652d0f5653544409758c5050a6e62d50319798e5188276619433297996434c2e66190921d514f414866d6214f108f590528425c6550d31b398b438c35553487108fd91534425d63953219758c548825d63d5321d354f210867461551309dd95411075653c421097997434ca6d62153109d185540c2d46150c4397195434c2ce62d0f329758e50886746154f4097d8d54886ce62d0c319758f54c425d6315310d9549511027a60150219b98b54c423c64549109b588544435443946309b58b540c66e6214c2197d8d5010a5c63544429d587540ca5d63951329758e500427561152309798f540865e6315010b398b438c63d64148109758c540827561d5232d558453486ce62d0e438fd95401025f635472097d8d544c2776154f40b518d41c426e62150109758c540867865501109d58453c823d6595020cb151424865d63145429798c540866f6255130d518553107555388710d954b410c66c65509209718d52042d46150f30d3d0d520c765524c431bc181214427661d5320b558c41cc65e6514d219b588548c3c5324c521b5584320c65e6394b41d514c515027b60551219798c540c2776544010b5185438ca7665cc5109e980540425d63d4a109d58754c82d5610ca319d987538825c6354a419d58
  | 2 => 0x613c05000030140a1380600c0a000056a80000405000004b8070c001241731080e000ab00009010a70a004350010000102010064341dc020000401c004e411001420100043c06034000108102000048010045f00138038b80004b004040141500009000f07007a00002360001383265000008015ec2d04c0e0001b551cc0d805010a6114560780207c00004021700e0a01a00ca45c40204c00000506dc1600817000020402f188f2000120c0000000325400010050080000806000001016801c006a80906005010060240a03801050c001000074c400044011a05541f00001050000e000284310080120c0a000140b4280000b001e5001ca028025b00106c1900406004001480000003050000600017409160022240f11c000d811016d46348710d554d510826e62d4f1097d8d51d02766194b439e181544cb4f5314940d998652d0e7661148109bd8954482766114c21cb550420835553cc7109758c528436662145439798c5150ad563105219d5845050a6f6254d10da54a501065f63544429b596420cb2c62550209798c52442746155132cd952510825f6550c32d594d5190b6562145439e580548c66e62951319798c5488357431454397d8d544c67665d0521da549501075653544209dd85544c6756510431b358e42c865c6354321b558c418865e63942219d987548c2cd6390921d554e210875651cc6309758e52d027661d4c10da949501066f6254e409798e5348679601503297d8d529076a52940419758e54c836452145409b58a544c2f16010521b5986304c274654c5218f990530434e5394840d9d48515026e62150319758f54c826d6215030d9949511023f6550842d998a518c2756115030d554e510825f6354a409d18554482e5620c7108f99053083565310610d3548320c756514c6309718d5010b2d52d0040d518553c426f62551109bd95320ca7a6015032d694d50107665294440b598e104437141540419b988548c27960d4e219dd95310c66e6214c109d58652d0e5c63552209718d52902f16010610dc546401027a60152319b1895010f5a53940419b58a54cc25e63d4b10bc580410c65f63551109798f528425e650c53097d8d544
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x3000618000010e100c18355263d0820a8ae528a63185447150c524c2a839a82a80839494d6010610c1aa831a421064452986304c322b12c229a43515c86154f10a8ae2312a6105457218553106a33968628a8789551610c82089aec29c8490d4672d0e518c262b90c2a1a639414d6010521a8ae2312a72160d5418d2008262b8cc5a1a65131d953484208aaec2988290e6152580410c6a2b88a499261151d95348710
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xc01008458714a618c130845869cb4394630845861c54314930845869cb4314543
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
  | 4 => 2*((h/228+packedAt s5K4 (20482+(h % 228)*10) 10) % 539)
  | 3 => 2*((h/15+packedAt s5K3 (1225+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/22+packedAt s5K2 (240+(h % 22)*2) 2) % 4)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe0fff0ffffffe0f0f0fc3f03ffffffc0ccfff
  | 1 => 0x3ff03ff1e07fc3f00ff1fc7fc1f0ff0233727c
  | 2 => 0x3fffc001ff87fffff001ff8001ff0fffc3838f
  | 3 => 0xc0000001fff803fffffe000001fff003fc03f0
  | 4 => 0xfffffffe000003fffffffffffe000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8222841021008001030240908c5111280444b5
  | 1 => 0x94618a82471116304550d42384b8aa1a11525c
  | 2 => 0x188512a48a3612d650419905112a8cd2c3830a
  | 3 => 0x11ce2cc914639b6b6e64100a29ccc8637c03e0
  | 4 => 0x210830001844218c8889224c30000081aaa800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeea8a0feeea8a0feeea8a0feeea8a0feeea8a0feeea8a0feeea8a0feeea8a0feeea8a0feeea8a0feeea8a0feeea8a0feeea8a0feeea8a0feeea8a0feeea8a0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36280
namespace PEqualNP.Outside.L_meta_36280
open PEqualNP.Outside.L_meta_36280.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x60005801f00800800890430830030713c2042147007f84001fd2001ff54c057f5401ffd4005fe42007f8c805ff41007fcc405fc40017f90001ff2001ffd4807fd5200ff0c4057d5400ff88405fc42007f48405fe4301ff54001ff30007f0c805fc43017fd0c01fd32017f55005fd41017fd0801fd31017fd5001fc3000ffc4005ff40007fcc805fd42017f95007fd51017f50c01fd3000ff90403fc4101ff14801fe3001ffd4403fc5101ff94807fe50017f15003fc1001ff94c01ff2100ff94405fd4001ffd4c01fd1001ff14003fc2101ff14c03fe31007f88001fc20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x28641eff08630197f82119007dc314c40fff9904003bf99720007fcc4988bbff40cc80dffa92200effd5120005fcc79003ffe654805dffa1e6400bf589100bffec999003fd2148039ff2126001bf98420025f8c098847ff418805dfe2066413ff10720015fcc8908d3fd508c83bff29a6007ff5903203dfcc50801ffe60c840fffa146423dfd51210d5fcc6180d3fd518c80fff290640aff94420127fca09081bff5044031ff2106001fb08721007fe649808ffc6448417beaa04004ff1421014ffe879883bff64480037fb022000ffc811006ffc4290013fc10c8035ff2a66033ff1523211ffa84908a37c654c40ffeb286404bf19430015fcc89001ffc21cc803fea0a2004f78c130045fac90805fff310c061fe21a6407bfd9721007fa6598057fd50c8059fe2a06404bf19630137f8a190813fd640805fff8826410ff9062003ffec990806fe618c82bfea8e4000f7cc930007de649903afd6448013fe29c2030ff951320bffc8799003ff634400ffeb064202bf19121027fc4108013fe4088047fea1a4209ff54e10007ba659802bfc310800ffc9004004fe0421003df8cb9003afd628800ffe1924207fb90832007fa6490007ff314c409f79044021ffc43300bff887980a2ff654c43bfea82602abf5973103df8c7908a2fd654c40fffa16401bff9453015ffc621901ffe52c800fff90c4007fd58432077dc849009bfd53c8439beaa26009fe5421000ff8839089bfc53c84017f31a202cffd5032027fec81801ffc618c801fd9826003bf19530025fec71001ffe324842fffb266207f78c932127fea090817fa4044009ff3204008ff5521003ffc431901ffe608c83fffa1c6024ffd4921027fec41806ffc314c04fff2126217ffd8332107fea318013bd6408029fe2a6400eff99120187fa8499017ff404401dfe3224017ff0cb30007fe6090013fe300c00f7f3146428ff94d3101dfccb99013fe408c0637fb2a6401ffd07310d6fea998003fd318c0097e30c6030ff50d32057f88210003fd6148061bfaa26400ff98132077fca890097fd54c8409ffb0c4005ff1091001dfccb90802fd61c800ffe90e400dffc412003ffa641903bfc43480617fb226407ff8843200ffa8290803fd614c035fea1e6000ff1891000fe86298843fc518800f7f3122029ff59331025f8c6100c7fe504c839feb22601aff50b30027f840880cbff108c827ff18e4017ffd87301b5facb99007ff318400f7f3106401ff90731007fc6598053ff54c8025fea944004ff99620027f8201001eff658c809fe2022031ffd9532027fec210013ff658403fffa0c6004ef99020005fac790817fd4044009ffb086017ffcc83003ff8a510003ff624c00ffeb086400ffcc9310c6faa81808bff52cc009ff286601bff8c53018ffea49905ffc310c00fff10e4001ff94531
  | 1 => 0x3ff508c00fff216402fff10532067f8a610003fd6348451ffa9a6204ff5022006ff8829008fff5448443fe20e6007bf193211b5fecb9901eff650c80ff71964200ff4c91018ffcca99017f94044003ff20c2004ffd8c2017ff82099017fe5444051fea926204ff992200cff8a418003ff614c045fea866001ffc861015ffca219067fd520c00f7f316622cdf55032027fac818013fe30c8009beb284003bf99530025feca1801efc624c05dfea1e6404ff98e10165fac8190c7fd514c80ffe10c4016ff1443018ffaa099007fe41c840fff9946401ff8c52103fbe6519047fe4388001ff9822000bf98d21027fac708013fc650802fff21e620bff55020187fea899007ff104402ffe3266407ff54b21027fc8108017fc4344001feb12201dff14d3019ffea919003fe60cc467beaa46407ff94932007fcc19907ffc428c05b7eb286401fdc41210d7fe8598013fc500c06dffa866400bf58d210effaa69800efe6548069ff29c6417ff0c43212ffc8190867ff530c00ffeb264030ffd0932117faa398013fc408c01ffe32a4000ff4873006ff8c290002fd6284053fe2166204bf18430015fcc8880a7fc40cc465fe20c6401bf98532197f863190bbfd41cc84ffeaa26223ff95121027dc409001ffc64c8009ffb142013ff9472000dfec69883ffd65480037eb0e422dff54032027fcca1808bfe52cc003ff10a4214df55320007fe62100c3fc544c847f7212422fff98532027f82090027fd52840097f3046400ff4811013ff8c898802f5610c809fe3084015ff94f20007fac2990a3fc504c439feaa26004ff19210025fec708073fc644c033fea986004ff99230027fc609800e7c654c8097e320400fff5412014ffa8198812ff64840097f3066400ffd81310d7f8a998003fd3248409feb1c400dff8c520075fec890013fd658400bbfaa2202aff54b3109ff86390003fe634401ffea8a4002bf1933000decc210027fc5284003fe28c2004ffd0230077fe8490017fd424402ffe2986007fec8120147f8ca988bffe314c8097f3066200bf58a3000dfec49081ffe420800ffe2964204ff9411011ffcc890813fc3088009ff1804001ff0873108ffe8710017f54144047fe21a422bff1043210ffc6398013fc640c00fff292400cff94c20007fac090803fc324400ffeb046401ff14721007fe629801efe628c003ff88242009fd953118ef8ca9906bff54cc001fe98c4004bf196200bff8c9980affc100c809fea046009ffd4e10027fec8100bbfe64cc851fea9a6228ff14d3103ffacb90896fd64c8409feb086004ff1922002ffa868801ffc42cc85fff10a6402bf19120005fec498003fe6244065ff18c640eff1512014fbc879889bff53c8401fb98a6212ffd46200c7faa818087fe21cc0017f31c401fff90e30185fac719003fe324400fffb
  | 2 => 0x3100ff8629088bfe65cc065ff28c641bff9053003ffcc990812fc658402ffe1966204ff04110027fa6108002ff604840fff3246407ff8ca20025f8c91800e7c654c409feb18401aff90b30037faa08809ffe404c45df72166404bf18e10177fca999003fd310c001fe31a4004ff14320097fea510003f52144059feaa06434ff54e3201df8cb99003ed32c8401ffb1a4035ff88732025f8c710013dd6308055feb2e6201bd98630027faca1001eff63c8433ffa886001ff545100fff88718002fd6188001ff98a4004ff9013003df8c99001ffd520802bfea9e4001ffd053103ffac319047fd4188009ff8846004ffd4220005f8c688057fc53c8001ff9926417ff18b31027be6118093ff6548453ffa066236ff59732027fcc61002bfc510800d7fb2a2000ffd852003ffc849001ffc5208009fe32c6004ffc8220037fca488017ff4244031ffa08602fff945320bffe65980aaff65cc40ffe3046400bf587320bffec1988cffd548c801ffb02420bbf59020007fcc4980c37d544c82fff29e600fff94d200bff887990a7fd42cc40fffb0c6404ff9003003ffcc819087fe51cc0037f31e6204ff8c120125feca90802fd62cc4017eb1a2035ffc433218ffca699002bd64080017eb086405ff15110117facb9801ffe650c80ffe3206401fd885100cdfaca1800afc64cc4077f32a202eff50332067fea610003df32cc003fe20a4225ffd0f2100ffc8298823ff4384035beaa66016ff90430035faca88017fe64440017f31e421fdfd523016ffaa219077fd524c05ffe18a6414ff553200dff8a298007fc10484037e30e6400ff18d2100ffa4288007fd3184047ffa12421cbf59130027fec518003ff210c03ffea14601dff14930027f861080a7fd43cc4457eb2e6002bf9902000dfcc318002fd60cc403fb18a4201ff1453100ffc6288013ff65880077e32e621fff50e30027fca118006fc618c809ef3184024ff54121007fe6490017ff5444003ffa8c2001ff4c721007f865180bafd64cc803fea8a4217ff0c73003ffc841901ffe428c855ffa966229f750f3103ffccb19097ed42c84077e32a6407ff10a20157fea19889eff644c409fd1806001ffd473106ffca29000efc6548003ffa0c2000ff1893100df8c290013fc500803bffa9a600edf5512000ffea390803fe6348409fe9844004ff58830027fcc908013fc618c009fe0866007ff94921176fea99901efc65c8403ffa0e4200ff8ca3013ffcc89887ffd418c003fea0e6200ffcc72001dfccb08006fd618401f7eb2a402eff50b32027fe81100c7fc654c86dff2866407ffcc83206ff86290012fe6084009ff1004004ff10220025f8c508002fc63484055f3204001ff88510067faa6100dbfe65cc847fe2a24220ffd4a3001dfcca990a3fc524c409fe2826036ffd4b32025fec91001
  | 3 => 0xf3284004fb4802009ffc839000efe65cc42fffb166204bf98020015fcc9190bbfd64cc8017eb0c6407ff5963213ff884988d7fc41cc837fe30a6018ff1083000ffe6290813fa20080017fb026407ffd90320fffe851808fff6448409fe2866001ff8c73114ff8a998883fd518c01fffa9a4007ff54a3203ffe439002fff430805d7f3186403bf1953103ffaa41901ffe61c804fffa026200ff4c42003ffec119013ff400c00fff32e4231ff14d32027fc8190003fd3288063fea9a6424ff94d21027f880180d7fc10cc827fe28e40009f59420005fac199003ff3244009fe1804001bf98520107fca518003ff604c8097fb184007ffd8f20005fac3980dbfd51cc801ff90a6004ff98e2000ffc439889ffd404c40ffe2946407ff14832027fa801800afc644c02ffe29e6001ff94510067fea210013ff10880257eb2c4004ffcc220015fcc89885ffe430c00bbeaa22036ff54332027eac21001efc624c445fea9e6000bf18d20037fca68800efe650c82fffb2e640fffd952008ff88710007fb1044023ff2a44030ff5513203ffca599013fa4084003fe10a6211bf59220027fc40900a7ff54cc40fff2124216ff08430007f8c688007de31cc417ffa084007ff58f2111dfec890873ff434c0057f3206402bf99132025fecb08003fd61cc05bffa98641abfd933013ffc869887ffe548c00fffb264000ff48630177fe8599013ff40840097fb2c6001fdc43310bffec399023fc428400ffea964000ff4c530007fac688007fc3144009fe9806000bfd8d20025f8c210097fe43c844fef21a6202bf19110027e8208803ffd534805dfe2a6641aff5533007ff8a69001ffc52c803dff18c6007ff50a32037feca88013fc4084061ff3226401bfd85310bffe6398077ff514c009ff3146007ffd923200df8c39801bfe654402bffa9e4011dfd5220027ba6018013ef20080017fb0a400eff551200fffea918012ff640c00ffe2164204bf98030057fc8210007fc414400dfaa8a2017ffd9330025f8ca10097ff40c840fef9906401ffd4531027fec710007fc2184001ff9924204bf1813201dfccb19013fd628c039ffa0a6000ff4cb3116ff8a019013fe610c009fea042000ff4ca3016ffaa619047fd42880297eb264003bf9973003ffe421001efc640c803fe10e420dff98520027fe61180d7fe31cc84bfe2064201ff9452111efaa890897fd40c840fff9964004ff58420027fec318013fe5088051ff32a621eff88630187f88099003dd32cc409ff2004002bf993311a7f8a11901bfa50440097e30c4018ffd0c30047fc87080bbff54cc803ff8866204bfd90200bffca6190a77f54cc469fe29c6407ff909320bff8c3980a7fe54cc42ffe21e6207ff0ca200bff8a619003fc604c803f710e421dffd9530157fca198847fd438804fffa1a6200ff8cb
  | 4 => 0x9f7f544c401ff90e6005bf59110007be65988a3fe504c401ff1906025ff95321027fcc508017ff64440097fb246007bfd8f20147faca9885ffe53cc409ff3284004ff9403003ffc8599023fc4384059ffa186404fd9863000ff02088012ff62840077f32c4004ff19230047fca908013ff1084035ff3266004ff04220005fac41808efd644840f7fb206417ffd973100df8c219093fd534840dfe29a2004ff1412003ff88410013fd5088049ffa9a421eff94630007f86498802fd630802ffe1906004ffd0020097faa310012fc648404dffa864207bfd9320007ee6288097fc43c840dfca82202cfb508320fefaa9180cfff438c80ffeb2e401cff99130005fac31805ffc31cc801fd984600cbf59420047fa85080c6fd654c809feb242007ff14932117faa598002dd630804ffea1a6218ff50c3004dfacb08003fe324c409fea004018bf5903010ff8a398037fe4148003f610a4207ffd972103ffcc019047ff4288009fe2004007ffd8032027fa410809fdd434c433ffa906028ffd493103ff6411001ffe528800bfeaa2201bff98530025f8c81805ffc65cc85ffe28a6400ff4c720007f8c0908c7fd524c859ffa086431ff59532027fec9100d3ff518c829ffa1e4004ffd403003ffe4290047fc548806bff28e640bff90c20147fea098813fc30c8001ffb1a4217ff1833200ffa8298893fc5048439fe2126004ff90120027fca10801ffc63c8411bfaa42001ff04331127fcca9081eff648c867ffa0c6401bf9873212efea990807fc41cc42fff29e641fff1523003fdc6419053ed42c800ffeb246422ffd4f3003ff8659080efe658c031fea08601cff50130027fcc31808bfc52cc039ffa02602bff14432005fcc6100affe410c837fe10a600fbfd952003ffa8590813fd3008009fe2026000b798c200affea39000afc644c449fe29a4204bf98321007fa4310013fe640c0017eb064207ff8cb21037faca880c7ff534c8077f32a4200ff0ca10027fc6088007ff31440017fb026207ff58f2002ff8c888007f631cc4017eb0860009f59630007fac399003fd62cc421ff18c4027ff10131115fecb98053ff41c800fffb2e4004ff0821002ffc8488003fd624c01ffea924033ff90232005fec298012fc604840fffa964208ff50e10197fc83190abfd50cc40fffb064211ffd522000feca288002ff6348459ff2006400ff8ca10006feca98807f43144003fea8e6207bfd932111ffaa89085ffc61cc80ffe31e401cff90d3004ffea508043fe2188009fe32c401eff1063013ffac89881ffc610c84bfea1e4207ff9932000ffa8308003fe62cc40ffe3286401bf9862001cfccb18016ff6444009fe084600dff1452014ffe85988c7fc504c839ef21a6000ffd8931027fe41080abfe52cc409ffa842007ffd0832027fcc418013fd508c009b
  | 5 => 0xc13013ffea898812fe608c0017eb1c4007fdc85210e7fca89803bfd404800fff3086404ff9961001cfcca1006bde43cc035feb266034ffd4e32005fac11909bfe50c8437ff882600bdfd502000fbc629889bfd50c8441fea9c6029bfd933103ff8c9908dbfc50cc803fea8e4207bf19432027f8c310017fd6444053ff2166209ff94a1000ffe8290893fd6548411ffa142007ff5082003ff8429009afd65c840fffa164207ff1083200ffe2190813fc638804ffea126217ffd8b30007fcc09880afc644c865fe28c6404ff9402000ffe2098813ff658c011fe2a42033ffd023200ffc429888bff51cc05bffa886400fb8c921077fc8690013fc6308059ffa006401bf58731025f8c91001bfd5244001fe982402eff55332027f8c418013fc628c02dff1086014ffd0320005fac7900c3fc644c80ffe214641fff55230187fe8699003ff3288001ee992622cff100320bff8a799003fe324c06dfea9e6401ffc8521167fa8019013fd6188063ffa8a6423ff9012112ff8a990843fc3188009bf32c6010ff9462000ffa4308003fd320c00dfe2922004bf98032007fa649882ffd4308023beaa4401dff1953000fec439084bfe5388067eea1c6420ff94e30005eac21001ffe3208003fe28a201cdfd51300e7fa849806bff43cc067fe2046407ff10b20007fe6518013ff6484001ff31a4007ffd4820125faca9081ffc210c803ff18c2033bf5923219ffa8119097ff54c8409ff2826000fb4c832047f28108003fd60cc467ef21c6400ff4c730187fe8299003fc324c009ff9806017ff19331167bc8619003fc604c42fff2186408ffd5210027fe401009ffc434c40f7e31e4007ff08632027fea010007fe31c842ffe2186018ff95030007f26018013f7108400dffa9a2004ffc4030027fac5080a6fd64cc401ff98c601fbf59230027be6018013fc40c801fffa8a4004ff1943014ffcc99880afe64c800ffe10e402fff90532176faa99902ffd4108029fea064017ffd973003ff84210012ff6144009ffb1c2004ff1411003ff8cb19053fe43c800ffeb00641dbfd9530105facb18013fe40cc01dffa1a4000bf98e100d7fe839800afe6484001ff3024201ff8872100ffc4308002fd6384001fe98a401dffd493001dfcca1805ffc62cc03fff2146002bf99330087f88310007dc31cc453beaa66207ff1923203ffa6590873dd434c0017eb084023ff59121027f86090003fd32840017ab0c6017ff1833100ffa8390806ff6148409ffb284030ff90132077da8490073fd414c02fff9966207ff18720147feca98893fd5248431bfaa06017ff197310effea098003fd60cc803fe28a420effd052003fdc8590813fe2044039ffb226000ff4c32000ffca398813ff308400ffe2924201bf9872003ff8a490063fd420c03dfe18c6006ff54d1010ffc8398
  | 6 => 0x9fe21e400bffd50200effcca980d7fe41cc80ffe9084023ff50121077fa8690003fc624c00f7f3166035ff147320effca498073ff424c027ff8864001bf9843203ffc6490003ff6244055fe2966204bfd9420007fac59802bfe310800f7f3106002bf9933201dfcca10006fe614c003ff28c200fffd4920157fea798807fc51cc40ffea10641dbf59530027f8c8100977d54c8403ffa8a2008df5521003ffe659081fff63c8441fea946030ff5013203ffe40900b7fe500c803fb20a2012ff14e2000ffca39089bfe53c84097fb2c402eff9033207ffea090073fc544c047ff21a4212ff54e20027ecc210013fd500c0017fb126233dfd523200ff6210800afe648c009ff30c4007ff94a32027fac318017ff4344067ff21c64009fd95320c7f8a818007fc414c40ffe3006400ff5813200ffa628801ffe52c8409fe0806007ff19720027f8608801efc624401dfea0a4034ff94232007fa4298012fe60880617eb226401ff04131007ea62908baff64cc803fe18c2034bf5963203ff8849901ffe2108003fe18e4202bf99220027ec208807bfc518c0057e3266407ff8c8320d5fac9980037f654c855fe2866230ffd013208ffaa9100537f54c8001ff3166003bf1973003ffea41901ffd61c8051fea826230ff90d320a7fa8790002fd634800ffea16401affd033000ffaa298813fd6588061feb22641aff10b300cffaa2180b3dd430c839ffaa26007fd9843219ffa8719003ff318805bffa806407ff4c820027fca19006ffe214c06dfea966407ff0cb20027fcc210083ff538c0037f3164201ffd0510027fccb1801fff528c8037f3086007ffd963213ffe8498813ff650c00ffe32e4218ffd083005ffca8100a3fe524c40ffe2966407bf1963203ffac990867fe520c0057f3264204fe9421000ff8830800afe644c017fe2184004ff10330027fe60100dbff53cc859fea086401bf1872003ffec39001ffe63c84017f31a4002bf990301a7fea119083fc538c04fff2a26204ffc402013ff8a89886bfd40cc009beb2c6003bf1952103ff842990cffd418c801feb1a4000ff5893111fda8490813fc610c00fffa964004ff18a1000ffc828801ffe32c80017eb006423ffd0d210bff8cb98007f6214c403fe0864201bf185301affcc39901efc648c855fea9e6207ff10920027fc2088013fe3088001fe9926004ff042100bff8a79881ffc60c8443fe10e6000ff48430157fccb98813fc508c039fea1a6004ff592200affea19001eff65c80077e32a2004ff1012000ffa629083bff4048003ff90a201dff5953000ffaa308002ff6244009fea84201cff10d300bffc8798063ff540c00ffe1904016ff8c43003ffc851000efe654c409ff2022000f74c9300adfacb90013fd2008003ff18a6201ffd45210a7fa83900a7fd54cc403ff20a4200ffc
  | 7 => 0x80060348e8020181580380006406c000000040040000001a0801e805090000128c803015c000000020a8070010040300000002c0000080d0201081288600a0400001a0441dc000350220d4122bda6c0681500000a0140581c004060000510002702198a01e00c2380106a00c0780c04a0440d01f0220040186a0040000001a0000500900e0328d80d804000004038080340b00600401c0081e0380001140080001a0340080600000800007006054348040160040000800c028000000040080482803c0000000f016158048001ba014020050043240b84800a0182a81100c0000580702a03402192000e24018100040000380c0640000382b01e0000780002e0e4010000de0281680502a0282201a0040340003809801c0000218447400006004008f90300220ad99860038088158ee2b0094058501a6014040250480600102a004008138010120001ddbd0000b80009a00c0780002d02600c0001506a000061160c60180980d07e010310002dc00c0400101c010010000002dc000000e80540886b0260080180200a0049700a0021480604701a0d43d81300200c0502401605cc68020082181c8650000100804c1b00040b00d0a4028010040120140400000a004028000c003c0c003002108028270941882a8072b80100300006004c0181403e00c0002f00a0080100600601c0080a0000400000e0181e4050000961701700201e000010030000200806e0000b4290bc0340183100414600c0002602e10800061182040050100d208c0300002a01c0183502209803800178034050110000080284b0d20980000f0f425c0802e00002833813fd5008001ef9926201bd98432177da8599006fe61cc00fff31e4007f74c832007fac098833fd510802dff288602cdfd503213efaa89881efe6208011ff214202bffc403203ffc64990dbff51cc803ff98e420eff5912003ffca410013fd648c003fe10a2000bfd85320bffca618003fd3044059ff2a06417ff10c320e5fec8980a7fe40cc44fffb226212ffd4e2003ffe8410002ff6344037fe20a602effd07320a7fca990017fe434403dff20c6001fd085210e5fac71803b7f54480037e30a6407ff1092103fdc859009efd644c41dfea124004ff04130027fc6108013fe5048063ffa826433ff10e32027f8c70802ffc5408009fab0c6007ff90b21107f8a5180cffe548c859fea186407ff4cb2000ff86298813fd658c001f69924207ffd84320d7ba87980bffc614c843ff30e601dff54530027faca180c3fd414c861ffb226409ff94e10007fe6190003ff218c001f79946400ffd853200ff8429088bff50cc009ffb246023ffd01210b7f88218093fc654840ffe1924000bf58b30007fe650801ffe618c803fe18e6207ff99720027f8cb0806bfd41cc00dfe32a2004ff1422000fdc429088ffc404842
  | 8 => 0x681180000002c0000128c0000b00008a038000003840000500500e104048b60180680302f0580580780200004c1780005a01803855000014001410000081000201c000610150c001c0e0000000b83480001000c048d112e080070010004dc0300008407c000180040140700102607001863010028b001b24c0b00d0010180c4140740720600213f07e054188000100000700002c0ec0705c0200080008
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf764cb3000df6710c91000cfe7298f210bcfc7498d102876f544c92100cfe764c110024fe7098d2124f7954cc2300067f7558d21004ff7558b311adef7258d21004ff7458f21024fc7058c203067f31d95310067c41594200067d54d89310267e70594200067d654c420007cd32c8530004fd70d8931005fb704ca20056f65158420025fa708ca30006bf7458d10026be1059020025f8704ca3029fce438c9210067f5458e10006f55358630006f45458420026f61058630006dd43d853003cfd7118d21014fc745863003edc3298f210067d7159420004ff7558420004ff7058b3103edf5298c20086f641586200267f305942003edf3258032006de7158c20006f675584200075f754cb310067f65181320befa634c0300bfcc624cb31024fc7058e20006bd644c4201f5f575cc5100067e71d9532004ff75d8520004fd7458a100bedf61cc931006f45258630006ee4258a10014fe745803201cfe75d85300057f7558d20006f6545843200cff76486200067f70d9532006f770584320bcfc76cc520014fe7458a30006de634ca10006f54158430004ff7558720006ef7258d20006f5614873003edc5258c2003ebc5259020024fc7058432004ff75d8530026f67058420004fd7458f21006f443586300bcff7418d21014fc745833103eee42587200bef4315873003cfc72584300bfda534c030004ff74d8131005f7714c9103275c754cb31006f5614c6300f6f441586303067f73d9531006f960181213667f73d9532006ee4218d210067d654c630006de5458c20006ef764c83203df6724c52103ef52158321006ed42d852003cfc768c910026de5098c2003eec62c811003ef452584320bede4318d20005f5710ca100067d71d9532006f774584321bff24048510027f161cc23000cee7298f210bcfc76cc91000cfe7158232004fe76cc9100047f74d9532004ff7558632014fc74d85320067c315942001cfc75d891001cfe7558420007f070485100b4ff764c73003cfc72587300067d5458732026f6205863001cfc7558620006bc73590200067f5458b310067d43594200def62158d1000df671cc11015cfe76cc931014fe74d8132006bc315902017fe7104c921006bc7458d10004fd7118d20006f7435842003ef5325842027775544c521026bf50590201457e759813103df4724c5212efce42cc93101cfc75584320067c7558910006ee4258a300bfcc324c8300b6dd3118d1003ede3258f21026de1058c2003ef47258420006dd5358c20026ee2058830007e7724c5210067f71d9532004ff75d8532027db63cc130004ff7558f210bef443584320bede63cca200067f7558d1000ef6614c42003edc624cb300067f5418d20006f4764c521005fb704c910006f741d853203ef6325842015ef441584320f6f47358630026ef7258a30
  | 1 => 0xc91003fcc324c921006fb60981310657c754c4201adde730c93100ddc764c931005ef724c62003fcc634cb21005df735852003eec62481100bedc5318d200357c755891003ef4425842003eee4258432024fc764863003ef65258432004ff7558c200bcfe73d89101c7f15048510006dd7598c2003ef42158720004ff75586200067d5498c20014fc7458910004ff764c52000df471cc9102b5ef744cb213067e41d9531004fd7458732004ef764c832086f6215862000ef661cc530004fd74d893032fce42ccb3101cfe7558b3003cfe76d89310bcff7498d210bedf3118d100057f754c6300bdde73c873003cff7258c2003ede4298c20025f8704c530004fd764c72001cfe7558331024fc764ca1003ef7715863217cfd764c9211bf7754485103077621d9531005fb704ca1001cfe7558332006f57258630006dc5198c200bef73158432006f654586300beee638c921004ff7258d10006f4745843203ede5258c200067f6558532006f775584200267e1059420005f7714c92100ef661cc4200067f65cc93203cec7258d100267f7059420014fc74d852000df671cc921004fd7458b30004ff7458332005fb70486202af6d544cb210065f5458c20006ed4258032006df6398d20014fe7458c2000df671c8110006f9405803200cfe7158b300067f54d8d10004ff71588300047f7558d213667c20d9532014fe74584201afd621cc931024fe70d89100067f545891000cfc71d8d20005f7714c11003cfe72d853001cfe7558d10006df32d81310bef46158732014fe74587300067e31d9532006dd63cc420006bd53590200057d74d9532006dd6318d2003eef64cca32024fe70d852001cfc75587300067c10d9532004fd76c863000ff360cc510004fd7558321004fd760ca10004ff764873003eee621893100ef661486200067d5458830026dc3058e1003ef7215872018d7e76d9532004fd74d852000cfe7118d100beed76cca320067c43594200067d54d89300bcfc7498d2100cfc764811011dbc74581213667c42d9532014fe7458732024fd71d8d103067f41d9531004ff74d893101c7c7558d10004bf7458910006dd4358e2000ef661487300057f75585200067d545833203eec628cb31006dc634c9210067d65cc63003def764cb210bcfc7358620014fe7458f20026dd7098c2003ef820580320bfcf624cb31014fc7458d2115ef6610ca300dcfd7098d1003eee6248730006de4358e10004fd7558e1003edf4298c20005f9708c9300267e2059420196f63158632026df2098c20004fd764c91001cfe7558e101567e65cc420014fe7458b3003dec724c42013ebe644c420004fd7498f200bcff7598e200067d72596300bedf7198c200067f65d8131025de70cc930006ed62189313675e32d953203ef55258420006bf7159020005d
  | 2 => 0xcff7658730006f753586300267f7059630014fe74d8931007cd324873001c7e76d95310bef73158730024fc7058732005f57198332026be3059020006ef764cb2109efa10d8121014fc7458e20004fd75587320bcfe7398d10014fe74d8d21027f261cc23003ef72158432004fd7458420006df7358d21004ff7558232005ef72585301aedd3198f21024fe7058a100067e215963000fe77248510024f47648510026f540584203067d31d95310067f5458d201dff240cc510026f7305863029f6f548c9211b57e75983320067d5498e2003edd3258432004fd72d81310067f40d953103eee62c87300067d40d953200df6710c931026df4058c203067d10d9531006dc5358e1014ebe64cc42000ef763cc531004fd7198e2015ef6415843203eee3298f210067c6518132024fc764c93018e7c73d953201cfe75d89310067f5458830006ef6248110014fc7458730006df5498c2000cfc7158032004fd745843203edf2158c20004ff76486303067c21d95310beef6298b300067f5498d21006df63cc921006df630c9100067d65cc420005f673485100067c7159630006f55458420056f63158420024ff71d8d10024fe760ca10025fa70cc92001cfc7558630006ec52d89300267f40596300bede4398d100bedc3118d20004ff7158a303067e21d9531006ee52588300067f545873203ef771587200067d7359630006ed6218930026dd2098c200067f54d85300beee634c9210bede63cca1017ef441d85320bcfc7598c200067d545863203efb7058232006de4158c20004fd7458e1003edc62ccb300bcfc7518d210067d54d8520006dd7198c200067c659893103cfc7258d10006f652586300067f5458b30024fa76cc1300beee634cb210067d41d953203ef732584200067f5498d10026f4205842003cff760ca10026de3058c20006df5358e10006f67558630004fd7498d20005f7714c931014fe745863200ef6614863003fcc324ca2023f5f54cc93003ebe5259020004ff764c4200bcfc7498c200067c651893117ef4615853201cfc755833110cfd7198d1003edc3258f20026df1098c2000cff765873203eec634cb21006f6745842003edc3298f20006fa5058032026f750586300067e4159630004ff764ca1000ddc71cc931004fd74d893100cfc7158d20005df734863033fcd434c832026f410584200def46158530014fc74d85300067c6558931026f4505842010cff764c430006df5318d203067f21d9531006ed4298d20006775458630006f676cc5101b67c65cc931004fd7558a100bcfc7358720006ed6248430024fc768ca10004fe7618d200067d74596300bef57198d21014fe7498e200bedc63cc12003cfd70d8520024fe7298f20004fd74d8d20006bd64cc420005f970cc920255df744cb3017eef2158b31006dd63c
  | 3 => 0xd4258a30006df634c9200bfcd62ccb31006bf735902003ede7258c2000cfc7198f201df7754cc510006df6398d1017ef71058b31004fd71d8d20007e76248510004fd7418d2001c7e76d953203ede624c93103eee7298f2124f7b54cc23000dee714c921004ef7258d10006de5158c2001cfc75d81310267f40594200f6f4215863003edc624c9310067f6518131006ed6218910004ff7058d2109dfb705891001cfe7558b31006df735891001cfe7558d2103ee632584320067f654c93127777544c52100cfe76cc921026de7398c2000ef661cc62003e7f2159420004fd74d81210067f65d81320f6f621586300067c21596300bede63cc320006ef72589103667f20d9532026f650584201df7554cc510006ef62c811003efb2058032004ff755873003ebf215902001cfc7558910007d763cc510006f4725863000cfe76cc110025f4704851000cfc7158830007cf624c931026de4098c200057f754c93000df471cc9310067f42d9532007e63248510024fd7058e10006f574584200067d658ca30004fb764c0300bcff76cca100beec6258b300267e305942018d7e7598132277d6434c521004ff74d8d210bfcd62ccb30006f77558432004ff74d8930014fc74588300067e74d9532024ff7058a1000cfc76c81103075c31d953103cff71d8d21014fc7458e1000dec714c9210067d54d81310067d54580320067e4159420006ed62c84300bcff76cc420026bf70590200075f65cc931005f572cc510004ff7558321006de4358232006df63cc1103067c71d9531006f561c86301b67c65cc93200cfe71580320067f658c9310067c6558532026f7715862003ef42158432006dd6318d210067f5458232006f54158420004ff75d81310067d545842001cfe75d8d210067f659813203edc2158c20006f5735863003edf63cc93200ef6614c7200bedf7598c201067e7359630004fd76c8430024fe70d8532024fe7058c200267e3059630006dd4358e1001cfc7558b300bcff7418d100067e745963001cfe7518d20006f7614c530006ed62c8730006dd63cc3200067f75589103067c73d95310f6f641586302c77554cc531014fc7458a3003eee6218930006f740584323075e31d9531086f6515862020f5d544cb3003eee4258321004ff75588301257c75581210047f7558f20004fd74d8910005fb704c530025f87048620347cd534c832004fd76cca10006dd325833100cfe7158a300067c659813118d7c7558132005ec725853000ef760485100067f65d853217cff7158d2103eec6298b3000ef6614c6300bef730584320bfce434c8320bedc7198c20007cd320c931004ff7258630006dd4318d200bfce62ccb30267cd42ccb300ed7c755853000df6710ca10006dd6318d1003ede2158c20004dc735891003edf7358f210067d65c8630
  | 4 => 0x8f21025f470cc5100067f40d953203def734c8320bef83058332004fd7298d1001cfe75588300067f5498c20014fe745863001cfe7558432006dc5458c2026ddd74ccb3001cfe75d8910025dc70ccb3003eee628ca300beed7298d20004fd75d85200067e7459420056f4515842003ef63258432026f74058630004ff7158d2009ef6315872034ded744c8320067c65d85320067f54d8930006dc7458c200047d745963010ef62158730024ff7058420356ef64cc9320bef6435843203e7d21594200bcff7518d213667e42d9532004fd7198c20026dc4098c200067c70d953201cfe7558f20004fd768c8300067f10d9532005dd73c8530004ff7258730004fd75d8d10007cf724c930026f410586200f6f65158630006f6325863003eec628c930006dd4398d10014fe74582320067c64d9531006be535902001cfc7558332004fd7598c20006f743584320bef63118d212af6f544cb2101cfe755872006ef710d8520026f77158430006de76cc931196f71058632026df30588300bcff7598e10014bc7458d10004ff7458d21006df4358c2003ebe32590200bedf3198f210bedf7498c20004fd7458c2003edd7258c200067f545843000fe7624c52100cfc7118d2003ebe21590201aeef21d8931004ff7258e10014fe7498e10004ff75586300f6dd31d8d100067f43d9531004fd72d8530006ed4258a1003ebc2159020026f47058630006be515902003ef62158321006d543584320047f7558d100bef4535843200cfc764c93103ef75258420006dc638c9100057d74d953109cff705891001cfe75d893000cfc76cc921006f65358630004fd7518d200bef6634c52103cfc76c853003e7e215942003ef64258420026f53058420004fe760c9100bfdb32cc130007d7714c9311e7f150cc5100bef65358432006fb40d8132006dd634c72003ef74258420006e5325843200cfc71d8132024fe768c93001cfc755873203e7c21594200067f5458332004fd745823200cec764c921026f7205842003efb7058321014fe74d8532014fe7458e20027da73cc230007e53248510026de3058e200067c7459630006ed42587201dfd643cc5100bef57118d21006f67358420014fc7458f21006dc7158c20004ff7058d200bcfe73d8121006de5358c20005fb704ca3001cfe75d852001cfc755823203ede3258c20005bf74585200067f7558d2017fcd314c9210ed7c754c53017ef661d853215ef651584320067d654ca300067f4359630004fd7498d21006dd32587302d75d544c931006bf75590200047d74d953203ef7725843200dec718c9212a5ed748c921004fc764c910006ed4218d210ad7c754c720006df634c9212efcd42cc9310dedd3158e100dcff7158d100bcff7498e2000cfe71d81320067d5498d20004fd7098d21007e46248510006e
  | 5 => 0x4fd7498f213067e31d9531006ed42584320057f75585300067f5498f20006ef628c9310067f7259630006ec21d89300057f754c4200067d5458a300057f7558121006dd63cc720006f55258630007e5324c521014fe7498d200bede63cc720006f474584200067f5498e20004ff745862000cfc715823201cfc7558f20004fd7458630005dc7358520335dd74ccb310bfce62ccb3103ebd5259020004ff75d89300bcff7598c20004fd7418d1001c7c7558d2020f5f544cb30026f86098331004fe76cc9303067c10d9531004fd7018d21006f53258630024ff71584200067f64d9532006dd7458c20006de4358632026dc5058c20006df4198c20277d5434c5210067d72d9531024fe7098e10026f520584200bef860583320bcfe7398d2032fcd42ccb310067c65d8132006f541586200076f754c832014fc74d8d203067f71d95310bcfc7498d20004ff7648430006f7545842001cfe7598d100075f754c930026dc7058c20006fa405803203cfe72d8d1007d7c754c5200067c7558d21014fe745843200ef760cc510007cd320ca30006ee42d81210057d7598931006ee21d89300dedf3158e10005df73589103576d54cc93217ef621d8532005f572cc531004fd7098f210067d5498e1000dec764c921024ff7358c200f6f431d8d10004fd7598e100067f435942003e7d3259420014fc7458d20006f76348510004ff7558e20004fd7518d21006de634c7200bede4398c2021ddf74cc9300067f54d85200067d5458f21026f77058420007e6324c5210067f54586320ed7c754c93015dee768c92103eec624c9300067f5458f20004ff7458e1000cfc7158f203175d544cb31004ff7158b30006f5614c72018e7d73d953203dee73cc932024fe7098e20026fa6018131024fc705862000cfe71588300bede7318d2003eec620c9100063d75590200f5f6710ca30004fd7458d21004ff74d8d1000cfe7198e20027f010c8110026dc3098c2003edd4298c200bfd4314c730006dd43582320057f7558930024fc764c62003edd5258c200067d5458d100befb6098332026dd3058a3001cfc75d8d21026dd5098c2003ef53258432006ef620c910006f45458432006f56148620004fd7458332024fd7058a1001cfc75d8d1000cfc7198c20004fd7558f200067d54d8d21004fd72d8d10004bf7458d100057d7518121004fd7458d2022ddd744c930006f74358630006ef6298930006f475584320057f755891001cfc7558f21024fe7018d210067c6598132004fd7558b31006fb764c03001cfe7558d200bfd571ccb3101cfc75d85200057d7598332014fc745842003ede7298c20005ed71cc9320057d759833103e7e325942003cff7118d21004fd75d89100057f754c92031ddf744cb310067e64d95312675d54ccb300beef3258b31024fe709
  | 6 => 0xe718c921004fd7418d2100cfc7198e200067d4159630004fd7458331014fc7458f2003fcf734c8320067d65cca3003ef4725843215ef41058432026f64058420026bc1059020006ef624c93017fcf314c921004ff7458b30006de4358032004fd7558630006df7558c202d75f544c9310f6f63158630004fd745832101cfc75d8532004ff745832100cfe7158e2016e7e650ca30006f44258630026f4705842007d7c754c920006f56148430006be3159020024fe76c86300bef43158430006f771589100bedc63cc921026fa60181320bede7318d21006dd5458c20004fd7558c20006df5198c20006df3258331006f4545863003ede62cc9310267d40596300067f545803206eed2158a100bedc5398c20024fe76c84300267c705963017ded738c92103edc62cc9310067c4259630006df5398c20026f45058630004fd76cc5200076f754c92103ef42058432007cd32c8730006dd5198c2001cfe75d8d10006ef628c930006de31d8d2001cfe7518d21006df764cb300067c72d9531014fc7458a10006f47458630005df735812103eee4298f21086ed21d89100bef43158732004fd74d81320067f54d813101cfe7598f20004ff75d8d2003edf7258c200065d5498c20014fe7458321005f571cc9210067d40d9531006de7458c20026ee2058a30026dc2058c20004ff745863001cfe75d8d20024fd73d853003cfc764c7202ef5d54cc93106ef661d852000cfe71d8d200befb30583320067d5458a1003edc764c93103e7d7259420006ef624c931026de3058e1003cff76c8630004fd7558e2003cfe76cc72000cfe76481100bcff76cc7200067f5458420006df6398d2101cfe7598d2118d7c7558532026bc50590201dfd543cc51003ef44258432006bd7359020004fd7458e201cdf57448510006be71590200067d5458720026dc1058c200067f659893103def734c9210267c20596302c77754cc5310067d5418d210f6df31d8d10006dd634ca20024fe7398c20004fe7648530006ee4298d21024fc7058420004ff7558d20026dd1098c20026dc3098e20006f77158d10004fd755843003cfc735873200fd673cc510006df63cc92001cfe75d81310e5bc7458530026f771584200067d54586200befb609833100ef661c86300067f65189310067d54d891006ef46158520006de3158c200067e40d9532006f47058432006ed525883003ebd32590200067f65cc931006bf74589100067c64d9532006f551584300075f654c93101c7c7558d210067e31596300bcfc7498e10006d6435843201cfc7558e10026dc7098c20026f86098332014fc74d8d10004fd755833200ddd76ccb31006f450584320067f6558931006dd32d8530004fd75586200bfd643cc5310267c10596300067c42d9531004fe76c8530014fc7458b3003edc3298c20
  | 7 => 0x8110026f6105843003eee4298f200057f754c720004fd7598d100bcff7498d10026f44058420004ff7558331006f763cc5100067f7558f2003cfe7218d10025fb734c030005ef7258d10007f270cc51003ede3298f2103ef62158f21005bf745853018e7d72d9532014fc74d8930006dd43586320357c7558d1000cfc7258f2129fcd438c9210067f70d9531026be7059020024fc7018d100067d74d9531026de5058c2028ded744c9210057f74d953121dde730c93003cf4764c52117cfd7298d21004fd73d81210beef32588300067f5458d10024f676cc5100bcff7598f211267e6548630004ff764c72001cfc7558b310067e43d953217fcd314cb21006f67058432026f540586300067d54584320bef461587300067e64d9532006dc634c92003eee624ca30005f5710ca30006f5545863003e7f3259420026f55058630024fc764852003ede62cc93022ddd738c930026bd7059020004ff74d812117ef6614ca30004fd7598e20007d932cc130026df7098c20004ff71582320277a65cc230014fe74d813100dee714cb2101cfc7558430004fd7458430006dd4158c20025fa70cca2000cfc7198d2000ddc71ccb31026de2098c2001cfe7558a30026df5098c2017fd7104cb3101cfe7518d100267c205942003cfe7298c200bcff7498f2103ede7398f20024ff7118d100067d42d953200cfe76c811003ef82058321026f71098e1001cfe7598d20006dd4398c2003e7c4259420007cf634c92135f6c65cc93203ebf3259020026f42058630006de7598c202375c754c9302177954cc130004fd7558d100267c1059420025de70ccb30006df7358d1000cfe7198f200067c73594200bede4398e20004ff7458a10247d953cc2300bfce534c832006f95058032004fd75587200f4fe7618d1001cfe7598e20006ee4218d200ed7c755893003edd2198c20004fd760c910026bc205902000cfe7158d200bfd671ccb3117fe4714c921026de7398e20026f4105863000dec714cb210067e3159420006f54058432026ec20588300bedc3198c20014fe7498d10006f73258630014fe74d8d20004fd7558032006f475586300067c40d9532196f6618ca3003ef67258432004fd7458d10026dd4058c2000df673cc5101457e75989313476c754c832004fd74d8d100057d759813203cff7658b31025f8704c930014fe7458d100beef3258b30024fc725872003edc4258c200bef8305803203fe4718c92120779544c030004ff7458b3103ef73258432004fd74d8d21025fa708c9300bcff7498c2000cff764c63003ef5525843203edf7358f200067f5498d2001cfe7558730024dc764c93001cfc7558632004fd76c8730004ff7558910006ed4258321026ee2058a100067e70d9531006de43d81310067f65981313067d41d953106cfd764811000de
  | 8 => 0x6dd43d8131004fd764c620004ff7358720006f7525863016e7c650c931006f74158420026f6305863023fce42cc93000df673cc5310bfd771cc931026be50590203667c32d9532006dc634c11003ef64258432004ff7458c200067e72596300067d54d8d2017df6719813200cfe768c9310267d3059630026dc3098e10004ff74d853203ef74258432006f65058432006ef6298931005f5710c9300057f754c8300bcff7598d21005bf7458121024fd7118d1001cfc755832103fe7614c9210067d5458630004fd745872003ebf525902003cfc73583321257e75181210057f754c9103067e71d953101cfe7598e10026af2059020024fc7648430024fd7058420004fd74d8532005ed71cca321edf574cc5100067c74d953203cfe76cc12003ede4258c20025f670cc510026f55058420004fe76cc520024fc764c92017ef631d85320067d5458d213175f544cb31006df638c91003cfc7218d20026fa6018121014fe7418d210bede4398e10026f4305842003edf4258c20006fb6098121005f5718c91003dee72cc3201467e654c630006de43d8d21026f71058a1015ef71018d21024fc7098c20026f650586303576f54cc932026dd7058c20006dd63cca20005f771481101067f7359630006f64358420026de1098c200067e7159420006de5498c20005f9708ca300067f6558132026df2058c20006dd634ca10004fd764c1200beed7298d21004ff7558a10024fc7258f2003ef75258432025f8704c920006dd5398c20006df634c120004ff74d8d2003ede3258f20006ef7258d21006bd715902003ee64258432004fd75d8121025f070485102976c754c9210bcfc7598e100067d4159420004fd75584320cd7c754c4300067f5498e10006dd4398e20026de7398e10004fd71d89300067f715942009ef71058720004ff70587320067f42596300067c74d95310267f20596300067f54d8d2110ef621d8131005ef724c4200067e4259630007e4724c52103fe7618c921006be75590200bcfc7358a10007cc634c921026de7058c201bfe642485100067f41d9532005ec7258d100067f54d8931014bc7458910006df32d853003edc5298c2003ef542584202f5dd74cc93103def764c83201cfe755862003fcf734c92103edf5258c202dddf744c9310077765cc5312c7d543cc5310067d5458331026f7715863001cfe75580320267d40594201acfd7198d210067f65581313776f54cca320bfd471cc9310bcfc7648730006ee4258910005bf74589100bedc4398c200bcff764c11003cfc7258c200067f5498f210067e72d95312675f54ccb30005f970cca20006dc4198c20006de4358d10006de634c420004fd7298d200057f754c53010dfb7058d10026de7098c200067e42d9531006dc7358910004ff705843200fd673cc53100df4714
  | 9 => 0xd745873000df4714c110004fd7098d2003cff764ca3003ecc624c930004fd7198f20004ff7558d21005ef7258131006f75158420006fb60981320057f754c921004ff7358910026dd2058c2003eef618c921006f55158420014fe74584301aef661cca30005bd749893115ef7105843203ef77158432006f75358420004fd74d8530006df5458c200057f755893101cfc7558c202b5ed744cb21014fe7458a100267d30594200067c65d893100dde714c93100675545842003cfc72583313067d73d953101cfc7558a30004fc76485300def631d8530005de731891000cfd72584201afd710ccb31007d7634c521004fe764c520014fc7458b310067c31d95320067c70d95310bcff76cc9100067c7459420004fd7498e1000cfc7118d10006f77158d210f6f4515863001cfc7558d10004fe764c91003e7e42594200267d205963017fcf314cb21026df1058c200065f5498c200075e43d95310bede63cc420004fd764c42003e7f425942003eec6298b310067f5458a100bddc73484300067d5418d10005dc7358910006bc51590200267f205942003fce634c8320cd7c754c830026fb63cc130025de704c93027f74754c52103edc3258f210f6f621d8d10024fc70586320bcfc7358420006f7614852003ede624cb3018e7e73d953200cdc764c931006ed42d8121006de3118d20025f476485100067d5458c2001cfe7598c2000df4714c910004ff7158c2001cfc75d8d20004fc764c52013dbe749893103def748c9210bcfc7498f2015ef45158432024ff7058e1001cfe75589100bcfc7418d20026f72058630004ff75d89312ef5f54cc93101cfe755863200ddc714c931006ee4258830004fd7218d100def661d85300befb30580320267f10596300bede4318d21006f7425863000cfc7358b31006f6425863032f5d54ccb3103ebe7259020004fd7558a3003dec724c62003e7f72594200ddf671189300067f54d89101acff7258d21014fc745872003edc62ccb310067f5458720026f5305863000dde71ccb310bef7315843003eee6248430014fe74d8d1001cfe75d8121006df325873003fe4214c9210bfcc324cb3103ef4325842003edc624cb3100cfc71d89300047f74d9531025fb764c030004fd7598d21006f5415863003ebf725902003fce73cca3203dec724c32003ede624cb31026bd3059020026bf20590200067e74d9531004ff75d8d213067f10d9531005ed72cc320025dc704c93003efb20583210057f7558d21004ff7458331007d8704c93003cfe7298e100067f5418d21005df7348430006de7498c20014fc74d89100067f5458a300067d545873003ede3298f20006dd435803200ef461485202077b544c03000ef661cc6300067f545862007d7c7558d20006f772586300beec6258b310bef73158732006dc5158c20
  | 10 => 0x8c200bcff7598d10006de7198c20004ff75d81210047d74d95310067d70d95320057f7558132006f5435842001c7c7558910004ff7458a30006f67458432255dd744cb30004ff74d85200957c754c620004ff755833203edf2198c20004ff75d8d10004fd7518d10005f7704c5210bedc5318d210bfda53cc23003cfe7298d10004ff74584321aef621587320b6f621584300bef976cc2300067f5458432026f75058420004fd7498d10006f554584320bcfe73d8520004fd768c9100267e405963032f5f54ccb31024fe7058e10024fc7058e10004ff755843003edf3258432014fe7458910006ef52d89300267f1059420006dd4398e10194ff764cb310bcfc7598d203667e72d9532006dd63cca10005dd73c87300bfcf724cb30006dd43d8d2101cfc75d8931004fd75d8532006ed4218d200bcfc7598d210057f754c93100cfd73584300bfd970ccb3003dde73cc9320357c754c910004fd75d8d21006f54158432004ff7458910026f52058630014fc7458632006df5318d2110ef431d813100677545843201cfc75d81320067c43d953203dec724c120007c5324c52106eef2158a1003fe5614c832005dc73581210067c41d9532007d4634c5210067e40d9531027da634c03000cfe76d8520056f431584200bcff7518d20004ff745883003ef72058432026bd2059020006ee42d8931006ed4298f21004ff75d89100bfda43cc1303675c32d9532004ff74d813215ef7735843200cfc764c11003ef47648510004fd7458910004fd75584200bcff764c921014fc7458032006f553584320067d5458321004fd74588300067d70d953103ed5325843200cfe7198d20024fc7058a10026df7358c2000df4714c921026bf1059020005ec7258131026f77058630005fb704c9300bef67358432005f5718c931006ed4298d210076f754cb21004fd7458032195df764cb31006f57358420026ad205902003eef614c92101cfe7558c200067e70d953201c7c7558f2001cfe75d853203e7c7259420004ff7558e1003ede5298c20026df7358e20006f47358420086ef21d89100bcfe76c8730006f45358420006f67558432006dd4358d101567e65cc6300067f7359420006df5398e102177b54cc13003dee72cc120006f775586300067d43d95320f4fe76cc530006dc53d8d21026f7305842003ef520584320beef6298b3110efa10d8131014fe7418d1001cfe75583210057f754cb301457c7558131277e6424c521006f75458432004fd7458f200057f754ca2003edc624c930004ff7258d201adf671983320bedc5398e100057f754c5200bef97098d20004fd7598f201157c754c730006de634c910026df63cc13000cfe7118d20006df53d8d210bedc63cc920006de76cc930024fc70d891003eee768c921004ff76485300067c7259630004f
  | 11 => 0x6ed4258910024fc76cca100067c61d9532014fe7458e101ffd9534c0300def43158d100067f5458d21006dc634c1200067e7359420004fd755891003edd76ccb31004fd7498e2000cfc7298f2103fcf734cb210067d42d9531007cc624c931004fd76c8530004ff73584200067f54586302cf7465cc53136fcd53cca32006ed4298f20005bf7458d100b6f65158430006f553584200067f74596300bef97098d100067c40d953101cfc7558a1000cfc7158a30004ff764c620197e6318c9210957c754ca20026f640586300beec3258b31006f67458630004fe768c91003ede62ccb300067c7159420006f960181310bef83058331006dd7558c20005de73c85301edf774cc510004fd7648630014fe7458620006f65458420376ed64cca32004fd7558b30004ff72583310067c6518131004ff7058f2103edc2198c2003ed73258432004fd7598d200067f74594201367e65c8630007cf724c9310beec634c921026f61058420004fd768ca10004ff7058632004ff7558f20007d532cc510026df7358e10014fe7498c20006ed624ca300067d71596300067f5458f21014fe7418d200067f64d953103ef4525842003edd3258232004fd70d8532024fc7358b30005f5719813200cfe7158c200bcfc7518d2003fcf63cc9320bef860583310ddf6710c930024fc70d85201257c754c921005fb704c9200075f754cb30004ff73586200067d54d8532026de3098e20006de43583310067d54d81320067d54d812100dde714cb31196dd31d8d2103ede62ccb3120ede634c83017fd4314c9310067f42d953117ef63158b31014fc74586200bcfc7498e200067d64d953110edd3198e10026f51098e10004fd71d81320067c6558132006f443584203776d54cca32004ff71580320bcff7598f2003eee6218910006f57458630004fd73d8520014fe7458b310bfda70ccb30006f6405843210ef7105873000cfc7158b300beec638c921004ff74d8910014fe74d8930056f4415842002dbc7458d10024fe70d8d21006f5614c4200bddf74ccb3003ede2198c200057f754ca100067f545833103edc7298c200067d5458e20007cc624c9301157c754cb3001cfc7558032024fc705863003cfd71d8d21075bc745852000df77248510014fe74d8530026de3098c20006ed628ca30025f8704c630006ee4258332024fc7058430024fc7058d21006de4358432006ef629891003cff76c8730006ee42d8930006f5755842006cff71589100057f7558d10014fc74d8d21026de4058c20005ef724c32001cfe7558e200bef63198d21006f75458630024fe7098c20026f62058420004fd7458b310267d2059420004fd70d8d210067d54d853030d7e76d9531026df3058a300b6f64158430026df4098c2000ddc714cb310beed7218d21004fd75d8d20006de419
  | 12 => 0xe62c843003eee32584320bef43058432004fd7598f2103ede7398f21006f57558630006ee42587320075f754c931004ff764c91000df6718c910004ff7558d10014fe7458830006ec7258d10025f670485100ddf97098d100067f650c93128def744c921004fd75583310067e43d9531006f561cc4200067f415963003cfe72d81310067d7359420026f44058630026f51058a10006f55058432007cd32485301c7f2504851023fcd42cc93004d7c754ca100067f5418d10006f571d8d10006de4358c20025dc704cb30006df4398c20006dd7498c200067d5458b31026dc3058c20006df764cb3100fd7734c52103ef662485100047f7459420217d943cc1301a67e658ca30006f7735842001cfe75d81320bcff764c1200067c65d81312275d544c930006fb7058d10026dd5058c2003ef54258432024fe76cc4200267c4059630006ef7258d1000cfc76cc11003ef820582321457c754c931004fd7458a300067d5418d20014fc7458332004ff74587301d5f57548510004fd76cc7202f5df74cc93103ef52158f210bcfc7598f2000cfc72583210267d70596300067d74d953200cfe76d853001cfe75586300067f715963033f6d544c8322dddd744c9310267e405942000cfe764c921014fe74d85200067c7558d1017ddd738c931006de43d8d20004fd755823201cfe7558f2103fe7718c9210067e4359630006f57058432026ef7258a10004ff7458420004fd75d81320067c71d953203edd4258c203067d71d95310267c30596300067d5498f21006de43587303667c72d9532004fd75d81310067e61d95320057f754c4301bfe54248510005fb704c63001cfc7558e2000ef4614c5300067f5458c20004fd74d813118e7e76d9532006e54258432005f571c8110006f57458432006ee42d852010cff7058d10006f5515862000cfc73d85300bcff7518d10026dc4058c2000cfe7258f21014fe7458d2103edc62cc9300bcff7598d2000cfe76d853217cfd768cb31014fc74d8121004fd76cc620006f960181320067f5458730005fb704852003cfc764c120005dd73189100bede63cc91017fe6314c921025f8704c9100057f754cb3100cfc71583322bf6c754cb210067c7558d2001cfc75d85300067f74d95310bcff76cc62015edd3118d21006f77458630014fc745843217ef710d8532005f47348510007db704c9301d5f77548510004fd75d853017edd3158f210067d42596300bede5398c2000cdd76ccb310067f54d8d2000cfc7158e200067d5498d21006de5198c200bcfc7418d21006dd4318d211bff14048510004fd75586320067f54583210067f74d9532004ff7558a3022ddf744c930004ff745872034def744c8320075d43d953101cfe7558732006f56348510006f67258630005de76cc93000cfe7158f20005ed72cc120
  | 13 => 0xca103667c21d9532004fd7198d2001cfc75d81210bddf74ccb310bef4634c5210bcfc7358910006df7458c2000cfe71d89101557c754cb310067d5458910006dd5158c2003edf325823200cfc71d8910006ee4298d200bcff7418d200267d7059420026de3098e10004ff7158f20004fd7558d201067c73596300057f754c73003ebc7259020006df5358c20004fd764ca100067f54d813203cfc7298c200067f72d9531004fd76484300067d5458f2007d7c7558520024fe768ca10014fe74583320067d5498f20026f630584200067e4359420024fe76cc6200bedf3118d21006dc53d8d2001cfe7598f21006f542586300bedc630c910024fe70d89310bedf60cc9300067f65d893100777754c5210067d5458e10006de634ca200057d759813103ef421586321257c7558d21026dd1058c20356ed64cc932004fd76cc42003cfc7258630004ff7458e2003ef4325843200cfe7198c20014fc74d8131004fd73d89101467e73d9531006dd435833103e7e725942003cff76c843031ddd744cb31026f43058630006be73590200bcfc7358321005bf74581313667f21d9532025f8704ca20006f440584322876d544c9210dcfd764c1100047f7558d200067f54d8532006dd634c32000df4714c93103e7d425942006df970989101057c754c63003edc3258c20007f170cc51000cfe71d893001cfe7558a10006f7415843203eee425803200cfc72d8520006df53d8d200057f755813103edd5298c2003cfe7258c20004fd7458632024fc7058b3103ef46248510006f731d8131006f77458420026bc30590201557e75983310bfd431cc931006ed3258432006f643586303077431d9531024fe7018d10007d532cc531006f575584320057f754ca300bfcf724cb3115dde76cc9310befb3058331014fe7458d20014fc74d8132004ff7358a10014fc74587321acfe760c931014fe74d8910014fe7458720004fe760c93017edf3158f21006df634c110086f43158620006df4158c20004ff74d8530006dd43584320267c4059420004ff755873200ef7624c52103ef7215863225f5c754cb3003fe6614c83203edd7298c2000677545842003edd32586320bcfc7418d1017eec764c92117fd4714c93129f6d548c921007cf624c930004fd7558f2118e7e654ca300bede7318d100067d650ca30026f67058630007d7324c5210057f74d9532006ed425873203ef652584200067e41d9532006bc74589100def710d8530014fe7498f2103efb7058032006dc5498c200bcfc7598f210267c7059420014fc7458321006de634c32003ede3298c20024fc764c53003edc7258c2003ebd72590200bcfc7598e202e75c654c93113dbc7458131196df31d8d2117ded7298d2121ddd74cc930006df7358d20004ff73583210bedf3198e10005ef724c12003ee
  | 14 => 0xbcfc7498f2117fd6214c9310bef43158432014fc74d8931006f453586300267d1059420026de2058c20006ed425833200ef661484303067c41d9531005f57118930006dd43d8d2003edf7298c20004ff7458d20026dc2098c20004ff7258430056f641584200067f54d8121024fe76cc92003efb2058232267ce42ccb30024fc764c420007d463cc510004ff7558b30006de4358e200067d5498d10006bc535902003fcf634cb211057c754ca30025dc70cc9300267d10596300bcfe7398d2102dbc74589100defa1058331006dc7558c20026df7058c20004ff745823200cfc7158c200bef57198d10006f74158630006bf51590200267e7059630025f676cc5100067e21d953203cfe7218d201f5f775cc5100bedc63cc110026dc3058e20006df63cc120006dd7158c20026dc5098c2003ef421584203667e32d9532005dc7348630014fe7458f210267e205963003edd2158c2000df6718c931004df7358910006f47558420006f55158630024fd71d891000ff36048510004fd755883003e7c3259420026ef72588300bcfc7518d100067d64d9532006dd4358730004fd76cc91001cfc7558d2101cfc75d89301aef71098d21026dc1098c20194fe7618d21004ff7458d1003cfc7258e100067d43596301457c7558931006bd5159020004ff745803206ef621d8520006dd32d813103ef77258420006ed4258830026dd3058830006dc31d8d2001cfc75587203067d21d9531006bf53590200057f7558532006de43d85301dff140cc51000675545843203cff7648110006f753584320057f754c620025f976cc230006de3198c20006df7158c2003edc4298c20006f75158432004fd75d893003eec62cc910004ff7158e2003eec624c931025f8704ca10007f370485100047f75589100067d6548630004fd7298e100067f5458e20006ed42d8931006df5158c2001cfc7558d202e75c754c9310067d745942001cfe75584300067d43d95310beee634c832004ff7558032026bd105902003eec628c93101cfc75584200067f4159420007d5324c521006f563cc51003edd3258032026f61058620026f740584200076f65cc932026ec2058a103067c31d9531006fb70589100277965cc230025fa73cc130006f5515843203cfd73d8532025f87048520026f41058430006dc5358c20027db734c030007e7714c921026bc705902017edf614c931006bd7559020014fe74d812103ef72158420004ff7558432006f43258630006f840d81320267f30596300267c3059420014fc7458d101bf755448510006ef62cc910024fc7358730007d732cc51003ebc32590200067d54d8d1000cfc764c9210047f7459630006bc7159020005f5710c91003cff760c9100beec3258b30025de73cc1300065d5458c20026bd505902003eef63cc932024fe76c
  | 15 => 0x10010000190d401504000a00701300200001d00b02a00002100301e00400101900300000000900400c00800000c00000f03300900200800000500400d0320f100d1ae0000aa00000d00b0052a60c702605700500500100c0090030ca00300000006e00503600600b04424801100234202400000601002003b6b901000000200301600100009e00100801201303400200472852d3f35620250c101c01811402143a00200606401d01d09b2ad00007d0433aa05503b0ab07e04c24800e00000b00000206101600101000000203900700401000e01004c00f02100427700111d14a03000002400000100e00502c01400e0cb00500401500363b00000000000100100a03d0150a10081bc01200000803601732d0d101300f0030760270072c528b00105e0030020022b800405e18e01700600003004e00a0067d545843003cfc760c91006efa1058321004ff71583322275f544c930004ff75d8132004fd764873000cfe715833203ede624c9300bedc7498c200bfd732cc5310bedc7598c20004ff7458632024fe764ca1001cfe7558232006f561cc62018e7c654c931004fd7498c2003cff768c9101a67c658c9311467e76d9531026be2059020006f543586300067d5458232006dd634c420006dc4358c20024fc7098e10004fd7458620006dd4198c200267e10596300067e7159630024fc760ca100bcff7498f200047d7459420024ff71d8910004ff7458732014fc745843033f6f544c832006dc4158c2003cfd7258c2001cfc7558830004fd75d8931024fc7058f21197e7108c921024dd76ccb300063e75590203067e10d95310067d5458d20006755458630006f75158630006dd634c9101b67e65cca30006bc755902000dde71cc931006de7558c20006f56148630006f75058432014fe7458331025de704cb301467e654c420014fe7498d210067c315963000df7734c52123f5d54cc9301e7f250cc51003ef62058432006ed62487300067f43d953203edf3258632026dd4098c2000fd763cc53103ebd2159020005f571cc110014fc7458c20024fd72d85200067c435963003df4764c521004ff74584302ff5c65cc9311cdf774485100beec32588300067c4159630006f54358432014fc7458232014fe7498f200dfd4314c530006dd5498c20004fd7558d210bcfc7598d1018e7d32d9532026ec2058a3003cff768ca10004ff764c830277e5424c521004fd7558730004ff7458f200dcfd76cc630006f653584200bcff7498e10026bf30590200067c655813103ef672584200bfce53cca32006dc3158c200067f72d95320bcff7498d2000ef6614853003cfd71d8121006dd4358c2000cfc7358331084fe761891003cfe76d89100067c7558f200067d5458b3003ded76cca32006fb7058d20006ed42d8930026df5058c200067c43d9531
  | 16 => 0x200000608903b0380e203500000018301000300007e00201100500000101000554002106400200600801b02300900000000500003000000103a00342a00800301013200003600401840800000700d03f0170e403f0280010000050010290080175100000030112b732904900500400601800101e01306d0220000370710430035f30070027a33e90000303fd04601100000100003a00012903d00013700321807e0700050123760640050000350881160050000010a50240010fc00629e00006900801b0180010000572380000030130040180ce00e20b00900300100102700305c00600006000007100100406817830f16209301d03702b00600300800000022200705800200000100001c00000401e01800203007f0044a402a0ce00100000500301700305400602900049e00500001d00100628d00100901b0080000b305d0a800002300d00403a00015e00000000101900401900a00d00100701800000100308f00904100000501000708b00f2e307000000001715600300500600004c04d0060040140000020002bd00333e02400000f00501201301600000003d58a19603551b00307401501102c00100c22309800000200000000033404700100112a08600705400000300201e00702600001d03f07116800402e00002a00000103601604600d00700003300e0670bf0380100020210690000060a50060210ce00000100004f24800006a0070000045b801533300d01b19203202a00201e00a0260050000001150020050fd03f03800400004601d00000700300600000005300000102100105900200000602e02f06800000001b06209d01500000f08403000000600500600000103d0442170140010200082bf03301304369e00402700006d00703806f02d02b32a00101500100d01000040300800200400e00700301f00001c0020041ee00503374402901d00f01000838600000b00602f4c60000270590002f636600c0002bd01a06700600101307a02e3dc03f0572620cf0011d604f02f3fc05121300c07500800006b0070000000780060060452090000203a300800500e00a01000f0d10100020ae0180000030a40a200f2cd0420f32a304702301401800d03700400a00e06d00600100055400301500000005901c0050050320a401d00103b0000030101f50fb00000a00a0000c900000001402b0000020233d500104b00000101d0205fb01c00200a2a60270070010161ff00002403800000800203b02900101900a00002901500401c03800000802701a03c00100136400901f1ee02901a00004b00400702100500b00601100301100501300100600001101d00200008c03500916103601300100a00800b00200200001b00200800600201b00f0020290060000020d400b0016b606e0040b918500000100400100900026300000100a0000
  | 17 => 0x490a701500000d01400501800100101801500000002b04300400
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa5d859d163080011df04baac1988030f1d474589100047dc3ac03026402c3e7455263484c14b90ca1eca988038be0975590200046fc1aeab0e4000a75859d1618c001caea729ac2100029de15735842039d2ec2ca8b18400387e86dd5604c801b8a65b82629080e1f215760c91003d73410e8b086400a7980107654c805878e8aa2c3180123d60774d8d100f56b418e4b0c6000c5f7598d31080095e5003a2c2100021f61f41d95320061eba2a9318400387f87d93654c801c5aa8a14c6900039921532584320061fba4c9b2a646ca5d831c3654c8c30f90eb2a63181cf8b481755902000536c1687b2a6200c3f85dd1624402f998c6b9660901b29760c71d95320053ac0881b2a6400a3d84194604c8091b906bacc6100021fa1d54589100071bc22a8b0c6071e1f4255163080010ff0eb26ca9905eb5a0e74584321443ec38c9b2a620087d87105658c0014eb0ba1ac31801eb9a085458432006363aec49926017ad6831d1610c8033a90e9926290803875d15458c2000716aa28431a426087e87595318c00187ee8aa6c68801fb1e0d3258432007623b26498a4201bc4874c931484510fb0e21eca9881f711d9324c5210053b42886b0c6000ad98010663080018eeeab0a62101ce976165498c2000579c0264b0c6000a6e82993654c401d8d06a12c219002b9e0950584320053b42e86b0c600387e87dd563c80e3c6e84aa2c21900237e1d6318d2003c76412e8b1a2000cd7635c432440070f90aba2c6880029d61470584320061fc22e8b2c60018dd83dd7604c40f1d904baac6100023761c4198c200054f420eab18400387e86dd5604c4018beebb9ac4880022fe11760c9100064e3a0e6b122002c3e7455162cc4091e90ea8ac3180038b5514298d210061eba284b2c600387c855d9318800156d0829ac3180133c18171981320054ec20a6b18400087e87103654c4018b8ea31a64900021fe157118d2038f0fa12a93184000af1801d5610c82f5a906b82c21900e1f2157458f200055ac20a4b0c6073a7585951610802f5af0521ac21901f351d9324c5210053ac0ce1b2a6460a5d83dc3654c50178b08992629082abc60074584200bf6218264b086400c9f74dcd62440010ff0aba2c48801e3da1f515843203d66412c79922000c3f74551618c00f998e4992c1988023be097558d2000572c2264b08640087d84dd563480031ed033b664980021fa1f43594200061fba4e9b2a640087d84dd563c800f59d0438ac6101bfb18c943584320161f3a2a831a4007ace829d163080095e501a1ac3180029ee0164d95320068fba287b2a6200c3f751d1634400187ae8aa4c7908030fdd7745891037f6341286b08647487e871d1658c0091b906b8cc610003171d77358d2000716aa28531e406fec64250d610c8078bceb29ac6100029d6147458420
  | 1 => 0xd0b3a2c31800b0f9d15458c200062ebaea7b1a4000acd82945630800117b0e29ac810002976144198c2000566c1843b126000e355450d618c0070fd0b3b264880031e553764c0300062ebaea7b1a4200c3d7455063480018e8eab0a62101cb954cb545843241e37396a931e420087d84dd5634840147b0832ac299002b960b40584320043f43ea8b1a4000c3c85dd163440014db0420acb180030f5d15458b300256d40082b184007ce4768c9314840f4dd0420aca100023de057458f200046ec3ec61922060c5c76d95324c40595ce8a14c6908123b21d52588300053b42e82b0c6017e5653d4d610c805958e8a12c48801f395c54218d210255d40462b204000ad5819db324c02f5af08a1ac21900e1f217764c4200161f3a2a93184000c3d74551620c1078dae5aa0c6908029d20564d95320061fb2ae931262048dd835db310800517d0fba2c4880028f61771590200061fba2c9b2a6407aac8254d64080e38eae2aa0c6908038b5514258830006363b6ea9924200c3d74553604c8014bd0610acb180021fa1c7558d100052fc2ae2b184000e2d54509628c00187ae8a1acb1801f711c9324c52100656b26e49884000a7a809c7654c8ed55f04baac8100029d61443584200062faa6e6b12200087c8755163c800187ae8aa6c29901e3de19710ca100053b428e8b0c6004af0804c9618c00f1e90eb1a42880123720f764c4200bd6a41aeab086470ad58290d610c80153b0829ec69001eaba0a515902005572c10e6b0840048f6869cd21440014bd0b3a2c61000317dd5634c4200256d400833184000c3d74552634842f9b4a7bb260180033654f764c0300062e3aec6992420087e8755163c80015d304206c099002b560e745843200c76412eab064200a6e82105658c0015b30020ac6101d38b482755902038f33212a8b08640087d87109658c0010ff0abb26488002b560f42586300070aaa286b086400e575450d610c82f1b906ba8c6900021fa1f655893101c3fc3ec9b2a62048f8805d163080070fd0fbaac69081f2b1c9644c4203652ec1ee9b2a64078f487545610c80187ee9aa2c48801eb9a0a54584320061fba2a9b122000e6554509610c8371eb0fb1e6288002ad61275586300046fc1aeab06420087d87d09658c0010ff0ab8cc61022697a0f74d95320061eba6c9b2a620387c855c663080010ff0aba2c6900021fe157458f200047bc0ae8b1a4000e1d5450e63440014dd04206ca9880a2f211764c9100043f43aa8b1a2000a79809c7654c8018e8edbaa629081e3da1f41584323643e436eab02640087e87107654c81755b0438ac810003171d77358d210053b428e8b084071e6632551610c82fd8e62992c21905e3720d74589100145e422eab122000e555490d610c8010fd0faa2c7900021fa1c65581310161e3a2a8b122000
  | 2 => 0x975590200061eba2a931a4002c3e7455263c840159b053a4c6100029b60841594200051f428e6b204000a5f855c6630800156908b9ac3180021fe157458d100043f43e84b2c6000a3e85dc5640800156f08b9ac3181eb175cc65181323a52f428a9318400087e86dd3654c8019e2c3b8263180028fa17735902037d6bc1286b086404af2801d5610800f59904b1a65080021fa1c65589310070eaa286b046400ab9808c564080014ed0ba12c318012bca0074586300057341686b0c6000cd473d8d21440010fb0e086ca990021f21d654c42038f16412eab204000c5c7518d32484033c90e99242880123d219718c91039f17902eab204000c6c751c963440018d8ebb92c688002972157198c2000477c12e8b1a2000c3d74d93654c80187ae8aa2c79080e1fa16764c52003ee33b26498a4200c5c75dd932cc0091ed0fa0ac2100021f61c40d95320053ac2e80b08640087d84dd56244001c3ae8aa4c610002b960b43584200056dc02e8b184004a7a808c5658c0018b8eab1a62100021fe15764c6200247c402e8b1a4200ec5434c9610c8015730028ac81000317e0d74596303cd37c12e8b284074a76851516108005958e8a16c0908021fa1c435942000727b28c499262048dc8754d630800f59d0418ac61007abc600755863000567436e49926007ae482541610c80187ae8aa4c70800237e1d6318d210055bc22e0b086400e2d5450b624c0015e302206c0990ae3de19710ca3003e66392c6986400087d87d0b654c42fd88c6992629080237a1e634c9100043f43e81b2a62178dc835d562440010fd0fa16ca9901eb32097558c200bf6339a64b086400a5d8510d63080014eb0a212c318002b5e0d50584320052e42ac631a4200a74855cd618c0c14bb063a6ca98806f1219324c5210052ec2882b18400087c8755163440015cf04b9ac3180028f610725963000572412e6b0c6002c3e745526344001c6aa9a1ac31821717dcc65589313a43f438e8b284000ad5831d1618c0031d90eb12439801e3e21d50580320061eba2a931e400387c855d9324400156d08292c31800a37e1d43d8d200062e3acc69884000c3f875d564080070f90aba2c69080a2f211760c91003e72b8c8431a4200acd821c56308001938e9b9ac4880030fdd142d95310061fba8e8b122000ea774509610c8014ed0ba02c219002bca00745843200566412c631a2002cac7490962440010fd0e21eca9900387551435803201c3e42ae8b12200087c87551634840187ae9a1acb18002b9a0874586300161f3a2a8b1e420087f855d832440e1d8c8521ac219002b560c725863000536c10e3b2a640387c87d5163c800187ae8aa4c688003a555143584320076321a84b0864048f487505610c0d94dd0418eca990029760f42596300255d400a2b20406c87e87d0f654c8014e
  | 3 => 0x4b086407acc8258d32440014eb0ba0ac210003875514398e200061eba2a931c4000e1d5450f614c0f50f90eb2a6518002b320d621891003d3741686b28406fad58250d610c8014ef02b26ca9900e1f2157218d100047b43880b086400cac74dc9634400195ee8392c688002976167498c200052f41e85b2a6407dc4874c9314840f1b90eb1a64880029760f42d95310246e43a86b184000c6f825d165080015cf06a12c2190123721d634c4200061fba285b2a6400a9d841d56308001ccaa8992c2190829e600715963000578c0686b0c60048f487505618c0014bb0a3a2c6100023ee1d601812100657ba6e4b1a20048f48754561080018b906ba2cb1800b0f9d154d85320053cc0462b2840178dc835d560c84014f30118acb180023be1d62189310071aaa684b0c600ca79801c5650802f5a906a8ac2191cb9990b54584323643f438eab1e40048f686dc5324400159b053a2c6100123721d4358e104452f418e9b2a6200a5d85d0563080e70fb0f3a2cb180029b21562189300070f3a2a93184000c5f75d4d638400587ce8aa6c09905f71cc972cc53100536c1687b2a6400cac741c963440014bf06ba2cb18012b62017458c200051f424e5b2a620387c87d5163440018ece2b28651805f3394f764c8320063b388cb30264078f887501600c8010fb0dbaa65180021f61f435963002579400eab0c6007ae682d05610c801c5aa8a12c5080133c1c161486200070eaa286b1c2000a6e82d0d658c0014bb06206ca988aeb560c74584320047bc0ae8b1a420087e871d56348405958e8a12c39005eb5a0c54584320061eba684b2c6000af180d4d618c001878ebba2c68800389551425843237e6639286b1a2000aad8414b624c00156b0829ac31800b0f1d354589100072baa486b0864048ec87509620c001878ea3a2c6880029d617415843200716aa284b122017ec6534c9610c8010fd0fa0aca1000399d5142584320be2fbaea7318406cc5c76dd5324c0010fb0fa06ca98802b960b43584320061f3a6cb312626ca6e82103654c80159b0418ec690003714c9710ca303a52f428a8b18400387c855d9210c0014ed0a212c318002b560c74584200253d40462b284002c3e7455163c8001d8a64b0a439800a37e1d43d8d210246f43e86b184017ec68290d610c8010fd0fa0acb18006f1a19324c5210052f41883b2a6400ec5534c9610c8e58eae3aa0c69080b0f1d154d891000557c12a6b204060b548150f654c4e9c5e413aac810002976174198c200253d400e2b2c607ba5e839c5658c0014bb0620eca990030f195749893100578c0084b0c606087e87d0f654c4c38bae6328c4988031d1d4764c5210043fc2aec9942071c3d725d564080019cec4b8864880029e20164d95320043fc3ac9b2a620087d8710d658c0010fd0e086ca9901eab20
  | 4 => 0x1080051b90ea1ac68801eb3a1b624c9300043ec3cc9b2a640087d87d0f654c8070f90faa2c6900038de1154584200043e43aa8b1a4000c3f759d56408001c38c8a1eca988038755143583310043f43e85b2a6200c5e65dcd218c00187f08ba2ca1000e1f215764c4200054ec20a6b1c200087e87d5163440e747b0f3aac8101c78d509545843200536c1081b2a6200ec5320c9618c0018deca392c0988030fdd343d953138f0ea12a8b184000e3754951618c0018e8cab8cc09900297a0f42d95310061eba2a8b1e4000c6c75dc963480014f30020acb1800b0f1d154586200043ec3e87b2a620087e87d03654c8d98b8edbaa64988021fe157458d210056b418e8b08400087e87105658c0091e903bb243180022fe11764c91039733196a8b086474a3e851d5640800187ae8326ca988038755143d81310053b42886b08400087d87d0d650802fd8c86992c2190129ea00715942003e6a3b66498a420087e87d95604c4010fb0dbaa62100031b5537258d100247bc3ac798a2000c7b54dd9300c03d1ed0e192c3180028f61773590200061f3a0cb31262028ef8750a63480e38d8e4aa2c6881c7875095498c200043fc2ae431a2017c5f759d6630800f4d904ba2ca10002dc61670cc51000579400eab0864008ed87908634840f9c8ec9926290802ada105358420005e2c08c49926000a9d831c564080091eb03baec6880063721d634c72003d67414e93184000c5f739cd65080014b90ab18c69001eaba0871590200061e42ee8b122000e1d5450d610c801d4a84a02c2190038b551425833203d7341080b086400d5471dd5324c4d9c9ec7b2e64990038d551435843203d7341680b0864008bf845d931880014bd0a20ac610003875514318d200061fba287b2a6202c3e7455162cc001e8eea99262909831d987754c6300053ac28e8b086400a77855c1610c80199ee6392c6880030fdd5644c4200053b40881b2a6471e5732551610c8010fd0faa2c4880021f617735832100c7a40ae8b1e400387c855c463480014db0538acb18002ad21170584320070f3a2a8b18400087f855d9210c0175730038ac8100031ddd5614c6300052fc1ae4b2c6000a76859d161080095e500292c31801237a1f5358e103c537c12e6b284000a7585d09618c0095e501a9ac31800237e1d6318d1000716aa285b0a406087c87d95324c4015af06baac21900b271d14358d1000636aa6ec9906400ec5634c9214403d5e3003a2c3180031d9c7659813201c3e43ea8b122000ad583d01610c8f94b906b92cb180038755143586320052f428833184000c5c75d8d32480ffe8aa899262909c78d50954584200070eaa28731c200087d879d3654c8014bd06206ca989cf1d5c554d8d100056ac18a8b086400e2d54509600c801d8b06a12c21900297a167498c2000752aa28
  | 5 => 0x90033354f764c8320053d40083b2a6400e2d5450961cc8015cf08992c2190028f610659813200536c1062b2c60008de87105630800587ce8aa0c6880029d21532586300145f43ee8b1a2000c3f845d3654c80187ee9a1eca9900e1f21573d81210043f43ecab0a64008be871d163440014bb07a16ca9900297a147458c200bf62c1486b086404aba801c564080010fb0e20eca990021fa1c65581320061fb2ee8b0262178de8710663080014bd0ba1ac610207d11d5324c5210052ec2e86b184000ea542d01610c80187ae83a6ca98812b6a035358e100061eba686b284000acd82106630800f5cd053a2c2190029d617435843203f53c2284b086400e965450d610c8eb57700b9ac8100063720d75583310051ec20e6b284000e4d654c8328c0010fd0e206ca9901eb3a084158c200061e3aac89884000e1f8455163080e38d904ba2ca1001e37a0e76cc9100043ec3881b2a6200c3d7455162cc401c3aa8a1ac71000317550735891000c7a40cec1922000d5431dd5324c4014db0420eca99003171d4735891000c7d436e09922004a7a80105658c0014e90ab82c2190123721d4358e200051ec28e2b204000a7685d0d610c8010fb0fa0acb1801e3b209760c9100061e3a6cab026200c3f7450f654c8010fd0dba6ca9885f351cd614843003d5741062b204086a5e83dc3654c42f9a862b88c690002976174398c2000556c1062b20400aae5821d161080014ed0a382c219002b560c40584323866639486b1a2000a5e8510d63080014f30020aca101fa9720d74596300047dc02e8b1a4200a3e851c5640800147b09396ca98803b1d8e32485100043ec3e85b2a6400a5e85d0e63080070f90abb26508002b9608545843203d67410833184060c7671d94324c4014dd0538acb180029ba0b43d95310061fba2a8b1a200087d859d932440011bf06baac69080b2b1d142584320061eba286b2840028ec8750962440f50fd0fb2a649880387d4e535902000477c12ec9922000c6f65dc9604c4014eb0a21ac31800387e115498c200047dc3ac0302622fbc5838c9314840153d0829ac6100038ddd154586300053ac2e86b084002c3c7455163440011df04baac688003171d7764cb310061fba4e8b2c6000e575394d618c0091ed0fa8ac210002dc61470485100063bb2ae3302640387c855d93048001ab6ea38264981b29ba0841d95320246f43ea6b1840018f4815d1634800187ae8aa0c690802b5e0d725863003c7a43a82b086400a3d84197614c80f5cd04a1ac2190029da1674584320051f420e6b284000ab6849d5618c0014bb06206ca990bfb1219324c52101477c3a85b126000aad8294564080014eb0b3a2c2190123e201764ca100043ec3e82b28400387e87dd5634400f55d05b9ac8100021f61e74d95310161f3a2a931c2000a7685d0d6
  | 6 => 0x53bc2ae6b0c6000c3c75dd1624400187ee8aa2c4880030f5d57359020005e2c18c490a2072e5732d51610c8018dea9b92c6880029be0973596300061eba2a8b18400087d87993654c4011df0eb10c4981829760c72d953139636396a8b1a2000a75851d1618c0014bd0ba0ac61000e1fa1f75589103a63ab8ea9b1a2000e1d5450e63080014db04206ca990038b55142583210054ec20a7b1a420387c87d5163484014eb03386ca988030f993754c4200045fc22eab1a2000e1d5450c63484018beea39ac48801eb920973584200053b42e82b08640087d84dd5634400187ae83a6ca990038d55343584200247a43aa2b0c4007cac625d2624c4095b50028ac6100031b19472581310161f3a2a8b1060078ec825d560cc4014d904b9acb1805fb1dd9324c5210247a43aa2b086000ccd63dc931080014f50130eca990021fa1d5458d210066639c84b122000c79701c3654c4051df0ea14c69080327dd073589100045fc22eab122007a6e820c5650803d5ad063a2c31801eb3a0a5158c200066a39ac290c602087e8710d658c001c6f08aa2c2190021fa1f435963001c3e42aec98e4060a76819c3654c4014eb0a202c21900297a174198c200255c402e6b2040008f5819db324c00517908bb263100028f6107558f200247a43a82b0c4017ad683101610c82f9a8c6b886488003331cd42589100247a432e21922000ae582d0d618c0014db0418aca100038d55143584203072bb1ecb98a6207a6c825cd65080d9c98c5baa64980031bddb754c8320053ac2e82b0c600baad82dcd64080011bf06baac6900028f6147359020007a3c2a6498a420087e871d3654c40187ae8326ca990038b55142584320063b30eea9946000c76655c4328c0018dea9bb264190029760e71596300051f420e4b2c6004ada8014663080018d8cbb92c098806b9219324c5210053741062b2c6000e2d5450863480014bd06206ca9905e3720d75587200bc6e41aec19220008f587141610c801d4ca8a12c2190029da0670d95320053bc2a64b0c6000ec58250d610c8015cb053a2c219002b560e54584320053b42e82b084000e3474551618c10f4bd06396ca9880b271d24358d1000733aa264b08643187d8710f654c8091d90eb12421800399e1532584320051ec20cab026400c5e651cd218c0ef4db0538aca100029d21573584200043e43aa8b12200087e87d95604c801d5284a02c0190aeb9608745843201c3f42ee6b064200af180149618c00587ce8aa4c7900023ee017458d200061fba685b2a6280bc7844c93148401c3aa8a1ec69085eb5a0e545843240fa242a6498a4200e2d5450961c80c14ed02396ca988031d1d5614c6300051ec20cbb026400c6c75dd9320c8014eb02206ca9880a2f2117558d1000673b92c29884004a7a8010565080d94dd0438eca9
  | 7 => 0xe4825c1610c8010fb0dbaa631800387d525458c203452f41ee5b2a6400a75811cb654c40187aebb9ac81000317d5073589103063b30eea988400087d8710b654c401c3aa8a1ac688002b3e097558c200246e41aeb31c200387c855d1634800f5cd05a1ac219003b150d42584320043f43884b2c60008f687141610c80587ce8aa4c69005eb5a0f41584320055ac20a6b084000c5f759d56308001c6ea92a2c2190038d551425863000578c00e8b08646fcd57150c634840f998ec9964298003331cf72589100043ec3e81b2a6400e2d5450b624c4014db05a1aca101c7954c9545843239c3ec3ce8b28400087e8755163480010fb0e21aca10002b66005158c200047ac3880b086482c6e7255263c84ffe8ea899262908029760c41594200043f43887b2a6200ad9809c563080091d90ea12c51801eb9a0873584200056cc1881b0264028ef8750b624c40f4dd0538aca100127ca1f70485100062e3aac69942000a5e83105650800117d0e3a2c4880033c5c760981320043ec3882b284007acc825c563080010fd0e20aca1000317a0f74d95320053ac2ce8b084002c3e7455063484018bb07ba6ca9900387d525498c200bc6e41aea31a4202c3c74d516344001998ec99242980123da1b71481100061fba6a8b1a200087e871d3654c80187ee9a16ca99003875534358c200061fc2ee8b1a2082c6d7255063484018deebb92c68801eb3a0b4398c200043fc2aec988406ca6e82d0f654c80187ee93a2ca100127ca0273485100063ab2ae21946000e4f654c8324c4015cb043a2c318003171d773589100053b42880b086400c6f751c963440015cb04202c2190031755373589100062fbaea6b184000e3554d0d610c80f5cd043a2c21000b0f9d15498e200045f438a6b204000ea474509610c8974bd06386ca99002a7a0c715902003e72312e21922004ada809c563080011bf06ba2c4880029760c41596300161e3a2a9b1a2000ad98014663080014b90ab8ac61000297a0c415963018c3ec38c9b2a6400e2d5450b60484015ad07a12c3180021fe15764c1204262eb98cb3026200a7980987654c8011df0eb10c4880038dd5254584200247643a84b14206087c86dd5604c401caaa8a1ac2190030f5d15418d100246e43ac69942017ad683d01610c8010fd0faa2c690802b960a545843203d7341686b084000e2d5450a63c84091b906ba4c6100029b60b43596300070eaa6873184000c3c65dd1604c4c94bd0638eca991829da0440d953100656ba6c5312620087e875953108001878e832ac0989f69ee01735963005578c00eab084000e1d5450d63080014ed0a3a2c2190021fe1573d812138e1fb92eab204000a6d82993654c40187f08ba6ca988063b60b75d81210043f43885b2a62008dd871056308001c3aa8a1ac398002b36084158c200
  | 8 => 0x100203140282700e00c0607b0040bc0d0030100282b00101600012823002480050020040102700300000c13016018004008000120083a05a09e0400000505c0000f00202c008070290080980000901e00806810002004068111420000180c04e0000500000402c0000e0165d8000101201282481003e0e40b83d034000018110040040680200000c0100e00c0901080009a0bc4081a000004070010180100581401a0241500703c000118020000487880b0000a0120000065a401074000030020000140700487400a0000402900c008068440de058008001240200004800c0140b04c0620000002c0660140780001800400025236048000150082c1878030360180302000807801000026034001b401c000048140602140000010c000060000226004b002000038958040000c80900343602406002072010120010006d80202900000d47811010018199af01600c0580700e07c0003800a00005803038108108020b002c0004e094000130160040b400014004cb0050040ac01c0184706209438800164000001bd03a0000d00003e0642d0410040c00081303e0205780200c00c000010c00140082200206c06002002390010030140440000001a01c0700b0001980302c00203c190060002e807800012ab42a809008000068070040840000200c0000580007e010280150081700000000a09400000000038020001660780f00b0680045c8070001b80880100e0a80100904a0180201a00800c1600f08c0c40200102c0cc000200041d00605c024078ec825d5634400187eebba2c6880123d207764c4200bee398ae39926417ad483541610c8011bf06bb264880021f616764c5200062e3acc69942000e1d5450f63480095e500212c3180021fa1c65585320bf4bc2286b086471e374255161080010fd0e3aac4880021fa1f41d95320061fba2a8b0c40008ef8750a63c84c30fd0dbaa649881eb3a0b4358c200046fc1aeab12200087f855d931c80014bd07a12cb180123d21d41584200052ec1842b2c6007a
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x10c520000000100260004080009c0001c5c700060000002000005a7402902f801300000022a9c00100040000004000061cd0d000000000840000000011420001e055450d4258432456856095450d610c801e055450d325843200689611544c9610c80141d941d4634c9200058564c74551618c00103f985d074d95320060bdd182d0f654c80141d941d7764cb300058364a74551630800181f7460f42d95320050d650655c6604c80582f875514298d2001c0fa6374593654c80181d736106518132457818c95450d610c801625921d154586300078155283509610c80141d941d6634ca100060be1d5450a63c8401835849c4659813245781a095450d610c801625951d142584320068955383509610c8016a1901d14258432385a1e5183509610c801e055490d425843200589650854c9610c801a878450d325843200607dd183d0b654c4012359421532586300040fe6174193654c80582f875514298d21457055c55450c63484e3c25715514218d210069121b854c9314840141c975514358d1003d3125d634c9214400182d7460b43596300050b65075d89324c001e0554609435843200711595325c4328c001c4476dd5324c52137da165283509610c801e055460d42584320068955182d0d610c80182f7460b43d95310050b65075dd9320c8012c591a1b724c93001c0f2617455163c800141d941d7764cb3100703550735096244115e064255143584320050765075d8d3248515c0c725514358d100060b60975dcd6408001a255460b43586300160721d5450d634400160d929d15498c20005076507518d324840142c9755142589100160b21d54509624400141d941d7634c92045685e095450d610c80181d7460f42596300068955182d0d6108001a155460f4258630005076507558d3284001a258550b4058432
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x94d
  | 6 => 0x94e
  | 7 => 0x3
  | 8 => 0x124d
  | 9 => 0x124e
  | 10 => 0x8a
  | 11 => 0x8d
  | 12 => 0x8e
  | 13 => 0x98a
  | 14 => 0x98d
  | 15 => 0x98e
  | 16 => 0x128a
  | 17 => 0x128d
  | 18 => 0x128e
  | 19 => 0x150a
  | 20 => 0x150d
  | 21 => 0x150e
  | 22 => 0xca
  | 23 => 0x4
  | 24 => 0xcd
  | 25 => 0xce
  | 26 => 0x168d
  | 27 => 0x9ca
  | 28 => 0x9cd
  | 29 => 0x9ce
  | 30 => 0x12ca
  | 31 => 0x12cd
  | 32 => 0x12ce
  | 33 => 0x168a
  | 34 => 0x168e
  | 35 => 0xb0d
  | 36 => 0xb0e
  | 37 => 0x154d
  | 38 => 0x154e
  | 39 => 0xb4d
  | 40 => 0xb4e
  | 41 => 0x16cd
  | 42 => 0x16ce
  | 43 => 0x3ca
  | 44 => 0x3cd
  | 45 => 0x3ce
  | 46 => 0x170d
  | 47 => 0xcca
  | 48 => 0xccd
  | 49 => 0xcce
  | 50 => 0x15ca
  | 51 => 0x15cd
  | 52 => 0x15ce
  | 53 => 0x170a
  | 54 => 0x170e
  | 55 => 0xb0955
  | 56 => 0xb0956
  | 57 => 0x94b15
  | 58 => 0x94b16
  | 59 => 0x16c955
  | 60 => 0x16c956
  | 61 => 0x956d5
  | 62 => 0x956d6
  | 63 => 0x9c0d6
  | 64 => 0x9c0d5
  | 65 => 0xcd695
  | 66 => 0x1689d5
  | 67 => 0x9d715
  | 68 => 0xcc9d5
  | 69 => 0x9ccd5
  | 70 => 0xcc9d6
  | 71 => 0x1709d5
  | 72 => 0x1692d6
  | 73 => 0x1692d5
  | 74 => 0x168cd5
  | 75 => 0xcd696
  | 76 => 0x171695
  | 77 => 0x169715
  | 78 => 0xb4b15
  | 79 => 0xb4b16
  | 80 => 0xccb15
  | 81 => 0xb0cd5
  | 82 => 0xccb16
  | 83 => 0x15cb15
  | 84 => 0xb15d5
  | 85 => 0xcd555
  | 86 => 0x154cd5
  | 87 => 0xcd556
  | 88 => 0x16cb55
  | 89 => 0x16cb56
  | 90 => 0xccb55
  | 91 => 0xb4cd5
  | 92 => 0xccb56
  | 93 => 0x170b55
  | 94 => 0xb5715
  | 95 => 0x170b56
  | 96 => 0x17ca
  | 97 => 0x5ca
  | 98 => 0xcd6d5
  | 99 => 0x16ccd5
  | 100 => 0xcd6d6
  | 101 => 0x1716d5
  | 102 => 0x16d715
  | 103 => 0xcc3d5
  | 104 => 0xcc3d6
  | 105 => 0x3ccd5
  | 106 => 0x170cd5
  | 107 => 0x170cd6
  | 108 => 0x17cb
  | 109 => 0x1715d6
  | 110 => 0x1715d5
  | 111 => 0xe8b
  | 112 => 0x178b
  | 113 => 0x104b
  | 114 => 0x1a8b
  | 115 => 0x1049
  | 116 => 0x1a89
  | 117 => 0x9695
  | 118 => 0x9a15
  | 119 => 0x8b16
  | 120 => 0x9716
  | 121 => 0x9896
  | 122 => 0x5cb
  | 123 => 0x12d6d6
  | 124 => 0x12c3d6
  | 125 => 0x12d696
  | 126 => 0x12c596
  | 127 => 0xccb4b1d
  | 128 => 0xb4b0cdd
  | 129 => 0xccb4b1e
  | 130 => 0x104a
  | 131 => 0x1a8a
  | 132 => 0x5c9d2
  | 133 => 0x5d5d2
  | 134 => 0xb40d6
  | 135 => 0xb5716
  | 136 => 0xb5796
  | 137 => 0xcc596
  | 138 => 0x104e93
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1643
  | 6 => 2679
  | 5 => 1135
  | 4 => 69
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
  | 8 => 2*((h/27+packedAt gbK8 (1612+(h % 27)*6) 6) % 62)
  | 7 => 2*((h/547+packedAt gbK7 (60791+(h % 547)*11) 11) % 1643)
  | 6 => 2*((h/907+packedAt gbK6 (128592+(h % 907)*12) 12) % 2679)
  | 5 => 2*((h/406+packedAt gbK5 (66965+(h % 406)*11) 11) % 1135)
  | 4 => 2*((h/72+packedAt gbK4 (4830+(h % 72)*7) 7) % 69)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3f0781e0fe0ff00ffffffffc598478c0ccfff
  | 1 => 0xfc1f801ff0ff0fff01f0ffc00ae478f233727c
  | 2 => 0xffffffe000fff00001ff07fff30780ffc3838f
  | 3 => 0x1fffffff00000001fff8003c07ff03fc03f0
  | 4 => 0x1ffffffffffffffe0000003ff80003fffc00
  | 5 => 0xffe0000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x41200806012019024c518c52808843840444b5
  | 1 => 0x5511808a50650a4e04b8d68180a458b211525c
  | 2 => 0x9a56b2a040d6a014112a432d1305805ac3830a
  | 3 => 0x101b5cdd6a04002829cc62062c06ad037c03e0
  | 4 => 0x820c67118c98c4b0b00000083f500001aaa800
  | 5 => 0xe3800601081088c0c00084303ffb76ec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefee0feeea8a0feeefee0feeea8a0feeefee0feeea8a0feeefee0feeea8a0feeefee0feeea8a0feeefee0feeea8a0feeefee0feeea8a0feeefee0feeea8a0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36280
namespace PEqualNP.Outside.L_meta_36280
open PEqualNP.Outside.L_meta_36280.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 2 := bs0_4_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 6 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 25 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 90 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 44 := bs1_5_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 2 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 6 := bs2_4_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 5 := bs4_2_0
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
theorem bs4_4_384 : Interval s4Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 414 := (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 (concat bs4_4_288 bs4_4_384)))
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
theorem bs4_5_576 : Interval s4Atlas 5 576 40 := block_range (n:=40) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 616 := (concat (concat bs4_5_0 (concat bs4_5_96 bs4_5_192)) (concat (concat bs4_5_288 bs4_5_384) (concat bs4_5_480 bs4_5_576)))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 69 := block_range (n:=69) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 69 := bgb_4_0
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
theorem bgb_5_1056 : Interval gbAtlas 5 1056 79 := block_range (n:=79) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1135 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat bgb_5_864 (concat bgb_5_960 bgb_5_1056))))
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
theorem bgb_6_2592 : Interval gbAtlas 6 2592 87 := block_range (n:=87) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2679 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576))) (concat (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)) (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 bgb_6_1248)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1440 bgb_6_1536)) (concat (concat bgb_6_1632 bgb_6_1728) (concat bgb_6_1824 bgb_6_1920))) (concat (concat bgb_6_2016 (concat bgb_6_2112 bgb_6_2208)) (concat (concat bgb_6_2304 bgb_6_2400) (concat bgb_6_2496 bgb_6_2592)))))
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
theorem bgb_7_1632 : Interval gbAtlas 7 1632 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1643 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)))) (concat (concat (concat bgb_7_864 bgb_7_960) (concat bgb_7_1056 bgb_7_1152)) (concat (concat bgb_7_1248 bgb_7_1344) (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 62 := block_range (n:=62) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := bgb_8_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefee0feeea8a0feeefee0feeea8a0feeefee0feeea8a0feeefee0feeea8a0feeefee0feeea8a0feeefee0feeea8a0feeefee0feeea8a0feeefee0feeea8a0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075680 * 2 ^ 32 + 4277053600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36280.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,1]⟩,⟨.and,[0,2]⟩,⟨.and,[2,3]⟩,⟨.or,[5,6]⟩,⟨.or,[0,8]⟩,⟨.or,[2,3]⟩,⟨.or,[1,10]⟩,⟨.and,[9,11]⟩,⟨.or,[7,13]⟩,⟨.or,[4,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4277053600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4277053600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36280

open PEqualNP.Outside.L_meta_36280 in
theorem PEqualNP.Outside.L_meta_36280 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4277053600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4277053600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
