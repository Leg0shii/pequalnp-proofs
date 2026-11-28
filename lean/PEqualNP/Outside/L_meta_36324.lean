import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36324.Model
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


end PEqualNP.Outside.L_meta_36324.Model

namespace PEqualNP.Outside.L_meta_36324
open PEqualNP.Outside.L_meta_36324.Model
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

end PEqualNP.Outside.L_meta_36324

namespace PEqualNP.Outside.L_meta_36324
open PEqualNP.Outside.L_meta_36324.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x41fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fb20e21fd41c43ea83887f10710ff98e21fe31c43ec63887f4c710fa98e21fc31c43fe43887f88710fb10e21fd21c43ea43887f08710ffa0621fe40c43fa81887f10310ff98621fe30c43fa61887f0c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843ee83087f90610fea0c21fc41843e883087fcc610ff18c21fd31843f863087fc8610ff10c21fd21843f843085f94210ffa0421fe40843fa81087f10210ff98421fe30843fa61087f0c210ff90421fe20843fa41087f08210ff88421f710843f621087fd5110bfaa221bf544427ea8887f95110bf2a221fd54442faa8887f15110be2a221bc5444278a8887fd4d10bfa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887fd0d10ff21a21fd43443f886887fd4910bfa9221fe52442fca4887f54910bea9221fc52442f8a4887fd0910ff21221fd42443f884887fcc910ff19221fd32443f864887fd0510ff20a21f641443fa82887d50510fe20a21ff31443fc62887d8c510fe98a21f531443f862887fc8510ff10a21f621443fa42887d48510fe10a21ff40443fc80887f50110fe20221ff30443fc60887f4c110fe18221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021be540427ca8087f55010beaa021bd540427aa8087f15010be2a021ff53042fea6087f94c10bf29821de53042bca6087f54c10bea9821dd53042baa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021ee52042dca4087f54810bea9021ed52042daa4087f14810be29021ff42043fc84087f50810fe21021ff32043fc64087f4c810fe190217e51043fe82087dd0410ff20821fd41043f882087d10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xe430c3fa86187f10c30ffa9061fe520c2fca4187b94830b729061fd520c2faa4187b54830b6a9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830fe99061fc320c3fea2187f94430bf28861f6510c2eca2187f54430bea8861f5510c2eaa2187f14430ffa0861fe410c3fa82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83dc85907f50b20f6a1641fc42c83fe65907f8cb20f719641fd32c83da65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907bc8720ff10e41fd21c83da43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883fc65107f4ca20fe19441ff51883fca3105f94620fea8c417d51883f8a3107fd0620ff20c41fd41883f883107fcc620ff18c41fd31883f863107fc8620ff10c41fd21883f843105f94220ffa0441fe40883fa81107f10220ff98441fe30883f461107f4c220fc98441fc30883fe41107bc8220fd90441ff54482fea8907f95120bf2a241fd54482faa8907f15120be2a241ff53482fea6907f94d20bf29a41fd53482faa6907f14d20be29a41ff43483fc86907f50d20fe21a41ff42483fc84907b90920fea1241ed42483f884907fcc920ff19241ee32483fa64907b4c920fe19241ff51482fea2907f94520fea8a41fc51482f8a2907fd0520ff20a41fd41483f882907fcc520ff18a41fd31483f862907fc8520f790a41fe21483fa42907b48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907e8c120fe98241f930483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8106f950209f2a041fd54082faa8106f550209eaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107794c20af29841fd53082faa6107754c20aea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041fe42083fa84107f10820ff99041fe32083fa64107f0c820ffa8841fe51082fca2107d94420bb28841fd51082faa2107d54420baa8841fc51083fe82107f90420fea0841fc41083fe62107f8c420fe98841fc31083fe42107f88420fe90841fc21082fca0107fd0020ff20
  | 2 => 0x3fe81206fd0240fda0481ff53502fea6a07f94d40fea9a81fc53502f8a6a07fd0d40dfa1a81fe43503fa86a06f50d40fe21a81ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940dfa1281fe42503fa84a06f50940fe21281ff32503fc64a07f4c940fe19281ff51502fea2a07dd4540bba8a81fe51503faa2a07f14540be28a81f451502e8a2a07fd0540dfa0a81fe41503fa82a06f50540fe20a81ff31503fc62a07f4c540fe18a81ff21503fc42a07f48540fe10a81ff40503f680a07f90140df202817e54103fea6207f94c40bf29881de53102bca6207f54c40bea9881dd53102baa6207f14c40ffa1881fe43103fa86207f10c40ffa9081fe52102fca4207b94840b729081fd52102faa4207b54840b6a9081fc52103fe84207f90840fea1081fc42103fe64207f8c840fe99081fc32103fea2207f94440bf28881f651102eca2207f54440bea8881f551102eaa2207f14440ffa0881fe411037c82207f50440fe20881bc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30ef21e61fd43cc3ba87987f10f30ffa9661fe52cc2fca5987f54b30bea9661fc52cc3fe85987f90b30fea1661fc42cc3fe659877ccb30ff19661fd32cc3ba65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe639877cc730ff18e61fd31cc3ba63987f0c730ff90e61fe21cc3fa43987f08730ffa0661fe40cc3fa81987f10330ffaa4617f548c3fca9185f95230feaa4617d548c3f8a9185f15230bea9c61ff438c3fc87187f50e30fe21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461fd328c3f865187fd4630ff28c617e518c3faa3185f54630fe28c61ff418c3fc83187f50630fe20c61ff318c3fc63187f4c630fe18c61ff218c3fc43187f48630fe10c617e508c3fe81187f90230fea0461fc408c3fe611877cc230fd98461ff544c2fea8987f95130bf2a261fd544c2faa8987f15130be2a261ff434c3fc86987790d30fea1a61dd434c3f886987fd4930bfa9261fe524c3faa4987f14930be29261ff424c3fc84987f50930fe21261ff324c3be64987f8c930fe99261dd324c3f864987fd4530bfa8a61fe514c3faa2987f14530be28a61ff414c3fc82987f50530fe20a61ff314c3be62987f8c530fe98a61dd314c3f862987fc8530ff10a61fd214c3f842987fd0130ff20261fd404c3f880987fcc130fd98261fe304c3bc60987fd5030bfaa061fe540c2fca8186f950309f2a061fd540c2faa8186f550309eaa061fc540c2f8a8185f94c30ffa1861f
  | 3 => 0x6218ff8c431fb18863fd310c7ba6218fd4c431ffa8063fe500c6fca018ff54031bea8063fc500c7fea990dfd5321ff2a6437e54c877ca990cf95321feaa6437d54c877aa990cf55321fe2a6437c54c87fea790dfd4f21ff29e437e53c87faa790df54f21fe29e437c53c87fe8790ff90f21fea1e43fc43c87fe8590ff90b21fea1643fc42c87fe6590ff8cb21fe99643fc32c87fe8390ff90721fea0e43fc41c87fe6390ff8c721fe98e43fc31c87fea190ff94321bf28643fd50c86faa190ff14321ffaa4437f54887fca910df95221feaa4437d54887f8a910df15221ffa9c437f53887fca710df94e21fea9c437d53887f8a710df14e21ffa1c43fe43887fa8710ff10e21bea9443ff42887fc8510ff50a21fe21443ff32887fc6510ff4ca21fe194437e51887fe8310fdd0621ff20c43fd41887f88310fd10621ff98c43fe31887ec6310ff4c621fa98c43fc31887fe4310fbc8621fb90c43ff50887fca110df94221fea84437d50887f8a110ffd5121bfaa243fe54486fca890ff55121beaa243fc54486f8a890ffd4d21bfa9a43fe53486fca690ff54d21bea9a43fc53486f8a690ffd0d21ff21a43fd43487f88690ffd0921ff21243fd42487f88490ffcc921ff19243fd32487f86490ffd0521fba0a43fe41487fa8290ff10521fa20a43ff31487fc6290fd8c521fe98a43f531487f86290ffc8521fb90a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043fd54086faa810ff15021be2a043ff53086fea610ff94c21bf29843fd53086faa610ff14c21be29843ff43087fc8610ff50c21fe218437e52087fe8410ff90821fea1043fc42087fe6410ff8c821fe99043fc32086fca210ffd0421ff20843fd41087f88210ffcc421ff18843fd31087f86210ffc8421f790843fe21087ec4210ff48421f690843f521087fea010ff94021bf28043fd50086faa010ff14021ffa9e81fe53d02fca7a07f54f40bea9e81fc53d03fe87a06fd0f40ff21e81fd43d037a87a07f10f40ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a06fd0b40ff21681fd42d037a85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a06fd0740ff20e81fd41d037a83a07f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40ff21c81fd43903f887207fd4a40ff294817e52903faa5205f54a40fe29481ff42903fc85207f50a40fe21481ff32903fc65207f4ca40fe19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640ff20c81be41903fa83207f10640de20c81ff31903fc63207f4c640fe18c81ff21903fc43207f48640fe10c817e509
  | 4 => 0xdf94f41fea9e837d53d07f8a7a0ffd0f41ff21e83fd43d07f887a0ffd4b41ff296837e52d07faa5a0df54b41fe29683ff42d07fc85a0ff50b41fe21683ff32d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720ff54e41bea9c83fc53907fe8720efd0e41ff21c83fd439077a8720ff10e41ffa9483fe52906fca520ff54a41bea9483fc52907fe8520efd0a41ff21483fd429077a8520ff10a41ff99483fe32907fa6520ff0ca41bf28c83ff419077e8320fdd0641ffa8483fe50906fca120ff54241bea8483fc50907fea6a0dfd4d41ff29a83fd53507f8a6a0df14d41ffa1a83fe43507fa86a0ff10d41ffa92837f52507fca4a0ff54941fe292837c52507fe84a0ff90941fea1283fc42507fe64a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141bf2a083ff53107fca620df94c41fea98837d53107f8a620ffd0c41dfa1883fe43107fa8620ef50c41fe21883ff52107fca420df94841fea90837d52107f8a420ffd0841dfa1083fe42107fa8420ef50841fe21083ff32107fc6420ff4c841fe190837e51107fe8220efd0441ff20883f641107fa8220ef50441faa0883b541107fea020ff94041bf28083fd50106faa020ff14041ffaa6637f54cc7fca998df95331df2a6633e54cc7faa998df55331deaa6633d54cc7f8a998df15331ffa1e63fe43cc7fa8798ff10f31ffa9663fe52cc6fca598ff54b31bea9663fc52cc7fe8598ff90b31fea1663fc42cc7fe6598ff8cb31fe99663fc32cc7fe8398ff90731fea0e63fc41cc7fea198ff94331bf28663fd50cc6faa198ff14331ffaa4637f548c7fca918df95231feaa4637d548c7f8a918df15231bea9c63ff438c7fc8718ff50e31fe21c63ff528c7fca518df94a31fea94637d528c7f8a518ffd0a31ff21463fd428c7f88518ffcca31ff19463fd328c7f86518df94631ffa0c63f7418c7fc8318ff50631fe20c63f4418c7fe6318f7cc631fb98c63ff508c7fca118df94231fea84637d508c7f8a118ffd5131bfaa263fe544c6fca898ff55131beaa263fc544c6f8a898ffd0d31ff21a63fd434c7f88698ffd4931bfa9263fe524c7faa498ff14931be29263ff424c7fc8498ff50931fe21263ff324c7fc6498ff4c931fe19263ff414c7ee8298ff90531fea0a63fc414c7e88298ffcc531fb98a63fe314c7bc6298ffd4131bfa8263fe504c7faa098ff14131be28263ff540c6fea818ff95031bf2a063fd540c6faa818ff15031be2a0637e530c7fe8618ff90c31fea1863fc430c7fea418ff94831bf29063fd520c6faa418ff14831ffa1063fe420c7fa8418ff10831ff99063fe320c7fa6418ff0c831bf28863ff410c7fc8218ff50431fe20863ff310c7be
  | 5 => 0x943bfa9287fe5250ffaa4a1ff14943be29287ff5150efea2a1ff94543fea8a87fc5150ef8a2a1ffd4143bfa8287fe5050ffaa0a1ff14143be282877e5410efca621ffd0c43dfa1887fe4310fbc8621ff50c43dea1887dd4310ffea421ff94843bf29087fd5210efaa421ff14843ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043ffa9e85fe53d0afca7a17f54f42bea9e85fc53d0bfe87a16fd0f42ff21e85fd43d0b7a87a17f10f42ffa8e85fe51d0afca3a17f54742bea8e85fc51d0bfea1a17f94342bf28685fd50d0afaa1a17f14342beaa485ff5390bfca7215f94e42fea9c857d5390bf8a7217fd0e42ff21c85fd4390bf887215f94a42ffa1485bf4290bde85217fd4642ff28c857e5190beca3215d94642fea8c857d5190beaa3215d54642fe28c85ff5090bfca1215f94242fea84857d5090bf8a1217fd4d42bfa9a85fe5350bfaa6a17f14d42be29a85ff4350b7e86a17f90d42fea1a85bd4350bf886a17fd0942f7a1285fe4250b7c84a17fd4542bfa8a85fe5150bfaa2a17f14542be28a85ff5050afea0a17f94142fea8285fc5050af8a0a15f95042ffa9885fe5310afca6217f54c42bea9885fc5310bfe86217f90c42fea1885fc4310afca4217fd0842dfa1085fe4210bdc84217f50842dea1085ed4210bfea2217f94442bf28885fd5110afaa2217f14442ffa8085fe5010afca0217f54042bea8085fc5010bfea9995fd5332ff2a6657e54ccbfaa9995f55332fe2a6657c54ccbfe87997f90f32fea1e65fc43ccbfe85997f90b32fea1665fc42ccbfea3997f94732bf28e65fd51ccafaa3997f14732ffa8665fe50ccafca1997f54332bea8665fc50ccbfea9195fd5232ff2a4657e548cbfaa9195f55232fe2a4657c548cafaa7197fd0e32ff21c65fd438cbf887195f94a32ffa1465fe428cbfa85197f10a32ff99465df328cbde65197fd4632ff28c657e518cbfaa3195f54632fe28c65ff508cbfca1195f94232fea84657d508cbf8a1197fd5132bfaa265fe544cafca8997f55132beaa265fc544caf8a8997fd0d32ff21a65fd434cbf886997fd0932ff21265fd424cbf884997fcc932f799265fe324cbbc64997fd4532bfa8a65fe514cbfaa2997f14532be28a65ff504cafea0997f94132fea8265fc504caf8a0997fd5032bfaa065fe540cafca8196f950329f2a065fd540cafaa8196f550329eaa065fc540caf8a8195f94c32ffa1865fe430cbfa86197f10c32bf29065ff420cbfc84197f50832fe21065ff320cbbe64197f8c832f719065fd320cbba64197b4c832e699065ff510cbfca2195f94432fb2886576510cbfaa2195f54432faa886575510cbf8a2197fd4032ff280657e500cbf4a0195e94032fea80657d500cbf2a0195e54032fe28065ff53d07fca7a0
  | 6 => 0x2400801007000002c00001c00401403000000001402000800000000006401c01c00c00400c00000c00400000000800001002801002404002c00001400002400c00800402400c05405802000000001c01800400000803800000001c02000800000401402801407402801000000400000400c05801800400803400000001c01c00001800801000800c00c00400000000000402c02400400003000000800800000000000402000c00001401c01800003001800000402400002402001001401800c0080000b400c00c00000800000000800000000801c00400c01000002800003000000400c02400003000000000000801002803402801c00402c02001001c01800800c00800003401400000c00000400400400801800007401001000000401800003400000800000002403800009800804c00000c0a404400404001002402406800c05c04c02003c0000100000240100cc04c00800400000c00001001004000004000003004c01000400000c07000c00000000001000407000001406402001400c04400400000009c00001402800002400001409400c01800000401400000001404003000404400001000400400401000801801401403c00002405400800800000000c03000c00c02c00005400c04000403c01800c00000800003001c00400400403001000c00c01400000000000402000000000401401801800800003800c00000000400c00000400001400400400001c00801c00002c07c00004401c00400000000802801405000c01000c00000800403400000801400407000800000c00805002800401401400c00001800400001401c01000003802001801800808007800802401400800003c00000800000801c03403000003000002002001400400400000000802000800000000c00801002000401005c00402400002c00000400c01400006c00003800002c00800400000802002000002c00000c00800000400402000800000804800800001c04c00000802000000000001005800c00c0200000040000b800400802000400401004001806001401803400000c01001402001400c00801801801c00800809000800800002000c00400808807c00000400400800400c00c03002400003802004801406c00c00c00c00800400000001000401000400004c00000001401004400800800c03400004400000403c000028017fea5a1ff94b43bf29687fd52d0efaa5a1ff14b43ffa8e87fe51d0efca3a1ff54743bea8e87fc51d0ffea1a1ff94343bf28687fd50d0efaa1a1ff14343beaa4877e5390ffe8721efd0e43efa1c87ff5290ffca521df94a43fea94877d5290ff8a521ffd4643ff28c877e5190feca321dd94643fea8c877d5190feaa321dd54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4
  | 7 => 0x8703f279063a61842aa10fb28822322230310f833a350000498000001980e22f30002b785299c0000fc24e8000169aa0e288880033a8003240440000001381a617830c8000000c180000a8000000000000000002bc80005200000032f8250000002ba95400000026100018639818893a80011724a3a4b8488022780006c1a72a629c11a03baee327b3e95d80037f8f532c800026b57a752743302699bd15a8f831284206037da2f8000000000510b619d8000ceaeea522a52bdb4597d000230b348000003670002a7b808ac8000db8c88a00000000001b093b34485c8003790a3007a032f014b2d6a10afc1bd8b7a849ab36eac02d2802b8186da64b629b10000de8000002aa96891a800a6505900010081893500001d8972c50000000003978002a020c2b680000000034b02130718397a961355045a9810aa3d8579d602a8000000660000003a08002a40001730b48000e60000000000001710d298201094f80021c9fb0001d18840002e1b9110c0df067b4f294b339388fd1fd01c0449110ee10ea099361c4a0592c35898480028d21980000000000005f26d8000000d300010800000025b84d0001178000000000002070b300e00037f34e31ea668f000000000025600011017baf5a6e949a2b0b91093892ff80c1e7b7e00000018ca3a8748000141ad00019b0000000002159b90cd1410301d01efa1eaf6083ac18fab1b98aa130dc20200022025081480000035e14d800000281a992c9143a2c00000000000024f93211f9dc3130f10000000d6a989e83022ce9a48bc8003758000002da18980012e80000004b2120002c49640000000000b12ff0001561158000000a40001bcba2b6d9482ed9af13cb9604e9b5122a720d721b8408052af9d71afb2318fa0cb5d27d8260e4226a9a35434988d0491a218e26400007992b2920002e80ec92791c22bb26948877b6aad383303501aae91a93992900d49be0daaf89818001a39a41b1ab51670653919972a322a000000000000027a0a84c1280002808000c30de0000ae0001c00001ca8000d50b41db0ea0000290c3b460c806f1f41e719a0e08bd0f6b7aa77225b332f2a42a32b4337a0c6a99ade10d89231094207f373a7f347393b822490548f6068a38823a841ec0eab0503aaf1af415c1a096eb8c258b1a31f26b8000002738000000001ba0062400002748c72f839036115c9569d980035b81f1d20000001aba9aa302f790723e1d825d0959c63519cd13380027a22d0000058001f88000a22eca69000000000000000356a3628a2bb1e61788000000d8b66b2b32f1a8800205396b68811292803008c00005001c02002000400c0f403c04804801009801401000804008402400401000003001402000001000000000802000800000000001c0040040000280300440b800005003802400402c00
  | 8 => 0x11e4a29b740000000002a38002f91fe0000000001108c98001f1064b4a0ed09e8002e31fe80016900000000000032d0000001b5ab1a870000000000a90000000000000000f580031880027334fa93a240f901522f2b30e826000032e2cb8a385399a80014280025d96a0a687416198eb5d8d79bf2609200001e020f0001eb09b00002f885a172952dd36d2cc3140088000001500000002c125580021800026fb1a80000026c1ef056a7f800291800398add9eb80028d9b78003708d1b830000001a1b5297023900000014d1ce800248a4d8000a716c103a780000000b5b9a0ffba514912da3420900038004caed30191407eb2480039c8a2a7d09f8b02fcb1c03a0d230119194a16a8e68000879049f2000195ae430f0001288f9b39990843057100000000139aacb5c00000f0b6a42000348170902b8589439b0ee88b9c3b2ba4b9b38091dd8682453521442d23618d9a5008328281b18911886e881b1700f803b308218793419fa0283038d0b37a7096c8eb33cb20034af4a9eb2620780026383d0f0a4f0001fb8bc2d52c680030eb0c35104a9f700000024c3a18003558821208d10002a69d3ab485426d00003da413703381018240dd2ea00000014020e0001bb80039f84f00036496e0b2abea8600000006a800000304800000029b8c955848afab81000359a24b8b1409a00f197f80013a37212300011e9a9a7b33d98d0fc80007180000000023700030b81782d08a895089a5f2b8b8faa18e3106b3684b9190a10c92cd80011f25faa2185b74a519ca05d25c9b31c8ba68669aeb328001d889480bb5aab91be803387176acb0d5b7c9f50003638000f328200000100001339aaef8002fa1833572c21ea329953b5f18dadc0e49da062a000a60e38b09a79c59128dda13b2a2c807699e85a8000e70003360d62060003408321810000930002d82583439b01d2b5f8589c12c42a98608feb9ea7e369b4c8000000ff2c32a5abf8002311149721878c797d9b8134354a8680013c2758160612e60e5113a03872ad038e0002289f800002e00da1a019ad19473119df1fc84017e00000011bba59e0ae222ea2aa7600ea1f2319509f02ad0723a30000b3a0404d92689a00009ba8130096082daaf0ad80025a8a8a5980012d0000000002441f3800166000217a689f28518ebae49e680000023f0000000711290000000938000aa00024b08103c86badb2ca0f78ac3712148001a28e033721d17700000021006919380013f1f9a8c8e902c9e90b208eb0000200019480000037b0fa00021db4008fa6801f8ef24093f8a5229007119b238000f293d0000000000478000a180011d8000001c523eb0d2208000000000001d5b9711e0000000000000001e580a16680000000014ba4588c92387a30924d0ba8359f9022a2c9bc19b9b2b3936080015218f0780
  | 9 => 0x2ce1e385e8000750001020000000000000bbb2ab168982789c92fd8208c517b2c5a34b0609e0000000000000000002068001d3030a16b6c0000000002c3985105931800262000000000000379a0180032c0000000000000cf80000039d8000000000000000000019550000001393868000000002838000003068001950d03940002fd000124aa28000000002448c41c286218090e08b3641f780036221fba414a997a282ba1c415f0181180ce15e00037500000000021b28c0410ba08d80033c12a9901872479cb00036b87d07aa5e800342a5a00027031ca480389041cc2caa0fb2203137295d1df97f25b0759b983639e16807e32db17839b16348adb8dc9211e99ee8001829a58c089a80023b0700000cb8001378000002430000a580002b8118afb2e80000006180000017e8000000cc80034e8001a3000390a0a198a8b9a680000015f80000000015e80029618b992999b3d0ab06b0000000a8159800055222ab2b650be2942219631dd2a908919e29da0494188a2b00258001ae2b096f2d78000000000002879b681a2511638001bf9ac80028909f1e1a8329e0000001e20000000560b82b380014689c9c7b210001e4000144ad4af3ae88002e7000164a5e2d88002ec1c21aab6c89d28f00038f0af0000289ee078a1e3a38002ae82b1cf83400031b125004394a4a9f0800000080ae280038d00028f8000f70002b138883c36a29b1f59b8adf2ae05bb35a418f4257ac633f2f526a1601513a20632851c83580f3865975a0d297055820305a2dac0ba013e85c34103faf090d169977a629760e780696f8a09eab53b442bd35005031901eadca969ff00027b80000031d19cb678fe34d2549de0960909881b615700006fad60470000001ff9328b980024680031987b8c5aa089907c36b0230002cd37d24724398b0370000001f4a0b00d0000e58002cfabb837929952ab71650002270b88000000001da80039c36631010b218b2533bb02817277a59098800000000233b080001370002160002bc0001de80010536fb0e20b8000001218002abb14a1908e1a52ef0caa1100019100008f000313800099b098000000001160b729c81cb73285b9d04f8581ce11686d30fae594c17197907385faa882a01217ca9b8cb03eb9f22600034793e3272f682708c00029d37b9241d902f26e297a95a53b040ef992356162b4bb89a009fc2f98db0000cc076031aa4b0d965a0291d38ba65b8a07cb851b42670002b42f114e98c0001930383a61308c12be26f00012f00023f9968000390868cda118ab87d8bf000000096b322c8b65a3c0192912e01c981e2aa3340b19d428e80000017990cae985a2f22141458e1ae105b0cf111ab833e1b4b078328003930000418771749d4b8795a00019417500028b31fad9167a1c1f61729589f3091125ad0909b5e9a
  | 10 => 0x38831220828aa7a9e126ab76b0a10785da36800004b59000350800013b3fa9f23b80000000004e2c296b2fe80009c0002908000000002b59ac07082c0c026c800108a570aab6800012c9369802d10f23920ca26300001032891535b000000399ac70000fda128002ab2e3a23b229e2800383a7c9d6ac99f191210a0fb8000000468002710000159fab291e889000015926b0003950a99960f4a540732daaa83a100002e9479621332fe01b95310b80cb77800320b632ad80b0a4ad984800005e0000ae8da16b97c33b2e698a00000017a11300037880031db8aa250000000000000000001270001062150c22d701d1d50003112460000d900006400007b28e0000000c28ad036a0100000012a0001518000001eda0eb6904a00000000012200014e0000000000000000001d0b21ad41430002b9b76012a3d15b14c9450000000098000e980013d9b230b16d0000002f713b80017436e1c095bafb93038627c3451dc88834224e000043a0880012e0b50001cba53392a1aad591cb3a37180000014f24985091b07f8002331c3000288891accb46b5cb1800003b2898000bb00000000025280000023580006999f9ed12fb7eaea9ad8002de9461311d79ecb0ab35279b319cf0002729cc8861ba8000bd8e12e53492fb23a38d8a78000530000000000000ec16d8dfb4c0001cdad3000000154a379c69bb134b4aa7692610f0000978d8395a662321a819d2cf19f0c6024aa71990000000edae7a9f8002bf2b20000000002eb1f69579d13530000598460d39dba93000315800000000000267b280be892ab6382b7c00000000020d9c186e0d40e8b60173884a2e3258bf80000031e0f8b8ea7eb9b80000000036f00012ba3838435a00000000000010125c2718000000453311fda39aeb9b703e0001c71e50081358002803781582ac33890324c8829e306734dac78c48852dfb08a5680006c80006a22100009dae098425523cb15186b77022
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xb400436d52d0010edd07400427f65900109f596400433e5490010cf552400435e5390010d754e400436e5290010db54a40042f66190010bd58640043b441900109fd95400433e5450010cf551400435e5350010d754d400436e5250010db54940042f76150010bd18540043b741500109fd94400427e65100109f594400427c6510010cf950400433d5410010b798c40042dd6310010d794c400435d5310010bb98840042ed6210010db948400436d5210010bd98440042f56110010ed104400427d65cc010cf953300433d54cc010d794f300435d53cc010db94b300436d52cc0109fd96300427d658c010cf952300433d548c010d794e300435d538c010db94a300436d528c010bd98630042f5618c0109fd95300433e544c010cf551300435e534c010d754d300436e524c010db549300427f650c0109f994300427d650c0109f19430042be640c010af590300433e540c010cf550300435e530c010d754c30042ee620c010bb588300436e520c010db54830042f6610c010bd584300427d65c8010cf953200433d54c8010d794f200435d53c8010db94b200436d52c80109fd96200427d6588010cf952200433d5488010d794e200435d5388010db94a200436d5288010bd98620042f561880109fd95200433e5448010cf551200435e5348010d754d200436e5248010db549200427f65080109f994200427d65080109f19420042be6408010af590200433e5408010cf55020042de6308010b758c200435e5308010d754c200436e5208010db54820042f66108010bd584200433e54c4010cf553100435e53c4010d754f100436e52c4010db54b100437565c4010bd99310042f464c4010ddd5310043b654c4010dd55310043b554c4010cd553100437753c4010f594f100437553c4010f554f100435553c4010ddd4b10043e652c4010dd54b10043e552c4010d954b100433e5484010cf552100435e5384010d754e100436e5284010db54a10042f56184010dd94610042f96584010de59610042796584010ee95210043b95484010f694e10043d95384010fa94a10043e95284010be586100437a5184010fc94610043f34184010fc106100427f6544010afd9110042bc6444010cf951100433d5444010d794d100435d5344010db949100436d5244010bdd95100437765440109dd9510043b76444010bd99110042f46444010ed19110042b46444010ddd5110043b65444010dd55110043b55444010cd55110043775344010f594d10043755344010f554d10043555344010ddd4910043e65244010dd54910043e55244010d954910042f76044010dd94110042fb6544010ded95100427b6544010eed9110043b86444010ee95110043b95444010f694d10043d95344010fa94910043e95244010bed8510043f36144010de94510043f25144010
  | 1 => 0x427c658c810cf952320433d548c810d794e320435d538c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810cf951320433d544c810d794d320435d534c810db949320436d524c810bdd8532042f4614c8109fd94320427e650c8109f594320427c650c810af99032042bd640c810cf950320433d540c810d794c320435d530c810db948320436d520c810f34c832042f6610c810bd58432042fa600c810be580320427e64944109f592510427e63944109f58e510427e62944109f58a510427d65d0410cf953410433d54d0410d794f410435d53d0410db94b410436d52d0410bd597410437565d04109d597410437754d0410ed953410437554d0410ed553410433554d0410ddd4f41043d653d0410dd54f41043d553d0410d554f410437752d0410f994b410437552d0410f954b410436552d0410bd583410427f65904109f596410433e5490410cf552410435e5390410d754e410436e5290410db54a41042f66190410dd94641042fa6090410be582410427f6550410cf951410433d5450410d794d410435d5350410db949410436d5250410dd945410427f65104109f594410433e5410410cf550410435e5310410d754c410436e5210410db54841043b54110410be98041042f96010410dd59441042756510410bd99041043b66410410ddd5041043b65410410dd55041043b55410410cd55041043775310410f594c41043755310410f554c41043555310410edd0c41043b54310410ddd4841043e65210410dd54841043e55210410d954841043b74210410ed50841043f26010410bd58041043f160104109f59731042be64cc410af593310433e54cc410cf553310435e53cc410d754f310436e52cc410db54b310427f658c4109f596310433e548c410cf552310435e538c410d754e310436e528c410db54a3104376518c410be98231042f9608c4109fd95310433e544c410cf551310435e534c410d754d310436e524c410db5493104376514c4109fd94310427d650c410cf950310433d540c410d794c310435d530c410db948310436d520c410be98031042f9600c4109f59721042be64c8410af593210433e54c8410cf553210435e53c8410d754f210436e52c8410db54b210427f65884109f596210433e5488410cf552210435e5388410d754e210436e5288410db54a21043765188410be98221042f960884109fd95210433e5448410cf551210435e5348410d754d210436e5248410db549210437651484109fd94210427d6508410cf950210433d5408410d794c210435d5308410db948210436d5208410be98021042f960084109f992500427d64940109f98e500427d63940109f98a500427d62940109f58650043774194010dd106500427d65d0010cf953400433d54d0010d794f400435d53d0010db94
  | 2 => 0x6550c10cf951430433d5450c10d794d430435d5350c10bdd8543042f46150c109fd94430427e6510c109f594430427c6510c10cf950430433d5410c10d794c430435d5310c10af99352042bd64d4810cf953520433d54d4810b798f52042dd63d4810d794f520435d53d48109f993520433e64d48108f993520427d64d4810cf593520423d64d48109f98f520435e63d48109798f520427d63d4810d758f520425d63d48109f987520437661d48109f983520437a60d48109f596520433e5494810cf552520435e5394810d754e520436f52948109f992520427d64948109f98e520427d63948109b596520436f5494810db95252043ae5494810cb952520436d5494810eb552520432d5494810db152520436f5394810db94e52043ce5394810d394e520436d5394810f354e520434d5394810db14e520436f6494810db992520436d6494810db192520436f6394810db98e520436d6394810db18e520436f4394810db90e520436d4394810db10e520436e6194810db186520436e6094810db182520433e5454810cf551520435e5354810d754d520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810dbd95520436f5454810db95152043ae5454810cb951520436d5454810eb551520432d5454810db151520436f5354810db94d52043ce5354810d394d520436d5354810f354d520434d5354810db14d520436f6454810db991520436d6454810db191520436f6354810db98d520436d6354810db18d520436f4354810db90d520436d4354810db10d520436e6154810db185520436e6054810db181520436c1054810af99052042bd6414810cf950520433d5414810b798c52042dd6314810d794c520435d5314810bb988520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109b988520427e6114810dd984520427661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d0810d794f420435d53d0810db94b420436d52d08109fd96420427e65908109f596420427c6590810cf952420433d5490810d794e420435d5390810db94a420436d5290810bd98642042f561908109fd95420427e65508109f595420427c6550810cf951420433d5450810d794d420435d5350810db949420436d5250810bdd8542042f461508109fd94420427e65108109f594420427c6510810cf950420433d5410810d794c420435d5310810db948420436d52108109fd97320427e65cc8109f597320427c65cc810cf953320433d54cc810d794f320435d53cc810db94b320436d52cc8109fd96320427e658c8109f596320
  | 3 => 0x109f98b540436e62d50109b98b540427d62d5010db58b540426d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d62950108f59654043b46195010cfd8e540433e6395010cf58e540433c6395010cfd8a540433e6295010cf58a540433c6295010cf986540433c6195010cf982540433c6095010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540437461550109fd81540427d6055010cfd9554043b46155010cfd8d540433e6355010cf58d540433c6355010cfd89540433e6255010cf589540433c6255010cf985540433c6155010cd185540433e6055010cf181540433c1055010af990540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150108f990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427661150109f980540437a6015010af99353042bd64d4c10cf953530433d54d4c10bb98b53042ed62d4c109f993530433e64d4c108f993530427d64d4c10cf593530423d64d4c109f98b530436e62d4c109b98b530427d62d4c10db58b530426d62d4c109f987530437661d4c109f983530437a60d4c109f596530433e5494c10cf552530435f5394c109f992530427d6494c109f98a530427d6294c1097596530435f5494c10d7952530439e5494c10c7952530435d5494c10e7552530431d5494c10d7152530435f6494c10d7992530435d6494c10d7192530435f6294c10d798a530435d6294c10d718a530435e6194c10d7186530435e6094c10d7182530433e5454c10cf551530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10d7d95530435f5454c10d7951530439e5454c10c7951530435d5454c10e7551530431d5454c10d7151530435f6454c10d7991530435d6454c10d7191530435f6254c10d7989530435d6254c10d7189530435e6154c10d7185530435e6054c10d7181530435c1054c10af99053042bd6414c10cf950530433d5414c10b798c530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd98453042766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c10d794f430435d53d0c109fd96430427e6590c109f596430427c6590c10cf952430433d5490c10d794e430435d5390c10bd98643042f56190c109fd95430427e6550c109f595430427c
  | 4 => 0xf195314433f544c510cf151314435f534c510d714d31442fb604c510be1813144374654c5109d19531442f7644c510bd59131443b7544c510dd9513144374544c510ed1513144334544c510f5d8d31443d7534c510dd94d3144374534c510f514d31442f7624c510ddd493144375524c510fcd8131442f4604c510fc181314427e650c510cfd50314433c540c510bd98431443d5310c5109f99721442be64c8510af593214433f54c8510cf153214436f52c8510db14b21442fa60c8510be583214427e6588510cfd52214433c5488510bd99621443766588510bdd9221442f56488510edd5221443765488510dd15221443b45488510cd15221442f76388510bd58e21443775388510dd54e21442f56288510dd94a21443745288510bd982214427c6548510cfd51214433c5448510dbd49214436c5248510bed8121442f86048510dd19521442746548510bdd9121442f56448510edd5121443765448510dd15121443b45448510cd15121442f76348510bd58d21443775348510dd54d21443e76248510f9d4921443765248510dd14921443e45248510fcd8121442f46048510fc181214427e6508510cfd50214433c5408510bd98421443e521085109f997404433f54d0110cf15340442f661d0110bd58740443b541d01109f996404433f5490110cf15240443b641901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd18540443b541501109f994404433f5410110cf15040442de6310110b758c40442ee6210110bb58840442f66110110bd58440443b641101109f997304433f54cc110cf153304435f53cc110d714f30442f661cc110bd58730443d531cc1109f996304433f548c110cf152304427f654c1109f595304427c654c110cfd51304433c544c110d7d4d304435c534c110bdd8530442f4614c110f54c5304427e650c110af99030442bd640c110cfd50304433c540c110bb98830442ed620c110bd98430442f5610c1109f997204433f54c8110cf153204436f52c8110db14b20442f661c8110bd58720443e521c81109f996204433f5488110cf152204427f65481109f595204427c6548110cfd51204433c5448110dbd49204436c5248110bdd8520442f46148110f9485204427e6508110af99020442bd6408110cfd50204433c5408110b798c20442dd6308110bd98420442f56108110cfd53104433c54c4110eed5310443b854c4110fc90710443f141c4110fc8c710443f131c4110fc88710443f121c4110cfd52104433c5484110bdd9210442f56484110edd5210443765484110dd15210443b45484110cd15210442f76384110bd58e10442f76284110bd58a10443f35084110b798f54042dd63d5010bb98b54042ed62d50109f98f540435e63d50109798f540427d63d5010d758f540425d63d5
  | 5 => 0x43442f66110d10bd58443442fa6010d10be580434433f54d4910cf153524427e64d49109f593524427e63d49109f58f52442be6494910af592524433f5494910cf152524436f52949109f992524433e64949108f992524427d6494910cf592524423d64949109f98e524427d63949109f98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109fd81524437b60549109f994524433f5414910cf150524436d52149109f990524427d64149109f98c524427d6314910db988524427e6114910dd584524427c61149109f980524427c60149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910bd98742442f561d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910bd98642442f561909109fd95424427e65509109f595424427c6550910cfd51424433c54509109fd94424427e65109109f594424427c6510910cfd50424433c5410910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910cfd53324433c54cc910dbd4b324436c52cc910bd98732442f561cc9109fd96324427e658c9109f596324427c658c910cfd52324433c548c910d7d4e324435c538c910bd98632442f5618c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c9109fd94324427e650c9109f594324427c650c910af99032442bd640c910cfd50324433c540c910d7d4c324435c530c910dbd48324436c520c910f34c832442f6610c910bd58432442fa600c910be580324427e65d0510cfd53414433c54d0510be98341442f960d05109f996414433f5490510cf15241442f66590510dd99641442766590510bd59241443b75490510dd95241443745490510ed15241443345490510bd58e41443b74390510ed50e41442f56290510edd0a41443b54290510bd982414427c6550510cfd51414433c5450510bed8141442f86050510dd19541442746550510edd9141443b75450510dd95141443745450510ed15141443345450510bdd8d41442f76250510fcd8141442f46050510fc181414427e6510510cfd50414433c5410510bd98441443b541105109f99731442be64cc510af593314433f54cc510cf153314435f53cc510d714f31442fa60cc510be583314427e658c510cfd52314433c548c510bd9963144376658c510bdd9231442f5648c510edd523144376548c510dd15231443b4548c510cd15231442f5638c510dd94e3144374538c510bd58a3144377528c510dd54a31442f6608c5109
  | 6 => 0x3b44190210cfd51408433c5450210bdd8540842f46150210edd05408433e5410210cf55040842de6310210b758c40842ee6210210bb58840842f66110210bd58440843b44110210d7d4f308435c53cc210d794e308435d538c210bd98630842f5618c210d7d4d308435c534c210af99030842bd640c210d794c308435d530c210bb98830842ed620c210bd98430842f5610c210dbd4b208436c52c8210db94a208436d5288210bd98620842f56188210dbd49208436c5248210af99020842bd6408210b798c20842dd6308210db948208436d5208210bd98420842f56108210bd597108437565c4210bd99310842f464c4210ddd53108437554c4210ddd4f108437553c4210ddd4b108437552c4210be597108437965c42109f98f544427d63d51109f98b544427d62d5110edd87544433f63d5110cf98f544433d63d5110cf18f544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f54951109f992544423e64951109f98e544427d63951109f98a544427d62951109f586544437561951109f58254443796095110cfd91544427f63551109f18d544427f62551109f189544427f6155110ddd85544427761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e6115110dd584544427c61151109f980544427c6015110af994544433e65151108f99454443b56115110cfd8c544433e6315110cf58c544433c6315110cfd88544433e6215110cf588544433c6215110cfd84544433d6115110cd584544433f6015110cf580544433d1015110cfd53534433c54d4d109f993534427d64d4d109f98b534427d62d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6394d109f98a534427d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10cfd51534433c5454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10cfd50534433c5414d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f98453443756114d109f184534427e6014d109f180534427f65d0d109f997434427d65d0d109f197434433f54d0d10cf15343442f661d0d10bd587434427f6590d109f996434427d6590d109f196434433f5490d10cf15243442f66190d10bd586434427f6550d109f995434427d6550d109f195434433f5450d10cf151434427f6510d109f994434427d6510d109f194434433f5410d10cf150
  | 7 => 0x314e10bb98853842ed6214e109f990538433e6414e108f990538427d6414e10cf590538423d6414e10d798c538427e6214e10db988538426e6214e109f588538436d6214e109b58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438433e54d0e10cf553438427f6590e109f996438427d6590e109f196438435e5390e10d754e43842f66190e10bd586438427f6550e109f995438427d6550e109f195438433e5450e10cf551438435e5350e10d754d43842f76150e10bd185438427f6510e109f994438427d6510e109f19443842fa6010e10be580438427e64d4a109f593528427e63d4a109f58f528437561d4a10de983528436f5294a109f992528427d6494a109f98e528427d6394a109fd91528427c6454a109fd8d528427c6354a10dbd8952842be6414a10af59052842de6314a10b758c528436d5214a109f990528433e6414a108f990528427d6414a10cf590528423d6414a109f98c528435e6314a109798c528427d6314a10d758c528425d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f197428433e54d0a10cf553428427f6590a109f996428427d6590a109f196428436e5290a10db54a42842f66190a10bd586428427f6550a109f995428427d6550a109f195428433e5450a10cf551428436e5250a10db54942842f76150a10bd185428427f6510a109f994428427d6510a109f19442842fa6010a10be580428427f65cca109f997328427d65cca109f197328435e53cca10d754f328427f658ca109f996328427d658ca109f196328436e528ca10db54a328427f654ca109f995328427d654ca109f195328435e534ca10d754d328436e524ca10db54932842f7614ca10bd185328427f650ca109f994328427d650ca109f19432842be640ca10af59032843cd320ca10bd98432842f5610ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610dd597418437754d0610ed953418437554d0610ed553418437753d0610dd54f418437752d0610dd54b41843f260d0610bd58341843f160d0610cfd52418433c5490610cf951418433d5450610bed8141842f86050610cfd50418433c5410610ed50441842f56510610dd59441843b66410610ddd5041843b75410610cdd5041843755410610ed15041843775310610dd54c41843b74310610ed50c41843775210610dd54841843b74210610ed50841842f56010610af99331842bd64cc610d794f318435d53cc610be98331842f960cc610d794d318435d534c610bed8131842f8604c610af99321842bd64c8610db94b218436d52c8610be98321842f960c8610db949218436d5248610bed8121842f86048610cfd53408433c54d0210edd07408433e5490210cf55240842f66190210bd5864084
  | 8 => 0x10edd9141c43b75450710dd95141c43745450710ed15141c43345450710bdd8d41c42f76250710bd18141c433e5410710cf55041c43b54110710be98041c42f96010710af99331c42bd64cc710d7d4f31c435c53cc710d794e31c435d538c710be98231c42f9608c710dd59631c42f7648c710bd59231c4376548c710dd15231c4376538c710f594e31c43d5538c710dd14e31c42f5628c710ddd4a31c4375528c710bd98231c43f2608c710fc58231c435f534c710d714d31c42f7654c710ddd9531c42f7644c710bd59131c4376544c710dd15131c43d7634c710f5d4d31c4376534c710dd14d31c43d4534c710bdd8931c4377524c710dd54931c42f4604c710d794c31c435d530c710f54c431c42fa600c710be58031c42be64c8710af59321c436f52c8710db14b21c436e5288710db54a21c42fa6088710be58221c43756588710bdd9221c42f56488710dd95221c43745488710bdd8e21c42f56388710ddd4e21c43755388710dd94a21c43e65288710f954a21c43745288710bd98221c43f26088710fc58221c436f5248710db14921c42f76548710ddd9521c42f76448710bd59121c43765448710dd15121c42f76348710bd58d21c43775348710dd54d21c43e76248710f9d4921c43765248710dd14921c43e45248710bd18121c436e5208710db54821c43e52108710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310ed50740c433f5490310cf15240c43b64190310cf95140c433d5450310bdd8540c42f46150310ed50540c433f5410310cf15040c42de6310310b758c40c42ee6210310bb58840c42f66110310bd58440c43b64110310d794f30c435d53cc310bd98730c42f561cc310f54c730c435e534c310d754d30c42f7614c310bd18530c43d5314c310af99030c42bd640c310bb98830c42ed620c310bd98430c42f5610c310db94b20c436d52c8310bd98720c42f561c8310f948720c436e5248310db54920c42f76148310bd18520c43e52148310af99020c42bd6408310b798c20c42dd6308310bd98420c42f561083109f98f548427d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a548433f64552109fd8d548427c63552109fd89548427c6255210ddd85548433d5415210b798c54842dd6315210bb98854842ed6215210cf990548427e6315210d798c548425e63152109f58c548435d63152109758c548427e6215210db988548426e62152109f588548436d62152109b58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e109fd91538427c6454e10d7d8d538427f6254e109f18953842be6414e10af590538435d5
  | 9 => 0x945200836d5148020f954520083655148020bbd81200836e5048020fa8c120083e93048020bed95200837b65480209ed9520083ba5448020ee551200837b5348020f694d20083795348020f654d20083595348020bed8920083eb6248020de94920083ea5248020fa8c920083e93248020fc94520083f151480209f98f54c427d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c43766195310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c427e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c42be6494f10af59253c435f5394f109f99253c433e6494f108f99253c427d6494f10cf59253c423d6494f109f98a53c427d6294f10dd98653c427f6454f109f19153c435f6354f109fd8953c427c6254f10d754c53c427e6414f109f59053c435e6314f109f98853c427d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10cfd5343c433c54d0f10bd98743c42f561d0f109fd9643c427e6590f109f59643c427c6590f10bd98643c42f56190f109fd9543c427e6550f109f59543c427c6550f10cfd5143c433c5450f109fd9443c427e6510f109f59443c427c6510f10bd98443c42f56110f109f99352c427d64d4b109f98f52c427d63d4b10dd98752c437960d4b10af99252c42bd6494b10dbd4a52c427e6494b10cf99252c423e6494b109f59252c433d6494b108f59252c427e6394b109f58e52c43766194b109fd9152c427c6454b109fd8d52c427c6354b10dbd8952c436d5214b109f99052c427d6414b109f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c433f54d0b10cf15342c42f661d0b10bd58742c427f6590b109f99642c427d6590b109f19642c42f66190b10bd58642c427f6550b109f99542c427d6550b109f19542c433f5450b10cf15142c427f6510b109f99442c427d6510b109f19442c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c42f661ccb10bd58732c427f658cb109f99632c427d658cb109f19632c42f6618cb10bd58632c427f654cb109f99532c427d654cb109f19532c427f650cb109f99432c427d650cb109f19432c42be640cb10af59032c43cd320cb10bd98432c42f5610cb10be98032c42f9600cb10cfd5341c433c54d0710cf95241c433d5490710be98241c42f96090710dd59641c43765490710ed95241c43b55490710dd15241c42f56390710edd0e41c43b54390710bd58a41c43b74290710ed50a41c42f66090710fc98241c43f16090710cfd5141c433c5450710bdd9541c437765507
  | 10 => 0x10833e54cc420cf553310835e53cc420d754f310837651cc420dd547310827f658c4209f996310827d658c420cf952310833d548c420d794e310835d538c420dd9463108375518c4209fd95310827d654c4209f195310833e544c420cf551310835e534c420d754d31082ef624c420bb1893108376514c420dd545310827f650c4209f994310827d650c420cf950310833d540c420d794c310835d530c420dd9443108375510c420af99321082bd64c8420cf953210833d54c8420d794f210835d53c8420db94b210837651c8420dd54721082fa60c8420be583210827d6588420cf952210833d5488420d794e210835d5388420dd546210827f6548420cf951210833d5448420d794d210835d5348420db94921083765148420cf950210833d5408420d794c210835d5308420dd94421083755108420be98021082f960084209f992500827d64940209f98e500827d63940209f597400833e54d0020cf553400835e53d0020d754f400837651d0020dd547400827f65900209f596400833e5490020cf552400835e5390020d754e40082ee6290020bb58a40083765190020dd546400827f6550020cf951400833d5450020d794d400835d5350020bdd8540082f46150020dd945400837551500209fd94400827e65100209f594400827c6510020cf950400833d5410020b798c40082dd6310020d794c400835d5310020bb98840082ed6210020bd98440082f56110020dd944400837551100209f597300833e54cc020cf553300835e53cc020d754f300837651cc020dd547300827f658c0209f596300833e548c020cf552300835e538c020d754e30082ee628c020bb58a3008376518c020dd546300837a508c0209fd95300833e544c020cf551300835e534c020d754d3008376514c020dd545300837a504c0209fd94300827e650c0209f594300827c650c020af99030082bd640c020cf950300833d540c020d794c300835d530c020bb98830082ed620c020bd98430082f5610c020dd9443008375510c020cf953200833d54c8020d794f200835d53c8020dd947200837551c8020dbd5320083ae54c8020db55320083ad54c8020cb553200836f53c8020f394f200836d53c8020f354f200834d53c8020f9947200836d51c8020f9547200836551c8020cf952200833d5488020d794e200835d5388020bb58a200836e5288020dd94620083755188020ee95220083b95488020ded4e20083da5388020de54e20083d95388020d654e20082f96288020de94a20083ea5288020fc94620083f151880209fd95200833e5448020cf551200835e5348020d754d20083765148020dd54520082ef6548020dbd95200826f6548020dbd5120083ae5448020db55120083ad5448020cb551200836f5348020f394d200836d5348020f354d200834d5348020f9
  | 11 => 0x5d53d08209fd96420827d6590820cf952420833d5490820d794e420835d5390820db94a42082f66190820bd58642082fa6090820be582420827f6550820cf951420833d5450820d794d420835d5350820db949420827f65108209f594420833e5410820cf550420835e5310820d754c42082fa6010820be580420827d65cc820cf953320833d54cc820d794f320835d53cc8209fd96320827d658c820cf952320833d548c820d794e320835d538c820db94a32082fa608c820be582320827f654c820cf951320833d544c820d794d320835d534c820db949320827f650c8209f59432082be640c820af590320833e540c820cf550320835e530c820d754c32083cd320c820bd98432082f5610c820be98032082f9600c820af99351082bd64d4420cf953510833d54d4420b798f51082dd63d4420d794f510835d53d4420cf952510833d5494420d794e510835d5394420ddd46510827e64944209f592510827e63944209f58e51083775494420dd95251083b65494420cd95251083755494420ed55251083355494420dd15251083775394420dd94e51083d65394420d594e51083755394420f554e51083555394420dd14e51083776494420dd99251083756494420dd19251083776394420dd98e51083756394420dd18e51083774394420dd90e51083754394420dd10e51083746294420ddd0a51083764294420dd50a51083744294420ddcca51083763294420dd4ca51083743294420dd98251083746094420cf951510833d5454420d794d510835d53544209fd91510827c64544209fd8d510827c6354420ddd9551083775454420dd95151083b65454420cd95151083755454420ed55151083355454420dd15151083775354420dd94d51083d65354420d594d51083755354420f554d51083555354420dd14d51083776454420dd99151083756454420dd19151083776354420dd98d51083756354420dd18d51083774354420dd90d51083754354420dd10d51083766254420ddd0951083764254420dd50951083744254420ddcc951083763254420dd4c951083743254420dd98151083746054420dd08151082be6414420af590510833e5414420cf55051082de6314420b758c510835e5314420d754c51082f66114420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420d794f410835d53d0420dd947410837551d04209fd96410827e65904209f596410833e5490420cf552410835e5390420d754e41083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420d794d410835d5350420dd945410837551504209fd94410827e65104209f594410833e5410420cf550410835e5310420d754c41083765110420dd54441083b541104209fd97310827e65cc4209f59731082be64cc420af5933
  | 12 => 0x950208f596540833f6395020cf98e540833d6395020cf18e540833e6295020cf18a540833f6195020cf986540833d6195020cf186540833e6095020cf182540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cfd95540833f6355020cf98d540833d6355020cf18d540833e6255020cf189540833f6155020cf985540833d6155020cf185540833e6055020cf181540833c2055020af990540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150208f990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540826e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a6015020af99353082bd64d4c20cf953530833d54d4c20bd98753082f561d4c209f993530833e64d4c208f993530827d64d4c20cf593530823d64d4c209f98b530836e62d4c209f987530837661d4c209d987530827d61d4c20dd587530827561d4c209f983530837a60d4c209f596530833e5494c20cf552530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530839e5494c20c7952530835d5494c20e7552530831d5494c20d7152530835f6494c20d7992530835d6494c20d7192530835e6294c20d718a530835f6194c20d7986530835d6194c20d7186530835e6094c20d7182530833e5454c20cf551530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20d7d95530835f5454c20d7951530839e5454c20c7951530835d5454c20e7551530831d5454c20d7151530835f6454c20d7991530835d6454c20d7191530835e6254c20d7189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20af99053082bd6414c20cf950530833d5414c20b798c530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209798c530827e6214c20db988530826e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209e980530827f65d0c209f997430827d65d0c209f197430833e54d0c20cf553430835e53d0c20d754f430827f6590c209f996430827d6590c209f196430833e5490c20cf552430835e5390c20d754e43082f66190c20bd586430827f6550c209f995430827d6550c209f195430833e5450c20cf551430835e5350c20d754d43082ef6250c20bb189430827f6510c209f994430827d6510c209f194430833e5410c20cf550430835e5310c20d754c430827e64948209f592520827e63948209f58e520827d65d0820cf953420833d54d0820d794f42083
  | 13 => 0x9f995414827c65505209f994414827d65105209f194414833f5410520cf15041482ee6210520bb58841483ad4210520ddd4441483745110520ed50441482fa6010520be580414827e65cc5209f597314827c65cc520af99331482bd64cc520bb98b31482ed62cc520ddd47314837451cc520be98331482f960cc5209f996314827d658c5209f196314835f538c520d714e31482ee628c520bb58a314827f654c5209f995314827c654c5209f994314827d650c5209f194314835f530c520d714c31482ee620c520bb5883148377510c520dd14431482fa600c520be580314827e65c8520af99321482bd64c8520bb997214836e65c8520bbd9321483ae64c8520bb59321483ad64c8520ab59321482ef63c8520bb58f214836c51c8520bb98321482ed6288520ddd4621483745188520be98221482f96088520ddd4521483745148520bed8121482f86048520bbd9121482ed6448520bbd8d21482ed6348520f9d8521483e75148520db14521483e45148520f9d0521483e44148520f98c521483e53148520fad8121482ec6048520fa181214827e6508520bb98821483e521085209f997404833f54d0120cf15340482ee62d0120bb58b40483ad42d01209f996404827f65501209f595404827c6550120cfd51404833c5450120bbd8940482ec6250120eb50940482f76150120bd185404827e6510120b798c40482dd6310120bb98840482ed6210120bd98440482f561101209f997304835f53cc120d714f30482ee62cc120bb58b30483cd32cc1209f99630482fa658c120de99630482f9638c120de94e3048378538c120fad8a30482fa628c120fa18a30483ea428c120fa50a30483ea328c120fa4ca30483eb218c120fa486304827f654c1209f595304827c654c120d7d4d304835c534c120bbd8930482ec624c120f34c930482f8654c120de1953048278654c120f6d8d30483db534c120de94d3048378534c120f614d30483da434c120f650d30483eb624c120be18930483e8624c120fa90930483e9424c120f6cc930483ea324c120f64c930483e9324c120f24c930483db314c120f64c530483eb214c120fa485304827e650c120af99030482bd640c120bb98830482ed620c120bd98430482f5610c120be98030483d9300c120bed8f20482f963c8120fa90b20483e942c8120fa8cb20483e932c8120fac8720483e921c8120bbd9220482ed6488120bbd8e20482ed6388120bb58620483eb5088120fa8c220483e93088120b798f54082dd63d5020bd98754082f561d50209f98f540835e63d50209798f540827d63d5020d758f540825d63d50209f98b540836e62d50209f987540837661d50209d987540827d61d5020dd587540827561d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d61
  | 14 => 0x88544827e61151209f584544827e64d4d209f593534827e61d4d209f587534835f5394d209f992534827d6494d209f98e534827d6294d20db58a534827e6194d209f586534827d6094d20de58253482bf6454d20af19153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f99453482be6414d20af590534835d5314d20bd98453482f56114d209f990534833e6414d208f990534827d6414d20cf590534823d6414d20d798c534827e6214d20db588534827c6214d209f98453483766114d209d984534827d6114d20dd58453482756114d20de580534827f65d0d209f997434827d65d0d209f197434833e54d0d20cf553434835f53d0d20d714f43482ee62d0d20bb58b434827f6590d209f996434827d6590d209f196434833f5490d20cf15243482ee6290d20bb58a43482f66190d20bd58643482fa6090d20be582434827f6550d209f995434827d6550d209f195434833e5450d20cf551434827f6510d209f994434827d6510d209f194434833f5410d20cf150434835f5310d20d714c43482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920be98342482f960d09209f99642482f66190920bd58642482ee6590920db99642482ed6490920db952424836c5490920bb58e42483e66190920bb58642483e56190920b958642482ee60909209f195424833f5450920cf15142482fb6050920be181424836c65509209b19542483af6450920ebd51424836e5450920db15142483ac5450920bbd8d42483af4350920eb50d42482ef6150920fad8142482ec6050920fa181424827e6510920bb98842483ad42109209f997324835f53cc920d714f32482fa60cc920be583324827e658c920bb996324836e658c920bbd9232482ed648c920bb58e324836e538c920db14e32482ed618c920fad8232482ee608c920fa182324827c654c920d7d4d324835c534c920bed8132482f8604c920db195324826c654c920bbd9132482ed644c920f3d8d32483cf534c920db94d324836c534c920f314d324834c534c920bbd8532483eb604c920bb18132483e8604c9209f99432482be640c920af59032482ee620c920f34c832482f6610c920bd58432482fa600c9209f993514827d64d45209f98f514827d63d4520ddd4651482bf6454520af19151482df6354520b718d514837551145209f990514827d64145209f98c514827d63145209f997414827d65d05209f19741482ee62d0520bb58b414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520bb98a41482ed6290520eb50a414827f655052
  | 15 => 0x882f56190a20cf951428833d5450a20bed8142882f86050a20d794f328835d53cca20be98332882f960cca20d794d328835d534ca20bed8132882f8604ca20af99032882bd640ca20f34c832882f6610ca20bd58432882f9600ca20ddd46518827e64946209f592518827e63946209f58e51882bf6454620af191518827f6454620cfd91518823f64546209f191518833c64546208f191518827f63546209f18d51882be6414620af59051882de6314620b758c518837551146209fd97418827e65d06209f597418833e54d0620cf553418827f65906209f996418827d6590620cfd52418833c5490620dd946418837551906209fd95418827d65506209f195418833e5450620cf55141883765150620dd545418827f65106209f994418827d6510620cfd50418833c5410620ed50441882fa6010620be580418827f65cc6209f997318827d65cc620af99331882bd64cc620d794f318835d53cc620be98331882f960cc6209fd96318827e658c6209f5963188376518c620dd546318827f654c6209f595318827c654c620d794d318835d534c620bbd8931882ec624c620dd9453188375514c6209fd94318827e650c6209f59431882fa600c620be58031882be64c8620af59321883765188620dd54621882fa6088620be58221883765148620dd54521882fb6048620be181218833f54d0220cf153408833e5490220cf55240882ee6290220bb58a408833f5450220cf15140882f76150220bd185408833e5410220cf55040882de6310220b758c40882ee6210220bb58840882f66110220bd584408835f53cc220d714f308835e538c220d754e30882ee628c220bb58a30882f9658c220de596308837a538c220f694e30883d9538c220de14e30882fa628c220fa98a30883e9628c220d7d4d308835c534c220bed95308837b654c220f6d8d30883db534c220de94d3088378534c220f614d30883da434c220f650d30882f8624c220f6cc930883d9324c220f6cc530883d9314c220af99030882bd640c220d794c308835d530c220bb98830882ed620c220bd98430882f5610c220f64c030882ed65c8220db597208836f54c8220db553208836f53c8220db54f208836d51c8220be597208837965c8220bed8f20882f963c82209f98f544827d63d51209f987544827d61d5120cfd52544827e64951209f98e544827d63951209f58a544836d62951209f986544827d61951209f58254483796095120b7d8d54482dc6355120bdd8554482f46155120cfd91544827f6355120d7d8d544825f63551209f18d544835c63551209718d544827f6255120dbd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f988544836d62151209f1
  | 16 => 0x65110720dd54441c83b541107209fd9731c827e65cc7209f59731c82be64cc720af59331c82ee62cc720bb58b31c827f658c7209f99631c827d658c720bb98a31c82ed628c720dd94631c8375518c7209fd9531c827d654c7209f19531c8376514c720dd54531c827f650c7209f99431c827d650c720bb98831c82ed620c720af99321c82bd64c8720dd94721c837551c8720be98321c82f960c8720bbd9321c83ae64c8720bb59321c83ad64c8720ab59321c82ef63c8720bb58f21c836e51c8720f994721c83e551c8720bb98321c83ea60c8720fa58321c82ef6548720dbd9521c82ef6448720bb59121c82ef6348720bb58d21c83e76148720f9d4521c836e5148720f914521c83e74148720f910521c83e63148720f94c521c82ec6048720dd94421c83755108720f948421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c83ad42d0320cf95140c833d5450320bbd8940c82ec6250320eb50940c82f76150320bd18540c82de6310320b758c40c82ee6210320bb58840c82f66110320bd58440c835e53cc320d754f30c82ee62cc320bb58b30c83cd32cc320d794d30c835d534c320bbd8930c82ec624c320f34c930c82be640c320af59030c82ee620c320bb58830c82f6610c320bd58430c827e63d52209f58f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220bdd8554882f46155220cfd91548827f63552209f18d548827f6155220ddd85548827761552209f185548837461552209d185548833d5415220b798c54882dd6315220bd98454882f56115220cf990548827e6315220d798c548825e63152209f58c548835d63152209758c548836d62152209f984548837661152209d984548827d6115220dd58454882756115220de980548827e64d4e209f593538836d62d4e209f987538827d61d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e20de982538827f6454e209f191538835f6354e209fd85538827c6154e20af99053882bd6414e20d754c53882f66114e20bd584538827e6414e20cf990538823e6414e209f590538833d6414e208f590538835e6314e20db588538827e6114e20dd98453882766114e209f58453883756114e209d584538837a6014e209fd97438827e65d0e209f597438827c65d0e20cf953438833d54d0e209fd96438827e6590e209f596438827c6590e20d794e438835d5390e20bd98643882f56190e20be98243882f96090e209fd95438827e6550e209f595438827c6550e20cf951438833d5450e20d794d438835d5350e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20be98043882f96010e20cf953428833d54d0a20be98342882f960d0a20bd98642
  | 17 => 0xc030fc545300c2f661d5320bd58754c827e63d53209f58f54c836e62d53209f98754c837661d53209d98754c827d61d5320dd58754c827561d5320de58354c833f54953209f98e54c827d6395320db98a54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c833e64153209f98c54c827d6315320db98854c827e61153209f58454c837960153209f99353c827d64d4f20db98b53c827e61d4f209f58753c837960d4f20d7d4e53c827e6494f209f59253c836e6294f209f98653c827d6194f209fd9153c827c6454f20d7d8d53c827f6154f209f18553c82be6414f20af59053c835d5314f20bd98453c82f56114f209f99053c833e6414f208f99053c827d6414f20cf59053c823d6414f20d798c53c836e6214f209f98453c83766114f209d98453c827d6114f20dd58453c82756114f20de58053c827f65d0f209f99743c827d65d0f209f19743c833e54d0f20cf55343c82ee62d0f20bb58b43c827f6590f209f99643c827d6590f209f19643c82ee6290f20bb58a43c82f66190f20bd58643c827f6550f209f99543c827d6550f209f19543c833e5450f20cf55143c827f6510f209f99443c827d6510f209f19443c82ee6210f20bb58843c833f54d0b20cf15342c833e5490b20cf55242c82f66190b20bd58642c82fa6090b20be58242c836d6590b20db95242c83ae5490b20eb55242c836c5490b20bb58e42c83e66190b20bb58642c83e56190b20b958642c82ee6090b20fa98242c83e96090b20cfd5142c833c5450b20bbd9542c836f6550b20ebd9142c83af5450b20db95142c836c5450b20eb15142c82ef6350b20ebd0d42c83ad4350b20bbd8542c82ec6050b20cf95042c833d5410b20eb50842c82fa6010b20be58042c835f53ccb20d714f32c835e538cb20d754e32c82fa608cb20be58232c836d658cb20bbd9232c82ed648cb20db94e32c83ce538cb20f354e32c836c538cb20bb58632c82ee608cb20fa98232c83e9608cb20d7d4d32c835c534cb20bbd9532c836f654cb20bbd9132c82ed644cb20f3d8d32c83cf534cb20db94d32c836c534cb20f314d32c834c534cb20bbd8532c82ec604cb20af99032c82bd640cb20d794c32c835d530cb20f34c832c82f6610cb20bd58432c82fa600cb20be58032c82be64d4720af59351c837751947209f99251c827d64947209f98e51c827d63947209fd9151c827c64547209fd8d51c827c6354720dd54451c827f65d07209f99741c827d65d0720bb98b41c82ed62d0720dd94741c837551d07209fd9641c827e65907209f59641c833e5490720cf55241c82ee6290720bb58a41c83ad42907209fd9541c827d65507209f19541c827f65107209f99441c827d6510720cf95041c833d5410720bb98841c82ed6210720eb50841c837
  | 18 => 0xdd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c36e5250430db549410c3765150430dd545410c27f65104309f994410c27d6510430cf950410c33d5410430db948410c36d5210430dd944410c3755110430ed504410c2be64cc430af593310c33e54cc430cf553310c35e53cc430db94b310c36d52cc430dd947310c37551cc430be983310c2f960cc4309f596310c33e548c430cf552310c36e528c430db54a310c375518c4309fd95310c33e544c430cf551310c35e534c430db949310c36d524c430dd945310c33e540c430cf550310c36e520c430db548310c376510c430dd544310c2fa600c430be580310c27f65c84309f997210c27d65c8430af993210c2bd64c8430cf953210c33d54c8430db94b210c36d52c8430dd947210c37551c84309fd96210c27e65884309f596210c33e5488430cf552210c36e5288430db54a210c3765188430dd546210c27f65484309f595210c27c6548430cf951210c33d5448430b7d8d210c2dc6348430db949210c36d5248430dd945210c37551484309fd94210c27e65084309f594210c33e5408430cf550210c36e5208430db548210c3765108430dd544210c27e64940309f592500c27d65d0030cf953400c33d54d0030db94b400c36d52d0030dd947400c37551d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030db94a400c36d5290030dd946400c37551900309fd95400c33e5450030cf551400c36e5250030db549400c2f76150030bd185400c3765150030dd545400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c2ee6210030bb588400c36e5210030db548400c2f66110030bd584400c3765110030dd544400c33e54cc030cf553300c36e52cc030db54b300c37651cc030dd547300c35f54cc030e7953300c35d54cc030e7553300c31d54cc030f394b300c35d52cc030f354b300c34d52cc030f5947300c35d51cc030f5547300c35551cc030cf952300c33d548c030b758e300c35e538c030db94a300c36d528c030dd946300c375518c030ee952300c3b9548c030be58e300c37a538c030f694e300c3ea528c030de54a300c3e9528c030da54a300c3f2518c030fc546300c27f654c030cf951300c33d544c030db949300c36d524c030dd945300c375514c030b7d95300c35f654c03097d95300c35f544c030e7951300c35d544c030e7551300c31d544c030f3949300c35d524c030f3549300c34d524c030f5945300c35d514c030f5545300c355514c030b7d81300c35e504c030bed95300c37b654c0309ed95300c3ba544c030ee551300c2fb634c030f6d8d300c37a534c030f694d300c3ea524c030de549300c3e9524c030da549300c3db324c030f64c9300c3f2514
  | 19 => 0x1520c36c5454830dbd91520c36e6454830db591520c36c6454830db98d520c36f4354830db90d520c36d4354830db10d520c36f6154830db985520c36d6154830db185520c36e6054830db181520c36c3054830af990520c2bd6414830cf950520c33d5414830bb988520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c36e52d0830db54b420c27f65908309f996420c27d6590830cf952420c33d5490830db94a420c36d5290830bd986420c2f561908309fd95420c27d65508309f195420c33e5450830cf551420c2df6350830b718d420c36e5250830db549420c27f65108309f994420c27d6510830cf950420c33d5410830db948420c36d5210830cf953320c33d54cc830d794f320c36e52cc830db54b320c2fa60cc830be583320c27d658c830cf952320c33d548c830db54a320c27f654c830cf951320c33d544c830d794d320c36e524c830af990320c2bd640c830cf950320c33d540c830db948320c36d520c830f34c8320c2f6610c830bd584320c2fa600c830be580320c2be64d4430af593510c33e54d4430cf553510c2ee62d4430bb58b510c36e52d4430db54b510c33e5494430cf552510c36e5294430db54a510c37751944309f992510c27d64944309f98a510c27d6294430ddd52510c3765494430ed952510c3365494430dd552510c3b55494430cd552510c3745494430ddd4a510c3765294430f994a510c3665294430dd54a510c3e55294430d954a510c3745294430ddd92510c3766494430dd592510c3746494430dd18e510c3774394430dd90e510c3754394430dd10e510c3776294430dd98a510c3756294430dd18a510c3774294430dd90a510c3754294430dd10a510c3773294430dd8ca510c3753294430dd0ca510c3766094430dd182510c33e5454430cf551510c36e5254430db549510c27f64544309f191510c27f62544309f189510c3776554430ddd51510c3765454430ed951510c3365454430dd551510c3b55454430cd551510c3745454430ddd49510c3765254430f9949510c3665254430dd549510c3e55254430d9549510c3745254430ddd91510c3766454430dd591510c3746454430dd98d510c3774354430dd90d510c3754354430dd10d510c3776254430dd989510c3756254430dd189510c3774254430dd909510c3754254430dd109510c3773254430dd8c9510c3753254430dd0c9510c3766054430dd181510c3743054430af990510c2bd6414430cf950510c33d5414430bb988510c2ed6214430db948510c36d5214430bd984510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c36e52d0430db54b410c37651d0430dd547410c27f65904309f996410c27d6590430cf952410c33d5490430db94a410c36d5290430
  | 20 => 0xc36f5288530db14a214c3d531885309fd95214c27e65485309f195214c2de6348530b758d214c3d531485309f994214c27d65085309f194214c2de6308530b758c214c36f5208530db148214c3775108530dd144214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130e750f404c27e65901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c39d4350130bdd85404c2f461501309f994404c2de6310130b758c404c2ee6210130bb588404c2f66110130bd584404c3da43cc130f650f304c2f962cc130f6ccb304c3d932cc130f6cc7304c3d931cc130b7d92304c2dd648c130b758a304c2dd618c130f6d42304c2ee62d5030bb58b540c2f661d5030bd587540c27e63d5030d798f540c27e62d5030db98b540c26e62d50309f58b540c36d62d50309b58b540c27e61d5030dd987540c27661d50309f587540c37561d50309d587540c27e60d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c23d6595030cf98e540c33c6395030cfd8a540c33e6295030cf58a540c33c6295030cfd86540c33e6195030cf586540c33c6195030cf982540c33c6095030cfd91540c27f63550309f58d540c27f62550309f189540c27f61550309f185540c33f6555030cf98d540c33c6355030cfd89540c33e6255030cf589540c33c6255030cfd85540c33e6155030cf585540c33c6155030cf981540c33c6055030cf0c1540c2be6415030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c23e64150309f98c540c35e63150309798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c27d65d0c30cf953430c33d54d0c309fd96430c27d6590c30cf952430c33d5490c30d794e430c2f66190c30bd586430c2fa6090c30be582430c27f6550c30cf951430c33d5450c30d794d430c27f6510c309f594430c33e5410c30cf550430c2fa6010c30be580430c2be64d4830af593520c33e54d4830cf553520c2f661d4830bd587520c33e5494830cf552520c36f52948309f992520c27d64948309f986520c27d6194830dbd52520c36e5494830eb952520c32e5494830db552520c3ad5494830cb552520c36c5494830dbd92520c36e6494830db592520c36c6494830db18e520c36f4394830db90e520c36d4394830db10e520c36f6194830db986520c36d6194830db186520c36e6094830db182520c33e5454830cf551520c27f64548309f191520c27f61548309f185520c36f6554830dbd51520c36e5454830eb951520c32e5454830db551520c3ad5454830cb55
  | 21 => 0x6550d3097195434c39f6450d30e7d51434c35e5450d30d7151434c39c5450d30b7d89434c2df6150d30f6d81434c2dc6050d30f6181434c27e6510d30b798c434c39d4310d309f993524c27d64d49309f987524c27d61d4930dbd4a524c2bf6454930af191524c2f76154930bd185524c2be6414930af590524c36d5214930bd984524c2f561149309f990524c33e64149308f990524c27d6414930cf590524c23d64149309f984524c37661149309d984524c27d6114930dd584524c2756114930de580524c27e65d09309f597424c27c65d0930cf953424c33d54d0930b798f424c2dd63d0930e750f424c36f52d0930db14b424c27e65909309f596424c27c6590930cfd52424c33c5490930b798e424c2dd6390930bd986424c2f56190930be982424c2f960909309fd95424c27e65509309f195424c33e5450930cf551424c39d43509309f994424c27d65109309f194424c33f5410930cf150424c2de6310930b758c424c36f5210930db148424c2fa6010930be580424c27e65cc930b7997324c35e65cc930b7d93324c2dd64cc930d714b324c2dd61cc930f6d83324c2de60cc930f6183324c2dd638c930dbd4a324c36c528c930be982324c2f9608c930dbd49324c36c524c930bed81324c2f8604c930b7d91324c2dd644c930f3d89324c3cf524c930d7149324c3cc524c930d3149324c2df614c930f6d81324c2dc604c930f6181324c27e650c930af990324c2bd640c930b798c324c3cd320c930bd984324c2f5610c930be980324c27e64d45309f593514c27e62d45309f58b514c3775194530afd91514c2bc6454530bbd89514c2ec6254530dd544514c27e64145309f590514c27e62145309f588514c27e65d05309f597414c27c65d0530b798f414c2dd63d0530ddd47414c37451d05309f996414c27d65905309f196414c33f5490530cf152414c2de6390530b758e414c39d43905309fd95414c27e65505309f195414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530e750c414c3775110530dd144414c3b54110530be980414c2f960105309f997314c2be64cc530af593314c2de65cc530d7997314c2df64cc530e7993314c2dd64cc530e7593314c29d64cc530b758b314c35c51cc530b7983314c2dd638c530ddd46314c374518c530be982314c2f9608c530ddd45314c374514c530bed81314c2f8604c530b7d91314c2dd644c530b7d89314c3d7614c530f5d45314c35c514c530f5145314c3d7414c530f5105314c3db604c530b7181314c3d8604c5309f994314c2de630c530f54c4314c27e65c85309f597214c27c65c8530af993214c2bd64c8530b798f214c2dd63c8530ddd47214c37451c8530be983214c2f960c85309f996214c27d65885309f196214c2de6388530b758e214
  | 22 => 0xa30db94a428c36d5290a30bd986428c2f56190a30be982428c2f96090a309fd95428c27d6550a309f195428c33e5450a30cf551428c2df6350a30b718d428c36e5250a30db549428c27f6510a309f994428c27d6510a30be980428c2f96010a30db94a328c36d528ca30be982328c2f9608ca30db949328c36d524ca30bed81328c2f8604ca30af990328c2bd640ca30f34c8328c2f6610ca30bd584328c2f9600ca30ddd46518c27e64946309f592518c27e62946309f58a518c2bf6454630af191518c27f6454630cfd91518c23f64546309f191518c33c64546308f191518c27f62546309f189518c2be6414630af590518c2ee6214630bb588518c37551146309fd97418c27e65d06309f597418c33e54d0630cf553418c27f65906309f996418c27d6590630cfd52418c33c5490630dd946418c37551906309fd95418c27d65506309f195418c33e5450630cf551418c3765150630dd545418c27f65106309f994418c27d6510630cfd50418c33c5410630ed504418c2fa6010630be580418c2be64cc630af593318c376518c630dd546318c2fa608c630be582318c376514c630dd545318c2fb604c630be181318c27f65c86309f997218c27d65c8630af993218c2bd64c8630db94b218c36d52c8630be983218c2f960c86309fd96218c27e65886309f596218c3765188630dd546218c27f65486309f595218c27c6548630b7d8d218c2dc6348630db949218c36d5248630dd945218c37551486309fd94218c27e65086309f594218c2fa6008630be580218c33f54d0230cf153408c33e5490230cf552408c2de6390230b758e408c33f5450230cf151408c2f76150230bd185408c33e5410230cf550408c2de6310230b758c408c2ee6210230bb588408c2f66110230bd584408c2dd65cc230d7597308c35f54cc230d7553308c35d52cc230d7547308c2f965cc230de597308c2f962cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c27e64951309f58e544c35d63951309f98a544c27d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c27f6255130dbd89544c26f62551309f189544c36c62551309b189544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27e6515130cf550544c33e64151309f98c544c35d63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c2f66190d30bd586434c2de6590d30d7996434c2dd6490d30d7952434c35c5490d30b758a434c3d66190d30b7586434c3d56190d30b5586434c2de6090d309f195434c33f5450d30cf151434c2fb6050d30be181434c35c
  | 23 => 0x7d9532cc35f654cb30b7d9132cc2dd644cb30f3d8932cc3cf524cb30d794932cc3cc524cb30b7d8532cc2dc604cb30af99032cc2bd640cb30db94832cc36d520cb30f34c832cc2f6610cb30bd58432cc2fa600cb30be58032cc2be64d4730af59351cc37751947309f99251cc27d64947309f98a51cc27d62947309fd9151cc27c64547309fd8951cc27c6254730dd54451cc27f65d07309f99741cc27d65d0730b798f41cc2dd63d0730dd94741cc37551d07309fd9641cc27e65907309f59641cc33e5490730cf55241cc2de6390730b758e41cc39d43907309fd9541cc27d65507309f19541cc27f65107309f99441cc27d6510730cf95041cc33d5410730b798c41cc2dd6310730e750c41cc3765110730dd54441cc3b54110730af99331cc2bd64cc730dd94731cc37551cc730be98331cc2f960cc730b7d9331cc39e64cc730b759331cc39d64cc730a759331cc2dd62cc730d794731cc3d651cc730f554731cc2de60cc730f698331cc3d960cc730b7d9531cc35f654c730b7d9131cc2dd644c730b7d8931cc3d7614c730f5d4531cc35e514c730f514531cc3d7414c730f510531cc2dc604c730dd94431cc375510c730f54c431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730af99321cc2bd64c8730b798f21cc2dd63c87309fd9621cc27e65887309f59621cc2de6388730b758e21cc3765188730dd54621cc3d531887309fd9521cc27d65487309f19521cc2de6348730b758d21cc3765148730dd54521cc3d531487309fd9421cc27e65087309f59421cc2de6308730b758c21cc33e54d0330cf55340cc2de63d0330b758f40cc39d43d0330cf95140cc33d5450330b7d8d40cc2dc6350330e750d40cc2f76150330bd18540cc2de6310330b758c40cc2ee6210330bb58840cc2f66110330bd58440cc35d63d52309f98b548c27d62d52309f987548c27d61d5230de983548c33f54952309f98a548c27d62952309f986548c27d6195230bdd85548c2f46155230cfd91548c27f62552309f189548c27f6155230ddd85548c27761552309f185548c37461552309d185548c33d5415230bb988548c2ed6215230bd984548c2f56115230cf990548c35d63152309f988548c36e62152309b988548c27d6215230db588548c26d62152309f984548c37661152309d984548c27d6115230dd584548c2756115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c2f66190e30bd586438c33e5450e30cf551438c2fb6050e30be181438c36f5294a309f992528c27d6494a309f986528c27d6194a30de982528c27f6454a309f191528c27f6154a309f185528c2be6414a30af590528c36d5214a30bd984528c2f56114a309fd97428c27e65d0a309f597428c33e54d0a30cf553428c27f6590a309f996428c27d6590
  | 24 => 0x211027e65084409f594211035e5308440d754c211036e5208440db54821103765108440dd544211033e4194040cf106501035e53d0040d754f401036e52d0040db54b401037651d0040dd547401039e53d0040cf54f401039d53d0040c754f40103ae52d0040cf54b40103ad52d0040cb54b40102be61d0040ed947401033d51d0040ed547401033551d0040af592401033e5490040d794e401035d5390040db94a401036d5290040dd94640103755190040be592401037a5490040ee95240103da5390040f654e40103ea5290040fa54a40103f25190040fc54640103ba4190040ee106401027f6550040d794d401035d5350040db949401036d5250040bdd8540102f46150040dd94540103755150040afd95401033f65500408fd95401039e5350040cf54d401039d5350040c754d40103ae5250040cf54940103ad5250040cb54940103b76150040af18540103b46150040ad18540103b65150040cf54540103b55150040cd54540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040f694d40103d95350040fa94940103e95250040fcd8540103f06150040fc94540103f15150040bd98754cc2f561d5330d798f54cc27e62d53309f58b54cc27e61d5330dd98754cc27661d53309f58754cc37561d53309d58754cc37960d5330cfd5254cc35e63953309f98a54cc27d62953309f98654cc27d6195330cfd9154cc27f62553309f18954cc27f61553309f18554cc33d5415330cf99054cc35e63153309f98854cc27d62153309f98454cc27d6115330de58054cc33f54d0f30cf15343cc33e5490f30cf55243cc2f66190f30bd58643cc2fa6090f30be58243cc35d6590f30d795243cc39e5490f30e755243cc35c5490f30b758a43cc3d66190f30b758643cc3d56190f30b558643cc2de6090f30f698243cc3d96090f30cfd5143cc33c5450f30b7d9543cc35f6550f30e7d9143cc39f5450f30d795143cc35c5450f30e715143cc2df6250f30b7d8543cc2dc6050f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc36f5294b309f99252cc27d6494b309f98652cc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30af99052cc2bd6414b30db54852cc2f66114b30bd58452cc27f65d0b309f99742cc27d65d0b30cf95342cc33d54d0b30b798f42cc2dd63d0b30e750f42cc27f6590b309f99642cc27d6590b30b798e42cc2dd6390b30bd98642cc2f56190b309fd9542cc27d6550b309f19542cc33e5450b30cf55142cc39d4350b309fd9442cc27e6510b309f59442cc2de6310b30b758c42cc36e52ccb30db54b32cc2fa60ccb30be58332cc2df64ccb30b759332cc35e52ccb30f394b32cc3cd52ccb30b758732cc2de60ccb30f698332cc3d960ccb30b
  | 25 => 0x3744394440ddd8a51103766294440dd58a51103746294440ddd0a51103764294440dd50a51103744294440ddcca51103763294440dd4ca51103743294440dd98251103746094440d794d511035d5354440db949511036d52544409fd8d511027c63544409fd89511027c6254440ddd9551103b46454440ddd4d51103765354440f594d51103565354440dd54d51103d55354440d554d51103745354440ddd4951103765254440f994951103665254440dd54951103e55254440d954951103745254440dd99151103776354440dd98d51103756354440dd18d51103774354440dd90d51103754354440dd10d51103776254440dd98951103756254440dd18951103774254440dd90951103754254440dd10951103773254440dd8c951103753254440dd0c951103766054440dd18151103744054440b798c51102dd6314440d794c511035d5314440bb98851102ed6214440db948511036d5214440bd98451103755114440cf953411035e53d0440d754f411036e52d0440db54b411037651d0440dd54741102fa60d0440be583411027d6590440d794e411035d5390440db94a411036d5290440dd54641102bd6590440cf596411023d6590440e794e411033d5390440e754e411031d5390440eb94a411033d5290440eb54a411032d5290440af98641103b65190440cf54641103b55190440cd54641102bd60904409fd95411033e5450440d794d411035d5350440db949411036d5250440dd945411035e5310440d754c411036e5210440db54841103765110440dd54441103b54110440be98041102f96010440e794c411033d5310440e754c411031d5310440eb948411033d5210440eb548411032d5210440af98441103b66110440ed944411033d5110440ed54441103355110440ee98041102bd6010440ee580411027f65cc4409f997311027d65cc440af99331102bd64cc440d794f311035d53cc440db94b311036d52cc440dd947311037551cc4409fd96311027e658c4409f596311035e538c440d754e311036e528c440db54a3110376518c440dd54631103b4418c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d311036e524c440db5493110376514c440dd54531103b4414c4409fd94311027e650c4409f594311035e530c440d754c311036e520c440db5483110376510c440dd544311027f65c84409f997211027d65c8440af99321102bd64c8440d794f211035d53c8440db94b211036d52c8440dd947211037551c84409fd96211027e65884409f596211035e5388440d754e211036e5288440db54a21103765188440dd54621103b441884409fd95211027d65484409f19521102bf6448440af191211035e5348440d754d211036e5248440db54921103765148440dd54521103b441484409fd94
  | 26 => 0x254c409fd85531027c6154c40d7d95531035e6454c40d7d89531035e6254c40d7589531035c6254c40d7d85531035e6154c40d7585531035c6154c40d7981531035c6054c40d710153102de6314c40d754c53102ee6214c40bb58853102f66114c40bd584531033e54d0c40d794f431035d53d0c40be98343102f960d0c409f596431035d5390c40bd98643102f56190c409fd95431033e5450c40d794d431035e5310c40d754c43102fa6010c40be58043102de63d4840b758f521035e53d4840d754f52102f661d4840bd587521035e5394840d754e521036f52948409f98e521027d63948409f986521027d6194840dbd4e521036e5394840f394e521034e5394840db54e52103cd5394840d354e521036c5394840db192521036f6394840db98e521036d6394840db18e521036f4394840db90e521036d4394840db10e521036f6194840db986521036d6194840db186521036e6094840db182521035e5354840d754d521027f63548409f18d521027f61548409f185521036f6554840dbd4d521036e5354840f394d521034e5354840db54d52103cd5354840d354d521036c5354840db991521036f6354840db98d521036d6354840db18d521036f4354840db90d521036d4354840db10d521036f6154840db985521036d6154840db185521036e6054840db181521036c4054840b798c52102dd6314840d794c521035d5314840bb988521036d5214840bd98452102f56114840cf953421035e53d0840d754f421036e52d0840db54b42102fa60d0840be583421027d6590840d794e421035d5390840db54a42102f66190840bd586421027f6550840cf951421035e5350840d754d421036e5250840d794c421035d5310840db948421036d5210840be98042102f960108409fd97321027e65cc8409f597321035e53cc840d754f321036e52cc840db54b321027f658c8409f996321027d658c840d794e321035d538c840db94a321036d528c8409fd95321027d654c8409f19532102bf644c840af191321035e534c840d754d321036e524c840db549321027f650c8409f994321027d650c840af99032102bd640c840d794c321035d530c840db948321036d520c840f34c832102f6610c840bd58432102fa600c840be58032102de63d4440b758f511035e53d4440d754f51102ee62d4440bb58b511036e52d4440db54b511035e5394440d754e511036e5294440db54a511037751944409f98e511027d63944409f98a511027d6294440ed19251103775394440dd94e51103d65394440d594e51103755394440f554e51103555394440dd14e51103775294440dd94a51103e65294440d994a51103755294440f954a51103655294440dd14a51103746494440ddd8e51103766394440dd58e51103746394440ddd0e51103764394440dd50e5110
  | 27 => 0x40ddd8f515037663d4540dd58f515037463d4540ddd0f515037643d4540dd50f515037443d4540ddd8b515037662d4540dd58b515037462d4540ddd0b515037642d4540dd50b515037442d4540ddccb515037632d4540dd4cb515037432d4540ddd83515037560d4540ddd46515037551145409f98c515027d6314540cfd0c515033d43145409f988515027d6214540cfd08515033d4214540bd99451503766514540ed59051503775314540dd94c51503755314540dd14c51503b74314540ed50c51503775214540dd94851503755214540dd14851503b74214540ed50851503776414540ddd8c51503766314540dd58c51503746314540ddd0c51503374314540dd90c51503754314540cd50c51503744314540ddd8851503766214540dd58851503746214540ddd0851503374214540dd90851503754214540cd50851503744214540ddcc851503763214540dd4c851503743214540ddd8051503756014540dd500515027e65d0540dd14741502be65d0540cf997415023e65d0540af58f41502bd62d0540edd47415033c51d0540ed147415033451d0540af98341502bd6490540ddd4641503745190540be98241502f96090540ddd4541503745150540bed8141502f86050540afd8d41502bf6250540edd8541503b75150540cf14541503b45150540cd14541503bb6050540af18141503b860505409f99441502be6410540ddd4441503b541105409f997315027d65cc5409f19731502be64cc540af593315037751cc540dd147315027e658c5409f596315027c658c540af99231502bd648c540ddd463150374518c540edd06315027f654c5409f995315027c654c540af99131502bd644c540ddd453150374514c540edd05315027e650c5409f594315027c650c540af99031502bd640c540ddd443150374510c540be98031502f9600c5409f997215027d65c85409f19721502be64c8540af593215037751c8540dd147215027e65885409f596215027c6588540af99221502bd6488540ddd4621503745188540edd06215027f65485409f995215027c6548540af99121502bd6448540ddd4521503745148540edd05215027e65085409f594215027c6508540af99021502bd6408540ddd4421503745108540be98021502f96008540ddd47405037451d0140eed0f40503b943d0140eed0b40503b942d0140fcd4740503f051d0140eed0740503b941d0140ddd4640503745190140af58e40502bd6290140af58640503b75190140cf14640503b45190140cd14640503bb5090140bb98b53102ed62d4c40bd98753102f561d4c40d7d4e531027e6294c409f58a531027e6194c409f586531035c6494c40d7d8a531035e6294c40d758a531035c6294c40d7d86531035e6194c40d7586531035c6194c40d7982531035c6094c409fd89531027c6
  | 28 => 0x98441903b75110640cf54441903b45110640af580419027f65cc6409f997319027d65cc640af99331902bd64cc640d794f319035d53cc6409fd96319027e658c6409f5963190376518c640dd54631903b4418c6409fd95319027d654c6409f19531902bf644c640af191319035e534c640d754d3190376514c640dd54531903b4414c6409fd94319027e650c6409f59431902fa600c640be580319027f65c86409f997219027d65c8640af99321902bd64c8640db94b219036d52c86409fd96219027e65886409f59621903765188640dd54621903b441886409fd95219027d65486409f19521902bf6448640af191219036e5248640db54921903765148640dd54521903b441486409fd94219027e65086409f59421902fa6008640be58021902bd65d0240cf597409033d53d0240cf54b40902be61d0240cf54740902f965d0240de597409027e62d4d409f58b535027e61d4d409f587535035f5394d40bd98653502f56194d40bbd8953502ec6254d40bdd8553502f46154d40d754c535027e6214d409f588535027e6114d409f584535027e65d0d40af997435033e65d0d40cf14f43502bd62d0d40af58743502be60d0d40af592435035f5390d40d714e43502f66190d40bd58643502fa6090d40be582435035f5350d40d714d43502fb6050d40be181435039f6350d40e7d4d435033c5350d40e714d43502bf6250d40afd8543503bb6050d40af18143503b86050d409f99443502be6410d40e750c435027e63d49409f58f525033f43d4940cf50f525027e61d49409f587525036f5294940bd98652502f56194940b7d8d52502dc6354940bdd8552502f46154940db548525027e63149409f58c525027e61149409f584525027e65d0940af997425033e65d0940af58f425033f53d0940cf14b42502bd61d0940af98342502bd6490940dbd4a425036c5290940bd98642502f56190940be98242502f96090940dbd49425036c5250940bed8142502f86050940afd8d425033f5350940ebd8942503af5250940cf14942503ac5250940afd8542503bb6050940af18142503b860509409f99442502be6410940eb508425027e65cc9409f597325027c65cc940af99332502bd64cc940dbd4b325036c52cc9409f996325027d658c9409f19632502be648c940af592325035f538c940d714e325027f654c9409f995325027c654c940af99132502bd644c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325036f520c940db14832503cd320c940bd98432502f5610c940be98032502f9600c9409f98f515027d63d45409f98b515027d62d4540edd93515037753d4540dd94f515037553d4540dd14f51503b743d4540ed50f515037752d4540dd94b515037552d4540dd14b51503b742d4540ed50b515037764d45
  | 29 => 0x2d027e658cb409f59632d02be648cb40af59232d027f654cb409f59532d027c654cb40af99132d02bd644cb409fd9432d027e650cb409f59432d02be640cb40af59032d03cd320cb40bd98432d02f5610cb40be98032d02f9600cb40ddd4651d027e63947409f58e51d033f4394740cf50e51d027e62947409f58a51d033f4294740cf50a51d027f63547409f18d51d027f62547409f18951d03755114740dd94741d037551d0740be98341d02f960d0740af58f41d02bd62d0740cf94741d03b651d0740ed54741d02be60d0740ee98341d03b960d0740afd9541d033f6550740afd8d41d02bf6250740edd8541d03b75150740cf94541d03b45150740af18141d03765110740dd54441d03b54110740be98041d02f960107409fd9731d027e65cc7409f59731d02be64cc740af59331d027f658c7409f99631d027d658c740af99231d02bd648c740edd0631d027f654c7409f59531d027c654c740af99131d02bd644c740edd0531d027f650c7409f99431d027d650c740af99031d02bd640c7409fd9721d027e65c87409f59721d02be64c8740af59321d027f65887409f99621d027d6588740af99221d02bd6488740edd0621d027f65487409f59521d027c6548740af99121d02bd6448740edd0521d027f65087409f99421d027d6508740af99021d02bd6408740d7d4e539027e6294e409f58a539027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40bb98853902ed6214e40bd98453902f56114e40d794e439035d5390e40bd98643902f56190e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40dbd4a529027e6394a409f58e529027e6194a409f586529027f6354a409f18d529027f6154a409f18552902de6314a40b758c529036d5214a40bd98452902f56114a40db94a429036d5290a40bd98642902f56190a40be98242902f96090a40db949429036d5250a40bed8142902f86050a409fd97329027e65cca409f597329035e53cca40d754f329027f658ca409f996329027d658ca40db94a329036d528ca409fd95329027d654ca409f19532902bf644ca40af191329035e534ca40d754d329036e524ca40db549329027f650ca409f994329027d650ca40af99032902bd640ca40f34c832902f6610ca40bd58432902fa600ca40be580329037751946409f98e519027d63946409f98a519027d62946409fd8d519027c63546409fd89519027c6254640b798c51902dd6314640bb98851902ed6214640dd54451903765190640dd54641902fa6090640be582419033d5390640cf54a41903b65190640cf54641903b55190640ee98241902bd6090640ee58241903765150640dd54541902fb6050640be18141903b54110640af594419033d6510640cf54c419033d5210640ed
  | 30 => 0x7f658c8219f596320875e538c821d754e32086f6618c821bd586320867f654c8219fd94320867d650c821af99032086bd640c821d794c320875d530c821f34c832086f6610c821bd58432086fa600c821be580320867e64944219f592510867e63944219f58e510867d65d0421dd947410867f65904219f596410873e5490421cf55241086ee6290421bb58a410867f65504219fd94410867e65104219f594410867c6510421cf950410873d5410421bb98841086ed6210421dd94441087b541104219f59731086be64cc421af593310867f658c4219f596310875e538c421d754e31086ee628c421bb58a3108776518c4219fd953108776514c4219fd94310867e650c4219f594310867c650c421d794c310875d530c421bb98831086ed620c421f54c431086be64c8421af59321087ae64c8421eb59321086ed6288421db94a21087765488421dd15221087775388421dd54e21086f56288421dd94a21087e652884219fd9521086ef6548421dbd95210866f6548421bbd85210876e5148421f990521087e54148421f9cc521087e43148421bdd95210877765484219dd9521087765448421dd15121087775348421dd54d21086f76248421f9d8921087765248421f994921087e64248421f950921087e73248421f90c9210877b50940219f992500867d64940219f98e500867d63940219fd91500867c64540219fd8d500867c6354021dbc8550087762154021db48550087752154021af99050086bd6414021b798c50086dd6314021de540500875f5394f40bd98653d02f56194f409f98a53d027d6294f409f98653d03766194f409d98653d027d6194f40dd58653d02756194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d035e53d0f40d754f43d02fa60d0f40be58343d033e53d0f40e794f43d039d53d0f40af58b43d02bd61d0f40af98343d03ba60d0f40ee58343d02f66190f40bd58643d02bf6550f40cfd9543d039f6350f40e7d4d43d033e5350f40e714d43d02bf6250f40afd8543d02bc6050f40d794c43d035d5310f40e750c43d02fa6010f40be58043d036f5294b40bd98652d02f56194b409f98e52d027d6394b409f98652d03766194b409d98652d027d6194b40dd58652d02756194b409fd8d52d027c6354b40cfd0d52d033d4354b409fd8552d027c6154b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d02bd63d0b40cf54f42d033e52d0b40eb94b42d03ad52d0b40af58742d02be60d0b40ee98342d03b960d0b40bd98642d02f56190b40afd9542d033f6550b40afd8d42d033d5350b40ebd8942d03af5250b40cf94942d03ac5250b40afd8542d02bc6050b40db94842d036d5210b40eb50842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40af99332d02bd64ccb409fd963
  | 31 => 0x4c5219f595314867c654c521d7d4d314875c534c521bbd8931486ec624c521bd1953148774654c5219d19531486f6644c521bd1913148776544c521dd15131487d7634c521f5d4d3148776534c521dd14d31487d4534c521d514d31487e7624c521bd18931487e4624c521b918931486f7604c5219f99431486f6610c521af99321486bd64c8521bd99321487b664c8521ad99321487b564c8521bd19321486f763c8521bd58f21486f560c8521f9d4621487e74188521f910621487e63188521f94c621486ed60885219f993504867d64d41219f98f504867d63d4121dd8c7504877531d4121ded4250486bf6454121af19150486df6354121b718d50486be6414121af59050486de6314121b758c504877950141219f990504873e64141218f990504867d6414121cf590504863d64141219f98c504875e63141219798c504867d6314121d758c504865d6314121ddd04504877441141219f98f540867d63d50219f98b540876e62d50219f987540877661d50219d987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530867e6214c21db988530867e6114c21dd98453086766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd97430867e65d0c219f597430867c65d0c21cf953430873d54d0c21bb98b43086ed62d0c21bd98743086f561d0c219fd96430867e6590c219f596430867c6590c21d794e430875d5390c21bd98643086f56190c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21d794d430875d5350c219fd94430867e6510c219f594430867c6510c219f992520873e64948218f992520867d6494821cf592520863d64948219f98e520867d63948219f597420873f54d0821cf153420867f65908219f596420873e5490821cf55242086f66190821bd586420867f6550821cfd51420873c54508219fd94420867d6510821cf950420873d5410821bd98442086f561108219f59732086
  | 32 => 0x1b798c50886dd6314221de540508867e63d51219f58f544877561d51219f983544867d60d5121cfd5254486de6395121b758e544867e64951219f98e544875e63951219798e544867d6395121d758e544865d63951219f58a544876d62951219f586544877561951219f982544867d6095121cfd91544867f63551219f18d544867f6255121dbd89544867f6155121ddd85544867f60551219f181544867e6515121cf550544873e64151219f98c544867d63151219f980544867d60151219f993534867d64d4d219f983534867d60d4d21af99253486bd6494d21d7d4e534867e6494d21cf992534863e6494d219f592534873d6494d218f592534867e6394d219f58a534876d6294d219f58653487756194d219f982534867d6094d219fd91534867c6454d21d7d8d534867f6254d21dbd89534867f6154d21ddd85534867f6054d219f181534867e6514d21d754c534867e6414d219f590534875e6314d21dd584534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434873f54d0d21cf153434867f6590d219f996434867d6590d219f196434875f5390d21d714e43486f66190d21bd586434867f6550d219f995434867d6550d219f195434873f5450d21cf151434875f5350d21d714d43486ef6250d21bb18943486f76150d21bd185434867f6510d219f994434867d6510d219f19443486ee6210d21bb58843486f66110d21bd584434867e65d0921cfd53424873c54d0921bd98742486f561d09219f99642486f661909219f195424873f5450921cf15142486f76150921bd185424867e6510921eb508424867e65cc921d7d4f324875c53cc921bd98732486f561cc9219f996324867c654c921d7d4d324875c534c921bdd8532486f4614c9219f99432486be640c921af59032487cd320c921bd98432486fa600c921be580324867e65d0521cfd53414873c54d0521bb98b41486ed62d0521bd997414877665d05219d997414877754d0521edd53414877554d0521ed15341486f563d0521ddd4f414877553d0521bd98b41487e662d0521b998b41487e562d0521bd583414867e6590521cf952414873d5490521bd986414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f994414873e5410521cf55041487b54110521bd99441487766510521bd99041487b66410521ddd5041487b65410521dd55041487b55410521cd55041486f56310521ddd4c41487755310521edd0c41487b54310521bd98841487b74210521ed50841486f560105219f99731486be64cc521af593314875f53cc521d714f31486ee62cc521bb58b314867e658c521bd9963148776658c521bd99231486f4648c521dd9523148774548c521bd58e3148776538c521dd14e31486f6628c521bd582314867f65
  | 33 => 0x82548867d6095221cfd91548867f63552219f18d548877461552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d6015221af99353886bd64d4e219f993538873e64d4e218f993538867d64d4e21cf593538863d64d4e21db58b538877661d4e219f983538867d60d4e21af99253886bd6494e21d7d4e538867e6494e21cf992538863e6494e219f592538873d6494e218f59253887766194e219f982538867d6094e219fd91538867c6454e21d7d8d538867f6054e219f181538875d5314e219f990538867d6414e21d798c538876d6214e21dd984538867e6014e219f580538867f65d0e219f997438867d65d0e219f197438873f54d0e21cf153438875e53d0e21d754f43886ee62d0e21bb58b438867f6590e219f996438867d6590e219f196438873e5490e21cf55243886f66190e21bd586438867f6550e219f995438867d6550e219f195438873f5450e21cf15143886f76150e21bd185438867f6510e219f994438867d6510e219f194438873e5410e21cf550438875e5310e21d754c43886f66110e21bd584438873e54d0a21cf55342886f661d0a21bd58742886f56190a21cf951428873d5450a21bdd8542886f46150a21d794f328875d53cca21bd98732886f561cca21d794d328875d534ca21bdd8532886f4614ca21af99032886bd640ca21f34c832886f5610ca21be98032886f9600ca21bd597418877565d0621ddd53418877554d0621bd58f418877753d0621dd54f41886f662d0621bd583418873e5490621cf55241886ee6290621bb58a418873e5410621cf55041886ee6210621bb58841887b54110621bd59441887756510621ed99041887775410621ed95041887755410621ed55041887355410621bd58c41887775310621dd54c41887b74310621ed50c41886f66210621f998841887e56210621edd0841887b54210621bd58041886be64cc621af593318875e538c621d754e31886ee628c621bb58a31886f5658c621dd59631886f6648c621bd1923188776548c621dd1523188776538c621f594e31887d5538c621dd14e31886f6628c621f998a31887e5628c621bd58231886f7654c621ddd9531886f6644c621bd1913188776544c621dd15131887d7634c621dd94d3188774534c621bd18931886f7604c621d794c318875d530c621bb98831886ed620c621af99321886bd64c8621bb597218876d65c8621eb99321887ad64c8621bd597218877565c8621bd99321887b664c8621ad99321887b564c8621bd19321886f763c8621bd58f21886f560c8621ded42508867e64942219f592508867e63942219f58e50887774194221dd106508867f64542219f191508867f63542219f18d50887763154221dd4c5508876f2154221af99050886bd641422
  | 34 => 0xc873d6095321cf18254c873f64553219fd8d54c867c63553219fd8154c867c6055321cfd9554c873f6355321cf98d54c873d6355321cf18d54c873e6255321cf18954c873f6155321cf58554c873f6055321cf98154c873d6055321cf18154c873d5415321cf99054c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c86be64d4f21af59353c873e54d4f21cf55353c867e64d4f21cf99353c863e64d4f219f59353c873d64d4f218f59353c876e62d4f21dd58753c867e60d4f219f58353c873e5494f21cf55253c875f5394f219f99253c867d6494f219f98253c867d6094f21cf95153c873d5454f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c86be6414f21af59053c873e5414f21cf55053c875d5314f21be98053c86f96014f219f99053c873e6414f218f99053c867d6414f21cf59053c863d6414f21d798c53c876e6214f21dd58453c867e6014f21de98053c867a6014f219f58053c87796014f219e58053c867f65d0f219f99743c867d65d0f219f19743c873e54d0f21cf55343c86f661d0f21bd58743c867f6590f219f99643c867d6590f219f19643c873e5490f21cf55243c86f66190f21bd58643c867f6550f219f99543c867d6550f219f19543c873e5450f21cf55143c86ef6250f21bb18943c867f6510f219f99443c867d6510f219f19443c873e5410f21cf55043c86ee6210f21bb58843c873e54d0b21cf55342c873e5490b21cf55242c86f66190b21bd58642c873e5450b21cf55142c873e5410b21cf55042c87ad4210b21bd98442c86f56110b21cf95332c873d54ccb21cf95232c873d548cb21d794e32c875d538cb21bd98632c86f5618cb21cf95132c873d544cb21af99032c86bd640cb21cf95032c873d540cb21d794c32c875d530cb21f34c832c86f6610cb21bd58432c86fa600cb21be58032c873e54d0721cf55341c86ee62d0721bb58b41c873e5490721cf55241c873e5450721cf55141c86ef6250721bb18941c873e5410721cf55041c87b54110721af99331c86bd64cc721cf95331c873d54cc721d794f31c875d53cc721bb98b31c86ed62cc721cf95231c873d548c721cf95131c873d544c721d794d31c875d534c721bbd8931c86ec624c721cf95031c873d540c721f54c431c86be64d4321af59350c873e54d4321cf55350c873e5494321cf55250c877b50943219f99250c867d64943219f98e50c867d6394321cf95150c873d54543219fd9150c867c64543219fd8d50c867c6354321af99050c86bd6414321cf95050c873d5414321b798c50c86dd6314321de54050c86de63d5221b758f548867e63d5221d798f548865e63d52219f58f548875d63d52219758f548876d62d5221dd987548867e60d52219f583548873f54952219f98e548867d63952219f9
  | 35 => 0xe63d5031d798f540c67e62d50319f58b540c67e61d5031dd987540c67661d50319f983540c67d60d50319f596540c73f54950319f98a540c67d62950319f982540c67d6095031cfd91540c67f62550319f189540c67f60550319f181540c73d5415031bb988540c6ed6215031be980540c6f960150319f990540c73e64150319f98c540c75e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f992530c73e6494c318f992530c67d6494c31cf592530c63d6494c319f597430c73f54d0c31cf153430c67f6590c319f596430c73e5490c31cf552430c6f66190c31bd586430c67f6550c31cfd51430c73c5450c319fd94430c67d6510c31cf950430c73d5410c31bd984430c6f56110c31dbd4a520c67e64948319f592520c67e60948319f582520c67f64548319f191520c67f60548319f181520c6be6414831af590520c76d5214831be980520c6f960148319fd97420c67e65d08319f597420c73e54d0831cf553420c6de63d0831b758f420c6f661d0831bd587420c67f65908319f996420c67d6590831db94a420c76d5290831bd986420c6f561908319fd95420c67d65508319f195420c73e5450831cf551420c76e5250831db549420c67f65108319f994420c67d6510831db94b320c76d52cc831bd987320c6f561cc8319f596320c67f654c831af990320c6bd640c831db948320c76d520c831f34c8320c6f6610c831bd584320c6fa600c831be580320c67e64944319f592510c67d65d0431dd947410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c67f65504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431dd944410c7b54110431af993310c6bd64cc431e7993310c79d64cc431b758e310c75e538c431dd952310c774548c431bd58e310c776538c431f594e310c775528c4319fd95310c6df654c431d7d95310c65f654c431b7d85310c75e514c431f5905310c7d5414c431bdd95310c777654c4319dd95310c776544c431dd151310c6f7634c431f5d8d310c776534c431f594d310c7d6434c431f550d310c775524c431f58c9310c7d4324c431ded42500c67e64940319f592500c67e62940319f58a500c67f64540319f191500c67f62540319f189500c75f3154031dd8c5500c75d3154031dd4c5500c6be6414031af590500c6ee6214031bb588500c77950140319f98f54c867d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f6395321cf98e54c873d6395321cf18e54c873e6295321cf18a54c873f6195321cf58654c873f6095321cf98254
  | 36 => 0x42319f58a508c7774194231dd106508c67f64542319f191508c67f62542319f189508c75f3154231af990508c6bd6414231bb988508c6ed6214231de540508c67e62d51319f58b544c77561d51319f983544c67d60d5131cfd52544c6ee6295131bb58a544c67e64951319f58e544c75d63951319f98a544c76e62951319b98a544c67d6295131db58a544c66d62951319f586544c77561951319f982544c67d6095131cfd91544c67f6355131d7d8d544c67f62551319f189544c67f6155131ddd85544c67f60551319f181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6f661d0d31bd587434c67e6590d31bd986434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d319f994434c79d4310d319f993524c67d64d49319f983524c67d60d4931af992524c6bd6494931dbd4a524c76d52149319f990524c67d6414931dd584524c67e60149319f580524c67e65d09319f597424c67c65d0931cfd53424c73c54d09319f996424c67d65909319f196424c76f5290931db14a424c6f66190931bd586424c67f65509319f995424c67c6550931cfd51424c73c5450931b7d8d424c6dc6350931dbd49424c76c5250931bdd85424c6f461509319f994424c67d65109319f194424c6de6310931b758c424c6f66110931bd584424c67e65cc931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c9319f994324c6be640c931af590324c7cd320c931bd984324c6fa600c931be580324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d0531bd997414c77665d05319d997414c77754d0531edd53414c77554d0531ed153414c6f663d0531f598f414c6d663d0531f558f414c6f562d0531ddd4b414c6f560d05319f996414c73e5490531cf552414c6f661905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c67e6510531cf950414c73d5410531ed504414c6f66510531dd994414c6f66410531ed990414c7775410531ed950414c7755410531ed550414c7355410531bd98c414c7b74310531ed50c414c6f56210531ddd48414c7b74210531ed508414c6f56010531af993314c6bd64cc531bd993314c7b664cc531ad993314c7b564cc531bd193314c6f562cc531bd583314c7d7518c531f5d06314c7d4418c531b7582314c67e64d41319f593504c67e62d41319f58b504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131af990504c6bd6414131bb988504c6ed6214131de540504c67e6414131cf990504c63e64141319f590504c73d64141318f590504c67e6214131db988504c66e62141319f588504c76d62141319b588504c7774114131dd104504c67
  | 37 => 0xcf55332cc76e52ccb31db54b32cc6f661ccb31bd58732cc73e548cb31cf55232cc73e544cb31cf55132cc6be640cb31af59032cc73e540cb31cf55032cc76e520cb31db54832cc7cd320cb31bd98432cc6f5610cb31be98032cc6f9600cb31cf95341cc73d54d0731b798f41cc6dd63d0731cf95241cc73d5490731cf95141cc73d5450731b7d8d41cc6dc6350731cf95041cc73d5410731ed50441cc6be64d4331af59350cc73e54d4331cf55350cc73e5494331cf55250cc77b50943319f99250cc67d64943319f98a50cc67d6294331cf95150cc73d54543319fd9150cc67c64543319fd8950cc67c6254331af99050cc6bd6414331cf95050cc73d5414331bb98850cc6ed6214331de54050cc6ee62d5231bb58b548c75d63d52319f98b548c76e62d52319b98b548c67d62d5231db58b548c66d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c67f62552319f189548c77461552319fd81548c67c6055231cf550548c73e6415231d758c548c67e62152319f588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31bd586438c73e5450e31cf551438c6f76150e31bd185438c6be64d4a31af593528c6be6494a31af592528c76f5294a319f992528c73e6494a318f992528c67d6494a31cf592528c63d6494a31dd986528c67e6094a319f582528c67f6454a319f191528c67f6054a319f181528c76d5214a319fd97428c67e65d0a319f597428c73f54d0a31cf153428c6de63d0a31b758f428c76e52d0a31db54b428c67f6590a319f996428c67d6590a31cf952428c73d5490a31bd986428c6f56190a319fd95428c67d6550a319f195428c73f5450a31cf151428c6f76150a31bd185428c67f6510a319f994428c67d6510a31cf950428c73d5410a31db948428c76d5210a31bd984428c6f56110a31db94a328c76d528ca31bd986328c6f5618ca31db949328c76d524ca31bdd85328c6f4614ca31af990328c6bd640ca31f34c8328c6f5610ca31be980328c6f9600ca31bd597418c77565d0631ddd53418c77554d0631bd98f418c6f562d0631dd54b418c6f560d0631cf952418c73d5490631b798e418c6dd6390631cf950418c73d5410631b798c418c6dd6310631ed504418c6f56510631dd594418c7b66410631ddd50418c7b65410631dd550418c7b55410631cd550418c6f66310631f598c418c7d56310631edd0c418c7b54310631bd588418c7755210631edd08418c7b54210631bd580418c6be64cc631af593318c6dd65cc631d7597318c79e64cc631e7593318c6f565cc631dd597318c6f664cc631ed993318c6b664cc631ed593318c6f464cc631bd58b318c6f560cc631ded42508c67e64942319f592508c67e629
  | 38 => 0xa51106bd63d0441af58b41106be60d0441af592411073e5490441bd59241106b56490441dd95241107b65490441bd58e41107b74390441ed50e41106f56290441edd0a41107b54290441bd982411067f6550441afd95411073f65504418fd9541106bf6350441afd8941106bf6150441cf94541106bc6050441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141106f76350441edd0d41107b64350441ed50d41107b44350441bdd8941107b74250441ed90941107b54250441ed10941106f46050441edd9541106b76550441cdd9541107b76350441add8d41107b66350441ed58d41107b46350441edd4d41107b65350441ed54d41107b45350441edd8941106b76250441ed98941107b56250441ed18941107b75250441ed94941107b55250441ed14941107b73250441ed8c941107b53250441ed0c941107b76050441ed98141107b56050441ed18141106b46050441ed50750107b54194041ded42501067e63940419f58e501067e62940419f58a50107b541540419fd8d501067c6354041cfd0d501073d43540419fd89501067c6254041cfd09501073d4254041cfd0550107764154041cf50550107754154041cd50550106de6314041b758c50106ee6214041bb58850107b54114041de540501075e63d53319f98b54cc67d62d5331dd58754cc67e60d53319f58354cc73f54953319f98a54cc67d62953319f98254cc67d6095331cf98e54cc73c6395331cfd8a54cc73e6295331cf58a54cc73c6295331cfd8654cc73d6195331cfd8254cc73e6095331cf58254cc73c6095331cfd9154cc67f62553319f18954cc67f60553319f18154cc73f6555331cf98d54cc73c6355331cfd8954cc73e6255331cf58954cc73c6255331cfd8554cc73d6155331cfd8154cc73e6055331cf58154cc73c6055331cf55054cc73e6415331d798c54cc67e62153319f58854cc77561153319f98054cc67d6015331cf95343cc73d54d0f31cf95243cc73d5490f31bd98643cc6f56190f31cf95143cc73d5450f31cf95043cc73d5410f31e750c43cc6f66110f31bd58443cc6be64d4b31af59352cc73e54d4b31cf55352cc73e5494b31cf55252cc76f5294b319f99252cc67d6494b319f98252cc67d6094b31cf95152cc73d5454b319fd9152cc67c6454b319fd8152cc67c6054b31af99052cc6bd6414b31cf95052cc73d5414b31db54852cc6fa6014b31be58052cc67f65d0b319f99742cc67d65d0b31cf95342cc73d54d0b31bd98742cc6f561d0b319fd9642cc67e6590b319f59642cc73e5490b31cf55242cc6f66190b31bd58642cc67f6550b319f59542cc67c6550b31cf95142cc73d5450b31b7d8d42cc6dc6350b319fd9442cc67e6510b319f59442cc73e5410b31cf55042cc6de6310b31b758c42cc73e54ccb31
  | 39 => 0x6f76150d41bd185435067e6510d41e750c435067e63d49419f58f525067e60d49419f583525076f5294941db548525067e63149419f58c525067e60149419f580525067e65d0941dbd4a425076c5290941bd98642506f56190941dbd49425076c5250941bdd8542506f461509419f99442507ad42109419f997325067d65cc9419f197325067e658c9419f596325067c658c9419fd95325067e654c9419f19532506bf644c941af19132506f7614c941bd185325067e650c9419f594325067c650c941af99032506bd640c941f34c832506f6610c941bd58432506fa600c941be580325077753d0541ddd4b41506f560d0541cfd4e415073f5290541edd4641506bd60905419f98f505067d63d41419f98b505067d62d4141ded4250506de6314141b758c50506ee6214141bb588505077950141419f98c505075e63141419798c505067d6314141d758c505065d63141419f988505076e62141419b988505067d6214141db588505066d6214141ddd04505073e4114141d7d4e531067e6294c419f58a53107766194c419f982531067d6094c419fd89531067c6254c419fd81531067c6054c41d754c53106ee6214c41bb58853106fa6014c41be580531075e53d0c41d754f43106f661d0c41bd587431073e53d0c41e794f431079d53d0c41af58b43107b661d0c41af58743107b561d0c41ad58743106be60d0c419f59643106bd6490c41bd586431067f6550c41afd95431073f6550c41e7d8d431073e5350c41afd8943106bf6150c41ed98543107b56150c41af18143106be6410c41d794c431075d5310c41bd98443106f56110c41dbd4a521067e63948419f58e521077661948419f982521067d60948419fd8d521067c6354841cfd0d521073d43548419fd81521067c6054841b798c52106dd6314841db54852106fa6014841be580521076e52d0841db54b42106f661d0841bd58742106bd63d0841cf54f421073e52d0841eb94b42107ad52d0841ed98742106bd61d0841ed58742106b561d0841af983421067d6590841af59242106f561908419fd9542106bf6550841cfd9542106bf6350841cf54d42107af6250841cf94942106bf6150841ed98542107b56150841af18142106be6410841db948421076d5210841bd98442106f561108419fd97321067e65cc8419f59732106be64cc841af593321075e53cc841d754f32106f661cc841bd587321067f658c8419f996321067d658c841af99232106bd648c841db94a321076d528c841bd98632106f5618c8419fd95321067d654c8419f19532106be644c841af591321075e534c841d754d321076e524c841db549321067f650c8419f994321067d650c841af99032106bd640c841f34c832106f6610c841bd58432106fa600c841be580321073f4394441cf50e511073f4294441cf50
  | 40 => 0x5214b41db94b42d076d52d0b41bd98742d06f561d0b41bd98642d076e5210b41db54842d07ad4210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d076e52ccb41db54b32d06f661ccb41bd58732d067f658cb419f99632d067d658cb41d794e32d075d538cb41bd98632d06f5618cb419fd9532d067d654cb419f19532d06bf644cb41af19132d067f650cb419f99432d067d650cb41af99032d06bd640cb41d794c32d075d530cb41db94832d076d520cb41f34c832d06f6610cb41bd58432d06fa600cb41be58032d077b50943419f98e50d067d63943419f98a50d067d62943419fd8d50d067c63543419fd8950d067c6254341b798c50d06dd6314341bb98850d06ed6214341de54050d06ee62d4e41bb58b539075f5394e419f98a539067d6294e419f982539067d6094e419fd89539067c6254e419fd81539067c6054e41d754c53906bd65d0e41cf597439073e53d0e41af58b43906bd61d0e41af983439075e5390e41d754e43906f66190e41bd586439075e5350e41d754d43906f76150e41bd185439079f6350e41cf94d439079e5350e41c794d439079d5350e41afd8943906bf6150e41edd8543907b46150e41af18143906de63d4a41b758f529076f5294a419f98e529067d6394a419f982529067d6094a419fd8d529067c6354a41cfd0d529073d4354a419fd81529067c6054a41db54852906bd65d0a41cf59742906bd63d0a41cf54f429073e52d0a41af58742906be60d0a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a41afd8d429073d5350a41ebd89429073e5250a41eb949429072e5250a41eb54942906bf6150a41edd8542907b46150a41af181429067f65cca419f997329067d65cca41af99332906bd64cca41db94b329076d52cca419fd96329067e658ca419f59632906be648ca41af592329075e538ca41d754e329067f654ca419f595329067c654ca41af99132906bd644ca41bdd8532906f4614ca419fd94329067e650ca419f59432906be640ca41af590329075e530ca41d754c329076e520ca41db54832907cd320ca41bd98432906f5610ca41be98032906f9600ca41af597419073d65d0641af58f41906bd62d0641af98341906f565d0641dd597419077553d0641dd54b41906f560d0641ded42509067e63942419f58e509067e62942419f58a509077741942419fd8d509067c6354241cfd0d509073d43542419fd89509067c6254241cfd09509073d4254241cfd0550906de6314241b758c50906ee6214241bb588509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e535075d5314d419f988535067d6214d419f980535067d6014d419f997435075f5390d41d714e43506f66190d41bd586435075f5350d41d714d435
  | 41 => 0x432ddd95510cb775454432dd951510cbb65454432cd951510cb755454432ed551510cb355454432dd151510cbd73254432f98c9510cbd53254432f94c9510cbc53254432ddd91510cb766454432dd591510cb746454432dd98d510cb774354432dd90d510cb754354432dd10d510cb766254432ddd09510cb764254432dd509510cb744254432ddcc9510cb763254432dd4c9510cb743254432ddd81510cb766054432dd581510cb746054432af990510cabd6414432cf950510cb3d5414432f34c8510caf66114432dd544510cafa6014432be580510cabe64d4032af593500cb3e54d4032cf553500cbcd32d4032bd987500caf561d4032dd947500cb7551d4032cf952500cb3d5494032f34ca500cb765194032dd546500cb7b50940329f992500ca7d64940329f986500ca7d6194032ded52500cb7a5494032ee952500cb3a5494032de552500cbb95494032ce552500cb785494032f6cca500cbea3294032f64ca500cbe93294032f24ca500cb7b5194032de946500cbf25194032dc946500cb795194032fc546500cb715194032de146500cb7b6494032de992500cb796494032de192500cb786394032ded0e500cb7a4394032de50e500cb784394032de18a500cb7b4294032de90a500cb794294032de10a500cb7b3294032de8ca500cb793294032ded86500cb7a6194032de586500cb786194032cf951500cb3d5454032f34c9500cb765154032dd545500ca7f64540329f191500cb5f3254032db8c9500cb5d3254032db4c9500cb4d32540329fd85500ca7c6154032ded95500cb7b5454032de951500cbba5454032ce951500cb795454032ee551500cb395454032de151500cbdb3254032fa8c9500cbd93254032fa4c9500cbc93254032ded45500cb7a5154032fc945500cb725154032de545500cbf15154032dc545500cb785154032ded91500cb7a6454032de591500cb786454032de98d500cb7b4354032de90d500cb794354032de10d500cb7a6254032ded09500cb7a4254032de509500cb784254032decc9500cb5b3254032de8c9500cb6a3254032de4c9500cb593254032da4c9500cb493254032de0c9500cb7b6154032de985500cb796154032de185500cabe6414032af590500cb3e5414032cf550500cbcd3214032bd984500caf56114032dd944500cb755114032be980500cb795014032bb98b53d06ed62d4f41d7d4e53d067e6294f419f58a53d07756194f419f98253d067d6094f419fd8953d067c6254f419fd8153d067c6054f41d754c53d075e53d0f41d754f43d06f661d0f41bd58743d06f66190f41d794c43d075d5310f41e750c43d06f66110f41bd58443d06de63d4b41b758f52d076f5294b419f98e52d067d6394b41dd58652d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d076d
  | 42 => 0xf586540cb3c6195032cfd82540cb3e6095032cf582540cb3c6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3f6555032cf98d540cb3c6355032cf989540cb3c6255032cf0c9540cb3f6155032cf985540cb3d6155032cf185540cb3f6055032cf981540cb3d6055032cf181540cabe6415032cf550540caf66115032bd584540cafa6015032be580540ca7e6415032cf990540ca3e64150329f98c540cb5e63150329f988540cb6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a60150329e980540ca7d6015032de580540ca7960150329f992530ca7d6494c329f597430cb3e54d0c32cf553430ca7f6590c329f596430cb3e5490c32cf552430caee6290c32bb58a430caf66190c32bd586430ca7f6550c32cf951430cb3d5450c329fd94430ca7d6510c32cf950430cb3d5410c32e750c430caee6210c32bb588430ca7e64948329f592520ca7d65d0832cf953420cb3d54d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd6390832bd986420caf561908329fd95420cb3e5450832cf551420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cbad4210832cf953320cb3d54cc832e7953320cb9d54cc832cf952320cb3d548c832b758e320cb5e538c832eb952320cbad548c832bb58e320cacd638c832db94e320cbce538c8329fd95320cb3e544c832cf551320cadf654c832d7d95320ca5f654c832e7951320cb9d544c832b7d89320cb5e524c832f3d09320cbce424c832f3509320cbcc424c832bbd95320cb6f654c8329bd95320cbae544c832eb551320caef634c832f3d8d320cb6e534c832f394d320cbcf434c832f390d320cbcd434c832f310d320cbcf654c832b3d95320cb4f654c832f3d91320cbce644c832f3591320cbcc644c832f3d51320cbce544c832e3951320cbcd544c832e3551320cbcc544c832f3d85320cbce614c832f3585320cbcc614c832f3d81320cbce604c832f3581320cbcc604c832af993510cabd64d4432cf953510cb3d54d4432f34cb510cafa60d4432be583510cb3e5494432cf552510cbcd3294432ddd46510ca7e64944329f592510ca7e60944329f582510cb775494432dd952510cbb65494432cd952510cb755494432ed552510cb355494432dd152510cbd73294432f98ca510cbd53294432f94ca510cbc53294432ddd92510cb766494432dd592510cb746494432dd18e510cb774394432dd90e510cb754394432dd10e510cb746294432ddd0a510cb764294432dd50a510cb744294432ddcca510cb763294432dd4ca510cb776094432dd982510cb756094432dd182510cb3e5454432cf551510cbcd32544329fd91510ca7c64544329fd81510ca7c6054
  | 43 => 0x548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438caf66190e32bd586438cb3e5450e32cf551438caef6250e32bb189438cb9d4310e32cfd53428cb3c54d0a32cf952428cb3d5490a32b798e428cadd6390a32bd986428caf56190a32cfd51428cb3c5450a32cf950428cb3d5410a32b798c428cadd6310a32b7597328cb5d65cca32bb597328cb6d65cca32bb583328cabe64d4632af593518cb7751946329f992518ca7d64946329f982518ca7d60946329fd91518ca7c64546329fd81518ca7c6054632dd544518cb7b50942329f992508ca7d64942329f986508ca7d61942329fd91508ca7c6454232d7cc9508ca7f61542329f185508cabe6414232af590508caf66114232bd584508cb795014232bd987544caf561d51329f987544cb7661d51329d987544ca7d61d5132dd587544ca7561d51329f983544ca7d60d5132cfd52544caf66195132bd586544ca7e64951329f58e544cb5d63951329f58a544cb6d62951329f986544cb7661951329d986544ca7d6195132dd586544ca7561951329f982544ca7d6095132cfd91544ca7f6355132d7d8d544ca7f6255132dbd89544ca7f61551329f185544ca7f60551329f181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d60151329f997434cb3f54d0d32cf153434caee62d0d32bb58b434ca7e6590d32bd986434caf56190d329f195434cb3f5450d32cf151434caef6250d32bb189434ca7e6510d329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e6590932bd986424caf561909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932bb583324cbcf528c932b7582324cabe64d4532af593514ca7e64d4532cf993514ca3e64d45329f593514cb3d64d45328f593514ca7e60d45329f583514cabe6494532af592514cb775194532dd544514ca7e64145329f590514ca7e60145329f580514ca7e64d41329f593504ca7e61d41329f587504cb7b5094132afd91504cabc6454132bdd85504caf46154132af990504cabd6414132bd984504caf56114132de540504ca7e6414132cf990504ca3e64141329f590504cb3d64141328f590504ca7e6114132dd984504ca7661141329f584504cb7561141329d584504caf661d5032bd587540cafa60d5032be583540ca7e63d5032d798f540ca7e62d5032db98b540ca7e61d5032dd987540ca7661d50329f587540cb7561d50329d587540ca7e60d5032de983540ca7a60d50329f583540cb7960d50329e583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540ca3d6595032cf98e540cb3c6395032cf98a540cb3c6295032cfd86540cb3e6195032c
  | 44 => 0xadc6354142bdd855050af46154142b798c5050add6314142bd9845050af56114142de5405050a7e6314142d798c5050a5e63141429f58c5050b5d63141429758c5050a7e6114142dd9845050a7661141429f5845050b7561141429d5845050b5f5394c429f9865310a7d6194c429f9825310a7d6094c429fd855310a7c6154c429fd815310a7c6054c42d754c5310af66114c42bd5845310afa6014c42be5805310b3e54d0c42d794f4310b5d53d0c42bb98b4310aed62d0c429f5964310af66190c42bd5864310a7f6550c42cf9514310b5e5310c42d754c4310b9d4310c42bb9884310aed6210c42dd9865210b756194842cf54f4210abd6490842cf9524210af66190842bd5864210aed6490842db9524210bae5490842f99864210be561908429fd954210abf6550842cfd954210a3f6550842cf54d4210abf6250842cf9494210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842eb90d4210bac4350842ddd465110a7e63944429f58e5110b3f4294442cf50a5110a7e60944429f5825110a7f63544429f18d5110a7f60544429f1815110ade6314442b758c5110b755114442be9805110af96014442ded425010a7e63940429f58e5010a7e61940429f5865010a7f63540429f18d5010b3f4254042db9095010b3d4254042db5095010a7f61540429f1855010ade6314042b758c5010af66114042bd5845010b795014042bd98754ccaf561d5332d798f54ccb6d62d53329f98754ccb7661d53329d98754cca7d61d5332dd58754cca7561d53329f98354cca7d60d5332cfd5254cca7e61953329f58654cca7e60953329f58254ccb3f64553329fd8554cca7c61553329fd8154cca7c6055332cf55054ccb3e6415332d798c54ccb6d62153329f98454cca7d61153329f98054cca7d6015332cfd5343ccb3c54d0f32cf95243ccb3d5490f32bb98a43ccaed6290f32bd98643ccaf56190f32cfd5143ccb3c5450f32cf95043ccb3d5410f32bb98843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32bd98642ccaf56190b32cf95142ccb3d5450b32b7d8d42ccadc6350b32eb50842ccabe64d4732af59351ccb7751947329f99251cca7d64947329f98251cca7d60947329fd9151cca7c64547329fd8151cca7c6054732dd54451ccb7b50943329f99250cca7d64943329f98650cca7d61943329fd9150cca7c64543329fd8550cca7c6154332af99050ccabd6414332bd98450ccaf56114332de54050ccaf661d5232bd587548cb5d63d5232db98b548ca7e61d5232dd987548ca7661d52329f587548cb7561d52329d587548ca7e60d52329f583548cb3f54952329f986548ca7d61952329f982548ca7d6095232cfd91548ca7f61552329f185548ca7f60552329f181548cb3d5415232cf990
  | 45 => 0x394742cfd0e51d0b3d43947429f98251d0a7d60947429fd8d51d0a7c63547429fd8151d0a7c6054742dd54451d0b7b50943429f98e50d0a7d63943429f98650d0a7d61943429fd8d50d0a7c6354342cfd0d50d0b3d43543429fd8550d0a7c6154342b798c50d0add6314342bd98450d0af56114342de54050d0af661d4e42bd5875390b5f5394e429f9865390a7d6194e429f9825390a7d6094e429fd855390a7c6154e429fd815390a7c6054e42d754c5390af66114e42bd5845390afa6014e42be5805390b5e5390e42d754e4390aee6290e42bb58a4390af66190e42bd5864390b5e5350e42d754d4390aef6250e42bb1894390b9d4310e42af5974290b3d65d0a42cf54f4290aed65d0a42db5974290aed60d0a42ddd465190a7e63946429f58e5190b3f42946429f9825190a7d6094642ddd4e5190b765394642dd54e5190b745394642edd0a5190be74294642ddd925190b776394642dd98e5190b756394642dd18e5190b774394642dd90e5190b754394642dd10e5190b746294642ddd0a5190b374294642ddd825190b766094642dd5825190b7460946429fd8d5190a7c63546429fd815190a7c6054642ddd955190b775354642dd94d5190b755354642dd14d5190bb74254642f9d095190b756454642ddd8d5190b766354642dd58d5190b746354642ddd0d5190b764354642dd50d5190b744354642dd9895190b774254642ddd815190b766054642dd5815190b746054642dd5445190af661d4242bd5875090b7651d4242dd5475090b765194242dd5465090b7b50942429f98e5090a7d63942429f9865090a7d6194242dd9455090b7551542429fd8d5090a7c6354242cfd095090a7f61542429f1855090ade6314242b758c5090af66114242bd5845090b765114242dd5445090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af66194d42bd5865350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350abe65d0d42cf9974350b3c53d0d42af98b4350abe61d0d42af5834350abd6490d42d7d4e4350b5c5390d42bb98a4350aed6290d42bd9864350af56190d42d7d4d4350b5c5350d42bbd894350aec6250d42e7d8d4350b9f5350d42cf14d4350b9c5350d42c714d4350baf6250d42af1894350bac6250d42ab1894350abc6150d42afd814350a7e6510d42af9904350baf43d0942eb50f4250aed60d0942bd9864250af56190942af58e4250baf5290942af9864250bb66190942ad9864250bb56190942af5824250a7e63d45429f58f5150a7e60d45429f5835150ade6394542b758e5150b775194542dd5445150a7e63145429f58c5150b3f4314542cf50c5150a7e60145429f5805150a7e63d41429f58f5050b3f43d4142cf50f5050a7e61d41429f5875050b7b5094142b7d8d5050
  | 46 => 0x43ddd895190f766254643dd5895190f746254643ddd815190f766054643dd5815190f746054643dd5445190ef661d4243bd5875090f7651d4243dd5475090f765194243dd5465090f7b50942439f98a5090e7d62942439f9865090e7d6194243dd9455090f755154243cfd0d5090e7f62542439f1895090e7f61542439f1855090eee6214243bb5885090ef66114243bd5845090f765114243dd5445090f795014243b75834350ef66190d43bd5864350f9f5390d43af58a4350ebe6190d43ed9864350eb66190d43ed5864350ebd6090d439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250ef66194943bd5865250f6d52149439f9845250e7d61149439f9805250e7d60149439f98b5150e7d62d45439f9835150e7d60d4543bb98a5150eed6294543ddd465150f7551145439f9885150e7d62145439f9805150e7d60145439f98b5050e7d62d41439f9875050e7d61d4143ded425050eef6254143bb1895050ef76154143bd1855050eee6214143bb5885050ef66114143bd5845050f7950141439f9885050f6e62141439b9885050e7d6214143db5885050e6d62141439f9845050f7661141439d9845050e7d6114143dd5845050e756114143dd9865310f756194c43af5924310f3e5490c43bd9864310ef56190c43b75924310f5e5490c43e79524310fd66190c43f55864310e7f6550c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43dbd4a5210e7e61948439f5865210e7e60948439f5825210f3f4354843cf50d5210e7f61548439f1855210e7f60548439f1815210f6d5214843bd9845210ef56114843be9805210ef96014843ddd465110f3f4394443cf50e5110e7e62944439f58a5110e7e60944439f5825110e7f62544439f1895110e7f60544439f1815110eee6214443bb5885110f755114443be9805110ef96014443ded425010e7e62940439f58a5010e7e61940439f5865010f3f4354043d790d5010f3d4354043d750d5010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010ef66114043bd5845010f795014043bd98753d0af561d4f42d7d4e53d0af66194f42bd58653d0a7e6194f42dd98653d0a766194f429f58653d0b756194f429d58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42cf94f43d0b9e53d0f42e754f43d0abe62d0f42eb98b43d0bad62d0f42af98743d0abd60d0f42bd98643d0af56190f42afd9543d0b3f6550f42e7d8d43d0b3e5350f42af18943d0abc6150f42afd8143d0b5e5310f42d754c43d0aee6210f42bb58843d0ade63d4742b758f51d0b7751947429f98e51d0a7d6
  | 47 => 0x540000088004001000600180050000066003803300200000004004000002a0004000000800a0000000003c0030030001000000000000240004000000000000000000000000004800800100090008000000001100040000010000000000f003c002003c057002c001002400b0030001000000300040050048001007c0150070000000000d003c01f0000000007800300000030058008000000d002c004000800000bc000001000c0018002001400d010c00000080040000000000c0050040000005c0020000000000000300000010010004000000200000000000008001c0080004000002403700f801a000000500c400900180000004004000c003001000c000c000003c00d003400000000000000000019c022000000000000000000001000002b00580050004000010800100540010110000000400200100070000024000c002000000c007005c000802400080040000000003001700180060000000000800600040320030015000c0000000000000c0010000004003c00c0038000000c00000100050008015000c00900f4043001c01a0054005000000000a000700b40080024033001c0000014018001c008001c009000c00900380030018003000401a0018000002800a00000000014000000c002001001b0004006002001100080040014032000000400d80020000008003c009001c0310000025004800400000190010000001001f003c0040000001001c0020008000bd98752d0ef561d4b43dbd4a52d0ef66194b43bd58652d0e7e6194b43dd98652d0e766194b439f58652d0f756194b439d58652d0e7e6094b439f58252d0e7f6154b439f18552d0e7f6054b439f18152d0f6d5214b43bb98b51d0eed62d4743ddd4651d0e7e62947439f58a51d0e7e60947439f58251d0e7f62547439f18951d0e7f60547439f18151d0f755114743ded4250d0e7e62943439f58a50d0e7e61943439f58650d0e7f62543439f18950d0e7f61543439f18550d0eee6214343bb58850d0ef66114343bd58450d0f795014343af5974390f3d65d0e43b75974390f5d65d0e43b75834390ef661d4a43bd5875290f6f5294a439f9865290e7d6194a439f9825290e7d6094a43cfd0d5290e7f6154a439f1855290e7f6054a439f1815290f6d5214a43bd9845290ef56114a43be9805290ef96014a43ddd465190f3f43946439f98a5190e7d62946439f9825190e7d6094643edd0e5190fd74394643ddd4a5190f765294643dd54a5190f745294643ddd925190f746394643ddd0e5190f374394643ddd8a5190f766294643dd58a5190f746294643ddd825190f766094643dd5825190f7460946439fd895190e7c62546439fd815190e7c6054643ddd955190fb74354643f5d0d5190f775254643dd9495190f755254643dd1495190f756454643dd98d5190f7743546
  | 48 => 0x6400000040030050014003000500280000010019000400200600060010001002c042001c0010068008000001f00000000010002001c00600180000000001007c0070000001000000000040070020001000000f001000700080010008000001c00200140040004001000c0020000000002c005001800200040020078003000c0050014000000000e0000055008c004002c000004800400000010010008000000000000020008055001800000a400a00040000000001000c00b00040040000003001400200000060000054002800300040050000000009c00000280020004000004c00700000160010000001c002000000100640010000001001800e000000300040050000017002c0040000000003000000840000014009000000f006c0060030000001c00300040150000035000000000000110000000001400400000000014000000800f000c0090008002001400000a00000000003001800a0000015003c0410014002001c00a00180030008000000000100140000034015004000e005400d002400c0020004000802e000000000040050004014000c000001c0000008000000c0060000003001c00e00180020000003000800000740050000022003c010000003700040020004003000000600440000004005003400c001c00b019c00a001800000e8020000000f00000140004006000c00f0020005002000d000c0020000003003c0020010003000c02100040000038005000800a006400300000040004014000000e0000001000c00600240150000006000000b0020010007800900080120004016001800800000040034006000401a006801600040090010005002c00000700010000013000c02100080050000009000c0310014000000c001002c00200040040000004000c00400040050020003006c0020004046000c0860020005000001c001400000140010004004006800000000110008000000000c0018003000800100000000000000003c00100700160000009000400100100000000005007c0130004006000c0010004020000c0110004000007001800740090004004001800d0028000000000100000210000007002400300900000018002009800a0054000003c00b001000200700090004001003400e008800d00000010010006000400100080010120004007c00a0018003001401b0024016001c0050044000002c05b000c02d00a400800000000008015001c0010024005000000c000802b0000000003000000140020004000005800000280040004002002406600000000000000000c01e008000200000170134069002801400000060044002005c00d0008000002000b006003e0000004001c0040030035001001b0000001003002700a800c005800900340010010002002000f0000002001400c00000070020002004401e00
  | 49 => 0x3c0370014001000401700040030000004004c00000000450018002001001800040130000000003000e000000d00080050040000000000a000c003000800200140100000021000400200000080054002003c001002c003001c0140008040000c00100000020008039002c00200400000004000000c0030008018000000000000030014002001000c00dc00200000020028002001800000d000000280020010019000c0020230000000802c0038001000000000b002e004c00a00080170004000000800d001c000001c00000140000008005001400200080070004002003402d00140090078003000400000100000010021000000200080310014002000000d002c005000800200000000000019001000000000110000000000400000180630004007000c0150018009000c002017c001001c002002400d000c00600040000000001003c03e000400a004403600000070020000001001400e00040008006002400c001001200540020038022001800001280000000039000400a000000300ec002005001c0040000004c013000000200bc0050000004003400300200010034007000000100000000000000005c0000000000000801100000010014001000c000001400100040000064003000800000080000000002001c000005003e0088031006c008002002c00b4010002400100380020008002000000000000000004009004c00f00000000008004002c002007400100c800c0008006003000000180070014000014c00300000020040005004000c00280030018000001c00c0028002001403b002c02a002800000080030058012001401f00080040000000003400c00040390000002002400600000040000000004800000bc0000018020007c0010000000000c002000400600040000008016000000b0000000000c0170018008004800200280000018003003402200100180020001002800000000010000002002001f00040020000001000400c003c0000044001000002f0000002000401300080070010003000400400000000080001000c0080038007003c00d002c022001c004001800e0018012005c00200140020024003000000a0004002000801b0004000002400f00000010010010000000e00000030114000000000900680000000006000800000480060028000001400201300000004000000000a0014019000400e00280010008000000c00a0018094006401200040000084002002c04400a814f00000110028000000000100340020028001000c00100c40000044002000800e005800d000000000bc00100040340010012000c005000400500180020000021000000800000440000000000400100000060010001005c00c014000500980200004001000c00800000100004001000c00d00000040010007008006a000800000a002100040
  | 50 => 0x1000800e0044000000000000000060000001002c000000400500280000014002000000100080100000031008800600040120080000002801b00000030000000001000c00f003a0020006006c0010040000021c00b00580000008000000000a004000a0028030002c000000000a0020000000000c0068000005c00a0020005009408a000401a00080070040005005400e00b400000000090024000004c000004c00700000150014007000c0050010012000c0050038052000001200a000000280000048004002801c000000100200020008003000401a0028003000000400000060008008003800900100020000003002c00000080010004000000001b006400c0050000000400000000020200004005000100e800600200080030003000800300280010004025007c000000000000000050000007006c0020000038000800e007800300040130030000004800201ac00c000801300180190024019001800a002800300000340028005004c00500b000200200000004006006c004004c02b006000d002c040002400f001c00100480060000002000801a000000400040130000000000c000000000000000000008001000c002000800b00000010000000000400600000e500840040018000005000300080000000003001400100140030014004000c05b00680040000002001801100040040024002000c0100034000002401a005c004003c00c00a00040040002005400600040000004000000800a008c00000000090008007000400d00240ac0004001005c005000800b0030014001001b000400d0030018001000a0004000000400000380000000000014000000140030040028000001800040000018002000400200280000050002003c006002c00500d40200004000000000200000000000000000401500000060018003000000100080010028007001800500000000004008000c00000740000000000000400100000000000021000000000240060010004001c00300b0001000c07b005400c0024001000000100080070048000000800c00140000040007000400300540130014000001401e001c011007c00e0000000002401500000000008001000800c0088003000400b0030000000000000b0016000001300180080010000000c00000940000008000000000000040020000009000400000140170038017000801a0000016000000c0050013002800c00280090010001002c0030000000002400900100030000091000800d001c00700240000008003000c00400000020090007001000500040020018001000c00e00140000010000001803c00340020000002001400200c0013000000100080010030000000801300740220004000000000d00000070000004000401400380000004002000400600440040008000001801600000b30
  | 51 => 0x4006001c006000000f00340980008002003400c00dc004006000300000520034008000c0010010000004800500180200004016002800200300060010007000000100240050044000000800100180040028005002c00000040000000010000400c002400000e4000002000800080040010000003400400280040088013002c0000000012000402e00000000000011000000d001800a0004006003400000a40030000009000400900c80050008009006400700000010028001000400600240070058019000000f000c002001401400a4000000000200cc00d00e0003005800800000180000007003c00000000010020006000400900200260000000000400200100130050007000c000002400800200000024015000c00400240020000008000c028001805c00c0004000000000c806b0000004000c00000000000000000000402000100010034003001000600100020038002001c008001401100140090000009000000000000010008002003005400700170004007000002000040020064000000c000000400f000000c009c00400040060044008002c00102b8005000400601640080004000003000a00380060044050000800000440010000002002800300080000054005001c000000400300c400000040010018000000001d0078000000400a0000027000c004003c001014c00d0030000000c00a0048000004c00c00500070024000002400000000020090004000c0090000000000000d013c007000c00000bc003000c00b001400d0000006000401100340a0000401a0004000004c006001c00800180000014000003005000f0000005c0000014003002800701100000000008000001a0020027001c001000000000040040038007003800000080000020000001000400000130010001002000600000060000001000c004000000a000000000000020008002004400300000060004001000000600000000074005000000400140910000000000000e01600050018003000800000680030000003000c001030c00f00340010058002001407600040080004003001400500200000004011000000800f400500400040000001004800b0000008000000900140000018000000800100d000a009c00b000400300c800100b4015000000a0010002001400c004c0000060006000400600b80120024001003c004003800500040010000032000c01e007000d0004001001000000080000000018001000f0008000004c00000bc001004002e00e800600bc00500c80180008004006400000440100008001004003d00640000000004003c003000000000ac006000c00200ac000002c005000c002000c0000020007001800a004000b004c000001c008010400600040020018063006000f000000b000000700000340000000000c000000c01300340280004
  | 52 => 0x60014000000000000000010000002000000800000080004038004401100200000040058003c00100500070000007000000000200020010001001c001001009000d4001000c00000000010048001000c0010050000000000100000180048003000c00400040010000000004400a0048002000001f000800200080140020001007000d002c010008c01e00000000060000000001d001c00300ac006001c01c001400200000070008007000000100380100008000000c001005403c00040000014017002402500000040000006000000e001c0000004000000000000240100008000000c04b0024003001000d00380000000001002c0050058000006c003000002900040010004001002801800000000020000000c014001c004013c005001000b00000020000003022c000000000700000020000000000000000040020018006000000b00180040004006000c024001c000000c01c0008002002c080006c000000c0090000003007c003002c002000c01400bc002005001200140030010028000000300500020024003003c004000000400280000054044000000000380310024021000000000000020000004002c000005c018002c00000540030004013001400000000020000000001800100100100014003008800400000000014000000800000140020000001000000400400030020000003c00000040180004006000000c002800000380040010007002000900240000000000000000900cc000000800600940010000000001c002001c006011800a00b4006002400600c4008001c00d000c0050088003002400b0050028000c00e000000e002801f0000015000400700040000000003000000000000140008003001c00f0020004000000500000060000016006c000003c0130000005001800400080080014032002000c00380000030001000400400000030444001007400a00080100000008001000a0148014002c006001000c000401800000070000000002c0080014001000c0090010001002800600180120064000006c00600880010000000003c00100000320000005000000000fc00200040020004003000001800000180068001000000000000030020003002401e00740010060006001400a0000029000000400000060018001001000e000000100000000094009000000200b0005001001800000010028002011c0020004002005000300080000000005003800100140000010012003401a0078002000000500740000008000002400e00000050000005000002000080090008001000400a0000000000c0070028000006c0130004004000400800040000024000001000500100480010010001400000fc001000000000040000048006000000300100010000001002c00b002405b00a000900b401d0000000006c000005c0310000001
  | 53 => 0x2cc4810cc36b800004a400000e400000675a2ff20903eac00019bd0e24347c00006c5408a00004160ca74abc0000000000032964c7909b0bb4117860bc0000e7e2e4a650467b80001bd69984000279a4b9c9150aec80004794516cfa68f961d6a28791cf26c442a217d89b91cc33600536425f80f0198c19fc92a90ef1df84b9c000139e000031f8e41848225ea4ae40001e91342c32b50f799532d560788b8f1540166800010e819ed1ec42d0829911754f40461c32a26e024c0000020d800022080eb858da3a300006f7878a80000c221ed88dd936144b04b9844d8b9807a80bd0ec29e8c24e84bd03591b2b456e54811c204390dea2d192e189ea16140e90b94a2dc2ba091d909a859c179c8ef00ce14851a085b80553a7ad1bfe63ac4de98bd1e0261849f113bf082e7dc53bf80c91a4263fc1e827d247ac0e48c10277435620c78add25804e5c41a88a3a3ae2df005112cd102f389c157094898e22c5649b42a709e239729ae91860a8e2b5437a81d9000f2d3492880bb848910a67d8c38180001576510903f1bd524921a8cb6a03894b421fac1f60d070000000000019cb4b2a18c13ad0c3604d45115047a64c2f9624e8649962400003ce07a58c4b4f3c6d4cba5815c2d464a0c2bb8a72418076d473589210d4885084cb8c13444a18e8694868d2258084847a975a00001b744bf15252b9c2e28bff8d12105e0000b6c83c9162c452400026853b3c23a91b8221f3ec09de4bbd800000002e84000000000007f25137191c4a349258164a5ba41dc4c5ca610661311271ec661241a24727b7d0101d2406d2116046c9a4a00000000c1b05c0344645a807e00002d180000d4e8940000018b0000132200001980d5080003d6201e40000db500008c990cb01e925d200004021b2700000000c1ea5884652518c0000f47408603f8000261b499a2adcd5501091d0c469011c90d00378837ca6e1aab41a0389073c00d6257e00c0000000000800540070000000006c0090004036000000000000020034008000800a00080000000001001400a0024000000000001b803a002000000100000000001000c01a000400d00cc0030010016002001c000001100000aa000c04e006400b001000100100000054000002c0000000004003000400100010008007000c0000078019000000a009c0020004001001802c00280050010004000c008003c010000000000440060054004000000400040080000001000002b000801c0010002000004d0004000000001b0000013000000000c8000002800300000070144003000000600380040018000000000300040020008001000801f00300090004008005000000b4028001000f004000c003400e00140060200010000000c000c00300000090078008018c0360000000006000c0004000000400400040060018002000
  | 54 => 0x645c678a3e42fb800fd35316d73a5c9c84eec17732d8e425c0001b7c00000000fb49fcb1ce8000022687e700007f3c1e180000cac51a05218a8a350c000037d01042b6e0fd434091453b46949c000000040825fa40001e701fa200000001a32000089e81d80a093f3293d4d5c19ef4e0c6ef41bf8f94336e69a0000176e1e769eb85a9174600001f94fc125e53b500000083028104285fc815b00223606731000027854a849eacf480000249418589fc135d362207e51e38009325e5fc443e11b90000000115226712d6854e8cbc09130000183cd8b115404da000000000003434000019b063734183ee43da05ac465e1e2c44990a636608a38c02231808806568000000000003368df015e0387c0824c4a0bf91d946090e7180001cb89ce0fe98a26000084b8bc891dc33660000cd58d8d367a7b90e5b15af08322f041b821341db830cd39da78b0d1472c80001617000000005af1ea3219a605836313991732000000009f604826698000242d039a2960d549bc637245098f2c92762c82844804c8aa80b304f180001de033f83a4000a215e16e296ecf790c2219ae1854e53a45b330e489000022114db00000fab17c12cce7f8465a9b6e4a584d00000185c12da7e912858a292e984ad0fc780003fd642100000cec0000158019c00002a704f8c00ca03b00001f58cae97a400004a3400002ef23560000dc60201030827e064885e63f9a5ca8f4aa29149da9680f1b9f4b436a123000000000000891087314380f80586c77c15c600cc13206be061b453025e46a584b42276646895e27703352711858fa750159674680001dc9251c17c845094ea401419ac9c385f9000000000000000201c68080000000282a63f525e21eb33e664f471008214fbe4d7c000054a20c2527c00001fc00002bdc96b8000317600000000250000056400c894620000963cc0385e928b4680cd36247500000001366000014e60000ee81e9800000001174000026707264b1fa23f401e86847de17241acc4b848d3048e3864257400003bf1746337c05c05ef021497340281cd72566064c000020803f00e8d1b188160000314029ca36d05d011f44d680001a368ad4ea28fbe000075e90e680003cfa434cc71958910aa71d4f4d80003d7a8bf492c26830a882b9c886095f1c3c651cf058d4137b48b1cf4c80001ec234b03280c1100000f15344a4ee37d80034f9e84ed00000900000119528de7b58ec69c5f000000006b7845d199c04ac2a481c015183e183f60e06168e86c525580da25360000f9d92050000000005b21f927a8299800010b200001808566935400006a5400021f4491a76c4ea9a29637109504c2e97b335322090739026912620000044084f48961ad800005180c007a4d1770d3021fe0000000267a1dee9aec000000000000000c77800016ce16
  | 55 => 0x1bcd1224583e84156400026b944520000ed5914a368673ec000162820209b0d187904c0bc45350931a2513e5a000096b13e043fa012801727b813c62e4cb5c1b5b4ba0452cda39a390bfc000000024b73ea26b70000249241e00000b411ba924021c711ec1b19000000001070000350a64d8e02852e4214465ccbc8de33f445a049a40de118ae0cfc8c326f312e2013cd52a61f41600ef8f9ba2793f502e413f9876f299498145d21b0b00001ec4d1a8a911cd44f546520000000000000000fc5000025788b40c6239d206b903d1a8b163214c400011d900004d5427b1d7e08f8000000020e838e055085281f70196c338cf238000369272ad1a1007514e018b4c7f1a8e00009820000104f102864c84a4a7641e640000000228f390044a4665025613d09dd832080002b1c2590000000015809c988442401186a8b60291229d130882a92aa0d1520de3c291df9a6509d07b05359227f4d228be8e720d1024b69d8c1969ba24c9e9bf88f383af4a325828195211d1ed08a088fe20d52ebc1024db8a3e9192e111000016201a9e1c5c8169e3107c4401530d15ff4d7a777827a25a921da773c2e980000a0625d80002121063a42700000000408c9ba122f00004e663efc000000000003f30000235247040580526014f4ed86c28f3b07483d8016e440b81ba051e01c42358ac14cc40989259174d02fc790c9332583189866ec10627cc4612171123105aa42b48d14e041ed144402c182190f874f8a0eb0000271200004e38d6306d7000000006d3800036280fb41848c4f4eba3764f899f81261a12d4dfa1ca62fdc0e449688fff13a2000135f00001e6c98a8abd047510e66d14a98a78d4376000102800001b8000000000000000000012fb000048fa0000aa88000094e4704000035f107c7f885ff1a570f547bd4f10228400003270000164f4416861486d0806299a78a0758a361121251210311420220637f9231a6762b9627d0fea25e231685cf87d310f7033e00000e9121521768968a8617600000000000019601b541a8431c839d1a1280f864e8093095c000104da5b131102d3cbad80002a5200008fd16b0476a1ba9263038b08c205146c08e8c03425ccc969108b470e2674000032c358070d4000265c45720eccdbe91b402f0514069f8b5804041eb4d2d00001f5e93652f8a18146f672ec3c0108c00007a80b7f8d691e5c560c81e0f74068a7c04f0207743b5200008d500000cc61ca87efa1a943269e48fdd00004de8000000006ae01da9cfd0f603fa0e602fcd39187083ecc2f1c290072703e0898815c000024640000000055146e68eac75582261520630807b264d354e6b28000000000007d0c000037b000000012038d9b000002b525c81201a4a73e80000f7d434a00000002008000050d41be1486305478a8c2626560f1c64053da00
  | 56 => 0xe3e42a493d0260800034587d0400000003de600009e095301ba673e50b515b835020000121a2e33b2a086c7bb917648e21b08f21118b43d42830f54266428865b60f94a4bd1c065a6017f9fa915348a987f106061a9a000000021d30ffa05ed03d9c0e1b101414582836a4c465028b331a1d4e4843489c4015e3c607bec00015c2384e00000001f47000095845e808780f389a88000263400003e0caf4105600000000000058e00009f6400014d100007d683e1923d000099b03af8000428200000d526b639ec249d24f0cdd45388a940000000249e466000000ca00009bc8f530c3114105484040a76f1b18055c00000001e4488f400002e44b080b380001327000097a8bf38ffb05422d7508b136c4e3a0000000022126401a2100f86140f0c000000027584b227bb000002a01c1c3a8c0001467053052745cd1ced29746950000029644206b4000009f1310a65ad0738a6133c270111ab10c04714904400023f30000020cf550bfd336000000000ee11cc460209fba05d00007d28fa0215d3e7e5c1067a9305000013f4220937000001ccc2801f34227c8e344338000182c00003e389784af09ad119580001a6600009eb10e948504810c9fa48c0f264df484780001dcc3de860e881e11c663792bd96d017cc29e12780abc1c8418381b880000c0a6fe4ca406fc3a7a57040b280000000704502e0f2948fe0000267953e404e990400017c0000000003051efc0000000000020f54f9009780000000184e0000572045f00001bcccc088ad147c645831101b900009014d8d000000000000000252615da70300000f5100001e49224a22400002d28c4e82ac29ae0000d0d80000000081cb90000000000000000103623d22eb00000000375c5c4000021ee00002ec13f79ae80000678cc8c000022f229110501a674bd2202101c8000000036141c70fdc00d002d40a980004af471713de228b01962e78e5607d232983644d481b63123a3f08cc1a3d225600608c689bfa05080004f271aef06863b0ca1e0e7132d400000000cfc40ae7e9c861a4030b9261d033b9a37304c80d0b190b304e6215e06558ad7159820c111a02654fba11c9303125e42f82b140930b4b1b688cd8df1905e179a0b4518d10912faa85e8aef075a134e4c8c93a85cb340a7a08b4993770e268bac4e51e07023046f8a659caa2bf08af46de8c05368c3e10552a2aa33ca0118a3b80004aca5fe42fc011a20c867ec3a614282b982cc44fba0ad3b2c13e113f09430000642927d0000391095ac5fa11280972997d0e00986084413280001ac334000000c889d0f04660000000087639be0000b168c6a00000000000000000000000ab08000279809f8cb29d890d808c2887106d64a240000370000000009dcc000113f397087c93bf0dd24da23d9c988a7a63e720cc4a74a783314e9
  | 57 => 0x8f003ec093e4a3a4cd9154815d2b8800dd3b516de2f4e316c0098f0807ae83748c1046d0114545454b93f32dcc2928e6d9d28026e4580ceda2d304e243a8eeea0483d6035cc8c19fa1190a8c944088dd00a3e021cccf05ca4690663042724e14b300000f0d0da8011c0000ebe9d142e943e3400005f749a60000b818a3749a2757057885634e84000060813d2475400011d11d1c179e9dac29e0000000000000000000362000000001af146f8848c127236f0f502d8801c9c8f083a5d4c1ec0dd73c0a9f58d1320090aba03bc3b69830000001f93db9f240000000082f982803320000daa00001472000000008350cb05af000001f61a180000ed000002a6c00001730af835aa538ca768000151227e82d30b970572513c9a59be22cd60000ac6976325d0007c62019d14b507f900000ae208d87ca8556187f44624b69272194d4e7a9338256a6eb07942114ebc15db2cde9c391f6937b1a4c1a9d182a2f21b5678b0364849c32da1508585a20816862ab84ec000000004d1800000001be46accec9243d2db408a045f800003aa5e545fd19381cee76ec541093040389ed49b506b40ccc0f089b108df121e998d01ba44e060e154c93d83e54fa85a8434b862816a88b6c446100625ba27708e91c9e17ce000070900004b26000000015e90000000000001d74304165ccb30fd42242827448211ad00000000c0d9f9f183c7c00467903a2ad650e4651076e194c1fbd32ba3cc388a740c4c1a287078e4408978880b1bb67e4041518e4253c568048500000d34548c579111e0dce3d293bd176f2c68728448304433a7c3c000e311a929882334067265b1f7a569110080c2000000001b6154e20841a4c0000fd6408403ec00023944f1e27501c514fb04841d4cddc9bf5411463ec05080781218034108302732a587d9c6cc07812fbc0b801f980003fe87f7823ca23a472a505c708a6034b9e88b0f22800030f85b850b20646000000002e900000416000120324dc3350000062a8000000017ac98c000041ee5d0c6d980001e86028c0000029264a0000000000047f0000000000002ce20000f388e85381455f0000000013ac0000000000000000001127003e000051d4000207f4c600c2913a896329dc39f040e0b9f4f2e00004de13a331e0697c01587164f289e9c80ca69429021dad2fd8c713f6a7f6445c000000003a80bd693f01dea59803e6072129280000772800049e27094df200004e6c7a592d799404e726f74a0c0252309c3a94fb2a7f23b6e000000013353bd8000004f800045146cdc708000029047ab45c20bd900000b8832e80004560365c0000000000098389faa71529863f606831e884c140ba8e4d88821c0418d89370a0a15d8487000000004a468b94d039522000068e8558832e10265b704169beb1d32582c8d2a6040d729e582a30
  | 58 => 0x2299167e7ca0858127c3bf47d2057809be0be8412cde224721a904a250a41ecb090045b41ad105d255c3b9090408ce2f3415782b7000002763210d930a6233cc990043899c618dc8f5000000000e340000763059102067df473e867a1caa5e2c8c9817035b29beca2a8000485c5d212970b802a1200003b38bbc33b899243e820f61e327ec8cd60000294e0c084ea951335ae00c87670b5a43140d208418b691f24867889d173b1eb42e34efa9a380e3c3f2ccfa10d11c8677140189a601ebc9e7441b9381275a990d1b1220c21ea23c89e98a3130f20000874053d000009985598b5600000000be624d401c64bb8d4401fa08049c7d2b9106d41e4050c52e1a8329569bfc75710924f82745c00006fb3c6423203be24ff2daa29902d78c183734845c00001763a4e0000a9a1b612524094c9658592096615ed05a8e7b482a0000ca20000000015ace2da1904a865df460f8000289a32c87b0172b4da865bd20b94831f48390002d038748f64e6d119084933120000b7a8ad0391c36401d0063c40dc000084f857c2e103eb4343093605d65ebc4cd9261000075753fc8f9d430e00000000000002476c0e3f96c0092c3ca0769035621a83dc8798a0d4492216e939809380ac8282d356235537f60000000054b414a57ac3dd0df9173a94e8cb20b6b00b81f8000008ba000025d4000131d0a4e3bf800024411a8a19904bd04c900ae10dc0e095f7029a036c893188d376842cd1620ebc374281352ff8643110a68500b505bc31b890005a01016496a5a0c05810a43460818cd5699934d305360e99a57938e839b01241a1e42609641042225d119438584d1853a39dc58ed2a41f973a082d8cde720e236242b082159e2b021e5228a2ea34a112e3afd210a30d187c6e7cb18a4e20c1a8b2c31f046e217000813f48b8e40aa13acdd9235c399280c13d51deb1fe494f4312066f059a7e98d4784ee08c082ccd8781903ff02c78088934f416e0888e8e84a1325c3e5cb5d02c53e6a3e00c4791f5403a9fc4cd22003098a612cda10cbc2ba86ce8c819aa3246e742d24c0e6f35e47e4ca8b27b32b9e9d4cb4723ea4d6e97d099e0f632fbe0c6488905ad4262078d21b861723b482ac5861ef64e0a92746ba0f2b278e31dc3529ae301fe61ac1bb16fc292c8a5c829190e074a86487c485fb37329d3d3378ca847ea562052b19c2496275012290d5e49b401f088002a4337438a5105032926585ae4240915914b6301cbc408a7410a1af511f1aff152c49e04288c9941c28db0b620198241638888f2827a42e83c50c999b6c4bd83ec539f1cb444ca7d4d36f9e771bde8d393d821e317a280542348cb94c787d407fc1eb8378a97703fb1be54ac810ed00c1247028c528c69d962702d87db4d6b2259023c5b1886f018904b43c94b21867011a671452e201793a7e
  | 59 => 0x600006e89549386e913032494d50df21f1090892c810c07b545f604dc000097e5160880a2d1042747d51407017e1c186b5a27435cc3a28210227330c00000000040f142047150b69f8b14da0aa80000000344a44e400000480bea00006bf0000000000002ad24133b9600008cda513000047193de8f210f4896147b288ab00000000eb78000366a959d10786754fcc68391f896541e9c34a0a7123471a2e025083ca2d032f80d3029b0ad627a25138c5500002aa09f0cac90b26245e3929023a6db38682f0895b9a9210da562c2b5123438b275a923506180efa0d8c746a44f3caa3c8cb6e89c01ace9418492a6fd05f2771051e9e8e4baa8f6800016e208e000002c2000040d86198bfd8fcf305a000063ea76042661654bf293f1210e96343b4800010506ca05b280ea0f3e000015e010736d653e839880004a8e43e800005c727be03cd10384d410e4623076a00000b8a79ed3a5189a2b0298d4414a7b94b3a92a01d6a07d13907230000208200000000ab408ff000002a931e8f09136466e080f87da319a2e94000000006c81db03f500004528710800000000000000000022b847ee000000017694e0000000f98ef11ab65224cf717cd00000000000149000000000000000000000000000000035966b3000025554fce40fc0001b86000047b907d1be72eae51fce80020326045674d948000196846440000a872c4614105f20a5310201ac0d70a00e05381c24000197219c27830c5b07ac16225304309851200005eb84bda76d0000263d0778b910eb25840ad9148047a2540cbe82602000058c0000067610447d90911000030847fb41f59ed44d9c89bc000000644da267043d1b64000077e0f30a0f31470000000008fd244c000094e00000000007036a9c6947740de46240fe7090c050018e25ab27d23a3831a92851a46000045894d01fe83e04ea91a332bf83ac00000ffe3bde1fd48631329091e666d280250340f2611400013c00f3c59b00001e19000004080cf000046a805ccb8703682e9e3f492de913c1ba831e064a9db83696012400014ac0f28775c76f0000434e0f7c0e516a030381e680001d1e000000000000000239a00011318eb427d62f18edb13c5000098ccc6a1bfd429a2414109a46528f64c981bea1ad3e08715cbf18f3946be16a4bff0a9e312679e528289d92b084ed8470891e0f3a31e4c41872c36c40bdc242933f110c845024c0194313c7a70e008ffd36e84e3c1e20c261e18669c616805541206f089cb853f2f04113814f0e9d122e4ba83790a170e569aa04ed86623dde042cbcc126903663bcc88701f148c00f7812b9ee3292622288a096080fc462c0e6914c62e0e7e708c492644c6272d43229142238070f116f9ca342f628488d791b60520242d3eb80600cb219708f6105b16669c1c43601b521948e009ac
  | 60 => 0x600004be479180000000349c1ea50a58d96000077a400000002d9c94eca208fea0ab65f209269074430c542086486a91d0408b432d873d02361f842548cb11e6a0074ab5051b0c52018c25d81c72fda733461e2040000099ac88b0698114483ec3a8957d276863cca8915f331f2610120e0a0311c04ee0538983510b816651bfa5094bfa7f2847b9b55275800000001c2922628ebc24f9ba80000000094c80b433f033c8c8a884b36ce00006fa26fc1c7a5cc0eea0be81fde048c0001558324c9aa934595e2000071b00000000140a0000876000000002b38000100a46743458bcb800011f24858000000027dc908d19f251109742ecd31d9ce11d1278e120400004ce46a6002192a142a8003802923df16440001369a21c000003005e923743a8c61ec0aa00000000639c04009ac4e1652ec3811bb6466a8e180001b73467052b844411a7000081380001140050a060c0001190000029b078e800031b200000001b843612105904e00000b3c77f0cfb22862e7889804e486c43fa45714ec18000000063110ce99e4149e0001232201214348d9400026c64d1c1adc1981a3c087e36fd3ce0435071e281c61421c6283e13010031bca44a09a1c49d9fa007b44fd0c6093750f9e50dc2c2a68a493818848ad95a2203657c871d1ae414383554dc287bb25ca277cc5089c14ff60dbc1fb1bbe450053780c604783f001a503b20de73fc094601f700e2285c8b84f279395381e0ee411a1a6d35906f44b1d09ec055219280000e5d13fe722cf39a0f9000000000489fea327690d805e14f438ba80e8d099cb11c580000e069099439e2aa4c31966426fc49f82bb26f000002c9054280004a369e651139f4537e24be48cf1b3312b84b34c1d993e43e61cbc3d81c5236fe483007309924ef8897898602154372461471b9f0b4f5e098400009723faa24a433e18cb000067f8bc80c7213a05a5800015c32ec4049d168a4fc378e00004aa21a0000084e506f05bb21362dbd32a0f2a0cdc3628255122b26f472fc6358ca900002eb40000450000062a4000000014be00008e8000a46e48b580cd9cce0000000000018c300000001142848806a400002bf000012ac18c461b9c724e2648240000000000030a40001c2032280000bbd000000000000000272f35042499233051a4ed29e54ae99d1b00009d1800000004ae80bb408b80001a7275b82a3972322d2776c6b696e326c0000027d8000126e2a010468000000000013768b2a005e00010a3a7882b5283b048fa0b200002368be2000000003a00717943d0b10000025b19f900003820d3a033e29521aec0c302f1498e0a300000de503443b1d0e880000a8058600000c3a0bb643ed041800007b27fd499202d4431c08c071310722ce62d38fda13782580230c9588000000052b4ac110340000734c0000d921e0
  | 61 => 0x589544647270f2b724ce4d62a2141da61d6cda78000000062d43991c2f3f580000fbf85e51e0866c48c2142d1d26945c7488000000006bc9d8244a01122a0c0a60ab44512852908f800032aa21d530005283bf60000ab3800000000000a6498b712de0b040d2099542dc3038122a79300008aeca6f834e083e6d78f88060b006c6965028859b000071dcd5400001706320800007ee4ad200011e204ce2c42255439da2b20250877c5ce049d234640c070a000031cc25cc1e9000000000aa0d7d1e44379608808d6128043987440000022a23f20000b7da1153e448c781c224b8000000013a7222a13008928a5e8000313041501cc96e7059e95180000f59280453e000000001aac751cd28000020040f992e4000026ae976d31106d4358e091ca6d8000296c15b07ec9b9d39b82e040fb85c3000055d919f9ce20b0647ec6750000455834c400000001e8a00000f60446061862109769e680000991877515a300002d911b411a2000023ac0000a593304218800000000c6830842fd0000000000011bf25860f0a4540a9a9b1d2e920000bc29e7506640dd0acd00000f6e0000e98099608f40000000000003a886e0270a409426400d4663854135740000feb07f41c6241a40000000118273cc000000000000c893e58eaa2178000114980000000000056980001ab820342138000122a0001167800000000001248000015e80210ff1943b000000004c51fb743660000e250000000000005f6a217101e49110cba0561c9613b07fb2534167047908ea898c021a0001381800009de317909583800000566cf538abe3f306778eff23a100000000aa78c563ce830ac00013fd0000880842b80c42cf608440669dc1391a000136e17ce2b7e00002cd00fa3c3083e0e5210651c5c3a2c0000ae025a04969308959138360ea0750807700001310000000044ec60d0e75a61344246bd805005f000007404f8880c642120000705000031da4904000165f0d4c21bc0000000000000012358c340fc6497c00021382afc000067792ba4eb2886800009c3279e000059b9eb724ee70a83b08ef0181e00a0d69a6971bbe9ba491b000016b88a8c00024800e465ec800000003aee41f11a822160d20529400025d94d5677cce728000000071e106b9655155469443510000000000012d719590000886c35f800022ba43b90cd800000000629026010137f07ef4abc996947cc1b411c614a03c6c5e58508a0f10692403cb69a3fd43120ab883e927043b69e250499d650dfc9998000022403c8818138614950cd01af840c259423500000d1fa71b08082a8c9010aa108d07424000025b0bfa00001bd0000052e06583e71be63d520b7cb6680003bf29f40adf000034240000000116726cc3ed800016591e361658fa301c23aa07df092000004c38675c78c0000438278d504
  | 62 => 0x8d800038ac10b4000000000004e4425925c0360429ac4b4150f1d7064e84c399d0318090605179665196614b4293216727ce00000001ee938264ea4d6e8405383a48fc0000bb212c2169c1f49b6d472000000000000359a6948000000009443b146068efb27265fad0c8902b46ee0000000142200007354000003d376083352838494000064400000e17000000013340d1d1d240c4c98500b34d1a000000000001c302e3112100000254000062c088e16b6542c42521d603c04fa10fd1ec339ee18ec59580b733323434633843c4a6069c4c8917c61c461fdc2fe02740de86a2832b88e9202e64e43ec8a7702584d240002327479c635495a93101b94567c2e8a19c338208947c58d473b1c0d2c2b29998011e48f00001eb24f3091a13421fc341d400000001410390a9090de0068023e01c2d02f91c3269831a4d0f8000017a1bacef28000139c5fc01d580e000740000c6e8fba064663285b022d43aec000042902fd00006a35358254c1066530066d8000027e9108d7526ef057c7660af197f82d204fb400013fb332c7c50b131e2e1af665f86210172270c4de4933832f00b25700342903d1a4000008758db73e708c8c40d800000003e8c221000002007b5c4900daf4252756cad6138438da00000001a5d28c21465340a14500fa6649014a101347c2f0c1a122363380056817f19452b3c9fd800000000cca26884b593a246b68580c2d0c320b0c3eb0000227d30aa0000f861e3c3eee8e7413da7023bee3dc50f3995e28d83c9cde79ab70c1800013c380000fcc00000000000165e2a3c502242204ce02c4c3e85e43a4623e078f90d8474c95293e220594e1008685318000000036c0ba20000280a07606e0800000005e38000000049862b745b5269e00000000000010e0f3000000000c741b487b383b9a60d36c000006992230047c17b000027dc380c35dd01c1c0b16ea65185dd98ee4f8060890d727442b186dd8f700d632a027fc91068f8e479200f09ce830000001b7cdcc00531eda7904f7824a508bc5a1cc3a8a99400458e0bd316012ca04dd08359e92248c9524e810a6527846294b831a660ad2514d034a74332d02f2c9daa6f94b389ef8c6f832838608bc490f1a4c04a203452baa102015e4becb0292a5189c0dc8c7927a918b80e206d891624edc526501989a9068c92a418084da012a235d33f115f38f28fe909424fd143623cc79f811546782f78c0827540898616cc0024e345f202904540c0405d259106b4250f081c4a9ce3e8b1d3a585914b8a19e7283840884dc8e9710bc80002d19db23cbc262504a1aaf38cc3c3c1391170086291e897195484bac94880160000243001b8ae526362dd28dc4c561d61243e0be0eb389c431ac664084a206f20a27428e0e05da2de23e6d2f2240c3ddc8918afa944002f85edcb249f9e04
  | 63 => 0x6889298d870a9500000000000000005aa2f8cab289b53172000000022220000495d39698952f38000000000000000000000004b0183250d923685933b0465fc1ea9e860ef682c4c16064d37ee397ce5f1db9082000009a09ea429e26780311a5684984749469f0000000000007538dbc42fa4c64000204914ba957530e9f1a1d66203100b87a539b40f38b261bf6169a3684ad281b64d3810a463801fd42f097e89409a180000333029c048d2260613c00000004b0e78e400011eb32be33d8a4e18913f3a274c1a226453dc46e78e949c532ff49d2133c0509296a79b13fa8e9432046de5287133d36fc748871f82b3162e0c8539e160f2aea22a9310801e4ce0674891c17e623381cd93fba3671a4e3fa0e0a9a931f0461cc00000003856000000021940a8a8c40fdc87d11ea866b48249fec2310382c00024ad464476fd29f9c9400003f6865d80000000120cfe01cec25342c9c2630e730022168034218522eee8f88914181400006a509b797b8193e0000e8a9e173d341e98f78929618b415c8ba090b52742240cab01712211288e521306384bbe8d90ff418d818da0a18ec39af82c0e1a393f09bac3da41718c430f5738f846293900908282c8de8000179b1d3c00005f280002f3a1b3c98420a60000617872885b039ba3938eb688cc0d8e07d128210cb000000000000335498a000000000001870739d136000000000c800ca80001d4c6ee8c7b86e84ab6216423106443a7641c40000b5745020000e26059d13107a7921909700000000042117d70bce70e451f98e836be4594ea58000000000000000000000046f079e0000143e71240001a2244086d490b19c1e000088180001728301e7ae8000055839782904e34005d2b6a0000ce3998d0000026023300000000850000027043f563ae53371262221a5bb800024434ae600000002775052437780001c140000121cabd80000000395800016ac00000000000141e0000000125f009a39600000c7d1f1d000000004728000000096b4ea899583b9800013578e7f4796000000024611c3e25f48b1a33217b686fc0001ff33cf89ee80000000314400002f9800000003d6c80925c734ac70f40001f912c6a00000000928497e52f8f3d1b2e222a15580f79e8d281243e09f791a021fa6eed386a69f4c5c711cda702d7466826bc709811224061c9472796a22f5431953e315562f9e72288c095534f64373c77786ab3eea79752fa8e642e3238e4ee3946d236690e110c0e7909c096242f0a3b7062c15c51a991c720e00d9d0b10bf2056e39a5328094b004c6d440df00d81ab272601fd89662e3e133035a80004cb21ce86500651000006c8000141429ac29350ad8a2d2fb093dd0299e543d1689140001505000086a01a500001ccc6d30ac3a4b40b7c335839f9f1e350e05a4d398d80129a0000f
  | 64 => 0xf768c9637360000000035d2a307510eb91f023ba22900cc70c2436ca000000022f51f4e8f34a1202c200000000fe898e5223e0000fd513dd15c2811048823a53bbe7504c47211a1d887b6136496cb3d5e22413fa157f000019f91018000112432bd259a32427bc67dc7d924f837667e5890d94b300004c6c74d18321e9216012ec040c3c225ef43a30f7538b0126c4891ad812dc3cccd1e8c941446866059c8a3c093c5a90b9b8465470a749800002cc18ec88ac86b202b06c00000963a524318e6f603bfa1374ab22dc93a6913541f859d10de818b0000209923f08be3bb299fc8f50d3d333e66d8f018da241b005880d2868c464272a06f0000015d68e68cd70a2506300f6c0000feb0000502c2908f4409c81b980a4809230f424d400000004b023d3000009ed32b69dc800003f70000000008620542ba40d608b591f129ce3920b3700003a2c65593149077077416dcf668eda466200005d59b9738aa5a7510e8d8200000ce400016ec00005b3c83b0c1a002a7fc0954000000004aa8ec5094c2c2668b83ee09673cd257d882e02af20083004c029cc7371c2280b111b2a4eee6d109c122bc371690d45af8a2e4498000117e131612287068528908e490a8d5c5ee184d3fb83b587e5053b18049850697a67b0000000042c1c2e061669a4846a4cb00048ff8000074036409300feea72c1f684db908391f84f4650d015d00000000842c884a52b39bc2608ab8a1c44ba859a905f800027d839a02da10a91cb69028f4e8b610346137400d8dbb39d04f243c120862b2e300c6a923f912d8002c519928645401ca13351e0a046e2dc12bf9d7f00009d7c0001dc6046c79881e89722274000000001432000000002bf8000000000010578000000000012868b483ea400012db880500000000956908518f47fdcae480002be89154000079700006880b1b92f8123200012a80cd300002afc0000af5170a00009f2980c2a0072f400004b7465a44cca70800000006084e3b1d5745da000004f202f0000000125b0b3b188682449650a67253e4b50c698000000029fc50080e711a83d3d3aa8fed2606000003808dd49bc000123c80004c7400003e08896472441e8c38210f18181de87208942201054b4b02000043462b7c1f0105a3ad09f687bd966d19063f0c05c8000351201c87f2176500001fe02d9a63737b855150860c3b0f0610bcd6494c721aa8f94792272a372c47f80000fa9014c576808b0d9d261e000000005060000871ce40a31b111e91c09a181fe476c9b78d461ade000081852660ed014420420252230b49b600000000000087a721ce5481ea246a0dcc7f3064b175259205e485d73d7245c4e8c13cb08a40304fa2106720c000000001de233ea8da4e95959c26e28ab4e39998624ca098c000194e06da000121a000000007df8a381c314
  | 65 => 0x445a1d482e613d82f8e7e486f800000000428c000184932d88a9cd5a804b070a75286580a753b26598d1c718fc237a545d1cb90f310560000cbd115623d07b1856f000000004b90f41a6da23fa77b43c88d140cbc000041000001846891c8e1000028a23e68042951929c09ac45bca65d13ca58a44358000000082586c7a65533924b8101197a02960085caaa8463088e8ab801999050d98167ce4b1cff3ad20c6c7771e2446400c1879d26c02462000118ca022000000000001a080000597495f000048dc0030222800049a4000102da67919882a191ae936b4b54014422e14f906ea00004f380000a7c8f09290169f387000007e48d7d2e3664dcba71e2f407a0000e90800031980000d6d21d82b000000144800000007a1cb79000044965f441cd000000000000f3f00000000000057c842a043276b01a083773cfe4c70b6913c3315c2e3cd3217683420708d3a5800000008c48ceb279020486cfc00012b8047e2abc14a0e4942d200005e512ef4aac2fe0dc1000000008f4c1d38000061e000043f0f8f481e000034399133cb8063c7138000285422692df1c2800008a40000036500002c8000019270d325da90a4800000000000ac78c4611c4000000000000000343c000000003520000f29986717ba994c13f8a4718ea9d48d770de8105c0d1ceb013474f1c2a80d3aa1f844c20000000000000000001226a7bf42206fa12f0a761092e750cda816914f367664ee4233703563b311a0a58a366839e86a1000016385d08d5e1c3b19cc541c8b211584f185ce93480ae820729b2c5fb80003de83f5466685b146fa87fc000178404c0786d02c12c322b808b927c98292a228c089d5878842de50fc87e15f02dca8f54b0d00002724000006197d600006c300001de70c9e0001377050c00007da913b9b2c1a328950000000043cc3fd4a3888430e5c0000000271931142f682b6a12209a22f7ca3ca33302387ec51ee9a534dac213488c17c542d081ac0a8a5b53b94552cb778d7911bc5b28e86835419a8965cb011e6d37c20f90d3e1a62030061204408844349e40d41411dbc204e0000e0fa54e3dfe0590c5f9e1f302e1dd52701f05148a7024035198434d60cdcc5c227219421c88cd080003dfa4d402baa0e90000361899880000000022c29a07b2358452600000000000019d03670a6e0000770817e192404d600000b3000009320000000099a000099cd3369a043984865490a1f062f0e9c713851e78437c00010398b231440147000001dc49482cf000022ce3b02000000003101736491428aa41e227089353a4863f15b4000002a0eb630e435888788000341479c845b9e0804626f0ce51124e1c18719caf78000435449641fe9b3c053449e5332a1734d84347800c07ae27488305351a4ef0d621b7092409b7008e5d6526f9eab1b3c27ec
  | 66 => 0x91799a2b2700000047b0000208092250af93aa1930872d26485a508a22ee4dac80be23ae826020182e50000000000021564fb0862000012af0a02000018a84d7118827a44fc800036b45abc0001b1f09700000b3e23814aa66650e951cd62ee4805933e9a312c1875c0849800000008bbce2a0fe91b340b70d25800000000000bc48000047a72cc85880000000000076aa12722a4000009821dd4e560000376800043748ca84f700004dd4436c00000b200000000000089c3c0c29780948a4b449e17a11cc1a5e3ec400005a482461854633c9e4210d15920b740000582456c4aacb349d063492543864d0000000046fc000028b4d6620e0000000000007e38bf0800003b229d80e79d4221ca82d84f811084ee229808128d58478226c40001a8402aa000000000000c5e68a88430f1a42fc4b0912097a23e4a5e287c99de1344e7c987b783121002947135708d60f1251f49de02b40e366d6018b8ee23b542f10077180b37fe2c509781f76233400007c282e34cc07748053906e12c0000044a1d203f8e1cd046895f129ee00007afa4d700000000640a55c4d3665ecbf021c52a8e96d938486522ae04000943a1ca2bba531459680d224747ba8000000022b422d5245857d00ac5c58d4e00001ac22e20c34208044cc00001d0a562435e7fc400020111bd86a6800012eb4a9a6ab8d679497014a148c907933b2b2c59e82780e32058e5e8c2ec87bc10a81d71096a7ee228c0000a7e89111234829000000000c4e3340b8b99093c1e0000d0e25da1cdc58f8b49190b349a00004488000000039c02aa10953292000115f89531b9a60f02ef9e580000648001686af2e7000012bb091c2b5656f086400000000289070d1d9f0b5639d40001e0d19aa4788d8f05ea108c1a3c13718ab009c34690d3138a24e6481c78992a946dc26905c3a692273e547cfae9d6430c4495019d82c01bb00000df4800019fc48184308a8400003738e78000044e0627c68199432530000089a0baa425e972cae68df600008c392b19c210000367cb799aec261601ac4f09c7a4698269827b94f60000138c0000000000044800000a2b000000008e40632420a3870000239b2d320000c6d1eb53a1c713c2730f583b4a24008c623b33c208dd8f3780004c2c33e4227918d3ebe92c00001efa015c7b9458c0223018e56c11f09892333822c8cc2a0ba08a816a0dc78f982818000109d1f8701f00000f40007f3cdc92bc74b243c20b2556cb4a15ae08fc833cc1ba62d20064bcc000051300008778c368305278840ed36e9ce6267c2cd87dc00002aba336431580002fd47f5c32d12560fc84cd037495fb1fba20485a9a2b3281e2d551fd902134ec88bc00000002086620409a1fc8280686acbea06b82d90000093e851e44761fec00026c7394a72251ac8beb090842d00001e40
  | 67 => 0xc3e000000001c94c4c246cfd280000ad086b11ce039325e44138bc79bf21dc6418800022d7337e00003d099504608000022b0df717240001294800041848c1d2cb00002fe80000000153f2a880000dea24d835be40dd0409dad3a32072cfd6a65e0a1a6f4c4d285610e0e17b87338856098e80c922b0db64d94919c5d005d6345a8dac1a802bf31742b703b813fc28f88600cf611052a5053cd27500000000317c938a5b034b02800d1a23db305c197c1031657012c50448be0f163c7c7bdd32d171a047094208b70f1e000000011a311662f500000e1319231a7458f48a7121d1ff2000000000004dee000097e16c3000028d0bb300000000334471d805e4e28511077d00003b38854c00000000000000018d141d2834000009f00001a1406686721fe900006475347892d0000243800025360000696c66027780a2c4f705d10de4000005c40e8000007700000dce00004ea20000677147a1fa0364ca7217f600002a0441390e335fc90c0fb59d7b080e000000027273d288900b93a50c436c162405d217141b461a4497a695025a3f052398bf1443295b85ca800000000000000178d24d0189439480000a9e0000000041e187e2c04c37000008ce000016c1670000038e0fb627cf26ca24acf871e3b44ce1e1045c8eed288c3bf408997c9026237cc6629a010000840c55d24811526000070a94f2061c988000012db000000000001745000000010fb9449237057a90da00001d2a0000000068b4ac00000b9706e40000194c00008152c4a00007a81e9718920000f8b0000000082780001c4d000015e8e891d744d3214c0af30ac6000027992f18000427a5d9c3f81bcd431e7b84f33188700000ce85bf1e51000022548a69ae020389310c1588ed1e8060c400011744b8a29a49199dc03888025c3d798db2b426298f290a3b37ae4104a420ad23af804d46bc1e013e4e00013d423b14da400001619efe3a9066d0000160e1b380af52e500003d120000349000000000000285800013d673d000011372d6e13c89d3800000004d380001d6300005fd40001616000000000000fb0000000005dba65200000000e789df6000000005a2800040ca0000cec1ebf41a400008608da341b21e3d3048000000054187478744280841d4cce80004240000012f8a28000016fc61006ee18a44a4c0000ba704ea0000e0b1af4034c0bb80c2800001fa09901aaa4ae1ed22b94c388ebd491e00013d2052c2ce492a85821dda20c63184e6a13be2b7a01e892e0d8e29ca0000553258b01201920d2285571a542bcc1439ebe3f18092ce1607ab0846128c4318bd7258a000012682780d401c28403a02c2ec2441c9b384d6007649e91d80c6819da15cd11085113ffc45f846921c208c889490630000142696302559510127a4134a3b21e20b82000052b8d6c138e26b
  | 68 => 0x9c00011f33a0a35b8b3c18f622ee985c93f95b60e9e3164a2b8b6c3f7042acb9a8000000000009000000349000004778a7e000000000000edf2f4a3d54fcda30636e4643ced08e4737d412280f6823b38d40000b1b145f118e7f1846288f13e6246841ee14ff38042e5072c86420bba1b4c57b0fd315642dd06128667182894581a7a444215498bd196191f25d860f80af809d4586463cab227453e3291d015380002c9c0e5c6ab946020620c50a25138b401a09300e8a5ef00000000407000027fe2ee11f4162a30826b481c12781477c1a7ca8527d5446a8a546a0000000000000000143a4c208e44688800000001ed47749ecc2d2a4ef44c81ea1477a207c856028d2a2860cc8a9800008960000704800000008320def99b515a8368116682f2084800006479603070c38d0ec78e50275c879016d80001cca04150b6000023ba0000339216500005ba0997875d35b62660f2480000000322124300000cd84554f000000000000012f0000012a200000000000000088b81930187000029e8b781297399076bcab6823510001938cae17bb0c247c20be50a98000059600000d9900000000ccd13af2b2662706228ec2062256d057e0396139a11bcf4fa3e73a6c591cffd104721c000000001bed000093f8b048b290d58000000019574a3c66e45c300002cec00d000000003d68000000024462da200008c708651ac06a5cedd00003ff6558cb649f594b981530a4d2184307e940823b902c4df0000000000e905760000000000005a6426800024e836943a6c000037840503d98f07044a10802f803e2a5332d0c710c3e126513c4a8bec5f080f245d274e443c9b0532620000b9e9e4d1b8a9eed1712525470631104f780eb2a3c02a4ed307e82bf4200c609234f288e765c59f17b9362600012149c9145803408e5b8a54002e72683398cae43327e50a4680f41a8819b4d9910a001564a30ed1083b4b4e14947cf22482c7885ac1da938537e065f4eac1cef43fc8a487a1006c26242a50f8c167924d80000cf494b447c06c348ff88d5000055d080a1fc111485968ff3800009ea000116919223f346f480001bf30b0e4c111898d0523e41fe8be901b700004ac865f006f2c3e411800011b52a8c353837e9de31b125c98e7a88a648582fecba91f0a000012bcdcaa00744ae99601b08000000010c000285332e620f8d3bda238365a7ef000020e545fc1240e681ef9013633245e28fec00007c5c00001dd3824523c156a7d3096220d88251d7326888e64e0c15fe07ac94a0545969e06cc401c003a4100bb080f0a25902a2acc7578c3291b24dec00001e604a503246ac108d98970cf0979d31c260b09a642e4ec302c82f60189800000003f8857545a8060703d67ffc00023d92d6690345e60000312c10290a3005f3da034b9371a79f19ce0000000000
  | 69 => 0xb10ba040a502d0fc621442fc082ba48713e6076c6bf858a1f6e9f0827c92231de827750a60cd84c3c485cc9484951912471137616aa2fc88358c64a5f344001e8112a90f221b22ae010518a3156a04653e4885f1244549c37f990809244a90a78000017de1fa400024452a9476f469207cb11c886347cc864c12484884a588cb82a5c0000960880900000000000032b2ae6128000010e7000062f8dca090720507c8d0d105520000000063da04b0000928c89905dc413e77587d2a43a22f096fd16c800036f000003c50000167442bc486800019d222947109ddc27fc69f8a47115e08f69b20b8c0de900002cd490908d047723eb8b299b1b0000453d220035104b81dd93c213ca1a5a6b507b71b214b363dcd3f8260f3b7c5578796000012f8050874380004ae261512451c930bc04464862045a00000188f2ba2c9263e65080000e3512669fe880a804d02ea275c70096a7004e4258a73042838c63304b7f11d33dd610b0388224934e465503ef922a10327c3c14c956c22ae3cbce7c0c0b07760000418881a32c40c0cfef9b2436ee61b0032095a375a31452d984593eaa975c56185ed3ef23948a7e04e73a0e55647568b7c024484f099909b60db22becd8e0b77441252a85138a8d139e1a6cc0fa2b4035082690e186c3236244883e4004208220000c6b9a6f2f426bf44c898584dae28c83489d6c15dc10e818219704e0281a00920d71357a22b862e9bcc217c0110ddba06d02643278de48f462dac7100b7c85cf1d804f68a34874705a41f5414d8c66320e132c4ef0d08299e0ffc60300003c9897b4d9ca0bb2d1426651119b57334a00004ed1b6a000037b813e895b116058649661fbe22902cc8c23121a3fec773800000001aa800007d40a0d2aae000000012722d2e5e30000000000008c5cd91835900003bb08528dc829ba3ba0d049d880a6a00000000b76225e4e3400012fe339e93982f19b1543b42f6109204fe2c2a41a07d991b7297869ec99403bc35485dd037884d038068690d9da566297e0ea8b088f3449749b8912983fe1eec4f5c53c867b387e398c1c618b328461334209885a3cbe24b924721253fdc3bc833c8f0d02ac8b99267949b108e318c000016328a800844a51f780b7029bd3401ace292407c8bde098e4aa420c89ada2f034aa00000001c5e25466e2854e8965000064a06e30cf313682ab482226324e3c63d497b140617509375121948828240000bc90a14433435304a8014a1fc26ce0000229e36d20000000000011929a08c7a0000097a1e552f8190d23c654f41451fbb318a36e0c969cd12102721000000004c564a540000000000000002d10000000085980000c7300009ab51eb9935142c9e944a300000000068121580003aa845b09bb175d2a980000000000000000000039800000003770000000000009a
  | 70 => 0x3dc3f98b070000802c57d027646607d38819a1f10ed45c30716955a2d7600000000aff0a0400003c609b3268463813b28c7c4ba46f5883f9a284b8c31287231e3f145451e12a298c6185e8e2117a111c4b4a8abc09b0fdb000072b42838b96406c615930c8000203a0000000064705f400006209d0c3f5c7b202de94a41efe04cc0000000486600007e38c9b0000000016500000b90000129a9eda000000007b2207000002fb8000000026da29a00000000186086f056c000004567b980000000031094046529a9f3c2638a9392a1133eb849bc76488fe4b24000000026c5187a2e0810c04330e944d78eba82fb48620000000275b49ac0000000000000001f2800009f200005fbc00017c2000000010ac03a64f8e0000bcf000000000000787117f1aea00005f497ba1d824e0cd03000000000000805a0dc07f06ad0565052411f68f2050a9c2d0b9c00007c61f2c05b400001ad800031e200009ca217235f8000028b920d076851780a70ce5042c40448d7069c25c41c5098a000040ce278000000000aaa87c0e70000013f866bcddaa51044b894a8a0d976c02281d5c6781f3e46026e34ea6a3ad08e28d986171b410000830d08c208b45aa22cd2499b903a5a3fc0376000001901d348e8937c0000643069c1f57232486dc7511633000027f8e8419ea225a2f540e296420e6a0000706a15c324236552761dc314b4444081f1b2238fc23c111b800000003b5cf8927e23fb653f924196ea00000100a8d96b62bda020854e00000000473088a0fde3ba689c400007d419fe72b8df79f5e48b82d4446315c81cec8854dc495dc26b826ecd7100dd4ff0100537080001db21734000178004942de800001974d6a2cb1312889f01bc5d60000000000000000cb3a4ac000056cc3150000000073293038c47000000000001a1508aa0000000197316f60000000191e165053b01c1800021ec0000c2381ac080c5c8515d0ecf26004b64fb90ac73bfa6dd423f8866225c917c3a08d650a28264d1f70f4820a689e072211241548862c5fe0da61b16587905392ff3e3e8d788e700760000063400019a0195491e06481df14fd6683505616bd03706884cea92942e3a1dc8c929368141c2fd8301973f1e3800006360a3a06a65dac645800030860f04000000000006348a13976d0c3a6cf83802161082800008679f8619862b98c588000000000008f307b32bbe313437b257c1d387240000240b2f529ed86a8922500009b541f080000000622d1701d903d9e9428d929eb3265a9774740a0881b923e444261d350000733c000030d26b2000100a155f26c6668c8cb0f411f42047c00014212c9a71945010f5d3f8a8724ef311f4222e808437c256c33a844d86af9301279a24051c4a1111d5e137c42d839f039c60945b4130902ce96b0c089d3811b6653cfa781
  | 71 => 0x9c8177e53481c800bb0e8a26a8eca21792a481c3ca86812e294c8c54e9b81c8478a2bf89f507b844266008378252f4f940ec45ea1ba348a274d03658777427e5834f900d4a206442b8f119bb823c071213ae211c1e044c18f4527412d8a6c1cd53122e48b2764422496521ac875e52d2114309e64078b250b00407e95a8afea05e427c29382298b730d121598179a41f4e8e97e09ec92ce303206c078b9e4a037a6774f9094a8084a2c485be9d5601ae81283e6a1e81990775400003242fc455a40081a4148d843f8000000000008068fd997f720a0821c162155441785bd1166000049946d750391a631bba5d54dd89eac037e000103b9e21299c948413800d910d42c2022b80004e6a3c2c000220e11e86a880001219262a2d305d3000000003800bdf8dae4f140000ce1893c2ea200000000000011a373066e0000000000000001f6e332e2678ed9932122263bac97d1afb0e9c1bdc6469f541a8c0cf4d3ea42f000031fcd8ba1e00752386cf739793301a2e2400000380dc6926cc95800030fc3d58a5b80002e1a646d1ffa34d0c667fbd0f2883f2c2477a820680000c1255dc997185046ea99a4a3298a01cb40001350a3ef00000b186a481df0000000099b8dc44c24881400027ec0f32083cf8e085d3a9c00012d91e5035e63aa03ac198a4fc07aed24f800014301c64011800000006a000708000000048a53460ff347521b200f094b21f80248c44580002eac856400019a22e6c1268f991ba733e07da0b8a92bd39404060ad38760389627903869c22283233d000027402730039000018771cae0000d82033300000000000000019183768000201e21c294e49dca6670000000060e000000005978000013a23be992c9fc80003486000096e25a236cc7e0c0001bbf00000000a14964b03ac0000c59016f1d580000bc09b70141e31800001f61019800001cda5ee137000000001b31417c00003dc91944bee7ff440e816b0282705ca99935a00005231388000039964ad8535000046961c14a57a06a3b1813a40ac8174000000010700e832dec18b92298dfb0000789900999c535363e54e4300f927628c58fca800000008c2028ea264337c00009d917ec0e928fd000000004c901ef85b684bc33889cc806a91ca2592056cf47811d000022d109500001dce00012539a192cc41f78000000000006144dde000014f854f0b3f949e019e9a580001bd01bac4d348098000000093cc00023c62bdc0000ab7a62c0e72000000000004d9e0000b9a000048a01360c0c19633190265137d03e7045e36e872f1578014452e129c1d3c2cea51607180acf45d422347e702b539f856c4e57821d28ac685c4a78750178059704b1231d005422b0b8008af043e1378acaa615365e85c091f230319f62ef4420907e2332306c36d8bff4f228e8054409390b1a0
  | 72 => 0x579cbb884c309500c94fd81da738e21c30b898bea3dbc000089e8dfc254c710531407243a3e9890fd7841523de000137a98bc0000000050e800010fe7c0c7bf000834fe42dc4df88e6000000007e4000040f083f4d780c000b020000c3504730000000012a951d48f845e800011d81ae099d4d7a99754f4449080f720c404f89e00bbaa10e0ae087a51d40d01258c079855ca0351b0e59a0d6080002cb695dc474202e139800001b1000032322cb922d00001cc2100120e81b42dee6004424000004b28e90106a7ea2d641e9d01698383f1038105d707bf03fe616521f0b13043c04bc3aa00004d7887506a80d72374a59f52441f89039819a8000000032e200000001a6e000039510e4042e1444000000000000c20000085080003fb062013940da523ee6afd1610f9f22540a4ccde000032603b350d8094422f614bccc0168021e87ce9350124c1d901acc000198b3f842d0400006ba35ca4ee800009573ff883b45160c64357c2a8867e956e214e06389a98ecb12048fac83c0f4d0522208caca01c31fee82a05d78f26146c8f40371255f3c3808a41f915e51d102460e3792df4afc0fc46160fe038665cbd3d08ebe2d0a0000fb9a3b211962db82a80e60233e467485b231f04d80e8800022c50fa637986e38df84e2c20d053a14743eb0489d3e68eff3254221cf999d3a0d9a17fc04e1e342f6a6dec341272204006e9064922da36ac8b193e897703e98350c7701a9122564f4000019b200008538dd0187614a433e1300a089133e3cdc85d0cde47b834d822d80e8460019c49898aea1b088a690fa9813451a0b2c396873731d8519834f00d30000766921380000f4403c4a2ca176086c5afc3779df00d0653ac0001ae71ed43eec5b318af250462a0fba15d7287c78cca29076201508a30000212633d056a000012d800009064eff8a9b00b620e904a94f538dc00c107a0000303400000000aef32003aec000000041926f0519d800046f20000e7e97ac23c268ec57186d2398a079ccfe87792216000000015d600002ed4fc2a07c30946a780000f300fe48f3c2b391060bbc4ce855b020507801a590ec9ec40cfa95b508414a12d845c44d5b1995000000007fd18271f4094c4a48994a0b64769060484be04ee7248c3c04d931d20a89068a33d413259442058e3641706c046ae8d8334f067644bf883c4ab40f4c1ca116f2c72001023b09fd42fe7958a8122be1ef82aad20b1b912d525570d6892a200006644088000000000001322000033be21d00001213000000002870000000081c4f048fe526d21ab454f80002d1a0b8400009cb00008d003b2a56f471e921062a03cf1c6642080d3800042005ed88720f112c0c59181681750374c5b909a892c446f0292538d278248ee714135c11cb0eaa82e52ff192c32dc9080000000044f8906cb179
  | 73 => 0xa69a113090fcbe9a1e128e4054875b87901a6e16306401d134fbc187129b8b0f10041a5532104c21bea163d03b1ec73f980604000083935ee80952e1180e00004dfc3708283277682480000bf505ac50347ae0fa2000078540002674000000010008e251f880fa0c05089d3ede8c44eda19aa078c0674036a5c90000000043b9c6200001de0efa000038c8190070e8f103e5c4e584bb8529000000005c589c20a140000e0807bd2dbe0e78ece9172128e585103a092a273895608229dee2b3220f4a66245d2d38089d01881fb0000000cfed223c1d3e000013797644d3a95006fe9c000f1a0fa849a22a24b8241b01b58000027a85d4e5d0dfa3f7e7588dc1823205bc2dfc000077100008a7c6ad00003484000120707f900008238000088900003488000122d069a2af476c2075082407d400006ca1b84000019e0000465c454460b800027e418102531b6f2718607438705b618149fa00309d6b2f0c1fb48ea0de22c38187875d1ec92972230039f00000000000000012843576522c1fc800045bc0000fc223b83268796c65ea4821d480950152a767253a2955029028e09aa1690090a53242088ce4b5f18640e3096e4685800047264ca80000308000096641db000000005000ca9000000005b3097b9baa00003ed4f6c98a400000f2c8d80bba000026e80000b210eac4e40b80a5571c984dcc0000d942f280bb015180002766150c00007262f7c0001194004119462f8864327371a385b6c79e9a46148c0001325215525bc70e8000128b000000000001ac400004e680001bab43f630e4cba2495000000006dc962c0cd20fd077b14a23cce928400b1ee84556867c0000d18275074c409e273a3ef435d8643807421ae00008e49d592a640520c3780241c0a2bf4b8e23f615600000ac3179f38c0691d3ab86da0ac467e80000b4423da0000d7c91253ef64cc006a20e341cc8eec1e4198f2bc242293238768000038f03551bd941a67601051800049289f944c58ded28fc15e4a1801bb0000504c82a928a455022d89f300004ec451706678000000036f80000a061baa2c944d0a5d329a63db1202000004b003b0bed92a0071a9860295132b2a726fb8cb09cc603d02b206d688fa2a821b0400023ec2ff85fa02c8016100000df80000426000003d484f000020e6953d30624e7218a3e70ced035e24d442f43b30086176c14dc81c1815015897984ac8f3e4ecc608c30c80df0000000000000000000000067d00003d027e28271124310dc5410e1b27ce0118122c000259f2d6a000020e0d6a369a000088d83f009ca3b75002800043060000000000024a087d8c031df200000000f9e263f49825c2cf6526e731d4000102788830ae80a74eaaa6a9135600010a180004a8800011f81a3605e09b98ecda269130a1804bd88edb4932863020c00003c2c
  | 74 => 0xc000017b08c2285e5cb45bc1f301f9a000000011733c7a50cc53e9d3224600000c0f1e6b0000370c7968000472c27d464504341fe25df0ae88000146a50aca359aac4fc884ec3a1a0640e2213fd06d88bb28020a9821f111107029c44a6426c1276e5aa08061cc110d25fcc9f0800044b650c4000228800007cd916422ec23ac5a100001f2f4a7c4160b991d843c96682d1341a6a40548bdc1b724f619968010c8226883abe344d0a812cf1d305cb1272952a3f466bad378a4e926a465d865b88bd1b9695f4e6c00e50000851000020ce0000394ca779b8100004974cf125bc00005874b3b94254196662023a20ae00007c1c0000000480439603e4804c1132969834e9600004a000012200002d4a43e4b75800012b0977929687fc49f679690638139197e62b4000189b16349638a071c82366c06b4586a53c2c8000002488e07393a05b800013db0e3e000044f000036f480400000f5338b40000ad69f2b439c13a8ed717fd47bc0000ae380003cd44f38dfe12fd09e273c8000000023b62680368800000000000baf9a9637fc87f0f1690dd0000000012e8f7000008b9c9479e3a3db60a7c9c4920a25201fc4ead17c3417a8064f8a9a2f2ac439b4ce7239f2e049b3507f831f43ae78783ff902e217e547078319ca2298442848b26933bc8521c86388642034673535f8c152b4c42b4dc38adb4e5251a80a3900107ba50b077c854d4a3e1754987275635404840afc900d29d00160ffca0ca22fa9a1835e000002f4144068008e72bd8019c0000cd200007874783846a2e121d7871595e43a9e87546d498ce26940e6131389d23ae248ec6711c2411b018f4f13823c2a4c4b5416c9a7a274a0870f112343000078090511aed02d05dfd0ab812511466ae4ab911f6345278a517c1fe5127e762c5240870000022110e90c53000090e425624972b3010691f182950f8c6910b4d85f1077a05f4878076349d60000cff94da4ae05bf400026d048760000000000011002370999882546d4437017a840802960edcac516a61282393402290900000935537290c22a3467c429591cf3cc825d0000170a0000825d22b800036d0000081180000500157cba390262eb869001ca88fc2f5600001e6800000006ebd28a20e44d4869c000014643d785df90d9000000000000dc000002fb2143cfa4860810a07a946d606a84c72968c3a58000177c7f9800002b000000000000062022c221a0fad8b092cc254dc00000004bd097f0d591bc817a600002d0a35a11dc00005818d0e27ec000000000000510654539a0d530000124c58700000000000128a8f8802a04260fe71356000032e8193a7b1488e96781f79edd2c5c83f8c7c00003c282a49212800000006d200001d494fc673a8000017f3e1299387c50655260e09a1012023a09f83e40ef4241224586f6c1ab
  | 75 => 0x2b103cd95523c9001ec929a42a462841ecb568a4244ac897d0a7a2f647585c14a95887b4716928056ca49a4036448caa6a11944d473643808e0f416816500001ec50f0e8d800000981274c09e400003401c3234d05ac99771e0a6384e03944c2ef25ab8b44a177000037c46040000000015bcc4127db31a0074c43e8000000024b038a800034ee83142ea168b3b9a725c8a200004ba226a1096153b00002b448101d2f44664aec000000046b09df4f5b0a7b09a40000e4aa1dc0564000000000004cee2c5445480000db0000000025820fae7b08000000000005ce4ac2985300000000f6e19060f465f74880800024a47b4c158800000000000000000000000000f0922dd443c9c6088d01de0ffc5c3c26d80001ef000000e223a700000000f328000000034ac000061a1fc66c209f216fa00000e705811473224e7300e7f1d110000727000023b400000000c4c824938d691a53a6241421be4d9000003344cf800000000000414200004a7152f230025488ef179933a62f20b2b1b062d82576137210a81c505f684a28bb1302400681080000000000007f70bd61ff825a439e1b933f1a88980000a3000ca8ff03a109c505561f6ca3711ba0b844024add80003e1a04e0000054845c8488086706e52e803aa400023511c8a0000fe8016d4bd6798c69e035c00004200bbc0ce03a9893202da842135d249acc1d0000000001a47688ad5223a4b4cf300cac02b0615d3af077e41525d50e6616b134c28b290f68eb2404c00000001e8534b8550c127a76849a010e058809b03d5c67c850c924b1e40000039c071d0000000088780000000617d1f91d6600005a3d1a4898d0000000098d0000000033a0bbb093236300768c9e06de00007be00000fd7040888a06d91e8427f40b9d2da263e0e088a8514da31c4d4a96e07891c6141d6000106600003f6c000069a9a7930125e0c062a7171af47a88e4f98034976000092880000000000100618440fba00000001a0f00000000574a27b01b8142000000000f2c7064637a3c3241c16b8cf5a7ed40cc502074204fa2f6823b07b596ed03ca89ad08f044800000ff13d609c64a962cf4944096a25583d49224000034220000ce624f22cfc8a0c000000045623de483326d9000060e4da013454f0
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x845d7598c200430f2a4c6100218755263080108beeab18400861e5458c200430eaa2c61002117dda53080108baed298400861e6494c200430eb24a61002117dd953080108baeca98400861e6454c200430eb22a6100218b9925208010c5ac9290400864e639482004326b1ca4100218b9915208010c5ac8a90400864e635482004326b1aa4100218d9526108010c6aa9308400865653984200432aa9cc2100219954a6108010c6ca8b08400863554584200432b29ac2100219554d6108010ccca4b08400866552584200423aba8c9880211d5db54c4010aaae7aa6200856572d53100423bbb2a9880218d99154c4010c6eecaa6200863476553100423abb6a7880214d5d353c4010acae5a9e20087155494f100438b2a2a788021c555153c4010cacc8a9e20086546454f100423abb6a5880214d5d352c4010aaae7a9620087255494b10043a2a9ca588021c995152c4010e4aa8a9620087465354b10043a2a9aa5880219999152c4010cc8c8a96200847576946100431cb2ca9080218e5955484010cb2cb29c20086596554e100438caa2a7080219a5965284010cd2caa9420087295454a10043a4a9aa5080211e5da518401087ced2a2200843c76951100421f3b2a8880210f1d95444010c3ec929a200861c6494d100430fb22a688021871915344010c5ec9292200862c649491004317b22a4880218b1915244010c6ee9b2a200863474d95100431bb2ec8880211d5d6644401096ce9322200863765191100431aba8c8880211d9db5444010c68c9aa2200855573d5110042b2b96a8880212d1da5444010a6aeb2a2200863765951100423a3b2a8880218d1915444010968ecaa2200863765551100431bbb2a8880214d9d95444010a68ecaa2200863476551100421a3b2a8880211d9db5344010a6ae9a9a200863464d4d10042b2b96a688021555d65344010caecb29a20086946494d100438aaa4a6880218d1915344010caecaa9a20086946454d100438b2a2a688021c55515344010e2ec8a9a20086566454d100432a322a688021c51915344010c28c8a9a200847676d49100429aba6a4880218d1935244010aaae7a922008565759491004333b2ca488021a91925244010e4aa9292200874553949100431a322a48802199d955244010d48c8a922008726545491004392aa2a488021d194d5244010e8aa6a922008727645491004333322a488021991915244010e48c8a92200862464549100431aaa6c0880219554f6044010ccaa5b02200863464941100431dba6ca880218e1d36544010c76cbb22200863b65191100431db2ca8880218ed955444010cb6cb29a200865b6554d100438caa2a6880219ad965244010cd6caa9220087295454910043a4a9aa488021ac19361440108f4ed28a20087315494510043a8a9ca288021d854a5144010
  | 1 => 0x400431bb288320021c554c4190010e4aa420c800847771d95400431b2a6c2a00218d5536150010caca7b0a800865553d854004333296c2a00219954b6150010c6ca830a800863554185400432b298c2a00219554c6150010ccca430a800866552185400425b3b682a00214d5d74150010c6ecba0a800871553d054004392a9682a0021179cf65100108bae7b28800846e72d944004236b96ca20021179ce65100108bae7328800846e729944004236b94ca200211d5c565100108bce6328800845d731944004237390ca200211b5c865100108baeb318800861e5498c400430eaa4c62002117dd56310010c3ca8b18800861d5458c400422fbb4a620021175da53100108beeca98800845d7654c4004236bacc4200218b9526210010c5aa9310800864e539884004326a9cc4200211bdd56210010c5ca8b10800862d54588400432729ac4200219354d62100108deed290800846d76948400432731ca4200219358e52100108deeca90800846d76548400432731aa4200219358d5210010c6aa9308800865653984400432aa9cc2200219994a6110010ccaa5308800863654584400431aaa2c2200219594d6110010caaa6b088008666525844004332a92c2200214d5d44110010c6aca208800869563104400438aa988220021a95884110010e4aa420880085b170104400431aaa4c3180219554e618c010ccaa530c600847775586300425a3a2c3180218d551618c010caaa6b0c600866552586300421f3a6ca180210f5d3650c0108dce5b28600846d72d94300421f3a4ca180210f5d2650c0108dce5328600846d72994300423ab8aca180210f9d0650c01087ae8328600846e721943004236b90ca180210f5d6640c01087eeab20600843f76950300421ebb4a8180210fdd9540c01087aecaa0600861e6494c300430eb24a61802187991530c010c3ac8a98600846d7598830043172a4c4180218b552620c010c9ca7310600864d539883004237baac4180218b951620c010c5aa8b10600864e535883004326a9ac4180211bdda520c0108daed290600862e649483004316b24a4180211bdd9520c0108daeca90600862e645483004316b22a4180218d952610c010c6aa93086008655539843004333294c2180219954a610c010c6ca8b08600863554584300432b29ac2180219554d610c010ccca4b08600866552584300431aaa4c3100219554e6188010ccaa530c400847775586200425a3a2c3100218d5516188010caaa6b0c400866552586200421f3a6ca100210f5d365080108bce7b28400845d73d94200421f3a4ca100210f5d265080108bce7328400845d73994200423ab8aca100210f9d0650801087ae8328400845e73194200422eb98ca100210f5d6640801087eeab20400843f76950200421ebb4a8100210fdd9540801087aecaa040
  | 2 => 0xc2190211e5d6600c810c74a9300640863954980320432ca9cc0190219a54a600c810c74a8b00640863954580320432d29ac0190219654d600c810cd4a4b006408669525803204364992c0190210f9d2639441087ae931ca20843e7498a510421eba4c5288218d9d165d0410aaae7aa6820856572d53410431ab2ca9a08211d5db53d0410a6ae9a9e820856572d4f410432ab2ca7a0821c555253d0410caacaa9e82087165454f410438aaa2a7a08211d5db52d0410a6ae9a96820855573d4b4104332b2ca5a0821c955252d0410e8aa729682086656554b41043932a2a5a0821c955152d0410e8ca6a9682087455354b410431aaa2c1a08219554d60d0410ccaa4b06820863954582410429ab8aa8208218dd954110410c6acaa08820871653504410438aa9a8220821c99494110410e4aa4a088208659539804104334a94c0208218e9516010410cb2a6b00820866952580410429abacc8208218d5966410410aaae7aa0820856572d50410429abaca8208211ddd95410410c6cc8aa0820853776550410431bbb2a8208214ddcd5410410a6ee4aa0820847576d4c410429aba6a620821595cb5310410aaaeb29882087155494c410438b2a2a620821c55515310410e2ce8a9882087157454c410432b322a620821c59915310410a6aeba18820863565d0c410438aa9e86208214d5d54310410c6acaa1882087155350c410423abb6a4208214d5d35210410aaae7a908208565759484104392aa4a420821d154e5210410e4ca8a9082087255454841043a329aa420821d154d5210410e4ce8a908208725745484104333322a420821c99915210410e4e86a90820872543548410429abae84208218d5974210410e2aa7a10820872552d08410429abaa84208218d5954210410e2aa6a1082087255250841043a8a9cc020821d854a60104108eeeab00820863554580410432aa9ac020821995496010410d64c8b0082087515358041043b0a92c0208210fdda54cc41087aed2a6620843f76553310421ebb2a9988218799253cc410c3ac929e620861e6454f310430eb22a7988218b99252cc410c5ac9296620862e6454b3104316b22a5988219654d608c410c72a9300620866952980310431caa2c0188219694d600c410cd2a4b00620843f76953210421ebb4a9908210fdd954c841087aecaa6420861e6494f210430eb24a7908218799153c8410c3ac8a9e420862e6494b2104316b24a5908218b99152c8410c5ac8a96420866952582210431caa4c0108219654e6008410c72a8b004208659535802104335292c0108210fdd16194010878e8b0ca00847576106500429abae83a00218d59741d0010e2aa7a0e800872552d07400431aaa4c3200219554e6190010ccaa530c800847775586400431aaa2c3200219554d6190010ccaa4b0c800853575106
  | 3 => 0xc76454810ac8e2b22a4085647158d52042973a0c6a90214b5d06354810c9ac631aa4085667118d52042b5380c6a9021599c64354810acae321aa4085677150d52042b238a86a90214b9d06054810a5ae8302a40854e7318152042a6b98c0a90214b9d01054810a5ae8082a40854e7304152042a6b9820a90210f5da541481087eecaa0a40861e5498c520430eaa4c629021879516314810c3aa8b18a40845d7694c520430f324a6290218759253148108beeca98a40861e6454c520430eb22a6290218b9526214810c5aa9310a40864e539885204326a9cc4290211bdd95214810c5cc8a90a40862d64548520432731aa4290219358d5214810c3cc9318a40861d6498c520430f322c629021875916314810c5cc9310a40862d64988520432731cc4290219358e6214810c6cc9308a40863564984520432b31cc2290219558e6114810c72c9300a40865963980520422f39ccba1021175ce65d08108bce632e840845d73197420423b388cba1021179ce65908108bae732c840847571596420422f398cb21021175cc65908108ece232c840847575986420431b2a4c3210218d5526190810caca730c8408655539864204332a94c3210218d9516190810c6aa8b0c840865653586420432aa9ac321021999496190810ccaa4b0c840845e73995420422eb9ccaa1021179cc65508108bae632a840847671195420423abaec2a10218d5536150810caaa7b0a840866552d85420423aba8c2a10218d5506150810caaa630a840866552185420422f39cca21021175ce65108108bce6328840845d73194420423b388ca210211e9c0651081087ce932e640843d74997320421f3a0cb990210f5d065cc8108ece232e640843e74996320421eba4cb190210f9d0658c81087ae832c640847671196320421f3a4ca990210f5d2654c81087ce832a640843d74195320423b388ca99021531c9534c810a98e6a92640847575d85320425b3a6c2990218d553614c810caaa7b0a640866552d85320423aba8c2990218d550614c810caaa630a640866552185320421f3a6ca190210f5d3650c81087ce9328640843d74994320423ab8aca190211e5c1650c81087ce8328640843d74194320423b388ca190211e9c0650c81087aeb320640843f75590320421fbb4a8190210f5da540c81087eecaa0640843d76550320430f324a61902187592530c810a9ae5298640861e6454c320430eb22a6190218b992520c810c5ac9290640854d739483204317322a4190218b591520c810a9eea990640854d754c83204327b2a641902193595320c810e1ca8990640870d544c8320423abacc2190218d952610c810c6aa9308640865653984320432aa9cc2190219994a610c810ccaa5308640863654584320431aaa2c2190219594d610c810caaa6b086408666525843204332a92
  | 4 => 0x9ce4304a60854d72182530428f3a6c6a9821475d36354c10a9ce5b1aa60854d72d8d530421f3a0c4a98210f5d06254c108ece2312a60843e74d85530421eba6c2a9821179db5454c10a9ce5aa2a60854d72d51530438a38ca8a9821c51c55454c108bcec2a2a60854e7215153042a6b90a8a9821559c76454c10aa8e2b22a60855471589530428f3a0c4a9821475d06254c10c9ac4312a6085567118953042ad380c4a9821479d06054c10a3ae8302a60854e7218153042a6b90c0a9821479d01054c10a3ae8082a60843d76950530421fbb2a829821879526314c10c3aa9318a60845f7654c530430f322a629821875915314c10c5ca9310a60862d549885304326a9cc4298218b9516214c10c5aa8b10a60864d53588530430f324c629821875926314c10c5cc9310a60862d64988530432731cc4298218b9916214c10c5ac8b10a60864e63588530431b324c2298218d5926114c10cccc5308a60866562984530431cb24c0298219a58a6014c108dce532e860846d729974304237390cba18211b5c865d0c108ece232e860846e729964304236b94cb218211d5c56590c108dce432c860846d72196430423b388cb218211d5d66190c10c6ca930c860863554986430432aa9cc3218218d9516190c10c6aa8b0c860865653586430432aa9ac3218211b9ca6550c108dae532a860846e721954304236b90caa18211d9c46550c108eaebb0a860863554d85430432aa9ec2a18211d5d46150c10c6aa830a8608655531854304237394ca218211b5ca6510c108dce4328860846d72194430423b388ca218211e9c06510c10c3ca931ea40861d5498f520430f2a2c7a90218755163d4810c3cc929ea40861d6494f520430f322a7a90218759153d4810c68e2b26a40861e6498f520430eb24c7a90218799163d4810c3ac8b1ea40863564987520432ab1cc3a90214b9d35294810a5ae9a94a40854e73d4a52042a6b9ea529021539cf5494810a9ae7aa4a4087247155252042a7398a929021535cc5494810a5ce9a9ca40852d74d4e52043872a4a729021c35525394810e1ca8a9ca40870d5454e52042973a0a7290214b5d05394810acce3b24a40852e7418e5204296ba0c7290219358c6394810acce231ca40856a7018e52042b338c8729021595c64394810a5ce8304a40852d7418252042a7398c129021535cc609481087ce831aa40843d7418d520423b388c6a90214b9d36254810a5ae9b12a40854e73d8952042a6b9ec4a90210f9d3615481087ae9b0aa40846e76d5152042a739ea8a9021535cf5454810e48e32a2a4087247155152042373b0a8a9021539cc5454810a9ae62a2a40846e76d4d52042973a6a6a90214b5d35354810e1ca929aa40870d5494d52043872a2a6a9021c355153548108dcec29aa40852e7414d5204296ba0a6a9021599
  | 5 => 0x863454d85404431baa0c2a02218d1506150110a68eaa0a80886346550540442d838282a022187d526310110c38a9318808861f5458c404430e2a2c6202218bd526210110c58a9310808862f5458840443162a2c4202218dd526110110c68a9308808863754584404431a2a2c2202212d5da4110110a6ceb208808863665904404434ab1c8220221a958a4110110c68a930e60886345458730442aa3aa6398221c515131cc11087ce9b2a608843d74d95304421fba2ca982210f1d1654c1108dee4b2a608846c72595304431a2a6c2982218d150614c110aa8ea98a6088714544c530442e838262982210fddb540c11087aedaa0608843f76150304421ebb0a8182218bd52620c110c58a9310608862f5458830443162a2c4182218dd52610c110c68a9308608863754584304431a2a2c2182218d15261c8110c68a8b0e40885647548720443922a243902210f9d3654811087ae9b2a408843f74595204421e3a2ca9022117dcd65481108b8e6b2a408863454d85204431a2a0c290221591d52148110e48a890a40885e070485204421fbb6a8102210f5db540811087eec2a0408843d76150204430faa4c610221871526308110c3ea8b18408861c5458c204431baa4c2102218d1526108110c6ea8b08408863454584204431ab20a9082218d9d85484110c6aec2a4208863454d8e104431a2a2c7082218d1536284110c68a8b14208864e6398b5404326b1cc5aa0219398d62d5010c9ac6b16a808655639875404332b14c3aa021479cf5495010a3ae7aa4a80852e72d525404296b96a92a0211d9c663950108ece3314a8085367198e540429b38cc52a021479cc6095010a3ae6304a80852e721825404296b90c12a021479cf6455010a3ae7b22a80852e72d915404296b96c8aa0214d9c66355010a68e2b1aa80853671989540429a38ac4aa0218dd8c6155010c6ac630aa80863762185540431ab10c2aa0218d1866055010a3ce6302a80851d731815404297390c0aa0214b5c86055010c68c2302a80843f76550540430eaa4c62a021875516315010c5aa9310a80862d54588540430f324c62a021879916315010c5cc9310a80864e639885404326b1cc42a0218b9916215010c9cc6b10a80864d63588540432b31cc22a0219558e6115010cccc5308a80866562984540432cb1cc02a0219a58a6015010c5ca9316a60862d5498b53043172a2c5a98218b55162d4c10c68e2b26a60862e6498b5304316b24c5a98218b99162d4c10c5ac8b16a608635649875304332b14c3a9821479d35394c10a3ae9a9ca60854e72d4e53042a6b96a729821539cb5494c10a9ae5aa4a6087147155253042a7390a929821535c85494c10aace3b24a60851e7418a530428eba0c529821935886294c10aace2314a60855a7018a530428f3a0c129821475d06094c10a
  | 6 => 0x24421fba2ca992210f1d1654c9108eee2b2a648843e74d94324421eba6ca192211d5c7650c9108f2e1b28648843f74594324421e3a2ca192210f9d0650c91087ae8328648847671194324423d380ca192210f9d6640c910878eab20648843f76d50324421ebb6a8192210fdd8540c91087aec2a0648854d7214c32442a6b98a419221539d5320c910a98ea990648870f544c832443862a264192218dd52610c910c68a9308648847475584324431baa2c2192218d151610c910caea6b08648866752584324431daa4c0192218e152600c9108f0eab00648863b54580324431c2a2c01922196d4d600c910cb0a6b00648866b525803244334292c019221b24c9600c910c70a9306828863774996414431b32ea920a218d1516390510c6ccba1c82885347550e414431b32a8720a218d1516290510c6ccba1482885347550a414431b32a8520a218d1526090510c76a8302828853675d91414431a32ec8a0a214d9d254505108ecec2a2828853676151414431b3b0a8a0a218d1536350510c68a9b12828863454181414426ab98c0a0a21395c86050510d66c8302828863454984414429a3aa8220a210f9d664cc510878eab26628843f76d53314421ebb6a998a210fdd854cc51087aec2a6628847675d923144272b96c918a211d5d8548c510c6ac82a4628863665152314431b3b0a918a218d5d8548c510e2ce62a4628871573152314429b3a4a718a218d151628c5108eeeca9462885347454a31442aa39aa518a218d152608c5108ecebb22628847475591314423b3b4a898a214d9d2544c510aace72a2628863764151314431ab20a898a218d9d8544c510c6aec2a2628871454d8d314438a2a6a698a214d9d2534c5108ecec29a62887175414d314431a2a6c498a211d1d9524c510a68e8a92628855473549314425aba0c098a218d150604c5109cae4302628863454984314438baa26218a210f9d664c8510878eab26428843f76d53214421ebb6a990a210fdd854c851087aec2a6428847675d92214426ab9ec910a211d5d85488510c6ac82a4428863665152214431b3b0a910a218d5d85488510e4ce42a4428872572152214423b3aec710a212d5d36388510c68a9b1c42886345458e214423bbb2a710a214d1d15388510ac8e4a9c42885367494a214431a2a4c110a211d9d764485108e8eab22428847676951214429b3a4a890a21599ca5448510c6ec82a2428863564151214431b3b0a890a218d5d85448510c68a9b1a42884747558d214431a2a2c690a211d1d95348510a68e8a9a42885647254d21443922a6c490a21c91535248510a6ce92924288476761492144393aa0a490a212d5d06048510c68a830242884d573181214431a2a4c210a21c9d512108510c68a930e808863454587404429a3aa83a02214d9d64190110c6ccb20c808
  | 7 => 0x698421535c8534c210c3ac9298610845f7654c308430eb22a6184219394d620c210c9aa6b10610865653584308432aa9ac2184214b5d052c8210a9ae629641084b47458620842373b0a4904214b5d05248210a9ae6292410862d649482084326b1ca4104211bdd95208210c5ac8a90410864d635482084333292c210421995496108210968e8b2e210853774597108431a326a9884211ddd954c4210c6cc8aa6210861f6398f544429ab88c7aa2218bd8a62d5110a6ae2316a88843f76550544422f398c02a221175cc60151108dce4300a88846d72180544429ab8ec62a2214d5c66315110c3ac6318a88852e7218c5444296b90c62a2214d5c46315110a72e0318a88853571d88544429ab8cc42a221479cc6215110a3ae6310a88862d62188544429ab88c42a2214e5c06215110a3ce7b08a88851d73d845444297396c22a2214b5cb6115110a6ee6b08a88853772584544431ab0ec02a2218d58560151108eee2b26a68843e7498b534421eba4c5a9a218d9916194d1087cedaa2a68843e761515344317aa6c4a9a218b1536254d10c5ea8312a68862c541895344317b26c4a9a218b1936254d10c5ec8312a68862c641895344327b18c4a9a21995c46254d10c68c9b0aa68866462d85534422fbb2a629a21531c95314d1087ce8300a68843d741805344237390c029a211b5c86014d108dce5b2e868846d72d97434431a2a4c3a1a211d1d561d0d10c68a8b0e868847571d96434423b388cb21a218dd526190d10c68a930c868847475586434431a2a2c321a211bdc96550d108d8e4b2a868847771595434428f39ea8a1a211b9c86510d108dae4328868851d73150434431a2a4c221a211d1d56110d10c68a8b08868863854980434423c3aac021a211ddc564d491087ce931ea48843d7498f524431b322c3292210f9db545491087cec2a2a48861f54d8d524430e2a6c6a922187d506354910c38a831aa48861f64d8d524430e326c6a922187d906354910c38c831aa4886557118d524432631ec4a92218d1936154910ca8c7b0aa48846f7654852442a639aa4292210f9d0601491087ae8300a48845e73180524422eb98c029221179cf65d09108bae7b2e848863454987424423a3aac3a12218d15161d09108eae3b2c848847671196424431baa4c3212218d15261909108e8eab0c848863454586424422fb9acaa1221171cd65509108eee2b2a848852e72d51424422f398ca21221175cc6510910a5ae42a0848863454984424423a3aac2212218d1516110910c70a9300848847875580424421f3a6cb992210f5d365cc91087ee8b2e648843c74597324431a2a4c3992211d1d561cc910c68a8b0e648843e74d96324421eba6cb192210fdd1658c910878e8b2c648863454986324423a3aac3192218d151618c91087ce9b2a648843d74d953
  | 8 => 0xb5348710ac8e4a9a43885e170d4921c429b3a4a490e211d9d852487109ccec29243884b57418121c426ab98c090e211bdd95208710dc242b00438843e7695140c431b2a0c2a06218d550615031087aedaa0818861f5458c40c430e2a2c6206218bd516210310c58a8b1081886375458440c425abb48220621a558e4110310d4ac5208818851d7494f30c428eba4a6986214b5d252c8310a5ae9292418843f76550548430eaa2c62a4218b5516215210c3cc8b18a90864e639885484326b1cc42a4218b9916215210c9cc6b10a90864d63588548432b31ac22a4219558d6115210cccc4b08a90866562584548429a3a2c3a9c210f9d06254e1087ae8312a70845f7654c538430eb22a629c219354d6214e10c3ac9318a70862e649885384316b24c429c218b9916214e10c5ac8b10a70864e63588538431b322c229c218d5916114e10cccc4b08a708665625845384334b14c029c211b9c865d0e108dae432e870846e721964384236b90cb21c219594d6190e10caaa6b0c870846f725954384236392caa1c211b9c86550e108dae432a870846e721944384236b90ca21c214d1d161d4a1087ce831aa50843d7418d5284237bb2a4294218b5915214a10c9ac6a90a50861e6498c528430eb24c629421879916314a10c3ac8b18a50862d649885284326b1cc4294218d9916114a10c6ac8b08a50865663584528432ab1ac2294219658e6014a108bce632e850845d73197428422f398cb21421175cc6590a10ccca4b0c850866552586428422fb9acaa1421171cd6550a108bce632a850845d73195428422f398ca21421175cc6510a1087ce832e650843d74197328421f3a0cb194210f5d0658ca1087ee8b2a650843c74595328421f3a0ca994210f5d0654ca10a98e4a9a650854c73549328425b3a6c2994210f9d3650ca1087ae9b28650843e74194328421eba0ca1942193d95320ca10c9aca99065086c932580328428eb98a920c214b5c8549061087ced2a2830843d76d50418428eb98a820c214b5c854106108eaedaa083084b576d5041842d9386a820c214d5db5410610c6aedaa0830853573d50418429ab96a820c21cc9c35410610b2ae62a083085a57215041842d9380a820c211d5db5310610a6ee8a98830853675d0c418429b3aa8620c21c554d43106108eaeda90830853774548418429b3ae8420c214d9d54210610e4aa4a10830863754580418430eb24a798c218759153cc610c5ac9296430862d6454b218428eb98a9a04214b5c854d021087cec2a2810851d731514084296b90a8a04218d150615021096ceda0a810843f76550408430f2a2c620421875516310210c5ca8b10810862d54588408431b2a2c2204218d5516110210d2ac620881086a562104408428eba0a798421535c853cc210968e8b0c610845e7614d308428eba0a
  | 9 => 0xcc92886010635649443008333314a2180419958a510c0208eeeca88601063664544300831ab22a21804199989510c020ccac4a88601054d73d5320082b2b8ea9900414b5d353c8020acae3a9e401070d5494f20083872a2a790041c355153c8020e4aa928e40107455394720083932a2a390041c955151c8020e8ca6a8e4010745535472008236bb4a510041c69515388020e32a8a9c40104797694a20083a8a9ca310041cc5515188020ea2a6a8c401046e76d5120082a6b9ea890041595c75448020a5aeb2a2401062f659512008317b2aa8900411b9db5348020a5ae9a9a401056571d4d20082a6baca69004193d965348020e1aa929a401064f6554d20083872a2a690041c35515348020e94e0a9a4010667659452008392aa4a290041d154e5148020ccecaa8a4010726545452008392aa2a290041d194d5148020e8aa6a8a401062d54d812008326a9ec090041ca5523048020e92a71824010761518c12008394aa26090041d254d3048020ec2a2982401063b65951200831db2aa8900411e9db5348020ab2eb29a401065b6594d200832db2aa690041c69515348020e32a8a9a401074a7254d200832ca9ec490041d254f6248020e52a929240107495394920083a4a9c6490041d254d3248020ce6cb28a4010751539452008339b2aa290041cc5515148020ea2a6a8a401076252545200821fbb2a82a6210f9d262d4f1087ae9316a7886366498653c431ab24c329e2117dd95314f108dce5b2e878846d72d9743c431a2a2c3a1e211b9ca6550f108dae532a878851e73d5143c4237390ca21e211b5c86510f1087ce931ea58843d7498f52c431b324c3296218d5926194b108deeca90a58845e73d9742c422eb9ecba16218d15161d0b108bce732a858845d7399542c4297396a8a1621179cc6510b108bae6328858843e74d9732c421eba6cb996210f9d3658cb1087ae9b2c658843e74d9532c421eba6ca996210f9d2654cb1087ae932a658843e74d9432c421eba6ca196210f9d0650cb1087ae832865886c93258032c421f3b0a8a0e216c5c354507108ecec2a283884b67615141c429b3b0a8a0e218d9d85450710e62e02a2838863454d8d41c431a2a6c4a0e218d15060507109aae630283884e57218141c421fbb2a820e21ac50560107109cae5b2463884777559231c431ab20a918e214d9d2538c7108bcec29a63884b574d9531c429b3a6ca98e211d9da544c710aace72a263886356415131c42e8b86a698e214d9d2534c7108ecec29a63884d67614d31c423b3b6a498e21551cd524c71096ae830263884e57218131c422fbb2a618e21b44c5600c7109aae7b2443884777559221c431ab20a910e212d5d36388710a6ce9294438846e7614921c425aba6ca90e214d9d365487108eced2a243885667295121c431ab20a890e211d9d
  | 10 => 0x53471551410829a3a2a2a0841179ce65104208bae7328821053571950410829aba4a2208414ddd54110420a6aeaa08821063765504410831ab2a8220841c594d4110420e2aa6a08821043e74d97310821eba6cb988410f9d265cc42087ae932e621043d75993310821fbaac9988410fdda54cc42087aed2a6621043f76553310821ebb2a9988418799253cc420c3ac929e621061e6454f310830eb22a7988418d99251cc420c6ac928e621063664547310831ab22a3988410f9d2658c42087ae932c621043e74195310821eba0ca988411b5d7624c420c5aa9b12621064d53d893108316aa0c4988419354c624c420ccec4a8a621066462545310821f3a4ca188410f5d2650c42087aeb326421043f75593210821ebb4a9908410fdd954c8420c3cc929e421061d6494f210830f322a7908418759153c8420c5ac9296421063664947210831ab24a3908418d99151c8420c6ac8a8e421065953983210832ca9ac1908419c54560c8420c72a9300421065953980210831caa2c0108419654d6008420ce4a2b00421062d5498a4008326a9cc5200411bdd56290020c5aa8b14801064d5358a4008333312a320041995895190020c6ca9b0a801063554d85400832b29ec2a00419554f6150020c6ca830a801063554185400832b298c2a00419554c61500208eced28a801047476945400823b3b2a2a00411d1d951500208bce7b28801045d73d94400822f39cca20041175ce65100208bce6328801045d73194400822ebacc620041879526310020c3aa9318801045f7558c400830f2a2c6200418755163100208beed298801045d7694c400822fbb2a620041175d95310020c5aa9310801064e539884008326a9cc4200418b9516210020c5aa8b10801064e535884008326a9ac4200411d5d66110020c6ca9308801063554984400832b29cc2200419554e61100208eeeab08801063654584400831aaa2c2200419594d6110020caaa6b08801047576944400832b31ca2200419558e5110020cccc5288801066562944400823bbb2a2200419598d5110020caac6a888010666625444008332b12a2200418b552628c020c9aa7314601046f7558a3008316aa2c5180419354d628c020cccc4a8c601066562546300821f3a6ca180410f5d3650c02087ce9328601043d74994300821f3a0ca180410f5d0650c02087aeb320601043f75590300821fbb4a8180410f5da540c02087eecaa0601043d76550300830f324a61804187592530c020c3cc8a98601061d6454c30083172a4c4180418b552620c020c9aa7310601062e545883008316aa2c4180419394d620c020c9aa6b10601047575984300831b2a4c2180418d552610c020caca7308601065553984300823bbaac2180418d951610c020c6aa8b08601065653584300832aa9ac2180411d5da510c020c6
  | 11 => 0x823abacc3210418d9526190820c6aa930c841065653986420832aa9cc3210411ddd56190820c6ca8b0c841063554586420832b29ac3210419554d6190820ccca4b0c841065953982420831caa2c1210419654d6090820cb2a7300841063a54580420832ca9ac0210419654e608c8208f6eab04641065953582320821f3a6ca190410f5d3650c82087aeb320641043f75590320821fbb4a8190410f5da540c82087eecaa0641043d76550320830f324a61904187592530c820c3cc8a98641061d6454c32082a6b92a61904193d95320c820c9aca990641070e544c83208386aa264190411d5d6610c820c6ca9308641063554984320832b29cc2190419554e610c8208eeeab08641063654584320831aaa2c2190419594d610c820caaa6b08641063a54980320831caa4c0190419654e600c820c74a8b00641063954580320832d29ac0190419654d600c820d9264b00641061e5498f510830eaa4c7a88418795163d4420c3aa8b1ea21061e6494f510830eb24a7a88418799153d4420c3ac8a9ea21053674d46510829aba6a328841559cf5194420aaae7a8ca21043e7498e510821eba4c728841559cf5494420aaae7aa4a2105567315251082aab98a9288414d9d35394420a6ae9a9ca2107165494e510838aaa4a728841c59515394420e2aa8a9ca2105367414e510829aba0a7288418d5906494420a6ce931ca2105357498e510823b3b487288411d5da43944208eaed214a210475760ca510829b3a065288414d5d03294420e8a64194a210572700ca51082b8b8065288414d9d06094420a6ae8304a2105567318251082aab98c1288411d9db5454420aace7aa2a21055573d51510823b3b0a8a8841559cc5454420aaae62a2a21047676d4d510829b3a6a6a88414d5d35354420e2ca929aa2107155494d510838b2a2a6a8841c555153544208ecec29aa2105367414d510829aba0a6a88418d5906454420a6ce931aa2105357498d51082b2392c6a88411d9da43544208eaed21aa2105677250d51082b239286a88414d9d26254420a6ae9312a2104767690951082b938084a88415c5c042544208ecec192a210536740c9510829aba064a8841d14c83254420ae4e0192a210571700c9510829b3a0c0a88414d5d06054420aace6302a21055573181510829b3a040a88414d5d02054420aace6102a21055573081510821ebb4a8288410fdd95414420c3ca9318a21061d5498c510830f2a2c6288418755163144208baed298a21061e6494c510830eb24a62884117dd95314420c3cc8a98a21061d6454c510831b2a4c2288418d5526114420caca7308a21065553984510823bbb2a2288418d9915114420c6ac8a88a21065663544510832ab1aa228841179ce65d04208bae732e821045e73996410822eb9ccb20841179cc65504208bae632a8210
  | 12 => 0x2a0418d5846195020a3ce6304a81051d73182540829b388c12a0414d5c46095020a3ce7b22a81051d73d91540829b38ec8aa0414d5c76455020a6ce331aa8105357198d5408296392c6aa0414d9c66255020a6ae3312a81063561185540828f398c0aa041475cc6055020a6ce2302a81053571181540821fbb2a82a041875526315020c3aa8b18a81063554984540831aaa2c22a041879926315020c3cc8b18a81064e639885408326b1cc42a0418d9926115020cacc7308a810655639845408333314c22a0418d9916115020cacc6b08a810655635845408333312c22a0419658e6015020ce2c3300a81063654987530831aaa4c3a98418d95161d4c20c6aa8b0ea61062d6498b530831b324c3a98418d59261d4c20c6cc8b0ea610635645875308333312c3a9841479d35394c20a3ae9a9ca61055671d4e53082aab8ea729841559c75494c20aaae3aa4a6105567115253082aab88a929841559c76494c20aaae3b24a61051e7418a530828eba0c529841559c46294c20aaae2314a61051e74d86530828eba6c329841479d06094c20a3ae8304a6105567118253082aab88c1298411d9c76454c208eae3b22a61051e74d8d530828eba6c6a9841559c76354c20aaae3b1aa61043e74d85530821eba6c2a9841179db5454c20aace3aa2a61055571d51530822f3b0a8a9841559c45454c20aaae22a2a61055671d9153082aab8ec8a9841531c96454c20a3ce8312a61051d7418953082ab388c4a9841555c46254c20a3ce9b0aa61051d74d8553082a6392c2a9841479d06054c20a3ae8302a6105567118153082aab88c0a9841479d02054c20a3ae8102a61043d76950530821fbb2a829841879526314c20c3aa9318a61045f7654c530830f322a629841875915314c20c6ca9308a61063554984530832aa9cc2298418d9516114c20c6aa8b08a61065553584530830f324c629841875926314c20c5cc9310a61062d64988530831b324c2298418d5926114c20cacc7308a61066662984530831b322c2298418d5916114c20cacc6b08a61066662584530831d324c0298418e5926014c20ce4c3300a61067161980530823b38ccba18411d5c665d0c208dce432e861047671197430823ab88cba18411d9c76590c208eae3b2c861047671996430823ab8ccb218411b9c86590c208ece232c861047571196430823d380cb218411d5d66190c20c6ca930c861063554986430832b29cc3218419554e6190c208eeeab0c861063654586430831aaa2c3218419594d6190c20caaa6b0c861047671995430823ab8ccaa18411b9c86550c208ece232a8610475711954308236baec4a18418b5536250c20c9aa7b12861046d751894308316aa0c4a18419354c6250c208ece33288610475719944308237390ca218411d9c46510c208eae2328861047a7019443
  | 13 => 0x5450d20a38e6aa2869053471551434823bb8aca21a411d1c56510d2087ce8328869047671194434823ab88ca21a410f5db5410d208d8eab10869064c53588434823c3aac021a41365cc6050920b4ce3b22849046e7615142482963aa86a1241335cc60509209cae230284905c97318142482373aec919241395c7648c920ad4ea30464904e571d9132482363aac899241539d7634c920a9ce729a649046e7614d32482a73b0a699241939d8534c920e1ce829a649070d7414d32483a3388a699241d15c4534c920e92e029a64904ad74d853248256ba0c099241395c4604c9208eeeca88a2905347454451482aa39aa228a414b1d54290520c5ccaa14829045f73594414822e39aca20a41179cc65105208bae632882905357115041483162a2c420a414b1d54210520a6ae8288829066562144414829b3aa8220a414d1d54110520d5284b0082906b141580414821f3a0cb98a410f5d065cc520c6cc9a8e62906366414731482aab88a718a412b5d2628c52087ee8b28629043c74594314821f3a0ca18a410f5d0650c520c98a6b10629046e75d8f2148256ba6c790a41365cc60485209d0e0b2242905a674d8521482733b68290a41599d74148520d4ac820a42905e17010521482b23aa6290a412b5d0604852099ae630242905c9731812148256ba4c410a41395c662d0120a58eaa16809045f73595404822e39acaa02414b1d54250120b50e0a12809063754185404831a2a0c2a0241a95086150120a3ae829e60905557114f304832629ac598241531d532cc120ad4ea31460905a97418a30482f0b88c518241785c6428c120b96e6a146090568754ca30483a429a65182416a5d3218c120b96e690c609043f74595304821e3a2ca98241475d0534c120aaae229a60904ad741893048272b88c498241531d5324c120c98ca992609047a7614d30482ccba0a698241745c4534c120b92e521a60905d17190d30482d4ba0c498241785c4624c120b92e721260905e17190930483c4a1a849824196197324c120cd0cb19260905c9738c9304832c32a64982415a1d5324c120cd0ca9926090748754c930483a5b2a6498241b2195324c120e90ca9926090648654c930482e5ba26498241725d1324c120b96e2992609059974cc530482e4b9662982416a5d3214c120b92e790a60905c97348530483e098a4298241a6591300c120d92c498060906d1614c030482f0b8c8590241b258e32c8120d96c699640905a974c872048273b8ac9102412bdd16188120d92c718440906cb634c22048326b1cc5aa0419598e61d5020caac730ea81065663587540832ab1ac3aa0419998961d5020cb2c7306a81051e73d52540828eb9ea92a0414d9c75495020a6ae3aa4a8104767198e540823ab8cc72a0414d9c66395020a6ae331ca8105367198a540829ab8cc5
  | 14 => 0xc5308a71063664584538831ab22c229c419598d6114e20ccac4b08a71066962980538823b388cba1c411d5c465d0e20a68e2aa6871047671d96438823ab8ecb21c411d9c46590e208eae232c871065653586438832aa9ac321c411ddc56550e208e8e2b2a871047671195438823ab88caa1c414d1c55450e208ece2328871047571194438829a38aa9a14414d1c55450a209b2e630285106c932580328821f3a4c728c410f5d26394620c6ae2322a31047776544518829a3a2a228c418d5915114620caac6a88a31053471553418828eb98a920c414d5c45490620a68e8a8c831045e73195418822eb98caa0c410f9da5450620a68e2aa2831053474545418821ebb6a820c41475cc5410620a6ae22a0831053475504418831bb2a8220c418d5954110620d6282b00831043e74d97318821eba6cb98c418759253cc620c3ac8a9e631053474546318821fba2ca98c410f1d1654c62087ce832a631043d74195318829a3a2a298c414d1d15188620a68e8a8a43104d973181218828eb98a9a04414d5c454d0220a68e2aa4811043e76151408828eb98a8a04414d5c45450220c6ea830a811063454185408821fbb2a8204414d1c55410220c3ca8b18811061d5458c40883172a2c4204418b5516210220c6ca8b08811063554584408828eba0a798441555c453cc2208bcec29a611051d7414d30882aab88a698441725cb534c2208f4ec29a61104da7614d30882ccba0a698441745c4534c220ba2e321a61105cb7250d30883643126498441665d3314c220b96e498a611061d6494c308822fbb2a61844187591530c220c9ca6b10611064d53588308832b29ac2184419554d610c220d32c898061106c9624c03088368b0a601844159dc554c8220a5ee8a8e41104767198e544823ab8cc72a24187d906355120c98c7b12a89065763d85544832a31ec2aa2418dd906155120caec630aa89065463185544821fbb2a82a241471cd5415120a68e2aa0a89047771593534823a38ac9a9a410fdd161d4d20878e8b0ea69061c64d8d5348316326c4a9a418dd936154d20c68c9b0aa69063764185534831a320c2a9a4195d8c6154d20ccec430aa69045f7654c534828e3a2a629a41551c55314d20c38e6b20a69062e645885348316b22c429a410f9d06214d2087ae8310a69063664984534831ab24c229a419958a6114d20c6cc8b08a690635645845348332b12c229a418e9916014d20c72c8b00a69066962580534833930ac029a419c5856014d208ece3b2e869047571d97434828e39aa9a1a414d1c554d0d20a3ae829e86904e57198b43482363aac5a1a411d9c76590d208eae3b2c869047671196434823ab88cb21a411b1d56290d20c6ea930c869063454986434823c3aac121a411bdc96550d208eee2b2a869047471595434821f3b4a8a1a410f1d9
  | 15 => 0x5765545300c38b2a2a298061c5551514c030e8ca4a8a601874552545300c30eaa6c0980618ed96544c030c76caaa260187195494d300c335b2ca4980619ad95524c030e54a8a92601872954549300c3a529aa498061d29cd524c030e96c6a92601874952cc9300c339b2ca298061d854a514c030ce6caa8a601873154545300c3a929aa298061d8549514c030a6ce3aa4a9904767198e54c823ab8cc72a6414d9c7645532087eecaa0a99047671d9153c823ab8ec8a9e410f9d36154f2087ae9b0aa79045f7654c53c831b324c229e418d5926114f20c6cc8b08a7906356458453c831d322c029e418e5916014f20cd4c4b00a7906726158053c8338b0ac029e411d9c765d0f208eae3b2e87904767199743c823ab8ccba1e41395c662d0f208ece3b2c879047571d9643c823b388cb21e411d5c46590f208ece332a87904757199543c828e39aa8a1e411d9c46510f208eae2328879053671d5342c831b2a4c3216418d5526190b20ccacb30c85906656558642c8370b0ac1216414d9c75450b2087cec2a285905a671d9142c82d338ea8a16416a5c35450b208dcec2a285904ae7615142c82963aa86a1641335cc6050b209cae2302859043f7655042c8354a12c021641395c7648cb208bcec29a65904e571d9132c82e4b86a6996411b9d8534cb2099cec29a659054e7614d32c83273b0a699641c39d0534cb20e1ae829a65907467114d32c83a2b88a699641d25c0534cb2095ae9b0a65904ad7418132c8272b88c09964117dd9530cb20cb4a6b0065906595358032c8364992c0196414d9d3519472087ce931ca39043d7498e51c823bbb2a228e41179cf65d07208bae7b2e83906666254741c822f39ecb20e41175cf6590720c5aa9314839062e6550a41c829ab8ca820e414d5d25110720a6eeaa0883905357550441c821f3a6cb98e410f5d365cc72087ce9b2c639043d74d9631c821f3a4cb18e410f5d2658c72095ae931463905547354531c831b324a390e418d99151c872095ae9b1e43906a96458321c82d33a6c290e41699d35148720bc2e1a8a43904e67614521c82b33ae8290e41a95904148720ac8ea98a43904ad7418121c8266b98c090e41b848560087209cae331681906365418540c831aaa0c2a0641a9508615032095ae8312619064d5318930c8272b88c4986411d9c663952208eae331ca91063764185548821fbb2a82a4414d1c55415220c3aa8b18a91063554584548830f322c62a4419398d6215220c9ac6b10a91065663984548832ab1cc22a4419958a6115220c6cc8b08a91065663584548832ab1ac22a4419958961152208eee2b26a71047471593538821fba2c3a9c410f1d161d4e208beeca98a71061d6454c538832aa9ac229c41875926314e20c5cc8b10a71062d64588538831b324c229c418d5926114e20cca
  | 16 => 0xc316b22a4288618d9526114430c6aa9308a21866652984510c332a94c2288611ddd95114430c6cc8a88a21863564544510c333312a2288619958951144308dce532e821846d72997410c237394cb208611b5ca65904308dce432a821846d72195410c29a38aa8a08614d1d151504308dce5328821846d72994410c29ab8ca8208614d5d25110430a6eeaa08821853575504410c31bb2a82208618d5954110430e4ca4a08821872552504410c21ebacc9988610fdd564cc43087aed2a6621843f76553310c30eb24a7988618b99252cc430c5ac9296621862e6454b310c316b22a5988618d99251cc430c6ac928e621863664547310c31ab22a3988619a54a60cc430cd2a4b06621867151583310c31caa4c0188619a54a600c430c72a8b00621866952580310c33928ac0188610f9d365c843087ae9b2e421843e74997210c21eba4cb908610f5d664c843087eeab26421843f76953210c21ebb4a9908610fdd954c843087aecaa6421862e6494b210c316b24a5908618b99152c8430c5ac8a96421863664947210c31ab24a3908618d99151c8430c6ac8a8e421843e74996210c21eba4cb108610f9d0654843087ae832a421845d75d8d210c30eaa6c690861875506348430c9ec6a92421864c63549210c32bb1aa2908619518d514843087ce9328421843d74994210c30eaa4c72006117dd56390030c3aa8b1c801864e6354a400c326b1aa5200619598d5190030caac6a8c801863654d85400c31aaa6c2a00619994b6150030ccaa5b0a801863654185400c31aaa0c2a0061999486150030ccaa430a801847676945400c23a3b4a2a00611d9d951500308e8eca8a801861d5498c400c30f2a2c6200618755163100308daeb310801862e54988400c316aa4c4200611bdd56210030c5ca8b10801862d54588400c236bb4a4200619398e5210030c9ac7290801846f76548400c32731aa4200619358d52100308eaeb308801863654984400c31aaa4c2200619994a6110030ccaa5308801847775584400c31b2a2c2200618d5516110030ccca4b08801866552584400c23abb4a2200619598e5110030caac7288801866662944400c332b14a2200611ddd95110030cacc6a88801865563544400c333312a220061995895110030a9ae5aa6601855571d53300c386aa4a598061c395152cc030e1aa8a96601871554947300c3a2a94a398061c595151cc030e2aa8a8e601874652547300c3a2a92a398061175da538c0308f2ed29c601872a5454a300c394aa2a518061d854a518c030e62a8a8c601876152546300c22f3b6a898061535cb544c030aaae3aa2601851d75951300c30fb2ca89806187d95544c030c9ecb292601870d54949300c327b2aa498061c3951524c030e1aa8a92601874a70549300c32bb2ca298061c5552514c030e8aa528a60186
  | 17 => 0x90614b5d06054830acce2302a41856571181520c2973a060a90614b5d0305483087aed2a0a41843f76550520c3172a4c4290618b55262148308deeca90a41862e64548520c316b22a4290618d9526114830c6aa9308a41866552984520c31b2a2c2290618d5516114830ccaa4b08a41847671997420c23ab8ccba10611d9c765908308eae3b2c841847671996420c23ab8ccb210611d5d66190830c6ca930c841863554986420c333294c3210619954a61908308eeeab0c841863654586420c31aaa2c321061999496190830ccaa4b0c841847671195420c23ab88caa1061175d76350830c3aa9b1a841861d5418d420c327b1aa4a10619318d52508308ece3328841847571994420c334a92c1990610f5d6640c83087eeab20641843d76950320c21fbb2a8190618b992520c830c5ac9290641862e64548320c316b22a419061c3951320c830e1aa8990641847575984320c31b2a4c2190618d552610c830ccca5308641866552984320c23bbaac2190618d951610c830c6aa8b08641866652584320c332a92c2190618e952600c830c72a9300641866952980320c31d2a2c0190618e551600c830cd4a4b0064186c932580320c3172a4c5a88618b55262d4430c5ca8b16a21862d5458b510c317324a5a88618b59252d4430c5cc8a96a21862d6454b510c29b3a6a3288614d5d35194430acce5a8ca21856572d46510c21f3a4c5288610f5d26294430acce5aa4a21856572d52510c2b3390a928861595c85494430a6ce9a94a21853574d4a510c3932a4a528861c95525294430e4ca8a94a2187255454a510c29b3a0a5288614d5d05294430c6ac8324a2184757690e510c29b3a4c5288614d5d262944308eced214a2184757690a510c23abb065288614d9d03294430a6ae8194a218745320ca510c2b938065288615c5c03294430a6ce8304a21853574182510c2b3390c128861595c860944308ecedaa2a21856672d51510c2b2b96a8a88611d9d85454430acce42a2a21856572151510c23b3b6a4a88614d9d35254430a6ae9a92a21872654949510c392aa4a4a8861c99515254430e4aa8a92a21847676149510c29b3a0a4a88614d5d05254430c6ac8322a2185367498d510c29aba4c6a88611d9da4354430ae4e021aa2185717010d510c29b3a4c4a88614d5d26254430aa8e6b12a21847676909510c23abb484a886155dcd4254430aa8e6a12a218476760c9510c29b3a064a88614d5d03254430e8a64192a218572700c9510c2b8b8064a88614d9d06054430a6ae8302a21856672181510c2b2b90c0a88614d9d03054430a6ae8182a218566720c1510c2b2b9060a88610f5da541443087eecaa0a21862e54988510c316aa4c4288618b9516214430c5aa8b10a21846d76948510c317324a4288618b59252144308deeca90a21862e64548510
  | 18 => 0x114530a68e8a88a29856472544514c28e3aa8720a618799543905308dee4b28829846c72594414c237390ca20a611b5c86510530a6ae22a0829861c5458c414c28e3aa8620a614d5d05110530caac6288829853675504414c29a3aa8220a61a650d6010530d6282b0082984e972181314c26c382c898a61659d3614c5309aceda0a629855675d05314c34ab208298a61745c0414c53093ae830262984cd72181314c2e4b90c098a61275d2630c53087ce832e429843d74197214c31b326a390a618d99051c853093ae931c42985657114a214c22f3acc690a61275d26348530ca8ca98a429843f74594214c21e3a2ca10a610f9d0650853087ae8328429864d63148214c26ab8cc7a0261471d543d0130a38eaa1a80985987050d404c31baa0c2a02618d1506150130d2a8630a80985d17190f304c364b166598261665d331cc1309aee2b24609849f74586304c32731ac5aa0619998a61d5030ccac530ea81865663587540c333312c3aa0619958961d5030cd2c5306a81852e72d52540c296b96a92a0614d9c75495030a6ae3aa4a8184767198a540c23ab8cc52a0614d9c66395030a6ae331ca8185367198a540c29ab8cc52a0618d5846195030a5ce4304a81852d72182540c29b388c12a0614d5c46095030a5ce5b22a81852d72d91540c29b38ec8aa0614d5c76455030a6ce331aa8185357198d540c29b38cc4aa0614d5c66255030a38e6b12a81863561185540c297390c0aa0614b5c86055030a6ce2302a81853571181540c21fbb2a82a0618b5526215030c5aa8b10a81863554984540c31aaa2c22a0618b9926215030c9cc7310a81862e64588540c32731ac42a0618d9926115030cacc7308a81866662984540c332b14c22a0618d9916115030cacc6b08a81866662584540c332b12c22a0619a58a6015030ce2c3300a81847575986430c31b2a4c3218618d5526190c308eeeab0c861863654586430c31aaa2c3218619594d6190c30c72a8b04861863a54580430c31b2a4c3a90618d55261d4830c6ca8b0ea41863554587520c2973a6a5290614b5d35294830acce3a94a41856571d4a520c2b338ea929061595c75494830acce22a4a41856571152520c2b338ec929061595c76494830a5ce831ca41852d7418e520c2b3388c729061595c46394830acce321ca4185657190e520c2973a6c3290614b5d36194830a5ce8304a41852d74182520c2b3388c129061595c460948308ece3b22a41847571d91520c21f3a6c2a90610f5d361548308dcedaa2a41856671d51520c2b2b8ea8a90611b9d85454830acce22a2a41856571151520c2b338ec8a9061595c76454830a98e6b22a4185667190d520c2b2b8c86a90615a9c24354830ad2e121aa41856a7010d520c2b4b8086a90614b9d36154830a5ae9b0aa41854c73585520c2973a0c0a
  | 19 => 0x9b2c439843d74d9621cc21f3a4cb10e610f5d2658873093ae931c439849d7498d21cc2b2392a290e619519531487309aae331e81986365418540cc31aaa0c2a0661a550c61503308ece3314a9184757198a548c31bb20c2aa4610fdd95415230a68e2aa0a91862d54588548c31aaa2c22a4619358e6215230c5cc8b10a91864d63588548c32ab1cc22a4619998a6115230ccac5308a91863664584548c32ab1ac22a461999896115230ccac4b08a91853471553438c29a38aa8a1c613a5c86050e308deeca90a51862d64548528c332a92c2294614d1c554d0a308ece3b2c851847571d96428c333292c321461995496190a308eee2b2a851847471595428c23b388caa14611d5c46550a30a68e2aa285186c932580328c21f3a4c528c610f5d26294630c6ae2322a31847776544518c29a3a2a228c618d5915114630ccac4a88a31853471553418c296b90a920c614d5c45490630a68e8a8c831846e72195418c236b90caa0c610f9da5450630a68e2aa2831853474545418c21ebb6a820c614b5c85410630a6ae22a0831853475504418c31bb2a8220c618d5954110630d6282b00831853474546318c29a3a2a298c613a5c8604c63087ce9b2e431843d74d97218c316b24a590c618b59152c8630a68e8a8c431843f74595218c21e3a2ca90c610f9d0654863087ae832a431853474545218c296b90a9a04614d5c454d0230a68e2aa4811843e76151408c296b90a8a04614d5c45450230c6ea830a811863454185408c21fbb2a8204614d1c55410230c3ca8b18811861d5458c408c3172a2c4204618b5516210230c6ca8b08811863554584408c2abb8aa99846147dd151cc2308ece3314a8984757198a544c317b20c4aa26193d8c6255130ccec5b0aa89866462d85544c31bb20c2aa26199d886155130cc8c430aa89843f76550544c296392a82a2614d1c554151309d2e4302869859671d91434c22f3b0a8a1a61335c86050d309aae230286985c972181434c23bb8ac9a92611d1c564d493087ee8b0ea49843c74587524c237bb2a4292614b1d15214930ac8e2a90a49862c72590524c31b324c2292618d5926114930c6cc8b08a49863564584524c31d322c0292618e5916014930ce4c2b00a49867161580524c296392a9a12614d1c554d09309aae331e849852d7414b424c23b388cb212611d5c46590930c6ea930c849863454986424c21f3b4a8a12614b1c95450930a68e2aa2849861c6550d424c23bb8aca212611d1c565109308ece2328849847571194424c21ebb6a8212619358c52109308bcebb2664984d571d93324c2ad3a8c199261355c7644c930a9cebb12649854e76149324c3273b0a499261c39d0524c930e1ae8292649874671149324c3a2b88a499261d25c0524c93093ae9b0a649849d74181324c26ab88c0992611ddd95
  | 20 => 0x464545211031ab288290881c554c4148440e4aa420a422045e73994211022eb9cca108810f5d84194040e1aa7296802070e5354b4010386a9aa5a00818754e61d0040c5aa530e8020715539474010392a94a3a00810fdd951d0040c6cc2a8e802071653547401038aa9aa3a0081c994951d0040e4aa4a8e802063776547401021ebb4a9200811e5da5490040e92a6a9480207515354640103b0a92a3200819594f6150040caaa7b0a802066652d854010332a96c2a00819594c6150040caaa630a8020666521854010332a90c2a00811d1da51500408ececa8a802063771d95401031a38ecaa008187d965350040c3ecaa9a802062f659494010386a9ca4a00818bd955250040e1ca6a92802070d53549401031bb2ec2a0081c554f6150040e4aa5b0a802061d531854010316a90c2a00818dd946150040e2aa630a802072552185401031aba8c2a0081a594c6150040c6aa630a802069553185401030aa98c2a0081a99486150040c6aa430a80206a5521854010312a90c2a00812d1da5150040c6ecb28a8020715539454010392a94a2a00818d1855150040968eca8a802063765545401038b29aa2a0081c554d5150040e4ca4a8a802072552545401029b3b2a2a00814d1d95150040c68eca8a802067371d95401033838ecaa008196d965350040cb6caa9a802071a5454d4010335b2ca4a00819ad955250040e54a8a928020749535494010339b2ec2a00819cd946150040d66c830a8020673659454010339b2aa2a0081cc9515150040ea2a6a8a802076152545401029b38ea92a6611d9c662953308eae3314a99853671d9154cc21fbb2a82a6614d9c754d0f30c6ca930c87986355498643cc32ab2cc321e61955956190f30da2c2b04879853671d5143cc21f3b0a8a1e61659c76450f30b2ce3aa2879859970d5143cc22f3b0a8a1e61279d85450f3099ae430287984d57118143cc21fbb2a821e61a650d6010f308ece3b22a59847571d9152cc21f3a6c2a96610f5d36154b308deeca90a59847671d9742cc23ab8ecba16611d9c665d0b308eae332e85984d57198f42cc23b38ecb216611d5c76590b30a58e4aa2859861c6550d42cc26ab8ec999661355c7644cb30b92e1a9265984ce7614932cc24eba6c299661275d0604cb309aae230265986695258032cc364992c0196614d9d3519473087ce9314a39843d7498a51cc23bbb2a228e611b9cb65d07308dae5b2e83986566354741cc237396cb20e611b5cb6590730c3aa931c839861e6550e41cc29ab8ca820e614d5d25110730a6eeaa0883985357550441cc31b324a398e618d99151cc730d32c8b06639859674d8531cc2cb3a6a298e61745c3514c7309acec28a639855675d0531cc34ab208298e61275d0604c73099ae430263986d13158031cc21f3a6cb90e610f5d365c873087ce
  | 21 => 0x3a329aa4a8881d154d5254440e48c8a92a2204767614951102ab398a4a8881555cc5254440a6ce931aa2205347458d511023abb486a88815c9c04354440ae2e021aa22053674989511029a3a2c4a88811d5da4254440ae4e0212a22057170109511029bba264a88814d1d132544408ecec192a220475760c9511029b3a064a88814d5d03254440e8a64192a220572700c951102b8b8064a8881559cc6054440aaae6302a2205667218151102b2b90c0a8881559cc4054440aaae6202a2205667210151102b2b9080a8881175da53144408beeca98a22064e539885110326a9cc4288819394d6214440c9aa6b10a22046d76948511032731ca4288819358e52144408deeca90a22064e635485110326b1aa4288819594e6114440caaa7308a220666529845110332a94c2288811ddd95114440cacc6a88a220655635445110333312a228881995895114440ce2a2b06822063671596411030eb2ca720881875955390440c5acb294822070d5394a4110316b2aa520881c394d5290440e1aa6a94822063565946411038aa9ca320881c954a5190440e2ca6a8c8220715535464110393292a320881c95495190440c3aa6b04822062d52582411031aa8ac120881c594d4110440e2aa6a088220726525044110392a9282208819654e6010440cd2a53008220659535804110334a92c0208819c9456010440e2ce2a9882207157154c4110386a9ca420881c394d5210440e1aa6a908220726715484110392b8aa4208814d5d66110440e2aa7308822072552984411038aa9ca220881c954a5110440e2ca6a888220715535444110393292a220881c95495110440a6eeca88822063776544411029bb9aa2208814ddc95110440e32a7300822072952980411030ea9ac0208818b5496010440e32a6b00822072952580411035930ac0208811b9ca65cc4408dae532e622061d6494f311030f322a7988818759153cc440c5cc9296622062d6494b3110317322a5988818b59152cc440c6cc928e622063564947311031b322a3988818d59151cc4408dce532c622046d72996311031ab288318881c554c418c440e4aa420c622046e721953110236b90ca988810f5d7644c440c3ec8a9a622061c6454d3110317b22a4988818b191524c440c6ec8a8a622063464545311031ab288298881c554c414c440e4aa420a622046e729943110236b94ca18881179ce65c84408bae732e422061e6494f211030eb24a7908818799153c8440c3ac8a9e422062d6494b2110317322a5908818b59152c8440c6cc928e422063564947211031b322a3908818d59151c84408bce732c422045d73996211031ab288310881c554c4188440e4aa420c422045e73195211022eb98ca908810f5d76448440c3ec8a9a422061c6454d2110317b22a4908818b1915248440c6ec8a8a422063
  | 22 => 0x81599c45394840acae229ca42052e7418e5210326b18c729081599c46394840acae231ca42056a7018e52102b338c8729081595c64394840a5ce9b0ca42054e7318252102a6b98c129081599c46094840acae2304a4204767118d521023ab88c6a90811b9db5354840acce3a9aa42056571d4d52102373b0a6a9081599c45354840acae229aa42052c7458d52102973a0c6a90819358c6354840acce231aa4205657118d52102b5380c6a9081599c64354840acae321aa42056a7010d52102b4b8086a90814b9d36154840a58e8b0aa42054e7318152102a6b98c0a9081599c46054840acae2302a42054e7310152102a6b9880a9081175da53148408beeca98a42064e539885210326a9cc4290811bdd95214840c9cc6a90a42064d63548521032b29cc2290819554e6114840ccaa5308a42065653584521032aa9ac229081995496114840cd2a4b06842065653986421032aa9cc3210819954a6190840caca6b0c8420655535864210332a92c3210819654e6010840cb2a6b00842066a52580421023b38ccb990811d5c665cc8408ece332c642047571996321023b388ca990811d5c4654c84087aebb2264204b671d91321030fb22a69908187191534c840a98e4a9a642062f645493210316322a499081531cd524c8408ece3b28642047571d94321023b38cca190811d5c6650c840c3cc9298642061d6494c32102a6b94a61908187991530c840c3ac8a98642062e649483210316b24a419081535ce520c840c5cc8a90642062d6454832102a7baa6419081535d5320c840c9eca990642064d654c8321023abacc2190819594e610c840caaa73086420666529843210332a94c2190811ddd5610c840caca6b086420655535843210333292c21908199549610c840cb2a7300642066952980321032d29ac0190819654d600c840cd4a4b006420669525803210364992c0190819394e62d4440c9aa7316a22064e5358b5110326a9ac5a88819398e52d4440c9ac7296a22064e6354b5110326b1aa5a8881559cf5194440aaae7a8ca22056672d4651102b2b96a328881599cb5394440acae5a9ca2207146454e51102b3390a728881595c85394440aace7a94a22055573d4a51103a329ca528881d154e5294440e8ca6a94a2207455354a5110392322a528881559cc5294440aaae6294a2205367498e511023b3b487288814d9d262944408eced214a220476760ca511023abb065288814d9d03294440a6ae8194a220745320ca51102b938065288815c5c03294440aace6304a2205557318251102b3390c128881595c860944408eceda9aa22056672d4d51102b2b96a6a8881c51925354440e28c8a9aa2204767614d51102b3390a6a8881595c853544408eceda92a22055673d4951102aab9ea4a8881d194e5254440e8aa7292a220724649495110
  | 23 => 0x145408eaed298a2a04777654c51502b3b92a628a81591c95314540a6ceba18a2a07175350c515023abb4a428a811ddd95214540aaee6a90a2a055473548515029b3ae8428a81c9d494214540aace7b20a2a055573d9051502b3396c828a81595cb6414540a6ae9b18a2a05357498c515029aba0c628a819558c6314540acce4318a2a05657218c51502b8b80c628a814d5db4314540e2cc7a18a2a071563d0c515029ab968628a814d9c343145408eaed218a2a05377650c515038bb9a8628a814ddc94314540a68e0a18a2a053574d88515029aba4c428a814d5d06214540aace6310a2a0555731885150332b10c428a815c5c06214540a6aeda10a2a053573d0851503933168428a81c958b4214540a6ce1a10a2a047576908515029bbb28428a814ddcd4214540e4ee4a10a2a053470508515029b3a66428a814d5d33214540a6ce9190a2a0535748c8515029b3a26428a814d5d132145408ecec190a2a0475760c8515029b3a06428a814d5d03214540e8a64190a2a0572700c851502b8b806428a818ddc665d0540c6ccba8e82a063563147415031ab10a3a0a818d14660d0540ce0a330482a067351181415029b3aec2a0a814d9d85150540c6cec28a82a063763145415031bb10a2a0a81275cc605054095ae430282a06b361181415031b326a398a818d99051cc540c6ac828e62a063664146315031ab20a318a814d9d7418c54087ceb32262a04ad7299131502ab39ea298a818d990514c540c6ac828a62a053675d05315031a32e8298a811b9c8650c5408dae432862a063664144315031ab20a218a81555cc510c540ce0a330062a063664d47215031b320a390a818d59051c8540c6cc828c42a063564146215029b3ae8310a810f9d6644854093ae732242a056672d45215031b320a290a818d5905148540a6ceba0a42a063465d05215022f398ca10a81175cc6508540c6cc828842a06356414421502b2b90a210a819c1466008540c6ac228c80a063576146405031ab18a3202818d5885190140a9ce5a9ca62054d72d4e53102ab38ea729881555c75394c40a3ce8314a62064d6218a53102ab388c529881555c46294c40ab4e0314a62051e74d8653102a7390c129881535c86094c40aace2304a62055571182531023b388c4a98811d5c46254c40a38e8b12a62051e741895310326b10c4a9881559c46254c40aaae2312a62055a70189531028f3a6c2a9881471d16154c40a9ce4302a62054d7218153102ab388c0a9881555c46054c408beeca98a62064d539885310326a9ac4298819554e6114c40caaa6b08a62065953583431032aa9cc3218819554d6190c40cb4a6b00862065653987521032aa9cc3a90819594d61d4840caaa6b0ea42054e73d4a52102a6b9ea529081599c75294840acae3a94a42056671d4e52102b2b8ea729
  | 24 => 0xb2a87a059970d4d43d029b38ca6a1e81279d85350f4095ae430287a04b57118143d034ca1ac021e818718d4354b408deeca90a5a05367194b42d021fbaac3a16812d5c76550b40a6ce3b2a85a052c7254d42d02d4b86a4a16814d9c65250b4095cec29285a049d7318142d025ab88c0a1681aa5096010b408ece3b2e65a047571d9732d023b38ecb196811d5c7658cb408ece3b2a65a047571d9532d025ab8cc8996811d9c7650cb408eae3b2865a06c93258032d030f31a8728e818b98942947408eeeca88a3a05b170d4541d025b3b0a2a0e81275cc605074095ae430283a06b14158041d0237396cb18e811b5cb658c74095ae532263a045e73d9621d022eb9ecb10e81275ce64487408ece2312a72047571189539022fbb2a629c819354d6214e40caaa6b08a72065653586439032aa9ac321c811d9c46354a408eae231aa52046f765485290326b1aa429481995496114a40ccca4b0c852066552586429023bb8aca994811d1c5654ca408ece232a652047571195329025b38ec899481531c9534ca40a98e6a92652047671d94329023ab8eca1948193d95320ca40c9aca99065206c932580329023bbb2a228c819558d5114640ccac4a88a3205377154c419029bb8aa420c812d5db5110640b64e1a8883205957314441902d2b90a220c816c9c05110640c3ac929e632061d6454f319031b3288318c811bdc9654c6408d8e4b2a632046e721953190236b90ca98c81c554c414c640c5ac9296432062d6454b219031b3288310c8117dcd65486408b8e6b2a432045e73195219022eb98ca90c81c95484148640968e2b2e812053771597409031b30aa3a04811d9c662d4d408eae3316a6a045f7654c53502a6392a629a811d9d66190d408e8eab0c86a043e75d854350256b90c0a1a812d5c46050d408ece331ea4a04757198f5250237bb2a429281531cd52149408eceb30c84a047475586425021f3aec2a1281275cc605094096ae230284a047771597325023a38acb992811ddc5658c9408e8e2b2c64a047671d95325023ab8eca992810f9d6644c94096ae332264a047771594325023a38aca192811d9c4650c9408eae232864a061d64d4c32502a6b90a6192818b593520c940a9ae629064a054e754c832502a63aa64192811d9d6610c9408e8eab0864a065b53580325032c29ac0192819ad49600c940cd0a4b0064a06c93258032502b3b92a7a8a81591c953d4540e28a6a1ea2a05577354b51502aa39aa5a8a81c914942d4540caec731ea2a05357418f515023abb487a8a81c550c43d4540ccec5316a2a05357418b515023abb485a8a81c950842d45408ecec196a2a0475760cb515029b3a065a8a814d5d032d4540e8a64196a2a0572700cb51502b8b8065a8a811ddd95114540a6ae3a18a2a05377150c515029ab8e8428a814ddc542
  | 25 => 0x64d4f314870eb20a798a439314d62cc5219cce53246290c7675192314863abb4a918a43559ce548c521a6ce929c6290cb67498a314861f3a6ca98a430f5d3654c5218eceb3226290ce672991314863b3b4a898a43559ce544c521aacebb1a6290d367494d31486ab39ca698a431d9d8534c521aacec29a6290e567614d31486aab80a698a43399d4624c521cccea3126290ce570189314865b3a6c790a43699d351885218bce7326a090c5d73993504861f3a4c7a82430f5d263d41218f6eca80a090e3771590504871a38ac828243879926314121c3ac9318a090e1e6458c504870eb22c6282431d5db4114121c6ac9a08a090e5563d04504871ab2082282439558c41141218ece331ca810c5e73181540862eb98c0aa0430fdd95415021c3aa8b18a810e3954580540870f322c62a0439358e6215021caac7308a810e5a63980540872cb1cc02a0438e9916015021cb4c6b00a810e59635805408735312c02a0439c985601502187ce9316a610c3d7498b530863b38ec8a98430f9d06054c2187ae8302a610c5f7654c530870eb22a6298439654d6014c21c3ac9318a610e2d64988530871b324c2298438d5926114c21c74c9300a610e3964980530873930cc0298438e9916014c21c72c8b00a610e5a635805308735312c0298439c9856014c218ece332e8610c7a70197430863cb80cba18431b5d662d0c218eaeb30e8610c7775587430863b388cb218431e9c06590c218f2e032c8610c7575986430872aa9cc321843395ca6190c218dce532a8610c7671995430863d380caa18431e5c06550c218dce43288610c7671194430863d380ca218431e5c06510c21a6ce3aa68410d1d73153420869cb80a9a10438d9526190821c6aa930c8410d2e72d51420869b38ea8a10430f9d85450821a3ae62a28410d3970151420861fbb2a8210431ddd5611082187ce9b2c6410c3d74d96320863bbaac3190430f9d3650c82187ae9b286410e1d6494c320870eb22a6190439554e610c821cb4a6b006410e59535803208764992c0190430f9d2639442187ae931ca210c5e73d96410862eb9ecb208438b55262904218bce63288210c5d73194410869aba4a2208434ddd5411042187ce9b2c6210c3d74d963108726a9cc5188430f9d0650c42187ae83286210c6d7694a21086aab98a9108435c5c054884218eaed2944210d367494a21086b3baa8290843595d73148421b4ae998a4210c767615121086aab98a8908435c5c054484218eceda9a4210d367494921086d2ba4a490843595d64248421e48a8a124210d65750c921086d2ba06490843d154c3248421bc2e01924210c5e73191500862eb98c8a80430f9d0635402187ae831aa010c7b76540500871cb22a0280439658d50140218beeca98a7a05367194f43d021fbaac3a1e812d5c76550f40a6ce3
  | 26 => 0x1fbb2a819643c3951320cb21e1aa89906590e365498432c871aaa4c2196438d951610cb21c6aa8b086590e555358432c871d2a4c0196438e552600cb21c74a8b006590e395458032c872d29ac0196439654d600cb21d9264b006590e2e5458b41c8716aa6c4a0e430f5d664cc72187eeab266390c3d7695331c861fbb2a998e438b553624c721c5aa83126390e4d5318931c878aaa26218e430f9d0635432187ae831aa190c3d7695050c861fbb2a828643879526314321c3aa9318a190e1e5458c50c870eaa2c6286431edd95014321cb2c6a80a190e4e6358b548872ab1cc3aa443479cf5495221a3ce7b22a910c5e73181548862eb98c0aa4430fdd95415221ccac5308a910e34715935388717322c5a9c438d59261d4e21ccac530ea710d1e74d4e538870e39ac929c438d9926194e21c6ac930ca710d1e74d8d538861f3a0c0a9c430f5d06054e218beeca98a710d1e73d53438868eba4a7a1c43395c662d0e21c6ca930c8710e3554986438868f39ea8a1c430f9d85450e218f4e03288710c7970194438861fbb2a821c438d5506150a2196ce9b0a6510e55531853288764992c019443555cf54d06218eaeda9e8310d3574d4f41887172a2c420c43555cf54106218eeecaa08310d3776550418871bbb2a820c434ddcd5410621a68e0aa08310d3574d4c418869abae8620c43c554f4310621b4ae5a188310d357550c418871aaa2c020c434d9d2538c62196ce93146310ce67299131886ab39ca898c431d9d8544c621a6ce929a6310c767614d318872729ac418c438b59664c8621c5acab264310e3565993218871ab2ac990c432d9d363c86218eaec20ca110c7b76540508870faa2c72a243955c66395121c9cc6b14a890e5663586544862f398c0aa243175cc605512187eecaa0a890d1d73990544870eb26a729a438d9916194d2187ce9b0aa690c3d74d85534869b3a6c2a9a430f9d06054d2187ae8302a690c5f7654c534868eba4c629a431b5cb65d0d218eae3b2e8690c7571d96434863a3aac321a4395d4d6190d21ca8a6b0c8690ce472586434863db82caa1a431e1c16550d218dcebb128690c7675d85434863d380ca21a431e5c06510d218d8eab108690c7475584434871a2a2c3a12439514d61cc92196ce9b0a6490ec932580324863bbb2a7a0a43399d662d0521ccceb3168290ce57098b414868eb9ca920a43179cf65505218bae7b2a8290c3e76151414868eb9ca820a434d5c6541052187eecaa08290d957395041486d2b94a820a431ddd9541052196eecaa08290da772550414869bbb2a820a438ddd95410521a6ee6aa08290d37725504148793b92a820a434d1c154105219c8e4b188290d3574d4c414863bbb2a620a434d5d74310521a6aeaa188290f175350c41486d3b928620a434d5d54210521c6aa8b008290e1d
  | 27 => 0x63351cd6210531a6ae9a908298d3575d08414c6cbb9a8420a63c9d494210531c6aa8b008298d9674d46314c637394c9a82631b5ca64d413187ce9316a098c3d7498b504c63dbb2a0282638ddc56414131c68e2b20a098e2e64988504c716b24c4282638b9916214131c5ac8b10a098c7576d04504c71ab2682282639958b4114131c6ac8208a098e6562104504c637390c0aa0631b5c8605503187eecaa0a818e2d54588540c71caa2c02a0638b9916215031c9cc6b10a818e6562984540c735314c02a0639a58a6015031c74c8b00a818e5a63580540c735312c02a0639a5896015031ce4c2b00a818d3671d53430c696b90a9a18634e5c054d0c31c6ca930c8618e3554986430c68f39ea8a18634d9c75450c3187cec2a28618d2d72151430c69cb80a8a18630fdd95410c318eeeab088618c3e74181520c61eba0c0a90631bdd95214831c5ac8a90a418e6952580520c66ab9cc3210639954a61908318f4e032a8418c7970195420c716b24a4190638b591520c831ccaa53086418e6a52580320c734a92c019063b24c9600c831c3aa931c8218d3574944410c69bbaa8220863175da538c431acae42a46218d7170152310c63abb4a7188634d9d2538c431aaeeaa0a6218c7676151310c6b2b90a8988635c5c0544c431a6ce929a6218d957494d310c6aabac8698863c5151434c431b2ae81926218f45520c9310c6e8b8064988631b9c864540318dae4322a018c3e74189500c61eba0c4a80631edd95014031c72c8a80a018e6962540500c69ab8ec72a6434d5c66395321c3ac631ca990d2e7218e54c868f398c52a643475cc6295321a74e0314a990d397018a54c868f39ec32a643475cf6195321a6ee2b04a990d1e7318254c868eb98c12a6434b9c86095321a6ae2304a990c5e7318154c862eb98c0aa6434d5c66355321a58e4b1aa990e1d6318d54c8697394c0aa6434ddc56055321a3ce6302a990d1d7318154c8697390c0aa6434d5c4605532187eecaa0a990e666258454c8716b24c5a9e438d99161d4f21cccc4b0ea790c3e7418153c861eba0c0a9e430f5da5414f2187eecaa0a790c5f7654c53c871d2a4c029e438e5526014f21c74a8b00a790e395458053c872ca9ac029e438d9916114f21c6ac8b08a790e3a6498053c871cb24c029e439c5866014f21c74c8b00a790e396458053c872d31ac029e439a9896014f21ce2c2b00a790e365498743c871b2a2c3a1e431e9c06590f218f2e032c8790e365498643c871aaa4c321e438d9516190f21c6aa8b0c8790d1c7355143c8716aa6c4a1e438b5506250f218f4e03288790c797019443c868eb9ca821e438b9516210f21c6ca930c8590e355498642c871b2a2c3216438d9526110b21c6ca8b088590e365498632c871b2a2c3196430f5d6640cb2187eeab206590c3d7695032c86
  | 28 => 0x5331a74e031ca998d397018e54cc69ab8ec52a6634d5c66295331a3ce6314a998e2d6218a54cc697396c32a6634b5cb6195331a6ee2b04a998d1e7318254cc697390c12a6634b5c86095331a6ae2304a998c6e7218154cc636b90c0aa6634d5c66255331a38e6b12a998e2d6218954cc68f39cc0aa6634ddc56055331a3ce6302a998d2e7218154cc696b90c0aa6634d5c4605533187eecaa0a998e566358454cc71b2a4c321e638d5526190f31c6ca8b0c8798e365498443cc71b2a2c221e630f9d06054b3187ae8302a598c3d7695052cc61fbb2a8296631bdd95214b31c74a9300a598e395498052cc71d2a2c0296638e5516014b31cd2a4b00a598e365498742cc71b2a2c3a16638d9526190b31c6aa930c8598e365458642cc71aaa2c3216634b1c95450b31c3aa9b1a8598e1d5418d42cc696b94a821663879516310b31c6ca930e6598e365458732cc61ebacc8196630fdd5640cb3187aed2a06598c3f7655032cc7872a26419663c3551320cb31c6ca93086598e355498432cc71b2a2c2196638d551610cb31ccaa4b086598e3a5498032cc71caa4c0196638e951600cb31c72a8b006598e6a5258032cc734a92c019663b24c9600cb31c3ca8b1e8398e1d54d8d41cc61f3a0c4a86630f5d0625433187aed2a0a198c3f7655050cc7172a4c4286638b5526214331c5ca8b10a198e2d5458850cc63dbb2a0286639a5895014331c9ac7316a918e6562987548c697396a92a4634b9cb64552318dce4302a918c6d72181548c61fbb2a82a4639558e6115231c6aa830a8718d2e74d4a528c716392c9294638d9926194a31c6ac930ca518c3e74181528c61eba0c0a94631bdd95214a31a5ce5aa68518cd57198f428c696ba4a5a14638d9526190a31c6aa930c8518d2e72d51428c61f3b0a8a14630fdd95410a3196ce9b0a6518ec932580328c6b2b96a9a0c63879516310631acae5aa08318c7776550418c69bbb2a820c638ddd95410631a6ee4aa08318d3470550418c69abae8420c63655cf4210631e4aa5a108318d3575508418c71aaa2c020c638759664cc631c3acab266318e3565993318c71ab2ac998c631d5d841942318f6eca80a118e2f5458a544c726b1cc52a263995c66295131cccc4b0ca898c6e72181544c636b90c0aa2630fdd95415131a5ae5320a898e3454587434c716b26a5292631bdd952149319a8e6b0c8498e6752586424c732292c3212631e9c065109318f2e03288498cb674d85324c764992c019263359d663d0531caceb31e8298cd57098f414c696b94a920a630f9d85450531a5ae52a08298d3571950414c61fbb2a820a63655ce5410531b4ae52a08298c7776550414c65bbb2a820a6365dcd5410531a6eecaa08298e3776550414c69bb9aa820a63c5dcd5410531a6ee4aa08298d3470550414c69abaa8620a
  | 29 => 0x8a0a0e1d639045050716b1482282834e5c241141418f4e0312a620c79701895310637390c0a98831b5c86054c418beeca98a620e4d53588531072ca9ac0298832ddd561d0c41c6eeab0e8620cb772587431065a382c3a18830f5d660d0c4196ae3b128620da572985431069bbaac2a18832b5c86050c4196ae23028620c7a7018d521063cb80c6a90838718d43548418bce6302a420c5d731815210637bb2a4290839358d5214841cd2a4b00a420cb775587421071bbaac3a10832ddcd61d0841968e0b0e8420c3d75983421065ab8ec6a10834b1c95350841b2ae730a8420d3775585421064eb98c0a10832d5c4605084196ae33266420cb574987321065ab8cc9190832d5d2618c8418f4e032a6420c7970195321065ab8cc8990830fdd5644c841a98e4a9a6420d4c73549321063d386ca190831e5c3650c84196ae33206420e4f654c83210726b2a64190832d5d2610c841d9264b006420c3d76952411063abb4a920883a558d4390441d4ac4a148220c9d731814110656b90c0a0883a5d8d435044196cec21a8220ea762509411065b3b084a0883355cc60504419cae43028220e3575d95411065ab9ecaa08832d5cb655044196ce1b2a8220e3676d95411069ab86caa08832d5cb635044196ce1b1a8220d357598d411069bbaac6a08832d9db535044196ced29a8220e976394d411065b3b2a6a0883a5d8d535044196cec29a8220f155314d41106d3390a6a0883695c85350441b64e029a8220db17014d411065ab9ec4a08832d9c36250441a6aeb3128220d3775589411065b3b6a4a08832d9da5250441d4ec52928220cb6765494110753b12a4a08832d9d85250441b2ce62928220d95731494110792a90a4a08836c9c05250441b62e02928220cb676cc9411065abb664a08832d9da325044196aed1928220cb6764c9411069bbaa64a08834d1d5325044196cec1928220cb5760c9411069b3a864a08834d5d43250441f0a641928220db2700c941106d8b8064a08834d5d66050441a6eeab028220d967318141106cab98c0a0883699c86050441b4ae43028220e3575181411074b398c0a08832d5cc6050441d2ae63028220c95731814110753390c0a08832d5c86050441d4ae43028220ca572181411065bbb283a80832d1d94194041b60e0a0ca020cb47650550106d838282a80831b9c863540418dae431aa020d3571d0d501062f398c4a8083175cc6254041a6ae3a12a020d3a70d0550106b938482a80834e1c14154041ae0e0a0aa020e3776505501069a3b282a80838d1d94154041a6ee6a0aa020d37725055010799b8282a80834d1c14154041e60e0a0aa020d3070505501065bbb28228083a598d4114041d2ac6a08a020ea6625045010752b1282280831edd95014041cb2c6a80a020e69625405010697390c72a6634b5c8639
  | 30 => 0x3109500cb94a1084a8065d2dc93254032e94c4992a01974b424c9500cba521264a8065d25093254032e9084992a01974b734c9500cba531a64a8065d2d0d3254032e9486992a019749434c9500cba421a64a8065d2dd93254032e94ec992a019749764c9500cba43b264a8065d2dd13254032e94e8992a019749744c9500cba43a264a8065d2d913254032e94c8992a019749644c9500cba432264a8065d2dc53254032e94e2992a019749714c9500cba438a64a80654e9d03254032a72e8192a019749320c9500cab938864a80655c5c43254032e9265b0aa01974932985500ca9dba2c2a80654e1d16154032ab0e6b0aa01956872585500cba4992c2a80654e9d06154032a72e830aa01955a73185500cab5390c2a8065d24c8615403287aed2a0a01943f76550500ca67bb26428065a39913214032d1ac8990a01963654984500cb1aaa4c228065b14ca6114032c6ca8b08a01963554584500cb62992c2280651d5da5114032c6cc9288a01963564944500ca3bbb2a2280658d9915114032c6ac8a88a01963a54980500cb1caa4c028065b24ca6014032ce4a3300a01967151980500ca3dbb2a0280658e9915014032c72c8a80a01974932540500cb3930aa0280659c5855014032a9ce5a9ca7a0c6e7218153d0636b90c0a9e8317dd95314f41a9ce7a94a5a0c5e7318152d062eb98c0a96831bdd95214b4196ce3b2265a0c7a70d9432d063cb86ca19683535ca530cb41c3cc8a9865a0d4d7394832d0717322a41968353dd5320cb41a9aea99065a0e565358432d072aa9ac21968399949610cb41ccaa4b0865a0e5a5358032d072ca9ac0196839a949600cb41cd2a4b0065a0ec93258032d063dbb2a028683539cb5394e418dce4302a720c6d72181539062fbb2a629c839554e6190e41a3ced29a8720e1e7694d439068eb84a6a1c830f5d46050e4195ae43028720cb57118143906a739ea529483179cc6054a418bae6302a520c6f765485290732a94c3214834b9da5250a41c5ced2928520d2d70949429061eba8c0a1483275cc6050a4196ae23028520cb571991329065b3a6c2994831e9c3650ca418f2e1b286520e1d6494c32906a6b94a61948387591530ca41c5ac92906520d4d739483290716b22a41948353dd5320ca41a9aea9906520e55539843290732a94c2194839694d600ca41cb2a6b006520e6a525803290734a92c019483b24c9600ca41ae2e1a0ca120d3a70d05509063dbb2a02848317dd95314d41caea6b0c86a0e1e6550c4350637bb2a42928399d496190941c5ccaa1084a0cb671d91325061f3a8c8992832d9d3614c9418f4e032864a0c7970194325065a38ac8192832d1d1610c941d9264b0064a0c7b76540505072731cc4282839358e6214141c9cc6b10a0a0e4d63588505072ab1e82282839958b4114141ae2e1a
  | 31 => 0xaaa4c228865b14ca61144328eeeca88a21963664544510cb1ab22a2288658e9526014432c72a9300a2196c932980510cb38a8cc0288658e9516014432c72a8b00a2196c932580510cb38a8ac02886533dd932d4032d1cc8996a01968d644cb500cb872a265a8065c355132d4032c6ca930ea01963554987500cb62994c3a80658d95161d4032c6aa8b0ea0196c532587500cb1b324a3a80658d59251d4032e8a6528ea01963664547500cb1ab22a3a8065d14c951d4032a74e9a84a01953974d42500cab938ea1280655c5c750940328eee2b24a01947471592500ca1fba2c3280650f1d16194032ae4e3aa4a01957171d52500cab9388a9280655c5c45494032ab6ea994a01956b754ca500cae5baa6528065d2dd53294032f14a8994a019789544ca500ca9d3a6a3280654e5d35194032e64a928ca01973154946500cbe0994a328065cc9515194032e62a8a8ca0197c132546500ca9d3a0a3280654e5d05194032ae6e2b24a01957071592500caad398c9280655a9c86494032ae4e2324a01957171192500ca9d3a0c7280654e5d06394032ae4e231ca0195717118e500cab938c87280655c5c64394032a74e8314a0195397418a500cab9388c5280655c5c46294032ae4e3214a0195717190a500ca9dba2c3280654e1d16194032a74e830ca01953974186500caad398c3280655a9c86194032e1ca8992a01970d544c9500cba2994a2a8065d14c951540328ece2322a01947571191500cb27bb264a8065931d93254032e96e0992a019748704c9500ca1f3a0c2a80650f5d061540328f4edaa2a01957271d51500cab8b8ea8a80651e9d85454032ae4e22a2a01957171151500cb8d2a664a8065c65533254032e54a9192a019729548c9500caadbaa64a8065c69513254032e32a8992a01956b754c9500cb952a264a8065ca5513254032b96ea992a01974b754c9500cba5b2a64a8065d2d513254032e94a8992a01978a544c9500cb852a264a8065d25513254032f12a8992a019709544c9500cba42a264a80651e9db5154032a74e9a8aa01953974d45500cba4996a2a8065d24ca5154032e64a928aa01973154945500cbe0994a2a8065d4cca5154032ec46528aa01975132945500cbb0994a2a8065d04ca5154032e9264a8aa01973254545500cb98aa2a2a8065f04c95154032ea664a8aa01976232545500cba8992a2a8065d84c95154032e8264a8aa01947a76145500ca9d3a0a2a80654e5d05154032e926428aa01955873591500cab4392c8a80655cdc56454032ae0e2b22a01955a73191500cab5390c8a80655c9c46454032ae2e2322a01956a7290d500cab4b9486a80655c9c64354032ae2e321aa0197194310d500cab539086a80655a5c84354032ab4e7212a01955973909500cab938c84a80655c5c64254032ab4e6212a0195597
  | 32 => 0x59c5856015032c5aa8b14861947575986430cb1b2a4c3218658d5526190c328eeeab0c861963654586430cb1aaa2c321865875954310c32c5ca8b10861968d43588430cb0eaa2c7210651d5d66190832c6ca930c841963554986420ca3bbaac3210658d9516190832c6aa8b0c841961e5458c420cb16b2a8421065a358d42108328baed29c641946d7694e320cb0fb2ca89906587d95544c832b8ce321264195c571909320cb17b2ca8990658bd95544c832b8ce321a64195c57190d320cb26baeca99065939db654c832a9ae1b2a64195c671d91320cae2b8ec899065535d6644c832b8ce332264195c571991320caa7baac899065a3590644c83299cedaa264195c671d51320cae2b8ea899065729c3544c832b92e1aa2641958d75951320cb47b2ca899065c3d96544c832e1eeaaa2641968f65551320cb87b2aa899065339d8544c832b1ce82a264195c671151320cae2b88a899065729c0544c832b92e02a2641958e74d85320cac6ba6c299065535d6614c832b1ce930a641958d74985320caa7baac299065b1584614c832a9aeb302641954f75581320cac7ba2c099065631d1604c832b8ee2b0264195c471581320cac73a0c099065635d0604c832b8ce230264195c571181320ca67bb265a8865a399132d4432d1ac8996a21970d544cb510cb1d2a4c1a88658e55260d4432d9265306a21963a54583510cb1caa2c1a8865b24c960d4432a6ce9a8ca21953574d46510cab9386a3288655c5c3519443287ee8b04a21943c74582510cab9386a9288655c5c35494432ae4e02a4a21957170152510caabbaa652886559dd53294432b8eea994a219747754ca510cbc32a26528865e15513294432aace7b24a21956672d92510cb1ab20c9288651d5da43944328eaed214a21953774582510ca9a3a2c1288654d9d06094432a6ae8304a21955673182510cab3390c128865c3551325443287ce8302a21943d74181510ca3b3b6a8a88655c9c35454432ae2e1aa2a21947676151510cab9380a8a88655c5c05454432e2aa9992a219725548c9510caabbaa64a8865c55513254432aceea992a219725544c9510cae3baa64a8865d1dd53254432e8eca992a219747544c9510cbc32a264a8865d15513254432f0aa8992a219705544c9510caab39cc8a8865599ca6454432c6ac8322a2195367498d510ca9aba4c6a88651d9da4354432e2a8621aa2195667210d510cab2b9086a88654d9d26254432a6ae9312a21947676909510caab39884a8865555cc4254432e4a84212a219536740c9510ca9aba064a8865d14c83254432a6ee8b02a21953474581510caaa39ac0a8865591c96054432a6ce8302a21953574181510caab398c0a8865599c8605443287aed2a0a21943f76550510ca67bb26428865a39913214432d1ac8990a21963654984510cb1
  | 33 => 0x142caac6b08a0a1637745845050b1a3a2c2282851d9c46054c428eae2302a62145f7654c5310b2aa9ac2298859654d6014c4287aed2a4842146d769524210ad2b8ec8a10854b5d64350842b4ae321a842145e731815110a2eb98c0a88851ddd95114442caac6a88a221671515805110a3b388c6a80851d5c463540428bce630aa02145d731855010a3dbb2a0280859658d5014042ce2c2a80a02164e6358b54ccb2b31ac3aa6654d9c75495332a6ce3b22a9994767118154cca3ab88c0aa6650fdd95415332c9cc6b10a99953671d5343ccb1b2a4c321e658d5526190f32a6ce3aa2879943e7615143cca1fbb2a821e65875506350b32a6ce9a8ca39943e7418151cca1eba0c0a8e651ddd951147328eee2b24a1994747159250cca1fba2c3286650f1d161943328f6eca80a19964d6398b548cb33312c3aa4654d9c75495232a6ce3b22a91947671181548ca3ab88c0aa4650fdd95415232c9ac7310a91962d54189438ca9b38ea9a14658d9526190a32c6aa930c851953671d51428ca1f3b0a8a14650fdd95410a32a6ce9a8ca31943e74181518ca1eba0c0a8c651ddd951146328eee2b24a11947471592508ca1fba2c3284650f1d161942328f6eca80a11953671d52544cb1baa2c32a2659558e6195132ccac530ca89953671d91544ca3b388c0aa2651d5c4605513287eecaa0a89953571990544ca3bb8ac02a2651d1c56015132a6ce3aa6869962c5458b434ca9b38ea8a1a654d9c754d0932c38a8b1e849953671d51424cb1ab8cc9a8a654d9d35194532c6ac9a8ca29947776544514ca1fba2c028a650f1d160145328ece3326a09947571993504ca1f3a4c3a82650f5d261d41328f6eca80a09963664984504cb1ab24c2282658d9916114132c6ac8b08a09967261983540cb38b0cc1aa0659698d60d5032cd4c4b06a81967261583540cb38b0ac1aa0654d9c75495032a6ae3aa4a81953a70d52540ca9cb86a92a0651ddc560950328e8e2b04a8195367198e540ca9ab8cc72a0654d9c66295032a6ae3314a81951e73d86540ca97396c32a0658d5846195032a6ee2b04a81953471582540ca8f398c12a0654b9c86095032a6ce2304a81953571182540ca9b38ec8aa0654d5c76455032a74e1b22a81953970d91540ca3b388c0aa0651d5c46055032a6ce331aa8195357198d540ca9b38cc4aa0654d5c66255032a3ce730aa81952e72985540cb1ab08c2aa065471cd6055032a58e4b02a81953771581540ca9a38ac0aa065479cc6055032a5ce4302a81953671181540ca9ab88c0aa0650fdd95415032c6aa9308a81963554584540cb1caa4c02a0658e5516015032c6cc9308a81963664584540cb2b31ac22a065999896115032c74c9300a81967261980540cb38b0cc02a0658e9916015032cb4c6b00a81966a62580540cb3930ac02a06
  | 34 => 0x4a321d357498a5190eab398c528c87995886294643a6ee8b04a321d35741825190eab398c128c87599c86094643acae4304a321c6e721815190e36b90c0a8c874d5d74354643aaaeba1aa321c7676d495190e3b3b0a4a8c875c9c05254643ae2e0292a321d35749895190eaa39ac4a8c87995886254643aace7302a321d37745815190e9aba0c0a8c87559cc6054643acce4302a321d65721815190e3bbb2a228c871d9c462542438eae2312a121c75769445090f33314a2284879958a51142438eeeca88a121e66625445090f32b12a2284871edd95014243cd2c4a80a121e97539864350f33a92c3292871bdd95214943ccac5a8ca2a1c77765445150e3b38cc5a82871d5c662d41438dce530ea0a1c6d729875050e3dbb2a0282879998a6114143ccac5308a0a1e66625845050f32b12c2282878ddd16114143c68e8b08a0a1c3d769524310e2ebb4a921887655c76450c438ece2302a421c75711815210e37bb2a429087995496114843cd2a4b00a421c6e721815110e36b90c0a88871ddd95114443ccac4a88a221e71515805110e3b388c4a80871d5c462540438dce430aa021c6d721855010e3dbb2a0280879a5895014043ce2c2a80a021d5671d4e53d0a3b388c0a9e851d5c46054f428beeca98a7a15367194f43d0a5b38cc5a1e854d9c65350f42aace7a8ca3a161e6350e51d0a2f398c0a8e85175cc60547428eeeca88a3a147b7654050d0a3b388c0a9c851d5c46054e428beeca98a721659535805390a3abacc321c851ddd56190e42ae4e029ca3215717014e5190a9abae8528c85595d74294642aace7b24a32155573d925190a9aba6c728c854d5d26394642caac631ca3215667218e5190a3abb48728c85559cc6294642aaae6314a3215727018a5190ab8b80c528c854ddd16094642a6ae8304a321556731825190aaab98c128c85599c860946428bce6302a32145d731815190a3b3b6a6a8c851d9d85354642ae4e029aa3215717014d5190a9abae84a8c85595d74254642a6ae931aa3215647258d5190b2ab18c6a8c851d9da4354642acee4a1aa3215647250d5190b8aa1886a8c85599ca6054642a6ee8b02a321535741815190aab398c0a8c85555cc6054642acce4302a321477765445190a3b388c6a84851d5c463542428eaed288a121656639445090b2ab1ca2284851ddd95114242cacc6a88a121655635445090a3dbb2a0284859658d5014242caea6b0ca6a145f7654c5350a5b38cc5a1a852b9ca61d0d42caea6b0c86a1654535864350a8f3aec6a1a85479d85350d42c3cec29a86a151d7014d4350a573a8c4a1a858b9d46250d4295ae031286a16a7529864250b2ab1ea328a851ddd951145428ece331ea0a14757198f5050a2f39cc3a8285175ce61d41428f6eca80a0a1656639845050b2ab1cc2282859598d6114
  | 35 => 0x40050004008000000002403400a00200240320000050058002002002000402800d0000008024000013800001802f000801000400000a800801800100280000020000080000000004004800000601d0008000006000006000001c0010000024000001000800401400b00100000000020010004010004000801001400d003800c00a0080010004002000001800c000018004000c00c000001009800a007001800800200f0010000004002005017000a056009803000000401b0028008033002000000200300080000000000048000012000002800000400b000001000a00100300100020000060010006000001000c00800200000040040010028024006000000004c006013001800402c017000008c0000020000004022000001800402200100080c800600d0088004012005000000c004000000000c00800600000a800000300080080220070010044028004000000400a013002000000000f000000c00600f002001c0000030038000002002000800000c000000004c03e0000078018004000000000000403c0040018002011000000c00e01400680180000040000004030009003000403a00d00280000000000008000018004000000c03000400080500000020010000000002001005c00600300a803802a000000801400600d000802000200100000000000040020000010019009001403c000001801800001a000802000a005003800800400d000000c0080070000030004003000800000a006000802400000f005000000000400b800408a0120008008012003007801c006000001803001e002000000000400900000000040000080010000003006003c000018000801c010000000003c00a003002009800200f0000004028005000800c00a0080000000002015000804800200b0010024044001000807800e000000000800600a0010010028005009800002e002002800c000009000800001e01c001801c02000000200200000000038000006002006002c002001000800001c0110008010002000001803400000300180300040250000040004000003000800200000080dc00c006000004c0020070020000006000004802400201a0000000052003002802001200a000001400000200000980000050028050014013001800000000800080080020030020018004000001001800800b0000020006011004004c00c00100a000000c000009000c008002001001000000200156671d4a52d0e3b388c0a96871d5c46054b438deeca90a5a1d6672d4651d0e37390c0a8e871b5c860547438eeeca88a3a1c7b7654050d0e3b388c0a94871d5c46054a438deeca90a521e69525805290e9abae8728c87555d74394643ae4e0294a321d717014a5190eb3396c928c87595cb6494643acce431ca321d657218e5190eb9380c728c875c5c06394643a6ae9b1
  | 36 => 0x1003e000002000000c000000000800e010001000000000b0000004010001002800000001900000000160000010044000005000800400a00900380100280020030004006000004800000e001007003800000000000080020010000004000006003000000000000080400240010000024014000005009004200c000001000200a00700780060040088004000001007000400600400200080140000028028016004000000c00600100180380000000008014002002002800c06a000015000c000006003002c00e0040008000000002012000403800000500000220020078038022003001801000a02c002805c0260050010004004007012800c0000000000018012007000000000a00000a0000012001005011000800a00000240020040038000000002003801002000000a801400a003000002000002200a000000c02a005803c01c01f00480040220110010074010001000802c00c000001801c00000200000100160000020000000008008000000a000008003c004005001000c00200000280180000000028000000000000000c00a0080000004000013004800002a000000000001e0000010000018001000801000200c0010010024000000000400000500000000000000000000000012000004801c00600000140060000000004006011000000000c006002800000600000480380020130000020004010000008803a000002000401c0000000000000000004001400000a00c800000e003001002000000000080000000010000010000008001800c0140010060000010011002004c002012000000000800f0030014006000001001802801a000007c01400f008000000400c00e800400c0060010008050000000001c0020000060004016000002800401e000004000402801e00880000020000288000000000004000400000b007003400000b000000001a000000001c0060010048000000008000003800200000100040060000000000000002000801000602f00080140060010068000014000000800c004004001000000000e0000068000003006000001e009004000c01a000000807400000b0058010000009009001c016009000000001600000380040000000018070020013000003800c00600000100020020000000066007000800c00000300080000000050030000002000000000000c0080000000000009000000c00200400100040160150020020000002000000000000000000bc000003001000001a00a002000c03c003002001800800400f001801201a003000800400000580640060050008014002008000000000a000000005c07c008002801000c0130010014000002000000c002000005803c0100030030000000003005000c002014000800c000004000000801e002000000007400d001800c0020010008008000010000800003e00
  | 37 => 0xa00380200000030008000018000001000000c000000800801201500580340160090000018000004009002400200300080100280010058010010001002802801001400c80380040050058000000000005800000000c00180200020000000004004009000800c00a0010000010008005001000c0060010008004000000009804c0000010000000018009000000000000c0058004008002002000c00802b002003000604500c8000004015001001c004000003800c0420040000050004010000002001801c003800c00000300180140020130000018004000000800c000001005000000a01900080040320010008024000007001800c000001002803800e002003001000600a001000400800f0008048008003002800c000001003801801c02800080200060020008004012000005000001a002002000001c001003000000000c000000001a000002000003800000180140020260008000000009000000001e00c000801801200400000000360040068054000001003800005200400000040000000020000000009002001c0040070000000008003009000c0000020020014002006000801000000000400ac02c003006800000c000001000000400900000180040020028038098001001801c004016000808800000e0000000008013000800001600200500040000050008000002001000000400602f001806c000000000002c00800100000a4000001006803001e01b001000000200700b806c00000000980d400001b001000800800000800000020000000028000000006004000000c0000000002001000800800a00d002002000600100e800c04e0040018010000011000800402c0000008018018000000001402c0020000014000016000000000c0000000008006007000800800200a000000400c0010008004004002003000402601f005800400c0010018000006001000000000e008004800c002001000801400601c0028000012008001800c000008001800000200300200080160010010014006000001006c01c009009000001400b001001400000a0010014012006004000401e00b0008044002000001803c000009002000001e003000800400800300280140000020020000002000000007404200d00c801001a00500080080180050048008002005002001400200300300000060160000038006000002000400a0070000000008000000800401c002000801400000100b001002c005000000000200400300000000100040000000010003000000e0010000008000006003002402600500100080040020000004002001000001000e0030010060004008000801c000005004800800200100100840000020118000028000000803001200800100080360130040014002008000000400000200400380000050000008006000000006800000b02b80
  | 38 => 0xd2b5a7860300006861378ec520ec11a112cc4d10680e80000dd31c546cb4580000000097b28ecc250000e8744d42674920a3613f400035f49b100011462bf8f7f04a96c8319cc3549850900000f3c46b49851c24edc31280000268000344cf322e100c601a84c955b8a7600012b80000fba0000a1d547d4e500005dc1ed856d0000612335400009c4b823fa48280000dda1e08d8900006f50000000425c00014500000000258348153d356c83200001c92af4b764238000000000040ed1a00e140003120c881c845d00000b354ac9591343055f1c0d3b700016ec0aa400053187f0000043a58c8000431c7070000daf57041831938ed9229cb3e3034a303a9837f2f941f7574c5f2004045950d919b2b4403d05607e55ab12331650ccf3a58ec7198c00057100000001033000056f4a68000452c0004ccc000376c000000108939c9650204c3b11f547622ba53da02d83c200000002ea800000000004be146d3fc533400b403800c8cbb368016d3cfd3e0448873d07ccb2d229829f15ac3fb16741b533453720f2c97518140004bc0ab31960000000034121f018c4b6cb1e2918b4b1f7c7fe388d4a54c1c9144aa50b61301567212864546c145b3f78390413cbe6016cc0027440000b6043b2cb090d1facdea3011628000000029603912ce40d751050f5323800037ccbe715954dd03e4ead1fcc58d000106600380000e4caa00000000000127627bc00000000000000000000000000008e937fc6e32974ed50c48000439000000001a655951d13f6109209cc103000000052e800000010ae4fac667008ccfe01a0bee274d37c20950ec00005fc00000004fb5596482d3ff00008dd2e6cb010000000000000000000000000b6f00002914df400000002ff25605a235880004e8476e5b3c1e8354d5150298f5d46951724b8c0bc000126c0000479051c3c83a0400005bce42169404000005ff0000b0e4ff000000002b110f484143095045580bec31ec0001954b1b45154d50bc033c553946249f8b6c48d48b624e8b4f1a8906d4eb546b50c08fc022840a36e83710000000000114000016315138005007800c0020000000074002001002000400000000000680080000008000000001002800400e00300000080080000030008008000000800000600000c00040000040038020000001000000c010003001000000801e000801c018021001000c00000000180040060060098000002007000000c0080090020000000002009001402c011003002000e00000080580280010150008000000000000802a003001000000000900c80b402200b000002000c01d0010088010000001801402a0030030040088001007000801e00f000000000000f005801800000100380000300000020010008014001001c03200600300c000600b002003800600a00000480060
  | 39 => 0x54608b1314954b141c7bc3580c032f744060000000541c4540000c132a740000000d0000000000000671000000000008af196565249b8dd03b6c1ec023c48f46580001f80000594c49346200cc0fb8d09000127400000002d9d65f0000d8e1168fb30e3041055908b90000925477d55b1ccc136000144f41546490000000112400000000005bc00000000281000109d0fd056e253048402cc00000004370000d224f70a642cccd862d149380640e0c0f5c3280000bf8230c86237780d12d28142509caef3ce4368195caf9398d2201c108b70fe900c30c4cc84d3453701b547935a8207397d244145924a4d594ac31c8438292471609905d41440ed62c944fb2f4d678450400025695a3234d0060000000076886932f8e514a0d0090974cf64fd4000215000042f05cc536842d4a286282f8cf0c0b1cfbd0000000562c8184f547790000000000134215749671d19063000000044cc0004b48395357400000000004accba445c000003b48ef0000dfa34f8df1244400000001fe0b5c00000014002d59286100d2da1f9005c20d519532453f743f800024d4000174c6b147208e300004f038c92b6020c6d94c7c28c000000000008e02a0000032fd1a658d508c149800021d80005b151154c484b252b429a0fc80002d752790bb962d30a01ca5824bdb2fa40001ea164e1daca1b3998f6d25652170d54000000102a00010710bb00004cdc8373ef80001bc87ef0f184fa000086b1624df637844a92e610825290000149403c3ff90a202fcbba48884610000301042477316d80984e6c0073d4167433b84d0293d4b71bec00014380000000000000000037ac52c48300000000e112864000000000024990440000000182930c000000006e011e2d6d07f2ee03720000000000000000011cb000000058d13b207848f3000000056c00000d70000206c23a00009ad4914000000100a3a088d6206400021f80004460466246c000382800000000741f3156b00001e700002c1069148d0da45e0057c4e8386000007d947b42e8076258c9194e790030000664037c0000000fcd395ce45168c5ce3b8cfac00004a112ad08800012773efc00002e42824d78d271eb8dc32dc0000000000035608ce08d4f3523b028050802f83eb4ec81b58d644b71031251476837d4005209cbcd2bf502919c000300014ee182cacb0d68f6a246878c0484cc74e3402400012f159c0a1800006ad16407400b2c1863994d36000075715ecbd14d7cce819fc40e4194a593e9505053e02624e2d4f10b88d4912589e6546d0d84d68ca61bb12c91644560048d3090000000249126b2f5cae445753f0363549d47b561300012730000f7a000107b318c000039cdc10000c4c2ecc0004e880005a6476f00000003160b3f073472b00000b109340003a8c12f00000001a642de00000000000
  | 40 => 0x40820000000197c5cd588c2b83281028029046301984d61070f273604d260de40220000e950000000000093d44f82af07d435b3cdc20a2cf400000000002ec83fe47e4cda4ce456c1fd4e8d42190b01aac2db1a080003f5452758f5327320c9c216ec949309c680538d5951f10ded1910f2302ecaa52b356562f045861e794c74a493622fa0ab6321886c1578c21599034726f802600607870c0d28b59544c32e5000010a0ca517c4fd3000000034f06f3007cbc41bdc00000013a600000001a10000107808811082a500014930d780002174217138cf9737f459c209048c368c1b74c0c9dc22b02180b582fa3af8aed0000e3d1a84eab48d95a216b4b66128827b00095cd00007960864bb51fa80aa550c00000007a13fb94bf567834f1e34aff00015ca2f5549f01d493e4fe16c111f00001328033463044157ac36c00011913ba805d4e5d4b448c51b72470d91353c8c04bc8b3144e8a413e80d8027c9067000017b51486a41f380001528000000111049755382aed0c341291e135ac1c50000d6d08412883d447d65430000000088300000005a1800000a060600004d31865432000000000004644064d48158499e1d4400041880002cd157f000000052a8c75000104c44311774d3cb7f00000a934916c700010143dc81014960000021443000010a8000000000010d703c8c982b3c6c3000000027040005120a240f9d6ad285121a118919c0f396021c300003b28199088c00007ac00000006d05b9d01f00007651b5000000010a3281922c0000000460454426181940f14c5900014bc0000000473c3aa240535906f8000000081626914f900003133dd532f47280000000000000033300000004cc40002dcc84233f1047227c00000009f700000fc239841b04dd6a80000a16014c960577484800000004298e9f00000001809527153400000000000c2c9f110bc8a52e38e8c4c04b593fc8e643c88d93564000003709132a4d417140879f2a7943e003c79759dc0003e34614019509900012c500011e81b780f5346cb0b43ac000000000000000000000a3800005a72e64000000067b0c8c84f00014ab36f8cf30998f8631b0fc8213116e22689c757e8ffd45f03d02a5014921c52c124ad2bd1cc0e5825100004730000098557b5b183ed04c169a00007930000000115946516fd4a63a187a63c7853a166c1a206b490e4e08000000000011e846b0001010000000055580002bb80000af80003fa82c31334ef5499c8bf00000000000c730000ecc00000ee18b869f3288953319801d0000f0a11fd3ac12a87444f5849c00007bf00016905b88e2428200002f410e545ed1570cb069c4f8c8d037b10952df4b7b55a928e1d58673073cc08298cc6823e8c7743e45ee000120a38ac47457fd51100000000000c3a00013fa0000eaf2ffcd1700014d2
  | 41 => 0xc5b5c0c300000000000bef35a021a08380001bd8000041c0005068bea0d34dc40001237323c4b601380000a1800014c80000000000000000034d150d000000056e050a0000c8c40601d12ed90720000b620001202315c000000000047b8000020000000000000000000000023900015df4a400f80cf95d5026d0cd553d2a14c88a0c000000024e45c830e43503ae400011450461661442508c9650000000381d42d53415e31a504d13e84b8a12540002cdc18b0578343043cb1752c8475282547621cc0000000c2453c14814f380005b4c000502800001f0000000003a1e68bcb14f40005584129511c00000000002c64000000117443fce7a43396244ee06e753809fe13fd16203411eb000095d37752aa1d384ba1a94000135c0000000000000077d00b110b000017300000003ae8000500400000004f82fcd17d4e8119743dc00006955250000000000018500000003d848d10000000387055453300eb044c72c0b90b4400000002e8cc9450fd3d82becaaf30d957d00005b02f286790000d1602893710000e203e9800000000003c24000561c000564cac73d68fdb00005343ca874b0000000000000042a400003bd5fe0000766251c33400012f324f0000000009f20382bb3dc4b2856e4e70260909f07306ef4c6130518407f709e053653cce852c98c0e04604e10a38dc80000200546800021a017c3fe044749c4e9918440642c0d20708c08c507c8966450806b2304c464cf905a0001040033537f301c0000e1024900003531968c6a1a44ba72b5cbc224280000390ae5363d13b2c1cba511ec0c427ad6823bcc54f0a614601ba562c4a98dfb13cd4d918b4a564d5463e24845714ebcad64e384395b6525c36091e31b7c8d93f0143c4cfc7245b546001dd82a120f460116f12df0000eb522608dc38e4a295b2c0004724a2d000008746a95a7236c2cd000025654b0de00ebc0000e2c6dc0fbc00000016ae5ad800055e0000207c00026b8000000000000014f24148000048032f3d0c000000168f0000c5d2b986b62ac00001ecc30e59a16d8000137e26f51b90d280000000722445c0000a6c641000138815fd65b4a1021f000046d27b4a2a159c00059acc74009547d392400006e44bf3cbcc063fc0eb600014e400000001e28000402c421000146f18613642ef47483bed5d400000000e3c44540b8a81000082c541800000000003f90cff0e64b5307111ce40150af1eac00019f4000000000040c94141d8d62e59c444a1174000025106a11106c4294800025bccc02b6d0263654bf51e40b404a70e023f3c725282c9124b08ec402745c11c004eb3fd866b035413b06a84e91c693f203f8a0535b898b2ef8000094950b265939f44c8c820bd000052c007a14e400047612fe00005aa4f202332170000283c000000018200012a0444d3b64f8
  | 42 => 0x8ae12a5c4271e9c9404e056463adc0001658d7c57d400000011be16c49b600015f736dc00000000de2ee4505306c7ba1f0964022d4159503c081574000009500003fb400002dc000000000023b542400000000000ece525464742a8000000000000000002f240003d604231a8c0003ea81b00000020294000000000000ad40001820000203c0e0345110a33c548c1f7156d5174db05a90fe7000013f00000da3f280000f305e62b745ae50354ea2894f2e33152894285475070d6b12b7000000000000f74000000000000007f943009c50c015e5522863745a4e9a3ec512e3e9c9411c6c66d508858e245ca3f5af8f4d2b7c0cb2ce01270000d561ee4c1d1af0a661f195db0ee416703fc0003a104d9000063f3d78cfa563d605000116c5064f634ec09b300000000ac13962f8063208a854925208951790b2e160141008bd3860888238294d18a5758aa358cc94617d01d858804af58644331ec48390000000301401b2aa48fb00000003a74bb40db90b41034e7b0d1062f2d7095b201871c162070d55c92993c944b025e80001e04cb0247d618526c4fc10b0e9018d02c62bb16a61a1d1e91be00fb0e34550000167f23f8000000068502101d935ec00059e472d3f983d5000000056240005aa4ec00830bc8143164940dc00055a16e8105c71f21a8ffc495c519506c00000001060400000573080a5060db921986f9169800056b006219811af2d5062958bc0000000e76023405e000125453a443244a8bcc0b980005a6c93314b4b693190bfb5778abc07780005a30000429c04a1d9c13535e1406514c4cb47154d12af8b77120937b0a2d344457c66c0ba10b506340730d946b4153130e09fd43117ac00000000000000bd600015b32ea4000000028446ec1920001627066c000295d2723e38f0451b945a3c0c45f0ef415d3c9941355e8ab715e40004da0f483360b7e0798a1228f15700500fbb1130e4c5aec4224e70e7700006c6382c00052d44a000000000000ed45bc566a2b9c97413d0f550000dfe0000d7f000000000014380001665000064c0000cb317f8021000034b55dc0000001468000015b4f740000000de241794c0000155e2584d2c12151f054a40004ad0000000005216a07f11a28b0646090760000b414f14d304a5007f000080800010e8000099a000000038502d23d9c134029c0000fc00291e148e22dd4e804ba1489393423e260c1ea000000000000002eb400024c8c142c480000eb943400000000000170386cc4f2d78ac1000000000006560b380001f4871e3e10000000039e2a84ec3125cee800010ed0000b9000000002a7c000000000000007530000f010000834000000000000000bb400000002f73e0151c35780000e6049046e000045ad5da00012213c1c17e4d38487237d2d91d40c385904def48e44a7350d3b
  | 43 => 0x57403400000000005b7400000002c4492c2e13c900004978000000000000000003d3d3524c6800006010bd00000003b88d9e5010f7e4c200000000f76000000022391f10000000112000014792f700014c100000175b840000000abf1d1532c4ac067e17ed16431109283c4d29d064d5e800d4ac957c52f406105010e7d4f53958d983ef0c990ac955c53ecb360b5451d1d8436b35c404934102bd18955ea0f60a40142082f5928f143d2d4c44c292b93a5d20f4c74e5b0ce0bab32f055656182aa20f9143131814a14ac4e41ffc91020c51ae48795350000f8f464065b00016ed29dd13d5a55647150c051000103d2b0d68d0c443a047e0cd04324e8b06bc1cb0a1d4cd1de917515f438e12288cc4da4990257c00045a00003714b1a3e2cbd815180004aa0c9f0001340000000020d8000000064a2d900000000db300000000000d111944000000085029f88aa20016aa17d46dd0adcf792da13a5403c00000015303d88000000164354c884d18c40000308ed0579c64d000069d0000000237800011bc0002c54000202c13a00008a103b00003838000000000050e43e8000000039d00000000d410000eb34a5800000008ae3db80000000e40000000016f956300012663c38d9f1e1049a0674cdb3699536491c69a19c82552c7000018f08960dc0c5157c90702f1cf0b43656a0122407d1bf89f347895a9490145600bcff549547473e7cf0213e489d448d43a4b789923be160d0000fe82478000000000000000000000cdd2b28000324c000000000035d400000005cf0c7000027fd3175220b4600002f24d210d62fe43f60000ac5581c3760000bdf16e850602d4855415cb881b3d226034804b437049b592c1e504b0a6b362c3eb3ee088541b145954cc85f0c80ea01d7cb1447fc69211cc0003fec0003b9cf9426a89a6253400015211db4e3083f343497d4dc0cd3065d2ed00011b5115c7862d30000055c00034b833f06a42f90cf4d6147e88070000000521000000008094c4016509e4e8a304914a4ff95c2097160600055cf372441d1ced2933a503480f6502555d55dc47dccb4000013c000130f1ff52d73919213000036700016d11020000000000b00001812b2125a3b040410000fec351400016e12fd532c0000000575000000011406d20000ad8413932e10d880c3e540003fe40002ac4000018c0003e448970eac02b0c6081c37440001ba0000000000038b518017a518f4ed54a236a40000000eed51dc0000000dae408cc371ebc42429795bd000000030c110600001d402e80004bd485a1b853783b787d723c52b553f51ab32b91de1295548347800022280000000000000014800000005b1018f505905321bc15a40e0fa200014ec385ca170000000520c00027e062100001ac3bd02a81ab84b811b914e02180003e652ff000076913
  | 44 => 0x6285e11f2c0001ae862a40fd36025cd0d145495f0278400030680004d9ca5136c41634b1d3d72d8028930d02032b54d1a4b943091c28000228d676000110e36e045b193c0002b5000042f877800000005b9441229710b85518a471890d5c44b4ea543745fa027850f000010c098d0013d500004d4166f3304d5155991d731944a82db86742184e312a2c72300010d54820ba1208c9da0454000145c6073530000501455900000003ed481a00006aa5871685000000052700003b080001c9851c24bd0455048eb127885114bb03a4452053f0a1502d0000000200400000000004cd50b732dd313000000000000000fe41d04b292b1000013346a03744d288f254f00000000bbf07e03490c108b40a40cfb33181db4314c9c00010bb2e44000000000000011835ba46b2000120944481e000000000000f662fd808c1e216b338d4491518569302bc5573c5d6ce2f78d8752147f42b40a104340997369ce0158447e11d61389221c70656b954c2ad0d0a08b509b332d4dc257963027344cc2481544322c5b500ec5811570b7100d88ab084d1bf0f78d3356c54a10d5060d137c3b338f16e62b7969827ec77f59842f552511b3224475a49b474924b4056122d6b023485a035656af5b8c46c3f1899f5b6cfce43850d3383d15a0fdcb5854091e40de87371c64d08338c13e58e40003cb061c0ee852e296899310d4000437939d2a3c16844dce121f3d50e35f92c03ebc9ba4e8ce5502d00a14150f600b4065c2a98c2d0000e2626b16831e50aa442acd634e908a801dcb500000212000000000007ca18e80001d6c00000012602878e2803649e3093951912c40f700014a72750aac131c91829f060e29b4e194740623170d66d00000004494cf20000000000156907fcb0200000000000d993d04ef2000000004344024234dc60000000000000000013001ea4000000000000000002124000000000000007bb00000000000000000159a3594000438d380373400000005ec51113ec04b880d3f944a61b454974798d734f7c000119c0000000000000000000000000000000000029241ad1dc345474352c55c502716044f9d66900010164184000150534100006fa000000000010d231516dc36ac99d266093f0a81558133c98a04154d408247dd0e747a004890363cc50303cd82fe10b8ca432013a94f30bdc580c1e916647db35385ed110000055b03ac00000000ef958d2e0000029c000059783f30000000480c0003a793b90efc00026800002828638000141d48f4c9e000123a32e07ed3ba4e5d047c000000111f210d22d0b680004594a992c4d2384ddc57a000142b00000000258a150000c403d24000000109a222c0000001395261c00017bc0001ae415c055418a01600003ab1128097d0e7370000000001f10e0c0005a383ca4660000000032133296
  | 45 => 0x30c2430317232ce13000047214c0e2c000000000000000000000053865e06cc5621c4400002b52ac3950dd60678000000016132040000000f4400001ed22407550b1510f340ca6e10f800022012e200003c00ffce3000006f40000a923350000000000000012560000aeb325822b3e8ce1a317d4b800003974931241240ce3e0000da43c20eae0a344dd2d44c5b000072a000000015680000324f853b816e03d7d4a04a04df449954e8474cf8a00007355b303c70164e4e04e4d67111824400000000000a23000022e03e8000000144b59440003a24dd7547907731f02052a0c1c2004806e41a46c5094c000000119900007fc33b16d219b8d29000000039e002e00013ba3a4903a00013380b50000110c9a33c680001a256a3024801a45553aa00014912ca8ac232acac045f8000268800030700002f9131917940000b2492e2b1800044a54781fd8b2934b487b3a840001d7800039c431b10015e44124d543438b32261029d2b8c2f114a4d9448ac4260f6c00021141d300000000ced16a311d2cb57cd1ec0ddc5ea22a553a4fa80002de0c620518d7900006390d1840c04983e30000f4532a8f5756a07d129e8dd451fc8294b811f63f696603448294000117f183cf2b4f1ce5a32683a1297d14d1e880ae39bc4ed2d8c1ab000105905894401ca06a006541123b981564f4889441b902f42b40003760a0e0a980003c6400056f0622578094e4510b1d172450d23e515b10c49cc4f6c504000087f351d124356800000015920a548b801e40000000d3d13680000000000513400000006d8387d21800003811684000000000000000002a14ae200000002cecb1800007e61748df82c5831d5a7cdd530b87360fa4aa73be940e03289db00012044b30c8931700165910c8d21912fa101158036d9549123424c02c045e44687e8120418e43512d116dd5f405b0dd9545841118ccf162a54e9845b568a0c140001a4d16f00015413b601d555349e80ae4a4a19f0f962b6545c11c0e2a092899121615d826e004c40494bb20e13295ad40a81dc86261bfc79803855c04d8c000312d498009d3f622f000010640d400014b634a000000013c423f4a372e190e0000084718302830000a7f51cc4b927d555d390c19a033cfa919d952e0b74ddc21c08750cc40000b64f9a29a00001360df21ce0a2c12740000001537000041f0000000000000000016eb4c6cfa4541400000000002d38000000000000000001b04c2f47494674c90d421d648d400016660af134c3f2c51a12192ab0034888169000000015972e78d6900005e70000a875358ffa2ff124d192141f00000000a5d663033832d255000046d8bc6000074a51443da00008b032d4b1f3dd022800000001948166018499931bc000000163c0000d3914a144943c800009200004db40000fc443f00016221
  | 46 => 0x3eb95fc1bf16bd22ec3802e1d35445d833a322845829b08bd21dc00029a50802074e091484f4c469cdad284c06754fc000161cd745b7c78f26d0db252649224f0c1d2593c0f01f4c0003db14af314000026f0d4d000135800006623b74000000102105b80000bac0000000000000000007f449e14540004e3d19d3ec8a2b0fa94250a584250edceff4c088eb48c0a9c00012244bac26b05c400000016c22b3125300010cb075c0002e2c0000b807121a9905840d0e7d4d0cb5a40712e65324a965a24e38270d33024182d3000082002242932e4c8113f7148e102c3620000f1b00a80000000cc411a4000000162a08850da0dbc4181004ab243cc00043e00e900f8a2633946544e115552c20d4a49380001b3016433ac73a388476c53f800014e0ecd37a0cfd000149254916160545042570d464355c81000010f146c8f832e712c64c99159330c0001a548b200dd3572a24e0650a0eaa41e08142e7ce6801b0e794d187da42c492c0000c3b04740002de800007911f2000132a51f0f12372817f07e800003d80003afd34700000002bc500814901c60b30388462c3d229c8452548c3a5086c6e00eed103055038242503d110d0fd4219cb304614b55042cea74cac4bb39fcc2a15a8000500841319dc25e23194fc4fa165d2fc12284f64000044559f0000e412b806424e6400000000001290f060001457005552f45847fb544cace000099500012c33614000000142f000023f09f4f1500d09e930b00e51ec957e0001184000099c249c00049f41722aa05c006c8000000061f3c740005b78000543c74c4d84000436cc9543211393b480000000936000057c3214ca3308c000421115e0000196299cc431154cf01ef55b71adc00056ac9d91381270151d27f146091d02ad2cd19001251b949fa172d26a015d67517cc356061c5fd1cc4c3c0cc00000e714f4560d1b40000f2d00002010000f4721800004718000140c0004af800050a4000580048e48b8d0b3f0459e1c2cfb01400000393d6cd4d942e72d24a91493d22f19408c40b7094200009794ea000049880000000720165c6bb56950834c10a115a9cccc1edc0544e1ca5b1728a790f4c1f02bd40004ced5ce2e340005bb961a08784be0c7c0003658000000000013208c84ef826a5660d6f5b4090200006b3000000022801310000f4636a0a420a3c3c126503073e7942c000113600000000000b92000000021b8d500ab45090eb525947f000000014e60514000000154a0ce51313d9039b0000000371d62917d86f048401c01f7894323540000000b970000a88422800054f868f2d84900000019c00014504f04df70000f342b100005b0000037380005a856150000e8f1e6d163433d4e7000000000000003e20000305c0004c7861d0f1062c266c5231ddc00013b101715c8000083d1bd0000
  | 47 => 0x56a55a10f2929d0a4c48c821129f40002208a392e3cddf0ca4a7b0420d31070426557ed20d003123e330833631f850b0064a2244003df0c350810000ed71649443000030259e889313949f430cd30b39715f6148096d00008f405e4e753d584651b88d38000068800014450000dbd1d08f980d44efe08341ef00006b859891710000000175c26d0000ad3045800048380000d5d3983708d2f000000000009150000000000000000000000000000000088d000109800000004d2d66c20cd5a1000120119a125100003c300000000510000000000044d00000000202136cd6c00008150000000103c000000138516ac55b43115d2000082d28042fc253d223000128c214419800000000000a4b29c400027408ca26a542e23b93f400014e136f00002394aea5920000000148031b8a6f533c9fd08187f8365c0090000000000107e000042000000001b6c4f235c03641eb45c5537c0005024e0301c157c0a6426f4f894032a08ee50000e6b4a3512f000147a00007134f2d12c00005d8000055328c47ec454077c1bb523456710791554ce240ac4fe33b43c90a791b119e8583072000026ed35c283544c3284c55233ce4a06d907d29146bd02c822737a54e23d9434e177c878146cb3a3cec1bb3bb8b21091cd55348d36a014167202549f05078f9c220518e04653e5469054000000c802e129e271022926ad5c827000000001599010d5b439a8a044de80004918045368453b09a11794e440005498f5b000000000000005474f6b00000002bc911c000000000000000000f70000012d1f0c0c50ca853c0f701fc34c90f43ea143500000000000ca90bcc00000006ca1c042b41bc461a45e13c64214fb62e740003910a783ac11143f880000f902a34c44e3f269d0fb36940001b5c58f3c3545f186c89b43e92c453e89fc1170f4a00014d3336400000000000000257289d50904c91674a448f84f0837c4c18f3d0548665000000000013b307388d81cd13bb4f4cb6503cc12b30c96260000000000000000016da000036a18ec00011a000006805785ba8ee14a90ff40000000000117a0000f81000000000003d600003b8597074158ec0003628000000122531ad2695a5072721587702c40000587d61d181068354803a811a8d9c52e45353bf560a0858f5225e070f535c1a74fb8da22f14b8556fd53b4d7516631a4bfa4634ab8255c23c357cf30226527c23d83b22fdc87a1b1c59a1abcde459f123c2d345f756501e34dd4e4809f8af6339828823094372b6869b3f744f61508a1f0b3d4bd231cfd630592f61a5d26438ecec919a847158e955f453168b00015be0fe15ad4280a6255880d609a40000c98e932ec096248002e948a52bf00000000000000337939031c50c631f400025f068b4940b894754ce0164c90b09b8bbb0c9452a1c748d73f80a1a
  | 48 => 0xc34e8b2f20987c0410c0000000ea80000000000000000007fa1bb8c5327b8bf2000130d3b7c33500001ba4908000036076a000011c1e4921d57847713b4d1dd397800032c4bfe2224dfc406d02c4b3d60c5150872242400000009374134000000000000007e71fb9573273c00012cc00000012954f3478e28b8840025cc3f4dd10a447001a113dc9e44ba94ca4768af849e00e218d53de2ebc25030084e601c806954a91ac2ae40db12d10751e00d8400013f902f4d2100004e23ae000032f4931341448800015d740e4225000150a25b8e4b52f91021aa49815404a6015d015344ac17a239c00058f8cce0ed1275545c1b40000859422c17400013250ab15c92d7c4761bf561b32b482e05a561e56d4a8e2c8c52221494554f44a444424e620d0024150a83fd3e1cbda1614fdf27780000db45f01630060446c8a23c4400019d4ecf022c0001c5cf9d0000cd2000000009d897e00001140afc0004fc4b003c007b855d8000339cc762c8044e364919e470cfd12f00000000001c5500000187955300002ef00000000000000000000019bc0001b00000000075c2420000295548f13140005690000591400016b0fd90000f8c30a5126185c18947d54ed23dd6593b9167d01189040770cdf1ed5243153848000010cc44c0000000069e51c84160c582c8171c0000788ba02b485693af0b83000000005813731c50000000110400013660d98d720c68cb60acc3ec3f140004e9cc705400e2902395884b515e626855a63bf0a8c3a90b6d000164c18d8000000069805dc55124d0a8a461d38a46e933c0fd40002be80001ac16423054ba24a1c20b0000fb73274322000040741040001ef95ba16c885e178cce9321000011345130000e59000023d47f4c1f30f83bc1d50000000024300000001e2c00000004a3026400000012e7000000000009cb3bdd21411f80000000f5c4ba535301e0000446529f4b84970000003119194c8094458b00001413af4000000034219745f9000100709b0000321c9301e90fb90e88f9b06f02a70000e1d02f8fc95ae964d27803a900011563aa505b0000cc9144968138b96bf2ad47c847f800008dcff7000000025d94872dc92d62aad34900009b530240003b680000000aa24c8cbe1000163813bcc0a56d80000d809805ac830600000004fed52d01ed3bd135562b11dc8e44e4800039b87aa0000c260000fd0000000000000000000000000000054c4cf826a00000000000471c9d20001579372c81254a000000011bc4ae91ea03d0000000000000000002a400004b3908f4668d2a22e8558394c000000073c000000000013ca000000031240000000cba3ce03450000000000000000000000000000363167b00013e600009e70000f4032b11080154a3549bc23126dc0000000d8337944d22bdccf90ff097250cc5d6030
  | 49 => 0xf2851d000041e922a000051f2dd169701f8d40502c415344000000000000000000449cf1009d047838d13d04efc0000000fff1b084bd176563f41cc62b075800045cd48645715543a212bb22cd1a3585162126e468d30ac4d4419150826207051b4c2e500182d1034c75d0000dcc15dd0e22558ecb3184f6f4db879c5278000509895000000005a1c0000000c974c5410a42780004170c92303c0000dd546a2e586e40ae83a739a482241a03cd3548f8900015ee0000f3302b12e4409d4f70000a3e12b476000000003ded58138cca735160f823c80414394861331040001cbc5e20d749ce000022643f51f3501c000000000008d800009195590df43b5277c00044fc00038bc00036a800041d05c433bc00000000000000b1156141b14044b7c2fd147130300005b283e000000004c509ca00002ae0000000000000000000000000e16000000055c40000000b2b45446a800012050cac0003df562500000000000000000000000013320000000424d28200009554bb965840380004d452fc5208000139c0005a000000000000000000026304b51e94000582c000000000000004ae52695571f24a54599ce91161038639b1013548438a1c6105129a90ee3878d0f4dad4a8407468e540d05f1180e47000027542b14eb2bc0000113c77408d000037991540b8c05f2870000000165a52b8b0d38940000001636580495116bcaba0000989470400039cd5c6000000010f0d9a4a14f0533901f934640000000dee000000000000005a48c60000000027592ef43f031428000003ac82ea4ec55500000000000084e0000732275c0000f847d80000d3500000002984f59188011b324159d0000fe3000101556a85d53a6c84b22b400000000005b0d3c000014c50000552177804713b800032bc00014c40440000c9b13707a3000056428c800054880001ba800000000004b5400009dc47d13100000d496a2582064b000063d031d0e60000178000027a0e680001f8c9ea1c3909633a954746506095b581df0d64f7c04a023213d52d000015d957e11382d214d800014964ca0f6900002ca3bb000032c8000054000031e00001b680ea42fd46c50ec332000030f096497f00000000f504833e4c4ce39805f8024496c038cb79053098d4088000257141c28811053faca9a30652a20000857000000052ccfc24ab51113d4c576000000055d00000000000214d5f90e500002c113fd000000028d0a4800012bc50853e956bc000583c0000cdc00036ed1d932e481722f810220ac0000000f421dd400000001fb3f5c7104b740001f343b0522c0002a6036133580004e4c0000000000152d5ef5bc801400000000b080000000afc4010e361e553ef26c80000900f9026c00000001584000000000000004845552585c8842a18a2f5638e042dacaad00001ae14cd6b
  | 50 => 0xf016e5688347c92933d43584618bd247816c92c251cd0c9d0ea25a40000000000000159b0000f920000d1d271800012dc0000a2873900006c8281c2a43aec846479569118550a5000083031e8b9a1a416ab1d9121b000000023a8c7f1a9d5e22c310915a585c234605db3f1c2fd4becbe200000001b240004474d7708100005adc00055bc000302d20605ac21400010ca421d28f2ef00001f140000000000000068c4a00363000000000013c91c20d90378cce1000000000007290000ba800000001b3949036b0fd2280c83a4dbd5e947d06270000000441ce3a409088602800003a88e7c0620e9c58390f621b54c216a4b0f23d400032a0000504558c0ed876d0000db51f504ac3a3859f00007d013a8fb452a48a40374e6d00001dd4ce80004758b42307873e3f10d014f900002754000160881e000129b1718000479c6eb0000c3d4f500002a6c000000013d57b4bed0ad81ee36fc0000000bb13bd8802158d11e1d3d01a5848000071d14927252af00010e930807891f8923b0c913454b4cd063ce85684a8d249102432e2368905000023b223cd9d293896b000000000000001a0479127941174078c1812640000bd80004174e2700001043888000000066927d824238dc03f3168000000009301340002a35637536c24f0000971092c00000007b400000000000000000001e000153400000c0091400001bc000000139a000022c124907c05a8000518d27a3bbc00a33dcec61a587832d5c0000000000000110d23fc0003bc0af3448158221940002e30000000000023340003c3c3a60000000399c00057440000000a7500000000001298530c5b3218cb9513c4b0a000000037c0d4428ccf3e14bd03c55450c128e904b3b448923ad0545337057e4560de712f03925bbcf18315819f59cc4c1024042a28a010e198449818581104688dcf4f3c9ec5b915a05a7494a3f0ccd718c0000000004800000002e0479d0000000241d5140df919f190cdb40000e7e0e58000572d1c40000000000000055083731ec151217a0fcc00016d44add6b944f06d52c9000043bc00027e4bb721105da38340003ddc9dd0000000000125f000100216d1193201091653fcf4e517874d0000000088131c496c21d0000c4239851d400001430a881a300000000000653000000042700a3000000004e000000000111fa521200109d84be400000011a100012150000000000000000000000c78bac2d1d4ce3854bf100006b50000ca74cf540800012d805d4beb000000000009a52ff420815c0c10551479934ed15331b4ef135194ef013d116000056647bcf784a954de05f43a323a152b000000033340f1437ca4d46a400035d800000008210e1c874308877b46492ae00000000000bce174430830040000168000263c00000000004e50f1c00003780000bcf22783e600
  | 51 => 0x112100013b40f3d44a42c890f4b201a84864000000000006fd31651f922709c000059b800054e4000000088c0b000002a108c949ed446053400014f8000000014f000092a41800003da0d0731e400028f541548fcf734e0c0a53c8421c21e4d3f56c89af27200421af89bf4405469052d18937e4315000000000012520000c4e00007d91cfc0004cb4a6501c45dd0000000000000059f89684db0000000083c000000000013ab34700000001510248cdd2000135b38011fb000165420a8af43814ae8252c8052d0c7c70f9493b57f480340f80002ab80e6382000042cd297528d048451c4054c815bb362114f165485b2d48e503178d022270a2142e44291d494f6004c000114c00000000004de4000000000000000003bad3f300003e2000000000008e116f4b2735e800000009520d7cb3c0b7c97741bc22400002150bec87d4000bc3304521c1b9921f00011c20c412632c8834c2f5096409f121656280305ae13ae1b34bd938406bf12510353c7c2ab51c13361eb098e1df8666000057300000000000000290cef906f4000408140c23c01f40000cf403f4ba64158a020dec00055680004dd849f34dc42b064430a00016101f04ff33a0d5c73eac25b2eb867835982600a71321096827225a8b05352d5ec3fbc0003f856b400012a700e43191cb92685a70aaa1ab0c4500001240e240000020d9b2da817650f4d251fc870251990
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x16210230d05745c4524c930d0a745c0524c930d09745c0524c930d42715c0524c930d41715c0524c930a308550560105308c9821c1644c530a9080590414c530c91645c0414c530989821c14350130991811c14350130a908050c6150130e0a544c9600c830e09544c9600c830d41325c03294430d41325c03254430d05745c4534cb20d0a745c0534cb20d09745c0534cb20d42715c0534cb20d41715c0534cb20a14815516315220c147458d5114620915831d54110620834875954110620a30855056010620a15831506150220a14815516310220a24815516210220d05745c4534c920d0a745c0534c920d09745c0534c920d42715c0534c920d41715c0534c920a308550560105208c9831c16448520aa0805904148520ca1645c04148520989831c142501209a1811c14250120aa08050861501209c181dd1324c12098984dc5324c120e0a544c9600c820e09544c9600c820d41325c03294420d41325c03254420c32765c05450710c14545cc6050710c24545c86050710c31769c35410610a15831506150210a25821506150210c0d635c86315110c19635c06315110c0d735886215110c29625c06215110a0d86151320c910a498214d600c910a4983149600c910a4a854c9600c910e0b544c9600c910e08544c9600c910c14545cc6050510c24545c86050510a3285d906050510a25829d8548c51083587150604c510c24545c8604c510a15839d85488510835871536388510835871506048510c14545cc6048510991831c141501109a1821c14150110c167558e4110110c267558a4110110991841c1314c110d10541c1314c1109c1821c1314c1109a1841c12148110d20541c121481109c1831c12148110c15731846055010c2572184605501083787553614c810c167454f614c810c267454b614c810a4980595320c810a498294d600c810a4983949600c810a4b854c9600c810a49854c9600c810e0a544c9600c810e09544c9600c810a31859916010410e126454d6010410e2264549601041083787d974150010c167654f4150010c267654b4150010c157558c4110010a158654c4110010c25755884110010e05535884110010a25865484110010e05635484110010c31655c04110010c91635c04110010d11535c04110010ca1625c04110010d21525c0411001083487551618c010c147454d618c010c2474549618c010834875516188010c147454d6188010c24745496188010c14645cf5444010c24645cb5444010836869d95444010835871935344010c24645cb5344010a14865525344010a14869515344010a14865515344010a16849915344010835871935244010c14645cf5244010a24865525244010e046454e5244010a24869515244010a24865515244010e046494d5244010e046454d5244010a26849915244010
  | 1 => 0x2d09744c83254032d41329c43254032d41325c43254032948874c96154032d0b744c96154032d08744c9615403294b874c86154032d0a744c86154032d09744c86154032e0a644c95014032e09644c95014032e41329855014032e41325855014032a498294d600cb41a4983949600cb41a4b854c9600cb41a49854c9600cb41a498294d600ca41a4983949600ca41a4b854c9600ca41a49854c9600ca418a5821c161d0c41a198018d4354841895831c161d0841929801c95350841949801c9534c841949801cd524c841a4980d95320c8418a5829d95350441d05535c85350441d11535c05350441895839d95250441d05735485250441d21525c0525044183686dd53250441931801d53250441d05754c83250441d81325c03250441c15759cc6050441c15755cc6050441c25759c86050441c85739c86050441c25755c86050441c86735c86050441c85735c86050441895831d941940418a5821d94194041991831c141940419a1821c14194041991831c141540419a1821c14154041930805c74354041930805c74254041919831c14154041929821c14154041951831c14154041961821c14154041915831c14154041925821c14154041b11831c14154041b21821c14154041932861c14154041c32861c14154041d12831c14154041931831c14154041d11831c14154041911831c14154041d22821c14154041931821c14154041d21821c14154041921821c14154041e0a544c9600cb31e09544c9600cb31925821c15410631a30805516010631925821c154105318d1801cd6210531a30805516010531b0582151434c431b1180151434c431d0574548324c431d41525c0324c431e0a544c9600cb21e09544c9600cb21915831c15410621a30805516010621915831c154105218e1801c96310521930805d54310521a30805516010521b05831514248421b21801514248421d057454c3248421d41535c03248421a498214d600c940a4983149600c940a4a854c9600c940d41325c032d4540c45635c86314540c51635c06314540925821c14314540c45735886214540c61625c06214540915831c14214540c45764c83214540d41325c03214540a3285d846050540a2582990514c540a15839905148540a1681d91534c840a2681d91524c840a498294d600c840a4983949600c840a4b854c9600c840a49854c9600c840d41325c03294440d41325c03254440a31859856010440e11539856010440e21529856010440e05539486150040e06535486150040e05535486150040c147654e5150040c247654a5150040c147694d5150040c147654d5150040c24769495150040c24765495150040a24815516215230c24745895114630925821d54110630834875954110630a30855056010630a25821506150230a14815516310230a248155
  | 2 => 0x84db0485d0240000112434790006b06d0f390b74e14710d39070003a0f804d372a4140fd0c4d87227cac47103274fa46c8c424d23580031400000d8001324500020d4d364913a9253200111d211fc970003d000a335c4f2fc623c09026d3b00007000714a4df01541000003f03e17cb14d4f22d9150bc9c0003905c00310482791f03ca11b0001791138c6848cd54b1493cd102f4f40b1282e8d434c813000052800370534785a1807700088250150000e08cf61f40d0b4c93dccb00c921e84c154590a44d20016000242f0003f4003b41f1b40002899000ff460b0475450000633c0004400418653b0c30006f374ae000201988a12d3023c0241d4c298a83bcb8400002d41d4a8aa42d2f408e74e9041403b0a8a5498c70e8e64904429c8b4587b0004204018210643945c020c129119000953e4fb19d200686a000ad000984f89a22496319052e4003a47e100c22088700000078000000052c0050c22000be45ceb0c84a4ac561393c084cd1d48e2cc28000851c074099480e08d15cab0c10800073330000313d184000f0492bc00340a00c40409c520dc19001014fc25000000000002c76510003282e150bb0d87c00000104002c8b43c4000006e01010180004098140e0c0081404000080c00000000016010202804110183c18260001c580100034184b050100217000b006050802000060000800070191000000101c00000182c0411000080c060885c0a02010100403000281013000800204008081a00028041a200b82c0000090088602010000002058240001945859c7644c83290d859d3614c832e09544c960d4432b4180d513254432d05435c84354432d05735084254432d05744c83254432e05544c961d4032e05644c951d4032f01544c95194032b0a841c13254032b09841c13254032b42811c13254032b41811c13254032b4281d513254032b4181d513254032d0b75551325403294a871513254032b42811513254032b41811513254032d0a744cb5154032d09744cb5154032f02544ca5154032f01544ca5154032b43854c95154032f02544c95154032f01544c9515403294b874c85154032d0a744c85154032d09744c85154032d09435c84354032d09735084254032b42819093254032b41819093254032b428190d3254032b418190d3254032b0b845d93254032b08845d93254032b43815d93254032b40815d93254032b0a841d93254032b09841d93254032b42811d93254032b41811d93254032b4281dd13254032b4181dd13254032b42819d13254032b41819d13254032d09741d13254032948875913254032b43815913254032b4081591325403294a871913254032b42811913254032b41811913254032b0a84dc53254032b0984dc53254032b0a849c53254032b09849c53254032d41711c53254032d0a744c8325403
  | 3 => 0xacfe160464d146339401b85b438860cc3524c340012249c00001424b4a2468da380000013100133344453b8691e10a0006314513378e23d52e3
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xe2401c500000000001500000401109440000a00f0000080004c02c301200c046356060040021831219220171d0d5010622326402e3a12a020e4060e821c14154041c8141b0438282a808390183608705055010644324402a8b008318c88648805516010531908c9900aa2c020c432119320154580414864432442a82b0083184a064880590414c530940c9100a18c2a026121193215415804188250326402c820a42904a064c805086150120888cc0a8382629822190054608704c530442243302a0e090a4088640151831c12148110a08cb2a6b808220021c015358970104400428432ca92e0208800870058d525c04110010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1870
  | 5 => 10236
  | 4 => 5875
  | 3 => 334
  | 2 => 23
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
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (718+((h/13+packedAt gbK7 (640+(h % 13)*6) 6) % 49)*7) 7
  | 6 => packedAt gbK6 (57966+((h/623+packedAt gbK6 (50490+(h % 623)*12) 12) % 2469)*12) 12
  | 5 => packedAt gbK5 (436736+((h/3412+packedAt gbK5 (388968+(h % 3412)*14) 14) % 12284)*15) 15
  | 4 => packedAt gbK4 (313329+((h/1958+packedAt gbK4 (287875+(h % 1958)*13) 13) % 7756)*14) 14
  | 3 => packedAt gbK3 (21039+((h/111+packedAt gbK3 (20040+(h % 111)*9) 9) % 401)*10) 10
  | 2 => packedAt gbK2 (1675+((h/7+packedAt gbK2 (1633+(h % 7)*6) 6) % 46)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xf1fe3fffc3e3fffe0c71f8fff1c1fffe08f0ff
  | 1 => 0xfe1fc3e3fc03c78ff07e3f1c3e01c71e774c93
  | 2 => 0x1ffc03fffc07f1ff803fe03ffe07e1878f1c
  | 3 => 0xffe00003fffff801ffffc0003ffff801f80fe0
  | 4 => 0xfffffffc00000001ffffffffc0000001fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10020000400400000000402400404100001025
  | 1 => 0x24c498c488c98b1070321908b20c925c334c92
  | 2 => 0xd0809491140940294802a41149404c4858518
  | 3 => 0x4041a292228201252954800229293009580ac0
  | 4 => 0x899133003b132649ce69349380302091eee000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_36324
namespace PEqualNP.Outside.L_meta_36324
open PEqualNP.Outside.L_meta_36324.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 23 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_128 : Interval gbAtlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_160 : Interval gbAtlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_256 : Interval gbAtlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_288 : Interval gbAtlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_320 : Interval gbAtlas 3 320 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 334 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128))) (concat (concat bgb_3_160 (concat bgb_3_192 bgb_3_224)) (concat bgb_3_256 (concat bgb_3_288 bgb_3_320))))
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
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_320 : Interval gbAtlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_352 : Interval gbAtlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_416 : Interval gbAtlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_448 : Interval gbAtlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_704 : Interval gbAtlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_736 : Interval gbAtlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_800 : Interval gbAtlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_832 : Interval gbAtlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_896 : Interval gbAtlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_928 : Interval gbAtlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_992 : Interval gbAtlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1024 : Interval gbAtlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1088 : Interval gbAtlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1120 : Interval gbAtlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1184 : Interval gbAtlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1216 : Interval gbAtlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1280 : Interval gbAtlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1312 : Interval gbAtlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1376 : Interval gbAtlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1408 : Interval gbAtlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1472 : Interval gbAtlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1504 : Interval gbAtlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1568 : Interval gbAtlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1600 : Interval gbAtlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1664 : Interval gbAtlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1696 : Interval gbAtlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1760 : Interval gbAtlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1792 : Interval gbAtlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1856 : Interval gbAtlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1888 : Interval gbAtlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1952 : Interval gbAtlas 4 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1984 : Interval gbAtlas 4 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2048 : Interval gbAtlas 4 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2080 : Interval gbAtlas 4 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2144 : Interval gbAtlas 4 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2176 : Interval gbAtlas 4 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2240 : Interval gbAtlas 4 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2272 : Interval gbAtlas 4 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2336 : Interval gbAtlas 4 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2368 : Interval gbAtlas 4 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2432 : Interval gbAtlas 4 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2464 : Interval gbAtlas 4 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2528 : Interval gbAtlas 4 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2560 : Interval gbAtlas 4 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2624 : Interval gbAtlas 4 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2656 : Interval gbAtlas 4 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2720 : Interval gbAtlas 4 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2752 : Interval gbAtlas 4 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2816 : Interval gbAtlas 4 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2848 : Interval gbAtlas 4 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2912 : Interval gbAtlas 4 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2944 : Interval gbAtlas 4 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3008 : Interval gbAtlas 4 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3040 : Interval gbAtlas 4 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3104 : Interval gbAtlas 4 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3136 : Interval gbAtlas 4 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3168 : Interval gbAtlas 4 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3200 : Interval gbAtlas 4 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3232 : Interval gbAtlas 4 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3264 : Interval gbAtlas 4 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3296 : Interval gbAtlas 4 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3328 : Interval gbAtlas 4 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3360 : Interval gbAtlas 4 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3392 : Interval gbAtlas 4 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3424 : Interval gbAtlas 4 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3456 : Interval gbAtlas 4 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3488 : Interval gbAtlas 4 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3520 : Interval gbAtlas 4 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3552 : Interval gbAtlas 4 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3584 : Interval gbAtlas 4 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3616 : Interval gbAtlas 4 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3648 : Interval gbAtlas 4 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3680 : Interval gbAtlas 4 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3712 : Interval gbAtlas 4 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3744 : Interval gbAtlas 4 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3776 : Interval gbAtlas 4 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3808 : Interval gbAtlas 4 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3840 : Interval gbAtlas 4 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3872 : Interval gbAtlas 4 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3904 : Interval gbAtlas 4 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3936 : Interval gbAtlas 4 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3968 : Interval gbAtlas 4 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4000 : Interval gbAtlas 4 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4032 : Interval gbAtlas 4 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4064 : Interval gbAtlas 4 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4096 : Interval gbAtlas 4 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4128 : Interval gbAtlas 4 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4160 : Interval gbAtlas 4 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4192 : Interval gbAtlas 4 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4224 : Interval gbAtlas 4 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4256 : Interval gbAtlas 4 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4288 : Interval gbAtlas 4 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4320 : Interval gbAtlas 4 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4352 : Interval gbAtlas 4 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4384 : Interval gbAtlas 4 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4416 : Interval gbAtlas 4 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4448 : Interval gbAtlas 4 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4480 : Interval gbAtlas 4 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4512 : Interval gbAtlas 4 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4544 : Interval gbAtlas 4 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4576 : Interval gbAtlas 4 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4608 : Interval gbAtlas 4 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4640 : Interval gbAtlas 4 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4672 : Interval gbAtlas 4 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4704 : Interval gbAtlas 4 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4736 : Interval gbAtlas 4 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4768 : Interval gbAtlas 4 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4800 : Interval gbAtlas 4 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4832 : Interval gbAtlas 4 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4864 : Interval gbAtlas 4 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4896 : Interval gbAtlas 4 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4928 : Interval gbAtlas 4 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4960 : Interval gbAtlas 4 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4992 : Interval gbAtlas 4 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5024 : Interval gbAtlas 4 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5056 : Interval gbAtlas 4 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5088 : Interval gbAtlas 4 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5120 : Interval gbAtlas 4 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5152 : Interval gbAtlas 4 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5184 : Interval gbAtlas 4 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5216 : Interval gbAtlas 4 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5248 : Interval gbAtlas 4 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5280 : Interval gbAtlas 4 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5312 : Interval gbAtlas 4 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5344 : Interval gbAtlas 4 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5376 : Interval gbAtlas 4 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5408 : Interval gbAtlas 4 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5440 : Interval gbAtlas 4 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5472 : Interval gbAtlas 4 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5504 : Interval gbAtlas 4 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5536 : Interval gbAtlas 4 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5568 : Interval gbAtlas 4 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5600 : Interval gbAtlas 4 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5632 : Interval gbAtlas 4 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5664 : Interval gbAtlas 4 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5696 : Interval gbAtlas 4 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5728 : Interval gbAtlas 4 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5760 : Interval gbAtlas 4 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5792 : Interval gbAtlas 4 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5824 : Interval gbAtlas 4 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5856 : Interval gbAtlas 4 5856 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 5875 := (concat (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 (concat bgb_4_192 bgb_4_224)) (concat bgb_4_256 (concat bgb_4_288 bgb_4_320)))) (concat (concat (concat bgb_4_352 (concat bgb_4_384 bgb_4_416)) (concat bgb_4_448 (concat bgb_4_480 bgb_4_512))) (concat (concat bgb_4_544 (concat bgb_4_576 bgb_4_608)) (concat bgb_4_640 (concat bgb_4_672 bgb_4_704))))) (concat (concat (concat (concat bgb_4_736 bgb_4_768) (concat bgb_4_800 (concat bgb_4_832 bgb_4_864))) (concat (concat bgb_4_896 (concat bgb_4_928 bgb_4_960)) (concat bgb_4_992 (concat bgb_4_1024 bgb_4_1056)))) (concat (concat (concat bgb_4_1088 (concat bgb_4_1120 bgb_4_1152)) (concat bgb_4_1184 (concat bgb_4_1216 bgb_4_1248))) (concat (concat bgb_4_1280 (concat bgb_4_1312 bgb_4_1344)) (concat bgb_4_1376 (concat bgb_4_1408 bgb_4_1440)))))) (concat (concat (concat (concat (concat bgb_4_1472 bgb_4_1504) (concat bgb_4_1536 (concat bgb_4_1568 bgb_4_1600))) (concat (concat bgb_4_1632 (concat bgb_4_1664 bgb_4_1696)) (concat bgb_4_1728 (concat bgb_4_1760 bgb_4_1792)))) (concat (concat (concat bgb_4_1824 (concat bgb_4_1856 bgb_4_1888)) (concat bgb_4_1920 (concat bgb_4_1952 bgb_4_1984))) (concat (concat bgb_4_2016 (concat bgb_4_2048 bgb_4_2080)) (concat bgb_4_2112 (concat bgb_4_2144 bgb_4_2176))))) (concat (concat (concat (concat bgb_4_2208 bgb_4_2240) (concat bgb_4_2272 (concat bgb_4_2304 bgb_4_2336))) (concat (concat bgb_4_2368 (concat bgb_4_2400 bgb_4_2432)) (concat bgb_4_2464 (concat bgb_4_2496 bgb_4_2528)))) (concat (concat (concat bgb_4_2560 (concat bgb_4_2592 bgb_4_2624)) (concat bgb_4_2656 (concat bgb_4_2688 bgb_4_2720))) (concat (concat bgb_4_2752 (concat bgb_4_2784 bgb_4_2816)) (concat bgb_4_2848 (concat bgb_4_2880 bgb_4_2912))))))) (concat (concat (concat (concat (concat (concat bgb_4_2944 bgb_4_2976) (concat bgb_4_3008 (concat bgb_4_3040 bgb_4_3072))) (concat (concat bgb_4_3104 (concat bgb_4_3136 bgb_4_3168)) (concat bgb_4_3200 (concat bgb_4_3232 bgb_4_3264)))) (concat (concat (concat bgb_4_3296 (concat bgb_4_3328 bgb_4_3360)) (concat bgb_4_3392 (concat bgb_4_3424 bgb_4_3456))) (concat (concat bgb_4_3488 (concat bgb_4_3520 bgb_4_3552)) (concat bgb_4_3584 (concat bgb_4_3616 bgb_4_3648))))) (concat (concat (concat (concat bgb_4_3680 bgb_4_3712) (concat bgb_4_3744 (concat bgb_4_3776 bgb_4_3808))) (concat (concat bgb_4_3840 (concat bgb_4_3872 bgb_4_3904)) (concat bgb_4_3936 (concat bgb_4_3968 bgb_4_4000)))) (concat (concat (concat bgb_4_4032 (concat bgb_4_4064 bgb_4_4096)) (concat bgb_4_4128 (concat bgb_4_4160 bgb_4_4192))) (concat (concat bgb_4_4224 (concat bgb_4_4256 bgb_4_4288)) (concat bgb_4_4320 (concat bgb_4_4352 bgb_4_4384)))))) (concat (concat (concat (concat (concat bgb_4_4416 bgb_4_4448) (concat bgb_4_4480 (concat bgb_4_4512 bgb_4_4544))) (concat (concat bgb_4_4576 (concat bgb_4_4608 bgb_4_4640)) (concat bgb_4_4672 (concat bgb_4_4704 bgb_4_4736)))) (concat (concat (concat bgb_4_4768 (concat bgb_4_4800 bgb_4_4832)) (concat bgb_4_4864 (concat bgb_4_4896 bgb_4_4928))) (concat (concat bgb_4_4960 (concat bgb_4_4992 bgb_4_5024)) (concat bgb_4_5056 (concat bgb_4_5088 bgb_4_5120))))) (concat (concat (concat (concat bgb_4_5152 bgb_4_5184) (concat bgb_4_5216 (concat bgb_4_5248 bgb_4_5280))) (concat (concat bgb_4_5312 (concat bgb_4_5344 bgb_4_5376)) (concat bgb_4_5408 (concat bgb_4_5440 bgb_4_5472)))) (concat (concat (concat bgb_4_5504 (concat bgb_4_5536 bgb_4_5568)) (concat bgb_4_5600 (concat bgb_4_5632 bgb_4_5664))) (concat (concat bgb_4_5696 (concat bgb_4_5728 bgb_4_5760)) (concat bgb_4_5792 (concat bgb_4_5824 bgb_4_5856))))))))
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
theorem bgb_5_3584 : Interval gbAtlas 5 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3616 : Interval gbAtlas 5 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3680 : Interval gbAtlas 5 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3712 : Interval gbAtlas 5 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3776 : Interval gbAtlas 5 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3808 : Interval gbAtlas 5 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3872 : Interval gbAtlas 5 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3904 : Interval gbAtlas 5 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3968 : Interval gbAtlas 5 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4000 : Interval gbAtlas 5 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4064 : Interval gbAtlas 5 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4096 : Interval gbAtlas 5 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4160 : Interval gbAtlas 5 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4192 : Interval gbAtlas 5 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4256 : Interval gbAtlas 5 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4288 : Interval gbAtlas 5 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4352 : Interval gbAtlas 5 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4384 : Interval gbAtlas 5 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4448 : Interval gbAtlas 5 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4480 : Interval gbAtlas 5 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4544 : Interval gbAtlas 5 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4576 : Interval gbAtlas 5 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4640 : Interval gbAtlas 5 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4672 : Interval gbAtlas 5 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4736 : Interval gbAtlas 5 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4768 : Interval gbAtlas 5 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4832 : Interval gbAtlas 5 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4864 : Interval gbAtlas 5 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4928 : Interval gbAtlas 5 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4960 : Interval gbAtlas 5 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5024 : Interval gbAtlas 5 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5056 : Interval gbAtlas 5 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5120 : Interval gbAtlas 5 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5152 : Interval gbAtlas 5 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5216 : Interval gbAtlas 5 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5248 : Interval gbAtlas 5 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5312 : Interval gbAtlas 5 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5344 : Interval gbAtlas 5 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5408 : Interval gbAtlas 5 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5440 : Interval gbAtlas 5 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5504 : Interval gbAtlas 5 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5536 : Interval gbAtlas 5 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5600 : Interval gbAtlas 5 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5632 : Interval gbAtlas 5 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5696 : Interval gbAtlas 5 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5728 : Interval gbAtlas 5 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5792 : Interval gbAtlas 5 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5824 : Interval gbAtlas 5 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5888 : Interval gbAtlas 5 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5920 : Interval gbAtlas 5 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5984 : Interval gbAtlas 5 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6016 : Interval gbAtlas 5 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6080 : Interval gbAtlas 5 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6112 : Interval gbAtlas 5 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6144 : Interval gbAtlas 5 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6176 : Interval gbAtlas 5 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6208 : Interval gbAtlas 5 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6240 : Interval gbAtlas 5 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6272 : Interval gbAtlas 5 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6304 : Interval gbAtlas 5 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6336 : Interval gbAtlas 5 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6368 : Interval gbAtlas 5 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6400 : Interval gbAtlas 5 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6432 : Interval gbAtlas 5 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6464 : Interval gbAtlas 5 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6496 : Interval gbAtlas 5 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6528 : Interval gbAtlas 5 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6560 : Interval gbAtlas 5 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6592 : Interval gbAtlas 5 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6624 : Interval gbAtlas 5 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6656 : Interval gbAtlas 5 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6688 : Interval gbAtlas 5 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6720 : Interval gbAtlas 5 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6752 : Interval gbAtlas 5 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6784 : Interval gbAtlas 5 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6816 : Interval gbAtlas 5 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6848 : Interval gbAtlas 5 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6880 : Interval gbAtlas 5 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6912 : Interval gbAtlas 5 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6944 : Interval gbAtlas 5 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6976 : Interval gbAtlas 5 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7008 : Interval gbAtlas 5 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7040 : Interval gbAtlas 5 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7072 : Interval gbAtlas 5 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7104 : Interval gbAtlas 5 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7136 : Interval gbAtlas 5 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7168 : Interval gbAtlas 5 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7200 : Interval gbAtlas 5 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7232 : Interval gbAtlas 5 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7264 : Interval gbAtlas 5 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7296 : Interval gbAtlas 5 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7328 : Interval gbAtlas 5 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7360 : Interval gbAtlas 5 7360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7392 : Interval gbAtlas 5 7392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7424 : Interval gbAtlas 5 7424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7456 : Interval gbAtlas 5 7456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7488 : Interval gbAtlas 5 7488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7520 : Interval gbAtlas 5 7520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7552 : Interval gbAtlas 5 7552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7584 : Interval gbAtlas 5 7584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7616 : Interval gbAtlas 5 7616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7648 : Interval gbAtlas 5 7648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7680 : Interval gbAtlas 5 7680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7712 : Interval gbAtlas 5 7712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7744 : Interval gbAtlas 5 7744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7776 : Interval gbAtlas 5 7776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7808 : Interval gbAtlas 5 7808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7840 : Interval gbAtlas 5 7840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7872 : Interval gbAtlas 5 7872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7904 : Interval gbAtlas 5 7904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7936 : Interval gbAtlas 5 7936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7968 : Interval gbAtlas 5 7968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8000 : Interval gbAtlas 5 8000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8032 : Interval gbAtlas 5 8032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8064 : Interval gbAtlas 5 8064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8096 : Interval gbAtlas 5 8096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8128 : Interval gbAtlas 5 8128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8160 : Interval gbAtlas 5 8160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8192 : Interval gbAtlas 5 8192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8224 : Interval gbAtlas 5 8224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8256 : Interval gbAtlas 5 8256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8288 : Interval gbAtlas 5 8288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8320 : Interval gbAtlas 5 8320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8352 : Interval gbAtlas 5 8352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8384 : Interval gbAtlas 5 8384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8416 : Interval gbAtlas 5 8416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8448 : Interval gbAtlas 5 8448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8480 : Interval gbAtlas 5 8480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8512 : Interval gbAtlas 5 8512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8544 : Interval gbAtlas 5 8544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8576 : Interval gbAtlas 5 8576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8608 : Interval gbAtlas 5 8608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8640 : Interval gbAtlas 5 8640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8672 : Interval gbAtlas 5 8672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8704 : Interval gbAtlas 5 8704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8736 : Interval gbAtlas 5 8736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8768 : Interval gbAtlas 5 8768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8800 : Interval gbAtlas 5 8800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8832 : Interval gbAtlas 5 8832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8864 : Interval gbAtlas 5 8864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8896 : Interval gbAtlas 5 8896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8928 : Interval gbAtlas 5 8928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8960 : Interval gbAtlas 5 8960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8992 : Interval gbAtlas 5 8992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9024 : Interval gbAtlas 5 9024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9056 : Interval gbAtlas 5 9056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9088 : Interval gbAtlas 5 9088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9120 : Interval gbAtlas 5 9120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9152 : Interval gbAtlas 5 9152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9184 : Interval gbAtlas 5 9184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9216 : Interval gbAtlas 5 9216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9248 : Interval gbAtlas 5 9248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9280 : Interval gbAtlas 5 9280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9312 : Interval gbAtlas 5 9312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9344 : Interval gbAtlas 5 9344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9376 : Interval gbAtlas 5 9376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9408 : Interval gbAtlas 5 9408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9440 : Interval gbAtlas 5 9440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9472 : Interval gbAtlas 5 9472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9504 : Interval gbAtlas 5 9504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9536 : Interval gbAtlas 5 9536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9568 : Interval gbAtlas 5 9568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9600 : Interval gbAtlas 5 9600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9632 : Interval gbAtlas 5 9632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9664 : Interval gbAtlas 5 9664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9696 : Interval gbAtlas 5 9696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9728 : Interval gbAtlas 5 9728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9760 : Interval gbAtlas 5 9760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9792 : Interval gbAtlas 5 9792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9824 : Interval gbAtlas 5 9824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9856 : Interval gbAtlas 5 9856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9888 : Interval gbAtlas 5 9888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9920 : Interval gbAtlas 5 9920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9952 : Interval gbAtlas 5 9952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9984 : Interval gbAtlas 5 9984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10016 : Interval gbAtlas 5 10016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10048 : Interval gbAtlas 5 10048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10080 : Interval gbAtlas 5 10080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10112 : Interval gbAtlas 5 10112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10144 : Interval gbAtlas 5 10144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10176 : Interval gbAtlas 5 10176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10208 : Interval gbAtlas 5 10208 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 10236 := (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)))))) (concat (concat (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888))))) (concat (concat (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 bgb_5_2432) (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528))))))) (concat (concat (concat (concat (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688))) (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)))) (concat (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))) (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168))))) (concat (concat (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 (concat bgb_5_3296 bgb_5_3328))) (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 (concat bgb_5_3456 bgb_5_3488)))) (concat (concat (concat bgb_5_3520 bgb_5_3552) (concat bgb_5_3584 (concat bgb_5_3616 bgb_5_3648))) (concat (concat bgb_5_3680 bgb_5_3712) (concat bgb_5_3744 (concat bgb_5_3776 bgb_5_3808)))))) (concat (concat (concat (concat (concat bgb_5_3840 bgb_5_3872) (concat bgb_5_3904 (concat bgb_5_3936 bgb_5_3968))) (concat (concat bgb_5_4000 bgb_5_4032) (concat bgb_5_4064 (concat bgb_5_4096 bgb_5_4128)))) (concat (concat (concat bgb_5_4160 bgb_5_4192) (concat bgb_5_4224 (concat bgb_5_4256 bgb_5_4288))) (concat (concat bgb_5_4320 bgb_5_4352) (concat bgb_5_4384 (concat bgb_5_4416 bgb_5_4448))))) (concat (concat (concat (concat bgb_5_4480 bgb_5_4512) (concat bgb_5_4544 (concat bgb_5_4576 bgb_5_4608))) (concat (concat bgb_5_4640 bgb_5_4672) (concat bgb_5_4704 (concat bgb_5_4736 bgb_5_4768)))) (concat (concat (concat bgb_5_4800 bgb_5_4832) (concat bgb_5_4864 (concat bgb_5_4896 bgb_5_4928))) (concat (concat bgb_5_4960 bgb_5_4992) (concat bgb_5_5024 (concat bgb_5_5056 bgb_5_5088)))))))) (concat (concat (concat (concat (concat (concat (concat bgb_5_5120 bgb_5_5152) (concat bgb_5_5184 (concat bgb_5_5216 bgb_5_5248))) (concat (concat bgb_5_5280 bgb_5_5312) (concat bgb_5_5344 (concat bgb_5_5376 bgb_5_5408)))) (concat (concat (concat bgb_5_5440 bgb_5_5472) (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568))) (concat (concat bgb_5_5600 bgb_5_5632) (concat bgb_5_5664 (concat bgb_5_5696 bgb_5_5728))))) (concat (concat (concat (concat bgb_5_5760 bgb_5_5792) (concat bgb_5_5824 (concat bgb_5_5856 bgb_5_5888))) (concat (concat bgb_5_5920 bgb_5_5952) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048)))) (concat (concat (concat bgb_5_6080 bgb_5_6112) (concat bgb_5_6144 (concat bgb_5_6176 bgb_5_6208))) (concat (concat bgb_5_6240 bgb_5_6272) (concat bgb_5_6304 (concat bgb_5_6336 bgb_5_6368)))))) (concat (concat (concat (concat (concat bgb_5_6400 bgb_5_6432) (concat bgb_5_6464 (concat bgb_5_6496 bgb_5_6528))) (concat (concat bgb_5_6560 bgb_5_6592) (concat bgb_5_6624 (concat bgb_5_6656 bgb_5_6688)))) (concat (concat (concat bgb_5_6720 bgb_5_6752) (concat bgb_5_6784 (concat bgb_5_6816 bgb_5_6848))) (concat (concat bgb_5_6880 bgb_5_6912) (concat bgb_5_6944 (concat bgb_5_6976 bgb_5_7008))))) (concat (concat (concat (concat bgb_5_7040 bgb_5_7072) (concat bgb_5_7104 (concat bgb_5_7136 bgb_5_7168))) (concat (concat bgb_5_7200 bgb_5_7232) (concat bgb_5_7264 (concat bgb_5_7296 bgb_5_7328)))) (concat (concat (concat bgb_5_7360 bgb_5_7392) (concat bgb_5_7424 (concat bgb_5_7456 bgb_5_7488))) (concat (concat bgb_5_7520 bgb_5_7552) (concat bgb_5_7584 (concat bgb_5_7616 bgb_5_7648))))))) (concat (concat (concat (concat (concat (concat bgb_5_7680 bgb_5_7712) (concat bgb_5_7744 (concat bgb_5_7776 bgb_5_7808))) (concat (concat bgb_5_7840 bgb_5_7872) (concat bgb_5_7904 (concat bgb_5_7936 bgb_5_7968)))) (concat (concat (concat bgb_5_8000 bgb_5_8032) (concat bgb_5_8064 (concat bgb_5_8096 bgb_5_8128))) (concat (concat bgb_5_8160 bgb_5_8192) (concat bgb_5_8224 (concat bgb_5_8256 bgb_5_8288))))) (concat (concat (concat (concat bgb_5_8320 bgb_5_8352) (concat bgb_5_8384 (concat bgb_5_8416 bgb_5_8448))) (concat (concat bgb_5_8480 bgb_5_8512) (concat bgb_5_8544 (concat bgb_5_8576 bgb_5_8608)))) (concat (concat (concat bgb_5_8640 bgb_5_8672) (concat bgb_5_8704 (concat bgb_5_8736 bgb_5_8768))) (concat (concat bgb_5_8800 bgb_5_8832) (concat bgb_5_8864 (concat bgb_5_8896 bgb_5_8928)))))) (concat (concat (concat (concat (concat bgb_5_8960 bgb_5_8992) (concat bgb_5_9024 (concat bgb_5_9056 bgb_5_9088))) (concat (concat bgb_5_9120 bgb_5_9152) (concat bgb_5_9184 (concat bgb_5_9216 bgb_5_9248)))) (concat (concat (concat bgb_5_9280 bgb_5_9312) (concat bgb_5_9344 (concat bgb_5_9376 bgb_5_9408))) (concat (concat bgb_5_9440 bgb_5_9472) (concat bgb_5_9504 (concat bgb_5_9536 bgb_5_9568))))) (concat (concat (concat (concat bgb_5_9600 bgb_5_9632) (concat bgb_5_9664 (concat bgb_5_9696 bgb_5_9728))) (concat (concat bgb_5_9760 bgb_5_9792) (concat bgb_5_9824 (concat bgb_5_9856 bgb_5_9888)))) (concat (concat (concat bgb_5_9920 bgb_5_9952) (concat bgb_5_9984 (concat bgb_5_10016 bgb_5_10048))) (concat (concat bgb_5_10080 bgb_5_10112) (concat bgb_5_10144 (concat bgb_5_10176 bgb_5_10208)))))))))
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
theorem bgb_6_1856 : Interval gbAtlas 6 1856 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1870 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)) (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)))) (concat (concat (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 bgb_6_1600))) (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 40 := (concat bgb_7_0 bgb_7_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfeeefeecfeeafaa8feeefeecfeeafaa8feeefeecfeeafaa8feeefeecfeeafaa8feeefeecfeeafaa8feeefeecfeeafaa8feeefeecfeeafaa8feeefeecfeeafaa8
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,2,34)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,2,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36324.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,5]⟩,⟨.and,[1,5]⟩,⟨.and,[1,4]⟩,⟨.and,[2,3]⟩,⟨.or,[0,8]⟩,⟨.or,[9,10]⟩,⟨.and,[6,11]⟩,⟨.or,[7,11]⟩,⟨.or,[2,12]⟩,⟨.or,[3,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36324

open PEqualNP.Outside.L_meta_36324 in
theorem PEqualNP.Outside.L_meta_36324 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
