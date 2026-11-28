import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40045.Model
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


end PEqualNP.Outside.L_meta_40045.Model

namespace PEqualNP.Outside.L_meta_40045
open PEqualNP.Outside.L_meta_40045.Model
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

end PEqualNP.Outside.L_meta_40045

namespace PEqualNP.Outside.L_meta_40045
open PEqualNP.Outside.L_meta_40045.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xa417c53883fc87997fd0b21ffa902175510c3faa4887f50721fea0061fd438c7fe21087f08720fe20e81fc41887faa3a1ff14321ff10c61bf41907fe80907fd0520fe216637f53087fe60187b90842fea1c41fc42503fc82887fd4242bea9e43fd50d0bfa87197f90c20be28285ff42cc7fa80887f0c310bfaa265fd5150bf8a9105f14d20bf2a083ed4210bfc62107f90840ff19041fc42907f887907dcc631ff98843fc53903f86418ff10b30ff29483fe324c3f8a2987f15130fe29063fc528c7eea2a17d14542ffa8687df310c7fc40107f88640ff18a61fd21903fa42907f4c830ff10a41ff42cc3fa84207f14042fe28063ff21086fca8207fd4f42bf29c437e51087fa61107f94342b6a9061fe50c87fc82a0ff4c910fe28e817d52887fea5885f94e42bf2a2637f540c2fca6207f14b10f7a1285fd218c2fea818df15121beaa441ff408c2f8a4887f94d10fea9661fc50507f882207f14e20fe98863fc424cbf8a710ff14632bfa8a61fe54086fea090dfd4930ffaa0217f53502fea0a1ff90d43fe28083ff424cafaa998ff94742ff20843ef4290bfc86987fcc810ffa0c637c51503fea9087f15331ff20081fd32507fc63a07f08540bfa9221ff5350bf8a7a07f90942ff19683fc43cc7f8a021ff54041ba28a85fc43503fe65087f0c720ffa0c41fe53c87fc65a05f94620ff18a437d52d0ffea690ff08730fea9a837e51d0ff8a4185f94910dea00817e53d02faa890ff8c921bfaa641fc40483fa8420ff8ca21ff18c43fe42106f8a2a1ff15210ff88221fc510caf8a7905fd5121fea8085fe52c42f8a4087f48620bba8a857d5490bf8a910ff95031be2a021fd30043fe81107f10b10be2a665ff53c82fca1207f10e41ff10c41fe53d07fa6410dd14532ffa1621fe51d03faa690774c030ffa1865fc21c43fe43906fd0842fea1821fe53106fca5085f14132ff21e81fe510cbfaa9105f54d20fe20461fc43cc3f8a0a1df55032fea0e217d51c83f8a5a1ff54931fe19263fc31c87fea9187f14243bea9c217f5350bf886997f14941ffa9a41ff310c7fa84907f50a40ff21481fe43887fca910ff90920fe10021fe43487fea0a16fd0e43fa18843ff53842fea6107d8c710bf2a0617f53483f885997bc8020ff21461fc5190efea6a0ff94730fea8663ee520c3f841087f4c210ff28c417e5210bfa87087f54443fe29281fc41483f8a5187f54843fe20441fd428c3faa6885f94241ff28443ff53903fe87905f94431ff19081fc41883fc62207fd4041ff99061fc41903d84290774c832fe294837e5010ffca7a15f54732fe21e85fc52107fe86995fd4f21ff296877e531077a87a07d4c510ff214657e51907fca2185f54041ffa88857d5110ffa85107f0c540ff20863ff32443d86510dfd4141fea9a81ff41843fea4a0df54232
  | 1 => 0xf51103fa63087f54e40fea1683fc53c43fea3a07fd4642ff19661ff404c3fc42985fd5120ff28265ff54483fca7087f94241ffa8287fe43cc77a8220df14931ff29a85fc53043fe8618ffd4530ff98441ff54cc7ee8320fd44010fd882217e51043fc64997f50c40ff10a437c53083fea9107f4ca31fea1665fe31c43fc61887fd4f41ef99465ff420c7fc86a05f54b10fb08221ff41487fe40087790d30fe99441fe43907fe4108774c431be28a657d50c87fea2197fd4443bfa8a85ff524c3fca4207f50431fd20081fe528c3f8a2a1ffd4a40fea9063fd42083faa1a1df54730ffa9081ff41d02fca1a1ff14c41ffa0c43fc540cafea4a1ff10020f7a9263ff53043f880987f94143fe19061ef32087fa81085f94a30ffa18617e53c83fe6420ffd0c42ffa9841fe53887fea3a17f14420bfa9c437f54883faa620df94021feaa4617d53443fa62187f90d32ef182617c53503fe42087f55330f7a92837d50086faa9187f14e10fea9a85ff43443fc43a07f54742fe90e817e54c83fc82087fd0f42ff19621fe54c42fea4085f54420fe19221bf43d03fca8087b8c920ffa8c81ff21843f8a3907f14640ffa18437d53907fc41887f54930bfaa0217d52103be60187f15131ffa82436e520c2fea9087f54a10ff98821ee20482fea990df94342ff99241fe54cc6f8a818ff4c510bfaa665fd4350afaa018df94630ffa9463fe548c2fca6197fcc610fea1261fe42083faa890ff10c31ff99461fc510c3fa6210df14d41fe21263fc5050bfea6217fd0832ff28c61fe53d03fa80085f94231ffa12637e510c3f8a3997f90430f699065fd54042eaa3107f90f10ffa08817c54842fca598ff90610bea9841fd43107dca5087f0c941fe29e43fc41083fca5987fcc210fe18641fd32043f88790dfd4941ff980217f548c3fa8298dfd4532ff108817d53887f8a610fd10721fe2a243ed32c83faa0195f55332ffa8861ff40903f8a098fb48421fe20a61fc52cc7fa86905f14941ffa0081ff20443fa42205f15321fe90041fc430cbfe85905794c40ff28887ff328c6faa8185d54440bf29e217e52103f8a9907f10b20ff18261bd43503d88510fd50510fe99421ec524c7fa85a05fd4e10be2a441ff50ccbfa83907f0c821fe28c41ff210c3fe65195fd5310ff21683fe40083fe60885f55110f7a1443fd43903fca421df55243fea8865fd41cc6fca1107fd0c43ff99441f641107fca6207f50a21ff20261f9300c3fea6887f50921ffa8c61fd30483f88590ff94e42ff90a21ff418c3fc87a0ff10521fe2a061fe30082faa7187f90b40ffa9281ff41903fa87187f94231ff21243fe42887fe62187d08510ff28085fd510c3fea521df94032fea84637e54442fca8197f10d31be29261ff42503faa610fd54620ff98a21fc51d0ffe20087f14440fe29
  | 2 => 0xcbfc82207f14c42fe29081ec21c83fea6207f94940fea9e83fe430c7fa85987fd4321fea9083f6310c7fc8598dfd5231fea9881f7514cbfaa0a17b88520ff19483fe314c6f8a9195f54b31ffa0621fc328c3fca5a07d50441ff28485fd318c3faa2107f54640fe18221fe42c86fca198ff90320fe21061fd5090ff8a5987f54530ef98461fc43042f8a7087f0ca31bea9c817e51c83f881987f48710ef98c63ef21086f8a6087f50b31ff10e21fe5150afaa3207f94c10ff20c81ff420c3faa6215f54620ff90241ff32083fca418fd8c510ffa1c41ff548c7faa818df94041fe20e43fc42087fc61907fd4021fe21221fd5110afca4107fd4f21fea1281fe32c82fca818df15030ffa8085f441087eca2207f50a41fea0a217d52107fa64205f54440fea9841ff540cbfc80a07fd0910ff19065fe42503f8a9197f90a41ffa9c85ff4210bf88398ef50c43ff19263ff51883f8a1995f54342bfa9821fd504cafca5a1ffd0e43ff20883fc430c3fca990ffc8640bf290437e53487fe42907f4c620fe10a21fc42507fc85987fd4520ffa9c43fc41cc3f240107f54943fea1841fd41502f8a8905fd4931fe20a817d54c43f842187f55120fe28c61fd424cafea2907fd0941bf28085fd51883bc8798778c932fe28485fe31c82faa5087fc8630bf2a021ff32d07f862087fcc520beaa241fc5210ffc86197fd4342fea8a41fe424cbf8a8907fcc640fea0843fd40483f881887fd4542b729421fd540cafca1217fccb40bf29863fc31843fc8698df54430faa8881fe42ccafea6885f54910fea1e83fc50d07fe63187fc8220fe28443fc31087faa9905f94441ff99443fe41483fc83185fd5221dea1085fd32107fa60107fcc921ff29a817d53102faa690fb50920be2a265fd434c3fe82987f14231bf28665fe53906fca8995f15230fe21885ee42483fa83987f8c721ff98241be540c3f621087f90b10beaa021fe40cc2fca810ff10d10bea9e41fd42c43fea9987f90930bea9e83fc548c3f865085f15020fea0461fc52d06fea9197f8cb21ff18a817e530c3f8a9987f14542bea9c65fe43c83fc63987dd0721fe294817f54083fa87a07f4c920ffaa2437e548c7fc6598f794c40ffa1821ff308c3f88418ffc8620ffa96617d52907fc81887f94142bf28e85ff41083f886a0dd94440fd10041ff318c7f681205f54231beaa263fd52103f883887fd0e10be28283fc524c2faa8997f50220fea9c43fd328c3fa8710ffcc620ffa9421bf4290afca6887dc8621bf29681fe418c7f864087fd4341bf2a461ff51502f8a4a1df55221ff21e61fd21083fc42107fd0020ff990817d5210ff862887f8c940fe98821fc53443f88610ff14730be28a85ff504c7f862187f48310beaa643fd43487fea810ff15310ffa9a81fe41883fea9195f54042fe90a61f
  | 3 => 0x8621df54643f7290817c52843ee6390ffd0821fea9681fc54087f88518ff10a32ff99481fd5090afaa1a1ff4c621ff99265ff54083f885107f08630ff10221fc54c87fca090ff88720ff996617d518c3fc86187f14742fea8e81ff428c7fe85197f50b21fe29a857e54083f865a07f0ca21fea8c61fe544c7fc20087f4c521fe98e81fd43c87fe42107f50831ffa80877e510cbfa8318ff4ca40fe99443ff41c83fc64a0ffc8530fe10c41ff42882faa9207f94743fe21c81fc43482fca9995f94243fea9821fd21c83f641105f15331ff29a83fd41882daa4207f90d10bf29c87fd51502f8a090ff4cb41fea8087ff31082faa7885f94a32fea1e63fe4310afca6087fd0c40fea0041fc438c3ea63885f94730fe18021fc51483ee82a0ff90f42ff29683fe5110bfe63a07f14d409f2a061ff514cbfe62987f54810bf28881fd40103fc6210ff90420ff28a81fd404c2f8a4a07fd4241ff98041ff40c83f88218ff50d40fea9e43fd43907dc4290ff90d41fd984617c548c7faa8997f54f42eea9881fd43cc2faa1217fd4032bf28c63fe5250efca521df94420fe2a041ed52843fc82987fd0e42bf29e43fd31102fea7887fccb10ffa0e43fd53487f887107f0c840ff28063fe53087f841885f14520be29a21ff4350bfe60987f94d21ff2a421f741086faa9197f10e31ff90e817f54087ec4210ffd0e40fa90843fd21cc2fca3997f4c921fea1a657e544c3f887197f4c820ff21843ff41cc6faa198ff0c640fe18a417c5350bf863187f4c930ff90c43ff21487fa63205f95121ffa0661fc5250ff8a7905b14941ff28487fd410c3faa2a1df95330fea8c87fc548c7bc6298ff0c210fea1065fe10443fea910ff54121ff21263ff54c83f883907fd0c41ffa0a81fd10043fe8320ffcc521ff190637d50887fe6310ffd4831fea12637f53c82faa3196750c43feaa663fe420cbf884087f94f10efa1c87fc40c83fc42a06fd0d40fea8e41ff54c42dca4207f10a10bea8e87ff42043fe83987f48540ff21887fe528c6faa610ff54440f619043fe41d037aa8187fd4031ffa0281fd41043fc8310ffd0e30feaa043fe52107fea118ff55232bf28887ed20083f86420ff14e41ffa1421fd43c43e8a2995f54742fe298416f52507fa83087fd5132fe19441f721c43faa4187f88730ff29263ff51c83fa62907fd0e32fe98621ff43482fea0995fd5131fe18c417e52107fe8698ff50b20ffa0e21fe42c82faa120df94e10bf2a0877e548caf8a610ffc8440fe192417d538c7fa87997fd4221bea96837e5210ffca521df55130bea8e817d52d02faa1997f4cb40ff99261dd434c3faa9087fd4943aea9881fc21043f865207f54e42fe21c21fc53103f8a5085fd4a10feaa665f641c43fca020ffd0e31feaa443fe43c87f8a2a07fcc440fe10c21fd518
  | 4 => 0x7f4cb30f799465fe52043fe43987fd0421ffa8465fc504cbfa83207f90540bb28c41fe438c7f884197f94343be2a0657d54087f843a07f94420fe29487fb304c2fca5a0ff94732ff98e61fd53907f887a0ffd4a41be282877e51903fa40085f55330ffa1483fe51903fca021ff4cb21ff200217e5190ff862107fd0d41dfa0883fd32cc7fc4210fb14941fe90843fd52506fea098ff90730bf29661fc40443fa41087fc8310bf28421fe40843f8a7a0ff54b43fea0661bf40103eca2185f54432fea1061f541c43f8a8997f4ca41ffa1e65fc42103fc60087f55321bea9e81ff42102fca0087f94910fea1863fe548c7fca1195f54a43fea94837e53883f220087fd4331ff2a0617d53043fc84187f10d21ff184217d5190bfca8997f94530f719065fd50ccbe86390ff4c940fea8a65fc50487f862987f50440fb28c41fc43d03faa9887f10e21ffa0883fd42442fca7207f95130ff21221ff5190ffca7907f94930dfa18873d540c2f8a690ff50842fda0281ff21c43fe6498ff94e40bea9461fc31d03faa8987d08710ffa8e61ff4250bfc84a0ff8ca10ff28a41fc50087f882187f8c410fea86437e52907fc84215f54810ffaa6437c53c86f8a5887f8c810ff20e21fc21102fca1a0ff10421fea0a417d520c3fea0a0ffcc710ffa1485fd42506dea498dfd4b10b6a9421fc41443faa110fbd0821ffa1481fe31843fca8197f88010bf28643fe500cbfea6a0fb8cb20ff98621ff410c7fe87a0ff10841fea0621ec42087fe8420ff94642f790441fe42086fca3197fd0c20ff10421fc54443fe86a1ff0c120ffa1c43fe53883fe65905f95210fea0883fd430cafaa518ff90030f799443ff53107f8a690ff95320ff21c21ff434c3fea3997fd5031fe18c437d54083fa8410ffd5110bf28461fc43103fea421ff0c521bf2a6637f544c3faa5187f90c10ffa9e81fe5310bfa40887f94131ff20221fd31083f885205f54c42ffa9683fc32083f280206fd0240ff180617e53082fea4a05f54610ffa1241fd434c7f884907f4cb10fe288857e52c43fca2a1df54c41ff19043fe420c7fca321f750f30f699241ff20083f864986f90541bf29485fd5290ffe6590ff8c431ffa1e81fd314c3f887217f8c110df21a87fd52d07fc8290df95042fe214617d5110bfca2207f95121be2a641fb20483f886a17f94632fe20a63fd528c6f8a098fdcc531ff2a241fc514cbf865a0df54243bea9661fc31102faa418df55241ff190617e528c7daa4205f94f42ff996637e5190afca8907fd0a30fea8e61fd43c83fca4185f94621ff18861fc21482fea2a1db14931fea0c61fd30c83ee4290ff14241bea8065fd52c42faa1a0ff8c910fe19243fe514cbf861107f10c41fe10c81ff32503fe6520ff94332ffa1a437d54843fe8298ff94b31ffa8e87fe31443bc
  | 5 => 0x24c0300b0000220501480200000004001016054048042be0005200b0000cc0606504e05c070070062785900705c0981300802800c0a01c24a0040100025a0000000600a09401c22060047f8a1195d94430fe1964177514cafca9887f10630bf29885fd428cb7c80a07f94141fe98e417e54882f8a8887fd4931fe18e617e52043faa7887fd0410fe21e217e54c87fca9987f50a31ffa1665fd43507fca4a0ffd0f21f799265fe40483fe8798ff4c831beaa4637f54cc3fca3905f94040ff99283fe428c7fc86207f54021be2a621fe21043f8a7215f54043bea94417f54442fca720df94031ffa9061fe42883fc60907f0cb21eea18877c54087f8a6a0ffd0010ff19241fd21043fea420fb88720ffa12617c544c3fc65207f90230fea9e81fe53083fc6420ff4c721fe180417e500c3f88318ff55030ffa0421fd21843fc43087d4c431feaa041fd430c3fea3195f14e21fd18061fc50d0ffa62a07fd0d40bfaa065fd54443fa60187fcc821bf290617c514c3fe8720ff90d42fea8465fe54883fa86217fd5130fe19663fe50087f8a1a17fd4b43fe19281fc20442faa7107f90e42ff98a63fc42083fa86887f54a40be2a661fe328c7fea0995fd4540ff28683ff53c43fe87987fd0820fb90a21ef21886f8a910ff8c640fe21261fd30442fea0a17fd4e41faa8861fc31c43fc62907f0ca41ff29a417c53c43fc8620fdc4010ff2a665fe54443fc40907f54141ff20a63fd43d0bfa82105f54a40fe28887fc43ccbfc81105f94d20fe2a0217e5310efca4197f55231ff99065fe50cc7f8659877cc832ff18c61e521087ee21087fd4a30bfa9c41ff52cc7fa63987fcc720fe200217e50083fe42a07f14810ff19461ff410c3fa82987f54b31beaa641ff540c3fea2a1df94c21bea9c85fc214c3fa64197f10210fb20a21fe41c83fa42187fcc320ffaa263fe30883faa7107f54131ffa0a21fe52843fea2107f08420fea0e81ff400c3f8a198ffd4243fe992637e51d03fc86907f90e40fea9c21fd40c83fa85085f54f42fd08021fd43087f8a4887f88430fe21683fd544c6fca910ff54241fea9e41fc42486fea690df94442f6a1641fd42042fca5207fd0b41f6a90617f54cc7fca8107fd4e20ff29481ff43c43fc85087fd0110ff10a217e53d07fa42887f90810ff98e43fe438c3f8a7a17f14931bf29063fd4390bfaa018ffd0541bf284437d540c7faa3217b90b20fe21681fc42887fe8490fdcc421ff18c41fc540c7fa8621f7d0d43ff19441fc43083fe8510ffd0b40ffa9843fd32c82f8a898ffcc831fe19621fc52d03faa1a0ff50521fe20821fe41c87fc87107f14642fe98e21ff52443f8a0195f94232fea9281be4250bf886987f10030fea0c43fe41cc7fea9997fd4b40fe2a665fc41843faa0a1ff90e32ff98a81fd51ccbfca919
  | 6 => 0x60581200505a0080a85a02201400800002000310020000180025090409002805004018068490120880500000c080040000185f00400604004c4002101e0000380009c02c0200a03a064178b80520101a00f032076110e601649c0d8025760003701a01a01c1180204c0b0010003ca0380101d0020000000128260c0b81800c04620002016068010080440303f02101c00805006000024048690020500000005001c066070000b8000170220140000000651c2700009a0940500f006ab40880605e2c01403a01800e318090060442300906e010450150220846e002000004000000004340000014c0f4100000022100780003c02c0a81300001c1b01200c07403862012148008150ce04c0280300002429809012020212750040040000901a0002d0080680080000500002c028780a4000ad8160100002282b0120001d81209e0292300f0000000000a0320000280000005c78005000004268000500000300d0004a4000bd0f402833041084000001f414b398290020000101501701a0207900000c0501a037006b900900f0280000183900002c09895094000008b10c800c0001f0161503080b0041e00100d0d23bc010070e822407808000004040050000680001800405c109c205e020008311060040700a00200027b570100a0038210320080302e4660800004b00003c0081b040029638010000080e05e0081481e8020020000480f02a0500008e000878060190000dc190247a20080400300a06c0101500404c0380a0040080601a0d84800c0027800c82304506100873826034010100010040002f80301007c1280101002c128000a8005dd00002a0002301802c02043001000001c080002a000000061d6000088a50e00a4000140100b00010d40000c0001900212c010c502400c2d00301609c0380c01a0ac0006b00c0801401702a0180000907c0080a00100a00824892014020000000860015d806006180070041e405827858000000010231dc00c260060000000000000001c568070180680100e0000000380000e0000000500a038000138880040000c002018070cd01a000048000000bc00027010080018000020200000202800c078180aa03c00
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x741c827d650c7209fd89548c27e65cc920be181544c6ef648c9209f196214c27d6094841bd597318c67f6254e109f58a538427e6015032bb189310875d53d0f419f196414c37551d0620b7d8d428c3e65294430be181328c35e6590d30dd984538827d6194b40cfd9152442bd6090d43dd984548c27d6494f209fd855090e7d60150329f59621082ed620c3209fd9742cc36d528c8109f990524436c52d09109f58a50043746154b109fd9743c867c6454231d754c53d0af46388421db54a420c67d6550521e7d91434c27f6510910b798c521067c6354341bb18951d02ed62d0520ee500408437764d4532d794e430873e54d48309f197214c3e73148421dd54c31086f564085109f58e51d0b6f63948409f980544436e5210210cf55142ccb3e54d0721bed95200837661150329f98e51083b554907109f996420c33f5490930ed9085150a7d6494331bb58a4390af96090410ddd465110f7461551329f58652902f960c8610b758c540827f6510010cf95340c42dd63101209fd81540c6f561103309fd97438826d62940109f59250c876e4394840af191524c37651c8220d354e521033f43542439fd8552442f56194d42ddd95310c75e538c030db94a21087f12044010bb98832482f7614cb209fd9731903765414532dbd4f52506ec64cca219f99352843e752c8510db15142c827d6510821dbd4a52cc6f960109309f196434836f5294841bbd89504c67c6548540dd58654443b76450510dd5445110e7d6550c109f98f54c836651c8220bdd855210f3c54d0230afd91319027f658c720bd98752102ec624c420bd98742442756194242fa94a401027d60950329f194400c2f6610c821db190524c6dd6314442d394d52102f561d01109fd8554c827c61552309fd97438867f6154e20e7d854310e7e6095331bed8132483ce534c8329fd8d50c877561153319b594420877565c4210dd953214867e60950319fd94430c6ef624c320be98342482f563087109f195418c27e64948309f195424427d6494f21bdd85438435d5394840d754e30042ef63885209fd81534867d6414a10db548520c76d528ca31bbd8954442ee630c821bb988521027e6014943be18131442ed62cc320dbd4d20082ef62541419f988540ca7d65cca419fd97311027f6354042dd58951883745454430b6181434c27d61d49309f58b544c27e61d52329f5875050a7f6510b30d794d328867d65d08319f994420427e65101209f19432c435d53d0f40bd58742d06fa6010c30e794f43d036e5290a10d79524310e7e6114d10dd14c21c436d52d0040e714d435027e61953329f9845050a7a6014c219f99731482ef624c6209f983548c6f661d5220be5805110b7553944409f596321036e62149109f596329033e6415321bbd81210867d6254c20de580540867e6590b30
  | 1 => 0x82ee62d0120bb98b43d0b756195132de983540427c62551319fd89544c27d65484309f58b548c36c60548409fd8953487775194620ebd91424833e5450831dd947408835f5390d41db98853c876c5250931b718d410c37631540319fd85544c76e5290a40db949310c27f6154c42dd584540c37552c8710d7d8d53443755190630db90f525067c62550109f99253883d8434c0309d98754883e96088520db94b311027e6094432ed15141442f561d48309f9875250f5d530c840dd1835150a7f6550730ddd5041c86f860509409f1815210f7452440109fd96428c27d6114e20d954a51103766494430bd185424c76f5354840b758e408c27e658ca40be597409027e61948309798c520427d6394241bb99332086fb654c0309f19543c827e6394442cf550540833f6455110bdd8532d027f650ca419f98c540867d60d4532d7d8d544c67d60952319f58e52903f261880209f9865010ebd6414830be580218c27d62d4d41cf55054c876e52d06109f596540c27d60d4941b7d8d218c27d6494332de983540c37551cc6209f189540c27e63152209fd95314837a6014c109fd8d51d033c54d0f309f197434827e6094c42b758f414c36d53d49419f98a51043766115031cf55241c42ee6210520dd146314c33d5415231db983525076e528ca109f596320c6fa600c9409f996438836d52d00309f99732443e561cca21f9146214833d54544309fd95401027b6055131bd9865090af8604c4409f18d529027d6395121db94b410c37753cc421bd597410875d63150219f597430c23e6415030db552528427d6194d21d798c54cc2f96010c309f58a54cc27d6395020d754d511036d6295131bb58a508c67d6590831cf95342882f96010820cf151404c3776548421db54842d027e65885109d1855210f9d4314043dbd49505067e65cc620db991521039d4310e20dd551510c27e62952109f58e540437660544409f994314827c6355220db588530437451541429fd9150cc76e52944309f986548c2ec624c120db949320c33d62550308fd95411067d61548109f1855310b3f6455220bd584434867d65ccb41d9d9521087ce530c821e71854310fd943cc1309f595438435e538c621bb988548437654085109f59643c873654544309f987544caf661885109f990540c67c6054b439f596324427e63d4b10bd185424caee62d0e219fd95100427d6394341e7d4e4350ef46150e109f181548c67e63946429f58e50886ed62904219f595438827d6594c21dd0c9511027f654c020bed8143c833d540c430dd54731cc27f6590910f958b41c875e5390440db54b42cc76f5294a419fd8d54843cc534c920af990308836e528c840bb58e21482ee6348421bed8141843755148430b7597318c67c6055131bbd92214827d61d5032b758c40cc27d65108309f59
  | 2 => 0x6014910cf55140cc2ef634c832db54832d067d60d4d41d754e438836d524c810ddd85534427f6255120db94842d06dd63d09329dd9541106ef6250510de582534435f6354d219f191518caf5618ca31dd4c9518827d65cc821f918941442fa6014841ddd0a511027c63543429fd8153442dd638c4319f592534835e5310f429f594410c76e53149419f59731483755354440bd98c41c877551145429b189534427e654c5209f99253082ec63c8421db58854883f060505109fd9741cc27c65d0c109f99253843e66108720cfd5254883b75190541db152520c3756590710bb98b51d0e7d63d4810ee181435036d5214a10db54a32903e631484219f58653882be640c9409f986539027f65cc841bd9845010fe63248421bdd8542503745110520f948421902ed638c920dbd89534827d62d5131bed81328c27e6550d10cf95242c82776155132b918532482ed6210d209f19643c82f5610c2208fd954310eec62501209fd95310427e61948409f98b540c36f6154830dd8c9518837751d4132ddd09511027d6294343bd58642086f561d0921db94a310c2fa60104109f983544cb5c530c9109f58e521076e64948309fd9443842fa60c86109dd85544c26e62d5030dd14641502f5618c931be181438c27e6508630bb1854210a7d60d5121d7d4e534433e54d0a21dd98454c435f530c520de59720882ed60d0821d794c43102fb6050430dd5865090bd6514c030cfd53424867c6254743f598c31086f86048510cf15140443db324c0309f995320427c6454810d7d4c434837554d0421ebd5142482f661d0b41f9987328867f6590c20d7d8d54443e53148421dd905501076e5490842bbd8941c867d6394b10bb584420867e658c720bb58b434cb7442944309b189544c76d524ca31ddd50514ca7f65504209f99421cc2fb6055131ddd46415026f6255130bb18931c835f53d0d10be98341d037561d4910c7151434c36e52cc6109f59432d027d6414132f948421102bd6414c21dd949100436e6214b109f984544c27f6590f21db15021c82ee62d53319f597328436e5290030bd984420867f6550020dd983514ca7d62944409f191538439d43503309f59742cc37753cc7219f58e548433f5490d10be58242c82f86050920dd589510c3755208510f6d81434c35d5388440db988530437652944409f99420042dd6310230f9d8941c42f561102309f995438436d5288510d9548214436f5214131d714f304427e658c740dd54621103b940100309f98c540827d6294341bb5834250af960d0610d794d511036f5248110fa98a10042f46150a409f99421d02746155130d7d4d304436e52c8440bd185428c67c6354042dbd4a52cc2f260c8510cd552510c27c6054f429f99643c87ad54948309f595434875e6314c21cf59053043755294440be983324
  | 3 => 0xb21bdd8540c436d62951329f596540cb5c53cc1209f982539077551902209f596410c27e6494a31cfd9153482f66190f21bbd89411027f6590030d794e300427561152309f59743c83d9300c210db94a218c36e524ca10db54f200827c6154e40de54050d0e6f65508429f592524427c654c120dd946410836f3294632dd545318832e54948309fd8953d076e524c4409f588535067f6154f40be580411036f520c910bb98843483e651087209f59720042f6630c421d7d51300c36d5250440af990530427e6294043dd50e510c36d658cb20db988548c33f64550319f59641cc2f661d50309718d544427e6514d20dd908514cbe76150b20cfd52424427e6590531d754c31c433e54948309f59353c433d5450320bd987531027e6094831dd945300c3e564484219f98a538435e538c821bb18931d03f251c8220dd546410836d5494830ed99041c867d65d0c219f59541c827c65504209f996430437751947209f59353486ed60c8421d7d4e5310b3f54d012097d95300c2ed6214e409f590530827c6055032dd50a510c27d654c9109f59432102f561150329f98053487e960087209f18154c876f6254443ddd8552cc76d52c8440cfd9154c867c6510f20b798f42ccaf5618c010bb98b519027d6194b309fd9643086f46150921db949210c2ec6250540db9095010bba54900409f196420425e6315210bb588404427d6014543bd58743c867d60d4f21de540504876e528ca31bd990410866f6254d21a75924310f6e43548409f9845350a7c65509309f98e52d06f561951329f595438867d61d5232f9d0521086f561d0e31bd18532483bb43d0140b718d218c27d65cc420bbd95210875f6550f309f58754c827c6510431dbd4a425067f654c120cf550548cb6e6215020db94a32903e9528c030b758c540867e6588730be18142cc33d5415120be58042c827e6395121bd58b410873d5410710cfd5254443d653cc721db54852102f96088410cfd51414436f63548409f58b540c6ed62d53319fd8d51883d5434c431f910841087753154031f34c8320c31d53d00409f19531483ba544c030dbd4a528c6ed61cca21cfd5254c827d6294241d798a531036e5308720dbd48505067f6154043d754f421027d6510c319f58f54082ee6008720ed504411027c6454420afd81401035e534ca20f9d8742086bd640c740fc885100427e6550b10bb583328ca6d6294241db18d528435e5350c20d7186531027c6590e20d794f32102f96014432bdd85424827f60548439f994314875d5314d21dbd53420879d544c030cf550420c27d62d4530ddd45504caf96090710db94920c42f561d0d31b7d8d514839e6050c43cf992534867c6254d10b798c40042f46154142ee50f40502f661d0b31ded425090b5d5314d409f99353086f96015021bb994525067e
  | 4 => 0xd189510c37654c8710bd59731c86ed620c1109f590514c35d6315020bb5924210b6d6214e10bb58742087765108630cf551430c36c5288540dbd95528436e52d0841b758c5110376534c510db152528436d52504309fd9743c82f96090d40d754d43086f86054d42f9085204427f6054e21d7d4e43502f761508329f594300436c5288530db94b511036f5294910f914b415077751085309fd85544437753d4542b758c214c27c6054e21bd984530827d64948309f595420427e62940319f194325033e54500309f996311027f6254c40bed81425037651c86209f992530c27e60d45439f990540827965840109fd96430c36e5290210db549408436e6154840be58042d03746394440dd584548827d6590840cf95043cc67d62951329f582538876e528c6109dd9521086ef6254d40bb58853102ed6214e10be18141502f561c8110ddcca511036c60548309fd9642cc3745494620db153524c77460544309fd8950cc67e6414520bb1895050f7553946209f99643c82766195132db14e521037454d4532cf552430c67a60150329f582534876e524c6109f997428c77752085109f592518c27e6115120e795243cc2ec62551309f18151d0b5d5354840cf55242083e73214532bd984300827d6015221db549420c33e54d0810db10152103775194520f954d21086de63102109f58e50c867d65d0a31b798c5010b4d5354840bd984400436f5454830be9803190274654c510dd592510c27c6354b10dd54951102ed638c8329f58a540c7ae54908429f98e52902746154b40bd185320caed6210c329f99353883765110440cf551300c3ea52c42109fd8d544827e654c540db90d520c33f5495120f514d314435f6354c219fd94210427f6550f21db54b210c2f76150b30b9185320ca7e6494a30bb58841c827d6510a10dd58754842f764c87109f98e52c427d6510e109f59431082f964900409fd8151d0e7f6550d21db54a421027e6014d41ddd4431502f4604c7109fd8d50886fa600cb30dd54631883b654504419f5845250f6c520c940cf551410827f650c910dd90e518827d6094f42cf551420c2f66190d41db94a31102f6618cb21cf590538436d64948309f19150c873d54d08109f994438827e6094442db94a401033f5495310dd90f514caf9600ca409f996324427f61548439f992530867f65cca41dd10e511036d5248210bbd89544c75d538c210db94e214827d62d4d10b798c5110add6314810ddd0e510c27d65085309f98f540caf66190d10b7d8d505073d6155030d9549511027d650ca40dd54721c827e61d5030bb189414827f650c020bdd8d414435e6315021db54b42d07746154831dbd5342886bd6414e10b7d8d544436d65cca32bb988418867d63951109fd954210b6e61948309f98053043775254430bd18532cc35e530c
  | 5 => 0x32cc36d60149419fd95424cb6e4314931bd98432c876d5410821db949218436c5294141dd90a518827e6194343cfd5254c867c6550e209fd95420427f65504309e181544c6f5644c510bb58843d0be55108520db54a429067c6254243dbd492004277654c431af983435027d6510930b798f41cc67e64d4f20de98354842ed62d4630afd91534427e62d4d409f588544c76e6214e10b798c400c37950140329f19741482f76154d40db148325076f5454a10dd14f21c436f52d0910db548328427e6215231bd185328c2ee6210c32bd98420042fa60d0510be58221c435e530c4409f191520c27f6550c20bb588511036e5210b319f58a508c76d52d04409f99641cc27e6590d319fd9521cc3e56110821de5405050ef9608c630bbd8941cc67d63947209fd815190e7c63546429f593524c26d6294231d794f30c4374510c520bdd85428c36e524ca31db548520c2f56110f31f9484218827c65d0930d758c544c27e65881109f597210c2df63507319f189500c73d5410832bd984540c2f663d0721e7953300c2f46148310db94932103b960d0f409f98b53442fa6014432cfd52434836d52ccb31bb993210867d60d5221bd18553502f56108010bdd85428876d6294d21cf191534827e6214d41bb988538437642d4532dd945419027e6510a30bb58c21483765450710d794e43902dd63d0a31bb583324cb6e524ca409fd89534435c53cc9219fd94410826f6254d109f9963048376538c510afd954210a7e63d49109f99352c436e5288710d754f320435e53104409f992520cade6310310db54a420c2fa6010710bd185544cafa6008530bb588548c35d53904409f996210c2f6640c4219b58b54cc6ed62d0320de54050906bd64d4430d7d4f32486bd64ccb40cfd52540cbe53248421db54a321027e62943439f58252d0eec6250730bd586308427f658cb41bd986204427f654cb41db186521037651506209f59532902f66290441db94b42d02fb6050920dd944210c3355410421fa54a40102f860549439f58b54cc73f54d0510af990304833f64552219f19732042f56190c21bb189438867e6510020bbd89315027e61d50209f99632d076c52cc910af59030082f86050730cf553430c2ee620c2209f189510c27d6510931db54b308427c6155320bdd85325067e60952319f19532c42de6390431ebd4a4250b6d5288630af990538837561d4e10bd58b31c867c6255330d7d4e53d0b5d544c030bdd85324427f6588630dbd4a325067f6590821dd553514cabe64cc9409f594219033d5415132bd185328867d6394410bd18542883ea21c8120d798c540cb766195132dbd93525077560d4542cf952418867f65106309f197315027e658c5209fd9631d036c52d0930de98353082bf6454530dd546411033d5410020db98c525076f52d0541d
  | 6 => 0x35d5310c40b718d51502f9608ca30be98243902de63150219b9885050eed6390b209f996304427f6354b40cf950320c33f65508429f5825290e7c6590b10dbd49325075e538c421db54a20042be6414e109f995214c27d6094432db98652103e74108520be582415036d52d0430de98354883756194020dd949510c3766114c21bd18540c427e650c540dd58f5150a7e65cc5109fd85530835f6294c409f597218c27e64d4f21be983411036c54509209fd91508caf56110010f994a210877551104409f983540837b654c0309f99421442f96008410bb189418877654c8510af990510c3665254430bd988214427d6550c20db983524c67e60d5030cf185540c2f66190f31be983434c2ef6250120dd14b108427d654c840be58243cc27d60153219f98e54882ee6290821db14c21c82ec6150b20af990500c6de6315020ddd46514cb5c5490f30bb58854843e432085109fd9632c437b60551329f59442cc27e6550e209f597315039e53500409f58c548833f64553319f597420833d54904109f59353882766194232b758c42cc2f960d0c409f992520c67c63552219f595428c6ed62d0d20db54c320867b6550040af99021502f6610c3209f98f540c6fb6050b309f19443c86f9638c030bd98432506f4640c4219f58653102ec624c721bd984324436c538c920cf95041886dc6350a309f18550ccb3d54084309d9845050e7e63940419f5845050b5e538cb41dd59431c876f52948409f197428433e54cc030d794d32106ec6250630d794d52102be640c740bb98b531027c65d0810dd10d511035d6395121e750c435027e65101309f58a510c36d6154840dd94440882f561d4840dbd46214827e6494d21ddd0b5150b765254440f9549511033f5495231dd584544437a6014e10dd14f218876d5288610ddd8d511036d5214a41dbd4a520c36e52d0440fc98021c435f654c4319d584540c31d43540439f98254886fa60cc610fc545300c27e6588440db94921102df6350b329fd9421103e4420c421db54a308436e5208440d798f540c39d53d0040de58354cc2fa60084209f983535067c6054c42f554c31087e762504419fd8554cc35c5450f309f18552cc2ec64c86219fd95325027c6454730ded4250d06dd65cca329f994404427d6194a309f996314876f62548109f98c52442de63d08319f984540c2f661d0c219fd95324436d524ca40b7d89320cb6d5414931bd984408436d52cc4409f98a530437660944409ed95100436d52100309f588544c27d6508410cf950420836f6354a109f99632503755114620cf553410835f5394d21bd58f214437551486209f99443842f7614c8409f59443042bc644c840f910821c436f5294b41dd94731cc2bc6454910bb58b510c2ef624c5209f582540c67c6154e20f998432086bf6454121be983
  | 7 => 0x214b31de58354c836f53cca21db58a544827661150209f58154043755114532bbd89419037751941429f98353083cd424c832dd590514ca7d6394640cf55054ccb5c5310d10af59030c827f6154342bb98b41c827f65ccb41cf552428cb3e54d0c209f18152d07e441087209f98c525067c60548319f994414c75f538c940cf951430837a60d4c109fd96428427f6454420dd54b21442f960c8420d754f31c86fa6014c419f592500c27f6154d20f91854210b5d534ca20b798f414c67e6115010bd98a41c427f65484209f596411037565cc721dd545400c27d6494730bd58420842df63505319f98a531073f5450f30bd98442c877b5094121db588540c67e61d5330b718d524437763546209f5865390adf648c1309f98853c43da43cc130cf152414c2de6310631dd18d5110376510c4409f18d528427f65908309f590538427e62d5330d798c53486f661d09219fd95414c2f46050510be18143043766254440bbd89414c67d6015031cf952210c27e63949109f98b544c76d6294d20db54b310c27d6590c329fd91510ca7d6510410db945210876e52882109f995414c27e6495131db54b42842df6354142de980520425e6315010f9cc4214827e6194e20cf191524433d54151309f59251882fa60cc4309f195404427d65d0f10db14a424c73d5490f32db14b425075f534c120ded42501079d53d0f40db54a320c27e6510540bd58a21086bd6414c20bd984400c39c5350f409fd94410875e5314440be9805110eef624c730de58053c42e56288421cfd91548ca7c6454b319f592508867e6510630bd5875290ef66115220d754f32103ae52d00409f988530867d65080109f595310837a6015010bdd8532d073e54904109f58f54442776154b40dd18e518833d5450610bbd894350b6f528c930dd95141442f56490510d794d4390a7c6590f10af593315027c6154a40bd98420843b541106319fd9420042fa600c620dd94741883796015031bb98b510c3b54110531dd8ca518827e6590920ed50441902f5648c5109fd96430c76c6054a109f59542cc33e5490040dd5875488374510c540ed55341c867f650c8109f18951102dd6310010bd996314427d63153109fd8152d06ee62102209f58354c86f464cc4219f19641482f5610ca419f181531067d64d4c219f98c540c35e6454c40f9948214427e64940309fd9643c435d53104409fd9531d027d65c8440f948750086dd63108329f59353886ee6210f429f993530837b5094232d754d32106f66110310d714d435077632d4532cf99053843ae5410821cf990538833e5410a32be982429027d65c8740db149414c63e6414e209f59441c82ec624c5109f9835250f773254440e750c434827c6550a109f988530827d6394840ded42508c65f654c4319f9885050e6e6214c20db9412008
  | 8 => 0x219bd8951d027f6255131bd986504cb6d5294430d795143cc27e64943329f596320836d65c86219f5885150e6e6215020db14a324c76f54480209f99053042f661d0110bd5845210e7d6550d20db54d528436e5250810cf952430c67f64546309f588530436c654c920db14d521027f6548410dbd8952c42f562d07219f98251d0e7e61d5021d754c32082dd63102109f59421102f56484110dd54451d0bea524c030db15242c826f6255131b798c428ca7e6194c42d994b108427f6354b419f99431d027d63949109f98a544c27d6594810b798c52042f76150a41cf597409035d5314f40bd586425067d60d4d219fd94438867c6548510db54b51102ed6290220dd54f100427d6494020d794f30c837652c4210eb508420833e5410410e750c430ca7f6454a319fd89539027d6094843db583524c67d65d0c319b588530437551d0740cf553400c3e55294430d718d52443775344010f90cb410867c63546409fd9731d03f241c4110db14d324836c54085209fd8951d027e6510e21db189544435d530cb209b58b540c27d6394440db54932102df604c030eb953428873e5450e32db54f328867e62d5021cf95342cca7d62d50309f994430827d61d5132b718d210c27c6254e41ed504414876d528c440bbd8c21c82df63484309f189501075d5314c41cf590530877a6015021b758c418c73c6055030db54a429036d5290040bd584408427f6454b309f98e540867d6054810db54b32d073e54d08309fd96319027d63d52109b98b54843ea52500409f58453c827d6590930bbd89430837565d04219f58c520427f64540329fd81528c76d63d4941db994525067e6510d21d754c300433d5410410cf55054c427e6294d109f597438836e52ccb319f98a53c43af43508429f98b544427e65151329fd96219027c6454331dbd4f208827d65c8730e750c43cc2fa6014442bd185329067d61d5030d798c53882fa6008720d7d4f434836d62d5221bd984424435e6395121b758c521031f6550c439f592510436e538c832dd94721902f5610c1209f59442c43cd434c832bdd90214427e6494d109d58453082be64d4430f598c31c877651d00309f98054ccb6d62d5331f5547300c3b65150040bdd85430867e65085409f58853c42f56190b219f997430427e65cc921f9d08214427e62d4c10cf952300c35d530c410bd59721c427f6510a30db94821902f96010910ddd8f5150a7e65d0940bd18532502ef624c6308f990530827e62d52109f99252cc35d53cc320cf55040843755190640bbd89318867d6494a10dd984548c73f54d0f30db98d520c3ad43508429f19532d07d65394440cfd52540c75f654c832dd14d518827e64943219f993534435c530c540ee509401036d52144309fd96410c35e6315031dd947318827f6550520bd587540c36d5
  | 9 => 0x181210873e6415131db953524c6f56110931bd586400427e6414132db14b324c76f520c931cfd52548427f6054442db54a400c2f960c8720bb98b31c82ed62941319f987540c67e61d4940db98b54c87776154f21dbd92520c2f661d5332bb988314827e6014543cf953438caed62d0f429fd97430835d538cb219f58e548876d524c4409f19532487766194232bb988511027e65d0730db14a41506fa60c84209f58253d076d52484409fd94329027c6510c10dd54c31c87f2518c0309f994314c35c5310d20dd10c514ca3e64148109f19443486f7614c931b758c40c42dd65cc230bd584400c375510c440e750c438867f6354810dbd89548867f6054c10dbd4b32443e92008210ded9540102f66114332be980428c36d524c4309fd95430436c52cc531bb98c42886f960cc5109f587540836f530ca21db54c328876d52906109f993530437551146429f5825190a7e65ccb10bd58753d0a7e63953109f994319036f520c940dd987540c67e6394d218f590530437754c42109f994534867e60d4931bb5885050e7c6510e10fcd85100427c6355210db182521027e64951218f99053086f66110d21dd547300c33c54d0921bd185324867e62d50109f994324867d6294d109f98b54cc67d6550f20f34c8320827c6154d20f590d310c75e5310840db18c525073e61950309f596530427e63d5221dd19251102ed62d05219fd8953d03776214542dd54f31c86f6618c9319f988530427e6590a319f98a500427c63548409f597324427d654cb40dd94b31086fa6010f409f594320427f6550a109b988530423f6454910bd587324426e6294010dd4ca51882f46150c219f583548caed6210421e750c438c3796094d209d594410867e6414d21bd58440c42ee64484219f18953c426e62d53319f994435027e65d09329f586520c2ee6214043be58021c43766194242dd182511027f6354342f90cb31087ad54548309f988540833c54105309d997214433d54d0610d794e430827c65909109f582529077654504419f594430c3b654d0721bb5834290aed65d0821bbd89414867e650c8419d984548833e6415130bb189311035e53cc810bd994514ca7e6494c10f9d8931443775194740d7597308c27c6550c20dbd89544867e62d4530b798c42cc76d6215030bd98432cc67d64d4810d794c32c837551146439f59631c835d538c0209f594318827d64d4121e7d814310e7e63942219f18550d0b6f5288540dbd49324c2f960108409fd9151cc27c650c421bb58b438873d54900209f191518836e52508209fd94328427e60d5232d754d30c42f960d0f409f984520437765507109f59053886ef6250c219fd9543c827d6294743db14b414c76f52d0931dd984540427e6194c40b7d8d420c39f6350f409f59443c876f5294930d754c538877652d04
  | 10 => 0x2842f6628c431bd99031c873f54509329f5825310ade6310130af59351ccafb6050e409f594434877462944309f988514c27e6590d32cf952410c3775494430cf153434c7774214532bd584438877651d0740cfd91544836d6510a21dd14d31c427e62d50329f586540cb5d530c440bd18542482ef6250620de580540cb6e5208420e754d401027e6014d10dd947210c27960150329f596420ca7f6454f10f9d0b310876d65d0a42de540500c67e65c8630fc98231c42fa60150319fd9443486de63908329fd9642cc6f561d0f419f18d52d06f66190a41de58352c42ee620c120afd91504caf76150b329f1815110ef764504419fd9421903ad5410821ddd47214c2f96010620db18352506fa60d0f409fd81544c3ce52cc030dd54451cca7e6394840af59741907e52108540dd546210c36e52084109f99442cc7db434c030cf953438c27c65d0e10bb98242482f7614c1109fd8d52842fa6010530bd98a31c436d528c8419fd8554482f4614c8109f5974004375518c0309f997424833f62950309f5964310b3c5450d319f59621d03e56188120f5505310c6ef6048020bdd85420427f654c840d794e30842bf64541319f59432c43b55150040ee552300c27d658c941ddd53410877453d4542db95142c827e6510832b7982434c36e534c832dd18e510c2f76150841bd58643c877661d5220f594d51102dd63100309fd8d51d0ae46150920f3189310c7f25144010bd98231c427e64940209f596400436e6094830db5485210776514c640f90c421c835c53cc920dd98752c427e6394341dd90e510c2f661cc841be18121882746155132dd947218c27d6014941d794d439067f65900109f582544c27e65c8440dd946318836d5410a21bb59021c83745490510bb58032886ee6590920dd94640882f9608c4109f195414433f64552319fd8d5190b6c5454830ddcc8514cabc644ca40cf55043cc36e52500309fd9542c439d4310f429f194414c2f66110b41af59050ccb3e5450e309f189519027d60d45429f990538436732145329f588514c27c65d0e21bb18954442fa60150329fd97218c27c6214d20bb189505067d6015121ddd4b214427f6355132bd986328c6ed65c8220dd94631902f86050f109f59352c437443d45429f19643042f7614ca31f908720c43e742d04219f18d518827d6195332afd85411075e6315331db948200436c52cc940db54a310c37b5094142bdd85329027e64d4532d7d8d538867e6494c31cf150434427c6510e209fd8152cc67d61d41329f59742cc7e552087109f58f525027e62145439fd815290e7d65d0e219f58c54482f4614c841bbd89418c67d6510520d754e32d073f64551319fd8954442f56194132bd584548c26f6255110dd0c9510c2f46150940dd945318835d534c7219f19743c82dd6390030f9
  | 11 => 0x7f65884309f592520c6f5638c510de58254483755150220cf95340cc27f65d0a309f19632502ef644c920bdd92314436d6154830d794c310436e62d53319d984540ca7e63d5121d754c5390a7e60d48109f58e544837761551309f185540ca7d6095321af99332907774254430dd945218827c6550520cf551438827e6115320b718d42ccb5f5394c20dd583514ca7f650c420be582429027d6294740d718d544827d650c841db19152843cd530c821bb18132c833d6494d21dd58453c87764294430eb54b40102f5610c831af590215027f61552309fd8d511033d54c8430f9107210867f6255020b758f41cc75d5314440bd987324427f6055231bd185328427d6414f20b798c40082ee608c9209fd95414c76e62d5020cd151414436f62551309fd81544caf960148319f196428436e5450920f9189310c76e6215320bb98843cca7c6550d30b7592304c27c6054a31ded425090ef561ccb41bd98743c873f6455030db148424433f5450d32bb98a40882de63d09309f9825290e7e6114910c7553300c2dd6390832db586520c27e6494432bb58840883ba54500409fd9152042f561902109f99251086796015031db54b328427e63d4142dd981518827e6550f10dd185544c33d5450a20bb189410427e6515121cf151404827d65906309f59521cc27d6590e219f99740482f5610cb10d798c540827d6094c219f987504cb6e53948409f58454082ee62d0721bb18941106f661c83109f98a5090e7e6394321b798c424c75f538c910d7d4e5350af7614c921dd945410c33e5454830d794d421027e62d5020db14b200427e65909109f98b53087e52108520d754e43086ed6284010dd54451102be6410d40be580540cb2e54548309f594428c2f56190d419f990538867f6254730bd984304436d5454830db988520433d54d0e30db548418427e6215310d794f431027e60d4c109f58a54cc774538c710db549210c27e61152329f58a540435d6395132db54821c43766114e21db58e521036f5290531af59032d036e538cb209d586544ca6f62547309f990528427f6454b319f58a53102fa60150219f181539067e62952319f99731902fb60485109f58b535036c53d4941cfd53408c2f96184010ddd46514c36e6215031db149324c6f96010f40f918542c835e5350c40db54842cc67d6094d209f98f544436c4314941b758f51102fa600ca10b718d424ca7f65481109f594420c7744294440cf550540c7d632145329f9944350af565c86219f997434c27c6254e40d754c53842bd6490d40dbd89534873d5450e30d798c530836e6094840ddd4421502f661d4f42bb58843ccaf960d0b40f918931c427c6054c21cf552430c2f56190d109f996434827d6094443dd945418c37a6015210d7d4e31502fb6055132d7d8d538427e6510730db10d5
  | 12 => 0x501309f98754ccb7665085109f99442506f565d0641ddd9531c427e6590b109f98453882ee62d0c42b758f414c67f6355310f9d85324827e6294730be983320c37743944409f59643103766115221de181544cb776155131bd185428c33e54904219f99443c833e54cc830cf14f43503d55394440be98031483775194442dd182510c27c650c941bb98b53d06ed620c2209f993514833d5415010be98043442f9608c710cf990540827f65cc8409fd96418c36e5408720cf550520c36d60d4941bb58a509076d6494a109f58254ccb3c54d0d219fd9742cc66f6255121af990300427d64d41319fd89544877553c4210db549321076c43d4931db94520082ee6215030dd551518827e6394d10d754c530867c63550109f99732d06ee6210120bd18532c427e6014d42b918941442f46250510cf552420c3e952500409f986544827e6590931db949408433e5410b319f99621902766115230ddd47414c27d6215031bd58742886ee6290d209f584534827e6590b31dd50e51102f860508309f19543c86ee6190920af993321073e5410430bdd85524c2f76148110bb592204827c654c521ded8152443e732085109fd94430835d534ca21dd192510c37554c4010f918d210867c6588540dbd92528439d6050c439fd95424c37661d48109fd9521102ee62cc120db948320c27e6394342bd987520c2f46154843afd95411076d53cc821be980320c27e65d0520d798c53c86f56188120dd984530835e53084409f1855010afa60c8720cf552408435f6354d20d754c4310b6d62d4e10cf55054843756114d109f98a548c27f6590620bd98431443e552c4210dd987530437a60d50209f997414c27e63950109f59053487ce630ca21dd589511027d6550b319f98a50cc75e538c8209f19153c873c5350d40bb58b53842fa600c540de980548c36e52cc030d7949320ca7f6454332d798c548833e5410f329f5835350af461508329f996434427e650c931cfd53434cb7542944409f58f5150abc6454121ddd4c5150a7d6014d429f596210427e6510b30cf551410c27e6590a10bb988318875f53cc510dd996314427d6095131af191504cb6e5294440bd19331c86ec624c640db949401036d6294231bdd8542842f661d0d10bdd85428ca7d6194c20bd19031c87e461cc8219f98c504867e6395020be580325035d530c210bd586508cb6e6214a10cf151424867d6315221b758c50d076c528c531dd14a510c36d52c83109b588540c67e61d4d209fd9543c42f561ccb31f919121087e76348421f9d4b314c67f65480209fd96318833f5495131fcd4210442bd640c1109f583524c67f6254c419f587535027c65509319bd95200836d31149319f992518c27d62d5330d794f43d0a7f6454c219f997314c2f46150b30d794c30042f960d07409f19743442
  | 13 => 0xdbd5042086ee62103309f58252cc67f65d0d20bd98732d067e6590630be58032cc27e6094c219f195404836d52c4210cf552320c26c62547409fd9432c42f96010d10db584525077551904309fd94428427e6195330db14b325067d658c4209f58f54c42ee62942319fd95424c67c65508109f58e50087745108540cf151434867d6414532afd894210b5d5310840bd192210875e5390e429f99252842de63d48409f595314877742145429fd97420c3ba43500409f59632d025f63551109f98a540c6de63103209b195424827d61d5220dd984530427d6550620bed81318c27d61942439f189548c27d6095232dd5445150f7a51440109f990540437551cc220bd58643cc7e762484219f596424c73e54d0e209f59431d02ee63d0a219758c54043d6538c4319f18d544876c6394a109f59742c427e6315320bd185428876d6214143dd986500827e61d5032af990500ca7e6510620b758c500867e6094e429f98c514827e6294e40f9484218c33e6415121d794d430c27c6510520db59621c833d5490c329f596315037b6055110ddd85524427d65506309f98254ccb6d5214a40bb588314835c5350d219f98650d0b795014342be580319027f658ca40cfd52540435c5390d41d754c53d07e52108730afd954310e7e65105109fd96321067e64149319f58a548c2ec624c521bd984424c77765440109f59643c82776154b309f99053442f563085109f996310827d6394010bdd85420c76e5408520bd984404c27f65485309f594310867c6254630dd144414c35e53cc4209f992508c67e61950309f98f514833e5450e209f181518ca7d60d5032db94a210c27c65d0d21bd98440082f56115220dd946410427f61553329b588540c2ed6290d209fd8d529075d5350c10db18953086ed62941419fd9640083ad5490b20dd947410c36e534cb209f990504c67e6314c109f195424827e65d05109f5965404375650c421ded4250906bf6454520f594d310c67d65d0430db597328867f6550010db14d528433e6415010d714c314839d4310e41d754c535067c654c110f3d4a314c6ef6450842bbd89515037b5094331dd8ca510c27d6215030dd94921086dd6314420cf550540ca7f65cc7209d586508caec6250610db949208433f6455010d7d4d434873e6415232db94a300c37565107218f59052042ef624c410dd544218c2f76150b10bd987538827d64d4520afd95401033e5410c30dd191518835d5314e209f58254cc67c6454031dbd4a525076f5354a10db54421c836f52105319f580548c6f4614c8309f58a5010e7e62d4143cf951428827f6454221f90c9210875c5350d40af593520c27e6314810bdd8532882f86050610cf553438827e650c120cfd51404c27d63d4b10cf550400c27e6508640de983538836d62940109f99641882dc63
  | 14 => 0x8953483754254440be580214c27d6195230bd584421075d5350e40fcd81314436d5288410ded425050e7d6194242af5974290b6e63948409fd8d54c867d61d4c20af99351ccadd6390431db54842d07755188620dbd50428867c6055031be58043102ec6250431be98041d02dc6350830b758f52d06f56110130d794c31c42776154d21fa58232c827f6154242ee50540103e431c8421ee500404427d6094732e750d404c2f560104219f596329079d5490f309fd8d524433e5410421dd14b415067e64d4121ded42504cbce434c8329f984504cb7442544409f994304436e520c831dbd4a504c6f960c85109f982538867661d4e20cfd51434876c52d4131bb98a41887755114640db14e32c82ee6108520bbd89318427c654c920f554d511027e6510940db94b308433d5414430be583421037453946209b19532482dd63d0b30af590325073d5410f319f990504867d6510d209f59721902f761508309f18550d0f76534c431de58254443d5324c431d7941300c27d6314540bb59221c82f960d05109fd96324437751d0520dd18d518827e61d4d42db948321027e64d4f10bd18543c876e62d50329f18951d03e74248421cfd85540c37552544309f59432d07e732d04219f594428c67d6494732bd984428c67d6094632bd5845010b674214542f6d01300c27d6294d209f98e528427d63d5021bdd8543c876552544309fd8d521067d6394a419f996414833e54d44309f98e534827d64d4e10db548308436d53c82209f58253442ee618cb20be181410c27e6394821de983520427d6215010e750c430427e6590f10be980520c76e52544409f597214c27d6015021cf95243cc2f661ccb31f998821c427f6454e20dd185544833f54509219f992544c33f6455020dbd4b32502f960cca20cf951428879d4310c419f596428c2ed628c621d754e320866d62150109f59732507e76448421db54831842f560d0641b7d954310e7e6414530bb98b31c86f46154930bb19032086be640c210bbd8d424833f6255030dd951518835f534c510bdd85435076e520cb30ded425010e7d6094b419f185520c37432546209f196434427c6054f219f98054cc67d6314b10be980431035d63148109f582520c6dd60d0d43dd944400c27d60d53329f584540caf8604c930bb18941c427e6510932ee98343d036e52d0830dd94421103755114720bd587538827e6115110bdd95411075d538c6219f59432842f661d0f41cf553410c36d6214e20dbd87524c6f56114032d514d31442ed62d47439fd8d529027f654c820d7d4d4350afa600c730d794e310c67f61551219f595404c27d6295110ddd8554c876d65cc821fa94a200827e6550f20db98b548427d62d4c10dd947310c33d54153209f597329027f654c8109f592538437760d45429f59443c427d639531
  | 15 => 0x103766114810cf990544caf965840109fd81510ca7c65909319f58a53c42ef62505409f58e54c82f56110c41b918d210867f6054910bed81324c27d6510b31bb98c42086ef624c7109f592530c3755110430d794f40103b554944309f9835388776514c6309f184544433f5495121bd9845090f7460145429fd8d500867f65d08319f59253486f96090c30db14b204427c654c7409f58a53d06fb6050830f34c832c867d658c940dd4ca510c27e63953209d58753882f5610c0109fd95404c3b65454430bd191210876e5210841dbd9521086f46348421d754f431036d5394840cf952420827f6054732cf951510c27e6394042ddd09518827c6154843bd58732486ee62d0c21ddd46314c2be64150309f997438836c5388521dbd91528427d6590420cf58a540c36e5354840be181434c2f561100209f597420cb5f5394d409f990540ca3f6454d10f5d8d310c76c6454830cf55340c427e60951329f99743507ad4210941edd5141442be640c310db94a218427c63151309b988540c67c6454432bb982214837443544309fd95428c36e62150219f194438873e6095030d794d31083f16008710be58341102f56390710db94a308427f6548630cf950310c2e46448421db152214876e5354a109f195218c3755114420d7d4e53903bb5090140bb58a438867e6094b41eb50842c867c6155332cf55054886f66110e219f58a530436d6354840be9805210f3c54d09209f58650cca7e6495110ddd85544427e65d0c20db553200827c63548109b988548c33d5490832b798f40cc2be6414432d914b41506f66110320db14b505067d61d4d209f19531c835d5314f10f9d85320cb6f6194a109d584548827c6510910dd1465050b765108420bb58b31c827d63d4910d758c548436d520c831de58054cc27e62d4141d7195434c27e62d5230bb58a430cb5f5394d41cf95141083d7634c710dd9835150aec6050b20db94f525067f6055021b718d504873e54503209f988548c3e76250510be59720883756014542b758c404c27e63951209f18d5090b7743544409f597414c33e6415031be982435037751cc5209f98f50487e732cc421e7d8d43503e4614cb209f58a53d027e65d0921d794e30882f760440109f597310873d54cc430dbd89544ca7c650c910bb98a43886fa6090940af18143503e66210421db15242482ef6148421db94a211037661d53329f98853442fb6050510bd98642086f46150d41db5485290e7661d4810bdd855050a7c6354241dbd52528427d6414e209f194428427f63552209fd9153886ee6210230bb98a544c67e63953219f982518ca7c6454d10d795243cc33d6414c20bb193320876e51c8220dd98f5150b75518c220be982218835d5350840bb18931883754354440db948328427d65d0630dd544210827f65087309fd
  | 16 => 0xe62151319fd95314867e65d0d10d7d8d53c437950140219f594320867f65d0a31e750c43c427d6590841cf550544c6f661d0d31d798c534437651840109f189548c76d62d4e20db193524c75f5394f21f54c4314877551084409f592500873e5450c10f9905210867d6394342d794e43907565394440cf550548c33d544c430be181544cb745494430d714f434427d63948109f983540c7744214532bd98241c427c65d0e20ddd4f10843bb41500409b594320867f65c8440db54a219027c63544409f59431042ee62d5030cf553430437651d00409f584524c36c534cb20bb5884310a7f65907209f58f54c827d64d4f209f58454c82fa6090f309f197215027d65d09319f592520836d5208510bd5845408376538c431b798c52102de63d4b41bbd89310c76e5250a309f98253486f960148439f98854cc27d6510c21bb58831886bd640cb41cf950430cb6d52500409f98b515027f62544439f980544ca7e61d4d40bd987428876f60d4941db148424c36e65149319fd96329066f62544439f58652102de6308730bd185429067e6590521ddd4721503756194232b798c548427f6154a43cf952428cafa60c85109f994318827c65ccb10be9804284377514c5309fd94311036e621532197d95320ca3f6454d20dbd4a528c3e9524c030f958d210876e5290430eb50842102ef6250520e750c43ccb3e54508109f994420c6f86050c20cf551320c35e514c4319fd95420c27e61d5220e750e5010f756195131dd15241c42f4624c431ddd465190eed648cb20be580318827f6155020dd946400c375658c710cf551430427d6510c329ed81544ca7c6254331be58021082e4624c431d794c521036e5454a109f98354886f661143429fd8d510827e63d51209f997434c76f65480209f58f528427e6294740de58354c435c534c110db54a51103ce424c832ddd83514ca7c654ca10be580414827d6194f20db183524c7766514542b758c400837553cc421ddcc9510c33f5450110bb98a430ca7d654c7209fd81529067e6215031d754c534437b50940329f98c54c867e62d45439f19431502f56114c42d798f540c77463d4542bbd89310c27e6494d20bd984431067f6254c209f98e51042f4624c7109fd8953c437661d50309f996324876f52109109f191528439d4310e10f9d8b310867c6454e219f586544ca7f6254031bd588310876e5210b409f596434873e5410020cfd9543d033d54944309f99631502ee62d4440dd94f5150af860485209f98a531033d5450810bd18530c42e4624c710f3d8d324833e64152309f590534827c658ca10b9588310867d6590e20dd55041c867e6114d409f1963204376514c4308f19152442f8604c6309f996319037654d4532db58a509076e52d0840dd946318c27f65d0e10be983431027d65c84109f19532
  | 17 => 0x4d10dd508514ca7d60d4e21bb9884310a7e62d5310e750d5110e7d6494232f918b31087756510421f64c0304427f65086309f9825210ede63d0730dbd0a510867e6014810dd945210c36c6354840dd552510c3745294440b798c50d0a7d6295030dd59251882df654c0309f1855390aed61cc821be982419027e6094b43db58c525075e53d4840d794d430436d5250a309f58e5190aee628c020cf153434c35d5308440cd952510c2ef62507309fd9643483ce538cb20bd992210873c5410930dd591518833c54905209f18d51d0a7f650c010d718a531035e6314e109f58854cc27e6510d419fd81518cb7560145329fd95210c2f561103209f181544cabe64cc740db94a219036f42946429f59730082766194242db149425035d6154c40db94b428427e60d4d429f594438867d61943439f18151d0fcf634c8329f593514ca7f6454031de5405090a7e6494c329f990540c2ee628c621bd5865050a7d654c640be58021c836f65548409f5805150b744314542ebd914210ade63144209fd85548ca7e63151209f983540427e60150309f18953043ad4210b41b718143cc3ad4210a329fd96300437965840109f595420c2f561d0841dbd95520c27f6550820bd58442c43756114e10f9d854210af664cc4219f99053c435d538c4219f595430867f65504419f594424433d5415030bb98a504c76d62951219f99743c86f66115032cf151434c27c60544429fd9743c427f6454231bd987438c6f764c8510d758c548836e52cc831dd951510c36e52908209f195219025c63549109718d544827c65cc940d794f328867f61551329758c540827e65d0931bd584308427e6195320bd18131442de6310730d754c300839f6550c43d7d4e53842fb65440109f995325075d5350e10ddd5151883766054430db0ca510867e61d4142bdd854210b776314532e750c430c67e6095021b718d41cc6f76248421cf552310c33e5410832db94a420427e6194a439f99632043795014042dd58d51103776154d20f9d4b41507766414532bb58332886bd65d0240d7d4e53102f561140439f98a510c3745194132cf953430435f5394e42ddd46515027c62546439f987548c27d64d4910bbd92204827f61551309f19531903775150540dd996414427d65cc740bb185324827e658cb10fc181314427c6590930f354e32c835e63d5332cf552400c27e6115332bb98850d079d4354043ded425010a7f6454830d794c320873e54d0420bd98021c433c54109109f993520427b65480209f597424c27c6550d329f994214c36e52885109f197430827c6155130bdd8540442df6354540f998620482ef6250e32de54050cca7f6590420bb98b43c827e6590930cf151408c33e6415330f658243cc2ed6210120cf95140c436c5214131db99421482ed644cb20af997435027
  | 18 => 0xbdd85434c6df654c431dd980514cafb6050d40ddd89510c2f661cc3109f98e518827d6394740ddd465150e7c6014d109fd9541086ec614c832db988548cb6d520c840ddd45214835e6314810de540504ca7c65d09319f196438437551c8630bd58443c427d60d5331dd58754c87d8404c030cfd91544cb6e5290610af5924310eef6250630b758c40c82f56110c319f18453442e66188120dd193514ca7d6095120bd98443c42de6315010db54951102f7614c920f9105210873d54152209f595434427d6414f10bb58a300833d53d0040af590315027c654c6209fd9432086ef624c120b798c501067d6550f10dbd4a52c43e760484219f988540436e5308520f34c832cc7743054430d714f434827c6254443af99050ccb6e528c8109f18d54c867d65cc640be580418c3e521084109f195404c2ed62103309f98b53c427e63151109b1895110e6e6215010dd98a51102f564c8710dd50c514ca7c6154f409f98a508c6f76150930d794c3084375510c4309f592528c27c6510c209f195424877743145329b98a508c67d6115332db948410c27c6154032bb98841086ef6388720bb588304836e6494a10be18143c82de63101109fd81520c75e53504409fd9531902ed62d4640dbd4a505067d6394820dbd4f200827e6195132dd94421c82f76154b30cfd52548cae5610c8219f993514c37565c4010dd945408827d61152309f18554cc2f5610c821d798c54ccaf66115230db948218c37754d4532db94b320c2f461481109fd8152d0e7e6294743dd98654c427d65d0c10dbd53524c76c6494a10cf55042c82f4614c930ddd4e511033d53d0240db94a41102ed610ca21d718253102fa600c820be58053086de63140219f18d50c867f6054f429f19152c427d62d4143db148214c3e44348421dd544515027f62553309f9845250e7d65104309f19541486f9608c5309f98f54c867f6254743bb98b41486ee62143439d58754ccaef654cb20be18132d033f5495332bd58430c427d6014d21af5974390f6d6510821de980540c39d4310c30bd987324867e6494620dbd4832507b54110621bd18542ccaee620c0109f98f52506f561141439fd94420835c5450d30d714d304827c6155220bb1894350b3c5450531dbd4a5250eec6250430db54e528427d61141438f59053086f66194d42d7d4e534827e658c941dd54641882dd6490c439f98254c86ed62cc120db549400c27f6550c43afd8d4310e7d63d52219f59252cc2bc6454530bdd8532503e942c8120dd14c5150b9d43944439f19531502fa6008640eb952520c36c4394830bbd9021c825f6550c43b758c41cc35e53c84409f584535036d5210a10a7d954310e7d63952209f99741c833d54904219f98251d0af46150810bbd8951cc23c6454d209f596311027e65d0e219f594410833c645
  | 19 => 0x2324c36d52cc030dbd0c52507754154041bd185404437965c42109f98e50042ee6210720bd586200427f65c8430bb588530436e5494830d794d30c435f5394f41bdd8532cc27d6414b10dd544418835c5390d219f586534435d538c2209f995424436d520cb309f597215027e6295131de54050d07bb6450040bd58742c425d6315210cf55342886ee620c210bd185434c75d5390c10f694e401027f60551109f5825110b7762d4542dbd0d528436d5208630cf550410867d6095121db10e52103d4614c8329f59542443e66348421be582425037661d5231d7d8d544833e5490f31d7181531027f6550910eb508424cb775294440d714d4350b6f52109319f59631042ec624c320dd989510c37751cc540bdd85420827d6494231f554f31c877651c8440fa087204827c6508530d7951434c27d658c8419f99441482f5650c421bd18a104436d43149419f99442486ed62cc7219f997325071d53500409f984540c79e544c030f694e300c2f46150a10cfd51404827e65cc940dd10d518836d5288440bd5845090f6c54149319f990524c2ed62143439f597428c2bc6454520dd94431cc3ae6410a219f181548cb5d5310f429f181534875c5390d409f98f5150b75510c730d754f401027e6494f10bdd85438c7746154b40b798c531036d4354a109f980548c67e60951219f58b504c73d5410230db14821503755114520cf586540c27d65d0a10dd54421902ed62d0720cf150414827e63948209f195324427e62946409f592520877754d07219f19153c427d6094910db549308427d6594c20cf189540c27c63551109f191508876c5250941db95242c827f6354341dd18553482ed62102309f196324427d6414f21edd0941106df654c832db58b548827c6154043de5405010e6c6254730cf950420c2f560107219f58254442ef648cb20dd545418c27e65d0b309f19743c427e6394640bd984308827f658ca10cf950408c3e65208710b718d414c7745308510f958742887e751885219f995438867e60d4d219f195414c6ec6250c20d594d511033f64553109fd95430cb7454c86219fd9621d035f534c920bd9945150afa60104409f59251c827c6254c41bd984430c6bc644c440bb58e21c836d5250a10bbd89434ca7f65508329f18951cc27e6494732bed81218833c5410d209fd95300c3764394440d794e421027e65d0f20cfd52414c27d61943429f58653d02f561cc310dd552518827f650c640db94a32082f66508510be982328c2ef6488720ddd0f5150b7551d00409f196438867d6590030f9108214436f64d4931bb580428867d6094742bd18532082df63506309f195314427e6315210f9cc9210873d5448430cfd91544c27c650ca10b758f52102f661881209f18d501076e6394a10fa949200827f62544309f18d51d02f965c4210
  | 20 => 0x42f4614cb20af19121102f461508309f58f504867e65d01109f98253d0a7e650c510db54d521036d5208610e750f40cc2ee62d5210b918532c827f6254043bd98a41442f46150831bd987528c37a538c030bd9865050b5e53cca20b758c424c35f5394f409fd94410436d5288430ded9520082de6315220db94b328427e64947309f99632d027f650cb419f99742c42ec624c520cfd52544c27e650c910cf95141cc67d61150309f98a5190f6d528c030db94932042f56115030d7d53300c33e5450c309f197414c27f6054f219f984524c2fa6010e20bb18940c837565c8710bb58a43cca7f6590c10eb508429027f6154e40ed950410867c6154b43bd18542c433e5490631cf951300c27e65d0941ddd4d511027d65486309f58251d0f6e64d4931bd98642c86bd6414c10bb98853042f7644c710bd98321c431c5450f30bd583310876e52ccb30dd547210837654946209f98453c827e650ca409fd9632d037b6054d20dd144504cb7642944409f58654487743294620db14e214827e6015131db94841843755114630bdd95310c67f64547209f19150087e55108720ba982214827e60d4542f6cc5300c2f7614c832d794c43d027f6590e20d754c521037651cc2209f19440043e521940219f597420427d6214d40d7d4e4350be732d4532bd587431067d65cc720dd58652442f66114c40bed81318437752944309f98253d077451d0520dbd4a529037661d5310dbd4b204437451c85409f58e52d036e62152109f98f548835e538c8409f594215033e54508309f993524c35d530cb219f997410c26e62951319f59631883e52108610db98052507ac5290541cf550408836e52cc8409f995424c6ec6250420db189540867d6195130b718d525027d650c910cf952400827d6414931be98031043d86050d309f982528c76d52d08409f98c52c427f6454a10afd9543d03af6450b20dbd4a524c67e6494010db548320c27f6154042bb193210877664d4532bb98b40c836c4394a10d794c32d076d5208210bb98840042f561d0831dd587540c27e6508430cf99054882fa60cc5109f99250cc67d6214d10db14b21442f561d4b43bb98a43cca5d6315021f998442086bd6490040db948411027f6454321d7d4e314835e5390c30bd185438c6f661101109f19632c43745150540ddcc951883765150440cf153414c7745254440bb98f21886dd63d0b32bed8132d035f5390d21ae181435027d654c7409f980544877663944409fd9643442bf644c8409f18553c82ec624c540f354b300c3b761508429f597321075e530c621be583324827d62952319f592530c67c654c4409f189544436e5490920fc087104426c6255110cf15141486fa60d0b409fd95421076e52d44309f58a544837754c4010af590308827461551209f986540caec6250c21be58
  | 21 => 0x6414c109f997311033e6395030db985520c2ef624c4209f99640482f561d0f10dd547211027e6494430ddd0b514cb3c54d0932bdd85544c3755344010cf950408823f6550040bb990328867d6294e40af191534827f6355021db548524427e65509309f9865090a7d6014931d554c31086f96010e209f995430827e650ca10d759643cc36e6054840d754e431027d64145209f596420867c6255331bed81438c2de6310b30bb189414c2f662841109f189509067d6214540cf50d5010ebf6454d20bd58831c86e662841109f594410876d650ca219fd9443042f9600ca10cf98d540c2f9608c8209e58054086f960d0a209f582531067f64548319fd954348376518c220db54b420c35d63152309fd8d540427d65d0d109fd95329027e6510d20dd15021442ef6550842fa18142482f76154d429fd8d501067e6494821f9484210c2f9600c540f910b310873c54d0130ded4250d0b9c5450d309fd96320436d52149309f195428c77b5094131af59332503775194640d7d8d544ca7d6014943be583438c27e65d0d32dd5445110abe640c020f90c5210875d538c7109f58e5110a7c65d09109f98c515027d6548440bd58620842ed65cca329f98b53507f25190040bd1855050ef76150b20dbd0f524c6ee6008520f554e31c427c650c520f994b108427e6195020d798c53c82ee62152309f995414837551145309d984530837643544409f19542cc6f461551309f596420c27e6394421edd91411067e6494b31bd59731087776294440f34c8324c67c6354442db98a53c835d5390e40dd550410867d658ca109f996424caed6214331d794f311027d6394a10bb1895150e7d63141429f997424437453c85219fd9153486f7614ca21bb58a418877651504209f994400427e6494032be582419027d6588010db94b20c427f654c431bd98451103755110740bd987421067d6510f20dd584540836d52cc831ddd855210f5e53d0440dd946218827d6194c42b7d8d40cc27f6590b10cf953430c35f530c9409fd9541c836e6354840db94821c437454c8521f948421c436d6215221d754f4310aee6284010f998421482f66190941cf95242cc67f6154b409fd8d51c833e54108219f59532d076e520c430bb988520c2dc6354520af993520c2ee620c310be58332cc33e5450b32cf553520c2f76150821cf990540873d5410b21b75834390e7e6114143dd147314837651c8420bbd89314c2fa600cb209d984530436f5288530be982214836f6194840dbd49504c75d5314f20dd545410836e524c8209fd9521086ee62cc521bbd89544c27d6550420cfd50414c3e442d0421b798e544879d4310c429f98a53d06fb6054543cf981540c2ef6254143f9949510c27e65cc5409f98653d02f7614ca30b718d544836f51085209f592510827f65ccb10af990520
  | 22 => 0x730dd18151102ec624c630cf55340cc27c6054a43dd145504ca5e6315021dd947311027d6294630dd54430883f2514c030b798f424cb764254440cf951430867f650c820dd94b41906f76150b40b758c404427f6550c40dd544318827d6195131bb588510c35d5350440e79514310ef76484110cf952408c27c6550b10be980424c2fa600c7109f59352843cf534c920b758f420c67d6114c20ee500408827f65d0630be98053086f661148439f98e54886f9608cb20cf5974390f3f6455210dbd954210b3c54d01109f98454cc2ee6210310cf95341cc77764946209f984540837a6015220be181318427d6494e20de9835384377530c7219f987524c27d6548740dd94a210876d6194840be5805110e7e64d4d209e181544caed6210f209fd8552d0f77530c421cfd0d5010f7451d41329fd815390b5d5350c209f98252107d9314c030db50f524c6dd638c0309f594218c27d6494b31be181321036e6094a10bbd89310867e62d4e10dd109510c25d63951219f586548ca5e6315220bb594328867f6510b31d7d4e539067c6215120dd991511027f65487409f19643c86fa6014c42bb58b540c33e54106319f586540c35c6154c409f194410875e534c840bdd8f21c427e65c87409fd95300427d6314121bd58620c42f56110110b798e408c36c5394a10bb58850d073d54d08319f181521066e62d4e10ded42500875c538c940dd19541442f66190421f5545300c36f5394a10ddd8e518839d4310d30db19252102f56114830f34c8324867f6154332d754f211037653087109f983540867d65885409f996215027d6314941be58053106f4614cb40db59432086ec6250720cf552418867e6394740af990520c27d6094f21bdd8c21c427d6590c219f99353842ef6250621f58cb514ca3d6595030cd551510c3b65490710bd58450d0b6e6294010dbcca510867e65905109f997314876d5348020f9951210879d4310d42bd99331c867d64944309f596430835d534c320d7d8d530436f61948309f98054c867f6055232bb189514c27f6254640db996324833f5450521bb98850cc76d52c8210bb58b51103774294620bb98843c83756114143cf950210c27f6154840dd98754086dd63d03309fd815110f5d53d48409bd9521086ed62d0c42bdd8121086e760484219f58f515036f52509319f592534436e21d41219f98f54043ac6250441dbd4a41507ad4210921db18953442ec624c7309b189544c39f5350d409f980540867f6550d10dbd4b424c2ee6210210d754c53903d9324c030ddd8552d03e76150920cf15341487bb6050d40bdd855250e7c6255130dd8ca511027f6354b10ddd49511027d63145209f99432042f9600c5209f59731883e76548421bb58a21087555394440bd587528c36f52509409f58a51cc2f76154143bd584538833e
  | 23 => 0xfd97219033d5410621f34c832882ef624c7209f99053c867c6550730e750c43086f661d0b10bd58740c427e61d5320d794c43106ec62507409fd8154cc76c52d09319f595304427e65105219f994414c33f5410d10afd91329035e53d44409f58e51882ee62d0e32d710153103766514532bb58c21c827d6094643dd50d510c27e6115220d7d86531036e54149319d584538827d6015232eb94940102746154b30db10f525067d61d49409f1815190f5e5350e10dd545300c35d5390e10be580410435d5310c419f98b548c6f6628c5109f58954083e92008110dd984540c3e762d04219fd9721d02ed62d0120d794c43d067d6550430db991520c36d64d49319f593514c2be6414831be5805310abd64144329f997214c3b65490441ddd52518836d52d02109f994544c76f654c832bb58b43086f46155120ddd92510c27f6255331d794e40102f6608c5109f587544c27d64d4f21be98042083b9544c030d794e430437561150329f18d521075e53cc841d794e311036f6254a10bd98752d0ebe64143319fd8153d07cf528c932d714f31486f561143439f580514caee62140319f997204427e62953309f993524c76e520c6109f18d54c83ce53cca21dd94c5150abe64d4b31af99032d027d6315321af99030c827d6550f21bb988400c3555354440e7d894310f754254430d7d8553103ad4210a209f58653903756454430dd94a510c2de6310832d754c32d06be6494d21dd144214c27d6494c10d7d4f314873f54d0920bd984539036652944309f98650ccb756114e209f185548ca7f6154a409f19532902fb6050640bb59732086ed62d0721bd185525037654c8621afd91211027e6494f21cf951438427f65cca40dd58754cc67e6590e21d798c54042f9600c730f9987428867e61d5130d75974390f5d5390840d750d5010efa600c430dd14731502be640c540db94b108427d6494031d754c53042ed6214c419f19442c42f66190e419798c540827e65c8510af191319033f6550c43db948311035e534c4409dd9510043eb2148020bb18951503b54110410e750c430827c6055121bd98d21087e421c81109f996329075c6494c40d794c308839f6450f309f990538835e534c320cf55042cc75e6254c409fd9632087776154b309f19531082e663484219f58b548433e5410b21d754c534827f6154a309f595428c27e63947429f195418826d62d52109f994310867d6114940be580320c2ef6250e209f980524c67e63150109f98e51c82ed6210520bb189318877651d04409f588504c73e54907109f194434427e6314a109f984544cb3f54d0d21db949510c2ed6214031be982318c37763944409f99743086ed62144439f983544c67f658c020d7d954310e7e60150109f18954842de6390631db54a411035f654c030dd58a510c2dd63d0
  | 24 => 0x548435d63951319f1855090e7e61149409f988548435f530c910db95252842f661d0831bb18f218876e5288020ddd805150b3d5410010b758c501073d5490431bb583428873e64150329fd9531c83b54110610dbcc8514cb6e5210830d794d211027c6014910d754f411027e62943419f19532d027c6454630db18e520c27d658c8219f59654087d651cc030f9189411067e65cc9319f584544c27e64d4131bd588410867e6014941bd584325073e5150441be983421037451485209fd95329067d6194a439f994424c27f654c831cf989540c36e5288010b958841087765108410dd180514cbae5490b20bb588418876e52144409f59641086fb6048520dd90c514ca6e6294241dd544510cb765490710bb588400427c62543439f586544427c6154f429f58854c435c5490d30dbd4b21443db508c1309fd89518c2ed600c821db54b321027e654ca10bd584300836f6254d10bd1854210b796014c219f98f54842f561148409f986528c3776154d21b91854210a7e65d0831bd987204427f64546209f58f548827c6355020bd58432443ea6090b20ddd445050a7f654c1109f586500ca7e6394020db98d528427e64150219f98c54887e461d08219f997219027f6550630dd946418837551d0440cf550544427e6495120dbd4b325075f53cc110ddd8951102e56110821db584524c67f65cc810bb18941086ed6110a219798e54486de6390a32bd580310867e60145329f98a509077453c85109fd8d509067c6550d10cf552408833e6155030bed8132102bd6414810db588534836d5210440cfd51434c77440544409f594325067f6355030ddd8c5150a7d6294c419fd95420c73f5495221cf941401027e6414532db15221c83763254440dd945400c37663544309f99053083765190640f90ca210876d5214843db9915284375518c630dbd4a52d027c6154b40d754f32107ce5394840db10d521027f65c8730bdd8532907eb6050920db948308427c6154a43f9584320867d6015331bb993328863f65508429f996328427c6548740dbd4821502f5650c7219fd8d54082f661d4a43fc546401027b654c0308f59053083e74288421db185520c33f54d05219f185521036f5314941bdd85504caf96010a309f99432d03774354430cf552520c36d5290430dd4ca511027f6055221f654e401036d6215230dbd4b20042bd64144309f58f54c86bd64140319fd9742c427e61d4c209f595320427f6355221dd545318c32d5494830bbd8941043e4624c5109f58d540c27f6550b30bd59021c437651c87209f996430867e6395210bb988510c27c6054f41db94e214867f6588410cf95343843b76450710bd58432c86ef6250441cf55340c827d65cc010cf552408c36f6394a10b798f428c67f65ccb409f58153042ed6214043dbd4a520435e63150309
  | 25 => 0x6fa6090c30bd18532506ee62d0d32dd10e518827d6315320be58331cc3754214542de980530827f6510a319f994544c36d53149419f594418c36d5214931bd9845010b5d53cca209f59741cc37652c4010cf550544867c65cc9419fd9741c82f46154132f9cc421c835c538c910d754c53906f66114143f64c0308836d5210430f9104214827d65cc840cfd5241482fa6090540db54b32cc33f61950309f990530867d6590d10bd58e104436e6414931dd550514ca7f6154f42af19153442f4614c910db588548439d54cc0309f18950d067d64d4c10d798553102df6350932bb58850106df6550f309f594438827e6295010be98042c82ee62d0520cf99054c83ae5454830bd59741c86f6610ca41af590304827f6155032bd584539039c5450f30cf18a540c27d6414c109fd91524435d6315232d714e315027d6588730dd14e511027f65cc6209f19153c827d6590b30dd55110042f560d0421c7551300c36c4354830d794c32083755150640b758e320cae765484219f5825390b6c5254141d754f31102ed60c8621be580540c6f76548421bb588540427d6494c20fcc8710442ef62506109f596430c27e654c910dbd4a5290f3d5490f309f194320427c6114910de540505076f6550b20bb58843c867c6454032db94e21c82ed62d4f419fd96430ca7f6154e429fd9151cca7e6014f21e750c43c827d65d04319f195214c33c54909309fd85508cb6d6215332d754d439067f654c420d754d4390a7e64d4910cf55342ccb7452c4010ddd46511027e63141419f98f54082f561cca21d7d4d314867c65d0f21f958a10443746154841af59050cc77460546209fd9541486ed6390920bbd8931d033e5410010f994a511027f6055321af5924210be742d45429fd89544cb6f63d49419f99721483e44248421be1815150e7e6510a319f19150cca7d6395132f9151210867d62944439fd94418835d538c8409f58f54486fa600c910dd544210c2f561108219f59421cc27c6054a41cf952430caf4614cb219f597420865f6355120af99332d027e6194b40dd586534435d65cca329f5964348376518c4409f19153087e741087209f58b544427f6255210bb189535037643d4542d714d324877651900409f582540873f65500409f194424c67f65d0c10dd547219037551cc440cf95041c427c6454e209f99721cc27d6414d10cf551400c35f534c921cfd5254cc2ed62d0f20bb185424827e60d53219fd95315027d6494b10db98a508c776514c440be181218433e54d0030f3949300c2f6618c421cf15243442bc6448640ded81544c35f6355130b758c54042f5600c721cf552418c76e5250831db94a428c35d534c810ddd4651cc27e650c941db94e528427e65904309f596300427c6155132bbd8940c827d60d4c21bd98430482ef62545309b988
  | 26 => 0x490441d798f54cc76f654cb20f950d210875c6254c40bbd89410c2be64087409f98e50086fb6050c10ddd4d518839f5350f40eb55342886f66114032bb58b531027e6590d309fd8153086f96088620bed81314c27e61152309f5885050efa6008540bbd8c21483745414532f914b314c67e61d4f20db988540ca7e6510c21dd185540867d6414131fa98221482ef6250431ded81534426d6214143db54852d0f6e52108409f58a51042ee620c421de58053c827f6054810dd54451d027f6054742dd94531082ed61d0a21ee952300c27d65cc810cf182540c2f4614c840bb98843c867c6550b30bb988531076d5290a30d794c31087e52108530dd90b5150be6620c421db94e324827e62148109f994324c37762145329f98652cc27e65cc930bbd8e204836f4394830d754e439079d4310f40dd0ca510c33e54d0831db54b218427f6550e209f181548867d62953109f59642843d5310c630d714f314437654905109f19152cc27d6115330cf15242443744254620f54c4318876d6394a10f5d4d314427d6294031db98853c836e62d5320cf550418c6f5610c320af99032507e54248421b798c410c76d5214a31af59241107773294620b798c40883756195121bb58b31487f160c8510ddd0c5150a7d6588530db54b421067d650c940bd984414437651106209f58c52842ef62507109f594300835e6314f10bb1894390be662d0721dd4c9511036e528ca30de58353c427e6588740bb9885110fe462507109f994434c77652cc631cf550540867d6494032cf5504208776518c4209fd85548837960951309f997210c36e63d49419f59531102ee62141439f195438432d5410821db54852c427f6510b10bb597218873c63550309f594329076c528c930cf99054cc67e6295110db50e520c2f76150941bd98620042f960107109f99253c827661d50309f997438433d5410c31bb588540c6be60d0f409f596218c3746294440bdd85424427c6454720db949300c2776154843bb988531036c5290531bd58331c877553d4542be980418836f6014941fa90b204827c6155030d714e4350af66190010dbd89524427d6314910ed55041087754314542b7d8d524427d6510730d7952434c36d6354a10bb588408436e4354a10dd10f514cb7651cc0309f994430433e64151109f5865448375518c420db98b530833c5450510db90c525076d52cc830fc507104427e6294041dd183514ca7c6508010bdd85320427c6454a31d7d4e530427c6590c21dd58753c876c5290940db58b54cca7f654ca10cfd5254082f7614c8419f990520436e5250830f9d4d21086f46150930dd544518cb75514c420d714d31486ed620c010d754e31042df6450c43dbd8c525073e54902209f5865010f6d65d0a21b758c548827f6590e219fd8950d0f6d5214943de5405088
  | 27 => 0x41cf552300c27e6550c21ddc87504876e5250840af59331d02f66188210d754e311037751d4142dd14d51102f56190a419f986500ca7f65d0620cfd52540c35d5390040cfd50424c27e650c7209f99742043da5350040dd593514ca7f6454f218f590538427e63942429f58b54c43e66208510f90c841086fa6010d20af593329067e6094b31cf55054cc27c6054b31db948210c34d530c821b7592434c27e65ccb40dd15141442f46154b40db54b510c33e6415332af590325025d6315220bd98643c436e5250a41db54942042f66190210dd509518835d530c821dd584548435d530c2209fd9641cc3766354440be982310436e43d4931bdd85328427d658c830bd987328877652104219f98c540c67e65109319f993504cb3f54d0d31bd98e21087ea32c81209fd9543843e65254440bb588400c37632145329f58b540427e6590c20db14a42506ee64c86219f98a518c2f76350710dd982510c2fa6010f30b758c21cc36e5454830bd594410867e60d4941cfd51408c37551900409f98c5050b5d54cc030db54a328c36e5210a10db54a428427e6510a10d754d311027f65104319f99251c835d53cc6109fd95325067e6494431dd546311027d6194232bb58830843e55448421db591520c27d6294643f9484210837464145329f594210c3b46150842dbd80524c76c62551319f194215033f6455230dbd90524c67d65d0c209f185508ca7c6510c21bbd895110e7e62151309f593504cbf36050510bb59242483756294440db504525076d520c440dbd53200833e5490842db148505067c60553329f58e5010b3f5410d20dd987538876d54d4931db59152843795014321dd50f5150a7e6494632cf550320c27d6590c41d794c4310b7454c85109f18954c427e650cb10cf952420ca7d65ccb40bb588540c27e6194232dd946210c27d62141419f993538876e520cb419f58a548433c5450920ddd85544827e63948419f9865210f5f6354910afd91219033e5490c308f992534875e538c0209f98a54cc776518c030be583424827f6355320cb15142482f76150840bd58432cc6f86050510d754d32102ee6190842d794e32c867c6548110bb18941442fa6010b409f59642cc67d60d5131dd545311035f5394e20f9d0d210875e6314c10cf553300c2df6350430ddd8b514cb745408710f398c320867c64544309e980540867f6055121db548528c2ed62103109fd85500cb7a6014c21bb18941c87ea608cb20db14921442f461508209f98c530867f6550b31f698243cc36f52948439f59641482ee620c020db54b42d033f54952309f59052442ed6284110db549418427e60d5032dbd91520c37b6055131d754c5310a7f65d0c219f584544ca7d64d4931b758c410c7765148440e71814310f746454430db98a544c76e528c8419f984540cb3e5
  | 28 => 0x58652442f96010f309f58e501075d5314f21cf95243cca7d6014d41b798f404c36e524c8419f996410836d528ca10bd18552cc27f6510830bd587430876d520c4309f58654cc33d54d0830bdd8542cc76d62d5210d754e430836e52d0b41db0c1520c27d654c620d798c534836f5250531bd18542c827f65cc910dd991510c36c43149319f596418827e60d4532cf952420c36d52080109f595304827f6590831cf55242c837653c8521d754c43d07755148440f90c4214827d6590e10db50e52843e521140219f997424c2ef624c510d714d314439d6150c43bb58a4350b7451c85309fd8553c836c53887209f583540867f6254241cf953210c27c654c941db949308427d6114132e794f40102f56114c20de58054c427e650c9209fd94420cb5e534c8109f58e510836f43948409f195211036e62d4f20bb98b518c2f56390510bdd8532c436d61d4941bed81415027d65900209f1815390b3e53d0f40dd992518836d4394840dd94d518827d61d5120dbd4c320876d5214b419f996428c36f6254740bbd8931c877751885209f588538436d5454a10bb59021483776454620d798e54cc27e650c4209f98653082f4614cb319f596320427c6254f40f9cca21086f86050e409f994420c36e5250a109f590504867f6254041bb58a200837a5490040ddd0d518827d6590c31de54050106df6354940dd952411067d6590b109f99742842ed620c3109f59542c43e42148310be983418437751945429fd94430873e54503309fd89539067d6194d209fd81540ca7d654cb10ddd8a510c3b940101209f195434c67f6454c20ed947401035d53d0f42bb9885090ff260c8510cfd9154c83776154b419798c540c2be640c110af99032d07ad52500409f990534836f42145429f982544c6f565107219f194420427f6454a30cf951410c35e5350e20cf94d43d02f56184010ddd0a510c27e6510910bd986430c6ee62cc520f314a314c67f63551319f997418833f6455121d758e544c27f6550821ded4250ccaf564904419f992520837565d0721cf553430867f6055010cfd9541106f561c8310d79514310e7f6054d209f59421d02ef62545439fd96200436f6414941d7d4e53c42be6414c20cfd5041483766094620de980540827f6154b30bb18931043795014243d754f511027e60d5121cf153414427d658cb10be982210435d5314d42dd50d51882ee620c7209d984540c27d65d0f21de540508c67e6508440bd98440882f4614cb419fd815190bcd53948409fd95200436d6154a10ddd90514ca7d6510030f9991210876d52102109f982540ca7d6494c21bd98454082f56194242cf552210c27d6394242d794f31c8775514c220d754c43d036c52105319f59443442fb6248020dd94f21c42ee6290d429f99732102dd63d0930cf550410c76f52d41
  | 29 => 0x34437965cc2309fd96310827e6014c20db54852503e521540219f99743482f66090510fc485100427d6510020d7d4f30482766115010dd941100436e62d52329f996318827c6354a41bb59621c837663546209dd8553483e653484219f596300835e53d0f40fa4cb20483765110740bd1855250f7661141439fd97410c27d6588430fc546300c2f56088421bb189534427d61152209f59741086ef6250e42f5905310c6f66114c42dd4c8514cb76510c220ddd4821c433f5495132db98b530867c6354420bb986214827f6254c109f597400827d6494f10d754f328867f654c8309f987544836d5208410bbd89311027c6550830de98052842ee62150319f994410c67e6590921dd547400c27e650cb41db54b31842dd63d47429f59743842f561d53329f18d54086ec624c610fc945401027e6548540f954a51102f563c8710dd14d314427e61d4810bb1895110e7e6510720ee50040cc33c61950309fd97428437661d4f10af590500caee6290c219f58b548c6ef6550b209f594314827f6154d21bed8143c427f6550c429f18154cc77761551329f98e52d039d4310f219f995430425d6314810db94820843e52108720d754d31843e46150920dd544218827d64d4d209f592520436c4294421af593321067d6590a31d758c54043e741c8421be580310427f650c841bd59131c437950141429f987540427e6094643ed90b5150a7c65cc5209f99432906ec6254730bd1855350aec6254d41fa181324833e54900109f987538827d6414810d794e320cb9d43d48439f197324423e6414c109fd9421d027f63551109f997329073e54148309b588538427e6214e10cfd53434c27e6588630cf950400c27f654c832db94d324827e6550d21e79524310e7f61548309fd95321066e6214e10bb98830c826f654c832bb98a410877663946209f58f514827f6454c10fa58a100427f6550c419f18d508867f63542429f19440082fa60086309f9945444376510c620fa58242c827d6315010f954720883e662cc721bd98442106f4624c510db14b415067d60d45439fd9541042dd65d0e43de540504c67d6014c219fd8d544875d5348440dbd4a424c67c654c940ddd5041087795014232cf55043ccabd64d4b31be181314c36f6254730db949328c2e4624c5109f98253c86f4614c110ddd4651d0e7e6015031bb988404c27c6550d219fd9732843e74210421bd586200827e61d4c21dbd0e52843e55254430bdd85320c6f66188310bb98242c836d5254430db98b540c36c528c941f9548214427c6154a30db54b41842f7614c8309f58e500833e54904319fd9441cc35c63551109f592510879f6450c43cf552400427e6294e41bb988400836d52144409f596414c27e60145429f59641c835e43540439fd9153843ea6008720bb58a31086f9600c8209f
  | 30 => 0x7d6094e419fd95310c3e52108740be98042442ec624c431bb98642c827f6454f20bb58a400833e5450610d714e31482f5618c821db587524c67f654c6209f58753c82ee6290f20bd59231c436c6094a10db988540c37651906309fd9152c437551c8430bd185328c7765308510bd98021442bc6454131dd945410436f52949409f98453086f4614ca40bb98b30c82dd63102209f594319027d6294e419fd94321033e5410431db55320883f131c41109f992510436e52d0030dd547208833e5410c31ed547401037561152309f994434c2f96010a109f595328423e6414e109f196325076f52d05319f195420c67e62141419f98a524436e5450842cf55141cc67e61952329f19541c827e65cc1109f992520427f654cb40bd584424436c5488520b718d50506dc6355110cf951438c775518c640d754c53082de6590d30cf9524208776520c421bb18931c436f528c931af99050086ec6250440b798e400c2df6355120ddd4651d0a7d62951309f98853502f96010d20dbd85521027e6414f20bb588310876f52109419fd91500867c61550209f195320439d4310e42f90c8310867d65d0620bd587529037651904309fd9431043775154142bd984320c75e63d50329fd9432d033d5490b21ded4250506ec6250731bed8141cc27d6394821b718d418c3e92148020be58052106ec6250d32bd185324c67c6254e109f99532c436d5248310bd584408837651c8410d7982531027d65505319f98f520435c534c920d794e438427561d50309f58c525027c6254c40de58252442f562107219fd8550d0f4c534c9209f58053c86dd63148419f99443c427d61d4e209f189540c67e64942329f58854842f561cc841af99053087f1608c710dbd8f524c67f6054e41cf953410c33f6455032dd545319037643544309f994410c33c6395030be597308c27c658c540db14920042f960cc830dbd4a42502f46150b40bed8d300c33e6295030cf952320c33e6415310cf59741906ef644cb209fd94434435f5310d10bed8153506f76384110af99051083e43208710bdd85424cb6e5250a40be98032902f6610cb10db94821842f56110b21e750c43442ee6215010d7586531037565cc4219f597410836c52941319f99632483e5620c4219f194420ca7e6194b43bb18132483e731c84219fd95430867d658c740bdd8552d027e6094732be983438c36d524ca30db588540427d6294640e750c435067d6550110bb58a430876d52148109f997435033d5450721bb191210879d6250c439f1855090b6e520cb319f59654082e46150b209f98a53d03776550441d794d31c86f96008640d7d4c315037732d4532be98231c427e6294440d794e310427e6494021de5974090374538c510de94a20082ee608cb20bb98f420867f65100309f99443c86ee62140419f5935
  | 31 => 0x509419f98b540c6f6618c010cfd51414c73e54102109f98f540c3e952c4210bd984434435e53d0c41be982420833e54d0c40dd185530867e65d06309fd96321027e63d45409f584548caf561d4c40f594e31c427e658c8419f594400437565d06419f982548cb796014b10bb583320867e6194f209f98c540caf560cc631d754e32c83764254430e750c5210f5d538c820d7d8d53882dc6050d30cf55142887d7324c431bdd9021c436d54d08219f996414c33c54d0120bd593214436d5250831cb551520c27e654c9409fd9641043e74208710dbd84525073e5410b20d754c531027c65487309f980530876d524c610fc545401027d6394b41be181328827c62540439f99732043eb6248020ed50d411067f6354840cf550420827d61940109f986529027d6595031edd0d411076e62141439f988504c6746154d20ddd91510c3bb42500409f5845350b3d5450c219fd95404427f6510831b758c42cc67d6550932bd584434427e63944409f585540437751105309f59541cc3d5310c410bd99121087e66048421d794d401027d61d53309fd95404836e52d0b319f59632d06ec624c430bb98a320867d6294d219f19631483d9300c120b798f51d0b6e52c8210fad81324836f5248510db947200835d63d52309f99631442ed62951319b58854843f220440109f99731c82ec6348421e750f5010f7960d4f20dd586534875e5394440d7d8d53082de6310530dd545410c27c65cca10dbd4b314c7796015320ddd465190af86050a409fd96438436d5208640bb58a43c82fa60d0a20bed8132882de63d4440bd584304436e5208510bdd85429027d6295131f5d8d31442e664484219f995420436e54885219f586548827d6590810bd18141c433e5450c40db189544c27d61953209fd94400837a60150319fd94310867f6355130cf5974290a7c65505309f997428c2f76150a31bb58b5190f5d53cc3109f58054ccaee62900209fd94210c33d54904309f580544c73f5450d30fc98241c42f76150931db14932507e7614cb209f594414c35e5350c219f58b53c437660145429f18d52d03ce53548409f9825110e7c6154c40bb98840c827e6510030cf55242cc77551147439f9865390b755114730cfd52540867f61548109f59431502fb604c740fc8c710442f560d0721b758e54486ef6250e21bb5974290b755294430be58032c827e60d4c21dd987540436d5210840db549328427e65d0d21dd597218876552944309fd9742043d7518c5319f992544caec6250e329b58a544c67f6510c329f592520cb775194432cf950510c33e6414810dd98453c43ac54509209f994424839d4310c40be98221c42dd6310a32dbd89538876f6114931b798c214c3b542504419f58c505073f5410910bd586439067f6590d21cf953310c3775454430cf953438c6
  | 32 => 0x9fd89548c67c6354910ebd4a41506bf644c440dd987530876e52884109f59732082ef62504209dd8554482fa60108409fd95219036f5294a10db981520c2fb64500409f994214833e54d0610b7d85310c67f6510430b798243cc27d61d5332ded81544827f6054c419f19151ccb9f5450d309fd8950d067c65504309f59643c427e61150219f99741502dd6390631bb58e204827f6590f20dbd48424c27c6550c10be181535067f6454d20db590524c7da534c0309f996404c2ee618c9209fd91510c27d65d00309f992510827c65d0b10bb592214836f5294b43d914b314c75e6194c40dbd49324c6bd6494d21cf55243cc67e61d4143e750c43cc67d6315110b758c548433d54d0731cf550428cbcd524c030dd15321c42ec6250631d7d8953103e7624c710b7d8d504875d53d0c419f58e544c25c6550d30dd98653c42f56110b41cf953430867f6510f209f595204436d5210830d794e31c437643145429f99454483773294430dbd4a520c75e6054c409f597310435e5394840d754f310836d4354840d794f43d073e5490b219f18054442f761509219f994410867e6315130dd984540834e5394840bb588404c2fa6010520db149324c37551100309f592510c6ee628c2209fd95320867c64548319f997304827d6194042bb990420876d4254042db98a54c83795014331bd98740c43e452c8510db94b401027d6590910be982324c3ae5450842db50f52506f9600c430db192520c2ec6250531d754c31886de63d0530b798c404835e538cb209f59532106de6314341e79894310f3e544c830dbd0f525073e5494430dd94e511037554c4210f354d521027e60152219f194300827e6510d10be58221482f6610c010bbd89534436f6154a109f99052c43ea528c030f594c310876d5250a40be58331842746550510db151528437b5094321bb58831c836d5214b30dd944410c2bd6414831de983548c2f7654c710db19542483e751885209fd85531037451d05309f99641c827e6215120bbd8d42c839d4310f41bd58730442dd63105309f99732902ee628c421bb58a535067d63d5010ddd4f10042ef6548020dd58d518827f6254243dd587528437664546209fd91534436d65d0821be181419027e6215331db54a31843746314542cf95141c875f5350d41dd149510c36d5290210f34c8328c36c61548409f99731d027f654c440fc58620082ef6254740cf55341c867f658c410f654d40102ed6210d21f9d0831087776155121af59021d027d61d4d42ed952510c2f661cc1109f58854443746154843f3d89310c6f9600c7109f98a54c427e65d0420cf551520c27c6454910bd98442c437451141429f98c5150b744394430dd14b314c6f661143439f996434873d5450310e750c438ca7d6550a10bd58341506f96010530d754e4390b6f52
  | 33 => 0x96319033f54d0531af590500867c650c010bd98c410867f6590832bd98443d076c6254740dd98c5150a7d6590410be98242c82ee658c920f994921086ee60887209f992538876e5250430bb189438836c63d4941bd98752903775194732b798f42cc27f65908109f58c5150b5e530c840fad4220482fa6090410d7d8d53c82ef624c640de980540cafb60486109fd815310a7d65ccb109f19532907db634c030bb58b314827e61951309fd91518ca7f6255030db551200827d654ca419f580538867f6254643bd185424427f650c620dd94e31c42f46150941cf990540c27f65904219f99742cc67d62951219f18151ccaf4614ca209f58b50506f6618c2109f99252442bd6414e20ddd95518827c65d0c21bd18941106ed6010821be583310c3755314542cf94d4310eec6050920db58652842f660c85109fd97434437860551319f99252c42f7644c510bdd85534836f54948309fd97310827f6510810dd98a510c27d658c4309f980548caf56110f419fd8554043756394620dd54d518833d54d0c20bb189544c6e46250441be58a20082f761551329f191508cb746154b30ddd46518c27f62544409f59731103e4614c920bb18941486ed628c2209f996214c3e65108520d798c53887775394620bd587320c67e6214d20f9cc8410876c6194830bb988434871c5350d40bed8142903756114a10cf550430c27f62550319fd8954042f561d5220bdd8543906ee6514931bb58b438cb6d5214b40dd547410c36d5248610cf952310c33e65d0d40be18131d02ed6210020db94b210c2ee61881209f98f54c427e6295030d7d8d53c876e5290831b798c40cc27d65d04109f98c525027a6015031cf952400c27e60d5332f54c4318427c60546429f195321067e65d0130dd10b514cb7763d45329d58454083763254430ddd46504ca7d63d51209fd81544827c6355120d7d4e53086f76550710f990d210867c6454c20cf553320c37653c8621cfd5254cc76e52ccb419f596430427d6315020bd984538833f54d0130af59051083f25184010dd94d31c427f65d0420be983328837454507109fd9631087e74214542cf55143082f86050a20dd547408836f61d4941db988530867e65d0f109f994300836f43548409fd9621102dd6310931dd94540102f46150b219fd81521076d52887109f592500427c6550a309fd96420837754440109fd81544c77552087109f99741486bd640c010bd987431077b65440109fd97424436e4394830db588544827c6550f10d754d438827d63d49419fd9532c42ee6294241bd58742443e7624c431db54852506fa608c8209f597434873e544c430dd10a518827f6510c30bb18941902f561ccb109fd96428c67f6550840db94b408433d5410430bb584320877661d4e20d954821c427e650c010ddd46518cb6e528842
  | 34 => 0x442f66110330b758c5010af56190c319f993534867d60d51329f58e544c6f7614c820bbd89414c3b664104219f994534436d62d5030db1895110ef6610c310ded42500c73d6414e209f9865090eef6250720db148424c73f6454d109f58a5090e7d6494a319fd9431d027e6215110db948400c33d54d44309f98653d0aed648c920d758a531033e5250842bd986544ca7e6510d329f58c54086ef654c832ddd0e518827e64942219fd95430c67e65d0830cfd95540c35e5390e20af58e405027d6414c21e750c434c76f53cc821f958b31c867f65500309d584540cabd640c210d798f54cc2f665905109f587548c39e6150c43cf551438c73e64152219f98b504c67e6014e219f597420c27c6550d209f582528c7746254440bb98f210867d65108109fd95215033e5448430d754d310827e65cc4209f982529067d6215231ddd905150af663d0421f998a10443f160907109f196430827e6215021bd98643087e761cc821f54c4310c2f960d0d30bd58643c437643546209f595420c67c65109309f592530cbe462d0421bb986320ca7e6195220f9505210867f6510d209f597325033c54d0d32ebd89411067f6354640ddd0f514caec6254131dd952510c35e5388440dd146214833d54d0e32bed81314433d64148109f99442c42de63102309f58b5150f7543946209fd96311027e6550f21cf551420c67d61d4143dd9085150af76544010db988540427e63d4940db95221c827e65d0d429f194434835f5394e21dbd4a314c776514c2209f994204427e65c8540db8c9500cb6f43548309f18d54c427e62d4c20dbd89544c6f560cc5319f58e510875f5394f20f9484214427d6494632bed95401027c61551209f181540876c62547309f98e509076e52908309f98f528436f5414931d794c30082f46150e41af993315027c6254f419f99632102796014c21bdd8530c435d65cc631db54821102fb61440109fd8553043775194420bdd85324c33c5450d32dbd4e52103cf634cb209f5943208374514c530de980538827f6155030dd50f514ca7d6510620dd55341c867f654c421e71894310f6d5250a41db149204433d5450e32bb5885090f6e6054a109f191528c2f76150a20db50d520c2ef62504219f580544cafa6010630d994a511027d650c440eb990420877a534c0309f594430827c6550c21cf151424cb6d65c8220cf152434827d6194f42bd58632c876f6255120dd547310c2f56114c40dd50a518827f6255310db580524c79d4354843e750c434cb7762946209fd95411037542d4532be980210436d524c030e7d5143cc3766114b10dd587538835e53cc6109fd9543887755114430d7553308c2f661101209fd9541883775110520bb988304427d62153319f98354cc6f96090e40bd98430843f151c8220dd58e511036e65909209f5
  | 35 => 0x661d5221cf55242087e562104219f994325027e6114c20dd58c5150b5e5350e409f19443c427f6588730bd986508cb6c6014941d714c3250376518c4109f98e52906f8604c9209f98353c86dd6390a329f996420436e5290a41be58032442756114143cfd53424caee62d0d20d754e511036e5250440bb98840442f66114840e750e5210e7d64d4c20db182520c2bf64549309fd95430c3b55454430ded4250887d7614c832bed8143082ee6210920db94b218427d6294331bed815250edc6350330cf99053082ed620c0209f98f540867d6510832bd58450ccb76510c430af59030c427d6215230d758c548c67d658c520d798c548427c6590d219d59431086bc6050f40bd98743c427f6354442dd944219027d60952219f59642082f7648c710bd18542d067e6114c10bb18532c827d63d4142dd19251882f561881109f584544835e53d0840bd58742cc76d520cb319f195424caf763c85109f597434827e6314c20d758f548c67e62d51309f992500c7755150620de94920082f661cc831db952214836e6014931ee10d40102fa608c5309fd8154ccade63109309f5835250ede6314440bd185428cb6f60d4931bed813110376514c410cf95340c823d6414e20bb98b538427d6294041dd0ca511027f658c8209f590524c36c5314941dd54540103766115220cfd51424823c6454d109f58e54c876d5208430bdd8c21442fa6010e10ddd95510c36f54c8220f9947208839d43d4443be58021503772154221be98331cc2fb6054d429f9865010af46154d20db988530839d4310e319f594420836e62d4e109f997414c76f6255110dd4c9510c27d6315210f9581210867e650c440ddd9551103756115321bb591324827e6394810f990921087e4614c8329fd9441c82ed62103209f980540827f6550431bd984510c27f6550a31db4c9500cbe754484219f994410827d65d0520d758f548cb3d5410c32db90e528436e62d4f21bdd85430427e61d4c10db180524c67d6494e21dd94d511036f6314931bd98732c437451d4142cf553438c67d6548640dd597318c6ee6294141d7d9553102ee6214e40ddd46510c36c5308520bd98443cc6ec62506209fd9443c87755108720dd997214433d53500409f195210c2f66188020d954421c83e45348421b798c434c35f5394c41e750c439033e6415231db18e521039d43d0130db54621c835f54cc2309f98e544433f64553329f988540c2dd63143429f58652d0e7d62d45409f996438427661d5332f910a21087765394620d7d4d435027c63540219b988540c27e6315121f394e320cb6d52882109f19153482fa608cb20bd58743442f461508409f58c544877561d53329f994524427e6114d20b7d8d404c35d6254c40bed81434c27f6154d109d984538827d6588440ded4250d0f7454546209f59742
  | 36 => 0x7e011001003c0dc001016801828c02901c801401c0a0000003c00e00601000f80ae00200080082ba003049006013801500180500000000000108038000014800000401b015278800c0540310008000015001801c002001021800000c005010803c02c003b2400d4006013011000c578000000000000e03a000000c02c00d002a2cc0000d400100980080000010280c3800e008000000c04700a800007a0020000000026002001807c00200000080c05b243d009001003e000002805c024003000042c0d8007000000816001c001000c0001c00048a784ac00500005c4006001002037006e011006800000418e0010c4000200700000b408600200000052b02ad00101a4016000002032800e0000040064006006000000000200100180281c8001009801a7c6254231e750c5110f755110220ddd44504caf462507109f988515036d62d4e219f18d51c836d6214e219f5875250f665254440bb994214833e6414c219fd97434873e6415120be98021c436e52cc430be58242082ee62d4643cf553438427f650c720be98241c433f54d01109f996420c6dd63d0130be580438435d530c421de98352843cd53cca21de951401039d4310d219fd9443c42ef6254d41cf0c1540c27f6510e20db98a50906f76155120dbd0c524c67e63d4141cf15143cc27d63d4141f9cc8310867c6550e219f596410c777510c520bdd853208775518c430bd986320877764d4542db98b540876f52d4131cfd91540867d60d5231bb99032087755190030dd18251882ef6408520db54842106f86050d409f996404427d60951329f191530437653c8510bd58b310867e6294443de94610042fb6050a20bd18542cc77565087109fd96410c6f56110a31bd58e310c6ee6284110afd91524435f53cc9209f597430cb6e5250610bb190328867d64944329b588548c27d6154c10db59642c82ee6294d41dd94621102ef62507409f99543483756114c209fd89508c73e5490c43cf551438427e6094642dd19531442f7634c431db54a420427e65cca109f98c54c433d54d0a209f586540836e52144309f58e540867e6550a10db50c524c77752c8710bbd8931486e462507109f98653482f76148310cf990548427d6194843bd597108427f65108219f58b538433f64553308f59253487764254620bb58b548426d62d4e10f9cc821c42ee6290e42bd185430425f63549109f181510cb765408710bb189314c2dc6354142dbd48214c33d54153319f997321067d60d5031db553428867c6154c20bd984408c27e6094c419f994321027c6454d219f59621902f96010740bd584404835d5350040ddd80514cb5e534c6109f596310867561d5220db149504c77661150219dd85544867d6550120db148324435e53d0c42bd984520c2ed6510a21bdd85525033e5410f30cf952408437
  | 37 => 0xa80d401800c02a802001000105f02640ec09603d801403602f00200001183495a400bd7a4014000001c18e02f003009c09e03807480080d400e00f800005e0150328014004005013014400c752096801406603101e00004202740000078044040001805033804e002801802603800900080a8009024002002a000003023800400301e00e8000001001807804c00005401d400600a02b15a800600001e80386c6003001006002804f00300300040010000b08000008018000006e00100200b809e0030070000006001011850000200001a812814402f0788014006001011800805800d00280001a8000001002c01cb01064800c98c00702287b0000003000145c02e0111ea808c0c6233001894401400139c001c00c00000c006401601700000600240300350000006001009800000e0192c1000002a00122e800400006d00001f000600d02800ac00a00000882002e0004000800800e0030048004010000002802000200d00500005be02300e000000427d00080000047d2a80000c214000014801412400000004dc05e0670002860c96065005801000410400a800001a00000b021800400500000007d40020068230146001000800403e6be060000018600500017c005600301580600860bc03b803c06e124000800006800100380040ba0111f780b41500c902101a002e2062db80000241bc000008002847c004805002e0ec00000000b62e7000000000c02001a0155ed6000020001806804b00000100000e109880580ba007003070001401500d80740d61e101980b00220b8002805c01204602b80000420090008b0c002056002801eb6a000326808000600504e8000c1a0e300482c0004005010800013802900000e400004703d8018014009010014000000802d00b800009700000b800000500300000007ed00481c001648e000800000606b00b001000000203001a000000004e80000d200703900e0022145001003406a0050320014012401010004401613c001003c21c009033814803400f164008400c00207c000000c0295fc80000200c901a87151ea0bd00905f0001e2c002817407000000016c00240f601c000800000b034c58402001000281b000e0d0000000c00a10900382901be08f014004803000a006802400200508c024800204e0080000058005000800470e02701305640420d1000002812a00b001011002000000000140002cd000014800002700000840340000500288000059004007400a07401b00d400002300b004400400001f000c00c000002003409800200180100000190be0000006009003b57804400200401b8028000010018807000a00480bc0d003002d80000361930b7021c018005000000c0181b300780e40280105678208000000000000004005800516aef0a00000380d402a00000008d417200c004f9080
  | 38 => 0x7e09402d800000800801904bc054001000800401a05502d003400e00704a00d801c03b001001800200a0028008034000001802c05c00b00480c401200b00135bc2720030038028288000023802c01d9910030300010017054809c008000009005000801f00c000a2fa0000168040008000005000801200000400004640aa000800000a00a000002400201300108580d200e002801413600003d010918a00003b0024000562009804c18201b044004005c01d00d852c004004005800000001100200a400400e1d700300c403d0050058284236000021401a000000002c046014010806802e000010866c02000000a00140000110000080032022001005402a002004121004001200780000de435000000805af5a011027c0960000000a640aa056008809000a01e000006401e00021d00100280100048d9400002100a01561ca02600b004400005c05581c802c00001280540000110001464070005012000800224f00480000ac22d002803c00a001000000003c012022000001c5820008004004003001003c1c00040000018038000008801001407a00b00a42ee00000c80480b601e013000804c000008000000201b0000c5802e1bd03380080000000480018108019001001401a036009803821400000b865c00600d0000110006000000002c0502a6002001c0080b0004002800e00401b8108002013140000007803700f000406a000000002c00000746b82b80b600300489f862c00f012009c01600100980100026cf00001140020120210000000000007b47c09001b000012000015000180441320000000108000006008816407207879a002c01c0050fc8090002019000000000c000002000400000200100000c603204680b414a00000f0124022000000809808a003016000400400300000001ba000005000c056070006828802c00f00b035402c045000804006a001000816c08601800500140080010d5802400610700102bc006000000000400000c003000804a001008800400c0000008038022007000007004e008000001c05845c0010890002004083801005402700300e400e6ba012800800001d00400000cc001006000c02e009003802402001a00d800018e000000001000c0044d68004024009007825c002001000004c00403d005813005e005019001802600303d00500920c9002800009e00000b001000000b006802401421c000823c2ca01300100140760010220000a5e01000100600380100008038000047001000803c04a0150000010000050801801e5a2003000c02e00300483380f805800b8014090129001801400a03e0000024000012009001800013a02301ec238000002000001c000001012c00000d000028c00000f0000030002011000005895800b05880ddab202942a8268008e93003000000203611680640c20020
  | 39 => 0x5003000627304a002c01800a3d6004801a0020000018000022008002400001b0140af800600200d81b800000300980040001a904800180be00200504cccb600b03c0004004001000002015a00400302400b800200900341d600e000000c078011000805807e000003815c14e002000000400e0970018000684195005000000000300000b8322066007801c03c00d00180a004000f016000800602600e808837e00a00300dc07e00e00f00140000810b48c7800031301b82e001c00401f004800402d00381c00020000420330e2c00c44c010402c036002011c00400b003802000802301c00b9bee019066007000400115b85bc1fc01f00a800008802500180240480050038000000004007000007003604d8000002004008eb240480406cb800003606601f804c0000070038000054114000012c09000300080040f800100101941cc00b00002b400a00100001d8022009001019803e8450328058040020000803800000e028003433c00002f800000800b09500e4000000000803400000002b806015404a00300200160937c080e004632d00a00947000e53e4001001e000005800016601f000000001e004001800402803a000000003000000700ac00e094005008801c09203d0000000b2500b800058a001002800807e004011000800002986f80102a801d1cb8efc000000000020400000000d002c1fc00100d806801c012011000405e0230028000054004000000800c000000022400a0120010000258043055006800825401a80985183cc001000003042e00c03e000600700000000140070b18000022004013800000018a0018080002078005011c1be17902c80bc0cc057004007403e00003483f40400010030028150001000016400001400400080b401d009040800600105501c8044000005006c00009100c8008018000014800000a04c00c802c022000003009800800002f804815400d140800002018c023008802200d0118014004009000101010400c00931841460010048000000000012000000c00400b81a000600c054800400a002004802001e000489233ca8a00000f001405200408c80080000000288b900b40472a1003802004105101cd7d402a005800c00600700a803800603f254000400401c07a801008414200c001000000e0038794048dbf01700d800201101700180e808400001e8014098013777004805e013021400203a0008010006000017800001000000004ec00e04b4fb008000000300100140040430f48008002007008808000601b05f060400001c00180000be000002004000a000007000c000008005006801200113680c800201e0648054000012003004c000002005005404800f02319fc000006001b6dc00600101480207580cb002802000e02d0018c9c00002008f800020400105d000407e0690000000
  | 40 => 0x76c00001e000004003801a000001c008009000803446c01400d0080012001026801c8080070030000066050006004000e00c001800002a00200da43001000000000600601610020000024032007805c00e00000f01fc08600b0008180046001000002c09806b001005403212300001d800a001000011499204800b1b00aa800300000cc00a00400000000003cf004800c09a026046001802c046022005cfe200100200e401a00000f000400a00f0188018028014005000942e09f012848c02201100a008c00c00a000000005000201d800400200105880640000f3000001c00808403381180b2000003801000a020018011800000f02a804c006160003803c0c2009001803402a09a04b80380600022338081e125fd02a000000e045339a61c2ec002000001c190150024000c00001f01189b000000000a8494000438009000404a00500e800800a00000002200020eb006800000800a00180680900e600100880080110048000012004009005400600100e008c042002004803401c0352fa031c14c0275e10f2800203600a803800002b00285b006215d0f300ac00400a03e209c02807500402640421dd01f80900986780030004078027004808801600d01080000010ed0008194066016038030800c3f80000000016002619800412800800d006c00000000002f800a029001800004200000f000000812100e004807247603980c001602d008005001a00d00d007805400f00780300ba00001d00000265110099128018002000001400000701f804005601f001002000600301f800401e0060470005ba400400280300360170cb008411001600001780bc00101080000000f4057000400c01100081640080060ce0008028002008803808206b1f600000a001b01c941c00200200d81dc00a0030088000008c21032804856400100320c801403900b0004002000001800005601d007804406600003980540fc007003859000031d02b800000602f04c10f400c1900070c0cd6607500304140000170000009be000100d807c04800c006865800000300380500e201f004801800e001018802c3ae000000800000c1b3061803c036005008003001000a008800c01004c019800c00000c000001001c02000200180060000100eb000e008014800c00601000080ec01c028030975001800a01681bc00e00000600540a00011c602e413201a0000000002021002922805003c001003800e02c088001c008007000001830a0ed00e801002a001000001c15208d0b88b6012c00c0150c440a0007016807c0000000388000000392
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1065563984548c2aabaca6188439994b614c830ccca430a651851d75951300c23bbaac2200614d1d152c8510a9cebb1a64905727010d510c30fb2a86218211b9ca60d5231caac6a88a22043d769524310eb3bae8210e4117dd95314e20ccca5b0a850852d7418252843a329ca5288811b5ca60d4c108dae532e821866452185424c6cc382c2a18871e5c06510f21cc8c528a831847671997420c316b22a429021b8d84604c9208f6eca80a0a0ce57598d2108732b14c3aa441691d15108520ac8e2a9085a0664525843250732328c4a0a21711c5320c8309cce9b024210d2d740c1520c2373b6a4a0a638d590510c5408f4e032a8418d70715405050e2fbb2a629e211d1d561cc9108dce532a82986655258452102a739ca910a439994861508318e8e2b2a851871554547300c30eaa4c7208634b9c86095030acae42a043885a474548214430f322c62a041391c961d01108dcec29aa42056672152510c236b90cba18214b9d85450920ccac52888110564745482144237390cb21c211b1c9650c540aaae6292a22046d721805344236392c32a221711c5320cb31ad2e021aa50864d5318930c82963a2a410a2195d8f5154142ce0c2302a8996666298454082363aac421a410f9d065cca10c72c8b00a610f45524c4310c2b8382c6a88819354d62d4440aceeb990428863654584400c22ebb4a9218878d5926114e209e2e03206390d3671d91540c332b12c2282879554c6150c21caca630a6510d367414e5188392aa24210861179cc65484408dae5306a6a0e445318532482363b2a4a0c212e1c164cc940c3ca8b18811846d72d974348637bb2a4292638e5926014c209cae23206510e1d64d4e53486b2b8aa410821559ce534c510c3ca8b18801052c74585521023bbb2a220061711cd2108430ac8e2a90a59861d6550c430432b29ac218041b8d88604c510c9cc62968298e6462945310c30eb24a618021535d6630c821cb0a6b00629046c76949311030e320c6a92218d591510c220c9ec7a92a0a0d6671152520c237bb2a8292631bdd95214a109c8e4b0e618861c7650d5010f0eb24c629c211d5d66110030acae5b26a29947671196430430eaa0c6a0661c554d51d0040cb4a6b00638843e741943004273394c118e219398e52d4440a5ae92908508475769524110636b90c0aa6634d9d362d4532ae0e0a9ea2a146c725875050f0eb22a6184418b592520c2108eae2b2c400852e7494e21486b338c8629283c91536150920caaa7308600853870550544cb1aaa4c2200211e1c16550d21ec0a4902200862d54588540c333b14a2a0881595d44208510a6ae3aa4a8186c463cc5210868eb9cc82a2430f5d0650c010a3aeb30a8621d577654c31086b3b8a8629263391c96110f4187ce931ea090e5563584548c2b3394a088021871936354d20
  | 1 => 0x520c297396c8aa663175cc65908108daeb31a4210e994358043882b3baac890843599c85354440cccc4b0ea81845d73194215024fbb286280871edd95014341acae22a2a41846f7258653442b2baa421086193d8f6255110da2e230286986656298454887b0a92a298061359ce64484218dee4b20a29846f7654840842b3394c0a88611e5c26550f218daed29c641970d535084210236bb0a810a41999896195131cb2a7304620863654587520c28f3aa8621a411b5c860550318ecec2a2828843f7655054c4317b20c4a9a211b5c864540318eaea30a86085a6740cb41086b2392a228a61175cc65105208eae3b12a1a1e3a5458041c422fbb2a629883595ca51084409c8ecaa24210d3671d52540c2b2ba865988439998961d4f219caec1908210eaa72181435032aa9ac218041175cc6510421d4a863128220d97715814310f38b0aa028065559cc54546208eaebb0a642046d72d94400432a31ec2a92218b5526290c32cc8c528a63186716198054082b2b96a6a8881c95534210421acee4b1aa2206646254531102b238aa4908619998a5110030ccaa5b0a841864d6314b414c673b82c418843699d05348421d1a86312a221c747159532d031b324c229c411b9ca6094643e2a8621ea2a146e72d9643c4296ba0a4900211d9c76590d208d8e4b2a831861d6550c438431caa2c019061d154f320c421e4ca8908421855673d49511029a3a2a228a619914c624c710cc8a530864a0c75759843088237bb2a4296831d9c76254243c5ac829042a047b765405088637390ca21c211e5c06510c21d4ac8908a010e2f651894110726a9cc4180419918951506208ece332a84084777158a540c2cdb82c2a188799d946250441c6cc8a886110534745895110237b92c7288819594e61148409c8ec9924210f4553949511023b38ccb99081691c54210a408ece3b2e86905647258454cc762b186410a211d1c56294c40acce5aa4a21866462d45314c23bbb2a228a87535d6530c821caaa7308a620635545844008332b14c2282871d5c4605533287cec2a281187455354a51102ab39ea328881179ce6550b108bae732a858843f7655043cc2ca38ac4a18871ddc5654c910cccc4b08a81966562584540c21fba2ca19221595cb63d4542d2a86b08a021e6962980530434ca1ac021a411e9c06510e218eeeca8861105c673d8b4108735b2aa498061b118f3248421d3286b00868847a7019443082b3bae6210e41a959041085208dae432c860846d72d8550d0e3a3aac3a1a218b992520c2108eae3306a89963554587520c35232286908430f1d165085308eee2b2864a047575d85430422eb98c0aa0431d9c66094a438dae5b2c800845f73595219032a318c2aa2419554f614c840c5cc8b10a81862c64149504c75332085988431ddd951145208eeeab0881
  | 2 => 0xcb98e419958a510c220c68a830a84906a654189411072731ac42a6659c5456014432e8a64192a21856671d4920042733b085988438719153484408daea31286104747158b5050f0e32a8621a438b590520c941c5aa83128610d657114c214823a3b28528861399cb6384110c3aa931c841956571948218c30f322c62a4414d9c76455332c6aa9308a81846e72d964004237396cb180218d5906414532ac8e2a9685a054d73d4a521032aa9ac3a90811b9c86510f10d8cc61968210c767614910042b2b90c1a8a658715163d0932a6ae92888310565721835150b86a188629263399cb6484110c98a6b16609065553987521023bb8acaa12211d5db530c721a9ce4302a6204e571993320872bb2ec299065a350e62140438daec29842906a464d052108716b24a5a88611d1c56295030c9aa6b1060086994358043d023bbb2a410e21591c5639484087ae932e421865763185544823db82caa1a431d9c46510c21c5ca831282105647158854ccb2ca9ac0208819358e6215232a68e2aa0a89843e74195210c31a2a2c221a21391da5448421d88a630a6490664625453188333290c2990414b9d05354a10cceeca904388656635845308236b94cba1c211b9cb65cc740cacc728880187445318931442cc38287a02611d9c66510e2087ee8b2a648866552185420c72731aa428881391d1610c8218daea3266410dc67310b3108732b14c32a26587d516395121acae4320a299565721805150a3b38cca990211e5c06510d21c98c7a92a0a0e4c53185324832ca98c0a18415a9c063149418dce432a82184e570991210863cb80ca990831d9c46510c108eeeab0c600861d6494c30082a6b98a4192831b9ca60944439d4e130c849052e740c1520c237b92c3298814b1d15250a308f6eca80a121d66721015110332a94c2288814ddc562950309cae23128610f61525464010237394cba08611bdd95214930aaae62a4a31066652986208432c29ac018a811b5ca658c440a6ae2304a81843d74194320423cb80ca21263b194c614c8328f0e0b2a8610c6c7259531d030eb2a86218619954a6188010bc2e02a24210e3554d85320c2d2ba4c6908431d5d4614c810d8ce631a4210c6d769485110273bb24328043179cc6550810e2a8621ca3106567614d314423b388cba1821691d160484218eee2b2a64084757198f5050aab398c028a858d55161102108dae532c831845f7654c53086b3394c12888117dcd6510910a9ce62a2a50864d53588511031caa4c018861875536350830ac8e4b1ca22061d54d81300c327298c498e43539cc4054840ac8e4a88a2a043d741943244237bb2a4292211b1c963145409c8e2b16809061d6454c5304332a92c229061391c5644c920ad0e4a80a0a1d3474589518822fbb2a6298211b9ca658c4408deeca90a22066561186
  | 3 => 0xd95415120a5ee8b0aa50864e6394840843a239aa410a21595c66054830a6ae8300a29945c735944148333294c320421471cd54151108dae5304a221ec543189310c6a6b98c8292639354d6214c41aaae7a94a22066765484211023abaec299441591c96454430a9ae6292400843d74d9732c423b388cba10211d5da510c220acce5a8ca321c6e7298f505063bb8ac52a461a550e6114843acaea21a4210ce47259131442b4b8086a9081471cd5450e109d4e130c64905647250c514ca973a0c1294219398d62150308dce4302a620e5953d81321038db8286a80870f5da5490842c6eca30a842152c72550544c2b3b8ac629283d8549518c03087eecaa0a910e5763185534831b322c22a0411edd9501413287ce831aa010ce571190320862f39ecaa0a439358e62951318bae732e42204e471588430ca3a3b264a8c411ddd951144429c8e2b16619051d73150434834cb1a80204218d9926115030caac6a88a22166662987540c3172a0c4a0e43785c05348421acce5a18a29943f76550540423bbaac2184419658d6015021cacc6a88a2204ea70d8e21482d33a66420843c550c4314532a6cebb228288666521854208333290c2990610fdd95415232d4cc9a106210c6c72590514c236baec4a08619a5896015031e4aa82168210e2c5458b4048332296c299283999486150a30c6ec9a8aa09945e73194428428e3aa8621a214e1d15014131b8ee2a126419595711814310e3bbb2a22886587d91534c8408f6eca80a120ce572190310873928ac0188611bdc96510530ccec528a821845f7654c5390733b14a2988619994c614c920c3aa831a82185657118352507b090aa0280430f9d0650c810a38e8a98a6906365458442c8732310a2a0a814d1d151506208dce432c8608555711825310236baec4a18411edd950140428deeca90a4a1e2d64988538422eb9ccb1088139dc162104218f6eca80a1216656548421102a6b98c129421399c66090920e1a86218a4a0e6776548214431b2a6c2990619a1496008530acaea208429064f7654c3208727b1aa490861539cb5394c40ce4c2b00a610d647254451d0353a18c4a0883531cd6154a10a6ce2304a81864d635485204273398c8908431b5c86510010cd2a5b02430861d5498e400c31ab22c229c21595ca5108640ccac4b08a91849e7615143cc2b238aa429261995846154830a9cec29a64907447254c31086793acc190a21559cc40544408f4e132a8710e3964540500863b388ca212611b1c9654c640cc8a630a649049f7650c5110eb23aa4210a819998951102208f6eca80a021e2e545884004333314c2298418b9915214830ccaa5308610845e731944204386a1887290814d9d35194732acae3300a498d357414a510c32631ec4a92218bd9552500408eceda8aa099476719835350a1f3a6
  | 4 => 0xc2e021042885647254441d031a2a6c2a12438755163900308dce432a86104e77058432086ac382a629a83c3551320c830acaea18842905717010d51102b2b90c028a65591c55214843cccc4b08a70866562987538821eba6cb992210fdd95415230c70a8b0082984767614d314430eaa0c690861c91504208510ccac4288629045d73d94400423bbb2a228887511cd52085108beeca98a6a046e76d51528430eb24a6184219a1886055131cd2caa9621086a664484500871bb20c2a9a41aa5096010840acae3b1ea4a0c6d721944384386a1886a94219358d6215010ccca530841086566358454cc63bbb28528c41175cc65d0810cd2a5300822066762545311022f39ecba0e419918b61551308deeca90a42066465d89414422fbb2a629a218b5916214e10e2a86a88a221d4c725855310352a18c2a1085665c35350f40acae4318a2a146e729835304332a92c220421879db6550c43acae429ca22055673d8b5150ad33a6c5988431b1da5250430e1a86a90a421c7671996420c2963a2a510a211b5d46250c21e4aa9292a2185657114c21c8333314c22982187d906355120acae3a9ca4204e676d0d2108637b92ca21a438dd9054c851087ae8302a610e3764185544c28eba4c629a439598d51102208eae332864206385458042442b339060a886187591530c0208dee4b2a86904f270d932144332b14c229c411d5d4614c840ce2c2b00a81965863d81544422fb9aca20a411bdc96550c108baed29c6218c7b7654050d0e36bb6a8214438e5536050830b8ce62a24210f25541512108732292c3902219554c614c841acee4b1ca22045d73d954148794a9280200611b9db53480208deeca90a521e6a62580540870fb20c6aa2219394c624c420c3ecaa188610476711944308237bb2a42886199949618c210ccac5308a91872954549300c333baac4188431d9c765d0f20ab2eba1a601843f7655054ccb2b298c2990839914b614c9318f4e032e8610d3574d4a510c23b3b6a2a8285875915314c21c98c7b12a888667651854210b16aa4c520843595ca51084309cce53046288565729805150a3a3aac3a12218b55162100108ecec2a283885677654821442b2b94c028a658b5516215031ccca5308810845e76d51300c27239ac420843559c46094c40cb4c6b06a9985e1700c42148297390c0aa0611bdc963145409e4e131482885347158a540c3b1b82a410a21179ce65c8440cc8a430a84a056970190524c71b2a0c2a14439c5866015030c9ac7310a908555739443188236392c329a218dd955150040e2a8621ca22062c64d49504c72ab18a610e21591c552149439c8e4b0e6088665629875488717bb2a8210431d5c46354042acae42a0428863764d85534832731ac42a063d194d2108440a6ae9b16a29965963983548c32db2aa6a00810fd
  | 5 => 0xe6552984400c3333b6ca90843691c54210b418eaea30a8418565750c821c4317b20a910a41d114f624c510cd2a4b00621861e7615143cc23bb8acaa14614b1c96155030a6ce9a8ca21847571993504ca36ba8c4a08618d550614c830cccc528c611046f72592510c2b238a8729421591c56354840acae4298428846e761515284237390c0a9e839a9896015032aace3a9ca62047771595430829b3a6a5288619954a6114840caca7b0a642045f7654c5348636392ca21a214b5d052c8010cc8c528a82087295454a300c333312c2282871d1c4654c9108e8ec994a2185717010d5188236b96c2a84871b1c96550430e62a2a008110479709954388636bb4a510843b198f3210421b88e6908431843c74594314829c3a2a028265635c86050c438deeca90610846e7598843486373b0a4a82638b990520c941cc8a4b0682a0d6572d465110236baec498c21399db54484218daed2a4439046d72d974344236b90ca21821b25c86050d308d8e4b2a839863864d815344333b2ec4a0883391c562d03208deeca90a51847b7654050d0b1aaa4c2290611d5c460550328eaed2a6438865563544400c316aa2c4204411b1c9654c440c38a8b18849861f6454d2110326b18a4212619354e6214440c5ec8312a89846d72197438432ca9ac02988339dd921d40218dce432862a064e6354b51102aa39aa298c81b49c46050d30d4ac820843906566358454882b5380c9294211edd95014231c6ac8a88a21046f7654852cc29aba0a5880218b9916294d21cb2c6a80a010cb674d85325062fbb2a629e839a5895014043cacc7308a91047776544514c326b1aa4290839c54560d0440b88e4988621865a63580540c636bb4a921085599c45394840cccc5308a81847571d9743c831cb22a028063c9dd1520851087ce8328629065553185321024fbb287a90879658d5014041c5ecbb128220c5e731942004333a90c2a12819554d6114c208ece2328640866654189414423bbb2a228c611e5da5490040ccaa430a652047970195420c735314c02a063b194c624c431cd4c4b00a610c6c75588434861f3a4cb108618b9516210f328dae531ea0a0ce7755843208716b20c8a94218b5915214830aaaeb3186210f195494d300c334316c0aa263395d66448421b4ce9b0e6410c6e729964384273bb242a8043999486150830aa8e2b14a6204757694e310c63b388ca21a41659c46050c438f4e0328640866652185320423bbb2a828a659c14560085308dce4322a018d6672d4e511023ab8cc129087599c75394840c9ac7290801866972181544cba4a9260184211ddd95114742ccac4314a2205717018c5150ab238ac529a41995846154840c58c9b12a69066652d85321038aa9a8220881a550d611484387ee8b2a431843d74d94300423ab8cca21061999496190210b
  | 6 => 0x10c326b18a4212638d55161150328dced29263084747159543482e239aa210a411d5c765ccb40d2a8630aa421d547154c534823b3aec2a122178dc15108520ccac4a88a21867361181544cb27b28c4988631e1d56010d10a6ae8182a2186a464d0d210871ab22c229c41599c752948408bce7326a090c6c72592510c237394ca21c211d9d46150932c98a6b10869043d74194314822f398cb210219918a514c410c6ac9308a610c75711815310a3bb8ac529c819558e6195132a68e2b12a81855673d08514cb16aa4c5a886199189514c420a98e6a90428851c7454d43086b2b8cc0292831b9d7648c920ccca430a84085c473548214430eb24c6298410f5d0654c810aacebb1a6288666521854290735b2ca49806178dc152085108eae3b12a121c7571594300423ab8cc1a9a859558c63145428eae332e8418479701964308636b94caa1c211bdc9654c6408e8e2b2a841846e721944004326a9cc5a88814b9d76450920cceca30a659046e729943110333312c2298411b9cb650c010a3cec29a86a043e74197320432729ac5a8881a9d5061509209cced1924210c6d75988400c29bb8ac4aa0611b1d952504308ece331ea0a166452185324c31caa2c02a0438d59151144328eae3b2c879066952580520c727318a4212638b5926214c10b96e498a60184767199543c832aa98c2a10814b5d05210931c74c9300a610d2d75990420863dbb2a0282859598d6115210acaeb31a4210d357414d518838c382a6a008159dc94314532e8aa6a92a22047771595420c30f322c62a04399597320c4218d8e4b2a860862d54988520c31b2a4c2290618d5506150310c68a83128288564724c5500c672392c221e211b5ca60d5231aaae7b16a2a166a5258042842733b065a0843b118b324c431e92a6a9280204ba751814350333b16c2aa2611b1da524c430ad2e021aa4184e776544214823ab8ccb99081875d76550c438deeca90a4184f270d8f2144392a92a2a0081995896114e109e4e1314628856671d4a5290237bb2a4292811ddd942944309ceed9908210c6e72181540c732b14a2200611b5ca65cc440ac8e4a18a2a156571183524c739b0ec0aa2651b9c86014d10c3ac9318a408535759904108722298c498a211d1d93294440aceeba1043884e67614d210872b31cc22a061b898b5084110d4ce931a4210d6672d46519023b388ca99081471d54350130a9ee4b0ca62063554185420c72bb2ca29806159dc56354a108dee4b2a60884f170190310863d380ca21a439c9456010620cc8c4a8a82107465394951103a329aa52888139dd95208510e1a8621ea498e4e63548400c332b2aa3904419354d600c8219c8ec21a4210c75719964388338a8ec0988810fdd954150308deeca90428867165547208827238ac8996411b9c86055331bc4e02a2421
  | 7 => 0x2200619314f624c521cc8c4a8a82185647254741d02abb8ac4a98818d5926114c10ccaeb3224210d4d7314b200427238ac421e85361c163d0930c3ac829864a04e47654d2108732b2a42108619994a610c210c5cc8b10a8085727018e518828e39aa8a1821559cc6094620c5aa8b10a2184767118d5010a9b3a060a886117dd95314440acae42a4a2184797019743086373b0a8a90611bdd954108218dae4328600866462d855344236bb4a420061c550c4394430caac6a88a21062c5458841483172a4c5a88619c94560104408bae632884085647154b32cc3932a4a4a8861875915314e20d88c721a4210c77765445190236b96cb21e21551c55314d40aceeab024210c757199543c834ca1cc0288871b9cb65d0f10b2ee2b128621e565398752102963a2c6a90811d5c465d0c208bae632a422061d5418d420c2aab8ea7298811b1d56290d209c8e2b1086905c673d083108637394cb18c811b9cb6510010acee2b22a50856a7010d528431aaa0c2a10613c1c1644c710acae5218a2a147b705954308636b90cb21c21999506250710cccc4b0ea90863464d85534430eaa2c62a4210f5d065cca108eee2b1ca42047571194438832731ac52a2431b5c86510d10aceea908421874453d85324826c382c7a0a61999896114f2187ce9b2a6290e1f6418d5244316b22c429c41591cd51087208e8e232a848846f72594434423d384caa1e4359dd521086308eae332c84184747650a511022fbb2a629081595d761d0821acee2a1ca5085a47448421102b239aa410a218b1906254d10c9cc6b10a8085687058d52102973a0a729421175cc6015110ccaebb2a4210e7161980540ca373b0a490021599ca43145428e8e2b14a6084e970190320869a38aa82a2411d9c46054f42cd2a5304420862e54988520c22fbaac72006117dcd655091087ce9b2e65884e67198242c831ab20a810e211b9c86550e108dae5b2c8690e57531853248332b10c4a8881359cf6150931c9ac6298439054e73d4a52d062fb9aca902219958a6115010acae5288420847571d9743482d2ba0a6908439514d61cc1109c8e2b10862167365545300c2b5baa4290041551cd52c8510ccecbb0a8421475711944348237390ca218211b9cb6590d10ccca5b0a841865963980540863b38cc129687879d85350d40ae2e0212a22062e6498853042373b2a4a08611bdd95208010acae3a94a42066552185429027239ac2210430f5d0654c4208eae332c851861d5458c548823ab8cca21c419c9456088620d3286b00870845f7654c539030fbb286a80871ddd56210421a9ce62a4a508666625875384236392c22a661599c752c8010c72a8b00a818e3964540500cab33a88690843995496114843cc8a430a64a0e3654185320c237baac21904395d94614c832c6cc9308a610564725452
  | 8 => 0x26214c21ae6e0aa6a299745530cb3108792a92a3a0081531c95314d40c5ac9310a4086646518931442cc382c4a18871d1d5610c9108dce432886884b57418532106b23928728c41691c941104408dae5326a098ce67418d2108636bacc8908439914a618c93187ae8300a6887187050d5010eb3b92c8a8c411d5c76590d219c8ec98a4210d4e72d4e53d072db2ca6a008193d4c624c510c6ec828aa0996a46455121087172a2c428861471d543d0130a6ce92a2828845f7654c53082b3baa4210881179cc65d08108eceda9aa22047671195420c23b3b6a88802159dc96454430aceea908432053474548214430eaa2c62a04195d8d5148430acce5a9aa220664621855408732298c498a219554d6114c40ab0e0b0aa62045c73595219032731ac42a4210f5d06508530a38e8a9a860861e76151434c392aa2a5288615c1c164544308ecedaa2a31064d5318941102b2bacc8908431bdd5628c020a98e6b22a41864f65549300c38aaa262188611b1c965501108f4e03288498d6572982510c30f2a2c620061175cc6510b108f4ed28a2008636645845388316b20c829263399db53484218dee4b2a8690e376454531103172a2c420c43595d52108440cccc5288611066552984510c333b10c2a9a418d95061508308eaed2a0a299639541814308297bb2a821043711cd6048421ae4e0320a29946e76d4d52842b2b96a8a88611d1d94254430caaa6b006210d727010951102e4b908098061551cd6254620c5ec9326a498d347458d511023a38acaa1841875516310020c38a8b1882985647154852502373b6a8900414d9d05254430cb0a6b0064a046e72983544c72729ac42888139dc560d0821ccca430a6518e2e64588538831aaa2c0208431b5c86550e10ccac4312a21866962980540434ca1ac0290874d5d060145429ceec21a4210c747159542cc2b3b8ac7294218e5954010030ce2c3300a50847671994420c273bb2a6908431d9c6658c840c38c9b1aa48861c6454d3210332316c2aa2211d9d66110d21ccac4a888110637765504108636b94caa0a619594d61d48408eae2302a7a162d5458b510c326b1cc42a0219c54760486208dae432862a046e7219531102b5386a490021179cc6510020ccaa430a651847a70196430870eb22a6298411b1d9524c6108dae5b2860086c5634845008734a92c1a10818b9926214c208eaed28c2008664621855308733b2a42108611b5d7624c440c6cc9308a60847571996321022f3b0a8a1a618d9506150b32acee4a18a2a16c4531893144335b2ca4a008166dc16250c4387ce932842186555318530c429b3a0a6a8c41555cc52c401096ce931a4210d65721015110326298c498a21a550f6154843c3aa8b18801870d4310d521032629ac418a41ac5c46050d408bae6328801062e6454b510c23abb4a
  | 9 => 0xac8a98a7084757598440882b2b8c86292838b5506250430ccca4b0c410864e63948400c327b18c4aa2619558c51105308dce5326a098c3f76550540863a3aac221a2199948614c8409cae53266210d2d7414d52842b238ac9290611bdc96550630caaa6b08a6214e673d81210863bb8ac529881175cc65504208eeec994a31066662544400c272bb08410a210f9d0650c421e1a8621ca5087154310d518823cb80ca19283555cc5454620aceea908420856671d4a520c23abb4a2204411b1c96155010caaa6b08a4205647454421c82a6b98a8a9421399da42484218e8e2b10a99864d535885304332292c221221591c951145439c8e2b108690d667198152102b4382c8a90619558e5110220c5cc8b10a818c777558831086f0b806410a21555cc60145429d0e0b22649051e75d91434c23bbb2a228e81599cb5454430a9ae7b0ea4a0e1e6458c548423a38ac52a0219354c624c440c9ac6b10a9187265454a510c21f3a0c029a211e5d46050c10cd6c4302a898c3e7615143cc31a326c2a9a411b5c8654c4408bce7328422068d435885010f2d3a8c0a1a61399cf6548421c9ac631ca50854c73585520c21fbb2a82a6413c1c1644c510c38caa1a809846d721954304332316a2a0a819594c614c840acae3a9aa4206595318143042b33aa4210a611d9c6650c840ba2e2202601861d5418d41cc61eba0ca10021a350e6214443a6ae8292200866762185544823ab8ccba1c418d9916115032caac7308a918f44530c421482373b0a6a94211ddc56550810ccaa430a6420e565358432c87a2a92a2980611d9c66094843cceca3126218c6d72983544c6b2b8ea8a90619598d6115032c9ac6b10a9105a77458121086b3390a8a88610f9d0650ca108ece3306a91953774589518821eba6cb98e411bdd95214a40d8c8630a641964d6394b511021fbb2a8290610fdd954153308eee2b28869063b65551300c22f39ecb212211b5c863540418deeab10610846f7259531d03172a2c5a88614b5cb54950308dce532e8708673659454010296b96c8aa06153dc96154c40acaebb166210c7776544510831caa4c1208218d5516114830ccca4b08810846e72994410c2aab88c0a98814b5d06014931ccca530c610847575d85428822ebb4a7190651bdc96114d40c3ac929861106c932580320c23b3b6a8a88619998a6114143acae22a4a41870d53949401038aa1886a8881879926314810c5ec9b12a6885657214d5110316aa2c42a0211b9cb6154243aaae7a92a2204777159532102b23aa4210e61475d66250c43cacc6b08a8105357595041086a739ec3a928378dc12154021e2aa928a601845e7615143cc23b38ccb194811e5da538c030aaae7a8ca22055573180514cb2bb18c2aa261b1d4c624c510c6cec2a2828855473544515021eba6cb192218b59
  | 10 => 0x47676d49511031b322c22a0619958862944308dceca9262206677558841087922a0c4a0a21785c25208510cb2a6b06862051c7454d4308237394caa1c21a650e6014843ad4e0320a498e2e54189410c2b3bb2a410e21995895114443aace6294a220636645865348727b1cc7a92839958961152108eee2b10a6a051d7414c4348272bb486908431b5d46250610acaebb0e6410ce5760c8214423a3aac2212214bdc96155030c3ecaa18861845d73195420421eba6ca98a431b5c86510530ccca430a652046c7258553042b4382a629283391da53484218eeeca88a39866762185544ca363aac5a1a411e9c0654c8418d8e4b08a6a061e5458c408830eb22a6180214b5d06014941cc8a5b0a84a0d2c745485244333314c22a0218d5906494620acce3aa2a41846c769494110317322a428861875536348430c6ca9b0a84186996350040cc32a298c29924199548614ca10c5ac82a0429047771588544c21eba0cb990211d9c6654c9409d2e4302879046e729835350732b12a2184411b5c865504308f4e03288610c77715954348398a8a8020061875926314c108dee4b2a821866765d89310c71a320c2a9a41599c45354840c5ac8a90a2184747158a5390358a0ac02088159dc563948408f0eab0084884e4725844344326b18a610a4117dd95314f408f2e03288710f44530c8214422f398ca10a819394d620c010ca8c7b0aa8904e671982324824f3b0a6a1e818d1935154132cceeca88439065663544400c326a9ac4184410f1d165481109c8eca124210e4e539885110326a9cc4290811d9c765ccb40e1a8621aa41846d72d9743c428e39aa8a18439a549601484387eecaa0a21845d731944284237b92ca988811d5d66348421caaa7b0a842063554185430863bb8acaa1a211d9d764c85108dce431aa020f24725504108733294c220061b190c624c4318eaebb0a841862c54d89414863a3aac898a219958a51902208beeca98a70847b70595434430eaa2c620421c554e5150040acce3a9aa42046d7519032086b2b94c0a8881531cd5288510acae22a043906a57498d2108733294c3100219954b614c84087ce832860104e57018d21087a8a9aa2a00811b5cb6590d108eceda9a20084c6739912108798aa2a298061369d46050d30e2aa928e601843f765505444316b22a429063175da5314440c76cb2a260185647254431cc30fb2a8621c219558d6115020ea2a2980611064d539885310237b92c22a6618e5516015032c6ca8b08a41856771592520c29c382c2aa061711c5320ca30f0a8621a4210c5d731944004236b90c0a9883d254d5290040c6ac9308a61045e73d94400831aaa6c2a10610f9d0658c810ccaa430a851863554584540c32731cc42a041399da4148421cd2cb29621086655218520c4332a92c2200611d5c66094a43c3
  | 11 => 0x1031b324a218441d154c5348421cccc4b08a9184e4725844348716aa4c42a0619a54960104408ecebb0a648856571948210c31cb24c0298211d9c46055032ccca5b0a650846c72586540c21fbb2a82a4211e1d5600c910a38e6aa0a890477764ca51103172a0c4988614b5c86095030aace7a8ca3a15557314a511023b38ec4a86874d1d151145208ecec2a2a3105557314910042b2bacc09084339dc960cc4218bae6328400870d5394b401023bbb28428a65c550c43d4532b8ae62a24210c7671996428c332292c2212631ddd95114440a6ae8304a31047771595329023bbb2a228e654b9d361d49318ecec29aa3106356415021442b4382a8292634b9cb64550309cce731a4210c7b7654050c86b3396a328881391c56210f20ccca430a84206657598d210871aaa2c22a041c9d494110531caaa7308a2204777654451d0eb3b92c628a859914b6150931c5aa9310801846e769493110327b2ec4988639554d610c2108d8eca926220476711954388332a92c21842117dd95314c42a3ce7aa28690c7b76540504c726b1cc42a0411d5d4615081087ce932e421863a64580540c71cb24c0290211b9c86510c20878e8b2a431847571995424c29aba0a4a8861ac9c46050d40accea90842a05677250e5188335b16c0aa2639394e62d44408dce432c861046e7218054442ca38ac0a18871b9c865d0e10ac8e4a8e63985647258653442b4b80c6292839c5456014442c5cec2a284906c5630c421482733b462908434d5c4605503087ee8b2a6088654535844344333314c22a4611d9c66590e208dcec2928298d1d759814310f86aa2a4980615cdd52144010cc8a4b066298d4d72182531023b388c8a8065395ca6190c21aa8e6a8a6310477755842004274b80c81944359dd56348421cb6c6302a89962d5458042086a7b9ac2a94211b9cb6154343c48a830a8490699644c03048338b88c0aa2631d9c465d0c20cc8c5b0aa898c6d72994438423ab88ca192810fdd1654c120e1a8621ea4a0f4653549511023b38ccb21021599c75294b43acae3304a4184e7715833208636b94ca18881171cd65085409aae630a8418d6571180524c636392c3298819558c5308510e88a630a649056b7054c5250637bb2a6292830fdd95415220caca630a842064d63988520431a2a2c3a02218d9916114c20ae0e0aa6a299665625845388333a90c2992638b5926214c20a9ae6300a4a0ce576d0d21087a2a92a398061a9d0c6150842ce4c2b00a81956a7010d521034cb226018221595d43208510cd4a4b0065086a56410821c4333a90c2992831bdd95214a41a3ae62a0868872552504418423abb0a5880218d951611002087eecaa0a818e35649443088275386c910a411d9c66550e20acae3290432062d54189310c2373b4a4a0c21711c9310c630c9cc7310a808
  | 12 => 0x908434d9d06014532acae229ca42054f7654c320861eba0ca19621c554e51d00409cce3b1c409056671981520c21f3a6cb992211d1c5650c9408dae5306a8086c46394d21086c6392c0a1887c6553404c030c9ac6318a4a0d677258e51882b2baa4210c614d5d35254430c3aa831a859945d73d9742c42b9b82a828a651b9ca60947438deeca90801863854583434c3172a0c4a0e63531cd524ca109cce73224210f3154546300c23bb8ac9290611d5db5410721ccea430a84a0e3554984400c23ab88c8a80658e9916015032c5ec8a92642061d6458c520428f3aec6a1a81b19ce64484218dcea3128298e6752185424c62f398ca212219354f62504408bce6328800846d72d9731d028e39aa8a1841179cc6510421bc2e128842904e671d922048272392c221c431d5c4654c840a5ae9a94a4185c673d874208733b28c2a1641395c86150c21a5ce5aa4a81855671181531023dbb2a0280651d9d854544308dce532c82184757694f21442733a4c8908438d5506150b328dceda9aa42056571948214430eaa2c6204618b5526210020c3ecaa1887104ce73991210863b388cb99021c355152cc0308e8e2b24a41847576d531004332314a2a0c41995895114440ccec4a8a821846f7654852d033232ec498a21599ca6094430cc8cbb0a649045d739942110332b14c22a0619a54a600c43087ae932c421845e73d974244333312c22a061b8187604c92087eecaa0a898d4c73549329021f3a0ca192211bdc961d41438bce6328858861d5498c400c237bb2a4290839994b61508408eceda9aa3104757694f21c42ab398a928c419998961d5331cc8a8312838864f63549420c2b938064a88610f9d065080108dce432e860863554986420871b2a0c2a10631ddd951145408ece232864a043f76550548c63bb8ac629281c95084254440cd4a4b06430851d7414c4344273394c120e21999486150a40ae2eb102200864d6354840842b2b88c0292838b99262150309cee4b068210d2c72586540c22f398c02a2211b1c961952309cae1b2a4210e39649805308733b28c4a0e21781c532c81208eae3b2c8690665650c8310862fbb2a629c851ddd95410421c3ca8b1881084e57298f4108754b90c0a1a811b5d66210210cb0c7b02a89065763d85544834aa1cc2280871ddc56215330c72a8302871846c72584544c2d238a84210818d9506150810ad6e0aa0a498e1e5458c428cb4cb226018441995896115220970e0b2662a062d6415021c830fb2aa6a0081879516310010ba6e299260184e7705844208733a90c2992611d1c56295230acce5a8ca31874773548214430e2a2c7a0a631b9ca65906308daed290810845f7654c53c8636bb4a428861599ca60544408dae4328878852e74d49424c726a98c4a18439554e618c821aceeb99043885727010d51
  | 13 => 0x621502187ce832865884e67690d2108732310a298a618d5906454620ccaa430a642065953580421039238aa8210431d5c66094b43c5ac8324a5086646294541902b238a84a80851b5ca60947438daeb3148610d8e721814310e3abb4a5108431bdc96155010acee4b24a21843f74594214c237b92c2a9821d1549310c610c68c9b0aa488664629454110333314a2204414b1d15250a10a3ce9a9a8690d1e76151434c333312c22a0413a1c1644cb208daed298a4a0c757119443c82ac39aa0282851d5d85408510d4cc9a144210dc772505310c63bb8aca212611b9d8534cb208deeca90a408564725445110f1aaa4c3a90610f5d0650c020ccecbb0a641963b64181544caaa39ac8a88611bdd95214b10ad4e021aa418475751853288317324a5a88611d1d56110d219cae331e8410d4e73d493250732a90c2a14219558d61152208deeca90a598ee061d8142482373b0a8a16419598d6115030caac7308a91045d73993504862fbb2a629e8559dd95108720acae5288431861d6454c308423bbb2a228c858b591520c210e4a84212a31066a62580540c63aba8c2a18439c9866015032c72a9304841066862d81544c21fbb2a82a6638d5916114c208dce532a87886556318d5188327298c4a0881631c96150c43ea2a6a8c802066562144414821e3a2ca992211d9c46590e20a6cec2a282886696558a100422e39aca212214e5d64350040caec6a8a8218671515805110f71b10c0a0a2159dd52108420cb2a7300822046f76548520c7522a0c2a1241a650d6010f30a9ce7a94a42063954181430423b3aec790a211d5d661d0c218eae3306a91949f7650f5010eb239282a80831b9db5254131ccca630a65904777654c310863b388ca21c419915061509208ece232e87106656298454882ab39ca990a439958a518c2208dcec29a649066962980540c30eaa2c6200211b5d4624c440c70c9b02a6904747158c52502b2b8cc1290810f5da5414430cc8e2b10a818ea67419121086a6b90c0a98811ddd95114532acae5a18a29965653d8542102d9b8a84a00818d95261d4830cccc4a88a21853574d46510c31d322c0298430f9d0654c420c3ac829862a065a63580530872ca9ac0298858b150615092087ae832a421854c73548525022eb98c8a8043591cd52087108eaec298428864f6318954442b8b8086a8861175cc65d0a108ecec292a22066462945318823d380caa184317dcd6550110c9ac631aa50866962980540c6b2392a228e61999896115321cd2a4b06641856671d0c524c63b38cc1aa265299d263484218eeeca98a2a166962540500c63dbb2a028063785c04108520ccacaa96210865a63580540ca36bacc5a18439358d52d4440972e0322422047571995438835232684908431edd950143318ece3326a09966952d813210272b84c6
  | 14 => 0xc6a90a42062e54d89410c3332a0c2a1241391c961d0310aace3a9ca7a143f76550544863ab88cb21c41531c96194c40ac8e2a92422047776544510c2aa39aa410a211b9d85248510c74ea30286a046d7218153d0673baac221043595d762d0421caecaa8a601856870553524c61eba0ca194211ddd94254430e4a84216a29966562544400c2b2b96a7288811d9d85154142c9cc7310a8186555398452103122a0c4a0a214b5d05394a1095ce931a4210c7b7654050086a6b98a929421591c96354440a3ce92a2869866b65549401030f322c62a0219918a514c440cc8a830a859062e64548308423bb8acaa1661391c96110c41cacc7288811056472592510c237b92c32a2219a54b6050830c5aa9b12621861f6454d311031b2a4c2200619398e6215210cc8c4a8a832053674182518830eaa2c6204411d5c46510930a9ae5a9ca62046f72586540c338b0cc0298411ddd95114720c5ca93108018656535845210237bb2a4290879394c624c4408daed29440106656508520442b3396a3288618b1936254d10ac8ea90842984767119543043353acc110a411d1c56510d208f4e03288790d647154832cc272bb084188431edd95014232a5ae4302a81861e5458c418c696baca821043999496108210cb4c6b00a810e4f6314950506973a6a5296631b1c96194e408d8eab22649054c7254c5344237394ca98a8139ddb420c4218eae232e87106a462d09411069a3a2a2a0c610fdd95415032d4ac82104288475711964308236b94cb208611b5da520c210cc8c528a82105c573991210870eaa6c6a08614d5d063145429cce3304659066462545418c32a29ec299243d154e5294440cccc528c200872552504411030eb2a86218418e9516010b208f2ed294401061e6550c43486aab98c128c419cd955150040a38e8a98a68863765d854210a3ab8cca992819598e6115020acae22a042907255494a510c33830ec0aa261a350f6254443caac6b08a90870d535494010333294c228861b29c86050d30caec731ea2a164f65949300c29b388c0aa06187191534c440c6ac9308a40854e7394d324832cb1aa0280858d9916114e10b1ee4b028621c7776548214423bb8aca996819318f6255120c5aa9b12821847671995424c2b2392c32a2210f1d1650c9108bce7b2e858847671d9742cc3922a6c4a0a21599c66094840acae3b26a498e3464145504cb26b18a410a61875954310c21cb2c7300a40863954580310c2ab39ea528881179ce6588440acaea2108210e5563984540432ca9ec0988818dd5061509209cae43206390e6562987538863a3b264a88819c1456008540c5ec8292a098e7151d81410c23d380ca2102117dd95314d20a9ae6300a498e2e649885384334a92c0290839918a514c640bc0e2a1640904e47458831086973a6a5290619358e
  | 15 => 0x6671982520c333312a2288810f9d3650c010c9aa7b12622066a5258021c428e3a2c2a98810f5d0650c421bc0e4a0e208870d4310e520c2b338ea5294618dd9151484408eaeb30c8610f155354540102373b0a8a12411b5ca6094643c5ec8a92422056671d4a5290e3bbb2a228a850fdd95410230acae3290422064e5398852103162a2c421a418bd906255110cccc528c8110665529862084326a9cc518843535cc40548408eaeb3224210c6f725865390333294c2288811bdc96550730a38e8b12a620565721442150333290c2994219958461948409cae33168610e5b63181544c732a94c229061471cd6155030c70a8b00849847471590524c22fb9aca10a81b198f31c84218daea3126308565719815210326318c4aa221551cd6254430c9cc7290a22052f72586540c237b92caa0221b158c3208710a70e0aa0a898c3e74d9632442b4382a4292879958a6114c10acae5aa4a21846e7614950506b238a86292838b55062503208bce7b28800861e6458c520432b298c2990210f5da54900408deeca90a518c7575190310872ab1ca2200615c9c04354620c6aa930c8618d6772590514ca373aec4a0a639919461509208dae532c8708665521853204362b186210e419958a61150319ceeca1a4210c6d72d963004316b22a5a88611d9d8534c710a9ce6304a508664629453108273baac420843171cd6550110ae0e0aa0a29951c7454d4384317322c429c21175da5314840a3cec2a2879866652584400c28fbaac0a18878e9916015021a3ceaa18868852c72550544423a38aca994819c585501404393eeca18a421d547158953102963a2c2a9421599c85394440c9ec6312a68847b70595434836331a4228043591c95148440cc8e4b08a81966462185544c33930ac0296219998961d53219ccec2a24210c7a701943250672b94c3a184387d936354910da262b00621843d76950520c32a318a2a82855adc154d4931ad6e0a9ea4a0c757694c5150a3b388cb218410fdd95415321c38c9b1aa6886556398454082973a0c029263539c86094c40bc4e029a4210e4f6314e21482373b6a4a8283691d12108640c3ac9318a7105367494f214872b31ac32a2434d9d35254430ca8c7b0aa888476711815310b16aa4c4288618e9516010c30acee0a90428865453584324421eba6ca180418b1936254910ad4e031ca50845d73d9741c83a299064a8c411b9c8650c010acce5a8ca3a1d6671151520c3393acc190a211d5c6658ca40cb2c7300a80856572981510c31caa4c01906199189514c63087eecaa0a810565711482150237bb2a429687561cd501414187ce932a65885657118c52507172a6c4988615a1c153d4941ae6e0a98a2a1570705445150f46a1ac428887595c754948308dce432a860845c7359542442b2ba88210e41399d26348421c9c
  | 16 => 0x23a3b284a8c410fdd1650c520cccc4b08a90870d5354b401022fbb2a629c43491d15208510acae5304a22065963980540821e3a2ca98241595c75294830bc2e3b12401066452984424c72c29ac0192211d1c56394840bc0e498e20887447154c3208636b94caa1e214b9cb5495331ac8e8a9043885a47250441902b2baa4210c818b5516210030c5ec9a92a098d4c73548524432ab18c728c419598e6115010e48a8208429066962540501061f3a0ca10a619358e62152308e8e2b10a6a063954582430c3322a0c4a0a219959651c82208ecebb0a849943e741815308726318a4a828387d95544c0308ece2302a99967165947208823b388caa18414d9c75495332c6cc8a88a2186a454189414422fbb2a6298813c5c46050f10ccac4b0ea81843d7499532c4236b90c02a2218b15062505108b8e6b2a408847a70194430423aba8c9988431b5d6620c2108eae232a86104e57198a4308636b94ca2086117dd95314d42b8ee6b024210e5953580530871aaa4c2288618d5905108540c6ac8a88a2185587054c5350b8cb80a8a1e618dd9264d45328dae532a62a045d7694e300c237390ca21843d85495150040caca7308a22066762945418823bbb2a228c41399d365484218dceca9282205c6739912108733292c218421395c064484218bae6328848856572151510c34cb1a80202415c1c15314542b4ce931a4210c7576d4f100422f398ca20a411b1c96394440e2a8621aa21851c73589540c21fbb2a82a2611b9cb65d0730e48a830a84906595398042102b9b82a7a8a851ddc56510d21caac7308a40864d6358854842b238a8629263395d83108520a38e8a9a871043f76550544cb33baac2190434ddd954104218bce632a82104e672982414431a2a2c2212211d5c765d0b309c8e4b088618d577358951882b9380c928c4139dd921140218f6eca80a19947b765405010637394c1aa021171cd6550120ccec430aa8986996350040442b338ea9290619694d600cb20c3aa8b18a810c3e74d943008237390ca20a61b118d5348421ccec528a631046d76d4c328867238ac421e438b99252144308dceca926218477715954348717b2ca4a00819c945600c6208e8e2b28849866465185324832ca9cc11904199989510c2208dce5b2e86886665318931c430eb2a8621c418b9526214430ca8a631262884747159532103932a4a5288611d9c46510810aace6292a220724745482144332b14c3aa6651b9db5454830d8ae73224210e4d63548521027238ac421e6599189514c640aaee2b14a62062d64948510c23dbb2a0282870f9d0654c810acae2290429856671d53208831caa6c0a0861595c46414931c9ac7290a2205677258d5188237b92caa1a21595cb51944308ecebb24628859970d5143cc296ba6c3a92638715163d0130c3aa8b18a8085
  | 17 => 0x8065561c16254c408bee6b2a80906a6541854210b32b2ca588421595c85108530c3ecb2a26018565750c421c82aa39aa228a419958a61d5030a70e0b12a81852c74548524c23ab88caa10611ddc56414930c5ca8b10801865a53580431022fbb2a629e415c5c032544309caec208429064d63548400c332a90c2a1061999506150b208dce432e8610699435805110e3ab8ecba1a43875926314c21d8ea630a649056775d08214438d2a2a6a0081179cc64540219c8e4b088798c7571594400427238ac5982410f5d265084308d8e4b2882985727018c5150ab3396a9884211bdd56210030aaae6202a22046d7694e21c826cb80c6908619398d5210210cc8c528a821862e6458853042aab98c828a6599dd56110821acee2b20a498e3854580414823b3b6a4a8861b150c614c8328bce6302a810e6465d8542482d5b9282a00814b9d25450920c5ac829064a06577654c3108752324a8908431ddd93254440c9ca7b12622047975181430823b388ca21e411d9d85154132a3eeab0a8621c6e76949410c29ab8ec8aa0619394f62504408e8e2b10a89862d64588530424fbb287a888739dd95448421c9cc6b10a608477765444088236bb4a829263d154d2108440dc0c5b02628843d74196320438aaa2a298061785cb6144010d8cc79944210cea7598221482aab9e8428a651bdc96195230acce5a9e210851c735514388338a8ac1988611bdd56290020cc8a530c84a0e65529844084236392ca982211bdc96115130ae2e0320a29943f74595204423ab88caa1c41539cc6014941cceca30a64196e261d4220482b238ac52a24117dd95314d41acae1a10a2a172952500408423a3aac321a21475c36550c43caac6a88811066a52580320c392aa2a4a8861b8d8460509208eeec992a218637659454010317aa0c4a0a21595d442d04218ece3b2c8790657631455050ab3b8ac6a90810f5d063540218deeca90a4a0e99635004088386aa4a49806159dc543149418deeab1081086685258021502b2ba88410e2159dc56494a10a5ae8318a4a0e665218542842b338ea7904411b5d76250610cceca312638864d639484084370316c0a0a219c5855014042ca8c7a8aa0a164d535885310237baac2210431ddd95114632ccaa430a84086365458443cc753aa0c4a0a21995944210421ce4c2b00a810d65720c1510c22eb9ecb212210f5d263d41218eaea30a85107154310c5150ab3b8ac8a9061b118d43484218eee2b16a0a1c3c74595304422eb9ecba12219c9856015031ac8e2b22a4185e3704865008637394cb988819914c614cb208dae5b2e839851c7550c434831db20c0aa2631e1d56010d20a6ae829ca3105567614d314423ab88ca21841179cc65d0a10caac628842985647548421d034cb2260184219cd96514c030ce6c2302a898e1f6594d401
  | 18 => 0x581280942e401001c0281c017c0b40082040dc68403001029002005c1c407800406001000802803806c0181ec13c0600001000381ac07400400437401404000c00009c0a09b81140140740e803002000007401507c00c5e8fe4000008260020e9400403800802400013471403c03401401011009801000002400804c00000800001c00408802c00c9cc3fc04c00001c0ea35405401c0bc07000407800800412803412805800000805400005910000407c02051c00000804400401c01401000803c00400c3941240a007800406c0080280003d00b83d42350a00082341ac38c0d825c3180900140281943b400000c01400401c2b40102340f000c02801c02400000808007424402c0140080100302c40040180b000000400c09800488012c01414c0180084f1b5c02c06800c31e5ec01801817c0000ac0840040680501702200241d02ac02800c1940187dc07c02418400016802820c06000006003800c4180bc1443a400801801ea440000100380a411005c00c1e804400c0340cc016ce801400004800000003007008005c4300100340400040200a401800000000000c7e443401018c21c378b0c00004c00000c0781d404406400009c2140940640840080040000c001800002c37801000000003800004c00000003c10c02803800024800402400436800008c0500143f000c0040640041a80002a00dc05000003803801c1040880080001d82004cc12000404006c00004000c66457c1441300300040001ec0b40280000041787280240104f001c24800801801802404c00c0080000500300000900100580141380e801800004402802c0040ac0000740081303d416412000639809c0b004c0141780300302f40000081cc02f1bb20c2aa2410f5da54904418eeeab0c80086696598a1004236b94cb18c819558e6115021b1ee4b0a8621d657214c21c42b2b8e8629263c61c1544c030e4ca8a92a21856570cc8514cb2d31cc02a0431e5da5184010cd6c4302a89951d73550430c23b38ccb190211ddd942d45329c8e4b22638846f7654c320868fbaac4a1887175cf6510020b30e0a1a809861f6550c4308726b1aa4288811b1c96550d108ecec29aa22064e635885488332b14c229c43a65806050c43acaea1906210f0d5494b300c273baac418843565d4404c030ccacba108210e6653189314429b3a0a528861a999341c8421ce0c3b02a89947b76540504863b38ccba1c419394d620c621c9cec29a64906576314f214423bbb2a228c8799149610c910c6aa8b0880184e47650521086a6b9ca41942159dc96494620ccca430a6420ce47650d2108735292c0210811ddd94254440c5aa83128398e6762945311023abb4a990a211d9d852544308dee4b2862a05987050d40cc23cb80caa18438d9526114430acae229aa4205647154852d02b238a64a
  | 19 => 0x59c00002002c05007c0740900000940001c40000180300381ec00808c0b402400800000043404c2b001801406c0042b86fc0001240c003c05802c12800000029806800414c01401c2784d014000000001c13c98c03406c01000400003400c06813407c0140bc008020a780080f80782901fc0980140cc0a41c00540040e400406c9c00380300000280740100000780180000000a82500cc00030c2e43303501080300000c400800804400818c0200280300b40200cc00805831c00407415400000c05413c950000014c280100341001c805c00000007c00010001c0480e813006c07c11000008000d92001402c09000005002063c04037c00c00001400800801874420409802001c014558000388b100040540040000380b003c07d9cc0140180100040000080040940005640440040080100101201580101820a800000410017800c01401803c13006c0b400c0b801c0080080080041a402c0000000040041400480f03b40b005c08803de249080952f407407405001802c0840380000541fc00810003802400c50c79c0600180ac00c0640680000285040601040000500081e40a8060000008000e7c5a45f000000401801800825400c00c0000580140640000780000080040040780980000680840001f00c80043322a40c40000043b80480040fc1ec03c0b000001400c0040380000100bc04802c73001d50807410855800c0140180200180940d400004400005c01000000414000800402821c0340880040080440cc0000187c00080540219d402c0002f400c00c0841700108780100a400001c0b455c03c00c00c29800c0000000000001e00080743cc0000981b80096e809801c27005c03c05407c01c00000400400406000005804400400c1540000681a80f82c023c1b801400c06c08511c00001c0000080241141e404006c6e400804c03c00007800863c3900781dc00802002002800000043c07004000400c0840500081500142dc0003b80980041381bc01405c00007801809038c04c000008008008038004002cf40240000a000000c1dc14c00c00000402c02005000037c00817c00057400001808c0000080000740040f00000580000040b80240004e402802c02c00c08802800014c00006401002c08c03407c00002c00000808400003001c0000582181800000481f00100c826806448000800403000000007400816c05409400007c0180001c00040000d800000c0000040fc00805401401c00800805000006401000c06001000001030801c0680040000082000000140000180080000381
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x95150620d21545c05448421d40535c03108520c29645c06414931e09635494010210a2684d486150931e0964549300c210e11535056010440b09821c1544c030c26541c96110f318e1801d84348421924875494110610a25861504108520a44835886254430c24541c562d012092684dd73108720d07741cd520851092687d494110531c51635c06314542a90815806050c43e21525056010440aa0815096010840c26541c56210f32ac0824c5600c430a24845846154840c46631c56215332a85839d06448421a4483548614ca40a4483548614ca10a4683d48614c941d05541c5320c830b09821c14354043ca1645c04108520c46631c96115331e0543549611484394683dd74208710a85849cc6348421e09535096010840b418314920440109c1801cd2108430e4163485501402192684dd73208710c25651d12108440d20545c04108520d05531c94110440d09435c04354a10a24845886254440a458614c3208510944835d52108640a24865084254620c24541c96110d1094683dd74108720a88825806050c43ac0814c9600c830d047454d2108440d11435c04354620c467314b6150931924845d43208510a24845486150a108a684dd84348421c267414b614c941c4473189514c620d40535c03208510c24541c56210d20d057550c43484218c686dc5424c832c31645c06414532d41325c03254430e21644855014021c25761504208510c25761504108520c4473189514c640924845d43108520a24845486150a308a6849cf6048421aa0825056010440c44531c562cc120d05431c55214843d05531c54210840ca1645c04208510b11811c15350040c847650c4348421e41524c5600c430a44864c83254620b11811c1544c030a19801954310d218c6839d36048421d21425c04254440e05435895114443a44835846154830c24741895150630c457614c3108520d057454c5348421cc1635c031085209a1801d12108440c44531c96110d10a60825456014443a24845942148110a19801915348440cc1635c0320851092684dd73208510c24541c961d0110a188550d6010d10e09544c9600c8308c686dc9414c4318a6849cf6548421d04741cd5208510c44531c56210d20c1a765c05450f30d05541c9310c430e11635454010220924845d52108630e1164545300c220a458614c310852094487549310c610e11544c5600c430c19545c06348430944835d4420851094683dd74208510d05545cc5448421a188550d6010d20864865d44348421d0474dcd5208510d41535c05348421e09435496014843c457614c3208510d05541cd2108430a25861504208510d20545c04208510b09821c15350040ca1725c46050d40e11435456014443a60815496014843b11811c14354043b21841492044010a44835942148110c45651cd2108430
  | 1 => 0x2f06001f08011a000c0608313b201d0a01440a01023605022e1600020815280807051149020120010202050002002307020c153916028c683dd84348421c49635c06314941a278650842d4532944835d44108520d05431c95114443c44531c961cc110cc1725c46050d308c6839d36548421c247418
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x300040500101000080400010070000d00aa10498ac018861421961517010821443402a641282b008220510658535c03208510c80aa30039a4210861a0143209515805110e903203b28621a4210d012597550c4348421d00a9902a12c0210818216560074484211028832c29ae0188429068050c815496014843c20b2b0039a4210861421961517010421483402a840a64b0064185406407454d2108440
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1798
  | 5 => 7915
  | 4 => 3074
  | 3 => 145
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
  | 5 => 2*((h/2645+packedAt gbK5 (300770+(h % 2645)*13) 13) % 7915)
  | 4 => 2*((h/1038+packedAt gbK4 (150626+(h % 1038)*12) 12) % 3074)
  | 3 => 2*((h/55+packedAt gbK3 (8700+(h % 55)*8) 8) % 145)
  | 2 => 2*((h/33+packedAt gbK2 (1136+(h % 33)*4) 4) % 16)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe07ffff03ffffc0f1e3fc7fffc7fff023f1ff
  | 1 => 0x1ff81f8ffc0fc7ff01fc7f8e07f8e071dcce67
  | 2 => 0x1fffe00ffff007fffe007ff007ff007e1f0f87
  | 3 => 0xe000000ffffff83fffff800007ffff8fe00ff8
  | 4 => 0xfffffff00000003ffffffffff800000ffff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xc23041011820800010208c1230c123100150ab
  | 1 => 0x4452c61228e50a8b00e4348453484520ccc665
  | 2 => 0x88a18b245143951572005920a5920a46170b86
  | 3 => 0x1c51448828a01a6a549000106249c0b600d50
  | 4 => 0x11061800e30c2638c9926249c000100dbaa000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeaea80feeaea80feeaea80feeaea80feeaea80feeaea80feeaea80feeaea80feeaea80feeaea80feeaea80feeaea80feeaea80feeaea80feeaea80feeaea80, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_40045
namespace PEqualNP.Outside.L_meta_40045
open PEqualNP.Outside.L_meta_40045.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 16 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 49 := block_range (n:=49) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 145 := (concat bgb_3_0 bgb_3_96)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeac0feeaea80feeaeac0feeaea80feeaeac0feeaea80feeaeac0feeaea80feeaeac0feeaea80feeaeac0feeaea80feeaeac0feeaea80feeaeac0feeaea80
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,6,38)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,6,38)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808384 * 2 ^ 32 + 4276808320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40045.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[2,6]⟩,⟨.or,[3,4]⟩,⟨.and,[2,6]⟩,⟨.or,[0,9]⟩,⟨.or,[5,8]⟩,⟨.or,[0,11]⟩,⟨.and,[8,10]⟩,⟨.and,[7,12]⟩,⟨.and,[1,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808384 * 2 ^ 32 + 4276808320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808384 * 2 ^ 32 + 4276808320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40045

open PEqualNP.Outside.L_meta_40045 in
theorem PEqualNP.Outside.L_meta_40045 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808384 * 2 ^ 32 + 4276808320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808384 * 2 ^ 32 + 4276808320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
