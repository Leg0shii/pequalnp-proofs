import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36673.Model
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

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

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
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
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

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
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
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
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
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
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


end PEqualNP.Outside.L_meta_36673.Model

namespace PEqualNP.Outside.L_meta_36673
open PEqualNP.Outside.L_meta_36673.Model
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

def mirrorSteps : List Move := [swapRows 32,swapRows 67]

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

def checkRow (g : Atlas) (k i : Nat) : Bool :=
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

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_36673

namespace PEqualNP.Outside.L_meta_36673
open PEqualNP.Outside.L_meta_36673.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x60003472a43c000066201b86002a1635c058446609261376b02852521039a7d504378c70800e080041040210223fe43fd43fc43ff31fe31fd31fc31ff40fe40fd40fc40ff30fe30fd30fc30fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x8417e51083eca2105d94420fea88417d51083eaa2105d54420fe28841ff31083fc62107f4c420fe188417e50083fe80107f90020fea0041fc40083fe60107f8c020fe98041fc30083fc40107e88020fe90041f920083d240107fd5310bfaa621fe54c42fca9887f55310beaa621fc54c42f8a9887fd4f10bfa9e21fe53c42fca7887f54f10bea9e21fc53c42f8a7887fd0f10ff21e21fd43c43f887887fd4b10bfa9621fe52c42fca5887f54b10bea9621fc52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fea0e21fc41c43fe63887f8c710fe98e21fc31c43fc43887d88710ffa0621fe40c43fa81887f10310ff98621fe30c43fa61887f0c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa9421fe52842fca5087f54a10bea9421fc52842f8a5087fd0a10ff21421fd42843f885087fcca10ff19421fd32843f865085f54610ffa0c21fe41843fa83087f10610ff98c21fe31843fa63087f0c610ff90c21fe21842fca1087fd0210ff20421fa40843fa81087e50210fe20421ff30843fc61087e8c210fe98421f930843f861087fc8210ff10421fa20843fa41087e48210fe10421ff10843ee21087ec4210ffaa2217f54443fca8885f95110feaa2217d54443f8a8885f15110ffa9a217f53443fca6885f94d10fea9a217d53443f8a6885f14d10ffa1a21fe43443fa86887f10d10ffa92217f52443fca4885f94910fea92217d52443f8a4885f14910ffa1221fe42443fa84887f10910ff99221fe32443fa64887f0c910ffa0a21fe41443fa82887f10510ff98a21fe31443fa62887f0c510ff90a21fe21443ec42887f48510fa90a21ff40443fc80887e90110fea0221f940443f880887fcc110ff18221fa30443fa60887e4c110fe18221ff20443fc40887e88110fe90221f920443f840887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8086f950109f2a021fd54042faa8086f550109eaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087794c10af29821fd53042faa6087754c10aea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087b94810b729021fd52042faa4087b54810b6a9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xe54cc2fca9987f55330beaa661fc54cc2f8a9987fd0f30efa1e61fe43cc3fa87987f10f30ee21e61ff52cc3fca5985f94b30fea96617d52cc3f8a5987fd0b30ff99661df32cc3fc65987f4cb30ee99661fc32cc3fea3987f94730bf28e61fd51cc2faa3987f14730ffa0e61fe41cc3fa83987f10730ff98e61df31cc3fc63987f4c730ee98e61fc31cc3fe81987f90330fea0661fc40cc3fea9185fd5230ff2a4617e548c37ca9184f95230feaa4617d548c37aa9184f55230fe2a4617c548c2faa7187fd0e30ff21c61fd438c3f887187fd4a30ff294617e528c3faa5185f54a30fe29461ff428c3fc85187fcca30ff19461fd328c3f865187fd4630ff28c617e518c3faa3185f54630fe28c61ff418c3fc83187f50630fe20c61ff318c3fc63187f4c630fe18c617e508c3fe81187f90230fea0461fc408c3fe611877cc230fd98461ff544c2fea8987f95130bf2a261fd544c2faa8987f15130be2a261ff434c3be86987f90d30fea1a61fc434c3b886987fd4930bfa9261fe524c3faa4987f14930be29261ff424c3fc84987f50930ff99261df324c3fc64987f4c930ee99261fc324c3fea2985fd4530ff28a61fd514c3f8a2985f14530ffa0a61fe414c3fa82987f10530ff98a61df314c3fc62987f4c530ee98a61fc314c3fe80987f90130fea0261fc404c3fe60987ecc130ff18261de304c3fea8185fd5030ff2a0617e540c3faa8185f55030fe2a0617c540c2fca6187fd0c30ff21861fd430c3f886187fd4830ff290617e520c3faa4185f54830fe29061ff420c3fc84187f50830fe21061ff320c3fc64187f4c830fe19061ff510c3fca2185f94430fea88617d510c3f8a2187fd0430ff20861fd410c3f882187fcc430ff18861fd310c3f862185f94030ffa0061fe400c3fa80187f10030ff98061df300c3fc60187e8c030fe98061dd300c3f260187fd5220bfaa441fe54882fca9107f55220beaa441fc54882f8a9107fd4e20bfa9c41fe53882fca7107f54e20bea9c41fc53882f8a7107fd0e20ff21c41fd43883f887105f54a20ffa1441fe42883fa85107f10a20ff99441fe32883fa65107f0ca20ffa8c41fe51882fca3107f54620bea8c41fc51883fe83107f90620fea0c41fc41883fe63107f8c620fe98c41fc31882fca1107fd0220ff20441fd40883f881107fcc220ff18441fd30883f861107fc8220fd90441ff53482fea6907f94d20bf29a41fd53482faa6907f14d20be29a41fe43483fa86907f10d20ffa8a417f51483fca2907f54520fe28a417c51483fe62907f8c520fe98a41fc31483fe80907f90120fea0241fc40483fe60907f8c120fe98241fc30483fc40907b88120ffa98417f53083fca6105f94c20ef298415e53083faa6105f54c20eea98415d53083f8a6105f14c20ff21841fd43083f886107fd4420ff28
  | 2 => 0xc7f8a998df15331ffa1e63fe43cc7bc8798ff50f31eea1e63fc43cc7fea598ff94b31bf29663fd52cc6faa598ff14b31ffa0e63ff50cc7fca198df94331fea86637d50cc7f8a198ffd5231bfaa463fe548c6fca918ff55231beaa463fc548c6faa718ffd0e31efa1c63fe438c7fa8718ff10e31ee21c63ff528c7fca518df94a31fea94637d528c7f8a518df94631ffa0c63fe418c7fe6318f7cc631fb98c63ff508c7fca118df94231fea84637d508c7f8a118ffd5131bfaa263bf544c67ea898ff95131bf2a263fd544c6faa898ff15131be2a263bc544c678a898ffd0d31ff21a63de434c7fa8698f750d31fe21a63ff524c6fea498ff94931fea9263fc524c6f8a498ffd0531ff20a63fd414c7fe6298fdcc531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031df2a0633e540c7faa818df55031deaa0633d540c7f8a818df15031bf29863ff430c7be8618ff90c31fea1863fc430c7b88618ffd4831ff290637e520c7dca418db94831fea90637d520c7daa418db54831fe290637e510c7fe8218ff90431fea0863fc410c7fe6218f7cc431ff18863f6310c7fa6218f74c431fa98863ff500c7fca018df94031fd280637a500c7faa018df54031fca806379500c7f8a018ffd4f40ff29e817e53d03faa7a05f54f40fe29e81ff43d03fc87a06f90f40fea1e81fc43d037887a07fd4b40ff296817e52d03faa5a05f54b40fe29681ff32d03fea3a07f94740bf28e81fd51d02faa3a07f14740ffa0e81bf41d03fc83a07f50740dea0e81fc41d03fe63a07f8c740fe98e81fc31d02faa9207fd4e40ff29c817e53903bca7205794e40fea9c817d53903baa7205754e40fe29c81ff43903fc87207f50e40fe21c81ff52903fca5205f94a40fea94817d52903f8a5207fcca40ff19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640ff20c81fd41903f883207fcc640ff18c81fd31903f863205f94240ffa0481bf40903f681207fd4d40bfa9a81fe53503faa6a07f14d40be29a81ff43503fc86a06f90d40fea1a81fc435037886a07fd4940bfa9281fe52503faa4a07f14940be29281ff32503fc64a07f4c940ffa8a817f51503fca2a07f54540fe28a817c51503fe82a06fd0540ff20a81fd415037a82a07f10540ff98a81fe31503fa62a07f0c540ffa0281fb40503fc80a06f90140bf2a081ff53103fca6205f94c40fea98817d53103f8a6207fd0c40ff21881fd43103f886207fd4840ff290817e52103faa4205f54840fe29081ff32103fc64207f4c840fe19081ff51103fca2205f94440fea88817d51103f8a2207fd0440ff20881fd41103f882207fcc440ff18881fd31103f862205f94040ffa0081bf40103fc80207e90040fea0081bd40103f280207fd5330bfaa661f
  | 3 => 0x7c270000007c450bc50009ea5de0cc16000000005c6001810e5226000000000005760000000000198a53800098d008147d8b01b0002b7558f826e34dcf40032a074000000c9800000000004660000000000000000000482b280000000063420800664000ba19f7558f3c9f9e70a0100000000030418b4375a779ada6d74abea5780021e378003c10007291d00000000000000000000a4dad1cc000a82b800000000000000000000000009700000000000089d641fe000d5bac000000802802000000801800000003800000801800001000800002801000002004000001800000802800000000002000000801000001800800800000000001000000001800001002002000006000800000800000003000000000000000000000802800800001800000004800000807003006800803000000000801000800002801801805800800001800800000000000001000002800800800000800801000001001000000800000003000000001806000801001000001000802001800802000800000805000000000000801002001800000800800000803000801000800000001003000000802000800805801801000001005000800800005000000000800801802801000800000000004800805800000002000800000000001804800000002001001006801000800000800000001000000007000800000800001000000000000002000000002001800800004802801001000000002000000001001000800003002801001800000000800801801001001000002001000000000005801803000000005800000800000001801800800003001001000002000000801000002001800000000802003000800001800800001000000000802001802800000001803800001800000800800800800000000800000003000000001000800800000804000000000000000000001000800000802801000000800000004002000003800000000000800006003003800000000000804803000000000003800000004800800803800000800800800000000000000000000000800801801000001000009001001000000000000000800801002000000800800001000000001801000800000801000800800801002800800000003002800000000803804001800801000801801000df55243bf29c87ff4390fbe8721ffd4a43ff294877e5290ffaa521df54a43fe29487ff5190ffca321df94643fea8c877d5190ff8a321ffd4243ff284877e5090ffaa121df54243fe28487fe4350f7c86a1ffd4543bfa8a87fe5150ffaa2a1ff14543be28a87ff5050efea0a1ff94143fea8287fc5050ef8a0a1df94c43ff21887de4310ffa8621f750c43cea1887ff5110ffca221df94443fea88877d5110ff8a221ffd4043ff280877e5010ffaa021df54043fe28087ff54cc7fca998df95331feaa6637d54c
  | 4 => 0x2cb0000004e1eb88fb5e1e70000000025c001710ea000000000000000000034b0000000000027e001a0800000a2c001b5000000a700055252c308003d4618002920000011b278702000000000000014c000508000000003480009bc0000000000000000868001b3000000000003581688c8001bfb92002900001d82389c6c041800000000480d50001e9000000000000000000000009dce8000000000000000000000000000000b610d87600142a284959009c800237c4000000000000002bb26440a0024a76a06c00000000b58128005d00004242e6ba8400000016fe1b2816a48d001b6400424000251f1c3cca0000003b5001d06b9636cf9b689b10c0005700000000157445a100000000070febc000003e4001e30000aea98000000f351fafac5000000ed2623b12c8ed8452adc8c003138000007c12f000e11bf301128a1c00000000000000770007811093a9eb6bc3d7712428c03f8000001700000000086a7b18dc1c3b40020d16035c0000000000000000000bac00000000000000340000004a400000001578000adbd400000396b810b45e1888ed96800000962db4003fa710002e60000000000000074c0028149cea8a2c0004289800000000000000000000003a4005bc9c1498006e66c316a6f2221c43e807e6c000000003d62480000000000000000000ab000000303000002cf80000000000000000003b4000000bf1ce088000000000000000581e8001c00000042f00000000327ad00025a0000000000017b00000000000000000b8230000b68001205f6be000000001010003caaf1116a9f49073900000006c75883e000001820001e40000000000000000000000001db800000000003a30000000013bafd000001dbd003be92217710998f1887c8ce2edf72926c0000b8bf72e001b8554660000001f5f620002be4362e708fa800000000000001c0536a640016654d9dafd1169e2000007700007ea953e82f5788d92b5000000005ed00000000000b640000000015800279000000a199b2f1000000674610000030d4315c8000000000000000000000000223000d1000000000b34003a72bd00000000000651a2b4a2885e0ce9e700c001ad15cdc26cbdc8006b0000002ce0002ba00000704001ba286000be1a68004f300074000000620000000000000000e000001c8000000d1e00055430a6c0006a0000006040000047e000000000a817a835c7000000000004cf4140000000000348820585ce000000e9ea3000000000000006450014bcba8dc6780000000007e001d92a2ed8c2400258e8bb82d280012c443c75f62e40013700000000000283570a46455d29ed3d2d40006d04b3a58d86f8001526f4a52ec0000006a50600072b0019a159ab0b099339f012000000e360a0000012a0000000000021828312800022476000000009
  | 5 => 0x24651a774000001d68a000000c56e6a9900077de20000003014b8003c79807100a0000009cc0000008c00325d4ac9c0000038ee5a16b0f3f836000000000001df9bf0c4124e78000000000000000000100ab202b000003090000000000028400000181000e491b8928000014e80042816a8822a497b3c002420005c55995fae0c19018000001daeb2d5000390002c000000000000000afc00000364000db80032a86d1010063e7e41b858000588f96c33764f52cba1000000002321970006f885ba0190042d81e855e00000000e22001f86db001853a6800276cc0000002540000071a9d929033598000b1a6319000035d7f8da000002733d09245b296800810121f30000005bb5300064c000826984f2000010000000011c8006993e940000b2c0018e3f35e6002a1000d9400000000000000003d3000c38a3444dd95b000000000000003f7000818000ef91c002f669000106d2634a5948d4f1cae00000000000001750dd40cb9d729dc0869950e00044d79a528000000000025600007400000000000b0093000515d323d800d859c1a7c175e80022f2bc744000000005eaf14f558e000002821f83e956800000000000005340f4000000000000000003800000000622309a3147000696cb20506b7240024b000bd1ca1cc0ea000c14ad12229c002d08000000027f71221c00000000000000000000000034e00000151000000000003a980000000000000000001ff000e64c18a000009b838000000005d8000003bc003515a233400000000504000000004f6851b900000114b7d5cde3ca426723d09e003b180014000000000001c188c47a0018c1f6800001d58ee18c000002a4000ec8000003780000017b2f75cda3943a748443d871aaab221026fc3e000002c852c00109800680cfc000004780000039a000001308000000006511a0800007b4000000019a80013a704003c35efbc8f0a6daba75085a53320a5010ccf000000ba880800000000006b2348fd80053e3501480034600000000000b74002ff0000010756f0002f13900000000000000462289042ef69e000002c95f2af80013e3fc01cc58160a26840027c0000000000021c0000014913753c001a880000000000000000000002dc000000004c8000000001484da34f498340013880057a0012da003d8000001222be2244208e0002db342ee555000c906844e91e0031a0009a9aaba38e67dc3904d0000000000000025c0c3238002d5ae0000000e200000000000000000002d2001ee0003400000054e4e000008adf175e4000000afa001e4000e806e13b1d20e400000000000fb0001680016980000000000000000e4c000000000014502c1b4b040030e00004c2f91d0009f9722161d83e72f18900000000000000000000006328912a6db52bf09170000000000000000049c0000047
  | 6 => 0x140e100000185800f16639d52380018a8f8e28000000002ce34c6a800000e88000e70002a400396000601c3bbb000338a040000000000000000000001a20000008b5d20008251a8002faef898398de600000182672ecc00000674000000005a0c0cf2e3fdeb3ec9a47e26800000033f80000233000009d48f0f280081cdd00038a001478000006684f800000cad8625780000000000512629630000007ce0b400000064558000000000000023300041a6b666000c792096b000000740007980000000000151b6a0000000000005100000000000000000be00000068970992001a900027d00d5fc7c4d2000b43910000000000000000000000000424003674a20015b800045000000000000000000066536c000000000002d800443000b75b00000000000057b00000000000000001e7e167000013353c56800104dee0000000000000075b97800001c31bd8000008bb6f00a6446ec000e7000f48006d2001bdbba6fe0000036380002a000ac729001b70000008e00000000070da9d4c130c9401023edf7bd2682265c000000002434d635935000b5cebb37070720da400432000000000d2c91488000000000000009e00000000000001bb8000006d81b7500005288900000000172c00000228000004146d76d00049e00158000730000000000004340000000000054000000000000000000004680002f00000000370b8b8e115385e300003f000856b593f800493de800000001158000007e82a00000000000028574b71ab0007603cc00000000000000005384a0c2904000a060026c000000d7c000000014733f80000091c0013c56430024800000ecc00490000003a8692000000000002a93a2580005a4003722e397400000000788002c0e26000003218c6001bcb14e7800000000540a2000000000000001bd00000058aae000000000788000018b0000000000000034e6a07f000000dac002b50000c000312700c210aa24c883e400000000a6200000000000000003ba00000000000001b20d600065c00144dda000000006429302c9791b5e55a10005be130479847140d400138b8119400000000054618c8d43c790ea0f6f05356201f22c07969142b3200197800000bb0000006ae922000004ee0ac000000000003ca598000000008500000000080000001de2ab818414003b280000000000000b9e4cb8e17ddf1d48000004a4000000000000000000000000000000000000000000000005203b000c5c000002e806800000670000002fe0000013c00032c0000017f000000dce3a000808000000000024980000035400000000000001e0109cd8001e2000ac4000645f2000000006c4d71075f813e4e5254a81ee000001e1d02000000cc000000006eabc15165580014d1f8001c28f800284df403dd468c00000000000000aa8000000002e600000
  | 7 => 0x2340000008112d2ec5dc090f72034c400122ab6000000000ab00000025979000663662cc1e800126a4b462000000000000000000000000157000a34f574cbda0012ab6c0000000009a1a9001b13543180003792b18a1caa5c006d7d8c8d8f78f00014cc00000120000003c99ba0038b000aa15580000000000326800299b42fe6440f0a5400748000e30
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x6500427d65d0010cf953400433d54d0010d794f400435d53d0010db94b400436d52d00109fd96400427d6590010cf952400433d5490010b798e40042dd6390010d794e400435d5390010db94a400436d5290010bd98640042f56190010de942400427f6550010cf951400433d5450010d794d400435d5350010db949400436d5250010de941400427f65100109f994400427d65100109f194400433e5410010cf550400435e5310010d754c400436e5210010db54840042f66110010bd584400427d65cc010cf953300433d54cc010d794f300435d53cc010db94b300436d52cc0109fd96300427d658c010af99230042bd648c010cf952300433d548c010d794e300435d538c010db94a300436d528c010bd98630042f5618c010de942300427f654c010cf951300433d544c010d794d300435d534c010db949300436d524c010de941300427f650c0109f994300427d650c0109f194300433e540c010cf550300435e530c010d754c300436e520c010db54830042f6610c010bd584300427d65c8010cf953200433d54c8010d794f200435d53c8010db94b200436d52c80109fd96200427d6588010cf952200433d5488010d794e200435d5388010db94a200436d5288010bd98620042f56188010de942200427f6548010cf951200433d5448010d794d200435d5348010db949200436d5248010de941200427f65080109f994200427d65080109f19420042be6408010af590200433e5408010cf55020042de6308010b758c200435e5308010d754c200436e5208010db54820042f66108010bd58420043e92008010cf953100433d54c4010d794f100435d53c4010db94b100436d52c4010dd59710043b654c4010ed55310043d653c4010f554f100437752c4010f994b100437552c4010f954b100436552c4010cf952100433d5484010d794e100435d5384010db94a100436d5284010bd58610043765184010be596100437965840109e596100437b5484010ee95210043795484010ee55210043395484010ded4e10043da5384010de54e10043d95384010d654e100437b5284010fa94a10043795284010fa54a10043695284010be586100437a5184010fc946100427f6544010cf951100433d5444010d794d100435d5344010db949100436d5244010bdd95100437765440109dd9510043b65444010ed55110043d65344010f554d10043775244010f994910043755244010f954910043655244010bdd8110043765044010fc88110043f12044010bed95100437b65440109ed95100437b5444010ee95110043795444010ee55110043395444010ded4d10043da5344010de54d10043d95344010d654d100437b5244010fa94910043795244010fa54910043695244010bed8510043f36144010de94510043f25144010fc88510043f12144010
  | 1 => 0x437661148109d984520427e6014810de980520427a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d0810d794f420435d53d0810db94b420436d52d08109fd96420427e65908109f596420433e5490810cf55242042de6390810b758e420435e5390810d754e420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420435e5350810d754d420436e5250810db54942042fb6050810be181420427f65108109f994420427d6510810cf950420433d5410810d794c420435d5310810db948420436d52108109fd97320427e65cc8109f597320427c65cc810cf953320433d54cc810d794f320435d53cc810db94b320436d52cc8109fd96320427e658c8109f596320427c658c810af99232042bd648c810cf952320433d548c810d794e320435d538c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810cf951320433d544c810d794d320435d534c810db949320436d524c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c810cf950320433d540c810d794c320435d530c810db948320436d520c8109f992510427d64944109f98e510427d63944109f98a510427d62944109f597410433e54d0410cf553410435e53d0410d754f410436e52d0410db54b410427f65904109f596410433e5490410cf552410435e5390410d754e410436e5290410db54a41042fa6090410be582410427f6550410cf951410433d5450410b7d8d41042dc6350410d794d410435d5350410db949410436d52504109fd94410427d6510410cf950410433d5410410b798c41042dd6310410d794c410435d5310410bb98841042ed6210410db948410436d5210410be98041042f960104109f597310433e54cc410cf553310435e53cc410d754f310436e52cc410db54b310427f658c4109f596310433e548c410cf552310435e538c410d754e310436e528c410db54a31042fa608c410be582310427f654c410afd9131042bc644c410cf951310433d544c410d794d310435d534c410db949310436d524c4109fd94310427d650c410af99031042bd640c410cf950310433d540c410d794c310435d530c410bb98831042ed620c410db948310436d520c410be98031042f9600c4109f597210433e54c8410cf553210435e53c8410d754f210436e52c8410db54b210427f65884109f596210433e5488410cf552210435e5388410d754e210436e5288410db54a21043765188410be98221042f960884109fd95210433e5448410cf551210435e5348410d754d210436e5248410db549210437651484109f59421042de6308410b758c210435e5308410d754c21042fa6008410be580210427e64940109f592500427e63940109f58e500427d62940109f58
  | 2 => 0x6254c109f189530427f6154c109f585530427f6054c109f581530435f6554c10d7d51530435e5454c10e7951530431e5454c10d7551530439d5454c10c7551530435c5454c10d7d91530435e6454c10d7591530435c6454c10d7d89530435e6254c10d7589530435c6254c10d7985530435c6154c10d7981530435c6054c10d704153042be6414c10af590530433e5414c10cf55053042de6314c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530425e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109e980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf553430435e53d0c10d754f430427f6590c109f996430427d6590c109f196430433e5490c10cf552430435e5390c10d754e430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d430427f6510c109f994430427d6510c109f194430433e5410c10cf550430435e5310c10d754c430439d4310c10af99352042bd64d4810cf953520433d54d4810b798f52042dd63d4810d794f520435d53d48109f993520433e64d48108f993520427d64d4810cf593520423d64d48109f98f520435e63d48109798f520427d63d4810d758f520425d63d4810dd987520437a60d48109f596520433e5494810cf552520435e5394810d754e520436f52948109f992520427d64948109f98e520427d63948109b596520436f5494810db95252043ae5494810cb952520436d5494810eb552520432d5494810db152520436f5394810db94e52043ce5394810d394e520436d5394810f354e520434d5394810db14e520436f6494810db992520436d6494810db192520436f6394810db98e520436d6394810db18e520436f4394810db90e520436d4394810db10e520436e6194810db186520436e6094810db182520433e5454810cf551520435e5354810d754d520427f64548109f191520427f63548109f18d520436f62548109fd81520427d6054810dbd95520436f5454810db95152043ae5454810cb951520436d5454810eb551520432d5454810db151520436f5354810db94d52043ce5354810d394d520436d5354810f354d520434d5354810db14d520436f6454810db991520436d6454810db191520436f6354810db98d520436d6354810db18d520436f4354810db90d520436d4354810db10d520436e6154810db185520436e6054810db181520436c1054810af99052042bd6414810cf950520433d5414810b798c52042dd6314810d794c520435d5314810bb988520436d52148109f98c520435e63148109798c520427d6314810d758c520425d63148109f984520
  | 3 => 0x110fc88530443f1214c1109f99430442fa600c110f64c0304436f52c8110db14b20442f661c8110bd587204427e6588110be996204437a6588110bed9220442f96488110bed8e20442f96388110be58a204437a5288110de14a20443f36188110be98620443f06188110fc88620443f121881109f595204436f5248110db14920442f76148110bd18520442fb6448110be59120442fb6348110be58d20443eb6248110fad49204437a5248110de14920443e85248110da14920443f36148110be18520443f06148110fac8520443f22148110fa48520443f12148110f8485204427e6508110af99020442bd6408110b798c20442dd6308110bd98420442f56108110be98020443e92008110bed9310442f964c4110bed8f10442f963c4110bed8b10442f962c4110fc88710443f121c4110bdd8a10442f56284110fcd4210443f24084110fc50210443f23084110fc4c210443f22084110fc48210442de63d5010b758f54042ee62d5010bb58b540427e63d5010d798f540425e63d50109f58f540435d63d50109758f540427e62d5010db98b540426e62d50109f58b540436d62d50109b58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e63950109f58e540427e62950109f58a540423d6595010cfd8e540433e6395010cf58e540433c6395010cfd8a540433e6295010cf58a540433c6295010cf986540433c6195010cf982540433c6095010cfd91540427f63550109f18d540427f62550109f189540427f60550109f581540433f6555010cfd8d540433e6355010cf58d540433c6355010cfd89540433e6255010cf589540433c6255010cf985540433c6155010cf981540433c6055010cf04154042be6415010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540423e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a60150109e98054042be64d4c10af593530433e54d4c10cf55353042ee62d4c10bb58b530427e64d4c10cf993530423e64d4c109f593530433d64d4c108f593530427e62d4c10db98b530426e62d4c109f58b530436d62d4c109b58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10cf952530433d5494c10d7d4e530427e6494c109f592530427e6294c109f58a530425d6594c10d7d52530435e5494c10e7952530431e5494c10d7552530439d5494c10c7552530435c5494c10d7d92530435e6494c10d7592530435c6494c10d7d8a530435e6294c10d758a530435c6294c10d7986530435c6194c10d7982530435c6094c10cf951530433d5454c109fd91530427c6454c10d7d8d530427f
  | 4 => 0xfd95424427e65509109f195424433e5450910cf551424427f65109109f994424427d65109109f194424433f5410910cf150424436f5210910db14842442f66110910bd58442442fa6010910be580424427f65cc9109f997324427d65cc9109f197324435e53cc910d754f324436f52cc910db14b32442fa60cc910be583324427f658c9109f996324427d658c9109f19632442be648c910af592324435f538c910d714e32442f6618c910bd58632442fa608c910be582324427f654c9109f995324427d654c9109f195324435e534c910d754d324427f650c9109f994324427d650c9109f194324435f530c910d714c324436f520c910db14832442f6610c910bd58432442fa600c910be580324427e65d0510cfd53414433c54d0510be98341442f960d05109f996414427c6550510cfd51414433c5450510b7d8d41442dc6350510bed8141442f860505109f99441442de6310510b758c41442ee6210510bb58841442fa60105109f997314435f53cc510d714f31442fa60cc510be583314427e658c5109f19531442bf644c510af191314435f534c510d714d31442fb604c510be181314427e650c510af99031442bd640c510bb98831442ed620c510be980314427e65c8510dbd4b214436c52c8510be98321442f960c8510bd99621443766588510bd58a21443765288510dd14a21443f36088510bd98221443f060885109f19521442fb6048510be18121442746548510fcd8121442f46048510fc181214427e65d0110cfd53404433c54d0110bd98740442f561d01109f99640442de6390110b758e40442fa6590110de99640442f96490110de95240443785490110f698e40442f96390110f658e40442d96390110be58a40442fa6190110fc88640443f121901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd18540442f86550110de19540442786550110eed9140443bb5450110de95140443785450110ee15140442fb6350110ee90d40443b84350110bed8940443bb4250110ee50940443f36150110be18540443f06150110eed0540443b94150110fc88540443f121501109f99440442fa6010110ee500404427e65cc110d7d4f304435c53cc110bd98730442f561cc1109f99630442be648c110af59230442fa658c110de99630442fb648c110ee99230442f9648c110ee59230442b9648c110be58e304437a538c110de14e30442f9628c110be98630443f2218c110fc486304427f654c1109f595304427c654c110d7d4d304435c534c110bdd8530442f4614c110be1953044378654c1109e19530442fb644c110be59130443db634c110f6d4d304437a534c110de14d30443d8534c110f6d0d30443d8434c110bed8930443db324c110f64c930443f3614c110be18530443f0614c110f6cc530443d9314c
  | 5 => 0x20843e85248210da14920842f86148210fac8520842be6408210af59020842de6308210b758c208436e5208210db54820842f66108210bd58420843e92008210bd597108437565c4210dd54b10842f965c4210de59710842fb64c4210be59310842fb63c4210be58f10842fb62c4210be58b108427e63d51109f58f544427e62d51109f58b544433f54951109f992544427e63951109f58e544427e62951109f58a544427d6195110dd586544427d6095110de58254442df6355110b718d54442ef6255110bb189544433f64551109fd8d544435f635511097d8d544427c6355110d718d544425c63551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e6015110de580544427c60151109f993534427d64d4d109f98b534427d62d4d10d7d4e534427e6494d109f592534427e6394d109f98a534427d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f984534427c6114d109f98053443796014d109f180534427f65d0d109f997434427d65d0d109f197434435f53d0d10d714f43442fa60d0d10be583434427f6590d109f996434427d6590d109f196434433f5490d10cf15243442fa6090d10be582434427f6550d109f995434427d6550d109f195434427f6510d109f994434427d6510d109f194434433f5410d10cf150434435f5310d10d714c434439d4310d10bd98443442f56110d10be98043442f96010d109f993524427d64d49109f98f524427d63d4910dbd4a524427e64949109f592524427e63949109f58e52443756194910de58252442bf6454910af19152442df6354910b718d524427f6354910d7d8d524425f63549109f18d524435c63549109718d524427f6154910ddd85524437b60549109f99452442be6414910af59052442de6314910b758c524436d52149109f990524433e64149108f990524427d6414910cf590524423d64149109f98c524435e63149109798c524427d6314910d758c524425d6314910db988524437561149109f180524427e65d09109f597424427c65d0910cf953424433d54d0910dbd4b424436c52d0910be98342442f960d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910b798e42442dd6390910bd98642442f56190910be98242442f960909109
  | 6 => 0x27f6454a109f191528427f6354a109f18d52842be6414a10af59052842de6314a10b758c528436d5214a109f98c528435e6314a109798c528427d6314a10d758c528425d6314a10dd584528437a6014a109fd97428427e65d0a109f597428433e54d0a10cf55342842fa60d0a10be583428427f6590a109f996428427d6590a10b798e42842dd6390a10be98242842f96090a109fd95428427d6550a109f195428433e5450a10cf551428427f6510a109f994428427d6510a10be98042842f96010a109fd97328427e65cca109f597328435e53cca10d754f32842fa60cca10be583328427f658ca109f996328427d658ca109f19632842be648ca10af59232842fa608ca10be582328427f654ca109f595328427c654ca10d794d328435d534ca109fd94328427e650ca109f594328427c650ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cf951418433d5450610b7d8d41842dc6350610bed8141842f86050610b798c41842dd6310610bb98841842ed6210610be580418435e53cc610d754f31842fa60cc610be58331842bf644c610af191318435e534c610d754d31842fb604c610be18131842be640c610af59031842ee620c610bb58831842f9600c610be98321842f960c8610cfd53408433c54d0210cf952408433d5490210b798e40842dd6390210bd98640842f56190210be59640843796590210de95240843ba5490210ee55240843785490210f698e40842f96390210f658e40842d96390210be58a40842fa6190210fc98640843f16190210cfd51408433c5450210bed95408437b6550210eed9140843bb5450210de95140843785450210ee15140842fb6350210ee90d40843b84350210bed8940843bb4250210ee50940842f86150210eed0540843b94150210cf950408433d5410210bd98440842f56110210ee500408435f53cc210d714f30842be648c210af592308435e538c210d754e30842f6618c210bd58630842f9658c210de59630842fb648c210ee99230842f9648c210ee59230842b9648c210de94e30843da538c210f654e3084378538c210be58a30842fa618c210fc98630843f1618c210d7d4d308435c534c210bed95308437b654c210bed9130842f9644c210f6d8d30843db534c210de94d3084378534c210f614d30843db434c210f610d30842fb624c210f6cc930843d9324c210be18530843db314c210f64c5308435e530c210d754c30842f6610c210bd58430843d9300c210db94a208436d5288210bd98620842f56188210bed9220842f96488210bed8e20842f96388210de94a20843ea5288210fa54a20843785288210be98620843f26188210fc58620842fb6548210ded9520842fb6448210be59120842fb6348210be58d20843eb6248210fad49208437a5248210de149
  | 7 => 0x550b10cf95142c433d5450b10db94942c436d5250b10bed8142c42f86050b109fd9442c427e6510b109f59442c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c435e53ccb10d754f32c427f658cb109f99632c427d658cb10af99232c42bd648cb10db94a32c436d528cb10bd98632c42f5618cb109fd9532c427e654cb109f59532c427c654cb10d794d32c435d534cb10db94932c436d524cb10bed8132c42f8604cb109fd9432c427e650cb109f59432c42f6610cb10bd58432c433f54d0710cf15341c433e5490710cf55241c42fa6090710be58241c433f5450710cf15141c42df6350710b718d41c433e5410710cf55041c42de6310710b758c41c42ee6210710bb58841c42fa6010710be58041c435f53cc710d714f31c435e538c710d754e31c42fa608c710be58231c42bf644c710af19131c435f534c710d714d31c42be640c710af59031c435e530c710d754c31c42ee620c710bb58831c42fa600c710be58031c42fa6088710be58221c42f66088710fc98221c43f16088710cf95340c433d54d0310bd98740c42f561d0310b798e40c42dd6390310cf95140c433d5450310bdd8540c42f46150310d794f30c435d53cc310bd98730c42f561cc310af99230c42bd648c310d794d30c435d534c310bdd8530c42f4614c310db94b20c436d52c8310bd98720c42f561c8310db94920c436d5248310bdd8520c42f46148310af99020c42bd6408310b798c20c42dd6308310bd98420c42f56108310fa48020c42de63d5210b758f548427e63d5210d798f548425e63d52109f58f548435d63d52109758f548427e62d52109f58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210de982548433f64552109fd8d548427c63552109fd89548427c6255210cf550548433e64152109f98c548427d63152109f988548427d6215210dd584548437a6015210af99353842bd64d4e109f993538433e64d4e108f993538427d64d4e10cf593538423d64d4e109f98b538427d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538437a6094e109fd91538427c6454e10d7d8d538427f6254e109f189538435d5314e109f990538427d6414e10d798c538427e6214e109f58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438435e53d0e10d754f43842fa60d0e10be583438427f6590e109f996438427d6590e109f196438433e5490e10cf55243842fa6090e10be582438427f6550e109f995438427d6550e109f195438427f6510e109f994438427d6510e109f194438433e5410e10cf550438435e5310e10d754c438439d4310e10be98043842f96010e10dbd4a528427e6494a109f592528427e6394a109f58e5284
  | 8 => 0x20fc546200837151880209fd95200835e5348020d754d20083765148020dd54520082fb6548020ded95200827b6548020ee95120083b95448020f694d20083d95348020bed89200837a5248020fa94920083eb4248020fa90920083e94248020fa10920083eb3248020fa8c920083e93248020fa0c920083f25148020de54520083f15148020dc54520083eb6548020bad95200836b6548020fad8d20083ea6348020fa58d20083e86348020fad4d20083ea5348020f294d20083e95348020f254d20083e85348020fa90d20083e94348020fa10d20083eb6148020fa98520083e96148020fa18520083eb5148020fa94520083e25148020fa54520083695148020f854520083615148020fa14520083eb3148020fa8c520083e93148020fa0c5200827e63d53109f58f54c427e62d53109f58b54c437661d5310de58354c433f54953109f98e54c427d63953109f98a54c427d6295310b7d8d54c42dc6355310cfd9154c427f6355310d7d8d54c425f63553109f18d54c435c63553109718d54c427f62553109f18954c433d5415310b798c54c42dd6315310bb98854c42ed6215310cf99054c427e6315310d798c54c425e63153109f58c54c435d63153109758c54c427e6215310db98854c426e62153109f58854c436d62153109b58854c43766115310de58054c427e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f10afd9153c42bc6454f109fd9153c433f6454f108fd9153c427c6454f10cf19153c423c6454f10d7d8d53c427f6254f109f18953c42be6414f10af59053c435d5314f10bb98853c42ed6214f109f99053c433e6414f108f99053c427d6414f10cf59053c423d6414f10d798c53c427e6214f10db98853c426e6214f109f58853c436d6214f109b58853c43766114f10de58053c427f65d0f109f99743c427d65d0f109f19743c433e54d0f10cf55343c435f53d0f10d714f43c427f6590f109f99643c427d6590f109f19643c433f5490f10cf15243c435e5390f10d754e43c427f6550f109f99543c427d6550f109f19543c433e5450f10cf55143c435e5350f10d754d43c427f6510f109f99443c427d6510f109f19443c433f5410f10cf15043c435f5310f10d714c43c439d4310f10bd98443c42f56110f109f98f52c427d63d4b10dd98752c436f5294b109f99252c427d6494b109f98e52c427d6394b10dd98652c427f6454b109f19152c427f6354b109f18d52c436f6254b10af99052c42bd6414b10b798c52c42dd6314b10db54852c427f65d0b109f99742c427d65d0b10cf95342c433d54d0b109fd9642c427e6590b109f59642c42de6390b10b758e42c436e5290b10db54a42c42f66190b10bd58642c427f6550b109f59542c427c6
  | 9 => 0x94e430835d5390c20bb98a43082ed6290c20be98243082f96090c209fd95430827e6550c209f595430827c6550c20d794d430835d5350c209fd94430827e6510c209f594430827c6510c20d794c430835d5310c20e750c43082de63d4420b758f510835e53d4420d754f510835e5394420d754e510837751944209f98e510827d6394420ddd4e51083765394420f594e51083565394420dd54e51083d55394420d554e51083745394420ddd8e51083766394420dd58e51083746394420dd90e51083754394420dd10e51083746094420d794d510835d53544209fd8d510827c6354420ddd9551083775354420dd94d51083d65354420d594d51083755354420f554d51083555354420dd14d51083776354420dd98d51083756354420dd18d51083764354420dd50d51083744354420dd98151083742054420b798c51082dd6314420d794c510835d5314420bd984510837551144209fd97310827e65cc4209f597310833e54cc420cf553310835e53cc420d754f310837651cc420dd547310827f658c4209f996310827d658c420cf952310833d548c420d794e310835d538c420dd9463108375518c4209fd95310827d654c4209f19531082bf644c420af191310833e544c420cf551310835e534c420d754d31082ef624c420bb1893108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420af99031082bd640c420cf950310833d540c420d794c310835d530c420bb98831082ed620c420dd9443108375510c420be98031082f9600c4209f992500827d64940209f98e500827d63940209f597400833e54d0020cf553400835e53d0020d754f400837651d0020dd547400827f65900209f596400833e5490020cf55240082de6390020b758e400835e5390020d754e40082ee6290020bb58a40083765190020dd546400827f6550020cf951400833d5450020d794d400835d5350020dd945400837551500209fd94400827d6510020cf950400833d5410020d794c400835d5310020bb98840082ed6210020dd94440083755110020ee500400827d65cc020cf953300833d54cc020d794f300835d53cc020dd947300837551cc0209fd96300827d658c020af99230082bd648c020cf952300833d548c020d794e300835d538c020bb98a30082ed628c020dd9463008375518c0209fd95300833e544c020cf551300835e534c020d754d3008376514c020dd545300827f650c0209f994300827d650c0209f194300833e540c020cf550300835e530c020d754c30082ee620c020bb5883008376510c020dd54430083d9300c020cf952200833d5488020d794e200835d5388020dd94620083755188020ee95220083b95488020f694e20083d95388020be58a20082e96288020de94a20083ea5288020fc946200837951880
  | 10 => 0x34827f6154d209f185534827f6054d20ded81534827e6514d20d754c534827e6414d209f590534835e6314d209f984534827d6114d209fd96434827e6590d209f596434827c6590d20cf952434833d5490d20d7d4e434835c5390d209fd95434827e6550d209f595434827c6550d20d7d4d434835c5350d209fd94434827e6510d209f594434827c6510d20d794c434835d5310d20e750c43482fa6010d20be580434827e63d45209f58f51483775194520b7d8d51482dc6354520b798c51482dd6314520dd544514827e6314520d798c514825e63145209f58c514835d63145209758c514827e65cc5209f597314827c65cc520d794f314835d53cc5209f996314827d658c5209f196314835f538c520d714e31482ee628c520bb58a31482fa608c520be582314827f654c5209f995314827c654c520afd9131482bc644c520d794d314835d534c5209f994314827d650c5209f19431482be640c520af590314835f530c520d714c31482ee620c520bb58831482fa600c520be580314827e65d0120cfd53404833c54d0120bb98b40482ed62d01209f99640482de6390120b758e404827c6550120cfd51404833c5450120bbd8940482ec62501209f994404827e65cc120d7d4f304835c53cc120bb98b30482ed62cc1209f99630482be648c120af592304827f654c1209f595304827c654c120d7d4d304835c534c120bbd8930482ec624c1209f99430482ed6188120fad4220482be64d4c20af59353082f661d4c20bd587530827e64d4c20cf993530823e64d4c209f593530833d64d4c208f593530827e62d4c20db98b530827e61d4c20dd987530827661d4c209f587530837561d4c209d587530827e60d4c20de983530827d6594c20d7d4e530827e6494c209f592530827e6194c209f586530825d6594c20d7d52530835e5494c20e7952530831e5494c20d7d92530835e6494c20d7592530835c6494c20d798a530835c6294c20d7d86530835e6194c20d7586530835c6194c20d7982530835c6094c20cf951530827f6454c209f191530835f6354c209fd85530827c6154c20d7d95530835f5454c20d7951530839e5454c20c7951530835d5454c20e7551530831d5454c20d7d91530835e6454c20d7591530835c6454c20d7989530835c6254c20d7d85530835e6154c20d7585530835c6154c20d7981530835c6054c20d708153082be6414c20af590530833e5414c20cf55053082de6314c20d754c53082f66114c20bd584530827e6414c20cf990530823e6414c209f590530833d6414c208f590530827e6314c20d798c530825e6314c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd96430827e6590c209f596430827c6590c20cf952430833d5490c20d7
  | 11 => 0x7a6015220af99353882bd64d4e209f993538833e64d4e208f993538827d64d4e20cf593538823d64d4e20db58b538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e20d794f438835d53d0e20bb98b43882ed62d0e209fd96438827e6590e209f596438827c6590e20cf952438833d5490e20bb98a43882ed6290e209fd95438827e6550e209f595438827c6550e209fd94438827e6510e209f594438827c6510e20cf950438833d5410e20d794c438835d5310e20e750c43882fa6010e20be580438833e54d0a20cf55342882fa60d0a20be58342882de6390a20b758e428833e5450a20cf55142882fb6050a20be18142883ad4210a20d794f328835d53cca20be98332882f960cca20af99232882bd648ca20d794d328835d534ca20bed8132882f8604ca20f34c8328837751946209f992518827d64946209f98e518827d63946209fd91518827c64546209fd8d518827c6354620af99051882bd6414620b798c51882dd6314620dd544518827f65d06209f997418827d65d0620cf953418833d54d06209fd96418827e65906209f59641882fa6090620be582418827f65506209f595418827c6550620cf951418833d5450620b7d8d41882dc6350620bbd8941882ec62506209fd94418827e65106209f59441882de6310620b758c41882ee6210620bb58841882fa6010620be580418827f65cc6209f997318827d65cc620d794f318835d53cc6209fd96318827e658c6209f59631882fa608c620be582318827f654c6209f595318827c654c620afd9131882bc644c620d794d318835d534c620bbd8931882ec624c6209fd94318827e650c6209f59431882be640c620af59031882ee620c620bb58831882fa600c620be580318833f54d0220cf153408833e5490220cf55240882de6390220b758e40882ee6290220bb58a408833f5450220cf151408833e5410220cf55040882ee6210220bb588408835f53cc220d714f30882be648c220af592308835e538c220d754e30882ee628c220bb58a308835f534c220d714d308835e530c220d754c30882ee620c220bb58830882f965c8220de59720882f961c8220af99353482bd64d4d209f993534833e64d4d208f993534827d64d4d20cf593534823d64d4d209f987534827d61d4d20af99253482bd6494d20d7d4e534827e6494d20cf992534823e6494d209f592534833d6494d208f592534827e6394d209f58a534836d6294d209f986534827d6194d209f58253483796094d209fd91534827c6454d20d7d8d534827f6254d20dbd895
  | 12 => 0x10c30cf950430c33d5410c30d794c430c39d4310c30be980430c2f96010c30dbd4a520c27e64948309f592520c27e61948309f586520c27f64548309f191520c27f61548309f185520c2be6414830af590520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c2de63d0830b758f420c2fa60d0830be583420c27f65908309f996420c27d6590830b798e420c2dd6390830db94a420c36d52908309fd95420c27d65508309f195420c33e5450830cf551420c36e5250830db549420c27e65108309f594420c35e53cc830db94b320c36d52cc830be983320c2f960cc8309f596320c2be648c830af592320c27f654c830d794d320c36e520c830db548320c3cd320c830be980320c2f9600c830ddd46510c27e64944309f592510c27e62944309f58a510c27f64544309f191510c27f62544309f189510c2be6414430af590510c2ee6214430bb588510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c27f65904309f996410c27d6590430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c3765150430dd545410c27f65104309f994410c27d6510430b798c410c2dd6310430bb988410c2ed6210430be980410c2f96010430d794f310c37651cc430dd547310c2fa60cc430be583310c27d658c4309fd95310c2bf644c430af191310c35e534c430af990310c2bd640c430bb988310c2ed620c430dd944310c375510c430be980310c2f9600c4309f992500c33e64940308f992500c27d6494030cf592500c23d64940309f597400c33f54d0030cf153400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c27f6550030cfd51400c33c54500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030d7953300c35c54cc030d754b300c35d51cc030af992300c2bd648c030b758e300c35e538c030ee992300c3b9648c030be58e300c37a538c030f694e300c379518c0309fd95300c2df654c030d7d95300c25f654c030d7951300c35c544c030d7549300c35d514c030b7d81300c35e504c030f6901300c3d9404c030bed95300c37b654c0309ed95300c2fb634c030f6d8d300c37a534c030f694d300c3da434c030f650d300c3da324c030f60c9300c379514c030f6cc5300c3d9314c030b798f54882dd63d52209f98f548835e63d52209798f548827d63d5220d758f548825d63d5220db58b548827e61d52209f587548837a60d5220cfd52548827e63952209f58e548827e61952209f586548833f64552209fd8d548827c63552209fd85548827c6155220cf550548833e64152209f98c548827d6315220db588548827e61152209f58454883
  | 13 => 0xd3149324c2df614c930f6d81324c2dc604c930f6181324c2d8604c9309f994324c2de630c9309f993514c27d64d45309f98b514c27d62d4530d7ccb514c35d32d4530ddd46514c2bf6454530af191514c2ef6254530bb189514c2be6414530af590514c2ee6214530bb588514c37551145309f990514c33e64145308f990514c27d6414530cf590514c23d6414530d7d0c514c35c43145309f988514c36e62145309b988514c27d6214530db588514c26d6214530de580514c27e65d05309f597414c27c65d0530cf953414c33d54d0530e7d0f414c27e65905309f596414c27c6590530cfd52414c33c5490530b798e414c2dd6390530e710e414c2fa6090530be582414c27f65505309f995414c27c6550530cf951414c33d5450530b7d8d414c2dc6350530e7d0d414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530e710c414c2ee6210530bb588414c2fa6010530be580414c27e65cc530b7997314c35e65cc530b7993314c2dc64cc530d7d53314c35d54cc530b758b314c35f52cc530d7147314c3db60cc530b7983314c3d860cc530b758e314c377518c530dd146314c2fa608c530be582314c2bf644c530af191314c377514c530dd145314c2fb604c530be181314c39f644c530b7991314c2dc644c530e7191314c29c644c530d7d51314c35d544c530b7d89314c35f524c530f5d85314c3d7514c530d7145314c3d4514c530f6d81314c2dc604c530f6181314c27e650c530af990314c2bd640c530b798c314c2ee620c530bb588314c2fa600c5309f997404c33f54d0130cf153404c2de63d0130b758f404c39c43d01309f996404c2de6390130b758e404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc6350130e710d404c27e6510130ee500404c3db43cc130f610f304c3db32cc130f64cb304c2f961cc130f6cc7304c3d931cc130af992304c2bd648c130b7992304c39e648c130a7992304c39d648c130b7192304c2dd628c130b7586304c3db508c1309f98f540c35e63d50309798f540c27e62d50309f58b540c27e61d50309f587540c27e60d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c33f64550309fd8d540c27d63550309fd89540c27c62550309fd85540c27c6155030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c27e6315030d798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c27d65d0c30d794f430c27f6590c309f596430c33e5490c30cf552430c2fa6090c30be582430c27f6550c309fd94430c27d65
  | 14 => 0x52418c2fa6090630be582418c27f65506309f595418c27c6550630cf951418c33d5450630b7d8d418c2dc63506309fd94418c27e65106309f594418c33e5410630cf550418c2de6310630b758c418c2ee6210630bb588418c2fa6010630be580418c33e54cc630cf553318c33e548c630cf552318c376518c630dd546318c2fa608c630be582318c2bf644c630af191318c33e544c630cf551318c376514c630dd545318c2fb604c630be181318c2be640c630af590318c33e540c630cf550318c2ee620c630bb588318c2f9600c630cf953408c33d54d0230cf952408c33d5490230b798e408c2dd6390230cf951408c33d5450230cf950408c33d5410230b798c408c2dd6310230ee500408c33e54cc230cf553308c2dd65cc230d7597308c35e54cc230e7953308c31e54cc230e7553308c35c54cc230d754b308c35d51cc230be597308c37965cc230ee953308c3b954cc230be587308c35d63d51309f98b544c27d62d51309f987544c27d61d5130cfd52544c2ee6295130bb58a544c27e64951309f58e544c35d63951309f98a544c36e62951309b98a544c27d6295130db58a544c26d62951309f986544c27d61951309f582544c3796095130cfd91544c27f6355130d7d8d544c27f62551309f189544c27f61551309f185544c27f6055130ded81544c27e6515130cf550544c33e64151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d30d7997434c25e65d0d30d7d53434c39f54d0d30d7553434c39c54d0d30b758b434c2dd61d0d30b7983434c3da60d0d30b6983434c3d960d0d309f996434c33e5490d30cf552434c2de6390d309f195434c33f5450d30cf151434c2fb6050d30be181434c27e6510d30cf950434c33d5410d30e750c434c2de6510d30d7994434c2de6410d30e7990434c35f5410d30e7950434c35d5410d30e7550434c31d5410d30b7588434c2dd6110d30b7980434c27e64d49309f593524c35f43d4930d710f524c27e61d49309f587524c2be6494930af592524c36f5294930db548524c27e64149309f590524c27e61149309f584524c27e65d09309f597424c27c65d0930cfd53424c33c54d0930e710f424c27e65909309f596424c27c6590930b798e424c2dd6390930dbd4a424c36c52909309f995424c27c6550930b7d8d424c2dc6350930e710d424c2fb6050930be181424c27e65cc930b7997324c35e65cc930b7993324c2dc64cc930d7953324c35c54cc930d714b324c2dd61cc930b7983324c2be648c930af592324c2dd638c930dbd4a324c36c528c930be982324c2f9608c930dbd49324c36c524c930bed81324c2f8604c930b7991324c2dc644c930d7951324c35c544c930f3d89324c3cf524c930d7149324c3cc524c93
  | 15 => 0xcc2df6350730b718d41cc39f43507309fd9441cc27e65107309f59441cc2de6310730b758c41cc39c4310730bb98841cc2ed6210730be98041cc2f96010730dd94731cc37551cc730be98331cc2f960cc730b799331cc2dc64cc730d7d5331cc35d54cc730b758b31cc35d52cc730d794731cc3d651cc730f554731cc2de60cc730f698331cc3d960cc730afd9131cc2bc644c730b7d9531cc35f654c730e7d9131cc2de644c730b719131cc39c644c730a719131cc35f544c730d755131cc2df624c730d754931cc3d7614c730d794531cc2dc604c730af99031cc2bd640c730bb98831cc2ed620c730dd94431cc375510c730be98031cc2f9600c730cf95340cc33d54d0330b798f40cc2dd63d0330e710f40cc2de6390330b758e40cc33e5450330cf55140cc2df6350330b718d40cc39c4350330d758f548c27e62d52309f58b548c27e61d52309f587548c37a60d5230cfd52548c27e62952309f58a548c27e61952309f586548c33f6395230cf58e548c33f6295230cf98a548c33d6295230cf18a548c33f6195230cf986548c33d6195230cf186548c33e6095230cf182548c33f64552309fd89548c27c62552309fd85548c27c6155230cfd95548c33f6355230cf58d548c33f6255230cf989548c33d6255230cf189548c33f6155230cf985548c33d6155230cf185548c33e6055230cf181548c33d5415230cf990548c35d63152309f988548c27d62152309f984548c27d6115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c33e5490e30cf552438c33e5450e30cf551438c2fb6050e30be181438c33e5410e30cf550438c39d4310e30af993528c2bd64d4a30cf953528c33d54d4a30cf952528c33d5494a30dbd4a528c27e6494a309f592528c27e6194a309f586528c33e5454a30cf551528c27f6454a309f191528c27f6154a309f185528c2be6414a30af590528c33e5414a30cf550528c36d5214a30bd984528c2f56114a309fd97428c27e65d0a309f597428c33e54d0a30cf553428c2de63d0a30b758f428c27e6590a309f596428c2de6390a30b758e428c33e54cca30cf553328c2be648ca30af592328c33e548ca30cf552328c36e528ca30db54a328c2fa608ca30be582328c33e544ca30cf551328c36e524ca30db549328c2fb604ca30be181328c33e540ca30cf550328c3cd320ca30af993518c2bd64d4630cf953518c33d54d4630cf952518c33d5494630ddd46518c27e64946309f592518c27e62946309f58a518c37a6094630cf951518c33d54546309fd91518c27c64546309fd89518c27c6254630af990518c2bd6414630cf950518c33d5414630bb988518c2ed6214630dd544518c27f65d06309f997418c27d65d0630cf953418c33d54d06309fd96418c27e65906309f596418c33e5490630cf5
  | 16 => 0xa6010440be580411027f65cc4409f997311027d65cc440d794f311035d53cc4409fd96311027e658c4409f5963110376518c440dd546311027f654c4409f595311027c654c440afd9131102bc644c440d794d311035d534c440dd9453110375514c4409fd94311027e650c4409f59431102be640c440af59031102ee620c440bb58831102fa600c440be580311035e6394040d758e501033e53d0040cf54b401033d51d0040af592401033e5490040b798e40102dd6390040be592401037a5490040ee95240103da6390040f658e401037951900409fd9540102bf6550040cfd95401023f6550040cf94d401033d5250040cf54540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040eed0d40103b94350040de54540103bb4150040ee50540102ee62d5330bb58b54cc35e63d53309f98b54cc36e62d53309b98b54cc27d62d5330db58b54cc26d62d53309f98754cc27d61d5330de58354cc33f54953309f98a54cc27d62953309f98654cc27d6195330cfd9154cc35c63553309fd8954cc27c62553309fd8554cc27c6155330cf55054cc33e6415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330b759743cc35d65d0f30d7d5343cc35d54d0f30b758b43cc2dd61d0f30b798343cc33e5490f30cf55243cc2fa6090f30be58243cc33e5410f30cf55043cc39d4310f30be98043cc2f96010f30d759443cc39e6410f30d7d5043cc39e5410f30d755043cc39d5410f30c755043cc2dd6210f30b758443cc2de6010f30f698043cc3d96010f30af99352cc2bd64d4b30af99252cc2bd6494b30dbd4a52cc27e6494b30cf99252cc23e6494b309f59252cc33d6494b308f59252cc27e6194b309f58652cc27f6454b309f19152cc35f4354b30d710d52cc27f6154b309f18552cc36d5214b309f99742cc27d65d0b30e710f42cc2fa60d0b30be58342cc36e52ccb30db54b32cc2fa60ccb30be58332cc2de64ccb30b719332cc35e54ccb30d715332cc35e52ccb30f394b32cc3cd52ccb30b758732cc2de60ccb30f698332cc3d960ccb30af99232cc2bd648cb30b7d9532cc35f654cb30b799132cc2dc644cb30d795132cc35c544cb30f3d8932cc35e524cb30b7d8532cc2dc604cb30db94832cc36d520cb30be98032cc2f9600cb30ddd4651cc27e64947309f59251cc35f4394730d710e51cc27e62947309f58a51cc27f64547309f19151cc27f62547309f18951cc35f3254730d74c951cc2be6414730af59051cc2ee6214730bb58851cc37551147309fd9741cc27e65d07309f59741cc33e54d0730cf55341cc39f43d07309fd9641cc27e65907309f59641cc2de6390730b758e41cc39c43907309fd9541cc27d65507309f19541cc33e5450730cf55141
  | 17 => 0x45409f58f515027e62d45409f58b51503775194540b7d8d51502dc6354540bbd8951502ec6254540b798c51502dd6314540bb98851502ed6214540dd544515027e6314540d798c515025e63145409f58c515035d63145409758c515033e4314540cf10c515027e6214540db988515026e62145409f588515036d62145409b588515037960145409f99741502be65d0540cf99741502be63d0540cfd4f41502bd62d0540cfd4b415033c51d0540eed8341502be60d0540ee18341502bd6490540ddd4641503745190540be98241502f96090540b7d8d41502dc6350540ddd4541503745150540bed8141502f86050540e7d8d41502bc6350540e718d415029c6350540cfd4d41502bf6250540cfd4941503b76150540edd45415033c5150540ed14541503bb6050540af18141503b860505409f99441502be6410540b798c41502dd6310540bb98841502ed6210540be980415027e65cc5409f597315027c65cc540afd9331502bc64cc540e790f315027e658c5409f596315027c658c540af99231502bd648c540d7d4e315035c538c540e710e31502fa608c540be582315027f654c5409f995315027c654c540afd9131502bc644c540e790d315027e650c5409f594315027c650c540af99031502bd640c540d7d4c315035c530c540e710c31502ee620c540bb58831502fa600c540be58031503ba43d0140ee10f40502f961d0140eed0740503b941d0140b798e40502dd6390140af98e405039e6390140a798e405039d6390140af58a40502bd6190140eed42405035f5394c409f98a531027d6294c409f986531027d6194c409fd89531027c6254c409fd85531027c6154c40d754c53102ee6214c40bb58853102f66114c40bd584531035e53d0c40d754f43102fa60d0c40be583431027d6590c40cf952431027f6550c40cf950431035e5310c40d754c431039d4310c40be98043102f96010c40dbd4a521027e63948409f58e521027e61948409f586521027f63548409f18d521027f61548409f18552102de6314840b758c521036d5214840bd98452102f561148409fd97321027e65cc8409f59732102be64cc840af593321035e53cc840d754f32102fa60cc840be583321027f658c8409f996321027d658c840af99232102bd648c840db94a321036d528c8409fd95321027d654c8409f195321035e534c840d754d321036e524c840db549321027e650c8409f594321037751944409f98e511027d63944409f98a511027d62944409fd8d511027c63544409fd89511027c6254440b798c51102dd6314440bb98851102ed6214440dd544511033e54d0440dd947411037551d0440be98341102f960d04409f596411027f6550440cf95141102df6350440b718d41102de6310440b758c41102ee6210440bb58841103765110440dd54441102f
  | 18 => 0xd794e439035d5390e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40d754c439039d4310e40b798f52902dd63d4a40d794f529035d53d4a40d794e529035d5394a40dbd4a529027e6394a409f58e529027e6194a409f586529035e5354a40d754d529027f6354a409f18d529027f6154a409f18552902de6314a40b758c529035e5314a40d754c529036d5214a40bd98452902f56114a409fd97329027e65cca409f59732902be64cca40af593329035e53cca40d754f329027e658ca409f596329035e538ca40d754e32902de63d4640b758f519035e53d4640d754f519035e5394640d754e519037751946409f98e519027d63946409f98a519027d6294640de982519035e5354640d754d519027f63546409f18d519027f62546409f18951902de6314640b758c519035e5314640d754c51902ee6214640bb58851903755114640d794f419035d53d0640d794e419035d5390640dd94641903755190640be98241902f96090640b7d8d41902dc6350640d794d419035d5350640dd94541903755150640bed8141902f86050640b798c41902dd6310640d794c419035d5310640bb98841902ed6210640be580419027f65cc6409f997319027d65cc640d794f319035d53cc6409fd96319027e658c6409f596319035e538c640d754e31902fa608c640be582319027f654c6409f595319027c654c640afd9131902bc644c640d794d319035d534c6409fd94319027e650c6409f59431902be640c640af590319035e530c640d754c31902ee620c640bb58831902fa600c640be580319035e53d0240d754f40902bd65d0240cf597409033e53d0240e794f409031e53d0240e754f409033d52d0240cf54740902f965d0240de59740903da53d0240f654f40902f961d02409f98b535027d62d4d409f987535027d61d4d40d7d4e53502ee6294d40bb58a535035d5314d409f988535027d6214d409f984535027d6114d409f997435035f5390d40d714e43502fa6090d40be58243502be6390d40cfd4e435039f5390d40e714e43502bd6290d40af58643502be6090d40ee98243502ba6090d40ee582435035f5350d40d714d43502fb6050d40be181435027e6510d40e750c43502be6510d40cf99443502be6310d40e798c435033f5310d40e794c435039d5310d40af58843502bd6110d40af980435027e63d49409f58f525033e43d4940cf10f525027e61d49409f58752502de6394940b758e525036f5294940db548525027e63149409f58c525027e61149409f584525027e65cc9409f597325027c65cc940d7d4f325035c53cc940e710f325027e658c9409f596325027c658c940af99232502bd648c940dbd4a325036c528c9409f995325027c654c940d7d4d325035c534c940e710d32502fb604c940be181325027e63d
  | 19 => 0x1500c77a6454031de591500c7786454031de98d500c77b4354031d6d0d500c77a4354031de50d500c7784354031d610d500c77b6254031de989500c7796254031de189500c77a6154031ded05500c77a4154031de505500c7784154031decc5500c75b3154031de8c5500c7793154031d64c5500c7783154031af990500c6bd6414031cf950500c73d5414031bb988500c6ed6214031db948500c76d5214031be980500c7795014031bb98b53d02ed62d4f40d7d4e53d027e6294f409f58a53d027e6194f409f58653d027f6254f409f18953d027f6154f409f18553d035d5314f40d794f43d035d53d0f40be98343d02f960d0f40af59643d033d6590f40cf54e43d02bd6290f40af58643d02be6090f40d794c43d035d5310f40e750c43d02fa6010f40be58043d039e6310f40e794c43d033d5310f40e754c43d031d5310f40af58843d02bd6110f40af98043d03ba6010f40ee58043d02de63d4b40b758f52d02de6394b40b758e52d036f5294b409f98e52d035e6394b409798e52d027d6394b40d758e52d025d6394b409f98652d027d6194b409fd8d52d027c6354b40cf90d52d033c4354b409fd8552d027c6154b40db54852d027e65ccb409f59732d039c43ccb40be98332d02f960ccb40ddd4651d027e63947409f58e51d033e4394740cf10e51d027e62947409f58a51d027f63547409f18d51d027f62547409f18951d02de6314740b758c51d02ee6214740bb58851d03755114740dd94741d037551d0740be98341d02f960d0740af98f41d033d53d0740af58b41d033d52d0740cf94741d03b651d0740ed54741d02be60d0740ee98341d03b960d0740b7d8d41d02dc6350740afd9541d033f6550740e7d8d41d02bc6350740e718d41d029c6350740cf54d41d02bf6250740cf54941d03b76150740cf94541d02bc6050740b798c41d02dd6310740bb98841d02ed6210740dd94441d03755110740be98041d02f960107409fd9731d027e65cc7409f59731d02bf64cc740af19331d035e53cc740d754f31d039e43cc7409fd9631d027e658c7409f59631d02be648c740af59231d039c438c7409fd9531d027d654c7409f19531d02bf644c740af19131d035e534c740d754d31d039e434c7409fd9431d027e650c7409f59431d02be640c740af59031d039c430c740bb98831d02ed620c740be98031d02f9600c740d7d4e539027e6294e409f58a539027e6194e409f586539035f6494e40d7d8a539035e6294e40d758a539035c6294e40d7d86539035e6194e40d7586539035c6194e40d7982539035c6094e409fd89539027c6254e409fd85539027c6154e40d7d95539035d6454e40d7d89539035e6254e40d7589539035c6254e40d7d85539035e6154e40d7585539035c6154e40d7981539035c6054e40d754c539035e53d0e40
  | 20 => 0xc76c4354831d310d520c76e6154831db0c5520c76f6054831db981520c76d6054831db181520c6be6414831af590520c73e5414831cf550520c6ee6214831db548520c6fa6014831be580520c67e64944319f592510c75f4394431d710e510c67d65d0431cf953410c73d54d0431e7d0f410c76e52d0431db54b410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c79c4390431db94a410c76d52904319fd95410c73e5450431cf551410c6df6350431b718d410c79f4350431db949410c76d52504319f994410c67d65104319f194410c6de6310431b758c410c79c4310431be980410c6f96010431cf953310c73d54cc431db94b310c76d52cc431b7993310c6dc64cc431d7d53310c79e54cc431d7553310c79d54cc431c7553310c7ce52cc431d754b310c7cd52cc431d354b310c73e548c431cf552310c6dd638c431d794e310c76e528c431db54a310c7b6548c431ed552310c6f5638c431dd94e310c7d6538c431f5d0e310c7d4438c431f994a310c7e5528c4319fd95310c6bf644c431af191310c73e544c431cf551310c76e524c431db549310c6df654c431d7d95310c65f654c431e7d91310c6de644c431b7191310c79c644c431a7191310c75f544c431e7951310c75d544c431e7551310c71d544c431f3949310c75d524c431f3549310c74d524c431b7d85310c75e514c431bdd95310c777654c4319dd95310c7b7644c431ed191310c7b6544c431ed551310c6f7634c431f5d8d310c776534c431f594d310c7e6524c431f9549310c6be64d4031af593500c73e54d4031cf553500c6ee62d4031bb58b500c76e52d4031db54b500c73e5494031cf552500c76e5294031db54a500c77b50940319f992500c67d64940319f98a500c67d6294031ded52500c77a5494031ee952500c73a5494031de552500c7b95494031ce552500c7785494031f6d0e500c7d84394031ded4a500c77a5294031fa94a500c76a5294031de54a500c7e95294031da54a500c7785294031f6cc6500c7f23194031f64c6500c7f13194031ded92500c77a6494031de592500c7786494031de18e500c77b4394031de90e500c7794394031de10e500c77b6294031de98a500c7796294031de18a500c7786194031ded06500c77a4194031de506500c7784194031decc6500c77a3194031de4c6500c73e5454031cf551500c76e5254031db549500c67f64540319f191500c75f4354031d710d500c67f62540319f189500c75f3154031d74c5500c77b6554031ded51500c77a5454031ee951500c73a5454031de551500c7b95454031ce551500c7785454031f6d0d500c7d84354031ded49500c77a5254031fa949500c76a5254031de549500c7e95254031da549500c7785254031f6cc5500c7f23154031f64c5500c7f13154031ded9
  | 21 => 0x548c531e7152314c71c548c531b758a314c7d7518c531b7582314c73f54d4131cf153504c67e64d41319f593504c67e62d41319f58b504c6be6494131af592504c73f5494131cf152504c77b5094131afd91504c6bc6454131cfd51504c73c5454131bbd89504c6ec6254131cfd50504c73c5414131de540504c67e64141319f590504c67e62141319f588504c6ee62d5031bb58b540c6fa60d5031be583540c75e63d50319f98b540c76e62d50319b98b540c67d62d5031db58b540c66d62d5031dd987540c67e60d5031de983540c67a60d50319f583540c77960d50319e583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c63d6595031e718e540c73e6395031cf18e540c73f6295031cf98a540c73d6295031cf18a540c73e6195031cf186540c73f6095031cf982540c73d6095031cf182540c73f6455031d718d540c67f62550319f189540c67f60550319f181540c73f6555031e718d540c73e6355031cf18d540c71c6355031cfd89540c73e6255031cf589540c73c6255031cf985540c73c6155031cf0c5540c73f6055031cf981540c73d6055031cf181540c6be6415031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6315031d798c540c65e63150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f592530c67d65d0c31cf953430c73d54d0c31b7597430c75d65d0c3197597430c75f54d0c31e7953430c75d54d0c31e7553430c71d54d0c31b7587430c67f6590c319f596430c73e5490c31cf552430c6de6390c31d794e430c6f66190c31bd586430c67f6550c31cf951430c73d5450c31d794d430c67f6510c319f594430c73e5410c31cf550430c79d4310c31bd984430c6f56110c31d7594430c65d6510c31b7990430c79e6410c31d7d50430c79e5410c31d7550430c79d5410c31c7550430c7d66110c31b7584430c7d56110c31af993520c6bd64d4831cf953520c73d54d4831be983520c6f960d4831cf952520c73d5494831dbd4a520c67e64948319f592520c67e60948319f582520c76f5494831db952520c7ae5494831cb952520c76d5494831eb552520c72d5494831db152520c7cf4394831f310e520c76f6494831db992520c76d6494831db192520c76c6394831dbd0e520c76e4394831db50e520c76c4394831db186520c76f6094831db982520c76d6094831db182520c73e5454831cf551520c67f64548319f191520c75f4354831d710d520c67f60548319f181520c76f6554831dbd51520c76e5454831eb951520c72e5454831db551520c7ad5454831cb551520c76c5454831f3d0d520c7cc4354831dbd91520c76e6454831db591520c76c6454831db98d520c76f4354831d3d0d520c76e4354831db50d520
  | 22 => 0x231bb988548c6ed6215231be980548c6f96015231cf953438c73d54d0e31bd987438c6f561d0e31e7953438c75d54d0e31e7553438c7d661d0e31b7587438c7d561d0e31cfd52438c73e5450e31cf551438c6f76150e31bd185438c79d4310e31b7594438c75d6510e31e7990438c75f5410e31e7d50438c71f5410e31d7550438c79c5410e31b7584438c76f5294a319f992528c67d6494a319f982528c67d6094a319fd91528c67c6454a31d7d0d528c75c4354a319fd81528c67c6054a31af990528c6bd6414a31db548528c6fa6014a31be580528c79f43d0631b798e418c6dd6390631e710e418c6dd65cc631d7597318c6de64cc631b7193318c75f54cc631d7553318c75d52cc631bd597318c77565cc631ded42508c67e64942319f592508c67e62942319f58a508c67f64542319f191508c75f4354231d710d508c67f62542319f189508c75f3154231af990508c6bd6414231bb988508c6ed6214231de540508c67e62d51319f58b544c67e60d51319f583544c79f63d5131cfd8f544c73d63d5131cfd8b544c73e62d5131cf58b544c73c62d5131cfd87544c73d61d5131cfd83544c73e60d5131cf583544c73c60d5131cfd52544c75d63951319f98a544c67d6295131dd586544c67e60951319f582544c75f63551319fd85544c77761551319fd81544c67c60551319f994544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c6be6515131cf994544c63e6515131e758c544c73f6315131cfd88544c73e6215131cf588544c73c6215131cfd84544c73d6115131cf4c4544c73f6015131cf980544c73d6015131cf180544c73f54d0d31cf153434c6f661d0d31bd587434c67e6590d31cfd52434c73c5490d31b7996434c75e6590d3197996434c6dd6490d31e7d52434c75e5490d31d7152434c79c5490d31c7152434c6dd6290d31b7986434c6dd6090d31cfd51434c73c5450d31bdd85434c6f46150d31e7d91434c79f5450d31d7951434c75c5450d31e7151434c71c5450d31b7d89434c7d76150d31b7185434c7d46150d31b7d81434c67e6510d31cfd50434c6de6310d31e750c434c73f54d4931cf153524c67e64d49319f593524c67e60d49319f583524c6be6494931af592524c73f5494931cf152524c76f5294931afd91524c6bc6454931cfd51524c73c5454931bed81524c6f86054931cfd50524c73c5414931db548524c67e64149319f590524c67e60149319f580524c67e65d0531cfd53414c73c54d0531b798f414c6dd63d0531e750f414c73f5490531cf152414c79e43905319f595414c67c6550531b7d8d414c6dc6350531e750d414c73f54cc531cf153314c7b754cc531ed153314c7d643cc531f550f314c73f548c531cf152314c6df648c531b7592314c79f548c531d7952314c75c
  | 23 => 0xfd855290e7c6154a439fd815290e7c6054a43db5485290f775194643d7d0e5190e7e62946439f58a5190e7e60946439f5825190f3f43546439fd895190e7c62546439fd815190e7c6054643bb9885190eed6214643dd5445190efa6014643be5805190eee62d4243bb58b5090f7b50942439f98a5090e7d62942439f9865090e7d6194243d7d0d5090e7f62542439f1895090e7f61542439f1855090f795014243e7d4e4350ebd6190d439f9835150e7d60d4543ddd465150f755114543be9805150ef96014543cf90c5150e7e6014543de9805150e7a60145439f5805150f7960145439e5805150f5f43d4143cf90f5050e7e62d41439f58b5050e7e61d41439f5875050f7b5094143de5405050e7e62141439f5885050e7e61141439f5845050edd6490c43a75924310f5e5490c43e79524310edd6290c43b79864310edd6090c439fd954310edf6550c43d7d954310e5f6550c43b7d914310f5e5450c43e79514310edf6250c43b71854310edf6050c43e7d954310e9f6550c43c7d954310f9f6150c43e79854310f9d6150c43e71854310e9c6150c43e7d814310e9f6050c43e79814310f9d6050c43e71814310f9d43d4443e750e5110f7751944439f9825110e7d6094443e750d5110f5e4354443d750d5110f1d43544439fd815110e7c6054443e750c5110f755114443be9805110ef96014443e750f5010f9d4394043ded425010e7e62940439f58a5010e7e61940439f5865010f9d43540439fd895010e7c62540439fd855010e7c6154043e750c5010eee6214043bb5885010ef66114043bd5845010f795014043cfd5254cc67e62953319f58a54cc67e60953319f58254cc67f62553319f18954cc67f60553319f18154cc73d5415331d798c54cc77561153319f98054cc67d6015331cf95243cc73d5490f31bd98643cc6f56190f31d795243cc79e5490f31e755243cc75c5490f31b758a43cc6de6190f31f598643cc7d56190f31b758243cc6df6550f31d7d9543cc79f6450f31e7d5143cc75e5450f31d715143cc79c5450f31c715143cc6df6250f31b718543cc6df6050f31cf95043cc73d5410f31e750c43cc6f66110f31bd58443cc6be6494b31af59252cc76f5294b319f99252cc73e6494b318f99252cc67d6494b31cf59252cc63d6494b319f98252cc67d6094b319fd9152cc67c6454b319fd8152cc67c6054b31db54852cc6de63d0731b758f41cc79d43d0731af99250cc6bd6494331ded4250cc67e6494331cf99250cc63e64943319f59250cc73d64943318f59250cc67e62943319f58a50cc67f64543319f19150cc67f62543319f18950cc7795014331dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c67f62552319f189548c67f60552319f181548c73d5415
  | 24 => 0xc0050000001000c01600240010010000000c01a0008001000000600100040008004001800000000010000003001000900080010004003000000000080000030000001c001000400c0034003001c0050054004003400000140080000000000c000003800100600030004001000c009000c0000000000000c00d0000000000000100000000004003000801200000000040000000c00300000020000004000c001001000000100030028000000400000140000000000003801a000400c000c00400040000000006000400000080030000004000800500080000014000000c0020004000000400400240000008000000c00300040010000003002c00100040100004002001800500000000000002005c005001c0080000000002800400000010000001001c0000030004000000400040010000003000000400080000018002000000a000c002001800800100000014001000400200000100000001001000000000000008002000c0010014000000800b000c001004000b00000000000001000000e0000018001c001000400500040030018000000400e000400000000010004004002400000000030010005002000c000800200180030000001000400000080020004003000800a001401800480010010003000400200040010018004000401c0000012000000000000020000006000c0090000002000000100280050004006000c00600000000010000001000400180000000000002c00300040000024002001400100000100018001001c00200200020014009000c001000000700280000000005000c002000c00200040030010008002c00000640000000002000c00000040000000000000400000040060010003000c004000c0000014000002c001000000000080180018000000800400000000000001000c00000100150000000000800200a8008001400500000050034005000400200000090000000000000200380030028000000000400000000018002001800300000090008000003c000000800100000040028000000000100000280008003005c0040008008000c015000400000000060020003000000200040000000002000400600000030004002000000200000000000000003800c0000001000800200080050000001002c0020034001002c0190000000000400900580010000002001c00200300000014001009c00f000801000140000004000000c001000400700140000008001000c001003800d0020000007000b00140100014000001401c0000002000400c0014005000c0000004001000400d000c003000000600140040004002000400100040060078007001800800000000030000000c002002800d0020000b75974390f5d65d0e43be9835290ef960d4a43dbd4a5290e7e6194a439f5865290e7e6094a439f5825290f5f4354a439
  | 25 => 0x4005000c0050024000000400000080000004003000c0020004000004000000000050004001000000000080010000003003400300040010030000000001900f4006000000c0014003000800b000000500000000000004000800c00040000004004001c003001c0030000000003400600280000010001002c00300080000010002000800100300090004001000c0000000000000000000240020008000001000000000150008003001c0020018010000c0000000006002c0040004000003c001002400100040060004005003c001000400000000000024001000400600280010018001000000a000000300340020010006001400d0020001000400700040000000004000800f002c00200080160014001001000a000c0040000000002c00c002c00b000c00300040000014001000c00100080050020000004400200040000000007000800a002400600040000014000000c00000180020008003001800a000000300200020004007000c000000400000000030018002000c0000008001000c002000400300000100004001000c0010018000000000400240000000002002801000040030000000000c00300000030004005000400a0048009000c000000c002000c0040000001000400500000020004006004c005000401c000401100000000000000000c035000000e0004000000000e00040030004002000800000000000000000000000300240140000001000400d000c002001c00300000000008002001c0040014007000000c0000006000c0020000000000c004000000c000c0020000006007400100000000000000000c00800000030008008000000200040030004002000000200000070008011000c00000ac0000000000000c00000380020008001002c003001000200d00050000001001400000300200014001000c008001000100000000000000000c00000000030004000000c00000000010000003000c000000800a0018004001800c0000000000400300040020000002000400700c0018000000a00080050008007000c000000c010001800d000000500040120008002000801f00600080008000000000000100000008001003400000040130038019000000800040000000016004800a0008001002c000001c001004000500000020000000000000000100010004000000800200100100010001004000200000010000004000c000000c00d0008001000000e000000000080000040001000000800040010010009000400000000000004001000400400140070008003000000400000020018000000400700040010008000002c0080020002000000600000000010006004000000080020018000001c00300080020000000001400e00a8017000400300000000004006002400300140030014004000c000002c009000000100040060
  | 26 => 0xc000000100100170000003000c00100400040008001000c0030010007000000300300000008003001400100000020004000000c014000c001000000200000070004005000000200080000000003001800400040010000000006000100200010000000000c00100040050000000001400d0004009000c0010000003000000200000070010000001800300000000020000001c001000000200100020004006000c00100000010004000003c00400000110004002005000000240030008002001c0000000000000400100440000000000000000e000000200080010034000002c004000c00000040000000000000c0000000014000000a0000002000800200300090040004004400c00000020000000002400c002c00d0010009000c00000140020004007000c001000c000000800600000030004000000000100200020004006000001c0008002001c008001c0050020004000001c000000400040020020000000c00000400010000000000c00100080060008003000000c002c004000000b002c000000c004000400b0004003000800000000010024000002c001001800000000040024000000000000140000004000004400600580100004000000800600240080040005001c000001000200000010018001002c000000400100340000004004000000100240000004002000c00400080010000001003400a000400f0000000001000000080080000005003001c0000001000c003000c001000000200580010028011000000600040000054001000c0010000000002000900040040008000000400200040020000001004800800140020004000000000b000000b0004002000400000040000004000005400200000070004001001c001000800600100010078004000c0000020000000000000040110000000001c002000800100000140014001000400000600000020006000c00000080020000003000c00100040040008004008800000040070014005000000500140050000003000000100040000000000000000200200020000001000c017000c000001c001000000e0010000007000000100070060000001400000140090000000000400000240020000006000c001001000f00080000000000000002300000040000006000800400300030000000000400700100000054003001c0030008002001401700000000000007000c002000000000000060034000001400100040000000009000000400000090004000000000000000000010002000c000004c0050004012001c00400000020000000001c0000044004000000a00300030000008001000100000010000000000000d000c000001000000000050014009000000c005800a001400f0004001000c0030010001000000f0004002000c002000000100100010000001000400400000010030
  | 27 => 0x80005d2190245787f06a0055600023e807a1c6a000151d00000005ec000000000000000000000170568ea4bc000000007a80004644000000000043a817e06c400099c80006b6df2a8bec030000000000018a84dba7389805a8c4758faa38406ca000091a1c92772269c00089095d809d55a36aea66c195000000000005484b9c000000094d80000000000000000000000964ea525c000000089727de00013c800017d5488a40e2e481cc36596462c0801e05a24248e7a56c2e20fdb4e50ac0257a24c88886884ebd7627df000000000000f607cc0002844207000000000a617500005778000099c72500008519c6a000000000002880000000000000024f6ec4000000000000000000000c3615b03f42cc68127db000000000009050de800000001c788dd0008005001c002001800e000401800000000040014000400c0000000000c0010000000000400000140090000003001000000080070000001000800600000030004004000400000040000004005001c002001400000140010024000000400100000000014001000c00500180030004000000801a00080020004000001800400000010000001000000100000020034000002c002000c00200180020004005000000100000000000005005400100700030020007000c00000040050008001000400800240050000005000000000040030010002000800000000000004001001800000100000004001000000100340010018000001000400040000010003009401400740030004000000000100000000000001000c0010130000000400400140110018001005004c00100030000006000400200080040008001000000300000000008001000000300180080014010000000c00040050004000003c00000000040018000000400100000050000000000800300000070020007000c007001c001001c005002c000000c0150004005000401d003000000040040018008000c01b000c001002c00000180030004003001000300000000000000000000c000000000100000000000000400100080050008008002c001000c0000050000003c000000800000000020008000000000d001800400000010014000000400d000400200000000004000001c000002c007001c018000c00b00000060014009000c000006800000140100020001000c000000000900000010000001001c000000000300080000000001000c0000000008000400200080060004001000c0000000000001800400040000014000000000600000010000002003c000000c002000400100040060000001003400600180080018021000800200040050000003000c00200000020000000002c00400000000000001000c0040004001002800100040010000000000000c003c003000800d0014002000c0000010000000400000140000000000
  | 28 => 0x62259149b1095a6788c8e74e000000000000001c0600001d6416941d00000008a089cc8f8433a71901500be511a15894c0844836c7938000000059a176133299400000be98ca000000083c00000001cc63e3800041396720801d30000000001600007c100005cc805419d1c38000205893200000000af19498ff64e410ee231c0000a28000797c0c68d911de3c0c00038b00007e39adc000198000020f40001f0a8dd0bc44878a2a0000000000146c21c272e000000000002f44a282f05321d4a66e14c60000eba1d7c00045b800034fa40c97c1ade0261da02b29cdc510a69a86249ce9309d4c3e5910e1685bcc94f0f2702f8e3287f4f602d0a24a74186b95801b7a6398a18000159c12e80007c586ec893984597787c49bf511029f893a85926fb2840e9c000053e6c895607865efc8fe000091a8a2e554800006103809b58c7c90a275c349e5601be2815124000000020f60000000450579e6b8058a0321ae12db66ba3390bd236943f848021c482bc0000000d1d000000040dd5ce3cc88420001cec1f791e38450c6a00013ca29c80008bf000000000000001adf000046700024d600000004f440000000000550c67e00020e82ab10ce4088c0546f89fea0e89c859f025437163e540010fa20b8a1627b63d037fcdca3c690f9187800090aa3ae19ca0f263c124380c82565eda1fc6148b366ac899e22b000000008d47d5cc10000000028d4db60000e6c060800000009947d4cb750000b350000c0a03f50b483b143294f58150191718746189861c80001fb97ec00014241b517133ce1ed6000177608680002f600000fe9dea00000002c7800000000000000d2c7a00adc5a3a5327cf17bc5c3148e482126e65291c400000000000000499a33934282570001acc00021485c817263af0497000207d6cfc4a4000016c4a51ff4896004a45f51d4280dcd042851ee00016063511d1c9764ca2753a2ec8f28e2e3a38f293e6c8fe618677691c4d66496902500014b85460000160c69e8fe838a83825f595f0d64717047c21f94b200028326178f0406a26519ec077e72599221bcc00012b941242d8cec163841b06901020000000000171e9fb976a4570eaf000086d000000000019933f800009a01228000000007213a80000000000000000000000000520000285e9bc80000001ac61cd97f85e024c959b885d80b14588e00cba6f55770248d1986ea8a6c2c5094887185b58b1088c00012b28f1160e0000000760870294b241f3c50f4c4e4c00044280b95fad8f86cd195053100006fa957d00002bc0da961499740008721a3e7f403e66e0235481800006438000000003a4f98000000209624300001bf80005c1e3a88f60000312880622d8ab0000203e9d90000000000066863335c29dd6000000000000000000000000000076a00007dc0000515
  | 29 => 0x11b8036dca78f994d22a4000093e000000024e4000000079dc0000000000642973f51409f258200ca619433d4718000885800000000c2000000080d10ba4bd15ae74a26a000022b8536000041e8000382059416c80000001df52fb281782d942a00011f066313e155100005bc8b2426e1cab6860000263000091c87da00004d6064a5b3795a6d345d000050d23841b617383df25f28bac0000000efd00000006089d5659300004c89ece000193900000009f5800037788229e780000000bc84d7c75c576a12a30315ad00014f441a54883eb40001d198063b08e983b180004070b3a000280c2140000424800000025298ba00000000000571239000028136b00000000253981c16e20000000058213e5d727802b5253b5cec0a1254a55c1ed91946ab02e54d640001e7822652d80004e580000000b1200005ba54025a800000007e01866a0d126478821b421c687a00019a72c8871681e16984bb00780002335103100b01ba63826449dc824e4a28a9155a6e19cbb3d000000002402997ca380001cca0000000000000000003fc4508dcd0000000000164e000100c00012b449400005af00000000d369c00000000286000004e44499864275430a8b298386618f2c130093c394000000010980000e300000000000000000011b40000000392963c51d8baa2e3dd430000000557855a27b10fe355050c000259074200007d2d74a78da04a00003260001e1e11880004a0800000000006620dc8117a040828dbec336dbda98f1113000000003c1eb6000177a00000007048000350800000027bc24ca39400019b500000005749f8858716c8000000011a8f42000000000000009049a6e00000000000f3f4a59196000000046fd8b47888e6a000000000017b8000058600016f6000258800000000001fce5758000396c0005ff8ca400000000000fb669612319e2000000000008dc133e00012fa00014809cd0000000000045fd5cc2df257689e14621ef800000020243739b624d0000074913342d6c0007bca51500000000000000338004600000000000c9f0000042000049c000000042180000001e90000022c17f8fc06ec80004b08000809a090123165e0000efa1250e8843dd58e0001115000032877b5f349c40fa6846800066d244c0001519572000057f80003a7800074280005d41e658198000000541a5604000000000051d000041312b62a59788789800000000005b5a5223e31d620001df61ff40000001a42000000059f97d60001ac20000000993800042b80000002684241800000027d93fd0000000259431b93809b7a1829194836700927d00020501a0e5aa3d8800014e1a447aa87084aa168c9f8a3e36b4800000000002489cb06ebe0992319db483a84770001f5c40d9ce88b587984501c4e24449e487c889e00003060000653525a3b
  | 30 => 0xc844ec56b076e19244d0dbde7fb0b2861315a06a588b21ae8e908818a8070f1c5837d83b872380da55a0eb804799fe7aba1a02e114681a9800000011229e8d63021340de91608b80da60e64930ccc37696020000bf4926a57a5c64506673841a3c94c400000699952842f00022bc609400025700000000000537149c3519b8225d939c00000006a3800043e2416000025c9be17c01820fda7b986aa00015f2000000018b9a047ea8000046000050e000088990100001fb247385e206c92656aa00003ff800051c1be03d8c84f20b4000000000041d0000000000000010a721867523c8995c00007ae8061b559260000774e2a0000251019b13d6000134a00000000001be8414c00098b9f4c8e81d1600000000000000791061407c00000f1956d000000000002125ef8000000000000000000001aa20000aee0a026009b294e1823c7d71e24000752194c08e18c42228dba78b837e0ea09185e61a1a03e0b526c81818000114a000099803d000020280000001d501e943bc00027aa0001b0c354052e38813a5732153e0d91cee516a12429e8dc35cb556c25301b80000ee235c82e121de40325980000000000374c7db7ca25083c998169971daa00016371e991ae3970000000000090d800000000001facc86000265a30d1a09906c0000000b98000000082ca028000162a3ab197ca0a00000001b0678051ba78e800088b80000000000000044a000270e000064c783546e4c78d20000000067980005eac0001991b1051f00000001a1e0001402000000000000009b38852000000038907f90000000000000000006da000000000000008e3019a8980b5064c5c7c4bf8a88549cefc00019e07f7a010000067053380000f280ec00025cc6a700005cf40000000000000000000000000000000000246600000003f38baf6c2639618a8d1c000066d1a8227237887646dba1ee0000c641fcc33c9a701af144993a967240000000008b3800028d0f7179f875d43a28062e4506329600387b208285f6a33a000232f08e9dfe0001a7e7b803c800000000001460000194263f80002b781d70001736000000036680001a48dae62b0d1e784a6be48d400055d27b2453204c6501c905eb04205e24000244800034c4a8400000000001de19ef516200000000001de900022e0536800000000003ca19725edc4aa00011d5849de11056248282200000000a860de242c0550edd1ec8000000000092c837000000000001d680000fe281195dd73ddb08845823408320166ad94200000afc000232808208ec2aeccf69244d84328619a7a503ac000118a00020f56f380000000000821cdf0000232e0001e040000e0e7c390dc9cd8000806800092719e84791b369abcc9800002ce0000acc00000004ca226800000004b6a36a1eb169a7c780000000000784220c00
  | 31 => 0x78c0000000000463a64a3dc0000537d88654b17ee28980000000000000216a07b00004dc95545ac9800824848057d8000367210219a95846d215dc8fc970e54392f02618dd27b603da74425d8a139a22519970015913247182520415874d3ec12dc8569308966000069317b181d0a0565180009ab90461cea53772e200e3a292422290000000000086c0514437523e6fb883774810270000000589927f00013f600000004c3a47a48c8d3a35784de3faa6a680b97aa9111b3e2e0233c13e85b86d4259a9a5cb9758a178c20e144e00000003ea000000000000000000372cfa00000bfe9b687f85eb522f6db451066593b99c2800026c9f5544f014e07f87523c1627a00028109b00b6387096893ad817827a12fc1601a4a7cb21180001b7100000007e98000074000023300009e396e020c45b600025440001aea8c1cc3c0000eae3ec8a3e3158000000000000001b7000051e00000002b4800096080005f519d800000003b81af40000000000000022ea74964d257d000000077c93426c719da3b7c47a262150a6550a090e7181e31823ba000267e7518d4c0001dc4000080d0ae00002758bb545581620000000000255482880002af82b24789dc69f39fb489b13a40000d97941858c00013a05a2c0003448fa2000029e7b310be0000000000000000015f72e8116a4c5902e00002b92a39aef0010000000000072980006f280008518000669a14c8b2183e332212519ac000196044c0b3130c7a700b81151efe3469e078c3c7ad2ee8ef1697012600023f300013d40000f120002298826048a000000030c824004a8bca72a216064c0f9400000007ce00003e2460e97ba5b96a48c991bf06c816d13dc5540a082cf15ac3b517d77c8800088380000f9011c41ec9ba000000000015140001c8a638000058b15a207e80008d10fed000000000002e8000000009c675a8189f44487e36e7e7277e000000064f800000000008d6a5350000a6000014e2000209c00000002ec470600021d69bb00000000534282a67485a1a4867190cc0000fcc8600d3d9a517541381978666e7948488bac000040a000089c635800075f19ec1511c9f991932001da84c077a6025841095962c18a186961e02ec00000028724e6e1583fc840868205f26bfca1b05c56212c81d7873fc678326ce3876419044af9616377144049161748ac9b8e6e9231f00000005f1c00083b8000323000000180000049aec7948000000168d00002068369ae22879b9430e80002aa833e34316580000b8da0253f20001170000008c0000c4c00000007f2878e0001f628c309e63b3933f8bfa7ae32c873c06d0000283063b0000b2a000187429700008f79ffe0000eea1b10000300c290895185f000178b000143a53f000022f82ae37606b437066c29f6cef369681db59a0000645a2ac66500
  | 32 => 0x5f00001b5d79187764b506094fc11787ed4f571fd4fd231de47484017ca00000003d700005f61cfe1ffc00046400008579c3a00000003001c86a06400091240004d3cca51c001806009ff00001b020001bd3570089205f214da0590760001fae6f9800074f91fa0000e9600013b50d9c000000000040780004db000086a8000986535c0000000000261698d00000001a5459c00002a80000088938e13403ba20f0000000000053286af23e68485f4427c390070a2158c1824919d45b785be5980a4455c40001c6800036f400000001660c019ca6eb8a74613800005a8000917206a62e97e135b540460b96fe000067a0da000074100004318f5944a000035d1d9a87987fc5a99b018f8800025b8f907042336000000068d904d9e48000000000047256b89070f240000000000232177f63e00cb1ce190180001a927594d1800000000003fe0000000000000000005f14bb40000000000000000002a6000010a0000000000000059d10d9000000015a000000000000000524421199200015ab9698a9e720984453257a668b0000838a7c61f7024a22a9038000048856f921d5bb0f6479099c26645ee8000092c356800000024e84149aa008a989000000005eb800000000000000000000000000018b60000811000286e446e61e41e0bb700026280a947873f840004c106447a780000001d925740000483a61212604848df8887000037685b25f82da9c268ab83903538ad60f016e69a85a0d30b9cb957f000021043f20339f6192588022a500000000000000000078d14ec55591207bba05200000000c9d34e0000ed807989a096781e2436e6240a90c0200000000001ed000000005eec0001df0000000000000020ac00007c800000009a3d7c2000000000000002090ec04448be300020c600027c8000000058c91ff7c195e666a00000bf40003eec00000028427c6800000012b000017123cad2892d300004ceda0f12d97de612e29c1ba07ce0ea99b9025021e9c7067f0000ad076900908f90d297360000000000066bd4a800015ee0751f367e321ca4e74000000000000000000000f079e70d1500000003d6256600000000a8918433ca2400000000000157e4f000000f5978e000000040e40003b703d20000000000081000002c22fda64048ade0a0000e0c00008dc6e79dd20000000908a14a11ec9be00000000000aae6c006c013d81888290dbe8d801207b18d4a4a12541000172f171201423f14a498700002c720dc48991cf65680000000601324232004196c017d00007e419063c70540795645a6d800000000beb29280009f006943e150b548fca826791fb66e8269200006cc6d29792000026a22640009eb65ce0000000785800000014223b54000901c00054c19820001a8a0000cfa2d1c000000000011109b09b1d9de357d55c0001a403
  | 33 => 0x30800013e2000000010195bc0c10f0c1278c7800024ec00000006fd2108894019470c882c53a8bc64680b066579e5800000006d7ce82000000000000000000000000063682743dc09e9d1e1bd03ee00013cd8295dc89ca05021421e6c000181008b915096b02d0476000012f000000016d444e8a004e1923b86389c60000f7300020c358d0de65ad1ae440a8e444f2400083bc00000009d000000000000000741c0003f089344fd5e8600023004f7953129c1b889a34e6821fc00051c9c34a1712ca36a8f9f18c0e9400000002dee3300d08ded000124417d994e04e911d3c3a14b47992881dd138c29f1df9000147a1cc0d47317025272a800000000007638000a04680a00014523a8a7162b68ae06df0a400b34c8000007c205ba07e000000000025788700cda40624b644e1ac865f908a45a1fa44954f309578b6106305da46f20de04897c347c84fe5891b5870b0d0500009c01248c1a28ca1287fb814c54f048e4d260ad7db9afd43926f43c2cdf806f4fc42fc865079b97222bda3f60188d92a129b2647f523671c23b8233c4dc19b95f88c74c6c0978eef1fd936018fd1a2000108d00000001891d5a4e7867567200007169c78387a18c2ca5d960001f48a0006ae5a70d8c000222c6680ea82c30d1000000000000000238118c95f800000000003f4d6ae7734b05142585d1a165bc5ed0000287000092402bf14ca52a9d0000052f1ce47d28000975a3729b9114f44e5ffa2600b930000000000000000013a20000b2d6e9a3c80000d5b00003cc0001944000000098304b08f720fe4b899c419283c4000232274d07fb3081bac72505580d3a57221940000000000247800000000000000000000000000000000000000000246e66ea6e859210930d45cb468c9d6a703857f9aa965c4368faf00000000000000000000038724ba2ed80005ef53263640000000000036b000064998a448494e65561676994800000017c48b0136100009da00000009d18c6b3438000000000000021d40002002780c00094089107f183e141ccb2c26d1b6b627000000025e80001384488000029b8ee600027a434340003d100007ac00000c54c307028000358a72d57093bf40359ea38100002cfddde44fc0008418000000008500003189eec33390048bf0001fd42b3968000019746c589d2000093b6669fda46e47f1511a00400017f62f8a2620000946000078f7e0a334000068a00000007ac8000411259170c00004a79b2495224800000b104b180007bb000000000005e9c00020a91ab7f210a4a0880001d9a7d73d39aa40000000423c000000226e9290000817a4a10000000314000000000006dc27e074e972b582a87400025a91cd400000007e40000e74655800000000006c29f987ee000000009d4681de687fa07f2722000000022a8000000035d9
  | 34 => 0x800047a80007230fa50000e2a6ad00004a6000000023da000000052a80000000e7e3090c221a04f8b4771998472da86772660a72d8310415da700b88fef63a23ec000129200021b8946273e8ada4e0538000000023a600010a301790d20a525ca334218a64712140000db0608e3b67618a0e027a768454c6a24e448f757ea830892028b9d8188a64d8f8861181989d7d04878080004e627960000000000019022a000052e8cd70000c2827ea13a910c72a03884162078bda3f455238d1a7440aa0fec00017278c480002978f526770fa77601350a189a3840680bd00000000000b274c5000028c1c760000d78000000000000008c60032198287013086ee41d50322dac0000b59a2a563000000012f600024940000d452ee000015d09a300000004a4679a0d982240001510213800000012697c980004d7a804833000066dca9245c568488720541e740005e845cf7fa8000415000000000009cb00002b626cc6e3000071a0000000000062159be94ea50e0001e6276f00000001622512099a80e800000001120001b3c1fa845a0000000243881948a400007d000033b836500000ba528000061f927400027183138a2060e8f541d6c89805bc46b9f68d600a100002bd1e1a993000000000009e84000141c06a018000000000000000000000000073311e50000e4e803078a8f1934d02b80003be400000024768df1066850881837b20954e2256290c951c6f70d5c95900001ea4000000000000000000000000912cac4622c00059995e70000000000151e8b980001c30c1c0000cd95cf26784bc51b760a1e9247f15ec0000000000193ca05000004d9512000000067b85a600000d80001ebe40d40001938b705a41f3e04f800027d8c46000160128540000000ef71e540004279c044d100003d957b26d51ff600000004da08124a395e4000000000000000000be03cbc00045f80000000c8a24b80006bb99a20000ecc8fdc0002e9400015a800081b179034240000ba4c585534476a1000009c9a68688fa724797a1866cb9ef61b8193f2fa21a278725838c380000000000000185000017420001eca96b86229e25a7a72cdb5e9b81b5b239800000007928f0a126000219e7cc0da60000000000000000020bf000000038d8640558800000010587c499180d64e7a59aa7ca75d800073980001709d845aa22f42a6242035a80002dba2840000ca80001a00277c0005d795360000f863ca800000020a85248c7e5f300000001fc206b08bc9020c0e95c0554228800000013c26e7000032d0000000268c000100e0000cc200000000b810282e500000000000000000034a000000000007b68a6696e08660002786000000018f9af29ee400079d00003f19281956229013e1c6c0000000000027000025fa323c00000021966e49a345811b3a0001c9c4929f72
  | 35 => 0xab000000008215601de00000000954a1d259914d000008b488e0000000000000008840001e966730deb00016cc00400005f8cdcf7dd23ac0bb90e387d09585c2499c037524609b8abd43522d80000e1627b8fbd30a95484e3c0009e10000000258c80818920091ef4040000012b0db268821b20001eea139800000b00000001dfa3dd9c1a000151f9cae13c04c8f473408000366208609207280000000211897c00000005da000072c57e2000000065818797d418b2000011a4ce0f1623464480000116835000011d000000027026da000079306100002296000000096f9f9e5599c462458cdc23a159e422000093a800000016c45cb16823c2250a000000000008490e3800034c80005ca991a1a61286264d97617991922e29fc000007854fae584524139aa03cbd94ecd0d69a6deb4442127615b9bbc48b45031965b663d78c923271f187402695461a7dc000000016880000bf8000000000066a5e065d800000c302b52ff00000001508209a45e70d9ab000018b892b0fbe8fc04ec53c8578356202276885c81d40de418982a74f680001918000000000060c000000011c2006870e5958efe65b1772843950444c8b486640f720000352000002620000000e48000000000041b18887b7222a000182d1cba2149c30428647c0002110c3800022d4667000092797e73ed223c7f700000000000000000050f9a822e9000066a81ca42be2f06ef63d25a899640000000497a362150931c0000000423865ba1e00005f809ab5c70a620a61dfc66c4b660000f0a00023f14ca90e72689923000235e000269800000003f7a3ef0000000000208b618000000017569e4000000000008f3937a19f108c4a90da4000000000020422e75f1c78e135400011aa000000017f00000000fa40000f3c79701a200006966fe00e600023b200000000000944000000041c8a14000245000000000000000172a5040001b7300000008ba80006938d8e091012e00000000000000221579a23d57a0000000000027b600000007a600000d880002b0800000000006d340006aa92300002666000000021e847024800003b4d51b377d54e7f900001ae0000000283810e000081a1cf8702207c0e515466d59b7e75d00146b3800000022a200000007be0b6c09ec00000000000001a6248f0a279e090674a7493736f1047218dc749d21ff20000000799e2ee00000000000cd249800002d015379dfc1f8000285460bd99e1f8141e47dce0a000000055aa05a000000014c000000016f00a20e3e80a823600000008ca843e00002324141b3b783863d9ba88b05cdc00015292ee000027861e03b600026600e9800060818c00000bdc794000000000000000000771451a0000000569cef552b21ac83400007d7800054aa7146f9001c3410374428267a1818000000115800000005b4
  | 36 => 0x1cba02a87320001e2c06da1dc7129bd773d1df834b80009e5c8f02529af887e220a85004829db9b676cc8fe382014cf0a662be422456016715346d1c0d406c23f5310847e72b835633764cc04418848cee1e84d4c0008ce000032f986c94780000001378492c00033a225a8cdc5e4715279595fde7a0001fa224d9b5200023cc242400000b800031987e2509852200000004c4800000009f49221df00f3a1da6338000328044600000004275cad6a61bd4000000000025e21e30000000054800025fb9768000a079de80000000940145e1aa00fe0001520a0358f27f800004da9bfa52090349811ca596c800000000000000e4290780000001b57646d262386881a22500001d100000000000921054600010b103040007d380000001f0c217a73c4289deb48e1d4041004783db208407480000fc0ac800001ce3ac800013b80000000000802000000000004580000000000000007704180000000000006f0000430e73a00018ae00000001621dca3e000005409add000019d00025fe180a81c1288ea000000000b280002d592720001e28000000000000000b8c3e271ca18829aa5385269c3e0002064532c000335000048e5db67e483300520e564b60c7458ba4104a421501299740000000020059bc00026205e4672a49a27066b8e2343f500027061e5a7795d9c1f9cd4d000247000013aa29e00008b319285c6a66272b07d42d78bee5eea7ac8bfdb903b6e3062b88276969000000001c212e000018291ca93e8255000188e03b8000000000082f80000002597000286800008c83becb3400000002588aa8203982a00004e261208e405d672200013f403f00082cf9bb031453eca19041e960280e0000000613c0006d69e480000af8000000000f98d4000098290f433500000000001cc287c0e9209760bc00000005e6e2d00000d811a40a8c00008c23ccc7594bc95242dd000000009287d946381e2000000025683b6585911a0b45986a132575000064e00002324000000000000006200000000564050576c968a0002630404800000006ce0000590a00a14913d00001d2dde6000093947489088fd0686781400054c80000000c040000000000286600025e60001241000000000000003c84000112000026a800000000002a7000000000006f21858161cfe400017664aa8b380001ff800019f618e800000000005ee417300000000761cbc00023660000b460000a220001188000234200004585b4000075b14d40000d9e000000097423087ab0000000282e777119e0001de2021df1008603a207adaca0000f4510b24f294c4eaa00000000002323000169e00002c688211db00000005c0c0000000000000282a8c9dcf22cf501470aa610626800000000521ea17a288da7235728000000000044b00009ea66580ac12107300b2e37a9758174800
  | 37 => 0x18aa00000001f540004d61e66000122e39988543b90d3856c800023000000000000000000091924f00000000000000000000000001c5000000000001345000148491ccdee19d8c761e085960000000368976e4f5610460f00007409e402e7800044d8000915000000000000001eb885f958a9fc000000000000001ca90000000501a4349708000000000056a00006b640000000e8000005d073d800034b400000000005f40bbe1858a2900010b00000000000000007180000001b6f00022f9000000070306b6561519c0d79f66615135603a8000000000000022940001dd50001e8e73880000001941906000003c980a7de90827661ada0001620000185a0001b1a80e094e000000000000007a926820000dfe4c40000110a6ac4ec90c4000000009344318a011e08c11fa87eea2fa2d349305b38000181141889a913d04914f667d502c79c26680000000000184297ac346691a852000000000003ec920cf849fe1a3c00026fc000266a6d0140a2eb4ab20000fac0001c8009680009248000a1a83203bd892d2d9e59275113e87eb646c27a97a3990a5a09dc0cfe00000003a314867d247349fc5e6a0000f1000011cc0001a689ef9b9a1f8e7f400012060bf083f889000000000005be1f2e000000021700000000e025be8000000000000007dd38d00002d8830e4ae99685d680006129d5200005ea0000f9897485c06691f5159e000007000008b08000994c24e000055c3f28cca23e987a000071c000000041c400000017c81d0800000000003dd20c034927f276b1a9e82a9a1648713a77e500000000000000010300000009ee802800009cf00000000000d1900019d600015423bfd92e611e0d680790d00000e784a800000000b60564861200019b600d95b05cd000015c00009538cde826a44a6a106c21d318e2000000064b400000000004b78000000243e00000005f3a12e000000022b9e2a00024f62500b822fe927e17c0a2c731165a1a383a41690b7632d822013383b44b0279b0d5e16657d04ca5f1821c77ec00000001522f0a6ad33c1ca133a96ffa099d9450220b300027a2344d78473040002bb287c265436063b000000010f600006620001b760000000080800032c00000000000000000042b400000006ab76f8000000237a2e9988061c00008048682000065218b13ce0001650000251c2080b1a0000dd600026486d0c388685000053e94f00000000000000071e98f650f0c915fe9e6457a947873f13b620540000ce265e0001cfa97708db000228e00000003f54108000000000000001b5800004112bc401031c26b000000000c053f800077d0000000164400005263b9e13000000009e32730493a57300022de000000000000003c240000001cb2456800a259107f0000a02000000000000000001d707b08e620db800000
  | 38 => 0xc08ca74d040003018072586000027c03632a89dae4f30f3e6189c621de140e1cb0400762007e85c082300008d80000d224e4800075900a00000ab802d82e64eb04148548000000174c000170436224b400000000eca60e91f8000000154a7a699629c7909c7ec248e7d921b667024402eccf6e3ac0e6464b06f0067103f6ed83542919ca223c90e593003b00000b870228b5d1b88000000181a4ff17641e5c0009e666d5794d7ea0000b7f04e0eda90692e400027b81c8952f8848e1431c81460038fcf7d1db7f4145dda0000a245c187848b914cc98194e89f559b03cedbc5180cf1e5dd07b482355891c409540a69e3236fc4c6029021665ba6c839c89024244f4b9fb0df48ff4eec50720a039b8e031d000001fd000000000004f48000560837c92f9c202fed3ba654a27c00016fc40080000a3905f476887c09f4f0614f08087b259ac33585f500015b453780004bbc000000209100000000000000410644e0000000000000000018c200025b797240dc00026146f580007b78000250839846d8ae80b69b127001ad85fc0fe61174d821e8806c00010e655e08347a080001c80e4c6f1800054580001091d320000ce286f9f6b26b80005151f521f64a0f58ea2f84884f2000012ce41863c05d48b304389f7840b4d868ac089385b84863b4a28a00024da136000005d1b8a00012274dc13f900008cb5e916f400000006e880003a191b09c7c1ae22080009c825ba13c8000212a63e205000045be7ed8278d189fa07d28e480009aa1b7967067326cc05d163b8000067c0004950b680001ef015e835c3e284045251b4401d081d66ba0c75634f567351d0e96d054e4fa5f08802800000000b200011c030f80001ac8fee000000007b8000205800085708ca0a80f9e41766b80be000048680009efd1f609324de4cf444009f8000774246028440007e584be57180001a7111c40bc00018f1abc0001832000000050b109f00000004ff800000016ee00000005e7c000000059e000000079e13ee19340001a3c00005080004d9669f5ca5f025c40a42401478631695983ce81da8c4d33c460982b2ada4b072f468900017d20001240412800014b00005a19d588339b4f1d5e13452b834a73acfc16f008808111f5917e000089586f280d8b5a098a6b08e902be8aa8b9b7a100bc499e73331c1fb90f400005e152934b5a386553098e30500004c0524900010fd0000718000264481d879478f07a714a916438f247c13a1882136969644b93f87eb18ea8ad05a585d919a28d80005e2a04e0000d3439d9ad45a4957b504000084713d8565083e000000000014289c84bce0000000424000056e23822f3000000001c510c8000000086e7c0060c9e60825000000000000008ea800094b800055c0000000000098e80001e9000000000009d40000000000000000
  | 39 => 0x5df0061f3a20100000000000910a08500020b599927e643d0bb29188d16477419663d0000043992a000241554b8584000000083b400098a8bae7a28eca000032290fc7c0708800000000009458000000000000025c03fa13c47ea65b65358af20770000405c0000a58164769800000002920159bfc78f98040001dba9a65d66a068a060b900004461016000000000006bc0b000003a6800044ec00007f1ea665217a500023d6331800010c084b9f516ca03fd0243e08fb77d9c000000150c34f0ffc197907000002f200000e448d00000000c9a000000006a8bf000000e09568088000258a00010aa1dc80000001f868550000500010c1a345045309cbe96040d20529d7a42007e888800008d3821070791b594f8000000000099c000009a26b2000000000000003bc0e1815f9106027139500000001da093800000002bf80000001216406547e7c924c64a9956e177e4047468f7e39c00004a7000000007fa354800039696dc0001afa000000069e0a6400004506ba00006848f5f00009681de98dc48089fc8faa0a6519188c000086441be85688c87c620c18263450d1774999f06ef800041f01f633101f207053627b127a842b00001c9a6fa93d23b43ee8a8a7821a560a180004fe8000225800000001e0126828200024d26ba4c544ee142e9311714436152207640001e6400000001df0001a66000144437100001148000447800000022c691480000000000000000000020569bd8086000000000009d163600005f90d65362993256580d54e8d06d9508f4818c8a1a35a2762000219c0000000000000056e8000264855234ce048000000000019b20000b37023861860f5d0d48e80009f30000000000000000001db9b3900011a667d0f5a000000041f922494d1bf004d00002e680002368b4a00015762780068000000067e0000294198f8ff884c6f8886a00003c200000000000000000000093625c8699235261066e2000000002a0c2c0000000674000001f26d4744890d76e589e330028c73796541d689f8247059840e8f663bc80000c3d1d1223c000615a33e83284103020ab40698000592a1a626f26fe6ca098a00013e400012b82d526ee43001fb0d5460500000007dd9e149c1000049b0000000000062f80000000680000000000004c40ba8e267cc80000000000000224600024680b7800055c84a000021f677b090048304b2000000035bc59295b80000001102000161a0001b6a233800000000003602270381909663f167a361c000000133a35c0888909a28c7b88da80000000000023e04a01f19edd86e000002a505076a40c1fa72f00000146278a78c27d052792e840f28209d60fab7090f683b5927800015830e3000000016b69acd6126ffa7660000cab0002266000000069c9d5e7d806d27268000644214e43080005618f395
  | 40 => 0x2af07ca00000004f826c62484000000000005c000000000000d40000000076000010ca19940007504000939800012a000000000c40000e125b180000001c980d8400000000000000000000000009d0d6e9bc00006ce00000000000000026c00000000000228000000086125860001dee00025e400000003ba1df77daa58e55f04cc0000000000050a0001bb84108316000135a474c000000231680183960001caf4b31d2c0000000000199d0000af3000141602027fe1f84f6d9da917a3cd00008b892ac0001662177800001204188fecc1e8c680000000f5d099882b000074ea02d5e08588f8729d83e80000000000000000018a229680000000b260000000a16039e0001b1194ac0000000000000000090dd2f8629886b00000003f400003e663322f787bc75500000000c9375827fa00015b132740007d086288f5285068387917a315a1773270800005663a8c000000000000019581db243890cce7c000235c4720d48927550663e80007a800003f7268e4c08000199c0004ef11f421c89567e3c00097d000000025a510080006dd00002ec000060d282c2281acd21cddbb3cd90a900017430001e247761f7e28128469d28000000000027780007148dfc86507488778a489d300008efa2ed2d71c847af0da09f10f4a3df40007709782311042a8a2000000012e05ae996aa1f84260000b7e4c2978600000000000000000000058e0000000000000000000001af6437a3ee00000000001bf28208460a168b437b905dc946a0ae4b41b980000000000117c2ccc8860101ac4829c0009a216949e8005a00000000000000a08c00015782d13120d2535b00002cbc000000185c21d9374261035a21e00002ae80001ce2136728232456e4000000000066240003058bd47f30000000032a7860d4197b000070580006829ed20bd80002d3a10a28e8000832625e9ebc0000001cf05e3c0000000000565cf7f8740dfa51703870f797f26d6587c5fd1cd632218c8091871226a013000000000faa632000024204b181c0000d0092280004dd80002cc80000af400000020a15ce9e7201100000f1c00035f0b7206fc4720002340000184069f179411b94a2943000050d800000010fc000096a00000009f08000000046c2120bd0344488e327800061a80005ab1f1444a914694c00009b614f842e214447e03230000bbc21b000025c26541471528317a23a512800017a0f5046b041c37c80000001b4200027e46f0866600022dc2e185ae73816d80001a889491fc42d9000046c8000000000013c00000001cf582c40008d31fd600024d420327124b140000001dd41e2c7b049aa59615d817685f0d536c120e49a9050e3ed429c000153a44d0f5b000017a495887460b0fc8000106a847800000018d0008931855e8cae000000000000006a5000000016f55c91
  | 41 => 0xa74e16a00000000186000045c00009e24690dc000000000e0e83653b83841be9b18822818e92800000000000496106e3960be43c6000000021206030000421c0004dbe4ce88100000001351647a11077bc000432000000028185f7131a000000000026833c060fc94520fa64822645c6c0843ad181948b281b772d0b7000248c1cf8cfc6d38d694811d3c00017e87121a100000b783bba19210d0000000000000000000000d7a879000000000004a6da504c18ed000018c67e80ca64a300003cf442e796cdaf7da11fe293000093fa190000000023493ae6aba6d264480008d20bf80000000000100800000009a8a5b08808d94000066900000001fb23500170000000275618020b820e631428f27547679ea28a980001758d560000000780043a0002824779db786d0400000022749f48f110000082000000024f815a1a100000001778a08437a0a1c00000000000000000235a156000197047a00003e44000249905c0eb800024943dd485dafe06e40f686f020e00006437b000000001b4900000004a68000000000034c223000000003fe5dc06a9a7fc9b7052832a9a749ad08350001d8a000145926924b83a9028d1a31afc52c033674da5ea79f1cea21825fc0d3229e370944c35e631e0cb9020697800000000008bc98e45a900008de08de62c0358748800027087e5000231c00015e200000008349cce00000001d78832000277a00000cc15f19d200021e28e88eb582c0f13033d98e42040001b9922a0000340000132e93299496898b2b38ea4412e380000f805507ece6369df00003e4c23c7be95b69b9a5289f4e439363425009905b08800b041944000000000000017a876c0ffb79801c90cd138a2951b058d29d0925d0d7f64cc74a18d1540000000000000007c8000000000000000000000000082d00009fd8000000000099b800034997af5df00000001a900000000000000000020c235000000001f9a42f0000694a39c5cc19fa44c00009d6d48a0000000000019e777465a9a794e48d581bb569146a23880345c5a5935c200000001b770001bba49f0000034400000020c500000006c38a9a000083a50d5c9e92a1e540001c7e9a940000000000220dfd8000043600023f900024096020fae7f9964200000009959e4a000000000f190029493990000cb81b70000000224479bca01000090539800001048ff0314800011980006d19a3078300000558eb3616e32c0130ee56d303720c0a36c59b0000938800000020725e3400089d96aa8bd8d1b49c0ec80001ab800000d66258cac00006b07d5020a96ee39a10f00001f98f9a0000000000240a4cd80000fd80000b20b586b5800008108d00001d013dad9f200002c4223514847b1ffc426d1766980b0068a000c9a8c332438029d11901cb4190b0717e9dd123e241d70500000000cd8
  | 42 => 0x246000000000ce67108fd800015fd61d800000009960e196da50c1c4c4188000422e43b000159a00024ee000000030480009db179617b84966c507d01ba9dc75c7d0a800000006050114000000031a0000876138200000000000000000061c00003120d361ec6c7a5d4823170b00000009e9932c56a9d7e5b0800090a454c000103e0000f6a1af80004d21c56000208e2c60db8000000000017b5391800014000000001e884d4a1fe64759661d880007d583131ff853a43040009c9e56a91e0000000000000022285a21c4400000008a69bf645480d763780006af9d8c1ee00004ef826346a00000001eba7509d2e7f88cf80ae8dc621a000000024d01bd4000989a608614c00087a8b7a719879c4a880001780cce75b8000211400000009a6000227e0000b793a1110c5af800074a8000000000066285ac5c5c0000002178000126f79ac000303c0001c5000069b0000000000026d9cfb00003482268ed771b8f9c27292c86368ef80d1283ea1b000097b4000817000000025e05c9400000000000000b168360000098124864314a621bc0000960000000000028a07543cba6bc9e9c6e43f2c000348d7fc0000e52000000000000001c100000002005000000000000000000000913400043c0f9202686480001f849558000000104f0001dce97100009b4000000002b468b85ce07100000dac000000000052d1ca40ef8eb11e58d63353cffa90b9cd2197096c4828ae6070daf193f1c2e134a7eaa1d81be4df23881138000419466100000002bc000000000005f3d5642ea02b6523206e8c4400052f800000000001b4000092b4c6245c9fbc9a4000074dc9900b509d87a6c00055bc0000c912ff8948ee395d0aa60000a4e16f15266494afa3b10d073c7c000207cfcd9531af032522ba1e6a4860000000160800000013c65f6d11100011d023a800000016407d0176c0001b5c0000000000000000021ce00000000000000000092a00008c409cddc35cb8db400000004df8d0b6f10d898c415e846053662f9c7ba6bdc49b0340f4d43c8bd62e5a326a0f13ea2169ad0204c0002c21ba87e2800085c9f5a0002742008134c654e38a3de262221007276125154717866897d82302ea621a0058000000000001985818ff13b490e80ac8660ebe03e800080713ab44516a031e93b09ed1652224106800000008c288cd347caa481ea1fa0000000000139f2c3a398710000003a000017b1b643258000000000000025c61e822100001124000015e0e0800048600008b6800000006424d900000138bea00018247ef8e286348950743000038025120001a9a397831e2e8a67c5fcc272341a6765ba90b204f06de00000000c696e466127d896880009518000000197a8e3800069d800063325500e680000000000000110402acd083de80001321836000100a06e
  | 43 => 0x1e9900021ba459a4aa16a85cc4e9805091188580000b5f13f00000001a02000203c98b0aea0b49e591959bd03c00ede43b1b961680dd4887905e1b1800041ad74e000149800002dc8691744000000000000008da0d03a1559fc87310940b6000024cc2ec481c000000000049492d241e49a55d1a6b637809041ea800000012576cb20f82f9a4562e3181200007d63f762d287804221bd984d000069a97be17a8dd8fb800000006830000000000090c08c144f80006038a1221887d800024a63209c926b95c1c24500006280b49000000061a0000625163e34a8b0a82508f422995a60000c262ce64ae55dc0008cf40000001a1c0001d3f40840001fb40009a29d5c8c04b900001f63648400054680000000000779275e5f9800048dc1e4886007a0000000689031400020c86dc807021d577e2d5451602d102602c040e0e810ab42692e62581a063ea43fe000000025c80006e124dc6f4960c3f95e7600000005c752c400000004458cd50001ed4000210c401a7786b9a0c41ab079035f84d445b170190f1f4654e1a6a000025f73688ee6bb613825e80009a5809225f80007aa06ad05ca1ae3bd074915c80000001bb450301448ef09c4295a77458d96e839528088c340000501b2a0000ac600023024539df35ca06bb00012ea0571575000000029a0000950130000002141d58fd60f50cf40000000388927a000090a41f66612fbd73e000075842640007d607330001fd24fc51008d600000000f023b8400042980008a4800000020307450fbc000000062f0dd0000181739205360002618000000000002aa0001b6c000029f00000001718000000000056bc00013a826586a04b44ab979c00000002b91588642069b25e00006f6000000013d000000003d840004a0000032f0b44451078023d8fe73d180000001c28000000047840003a9a286000133006800000000000000109784b0dcc45b607b82e800000004560001d7
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x862d6454a3004332a94c3180219554d618c010ccaa4b0c600863964942300421f3a4ca180210f5d2650c0108dce5328600846d72994300421f3a0ca180210f5d0650c0108dce4328600846d72194300431aaa4c2180219954a610c010c6aa8b086008656535843004332a92c2180219954a61880108eeeab0c400866552586200422f39eca10021175cf650801087ce9328400843d74994200422f39cca10021175ce65080108eae2b28400845e73194200422eb98ca100210f5d6640801087eeab20400843f76950200421ebb4a8100210fdd9540801087aecaa0400845d7598c200430f2a4c6100218755263080108beeab18400861e5458c200430eaa2c61002117dda53080108baed298400861e6494c200430eb24a61002117dd953080108baeca98400861e6454c200430eb22a6100218b9925208010c5ac9290400864e639482004326b1ca4100218b9915208010c5ac8a90400864e635482004326b1aa4100215a5c15208010c6ca9308400863554984200432b29cc2100219554e6108010ccaa5308400863654584200431aaa2c2100219594d6108010caaa6b084008666525842004332a92c2100219ad952008010cd2ca900400872a544802004394aa24010021d294d2008010e92a690040086e161480200438aaa2a7880211d5db52c4010e4ca8a9620087255454b10043a329aa588021d154d52c40108eaed28c200847976d5210042acb9ea9080215a5cb5484010c72cb2a4200863965552100423cbb6a7080214e5d35384010ad2e5a9c20086596594e100438caa4a708021965955384010e34a8a9c20087195454e100429cba6a508021565cf5284010cd2cb29420087295494a10043a4a9ca5080219a5955284010e54a8a9420087295454a10043a529aa508021d254d52840108f2ed28c200863765951100431bb2aa88802195d965344010caecaa9a20087155454d100423b3b6a488021595d65244010ccecb29220086676554910043932a2a488021c95515244010e8ca6a9220087455354910043b1382a4880219954b6044010ec2a5102200876152481100423d3b6a888021565cf5444010ad2e5aa2200853975951100431db2ca8880218ed9554440108f4eda9a200853974d4d10042b4b96a688021565d65344010cb6cb29a20087195494d100432db2aa688021c69515344010e32a8a9a200847a76d49100429cba6a488021565cf5244010ad2eb292200866b659491004394aa4a488021d254e5244010cd6caa92200872a545491004394aa2a488021d294d5244010e92a6a92200876271549100431caa6c2880219654f6144010cd2a5b0a200873154d8510043a8a9ec288021d854b61440108f4ed28a2008761529451004398aa44288021d454e2144010ec2a510a20087315448510043a8a9a4288021d85492144010
  | 1 => 0x4104316aa4c4208219394e6210410c9aa7310820846f7558841043172a2c4208218b5516210410c9ca6b10820864d535884104237bb4a4208211b5da5210410c9cc7290820864d639484104237bb2a4208211b5d95210410c9cc6a90820864d63548410431caa4c0208219694e6010410cb2a7300820866a529804104334a94c0208218e9516010410c72a8b00820865a53580410432ca9ac0208219a9496010410cd2a4b00820863954982310432ca9cc1188219a54a608c4108f6eab04620863954582310432ca9ac1188219a549608c41087ced2a2620843c76951310421f3b2a8988210f1d9544c410c3ec929a620861c6494d310430fb22a69882187191534c410c5ec9292620862c649493104317b22a4988218b191524c41087ce9b28620843d74d943104237396ca188211b5cb650c4108f2e0b28620843d75990310421fbaac8188210fdda540c41087aed2a0620843f76550310421ebb2a81882187992530c410c3ac9298620861e6454c310430eb22a6188211b5d6620c410c5ca9310620862d54988310432729cc4188219354e620c4108deeab10620862e545883104316aa2c4188219394d620c410c9aa6b10620846f769483104236bb4a4188218b992520c410c5ac9290620846f765483104236bb2a4188218b991520c410c5ac8a90620863a54980310431caa4c0188219654e600c410cd4a5300620866952980310431d2a2c0188218e551600c410cb4a6b006208659535803104335292c0188219a549600c410c72a93044208659539822104334a94c1108211edd56088410c72a8b044208659535822104334a92c110821175d66308410c3ca9318420845f7558c210430f2a2c6108218755163084108beed298420845d7694c210430f324a61082117dd953084108baeca98420861e6454c210430eb22a6108218e9526008410c72a9300420865a53980210432ca9cc0108218e9516008410c72a8b00420865a53580210432ca9ac0108219a9496008410cd2a4b00420845e73d96400422eb9ecb20021175d66390010c3ca931c800861d5498e400422fbaac720021879516390010c3aa8b1c800845f7694e400422ebb4a72002117dd953900108baeca9c800864e6394a4004326b1ca5200219398d5290010c9ac6a94800866552986400431aaa2c320021995496190010cb2c7284800845e73994400422eb9cca200211b9ca65100108dae5328800845e73194400422eb98ca200211b9c865100108dae43288008655539844004332a94c2200218d9516110010caaa6b08800866552584400421f3a6cb180210f5d3658c01087aeb324600843f75592300421fbb4a9180210f5da548c01087eecaa4600843d76552300430f324a71802187592538c010c3cc8a9c600861d6454e3004317324a5180218b592528c010c5cc8a9460
  | 2 => 0xa6a9021539cf6454810a9ae7b22a4085687059152042973a6c6a90214b5d36354810ad0e0b1aa40870d4310d52042973a0c2a90214b5d06154810a9ce630aa40854d7318552042973a0c0a90214b5d06054810a9ce6302a40854d7318152042973a020a90214b5d01054810a9ce6082a40854d73041520421ebb4a8290210fdd95414810c3ca9318a40861d5498c520430f2a2c6290218755163148108baed298a40861e6494c520430eb24a62902117dd95314810c3cc8a98a40861d6454c52043172a4c4290218b5526214810c9ca7310a40864d539885204237bb2a4290218b9915214810c5ac8a90a40864e635485204326b1aa429021879926314810c3cc8b18a40861d6458c520432b31cc2290219558e6114810c74c9300a40863964980520432d31cc0290219658e60148108bce732e840845d73997420422f398cba1021175cc65d08108bce7b2c840845d73d96420422f39ccb21021175ce65908108baeb31c840861e5498e420430eaa4c72102117dd56390810c3ca8b1c840861d5458e420422fbb4a721021175da53908108beeca9c840845d7654e420432731ca5210219358e5290810c9cc6a94840864d6354a420422f39ccaa1021175ce65508108bce632a840845d73195420423cbaec0a10218e5536050810cb2a7b02840866952d81420423cba8c0a10218e5506050810cb2a6302840866952181420422f39cca21021175ce651081087ce932e640843d74997320421f3a0cb990210f5d065cc81087ce9b2c640843d74d96320421f3a4cb190210f5d2658c81087ce832c640843d74196320423b388cb190210f5d6648c81087eeab24640843f76952320421ebb4a9190210fdd9548c81087aecaa4640861e6494e320430eb24a71902187991538c810c3ac8a9c640862e6494a3204316b24a5190218b991528c810c5ac8a94640843e74995320421eba4ca990210f9d0654c81087ae832a640847975d81320431caa6c0990219654f604c810cd2a5b02640847975181320431caa0c0990219654c604c810cd2a4302640843e74994320421eba4ca190210f9d0650c81087ae8328640847671194320422fb9ac928821171cd649441087ee8b1ca20843c7458e510431caa4c1208219654e6090410cd2a5304820847b75582410431caa2c1208219654d6090410cd2a4b04820861e54d8d410430eaa6c6a0821879506350410c3aa831a820845e7694d410422e3b4a6a0821179d953504108b8eca9a820864f63949410432631ca4a082193d8d5250410c98c6a92820845e73d94410422eb9eca208211b9cb65104108dae5b28820847970594410422ebacc620821879526310410c3aa9318820845f7558c410430f2a2c6208218755163104108beed298820845d7694c410422fbb2a620821175d953104108daeb310820862e54988
  | 3 => 0x9260d4c10cd2c5306a60851e74d4e530428eba6a729821539cb5394c10a9ae5a9ca60843e7498a530421eba4c529821539cb5494c10a9ae5aa4a60854e7215253042a6b90a929821875906494c10a3ce9314a60851d7498a530428f3a0c329821475d06194c10a9ce430ca60854d72186530428f3a4c129821475d26094c10a3ce9b1aa60851d74d8d53042a7396c6a9821535cb6354c1087ee8b0aa60843c74585530422f3b6a8a9821539cb5454c10a9ae5aa2a60845e7615153042a7390a8a9821535c85454c10c3ac8322a60851e74989530428eba4c4a9821561c16254c10a3ce830aa60851d7418553042a7390c2a9821535c86154c10a3ce9302a60851d74981530428f3a020a9821475d01054c1087aed2a0a60843f76550530430f2a4c629821875526314c108beeca98a60861e6454c530430eb22a6298218b9526214c10c5aa9310a60864d5398853043172a2c4298218b5516214c10c9aa6b10a60861e6498c530430eb24c6298218b9926214c10c5ac9310a60864e639885304317322c4298218b5916214c10c9cc6b10a608635649845304332b14c2298218e9926014c10c72c9300a60866a629805304334b14c0298211b9ca65d0c108dae532e860846e721974304236b90cba18211e9c065d0c108dce532c860846d729964304237390cb218211b5c86590c108f4e032c860846e729954304236b94caa18211b9c86550c108dae432a860847a70195430428e39aa8a1821471d15350c108dce5328860846d729944304237390ca218211b5c86510c108ece2328860847a70194430428eb9ca821821475d25310c10a3eeaa18860851d7550c430430fb2a8621821875954310c10c3ca931ea40861d5498f520430f2a2c7a90218755163d4810c3cc929ea40861d6494f520430f322a7a90218759153d4810c3cc931ea40861d6498f520430f322c7a90218759163d4810c72c9306a4086596398352042973a6a5290214b5d35294810a9ce7a94a40854d73d4a52042a739ea929021535cf5494810a9ce62a4a40854d7315252042973a6a7290214b5d35394810e1ca929ca40870d5494e52043872a2a729021c35515394810a5ce829ca40852d7414e52042a739ec929021535cf6494810a5ce9b1ca40852d74d8e5204386a1887290214b9d06194810a5ae830ca40854e7318652042a6b98c3290214b9d06094810a5ae8304a40854e7318252042a6b98c129021179cf64548108bae7b22a40843e74d8d520421eba6c6a90214b9d36254810a5ae9b12a40854e73d8952042a6b9ec4a90211b9db5454810a9ce7aa2a40854d73d5152042373b0a8a9021539cc5454810a9ae62a2a40846e76d4d52042973a6a6a90214b5d35354810e1ca929aa40870d5494d52043872a2a6a9021c355153548108dcec29aa40852e7414d5204296ba0
  | 4 => 0xb2e7306828861f5418d414430e2a0c6a0a212e5d260cc510c38c9a9a628861c6414d3144296ba0a590a21535cc52c8510cd0a4b0642885727518221442d8ba0c110a21745cc6088510972e830242884d97318121442d8ba0c090a21745cc6048510da2c710c80886d1634864044370b12432022117dcd65501108b8e6b2a808846f725954044272b90c2a0221669cf64501108f4ec2a2808853a7590d404431c32c86a02218e1944350110b62e221a808853875509404426cb98c2a02213a5c86150110bc2e430a808863865d05404431c32a82a0221661cd4150110d60c2a0a80886e3628854044358b244318221ac591218c110dc2c490c608843f74595304421e3a2ca982211bdc9654c1109cae430a608847875591304427838ac898221669d3634c1108f4ec29a60884da76d0d30442ad3ae869822196197434c110cb0ca21a60886996410d30442e8b888698221561d5324c110972e830a60884e97218530442f0b90c29822196197314c110cb0ca98a6088598744c5304436830a6298221b8d8a214c110f826490a60884b974980304423d3aec910221365cf64881108f4ebb1c40884b974d8e20442b93a8c3102215c1d521881108bee6b2a408845c73595204426cb9ec8902212e5d36348110ad4ebb12408847a7614920442b53b0a4902219a9d85248110e54e829240887297414920443a5398a490221d25cc5248110ec2e229240884b974185204426cb98c290221785ca2148110ec0a510a40885687548520442b83aa4290221581d52148110dc6c690a40886e1634852044370b0a401022136dcd64c4110976e8b1e20886e1628871044371b124388221745ce4084110b62e918420886e1628821044371b1241082219398e62d5010c9ac7316a80864e6358b5404326b1ac5aa0219958a61d5010cb2c7306a80866962983540428f39ea92a021475cf5495010a5ce5aa4a80852d72d52540422f39cc52a021175ce6295010c3ac631ca80851e7398a540428eb9cc52a021479cc6195010a3ae630ca80852e721865404296b90c32a021479ce6095010a3ae7304a80851e73d91540428eb9ec8aa0214b9cb6455010a5ae5b22a80861d6318d540428f39cc4aa021475ce6255010a70e0b12a80851e73185540428eb98c2aa0214b9c86155010a5ae430aa80851e73981540428eb9cc0aa0210fdd95415010c3aa9318a80861d5458c5404316aa4c42a0218b5516215010c3cc9318a80861e6458c5404317324c42a0219398e6215010c9ac7310a80862e64588540432731ac42a0219358d6215010caac7308a80866562984540432d31cc02a0219658e6015010cd4c5300a8086696298054043172a4c5a98218b55262d4c10c5ca8b16a60862d5458b5304317324c5a98218b59262d4c10c5cc8b16a60862d6458b5304332b14c3a98218e5
  | 5 => 0x84ba76151408429d3ac86a04214e1d542502109b2e630a81084e97218540842cc39a82a04210fdd95410210d62c2a00810851e74d4f308430f324a71842187991538c210c72cb3246108639655923084358b22c318421479d3534c2108bcec29a610859a74d8d30842cd3a6a698421745c7534c2108f4ec29a61084da7614d30842ad3ae8698421a6590434c210ab0ea99261084b9741853084274b90c298421661d1314c2108beeca9861086d1614c0308426cb9ec9104212e5d363882109b2e7b2241084b974d8d20842f0b8ea4904211e9d852482109d4ec292410856a7614920843353b0a490421d29cc5248210e92e6292410876171149208425cba0c290421365cc6148210ccca4b084108665525842084370b0a401042136dcd64c4210976e8b1e210845e7398a544422eb9cc52a22187d906355110c9ec7b12a88864c63d895444317b20c4aa22193d8c6255110c98c6312a88866862d81544421fbb2a82a221471cd5415110a58e4aa0a88845e73980544422eb9cc02a2210f9d26294d1087ae9314a68861c64d8d5344317b26c4a9a218b1936254d10c5ec8312a68862c641895344327b18c4a9a219a18b6054d108beeca98a68851c7454c53442a6392a629a210f9d06114d1087ae8308a68843e74980534421eba4c029a211b9cb65d0d108dae5b2e8688478755834344237396cb21a211b5cb6590d108f0eab04868846f725954344236392caa1a211bdc96510d108d8e4b28868846e721944344236b90ca21a21475cc5410d10a3ae8298868851e7550c434428e3aa8621a211d1d56110d10d2a86b08868847875580434431c2a2c021a219614d6010d108bee6b26a48845c73593524421fba2c7a92210f1d163d4910c3ec9b1aa48861f6418d524430e320c6a92218e1936054910cb0c7b02a48846f7654852442963a2a429221531cd5214910c58e4b20a48861e6498c524430eb24c629221879916314910c3ac8b18a48864c7258c524431b322c2292218d5916114910cacc6b08a48865563584524422f398c029221175cc6014910a38e6aa6848852c725534244296ba0a5a1221365ce60d09108bce7b2c848845d73d96424422f398cb21221175cc6590910c3ea931c848861c5498e424421f3b4a8a1221471cd5450910a58e4aa2848845f73594424422e39aca21221179cc65109108bae6328848843d76d504244334292c0212210f9d365cc91087ae9b2e648851c7454f32442a6392a799221535cc52cc910972e9306648843e74d96324421eba6cb192210f9d0658c91087ae832c648861e64d4e324430f320a7192211d1d5618c91087ee8b2a648843c74595324422f3b4a699221471d1534c910a98e4a9a648843f74594324421e3a2ca192210f9d0650c91087ae8328648845d76d4c324423a3aac2192219a149600c9109
  | 6 => 0x3c4335312c029e219a5896014f108dce432e878846d7219743c428e39aa9a1e21475d053d0f10a9ae429e878846e7219643c4236b90cb21e21475cc5490f10a5ae42a4878851c7454e43c4237390caa1e211b5c86550f1087ced2a2878851c7355143c422f3b4a6a1e21471d15350f108dce4328878846d7219443c421ebb6a821e21475cc5410f10a5ae42a0878845d76d4c43c428eba0a621e21535c85310f10a3ceaa18878851c7550c43c430fb2a8621e21875954310f10d2a86b08878843f7458f52c421e3a2c7a96211bdd95214b10c5ac8a90a58864d6354852c428e39aa9a1621179cf6590b108bae7b2c858864d6394a42c4326b1aa52162117dcd6550b108b8e6b2a858845e7319542c422eb98caa1621471cd5450b1087ce832e658843d7419732c428e3a2a7996210f9d3658cb1087ae9b2c658862d6494a32c4316b22a5196210fdd1654cb10878e8b2a658843e7419532c421eba0ca99621471d1534cb10a3ae62a6838852d7215341c428e39aa920e210f9d85450710a3ae62a2838852d7215141c430faa0c6a0e2187150635071087eecaa0838851c7355041c430f2a2c620e21875516310710c5ca8b10838862d5458841c431d2a2c020e218e5516010710a3ae829e638854d7214f31c428e3a2a718e2187193534c7108bcec29a638851d7414d31c430e320a698e21535c8534c710c3ac9298638845f7654c31c428e3a2a618e2187591530c710c9ca6b10638864d5358831c432d29ac018e219654d600c710a38e6aa6818851c7355140c4272b90c2a0621471d153cc310a38e8a9a61884e57218530c4370b0a4010621479cf54952108bce7314a90845d7398a548428f39ec8aa4210fdd95415210a3ce9a9ca70843e7498a538421eba4c529c21479d36354e108beeca98a70846e72d974384236b96cba1c219654e60d0e108dce5b2c870846d72d96438431caa4c121c211b9c86510e108dae4328870851d73950438428eba4a621c2147dd54310e10a3aeaa18870845e73d91528422eb9ec8a94210f9d36354a1087ae9b1aa50846f76548528430f324c629421879916314a10c3ac8b18a50865663584528432ab1ac229421179cf65d0a108bae7b2e850845e73997428422eb9ccba1421365ce60d0a108bce7b2c850845d73d964284296392a8a14210f9d365cca1087ae9b2e650843e74997328421eba4cb994212e5d260cca1087ce9b2c650843d74d96328421f3a0cb194210f5d0658ca10a98e4a9a650843e74194328421eba0ca19421365ce60d0610c3ca831a830861d5418d418425cba4c198c2187192534c610c38c8a9a630851e73d53408430f2a4c720421875526390210cb2cb31c81086596558e4084368b1ac320421479cf545021087cec2a2810859a73d9140842cd39ea8a04216c5c754502108f4ec2a2810
  | 7 => 0x310041d454d5188020c76cb2a2401063b65551200832db2ca69004196d955348020e32a8a9a40105ca7390920082e4b9c84900416a9d23248020b52e91924010673659452008339b2aa290041cc9515148020e62a8a8a40107525354520083a8a9aa290041d89c95148020ec6c4a8a40107634254520083b1212a290041d85095148020ec084a8a40107633254520083b1192a290041d84c95148020ec064a8a401066975d9520083353b6ca900415a5c76548020b54e9b1a40105a974d8d20082b4bacc6900416a9d26348020b52e931a401056b7558d2008364b18c6900413a9db5348020b54e9a9a40105a974d4d20082f138ea690041785c75348020b92eb29a40106cb6594d20083a5b2ca690041e29525348020e96eaa9a40106cb6554d20083a5b2aa690041d2d515348020f14a8a9a40107495454d20083c4aa2a690041c255153480209d4ec29a40105aa7414d20082d4ba0a690041729cc5348020bc4e229a40105e17114d20082753b486900413a5da4348020ad4ea21a40105697510d20083c4a1886900415a5d66148020ad6eab0a40105cb7358520082e439ac290041729cc6148020b92e630a40104ea76d4520082e539ea290041725cf5148020e94a7a8a401074953d4520082f0baca290041b8d965148020ec6cb28a40107c25394520083e0a9ca290041d294d5148020e92a6a8a401056a7654520082b43b2a290041d8d855148020ec0c2a8a4010763755452008371b2aa290041d8d955148020ec6a6a8a40107625354520083e129aa290041d094d5148020ec2a6a8a40107c15354520083a0a9aa290041d814d5148020ec6eca8a40107627654520083b0bb2a290041d81d95148020ec6e6a8a40107627354520083b0b9aa290041d81cd5148020ec6c6a8a40107626354520083b0b1aa290041d818d5148020ec486a8a40107614354520083b021aa2900413a9d85148020b94e628a40105c97314520082f1388a290041d85445148020ec2a398a401056a758c520082b4bac6290041d854631480209d6ec98a40104e8764c520082d5ba262900416a1d13148020ec2a298a40104ea760c52008274bb062900415a9d43148020ad2ea18a40105aa740c520082d4ba06290041d854431480208bce7314a98845d7398a54c430fb20c6aa6210fdd95415310a38e6aa0a98861d5458c54c4316aa2c42a621879916315310c9cc7310a98864d6398854c4317322c42a6219398d6215310c9ac6b10a98865a6358054c432cb1ac02a6219a9896015310cd2c4b00a98843e7498a53c421eba4c529e21875cc6454f10c38c9b1aa78845f7654c53c428e3a2a629e21875915314f10c9aa6b10a78861c7359053c430eb24c629e218b9926214f10c5ac9310a78862e6458853c4316b22c429e219398d6214f10c74c8b00a788639645805
  | 8 => 0x15354420e2aa8a9aa2104767614d510829b3a0a6a88414d5d05354420a6ee8b1aa2105347458d51082b2392c6a88415c1c16354420a6ce831aa2105357418d51082b3390c6a88415c9c06354420acce521aa2105657290d51082b938486a88415c5c24354420e2a8621aa2105567308151082aab9840a8841175da5314420c3cc9298a21061d6494c510822fbb2a628841879915314420c3ac8a98a21065653984510832aa9cc2288411ddd95114420cacc6a88a21065563544510821f3a4cb988410f5d265cc42087ce932c621043d74996310821fba2ca988410f1d1654c42087ce832a621043d74195310821ebaec8988410f5d4644c42087ced2a2621043c76951310821f3b2a8988410f1d9544c420c3ec929a621061c6494d310830fb22a69884187191534c420c9aa7b1262104e970189310831bb24a2988418d192514c420c6ec8a8a6210634645453108333b12a29884199189514c420cb2a7b02621067151d813108274b90c0988419c544604c42087ce9b28621043d74d94310821f3a4ca188410f5d2650c42087aeb320621043f75590310821fbb4a8188410f5da540c42087eecaa0621043d76550310830f324a61884187592530c420c3cc8a98621061d6454c31083172a4c4188418b552620c420c9ca7310621064d539883108274b84c4188418b951620c420c5aa8b10621064e535883108326a9ac4188418d992510c420c6ac9288621066562944310831b322a2188418d591510c420cccc4a88621066562544310831d2a4c0188418e552600c420cb4a73006210659539803108274b94c0188419c546600c420c74a8b00621063954580310832d29ac0188419654d600c420ce4a2b00621067151580310822f39ecb20041175cf65900208baeb31c801061e5498e400830eaa4c72004117dd56390020c3ca8b1c801061d5458e400822fbb4a720041175da53900208beeca9c801045d7654e4008316aa2c5200419598e5190020caac728c801065663546400832ab1aa320041999895190020ccac4a8c801064d5398840083172a2c4200419354d6210020cccc4a88801066562544400831cb2a8020041c654d4010020d52c4a00801073151500400821f3a6cb180410f5d3658c02087aeb324601043f75592300821fbb4a9180410f5da548c02087eecaa4601043d76552300830f324a71804187592538c020c3cc8a9c601061d6454e3008326a9ac5180418d992518c020c6ac928c601063664546300831ab22a31804199989518c020ccac4a8c601043e74994300821eba4ca180410f9d0650c02087ae8328601062d549883008316aa2c4180419394d620c020cccc4a88601066562544300832cb2a6018041c6551300c020d92c49806010751514c0300838caa2a7100411e5da5288020e64a8a8c40107315454620083a929aa
  | 9 => 0xae832c629051e74d4e3148274382c518a413a1c9608c52087ce932a629043d74995314822f3b4a698a41475d2534c520c38c929a629061c6454d314821f3a0ca18a410f5d0650c5208baeda98629051e74d4c314830eb26a618a4187590530c520c9ea6b10629064c535883148274382c418a4196d4d600c520cb0a6b0062904e872580314828f39ea9a02418b15162d0120a3ce7aa2809051e74d4f304832629ac5982410f9d3654c12087ae9b2a609051e74d4d304831b324c3a98418d59261d4c20c6cc8b0ea610635645875308333312c3a98419c58660d4c20a3ce9a9ca61051d74d4e53082ab38ea729841555c75394c2087ee8b0ca61043c7458653082ab38ea929841555c75494c20a9ce5b24a61055a70d92530830eb20c929841479d26294c20a3ae9314a61051f74586530828e3a2c329841479d06194c20a3ae830ca61054e7218653082ad380c329841479d26094c20a3ae9304a61051e74d8d530828eba6c6a9841559c76354c20aaae3b1aa61043e74185530821eba0c2a9841559c75454c20aaae3aa2a61054e7299153082ad384c8a9841875906454c20a3ce9312a61051d74989530828fba2c2a9841471d16154c20a98e4b0aa61055870585530828f3a0c2a9841475d06154c20a9ce430aa61055a70185530828f3a4c0a9841475d26054c20a3ae8102a61043d76950530821fbb2a829841879526314c20c3aa9318a61045f7654c530830f322a629841875915314c20c6ca9308a61063554984530832aa9cc2298418d9516114c20c6aa8b08a61065553584530830f324c629841875926314c20c5ac9310a61063664984530831ab24c2298419598e6114c20c6cc8b08a61063564584530832b31ac229841999896114c20c72c9300a61067161980530823b38ccb218411d5c66590c208ece232c8610475711964308236bacc5218418b5526290c209d2e1314861062d5458a430832729ac5218411e5d66090c20c72a930486104e972982430831caa2c1218419694d6090c208ece332a861047571995430823b388caa18411d5c46550c20a38e8a9a861047671994430823ab8cca218411d9c46510c208eae2328861047a70194430828eba4a62184147dd54310c20a3aeaa18861061f6550c430830eb2a86218418799253d4420c3ac929ea21061e6454f510830eb22a7a8841559cf5194420aaae7a8ca21043f7458e510821e3a2c7288414d9d35394420a6ae9a9ca2107165494e510838b2a2a728841c55515394420a6ce829ca2105357414e510829bba2c7288414d1d16394420a6ce831ca2105357418e51082b3390c7288415c9c06394420e2a8621ca21053674182510829aba0c128841559cc6094420aaae6304a21043e7418d510821eba0c6a88411d9db5354420a6ce9a9aa21053574d4d510838b2a4a6a8841c595
  | 10 => 0x66962980540c338b0cc02a0618e5526090c30a3ae6aa0861851d7494c430c28fbaa86218610f9d0615483087ae830aa41846f76548520c316b22a4290619954961148308beeab1e84184d97098e420c32731aa5210611d9c465508308eae232a841846e72191510c236b90c8a88610f9d0625443087ae8312a21847776544510c31ab22a2288619958951144308dce432a821846d72195410c30f2a0c6a08618755063504309b2e031a821865463945410c237396ca208611b5cb6510430c38c929a621863564944310c332b14a2188618d591510c430ccac4a88621867151980310c28f39ea9a00614b5c854d0030a6ae22a6801861e5498e400c30eaa4c720061479cf5450030a74e1aa2801843e76151400c296b90a8a00614d5c4545003087eecaa0801845f7558c400c2a6b90a998061555c454cc0308baed29c601861e6494e300c23cbb4a718061179d8544c030a9ae42a2601855571151300c28f3a4a098061565d6404c030e30a8a02601859974d8d300c2adbaa8698061565d6324c030b32e9192601875151cc5300c2cdba262980619658e60d5220cd2c5306a91051e73d52548828f39ec8aa441179cc61552208bae630aa91043f765505488334b14c02a4418e59260d4e20cd2c5306a71051e74d4e538828f3a6c6a9c410f9d06154e2087ae830aa71045f7654c5388334b14c029c411d9c46510e208eae2328871051d73950438828eba4a621c4147dd54310e20a3aeaa18871063954181428832ca98c09944117dcd64946208b8e6b24a31043f7458e518821e3a2c728c411ddd951146208bce732e831045d73997418822fb9acaa0c41171cd6550620c3ca831a831061d5418d418822f39eca20c41175cf651062087ce932e631043d74997318821fba2ca98c410f1d1654c620c38c929a631061c6454d318821f3a6ca18c410f5d3650c620a3ce7aa6811061e5498e408830eaa4c720441479cf545022087cec2a2811043f76550408828f3a6a79844187992538c220c3cc8a9c611051e74d4d308822f3b0a69844117dd9530c220a3ce9a9ca69061d64d4e534830e39ac929a418b9916294d20c74c8b04a69051e74d8d534821f3a0c2a9a410f5d06154d208beeca98a69051d7498c534821fba2c229a410f1d16114d208dae5b2c869047970d96434828eb9ca921a41479d35390d208bae732a869047771595434823a38acaa1a41479d35350d208bcec29a869047671194434823ab88ca21a41175da5310d20a3ae9298869045f7654c434828fbaa8621a41475d54310d20c3ccaa18869061c6550c434823c3aac021a413a1c96010d2087ce931ea29043d7498f514823bbb2a228a41879926314520c3cc8b18a29061d6458c514821f3a4cb98a410f5d265cc520a3ae929e629043f74596314821e3a2cb18a410f9d0658c52087
  | 11 => 0x8c31d2a2c020c618e5516010630c72a9304631863954582318c21ebaec898c610f5d4644c63087ced2a2631843c76551318c21ebb4a818c610fdd9540c630c5ca9310631862d54988318c3172a2c418c618b551620c630c74a8b00631863954580318c30f2a4c720461875526390230c3ca8b1c811861e5498c408c30f2a2c6204618759654cc230c3acaaa6611863965953308c31cb2aa9984618bd516295130c9ac7314a89864d7398a544c335312c12a2611b9c861551308dae430aa89843f76550544c296b94c82a261369d660d0d30cb4eb30686984d971983434c296b94a921a610f9d85450d30a3ae72a0869852d72950434c21fbb2a821a61635ca5410d30b32e12a0869845f76550434c24fbb2a821a6166dc15410d30a3eecaa0869861f76550434c28fb92a821a61471c55410d30a3ee0aa0869871b70550434c26c382c421a61875516110d30c3ac821ea49862d64d4a524c237bb2a4292618759443d09309b0e0b1c849864d63d4a424c326b18a521261a610f60509309b4e1326649845e75193324c22ebb4a999261539ca54cc93093ce9306649862d64d4a324c316b20a519261369c2644c930a9ce52a2649854e75d89324c2a73b0a499261939d8524c930a9ae229264984da75181324c32d3a8c099261365c4604c9308dce5326a29846d72993514c21f3a4c5a8a610f5d262d45308eeeca88a29861f73590514c30e39ac828a61175db4314530c3ac9a18a29861d6410c514c317324c428a618b5926214530c5cc8b10a29862d64588514c327a1ac428a619310d6214530c74c8b00a29863964580514c335312c028a619a5896014530a5ae52a6829846f72596414c236392cb20a611b9c865905308dae432c829869843582414c21f3b4a8a0a614b5ca54505309b4e1b1a829861e5418d414c30eaa0c6a0a61279db4350530c38cba1a829846e72194414c236b90ca20a610f5db5410530c3ea8b18829861c5458c414c30eb288620a618bd516210530c58a8b10829868c43588414c31daa2c020a618e1516010530d3086b00829843e74997314c21eba4cb98a61279d265cc530a3ae932e62984da70993314c22ebb6a998a6117dd954cc530c38c8aa662984d87058b314c28eba0a398a61535c851cc53093ce9306629855a75183314c24f3a4c898a61369c2644c530c3cea322629861d75191314c22f3b6a898a6187193544c530c38c8aa2629861c64d49314c28eba0a298a6187190514c530a9ae428a629869864d81314c34db20c098a618715163d0130c3aca21a80986d161cc7304c2cc3a26398261a6993508c1308dce430aa81846d72185540c21fbb2a82a0618b5516215030c6aa8b08a81862e64588540c32731ac42a0619998a6115030ccac5308a81863664584540c32b31ac22a061999896115030ccac4b08a818
  | 12 => 0x990811d5c4654c8408dce431aa22046d7218d511022f398c4a8881175cc62544408eeeca88a220655635445110332b12a228881879506350440caac7288822066562944411032ab1aa220881995895110440ce2a3300822046e721953110236b90ca988812e5c0644c440c38c929a622061c6454d311031a324a2988811b9cb650c4408dae5b28622043d76952401023cbb4a920081665cf6450040a76eaa1a802073151d0540102cdb9a82a00819398d62d5330cd4c4b06a99852e72d5254cc297396c8aa6611b9c861553308dae430aa99843f7655054cc32d31ac02a661535cb54d0f30c74a8b00879854d72d5043cc22fbb2a821e6147dd95410f30c3eecaa0879851f7255043cc28e38aa821e61875516110f30a5ce9a94a59862c7259252cc21f3a0c2a96610f5d06154b308deeca90a59861d6510f42cc26cb9cc1a1661a610d60d0b30a3ce9296659849e7498332cc26d384c899661539ca544cb308bcec2a2659851e7494932cc22ebb08728e611ddd951147308dce532e839846d7299741cc30fb288720e61879506350730c3aa831a839849e76d0d41cc237396ca20e611b5cb6510730c3aca218839868c4358841cc34c21ac020e61535cb54cc7308beecaa6639861c6455331cc24f3a4c198e6187d94644c730c3aea322639869a7019131cc34cb80c898e61179db544c730c38c9aa2639854d72d5131cc22e3b2a898e6187191544c730c38c8a92639861c6494531cc338a8ac018e61875506350330a5ce5b1ca91852d72d8e548c28eb9ec52a461475ce6295230c5ac4314a91853a7018a548c28fb9ac32a461475cc6195230a5ce430ca91852d72186548c29d380c32a4614b9c86095230a5ae4304a91853671182548c29ab88c12a4611b9c861552308dae430aa91851d73989548c29c382c4aa4618b5886255230a74e130aa91851f73585548c28eb98c2aa4614b9c86155230a5ae430aa91853a70185548c21fbb2a82a4619658e6015230c74a8b06871863954d81438c21f3a0c2a94610f5d06154a3087aed2a0a51843f76550528c237bb2a4294618d9526114a30c6aa9308a51863654584528c31aaa2c229461995496114a30c3ca931e851861e5458f428c30f2a4c721461879516390a30c3aa8b1c851843d75992328c21fbaac9194610f5da548ca3087eecaa4651863954d81328c31caa0c099461c3551320ca3087ce8312a31843d74189518c21ebb4a828c610fdd95414630c5ca9310a31862d54988518c3172a2c428c618b55162146308eeeca88a31866562544518c31caa4c120c618e5516090630c3ca9b1a831861e5418d418c30eaa0c6a0c611b9cb65106308dae5b28831861e5498c418c30eaa4c620c61879516310630c3aa8b18831862e54988418c316aa4c420c618b9516210630c5aa8b1083186395498041
  | 13 => 0x6154e40a3ae9312a720558705895390326b10c4a9c81569c26154e40a3ee8b0aa72051d7418553902a7390c2a9c81535c86154e40ab4e030aa72045f7654c539032d29ac121c819654f6050e408bce630aa52045d73185529022ebb4a62948117dd95314a408deeca90a52065653984529032aa9cc2294819594d6114a40caaa6b08a52066552584529030f324a7994818759253cca40c3cc929c652061e6454e329030eb22a719481179cc62546408bae6312a32045d7694c519022fbb2a628c819394e6214640c9aa7310a32064e535885190326a9ac428c811ddd95114640ccac4a88a32065953982419032ca9ac120c81175d763506408baea31a832045e7694d419022e3b2a6a0c819394e6210640c9aa7310832064e535884190326a9ac420c819694d6010640cb2a6b00832065953982319032ca9ac118c8187d92534c640c38c929a632061c6454d3190237396ca18c811b5cb650c640c3cc9298632061d6494c319030f322a618c8187591530c640c9ca7310632064d53988319032729ac418c819354d620c640cb2a7300632065a53580319032ca9ac018c818759653d0240c3acaa9e81206596594f409032cb2aa7a048193d4d6294d408beeca98a6a04ba75982435031d3acc121a812e5c66090d40b1ae529886a05997094c435024fbb2a621a8166dc15310d40970e0b1086a061d6310f5250326b1ea5292811bdd95214940c3aca21e64a04b8705923250316b26a5192818b590528c940d3087b0264a046e7298f5150236b94c7a8a81179ce62d45408bae7316a2a047776544515030fba2c628a81871d1631454087aed218a2a061d6390c515030eb188628a819398e6214540c9ac7310a2a064e635885150326b1ac428a818b90d6214540c5886b10a2a065a63580515032cb1ac028a819a9896014540cd2c4b00a2a045e73997415022eb9ccba0a81279ce65d0540a3ae732e82a04ba7098f415025c382c5a0a81475cc51d0540a5ae428e82a049e73983415029d3a8c1a0a81879d46350540c3aea31a82a043e76d4d415030e31ea6a0a818718f5250540a3ae628a82a061c631454150296b90a2a0a81a618f6050540d36c630282a04ba70d933150237b92cb18a811b1c9658c5408dce432c62a046d72196315034c21ac118a812e9c3644c54093ced21a62a061c6590d3150237390ca18a811b5c8650c540c3ac9a9862a061d6414c315024ebb08618a8187594430c540c9ea6b1062a064c53588315034621ac418a8196d4d600c540cb0a6b0062a0698435803150358b0e83a0281661cd41d0140d34c7a8480a046e721855310236b90c2a988117dd95314c40c9aa6b10a62065553584531028fbaa8621881179cc61548408bae630aa42046f765485210326b1aa429081995496114840972e1324642062e6454a321023b388ca
  | 14 => 0xe8312a018c3d74189500c68e3a262a80631e9db5454031ad4e5aa2a018d6972d51500c78c39ca8a8063c61cd54540318f4ec2a2a018d6a72151500c6b4b90a8a8063565d74354031e34a9a1aa018f1954d0d500c78d2a086a8063c655043540318f4eda92a018d3a74d49500c69cba6a4a8063ca9525254031e52a9292a018f4b43949500c7a421ca4a8063ca9515254031e52a8a92a018f4b43549500c7a421aa4a80631e9d85254031a74e8292a018d3974149500c78d2a662a8063c65533154031e94a598aa018f4952cc5500c798aa462a8063d854a3154031ab6ea98aa018d98744c5500c78d2a262a8063c65513154031e94a498aa018f49524c5500c6b9baa62a8063cc5513154031ec2a498aa018d5a73d91500c6ac39ac8a8063565c74354031e328621aa018d727110d500c6b8b8886a8063c69d04354031e34c821aa018f196410d500c7a938886a8063565c44354031ea2e221aa018d5873589500c69d3a0c4a80634e5d06254031ab4e6312a018e6962189500c6b9388c4a8063c6d0f4154031ab4e720aa018d5973905500c78c21c82a806356dcd4154031ab0e6a0aa018f1b43505500c63d3b082a8063569cc4154031ab2e620aa018f1843105500c6b539082a80635a5c84154031ab4e998aa018d5874cc5500c69dba262a80634e1d13154031e36e898aa018d5a744c5500c6ac3a262a8063c61d13154031a30e898aa018f53714c5500c69d3a062a80634e5d03154031ad4e418aa018d69720c5500c61ebb4a8280630fdd95414031c5ca9310a018e2d54988500c7172a2c4280638b55162140318daed290a018e2e64948500c716b24a4280631bdd95214031c5cc8a90a018e2d64548500c71d2a4c0280638e5526014031cd4a5300a018e6952980500c63dbb2a0280638e9915014031c72c8a80a018e6a62540500c734b12a028063539cb5394f408dce430aa7a046d7218553d022fbb2a629e8147dd95310f40c3eeca9887a051f7254c43d028e38aa621e818754d6110f40a9ce7a94a5a045e7318552d022eb98c2a96811bdd95214b40c3aca21e65a04b97498332d034c21ac1996810f5d843947408eeeca88a3a043f7654f41d024f39cc1a0e8187d946350740c3aea31a83a069a7018d41d034cb80c6a0e818718d5350740c38c6a9283a061c6394541d0338a8ac020e811b9ca65cc7408dae532e63a061c6454f31d030fb288718e8187192534c740c38c8a9a63a049e7690d31d0237396ca18e811b5cb650c740c3aca21863a068c4358831d034c21ac018e81539cb6494e40a9ae5b24a72051d74d8a539028eba4c529c81935886294e40ab4e0314a72051f74586539028eba0c329c81539c86194e40a9ae430ca72055a7018653902a7390c129c81535c86094e40aace2304a720555711825390237390c2a9c811b5c8
  | 15 => 0x3a54580520c71caa2c0290639a54960148318baec21ca218d1d75d0f410c70eb2e87a0863c3d0d52d0431c3aa931c8218c5f7558e410c70eaa2c72086387d944390431c9cc6a948218e4d6354a410c78621aa520863879536350431c3aa9b1a8218e1e5418d410c70eaa0c6a0863279db4350431a3aeba1a8218e1f65d0d410c727b1ca4a08639318e5250431c9ec6a928218e4c63549410c787a1aa4a0863879516310431c3aa8b188218e1d6510c410c6cab8886208631e5d66010431c74a93008218e3954980410c735294c0208631edd56010431c74a8b008218e3954580410c74c21ac0208639a9496010431cd2a4b008218d4d72d53310c6acb86a99886317dd954cc431c3cc8aa66218e1f76553310c70e3b2a998863c355252cc431e1ca8a966218f0d5454b310c727322a5988639319152cc4318baed29c6218c757694e310c792aa2a5188630f9da544c431878ed2a26218c3e76551310c717b24a4988638b192524c431c5ec8a926218e2c64549310c70fba6ca98863871d3654c431c3ecbb226218c5d75991310c64f3a4c89886387d94644c431c3aea3226218c5e76d51310c70e326a898863535cb544c431ab2e1aa26218c9c76951310c68ebaca89886387d96544c4318b8ecaa26218e1c64551310c64e3b2a89886387d95544c431c3eecaa26218d1e76551310c68e3b2a898863871d9544c431838ecaa26218e4f65949310c746324a498863c3552524c431c38c8a926218e4f65549310c746322a498863c3951524c431e1aa8a926218f0f64549310c727322a49886393191524c431e18c8a926218e0c64549310c70eaa6c29886387192514c431c6ee9b2a6218e3474d95310c71bb2ec8988638dd94644c431c6ecb2a26218e3765551310c74a326c698863c5552534c431ccecb2926218e6765549310c792aa2a498863d194d524c431c5ca9316a018e2d5498b500c7172a2c5a80638b55162d4031c5cc9296a018e2d6494b500c717322a5a80638b59152d4031a74e9a84a018d3974d42500c6b5396a1280635a5cb5094031ad4e5aa4a018d6972d52500c78c39aa9280635a9c85494031ad2e42a4a018d5975d0e500c78caa68728063c65504394031a74e9a94a018d3974d4a500c7952a4a528063ca5525294031e54a8a94a018f295454a500c7a5a1aa528063d210d5294031a74e8294a018d397414a500c78caa66328063d254b3194031ab6ea98ca018d98744c6500c78caa26328063d25493194031ae6ea98ca018d5a73d92500c78ca1887280634e9d06294031a72e8314a018d5a7318a500c734b10c5280635c9c46294031a74e830ca018d3974186500c6b5390c3280635a5c86194031ab6e6a0ca018d5873506500c63cbb08328063569cc4194031ab2e620ca018d6a72106500c69dba263280634e1d1319403187c
  | 16 => 0xc71daa6c0a92638e1536054931c76a8302a498e3854181524c637bb2a4292635a1c15214931c38a931e8298e1c5458f414c68f3ac8720a6387d506350531c38a831a8298e1c6550d414c6ca38a86a0a6387590548c531c3aec2a46298e1c5458a314c70e2a2c118a630f9d262d413187ae9316a098c3e76d51504c61f3b0a8a82638bd536254131c58a9b12a098e2f54189504c7162a0c4a82631edd95014131ad0e4a80a098e4e6358b540c735314c1aa0639a58a60d5031cb4c6b06a818e6a62583540c734b12c1aa0634b9cb5495031a5ae5aa4a818d3a70d52540c69cb86a92a063479ce6295031a5ce430ca818d2d72186540c69d380c32a0634e5c06195031a3ce7304a818d2e72d91540c696b96c8aa0634e9c36455031a72e1b22a818e1c63d89540c68f39cc4aa063471cd6255031c38c730aa818e1c63185540c697390c2aa0634b5c86155031a74e030aa818d3970185540c70e31ec0aa063479ce6055031a38e6b02a818c3f76550540c716aa4c42a0638b5516215031c72a9300a818e3954580540c71d324c02a0639698e6015031cd4c5300a818e3a64580540c72d31ac02a0639a9896015031cd2c4b00a818e7261580540c70f3a2cba1863535cb54d0c31ab2e1aa68618e1d65953430c70eaa2c3a18638d5516190c31c3ecaa188618e1d6550c430c71b2a2c221863475d66410c31c3acb3208618d4d72d50430c6acb86a821863475d65410c318beecaa08618e1e64550430c68fbb2a82186387dd95410c31a3ee4aa08618d1f70550430c62fbaac221863875516110c31d2cc8b088618e3a54983520c71caa4c1a90638e95160d4831c72a8b06a418d2e74d4a520c696ba6a5290635a9c35294831ad2e1a94a418d6a70d52520c6b4b86a929063c31cd5494831ad4e02a4a418d6970152520c6a6bae8729063c35534394831e1aa821ca418d4e73d92520c786a1887290634b9d06194831a5ae830ca418d6a70186520c6b4b80c3290634b9d06094831a5ae8304a418d4e73182520c6b3388c1290639a580609483187ce8302a418c3d74181520c6373b6a8a90635a9c35454831ad2e1aa2a418f0c73951520c78639aa8a90631b9d85454831ad4e02a2a418d6970151520c6a6bae86a9063c39534354831e1aa9a1aa418f0e5410d520c786aa086a9063539cf6454831a98e6b22a418d4d71d0d520c786a1886a9063599c44354831acae221aa418f0e7410d520c78732086a9063c35904354831e8ce221aa418d4d7110d520c7a2b8886a90634b9d03154831a5ae818aa418d4c73581520c6973a0c0a90634b5d06054831a9ce6302a418d6671181520c734b00c0a90630f5da541483187eecaa0a418e2e54988520c716aa4c4290631bdd95214831c5cc8a90a418e2d64548520c71d2a4c0290638e5526014831cd2a5300a418e
  | 17 => 0x1002007c004001ad4e1a94a521c7a701855290e3cb80c2a94871bdd95214a43a6ce3a1aa321c77765445190eb5396a1284871b9c861542438dae430aa121c7b765405090e3bbb2a228a874d5c64314543cd4c5300a2a1e6a625805150f34b12c028a8796d0d6014543c7486b00a2a1c7b765405050e2ebb4a921887335c86150c439b2e030a8621e1d75d954310e4f38ecaa1887275c36550c43c3cedb2a8621d1d71d954310e8ebacc2a188747dd56150c43b34e030a8621d99701854310f0eba8c2a1887a69c06150c4393ae030a8621e99701854310e4cb80c2a1887275cb6050c4393ce3b028621d1d759814310e8fbaac0a188727dd943d4443938eca1ca221d947150e5110e4e3b286a8887651c54354443aace321aa221d547150d5110f0fbb286a8887471d94354443c38eca1aa221f177150d5110e8e38a86a8887c51c54354443a28e2a1aa221d1f7050d5110e37390c0a88871b5c8605444393eeca18a221c77765445110f4ca1cc028887a650d6014443ce2a2b00a221c9f7650f5010e4fbb2872808766dc1439404393eeca1aa021d9b7050d5010e3b388c4a80871d5c462540438dce430aa021c6d721855010e4fbb28628087a350e6214043d1a86b10a021e95439845010f4aa1ac2280871edd95014043e3286a80a021e69625405010f38b0aa0280870fdd95415331b2ae3aa28798c5e7615143cc64f3b0a8a1e63479d85450f31c3cec2a28798f157115143cc70e2a0c2a1e63335c86150f319b2e030a8798e1c54d8143cc74aa1ac221e631bdd95214b318f6eca80a198c3f76550548c716aa2c42a4638e55160152318baedaa08718c9d76d50438c6cb38ea821c63475db5410e31c3aedaa08718f1671d50438c68eb86a821c63635c85410e31b2ce22a08718d9970150438c70faa2c221c6387d904354a3187ce8302a518c3d74181528c637bb2a4294638b5915214a31cd2a4b00a518c9c74597318c68fba2cb98c638719354cc631c3cc8aa66318e1f6410d508c61f3a0c4a84630f5d062542318f6eca80a118e3964540508c734b12a0284638bd8a62d5131a3ae6316a898e3b60983544c68eb98c1aa2630fdd95415131a5ce5b18a898d2d72d8c544c69d386c62a2634e5c36315131a3ae7b10a898d1d73988544c68eb98c42a2638b5886215131a6ae2310a898d3a70188544c69cb80c42a263475cf6015131a3ae7300a898d1d73180544c697390c02a2634b5c86015131a6ae2300a898e3960180544c71a2a4c3a1a6387dd26590d31c3ccbaa48698e1c5458a434c70e2a4c321a63871516090d31c6ea830a8698d1e75d91434c62f3b0a8a1a63479d85450d31c3cec2a28698e1c54d89434c666b90c2a1a63365c06150d31d2ec830a8698e1c54d81434c61f3a4c1a92630f5d260d493187cedaa2a498c3e76151524
  | 18 => 0x360080098000046005000001c004004000002000200000180280080060000010000000000801c00600900a000000400200100480000000008034002005004804401600400180140360000058000004030000003c010006000001400a00b0028058000008003804c00200100880000100020060098006008000001002e01300080640040000010000000001000002c00a0000020000012000002000801801c000002000000800180280000000030000020000006000400e004000800000e00b001800800c00e000001c00400a01900000080090080000002007000001c0000020090004000000003004400a000000002c00000500a801001400100080000000020000058000000010803c018004003803001c004002000003e0000030000000002004000c00400200200000360040008000002001001800c0180010000014002001001006c000000003800c0020000000010000003001001800202d004000000400000300000160040000000000001003804000000300b80000000080008008018001010006400e01b000800801c00700000000300060048004016000000000800000201980000000000010000004001005002c03e000009800800000b006002c000003000001000e000000000c000002001000001200d00280080060050040000002012001800c0000010000014000000000001001400500080080020000050034000000001000000a000000000800c0140000000006005000800400000100180480080010000020006002000001c000000003000401801b00200040260130008000006003002803c00a0010008058002000000005400e009003805c0040010000030000009003000402e021001800000001200100080040000028018014002001800402e00b00a8000006001000812c0060070020000000004002006c008000000004800600100e00080040030048000004003000004000c000000800000000b00100000000170018004000002001000c0200000000024000003001001400c00c005005400000500500280000030020000000003002800801a001000800800000000980100040150048030002003003000400200d0040000002000004000000600000080040020070050014004002003000400400000c001c00000b00100000000070060030004001001000c000007000000800e0030028000004000000800400000b001800800400d000000c00000100180080000010080000000002002002c066000012800c002005000000800000b007001c004001005004c00001d0000018000002001000c002010000000000600c0028008004000000001c00a000003000c00003d000800000c000004000c01e004003000000600000100000000020030004000001003804c0000030048000050000001001c0020000020000006
  | 19 => 0x64a22d28740006727481a81660acb05fca38524000955000000031809f0000d0800044bcd80f54949a4c8000bac0d478f00025ac7c05c3000023a0008973a981b018456e0430ca6a329305008e091280005bea900000a3600021040004dab6a80001520001fa044884e523000084086a68818fa2a81c800049515a442c00008c00000009fb40e8ddcc1e15b8ad5ba51f257920e1edcfa46a91640e2a00500100080040070008004002002002000404c02600000bc00c000000002003800a001000000000b003800000401e000809400e000004800c00c000002800800001f000801800c000004000000c001009000400000600b8010012000000801000000000300000080370050008014001004800000c000000800004800400080040020020000000000004000003402c001001001c0080000028000008000000802800000b000000800200500100200080000028010022002008801000000a0018000000004004800400000000380000000000030008000001001003000200500000300060010000000056000007001000400f006805c00a00500100100060000010088008000001000800002c00301980020000010008008000000800000200100000040000000000000014001003801800000c003002c03401b0000004004002001006800800000180200020170020004004001014000000001c003006400800000000080000000080008006007007002400600a000000000000100a806000201200380340000000008010004002001801800001d000008c0160000018008006002001800c016002009002400800000000280000000000020018006002001001e009009801800800a0020020012025000800c00800000200080340030000004002000000000c0000260020030002001001001c00400401f0000000008000801c00200600000280000060070000000003000801c000007001005800000100080000060150048010000000009000001c00c0018010000005004009c01a00c007800801a00000000d4000002007000401c001002003c00c007000000400400000a801000000e003808802c00e0000030010004000000c008002000000001800b00800a000e0010000000010000001005000c012000800001a01300d8000006006002003c008000008000002400000080080000010008004024009002800c0040130018000006005003001c014005000002800200600280a402400800000440000010000010000006002000c010007005802000002700f800804a003001000c00000000f000c006032005019401600200000140be001008800400e016000801c0120010020024004000000004c00a000006800001801500480700000020010060000001001800000201e0000004038000010000400000100d00140000050018000000002001
  | 20 => 0x32911e5ccfe000592800137827d0001dac90a00029f8df400000034997e4f7c7c432592e00000000000000598b4e5369fd02ca8670cb8e76320462028a440492000163c7c887a82533668d4b727bb15e856c74e6514819a98d1c0de3eca674f368562879fb8e7246531a9296af465900b16c9632000139000024a0003ab1da800073000000000000000000000000079000037000000000018bc000000000097c8190004fe1ab0a02000000000029600000002cc9d4af719d81f15f70143f098029f06fe4a4dd78888173b1518f4c125d82dc0bc14000ac3678dc4b1a5e220b800056a324047e44d65084d00000005a0ac4a85242b2a27454938fbc0001fa0002ce07481c8af040016f28593e68a287fe98f596a982d7e0d214798897384934bdac1cc884714798444ed8556075120c61816b288a9593041a543e1e7ca910fb42102d868751f8e2090136a21d0001274000000000000000009e95f0000df061b00000000000000bb23b05ee2462674000000000292400066e000000005d3500000bc85341221a0000171e9a4bac0ac6d9548201549011190dea4ec1d41e0c140000000000c2c0001c89f040000001dd20da38f3660c6a6905cb2f9c8d27641c29c648f289400637b246a5283faacc3700279552167424136d706ba3a02a9209b1a1a2ca1fed51261c0208f985940bb9f819b11589311361820fc7a5891f2e789e05e65b92c963ca73c4bc9694a2e0c9445ab9d1ba9532172c007658453e3a4600000004f69f2800063027a00c800043600007fc7840001792634e2200000000016042dd94d87603a2b11131244878c3935db00010540005aaa9ac00071c41a800035610c00000001889890001fc8b3a000000000000036b45d95040008fa21600b8000000000202800086f8000aa159582300000000002e6000000068000029b9daa0c488c0fa9d00000b9d9b1abecbd646024b800030000b5990f70a3851532601080000a12fc2c0cb8b00000000000000000001c4e29300000000000000001210c290c67a3800210c3b8000295a8e800000043fe38d2b80000e38ea000074a40c148f24a04f0780b600008803f3843812e54f33e80000002590bb9990000ac6029878478e0bd1221a18ec8559284268d10e3184dea1c12ee0920c1a02c6d2a53a5805a896e65c8181dc44061e90002edd09e9f00342d6c0000002d982e850c000307000000000057f54f000000003d9f6e5820000000000f7a874d908000a5933528045d40007158bf59e153e181194ad3c000000000187afaa0850002d644623ce00002710c48823602c486b496a43428257300d6800179c0005800000000ee6000403c0007f200016780640000001d4800125600000000007c200000012f0c5800020f1308000a9c0eb80007a22ee1e2442cb203835042168ed71e88001bb
  | 21 => 0x9400000027f883c00043100008f0a1c69901f9724000ac92722b207c41f756cd3c44c06b43412bc438b6f4000175800085553a800163cb0c06c5aee8a62e700018463d97e50d42c2d3b86c121092f897767a4f11c8c9817aa100a2841b600000018d76921ee1002da144f18a0fa133000000000001bc5c82e7a8c00e800037600000005648e60002e7e00055e00005c099c0001d600000007a5396108162a000000000099900039286d53ac94e882000051a82005329bccf83d93cc8aa4cbc0002e128540008ae463aaad06e76980017487461ed3e28c3c25e22700006c89bc16e466c00014aaae0000d4d4e080f41424e53dea3d54a8000fc0ad4aa3c0000000001985f583c400010e01fc0009194fb90ed5e00001b623440872a13ed07240003708002a5c00062816fa7800ec7e22c3a79c01c31e902800000077c15d82b400038b5bf122cf301160002ce854a2453bb0eff6ac0004cc9cac9d317109d89e82f40be1060c8864e54a0002da8000000000000001274c316abb56300004a0c810ad6b8a8b9a8993eaba234604906de7883408ef030e00007901785aa4a83820000000000109800000000055f8000dd40001ce9abf0981cc4ef2594f110000002b1c00013f18324dc1cfb71312abe46a182c0f203b8cc274b17c9d845f611c35080188e800000029282d30000f50a580000f511512653fe000329012065d44900000015a50002f78001672b5da2440000000004d68000d547660001d680521be0000428fa60000000d5e27a9e55460be8000b63449103000000049408ae9128950fb22a0014a324bc00004aa99c0002428cfd0000aacd3466b08c23d09d0e1e66d35700000ae13107990460007ce00003540000000d680015cb000474956c0007844559bb42f07cc17e4eb6d8623f00023f035eb4c00003bc3b28d834480008945654010000b875105452a0410e8d38ac8c454387d70a20e82e6c00000000008ae966183ab5910c000000214d6e804e2e00bea91c00036688e09877934dc2024f965f40718000c0612853313a27a00b20c127b0efc00000000011e224c1e28000f371850a313ac6ba000000000085200000005a40507f30991328fc500003f21c4796000baeac051225895d6aba0d3480d3892db56560004a682749fc00000006b8a96410118000033a00000014f600070e5dd800000000059b800095800056b80000005dd1a40cc400037c4a344d0000b5fb9700014aa00029a0ac0055b862f22c8cbbc3a61cf5db52020001a712fcc167b94361484a0e5218000b50c68ae100d000089b00000008b17204a38000ba837809fab746b03ce05a8d2cf06394334d96c0000000002a815d507413d8000ce894a6910a40000bf98e121c055561a338800000166688a48386560dc99f218e1fceb8000000000015eac3b581b6c4d0b9
  | 22 => 0xe8000143ea261640000000d768ed3fe800000000000016310910003f52b10ae25201d68560000a10164514600041418e535000076e00000005fe46d0000f94072b84ad517a103498195b14c65c595227a61194bc5f30f801109a337fab6963c000000327abe0f578db3158a140b68de4b99c208bca8d27b0e295e80c518b61e51e44d2db01c8170456181b142a638b46312228c45eac5025686149c4d119784d83246fb0001bc01167c22ba03280008bc49a00006315a31c4247c01a1230001e7521c00030100013d62773e413d4a08ba55bfa9410ba0010dd2d66a1b3c00000d44000337a2a8e10b7a00000000016a898653a22ba4726c648b920534cae90001c9c0000000000000b820000001b380004b1000041d7480000000688000000000000000093a0b094bd1ea8b2442276c33294055dde24548991584ae808b465f039c5db504781000106c0008782680824000bb10002a4000093502a15ec3a600034e2b0058c086d4c1ad420605d18f18dc000000000029c9eb00000019395f8000279847c93c00000025080000005152c46000b2a542a27036e3055b117c4a3c01f001033137481e3e82e9c00000000bc0012da2aa1ae2b5a0005520002e84000b66ce68da138ead0000191c0000001649d6092a9755668e2e000a4fcd126bcaf10000e10000cff5f7084a7154986c92d31d446b29bf4e717d60009334b800000009f10000d3c8d048600013420000001ab966c0f9303a991b5873532a34fe498f447354e4a99d5e405648a97101b98df153caf106c3e8acd25a010246a4e228a40006504e40cdb2ce342920a0b95541c6966841b3a4648b39265c9668a3dac259000081200019a52580919cf253081c9e6063246c1b700039911308de00049e05160000000cd2cec000000000000000000000028ac0000003ed94d4fc600029d400000083d55380851eeb85bff873d3be00000014310060003c8ae580008ce1d814c4cca2ec3c68000000b8000f01f4e2c24f3ca91ed16863680008642e43cf3f88a7c0246d94d6000064200029340000002660000fa82cf00007625740000000002e316d6b138be2ebc76a8d253f00000000000000000eea09b97340000008b100015a8bfb000000013e000b1b04c0a8c0004b480021160005ab3cd67a000066020200013a2834392135ce5a000000000058a2734741ee66a47d4a0f976849c43c00011dd57904ec912814000ae62a4d9d80000003ec140000098c0002dba8ce5640d383649046d0385000000000005c0f0ebdc0000a0800000019f00000008ea220044e5360009b756d0c040006902c885510ec00056f9da29ce63f0729a9b2c6000025899d4d44025c6a30ca4c39b1a61885356a7f0001d7b49e8933d80fb51846480322190d2cae4051962140800034acb784525660000124b1c17d0001d
  | 23 => 0x8ecabb49c2a29780000acb2b600016e600026ca1280005050cc2ef571670700016b4972a07239800000038e240000139e00011700012385773fbae9918c9884ec0958e1fab12fd2e440000bb57780000009f900001d200017e1b69358a284ad3a71dd03c00000e0985305e3c9000000175200000000000000000000bcc00013300003001d638939c23244a46baa5215248169fd30f222149b4d80d518cccc69f44f1a29942c5a81b106e467e65c26000000000000000000000b4329d9b9c53261d5dc03a4d0058b2e69ff876c0005b600000d25540b6e0a40007eb442a84272c6204858000adb0002e60000f000825b44ea800000000013be0000003f31e680006eb2288000c82980299400000060680011f40004f1a30a334bb862e0002358000472475800046600041ac000000aee33a000000000000000000000000000000000ba359e97fa7f0a4d375c00000000000000000000003c84000e8ea172af86d965c1da4f500000000003b8000142837203a00002b4b8f51e61440006df0001de0f92703009800136800034f8bf082cafa0da000116067b4549e854ca00010b863827471a2848fdd70aa1d3a92d8400000029dc9400001c83510000179b3113781814c477f55207f97560000811fa0244ad42258000cc900f21f19c4f5c1143dc24180000004f21490f6885b4ca8200954731060ca746096420b1925004686e36898642566182636cd0d4826b269a3289bf4dead79af0c3e6f516bdc8541625a1420186af06e83f22b0cdc9b3c08b810cc4ea9e57010cd5eab2908a894c6585a243280002710004810d28dfe53d00000016ba1cb07d1b140002bf0001bb25c61f9227800156c8e24b6233a4b60842c289502d84110b100ec66581400025f4aa66da05b97546040e0486a1511a05fe000284800063a00000440000005491de893039a0000aa6e507ba0e700000009815da80011fc0004df0accc240002e5cc7522c000000008105668a26200000007a7198057562e69c800118d5609cc1bc00006e80002740558cae9041b3ae75172b65a11063c71e2a20f4c000b74987000001052603c0829d8050e9ae4ca0000c2832054799755b028942c14d84900f75bfd372d621509ac29e92e882100c031cf46800352adf02a4b2f0b68f6ce8239c2ab9c3400000002695cd58540a5c086700000003ee00004e25ea0000000e2e5fbd2fcce134200059022690bc29153d80dc1107431f90472f665441820c212522285070eed5407183538b80a4f4e3565274ccea2b82831e98e7f1c9d22cde47dc75f522009846a95937b879e5205c714a00141442ed4770e3070193b39511386c86130000184f5f00004515a2cce647b0bac3807c68d0a06decc34aea00000011743fe34396791e847380626d8b9d6e635ba6c48342695b493e40000001f216dc0002
  | 24 => 0x21a000000000056c5bc800057c0bf800065645b19689340003b81ed0000038ae252893c8e7e000353da810a471e1e91fe44342cb1946ad0d083cd204a8e062a0e9b9bac5000000000029ba000a22000000000063e4eb8000ea00005cf42250c200000002c0000b5f16ca1ca000048b2b2b04000a1b00020f0da81470a7993576564633858111fa0e85dc8b85496b83ab41e701fc4120c209451b28d40fe0d108e0b7a5b383b648e67905c819c8a83d7510017c3708b8198c14a0688e01192a2cb763b42eb891a502211372ce612fe2253998000b8d50d38ea9cc00000037780000000004c1800037e0003fc24f400031200000012bc0004301244000aa552ea7081278b310411d8dc247916d921c00000029619c6f1854ab7e82903bea11d401284bd86c8264a6ed0f4b6419996b08f89464781e28ab01d043496b87ac00004c895d5fab470000000dca5a12e98bbb462172823a69c00000039f0000000000065eec91f02f651a06202cca430002474e0c51b000037400090c0680d04a519cb42e00000000000000a491f65718000000cd0326000284c00000000015540b00a003a94e13aab8a3001134000000000000000042f000000151c00000000000001000000000f419411749eb00000000cb2c415ec0002771b115a40004f4a04cd4787ec6b80000008ea093a0ec2bd2063082ee800000037c800000008f54e82a9734090990c90d5749850332cb04a18b2d93add818629c38aa11a69614c5299abd19e00018b87e017d36c80000010a0a0d3c5822a0009f309600008a10005b8000049407106f8cf80000004d98ff20000003b1c00082a441464127c1634c74b10bee9fab2196b0000000464455c00000099000014b475d0001d100017107af00000000002b753080000003d807319a89bb7fa3f48e8000040d25300014c01f1089800076600017a0cbea66872424a064b9473a00022bd5469aa1e5e451102191297c87cfbabae3b1aaf09745161dedc6c44818b10a000113c0004f7000141469b1ad800011aa7c00000001e80005c91520664ad12f4a9915d6000347a7e88843b706b0ce68565d11c1400000000000000005de00000021a800027048400011ce0000a128451c84bb000000000000030fecf800057f0002cd94728a71601bd904c09a4500000964a4921d1e4868e00036c05440004ed1c080b4a453c341e45d0b041ef33f10652c210656990a1558a914138c409cf313419910c4689214568ae4ec455d39e89a92fc7f880000000000e2cbe215d5e6a9600000000004035c7000012c20a4ad985adae567421e8b4d6308cd18ca9800076752e13ece1899e2c30fa00008b19cbec141b0000000210000000000022dc0002f10ab82fcf640001545a794f2000270800000010d58b195419600001790605ed20d058ab942366de0002
  | 25 => 0x18c91f8a4a4c31501580254000000000103e2e20d8a8cd576b10da22e1000000000000000009c000026a4ef24c54b8a12717a00003140000002374ab128c00e0004878000872a47000000109c7a800000014b2ab5000173c15ca5724dae8b3a07f012f28641fa9325df178d760793cb71ec4b9b2838000000a34a6e411000000000016b4000516650903a9236dc1a1501142c15d9fe05fc09d60c7bf132901c84c000080800167e000000153502e53943a93c32880002c51e1868693600007b000035f0d80960000a2456e9648df84ec263c00029494f000222484800018d1c7cdc81de00013bc1c431600017d49f490927b52881b49540000000000000000018c000000253400145e3bf00029dca60000000232e08c0004c14000000b6f0001d244970000000970ff894500022f85a422b000116000028e0002e500000cf000231066700016392d81f200054a000070ca9a41f80000000004479e0ca13bb44cd2014ab38ff0390000000566b29800042465b380800000089d0002ae14a50005138ab8000a9923724b8edd3c42812b5411c22a9c69518f565c5071c0ad5ab4a7359800063605a3540000000aa12df1a2c92c81b327c0016af3e3064000024200015385403e62ac0000141508b5a0e0019496871016983390f69985cf8000000b975b3000125e5763d0cff16a695a0dea57cc465293b9000000047f0000c6f70e0001d90000be47540002878f5a8d500009ec0003f3107000148498a0001df40001a90000000fd842500017f4000000000000000089b44700006aa753ad023bd6608cc394a444a3e5c832d000000084b433057cab474d8d18dfd6bc0bc4190ee45b4000000000163a78e31b1422376721ac1878c3cc6113abaaf4ac4a544d903fcf3c0d590f155a9080004399074f2800000000000000000002658000a29800000075c48a03d1c8b43e3c800000015d86492a882ac2a66bd14188ec1685ed4368fa4b2e1382ec8c7754c19e13c9ddc06a3ec09e0001614b0f5610c514a4a6c3c1158d5505bc105a7051b804d8932ae45d366623bd1ac000300522a516af346657f97500006313b0cc2c000000000000000039f4b90b716265e13811fb4d3a1c64ed000000000000000010721a400014489b845f0000000a0f22114140014183923adc00070081624d14a00005423651c9959e39500017ecd6c4da46280000009d4025134e17b0000e68d240ee0591c2ab9e3aa404ba21f785104302ae18ed3e454c1fb0254ce05cad2c1866df43280199ae16a42d132a20c166ab774dca3d96a069251f25bc2525339e99d3cd308991110d78b9ca6346d2efd5fc712b1c9500bca0000000e5c000000000104d4060250000000000ba8d36d0dc95e56f000000080cb278001248f0e42a2668758dc60002ca8d1714aab20000001450
  | 26 => 0x62ad45148d8d283df0000000f783540698000b480003192af80005f015d180518227f43f0b081a240108f1b48474900000124038900000004f8000000097000000000019b20e16088074a703d90484e9197148200014e49180006e04f3800249075ea2e1321976d967ef266c0017418151ca00f495600000000002f60001b9a6480002a6bc8d148534aa20002520bbe2fe33ba258b6c00000009f000000030393807561db13c00002d05471df2eccd72000000228874238700000014c3b782b1d960b029930a7530514826d1401d084ba6c70d31ed41ae0002e30304f860002a182360000385569da01074325079e625863bd187220cd986ab371000000011a43b9572000000467cb38b6a59c0000000cd752a2d48c0d16a984557ab9a1f00001b500010620001ba941a000a301cfd7ff17e66f8001c0127c1eb3a5400169a09b0ca80016385ff3eec33aa7415e23c0000000530be00000ddc4482da1b0897abb088e972c00000000009840000000000000a9c2b43ea133c00098b5a400009dd00020957f12c06a5800000000000000024e000023ead38000646a6900028fc16aa870e5cb10ba034600011a40003fab7884d4f510001e6077511a6f35ddc00080087d3d4800000044551080009be8e514f0102000a37572533eb3216f3d94a608d837a34a88554be41499e2ea044600039a00a905a8100481cbc0000733a3000000000000021accd6000000000005905c584000021e29525aaa4c0626295442ea8fbe3341ea0000f6c0000e18c341ce000460263800000056e20180000003aec000150ab700007a030c00000020212aeb9b0000000d0a0003b48000c800c080020f92922dd03bc000000a5a08822604ec0c2b8c80894eca6804a1f45018a783cb1a0c9ba0001fe81c03a4976084000150600021184dcce64dbae15e80c4c21842219bd34092d0a00d815bcb4054311587202f80ca25a4203139004002f59352e257272847a01d5031d64d5ab5736e16c47ba0553aa983101c9dd5911c4c8ad63c09028f16482262042a6ce44b5c56703c4e7600056ca9c969600008c93180d611d80014ae645ac7ac20000000a6984d5f3ca7c4c813f190c31200058d1e5f63e000155a32c0000001b703b50223f52be8000d6489027b9fd4e129051d2820c8807900000f788ed1c50a1ad0408094b1f580008b8b452168cf42b84590ea2dd4518000000234c00026e27e1b4c00000000000000005c89cc8d949d59f83030dc6dba24b3ad80006ac0522cb115e95276f07e0000ac216000000900006625599496d1f70b32296fc9b304c281866d4c715ca6a8bf4f0a6383d20f22762b4201a58349ca1304239eba4365271fd9e567e21b31411140d7400043a00010e70001e515c800059f45b25e881e0005de111c0360004524001694000000000000066e000
  | 27 => 0x16a20003eb40000000000000c2468a0003ce617d2b0bac8081c14000000571992800000051180000000001bf2e640da0003bd80000002d7319d474ae000000029f40008010968000c0a1ed94ba50c4c674d2442c9812680406a132d27e6970668115038a5b07068b028a9501588fe85ca2f5016227d3364e252309d46c26151e0a9c4afc48c35f1a8c0000000000abc7ce1fb00000000000004d290fd5b6b953fb00000001934f080013ec4e64e188089970df8aec000b267142d82e2400045d0001280f8c48f0f357d8bb
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2524c431a0c86951524c431a0c86551524c431918875513194031d08745493194031918879513154031918875513154031d08749493154031d08745493154031d12745c4435403191a87d0d4154031b118110c4154031d08435c8415403190d821c55310f40a148154d6110f408b1811c16210d40c0c635c8515054090d821c55410f30a14815516110f30c0c645cb544c73090d821c55410d308d1811c16210d30a14815516110d30a0d82950635053081d87190514c530c0c645c8514c530b0982151404c030b1181151404c030914815d54310d2081e879954310d20a15811954310d208e1811c96010d2081f87593530c520a0e84d4d620c520a1a84d4d600c520961809ca4354420961829c24354420a6180189514c420c6172544604c420a6180989510c420c6172546600c420e09535894010020e21625454010020e0954589300c020e4162545300c020b42839095148020b41839095148020b22848c95148020b21848c95148020929859d36348020b4181d515348020b09859515348020961819d44348020d097550c4348020d097454f5148020f015454e5148020b42831855148020b41831855148020b2284d4d5148020b2184d4d5148020b418594d5148020f025494d5148020e436554d5148020f025454d5148020f015454d5148020a628614d5148020b228414d5148020b218414d5148020b428314d5148020b43835d95148020b40835d95148020b42831d95148020b41831d95148020a60865cd5148020b23845cd5148020b20845cd5148020a62861cd5148020b22841cd5148020b21841cd5148020b2284d8d5148020b2184d8d5148020b228498d5148020b218498d5148020e416318d5148020a628690d5148020a618690d5148020f014310d5148020d42735445148020d41735445148020929851d13148020c63765453148020d23745453148020d20745453148020c62765443148020c61765443148020d22745443148020d21745443148020a0c835516215310a0c8454d6214f1090d821d54310f1081c875954310f10a148550d6110f10a0d821506350710a0c835516210710a1883551601071081d87190534c710c0c645c8534c71081c87591530c710a0c8454d620c710a188454d600c710d09745cc5248210d42735c45248210d41735c45248210a148550d6110d10c18651cd4150110a91831854150110c90731854150110aa18218541501108e1821c5644c110a1885590434c110a9081590434c110c91645c4434c110c18651d1314c110a9184185314c110c9074185314c110ac182185314c110d09745cc5248110d22745c45248110d21745c45248110d42735c45248110d41735c45248110aa184d8d2148110a61815952008010e22545852008010e21545852008010e42535852008010e41535852008010
  | 1 => 0x200000146c1394c000022000005c0002c0000002985c0000000000051c00812908ab80046000000000000007e00560010000000c6b20000120000042800780357e94d059c822844895840000000017800133516a0000002528a5a3cc048700120ec00a8d15d0005bc7000b62b26a503c07468804c00000004a950c87cd2423308e1a080027200002599c70a7260dc9c8b000012c0587084367dbd9f4a41d184d9434cd6c001e001aa6cc25655dce00418b21038980c1a354144605a007944000a20c002360000189f0340000000a17f2e800e4002c00000002c550f011981dc00000011c000000001590000001220035800000602000f40550000645f048005e920000000004f0000000249b40000000e4749d49c0000620000085b00000094750000102645115c002c0a9cd2b198008cde650ba6562a82192b3449d7ab4689c2aa0cfc9f000a126568025d4f12381b8c6821e8b420710000000a40000000001f0016300000011e003b180664f50a1ca52a0000082002268d0c00000000000282ac31a4800008000002a4000027c00000600c12000001402000401002050381c0a0000014000502008040100018040d028002c010000000020000808000002800000a0040002008000a00020040c050580c2a01000001200000000a07008180200c19759c06150c43c19755c06150c43c8a725c06150c43c89725c06150c43899801d94394443991801c54394443991801c54354443945821c54354443951801c54354443919801c54354443b11801c54354443916861c54354443c16861c54354443d12801c54354443915801c54354443d11801c54354443911801c5435444388d82dd94354043e09435895014043e11435855014043c16765c45450f31c18545c06150f31c15769c75410e31c25625c46215131c29625c06215131c29725806015131c31715806015131a1685d906150d31991801c54350531c0c635c86155031c18635c06155031a15859916110c31d06745c4435483181f87d974350431a0e86d0d5250431c15655c44310431a918110d6010431e08435496010431c0c645cb544c431c18645c3544c43181e869d9544c431a0c8655
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xc0140c9002016d2a381032180014080640a09801c54354443c80c130038a86a88876019110d52580410c6a032221ae420aa018c816488154d6110f40902c9102aa2c221e612059220554584434c240b2442a86b0887886201cd821854150110940c9102b208698221410955917110d30442123303a0c298a60886201d182185314c110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 22
  | 6 => 969
  | 5 => 5184
  | 4 => 3008
  | 3 => 178
  | 2 => 13
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
  | 7 => packedAt gbK7 (430+((h/13+packedAt gbK7 (352+(h % 13)*6) 6) % 49)*6) 6
  | 6 => packedAt gbK6 (31287+((h/427+packedAt gbK6 (26163+(h % 427)*12) 12) % 2475)*11) 11
  | 5 => packedAt gbK5 (227036+((h/2146+packedAt gbK5 (196992+(h % 2146)*14) 14) % 9347)*14) 14
  | 4 => packedAt gbK4 (162589+((h/1169+packedAt gbK4 (147392+(h % 1169)*13) 13) % 4632)*13) 13
  | 3 => packedAt gbK3 (11346+((h/74+packedAt gbK3 (10680+(h % 74)*9) 9) % 355)*9) 9
  | 2 => packedAt gbK2 (948+((h/5+packedAt gbK2 (923+(h % 5)*5) 5) % 20)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe0fe1fe3c3fc7c7e3e38f8fc31f871fe1dc70f
  | 1 => 0xff1fe1fffc3fff8fc03f1f1ffe3ffe0e2279f3
  | 2 => 0x1ffe03ffc07ff1ffc01fe03fc07ff1c38e3c
  | 3 => 0xffe00003ffff8001ffffe0003fff8001fc0fc0
  | 4 => 0xfffffffc00000001ffffffffc0000001fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2a0284444890a8800a182824904910ac0cc305
  | 1 => 0x40040000800000100001010802102000001052
  | 2 => 0x14c8488911095002d440124124824d40c30c28
  | 3 => 0x86415d522a28192566aa400239270465740f80
  | 4 => 0x1891918033b26249b9349c9380040989bbe000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeecece8feecece8feecece8feecece8feecece8feecece8feecece8feecece8feecece8feecece8feecece8feecece8feecece8feecece8feecece8feecece8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_36673
namespace PEqualNP.Outside.L_meta_36673
open PEqualNP.Outside.L_meta_36673.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 13 := bgb_2_0
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
theorem bgb_3_160 : Interval gbAtlas 3 160 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 178 := (concat (concat bgb_3_0 (concat bgb_3_32 bgb_3_64)) (concat bgb_3_96 (concat bgb_3_128 bgb_3_160)))
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
theorem allgb_4 : Interval gbAtlas 4 0 3008 := (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 (concat bgb_4_192 bgb_4_224)) (concat bgb_4_256 (concat bgb_4_288 bgb_4_320)))) (concat (concat (concat bgb_4_352 (concat bgb_4_384 bgb_4_416)) (concat bgb_4_448 (concat bgb_4_480 bgb_4_512))) (concat (concat bgb_4_544 (concat bgb_4_576 bgb_4_608)) (concat bgb_4_640 (concat bgb_4_672 bgb_4_704))))) (concat (concat (concat (concat bgb_4_736 (concat bgb_4_768 bgb_4_800)) (concat bgb_4_832 (concat bgb_4_864 bgb_4_896))) (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat bgb_4_1024 (concat bgb_4_1056 bgb_4_1088)))) (concat (concat (concat bgb_4_1120 (concat bgb_4_1152 bgb_4_1184)) (concat bgb_4_1216 (concat bgb_4_1248 bgb_4_1280))) (concat (concat bgb_4_1312 (concat bgb_4_1344 bgb_4_1376)) (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472)))))) (concat (concat (concat (concat (concat bgb_4_1504 bgb_4_1536) (concat bgb_4_1568 (concat bgb_4_1600 bgb_4_1632))) (concat (concat bgb_4_1664 (concat bgb_4_1696 bgb_4_1728)) (concat bgb_4_1760 (concat bgb_4_1792 bgb_4_1824)))) (concat (concat (concat bgb_4_1856 (concat bgb_4_1888 bgb_4_1920)) (concat bgb_4_1952 (concat bgb_4_1984 bgb_4_2016))) (concat (concat bgb_4_2048 (concat bgb_4_2080 bgb_4_2112)) (concat bgb_4_2144 (concat bgb_4_2176 bgb_4_2208))))) (concat (concat (concat (concat bgb_4_2240 (concat bgb_4_2272 bgb_4_2304)) (concat bgb_4_2336 (concat bgb_4_2368 bgb_4_2400))) (concat (concat bgb_4_2432 (concat bgb_4_2464 bgb_4_2496)) (concat bgb_4_2528 (concat bgb_4_2560 bgb_4_2592)))) (concat (concat (concat bgb_4_2624 (concat bgb_4_2656 bgb_4_2688)) (concat bgb_4_2720 (concat bgb_4_2752 bgb_4_2784))) (concat (concat bgb_4_2816 (concat bgb_4_2848 bgb_4_2880)) (concat bgb_4_2912 (concat bgb_4_2944 bgb_4_2976)))))))
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
theorem allgb_5 : Interval gbAtlas 5 0 5184 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)))))) (concat (concat (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888))))) (concat (concat (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560))))))) (concat (concat (concat (concat (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720))) (concat (concat bgb_5_2752 bgb_5_2784) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880)))) (concat (concat (concat bgb_5_2912 bgb_5_2944) (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040))) (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200))))) (concat (concat (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360))) (concat (concat bgb_5_3392 bgb_5_3424) (concat bgb_5_3456 (concat bgb_5_3488 bgb_5_3520)))) (concat (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 (concat bgb_5_3648 bgb_5_3680))) (concat (concat bgb_5_3712 bgb_5_3744) (concat bgb_5_3776 (concat bgb_5_3808 bgb_5_3840)))))) (concat (concat (concat (concat (concat bgb_5_3872 bgb_5_3904) (concat bgb_5_3936 (concat bgb_5_3968 bgb_5_4000))) (concat (concat bgb_5_4032 bgb_5_4064) (concat bgb_5_4096 (concat bgb_5_4128 bgb_5_4160)))) (concat (concat (concat bgb_5_4192 bgb_5_4224) (concat bgb_5_4256 (concat bgb_5_4288 bgb_5_4320))) (concat (concat bgb_5_4352 bgb_5_4384) (concat bgb_5_4416 (concat bgb_5_4448 bgb_5_4480))))) (concat (concat (concat (concat bgb_5_4512 bgb_5_4544) (concat bgb_5_4576 (concat bgb_5_4608 bgb_5_4640))) (concat (concat bgb_5_4672 bgb_5_4704) (concat bgb_5_4736 (concat bgb_5_4768 bgb_5_4800)))) (concat (concat (concat bgb_5_4832 bgb_5_4864) (concat bgb_5_4896 (concat bgb_5_4928 bgb_5_4960))) (concat (concat bgb_5_4992 (concat bgb_5_5024 bgb_5_5056)) (concat bgb_5_5088 (concat bgb_5_5120 bgb_5_5152))))))))
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
theorem bgb_6_960 : Interval gbAtlas 6 960 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 969 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 bgb_6_576)) (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704))) (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832)) (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 22 := bgb_7_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfeecece8aaa8a8a8feecece8aaa8a8a8feecece8aaa8a8a8feecece8aaa8a8a8feecece8aaa8a8a8feecece8aaa8a8a8feecece8aaa8a8a8feecece8aaa8a8a8
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,6,38)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,6,38)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372960 * 2 ^ 32 + 3940608672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36673.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[0,1]⟩,⟨.and,[4,5]⟩,⟨.or,[2,8]⟩,⟨.or,[3,9]⟩,⟨.and,[2,6]⟩,⟨.and,[3,9]⟩,⟨.and,[7,10]⟩,⟨.or,[0,11]⟩,⟨.or,[12,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 3940608672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 3940608672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36673

open PEqualNP.Outside.L_meta_36673 in
theorem PEqualNP.Outside.L_meta_36673 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 3940608672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 3940608672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
