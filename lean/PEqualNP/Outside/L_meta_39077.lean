import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_39077.Model
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


end PEqualNP.Outside.L_meta_39077.Model

namespace PEqualNP.Outside.L_meta_39077
open PEqualNP.Outside.L_meta_39077.Model
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

def SBf (j : Nat) : Nat := [6, 8, 8, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_39077

namespace PEqualNP.Outside.L_meta_39077
open PEqualNP.Outside.L_meta_39077.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x3013002010dc32de32bc42bf43de43bd43dd439d43be42
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40020001091f548ca38a4a1cb14943a6292871d5490f1ea4a1c755032c6292871d5310b1884194314943
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x20d6510832
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 11
  | 2 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/10+packedAt s0K4 (144+(h % 10)*4) 4) % 9)
  | 3 => 2*((h/10+packedAt s0K3 (297+(h % 10)*4) 4) % 11)
  | 2 => 2*((h/1+packedAt s0K2 (38+(h % 1)*1) 1) % 1)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x7ffff81ffffffe07fff83fff83ffffcf1f1ff
  | 2 => 0xf81ffffe07ffffff81fffc1fffc1ffff3e3e3f
  | 3 => 0xffe03ffff80fe0fffe0fffe0fffe0e03cfcfcc
  | 4 => 0x3ffffff000fffff00000fffff003f00ff0
  | 5 => 0xffffc000000000ffffffffff00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x9082888c4122482016528129281292a850d0d5
  | 2 => 0x224511103244904580a524125241255126262a
  | 3 => 0x5149a22490e9018aaa09ca409ca4081a8b4b4c
  | 4 => 0x65963c492481daf34d306318e739c063f00db0
  | 5 => 0x86183871c70e1cfc71ce739c06318183fdb000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0fcc0fcc0c0c0fcc0fcc0fcc0c0c0fcc0fcc0fcc0c0c0fcc0fcc0fcc0c0c0fcc0fcc0fcc0c0c0fcc0fcc0fcc0c0c0fcc0fcc0fcc0c0c0fcc0fcc0fcc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_39077
namespace PEqualNP.Outside.L_meta_39077
open PEqualNP.Outside.L_meta_39077.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x1e0c02c04421150050011c0105148fc32fd42fd20ff31fe20fd32ff42ff21fd10fd43fc20fc10fe42fe21ff43fc30ff20fe31fd40fd30ff40fc21fd21ff10fc43fe10fd41fc31fe40ff30fc42ff32fc40fd31fe41fe43ff41fc41fe32fe30
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x2637d51cc2fca818f74c530dfa1c87f521442faa898f754c20bf2a421de438c2fea498fb94810ef18c617c524c7de41105f94621be29a43dd43cc7ec8220df55021f790e41be54043ba63985f94442bf29061bd42106f8a6a16f50f42bf280637f54c87b86498df94221beaa4437e50042f8a9187b50842dfaa2217f548cabaa7a05bd4910ee29a217e53d06faa4207b48720bfaa461bf43506fea790cf15131bf29e857c54c83b864187dc8621dea12817e54c82fca8205f55320beaa261be540cafea4a1df94910df21a81f741506faa4085f94041eea98217c514cafea7107ecc230af298837d54c86faa221d7d4d41f6990657c5050fba60185f14810bea96837f54486fca4205f54b40bea84437c54042faa3a1df54830bea8c657d50086faa1a0fd54420bf28065be43107be86a1df94421ef980617e50d06f8a9197750d31beaa6217f53c437e8320df95321be28a417d5390bee8320df94832bea9c83df534827ca990ef90640bf29c837c54cc77aa910df94e43bf290637d52cc27aa990df94440dea00817e52c42fca410df94640de21e81fa100437aa990df942429eaa4437c52443be86985f55230ee21c637d52886fca3185f54f10bf29463bd540cafea0a1d754e40bf28e817c53043da40106f10440fb90c215f534437aa9185f54910f7a1285df43cc2faa9197710c31fa10c21bf4350bbe86195f94b31bfa9a21ec52442fea6a05f94410bea9c415e53082faa920efd0842ef182617c54887ee6298df95030bf284837f505077ca990ef50740ef29e817f53842fea8887dc4210bf294837d5290efaa8085f14930bfaa2617e510c7be61185fd5210aea98837c52c42faa1997750c30bf2a661bf4290bea20085f15220ee19461f621086fca5185f95220bf280415f5350a78a8995f54e40bfa9621f721486faa5a1f78c932bea8465de4310efaa620df94441dea1c81f621c42fca1995f94631bf29a41df535077e86205f14c20be28265f5210867aa8085d14520bea9c21ef4290afca610d714d20be2a265ee4210af8a098df15120af29e817f53506fea8995fd4c10bf29841f521c42fea2a15f55210bf294217f5350af8a4a0d754c42bf298877e51c83bc6498df94c309faa2657e50cc6fca3195f55242bea8c873f54443bca7204f95330bfaa2417d50c87ba87185714d10df2a0417e51cc2faa8106f10e41df21683de53c86fea810fe8c030bf29e817c53483de64994fd5120dfaa2636d52042faa3205714d419e2a241dc535077a85a06f90f40bf2a6217f53082faa6216f50f41ee21a61bc54442fca2105794f21de214815e5310af8a6a0df94042bea9a217e5310af8a6884f55230de216837e52043b887985f94443f790843dd320c6fea7905fd4520bea84857c53c437e84a05f54031bf28e657c540c37c82a0df94b30
  | 1 => 0xe544c37ea8995f94c40f710c417e52902baa6107ecc130dfa1e857d52cc6faa7197ed0240be28243dc53482f8a9087dc84109eaa6617c514c2faa5085fd5221fd90441f451482fca190ef55010be29a817d540c6fca7105f54c40eea18877c53842f8a8196f15131ee99463f421042f8a7905f94620bfa82657c544c37a8621dfd5010f610c417e530c6faa120df942439f2a065f710042faa1a15f94d10de20c817d53886f8a710ef50a41be2a221be43907be65195f95032ef98c63be40502fca1105f94021bea88417e5210bca4210df54f40bea88657c548c6fca1195fd4810be2a043bf41502fca8906f10c42ee990657f530867ca818df95010bf280877d530837e87a0df54440ef988637f540c2fca2195f94e42beaa241bd43507baa790cf55031fd88221ed52042fea9105f14940bea80657e53106f8a2a06750c43fc90041bf41106f8a2a1df54d20aea9e437f540c6f8a9996f10e42beaa0657e52107bc86995f14542bea8c617d528c778a8906f90440dfa1c815e53902faa690cf15110b729021de530837884a0df55121dfa16817e544c6fca6195fd4a10bf29c813e548c2faa2187790f31bea9e837e52082eaa2107754c42bea9e43de53043bca620df950429f2a0217f544c77ea89077cca31bfaa6617d538c6f8a9885f14a10ef19061df320c6faa3a07bd4910f790a41be540c77c84a0df54243fd902417d54902fea9885f54720bf2a043dd32cc2baa608778c531beaa0617d5010778a8996f10d40bfaa4637f52442fea4a0fdcc631f690a417e52d06fca7886f55031bf284637e54487bca6215f54b10bf2a465be4310b788420774c431ee992617c5250fbe8721df54c21bf296877c54cc2faa0215fd5320f719065f9300c2fca1185f54a409eaa0657e548c6fca2186f95221bf28c83df438cb7aa8105f94b40ef218613f544c6fca8105f94e10ef98a615f53482faa9107dd4520fca00817e548877a82a05f54331bf2a221df53443bc87995f94743bea8c21de328c2fea710df94742f710241dc310c2faa6086f50842bfa9a43df31cc2f8a790df15121bf286877f514cbbc62187790d31deaa6617c540c6faa021df94342bfa92617c54083788620f70cb31bf28081dd531077a86a17710e32bea9461ee21082fca321df55231fb10a21df32cc3f621085fd4d20fb08221be4250afca820df54843bea8c85be4390b7e83a05f55331dfa1483bd43103d842105f94d21bf2a087fa40103eca2104f95020bf28061dc5350afaa8995f15321fc88021bf409027ca910f70c630bea9483dd434cafaa420fd50441df21081dd53903be8718dfd4121eea1e65bd411077c86a1f7cc930fa988637e5210efca3215714d42eea9e817c5050bbe64195fd4543bfaa0657e544cafaa3a177d0c31be28283ef328cb7e8621df15131bfa8
  | 2 => 0xc802040000284e30800004070681002c000d8010140100402004042280e01807014320a095000020000100c7b44001010250116f03c000003c038000bc00000000001c00831004290000203c0031dc4000010180606000038290000b0142001c01070020109a008580005e04c0000400000050580208445000010101f04c09058080001a03006020a10000003c000041507c00054140307a000031f03500407068000003b00000058150900201003094200400514c0106004000190980001847038010100401814224000b002020a80d800000320280026c1804caf04816000331a0060181d0085113c000002a068180080800c0a0040300c001585e0e00f0260050c000e000020740849400002000010201406c0005001140000e4311dc6d0001b0482309286008000046903c03002faa921cf55020bea9e417e53c83b886195f94210f790c435e530437c85205f54231bf29e437e548c2faa9985f14e20bea94417f54ccafca9995f94240dfa10837d5110bde40105f54e30f690843fb40503dc4290fe88020bfaa041bf40102f8a610dfd4142ef29c43be548c2fca521778cb31bba8a417f51503ec6218d794e21beaa6657f52502faa8885f54732bea86876c52442fea2985f94a43bf298217d53d0aeca2105f95331eea9c43be54cc2baa710df94e21efa9a857d520c6faa3105fd5331bf294657
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xd544433554944209798e544425e63153219798f54842786055121c714e425063e65d09408f59053c829c644c8329b189534427965840108f593538865e6394821d9549100432c54d49109718d518825d63949108f191500865e63d50208f992500c23e6515132d9544210826f6550842c7553430ca3c6454d109d195214431c548c9319758c544871d5454e219798e52c423f6454d10c755331cc25d63150218f596540423e64d481097d8d509065d65d0c3197994534423d64148108fd91508ca7b60551218f992544cb1c5450f319e980540863e64150329758c515025e63943429b98854cc6756194d20c7d50438c69c644c73097996434cb1e5494e21c750e5010e7561d5232cdd53514831d54d0c319d587530825d6395120d9545200831c5490d318f59353c874c53149108f590530831c635503197d8d5090a766114c20c795253c867b6550040c7153534825f6550c43c7150324c71d5310c429718d544869d63d0040c794e419031d54ccb3097d8d54c423e64948218f990530427565c8410cbd50524425e63151219d594210423d6590c428f99053c871d53504419e181534865d63149408f593538431c6355330c714d4350a3e6414c219bd95200823d64d4c10c794c419025e63145409d987548ca3d6494e208f191520c26d62d5010c754f411065d63952209718d528425d63943428f593538823d6590c41c7151430c35653944208f59352c431c53d0d418f592510865f6354b41cb150524425e63150318f590530425e6314940c755253c865e639491097d8d544c63f65508418fd954310f6451c8520c714d435066d62d5231d554e510823f65500408fd91530865d6394b109b98b530425c6355310c7952318c31e53d0e408f590538865d63d521097997434c23d64145309d58454ccb1e53d02408f596540ca6e6214810c755043cc25f63549108f590504865f63551108f992534425e63952209bd95320ca5e6315320b9189100423f65504419798e544831e5310a408f191530865e63153108f990540423d64d4c209798e50d071d53d0b40cb5525204275619512097d95310c63d65908409b58a534423d6494d108f992544829d64cc0308f592534825f654c0309b997214823e6494910d5d4f514831e5454c209798f548829c644ca319ed81534863e641481097997314c29d63109419dd85534823f6454f108fd91508c65e63d5221c7d53534831d435484397d95320c63f6454d208f191510c36552c40108f992534831d544cb308f596540c65d6315020c7551530827b65480208f59053c423d6414a109e580530869d6310b41a718d429067a6014c218f990528425e6394d108f191528431d5494c2097d8d511026e62d52319758c520425d6594c108f59250cca3c64546208f19152cc63e6510941c7952530826d6295110
  | 1 => 0x4277615512097d8d528431c5450d319b98b540425c63540218f99252c425d63141219b5962108337541452097997324c23f6550842c7552538871e5454c109bd95210865d6510c32d914a214423c6454f20a718d41d029c63508428f99250cca5d63152218f992510871e5350e408f59252c431d54cc431c794e429031d63151329d986534826e6214c108f592524423e6494c30c7d954310f6452487109718d509065f6550c308f993538425d63d5220d9d48218423c64542319718d51d0b4e5394810a758c411025e63d4b10d9548210431e5454f218f191534827661d50209798e51c823e65d0d419758f52c427561150208f992538425d6314a109b98a524425f6354620c7952530423d6494632c7553320ca9f6550c43c7150534825d658c8308f99053c429e648c1309798e548432e54548109dd85544c23e6495131a7191324c36561149108fd95431023e6414f20c754f421065f63548409798c530829d6310a40d914a104436552c841097d8d540863e64d4e20d3d4c524423d6494c30d9546210829c63509409718d544825e63150329d584530825e6590d319758e529065e63946428f993530825e6315010d9145214831d5410c32c714c425066d6215331a71894310e746155130c7553320c76521540219bd89544425d6315320a7590310c23e6414e218f99741502e461480209798e529065e63d50108fd91520c26e6215030a7590320c25d6590c30c7152324ca7765484219759653083565354420c7550434c25d6510c319d185534823e6510d409d98454cca5e6514d20b958a210865f654c832c754e43d025c6354840d354d52042776550441d554d510823e64145308f596411023c6454232cd15351482e765484218f993538865e6315221a758c421023d64149309758e510869c6350540a7191314c31f5414d10c7550430c6746155120c714e4250b1d5350b409718d524425f6354021c7551320ca3e64150319758e544c23c6454f108f59250cc65e6315020c7952328c23d6414d219ed95100425d63d50209d996214431d5454f21a71854310e3f6454b31c7150534423f64544309758f548865d63d50109d987530834e5354810c755131cc31c6355032c758e548c277654c4318f59251c833654944209758f54c872f54d49108f990504866f6254d108fd91518834c53d49109dd95100425d63153219b588540c31f5414d209758e51c831d544c8318f99353c863e64d4c10a758f409035453d45209718d54c829f6050c43c754c431063c6454d219798c528431e54cc2309798f54c871d4354443a7590328c23e64946328f191524435753145209b58b530425e650c931c7950328c29d6490c43c754f4210a6f625513097d8d51d0a7b654c030c7952438c31c5490d32a7590318c25d63d48109798c520429c644cb309718
  | 2 => 0x900c01004f7054110d00d000070480400003144280100a0080006c1100002064080000e008130641b0b80500019010160001a01405000030000b008020040900c01000600000c00c1b010440103100426080080000c0380000005064043c03c0000b054000241e000040050a01c000000b00000000340b8df0e4000040003811058000040b0200204000004020245b330100a82b03400050150002d20c0202c060582c01c0a00001004060143202c1b4b0020201f0ec000000015c0300000058000501f044420402b0340b2b000040080000807c010040700401000001040003001000040800203c00030160b05100c020dc01018041480b0500000c2300802118040340003414000000d0410af1d5454c108f990524c25e6315021a7191320c71d5390c41a718d421071d544c4318fd9151cca3e65151209e580540867661150209798c504871c548c5319758e544429d640c931c754d421071d5310f409798e534831e540c6309758e50d063e64d4b108fd9153c8334541452097195434c65e63944219d984520429d64cc2309798c530423f64549108f990530826d6594810d9547200823d64948218f99251c831c53905419758c54c425c635502197596310c23e6414d21c714f4350a5f63551218f994544423e65151318f19151ccb1e5450e30d9d95210871c5450f328f592538423d64940309d587540829d63106409798f540c23d64d48109b988540423f6454d21c7552530425f63553209718d511025f63551329d984540c36452485109b994524426d6214c108f992544431d54d0f30cb952520429c644c431c754d41d031f54d4d10a718d42d031e5454e21c7151434cb2d54548109b189544c2756115030a718d411065e6510d308f992538829e63901409b98a544425c6354b418f592528c65d65d0c328fd91528427661951209758e520865f63551209b588540429d640cb318f590530863e65d0d429758e5190b4f53d4910c7153534425d63150108f990540831d5350842d514c514826e6294d109dd85524425d6395210c754f41d023e6494331c754e4310b1d63151319718d5090b3654544208f596540823f64540218f992528c76451881208f59053c865c6550d329b18954443355454420b9181210871f5410e329798f520434d5394810d9185520
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x20000400000104020000001800000032041071d9544c43183aed2a6611841c76551320ca0e3b2a899063451c543544438c8eca92200841d76950318c20ebb4a819461435c85450c30a18e4a1aa421d0c72550434c28b38ea821c65075d8540c931a28e2aa0869841c7655131cc28ab88a8a1861435c85450f31838ecaa2659851b7050e5010e8ab88a8a1e65439cb5410e31
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (i*5) 5
  | 6 => packedAt s1K6 (i*16) 16
  | 5 => packedAt s1K5 (i*27) 27
  | 4 => packedAt s1K4 (i*38) 38
  | 3 => packedAt s1K3 (i*49) 49
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s1K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/20+packedAt s1K6 (640+(h % 20)*6) 6) % 40)
  | 5 => 2*((h/243+packedAt s1K5 (17982+(h % 243)*10) 10) % 666)
  | 4 => 2*((h/218+packedAt s1K4 (20938+(h % 218)*10) 10) % 551)
  | 3 => 2*((h/35+packedAt s1K3 (1029+(h % 35)*5) 5) % 21)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffc1fffffff03ffff83ffc1fffffcf8f1ff
  | 2 => 0xf03fffe07ffc3ffc1f07fc3ffe1fc0ff473e73
  | 3 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8104044410480000a5090044802254501850a5
  | 2 => 0x248a48832490612c0a42a429521482a9432652
  | 3 => 0x429291090d2206554084ca8265412a0a858b18
  | 4 => 0x6b2ce252483aab9a73d06223b9980c33e80de0
  | 5 => 0x8c30c39c71c333e39ce77330311030c3f6f000
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faa0aaa0faaafaa0faa0aaa0faaafaa0faa0aaa0faaafaa0faa0aaa0faaafaa0faa0aaa0faaafaa0faa0aaa0faaafaa0faa0aaa0faaafaa0faa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_39077
namespace PEqualNP.Outside.L_meta_39077
open PEqualNP.Outside.L_meta_39077.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x210604000900024710004124300400240008d001fe30fd21fe43ff10fc30fe40fc31fd41fc40fc32fd43fc41ff41fe21fc43fe32ff32fd32fe20fd20fc42fd40ff42fd30fc20fc21ff30ff31fd31fd10ff40fe31fc10ff43fe41fe42ff20ff21fe10fd42
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x8617d548c3bca620fdcc631bf288437c54482f8a790cf15120bfaa4437d51083da401077d0e32bea8c21dd32cc37ea898df14a10bf280217e53086faa620fdc8410ee21e61bd540cafea9905f54b31be2a4217e544437a84215f54242dfa1085be54043ec20885f94d20bf2a2637c53c83b86598df94f20bf2a0877d54842fca9985f14132bea8c857c5050af8a898fe48020dfa1c81df5350b7aa9187d88510deaa0413f544cbbca7a07710c32de2a2417d548c6faa998df14e20dfa0c83be41102faa5a05f54910bea90837e50882fca190df54c20de2a221bf42906fca198fb50842faa88413c544cafca9995f95331bf28e857d52842faa3a15fd4d42bf2a265f421042baa710ef10c42bea90637e50ccafca710dfd4530bfaa0415c5350afca3204f95230bf29821df53442fca2084f95221bfaa265de53042faa7907948421fb88421bd43902faa010df55243bea8e81be42903bc8798dfd4e21f790843df320cbbca710f74c832bf2a6217e5190af8a810f78c932ee21c65dd430c3ec43885f14c21dfa08837d54ccaf8a9905f14532afa9a83bc42506fca6187b94810bf29e837e5410778a898df94243ef196637e53d02faa190df95230bfaa2637e51d02f8a9186fd0240ef98061fa40102f8a6a05f94c31bf2a4417c5150ff681205f94240bfa9c21bc41102fca910fdcc531bf2a243de530837ca990df94840f710841de318c2fca620fdc8521bf294637e51d0efaa118df94d21fd98461dc53506fca0214f55010bea8c413f54442e8a2905f94e40bfaa2437e508cafca5a0df54c42be29a21de43ccafaa6885f14c10de218837f534827aa9985f54332df2a461bc43906faa3205fd4931bfa8287bf41503bc8621fe500409f2a021df328cad8a4885f14d41fd982617c544cbde43907d48421dfa1083de314c6fca5a06f50040efa1a87de434cbf620885f95040faa0883ed52043f621085f94a32eea98857f54442faa3187d14520beaa0215f5350afea4a0df54840ef182617e5290efca9195f94c32beaa6617e520c6baa6107b08620beaa2617e500c6fca8085f14d21be282637c54083b864186f90541ee18c617e53c42eca2106f90e41af29c437e548c6fca621dfd5230af298217d538cafca6885f54241df21683bf42502fea8085f15231dea14837d54882fca721df14542bf28c43be540cafca12177d0e31be2a065de320c2faa8185754c42bfaa661be54cc3ee4310df54d21bea88653e54c87baa710dfd4d40f6908437d508cafaa6905b94810bfa82437e54086faa5206f50841f790a41df434c3ba6218f750e30fda0281dd314c37e87a0dfd4810be29263be54886faa1a1ef10d40dfa18813d540cb7a84a05f54a30be292217f54087bc86184f95020f7904417d540caf8a9985f54e42be29621df53483bca790dfd5310
  | 1 => 0xf54ccaf8a818df94341bea8e65f641107be61185f15220bf28c657d53c86fea0a15f94230bf2a643f510042f8a6105fd4543dfa1887dd434c6fca118f7cc631fd90441f421842fca9905f95020af298837d54482faa2217794c42f710a437c54042fea6087b88120bea88617e510837e85215fd4a10de214817d518cafaa910ef50f42be29c217e51102fca8187794e40bf288833f544827ca8197e8c030ef98863f621086faa9907754c41b7a92217c54cc6fea4985f54221ef98a617d52d07de4310df95210fba0a837e53082fea8187754f40bfaa2417d51102faa7205fd4d10bea9e85df328c6faa6085f94b31fc980617e539077c86a1df54b30eea98417d5290fda42907754c10bfa8a85dc438c6faa898fdc4010bfa9281bf544cb7ea8906f90640bf28041bd54cc3eca2105f15321bfaa2617f514837e86a0df94b10bea9021bf4350af8a910efd0e43bea9843bc4390afca5985794f21ee99463bd4310fbe879877cc930bfaa4637c505077e83a05fd4f10fd90241bf42d02faa7887e84010dfa00817c52506f8a78877cc831bfa8a65f910043b865185f14540df212855c53482fea610df94820bf28c617c5250efca2215f94843bea94437f530827aa8105fd5331bfaa065ec21082fea990fd48510ee29a215d53902faa8105f94b43bfa9e415e5310a7aa818f70c931bf28e417d52d0e7ca818ef90941f7210857d544caeaa2106f90e42bfa82657e510c2fca7107bcc932deaa4437e52906faa321d754f21bf29481bd43506faa018f714d20bf280437c5050ef8a9994f15110ee99261bd4350afca1a1f710d30bf29e85ee21883ba6418df95032be2a2437e528427ea898df55031f6990653d54c87bc8698f710c31bea9441de438c3ec6218df55110be28a617c54c42f8a9195fd5220de2a265dc5350afaa890f750c43bf280817e51906faa0215f54c40f7a1285bc41903ba8798f78ca30beaa0437d520c2bea6885f94732bea8087f521c42fea7105f94431bf2a0857d52907bc62187b8c832bfa92217d53886fca020df95031bea9e81df53506faa990d754c10ef98e61df430cbee8320ef10f40dea0e81ef328cafea2a05f14d42bea86637d5210f7c86215f54a31be2a2217e5210afca0185794c20bf280657d54902f8a090df94241f7900417d548cafca321ef90140bf284437d50d0af8a710ef95020fd100417e518c73a8621df54b10deaa0633d548c3bc6498f754e40bf29461dd43ccafaa1a0ef50b40bfa82837d50106faa7185fd4d41de216837d5090fea6218df94443eea1a65ef52442fca4885f94832bf29083bc42102f8a4a05754f40df2a0633e54cc3be65985f54730bfa8263dd300c37c87a05f14810bf28c417e5390afaa7084f15131bea9c637d53907be8721df54e20bf28865bd54042f8a8985fd5232ee18
  | 2 => 0x78040cc020980000c06000000b00026c000880c01410099d12480a0000000800030050280610c00090010401a07c0602407000580116304000000000045d088000000000400008cd00418050030144f2b4000000b1500f0000b01c13104003e4000402d1a8010280000001018160100d4fc560040022000000000000a2a40a074040182500018014090040000800020d7088750001706c0b0005f1bc1501c2003801000130000e6ccaf08c080040200c030006408400300a01380545c037f40005c00018042a44581c4101814001ef64dc90082f038120001d0280e09404000000440819c0e00c000206302803058010f8000000001c0600c540000100803154000000300c030002c00c1e05c0300c0112802004071040405c1c15c040042608402000010703004c000e80201c0e0dc180e4320000608008170030140b02805012faa0195f94043bf29c217e50d0abca7205f95130be28a41dd31cc3ee43085dd4520dfaa221be43106fea790df55241beaa6217d5490b7a8220df94830ae29a837e52086faa3a1df14930efa18635c53442fca5215f94f21aea98835e53d02bea6905f14d20bfa9287ef4290b7c86a05fd5031f690e41bf43d0af8a8186f50f41bf28e617d51c837aa990f754f21f629221bd431037c84205fd4d21bea8887bd41502fca4085f94c42bf284216d52042fea5885fd5210bea9e837e53102fca8907dd45209eaa4437
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x6520431d6315132d9544210823d64940308f994544825e6314c1097d8d544425e6315121a7191328c66f654c83297d8d528423f65508419d987548ca5d658c8308f593520431c548c9329d587540827561d4c2097996434ca3c6454d209b588530426f6254d109d584530831d5390c419758c540832f54149109798f52c423d64149308f990530829d640c6309798c530831e5350e40c754f421071d544c8319b98a524423f65504419b588540429d63104408f590514c31e5390a408fd91534425e6394642d354e520425e6394d20d954b210425d6394b10c754e43d031c548c931cb552520429c63504418f99053c863d6494b108f590530866e6214c10c754d411075453145209d584540c23e65d0d41cdd50514823f6454d2197d8d524425d6395110a718d42d023e64944219798f548865d63d52218f592534826d6295110c7550434c23f6454b318fd9151ccb1c5450d31c714c425063e64150328f592528c65e650c9319b588540c2756194d208f596540c67a6014c219d987530825e63150319718d544831c54d4d1097d8d544c69c6350842c795153c863e64d4e109718d544423d64943319d587548ca6e62d52319718d544869c6350a41c715053442e765484219ed95300c26f62551108f990504863d64141218f590538871e5494f219758e510863d64948218f590530425e639442197997434c25f63544409b189544423f6550c408f593538871e548ca30c7551310c71f5414d108f59053c825d6394720c7952530423e6414f20c7950328c23e6414d21c7d53534432e54548109718d54c831d53d04418f992524431c5414d209718d528425e6315221a7590310c25e6514d109d996214423d64d4c109758c525031c5490d328f992544c66e62148109798e534431d63952309dd85524431d5494e21c758c544c63f6454f209758c528431d54ccb3097997314c25f63547428f596540823e64145309d185534829c6350540c7151430c23f645483097d8d54482756115020d9547200829c6250c439dd95411065f63546208f593538831d54d0c318f191534863d6414d2197d95430c23d64949109bd954210a3f6454231a719131cc31d43544438fd95401023d64943328f59053c863d6590c42a758c425065c6354b419798c528431d5454c109798c515029c6150c439798f548431f5410e32c7553320cb6451485208f19153c425f63553209798c540cb1c53d0d41d914a214425e6590d31d954b100429f6050c438f992534827b6544010c754d41d029d64cc23097596530429d6490c4397d95300c31d54cc4318f590520425d6315121c7d53534823c6454732cd951510831d53d0842a758c419029c644c530cd15351482e462440108f990520423e6510d408f592530c2e460484219798f54043355454420d394d520426d62d5010
  | 1 => 0x431d5454e219d594210423d6494720c7d50534826d6294d1097195434c65d63d52109758c54c823f6550c439b98854cc71d54d0c32c754c43d03645248710d394e520423d6414a108f990528433754d45209718d540863e6415031c714e415071d5410c319e18154486766115030c755153c865d6594c20c718d540ca5d63148109b98b530431e53106408f997415025d6395210c7152434c71c53d0d429798e529069d64cc0309b189534425f654c4319798e544425d63946429bd89544c34f53149109d986534823e6494c30a7992304c31e548c6308f990524c31e5454c108f593530831c5350d42c7951538873454145209758e50d0a5e63150109798c540871e5450e308f592538825f654c831d9485500865d6590c30a759032cc63c6454910a7590320c25f654c83297d8d540871f5410e319798f54c871e540c630d314c524431e5490e308f992544827b65480208f592518ca5e63141219d1855448277654c431c754d421063e6494a319d98454cca3c64542318f993520425d63943418fd91508cb5453d45209d185544c27661951209798c54c426e62d501097594430ca3e64951329dd95210872c54d49108f99352c423f6454c2197d8d544ca9c63507409dd8553483655188420d5d4c514825e63952208f592534426e62951109758f548826f6548421c7553320c74d53548108f990540432d54548109758c54c87645248510c755253c871d544cb309ed81534865e63148109798c540831d544c8329758e520865d63d53219758c548872f54d49109758e524425e63d50208f593538431d5494c2097994534825c6550d329b994524426d65884209798e50d0b1e5494e218fd91500865e63d48108f99252c42e56288421d9d48218423c6454f20c755253043645284110a719132cc25f63540218f19152cc764518812097d954310e5e65cc9308f99250cca7661d50209758e544c23e6494720c7150324c63e6510941c750e5010e3e6494e109d98453082786054d21a7191324c31c5450f319798e52c425c63542428f992538825c63540218f596431065f63548408f191528425c63548409798e520866e6215010d594e510825c63546209758c54c431e5494c208f191534423e65151318f59352c431c5450d32c718d54cc25d63d48109e580530871d5390c4297596310c23e64d4e209e58054087565354420c754d4210a5d6314121a718d421066e6294d109b58b548c63c64542328f992520869c644c8319758e544823e65151329d597210423e6414f109718d54c431c63550319bd95200826d6215331d9584524431e5310a409e980540863d6414c20c794f439023d6590840cb150524431d5350b40c7153534826e62150308fd954210b646154810d9549100425d63145409798f540c25d63d50108f990538863c64540219b59
  | 2 => 0x4500080102823028770300301439000247815a07059000e807817274230001103c020700c0000201c0a224160f5bd010010ac77004020303000036010000940d0240106486000074a403031a70181331c000340800c3c1080f15c000110e088150a0120009c0fc000000200403048071a4c6044200b04a0e00800c17000090301f02c19224154500002c1c110350140100000044231ac0306c4505c090380a000000083d0500d2f40c028095c80043ce3008530581202087304e91381604c0f0180e0cc010088b0201801431024020443c06c06005bd0040b0000800820000000180204a5c6354440a758c42d071d5310c418f99250cc71d5454c208f592538423d65950109ed95401031c5390941a7191320ca9d63d024097594430c67661150209718d51d0a7561153329798e50d071d53d0b408f59053c431c5350d41c755043cc35753d4520c715143cca3d64944218f997425023e64940309ed81544865f6354b418f990530863d6595032a7191310c71e53d0240d9548210429d640ca308f992518ca3c6454c218fd91524431d53d07408f9974350b1c548c531cd552510832e5494810d3d4f524433654944209718d524425d65d0c318f990540823e6494d109798e548425d63d4b108f191510c23e64d4c20b9185200834c53d49108f99353c865d63150109798e51c827761551209798e524425e6315320d9d95210863e64d4e218f990530426d62d4c10c7550430ca6e65c85209d195214431d544c730a758c429026c625513097d8d5090b6551480208f992544425f63542419d586544825e63149408fd915348277615513097597430ca5e63951209718d509071e5390640d554d510825d6315021c7951530829d631084097d8d54c425f63551218fd91528425e63d52209798c54c869d63d0040c755343cc29e6390140c7953308c23d65904408fd91510c25d63952208f191518831d54cc7308fd91518829c6350940d9147214825d6394a418f59353c86776544010a7590324c65e6510d30c714e4250b1d5310c42d554e51082796584010c750d5210f1f6550c439758f540823f6454f109d984520429f6550c438f993530423c64548308f994544
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xc003c00000400000e020000001431c94354843a36e0a1ca021d147150d5110e0e3b2a899063071d9544cb3083aec2a06498c6476549100420e3b2a898e61071d9544c431a18e4aa0869851571151430c287396a821c63071d9544c832a2ce3aa087195157115143cca0ebb4a998461451c55410d30a1ae42a28798c1d76950318c20ebb4a819461435c85450c30
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s2K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/257+packedAt s2K5 (17982+(h % 257)*10) 10) % 666)
  | 4 => 2*((h/183+packedAt s2K4 (20938+(h % 183)*10) 10) % 551)
  | 3 => 2*((h/21+packedAt s2K3 (1029+(h % 21)*5) 5) % 21)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffc1fffffff03ffff83ffc1fffffcf8f1ff
  | 1 => 0xf03fffe07ffc3ffc1f07fc3ffe1fc0ff473e73
  | 3 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8104044410480000a5090044802254501850a5
  | 1 => 0x248a48832490612c0a42a429521482a9432652
  | 3 => 0x429291090d2206554084ca8265412a0a858b18
  | 4 => 0x6b2ce252483aab9a73d06223b9980c33e80de0
  | 5 => 0x8c30c39c71c333e39ce77330311030c3f6f000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_39077
namespace PEqualNP.Outside.L_meta_39077
open PEqualNP.Outside.L_meta_39077.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x4c00804010042df43bf41bc40be43dc30de30bf42dd31dc43dd329c43bd42bc43be40df32bd41df31
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x80000080000000601000001800247151318ea90871e548c23aa221c714d428e2a6631c540c238a8994794e408f280871e5390e38a9994714d41
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x148558454cca0d621533183588540c2156115030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | 2 => packedAt s3K2 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/12+packedAt s3K4 (272+(h % 12)*5) 5) % 17)
  | 3 => 2*((h/32+packedAt s3K3 (351+(h % 32)*4) 4) % 13)
  | 2 => 2*((h/8+packedAt s3K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff07fffc1ff83ffff07ff07ff07fe7cf3cf
  | 1 => 0xf07fff83fffe1ffc1f07f87ff87ff83fa33cf3
  | 2 => 0xff83fffc1fffe1ffe007ff87ff87ffc1c3cf3c
  | 4 => 0x3ffffe00001fffff80007fff80001fc0fc0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8108111084820000a5090089008902940c5145
  | 1 => 0x24112209091030940a42485248525028a12492
  | 2 => 0x4222442052210329408495049504a501428a28
  | 4 => 0x6b5b894a43b555ce73d0c447e660318df40fc0
  | 5 => 0x8c630e739c3999f39ce7e660c440c631fbf000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_39077
namespace PEqualNP.Outside.L_meta_39077
open PEqualNP.Outside.L_meta_39077.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x8887002aca0001de0015000804800c2381200000fd43bd40fe21ff21fe30fc40fd42fd30ff10fe43ff43fc32fd21ff40fd32fc43ff31ff41fc41fe31fe32fe42fc10fd40ff30bc43fd10fe41fc42fd20fe10fd41fd31fc31ff20ff42be43ff32fc20fc21bf40fc30fe40fe20
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe617c530827ca8106714d40bea9a41df32cc7f681205f54f40dea00617f548827ca621dfd5121dfa06217d54442fea6a06f94643dea0a817d5390afca7a16f50b419f29c87be32d03de40105f15230be2a4437e538437a63a05fd4520de2a2617d520c7be64195f54642bf29e437e528c2faa3207d50441fc90221bf5010fbe6218efd0f40bea9a21be43502faa2185f54a21dfa1085fb10843ea42885f94a31beaa4817f5384378a898dfd5010bf29861bf400c37887986f90f40fb880217c54cc37887214f15121df98a81bc43506faa920df94842de19681f641106faa890df14940dfa1a817d52cc7788690df14132ee21c61bf31d02fca120df94342fa98a217f52842faa1a0df55210bf288837d538c6fca8985f15310df90a81bc43906fea7905f15010beaa063ee4210b7c8698db94810bea86877e518837a80905f14d42de2a2653e548cbf460185f95321bf29e213e54087788698ef54243bfaa6419c43ccb78a890df54e41df21c817e52cc6f8a818ef10841bf28c617c544c3f480204fd5121be28a417f53c877ca421df14141bf2a243df324c77887a0ef14443dea80877e54442faa010df54c42dfa02417c50487ba60185f94e41df2a461df438c2f8a7105f55230bf286877e548437c85a06f14b40dfa9a81df32cc3f260186f94740bea88877d50906faa3a1df54e32de21a65bd53d037aa2a04f55240af298413e541037c86206f10e32df218437f524c6fca520df54b409faa2617e50903788610df54b43bf28c43bc43102daa4084f15330bea8443bd548c6faa5087bcc9329eaa421bd40cc2faa921df14d41f799465f920842faa11977cc530bfa8a617e54cc2faa5a0df54043de2a661be42906fca610dfd4c10bf288417e501077c84a06fd4140ef984617c524c77a42a06710e30eea9821be43c82faa121df94e21fb10a21ef208837c86105f94743df20a817c5350378a7a06f48740bfa9a837e520c2fea0995f55021de21841dd310c6faa690dfd5232bf2a665bc43c837ca8106f90740bfaa2217e508837ea7a05f94820bf29821bc51d037c82a0ef4c540dfa9487be43886faa7907ecc230beaa0657e5410f7aa221ef50c43efa1e65bc43886fca210ef95021bf29087de5390bec628877cca329eaa4617e5290afca0215fd41429eaa0433e54842f8a9996fd0540bea8e653f544cbbe86996fd47409ea8087ee320cb7c8718df54032bea8e417e524437ca4a05f54321bea8865bf41d037a64a06f10e31bf29e837551082faa3197e88020fd904417d544837c64a05f94e20bfa9283bc43903bca720f710f31bfaa0417e54c42fca5a1cf94f40bea9c81bf419077c86a1dfd4d10df21c83de4310f7a65a04f15130de10a81dc430c2fca0206fd0040df2a4653d5090ff660985f95231bf2a0857c504c77ca8086f08740
  | 1 => 0xc53c82f8a8106fd4940bfaa241bf544c2f8a2a1fd84110f719241be53502fca6105f94231bf28065dd530837c86996f50110bf28061dd32cc7ec63886f50220bea8e617c54c87be8698ef10e30dfa0221ef4250b7c87087710d32de21281ed324837a8220fe94021dfa04417d538837c8420f754e42bf28021bc43842fea710ef107409f2a0217d50cc77ca5a05d94430df28a81ef21086faa7885f94742bf28c81bc43d02faa5185f94f40be2a421dd320cafea9085f54a40fba0a83dd530877a83a05f95030be2a4637f52042fea918efcc940dfa8a81be43506f8a8906fccb40dfaa6617f5150b7aa8085f94031be2a0617e548cafca2215f14e10de280877d548cbea20086f95030df21821bc42d03388698de54021bea9c21fa20842fca3215f54810f690041bc315037886987dcc631f790e41ed32c837c86986f10d20bf2a4437651082faa3a17dd0641bf284217f538837e8220ef10c10df21a85bc42907da4210df55231de18e817f5250ebaa720e7d4d40bfa9e21ef21887ba63985f94720de21a857f544c6f8a0a17e50040deaa0617d544cafaa1215f54440b7290617d540c3ea4210efd5121bea8e81bd54082fea2a07794c21dfaa2659c434cafea0a1ef10f31bfa92217d53082fca218df95120bea94637e5310bba8621df94341bf2a641ed4210afaa3187754e41be2a065f9100437a81186f14843ef99261e521086f8a4086f90f109eaa465dd324c7ba659877cc631bea8841bc5090fda43905fd5230af29843bd40843dca4085f15132fd902417e52102fca198ef10f10bf28821f92008376a0a05fd4b109f2a0617f540c2f8a2a16fd0210bf28c875c53502fca7217b8cb20bf298837c544c6faa610fb88521bf296613d548c6faa420df55010df29e817e5390fbe86a1cfd5131bf29421bd5484278a8996f90c30df2a4635e53042faa4886f90f41bfaa643be434877e81986fd0130de218617e54082fca3195f15232bfaa665dc53502fca010efd0010bf29887be5310ef8a7887ec4110df218657e50ccafca5195f94230dea12833d540c37ea321ef90f31bf29863bd400437a80985fd5032ef18a63bf5210efea998df15220bfa8283be54882fca810fe54021bf284657e51cc37aa9184714d40bf29065ed520c2fca5205f54c10ee21e657c525077886197b88120df212857e54cc6faa710df95041dea00817c54086faa020ef50b40df2a4217e544caf8a890df15320dfa1c877d54c43bc64995f94821bfaa2657c544437a81885f54620dfa1887bc52503daa4085fd4121deaa4417d52cc3de8521778c130bea9441bf52d02fca6207e84010df21a41be43c8678a898ef54740de29487be4390af4a010ef10d40fb10843f710843788790df95040dfaa2633d54042daa4185f55332dfa88877c54cc7eca2105fd5130df21
  | 2 => 0x417080c707401784010740e0140209c01004010180300c0300c372bc0000400250010002909822088000001507827010000002d00001078020028d03043000a2015800000c04c190000d2c80e00002009b90000e17c3b1602100c0901cae0002d04c020e61000c11000270704e240000000604c04008320f80200009008050181101c450f01800598008e90240402d640140000005045b336408000140b00000160000030341500c000000448c00059440280576c4200c0200c0a12401004301ee1b03c2103c0a00c050064e0180603c0300a6e00040000170140300400070004800e0900c0bc0a03c010300a04c670000a000000640e68001014020040700000008790011551800061550015300037004a80001d6182149c04004490200023406038030281b0216f0100b04402120994f8c6004c40180aaa1eb2680a00c000388502e66920000040f038000541d05c3e3c01100d250002800192000008a0720000801402afc1600c000140400a7aa9105f94242bf28887bc43d0b7c87a14f14d40bf284877f53082faa8105f54f42aea9841f6310c6f8a5085f14540bea9e43bd40c837a84216f94443dea96817d52c42f8a610df14d20bf29a217d544c37c87197d48710de29a817d544c6faa1a16f94043df29487df430c2f8a29877d0e43bfa9a857e53486fea910df95131bf29c817d50ccafca021dfd4532de28c87bd40082faa4205f94831fa98e215e5390b7c42a06fd0320efa1e637f5150fba62985f54f41bf2a461bd548cb7c8620df14d21faa88617e510cafaa9106fd0020f790a419e5310efaa0216f88740bf28643bc415037887106f94243aea98437f504c6fea4a06f90e20df21a217f53086fca0106f10d10ce218617d5190efea818df95220ef298417d53107788620df55221bea8c217e51ccb7aa810ef8c540bf28c83bd5190f7aa4a05f14930bea8063bd5290ef8a4a1df94f20df20281bd435037887995f94b40bfaa621dd324c2fca5a0dfd4d20df18e819c43cc6fca521fe88110beaa643be43ccbee4290ef54d40fb98a637c534437e85a05754c10dfa84877d5290e7aa8107d4c431dea90877f524c2fca61977cc030bfaa6617d5210f7c86215f14143dfa0481f6510c37a87a05f95010bf29621bf42502f8a2995f95031de21885ed21483be63986f14540be29621df53503ee4310ef10c31bfaa0437e52106fca3a06fc8740bf28443be430c77a84a07ed0140bea8885bc32502fca81957d4d409f2a4617c52442fca318df94440dfa1485bf42506eaa2185f94d20faa8841dc434c6faa9214f95231be29e437d529067ea9987d88710ef298213e54882fca4087b94830beaa6617f534877e85a0fb4c832af29c837d538c2faa4185f14e21dfa04617d508c6faa6206f90e30bf288615d5390af8a6085f55331beaa6417
  | 3 => 0x80400c02004000080012408024040100000c030003415dc31d00001
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1520c63f6454432e9484215029c6354940c7d92530423d64940108f994215029e6390c30c7151324c7355494430cb949400439443cc531c7d91530429d6010c30d8485500863d6494332cd94540083a52108740f8486500869e6394d4097d8d544c27a6015032ce58054cc23e63950109d584538831d63d5121ae58353d023d6510c10c7952530427965840108f992510c65d6594c21cd54740082b960d4b408f993530423f6454c208fd95315023d6414a10c714e315023c6454f20c7152304c34e53548109718d544425e63d50108f99251cc31e5310f208f99252cc23d64943319798c540434d5394810ab9885110f1f5310e208f18d54087e12154021f194d21086b96010e10c7953318c66d62141318f583544ca3f6454f219758f540863d64940329dd8554482746154d208fd81548cae76548421a7994434ca7561150328fd91538425f654c4318f19151cc25e63d50219798c53083665294430d9149214423e6315130d9549100431e5310f40c714e415026d62d50109718d524423d64942218f99052442b96010d208f594430838c434c9209798e51d023e64940108f18d54042b96094d408f997404c31e6510c30c754d400829e648c5319bd95200829c63501108f990530431c5310d108f59352043655294430ab5884310a3d64d4f218f990538436552c40108f596430423d6494b30cb949400c31d5390c21e510d510c2766115030c714e325023e6494021cb951520426d62150309d584530823f6454910ce10e500863e64148108f59052c423d6590e20d5545300c26e6214c109ed95100423e64947329798c524431c43d4931c714f425023e6414131c794c43d0a3e6495121cb549400c274654c510dac85500871c53d05409758c540431e5310c408f590530429c6355210c7d84535031e5310f10ae580315023f6454c10a718d40c827561d4c20cd947400832e52d00108f994544cb1e63d5330d9547200823f6510c30a718d40c423d6494732c7953328cb1e5390c208f596421069e6394540a798f544863d6414910ad185525031e6510d31c714d415023d6494031c794c43886b56110c419d195214425f6355120c714e525023d6510e20c754c430866e62d4c109798f520431c53105408f191520c65d6314b10c794d400431d5454c108f583544c7b14044010e398843ccb676548421a798e425023e64141329798c540831c5350940a7191300c29e6390a418f580544872e52d0030cdd465190e6d6215031c7192530871c54cc730e990d21086b960147409758c540863e65d0d40c714f505033654944308f994544865d6314121c714e405031d5314d40a758e52d031e5494c21ce10d500871d53d0020da54a100423e64940208f594430863c6454f219758f540833643544309ed95200835551cc030c758f544caad6214043
  | 1 => 0xc31d6510c30c754c431065f6355110a798f40cc31c5310940cd551510834f43548308f592500823f6454e2097d8d548423c63552108f195215029c64cc2309d987540827661d4c20e610e300c26f654c832d9485500863c654c940a798e52d031c5394540ab98b5190e3c6590d219d984538831f5310d108f993530873643944308f993528423e631512197d8d548823e63d5121c7580535027960d50218f990504863e6515130cb10e520c26d62d4c10c7d92530863c6454d10ab9885090f1d5494c108f191534871c6214d408f191538831d6114d40c794d400831f5310d2097997434cab76154940c718d548421c6355210a718d408c31c544c9309e181534863d64141319e98053087355150030a7193300c37151480208f19152c42b96010f30cb10d520c25c63552108f582540863f6590c30c7153324c61e63d5121dc88550087966110f31ad9875290e3e6590d30cb952520431d5310f409b189544431c6494c109e19520442bb60549408f98e540863c6454e10d654d50086ce62d0d32e510d31c423d64d4d1097596530423d64d4c10cd952510825e63d51218f992544c6766115032c714c515023f6454d108fd9153c423f654c7408f590520426e62d53319d987540c30c43548309798c52c43355150020e9951210863f6454f20c794c430423e6414c20c759443cca5e63d5031ab9885010e3e6590d31c710d528c23e63952108f59631d026d62d50308fd8154043a764484218f590530833a6494021a758c21d03355494420d310d520c29d6294c439b988540429c6350030cb551520423d65d0020a7d8d525023c6454d20ae9805210f4d53480209798c53086ba6014443c7d4f505034c524c931c714e4350a3d64d4e20c714e425037121540219798e52d023c654c5408fd96438425d63d5010e510d314429c644cb31ce90d50086b960d47408f994434cb3443944308f592534863d64d4f10ce951401023c6355020c710e500c23e64d4d10cb952520c31e6510f31ae58052d025e63150218f992500cab66114243c794e439063d658cb40c754c43c831c530c540e6d4f50502b96094540c754c438865e6394b41cb10d520429d6390b40ab98a4350b1e5310f41c7951530832e5454830c794f400829e6394740ae580325023d6015132c7d50434c71e6214d40a7580438c26f62551109d98454083a55448421c7184535029d6390740ad5845010f9a434c0308fd96430871e63153309bd89534431c6454c209758c540831d5454c20c7d88535027765484218f597400423e64d4810ae582430c23d6414121a7191324c71d5390c10ba181324833551d003097997434c6ad62142439e980540c71e5310c428f596431023e6495132c7d4c438431e5390c21e358843ccb1f6414d40a718d400439a6010c308fd9541106b960144438fd9
  | 2 => 0x6494c209d984504cb574354430c710e50cc65d6314a109b988504c63d60d51218f59353c823f6510c20c7d8d548825d6394742a7580434cb1d5310d218f191510cb665254430aed81515023e6494031e6501300c31c54cc930cb90d520c31c5354540cb5485210f3443544309bd954210b5553544208f19152cc31e6394c43d354b300c2776544010ab189515031d5494c218fd954310f6552544308f992520ca3e64145208f592500863e6415030c794c43486796015021cd947400c25e63d5320ae580215023d64d4c20ae58043443144354430aed81535023e64943318f19151c823d6414e108f59353483344354420c7588535023f6454e218f99054042766114c20e310d32c825e63145208f99632d031d63d5131ad986435063e64943328f993534831c54cc5309e983530863e6508740a798e415031e5390c108fd91534871c6494c20a798e434ca6d659481097d95320ca3e65d0941b5987434c69c6350040c754d400423c6355220d510d510c25d6394b418f99052c423c6454c20a798c215023f6510e20d694d500872d54948108f992500c31e5454c218f596540863d6595020e390d320cb1f6014d409e58353086ba60087408f59250c863d64942329b98b540423e6495130c714e215023c654c7408f582548c75a5394021c710d518c23e6590d328f19443487944394430ce90e500871c5314940c7151314c29e63907408f19521d029e63d01309d584504cab96014f40c794e439031c6454c218fd9153483a940480209ed95401023d6590c3097d954310f956110f31a758e415031c53d0d40cb551520c31c43544308fd95400831d5410e308fd81548c71e53d06418fd9521d031e5494c208f590504cb655148020a7992324ca9c6355220d554e51082b96014843abd89515023c6454e21d914921c43a44348421c718d540c25d63148108f990530865d63d53218f580544c71d5494c20c7d50434ca9c6350120a718d408425d63d4810cb90d520432c4394810a798e415066e6215031c710d520c26d62d53319d98754cca5e6314810cd10e510831d5310c20c710f514ca9d6390940da549100423e658c740ae58021d023e658c540e310f324cb1d5454c219d984530423e64942328f990528427b654c030c7553430c2b96010e208fd9152cc23d6508740cd951510825d63d5310cb552520c2f0604c5108718d548829d6194c438fd9152c426e62d5030d394e520425d63d53208f581540423f654cb40ae980315031d53d0010c7d8d548423c6454f10c754c53d025e63d50208f992534871c53485408f994434863d64948329718d54883e12148110c710d52cc67a6014810a7994434c69d6308540d654e500871d5310c42c754c43c8677654c431a7994535027561150209dd95411063e6510d31a798c21d029c6354540e6580430
  | 3 => 0x9409e580530869d6510e30ce592500869c6350130c794c430873643544209718d544823f64547308f99353c431e5310f219dd8553482b96010c30c714f32502b66114843cb549400431c534c5408fd9151c831f6454c218fd91530863d6494b318f594438432d52d0030f154d210869c6350220c794f4290ae56288421c714c438427561d5030c7d92539063c654cb40c714c438823e6590d218f594430c2766114810c710e50cca3d64d4c219b988520431c53d4540ad5875290e3f6550040ce591500869d63947408f582548ca3e6414e208f593538871e5310c41ae58243cc23e64d4f20c7994535031c43547328f592500c36451485208f993538871e6114d408f98e540826e6215030c7d8d548c29e6390841ce952500871c6454c108fd96438826d6214c10c710c504c71c53d49408f596540c31c53085408f596540423e6494221a798e4250a9c635033087594430c2996010c30c794f400431e63d51219758c514826c654c920c794c430c65d6394740d554d100438c4354830ae582525029e6390b40c714c434823e64d4e10c7d9153083565394420cb90e520425e6314a10b6580430c23f6550010c7994434ca5d6510c30d354f200825e6394742a758043cc63e64d4e20e310e520c23f6510c218f996325031e6510f328f98e54882d4614c9319b189534423f6510c108fd94438423d6414c21ce991500871f6494e42c794c430cab56114243c714e435063f6548540c714d525025d6594c208fd954210a9e6390d318f18c544c32f5294a43cd90e510823d65d00309ed8153487692154021ab58b5190e6e6214c208f992508c7395494021c794e429067561d5020cd945400c35553c40109758f54887a46448421a718d400829d63945408f99252cc65d6394b40e590d310c6b661140438f99250c874d524c030a758043ccb3a54540218fd95400c23d64d4a109b988538431e5454c10c7d4c435031d5310f109798f54c877151880208f195404c279601503197d95300c32d52d0010a7580434c66d6214e10d354d520425e63d5221c715132cc23d6590c208f994434c31c534c9408f993530823d6494431cd551510c26f65484219758f544869d63949409798c50486ba60085408fd9643082b561148438f596315031c5390d409e983540871c53c8540c718d548829f63545409d185544831e5310c20c714c325031d5310e428f191524425f6354910c754e430823d64942318f99353c865d63149109b588540431d5310e418f191530433551144439e980540865e63d53109798c530427561150309798f540ca3e64150218f590514831c43141328f593534863d6590c21cd951510c23d6508540ce551500871e5390e428f59251cc23e65151318fd96430432e43948308f990540823c6454c21ae98032502ad62144438f993534871f
  | 4 => 0x1307c180100b000000800507400234000000901414008340200f6a0060685306019000000009c04c0006805018011a8010086100000038000041801c0300c2b0100018405260260b400120170040002c200005b02c001640026c020000001400004330040001458a0c29048050001402811314020b80014c23151a10688f04c121580d00056004030880a038050601d00409008000241a04006014020002024c5b00226008010200007c02014000080101027028010000d1b4780100400c03088001682700c040a4000a400000390142f008010000200d0e0143d00416010ca3580002829008001e85f0401616d5a01000054030001c04c4d1581003c0015c1202000035343e01d0282e0005b00c390140300055038070180300001000080a407021320141e02c9701800014000540002c011ac0101831070231d400000020000317039000000003a000230a401060000d4032cc6901000024000045d00403008150341500000000d90b804030570205d00821000970240104d2200446000ae00c0200404600c00016002802014000080000800004000100501c0012c0202448034000ac220000804023000000000803402040630284e12c00004000040d040182a0000109b3671c53cc540d594d510827561d5332c754c43042796015032c715332cc29e63949408f593538433960d5330c714d435023f6055021a79825310e3d6590e108f596325039853d4140c794c429071d6510f31c715131cc31d6510e308f590538823f654c
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x115195c001b0f480c0000000301110e020012242b18121117000c050401016e74060a0f1b002a57021d042302050929183b020b10000a1d5004001200a2ae229887105197010d520c28c39ac9280438314f6254540d4242b0043a0709535012008306b10c429a81075d85308540a52e021aa4187097010d520c20f39ec8a9621261d9404c030e22a6a02200851970188535030d31ac02a661a410c604c510838eab1c84a060c63549400c38221aa4a8861071cd6508540c28c8a8a601861853580438833032a42902218510d6114132e46e890aa010f4153485500860e39ac9284438514f615494094ced21a4210f20434855008782aa2a690843435c86114d40a30e6b22a010c1c7558c215028b38ec929c85071d95350020838eab1c82a041c73592500860fbaac021861c85454048020e0886a94a218618539803150286b94ca21861435c04354830e24e021aa2185917010d510c30a31aa2a0061461c15310d21e22a2a02601841c73593528428ab8cca21861c85912154021c18c8a9660185157010d510c3063288699241495d44348421838e6b00a890ea121580215020e39ac0aa021079cf6548540a62e021aa21850e72d92539060e3b4a6a0021c114d2108540c30a6b0087085517010d510c2c4b8086a9061465c04354430a1ce5b20a6a060c63949400c2923aa4210a81071cd60950219c2e430262887117010d510c286b96c829a81c85512154021c62a2b00a221e0c43588504c744218c0992418614e6008540934ed21a601841c735925004390a928088021619cf644842183aed2988690ce171181324838221ca4a88618614d6010d20a1ae53288798d16711885350288b8086a88618518e5150030c52a4b00a421d0d7214c438428cb808628263465c04314132e84a690aa010c39701944348706322a498061c81d12154021838eca9a800852671d4a5290f12a92c229087855846114d40a2ce3b20a6a060c6354940043912a242a8043439c86114d40c18c7292800861853580215039132242a8043641cd4044010936eab00861841e73d9521d030a3288698a21079cf6454720838e6b24a0105897010d324820e3b4a6a0041499cb5194643a2ae2310a6a061b75580430c38538086a9061645c04394430c28c8a8e601872243485500870a298c2a9281625c04394830a12e021aa4185497010d520c312b12a2288878614d6010d10c28c728a80106185398032502c439a80900418314c6254540a2ae3328879961463545400828cb80c229a8107dd85308540b22e021a628870952501300c28ab8ec829a81071cd6494321
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x4218000280008cc000000038120b018010d5294430920875912154021a118114d6010e20c10655c0434c510b0283dd12154021a098010d6214131c09625c06214d40b00835912154021d00735454048020c08655c0434c9209108754d4044010c05625c46214d40c11615c06114d40e00534856008540905859cf6448421c80435c4604c920d00735494044010b018010d5254430b018010e52544309228790d2154021a058614d21085409088754d4048020a098214d6010e10c05725846114d40c80435c8604c510a118010d6114132
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 802
  | 4 => 883
  | 3 => 144
  | 2 => 26
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
  | 6 => 2*((h/28+packedAt s4K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/316+packedAt s4K5 (21654+(h % 316)*10) 10) % 802)
  | 4 => 2*((h/364+packedAt s4K4 (33554+(h % 364)*10) 10) % 883)
  | 3 => 2*((h/62+packedAt s4K3 (7056+(h % 62)*8) 8) % 144)
  | 2 => 2*((h/22+packedAt s4K2 (1560+(h % 22)*5) 5) % 26)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3fe0fff0ffffe3f078f1f8ff1fff83fc0cf3cf
  | 1 => 0xc1ff0fff07c7fc7f80fe3f1fe383fc3c733d33
  | 2 => 0x1fff0fff807ff8fff003fe3fc03ffc383ce3c
  | 3 => 0xfe0000fffff8000fffffc003fffc0003fc0fc0
  | 5 => 0xffffff000000000ffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x280010210104001020482404a08110045045
  | 1 => 0x14424222120a40828052110921092828312512
  | 2 => 0xa8842444409480152900224248125281828a28
  | 3 => 0x8c16aa889480c929ca9480039258188ad80f80
  | 5 => 0x3118cc0ee727124e74e93c90006063336ff000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfee8fee8eae8eae8fee8fee8eae8eae8fee8fee8eae8eae8fee8fee8eae8eae8fee8fee8eae8eae8fee8fee8eae8eae8fee8fee8eae8eae8fee8fee8eae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_39077
namespace PEqualNP.Outside.L_meta_39077
open PEqualNP.Outside.L_meta_39077.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x1181020741000000141041104201042002001001fc21fe21fc30fd30fc42bf40fd40fe42ff10fe41ff42fc32fe30fd32fc41ff21fe31fc10fd31bd40fe32ff30ff31fd10ff43ff41be43fd42fc31bc43fe10fd20ff40fd41ff20fd21ff32fe40fc43fd43fc40fe43fe20fc20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x4637d52c42faa120f754c10de98e817d538cafca710ef90c41bea9c853c54cc37e42a0774c930bf29687ef21482faa2186fd03309eaa0617f544c37887a05f94a32dfa8e81f641106f8a910df95041bf28e617c54c82fca518df94630bf29c81be43082faa3985f14d10be294217d53443be8721cf95040be28265bf515027ca8186fd5132dea88877f54c82fca198ef54f40df98a81df4350efca9195f94c409eaa043bd525037a81905f54610bf28863bc434c37e81207750c43bf280433d540437c86a1df54a30ef298417e53106fca610df55242be29e217f540c6f8a8885f95043bf29a217d53902fca220df54b30bf284877f54042faa898efd0f40bf280837d52d02fca890df54041df2a4417c5050afca1215f95220be28243bd51d02daa4185f94842bfaa661be43d0afaa9885f94c30bb28841de53043be6598dfd5332be29c217d50c877a80086f90f40df21c65bc43483f2410877cca32bfaa4657e518c6faa2196f48540ee980613d548cafca8995f55331bf29c877c5448278a8996f50842f690a41ef324cafaa9996f54843bf284617c505067ca918df54831dfa0a817f504cb78a8996f55230bfaa421ef4250bde41107b90842bea9c83e521086fca1196f10e309faa2439c43cc6f8a9885f54a40bf2a0657d5190afca1a0ef10a41fca00817d52906fea9887bd0a42ee98a61bf401037883a06fd0020df280877d548c37864a05fd5220f7192417d544cb7c86905f14d42de21c417f52c437c62a05f54e31bf2a661fb405037c86986f8c940dea1e81fb104437a64a05f94421be29283ed3248378a890df54a31de21c21fa208437aa321ef14f40bf288217d520c27aa121db94810be292877c514c2faa021ef952309eaa4417e54442f8a810dfd4943f790843f721486faa7a06f50110dfa16817a50086fca5086710d329faa265f610442fca6106f50941dea12817f514837c87107e54021fb288417e53c877ca6a05f14e20bf28081be41506fca421df94c32df29281bf544c77ca221cf14d40bfaa463f521086fea4885f95230fb98c637d5290efca7906f50b41df20a81df308c3be64196f90940ef298433c544c77862a05f55321df21c61dd324c7b887186fd4a43bea9e417e51ccafaa9985f54740df21c215f535027aa8105f94f41aea9821f6510c2f8a6085f55032de218857d51d0ef8a690df15210dfa0241ef21c82fca7215f94420be2a4657e5310efea498df94831bfa9261bd400c2faa610ef10f32de21e63bf404c2fca018ef94a43bfa9283bc43c86faa7085f94810dfa14857c52c43f640905f15331de218437d51ccafaa6205f95221f6a90217e511027ca7a07ec8220be28287be515037886a0f7cc431bf2a021df438c2f8a8187b48421ee21e63be548cafea0a17794e419eaa4813f544c6b8a6a05fd4f21
  | 1 => 0xe500c37e84a0de54021dfa1281fb40902fca5186f10e31bf29e85bf21d02faa8106f10c30de21c837e51d03eaa2105f94b31deaa441be540437ea0a06f14940bfa9c21bc4350b7886196f48740fb98a63df43cc6daa4085f94010f710a437e50082fca021df54243fb18a217c52442f8a6906f90d32f790c437e51d0afaa790df95320bfa92817e5010afea090df55121df28487fb304c37e81905fd5132aea9c857c5150efaa0195f94332f6990657f504c77c87a0df54841fd18061dc434ca7ca9107b94830df98e81bd4310f788618f754c20dfa92813f54cc3bc6298df54221bea8841bf41106fca1a1ef90e41be292617f54442f8a7906f90e31bf288653d548c2fca521ef95020df218637e5110fee20085f54910be29841be43442fca2215f94a42df21a857f514cbba6218fd48710de196815e53086fca6086f50120fb18863bf40042fea7885fd4d42ef992617e52cc3dc64196f90c32bfa9841bf5090fbaa720ef14643be2a6437d508c77ca5a07ecc230de99681bf52d02fea60877d0d32deaa0217d518c3ea8220fd54430df21c857e53d02fca520df94720fd28043bd51502dca4185f95310de21c437e540c77887985f94621bea90217e544c7ea62885f94231dea8087bd40842fea898ef50b40dea04417d50cc7f621086f10f10bfaa6637d53486fca410d794e42dfa9a817c544cafca810ef502309f29c87be43cc2faa6904f54043ee21861bc544c37e83a07d88510deaa4217f52043ba63985f94e41fb18e217d53d0afea2a07e48020beaa483bc43902fca1a16f90841bfa82877d5310bbca7215f54332df196817e50906faa9205f552109f29887bf40442faa8907b88120de21883df434c7be86186f90e40be28a857d51102fea0a0cf95230ef98a61bf4310efca990f710d31df18e817d530837c8698e710e30df20e81bc53502f8a710ef90e21df21e21be5310efaa9907d4c431de29487bf325037ca9086f94643dea9681bf5110efca9085f94820bf290617c53c86fca9995f54031aea9c83be42d02f8a898df95042deaa463bf54486bca6105f15121efa9a817e529037ea8987bc8020bfa8a87ee520437aa8186f10940df290877e530c6fca321fe44010be290217f52842f8a2906f95021bea98837c540cafca1086f14043bea9c43bd548cafaa7a0ef0c740de218417e53882fca3215f94b10bfa9a43be21d02faa1196f542439f2a021be540c2fca8906fd0030bf29681be548c7b8a6a05f54a21bfaa065fa2008378a5a05f15130dfa1c879c43ccb7842a05f55221df21881bd5290efca690ef153308e29a81ed520c3bc8621ef14243dfa06217e520cabaa610fd88710be2a063bc51d037a82a07d4c710dfa9087bf5010efea8186f10f42bfaa6437d53c42fca998df54720de218817e54082faa3205fd52309eaa
  | 2 => 0x423218000041301407014df0141d000000d40301801001a40c41017403028040540505c0b0001b06c050540118c160040d0282a1dc0100c4b000090000000c18038070340b018c5150162ac030400d1a03400007000010459605003120cc09801030a300847060020cc1b00817002150b8e405401000440bd901fca00040000022031060e40901c0511c2401dd2000780000f6e4000640c03803064070001c2b428008010ecad0181b3bc120083a04401000000200202000948010813d00c0014c000040400033004e5000190040000807058068f8260340105c0400c0006420000000401d02800020060001d090000040604410064000582000c0e0140c0d4070080000c000bc0e0100401c100d00e0240600411078050040c000006b40102c011882502000434029102902c200780656c210040c1500d2280a0f80a1040f2bc000483000005000180b53f014ee0280000005000070342200c005f400240011fc480292f01400000050380407b7a62a05f15020bf28441dd32cc77c86215f14532ef98c637e51882fca320df946409f2a0437c524c77c42a05f15220ce21861bd40cc3b887995f94e10de21a81ef328cbbe6498df54840bfaa0437d5490f7a81887dd0541bfaa0419c53502f8a9987dc4210beaa043df32cc2f8a9995d94430bea96877e50902faa5086f90140af298217c515037c87995fd4d20dfa04613d54842fea7906f10841beaa0617e52106faa1216710d31de2a2637c54042faa1a16fd0641dfa0441be43086faa8086f55020bf2a0817d544c37887906fd0210bea96837e521037c8790df54742bf2a061ed4210b7e86a067d4d40be282637f54483be87994f15121dfa9e817c52502faa1a0dfd4d10f690e417d500877ca3a06f50740bea86877d52cc67ca9194f95210dfa8c877e5088778a421efd0b41dea9a81bc434c77886995fd4c21bea8c877551082faa918df54443de21821be43507f420085f14c21bea9c417f5150b7c86a0778c932bfa9a83bb50502fca621774cb30dea08837f53883788690df54a209e2a2617e534837c84a16f50130fc902215e53906faa7186fd0842df21861be42906faa3195754c20baa8861ee32c83baa610f754e42fa88021ed200837ca7a06f14443fb10843bc42d03ba64195f94632bea8c41be43cc77843a06f90f20f699641f5214437a80107dc8621bfa8a61bc41502fca190df55232df99681df31cc2fca918dfd5221be2a4637d540c6faa421df54042dea00817c548c2fca7886794c439f2a0417d5110b7a86a06f10e42ef98061bc515037aa810df55220fba0c837e500cb7887a0fe90040de21a217f53886fca3a1df14d40df21a43bc438cafaa8887e4c030bf29683be43042fca4885fd5121bf2a2617d530427ea898778c130dfaa6617c53506fea6a05f94430fd102217
  | 3 => 0x3e00
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc215023c6355210a7193308c31d5390c219ed9540102ad6214043c754c4310a3e64d4c20a798c21d031c6114d409b58b540431c5390540cd10d510c31e63153308f99251ccaad6210c42c7550438c27a6014c218f99250087966110f319b588540431f6494c1097d8d544c25d63d53219b588540c34d5354810c7d92530829c63501109758e51d0b1c5394940d3d0d520c23d658c9409798f54c832e54548308f98e540431d5350020da5491004274654c510c7951530831d5454c108f99353c863d6590c21c7192530831e54cca32b9d9521087555354420c714c434423f6590c108f993530433651500309bd89544431c53505409798e52d03364394420dc485500863e6515130d9d9521087a46448421a7580430c31f6355210c794c430877151480208f191530823d6494231c714e515031e5310a419718d544825f6354910d5545300c2756114132cb552520c32e5250010add85525023c6454f21c714e31503655294430c7988535029e6394740f8485500863e64141218f994544cbb140440108f994434c23c6454d208f992544c63e6414810c714e32503652154021e358843cca5e63d50219798c530871e5310f21d394e520431c544c530ba181324829c6350230c794e4390ab96014f40cd90d510836551480209798f54042b960949409e983530873651d00308f580544c67661d50208fd9153882756115032cd952510827561d50209758f52042b960147408f195404c23d64d4f20a7191300c23c6454b309dd85534829c6350040d9145214832d5454810e310d324831c6355030e398843cca3e658c740e690d300c3e121940218f594430431d5494c21cb94b40042ad62d4643c715132cc23f65500108fd81540871c5390940c794c43c432e43548308f18d548823e6510d21c794c43886b56114843ce591500863c6454c21a719132cc65e6394740c754c43c431c530c940c714e435072c4394810e510d510c31f5310e209798c52c423d658c740c714d425027960d50218fd9153843365150020c798453502786054d219bd954210b1d6114d40c7d92530869e648c932c754f400821d6510c308f580544867561d5332ab9885110e3c6454720a7994434ca3e65151218fd94430865e63150208f98c544c31c5314540ae58352d025f654c030c7588535026e6214810a798e52d031c5310e209b98b530431c43943318798f544867960150219758c520423e6494232a758c21d025d6594c20ab9885090f9443cc531c754c43083344394430d9949510c29c63502208f990524432e54948108f99250cc69e6390740c714d325031c53d4540c754c43086b960148438f59740042d4614c931c794e439071e5310c418f195325032d52148438f593530431d63d5132cd5445110f365454420c794c430ca5d6314a10c754c43d029e648c531
  | 1 => 0x82b96094d409758c524432d5454830a758e525031c6214d40aed81535029c63503108f59250ccb2d52d00108f99250c867b654c030d354f200823d6590c40c754c4390a1c63552109798c540869c63500108fd91530425d6315021c7994434c6776544010a758e52d031443544308f99353486b96008740c7994535031f6494e41c7953318c71c54ccb308f997425063d60d5131c754c53d031c54cc931ad986435065d6314b10c754c43107a52108740a798e535031d5310c108f592520ca5e6314c208fd9531d031c6454c21ae58353d025d631502097d95320cba44348421bc181314432c4354810c754c43c863e6508740ce10d500863e64d4e208f59052c431c5308540c710c504cb1c5310d20ce58354cc31c530c540c7151324c37151880208f994544c63c6454b1097596530426d6594810c7552530423c6454f10a7580438c29d6010f328f593528431e5390c21cb951520425d6394b40c710d520c23d6414e208f5935308396434c431c7951530423f6510c20a798f40cc31e5454c21ae580438433551500308f99251cc23f6454730c754c43c82e56288421c798f54cc23f6454b108f596540439853d4140dac85500871e5310c20a7994535023e6590d309758c540433751946439758f544871f63552309e195204427a60150329758f54c825e63d5020a758a5310f655254430c794f41906b96010c30e610e300c23c63550108f99743502bb60549408f992544cb1c43d4931a798e52503a55448421b5987434c71c53d4140ce10e500867b6054d219d58753082ba60087408f19151cc27a6015031c7d91530871d5494c20c714d515023f6550040c794c430c6766115030ce551500863d60d5121a7580434caaf6254540ad9845010e796014c21c754c434865f63551208fd91538867765504419e583530863e658c9408f593534863d609523297d954310f1d6510c30c7d4c435039b53d41409798c528434d53480208f592508863d65950308f59353c878c4394830d554e510823e6508540a718d525033960153308718d548825d63141218f992534871c5390140c710d51ccb1c43546309798c524423d65085409d987540c38c434cb209e980520431c544c931cb90e520430c43548309b98853042746154d208fd91534423e64940308f593534825d63d5310c710d510c31f53d41409798f544871c5388540b398b434ca9e6308540a718d548823e6590d32c7d9153043365494430ae580315029e63d01309798f54c871c53d09408fd954210b6551c8020d5547300c31c53cc940c754e43083395494021cd90e510c31f6214d40c710e50ccb4c43548309798c504863e64951308f59250cc73551d0030c714f435027661141328f191534863d64141318f593530871c5314940a798e421063e63151218f596315023f6454c20a758
  | 2 => 0x64548318f59250c871f6414d408f59252cc23d6510e209b189544436552440108f992508c65c63552108f592500c2b96090c309d584538825e6314c10ce952500872d5494810c714c41502b96010e208f582548c69e6510d319798c540431c5310940ce991500869e6390a41cb90e520c23d6590c20a79825310f4d524c0308fd95325029f6354540cd552510c2756115030ce951401025d63d5010d510d510c32e5494830c758f544871c53485408f9925004394434c5109d587540c23e6494032c7952530431c5390d408fd9153c871d5390c108f98e540831c5350d408f592508ca9c6350030c715131cc2ba6014843ae580325023d64d4d10ae980215029d6194c43cb90d520438e434c8328fd95400823d64940318fd81540423c6355021c798f544865d63145208f59632d035653944208f990538423e6414a108fd91510cba643484219758f540866e6215030c715331cc2b960085408f191510cb8c435483097d95310c71f5410d328f590530429e63909428fd81548c73a4354021c798e5310e3c6454f20c710d52cc71c6494c21a798e415071e5310c428f18c544c23e64d4f20c794d400826e6215010c7153324c3574354430ae980315023f64547209e596100423f6510e20c7d80535036921540219d98754cca3d6590e10a758e51d026d62d5030c794c43c823e6494221a758e515031e5390c208f194434874c524c9319b98b54cc71c534c540a6580430c23d65950209d984538831e6510d328f590514832d52500108f996434c63c6454e20a798e425029d6390940c758f544c72e52500308f990540431f6454c208f992500c677654c431c7952530823d6590c308f596540869d6510e30d594d51082b960945408f996315031c548c130cd90d510c2b66114243ae58043cc23f65487408f99353c431e5310f42ae58052d025d63947408f59250083695284010aed81515023f6590c21a718d408431d53500108f990514823f6590c20c794c43d073a4394021c714f315025c6355110c7191530823f654c54097d8d544427661d4c20c710d528c25c63552209ed95200831e5390a41c754c535023d60d5132cd951510c23d64940219b988504c63c6355020c754f400423d6590841e9484215026f6548020d394d520431e6510c30c7952530863e6494332c718d548833964940218f997404c31f5310e109e98354086ad62144439718d524429f63549408f594430871c53c85409e980540863f6454d20cb10e520c25e65d0d329798c514831f6494e42a798e434c7a94048020c794f400825d6510c30f8485204425e63d52218f59643042b561d4a438f59421d02b56110c418f590524423f6590e20a758e42d026d62150319b988530823d6510c208f590530878c43cc932a798e515032e52d00308fd81548ca9e6390c30ae580434
  | 3 => 0x9108f990530872d52500308fd954310e9c6355210c7d8453503645248510c7153314c23e6510d31c794e430423f6454f208f19153042b96090f309bd95320cb1e5310c409b988538425d63d52218fd91534865e6394b41c710e500c2776155120a758e415031c43d45328f994434ca3d64947328f59643883344394420cd54540082b56114043ae5805110e6d6214131c7551530871c6494c10a798e42d03c653484218f592534863f6510e108fd94430c27661150208f590528429c63503209d984520425d63d5020d354b300c35a5354021c714f525031d5310e418f592500cb1d6510f328f195215027561150208fd95411063e64d4d10ce992500863d64d48108f590520429c644c9318f59251cc29d6390740c754c438863e64d4810e6580430c23f6454b30c7d50434c79443944308fd9521502b96010d10cd551510c23e64948328f19521d035553c4010a798e415023e6395021cd55251082796015032e510d31c431c63552108fd91524429c63503309b588530436652944308f597400c23e6414c20ab98a4350ab56114243ad9875290eac6254540ab5885090eb960d47408f590504cb6552c4010c714e4350a3e6414b109798f540ca3d64944319798f520426d6214e108f990540c23d65d0020ab98b5190e9c63500208f590530835953540218f19532d023e64d4e21c714c438423e64951218f98e548423e64150218f590538423e64d4c21cd547400831e5350010c794f4290a3f654cb40a7580434c66f65484219d98453083a654484218fd94430435953940218f99632d02d96010c30cb10d520c26d62d53318f191538875a53940218f990540827461551208f990504ca3e63952208f594430c3344354420d354e520431e6510f31c7d4c434832d52d00309b98b540425e63148108f98f54486ae62140438f996434865e63d50318fd96430c2756114c20a758043cc71c53d054097d8d548831f6355220a7193300c27465485108f590504866d62d4c10c794c43d023e6414e20cbd4a5290e5e65d0d318f196434863f6590e10c7580535029e6390d328f59353c43a764484218f992500831c5354940c7553430c3612154021cd551510829c63545409bd89534429c6350120a798f544863e64d4d209b195324823c654c540c759443cc63d64940108f59353843956110f319798e51d0a9c63501309b98b540c2b66114843dc885500873a54540219798f54c431d6510e30c7191530423c6454e108f990504c7c55348421c794f400425d6394b418fd91520c63d60550108fd95400c23d6494b318f993528431c43141318f582540871e6510f328f992510c63e6414c108f594438435553440109d984540cb1e5310d21d914921c423e6494b31c794e439026c6254d108f99252cc31f5310d108f593538831e5310c108f993538423c
  | 4 => 0x320a8020000f02b5170c36000023cc2b00000070010240d1ec0908c040003700064004091087d004000004201437008000001f04c0c2200000800004090080231ad204c0b058680140e092a7200050100b024040000b0fc0b2f43c0e4000341c09c09178380a40e02404000188f43e27800000340002100c2a000f93f81a7ec3105c0600c01018020d40a0f0126e400000000b4260a80d0101d0240800000048000501200947008020040580004064050100d028010480200402000081ec001d0231881b030010000000c0300c00110e00183102c01040020045a07c710004002c0f008171bc040b48d0000401c640045203c6c000000181c05c4501c6e00403000020482205c0902814668631b46c038c90003702c040000c0dc3c00822070430002400c30bcc110380303c560040c138053d801020b26c00002001004413c409038bd0004d1e4000700100c0f2880304c550a4280300400801080ac66c9d0f8a70cc0c240140080c0740000cc2074032fc090040206c64034070141c1401101e3c654c7409d984530423d64d4e2197d8d54842ba600c9409b988540c6ba6014443e6980430c31d5454c209dd95210863f6454c218f580544cb3651d00208fd9153c42b461549408f191534427b6544010975965308799404c0309e580540c63c6454
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x21c00070f0a0800001502000006182b000306270006190400370000000000060000022f080800080e0102001d00050035016a0b6310230b00090a041e0008201a0e001a07c18c7292800841c735935284390a92808802183191524c030c28c728a801061853580438420e39ac02a243625c04354830838e6b2842a061853580438830c29cc010a818518d5150020a32e0218a098e0c43588504c60e3b2a6a00218614e600c940d2086302628841c73592500835090ac010a81465c04354430a4aea21a4210f2074485500870a322a398061461cd6454021a12e021aa41850e72d905350318a8ac028887465c06114d40b20e6a02200841c7558e42503912a242a8043075da5310d21a1ae021aa4185157199443ccb06322a598061455c04354430c18a7b12a2a049b75580430c30ab08c229a81071cd6494021838e6b04a810e1853580434420f39ec8a9621299da4348421a2ae2310a6a050d7218453502a8b8086a8861c454d4044010934ed21a601860c63549400c344218c099241071d95350020e12a4a026018741534855008788a8a80980618514f6154940a22e021aa2187044354a510c20f39eca90a8107dd85308540e448690aa010e146510d31443063288699241491d52108540930eca02601866065485204430a31aa2a00618698d601533083eeab0086185297010d520c298b8086a8861435c85310e10b22e021ca218721644855008791ba242a8043459c76414d40838eab1c82a070453484215020e39ac928021499cb5194643e0aa8a9a4210c1c7359250c86a4b8086a9061895895114443a32e0310a6a051571d90535030a21ac228265079cf6454720e42a890aa010d0d7299443cc75090ac010e818a5496014843c18a6312a2a074253485500868ab8cca21861071da5350020e0886a92a218588735012008286b96c829a810e5c06510d21a1ae532886185917010d314430631aa4a0021499c75294a4383ce7b2a43a0722644855008706b10c429a81c25c04354830a2ae2298871070a7010d520c270b90c098a2185191514c030e42a2a02401041c73592508868c39ac9280438614e600c540b0ce7b224210d0e72d92539060e3b4a6a0021385c4604c920838eab1842a07117010d510c30c29ac021a41459c46214d40e408690aa010d187054c434868cb8086a9061c110e5254430838e6b02a8087127010d510c384a9a8090041465c04314132c28c728a80185897010e520c312a92c2290878614d6008540b12e021a649041d7614c215028b38ec929c858318e5250030c28a630aa4a061b75580430c2c8b8086a8861439c86114d40
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x200280000c070010090c00054402040500000000002000000000c08655c0434c920905859cf6448421c05625c46214d40d00735494044010b018010d5294430920875912154021b008359121540219228790d2154021c05725846114d40c80435c8604c510c11615c06114d40a118114d6010e209088754d40480209108754d4044010b018010d5254430c80435c4604c920b0283dd12154021a098214d6010e10a058614d2108540e00534856008540c10655c0434c510d00735454048020c09625c06214d40b018010e5254430a118010d6114132a098010d6214131
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 802
  | 4 => 883
  | 3 => 144
  | 2 => 26
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
  | 6 => 2*((h/28+packedAt s5K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/295+packedAt s5K5 (21654+(h % 295)*10) 10) % 802)
  | 4 => 2*((h/308+packedAt s5K4 (33554+(h % 308)*10) 10) % 883)
  | 3 => 2*((h/69+packedAt s5K3 (7056+(h % 69)*8) 8) % 144)
  | 2 => 2*((h/43+packedAt s5K2 (1560+(h % 43)*5) 5) % 26)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3fe0fff0ffffe3f078f1f8ff1fff83fc0cf3cf
  | 1 => 0xc1ff0fff07c7fc7f80fe3f1fe383fc3c733d33
  | 2 => 0x1fff0fff807ff8fff003fe3fc03ffc383ce3c
  | 3 => 0xfe0000fffff8000fffffc003fffc0003fc0fc0
  | 4 => 0xffffff000000000ffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x280010210104001020482404a08110045045
  | 1 => 0x14424222120a40828052110921092828312512
  | 2 => 0xa8842444409480152900224248125281828a28
  | 3 => 0x8c16aa889480c929ca9480039258188ad80f80
  | 4 => 0x3118cc0ee727124e74e93c90006063336ff000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_39077
namespace PEqualNP.Outside.L_meta_39077
open PEqualNP.Outside.L_meta_39077.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa28214004000008904001ffd5003fd31027f14005fe5200ff04003fd2100ff88403ff21007f4c009ff53017fc8007fc40017f90803fe41017f8c805fc42027f94009fe5300ff08407fe43017f54805fc5200ff10403fd51017f08003ff41027f14c05fe2001ff90001fc3000ffcc403ff51017f50803fd41017fcc807fc4300ff44009fd5000ffc4007fc5400ff84003fe5100ff8c407fd4001ffd0c05fd20017fd4803fc51027fd4007fd4301ffd0007fd54017fd0803fc3101ff95005fc32017f4c801ff30027f54c01fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x84600bff14530037fcc99801bfd31cc00bff32c6005ff5863002df8c418033fe624c01ffe10c6005ff9423002ff8801801bff61cc00dffb2e600eff19530067fc6498036fd644c029ff2166005ffd003002ff8c21801bfe53cc01ffe20c600bbf5853002ff4601801fff210c00b7fb20600bf74c53002ffec318017fd640c0037e30e6001bf9863006ffa809800efe644c019fe292600fbf5863002df8c818017fc10cc00dff21e6006ff8c43002ffa411801afe630c001bfb2a600cff90930037fea61802ffd314c01d7fb2a6006f7cc7300a7fa8598047fd548c00fff2086005ff04130037fe6318037ff644c00bfeb246005ff19230037fca698023fc420c005773106005ff9943005ffaa29804ffe21cc00bfb3086010ff8ca3002ff8c418017ff640c00dfea186014ffd0b3002dfeca18053fe52cc00dff21a600fff14630037fcc398017fc628c00dfe29e6016bf5973003ffea218017fe200c0177eb1c600cff5093002ffaa01804fff41cc00b7fb0c6005f7cc030087f8a51803ffe218c0075f3206006ff10f30037f8a71803ffd318c00bfe320600bf7cc53002dfcc018017ff650c0093f3286006ff0c430067fe8498027fc540c00bff2006009ffd5030067fec498017ff300c019ff2926005bf1923002ff82118043fd428c00bee9806006ff18b3002ffa601802eff614c00dfe21a6005fb98830015fcc41801bff314c01dbe32a600cff589300057ec898017fc658c00dff21c6002bf9893007ffaa318017fc20cc0237eb246004bf19530087fca51801bfd53cc00bbf328600def1913003ff88218017fe500c00ffe1086006ff14d3002ffc2198017fc500c00dff1906006ff0cb30047faa418033ff204c00dff9906006ffd0f30047fea418016fc628c00dfe21c6001bf9843002f7cc818016ff610c017ffa0a6006ffcca3002ffa2018043ff428c00bff8846015ffd033001dfcc99801bfc65cc0097f32a6005ff8413002ff84098037fe544c0157eb28600eff54d30037f66098053dd32cc00bfe900600cff189300b7fea19801bff32cc00d7fb0e6006bfd973001dfcc81804ffe51cc02bff2a66006ff4cb30004feca98017fe620c0017ab086006ffd4f3009ffe2198023fd420c00dff32e6014ff54b3002ffcc91803fff418c00bff1806005bf19630077faca9804ffd21cc013feaa06005ffc823006dfec89804ffd41cc00dffb166007ff1443002ffec21804bfd538c00dfe1926013ff54730067ba6498037ff434c011fe290600bff9453009fba6398017fe610c00dff98e6005ff0823002ffa801802ffe614c017fe30a600dff1913003ffaa21801bfd310c023fea1c600bffc413002ffc2118017fe20cc019fe9926013ffc873006ffaa89801bfe530c00bfe206600fff94630037fac39802ffd414c00dfd984600effd4130
  | 1 => 0x1ee0e0001c00c20c00c04042c828040a025141a000200400073bb40123326041143b000440c1d000d80a000d0003004019f0080d0080c0a2c0086d3a001410c000c1803564093588c002701804000f0087040040000428000000402041405406cd440703601088401245028341020000c0201b0080c7e15000504c230500408081c80420210001c0207000180000000480804049ac0e1d6b454800f0380004120003006230000c093e32a600dff1513002dfcc118017df308c00bff3206006ff58b3008ffca918017f5610c00bfeb286005ff0403002df8ca18032ff624c0057e3126014ff4833002dfec41800ebc644c023ffa1c600fffc8630065fac49801bfe430c01bffaa26006ff8c730047fc8418043fd328c027ff20e6006ffd933005ffe429800efe648c023fe2a4600dffd013005ffa429801bfd43cc01d7eb2a6014ff10b30037fac998006fe61cc00dfe3266005ff88130035fec998023ff420c0057e3166005ff1433003ffc421802ffe314c00bfe202600fff5063002ffa81180027d650c01dff32a6008ff9483009ffea39805bfd50cc01dffa9a6001bf18530025fccb1801bfc61cc00dff9886015ff15330037facb98017ff628c00bfeb146000af5903002ffcc51802ffe414c019fe2126005ff9863002ffe811801bfc430c017ff10a6006ff0c73002ff8ca18017fe40cc02bffaa66000bb58830037f8a618037fd434c01dfea826005ff5963009ffa219803ffd218c013ff2a06005ffd883002ff8c31801bfd530c027fe10e6005ffc8030035f8c99801efd610c00bfe204600bffd453001df8c898017ff648c00dfe18a6001bf98530037be659800afe62cc00b7e30c6006ff0ca3002ff8401802ffd614c00bff0806007ffd0430097fea718017fe404c00bff286600fff8c63006ffcc8980177d650c017fe10a6006ffcc13007ffc8318012fe65cc00d7e32e6010ff10a3009ff8839800afe628c00d7fb166005ff8823002f7ac818017ff658c00b7fb146014ffd4b300a5fac598022fd620c00dfe18c600bff1053002ffea11801bff430c00bf6b106010ff90a3002ffac218017fd508c00bfe8846013bf5873002ffca09801bfc320c01fffa8c600cf7cc93009ff8a39801bf9300c019fea92600cffd493008ffea918017fc504c01bfeb226005bfd9630037fcc598026fd640c00bff8806015ff55330037fe6498017fe408c0217eb146005ffcc23002df8c21801bfd320c00fff2886005bfd9230095facb18003bf644c029ff9066006ff8cb3005ffa2098017fd620c00bffa806004bf994300affa8198006f6610c019fe9026007ff4843003ffa8218017fe304c00bef1826006ff94e30087fea518043fd528c01dffb2a600bffd85300adfac998053fc52cc00bfe2
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd515903002ef770584300073f65d9130036ee735883002e7c105943002e7f4059430006bd75d91300073c65d9130006bc755903002ef52058430036be73590300ce7e40d9530006bf525903002ebc20590300073c64d953002ebe5059030006f574584300767d30d95300cf5c30d9530036ef43588300067e7159430036bc3259030006ed5458830006bc72d91300bebc30d91300067f20d953002ef430584300d67f30d95300067d43d95300067d42d95300367d3259430006be61d91300067e745943002ebe7059030006bc72590300c6be53d91300bebe30d913002e7d4059430006be65d9130006bf65d91300067d7259430036bf7359030036bf325903002e7d10594300d67c31d953002ef630584300067d62d953002eef405883002eec1058830006f7545843002e7c4059430006bf53d9130006be72d91300067f41594300c7b830d9130006ec5458830006bc21d9130006be21d9130006be51590300067d2159430006f77558430006bd31d913002e7d70594300063c65d91300075d31d953002ebf70590300067f62d9530036f5735843002ebc1059030006bf52d9130006bd65d91300067d42594300bebc20d9130036ed735883002ed53058430006be71d91300067e31d9530006bd51d9130006ec515883002eed40588300079f31d9130006bf71d9130006bc5159030006bd61d91300bebe50d9130036f753584300067e41d9530006ed7158830036f653584300067c74d95300d67e43d9530036bd3259030006bd53d91300c6bf70d91300067f72594300ce7f73d9530036f5535843002ebd705903002ed7305843002e7f20594300d67c43d953002eed105883002ef6505843002eec4058830006ed75588300d77b30d953002ef4205843002eed50588300247e76d9530006f752584300067d61d95300367d4359430036f432584300ce7e70d95300c6bc32d91300067d415943002ebd10590300c6bc31d9130006bd215903002e7e7059430006ef415883002e7c705943002ebd505903006ebd73d9130036f473584300367c3159430006bc71590300067c42d9530006f45458430006bc75d913002ef670584300367f31594300075f32d9530006f6425843002e7d30594300067f74594300bebf73d913002e7e4059430036ec5358830036f743584300c6bf32d91300067e32d9530006be71590300067f7159430036ed4358830036f73258430006f47258430006be51d9130006ee7158830006bf72590300757e76d953002eef70588300bebe20d913002e7f305943002eee7058830006ed415883002e7f1059430006f6745843002ef62058430006f554584300bebc10d9130006f742584300067f10d953002ef74058430036ec3158830006bc65d91300067f21594300067d7459430006ec745883002ebf205903002eed3058830
  | 1 => 0x9530006f675584300d77830d953002e7f70594300067d71d9530006f54258430006f6725843002ebc70590300067e215943002eec5058830006bd725903002eef10588300079d31d9130036f67358430006bf75d9130006ee5458830006bd5259030006bf20d9130036be315903002e7d2059430006be525903006ebd70d91300d67c73d95300bf9c30d913002ef72058430006bf755903002ef53058430036ef7358830006ef71588300c6bf31d91300bf9e30d91300067c41d9530006ee74588300067f74d9530036f54358430006bc62d91300d67f70d953006ebd30d91300767d73d95300ce7c20d95300075f31d95300067f72d95300067d41d95300ce7c70d9530006bf62d913002ef47058430036f643584300c6bc53d913002e7c3059430036f453584300d67c32d95300bebc70d9130006f45258430036bc735903002ef6405843002ef45058430006bf51d91300067e725943002e7e30594300067d72d95300067c21594300067c7159430006ec75588300079f32d9130006bf21d913002ebf50590300c6be73d91300c6bf30d91300c7bb30d9130006be725903002ef730584300067e42d9530006bf72d91300c6bc73d91300bebc50d913002eee10588300367d31594300d67f32d95300067f42d953002ebd2059030006f5525843006dbe76d9130006f654584300067d74d9530006be31d9130006bd62d9130006ef7558830006bd71590300ce7e20d9530006f7745843002eec30588300067f40d9530006f475584300d67e73d953002ebc30590300067f61d95300ce7c10d953002ebe10590300067d10d953002eee30588300367f32594300067e64d9530006ee75588300767e76d95300367f7359430006ef5458830036f44358430006bd52d91300767d70d95300367d73594300067c41594300067f64d9530006f474584300067d32d95300067e62d9530006f44258430036f77358430006be52d91300367e735943002ebe3059030036ed31588300063f65d913002e7c20594300067d40d9530006f6525843002eec70588300067c72d9530006bc215903002ecd30588300d67f31d95300367c73594300367c32594300067e71d9530006f575584300067f21d95300067d21d9530036ed5358830006bc71d9130006be32d9130006be2159030036bd3159030006bd72d9130006bd20d91300067c7259430036ee53588300bebe10d9130036ef5358830006be7559030036bf5359030006ed5158830036ec73588300067c64d953002ecf30588300067e42594300367f4359430006ec4158830006bd71d9130036f632584300067c61d9530036bd5359030006ee515883002ef750584300067e72d953002ebe2059030036be53590300063c64d95300079d32d9130006bf10d913002eee50588300067f425943002e7e2059430006b
  | 2 => 0xe71d80814163c80000102e80400070ebb808110402c0c450399c8e040780400100009c261b01034000106000001a000886a1b00860081c0200000051b00c16320102c22320080c000001800000517005463803808040400118100c109e8000c0001c5c0e0011c000b00000569f068000e4f0180000871a8004a001103c0820040000002000042c2d0001406063303c023c0786d4224000bc2a070000400040380c540d00a296e000300cc8015280004010a88c0078000040409018340c05321d400000367e43594300067e4159430006bc52590300367e3159430006bf61d91300067c7459430036bd7359030036f532584300067d20d9530006be62d913002eee4058830036ef3158830006bc51d9130006bd32d9130036be32590300075d32d9530036bc31590300ce7e30d9530036bf31590300ce7c30d9530006ef51588300367c435943002ebc505903002ebd305903002ef540584300067f43d953002eef3058830036bc53590300067c21d9530006bf71590300ce7e10d953002ebf1059030006ef7458830006bd21d9130006f5725843002ebf3059030006bf51590300067c425943002ef570584300067e74d9530006bd10d9130036ee4358830006bd755903006ebe76d91300067e21d9530006bc61d9130006ee4158830006bd50d91300067c71d95300067d715943002ef550584300cf5e30d9530036ec4358830006bf21590300bebe70d9130006f772584300067c62d9530006be75d91300067d64d95300067f41d95300067e61d953002ef4405843001cbe76d9130006bc52d9130006ec7158830006ed7458830006bf50d91300367e325943002eed705883002e7e1059430036ee31588300067d31d95300ce7c40d953002eef50588300067f71d
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87e87087654c02f17d0f18ec8980039948421594300354e41aeab206000ab5841c9610c00155d0838ac41807e2fe1d53d91300045ec3ea1b22601bad7835c9610c00117b0e10ac818002ada1075584300051ec24e5b2a6000aad841d5620c0334b90c996ca980028f61472590300053bc0ac5b2a6000aac82587644c00147b09196ca980021f61c41d95300c54f418e5b226018e94314c7644c0010fb0e10aca18022ba60071588300051f42ce5b226000aad84145620c0014790ab0ec898062a7a0c21d91300045f43842b20601aa5e831c7654c00156b08292c2180669760c72d95300c54f418e3b226000a3e851c9640c00147d0a10ac8180028f61021d95300d43f43e81b2a60008bd878cb644c00147d09316ca980022fa1c525903002d79400e4b086006ad6831c9610c00147908b16ca9801a9720d74594300051e422c3b2a601987e878c7654c0014dd0a38ac418002ad20562d913002d75400e2b106000c3d751d7644c02f5750010ec8980028fe1562d91300051f420e2b28601cacf835c5620c00156b083aac2180028fa1865d91300051ec2ce5b226000a3d859c7644c0014df04b0eca980021fe1d61d95300051ec2c63b226017a9c864cb644c00147d0b38ec89805e2f21d53d91300051f42cc3b226000e4c624cb654c001ca8c298eca98002abe0961d91300043f43883b2a600087d8710b654c0010fd0e20aca180029d61474584300051f424c3b2a60008bd87149640c00147d09396ca980030fdd2745943000536c28e8b106000a5d83087654c00117d0e10ec8980022f61c21d91300051ec2842b206000a9d83085640c00156d08392c2180028f61632d91300ed4fc1aeab206000a3e848c7654c00155d083aac41805ea760c72d91300053b428e4b0860008bd8714b644c0010ff0eb16ca98003395c471588300043f43885b2a6000a5d83085650c00147d0b18ec8980022f61e61d91300cd2e43263b2a601ea5f835d1650c00187eeb3aec898003a948421590300043ec3cc3b2a6000ab684149610c0014ed0a3a2c2180022f61e31d91300051f428e2b20600087e87085650c00155d0828ac4180021f61c41594300051f42043b2a6000e6521087654c0010fb0e10eca98002ae60021590300cc3f43c65b2a6000a3d8498b654c00147d0a10ec8980028fa1021594300051f424e3b2a6000a3d84085650c00187aea3aac8180022fe1d61d91300043ec3cc9b2a60178be878cb644c00147b0918eca980029e60021d95300071baa4a8b086000a7980085650c00b5750010ac8180038bd52545883000537428e8b10600087d878cb654c001d18c4996c8980028f61421d91300051ec2cc3b2260008bf8758b644c00d59d0638ac41806a97a0c21d95300053ac2884b086006a9e83085640c02fc74a1a86c898003a518531d9130
  | 1 => 0x6000000421e121e000202067a0000da7a524600000892a82c103802002e022606386a043e0208180a180ea00e0e0e00007e00560e2e5204020a0c4a5e000004000a000438001a00220026080006043c740040026c0800020c520400c3d741d1650c00156f02b16c8980661f21d43d95300043ec3c63b2a60008be87145640c001c6aa82a2c2180021f61c42594300c45f43ea1b226000c3f759d5640c00147f08b0eca98002a760c21d91300356a41ae4b0860008bd87145640c001d4a4210ec8980021fa1c42594300051ec28e2b20600087d87d03654c00f5ab06392c2180022fa1c52d913002d3d40042b286008acd831c5620c0014db0a38ac41805ea760c71d91300061f3b0cbb226017a9c864c7644c0015af06aa2c2180028f61271d95300d72a18a63b2a601aa5e831cb654c00147b08392ca180029ba1441588300043ec3cc5b2a6006ad483551610c00155b0838ac41806b930c932d95300045ec3ccbb226000a3c8558b644c00d4bd0610aca180029b20961d95300051f42ccbb2260008bd87147644c00117b0f316c8980038b55054588300c74619265b226019a5d831c7654c00187ae83a6ca980022fa1c51d91300043fc3ac9b2a6000a3e8598b644c00147d09196ca98002ae60021d91300051ec24c3b2a6007af1801c9610c00d59906aa2c4180028f61071594300051fc22c5b2a6000a3f85587644c0014eb0a392c21801ab320d71588300cd3d40043b2a6000a3d8598b644c0410ff0ea1eca980029d20562d953000536c2882b106000acf83551620c00147d08392ca180030fdd274d953000672b90e4b086000a3e858cb644c00117f0eb2ec8980029da1442584300061f3b6cbb226000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x180cb00401c04341c935d4755903000638601721c9610c00103f985d475d91300069848580085650c001237985505458430006a848580085640c00103f985d475590300040fe61741d3654c04341c935d07459430006a848580087644c00103f985d074594300048be6154151620c04360c93550545883010d8524d54151610c001a612160021d9530
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x4
  | 7 => 0xca
  | 8 => 0xcb
  | 9 => 0xcd
  | 10 => 0xce
  | 11 => 0x9ca
  | 12 => 0x9cb
  | 13 => 0x9cd
  | 14 => 0x9ce
  | 15 => 0x12ca
  | 16 => 0x12cb
  | 17 => 0x12cd
  | 18 => 0x12ce
  | 19 => 0x168a
  | 20 => 0x168b
  | 21 => 0x168d
  | 22 => 0x168e
  | 23 => 0x1789
  | 24 => 0x130c
  | 25 => 0x17c9
  | 26 => 0x134c
  | 27 => 0xd5d2
  | 28 => 0xd453
  | 29 => 0xda55
  | 30 => 0xd8d6
  | 31 => 0x58e
  | 32 => 0x5cd
  | 33 => 0x74c
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 402
  | 6 => 416
  | 5 => 211
  | 4 => 15
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
  | 7 => 2*((h/148+packedAt gbK7 (14874+(h % 148)*9) 9) % 402)
  | 6 => 2*((h/173+packedAt gbK6 (19968+(h % 173)*9) 9) % 416)
  | 5 => 2*((h/91+packedAt gbK5 (12449+(h % 91)*8) 8) % 211)
  | 4 => 2*((h/12+packedAt gbK4 (1050+(h % 12)*4) 4) % 15)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xf07f83c1e0fe0ffc7fff80fff09f033c0cf3cf
  | 1 => 0x7f87fc01ff0ff0ff8e03ff03f3681ccc733d33
  | 2 => 0x7ff87ffe000fff0ff003fffc0c70e0f383ce3c
  | 3 => 0x80007ffffff0000ffffc00000f80ff03fc0fc0
  | 4 => 0x7ffffffffff0000000000fff0003fff000
  | 5 => 0xffff800000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x900880804012011012a0805140030114045045
  | 1 => 0x24851400a90490a484092a02a1280c48312512
  | 2 => 0x4950295200092a09201254a8045060a1828a28
  | 3 => 0x4e6532a0000e495806082a80b602d80f80
  | 4 => 0xc4473b9dccfccc000601830cffd00036ff000
  | 5 => 0x7e66003018818880018060c30ffedbfc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeafee8fee8eae8feeafee8fee8eae8feeafee8fee8eae8feeafee8fee8eae8feeafee8fee8eae8feeafee8fee8eae8feeafee8fee8eae8feeafee8fee8eae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_39077
namespace PEqualNP.Outside.L_meta_39077
open PEqualNP.Outside.L_meta_39077.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 1 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 11 := block_range (n:=11) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 11 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 9 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 21 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_192 : Interval s1Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_288 : Interval s1Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_384 : Interval s1Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_480 : Interval s1Atlas 4 480 71 := block_range (n:=71) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 551 := (concat (concat bs1_4_0 (concat bs1_4_96 bs1_4_192)) (concat bs1_4_288 (concat bs1_4_384 bs1_4_480)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_96 : Interval s1Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_192 : Interval s1Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_288 : Interval s1Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_384 : Interval s1Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_480 : Interval s1Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_576 : Interval s1Atlas 5 576 90 := block_range (n:=90) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 666 := (concat (concat bs1_5_0 (concat bs1_5_96 bs1_5_192)) (concat (concat bs1_5_288 bs1_5_384) (concat bs1_5_480 bs1_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 40 := bs1_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_7_0 : Interval s1Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_7 : Interval s1Atlas 7 0 1 := bs1_7_0
theorem alls1 : ∀ k ≤ 7, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 71 := block_range (n:=71) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 551 := (concat (concat bs2_4_0 (concat bs2_4_96 bs2_4_192)) (concat bs2_4_288 (concat bs2_4_384 bs2_4_480)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 90 := block_range (n:=90) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 666 := (concat (concat bs2_5_0 (concat bs2_5_96 bs2_5_192)) (concat (concat bs2_5_288 bs2_5_384) (concat bs2_5_480 bs2_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := bs2_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 13 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 17 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 26 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 48 := block_range (n:=48) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 144 := (concat bs4_3_0 bs4_3_96)
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
theorem bs4_4_480 : Interval s4Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 19 := block_range (n:=19) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 883 := (concat (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 (concat bs4_4_288 bs4_4_384))) (concat (concat bs4_4_480 bs4_4_576) (concat bs4_4_672 (concat bs4_4_768 bs4_4_864))))
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
theorem bs4_5_576 : Interval s4Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 34 := block_range (n:=34) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 802 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 bs4_5_288)) (concat (concat bs4_5_384 bs4_5_480) (concat bs4_5_576 (concat bs4_5_672 bs4_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := bs4_6_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 26 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 48 := block_range (n:=48) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 144 := (concat bs5_3_0 bs5_3_96)
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
theorem bs5_4_768 : Interval s5Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 19 := block_range (n:=19) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 883 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384))) (concat (concat bs5_4_480 bs5_4_576) (concat bs5_4_672 (concat bs5_4_768 bs5_4_864))))
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
theorem bs5_5_768 : Interval s5Atlas 5 768 34 := block_range (n:=34) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 802 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 (concat bs5_5_672 bs5_5_768))))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 15 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 211 := (concat bgb_5_0 (concat bgb_5_96 bgb_5_192))
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
theorem bgb_6_384 : Interval gbAtlas 6 384 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 416 := (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384)))
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
theorem bgb_7_384 : Interval gbAtlas 7 384 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 402 := (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384)))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeafee8fee8eae8feeafee8fee8eae8feeafee8fee8eae8feeafee8fee8eae8feeafee8fee8eae8feeafee8fee8eae8feeafee8fee8eae8feeafee8fee8eae8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813544 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_39077.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,2]⟩,⟨.or,[4,5]⟩,⟨.or,[1,2]⟩,⟨.and,[3,7]⟩,⟨.or,[6,9]⟩,⟨.and,[4,5]⟩,⟨.or,[0,10]⟩,⟨.or,[3,11]⟩,⟨.and,[0,13]⟩,⟨.or,[8,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813544 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813544 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_39077

open PEqualNP.Outside.L_meta_39077 in
theorem PEqualNP.Outside.L_meta_39077 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813544 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813544 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
