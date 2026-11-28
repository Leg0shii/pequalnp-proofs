import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36410.Model
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


end PEqualNP.Outside.L_meta_36410.Model

namespace PEqualNP.Outside.L_meta_36410
open PEqualNP.Outside.L_meta_36410.Model
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

def SBf (j : Nat) : Nat := [5, 6, 7, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36410

namespace PEqualNP.Outside.L_meta_36410
open PEqualNP.Outside.L_meta_36410.Model
def s0K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x2030100405f32dc6574cb6994d32
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*4) 4
  | 3 => packedAt s0K3 (i*15) 15
  | 2 => packedAt s0K2 (i*26) 26
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (5+((h/1+packedAt s0K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s0K3 (79+((h/1+packedAt s0K3 (75+(h % 1)*4) 4) % 9)*4) 4
  | 2 => packedAt s0K2 (27+((h/1+packedAt s0K2 (26+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 2 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 3 => 0xebf03f3f80fec3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xfffffffffffffffffffffff404104009020045
  | 2 => 0x208041042040112
  | 3 => 0x150aa0690a94c28
  | 4 => 0xe082ab24a14e80
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 30 s0Pos s0Neg, 0xfcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36410
namespace PEqualNP.Outside.L_meta_36410
open PEqualNP.Outside.L_meta_36410.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x80be40bc40
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (34+((h/1+packedAt s1K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x1ffffe03fe1f087fc3fc3ffff0fe070133f7cc
  | 2 => 0xe07c3ffc3fffff83fc3fc380ff0ffffeccc8ff
  | 3 => 0xff803fffc01ffffc003ffc00fff007ff0f0f0f
  | 4 => 0x3fffffe00fffffc00000fffff803f00ff0
  | 5 => 0xffffc00000000fffffffffff00000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc31802388422100cc04c048e701231181153cc
  | 2 => 0x4900444890080101441441121104924844c055
  | 3 => 0x842aa8910d548ab4222aa824aaa044b30b0d0a
  | 4 => 0x165331222906acdaaa822048ccc96023b00ea0
  | 5 => 0x186221c33198cf6333333270088180c3eea000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaf0f000fafafaaafaf0f000fafafaaafaf0f000fafafaaafaf0f000fafafaaafaf0f000fafafaaafaf0f000fafafaaafaf0f000fafafaaafaf0f000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36410
namespace PEqualNP.Outside.L_meta_36410
open PEqualNP.Outside.L_meta_36410.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1e52380803000022004c6213e1c79b2c0001d009d500003411c0c41223005c200220059234654264a0000a5621014000ca890a0c10410c0004100050103ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x7618848600820000003400002200b40000004c0000008ca666ac00408a9000301e023e44800c8896b60894005600000000005aa2ae68b26c4aa800006a42640000781ca42e00100e505400248e12000000002a5200009e7e000000aa007200620046200a0004483800583a26009a7400701600000000920000005c60a098009c007a065e7c281a0000000036324eb03c142c6e0e0000010900000204020006030202060300020005010300020201050100b7290876d5210ebca6215754c429f2a0653d540cb9a64195794f41aea9e836e52d06daa5a0e794f41cea9e83ae52d075aa5a0cf943419eaa483b75150678a0a0cf950419f2a4633d548c6dea498db149319f2a0633d540c6dca418db54831bd2806379500c67ca910cf55221afa9a435c534867ca810cf55021af298435d53086f4a010de540219ea8c813e50902bca6205754c40b7290816d52102eca2205d54440cf298819d531035ca4206b54840db288813d511036aa2204d544409f28081ba501027ca9984f55330b7296616d52cc2dca5185b54a309faa2613c544c27ca9904f55320af29e415d53c82bca7105754e209faa2413c544827ca9884f55310daa0e213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b629221b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xe006020c84a000020c3551320cb0d5354b41c354d52103165354440c554d51103265254440c954951102346550510
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (788+((h/14+packedAt s2K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s2K4 (2724+((h/30+packedAt s2K4 (2484+(h % 30)*8) 8) % 147)*8) 8
  | 3 => packedAt s2K3 (312+((h/2+packedAt s2K3 (304+(h % 2)*4) 4) % 15)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc3ffff81fe1f0f0ff0fe1fffe1fc1c1e99f793
  | 1 => 0xfc1f0ffe3ffffff07f0fe1c0fe1fffff6648ff
  | 3 => 0xffe00fffc01ff1ff800ffe00ffe01fe1878f1c
  | 4 => 0xfffffe001fffff00000ffffe001f80fe0
  | 5 => 0xfffff000000001ffffffffff00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4846008c04221001901202466024444c089391
  | 1 => 0x81001110100800202104208802090910224026
  | 3 => 0x188aaa248d548356888b5412b54092c5858d18
  | 4 => 0x32d4cc492906a59b5aa11024d992c089d80ec0
  | 5 => 0x23188871b198c9ec6ccd993811030311f76000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeecccc88eeeeeeaaeecccc88eeeeeeaaeecccc88eeeeeeaaeecccc88eeeeeeaaeecccc88eeeeeeaaeecccc88eeeeeeaaeecccc88eeeeeeaaeecccc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36410
namespace PEqualNP.Outside.L_meta_36410
open PEqualNP.Outside.L_meta_36410.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x2516440000000aa800282190a800260e0c4212424d000000f23524c7013000000007c3001850ba21e9cb1b00715003a0868048ac8000000004050300b141102043ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x150800110006052025395153493d3c45265716480a420733303f0038210c28000000000d002b5943544b402c1a581d343a00172d0f002e1e272429350e0031181c2203555a1913564e461b124d3e2f470902140152442350363b0410000b004100004f321f4c000037004a2a002a4ca890614006040c8801c089000070000025000802109040d7a5090ef2a121de94242bca84853e540ca7aa819734c832bb2886575510caf4a0195e540329f286833d54906f6a0a0de14141dba8a83bb5050678a0a0ee141419c282833e541067ca918cf55231b7a92636c524c67ca818cf55031b7290636d520c6f4a018de540319f2a4433d54886bea690d714d219f2a0433d54086bca610d754c21bd2804379500867aa3204f94240af298815d53102dca4205b54840bb2888175511033ca6206754c40d729081ad521036ca2204f54440daa888135511027ca0206e940409f2a6613d54cc2dca5185b54a30dc204613f544c278a8986e101309f2a6413d54c82bca7105754e20dc204413f5448278a8906e101209f2a6213d54c436a83886e103109faa4213c548427ea8884f15110daa0a213e540427aa8085794c10aea98216e52042daa4086e10010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xa022010a1458001a30010000001c000180000b8000080000801878000002c002000a9200000098e93000100304314003453254432c698c50507196314141ca988505072962141418e181548c6386055221c354d52103165354440c554d51103265254440c954951103306054440ca548408c2b16110230ac584404c3195310220ac58440882b16110120ac18141c42b161103108d19541442396510010c654c40043295210010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x8410c0018258d6214141a22e6302a220521721815110310a92c2204618454d6110220
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | 2 => packedAt s3K2 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2667+((h/30+packedAt s3K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s3K3 (998+((h/8+packedAt s3K3 (950+(h % 8)*6) 6) % 57)*6) 6
  | 2 => packedAt s3K2 (249+((h/1+packedAt s3K2 (245+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fe3fffc0e3c78e3c71f8fffc7070e1e19fc93
  | 1 => 0xe1fc3e3ff03ffffc07e3f1c0f807fffe6640ff
  | 2 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 4 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x44288c0460489100c1048246c131224c089c91
  | 1 => 0x8410048809020040221108808024490224026
  | 2 => 0x94881491240940294802a41252500944858518
  | 4 => 0x4012a9224820125295480024a4a4a009580ac0
  | 5 => 0x991330038d32649f2693493800c0c191f76000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefeeaeafcfcc8c8fefeeaeafcfcc8c8fefeeaeafcfcc8c8fefeeaeafcfcc8c8fefeeaeafcfcc8c8fefeeaeafcfcc8c8fefeeaeafcfcc8c8fefeeaeafcfcc8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36410
namespace PEqualNP.Outside.L_meta_36410
open PEqualNP.Outside.L_meta_36410.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x920018000285c0003e3000b003c01b4eac01d0434000484140a389400000200112aa4d16001150500981980e811a20084c893c000131c3c0100044040004000003ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x842ce0f901680014990d2c00485d20002800000000e558000000bcc4a0d80165309c004d2400f0003488fc1ca851615d1d3c094000000000003c0c00381800f49400300064005800b00518780000dd080040000090000000d0b80000000020014cb480546cd4000000a40000c110e8000128006800000001054844acc8000114ed44747c008d5001542400700138cc6011343a00020a12001000000208002400020e06000002000202040404000c00017a5090ef2a121de94242bca84853e540ca7aa819734c832bb2886575510caf4a0195e540329f286833d54906f6a0a0de14141dba8a83bb5050678a0a0ee141419c282833e541067ca918cf55231b7a92636c524c67ca818cf55031b7290636d520c6f4a018de540319f2a4433d54886bea690d714d219f2a0433d54086bca610d754c21bd2804379500867aa3204f94240af298815d53102dca4205b54840bb2888175511033ca6206754c40d729081ad521036ca2204f54440daa888135511027ca0206e940409f2a6613d54cc2dca5185b54a30dc204613f544c278a8986e101309f2a6413d54c82bca7105754e20dc204413f5448278a8906e101209f2a6213d54c436a83886e103109faa4213c548427ea8884f15110daa0a213e540427aa8085794c10aea98216e52042daa4086e10010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1e000000a800002a400e00000050002202809a30012000002658019cb12c0002e40000001820004004000013453254432c698c50507196314141ca988505072962141418e181548c6386055221c354d52103165354440c554d51103265254440c954951103306054440ca548408c2b16110230ac584404c3195310220ac58440882b16110120ac18141c42b161103108d19541442396510010c654c40043295210010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x642000818258d6214141a22e6302a220521721815110310a92c2204618454d6110220
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s4K5 (788+((h/14+packedAt s4K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s4K4 (2697+((h/30+packedAt s4K4 (2457+(h % 30)*8) 8) % 146)*8) 8
  | 3 => packedAt s4K3 (998+((h/8+packedAt s4K3 (950+(h % 8)*6) 6) % 57)*6) 6
  | 2 => packedAt s4K2 (248+((h/1+packedAt s4K2 (245+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fe3fffc0e3c78e3c71f8fffc7070e1e19fc93
  | 1 => 0xe1fc3e3ff03ffffc07e3f1c0f807fffe6640ff
  | 2 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 3 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x44288c0460489100c1048246c131224c089c91
  | 1 => 0x8410048809020040221108808024490224026
  | 2 => 0x94881491240940294802a41252500944858518
  | 3 => 0x4012a9224820125295480024a4a4a009580ac0
  | 5 => 0x991330038d32649f2693493800c0c191f76000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafcc8fcc8feeafeeafcc8fcc8feeafeeafcc8fcc8feeafeeafcc8fcc8feeafeeafcc8fcc8feeafeeafcc8fcc8feeafeeafcc8fcc8feeafeeafcc8fcc8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36410
namespace PEqualNP.Outside.L_meta_36410
open PEqualNP.Outside.L_meta_36410.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300123819407165939a1298a2036902801c0001e00840004608a83321149f14006970060000003ce80008898022208014a0000450000430820c244bff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fa20fd20f920fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x6617c54cc2fca5985f54b30bf28e617d51cc3be6398774c730fd20661f940cc2fea9185f95230beaa4617c548c2faa7187790e30eea1c617e528c2faa5185f94630bea8c617e508c3f681187e10230ef98461fb308c2fea8985f95130beaa2617c544c2fea4985f14930bfa8a617c514c3be6298774c530fda0261f8404c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea90617e510c2faa2185f94030fd20061f9400c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c82fca3905f54720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c417e50883f681107e90220fca0441f840883f661107e8c220fc98441f830883de41107ec8220fdaa441fa54883f2a9107e15220fda9c41fa53883f2a7107e14e20fda1c41fa43883f287107e10e20bca9441fb42883f485107e50a20fc21441fb32883f465107e4ca20fc19441fb51883f4a3107e54620fc28c41fb41883f483107e50620fc20c41fb31883f463107e4c620fc18c41fb21883f443107e48620fc10c417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a417f51482f8a2907bc8520f690a41fb40483f480907e50120fc20241fb30483f460907e4c120fc18241fb20483dc40907ed5120fd2a241f954483f0a8907ed4d20fd29a41f953483f0a6907ed0d20fd21a41f943483f086907ed4920f5a9241fb42483f484907e50920fc21241fb32483f464907e4c920fc19241fb51483f4a2907e54520fc28a41fb41483f482907e50520fc20a41fb31483f462907e4c520fc18a41fb21483d642907e88520fc90a41e921483f042905fd5020bf2a0417d54082f8a8105fd4c20bf298417d53082f8a6105f94820bf288417d51082fca0105e94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fda0621f840c43f661887e0c310fd10621f920c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd20421f940843f461087e4c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fd20221f940443f460887e4c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f680087e10010fd98021f830043f440087e48010fb88021fa10043ea20087e44010
  | 1 => 0xe544cafaa8995f15132ef21a65dd434cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cafca2197d94432bb288657d510cbeaa2195d54432bf28065fa500caf4a0195f54032fca806579500cafca7a0df54f41dfa1e83bd43d06fca5a0df54b41dfa1683bd42d06fca1a0df54341beaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83bd43506fea4a0df14941dfa1283bd42507ee82a0ef90541bfa8283fb50506f6a0a0df14141fc282837850506fca820df94c41ef298835e53106faa620f754c41aea98837e52107dca420db94841bea9083ed52106daa420df94441dfa0883f6411077a8220fd50441bf28083fa50106f4a020df54041fca80837950106fea998df95331beaa6637c54cc7bc8798f750f31bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7bc8698f750d31bfa92637c524c7be6498f74c931fb98a63de314c6fea098fed4131bda82637c504c7f0a098de14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf298637e520c7dca418db94831bea9063ed520c6daa418df94431ef98863f6310c7ba6218fd4c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87dc8590fb50b21f719643ed32c86fca190fe94321bd286437d50c87f2a190de54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea94437e51887ec8310fd50621fb18c43f531887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c53487dc8490fb50921f719243ed32487ec8290fd50521fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410df94421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a07794f40af29e817d53d03baa7a05754f40bf296817d52d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81bf439037a87205f94a40bea94817e51902faa3205f94240dfa0481fb40902fea6a05f14d40bfa92817c52502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53102faa6206fd0c40dea18817e52102faa4205f94440bea88817e501037e80207e90040dea0081f940102fea9985f95330df2a6613e54cc2faa9986f553309eaa
  | 2 => 0xe0b517000096000ae000000000002d057e485270653042749f861082b3c9d9fc13e604301e727a760871ed266628e68d00004945d038000ae000298352995440ad1da6c08ca3511c0016d97546e2548e1084580006b00000024cee1071100b0a78571ec3c8c18ac3842442796c4ae2609d0630625300020a04a8404517a0b43a5570c5200020ca8000007303d8f32dc898a400017cb450b80048c80153994000830c6000000a48000000001f400110038780aba3d0009ac001e5000000001e24808147da3a4d82912d0eb2921f1110760f433c59a1e1f2580468222587c0a0a6f58a37d582735869dc4781827c4e4c98a21f83782188621a6ad409582a0b34760d95541a484a1f07cab55d0ab34a084742b25a87205490f1c8a00399e1006000080000e2700801802010020000e0b02609000048100080c0081403004120060300601004018000a8220201a00806000060080400000038020900415804020000582c0480a03004028000080600002048040000801002018000285c000520708e238641300400800000101080a0580800014008000f800010020100601004010060400e0001007002008760280c0a0001000a02018020000680207004000160080200000008680180a198080184c000400001c0c800000101181a1c0020200604000028060081a0180a008000700000018020000a80a08802000000180c0282e0000402000070720280a0885c00808020020e8140e8000200001838128020001c018000480a0002a028040600200802050020100400008000160300c0000e100080100001804010020480001006000017e52d0efaa5a1df94743bea8e877e50d0ff4a1a1de94343bea8687f950d0ef2a1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243fd284877a5090efaa121fe54243bca8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621e750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1217e94242bd284857d5090bf2a1215e54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea98857e5210b7e84217b90842dea1085ed4210afca2217d94442bb288857d5110beaa2215d54442bf28085fa5010af4a0215f54042fca8085795010afea9995f95332beaa6657c54ccbbc87997750f32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbbe65197bcca32bf28c657d518cafca1197e94232bd284657d508cbf2a1195e54232bfaa2657
  | 3 => 0x6f05726d35459d54a443e40d84d11b1462f4cca5f2be3047721c0009792900014e0106d8af38ea44080004840596d07905406c0493122a0d0ae852402645321322eca787c1dd4540300011f24e410001d2430820752d64f29fc458740002088e81f0005696598e244a09479d43ec5f0c0163464954ed91156a20d178145505c54e9620927d02f95454272d2620b51c65d258943de3842f11354807873a19308b00071434b67dc5dabd2481740d2d31de004970005aa9443f0000008d8001bb25432d6e80019a769311b9466578cfac700068cd098629a8b43400037e0008b1b11367e15127b320b080020d0001012984208c8c42706406a0014b1204e873c61a070a69e87b8892cc48c9b03c5721651480f0765ac00178334330eaaa01247105305c344719661442e00008a2845b8000001b40000000018d00000126a47072a940300000098c6ba6a40ca0c0027005000013800000000002903b20003b800000000000aa0003d4000000000fcfd95b3f40014a1650000000000040889c00000000398cb2150007e4fe9ac2a42d0c780013cad0b09f52e45ecd79d326a214789be0000006e2663fcb382a8672de1fc15a752a6134e89371a646837156016a14380001401c55d9b3000508000004d07040028a00047800261404514980000000000007500e44895845000300541e44e4000c4a305b20009400038062cd381905e4f000271324130b6a3e07a404c41e90a03fc5e24141c958c2ac150c7a91d97452a0c1091ba1ca3f8312b719c3f4851a847e6906d1343be11c3916a4783608199d0de5fd1a21a538325460111a4518a00294869256c000000660190903bc311241ce338419129051c00ccf428b000ab0d6a16000960240a534ca640000018c16cb20000007292500038a081578f02706791415916ea68330004fc0000000041e21d622c8000accc38000002e51180022e000f883a00000000051294a1d0ea09024915338c72040542c06c1709f40006d1640007d1b71002705b1ec3e688144a76370b5cd908c4283202a2604ba5e46889953e098daa030ac000858c2194af86e8784a0798011bd52666c002bc3dc4bd1c8000009e06a1c35a4758098375567404b9ff2e60016321b2962c08c26e03a5f86a80549e38d469e3442205121b62d2258121ae01a4a45090c2aaa6c00000392b28170005bc538001470d60002500000000158ac94560007a0005464b553003422000000b50000292e0b10466803517d2a2388221d73d64991c2b610800134a540009f00025917e05d4ba132d0000000002e
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xa53482eb6254d20d654c534827a65d0d209e597434827a6590d209e59643482eb6250d20ba18943483994310d20ba98843482e96210d20ba587524827a65909209e99442482da6310920b658c42483a94210920bc98442482f161109209e996324827a650c920ae99032482b9640c920f24c832482f2610c920bc58432482bb6454520ae19151482db6354520b618d51482ba6414520ae59051482da6314520b658c51482ea6290520ba58a414827b65505209e195414827a65105209e59441482da6310520b658c41482ea6210520ba58841482ea628c520ba58a314827b654c5209e195314827a650c5209e59431482ba640c520ae59031482ea620c520ba588314827a65c8520ba997214836a65c8520ba58a21483e36148520f8d4521483e05148520f890521483e14148520f88c521483e131485209e99421482ba6408520ae59021482da6308520b658c21482ea62085209e983540825e63150209758c540827661150209d584540827a60150209e983530823e6414c208f59053082766114c209d584530827a6014c209bd95200836a50480209ed95200825e63153109758c54c426e62153109b58854c423e6414f108f59053c426e6214f109b58853c423e6414b108f59052c425e6314b109758c52c42da63d0310ae99330c436a5248310da54920c425e63952109758e548423e6494e108f59253843695288210dad49208425e63951109758e544427b60551108f992534423d6494d109ed81534427960949108fd91524423c645491097d8d524425c63549109e980524427a65901109e195404427a658c1109e19530442786548110dad49204425e63d50109758f540426e62d50109b58b540423d6595010ce181540423e64150109798c540425d63150109b988540426d62150109e980540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d6181530423e6414c108f590530425e6314c109b988530426d6214c109e980530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810da98252042796054810cb951520432d5454810d394d520434d5354810da981520423e64148108f590520425e63148109758c520426e62148109e980520427965d0010ce55340042da63d0010d654f400436952d00109e59440043395410010d654c400436952100109e59730042ba64cc010ce553300435953cc010da54b3004279650c010ce5503004359530c010da54830042796588010ce95220043395488010d694e20043595388010da54a200433a5448010ce551200435a5348010d654d200436a5248010da54920042796584010ce55210043595384010da54a100427765440109ed9510043395444010d654d10043695244010
  | 1 => 0x863d6414d219e98053486796014d21ba582424866c6550921ba582324866c654c9219d19541487a542505219d19531487c5324c5219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219b988540867661150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219b98853086766114c219e98053086796014c21cb553210874d53c8421cd552210875553884219bd95210872d5448421d354d21086776548421cd55121087555348421ce95250087395494021d694e50087595394021ce95150087395454021d694d50087595354021dac8550087692154021d658253d031d53d0740c754d41d02b86050740ae583439031e5350e40a758f40902da63d02409798c515025d63145409b988515026d6214540b698f405029d63d00408fd95401027b6550040ce58254cc31d54cc730c755131cc2d8604c730ce95240cc33a54503309b98b548c26d62d5230b6582438c31e5450e30b698f408c3994310230a7593308c2ba64cc2309758e544c27960951308f990514c23d64145309b988514c26d62145309e997404c2da63d01309e994404c2ba64cc1309e983540c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c30c7151430c2796590030e650e400c27b6550030a7593300c25f654c0309ed95300c25e63153209758c54c827661153209d58454c823e6414f208f59053c82766114f209d58453c825e63d52209758f548825e63952209758e548823e64d4e208f593538823e6494e208f59253882da63d0220b658f40883395410220ae99330882b964cc220d654c30882da63d5220b658f54882e962d5220b698e54882d96395220ce55054882e96215220ae99353882b964d4e20ba58b53882ba6494e20ae59253883595314e20ba588538827a65d0e209e597438827a6590e209e59643883994310e20b698c42882d96310a20bc98442882f16110a20ae99032882b9640ca20bc98432882f1610ca20ae99051882b96414620b698c51882d963146209ed95418827865506209e99441882796510620b698c41882d96310620ba98841882e962106209ed953188278654c6209e9943188279650c620ae99031882b9640c620ba98831882e9620c620ae99021882b96408620b698c21882d96308620f8484218825e63951209758e544823e6494d208f592534823e64145208f590514825e63145209758c51482ea60c8520d9145214827a65d0120b698f40482d963d01209e195404833854501209e99730482ba64cc120ae5933048278654c120d614d30482da6395120b658e54482e96295120bad8954483395415120ae99253482b96494d20ba58
  | 2 => 0x60d53329e98254cca796095332c715143cca7b60547329e18151cca7a60d52329e583548ca7661152329d584548ca7a60152329e580548ca7a60d51329e583544ca7a60951329e582544ca5c6550d32c7151434cacc6250d328f990514ca3d64145329e980514ca7960145329d987540ca7561d50329e983540ca7960d50328f596540ca3e64150329798c540ca7661150329d584540ca7a60150329e580540cb1d54cc83297d95320cb1d544c8329bd95320cb365494432cd552510cb365454432cd551510cb573254432d98c9510cb553254432d94c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500ca7a6094f419e58253d06b960d0f419e98252d06796094b419ed8153906786054e419e98252906796094a41ae583435071c5350d419798c525065d63149419e980525067960149419e58b505073b4314141ce50c505067962141419e98252106796094841d394e521074d5394841da98252107696094841d394d521074d5354841da98152107696054841c754f411072d52d0441d954a411063f6550441c754d411072d52504419dd9541107655250441d694e50107595394041da94a501076952940419e58a501075a5354041d654d501076a5254041da549501067b6254041ced05501073941540419e98354cc67960d53319e98254cc6796095331b658243cc71c5450f319e98252cc6796094b319ed81548c67860552319b988548c66d62152319e980548c67960152319e982528c6796094a319e982544c67960951319bd89544c66c62551319ed81544c6786055131b6582434c65c6550d31c7151434c63e64149318f590524c67a60149319e580524c67962d4131d690c504c75943141319e588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f990540c65e63150319b988540c66d62150319e980540c67960150319e982520c6796094831cb952520c72d5494831da982520c7696094831cb951520c72d5454831da981520c7696054831c7553310c74d52cc431d954a310c65f654c431c7551310c74d524c4319dd95310c765524c431ce952500c7395494031da94a500c76952940319e58a500c73a5454031ce551500c76a5254031da549500c67b6254031d6cc5500c75931540319e98354c867960d53219798c54c865d63153219e98054c867960153219e98353c867960d4f218f99053c863d6414f219e98053c86796014f21ba58242c86e9608cb219ed81548867860552219798c548865d63152219e980548867960152219ed8153886786054e218f990538863d6414e219e98053886796014e2197d8d544865c63551219ed81544867860551219798c544865d63151219e980544867960151218fd91534863c6454d219ed8153486786054d218f990534
  | 3 => 0x2c158658af94d000a0813a4d000278260000003d07321a0648793c0d04e8218b51ae4a02e0d6a2f1aa118d7898000a74060003507613c855000058fa140332008b38003f2000d2992000000f281c4a4a012b1d45880005702039a4948f9ce070000518784c89102d8000006a4358001d0a8c3184e00045cde8000002393a9b70363c8551ec05eaf868800420000000000ac265542b508a000530cd2f69d9431ca2540008dac027c624492b95080013194658a00000000336078800000da3fceda5827a001561d52aa52c5698d4608000400000000097a620323b8000dc06e2e90080000021c1189d3a4000000003888ed3e8004b80000004000097c62800000350371794ee7e0002ab1909506104f3e6311101cb052000e40002e6850fd07a030000e81eb0d858c000cc000000002b40006d04d0000000011c8001ce6ac840002a849ce896147a5b11a1e22da1e4002731c23905f00036c288409321f822d4c8133184c54f1b54980a8e99c20068b4d81e3474969241c537cb05258fe000000002052681782988d52c820120442c00009a8900a01854a1f10b2000001721120012180e00c0b04c01000020200502c070000d0041100c12000000000001001048090080f00c040540000c07018000080000803018080140d00002034040040301001030010000201c00014020000101c0900c010180801001000000380c0080300c0004c00018030080004c000140700c0000030048020040407c00020040201100c010140000009000030080502005000010040100400004030280002408010170000200012020000280f00001008000180100401030110100603809008020300101c000001201c03000000000702c000040000c060000300002020000001c0140403400014000040701401000000040003c0b00c00000010000007809028020240a000000080000807000050080300c0100402008010000f02c130101201c0201c030000001c00018039e98252d0e796094b439e58a50d0e7b6254343b69834390e7a6094a439e5825290f3b43942439e58a5090e7b6254243b69834350eba6090d439d9845250e7561149439e9805250e7960149439b9885150e6d62145439e9805150e796014543a75924310e3f6550c4397d954310e9f6550c43c7d954310e7a60948439e5825210f1d4354843c750d5110e7b60544439e1815110f1d43940439e98253d0a796094f429ed8151d0a7860547429e9835350a7960d4d42c714d4350aac6250d429798c5150a5d63145429e9805150a796014542c754f4210a3f6550842c754d4210a6f6550842d594e5110b555394442d594d5110b555354442cdd095110b664254442cd5095110b654254442d694e5010b595394042dc9465010b715194042d694d5010b595354042dc9455010b7151540429e98354cca79
  | 4 => 0x14c00000106000470640250060280000000b0009ec0019a48a848d31da1763f484ac200069c460005780010894400084c64a693645bc60a3c54a001070003f6000ff0000009f0748003e4600be0003920b8000361265e9531434088a40009628a42c0022e014700258914bc214c59700d4134c511c49c4f0e326c21c0ac4e0f720a0002d00000060d0d8000006b01f10a38e0000016444e9015b0b5574a0400000000891198002280000023e3f87bc000215769b40000018c001159f01b66742e1882cc04943848000174000003d000000292586af431000000aa4001693ce0000024103a000e0800340001350003bc524000005223e1130b40003ed160ab186a6ca810c2a6004ee95b3ae1d95084333e000141e12ee6f0c98d953e5b8a100f00007d58297000358000880000014a8000e28a8000000002000007202e001308b6000068a70354e200000000000000000eb2e80000000012a998fb91241a9f800000000000cb9330004a4002570f82fc80a310f619c000a81d46700000044a0000006f4164acfb1c312e0f42f9ee260410000000000000a93a4a64190b9a1442000c88cf4ce5fc3315d25a4795b916398a291f80e3d25f89c81123241c58804194aa8cc2903545590f87e2063c000083082ac4001e0000594599820003e8382850001a00000046e6045c8251d80b43a8e54aa6cc6912131c0c5638331405d5569240fe8192c985276368001ff000000000af308000000260e6860dc0001ea654918000000005b800000a4d28800000a380013640e0006c0004c0088910000000009329a000374810000001a4000004ca690df9414843cc00148000808af27a2f00e55217d3fa5ac450520ee9286011143a2511b1762b8828000000004680000000052842000000000b425b0004405398713611c89a09346339190000006192e9a20004b000000000a0c068000c05886b8a90685447020f2a4858f50071e2889248003c80fcefaaf2e29c81d0002b4144dc9941f2b189410d5123bd572a757eae050a8b0ca4806f8573cc73d440420603b53800017a290dd91510463d3f9180127580020300038d359ba4508d4320000000f10a91d00a871590000927b4ac80011e6789726e178a609b80054055c6f01043251c00000000000ac24f5441f537a9c27e0001d80016491cd8a6829e27c63ab321e764528d3270161469dc446a3c659f548ca30710741601507b0
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2a71e5301b8980da212eea0000a00024210016300098b0001a48a00e034c80042143180000028d386caa18878650c60544438d2e4302a221ca5711894350a62b88c4a1a658654c6050740c32a8302639850d72151430c28ab88a8a1861a85912108620d82c690843105257414521482a2b98a290a41385c46250d20d1286b108690689635084248350a12c221241a2591320c920d8264b08649056275d8521482d0ba0a290a41705cc5148520ac0eaa0a4290560754c5214830caa4c7a002116dd953d0010c94c6a96800843b76553300430d322a7980218a99152cc010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x80909829c36550c43c09435c86054443
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 735
  | 4 => 712
  | 3 => 30
  | 2 => 2
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
  | 6 => packedAt s5K6 (756+((h/14+packedAt s5K6 (672+(h % 14)*6) 6) % 56)*7) 7
  | 5 => packedAt s5K5 (22295+((h/245+packedAt s5K5 (19845+(h % 245)*10) 10) % 883)*11) 11
  | 4 => packedAt s5K4 (29426+((h/237+packedAt s5K4 (27056+(h % 237)*10) 10) % 940)*11) 11
  | 3 => packedAt s5K3 (1530+((h/10+packedAt s5K3 (1470+(h % 10)*6) 6) % 40)*6) 6
  | 2 => packedAt s5K2 (122+((h/1+packedAt s5K2 (120+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc3c7e1c78f0e3c71de38f8e1c63871cf3e4c93
  | 1 => 0x3f9fe07fff03fffe03f1f01ffc07fff4070ff
  | 2 => 0xfc01fff80fffc07e3fc01ffe07ff81f0878f1c
  | 3 => 0xfffe00000fffff803fffe00007fffe00f80fe0
  | 4 => 0xfffffffff00000003ffffffff8000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x78742c8b116458e20e18382c560b146e1e4c91
  | 1 => 0x804010020080000001010080402080001026
  | 2 => 0x880484012420090042400a4402910122028518
  | 3 => 0x111011a648c82024b4aa401025264c04e80ac0
  | 4 => 0x22211904008d32493934949930040808f56000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfefcfcc8fefcfcc8fefcfcc8fefcfcc8fefcfcc8fefcfcc8fefcfcc8fefcfcc8fefcfcc8fefcfcc8fefcfcc8fefcfcc8fefcfcc8fefcfcc8fefcfcc8fefcfcc8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36410
namespace PEqualNP.Outside.L_meta_36410
open PEqualNP.Outside.L_meta_36410.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12ac72f000c62800880004a98b0040b0f860060a2e38011807e45f0260dc52a0a2079978e508474a40a768343803a90b927a019805a01b1000d499e76000000001c0b6200d802ac801a11000800112000821204b8000048801428d80027fd5007fe54027f55007fc54027fd4c05fe53027f54c05fc5301ffd0c05fe43007f50c05fc43027fd4803fe52027f54803fc5201ffd0803fe42007f50803fc42017fcc803fe32007f4c803fc32027fd44097f51027f94409fd51005f54409fc5101ffd0401fe41007f50407fc41017fcc401fe31007f4c405fc3100ffc8401fe21007f48403fc21027fd4009fe50005f94009fd50027f140097c5001ffd0001fe40007f50007fc40017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a2004bf9951007ffaca8803efd654401ffe32a2004bf1951007ef8ca880127c6544001ffb222000bfd9110077fcc88800efe6444001feb222000bf59110077f8c88800efc644401fffaa2200eff9511007ffaa88803bfc5444001ffb1a2000bfd8d1006ffcc68800afe6344001feb1a2000bf58d1006ff8c68800afc634401fffa9a200dff94d1007ffaa688037fc534401dffa1a200dff90d10007fa8688037fc4344001ffb122000bfd8910067fcc488006fe6244001feb122000bf58910067f8c488006fc624401fffa92200cff9491007ffaa488033fc524401dffa12200cff90910007fa8488033fc424401bff992200cff8c910007fa6488033fc324401fffa8a200fdfd451002ffca28803ff6514401ffea8a2000df5451007feaa28800375514400bfe28a200effd051002ffc8288003fd414400bfe20a200dffcc51002ffc6288003fd314400bfe18a200cffc851002ffc4288003fd214400bfe10a200fffd411007ffca0880037e504401ffea82200fff1411007ef8a08803bff4044001ff2022000fe90110007fa8088003f9404401dfe202200dffcc110007fc6088003fa3044001fe9822000fe4c11006ff86088033ff2044001ff1022000fe88110007fa4088003f92044019fe1022005ffc411002ff62088003fe1044001fb0822006ffd941002dfeca08017fe65040097f3282005df99410024fcca08017fd65040157eb282005df59410004faca0801bfc650400b7e3282006ffd901002dfec808017fe64040077f3202005ef9901001d7cc808017fd64040017eb202005ef590100057ac80801bfc640400b7e320200affd501004ffca80802bfd5404013fe2a02006ffd8c1002dfec608017fe63040057f3182005f798c10015bcc608017fd63040017eb182005f758c10005bac60801bfc630400b7e318200affd4c10047fca60802bfd5304011fe2982009ffd0c10047fc8608003fd4304011fe2182006ffd881002dfec408017fe62040037f3102005fb9881000ddcc408017fd62040017eb102005fb58810005dac40801bfc620400b7e310200affd481003ffca40802bfd520400ffe2902009ffd081003ffc8408003fd420400ffe2102008ffcc81003ffc6408003fd320400ffe1902005bf9841002ffea2080177f510400bff2882005ff5441002efaa208017fc510400bffa082005ff9041002ffa8208017fc410400bff9882005ff8c41002ffa6208017fc310400bff9082005ff8841002ffa4208017fc21040177f300200affd4010037fca00801b7e5004015fea802006ff14010036f8a008027ff400400dff2002000ff50010037f88008023ff300400dff1802000ff4c010037f8600801fff200400dff1002000ff48010037f84008017ff100400bfb8802006ff8401002ff42008017fd1004001fa8802005fe44010
  | 1 => 0x3fa3048001fe9824000fe4c1200bff86090007ff2048003fd9024001ff88120007dc4090007fc2048003f61024001fe0812002ffecb88016ff65c400bff32e2004bf9971002efccb880127e65c400bfeb2e2016bf5971002efacb880027d65c400bfe32e2005bf1971002ffec988016ff64c400bff3262003bf9931002ffac988002fd64c400bfe3262005bf193100b7fea988057fe54c402dfeaa62015ff1531002ffec788016ff63c400bff31e2002bf98f1002ffac788002fd63c400bfe31e2005bf18f100b7fea788053fe53c402dfea9e2014ff14f100affe8788053fe43c4001fea1e2014ff10f1002ffec588016ff62c400bff3162001bf98b1002ffac588002fd62c400bfe3162005bf18b100b7fea58804ffe52c402dfea962013ff14b100affe858804ffe42c4001fea162013ff10b100a7fe658804ffe32c4001fe9962013ff0cb1002ffea3880177f51c400bff28e2005fd9471002ffaa3880177d51c402dfaa8e2000dd5471002ff8a388017ff41c400bff20e2005ff5071002ff88388017ff31c400bff18e2005ff4c71002ff86388017ff21c400bff10e2005ff4871002ff8438805bff50c402dff2862000df943100b7faa18805bfc50c402dbe2862015ffd0310007fc8188003fd40c402bfe2062014ffcc310007fc6188003fd30c4029fe1862013ffc8310007fc4188003fd20c4027fe1062006ffd961005dfecb0801b7f65840013fb2c200bff99610025fccb0802ffd65840177eb2c2006ff19610025f8cb0801b7c65840093e32c2006ffd9210005fec90804bfe64840077f3242000ff59210005fac90801bfc64840077e324200bffd5210097fca90802ffd5484025fe2a42006ffd8e10005fec708047fe63840057f31c2000ff58e10005fac70801bfc63840057e31c200bffd4e1008ffca70802ffd5384023fe29c2012ffd0e1008ffc8708003fd4384023fe21c2006ffd8a10005fec508043fe62840037f3142000ff58a10005fac50801bfc62840037e314200bffd4a10087fca50802ffd5284021fe2942012ffd0a10087fc8508003fd4284021fe2142011ffcca10087fc6508003fd3284021fe194200fbf5861005ffea30802f7f518400bff28c200bff54610006faa308017fc5184025ffa0c2005ff90610007fa8308017fc4184023ff98c2005ff8c610007fa6308017fc3184021ff90c2005ff88610007fa4308017fc218400b7f304200bffd4210037fca10801b7e5084017fea842006ff14210036f8a10804bff408400dff2042000fe90210007fa8108003f9408400dfe2042011ffcc210037fc6108003fa3084001fe9842000fe4c210037f86108043ff208400dff1042000fe88210007fa4108003f9208400dfe1042005ffc4210007ee2108017fb108401fffb2a200fbfd9510006feca880027f654401fff3
  | 2 => 0x30007fa4298077fc214c0057fb02601fffd41300fffca0980037e504c03ffea82601fff141300fef8a09807bff404c001ff2026000ff501300f7f8809800bff304c005fd9826002ff8c130007bc609800bfc304c005ee1826002fe0c1300effe4098077fc204c00dffb2c401cbfd96200e7fccb10012fe6588039feb2c401cbf59620037f8cb10012fc658800dffb244000bfd92200dffcc91000efe6488001feb244000bf59220037f8c91000efc6488039ffaa4401bff952200e7faa91006ffc548800dffb1c4000bfd8e200d7fcc71000afe6388001feb1c4000bf58e20037f8c71000afc6388039ffa9c401aff94e200e7faa71006bfc5388037ffa1c401aff90e20007fa871006bfc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944006ffd8620007fcc310016fe6188001feb0c4000bf58620037f8c310073ff5188039bfa8c401cff946200e7faa3100037d5188039fe28c401bffd0620007fc8310003fd4188037fe20c401affcc620007fc6310003fd3188035fe18c4001ffc862000ffc4310007fd2188003fe10c4001bf982200e7fea110073fb508800dff2844006df942200e7faa11001bfc508800dbe284401cfe142200e6f0a11006fff408800dff2044000fe90220007fa8110003f9408800dfe204401affcc220037fc6110003fa3088001fe9844000fe4c220037f86110007ff2088003f79044001fec8220037f84110007f82088033ffb2a4019bfd9520006feca900027f6548033ff32a4004bf995200cffaca90066fd6548033fe32a4004bf195200cef8ca900127c6548001ffb224000bfd91200c7fcc89000efe6448001feb224000bf591200c7f8c89000efc6448033ffaa24018ff951200cffaa890063fc5448001ffb1a4000bfd8d200bffcc69000afe6348001feb1a4000bf58d200bff8c69000afc6348033ffa9a4017ff94d200cffaa69005ffc5348031ffa1a4017ff90d20007fa869005ffc43480037fb124001ffd492000ffca490007ee5248003fea924019fb5492000ff8a490007ff4248003ff2124001ff5092000ff88490007ff3248003ff1924001ff4c92000ff86490003ff61480017fb0a4000ff98520007fac290003fc614800b7e30a4019ffd45200cefea290067fe5148033fea8a4000df545200cff8a290063ff4148001ff20a4000ff505200c7f8829005fff3148001ff18a4000ff4c5200bff86290007ff2148003f790a4001ff8852000ffa4290003ed2148003fe10a4001bfd81200cffea090067fb5048033ff2824000df941200cffaa090067fc5048033be2824019fe141200cef0a090063ff4048001ff2024000fe90120007fa8090003f94048031fe2024017ffcc120007fc609000
  | 3 => 0xfa128003ff9094001ffa84a000ffc4250049ff9928023ff8c940007fa64a008ffc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8005bf1854012ffea2a00977f515004bff28a8025ff54540006faa2a0097fc5150007ffa0a8003efd054001ffc82a000ffd4150001dea0a8003ff10540127fe62a0003fe3150001fe98a8024ff0c54011ffe42a0003fe2150001fe90a8023ff0854001dfec0a0097ff505004bff2828000df9414012ffaa0a0097fc505004bbe2828003ffd014001ff680a000ffe4050001df2028003ff1014001f7880a000ff84050049ff9828024ff0c14011ffe40a008ffc205000dffb2c6022bfd9630117fccb18012fe658c045feb2c6022bf59630037f8cb18012fc658c00dffb246000bfd923010ffcc91800efe648c001feb246000bf59230037f8c91800efc648c045ffaa46021ff95230117faa918087fc548c0057eb1c6002ffd4e30017fca71800bfd538c005fe29c6002ffd0e30017fc871800bde438c005fea1c6000f750e30017f8871801bff628c041ff3146001bf98a30007fac518002fd628c00dfe3146001bf18a30117fea518083fe528c045fea946020ff14a3010ffe8518083fe428c001fea146020ff10a30017fe651800bfe328c005fe9946002ff0ca30037fec318003fe618c00b7f30c6000ff58630005fac31801bfc618c045ffa8c6022dfd4630117fca31808bfd518c001bea8c6022ff1463010ffe8318003fe418c001fea0c6021ff10630017fe631800bfe318c005fe98c6002ff0c630107fe4318003fe218c001fe90c6020ff08630015fcc11808bff508c00dff2846006df94230117faa11801bfc508c00dbe2846021ffd0230037fc8118003fd408c00dfe2046002ffcc230017be611800bfb308c00dfe1846002fe0c230107fe411801bfc208c03fffb2a601fbfd9530006feca980027f654c03fff32a6004bf995300fffaca9807efd654c03ffe32a6004bf195300fef8ca980127c654c001ffb226000bfd91300f7fcc89800efe644c001feb226000bf591300f7f8c89800efc644c03fffaa2601eff951300fffaa89807bfc544c0057fb1a6002ffd4d30017fca69800bde534c005fea9a601ff754d30017f8a69800bff434c005ff21a6002ff50d30017f88698003ff624c0017fb12601dff9893000dfcc498003fd624c03bfe3126001bf189300fffea498077fe524c03ffea92601dff149300f7fe8498077fe424c001fea12601dff10930017fe649800bfe324c005fe9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298016fc614c03fffa8a601fdfd45300fffca29807ffd514c001bea8a601fff145300f7fe8298003fe414c001fea0a601eff10530017fe629800bdf314c005ff18a6002ff4c530007ba629800bfc314c03bff90a6000ff885
  | 4 => 0x8b7ff414840bff20a4200fd90521007fa8290803f5414840bfe20a422cffcc52102ffc6290803f63148401fe98a4200fd4c52102ff86290807ff2148403fb90a4205ff8852102fdc4290817fc214840bf610a4201fd08521007fec090802ff6048401ff3024200ff58121007f8c090802fc604845dffa82422eff94121177faa0908bbfc504845dbe282422dffd012116ff880908b3ff3048459fe1824201ffc812100fde4090807fc204840dbfb24a02bdf99250006fac92801b7c649400dbfb1ca02adf98e50006fac72801b7c6394057bfa1ca02adf90e50006fa87280ab7c439400dbfb14a029df98a50006fac52801b7c6294057bfa14a029df90a50006fa85280a77c4294055bf994a029df8ca50006fa65280a77c329400dbfb0ca000df98650006fac3280027d619400dbe30ca02bdfd0650006fc83280037d4194057be20ca02adfcc650006fc63280037d3194055be18ca029dfc8650006fc43280037d2194053be10ca006df98250024fcc1280137a6094057bfa04a006df10250156fe612801b7c3094053bf904a006df08250037fecb200a2ff6590051ff32c8004bf99640147facb200a2fd659000dfe32c8004bf1964001dfac92000fff5490007ff2a48003ff5524001ff8a92001bff639004fff31c8002bf98e40007fac720002fd639000dfe31c8002bf18e40147fea72009ffe5390051fea9c8027ff14e4001ffe872000fbf4390007ff21c8003ff50e400077a872000ffc439000dffb148026ff98a4000dfcc520003fd62900017eb148006ff18a4000df8c5200a3ff529004dff2948028ff54a40137f8a52000fff4290007ff2148003ff50a4001ff8852009fff329004dff1948000ff4ca40137f8652001bff6190001ff30c8005bf98640007fac320002fd619000dfe30c8028ffd4640146fea3200a3fe5190051fea8c8000df54640147f8a32000fff4190007ff20c8003ff5064001ff8832009fff3190001ff18c8000ff4c64013ff8632009bff2190001ff10c8000ff48640137f8432000efe6090051ffa848006ff94240036fca1200a3fd509000dfe2848006df1424001ffe812000fbf4090007fda048006ff1024001ff0812009fff309000dfe1848026ffc8240037f84120097ff655004b7fb2a8000dfd9540004fecaa0097fe65500097f32a8025ff5954012dfacaa0097fc65500097e32a8025df19540024f8caa000eff6450007ffaa28003ff9514001f7ca8a000ffd545004bdeaa28003ff15140007fec6a0002ff6350049ff31a8002bf98d40007fac6a0093fc63500057e31a8025ffd4d40127fca6a0097fd5350049fe29a8003ffd0d4001ffc86a000ffd4350007fe21a8000ffd8940005fec4a008ffe62500037f3128000ff5894011ff8c4a0006fc625004bffa928023ff9494012ffaa4a008ffc5250007f
  | 5 => 0x4d31017faa69880bfc534c405ffa1a6202ff90d31017bc869880bfd434c401eea1a6202ff10d31007fec498802ff624c465ff3126201bf98931007fac4988cbfc624c4037e3126234ffd4931197fca4988d3fd524c465fe2926233ffd0931197fc8498803fd424c465fe2126202ffcc931017be649880bfe324c405fe9926200f74c931017f8649880aff614c469ffa8a6234dfd453102ffca2988d3fd514c401bea8a6205ff1453119ffe8298817fe414c401fea0a6205ff10531017fe629880bf7314c40bff18a6205f78c53102ff86298817dc314c405fa18a6232ffc853102ff84298803ff604c4017fb026200ff98131007fac098803fc604c4017e3026234ffd41311a7fca0988d3fd504c469fe2826234df1413119ffe80988cffc404c405ff9826202f7cc131017f860988cbff204c465fe1026205ffd962102dfecb10817fe65884097f32c4205df99621024fccb10817fd65884637eb2c4205df59621004facb10817fc658840b7e32c4205ffd922102dfec910817fe64884077f3244205ff59221005fac910817fc648840b7e3244231ffd5221187fca9108c7fd5488461fe2a44205ffd8e2102dfec710817fe63884057f31c4205ff58e21005fac710817fc638840b7e31c4231ffd4e2117ffca7108c7fd538845ffe29c4230ffd0e2117ffc8710803fd438845ffe21c4201bf58a2100ffea510807fe5288403fea944201ff14a2100ffe8510807fe4288403fea144201ff10a2100ffe6510807fe3288403fe9944201ff0ca2102dfcc310817ff518840bbfa8c4205ff9462102ffaa3108177d518840bfe28c4205ffd062102ffc8310817f6418840bfea0c4200fd5062102ff88310817ff318840bff18c4205fd8c62102ffa6310803f5318840bfe18c4205ffc862102fde4310807f7218840bfe10c4205fd0862102ffec110817fe60884017f3044205ff58221005fac110817fc6088463ffa844231ff9422118ffaa1108c7fc5088463be2844230ffd0221187f881108bfff308845ffe1844201ffc822100ff841108bbff654845d7fb2a422eff99521025fcca908bbfd654845d7eb2a422eff19521025f8ca90803ff64484017fb22422dff9912101dfcc890803fd64484017eb22422dff1912101df8c8908bbff544845bff2a2422eff5512116ff8a890803ff63484017fb1a422cff98d21015fcc690803fd63484017eb1a422cff18d21015f8c6908bbff5348459ff29a422eff54d21167f8a6908b7ff4348459ff21a4200ff50d21167f88690816ff6248403ffa924201ff9492100ffaa490807fc5248403ffa124201ff9092100fdc8490807fd4248401f6a124201ff1092100ffe6490807fe3248403f71924201ff4c921007da6490807fc32484037fb0a422effd4521176fea290817fe514845dfea8a4200df5452102ff8a290
  | 6 => 0xbdfa0c8203fdd064102ff88320817f4419040bff98c8205ff0c64102ffe4320817fc219040bffb048205ff98241005fcc120817fd60904017eb048205ff182411effea1208f7fe509047bfea84823dff142411eef8a12080fff4090407fe204823cffcc2411e7f861208efff2090477fe104823affd95411d5fecaa08ebfe65504097f32a823aff595411d5facaa08ebfc65504097e32a8205bfd914101ffea8a080ffe5450407feaa28203ff15141007fec6a0802ff6350473ff31a8202bf98d41007fac6a08e7fc63504057e31a823affd4d411cffca6a08ebfd5350473fe29a8203ffd0d4101f7e86a080ffe4350407fea1a8200ef50d4101ff886a0803ff62504017fb128238ff9894100dfcc4a0803fd6250471fe3128201bf189411d7fea4a08e3fe5250475fea928238ff1494101ffe84a080fbf4250407ff2128203ff509410077a84a080ffc4250473ff9928238ff8c941007fa64a08e3fc32504077fb0a823affd45411d6fea2a0817fe5150475fea8a8200df5454102ff8a2a080fff4150407fba0a8205ff9054102f7c82a0817fc415040bde20a8203fd105411cffe62a0817fc3150471ff90a8205ff08541007fec0a0802ff6050401ff3028200ff58141007f8c0a0802fc6050475ffa82823aff941411d7faa0a08ebfc5050475be2828203ffd014101f7e80a080ffc4050473ff9828239ff0c1411c7fe40a08e3fc205040bffb2c6205bfd963102ffccb18812fe658c40bbf32c62049f9963102ffacb188defd658c40bbeb2c62009f5963102ff8cb18816fc658c40bffb246205bfd923102ffcc91880efe648c40bfeb246200bf5923102ff8c918816fc648c46fffaa46236ff952311bffaa9188dbfc548c4057eb1c6202ffd4e31017fca71880bfd538c405fe29c6202ffd0e31017fc871880bfd438c405fe21c6205ffd8a3102ffcc518806fe628c40bfeb146200bf58a3102ff8c518816fc628c46fffa946235ff94a311bffaa5188d7fc528c46dffa146235ff90a31007fa85188d7fc428c405ff9946202ff8ca31017fa651880bfc328c40b7f30c6205ffd463102efea318817fe518c40bfea8c6205df5463102ff8a318817ff418c40bff20c6205ff5063102ff88318817ff318c40bef98c6202fdcc63102ff86318817f4318c40bff90c6205ff0863102ffec118817fe608c4017f3046205ff58231005fac118817fc608c46fffa846237ff942311bffaa1188dffc508c46fbe2846236ffd02311b7f8811880bff308c405fe1846235ffc82311aff841188d3ff654c4697fb2a6234ff99531025fcca988d3fd654c4697eb2a6234ff19531025f8ca98803ff644c4017fb226233ff9913101dfcc898803fd644c4017eb226233ff1913101df8c8988d3ff544c467ff2a26234ff5513119ff8a898816ff634c405ffa9a6202ff9
  | 7 => 0xa1002ff6150801ff30a8400ff58542007f8c2a1016fc6150889ffa8a8444dfd4542227fca2a1113fd5150889fe28a8403ffd054201f7e82a100ffc4150887ff98a8443ff0c54200ffe42a1007ef2150803fe10a8400ffd8142005fec0a1003fe6050801feb028400ff18142005f8c0a1113ff5050889ff2828444ff54142227f8a0a11137c5050807ffa028403ff1014221ffe60a110ffc3050803ff9028401ff08142217feca9910aff654c885ff32a6404bf99532217faca9910afd654c885fe32a6404bf19532007fec899002ff644c883ff3226403bf99132007fac899002fd644c883fe3226403bf19132217fea899107fe544c885feaa26441ff1513200dfec69900bff534c805ff29a6402ff54d32017f8a69900bff434c805ff21a6402f790d32017fa8699003dd434c805fe21a6401bfd893200ffea499007fe524c803fea926401ff1493200ffe8499007fe424c803fea126401ff1093200ffe649900bef324c803ff1926401f78c93200ff86499007dc324c803f61926400ffd8532005fec299003fe614c801feb0a6400ff1853202df8c29910bff514c885bfa8a6442ff94532217faa29910bfc514c883ffa0a6441ff10532017fe629900bdf314c805fe18a6401ffc853200fde4299007fc214c801ffb026400bfd8132007fcc099003fd604c801fe3026400bf18132217fea09910bfe504c885fea826442ff14132216f8a099107ff404c883fe2026402ffcc132017f86099007ff204c803fe1026400dfd9151206fcc8a88037d6454481be322a200dfd8d511fefcc6a88037d635447fbe31aa240dfd0d511fefc86a88037d435447fbe21aa200dfd89511f6fcc4a88037d625447dbe312a240dfd09511f6fc84a88037d425447dbe212a23fdfcc9511f6fc64a88037d325447dbe192a204dfd8551024fec2a8813776154481bfa0aa205df105511fefe62a88177c315447dbf90aa205df08551006fec0a88037e6054401beb02a200df18151004f8c0a89037f4054481be202a23fdfcc1511fef860a88fb7f205447dbe102a205ffd964102dfecb20817fe65904097f32c8205df99641024fccb20817fd659047b7eb2c8205df59641004facb20817fc659040b7e32c8203bf5924101ffea92080ffe5490407feaa48203ff1524102ffec720817fe63904057f31c8205ff58e41005fac720817fc639040b7e31c823dffd4e411e7fca7208f7fd5390479fe29c8203ffd0e4101ffc872080ffd4390407fe21c8205ffd8a4102ffcc520806fe629040bfeb148200bf58a4102ff8c520816fc629047bffa94823bff94a411effaa5208effc5290407ffa148203ff90a4101ffa852080ffc4290479ff994823bff8ca41007fa65208effc329040b7f30c8205ffd464102efea320817fe519040bfea8c8205df5464102ff8a320817ff419040
  | 8 => 0x900000705300000d00000400001d00600300000000b00003500002500600000000000f00000604f00004300600700200500400900100600000100700000b02301700300f02600600100e00003c00100800000200200000e01000000500300700a00c00200900001100300000000700100400402500a00100201600000100001f00000000400d00102500000900901a00400100601200100300101300300000401900000900703800d00100800100f00700401700000d00e00800500000000000900100900200200100001300000100101b00200c00000300102300800001000e00500000a00100000804300100300600d00500000200200a00000000900300800000800000502a00600100000500d00000500300000200000100800400600302300c00302602600000003000000300200300301500100602e00000200800800200100200500500102e00c00001700000e00300000a00600f00301a00000100200200400000d00300000001800600400600301800400400700000e01901f00000300300906204c001004007014000001003002001000001015009237fecaa191aff6550c8dff32a8604bf99543237facaa191afd6550c8dfe32a8604bf19543015fec8a180fff5450c07ff2a28603ef9514301ffaa8a191bbd5450c07fe2a28602bfd8d43017fea6a180bfe5350c05ef29a8602ff54d43237baa6a180bfc5350c05ffa1a8603f7d0d43017fc86a180bbe4350c05fe21a8602ef10d43017b886a180b9c4350c01ffb128600bfd894322ffcc4a1806fe6250c01feb128645ff1894300df8c4a191bff5250c8bff2928646ff5494322ff8a4a180fff4250c07dfa128603ff9094301ff884a180bff3250c05ef9928602ff8c943017f864a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c0b7e30a8646ffd4543236fea2a191bfe5150c8dfea8a8646ff1454301ffe82a180fbf4150c07fe20a8602ffcc543017be62a180bfc3150c8bff90a8645ff08543007fec0a1802ff6050c01ff3028600ff58143007f8c0a1802fc6050c8dffa828646ff94143237faa0a191bfc5050c8dbe2828603ffd014301ff880a180fbc4050c05ff9828602ff0c143017b860a1917ff2050c8bfe1028644ffd9542225fecaa1113fe65508097f32a8444ff59542225facaa1113fc65508097e32a8401bfd914201ffea8a100ffe5450807feaa28403ff15142007fec6a1002ff6350887ff31a8402bf98d42007fac6a110ffc63508057e31a8444ffd4d4221ffca6a1113fd5350887fe29a8403ffd0d4201f7e86a100ffe4350807fea1a8400ef50d4201ff886a1006ff6250803ffa928401ff9494200ffaa4a1007fc5250803ffa128403fbd094200ffc84a1007be4250803fe2128401ef1094200fd884a1007ff3250803ff1928401ff0c942007fec2
  | 9 => 0x6ac4f09646fe618b76b6e2569b465ce3a25e1aa2ae122704b940002a6db605e000000e0acd419a158788632b4ee4a8c6612cde7b410ce2e8828b87a8000a6ac7e30a000b4a8b488a90e000000c440000006e27160ca000126cc01a652ed4c00024095cb8440693a6beede04c1fe4f64d83a8a7848217687e32a8f0ca2236734996886bb8d8263891425c93202a92291c43e590834d2a574dba7a6cf2144026d086d6a6600035a4bc1b8c1c296b86754152884e3867aebc7ce8c8516bf069c2c8bce47e1e26304c03ea6ccbda6580008fc4fcb6a0006ea19279ecc8c2000036654220e000a226280000000001b6000000a3c1c0000000aa09b8000000000000000090888c64dd40000007ac0000d20008d805a05c8246360746f41189c6c88d1edc698413668cd921481e8e1ad764e015ad60a3a5928105ba018b601dc0d0b92828714daa008d3854ceb6a62c5eca016cbfee928be1ac000bd6d70e02d86000254926276368950392c84beecb083c2180e278e63ca4ce3e00085816a00000068476c702d9a95a0e8c92000000a326b8088000034d26000b82556000bb2000db8000cd230c1c60000668ca52a4dcd8a9a05f6ac40b800029e86c7e6a40706a940008aecd61a02ba000e7c8188a2c689b2ac84b4b8a0006b49cc4940b00000f203800000000100000100100c01c00401c00900000000100300000100d00001f00300000100000600d00701300600000a00001d01300900000000300200200a00400100000100602a00000000101901000300200600303901500300100400500100200602e00000300202403100000300001600900400800900200000100200000100700300a00500101e00604700000200400000002800100001200800900200e00300300200300200000000f02d00900000900100100300500006100000001c00200401200400200600000201700800000000000000200204500200c00000000a00500100500400802400500300600401800c02200402201600200a00000700000900200200001400002000500102d01301700000002000000000000000103100b00801601701800200100000201100001400b01000200000000100900702200200300600300a00500000502100100101500702300100000500001600000300300200100000100500400400000000200e00300c00101500200300400500000500100000b01100001400500000300101e00c03800400a00000000000d00801101e00003b00200000000701300801200700000300f01400302900800000100000000005b00300000001600500302b00305100500002001603900000f00d00c00400501d00200300300900700501003a01701300a00e00000000000001501600001400600900100002b02000100700100500700b01500000b00e00200a00c00901
  | 10 => 0xcc48440c77e204b5097a51c2649fc6a46780003501ecbdcc0e60800050edfa688a8470e584000000c9675c0000005e6ae48a43c00000007400a65e284a5343e2b0892048e9689ac84e6aade8da6e340000005b2e6cddc00044c992adced04580003300d6012294a2c00012000082e00095882c0004ee0003de0fe09e4c618086402e3866965242e68a8000000aeaeb40002fa0008381f4c12650a287c67da6205bc000000d9e0000006f00000000d44d4928dc86223fa796000000798000a1880a536000e40a4a78adead7a78cc369ec51082251a648274000000690aba3d6124b7494a8a09e81ea1dec9a8b25580000003707a2b5ced8000e5cbec000b426bc3523224d00aa8722f8b783e8c7231ec240008e29068629185c0160b580e400000080e3a2000ab20008f4000cce1cc57ece8766de05f02f004a0009ced2c2fe10a0a25d4846286a5ac5a00062c7e402066201c23a53887a5f41344a6e16a7cc6c7d6a2673ca2a04e9ba000d90ba800076a70c6c86141b2bf4a24abc9d4a52832ce01c4000000000000e285a47c0b52840206c10b40dbc3a464a000df6736000bbe0000009fe0c48d0110a2e48a1040000045ac000a6c7924f800009c2d8e64354a6edfc8ec000466626000172ade79cd0617ea0c260676866462aa8a36000030808b54142aa6cb48940005d00000000163986d283a9a80002c4be281e096a9000089e000184c087ee4cc000cdc2660003acacc000b0e7f2a4200094e0c641832c794e1cbde000b686fad0a8524c261028a75a0000005e4b9ca86744a54aaeb0200077a7863006047a46e066cbb63d862e4a4cbe078000c6a26244a4a2036b44000298c1a1f60dacfc4e42cc7b66a68e0a300003c20003888aab1c16664c5826820005261d2000a9800000040e36c00000006e7300003bc67c356ad2000000e186c4b1e150dde74e7f82f2496ab63f484400069e5b041a93c81aa7401e66aa2000069a6dc4e88ba07c4be292dca49813a472000decbbc1bcdee9eaa022e20468165cc4544ae2a03328487f44e211a430746a38a14dccd72b7a72c642546be8384904776c069303c460032e302772b183a67bcd1a594646476278318a8c272b1aa56d28708116cf09409f4000e48cda094e3ccd859aa087c264e9d25fc36050a54a0000f88bc1886de212080000cbad78cbce080002b01e600000030800086e518bb051405017a4320003904a8000c4646cbaa2c61e0de2000c800002160deda8000ba4a10000328b0a0000000005b6ca814e8a672adf200a7e2af83586602da9dadb4528ccc0be0ba38214c0ec4929a618c6e86daca66a8b88a50cfe4648b667286a102e10d62cc69600842483762b87dc00040492400093e71aa5890049ccee0004869c8b30726a0a4b01d6596b32000000000bfce667dee361f8eba50c0008dc
  | 11 => 0xd8186540c540701ca0fce8c44e586ea6898d5aad6b00c7c20c24a38e5781465ea38ae060ce0a0000000000c0269800000058a00665a85ec32000b5e000c9c90887c5d603200024e00091253a000000b620000000000006b017c2080002d600035ee4c000000000000000000cac0000000002b68eeaee27cd6cbf89ee6d8db03ce0e62b28c4e6296e8201a8c0a0861143f27d412a5a0e32414ed4df00acab891e26e03ae2059caec718ab06a03d07fe95600091a47cc2698a9be8600ae49eae0c3a8f8b668ac000b12000372606eaa8d4aa400263e1a477c1ce69431698ed983048de0a49e0000dfe74c4f2c7ab9055c400eae9527809c45d828413ed685dc39a0000002eaafc2e860a11c842d2489c9d8bea0002a4790be4674000ada1c888e0421be6c0b56b7cd5041626abd2552000d4a8685a894c4123da0004dad029aeb3e37c41c7fcd30106190bba21e5727ec762c90e04eca06428e1122343eee721b4e52732c160007ea3483a0a4ea7218aba0b48bd8344be0e0ec522bea167f027e74adc4a9c5ec2f40b4242df4052ec2de4d645d2cb67cc3365ca01465680cb2c0f4c56d7c6b29e2402d48000000a1a4fe3d442c680000b3846ae98ac2aceae29aaa8a2c25700c8ab4ea2394b3a700598092000d4023200096cd4e0ee312258df822ab64000e70b2e18e16881c9f29825680243068267685c45f2e902e0752000c74dd012cec40dc80000041e0005be000af4000d0e6682ee57634c000854238000af6000000bc2e1438c7aa3be9f01d83dc4f4c8ed146349807123b203c9dea60346000000e2600042edda000000000ece5da470000750c2a0007c499800000061c00000000000053c34a362778000a8e338420488000640602000bc8abe2b42f6e8e2d2dc202cafa2e4c703c6ebeca4456e2cd1097868e4506a27b098689248cafe000000a6400000083ee86da0c280005325c2e56ed2c3e3aebacd9c19c2021ba0006ba8749c2000000000e9400094602227a580000a3e00001a9d60000000eaa466f60007ca5020007823640006543403ec000af00fa60c8500002880009e4000d1671c11ec3ce2400000034eb1000091053eaf223c0004401c24ba422a1246e3f0e5eaaa0e0e0000067000044600020a4c829a0000002ce5a60003aad427bec60000000282000000000a80dd8ea00000000bc9483105aee96830c3456aaaceda6c20c0880cb28e668a000e5a4a000000022c000c42a5e41005803e3141ae33acecd6a16e506d209d06d4b0c6166c6c984740002ca000ad000059e00054e0008707b200079aa1c1d49bc66626c5c821aae62683e0a76d00138d5e000c18de6db262455a0000000004b695428c00045200058e758000e60342e1e90a33400010e108252000d2e000d12ec6dd2140000000000000cf4000e541a27d232029c0
  | 12 => 0x174b3445e13208c000000c620005b4000c149940000c2966e9eba25fec86000edcc40b36e9ad3a728eb8e78cfa00009a836774000bc6220178878500e6a916564bf2ba60003b4000b5a06012eb9671e2268040000003c8000b4c434d340005ee19e00089a7fa37e000000b7e378d1cb70000000a00aa2c82dce3b84b2c667a062a0004ca000000198784324a92938dbeb0654830e7202d47e852251e85ccf62149744aa8f28ead321f265e9b60542468d65ce7e002860e7482a8ce6d8e73e8900762ac8020f60682dc0482a223e1ee4b800061e988812c22c5c8da000c6e00089658c4487c86cea0e25a39c1d0cb8bc46ee652e8039642443636a00075672287661a36ed5cdae0003f8000d80a44b3c5e00f0562c8c9a4b6c224eb0ae8e12194408a347f6d363e47ae250bca4d67647b856066ebae14a8fac7807ad54e8a962a04ea4bb4222a7057a15e3ca5f82bca9692e000e68a6847876e67edac9dc31c85ae4692aa1e39e0001da6ec1b00007103269f8ac000ee0c37a99ee42000000000ce2a7ea880446e4e7ae304d20009ca08ad7440a56ccc2182426a5cd0c5e80003e6c4a75e000d4422ed3c1fa08e8e852c8f6c30d6e73a442040e9cbd46f21fc512d562c007e4ec99015c944be6170000b208ce5a29e6eb21e4480b229709723cc8b0270b0400000099c5de3b0d845080004fa154000aca000530cd02fc000e7e33c000a06000c1e5b86d000055e2000004acea8588d040b6162bfa2aac8ada25544de100bf624c90c380bd0d3e000b8ee4e692814eac9022d057c000374d88dd6460000000082e820109428cccf84385666ae9faa824443fc9345aa490228caa3f6000000b80b9a97c0000003ba1640008e4664e589c00004ce9b029000000012893613c8d2e88c5800c4c47708c0000eccc48742ad8000000ec80b2d660005fad2231a244520b16b245449f6c2e06c56ec2c98cd462802de47a550d7e000b26056c0045c4e6b141f06b6000c04000dc07bacae000ed69a221c210230000d58856b98000b4600073897600033e3fec4e72e43abc000035c000000428000e8443cb8cec0ac684c6e6a48d96e2acc4000000a9e000b288067d8e50e760004eaa9a6446865c696a130c0c82a49a00092c88c8fe4683d2000000d8ce74c38b9e0980006ca06ac76724c94c4cc9eda4d94ce497eb2aa7a072e22cca45a3b6c50cea63a7d0196156ad470a0a8e446f8062d1895e2ecd5242ab72504bcc6fc8c299ae6e76
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc5258810006ef425881003eee425881003eec4258810006ef325881003eee325881003eec325881002cff715881002cfe715881002cfd715881002cfc715881002e7f515881002e7d515881002eee215881002eec215881000cff7058810034fe705881000cfd7058810034fc70588100367e50588100367c5058810036ee2058810036ec205881002efa105881002ef91058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881002eef715881002eee715881002eed715881002eec715881002eef515881002e6f515881002eee515881002eed515881002e6d515881002eec515881002eef415881002eee415881002eed415881002eec415881002eef315881002eee315881002eed315881002eec315881003eef7058810036ee7058810036ec7058810006ef5058810036ee50588100366e5058810006ed5058810036ec50588100366c5058810006ef4058810036ee4058810036ec4058810006ef3058810036ee3058810036ec305881002eef1058810036ee105881002eea105881002eed105881002ee91058810036ec1058810004ff7650810034fe7650810004fd7650810034fc76508102267e65508100067d655081001ebe6450810006bd645081021ede6350810006dd635081000eee6250810006ed6250810004ff764c810034fe764c810004fd764c810034fc764c8102167e654c8100067d654c81020ebe644c810006bd644c810016de634c810006dd634c81000eee624c810006ed624c810094ff76500100057f75500100557c755001012e7e65500100067d655001001ebe6450010006bd6450010126de6350010006dd635001011eee6250010006ed6250010096fa605001008cff764c0100057f754c0100557c754c0100fe7e654c0100067d654c0100f6be644c010006bd644c010016de634c010006dd634c0100eeee624c010006ed624c01008efa604c010084ff76480100057f75480100557c75480100ce7e65480100067d65480100c6be6448010006bd64480100bede6348010006dd634801000eee6248010006ed6248010086fa6048010037785048010035f77644010006f77644010004f7764401000777754401023f747544010036f7654401003776654401023ef56544010037756544010006756544010037b66444010037b56444010037d66344010037d56344010037e66244010037e56244010035f7704401002ff37044010036f66044010037f26044010037765044010037745044010
  | 1 => 0x9010006be3259010006bc325901002ebf715901002ebe715901002ebd715901002ebc715901002ebf515901002e3f515901002ebe515901002ebd515901002e3d515901002ebc515901002ebf315901002ebe315901002ebd315901002ebc315901002ebf215901002ebe215901002ebd215901002ebc215901004ebf7059010036be7059010036bc7059010006bf5059010036be50590100363e5059010006bd5059010036bc50590100363c5059010006bf3059010036be3059010036bc3059010006bf2059010036be2059010036bc205901002ebf1059010036be105901002eba105901002ebd105901002eb91059010036bc1059010004ff7558c10024fe7558c10004fd7558c10024fc7558c10004ff7458c1001cfe7458c1001cfc7458c10034ff7358c10036df7358c10006df5358c10046de5358c10006dd5358c10046dc5358c10006df4358c10046de4358c10046dc4358c10004ff7258c1000cfe7258c1000cfc7258c10046df3258c10006de3258c10046dc3258c1002cff7158c1002cfe7158c1002cfd7158c1002cfc7158c1002e7f5158c1002e7d5158c1002ede3158c1002edc3158c10014ff7058c10034fe7058c10014fd7058c10034fc7058c100367e5058c100367c5058c10036de3058c10036dc3058c1002efa1058c1002ef91058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006de4258c10006dc4258c1002edf7158c1002ede7158c1002edd7158c1002edc7158c1002edf5158c1002e5f5158c1002ede5158c1002edd5158c1002e5d5158c1002edc5158c1002edf4158c1002ede4158c1002edd4158c1002edc4158c1002edf2158c1002ede2158c1002edd2158c1002edc2158c10046df7058c10036de7058c10036dc7058c10006df5058c10036de5058c100365e5058c10006dd5058c10036dc5058c100365c5058c10006df4058c10036de4058c10036dc4058c10006df2058c10036de2058c10036dc2058c1002edf1058c10036de1058c1002eda1058c1002edd1058c1002ed91058c10036dc1058c10004ff7650c10034fe7650c10004fd7650c10034fc7650c102367e6550c100067d6550c1001ebe6450c10006bd6450c10016de6350c10006dd6350c100479c4350c1022eee6250c10004ff7558810024fe7558810004fd7558810024fc7558810004ff745881001cfe745881001cfc7458810004ff7358810014fe7358810014fc7358810034ff7258810036ef7258810006ef525881003eee5258810006ed525881003ee
  | 2 => 0x5f97348110006fb6348110006f96348110065fb7248110007eb7248110007eb624811000efa624811000ef86248110067e86248110067ea5248110257e95248110007f3714811002dfa714811002df87148110007f071481102577b5148110257f25148110007795148110257f15148110007715148110067eb2148110007e921481100357f75841100357c75841100067f658411005e7c658411024777518411000775518411002dfa708411002efb608411002df67684110036f6768411002cf67684110035f7758411003777758411003577758411024df57584110037747584110007776584110247746584110035f67084110036f7608411002ff36084110037765084110037745084110037f24084110007f14084110037f23084110007f13084110037f22084110007f120841100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067c42594100067f32594100067e32594100067c325941002e7f715941002c7f715941002e7e715941002e7d715941002c7d715941002e7c715941002e7f415941002e7e415941002e7d415941002e7c415941002e7f315941002e7e315941002e7d315941002e7c315941002e7f215941002e7e215941002e7d215941002e7c21594100567f70594100367e70594100347e70594100567d70594100367c70594100347c70594100067f40594100367e40594100367c40594100067f30594100367e30594100367c30594100067f20594100367e20594100367c205941002e7f105941002e7710594100367e105941002e7d10594100367c1059410004ff7559010024fe7559010004fd7559010024fc7559010034ff7459010036bf7459010006bf545901004ebe5459010006bd545901004ebc5459010004ff7359010014fe7359010014fc735901004ebf4359010006be435901004ebc4359010004ff725901000cfe725901000cfc725901004ebf4259010006be425901004ebc425901002cff715901002cfe715901002cfd715901002cfc715901002e7f515901002e7d515901002ebe415901002ebc415901001cff7059010034fe705901001cfd7059010034fc70590100367e50590100367c5059010036be4059010036bc405901002efa105901002ef91059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf325
  | 3 => 0x471501100077551501100077a5050110277785050110077b8405011002df8765011001ef8765011002cf876501100077b75501102777875501100077b6550110277786550110075fb7450110007bb7450110007bb645011001efa645011001ef86450110077b86450110077ba5450110277b95450110005fb7350110005fb7250110006fb6250110006f96250110007f3715011002dfa715011002df87150110007f071501102777b5150110277f25150110007795150110277f15150110007715150110077bb4150110007b941501100a4fe768c1100067f658c1101167c658c11000775518c1100377a508c11003778508c110005fa768c1100a6fa768c1100077b658c11026f78658c110005fb748c110005f9748c11006df9738c110016fa638c110016f8638c11006fda438c110007d9438c110005f9728c110006fb628c110006f9628c11002dfa718c11002df8718c110036fb618c11026f7b518c11026ff2518c11000779518c11026ff1518c11000771518c110014ff764c11006cfd764c11002cfc764c1100057f754c11007d7c754c1100067f654c1100fe7c654c110006df634c110016dc634c110005f7714c11002df4714c11000775514c1100077a504c11026778504c11006fd8304c11002df8764c110016f8764c11002cf8764c1100077b754c11026778754c1100077b654c11026778654c110005fb744c110005f9744c11006dfb734c110007db734c110007db634c110016fa634c110016f8634c11006fd8634c11006fda534c110267d9534c110005fb724c110006fb624c110006f9624c110007f3714c11002dfa714c11002df8714c110007f0714c1102677b514c110267f2514c11000779514c110267f1514c11000771514c11006fdb314c110007d9314c11009cfe76881100067f65881100e67c65881100077551881100377a5088110037785088110005fa768811009efa76881100077b65881100e6fa65881100e6f8658811025f7865881100e6786588110005fb7488110005f97488110006fb6488110006f96488110005fb7388110005f97388110006fb6388110006f96388110065f9728811000efa628811000ef8628811002dfa718811002df87188110036fb618811025f7b518811025ff2518811000779518811025ff1518811000771518811000cff7648110064fd764811002cfc76481100057f754811007d7c75481100067f65481100ce7c6548110006ef624811000eec6248110005f7714811002df471481100077551481100077a5048110257785048110067e8204811002df8764811000ef8764811002cf876481100077b75481102577875481100077b65481100cefa65481100cef865481102577865481100ce786548110005fb7448110005f97448110006fb6448110006f96448110005fb7348110
  | 4 => 0x45101fe7e63545100067d63545101fe7c63545100067f62545101f67e62545100067d62545101f67c625451002d7f715451007f77715451002e7f615451029f77415451002f76415451002f74415451029777315451002f76315451002f74315451028f77215451002f76215451002f7421545100077b70545100357c705451000778705451000578705451002e7f605451002f7b105451002f74105451002f78105451007f77765451002677765451007f74765451007d74765451002674765451002474765451000777745451029f76745451000775745451029f74745451000777645451029f76645451000775645451029f74645451000777735451029776735451000775735451029774735451000777635451029776635451000775635451029774635451029f77435451029776435451000775435451029774435451000777725451028f76725451000775725451028f74725451000777625451028f76625451000775625451028f74625451029f77425451028f76425451000775425451028f74425451029777325451028f76325451000775325451028f74325451000777705451000773705451000776705451007f75705451000774705451003574705451000770705451002f77605451002e77605451002f73605451029f77405451029f74405451029777305451029774305451028f77205451028f74205451001cfc76505100067f65505101d67c6550510006bf645051001ebc6450510007755150510005fb7050510005f87050510014fc764c5100067f654c5101a67c654c510006df634c510016dc634c51000775514c510005fb704c510005f8704c51000cfc76485100067f65485101767c6548510006ef624851000eec6248510007755148510005fb7048510005f870485100057e76941100367e76941100b47e76941100067f649411015e7e64941100067d649411015e7c64941100067f63941101567e63941100067d63941101567c63941100067f629411014e7e62941100067d629411014e7c629411003777719411007d7d71941100377471941100367f61941100357e70941100377a70941100367f60941102877b10941100377810941100acfe76901100067f65901101467c65901100077551901100377a5090110037785090110005fa76901100aefa76901100077b659011027f786590110075f9749011001efa649011001ef86490110005f97390110077bb4390110007b94390110005f97290110006fb6290110006f9629011002dfa719011002df87190110036fb619011027f7b519011027ff2519011000779519011027ff1519011000771519011001cff7650110074fd765011002cfc76501100057f755011007d7c75501100067f655011012e7c6550110006bf645011001ebc6450110005f7715011002df
  | 5 => 0x47f7559110024fe7559110004fd7559110024fc75591100067c75591100247c7559110074ff7459110006bf7459110004ff7359110014fe7359110014fc7359110004ff725911000cfe725911000cfc7259110094ff7159110006f771591100067f51591100acff7059110006fb70591100067c5059110014fe76d8d100067f65d8d100067c65d8d1006ede63d8d10004ff75d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d1006ede43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006de32d8d1006edc32d8d1002cfe71d8d1006cfd71d8d1002cfc71d8d100067f51d8d1006edf31d8d10034fe70d8d1002cfd70d8d10034fc70d8d100067c50d8d1006edf30d8d100057f7558d1007d7c7558d100067f6558d100067c6558d1006edc6358d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c7558d100247c7558d10004ff7458d1001cfe7458d1001cfc7458d1006cff7358d10006df7358d10004ff7258d1000cfe7258d1000cfc7258d1008cff7158d10006f77158d100067f5158d100a4ff7058d10006fb7058d100067c5058d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d102367c6550d10006bf6450d1001ebc6450d10006df6350d10016dc6350d1006f9c4350d1000cfe76d89100067f65d89100067c65d8910066ee62d8910004ff75d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d8910014fe73d8910004fd73d8910014fc73d891002cfe71d8910064fd71d891002cfc71d89100067f51d8910066ef21d8910034fe70d891002cfd70d8910034fc70d89100067c50d8910066ef20d89100057f755891007d7c75589100067f65589100067c6558910005bf7458910075bc7458910005df735891006ddc7358910066ec6258910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc7358910064ff7258910006ef7258910084ff7158910006f771589100067f515891009cff7058910006fb70589100067c5058910004ff7650910004fe7650910004fd7650910004fc76509100067f65509102267c6550910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9102167c654c9100267f765451005e7e765451007e7d765451007d7c76545100267c76545100247c76545100067f64545102067e64545100067d64545102067c64545100067f635
  | 6 => 0x86588210037786588210036786588210035fb7488210005f97488210036fb6488210006f96488210035fb7388210005f97388210036fb6388210006f9638821000efa6288210037ea6288210037e96288210036f8628821002dfa7188210037f27188210037f17188210035f871882102b77b518821000779518821003cff76482100057f754821005d7c75482100367f65482100367c6548210036ef6248210036ec62482100377a5048210037785048210037e82048210005fb764821003efb76482100077b75482102af7875482100377b65482100cefa65482100cef865482100377865482100ce786548210005fb7448210005f97448210006fb6448210006f96448210005fb7348210005f97348210006fb6348210006f96348210037eb7248210037eb624821000efa624821000ef86248210037e86248210087ea52482102afe9524821002dfa714821002df871482102af7b5148210007795148210087eb2148210007e92148210035f576c421002ef576c421002f7675c421002f7575c4210036f765c42100377765c42100367765c42102a6f565c42100377465c4210037f260c42100377650c42100377450c421007d7e76d951007e7e76d95100247e76d95100067e64d95100067c64d95100067e63d95100067c63d95100067e62d95100067c62d95100077771d951007f7471d95100357c70d95102877b10d95102877810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067c42d95100067f32d95100067e32d95100067c32d95100067f71d95102867e71d951007e7d71d951007c7d71d95102867c71d95100067f41d95102867e41d95102867c41d95100067f31d95102867e31d95102867c31d95100067f21d95102867e21d95102867c21d95102867f70d951007e7e70d95100347e70d951007e7d70d951007e7c70d95100347c70d95100067f40d95100067c40d95100067f30d95100067c30d95100067f20d95100067c20d95102867f10d951007e7d10d95102867c10d951001cfe76d91100067f65d91100067c65d9110076be64d9110004ff75d9110024fe75d9110004fd75d9110024fc75d9110014fe73d9110004fd73d9110014fc73d9110076bf43d911000cfe72d9110004fd72d911000cfc72d9110006be42d9110076bc42d911002cfe71d9110074fd71d911002cfc71d91100067f51d9110076bf41d9110034fe70d911002cfd70d9110034fc70d91100067c50d9110076bf40d91100057f755911007d7c75591100067f65591100067c6559110076bc6459110004ff75591100067f7559110
  | 7 => 0xca102167c654ca100267f76546100357c76546100267c76546100347c76546100067f64546102067e64546100067d64546102067c64546100067f63546101fe7e63546100067d63546101fe7c63546100067f62546101f67e62546100067d62546101f67c625461002d7f715461005f77715461002e7d615461007e7561546100077b70546100357e70546100357c705461000778705461003578705461002e7e605461002f77105461002f7b105461002f78105461001cff7650610034fc76506100067f65506101d67c655061001ebe6450610006bd6450610005fb7050610035f87050610014ff764c610034fc764c6100067f654c6101a67c654c610016de634c610006dd634c610005fb704c610035f8704c61000cff7648610034fc76486100067f65486101767c654861000eee6248610006ed624861002fe42148610005fb7048610035f87048610035f97690210036f9769021002cf976902100377b659021003778659021001efa6490210037ba6490210037b96490210036f86490210005f97390210097bb4390210007b94390210005f97290210036fb6290210006f9629021002dfa7190210037f27190210037f17190210035f871902102d77b519021000779519021004cff76502100057f755021005d7c75502100367f65502100367c6550210036bf6450210036bc64502100377a5050210037785050210037b84050210005fb765021004efb76502100077b75502102cf7875502100377b6550210037786550210037bb7450210037bb645021001efa645021001ef86450210037b86450210097ba54502102cfb95450210005fb7350210005fb7250210006fb6250210006f9625021002dfa715021002df871502102cf7b5150210007795150210097bb4150210007b94150210035f9768c210036f9768c21002cf9768c2100377b658c21003778658c210035fb748c210005f9748c210016fa638c210037da638c210037d9638c210036f8638c21008fda438c210007d9438c210005f9728c210036fb628c210006f9628c21002dfa718c210037f2718c210037f1718c210035f8718c2102c77b518c21000779518c210044ff764c2100057f754c21005d7c754c2100367f654c2100367c654c210036df634c210036dc634c2100377a504c21003778504c210037d8304c210005fb764c210046fb764c2100077b754c2102bf78754c2100377b654c21003778654c210005fb744c210005f9744c210037db734c210037db634c210016fa634c210016f8634c210037d8634c21008fda534c2102bfd9534c210005fb724c210006fb624c210006f9624c21002dfa714c21002df8714c2102bf7b514c21000779514c21008fdb314c210007d9314c210035f97688210036f9768821002cf976882100377b65882100e6fa6588210036f
  | 8 => 0x367c30d96100367f20d96100367e20d96100367c20d96100367f10d96100367c10d9610034ff75d9210024fe75d9210004fd75d9210034fc75d9210094fd74d9210014fe73d9210004fd73d9210034fc73d9210096bf43d921000cfe72d9210004fd72d9210034fc72d9210036f571d92100067f51d9210036fa70d92100367e50d92100367c50d9210036bf40d921001cff76592100057f755921005d7c75592100367f65592100367c6559210036bc6459210004ff75592100067f75592100047f7559210024fe7559210004fd7559210024fc75592100067c75592100247c7559210036bf7459210096be5459210006bd5459210004ff7359210014fe7359210014fc7359210004ff725921000cfe725921000cfc72592100067f5159210096bf4159210034fc70592100367e50592100367c5059210036be4059210036bc4059210034ff75d8e10024fe75d8e10004fd75d8e10034fc75d8e1001cfe74d8e10004fd74d8e10034fc74d8e1008cfd73d8e1008ede43d8e1000cfe72d8e10004fd72d8e10034fc72d8e10036f571d8e100067f51d8e10036fa70d8e100367e50d8e100367c50d8e10036df30d8e10014ff7658e100057f7558e1005d7c7558e100367f6558e100367c6558e10036dc6358e10004ff7558e100067f7558e100047f7558e10024fe7558e10004fd7558e10024fc7558e100067c7558e100247c7558e10004ff7458e1001cfe7458e1001cfc7458e10036df7358e1008ede5358e10006dd5358e10004ff7258e1000cfe7258e1000cfc7258e100067f5158e1008edf3158e10034fc7058e100367e5058e100367c5058e10036de3058e10036dc3058e10004ff7650e10034fe7650e10004fd7650e10034fc7650e100067f6550e102367c6550e10006bf6450e1001ebc6450e10006df6350e10016dc6350e1008f9c4350e10034ff75d8a10024fe75d8a10004fd75d8a10034fc75d8a1001cfe74d8a10004fd74d8a10034fc74d8a10014fe73d8a10004fd73d8a10034fc73d8a10084fd72d8a10036f571d8a100067f51d8a10036fa70d8a100367e50d8a100367c50d8a10036ef20d8a1000cff7658a100057f7558a1005d7c7558a100367f6558a100367c6558a10036ec6258a10004ff7558a100067f7558a100047f7558a10024fe7558a10004fd7558a10024fc7558a100067c7558a100247c7558a10004ff7458a1001cfe7458a1001cfc7458a10004ff7358a10014fe7358a10014fc7358a10036ef7258a10086ee5258a10006ed5258a100067f5158a10086ef2158a10034fc7058a100367e5058a100367c5058a10036ee2058a10036ec2058a10004ff7650a10034fe7650a10004fd7650a10034fc7650a100067f6550a102267c6550a10004ff764ca10034fe764ca10004fd764ca10034fc764ca100067f654
  | 9 => 0xe6250b10006ed6250b10004ff764cb1002cfe764cb10004fd764cb1002cfc764cb102167e654cb100067d654cb10016de634cb10006dd634cb1000eee624cb10006ed624cb1002f77765471002d7776547100567776547100077774547102f77674547100077574547102f774745471002f77645471002f76645471002f75645471002f7464547100077773547102ef7673547100077573547102ef74735471002f77635471002f76635471002f75635471002f7463547102f77743547102ef7643547100077543547102ef7443547100077772547102e77672547100077572547102e774725471002f77625471002f76625471002f75625471002f7462547102f77742547102e77642547100077542547102e77442547102ef7732547102e77632547100077532547102e77432547100b77770547100077670547100077570547100077470547100357470547102f77740547102f77440547102ef7730547102ef7430547102e77720547102e77420547102857d76943100367d769431007c7d76943102867f649431015e7e64943100067d64943102867c64943102867f63943101567e63943100067d63943102867c63943102867f629431014e7e62943100067d62943102867c62943100377771943102857d71943100377471943100367e61943100357e70943100377a70943100377a1094310037741094310074fd76903101467e65903100067d659031000775519031001cff765031002cfc76503100057f75503100b57c755031012e7e65503100067d655031001ebe6450310006bd6450310005f7715031002df4715031000775515031006cfd768c3101167e658c3100067d658c31000775518c310014ff764c31002cfc764c3100057f754c3100b57c754c3100fe7e654c3100067d654c310016de634c310006dd634c310005f7714c31002df4714c31000775514c310064fd76883100e67e65883100067d658831000775518831003778508831000cff764831002cfc76483100057f75483100b57c75483100ce7e65483100067d654831000eee6248310006ed6248310005f7714831002df471483100077551483102df7850483100367f74d96100367e74d96100367d74d96100367c74d96100367f73d96100367e73d96100367d73d96100367c73d96100067f43d96100067e43d96100067c43d96100367f72d96100367e72d96100367d72d96100367c72d96100067f42d96100067e42d96100067c42d96100067f32d96100067e32d96100067c32d96100367d71d96100367571d96100067f41d96102867e41d96102867c41d96100067f31d96102867e31d96102867c31d96100067f21d96102867e21d96102867c21d96100367e70d96100367a70d96100367f40d96100367e40d96100367c40d96100367f30d96100367e30d9610
  | 10 => 0xc12000dfa724c12000df8724c1200efe8724c1200eefb624c1200efea524c12030fe9524c120005fb714c120006fb614c12030f7b514c12000779514c1200bfdb314c120007d9314c1200efeb214c120007e9214c120035ef7588120305ed75881200076f65881202ff6c6588120005ed71881202ff6f51881200076d5188120035ee7088120037ea7088120036ef608812000feb60881202ffeb50881200376e50881200376c5088120037e85088120037685088120037ea4088120007e94088120037ea3088120007e930881200067f74597100067e74597100067d74597100067c74597100067f73597100067e73597100067d73597100067c73597100067f43597100067e43597100067c43597100067f72597100067e72597100067d72597100067c72597100067f42597100067e42597100067c42597100067f32597100067e32597100067c325971002e7f715971002e7e715971002e7d715971002e7c715971002e7f415971002e7e415971002e7d415971002e7c415971002e7f315971002e7e315971002e7d315971002e7c315971002e7f215971002e7e215971002e7d215971002e7c21597100b67f70597100b67e70597100067d70597100b67c70597100067f40597100067c40597100067f30597100067c30597100067f20597100067c205971002e7f105971002e7e105971002e7d105971002e7c1059710004ff7559310024fe7559310004fd7559310024fc755931002ebf7459310004ff7359310014fe7359310014fc73593100aebf4359310004ff725931000cfe725931000cfc72593100aebf425931002cfc715931002e7f515931002e7d515931002ebe415931002ebc41593100067c50593100aebf405931002efa105931002ef91059310004ff7558f10024fe7558f10004fd7558f10024fc7558f10004ff7458f1001cfe7458f1001cfc7458f1002edf7358f100a6de4358f10004ff7258f1000cfe7258f1000cfc7258f100a6df3258f1002cfc7158f1002e7f5158f1002e7d5158f1002ede3158f1002edc3158f100067c5058f100a6df3058f1002efa1058f1002ef91058f10004ff7650f1002cfe7650f10004fd7650f1002cfc7650f102367e6550f100067d6550f1001ebe6450f10006bd6450f10016de6350f10006dd6350f100a79c4350f10004ff7558b10024fe7558b10004fd7558b10024fc7558b10004ff7458b1001cfe7458b1001cfc7458b10004ff7358b10014fe7358b10014fc7358b1002eef7258b1009eee4258b1009eee3258b1002cfc7158b1002e7f5158b1002e7d5158b1002eee2158b1002eec2158b100067c5058b1009eef2058b1002efa1058b1002ef91058b10004ff7650b1002cfe7650b10004fd7650b1002cfc7650b102267e6550b100067d6550b1001ebe6450b10006bd6450b1000ee
  | 11 => 0xfeb6048520357eb50485203576c5048520357e8504852035768504852034d7e76941200367e769412034c7e76941200067f649412015e7e64941200067d649412015e7c64941200067f63941201567e63941200067d63941201567c63941200376f72941200376c72941200367f62941200057d71941200067f61941202867c619412014f6f21941200076d21941200357e70941200377a709412034d7a70941200367f609412014f7b20941200376c2094120037782094120344fe76901200067f65901201467c65901200377a5090120037785090120345fa769012033efa76901200cdfa75901200cdf875901200077b659012033778659012011df9749012001efa649012001ef86490120005f973901200c7bb4390120007b9439012000dfa729012000df87290120036fb6290120137ea5290120337e95290120005f97190120006fb61901203377b5190120007795190120137eb2190120007e9219012001cff765012000cfe765012011cfd765012000cfc76501200057f75501200cd7c75501200067f655012012e7c6550120006bf645012001ebc6450120005ef725012000dec72501200077a505012032f78505012000df8765012001ef8765012000cf876501200077b75501200cdfa75501200cdf8755012032f7875501200cd7875501200077b655012032f786550120135fb7450120007bb7450120007bb645012001efa645012001ef864501200c7b864501200c7ba545012032fb95450120005fb7350120007eb725012000dfa725012000df8725012011fe8725012011efb625012011fea525012032fe95250120005fb7150120006fb615012032f7b51501200077951501200c7bb4150120007b9415012011feb2150120007e92150120324fe768c1200067f658c1201167c658c1200377a508c12003778508c120325fa768c12031efa768c1200cdfa758c1200cdf8758c1200077b658c12031778658c120005fb748c120005f9748c1200edf9738c120016fa638c120016f8638c1200bfda438c120007d9438c12000dfa728c12000df8728c120036fb628c120107ea528c120317e9528c120005f9718c120006fb618c1203177b518c12000779518c120107eb218c120007e9218c120014ff764c12000cfe764c1200ecfd764c12000cfc764c1200057f754c1200cd7c754c1200067f654c1200fe7c654c120006df634c120016dc634c120005ef724c12000dec724c1200077a504c12030f78504c12000df8764c120016f8764c12000cf8764c1200077b754c1200cdfa754c1200cdf8754c12030f78754c1200cd78754c1200077b654c12030f78654c120005fb744c120005f9744c120105fb734c120007db734c120007db634c120016fa634c120016f8634c1200bfd8634c1200bfda534c12030fd9534c120007eb724
  | 12 => 0xf2158d20394ff7058d20006fb7058d200067c5058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d202367c6550d20006bf6450d2001ebc6450d20006df6350d20016dc6350d200bf9c4350d20005ef7250d2000dec7250d2038f785050d200cd7c75d85200067f65d85200067c65d85200077850d8520004ff75d85200067f75d8520024fe75d8520004fd75d8520024fc75d85200067c75d85200247c75d852001cfe74d8520004fd74d852001cfc74d8520014fe73d8520004fd73d8520014fc73d85200067f51d8520086f621d8520086f521d8520034fe70d85200067c50d85200cd7e75985200057d75985200067f65985200067c6598520006f76198520065f970985200077850985200057f75585200cd7c75585200067f65585200067c6558520005bf74585200c5bc7458520005df73585200bddc735852009dfb70585200077850585200cd7e75185200057d75185200067f65185200067c65185200c5be7418520005bd74185200bdde7318520005dd731852002ef66118520006f561185200077850185200067f76545200057e76545200067e76545200047e76545200067d76545200057c76545200067c76545200047c76545200067f64545202067e64545200067d64545202067c64545200067f63545201fe7e63545200067d63545201fe7c63545201f76e72545200076d72545201f67f62545203857f71545200cf7771545200067f615452002e7e615452002e7c61545201f76f21545200077b70545200357c70545200077870545200057870545201f67f60545201f77b20545201f76c20545201f7782054520004fe7690520004fd769052002cfc76905200cd7e75905200057d75905200067f65905201ee7c6590520006bf649052001ebc649052000dee7290520005ed7290520005fa7090520005f9709052037f785090520004ff7650520004fe7650520004fc76505200067f65505201d67c655052001ebe6450520006bd6450520377785050520004fe768c520004fd768c52002cfc768c5200cd7e758c5200057d758c5200067f658c5201be7c658c520006df638c520016dc638c52000dee728c520005ed728c520005fa708c520005f9708c52036f78508c520004ff764c520004fe764c520004fc764c5200067f654c5201a67c654c520016de634c520006dd634c52036778504c52002cec764852035def754852035ded75485200076f65485203576c6548520006ef6448520006ed6448520006ef6348520006ed634852000def714852000fe77148520007e7614852002eee614852002eec6148520007e4614852002ee461485203576f51485200076d5148520007e64148520007e54148520007e63148520007e53148520007eb7048520035ec7048520007e8704852000eef6048520
  | 13 => 0x95200076f72d952014f6c72d95200057d71d952014f6f21d95200cf7a70d952014f7970d95200357c70d952014f7b20d952014f6c20d952014f7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067c43d952014e7f72d952014e7e72d952014e7d72d952014e7c72d952014e7f42d952014e7e42d952014e7d42d952014e7c42d952014e7f32d952014e7e32d952014e7d32d952014e7c32d95200067f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067c31d952014e7f21d952014e7e21d952014e7d21d952014e7c21d952014e7f70d95200ce7e70d95200ce7a70d952014e7d70d952014e7970d952014e7c70d95200067f40d95200067c40d95200067f30d95200067c30d952014e7f20d952014e7e20d952014e7d20d952014e7c20d952001cfe76d91200067f65d91200067c65d91200c6be64d91200077850d9120004ff75d9120024fe75d9120004fd75d9120024fc75d9120014fe73d9120004fd73d9120014fc73d91200c6bf43d9120034ff72d912000cfe72d9120134fd72d912000cfc72d9120136bf42d9120136bd42d912002cfe71d9120004fd71d91200067f51d91200c6bc41d9120136ef21d912000cfd70d91200067c50d91200c6bf40d91200057f75591200cd7c75591200067f65591200067c65591200c6bc645912039dfb7059120007785059120004ff75591200067f75591200047f7559120024fe7559120004fd7559120024fc75591200067c75591200247c7559120134ff7459120006bf7459120004ff7359120014fe7359120014fc735912011cff7259120006ef7259120004ff715912002cfc71591200067f51591200c6bf415912011eef215912039cff7059120006fb70591200067c5059120014fe76d8d200067f65d8d200067c65d8d200bede63d8d200077850d8d20004ff75d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d200bede43d8d20034ff72d8d2000cfe72d8d20104fd72d8d2000cfc72d8d20106df32d8d20106dd32d8d2002cfe71d8d20004fd71d8d200067f51d8d200bedc31d8d20106ef21d8d2000cfd70d8d200067c50d8d200bedf30d8d200057f7558d200cd7c7558d200067f6558d200067c6558d200bedc6358d20395fb7058d20007785058d20004ff7558d200067f7558d200047f7558d20024fe7558d20004fd7558d20024fc7558d200067c7558d200247c7558d20004ff7458d2001cfe7458d2001cfc7458d20104ff7358d20006df7358d200ecff7258d20006ef7258d20004ff7158d2002cfc7158d200067f5158d200bedf3158d200eee
  | 14 => 0x67f5158620006f65158620006f55158620066f62158620066f5215862002cff7058620034fc70586200367e50586200367c5058620066ef2058620036f61058620036f410586200067f76546200067e76546200067d76546200067c76546200067f64546202067e64546200067d64546202067c64546200067f63546201fe7e63546200067d63546201fe7c63546201f67d62546203857f71546200e777715462002e7e615462000776615462002e7661546200067d615462000775615462000675615462002e7c61546200077b70546200357c70546200077870546200357870546201f67e60546201f76f20546201f77b20546201f778205462002cff7690620034fe7690620004fd76906200e57e75906200057d7590620035fa7090620005f970906203ef785090620004ff7650620004fd7650620034fc765062001ebe6450620006bd64506203e778505062002cff768c620034fe768c620004fd768c6200e57e758c6200057d758c620035fa708c620005f9708c6203df78508c620004ff764c620004fd764c620034fc764c620016de634c620006dd634c6203d778504c620035f97690220036f9769022000cf976902200e5fa7590220035f8759022001efa6490220037ba6490220037b96490220036f86490220005f973902200dfbb4390220007b9439022000dfa7290220037ea7290220037e97290220035f87290220005f97190220006f961902203cf7b519022000779519022039cff76502200057f75502200e57c75502200377a505022003778505022039dfb76502203c6fb76502200077b75502200e5fa75502200e5f875502203bf7875502200e5787550220037bb745022001efa645022001ef864502200dfba54502203bfb95450220005fb735022000dfa725022000df87250220005fb7150220006f961502203bf7b51502200077951502200dfbb4150220007b94150220035f9768c220036f9768c22000cf9768c2200e5fa758c220035f8758c220035fb748c220005f9748c220016fa638c220037da638c220037d9638c220036f8638c2200d7da438c220007d9438c22000dfa728c220037ea728c220037e9728c220035f8728c220005f9718c220006f9618c2203b77b518c22000779518c220394ff764c2200057f754c2200e57c754c2200377a504c22003778504c220395fb764c2203aefb764c2200077b754c2200e5fa754c2200e5f8754c2203a778754c2200e578754c220005fb744c220005f9744c220037db734c220016fa634c220016f8634c2200d7da534c2203a7d9534c22000dfa724c22000df8724c220005fb714c220006f9614c2203a77b514c22000779514c2200d7db314c220007d9314c22034d7e76d95200ce7e76d95200247e76d95200067e64d95200067c64d95200067e63d95200067c63d
  | 15 => 0xf629413014e7e629413014e7c62941300057d71941300067f61941302867c61941301575f31941300075d31941300357e70941300377a70941300367f60941301577b30941300375c309413003778309413040cfe76901300067f65901301467c659013001ebe6490130006bd6490130037d8309013001cff7650130014fe7650130124fd7650130014fc76501300057f75501300fd7c75501300067f655013012e7c6550130006bf645013001ebc6450130005df7350130015dc7350130127d83050130035df758c130405dd758c1300075f658c1303ff5c658c130006df648c130006dd648c130005dd718c1303ff5f518c1300075d518c130035de708c130037da708c130036df608c130017db608c1300375e508c1300375c508c130034ff75d9220024fe75d9220004fd75d9220034fc75d922011cfd74d9220014fe73d9220036de73d9220014de73d9220004fd73d9220036dd73d9220004dd73d9220034fc73d92200debf43d9220036ed72d922002cfe71d9220004fd71d92200067f51d9220034fe70d9220036fa70d92200367e50d92200367c50d922001cff7659220036bc6459220037785059220004ff7559220024fe7559220004fd7559220024fc7559220036bf74592200debe5459220006bd5459220004ff7359220014fe7359220014fc7359220006be43592200debc435922011ebf425922011ebd4259220004ff715922002cfc71592200067f51592200debf4159220034fe7059220034fc70592200367e50592200367c5059220036be4059220036bc4059220034ff75d8e20024fe75d8e20004fd75d8e20034fc75d8e2001cfe74d8e20036be74d8e2001cbe74d8e20004fd74d8e20036bd74d8e20004bd74d8e20034fc74d8e200ecfd73d8e200d6de43d8e20036ed72d8e2002cfe71d8e20004fd71d8e200067f51d8e20034fe70d8e20036fa70d8e200367e50d8e200367c50d8e20014ff7658e20036dc6358e20037785058e20004ff7558e20024fe7558e20004fd7558e20024fc7558e20004ff7458e2001cfe7458e2001cfc7458e20036df7358e200d6de5358e20006dd5358e20006df4358e200d6dc4358e200eedf3258e200eedd3258e20004ff7158e2002cfc7158e200067f5158e200d6df3158e20034fe7058e20034fc7058e200367e5058e200367c5058e20036de3058e20036dc3058e20004ff7650e20034fe7650e20004fd7650e20034fc7650e20006bf6450e2001ebc6450e20006df6350e20016dc6350e200d79c4350e203f7785050e200e57e75986200057d7598620036f76198620036f46198620037785098620036f46158620037785058620004ff7558620024fe7558620004fd7558620024fc7558620004ff745862001cfe745862001cfc7458620004ff7358620014fe7358620014fc7358620
  | 16 => 0x89300eeee62d8930004ff75d8930024fe75d8930004fd75d8930024fc75d893001cfe74d8930004fd74d893001cfc74d893000cfc73d89300eeee32d89300d6ed32d893002cfe71d8930004fd71d89300067f51d89300d6df31d8930014fd70d89300067c50d89300eeef20d89300057f75589300fd7c75589300067f65589300067c65589300eeec625893031dfb7058930004ff7650930004fe7650930004fc76509300067f65509302267c6550930005df7350930015dc73509300fd7c75d85300067f65d85300067c65d8530004ff75d85300067f75d8530024fe75d8530004fd75d8530024fc75d85300067c75d85300247c75d853001cfe74d8530004fd74d853001cfc74d853000cfe72d8530004fd72d853000cfc72d85300067f51d853008ef631d853008ef531d85300067c50d85300fd7e75985300057d75985300067f65985300067c6598530006f7619853006df970985300057f75585300fd7c75585300067f65585300067c65585300a5fb70585300fd7e75185300057d75185300067f65185300067c65185300f5be7418530005bd74185300edee7218530005ed721853002ef66118530006f561185300067f76545300057e76545300067e76545300047e76545300067d76545300057c76545300067c76545300047c76545300067f64545302067e64545300067d64545302067c64545301ff5e73545300075d73545301fe7f63545300067f62545301f67e62545301f67c625453042d7f71545300ff7771545300067f615453002e7e615453002e7c61545301ff5f31545300357c70545301fe7f60545301ff7b30545301ff5c30545301ff783054530004fe7690530004fd769053002cfc76905300fd7e75905300057d75905300067f65905301ee7c6590530015de7390530005dd7390530005fa7090530005f97090530004ff7650530004fe7650530004fc76505300067f65505301d67c655053001ebe6450530006bd645053002cdc764c530425df754c530425dd754c5300075f654c53041f5c654c530006df644c530006dd644c530006df624c530015df714c530017d7714c530007d7614c53002ede614c53002edc614c530007d4614c53041f5f514c5300075d514c530007db704c530035dc704c530007d8704c530016df604c530017db604c53041f5c504c530004fe7688530004fd768853002cfc76885300fd7e75885300057d75885300067f658853018e7c6588530015de7388530005dd7388530007d53188530005fa7088530005f97088530004ff7648530004fe7648530004fc76485300067f65485301767c654853000eee6248530007d531485304157e76941300367e76941304147e76941300067f649413015e7e64941300067d649413015e7c64941300375f73941300375c73941300367f63941300067
  | 17 => 0x2e7e615463000776615463002e7661546300067d615463000775615463000675615463002e7c61546300357c70546301fe7e60546301ff5f30546301ff7b30546301ff78305463002cff7690630034fe7690630004fd76906301157e75906300057d7590630035fa7090630005f97090630004ff7650630004fd7650630034fc765063001ebe6450630006bd64506300079d435063002cff7688630034fe7688630004fd76886301157e75886300057d7588630035fa7088630005f97088630004ff7648630004fd7648630034fc7648630005df7348630015dc734863000eee6248630006ed6248630434ff76502300057f75502301157c7550230015de73502304157e76d95300fe7e76d95300247e76d95300067e64d95300067c64d95300075f73d95301575c73d95300067e62d95300067c62d95300057d71d95301575f31d95300357c70d95301577b30d95301575c30d95301577830d95300067f74d95300067e74d95300067d74d95300067c74d95301567f73d95301567e73d95301567d73d95301567c73d95301567f43d95301567e43d95301567d43d95301567c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067c42d95301567f32d95301567e32d95301567d32d95301567c32d95300067f71d95300067e71d95300067d71d95300047d71d95300067c71d95300067f41d95300067c41d95301567f31d95301567e31d95301567d31d95301567c31d95300067f21d95300067c21d95301567f70d95300fe7e70d95301567d70d95301567c70d95300067f40d95300067c40d95301567f30d95301567e30d95301567d30d95301567c30d95300067f20d95300067c20d953001cfe76d91300067f65d91300067c65d91300f6be64d9130004ff75d9130024fe75d9130004fd75d9130024fc75d9130034ff73d9130014fe73d913013cfd73d9130014fc73d913013ede53d9130006dd53d913013ebf43d913013ebd43d913000cfe72d9130004fd72d913000cfc72d913002cfe71d9130004fd71d91300067f51d913013edf31d9130014fd70d91300067c50d91300f6bf40d913013edc30d91300057f75591300fd7c75591300067f65591300067c65591300f6bc6459130435fb7059130004ff75591300067f75591300047f7559130024fe7559130004fd7559130024fc75591300067c75591300247c755913013cff7459130006bf74591300f6be5459130006bd5459130124ff7359130006df7359130126de5359130006dd5359130004ff725913000cfe725913000cfc7259130004ff715913002cfc71591300067f51591300f6bf4159130126df3159130434ff7059130006fb70591300067c50591300f6bc4059130126dc305913000cfe76d89300067f65d89300067c65d
  | 18 => 0xf61941402867c619414015f3f41941400073d41941400357e70941400377a70941400367f609414015f7b40941400373c4094140037784094140035bf7590140455bd75901400073f659014044f3c6590140006bf6390140005bd719014044f3f51901400073d5190140035be7090140037ba7090140036bf609014001fbb60901400373e50901400373c5090140034ff75d9230024fe75d9230004fd75d9230034fc75d9230124fd74d9230036dd73d923000cfe72d9230036ee72d923000cee72d9230004fd72d9230036ed72d9230004ed72d9230034fc72d923002cfe71d9230004fd71d92300067f51d9230034fe70d9230036fa70d92300367e50d92300367c50d923001cff7659230036bc6459230004ff7559230024fe7559230004fd7559230024fc7559230036bf745923010ebe5459230006bd5459230126bf4359230126bd4359230004ff725923000cfe725923000cfc7259230006be425923010ebc4259230004ff715923002cfc71592300067f515923010ebf4159230034fe7059230034fc70592300367e50592300367c5059230036be4059230036bc405923010ddf7650e3001edf7650e3001cdf7650e30446df6550e30446dd6550e30015df7450e300179f7450e3001ede6450e3010f9e6450e3001e9e6450e300079d6450e3001edc6450e3010f9e5450e304479d5450e3010f9f4250e304475f5150e3010f9f4150e30005df7050e30007db7050e30007d87050e30016de6050e30017da6050e3043f5e5050e3043f5c5050e3043f9e4050e3043f9c4050e3000cff7658a30036ec6258a30004ff7558a30024fe7558a30004fd7558a30024fc7558a30004ff7458a3001cfe7458a3001cfc7458a300bede4358a30006dd4358a30106ee5258a30006ed5258a30006ef4258a30106ec4258a30106ee3258a300beed3258a30004ff7158a3002cfc7158a300067f5158a30106ef2158a30034fe7058a30034fc7058a300367e5058a300367c5058a30036ee2058a30036ec2058a30004ff7650a30004fd7650a30034fc7650a300079d4350a301157e75986300057d7598630036f76198630036f46198630036f46158630004ff7558630024fe7558630004fd7558630024fc7558630004ff745863001cfe745863001cfc745863006ede4358630006dd4358630004ff725863000cfe725863000cfc72586300067f5158630006f65158630006f5515863006ef6315863006ef53158630034fc70586300367e50586300367c505863006edf3058630036f61058630036f410586300067f76546300067e76546300067d76546300067c76546300067f64546302067e64546300067d64546302067c64546301fe7d63546301ff5e43546300075d43546301f67e62546300067d62546301f67c625463042d7f7154630117777154630
  | 19 => 0x894011eee62d8940004ff75d8940024fe75d8940004fd75d8940024fc75d894000cfc74d8940014fe73d8940004fd73d8940014fc73d894011eee42d89400deed42d894002cfe71d8940004fd71d89400067f51d89400debf41d894001cfd70d89400067c50d894011eef20d89400057f755894012d7c75589400067f65589400067c655894011eec625894033dfb7058940004ff764c940004fe764c940004fc764c9400067f654c9402167c654c940005bf744c94001dbc744c94012d7c75d85400067f65d85400067c65d8540004ff75d85400067f75d8540024fe75d8540004fd75d8540024fc75d85400067c75d85400247c75d8540014fe73d8540004fd73d8540014fc73d854000cfe72d8540004fd72d854000cfc72d85400067f51d8540096f641d8540096f541d85400067c50d854012d7e75985400057d75985400067f65985400067c6598540006f76198540075f970985400057f755854012d7c75585400067f65585400067c65585400adfb705854012d7e75185400057d75185400067f65185400067c6518540125de7318540005dd731854011dee7218540005ed721854002ef66118540006f561185400067f76545400057e76545400067e76545400047e76545400067d76545400057c76545400067c76545400047c76545402073e74545400073d74545402067f64545400067f63545401fe7e63545401fe7c63545400067f62545401f67e62545401f67c62545404757f715454012f7771545400067f615454002e7e615454002e7c61545402073f41545400357c70545402067f60545402077b40545402073c405454020778405454002cbc765054046dbf755054046dbd75505400073f65505404673c6550540006bf6350540006bf625054001dbf715054001fb77150540007b7615054002ebe615054002ebc6150540007b461505404673f51505400073d5150540007bb7050540035bc7050540007b8705054001ebf605054001fbb60505404673c5050540004fe768c540004fd768c54002cfc768c54012d7e758c5400057d758c5400067f658c5401be7c658c54001dbe748c540005bd748c540005fa708c540005f9708c540004ff764c540004fe764c540004fc764c5400067f654c5401a67c654c540016de634c540004fe7688540004fd768854002cfc768854012d7e75885400057d75885400067f658854018e7c658854001dbe7488540005bd7488540007b54188540005fa7088540005f97088540004ff7648540004fe7648540004fc76485400067f65485401767c654854000eee6248540007b5414854045d7e76941400367e769414045c7e76941400373f74941400373c74941400367f64941400067f63941401567e63941401567c63941400067f629414014e7e629414014e7c62941400057d71941400067
  | 20 => 0x4fd7558640024fc7558640004ff7358640014fe7358640014fc7358640076bf4358640006bd4358640004ff725864000cfe725864000cfc72586400067f5158640006f65158640006f55158640076f64158640076f54158640034fc70586400367e50586400367c5058640076bf4058640036f61058640036f410586400067f76546400067e76546400067d76546400067c76546402067d64546401fe7e63546400067d63546401fe7c63546402073f43546400073d43546401f67e62546400067d62546401f67c62546404757f715464014777715464002e7e615464000776615464002e7661546400067d615464000775615464000675615464002e7c61546400357c70546402067e60546402073f40546402077b405464020778405464002cff768c640034fe768c640004fd768c6401457e758c6400057d758c640035fa708c640005f9708c640004ff764c640004fd764c640034fc764c640016de634c640006dd634c6400079d434c64002cff7688640034fe7688640004fd76886401457e75886400057d7588640035fa7088640005f97088640004ff7648640004fd7648640034fc7648640005bf744864001dbc744864000eee6248640006ed624864045d7e76d954012e7e76d95400247e76d95400073f74d954015f3c74d95400067e63d95400067c63d95400067e62d95400067c62d95400057d71d954015f3f41d95400357c70d954015f7b40d954015f3c40d954015f7840d954015e7f74d954015e7e74d954015e7d74d954015e7c74d95400067f73d95400067e73d95400067d73d95400067c73d954015e7f43d954015e7e43d954015e7d43d954015e7c43d95400067f72d95400067e72d95400067d72d95400067c72d954015e7f42d954015e7e42d954015e7d42d954015e7c42d95400067f32d95400067e32d95400067c32d95400067f71d95400067e71d95400067d71d95400047d71d95400067c71d954015e7f41d954015e7e41d954015e7d41d954015e7c41d95400067f31d95400067c31d95400067f21d95400067c21d954015e7f70d954012e7e70d954015e7d70d954015e7c70d954015e7f40d954015e7e40d954015e7d40d954015e7c40d95400067f30d95400067c30d95400067f20d95400067c20d9540014fe76d8d400067f65d8d400067c65d8d40126de63d8d40004ff75d8d40024fe75d8d40004fd75d8d40024fc75d8d40014fc74d8d4010ebe54d8d40006bd54d8d40126de43d8d4010edd43d8d4000cfe72d8d40004fd72d8d4000cfc72d8d4002cfe71d8d40004fd71d8d400067f51d8d4010ebf41d8d4001cfd70d8d400067c50d8d4010ebc40d8d40126df30d8d400057f7558d4012d7c7558d400067f6558d400067c6558d40126dc6358d4047dfb7058d4000cfe76d89400067f65d89400067c65d
  | 21 => 0xe434c6500075d434c6500057f724c65014d7e724c65014d7c724c6501575f324c6500075d324c6501557f714c6500067d614c65015777314c6502875e314c6502875c314c65015774314c6500057f704c6500357c704c6504167e604c6501a77a604c6501575f304c6502857f76886500357e76886502867e76886500347e76886500057d76886502867d76886500047d76886500357c76886502857f748865015d7e74886500057d74886502857c74886502857f73886501557e73886500057d73886502857c738865014d7d72886502857e71886502867d61886502877641886500077541886502877631886500077531886502876f218865014f7721886502877421886500357e70886500057d70886500357c708865048e7e608865018f7a60886500057f76486500357e76486500057d76486500357c76486500057f744865015d7e74486500057d744865015d7c74486500057f73486501557e73486500057d73486501557c73486502857f724865014f6e62486500076d624865014f6e42486500076d424865014f6e32486500076d324865014d7f71486500067d614865000776414865000775414865000776314865000775314865014f7721486502876e21486502876c214865014f7421486500057f70486500357c704865034e7e60486501777a604865014f6f2048650014ff7658e40036dc6358e40004ff7558e40024fe7558e40004fd7558e40024fc7558e4013ede5358e40006dd5358e4013ede4358e400f6dd4358e40004ff7258e4000cfe7258e4000cfc7258e40006de3258e4013edc3258e40004ff7158e4002cfc7158e400067f5158e4013edf3158e40034fe7058e40034fc7058e400367e5058e400367c5058e40036de3058e40036dc3058e4013dbf7650e40016bf7650e40014bf7650e40486bf6550e40486bd6550e4001dbf7350e4001f9f7350e40016be6350e4013f9e6350e400169e6350e400079d6350e40016bc6350e4013f9e5350e404879d5350e4013f9f3250e404873f5150e4013f9f3150e40005bf7050e40007bb7050e40007b87050e4001ebe6050e4001fba6050e4043f3e5050e4043f3c5050e4043f9c3050e4000cff7658a40036ec6258a40004ff7558a40024fe7558a40004fd7558a40024fc7558a40004ff7358a40014fe7358a40014fc7358a400c6bf4358a40006bd4358a40136ee5258a40006ed5258a40136ee4258a400c6ed4258a40006ef3258a40136ec3258a40004ff7158a4002cfc7158a400067f5158a40136ef2158a40034fe7058a40034fc7058a400367e5058a400367c5058a40036ee2058a40036ec2058a40004ff764ca40004fd764ca40034fc764ca400079d434ca401457e75986400057d7598640036f76198640036f46198640036f46158640004ff7558640024fe7558640
  | 22 => 0x86500377410986500357f76586500057f745865015d7e745865015d7c74586500367f64586500067e64586500067d64586500367c64586500057f73586501557e73586501557c73586500367f63586500067e63586500067d63586500367c63586500057f725865014d7e725865014d7c72586500367f62586500067e62586500067d62586500367c62586500357f71586500377761586502867e61586500367c61586500377461586500357e70586500357c70586500367e60586500377a60586500377610586500377410586500067f74586500067e74586500067d74586500067c74586500067f73586500067e73586500067d73586500067c73586500067f43586500067e43586500067d43586500067c43586500067f72586500067e72586500067d72586500067c72586500067f42586500067e42586500067d42586500067c42586500067f32586500067e32586500067d32586500067c32586500067f41586502867c41586500067f31586502867c31586500067f21586502867c21586500367e70586500367c70586500347c70586500067f40586500367e40586500367c40586500067f30586500367e30586500367c30586500067f20586500367e20586500367c20586500367e10586500367610586500367c10586500367410586502857f76906500357e76906502867e76906500347e76906500057d76906502867d76906500047d76906500357c769065015d7d74906501557e73906500057d73906502857c739065014d7e72906500057d72906502857c72906502857e71906502867d61906502873f419065015f7741906502877441906500357e70906500057d70906500357c709065048e7e60906501ef7a60906500057f76506500357e76506500057d76506500357c76506502857f745065015f3e64506500073d64506500057f73506501557e73506501557c735065015f3f43506500073d43506500057f725065014d7e725065014d7c725065015f3f42506500073d425065015d7f71506500067d615065015f7741506502873e41506502873c415065015f7441506500057f70506500357c705065045e7e60506501d77a605065015f3f40506502857f768c6500357e768c6502867e768c6500347e768c6500057d768c6502867d768c6500047d768c6500357c768c6502857f748c65015d7e748c6500057d748c6502857c748c6501557d738c65014d7e728c6500057d728c6502857c728c6502857e718c6502867d618c6502875f318c65015777318c65028774318c6500357e708c6500057d708c6500357c708c65048e7e608c6501bf7a608c6500057f764c6500357e764c6500057d764c6500357c764c6500057f744c65015d7e744c6500057d744c65015d7c744c6502857f734c6501575e634c6500075d634c6501575
  | 23 => 0x15e7e64592500367c64592500373c64592500363c64592500057f73592501557e73592501557c73592500367f63592500057f725925014d7e725925014d7c72592500367f62592500057f71592502857c71592500367f615925015f3f41592500357e70592500357c70592500367e60592500377a60592500373e40592500373c40592500357f7658e500057f7458e5015d7e7458e5015d7c7458e500367f6458e500067d6458e500357f7358e500375f6358e501567e6358e500367c6358e500375c6358e500057f7258e5014d7e7258e5014d7c7258e500367f6258e500057f7158e502857c7158e500367f6158e501575f3158e500357e7058e500357c7058e500367e6058e500377a6058e500375e3058e500375c3058e500057f7650e500357e7650e500057d7650e500357c7650e501557f7450e5043f3f6450e5043f3c6450e501557f7350e5043f5f6350e5043f5c6350e5015f5f4350e501573e4350e501573c4350e501575c4350e501571c4350e500057f7250e5014d7e7250e5014d7c7250e5015f3f4250e501575f3250e500057f7150e502857c7150e5015f3f4150e501575f3150e500057f7050e500357c7050e504167e6050e502377a6050e5043f3c4050e5043f5c3050e500357f7658a500057f7458a5015d7e7458a5015d7c7458a500367f6458a500067d6458a500057f7358a501557e7358a501557c7358a500367f6358a500067d6358a500357f7258a500376f6258a5014e7e6258a500367c6258a500376c6258a500057f7158a502857c7158a500367f6158a5014f6f2158a500357e7058a500357c7058a500367e6058a500377a6058a500ce7a6058a500376e2058a500376c2058a500057f7650a500357e7650a500057d7650a500357c7650a5014d7f7450a500057f7350a501557e7350a501557c7350a5015f3f4350a500073d4350a5014d7f7250a5015f6f4250a5014f3e4250a5014f3c4250a5014f6c4250a500057f7150a502857c7150a5015f3f4150a5014f6f2150a500057f7050a500357c7050a5034e7e6050a502277a6050a500057f764ca500357e764ca500057d764ca500357c764ca500057f744ca5015d7e744ca500057d744ca5015d7c744ca5014d7f734ca501575e434ca500075d434ca5014d7f724ca501576f324ca5014f5e324ca5014f5c324ca5014f6c324ca500057f714ca502857c714ca501575f314ca5014f6f214ca500057f704ca500357c704ca5034e7e604ca502177a604ca500357d769865015d7e74986500057d74986502857c74986501557e73986500057d73986502857c739865014d7e72986500057d72986502857c72986500357e71986500367f61986500377761986500367761986500377461986500357e70986500357c70986500367e60986500377a609865003776109
  | 24 => 0x6759052102f7575905211c5f5749052101ef6649052101ef46490521005f5739052102fe7729052100df6729052102df4729052102fe4729052102ef7629052102fe762905211dfe6429052116fe542905211dfe63290521007e532905214b77450905211dfe7209052101cff765052100cfe76505211c4fd765052100cfc7650521006bf645052101ebc6450521005ef725052100dec7250521007ad42505214af77515052100775515052102fb4415052102fe4215052100df4765052101ef4765052100cf4765052102df7745052102fb77450521007b7645052101ef6645052101ef4645052116fb46450521005f7735052116fb74350521007b54350521007e7725052100df6725052100df472505211c7e4725052102ef7625052102fe762505211c7b742505211c7e642505211c7b5425052116fe54250521007a542505211c7e63250521007e532505214af74505052116fb740505211c7e720505214a5f6768c52102ef6768c52102f76758c52102f75758c52102df7748c521005f5748c521195f5738c521016f6638c521016f4638c52102fe7728c52100df6728c52102df4728c52102fe4728c52102ef7628c52102fe7628c5211afe6428c521007e5428c5211afe6328c521167e5328c52149f74508c5211afe7208c521014ff764c52100cfe764c521194fd764c52100cfc764c521006df634c521016dc634c521005ef724c52100dec724c521007cd324c52149777514c52100775514c52102fd4314c52102fe4214c52100df4764c521016f4764c52100cf4764c521005f7744c521005f5744c52102df7734c52102fd7734c521007d7634c521016f6634c521016f4634c521167d4634c521167d6434c521007d5434c521007e7724c52100df6724c52100df4724c521197e4724c52102ef7624c52102fe7624c521197e6424c521007e5424c521197d7324c521197e6324c521197d5324c521167e5324c521007c5324c52149774504c521167d7304c521197e7204c5211757e75d81210057d75d8121004ff75d8121024fe75d81210067e75d81210247e75d8121004fd75d81210067d75d81210047d75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d8121014fe73d8121004fd73d8121014fc73d812102cfd72d81210067f51d81210067d51d81210067c50d812109efa20d8121006fb60981210057f75581211757c7558121005bf745812116dbc7458121005df7358121165dc7358121006f96018121034ff7518121024fe7518121004fd7518121034fc751812101cfe7418121004fd7418121034fc7418121014fe7318121004fd7318121034fc731812102cfd72181210067f51181210067d51181210367c5018121036ef2018121036fa201812103ef920181210357f76592500357f74592500373f6459250
  | 25 => 0x912116ebf41d9121034fe70d9121004fd70d91210067c50d912116ebc40d912116ebc6459121005df7359121165dc73591214ddf77159121004ff7559121024fe7559121004fd7559121024fc75591211dcff7459121006bf7459121004ff7359121006df7359121004df7359121014fe7359121014fc7359121006dc7359121014dc735912116ebf43591211c4ff7259121006ef72591214dcff7159121006f771591210067f5159121004ff7059121034fc70591210067c5059121014fe76d8d21166de63d8d21004ff75d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d21166de53d8d21006dd53d8d21006df43d8d21166dc43d8d2102cff72d8d2102cfd72d8d211aedf32d8d211aedd32d8d2100cfd71d8d210067f51d8d21166df31d8d21034fe70d8d21004fd70d8d210067c50d8d21166dc30d8d21005bf7458d2116dbc7458d21166dc6358d214d5f77158d21004ff7558d21024fe7558d21004fd7558d21024fc7558d21004ff7458d21006bf7458d21004bf7458d2101cfe7458d2101cfc7458d21006bc7458d2101cbc7458d211acff7358d21006df7358d21166de4358d21194ff7258d21006ef7258d214d4ff7158d21006f77158d210067f5158d21004ff7058d21034fc7058d210067c5058d21004ff7650d21004fe7650d21004fd7650d21004fc7650d2101ebe6450d21006bd6450d21016de6350d21006dd6350d211679c4350d2100dee7250d2102dec765092101eec765092102cec765092100def745092100faf7450921007af645092101eee645092101eec645092116fac6450921005ef735092116faf4350921007ad4350921007e7715092102dee715092102dec7150921007e4715092100eef615092100fe761509214cf6f515092116faf4150921005ef70509214cf6c505092102dec764c921016ec764c92102cec764c921005ef744c921005ed744c92100def734c92100fcf734c921007cf634c921016ee634c921016ec634c921167cc634c921167ce434c921007cd434c921007e7714c92102dee714c92102dec714c921007e4714c92100eef614c92100fe7614c9214c76f514c921167cf314c921005ef704c9214c76c504c9210267f76545211f67e76545211f67d76545210267c76545210067f64545212067e64545210067d64545212067c64545210067f63545211fe7e63545210067d63545211fe7c63545210076f72545211f76c725452102e7f62545211f76e42545210076d42545211f76e32545210076d325452102d7f715452117777715452102e7f615452102f76415452102f7631545211f777215452102f6e215452102f6c215452102f74215452102f6421545210057c70545211f76f205452102f7710545214bdf6769052102ef6769052102f7
  | 26 => 0x1f67f20596211f67e20596211f67d20596211f67c205962102e7f105962102e7e105962102e7d105962102e7c1059621004ff7559221024fe7559221004fd7559221024fc755922102ebf7459221004ff7359221014fe7359221014fc7359221186bf43592211c6bf42592211c6bd425922102cfe715922102cfc715922102e7f515922102e7d515922102ebe415922102ebc415922102eef215922102eed2159221004ff7059221034fc70592210067c5059221186bf4059221004ff7558e21024fe7558e21004fd7558e21024fc7558e21004ff7458e2101cfe7458e2101cfc7458e2102edf7358e2117ede4358e21196df3258e21196dd3258e2102cfe7158e2102cfc7158e2102e7f5158e2102e7d5158e2102ede3158e2102edc3158e2102eef2158e2102eed2158e21004ff7058e21034fc7058e210067c5058e2117edf3058e21004ff7650e2102cfe7650e21004fd7650e2102cfc7650e212367e6550e210067d6550e2101ebe6450e21006bd6450e21016de6350e21006dd6350e2117f9c4350e21005ef7250e2100dec7250e2102df67150e2102df776506214fef7765062102f76655062102f75655062102fb7745062102fb7645062101ef6645062102ef4645062102fb46450621005f77350621187b74350621007b5435062100df6725062100df472506211c7b742506211c7b542506214f7745050621187b7405062102df7764c6214eef7764c62102f76654c62102f75654c621005f7744c621005f5744c62102fd7734c62102fd7634c621016f6634c62102ef4634c62102fd4634c62117fd6434c621007d5434c62100df6724c62100df4724c621197d7324c621197d5324c6214e774504c62117fd7304c621034ff75982210367f7598221024fe7598221004fd7598221034fc75982210367c75982210347c759822101cfe7498221004fd7498221034fc7498221014fe7398221004fd7398221034fc739822102cfe7198221034fc719822102e7f519822102e7d5198221036fa70982210367c5098221036fa2098221086f9209822102efb1098221036f81098221004ff75582210067f75582210047f7558221024fe7558221004fd7558221024fc75582210067c75582210247c7558221004ff745822101cfe745822101cfc7458221004ff7358221014fe7358221014fc735822102cfc715822102e7f515822102e7d515822102eef215822102eed215822102efb70582210067c5058221066fa205822102efb105822102ef8105822101cfe76d912116ebe64d9121004ff75d9121024fe75d9121004fd75d9121024fc75d912116ebe54d9121006bd54d9121014fe73d9121004fd73d9121014fc73d9121006be43d912116ebc43d912102cff72d912102cfd72d91211debf42d91211debd42d912100cfd71d91210067f51d
  | 27 => 0xc625893150df77158931004ff7650931004fe7650931004fc765093101ebe6450931006bd6450931015de73509310079d435093102ddc764c93100edc764c93102cdc764c931005df744c931005dd744c931006df644c931006dd644c931015df724c931017cf724c931007cf624c93100ede624c93100edc624c931197cc624c931007d7714c93102dde714c93102ddc714c931007d4714c931016df614c931017d7614c9315075f514c931197cf214c931005df704c9315075c504c9310267f76545311fe7e76545311fe7d76545310267c76545310067f64545312067e64545310067d64545312067c64545310075f73545311ff5c735453102e7f63545311ff5e43545310075d43545310067f62545311f67e62545311f67c62545311ff5f32545310075d325453102d7f71545311a777715453102e7f61545311ff77315453102f5e315453102f5c315453102f74315453102f54315453102f7621545310057c70545311ff5f305453102f77105453101cff7650531014fe76505311ccfd7650531014fc7650531006bf645053101ebc6450531005df7350531015dc73505310079d43505311a57e75d81310057d75d81310077850d8131004ff75d8131024fe75d81310067e75d81310247e75d8131004fd75d81310067d75d81310047d75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d813102cfd73d813100cfe72d8131004fd72d813100cfc72d81310067f51d81310067d51d8131006fb50d81310067c50d8131006f850d81310067850d81310a6fa30d8131006fb60981310057f75581311a57c7558131006f96018131007785018131034ff7518131024fe7518131004fd7518131034fc751813101cfe7418131004fd7418131034fc741813102cfd7318131046de4318131006dd431813100cfe7218131004fd7218131034fc72181310067f51181310067d5118131006fb50181310367c5018131036f85018131036785018131036df3018131036fa3018131046f930181310067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067e43596210067c43596211f67f72596211f67e72596211f67d72596211f67c72596211f67f42596211f67e42596211f67d42596211f67c42596211f67f32596211f67e32596211f67d32596211f67c325962102e7f715962102e7e715962102e7d715962102e7c715962102e7f415962102e7e415962102e7d415962102e7c415962102e7f315962102e7e315962102e7d315962102e7c315962102e7f215962102e7e215962102e7d215962102e7c21596210067f70596210067e70596210067d70596210067c70596210347c70596210067f40596210067c40596210067f30596210067c3059621
  | 28 => 0x8a3102cfe7158a3102cfc7158a3102e7f5158a3102e7d5158a3102edf3158a3102edd3158a3102eee2158a3102eec2158a31004ff7058a31034fc7058a310067c5058a311aeef2058a31004ff7650a31004fd7650a3102cfc7650a312267e6550a310067d6550a3101ebe6450a31006bd6450a31005df7350a31015dc7350a3100eee6250a31006ed6250a31034ff75982310367f7598231024fe7598231004fd7598231034fc75982310367c75982310347c759823101cfe7498231004fd7498231034fc749823100cfe7298231004fd7298231034fc729823102cfe7198231034fc719823102e7f519823102e7d5198231036fa70982310367c5098231036fa309823108ef9309823102efb1098231036f81098231004ff75582310067f75582310047f7558231024fe7558231004fd7558231024fc75582310067c75582310247c7558231004ff745823101cfe745823101cfc7458231004ff725823100cfe725823100cfc725823102cfc715823102e7f515823102e7d515823102edf315823102edd315823102efb70582310067c505823106efa305823102efb105823102ef8105823101cfe76d913119ebe64d9131004ff75d9131024fe75d9131004fd75d9131024fc75d913102cff73d913102cfd73d91311e6bf43d91311e6bd43d913100cfe72d9131004fd72d913100cfc72d9131006be42d913119ebc42d91311e6df32d9131014fd71d91310067f51d913119ebf41d9131034fe70d9131004fd70d91310067c50d913119ebc6459131005ef7259131195ec725913151df77159131004ff7559131024fe7559131004fd7559131024fc75591311e4ff7459131006bf74591311ccff7359131006df7359131004ff7259131006ef7259131004ef725913100cfe725913100cfc7259131006ec725913100cec725913119ebf42591311cedf325913151cff7159131006f771591310067f5159131004ff7059131034fc70591310067c505913102ddc7650d3101edc7650d3102cdc7650d31516df6550d31516dd6550d31015df7450d310179f7450d310079f6450d3101ede6450d3101edc6450d3119f9c6450d3101e9c6450d3119f9e5450d315179d5450d31005df7250d3119f9f4250d31007d77150d3102dde7150d3102ddc7150d31007d47150d31016df6150d31017d76150d315175f5150d3119f9f4150d31005df7050d315175c5050d3119f9c4050d3100cfe76d8931196ee62d8931004ff75d8931024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d893102cfd73d893117ede43d8931006dd43d8931006ef42d8931196ec42d8931196ee32d893117eed32d8931014fd71d89310067f51d8931196ef21d8931034fe70d8931004fd70d89310067c50d8931005bf745893119dbc7458931196e
  | 29 => 0x267f76545412067e76545412067d76545410267c76545410073f74545412073c745454102e7f64545410067f63545411fe7e63545411fe7c63545412073f43545410073d43545410067f62545411f67e62545411f67c62545412073f42545410073d425454102d7f71545411d777715454102e7f615454120777415454102f3e415454102f3c415454102f74415454102f7621545410057c70545412073f405454102f7710545411d57e75d81410057d75d81410077850d8141004ff75d8141024fe75d81410067e75d81410247e75d8141004fd75d81410067d75d81410047d75d8141024fc75d814102cfd74d8141014fe73d8141004fd73d8141014fc73d814100cfe72d8141004fd72d814100cfc72d81410067f51d81410067d51d8141006fb50d81410067c50d8141006f850d81410067850d81410aefa40d8141006fb60981410057f75581411d57c7558141006f96018141007785018141034ff7518141024fe7518141004fd7518141034fc751814102cfd7418141014fe7318141004fd7318141034fc731814104ebf4318141006bd431814100cfe7218141004fd7218141034fc72181410067f51181410067d5118141006fb50181410367c5018141036f85018141036785018141036bf4018141036fa401814104ef940181410067f74596310067e74596310067d74596310067c74596311fe7f73596311fe7e73596311fe7d73596311fe7c73596311fe7f43596311fe7e43596311fe7d43596311fe7c43596310067f72596310067e72596310067d72596310067c72596310067f42596310067e42596310067c42596311fe7f32596311fe7e32596311fe7d32596311fe7c325963102e7f715963102e7e715963102e7d715963102e7c715963102e7f415963102e7e415963102e7d415963102e7c415963102e7f315963102e7e315963102e7d315963102e7c315963102e7f215963102e7e215963102e7d215963102e7c21596310067f70596310067e70596310067d70596310067c70596310347c70596310067f40596310067c40596311fe7f30596311fe7e30596311fe7d30596311fe7c30596310067f20596310067c205963102e7f105963102e7e105963102e7d105963102e7c1059631004ff7559231024fe7559231004fd7559231024fc755923102ebf74592311cebf43592311cebd4359231004ff725923100cfe725923100cfc72592311b6bf425923102cfe715923102cfc715923102e7f515923102e7d515923102ebe415923102ebc415923102edf315923102edd315923102ef62159231004ff7059231034fc70592310067c50592311b6bf4059231004ff7558a31024fe7558a31004fd7558a31024fc7558a31004ff7458a3101cfe7458a3101cfc7458a3102eef7258a311aeee4258a311aeee3258a31166ed325
  | 30 => 0xd4158a4102eee2158a4102eec2158a41004ff7058a41034fc7058a410067c5058a411deef2058a41004ff764ca41004fd764ca4102cfc764ca412167e654ca410067d654ca41005bf744ca4101dbc744ca41016de634ca41006dd634ca4100eee624ca41006ed624ca41034ff75982410367f7598241024fe7598241004fd7598241034fc75982410367c75982410347c7598241014fe7398241004fd7398241034fc739824100cfe7298241004fd7298241034fc729824102cfe7198241034fc719824102e7f519824102e7d5198241036fa70982410367c5098241036fa4098241096f9409824102efb1098241036f81098241004ff75582410067f75582410047f7558241024fe7558241004fd7558241024fc75582410067c75582410247c7558241004ff7358241014fe7358241014fc7358241004ff725824100cfe725824100cfc725824102cfc715824102e7f515824102e7d515824102ebf415824102ebd415824102efb70582410067c5058241076fa405824102efb105824102ef81058241014fe76d8d411cede63d8d41004ff75d8d41024fe75d8d41004fd75d8d41024fc75d8d4102cfd74d8d411cede43d8d411b6dd43d8d4100cfe72d8d41004fd72d8d4100cfc72d8d411b6bf42d8d41006de32d8d411cedc32d8d4101cfd71d8d410067f51d8d411cedf31d8d41034fe70d8d41004fd70d8d410067c50d8d411cedc6358d41005ef7258d411c5ec7258d4153df77158d4102dbc7650d41016bc7650d4102cbc7650d41536bf6550d41536bd6550d4101dbf7350d4101f9f7350d410079f6350d41016be6350d41016bc6350d411cf9c6350d410169c6350d411cf9e5350d415379d5350d41005bf7250d411cf9f3250d41007b77150d4102dbe7150d4102dbc7150d41007b47150d4101ebf6150d4101fb76150d415373f5150d411cf9f3150d41005bf7050d415373c5050d411cf9c3050d4100cfe76d89411c6ee62d8941004ff75d8941024fe75d8941004fd75d8941024fc75d894102cfd74d8941014fe73d8941004fd73d8941014fc73d8941186bf43d8941006bd43d89411c6ee42d8941186ed42d8941006ef32d89411c6ec32d894101cfd71d89410067f51d89411c6ef21d8941034fe70d8941004fd70d89410067c50d8941005df73589411cddc73589411c6ec625894152df7715894102dbc765094100ebc765094102cbc7650941005bf7350941006bf635094101dbf725094101faf7250941007af625094100ebe625094100ebc62509411c7ac6250941007b7715094102dbe715094102dbc7150941007b4715094101ebf615094101fb761509415273f51509411c7af2150941005bf70509415273c5050941004ff764c941004fe764c941004fc764c94101dbe744c941005bd744c941016de634c9410079d434c941
  | 31 => 0x81511f56e72181510057d72181510076d72181510056d72181511f57c72181510067f62181510067e62181510067d62181510067c62181510577571181510567f61181510577761181510067f60181510077a60181510067d60181510077960181510077b40181510077840181510077b30181510077830181510367f74181510367e74181510363e74181510367d74181510363d74181510367c74181510367f73181510367e73181510365e73181510367d73181510365d73181510367c73181510067f43181510067e43181510067d43181510067c43181510367f72181510367e72181510366e72181510367d72181510366d72181510367c72181510067f42181510067e42181510067d42181510067c42181510067f32181510067e32181510067d32181510067c32181510367f71181510367d71181510367571181510067f411815148e7e411815148e7c41181510067f311815148e7e311815148e7c31181510067f211815148e7e211815148e7c21181510367f40181510067b40181510367c40181510367840181510367f30181510067b30181510367c30181510367830181510367f20181510367c20181510367f10181510367c10181512067f74596412067e74596412067d74596412067c74596410067f73596410067e73596410067d73596410067c73596412067f43596412067e43596412067d43596412067c43596410067f72596410067e72596410067d72596410067c72596412067f42596412067e42596412067d42596412067c42596410067f32596410067e32596410067c325964102e7f715964102e7e715964102e7d715964102e7c715964102e7f415964102e7e415964102e7d415964102e7c415964102e7f315964102e7e315964102e7d315964102e7c315964102e7f215964102e7e215964102e7d215964102e7c21596410067f70596410067e70596410067d70596410067c70596410347c70596412067f40596412067e40596412067d40596412067c40596410067f30596410067c30596410067f20596410067c205964102e7f105964102e7e105964102e7d105964102e7c1059641004ff7558e41024fe7558e41004fd7558e41024fc7558e4102edf7358e411e6de4358e4119edd4358e41004ff7258e4100cfe7258e4100cfc7258e411e6df3258e4102cfe7158e4102cfc7158e4102e7f5158e4102e7d5158e4102ebf4158e4102ebd4158e4102ede3158e4102edc3158e4102ef62158e41004ff7058e41034fc7058e410067c5058e411e6df3058e41004ff7558a41024fe7558a41004fd7558a41024fc7558a41004ff7358a41014fe7358a41014fc7358a4102eef7258a411deee4258a4116eed4258a411deee3258a4102cfe7158a4102cfc7158a4102e7f5158a4102e7d5158a4102ebf4158a4102eb
  | 32 => 0x1fd7c73d89510067f63d89510067d63d89511f67e62d89511f76e62d89511f67c62d895102d7e71d89510257d71d895118e7f61d895118f7761d89511f76f21d89510057e70d89510057d70d89510057f74589512057e74589512057c74589510067f64589510067d64589510057f73589511fd7e73589511fd7c73589510067f63589510067d63589511f57f72589510076f62589511f67e62589511f67c62589511f76c62589515457f71589510077771589515457771589511767f61589511777761589510057f70589510057c70589511f76f20589510057f76509510057e76509510057d76509510057c76509511f57f74509510057f73509511fd7e73509511fd7c73509512073f43509510073d43509511f57f72509512076f42509511f73e42509511f73c42509511f76c42509510057f715095102d7e715095102d7c71509513867f61509512277761509512073f41509511f76f21509510057f70509510057c70509510057f764c9510057e764c9510057d764c9510057c764c9510057f744c9512057e744c9510057d744c9512057c744c9511f57f734c9511ff5e434c9510075d434c9511f57f724c9511ff6f324c9511f75e324c9511f75c324c9511f76c324c9510057f714c95102d7e714c95102d7c714c9513867f614c95121777614c9511ff5f314c9511f76f214c9510057f704c9510057c704c9512057e74d81510057d74d81512057c74d81511fd7e73d81510057d73d81511fd7c73d81511f57e72d81510057d72d81511f57c72d81510b77771d81510b67f61d81510b77761d81510077b40d81510077840d81510077b30d81510077830d81512057e74981510057d74981512057c74981510067f64981510067e64981510067d64981510067c64981511fd7e73981510057d73981511fd7c73981510067f63981510067e63981510067d63981510067c63981511f57e72981510057d72981511f57c72981510067f62981510067e62981510067d62981510067c629815107d7d719815100775719815107d75719815105e7f619815105f7761981510557e70981510067f60981510077b60981510057f74581512057e74581512057c74581510057f73581511fd7e73581511fd7c73581510057f72581511f57e72581511f57c725815105d7f715815100777715815105d77715815107e7f615815107f7761581510077b60581510067e60581510b57e76181512057e74181510073e74181512053e74181510057d74181510073d74181510053d74181512057c74181510067f64181510067e64181510067d64181510067c64181511fd7e73181510075e73181511fd5e73181510057d73181510075d73181510055d73181511fd7c73181510067f63181510067e63181510067d63181510067c63181511f57e72181510076e721
  | 33 => 0xe75d81320067e75d81320247e75d8132004fd75d81320067d75d81320047d75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d813200cfd73d8132014fd72d813202cfe71d8132004fd71d81320067f51d813231edf31d8132396ef21d81320067c50d813231efa30d8132396fa20d813220dbe7498132005bd7498132006fb60981320057f75581322157c7558132006f96018132034ff7518132024fe7518132004fd7518132034fc751813201cfe7418132004fd7418132034fc741813200cfd73181323aede4318132006dd4318132014fd721813202cfe7118132004fd71181320067f51181320367c5018132036fa30181323aef93018132036fa2018132326f920181322057e76d91512067e64d91512073e64d91512063e64d91512067c64d91511fd7e73d91510057d73d91511fd7c73d91511f57e72d91510057d72d91511f57c72d915102d7e71d91510257d71d91511ee7f61d91511ef7761d91512073f41d91510057e70d91510057d70d91512057f74591510073f64591512067e64591512067c64591512073c64591510057f73591511fd7e73591511fd7c73591512073f43591510057f72591511f57e72591511f57c72591515557f71591510077771591515557771591511d67f61591511d77761591510057f70591510077b70591510057b70591510057c70591510077870591510057870591512073f40591511fd7e76d8d512057e74d8d510057d74d8d512057c74d8d510067f64d8d510067d64d8d511fe7e63d8d511ff5e63d8d511fe7c63d8d511f57e72d8d510057d72d8d511f57c72d8d5102d7e71d8d510257d71d8d511be7f61d8d511bf7761d8d511ff5f31d8d510057e70d8d510057d70d8d510057f7458d512057e7458d512057c7458d510067f6458d510067d6458d511fd7f7358d510075f6358d511fe7e6358d511fe7c6358d511ff5c6358d511ff5e4358d510057f7258d511f57e7258d511f57c7258d5154d7f7158d51007777158d5154d777158d511a67f6158d511a7776158d510057f7058d510077b7058d510057b7058d510057c7058d51007787058d51005787058d511ff5f3058d510057f7650d510057e7650d510057d7650d510057c7650d511fd7f7450d512073e6450d510073d6450d511fd7f7350d511ff5e6350d510075d6350d512075f4350d511ff3e4350d511ff3c4350d511ff5c4350d511ff1c4350d510057f7250d511f57e7250d511f57c7250d512073f4250d511ff5f3250d510057f7150d5102d7e7150d5102d7c7150d5142e7f6150d51237776150d512073f4150d511ff5f3150d510057f7050d510057c7050d512073c4050d511ff5c3050d511f57e76d89512057e74d89510057d74d89512057c74d89510067f64d89510067d64d89511fd7e73d89510057d73d8951
  | 34 => 0x8542006f76198542005df735854221ddc73585422257e75185420057d751854221dde7318542005dd731854202ef66118542006f56118542005fa7018542005f970185422257e75d81420057d75d8142004ff75d8142024fe75d81420067e75d81420247e75d8142004fd75d81420067d75d81420047d75d8142024fc75d814200cfd74d8142014fe73d8142004fd73d8142014fc73d814201cfd72d814202cfe71d8142004fd71d81420067f51d814233ebf41d814239eef21d81420067c50d814233efa40d814239efa20d814221dde7398142005dd7398142006fb60981420057f75581422257c7558142006f96018142034ff7518142024fe7518142004fd7518142034fc751814200cfd7418142014fe7318142004fd7318142034fc73181423c6bf4318142006bd431814201cfd721814202cfe7118142004fd71181420067f51181420367c5018142036fa40181423c6f94018142036fa2018142346f9201814201cfe76d913220ebe64d9132004ff75d9132024fe75d9132004fd75d9132024fc75d913222cfd74d913200cff73d913200cfd73d913257ebf43d913257ebd43d9132014ff72d9132014fd72d913256ebf42d913256ebd42d913202cfe71d9132004fd71d91320067f51d913220ebc41d913257edf31d913256eef21d9132034fe70d9132004fd70d91320067c50d913220ebf40d913201cff765913220ebc6459132565df7359132575ef7259132004ff7559132024fe7559132004fd7559132024fc755913256cff7459132006bf7459132564ff7359132006df735913222cff7259132006ef7259132004ff715913202cfc71591320067f515913220ebf415913221edf315913222eef2159132004ff7059132034fc70591320067c505913200ddc7650d3201edc7650d3200cdc7650d3255edf6550d3255edd6550d32015df7450d320179f7450d320079f6450d3201ede6450d3201edc6450d3220f9c6450d3201e9c6450d3220f9e5450d3255f9d5450d32007cf7250d3200dde7250d3200ddc7250d3222fcc7250d3200dcc7250d32016df6250d32017cf6250d3222f9f4250d3222f9d4250d32005df7150d3255f5f5150d3220f9f4150d3222fcf2150d3255f5c5050d3220f9c4050d3202cfe76d8532004ff75d8532024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d853200cfd73d853250ede43d8532006dd43d8532014fd72d85320067f51d853250ef631d85324d6f621d8532034fe70d8532004fd70d85320067c50d85322157e75985320057d7598532006f76198532005bf745853220dbc74585322157e75185320057d751853220dbe7418532005bd741853202ef66118532006f56118532005fa7018532005f970185322157e75d81320057d75d8132004ff75d8132024f
  | 35 => 0x22eec21d8943034fe70d8943004fd70d89430067c50d894322eef20d894321f9c435894322eec625894302cfe76d854351f9c43d8543004ff75d8543024fe75d8543004fd75d8543024fc75d8543014fd74d854301cfd73d854300cfe72d8543004fd72d854300cfc72d854353ebf42d854351edf32d85430067f51d854353ef641d854351ef631d8543034fe70d8543004fd70d85430067c50d85432357e75985430057d75985431e79c4398543006f761985431cf9c4358543005ef725854322dec72585432357e75185430057d75185435a79c431854322dee7218543005ed721854302ef66118543006f56118543005fa7018543005f970185432357e75d81430057d75d81434379c43d8143004ff75d8143024fe75d81430067e75d81430247e75d8143004fd75d81430067d75d81430047d75d8143024fc75d8143014fd74d8143436bd74d814347ebe54d8143006bd54d814301cfd73d814347edd73d8143436de53d8143006dd53d814300cfe72d8143004fd72d814300cfc72d814302cfe71d8143004fd71d81430067f51d814347ebf41d8143436df31d81430067c50d814347efa40d814347ebc40d8143436fa30d8143436dc30d814313f9c439814322dee7298143005ed7298143006fb60981430057f75581432357c75581431279c435814340f9c4318143006f96018143034ff7518143024fe7518143004fd7518143034fc7518143014fd741814301cfd731814300cfe7218143004fd7218143034fc721814302cfe7118143004fd71181430067f51181430367c5018143036fa401814359ef94018143036fa301814340ef93018143014fe76d8d4221ede63d8d42004ff75d8d42024fe75d8d42004fd75d8d42024fc75d8d4200cfd74d8d4221ede43d8d42596dd43d8d4201cfd72d8d42566df32d8d4202cfe71d8d42004fd71d8d420067f51d8d42596bf41d8d4221edc31d8d42566ef21d8d42034fe70d8d42004fd70d8d420067c50d8d4221edf30d8d4221edc6358d4258def7258d4200dbc7650d42016bc7650d4200cbc7650d42586bf6550d42586bd6550d4201dbf7350d4201f9f7350d420079f6350d42016be6350d42016bc6350d4221f9c6350d420169c6350d4221f9e5350d425879d5350d42007af7250d4200dbe7250d4200dbc7250d4222fac7250d4200dac7250d4201ebf6250d4201faf6250d4222f9f3250d42005bf7150d425873f5150d4221f9f3150d4222faf2150d425873c5050d4221f9c3050d4202cfe76d8542004ff75d8542024fe75d8542004fd75d8542024fc75d854200cfd74d8542014fe73d8542004fd73d8542014fc73d854252ebf43d8542006bd43d854201cfd72d85420067f51d854252ef641d85424def621d8542034fe70d8542004fd70d85420067c50d85422257e75985420057d759
  | 36 => 0x801000000300000040040130000000002002000800c0040070008020004001004800400000900500100000000020080000000004801800e000005800400201800580040020000048004004011003800400000200000140000050018018000000001801c018002003000003a001003000c04a0040008034006000002000001000500100080000000000004002003012800000600f000800401200b000002800400900000240000000038000000008002000800000100080740020020000008002001000800c004002006000c000002000800800a001005002401e000002001c00e00f00080dc042000001801400a00d000800c00a00000400180000070040000002003001000001800000000040040050008004000003001005c000004004801800800000280300260000000008004001013000000600501980000100000030020002003004000400200100c80080100090028004000003002002800001d002800c00e00400300080000030080000000001000805c00801600280b80040020070064002003000000400400700e0000048006001801c0260010000014004003000000000400100000000000010040000000000011000800000100080000060120008000002005006007001c005000801400600700000080000250000004002005002000c012001002801400400000080100100070000098004003000000400a00300080b8006004010002000c004000004400e021028800000200d0000014006000000000000801e002800c06a00100100040040010018010002002006002400a0080020000000004000800802600100000200580230000094000004008800c000008004000000000300a800000a008000004401e00001f800000600d00200980140000010038002001000803004601f001003c04002c0150000008000007800c00200200080080060000070054006006000000801000b002000000000400a802c00400b0250004004000000000000400200500040040000048014000000000801c020004000008c006005002800001200400c8000004000000800004000d001800000000700e800c016017001803000e002002000c002001000801800400000a0004022004000005c000001000000802c00000d002000e000000000c008002002800802e00a000000401000800580200120060038004012031004800c0080140010004000001000001800000300000300040000000004006000007001c00a0000030000008009000800c00400900000080040020018114000000000800000c00100cfe76d89435779c43d894322eee62d8943004ff75d8943024fe75d8943004fd75d8943024fc75d8943014fd74d894301cfd73d894322eee42d894322eee32d894302cfe71d8943004fd71d89430067f51d894358ebf41d8943576df31d8943
  | 37 => 0x6002001000c028002000000400e0030038010014012008802400e00200080480000040088008000002008000800e00000000000020000138038008000001801c00400d0038004004000000001000400a00500100000000008000000014006000800000c0020000008004005000c00c01e001000002c0000038108006000003800800400200380040040050008004006000001000000000300b8000020001005000000a00a0140040000014002800000a00100a0068000003000000000a01f000800401e00000b0004004007001000800600000000080060020100008018000002802c004001001800c0060020008000000003001000000000200a0018000033001800802200d003804c008000001000c0000000000008002000009800000c0040010000004002001000800c0010000000002003002801400200d0010000002000002800c00400e002800c002023004000400000e000801402e000003001c00200500400340b40080010024000001002803800802c000000000200c001000407600b000800c00a00f001802c000003002001000e000000000000800200800080020010020008000005000000c0040000048050000000001001800000c0000008000003000800c00600400280000040030008000004007000000400600f0018004008001000800000a001000002800a0040020008002021000000000e000000001000c0050000008002005001800000a001001000c01a003003000800e004001805c004000004000003a0010010014000002000000803e00500000040100000008038000003002002000400100000000020090000054014008002800402e001003800002601500180040000000038058004000004001802800500300240060000000024040001006801400000000300000060080100004012002000000000a015001001800200000000080000000000004000006001805001c001009800000801b003000c000000003004800200500c0040006000000800c01200a002007402c002003800000c002004805000000f0010048002012000000000201400100000060020000008008001000000004800000000080360040050004000001004800802c0040028010004001000005000600800a80000100050008034002000003000001c0160038018026002000007c014001001000000600600000000040090000008054001000000801c0000000000000001001800000000100000000020050000024022000000002800200000080180000000040020008003000801c006001000001000000000080340000160010008002005000800c00000a0000010006000000003c02c003007000800200d00000080000580060004008007002800c004000000005c00000000080380060000010084000037000001c000000000000c00a000001
  | 38 => 0x80040b40030090020020006000000400c00a000000000402f0068000002012000000c0060020008000002018000800000e000003800c008001011000000e00e00280000040080038020064000000004c0020000038074000001001000400000700380180040020018030012005000007000400d0000008000000005800000000d000006400a000001801c00a0150008058000004007000000200500700000140040000004060000000000403800000c801000c00200000000060020000018000000000801800c00d000000000400800000000240130000010004015000000c0020030008004000000008004001000800080000060100140000000002003000000200a000004000a00000200240060010000000004007000807c00400000a000c02a011001000802e00000000340120160000000000002003005800a003004801c0060020000000048002000001404000b000000c000000000000400800400480000040040008000004011004000000400000100000140000000028004014007801c000014004009000800100280000000080058000000006014801c00400b003000c00a0000018004002003000800400a006003002001000000c000400600600100740000000018018000001000000000e0070000008000001002001801001100100140040000008034000008002003c00800000c800000400100000080440000048000000025001000401c000000000401600000000540040100188008006004000000400000800b000000c01600080000020000040038016000000000000400c00000040000040028020030002004003000c0010148004008000005009400200400480000040190010044042009009800802a0130020008002007001000800600000000000000020000020002000008800c008018005800400c005001001000400000280080100010020000006013002003000200000000500200070020000000000001004000200b001000c0000000018004012014002000c0060460000000002000002000400002400a80000000010008000000004000002000000100d800000c00000480180040030008000000006000000402400000800000000000038010002006002000c002006008800c048000000002000c000002000000000100380000000150008000002015000802c01a01a002000c0460000000028000001007000801c00600b0004002000004000400e01600000000000020000000002004007002c00000f00280000000080018008000007009800401400d000800400a001000800801e0020020034000002002000000a00100b8020012008000000400000a0000008000003008000000200300c001c0100030090050000000001002800000a000000800600000000080120120060004014000002000400e002003000c00
  | 39 => 0x12ba94581634da31cd83305530000577000018ed3f90000000142d7b614600002a3d26a52200002d512e540d0ab119312c801c01ca5ad518b45e12bb22789ad0dc519a400507d46a14082e7926130ad05d1ef0b361d842a65170a7b01ac55b1c38f235be04ca5870b6d00014125d900373dd00005b3cbb223094863050eed1300c3d2a947d22b787745c313191fd4bee032d3c109fc45621c017e18843102c380a51598f765395161467cd632ac07225becfba56e1386238d53857d433119441fe000009008001a225ec4ec1b9072f0000ca14888aa8474966d01bc2fc5274e2d16ec3e416d40fe454966c3d30000212d53d20d86c753b0000000007d396ce4b311100e24b0a5c00004f700017853394d05578000000014985fa0a5a000000046800000000c89464c219208c08c3f787671288bc426891a7316c80716280003a44000472ce82510c55430880003f94cab24d90e0540045d2f20f694e9132109ed0a70fa08fa2aa863616dd53f0a48b08000000056f00000000bbf05c50093a4892e3c5467a031839c567025609310fd0000dc3164800015400002bc80001a8922e0e8494240440843780dc902ad1f50ab9448357cc243d1105936c03b81bed7b25468000114c0005c90c1b33380440000e2f0c7967a1a2c00046380000000923000112f06b4f21000125610197001fe800047e890811dd4cc4a7094d0000000387d4d74d712fc31b80000384fd400017920000b1e211504142540004c1800000005b31f180003c1ceb3150c7dd240cc024b7c0003bac1b90000dc12f0c0003f1c000000007757f800000012a2264800000000005e98ddf50c109d00008da457870611d487459e473a556082800001b12fa800000006ab0001552557176d1ed8f8903583df24880000f2c00009f000001b01c44e200003f4000500000d4002002000001401800300b000400a0190158040000012000000c01000000500000120060000004002004002800004c000000001400c005008803c004010002001000401a0020028006023000805400a000000000000400c007800003800100300140020010008004006014000001401000300000940120020110010000000000000003200a000800800000a003000800200200b803000a00c00100180000010000138020002000800c02e00d000001c00000b008000001c000000801c000006001800c000003000800800800400080100060130008000000009000007800000100180f801802c000002c006000000004c00e00900000000000030008000002001000801c006000002000000601e000801800e007000000000a0000000000002002007005000000a0000020002000001804c000000006801001c0010000000000001000001400000100400300000010000000008003004001401e04a001800402000000
  | 40 => 0xc853c24940004bfce6c42b8bb800016b24ac000051f000000000003aa0dd8228c910451110200000002700000000161e00017f54c8c0000001689560400003e86373e0c0004a7ca4d3d900000c986640000d9216685834edc0001998000000000015c800000000004438dee0530de800000000000cca000103139acfd33ac0aba1af0000000000000000000c18ba1000019306d0ed858650912ea88b1000000044ac5643ac4bc7296466c22d000012b80000000b8d123946711bd3b52490fa826700003f6400036e0000051c1640cec000000014d55008f9000123a3f10000482932f11b4fbb2d70af100006db34490b9210c9d532b400027786a6000000035e8d0d5ce0cc207ccbc129b40fb57e800b000041e0f7800031e475b3d4ce1029157c30ea88e803396eb1fd0aa300016c6000007a48451da36350204ecd18d1f5cecb32f4c6d4f7d7e4000159e000075f08708944c311661c48a7f000000012214442690ad705782db085085939cd25755bd7443564744455c34900000000e3c0002cbc5f957d0b4800009044d38b5f0000b311aa0bd810352ce471111d00000004a0533611f46920934a100d8d7040e44000156135f3dc0da8176064b5880228000000032d40000000000000036d1ac93d80000000583c5691e184111bccb630c4c9400000f98000000026ec77d081933907d4c9e3db8b291d4cbb719340000bacd21224c000398c2b038f800053413e128610031a200005f593770001409125917d00000002888291079d7893980edb34fc00000008183faca4200010f4000029e3dcceba47f13a600001242b545c3577c4dc00000000000ed521980000654000419974f0000000190003a091421b0b196a35c9ca703c111db2b04b5939e000035fc0000000a143c5d3b957407463b9968b07a82410f6866b53ac517272c000266c0001c40a390cf40f42fc89b225a04cc545870700217eb02dc000509000026e400000008950000e2a07080005e109d0333c00008d4a2b00000003a40983000080100005e3289022c08dd54615b80001ff000000005d51118f875f8c1c802cd02253d4610196558254dc0004ca5379512c3542f5cab400000002d3c00000016f204c1396000180e0830d4e00014ef283c0610000b910000d2a079550212493ad0000d8747a934d000000017000000e496e30e7c54200011d84a38000000002d0000000000000014b00000a38dfd360d5fd5b68e521e38c6204a940148bd515166d0a3000096e000095144b8000000027a0000000000120f000053a325879958300000000444000111e4d5c000514c5dd0000000180c4f225c0fcc4f44a8746ece9e00011945d70000000000004bc000072c39a3a18fbf00000001348b9231d8000226cc0f3c3810d37ec00000006fc083d41b1ee400053c87b70960e171b54a8
  | 41 => 0x4048f6f217530d332d5f01b300005fa939203a800028381485de83b64a6d282315c403325000055447db56a800000012171f38a8a4228957507c8471160f1c00010e446300d044844c15d455233314c0430ed25f044436e1d44d7912140005405563055145a12d0a6c40e4fa940543013aec3602bfc97c29182c01438aa916b508c0fd8e5d0b20dc42590b73115d1bd42c171010eccf2077c35c23f12750bd12af05496261aa8c151f697c42365158404c46a44b035b3cf017f440045f15e970306100003918b2b5ec43d7451c4a9599000005c800054287ee00006a726254a0551d0784ad4000120456a139c0004bac00018944d643c000057640490c28d961028fd74c5106308114cd00cc2d14a982ee46948d05d6c85a50007e12a0cbe317087a6000083100400004c5c0000dcd4d400000001478adf41095ad000000000000003e2d58731cd7ee0594d544cf0aab53c4b9951503a852b80000ce04370000cd430f85a4179971a0000658055d06b00008d751a48c600009f055380002d0809a290d1f70000efc26156af55b4ce93b7115306044204c380002af8e665f60c0712e10c1000000052b098c0facf3029f4de54a5d03015b0e8310094c73480b1500009bd27a80ac000134f2fa40000000000518972e07583b14ab971d3d14000172c0290000bd959cd352000079202a80000000d7b0b412073f155f1406caa226cc6180bb17ca3608c0e05094a50efd0443c051060000ee35af883300007a2261007c5e8950509a4fc00630031430ca110214000000000037454463a2c00060291c30000000000000042e074900000005c1c00014f874c4c7c49b00001f224f000023f881b05d0d941b253ae46b07094aa0a3328c0000000000027584e31094fcb0000000000000022b125e5c4d6a2000070b53854c450f43f107e57a8411493e11e8000000000000000001c70fbd13a86245c3d06a0000000053c9414d0868a02f905048f180709dc00009387d326a41c90000855302400007b53c95fd0369000063a06380003fa5477484025a22a400014c94bc01c8ce229acb9758380550000bac5f88eec177843e000131b5cf865621245000000000000000000012530000efd40cc2b60000c673e293d60bc0b9519892db575400000010df3ec921b1758f3848d02a03f91776485148f34405bc02eccdc20902ad019469b52901d901813f843f11df3cf810530c09ff549062956d443a4211484000013200000d535194ff00992273df55773a503c94c954a725e0b51000000005cc00000003c63c44000309c0004f640004dbc21a23ed74836841c3185c0003fd16634f6c054515400050d4000433800040581a0372843500008721450b7e00003083cd000021115dd1cc40003f8400000015de35584123ce80004a80d78099023027b40001cb933b16
  | 42 => 0x38c4491b990a1097c81f4d60d653e5d5a3331c07935f47685e00d0f601494b522d6414f1409727bcda927ccdb613cc49d41d51255e602543a1c35631dd4683514e3d2ae44cd0000aa120dc8c300015a80ad43dd1e4d223017d14f0c557f000011045e0cea73a741620000000022cdf640f429003bd119542c9be190c38c000179f000055c0f11233488483418f08774cd16c849cc0003e4cf7b29985e552f8df42594a6f00000003f9d3bb000000035ad226497000043cd2d85d4892a1b493e4509d37e23d86a41ef563c000022b4f5400036d43ea00008ae1a9400012f56c5237c000349d6494c20a07420d6aa416c32501497bc4588000000018200008985bd09a351e88d100017203978a754e740004f95556394d0643c6d2681f3551e000000000000002b60b7638b86b12c5c6d9355d181000000000010dc000000059a8524000000000000001eac19b21416703f084f900013af21880d8000143e12c0b8058085a50e9400039a934012792995ed0a5d15c06ff000000051ec000346c64806bc0002b44000327400012cd1f95498a3e183521638786904270000101c0000000000000000006a4bce4b180000000dc000016784e0800000015a226682e300015831dcc000000034d00005f500016d115ac0001d50000000126e2310000058c5b638102365ba40000cdcc1a000171115586f7239459541ec00046b53555dc8000279c1f638e0ba557b0596270c00028b576c52bca5f45a83a432b883b00000005aad1b546000f640206650000000000000000016e70001309382d1a6518c0004f74a9b007536d00000001a3000033fc42d11ac891218c98f3d44ad61f9d1280001088059c2f95e302c133e0000000000008a40001d74000000000034080005a8051b0e995fc000000000003a35fcc00018685fc2d1d3ac28c80001df935912f00000000e9b35082731b4177e0000cdb580400011a57d54c0d44d24f4bd60c3d2c10d880005b3400041e93cd402c0002d9c80809800000000000000000000000004040fb70000000000013a2ce400048fc73e4cdc00025b088c10f4ff8496cecf42a80005788d8400000002b907e5412c0002900d69431c0001a8c0000000dec27ad2ca10d897e00014904354cb656587fd00000002010bd22cf17da440404203117e532f8a361de13ff478487654d940f076d4b127b916f0000a152c647c800000003f20cd000002960c389d3503804c292844019188d300001680000f4a564c00018b01dd59382403e08000000068e169d4261d047ed4ec06940da0a681454d081bb84395e711175e9cf775588d0a03a0e0a112ce555690acb45ac3535e1c2ab12252250000a0a00000004e3000000000002f8000000000004e014c93ebc7fb0fd00000000ca32d0401a5bd935a00009660acc1494afc60b2c190bc39c80
  | 43 => 0x700251869313610ca58210c91871367358150e000000057cd8032eb87aa2af4c4f00d93a046c0b0a4c0578d4f1165006980000000eea00004f800014041eeca863aa49fa039800000000000000d192dd49d107ac65c5aa488900004ad24c0cdd00000005d093a9084580b199cc8620e00003199093384c7694dc48d400005f05a100005ae07940050da42ba47c921e01bc5980dea000049145e4674373c6e034e4059043c12616b8b2700000e71f990ed37856330000249348c71820f958a45510a509ac5f15b98000417c961168854648a119c293c4d000011d04a1d3fc4e040000000000029c2cb0e2452b11280002a90000352c0003ae1470541803c1cb1252000034b08280004e2c0001c30e9a4754c5150180000e04e27171400032e162500000000e2c7d53c18b5d3ffc7200000000000000000007ef047cebf221000000001ff0ddc91d0000f6b21780005c7d2b100001a135980004ba80004b2d25d378c483253c68f4b249135748fb45664000000146b4c68c3f282c66f1e741580cb000056990822da4df035c827124e149120b800036d0000017000000009cc29e53975064a4c3b84fe82f6d3d3451541723fc4143bd000022701562884f624d1c67c08800005da800017392fd108cce4156800025fcb341644000000123d11c46553e04000060c0003cac00010382780fe000000005a15c9409500000000000daa000000058000005a011e421a40002fbc0002be00004c000001e5442f55e80ad000000008e0982000141d4728dbb419c6e706692e400000000000bde1ba4f1e3da091f27114ed3a80f673fc0a552ed4b9f26dc0000000b4c39b4acf3808a284d752f651a96f5539c00019c4ac04d5166f2c8850a187c000443113906ec00000000002c8d45e5744c5900000002a812b9599499857696ef2d28000222c499000084f3a3c4df246c0000000cbf02440000000cd758c486055a00005b880005b25389000012e052cc723abd44f41f00001ea4c84000063453ec0000000000324502a5e656c03520c0538d07eb5f5168d082141103280000b9cd9823a8d3b0d300005e580003d080000000585000106834d0593397d705000013900000000f1d7193df14414e786ca0b1176506740001830b79423c4640848e252a390b505bc44753f02a53071237525d40a00003b70a5d27b4eacca03cc8ed64738f025fe4f46000000043dc00000000004358000000000000000004cb80001004efe0bc8c4d04b550c09b91852988d55225800000001980000000184cdda417080b1b500003d04bb955acb165eace5628300001d3400000000c90b308e10168f03511cee02cb80000000e19000000000000000aed235183c00000000000000000187871e2880282000123132301ec24243ba0df406d000000000005890000c4201c49f443080004
  | 44 => 0x26f0f8cf61511425540c85765750ba85e8400040001384b48835480957d58c12063e64e1c3b896241600ca82de0c1e46d0e453d8d3075cd415b1b5c2dd25517283ab8117024c92b388d65e38684fd49002bc3ba5672091802f0f28e5a2a700d93f483d60000ec40000ae5000000041a40000ffcbbb53880e22c08789205cc8e0d6400000011823c4d1fe0000463000000014a00001b180000478203092910331600002cb00000000e4a000138333dccd90f717d200006e8000119d27996141e3570e3175666026d31517e037010642e85f6c58f3bfd6ed2d68ac53c2c40800012ed02754dc000000036f405b12dc50251754e44a481ce07e09e9282515b0e0d15d02fc101093c0004bb8c5a1b20000500c61d00000003ed80002e59801576d52c1a440003c017b90c7400000001aa0000f7a00000003fb872b32a8000092c1f4267569a28740f15630d0e32694f928341bf29cd2b34cf4000000000026c4f9d2df0fd659c49af27650173db025b18e400f4fcc0000f096b4000167c000159700000005484000363d74947a09293c9135015f0ef800000000af491e5848000000007f200000029d8a5636b0fe0434d6ad130d6861a1c00023d040f0000c2d17bd3aa34b918803dd2aa19c0fca4968aae1720fa20000000000144900006b000000000d7800003700004ff874a5aa01e9173c22500013fa225c17000014201b8d7e622e84d11d913c7000127900000004bd517237fc00000000004d180005bb11b147a4d6a07ed0a4132cca422ace4c0000000250cb1b5a9020d4dc8281037ce1b0790be23e7c947000000000001cc000000000004f04bbc28c2cf554854c04b52e9967e4788c4604657d948481d74f40cc82650af44fb81a84498edd0000c01027049a578c19c5be80302a011de1ce0cea45f920c5b6ca27074c45a3d780af0044c104a2c3882d40c3402f11a3378800000015cc00002a73f7128000001d01dfc00038ac0000000a2e34f800056940005cc4627336173d00000834c2800059dc0002ffc00058d00001354000000000018fd2d7536400017ac00000013ce02a00002868e2939c47030000e4e0410f481ddd7573adc1c00eb4bc00000000320000012540000000000000000046900000000000571c4791ef93b653dd0730000000000100c528c92749800cc00000000000000000038439f95d3221944c0b090d100000002978647271800000000000000bdd26b800000000000000000311c00057bc49f5a283a70000000119cfb8081c545000000028e029a00000000cfcb49000093a00000000000000000000033a00000c5c80500000000000d01597558f0000d35005938d4f3000003f159a0000223554067e0b6403e0000d160000000000000002d402c59845620000cc430e14db00000005bf95fb00002da000065f0000
  | 45 => 0xe244b54d18000000000000004c58e4121cc000221c00036cc17a0f482f560340005d540002f3cf101024900421962100001031ad08e7000180c4ef17af0001163210972d161c00034e164c1d643820000000000170849e82cd000000000000004dd042946e413505dd5a900016622098f5a000000041180004c4800024545cd40840000000000000000000002054c44000213848036c8be44764e8430f12a7017817c000109800000005cb08391bac0000000000499147308f0e8d1ae08c93130d2d1618e80482064f0000f20234931d08f411c17057df0d9800000000000000b7f371cec54d4543a0769567260047b15105d256448033a307982804a650000fa008f8450000097d0e583fd14a87793d396c239916232480791340c4b12fd0cc622202441350a88128546c1d9936348240000ba816935b00005ced34a213546e236cb405fdcae234c900f1d2d22d3f4409f33ec16c55a826a30b0ef120808bc528400019756d73ad80000bbd5c254104be4534e2021603b4322139a40f82be19c8d970f34538487c34817d91c914401d11e78b524cfd25119d4b301e28fa1571808000000002a74c31314813300007c4188032f00000001ff803903f476a5b7055f1eccb8359480003fbd3262e9cdab0000000000000045b400000000001cfc8a754bc00042241592f5063130191430e1d6450c849e5345d4e80000000388444c00000001c3400059d000059a00000001276312863d000048745700003dfcbb10000adb115400047180000000b4600017914d2cd5237f800015e419f12197a900ac0002784c98088548300006e12ea44de0000d8823149955fd888d4b755bb5af53491e700002a4d7700000e0652c06b7152c5a92ef400016617ad25dc5370a180001e308ec53013ec5ef91d6000157440600000bf82e2452451a057030035f8000000154a10ccd33587d7334f8954b2e0504f27dc00022fd78b3d740001a108b25f5cfab25e400030b8a2f3e480d40000000364400016e46bd000084c13b90d237cc0000000bda00000004924b2400013f246b8e5c5ac40003240b122b4800025cc00000008792120000115093347509c8000000042ec0000000000540c96949bc332367830d45c4d6e5208c0808b921d48014e641c410b5c28681342c00010ac00053691352a9cd47000000050a0e573b2800037504154565132000000000013ea39d800039d41c128d400005ac00e0000136082c000099472517a8e4300000000000000000000029c572900012a12048000212814a59190293bbc15001a1037300161d30cc00024453ed2760c361a552d61c1569452eca2315485c941680e30e60e672ae0559023c59d15bcdb10b5948a2541028186c1440b700001b689592bb058b5b296430228dd55b5434610013c2571469c00000ec56849f63875528
  | 46 => 0x105600004da0000fb94db0b9441786f50000000000127218b946f43643201e2c000353c000000000000002503c8800057a836b0000686000112358b949b028166b13140002c10000000000029f14c30000d5d34c400014fc000000000000011d72c50a08003133013a4c6b461d03645311ed021c4b209a0bcc3bc0da24b157c03830a841808c8331d402056dcee72df4ddb1eb55b93d24bd158346545ef552b2bd81432d852be5af054101180003f19232499c26304dcba01ed579a6020aef145904814b800000004fc00000003158e890c9cbfe132400057d8b03553485c2ff00000000afb4b0800017f525433c40003a040000000000000010a1ab10073dd4e0f287083f2d587a15b797ef15cd1cf0b50ced2b996ce20308651ab9541021828f0dbc6ba094c2af31f482524c443159450ea3a282572f7c4e635dc8e03028c130f14ee509f8c6340183bd305936449c098e00ecc875b7cd2b4520c9c50cce3a123c0f2057cd9f0000bf54c4cdfc252487c34f000000012c75234afd3c490ab000000000000000000000000086d2d4c1f027d40f00000e371bc40002064ac7000099000014025ee000038991c1268447f4160a5122e4ffc466011d110c000471c000330cf793e011c80000000414c00000000005bc400032d0f520f88b442eac11a242c00000000004ef4a3c108453d2da8dfa3ec40002a7cdcd000000024d400922d40ff0da924a3af500d4f0038a0ae40004c780000001236000038d393c000000000027900644cf83e016b000019e520d14715430ff8d372f0800034bc71d1f1d04c5da53991dc8b6e15749b03b300340000fa75a7841d0000e1433241415f051b620680004b0c5d45a0c74040989d402d822a0c1c62d42981f700000004a24b0d5fa40e933e860039657b001980000320df7039454e5734e110000523276ce0e007c7dc2ee853b58b000020bc0005c60c743378000537817d4efc7132a68000401428d02880004624ee81d082c914d037a00009c11ce42a40000000034c00057fcd2c01045f40010762000045e1cd0000194c0000a00000000044f4cd438534f46091f600000fc800058bc00000007d90000000000000000010275df0000000134c4ba0007000164400000002d0d4fd0000d0000000002c6942200000000000347000000000015b400001103fc547e00008cc00000c700000000000eaa563502554a859413884275238e2c1cdd2243790b383ad520b0420fdb1fc0fb548046df2b287ec3b1d2bc23c12b70c48a5455ec9f90d28906359c201155d45f12706ad3bc809957dc50c3fe85bf5ad804e3f0444200006cb0d541a500010fb457c00018f880d000114622dc0004628d49490400053f9549085c2980001295000032332b129e00000000000ea20001438044d2e137e51340000d75443cb642c6
  | 47 => 0xdcece5b0d7f21e9d62b50fc7c0407cebe5b8517c56c029f5acd6f90760c111bd0f9c360544228590922814227257d27d0eb800039dc3ab333467b5f443ed57115920bc549c51e4a4e57c970147c83d81e8ca5b0fb8e3932480193df8e5801281c5363062319397593b4c1b60618dae0501332256977f1e3d24d1b4d4f45cf09fb0dd486a00003364a141b054203351b70d1f5c5cd7c20f490d4ab515517b00001d1421f00016b75bf11e525113eb000171e4bdd2634d0ccfd463c6e24a180000001052040052955c0000147453100014ce0001472000082d42810af3e6912411c140c2a357fd0988d8b4340fc3444d61046a439906e8000168000035792dc30dc4590c880004994ada000000024bc0000000000000000046452f9270800100000001a7d61a000151d0e411180000a9e41f8000000058c0d9458455f885b12354df1ec0d3a2b395e939f0d934f28000504c4cf1640b6800e050916082f3159d474058076c40904c600000002d60e1845a42131d7093f000033341009141788505421d37b181c04843183501c09150200800054c90e64f3c209550800000009265c8483a2b215c0000000000000004d4cc501fc88210000fe30000d51359109f00000000fc073525c429900015b336390a9443400043bc000516cd680000f575a8400050684f644d925830a96910000295185800000000004f5c9b81db4521286c2474194b3200017ac4a7400056b8a5700002c72a603722c457ff521400042380a45640b4d570c00000008ad00016bb000004342d0000000000033bc3a254352a94fa0a491d9564a4fbca7a5d8c000000000034255b60000b3309b40005bc0698000132d02c000045a116434944345d14b7441c857d4de00005c8875a35c128f255400007e80000000b0c3ab00004a3180627c841c23341e0369cd4c3e8d6850f9963f0000b05501cdc638c41b5284d24355900004cad4ca337d2fb219cf08009c05158d969c27f9324000060624d05083e303cc000132a0000000000000007995cb0000723491130200008ee2295494000000019e10ff00002d2556c8a628d09073fa8f5925a800031a800000006995728a6000015754810d154e4c5742cdd4b338200001f3c000480c00000016c12d6c51f00000005d2cf2e0001130000165415814180e394cf000052239fc6bf307c0005a3c43c5ddc000000035a4d78fd53ea94ab10141454f702df33441fc00000002fad5554e7043225e8d500dd950700006e5181551b30a464a2ef09325c994504e845ff43e023218bd5710ef89620000781118000000000001b0d49f000069e0eec0000ca81b80000ec03e544282a490045888ff9000000000000000000814491919e1e5907042506150de50ee2b70000000000037c509e1b0865a1ee0000492176e40b4dd600951bc464829d585400
  | 48 => 0x7f0b785195ba08cf3c7556140503f35e3d45656c563e431478003ac36134a00b804311b24135376322d2713c681062adc0c55ca97fe5efc17b599c0000000c993d581894f0d66e31807881ba8e691b4528a2a153c81fd93da35b57dd3ca800000000000001425280079712fd761000000013ecabc00000001c3c0ed00007e250e4bcd1ea1659554d2cc5f38000000102c0000c93354d4d302d065e00000005a1ce3f3bccd9531500002ddd2cf000109733b12192b3495656108fd2bf123b08fcb105f7012907789022338716280958609c90b10000ea139110de000000000000006008000328889917101884a58187023420e4640000269cafe2fd86f800003a9597039e5cfc0b1000000030e8000000102b00008460034000000003f00006d6000085f0000ff21b3833c51292622e680cf0a2c2b20000000228138400015ed0ec8ae12320e33241525549147f353b95444b655af58dc05833c15cf03040001cf4000306400000016042b4cbe63ce4f6d1f295452355629030841754f07ff4fc00a11898ba3046ce6505682e52afd732116d1b853d91f023880cd00017d000016ba04fc0000fd40005e6c6ec33480000000000000000017400000000000305cf66063400000010b75e5c0f3000000052980000bb53654bc94b42b100001c10f5438d49aa5fc48d600013de04f4f190a8cbc939b94214a4c8dd4be04105cbced218c0ef745dd57829e14a215c40004da937d586c4aa29b81be0ce80001530d292a500000fe40005e4087100006c552d80000000000014c000585841f00016dd22a0c7c4fdc77b54f922a00013b1000000000000005320000000000005e0000000000000000004af50e50574f280000b655dc4eb400016530000dc239c00000001038182800027800004e1c0001dc0000140c000000000038c83b0201800037380003fb45ca000156000000004ae02f70000000178511628fc04500000000000000203c31a4684000547096700017670000000584c99634185112a5d49a4214822000000000015e53be819615e0000122806e428800000000212960a2900000000e5c7ae1404000000000000000003984f0905a8dba000171b4d21566450037837784c25638c681c50cda3cdc5aa50d0619000165a006c0004b8d5250000bd52528ca724496f7573969d018c63258b522b041c0005fb513d5de01e85ce455119800000000b353eb80a63ff4000547c00010a80001b015eb00007b10b4c000000012500015343f7c0000380f911f90000000061115ec00025480e43900000000000021000810378000382400059ec000538cee423ac16616ac0001134f583dc8608251557c41d89930fbd42f2b8d5d84421589490862a257076e0b1513b4f4892106491ee43a060147ad21a2269658000cdef46f8f2f52dc5a8034978e024943224
  | 49 => 0xa24ccc3228341000000047c40002e887cb39bd2e9090800045b1165000000000015e400001020a1cd1e071c581008854a000148102793412ed143737985e714cc0005360000155406257e40245eec00044a8000294ced10c115e6068cc0d07543af0a892304c2c00023787af41dd0f9593d3d42f2d4a8494025e5ab927c037575f00d400012995330000a670368f272e3000009700960b84c494e611f832984e008d17c748e400017a0ff300015d7013d5be165c2ff000000020ac7c5131c9c90000dc800000003c94000285c87d58ecd36280ccd652c8a953a7d24e2fcc52f08e96fd0000000000072721ec00010fc00012ed23e492c0000f447711e688f10e18b213d805b40000e480000000000008855946773fb00003c140004e390b20000000000000027f4a2c18e000007f40000000da055509b44ad8b7b00001200000dcb0000d6f0000b8b5f3c0000008dbc32cc3d028c52d00f004d313d40001320ed03eb473b237037e41391dd35880005860a82030d58012600002ca16a716f46fe15a10bd49312130d014523fdd42a0fa45c6000021e000066100014890000e5043c91e7119800022f876300016b90000000000143100000004d5800000000000f500002cfc358298446835d0a3b231c0005f3400002240000a707820f952691f5103a054c02a43305dc0d7c06700000004c10548063c0004870000268129a122cb1f4d10a890000000000000000011c24a500002e612c0000044500004180000000192400000c80db33f96b0157965b3a65753000089221fc00000008102bdc000000109b0cf975d000094e00017742eccbf7381c0000000448312113a1374fa5474d1f4278ca992d9800003d51ec2cecc9709440004cb00001c54abb12bc284000000014940003e6d1270000d44000175e3b0c000154c91c03b868200000001b34caf000000029d000059356bf52e40004428000229000036fd33a00006691c7d196000000019b8bfb32c80005f2ce030be800000000005d0d68e1b3ccee28a80003a5977d256cd413bed42c1c6434416c4ac926654103e980005828b092e700004ee92f43f756f31ca87875b4c000243000000001905e807c153c17c938047e8004cd30485427d1dd4507078886c3ec141e1bd881d1d3c6731fe000000000000000b722ed94bf5818dd35054a910d909e8579c26c1d595593084bf13e516054b4ce744c8000043a47de535979d25d400028dcc85271c0000000000258c1990018000121000000002aa0000000000000000000000000000000060445b80000ca15315c70cc100007b439f40ae215000058d4f180454c0c20545b83eb0d24260556e1b603744008404000175456e80001acce120000c5f00016c75dcc000350cc391d1c0005c1800000000000000000334c0000000811524839b33cd3
  | 50 => 0x5ee800000017b7000059e0000000000034f53146b9391c9ca219000059fc9ac16bc0002d1400016384240000d854028ce354884eb00014f80000c6c0000000414400047fc72944480d1408d29137a400007b82483ecd266000127e00010cf148036c2bb955f44b4d2644dd0bf38c06f01ad977501d400036412a309d0633565156900000000001141167c45c000078300011602e4c00031bd15a5e28e1500005b012d88b8220048c3f340005da16a6362512900609763f8929800000001310bd34b110900840bca367483226ac00000007522ac8599437569623c8683000149651640002c4c0002cf86ed17800691fe4f96209c5265f785a6099cf6520b02b72bd556c18488f755740003384e280ff0bf944400002e9175000004225dbc4ff0a6c131048400031a56691c0471b5654000000168c01740000000c653665331000075508cd493514400000010eb291164758248ed0b54b0722402ca548144e24690ec4e7d5ab5f30b8a000039d2b502a90ed4a520d08f2918a0dcc22bc37c4bb13851a847f7240563d000070a02c96273af17a555ccc7a2fb0df55cdd76b394447e00015f8207980f44f05ed3f3800000006b5532c4380000f8e1dbc000323568200003b307700002f14b554fd41275a0400046a93b85a54f4b49b47df00011e0011c5e40c580002db00003d3c697319158b00000bd5f096ee00012883fec88f5e784930000239194962a06dc32b04b1360317906c30489ce32ed34510b114b0000816580ca41008d79310311740a284412b08b882d7922927346f204482c322f569b245907f00795e13a616d40b5d5881184b4b105958507852743748a4b362941c2a980000000ce72e6d414267d43c4dd44b9361887e52a8b1d00009390000a9606ac00000007c2569c3d9356c00057a00000000b57000124742f97ae00011972bac0002bccbfd52780001ee8000000081c19f4ef93cd8a25026140b05d54a90c2c0000000882067800000016280000d145d612843e342e922ccd9b000104a38f00000000a4800013a31cc87ea3468e7959212da5e08e7b048c79f4a94851000000000000001cb503c00004a80cb833904f10d702e971522c000031f845156604e5438800000000005f801550001756415c10e5ce8452310000056fcae74b794c257b80005b48c4e0b9800005d90e113852ab17448131ca08831d5c16154250c021e89582ad50b30134a1217dc77c4fa5043000000013a030950ac0002f94b203c98e620000d760c0886e2ab0000000000000005df253147d2fa17023e780002b184973a987bf2a40276168d2d4353428305b9487317163a243c85652d4e9c0000b824db963951951fb0c5025910c103b54d4d4a0eb11221a013f42cb44f448b06bb5014b7046553224d6c7ac3cb177b446812b47bc80e000000006157860
  | 51 => 0x1f44bed3e109911ec86632b410610a8413b40d4acc1f3090e00a0ec2143425251b551453494bd261d1b35cd8b863e405db38ecb8403e459c567c1d25de4cf647cd3f617ec809151c4760e512ac597cc322be4e885e8d3334a0cde75a5d65614d81b20854eee52e0275519012848780001250000335580044816d60d48000000005600000002770000381400018ac6a016f97810000b4e15fc00000009d74f2cef5090d53a28e8539245d5c94700f47446c37b289872443e84d947d831c109800003e0aaf000000000007e0129c00500002e44528a5006288680b3c00045c0b26544c000000000000f502f50b844e09e464154e46c14bf92fa00000003d00f14471446232a4d9a0000c9f00000004ad08cb0bed3be0000fbe2768000000000000003180000f3529dcd0c1e9102e51fc1f12b74daf0ee4d115a416e02228c25104c0a917e94d10c650ac3ff95bd5f9c0760000c455fb152d33e40000650e7a4f815792878a4730bc00000000000000b713cfce930000d73439caed2c013623204000143c00000000002b644e40000000000138f323cb8f52000005198b60062c5d70e805610e4c8a132553665ba85c72f415ac04d0d2200000001aa4db700000000000000035c0000000a6300000004814fbc000000011cc5d35bfd457310c000442c0003858000162093b1838d1d508cb0129a471a21bc0003b7c57e5a651cc00008ef19fc00000000001e805f3460c000000113135700000000000194000038896982e753a82e256ac26187d03cf49df308c00041b400000000004c4180900000000000bf800004781e6c01255c926c185000044cd6754bc03cf33d11bf26200005b111e6341d0604ce04ba000000000002bf00013e6000000059d96a52328e8e0d7400000000004a34345005d64b5f84f5b55781d43a90e544fc4c7047457f8546438023602a8089800050b4474496400000016404150c7b00000001f0c000000086b4c70f330000000000105506f450624614f304f850415dc000000046c13b40001764ac33b505da227565756806c441d14754b9cfcf00013a22a2cdc51b797603e206f93294ead0ae89c5210400026f0bbe19a000000000002be800033980003cec00042580004c3d4ad0ca50c43d400002ba021d000000043c4000555c00000000005c2400a0000000000046e53a4000000000034101cf00007503f600004bcc000000000000000000238b0f000000044242610000c0b000131851d8c9b46197143e1874e5374dd732e511f4e5511100000000f20000581cf8f17b86fa000000020a4000582ce855380c18000129025b44a30000a1f281895d33810a83a543432eb56550c7c00060110795b2c56500017415a20c7f00543034610000158c00027b007832c40004de8000000034e54ec0002f8400000000001bbd19b4f18
  | 52 => 0x2ce000000000002e0000000000000005c589ba5b947850250c2046dc8a255d8000242800008bc63500006423cc57c54b35511000000013c40000538f5c26a174a5c8cf1f0000000069c0000000000376468900000003ae549553040002a304fa309936800000000000216218441b00000000000000000001c33ad328000111500000000be172b411c540000143b20280000f841ae0000c823d7cc554c140000000000153496b0d9c0003a953e758c8aad21480000000bfa124000026d4a0400009b605187262464000590819150d840b48e0f0f4ed05fe4e414295d193691fa50cb4a90151269548c1e9513f4f8d27709c01ef000066d05b517b30d57fa412425d46880c0173111c56c894842d8073089169f2c2cef646ac89f33d52f12c708855f2031b0f055173184ff51cf139b377077a3b040003e903ce00014ba2204f2d3fd8fda14497940fed3945d88ec81a68f0a28f466a5a483952f186764d8501938d96e45fec8f808b50fe4c9ce9731e006a01d0b900ae09535b6570b08ed16745fd1070000c4b4e9d09a22d937054a498b1e40830423559b17c97aa000136b00004fe37b4324012caf01d20eab0000000065ce0055689bf32e93b21daca6a5b308aa04580000000fe600000000000000195c7f1407000057204820000b854ae86440dfd2d15cd17662b80d9c274800020a875e080800000000000000cbc000000000003fa42000b93e1400001f952e44509e21c5cb8700000003b34b7a00014d508c4e4930a0000196c0000000b8e06003db21d400000001a4356883c00000001c4400031040000000deb00004a5436069d239888e1a580001d800000000ea3344c0000001460000000000000005b4106e230477657040000000da5273c0002acc000000159d31c50d4000000000000000000000239000012800000f0c00000009f8000103f29f800000000004b88f783b1835729c8000000000000000005d311752ec07300ac4cc05e905ba00000000000000426496f4e2970d0000eda35000000000d585a4d5d600000000000cb737c9199265c0003c340003f2400006b0000422c9dd2634a64000101a4538da648603ec0f4c000000101e000095e000026611c800046e8000544117643694994e44d8000016d85ed496022ec00000000002ad82855e211fd3b641795058ede01007e3549d75a48381b34414f550a4c98a3c580a34fed7d34dccf6a106897226780000b61138418901d02082fd000140d214ce6800003bc00000001b757c64320685153c3054e9400000014fa1d6000000014400000ed72fc04db00005355d0117a58e127810b90db0c301cd2300d612ca81e336f947112b00004df0057543c05043d4ddd42e86be454452700000001524a192d88f4d2f9d74d5c4926b300c6fd12acb6b17a435100000003ac8b6f00010cd
  | 53 => 0x460d1c5318000000072100009fc00000000000b3a5d1d4610a212e00000000383557f478d7b30cd051343d8df836b4bdc133800000005301f582220a5167d51e01225d3800011940004508b2500000004ac802e0000f43493c92844f84a4553c1c61abd2e6135c68d1d0d5185e5400001ec857000056d49fccb00860c1d54482b413bcdd042b464500003e73dc41091ccc0004770e4d0000baf14b400024b40001e1173041bd611314c8f500002ac00000005ff11af420400035c51cd27c46221c2000053a82f6000000015d561748800000fdcdb900009a623a51560000000000047c0cb4f0c045000023cd17300013fd0f54ec925d0e42000031133f
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa5d851c9630400153d08392c608002a76107258c1002d6b408e4b182008ad5811c9630400d5b500392c608022b66007258c100356d404a4b182000ad98094963040011bd0e212c6080023761c4258c100052f42884b182000a5d85109630400b5ad02212c608002b56044258c100356d40084b182000ad980109630400d4bd0ba82c60801a97e155058c100446f43e80b1820008dd87d0163040014bd0ba02c608002976174058c100372c28680b182000a5e85c8163040014bb0b902c6080032710f7650c100064e21aeca182000e1c43595430400d1790eb22860800aa720d6450c100346e43ac6a182003a9c8458d43040031f301baac40801a3ba1f52588100347643aa4b1020068ee87d09620400d1dd0f992c40801abaa03755881003d74c06eab102000a6e851d162040014db0a3a2c408002b3a0c745881000566c18e8b102005ae6811d1620400f5cb023a2c40801abaa00745881003d74c00e8b102000e2f5495162040015d700aa2c40801aba201545881000567418a8b102000acd8315162040014dd0a39ac4080029b614735881000557420e6b102000aad841cd620400b5cd0239ac40801eb9604735881003575400e6b102007ae9801cd62040015d700a9ac40801aba201535881000557420a6b102000aad8414d62040014dd0a21ac4080029b614435881000746a1886b102006a6e85d41620400d4df0aa82c4080029ba17405881000536c2e80b102000ace83d01620400159b07a02c40801b9a14340588100053742e60b102000a6d85cc1620400155d09982c408002ab61330588100373428660b1020068bc84dd9420400d1790eb22840801a3b21d62508100346e41eec99020068ec82dd9320400d1b90eb1a640801a3b21d624c81012c3ec36eaa00202bc3e64dd540040018bcc7baa80080031b98b75500100043f43acaa00200a87c87595400400187eeab2280080030f1d564500100062fbaac6a002000c5c7558d40040018deeab1280080031b1d562500100fc3ec36ea9802000c3e64dd530040558bcc7baa60080031b98b754c0100043f43aca980200a87c87595300400187eeab2260080030f1d5644c0100062fbaac69802000c5c7558d30040018deeab1260080031b1d5624c0100cc3ec36ea9002000c3e64dd520040018bcc7baa40080a71b98b75480100043f43aca900200a87c87595200400d4f100b2a40080030fdd564480100061e3aac89002006e385059120040018beeab1a4008003171d563480100372c282c69002000c6f7558920040018d8eab12400801b9a14162480100063a3aeec8802000c7785dd910040018e90bbb2200801b1d94376440100363a286ec8802000c7776dd510040014ed0eb2a200811e9d21d65440100353b402ca8802006a7480595100400d8eee0b2a20080179cdc16544010
  | 1 => 0x10ea8a40880035c21d51481100cf39c32a2902204ab70865452044033ce10ca8a40880669c219514811002eb93b2a29022005d70765452044001ae6e8a8a40880035c5d15148110006b9b9aa29022000d717354520440a3ec504a8a4088003d8609514811028eb9b92a29022000f63725452044001ec6c4a8a4088147d8189514811002cf443a429022005ce87648520440d5cd0ca90a4088017781c52148110007b0a8a42902200687e87d96104400d0f90fb2c208801a9d60765841100353a432a30822005c7676546104400d6e100a8c20881431d9db6584110036b9baa810822006d73754c2104400dae6ea90420880030fdd274594105bd3dc02e8b282006a78805d165040014bd063a2ca080029760c74594105b53dc02e6b282006a78805cd650400147d0839aca080028f61073594100043f43886b28200087d8710d650400d4f501392ca082d69e60272594100043f43884b28200087d8710965040014bd06212ca080029760c425941002d3b40884b282000a7581109650400d4f500212ca080029e60042594100043f43864b28200087d870c9650400147d08192ca080028f610325941002d3b40864b282000a75810c9650400d4f500192ca080029e60032594100543f43e80b28200087d87d0165040014bd07a02ca080029760f40594100363c38680b28200a87e87cc165040010fb0f982ca080028fa1330594100051ec2660b282006c7870cc165040150fd0f902ca080021f61f20594100347c402eab2020068be87d51640400187eebaa2c80801a2f21d54590100355c402a8b2020068be8790d640400d17d0f212c8080030fdd675590100055dc02eab202006ab8805d5640400153d063aac808002a760c75590100051f428e6b202000a3d851cd640400193ae639ac808002aee0153590100355c402a6b2020008be8714d640400117b0e29ac8080028fa1472590100051ec28e4b202000a9e831c9640400153b06392c808016ada04725901004d5ac08e4b202006aba801c9640401357300392c80801aaea0252590100055cc04a4b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202005ab6810c9640400156b02192c80801aaea0032590100055cc0064b202006a3e85d41640400d47f0aa82c8080262fa1f30590100045ec3e60b202000a3e85cc1640400147b0b982c80801b8e14330590100051f42e40b202000a3d85c81640400d1f100baac60801a37a1f5358c100346e43aa6b182006ad88054d630400d1bd0fa1ac60801a37a1e3258c100056dc02eab182006ad8805d5630400153d083aac608002a76107558c100052f428e8b182000a5d851d1630400193ae83a2c60800387d525458c100056dc02a8b182006ad88055163040011bd0e2a2c6080023761c5458c100052f428e4b182000
  | 2 => 0xd51501100353a432a2a022053f304054540440a18f0ed28280880af1e1db75501102863c3b6caa0220038f88758940440016e30a38a80880025e21d515011002e3c3b2a2a022053f33415454044001ae70ea8a8088002dca1d5150110005b843aa2a022000d7087545404409d6e10ca8a80880175c9d9515011002eb83b2a2a022053f32845454044001e6308a8a808814f5cdd1515011000799ba2a2a022000f336454540440a7e60c8a8a80880035cdcd5150110006b9b92a2a0220059b887505404400b970eca0a80880176c1c5415011000798a8a82a022006a748654630440bb8ececa8c60880031e196768c110004f4c16e91822002ad88358a304400bae4e2a8c60880035ce1d518c110006b843aa31822006b7286546304400d6e10ca8c60880035c9d9518c1102ef393b2a31822000d73745463044001ae2e8a8c608814b5c5cd518c110297a921aa31822000f51435463044001ae2e4a8c60882461fa1b754c1104143f43eca982205087c87d9530440012ed0ea8a60880025d21d514c1100353a432a29822052f503054530440a18f0ed28260880ab1e1db754c1102863c3b6ca98220058f8865d130440051f10eb126088002dc614714c110004bc43aa29822005c787654530440a5ea662a8a60880035ce1d514c110005b943aa29822000b70875453044001ae10ea8a6088132dc219514c11002eb93b2a29822005d70765453044001ae6e8a8a60880035c5d1514c110297a941aa29822000f518354530440a5ae6e6a8a6088003d4dcd514c110007a9b1aa29822052f50635453044001ae6e4a8a60880167621d314c11002e6c3b2629822005dd0714c53044001ea2a298a608801a9ea0365881100353a432a3102205cc767654620440394f50db2c40880027660f74881100e53c42ac910220009b984dce20440394f10ab1c408801a9e219518811002eb938aa31022000d73875462044001ae10ea8c40880739ce195188110035b9432a31022006b70865462044039ce10ca8c408801a9c2195188110006b93b2a3102205ce72765462044001ae6e8a8c40880035c5d15188110006b9b9aa31022000d717354620440a3ae2e4a8c40882461fa1b754811034c3f43eca902205087c87d95204400d4f501b2a40880039a14362481100347b436e290220009768754520440012e90ea8a408801a9d219514811028fb0102a2902205ba7a8694120440a18f0ed28240880029ea1b754811014e3c3b6ea9022019a7a86d9520440a18f0edb2a40880163e219744811000c7c43ac89022019a7885591204400b1f10cb9a40880063e21d63481100cd3c42ac6902205fe6865dc92044001cd0cbb124088002dc6147148110004bc43aa29022019a7886545204400b8f0eca8a4088147d8c855148110006b9c3aa29022000b728754520440016e
  | 3 => 0xa8a205097a861c1514400d8f50c382a28801b4ea1070545100369cc20e0a8a2000c7a641c151440018f0c8382a28801b56a0c7054510036acc18e0a8a2000c7a631c151440018f0c6382a28801b5aa087054510036b4c10e0a8a2000c7b621c151440018f2c4382a28801b5ca0470545100363db08e0a8a203dc7476dd151440014ef0cba2a2880029d21974545101d63a3b2e8a8a2000b73805d151440016e100ba2a2880031d1db64545105e71b326c8a8a200f9748759151440018e8ecb22a2880df1d1db73545100053bc32e6a8a2000a74865cd51440698e8ecb9aa288002dce017354510005b8402e6a8a2000c7476d8d514401f2e90eb1aa2880031d1d963545105df2a31ac6a8a2046c747650d51440a5e2886a1aa2880c71d1db72545100053bc32e4a8a2000a74865c9514405d8e8ecb92a288002dce017254510005b8402e4a8a2000c7476d89514401f2e90eb12a2880031d1d962545100059bc22c4a8a2053b348458951440016af06b12a28814ad520d62545105d732312c4a8a2044c747650951440858e8ec992a2880129de1b705451002d3a436e0a8a2016c7476dc1514400b6e50db82a288016dc21b70545105ceb83b6e0a8a2000b7184dc151440016e307b82a288002dc60b70545100253b434e0a8a2006c74769c1514408f6e501382a2880035cdc270545100053b430e0a8a2006c74761c151440a766d08382a288002cd6107054510295ab418e0a8a2000b55831c151440a36cd04382a288002d960870545105c5b9438e0a8a2000d72871c151440016e50c382a2880039ca187054510036b93b0e0a8a2006d70761c15144001e6508382a288002dc610705451000798c20e0a8a2000b31841c15144001ea506382a288002dc60c7054510007a8c18e0a8a2000b51831c15144001ec504382a288002dc6087054510007b0c10e0a8a2000b61821c151440754e90ca8a82881031d1d951505100063c32ee0a0a2000d7151dc141440018f0ca38282880d29d219514c5101fe3a3b2a298a203fe546354531440018f0cbb8262880035c547704c5100063c328e098a202ea7486545214407d8e8eca8a42880fb991895148510006b8a8ee090a200687e869da504400d2eb033b4a08801b1dd8676941100043fc3ac9282200087f8758e50440010ff0eb14a0880028fe11629411015d1e422c52822000a5f8358a50440554b906b14a08801a9d21951901102f63b3b2a32022000c78659da404400757108b1480880175c9c55190110006b9c3aa32022000d7087546404400d6e50ca8c808801adc2195190110006b93b2a3202205ee727654640440a7ae2e8a8c80880035c5cd519011029f99a1aa32022000f31435464044001ae2e4a8c80882461fa1b755011045c3f43ecaa02205087c87d9540440012ed0ea8a80880025d21
  | 4 => 0x5440010fb0e21eca882fe9ea0072d95102853cc00e5b2a200087e8710b65440010fb0e216ca8800297a0c42d95100052ec1885b2a2050a768110b65440014eb02216ca880029ea0042d95100053cc0085b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a2050a76810cb65440014eb02196ca880029ea0032d95100053cc0065b2a2006c7571dc7654408f4f501b8eca881421fa1f40d95100043ec3e81b2a2000a5e83d0365440014bb07a06ca881421fa1f30d95100043ec3e61b2a2000a3e84cc3654400147b09986ca881421fa1f20d95100043ec3e41b2a200087e87d9564440010fd0e32ac8880121fa1f75591100047dc02eab22200087e871d564440010fd0fa8ac8880121f21f51591100063c3aee0b22200087e87141644417d8f6e0282c8880021fa1f6558d100043f438cab1a200487e87dd563440011f700baac6880021fa1c7558d100043f43ea2b1a200487c87d4563440018f0ebb82c6880021fa1c5058d105ee3db80a0b1a200487e85dd943440010fb0bbb286880021fe157650d100243e42aeca1a20008ef825d943440031d904bb286880038710f6550d100145f43ec8a1a2002a9e83d9143440071bd0fb1a868800ea7a136350d100347c402ebb12200487e86dd562440010fd0fb2ac4880030f1d365589100062e39ecab12200087e871956244001878e832ac488003171cc65589100061fb2ee8b122000c3c65dd162440018becbb9ac4880031719773589100243f43eeab12200687e80dd5624400117f08baac48800e2f21175589100046fc1aeab1220028dc835d562440010fd0e3aac48800e2fa1f74589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100146f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b12200087e87d4562440090f90fa8ac4880030fdd351589104761e3a6a2b122000c5f73d45624410b8b8e7a8ac4880021fa1c50589100061fba0a0b12208bc3c7414162440018bee6282c48820b171cc50589100243f42eeca12200087d85dd942440010ff0abb284880121f21576509100045fc22eca1220008df835d942440051b906bb284880121fa17764c9100043ec2eec992200087f855d932440090f90abb264880022fe11764c91001c5e422ec99220008df835d932440a74eb03b22a2882f38dd0764545100043fc3ac8a8a200487c8759151440a54eb03b1aa2880021fe1d63545100243e43ac6a8a2051a7581d8951440010ff0eb12a2880121f21d62545100051fc22c4a8a2040a3c8458951440014bf06b12a2880fe9720d6254510034bd43ee0a8a2006c7a761c1514400167308382a288002d660c7054510005b4c10e
  | 5 => 0x811f1ddd970547102f59b420e0a8e2000b35841c151c40bb6ad06382a388002d560c70547102e5b3410e0a8e2000b65821c151c400dae4e0382a38814f1d5d951903100043ec36eaa06202b87e8759540c41170f90eb2a81880025da1d5150310004ba43aa2a062052c757654630c40010fb0dbaa61880aa1fa1d654c3104143e43aca98620009768754530c40012e90ea8a61881471d5d95188310035b8402a3106200087d86dd520c40530fd0eb2a41881a61f21d654831002e7238ac49062000e685058920c40012ed0ea8a41880025d21d5148310035b8402a2906200687e8710f65840010fb0e21ecb0801a1fa1c42d96100043ec3885b2c2000a5e8310b65840014bb06216cb081429da0442d96100053ac0885b2c2006a7a8010b65840014f300216cb0801a1fa1c32d96100043ec3865b2c2000a3e840cb658400147b08196cb081429da0432d96100053ac0865b2c2006a7a800cb65840014f300196cb0801a5ea0375592100243f43eeab24200687e80dd5648400d0f901baac9080021fa1c75592100345e43aa8b24200087e87d45648400d2f501baac7080121fa1f7558e100343f406eab1c200687c80dd563840010fd0e3aac70801a3721d5358e100043f43ea2b1c200487e85dd943840010fb0bbb2870801a3ea037650e100043fc2aeca1c200487c855d94384001c3887b2a870800a2fa1f6450e100154f41ec8a1c20038de87d8d438400753d09b1a870801a5ea037558a100243f43eeab142006a7a80dd5628400d0fd01baac5080031ea037558a100063cc06eab14200687c80dd562840010fd0e3aac50801a3b21d5258a100043f43ea2b14200487e85dd942840010fb0bbb2850801a3ea037650a100043fc2aeca14200487c855d942840090fd0bbb265080021f617764ca100347d406ec994200087f855d932840090f90abb265083121f21d645461061c3e43ac6a8c2006c7870d8951841850f90eb12a30801b1e1c162546100059cc20e0a8c2000b59831c151840016d304382a3080031e19770506100063c32ee098c2050e6421d95218400b8f2eca8c810801b1e1977650210004ecc1eeca04200097887545408400d3710ea0a81080171e5d9518c2100363c32eec98420009b984dd930840012f10ea8a610801a7621d314c2100e53c42ac9104201ca788558e208400d4f10ca8c41080171e5d951882100cd3c42ac89042019a788558d20840012f10ea8a410801a9e2195148210034f443a42904206ae6865485208400bbc0e290a410800297a0e64d95100052ec1cc9b2a2000a3e8498f654400147b0931eca8803e9da1b71d95100052f41ce9b2a2000a5d839d3654400187ae83a6ca883069ea0074d95102853cc00e9b2a2000a3e849cf654400147b0939eca883029ea0073d95102853cc00e7b2a200087e8710f6
  | 6 => 0x2e363b2a290a4005e646154521480016d100a8a4290016b921a414852000753b248290a40cdf605090521480015c90ca0a4290003a95914148520667b02828290a4005ae4868c52148001d8ec718a429032fd81423148520005724326290a4000ec5634c52148195ec0a098a42901aadaa1770485200043fc3ac9282400087f8758e50480a10f90cb8ca0901431d1857194120036b9082e3282400087f87d8650480018eae3b0ca0901a71b9d921941202873230a432824069d6a704865048001ae2e2a8c80901a61fa1b755012045c3f43ecaa02402987c87d954048001ad0a1b9280903265ea1e505012014e3c3b4a0a02401997a87dd540480578f0edbaa80903265ea1f655012014e3c3b6caa024000d6875dc940480332f10bb8a80900025e21d51501201f63c3b2a2a02406ad68754854048001f428290a80900067aa0b748c120006b8b8aa3182406987e86dd530481050fd0fb2a60900a61f21f654c120006b4286e498240c897a8794130480538f0ed28260900665ea1f754c1201563c3b6ea98240c897a87d9530480538f0edb2a60900063e219744c1200ccbc42ae89824000d6875dc930480332f10bb8a60900025e21d514c1201f63c3b2a2982406ad68754853048001f826290a60900a71b9db6588120035b5406cb1024006d68505c6204800dbc420b8c4090003595c55188120035b4402a3102405fb688550220480bf6d10a98440900030fdd274597100053dc02e8b2e20c7a78805d165c40014bd063a2cb880029760c74597100053dc02e6b2e20c6a78805cd65c400147d0839acb880028f61073597100043f43886b2e200087d8710d65c418b4f501392cb880029e60272597100043f43884b2e200087d8710965c40014bd06212cb880029760c425971002d3b40884b2e2000a758110965c40014f500212cb880029e60042597100043f43864b2e200087d870c965c400147d08192cb880028f610325971002d3b40864b2e2000a75810c965c40014f500192cb880029e60032597102a53bc0ae0b2e200087e87d0165c40010fb0fa02cb8800297a0f40597100052ec1e80b2e200087e87cc165c40010fb0f982cb880028fa1330597100051ec2660b2e200087e87c8165c40010fb0f902cb880029d60450593100053ac08a0b1e20008ef825d943c40031d904bb287880038710d6550f1002c5e43ac8a1e2002a9c8359143c400b1b90eb1a878800ea72116350f100053ac08a0b1620008df835d942c40051b906bb285880162f21d6450b1002c7643ac4a1620008bf845d932c400717908bb265880163721d634cb1002c7643ac49962000a77865d151c40016e700ba2a388002dc20174547100053bc32e6a8e2000b73805cd51c40016e100b9aa388177c510d43547100053bc32e4a8e2006977875c151c40094ef0cb82a38
  | 7 => 0xf980dd761480014eb03baec2900029d60475d85200043fc2ae9b0a400487c855d361480010ff0ab9ec2900121f21573d85200043f438a1b0a4000a758114361480d38f2e0286c2900025e61c5098520005b8c08a130a400487e86dd561480010fd0fb2ac2900030f1d365585200062e39ecab0a400087e871956148001878e832ac290003171cc65585200061fb2ee8b0a4000c3c65dd161480018becbb9ac290003171977358520004bd438a0b0a4000d3b7414161481a1a70e8282c29000356dcc505852067eac398a0b0a4000b718114161480330fb0fb28c2900030f9d365185200062f39eca30a4000a7581d94614800187ce8328c290003179cc65185200053ac08ca30a4069c7970194614800187ecaba0c2900030f19574185200062fb2ae630a4000c5c655cc61480011ef0eb08c2900025e61c50185206869d3a0a030a4000d3974140614819fab4e6280c290003565cc501852034eb5390a030a4000b718114061480010fd0d3b2a2900029d60676545200063ac0ceca8a4000c79809d9514800147f08bb2a2901028f21176545200052fc1aeca8a403fa5c835d951480014ef02bb2a2900031ba08765452000636c10eca8a4000c6f211d9514800d0f9003b2a2900021fe1d64545200043e43ac8a8a400087f8758d51480010f90eb1aa2900029b2197254520675b3c0ae4a8a403ea7a86dc151480018f4ec382a290002ce6107054520005acc18e0a8a403eb6a821c15148001ad4e4382a2900035a5c87054520004bd430e0a8a4006c7a861c1514800da7508382a29001b4e61070545200063d320e0a8a4000c78641c1514800dab506382a29001b5660c70545200063d318e0a8a4000c78631c1514800dad504382a29001b5a60870545200363db10e0a8a4006d71811c151480018f6c2382a2900035ac8470545200243e42ced20a400087f855da41480090f90abb4829000237e0d76905200146e41aed20a400087c865d6414800d2f100bac82900021fe1f65905200043ec3ecb20a4000d68505ca414800d2f10b38482900163e21970905200ccbc42ae120a400487e85dd941480010fb0bbb282900031e14376505200063c280eca0a40058bc8759141480090f90b3b462900021fe15768c5200243e42aed18a40008bf845da314800717908bb462900021f219758c520034bc402eb18a400087f87d9631480010fb0fb2c62900035a141728c520034bc42ce118a40058f8865c231480332f10ab8462900121fa17764c5200043ec2eec98a4000c7850dd931480018f0a03b262900163721d634c52002c7643ac890a4005ae481591214800b1d90eb1a4290016b9205634852002d73436c290a4000f6050d852148001cceca30a4290003991946148520005d2c20c290a4000bc5831852148001ec0a030a42900029b21951485200
  | 8 => 0xc3b82a3100fa9e61870546200363d3b0e0a8c4000b39841c151880016b306382a3100039c5847054620034bc402eb20c401c978855c241880090fd0bbb283100021f61776506200347d406eca0c4000c7850dd9418800d2f100bac63100725e215708c6200243f42eec98c400087d85dd9318800d1f501bb263100031e143764c6201f63cbb2a32044000d71715464088001ce2c2a8c81100725ea1f75502200e4bc42ee2a044000978875454088001ce2c2a8a81100fb1e5d9518c220006b8b8aa31844000e716154630880392f50fbaa61100725e215744c2200e4bc42ee29844000978875453088001ce2c2a8a611000297a0e64d95200052ec1cc9b2a4000a3e8498f654800147b0931eca900669ba1b72d9520036b5386e5b2a40d5a7a80dd365480534f301ba6ca9000297a0e74d95200052ec1ce9b2a4000c3d741d365481a94f5003a6ca900a69e60074d952069d3d406e7b2a4029a7980dcf654800147d0939eca900028f61273d95206953d400e7b2a4029a79801cf65480010fd0e21eca900021f61c43d952068d3d406e3b2a4029a7980dc765480018f2e1b8eca900031e5c171d95200343e402e3b2a4000a3e841c7654800147b0838eca9000297a0c71d95200052ec18e3b2a4029a6e821c765480014db0438eca901569ea0071d952014d3cc00e3b2a400087e8710765480010fb0e20eca9000297a0c41d95200052ec1883b2a4029a6e8210765480014db0420eca900029ea0041d95200053cc0083b2a400087e870c765480010fb0e18eca900028fa1031d95200051ec2063b2a4029a6e820c765480014db0418eca900029ea0031d95200053cc0063b2a402987e87d0365480010fb0fa06ca9000297a0f40d95200052ec1e81b2a402987e87cc365480010fb0f986ca900028fa1330d95200051ec2661b2a4000b718114364480031f301baec8900029d60450d912034e3cb80a1b22400087e87d9564480010fd0e32ac8900025ea1c50591206871c320a0b224000b718114164480090fd0fbaac8900021f60775591200043f438eab22400087e87d4564480090f90fa8ac8900021fa1c50591200053ac08a0b224000b718114363480031f301baec6900029d60450d8d2034e3cb80a1b1a400087e87d9563480010fd0e32ac6900025ea1c5058d2067f2c318a0b1a4000b718114163480090fd0fbaac6900021f6077558d200043f438eab1a400087e87d4563480090f90fa8ac6900021fa1c5058d200053ac08a0b1a400487e85dd943480010fb0bbb286900021fe157650d200243e42aeca1a40008f7815d9434800b1e902bb286900038710f6550d200145f43ec8a1a4002a9e83d9143480071bd0fb1a869000ea7a136350d2003477436e4a1a4000d6850dc943480012f50e286c29001b5adc850d8520005b8c08a1b0a40018
  | 9 => 0x75d85300053ac08ebb0a600087f855d3614c0090f90aba6c2980021fe1572d85300243e42ae5b0a600087e87143614c0014eb02286c2980121fa1b75585300043f43ecab0a600087e87195614c17b8f6e032ac29807e1f61f65185300061f3a6ca30a6000c6e72d94614c0014eb03b28c2980030f9d0651853000637390ca30a6000a7581194614c1058f2e0328c2980030fd9574185300061e32ae830a6000c6f655c8614c0018d8cab90c2980023de1d61185300043f434eca8a6000a75819d9514c0018eb033b2a2980029de0576545300053dc02eca8a6040a3e841d9514c00147b083b2a2980030fa1076545300061ec20eca8a6000c5e831d9514c0018bb063b2a29800317cc476545300063d980eca8a6000c78301d9514c0010ff0eb22a2980021f21d64545300052e432e6a8a60d6b57815cd514c0090f90b3b482980021fe1576905300243e42aed20a600087c865d6414c0010ff0fb2c82980021f61f659053002c7c432e120a600487e85dd9414c0010fb0bbb282980162f21d645053002d5a40ac8a0a60058dc87591314c00b5a902b22629800395d94614c530005e2c10c298a6000a5c86545314c00b8b8eca8a629801795185514c5300243e42ced10a600087f855da214c0090f90abb442980021f21975885300043fc3ecb10a600087d87d96214c00b1f10cb8442980121fa1776485300043ec2eec90a600087f87592504c0a10f90cb8ca0981431d1857194130036b9082e3282600087f87d86504c0018eae3b0ca09820b179d931941300145fc3ac9202608287e86dd5404c1170fd0fb2a80980aa1f21f65501301562f3b6cb18260038df87592304c00dba420b8c6098003555c5518c1300362f282e7b244006c5c505cf648800d9b420b9ec910217179cf51d92200062eb9ea3b2440068f8805d5648800d1790eaa2c91001aae20154592200345f43c86b244006c3e505d3638800d878a0ba6c71001b2e84174d8e204761f3a6a3b1c4000c3d74d47638800d1f100baac71001a3721d5358e200356c402a6b1c40068de87d0d638800d5b501a1ac7100121fa177650e200043ec2eeca1c4000c9c43dd9438800d1f501bb287100032710d7650e200145f43ec8a1c4002a9e83d9143880071bd0fb1a871000ea7a136350e20034bc402eb30c40068f8805d5618800d1e90ea8ac3100029d60676546200053bc0aeca8c4040a3e841d9518800147b083b2a3100fe97a0c76546200052ec18eca8c403fa5e83d9151880014bb07b22a3100169da0764546200053ac0ec8a8c4040a3e84d8d518800147b09b1aa3100169da0763546200053ac0ec6a8c4006d7070985518800d8f0e0b0aa3100169de196154620036b8382c2a8c4004a768758551880094e90eb0aa31001b1d9c161546200363a382c2a8c40bae67205855188001ce2
  | 10 => 0x18a800087f87d9631500010fb0fb2c62a00163e219708c5400243f42eec98a800087d85dd931500090f90b3b442a00021fe1576885400243e42aed10a800087c865d621500010ff0fb2c42a00021f61f658854002c7c432e110a800487e85dd921500010fb0bbb242a01421f21971941402863a30ae32828006d72105c650500010ff0fb0ca0a00031d5c7619414045e1f3b283282802bc3e76d964050057c76c1b2c80a001b6c84171901400069ab8aa32028006c6e505cb648c00d8d8a0b96c91801b3a84172d923038637396a3b246000c6d72d47648c00d1f100baac91801a2f21d545923001d4fc32c8a1c60248dd86dc1438c00533b09b82871821f669037050e3001e4f3a286b1460068ec87549628c001d1a87a12c5180121fa177650a300043ec2eeca146000c9f7650d428c00793ce8a1ac31801a3d21d51586300053ac0ceca8c6000a7a809d9518c0014ef02bb2a3181028fa1076546300051ec20eca8c603ea6e821d9518c0014db043b2a3180fa9ba0b645463000536c16c8a8c6005a7681d91518c0014eb03b22a31810297e1943546302070f32286a8c6005a7786585518c0094ed0eb0aa3180129d21d61546305df2b21ac2a8c6000e5543585518c00d8ece0b0aa31801b1d1c161546305df2b982c2a8c600487e85dd9418c0010fb0bbb2831800ea7e1943506300064fbb286a0c600487e85dd9218c0010fb0bbb2431801a3ea03764863002d7240ac490c601fa5e86dcf654c1af4f501ba6ca980aa9e60374d95301552f41ce9b2a6000a5d839d3654c00187ae83a6ca981d29ea0072d95301553cc00e5b2a600087e8710b654c0010fb0e216ca980aa97a0c42d95300052ec1885b2a6000a768110b654c0014eb02216ca980029ea0042d95300053cc0085b2a6000a3e841c7654c00147b0838eca980aa97a0c71d95300052ec18e3b2a6000a6e821c7654c0014db0438eca9815e9ea0071d95301553cc00e3b2a600087e87107654c0010fb0e20eca980aa97a0c41d95300052ec1883b2a6000a6e82107654c0014db0420eca980029ea0041d95300053cc0083b2a600087e87087654c0010fb0e10eca980028fa1021d95300051ec2043b2a602aa5e83087654c0014bb0610eca980029ea0021d95300053cc0043b2a602a87e87d03654c0010fb0fa06ca980aa97a0f40d95300052ec1e81b2a602a87e87c83654c0010fb0f906ca9800a3e60375d91300053ac08a1b226082c7970143644c0010fd0fb2ac8980021fa1c65591300243f43eeab22600087d81dd5644c0010fd0e3aac8980122f21d54591300246e43aa6b226000e1d5454d644c0010fd0fa8ac8980121f21f51591300043f438a0b226000a7581141644c0014eb02286c4980021fa1f65589300043f438cab12600487e85dd9424c0010fb0bbb284980029d607
  | 11 => 0x9003d17b0db82872000e6760f7050e4043e9d286e0a1c8002c9e7350d629000d1d90ea92c520003a350f3258a400243f42eec994800087d85dd9329000193eeca1a652000b279cd43586400347a43aa2b0c8000a75819d951900014f5013b2a3200029de0576546401fd2f418eca8c8000a5d831d9519007d4dd043b2a3200029b60876546401fd1fc3286a8c803fe1e6350d519000b4ef0cb0aa3200129da1d61546400253a43ac2a8c80bce37435855190001c6a86b0aa32001b1d9c161546400363a382c2a8c80bce374058551900090fd0bbb263200021f617764c6400154fc328698c8000c9f7650d31900090fd0bbb243200021f61776486400347d406ec90c8005ae481589219004b47d0dba6caa03669ea0373d954015d3cc06e7b2a802ba3e849cf655000147b0939ecaa01de9ea0072d954015d3cc00e5b2a800087e870cb65500010fb0e196caa00ae8fa1032d95400051ec2065b2a8000a76810cb65500014eb02196caa00029ea0032d95400053cc0065b2a802ba3e841c7655000147b0838ecaa000297a0c71d95400052ec18e3b2a8000a6e821c765500014db0438ecaa01669ea0071d954015d3cc00e3b2a800087e870c765500010fb0e18ecaa00ae8fa1031d95400051ec2063b2a8000a6e820c765500014db0418ecaa00029ea0031d95400053cc0063b2a800087e8708765500010fb0e10ecaa00ae8fa1021d95400051ec2043b2a8000a5e8308765500014bb0610ecaa00029ea0021d95400053cc0043b2a802b87e87cc365500010fb0f986caa00ae8fa1330d95400051ec2661b2a802b87e87c8365500010fb0f906caa000e3e60375d8d400053ac08a1b1a808bc797014363500010fd0fb2ac6a00021fa1c6558d400053ac08a1b12800087e87d9562500010fd0e32ac4a00121fa17764c9400043ec2eec9928000a7581dd761500014eb023aec2a00021fe1573d85400243e42ae7b0a800087f855cb61500090f90ab96c2a00021fa1c50d85400053ac08a1b0a800487e86dd561500010fd0fb2ac2a00021fa1c65585405f63db80cab0a802587d87d9461500018bce7b28c2a00031b9cb65185400053ac0eca30a8000c5e7319461500018dce4328c2a00029d604651854045e3cb80ca30a8000c5f655cc61500018b8cab98c2a00031bd9572185400063632ae430a80008f78758461500010fd0d3b2a2a00029d60676545400063ac0ceca8a8000a77815d951500014f700bb2a2a00fe97a0c76545400052ec18eca8a8000c3e841d9515000187b083b2a2a000317a0c76545400062ec18eca8a8000c3f411d951500018f6803b2a2a00031e10076545400051e432e8a8a80d8b37815d1515000174b0430a82a00028f219515054002e1e3b2a2a0a800487c859da31500010ff0abb462a00121f215768c5400043e432eb
  | 12 => 0x82a1fe1d51d81211f43ec3aa3b024200a758114360484011f70eb00c0908171b5cb51181211543e43ac8b1ca02bc3c74591639410f27b09bb2872821e5760f7650e5043c9ec26e0a1ca08795d83dc143940530f90eb22c5280af0f1d16458a5014c3e43ac6b14a02993c8750d4294055a38e6a1a85280a6cb2094350a5014cae43a86994a02bd1c7450d329405369904a1a65281421fa1e64586500052f41cc8b0ca000a5d8399161940a14ed03322c3281421f21d645865015e1e3a2c8b0ca05087e8798d619400147d0931ac3280028f61263586502843e43ac6b0ca05087e8798961940a10f90eb12c32800297a0e74586500052ec1ce8b0ca000a75819d161940014ef02ba2c3280030f5d074586500353d400e8b0ca050a79801d1619400147d0939ac3280028f61273586500053ac0ce6b0ca000a77815cd619400d4f50039ac3281429e60073586500043f43886b0ca00087d8710d6194001c3a8621ac3281429da0443586500053ac0886b0ca000a75819c9619400147f08b92c3280028f21172586500052fc1ae4b0ca000a5c835c961940014ef02b92c32801a9ea0072586502853cc00e4b0ca00087e8710961940010fb0e212c32800297a0c42586500052ec1884b0ca050a768110961940014eb02212c32801a9ea0042586500053cc0084b0ca00087e870c961940010fb0e192c3280028fa1032586500051ec2064b0ca050a76810c961940014eb02192c32801a9ea0032586500053cc0064b0ca05087e87d0161940010fb0fa02c32800297a0f40586500052ec1e80b0ca050a7681d0161940014eb03a02c3281421fa1f30586500043ec3e60b0ca000a3e84cc1619400147b09982c3281429da0730586500053ac0e60b0ca05087e87c8161940010fb0f902c3281429da0720586500053ac0e40b0ca050c3f415da41940a187a82bb4832801a1fa0176906500343e402ed20ca09187f865c241940018f4c1bb2832801a4f21d64506500361e3b2c8a0ca05093c8750d4194055a38e6a1a83281424f21d42506502862f98aed18ca050c5d315da319400d0fd00bb4632801a1f201768c65048c3fc32e118ca000c7a60dd931940012df04ba263280a65b209744c650034ae43ac698ca05095c8750d3194057a38e8a1a63281425721d324c6500343ec0aed10ca050c6f215da21940a18da42bb4432801a1fa0176886500343e402ed10ca09187f865c2219400127f08bb243280ae4f2117648650004afc1aec90ca02a95c835d921940012bf06ba243280aa5720d74486500049fc22e690ca02b93c845cd219400d2d90eb124328142d9205624865035f35302c490ca05096c8750921940a12d90e99243280a65d21d414865000792a128290ca029974874c52194001e8a6498a432801a3e2017558e400346e43aa6b1c8002a9f8658d43
  | 13 => 0x5e3c128698c420087f855d260884090f90aba4c1108021fe1573982210243e42ae7304420487e87dd560884a10fd0e282c1108029d60450582210245fc3aa9b22420087f855c364484090f90ab86c89080237e0d70d91210146e41ae1b224200a758114364484011bf06baac89080a3720d75591210047dc02eab2242068f8805d564484051bd0fb9ac89080327dd073591210066639ee4b224200c5f73d45644850b8b8e7a8ac8908121fa1770591210043ec2ee0b224200c5f7314164485058b8e6282c8908029d60450591210063db80a0b224206c787014164484091bf0ea9ec6908021fe1570d8d210243e42ae1b1a42008bf845c3634840717908b86c6908029d60450d8d210045fc22eab1a42038bc845d563484011f700baac69081a3e2017558d2101c5f43ee8b1a4200c9c74dcd6348401958e9b92c6908030fdd35158d214761e3a6a2b1a420487e85dc163484010fb0bb82c6908030fdd05058d2145e1e3a0a0b1a4200a758114163484018f6e0282c69081b1e1c05058d210064e21ceca1a42008bf845d943484011bf06bb286908023be097650d210243f428eca1a420087d851d94348401938863b2869081a3ea007650d210047cc00eca1a42028bc87591434840553906b22869080e3721d6350d2101d4e422c6a1a4200aac8650d424840178b0638a84908163b219744c92100566432869924200ba5841c532484014bf06b22a2908fe9720d64545210051fc22c6a8a4240a3c8458d514840b6cd03b92a2908169b219425452102db240a84a8a4205a6c864c9514840b6c902992a290a47590847054521005d3c226520a4200dc5734ca414840b3590ea128290816ab219425052102dd240a84a0a42dcf2751509414847d8e8eca8a82908fb591c9515052100792a12a2a0a4200dc632dcd414840b7490ea1282908076921d425052102dd343284a0a4205ba4865094148407d490ca12829080fa9dd9425052100ed33b284a0a4201da4765094148407d48eca128290802e9e0d4250521006d3b9a84a0a4200ba78050941485b9e48a0a128290802e96113250521007c2a1a64a0a4200da57450a314840178f06a1462908167321d324c52102d664326498a4205bc4814c931485b7e8ea299262908fb1d1d9514c5211ff2a31aa298a423ed64725453148401e8a64a8a62908036990b744c52100c7a432e898a4200da5745093148401f0a86a126290816f121d324c52100ee243a6498a4205bc6864c9314840b7890c992629080bb1219324c52101763bb26498a4201dc6764c93148403b88ec992629080bb11d9324c521005e3c226498a4200bc5844c93148401b8ee89926290803715d1324c521005e3c026498a42dbf44504c931485b54eb033aec0908121fe1d75d81213843fc0aebb02420487f87d4760484010fb0fa8ec090
  | 14 => 0xf72d45644c4e18d8e5a8ac8988121fa1770591310043ec2ee0b226200c6f72141644c4d38d8e4282c8988029d60450591310063db80a0b226206c7870141644c40753d0db228698802f16087150d310047dc02ebb1262068f8805d7624c407938e8a1ec498803a350f42d89310043fc2ae1b12620487c855c3624c4014eb02286c49881b1e1c050d89310243f428eca12620087d851d9424c4031790eb228498806ab20964509310064e3b286a1262058dc865d1324c4031b90eb226498806b3209644c93100537c12c8a8a623ea6c82591514c40b6ad03b9aa2988169721943545312070e32286a8a6205b548150d514c40b4b90c992a298816d52053254531006ad980e0a8a620599c8750d414c40b5390ca1a829880b271d9435053102dca40a86a0a6200b7181143604c5bf4eb033aec0988121fe1d75d813142c3fc0aebb026200c7b805d7604c4090ff0fa8ec0988021f61f51d81310543fc3aa3b02623f87d87547604c4014f100a8ec0988029d60450d81310063cba8a1b026200ad983143604c4015e302286c0988029e61c50d81310063cc38a1b026200e3a84143604c401c7308286c098af796a0c50d81310072cc18a1b026200e6a82143604c401cd304286c0988031e5c850d813100739408a1b026200a7981143604c401ce302286c0988029c60450d81310047dc3ac03026200a7885580604c4016e302280c09880f271d1431813143f2c282863026206c78505c8604c40b8bae7a88c09881a9e20351181310353c402a23026206a7a85d40604c40187ee93a2cb108169da0674596216f53ac0ce8b2c4200a7b805d165884014f100ba2cb1080297a0c74596210052ec18e8b2c4205a76819cd65885bb4eb0339acb108029ee0173596210053c402e6b2c4200a3e841cd658840147b0839acb108021fa1c43596210043ec3886b2c4200a3e841c1658840147b08382cb1080297a0c70596210052ec18e0b2c423ea6e821c165884014db04382cb108169da04705962118d3ac08e0b2c4206c7a701c165884010fd0fa02cb108021f61f40596210052f41e80b2c4200a5d83d01658840d8f0e1a02cb108169da0440596210053ac0880b2c4206c787010165884010fd0f982cb108021f61f30596210051f42660b2c4200a3d84cc1658840d8f0e1982cb108169da0430596210053ac0860b2c4206c78700c165884011f700baac91081a3e20175592210243f42ee0b24420087d85dc164884014eb02282c9108031edc050592210363c380a0b2442008fb805d5638840d1f100baac7108121fa177058e210043ec2ee0b1c4200a758114163884018f6e0282c71081b1e1c05058e2102c7b40eeca1c4200e1c43595438840b1790eb22871080aa720d6450e2102c6e43ac6a1c4203a9c8458d438840174f04a1a831080679209744c62100
  | 15 => 0x2282c5208163721d634ca4102c7643ac4994820087f855ce60904090f90ab9cc1208021fe1572982410243e42ae5304820487e87dd560904a10fd0e282c1208029d60450582410043fc2ae1b1a820487c855c3635040517908b86c6a08029d60450d8d410154f436c6a1a8200ba5821c543504011f700baec4a081a3e20175d89410164e39a87b128200e8d43ccb62504010ff0ab86c4a08121f21570d89410053ac08a1b128206c787014362504090fd0a3b264a08021f614764c94102c5e432e89928200c9c7650d325048187cedba2a2a08168f21943545411ff0e31a86a8a8205b348150d515040b4790ca12a2a08034ed007054541005b8c08a1b0282e0a75819d760504090ff0ebaec0a0a3a1fe0575d81410063dc02ebb02820487f87d4760504010fb0fa8ec0a082a1fe1d51d81412043ec3aa3b028200a788054760504014eb02286c0a08031e5d450d81410055cc20a1b028200af18114360504014f30e286c0a08031e61c50d81415f71d420a1b028200e39841436050401cb506286c0a08039660c50d814100735410a1b028200e698214360504018f2e4286c0a08039ca0450d81410053cc08a1b028200e718114360504014e302286c0a08023ee1d60181410053c42ac03028200b71811406050405938e6a18c0a0a1f8e14143181410363c282e43028205c3d74d44605040d4f101a88c0a081a9e20151181410353d42ea03028200c3f749d1658c4014f700ba2cb188029e20174596311fd2f418e8b2c6200a5d831d1658c40b4ed03392cb18a4e9d60672596310053d404e4b2c6200a79809c9658c4010fd0e212cb188021f61c42596311fd2f41884b2c6200a5d83109658c40b4ed02212cb188029d60442596310053d40084b2c6200a7980109658c40147d08382cb188028f61070596311fd2f418e0b2c6200a5d831c1658c4014dd04382cb188029b608705963102d3b408e0b2c6237a75811c1658c40d8f4e0382cb188021fa1f40596310043ec3e80b2c623fa5e83d01658c4014bb07a02cb1881b1e1c3405963102d3b40880b2c6200a7581101658c40d8f0e0202cb188021fa1f20596310043ec3e40b2c6205a7681081658c4014eb02102cb188023ee0175592310347c402eab24620487e85dc1648c4010fb0bb82c9188029d60450592310063db80a0b246206c7870141648c4090fd0bb82c5188021f6177058a310053ac08a0b1462058bc87591428c40b1d90eb1285188021fe1574982310243e42ae9304620087f855ca608c4090f90ab94c1188121fa1f75582312843f438a0b046200a7581141608c4010ff0ab86c8988121f21570d91310146e41ae1b226200a7581143644c4011df04baac8988063b20975591310047dc02eab2262068f8805d5644c4031dd0fb92c8988032bdd0725913100667b98e4b226200c6
  | 16 => 0x3181517571c20686302a2e9c757190c605440d4f501218c0a88029e60243181517472c18486302a200a7b8050c605440d4f100a18c0a8a1f8e101431815143f2c18286302a20687e8710c60544010fb0e218c0a88038750c431815173e3ab8886302a206a788010c60545cd8eae3a10c0a881a9e203421815172e3ab8c84302a206a7a8090860544014f301210c0a88029ee0142181510353c40284302a20687e8710860544010fb0e210c0a880297a0c42181510052ec1884302a291a768110860544014eb02210c0a8b931d5c442181510353d40084302a200a798010860545c78eae3990c0a881a9e20332181517163ab8c64302a206a7a808c860544014f301190c0a88029ee0132181510353c40264302a20687e870c860544010fb0e190c0a88028fa1032181510051ec2064302a291a76810c860544014eb02190c0a8b871d5c432181510353d40064302a200a79800c860545558eae3a08c0a881a9e203411815154e3ab8e62302a206a7880cc460545518eae3908c0a881a9ea0321181510053cc0642302a206a7987d0060544018f30fa00c0a881a9ea1340181510371d42680302a206e3a74d00605440dc72e9a00c0a88029ea0f40181510072d41e80302a200a5a83d006054401cb307a00c0a881b969cf40181510372cb9e80302a200a7982d00605440dcd4e5a00c0a881b9a5cb40181510053cc0e80302a206e7271d00605440dce2e3a00c0a88038ed0740181510353cc3e60302a200c7987cc060544014f509980c0a88038ea1330181510051d42660302a200e3984cc060544014f109980c0a881b8e9d330181510371cba660302a206a7a83cc0605440dcb507980c0a881b969cf30181510372cb9e60302a200a7982cc0605440dcd4e5980c0a881b9a5cb30181510053cc0e60302a206e7271cc0605440dce2e3980c0a880396cc730181510053dc02e6b2c8200a78805cd659048147d0839acb208028f610735964102d3b40ce4b2c8296a75819c965904014f501392cb208029e60272596410043f43864b2c820087d870c9659048147d08192cb208028f610325964102d3b40864b2c8200a75810c965904014f500192cb208029e60032596412051f420e0b2c8200a3d841c165904014bd06382cb208029760c705964100537410e0b2c8200a6d821c1659040b4ed02382cb208f69d60470596410363d380e0b2c820087e87cc165904010fb0f982cb209028fa1330596410051ec2660b2c8206c7870cc1659040b4ed02182cb208029d60430596410363c38060b2c820087e87c8165904010fb0f902cb208169da0420596410053ac0840b2c82008fb805d5639040d1f100baac7208121fa177058e410043ec2ee0b1c8200a758114163904018f6e0282c72081b1e1c05058e410243f42ee0b14820087d85dc162904014eb0
  | 17 => 0x92a20087e86dc132544010fb0db8264a88165da04704c951004bac08e0992a2aa977815d360545532ef02b9ec0a8aa25de0572d81510053cc3681b02a200b5a83d0360544016e302206c0a8802cea1330d8151005b8c0861b02a200c3d74992605440d4f501324c0a88029e60264981510353c402c9302a200a5e8319260544014bb06324c0a881a9ea0263981510353c402c7302a200a3e8418e605440147b0831cc0a881b1e18172981510353d404c5302a206a788058a605440dce0c0b8cc0a8ae75c5c760981512a6b9b8ec0b02a200d35719d0605440dc74c13a0c0a89024fe1d74181510069ab8ae8302a206e3a605d0605440187ec2ba0c0a88034dd8574181510069c402e8302a206c3e605d0605440d878c0ba0c0a89021f61f64181512061f3a6c8302a206a7a80d9060544014f301b20c0a88030f5d264181515563ab8cc8302a240c3e7459060544014f700b20c0a881a9e20164181510052f418c8302a200a5d8319060545898eae2320c0a881a9ea0064181510068f3a4e6302a200d1d749cc6054401aaae3398c0a881b9698273181511fcafc3ae6302a200d1e745cc6054401a3ae8b98c0a8803555c573181510372d302e6302a200c5f645cc60544018bac8b98c0a880317d857318151006abb0ae6302a200d58805cc605440d8bcc0b98c0a881b1718173181511fc3ec3ec6302a200c3d74d8c605440d4f501b18c0a88029e60363181510062eb9cc6302a2a9c757198c605440187ae8b18c0a88ff179cd63181510053dc02c6302a206a788058c605440147d08318c0a88028f610631815161e3ab88c6302a206a7a8018c6054401a5ce9390c0a88034b5d27218151006a739ce4302a200d4d739c86054401acae3390c0a881b9a98272181511f4b7c3ae4302a200d2e745c86054401a5ae8b90c0a8803539cd7218151006a6b9ae4302a200d65715c8605440dcd4c0b90c0a88031bd91721815100636b22e4302a200c6f635c860544018dac6b90c0a88031bd857218151006b3b0ae4302a206c6e605c8605440d8d8c0b90c0a88fa1f61f62181510061eba6c4302a200c5d73d88605440d4f501b10c0a88031b5ca62181515463ab8cc4302a206a7a8098860544014f301310c0a88030f5d162181510062eb9ac4302a23ec6e7258860545858eae2310c0a881a9ea0062181510053cc00c4302a206a7481d8060545db6e303300c0a88021fe1d601815107e3ab8ac0302a20097b8758060545d96e702b00c0a88029e61b40181510069cba680302a200e3a64d006054401c72c9a00c0a8802d6a0f40181510353dc3080302a200b718110060544014f30d980c0a8802cea133018151006acb9e60302a200e5a63cc06054401cb2c7980c0a881a9ee183018151005b8c0860302a2ebc7571d0c605440d4f501a18c0a88029e6034
  | 18 => 0x8018f2e0286c6a100aa7a1b6350d4200cd743ee4a1a84019ac82dc54350805938e6a1ec2a10021fe1570d85420243e42ae1b0a8400a758114361508011ef0eb08c2a10021f61e75d81420243fc3aebb02840087f815d760508090ff0fa8ec0a10021f61f51d81420053ac08a1b0284008fb875806050805938e6a18c0a101a3ea0375d91320047cc06ebb22640087f855c3644c8090f90ab86c8990029d60450d91320363d380a1b226400c7970143644c8090fd0bb82c8990021f61770591320053ac08a0b226403a9e86d91434c80339d0fb9286990067320b7150d3201e4e3a287b0a640087f855c3614c8090f90ab86c2990029d60450d85320047bc3ac230a640087d879d7604c8090ff0ebaec0990021fe0575d81320243fc3ea3b02640087d87d47604c8014eb02286c0990023ee1d601813201e4e3a2863026405976819c3645441f2eb03386c8a8bcb4ddd37159151006b9b8ee0b22a200c7986dc16454401ae703b82c8a88031ed877059151006b9b0ee0b22a200d73711c1645440d8f70c382c8a88034ea1070591510063d320e0b22a200c78641c16454401a7686382c8a88035c60470591510063db08e0b22a200d73611c1645447f0fb0fb26c6a89030f9d364d8d510053c402c9b1aa205976819c3635441f2eb03386c6a88fe1f21d6458d510053c402c8b1aa2f1d5773dc56354401ae6e3b82c6a88031e61b7058d51006b9c0ee0b1aa200c7b61dc16354401ae6c3b82c6a88035cdc47058d510363dc30e0b1aa200c7b641c163544018f2c8382c6a880356a0c7058d510063d318e0b1aa200c78631c16354401ab486382c6a88035c6047058d510063db08e0b1aa200d73611c163544012eb03bb286a88025be097650d511f4b6412eca1aa200977815d943544012f700bb286a88025e2017650d511fc9e43ac8a1aa23fb1c8359143545e166f02b2286a8802ce2016450d51204ae43ac6a1aa240b1c8458d4354401c3ac8b1a86a8bbed5e056350d51005ac402c6a1aa20087e86dc143544010fb0db8286a88165da047050d51004bac08e0a1aa23e87d87d93625448187ce9b26c4a88029e20164d89511f43ec3ec7b12a200a788058f625440b2ed03386c4a883e5d60670d89511f43e43ac8b12a200a7880591625447d0f90eb1ac4a88029e2016358951776b3b96e2b12a20097581dd942544012bf06bb284a88fe5720d7650951004bbc0aeca12a20097b805d942544012f100bb284a88fa4f21d43509511fe8e39a86a12a23eb2c8250d42544010fd0db8284a88021f61b705095102cbb408e0a12a200975811c142544012eb03bb264a88024fe11764c9512049e422ec992a200977815d932544012f700bb264a88025e201764c951004bbc0ae8992a205974815d1325447d2b90ea1a64a8903471d1434c9511f5a6412869
  | 19 => 0x3800d00100900003400100200100b00400000200000400a00600500300100700600500000300000600600000e00100600301f00000400000000001001100500000300400300100000000900600200500000600d00100000000a00200000000000900000000b00700300a00300000000100000000100700000800700000000500000100005100400200100300100200200102700300001900000800500200500900001c00900a00000200200000800600000c00401100302500000000700c00704600b00000000400800200800100100000001900000000000200400000000500200700002000800900100100400700300500000300200000000100000000000900000000500e00000600000200300100300000f00300400300900d00000400300101700100000200000000200500700300000700001404200000f00d00000301401100002303400000200100e00000300002800700001300200600500803200200100800500100700100100100f00100a00400200000000000c00000900200e00300100000200100400700200000000200200601100300000000000700200500200002700500700100700100000400200600300000000901c00100701400300300000000300000400400801000300100100100600800001200400800002600502300100200000300100600000000000000000600e00000000106a00000000600000300106200000000200f00000000900001100000300100003c00000301000000400100500801700800400201600200000000d00000400000800300500000600300400600000000300e00200101602d00100b01400000400000700302601800b00300000300200700000200b00200301300000100000200d00200700000000700800700700a01100100101000500000e0000010030000000000020000010040000010000050030000050030000043fc2ae1b12860487c855c36250c014eb02286c4a18021fe1570d85430243e42ae1b0a8600a75811436150c01a3886bacc2a18036310f72585430068e21aea30a8600d8c435c86150c0b9ccc2b90c2a18023de1d611854300672b92c230a8600d98439c06150c01b3086b80c2a18034710d75d81430145ec26ebb0286038dd83dd76050c010fb0f3aec0a18030f5d275d81430062eb9cebb02860487f875d76050c0187ae8baec0a1803175cd75d81430043fc0aebb028604c3e755536050c0793ae6aa6c0a1813179d553d81430164eba2a7b028600e1d5454f6050c090ff0fa8ec0a18021f61f51d814342e1eba6a3b02868ec5d73d476050d0f87ae8286c0a1a1f175cc50d81430053ac08a1b028600d8c435ca6050c01a3887baac0a18023ee1d60181430347d406ebb1a84008f980dd763508010ff0ab86c6a10121f21570d8d420053ac08a1b1a8406c7a70143635
  | 20 => 0x14900000000007e83bb91d400005f00000000000002dba0e800000000000014c6a1e0db00000000000be987400016500027b00005774de800066e2e504d0abd46a3f113e2054bf07a23aa000121a79849889d80000000000000dda1783fe9e10a9266b00008406da5443ab800103235b0438000fd67f946a89040000000000000000145000058cd1876a149000000027445d000000058f0698fd00001d21570f3512c1d701e9bcd3b005039009c8adaa121e18d4ca6a4913cc857d2e441a072a2508941b43321f1805813a534942c51452e37fa98514a9cb3340b29420a293dd1e084d605e2129e6848c7c117020b0b063514e70d842601a7391a8c8c2a12850b000122c00022e8f58b9e901277191c7b80003daa5046847033a88528db624d25c0e348a22ad39b000000049c00000002786f2000000085a2a907d8000176a4f51b81240000000000cac4e68b4000068c00051c0000ed88e425518911d069a40c0002788e300004f304f520e00b00500400000600300700b00101800800a00000000200400000100000100100200400000200201100200100c00400100000000600500100500700300000000204700001201100101a00100000c00100200000800000b00500201100200007900400200f00c00001d01b00000200600601200000200200c01300100c01a00600100000300502400200701000700301e00100100000400000100000000000500100f00000000200d00000200700100c00900800100000000000000200900000100100000300000b00400500600801802300500400000000e00000600000000600500200100c00801600200000400600700100000100500400500300600000000000500000000300800b00300100300a00600000e00a00800000000400800000000c00000000200100700900100101500000100700200200000000400600000d00100000100100300100e01b00600a00400001500600100b00f00000000101800a00000000000200000e00500c00000300200200200b00900200900000b01302200200200d00600e00500601c00004900000100300200300201601000e00500b00001600600000000200300200000601c00a00507200000a00406d01000100400300600000000200200200300000200400000000000000000a00f00200300000400000000500100000000101200401f00300b00900300100000100800600000000000300000d00100300001400100f03000e00100100100400000c00101601700100300200100d00200100000000100a00f00200d00e00800000000000001500b00500000500400100000201100000400300d00b00601000200200000000900100400800401e00104b00a00100000300400100600400000503100000200300b00200100300000700e003016004000000
  | 21 => 0x54200000014980007334070000b02000000225538059048c1f549ba44200000000000001220000ae20004c20000390000321a8acf428262dd1f844182622530000e0e99d000000000000005000000000003eb00010ac19219285d8deea411259464bb202517d25cd0782502a1a02c4163362f8a34c29aa1549a81a489e8760a800012000000000000000000215a1b80005a914f258c05c8db2e114f063c9cf31022d825e32d0001b70fae1953ac8000b6057e01a1fb029c92e2e3839800000047a1d080003a90ee00000008160000ee800000000000000007d134200012688f900014d80002660000000a6200000000000000003621cfcd445274941b2860605a2300000d043f5000000000067e0000068f068393ce906d166a642fe1f64dd214603300000009202d7276c0006630000000802000079000068e0812d593a847e69d0001c84ce00ec38b0000cbe92649f0634d7284334c25bcbc40002240000ede4d01fc000033e7e515e00003c41262cc812c8c80004b8a1f800026825e06194406c61b400000000002bd16f47d40000700614fdc530309186835a21b08c896c0000000001af49b800000000000004da000000101a00021604e49fe50a0c7152d4284b71421d7437e6fa1229268c460002d610880007d4000000114c5e9484a57c664989095a280a5860119d8210ad89661c79d492605b40001bc458e0ef31598989da8c13df88b42960e84d607b00000003ee810c8c48ca2f421a8db411f2239d1800082400001d46c800023628200000001fe919c0001520000000000000194998880a0004ee97ed3d689221e0ae48ee72d4f28cbc886a3b000272139a7c020494054920003f69560bae10d0000fd87825b2000000000004a2b083e4f4c6a9000263cd0695223b25e144899b2ae8970f20582304168c17269f2fd20c800010e3d3a234000a222e600001e8110000000004c79e4e098845c48360000000b9600002000005507fb0ac18e80004bd05388611b279230517803b483124ba6d00007b94201ea464611136600010f200022b8000cd8000405191057c3b211296880001bc1c9845466633d00005fc00000b0dd8000d0c85e00022147881e916418e067e86524199e400044c00684100005e110a0bd87922de00000013f03270f41ad80001cc00002fc00048b000000000048e49282500006920000000ffe7db4649a9c2f641828900000008a732726dd0b69e72c906bc6180000a1a71873c4db2d0800054063f0000000a04a1b05113480000001602388ef887545900000005c300000005c238a32d148cd685da1870c4c00067f3e91b1d0aa55616c9e7c51c65d13294ec054a171a794f8f609d01bf1c38e260000ef237400090546f8000f361c0000127cf483b42e7015400000000000000000000
  | 22 => 0x36128f92900452ac8efc8d29fc4a588249ae4ad2170b3c7f86952268a5848e31729d275cc5c579306a62c2e2690129039143e6fc2fa064c5c89de2ec0f3c0126d02672564ed01b9011a6903660a915a0ee529206e093941536a4fc28d22104623e953d03d4010471187a9a1270a4735500000000000498f654be0000001c785a80000001be4a5415919613d41c69173c38c2847a1131b4a5c11ca5f542e02d44787121d11c345a20be2150dd922616b1ae90d8b4a9954b38e548a445f0379c007a4480296a5400003261b280003e6a6230b92ac7f4429000000000002241700004560001d5a24c0000460000ab00000001af80005e82e3000131c00000000000009a88d42781ef800000000013440000004a88bbc99087300a0e94ec01a00f18bd4aa2000000296d36677d4e500001c49471b580000000000002270000105000000020400050d1cf115023942487952b69ee4e4a0c065400033c07e400080c4820670cb23ec000000000e9432460cd4cde00017389fcf7a0c014400009f61082041d7c00055b00000000003190000000f8a1b10000eb837c81c38d96ecfb484f000145481e43f235981531c2232be13009c84591af23c0fc449e00f9b44d2e3784ca00010100eb05e885c82e05834c84012f22a71d80ce01922da0000a7ca9a0004569b546f28271731f0cc0000000025e91e25873ae1e24a6893a05424a94ba4e700019a43645e300000001fa000429800000073700014fc2480cc35307288f883e07b8a702ba5971941d684c27454cba0a123464b19f099cdbc5d41ac9048dc20002178884d1c4e304181fc2986e33a012d54e400000000014143970000304bd80003b121ec000000000195547000022c00009040c80000ffc00074802d80009309872069f2c000371358855c4740aa471a1e030472e28e83513d2a501e409a852634e1e50000000000529a004dde00036a00004e29540108e3800084c44580003545a616b10646fe5cd1c4a7c83b00192701f3800013637219f027e3565361dd00007b63b30000000a7503d813428025a000018d0e099c182933d40c0000aa13e4b164f700012ccb0888e3dc00000007bb345800000000000000000008d600009ed1901dd2fb91153f6263001a0ec09e6ba2a787108a80b81a90fbc0002fe0580980e4800000024b40007671801904c180000fa1e14d8a908225a92c07c87251a289d3221cf430071c12c7ea4dc0000b940000000db07422703f391b855400051d0f008fc64900000004241254cf274c8f073b0000d9825861b3db932cdaca601e385a40005d52299f2529a00000028844dca310000000f500004f8832c00070902e0add3fa00033a1ef00004b408f00000049112cb0000e98000000000000000049580a4ae86e522209653a86b82528a411fe2a317c1cf4aa41370000000
  | 23 => 0xcd920000001b8800028624380014ec00051e05f93ec19039d1ce400069438f8000c940df0000fa056490630f0c743cc7260000bf51f40001cda648ac650937a800080022022d800000000000010394a89aa36c800105e47d0f20000a204233f1a614000a2a27c25a07020003d580003746114b22510a7264d3809a2006e7fe444a5a80b200033025847a80002b48c7000083f0000000ba40000000b40000a25502800003802f4e893f41aa3f928b00011ee94a000000000087c0da81d14bc92f3cb81d880c76545593a0fe467748f88010d28645038bb000092c4fd0000f548002bea5ecbd493d3d61d2c9541b827791b42b400040e800075e0003c717b463608c1271fd517c68000280006742c34659db856a83d2f5a5b12840003c4028c1567440d60a08dd60475019e8cb2a91e08d9430d968d13b900c51c28c2000000000029a0000f44000a6e29296f89522a51ce800094e18c4d6889000000053b997074828f00029480000002709308fa613b30729cd054a2307b17144500734761674660235382800033a7610000f6cdf0000000200d28a0004330b2d1ae7df3e686045aa0002760001070000431800000069b000247530600000029e40008c74d91c6400024c0000244f64a781d8954c2d44ae3810000020000297960131010b42422600005680000000dd88f30001a9528c89b3191a8465c6542629504ee621c1f08d0400024f4620eb44f48fc0d8000086401802e80000000000000e2c0000044ba00000009c400000000000000000000e580530000000cae78d40900009b22df19026313fc00c1c39d58ac88e4000182cace0001369e4c7ae84e00011a11d04024c9a6951720e700016c52bc00005d20cca6e1a2425a8d800030600021888c612e0001264d0239f1b11fbc7ba53820e95d91320000001af061626925f0e807bc6222501d4c000000000000011aa3d1a4a9007c40002d400000000004de221c0261a60f7a014c4a8c506e94182d803a393a7907cc0004080d70c32183315223c6c08bb19c80006d47c72c49284c5e8de254296000059a42d0a9038c1df40f23ed2246100001ad4000000000257400085041280000008f645c25ac00047a00009907e000012b0000c06000099177000000000000010de23703297e4d5a3500691a3c000299382157000000045886014165a039400001fe00004320600008594211740d123b800022c0000000523169c00017a31812e40000003c30000acc0320208000000133000134d1d41d64f000000007c415300006f60003739a1545c5330e0a9200009273ac03cc19a3d534f1f209240d60120b5c5447694ef9c8815c120201996c29e06c1a41704f5e93c3d6a2f4994598283909c2627b44818158b2225f3fe20b50b07143cb20dd09a6e019887840226661692360ae00893d00e0002a4fe
  | 24 => 0x106708293d416d3e60e08e1009b43fa1f4c260000002824aae1351740c1c23a7ae0001b3934e78114c000023000042f8bdc9128ed00009011a000036ba7b49ca809000005cfe0a1836c12ec79616828680008d49960000a314086b31360fecd5e15300023e12da0002c689e011c4260fb1d4073470b00013240600003ad8db92149d2038879d1fc0000e8204c384000208000100843a000089cc624f3356284cbfa00002a0dc0c6c5a4034029949c6cd395014890c8900a888b01d242400000000000882e30bfc28221600000008803ed4be15408aa0610001d9000077f30381380009c333a80013b499032992fcc90a660708afc5ba25d240876c69691c00000011e41a40002450ff056e1f9859800000042912910a849d0af01100005d100000cc90a07a35b95cc00046f00014104085de21c0000bbe93b01c0e453e84130e5a78c0003a32f798081d4000000228cb90208000253028832400000012040002aaa9c41dc71c1ff1578f9e2360639e5061a52100000007549a2000175800003f04f1d351ce67b04ba634eea6f0013810841a3c610d1aec0000820300000c284a3000205079800040b82dd27e9a600000010346e615d064418470f49b800000038500029bc00082353594a02ee00000d96381b853d162901d1cc00007d08540007d042295bc9601670d4a9354ca0000ad80000000000000e700003f200000009100004bf246515e47352b9afc2aca43499a8cccc2a390b91078c84016109848435c00012b979000000000002c438aa552920000cdc2b036090f4bba9150000ea07580002588738f160002b000011981383e50b092529f03b5a3493f213e34882600000001b7a67c00071d28780000ee00000000010e20000000000c5a0000ff02f00560001cb1958b181870001e9420e7dc3398424e9c0af40d86a0ddc0000878000dbe54200023b837a0280000d30d348c6000108040200031b800062c10a3b8000000000000000000006a42b5989050a1f100028fc4fa34400529142186e84bf9cc087670a0688580bfc00000016700002dc0000000000309050a9ec88200000014007203be26f092057a578430a6847be7383ce07247a059b35f12410567f31dea9d0c9e8ac51310f80000000260bb80000004d700005e000044323bc39a78f4df89603a677b0000000f14000397a4e4a568470000000c8a00000017fd22084a436a2285760000001df8fc00001749bd90e8a5c2a61210bdc9a81cc270805a2970000000df6000395a8043d43550001568a8047000000005981fc4d880000005bf39920a40c800028b91701200ca1dd8000c301163d999180003bc0351e546b4280000130c0ae0d831d8b6c0000000000a2ce222263fb96f12ea3752b917cd08c3342669a80fec40b2330d0d3fe000266058800000000006dca907151ec1a4
  | 25 => 0xc84a60c308e0fdc8f61fd18c243113a0803a3a8bc53a20306f00d400052020202b076ea191be01f52ca0001190314dd46c0103a0191c0310000000000084146180f0000a302c280006e40004c305080000002ca27840400004dd06280c47de4c50000c680000001f980007f100006606ae0001f700008141f74ee29c050667644f194400024a0358e5145a8da1c60000d601ab314000116a00026f95289d601d21980000009ab4aa964c00092103e275456622919080000009a04b112b0dfa74128f0944b5e9a316c111847c7631110b38d565ad2a30c68000000000107000000f24a9d24bce33c4dc84a87848eb102800000023b407895000015c000000032861c11800000001f000026f80009220ff9a291100005071ab926c1842b11140cfa00037f250000038818400013e62490ba13987c6a1d0ba93892ac19e37a08cd4ce0000fd0b240000d000005901b41341c215947c89af000246d19a0000520000b66779433800000000003390c4e6a7d8000051c000953000189c00000019102653526062452244d1a00021b99009ac5e52cf96d82de2022bfa1a13323633af13a40e000000000012ee61605993193ac00052200005f28bf3b88c54cd445a00000000008110000000be051f18f865c96c27e00000000003e730780492c000000000000001d123f800000097643d17994b418b31f233c5281a130fa089334000000174c00000000007e068037d2511a1c00000041a9fe8c7a51b29482141644143e101208bc49400019405e6416160a370a8a5c008093d85a60004e38d281161fb02880ed00e743364260521e0004d81ec4f225db1e28bc400065e03907b820ca561759184000000049142052a2f203f24c91000000000ac456c672000090cc660d700000002dc60400025700000000000018eec5c422b08380000001bd000000000000001e0000001329226800048f4ac1ac87d60002990000a302771e70000eaa0000000000228000000000000018f15c00000002fb0001c182528204361fa443c11a0bca2a8aa80fc4c000014a21d5000000000000000028a10040d900000013ea0002328f4d11822f11c055486aa0d1558764e1842808b9de0e7c0004eca8443c0000000207d3ee0000919c5c00071027d21740004393c01c68abe00016224907327f41c1a2b8a1c76c0b827a000088110c9cc51ea51104f800019e28141a107c0005c917500000002750b983b400063508180007ca5f20000310cb00001da800000052250e07d4b1474f0000d5141e5034bea5a4a9c98206d8000e52000000000014a00014486650ae0000000e980f200005b16d4e948bc30498e470c20601b28304224d507c0f693766dd0001b3caea8a218880004bc000392a53d1484b204e88b82243e02b529307246a80000624b1019a000087458c5f65210c083da85
  | 26 => 0x29a800000e000000000054700000000006672cf1b4cef414811a0000fc89cc25d13114da4300cb193000008f2dc8000608479137a27c2448972270a4445496e0450b3529c415180926c43e4490f58000d2c09c21a0000822000336a8085360000b0a7bc03c63c249a1ac6e86712bd9e30eda18810784b46b051404aa300000377485800062887700005f051a6c345481b46e60fe13c80000000002578d9ce6849605a248c8420004508bb49e48fd52c82b510662c3691a8d19c5131a321103362422c30694cf44c144116e038695717e0318000000000243800066500026614003a727a0000b541d44e2a8b12b48b71439a714943b300003c09b034527898a504203900023a536c0f124687
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x19337460450585200064c1d1811416148001953736045058520006541cd8114161480018717060465185200050d644655d061480014559119573185200064c9d1811406148001931746045018520006549cd811406148001951736045018520036585c981140614800146591a08765452079e58606721c15148001929845c870545200065260d721c1514800145a9399070545200050ea52631c151481e796181c84705452000558644505ca414800147191143765052000558644505ca314800147191143764c520004d8a6050d852148001a2765610614852000689195841852148001a476560c614852000691195831852148001361981406148520006c8610501852148001b418314061485200069814086505214800b2a498591414852000698140864c5214800b2c49858d31485200055864450dc9404800156191143724c1200365820171546204800121d9810d6550f10005986445058920c410f21e9810f6550e1000487a6043d95434400145a9399070545100050ea52631c151440014389458870545100051624d621c1514400187076e0174545100361c1d8805d1514400187076e0173545100361c1d8805cd514400d870801db62545100060d210765895144001854831d962545100060d1db84589514400185476e0d62545100360d1d9841c1514400d8547660c7054510036191d9821c1514400d87076a1870545100364c9d9841c1514400d930766107054510006c4612831c15144001b128460c7054510006c4611831c1514400d9527660c7054510036541d9831c15144001b2184a087054510006d060e821c15144001b22846087054510006c8611821c15144001b42836087054510006d060d821c1514400d962766087054510036581d9821c151440014709654770505100051c25951dc131440015519321d51901100055864887546404400d870869d951901100055464c8754540440015309761151501100054c25d5150540440015319421d518c1100055864887546304400d870869d9518c1100055864b7454630440015319421d514c1100055425d83545304400155097545314c11002f141d9514c530440015319421d51881100055464c87546204400155193dd151881100054c65373546204400d07696a1d51481100349ca5a8754520440015609760951481103569821982545204400da6086dc951481100069821b6254520440015609754521481103559825951485204400bc607654521481100341e2418710d65041d185870a0f40594107560e1c284cc1650400d23890614735901000607615731cd640400d258906147458c1000607615741d1630400141d9510f7650c1000507654435d9430400121d9810d6550c100349a2418510d6204001a0d8550c43588107469214283d0162041d5a2850a133058810
  | 1 => 0x10351a241635c8605440d86a805ca62181510061c5c58098860544018717160062181510060761d4310c60545e9c157150c431815143e862014310c605440185571a0c4218151006155c58310860544010759760442181510061c5c580108605440183571a1032181510060d5c5840c860544010759760432181510061c5c5800c860545d125b97a0f40181517449665e83d0060545d1a1a74a0f4018151746865d283d0060545d1a4a72a0f4018151746925ca83d0060545d1a5271a0f4018151746945c683d00605450fa1a8460f40181517548ee5e84cc060545d523997a133018151756869ce84cc060545d5a1973a1330181517568a9ca84cc060545d5a2972a1330181517568c9c684cc060545d5a3171a13301815143e86a0d84cc0605440187181dc05058e41005076547650d3250401a198460c50d81410061a61d821436050401a298460850d81410069260d821436050401a328460450d81410068c611811436050401a528360450d81410069460d811436050401a628260450d8141006986098114360504018717260450d81410061c60770141648c401867726045059131006191c981141644c40187181dc05059131005076547650d424c401a198460c50d81310061a61d82143604c401a298460850d81310069260d82143604c401a328460450d81310068c61181143604c401a528360450d81310069460d81143604c401a628260450d81310069860981143604c4018717260450d81310341e2418710d65885d185870a0f40596217560e1c284cc1658840187181dc050592210061c60770141638840121d9810d6550e2100615dcd8114164484018547360450591210061c607701416448401837746045058d210060d1d181141634840187181dc05058d2100507654439d9434840109d9810c7650d2100507654431d9434840148d9210c7650d2100525644431d9434840b52497509515052102d5125d32545314840b644964c9514c52100d292597450931484034c4965d1324c52100607a1d4310d6194001a15436044358650005076577650d329000141d95dd9434c6400061c5c181143635000187170604651854000519644655c8615000181d8460c76545400051c644401d9515000141d95dd94350a30005076577650d418c0018717060450d91300061c5c181194614c00146591195721853000607611831d9514c001471910c0765453000691d9582185314c10f09d9810f7650e200050765443dd9438810f49a9010f7650e2000507654435d94388001a318458470546200069460d611c151880014719114376506200051c64450dd931880018717060450d91200068c1918114164480018717060450d8d200069418d81141634800121e9810f6550d200055864450dc9434800d9637260450d85200061c5c1811436148
  | 2 => 0x780440b0be220064712a2a9ae000a45100e6e8005812e608000f10610800299927719c498005c03400000852105a0ea830a8049da209004b1ce269c23c8c48491208a047a9084d16e130ba6a8323b0fe721b0869d20c1f280124790108714c7d1c05f838061843c14a661d8369fa2f06832002340b2021a805940878000001c00072808007d8361186a74000380a05d20a65966000001399e00176000141280075000000006c8005c9624300009854000e25e05800000000a2718c24e0ac2005a78800000b617800001ca0296a6f1fc5086c6317a0909c3e09062990370484f1942b8003b83a3d0c6428202c1324c1a26e004779ac1411a3f1a61b8c0248e4668de7992257886681363518e068d8541581c0ce258607b8d21997c0f98055000459464389e4e8b40a00c6d9884a05c1e1c44816447800228d67e102548cc4614e1487a731481f02e6f9f02e08c7b20e440ca82000000fa001d67a0565b000001140008e000843a000000f656a16001561000000000000741f80007800861044f95c6d1fe69206000641d862260000a8000009400000000e66180a31000540005038340002008081c05138102c07038d408000004412080089c0202020002204010200c01180000203000102e0001808380007814000100000000c010001201008103202018140207088000002040740e0d05838001610038080500024000a00447660435d66150c0150d9510f725854300447660435d46150c0150d9510d721854300561644435c86150c015199510e701854300546654435c06150c015919110d701854300447660435d76050d0f8357460450d814343e155cd811436050c0150d9510d729814300447a6043dd56050c0d8727060450d8d420061c60570143635080d8727060450d91320061c60570143644c80151993a1070591510051664c641c1645440151994a0c7058d510050e650631c1635447f21c985916350d51005862416458d4354401a19642016350d510370c981715d06054401531912017418151006155c68319060544018557160c641815103714981715cc605440d45890591731815100554644805cc605440d838805d163181510060d5c68418c60544018357161063181510370a981745c8605440dc4a605cd721815103718981715c8605440d46890591721815
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x8c4414e30040a8878462819810d759854343ca1140ca886b94c0a1a1e218a066043595438850f20c5032a21aeca1c4087a06281855cc735901043d03140c2ae83a2c60821e418a0654435d9430410f10c5033021acaa182087a822818550c4358810
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x1
  | 7 => 0x4b
  | 8 => 0x4c
  | 9 => 0x4d
  | 10 => 0x4e
  | 11 => 0x124e
  | 12 => 0x94b
  | 13 => 0x94c
  | 14 => 0x94d
  | 15 => 0x94e
  | 16 => 0x124b
  | 17 => 0x124c
  | 18 => 0x124d
  | 19 => 0x138b
  | 20 => 0x138c
  | 21 => 0x138d
  | 22 => 0x138e
  | 23 => 0x98c
  | 24 => 0x98d
  | 25 => 0x98e
  | 26 => 0x128c
  | 27 => 0x128d
  | 28 => 0x128e
  | 29 => 0x9cb
  | 30 => 0x9cd
  | 31 => 0x9ce
  | 32 => 0x12cb
  | 33 => 0x12cd
  | 34 => 0x12ce
  | 35 => 0xa0b
  | 36 => 0xa0c
  | 37 => 0xa0e
  | 38 => 0x130b
  | 39 => 0x130c
  | 40 => 0x130e
  | 41 => 0x134b
  | 42 => 0x134c
  | 43 => 0x134d
  | 44 => 0xb0c
  | 45 => 0xb0d
  | 46 => 0xb0e
  | 47 => 0x140c
  | 48 => 0x140d
  | 49 => 0x140e
  | 50 => 0xb4b
  | 51 => 0xb4d
  | 52 => 0xb4e
  | 53 => 0x144b
  | 54 => 0x144d
  | 55 => 0x144e
  | 56 => 0xb8b
  | 57 => 0xb8c
  | 58 => 0xb8e
  | 59 => 0x148b
  | 60 => 0x148c
  | 61 => 0x148e
  | 62 => 0xbcb
  | 63 => 0xbcc
  | 64 => 0xbcd
  | 65 => 0xccd
  | 66 => 0xcce
  | 67 => 0xd0c
  | 68 => 0xd0e
  | 69 => 0xe8b
  | 70 => 0xe8e
  | 71 => 0x94056
  | 72 => 0x124956
  | 73 => 0x95256
  | 74 => 0x98956
  | 75 => 0x128956
  | 76 => 0x9c956
  | 77 => 0x12c956
  | 78 => 0xa0956
  | 79 => 0x130956
  | 80 => 0x134a
  | 81 => 0xbc953
  | 82 => 0xbc954
  | 83 => 0xbc955
  | 84 => 0x139256
  | 85 => 0x99256
  | 86 => 0x129256
  | 87 => 0x9d256
  | 88 => 0x12d256
  | 89 => 0xa1256
  | 90 => 0x131256
  | 91 => 0x99396
  | 92 => 0xbd393
  | 93 => 0xbd394
  | 94 => 0xbd395
  | 95 => 0x128996
  | 96 => 0x99296
  | 97 => 0x9c996
  | 98 => 0x12c996
  | 99 => 0x150c
  | 100 => 0xcb
  | 101 => 0xa0996
  | 102 => 0x130996
  | 103 => 0x150d
  | 104 => 0x10b
  | 105 => 0x14b
  | 106 => 0xb0996
  | 107 => 0x98b16
  | 108 => 0xb4996
  | 109 => 0x144996
  | 110 => 0xb8996
  | 111 => 0x148996
  | 112 => 0x19cb
  | 113 => 0xe8996
  | 114 => 0x168b
  | 115 => 0x180b
  | 116 => 0x9d296
  | 117 => 0x8c
  | 118 => 0x12d296
  | 119 => 0xa1296
  | 120 => 0x8d
  | 121 => 0x131296
  | 122 => 0xb5296
  | 123 => 0x145296
  | 124 => 0xb9296
  | 125 => 0x149296
  | 126 => 0xe9296
  | 127 => 0x12c9d6
  | 128 => 0x9d2d6
  | 129 => 0x10c
  | 130 => 0x14c
  | 131 => 0xb49d6
  | 132 => 0x9cb56
  | 133 => 0x19cc
  | 134 => 0x180c
  | 135 => 0xe89
  | 136 => 0xe92d6
  | 137 => 0x130a16
  | 138 => 0xa1316
  | 139 => 0x14d
  | 140 => 0xb8a16
  | 141 => 0xa0b96
  | 142 => 0x19cd
  | 143 => 0x168d
  | 144 => 0xe9316
  | 145 => 0x14a
  | 146 => 0xb4b16
  | 147 => 0x144b16
  | 148 => 0x24b
  | 149 => 0xb8b16
  | 150 => 0x148b16
  | 151 => 0x28b
  | 152 => 0xccb16
  | 153 => 0xd0b16
  | 154 => 0x16cb
  | 155 => 0x184b
  | 156 => 0xb5416
  | 157 => 0x20c
  | 158 => 0xb9416
  | 159 => 0x20d
  | 160 => 0xccb56
  | 161 => 0x154c
  | 162 => 0xe8b56
  | 163 => 0x184c
  | 164 => 0xd0b96
  | 165 => 0x154d
  | 166 => 0xe8b96
  | 167 => 0x16cd
  | 168 => 0x154e
  | 169 => 0x16ce
  | 170 => 0x184e
  | 171 => 0xe8cd6
  | 172 => 0x18cb
  | 173 => 0x178b
  | 174 => 0x188c
  | 175 => 0x160c
  | 176 => 0xe8d16
  | 177 => 0x170d
  | 178 => 0x15cd
  | 179 => 0xcd
  | 180 => 0x28c
  | 181 => 0x4996
  | 182 => 0x5696
  | 183 => 0x5816
  | 184 => 0x95396
  | 185 => 0x138956
  | 186 => 0x94bd3
  | 187 => 0x94bd4
  | 188 => 0x94bd5
  | 189 => 0x15394
  | 190 => 0x15395
  | 191 => 0x95296
  | 192 => 0x952d6
  | 193 => 0x95316
  | 194 => 0x20e
  | 195 => 0x24e
  | 196 => 0x28e
  | 197 => 0x139296
  | 198 => 0x1380d6
  | 199 => 0x138116
  | 200 => 0x98154
  | 201 => 0x98155
  | 202 => 0xb4b099e
  | 203 => 0x144b099e
  | 204 => 0xb8b099e
  | 205 => 0x148b099e
  | 206 => 0x99556
  | 207 => 0x14994
  | 208 => 0x14995
  | 209 => 0x98056
  | 210 => 0x992d6
  | 211 => 0x980d6
  | 212 => 0x99316
  | 213 => 0x98116
  | 214 => 0x9d6d6
  | 215 => 0x9c116
  | 216 => 0xa1856
  | 217 => 0xa00d6
  | 218 => 0x138bd3
  | 219 => 0xccb4b1e
  | 220 => 0xd0b8b1e
  | 221 => 0x140b56
  | 222 => 0x140b96
  | 223 => 0x138bd4
  | 224 => 0x138bd5
  | 225 => 0x3ce
  | 226 => 0x15ce
  | 227 => 0x170e
  | 228 => 0x40e
  | 229 => 0x160e
  | 230 => 0x188e
  | 231 => 0x58e
  | 232 => 0x1789
  | 233 => 0x178e
  | 234 => 0x18c9
  | 235 => 0x18ce
  | 236 => 0x5256
  | 237 => 0x4956
  | 238 => 0x155416
  | 239 => 0xe96d6
  | 240 => 0xe9856
  | 241 => 0x16d456
  | 242 => 0x185496
  | 243 => 0x154996
  | 244 => 0xe8596
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1904
  | 6 => 6160
  | 5 => 2684
  | 4 => 272
  | 3 => 9
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (78056+((h/634+packedAt gbK7 (70448+(h % 634)*12) 12) % 2285)*12) 12
  | 6 => packedAt gbK6 (322369+((h/2053+packedAt gbK6 (295680+(h % 2053)*13) 13) % 8132)*14) 14
  | 5 => packedAt gbK5 (169084+((h/894+packedAt gbK5 (158356+(h % 894)*12) 12) % 3543)*13) 13
  | 4 => packedAt gbK4 (19850+((h/90+packedAt gbK4 (19040+(h % 90)*9) 9) % 327)*10) 10
  | 3 => packedAt gbK3 (741+((h/3+packedAt gbK3 (729+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc3f8fffde1c3f1c0e0c7038387c8619f3e4c93
  | 1 => 0xfc3f1c0201fc3e00fff803ffffd186644070ff
  | 2 => 0x3fe003fe003fff00fffc03f8261878878f1c
  | 3 => 0xffc00003ffffc00000fffffc00381f80f80fe0
  | 4 => 0x3ffffffffff000000003fe000fff000
  | 5 => 0xfffffffc0000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x40482438e0c0704622c11888938020891e4c91
  | 1 => 0x84110840000402004808012124008224001026
  | 2 => 0x2a4088220014920052480250820858028518
  | 3 => 0x6a800113556a800804a4b25801381580e80ac0
  | 4 => 0x2200022399b3292c96002010023d6000f56000
  | 5 => 0xb33493c0102200301800c060643fdf76000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeeafefcfcc8fefefeeafefcfcc8fefefeeafefcfcc8fefefeeafefcfcc8fefefeeafefcfcc8fefefeeafefcfcc8fefefeeafefcfcc8fefefeeafefcfcc8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36410
namespace PEqualNP.Outside.L_meta_36410
open PEqualNP.Outside.L_meta_36410.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 1 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 5 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 2 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 92 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 5 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 91 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
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
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 91 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 2 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 30 := bs5_3_0
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
theorem bs5_4_448 : Interval s5Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_512 : Interval s5Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_544 : Interval s5Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_608 : Interval s5Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_640 : Interval s5Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_704 : Interval s5Atlas 4 704 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 712 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 (concat bs5_4_192 bs5_4_224)) (concat bs5_4_256 (concat bs5_4_288 bs5_4_320)))) (concat (concat (concat bs5_4_352 (concat bs5_4_384 bs5_4_416)) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512))) (concat (concat bs5_4_544 (concat bs5_4_576 bs5_4_608)) (concat bs5_4_640 (concat bs5_4_672 bs5_4_704)))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_640 : Interval s5Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_704 : Interval s5Atlas 5 704 31 := block_range (n:=31) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 735 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 (concat bs5_5_192 bs5_5_224)) (concat bs5_5_256 (concat bs5_5_288 bs5_5_320)))) (concat (concat (concat bs5_5_352 (concat bs5_5_384 bs5_5_416)) (concat bs5_5_448 (concat bs5_5_480 bs5_5_512))) (concat (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)) (concat bs5_5_640 (concat bs5_5_672 bs5_5_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 42 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 9 := bgb_3_0
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
theorem bgb_4_256 : Interval gbAtlas 4 256 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 272 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256))))
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
theorem bgb_5_2656 : Interval gbAtlas 5 2656 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2684 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)))) (concat (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)))))) (concat (concat (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))) (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))))) (concat (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)))) (concat (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464))) (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)))))))
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
theorem bgb_6_4480 : Interval gbAtlas 6 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4544 : Interval gbAtlas 6 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4576 : Interval gbAtlas 6 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4640 : Interval gbAtlas 6 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4672 : Interval gbAtlas 6 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4736 : Interval gbAtlas 6 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4768 : Interval gbAtlas 6 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4832 : Interval gbAtlas 6 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4864 : Interval gbAtlas 6 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4928 : Interval gbAtlas 6 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4960 : Interval gbAtlas 6 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5024 : Interval gbAtlas 6 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5056 : Interval gbAtlas 6 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5120 : Interval gbAtlas 6 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5152 : Interval gbAtlas 6 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5216 : Interval gbAtlas 6 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5248 : Interval gbAtlas 6 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5312 : Interval gbAtlas 6 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5344 : Interval gbAtlas 6 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5408 : Interval gbAtlas 6 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5440 : Interval gbAtlas 6 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5504 : Interval gbAtlas 6 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5536 : Interval gbAtlas 6 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5600 : Interval gbAtlas 6 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5632 : Interval gbAtlas 6 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5696 : Interval gbAtlas 6 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5728 : Interval gbAtlas 6 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5792 : Interval gbAtlas 6 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5824 : Interval gbAtlas 6 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5888 : Interval gbAtlas 6 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5920 : Interval gbAtlas 6 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5984 : Interval gbAtlas 6 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6016 : Interval gbAtlas 6 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6080 : Interval gbAtlas 6 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6112 : Interval gbAtlas 6 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6160 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))))) (concat (concat (concat (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928))) (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))) (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504)))))) (concat (concat (concat (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696))) (concat (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792)) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)))) (concat (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))) (concat (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)) (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272))))) (concat (concat (concat (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)) (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464))) (concat (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)))) (concat (concat (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848))) (concat (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944)) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040))))))) (concat (concat (concat (concat (concat (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136)) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232))) (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)))) (concat (concat (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616))) (concat (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712)) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808))))) (concat (concat (concat (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)) (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000))) (concat (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)))) (concat (concat (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288)) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384))) (concat (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480)) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576)))))) (concat (concat (concat (concat (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672)) (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768))) (concat (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)) (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960)))) (concat (concat (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056)) (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152))) (concat (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)) (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344))))) (concat (concat (concat (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)) (concat bgb_6_5472 (concat bgb_6_5504 bgb_6_5536))) (concat (concat bgb_6_5568 (concat bgb_6_5600 bgb_6_5632)) (concat bgb_6_5664 (concat bgb_6_5696 bgb_6_5728)))) (concat (concat (concat bgb_6_5760 (concat bgb_6_5792 bgb_6_5824)) (concat bgb_6_5856 (concat bgb_6_5888 bgb_6_5920))) (concat (concat bgb_6_5952 (concat bgb_6_5984 bgb_6_6016)) (concat (concat bgb_6_6048 bgb_6_6080) (concat bgb_6_6112 bgb_6_6144))))))))
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
theorem bgb_7_1664 : Interval gbAtlas 7 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1696 : Interval gbAtlas 7 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1760 : Interval gbAtlas 7 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1792 : Interval gbAtlas 7 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1856 : Interval gbAtlas 7 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1888 : Interval gbAtlas 7 1888 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1904 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat (concat bgb_7_224 bgb_7_256) (concat bgb_7_288 bgb_7_320)) (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 bgb_7_448)))) (concat (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672))) (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800)) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928))))) (concat (concat (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152))) (concat (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280)) (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)))) (concat (concat (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632))) (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760)) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 bgb_7_1888))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeafefcfcc8fefefeeafefcfcc8fefefeeafefcfcc8fefefeeafefcfcc8fefefeeafefcfcc8fefefeeafefcfcc8fefefeeafefcfcc8fefefeeafefcfcc8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124266 * 2 ^ 32 + 4277992648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36410.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.or,[1,2]⟩,⟨.and,[4,7]⟩,⟨.and,[0,5]⟩,⟨.and,[0,4]⟩,⟨.or,[7,10]⟩,⟨.or,[1,9]⟩,⟨.and,[6,12]⟩,⟨.or,[3,8]⟩,⟨.and,[11,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277992648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277992648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36410

open PEqualNP.Outside.L_meta_36410 in
theorem PEqualNP.Outside.L_meta_36410 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277992648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277992648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
