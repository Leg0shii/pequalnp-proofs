import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36404.Model
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


end PEqualNP.Outside.L_meta_36404.Model

namespace PEqualNP.Outside.L_meta_36404
open PEqualNP.Outside.L_meta_36404.Model
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

end PEqualNP.Outside.L_meta_36404

namespace PEqualNP.Outside.L_meta_36404
open PEqualNP.Outside.L_meta_36404.Model
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
end PEqualNP.Outside.L_meta_36404
namespace PEqualNP.Outside.L_meta_36404
open PEqualNP.Outside.L_meta_36404.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x51201221586539a2048e003600000520ca021e78b8c2a9558e3a0000a40000003e8c0041a18b08541cc0b4c0512826b48a20c100b1c00d1105182080ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x435711000a222f000054005b006f000200133a53041564450b5d011b2c0e2d69302003215a12554e703660005f28663200402b720026246b1f374d50083c6700140c481800636d07561a474b0d42651d580000192335003e005e006871743b000025444f415110610005000f4c4a167359493f465200622931003906343d38171c6a33271e002a6c096e2e5c001e86009504808c0f008180018000020580000088868515000d8000828e000581848207800200056750c43b7290876d5210e7aa9215794e42aea9c85775150ae8a2a16bd4942dba8a85b45150a7ca8215794c42aea98859f42ccb3a85994f952329eaa4655d538cb5a85196b50932bba8a6574514cb9ea49967d0932e7212659d424cb9a84996350932eba8a65d4514ca7ca8194f55032af298655e53d06baa7a0db94b41b6a96833e54cc67aa998db94b31b6a96633e54c867aa990d794f21aea9e43ad428879a6510cf950219eaa0435e53086baa610eb50821e6990437a50086f2a010dd94640baa8c815f53502b8a6a05794c40aea98816e52102daa4205d94440baa888176518c2eaa3184fd51309e2a2613e540c27aa8185b94830b6a906176510c2eaa2184f953209eaa6415e53c82baa7906b50b20e6996417651882eaa3106b50920e6992413e540827aa8105794c20aea98417651082eaa2106dd0b10daa1621d732c43aa65885d546109faa2213c54442bea6885714d10b7a92216c524436ea8886d15110eba9a21d453443cea4887914910dba1221b542443ae6488754c910f9a8221f220443e240885d94410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1a0066002901000a2008b9ea0080001c48050c5ac9aa3a40116032800c350d5210f254214532a3592424cac46150932e1d85424cb846150932e150b514cb854214532c354d420870d544c821ca5095008749325402193588535022d6215130c354d42c830d544cb20e150932c43245414910d114c52442346550910951953244385424c910e850920443c13248110
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x6420a0cebb0a84994877650b514ca823aa849922181195424c910
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (826+((h/15+packedAt s1K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s1K4 (3471+((h/39+packedAt s1K4 (3159+(h % 39)*8) 8) % 141)*8) 8
  | 3 => packedAt s1K3 (952+((h/8+packedAt s1K3 (912+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s1K2 (199+((h/1+packedAt s1K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x83ffff07fffe1f07f0fe1fffc3fff81e89f3f3
  | 2 => 0xfc1e1ff83c3fe1f8ff0fe1c1fc383fe176cd9c
  | 3 => 0xffe01fffc03fffff000ffe01ffc03fff870e1f
  | 4 => 0x1fffffc001fffff00001ffffc001f80fe0
  | 5 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x884001108000200010120244404888440050b1
  | 2 => 0x19442231905402287106208cc41192c432c594
  | 3 => 0x208954420aa91153088954112a822519850a0a
  | 4 => 0x729598852a0d559daaa11021b3270189d80f40
  | 5 => 0x431910e6333199e6cccd993822040611efa000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36404
namespace PEqualNP.Outside.L_meta_36404
open PEqualNP.Outside.L_meta_36404.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x141000022a50032ce400d819c00bf43bd43bf42bd42df32ee32dd32ed32cd32bf41bd41be40bc40
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x882bd6950006008016b8071b00180a1a6a9c658f424cb1a849963d0d32c6a1a658e544cb1aa8994754f4196a96838d32d071a64a0e34ca408ea98812d521031a64204d54440
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x4c10a1586544ca0d654cb418359532103053254440
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
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
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (228+((h/4+packedAt s2K4 (208+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s2K3 (457+((h/5+packedAt s2K3 (432+(h % 5)*5) 5) % 20)*5) 5
  | 2 => packedAt s2K2 (155+((h/1+packedAt s2K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7fc7fff87f0ff0ff0f87e1ffe1fc3f0fa4f4cf
  | 1 => 0x87f870ff8ff0ff0ff1f87e1c3e1fc7f1db4b33
  | 3 => 0x7ff80fff000fff1fe007fe03fe007fe638c3c
  | 4 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 5 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x400008001001000000802400240100001045
  | 1 => 0x20820111040140102088220882090241094112
  | 3 => 0x55112aa222aaa88356445541354094ac628c28
  | 4 => 0x14354cc44a882aa59b5511023992b024740e80
  | 5 => 0x662668876cccccc9ede67993910320c97fe000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeeeee88eeeeeeaaeeeeee88eeeeeeaaeeeeee88eeeeeeaaeeeeee88eeeeeeaaeeeeee88eeeeeeaaeeeeee88eeeeeeaaeeeeee88eeeeeeaaeeeeee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36404
namespace PEqualNP.Outside.L_meta_36404
open PEqualNP.Outside.L_meta_36404.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x15a51a440001000aa800302190c800260024503242cd210000f23524c7813000000007c38000500222c9cb9b00715003a0870048008050000004040300b103100043ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x613e540c2faa8186f550309eaa0617c540c2fca6185f94830f7290616e520c2faa4187b54830b6a90617e510c3eca2185d94430bea8861f5510c2eaa2186fd0430dea08617e500c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c83de85907b90b20f6a1641ec42c83de65907b8cb20f699641ec32c82fca3905f54720dfa0e41bd41c83de43907b88720f690e41ec21c83dea9907b95320f6aa641ec54c83dea7907b94f20f6a9e41ec53c83de87907b90f20f6a1e41ec43c83dea3907b94720f6a8e41ec51c83de83906bd0720f720e41ed41c835a83907b10720f798e41ee31c83da63907b0c720f7a0641ee40c83da81907b10320f798641ee30c83da61907b0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94416d52882fca3105f54620dfa0c41bd41882fca1107bc8220fd904417f544837ea8904fd5120bf2a2417d54482f8a8906f151209e2a2417f53482fca6905f54d20be29a41ef42483dc84907b50920f621241ef32483dc64907b4c920f6192417f51482f8a2906fd0520dea0a41ef21483dc42907b48520f610a41fb20483dc40907bd5120d7aa241ee54483daa8907b15120d62a241ef53483dca6907b54d20f629a41ef43483dc86907b50d20f621a41ef51483dca2907b54520f628a41ef414835e82907b90520f6a0a41ad41483d882907bcc520f718a41ed31483d862907bd4120f5a8241ef40483dc80907b50120f620241ef30483dc60907b4c120f6182417f54082fca8105f55020be2a0417f53082fca6105f54c20be298417e52082dca4105f94420bea8841bf410837a82105f94020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21f641c437a83887d50710daa0e21f631c43ea63887bc8310f6906217f54842fca9085f55210be2a4217f53842fca7085f54e10be29c217f52842fca5087b94a10b7294217d52843daa5085b54a10be294217d518437e83086f50610bf28421fa30843f261087bc8210fd10421ed20843f241087a48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c524437e82887d90510dea0a21f5414436a82887d8c510fa98a21fa30443f260887bc8110fd10221ed20443f240887a48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2086fd0410dea08217e50043de40087b48010fb88021fa10043ea20087e44010
  | 1 => 0xe541067ca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31ef99663dd32cc77e8398ef50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31bea94637e518c77e8318ef50631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa9263ef524c6dea498df14931f6292636c524c7be6498f74c931dfa0a63bd414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831f7290636e520c6faa418fb54831b6a90637e510c77e8218ef50431ef98863f6310c7ba6218fd4c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87dc6590fb4cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53886faa710df14e21bea9443ef42887d88510fbcca21f6194437e518877e8310ef50621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f719243ed324877e8290ef50521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043ef42087d88410fbcc821f6190437e510877e8210ef50421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40dfa1e81bd43d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c52502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2206fd0440dea08817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3bc87987750f30bf296617d52cc2fca3985f54730dfa0e61bd41cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c617e528c3dca5185b94a30bea9461ed528c2daa5185f94630bea8c61bf418c37a83185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c2fea2985f14530dfa0a61bd414c3be6298774c530fd98261de304c2fea8185f95030df2a
  | 2 => 0x380100a034050060160040100100000c0480100000c018000020000600002c04400000000000050010080080a8030020180800002802c0b00d00c02404003004048038060020040200000206001006000004000000080000100100000403809004018000030000280001500800000016000000010020040480000301c01000803000010000000000000180200003403000020000000020020080000000a004018050100180380100a0000000801e024020000020000980000000002005006000010030000800080000c0000180e000000028010020080000000a06c050010020000500400e008018000060080080100a0000000000200c030000120300180100001c0080c02c010018090040200200201c000070000000000200600001800002000038008090020180100300200c0200cbf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521fb94a43b7294877d5290fdaa521db54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885bf4310b7a86215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbde85197b10a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde84997b10932f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef94341dea8683bc50d06faa920cf55241bf29c837d53906fca520df54a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0efd0d41df21a83bd435077886a0dfd4941f7a92836f52506f8a4a0fb14941b629283bf425077c84a0ef50941de21283f7415077c82a0dfd4141be28283bf535077ca6a0ef54d41de29a83bf525075ea4a0ef94941dea9283bc5250758a4a0efcc941df19283bd325077864a0efd4541dba8a83bf505077ca0a0ef54141de282837
  | 3 => 0x9fc62800000086442840920c91549000024a000000000003b40005685d0002a4000005bc64c002e91f6a68ee80021044c4299957a3043ea0d0002d8962751fc114002b83cc478000005b80014680f63c000002fd000000000000007d00024336814c4b8ed1889780013a0ca00142000260001288000780d4ad1cb1100942d099000000000002b85cc002622a2020001c8540000000000000009900000030800000000001819350009557c1795ee7e0b314b2b00000019e354600000ca02e000520003e03981da1253a4194d8000586b93c000278b48d787500002c001a01b8818000000007e4a40001a80000023e1569244804e1fa9047c0601a6824881ed202400a5000374454791bf346608d332c1b04b5918a1084c256d9464dc135958f12d63841a02f3ea1acee0c555285cf610c5d874d3e00000006915858000cc9558333220f80000027e29cb29d448800012155042914d100044ca4d7aae05f29a0002a7022801290db000274002b0000000d985417e88847000000000000824ec0002d8004046ac00000000000002294ee000001763380008b000000000002f2000000002c5000c4400000510001088000000010a86e5ae6ed5b15e0000fc000000009998500008e000ca2e32727bd3ea854460004f28a0983485c8050547d8528af6385f0e800032c00557800000000db98c19c7dc4186a3fa628003134500dc000744daab40009a0dac04001715505c8000005e8b040000000056d7f8ae4e4000191de51e00173800000000000000000001ead9000000000a632aca89116900000000000466000b08935f695d5297d070000288de2341049b17a578c640016d4b2cc47d0e701444928219000510a107116e2b0ff2dd29e001261e710e62d741a70181415918465a67d1ba131e6b1d6413e2686617824d21a1e4821884348949898d1625a0000ef4f6a891603a1640000000053e81578a923c6c3527b0213e5fc462560008c4b6031150c54380bd2048d0000000007c4c2800000000000005c400000283138550ea9d11a2a50c7884000bcd5f000000000000e40001791388f5328e8243085f4b902a8690000011e000334000518e22d4001890002f013c0000000080d0600043c000000000003ad2c0403ac97d5203000000000177586bd8011cf000000000000000000000046a000a681b61e000091a461c184000001ea2000029762eb10773261be04c948fc0c8000941ad23e45185abf362b313a000436010d91674fe000002b337c5d11528b2f61bd688cf45c6d9508e80009ad929a13e4000002071d299c8c8005941a06d2900720b4231cc63a6e1881c700c00200000805004008000030000040180202e00c0000500c0000200100000401000000018088000060040280800005c038110000180080300a0180580d006020008000040040
  | 4 => 0xaece680041442c00000286c14000000000000a800254000000000000000000000099000000000b7cf0800000860000004e200130acf1ac0004088926e000a928e03cb3400094000000e0afc00000158aae3845d42b8e0000000141a900612800280266501300003244f4000000002800000000000000000020000001d900035c7fa3847aa8cf5a6524c2d4ec0e50f42f95cb182121c8f50006400ac8da462beb09920594483541387c3c455cf9873166558819c30006757f0000ac638fd1e40000015b90a5020014f000558c00000002c4880aeb21000000003295b45c0489860003400006c000000248003029e529800000000002c020e001648005a6234000983200012a2e541e4800c9ac6500010b00000054014a3000000000000000b180000003a001020cc18e4943c00056a8c8631410009f80000043a49cd2b33000000000631440000e25b01c0008c08a3be000000003dc0000a28645e7801b00028e75d0080036a198001bc0008207526a00000148b2f360738ac82e5b0850002ce0009bc761c52c8254a994525c374e209663ec30dca5d65c01d05a985da00170960178000e484b0008d800062000728de80029c48568000350000002ba000000102eb00000000000000000000000eec9d1d8c000045c00295000a1c0f816636000000f00000009d90519a0000000000000000000000000ed800000718000c8116000130003361f89187b0000018b0f621c52411a1f5128fc7a1d21b28e5270f916092088aef660a582f91c13665c3b1380a42483f8ba3d0111168005aa018958220004bc8e94c5a80014101864458d8d00016832d3d1ff4d2839258c35ac000f2a6c0009cc000bb000bb8fda47568908f49835185f965a7060e19cc496e4b861d553065385bc0004354c87071ae60b8024003044b400000000170000000f7000001751c001a000000004c600087
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xb530823e6414c208f590530826e6214c209d98453082756114c208f992510823d6494420cb94b410832e5250420cd945410833551504209bd95200827b6548020da949200833661953109bd8954c426c6255310cbd8954c432c62553108f99353c423d64d4f109bd8953c426c6254f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b108f99052c423d6414b109798c52c425d6314b10cd95141c42b76550710cdd9541c43a76250710e918941c42b5648c710cb95320c432d54c8310e950720c432e5448310cb55120c43a541483109b98b548426d62d52109798c548425d63152109b988548426d62152109b98b538426d62d4e108fd91538423c6454e108f990538423d6414e109b988538426d6214e10da982528423f6454a108f191528432f6454a10cb191528432e52d0610cb54b418432e5250610cb54941842e9628c210da94920842eb6548210dad9520843ab6448210ea19120843ab4148210ea505208425f63551109718d544426f62551109b189544423f6454d108f191534426f6254d109b189534423e6414d108f590534426e6214d109b588534423f64549108f191524425f63549109718d52442b564905109d19541443376550510cd19541443a76250510e918941443b36050510ec18141442b5648c5109d19531442e9628c110ec5063044278654c110ec50530443d1314c110e950720442e96288110ec50620443a541481109e19520443b14148110dad9520443686548110ead9120443a86448110f8d8520443e06148110ead0520443e24148110ea50520443e14148110e850520443e23148110f84c520443b141c4110f8482104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c109d984530427a6014c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520426f60548109b581520423e64148108f590520425e63148109758c520426e62148109e980520423e64944108f592510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410433651504109b98a500426d62940109b597200432e54c8010cb553200434e53c8010d354f200426f6548010cb951200432d5448010d394d200434d5348010da941200433554c4010d554f10042796584010d654e100436952840109dd9510043355444010d554d100427b6544010d654d10043695244010
  | 1 => 0xc31d544c030d5545300c27b654c030dc545300c25e63d53209758f54c823e64d4f208f59353c823e6494f208f59253c82ae64ccb20ab59332c834d530cb208f99251c823d6494720ab99221c82ad6488720ab99021c82ad6408720b398c21c82cd6308720b398f54c82cd63d5320ba58354c82e96015320ab99353c82ad64d4f20ba58353c82ae6494f20ab59253c834d5314f20ba58053c826e6590f209b59643c82e960d4720ab99251c82ad6494720ab99051c82ad6414720b398c51c82cd6314720ba58051c826f65507209b19541c832f6550720cb19541c83a76150720ab99231c82ad648c7209bd9531c826c654c7209b99431c826d650c720ab99031c82ad640c720ba98031c82e9600c720b398c40c82cd6310320b998440c82e56110320abd9130c82ac644c320ab99030c82ad640c320b998430c82e5610c3209798c548825d63152209d984548827561152208f990538823d6414e209d98453882756114e208f992518823d6494620cd94541883355150620cb58b544823d61d51208f992544823e6515120cb588544823d61151208f992534823d6494d208fd91534823c6454d209dd8553482746154d209b997424832c54909209b195424832f54109209b99732482ae64cc920ab593324832c548c9209b195324832c544c920d314d324823e64145208f590514825e63145209758c514823e65d05208f197414823e65505208f19541482ae6488520ab592214832c5488520ba98221482ae6408520ab590214832c5408520b398c21482cd6308520ba98021482ad61d5120ab99254482e96095120bad8154482ae6515120cb99454482ad6115120cb15353482ae6494d20ab59253482e96094d20abd9153482ac6454d20cb15153482e76154d20b918553482eb6054d20d354c534826e6590d209b59643482eb6050d20ba18143482ea6010d20ba58043482ae6494520ab592514832c5494520ba58251482af6454520ab19151482cf6354520b318d51482eb6054520ab99051482ad6414520cb15051482ce6314520b358c51482ae65d0520ab19741482ad6490520ba98241482e960905209bd95414826c6550520cbd9541482ae6550520ab195414832c65505208b19541483a76150520ab99041482ea6010520ba58041482ae648c520ab59231482ea608c520ba582314826f654c5209b195314826e650c5209b59431482ae640c520ab59031482ea600c520ba580314832f54d4120cb15350483ab54d4120ea15350482e961d4120ead0750483a941d41209b996404826e6510120b398c40482cd6310120b998440482e56110120ea500404826e658c120abd9130482ac644c1209b99430482ae640c120ab59030482e6610c120b958430483c9300c1209b98b540825e63150209758c540826e62150209d984540827561150209b98
  | 2 => 0x60d50219e583540863d6595021cb189540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530874c6254c218f990530863d6414c219798c530866e6214c219e98053086796014c21cb553420874d53d08219b594420874d5310821b9584420866d65cc821ab993320874d53cc8219b594320874d530c8218f992510863d64944218f597410871e53d0421c754f410863f6550421c794d410871d5350421d354f210866f6548421d354d21087a541484219dd95210873a5494021ce552500875a5394021d654e500873b4194021ce506500873a5454021ce551500875a5354021d654d500876a6254021dad0950087684254021dacc950087683254021ced0550087394154021dac85500876921540219b98a53d026d6294f409bd8951d026c6254740cd54741d02ae6290e40cb548429032e52d0640cb54b41902ac6250640cb949419032d5250640cd945419033551506408f997435033751505408f596431031d5390c40ab98a431031d5310c40d394e521034d5394840d394d521034d5354840c754e421032d5290840c754c42102b96010840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cd99151103364354440cd10d51103364254440cd109511031e53d0440c754f411032e52d0440cb54b411033551d0440c794d411031d5350440ab189411032e5250440cb54941103365150440c754f401033551d00408fd95401031d5350040cd545401027b65500409b98b54cc26d62d53308f99251cc23d64947309bd8951cc26c62547309b98b548c26d62d52309b988548c26d62152309d984548c27561152308fd91528c23c6454a30cbd91528c32c6454a308f992518c23d6494630cb94b418c32d52d0630cb949418c32d5250630cd945418c33551506309b98b544c26d62d5130cb98b544c32d62d51308f587544c23e64951308f994544c31d63151308f584544c31c5490d3097195434c2d86050d308f990514c23d64145309b988514c26d62145308f997414c23c65d05308f995414c23c65505309b98b540c26d62d50309d987540c27561d50308f596540c23d61950308fd85540c23e64150309798c540c26e62150309b588540c27661150309d584540c32e5494830cb552520c32e5454830cb551520c23e64944308f592510c3365494430cd552510c3665294430d954a510c3366494430cd592510c3365454430cd551510c3665254430d9549510c3366454430cd591510c23f65d04308f597410c32e52d0430cb54b410c33651d0430cd547410c23f65504308f595410c32e5250430cb549410c3365150430cd545410c31d54cc030d5547300c371518c03097d95300
  | 3 => 0x1329b997424cace63d0932ab993324ca3e64145328f590514ca7a60145329e580514ca6e62d50329d984540ca7561150329e980540ca7960150328f992530ca3d6494c3297d95320ca6f654c8328f992510ca3d64944328fd91500ca3c64540329b98a53d066d6294f41ab98a43d06ad6290f41c754c43d066e62943419b58a50d06ae62d4f41ab58b53d06b561d4f41ab98a53d06ad6294f41c754c53d06b56114f41a798f52d069d63d4b41ad58752d06b56114b418f99732d063d65ccb41ab98a50d06ad6294341a798c50d069d6314341ab98850d06ad62143419b98a509066d6294241ab98a43506ad6290d41c714d435066d60d4941cbd0c525072d43149419b580525072c52d0941cbd48425065e63141419758c505066e62141419b58850506ae6294d41ab58a53506b56194d41abd8953506ac6254d41add8553506bb6054d41ae181535071d5314d41ab58352506ae6294941ad58652506b76154941ab994525072e6514941cbd4c525072d5314941ab580525063e65cc9418f59732506b7614c941ad18532506b6610c941ad584325072f52d4541cb14b51507a752d4541e914b51506b560d4541ab98a50506ad6294141cb14a505069f6354141a718d50506af6254141ab189505069e6314141a758c50506ae6214141ab588505072c52141418fd9541106776550441cd951411066e62940419b58a501066e62d53319b58b54cc66e62943319b58a50cc63f64543318f19150cc66f62552319b189548c72f6255231cb189548c66e62942319b58a508c66e62951319b58a544c66f62551319b189544c67b60551319e181544c63e64d49318f593524c72e64d4931cb593524c66d60d49319b580524c74c52cc931b5185324c72f52d0531cb14b414c72f5250531cb149414c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f990540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c66d6094831cb951520c72d54548319bd81520c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc43197d95310c74d524c431e5505310c677654c4319b98a500c66d6294031ce952500c7395494031da94a500c7695294031da98a500c7696294031ced06500c7394194031ce951500c7395454031da949500c7695254031da989500c7696254031ced05500c7394154031d6cc5500c7723154031d64c5500c77131540318f99253c863d6494f218fd9150c863c6454321cbd89548863e64d4e218f593538863e6414e218f590538867a6014e219e580538872d5410a21ab993328865e63951219758e544866f62551218f992534863d6494d219bd89534866e658c9219b195324865e63d50219758f540867a
  | 4 => 0x91ae90003e0790273bc4cc6fb4a2e4720cd9fd364868a49c43b4000fe3250d8b850b97a54a1002c00017cd158c2c955cbd42d9ae2166a14286b3b2001ae8000002046c0940b236c113220601280017e6aa385941e62083305d1f428cd78f419d446a6d101681d287cee87f0bed859a8b05ec475898e636a449609e452a230698185dec04a60000144841415867008480a7d5f026d532f06042a8e112d000001969824e4830000005320013db100004f4001740a2338002280ce000000a44e6001340000000000034339e0016a8000c8d888191b34200000049000be402b030260016c839494000739ef000d080499e5869c4869ee00000041987000db400079004554000e86720012d36b42aac4f81f15d072d160721f64e50883452647c9023f03c000000000000100887a63a000000f4678c6c8b3585162899f8cb096001548004024f8341281a45e168a43638ccd15270504c5400314000b4000091278000de23a330001279c91aad90000000ba7885d88b53cdec4ca7f4d6000d1800000504df8005002294d11e5563c4aca062a6071128030a0900d825f49ac9c83abf0000007f9e72c04b8531c02b4a29488824ee10d7dafe1d4cc51e376002834cc9d467a6315e10e306570038c916e7809800501403a114000140000000000500204000000018068000000360d00300101800c0200100800c0200101400405008008008000000000100280101a04000002036010020000060280180700000c008110021c4080040100180181900e00c0600109a004018010000000501e0000180700000c00c0400000c01c0280a00c01c000010001380480b0ba000038010000180081000400c088060180000180802e03803000038000020050220100580b0000080780102600001800008020130180020000c80803e080038010100380200002000c0080101c02c0000100400c038010240040482c006000000080060000300000200800009002000058570000000000200200807801000000010070040080c02500c000000060000000480c00000c00826002064040000000b800001000010098120120080f8000100080581f04000c0180601000800003004008008170120180080300805c0000001202416801004044018000000080001a0060280080306a0080401107c0c803002002004000070000180480a000008000010040141801200c00c0f806000010040089b98a50d0e6d6294343cbd0e5290e6d6094a439bd815290e6e62942439b58a5090eae6290d439b9885050e6d62141439d9845050e7561141438fd954310e5f6550c439bd895110e6c62544439b98a5010e6d6294043c794d4390a3f65508429bd954210a3d61953328fd8554cca3e64947328f59251cca7a60d52329e583548caae64cca328f992518ca3d64946329d986544ca756195
  | 5 => 0x17e0524f463c9490524868876b3b1fa988642be0c60000000003e5ac071883746d8471fe00000184a8c4060949fb0d38657951800000bb18d0a0000000f92b45e24d80031102cc5c9b8450320010c29664ca51370e3506b80572590e66ac7c94359835d3b07c05e030991d34c8001be10f1241a4382f25ba4701c1a95fa0d86f06055e3f9a984c3fe0007b9186827140017531a8845e1e96ee810001b96c6c389285a000001a81062f8a490736900000000000000bac0b82d000c780007d0009715c2f30c2364a696229e4086017d35494c79a4211e9556736554e464a59713f23b15c88643c8cc4c26c39c000a81e153867d6226d45aa386286f47c1791cb46058a845c000554d5800312308048c91ea0f096cda12c150bfc0d0000001200015b24cd503db6013c001afa97000b19a434e1e06f5172a2000cb8002650668484e1a422e00000080000585ba000000000aa20f1520002e16f00058d6500051e000001342d480893a13642625982470ae000002b302008c00000584d6400000062000001d550c8c80e80018e544000004c22ad9a00035e001722b01ac188231b31423ac468000001b4482a46985083f32f0008580024e4c0001829906e45911325849891171aa8000000bf9086320016e00000055dba8006885748d0004c6670cb0005b00003500007cb1c619130e84ac05b5c590cb09a9095f41090801534c000000b1680af50513a4a0d693a00050e920001eb32e66842800280000000000008152f00d38e0219188859ada134ae66f2394e902b60eb4d5018e468001330d1370a05a880000ccc8979cc3ac81cc527830c538bbb6600086c5c800432001858006a45b4711f348cde0ca00000000167a416485102a82e4f8b88002673260011da362e0bdd4ea8d2ec304779dc3f0440b30001880d5a5aad000b692e94809c000000002f6ca9002222189483b875322704b4ab214eb6d22b49078b9c001fb22a21c0003f13492d37b370407e8bc8955800006a0005087dc578000a800118814000d9c00229000b58801651f400117a092765b0851e33a0c1987aba000950001cd4f20f5041e543a2d10e0000000001b82a0000017700066c8f51a9db5a44e1481521ecba9b630c1f85cc4b3006d47b55b3162dc8dd6f8a516ca24cab043000c8610b218c959a683a0528515d9311ba2d4a2b4f17e2f5be8891b87d8d002607669d6f27e6e09458433e1b48e0888e03ae2b4a522b3767b07a94761414c3728838c77c771d15e872976a5709a39051b7141625d62ab7640b50c0a2768e55823a6a53e34118114166b5c4204434a890d69224ea4a9b9b7a63e59c679b730a06c4f9b1082ce9b70936de275958240001c4001d80ca00027b5b316d5c0015f19a6f9658ac4927d42b2b51941d9949ac5ca03d560000cca6
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x101f080596110d060700000b02140e0e9b079e0015a0801c8f9c12800680050480150c801d9917090c1680038002800a1b981e8400008000030f01001897a1000b921a8a8d99909a000000000014801311a00008a1939d099f8180050800385040001d000018600480833e0c00a8d2e0312a221c3571191500ca8c382a629a834a1c15314941962e030a64a0e0d631485050694b80a428283345c0614c93185ceda928298f0552505310c788a0a62a80639154d611082194ae33266410e0e6454f3208782a9a8290843585c44254021a54e9992a010f21414855008706a9cc5218812a5c26290c40c32a6b0084205267290d5110298b8084a88818354c6250440952e0312822042c76549418c268b88c0a1a610b5d85408520a4ae22a0429060c5458c21483122a0c2a9a41511c55314d209c2e230286905257115051483062a2c628a410b9d66550520858eab246290689635004048350b0a80202410b9d7644c120d12c898060906c1614c030482163b2a890621291d94148310858eca9283084a8765052084312328c4a0a21685c06250510b22e630282885a1721814144350310c0a0a21a8589418c110948eca0a40884b0765052044314328c890221685c46448110b42e830a40886a06418520442e0b98c290221685d24148110950eca0a40884e0765052044351bb28290221689d94148110b40eca0a40886a07650520442503b28290221685d23148110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x85b520004833280238185038001c03c09635c05214141a058199153cc821921819d33254021c09535c26290c40921809ca4354440c09535c06250440a05811516308520a05811516314520c20655c06250510c817318860505108a087589418c110c20655c46448110c80645cc61481108a2869d941481108a0865d23148110
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
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
  | 6 => packedAt s3K6 (788+((h/14+packedAt s3K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s3K5 (25143+((h/273+packedAt s3K5 (22140+(h % 273)*11) 11) % 1191)*11) 11
  | 4 => packedAt s3K4 (37250+((h/298+packedAt s3K4 (33972+(h % 298)*11) 11) % 1073)*11) 11
  | 3 => packedAt s3K3 (3486+((h/22+packedAt s3K3 (3332+(h % 22)*7) 7) % 90)*8) 8
  | 2 => packedAt s3K2 (925+((h/5+packedAt s3K2 (900+(h % 5)*5) 5) % 19)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x8ff87fff07f8fe3878c7e3ffe3f0fe0e09f673
  | 1 => 0xf07f878ff8ff1fff80f8fc707c7f0ffe36499f
  | 2 => 0x7ff80fff001fc7ff00ff807f800ff1c78e1c
  | 4 => 0xff80000fffffe007ffff00007ffff001f80fe0
  | 5 => 0xfffffff000000007ffffffff80000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x81090101101100400801209120902224009231
  | 1 => 0x4102012204028010048442204240488124086
  | 2 => 0x6b2313245232540ab900a90569026964c58e18
  | 4 => 0x2206544884a00494d2920008524ac041680d40
  | 5 => 0x4c446600e6c4992764e4d24e000c8189bf6000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefeeaeaeeeec8c8fefeeaeaeeeec8c8fefeeaeaeeeec8c8fefeeaeaeeeec8c8fefeeaeaeeeec8c8fefeeaeaeeeec8c8fefeeaeaeeeec8c8fefeeaeaeeeec8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36404
namespace PEqualNP.Outside.L_meta_36404
open PEqualNP.Outside.L_meta_36404.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xeab5029700364538000000000054690383800000000000098000187962f2c2c01200a8106000001400b478944682000000000005d0253e000a33064180000028000a400048200000000000004c0004200007000000080020008116080010000081ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x630a0a888223217078362a940c468339e0a40a0ea104e6525130002500204002c1401c005121058f27d240d0c249180a4fc1f1d9c87e69060006e15258009c5d0420d04133a9582e4d001790e5800000628019800701e000008c6c3a008827c3d048120300090002e33038da26000008a77000c800062a1001a00001b8ec7f089c04600298e4004f000847a0002014b43a1a800361a0c8010a86000ac303e39964d40f238b4001c21980006b2b9c45e0105880de7b2f96c203202010c010002014201010801001307000b030c020000020a0b14110400060e0511030900023e03020e0813039ea8e873e50d0e7aa921e7d4d439fa8a873c5050e7ca821de94242bca84853e54cca7aa9994f950329eaa06576510caeaa2195e94032bca80653d53d067ca1a0cf552419fa9a83b75150678a0a0cf950419f2a6633d54cc67ca918cf552319f2a2633d544c6dea498db149319f2a0633d540c6dca418db54831ea988637a500c6f2a018cf952219eaa4433e540867aa810d794c21aea98437a50086f2a010db94a40b6a94813d539035ca5206b54a409ea8c813e50902bca6205754c40b7290816d52102eca2205d54440cf298813d531033aa6204754c40d729081ad521036ca2204f54440daa888135511027ca0206e940409f2a6613d54cc33a87984fd52309e2a4616e528c2daa5184fd51309e2a2619d434c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c835ca9906b55320d7a1e41ad43c835e83906b50720d720641ac40c82daa5106e102209faa2413c544837080906bd5120d62a241af434835a86906bd0520d6a0a41eb50483d680906b90120d620241e8404835080907a8c120f4982416e520827ca9884f55310daa0e213f5484278a9085b94a10b6a9421e9208427ea8884f15110daa0a21e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x50083a62c04b9440a8d0f3ec070044001910048a8b10c4e89000002b522832442bc00c0001190009cdac304d69e321402e1a00e044a0d04020812405001cd0000058d5845050e1d63141418e181544c6696014931d1549310c7513154031c354e521030d5354840c554e51103165354440c554d51103265254440c954951102a962940408d584548c21c6550d30a358c40c82a56110320a658c40882b16110220a658c40482b16110120aa18143482a86050520aa993504822e6590120aa982404822e6510120a358c40482a56110120b258c40482e16110120aa994404832a6510120e298c40482a96310120e258c40482896310120e898440482a96110120e858440482a16110120aa19230482a8644c120e250d304821d6315210ca15120842346550510ca15120443a14148110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x601110028400380c0001001285c46050d20912e6302829068163984404834131ac220241a058d6110120942e232460904887650d3048284b98a890421481d54148110
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
  | 4 => packedAt s4K4 (4032+((h/45+packedAt s4K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s4K3 (1996+((h/16+packedAt s4K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s4K2 (453+((h/3+packedAt s4K2 (441+(h % 3)*4) 4) % 16)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1e7f8fffc1c78fc71c63f1ffe3871f8709f873
  | 1 => 0x1f87f1e3fe07f1ffe07c7e383c07e3ff36419f
  | 2 => 0xe007fe03fff801f8ff807fc03ff803f8c78e1c
  | 3 => 0xfff80003fffffe00ffff80003ffffc00f80fe0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4210a0404409100804009048a0910892009831
  | 1 => 0x84210404881202802024221104024124124086
  | 2 => 0x415220c9148125014c805482a9300a52458a18
  | 3 => 0x8004912210400129149000412449000a80540
  | 5 => 0x91644d8039a649a4fa7269270060d064ff6000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafec8fec8feeafeeafec8fec8feeafeeafec8fec8feeafeeafec8fec8feeafeeafec8fec8feeafeeafec8fec8feeafeeafec8fec8feeafeeafec8fec8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36404
namespace PEqualNP.Outside.L_meta_36404
open PEqualNP.Outside.L_meta_36404.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x40006005498c09064008f005800d267c4000468b874a009280010a2948713953601086564452316151000074c8e3c040017106004008001080ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x790a6002915960300922ca1000c8020a580041684800a18080c039c022b931017a814801b8881801d23000000011722ad202c1380129f001e00001c859a240f8d802a8011a7852da68b8706a8998a9ea50f2a110d0e23a21a899409248299219f98ab152980000e801d9b00270b06008f0000189042000c04108000c0048106018010c002891528081b7296876d52d0f5ca5a1eb54b439eaa4879f5350e7ca821d794f42aea9e857a5090af2a1214f953329eaa6659d438ca7ca8194f55032cea186576510caeaa2195e94032bca80655e53106baa620db94841b6a90837a50106f2a020cf953319eaa6639d43cc73a8698dbd4931b6292633e540c67aa818db94831b6a90637a500c6f2a018cf950219eaa0435e53086baa610de94021bca80436e52902daa5205794c40aea98816e52102daa4205d94440baa88813e54cc27aa9986750f30b7294616d528c33a86984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9906b95320d6aa641af43c835a87905b54a20d7a1a41ad43483d6a0907ad0120f420241ea30483d260905b94820b7294216d52843d241084fd51109e2a221e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x37156830940035e038124004000300184809a58252d0ea96094b43a398b5350f154354432c650d500cb0d43149319a580524c61d6395320a358e54c822d65d0f20aa99350482c96310120b85844048389434c1208758c54443285448110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x8b0912e1316a6a1e0943580524c644b9cc9a8241425cc5448110
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
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s5K4 (2694+((h/30+packedAt s5K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s5K3 (633+((h/5+packedAt s5K3 (608+(h % 5)*5) 5) % 24)*5) 5
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf3cfe3f1fc38e3e39c47c7e3e3873f18b3873
  | 1 => 0xf03f1fcfe3fc0fc7fe078f8fc3c07c7f94c19f
  | 2 => 0xffc01ff003fff007c7f80ff003ff807e670e1c
  | 3 => 0xffffe00003fffff807fff00003ffff80780fe0
  | 4 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x184428220481440404014120a091115011831
  | 1 => 0x10080400048020080000808400402020004086
  | 2 => 0x2282c886491904940ac80d209a93014d270a18
  | 3 => 0x44100128922208009515200121244a00580540
  | 4 => 0x8822912c0033492527a64a49b0060a087ea000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeefec8feeefec8feeefec8feeefec8feeefec8feeefec8feeefec8feeefec8feeefec8feeefec8feeefec8feeefec8feeefec8feeefec8feeefec8feeefec8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36404
namespace PEqualNP.Outside.L_meta_36404
open PEqualNP.Outside.L_meta_36404.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xb85042000001b08801a00001683869200a09600129e80098e908314211180001f022180149715879801998f0e0806058c0d9a9b8f8a028015011d9f931c800a870d18990000091c048b1380110c9e1d17901786120428062000801e14887001c480002800002ffd5009fe54007f55009fc5401ffd4c077f5301ff94c07fd5301df54c07fc5301ffd0c07bf4301ff90c07fd4301ef50c07fc4302ffd4801fe52007f5480bfc52027fd0801fe42007f50809fc4201ffcc807fe3201ff4c807fc3202ffd44017f51017f94401fd51005f54405fc51027fd0405fe41007f50405fc4101ffcc405fe3101ff4c405fc31007fc8405fe21007f48405fc2102ffd4003fe50007f54003fc50027fd0003fe40007f50003fc4001ffcc003fe3001ff4c003fc30007fc8001ef2000ff88001fd20007b48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xa4000fbc852005ffc429002fee2148001fe90a4000fb4852004ff8429002fec21480037fb024001ffd412000ffca090007fd5048003fe2824001ffd012000ffc8090007fd4048003fe2024001ffcc12000ffc6090007fa3048003fe982400afe4c12000ff86090007ff2048013fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffe2090007fe1048003fd0824001ff04120007deca900036f654801bf732a4000fb5952006fd8ca900036c6548001f7b22400cfb99120007dac890033ec644801bf7aa2400cfb95120007daa890033ec5448015f7b1a400afb98d20057dac69002bec6348015f7a9a400adbd4d20057dca69002bed5348015b6a9a400afb14d20057de869002baf4348015f721a400afb50d200575a869002bec4348001f7b0a400bfb98520007dac29002fec614801bf7a8a4000dbd452005fdca290003ed5148001b6a8a400bfb14520067de829002fee4148001f6a0a400bfb10520057de629002fee3148015f698a400bfb0c52000fdec090006ef6048001f5b024001fbd412000fdca090007ed5048003f62824001fbd012000fdc8090007ed4048003f62024001fbcc12000fdc6090007ea3048003f6982400afa4c12000fd86090007ef1048003f70824001fa8412000fd82090003ff65440017fb2a2008ff9951002dfcca88003fd65440017eb2a2008ff1951002df8ca88003ff64440017fb222007ff99110025fcc888003fd64440017eb222007ff19110025f8c888023ff544400fff2a22000ff5511003ff8a88801bff634400d7fb1a2006ff98d1001dfcc68801bfd634400d7eb1a2006ff18d1001df8c68801bff534400dbfa9a2006ff94d10037faa68801b7d534400dfe29a2006ffd0d100377e868801bfe434400dfea1a2006ef50d10037f88688003ff62440017fb122000ff9891004dfcc488003fd62440017eb122000ff1891004df8c488023ff5244001ff2922000ff54910047f8a48801fff4244001ff2122000ff5091003ff8848801bff324400dff1922006ff4c910037f86488006ff6144005ffa8a2002dfd4510017fca28800bf65144005fea8a2002df54510007eaa288003755144005fe28a2002ffd0510017fc828800bf64144005fea0a2000fd50510017f8828800bff3144005ff18a2002fd8c510017fa628801bf53144005fe18a2002ffc8510017fc428800bfd2144005fe10a2001bfd811000ffea088007fe5044003fea822001ff1411000ffe8088007fe4044003fd2022001ff50110007f28088007fc4044003ff9822001ff8c11000ff46088007fd304400dfc9822001ff0c11000ffe4088007ef2044003ff1022001fe8811000ffa4088007ed2044001fc9022000fa4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3ed52c8013fe2964009fb14b2004ffe8590043ef42c8013ff2164009fb90b2004ffa8590003ed42c8013fe2164009fb10b2004ffe659003fef32c8013ff1964009fb8cb2004ffa659003fed32c8013fe1964009fb0cb2004ffec390027fe61c80057f30e4009ff58720005fac390027fc61c80057e30e4011ffd4720006fea39003bfe51c8001fea8e4000df54720077f8a390043ff41c801dff20e4000ff50720077f8839003fff31c801dff18e400fff4c720077f86390027ff21c8013f790e4009ff88720077dc4390027fd21c8001f690e4009ff0872004fd84390006fd60c8003ffa864001ff9432000ffaa190007fc50c8003ffa064001ff9032000ffa8190007fc40c8003ff9864001ff8c32000ffa6190007fc30c8003ff1064001fb8832000ff44190007fc20c8003f61064001ffc432000ffc2190007fc10c8013f7b2e4011fb99720007dacb90027ec65c8013f7b264010fb99320007dac990027ec64c8023f7aa64010fb95320007daa990043ec54c8013f7b1e400ffb98f2007fdac790027ec63c801ff7a9e400fdbd4f2007fdca79003fed53c801fb6a9e400ffb14f2007fde879003faf43c801ff721e400ffb50f2007f5a879003fec43c8013f7b0e400efb98720007dac390027ec61c8023f7a8e4000dbd4720077dca390003ed51c8001b6a8e400efb14720087de839003bee41c8001f6a0e400efb1072007fde639003bee31c801ff698e400efb0c72000ddac190007ef50c8003f72864001fb5432000fd8a190007ef40c8003f72064001fb5032000fd88190007ef30c8003f71864001fb4c32000fd86190007ef10c8003f70864001fb04320007feca90002ff6548001bfb2a40009fd952006ffcca90016fe6548001feb2a4000bf5952006ff8ca90016fc6548001be32a40059f19520007fec890002ff6448019ff3224004bf99120007fac890002fd6448019fe3224004bf1912006ffea890033fe5448001feaa2400cff15120057fec69002aff6348015ff31a4003bf98d20057fac69002afd6348015fe31a4003bf18d20057fea69002b7f5348015ff29a400aff54d20056faa69002bfc5348015ffa1a400aefd0d20057fc869002bfd4348015dea1a400aff10d2000dfec490037ff524801bf7a924009ff94920007dca490003fd5248001f6a924009ff1492006fd8a490033ff4248019f7a124009ff90920007dc8490003fd4248001f6a124009ff10920067d8849002bff3248015f79924009ff8c920057dc649002bfd3248015f69924009ff0c920057d86490003ff61480017fb0a400bff98520015fcc290003fd6148017fe30a4002bf1852006ffea2900037f5148017ff28a4000ff54520006faa29002ffc5148019ffa0a400bff90520007fa829002ffc4148015ff98a400bff8c520057fa629002ffc3148013ff9
  | 2 => 0x500b7fe86a805bbf435402dff21aa016ff50d500b77a86a805bfc4354001ffb12a000bfd8950007fcc4a8003fd6254001fe312a009bf1895002ffea4a8017fe525400bfea92a005ff149500bffe84a8003fe4254001fea12a017ff109500b7fe64a805bfe325402dfe992a016ff0c950007fec2a8002ff615402bff30aa002bf98550007fac2a8057fc61540057e30aa005ffd455002efea2a8017fe515400bfea8aa000df5455002ff8a2a805fff415402bff20aa000ff505500aff882a805bff315402bff18aa016ff4c5500aff862a8003ff215402bff10aa000ff485500aff842a8006ff6054003ffa82a005fed415000ffca0a80077e5054003fe282a001df1415000ff0a0a8007ff4054003ff202a001ff1015000ffe60a8007fe3054003fe982a001ff0c15000ffc40a8007fc2054003ff882a001ff8415000ff820a8003ff65500017fb2a8000dfd9540004fecaa0053fe655000b7f32a8000ff59540005facaa0053fc655000b7e32a8000df1954002cf8caa0006ff6450009ffaa28004ff951400277ca8a0013fd5450001deaa28004ff1514009ffec6a004eff6350027ff31a8003bf98d4009ffac6a004efd6350027fe31a8003bf18d4009ffea6a004f7f5350027ff29a8013ff54d4009efaa6a004ffc5350009ffa1a8004efd0d40027fc86a0013fd4350027dea1a8004ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0026fc6250029ffa928000ff94940007faa4a0053fc5250009ffa128004ff90940027fa84a0013fc4250027ff9928013ff8c94009ffa64a004ffc3250001ffb0a8000bfd8540097fcc2a000afe6150001feb0a8012ff18540015f8c2a0053ff5150001bfa8a8012ff94540007faa2a00037d5150025fe28a8004ffd05400277e82a0013fe4150009fea0a8000ef50540027f882a004fff3150025ff18a8013ff4c540097f862a0003ff2150025ff10a8000ff48540097f842a0006ff6050003ffa828001ff9414000ffaa0a0007fc5050003ffa028004fed014000ffc80a0007be4050003fe2028001ef1014000ff080a0007ff3050003ff1828001ff4c14000ff860a0007fe2050003fe1028001ffc414000ffc20a0007fa1050003fe0828009ffd972004dfecb90027fe65c800b7f32e4009ff59720005facb90027fc65c80137e32e4009ffd932004dfec990027fe64c80097f3264009ff59320005fac990027fc64c80137e3264011ffd5320087fca990003fd54c8021fe2a64009ffd8f2004dfec790027fe63c80077f31e4009ff58f2007dfac790027fc63c80137e31e400fffd4f2007efea79003ffe53c801ffea9e400fdf54f2007ff8a79003fff43c801fdfa1e400fff90f2007ffa879003fbd43c801ffe21e4001bf98b2004ffea590047ef52c8013ff2964009fb94b2004ffaa59000
  | 3 => 0xfb264209bfd932104ffcc990812fe64c8413feb264200bf5932104ff8c990826fc64c843fffaa6421eff95321007faa99087bfc54c8413ffb1e4209bfd8f2104ffcc79080efe63c8413feb1e421dbf58f2104ff8c790826fc63c843bffa9e421ddfd4f210effca790877fd53c843bbea9e421dff14f210effe8790877bf43c843bff21e421dff50f210ef7a8790877fc43c84057f3164209ffd4b2104ffca590827fd52c8413fe2964209ffd0b2104ffc8590827ee42c8413fea164200fb50b2104ff88590827ff32c8413ff1964209fb8cb2104ffa6590877ed32c8413fe1964202bf58721017fea39080b7f51c8405ff28e4202ff54721016faa39080bfc51c8405ffa0e4202ff90721017fa839080bfc41c8405ff98e4202ff8c721017fa639080bfc31c8405ff10e4202fb88721017ec439080bfc21c8405f610e4209ffd832104ffcc190806fe60c8413feb064200bf5832104ff8c190806fc60c843fffa86421cff943210e7f8a19087bff40c8439ff206421cff103210effe6190873fe30c843bfe986421cff0c32104ffc4190827fc20c8405ff8864202ff84321017f82190803ff65484017fb2a421bff9952102dfcca90803fd65484017eb2a421bff1952102df8ca90803ff64484017fb22421aff99121025fcc890803fd64484017eb22421aff19121025f8c89086fff5448435ff2a24200ff551210d7f8a890867ff63484337fb1a4219ff98d2101dfcc690867fd63484337eb1a4219ff18d2101df8c690867ff5348433bfa9a4219ff94d210cffaa6908677d5348433fe29a4219ffd0d210cf7e8690867fe4348433fea1a4219ef50d210cff8869080aff6248437ffa924209ff94921007faa490827fc5248435ffa124209ff90921007dc8490803fd4248401f6a124209ff109210cffe6490827fe3248433f71924219ff4c9210cfda6490827fc32484057fb0a4202ffd4521016fea29080bfe5148405fea8a4202df54521017f8a29080bff4148405ff20a4202ff50521017f8829080bff3148405ff18a4202fd8c521017fa6290867f53148405fe18a4202ffc852104fee429080bfe2148405f710a4202ff08521017d8429080bf42148401ffb024200bfd81210c7fcc090806fe6048401feb024218ff1812100df8c09086fff5048431ff2824218ff141210d7fe8090863fe4048431fe2024219ffcc1210c7fc6090867fd3048431fe1824218ff8812104ff8409080bff1048405ff0824202ff0412100dfecaa8003ff64540017fb22a017ff99150025fcc8a8003fd645402ffe322a004bf1915002ffea8a80177f545400bff2a2a005ff55150006faa8a8017fc545402dffb1aa016bfd8d500b7fcc6a800efe635402dfeb1aa016bf58d500b7f8c6a800efc635400bffa9aa005dfd4d5002ffca6a8017fd535402dbea9aa005ff14d
  | 4 => 0x817ff525440bbfa92a205ff94951006fca4a8817fd5254401bea92a205ff1495102ef8a4a8897ff4254401ff212a200ff5095112ff884a8893ff3254449ff192a224ff4c951127f864a880aff6154405ffa8aa205fdd4551017fca2a880b7e5154405fe28aa202df14551017e8a2a880bff4154405ff20aa202ff10551017fe62a880bfe3154405fe98aa202ff0c551017fc42a880bfc2154401ffb02a200bfd815111ffcc0a8806fe6054401feb02a223ff1815100df8c0a8817ff505440bbfa82a205ff9415111efca0a8817fc505440bbe282a225ffd015111ffc80a888ffc4054449ff982a223ff8c151127fa60a888ffc3054447ff102a223ff08151017fe20a880bf71054405ff082a202ff04151006fec8a88977e6454401beb22a225df19151126fec6a88927f6354449bf31aa224df58d51124fac6a88937c6354449bfa1aa224cfd0d51126fc86a88937d43544499ea1aa224df10d51006fec4a88037e6254401beb12a200df1895112efe84a88037e4254401bea12a225df10951126fe64a88937e3254449be992a224df0c951016fec2a880a7f615440bbbb0aa202dfd0551016fc82a880b7c4154405bf98aa202df8c551016fa62a880b7c3154405bf10aa202df08551006fec0a888f7e6054401beb02a223df1815112efe80a888f7e4054447be202a224dfcc15111efc60a88937d3054447be182a223df8815111ef840a880b7f1054405bb882a202df84151016f820a8803ff65504017fb2a8222ff9954102dfccaa0803fd65504017eb2a8222ff1954102df8caa080aff6450409ffaa28204ff95141027faa8a0813fc5450443ffb1a8221bfd8d4110ffcc6a080efe6350443feb1a8221bf58d4110ff8c6a080efc6350443ffa9a8221dfd4d4110ffca6a0887fd5350443bea9a8221ff14d41027fe86a0813bf4350409ff21a8204ff50d4110f7a86a0813fc4350401ffb128200bfd8941007fcc4a0803fd6250401fe3128209bf18941117fea4a0803fe5250401fea928222ff14941027fe84a0813bf4250409ff2128204ff509410077a84a0813fc4250443ff9928221ff8c94110ffa64a0887fc32504057fb0a8202ffd4541016fea2a080bfe5150405fea8a8202df54541017f8a2a080bff4150409fba0a8202ff905410177c82a080bfc4150405de20a8202fd10541017fe62a080bfe3150405fe98a8202ff0c541017fc42a080bfc2150401ffb028200bfd8141107fcc0a0806fe6050401feb028220ff1814100df8c0a088bff5050441ff2828220ff14141027fe80a0813bf4050409ff2028204ff1014110ffe60a0883fe3050443fe9828220ff0c141107fc40a0883fc2050405ff8828202fdc4141017fc20a080bfc1050413ffb2e4209bfd972104ffccb90816fe65c8413feb2e4200bf5972104ff8cb90826fc65c8413f
  | 5 => 0x4642177f8a321013ff4190809ff20c8404ff1064217ffe63210bbfe319085ffe98c842eff0c64204ffc4321027fc2190813ffb048409ff9824200dfcc121027fd60908017eb048409ff1824200df8c1210c3ff509085bff284842dff14242027fe8121013fe4090809fe204842fffcc24216ffc61210bffd309085bfe1848409ff8824204ff841210bbff109085bff084842dff04242007fecaa1002ff6550859ff32a8405bf99542007facaa1002fd6550859fe32a8405bf1954204dfec8a1013ff5450809ff2a28404ff55142027f8a8a10afff63508577fb1a842bff98d4201dfcc6a10affd63508577eb1a842bff18d4201df8c6a10afff5350857bfa9a842bff94d4215ffaa6a10af7d5350857fe29a8404ffd0d420277e86a1013fe4350809fea1a842bef50d42027f886a1012ff6250859ffa928409ff94942007faa4a1027fc5250809ffa128404fbd094204ffc84a1027be4250813fe2128409ef10942027d884a10afff3250813ff192842bff4c94204ff864a1003ff61508017fb0a842aff98542015fcc2a1003fd6150855fe30a8402bf18542167fea2a10abfe5150855fe28a8404ffd05420277e82a1013fe4150809fe20a842bffcc542157fc62a10affd3150855fe18a842aff8854204ff842a1003ff60508017fb028429ff9814200dfcc0a1003fd6050853fe3028401bf18142167fea0a10a7fe5050853fe2828404ffd0142027fc80a1013fc4050857ff9828429ff8c14215ffa60a10a7fc3050853ff1028409ff08142157fe20a10a7fe1050853fe0828405dfd935102efcc9a88177d64d440bbe326a205dfd8f5102cfec7a88177e63d440bbeb1ea2279f58f5102ef8c7a889f7f43d444f9fa1ea227df90f5113efa87a889f3d43d444fbe21ea205dfd8b5102efcc5a88177d62d440bbe316a228dfd0b51006fc85a88037d42d4451be216a227dfccb5113efc65a889f7d32d444fbe196a2029f58751016fe83a880b7e41d4405be20ea202dfcc751016fc63a880b7d31d4405be18ea202df88751016f843a88177f60d440bbf306a205df5835102ef8c1a88a37f40d444dbf206a226df1035113efe61a889b7e30d444fbe986a226df0c351136fc41a889b7c20d4405bf886a202df84351016f821a880aff6554401ffb22a200bfd915112ffcc8a8812fe6454401feb22a225ff19151025f8c8a8817ff545440bbfaa2a205ff9515112efca8a8817fd5454401beaa2a205ff1515102ef8a8a8893ff63544497fb1aa224ff98d5101dfcc6a8893fd63544497eb1aa224ff18d5101df8c6a8817ff535440bbfa9aa205ff94d51126fca6a8817fd5354449bea9aa205ff14d5102ef8a6a8893ff4354449dfa1aa224ff90d51127fa86a8893bd4354449fe21aa200ffd8951005fec4a8803fe6254401feb12a200ff1895104df8c4a8
  | 6 => 0x1beaa4a405ff1525204ffec729026ff6394813ff31ca403bf98e5204ffac7290defd6394813fe31ca409bf18e5202ffea7290177f539480bff29ca405ff54e521befaa729017fc539486fffa1ca437efd0e521bffc87290dffd439486fdea1ca437ff10e5204dfcc529027ff5294813bfa94a405fbd4a5204ff8a529027ec5294813ffa14a409ff10a5204ffe6529027fe3294813fe994a409ff0ca5204ffec329027fe61948057f30ca409ff58652005fac329027fc61948057e30ca405ffd465202efea329017fe519480bfe28ca438ffd06521b7fc83290dbfc419486fff98ca436ff8c6521bffa63290dbfc3194813ff10ca409ff0865204ffec129027fe60948037f304a409ff58252005fac129027fc60948037e304a405ffd425202ffca1290d77e509480bfe284a405df142521c7fe81290d7fe409486bfe204a437ffcc2521affc61290dffd309486bfe184a409ff8825204ff841290dbff109486bff084a435ff0425204dfecaa9003ff64548017fb22a434ff99152025fcc8a9003fd6454869fe322a404bf1915202ffea8a9017fe545480bfeaa2a405ff1515219ffec6a90ceff6354867ff31aa403bf98d5219ffac6a90cefd6354867fe31aa403bf18d5202ffea6a90177f535480bff29aa405ff54d5219efaa6a9017fc5354867ffa1aa433efd0d5219ffc86a90cffd4354867dea1aa433ff10d5202dfec4a9017ff525480bf7a92a409ff9495204efca4a9027fc5254813be292a405fb149521a7fe84a9027fc4254867ff992a409ff8c95219ffa64a9027fc3254801ffb0aa400bfd8552197fcc2a900afe6154801feb0aa432ff18552015f8c2a9017ff515480bbfa8aa405ff9455202ff8a2a90d3ff4154865ff20aa432ff1055219ffe62a90cbfe3154867fe98aa432ff0c552197fc42a9027fc2154801ffb02a400bfd815218ffcc0a9006fe6054801feb02a431ff1815200df8c0a9017ff505480bff282a405ff141521a7fe80a90c7fe4054863fe202a433ffcc15218ffc60a90cffd3054863fe182a431ff8815204ff840a90cbff1054863ff082a431ff0415204ffecb21026ff6590813ff32c8405bf9964204ffacb21002fd6590813fe32c8409bf19642025fac921013ff5490809ff2a48404ff55242027f8a921027ff63908137fb1c8409ff98e4201dfcc721027fd639085f7eb1c8409ff18e4204df8c7210bfff539085fbfa9c842fff94e4217ffaa7210bf7d539085ffe29c8404ffd0e420277e8721013fe4390809fea1c842fef50e42027f88721026fe6290813ffa948409ff94a4204ffaa521027fc5290813ffa148409efd0a42027de8521027fc4290813f62148409ffcca4204ffc6521027fd3290813fe1948409ffd864204ffcc32100afe6190813feb0c8400bf5864204ff8c32100afc6190861ffa8c842eff9
  | 7 => 0xc00400000800401001402000000003401401402800c00c00c00000000000800400000400400400000800400800000801400001000800000400000000400000000800000800000800800400000001400000002001c00400000400000000000000800400800c00800000800c00800400000800401c00001000804400c00000000000000002000800800002000000400001801000c01000000000000400000000000800800400000c00800400c01000000000000000000802000000002802800001000000400800000000000c00400c01000400000800c00400000000400000000000800400400400c00400401c00400000400000000000400400000000000000000000400803401000c00000800004801800401400002000000800000800c00800000000000401400000801000000800000000400c00400000000001c00400c00800400400800400400000002000000c00000400001400c01400400401401400001000400800002400001400800400400000c00000000400000000400c00400c03401403c00000400000c00400000c00400000000001402400400000000001000000800000400000001400000c00800002400400400800400000000c00000400800000000000400400800400c00400400000001400000400000000401c00000400000000002800400000801000400000000001000000c02800400800400000000000401000400000400400401400002000c00000000001001400400c02000800000000000c00c004000000000097fb2aa804bfd9154027fea8aa017bf5455009ff2a2a804df95154027f8a8aa0137c5455009de2a2a83bffd8d541ddfec6aa0effe63550077f31aa83bff58d541ddfac6aa0effc63550077e31aa805ffd4d5402efea6aa017fe535500bfea9aa83bdf54d5402ff8a6aa013ff4355009dfa1aa804ff90d54027fa86aa0efbd4355009fe21aa800ffd8954005fec4aa003fe6255001feb12a800ff1895404df8c4aa017ff525500bfe292a805df14954027fe84aa013fc4255077ff992a83bff8c9541dffa64aa0effc3255001ffb0aa800bfd85541d7fcc2aa00afe6155001feb0aa83aff18554015f8c2aa017ff515500bbfa8aa805ff9455402ff8a2aa013ff4155009ff20aa804ff105541dffe62aa0ebfe3155077fe98aa83aff0c5541d7fc42aa0ebfc2155001ffb02a800bfd81541cffcc0aa006fe6055001feb02a839ff1815400df8c0aa017ff505500bbfa82a805ff9415402ff8a0aa013ff4055009dfa02a804ff90154027f880aa0efff3055073ff182a83bff4c1541cff860aa0e7fe2055073fe102a83affc41541cffc20aa0e7fc105500b7eb2ca409ffd925204ffcc929012fe6494813feb24a400bf5925204ff8c929026fc649480bffaa4a405dfd525202ffca929017fd549480
  | 8 => 0x26d8002078002e5acd17aa6c09e1c51638000000000002890000000002459b300026100000f8000000000001a01a71991650a180000000000000e97927aacc0000000129ed00024100013720d93c8000001988002df0000000000290000001bb1d980000000000000000000000000000280009900000028f1510000000001430002201458f92aaad400dae32470001880000002940000002398edb368000000001009ee32aa041d38000910988002152a5238ae688600027481600009087393380013aa0380000000000000000021a1be00011980000000028d80000005c1920580001a50000d280022e00000004f000291a740001b005784a80000000031c91a80000024f1d18001fb80015e0090000002120000000000720000003299e023d80000000000000000029296700000000000e0000000000000000000d180000000000000000000000025217d2d096404900000007780000000019800000028b00026a9668000000000000001f030d80000012e00000027894197e00005f026b30a8e00014e0002cdab90000000000cf00000000000000000020f8000000000938000000e28000000000000000f200030f1f22bc00883c8000f78003048002130000000620338000a980000029131d1fc000000000000059872ae70000af0000000000001899708000000000000000000000b98000001b800000011b861b252000000000002c780007e0000100000000391b9049a362900000002d90001c393e00000000031800000000005e80000000000015c8000000000003159910001cb96480000000007d980af12f388f00000000000000000000000010108c2fe0000001e299603c00000000026e13325326c800000188a5e8000f617f0978000000002db2bcb179ad9e3ad00000000002268000000002da9fb31c2660000ca00021696a19c07108300000024480000000000000000000005b80000000027b00000000001b80000000026ea0280000012d0ff0e68a480018a16800023d0828480298fe80000027c0003142138000000bb2c28ec0fd869800000000802000000800002400800000000000800800c00002c01000400000802c00001000000400000400000c00800000400c00000400400000c00001000400000c00000c01000000c00400800400400000800000400003800001800000000000800000400000400000400000000400c00000c00801400400800401c01000000400001000800000800000400000801000000c00000000400800c00400401c00000000001001401400000400c01800000c00c00000000000400800000000000000c00400400001800800800000400000000402401002c00800403400000001c00400000400800000800800c00000400c00c00000000c00000400001c000000004000004004014008004
  | 9 => 0x1eb2a6a2a9220000658000000000001160000000000000001072ea9210211938000002141588000000672460000000000000000002f080000000021780023032d03fa0680000011f0001320001860000888000000000002848001fa2fd31b1970ee8411df81c01d0000000000702a090502e00000000000024a0000000000002b8aca984800093051a63979a7f23c92c80016e2808001842d50001c4a86a4f8c0800047085a9f86ca2500000000000000006513080000011d00011f8002780c80188001d48000000000000000000002800000000000000f59fe09f02880006c0001618e43232a300003f1fda9a07a16ca47b1f25f8001140000c78000000000198758000000002020000001ec1468000e5000000297abe8000000000b08f700003680000000011d8000ee2a487980000000000010600000000004c80000000000000000025830e9f79f18b180000021e8000002e415a98186122d92f8000003330000b78000972ec90f0d30000000000000000000000000003170000000000000000000000f5000000000060b0c93d8001ea00000000000015c2ffb0a316a441df0ac32024e1d20001e98002bd80000016d0001a080007180000000000018a8000d20003008000001ad0000000001620bf3322b080000a8000001312b79598000000001740000000000002828489b2892217103a008ab800011a779e50000001119d006028200009d80007f2f58000000e600000000000000000000002b0000000000002d2b26a2580028c00002388200014f8000000001ec8000000000000000002c107ea939820b293b02c2080fe00000009580000000000026900014b1b7a10a770001bf9b42a70819190000c9000000000000000219a5900017796b8000000000000000000000002e285a8bc0001560000000002ab0001b18002a80000002308001ed80032e8c88001fd1c198b25100025582d80008a00009d25b00019b96920a0001f09609d12c93018000000000000002c5110a3200000000017c8000000000002630000002640002810533290c48000001098001d70000002430c380029200000000025c8000080c980000000000000018da2b0000000001a4a6a1088001630001b68001a98a32b58e20000001a38002e10000000000000270a209a8000000a425500000002d0000000000002729768c29360ae9a400028a8e70000002498001b50000000000002049a332b01400010a00005d0000000000869068000000000342f4000000271a0b8a11da9cf0002a911720f2d60b316f800000129b068121879f50f02e831200000000000000000000004f94106787714519c9558000000002b00002ed1408030000000002330000000bf8000000000001c6a758b88003350000002fda4ca688000001aa1e584184d96d8001e21a79531ba8c300000
  | 10 => 0x27c9dd00000020d0000002540002b20558eb8000000000000000280000e080000017c0eb0ce00000000000000000000016aa450000630000000e0251800218139ae880000000010d0000b61dc33294a00d1242589090ad0250000000000b58a8a6d0000000000000000002a400009b8458000001f9800105b1a8002568000398cc80000000003106f80000000000000000012580000000000000005db1f8002faa2d28d0000e88000001828000f28f68000000002428000a70000001b3b3180004699197130d30700023eb079efb0505e211a279701952fc3241ff0ef23a99a862b3780000007c0bb9feb239c30000918842af80000000000000007b00000c8000001ae9260e98000000001bb904a6503b80007bafb8b804480019a237b3580009c8000900838588be9e195b9af8000000001cf87a8950000002ef98b8002348000000cd25e0329500000279ee92dab1ac41cd0002eb2dcad201a0000320572de8be00010f8000000001bc0058000d8b1ba9b9be9fa93480000000016c0a780000007080000011113d00000027a00000000014c8000000002ae8001830f3b272e0add00523b8d82a3a28a67aae00000000020100015188501780004780000000008000000014d8000000000790002098000000bd9d523a0000002f28001752c62b322cae21d431902f87f9f8239084a841900003219de80006baf007400000022c0000000dd8002969770cb84e91a00000030b00000000000000480017489a0000020001268001b0a7e20718c27eaf806b04b26f8358000001c100026bb2821c9152860dd0a600000015200000012793f0c40041dc8000000002c080000026980680000000000000000000028880000000027f8000e380000000023e25701801b30312c00025496797d8000000000002720000a2a5c1f49231ffb119b8824b2486680012732fa0c80007d01f8002b40b018eaef28a1159b9adb8002ce2ca12808b00014eabb8309480000002c9a971ce91680000030a8000000370000000000000db84080007c80000000000000020e8000000001d829a80005400000000029f0002da0001eb8fba1d1968000000060001948000001da2e7ac70db00000000000013500000000019b0000cf8000000002ff00029ea2380000000000000000000012a822015ab10000001ac80000000017a2c193e8000001858000000000002d78001ef0aa00000000029b000000000000000193275000000000249000000000000000314acf0cda0901315f098162b38a960002a1af880f0000001e30000e195380024c1d913280000000000000013582a8000000c522b8000000000000000000a821c1c00000002ce80023f8000002bf2270001578ae000000000a4d80014a8000000242f180028e80027b8000a3a4d0001bd0001f3b1092f190a57800
  | 11 => 0x14880025a0000000000a50c70002f48000000000000000000000000000000000002ccb373022e38000000000000001b60548f48b70000000000000000001ab10e0c68001b580012291219f80000011e9040d490d80016980006e9d3000000334ab81f10d000000000030e2fe8002d70000002539e100000005f8000000000002bf9200000003188000002ee0000000d418006e00019e1bd8aa8002cfa839ba3162d3a6b1fc80a0000bd00000015a30980003d2623362ea07888f973000214a36a7997818515480c1472e63150002d497200014900000008c86a10313a1541aa8000001f931a32111c06f00006902a00028b8568bc972800000000183a1d84419788798e205814b2c17191295828585502f2f60000000001100cc0000002f22338000000000430000e90001f5b130462103279388000f320b2878680001ca2a60348e780001100018f809aac8ff8508000001078000a696b00011ca951590000000b400019e80b8000ba2e18001cc8000000d9ab684222f0000002e92598002438000000000ea00000001d97880000012a1a5a1b0001760000dc81c80000024800000000010c00000003a8000d93101f30768000000000000000000648b49bf10a9e70001d6250a673139662d59759ea96e8dc2128001db00000000000012ba9c8001d580006884d0000000000002988000000000039c98fa80003e93900000000000018690e96582580000011b0000428001e90e4a2190cb05ab2a5aabe0f4000000000000270a20a8314219d2089a92760001d783783a00000000027022a0000000002898000000002b50000fb00010b0948b12f98168000ba8000000000000002d98000000640001cd80028180000000000000000020e1d080000015e800194173a1880000000005a2f91d880000000017e8000000968001ae0001db8d080000003e0000000001dda420f9abb0000200000000002649f68002bd00000026800014493780010b8000003002c005b0000000218000000000002eb9cb0001d28e10f08000000000002d18000000000000000001872768000000000000000000002738001a81b48000000000000000000002b9800131af30ad8c200030c262aa100000000000000000011300014c000000000256000000265a243340000001ca9ce1218000000001a100030b8000000001c882b8a082e800000000120a260f880000000000000000000021f240b1e0000003090000748000eca060000000000002e9b2c8002351a20880000000001c42b72d88001d68001438002fc9f611380003008eaa79189e419f0000002a000000000000000004b8003228002ba102b288001569ac0512de00030380027d9e78002e500000000030808d95d856000123a2123113b80025f000248a710362b38000000002299de00023c2c88000001
  | 12 => 0x15b1018000000d6a2fb2d8de9f70000000000000000890d580009280000000011780029814b8000003128000ef80000009c1a2a99800043aa58000001369a18d618120a8520de0b68000eaaac0fc8761998590d50000002d81c2320ab480021faed80000000016100000000000000022e8000003259892018001340001300000b52dd9688812aa000000000007a1600000000000000018f0001e48000000001148cb17b2b600000000025d0000002e00000000000002528808002c831eac30002f715f9401248073088190002908752f693c0f81462358df8000a58000138da8000000000000000000941e82cb00000019da7d0fd0000fc0000000fa1c78000002f530600000004c0000000df00000028f8da0c61c0a4b3028cea1e00031d81700000007300032b80029492b0000000000960012050000000228001e619581e88712500015d0000330000000000c5aee9a68a901e00000000000000000000000004a00003880000021a80000000000000025b9601a89c70000e82880502401a61570318002fb2c200029d800138001800246aaf0001cc2a200000000030400000000000029d0000000000000000000000000000b39e0ac680000000000020c2418000d78000001bc8c12fa222aec00023b261a282adaba81524b8001c58e5a2200033394280000000018cad30000002668003260000001af00000027309f8000b214f0d700000014424e80023827900002300023f0000208000000000000002dc000000000000000000000295a6f0002992603111f415080000000008e0f18d38662ab80000000021580000000001a8109b21f8b198000001c2a1bacb80000006daa280000000000000029c28500032200000008d00032e0acaa98400000001c62e48898002f780000014d10814780000000000000030123186d229099b2f118224a932c4a4aac580028700000000000000008a80000000025da371ab8350528000000001b700000000000000000000018d00006a85c8d10000002190002608000002030000000000000000538000000000000001928000001e89c81b100000000b2c381f16f0000450ab0000000002ad09b2d10f100002c80000017b83b0002340000000c000000000000000000000000000000032a0c180015280000000012893f8001e680000000000000000000014980028c97fa9e0000b909e80000030f9f28000000000002a88000000e30000000638000000780000002500260000a00000ca8002df92ea233381552112d680011e000000102331000000000000000000232b300380af8001c903d80000004e0ed08b92900
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x72050510107f22050510107e52050510015f87650110026f87650110014f876501100077b755011000778755011000dfb745011000fbb7450110007bb6450110026fa6450110026f8645011003fb8645011003fba5450110007b9545011020dfb735011020df973501102077b535011020779535011003fbb4350110207b94350110005fb7250110007f37150110015fa7150110015f87150110097f0715011000efb615011000ff361501100977b5150110097f25150110097795150110007f15150110007715150110097bb4150110097f24150110097b9415011003ff14150110007b14150110097f23150110207f13150110015f8764811004ef87648110014f876481100077b7548110007787548110005fb7448110005f974481101edfb73481101edf973481101e6fb63481101e6f963481101e77b53481101e77953481101e7bb43481101e7b9434811000dfb724811000feb7248110007eb624811004efa624811004ef86248110007e862481101ffeb5248110007ea5248110007e952481101ffe852481101f7eb4248110007ea4248110007e942481101f7e842481101e7eb32481101e7ea32481101e7e932481101e7e83248110007f37148110015fa7148110015f8714811005ff0714811000efb614811000ff3614811005f7b514811005ff2514811005f795148110007f1514811000771514811005ff24148110007f1414811005ff231481101e7f1314811005feb214811005fea214811005fe9214811005fe82148110007eb764811004eeb764811005fe8764811005ee87648110007eb75481100076b75481101ffea7548110007e975481101ffe87548110007687548110007eb65481101ffea6548110007e965481101ffe86548110007eb74481101f7ea7448110007e974481101f7e87448110007eb64481101f7ea6448110007e964481101f7e864481101ffeb54481101f7ea5448110007e954481101f7e854481101efeb73481101e7ea73481101efe973481101e7e873481101e7eb63481101e6eb63481101e7ea63481101e7e963481101e6e963481101e7e863481101e7eb53481101e76b53481101e7ea53481101e7e953481101e76953481101e7e853481101e7eb43481101e7ab43481101e7ea43481101e7e943481101e7a943481101e7e8434811005feb7148110007e3714811005fea714811005fe9714811005fe8714811005fe0714811000feb614811000eeb614811000fe3614811005feb514811005f6b514811005fea514811005fe2514811005fe9514811005f695148110007e1514811000761514811005fe8514811005feb414811005fea414811005fe2414811005fe94148110007e1414811005fe8414811005feb314811005fea314811005fe2314811005fe931481101e7e1314811005fe83148110
  | 1 => 0x4910004fd769491004cfc76949100067f659491002e7c659491000dfa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc765491004cff7690910004fe7690910004fd769091004cfc7690910006bf6490910026bc649091004eee6290910006ed629091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc765091004eee6250910006ed625091000dfa705091000df4765451002ef4765451000cf47654510015f7755451001777755451000777655451002ef6655451002ef46554510047746554510005f7745451004777545451022f765454510007755454510047745454510235f77354510235f57354510047775354510227765354510227755354510047745354510227b74354510227b54354510047775254510007765254510007755254510047745254510007f3705451000df6705451000df4705451011ff07054510016f76054510017f3605451011f77505451011f76505451011f75505451011f74505451011ff2405451011ff23054510227f1305451011fe7205451011ff2205451011fe5205451004777765451002e77765451011f74765451002e74765451000777745451022f76745451000775745451022f74745451000777645451022f76645451000775645451022f74645451023777735451023577735451022776735451023775735451023575735451022774735451022777635451022776635451022775635451022774635451022777435451022737435451022776435451022775435451022735435451022774435451000777725451000776725451000775725451000774725451000777625451000776625451000775625451000774625451022f77425451000776425451000775425451022f74425451022777325451022776325451022775325451022774325451011f77705451000773705451011f76705451011f75705451011f74705451011f70705451001777605451001677605451001773605451011f77405451011f76405451011f72405451011f75405451011f74405451011f77305451011f76305451011f72305451011f75305451022771305451011f74305451011f77205451011f67205451011f76205451011f72205451011f75205451011f65205451011f74205451000df47650510026f4765051000cf47650510005f77550510005f57550510015f77450510017b77450510007b76450510026f66450510026f4645051003fb4645051021df7735051021df5735051021777535051021775535051003fb74350510217b5435051003fb74250510007b54250510007f3705051000df6705051000df47050510107f07050510016f76050510017f36050510107b74050510107f24050510107b54050510107f23050510217f13050510107e
  | 2 => 0x11eef205951011eed2059510024fe76d911003ebe64d911002cfe75d9110004fd75d911002cfc75d9110104fd74d9110006bf54d911003ebc54d9110004ff73d911001cfe73d9110004fd73d911001cfc73d91100067f53d91100067d53d911003ebf43d9110006bd43d911004cfe72d9110004fd72d911003ebc42d911000cff71d9110014fe71d911000cfd71d9110014fc71d91102667f51d91102667d51d9110266bf41d9110266bd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110256bf40d9110256bd40d9110256ef20d9110256ed20d9110024ff76591100057f75591100457c755911003ebc645911024df7715911025dfb7059110004ff75591100067f75591100047f755911002cfe755911002cfc75591100067c755911002c7c7559110254ff7459110006bf7459110004ff735911001cfe7359110004fd735911001cfc73591100067f53591100067d535911003ebf4359110006bd4359110004ff725911004cfc725911024cff7159110006f771591100967f51591100967d5159110104ff7059110006fb7059110106ef2059110106ed2059110004ff7655110004fe7655110004fd7655110004fc765511002e7e65551100067d6555110015f6715511004cfe76d891002cfe75d8910004fd75d891002cfc75d8910024fe74d8910004fd74d8910024fc74d8910004ff73d891001cfe73d8910004fd73d891001cfc73d89100067f53d89100067d53d8910006bf43d8910006bd43d891000cff71d8910014fe71d891000cfd71d8910014fc71d89102467f51d89102467d51d8910246f631d8910006f531d8910246ef21d8910246ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d891023efa30d8910006f930d891023eef20d891023eed20d89100c4fd7698910006ef62989100c5f5719891005df9709891004cff76589100057f75589100457c7558910005bf745891003dbc7458910005df7358910035dc73589100e5f77158910075fb7058910004ff75589100067f75589100047f755891002cfe755891002cfc75589100067c755891002c7c7558910004ff7458910006bf7458910004bf7458910024fe7458910024fc7458910006bc7458910024bc7458910004ff7358910006df7358910004df735891001cfe7358910004fd735891001cfc7358910006dc735891001cdc73589100067f53589100067d5358910006bf4358910006bd4358910006ef7258910006ee3258910006ed32589100e4ff7158910006f7715891005e7f515891005e7d515891005ef63158910006f5315891005eee215891005eec21589100c4ff7058910006fb70589100c6fa3058910006f930589100c6ef20589100c6ed205891023cfe761891004eee6218910006ed621891004cff7694910004fe769
  | 3 => 0xf755052006dee7550520005ed755052006dec75505200076f65505200076c6550520255ef7450520067ae6450520007ad64505202b5ef7350520055ee73505202b5ed7350520055ec73505202af6f53505202af6d5350520067af43505202afad435052024def715052005f6f515052005f6d5150520067e7415052005fae415052005fac415052005fe44150520105ef705052000dee705052000dec7050520106ef6050520107af4050520107ad4050520107ea30505202afe93050520107e71050520107ea105052000fea76d812000dea76d812000eea76d812004feb75d812004fea75d812004fe975d812004fe875d8120007eb65d81200076b65d812029fea65d8120007e965d812029fe865d81200076865d812004feb74d812004fea74d812004fe974d812004fe874d8120007eb64d8120297ea64d8120007e964d8120297e864d812029feb54d8120297ea54d8120007e954d8120297e854d812004feb73d812004deb73d812004fea73d812004fe973d81202a5e973d812004fe873d812028feb63d812028fea63d812028fe963d812028fe863d812028feb53d812028f6b53d812028fea53d812028fe953d812028f6953d812028fe853d812028feb43d812028fab43d812028fea43d812028fe943d812028fa943d812028fe843d812004feb71d812004fea71d812004fe971d8120005e971d812004fe871d8120007eb61d8120287ea61d8120007e961d8120287e861d812029feb51d81200076b51d8120287ea51d8120007e951d81200076951d8120287e851d8120297eb41d8120287ea41d8120007e941d8120287e841d812028feb31d8120287ea31d812028fe931d8120287e831d812002cfe76d95100467e65d951011cfd75d9510024fe74d9510004fd74d9510024fc74d95100067e54d95100467c54d9510004ff73d951001cfe73d9510004fd73d951001cfc73d95100467f53d95100067d53d9510006bf43d9510006bd43d951004cfe72d9510004fd72d95100467c52d951000cff71d9510014fe71d951000cfd71d9510014fc71d951027e7f51d951027e7d51d9510014ff70d951000cfe70d9510014fd70d951000cfc70d951026e7f50d951026e7d50d951026eef20d951026eed20d951002cff76595100467c6559510005bf745951003dbc7459510135f77159510275fb705951026cff75595100067f7559510004ff7459510006bf7459510004bf7459510024fe7459510024fc7459510006bc7459510024bc74595100467f5459510004ff735951001cfe7359510004fd735951001cfc73595100467f53595100067d5359510006bf4359510006bd4359510004ff725951004cfc7259510134ff7159510006f771595100ae7f515951011e7d515951011cff7059510006fb705951011e7e505951011e7c5059510
  | 4 => 0x452006f6f74d452006f6e74d452006f6d74d452006f6c74d45200076f64d45202e76e64d45200076d64d45202e76c64d452006f6f73d452006d6f73d452006f6e73d452006f6d73d45202dd6d73d452006f6c73d45202d76f63d45202d76e63d45202d76d63d45202d76c63d45202d76f43d45202d72f43d45202d76e43d45202d76d43d45202d72d43d45202d76c43d452011d6d71d452005f6f61d452005f6e61d452005f6d61d452005f6c61d452005f6f41d452005f6e41d452005f6c41d452005f6f31d452005f6e31d452005f6d31d452005f6c31d45201376f70d45201376e70d45201376d70d45201376c70d45201376f60d45201366f60d45201376f40d45201376e40d45201376d40d45201376c40d45201376f30d45201376e30d45201376a30d45201376d30d45202d76930d45201376c30d45201376f10d45201376e10d45201376a10d45201376d10d45201376c10d4520005ef7654520005ee7654520005ed7654520005ec765452026def75545200076f655452006f6e65545200076d655452006f6c6554520005ef7454520065ee7454520065ec745452006f6f54545202cf6e54545200076d545452006f6c54545202c5ef7354520055ee73545202c5ed7354520055ec735452006f6f53545202bf6e53545202bf6d535452006f6c53545202bfaf43545202bfad4354520135ef715452006fe7515452005f6e515452005f6c515452005fe4515452011def705452000dee705452000dec705452011eef605452011f6f505452011f6e505452011f6d505452011f6c505452011fea30545202bfe9305452011fe7105452011fea10545200076f76545200076e76545200056e76545200076d76545200076c76545200056c76545200076f74545202cf6e74545200076d74545202cf6c74545200076f64545202cf6e64545200076d64545202cf6c64545202c76f73545202c56f73545202bf6e73545202c76d73545202c56d73545202bf6c73545202bf6f63545202bf6e63545202bf6d63545202bf6c63545202bf6f43545202bf2f43545202bf6e43545202bf6d43545202bf2d43545202bf6c435452005f6f71545201356f715452006f67715452005f6f615452005f6e615452005f6d615452005f6c615452005f6f415452005f6e415452005f6c415452005f6f315452005f6e315452005f6d315452005f6c315452011f6f705452011f6e705452011f6d705452011f6c705452011f6f605452011e6f605452011f6f405452011f6e405452011f6d405452011f6c405452011f6f305452011f6e305452011f6a305452011f6d30545202bf69305452011f6c305452011f6f105452011f67105452011f6e105452011f6a105452011f6d105452011f6c1054520005ef7650520005ee7650520005ed7650520005ec7650520005e
  | 5 => 0x16ded70d912000dec70d912016eef60d912016faf40d912016fad40d912016fea30d9120007e930d912016fea10d9120315ef7659120005ef75591200076f75591200056f755912006dee755912006dec75591200076c755912006d6c75591200076f65591200076c655912016def7459120007af6459120066ee6459120066ec6459120067ac6459120005ef7359120055ee7359120005ed7359120055ec73591200076f53591200076d5359120067af4359120007ad4359120005ef715912005dee715912005dec7159120067af415912014def7059120007eb7059120005eb705912014eef605912014fea3059120007e9305912014fea1059120005ef7655120005ee7655120005ed7655120005ec765512030def75551200076f655512006f6c6555120305ef745512006faf54551200676e54551200676c5455120067ac54551202fdef7355120055ee73551202fded7355120055ec735512006f6f53551202f76d5355120067af43551202f7ad4355120005ef715512005dee715512005dec715512006f6f51551201cdef7055120007eb7055120005eb705512000dee70551201cded705512000dec70551201cfe8705512000de870551201ceef60551201cf6f50551201cf6d50551201cfaf40551201cfad40551201cfea30551202f7e930551201cfea10551202edee76d85200076f75d852006dee75d8520005ed75d852006dec75d85200076c75d85200076f65d85200076c65d8520065ee74d8520005ed74d8520065ec74d8520006ef64d8520006ed64d8520005ef73d8520055ee73d8520005ed73d8520055ec73d8520006ef63d8520006ed63d85200076f53d85200076d53d8520007af43d8520007ad43d852005eee61d852005fe661d852005eec61d852004def70d8520007eb70d852000dee70d85200e5ed70d852000dec70d85200e6ef60d85200e7ea30d8520007e930d85200e7e710d85200e7ea10d85200e7e510d852023def7658520005ef75585200076f75585200056f755852006dee755852006dec75585200076c755852006d6c75585200076f65585200076c6558520005ef7458520007af7458520005af7458520065ee7458520065ec7458520007ac7458520065ac7458520006ef6458520006ed6458520005ef7358520007cf7358520005cf7358520055ee7358520005ed7358520055ec7358520007cc7358520055cc7358520006ef6358520006ed63585200076f53585200076d5358520007af4358520007ad43585200e5ef7158520007e7615852005eee615852005eec615852005fe4615852005fe63158520007e531585200c5ef7058520007eb7058520005eb70585200c7ea3058520007e930585200c7ea105852006f6f76d452006f6e76d45200056e76d452006f6d76d452006f6c76d452006d6c76d
  | 6 => 0xe76d95200076f74d95200076e74d95200076d74d95200076c74d95200076e64d95200076c64d95200076f73d95200056f73d95200076e73d95200076d73d95200056d73d95200076c73d95200076f63d95200076e63d95200076d63d95200076c63d95200076f43d95200072f43d95200076e43d95200076d43d95200072d43d95200076c43d95200076f71d95200076e71d95200076d71d95200056d71d95200076c71d95200076e61d95200076c61d95200076f41d95200076e41d95200076c41d95200076f31d95200076e31d95200076d31d95200076c31d95201af6f70d95201af6e70d95201af6d70d95201af6c70d95201af6f60d95201ae6f60d95201af6f40d95201af6e40d95201af6d40d95201af6c40d95201af6f30d95201af6e30d95201af6a30d95201af6d30d95200076930d95201af6c30d95201af6f10d95201af6e10d95201af6a10d95201af6d10d95201af6c10d952032def76595201adef75595200076f655952006eee655952006eec655952006f6c6559520005ef7459520065ee7459520065ec7459520005ef7359520055ee7359520005ed7359520055ec735952006f6f53595200076d5359520007af4359520007ad4359520005ef715952005dee715952005dec715952006f6f515952018def7059520007eb7059520005eb705952018eef605952018fea3059520007e9305952018fea105952006f6e76195201ad6e761952006e6e761952006f6f741952006f6e741952006f6d741952006f6c74195200076e64195200076c641952006f6f731952006d6f731952006f6e731952006f6d73195200056d731952006f6c73195200076f63195200076e63195200076d63195200076c63195200076f43195200072f43195200076e43195200076d43195200072d43195200076c431952006f6f711952006f6e711952006f6d71195200056d711952006f6c71195200076e61195200076c61195200076f41195200076e41195200076c41195200076f31195200076e31195200076d31195200076c31195203276f70195203276e70195203276d70195203276c70195203276f60195203266f60195203276f40195203276e40195203276d40195203276c40195203276f30195203276e30195203276a30195203276d30195200076930195203276c30195203276f10195203276e10195203276a10195203276d10195203276c101952031dee76d912006dee75d9120005ed75d912006dec75d91200076f65d91200076c65d912014ded74d9120066ee64d9120067ae64d9120066ec64d9120005ef73d9120055ee73d9120005ed73d9120055ec73d91200076f53d91200076d53d9120067af43d9120007ad43d912005dee71d9120005ed71d912005dec71d9120007ae41d9120067ac41d912004def70d912000dee70d9120
  | 7 => 0x45202bf3f43545202bf3d43545200076f72545200076e72545200076d72545200076c725452011e7f62545202cf6f42545200076e42545200076d42545202cf6c42545202bf6f32545202bf6e32545202bf6d32545202bf6c32545201357f715452006f77715452005e7f61545200167e61545200167c615452005f6e215452005f6c215452011e7f605452011f7a30545202bf7930545203577b205452011f6e205452011f6c205452011f78205452011f77105452011f7a1054520004ff7650520004fe7650520004fc76505200067f65505201167c6550520026be6450520006bd6450520005ef725052004dec7250520067af4250520007ad42505202edee76c852004eee76c852004def75c852006dee75c8520005ed75c852004dec75c85200076f65c85200076c65c852004def74c8520065ee74c8520005ed74c852004dec74c8520006ef64c8520006ed64c852004def73c8520055ee73c852034ded73c852004dec73c8520346ef63c8520346ed63c85203476f53c85203476d53c8520347af43c8520347ad43c85200c5ed71c8520016ee61c8520016ec61c852005f6f51c852005f6d51c852004feb70c852000dee70c852000dec70c852004fe870c852004eef60c852004feb60c85200e7ea30c8520347e930c85200e7ea10c852000cfc76485200067f65485200de7c654852023def7248520006f76148520016f46148520005fb704852000df8704852004fe8204852000dec7648520016ec764852000cec7648520005ef754852006dee7548520005ed754852006dec75485200076f65485200076c6548520005ef7448520065ee7448520005ed7448520065ec7448520006ef6448520006ed644852033def7348520055ee734852033ded7348520055ec7348520336ef6348520336ed63485203376f53485203376d5348520337af4348520337ad434852004def714852004fe77148520007e76148520016ee6148520016ec614852005fe4614852005f6f514852005f6d514852005fe63148520337e53148520007eb704852000dee704852000dec70485200c7e8704852004eef604852004feb60485200c7ea3048520337e930485200c7ea1048520325ee76d952018ded75d952006eee65d952006f6e65d952006eec65d9520065ee74d9520005ed74d9520065ec74d952006f6f54d95200076e54d952006f6c54d9520005ef73d9520055ee73d9520005ed73d9520055ec73d952006f6f53d95200076e53d95200076d53d952006f6c53d9520007af43d9520007ad43d952005dee71d9520005ed71d952005dec71d952006f6f51d95200076e51d952006f6c51d952004def70d952000dee70d95201aded70d952000dec70d95201aeef60d95201af6f50d95201af6d50d95201afea30d9520007e930d95201afea10d95203256
  | 8 => 0xcfc76509200067f65509201667c6550920006bf6450920026bc6450920315ef7250920005fb705092000df8705092000dec7650920026ec765092000cec7650920005ef755092006dee7550920005ed755092006dec75509200076f65509200076c655092004def745092004faf7450920007af6450920026ee6450920026ec6450920067ac645092036def7350920055ee735092036ded7350920055ec73509203676f53509203676d5350920067af4350920367ad4350920005ef715092005dee715092005dec7150920067af4150920007eb705092000dee705092000dec705092014fe8705092004eef605092004feb605092014fea3050920367e9305092014fea1050920014fe76d85200067f65d85200067c65d852004dee72d852000ded72d852005ef661d852005fe621d85200067f75d852002cfe75d8520004fd75d852002cfc75d85200067c75d8520024fe74d8520004fd74d8520024fc74d8520004ff73d852001cfe73d8520004fd73d852001cfc73d85200067f53d85200067d53d8520006bf43d8520006bd43d852000cfd72d85200e6ed72d852000ced72d8520014fc72d8520006ee42d8520006ed42d8520006ee32d8520006ed32d852005eee21d852005ef621d852005eec21d852000cfe70d852004cfd70d852000cfc70d85200e6fa30d8520006f930d85200e6f710d85200057f755852006d7c75585200067f65585200067c6558520005bf7458520065bc7458520005df7358520055dc735852005ef4615852002e7f76d45200057e76d452006e7e76d45200047e76d452006e7d76d452006d7c76d452002e7c76d452002c7c76d45200067f64d45201467e64d45200067d64d45201467c64d452006d7f73d45202dd7d73d45202d67f63d452013e7e63d45202d67d63d452013e7c63d45202d73f43d45202d73d43d452006f6f72d452006f6e72d452006f6d72d452006f6c72d45201367f62d45202e76f42d45200076e42d45200076d42d45202e76c42d45202d76f32d45202d76e32d45202d76d32d45202d76c32d452011d7d71d452005e7f61d45200167e61d45200167c61d452005f6e21d452005f6c21d45201367f60d45201377a30d45202d77930d452035f7b20d45201376e20d45201376c20d45201377820d45201377a10d4520004ff7654520004fe7654520004fc76545200067f655452002e7e65545200067d655452002e7c6554520005ef725452004dec725452006f6f52545200076e52545200076d525452006f6c52545200067f76545200057e76545200067e76545200047e76545200067d76545200057c76545200067c76545200047c76545200067f645452012e7e64545200067d645452012e7c64545202c57f73545202c57d73545202be7f63545201267e63545202be7d63545201267c635
  | 9 => 0xe72d912000cfd72d912016eed72d912000ced72d912004cfc72d9120066bf42d9120066ef42d9120066ec42d9120014fe71d9120004fd71d9120014fc71d9120006be41d9120066bc41d912004cff70d912004cfd70d912016ebf40d912016ebd40d912016efa10d91200057f755912006d7c75591200067f65591200067c6559120066bc6459120315ef7259120004ff75591200067f75591200047f755912002cfe755912002cfc75591200067c755912002c7c755912016cff7459120006bf7459120004ff735912001cfe7359120004fd735912001cfc73591200067f53591200067d5359120066bf4359120006bd4359120314ff7259120006ef7259120066ef4259120066ec4259120004ff7159120014fe7159120014fc7159120066bf415912014cff7059120006fb705912014efa1059120004ff7655120004fe7655120004fd7655120004fc76551200067f655512002e7c6555120005ef725512004dec725512006f6c5255120005fb705512000df87055120325ee769492004eee769492018ded75949201af6f659492002eee659492002eec659492006f6c659492002e6c6594920065ee7494920005ed749492004dec749492006f6f54949200076d549492004def7394920055ee739492039ded739492004dec739492006f6f53949203976d5394920397af4394920397ad439492005dee7194920005ed719492004dec719492006f6f519492000dee709492000dec709492004eef609492004feb60949201af6e50949201af6c50949201afea3094920397e930949201afea109492002cff765492000cfe765492018cfd765492000cfc76549200067f655492002e7c655492032def7254920005fb705492000df8705492000dec765492002eec765492000cec765492004def755492004f6f75549200076f655492002eee655492002eec655492006f6c6554920005ef7454920065ee7454920065ec745492038def7354920055ee735492038ded7354920055ec735492006f6f53549203876d5354920387af4354920387ad4354920005ef715492005dee715492005dec715492006f6f5154920007eb705492000dee705492000dec705492018fe8705492004eef605492004feb605492018fea3054920387e9305492018fea105492031dee769092004eee769092004def759092006dee7590920005ed759092004dec75909200076f65909200076c659092014ded7490920026ee6490920026ec649092004def7390920055ee739092037ded739092004dec73909203776f53909203776d5390920067af4390920377ad439092005dee7190920005ed719092004dec719092000dee709092000dec709092004eef609092004feb609092016fea3090920377e9309092016fea1090920024ff765092000cfe765092014cfd7650920
  | 10 => 0x95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95200073f43d95200073d43d95201af6f72d952006f6e72d95201af6d72d95200076f42d95200076c42d95200076f32d95200076e32d95200076d32d95200076c32d95200057d71d95200067e61d95200067c61d95200076e21d95200076c21d95201af7a30d95200077930d95203af7b20d95201af6e20d95201af6c20d95201af7820d95201af7a10d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200063f43d95200067e43d95200067d43d95200063d43d95200067c43d95201ae7f72d95203ae7e72d952006e6e72d95201ae7d72d95201ae6d72d95201ae7c72d95200067f42d95203ae7e42d95203ae7c42d95200067f32d95203ae7e32d95200067d32d95203ae7c32d95200067f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200067e41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95203ae7f21d95200067e21d95203ae7c21d95201ae7f70d95201ae7e70d95201ae7d70d95201ae7c70d95201ae7f40d95201ae7e40d95201ae7d40d95201ae7c40d95201ae7f30d95201ae7e30d95201ae7d30d95201ae7c30d95201ae7f20d95201ae7e20d95201ae7c20d95201ae7f10d95201ae7e10d95201ae7d10d95201ae7c10d952006e7c655952032def72595201acff75595200067f7559520004ff7459520024fe7459520024fc7459520004ff735952001cfe7359520004fd735952001cfc735952006e7f53595200067d5359520006bf4359520006bd435952032cff7259520006ef725952006eef525952006eec5259520004ff7159520014fe7159520014fc715952006e7f515952018cff7059520006fb70595201ad7e761952006e7e76195201ac7e76195200067e64195200067c641952006d7f73195200057d73195200067f63195200067e63195200067d63195200067c63195200073f43195200073d43195203276f72195203276d72195203276c72195203267f62195200076f42195200076c42195200076f32195200076e32195200076d32195200076c32195200057d71195200067e61195200067c61195200076e21195200076c21195203267f60195203277a30195200077930195203a77b20195203276e20195203276c20195203277820195203277a1019520024fe76d91200067f65d91200067c65d9120066be64d912004dee72d912000ded72d9120067af42d912002cfe75d9120004fd75d912002cfc75d9120004ff73d912001cfe73d9120004fd73d912001cfc73d91200067f53d91200067d53d9120066bf43d9120006bd43d912004cf
  | 11 => 0x26def75547203576f655472008f6e65547200076d65547203576c6554720005ef7454720085ee7454720085ec745472008f6f54547203d76e54547200076d545472008f6c54547203cdef735472007dee73547203cded735472007dec735472008f6f53547203c76e53547203c76d535472008f6c53547203c7af43547203c7ad4354720135ef715472008fe751547200776e51547200776c5154720077e4515472011def705472000dee705472000dec705472011eed605472011f6f505472011f6e505472011f6d505472011f6c505472011fe710547200076f76547203576e76547200076d76547203576c76547200076f74547203d76e74547200076d74547203d76c74547203576f64547203d76e64547200076d64547203576c64547203cf6f73547203cd6f73547203c76e73547203cf6d73547203cd6d73547203c76c73547203576f63547203c76e63547203c76d63547203576c63547203c76f43547203c72f43547203c76e43547203c76d43547203c72d43547203c76c43547200776f715472008f6771547200776f61547200776e61547200776d61547200776c61547200776f41547200776e41547200776c41547200776f31547200776e31547200776d31547200776c315472011f6f705472011f6e705472011f6d705472011f6c705472011f6f405472011f6e405472011f6d405472011f6c405472011f6f305472011f6e305472011f6d305472011f6c305472011f6f105472011f67105472011f6e105472011f6d105472011f6c1054720005ef765072004dee7650720005ed765072004dec7650720005ef755072008dee7550720005ed755072008dec7550720255ef7450720087ae6450720007ad64507203bdef735072007dee73507203bded735072007dec73507203b76f53507203b76d5350720087af43507203b7ad435072024def71507200776f51507200776d5150720087e74150720077ae4150720077ac4150720077e44150720105ef705072000dee705072000dec7050720106ed6050720107af4050720107ad4050720107e7105072002cfe76d952006e7e65d952004dee72d952000ded72d952006f6f52d9520024fe74d9520004fd74d9520024fc74d952006e7f54d95200067e54d952006e7c54d9520004ff73d952001cfe73d9520004fd73d952001cfc73d952006e7f53d95200067e53d95200067d53d952006e7c53d9520006bf43d9520006bd43d952004cfe72d952000cfd72d95201aeed72d952000ced72d952004cfc72d952006e7f52d952006eef52d952006eec52d9520014fe71d9520004fd71d9520014fc71d952006e7f51d95200067e51d952006e7c51d952004cff70d952004cfd70d95201ae7f50d95201ae7d50d95203257e76d952002c7e76d95200067e64d95200067c64d95200057f73d
  | 12 => 0xe7359720005ed735972007dec735972008f6f53597200076d5359720007af4359720007ad4359720005ef7159720075ee7159720075ec715972008f6f515972018def705972000dee705972000dec705972018eed605972018f6f505972018f6d505972004def7659320005ef755932008dee755932008dec755932004def745932004faf6459320086ee645932004eec645932004fac6459320007af5459320087ac5459320005ef735932007dee7359320005ed735932007dec73593200076f53593200076d5359320087af4359320007ad4359320005ef7159320075ee7159320075ec715932004eef6159320087af415932014def705932000dee705932000dec705932014eed605932014faf405932014fad4059320005ef765532004dee7655320005ed765532004dec765532030def75553204076f65553204076c6555320305ef745532008faf54553200876e54553200876c5455320087ac54553203fdef735532007dee73553203fded735532007dec735532008f6f53553203f76d5355320087af43553203f7ad4355320005ef7155320075ee7155320075ec715532008f6f51553201cdef705532000dee70553201cded705532000dec70553201ceed60553201cf6f50553201cf6d50553201cfaf40553201cfad405532004def7658720005ef755872008dee755872008dec7558720005ef7458720085ee7458720085ec745872004eef6458720006ed6458720005ef735872007dee7358720005ed735872007dec735872004eef6358720006ed63587200076f53587200076d5358720007af4358720007ad435872004def715872004fe76158720076ee615872004eec615872004fe46158720077e63158720007e531587200c5ef705872000dee705872000dec70587200c6ed60587200c7e710587200c7e5105872008f6f76d472035f6e76d472008f6d76d472035f6c76d472008f6f74d472008f6e74d472008f6d74d472008f6c74d472035f6f64d47203ef6e64d47200076d64d472035f6c64d472008f6f73d472008d6f73d472008f6e73d472008f6d73d47203e56d73d472008f6c73d472035f6f63d47203df6e63d47203df6d63d472035f6c63d47203df6f43d47203df2f43d47203df6e43d47203df6d43d47203df2d43d47203df6c43d47200776f61d47200776e61d47200776d61d47200776c61d47200776f41d47200776e41d47200776c41d47200776f31d47200776e31d47200776d31d47200776c31d47201376f70d47201376e70d47201376d70d47201376c70d47201376f40d47201376e40d47201376d40d47201376c40d47201376f30d47201376e30d47201376d30d47201376c30d47201376f10d47201376e10d47201376d10d47201376c10d4720005ef765472004dee7654720005ed765472004dec7654720
  | 13 => 0x87200067d5358720006bf4358720006bd435872000cfe7258720014fd725872000cfc725872004eec725872000cec725872004eee4258720006ed425872004eee3258720006ed325872004ef77158720076f63158720006f5315872004ef72158720076ee215872004eec215872004ef4215872004eef205872004efa205872004ef920587200c6f7105872002e7f76d472035e7e76d472008e7d76d472002e7c76d472035e7f64d47201467e64d47200067d64d472035e7c64d472008d7f73d47203e57d73d472035e7f63d472013e7e63d47203de7d63d472035e7c63d47203df3f43d47203df3d43d472008f6f72d472035f6e72d472008f6d72d472035f6c72d47201367e62d47203ef6f42d472035f6e42d47200076d42d472035f6c42d47203df6f32d472035f6e32d47203df6d32d472035f6c32d47200767f61d47200167e61d47200767d61d47200167c61d47200776f21d47200776e21d47200776c21d47201376e20d47201377a20d47201376c20d4720004ff7654720004fd765472004cfc76547203567f655472002e7e65547200067d655472002e7c6554720005ef725472004dee725472004dec725472008f6f52547203576e52547200076d52547203576c52547200067f76547203567e76547200067d76547203567c76547203567f645472012e7e64547200067d64547203567c64547203cd7f73547203cd7d73547203567f63547201267e63547203c67d63547203567c63547203c73f43547203c73d43547200076f72547203576e72547200076d72547203576c725472011e7e62547203d76f42547203576e42547200076d42547203576c42547203c76f32547203576e32547203c76d32547203576c325472008f7771547200767f61547200167e61547200767d61547200167c61547200776f21547200776e21547200776c215472011f6e205472011f7a205472011f6c205472011f771054720004ff7650720004fd765072004cfc7650720026be6450720006bd6450720005ef725072004dee725072004dec7250720087af4250720007ad425072004def764872041eef7648720005ef754872008dee7548720005ed754872008dec7548720005ef7448720085ee7448720005ed7448720085ec744872004eef6448720006ed6448720415ef734872007dee7348720415ed734872007dec734872004eef634872040eed634872040f6f534872040f6d534872040faf434872040fad434872004fe77148720016ee6148720016ec61487200776f51487200776d5148720077e6314872040fe5314872000dee704872000dec704872004def765972004def755972004f6f655972008eee655972004eec655972004f6c6559720005ef7459720085ee7459720085ec74597200076e545972008f6c5459720005ef735972007de
  | 14 => 0xdbc7650540016bc765054000cbc7650540005bf7550540005bd75505400073f65505400073c655054045dbf735054045dbd7350540456bf6350540456bd63505404573f53505404573d5350540006bf6250540025bf7150540027b77150540007b76150540016be6150540016bc6150540097b461505400973f51505400973d5150540007bb705054000dbe705054000dbc7050540107b87050540026bf6050540027bb6050540107b71050540107ba1050540004fe76c8540004fd76c854004cfc76c85400067f65c85400fe7c65c854004eee62c8540004ff7648540004fe7648540004fc76485400067f65485400de7c654854004e7f7559720004ff7459720024fe7459720024fc74597200067e545972008e7c5459720004ff735972001cfe7359720004fd735972001cfc735972008e7f53597200067d5359720006bf4359720006bd435972004cff725972000cfe725972004cfd725972000cfc725972004eec725972000cec725972008eef525972004e7e525972004e7c525972004eec5259720004ff7159720014fe7159720014fc715972008e7f515972018e7f505972018e7d505972004eef2059720004ff755932002cfe755932002cfc755932004ebf7459320006bf5459320086bc5459320004ff735932001cfe7359320004fd735932001cfc73593200067f53593200067d5359320086bf4359320006bd435932004cff725932000cfe725932004cfd725932000cfc725932004eec725932000cec7259320086ef425932004ebe425932004ebc425932004eec4259320004ff7159320014fe7159320014fc7159320086bf415932004eef215932014ebf405932014ebd405932004eef2059320004ff765532004cfe7655320004fd765532004cfc76553204067f655532002e7c6555320005ef725532004dee725532004dec72553204076e52553204076c525532004def7654b2044eef7654b2004f6f7554b2002eee6554b2004eec6554b20005ef7454b20085ee7454b20085ec7454b20445ef7354b2007dee7354b20445ed7354b2007dec7354b2008f6f5354b2043f6d5354b2043faf4354b2043fad4354b20005ef7154b20075ee7154b20075ec7154b2008f6f5154b2000dee7054b2000dec7054b2004def7650b20436ef7650b20005ef7550b2008dee7550b20005ed7550b2008dec7550b2004faf7450b20026ee6450b2004eec6450b2042def7350b2007dee7350b2042ded7350b2007dec7350b204276f5350b204276d5350b20087af4350b20427ad4350b20005ef7150b20075ee7150b20075ec7150b20087af4150b2000dee7050b2000dec7050b20004ff755872002cfe755872002cfc7558720004ff7458720024fe7458720024fc7458720004ff735872001cfe7358720004fd735872001cfc73587200067f535
  | 15 => 0xc5255140005bf71551400a73f5155140007bb705514000dbe705514000dbc70551401cfb87055140026bf6055140027bb60551401cf3f50551401cf3d50551401cfba105514004cfe76d89400067f65d89400067c65d894002cfe75d8940004fd75d894002cfc75d894000cfd74d8940004ff73d894001cfe73d8940004fd73d894001cfc73d89400067f53d89400067d53d8940496bf43d8940006bd43d8940496ee42d8940496ed42d8940014fe71d8940004fd71d8940014fc71d8940496bf41d8940024fd70d8940316ef20d8940316fa10d89400a57e75989400057d75989400067f65989400067c6598940006ef6298940065f970989400057f75589400a57c75589400067f65589400067c6558940085fb70589400067f65189400067c651894004eee6218940006ed6218940004fe7694940004fd769494004cfc76949400067f659494002e7c65949400073d5494940004ff7654940004fe7654940004fc76549400067f655494002e7c6554940014fe76d85400067f65d85400067c65d8540096f661d85400067f75d854002cfe75d8540004fd75d854002cfc75d85400067c75d854000cfd74d8540014fc74d8540004ff73d854001cfe73d8540004fd73d854001cfc73d85400067f53d85400067d53d854048ebf43d8540006bd43d854004cfe72d8540004fd72d8540096f641d854048ef541d8540024fd70d854024eef20d854024eed20d854024ef710d85400057f75585400a57c75585400067f65585400067c6558540096f46158540485fb705854002e7f76d45400057e76d45400a67e76d45400047e76d45400a67d76d45400a57c76d454002e7c76d454002c7c76d45401473e74d45400a73d74d45401367f64d45400a57f73d454047d7d73d45404767f63d454013e7e63d45404767d63d454013e7c63d45401473f43d45404773d43d45400067f62d454035e7c62d454011d7d71d45400967f61d45400167e61d45400167c61d45400973f41d45401367f60d45401477b40d45401373e40d45401373c40d45401377840d45401377a10d4540004ff7654540004fe7654540004fc76545400067f655454002e7e65545400067d655454002e7c6554540025be745454012f3e54545400073d54545400067f76545400057e76545400067e76545400047e76545400067d76545400057c76545400067c76545400047c765454012f3e74545400073d745454011e7f645454046d7f735454046d7d73545404667f63545401267e63545404667d63545401267c635454012f3f43545404673d43545400067f62545403567c62545401357f71545400a77771545400967f61545400167e61545400167c61545400973f415454011e7f605454012f7b405454011f3e405454011f3c405454011f78405454011f77105454011f7a1054540
  | 16 => 0x9540004fd72d95400a67f52d95400a67c52d9540014fe71d9540004fd71d9540014fc71d95400a67f51d95400067e51d95400a67c51d9540024ff70d9540024fd70d954030e7f50d954030e7d50d954030eef20d954030eed20d95404ad7e76d954002c7e76d954030f3f74d954030f3c74d95400057f73d95400057d73d95400067f63d95400067e63d95400067d63d95400067c63d95404c73f43d95400073d43d95400057d71d95400067e61d95400067c61d95404c73f41d95404c77b40d954030f3e40d954030f3c40d954030f7840d954030f6f20d954030f6d20d954030f7a10d954030e7f74d95404c67e74d954030e7d74d954030e7c74d95400067f73d95400047f73d95400067e73d95400067d73d95400047d73d95400067c73d95404c67f43d95404c63f43d95404c67e43d95404c67d43d95400063d43d95404c67c43d95400067f72d95400067e72d95400067d72d95400067c72d95404c67f42d95404c67e42d95404c67d42d95404c67c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400047d71d95400067c71d95404c67f41d95404c67e41d95404c67d41d95404c67c41d95400067f31d95400067e31d95400067d31d95400067c31d95400067e21d95400067c21d954030e7f70d954030e7e70d954030e7d70d954030e7c70d954030e7f40d954030e7e40d954030e7c40d954030e7f30d954030e7e30d954030e7d30d954030e7c30d954030e7f20d954030e6f20d954030e7e20d954030e7d20d954030e6d20d954030e7c20d954030e7f10d954030e7e10d954030e7d10d954030e7c10d954002cff76595400a67c6559540305bf74595404bdfb705954030cff75595400067f7559540304ff7459540006bf7459540004ff735954001cfe7359540004fd735954001cfc73595400a67f53595400067d53595400bebf4359540006bd4359540004ff725954004cfc7259540004ff7159540014fe7159540014fc71595400a67f51595401ccff7059540006fb705954030d7e76195400a67e761954030c7e76195404b73e74195404af3d74195404ae7f64195400a57f73195400a75e73195400057d73195400a75d73195400055d73195400067f63195400067e63195400067d63195400067c63195404b73f43195400073d43195400057d71195400067e61195400067c61195404b73f41195404ae7f60195404b77b40195404af3e40195404af3c40195404af7840195404af6f20195404af6d20195404af7a101954000dbc765514002ebc765514000cbc7655140025bf75551400273f75551400073f655514002ebe655514002ebc65551400a73c65551404a5bf73551404a5bd735514049ebf635514049ebd63551400a73f535514049f3d53551400a73
  | 17 => 0x4fd71d9150014fc71d915050e7f51d9150006be41d91500bebc41d915002cfd70d9150306bf40d9150306ef20d9150306ed20d91500bebc6459150505fb705915000d7c76551500267c765515000c7c765515002d7f745515002f3f74551500073f64551500267e64551500267c64551500bf3c64551504fd7f73551504fd7d73551504f67f63551504f67d63551500bf3f43551504f73d43551504067c62551500057f71551500077b705515000d7e705515000d7c70551501cf78705515002e7f605515002f7b60551501cf3f405515004cfe76d895000cfd75d8950024fe74d8950004fd74d8950024fc74d8950004ff73d895001cfe73d8950004fd73d895001cfc73d89504ee7f53d89500067d53d8950006bf43d8950006bd43d89504eeee52d89504eeed52d8950014fe71d8950004fd71d8950014fc71d89504ee7f51d895002cfd70d895032eef20d89501ae7f65989500bdbe7498950005bd7498950006ef629895006df9709895008dfb70589503267f651895004eee6218950006ed6218950004fe7690950004fd769095004cfc7690950004ff7650950004fe7650950004fc7650950006bf6450950026bc6450950014fe76d85500aef661d85501367f75d855000cfd75d8550014fc75d85500147c75d8550024fe74d8550004fd74d8550024fc74d85504e67f54d85500067d54d8550004ff73d855001cfe73d8550004fd73d855001cfc73d85504e67f53d85500067d53d8550006bf43d8550006bd43d855004cfe72d8550004fd72d85501367f51d85500aef651d85504e6f551d855002cfd70d85501367e50d85501367c50d8550136ef20d8550136ed20d8550136f710d8550005bf74585500bdbc74585500aef461585504ddfb705855011e7e765455000d7c76545500167c765455000c7c76545500057f74545500067f645455012e7e645455012e7c64545504d57f73545504d57d73545504ce7f63545501267e63545504ce7d63545501267c63545504cf3f43545504cf3d43545500067f62545503567c625455002d7f715455002f7771545500ae7f61545500077761545500067761545500167e61545500167c61545500af7461545500077b705455000d7e705455000d7c705455011f78705455002e7f605455002f7b605455011f771054550004ff7650550004fe7650550004fc765055002d7e75505500057d7550550004fe76c8550004fd76c855004cfc76c8550004ff7648550004fe7648550004fc764855002cfe76d95400a67e65d95401ccfd75d954000cff74d9540024fe74d954000cfd74d9540024fc74d95404c67f54d95404c67d54d9540004ff73d954001cfe73d9540004fd73d954001cfc73d95400a67f53d95400067e53d95400067d53d95400a67c53d95404c6bf43d9540006bd43d954004cfe72d
  | 18 => 0xf43d9121006bd43d9121014fd72d91210d6bf42d912104cff71d912104cfd71d91211767f51d91211767d51d9121176bf41d9121176bd41d912100cfe70d9121004fd70d912100cfc70d9121006be40d91210d6bc40d91210d6bc645912153def7259121004ff755912102cfe755912102cfc7559121174ff7459121006bf7459121004ff735912101cfe7359121004fd735912101cfc73591210067f53591210067d53591210d6bf4359121006bd435912153cff7259121006ef7259121154ff7159121006f771591211567f51591211567d5159121004ff705912100cfe705912100cfc7059121004ff7655121004fe7655121004fd7655121004fc76551210067f655512102e7c6555121006bf6455121026bc645512102cff7654921014fe7654921194fd7654921014fc76549210067f655492102e7c6554921005f77154921015f4715492104fe42154921535ee769092104eee7690921155ed7490921026ee6490921026ec649092104def739092152ded73909215276f53909215276d53909210d7af4390921527ad4390921015ee7190921015ec719092104eef619092104fe761909211776f51909211776d5190921177e63190921527e53190921005ed7090921024ff7650921014fe7650921154fd7650921014fc7650921006bf6450921026bc645092104fac4250921005f77150921015f47150921015ec7650921026ec7650921014ec765092104def745092104faf7450921007af6450921026ee6450921026ec64509210d7ac645092151def735092151ded73509215176f53509215176d53509210d7af4350921517ad4350921007e77150921015ee7150921015ec7150921157e4715092104eef615092104fe761509211576f51509211576d5150921157af4150921157ad4150921157e63150921517e53150921005ef705092100cfe76d81210c6fa60d812102cfe75d8121004fd75d812102cfc75d8121024fe74d8121004fd74d8121024fc74d8121004ff73d812101cfe73d8121004fd73d812101cfc73d81210067f53d81210067d53d8121006bf43d8121006bd43d8121076ef72d8121014fd72d812100cfc72d8121006ee42d8121006ed42d8121006ee32d8121006ed32d812104cfd71d812100cfc71d81210767f51d81210767d51d8121076f631d8121006f531d8121076ee21d8121076ec21d81210c6fa20d81210c6fa10d81210057f75581210dd7c7558121005bf74581210d5bc7458121005df73581210cddc73581210c6f86058121024fe76d91500bebe64d915000cfd75d9150024fc75d91500bebe54d915050ebd54d9150004ff73d915001cfe73d9150004fd73d915001cfc73d915050e7f53d91500067d53d91500bebf43d9150006bd43d915004cfe72d9150004fd72d91500bebf42d9150014fe71d9150
  | 19 => 0x9721024fc7459721004ff735972101cfe7359721004fd735972101cfc73597210fe7f53597210067d5359721006bf4359721006bd4359721014fe7259721014fc725972104e7e525972104e7c52597211967f51597211967d5159721004ff705972100cfe705972100cfc705972104eef2059721004ff755932102cfe755932102cfc755932104ebf7459321004ff735932101cfe7359321004fd735932101cfc73593210067f53593210067d53593210f6bf4359321006bd4359321014fe7259321014fc725932104ebe425932104ebc42593211567f51593211567d5159321156bf4159321156bd4159321004ff705932100cfe705932100cfc705932104eef2059321004ff765532104cfe7655321004fd765532104cfc76553214067f655532102e7c655532104def7650b2155eef7650b2104faf7450b2104faf6450b21026ee6450b2104eec6450b2104fac6450b21555ef7350b21555ed7350b2154f6f5350b2154f6d5350b210f7af4350b2154fad4350b21015ee7150b21015ec7150b211576f5150b211576d5150b21157af4150b21157ad4150b21005ef7050b21004ff75583210067f75583210047f755832102cfe755832102cfc75583210067c755832102c7c7558321004ff7458321024fe7458321024fc7458321004ff735832101cfe7358321004fd735832101cfc73583210067f53583210067d5358321006bf4358321006bd4358321014fe725832104eee725832100cfd7258321014fc725832104eee4258321006ed425832104eee3258321006ed325832105e7f515832105e7d515832105eee215832104eec215832104efb70583210e6fa3058321006f9305832104eef205832104efb205832104eeb205832104ef820583210e6fa105832102cfe76d95210de7e65d9521024fe74d9521004fd74d9521024fc74d95210de7f54d9521004ff73d952101cfe73d9521004fd73d952101cfc73d95210de7f53d95210067d53d9521006bf43d9521006bd43d9521014fd72d95210de7f52d952104cff71d952104cfd71d95211b67f51d95211b67d51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210de7c50d95210de7c6559521545ef72595211b4ff75595210067f7559521004ff7459521024fe7459521024fc7459521004ff735952101cfe7359521004fd735952101cfc73595210de7f53595210067d5359521006bf4359521006bd4359521544ff7259521006ef72595213567e52595213567c5259521194ff7159521006f771595211967f51595211967d5159521004ff705952100cfe705952100cfc7059521024fe76d91210d6be64d912102cfe75d9121004fd75d912102cfc75d91210d6be54d9121004ff73d912101cfe73d9121004fd73d912101cfc73d91210067f53d91210067d53d91210d6b
  | 20 => 0x67f63581510067d63581510073f43581510073d43581510057f72581513557c725815100777715815104777615815111d7f70581510077b605815111e7e605815111e7c605815111f78605815111f77105815102cfe76d95411167e65d95411d4fd75d9541014ff74d9541014fd74d954158e7f54d954158e7d54d9541004ff73d954101cfe73d9541004fd73d954101cfc73d95411167f53d95410067d53d954158ebf43d9541006bd43d954104cfe72d9541004fd72d9541024ff71d9541024fd71d95415867f51d95415867d51d954100cfe70d9541004fd70d954100cfc70d95410067e50d95411167c50d954158ebf40d9541586f710d954102cff76595411167c655954157dbf7459541145f77159541584ff75595410067f755954157cff7459541006bf745954112e7e545954112e7c5459541004ff735954101cfe7359541004fd735954101cfc73595411167f53595410067d535954112ebf4359541006bd4359541004ff725954104cfc72595411167c52595411d4ff7159541006f771595411d67f51595411d67d5159541004ff705954100cfe705954100cfc70595411167f505954112ebf40595411d6f7105954104cfe76d89411157e75d89410057d75d894102cfe75d89410067e75d894102c7e75d8941004fd75d89410067d75d89410047d75d894102cfc75d8941014fd74d8941004ff73d894101cfe73d8941004fd73d894101cfc73d89410067f53d89410067d53d8941576bf43d8941006bd43d8941576ee42d8941576ed42d8941006ef32d8941006ec32d8941024fd71d894153e7f51d894153e7d51d894153eef21d894100cfe70d8941004fd70d894100cfc70d8941006ef62989410d5f571989410f5f7715894104eee6218941006ed6218941004fe7694941004fd769494104cfc769494102e7e65949410067d6594941025be7494941005bd7494941004ff7654941004fe7654941004fc7654941015bc765094104ebc7650941014bc765094156dbf735094156dbd7350941566bf6350941566bd63509415673f53509415673d5350941025bf7250941027af7250941007af625094104ebe625094104ebc6250941007ac6250941007b77150941015be7150941015bc7150941157b47150941026bf6150941027b761509411573f51509411573d5150941005bf7050941157b7105094100cfe76d8141106fa60d814102cfe75d8141004fd75d814102cfc75d8141014fd74d814100cfc74d8141004ff73d814101cfe73d8141004fd73d814101cfc73d81410067f53d81410067d53d8141486bf43d8141006bd43d814104cfe72d8141004fd72d8141024fd71d814125e7f51d814125e7d51d8141106fa40d8141106fa10d81410057f75581411157c7558141106f8605814104e7f7559721004ff7459721024fe745
  | 21 => 0xd63989510073f43989510073d43989515b57e72989513567f62989510076f62989511b57d71989513577571989510057571989511b67f61989510ff77619895111d7e70989510057d709895111d7c70989510067e60989510067c60989511b77710989510057f745895112d7e745895112d7c74589510057f73589511257e73589510057d73589511257c73589510067f63589510067d63589510073f43589510073d43589510076f62589513567e62589511957f71589510077771589510057771589510df7761589510057f705895111d7e705895111d7c70589511977710589515457e761895112d7e74189510057d74189513557c74189510067f64189510067d64189513557f73189511257e73189510057d73189513557c73189510067f63189510067d63189510073f43189510073d43189511b57e72189513567f62189513576e62189513567d62189510076d62189510076f32189513576c321895102d7f71189510157e711895102d7d71189510157c71189515b67f61189515bf7761189515b76f21189515b76d211895111d7e70189510057d701895111d7c70189510067e60189510067c60189515b77710189513557f76909510057e76909510057d76909513557c76909511557d74909513557f73909511257e73909515ad7d73909513557c73909515a67f63909515a67d639095112f3f43909515a73d43909515357e72909513573f429095112f6f42909513576c42909511757f71909510157e71909511757d71909510157c71909511767f61909511877761909511776f219095111d7e70909510057d709095111d7c70909511777710909510057f76509510057e76509510057d76509510057c76509511757f745095159d7f73509511257e735095159d7d73509511257c73509515967f63509515967d635095112f3f43509515973d435095153d7f725095112f6f42509513573e42509513573c425095112f6c42509511557f71509510157e71509510157c71509511567f61509511677761509511573f41509510057f705095111d7e705095111d7c705095115777105095111d7e76d815112d7e74d81510057d74d815112d7c74d81510067f64d81510067d64d81510057f73d81511257e73d81510057d73d81511257c73d81510067f63d81510067d63d81510073f43d81510073d43d81513557e72d81510057d72d815102d7f71d81514df7771d81510157e71d815102d7d71d81510157c71d81512767f61d81514df7761d815111e7e60d815111f7a60d815111e7c60d815111f7710d815111f7a10d81512777910d81510057f74581510073f74581510053f745815112d7e745815112d7c74581510073c745815112d3c74581510067f64581510067d64581510057f73581511257e73581510057d73581511257c7358151
  | 22 => 0x495111d7e70949510057d709495111d7c70949511ae7e60949511ae7c60949511b77710949510157c765495104e7c76549510147c76549510057f745495112d7e745495112d7c74549515e57f73549511257e73549515e57d73549511257c73549515de7f63549515de7d63549515df3f43549515df3d435495102d7f725495102f6f72549510076f625495104e7e625495104e7c62549510076c62549510077771549510157e71549510157c715495119774715495102e7f615495102f7761549510057f705495111d7e705495111d7c7054951197771054951004fe7690951004fd769095104cfc76909513557f759095102d7e75909510057d759095102d7c7590951004ff7650951004fe7650951004fc76509510057f755095102d7e75509510057d755095102d7c755095100cfe76d815102d7e75d81510157d75d815111efa60d815111f7a50d8151014fd75d815111e7d75d81510147d75d815100cfc75d8151024fe74d8151004fd74d8151024fc74d81514de7f54d81510067d54d8151004ff73d815101cfe73d8151004fd73d815101cfc73d81514de7f53d81510067d53d8151006bf43d8151006bd43d815104cfe72d8151004fd72d815102cfd71d815111e7e50d815111efa50d815111e7c50d815111efa10d8151005bf745815112dbc745815111ef860581515d57e76d915112e7e64d915112f3e64d915112e3e64d915112e7c64d91510057f73d91511257e73d91510057d73d91511257c73d91510067f63d91510067d63d915112f3f43d91510073d43d91513557e72d91510057d72d915102d7f71d91510157e71d915102d7d71d91510157c71d915157e7f61d91515cf7761d915157f3f41d915157f3d41d915111d7e70d91510057d70d915111d7c70d91510073e40d915112f3c40d915157f7710d91515857f765915157d7f74591510073f645915112e7e645915112e7c645915112f3c645915112e3c64591510057f73591511257e73591510057d73591511257c73591510067f63591510067d635915112f3f43591510073d43591510057f72591513557c72591511d57f71591510077771591510057771591511177761591510057f705915111d7e705915111d7c705915112f3f40591511d777105915112d7e74d89510057d74d895112d7c74d89510057f73d89511257e73d89510057d73d89511257c73d89510067f63d89510067d63d89510073f43d89510073d43d89510076f32d89510076c32d895102d7f71d895102d7d71d89515467f61d89515c77761d89515476f21d89515476d21d895111d7e70d89510057d70d895111d7c70d89515477710d895112d7e74989510057d74989513557c74989510067f64989510067d64989513557f73989511257e73989510057d73989513557c73989510067f63989510067
  | 23 => 0x2d7e7690b511857d7690b5102d7c7690b511473e6490b511873d6490b5135d7f7390b5113d7e7390b5162d7d7390b5135d7c7390b511867f6390b516267d6390b511473f4390b516273d4390b515357e7290b5135f3f4290b511476f4290b5135f6c4290b511757f7190b510157e7190b511757d7190b510157c7190b511776f2190b511357e7090b510057d7090b511357c7090b511657f7650b5102d7e7650b511657d7650b5102d7c7650b5161d7f7350b5113d7e7350b5161d7d7350b5113d7c7350b511667f6350b516167d6350b511473f4350b516173d4350b5153d7f7250b511476f4250b5135f3e4250b5135f3c4250b511476c4250b511557f7150b510157e7150b510157c7150b511573f4150b510057f7050b511357e7050b511357c7050b51024fe76d915102d7e75d91510157d75d915112ebe64d915112f3e54d9151014fd75d915157e7d75d91510147d75d915112e7e54d915112ebe54d915112e3e54d91515cebd54d915112e7c54d9151004ff73d915101cfe73d9151004fd73d915101cfc73d91515ce7f53d91510067d53d915112ebf43d9151006bd43d915104cfe72d9151004fd72d91515ce7c52d915102cfd71d915157ebf41d915100cfe70d9151004fd70d915100cfc70d91515ce7f50d9151006be40d915112ebc40d915157ef710d915112ebc645915160df771591510157c76551510267c76551510147c765515102d7f745515102f3f74551510073f64551510267e64551510267c645515112f3c64551510263c64551516057f73551511257e73551516057d73551511257c73551515fe7f63551515fe7d635515112f3f43551515ff3d43551510057f72551513557c72551514067c62551510077771551510157e71551510157c71551511d774715515102e7f615515102f7761551510057f705515111d7e705515111d7c705515112f3f40551511d777105515104cfe76d8951014fd75d89515467d75d8951024fe74d8951004fd74d8951024fc74d8951004ff73d895101cfe73d8951004fd73d895101cfc73d89515c67f53d89510067d53d8951006bf43d8951006bd43d89515c6ee52d89515c6ed52d89513567c52d8951006ef32d8951006ec32d895102cfd71d8951546ef21d895100cfe70d8951004fd70d895100cfc70d8951006ef62989510ddf571989510fdf7715895104eee6218951006ed62189510157e76949511b67e76949510147e769495112d7e74949510057d74949513557c74949510067f64949513557f73949511257e73949515f57d73949513557c73949515ee7f63949515ee7d63949515ef3f43949515ef3d439495102d7e729495102f6e72949513567f62949510076f62949513576c62949510157e71949511b77671949513577571949510157c719495102e7f619495102f77619
  | 24 => 0xc71596421867f5159642004ff705964200cfe705964200cfc70596420067e50596421867c505964204eef2059642004ff755864202cfe755864202cfc7558642004ff735864201cfe7358642004fd735864201cfc73586420067f53586420067d53586420d6bf4358642006bd435864204cfe725864204cfc725864204ebf425864204ebd425864204ef77158642176f64158642176f63158642006f5315864204ef7215864204ef42158642004ff705864200cfe705864200cfc705864204eef2058642004ff755824202cfe755824202cfc7558242004ff735824201cfe7358242004fd735824201cfc73582420067f53582420067d5358242066bf4358242006bd435824204cfe725824204eee725824204cfc7258242066ef425824204eec4258242004ff7158242014fe7158242014fc715824204eef215824204efb7058242006fb505824216ef8505824216efa405824216efa3058242006f9305824204eef205824204efb205824204eeb205824204ef8205824216efa105824202cfe76d95421667e65d954204cff74d954204cfd74d95421c67f54d95421c67d54d9542004ff73d954201cfe73d9542004fd73d954201cfc73d95421667f53d95420067d53d95421c6bf43d9542006bd43d9542024fd72d95421667f52d9542014fe71d9542004fd71d9542014fc71d95421667f51d954200cfe70d9542004fd70d954200cfc70d95420067e50d95421667c50d95421667c6559542635ef72595421c4ff75595420067f75595421a4ff7459542006bf7459542004ff735954201cfe7359542004fd735954201cfc73595421667f53595420067d53595421a6bf4359542006bd4359542634ff7259542006ef72595424067e52595424067c5259542004ff7159542014fe7159542014fc71595421667f5159542004ff705954200cfe705954200cfc705954202cff7654942024fe76549421a4fd7654942024fc76549420067f655494202e7c6554942005bf7454942025bc7454942014fe76d8542156f661d854202cfe75d8542004fd75d854202cfc75d854204cfd74d8542004ff73d854201cfe73d8542004fd73d854201cfc73d85420067f53d85420067d53d85420f6bf43d8542006bd43d8542024fd72d8542156f641d8542156f621d854200cfe70d8542004fd70d854200cfc70d8542156f4615854200cfe76d814214efa60d814202cfe75d8142004fd75d814202cfc75d814204cfd74d8142004ff73d814201cfe73d8142004fd73d814201cfc73d81420067f53d81420067d53d8142086bf43d8142006bd43d8142086ef72d8142024fd72d8142086ef42d8142086ec42d8142014fe71d8142004fd71d8142014fc71d8142086bf41d814214efa40d814214efa20d81420057f75581421657c755814214ef8605814235d7f7690b51
  | 25 => 0x52521c73f435525264f3d43552524057f72552520076f72552524076c725525202e7e625525202f6e62552520057f71552521ad7e70552521ad7c70552521c73f40552520067d7558652004ff7458652024fe7458652024fc74586520de7f54586520067d5458652004ff735865201cfe7358652004fd735865201cfc73586520de7f53586520067d5358652006bf4358652006bd435865204cfe725865204cfc725865204e7f525865204e7d525865204ef771586521b67f51586521b6f651586521b6f63158652006f5315865204ef7215865204ef42158652004ff705865200cfe705865200cfc70586520067e50586520de7c505865204eef2058652004ff7458252024fe7458252024fc745825206e7f54582520067d5458252004ff735825201cfe7358252004fd735825201cfc735825206e7f53582520067d5358252006bf4358252006bd435825204cfe725825204eee725825204cfc725825206eef525825204eec5258252004ff7158252014fe7158252014fc715825206e7f515825204efb70582521ae7e50582521aefa50582521ae7c5058252006fb40582521aef840582521aefa3058252006f9305825204eef205825204efb205825204eeb205825204ef820582521aefa1058252024fe76d91521a6be64d915204cfd75d91521a6be54d9152186bd54d9152004ff73d915201cfe73d9152004fd73d915201cfc73d91521867f53d91520067d53d91521a6bf43d9152006bd43d915202cfd72d91526467e52d91526467c52d91521a6bf42d9152014fe71d9152004fd71d9152014fc71d91521867f51d915200cfe70d9152004fd70d915200cfc70d91521a6bc645915263def7259152014fe76d8552196f661d855235e7f75d855204cfd75d8552024fe74d8552004fd74d8552024fc74d8552004ff73d855201cfe73d8552004fd73d855201cfc73d85520fe7f53d85520067d53d8552006bf43d8552006bd43d855202cfd72d855235e7e52d855235e7c52d85521967f51d8552196f651d8552196f621d855200cfe70d8552004fd70d855200cfc70d8552196f4615855200cfe76d815218efa60d815204cfd75d8152024fe74d8152004fd74d8152024fc74d8152004ff73d815201cfe73d8152004fd73d815201cfc73d815208e7f53d81520067d53d8152006bf43d8152006bd43d815208eef72d815202cfd72d815208eef52d815208eec52d8152014fe71d8152004fd71d8152014fc71d815208e7f51d815218efa50d815218efa20d815218ef8605815204e7f75596421a67f54596421a67d5459642004ff735964201cfe7359642004fd735964201cfc73596421867f53596420067d53596421a6bf4359642006bd435964204cfe725964204cfc725964204e7e525964204e7c5259642004ff7159642014fe7159642014f
  | 26 => 0x1400803d000800003e0090018000010000000000002a00d00000140020030000000000008001803c0040020018038008006000803c0f20000010038032003000002801c0030038000000000000000801600a00b001c000066010002001a003000017000800d001802c0000000020050000001003000001a00601e80140000100038000000002003000800000e0090064000000000000000a0020018004010004000000000a002000001400400800280040100010000050006009002800000000000380880060050008004004000009808400000200000080040090040000002000001820400000200480500040000000004004000000803000200d000000000000000300040020000058004008009000001c012007000000000800b0008034000003006800800000000600f4008000001000000800301f0004028000001801802a006000800001a01704cfe76d8954024fd75d89546367d75d895402cfd74d8954004ff73d895401cfe73d8954004fd73d895401cfc73d895463e7f53d89540067d53d8954636bf43d8954006bd43d895463eee52d89544067c52d8954636ee42d8954014fe71d8954004fd71d8954014fc71d895463e7f51d895400cfe70d8954004fd70d895400cfc70d8954006ef62989541cdfa7098954005f9709895404eee6218954006ed6218954014fe76d85541d6f661d85541467f75d8554024fd75d855402cfd74d85541467e54d85541467c54d8554004ff73d855401cfe73d8554004fd73d855401cfc73d855460e7f53d85540067d53d8554146bf43d8554006bd43d855404cfe72d8554004fd72d855460e7c52d85541d67f51d85541d6f651d85541d6f641d855400cfe70d8554004fd70d855400cfc70d855460e7f50d8554146bf40d85541d6f4615855400cfe76d81541cefa60d8154024fd75d815402cfd74d8154004ff73d815401cfe73d8154004fd73d815401cfc73d81545067f53d81540067d53d81544bebf43d8154006bd43d815404cfe72d8154004fd72d8154014fe71d8154004fd71d8154014fc71d81545067f51d81541cefa50d81541cefa40d81541cefa20d81541cef8605815404ebf74592521c6be5459252166bd5459252004ff735925201cfe7359252004fd735925201cfc73592521667f53592520067d53592521c6bf4359252006bd435925204cfe725925204cfc725925204ebe425925204ebc4259252004ff7159252014fe7159252014fc71592521667f51592521c6bf4159252004ff705925200cfe705925200cfc7059252006be40592521c6bc405925204eef20592524057f76552520267f76552520247f765525202d7f745525202f3f74552520267e64552524073e64552520263e64552524073d64552520267c64552526557f73552526557d73552524067f635525264e7d635
  | 27 => 0x2000001003800c000000000000000100d00b800a006000003000000e001006800000e002800400a000001000400a00e0040030010000000000c01e004006800c00800b00100000060030008010040006007000000000c00200840000000020030004000000000000000300300140020040000000010010006002800e00000000000100010018010008016002000800000600000000120020128064000001000000c002000000001400200000000000060050000004006000001804000e00401600080220060000018028004001000001c0000000018002006007800c01a001001000c0020000010018000000000000801401200180000000060360004000000002002c00a0020158004028016000001000000300000480000010008000000009000801401800e002001400801e00e80040020030080008000002002001001400000c000402600900000200280050010004002000000001c000000000800402600000d80000020010020000002003001801400800000580080000000000094000007005001c000000000801400000300000000040020038004000000000000000c001000003008400c0000000000000008000000600c00d800000c002005006400000a00a80340080060030000006003000000400202b0000000004002003802c01e002000000c00000300000000000010000050004000000000005400c000001c000022005003802e0210038004018005002802c000003002800c012005000000000201a003000000a016001000400400b00080200020010000000024000000801001e003006001c002004000801c0020020000028000001000801000200400080000020090000014002000000000000200001180240040000000000000006003002800a000000000000a001001002c00000000200140020250040000012029009000401000b014801800a00c02e001c012017000002800600000080000000030028000010008014020001a000000000401a01900380280020130000018008000000000402600a0000020000000001801400a001002801c00c003000800001e002003803c004002003000400000400a801401800100280000040060028000000006001002400a00300100140060070038004038000001802400200f000000000600f01a801000a000001000001c0030000034002011000805400e01b00b0018000001004804c0080060000000006006001006c00800000300a000a00200900080040000020000000003001001404200200100b4010013001800000000c000000401200c0000028008015000000800400c00a0004000001014800402c00200000a8052012003809c00400100400000060040010000012005002001400000000680380020010000014000004003803800000d00000040bc001001001800400002a
  | 28 => 0x1000401e00400200280000040018020008004000000000000000280080000090178000004006002800802000000000500000010000024010003000000c01000400a000400605500300380040090010004020002006802800e007002800400000200f801000200d0010060010000005000401800a001000c0040120010008002000008000800a000000001400600b000000400e001000000000000000200000060010008024002033007802c00400300000000020000238014000000001807402600600000600260030048004004006006005c03c000006800c018000001800c000003005800c00200e0010000000006000003c000004001801c00c001000802c00800400100080080070020000018008000800000e001003802c0280000018008000008001800005200a004800c0060020060024000007000003c00400f008001400000800d8008000003000000000400000e00080020050000034052003000800c002003001000000c002020000c00000800400000040290000004018001004000800e000005800000001300500100080020050004000001000800800000700680340040010018018016003000802800200000e804400400000880000520040050000000003000800000600d002800000a00d000001c00a00d00b000c000027001002401001e008800000800000000040000000000000032000000803c00600c000000000200a0008010008000017800002000800000000000000000000004001001000001600700100000260000000068016000003007c0000000030008000000000800000000d00480c8000001000003400600000780000000050000008002000000000403c000001800400c01c001809c00000001a0048018005000000c0040050008000002000000800400000300300040020020010010012000000000000c00100f801c01e0000000078000003000803800a003000801802600d005800800000200b000001e00500100240040090188038010003002804400400400000080040000010000032001001000000a00b00080300220550008004008001000001000200700000080000000040000004003001800002200000200040000040018000000001000002c00a011000000400600600f80100040040028044018001000008005e002002800400400e001800c0000020050000000011000808802a0090000000000004015803c00000e00000000e4003007001c00e01100800000020000000000012020004800000002d0040014040001001800000000700080440160040018058004000000004401000100400000000060010014002003000801c05c001016000000000c002000c0000050008018000000000000400e006001000400200a0010004018000000800400e00100080000160000080004002005000000000
  | 29 => 0xb33385404324c0013c0f2a3e088da2c74a653db84672730ac9000000013dc00031240001b54f841f9825612ac000225000021f000021c80000000000056861c00001042b14cd60b640bb42e4a9700e071a0000eff000000000002133b1c6fa36a48d813f0588072492913189521e9d03b45740a72d400002c482910b347261b7c00011280002b646771234c7939a081900000000000000251c19f3818000000031b000000000006fc06b800028f8abd00009e41df4b1600005b9399c5a300004182da00003cdccba3204b8a22a46ca42c4000000000012c109a000000043e82f0316c0000000ec536c000000001410000444000046c00002e32480fe12894000355800032b4000390c0002c9c00000008ff3f000000000a4e000000000009e5000038102180000000000088c9ff0000000105d08b0f14a4b0000bff3f8c0d23010cfc1d18c1c34dc0002a940003bf00001030e5a1420d2f163cd553e840002d5c00035f11260000bc93d281b6000000017000000001141267893c2908d2933bc09316303c02544af7000077b3f78f72133d07629f8391358851a40dd1c70c4c013079cdc12174a523ac44ba387c1ac20e02a63ba8b053d6d1a31f208ce424cd4732908b9207103c44784980e3c12b0abc60a1569008215901a3f0d1c122a8ef0250c1781970c95102467e3c5ccd834d0261137032f1e3c56107583313d687ba10910183e2c1030f184892054878369c8951c8862e2ef4c8a14a0a2210842b238980c607289ee1fe822c19d0ea42a38fa617903ca2f581f50924abf1a606a41f4c5cd3ecc8c61a287ac1208ea718e8b010f604ae4270a243918e330d00a9146780001544f480000000419400014e0b3028f447a04c804a3fbc7d729a44620c64a59166882e2a28fcb2eb480b2b3866b34c839800007612d04a1908041db070c40b019c06f2e18366361c79e1e5c6c703a833a3e584292fd0764000057c02680002e6000024c424e3c000000000d07000112e0bb400035b40003c10c22090880e0d74ce43d0cc7735288c2000000000007714174c430000000000000021dc6e305cc00023a0f9f00000ab1b00bb4217068d0c400e202f4f22396c00000003fb3620e130000bfe0000d06194c000000000000011051db80000000000000000000007f62cbc82a110d0413bf81ed0b9cd4908d8e2915107484718fe701583833b480000000000000000000006520000a303cacaef095ccbe354ce1417e8cf62b5c19b2134a4c2234000459c2a90000232367c2de17051ab00000db000007329b519f2ba09fe0000f6b158c00100e003c01200100780140020010000000002000003800c0060050008010004018002003c000009000801801e0010018000008000000001001c000001802800000e00180040020000070000000002000800800200600
  | 30 => 0xbc0003f18d350c3872d385c169000000015b40000500000000000041cc6d20048000000000000006ad04d446843742cc1b6893e12b466a3478dc41af4e4d000098d08f84410000f650000b871c4d1023b88fe0336516a296018f402cda8303d12310d002e18ec4c709f4f9e3dec46522bcad621fc74c0be47091c0ccb416cc5201d685b71bb49ef02083c32b94b4643443a701fce763b5c92833b89712a1065d4000cb5384040a31048360000db5099088625f400001005be00000003d08b5f2eb021204c411d27106590dbc7ab0000896000014c2238166151cffa073423d3f449e62ff00001abcd141fd10d31b100000794f55089057f08780001e7c43d00000df41b1083257400030c4b7e0000f9c332c16a000015d15885bb2ef000024f47844138c7f0508fdf43c4463000869a0e8cf0f0000c4d21486d00000fce2e90df536883e12240c0a12d4c1825cc14642e0e98000116c1658f5606ed08f3280991000000000003841b38e4a0a5c2d713a10f60000b6d1b5c49031940000cfc13f3694f02009847608580970354a6f0600fab049d0e400009ae1c7cf6c230ccdc46b8be922849a930744b10b205e232c443243f4c352cacdd51a4ca4434b089700011b846545dd238ce090d4cc7c1e0478a1330ef30da0ce72e40f54464c00026e02a7416c0d90000c4638e000027d836211982f6250103e2a584730bdc4f5364c8cc0000f1900000000000000000051b171c00000002b9000000000003f200000000000a7f0000da0000109233080002c3c0aa308c00036280001b747fc28fc08438ec76d0000000000000043b4000000000000000003a3c000188000041d0e53000107b000000038a0000443c8ac000000046980003584000000000030200001a5878b3ce05782d106a01c645f9288000000000000f3c0000000fe82a1cbdd12000001c38b1424cc43905ec43b36b823435c40c837bc6442fb00003d1438a00000000000d01000000046c042d0000c2c051c000152519009949eb000075000003730000a60451c0002b0c21a45c41bc0c8cca14500c5900011603ed4d6e36f45d130ed161012c3773ab85a92c8d14421d023a18908894624b0b17a0b40315510b26bc83302d90b644d02603e5cfa73cf490a3730a2b11f44d743b8c4f017cd1b15b0b9f3e1c6890e8032e2c251b718c913c31b0ea21fdc7e510342410e38eed24241c70fe4ba22c009f1103c5582b204aa1cf88bf4358fbb2454a2125305df3b291c009a47254048be7154875617bca10424010201b4d441f8c66f35d4231401ca9d07f8b481040412081c0b502b830339dce9c408c90612e40ec0270afb159491c144497735a402034400f6281d18b0e6c5013e28ef71ec518526fd0770a30ffe1e2110438142c20000b8011582e410c000000000002eccbd23778b5e2354a7
  | 31 => 0xa309780a21dfc56725981d53fcc16b36ac84f1384cd513b4a0e37c485a25d40bc1b0caa42bd901438b8163026002933a46bf1bc40002cd020800001292a782463b3068e0b3d17b0bec2fd24dce242d540001d947bc43f9081000000036c800011b4351143c14f46a802432dc8f00310ddc3ff09f30e9012636687b720942c31184c7118fc62628342932f20dfa2370ba8000089f000000033680800000009128c1090dec000000000000007450000e5821810a40eb882f0000000270ca2a034400014b8cb9000000000000003158a1f0000e86318c000000049c00006710f3000010dc0003df51780000834000091b05388c10bf8e9f30040003f4cb9900000000000000000033621e40331344137199052d05d00003a20fed00bca610ad40fd27f517f3d710bb00000003495155020400025204702b28c33204c92d0044b5d2f18000000019c01b83b504300000874402000118f0000000372908a45340162ae40001fd4e350000f140000934068c1600c54000222896100005c40d94cc100003160000c2d0000aa111bd1b51c187fb1354edd1ac4d8d3878f8630082b136140001d60e23226104b21c4b523a109b929b8c5d2d8455911f012a331d18a472107e3f64000351491239011111fe4c7204ccec937945d433e08fb235c6b909008b238c860033fc9011d887ea1f584c5355047908882380400c5c46a4e940a181a0088514c09f0d231760f982534bd3183c1a617f42843a142041178a350de055c2f5cd72471464b3c14c6607c8e4b104cd113aa0ac009a8ae12ce82bf10f0a950000e6e0000acd101400131ec0002f389961bc80c02f64c7500000000000fa43ea909409e06222bd0c870000e190000ebe06448413ea455500001ee03c42752ca50c33d19139000107d2d28481394800020108c72b04e4c260c9e723c50db1ddc4d92d3044e028cbf12be405141401643cb01ea169c5290e350ca11ac4012870b4313c43b31d08000312876a0a6905202bc266223c57312800870714b2c1ed400000000000cc8fe91cf097023e83120af011346f86bc089ca8627f045d25d880614f04e90000000463825208f0c7600009df15980000000000000000022c49880000000216449b07e42ea465cc4e1b6099b156c0000d3000000000000c9846906280002de4000000002519984fd0000a49030c17e000000024e0d4e3430000000091621ed03941180002728a981ad4aad000084a000008c17b000000000003d8c00a426ccab1ac0138000000002e442709d00000ca408f2b108ec1c748a42420000000041d13940003988dc30000000364400029d8c2f37b80000f445eb00003b200007f02a64bdb08a400046bc5b1000049e43187ca2800ed60bc47802c787630fc03ad46444a53e5400005280002df413603c034810680003454532000086516
  | 32 => 0x9fcfb60000d42000000000008cf43b03f8355c1571c1519d00c0a700108cec29cc89234f8b0e086c739043c8001dd84993fd87e0438443f41091290b6c6e52b4cef12b51131151848c087c0ed05dc01a34d82812f840000000000000000002d04de1ae822a000000000007d80c20f2f2d586a144240002f340004560de635a00de1a9d09e36ccc930000cdb0000c2524eca8f11540003ee02dd08ec0000efc0001b14000000000024788fd0ec04363474000184000022c0cfd0000ff925700000ff400000f07003d6400016b80000000ef4397c49530ac66e4128ae20000cb83740dcb2c448ab3d60a291be41a7317869d05346ff239c86e1cc46652cdd0a9000090c273c8881f0026d0ea0a7231685a52c611880000dcf1f840001894904286cede0aac9942e70a362208942000035f1b909c20000c7e00000001f1cb0802380000000400162445800005f100000000d5025506cc751000062d0000ee400003900360000000116200000000000bfd00000002f2cf88000000000000001d24aa20aec8dd0000a9009ec48a236cc973344e343f080000ae030c1d6400036ec1393b2c18800009f9000039700000000000e8700000001bd05fc2904045000089b41c07e42e140001a30d5e00000001f705d6000010d0e7800042bc017026cb3c24886112c94a672c4d1823a681532a8cecf42180282f4428800005f31d5cb621cbc0001ec908443049f832190c810445d3212c0003121115411d103353c1ba3999174404c112455c00032b0b3d0000f8d0b00c3e130867003c8000054446a000000033a8987000078d2f1400013980000f791501eb882324fcd78150400000000001bcc00026c000000000000a540000c880003d407a642b887536f0a1e34640003dbc53a36e4fdd0a2889c1915002404000000000000f40272205c0001de0000000003b13bc8541c9c6db00000000b68b321bc00000470dba1e8c25140ace7210180003b40000000010700003463cfc0000e890992ba86ae02a0e69174837e42240003e6c00030d00004634868000000028b800020281b43b38d3005c00001e38bf335fcbb708240000000aa72580b2608c0a2826f8f66050d0573df80001f144bb1b9c00030244c12bf43fc10a8c9c2008d3304200001b3050d40c87b90000e830000b2d16a8dfb0fdcd74114caed20ad0c207b029643a0ec11bb8000171400020dc000000065a316000006d4acb210000000006040828e9d03fd12c1a080000b9400042580001d787da01a01a912980000000850000011503acfee062c6152fc8000218c181065070104389d21c60dfc00002171f34ccf16e8ae4147c6691fc8d6b36dca4f17c03ce3f2119b01682f42be0c4c1df8e0a3c407c11a049240000c8d41e0488000030f38e874f3edcc450898eb90d9d11035d8ab3102024815a09
  | 33 => 0x1900000000d249b3183873b0000c8043100000fe8c271978000000036000000000000ed11cfd03809c00000000000395c000253cae02990e592bb0e0106f8b350694a512ec0a8c04f03bd2fbc5a6410c1f83abc6f500000000000ae31dcc05214f900d435cd0d3c946c134ac30a2bd4d0a0b5067b33881961adcb6e37a0e92461800032f00001ba49bc3690de236f8000401458500000000000f99115c0850000000000054e2ae02e0000000026d80002bfce8b25100a40000fb0262c0b135985e1000104c000117525e44200000a04417caf219c8062000000006250d232d86b836a80e50000a6a41bcc3200000001558ee81a88d8116500003064000000000000000002bc085e45200000000000000064e2444782463017d36408d415287c9295c0000b240000000cf73d380003b7c000326901134686f8377c6de274402228e800816c8a3212bcc0d0e580f8099cab7116c7721db069b00003b82124000000038b00000000000c60353504546846022e84f0900000752dd0283001434e32a8b240000000429c000328800000000002ce0c6f0dc43522c3400015f44e414640003ca0446000000000001503d7903a1cd507915748a822740000e2400012882ac29782333f2434345909a4000011700010c004600000001097335ce8923b80d43910e651daca450ea4330271858e0dd4baa26b07dd30385fe217cfcc2020d3d0ce4e7a000069700006ac3ea077c182c4140000276363c494145428000000001c4859535405db338c9900000f700c340001144cf04368b201e14167027c61836c41a83d7d15e33e800037b4000000000000003e924b0d8e0000cbb40cc54339d000041c898527851b21e7428731a908708bc98a0f2c00007a031120b052c000101f3acc6230000a1a000034d27a40002ab846e09ccd0f2aa40001718f122f98f010d60fba01e01da0000d0e32a06ec2e510d40c08ead199c2e935682152c28ef63500e21064ca0f2d9c8612c5c734196017a000000001902540cf0f321c7022e04f40e73fe103d0000000275c00000004c822f4c8c23840004208000362c386000000000551704288000382075200000000000eb526d09990000c822d8c0000000c16185c8cb27d0d9d4214f0e1470f6d2144000211c96c00006d40000000000000001e80003d88c50000000036d800011fcaa646ec4ea17b454b209c31c00011281ef464918f913a03cc2c73874df20000e1818cce6a092c0001a78e7c00000442f040960000475000000020c812500000001e94000206c08800005cf40c45543eb456f0c7c744315c9ce00010fc2aa06f700f4b720380000010400002b049f297000000011363d34000000000027005b6366c4f32d8080d39acd971460472014042e0338df031f4d770000fd532fc0003b8000021f457515c0bae13109720
  | 34 => 0x2040cc43848ff000009db16450f839b4076322099545a47a1125d1730074ed317251a205d811e1fcc8ba00000a932950d8055060340d4cf93fec92605942b344746bb3aad0e61d985271ca4b0322d4b0235f83db1ff80001804a5400000e10000b15000000000ac7cf3938740205892f000113324400003394b4f38b0000403c37a1a5032834609b72b4448e00e8000232000017c800026b40ca04185794018d9800000002638d123600d7b37805262e580001bd80001ba04f21458000165c000000000c0000271000042f19a0000181c00025f0f5d248459f0a0800000008f20000fb10000ee545442f800010eb2f5400040880000000c983654e632a500000340000213800000011ba460000000000001b4cbf500000001de400033f8423006020231ac00000000002bcc0000000f610000adc2d450ef4434000000109d29b0000011c000000000014949a7000000000009460000aab2764183196ca2c37d800045b80002ba44dd000113e12846430fb400036b0426000036d1b800001e58c142cfca0831b80000000e5d1c20000347c049226400000010250000fc11fa0cc81bf42e60f2056a2af82d32ac102d252424c2954d090ce09b23a80000300c0000000a4d00007d2000000013400003fac000129c00000005d7000117616f00000000f473bf44ce46f46283300e9507106fb01ec00000011b30000043000000004d0e361fa48f92f091b10000502257c8b445b511642f800000002452d70f1d1858dd93a8473044500003a3800034587753ddc0000c50d3a0000d1c000069900007bf265c6080000c380000f204200adb431495400010a1000000029740002030a11001c4d440040001cb8000075ceba0bf0fae0000d842288b1c27240000bc8a0145e87160000000160d14e0000000155cb49000051d25accf200000b800002c400001e61ecc8bb42cce253b98eda46611631ca8b8843d4f4c284800000000fc04402a235e802d000005504c11990000000000039f00000d746b4000139c6c816e01af4694341000063700009c51f0d0e22630c64000000039f864a375c0000a6048409a02be0000000042cd0800000001fb800024640001d1cc063e502b4453c88100003ab39c40000000bf600000be00005330db80000000ce03a780000d682b028086a817203343fa8f060000fb42cf89d40c94b1f190085825a815e0800b532abc4504668059239002a383843e432cfda35901e12f691200000000000050641a80fa2d900000f08000368c05c267c5b03f1c0003bac6500000de426d40002a6879514d80001a8c35510e00001c8029900000000000c1700011833c8c0001c505da2efc9b146f042b0b60fcd2280cf43d04036242cc74000000016f420f0000000237812e0b2cff109340001708791000000000000000000d0b19440000fd4
  | 35 => 0x8801e1cf3b23f05772b1c73610e8514307864744fc5e5018474d107c8872b082770b3918725ec0e4181400037b037600001f04490fe600003b71cf41d21eb5026000025a18f40320a803440001142058400000000000000805000110c3a44c69065400015b906d000000013e4ccd000000006c49a808fc26c187c5693da00004070000000000000000fe34c43d73ee40000228d591114000080cb4e000035739fc9ba2ee0478361829c083811b0000000391c8240fa8000305400035e400009f8000064039228145a1130c4592068ef50000000000000037dccfb0000a68000000046b00000000e0000005c300003b6304400014bc00000b095535a8c2103ec37d2760ff50000bd00000b06160434f00005210000ba0132504d41540000d710c7016c00022f8000281841622b801c2e34c4721d8010452895a022c9a11c2c00042d0bd42e04c291c78c3c0ea8ec42648e15306c5cb034c9dd00d01b83d2cae625d00d62c88bd8208016f00000001688000077400037208a604b0d5c0000b5a235800030d80000000000298c000000000018a400013803ff191800012140002dd49dc01f4c0700000003b6c0003f70fd228e0f733e94b820ed08e01348000000033b0000b040a34d60296c00037fd040166c0002074d480000f1800008d94120a620000000000050a42607ce39e4ea5000109144c901b2495154436500a07880003e68867389d1191f088182ebc6193594dda28dcaeb033ca74086469100e405e0fcce2b3c287542c6c9c72f8cd521038156359c15f3718a0914306fe041400000010e00000ced000093a0308b4230a05234030e1601c43953831149033425f3d48ada418cab100004b34484e56241c00039ccf670000000000024a41ac99800001d400000000000ad825fc958307c00000c40000000000000000000007922af0000000000000002f527886a900000000c845480d840002f700003ca496f2188d7d0000f901f44000000000000010a63f5c9781440bcf00009453aec61d0001028000000000000003914957408400019304a92e0c2902dec000297c00000000000000000000058d395040700009f72bb86aa0aa8864096c74e07a4f0810ccdc9000063c0f8cba619810e50c7800038e4b950000ebc289cd5f17d48e93c589360ab8df8405c9fb0120ef22a2c4b72f809630d2803e44d49301ef901e16b0edc18d4fe2214c67f2154ba91ba8fd42de875b3c788440ee4f3141808e23e4c5f635b06e2337882906483e737382583e383df1950c701180d2728611921ea0d822fa000027e8539074cb84081436a16609da0450000000024713d00000cacf3401a853d12180003b8c17200000370e4c00041e8c3f3090843048009404bc8b7179c121470cf1b01a4448089511b0618dbf078c8c01ccc13e00004bf00000000000c51
  | 36 => 0xe23f8eb8000094b392058018300000b408a707d87f1234d113003445a00001113624dd300009ea3b5434744040001414eaa0000aba000048f2fe4000270495300007cc08502b721200003250bcc000072100009e039c068f28e401f00006b2245c4fb0404364000c0f509bc44c3bb00003530b210b4511c302cb4b381c220411007223441f308dc4d6290cdd221080540554ca934909cd173822800010b22ac80a100000000000000121c00000000000000000138ce8d33240790000a9b41500003c84d9e21a832d37d08f602c030b0764b8e1368dc7142400007301622858a662da508d12d0b73161c06512f8f270018bab0c60e963e0047b2078a8003a00bf0000000456c0002398a533be400041a0c050ccc000414c2e20000000000000046d00001ce0e4235c086f09ac783106439c16409800fd8dd12cb86ab0bb0bfa0520a8513ac65f05a000011f8f2d00005a41a1020c2dac000000115f358c885068482d000045f145cc1a3d4400014d49a0000041544dc00006ac00018b10bc00005ee441c8390000ddd1d8000010700000e149863d240c1000117e06341980e08cd32e9cb661a004833c7c54c1e64ea33e30be40564f783278c8f2da871019f0f151bac5e91a20d4b1b24d2e447c8f428983e405b45823af46091af8cb006784ee167465732b87b83844503216c9680eb022b0d141871e40afa000112b45dcdea0a2cf57285014b00d4a782fb51304354a50256412d000101d000090d00008c400000000f982a1000096506b4cdf19040002928eb4000098400003003de872c24c88ea3c351180f501d11ffce3f282c00e23d502c0dac77002242a30370bde41c4000112cacc02dc92a2fec00038700000000fb22f8891d00003d52db10bd348809007dceee19e070d1f9cb7100001243b0010a207c00002540003b6400034b4000154ca0c00011943ba440333148c90d6425905e4301020c743439c9394158b5400010fb0000000000086d41788260000f1a40d8000000000000000002f00e2a295800025049f243a80003bbc723433851200002d23258c2629ac00f0000fd60000f112dd800017dd0e30000464000094e0c9c914351800002743243c903bc1f887931eecca326686cf000000007f006600010aa0b145e6428c0001258e203a6c00003a400019880004144caf27a07890f48905136d156000000000007af45f0004000113b000000000004930000b19000000001d0000468000040a41520000c0c0000fa000000000000ce12f1000000007b430dc0004658732272035e350cb931a2c6613670f1c13fcbf80000dad000000027540000000e6f17402d63d90be50f7032c27405d9000055e0e1c61432c83bb284c8840c18b8c14fc0001ea8d033d00c2a1d547ed203c3883944aac461057e26acbc7269906100003e00000807267
  | 37 => 0x840ee291c956208800000005b400002c1240000000007a220fcdb43560000173000021b000022f0477141cf603ffcdc5164c83c35bcb0c30e8c6d1a1c72420502c629009693924cf128f01d0181839d0001015327c4df1e9090e2fdc239324097e0000000000013a0000a9c0000e041b2ced8220c00034140002048eb221c000019d4ab41274acf0bb85303f10cd005b883b3ef04490ca82ba23dc0000c1462100003202a0800019d8d96240cde100003fe2cc4292000020600000000000000000000000010620464f2e46e400028b462b07d0beb00000000a945a029e80b200004402d34bb20770000000038c1a7c2bd00009d637e40002b9c000000091a43780000000e5e00011220c7400009e84b2065c000322ca79215c26e00003e22e94cd420e8f89340800010c4000000000000000000001067000000011486ef0f740000000000427c95000000000000574356c0001fe009126f4ec3000034241fccf536500003e8c00017fcd9910b0ba319cc03f01f825001b0337007872b33749ec08441cf10881c829f07d42a808eb048c000314c00003d00004599179000071b000088b425400000000002fb836900003e518e4e3e19e48450000dfe44b4000380c00000000001e710cd0000f6a000000042c11683a08ff71f2cb07134cf4445680cc4420fbe3150fc53da4000090c0000000ad223cca8915ec1840664c5f330cc423c308c5011916f06885f41ca0e1b41f0efa0cf8ce8000000045ac52406fc00000011c40000e5c0000f3a46d852b0000e2d34e0e0f2578000332879400003703a4058a0974d132bf00002e5cb5939b000019f49a525e854232142630000a2f0000deb12b00003a5ca75441876714dc6cd363009929f4ffd000076934845922fa81b931cc52238f49812ed800001dcab6038cc9d1fbc2e100000002ed4afe2df08281618000437070200003c126ec0000000000326c2530cd452a000014400006b600000a6032c79b0c682eb288d0a51678b7800002d51fb000000000001b64eb00368de33b18f741dd04a83e0c3f421cc48b000000040bc1f1000000000000dd072c0003f287d50bbc00000000000000000193c0000000d2618340004400eb621f80000000000000088c000112a000062f000017c2a3400000000000a7459900006b40570abb2b7c2ad01745ca408000000001a40dd10752a04f3500003ee39d4a920130000000000047084cb44f477a360c3ba07ec00006740000000c891b186270e648010000ccc00010f40000000248c0c7409018e12d800008b400000010d0008cb9b00000000000de91400dc2002c0f91a70f3642ac0000d584423a647d93dd8e7845483be3048b33000070c46a0000000103f0dfcee1000000014ec00000000000000000000000046900000000000416019a2f7c000000000000005d
  | 38 => 0x25883e8175400042b0f4f274cc2e17a8c202eec0000000a7100002103bec0001f7879a000000030c02dc23410641c3c830000000046047df16110a840a83943ebd04f1d2c7a91290a03063011f329cb1a01ac51e27b49cb0000e020000e64319cb9a0488000000000031100003c980000000000015c17100010f93b9c0000000fac373461a000000002e80000000000107800000000000000d7300000002ee40000000798000000000000000870a15320c000000101906c8000000011a3298fdb0c244f80000000247cb772918000000108c296904940244fa2e44d390000ff20000dc042fc5720278e501a940002d6c447383455f42e80003be00000000bbe0b7c1b03b505b5000000042b4918106d0cf1cdcb453a290041a40bca445d15331005762d6005811c480945947152ce456443c04921150cf32118000000000023bcc9100009e338f04f60f581fd15e8000469d06941710df0000cc60000d28154096d0970474321101607788b80f110ff0d8c69514d0b7020445f80280a83243d12f138844f3dd4c7827d4e55400ce9305d442822d80003e44b650000f3016fc000304cea624086480000e6102b4000000089a18490cc2f0d112259073a051435b3398eb723e04fe193450e0f2475f26887fd263c1ff3980b6f3e3c28e44380001f1800018c07eb16a059c0f646d63148f3342d4ad00000f9209e41ce43a4ea92a4cb8919b42f3000009234f0000449c7d000011250d2cf073fb09f02cec0000000fd000000001ec0000318839a2cd90302920d3b239463607e8000000095b35448d222cc8cd3e146e100004ca000098207bc00021e80000a90000056c00006140000000425393c7170790da63c0ce31000050b00010f7379c84c376c6c200000630398379423811630e506e1958b28249cec82e782ca0ec5027178cdd414100004280dd61b7029b2fc0bb100011460000655000000029dc00038bc786000000037cc0003f94c992ee800015ac0001c441c20000000178000002cc000237c0000db00000000000000115900000003e8914b00003d33a000c5190831718d03ec2dfc000000074a39ec54f00000000000a33368400040d058b0000b1019b0e3038dc00015c5066000075d00011721c10000000076f00003eb0bfc00000003500704000000033d093c00000003da3df061e3dc4060345cb9205248032624ad5244c8311c1c86b36e0a9f1a48b9d20f856022946b31f6c9de13b0f3e0f1ca0a41680c934fd0883c4c070348100e11710b73f6083d24b84b810d41eb08d4f812b744c032480ef184cecd177119c1b98ab51a98cbd05fcc4b39f4e8121983720fc41582e2c182388911a0a1510a0be8cd207000000000ceb000029e1e800001c28000304000039044bd28ec92b186c20d0134000198c5fb0000e8c1a140000a500000e
  | 39 => 0x32cc1aa37600000000000076115c1534c3d15140530000a31267400000000002e3caf10ebd0591d4c0140e940002d1cd2a21a400002348930294fe40a2424406dc00000001df0000000000000000001bd43cc000000000000004bc14c4f7f000044d26a8c7a25b800010104cd0000000000062a3400a1d00003ef00000003b0800016b40002b18d04228ca173574000144c04f0a7cd9209880000000000350475c18c400023b46833ef4f0b00004913ce43070000000082c000000074100000002ca80000000000000094a0df0000386867a18e000000000000a3d0f21b4400028d02a800000000000f5331a00001f10304000093500840003ab013b37f40000000f7912680f723280000e980271da02180f3400001f078c2aa8daf318499304a02e832388ad3fd000016ad1383cf01c620851450e002b63f3c68646fc0003afc000000000005b0a880780fbf0138ade382c96740b8000000000022787b6136083545f401b450c8913e740
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xb61811d52044001ec0e23aa40881939ad847548110327b1b08ea9022000f62411d52044001ec4623aa4088003d84c475481106973432aca9022000bab84595204407d75108b2a408809af8e05654811005df040ee89022000fa241dd120440015d70cba2408802eba2197448110005b5c2ae8902203fb68855d120440017c702ba2408802ef82057448110005b5c2ac8902203fb688559120441a3d50c8b224088126f8e05644811000575c32a89022000ae88655120440177c502aa24088176f8a1f714811005ef143ee29022001be286dc520440037c10db8a408802f789db714811005ef03b6e29022000f6385dc520440017c30bb8a4088003d82177148110007b1baee29022000f6075dc520440017c309b8a408800378dd37148110006f0ba6e29022000be383dc520440017c307b8a408800378dcf7148110006f0b9ee29022000f6353dc52044001ec2a7b8a4088003e8d0f7148110007d0a1ee29022000be28754520440017c10ea8a4088006f8a19514811000df0432a2902204dbe3855452044017ec70aa8a4088003d8dd551481101ffb13aaa29022000f6175545204407fec0eaa8a4088003d8d9551481101ffb032aa29022000be384545204407fec6a8a8a4088343d89515148110007b0aa2a2902203ff6054545204419f7c706a8a408833ef860d51481101ffb1a9aa290220cdf6253545204419bec2a6a8a40880ffd814d514811066fd1a1aa290220cdfa1435452044001ec70ea8a4088003d8a1d5148110005b143aa29022000f61875452044001ec10ea8a4088002d821d51481101ffb1c32a29022023f62865452044047ec30ca8a408808fd82195148110007b1bb2a2902200bf62765452044017ec2eca8a408802fd81d95148110007b1c22a290220d0f62845452044001ec308a8a4088343d82115148110007b1ba2a290220d0f62745452044001ec2e8a8a4088343d81d15148110007b1b22a290220d0f62645452044001ec2c8a8a4088343d8191514811067fb1c1aa290220cfb6383545204419bec506a8a408833fd860d514811067db0c1aa290220cdf6083545204419dec6e6a8a4088337d89cd5148110677b0b9aa290220cdf6073545204419bec6c6a8a4088337d898d514811066fb0b1aa290220cdf6063545204419bec686a8a4088337c8d0d514811066fb121aa290220cdf6143545204419be4286a8a4088337d810d5148110005f143a829022000be08750520440037c50ca0a4088006f82194148110005f1c2a829022000be1855052044001ec6eaa0a4088003d81d54148110255f1c2282902200bfa384505204407df44e8a0a4088003e85d14148110007d1b2282902203efa06450520441997c706a0a4088332f860d414811065fb1a9a8290220cbf6153505204407df4686a0a408832fe850d4148110
  | 1 => 0x307b82a2880035cdcf7054510006b8b9ee0a8a2000f3343dc15144001e6287b82a288002dc60b705451000c7a432eaa0a2098c7876dd5404412d8f0ec3aa8088002d660c7550110005b8c08eaa022045f32545454044001e62a8a8a80880035ce1d5150110005b943aa2a022000b70875454044001ae10ea8a808800b5c9d95150110016b83b2a2a022045f32845454044001e6308a8a808808f5cdd1515011011f99ba2a2a022000f3364545404408be60c8a8a8088362dce0d51501106c5b8c1aa2a0220d7d737354540441afae2e6a8a8088117ccd0d51501106b798a1aa2a022000d737254540440037610ea0a808800b6c21d415011000dd943282a022001bb0865054044009d610ca0a8088013acdd94150110016d93b282a022002db0765054044009d60eca0a8088002ece154150110005d8c2a82a022000f33755054044001e60eaa0a8088356ece0d41501106add8c1a82a0220d4db37350540441a9b62e6a0a808834fccd4d415011069f98a9a82a022000db37250540440eb8f0edbaa40881d31e1d87548110005b8c08ea9022000d70711d520440033d305ba240880036c90774481100147c432e890220009f087545204407fec6a4a8a4088003d89495148110007b0a92a2902203ff60525452044001ae70ea8a4088002dca1d5148110005b843aa29022000d708754520440012e10ea8a408800b5c9d95148110016b83b2a29022000d73745452044001ae2e8a8a408833edce0d514811067db8c1aa290220ced7373545204419dae2e6a8a4088337ccd0d514811066f98a1aa29022000f63825452044001ec504a8a4088003d86095148110007b0412a29022023d73725452044047ec6e4a8a4088003d8d895148110007b0312a290220d0f63425452044001ec484a8a4088003d85095148110687b0212a290220cdf6332545204419bec464a8a4088337d84c9514811066fb0192a29022000db174505204407df4684a0a4088003e8509414811004e743b6ec9022018be181dd920440177c103baa4088003d89477548110325b543eea9022075e6b76dd52044001cd0edbaa4088002dae0f7548110005b4c1eea9022000e6b63dd52044001cd2c7baa4088003cad0f754811000794a1eea9022000b6b81dd52044001ec703baa4088002da6077548110007b040eea9022000f6071dd5204406bcd6c3baa40880d7d8d877548110007b120eea9022000f6231dd52044001ec263baa4088002bae19754811005d74432ea9022000be3815d520440177c102baa40880d6daa1c7548110696b5438ea9022074e6b761d52044001cd0ec3aa40880fedae0c7548110005b4c18ea9022000e6b631d52044001cd2c63aa4088003cad0c754811000794a18ea902203fb6b811d5204407fec5023aa4088002da60475481101ffb0c08ea9022000
  | 2 => 0x774589100045ec1ee8b122000c3f51dd1624400187aa3ba2c4880032bc83745891000656906e8b122000c3f751d16244001878ea3a2c48800e37a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fc2ee6b122000c5c85dcd624400193f09b9ac4880032721373589100062fa8ee6b122000c5d51dcd624400199e41b9ac4880033348373589100043fc2ae6b12200587c855cd624400117f08b9ac4880122f21173589100046f438e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b12200087e87d4d624400b0f90fa9ac4880030fdd353589106ee1e3a6a6b122000c5f73d4d62440078b8e7a9ac4880021fa1d53589100043e43aa6b122000c3f7454d62441b9878e8a9ac48800317dcd535891001e2e39aa6b1220008be87d0d62440091790fa1ac4880030fdd743589106de1e3ae86b122000c9f73d0d6244007938e7a1ac4880022fa1d43589100045e43a86b122000c3f7550d62441b5878eaa1ac48800327dcd435891001e4e39a86b122000e1d5350d6244007998e7192c488003a350e325891001c7643a64b122003ccc734c962440071e90e98ac488003a550d31589100076299262b1220018fa87dc162440071f10e982c4880039654d30589100074ca1a60b122000ed1314c162440011df0eb10c48802f3a5c162189100147c432e1292200087f855d9524400117f08bb2a4880122f21176549100046fc1aeca9220038dc835d952440131dd053b48488012ab21162909100147c432e12122009cea625c242440010ff0abb284880161f21576509100045fc22eca1220008df835d942440071b906bb284880123b21d6250910014bac2ee8a8a2045d3654dd15144001b6481ba2a2880171d1da525451011db9404a4a8a2000b718094951440476e101ba2a288003cc90374545100053bc32e8a8a2023a74865d1514408ba68e8ba2a288002dce01745451011db8402e8a8a20d9e3664d9151440012ef0eb22a2880225d21d645451025db9c02c8a8a2023b7080dc951440474ed0d392a2880029d61a72545100fe3a3b4e4a8a2023b72809c951440016e301392a2880035c1c272545100053bc32e4a8a2023a74865c951440016e700b92a28808edc20172545105be3a3b0e4a8a2023b72801c951440016e300392a2880035c1c0725451005db8c04c4a8a20009778758951440112e90eb12a288002cde11625451022d9a422c4a8a2000b578358951440896a906b12a28803adce01625451000732b10c4a8a2023b728090951440016e301212a28808edca01425451011db943ee0a8a2023d7287dc151440056e50db82a28800adc21b705451011eb93b6e0a8a2023d7076dc151440016e309b82a2880035cdd37054510006b8ba6e0a8a2000b7383dc151440016e
  | 3 => 0x9b0240019e8865c76048001ad6cab8ec0900035a19571d8120004f5c1ae3b0240009e9835c76048001ad6a6b8ec0900035a54d71d8120006d5a1ae3b024000da9435c76048013bc702b8ec0901437818571d8120286f118ae3b024000de1315c760480033d70fb0ec0900267a21f61d8120006f0b8ec3b0240479eb8758760480016d70ab0ec09014eda21561d8120005d5c22c3b024052ba884587604800179706b0ec090146f220d61d8120005b5436a3b024053b6886d47604804dad4eda8ec09009b9a9db51d812029db5c1ea3b0240e4b6983d4760480d7ad6e7a8ec09038f5a5cf51d812071795a1ea3b0240e2f2943d4760480476d303a8ec0901af5adc751d81206f6b4b8ea3b024000b6a8654760480016d10ca8ec09008f5a9d951d812011f353b2a3b0240e1b6b8354760481c36d306a8ec0901ab5adcd51d8120706b4b9aa3b0240dff2b4354760481bfe5286a8ec09009adae0551d812029fb1c0aa3b02406ad6b7154760481bdad2e2a8ec0900030f5d254d95100053ac0ca9b2a2000a798095365440070ff0ea9eca88003175cd53d951001e4f39a87b2a2000c9d7350f6544001c3aa6a1eca880034d54774595100245f43ee8b2a20008bd83dd1654400187ea7ba2ca880030fd4774595100061ea8ee8b2a2000caf20dd1654400195a41ba2ca880030fdd474595100054ec18e8b2a200387c85dcd654400117f08b9aca880122f211735951000477c12e6b2a20098ec825cd65440070f90ea9aca880030fdd153595106e61e3a2a6b2a2000c5f7354d654400117d0fa1aca880122f21f43595100045f43a86b2a20008bc8750d654400793ce6a1aca88003275cd43595100070ea9a86b2a2000c3d75d53644400156b03aa6c88800e2fe1d43d911001e4f39a87b222000c9d7350f6444001c3aa6a1ec8880021fe1572d911002c3e42ae5b2220008df835cb64440071b906b96c8880161fa1f75591100043ec1eeab222000c3f43dd564440010ff03baac8880021f607755911000637906eab222000c6d20dd56444001878ebba2c88800e2f21373591100043fc2ae6b22200587c855cd64440011df04b9ac8880263b20973591100043f43ea6b22200587c87d4d64440010fd0ea9ac8880021f21d535911001c5e43a86b222000c3f7550d64441b5878eaa1ac88800327dcd43591100070ea9a86b22200087f855d9544400117f08bb2a8880121f21d65551100251e422caaa22003c9e7350f624400193ae6a1ec4880038754d43d89100074aa1a63b122000e59534c36244001d3286986c488003b44c530d8910006b4906eab122000da920dd16244001b9241b9ac4880161fa1f75589100043ec1eeab12200087f81dd562440010fb03baac4880031bc83755891000636906eab1220048be87dd1624400187eebba2c4880030f1d
  | 4 => 0x148001b5287b82c2900267a6077058520006f1b0ee0b0a4050de061dc161480a1ad6a3b82c2901435a5477058520286f118ee0b0a4000de131dc161480013d50e982c29002a7a21d3058520006b5baa60b0a40e6d68754c16148001b56e8982c2903976a1d13058520006e5b9a60b0a400adc8734c16148001d96c6982c290003d254d3058520007c4a1a60b0a4000fc1314c1614801b8dd0d3b6a2900025be0e76d4520004b6c1ceda8a4000d2f439db5148001a5a873b6a2900031bd8676d452000636b0ceda8a4000c6f609db5148001ad4613b6a2900035a4c276d4520006b5084eda8a4000d69109db51480012df0eb26a2900365b21d64d4520005b5c02c9a8a40009e980dd9514800135f08bb2a2900326b2117654520004e7c1aeca8a400a9cc835d951480013d700bb2a29002e5ba1f6554520006363b6caa8a400b96c8759551480016d700b2aa29002e5b61774545202ce972a6e8a8a400b96c875515148019a58e8aa2a290002dae01545452011db4402a8a8a4000b6980dd951480016cb033b2a2900025ba1a7654520004b7c1ceca8a400096d839d95148001a5e873b2a2900034b50e7654520004b6c0ceca8a4000d65819d951480018dec13b2a2900035a8c27654520006b4984eca8a4000d67109d95148001ad4213b2a29000359442765452000597c22eca8a4059b2c845d9514800169f06bb2a29015ed320d7654520005b3c0aeca8a4000b6b805d951480012dd0c3b2a2900031ba187654520004b7c18eca8a400096d831d951480018dcc63b2a2900031b18c765452000697a18eca8a4000d2d431d9514801b2df023b2a2900365b604765452000637b08eca8a4000c6d611d951480018dec03b2a2900035a8c07654520006b4980eca8a4000d67101d95148001ad4203b2a290003594407654520006b4880eca8a4059d2e74dd151480b3a58e8ba2a290002d9e057454520005b5c02e8a8a4023b68805d151480012df0eb22a2900025b21d6454520005b5c02c8a8a400d96e85dd941480012db0bbb282900027a6037650520004b7c2aeca0a400d96c855d9414800139f06bb2829002a7320d7650520004f5c02eca0a40009eb805d541480033d100baa8290002d9604655052005cd643ac8a0a4000bab8059141480c96d50db2ec0900d75a9db65d81201af353b6cbb024000b6b83d9760480016d307b2ec0901d75adcf65d8120006b4b9ecbb024000f2b43d976048001e5287b2ec090002da60765d812032cf5c3acbb024035b6a8619760480a7cd50c32ec0901935a9d865d8120327353b0cbb024053b6b8319760480016d30632ec0901d35adcc65d8120006b4b98cbb024000f2b431976048001e528632ec090002da60465d8120314f5c3ac9b024000b6b8559360480a76d10ab26c0900027ae1d54d812004cf443aa
  | 5 => 0x25be1574d852006cb642ae9b0a40009eb805d361480033d100ba6c29002e3b61f64d852000cf4406e7b0a400096f855cf614801b2d90ab9ec2900027ae0173d852000cf4402e7b0a400b8ed87d8f6148015998e6b1ec2900025ba1f53d852006cb643ea7b0a40f3d6b70d4f61481e5ad0e1a9ec2900025b21d53d852078eb5b82a7b0a40f0d687054f61481d1a58eba1ec2903bf6adc343d8520776d438687b0a40e7d2c7550f6148001b1ee6a1ec29002b631cd43d852000747b1a87b0a4000f0d5350f61481dbb56e0a1ec2903b36a1c143d852005d75436e1b0a4000d6b75dc36148001ad0ebb86c2900267aa1d30d852075cf443a61b0a40e6d68754c36148001b96e6986c29002b721cd30d852000765b1a61b0a4000f49534c36148001f1286986c2900365ba1f7558520004b6c1eeab0a4000d6a30dd56148001ad421baac2900025ba1f6558520006963a6cab0a4000d4c73d956148001cc8c3b2ac2900025ba1c6558520006963a0cab0a4000d4c73195614801935d0fba2c2900034bdd77458520006963aee8b0a4000d2f65dd16148001a58cbba2c2900026b60f745852000697a8ee8b0a4000d2d51dd16148001b5461ba2c2900036a843745852000697ba8e8b0a4000d2c751d16148019958e9b22c29002e3b21d645852005d7240ac8b0a40019e880dcd614801539d0fb9ac29000353dd77358520006a63aee6b0a4000d8f74dcd6148001b18e9b9ac29000353e177358520006a642ee6b0a4000d4f65dcd6148001a98cbb9ac29000363e137358520006c6426e6b0a4000d4f51dcd6148001a9aa3b9ac29000372e037358520006e4406e6b0a4000dca10dcd61480012df0ab9ac2900365b2157358520004d7c22e6b0a400c9ac845cd61480013d700b9ac29000353dd47358520006a63a8e6b0a4000d8f741cd6148001b18e839ac29002b331cf63585200076318ec6b0a400b8ec8758d6148015998e6b1ac2900025ba1f535852006cb643ea6b0a4000d2f74d4d61481d5a58e9a9ac29000353dcf5358520056a639ea6b0a400096e8754d61480012d90ea9ac2900034bdd1535852074e963a2a6b0a4000d4f7354d6148015a98e6a9ac2900026ba1f4358520064d643e86b0a4000d2f75d0d61481d1a58eba1ac29000363dcf4358520056c639e86b0a40009ae8750d61480013590ea1ac2900034bdd5435852073e963aa86b0a4000d8f7350d6148015b18e6a1ac290003a3d8d435852000786a9a86b0a400a9e4874c56148001d8ac698ac290003e150d3158520006b5baee0b0a4000d6875dc16148001b56e9b82c2900036a1d37058520006e5b9ee0b0a4000dc873dc161480033d50db82c2900067a21b7058520006b5b2ee0b0a4000d6865dc161480013d307b82c2900035ad4f7058520006b4a9ee0b0a4000dab43dc16
  | 6 => 0x4b6c388232a4000a6e8610465480014db0c208ca90002d3a0c4119520005a6c188232a4064b6a8010465480016d300208ca900365ba1f3119520004b6c3e6232a4000b2e84cc4654800165b09988ca90003535cf311952000786a1e6232a4064b6a80cc465480016d301988ca900365ba1e3119520004b6c3c6232a4000d65718c465480c96d501188ca90002da6023119520004b6c3a6232a4000a6f864c465480014d90c988ca90003535cd311952000786a1a6232a4000d65714c465480c96d500988ca900365ba1c3119520004b6c386232a4000a6e860c465480014db0c188ca90002cba10311952000596c206232a4064b6a800c465480016d300188ca90002da21930195201aeb53b26032a40e6e6a764c065480c96d706980ca90193d2e0d3019520736b5b9a6032a40e6f4a734c06548001ad2e6980ca9039bd25cd3019520006a4b9a6032a4000f4b634c06548001e90c6980ca90003cad0d3019520007a521a6032a4000f29434c06548001e9286980ca90003c250d3019520005b5c0a6032a4000d69714c06548001e9662980ca90003d24c5301952000717326cbb224000a6c8654f644801535f0ea1ec890003635cd43d912000786a9a87b224000ba9809076448001b96e6986c89002b721cd30d9120007a4a9a61b224000f89434c3644801b2dd0fbaac8900025b60f755912000697a1eeab22400096d81dd564480018dec1baac8900035a8c37559120006b5086eab22400096e87d9564480012dd0e32ac8903ba6b2137359120004b7c2ae6b22400d96c855cd64480013cf02b9ac89002e792057359120004f5c02e6b22400096e87d4d644801b2d90fa9ac8900025ba1d5359120004b643aa6b224000a6c8654d64480153590ea1ac890002ab219435912000697baa86b2240e7d2c7550d6448001b1ee6a1ac89002b631cd435912000786a9a86b224000d6b75dc16448001ad0ebb82c8900035ad977059120006b432ee0b224000dab64dc164480a5b50c9b82c8900027a60f7059120006b5a9ee0b224000d6953dc164480a5b5687b82c8900036a50f7059120004f4c0ee0b224052dab41dc164480013d50e982c89002a7a21d3059120006b5baa60b2240e6d68754c16448001b96e6982c89002b721cd3059120007a4a9a60b224000f89434c164480013d301bb2a8900025be157655120004f5c02ecaa2400c96e87d9554480018d8edb2aa890032cba1365551201aeb4386caaa240019e880dc554480033d50fb82a8900267aa1b7055120006b5b2ee0aa240f5d6865dc154480013d707b82a8900027a60f70551207aeb5a9ee0aa24000d6953dc154481edb5687b82a8900036a50f7055120004f4c0ee0aa240f5d6b51dc154480013d700baec2900067a20175d85207a6b4380ebb0a4000b6581d9761480016cb0232ec29
  | 7 => 0xd434c76548001acae298eca900d6daa0131d9520004b743863b2a400096d870c765480014dd0c18eca900029b61831d95200059742063b2a4000b2d840c7654806b6d50018eca90002da60031d9520005b443261b2a4064d6a764c3654806b6d706986ca900d7d2e0d30d9520006b5b9a61b2a4000f4b734c36548001a96e6986ca900035a5cd30d9520007a439a61b2a4000f4b634c36548001e90c6986ca90003cad0d30d9520007a521a61b2a4000f29434c36548001e9286986ca90003c250d30d9520005b5c0a61b2a4000d69714c36548001e9662986ca90003d24c530d9520794b642ee6b2a400096f855cd65480013d700b9aca9002a5b21d5359520006a7b9aa6b2a4000d8f7350d6548015b18e6a1aca90003c354d4359520006b5b2ee0b2a4053d6865dc165480013d307b82ca9014f5ad4f7059520006b4a9ee0b2a4000dab43dc16548001b5287b82ca900027a607705952029eb5a8ee0b2a40009ea874c165480153d10e982ca9000372dcd3059520056e439a60b2a4000f49534c16548001f1286982ca90002d3a0e6419520005a6c1cc832a4000b6980990654801ba9f06b98ca900025be05731952008e37b02e632a4000d4f305cc6548001ad460b98ca90003534c17319520006b5082e632a400096f87d8c6548001a9ae7b18ca900025b61e631952000597424c632a4000b2d8498c65480016d301318ca900025be1d6319520005b5c02c632a400d96e8718c65480012db0e318ca90002cba10631952000596c20c632a4000d4d7318c6548001c9ac6318ca90002d9a046319520005b2c08c632a4000a6e86d0c65480014db0da18ca900038ba1b431952000716c368632a40fcd2e76d0c65481d1c5ceda18ca903a34bdcf431952000696b9e8632a40fbe2f60d0c65481f7e5461a18ca903efca843431952006cb743c8632a400096d8790c65481f565b09218ca90003535ce4319520325b54048632a4000b698090c6548001a9ae6a18ca903e74b9d9431952073f173b28632a4000f0f8350c65481cfa5ee6a18ca9039fc39cd431952000696b9a8632a40e7f0d7350c6548001a1ae6a18ca90003c3d8d43195200078631a8632a40f8e2f6050c65481f1e1e60a18ca903e3ca8c143195207c7869828632a40f8f2a1050c654801b2dd0e218ca900025b61c43195207bd974208632a4064b6a8010c65480016d300218ca900025be0d711952000697a1ae232a4000d2d435c4654801bacf02b88ca900471bd817119520006b5182e232a4000d67105c46548001ad420b88ca90003594417119520005b4c04c232a4000b2e84184654800165b08308ca90002d3a0c6119520005a6c18c232a4000d6571184654801b2dd0f208ca900025b61e4119520006b2b8c8232a4064b6a8090465480016d301208ca900365ba1c41195200
  | 8 => 0x929eca90002da60253d9520054b7c3aa7b2a4000d4d7354f6548001b1ee6a1eca9002b631cd43d95200078729a87b2a4000f0d5350f65480016d30128eca9000372dcd30d9520056e439a61b2a4000f4a534c36548001e92a6986ca90003e250d30d9520005b4c06e9b2a4000d2f749d3654800169d073a6ca90002d360e74d95201adb5404e9b2a4000b69809d365480014dd0c3a6ca900034b5d074d9520005a741cc9b2a4000b4d8399365480016d301326ca900029ba1b73d952000637436e7b2a400096d81dcf65480018dec1b9eca9000353cc373d9520006b5186e7b2a4000d4d30dcf6548001ad421b9eca900025b61e73d952000597424e7b2a4000b2d849cf654806b6d50139eca90002da60273d9520006a7c1ae7b2a400096f815cf65480018dec0b9eca900035a8c173d9520006b5082e7b2a4000a6e861cf654800165d0839eca90002cb61073d9520005b3408e7b2a4000b65811cf654806b6d50039eca90002da60073d9520006a6b9ec7b2a4000b2e8498f654800165b0931eca90002da60263d9520005b5c02c7b2a400d96d8718f654800165d0831eca90002cb61063d9520006a6b98c7b2a4000e4d6318f65480016cd0231eca90002d960463d952000697b9e87b2a4000d2d73d0f65481f9c5ec1a1eca903f3ca8c343d95207e79508687b2a400096e8790f65480012db0f21eca9000353dce43d95201adb540487b2a4000b698090f6548001a9ee6a1eca90003c3e0d43d952000697b9a87b2a4000f0f7350f6548001a1ee6a1eca900034b5cd43d95200078639a87b2a4000f0f6350f6548001e18c6a1eca903e78bd8143d95207cf8798287b2a40f9f2a3050f65481f3e1a60a1eca903e7ca84143d9520004b743887b2a400096d8710f654806b6d50021eca90002da60043d95201adb5404e3b2a4000b69809c765480012df06b8eca900034bd0d71d952000696a1ae3b2a4000c6f605c76548001ad460b8eca900035a84171d952000537430e3b2a4000b2e841c7654800165b0838eca90002d3a0c71d9520005a6c18e3b2a4035b6a801c765480016d30038eca90002da60261d952006cb6c38c3b2a4000b2e84187654800165b0830eca90002d3a0c61d9520005a6c18c3b2a4000d657118765480012dd0f20eca900025b61e41d95201adb540483b2a4000b698090765480012dd0e20eca900025b61c41d95200053743083b2a4000a6d86107654800169d0620eca90002d360c41d95201adb540083b2a4000b698010765480012dd0f98eca900025b61f31d95200059742663b2a4000b2d84cc76548001a9ae798eca90003c350f31d95201adb540663b2a4000b6980cc765480012dd0f18eca900025b61e31d9520006b2b8c63b2a4035b6a808c765480016d30118eca900025b61d31d9520006a6b9a63b2a4000f
  | 9 => 0x65551203ae36396caaa24035c7870d9554480031dd0db92a8900263ea1b7055120064b7c3aa92924000a6c865525248019a5ce8aa4a4900d6da20154949201ae3c386caa924035c6c76d9552480031d90cbaa84900067a20175509201ae363b6caa124064c6c76195424806b8dae5b2ec2901931b5c865d852000636b96ebb0a4000a7581dd761480018dae43aec2900029d60475d85200043fc2ae9b0a400587c855d361480031db05b9ec2900021fe1573d852002c3e42ae7b0a400087e87d4f614800b0f90fa9ec2903cb1b5cb53d85200043e43aa7b0a40f0c6d7254f61481b7878eba1ec2903bb2b5cb43d85206d61e3aa87b0a4000c9f7350f6148007938e6a1ec2900038754d43d852076656b9287b0a400b8ed8790b61480171db0f196c290003a350e32d852001e6639a65b0a4000e59534c36148001d3286986c2900073a5c930d85201ac3e436eab0a400087e87d956148001878e9b2ac290003171cf65585200043f438cab0a4000c3c7419561480018b8e632ac2900030fd9774585200061e32ee8b0a4000c5f65dcd61480018b8cbb9ac2900021fe0e76d45200043ec1ceda8a4000c3f439db514800187a873b6a2900371ba0a76d452006e36c14eda8a4000c6f219db51480018da433b6a2900031e84276d45200063c884eda8a4026a6d82d9351480010ff0eb26a2900161f21d64d45201353643285a8a400587c851d951480050fd0fb2aa29008e9b60b65545203ae36396caa8a400287c8759551480031dd0db92a29002e5ba1e5254520006363b4a4a8a400996c87549514800b4d90ca92a2900021fa1a76545200053ac0ceca8a400087f839d951480010fb073b2a2900030fd0e76545200061ea1ceca8a4000c6d829d951480018eb033b2a2900031dc4276545200051fc22eca8a4025a3c845d951480014bf06bb2a2900929720d76545200053bc0aeca8a400087f831d951480010fb063b2a2900030fd0c76545200061ea18eca8a4000c6d821d951480018de643b2a2900031b0c8765452002c3fc08eca8a400587d811d951480018de423b2a2900031b48476545200063b880eca8a4000c7a101d951480018ea203b2a2900031e440765452011d36c16c8a8a400087f8759151480010f90eb22a29008e9ba1b7254520006363b4e4a8a4000b65819c951480474d90cb92a290002d9e057254520006373b0e4a8a4023a6c86509514800b0fd0bbb282900021f61776505200145e43ac8a0a40018ee86dc9414801b2dd0bb9282900025b617725052004cd643a84a0a4000b658119721480191db0fb2642900063b21975485201ae363b6ca90a4000e6461d9521480c98d8ec32a42900063b2197448520066563a6c890a40028ec8759121480055c902b2242900029b61a54d952000696ba4a9b2a4000b2e8494f654800165b
  | 10 => 0xb2a4075a6e821c7654806b4db0438eca900d69ea0071d95203ad3cc00e3b2a400087e8790765480010fb0f20eca900021fa1c41d95200043ec3883b2a4000a5e8310765480014bb0620eca901d69ba0841d952000536c1083b2a4035a7a8010765480014f30020eca900021fa1f31d95200043ec3e63b2a4000a3e84cc7654800147b0998eca90003175cf31d95200070ea1e63b2a400087e878c765480010fb0f18eca900031d5c631d95200043ec3a63b2a4000c5d734c76548001c3a8698eca900031d5c531d95200043f43863b2a400087d870c7654800147d0818eca900028f61031d95203ad3741063b2a4000a6d820c7654806b4f50018eca900029e60031d95201ac3f43c43b2a400087d8788765480010ff0ab9aca9000e1f21d53595200062fb9aa6b2a4000c9f7350d6548007938e6a1aca900038754d43595200143e42ee2b2a4000a5e8399065480014bb07320ca900021fe1f63195200062eb9ec632a400087d8798c654800147d09318ca900028f61263195200043fc3ac632a400587e8718c65480010fb0e318ca900028fa1063195200051ec20c632a4000c5d7318c65480014ed02318ca900029d60463195207e61f3b68632a40f9c3e7650c6548001a3ae6a18ca9000387d8d43195200070e31a8632a406496e87d0865480012db0fa10ca90002d3a0f4219520005a6c1e8432a406496e87cc865480012db0f990ca901929ba1b3219520005974266432a4000b2d84cc865480c96d501990ca90003535ce321952000786a1c6432a4064a6c864c86548001c98c6990ca900365ba1c3219520004b6c386432a4000b2e840c8654800165b08190ca90003535cc321952000786a186432a4000b66810c865480016cb02190ca90192daa0032195200051f420c232a4000a3d8418465480014bd06308ca900029760c61195200063ab88c232a406496e8788465480012db0f108ca90192daa02211952006cb74384232a400096d87084654800165d08108ca90002cb6102119520005a74184232a4000b4d830846548001acae2108ca90192daa0021195203a53c4326032a4000d59734c06548001e3286980ca900d71b5cb65d912000717a16cbb224064c6d7219764480031db05b9ec8903cb1b5cb53d912078636b92a7b2240038bf8750f644800193ae6a1ec8900038754d43d912076656b9287b22400087e87d9564480010fd0e32ac8900161fa1f75591200043ec1eeab224000c3f43dd564480010fb03baac8900021fe15735912002c3e42ae6b2240008f7815cd64480051e902b9ac8900021fa1f535912002c3e43ea6b22400087e8754d64480010f90ea9ac89000e2f21d43591200061fbaa86b2240dac3c7550d644800193ee6a1ac89000f271cd43591200070ea9a86b22400087f855d954480090fd0fb2aa8900128fa13
  | 11 => 0x480014db052a6ca900063b60b73d95200051f424a7b2a4000a3d8494f65480070ff0ea9eca90003175cd53d952078636b92a7b2a40eecad72d0f654800193ee6a1eca9000f271cd43d95200070f29a87b2a4000e1d5350f65481d995ae4a1eca9000297a0e64d95200052ec1cc9b2a4000c5d73d8f654800147d0931eca900028f61263d952006c3ec38c7b2a4000a3e8418f654800147b0831eca90003175cc63d95200053b408c7b2a4000a758118f65481b787ceda1eca9036b0f9d943d95200068fb9a87b2a4000e1f6350f6548001c38c6a1eca900d65ba1f42d9520004b6c3e85b2a4000b4e83d0b654800169b07a16ca900d65ba1f32d9520004b6c3e65b2a4035a6e86ccb654800165d09996ca90002cb61332d95201adb540665b2a4000f0d438cb654806b4d90c996ca900039318d32d9520004b743865b2a400d96d870cb654800165d08196ca90002cb61032d952000786a1865b2a4000b66810cb65480016cb02196ca900d6daa0032d952006c3ec38c3b2a4000a3e84187654800147b0830eca9000297a0c61d95200052ec18c3b2a4000c7571187654806b2dd0f10eca900025b61e21d95201adb540443b2a400096e87087654801b2db0e10eca90002cba1021d952000596c2043b2a4000b4e83087654800169b0610eca900d6daa0021d95203ad3c43261b2a4000d5b734c36548001e3286986ca900d69b60b74d95203ad3cc06e9b2a4000c3f749d365480014bd073a6ca900029760e74d95200061eba0e9b2a4075a6e821d3654806b4db043a6ca901d69ba0b73d95201ad36c16e7b2a4000c6d72dcf65480018dd05b9eca900031b60b73d95200043ec0ee7b2a4000c5f30dcf65480018ba61b9eca900021f61e73d95200051f424e7b2a4000a3d849cf65480018dae4b9eca9000317e0d73d95200043fc0ae7b2a4000a3e841cf654800147b0839eca901d69ba0873d95201ad36c10e7b2a4000a76811cf65480014eb0239eca900d69ea0073d95203ad3cc00e7b2a4000c3f73d0f654800187ae7a1eca903a38b9cb43d95207e716b9687b2a400087e8790f65480010fb0f21eca9000317dce43d95200062fb9a87b2a4000e1f8350f654800187ee6a1eca9000387dcd43d95200060fb9a87b2a4000c3d7350f6548001c38e6a1eca9039f8b9c943d95207cf16b9287b2a40fde1e3250f65481fbc3864a1eca903e787cc143d95207cf0e98287b2a400087e8710f65480010fb0e21eca900d61fa1f42d95200043ec3e85b2a4000a5e83d0b65480014bb07a16ca900d61fa1f32d95200043ec3e65b2a4000a3e84ccb654800147b09996ca900d69b60b71d952000636b96e3b2a4000c6d725c765480010ff06b8eca900030fd0d71d95200061ea1ae3b2a4000a3e841c7654800147b0838eca9000297a0c71d95200052ec18e3
  | 12 => 0x30fd0c76545400061ea18eca8a800587f811d9515000b0fb023b2a2a00030fd0476545400061ea08eca8a8000c3e401d95150001878803b2a2a00031bc80765454000636900eca8a8000c77101d951500018f4203b2a2a00031d44076545400063c880eca8a8023a3c865d15150001878ecba2a2a0002cde05745454000c5e432eaa0a8061c3c76d95415012b878ec32a82a0002c760c655054001477414ed90a800087f855db215000b0f90abb642a00161fa1776485400043ec2eec90a800987e8795165c800187ee92a2cb900063b209735972004c3e43aa6b2e4000c5f7354d65c81e18d8e4a9acb903bb2b1cb43597200064fb9a86b2e4003c9c7350d65c8001c3aa6a1acb903b32b1c9435972004c5f43ea8b264000c3f75d5164c80031d904b9ac9903cb1b1cb535932078636392a6b2640098bc8750d64c800193ee6a1ac99000f271cd43593200070ea9a86b264009aac8250d64c81d9958e4a1ac9900121f617765532000c77416ecaa640018ec825d954c81012db0bb92a9900161fa1774587200043ec2ee8b0e40018ec825cd61c81e58d8e5a9ac39000317dcd535872001e2e39aa6b0e40f0c6c7254d61c81dd958e5a1ac39000327dcd435872001e4e39a86b0e4000e1d5350d61c81d9958e4a1ac3903b7a38c943587200747643a84b0e400eae48150961c801d1d90e992c3900263d21d31587200074aa1a62b0e4000ec5324c561c804d4d904b26a39000a1f617765472000c77416eca8e40018ec825d951c80050f90eb2aa39008e9b2096554720074b6c2ee4a8e400996c8754951c80474dd05bb2a39008e9b20976547200053bc0aeca8e4023a6c8259151c80016cf02b92a3900161fa1776507200043ec2eeca0e40018ee82dd941c80031d904bb2839000a2f21d645072008cb742ee4a0e400096d85dc941c80133590ea1283900423b21d644872004cb743ca8b2e4000d2f7495165c81e52d90bb9acb900265b21d5359720006a7b9aa6b2e4000d8f7350d65c801fb18e6a1acb90003c354d435972004cd743ea8b264000d2f75d5164c81dd35909b9ac9900266b21d435932004d5643286b264000d8f7350d64c801fb18e6a1ac990003c354d4359320404b6c2eecaa6401196e85dd161c80012db0bba2c39003a3b21d64587200757240ac8b0e400e8ec8758d61c801f998e6b1ac39000353dcd535872007ea639aa6b0e4000d8f7350d61c801fb18e6a1ac3903b7a3d8d435872000786a9a86b0e40099e4874c561c8001d8ac698ac390003e150d3158720074b6c2eeca8e400996c8759551c801d2db0bba2a3901eb4b9537454720074b643aa8a8e4010d2c7455151c80016cf02bb2a3901eb4b9d374547203d6963a2e8a8e4000b67815d151c80232dd0bbb283900025b617765072004cd643ac8a0e4000c3d7495365
  | 13 => 0x43ec3863b2a8098a3e840c7655000147b0818ecaa00029ba0831d954000536c1063b2a8061a7a800c765500014f30018ecaa00021fa1e21d95400043ec3c43b2a800087e8708765500010fb0e10ecaa02628fa1021d95400051ec2043b2a8000a5e8308765500014bb0610ecaa01869ea0021d95400053cc0043b2a8102c3f75dd165500010ff0ab9acaa000e1f21d53595400062fb9aa6b2a80038bc8750d655000193ee6a1acaa00038754d43595400068fa1ae632a8000c5e865cc65500018b90cb98caa000347a1173195400068ec22e632a80a1c5f645cc6550001a3e82b98caa028317d817319540006ada02e632a8000d1e405cc6550001a3880b98caa0003561017319540006a7902e632a8000d4d205cc6550001ab420b98caa00021fe1f63195400062eb9ec632a800087d8798c655020347b09318caa0003175ce63195400043fc3ac632a8000c5d7358c655000b0fd0e318caa00021f61c63195404b51f420c632a8000c5d7318c655012b4790ca18caa02630f9d943195400068eb9a8632a8000e1f6350c6550001a6e82b88caa0003175ce61195400052f418c232a8000a5d8318465500018bae6308caa00029ba08611954000536c10c232a8000c757118465500c3878edb2aa8a00029760c65d894001e2f39aa7b128000c5d7354f625000793ce6a1ec4a0003275cd43d89400070ea9a87b128100c3d7419662500014bb0632cc4a03ff1e5c065989400043f43ecab12800087e8719562500014bb0632ac4a00029760c651894000477c3ac43128005a3c86552525000187cecaa4a4a00029760c65d85400053ac0eebb0a8000a5d831d761500014eb023aec2a00021fe1573d854002c3e42ae7b0a800087e87d4f615000b0f90fa9ec2a00021f21d53d854001e2f39aa7b0a8000c5d7354f61501b5878eaa1ec2a000327dcd43d85400070ea9a87b0a800087f855cb615000b0f90ab96c2a01861f21b75585400043f43ecab0a800087e8719561501fd87ee832ac2a00029760c65585400043fc1ceda8a800087d839db515000187e873b6a2a00030f50e76d45400061fa0ceda8a8000c3d419db51500018de413b6a2a00031b48276d45400063d084eda8a8000c79109db515000b0f90a3b2a2a00030f950765454001c6f418eca8a80008dd831d951500050fd0fb2aa2a000a1f21d655454002d1e432a8a8a8000c3c7655151500010fd0d3b2a2a00029d60676545400043fc1ceca8a800087d839d9515000187e873b2a2a00030f50e76545400063ac0ceca8a8000c6f209d951500018da413b2a2a00031dc4276545400053bc0aeca8a800095d831d951500494bd063b2a2a00029760c76545400061f420eca8a8000c3d841d951500010ff063b2a2a000317a0c76545400043ec18eca8a8000c5d831d951500010bb063b2a2a0
  | 14 => 0x5324c760484018bee6a9ec8a800e2fe1d43d915001e4f39a87b22a000c9d7350f6454001c3aa6a1ec8a80121f21572d91500051ec2c83b22a003c9e7350f625400193ae6a1ec4a80038754d43d895000477c3ac4312a075a6f8558862540c30ff0aba6c2a800a1f21574d85501343e43aa9b0aa00587c85dcf61540050f90ab9ec2a809a1f21d53d855083e1e3ae87b0aa106c3c7550f615400793ce6a1ec2a8003275cd43d85500070ea9a87b0aa00287c855cb615412b0fd0dba2a2a80970f19374545500153a43ec2a8aa000e3743d855154001c6a87b0aa2a80169de03615455002d3ac06c2a8aa105e7070d85515420bcce41b0aa2a84179948361545500153d436e0a8aa000e7361dc151540030f90cbaa82a81d61fe1576c855004c77416e7b2a80008ed82dcf655000147b0929ecaa000e1fe1d53d954001e2f39aa7b2a8000c5d7354f655000193ee6a1ecaa00038794d43d95400070ea9a87b2a8000a3d8494765500018bae7b1ecaa04128f61263d95400062fb9cc7b2a8000c5f7358f65500290fb0e31ecaa0003175cc63d954030d1e43287b2a8096c3e7650f6550001a3ee6a1ecaa000387d8d43d95400070e31a87b2a801487d8718765500014bd0630ecaa00029760c61d954000537410c3b2a8000a6d8218765500018eae230ecaa00029ba0b73d954000536c16e7b2a8000c3f43dcf65500018bc87b9ecaa00031750f73d954000637416e7b2a8000c6d82dcf65500010fb03b9ecaa000317cc373d95400062e986e7b2a8000c6f20dcf65500018da41b9ecaa00021f61e73d95404c51f424e7b2a8104a3d849cf65500018bee739ecaa000317e0d73d95400061fa1ae7b2a800087f815cf65500018de40b9ecaa00031b48173d95404c51f420e7b2a8061a3d841cf655013147f06a1ecaa026387e0d43d95400061fb9a87b2a8000e1f7350f655000183ee6a1ecaa00030f5cd43d95400070e39a87b2a8103e1f3050f6550207c3a60a1ecaa040f8bc8143d954081f1690287b2a800087e87ccb65500010fb0f996caa02628fa1332d95400051ec2665b2a8000e1d438cb65500010fd0e196caa00021f61c32d95404c51f42065b2a8000a3d840cb6550001c3a86196caa00029da0432d95400053ac0865b2a8061a7a800cb65500014f300196caa00021fe0d71d95400061fa1ae3b2a8000c3d435c765500018de40b8ecaa00031b48171d95404c51f420e3b2a8061a3d841c765500014bd0638ecaa00029760c71d954000537410e3b2a8000a6d821c765500c34f50038ecaa02629e60071d95400043f43e63b2a800087d87cc7655013147d0998ecaa00028f61331d95400062eb9e63b2a8000e1d43cc765500010fd0f18ecaa00021f61e31d95400043ec3a63b2a8000c5d734c76550001c3a8698ecaa00021fa1c31d954000
  | 15 => 0xea9ecaa0803175cd53d95410064fb9a87b2a8200e1d5350f655040147b09286caa0c230fdd7745954100477c12e6b2a82098ec825cd65504011f700b9acaa08063e201735954101c3e43aa6b2a8200c5f7354d65504071790ea1acaa080327dcd43595410070ea9a86b2a820587f875d762504010ff06baec4a08030fd0d75d89411443fc0aebb12822587d815d7625040b0fd0bb9ec4a08021f61773d894102c3fc3ea7b12820087d87d4f62504010ff0ea9ec4a08021f61d53d89416d61f3aa87b128200c3d7550f625040793ce6a1ec4a0803275cd43d89410070ea9a87b128200aad840cb6250401d1a86196c4a0802b960432d894100574c0065b1282008ef87588625044b87ce8b2ca4a080a2f21974949410043ec2ceca9282008ef825cf60504131d904b9ec0a080327dcd43d81410070ea9a87b02820987c8754d65c84018bee6a9acb9080327dcd435972101e4e39a86b2e4200e1d5350d65c84131790ea1ac99080327dcd435932101e4e39a86b264200e1d5350d64c84090fb0bbb2a9908063b60b755832102c3f43eeab064275e6b20dd560c84010fb07baac1909d71ba0b755832100636c16eab064275c6f20dd560c84018da41baac1908371b5c875583210053ac08eab064274e6b201d560c84031db05ba2c1908063b60b73583210043fc2ae6b06420587c855cd60c84010fd0fa9ac1908161f21f535832179f35906a6b06420087e8754d60c84010f90ea9ac190bc31b5c9535832178f35902a6b064200c3f75d0d60c85b7878eba1ac190bbfaac8343583210061fbaa86b0642dac3c7550d60c840193ee6a1ac19080f271cd43583210070ea9a86b0642eccad7250d60c85dbd1c64a1ac190bb7aac81435832100575c0284b064203ccc734c960c84015d700992c1908263e21d30583210072ca9a60b064200e99434c160c84135d504982c1908073a5c9305832101c3fc3aa7b2a4200c5d7354f654840193ee6a1eca9080f271cd43d95210070ea9a87b2a42008ef825cd65484070f90ea9aca9080317dcd535952101e2e39aa6b2a4200c9f7350d6548407938e6a1aca908038754d43595210062fb9aa7b224203c5c7354f644840717f0ea1ec890803275cd43d91210070ea9a87b2242008ef825cd64484018bee6a9ac89080f171cd535912101c5e43a86b224200c9f7350d6448407938e6a1ac8908038754d435912100c76416e0b2242038de83dd954484011bb07bb2a8908121fa1f655512102c5f43ec8aa242018ec825d760484031d904ba6c0908063b20973d81210062fb9aa7b024203c5c7354f60485e18d8e4a9ec09080327dcd43d812101e4e39a87b024200e1d5350f60485d9958e4a1ec090802ba60242d81210747643a85b024200e8d438cb60484015d301196c09083a3b21d32d81210074aa1a63b024200ec
  | 16 => 0x35915112d1e426c6b22a22487c8758d645444b47908b1ac8a880317dcd635915100536412c6b22a22493c8750d64544014790ca1ac8a880347dcd43591510070eb1a86b22a30de3464dc56454401a6ec9b8ac8a8c374d193715915186e9ba1ee2b22a200d3543dc564544012eb01b8ac8a8c374dd0371591513543ec3ec7b12a200c5d73d8f62544d54d904b1ec4a8893479cd43d89510068eb9a87b12a200e1d6350f62544014db0c196c4a8803c350c32d8951005b2c0865b12a200b69800cb625444b87ce8b24c4a88921fe1d63989510062eb9ac7312a30cd1f7350e6254449a38e6a1cc4a88038758d43989510063bb1ae3312a200c75635c66254401a6e86b8cc4a88034d50d7198951006b3b12e3312a26ad64625c662544012ef00b8cc4a89ab59c817198951356b5902e1312a200a3d8418262544014bb06304c4a88029b6086098951004b7c12e6b12a200977815cd62544d50f90eb1ac4a880317dcd63589511262e39ac6b12a200d1f7350d6254449a38e6a1ac4a88038758d43589510069ba1ee2b12a200d3543dc56254401acec5b8ac4a88025d6037158951014ba40ee0b12a22587d87d90625444b87ce9b20c4a89aa5b2097318951356a6192e6312a22487d87d8c62544018bae7b18c4a88029be0963189511268f39a86312a200d1d7350c6254401c3ac6a18c4a8c33c30c94318951004b7c3ac4312a200b678158862544014db0d990c4a89ab5ac81701895100536c14c0312a200a3d8418062544014bb06300c4a88031e5c06018951004bbc0aed212a26ad6b205c242544012eb03bb284a88025de05765095160cbbc0ae9b02a202974815d360544470fb0fb26c0a88970f9d364d81510043fc3ac9b02a225c3c7459360546150fb0cb9ec0a88025be0973d8151354b6412e7b02a30b977815cf60544052e902b9ec0a888e1f61f63d81510062eb9ec7b02a309c7471d8f60544018bee6b1ec0a8c2b1d1c563d81516de9bb8e87b02a307d3471d0f6054449a3ce6a1ec0a8803475cd43d81510070eb1a87b02a2dad377150f605460da68e2a1ec0a887e5de0572d8151014ba40ae5b02a22593e87dd1605440127b07ba2c0a88034dd87745815100697906e8b02a200d2d20dd16054401a6e21ba2c0a88030fdd874581510058ec18e8b02a20087e87d91605444b878e9b22c0a888e1f21d645815112e1e3a2c8b02a30987c86dcd605440127f08b9ac0a88964f2117358151004b7c12e6b02a26a96c825cd60544012ef02b9ac0a88030fdd363581510061e3a6c6b02a22387c8758d605440187ee8b1ac0a88030f1d163581510062fb9ac6b02a20093e87d0d605444b2790fa1ac0a88024fa1d43581510049e43a86b02a224d1e7350d6054401a3ae6a1ac0a88038758d43581510069bba6e2b02a200d3474dc560544070ff0
  | 17 => 0x4a4f1e6b2054d60949dfd5641a1ac12900327dcd435825201e4e39a86b04a400e1d5350d60949dbd5640a1ac1290029e61740582520071caa680b04a4098f8874c16094801cb2a6982c129003a650d30582520062fb9aa7b22a4038bf8750f645480193ae6a1ec8a90038754d43d915235c3e43aa7b0aa400c9f7350f6154807938e6a1ec2a90038754d43d85520143e42ae1b0aa400c5f7354f605480193ee6a1ec0a900f271cd43d81520070ea9a87b02a4098ec825cd65908130f90ea9acb2100317dcd53596420064eb9a86b2c8400e1d5350d65908018bee6a9ac32100f171cd53586420064eb9a86b0c8400e1d5350d61908131e90e98ac321003a550d315864202c3f42ee0b0c840087d85dc161909e7cd641a9ac1213c79ac8153582420064eb9a86b048400e1d5350d60909dbd5640a1ac1210063b60b715824204c7c43a60b048400e59534c16090801d3286982c1210123b60b73d954201c3fc3aa7b2a8400c5d7354f655080193ee6a1ecaa100f271cd43d95420070ea9a87b2a840387c8754d65508018bee6a9acaa100e2f21d43595420064fb9a86b2a8403c9c7350d6550801c3aa6a1acaa10030fd9774549420053ac0ea7b0a8400c9f7350f6150807938e6a1ec2a10038754d43d85420043fc2ae1b0a840587c855c3615080193ee6a1ec0a100f271cd43d81420070ea9a87b0284018ec825c760508d7ad640b8485a880a1f61773d91510061f2a6e7b22a200c3e545cf64546150fb0ea9ec8a88968fa1153d91510062fb9aa7b22a2038bf8750f645440147f0aa1ec8a8c1b0f5d543d915101e4f39a87b22a200c9d7350f6454401c3aa6a1ec8a88028f61640d91510251f436c8aa2a20287d85dcf62546150fb0ea9ec4a89aa9b20953d895183e1ebae87b12a306c3d7550f625440793ce6a1ec4a8803275cd43d89510070ea9a87b12a200a6d850cb6254401d1a86196c4a8802b960432d895100574c0065b12a2008ef8758862544d5ad640b84a4a880a1f61676909510143e432eb212a20287e86dd542544050f90cbaa84a8a5a1fe1d54d81510261e3a2a9b02a20287d85dcf60544011df04b9ec0a88263b20973d81518543ec3aa7b02a200c5f7354f605460f87aeba1ec0a8c1b0f5d543d815101e4f39a87b02a200c9d7350f6054401c3aa6a1ec0a88030f99373d91510061f322e7b22a22487d87d8f645444b47d09b1ec8a8803175cf63d915112d1f422c7b22a200c5f7358f64544014d904b1ec8a88924fe1d43d91510051fc3287b22a224d1e7350f6454401a3ae6a1ec8a88038758d43d91510051ec3481b22a200b3581903645444b47d0db22c8a88970fddb645915183c9e426e6b22a200c3c64dcd6454401878c8b9ac8a88025be097359151354b6412e6b22a200977815cd64544012f700b9ac8a888e5e2017
  | 18 => 0x400000401800804c00806800c0040100040080e001003800006c00401c00002800c00002000c00801405003800002402400000401801001400400c00400000401803406803001c00002000401400000002001004800000000000000002000000000000001c02c00405800000000800000400401c02406000807802001c04000000400c00000c01401400c01800002000400000401405001801800c02001000000c0200000000a003400c01800401c03c03401400002400000800400003c00406c00001400001401c00000003801800c0cc00000800800400800000800c00000005c02801000800001800001401001002400000000000405401000000400002400402403406000000000000001001400004000000000801401000000000c00401800800400400400401400800000803002800000801800c03400000403c01403001800001c00800401c0080040000200bc00400000002800400c0140000040cc00000000800004401400000406400c00400002c00c01401401800000c03000401400c03c02002405c06400c00401002408c00800000402c00000000000c00400c01c03400400404c0100080100000300000000000100000380340d800003800000401800c03800c00000402401000001400c00000400000005400000400803808400400000804000800009406400400005405400002c00003c01800407802800004c00000006c01005000000403402800001400003000000c01000000000c03800000403000407401400007800000803000c00000800800000002400005c00400406c03c01403801400001801800000403005803c00801800800000009801007001803c08800400c00c02408800000c0080380b001c00400800400401400400c00800002001c05800800c00403c02400800000000804c01002800004002c0cc00000000000c00402400802c0300b005801401401001800000405808c01000802800c01c01802c01402000000001400000001000000c00400c00800800c03800000000001404000401402803001c01803400000003401007c02801800c084090fb0bb9ec4aa00317d4d73d89546e43ec3aa7b12a804c3d7550f625500793ce6a1ec4aa003275cd43d89540070ea9a87b12a800ceb625c262550139d0c4b84c4aa0023be1d621895413c3e43aa7b0aa800c9f7350f6155001c3aa6a1ec2aa2621fe1570d85540062fb9aa7b02a800c9f7350f6055001c3aa6a1ec0aa003175cd535925204c5e43a86b24a400c9f7350d6494807938e6a1ac9290038754d43592521461f326e2aa4a46ba77815d5619484f0ff0ea9ac32900327dcd435865201e4e39a86b0ca400e1d5350d61948131e90e98ac329003a550d31586524b43e43aa8b04a404c3e74551609486b4f100aa2c1292039ac8154582520062eb9aa6b
  | 19 => 0xd835249f16d000000015e0c28f78c7c1d702400004c099f0150b10e2a06509588551e04ba0000ed800000008700003fc72a2648b3000000026a8328db00ae34e800000070b1d924c40008a625580006440000000000978000342930429e43b3eb84591f463d07521003d82c0497a7902442401701a1c93c8d223e0e9cd9c71e13b929c7c62d800a140d1a85a44881d5490c4c83570a5807279e44e05ac78057209998dd2b03813da8e1c42657b0fa937d2f27e04c218888ea38624626341e810c00010a00003a121200293ca2e133580012a21fd000252c16a5650000a2083446c325800000000003a85441de60e00000013020d400022780000004d1800000000000000000007f43e10000f8c0004cd0bdcf6639e30e8d700000000b3862c6209b60f3000000033b0001c611ba58819822ac0003f90000d0d31e0000681664b3c8922b401e50ce95f0bc800000081100000010103730000d30cca0002cc01f857e28e1549f2109a0003f780010ae03b0000000a505d6337a0f40004cd4d511a431c54a426058420e2a000020c4ab26e717f8ce057a62d10a01e82728c530c20d47ea5de0a91a5502e4a6116a39d03c6a61970cc80001c325e8000d380000c68e08fb67202d2984809846e00005d800000018109fcbb66d20a1170472a0001248000f0600037a982c75a9480001b50cfe1b9292a2f132a36b006102c0001702d4a254a9c5ff4dca310db6000273801800000800800002001800402404800400400001407c00403401005000c00401000002800802004400000800400801801800800001800000400005000006405802002401c03400c00403000000001803000000400800800401401000001000002400c00001000407c01800401405001400002000800800000000000000401000800400404001400402401800000c00000002000c0a000c00c00000001800400401800004800400003400014c01800000000000003800400800400001801802000400403401801404c00c00805803000413c00c00000002400003002800000401802400000000800000800007008000000400002800800804003400800400000c09800400401000801400c01000000400800000403400000803003800c02401800401400003400c01000400400000408403802000400801800000000404808400401c00001c01c00000c00000803400404c01400803400000400403c00400001800401000801000800001000800003000000000006c00000400000800403c01c04003800000013801002000c00400000401000001c00401401001800802c01401804801403801005801c01800000800000001000002c00000007000403c00000400800801c00000000002c00001c02000409401801c00400000800c01000c01c000050004004000010008034000008004000
  | 20 => 0x3ae80003383f33498000f1e66700021a91f817c2da9ff400016431388040003ff3f40ba0c7816e0000000f9800005d800006e21e0001ee082c00001600000000000000cdc0004da0000000000000162a398e480000000ae00002ef4140fec0000fa38b1bd07305ad3c885e83044ce30d271826a6e21b01018bf00173349acc88666c082910850842c0b31f7c13800032392c423400000019f4a565811f78fd01fa00017215f8fee27c326a4b480a1e335695f47680001380000f7c48026c072cbae2f918390386aa0003d08528f3243246b0000bde2041ada1c5092299000000000025d423220cf7a000000023000037b0000c5cd744111e7953c00019226a26452b46c911800006160000001c444ca1f43cb095868453b27d80387d81ab2768dc0abc65410588641d030e4bc19a06946a73709bfd10a2b3000114000093821ca4541f08a33de253c6ee76e29015cc0000b41bb159873822700007fc01a36c1e29c882ac0dc34c03c116e65847892a00a25ee3c280001e4000000000039a4070881adc00000043694d00004d60b121900000004c5a344dc64ee36f800000000022901680000001290efcd8e7670909af40fa51a08f9f6809e00000016087b40004c19e0022a46a43f25b010a5a30cc82f815e8b30001bd84149b5245112d13647603490807280f50180cac2083e138100000000f70001decb7e44e3d20dd090e2860000a1c45e7ad2379bec73406740d887137c91400024e80d46993af91607d26d14b89f0d1588b8122a3bcf408992681c6c5ca84f2d800012b67870830000a981b2135846c8fa5a103d8000ba056712a236445c2f30000000b3e1724e79fa91228f347222a83f245a2c7a1413946231619ac431e0000000cf91d20f106884a07164e90000fc848e0001c718c108600018d158c0000001e20c9133a43d1ee05212e61963b58f30f247a20e8a7548ce82f0550b8c71069f2080000eca27a2a186d8f4a47b45100000002850198690f026e03669b406ce01822f951c0068a700020e888c0003310000be414e4dc026400016a4cf1f647249800bd9f9054253225c00003b28cb00000008e800011200011d808900011700000d21cf980493457629685b11f600000000000008f719ca5d4ed000010b25b40000000001a383a85120000000fce369146912120e6641b080000f86523850f7c0008c1015a474ed829115d2024df486f2f6839800000000000000002d23bc0104e4c937000000000073c1bc80000bc7c03a1005406a14938626808e084a2cea35ca6250844500000004fe2170000d9414b1d10000a7e98c000000120200049c8ebc00058c0000c183801a64660294000237000140000000043c00010729530af9318fba00020a80000000713d590cc2e28481c280000000000000000c0a000000000074c00024083
  | 21 => 0xff80940d900000012949720b18d4800098e444000119e7d40000fe035c39320c1f2c8fc13d000000136000000004f80003620c31720000000000000108290639e964cf82676000000000003f00024480006de00026d000007000023405be6754c81a348b6000000258c06252f0e90330b280b0199800000000043e9a6c0000080000abc4a00002dd157c90a0000000b70924736176124c000000000188095851028b80006248320e109ec0264dd1f51a880c207743a17392fe2804e6a6c4328970233110025819e1ce940823281d49a8000f188d809a1b2cf4c73f02a1da8ff85c21b78000ffe4ff00000010ec1a7268929012e04000019192986e911c8fe8f606844af15683409d73ce141ce58353097111ca0a8373a516e01f66534b415c03a03db35013a89882ee000122c0004c729c8000b5474b3480000fe02cd0001cac00000026580002625750000c583a697b48b1180e3275e1cd8278e2048821f10e021066d4d980002140d80fd0d24dfc0000f70b9800029717a0d180e86b4000123cb780000f984ed3767fe0f78ea49ea5642c3826046a23a239091864223b26d82990c65da1591b180007720000818df209332899790282514b30d0074698600000006b46091000f0810e3804498c0c6c6771000000042209143a8f80d3427e31f972928c6c520900010040042ec0000c9c31e00021741464eb1d99260b225694930000fa203231c000000074f4648a485b6318197977c00001112c000069037d156a4f03e470d4b39de8c3636a000000049c1831d600004c45f93be92649fa56213b1438d8820c21680000000bc2d78000d423a50d5071c3206960238000368749000085c00000026b9ae40000004c12168c648b200024a49e6354000000000038408680002380a21c79b74000000000150864c00022e9b684dc2ea3e50a7c0002fc2f5007437c00038a1ec828c5f70ea89cc18c96f0001ebcb863bd442107c1d29a840a8ba404646400006fd13a000187983cafe0000000aecfdc3d728aa714fc414430318d43ee7d500000000001c524b00010e0648000154c26090b00010bc2985a800019305145e1084800000000042700000000de3c5000000000000021cca4841b09900007da00046180011aa000000090c0002e22760ed40009284e909e53582071ba9e2c00022330400002b27394ef836c8023c11c500951300b9000241128e00008591940480953d70c640000d500000010246c2000107000037a0ba1d047949cb4a715dc4b8826000000000093b4e40c7c00000040c80000005f116080010580000000c0000011d000000011469e0aa250ce508a035f0bd4dee4d90000000e1e3f015299ec96e92c0f2171c1d8000317800075419d2e7800067a24c4000450c687a7000237c03c00000010084fa54400004fc7ee12327088880000
  | 22 => 0x99927427753806f81581c380005fa4c48000000364000270892051f0000170810289375086837a0000d8212c00073b080234c63a13822080000003d32d5a6200000003248000000000230800000004d36a87a12c800004180000001432368d34c6220343906040006a8000128cbc09232a8997c0001dd2a80000fc29604770e4000044411402d8ccc18a2fea0b897e53c0001394c2273348715bc2a60003c405f8dda6590d28f6000003e202000000000015b98001d651c28b09bc00067946693483bc4e421f97a40000c000000880b679f1f58cf12348ce1ab06b4b126bf1e8100c85666341222e8cd470031c9d6c7967dc08c00000000000e7063096400034091300c830c00020b40000002b500000006242001e6000074e000247092e7e6317000100e0003e818353288f50b79a0cc146c8024800000000000006b024032d23187d921e91805499d06883e72f190d4f768810000cfc95a1c90000610d180a005d0a08e7c89000011593c06b61078f8832225f0e222b53b002d23b992938e68b0f1077c87487948880007769ae3d1a70d3c631c0000b4c00095633b9830f2e112211913cd225cb42e000000065646414b0f6e7750001b640004f42ab9124eec97412400000403f1000276c00019a295240061263632e9a3c844546430015cb880d337818a44f073829720300003a030b01e06544bb3f6a55cf125193ce88ace866a33fc1064b2a8650728a3c0003d900006a13ac00047c00002fa0000001178af484218a9c0c00000041500000009af18993284b415c0a8145103070104808c80006170001d48d1447819601580009191a0844400000010400000000004a680011349ab0000200b0620d47500009b87482b60000ec40e400000000002fd0f680010b099b2c200009f22680000e243107511298000a9000000012c0a668470048c140000000000000a265e739297251d075a47a00008c49ce000065c58c5e200000006fe2eb35e00008261db29d1ea400000037717f815a32000000008180000000aa884a8771a89dc0ba49bf30a1aed07e8102d611ac3d24b440683f886c325000000053686e047a4c039400020a007046299c0000000a443453dd1e18f360004e4800005e9034d30bd934e4f000007701108c013500000040841b300000000002269378ae8383000000000000000008840000683c11d35184445037151526c2bc24d97a04540e04c91cd40340002a091e86ba000000127400057800000000005010f3800000000000000008140004360000ab805800000000000000001e4c0006ef45c80000008a92600ec11501ba4c98000fec2dd0002434a6a000000000000090245f80000000004ee227d1da5a005890f124e65b00001fc23c14d00000000ba6e500000000000003e716ec5f42c828c000000067a35819f8d480001408
  | 23 => 0xa5486a01013720f5406c96e0231ec434480600014240000733b48f989040000000000be00003ca8a50de62612fa96f4f1a32949e9d980000003c216706da5d32489fc4e522ac4dd000000a78e3019f3c5e20004e0806534a0bf2f221a4eac9d00a39ad4b2e26930f127000000024a02f48ae4c210e800004e00040f9c1c81a000000051521258500016c8c5612541080411b62d42551fa47a25300001d600d672d27102c8e2e6920001210ac26cc4bf000104012931d0a301ac5b708196688a62a8489a01517c63315b04d83e22ce4cc15b4e743c819a1bb0c0e48d2879c6918c2d62448df056293f213099d37a6cf3cd1b9911c7404cb8c443424090f0817cba818747e98849c61b30f800000007c4000202c00061543110a802c3470ae80000009a11e6a0e0000000000109c0001af3b980e0000000399043c5842020001a9400001b3d62484a9a2102ab1d140007d300009d00006702b000012ec0001388000bcc6f21ee8000bba0003da0ae52a06441e18c28e885d906688940de64f415a3ad0cc0500739a1934887a0db844cdd0055241899906c2b54b596406508560812250df82a443fa5102ea35748603cc86269400000011bc3ba277800097c0a8000217c00088911f13d854e4552149c8d116000000000055c00000000000003ee1318a544586020000da096a00013220c0efc82900018a00000002a5a61c2785374db99802ae8f2390800015800000009080001a30001cbc1da0002180000ce600014197d80004d338284b4a7a000014a2d12804ae2ac00011941c13831d405a280a0641bf4d1296a49a2200c3e8b540200000008532909aac00021b00026b45aa9b22850a6044c7d640b066025e08b33c0ce8ad61414de029cb5c1b811ea6141821372c712a4dac7a8039000046c5803bc80000005c502c8ee076e5b60000ff40000000508ec4e248f94508274520275104800069c84402282502ca0002f2948caf8189059838518e034092000000c1cf3df905c0000001e386f00004f701d25a4c4a0001e9000018e1d800003e45bc08e2e89718f281b51090b2c8425a62ae800000000011c0000ab60000001f492f874c4f100012aa5c040e0000b2480300022f4d588e229b033803e8873fda62800050d1c88d6104e00018a01b40000000621754ca086b00022ec7c867c1f4018c6082a63970928b66823400a5f46bc5a714994746ca081250a0ccfea49506e97d128a9610008be0c329081f29fb06e2000447a5651605be1199db508a31b0000000cae30814592bd29202e13624780007773c80bf8c588dc4ed1908f9a81a26280002fe47900009640000000469f6000085937580001dc0120b4a5500000001d707312ca000457000000000004d990ce260003698c341ae87b0001cd0fc6000000225c10c0000ca9b0107c882198946c9f4
  | 24 => 0x4101808fe0000000000bf855200000000000001b700000000000bc24b914850c38f80000000002bc9abc0000000001dbd1c268221a000000000000000005340003200000b1612a0000001344301061a3f8792000361a3d911a00717922bd2660c500014105a03a80059df00000003b087200783d60ed0cd89cc0000000000e627541d5800000000028880000003ce000274400006600016c4a700000000b1c0000002aa800107800017d800015600016c800048271d17817ec280704000056c0005eb0310af80a66262a48718a16323344087c83a5cd49113e111838c0b001d90a8540126a50800013a14f000077200007100000005dc19a8000db80001bc246d2144fc00000005682ca23894a4a0c77f32e01b0c5403d4f080011b40004ef000000095c0000e6499e730499203d2c460422c89c878c09200012808a815a270204c0000002e6000069e7c90000000ff20000658f50f8a1273a98ef800092400011a000067131da2c43d604b2da1dd0e3804e00005cc1f892b00000000000000aa800098600000000000000000001d5c00065542d9fcc0002551fb05dceb8554360a45c00029d0f500001842443f293c814866e0d8845cc380003b008f04da0002dc9d8c1b425b1518814c820001d20e580000000000560cc20003591a0101c1e516786ec0a45271510a7091c5a244b0000ec80cf12b800000000007188384407594700000f7259b48280003c023f05c092c00018000024a91c60431558000c2000000007ec2da00f00025745ce8860109478e100df0001498fbc8340b40ef0b1400000026a5240126000218504a7fa00000001924b945296180007eb00015b8e127aa00020880000003228000d5485200020ec6b20004ec9d1d0f80000cda5dc00025e47f800013e00042894f8f6c09a16496587f838d0fc00008a237e259a1a0c263723a30000ae20000001a5c99841e000064cfe434b4e207f10aa72733924f8dae09619397b094a925354800000004248fa7311ca0b732d11cce6e000127867cd705f3000000072e94100000000009d42788000f8e8b6014000132c58d00000010bc40f25112d88940260000000de22ed07f81105ae0004bd00000000000eb274c00021821b88d00002291af
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x14949750d315891001e2521d434c562440078c4874c9315891001e1621d534c162440078988750d30589100054c650709c95144001551931c2725451000558648709c951440018707660072545100054c650701c95144001551931c07254510006c8483845895144001b4120e0d625451005e98601621895144047361926024254510004d8e4983dc1514400195183dcf705451000654e0d73dc15144001b118350f7054510007445cd43dc151440018587660c75501100061c1d9811d540440019337421d5150110004d464c8754540440015519321d515011011d4c25d845454044001930876115150110005c464c7550540440018707660475481100054c650711d52044001551931c475481100065821e52545204400117297a1d51481100045ce4c8754520440011719321d51481100064cd0c8754520440019314321d5148110006586488754520440019633221d5148110006580c887545204404756192dd151481100045c26174545204400196087a09514811011d5825d8254520440013639160f7548110006c2e0d43dd52044001e096350f754811000558a5c81dd52044001721942077548110005d064c81dd52044001721941c77548110005d064c71dd52044001362989077548110004d8a6231dd52044001b41834c77548110007c050d31dd520440e94689758c75481100069260d631d52044001b098350c75481100078258d431d52044001a63766047548110006981d9811d5204400136393604754811000698d8d811d52044001a61636047548110006c8d0d811d52044001b21436047548110005c8650711d52044001741931c47548110004d8662411d52044001361988c47548110004d8661311d52044001560974c47548110006d060d311d52044001f01434c47548110006c854784595204400156297e17714811000558a5c85dc52044001363956137148110004d8e5583dc5204400136298d4f7148110006e0e0d43dc52044001d837350f7148110007c054d43dc5204400196087dd5514811005cd826175545204401736195e115148110686c895384545204400136297a1d5148110004d8e4e87545204400136193a1d5148110006c8d0e875452044001b2143a1d514811000598e598754520440017239461d5148110685c82518754520440017439361d514811066dd024d8754520440013629721d514811000658a5c8754520440019617621d5148110004d8e4c8754520440013619321d5148110006589cc8754520440019607321d5148110006c8d0c875452044001b214321d51481100065821f76545204400166396611514811011d982598454520441a1b20846115148110004d8e61745452044001360985d15148110004d8e6164545204407f36098591514811000cb82598550520440173a0985d14148110
  | 1 => 0x613219734c4654800190d8750d311952000683219434c46548001864865c531195200074150d714c46548001948865cd301952000552e45734c0654800154b97d8d30195200055265c634c065480017099418d3019520005d0644634c06548001d0973d0d30195200055265e434c065481f57099490d301952087f42dcd434c06548001d097350d3019520006c2219434c065481f3d0a7650d301952087f829d9434c0654800194973e053019520006c250f814c06548001d09435c530195200055265f314c0654800170994cc530195200055265d314c06548001d41714c53019520005832595350f644800150e9754d43591200054325d5350d644800160c9654d43591200074254d43dc1644800154a9754d30591200055225d534c164480155889750d305912000662a1d434c164480159888750d3059120005a2259434c16448001d0b7550d305912087f421d5434c1644800194b8354f705512000662e0d43dc15448001d095350f70551200054325d5350f6148225d0b7054d43d852088f421c15350f61480015489754d30d852076e62a1d434c361481d79888750d30d852087f421d5434c3614800164593187655852000643e1784dcd614800194b85e03735852000662e1380dcd614800188c87d8d435852000543a5d5350d614800150c9754d435852000643a1d5350d614800190c8754d43585200563121d634c561480015849750d31585200566121d434c56148001d095350f70585200076050d31dc161480158c887d8d305852000552a5d534c161480015489754d305852000652a1d534c161480159488754d305852000742dd1534c16148221d087454d305852000562a5d434c161480015889750d305852000662a1d434c161480159888750d305852000742dd5434c1614821fd087550d30585200557025d314c1614800190f8350e76d452000652e0d309db5148001d09434c276d452000643e0d439d95148001561918c2765452000652e0d309d95148001d09434c276545200041b660631d9514800184d8318c765452000519644631d9514800190d8350c76545200070318d431d9514800144c93584765452000558646301d95148001468964c076545200065260d301d95148001d09434c0765452000718d81101d951481a5961814407654520006c2e0d43d9760481fbd0b7350f65d812000652dcd831976048001b098350c65d812087742dcd43197604800194b8354d71d812000662e0d435c76048001d095350d71d81200076050d315c7604800741f9754d43d951000607dd5831d1654400909c985cd435951076d232497350d654400181e8754d435951000507a5d5350d644400181f85e13735891000507a5d5350d624400141c9754d435891000607a1d5350d624400181c8754d43589100052325d438c96244
  | 2 => 0x81fb60e921cd43d9520005856447350f65481fb619901cd43d952000607e0d435c7654800181e8750f31d95200070550d714c7654800741c9754d4359520006076117318c654800185573604631952000507e5f6350c654800141d9718d4319520005856446350c65480016459118d321952000643611730c8654800190d8750c3219520006515cd810c86548001b054360432195200060d611711846548001855835c4611952000649611710846548001945835c4211952000616219734c0654821da188650d301952088f035c95350f644800141e9754d43591200050725d5350d644800141c9754d43d852088f035c95350f61481e1c497254d30d8520767225c9434c3614800181f8350e76d452000607e0d439d9514800181d8350c76545200041b660321d9514800184d830c876545200070350c321d95148001465910c8765452000718c85101d95148001c612144076545200059164c61d9521480017099094d43d9520005c2652534c3654822d52a90dd274d952000643dd1839d3654800192b7460274d95200044be61741d3654800150d94cc373d95200055264e10dcf654800144e96e0d73d9520006515cd8118f6548001a456360463d952000652dcd8090f6548001d0a30dcd43d952000583a5b7350f6548001c0e96dcd43d9520005436477350f6548001c0f60dcd43d9520007428437350f654800160e961cd43d9520005c16447350f6548001709901cd43d9520005c16446350f654800190f8350d71d95200065160d71187654800190e8750f31d9520006c250d80cc76548001d05435c531d952000592a5b734c36548001c4a96dcd30d952000552647734c3654800164a961cd30d9520005c2650734c36548001741911cd30d9520005c2650634c365480017419118d30d952000742dcf434c3654800154a9790d30d952000742dcd434c36548001d097350d30d9520006c2219434c36548001b0943e0530d952000552e4d714c36548001d09435c530d952000552a5f314c3654800170994cc530d9520007505c5314c3654801550c9754d43595200074254d43dc165480155489754d305952000652a1d534c1654800198a8750d30595200566221d434c1654800150d94cc173195208ad5264e305cc6548001549938417319520006436117318c65480019457360463195200069158d8118c654822990d845ce4319520006525cd8090c654800160e96e0d4319520007428c17350c654800150f915cd431952089f03d817350c6548001d0a105cd431952000543e5f6350c654800150d9718d4319520005c16446350c6548001561918c1711952000649611711846548001945835c46119520006585c580904654800190d845cf31195200064361d43cc46548001949736033119520006c250d80cc4654800196171602311952
  | 3 => 0x410050765d5350f6250401a854360432d8941006a250d800cb625040741c9754d435972100698c81811d560c840141e9754d43583210050725d5350d60c8415c0d7254d435832189782c815350d60c85e1c497254d305832101e2621d434c160c85dba8a8250d3058321767225c9434c160c840741c9754d435952101e0721d5350d644841fc0c7254d43d8121006a250d808cb60485db48e92dcd43d954000417e617318f655000141d94cc373d95400041be6120dcf6550001c493048373d954000607613739cf655000160e92dcd43d954000703a4b7350f6550001c0d92dcd43d9540005076477350f6550001c0f20dcd43d9540007034837350f655000181e8750c32d95400068550d810cb6550001a194360032d954000607e0d435c7655000181e8750f31d954000513a4a865cc655000144d92a1973195406dd07a50865cc655000141c96611731954000607a19845cc655000151890611731954000507a5b415cc655000111d98101731954000507a58405cc655000151591101731954000516a58405cc65500015519110173195408bf12d81205cc6550001d08404817319540006076117398c655000b05d9361c63195406de07a117318c655000181c865cd431954000507e5f6350c655000105d97a0c611954000417e6173184655000184d73a086119540006135cd821846550001865825c46119540006075d18319662500018597060c659894002c172617354f615000181f7460c655854000607e0d439db5150001c314144276d454000607951831d9515000141d931d9545454000607e0d439d9515000105d98a0c765454000607a11831d9515000181d8460c765454000607a51831d9515000181d9460c76545400060760f431d9515000181d8350c76545400060760f411d9515000181d8350476545400060760e401d951500014359190076545400040f660401d9515000141d9310076545400060760c401d951500014359110076545400061360f201d9515000184d8348076545400070a101201d9515000185583c4076545400061660e101d9515000185583440765454000718c81101d951500018598344076545400070c505101d9515000141d931d97454540006071d983195415000741c9754d435972088f031c95350d65c8223c0c7254d435932088f031c95350d61c80078948750d315872076d4325d5350d65c80138c48758d315872076e6121d434c561c8223c0d7254d43d9520006155cd8118f65480016159118d43d952000591644634cb654800190e8750c32d9520006c150d810cb6548001855835c461d95207ee86219434c3654800181f7460e74d95200040fe61741d3654800141d94cc373d95207ed83a4b7350f6548001c0d72dcd43d952000703a4b7350f6548001c0d92dcd43d9520005076477350f654
  | 4 => 0x9c09100240000db06e29a000521a2000000000001e0000dd04210e64ca50150006a06d000000500cd8fc0666fc6201f27c0005c0c925e374a98220e63fc751582a2000bf0bf156414000001fc000000162fa280b891e0d2408400542d27a89c15f40c710f38000000007a911000124c393c000000da16e2ca000771800f0000560d50c2000000303165e41586d00059c000e80007b800000000000981030000009b05304e0000005700029c0007b0001d4e50003fc490ec8c13a83d01016d3243bc178db0007d40000000000000028048000000000003384790700078c0000028438c000340186604c8000002180000039e000000d400067cf89c81ec468c78d80004880014f0b4050d39153f24507288516c5ac0c9c13e824c9d81e14a7404e1a13b01c4769bc32a474491af2ba3cca49c0004084568811127781902a1e22a4b00aa0ca49432000210000d89940be3dc3f10a0b06e48691b0123007304504a5fc0e20028a6a823127212020000d40c0001a0140900005000120040b01403020020001800000004050000305005020100280800401000010000200c0002403008020a000000620280d008000e8010100104c1100c0600c00000010280507c02000010002503c0201002000050b0030080000c00000010080c01c1802c020240203c000380103c090000a0000402002094010100f058030140000c04050220040001c02040020080400801054000000500c000140b0080907c030700000802034000480001800000150342d00004000130000c0641c018000100000001000000cc0103db941d9754d43d895401e2521d434c56194a25e0b2054d435825201e2621d434c1609484f41c9754d43d8552025232497350d6590a25e0b2054d435824201d0725d5350d655080141d9395173d91518d50765d5350f645463541d9754d43d8951865832495350f6254401a0d8550c32d8951006a150d810cb6254401a894360032d895176d232497350f605463541d9754d43d81510040f662645cf645440141d9399173d9151005832496350f645440103f9761a40d91510040fa6064dcd645440141d9319373591510040fa60645cd645440141d9319173591510060e200645cd645440103e97219435915112c872616350d645440160c9258d4359151865832496350f6254401a0d8650c32d8951006c150d810cb6254401b094360032d89510070558d435c6625444941c9758d4358951865432497350c6254401839845c060189510061660d70180625444941d965cd43d8151865432497350f6054633517915cd43d81518c7051c56350f605440181f7660c74581510050764c74d8d605440141d931d1635815112c472617350d605461950c925cd435815100545e457350d605440181e8758d43581510054564c74dc5605440141f9754d43d89
  | 5 => 0x2581882899e3a612c4114b3ac0405d1ed06205c989ab3fe0a43a1fd164668f31740f80009a13d2026b0ed10f220314c2926000589019680226580798a3f46042518219e000000003080680002e1782542f000000000160000d04b4218000002100000009e000de96f000780a71760003307d87d274110000ec000258001121c46a43b000000250000d70a4000b3183000000001a02f46dc000c700a0008580007c6182a977000520820b41a2000f90002e06cc36000000000e91ad0ee2989581828e0007d00000038497000246000001181e4000720c32ea6241a85c0003281d813376000fc16c0c60000002d0000dc2e8f90000000000018425c5097c3463343c9c7000734f100400002c0000013a4c8698be0000002815e18c3700000039c22c00106000774681a50005642400021c104eb9f00d676c510e01bc2348f8000361e81d00025456c6404e136548571411be000488a30e44d45a8071140f02c96a1d25309b84d1d6038c609f3646d4ab800398000c40d23ec2ecef9613847ac001190fe5ec380002ac784238b0286510579e42266987e8000003e0f400033808c5413313c6e02d83f0005c8001551342390109800001837888320100fd84c0d4364000b13aa0d9021c6250540ad1390003582b0390002e40016411819c0180040a7f0e2800000000001213d8020d8000000000e19dc01a2ccf4800000000aa1782e66b8ce80022e0000e80032e004e880000058c0010c28c0001c1be014644f295c27e458d218e3ee6341e91c39272c33000196000f78900c04a4f988316e804130bd3323
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xb8300000949a007958000000001cb40180000a13000178000013800040000407c0a1105d1994c2401c2a6d607063420a3a3cb0c54a12a24844585241a040002200000062c1013c0040000603326400c8b9ac8a880240fa94837350f6550001224d0525432e632a8000a03a8a866117319540004a234248308b98caa0002909a8101205cc6550001680d0880902e632a8000a062819460c765454000602b06c8c803b2a2a000201da960c401d9515000180ac1b22200eca8a8000a0a6a040480765454000581346202403b2a2a000380983101201d95150001610d0880900eca8a8000e1060f20440765454000702306a0a203b2a2a000300d9850c321d95148001822c1b22190eca8a4000d0150d910c876545208b521541ba3073a6ca9045a12aa9dd1809d36548001c0243286b8a6232a4000c1160d9118c765452000501b5031a863b2a290002c05a118d431d951480018244b306980eca8a4000d02259434c07654520006226e8c990ea8a8088002911a321d845454044001888c9a8643aa290220008586a43221d5148110006283261910ea8a4088003901430c88754520440018244bb06b18ea902210eb0229d6350c75481100050c14eb1b023aa4088003a016350d811d520440018a04bb06988ea9022000cc0661434c47548110006a012ea1a623aa40880033039350e8754520440014a051aec43aa290220008586a47321d51481100050c34c3990ea8a4088003141931cc875452044001980c9a8643aa29022000e401cd4321d5148110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xa06628080388000b004809b0a8a866117319540004811b12819460c7654540004809ba60c40480765454000680183684404807654540006101a950c3221d5148110005800b758d436047548110006041a664c7321d5148110005101b91cd4321d5148110005801b61cd4321d5148110
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
  | 18 => 0xa0a
  | 19 => 0xa0c
  | 20 => 0xa0e
  | 21 => 0xa4a
  | 22 => 0xa4c
  | 23 => 0xa4d
  | 24 => 0xb09
  | 25 => 0xb0c
  | 26 => 0xb0d
  | 27 => 0xb0e
  | 28 => 0x1549
  | 29 => 0x154c
  | 30 => 0x154d
  | 31 => 0x154e
  | 32 => 0xb89
  | 33 => 0xb8c
  | 34 => 0xb8e
  | 35 => 0xbc9
  | 36 => 0xbcc
  | 37 => 0xbcd
  | 38 => 0x19c9
  | 39 => 0x19cc
  | 40 => 0x19cd
  | 41 => 0xd09
  | 42 => 0xd0a
  | 43 => 0xd0c
  | 44 => 0xd0e
  | 45 => 0x1609
  | 46 => 0x160a
  | 47 => 0x160c
  | 48 => 0x160e
  | 49 => 0xd49
  | 50 => 0xd4a
  | 51 => 0xd4c
  | 52 => 0xd4d
  | 53 => 0x1649
  | 54 => 0x164a
  | 55 => 0x164c
  | 56 => 0x164d
  | 57 => 0x1049
  | 58 => 0x104a
  | 59 => 0x104c
  | 60 => 0x98954
  | 61 => 0x94994
  | 62 => 0x98955
  | 63 => 0x98956
  | 64 => 0xa0954
  | 65 => 0x94a14
  | 66 => 0xb8954
  | 67 => 0x94b94
  | 68 => 0xbc954
  | 69 => 0xbc955
  | 70 => 0x94bd4
  | 71 => 0x1409
  | 72 => 0x128a
  | 73 => 0x1849
  | 74 => 0x1489
  | 75 => 0x180a
  | 76 => 0x130a
  | 77 => 0x14c9
  | 78 => 0x198a
  | 79 => 0x134a
  | 80 => 0x150992
  | 81 => 0x150994
  | 82 => 0x150995
  | 83 => 0x150996
  | 84 => 0x99514
  | 85 => 0xb8994
  | 86 => 0x98b94
  | 87 => 0xbc994
  | 88 => 0x98bd4
  | 89 => 0xbc995
  | 90 => 0x19c994
  | 91 => 0x999d4
  | 92 => 0x19c995
  | 93 => 0x209
  | 94 => 0x104994
  | 95 => 0x99054
  | 96 => 0x1a89
  | 97 => 0x1949
  | 98 => 0x1889
  | 99 => 0x409
  | 100 => 0x449
  | 101 => 0x1a09
  | 102 => 0xb0994
  | 103 => 0x98b14
  | 104 => 0x154994
  | 105 => 0x99554
  | 106 => 0xbcb
  | 107 => 0x19cb
  | 108 => 0xd0994
  | 109 => 0x98d14
  | 110 => 0x160994
  | 111 => 0x99614
  | 112 => 0xd4994
  | 113 => 0x98d54
  | 114 => 0x164994
  | 115 => 0x99654
  | 116 => 0x14b
  | 117 => 0x134b
  | 118 => 0xb9514
  | 119 => 0x150b94
  | 120 => 0xbd514
  | 121 => 0x150bd4
  | 122 => 0xbd515
  | 123 => 0x19d514
  | 124 => 0x1519d4
  | 125 => 0x19d515
  | 126 => 0x105514
  | 127 => 0x151054
  | 128 => 0x104b
  | 129 => 0xb1514
  | 130 => 0x150b14
  | 131 => 0x8a
  | 132 => 0xd1514
  | 133 => 0x150d14
  | 134 => 0x8d
  | 135 => 0xd5514
  | 136 => 0x150d54
  | 137 => 0x8e
  | 138 => 0xb8a14
  | 139 => 0xa0b94
  | 140 => 0xbca14
  | 141 => 0xa0bd4
  | 142 => 0x19ca14
  | 143 => 0xa19d4
  | 144 => 0x138d
  | 145 => 0x124d
  | 146 => 0x128d
  | 147 => 0x104a14
  | 148 => 0xa1054
  | 149 => 0x749
  | 150 => 0x14d
  | 151 => 0x198d
  | 152 => 0x134d
  | 153 => 0xbca54
  | 154 => 0xa4bd4
  | 155 => 0x138e
  | 156 => 0x124e
  | 157 => 0x128e
  | 158 => 0x104a54
  | 159 => 0xa5054
  | 160 => 0x180e
  | 161 => 0x130e
  | 162 => 0xd0b14
  | 163 => 0xb0d14
  | 164 => 0x160b14
  | 165 => 0xb1614
  | 166 => 0x40a
  | 167 => 0x188a
  | 168 => 0x1a0a
  | 169 => 0xd1554
  | 170 => 0x154d14
  | 171 => 0x20d
  | 172 => 0xd0b94
  | 173 => 0xb8d14
  | 174 => 0x140d
  | 175 => 0x1a8a
  | 176 => 0x194a
  | 177 => 0x14cd
  | 178 => 0xd0bd4
  | 179 => 0xbcd14
  | 180 => 0x160bd4
  | 181 => 0xbd614
  | 182 => 0x44a
  | 183 => 0x20e
  | 184 => 0x140e
  | 185 => 0x148e
  | 186 => 0x74a
  | 187 => 0xd4bd4
  | 188 => 0xbcd54
  | 189 => 0x164bd4
  | 190 => 0xbd654
  | 191 => 0x104bd4
  | 192 => 0xbd054
  | 193 => 0x184e
  | 194 => 0xd19d4
  | 195 => 0x19cd14
  | 196 => 0x1619d4
  | 197 => 0x19d614
  | 198 => 0x1a0d
  | 199 => 0x188e
  | 200 => 0x1a8b
  | 201 => 0x105654
  | 202 => 0x165054
  | 203 => 0xb89895c
  | 204 => 0x9894b9c
  | 205 => 0xbc9895c
  | 206 => 0xbc9499c
  | 207 => 0x9894bdc
  | 208 => 0xbc9895d
  | 209 => 0x94995
  | 210 => 0x94996
  | 211 => 0xb8a095c
  | 212 => 0xb894a1c
  | 213 => 0xa094b9c
  | 214 => 0xbca095c
  | 215 => 0xbc94a1c
  | 216 => 0xa094bdc
  | 217 => 0x94bd5
  | 218 => 0xe8e
  | 219 => 0x18ce
  | 220 => 0xecd
  | 221 => 0x1a4d
  | 222 => 0x99512
  | 223 => 0xbd5099c
  | 224 => 0xbc9951c
  | 225 => 0x15098bdc
  | 226 => 0x19d5099c
  | 227 => 0x19c9951c
  | 228 => 0x150999dc
  | 229 => 0x9c995
  | 230 => 0x9c996
  | 231 => 0xe8996
  | 232 => 0x18c996
  | 233 => 0xec995
  | 234 => 0x1a4995
  | 235 => 0x99254
  | 236 => 0xe89
  | 237 => 0xe8b
  | 238 => 0x18c9
  | 239 => 0x18cb
  | 240 => 0xec9
  | 241 => 0xecb
  | 242 => 0x1a49
  | 243 => 0x1a4b
  | 244 => 0x99256
  | 245 => 0x180996
  | 246 => 0x198995
  | 247 => 0x458d1
  | 248 => 0xe8451
  | 249 => 0xe9651
  | 250 => 0x44e91
  | 251 => 0x18c451
  | 252 => 0x18d651
  | 253 => 0xe9353
  | 254 => 0x75491
  | 255 => 0x14995
  | 256 => 0x74d11
  | 257 => 0x74e91
  | 258 => 0x1a9951
  | 259 => 0xe9951
  | 260 => 0x194e91
  | 261 => 0x19cbd1
  | 262 => 0xe8a
  | 263 => 0x18ca
  | 264 => 0x1a9952
  | 265 => 0x1a4a
  | 266 => 0xeca
  | 267 => 0x16ce
  | 268 => 0xe8bd3
  | 269 => 0x19cbd5
  | 270 => 0xe8153
  | 271 => 0xe89c99e
  | 272 => 0xec9c99d
  | 273 => 0xece91
  | 274 => 0xece93
  | 275 => 0xe9516
  | 276 => 0x98e96
  | 277 => 0x989d6
  | 278 => 0x98155
  | 279 => 0x99816
  | 280 => 0xece92
  | 281 => 0xe96d6
  | 282 => 0xe8ed2
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 68
  | 7 => 1650
  | 6 => 4553
  | 5 => 2534
  | 4 => 519
  | 3 => 48
  | 2 => 9
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
  | 8 => packedAt gbK8 (1922+((h/22+packedAt gbK8 (1768+(h % 22)*7) 7) % 82)*8) 8
  | 7 => packedAt gbK7 (67650+((h/550+packedAt gbK7 (61050+(h % 550)*12) 12) % 3187)*12) 12
  | 6 => packedAt gbK6 (238265+((h/1517+packedAt gbK6 (218544+(h % 1517)*13) 13) % 6010)*14) 14
  | 5 => packedAt gbK5 (159634+((h/844+packedAt gbK5 (149506+(h % 844)*12) 12) % 3345)*13) 13
  | 4 => packedAt gbK4 (38060+((h/173+packedAt gbK4 (36330+(h % 173)*10) 10) % 685)*11) 11
  | 3 => packedAt gbK3 (4000+((h/16+packedAt gbK3 (3888+(h % 16)*7) 7) % 69)*7) 7
  | 2 => packedAt gbK2 (840+((h/3+packedAt gbK2 (828+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc30fe3ffce10fc7e0fc70387f072084f8b3873
  | 1 => 0x3f0fc70301f0f8ff07803f87ff431b214c19f
  | 2 => 0xfc00ff803fe00ff0007ffc007f89c63c670e1c
  | 3 => 0xffff00003ffff000007fffff800e07c0780fe0
  | 4 => 0x3fffffffff800000000ff8007ff000
  | 5 => 0xffffffffc000000000000000000fffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x40012090820014120141088111200004811831
  | 1 => 0x1104421000100848008012024401092004086
  | 2 => 0xc400a90296200d20235258014b20c22c270a18
  | 3 => 0x2aaa0004295aa0004424a256000e0540580540
  | 4 => 0x208800083d9cca496e003012020f68007ea000
  | 5 => 0xb3ccd24f010880018800c0640c4fbffb000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeeafeeefec8fefefeeafeeefec8fefefeeafeeefec8fefefeeafeeefec8fefefeeafeeefec8fefefeeafeeefec8fefefeeafeeefec8fefefeeafeeefec8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36404
namespace PEqualNP.Outside.L_meta_36404
open PEqualNP.Outside.L_meta_36404.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 24 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 117 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 bs1_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 46 := (concat bs1_5_0 bs1_5_32)
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 16 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 13 := bs2_4_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 15 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_64 : Interval s3Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 68 := (concat bs3_3_0 (concat bs3_3_32 bs3_3_64))
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
theorem bs3_4_704 : Interval s3Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_736 : Interval s3Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_800 : Interval s3Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_832 : Interval s3Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_864 : Interval s3Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 894 := (concat (concat (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat (concat bs3_4_96 bs3_4_128) (concat bs3_4_160 bs3_4_192))) (concat (concat bs3_4_224 (concat bs3_4_256 bs3_4_288)) (concat (concat bs3_4_320 bs3_4_352) (concat bs3_4_384 bs3_4_416)))) (concat (concat (concat bs3_4_448 (concat bs3_4_480 bs3_4_512)) (concat (concat bs3_4_544 bs3_4_576) (concat bs3_4_608 bs3_4_640))) (concat (concat bs3_4_672 (concat bs3_4_704 bs3_4_736)) (concat (concat bs3_4_768 bs3_4_800) (concat bs3_4_832 bs3_4_864)))))
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
theorem bs3_5_704 : Interval s3Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_736 : Interval s3Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_800 : Interval s3Atlas 5 800 20 := block_range (n:=20) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 820 := (concat (concat (concat (concat bs3_5_0 (concat bs3_5_32 bs3_5_64)) (concat bs3_5_96 (concat bs3_5_128 bs3_5_160))) (concat (concat bs3_5_192 (concat bs3_5_224 bs3_5_256)) (concat (concat bs3_5_288 bs3_5_320) (concat bs3_5_352 bs3_5_384)))) (concat (concat (concat bs3_5_416 (concat bs3_5_448 bs3_5_480)) (concat bs3_5_512 (concat bs3_5_544 bs3_5_576))) (concat (concat bs3_5_608 (concat bs3_5_640 bs3_5_672)) (concat (concat bs3_5_704 bs3_5_736) (concat bs3_5_768 bs3_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 44 := (concat bs3_6_0 bs3_6_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 9 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 48 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_512 : Interval gbAtlas 4 512 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 519 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)))))
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
theorem bgb_5_2528 : Interval gbAtlas 5 2528 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2534 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)))))) (concat (concat (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888))))) (concat (concat (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 bgb_5_2432) (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)))))))
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
theorem bgb_6_4544 : Interval gbAtlas 6 4544 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4553 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)))))) (concat (concat (concat (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)))) (concat (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504)) (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664))))) (concat (concat (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792)) (concat (concat bgb_6_1824 bgb_6_1856) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)))) (concat (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 bgb_6_2080)) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))))))) (concat (concat (concat (concat (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368)) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)))) (concat (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 bgb_6_2656)) (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816))))) (concat (concat (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)))) (concat (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)) (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)))))) (concat (concat (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)) (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680)))) (concat (concat (concat bgb_6_3712 bgb_6_3744) (concat bgb_6_3776 bgb_6_3808)) (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968))))) (concat (concat (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 bgb_6_4096)) (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)))) (concat (concat (concat bgb_6_4288 bgb_6_4320) (concat bgb_6_4352 bgb_6_4384)) (concat (concat bgb_6_4416 bgb_6_4448) (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544))))))))
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
theorem bgb_7_1632 : Interval gbAtlas 7 1632 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1650 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))) (concat (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800))))) (concat (concat (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)))) (concat (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))) (concat (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_64 : Interval gbAtlas 8 64 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 68 := (concat bgb_8_0 (concat bgb_8_32 bgb_8_64))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeafeeefec8fefefeeafeeefec8fefefeeafeeefec8fefefeeafeeefec8fefefeeafeeefec8fefefeeafeeefec8fefefeeafeeefec8fefefeeafeeefec8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124266 * 2 ^ 32 + 4277075656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36404.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[0,4]⟩,⟨.or,[2,6]⟩,⟨.and,[5,7]⟩,⟨.and,[4,6]⟩,⟨.or,[0,2]⟩,⟨.and,[1,11]⟩,⟨.or,[9,10]⟩,⟨.or,[3,12]⟩,⟨.or,[13,14]⟩,⟨.and,[8,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277075656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277075656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36404

open PEqualNP.Outside.L_meta_36404 in
theorem PEqualNP.Outside.L_meta_36404 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277075656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277075656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
