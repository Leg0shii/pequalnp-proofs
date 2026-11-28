import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37445.Model
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


end PEqualNP.Outside.L_meta_37445.Model

namespace PEqualNP.Outside.L_meta_37445
open PEqualNP.Outside.L_meta_37445.Model
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

def SBf (j : Nat) : Nat := [4, 6, 7, 4, 7, 7].getD j 0

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

def mirrorSteps : List Move := [swapRows 84]

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

end PEqualNP.Outside.L_meta_37445

namespace PEqualNP.Outside.L_meta_37445
open PEqualNP.Outside.L_meta_37445.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfc07ffffffffffffffff01fffffffffffc3fff
  | 3 => 0xfff803fe01ff00ff007ffe07e03f01fc07cccc
  | 4 => 0xfffffc0001ffff00007ffff8003ffe0007f0f0
  | 5 => 0xfffffffffe000000007fffffffc0000007ff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x940924921451121252151628aa4552a551d555
  | 2 => 0x2b42492528a2a4a4a42a815554aaa54aa42aaa
  | 3 => 0x4d5762394d348ec836cfab06663331f036cccc
  | 4 => 0x726473b1b1c8c88ec773cd9c183cf860c770f0
  | 5 => 0x838783c1c1f0f0f0f87cf1e79f20c18307bf00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37445
namespace PEqualNP.Outside.L_meta_37445
open PEqualNP.Outside.L_meta_37445.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3149009000008618160384a008a0bf43de43bd43dd439d43be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x480823800101506182023aa921c7141438ea98811f548c23aa8186350e20c6a184195438432a86087808010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x1080002886050c20a418143043814308010
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 10
  | 2 => 3
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
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (228+((h/4+packedAt s1K4 (208+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s1K3 (282+((h/3+packedAt s1K3 (270+(h % 3)*4) 4) % 13)*5) 5
  | 2 => packedAt s1K2 (117+((h/1+packedAt s1K2 (114+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x7fff00ffff00fffff80fffc0fff81ffe71e3f
  | 3 => 0xf80ffff00ffff00fffff01fff03ffe07f9e3c7
  | 4 => 0xfff000000ffffff00ffffe00003ffff83e03f8
  | 5 => 0xfffffffff00000000fffffffffc000003ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x81210a0a2112121220b162d1445a2884a6cdb
  | 2 => 0x42a4aa694528ea4a45c0ab548aaa9156a5162d
  | 3 => 0x5688c94a694a48ec89d5819aa233544731a346
  | 4 => 0x64ce8d8d8e8c8c88eee6cd030c3c79e23e03b0
  | 5 => 0x870f0e0e0f0f0f0f0f78f1e3cf2061843fd800
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaa0aaa0aaa0a000aaa0aaa0aaa0a000aaa0aaa0aaa0a000aaa0aaa0aaa0a000aaa0aaa0aaa0a000aaa0aaa0aaa0a000aaa0aaa0aaa0a000aaa0aaa0aaa0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37445
namespace PEqualNP.Outside.L_meta_37445
open PEqualNP.Outside.L_meta_37445.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x5c354a1301400008000250024a00106c1263e28012347401300000005aa00070000000000088b18ac72a2abc027405c19038b0c8f4888b1e028c00600067c000000008702000110630a02ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff40fe40fd40fc40ff30fe30fd30fc30ff20fb20fe20fd20fc20f820ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x210c05e8f00000000000000000b11800ae002780000003c1151889250ac000000000ec1639000d6151f0009600439207e0d33000000a000002e1f000382207150000a0000000005d001a4f81a009b800500a0651400000004e6a00104005b2f0006a313d03cee6237894860000018400400000000004800ac4600000000000000ce1b00000520012000427b001c10c00248006c00420a00000001c400440e8480013001a000003a9f49a000011ce68500070000032800a6001c000a410271605a742e000008b001900000000d0003d3183000020400000004116476180017cf200000000000000005c3c00204002230130aa8e00150000000144000000078007e1ba20da0019000fe3a001b11a8300200002c018e4c2331316880030300041a06010000040002000201000502010003000205000000000300020000060204000006030100030201010200bb28e877551d0eeca321dd54643cea18875e53d0abaa7a15d94742baa8e857a50d0af2a1a14f94a42afa9a855c5350aeea2a15d14542bda8285785050a7ca4216b948429f2a6653d54ccaeca3995d54732bd286657950ccabca5196790a32ce214653f544ca78a8995dd4532ba28a657b504caf0a0995794832e7290659e420cb3884195794f41aea9e835e53906baa720ed504419f2a6633d54cc67ca918cf55231ea98863b642c87688590f58cb21ea196433e548867aa910d794e21aea9c437651886f4a110de542219faa2433c54486bea690d714d21bda82437850486eca410f994821db21043b442087ac6410f50c821afa9a815c53502dea4a05b14940bba8a817451502bca6205754c40bb2888175511027ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2eca2185d54430dd21641b842c83b46590760cb20f990e41f021c827ca9104f55220af29c415d53883588510730ca20bb28c417551883c843105e942209faa2413c54482bea6905714d20bba8a417451483588410730c820f2108417a52083d4a4107ad0820dd21041b842083d084106a10820f599041da32083b064107a0c820e419041f321083d442107a08420f810841e0210827ea8884f15110afa9a215c53442dea4885b149109f2a0213d54042bca6085754c10
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x28038290050001e48001a61600c70688010042020010c0018b84420c821b298f42082e261d0820aa98a42082aa64cc820b898732082ca628c820e210a320838a420c820e210832083a042c8420f00cb21082aa6488420b298e21082e26188420e890821083a04208420f08c821083c03208420
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 144
  | 3 => 19
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
  | 5 => packedAt s2K5 (880+((h/16+packedAt s2K5 (768+(h % 16)*7) 7) % 69)*7) 7
  | 4 => packedAt s2K4 (4272+((h/48+packedAt s2K4 (3888+(h % 48)*8) 8) % 251)*9) 9
  | 3 => packedAt s2K3 (752+((h/6+packedAt s2K3 (722+(h % 6)*5) 5) % 29)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffc07fffffffffffffe03ffffffffff87fff
  | 1 => 0x1fffff803fe01ff00fffffc07f01fc07ff98c7
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xe0ffffffc0001ffff00fffff8001fff80fe0f8
  | 5 => 0xffffffffffe000000ffffffffe00000fff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8412f412493145192922b025cb532d4a982b5b
  | 1 => 0xa82554f61354cb28ea45f2e0553154c7ab98c5
  | 3 => 0x10498124a28292424489454aa6a49a9545d5ae
  | 4 => 0x1d8e26473b1b1c8c88ee79b340c1e3e18ee0f0
  | 5 => 0xdef038783c1c1f0f0f0f9e3c78f903060f7e00
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xee00aa00aa008800ee00aa00aa008800ee00aa00aa008800ee00aa00aa008800ee00aa00aa008800ee00aa00aa008800ee00aa00aa008800ee00aa00aa008800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37445
namespace PEqualNP.Outside.L_meta_37445
open PEqualNP.Outside.L_meta_37445.Model
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
  | 3 => packedAt s3K3 (6+((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfff00fffe01fffc07c0fff81ffe07ff0139e7c
  | 1 => 0xffff01fffe03ffffff01ffe07ff81fffce38f
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x929a68c631d2a48a9e097390cce43390d18e3c
  | 1 => 0x84a8aa4a5251a91a2e5814b2452c91a554a285
  | 2 => 0x284141108484122040a2a9451251444a8a555a
  | 4 => 0xce8d8d9d191923b3773cd061879e78831f03e0
  | 5 => 0xf0e0e1e1e1e3c3c7bcf1e79e418610c1ff800
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xe0e0e0e0e0e0c0c0e0e0e0e0e0e0c0c0e0e0e0e0e0e0c0c0e0e0e0e0e0e0c0c0e0e0e0e0e0e0c0c0e0e0e0e0e0e0c0c0e0e0e0e0e0e0c0c0e0e0e0e0e0e0c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37445
namespace PEqualNP.Outside.L_meta_37445
open PEqualNP.Outside.L_meta_37445.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x80058000004e38000123ca983830400000030244441a5241001d142c3a93678b232e7d51a5a14a20320520d008400056989a800000060830cd440042000188440ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xb001540000d8343d08fd48790cd08458e8881c6d68ac05714000b40000944401889930000144f4002c0ced50180068bc000000240174b8a449843920017d79189c5c00702001140100f0000139580028d4dcf850013d2d352864083000a8000001100054c4e4748cc810e081644d24c040607d811ca090016d5c14014ccd6104000402080000000e0a06060240020c00020616001206141e240814200612020600257b5050ef0a0a1dd94742baa8e855e5310abaa6214fd51329e2a26577514cae8a2995ed4132bc282653e540ca7aa8194f943419eaa483b75150678a0a0cf950419f2a4633d548c6f4a118de542319f2a0633d540c76a8390cf952219eaa4433e540867aa810d794c21aea9843b541086f4a010de54021af29e815d53d027aa3204f94240afa9a815c53502eca2205d54440db288813d511036aa2204d544409f28081ba501027ca9984f55330dc206619f418c33a83185794230cf204619c408c27ea8984f15130dc200619f410c33a82185794030ed28061db400c33c80186710030ec2006198400c27ca9904f55320af29e415d53c83b061904fd51209e2a2415f53482b8a6905dd4520ba28a41d8300827ca9884f55310af29e215d53c436a83884fd52109e2a421d8308427ea8884f15110afa9a215c53442dea4885b14910daa0a21d8304427ca8084f55010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1411e01a21600a98072860001000038c9000220804a00001800042410001e586054c42cc50550086b16110330a5584408c2b16110030a6181410c29a6090030a5584400c2d16110030e4984400c2996110030e4584400c29161100308d58654c831a540c320c615030842346550510c91494144318540c110d21483044391410c110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8405117195030c82883aa8218221c0149410c110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s4K5 (826+((h/15+packedAt s4K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s4K4 (2937+((h/33+packedAt s4K4 (2673+(h % 33)*8) 8) % 130)*8) 8
  | 3 => packedAt s4K3 (840+((h/7+packedAt s4K3 (798+(h % 7)*6) 6) % 33)*6) 6
  | 2 => packedAt s4K2 (149+((h/1+packedAt s4K2 (147+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc07ffc07ffff0383fffff81ff83ffe00fe73fc
  | 1 => 0xff81fff81ffffffc0fc0ffe0ffc3ffff638c7f
  | 2 => 0xffffffffe07ffffff000fffffffc1fff83ff8f
  | 3 => 0x1ffffff8003ffffff0000ffffe003fc0ff0
  | 5 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x530c447145122480b2c93909380532182e31bc
  | 1 => 0x8524c890c824619405584b284a4354a9628455
  | 2 => 0xa111122034882295020945294a80952815a8a
  | 3 => 0x2c59a244920ecb4e69b20610e7328063d40f60
  | 5 => 0x3061c3871c70f3f38e3ce79c06231183fbe000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeae0eae0e8c0e8c0eae0eae0e8c0e8c0eae0eae0e8c0e8c0eae0eae0e8c0e8c0eae0eae0e8c0e8c0eae0eae0e8c0e8c0eae0eae0e8c0e8c0eae0eae0e8c0e8c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37445
namespace PEqualNP.Outside.L_meta_37445
open PEqualNP.Outside.L_meta_37445.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x260000300005122e0000000014060e9429e00200000000c9542000005670c001c0162d009910904000270010a0000006a90090880020000b007402a368c0000000d000000000007c7a018000002c4004003000000500001030010000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc3448005c00520076000064883066009eb0acbe100a6a8cb65e545640841c202e78a0327a04604a3a029a2800148eba1a2a6e081e0044382400008a164e820096003e0000c4a63c00809c00180098a82cbc687036947c00aa58a4a2b85a06ae7e50c0009212b474904c26c2726c228600b242460e00620001c06021c2810810001007000000acb880430006060410100384140f7b5050ef0a0a1dd94742baa8e855e5310abaa6214fd51329e2a26577514cae8a2995ed4132bc282653e540ca7aa8194f943419eaa483b75150678a0a0cf950419f2a4633d548c6f4a118de542319f2a0633d540c76a8390cf952219eaa4433e540867aa810d794c21aea9843b541086f4a010de54021af29e815d53d027aa3204f94240afa9a815c53502eca2205d54440db288813d511036aa2204d544409f28081ba501027ca9984f55330dc206619f418c33a83185794230cf204619c408c27ea8984f15130dc200619f410c33a82185794030ed28061db400c33c80186710030ec2006198400c27ca9904f55320af29e415d53c83b061904fd51209e2a2415f53482b8a6905dd4520ba28a41d8300827ca9884f55310af29e215d53c436a83884fd52109e2a421d8308427ea8884f15110afa9a215c53442dea4885b14910daa0a21d8304427ca8084f55010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1001100f08d1470080000040ca30605350b00e00024048600420a02586054c42cc50550086b16110330a5584408c2b16110030a6181410c29a6090030a5584400c2d16110030e4984400c2996110030e4584400c29161100308d58654c831a540c320c615030842346550510c91494144318540c110d21483044391410c110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x20405117195030c82883aa8218221c0149410c110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s5K5 (841+((h/15+packedAt s5K5 (736+(h % 15)*7) 7) % 96)*7) 7
  | 4 => packedAt s5K4 (2904+((h/33+packedAt s5K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s5K3 (833+((h/7+packedAt s5K3 (798+(h % 7)*5) 5) % 30)*6) 6
  | 2 => packedAt s5K2 (150+((h/1+packedAt s5K2 (147+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc07ffc07ffff0383fffff81ff83ffe00fe73fc
  | 1 => 0xff81fff81ffffffc0fc0ffe0ffc3ffff638c7f
  | 2 => 0xffffffffe07ffffff000fffffffc1fff83ff8f
  | 3 => 0x1ffffff8003ffffff0000ffffe003fc0ff0
  | 4 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x530c447145122480b2c93909380532182e31bc
  | 1 => 0x8524c890c824619405584b284a4354a9628455
  | 2 => 0xa111122034882295020945294a80952815a8a
  | 3 => 0x2c59a244920ecb4e69b20610e7328063d40f60
  | 4 => 0x3061c3871c70f3f38e3ce79c06231183fbe000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeae0e8c0eae0e8c0eae0e8c0eae0e8c0eae0e8c0eae0e8c0eae0e8c0eae0e8c0eae0e8c0eae0e8c0eae0e8c0eae0e8c0eae0e8c0eae0e8c0eae0e8c0eae0e8c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37445
namespace PEqualNP.Outside.L_meta_37445
open PEqualNP.Outside.L_meta_37445.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x210058018c300c831c3b38d8401027a0007800020026b83f2a0c9242843a8a01b8000b800200000472c3260029400241d49a5544025806a6643c660222861513187cd8d2a00000000000000011830e06085010000102140008e0214000000405fe54007f55005fc54017fd0c01fe43007f50c05fc43017fd0803fe42007f50803fc42007fcc803fe32007f4c803fc32017fd0401fe41007f50405fc41007fcc401fe31007f4c401fc3100ffc8401fe21007f48403fc21017fd0001fe40007f50005fc40007fcc001fe30007f4c001fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1c2000bfd8e10007fcc708002fe6384001feb1c2000bf58e10007f8c708002fc6384013ffa1c2000ff90e10007fa8708027fc4384001ffb142000bfd8a10047fcc508006fe6284001feb142000bf58a10047f8c508006fc6284013ffa142008ff90a10007fa8508023fc4284001ff9942008ff8ca10007fa6508023fc32840017eb0c2009ffd061001ffc8308003fd4184007fe20c2000ffcc61001ffc6308003fd3184007fe18c2008ffc861001ffc4308003fd2184007fe10c2003bf9821004ffe8108003fe4084001fea042009ff10210007fe6108003fb3084001ff1842000ff4c210007f86108003f83084011ff9042000ff88210007f44108003fd2084001fc9042008ff0821001ffe2108003f71084007fd8842000ffd9110005fec888003bf64440015fb222007ff99110015fcc888003fd64440017eb222007ff19110015f8c888003bc64440055e3222007ff95110007faa88801ffc5444001ffb1a2000bfd8d10007bec688002df6344001ff31a2000bf98d10007fac688002fd6344001fe31a2000bf18d10007b8c688002dc634400fffa1a2000ff90d10007fa868801ffc4344001ffb122000bfd8910007dec488002ef624400dff3122001bf98910007fac488002fd624400dfe3122001bf18910007d8c488006ec624400fffa122006ff90910007fa848801bfc4244001ff9922006ff8c910007fa648801bfc324400fffa0a2003ff90510007ec8288003fd4144001faa0a2003ff10510007fe628800ffe3144001fe98a2003ff0c510037fe428800ffe2144001fe90a2003ff0851003ffe8088003fe4044001fea022007ff10110007fe6088003fb3044001ff1822000ff4c110007f86088003f8304400dff9022000ff88110007f44088003fd2044001fc9022006ff0811001ffe208800ffb1044001ff0822000fd8411001ffec80800eff6404007ff3202002bf9901001f7cc80800abe6404007feb202000bf5901001f7ac808002bd6404007fe3202003bf1901002ffca808003fd540400bfe2a02003ffd8c1001dfec60800ffe63040017f3182003ff58c10005fac60800ffc63040077e3182005ffd0c10007fc8608003fd430400bfe2182003ffd881001dfec40800ffe62040037f3102003ff58810005fac40800ffc62040077e3102005ffd0810027fc8408003fd4204009fe2102000ffcc810027fc6408003fd3204009fe1902003bf9841001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff08410005fcc008017ff4004001ff2002000ff5001002ff88008003ff3004001ff1802000ff4c010007f86008013ff2004001ff1002000ff48010027f8400800fff1004007fb8802003ff8401001ff4200800ffd1004001fa8802003fe44010
  | 1 => 0x3fd400c01ffe2006000ffcc030007be6018003fe300c001fd1806000ff4c030007ba6018003f9300c01dff900600efec8030077f8401803bf8200c001ffb244000bfd922006ffcc91000afe6488001feb244000bf5922006ff8c91000afc648801bff2a44000ff5522006ff8a910003ff63880017fb1c4000ff98e20005fcc710003fd63880017eb1c4000ff18e20005f8c710037ff4388001ff21c4000ff50e2006ff88710006fd6288003ffa144001ff90a2000ffa8510007fc4288003ff9944001ff8ca2000ffa6510007fc3288001ffb0c4000ff9862001dfcc310003fd61880017eb0c4000ff1862006ffe8310003fe4188001fea0c400dff10620007fe6310003fe3188001fe98c4000ff0c62000ffe4310007fe2188001f710c4001ff4862000ff84310007ec21880037f304400dffd0220007fc8110003fd408801bfe2044000ffcc220007fc6110003fd3088001fe1844001ffc822000fde4110007fb2088003fe1044001fe08220007fec890002ff6448019ff3224002bf99120007fac890002fd6448019fe3224002bf19120067fca890003fd5448019fe2a24000ffd8d20005fec690003fe63480017f31a4000ff58d20005fac690003fc63480017e31a400cffd0d20007fc8690003fd4348019fe21a4001bfd892000ffe8490007fe4248003fea124001ff1092000ffe6490007fe3248003fe9924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c29000efc6148019ffa0a4000ff90520007fa8290033fc4148001ff98a4000ff8c520007fa6290003fc3148003ff90a4001ff8852000ffa4290007fc21480037fb02400cffd0120007fc8090003fd4048019fe2024000ffcc120007fc6090003fd3048001fe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f82048007ffb262003bfd931001ffcc98800afe64c4007feb262000bf5931001ff8c98800efc64c4017ff2a62000ff5531005ff8a98800fff63c40077fb1e2003ff98f10005fcc78800ffd63c40017eb1e2003ff18f1001df8c78802fff43c4001ff21e2000ff50f1005ff8878800fff62c40077fb162003ff98b1000dfcc58800ffd62c40017eb162003ff18b1001df8c58802fff42c4015ff2162000ff50b10057f88588003ff32c4015ff1962000ff4cb10057f8658800fff41c4007ff20e2003fd9071001ffa8388003f541c4007fe20e2003ffcc71001ffc638800ffd31c4007fe18e2003ffc871001ffc438800ffd21c4007fe10e200bffd0310007fc8188003fd40c4017fe2062000ffcc310007fc6188003fd30c4001fe186200affc8310007fc4188003fd20c4015fe1062000ffd9210005fec908027fe64840057f3242000ff59210005fac908027fc64840057e3242009ff95210007faa908027fc5484001ffb
  | 2 => 0x300a7f8c598006fc62cc02bffa166014ff90b30007fa8598053fc42cc001ff9966014ff8cb30007fa6598053fc32cc001ffb0e6000ff9873001dfcc398003fd61cc0017eb0e6000ff187300affe8398003fe41cc001fea0e6015ff10730007fe6398003fe31cc001fe98e6000ff0c7300a7fe4398003fe21cc001fe90e6014ff087300affe8198003fe40cc001fea066015ff103300a7fe4198053fb20cc029fe1066014fe08330007fec918002ff648c027ff3246002bf99230007fac918002fd648c027fe3246002bf1923009ffca918003fd548c027fe2a46000bf58e3009ffe871804fdf438c001ff21c6000ff50e3009ff8871804fdc438c001ffb146012ff98a3000dfcc518003fd628c0017eb146012ff18a3000df8c51804fff428c025ff2146000ff50a30097f88518003ff328c001ef9946012ff8ca30007fa6518003dd328c025fe1946000ffd8630007fcc31800efe618c001feb0c6000bf58630007f8c31804fff418c001ff20c6000ff5063009ff88318003ff318c001ff18c6000f78c630007fa6318003fc318c001ee18c6012ffc8630007fc4318003fd218c025fe10c6000bf9823009ffe8118003fe408c001fea046013ff10230007fe6118003df308c001fd9846012ffc8230097f84118003ff644c0017fb226000efd91300057ec898047fe644c0057f3226000ff59130005fac898047fc644c0057e3226000ef1913001578c898047fe544c001feaa26011ff1513008ffe8698003fe434c001fea1a6011ff10d30007fec498002ff624c021ff3126001bf98930007fac498043fc624c0037e3126011ffd0930087fc8498003fd424c021fe2126000ffcc930087fc6498003fd324c021fe1926000ffd8530005fec298003fe614c001feb0a6000ff1853001df8c298047ff414c001ff20a6000ff5053008ff88298003ff314c001ff18a6000ff4c530007f86298043ff214c001ff10a6000ff48530087f84298047ff404c001ff2026000ff5013008ff88098003ff304c001fd9826000ff8c130007bc6098043ff204c021fe1026000ffd9030005fec81803ffe640c0057f3206000ff59030005fac81803ffc640c0057e320600fff95030007faa81803ffc540c0017f318600fffd0c3007fbe8618003fe430c001fea18600fff10c3007fb88618003ff620c01dff3106001bf98830007fac418002fd620c01dfe3106001bf1883007ffe841803bfe420c001fea10600eff10830007fe6418003df320c01dff1906000ff4c830007ba641803bfc320c001ffb086000ff9843001dfcc218003fd610c0017eb086000ff1843007ffe8218003fe410c001fea08600fff10430007fe6218003fe310c001ef1886000ff4c430007f86218003dc310c01dff9086000ff88430007fa421803bfc210c0017f300600fffd0030007fc801800
  | 3 => 0xf98a4203ff8c521007fa629080ffc3148403ff90a4201fdc852101ffc429080fee2148407fe10a4203fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc60484017e302421bffd01210dff88090807ff2048403fe1024200ffd9640005fecb2006bfe65900317f32c8000ff59640005facb2006bfc65900317e32c8002bf59240017fea92006bbf5490005ff2a48002ff55240017f8a92000bbc5490001ffb1c8000ff98e40005fcc720003fd63900017eb1c8000ff18e400d7fea720003fe5390001fea9c801aff14e40017fe872000bfe4390001df21c8002ff50e40017f8872000bbc4390001ffb148019ff98a4000dfcc520003fd62900017eb148019ff18a4000df8c52006bff5290033ff2948000ff54a400cff8a52000bff4290005dfa148002ff90a40017fa8520003bd4290005fe2148000ffcca400cffc6520003fd3290033fe1948000ffd8640007fcc32000efe6190001feb0c8000bf58640007f8c32006bff5190001ff28c8000ff546400d7f8a32000bff4190005ff20c8000ef90640017fa832000bfc4190005de20c8000ffcc640007fc6320003fd3190001fe18c8019ffc8640007fc4320003fd2190033fe10c8002bf982400d7fea120003fe5090035fe2848002ffd02400177e812000bfb4090005fe2048002fe102400cffe4120067fc2090001ffb2a8000bfd9540006fecaa00027f655002fff32a8018bf99540007facaa0002fd655002ffe32a8018bf19540006f8caa00627c65500057fb228002ffd5140017fca8a000bbe5450005feaa28000ef55140017f8a8a0003ff63500017fb1a8000f7d8d40005bec6a0003fe6350001feb1a8000ff18d40005f8c6a0003dc63500016e31a8017ffd4d40007fca6a0003fd535002ffe29a8002ffd0d40017fc86a000bfd4350005fe21a8000ffd8940005fec4a005bfe62500037f3128000ff589400b7f8c4a0006fc625002fffa928016ff94940007faa4a005bfc5250005ffa128002ff90940017fa84a000bfc4250001ff9928016ff8c940007fa64a005bfc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8003bf185400bffea2a0003fe5150001fea8a8017ff14540017fe82a000bbf4150005ff20a8002ff505400077a82a000bfc4150001ff98a8000ff8c540007fa62a0003fc315002dff90a8000ff88540007fa42a005bfc21500057fb028017ffd4140007fca0a0003fd505002ffe2828002ffd0140017f680a000bfe4050001df2028002ff101400177880a000bf8405002dff9028016ff08140007fec998002ff64cc02bff3266002bf99330007fac998002fd64cc02bfe3266002bf193300affca998003fd54cc02bfe2a66015ffd0f30007fc8798003fd43cc02bfe21e6000ffd8b300a7fcc598006fe62cc001feb166000bf58b
  | 4 => 0x80fdf318c401fb98c6203ffc863101ff8431880fff608c407ff3046200bf9823101ff4c118802fa608c407feb046200bf5823101ff2c118802f9608c407fe3046222ffd0231117f88118887ff208c443fe1046200ffd9131005fec898883fe644c4057f3226200ff59131005fac898883fc644c4057e3226220ff95131007faa898883fc544c441ffa1a6200ff90d31007fa8698883fc434c401ffb126200bfd89310fffcc498806fe624c401feb12621fff1893100df8c498883ff424c43fff2126200ff509310fff88498803ff324c401ef992621fff8c931007fa6498803dd324c43ffe1926220ffd053101ffc8298803fd414c407fe20a6200ffcc531007ee629880ffe314c407ef18a621fffc853101ff84298803ff604c4017fb026200ff98131007fac098803fc604c4017e3026220ffd0131107f8809887fff204c43ffe1026203ffd903101dfec81880ffe640c4057f3206203ff59031005fac81880ffc640c4077e320621eff95031007faa81887bfc540c4017f318621effd0c31007fc8618803fd430c43dfe2186203ffd883101ffcc418806fe620c407feb106200bf5883101ff8c41880efc620c43dffa10621dff90831007fa8418877fc420c401ff990621dff8c831007fa6418877fc320c4077f3086203ffd043101ffc821880ffd410c407fe2086203ffcc43101fbe621880ffe310c407fb1886203ff4c43101fba6218803f5310c407ff908621dfdc843101ff8421880ff4210c407ffb006203ff98031005fcc01880ffd600c4017eb006203ff180310f7fe801887bfc400c43bff900621dff0803101ffec91080eff6488407ff3244202bf9922101ffac910802fd6488407fe3244203bf192210e7fca910803fd5488439fe2a44203ffd8e2101dfec71080ffe63884017f31c4203ff58e21005fac71080ffc63884077e31c421cffd0e21007fc8710803fd4388439fe21c4201bf58a2100ffe8510807fe4288403fea144201ff10a2100ffe6510807fe3288403fe9944201ff0ca2101dfcc31080fff4188407ff20c4203ff5062101ff8831080fff3188407ff18c4203ff4c62101ff8631080fff2188407f790c4201fdc862101ff8431080ff42188407ffb044203ff98221005fcc11080ffd60884017eb044203ff182210e7fe8110873fc4088403ff9044201ff0822100fd84110803ff64484017fb22421bff99121015fcc890803fd64484017eb22421bff19121015f8c89086ffe5448401feaa2421bff15121007fec690802ff6348401ff31a4200bf98d21007fac690802fd6348401fe31a4200bf18d210dffe8690803fe4348401fea1a421bff10d2101dfec490807ff4248403ff2124201ff5092100ff88490807ff3248403ff1924201ff4c92100ff86490806ff6148437ffa0a4203ff90521007fa829080ffc4148401f
  | 5 => 0x8e41147fea720803fe5390401fea9c8228ff14e41017fe872080bfe4390405fea1c8202ff10e4101ffec52080ffe62904037f3148203ff58a41005fac52080ffc62904077e3148228ffd4a4113ffca520803fd529044ffe2948202ffd0a41017fc852080bfd4290405fe2148200ffcca4113ffc6520803fd329044ffe1948203bf9864101ffea32080ffe5190407fe28c8203ffd064101f7e832080bf74190407fe20c8203fd1064101ffe432080ffc2190407ffb048203ff98241005fcc12080ffd60904017eb048203ff18241147fea1208a3fc5090405ffa048202ff1024101778812089fff209044ffe1048200ffd9541005fecaa089bfe65504317f32a8200ff59541005facaa089bfc65504317e32a8203bfd9141017fea8a089bbf5450405ff2a28202ff55141017f8a8a080bbc5450401ffb1a8200bfd8d41007fcc6a0803fd6350401fe31a8200bf18d41137fea6a0803fe5350401fea9a8226ff14d41017fe86a080bfe4350401df21a8202ff50d41017f886a080bbc4350401ffb128200bfd894112ffcc4a0806fe6250401feb128225ff1894100df8c4a089bff525044bff2928200ff5494112ff8a4a080bff4250405dfa128202ff90941017fa84a0803bd4250405fe2128200ffcc94112ffc64a0803fd325044bfe1928202bfd8541137fea2a080ffe5150401fea8a8203ff14541017fe82a080bf74150407ff20a8203ef9054101ff882a080fbc4150405fa20a8225ffc854101ff842a0803ff60504017fb028200ff98141007fac0a0803fc60504017e3028226ffd4141137f8a0a080bff4050405dfa028202ff1014112ffe40a0897fc2050401ffb266200bfd9331127fcc99880afe64cc401feb266200bf59331127f8c99880afc64cc449ff2a66200ff55331127f8a998893ff43cc401ff21e6200ff50f31127f88798803ff62cc447ff3166201bf98b31007fac598802fd62cc447fe3166201bf18b31127fe859888ffe42cc401fea166223ff10b31007fe6598803df32cc447ff1966200ff4cb31007ba659888ffc32cc449ffa0e6203ff90731007fa839880ffc41cc447ff90e6223fdc873101ff8439888ff421cc401ffb066200ff98331005fcc198803fd60cc4017eb066200ff18331127fe8198893fc40cc447ff9066223ff0833101ffec91880eff648c407ff3246202bf9923101f7cc91880abe648c407feb246200bf5923101f7ac918802bd648c407fe3246203bf19231117fca918803fd548c445fe2a46200bf58e31117fe8718803fe438c401fea1c6222ff10e3101ffec51880ffe628c4037f3146203ff58a31005fac51880ffc628c4077e3146222ffd0a3110ffc8518803fd428c443fe2146200ffcca3110ffc6518803fd328c443fe1946203bf9863101ffe831880ffe418c407fea0c6203ff1063101ffe6318
  | 6 => 0x5ffa0a8602ff10543167fe42a18b3fc2150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028600bf1814316ffea0a18b7fc5050c05ffa028602ff10143167fe40a18b3fc2050c01ffb2a8400bfd954215ffccaa1062fe6550801feb2a8400bf5954215ff8caa1062fc65508037fb228402ffd5142017fca8a100bbe5450805feaa28400ef55142017f8a8a1003ff63508017fb1a8400ff98d42007fac6a1003fc63508017e31a842bffd4d42007fca6a1003fd5350857fe29a8402ffd0d420177e86a100bfe4350805fea1a8400ef50d42017f886a1006ff6250803ffa928401ff9494200ffaa4a1007fc5250803ffa128402fbd094200ffc84a1007be4250803fe2128401ef1094200fd884a1007fe3250803fe1928400ffd8542005fec2a1003fe6150801feb0a8400ff1854201df8c2a10afff5150857fe28a8402ffd05420177e82a100bfc4150803ff90a8401ff08542007fec0a1002ff6050801ff3028400ff58142007f8c0a1002fc6050857ffa82842bff14142017fe80a100bfc4050805de2028401ffc814200ff840a1003ff64cc8017fb26642aff99332015fcc999003fd64cc8017eb26642aff19332015f8c9990abfe54cc801feaa6642aff1533200dfcc7990abff43cc801ff21e6400f790f32007fa8799003dd43cc855fe21e6401bf58b3200ffe8599007fe42cc803fea166401ff10b3200ffc6599007de32cc803f71966401ff0cb3200fb86599003ff61cc801ff30e6403bf98732007fac399002fd61cc801fe30e642affd0732157f88399007ff21cc803fe10e6400ffd8332007fcc199002fe60cc801feb066400bf58332007f8c1990abff40cc855fe2066401ffc833200ff84199003ff644c8017fb226400efd91320057ec8990a7fe644c8057f3226400ff59132005fac8990a7fc644c8057e3226400ef1913201578c8990a7fe544c801feaa26429ff1513200dfec6990a7ff434c801ff21a6400f790d32007fa8699003dd434c853fe21a6401bfd893200ffe8499007fe424c803fea126401ff1093200ffe6499003ef324c803ff1926401f78c93200ff86499007dc324c803f61926400ffd8532005fec299003f7614c8017bb0a6400ff98532007fac299003fc614c8077e30a6400fd18532005e8c2990a7ff414c853fe20a6401ffc853200ff84299003ff604c8017fb026400fed8132005f6c099003fe604c801feb026400ff18132005f8c099003f8604c8017c3026429ffd013214ff88099007ff204c803fe1026403ffd964101dfecb2080ffe65904317f32c8203df996410c4fccb2080ffd65904017eb2c8203df59641004facb2080ffc65904077e32c8202bf59241017fea92080bfe5490405df2a48202ff552410077aa92080bfc5490407ffb1c8203ff98e41005fcc72080ffd63904017eb1c8203ff1
  | 7 => 0xd00800204a04400300400000100700200101100700e00a00400001400b00000401900300500500800100001500100101400000500100000700000803c03000000000100000000100500000f00305500300400200002800001400000400000000000100100b00000c01900100200100400100300100002d00f00000400200500b00700201b00100200403200100700000500e00f00001500207000400100b00700300002c00000000000300000000000700103700000500c00500201400c00c00b00100200204d00500900000000101303600400301d00600000200800201801200100703100300100001b00000100200c00b000042006010004001024004022015fec8aa00bfe5455005bf2a2a802ff1515401778a8aa00b3c5455001ffb1aa800bfd8d54007fcc6aa003fd6355001fe31aa800bf18d54017fe86aa00bfc4355005de21aa800ffd8954005fec4aa0c3fe62550037f312a800ff58954187f8c4aa006fc6255005ffa12a802efd0954017fc84aa00bfc4255061ff192a830ff0c954007fec2aa002ff6155001ff30aa800ff58554007f8c2aa00efc6155005ffa0aa802ff105540177882aa0c3ff2155061fe10aa800ffd8154005fec0aa003fe6055001feb02a800ff18154005f8c0aa00bff4055005dfa02a802ff10154187fe40aa0c3fc2055001ffb2c8600bfd964317ffccb21862fe6590c01feb2c8600bf5964317ff8cb21862fc6590c057eb248602ffd5243017fca92180bbe5490c05feaa48600ef55243017f8a92180afe6390c5fffa9c8600ff94e4317ff8a72180bff4390c05dfa1c8602f7d0e43017f8872180bdc4390c01ffb14862eff98a4300dfcc521803fd6290c017eb14862eff18a4300df8c5218bfff5290c5dff294862eff14a43017fe852180bfe4290c5ddf2148602ff10a430177885218bbfe3290c5dfe1948600ffd8643007fcc32180efe6190c01feb0c8600bf58643007f8c3218bfff5190c5ffe28c8602ffd06430177e832180bfc4190c5dff90c862eff08643007fec121803fe6090c017f3048600ff58243005fac121803fc6090c5fffa84862fff14243017fe812180bfc4090c05de204862effc8243177f84121803ff6550c017fb2a862dff995430c5fccaa1803fd6550c017eb2a862dff195430c5f8caa180aff6450c05ffaa28602ff95143017faa8a180bfc5450c057fb1a862dffd4d43007fca6a1803fd5350c5bfe29a8602ffd0d43017be86a180bfe4350c01df21a8602ff10d430177886a180bdc4350c01ffb128600bfd8943167fcc4a1806fe6250c01feb12862cff1894300df8c4a18b7ff5250c59ff292862cff14943017fe84a180bbf4250c05ff2128602ff10943167fc64a18b3fc3250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8603bf1854316ffea2a18b7fc5150c0
  | 8 => 0xb84000cfeb09000cdca0800004b000000b42d21165b0c00000093f8e5000a68000b654a2866000000085a8e000475b5600066457ab0179d59c50f150bf85e00000008bb42b1d410c53091021a2c2c8066e9cda70000000c8483bc48294000c7c3ac0000988f824fa1aace5c8b5a000b26a0acf072c0042bc0003b123865d00014e4da00000009183e4505708627a484c2e62a82220002d6000c4e69a02c00000601603600801700301100101800700200400000800f02602900000601700100705200000000d00603100102900301602500500000b00001201e07302001900000500000100400004b00000b00c06900000000005b00000502c00000900201500400200000500104700900600600400000400c00100401200001c00000300100000e00601100c00700a00000200201100500601c00100300901200500f00101500500200300203407600100601701501a02d00c00001000700d00a00b00100000400001500300002100500100000003100300201a00301300500001b00000001800d00800500d00000400000208500b02100002c00100100102802100a00000400500500400900c00500900300c00201f00e01500f02700803a00000900005200105400a00100000306200300301600000800001e01700500000200e01d00c01300600b00001100000700300a00600200400e00100100400502200200300e00000000600e00900304100500201400101405500000000000d00200100000d00801f00001600300100101f00000000a00300001400002800201400200002301100300300000b00000604402300700000004e00600e00500301b00100502102001a00f01d00004100100203b00003d00100900000400000700000200200d00e00000203000c00a00200000000101003700800000400800200001800b0000130010100050000670c100101b03600108801800500503101200000000b01400100302400300f00000400d00800000600300100a06301200301500100500200300500100606f01d01300200b04600000c02500000c00400101605600300100500200200000702500e00000300504100000000000600500100000000800003100500100000606900000500000a00b00100b00001502000b00800c00000b00100000600000000400000000b00000003500204f00001b00600200600a00102001e00200800901200000100601d00001100100908201c00001400000300800000001d00203700300300000200000d00000f00400600000002000200101f00400a00d00103200001100200100101000601501400000500700800100000000400e02b00400100100004c01300202300201c00d00100300200700201e01000200000600000500b00800503103500000d00000000101300201401400001800800100000b00000000
  | 9 => 0x8606fe4ac0000000001222c9000271b64ab3ae09388658e30007d95a29ca0000000000002a214482cd04000d1f000325c327c404f1142c000cb364b807807a955a2c77c0000000000000005d7c684b6000d50c0e00000000088a6caad600095a3c48bf0001f68da1624486b450a81a6721dc0f642f1e62c42844726a69da75f000000b94a368ed00000008db692fa87c53d0bd8ae2505369f68cc6b00001da0000360003d43b576208c27e6ce220a740008d6000b448ec0000240000dc73100003ecc400076e6388a6b5c000a1e000d541d1c9036040c54a353a8c06810e578a5ba82d3e8ab1fe11c5a62298888ead2351013b61c9aa3fc6207525a058c9de6f641438e644446b029643189fe37862d411026650cae46368e01411854226d8f47e51e0d00d24552396cb003b256b623de8410a6c145b08c6c3493c85a61a0a83ec3d06ae3f601ebcd07f5295f696a15ac52c3088461689ca3c4deb2e9161bab04d144dc54978a6481b841c362230876a240fe37a44d8df8864a02f461801f941086141cd89862d52f80c83930009009c6a142a75380004600500c6000a31000000b22bb4186bea6a03333d93720669a4a329d01909323207f4506b401cf4a613400032eb435dc8c0887875b480004303f721366c0006224442018d4b676e47e0a7cd3595e4f668c98a245acc7ff0bf50e33555e23e06316e78c6e2be03cc3733b65404b29e696084f3a07fa9466060e63401c0ac64f072b9c494d1334eed674e669047e84aa2a9b64d6d5c0008d159470692d71c68044100096650b7ca4e4574c2c81700eaf4416a8a4ec3e18e469390c87d5b61f86c9000ba45471265ac137c4a2047003c9ba6a90bceac8adcd1e4826144558828721e8000a483ea6d476ad6200001005e9500d0818b242b6bbe196c5f00008365822c5da2ce97035c4f17fc52a0cad165a4d108fe90478635e2ad64b848b38b2c194bd42808013309c87f2c94722d329f226453e66126e796aa2462309774a0cceb1ff6ec1d843c23c17f16a3c691a26212b1c8972c12d4c79c604cc27a10d63b87b86e608894405c4932431e203f86995c0bb30caf718f89447a80e4aea4e18c54e67845d2d09560001c6766ab68649b04b153b13887e8af0ee1c9c168fa64c286af97404155553228984e8bd09178c27d3ce62146b613e879be17341e3c2a1c7a2d45c78856e11222a94ba6f3973128fc577aaea7aab887f4ea7d6000000af6000adb000000120ad8000000c062162a57988fdcc67e2c183cf0eba1698e88ebc20002d3131d4f000000000000b0a79a8927a392e2686c0000000af800097a7632279342ec000461130b070009b8000b9200094277374e000698000cec86bca872fcba070000844c86000a06b1579e0000f4000affa341d270577057cc66b2aca05aba460001840003e8
  | 10 => 0x14c0257b000000030a4c4000266532a92000000000d5a00038204cc9e000ad000010600032c0008ce21c0003312d7cda3c2682889b08b807260000006263fd0001e7ae98bc60200000077b70a0968587d442c000666054000000c5e85e0000d1236a6e000181c5075007c49500097837929a3b23dd2e838a20645bc6e44a0000d873896ea5d676aba00064ec2e454000038000500936d2ec8205a000000c463660e28dc4cdb5e0000320006a8abc338a7e7140816edbd645a224d3c0008a800091c0002a411696840e63400063c5b42c60007bab1a99e8342783d64080006f04fec98a5ca8839034e6fc000bcf639ab500088cbccc72a506be890000cb8a2e3291d6000000234346000000abeb53000a64388b3e0ba0000000000210000005f045f514b4a0000006007650009e02b8d283e672e4f781587300000000052600000068497e7bcc671f27e95566cc24c58180456f0000003f9c60306ae4cc80000004aa00000000000083c0001f000000000000018d4af00000095900006e0000000002f013d37500057611e86700033430e00000036e5d6051000544caa27400052e3560005a86bc000a5e00000011a4347d00002895ca000b55ba08c15081e935243187b695a602a32d28247aebde0d3210912674bb82a05027d85939bc316cb209a097c1c0002dc0002e000000080044e00030bad9000000000000188000bf60000000000b2a443b70002ea000000a5234b2eb182000000b4eb3200000000039c0000003512488ff92a000240d6000000060ad370560de7aa16c9ea7d59aca22b907ac948bac1fa47c8093e74f3d0e8a41a9b18b7654d7715d885359abe431ab2732a1f41a400077886caee000bc8a864cb94c33245124b2cd6405c44a834fc44906d484c6cf4951a30ce40002908e0b70d4ed0c43a9a926f7fea628389e17adad2c267ea9141c5253aeb9d60342006f88770e8022d223575cc018be8bd23ce2980c4636cf812832f3fab7400049e52b49c1c32da5165901e5ce940aae2016c9a00033e4bc8201359b2a8474680dba808b2448401ab0004ba8eb29613906c86a77f38c58a2d8612bb27026087fb292a120923be6de36441e3688f7d067247c03e53760002c8d0871e72dbc45aac8a3e4b786562b44cf4a480c76c77ad655837a003a980a1c7f0ccc81cc9683d12a81625c2150005988f27a85c200000067abd800081e3988710650000000005628aa0001a6000000a42c244100007b663e443000000000cea000b304c8aedd09d3a0008d327ca6ab98bca000cf212d7480d9aca0e769200039201c17b000000cce8540c027a3c700000000059ec9c86800092f00048f81f0000000000e43cb17e28e00030f5045869e83a2458000b6e0003f2000ae618a3704923f45516104f41407a2d4d6f10007810009f07010000006da0
  | 11 => 0x84e00000091ea6c000000cd60006c700001a7040005d413c1766d01fb168712000b1685c154c4020248a70c158727ce09841647da0f22ccb3a3e0b0dd2c3f0881c0236a5fe4743bc6e0a3ecb4b589404d0c6a2a120c5faba2d2a300156b45044c1abfa6a20a03e36714f28f56a95e28e936c424b203e261e2fe478cf67af709c58b14c204909154c22f10894180a4cfa7ee4028b43a817c06a65c0a293ab9c04e44c3426a496cb86a4c654aaaa20926918a7821e0909cb718d30afe7c235a842ac23268f09d46c202c34819aa0275abfe07e5ee9eea721a749a1ae4989fca38aa442e51ab28c00a568be2521e43b44c9276ce24c562eb005b86689576351982cf8de5349d25480dbb541ac9dc735ae86aaca62af8e615c72815eac42de7f806099429caa62d1000c927e65fc58298d46a380000b1c54bae73d82aab1046ec369994e2930456be2c04b8a3d2b12c5aa043089d8a00b5da7619e436568c5482222e7607b45ec7c89e23024c05664beca2aa890a9a096238419c5d0b03a54b82aac5f451e58e806cd06b28114646f36ac1fd336c0ad1c8e114208a4e0a9a7d277db7a3ba41371614603d83043e1de5281bc191b13b0534c6700280768ad4b3813b9e4962d4b462caa1004d560a9e4d2896040b5255c10004a5466b855ad0d8bdb4b1c459264a2ed5be89e2b13feb6c8ba42d550bfc66a62abf4aa089a4fcc3e9f45f8b7e2ba68a8ca8c457200042a395a5866248c178b8c37c7304db000208a9cadd000af01c24d9c6257dc4c9e4a4a3b3d5f82116633c1808023b08320e52ac0005b28500006dc4762475ea4df00056a0001aa98c4dd0009fa4948e8902bb099000000000025a5ceb0e97432b4cec70285212cfc35474c9762881ee9b49a29a817d000d2092035077599a242a98792b519c2b3c6ff0f815295400035b00086e4e30000000005d2000c1e4914e1ab40007eb83a0004685b72cb29e1c1d46160000272000aec0007640425bc00000075c00002350d557bba4d747092c000628af509323ad6662465a4f894a8b2422a18a9445e69e8e760e0875270c26375584b41a25f3524bf21611923fbc7473e1099951a8a96d4a9ba57f0e07ce471000a262eebbc3a47a5104002084c6c780000000b290006d83770001a0b6a0000004ca39e814000000000710b6001226c00000034d6fa00000000070d4c7203355952000000aea0000008f3aded02a801a52111ea73aad430400080b76170869c2e4a9700094fafa54c99213a649a3a7cc1ce20ed3b03045900079773cd4000087a3dc82abc067e07424db960f00003dfb4c2e202ea0ebdc4530d2afcbee92b148d4412c1d0596b9ac38919cbc80a406855cee92863210b34477646690e7fd2181cb2f273d7a7ae38a008263060c7334044f570f1cd386b0651cb41d4b77e14a9ae000c0800
  | 12 => 0x3da5d55ae4d80cc0002050005e42825f20580bc0000b08f100062f000c882b2232cb6cbe63a00099c8268d54579a60ac27000002a00017200028a729b4d0ae2b076831e0fcc10067b6d79f13f1708b0484cd27ec0460000006e844000000006200059528c400000000000d5200007262c91b8d04800008e200058437e4456f48b6c3c694426287cde0d4b617f600025e65e000c2826013257e7a66867de0005de00083652597c08074a1673e93cd3c024e71a26a3282c71073aa00000018e2fc0009ec3583c8ab034a4776d20006ee0003db7824b078ec7e0525c6000000000000a40d265120004887e8000554b47000cca00000000026b2be3ee2a69cc0697b2cd40b456c0009967569be0b600070b8081be452b63094a9917a310000ac02ae20f000000000000000000adaa66819000754d0b0004d40004208d7c7800080f000c56696447b68799b7c52c1740d748e0004e700054fa2867c784ab24fa8d84e5000d560640009ce0e9ca448687809e2ab53f0000003d109c828c5c3a69248d2520baed5e79073f24953aaf26885ba442000000be692977225103912400000039130d0002540000000000002f6642908b8e24a102b6b258c7a1631b2327846bc60488a903c0006d60003ca5e80003246461b040f000732000000000b5f5188ac473d361ecae50007037d746cd6420a7947208100000ce7e47be31441222b000000c4295b0ec0007e7c22d0a8b875e79b22600a0be4288527586600001360dab729c011033ac8c0003941b641a87010a7426ba5a7000000b344320005410000000000003ae1930000005f1d180000006ea94e1b412f00008f988cc00fa9436c80004b5000afb0007c6874020a3dd63bf008e9229532466f228b000b5093eb880d59820aad4239a00053c12ec0c5c000070ebb6000d121ccadf998359580579baa129000a5a0b83f80000005648ef8a28eecac000afd0005092ef31c000c8ed391cab4f000d1a22d095744a71000374d380001fcb666c45538566330006ef00000050c777c3abda7250b9652becce80eabe373681272ab1e0006c6000d340000007dc83f8f65e600010800800052244f000c6482e9f8958d582280064cc588b0b465880000000851438000105945000c768c8
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe7158c1001cfd7158c1001cfc7158c1001ede3158c1001edc3158c100a4ff7058c10084fd7058c10004ff7690c1001cfe7690c10004fd7690c1001cfc7690c1017e7e6590c100067d6590c10016be6490c10006bd6490c10004ff7650c1001cfe7650c10004fd7650c1001cfc7650c1016e7e6550c100067d6550c10016be6450c10006bd6450c10004ff7458810014fe7458810014fc7458810004ff7358810004fc735881001eef7258810026ee325881001cff715881001cfe715881001cfd715881001cfc715881001eee215881001eec215881000cff705881000cfd7058810024fc7058810026ec205881001efa105881001ef91058810004ff765081001cfe7650810004fd765081001cfc765081015e7e65508100067d6550810016be6450810006bd6450810005f7715081001df47150810004ff76cc81001cfe76cc810004fd76cc81001cfc76cc810156be64cc810006bd64cc810006de63cc810006dd63cc810004ff764c81001cfe764c810004fd764c81001cfc764c810005bf744c81002dbc744c81014ebe644c810006bd644c810006de634c810006dd634c81000eee624c810006ed624c810005f7714c81001df4714c810005fb704c810005f8704c810014fe749801004cfd7498010014fc7498010004fe7398010004fd739801000cfe7298010044fd729801000cfc729801001cfd719801001cfe709801001ef7109801001efb109801001ef8109801004cff769001001cfe7690010014fd769001001cfc76900100d67e65900100067d6590010016be6490010006bd649001001df67190010005f5719001004cff76500100057f755001018d7c75500100be7e65500100067d6550010016be6450010006bd6450010005df7350010005dc7350010004fd76cc0100aebe64cc010006bd64cc010006fa60cc010004ff768c010004fd768c01009ebe648c010006bd648c010006de638c010006dd638c01001df6718c010005f5718c010004ff764c010005bf744c01002dbc744c01008ebe644c010006bd644c010004ff760c01001cfe760c010004fd760c01001cfc760c01007ebe640c010006bd640c010006de630c010006dd630c01001df6710c010005f5710c010006fa600c010044ff768801001cfe768801000cfd768801001cfc768801006ebe6488010006bd648801000eee6288010006ed628801001df67188010005f57188010046fa6088010044ff7648010066be6448010006bd6448010046fa604801001df77644010006f77644010004f77644010007b77444010007b4744401001ef7644401001fb66444010006f5644401001fb56444010006b56444010007d77344010007d47344010007e77244010007e4724401001df7704401001ff37044010006f6604401001ff26044010007f25044010007f15044010
  | 1 => 0x8110035f97288110007eb628811000efa628811000ef86288110037e8628811000ee8628811001dfa718811001df87188110007f24188110007f14188110197ea2188110197e8218811000cff7648110034fd764811001cfc7648110006bf6448110066bc6448110006df6348110006dc6348110006ef624811000eec6248110005f7714811001df4714811001df8764811000ef8764811001cf87648110007bb6448110007b86448110005fa7348110005f87348110007db6348110007d86348110035fb7248110007eb7248110007eb624811000efa624811000ef86248110037e86248110007f3714811001dfa714811001df87148110007f07148110007f24148110007f14148110006bf648411004ebc6484110006df6384110006dc6384110006ef6284110046ec628411001dfa708411001ef6768411001cf67684110005f77484110005f57484110007b76484110007b46484110007d76384110007d46384110007e76284110007e4628411001df6708411001ff36084110007f33084110007f03084110007f22084110007f12084110004ff75590100c4fe75590100c4fc755901001ebf7459010006bf545901002ebe545901002ebc5459010004ff7359010004fc735901002ebf435901002ebc4359010004ff725901000cfe725901000cfc725901002ebf4259010006be425901002ebc425901001cff715901001cfe715901001cfd715901001cfc715901001ebe415901001ebc4159010014ff7059010014fd705901002cfc705901002ebc405901001ef71059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bc5259010006be3259010006bc325901001ebf715901001ebe715901001ebd715901001ebc715901001ebf515901001ebe515901001ebd515901001ebc515901001ebf315901001ebe315901001ebd315901001ebc315901001ebf215901001ebe215901001ebd215901001ebc215901002ebf7059010006be7059010006bc7059010006bf5059010006bc5059010006bf2059010006bc205901001ebf105901001eb7105901001ebe105901001ebd105901001ebc1059010004ff765501001cfe7655010004fd765501001cfc7655010016be6455010006bd645501002f3c5455010014fe7498c10004fd7498c10014fc7498c1001ede7398c1000cfe7298c10004fd7298c1000cfc7298c1001cfe7198c1001cfc7198c1001ede3198c1001edc3198c1001efa1098c1001ef91098c10004ff7458c10014fe7458c10014fc7458c1001edf7358c10004ff7258c1000cfe7258c1000cfc7258c1001cff7158c1001cf
  | 2 => 0x3fb45450510007d76350510007d46350510007b6435051003fb44350510007e76250510007e4625051003fb74250510007b54250510007f37050510005f47050510007f0705051001ef7605051001ff3605051003fb74050510004fe76cc510006bf64cc510126bc64cc510006df63cc510006dc63cc510006ef62cc51011eec62cc510005fa70cc510005f970cc510004fc764c510006bf644c510106bc644c510006df634c510006dc634c510006ef624c5100feec624c510005fb704c510005f8704c51000cfc7648510006bf64485100debc6448510006df6348510006dc6348510006ef624851000eec6248510005fb7048510005f8704851005cfe76901100067f65901100d67c6590110006bf6490110016bc6490110006df6390110006dc6390110006ef62901100ceec6290110007b64190110014ff765011003cfd765011001cfc76501100057f75501101ad7c75501100067f65501100be7c6550110006bf6450110016bc6450110005df7350110005dc7350110006df6350110006dc6350110006ef62501100b6ec6250110005f7715011001df47150110007b5415011001cfe76cc110006bf64cc1100aebc64cc110006df63cc110006dc63cc110006ef62cc1100a6ec62cc11001df671cc110005f571cc11001dfa76cc110006fa76cc11001cfa76cc110007bb64cc110007b864cc110006fb63cc110007db63cc110006f963cc110007d863cc110005f972cc110007eb62cc1100a6fa62cc1100a6f862cc110007e862cc1100a6e862cc11001dfa71cc110007f271cc110007f171cc11001df871cc110007f241cc110007f141cc110004fe768c110006bf648c11009ebc648c110006df638c110006dc638c110006ef628c110096ec628c110005fa708c110004ff764c110004fd764c11001cfc764c110005bf744c11003dbc744c110006bf644c11008ebc644c110006df634c110006dc634c110006ef624c110086ec624c110005f7714c11001df4714c110004fe760c110006bf640c11007ebc640c110006df630c110006dc630c110006ef620c110076ec620c110007d9300c110005fa760c110006fa760c110007bb640c110007b8640c110005fa730c110007da730c110006fb630c110007db630c110006db630c110006f9630c110007d8630c1101a7db430c1101a7d8430c110005f9720c110007eb620c110076fa620c110076f8620c110007e8620c110076e8620c110007db320c110007d9320c11001dfa710c11001df8710c110007f2410c110007f1410c11019fda310c11019fd8310c110054fe7688110006bf648811006ebc6488110006df6388110006dc6388110006ef628811000eec6288110005fa7688110056fa7688110007bb6488110007b86488110005fa7388110005f87388110007db6388110007d8638
  | 3 => 0xf74d8910006ee74d8910006ed74d8910006ec74d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d8910196ee71d8910006ed71d8910196ec71d8910006ef41d8910196ee41d8910196ec41d8910196ee31d8910196ec31d8910196ef70d8910036ee70d8910006ed70d8910006ef40d8910006ec40d8910196ef10d8910196ec10d8910005bf745891003dbc7458910006bf6458910006bc6458910005df7358910005dc7358910006df6358910006dc6358910036ec6258910004ff7458910006bf7458910004bf7458910014fe7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df7358910004fc7358910006dc7358910004dc7358910034ff7258910006ef7258910044ff7158910006f77158910054ff7058910006fb7058910005ee7618910036ee7618910004ee7618910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910037e970189101beef60189101bfeb10189101bfe81018910004ff7650910004fe7650910004fd7650910004fc76509100067f655091015e7c6550910006bf6450910016bc6450910006df6350910006dc6350910006ef625091000eec6250910004ff76cc910004fe76cc910004fd76cc910004fc76cc910006bf64cc910156bc64cc910006df63cc910006dc63cc910006ef62cc91000eec62cc910004ff764c910004fe764c910004fd764c910004fc764c910005bf744c91003dbc744c910006bf644c91014ebc644c910006df634c910006dc634c910006ef624c91000eec624c910005f7714c91001df4714c910005fb704c910005f8704c910005f6769051001ef6769051001df7759051001f767590510005f5759051001f75759051000575759051000777659051000774659051003df57490510007b76490510016f66490510016f4649051003fb46490510016b4649051003fb65490510007b55490510007d76390510007d46390510007e76290510007e46290510005f6709051001ef7609051001ff3609051003fb44090510014fc76505100067f65505101367c6550510006bf6450510016bc6450510006df6350510006dc6350510006ef625051012eec625051001fb44150510005fb7050510005f8705051003df47650510016f47650510014f47650510005f77550510005f5755051000777655051000774655051001df7745051001fb77450510007b76450510016f66450510016f4645051003fb464505101b7b75450510
  | 4 => 0x8d10004fd7298d10006ed7298d10004ed7298d1000cfc7298d10004fd7198d10006f57198d10004fd7098d10006f97098d10005bf7458d1003dbc7458d10006bf6458d10006bc6458d10005ef7258d10035ec7258d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10014fc7458d10006bc7458d10014bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d10006bf6418d10006bc6418d10006dd6318d10014fe7418d10004fd7418d10014fc7418d10006de7318d10006df4318d10006dc4318d1000cfe7218d10004fd7218d1000cfc7218d10006de3218d10006dc3218d1001cfe7118d1001cfc7118d10094fe7018d10074fc7018d10005de7618d10006de7618d10004de7618d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d1019fdb7018d1019fdb1018d1019fd81018d10006df7418d10006de7418d10006dd7418d10006dc7418d10006de5418d10006dd5418d10006dc5418d10006df7218d10006de7218d10006dd7218d10006dc7218d10006df4218d10006de4218d10006dc4218d10006df7118d1019ede7118d10006dd7118d1019edc7118d10006df4118d1019ede4118d1019edc4118d10006df2118d1019ede2118d1019edc2118d1019edf7018d10006dd7018d10006df4018d10006dc4018d10006df2018d10006dc2018d1019edf1018d10006dd1018d1019edc1018d10004ff7690d10004fe7690d10004fd7690d10004fc7690d100067f6590d1017e7c6590d10006bf6490d10016bc6490d10006df6390d10006dc6390d10176ec6290d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1016e7c6550d10006bf6450d10016bc6450d10006df6350d10006dc6350d10166ec6250d10005fb7050d10005f87050d1000cfe76d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910036ee62d8910014fe74d8910004fd74d8910014fc74d8910004fe73d8910004fd73d8910006ef42d8910036ee42d8910036ec42d8910036ee32d8910036ec32d891001cfe71d8910034fd71d891001cfc71d8910036ef21d891000cfe70d891001cfd70d891000cfc70d8910036ef20d8910035ee76d891000cee76d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910197eb70d8910197eb10d8910197e810d8910006e
  | 5 => 0x6bd73d9110006bc73d9110006bf53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bc52d9110006be32d9110006bc32d9110006bf71d91101d6be71d9110006bd71d91101d6bc71d9110006bf51d91101d6be51d91101d6bc51d91101d6be31d91101d6bc31d9110006bf21d91101d6be21d91101d6bc21d91101d6bf70d911003ebe70d9110006bd70d9110006bf50d9110006bc50d9110006bf20d9110006bc20d91101d6bf10d91101d6bc10d91100057f75591101ad7c75591100067f655911003ebc6459110005df7359110005dc7359110005ef7259110035ec7259110004ff75591100067f75591100047f75591100c4fe75591100c4fc75591100067c75591100c47c755911003cff7459110006bf7459110004ff7359110006df7359110004df7359110004fc7359110006dc7359110004dc7359110004ff7259110006ef7259110004ef725911000cfe725911000cfc7259110006ec725911000cec725911004cff7159110006f7715911005cff7059110006fb7059110005be761911003ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6219110006bc621911003fb571191101cebf60191101cfbb10191101cfb81019110004ff7655110004fe7655110004fd7655110004fc7655110006bf6455110016bc645511003f3c5455110186ec6255110006bf64d8d10006bc64d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df43d8d10006dc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006de32d8d10006dc32d8d10006f970d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d10007d970d8d101c7db10d8d101c7d810d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df42d8d10006de42d8d10006dc42d8d10006df71d8d101c6de71d8d10006dd71d8d101c6dc71d8d10006df41d8d101c6de41d8d101c6dc41d8d10006df21d8d101c6de21d8d101c6dc21d8d101c6df70d8d10006dd70d8d10006d970d8d10006df40d8d10006dc40d8d10006df20d8d10006dc20d8d101c6df10d8d101c6dc10d8d1003dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10035ee7298d10005ed7298d10014fe7498d10006be7498d10014be7498d10004fd7498d10006bd7498d10004bd7498d10014fc7498d10004fe7398d10004de7398d1000cfe7298d10006ee7298d1000cee729
  | 6 => 0xf63cca10006dc63cca10004ff764ca10004fe764ca10004fd764ca10004fc764ca10005bf744ca1004dbc744ca10006df634ca10006dc634ca10005f7714ca1001df4714ca10005fb704ca10005f8704ca1001cff705861001efb1058610014ff7650610016be6450610006bd6450610005fb7050610005f87050610006de63cc610006dd63cc610005fa70cc610005f970cc610006de634c610006dd634c610005fb704c610005f8704c61000cff764861000eee6248610006ed624861001fe42148610005fb7048610005f8704861001cfd7690210016be6490210006bd649021001df67190210005f5719021002cff76502100057f75502101e57c7550210006bf6450210016bc6450210005df7350210005dc7350210005f976cc210006f976cc210006fb63cc210006f963cc210005f972cc2100a6fa62cc2100a6f862cc21001dfa71cc21001df871cc21001cfd768c210006de638c210006dd638c21001df6718c210005f5718c210005bf744c21004dbc744c21001cfd760c210006de630c210006dd630c21001df6710c210005f5710c210007d9300c21001df9760c210006f9760c21001cf9760c210007da730c210006fb630c210007da630c210006f9630c210007d9630c2101dfdb430c2101dfd8430c210005f9720c210076fa620c210076f8620c210007db320c210007d9320c21001dfa710c210007f2710c210007f1710c21001df8710c21019fda310c21019fd8310c21001cfd768821000eee6288210006ed628821001df67188210005f5718821001df9768821000ef9768821001cf97688210005fa7388210005f8738821000efa6288210047ea6288210007e9628821000ef8628821001dfa7188210007f27188210007f1718821001df87188210197ea2188210197e82188210024ff7648210005fb7648210026fb7648210005fa7348210005f87348210007eb724821000efa624821000ef8624821001dfa714821001df87148210005f576c421001ef576c4210006f764c4210006f564c421001ff260c4210007f250c4210007f150c4210014fe76d911003ebe64d91100c4fe75d9110004fd75d91100c4fc75d9110006bf54d911003ebe54d911003ebc54d9110004fe73d9110004fd73d911003ebf43d911003ebc43d911000cfe72d9110004fd72d911000cfc72d911003ebf42d9110006be42d911003ebc42d911001cfe71d911003cfd71d911001cfc71d911003ebf41d9110014fe70d911001cfd70d9110014fc70d911003ebf40d911003dbe76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bc65d9110006be62d9110006bc62d9110007b771d91101d7bb10d91101d7b810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110
  | 7 => 0x3101d6bf6490310016bc649031001df471903101d7b64190310014ff765031001cfc76503100057f75503101ed7c7550310016be6450310006bd6450310005df7350310005dc7350310005f7715031001df47150310007b54150310006de63cc310006dd63cc31001df671cc310005f571cc3101c6df638c3101c6dc638c310005bf744c31005dbc744c310006de634c310006dd634c310005f7714c31001df4714c31019edf630c31019edc630c310034fd7688310196ef628831000eec628831000cff764831001cfc764831000eee6248310006ed6248310005f7714831001df4714831004ebe64d92100c4fe75d9210004fd75d92100c4fc75d9210006bf54d921004ebc54d9210004fe73d9210004fd73d921004ebc43d921000cfe72d9210004fd72d921000cfc72d921004ebf42d9210006f571d92101d6be41d92101d6bc41d9210006fa70d921004ebf40d92100057f75592101e57c755921004ebc6459210004ff75592100067f75592100047f75592100c4fe75592100c4fc75592100067c75592100c47c7559210006bf745921004ebe5459210004ff7359210004fc7359210004ff725921000cfe725921000cfc725921004ebf415921001cfc705921004ebc4059210004ff7655210004fe7655210004fd7655210004fc7655210016be6455210006bd645521004f3c5455210014fe74d8e10004fd74d8e10014fc74d8e1000cfe72d8e10004fd72d8e1000cfc72d8e10006f571d8e101c6de31d8e101c6dc31d8e10006fa70d8e10006df6398e10014fe7498e10004fd7498e10014fc7498e1000cfe7298e10004fd7298e1000cfc7298e10005bf7458e1004dbc7458e10004ff7458e10006bf7458e10004bf7458e10014fe7458e10014fc7458e10006bc7458e10014bc7458e10006df7358e10004ff7258e1000cfe7258e1000cfc7258e10006f87058e10006dd6318e10014fe7418e10004fd7418e10014fc7418e10006de7318e1000cfe7218e10004fd7218e1000cfc7218e10006f57118e1019ede3118e1019edc3118e10006fa7018e10004ff7690e10004fe7690e10004fd7690e10004fc7690e10006bf6490e10016bc6490e10004ff7650e10004fe7650e10004fd7650e10004fc7650e10005fb7050e10005f87050e10046ee62d8a10014fe74d8a10004fd74d8a10014fc74d8a10004fe73d8a10004fd73d8a10006f571d8a10196ee21d8a10196ec21d8a10006fa70d8a10046ec6258a10004ff7458a10014fe7458a10014fc7458a10004ff7358a10004fc7358a10006ef7258a10046ef2158a1001cfc7058a10046ec2058a10004ff7650a10004fe7650a10004fd7650a10004fc7650a10006bf6450a10016bc6450a10005f77150a1001df47150a10004ff76cca10004fe76cca10004fd76cca10004fc76cca10006d
  | 8 => 0x4fe760c520004fd760c52001cfc760c520006df630c520006dc630c52000dee720c520005ed720c520006f7610c52001ef4610c520005fa700c520005f9700c52020cfe7690120016be6490120006bd6490120014ff765012000cfe76501200b4fd765012000cfc76501200057f75501202057c7550120006bf6450120016bc6450120005df7350120005dc7350120005ef725012000dec725012000cfe76cc12000cfc76cc120006df63cc120006dc63cc12000dee72cc120005ed72cc1200a6fb60cc120074fe768c120006de638c120006dd638c1200a4ff764c12000cfe764c120084fd764c12000cfc764c120005bf744c120065bc744c120006df634c120006dc634c120005ef724c12000dec724c120094fe760c120006de630c120006dd630c120076fb600c120196ec618812000dee708812000fea708812000eef608812000feb6088120004ff75593100c4fe75593100c4fc755931001ebf7459310006bf545931005ebc5459310004ff7359310004fc735931005ebc4359310004ff725931000cfe725931000cfc725931005ebf425931001cfc715931001ebe415931001ebc415931005ebf4059310004ff765531001cfe7655310004fd765531001cfc76553101febf6455310016bc645531005f3c545531001df671553101ffb64155310014fe7498f10004fd7498f10014fc7498f1001ede7398f10006df4398f10006dc4398f1000cfe7298f10004fd7298f1000cfc7298f1001cfe7198f1001ede3198f1001edc3198f1001efa1098f1001ef91098f10004ff7458f10014fe7458f10014fc7458f1001edf7358f10006df4358f10006dc4358f10004ff7258f1000cfe7258f1000cfc7258f1001cfc7158f1001ede3158f1001edc3158f10004ff7690f1001cfe7690f10004fd7690f1001cfc7690f10016be6490f10006bd6490f10004ff7650f1001cfe7650f10004fd7650f1001cfc7650f10004ff7458b10014fe7458b10014fc7458b10004ff7358b10004fc7358b1001eef7258b1001cfc7158b1001eee2158b1001eec2158b10056ef2058b1001efa1058b1001ef91058b10004ff7650b1001cfe7650b10004fd7650b1001cfc7650b10016be6450b10006bd6450b10004ff76ccb1001cfe76ccb10004fd76ccb1001cfc76ccb10006de63ccb10006dd63ccb10004ff764cb1001cfe764cb10004fd764cb1001cfc764cb10005bf744cb1005dbc744cb10006de634cb10006dd634cb10005f7714cb1001df4714cb10005fb704cb10005f8704cb1001df7765071002ef77650710005f77550710005f5755071001fb7745071001fb76450710016f6645071001ef4645071001fb464507101f7b7545071005fb45450710007b6435071005fb4435071005fb74250710007b54250710005f4705071005fb7405071003cfd769
  | 9 => 0xf75591202057c7559120066bc6459120005df7359120005dc7359120005f77159120005f47159120215fb7059120004ff75591200067f75591200047f75591200c4fe75591200c4fc75591200067c75591200c47c75591200ccff7459120006bf7459120066be5459120004ff7359120006df7359120004df7359120004fc7359120006dc7359120004dc73591200b4ff7259120006ef7259120004ff7159120006f77159120004f7715912001cfc7159120006f4715912001cf47159120066bf4159120214ff7059120006fb7059120066bc4059120004ff7655120004fe7655120004fd7655120004fc7655120016be6455120006bd64551200673c5455120014fe74d8d20004fd74d8d20014fc74d8d20006df43d8d20006dc43d8d20094ff72d8d20094fd72d8d20096df32d8d20096dd32d8d2001cfe71d8d20004fd71d8d20006df6398d20085f97098d20014fe7498d20004fd7498d20014fc7498d20074fe7398d200a4fd7298d20006ed7298d2001cfe7198d20004fd7198d20084fd7098d20006f97098d200a6fb2098d200a6f82098d20005bf7458d20065bc7458d20005f77158d20005f47158d200a5fb7058d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20014fc7458d20006bc7458d20014bc7458d20006df7358d20084ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2001cfc7158d20006f47158d2001cf47158d200a4ff7058d20006fb7058d200a4fb7058d20094fe7618d20006dd6318d20014fe7418d20004fd7418d20014fc7418d20006de7318d20006df4318d20006dc4318d20074ff7218d2000cfe7218d20074fd7218d2000cfc7218d20076df3218d20076dd3218d2001cfe7118d20004fd7118d20076fb2018d20076f82018d20004ff7690d20004fe7690d20004fd7690d20004fc7690d20006bf6490d20016bc6490d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20014fe74d8520004fd74d8520014fc74d8520004fe73d8520004fd73d8520006f741d8520006f441d8520046f621d8520046f521d8520006f76198520035f97098520005bf7458520065bc7458520005df7358520005dc7358520055fb7058520065be7418520005bd741852001ef66118520006f56118520004fe7690520004fd769052001cfc76905202057e75905200057d7590520006bf6490520016bc6490520005fa7090520005f97090520004ff7650520004fe7650520004fc7650520016be6450520006bd6450520004fe76cc520004fd76cc520004fc76cc520006f761cc52001ef461cc520004fe768c520004fd768c52001cfc768c520065be748c520005bd748c520006df638c520006dc638c520005fa708c520005f9708c520004ff764c520004fe764c520004fc764c520
  | 10 => 0x8e20006f571d8e20004f571d8e20074fe70d8e20006fa70d8e20074fa70d8e20084fd7698e20006df6398e20014fe7498e20004fd7498e20014fc7498e200a6df3298e200a6dd3298e2001cfe7198e20004fd7198e200a6fb2098e200a6f82098e20004ff7458e20014fe7458e20014fc7458e20006df7358e20086df3258e20086dd3258e20004ff7158e2001cfc7158e20006dd6318e20095fa7018e20014fe7418e20004fd7418e20014fc7418e200a4fe7318e20006de7318e20006ed7218e2001cfe7118e20004fd7118e20094fe7018e20006fa7018e20076fb2018e20076f82018e20004ff7690e20004fe7690e20004fd7690e20004fc7690e20016be6490e20006bd6490e20004ff7650e20004fe7650e20004fd7650e20004fc7650e20025fa70d8620006f76198620004ff7458620014fe7458620014fc7458620004ff7358620004fc7358620036f62158620036f52158620196ec215862006dbe7418620005bd741862001ef66118620006f56118620045fa701862001cff7690620004fe7690620004fd769062021d7e75906200057d759062001ef66190620006f56190620005fa7090620005f97090620004ff7650620004fd7650620004fc7650620016be6450620006bd6450620005ef725062000dec725062001ef66150620006f56150620004ff76cc620004fe76cc620004fd76cc62000dee72cc620005ed72cc62001ef661cc620006f561cc62011fe421cc62001cff768c620004fe768c620004fd768c62006dbe748c620005bd748c620005fa708c620005f9708c620004ff764c620004fd764c620004fc764c620005ef724c62000dec724c62001cff760c620004fe760c620004fd760c62001ef6610c620006f5610c620197e4210c620005fa700c620005f9700c62000dee718862000fe67188620197e66188620196ed6188620007e56188620197ea7088620005ed7088620197e9708862000eee608862000fea608862000cff7690220014fe769022000cfd7690220016be6490220006bd649022000dee7290220005ed7290220214ff76502200057f755022021d7c7550220005df7350220005dc7350220084fd76cc2200a6fa60cc22000cff768c22000cfd768c220006de638c220006dd638c22000dee728c220005ed728c2200a4ff764c220005bf744c22006dbc744c22000cff760c22000cfd760c220006de630c220006dd630c22000dee720c220005ed720c220076fa600c220014fe76d9120066be64d91200c4fe75d9120004fd75d91200c4fc75d9120006bf54d9120066bc54d9120004fe73d9120004fd73d9120066bc43d91200ccff72d912000cfe72d91200ccfd72d912000cfc72d91200cebf42d91200cebd42d912001cfe71d9120004fd71d9120066bc41d912000cfd70d9120066bf40d91200057
  | 11 => 0x6f5610c430005fa700c430005f9700c43007dde740c43019ddc740c430005dd720c43019dde710c43019fd6710c43019fd6610c43019edd610c430007d5610c430247d7210c43019fd4210c43019fda700c430005dd700c43019fd9700c430005d9700c430247db200c430247d8200c43001cff7688430004fe7688430004fd768843019ddf738843019ddc738843001ef66188430006f56188430005fa7088430005f97088430077e82088430004ff7648430004fd7648430004fc7648430005df7348430005dc734843000eee6248430006ed624843001ef66148430006f56148430005fb7048430005f87048430014fe749803009cfd7498030014fc749803009edf439803009edc439803000cfe7298030096df3298030096dd32980301c6de31980301c6dc319803009cff7690030014fe7690030014fd769003007cfc7690030016be6490030006bd6490030005de7390030005dd739003007f9c439003009cff76500300057f755003023d7c7550030005df735003007ddc735003007dde74cc03007ddc74cc030005dd72cc03019dde71cc030237db20cc030237d820cc030005dd738c030006de638c030005f9738c030006fa638c030007da638c03022fdb438c03022fd8438c030075fa728c030075f8728c030007db328c030007d9328c030005f9718c030007da318c030007d8318c030004ff764c030005bf744c03007dbc744c030005df764c030006df764c030004df764c0300079f744c03007dde744c03007ddc744c0300079c744c03007d9c744c030005df724c03019ddc714c030005df704c030006de604c030227db204c030227d8204c030005fb764c030006fb764c030004fb764c030007bb744c030007b8744c030005fb734c030007db734c030006fa634c030007da634c030075fa724c030075f8724c030227da324c030227d8324c030005fb714c030007db314c030007d9314c03006ebe64d922020dfa70d92200c4fe75d9220004fd75d92200c4fc75d92200b4fd74d9220004fe73d9220004fd73d9220006ed72d922001cfe71d9220004fd71d922020cfe70d9220006fa70d9220014ff765922006ebc6459220004ff75592200c4fe75592200c4fc7559220006bf745922006ebe5459220004ff7359220004fc735922006ebc43592200b6bf42592200b6bd4259220004ff715922001cfc715922006ebf415922000cfc705922006ebc4059220004ff7655220004fe7655220004fd7655220004fc7655220016be6455220006bd645522006f3c545522006dbe74d8e20005bd74d8e20005f671d8e20005f571d8e20075fa70d8e20014fe74d8e20006be74d8e20014be74d8e20004fd74d8e20006bd74d8e20004bd74d8e20014fc74d8e20006ed72d8e2001cfe71d8e20006f671d8e2001cf671d8e20004fd71d
  | 12 => 0xd7655030004fc7655030016be6455030006bd645503007f3c5455030005df7355030005dc735503007f9c4355030005fb7055030005f87055030014fe7498c300acfd7498c30014fc7498c3000cfe7298c300acff7690c30014fd7690c30016be6490c30006bd6490c3007dde7390c3007f9f4390c30005fa7090c30005f97090c300acff7650c3007ddf7350c3007f9c4350c30076ee62d883000cff7658830076ec6258830077e82058830004ff7458830014fe7458830014fc745883000cfd7358830076ee4258830076ec3258830004ff715883001cfc7158830076ef2158830076f87058830076fb2058830076ec2058830076f82058830004ff7650830004fd7650830004fc7650830016be6450830006bd6450830005df7350830005dc735083007f9f435083000eee6250830006ed6250830005fb7050830005f8705083000cfd76cc83000eee62cc830006ed62cc830005fa70cc830005f970cc830075dd76cc83000edd76cc83000cdd76cc83007dde74cc83007ddc74cc830006df64cc830006dd64cc830075dd72cc83000ede62cc830077ce62cc830007cd62cc83000edc62cc83019dde71cc830007da70cc830005dd70cc830007d970cc830005d970cc830077db20cc830077d820cc8300a4ff764c830005bf744c83007dbc744c830005f7714c830005f4714c830005fb704c830075f8704c830005df764c8300a6df764c8300079f744c83007dde744c83007ddc744c8300079c744c83007d9c744c830006df644c830006dd644c830075df724c830007cf724c83000ede624c83000edc624c830007d7714c83019ddc714c830007d4714c830005d4714c830005df704c830007db704c830005db704c830077d8704c830077db204c830077d8204c830006f76198430004ff7458430014fe7458430014fc7458430004ff725843000cfe725843000cfc7258430006df3258430006dd325843007dbe7418430005bd7418430075ee7218430005ed721843001ef66118430006f5611843001cff7690430004fe7690430004fd769043023d7e75904300057d7590430005de7390430005dd739043001ef66190430006f56190430005fa7090430005f97090430004ff7650430004fd7650430004fc7650430016be6450430006bd6450430005df7350430005dc735043007f9c435043001ef66150430006f5615043001cfd76cc43001ef661cc430006f561cc430005fa70cc430005f970cc430004fd768c43007dbe748c430005bd748c430005f9708c430005dd768c43019edd768c43007dde748c43019f9e748c43007d9e748c43019f9d748c43019ddc748c430005dd728c43019dde718c43019edd618c43019fda708c430005dd708c43019fd9708c430005d9708c43024fdb208c43024fd8208c430004ff764c43001ef6610c430
  | 13 => 0x930004fc76509300067f655093015e7c6550930006bf6450930016bc6450930094fe76cc930006bf64cc930156bc64cc93000cfc764c930005bf744c93008dbc744c930006bf644c93014ebc644c930006ef624c93000eec624c930087cc324c930005f7714c930005f4714c930005fb704c930005f8704c930006bf64d8530006bc64d8530014fe74d8530004fd74d8530014fc74d853000cfe72d8530004fd72d853000cfc72d8530006f721d8530006f421d853008dbe7498530005bd7498530006bf6498530006bc6498530006f76198530005bf745853008dbc7458530006bf6458530006bc6458530005ef7258530085ec7258530006bf6418530006bc641853001ef66118530006f56118530004fe7690530004fd769053001cfc76905302557e75905300057d75905300067f65905301467c6590530006bf6490530016bc6490530004ff7650530004fe7650530004fc76505300067f65505301367c6550530006bf6450530016bc6450530004fe76cc530006bf64cc530126bc64cc53008dbe748c530005bd748c530006bf648c530116bc648c530006f7618c53001ef4618c530005fa708c530005f9708c53001cfc764c530006bf644c530106bc644c530006f7614c53001ef4614c530005fb704c530005f8704c530004fe760c530006bf640c5300f6bc640c530004fe7688530004fd768853001cfc7688530006bf64885300e6bc6488530006ef628853000eec6288530004ff7648530004fe7648530004fc7648530006bf64485300debc64485300acfe76901300067f65901300d67c6590130006bf6490130016bc6490130014ff765013008cfd7650130014fc76501300057f75501302557c75501300067f65501300be7c6550130006bf6450130016bc6450130005df7350130005dc7350130006bf64cc1300aebc64cc130007bb64cc130007b864cc1300a6fa62cc1300a6f862cc130006fb61cc130006bf648c13009ebc648c1300079f648c13009ede648c13009edc648c1300079c648c13009e9c648c130006df628c1301c6dc618c130007db608c13007ebe64d90300c4fe75d9030004fd75d90300c4fc75d903007cfd74d90300acfe73d9030006de73d903007edf43d903007edc43d903000cfe72d9030004fd72d903000cfc72d903001cfe71d9030004fd71d903009cfe70d9030006fa70d9030014ff765903007ebc645903007f9c4359030004ff75590300c4fe75590300c4fc7559030006bf745903007ebe5459030014ff7359030014fd735903007cfc735903007edc735903007cdc735903007edf435903007ebc435903007edc4359030004ff725903000cfe725903000cfc725903007ebf4259030004ff715903001cfc715903007ebf415903007cfc705903007ebc4059030004ff7655030004fe7655030004f
  | 14 => 0x5df7348630005dc7348630014fd7690230016be6490230006bd6490230005de7390230005dd739023009f9c439023007cff76502300057f755023025d7c755023009ddf7350230005dc7350230005dd76cc230006dd76cc23009dde74cc23009ddc74cc230005dd72cc2301c5de71cc230007da50cc230007d950cc230005f976cc230006f976cc230007da53cc230007d953cc2300a6fa62cc2300a6f862cc230006f961cc230014fe76d913008ebe64d91300c4fe75d9130004fd75d91300c4fc75d9130006bf54d913008ebe54d913008ebc54d9130014fe73d913008cfd73d9130014fc73d913008ebf43d913000cfe72d9130004fd72d913000cfc72d913008ebf42d9130006be42d913008ebc42d913001cfe71d9130004fd71d913008ebf41d913008ebc41d913008cfd70d913008ebf40d913008dbe76d9130014be76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bc65d9130006be62d9130006bc62d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130006bf73d913008ebe73d9130006bd73d9130006bf53d9130006bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bc52d9130006be32d9130006bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006bc51d9130006bf21d9130006bc21d9130006bf70d913008ebe70d9130006bd70d9130006bf50d9130006bc50d9130006bf20d9130006bc20d91300057f75591302557c75591300067f655913008ebc6459130004ff75591300067f75591300047f75591300c4fe75591300c4fc75591300067c75591300c47c755913008cff7459130006bf745913009cff7359130006df735913009cdf7359130004ff725913000cfe725913000cfc7259130004ff715913001cfc71591300acff7059130006fb7059130005be761913008ebe7619130004be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c6519130006be6219130006bc6219130004ff7655130004fe7655130004fd7655130004fc7655130006bf6455130016bc645513008f3c545513009cfe7690d300067f6590d3017e7c6590d30006bf6490d30016bc6490d30014fc7650d300067f6550d3016e7c6550d30006bf6450d30016bc6450d30005fb7050d30005f87050d3000cfe76d8930006bf64d8930006bc64d8930086ee62d8930014fe74d8930004fd74d8930014fc74d893000cfc73d8930086ee32d893001cfe71d8930004fd71d8930086ec21d8930086ef20d8930005bf745893008dbc7458930006bf6458930006bc6458930086ec6258930005f77158930005f47158930004ff7650930004fe765
  | 15 => 0xf435923009edf435923009edc4359230004ff725923000cfe725923000cfc7259230006be425923009ebc4259230004ff715923001cfc715923009ebf415923009ebc4059230004ff7655230004fe7655230004fd7655230004fc7655230016be6455230006bd645523009f3c5455230005df7355230005dc735523009f9c435523008cfd7690e30006bf6490e30016bc6490e3009f9f4390e30014ff7650e30016be6450e30006bd6450e3009f9c4350e30005fb7050e30005f87050e3009dbe74d8a30005bd74d8a30096ee62d8a30005f671d8a30005f571d8a30096ec6258a30004ff7458a30014fe7458a30014fc7458a30096ee3258a30004ff7158a3001cfc7158a30096ec2058a30004ff7650a30004fd7650a30004fc7650a30006bf6450a30016bc6450a30005df7350a30005dc7350a3009f9f4350a30084fd76cca30005dd76cca30086dd76cca3009dde74cca3009ddc74cca30006df64cca30006dd64cca3000ede62cca3000edc62cca301c5de71cca30005dd70cca3000cff764ca30005bf744ca3009dbc744ca3000eee624ca30006ed624ca30005f7714ca30005f4714ca30005fb704ca30005f8704ca30095df764ca3000edf764ca3000cdf764ca300079f744ca3009dde744ca3009ddc744ca300079c744ca3009d9c744ca30006df644ca30006dd644ca30007cf724ca3000ede624ca30097ce624ca3000ece624ca30007cd624ca3000edc624ca30007d7714ca301c5dc714ca30007d4714ca30005d4714ca30005df704ca30007db704ca30007d8704ca30006f76198630004ff7458630014fe7458630014fc7458630004ff725863000cfe725863000cfc7258630006df3258630006dd3258630006f72158630006f4215863009dbe7418630005bd741863001ef66118630006f5611863001cff7690630004fe7690630004fd769063025d7e75906300057d7590630005de7390630005dd739063001ef66190630006f56190630004ff7650630004fd7650630004fc7650630016be6450630006bd6450630005df7350630005dc735063009f9c435063001ef66150630006f5615063009dbe748c630005bd748c63001ef6618c630006f5618c630005fa708c630005f9708c63009dde748c6301c79e748c63009d9e748c6301c79d748c6301c5dc748c630005dd728c6301c7d6618c6301c6dd618c630007d5618c6301c7da708c630005dd708c6301c7d9708c63001cff764c63001ef6614c630006f5614c630005fb704c630005f8704c630005dd760c6301c6dd760c63009dde740c6301c5dc740c630005dd720c6301c7d6710c6301c6dd610c630267d7210c6301c7d4210c630005dd700c63001cff7688630004fe7688630004fd76886301c5df73886301c5dc7388630004ff7648630004fd7648630004fc7648630
  | 16 => 0x93300c4fe75d93300067e75d93300c47e75d9330004fd75d93300067d75d93300047d75d93300c4fc75d93300aebe54d9330006de73d933000cfe72d9330004fd72d933000cfc72d933001cfe71d9330004fd71d93300aebf41d9330006f970d93300aebc40d93300aebc6459330004ff75593300c4fe75593300c4fc7559330006bf7459330006bf54593300aebc54593300aebc4359330004ff725933000cfe725933000cfc72593300aebf4259330004ff715933001cfc71593300aebc41593300aebf4059330004ff7655330004fe7655330004fd7655330004fc7655330006bf6455330016bc64553300af3c5455330005fb7055330005f87055330014fd7690f30016be6490f30006bd6490f30005fa7090f30005f97090f3007cff7650f300a6ee62d8b300a6ec6258b300a7eb2058b30004ff7458b30014fe7458b30014fc7458b300a6ec3258b30004ff7158b3001cfc7158b300a6ec2158b300a6fb7058b300a6ef2058b300a6fb2058b300a6f82058b30004ff7650b30004fd7650b30004fc7650b30016be6450b30006bd6450b30005fb7050b30005f87050b3000cfd76ccb3000eee62ccb30006ed62ccb30005fa70ccb30005f970ccb30074ff764cb30005bf744cb300adbc744cb300a7cc324cb30005f7714cb30005f4714cb300a5fb704cb30005f8704cb300adbe74d8730005bd74d87300a5ee72d8730005ed72d87300adbe7498730005bd7498730006f76198730004ff7458730014fe7458730014fc7458730004ff725873000cfe725873000cfc725873001ef66118730006f5611873001cff7690730004fe7690730004fd769073026d7e75907300057d7590730016be6490730006bd6490730005fa7090730005f97090730004ff7650730004fd7650730004fc7650730006bf6450730016bc645073001cfd76cc73001ef661cc730006f561cc730005fa70cc730005f970cc7300adbe748c730005bd748c730005fa708c73001ef6610c730006f5610c730005fa700c730005f9700c73001cff7688730004fe7688730004fd768873000eee6288730006ed6288730005fa7088730005f970887300a7e82088730004ff7648730004fd7648730004fc7648730005fb7048730005f8704873008cfd7690330006bf6490330016bc6490330014ff76503300057f755033026d7c7550330016be6450330006bd6450330005df7350330005dc735033009ebe64d923009f9c43d92300c4fe75d9230004fd75d92300c4fc75d9230006dd73d923009edf43d923009ebc43d923009edc43d923000cfe72d9230004fd72d923000cfc72d923009ebf42d923001cfe71d9230004fd71d9230006fa70d923009ebc645923009f9f4359230004ff75592300c4fe75592300c4fc7559230006bf745923009ebe545923009edf735923009eb
  | 17 => 0x4fe73d8540004fd73d854000cfe72d8540004fd72d854000cfc72d854004ef641d854004ef541d8540006f721d8540006f421d85400bd7e75985400057d75985400067f65985400067c6598540005de7398540005dd7398540006df6398540006dc6398540006f7619854003df970985400057f75585400bd7c75585400067f65585400067c6558540005df7358540005dc7358540006df6358540006dc6358540005ef72585400b5ec725854005dfb70585400067f65185400067c6518540006df6318540006dc631854001ef66118540006f56118540004fe7694540004fd769454001cfc76945400067f65945400c67c6594540015be7494540005bd74945400073d5494540006df6394540006dc63945400bf775194540004ff7654540004fe7654540004fc76545400067f65545400c67c6554540015be74545402bf3e5454540006df6354540006dc635454001cbc7650540005bf7550540005bd75505400073f6550540136be6550540136bc65505400073c65505401363c65505400079f6350540006bc63505400079c63505400069c6350540006bf6250540015bf7150540017b77150540007b7615054001ebe615054001ebc6150540007b46150540007bb7050540005bc7050540007b87050540016bf6050540017bb6050540004fe76cc540004fd76cc540004fc76cc5400067f65cc5402b67c65cc540006df63cc540006dc63cc540004fe768c540004fd768c54001cfc768c5400bd7e758c5400057d758c5400067f658c5402ae7c658c540015be748c540005bd748c540006df638c540006dc638c540005fa708c540005f9708c540004ff764c540004fe764c540004fc764c5400067f654c5402a67c654c540006df634c540006dc634c540004fe760c540004fd760c54001cfc760c5400067f650c54029e7c650c540015be740c540005bd740c540006df630c540006dc630c540004fe7688540004fd768854001cfc76885400067f65885402967c6588540015be7488540005bd7488540006df6388540006dc6388540006ef628854000eec6288540004ff7648540004fe7648540004fc76485400067f654854028e7c6548540006df6348540006dc6348540284fe769414027e7f65941400c67c6594140015bc749414027f3e5494140006df6394140006dc63941400bf7b5094140014fe7654140274fd7654140014fc7654140005bf7454140015bc74541400073d5454140006df6354140006dc6354140005bf7590140005bd75901400073f65901400d6be65901400d6bc65901400073c65901400d63c65901400079f6390140006bc63901400079c63901400069c6390140006bf6290140005bd71901401d6bc6190140015be7090140017ba7090140016bf6090140017bb609014026d7e75d93300057d75d93300aebe64d
  | 18 => 0xd7518d400c4fc7518d4007ebe5418d40006bd5418d40006df5318d40006dc5318d4007ede4318d4007edd4318d4000cfe7218d40004fd7218d4000cfc7218d40006de3218d40006dc3218d4001cfe7118d40004fd7118d4007ebf4118d4007ebc4018d4009dde7618d40006de7618d40006df6518d400075f6518d400065f6518d40006de6518d40006dd6518d40006dc6518d400075c6518d400065c6518d4007f9e5418d400079d5418d40006de6218d40006dc6218d4007f9f4118d4007fdb4018d4007f9c4018d4007fd84018d40006df7518d40006de7518d40006dd7518d40006dc7518d4007edf7418d4007ede7418d4007edc7418d4007edf5418d4007ede5418d4007e9e5418d4007edd5418d400069d5418d4007edc5418d40006df7218d40006de7218d40006dd7218d40006dc7218d40006df5218d40006de5218d40006dc5218d4007edf4218d4007ede4218d4007edd4218d4007edc4218d40006df7118d40006de7118d40006dd7118d40006dc7118d40006df5118d40006dc5118d4007edf4118d4007e9f4118d4007ede4118d4007edd4118d4007edc4118d40006df2118d40006dc2118d4007edf7018d4007edd7018d40006df5018d40006dc5018d4007edf4018d4007ede4018d4007edd4018d4007edc4018d4007e9c4018d40006df2018d40006dc2018d40004fe7694d40004fd7694d40004fc7694d400067f6594d400c67c6594d400073d5494d40006df6394d40006dc6394d400bf5f5394d40004ff7654d40004fe7654d40004fc7654d400067f6554d400c67c6554d40006df6354d40006dc6354d4000cfe76d89400067f65d89400067c65d8940006df63d8940006dc63d89400b6ee62d89400c4fe75d8940004fd75d89400c4fc75d894000cfc74d894006ebe54d8940006bd54d8940004fe73d8940004fd73d89400b6ee42d894006eed42d894001cfe71d8940004fd71d894006ebf41d89400b6ec21d8940014fd70d894006ebc40d89400b6ef20d89400057f75589400bd7c75589400067f65589400067c6558940005df7358940005dc7358940006df6358940006dc63589400b6ec6258940005f77158940005f471589402d5fb7058940004ff7654940004fe7654940004fc76549400067f65549400c67c65549400073d5454940006df6354940006dc6354940004fe76cc940004fd76cc940004fc76cc9400067f65cc9402ce7c65cc940006df63cc940006dc63cc940004ff764c940004fe764c940004fc764c9400057f754c9400bd7c754c9400067f654c9402c67c654c940005bf744c940015bc744c940006df634c940006dc634c940005f7714c940005f4714c940005fb704c940005f8704c9400067f65d85400067c65d8540006df63d8540006dc63d85400c4fe75d8540004fd75d85400c4fc75d8540
  | 19 => 0x95400067e72d95400067d72d95400067c72d954027e7f42d954027e7e42d954027e7d42d954027e7c42d95400067e32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d954027e7f41d954027e7e41d954027e7d41d954027e7c41d95400067f21d95400067c21d954027e7f70d95400be7e70d954027e7d70d954027e7f40d954027e7e40d954027e7c40d95400067f20d95400067c20d95400be7c6559540005df7359540005dc73595402ddfb7059540274ff7459540006bf7459540004ff7359540006df7359540004df7359540004fc7359540006dc7359540004dc7359540004ff725954000cfe725954000cfc7259540004ff715954001cfc71595402dcff7059540006fb705954027d7e76195400be7e761954027c7e76195402873e74195400bf3d74195402867f64195400067e62195400067c62195402873f41195402867f60195402877b40195402873c40195402877840195400bdbc76551400c6bc76551400c4bc7655140015bf75551400173f75551400073f65551400c6be65551400c6bc65551400bf3c65551400c63c65551400bf3c53551400bf3f5255140005bf71551401febc61551400bf3c5155140007bb7055140005bc7055140007b87055140016bf6055140017bb60551400bf3f50551400067f65d8d400067c65d8d400c4fe75d8d40004fd75d8d400c4fc75d8d40006df53d8d40006dc53d8d4009ede43d8d4009edd43d8d4000cfe72d8d40004fd72d8d4000cfc72d8d40006de32d8d40006dc32d8d4001cfe71d8d40004fd71d8d40006df65d8d400075f65d8d400065f65d8d40006de65d8d40006dd65d8d40006dc65d8d400075c65d8d400065c65d8d4009f9e54d8d400079d54d8d40006de62d8d40006dc62d8d4009f9f41d8d4009fdb40d8d4009f9c40d8d4009fd840d8d40006df75d8d40006de75d8d40006dd75d8d40006dc75d8d4009edf74d8d4009ede74d8d4009edc74d8d4009edf54d8d4009ede54d8d4009edd54d8d4009edc54d8d40006df72d8d40006de72d8d40006dd72d8d40006dc72d8d40006df52d8d40006de52d8d40006dc52d8d4009edf42d8d4009ede42d8d4009edd42d8d4009edc42d8d40006df71d8d40006de71d8d40006dd71d8d40006dc71d8d40006df51d8d40006dc51d8d4009edf41d8d4009ede41d8d4009edd41d8d4009edc41d8d40006df21d8d40006dc21d8d4009edf70d8d4009edd70d8d40006df50d8d40006dc50d8d4009edf40d8d4009ede40d8d4009edc40d8d40006df20d8d40006dc20d8d400bd7e7598d400057d7598d400067f6598d400067c6598d40006df6398d4008df97098d400057f7558d400bd7c7558d400067f6558d400067c6558d400adfb7058d400067f6518d400067c6518d40006dd6318d400c4fe7518d40004f
  | 20 => 0x15bc74cca400079e43cca40004ff764ca40004fd764ca40004fc764ca400057f754ca400d57c754ca40005bf744ca40015bc744ca400079e434ca40005f7714ca40005f4714ca40005fb704ca40005f8704ca4002dfa70d8640006f761986400057f75586400d57c7558640004ff75586400067f75586400047f75586400c4fe75586400c4fc75586400067c75586400c47c7558640006bf545864003ebc5458640004ff7358640004fc7358640006be435864003ebc4358640004ff725864000cfe725864000cfc725864003ebf4258640006bd425864003ef6415864003ef541586401d6bc415864003ebf40586400d57e75186400057d751864001ef66118640006f5611864004dfa701864001cff7694640004fe7694640004fd76946400c67c6594640015be7494640005bd74946400d73f549464001ef66194640006f561946400d7775194640004ff7654640004fd7654640004fc76546400c67e65546400067d6554640005bf7454640015bc74546402bf3c545464001ef66154640006f561546400d5be75906401d73e75906400d53e75906401d73d75906401d5bc7590640006bf6590640006bd6590640005be7390640005bd7290640015be7190640017b671906401d7b661906401d6bd6190640007b561906401d7ba7090640005bd70906401d7b97090640016be6090640017ba6090640004ff76cc640004fe76cc640004fd76cc640015be74cc640005bd74cc64001cff768c640004fe768c640004fd768c6400d57e758c6400057d758c640015be748c640005bd748c640005fa708c640005f9708c640004ff764c640004fd764c640004fc764c640005bf744c640015bc744c64001cff760c640004fe760c640004fd760c6401d5bf740c640015bc740c64001cff7688640004fe7688640004fd76886401d5bf7488640015bc7488640004ff7648640004fd7648640004fc7648640005bf7448640015bc74486400c4fe7694240014fd7694240015be7494240005bd749424027f3c549424027fbb40942400c4fe76d95400be7e65d954027cff74d9540014fe74d954027cfd74d9540014fc74d954027e7f54d954027e7d54d9540004fe73d9540004fd73d95400be7f53d95400be7c53d954000cfe72d9540004fd72d954000cfc72d95400be7f52d95400067e52d95400be7c52d954001cfe71d9540004fd71d95400be7f51d95400be7c51d9540014fd70d95400be7f50d95402857e76d95400c47e76d95400073f74d954027f3c74d95400067e62d95400067c62d954027f3f41d954027f7b40d954027f3c40d954027f7840d954027e7f74d954027e7e74d954027e7d74d954027e7c74d95400067f73d95400067e73d95400067d73d95400067c73d954027e7f43d954027e7e43d954027e7d43d954027e7c43d95400067f72d
  | 21 => 0xa20d8121006fb6098121005bf74581210ddbc7458121005df7358121005dc7358121006f96018121014fe7418121004fd7418121014fc7418121004fe7318121004fd731812101cfd72181211beee21181211beec2118121026f920181210d67e65d964027f3c54d9640285fa70d964027e7e54d964027ebc54d964027e3c54d9640004fe73d9640004fd73d964027ebc43d964000cfe72d9640004fd72d964000cfc72d964027ebf42d964001cfe71d9640004fd71d964027ebc41d9640284fe70d9640006fa70d964027ebf40d96400c4ff76596400d67c6559640015bc74596400d73f54596400067f75596402767f54596400d6bf54596400d63f54596402767d5459640276bc5459640004ff7359640004fc7359640276bc4359640004ff725964000cfe725964000cfc7259640276bf4259640004ff715964001cfc71596400d67f5159640276bc4159640014fc70596400d67c5059640276bf405964009f9c43d8e4007dfa70d8e40006df6398e400c4fe7598e40004fd7598e400c4fc7598e400aede4398e400aedd4398e4000cfe7298e40004fd7298e4000cfc7298e4001cfe7198e40004fd7198e400057f7558e400d57c7558e40004ff7558e400067f7558e400047f7558e400c4fe7558e400c4fc7558e400067c7558e400c47c7558e4008ede4358e4008edd4358e4008ebc4358e40004ff7258e4000cfe7258e4000cfc7258e4008ebf4258e40004ff7158e4001cfc7158e40006dd6318e4007f9c4318e4009dfa7018e40004ff7694e40004fe7694e40004fd7694e400c67c6594e40015be7494e40005bd7494e400d73f5494e400d75f5394e40004ff7654e40004fd7654e40004fc7654e40005bf7454e40015bc7454e400d5be7590e400d5bc7590e40006bf6590e40006bd6590e40015be7390e400179e7390e400079e6390e40006bd6390e400079d6390e40005bd7290e40176be6290e40176bc6290e401d5be7190e40007ba7090e40005bd7090e40007b97090e40016be6090e40017ba6090e400ceee62d8a402e5fa70d8a4000cff7658a400ceec6258a40004ff7558a400c4fe7558a400c4fc7558a40004ff7358a40004fc7358a400ceee4258a40066ed4258a40004ff7158a4001cfc7158a40014fc7058a400ceec2058a40004ff7654a40004fd7654a40004fc7654a400c67c6554a40005bf7454a40015bc7454a400d73f5454a400cdbf7650a4000ebf7650a4000cbf7650a400d5be7550a400d5bc7550a40006bf6550a40006bd6550a40005bc7350a40006bd6350a40015bf7250a40017af7250a4000ebe6250a400cfae6250a40007ad6250a4000ebc6250a401d5bc7150a40005bf7050a40007bb7050a40007b87050a40016be6050a40017ba6050a40004ff76cca40004fe76cca40004fd76cca40005bf74cca40
  | 22 => 0xe21014fe7498221004fd7498221014fc7498221004fe7398221004fd739822101cfe719822101efa7098221046f9209822101efb109822101ef81098221004ff7458221006bf7458221004bf7458221014fe7458221014fc7458221006bc7458221014bc7458221004ff7358221006df7358221004df7358221004fc7358221006dc7358221004dc735822101cfc715822101efb7058221036fa2058221036ec205822101efb105822101ef81058221014fe76d91210debe64d91210c4fe75d9121004fd75d91210c4fc75d91210debe54d9121004fe73d9121004fd73d91210debc43d912101cff72d912101cfd72d912113ebf42d912113ebd42d912100cfd71d91210debf41d9121004fe70d9121004fd70d91210debc40d91210debc64591212edf77159121004ff75591210c4fe75591210c4fc755912113cff7459121006bf7459121004ff7359121004fc735912112cff7259121006ef72591212ecff7159121006f77159121004ff7059121004fc7059121004ff7655121004fe7655121004fd7655121004fc7655121006bf6455121016bc64551210df3c5455121014fe74d8d21004fd74d8d21014fc74d8d2101cff72d8d2101cfd72d8d2110edf32d8d2110edd32d8d21004fe70d8d21004fd70d8d21006df6398d210fdf57198d21014fe7498d21004fd7498d21014fc7498d210ecfe7398d2111cfd7298d21006ed7298d210fcfd7198d21006f57198d2111ef72198d2111ef42198d21004fe7098d21004fd7098d21005bf7458d210ddbc7458d2111df77158d21005fb7058d21005f87058d21004ff7458d21006bf7458d21004bf7458d21014fe7458d21014fc7458d21006bc7458d21014bc7458d21006df7358d210fcff7258d21006ef7258d2111cff7158d21006f77158d2111cf77158d21004ff7058d21006fb7058d21004fb7058d21004fc7058d21006f87058d21004f87058d2110cfe7618d21006dd6318d21014fe7418d21004fd7418d21014fc7418d21006de7318d2101cff7218d2101cfd7218d210eedf3218d210eedd3218d210eef72118d210eef42118d21004fe7018d21004fd7018d21004ff7690d21004fe7690d21004fd7690d21004fc7690d21006bf6490d21016bc6490d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21014ff765052100cfe765052112cfd765052100cfc7650521006bf6450521016bc6450521005ef725052100dec725052100cfe76cc52100cfc76cc521006df63cc521006dc63cc52100dee72cc521005ed72cc52111ef761cc52111cff764c52100cfe764c5210fcfd764c52100cfc764c521006df634c521006dc634c521005ef724c52100dec724c52101fe4214c521014fe74d8121004fd74d8121014fc74d8121004fe73d8121004fd73d812101cfd72d8121056f
  | 23 => 0xf6bc4359031004ff725903100cfe725903100cfc72590310f6bf425903101cfe715903101cfc715903101ebe415903101ebc4159031004ff7059031004fc70590310f6bf4059031004ff765503101cfe7655031004fd765503101cfc76550311febf6455031016bc64550310f73c5455031014fe7498c31124fd7498c31014fc7498c3100cfe7298c3101ede3198c3101ef63198c3101edc3198c3101ef42198c31124ff7690c3101cfe7690c31014fd7690c3101cfc7690c31016be6490c31006bd6490c3101df67190c31005f57190c31124ff7650c310f79c4350c31004ff7458831014fe7458831014fc745883101eef72588310eeec325883101cfc715883101ef4715883101cf4715883101edf315883101edd31588310eef7215883101eee215883101eec215883101ef4215883101ee42158831004ff7058831004fc70588310eeef2058831004ff7650831004fd765083101cfc7650831016be6450831006bd6450831005f7715083101df4715083100cfd76cc83111ede63cc83100eee62cc831006ed62cc83101df671cc831005f571cc83111cff764c831005bf744c8310f5bc744c83111ede634c8310efcc324c831005f7714c83101df4714c831005fb704c831005f8704c83101df7764c431006f7764c431004f7764c43101df7734c43101fd7734c431006f6634c43101fd6634c431007d6534c431007d5534c4310edf6724c4310edf4724c431014fe7498031004fd7498031014fc749803100cfe7298031004fd729803100cfc729803101efa709803101efb109803101ef81098031004ff7458031006bf7458031004bf7458031014fe7458031014fc7458031006bc7458031014bc7458031004ff725803100cfe725803100cfc725803101efb705803101efb105803101ef81058031004ff75592210c4fe75592210c4fc755922101ebf7459221006bf54592210e6bc5459221004ff7359221004fc73592210e6bc435922112ebf425922112ebd425922101cfe715922101cfc715922101ebe415922101ebc4159221004ff7059221004fc70592210e6bf4059221004ff765522101cfe7655221004fd765522101cfc76552211febf6455221016bc64552210e73c5455221014fe7498e21004fd7498e21014fc7498e2101ede7398e2111edf3298e2111edd3298e2101cfe7198e2101cfc7198e2101ede3198e2101edc3198e2111ef72198e2101ef42198e21004fe7098e21004fd7098e21004ff7458e21014fe7458e21014fc7458e2101edf7358e210fedf3258e210fedd3258e2101cfe7158e2101cfc7158e2101ede3158e2101edc3158e21004ff7058e21004fc7058e21004ff7690e2101cfe7690e21004fd7690e2101cfc7690e21016be6490e21006bd6490e21004ff7650e2101cfe7650e21004fd7650e2101cfc765
  | 24 => 0xa715823101ef8715823101efb415823101efa415823101ef9415823101ef8415823101efb315823101efa315823101ef9315823101ef8315823101efb215823101efa215823101ef9215823101ef82158231014fe76d9131106be64d91310c4fe75d9131004fd75d91310c4fc75d9131106be54d913101cfd73d9131106bf43d913100cfe72d9131004fd72d913100cfc72d9131006be42d9131106bc42d9131104fd71d9131106bf41d9131004fe70d9131004fd70d9131106bc40d9131106bc6459131004ff75591310c4fe75591310c4fc7559131104ff7459131006bf7459131114ff7359131006df7359131106bc4359131004ff725913100cfe725913100cfc7259131106bf4259131124ff7159131006f77159131004ff7059131004fc7059131004ff7655131004fe7655131004fd7655131004fc7655131006bf6455131016bc64551311073c5455131114fe7690d31016be6490d31006bd6490d3101cfc7650d31006bf6450d31016bc6450d31005f77150d3101df47150d3100cfe76d89310feee62d8931014fe74d8931004fd74d8931014fc74d893101cfd73d89310feee32d89310feef21d8931004fe70d8931004fd70d89310feec20d8931005bf7458931105bc74589310feec6258931005fb7058931005f87058931004ff7650931004fe7650931004fc7650931016be6450931006bd645093110cfe76cc931005de76cc93110ede76cc931006df64cc931006dd64cc9310fddd72cc93100ede62cc93100edc62cc93101dde71cc93101ddc71cc93101cfc764c931005bf744c931105bc744c931006ef624c93100eec624c931005f7714c93101df4714c931005fb704c931005f8704c93101ddc764c93100edc764c93101cdc764c9310079f744c9310079c744c931006df644c931006dd644c9310fddf724c931007cf724c931007cf624c93100ede624c93100edc624c9310ffcc624c93100ecc624c931007d7714c93101dde714c93101ddc714c931007d4714c931007db704c931007d8704c931014ff7650531104fd7650531014fc7650531006bf6450531016bc6450531005df7350531005dc735053101dde73cc53101df673cc53101fd763cc53111ef662cc53111ef462cc531007d732cc531007d532cc531014fe74d8131004fd74d8131014fc74d813100cfe72d8131004fd72d813100cfc72d8131006fb20d8131006f820d8131006fb6098131005bf7458131105bc7458131005ef72581310fdec7258131006f96018131014fe7418131004fd7418131014fc741813100cfe7218131004fd721813100cfc7218131006df3218131006dd321813119ede311813119edc3118131006fb2018131006f82018131004ff75590310c4fe75590310c4fc755903101ebf7459031006bf54590310f6bc54590310f4fc7359031
  | 25 => 0x923101ebc2159231006bf7059231006be7059231006bd7059231006bc7059231006bf5059231006bc5059231006bf2059231006bc205923101ebf105923101ebe105923101ebd105923101ebc1059231004ff765523101cfe7655231004fd765523101cfc7655231016be6455231006bd64552311173c545523101ede3158e31104fd7690e3117e7e6590e310067d6590e31016be6490e31006bd6490e31014ff7650e3101cfc7650e3116e7e6550e310067d6550e31016be6450e31006bd6450e311179c4350e31005f77150e3101df47150e31004ff7458a31014fe7458a31014fc7458a3101eef7258a3110eee3258a3101cfc7158a3101edf3158a3101edd3158a3101eee2158a3101eec2158a31004ff7058a31004fc7058a31004ff7650a31004fd7650a3101cfc7650a3115e7e6550a310067d6550a31016be6450a31006bd6450a310fcfd76cca31156be64cca31006bd64cca3100cff764ca31005bf744ca31115bc744ca3114ebe644ca31006bd644ca3100eee624ca31006ed624ca3110fcc324ca31005f7714ca3101df4714ca31005fb704ca31005f8704ca3101df576cc631006f576cc63101fb664cc63101fb564cc63101fd673cc631007d653cc631007d553cc63111ef662cc63101ef462cc63101ff260cc63101ff160cc631014fe7498231004fd7498231014fc749823100cfe7298231004fd729823100cfc729823101efa7098231006fb4098231006f84098231006fb2098231006f8209823101efb109823101ef81098231006fb7498231006fa7498231006f97498231006f87498231006fa5498231006f95498231006f85498231006fb7398231006fb4398231006fa4398231006f94398231006f84398231006fb7298231006fa7298231006f97298231006f87298231006fb4298231006fa4298231006f94298231006f84298231006fb3298231006fa3298231006f93298231006f8329823101efa719823101ef9719823101ef8719823101efb419823101efa419823101ef9419823101ef8419823101efb319823101efa319823101ef9319823101ef8319823101efb219823101efa219823101ef9219823101ef82198231004ff7458231014fe7458231014fc7458231004ff725823100cfe725823100cfc725823101efb7058231006fb4058231006f84058231006fb2058231006f8205823101efb105823101ef81058231006fb7458231006fa7458231006f97458231006f87458231006fa5458231006f95458231006f85458231006f97358231006fb4358231006fa4358231006f94358231006f84358231006fb7258231006fa7258231006f97258231006f87258231006fb4258231006fa4258231006f94258231006f84258231006fb3258231006fa3258231006f93258231006f8325823101efb715823101ef
  | 26 => 0xcfe725933100cfc7259331126bf4259331126bf4159331004ff7059331004fc7059331126bc4059331004ff7655331004fe7655331004fd7655331004fc7655331016be6455331006bd64553311273c545533101cfd7690f31016be6490f31006bd6490f3101df67190f31005f57190f310f4ff7650f3111eee62d8b3111eec6258b3111fe72158b31004ff7458b31014fe7458b31014fc7458b3101cfc7358b3111eee4258b3111eec3258b3111ef77158b3111eef2158b3111ef72158b3111ef42158b31004ff7058b31004fc7058b3111eec2058b31004ff7650b31004fd7650b31004fc7650b31016be6450b31006bd6450b3100eee6250b31006ed6250b31005f77150b3101df47150b3101cfd76ccb3100eee62ccb31006ed62ccb3101df671ccb31005f571ccb3101ddd76ccb3100edd76ccb3101cdd76ccb31006df64ccb31006dd64ccb3100ede62ccb3111fce62ccb31007cd62ccb3100edc62ccb3101dde71ccb31007d671ccb31007d571ccb3101ddc71ccb3111fd721ccb3111fd421ccb310ecff764cb31005bf744cb31125bc744cb3111df7714cb3101df4714cb31005fb704cb31005f8704cb31005df764cb310eedf764cb310079f744cb310079c744cb31006df644cb31006dd644cb31007cf724cb3100ede624cb3100edc624cb3111fd7714cb3101dde714cb3101ddc714cb31007d4714cb3101dd4714cb3111fd7214cb3111fd4214cb31007db704cb31007d8704cb31014ff7650731016be6450731006bd6450731005df7350731005dc7350731125be74d8331005bd74d833111dee72d8331005ed72d8331006fb6098331014fe7498331004fd7498331014fc749833100cfe7298331004fd729833100cfc7298331006df3298331006dd32983311c6de31983311c6dc3198331004ff7458331014fe7458331014fc7458331004ff725833100cfe725833100cfc7258331006f96018331004ff75592310c4fe75592310c4fc755923101ebf7459231006bf5459231116be5459231116bc5459231116bf4359231004ff725923100cfe725923100cfc7259231116bf4259231006be4259231116bc425923101cfc715923101ebe415923101ebc4159231004ff7059231004fc7059231116bf4059231116bc4059231006bf7559231006be7559231006bd7559231006bc7559231006bf7359231006bd7359231116bc7359231006bf5359231006bc5359231006bf7259231006be7259231006bd7259231006bc7259231006bf5259231006be5259231006bc5259231006be3259231006bc325923101ebf715923101ebe715923101ebd715923101ebc715923101ebf515923101ebe515923101ebd515923101ebc515923101ebf315923101ebe315923101ebd315923101ebc315923101ebf215923101ebe215923101ebd215
  | 27 => 0xe7694d41004fd7694d41004fc7694d410c67e6594d41015be7494d41005bd7494d411373f5494d411375f5394d41004ff7654d41004fe7654d41004fc7654d41005bf7454d41015bc7454d4101cbe7690d41135be7590d41135bc7590d41006bf6590d41006bd6590d41015be7390d410179e7390d41006bf6390d410079f6390d410079c6390d41005bd7290d41176be6290d41176bc6290d4101dbe7190d41007b67190d41007b57190d4101dbc7190d41016bf6190d41017b76190d41005bd7090d4100cfe76d894112eee62d89410c4fe75d8941004fd75d89410c4fc75d894101cfd74d8941004fe73d8941004fd73d894112eee42d89410e6ed42d8941014fd71d894112eef21d8941004fe70d8941004fd70d894112eec20d894112eec62589412f5f77158941004ff7654941004fe7654941004fc76549410c67e6554941005bf7454941015bc74549411373f5454941005f7715494101df4715494101dbc765094100ebc765094101cbc7650941135be7550941135bc7550941006bf6550941006bd6550941005bc7350941006bf6350941015bf7250941017af7250941007af625094100ebe625094100ebc625094112fac6250941007b7715094101dbe715094101dbc7150941007b4715094101db47150941016bf6150941017b76150941005bf7050941004fe76cc941004fd76cc941004fc76cc941005bf74cc941015bc74cc9410079e43cc941004ff764c941004fe764c941004fc764c9410057f754c9411357c754c941005bf744c941015bc744c9410079e434c941005f7714c94101df4714c941005fb704c941005f8704c941014fe76545412bcfd7654541014fc7654541005bf7454541015bc74545412bf3c545454101fb441545410c4fe75d8141004fd75d81410c4fc75d814101cfd74d8141004fe73d8141004fd73d814100cfe72d8141004fd72d814100cfc72d814105efa40d8141006fb60981410057f75581411357c7558141005df7358141005dc7358141005ef725814112dec72581411357e75181410057d7518141006f960181410c4fe75181410067e75181410c47e7518141004fd75181410067d75181410047d75181410c4fc751814101cfd7418141006bf541814102ebc5418141004fe7318141004fd7318141006be431814102ebc431814100cfe7218141004fd721814100cfc721814102ebf4218141006bd421814102ef571181411cebe41181411cebc411814102ebf401814102ef94018141126be64d93310c4fe75d9331004fd75d93310c4fc75d9331006de73d933100cfe72d9331004fd72d933100cfc72d9331006f571d9331004fe70d9331004fd70d9331126bc6459331004ff75593310c4fe75593310c4fc7559331006bf7459331126be545933101cfc7359331126bc4359331004ff7259331
  | 28 => 0x4e410c67e6554e410067d6554e41004ff7558a410c4fe7558a410c4fc7558a410debe5458a41006bd5458a41004ff7358a41004fc7358a4101eef7258a4113eee4258a410deed4258a4101cfe7158a4101cfc7158a4101ebf4158a4101ebd4158a4101eee2158a4101eec2158a41004ff7058a41004fc7058a410debc4058a41004ff7654a41004fd7654a4101cfc7654a410c67e6554a410067d6554a410073d5454a41005f77154a4101df47154a41004ff76cca4101cfe76cca41004fd76cca412ce7e65cca410067d65cca41006de63cca41006dd63cca41004ff764ca41004fd764ca4101cfc764ca410057f754ca411457c754ca412c67e654ca410067d654ca41005bf744ca41015bc744ca41006de634ca41006dd634ca41005f7714ca4101df4714ca41005fb704ca41005f8704ca410c4fe7598241004fd75982410c4fc7598241004fe7398241004fd739824100cfe7298241004fd729824100cfc729824101cfe719824101ef6719824101cf6719824101efa709824104ef9409824101ef7109824101efb109824101ef81098241004ff75582410c4fe75582410c4fc755824103ebe5458241006bd5458241004ff7358241004fc7358241004ff725824100cfe725824100cfc725824101cfc715824101ebf415824101ebd415824101efb705824103efa405824103ebc405824101efb105824101ef810582410c4fe76d95411367e65d9541015be74d954101dbd74d95411373f54d954101cff74d954101cfd74d9541136bd74d954101cbd74d95413067f54d9541136bf54d95411363f54d95413067d54d9541306bc54d9541004fe73d9541004fd73d9541306bc43d954100cfe72d9541004fd72d954100cfc72d9541306bf42d9541014fd71d95411367f51d954130ebe41d954130ebc41d9541004fe70d9541004fd70d95411367c50d9541306bf40d95411367c65595412bf3c54595412fdf771595412bcff7459541006bf74595412be7e54595412bebc54595412be3c5459541004ff7359541004fc73595412bebc4359541004ff725954100cfe725954100cfc72595412bebf42595412fcff7159541006f771595411febe41595411febc4159541004ff7059541004fc70595412bebf40595411357e75d8d410057d75d8d410c4fe75d8d410067e75d8d410c47e75d8d41004fd75d8d410067d75d8d410047d75d8d410c4fc75d8d4101cfd74d8d41116de43d8d41116dd43d8d41116bc43d8d4100cfe72d8d41004fd72d8d4100cfc72d8d41116bf42d8d41004fe70d8d41004fd70d8d41006df6398d41105f57198d41125f77158d41006dd6318d410c4fe7518d41004fd7518d410c4fc7518d4101cfd7418d410f6de4318d410f6dd4318d4100cfe7218d41004fd7218d4100cfc7218d41004fe7018d41004fd7018d41004f
  | 29 => 0x6fb7418132006fa7418132006f97418132006f87418132006fa5418132006f95418132006f85418132076fb7318132076f97318132006fb4318132006fa4318132006f94318132006f84318132076fb7218132076fa7218132076f87218132076fb4218132076fa4218132076f94218132076f84218132076fb3218132076fa3218132076f93218132076f83218132006fb7118132006fa7118132006f97118132006f87118132006fb4118132006f84118132076fb2118132076fa2118132076f92118132076f8211813201e7f75596412be7f54596412be7d5459641004ff7359641004fc73596411467f53596411467c5359641004ff725964100cfe725964100cfc72596411467f52596410067e52596411467c525964101cfe715964101cfc715964101e7e515964101e7c5159641004ff7059641004fc70596411467f50596411467c505964101ef710596412be7e74596412be7d74596412be7c74596410067f73596410067e73596410067d73596410067c73596412be7f43596412be7e43596412be7d43596412be7c43596410067f72596410067e72596410067d72596410067c72596412be7f42596412be7e42596412be7d42596412be7c42596410067e32596410067c325964101e7f715964101e7e715964101e7c715964101e7f415964101e7e415964101e7d415964101e7c415964101e7f315964101e7e315964101e7d315964101e7c315964101e7f215964101e7e215964101e7d215964101e7c21596410067f70596410067e70596410067d70596410067c70596412be7f40596412be7e40596412be7d40596412be7c40596410067f20596410067c205964101e7f105964101e77105964101e7e105964101e7d105964101e7c10596411fdbf76552410c6bf76552410c4bf7655241015bf75552410173f75552410c6be65552411ff3e65552410c63e65552411ff3d65552410c6bc65552411473c53552411473f52552411fdbf7155241007b771552411ffb47155241016be6155241017b661552411ff3e51552411ff3c5155241005bc70552411473f50552410c4fe7598e41004fd7598e410c4fc7598e41126be5498e41006bd5498e4101ede7398e41126de4398e41126dd4398e4100cfe7298e41004fd7298e4100cfc7298e4101cfe7198e4101ebf4198e4101ebd4198e4101ede3198e4101edc3198e41004fe7098e41004fd7098e41126bc4098e41004ff7558e410c4fe7558e410c4fc7558e4101edf7358e41106de4358e41106dd4358e41004ff7258e4100cfe7258e4100cfc7258e4101cfc7158e4101ede3158e4101edc3158e41004ff7058e41004fc7058e41004ff7694e4101cfe7694e41004fd7694e410c67e6594e410067d6594e410073d5494e411475f5394e41004ff7654e41004fd7654e4101cfc765
  | 30 => 0x56418532006f46418532007b46418532006b464185320efd57318532007d64318532007d54318532007e732185320efd632185320efd432185320efe4321853201ef7741853201ef6741853201ef5741853201ef47418532006f65418532006f55418532006f4541853201ef7731853201ef5731853201ed57318532006f74318532006f64318532006f54318532006f4431853201ef7721853201ef6721853201ef472185320eef742185320eef642185320eef542185320eef442185320eef732185320eef632185320eef532185320eef4321853201ef7701853201ef6701853201ef5701853201ef47018532006f74018532006f440185320eef720185320eef620185320eef520185320eef42018532006bf64d8132006bc64d8132006f761d8132006f461d8132014fe74d8132004fd74d8132014fc74d81320a6dd73d813201cfe71d8132004fd71d8132006fb40d8132006f840d81320a6fa20d8132006fb64d8132007bb64d8132006bb64d8132006fa64d8132006f964d8132006f864d8132007b864d8132006b864d81320a7d973d8132007da43d8132007d943d8132007eb32d81320a7da32d81320a7d832d81320a7e832d8132006fb61d8132007f361d8132006f361d8132006fa61d8132006f961d8132006f861d8132007f061d8132006f061d8132006fb74d8132006fa74d8132006f974d8132006f874d8132006fa54d8132006f954d8132006f854d81320a6fb73d81320a6f973d81320a6d973d8132006fb43d8132006fa43d8132006f943d8132006f843d81320a6fb72d81320a6fa72d81320a6f872d81320a6fb42d81320a6fa42d81320a6f942d81320a6f842d81320a6fb32d81320a6fa32d81320a6f832d8132006fb71d8132006fa71d8132006f971d8132006f871d8132006fb41d8132006f841d81320a6fb21d81320a6fa21d81320a6f921d81320a6f821d813214dbe7498132005bd7498132006bf6498132006bc6498132005f67198132005f57198132006f76198132006f46198132006fb6098132005bf745813214dbc7458132006bf6458132006bc6458132005f77158132005f47158132006f76158132006f46158132006bf6418132006bc6418132006f76118132006f46118132006f96018132014fe7418132004fd7418132014fc741813201cfe7118132004fd7118132006fb4018132006f84018132076f920181320a5fa7618132006fa7618132006fb6418132007bb6418132006bb6418132006fa6418132006f96418132006f86418132007b86418132006b86418132077db7318132007da4318132007d94318132007eb3218132077da3218132077d83218132077e83218132006fb6118132007f36118132006f36118132006fa6118132006f96118132006f86118132007f06118132006f06118132
  | 31 => 0x91320073f65191320063f6519132006be6519132006bd6519132006bc65191320073c65191320063c651913231f9d731913231ebf631913231ebf621913231f9e321913231f9c321913231fac3219132004ff7655132004fe7655132004fd7655132004fc7655132006bf6455132016bc645513214f3c545513231cfe7690d320067f6590d3217e7c6590d32176bf6490d32016bc6490d3231dde7690d32316de7690d32005df7590d32005dd7590d320075f6590d320075c6590d32165dd7490d321779f6490d32016de6490d32016dc6490d3214f9c6490d320169c6490d3214f9e5490d320079d5490d3200dde7290d3200ddc7290d32176df6290d321779e4290d321779c4290d32005dd7190d3214f9f4190d32005de7090d3214f9c4090d32014ff7650d3200cfe7650d32164fd7650d3200cfc7650d320067f6550d3216e7c6550d32006bf6450d32016bc6450d3214f9c4350d32005ef7250d3200dec7250d3200ddc7650d32016dc7650d3200cdc7650d32005df7550d32005dd7550d320075f6550d320075c6550d32175df7450d320079f7450d320079f6450d32016de6450d32016dc6450d3214f9c6450d32007cf7250d3200dde7250d3200ddc7250d32167cc7250d32166df6250d321679f4250d321679d4250d32005df7150d32005dc7050d32007af64cc932007ac64cc93200dee73cc93200fce73cc93200eef63cc93200fcf63cc932007ce43cc932007cd43cc932006bf64d8532006bc64d8532014fe74d8532004fd74d8532014fc74d8532006f741d8532006f441d853211ef621d8532004fe70d8532004fd70d8532006f764d8532007b764d8532006b764d8532006f664d8532006f564d8532006f464d8532007b464d8532006b464d853211fd773d8532007d643d8532007d543d8532007e732d853211fd632d853211fd432d853211fe432d8532006f774d8532006f674d8532006f574d8532006f474d8532006f654d8532006f554d8532006f454d853211ef773d853211ef573d8532006f743d8532006f643d8532006f543d8532006f443d853211ef772d853211ef672d853211ef472d853211ef742d853211ef642d853211ef542d853211ef442d853211ef732d853211ef632d853211ef432d8532006f770d8532006f670d8532006f570d8532006f470d8532006f740d8532006f440d853211ef720d853211ef620d853211ef520d853211ef420d853214dbe7498532005bd7498532006bf6498532006bc6498532006f76198532005fa7098532005f97098532005bf745853214dbc7458532006bf6458532006bc6458532005fb7058532005f87058532006bf6418532006bc641853201ef66118532006f5611853211df67618532006f67618532006f76418532007b76418532006b76418532006f66418532006f
  | 32 => 0xddc7290f321779e4290f321779c4290f32005dd7190f321579f4190f32005de7090f321579c4090f32324ff7650f32006bf6450f32016bc6450f321579c4350f32325df7650f3232edf7650f32005df7550f32005dd7550f320079f7450f320079f6450f32016de6450f32016dc6450f321579c6450f3200dde7250f3200ddc7250f321679f4250f321679d4250f32005df7150f32005dc7050f32155be7498732005bd7498732006f76198732005fa7098732005f97098732004ff7458732014fe7458732014fc74587320fef62158732004ff7058732004fc705873201ef66118732006f56118732006fb6098332014fe7498332004fd7498332014fc749833201cfe7198332004fd7198332096f92098332005bf7458332155bc7458332004ff7458332006bf7458332004bf7458332014fe7458332014fc7458332006bc7458332014bc7458332086dc7358332004ff715833201cfc7158332086fa2058332006f96018332014fe76d913214ebe64d91320c4fe75d9132004fd75d91320c4fc75d9132006bf54d913214ebe54d913214ebc54d913200cfd73d913214ebf43d9132174ff72d9132174fd72d9132176bf42d9132176bd42d913201cfe71d9132004fd71d913214ebf41d913214ebc41d9132004fe70d9132004fd70d913214ebf40d913214ebc40d913231dbe76d9132014be76d9132006bf65d91320073f65d91320063f65d9132006be65d9132006bc65d91321779f73d91321779e32d91321779c32d9132177ac32d9132006bf75d9132006be75d9132006bd75d9132006bc75d9132176bf73d913214ebe73d9132176bd73d9132006bf53d9132006bc53d9132176bf72d9132176be72d9132176bd72d9132176bc72d9132176bf52d9132176be52d9132176bd52d9132176bc52d9132176bf32d9132176be32d9132176bc32d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006bc51d9132176bf21d9132176be21d9132176bd21d9132176bc21d9132006bf70d9132006be70d9132006bd70d9132006bc70d9132006bf50d9132006bc50d9132176bf20d9132176be20d9132176bd20d9132176bc20d91320057f75591322c57c75591320067f655913214ebc6459132325df7359132005f77159132005f47159132005fb7059132005f87059132004ff75591320067f75591320047f75591320c4fe75591320c4fc75591320067c75591320c47c7559132174ff7459132006bf7459132324ff7359132006df7359132164ff7259132006ef7259132004ff7159132006f77159132004f7715913201cfc7159132006f4715913201cf47159132004ff7059132006fb7059132004fb7059132004fc7059132006f87059132004f87059132175be761913214ebe7619132174be7619132006bf651
  | 33 => 0xc7558d42155ef7258d42005f77158d42005f47158d42005fb7058d42005f87058d42006dd6318d420c4fe7518d42004fd7518d420c4fc7518d4200cfd7418d4231ebd7418d4232ebe5418d42006bd5418d4232ebf4318d4232ede4318d4232edd4318d42014fd7218d4231ebe4218d4231ebc4218d4231edd3218d4201cfe7118d42004fd7118d4232ebf4118d42004fe7018d42004fd7018d4232ebc4018d42004fe7694d42004fd7694d42004fc7694d420067f6594d420c67c6594d42015be7494d42005bd7494d420073d5494d4215f5f5394d42004ff7654d42004fe7654d42004fc7654d42015be7454d4200dbc7650d42166bc7650d4200cbc7650d42005bf7550d42005bd7550d42015bf7350d420179f7350d420079f6350d42006bc6350d420079c6350d42007af7250d4200dbe7250d4200dbc7250d42167ac7250d42016bf6250d42017af6250d42005bf7150d42005bc7050d4201cfe76d85420c4fe75d8542004fd75d85420c4fc75d854200cfd74d8542004fe73d8542004fd73d8542014fd72d85422f6f641d85422eef621d8542004fe70d8542004fd70d854215d7e75985420057d7598542006f7619854201ef66118542006f561185420c4fe75d8142004fd75d81420c4fc75d814200cfd74d8142216bd74d81422d6be54d8142006bd54d8142004fe73d8142004fd73d8142014fd72d814201cfe71d8142004fd71d81422d6bf41d81422d6fa40d81422d6bc40d8142216fa20d8142006fb60981420057f755814215d7c7558142005df7358142005dc7358142005f77158142005f47158142006f960181420c4fe7518142004fd75181420c4fc751814200cfd7418142004fe7318142004fd7318142014fd721814201cfe7118142004fd71181422e6f9401814220ef92018142156be64d933231dde73d93320c4fe75d9332004fd75d93320c4fc75d9332164fd74d9332156be54d933231cfe73d9332006de73d9332156bf43d9332006ed72d9332176be42d9332176bc42d933201cfe71d9332004fd71d9332156bf41d9332004fe70d9332004fd70d9332156bc40d9332014ff7659332156bc6459332004ff75593320c4fe75593320c4fc7559332006bf745933200cfc7359332156bc4359332166bf4259332166bd4259332004ff715933201cfc7159332004ff7059332004fc7059332004ff7655332004fe7655332004fd7655332004fc7655332006bf6455332016bc64553321573c545533200cff7690f32014fe7690f3200cfd7690f32016be6490f32006bd6490f3200dee7290f32005ed7290f3200ddd7690f32016dd7690f3200cdd7690f32005df7590f32005dd7590f32016de6490f321579e6490f320079d6490f32016dc6490f321579e5490f320079d5490f3200dde7290f32177ce7290f32007cd7290f32
  | 34 => 0x9543004fb7059543004fc7059543006f87059543004f87059543364fe7694d430c67e6594d4316f5f5394d4335f9c4394d43014fe7654d43354fd7654d43014fc7654d43005bf7454d43015bc7454d433579c4354d43006bf6590d43006bd6590d43015be7390d430179e7390d43016bf6390d430179f6390d43005bd7290d43176be6290d43176bc6290d4300cfe76d8943166ee62d89430c4fe75d8943004fd75d89430c4fc75d8943014fd73d8943166ee42d8943166ee32d894301cfe71d8943004fd71d8943004fe70d8943004fd70d89430057f755894316d7c7558943166ec6258943005f77158943005f47158943005fb7058943005f870589430c4fe75d8543004fd75d85430c4fc75d8543006be43d8543126bc43d854300cfe72d8543004fd72d854300cfc72d8543126bf42d8543126f641d8543006f721d8543006f421d8543004fe70d8543004fd70d854316d7e75985430057d7598543006f76198543005fa7098543005f9709854301ef66118543006f561185430c4fe75d8143004fd75d81430c4fc75d814300cfe72d8143004fd72d814300cfc72d814301cfe71d8143004fd71d8143006fb50d8143006f850d81430aefa40d8143006fb20d8143006f820d8143006fb60981430057f755814316d7c7558143006f960181430c4fe7518143004fd75181430c4fc751814307edf4318143006be431814307ebc431814307edc431814300cfe7218143004fd721814300cfc721814307ebf421814301cfe7118143004fd7118143006fb5018143006f8501814307ef94018143006fb2018143006f820181430c4fe76d954215e7e65d9542184fd75d954200cff74d954200cfd74d954234e7f54d954234e7d54d9542004fe73d9542004fd73d954215e7c53d9542014fd72d95423467f52d954201cfe71d9542004fd71d954215e7f51d9542004fe70d9542004fd70d954215e7c50d95420c4ff765954215e7c6559542335bf745954233def7259542334ff7459542006bf7459542004ff7359542004fc7359542184ff7259542006ef7259542004ff715954201cfc7159542004ff7059542004fc705954200dbc76551420c6bc765514200cbc7655142015bf75551420173f75551420073f65551420c6be65551420c6bc655514215f3c65551420c63c6555142005bf735514215f3c5355142007af725514200dbe725514200dbc7255142187ac7255142016bf6255142017af62551421873f52551421873d5255142005bf71551421febc615514215f3c5155142005bc705514215f3f50551420c4fe75d8d42004fd75d8d420c4fc75d8d4200cfd74d8d42316de43d8d42316dd43d8d42014fd72d8d42326df32d8d4201cfe71d8d42004fd71d8d42004fe70d8d42004fd70d8d42006df6398d4214ded7298d420057f7558d4215d7
  | 35 => 0xcfc7218154286bf421815401cfe7118154006f6711815401cf67118154004fd7118154006f57118154004f57118154286bc4118154286bf4018154286f9401815417e7e65d9643365de73d9643364fe73d9643006de73d964300cfe72d9643004fd72d964300cfc72d964301cfe71d9643004fd71d9643004fe70d9643004fd70d96430c4ff765964317e7c65596430067f75596433567f54596433567d5459643014fc735964317e7c5359643004ff725964300cfe725964300cfc725964317e7f5259643004ff715964301cfc715964317e7f5159643004ff7059643004fc705964317e7c505964317dbf76552430c6bf76552430c4bf7655243015bf75552430173f75552430c6be655524317f3e65552430c63e65552430073d65552430c6bc6555243005bf73552430079f73552430079c7355243016be63552430179e635524317f3c5355243175be7255243175bc725524317f3f5255243005bf71552431febe615524317f3c5155243005bc705524317f3f50552430c4fe7694e43014fd7694e43015be7494e43005bd7494e430073d5494e4335f9f4394e43176ee62d8a4300cff7658a43015bc7458a43176ec6258a43177ae4258a43004ff7558a430c4fe7558a430c4fc7558a4314ebe5458a43006bd5458a43014fc7358a4314ebf4358a43176be4258a43176ee4258a43176bc4258a43176ec3258a43004ff7158a4301cfc7158a4314ebf4158a43004ff7058a43004fc7058a4314ebc4058a43006f76198643004ff75586430c4fe75586430c4fc7558643004ff725864300cfe725864300cfc7258643106f64158643004ff7058643004fc705864317d7e75186430057d751864301ef66118643006f5611864317d7e75d82430057d75d8243006fb60982430c4fe7598243004fd75982430c4fc759824309edf439824309edc439824300cfe7298243004fd729824300cfc729824301cfe7198243004fd719824309ef94098243004ff75582430c4fe75582430c4fc755824308ebe5458243006bd5458243004ff725824300cfe725824300cfc7258243004ff715824301cfc715824308ebf415824308efa405824308ebc4058243006f960182430c4fe76d954316e7e65d954335cff74d954335cfd74d954335e7f54d954335e7d54d9543014fd73d954316e7f53d954335ebc43d954300cfe72d9543004fd72d954300cfc72d95430067e52d954316e7c52d954335ebf42d954301cfe71d9543004fd71d954316e7f51d9543004fe70d9543004fd70d954316e7c50d954316e7c655954336ddf7359543005fb7059543005f87059543354ff7459543006bf745954336cff7359543006df7359543356bc4359543004ff725954300cfe725954300cfc7259543356bf4259543004ff715954301cfc7159543004ff7059543006fb705
  | 36 => 0x400a0028004004c00b00100340000002000c004000400900000000034000000c006000c00800200010028004000400200100160010005000000000000060098003003c000000000a0008001000000000240010004003014c0090000003002c000000000f00bc0000028000000800a0014000000c0040000001001c0030000003007401b000001100000150000002000400100340160008019000c000000400000040010010001002401d000c01000040010008006001400d0080000000c0000030009002400c000800900100030000014002800000040000000001000c0000004019000000e00000030000005000802800040020000000000000600b8003006000b0008004003401a00440050008009006c00400040020024001000000100040000010001002c003004c00a000000000400020090002011c000002000f003400b0010000001800200040000000004001000a0000002001400000040010004002000c001002800f000001e0014000000400000000000004014000000100640050004010002000400180000008005002800100040000014000000000300140070000011000c00300000030008002000800136f3c54d8d540c4fd74d8d54396bd74d8d540065e53d8d5436ede43d8d5436ebc43d8d5400cfe72d8d54004fd72d8d5400cfc72d8d5436ebf42d8d5401cfe71d8d54004fd71d8d54004fe70d8d54004fd70d8d5435f3c5498d54006df6398d543573c5458d54005fb7058d54005f87058d543673c5418d54006dd6318d540c4fd7418d54366dd4318d5400cfe7218d54004fd7218d5400cfc7218d5401cfe7118d54004fd7118d54004fe7018d54004fd7018d5400cfe76d895433f3c54d8954186ee62d89540c4fd74d8954004fe73d8954004fd73d8954186ee42d895401cfe71d8954004fd71d8954004fe70d8954004fd70d895438f3c5458954186ec625895401cfe76d85542ff3c54d85540c4fd74d8554386bd74d85542fe7e54d85542febc54d85542fe3c54d8554004fe73d8554004fd73d85542febc43d855400cfe72d8554004fd72d855400cfc72d85542febf42d85540067651d85542fef641d85541febc41d8554004fe70d8554004fd70d85542febf40d85543073c5498554006f761985542bf3c545855437f3c541855401ef66118554006f561185542df3c54d81540c4fd74d8154004fe73d8154004fd73d815400cfe72d8154004fd72d815400cfc72d815401cfe71d8154004fd71d81542defa40d815427f3c5498154006fb60981542773c5458154005df7358154005dc73581542873c5418154005f67118154005f57118154006f960181540c4fd7418154376bd74181542867e5418154286bc54181542863c5418154004fe7318154004fd7318154286bc431815400cfe7218154004fd7218154
  | 37 => 0x20010007006000800500090010003000800e000c003001c004002001e0030000000001a0004007005800000200150008001000800000080000000004000401a00000000020000002400200080030008002005000f00480040008000000c001000c0070004001000400f001800100000030000001000000600040000000006001c0070000000004c017000000600000140084007006800c00700030010000003800a0008000006c006000400200080000070002000400b00000170008000000c01200000000020009000c000000c0060008004000400100380020008003000c0010020005001c000000800000000030020008001000f0010001001000200280000000001002400f0064008004c00100100130000015000800600040060030002000800100000090020003000000e000c013001000600040020010003002400400040010004003008c03a0004002001c003000c00f0004000000001f000c000000000c000c00000000070000003002c00b00080000010005014c0000000000005c00f00000080008011000800000000010004000000c005000000100e400100640060010007001c000000000000440020004000000400000000000004005001c001000c00100000000004000001000b003000d000800400000470004001001000b000000a001000d0008004007000000000000024000000000000040020008003000000c001c00100240000024005000000400040020000019000c0080000013001400400500000028005000400300200070000005006c008000000000200000034014001800a007c02000040490008002000c0020000006000000600000000004003001c003000000a000c002004801300080010004011002000300a000000000170000000000c000000801600600050000002001c00c000000000000000000007000400200100020064005007800000100010000005000000000000050018009001000b0008002000400500140030000000002000000c001e00040060010000002000300000020004000000400c000000200040050010000002000300180010014003000400d00180030008008003c000000c000001c00300000050000005002000d0000000003c00000040050000000000400300100160018011000c000000c000002800200a800000b800100800020074003000400c000000e0000001001c000000400600080000010000000c002000c00000180070010000004c00000000000030006000c0030004002000000e003000300140060048008001000000080030000001003c00500000000000000001000000340010008001003c008000000400000030034001002c004002000c00840020050011006c00000180050010003001401100080030004004006800200100150010000000c005000c0140004001000
  | 38 => 0x4009003000800100360000005001c00000040000004002000400000300030010000000c00d000800000f0015004c000000c003007800000380010008002000400300040030004005000400b00000080004018000800b00000000000006004800400000070034000003400b00000000000002000400c00140060000002004800100040010004005000801c000800400040100008000007000c0004000005001400080060098009001c0020000000000000600080000004000001400000240030000003000800a00100090000006000400200000030004005000000000340050000002002800b000001000000030008001002c002001000000040000000000000000900000000014000025c004006800400080020000002002c000000000200080000020001000800000000040010002001c001000800000140030000022002000000040210048009000000000640000010001000c00000040000094003001800600000000000000001400c002c0090078005000000d0008000000000b00080020004008000000200240000014006004c00200040060104001000000000680080018044000c0040054004008400a0014002000400600580000000006002400100040100090001000400100000000010004000000000300000018000003000000000010018001002c0010004005003800300000010010008000800800140070008004000000900200020000000000c003000000000200010018000000000400000020004000000c0000004000000c0010068010000000d002801700300010000002000800800040030018000003400200100090028011000800300040060008001002c0010004000001800900000050008000000000000480000030000002c00b0000009002400100100010020012000c00500180010018002002000e002c00b00000030000000000800c0018007003800a00000000004000001001e00040030008001000000f00040030004005000000b00040080008006004800700040050000005000c0000028000000c000005400000040000000005001000200140270014001000c00c00000170000005001c0020000001003000800180120008000003000000700040014001006c001002c0000024005002c000003c0000000006000c001004400900000010008004000800200040000004002000000e000c002001c001000401000080060030004006c000002c003001000c001c0000000006000c000005400000000090028009002400a000001600400090014000000800100000210004000008000900480000000009001c004003c0000014000000000300140010010001001c000000400000400020000002000800b003c00600000030068007000400300680010008000001001400080000000004000000100080030020006002c00
  | 39 => 0x40020008002000000000000090088005000c000000800700080030004005000800100000020008000002000000080030014000000000100200000080000000400300480030000000000000c001001b000800b00000000058001000c0000004007000000e000800000380030000003000000a0010000000001600080080000005003000000100030000000000400a0008002002c00f00000060010007000c005001c0030004047000c004000000000040100004002000400000000010008006002400100500000010000005800000280020008004002c00200000010000001000c00d000400e00400000010000003000800040070000005005c000000000e001c009000000c00100020004002000c00200280030000001000400600000090004001001c00100000020000005000400500980050000005002c000003c0000000003000000d00000070004006000000600040000008002002c0000004000000001e007800900000090048003000000000200000008004006000b0000000003401f008c00c00080080000007000000701080110014007000400a0000002000000d003000200000030034005004800500200010010004000000e0068000001c01c003c00100000000018002001401a00100050004002003400a000000200040000080000000800c0010006000c00600100060050007000400c00000000018004000800b000c000007c0050010000002c00900000010018044000001b000403e000c000002000300000010000008000c0120034010000c00400100070004000000c005001c01e001400200040000014000000400700340010008027000001d002000d002800c0060010003000600000000014000002c0010004000000c000001800400200060000000000000400240050000000001000700b401000ac00100400000000000000800400000100014014005c00100740100000017005800200040000000000000c00200000020008000000000300040070010000000800000140060004018001c00400640010018000002c007001c0010030001000001600140000000007000000e000c006001801c00000290004006005c0020000001000c00100180060008000000000100040000004000008c000002400700240070020003000000b007000900340040008001001c00100300030004000000800000000000024000000000d000c02c002800a002c00c0030004001c0000000005003c002002c00000040000004002000c0210004000003400000000000040000000800300000180030005002800900000030004001001400100b000100040000004001000000c003c00c001c00100040070008001000000b000c002005000500100010004008000c0000000002000c00100000000004009000000100000000000004000c01300
  | 40 => 0xaf800098c0c628b28e9e789aa24b7812924d8b08a0001dfc00025f82fc80d03981fca50d2eb078140005bf0edc2afa9b004c2d709bbaff4407ef444989ec2c16d15e782130d01c7048921184800029caaec868e12581562cfe428590c7384f51b523f8233fa949afcb3711400e74000426e9dc56a966c03d9c100000000000245e550823e02b963205930bf85dc000123c0002648000000281ba4d1c484fb8275862235a263a69298580002d7cdbe51d00000000000000400100040020000001003000000200080050001000000400000000028005000c00200240090000000000c00000140010008001000800000400000008000000c00000000050008006000000b001400f00100100000002000000000000030010000007c0030000003001400500040050004005001c00300000010010021000400a00100120030000003000400040020010002002c000000800300080020004000000000000040000018001000400000080000024003003c00000100030000000005800000000000004002000800f000400100000050000000007401700200010010000000800600000050030001002c001000c00000400080028000000400000000100040001001c0000004000001c0010010015000000500040060000000004000d0010005002000000000010060001000c00200200000004003000000100000010004005001000000100040010004003c002000c00c000400500040100028006000000300000010018009000801a0000012000400400080060000002001400e000c003002c000004800a00080000000001000400800000000000004001400000080080004002006c00000180000008004002003a00280080004001001000100180090068008001c0020010001000000000680000008000000400000000000000001000c000001c004000c0000020000000c003000c00b001400100000000034001000400700400000020022004000d006000000440050004006000c002001c000009c00600180100020002000000000080190000008000000a0000002002800000100000000001002400700000080000000001c00a002400b00000030010003000400c000c00300a40060004007000c00000040030014000000000600040120004010002400000140010000001000000300080190034000004c002000c013002000000640020028004001801200040020010006001400600040020004000001c003005c012002c0020034002001c0120000003003c004002800100000090008004000c0090018002004800000640000008000001c00000100020000000000400300100010008006003c0310098005000400f0008006000402a001c008000c0010010000001c0050000028002c0000008004000400e000800000080030004000000000a001c004001c0
  | 41 => 0xcba1b180000d0897c24da7d00e0676c0001c99810400000027d200000006aa29b1498400042dd7b54f1a4e0647251e8a5190203a8000431a9519460e0e0002485afaa282a4e800000023d16f612ee11b00000468000000000025ec7c40001878000000000000000001214411284a00000000000000b311ba00000000424830a86c00000d10000a9c127c5cb266053184a282811681ea911b87980000002f4a00008fe00000001022190667ae123ed8db40c49f0eb4c82c437680000002278b6dd208000090a55eaf99a679ea488e1ed2a7e4000059679893d10f40bd80009960000b8527d900009eb3fe44c231852b4239035414a0cb882303149621b4c3cb0c226b52c864131da03d250205b4c67e934d5946dca9d98208dca0946b0a968c06602e01863870f1c96902b231da308ac1aa4c0001315115000025485644b4d62c00012250002d5cc15267b0df4c7400023ca53b1edaa8189328c300e8b7185dc3a69defa5880006c26f560000d5e19909ce0ea86839f1946c9ac1f9293500003c000007e7abc17daa2a63378e73aa1ed44437a61cb6b0000bbaf09ac18c000aeac4910000000a2b61b60120000355126e6c8000000000007be06fba13aa2253e074c4352dfa2a32ec6c2f111992f01e4aa72bad06e0000b646aa3645800000020c419b89503250000ae85f3d89520bf35a954a0d1aea818724ee0680478130192eb951562b2f8bd661a86fa94c2db4743800056391700000f689d80c082b780000000ac01f987704aae7170001c2432218a60001dc041e1144332d7d60000f220000201a2c40004d200000d320aa844856217eec80429000007c800024b91bd0de00000000bea0e38f54127e9d20001308014ad2c00000f239085085e5800083580007253056ad429f449b127874982ce4f9800073e800005b1e04000125f364083ac108ce50001eb000f022e0001d1d0000b744539d868858ae012491602e6945ab421dc80a6000083f80001c381d698c97b26d089937f2485cbcc0000000078a430942088680000000670000159a5d28c543370000324423f92b00001faa1a800000007db80006720000800235216657a6a40db80000172e60f254c000000000024ce17309ac45067480e854a81619dac42c01e2a06180416615080000000c138c60a0e26c4a91a93f00000005d3c700162810c400219e4a387f60eb1d9c92287f43110160903a8fe6bd9505a685b864cf8000a2666a20000000000264b58a80001afe1fb8309c6420b23fa00000000000000000000000000000001104000000095629b4000000044f8000000044e57d544f000000000000009971de033c232a1d162daafe1ddd000000000012f229028d752215baa0281840000ca26c385d94b913fa2c10c92a3919fab632c940000e5e674824f0002b989b2295da5f1a78b
  | 42 => 0x86574ac9fdf0000000210a69c1780f906ec0000a23800007486dc37e00000002152153a18a84d800000000000001fdc0ee8a842d4cd005bc80000000000713835656c297a2a0ac1a82c00007ce00007e18000309800057026b358f2d7c83914be20f800054d84aeb44692c96851947f5530e2b69e7a1aa052cabb2b4c8528b1a6ce8000afc02006e218082188000000000000000640001e1600002805ed8000a01806000000001b9a8c4000125d67f94420b1aa4a9aa92273bf988402000007d987501db80000002ec00000000491000031200002b98000711800001b9af00001f480a085c400019b200023e95c02c0400009ee00000000000a200000000000203000000000002d3a1b6c0000001b0a0000000000000000029b3000302600026a6a2f80c444fc000a56400057b0bafbe1009698f91e66f9e04e6a68000b26141e7cda168000000000000006ea009cbe21fb13cc805fbdda49f84280000fe00003a38000bee00000e480001414000000000079c8000000221e905156c000101b36220168da93a61c5a60251d8176c2205b64c1f06c9cfa93c8d06e563c3200863b0dd87e28000000000084198220002cf094ce5be078268c17e4000b259e9a00019584da22e60002fe61ac1ab66d2253800018e64e685883cf00007c2996c32f1d38aac800000017e61da97dcaf4ab6c000254a000000000000000000b654ec1be800018506f500000002252b3589a05019a7261811f04b68000b928cb67cf1b5a5b48e641d89d1154e94ae62792a867e0000bae0000a0d565f1801f008602e4e1c4aa6a8c0a9407cb0000be7ee004e5051fa46a714b7c176a664a9711159484365800000010ac78a289686e4000be76c3800000000000aa600009e14c9000092e973a0001f750001b0400000006c4cd92bdb29ae972b04a6ee2ffe8cd691b0000ec200027a859fadc8b498e5400019f44d8000000028e80000000110eb1c0000b508b888a0344a92aae6c0001f500004d7a3ec7159e10bbc006fa7ac36a6a28bdc0002da00001dce828d6e61736f546b81fd24b2506c00027f0428c0000002f406029cd297180000000a48754400050e0000000233a9148000398816300004e4614a61ea7f952a00004b23a4a82d00005e2a3dc000455a85c00007b40000000000000052eceb287d00004aa80007ab408a86619407f5da5a00008122a70c6a8e82a6c20111ca000095697e412d000233386982d2b22a52849d98a225f61f65aa81667d285565a69588964abe6840142a54d6cfe2a58b149b199061d905ac8de443d82883186a2237c2e7a5fc73823342149f529330000790031e7e686ee777cb372fe9972b54800023b08d2a7c94ce85a91b49fd059f9138000657b0600f19de30000d2228b957610fc3846a09db27d1160c000126400001a418199c63fd8
  | 43 => 0x2d803b61f80145d342427c000000261a59a8000000277a0e012ba87240000109e5400002060002e5a37e800000026ac2af02f90000bce0000c8fa350faf3442eae79a242a3cb84a917a896c75600001f680006d99e4c5349cb60ad5e9416b8ce0a0a5ef4aaf884e000051200000000000012000000000018c84ad800000000000000000000208ab3693f00002bcb0000000a54e9160621d92a6fcc0f8cb21b8a7cca9e00000000001036938800000000006d50000ba100001cb000013a9f12000000039740000000ee424902e48e9ad98000000095e00000002118a2b0000000000035d886000018c0000098f8851ddb00006d474d00000001978000160e0066f78a9f834a0de88b02df0000000292e1b586e433894d455785d200000004a04000524972420adb365540000224000000022f0bb500006f91cd0ac60ae8000284c7f214b600b409914bc68024080006958769220037c3f79fac0030000387a98c00009697895c34000000064900004e08a24c02000053e86427452fe79f725dea040000000073f000000000004520001fd4243b0405b01ef201d89660000a014762a26000260c3412d36003a1710000000792054000005820002124000000088880000002e8a3aaa04a00007a64a12fa000016bc00027dd486029c4e30000c1180006550b3c0000000857011c0002426834000000000007f1000060c80006af80009fb2668804914f36780008aa2fce7aa8000604400053703da000296600010299ef913273d8d8294fd3380000364954052253914b31600708c30a5f649169d56d58000aa60fd24a9c28c0000000c1c0cbd41f8df114c000038d2a8c4060b20b8fa19a4031da56b0000000026e2316546e1ac93fc0000000083a3da0000000000108000000000002996aea9afa00020fa362800000017ac8f90f0647fc00000028ce00004a60001ef7000000000028ae00000001a580006eba718000000090caf2a09540000001bf449acd1e9e8164043da26c3da915c9602b900acc2f77ce6e82bd69cc03732e388318dac72120bdb8a83321a10efa69116b6c1103d48d6141682d11274f7ee3c64a93285f410860b42a41a464122940ad047b46f2001d023a687ae264ac2442321922302e9114538c7ba1baaa6604e97fe2c992e60e917843a2450374b83fb2e500e665a92d12351b381db09fcb6f03d64b2800080b28004e5c000ad7afafabc57e0a085f4f949913c05ea14c6781110000054c8a1e40645421a1051ebc900029e43fb173c7a35d5f473a57c393e33697c0000666083648b41de0000000928a3e85f0af3a94f03e82800f100a195fc7611cc49842487694a07d00009d51fb010269b8ba05b51ba60821e8f88c6fd869c2c08a23e9448451e4ab81806822e4b8209fa4985a8aa27c262928000191a80daabaa558d697970000
  | 44 => 0x533300009c2f0c168405f80000000b62a494000165400023720018d24620800034b80004180a7c0b298fc000000000002fea73c000993000031146c8a2a00002770000ad200002a508260001bba0002d147f38b3ac169ea89abb01c12e9cbc8bbb01e00025539170d0a00000000002cd800017801e08000584ebc000028426670000000000069f800035900000000000becaa0234a11900001b76189a9e00000b30436a3ea76e845ca4ad22ea2d189862c00002b5198a5d21fde00011fd0308370000000082100005041cc83e48fe842d455c6fd4f16000000011f5e890001706751a07235958b2bf909d100000009579b46886eb60175e2d46d4030e0000f479220fe43b28eb881b000044494fe0cccc4c096917a0000000000000000009201a48000c298000a7a8776321169e3061c54000231c04500004719bc60001b557069ee80d600000002ec2000238e576264600011130002da68cc9e92a8789da00005c7750db6c4b7000080fc0006c62181bb6012a8eaa70c08293568cb80004359952826a7a6825400087e502ec1f931e1e713307051c9e6ca1310bd9922b8328fb84c298621ab116a48408c802217047f667700002c2000015f23310eb4b43523aa640000000000099cd7601c50c4a88b03cc06c800012f005c00000007350dec84badaa55129835d492ac20d00002d9b011006de14a5d965e7514ffa4e8ab3a000222a00018fe7ef80008559dd68d12dc20000000ba5afca00000004682645b0da0d415780872cd30a8b1b2c9053aa926c0a8000374148a60fc0000001f82aa156ac8ae97f2a15c000043a7dba35931aa341be28d780007c420a621aaf023ba89460002e283ca8bcc708800046888640001fa67a42e2e9c3c0001edaef8b51ac9a0000a36000000001280004711bc24c1077a7b3a395544800000005010000000596286c4c89bc8a1d045e126215e45884b4ba61c6855c91cc00000000ddad30000007a3b4800000030812a680002a425d425fee18153c0a4a1a0e46a60833a6e6d2eb000000088f830c000000044e5242be06c5c68440003800c633f69f548792bd6aa5855800280000c8155c6a5000033228146338000975800077191ba0000fdcbc7217aa39617fb8c8e3a00027035e5224e9faa8261d06d385740cfb9c9c000b5dc0000000000540000000021e000021c08708bad5f908617b5000068c63cc0000b8c9fb8e96b28800057480000000000000099a0a6800000011474cb20c02f4160a925a37eb97000024708720002e666afc000b6eadd85a327fb8d9000000028590000f699682929b3b106648594784431d6e2c015161de2f86aa20e805d92ef6ab10cb09af2ee4274e023017464665704a800013a4ba4dcee244a6ec000046a073a21c3fc000007a2ad8c25800026e06ed00022a43b45452b1584af1e4
  | 45 => 0x4c000000000000022583f003c09a61a9e8750a620000ce358f905c8409ce4aa6aba45f881b44d3abb402183001a8113118f800010728ec29800009d380147232070ba2d00ab6e6be82699fe029a196608615ee0fc9f028181aea423880214742ba90d00009740e14b673082a8120ac000016a3136cc28831b3e2c4ec7e4f08ecbc2e430290200174088000351a98026926de00000001f30d9c0000c7aba669b600003f4248ac6aab98706000000028b000000000002400c580af02ea31f12d6967151a8cc27948730f5582cc72e3ba111690400006540000543297f11d003400016de19706f463ba9020002a585aa17be478c0000000000000000000014f98be0d910000000a7140446dc000000021cd09aad2e00009d40000000000000012fa6c210523b519564864409c4000019560000c12882041175d0fca626a3d6000144e877a514ae09fb3891882f00000002db9106869000032a000007e12969a222340002a8200018306e5064c0a390e89fa09fa6701b5e1582236000236233c967438b0c800000c669f16382bf51180528800072147468a889c1c1ba8dda53ecb6aa92b382440ea000018006b42ed0b0b000052c9825000200c00000d50000ab61bdc0007ee000081e802ab8590ef49e9b1e2b899fc0000cf698e046e000000000000b91fe854a95d9220a1b40000000000a1e80006e38c5eb1b8d1a0000000b4a0000959000031c162e1ef30520000018057a879000000067c16a000026a04bcd630013981092c85908f9988e8ff800011c09d20055c2a00000000000335027a9ad5ee817b0001ac4a9200001bb00004ec89d896e30b20000000b0180000000000a5780000001d78000000000000004a6023d69392934d4257a96ece7479e147a1d5adb20000000bfbcc00000299a98919201838f782370986b05000059e8000bdc0cd4a428000340ef3459f000006b10a6468d75a000208000016061f2239058d0000000243c74c63c44148fd670155340000000b82a83f385cfa60000000000045589f27eb51500000001134a248bec81a8a0ec23a4180002393a70107a1656b3e53f0000be380002f9842626d80008f8296fa2429061198dc4b712872a902e929ff1d8823389e40001ff8b509f73352819ec089a84000112049fc000000066c0000000000000000016480000000b5d29080001b876f40e4a00024822a805540000000000256880967f833fae8e9d517c04d01246acaa3f60000000246930614b85bc6788eb0c0187d81e89feaae21da4b1185e4b55ae46adb8f201aed2303c92d6a7d38000033137e47587722645e8b7e3ca124be99145c09f7e663208600ad7ab8fe0b0ebe1539260d29646359df6a08e39a42747e4b4d27d8880acfdc0f9202a33137649c800046e000062e1b0d018a7ccada831aafda26f7bbdd7286a9b2
  | 46 => 0xb2c000032e455a75284e20002bfc77520069a41968000169c000105e39e152009e1027710a834498e89e85345788b813f812c03b26c900d893084d827fd3342b4a0ea63420f2a56ac00a1e1f8471492f1a1483868b40480736a19f78f9480c2880000000000000000000024b40d6da5437bd23b5c298fa0001380b7011f11a560f845e2e78665a5e08bf9b9c644ad1315eaaf235392918da21869cd2c9e0f811c820cc000421143d007a73600014b8000193000000001e7993c0901816b0b98649851e6a9d31cea1adc000858b0539e300533cd00001b040000000000000000002880007e8000018a870f5d766523368f74290938e0000b966312394a07c0001a700006129e7400f4000000000035f0d4c6259e7e00000003d9c0002e4a58e89c0f7600000000f380001aba6a80000c0c00000000000e322ea808e426178cabe0e97beb5f5c2f8a6cc0000e6e000000034ea3260508000237a5b91cd0000000000000000001a2f0940000000898000000021ecb6fa5c42c0a1cb2c18f3e00021b7037903809280006799b640001a7c63a280e0000a581bcaf16b008000a9f2bba8a150ca00030be00000002a01b4529ba75626fd3b3000025c000138a0002e2441a1c8a75e94da0000000000306605288acb5a01681161603b811c4cbfb956e9e3a3f45b4222fab48000000031b0000000000211c46480000001fba000042000007180f9adbd0001c7c7f687ca378a8ca2362dee6ad2506634b0373781b2a06f03dc1ee000046c1a2602b008227a448a3e7818523e80003ce9e7c9ee86cd8652f773d0da0433b06c9af3ab10b028d369f2000023a1e8e029a84000002cfb1680008930e124fca39c0002ff88770ee6000283c7f915c17361edc5c3287e034400000005a800590640a668bc2a1ac7aaf300000001e4424c13931851d0c959a48c168c5df5baacf47cd4940b249d426c997d44a6a31036300000001eacac00f88186400049c2eefc0a1eea000182e2878152000144314980005730954000000000000007b9000028f22de35a000000000008c8c00000002aea0e92549d71c209bf266c000000006620ae553915a000280891a05557f60cfc0002ba34824dc6447b04f1b640001c3400006681aa000299c35126ba462800017149d00c1995a30d00fa66d1cec9c28ea84f430861a4e9f731c8482905a0960d655965e69ba21e30aa84638f6e1372b2e92f83fc43f9c08c2799ba00017360000bb200002c0a334000000284882400f0819800037500000000b1e084a08e5789f080001bf29dd84460000000613ad1228e0000bfacd6600000b4567a6f8bd3a9b8ab2a33c00000004c0301ac0611544532f2c2c4a9bd10e82887969fc69fb59c22d6800000025b12c4519a7b56aae0000000c1a400032ecf04000213a00000be5f200000000eccc0
  | 47 => 0x44207e0000506a7885365fa80006ab097ec11da2887fa772686998654a149a0002f7b0001b7322100002799c27445d0a861d25d200000003af00009b800000000d9854b800014b44ee3d1049d5892a00c1403dd84c1f9413a04841a184ad81edfc20710e5a5e88698ba72680000300c3e6d5fec0f0e4300029a8af6800035027ce88180a8bc180000000ef2360145387692c48410000c03d64132570580ff93e07629490b64063194f94242fb9b6a000060c5410000774a9cc2e7249e86cc1830000400000137c2bc2c500000000bef068c98f0000b6d9ce861612384c3c000a282ef46710b2941885ca64d88c61b08eb900008067c12c07033c42c4dd0eae000111c80b9aa613fa79032dce38b7a8ac2589949e9c95a46b6780005844000000140a00028e3481e5bd000021c99a903768bede27ae23ee18b8000469285aad5265e2b75364b482d962c610ae14f00005c788a600023bc000000000005c68f7918c5c6000029d00d677840000000ef8615ac0c0001cffa380000542447b7b307be1c9ad227818000a8b1d6636500009d08000000000000006304ba800075911389318000000000090b81fe0000000ac522681a140002df955868d00006b2981c00000000002be20002925721d0f2000217322c9040b7999ea5b80000571150a56f00dc1f8a9dd08d94e682712740a25ca2bc61054000143c1d6291200028df781c0000000ec00e82d829898104b7a26963f199acbc3a7fa18cd5b40f4a1dda6f9f14221982a3d810d2824de186aaa1bcae70e4474a04536f02fe02d02bbd09816a48ad1bbe0fa9e2e7fc83724899432864a7468ec9e3a36f1b023b056ba135000000006f88824000689c000000061f6ea90020002d1851c13ec00008760000000000000063e2aa2000150e5d26ddc899aea43bf2af6ab42e9e0000000aeb17ee4ef90702ff86f9c2d15130000cd8757800026ca8a6ac3ab3c3db1e80abf123215d9f98636131c45ec0009e5877e11002300002c7c83a24da1ce8f5352d132d0ed9726a156ec995c839a00018bea2087282cd9c602d04a5aab3283086b20420002f925330b104bf8b2446600aaaeb9a1b3e00000b6a21c81841bfe0240d8f0000000a5d02329901828ac5a8f800007118c4831dc2700b62a38d849c4103e590ae1e4cfc0000e70cfd05fc00036916ae000072a0000000028e71c000135c0000000788000000000000000a7eaf12eca64280001b2d5780001f647be8252912aa6896d800068600000001b4e0000000000136c47a85960000584728220510da6d099393e40000000000000088e9bfc37585b28f6237a9cea4922ed80003a1e7640158828a5240006590f6400028890a4a01c52c49c614f800000004d6adea47800003b00000000986139c7558000165d5f782e800000000000000000000000000000
  | 48 => 0xa7d6584000040452a80006f9ab99000165a00004903bc255a000158298a21d05068e6893410ecae680000001b3254791b680820ec9ffd8de52584e6b52849e26a2762a3086979ed97921ae1d4e0001e56948127b77700009812a36b280000a23000022501e6000066200000002728748b1d836600000008ad8000beb800062509df2121d7e000000099500000f20000b0fa7660651dae339a1ea0ba2495867084c1bdac1e3d39ca69ff9c7d15fa88d0aa961c6de8b16b23230a275ca7200017c485c0368b0d00004a8000000000000001f3409609888d7289c143074a048d6b868eaeb480b5fe2668000077d19dc14f63809f9d3c7ab6a8708970352253a27a4610000496adae75324545f3870200011cd8398000000000000017a9a011df011d84dec0590dc387e021000101c0670000c1917f800000000000000000000063d0000aebe7d47ae8000314800000000500002f6e0b527ac00029a0b692c262368ac800027a2ba823fca0f87946d2dae80c854b00f08000280a59aa5f51bb0002e300f7c000000000000e807c04f95a8000000055595a21af51e86588000621800034620642589b37154ea206cd04aa70f000039980006a886340000ff88f0a2f60002e4859a087e9b383c435480007f5863b000000062ea8667cdc000000000004204ac1652c5844a077c3b500000890e7c9d78000c01529cbab17270002a56ae784448489217039098a04d000052f4df47c726f65f49e4200029c47002e421d128b26971a62303893e6391bbc3051dbd7ed20fc83ba8d349992561ad54562cb0620000258ab18a9de29e05460000000afea12a0e293b893c8000034cf1e00001ec0002316434c9e26e36ed2a7bc88a4ff8fae5d9800063a80005394000a0659d8000000087b467a0000ffc3cbc00000011ef42a8e824ef0eee99f190468c90963749fee60e2930b1900003ee9680007ddcc0000fd006080008b4a2105bd1f9024d085f2d705c2a452969501179800015fb4adec66000000000016f01ec9b449c4a48ebcd80002e281c672b905a433868849f58725814274033b03a886585c642015c70c06eb898c28ba9bd30b1fe16a693984a1267a932877c8b85492d1a8c522ae97c53dc511850a000082a672a1f0881c00000000006c700000000f1a653ae722cb80005244000000005100000005de8b5200029371fa0ace3bb13e117caf97a860000967a1821b3ca1ab9028b8516000074ea82a1a914d07c90fc45b3177600025e28b60c3800ed146b888000000000077926e67da1f58026a29e82c8dae00000009489e1d07420f6382a682523efea00019b0b1a309987a67c418b25425bfa84670600007d781caa651f314296c2fa8fa9720000000310c0000002cee4b30000470af747b6000043f124c234186e000117493485ce8
  | 49 => 0x39593cc0aa13b71b780001edcd32000291e00024de3cc1486b7b00940000000c080000101a5aa485413c851aeda486800013c1faa848022254caa102dca9467b40c5c000000059e0000c248a646a1800099c000000000006382922322972ab0f1f600002f9470ee232adcad9918e547d40aa3be230800008117394a5069e72695bf4dc20527a0800013eaee8047800000009b4811a63a5b0a8ed7801f4b56618adb8e86d000030240000000b1830b80002afe0000cac5a580001cec1cc2998000a1a845030925c2a7c00006b6143a00025e63cb4000bd1800000007843a2000042d80000fcd06e77e15ae50fe88b08412b52580f8a0000e280001af4000000006a000000000000000000000000000017aabb10df6000007b6e28e94abe93d227226476e61b2e76fa4b668f00000001c320000000000000043fc3f5800a7860002ea29d40a3ec2b9fb006005b769281d454cd5e455f944413d29577338000000000000000000000c65000093aa8512ae00020040000000000033e73fa1785b3933a2871fd00002cb872e17c60000de41940000ab200000161d9618d700a4b38000000120c41e58669e121ef0000000ad5aff64280000aada24034f885aad12d5a78d9c62241000000005ec0002f9e0000000550062d2cc93ea41d16e30001dee07f16d800000006ed00003078140a31ae58214000076e68d814fc0009198518a2682c8bf795ca6248b199f58b4a3e563b8000000075890ea9c015382de8798018ea867de09e00260a075e80f12aae21676178b56ab0a730282a6fe55c000073096883f50c3e16e11e147cacea9fca1d64e2089ab476b1e28602b62db238438d800000006f01d786e94e8256c4320462a6be93d7d888a4b64997c859ac12233115876891b218f093881d9c4a36881708afaebb0000000aac27f7148000041093aa5d01ff470a212c0cec5aa2d2269402ca03d35690d85cd000000000007e38a7a9032db09bca34800011ec64329db9e48000000298e7a59a600001b0c69986815e91b5c415aa0c18c80002050fbc000183a0001f30000202600008320000000000184900000000000000000000038d400000016e20000000000000000000000002bf41bf85b41a69402461800038880000001c1c2525560000057ca36d8449a2912a74288005d1862f21a0b0cafb1a5e4f021f85e7099c6990faa323aae03df61ebac91eb6b072e5099eb00d0db2a926bb9c3a0cf11dc0102298745d2480c202500e3053a3af6a7686580006e422ac8a68dc25f31526252ad1e109db3d4ba000000004ec100aff22ff000035402c206b8000000052b5b750e23c985cf68704da6460000507400098da8f100012e0435ce766b38000b1229d63c2000078799480000021000000076500009449311af816bead986400000000000247e00000000000
  | 50 => 0x4c061e1ab2c9b4825379895683e71e2aa2600f490892a2186e03e0fb24b01d36b2895a9de2b5c9450000099f53842fa1ff1beb202a1d942ead9a73d02e28b30b281951a90b8b05d07c8284b8e5a70d5b700000001e5e93e8b0811e60daac118067aca0e94bf0f4842700008d58e2a21185de42f00610000e8a0002877add02420001d180000c9e6530e8c8710000000000024180000000cc20002b0c31ac07e0001a74a09ca4a512adfc39d703013cab804960000ad5c000b74a0f4000059a0001f3a69d9e955c422c66ae05ab89f8000b3e00002efade400000008c881257b2067c3680b1c6099c5aabba91804cd96054899be9bc0ab84cc8e4e6758ee01b600004800ece7af9a0e0d3873d0002c4e7f9a140bc315ce2d7576e00012c639c4aba8a31e860001afea6b00009c581ba00000f70002534914000000026751452a070000d7253080009b5888eb5f8fe2518c0002bb000000007ce35d01509272e203142bca58accc6000000076d8309000132000000000000000b8400000001b009ec920a0002ecc0002193000160800010e449a00000000c2c01500001f80cc0ae38000000000078f2f1200025a8000040e0b0c494269f0109cf1c8e13f0a50063223ba26d75895521fc35b82dc0002aa983ac00097f8c4632aae6ea561c7a2b6c0008bc936e4b79abcb2a20dc898ae603520468951800059c223cbbe800000004fd66102a2bc9975019cad7601aa76e65180001058000b87050eab58000960823804e307c680169286f93956a5a96a86d051ca1820be23aad5059105ee45c9d3c6352038afb83ee77e83a298380005bb961a82200009e91b58c2c09fe8f34000247800033b9cac6e58000a94185a8cfad645691ee05fb22d675c23f272208169e00a46198ef2e24b23287ed5de684e00007ad12be03f99e83a640000001d160cb99d0a220bca73c2bf221e274a2160aaea354000302800087c8ede00010cc767cba8c2006be00000000001f2e000193a000000000024a54508c6894b2d4e1ea00007b18032000000078c074b00000006829bf70001a8c0000000b292fba96b89de000027c00006377c980000002eea0b30000275a1b20000000a5c2c281c40000b392c303898666b1d03b8982a15446f11cb7dd158607e8296666a26e11dde2c5d71a300b98ec897228444d49e460001e0a00027204fa0ca08c78000b38a05d7a12c4c2f680003e820180e6171230d80ee3d89e1fbf211a8a7e98a0976041a510031f313800068880000001b6e2d08e0672a8774bd31f4db7665c04f7a6dc55491b53d2800000000000001c2c000295c57a000078c8c040000000753c10600003825329d476fd800000012bb0000fd80000000973000004ba4d80000e3004412c0000000000015f68430f9a0001ce2000000096c00000ff40000000ef600028aa
  | 51 => 0x2000000000012b80000000c300d1408e632160de5707cf80924b21f968ac27da3d99222abd12d0519801d20886aa5da2880438139677a1384285116c75a00005a3a6725cfa7525dc9ea98e28cf827d24766a486d200019f204a03a647400000002aa89daa1515116b8a31a6cf2a300bd49fe492696a461a58880005e3a5b260081b6a839efe6eb08a85ce09b02158972606a50c145657e5c50dfe6c3d6d62d9ed78748a116ad0ab264138a0c23284223ead666675250888981a21ba26c0996e47a0f289cc29a9288954800062d879a2d8a4a800026f44d680000001d07bf694220000000bf3000000000005b2000000003508e91f228d02edc198000084d000000018150001d6c1092c54c2114f60e56e081181c36a0a152cc1c80000000000c2c4000b70400005683b91680bf4131112400012e17d68000580076f12d97b42e8a34648d9ba3b63461e00021c63ea000086304f6197dd2c2ed1d2fb1c00007f00bb09c780005a09ddab56236b9ba8000929851a69422a0860e5bf4970ec4863ac824fda13e159948208a29c1ad2a0791b1239210c6cfa00021bab58ab844e627b794000781dc629ca7e1df20001d30a9ea184000060b00021e20000127089800010300000001d7c409ad1004f416229fedf2000241c879d7a171da4045178000266000016b6d2a6f680003c087f2a49e3c65f6860aa2e954861b1be037b852a06409ec2531e583eb403e4241f8c74c8d1c9092e36000228a0001c50194800021e8000a2c1aff0000000798126d0001b105fd9ae2129241a0000144000244876ee0784cf2ec126e878889915542cf695566a9bc44fd290404b1e6c7a61b922d7adda8e894e8a3d800061309580002e0e4726ccc0002f64a6955c605f40008e780004c980005ee21480000000000000000000000be0e5ca98acfca18a17ea9d04c66f799a457d149c22781b002ede6672d1dc4000165d8de030b03027b452dd744a2764644cd82022e1a3420ad279c99d8cbe76a0cce80380000002708ad491da10415b600015e60b14000a0b2a38000000015a11762e2201078d0cd0b7d9cdcb0b40005d311de769a9a45f790f82fe14600e7e0240000000884a9fb00000005ad1d8c4a7a1085b6cd5cae506043faa2848c91c7e305a01a89680005a60af42be6d06777a6b89ef0000bf180003811a401671f7c44c305c0000e4100023dc00029508b205100002b1a6499f3b395e816077220488bac10ba31d5a33360bc965925248dc73e47010bebfb08540002894a59e0d16fc026e7bc00009ca1a4c30c26d4000000001e6efeb39950681006656b7a650a7215a09dfa14e000000020780009be96e833e9cf21eb83e2c25dac8946941251f00002948000bda0000867651c25084f8615029057e8e0c0001efcbec04fb68aa09861d8c7e81d0a54ad18100391
  | 52 => 0x17280000e9b562a6d85070000103c4886851f508979d76ac48000aea0b2a2eb0a928958f504dea4ea0000eba0001cba000170e00000006d280000002740aad1546ae540006da0bd2992a5a600014d35361d3e3359af8000000074b427a000305e0002e5e00000004a75ef19ec1ac6b75800000006827fa20c8394a58c21b1a089ca854819d2f4217d98caae896d57e70000965111a6d01a9892e20f00cd2218608106b9a6a6560552b8c495e058c1e29860e581741536e44a192ef23a1558c000286b44b08f21e76a1a7b4d4ac7eb9a2c0001e9384a00000002b9725b800000012794b0a2fc16c2132a491af9481081a270c00053b80000000000000000000005ed507d3ac0000000000000039c91b9000000022fa5da0000000a4e6b92471edf448a10170b9c0007601756584ad849fa50a28b393c40002d3e6e919881762139a76800000000005e1823b39c000016897fc1d4aa7f0a500008c180000000000b31800039b0000a750b22000000027005116b926a4000279ebe022aa13fc00007083a80001eaebf0907c1cf216c00010d50002dd4a09447cc1e9c7000000003a9262e0000000a0da9a60000b68a7999807ca800009b2bdc1a34000b2a8000a17800000000e00000000bc680000000000000000013207390000000be68e0800000000000000aec0000b83307b7a44000000277c1a1ead4000000058fda8e67d800003b00000000000000000000000000000000c010000b580000c290310a63c56a4cb80001cc279a2462c84188aa6d29c19de0000980b08a094a8c81780002b4e00da3d0000243e9a383f64672fac23d00009236b309f9081cad8858e17500005fd0b9058816c400003bb16e90b85aca662000000001c244c340800036c94ba46f8000000000000008300000000a979b743f3210da08000000000000002c4000004413fcaf6a76d00003d000005e2c25e90280003dc8000000246c984882048482b890e8a092f60000076881f76e0000000210e282000000000000000000b12818e00000007494000968a8e27e2238c3414000ae598b4a1580000990e4d535ae4c000014ebc01a15af62ff000024e314e4f8c00005f081f00000000888af20ae435e1a020000000a60400000000000000000576800046780008dba5ac45985c113e69d85778000000000053200002bdad7a000101dbb780001048db6164ad16000089258780007e9144c76080009ad0000aefd0c4b7f8ad6000252a00022498ed248f5932f9640c011620616361939fb604808576b493ae9cb2a5a00021e81808000187634c0001b1a6b697f00c580000001944bb0c00020909470319d36000166e000036e10a076d00000005610000000161892b8000196000000000000002fcf00028d100014649ba0000000037f67915dc9880266be2a9ee0bc9942788a72
  | 53 => 0xcd0002f7c0000c983a70d30a2d8000000090c49f8c9647d098c00029f69f980000002884c240aac6fea3d2c000000a3a85509dd00005409ea08eae2240002d0cbc2800045e40104a1869900000000000000bd20000228889800025c10000d56bac92e21848000c2da4d6271000010f0af263700e50002ee200023acc0d9e1a394087434a83970002ae24749e122d1999416f800085b9088a2ad81398d29e1bf40e7a107a03ab23b067953a73831e6aaa64c99ce54427264591c1207d1a243618f0a452843e3f217bc00008210001c780001b19000095a1798256497833696e80001ec0ea2c1da5fabd8a02f71b0000a16ccff2579d0617a2d02a1245f40bf29ed0000bc654f03a903200008a38c1000000000000000000217c68b9814000000000222c00000f7e41280003422f329329c6a000225079dacb4b4017228d9ebb81c32f1e7d580000002248000000062a800062764dcaaacb4e8560e1a000215a00000000000b38aa100000000fb23930ee2b32994a2570964423001c23f29784f38c8c47f062165d00004da9d547d322bcbada97e7571e1c6c514412bb873236680008801708890c0001c69976ad688e6a85aa804caa6bea32dfec88a00005de0000ac20000a6124904ea21874a280007a720b600007a0000036f54700000e52a0528a000039a800064fa7115992ed6574d8a5815000026509c20f600003d71c920491d957330f700000000a7a2e86be91b3057aabde000298a0002d6cb5f4000186034827740000001e640002cae00000008586e7021000008278000acd88230000000000024c0000000bfa0000a37000048a8eb60002dbb2b4291d40b26da64e0000000000010d05440000e7eb3da48062700d426a9a58405abbc45f976c76a8000a3d1d2a86894c48d401fd087af5089da71a000066aa14291cb149cc61c2eeba2ac05135d51b7e000246e7dc0000000000007c19b88540cb430a1b7c00015f827c2869a1d9d972810dc078080000001dfe6a020d2c09d00ea740000affaf240f2ee9412316943e18d6009db01200005a447ac000000000086800007b101ee6e694684160b8e20f0000402237645ba8e6b501bd644f4daa748000059585da49814b96b58c7338910720919a3817e88660000000a6f1b840002fa6a50a83d0000000719ae7c00000003b18000908126a93e070464a109e1060ec90ce1234b6e0000b0c8d2c297968a0002c2a00000b0815800034f20cd1c240008f228af000193409205d6b7e1be963316dab2e8f5a08303283ca1076b598284966cbb8746800000010ee5380a7d00023b622baf8c5e294720ef08dbb35123e4e1affc00020a41508d264f2a3c9a8f0268341998e1218aa243ead880001d4092a9c3e89116289160ad8929034005848e0660a5443eb2fcb33283f000002148ec0000aab000000
  | 54 => 0xf616e468180000002dde46200001b881ea000000050600000002fa820320de469a24a00007926bb2a6000000000002a122642706711000007228fc99d270e3fde0e0000000000011e2b10893c000000052d4000028000015481324d500000001c02313d1f8b9d0c4200000001c71032000275800021db0000000be8875a585953e74416d747d80002fdaf9b115cc5b3f080007b78ea67fd80000000000327211e0000ff434e00000000000000204c8e6000089ab02e0001c80000000000000720001a1300010820000000a550445c280000000000026b40002358f4650387fe4d2977400021fa6f480fca21a7025722044000294ea97253a37ca2b88a2171533840000002a9e66b9a6b0000000a73968663080000002d860001f0600000000000322377a4c800000000001dd8000040a0000ebba480000a9c800071625f2541e6e40001c5cbaf22351eb072122aa8a472428a94a5d046000236014d281c64b000061184ca00000004879ea525d800000000000000b60c13574200006a2000000000019ec6f707d6a7f266422e988c8f00dba2bf27df000000041429050c70644315800000000001890a22000254b15b02628d945c0ba69e23000000069ea96c3d2d4df00000009f7800035ea5ce27d8b5408aa01e87480001b28e2e2364e020700a10000038d2d12590955aa641c7974e000000000021421dcc00005623542dc1f7a8c80cf9ab195b88da48f84b36c188db1aa06cb15be00023180000000000000000004380001318bc880000000000a5b9ae6ae4dca459d9f728e1a3cf89ec000133c0005146a8a00009db0000f0e1c816f100a0dce0001462b4280005020000000000050f977c065963aa049ce60002292a3bc000ada01465d79662429e9d150c29c200000006ac929b0002c44bff400040e9c1e149000072faa4e8fc0571439ab5c5beacbc4954c1a93900009048000000000060b29525c5aac0be2c000bf5a1b500012501c8c0001a240009de1d503ad680c07d84cc94280000d69fbc96198f65bb09ea3ef9be503f469453c00000000ce8b270ba4be09ffe0001c2641a62e40dc4a3abb990d90000000000000058e000060ac0007c322b296f2cde0000ecf00000005e2056eb438fa91d3800000014988beb0140000000529800000004ce00024e900019000002f3e4be0c20000023c766a06891aa3376d81fccab719da1dde1ca00000000002aa77b5a0d81fb88e250992246e3130c02f52d21e38000017800052304424c50a6c4bd09f886440387d000001d5057091815800b35c9c4090bbc2676e7a1686f903de9dc26c21f46a25c17cc0e1a6db3004d19079d9e3dfdee274485fd2450be4476626193c6f60b5780000a5e2390002d8537a88384de1ee6492857372c800040f0c820000fee2ee800000000000df90b487b800000003
  | 55 => 0x824a87170100000003d14f7c319084a3698000833d2bc22d14f20f90000793ad247ff0000adf8ab2a56df1ea07a5109aed0b214108bc03293d600698ac00000005cc00007ccc6cc1978c6c3901e882230000064a5166a704299792efc4f8a7c285d1cd6000000061f8c6e3101dbc00014a4a430fb49310b800000000a622c16483800025c0000134205a0000aaa185800069aa2c47c58d6278925ea525187d38f98801aead4c604aa942d651820880cea000134400017209589868446304c493910e29711e094daa7899684729aad56419282d89ac91fe4d1800015c987ca0de048758400045f04cd8052a0aab92d94128097853440e275829e3754800000014145ea183e0a7800000011b70002a340000000000151400012f073f0a031f780005938000ba2074200000000000000a162a08000000000000007641d02a28856f66d80000000000406501467300000002ca657c18f20bb800095169381a40cc34a404e03b6a49a08588f00000000a3e9e0c0002e62a8a67ae63c0a4c1d719eec2ea3ba60609440a2821a0ab09e8725a9000001ea610940002422e6c53880004c08000181c00019d85c8a6e80000002da2000074000012f60000000ab78c9051200000002c723e64d3450d9aa47af4668abc0000684a76840793ba48b2fed0000000a582aa61268000b73299821c000068800002b70827a08a93e09c9d0800024fe93f037430ba8f2000202a0002c0e0001cf872c000000018ae5b2805a2f08a880001e8caf187362f780001270000000000017f0000772a0a5000267e7948a2a78382da8c7c2e5a648a343e117327a880004041c6e0000000669a94a30a458c000157cad906e0b522ece1c907d2000000033480000a800bc00023ae29d9b3c00012a6720872b0000000882add0c1a80000b80da822d9684000079600000007d08000bd7237400000003e50ab40000000bf1000071c800050300006fe0ba66aea99f0002e64a4d92d40a997b06fbabc28590000610800099e0c3c6640000000000000029751e90d6c00000003c50a3014087c6bd7abb612e000000000e30000e3c6ec8000b3801be196ea9000012403d08004c230ffe119000000020e2859551893027fd7178000bacd5f39d6a40000000000000000000000000b93b68b7217600011aa68329ec683c9d900022903ec22e8134870a0002f7a4f608ee0000000000000084f089c59800002d625ee3f392820002be41364bae0002ffa00b2a8e0002220000254839200000000000000000000000000000000000025400000000000000440152b51fdebc00000006b31151000000015d00000000000000000000000006ac245a4b2ee52b63a606454857b603e6480002470bb80cf47029a3637210c07bb5e6e49a6126b0e87808a001d829389bc6079b7800000002b1800010aa7325
  | 56 => 0x90c0000519dc067a9dfb27218f5609cc0001130a060002f9cad0177e000000000021750001eca5d89790000180c35c12d800027883840ca44a3227400000000000fa70000f980001d040ca9a16326961054540005971af213540003f9a00a0d8142e00000006c1adcab338362ab380009a1ac78a9094a041eea2a81b918b02300000002b22a5214f4404a46240a00000bc27e0413c00000020a8000032cadc12a43d7b068b5516b011e8d7e5949d1c2958b1500910f06c48000638800005ca7ca37c2faa4268000873d92278e13720002bd09f88d1694127c00532bbe3264ce47bda1ce00011bf77c523c0000000bd605770002b7823daf2800021446228000000247c2b2ae6838ceb868c68000000000026f8000b090000adf21600910000ba995a61ca40005928e586c880006908db0524ef100000000c2edc9190e0000000155a00030343bd2574a75e0500001c9882480000002524b73800000023a83304000c0b0000a0b8acc0002aa0b9d8000ae81bcc7bb15d6000000044b800017f8000000000000000000002e6a00000001035bca61c00000000000a068000ba45824629098441215fd5cdd312a3b80000002f52000000050b01362be8a160002c88b5b9004a3780005670f367fc0270000148e00016f80ef90068dc00001d800001f712678a18000bdc8d423ce22420e20aa42bfa72e6ab884444ea7f64818e90a1505b911f8c02135dbce05b8000a52c42ec0caabc8338628bed9c2e2de1e9e27ca86e7fe9adc0eb971a5a409ae3431b3f2f213c8692284100007f021b90474659fa801b24f600000201c95beca322230231203c3ab2cd2382424e4c585006478af80000000a0085793adc5a600000000000c2ab34017e98a871d76c2fb41b69dd032c8ddc9770a8a19740f801325e799986480001782154587a7db000005217700001566000000000000000002f080001c37b3213da5708c97a950c5abe60000bdfa4e837f1a4952f07c04e406b4b3a13b407cc6b600003262ba946a245a062808b00e1ae40004bb07c270587d09e2afdca4ecf18addafe23299eee25e85eb7491e1b2a62fd22f826445641910000000000027820f40000bcf04d314ec48e90b03047a280007b027b8ac08de8291000065c000048a68f92259de53d31ef5853c9280b59280a70d45c2ce46fc0fea05c73795e00afa36693b00daa7c5d1e8839136a9ba867044a1d8196857562a22ec8f394c0a5302b0a0c84cb9ada8f0acd16463af95ac8baa66ea36400000021639c1238894baa3000024a0bbb83908dec51e1c88000537acb2a5a0f527c60f8232b8000a63400025a997e3a1056d580896b145ab2069b135893c2b32816ce18a8b9f1a0000d8e77a818a0211b620bd11d410c90d000011ac0c90e200f782ec51f98c6220881030e901a701067847eaeaa1c7e
  | 57 => 0x2de00026085e79c743e8a6ca56caf7d1af20b8000063698b0532a4409a2b86a90e42525f43d61428034a8d25853002ae76f384521d8e0a9106a4d980000001c0c2b1000080a0000a8a00001a991ae000076600000000098126000096880c8b6472a244497a000055d00000000de60000be82c2859e00000000000000449823400020348d28000000244630c800083318900002eec000000000000464a5400088cc000000039ebc11fa200000003e58000000000040d0e983a180006c5959291000004e78000817882e0000000000000000c1d44000000000000001a2a9df2fc000000005386ed97ae0698000000060862f18400002b9f6e08000000269e92462c2a45e402112000000000000000000000227246cc00000016040000000000000091c9d00000188800030aa6e7a34e4790000ba0000070e1f280429e70846a1852f10cbf1826456000022c897c000bf0000090d997a553256e27b4000ba409749eaa172980171cabaa74486b86562daa9aa3e3892a48706388a58b84343983676606cea1f09829c90b4c0000ebfc1d1f760ed214b6438000732a3388f8800000017e8943835cb4f29c665b99a28c3a560448aa3a1d0e88a1da0fa466f1beaa0ad73b4ae6a4468fa30091d1a695752e02b8d2bd442857fa2020e164d3108a9661672116a540304499675206c0b2b0430ad62ba618ea3d466a22f4c18a3e7779ef1433dd6c641de6227f7402228c97ca9571e5069a033078269a247b88bb0001f32c2b2ae82898000c194118000000000000002cf800000000002d6db2f5bd8d58b47000000014000000000703800097b0727203ae7e21f0b76a9740002d54000a6ca9a344225320000000230044a2f02fbebb20c7892bcc1c3b4085e75aa3049f1cd20a5cdac296d0ed6b17a68407d580e81fcdb8000110a252000054c165077b03390000b98636a8da55a835e0001d5d9908000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa3e85dcd640400147b0bb9ac808003275cc73590100045f43ea6b2020008bd87d4d6404001c3ca7a9ac80800ead20572590100051f428e4b202000a3d851c9640400153d06392c808002a760c72590100045f438a4b2020008bd87149640400153d06292c808002a760c52590100045f43864b2020008bd870c9640400147d0a192c8080028f61432590100051f428e0b202000a3d851c1640400b56b02382c8080022fa1c50590100045ec38a0b202003ab681141640400156b02282c8080162fa1f20590100045ec3e40b202000a3e85c81640400147b0b902c808002a7a0f20590100054ec1e40b202003ab681081640400156b02102c8080030f15376550100061e2a2ecaa020038bc8759154040314790ab22a8080022fe117298c100145e422e531820038bf8759243040071790eb228608002a720d6450c100145f420e6b1020008bd841cd620400717909bb2840800e3d205765081001e3a38acaa1020038bc875914204007968e2b2284080031d59771508100065ab26e2a1020038dd8798f320400517909bb264080022fe11764c8100145e422ec99020238f7815d932040071e902bb264080523ee01764c8100045ec36e89902000c3e65dd1320400117d0eb2264080022f21d644c8100061fbaac89902000c3c755913204007968e2b22640800f351c6634c81001c6e43ac699020038ec87589320400196cc9b8a64080032d593714c8100065d326e09902000cb964dc132040011f30c38264080032e990704c8100065cb20e09902000cda631c132040019b2c6382640803b3a988704c8100045fc22e730020028bc845ce60040078ece2b2c800800f2d9c564900100047bc32e32002000c75655c6400400196ac8b8c800805e1f61b755001027e1f326eaa00200087e8759540040630f90eb2a80080030fdd564500100061e3aac8a002000c5e65dcd40040018bacbb9a800804f2799373500100064eb26e6a002000c5e651cd40040018baca39a800803f2799073500100064eb20e6a002003cb671592300400196ac8b8c600800a2f213764c01008c5ec36e89802000c3e65dd1300400117d0eb2260080162f21d644c0100061fbaac89802000c3c75591300400796ce2b2060080032d591710c01001c7cc3cc01802003cb671592200400196ac8b8c40080032de1376440100065a426ec8802000cb776dd1100400196eec3a22008002ada1d64440100055a43ac88802000e37755911004001c68eab22200800f2ddc1644401001f59b82c88802000cd776dcd1004001d2ac9b9a200800335dd873440100074ab20e68802000ce776dc91004001d4ac9b92200800339dd87244010006d23a0e48802000ea5641c91004001b88e6392200800e3da1e604401000679bb4a08802000eb16494110040019e6eca822008003ac5915044010
  | 1 => 0x8c5b9a80880e237a1873501100062fb28e6a022000c5c651cd404400193ec839a808803f27190735011000666310e6a02200f8de87d8d40440711b90fb1a808800317dd763501100062e3aec6a0220138de8718d40440671b90e31a808800317dd463501100062e3a8c6a022000c6f75d8940440018d8ebb12808800333dcf62501100066639ec4a022000ce462dc540440073690ea0a808800aad21941501101b69a3aa82a022000d9473505404400176100a0a80880cf359c463cc1101d65d3b6c99822039cba761933044001c70ca326608800396d9763cc1100a574412c79822033cda7618f30440299d0c4b9660880cb3a9db62cc1101be753b0c59822000eab6418b3044001d50c83166088003b218c62cc110005d8c24e39822000b718590730440013e70ea0e608800a2fa13764c1100045ec26ec98220018ee82dd930440011db05bb260880022fe11764c1100145e422ec98220008ef825d930440031d904bb260880e62fa1b744c1100061e32ee89822000cac62dd1304400117d0fb2260880ea2f21f644c1100061fbaec89822000c3c75d91304400193ee9b1a6088003271d3634c1101c66a38ec69822000c9f7418d3044001938e831a60880032bdd3624c110006563a6c49822000ce462dc530440675b10c98060880d2e6211300c11022764312601822000e386519030440299d0c5398608811bb218a730c11019de940ce618220038f987d8c3044001d36c9b186088003a6193630c11019d6cc3ec61822038cd987d8c30440011f70eb18608803aba209630c1100056d430c61822000cda7618c304401d1f10cb90608803abaa1b620c11000765b1ec41822000eab641883044001d50c83106088003b2d8c620c11000764318c41822000ada86cc8304401dd90c59906088002b6219320c1101a5cc42264182200eec8624c830440677a1029906088002dc616410c1101a7c821a821822000ea862d922044001d50c432440880533a18a738811007674310e71022000ec862d8e20440019b4ec31c4088003b2188638811000d75436c51022000cea76d8a20440016e30b20c40880cf351c463481101967238ec49022000cb464dc520440019a8c7b8a40880eb2e1db64481101ce5c3b0c89022000ea86219120440071f50d39a40880e3361db634811019e6c3b0c69022000ec86218d20440039d0edb9240880cb3a1db6248110005d8c20e29022032de3721c520440016e30b20a40880027c21d41481100147b436e90822000977855d2104407596cedb24208800b2d9d864841101c66b3b6c70822033cd67618e10440659ccedb142088007399d8628411000752320c50822000ec46318a104400717d0faa2c8080030fdd754590100c43f42ee6b20200087d85dcd640400717d0f212c8080030fdd675590100061eba8eab202000
  | 2 => 0x8631891000747b20c63122000e8c6418c62440edd9700318c488003b25c063189103b765880c63122076ec81018c62440310fd0bbb284880021f61776509100046f41eeca1220008dd83dd942440010ff0abb284880621f21576509100045fc22eca1220008df835d942440011b906bb284880023be0976509100047bc0aeca1220018be87d9142440051dd0fb12848800a2fa1376cc9100045ec26ed99220008de83ddb324400117f08bb6648800a2f21176cc91000c6ec38c799220028be84dd9324400117b09bb2648800a2fa12764c9100045ec24ec99220008bf845d9324400517908bb2648800237e0d764c9100047bc0aec99220008fb805d93244005179083b2648800e3d204764c9100747c400ec99220008be86dd13244001878cbba264880bb2b18b744c9100045f43ec899220008bc87d91324400187eebb2264880030f1d7644c9101d65a38ec899220018de87d8d324400193ee9b1a6488003271d3634c9101c66a38ec69922000c9f7418d3244001938e831a64880cf351c4634c91000657ba6c49922000cac74d8932440659c8e3b1264880023da1b714c9100065bb26e29922000cb464dc532440019aec7b8a64880033518f714c91011e72316e299220038fa86dc13244001976c9b8264880032e193704c9100066c31ee09922014ce862dc13244001976c838264880032e190704c9100066db18e09922000cd8631c132440019d6c4382648803b3a188704c9103ae9a322eb20a2003c77605d64144007ae6c0bac82880025de1f65905100071a326cb20a2000975871964144001c68c832c828800aada1b64905100065b3b6c920a2000d3575d9241440015690caa48288003555d763905100074a326c720a2000d557518e4144001d28c831c8288003595d7629051000752326c520a2000ce67618a4144001acaea314828800399194629051000752320c520a2000ec46318a41440071ed0d38482881cf8d10765505100065db20e0a0a20039b584dd5414406da6ea9baa82880023d21975505103ae9a2a2eaa0a2000c7476d954144001c68c9b2a82880031d1d8655051003e5a3b6c8a0a2000cd476d8d41440019a8ec31a828800b2d1da4350510006723b6c4a0a2000ce4761894144001cc8ca3128288003a9190625051000762318c4a0a2000ab4865094144005968eca1282880025d61470505101ced9ba0e0a0a2000cd8639c331440019d0c5b82628800336d8c704c51000674310e098a2000cd863dc121440019b0c638242880033ad8870485101ce5b3b483202207487e86dd5404409f878c9baa80880031b18b75501102843f43ecaa02207387c87d95404400187eebb2280880030f1d764501101d65a38ec8a0220338de86dcd40440018becbb9a80880031719773501100064fb26e6a022013c9c64dcd404400199
  | 3 => 0xd21a20008ed82dda43440010ff0abb486880621f2157690d1000477c12ed21a20018ec825da43440051bb0e31c86880621fa177650d100043ec2eeca1a20018ee82dd943440011db05bb286880021fe157650d100c43e42aeca1a20008df835d943440011df04bb286880063b2097650d100146f43ec6a1a20038fa86dc143440018f0cbb8286880033a18b7050d100063c328e0a1a2000cbb641c143440019b6c638286880033a1887050d100145f424e7b1220008bd849cf6244001c5ecbb26c4880029ba1664d891000536c2cc9b122000ace83993624400159b07326c4880029be1564d89100053642ac9b122000acf83593624400159906b26c4880038bd9464d891000716328c9b122000ea5811936244001d1ec9b1ec488003a319363d891000764c06c7b122000aae8498f624400155b0931ec488002abe1163d891000556422c7b122000e8f6418f6244001d18c831ec4880029ba1674d891000536c2ce9b122000ace839d3624400159b073a6c4880cab9a0474d891000572c08e9b122000e2f549536244001c5aa82a6c488002aba1373d891000556c26e7b122000ae581dcf62440655d301b9ec488002aba1273d891000556c24e7b122000a6e85d0f62440014db0ba1ec4880029ba1741d891000536c2e83b122000aaf845c3624400155908b86c488002b3e0d70d89100056641ae1b122000a6e8510362440014db0a206c4880cab9a0440d891000656316e8b1220008be87d91624400187eebb22c4880030f1d764589100045f438c8b122000c3f751916244001878ea322c48800327d9373589100064e326e6b122000ccc62dcd624400193ec839ac48800327190735891000666310e6b1220008de87d8d624400193ee9b1ac488003271d363589100046f438c6b122000c9f7418d6244001938e831ac48800a2fa1f74589100061fbaee8b122000c3f751d16244001878ea3a2c48800327dd373589100064e3a6e6b122000c9f741cd6244001938e839ac4880032bdd37258910006563a6e4b122000ccf73dc96244001998e7b92c4880032d1d371589100066a39ee2b122000cd873dc1624400195cedb20c4880038bd97641891000754b86c831220008ed8799062440014dd0b320c4880029b616641891000557424c83122000ace83990624400159b07320c4880023be1d641891000537c2ac83122000a6c85590624400159f06b20c488002b320d641891000557430c83122000cae761906244001c5eca320c4880038b194641891000752c08c83122000ea970190624400199cedb18c488003a3d93631891000746326c63122000ec980d8c6244001d92e1b18c4880023b61e631891000557424c63122000aad8498c624400159d07318c4880023be1d631891000557c22c63122000aac8458c624400159d0c318c488003339d
  | 4 => 0x3440015b5003a6c6880e2b660074d8d100070faa4a9b1a2000e1d54153634400153d09b96c688002a761372d8d100056ac0ee5b1a2038ad980dcb634400153d09396c688002a761272d8d100056d400e5b1a2038ad9801cb63440011bd0e216c6880023761c42d8d100052f42885b1a2000a5d8510b63440014bd0ba0ec6880029761741d8d100052f42881b1a2000a5d8510363440715ad02206c6880e237a1f20d8d100046ec3e41b1a2000a9e84c83634400153b09906c6880030f9d76498d100061ebaec931a2000cae72d92634400187cea324c6880030f5d46498d1000657390c931a2000c9e74d8e634400193ae9b1cc688003339cb6398d1000657b22e531a2000cac645ca634400199ec6b94c6880030f9d67498d100061f3aae931a2000c3d755d2634400195ce9394c6880032b5d27298d10006573a2e531a2000cad745ca634400117d0fb22c6880030fdd76458d100061e3aec8b1a2000cac72d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000cac72191634400195ec9b92c6880032b1937258d100061fbaee8b1a2000c3f751d16344001878ea3a2c68800327dd37358d100064e3a6e6b1a2000caf74dc96344001958e9b92c68800333dcf7258d1000657ba0e4b1a2000cac741c9634400199ee6392c688003391cb7158d1000674396e0b1a20008df8758c634400153f08b18c688002a72116318d1000567c12c631a2000acc8258c634400153d09398c688002a76127318d1000567414e631a2000acd829cc63440014bd0ba18c688002976174318d100045fc22e431a20028bc845c8634400153d08190c688002a76103218d100064f3b6c831a2000e1f65d9063440011bb0f320c68800297a166418d100052ec2cc831a2000ace82990634400159b05320c68800237e1d6418d100052fc2ac831a2000a5c85590634400159f04b20c688002b32096418d100064f3b0c831a2000e1f651906344001c38ca320c688003a56046418d100054f424c431a2000a9d8498863440014bd0b3a0c688002976167418d1019d6b408e831a2000ad5811d06344001c3ea92a0c688003875505418d100054fc22e431a2000a9c845c863440015af02b90c688002b6e017218d100054f420e431a2000a9d841c863440675ad02390c688002b56047218d100056d400e431a2033ad9801c863440675ad03a10c688002b56074218d100046f4388431a20008dd8710863440014bd0a210c688002976144218d100052f42e8231a2000a5d85d04634400153f08b80c688002a72117018d100052f4288031a2000a5d8510063440675ad02200c6880ce37a1f2018d100046ec3e4031a2000a9e84c80634400153b09900c688002a7e111018d100054e4222031a201887e85dda43440010fb0bbb4868800237a0f7690d1000c77416e
  | 5 => 0x800e3e61873882100053bc2ac98842000c3d75d53644400156b03aa6c8880021fe1573d91100c43e42ae7b222000a9e83997644400153b0732ec888002aba0a65d911000556c14cbb222000a3e8598b644400147b0b316c888002a7a0e62d91100054ec1cc5b222000c3f759d7644400187aea3aec8880eaada0475d91100055ac08ebb22203aab980dcf644400147f0ab9ec8880028f21573d91100045f43ea7b2220008bd87d4f6444001c3ca7a9ec8880028fa1672d91100051ec2ce5b222000a9e839cb644400153b07396c888002aea0072d91101d55cc00e5b2220008be8714b644400117b0e296c888002a7a0c52d91100054ec18a5b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b222000a3f855c764440014790ab8ec8880022fa1f51d91100045ec3ea3b22203ae3651d476444001c74a1a86c8880022fa1c50d911003c5ec38a1b22203aab681143644407517d0f906c8880022f61f20d91100051f42e41b222000a3d85c83644400153d07906c888002a760f20d91100061e326eab222000c6c72d9564440018becbb9ac8880032719373591100062fb28e6b222000c9c641cd64440018decbb92c8880032b19372591100c43f43eeab222000c3f75dd16444001878ebba2c88800317dd773591100062e3aee6b222000c9f74dcd64440018beea39ac888003171d473591100064fba0e6b2220018ee87dc964440018deebb92c8880031b1d7725911000657ba6e4b222000ccf73dc96444001998e7b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc725911000672396e2b222000c3e76d946444001c6ae3b28c8880022f61e65191100051f42cca3222000a9e83994644400153b07328c888002aba0a651911000556c14ca32220008bf87594644400153f06b28c888002a720d651911000557c12ca3222000aac82594644400187cec328c8880038d5c465191100051f42cc43222000a3d85988644400153d07310c888002a760e62191100046f41eecaa220008dd83dd954440031dd05bb2a8880023b60b76551100061e2a4ecaa220008bf845d954440011bf06bb2a8880023720d765511000477c12ecaa220018ec825d95444001878a83b2a8880622fa1f64551100c51f42ec8aa22000a5e85d0f63440014bb0ba1ec688002a7a1032d8d100054ec2065b1a2000e1f65d9363440014bd0b326c6880029761664d8d1000567414c9b1a2000acd8299363440014bf0ab26c6880029721564d8d1000567c12c9b1a2000acc825936344001c3eca326c6880038719464d8d100074ac08c9b1a2000a9e8498b634400153b09316c688003a6d9170d8d100074c322e1b1a2038ad980dd363440014bd0a3a6c6880029761474d8d101c56b408e9b1a2000ad5811d36
  | 6 => 0xc43e42ae9b0a40008bf845cf614800517908b9ec2900523ee0173d85200053b42e83b0a40008f787584614800156908b08c290002b520d61185200061f3aec920a40038f8865c241480310fd0a3b282900021f614765052001c5e43ac8a0a4026a3c85591414800153906b22829000ead20564505200064f3a6c718a4000c9e7418e31480071f10cb8462900033618d708c5200045fc22ec18a40028bc845d831480079c8c2b90629000e3e219700c5200066c31ae018a40018bf8759240480354790ab248090002a720d64901201d55a40ac92024000c3c75d91404800193ec839a809003f27190735012000c6fc3ac71824013a9c8458e30480715a902b1c6090003271d3634c1200046f438c69824000c9c7418d30480031bb0f31860901e6b6602630c1200046fc3ac6182400fa9c8458c30480675a902b1860901e2b6e01630c12001c5f43ea8b262000c3f75d5164c400756d03aa2c9880621fa1773593100043ec2ee6b2620188bd84dd954c4001878a9bb2a98800e3da0776553101fe3b28eecaa62000c3c545d954c40014bd0ba1cc78800e3761c4398f1001c6f43e86b1e2000a5e85d0d63c400717f0eb24878800e2f21d6450b1001c6ec3cc799620008bf845d932c400517908bb2658800e3d205764cb100064e3a4c69962003cd47198d32c40071b90eb1a6588003271d1634cb1000d66412c69962003cd47158d32c40019b4c7b8265880fb4dd5375507103be9a2a2eaa0e2003ab48650941c40012eb0a38283880030f1d5645031007e4f320e6a062000c9d641cd40c407da68eaa0a8188003651cd415031019c6fc3ac798620388de8798d30c4001938e931a6188003271d1634c31001e7238ac49062000c3d75d5364840010ff0ab9ec9080621f21573d92100c43f43eeab242000c3c75dd16484001878a93b2a9080022fe1176552100061e2a0ecaa420188bc8759154840314790ab22a9080030fdd77458e100061fba8e8b1c2000c3c751d16384001976e8382c7080032e1d07058e100046fc3ac631c201887e85dda43840010fb0bbb487080021fe157650e100c43e42aeca1c20038f9861c143840010ff0abb285080621f2157650a1000c5f43ec8a14203acb471d91428400117f08bb6650800a2f21176cca1000c6ec38c799420028be849d9328400117b093b265080022fe11764ca100145e422ec99420018de87d8d328400359d05b1a65080cf351c4634ca1001c7cc30e09942026a3c8559141840711bf0eb1e63080ce37a1e634c6100d51e42ac920420038be87d914084001878ebb22810800327d90735021007e4e320e6a0420148fb865cb308402753908b1c610803ea7211630c2101ddcc4226018420008fb8758c308407773108b186108002b661b320c2100056dc3264184203bb98844c830840677a102990610
  | 7 => 0x9e87dd1300c00193eedba2601800327dd8744c0300068fba8e89806000d1c751d1300c027938e930260180032eddb744c0300065dbb0e89806000d38751d1300c08bb30e9b9a601800276a1f314c0300c43f42ee6b24400087d85dcd64880071ed023b2a9100023d60476552200c45e43ac8aa44018a3c85591548800187ceb3a6c71000a2fe1d74d8e200061f3aae9b1c4000c3d755d3638800196ce938ec7100032d5d271d8e200065b3a2e3b1c4000cb5745c76388001974e9386c7100032e5d270d8e200067938ce1b1c4000cf1719c3638808d5b501b1cc710112b6a037358e200046fc3ac631c401887e85dda43880010fb0bbb487100621fa167690e200043ec2ced21c40038f6819da43880011eb033b487100621fa167650e200043ec2ceca1c40008bd849d943880071ed033b287100023d6067650e200047d404eca1c40028be84dcd618800117b09b9ac31003a3ea03735862001e5b30ae830c40008f787584618800196ae8b08c31000e3da06769062001e3b30aeb20c4000c757558641880071f30d38483100621fa1476506200043ec28eca0c40028f487585418800517d09bb663100022f61376cc6200145f424ed98c40008bd849db31880071f30d384631000e3e61a700c6201bc77c32e110c4000cce635c8308800187aebaa6c8900021fe1573d91200c43e42ae7b22400087f855c764480310f90ab8ec8900032719073591200065a320e2b22401887e87dd56448001878ebba2c89000317dd773591200062e3aee6b224000c5f751cd64480018b8ea39ac89000327dd073591200064f2a0e6b224000c9f411cd64480019388039ac8900031ddd771591200063a3aee2b224000cd773dc564480019a8e7b8ac8900031ddd471591200063a3a8e2b224000cb7741c564480019aee638ac890003351cc715912000673b90e2b224000cd873dc16448001878a93b2a8900022fe1176551200046fc1aecaa240008dc835d954480011ef02bb2a89000e3d20576551200061e2a0ecaa240188bc8759154480314790ab22a890002a720d64551201fd5a40ac8aa24000a5e85d0f634800517d0fba2c6900030fdd77458d200061fba8e8b1a4000c3c751d16348001938e9b9ac6900032ddd37158d200065a3a6e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4000cbb74dc16348001970e9b82c6900033cdc77058d200067838ee0b1a40008df8758c634800153908b18c690002b52056318d203c56dc02c631a4079ad9809cc63480014bd0ba18c6900621fa177690d200043ec2eed21a40008de83dda43480071ed03bb486900023d6077690d200043fc2aeca1a401887c855d9434800117f08bb2869000237e0d7650d200047bc0aeca1a40038f4815d943480011f700bb286900021fe1574d85200
  | 8 => 0xfb2c82980030f9d764905300061ebaec920a601887e85dd9414c0010fb0bbb282980022f219748c5300061e32ae918a60008bd87d92314c00187cebb2462980030f5d7648c5300065db24e118a6000cb8649c2314c001976c8b8462980032e191708c53000679b0ae118a60008bf845da214c00517908bb4429800a2fa1376485300045ec26ec90a600087e86dd5404c09f878c9baa80981421fa1f655013027c3e43ecaa026000c3f75d91404c001878ebb22809800317d9773501300062e32ee6a026000c9f64dcd404c027938c9b9a809800317d9473501300062e328e6a026000c9f641cd404c01f938c839a80980038e19464cc13008e4f3b6c91826002c9e76192304c001c3eca324609800387194648c1300072db2ec118260018ee821d9540c0011db043b2a81800e3da0476550300047ac08ecaa060188bc87591540c0314790ab22a81803ea720d64550300046ec30e6aa060008f9861c1540c0f7a70a8382a8181ef6610c7055030004f8c08e0aa0600087f855d9420c0310f90abb284180023de05765083001c7a40aeca10601887e851d9420c0010fb0a3b2841800e3da0476508300047ac08eca1060018bc87591420c0051d90eb128418003331cd625083000674b10e0a1060018dd87d93320c01f33908b86641800276e1970cc8300066dc32e19906000d9b845c3320c001b3108b86641803e67a1f744c8300068fba8e89906000d1c751d1320c0f5b30e03a2641803f271d3644c83007c6e43ac89906000d9474dc5320c001b2ee838a6418003651d0714c830246e8380e29906033cd5861c5320c067ba50038a64180cf74600714c8301c66b300e29906048dd3201c5320c091ba04038a641800366dd3704c830006cc3a6e09906000dd371dc1320c001ba0e3b8264180533661b704c83019c6e43a64b086001ccc724c9610c00796cc2ba0c21800f3998572184300047bc3ac23086000cb574584610c0019cae4b08c21800e3da06769043001e3b30aeb2086000c7575586410c0310fd0a3b282180021f614765043000c77410eca0860008ed821d9410c01f53906b22821811e57a1773504300064eb20e6a0860028f487585410c0019a8e6b0a821800276e01728c43019cea40ae41886033dc4215c8310c0013b700b90621812372c81720c43007cce422e018860009db865c0310c0719b70cb80621800366e11700c430006cc422e018860038f6819da210c0013b706b8442180022fe1176484300145e422ec90860028be841d9210c00117b083b24218003331cd624843000c7a43ac2908600fa9c83592400c08f2b90ab9c801811b72c8172cc0300046ec3cc718060008f98798e300c0f33b30f994601803a76e1d328c03022dcc42265180600edca724ca300c0017a1029946018116e6a12318c030006e8b8c63180600f9
  | 9 => 0x739023025eac3aca1984604b9db87543308c0f93b70ea9e61180030f5d754d91300043fc2ae3b22601887c855c7644c00147d0b316c8980028f61662d91300061fbacebb226000c3d751d7644c00147f0ab9ec8980028f21573d91300045f43ea7b2260008bd87d4f644c001c3ca7a9ec8980028fa1672d91300051ec2ce5b226011a9e839cb644c00153b07396c8980022fa1c52d91300045ec38a5b226000a9e8314b644c00153b06296c8980022fa1c32d913008c5ec3865b226000a3e850cb644c00147b0a196c8980028fe1571d91300051e42ae3b226000a3e851c7644c00147b0a38ec8980022fa1f51d91300045ec3ea3b226000e3651d47644c00117d0e10ec8980022f61c21d91300051f42843b226000a3d85087644c00153d0610ec898002a760c21d91300055d40043b226000ab980087644c00147d0bb86c8980028f61770d91300071d286a1b2260008be87143644c02317b0e286c898002ada0450d91300055ac08a1b2260008be87c83644c00117b0f906c8980028fa1720d91300051ec2e41b226000a9e83c83644c00153b07906c8980030f19375591300c43f43eeab226000c3f75dd1644c001878ebba2c89800317dd773591300062e3aee6b226000c7875dc1644c00187cedb28c8980022f61e65191300051f42cca3226000a9d83994644c00117f0eb28c8980030f9d865191300051f42cc43226000a3d85988644c00153b07310c8980030f15276551300045fc22ecaa260008df835d9544c0011f700bb2a8980030f15076551300c45f43ec8aa26018a3e85d91544c0018f0cbb8286980031e1947050d300065db20e0a1a60008be87d91624c00187eebb22c4980030f1d764589300045f438c8b126000c3f75191624c001878ea322c4980032dd9371589300065a326e2b126000cb7641c5624c001968c838ac4980033918871589300c43f42eeca12600087d85dd9424c00317d0fb2284980022fa1b744c9300061e32ee899260638be87d91324c05d1790fb2264980030fdd7644c9300061e3aec89926000cb764dc5324c001968c9b8a64980032dd90714c9300065a320e29926000ce7621c5324c03b9c8c438a64980032ed93704c9300065c326e09926014ce862dc1324c001976c838264980032e190704c9300043fc2ae9b0a601887c855d3614c0015ab0610ec298002bc60021d85300061f3aec930a6000c3d75d92614c00187cea324c2980030f5d464985300045f43ec8b0a6000c3f75d91614c001878ebb22c2980032b1cb64585300045f438c8b0a6000c3f75191614c001878ea322c2980032b1c8645853000657b26e4b0a6000cac64dc9614c0011ef0eb08c298002b920961185300c43e42ced20a600087f855da414c0310f90abb482980021f21975905302be1e322eb20a600087f87d96414c0010fb
  | 10 => 0x18a800087f855da21500310f90abb442a000237e0d76885400046e41aed10a8000c3c655d2215001f93ce831c42a0003275d063885400c43f42eec90a800087d85dd921500011bd07bb242a00023760f76485400072da86c7282800fc9c7418e50500ffc3ca831ca0a00030fd9774541400d61e32ee8a828018a3c865515050005878ecaa2a0a0002ce201545414023c6f43ec6a8280138dc87d8d505000193ee9b1aa0a004f271d3635414025c6f438c6a82800f8dc8718d505000193ee831aa0a003f271d063541400070eaa0c6a8280188be86dd64050035878cbbac80a000a2f21975901400d61e32aeb2028050a3e86d96405009f87cedb2c80a013f8ed8365901400c61f3b0cb2028013c9e76d8e4050001c38cbb1c80a003f279d863901400070fb28c72028000e1c6518e405000193eea31c80a0003275d4639014007e4f380c7202800fe9a7018e40500051790cb8c80a00024fe1571901400061e32ae32028000c9c635c64050075968c2b8c80a00621fe1d75d93300062f3ace7b266000c5d759cf64cc00147d0bba2c9980030fdd754593300c43f42ee2b26600087d85dc564cc001878a9bb2a9980022f61276553300061e2a2ecaa660188be87d9154cc03147d0bb22a9981fb4e1507055330004f8c08e0aa660018bc8759142cc0310fd0bba2c3980021f61774587300047bc3ac230e6000c3e7559241cc0310fd0bbb283980021f617765073001c5f43ec8a0e6026a3e85d9141cc00517d093b443980022f61276887300d51f42ec92066000c3c7559140cc01f93cc839a819800327590735033001c7b408ecaa460008f5811d9548c0311790eb22a9180628f21564552300062eb2ee6aa4607dd98431c1438c00317d0fb22851804e6721176cca3009c6fc3ac9994601399c845c3328c01d9d4c4382651804e67a1f744ca301764fbb6e8994602ee8e62dd1328c0c793eec3a2651800347dd4744ca300068e3a8e89946063e8e621d1328c0031bd0fb226518006b3a0b644ca3009e4e3a2c89946010acd86dc9328c00359f0cb12651808f35ddb714ca30006ca3a6e29946023ec662dc5328c03b9aeec38a651800365dd0714ca30006ca3a0e2994601dec6621c5328c0719ad0c38a65180e335618714ca30006adbaee09946014eca62dc1328c01d9b6ec3826518003661d0704ca3007765310e09946000dd0711c1328c0711bd0f992c3180e2b520532586300055ac2042b0c6000ad583085618c0015e50010ac31800f2d98574186300047bc3ac230c6000cb574584618c0071ed033b4831800f1d985759063001e6b30ae720c6000c7575586418c0310fd0a3b283180021f614765063025caf42ee6a0c60028f487585418c00796cc2ba463180032d5d1618c63000678b0ce118c6038dc4215c8318c02733908b80631812e57215
  | 11 => 0x50001878cbba264a000637a1f634c9400062fbaec69928000c5c75d8d325000193ee9b1a64a004f271d3634c9400062fba8c69928000c5c7518d325000193ee831a64a003f271d0634c9400063bb2ee29928000c7465dc532500019aec7b8a64a00033518f714c9400063bb28e29928000c74651c532500019aec638a64a00033518c714c9400147d436e09928000c7b65dc132500018f0cbb8264a00033618f704c9400063db28e09928000c78651c132500019b6c638264a00033618c704c9400043fc2ae7b0a801887c855cf615000156b0810ec2a0002bc60021d85400062fb2ce730a8000c5c659ce615007593ec939cc2a000317d9573985400062e32ae730a8000c5e75d8e61500018baebb1cc2a0003179d463985400062eba8c730a8034cd97018e61500010fd0fb2ac2a00031b1cb65585400043f438cab0a8000c6c7219561500018becbb9ac2a00031719773585400062fb28e6b0a8000c5c651cd61500011bd0fb1ac2a000317dd763585400062e3aec6b0a8000ccc72d8d61500011bd0e31ac2a000317dd463585400062e3a8c6b0a8000ccc7218d61500018decbb92c2a00031b197725854000667b1ee4b0a8000ccc63dc961500a187ce8328c2a00023de1d611854000572412c230a80038bc849da51500011bf06bb4a2a00023720d769454027e1f3a6cb28a8000a7581d96515000187ecaba4a2a009b0f19574945400149fc3aa928a8018a3c86552515000187cecaa4a2a0002cde05549454009e4f3a6c728a8000c9d74d8e5150001caea3b1ca2a003f279d063945400064eba0c728a8000e1d5418e5150001caea231ca2a000237a0f76545400046ec1eeca8a8000c3e541d9515001f93ce831aa2a02038795063545400045f436eaa0a8026c3c65dd5415004d878cabaa82a01428fa1b65505400070e32ec6a0a8000e1f6518d4150001c38ca31a82a000327dd463505400064eba8c6a0a800fc9f7118d415001fd2ee231a82a00038d19761505400074a31ec2a0a8000e3765185415001317d0c38282a00024f61470505400061e328e0a0a8000c9c631c141500010ff0abb662a00621f21576cc5400c43e42ced18a80038bc849da31500010ff0abb462a00621f215768c5400043e432eb18a800087f87d9631500010fb0fb2c62a013f0f9d3658c5400061fb2ae918a8000c3c655d231500018bcebb1c62a0003175d7638c54009e4f3a6c718a8000c9d74d8e31500018bcea31c62a0003175d4638c54007e4f3a0c718a8000c9d7418e31500018f6cb38462a00031e196708c5400066db1ce118a8000cd8639c231500071f10cb8462a00031ed95708c5400063c32ae118a8000cd8635c231500310fd0bbb262a00021f617764c5400043fc2aec18a801887c855d83150001878caba062a003f279d0630c5400064eba0c6
  | 12 => 0x237e1d6518d404256dc02ca31a807fa5e8619463501078bcec328c6a01ef87a106518d400070ec20ca31a807be1f4119463500f7cb680328c6a01ef871006518d403df2c200ca31a8000e1f655506350001c38caaa0c6a000297a166218d400052ec2cc431a8000c5f759d4635001f53d093a8c6a0002a76127518d4007d4f420ea31a8000a9d841d4635000159d043a8c6a0002b36087518d4007d4fc2aa831a800fe1f855506350001c3eeaaa0c6a0003871d55418d400054fc0aa831a8000e9b80550635000153900aa0c6a0003a62015418d400052fc2ae431a8000a5c855c8635000153f08b90c6a0002b5e057218d400056a40ae431a8081adb805c863500014bd0a390c6a0002976147218d4007d4f420e431a8000a9d841c8635001f53d09a90c6a0002a76135218d400070eaa6a431a80008de8714863500011bb0e290c6a003ea7a105218d400054ec20a431a8000a5e859c463500014bb0b388c6a0002a76127118d401a56cc04e231a8000a9d841c4635001f53d09a88c6a0002a76135118d404170f2a6a231a800fa9e84144635000153b08288c6a0003875505118d400056d400a231a8000ad98014463500011bd0e108c6a00023761c2118d400052f4284231a8000a5d85084635001f53d08108c6a0002a76102118d400056d4004231a8000ad980084635001f53d09a80c6a0002a76135018d400070eaa6a031a800fa9e84140635000153b08280c6a01ef879505018d400056b408a031a8000ad581140635001f1bd0f900c6a00023761f2018d400052f42e4031a8000a5d85c80635001f53d09900c6a0002a76132018d400062fa9ced29a8000c5f531da53500014bb07b2ca6a00628f2195494d400061f3b2a929a8018a5c85d8e53500311bb0e31ca6a006297a146394d400070eaa0c729a80188de87d8d5350031878eaaa6c4a00621fa1673d89400043ec2ce7b1280018be849cf62500010fd0fb2ac4a00021fa1c65589400062fb2ee6b128000c5c65dcd62500018beca39ac4a00031719473589400046f43ec6b128000c5f75d8d62500018b8ebb1ac4a000237a1c63589400062fba8c6b128000c5c7518d62501039b6e031ac4a00031dd9771589400063a32ee2b128000cd763dc562500019a8c7b8ac4a00031dd9471589400063a328e2b128000cd7631c562500019a8c638ac4a00033918871589400046f41eeca9280008dd83dd952500030fd0fb2aa4a00628f21954549400061e3b2a8a928000e1d5418d52500010ff0abb664a00621f21576cc94000c6ec38c7992801887e85dd932500010fb0bbb264a00621fa16764c9400043ec2cec99280038f6819d932500011eb033b264a00621f214764c9400145e420ec992800087e86dd532500010fd0fb2a64a00021f21f654c94027e1e3a6ca9928000c3f65dd132
  | 13 => 0x476c16ed98c80038f9869c231900010ff0abb263200621f215764c6400043fc2aec18c801887c855d831900010ff0abb443200621f21576886400043fc2aec90c801887c855d9219000187acaba4a12000a2f21173d95400145e422e3b2a8000a5e8398b65500014bb07316caa00028fe1173d954027d1e422e7b2a8000c5d731cf655009f47d09396caa00028f61272d95400052f41ce5b2a8000a5d839cb65500010fd0e196caa00021f61c32d954027d1f42065b2a8000a3d840cb655000147f08b8ecaa013e8f21171d95400051ec20e3b2a8000c75711c765500010fd0e10ecaa00021f61c21d954027d1f42043b2a8000a3d8408765500014bd0610ecaa00029760c21d95400053d40043b2a8000a7980087655009f0fd0f906caa00021f61f20d954027d1f42641b2a8000a3d84c8365500014bd07906caa00029760f20d95400062e32ee6b2a8000c5c651cd655000193ee9b9acaa000327dd073595400066c39ee0b2a8000a3d8498865500014bd07310caa00029760e62195400c51f436caaa28017c3c76d95545000117d0db8aa8a01c30f197715514027c5f430e0aa28050c3c651c1545000136b02382a8a01434edd470551400062ebaea7b1a8000a9d84d4f63500014bd0a196c6a00029761432d8d400054ec2065b1a8083e1e841976350001c3b0832ec6a020f87d0465d8d4041f0e200cbb1a8000e1c6555363500014bd0b316c6a00029761662d8d400062eba8ebb1a8013a9e841d7635000153b083aec6a000297a1772d8d400052ec2ee5b1a8000a9d84dcb63500015ad03b96c6a0002b560772d8d4009d6cc06e5b1a8000a5e859cb63500014bb0b396c6a004ea7a1272d8d400054ec24e5b1a80008de8714b63500011bb0e296c6a004ea7a1052d8d400054ec20a5b1a8000a5e851c763500014bb0a38ec6a0002a761071d8d4009d6cc00e3b1a8013a9e84d47635000153b09a8ec6a000237a1c21d8d400046ec3843b1a8000a5e8508763500014bb0a10ec6a004ea7a1021d8d400054ec2043b1a8000ada8008763500015b30010ec6a004ea7a1050d8d400054ec20a1b1a8000ad68114363500015ab02286c6a004e37a1f20d8d400046ec3e41b1a8000a5e85c8363500014bb0b906c6a004ea7a1320d8d400054ec2641b1a8000c5e75d8e63500018baebb1cc6a00021fa1f6558d400043f438cab1a807ec7b7019563500011bf0eb18c6a000297e156318d400052e42ac631a8018c3c75550635000153b09a98c6a0002a76105318d400070eaa0a631a800087f855c863500310f90ab90c6a00023de057218d4001c7a40ae431a8000a5e850c863500014bb0a190c6a0002a76103218d4043e2f3b6ca31a8000e1f84d94635010dc3909b28c6a021b87d076518d404370e206ca31a80008dd87994635010b4bd0b328c6a0
  | 14 => 0x471591420c4079cce2b16641880335dda534c4310066bbb2a6988620087f855d2600c4310f90aba4c01880a2fa1f74580310061fbaee8b006200c3f751d1600c401878ea3a2c01880e2fa1f54592210061fbaea8b24421887e85dcd64884010fb0bb9ac9108621fa1470592210043ec28e0b2442188bd84dd95488401878a9bb2a9108030f151765522101c5fc3ac921c420087f855d260884310f90aba4c1108022fe1173982210145e422e730442028be87dd1608840187eebba2c1108030fdd474582210061e3a8e8b044200c9f74dcd6088401938e9b9ac1108e33660373582210064fba0e6b044200c9c741cd60884010ff0ab9ec8908621f21573d91210046fc1aecaa242008dc835d954484011f700bb2a8908023e20176551210c45f43ec8aa24218a3e85d91544840517d0fba2c6908030fdd77458d210061fba8e8b1a4200c3c751d1634840196ee9b8ac6908032d1d37158d210065dba6e0b1a4200cb874dc163484019e6e3b82c6908032edd07058d210065c3a0e0b1a4200cdb731c163484019d6e4382c6908033cdc47058d210046fc3ac631a428aad78158c63484015b100b18c6908022fe117018d210145e422e031a420087f855da43484310f90abb486908621fa147690d210043ec28ed21a420087f855d943484310f90abb286908022fe117650d210047bc0aeca1a42008fb805d943484011f100bb286908033318d72cc5210047dc3ac03024200ad883580604840117f08b98c09080a2f21173181210062f29ae7b2c8000c3c545c765900018eca2b8ecb202278e15270d964027e1e3a6eab2c801887e87dd5639000187887baac7200030fd0b7558e400046fc3ac631c801ac3e75d96439002717f0eb1c87200028fe156390e4009ccfc3ac721c8013d9a739c2439002b17f0cb8487200023de057654a4001c7a40aeca9480018be87d954290035878ebb2a852018e2f21d6350a400051fc2ac6a14800c8bd86dc142900010ff0abb665200621f21576cca400043fc2aec994801887c855d932900011ef02bb2652000e3d205764ca400064fbb48699480028f9861c13290001878a9baac3200621fa1f75586400061f426eab0c8000c3d84dd5619000187887baac3200030fd0b75586400061f20eeab0c8000c3c41dd5619000187e81baac3200022fa1f54586400061fbaea8b0c803aab681d51619000193887b9ac3200030fdd643586400061fbaa84b0c8003c76615d461900011ef0eb08c3200031d5d5611864001c7b40ced28c8000c3f545da519000796cc2ba4a3200629d21561946400065aba2c328c8000e3754586519000187acbba2a3200623d21d61546404471a2a2c2a8c801ac3e75d96419000117f0eb2c832006b0f9d565906401cc5fc32e120c801887e85ddb31900010fb0bbb663200063ba0b76cc64000
  | 15 => 0xeb22651898e2f21d644ca310061fbaac89946200c3c75591328c407968e2b2265188032d993714ca310065ab26e299462008f986dc1328c401974c9b8265188032e593704ca310047cc30e09946200cba641c1328c401972c838265188021fe1574982310c43e42ae93046200a7a85102608c4014f30a204c118802aea1320982310055cc26413046200ad983c82608c4014f70aba4c1188029e21574982310056dc1ae93046200a7a851d2608c4014f30a3a4c11880ebca04749823100578c08e93046200e3b54952608c401c72a82a4c1188029ea1743982310053cc2e873046200e994310e608c40157509394c118802ae61272982310056d41ce53046200ad9839ca608c4075e502394c118802bc60472982310053d428853046200a798510a608c4015b506214c118802b660c42982310a47dc3a653046200abb844ca608c40157108994c118802bce05329823101d7840a653046200aba840ca608c40157308194c1188029ea1440582310053cc2880b046203af281101608c40157509902c118802ae61320582310056cc1e40b046200ada839d1608c4015b3073a2c1188029ee1574582310053c42ae8b046200adb835d1608c4014f50a3a2c1188029e614745823101d79408e8b046200af1811d1608c401c76a92a2c1188038e55054582310055dc22e6b046200ab8845cd608c4015d704b9ac118802ba20973582310053d42e86b046200a7985d0d608c4075e503a1ac118802bc60743582310055d424e4b046200ab9849c9608c4015b507392c118802b660e72582310056dc1ae4b046200a7a85109608c4014f30a212c118802b6a0c42582310056cc1884b04620e8f8874c9608c40157708992c118802ae211325823100579c0a64b046203af0814c9608c40157508192c118802ae61032582310076499064b0462008ef825d9544c4031d904bb2a8988023ee0176551310047c402ecaa262188be87d91544c43147d0bb22a89880e2fe1d6490d310045fc22e1b1262028bc845c3624c4019d0c4382c4988062f21d645093111e72316e29926200ceb621c1324c41d9d0c438264988bb271db744c93117746316e89926263c9c761d1324c4c7d18c43a264988063721d644c93100d66412c89926221ace86dc9324c40359d0db12649888f351db714c93111f62316e29926203cd4761c5324c401aaeea38a6498803651d0714c9310ef62310e29926214cd876dc1324c429d90c5b82649883b361d8704c931006cc3a0e0992620eec8621c1324c401ba0e2382649880eb521932cc53111f623126598a62008fb87580604c4015d104b00c098802b660f201813101c5f43ea8b206200c3f75d51640c4310fd0a382c8188021f61470590310c45ec26ecaa06200c3c54dd9540c401878a8bb2a81880e3d205765083101c5e43ac8a106203cb
  | 16 => 0x4582410145f424e1b2a8200c7a505c365504af47d0bba2caa08031794f735954146e3bbaee2b2a828ce3454dc56550401878a8382caa08621fe1d75d8d410061e21aebb1a8200c3f425d763504011bf0eb18c6a08021fe157018d410c43e42ae031a8226c3e75596435044117b0fb1c86a08028f6176390d411cc5e432e121a820087f855c362504310f90ab86c4a08062f21170d89410046fc1ae1b1282008dc835c362504051ed0db8aa4a09872d1c7655094100c5e43acaa128226c3c75595425040355904b2a84a08ff2d1c5655094131c5f43ec6a128200a3d85d8d425040736d0fb8a84a08e62fa1b70509410c43f42ced992820087d859db325040717d0dba664a080e6da0774cc9410c43f42cec992820087d859d932504011f5013b264a08023e602764c9410064e3b48699282028f686dc5325040187ecbba2a2a08023ee1d60181410063ab8cea3028200c3c545d460504310ff0eba8c0a08031d5c575181410061fc22ea3028200c3c845d4605040187886ba8c0a08030fd0975181410061f20aea3028200c3c415d4605040187e80ba8c0a08022f61f54181410061ebaea83028202cb571d50605040187aeb218c0a08030f5d542181411cd5a40a8430282018ee821d954cc4011db043b2a9988622f21d64553310c51e42ac8aa662028be84dc162cc40117b09b82c5988021fe157650b310c43e42aeca16621887e851d942cc4010fb0a3b285988062f21d6450b310147643ac4a1662018dd87d9332cc4073a903bb2659880365dd0714cb31006ca3a0e29966200dd071dc132cc5179b6ec3826598803661d0704cb31006e8388e09966200c9d641cd41cc40399ce4994c1988e2b520532983310047dc3ac030662038be87d51648c40187eebaa2c9188621fa1470592310043ec28e0b246200c3f759d5648c40187aea3aac9188028fa1773592310051ec2ee6b2462008be87d4d648c40117b0fa9ac9188038794f53592310051f428e4b246200a3d851c9648c44553d06392c918802a760c72592310045f438a4b2462008bd87149648c40153d06292c918802a760c52592311145f43864b2462008bd870c9648c40147d0a192c9188028f61432592310051fc2ae0b246200a3c855c1648c40153f06b82c9188028fa1470592310051ec28e0b246203ab6811c1648c44556b02382c9188022fa1c50592310045ec38a0b246203ab681141648c40156b02282c9188022fa1f20592310045ec3e40b246200a3e85c81648c40147b0b902c918802a7a0f20592310054ec1e40b246203ab681081648c40156b02102c9188030f15376552310061e2a2ecaa462038bc87591548c4314790ab22a9188038710d6550e310065ab26e2a1c62028be84dc1628c40117b09b82c51880e2f21d6450a310045ec36e89946200c3e65dd1328c45d17d0
  | 17 => 0x26492cf276d84604c801d66c9b08c099003ac19361181320047cc3cc23026400aba84984604c80157309308c09922ebca0661181320047dc3ac23026400abb84584604c80157108b08c09923ab6e0d611813248d79430c23026490cf276184604c801d66c8308c099003ac190611813224768c18c23026448ed373184604c801da486308c099003b450c611813200771990c23026448ed232184604c891da064308c099123b80c861181320053dc2ae83026400a78855d0604c91f5b706ba0c0990029ea1474181320053cc28e83026400ada831d0604c81d5b3063a0c09903abaa08741813200574c10e83026400af2811d0604c8015e3023a0c0990038ed5254181320056d41ca83026400ad983950604c801c72a82a0c0990029ea1743181320053cc2e863026400e994310c604c80157708b88c099002ae21171181324756dc1ae23026400aeb825c4604c80157508388c099002ae61071181320756cc18e23026400ae9821c4604c8014f50ba08c0990029e61741181320056d41e823026400ad983d04604c81d5d505a08c099002ba60b41181322bd1f426e6b2c8200a3d84dcd65904018bee739acb2080e9d20572596412bd1f420e4b2c8200a3d841c965904014bd06392cb208029760c72596410043f43864b2c820087d870c965904af47d08192cb208028f610325964101d3b40ce0b2c8200a3f845c165904014bf06b82cb208029720d70596412bd1f420e0b2c8200a3d841c165904074ed02382cb208a29d60470596410043f43e40b2c820087d87c8165904af47d09902cb208028f61320596410052f41e40b2c8200a5d83c8165904074ed02102cb208029d60420596412fe9bbaee2aa482008bd861c154904dd87cca382a9208026d60470552410c61e3aaa931c820087f855ca63904310f90ab94c7208021fe157098e410c43e42ae131c8200a5f83596539043147f0caa4a7208030f5d95494e410c61f3aaa8b14821887e851cd62904010fb0a39ac5208621fa177058a410043ec2ee0b1482008de83dc162904011bb07b82c52080e3d2057654a4101c3e43acaa948203c7471595529043147f0caa2a5208030fdd95454a411fe9a38aa8a948200c7565dc552904071bb0f31e65208621f217764ca410043fc2aec994821887c855d932904071e902bb265208023ee01764ca410047c402ec994820087d86dd532904010fd0eb2a65208021f21d654ca412be1e3a2ca9948203c7471595329040187ccbba265208030f597744ca410064fba4c69948203cd47198d32904071b90eb1a652080f351c5634ca410063b32ee29948200c7565dc532904018f4cbb8265208031e597704ca410063d328e09948200c79651c132904019b4c638265208033658c704ca410043fc2ae7304821887c855ce60904dd1790eaa2c1208630f9d55
  | 18 => 0xc8014ed0ba18c2990029d61743185320074aa188630a6400ad683d00614c8015ab07a00c29900e3da1c40185320047ac388030a6400a7685100614c8014eb0a200c2990029ea1440d81320053cc2881b026400af281103604c8015e302206c0990038ed9764d81324b74cb9ec9b026400a7a85993604c8014f30b326c099002bca0664d813200578c0cc9b026400a7b85593604c8014f10ab26c099002bce0564d81320057840ac9b026400e3b65193604c801c70ca326c099253a660c64d81324a74cb98c9b026400e986490f604c8295b10ca1ec099003acd9361d813200758326c3b026492ed173d87604c8015750930ec099002ae61261d81320055dc22c3b026400ab884587604c801d66c830ec099003ac19061d813248768c18c3b026490ed173187604c8014f50bba6c0990029e61774d81320a56cc1ee9b026400a7a859d3604c8014f30b3a6c099002bca0674d813200578c0ce9b026400ada831d3604c8295b3063a6c0990038ed5254d81320071caa0a9b026400a7a85d0f604c8014f30ba1ec099002aea1371d81320055cc26e3b026414ad983dc7604c8015d305b8ec099002aea1271d81320055cc24e3b026414ad9831c7604c8014f50ba0ec0990029e61741d81320061f3aec93026400c3d75d92604c80187cea324c0990030f5d464981320065bb24e33026400cb4649c6604c80196ec8b8cc0990032d19171981320065b3a6c33026400cb574d86604c80196ce830cc0990032d5d061981320065d3a6c13026400cb974d82604c8019e4e3b04c0990033c5c760981321745e436e8b0264008be87d91604c80187eebb22c0990030f1d764581320045f438c8b026400c3f75191604c801878ea322c09925f27dcc64581320065bb26e2b026400cb464dc5604c80196ec838ac0990032d19071581320047b43ec2b026400cb774d85604c801968e9b0ac0990023da1c61581320065bba0c2b026400cb474185604c8999aee630ac0990023ee1d60181320055dc22c03026400ab884580604c8015e702b00c099002bc20560181320043fc2ae8302641887c855d0604c80117f08b88c09900a2f21171181320053d428803026400a7985100604c8015b306200c099002bca04401813200578c08803026496cba76d90604c801c76cbb20c0990023e61e64181320053d42cc83026400a7985990604c92757509320c099002bca06641813200578c0cc830264008fb87590604c8014f70ab20c0990029e215641813247d6dc1ac83026400af381590604c8015e102b20c099256aea1864181324a65d3b0c83026400e3b65190604c801c70ca320c0991eba660c64181323d74db98c8302647ae9a32190604c8f5d3064320c09924eb6a1a43181320072c32c863026400e986490c604c81d5b10ca18c0990039619543181320074c322863
  | 19 => 0x22f61e65191325151f42cca3226400ab681994644c80156b03328c899002aea0265191320055cc04ca32264008bf87594644c80156f02b28c899002ad20565191320055dc02ca3226400ab880594644c94387cec328c899283875cc651913201c7b40eecaa264008f581dd9544c8011f501bb2a8990023e60376551320061e2a4ecaa264008bf845d9544c8011ef02bb2a89900e3d20576551320047dc02ecaa264008f8805d9544c801878a83b2a8990622fa1f64551320c51f42ec8aa26400e1c64d96434c801c38c832c8699002a72195490d3200ce6412e321a6413c9c649c2434c80339d0538486990038710f6550d3217656396c8a1a64018dc865d5434c8013b100baa869927f171db6550d320070e326caa1a649ec5c76195434c805938edba286990bb631cb7450d321764e3b6c8a1a640087f855d3614c8310f90aba6c2990029da1741d85320053ac2e83b0a64028be849c3614c80117b09386c2990038dd9764d85320053b42cc9b0a6400a7585993614c8015e501326c299002bc60264d85320053bc2ac9b0a6400a7485593614c8015e700b26c299002bc20164d85320071bb28c9b0a6400e3465193614c933d2b06326c299003a519243d853211d6a43287b0a6400a77855d3614c8014e90aba6c2990029da1474d85320053ac28e9b0a6400ad6831d3614c8475ab063a6c29908eb9a0874d853200572c10e9b0a6400e3754953614c801c6aa82a6c2990029da1743d85320053ac2e87b0a6400ab684dc3614c80156b09b86c29908eb560f70d853200572c16e1b0a6400ab6849c3614c80156b09386c2990023da1c40d85320047ac3881b0a6400a7685103614c8014eb0a206c29900f2d18574985320061f3aec930a6400c3d75d92614c80187cea324c2990030f5d464985320065b3a6c330a6400cb574d86614c801976c9384c2990032e192709853200679b0ce130a6403cf0619c2614c801976c8b84c2990032e191709853200679b0ae130a6403cf0615c2614c80117d0fb22c2990030fdd764585320061e3aec8b0a64008be87191614c80187eea322c2990030f1d464585320065db26e0b0a6400cb864dc1614c801976c8382c2990032e19070585320047bc3ac230a6400ab784584614c80156908b08c299002bce01611853200578402c230a649dcb676d90614c801c6ecbb20c299273a55cf64185320047ac3cc830a6400a7685990614c8014eb0b320c29926eada12641853200579404c830a6400af180990614c8011ef0eb20c2990029de1564185320053a42ac830a6400af380590614c8015e100b20c29926aada1864185324ce5b3b0c830a6400e3765190614c801c68ca320c299263a560c64185324c74ab98c830a6400e946490c614c83b5a90ca18c299003a519143185320071baa4a830a6400e3554150614
  | 20 => 0x3fc2ae1b12861887c855c36250c0156b0810ec2a1802b560c21d85430047bc3ac230a8600c7975d436050c0157308286c0a1802bc60450d81430053d42e41b0286008fb875806050c014f10ab00c0a19f6b6e0d601814300578c08a03028600a7a85c806050c0157309900c0a1802b660f20181435361fbaee8b2a8418a3e86d9554508c717d0db9aa8a11c30f19771551420069b28ee2aa2846ec3c651c1545080136b02382a8a100237e1d6318d4252d4fc22c631a8400ad88058c6350831878eaaa0c6a10021fe157018d420c43e42ae031a84008f7815da53508071e902bb4a6a10029760f6594d4200c5e432e929a8400c3f655d2535080527f0eaa4a6a10628f2195494d420061f3b2a929a8400b1f8355253508031790cbaa86a10026e2017550d421545f438c6a1a840087f855cf61508310f90ab9ec2a10023ee0173d85420047c402e7b0a8403c74615d661508018eaebb0cc2a10023de1d61185423745fc3aa9b028418c3c7555360508011f70eb00c0a1002b620d60181420043fc2ae6302841887c855cc60508018bca7bb2a9990622fa1f64553320c51f42ec8aa664018dd86dd643cc80317d0fb228799002762017550f3200ccf43ec8a1e6400b8d82d9143cc8011ef0eb08c39900a2fa1f74583320061fbaee8b066400c9c73dd160cc80187eea3a2c1990030f1d474583320064e398e8b0664008fb8758060cc80187aebaa6c899002a760f54d91320043fc2ae3b22641887c855c7644c8310fd0b386c8990021f61670d913201c7b40ce1b2264008f5819c3644c80156d0332ec899002ad60665d91320055d404cbb226400ab980997644c80187eeb3aec8990030f5d475d91320054f418ebb22642ea9d831d7644c85d17d0fa9ec8990022f61f53d91320070f29ea7b226400a3f855c7644c8014790ab8ec8990028fa1471d91320051ec28e3b22642ea9d831c7644c80117d0fa8ec8990022f61f51d91320071b28ea3b226400a3e85dc3644c80147b0bb86c8990baa760f70d91320051f42ce1b226400a3d859c3644c80156d03386c899002ad60670d91320045f438a1b2264008bd87143644c80156d02286c899002ad60450d91320061e326eab226400c7765dc5644c801968c9b8ac8990031dd9471591320065a320e2b226400c7b65dc1644c801970c9b82c8990031ed9470591320065c320e0b22641887e87dd5644c80187eebba2c8990030f1d774591320063bbaee2b226400c7475dc5644c80196ee9b8ac8990031ddd471591320063a3a8e2b226400cb7741c5644c8018f6ebb82c8990031e1d770591320065dba6e0b226400cf371dc1644c8019e0e3b82c8990031edd470591320063c3a8e0b226400cbb741c1644c8019b6e6382c8990033cdc4705913200678388e0b2264a4c3e76d94644c947c3ae7b28c8990
  | 21 => 0x20058000009000000000600300000240020040060000000000000003400e0060038000000002004800000400100200040060000018030000006000800800000200280040000020010004006001000800000601d00200080080010000018000002000000002600500000000080000008000000004007000800000300300040020000110010002009001000c00000000300080000060020074024006000002000a00000300180160000000024002000005801c00400c0000008006006001800001600000000e8000007001800000001c0000004008001001801c04602d0000044006000000002c00e002008008c00c005003800c0000000000008012000001000400c000000000400200400200000000050030000002012007800400000200280000080040010000004000001800400e0010018008000020000000c0060000008018002002001000c02a005003001800c0000000050002009001803c00000300080080000000000000004015001802800800e0060008000001000002801200e000801c00400d00180040160000008014014002000800000400500100140040120000000000000004000c0000390028000018000006800800400a5d8794f635505b8bb0f29ec6aa2af879d253d8d543970eba4a7b1aa8abe1f4294f6355001a70a9b82c6aa0034e1507058d540046fc3ac631aa800ad88058c63550011bf06b86c4aa0023720d70d89540047dc02e7b0aa8008f8805cf61550014eb0f28ec2aa0ff1d61e51d85541ff1b424a3b0aa83fe3584947615507fc6ce928ec2aa0ff8d5d251d85545571a21ca3b0aa8aae37429476155155c6e8128ec2aa0030f15270d855454e5aba6c330aa8008f7875846155001a38a9b9ac0aa0034715073581540069a2a4e2302a800d34545c460550011f70eb00c0aa2a2aee1160181540056c41ac0302a800cb5749c46055001c68a9388c0aa0030f15171181540065a20ae2302a800cb5745c46055001c68a8b88c0aa0032de1171181540065a422e2302a800c76545c46055001968a8b88c0aa0030d15171181540065a21ae2302a800cb7425c4605500196e80b88c0aa0628fe1965552433545ec36e6aa48670c3e65dc55490c01a6ca3b8aa9219bb0f9947055243004dac08e0aa48600c3d655d25390c3147f0caa4a72180b0f5d95494e430058fc1aa929c8618c3e755516290c310fd0bb82c5218021f6177058a430047bc3ac230c8645ada83d826090cdd1790eaa2c1218630f9d554582430047dc3ac03048600a3d8494b6550c014bb07296caa18031b5ca52d95430063d282e1b2a8600c78651c16550d4f8beebb9acaa18032edd070595430066db98e0b2a8600cb8431c16550c0197684382caa18030fd977454d430c45fc3acb21a8600ab8805964350c051790cb9486a18bb2b1897290d43004
  | 22 => 0x400300100040200000028008004002015003800400100800040000010008014000008006000001201d000000000800100000240000020028000006001000000400600000080180000000018010004008002000400000a0000004020000000000800200d003802400600000080100060030000000000004003000001e00400300100000040018024008006001000000400b00200000300050010004006001000800000400000c801001000b00a8004000007000800402a000002000000000200000200340020000004026002004803c000000000800c01c00e00000540160060010038016001000802000c00900100100080110000034004000003000400c000000000400000500000bc0300010008004004001000003400600000100000140010018004008000000000000c0050008018014002000001000c000000000c00a000004001c018007001800c008002000000800600200300180020000050000010000001000c004004001000000e006004809000c000000000800400100000000160030000000012001005000000200600380000000000000014056001000801400000800000140040010048008018004001000400200000000240000010000004000001000000c000002001000c00600a00100000020020000004016003009800400200700080240000090000004002000002800c000004000000400000000380180060010000014002000000000000000400100000000010000000004005000012c0040000030044000004002000c00c000006002000600100580100000010000000000003000004401e000004800400a000000800000e003000000000c00100180000000010000004016001004002c0000100000004006000001000000a003004800800c004000801400600000300080020000000004018002000801c002000003000000200200480100040000008024016011003801401c00000000e8008002000001800a00800080000140000000004006005000000000c000000001000200900000000060000010010026001001002800000100080000040000000000004000002009c000002001000c000000003802400000100980100000090000008004004000800800400c00a800000600000080240000000000004006001000800c03c005002800400c001002007800601a000001c0040020048020022001003000800200800480140020070000010038000000001400000600180180000020018020000000000000c000001000001c00400a0018000000004000800000000600080080000010000040002002003001000200b0018000020002008803c00a001008000000000000000180000000010000000000001000401200000000040060000000004000003000000002000a000800402e0020000058000000000800000200b0
  | 23 => 0x52e596800000076400e400115c0e70000000cd825b4bb09f925c00031980000001d320f10151107efc2806c94c24eec7286d40001111ae2b20000000000228828829dc6e14686ec44900000016d3000000112d42aa8612210555baaec0001bac53c4d7bc600009d000031382980000000001a28f8e0000000de85265e600020903b80003ea0000044458b780e2c2c801780026dd69671d3a5800095ca4f36d80005400000001196bda0000ea469514349d0ac0c1400057827114d88a6639043936908645b0750094000acf3412b0400000000019b51633a6000085d0ea1608a4935c000b5e267d7f81788e831e0d2400056938c84ac16c4204e580009195592d80b8492a4d0000247057d11c340111c00000044b000000067d4544e5400007b29b9ea106619b55526c30beb2c281c0004460000000b6d41e0005718a714be1de000006296d9ef0000ede00032900000014ae4b9000000000018c8ffde9831899e55480012565169de8cf86ba2bb289c000920000537ea8800000000000000000000002af08521233b4134c7d0000000000000061003527d40000000000000e3c0001e08000000b8b414a12ad32296442177400026647c0fec0985ff49199410fd41bc6304695559044328000aec9082412c8489430a01fc6c4c16a900f7dda453783b27f9cf44420092300140c5c06c2922b50cee8e2d4740015eca130f880000007c300000000000000000000af81202b002649168542108c645101b60002e0477c3f5000145887e7e44d992c46b98ed00040000000000020000000001002c00c0000038000000002001800400000500780040080020010000004005002801401c0010000008000005000001000600100400000020010030024004001000004c01200a00f80000240050008000032002000000400000500000300040020008010002000003800000200000300000080120048048006000004800c010002005800400400f000001801a00700000000020000018010000004009800c00a001002000400a004002000401600000300040060000008014004004001000001c0000058024000003000800000400b0030020000000000001400a0000020050022000001802c002000000003400200300280000000020018000004006000003c0100050018000026003004800000000e00000040000070008004014000003802c024000000000400602e0018000010000004000400200100200300020030008004002002005002400000e000800000200000000000000000000028002004003000000a0030010004006000001800c008004000000c00c001002800000000500480280240000020014000002005800000200100100140020000010004000016000000000400000980000000010000000000008000000c00800000000300000010008000
  | 24 => 0x1033bc0000002dc0000031441477a0000000000000d960005a3170400089e00028a00100000001c940005d3528872615e231000026200000037e1fd2d280460000cb968e0002662a24000a8a4fe810539d24c0ab4d3c8701b1b1615cd33a38539b8d540008ec000255157b00020b0001476a7200003b20000005c700014a463500000013310000034000ebe2318000f180ab0005768000b983cb1980000bb0b291190a062320492d52c40d2a000000019813f60e1b6952cc3087e40122947bc9c842c8ad8a4e44000f0c084730003e803368fe61225380012782aa000227218a326379820d4f900006987460008f5800147679000021c8f8c58e8d85456a0a00000000000000002614ae95a80000000000f966986a144088143e400055380013842a613dc00000019300000000003064bf11a24288a484000002bc9bd4f8106b12a25396d00102ce4ee27d83f96564673dc12f80000000746b435b07152eb80000009f28d99404c265c0497a7ccf9c5b81c72702e8649c00000000000000001db4bd87f2ab31e640002ab3bd8000000000593aaec0000003b729aa00000044800000000070e4400005c00050a252954600d00015a094000030280000007cb4261d8055c00052e880cd9ca4c0000000000200599800158c58f4258000a593bc000000000057e13a9c9cd0a5a213693c469aad642b8c1137c8d9b6c000170f0004ccd6f0c060000001dbce1e3598f580000000f30000000d745a70ea241c1fe28cc71000153c000000000161c00037c0b78e36b8c3788afc0000003941624000000394aae00003b75b2a4d127e0000fb00000003a800000000850000f2166c000b910001e455f68db055800000000001da6900000000000000000000000000000000044194e427022437e80640000000002daa8dc4170102c80000b574cd00012d080040f8cdc7e69b5a13289c9e91721f680d44c77650a613c08d25f650b9abcb099ec1b311902d23f609d4000df200005fa80a0000001d080000002e9481adb200077c366a72800017406bd3714700e050a4000b8a0001fc2ea027e1540000000000540000000040e75e0e100007a48eb80000012bc4bb377241454a12705dd80400008a56d0d1cea6340000000000009a39d0000bf80003132d6c00000000000000000000000000000000582000000059e54aad36000a562d000002a30003bc14f800054a00000000000003d28a6c1bf2d323344882dc480575965d3a059028c11b4f944a23491b8000070b40c8e9c95442204da35860085880026d0000000039c67aece05f8f497792a4b86dba14846563e931d9bd0eba262347800004c6170eba330f2a03e3c0800000000000ae4c0000432000227424c4b70000000000698371a75c4ba20f0002cf251bb310000d4c15530714ea7912043b31592314000
  | 25 => 0x68e12038b5b29c1e53a681c89be4d219400000004bd8f558584200000002d0161a22d0001b0949a9453e08000334000000000000022f00020dc00067337a80002b8000000118ccf40004d4ae5248a00046b80012c65d10d691dd21a34a27b54151bc0000000000000000000014c000000000000104a000000078c000a1d32f81480870000000000ce266659a0f305e0000502e0b40000d884a131d4b4000000071200000024b00003479aa46180006683320002d540009580000000f1e4ea800000023600000000000000000001d482a030d402e97946d9971bf23e400000050d80000000004b48000000000157a5b473c6fb369029c0008a73df8000a4797c3b8800000000000022d800053400000005158700000000a230000000000ff8a6c86c0eecc3aac70000000312000000155c0000000000f98000000000097800027098700000000001d000000002b83b8cec000028d00007f8e4848d2e400004780004888dac0000000c22d080006da2aa87560007923699cfc99e00000020390c2b3e0000f267260005c7460839224ba8ba81163e87800a08243ce12100009f000000000000000009becc210f43c03802f34fc02fc2d51e561b14f30000000000000000505c000000188c4380000005c332080000000005348e08548a2c22880001e0bb1494a7c422c4f2becaa3128c87899b002d45f09b9c08000000b6200007883590001401ae50f2b6d343cbbc00083a1d883303072d2156d0ec75882f065a9f525018513712845661d98000a840ca0003e8811d35a0000000000d4876a0000d8093d5fb3588000000a264881268f8db37522adb95507df4118745236a8100004486200000000000e1a00051690200003094551eed64a000460906c4a8ad901e22cced6000000000000021f0b7960c0000000002b9800000000003ae000000000000015c7841f88a4b38200000029ac00055f97183720009834ca01f00005a60edc000e2842d53c2504104000043282800000037f800000028ba824d793987d5099230046100000013905804f436a913e000000000057600014a00029a93d50000f500000000004060001318000000000119c519a65a02000000000000014b20000002c0145304dc7901a0a290001d209e6b2c4a558299947542ec56aa9cc0c2b8953d90351340003f5a07963a000000156888a4b310d88ec00000000000003441314c880000005d028200002fb0005a900000000002608000000000000119e00000006100003da7cf29114a04020001b4023800068600014502ec0000001ffcc790003ec5e182890002e200005909f903d07301d21f31a804d159600000002340003ba220e3f40000003f3c0740003c95b5a6c4c0c180049c0006851f09a416a021c05480015ea0008644b5095c0000004e21e093a68300000000000182800
  | 26 => 0xd91c4fcc0002d68e940236b60f825805c4af842e09f4c8e20a2c5a9c4166a6439611527648ba0a180ad6c80001ab0001296bae000000159a3ea5892158000ac93fdc5ae5161ae000006d41c00026b00000000002ca8000000b7526a4798a88a97000000073676200029555d20dd80027936f40000000000b590000d01228000000000019000000000022f0b960000000e2f248000000000000000000000000004508000564000000000115893c9d63db8000c4a0004465cbc0b056e0000580000ac40e7400000000022dc00076a53f000000000000005109d94130000000000000000000072afe27b900021d117a044b2c10900008e886eab4971a0001798fdd752475148000047100028f06900000000002c5c00082a197ae900000001561b9400000009d0001007833dca27388a043a2f216bcaff80f5c29f6cc9c52d1ce8ce9008000000000000000000011f00006fa0b5028131446c5036a346dc959d5cad34fa4b483e290c064e3690721440f160002d220480002e800000003be000000000000000021a9d14f46679000000144284e4c79578e444de00008641f40001abc16c0000181e22aca1834340e940867ae00007e008d2f420800000000004f52c6ac8c8f259e80017e00002cc80007b8000431138a68400000007600000003af000279600010620200001de71150400003e979a1a580000007800d364b0000b3c4ed00003880001d1082c3300003bb16b850e01a3f44000474000245c0006f60003260b0d4909900000000961a0350f26ecc85a2d96b9434fd2000000000033f0690000000c0e04d08221f66fe73311a9cf08ca1fc0bc807c57b1ef1f7ae6ed02a6d4cac17afee24d2686dff0368944d0005a1585ca0619ea53c00ad597178000000000000007bba6ec498001012000585ae0cc220f2359a804b64a462a918a06886ea06daeb4ce8000000000000060800023c03729fda9d043d0d539a967a17418853c0126e28d16862a0505b0f9891d35324ed3ef28638025f400000031c000137800000015ac78ea8b5bc8ff887f0005b340013100d985a2c6d2f248737b08e09f900043b2e2a0000002c31794db87561b50f287f21da4c30158846a3039012773d64784cc85004aa7de4f4ab46cc224aae7a1140000390002ebd04f96600000000000004b806ac409000161062f3f648e2da1e708289ff00000005ea18b166a8d052a4b60ec16201ac000415943057a0000b348680006761cc1fb02c37881f0cc5934c2b015680010d0000000298000000000000000007f80a700000002ee4231c0817aa5b13d0000f44370caa9e38102114000271261098d4952b4071e3651bca4580001a7c870544c3c40c2cfa7d887c386439a2bd02207923a00a431a00050f9f58212b1909203e0866000508897d2d644d1bc46640000000c0d6cd00
  | 27 => 0x82255b800000017180002400140004588e40a3f0000a163da1302361420b913c482e29a89813dc2a300007e86f8a1920e400170c0000000320000a28a4308220002f248b85dd2921899a880000000003d00000e8e5ac58426c67ce70542895908550000002564000000004c0002b600053f04000000000a9d87127441220d17094e90003338000da0000000000108400022d0d040004a1cd806500009e60000000108a651a3e4e01b590f010800000000027080017544fdd97a37c0004093d79aac5980f1acc6da5392af052490760006a50e5a6e8000011000000171941313a18c400029e80e28cca105723de0daf4fe3b9433000104c0134da9d2800037d510000137000008980000000b83e10dba000550585220634e5df528110c1b40a40b82e5482207f00000000000003ba231c00025047b000000000027e823c38200009e80000002938000000000657276839e000000000000000000000000000d62e03d82e089700004a190a737b1dc80000000000000002df0f8c06480000005b8267d3d15d55860001158b048880002fe9f7400000018f92b40006e4189aec068b71202000000009dc000000059ca8751b15895680000860000a70a00158c0000005472aa0b100008b426c95704254ec1ac48801a238d205abbc3503582c7c8fc5ec246080800000000000003d00002182f591f8a84162132eb7d57c8e44b38e30ad802a4e28000ff4a80d7f8cfc00a00045600001ca27781deca8096a8000000000000005a500000002780000000000ba300000017135f700000000000000002c1800000015f1af17301d0000000147a571192932f37e055001896401e9c62de53200009720f09af8c0490c3f516449746515121b5c9d7accda214c5732b3f01f80004a56f24898af11dc6141d3623000000007e93294ccb1a2ab29a6ba50cf5080000f7c225000131f643b80455c2c4d7a00000005e000000000007868fa0000002b380000000000000a25a4222c000000000000000000000000000000000099a29d4540000005a0ac7098c63f1e9a8700000331a181dc0dc1c01a3232900a000275994c00000017880005f87fb2c64000cba0002fc80000003173b300015f40000c080000000004d107f60000003158000000000147c00000086b1b618dd356604589900000000028900b036e8a8000133832c6b84af80000005705ae000000048c4db1d6c54415512924c8b0488dd31072e09745725586793755742bd93fea3817343124f8afa9efc8c8960e0887d14b9684db23e217c035514f86d06f09a04d855b58c266c02a41f0c89924eaa1f91f01e0c2fa79b196a6d32b675905ca88916a659537871406087a3320c8916524f0b18fb06c298103e8f007d10aa06a41767d3000000061c79e2c918a1cb9140a5c04600000000005ce2d0c1225f14b
  | 28 => 0x107ea790001ff51ee2c1c850e7c000a0b00000000000ee3a400009a36e15cd947c0000000e6400095e69c000015116ea2a0001096bea5e800000360003910002b6c00016e8001664f420001a4c000000000000030a00031d11ba4880000000e401e173a00044f966906c0000000d903529e337ba31083a31a000285f0259181fe0254d34b143fbc0001ae5e1253080369e0004064000c88000000174f0024ef000068a9a200003aac0ca1215a521818892db0903b0b9cb9c2bb848ca1340e00000029fe0003633d2000000000000011857640000002e4c00048409c400132900000019c000000010a9db000072b18a80000009fc4bf80002eb000348ae2e0002651fc40000004c332f04c6d60acda272af2a5201993180002d000000000000000000031d304656dd53b968c1a4aca380a33c00079f28040009488a2800000000096c0000ffc000000000234145608b01b0000000a12085000014616d00000001be0000000000000000000a764b7e0000e7a4553b07104472c89452298360a1ecc60000554e2b4caab8733199687fa0004ea02e80c0a2517fae68efa00000b800000058e55f4000000000339000000000022ad1ec4fe00011486bca364622350328a0000053383a104025657f1b7c54e0003469a9d58152c0000000000000000000092b000012000040ba2cadd2ce953a1ba13481393380f50000cb0a320000841356b5655f1c759fc2788323358000648167cf8c9680008d35790001092b6a000010c00000000000000005708000000fa6145027924d5c04b400000016f600047016945ac2fb0000440484246c0317240000002d8a0ae2828821c41dfc9ce66940d51553eb39721ec54c4deb97221c0000000000000000000aac4c5ae3cb72000359094c0a77ed000193452412a26aa8c4bac49850c1198bc44b20001ee80000000000000ea81330001a0d6708410ed8c7025c7442696320a062eb04e0000ee428523d05f141500009429e33d0247c099ec4d404be9d6a98c83272a5191cc08813924f2925129852b1891834e6c81c39880c930a33c2d2cf44ba862f05aa4b4084a0ebb19ba0518000289a4182fea0d34f19f0f562f7022d0040008d5578899a84a0000001f691520000000000000afd0980cd400000058a9cf804b0005b780005322ec8ff911e29eae42f1a062000b8f9d5447953f4db0001ff90ab1f705093750b60001ad4ed8d2900042690f152200003798552de0001db62000009f4000261cda83a300000008e400000000016500005660000000000000000130452f203202800000005294f51d27131d71aa523c00000000000009b934b800174ab775af80eb3da0000002484c9e00000024f412624e00007a0d882d0800232c00033900013f80008341d4449400040300025dc0009405a6164945740200004ec0
  | 29 => 0x26b1769e8ee0e2df0061ec94f8147121954d6a83e526012212f04c938b162f2b8000139173400000039d87540007e80000000ee00a948f80000007580001474b7530c12b6a7c12e00007ca218d8600006e000131c0005a48b604f90002ae8000fce78a00026e6358000005c5e8eb8354390948cc8c1972491594000000437a4d55e645e172409c89e0003290764284000573800083073525fee983ac9c02944000eea63a0ce0c8d52c00009f02243e8000431a5b8c543890002a26fc00005c82ab91a461a1dd5de51e873919e847cdc496200022e400081017f0000000a580001e4c00000016a1e50000000147001f0eea440002ac0d1c24a000000000017528597640006c821593626d3b163c38000d8a00030caa9835439a024068c0004f213c92fd4e037300027dc4546ef068057c00000036b0e2800033b1b8aaad0e4b532bba3b25c79db000192073f1f3aa780002d5b6125408c06f302f3a705756a00003a4953800005d22c9a4ceee000241aa4907282100019090a69eb9e197cd5108e7509cf646421392b6c00010aae111a030445844db25152167a8ef2cc186d36400000008cc00000000000016ac8f880029d4e680003c480010b300000022960007e200021f0000543418a7540000000000001744a08cd38cc4ade70e1879ed15b12019ec061839a0000001bb08ba9cf11f1610d5d0f621f400051482c00028f029b84a03a08f400022803196d96fa2220541e1547200027d1e58a0b9f200004a400000000000002831fecb2ea94568b7f0fc00007e59fa1ba0e8b66a9cd0001ea901600000002210aa0bb423a3ac0001900000b2e7b80001aec000fe100000006c069c7405bc23340000004d299b95ee6560002d64b7c0000000001070879c5300014342989ea000129a0004d4230906ab1150c6d396e213631e88340008400818000dda2494f088980000001b800000000000002600dcc32008e8a3d0b048936600006e4b6600012b06020002152a500005f0000000049630b2ee2d600007c900000016c6899501d118bb46365990efc00000000000006225fa0002b14000000000000022e000000000038c27b4459d3c6ce7d8140a79c86e00038d226d1a80005bf1a8caa288a5342cd88d900010206f123f00000017b91220cd00000000006bb1950000b5200007b800000048f0000f7c2cc000433a02efec3990001d685f419238e1800e1089bc0351469c60000d96cb35ca4bc0dd8414ada546000053400000000000004a25a08000dbd1383e6a4dc3ac0000000c711c0b0aa04c9980008d07bd2f9080b1e200018f2a0c30637749c80000008dd40a8000d2c8f340a0a500000000000000a8a2e080025b200058100021a40000004fd67da00021380713a40007e3000000000000000000014040003ce92140007180000b656b46320
  | 30 => 0x3f9000055225c48a188955eb5110f23e92c24f85184c60e1439439c28325063840e3c00000039c35c592cd800925b62a80000769a211e414a8af94370000a043f24ffc00000000024d8bf56ba00034fa9b0000a3722627ba3f6506455a6bc0000000001360000014c4b80003a43f42f78388c40a7e80011beace0000002ad80000001588fae0008c95b010d923455800002582f60d900000004e30000cf93f00000004068f9e00059416800001e2b9f393000007a86a0228000534010000000124a1e9ba10f6c932a9334802dd11253215648b800079800b288c000000427a05cc8aae80da104000028200022e00000000001ab800000000028aa000a8e000000172c00000000005f200054d95340007e525ea2844040004924ac326eb924848000fe6616d1785c20006a2000004a00000000000000006a800004600000efb848000501000000127cefc4e62241c8cd0e057449254413c46b3b0863d1600cc800163037e000000000000058700029d10b4a9c2deabb956a00046d00000005c64a400000000001bc2cc14e350a5d622f803f7570220871240ba755f8ee000034500000009600005d09d4110a74614ac0010fe91252b4000000a4e0ab0b877102e63d3855c6b200051f0674a400005879ba428c216299800000081629daa60000acea6b612000016100020f43091868001334a1c0002eaa07400050f283800078b9014f500000003030000f8a000ab1000218e000adc000000138e27680023a8bd247355d04b52883bb80000008a44b517a23f04725d223781647684569eb1aa88824c500006e0952a3a5238f350e299f4fc0d7d1b212c0000000b8e2124b2039960e4ea0812ead0348d113d583c0000000002cec18e00055686201da9dd00000000000002b0a3ec0002e50001fd7284264b5619bcfde4f93b9a49c13e16b000109c70e00019c15e45ba00007da624a220513052a10522ab24d613113fc368a7b0f68000a8f51a800156600000000000000001ad0fb84221350002b013be0000000698e649c7ae840009050000398000e18ab48001ecc0000003eccb440000000000000000a7d800000043a0005862af481c09d0000000000000038a824d6e0001a1270c0000000000d2200000020e042c09420c3da80001646d108693cc9845b73cb98ea7a0257ccc000085e62d00010b9164270000000000090b15b800173cb8582f95240ce00040c07f41e5b72427491c52d65b4b280490bcac257a00003860004cb212e0000004d700000005414e0c0000007f92d6c0000006de36398d0000000165800000000001400003ba4760000f90c7cb7d8000c62d1083e3f80d880007f385f00000008f54e880000000000bb40e174080700023f81c662100018912b43fa00023fc0007ee00016d430bb01471a92c00000000000000000000000000
  | 31 => 0x1b242db65c01b9c5c81e4974a999d511a00000004be1a8000550800038e43ccc9a81f24c0001ee8000c1877a00001b49ee8a408a800000000022e2a654dc2065b393940009d23a89150000ac683800000000003420000bce45f34da00a18000055200000000004b89f3400000013f4000b3820e00000000000004a38e580008440001ad000000041389b2d6a0ce435d204f5c56329813516482b9000254000000000000000004e00001980000a5341407060000000002b4c0000002dd8520000ad758f000141857f45fa5cc000643000000147e22700024c57259745bb09040000003200f38af45dbb81800000068900000015ea7ad2f505c400000000019ec7110000000001146000000000018caea3e40dd43d8a0631180000002ba12028587c20003c6800111e000000000134600013b86af6d000028447385940000000000000975000076205a00000001f866642c5c200000000000000000fe8b261f599a00b82673aee55c00072d172c00000038300000000002c6568a4d800000014fa900f8859315aa53cb3a7c03cf20f032a26a24a52454945db383000000090050280000002c532a00d16040000002b3ecc4000373a260cfc7e10002b780007dc0002bf151b00029500000000005b980006366c64044ea46a400035fa8b8000a6dd428d5c1926cf17518250a462902f0f14550ae22519a745792889c6c0090c07d734629055041bd36529d8cf022f8582558f6c3d51d587d53e9063da291aea4a6fe0b2841c4e699259c84dc2b90000000000cd40000a9000039461f00000003420000000000000000000000025e0000001da2b00000136ca241c25263a097d132a0000c5141a07400002d09900000001ad800000014b3d61ab40000000000f0800000000016280004284731530fea1be45d9c7c4908548002a68426000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x103e9815171181540050da44545c460550014399015171181540050d254415c460550014359715171181540058c640545c4605500143695e1171181540052c640545c460550014369815171181540050d260545c460550014369315171181540050d648545c46055001c329015171181540050d640545c46055001c319015171181540050c640545c460550014349510d71181540050d257425c4605500143495d0171181540060d995811c15490c018346560470551420040fe61751d7644c80103d9815276551320040fa60541d9544c80141e9315076551320050b648541d9544c8012379855054d85320048de6154150614c80123b9855054d81320048ee6154150604c8018366560470552410050e640541c165504af03d98d9774545410050e640415d46050401834815d542181410040fe61751d5648c40103e9815376552310040fa60545d9548c40123b9855054982310048ee6154151608c4f5c88621d0704c93124730188711c1324c47f03d9815376550310040fa60545d9540c47f03d9815376552210040fa60545d954884014369115171d96400040f66241dd5619011143597d51619464027c0f261655d2509000183465604705514000583648755506350001295912015418d403de86e1480550635015921f985505118d400068655180144635010b21f985535018d400068595181140635001f41f97550639454000585e455418e515000103d9819470505402860d604651c1415000181d8518c70505402860e1d880551505000133191201545414007d0725d5418d505001f81c875506354140005862415418d50500a103e96e1571901400040fa60655c6405000181f8518d71901400040f66054dd954cc00103e9815176553300064c151811c154cc0f5c8a621d0704ca3024730988711c1328c00103f985d475d91300040f660549d9544c00103e9815076551300064c151811c1540c00199043604705503000646214845c3320c00191885211700c43000507654641cd644800143595190715912000507657411cd644800141d95100735912000525644401cd644800103d9815276551200040f660541d9544807f03d9815376553101fd0da4454dd954c400103e9815176553100040f660549d9548400103d9815076552100050e640541d9548400103f985d475d91100040f660549d9544400103e9815076551100050da44541d9544400143990150765511000487e6154153634400121f985505418d100048be615415362440018358719065905100051965c6518a4144001c25751906290510007115d46318a414400183454219755051007e252187350540440013319520141501100040fe61751d5640400103e9815376550100040fa60545d954040014a4975907244010007091d5641c91004001c85641cc7244010
  | 1 => 0x31186f2436b7952e25390898bd38bdad933a24bb0b11aab63e1ea81c1b9f348f040e93808f853b8c00002080d694a1ac30927412380027868dad001a1b35800020002ca61c8284aa1e000900370d000809a23018ff078203071633bcbc1781004019258000001d000032803529b31d8c80292319a3838a3abe980015ae8a80128e1aafa28000110005aba110803190170000000632268b9fa881ab14002739820342c180c20082010042000b4000028040000140004201c10245c0c002870180420080004000c04142404980143a961537058d540050ea58541c1635500103d9815270d855400507a5854dcd605500141e9615073581540050da58549c460550014369615171181540054c640545c460550014359715271181540058c640549c46055
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x85401c03c05cb40330d08119601200a2580001b150414e4c31b16000c00094428d901517118154004c2146c80a9388c0aa002418a3640545c4605500130851b202a2e2302a80092428d901517118154004863404c0a8b88c0aa002414a3640545c4605500160851b202a2e2302a800d04e8d90151711815400486146c80a8b88c0aa003410a3640545c4605500120851b202a2e2302a8009096889510d7118154004863404a886b88c0aa002431a0257425c46055001418d04cac08e0aa4860090628d9015070595413de0310e482a831aa0a0002611a12415418d5050001419530a8c08e0aa66000a0c6985460470550300052214a21b02382a818002418a3640541d9548400120c51b202a0ecaa22000a0c680542197550510
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x6002800004410b3680981517118154004410b368095d097118154004901b2294436047055030004810b3680542197550510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x2
  | 4 => 0x4b
  | 5 => 0x4d
  | 6 => 0x94b
  | 7 => 0x94d
  | 8 => 0x124b
  | 9 => 0x124d
  | 10 => 0x138b
  | 11 => 0x138d
  | 12 => 0x98d
  | 13 => 0x128d
  | 14 => 0xcb
  | 15 => 0xcd
  | 16 => 0x9cb
  | 17 => 0x9cd
  | 18 => 0x12cb
  | 19 => 0x12cd
  | 20 => 0x168b
  | 21 => 0x168d
  | 22 => 0xa0b
  | 23 => 0xa0e
  | 24 => 0x6
  | 25 => 0x130b
  | 26 => 0x130e
  | 27 => 0xb0d
  | 28 => 0x140d
  | 29 => 0x24b
  | 30 => 0x24d
  | 31 => 0xb4b
  | 32 => 0xb4d
  | 33 => 0x144b
  | 34 => 0x144d
  | 35 => 0x16cb
  | 36 => 0x16cd
  | 37 => 0xb8b
  | 38 => 0xb8e
  | 39 => 0x148b
  | 40 => 0x148e
  | 41 => 0xccd
  | 42 => 0x170d
  | 43 => 0xd0e
  | 44 => 0xe8b
  | 45 => 0xe8e
  | 46 => 0x178b
  | 47 => 0x178e
  | 48 => 0x104b
  | 49 => 0x4e
  | 50 => 0x128a
  | 51 => 0xca
  | 52 => 0xc955
  | 53 => 0x94e
  | 54 => 0xb8956
  | 55 => 0x8a
  | 56 => 0x12ca
  | 57 => 0x10a
  | 58 => 0x130a
  | 59 => 0xd255
  | 60 => 0x124e
  | 61 => 0x138e
  | 62 => 0xb9396
  | 63 => 0x104a
  | 64 => 0x98e
  | 65 => 0x10b
  | 66 => 0x180b
  | 67 => 0x128e
  | 68 => 0x9c0d3
  | 69 => 0x12c0d5
  | 70 => 0x1680d3
  | 71 => 0xce
  | 72 => 0x240d3
  | 73 => 0x1440d3
  | 74 => 0x9ce
  | 75 => 0x12ce
  | 76 => 0x252d3
  | 77 => 0x168e
  | 78 => 0xa4d
  | 79 => 0x134d
  | 80 => 0x14d
  | 81 => 0xb0e
  | 82 => 0x140e
  | 83 => 0x24e
  | 84 => 0xb4e
  | 85 => 0x144e
  | 86 => 0x16ce
  | 87 => 0xbcd
  | 88 => 0xcce
  | 89 => 0x170e
  | 90 => 0x150d
  | 91 => 0x198d
  | 92 => 0x8d
  | 93 => 0x184b
  | 94 => 0x154d
  | 95 => 0x19cd
  | 96 => 0x14cd
  | 97 => 0x194a
  | 98 => 0x15cd
  | 99 => 0x58b
  | 100 => 0x18cb
  | 101 => 0x3cd
  | 102 => 0x1a8b
  | 103 => 0x1a0d
  | 104 => 0x194b
  | 105 => 0x164d
  | 106 => 0xecd
  | 107 => 0x17cd
  | 108 => 0x5cd
  | 109 => 0x1a4d
  | 110 => 0x10e
  | 111 => 0x2cd
  | 112 => 0x184e
  | 113 => 0xd4d
  | 114 => 0x18ce
  | 115 => 0x134a
  | 116 => 0x14a
  | 117 => 0xbc955
  | 118 => 0xc092
  | 119 => 0xbd395
  | 120 => 0xd693
  | 121 => 0xc9d3
  | 122 => 0x580d3
  | 123 => 0x140d5
  | 124 => 0x12c0d6
  | 125 => 0xd2d5
  | 126 => 0x15695
  | 127 => 0xd355
  | 128 => 0xcbd5
  | 129 => 0xd515
  | 130 => 0x19c0d5
  | 131 => 0x152d5
  | 132 => 0xd995
  | 133 => 0xc155
  | 134 => 0x1340d5
  | 135 => 0x1352d5
  | 136 => 0x94bd5
  | 137 => 0x15355
  | 138 => 0x256d3
  | 139 => 0xc253
  | 140 => 0x19cbd5
  | 141 => 0x19d4d5
  | 142 => 0xd453
  | 143 => 0xd8d3
  | 144 => 0x25693
  | 145 => 0xd6d3
  | 146 => 0x16d693
  | 147 => 0xc593
  | 148 => 0x59693
  | 149 => 0xd793
  | 150 => 0x179693
  | 151 => 0x592d3
  | 152 => 0x58253
  | 153 => 0x596d3
  | 154 => 0x25793
  | 155 => 0x24593
  | 156 => 0x178253
  | 157 => 0x1796d3
  | 158 => 0x5cb
  | 159 => 0x17cb
  | 160 => 0x5c593
  | 161 => 0x5d793
  | 162 => 0x585d3
  | 163 => 0x17c593
  | 164 => 0x17d793
  | 165 => 0x59793
  | 166 => 0x1a9953
  | 167 => 0x1a57d5
  | 168 => 0x11316
  | 169 => 0x184b96
  | 170 => 0x14d9d5
  | 171 => 0x17da55
  | 172 => 0xd9d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 43
  | 7 => 1716
  | 6 => 6242
  | 5 => 2995
  | 4 => 127
  | 3 => 25
  | 2 => 4
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
  | 8 => packedAt gbK8 (1258+((h/20+packedAt gbK8 (1118+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (72480+((h/749+packedAt gbK7 (63492+(h % 749)*12) 12) % 2697)*12) 12
  | 6 => packedAt gbK6 (334462+((h/2489+packedAt gbK6 (299616+(h % 2489)*14) 14) % 9859)*14) 14
  | 5 => packedAt gbK5 (192123+((h/1186+packedAt gbK5 (176705+(h % 1186)*13) 13) % 5167)*13) 13
  | 4 => packedAt gbK4 (9242+((h/44+packedAt gbK4 (8890+(h % 44)*8) 8) % 159)*8) 8
  | 3 => packedAt gbK3 (2065+((h/8+packedAt gbK3 (2025+(h % 8)*5) 5) % 32)*6) 6
  | 2 => packedAt gbK2 (371+((h/1+packedAt gbK2 (368+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fe07ffffff807ff80ffff8018733f9cfe73fc
  | 1 => 0x80ff80fe01fff80fff07ffffef9cd8e3638c7f
  | 2 => 0xffffff0001fffffffff80ffff01fe0ff83ff8f
  | 3 => 0xfffffffe00000ffffff0003fe0ff03fc0ff0
  | 4 => 0xfffffffffffff0000000003fff0003fff000
  | 5 => 0xff00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x29200b9693384293800a9c8188310b8c2e31bc
  | 1 => 0x886280aa314ac884a907ad2a8b9458a1628455
  | 2 => 0x529555004095152952d00255300aa056815a8a
  | 3 => 0x10d9e64d6401810e7ce5400635c0f503d40f60
  | 4 => 0x60fe78f1f9e7e7c0184184183eff0003fbe000
  | 5 => 0x7c10408181060600608608603f7ffef8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeee0eae0eae0e8c0eee0eae0eae0e8c0eee0eae0eae0e8c0eee0eae0eae0e8c0eee0eae0eae0e8c0eee0eae0eae0e8c0eee0eae0eae0e8c0eee0eae0eae0e8c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37445
namespace PEqualNP.Outside.L_meta_37445
open PEqualNP.Outside.L_meta_37445.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 3 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 10 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 13 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 19 := block_range (n:=19) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 19 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_128 : Interval s2Atlas 4 128 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 144 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 48 := (concat bs2_5_0 bs2_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 21 := bs4_3_0
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
theorem bs4_4_96 : Interval s4Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 99 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 99 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 4 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 25 := bgb_3_0
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
theorem bgb_4_96 : Interval gbAtlas 4 96 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 127 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_2976 : Interval gbAtlas 5 2976 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2995 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))))) (concat (concat (concat (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))) (concat (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728)) (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)))) (concat (concat (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)) (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016))) (concat (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112)) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208))))) (concat (concat (concat (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)) (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400))) (concat (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496)) (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)))) (concat (concat (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)) (concat bgb_5_2720 (concat bgb_5_2752 bgb_5_2784))) (concat (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880)) (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)))))))
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
theorem bgb_6_6144 : Interval gbAtlas 6 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6176 : Interval gbAtlas 6 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6208 : Interval gbAtlas 6 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6242 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))))) (concat (concat (concat (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928))) (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))) (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)))))) (concat (concat (concat (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))) (concat (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824)) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)))) (concat (concat (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016)) (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112))) (concat (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304))))) (concat (concat (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496))) (concat (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592)) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)))) (concat (concat (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784)) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104))))))) (concat (concat (concat (concat (concat (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)) (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296))) (concat (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)) (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488)))) (concat (concat (concat bgb_6_3520 (concat bgb_6_3552 bgb_6_3584)) (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680))) (concat (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776)) (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872))))) (concat (concat (concat (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)) (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064))) (concat (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160)) (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)))) (concat (concat (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352)) (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448))) (concat (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544)) (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 bgb_6_4672)))))) (concat (concat (concat (concat (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768)) (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864))) (concat (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960)) (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056)))) (concat (concat (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)) (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248))) (concat (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344)) (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440))))) (concat (concat (concat (concat bgb_6_5472 (concat bgb_6_5504 bgb_6_5536)) (concat bgb_6_5568 (concat bgb_6_5600 bgb_6_5632))) (concat (concat bgb_6_5664 (concat bgb_6_5696 bgb_6_5728)) (concat bgb_6_5760 (concat bgb_6_5792 bgb_6_5824)))) (concat (concat (concat bgb_6_5856 (concat bgb_6_5888 bgb_6_5920)) (concat bgb_6_5952 (concat bgb_6_5984 bgb_6_6016))) (concat (concat bgb_6_6048 (concat bgb_6_6080 bgb_6_6112)) (concat (concat bgb_6_6144 bgb_6_6176) (concat bgb_6_6208 bgb_6_6240))))))))
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
theorem bgb_7_1696 : Interval gbAtlas 7 1696 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1716 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608))) (concat (concat bgb_7_640 (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 bgb_7_832))))) (concat (concat (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024))) (concat (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)) (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248)))) (concat (concat (concat bgb_7_1280 (concat bgb_7_1312 bgb_7_1344)) (concat (concat bgb_7_1376 bgb_7_1408) (concat bgb_7_1440 bgb_7_1472))) (concat (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568)) (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 43 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 50, 58),(inputs.getD 4 zero, 42, 58),(inputs.getD 5 zero, 26, 58)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeee0eae0eae0e8c0eee0eae0eae0e8c0eee0eae0eae0e8c0eee0eae0eae0e8c0eee0eae0eae0e8c0eee0eae0eae0e8c0eee0eae0eae0e8c0eee0eae0eae0e8c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4007717600 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37445.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[0,6]⟩,⟨.and,[0,3]⟩,⟨.or,[2,8]⟩,⟨.and,[2,8]⟩,⟨.and,[4,5]⟩,⟨.and,[3,11]⟩,⟨.or,[7,10]⟩,⟨.or,[9,12]⟩,⟨.or,[1,13]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717600 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717600 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37445

open PEqualNP.Outside.L_meta_37445 in
theorem PEqualNP.Outside.L_meta_37445 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717600 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717600 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
