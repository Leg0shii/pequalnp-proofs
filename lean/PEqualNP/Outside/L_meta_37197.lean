import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37197.Model
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


end PEqualNP.Outside.L_meta_37197.Model

namespace PEqualNP.Outside.L_meta_37197
open PEqualNP.Outside.L_meta_37197.Model
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

def SBf (j : Nat) : Nat := [7, 7, 6, 6, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37197

namespace PEqualNP.Outside.L_meta_37197
open PEqualNP.Outside.L_meta_37197.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x1200f800c690174a00000101422a26053ab420131944606230008691140d49b2854e9238787875058010009058e001032001d200638a1520c1ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x12380000500c04005c9e14260060001800440a5a008a4e002200ae0090a0b4400016000200009c78009874009600003a00005210640082005600000062000000006a000608007a340000926c004800002c002a240000322800b6000000aa6e365e00000000b27094008e88540000000000000000a81a1c76000030002e20589a683c84ac72807e4aa68ca23e00000000000000a4b046007c00421e4c66860e00000102010002080206070000000200000800080103010101010000020c050eb7a92876c5250ebea6a15714d429faa2653c544cb9a64194f943419eaa4835f53506b8a6a0dbd4941b6292837b50506f0a0a0e7d4d41ce29a83af5250758a4a0edd4541dda82833c5050770a0a0ce141419f2a0836e52cc6daa598cf952319eaa4636e528c6daa518cf950319eaa0635e53c86baa790cf952219eaa4435e53886baa710cf950219eaa0435e53902baa7205b94a40b6a94819e539033aa7206b94a40d6a94813d519027ca1204f544409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520af298415d530827ca9884f55310dc206213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4086e10010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xe04002086ca70a3191320cb0c5314941c6d4c50507185314141cad4850507285214141c394e52902396510010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (788+((h/14+packedAt s0K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s0K4 (2724+((h/30+packedAt s0K4 (2484+(h % 30)*8) 8) % 161)*8) 8
  | 3 => packedAt s0K3 (312+((h/2+packedAt s0K3 (304+(h % 2)*4) 4) % 12)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 2 => 0x3f81ffffffffffff81f03e07ffffffffc88fff
  | 3 => 0x3ffe03ffe03f81fffe003ff83ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x84882808c489082016514a284a212954133615
  | 2 => 0x11245191091260c580a4148694c652a8c888ea
  | 3 => 0xa6149aa243a42b6aaa0927b227691c0d70d34c
  | 4 => 0x3459634492074db34d3d812439b38831bd03b0
  | 5 => 0x386183871c3871dc71ce39c701c210c1eeec00
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37197
namespace PEqualNP.Outside.L_meta_37197
open PEqualNP.Outside.L_meta_37197.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x340088028007804800a8038000004c00b8a181800000491253aa00003e084000001580000000108010800064d80200000352011800001380160068500a8000001c00000600003c00000004c00e0058020000000012000000102002000608000000c001ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x50d09801125018028060e9f000f801e9a0b02001a802b16a285a395a580002a0f27a926891ca204198b9421ad0c9012a8ac981711ada4ab961d1c0700000e29811080260a9480000323191380079e211520a4200c131d88868a120017ac00802a801f8027048288001b1880039b8d80011a2000c52480000040d00000400628000030824c020400101bba8a87745150e7ca1a14f55242afa9a855c5350aeea2a15d14542bda8285785050b3ea6a16714d42d7a9285b75150b68a2a16ed41429e28285b85050a70a0a14f95042bb28e657551cca7ca9194f55232bb28c6575518ca7ca8194f55032afa9a835c535067ea898cf15131ea988633e54c867aa990d794f21aea9e435e53886baa710cf950219eaa0435e53902baa7205d94640baa8c819e539033aa7204f54a40db28c81b5519027ca1204f548409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2eca2185d544309f2a6413d54c837081904fd52209e2a4413f5448278a89057d4d20ae29a417751482e8a2904f950209eaa0415e53082baa6105d94420baa8841b8400827ca9884f553109faa2213c54442bea6885714d10b7a92216c52442bca6085754c10
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x20406aec809c514c5150b1b5314142c614c5050b335114142cc1445050a94644c431c594e51902396510020
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
  | 3 => packedAt s1K3 (312+((h/2+packedAt s1K3 (304+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 2 => 0x3f80ffffe03f81ff83f03e0ffffc1f01d89fcc
  | 3 => 0x3fff03fffffffffffc003ff03fffffffe0e3ff
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x848a1008c489082014b14a114a2129540b2e15
  | 2 => 0x9526299143922ae58155168d96e51a0cd896cc
  | 3 => 0x22144aa20924614aa80825a4254a54a960c16a
  | 4 => 0x3458b34492074db34e6d810939b38831bd03b0
  | 5 => 0x3860c3871c3871dc738e39ce01c210c1f6f800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37197
namespace PEqualNP.Outside.L_meta_37197
open PEqualNP.Outside.L_meta_37197.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x20df32dd32
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (34+((h/1+packedAt s2K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfe07fffffffffe07ff03ff03fffffffcc78fff
  | 1 => 0x7ff80fc07ffc0ff83ffc1ffc1f07fe0378f27c
  | 3 => 0x7fffffff81ffffffc0001ffffff83fff80ff8f
  | 4 => 0x80000ffffe000fffffffe0001fffc003ff03f0
  | 5 => 0xfffff00000000fffffffffffe0000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x290a449104904014b412541250c62a84384b5
  | 1 => 0x143264872491565815550b550b46b41958b25c
  | 3 => 0x584149120d224aaa8092129a52d21953805b0a
  | 4 => 0x51658a24483a6b34e69a40921ce31063ad03e0
  | 5 => 0x61860c3871c38dc738e39ce380842182f6ec00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeee00aa88aa00eeeeee00aa88aa00eeeeee00aa88aa00eeeeee00aa88aa00eeeeee00aa88aa00eeeeee00aa88aa00eeeeee00aa88aa00eeeeee00aa88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37197
namespace PEqualNP.Outside.L_meta_37197
open PEqualNP.Outside.L_meta_37197.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x8df32dd32
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (34+((h/1+packedAt s3K4 (32+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfe03ffc07ffc0e0fff07ff07ff07fe01c79e7c
  | 1 => 0x7ffc0ffffffffff03ff81ff81ffffffe78e3ff
  | 2 => 0x7fffffff81ffffffc0001ffffff83fff80ff8f
  | 4 => 0x80000ffffe000fffffffe0001fffc003ff03f0
  | 5 => 0xfffff00000000fffffffffffe0000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1298644714495602cb42a742a7467218c38e3c
  | 1 => 0x429248920910450154a094a090ca4a858a0d5
  | 2 => 0x585089120d224aa540849294d2d2195380570a
  | 4 => 0x5162ca24483a6b39a694c0849ce31063ad03e0
  | 5 => 0x61830c3871c38dce38e71ce70084218376f800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeee0e0c8c8c0c0eeeee0e0c8c8c0c0eeeee0e0c8c8c0c0eeeee0e0c8c8c0c0eeeee0e0c8c8c0c0eeeee0e0c8c8c0c0eeeee0e0c8c8c0c0eeeee0e0c8c8c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37197
namespace PEqualNP.Outside.L_meta_37197
open PEqualNP.Outside.L_meta_37197.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2126119001801d2000b95102a3cb06127071b020129e16895a72815c2d480de35001d63330f8fb76035fb65ee5a1722a40190420000000130000c519d00f5d8a5068012000a08203000000128082010aa804400c0105bda8287785050edca421db54843bba8a85745150abca6215754c429faa2653c544caeea2995d14532bda826578504ca7ca8194f55032b7a92836c52506f4a020de540419f2a6633d54cc6dca598db54b319f2a4633d548c6f4a118de542319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502eca2205d544409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f209f2a4413d54882eca3105d546209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (731+((h/13+packedAt s4K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s4K4 (1875+((h/21+packedAt s4K4 (1728+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 1 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 2 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 3 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x309118a290425014a849d0930194d21886315c
  | 1 => 0x52922864129212816942528510a154a8b284c5
  | 2 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 3 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37197
namespace PEqualNP.Outside.L_meta_37197
open PEqualNP.Outside.L_meta_37197.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1c813be00140825a4dfa622e5b190034aba0600000700003560b0c3434480007801dab0050b176eb928a467d4a13a40209626c00b00cc01e001800c00000225e0151c50c83a41e2003d05040818f003808100042802c000040c08400bda8287785050eeca221dd54443bba8a85745150af4a0215e540429f2a6653d54ccaeca3995d547329f2a4653d548caf4a1195e54232b7a92836c52506bca620d754c419faa2633c544c6dea498db14931bda826378504c67ca818cf550319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502dca4205b548409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309faa2413c54482bea6905714d20bba8a4174514827ca8104f550209f2a6213d54c42bca7885754f109f2a4213d54842dca5085b54a10
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (718+((h/13+packedAt s5K5 (640+(h % 13)*6) 6) % 49)*7) 7
  | 4 => packedAt s5K4 (1875+((h/21+packedAt s5K4 (1728+(h % 21)*7) 7) % 84)*7) 7
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307c1fffc1ff0ffffe011e73fc
  | 1 => 0xfffffc0fc1ffff801f07fffff0f01ffe13fccf
  | 2 => 0xf83ffff001ffffffe007fe0fff001fffe38f0f
  | 3 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 4 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x309118a2904250150549d0930914d21906315c
  | 1 => 0x51222864229422820b82632590a144aa10d4c5
  | 2 => 0xa29451019522152d2044948a2a029951630b0a
  | 3 => 0xc52882492034a9ca5290210cc4cb0062b80ea0
  | 4 => 0x630e38e39c73e739ce739c0888c1183dfe000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37197
namespace PEqualNP.Outside.L_meta_37197
open PEqualNP.Outside.L_meta_37197.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001027fd5007fe54007f55007fc54027fd4c01fe53007f54c09fc5301ffd0c01fe43007f50c07fc43027fd4801fe52007f54809fc5201ffd0801fe42007f50807fc42007fcc801fe32007f4c801fc32027fd4405fe51007f54405fc5101ffd0405fe41007f50405fc41007fcc405fe31007f4c405fc31007fc8405fe21007f48405fc21027fd4003fe50007f54003fc5001ffd0003fe40007f50003fc40007fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x64001ffcc32000ffc6190007fd30c8003fe1864001ff8832000fdc4190007fa20c8003fe1064001fb0832000ffe2190007fe10c8003fe0864000ffd9520005feca9002ffe65480097f32a4000ff59520005faca9002ffc65480097e32a4000ffd9120005fec89002bfe64480077f3224000ff59120005fac89002bfc64480077e322400bffd5120057fca890003fd5448015fe2a24000ffd8d20005fec690003fe63480117f31a4000ff58d20005fac690003fc63480117e31a400bffd4d20007fca690003fd5348017fe29a400affd0d20007fc8690003fd4348015fe21a4001bfd892005ffea49001ffe5248001fea924007ff14920057fe849001ffe4248001f72124000ff50920007da849001ffc4248001ff9924007ff8c920007dc6490003fd3248001f69924007ff0c920007fec290002ff6148013ff30a4002bf98520007fac290027fc61480057e30a400bffd452004ffca290003fd5148013fe28a400affd052004ffc8290003fd4148013fe20a4000ffcc52004ffc6290003fd3148013fe18a4007ffc852004ffc4290003fd214800ffe10a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe409001ffb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fa1048003fe0824000ffd9510005feca880037f65440013fb2a2006ff99510025fcca88003fd65440017eb2a2006ff19510025f8ca880037c65440093e32a2000ffd9110005fec888017fe64440077f3222000ff59110005fac888017fc64440077e3222006ffd511002ffca888003fd544400bfe2a22000ffd8d10005fec688003fe63440117f31a2000ff58d10005fac688003fc63440117e31a2006ffd4d10007fca688003fd534400dfe29a2005ffd0d10007fc8688003fd434400bfe21a2000ffd8910005fec488003fe624400f7f3122000ff58910005fac488003fc624400f7e3122006ffd4910007fca488003fd524400dfe2922005ffd0910007fc8488003fd424400bfe2122000ffcc910007fc6488003fd3244001fe1922001bfd8510017fea28800bfe5144005fb28a2002ff54510007eaa28800bfc5144005ffa0a2002ff90510017fa828800bfc4144005ff98a2002ff8c510017ec628800bfd3144001fa98a2002ff0c510017fe428800bfe2144005fe90a2002ff0851000dfec088007ff5044003ff2822001fe9411000ffaa088003f95044003fe2822001ffd011000ffc8088007fd4044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3ff61cc011ff30e6002bf98730047fac398002fd61cc011fe30e6002bf187300a7fea39804bfe51cc001fea8e6012ff1473009ffe839804bfe41cc001fea0e6012ff10730047fe6398023fe31cc011fe98e6008ff0c730007fe439804bfe21cc001fe90e6012ff0873000dfac198007ff50cc003ff2866001ff5433000ff8a198007ff40cc003ff2066001ff5033000ff88198007fe30cc003ef1866001fe8c33000ff86198007dc30cc003ff1066001ff0833000ffe2198007fe10cc003fe0866000ffd9530005feca98047fe654c0097f32a6000ff59530005faca98047fc654c0097e32a6000ffd9130005fec898043fe644c0077f3226000ff59130005fac898043fc644c0077e3226011ffd5130087fca898003fd544c021fe2a26001bfd8d3008ffea698023fe534c001fea9a6008ff14d30087fe8698023fe434c001fea1a6008ff10d30007fec498002ff624c001ff3126000ff58930007f8c49801efc624c023ffa926000ff94930007faa498047fc524c021ffa126000ff90930007fa8498043fc424c011ff9926000ff8c930007fa6498023fc324c001ffb0a6000bfd853007ffcc29800afe614c001feb0a600fff18530015f8c298047ff514c01fff28a6000ff5453007ff8a298043ff414c01fff20a6000ff5053007ff88298023ff314c01fff18a6000ff4c530047f86298003ff214c01fff10a6000ff4853007ff84298006ff604c003ffa826001ff9413000ffaa098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9826008fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007fe204c003fe1026001ffc413000ffc2098007fc104c00fffb2e4007bfd972003ffccb90012fe65c800fbf32e40049f9972003ffacb90002fd65c800fbeb2e40009f5972003ff8cb9001efc65c800fffb264007bfd932003ffcc99000efe64c800ffeb264000bf5932003ff8c99001efc64c801dffaa6400dff95320007faa990037fc54c800fffb1e4007bfd8f2003ffcc790022fe63c800ffeb1e4000bf58f2003ff8c79001efc63c801dffa9e4000ff94f20007faa79003bfc53c801bffa1e4000ff90f20007fa8790037fc43c80037f3164007ffd4b2003ffca59001ffd52c800ffe2964007ffd0b2003ffc859001fee42c800ffea164000fb50b2003ff8859001fff32c800fff1964007fb8cb2003ffa6590003ed32c800ffe1964007ffd872003ffcc39000afe61c800ffeb0e4000bf5872003ff8c39000afc61c801dffa8e400cff94720007faa390033fc51c801bffa0e400cff90720007fa8390033fc41c8001ff98e400cff8c720007fa6390033fc31c800fff90e4007ff8872003ffa439001ffc21c80037eb064001ffd432000ffca190007fd50c8003fe2864001ffd032000ffc8190007fd40c8003fe2
  | 2 => 0x5001df8c8a8013ff5454009ff2a2a004ff55150027f8a8a8003ff63540017fb1aa000ff98d50007fac6a8003fc63540117e31aa004ffd4d50026fea6a8013fe5354009fea9aa000df54d50027f8a6a8063ff4354001ff21aa000ff50d500c7f886a8003ff62540017fb12a000ff98950007fac4a8003fc625400f7e312a004ffd4950027fca4a8013fd5254009fe292a018ffd0950007fc84a8003fd4254031fe212a000ffcc950007fc64a8003fd3254001fe192a000ffd8550005fec2a805ffe61540057f30aa000ff585500bff8c2a800afc6154009ffa8aa004dfd4550027fca2a8013fd5154001bea8aa004ff145500c7fe82a805ffe4154001fea0aa017ff10550007fe62a805ffe3154001fe98aa017ff0c550007fe42a805ffe2154001fe90aa017ff0855000dfec0a8007ff5054009fda82a001ff9415000efca0a8007fc5054003be282a001fe1415000ffe80a8007fe4054003fe202a001ff8c15000ff860a8007fe2054003fe102a001ffc415000ffc20a8007fa1054003fe082a000ffd9540005fecaa005bfe65500097f32a8000ff59540005facaa005bfc65500097e32a8001bfd914001ffea8a000ffe5450007feaa28003ff15140007fec6a0002ff6350001ff31a8000ff58d40007f8c6a0022fc635002dffa9a8000ff94d40007faa6a005bfc5350007ffa1a8003efd0d4001ffc86a000ffd4350001dea1a8003ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a001efc625002dffa928000ff94940007faa4a005bfc5250007ffa128003efd094001ffc84a000ffd4250001dea128003ff10940007fe64a0003fe3250001fe9928000ff0c940007fec2a0002ff615002bff30a8002bf98540007fac2a0057fc61500057e30a8016ffd45400affca2a0003fd515002bfe28a8003ffd054001ffc82a000ffd4150007fe20a8000ffcc5400affc62a0003fd315002bfe18a8000ffc85400affc42a0003fd215002bfe10a8001bfd814000ffea0a0007fe5050003fea828001ff1414000ffe80a000ffb4050003ff2028001ef9014000ff880a0007bc4050003fc2028001ff8c14000ff860a0007fe2050003fe1028001ffc414000ffc20a0007fc1050011ffb2e6008bfd9730047fccb98012fe65cc011feb2e6000bf59730047f8cb98022fc65cc011ffb266008bfd9330047fcc99800efe64cc011feb266000bf59330047f8c998022fc64cc029ffaa66013ff95330007faa99804ffc54cc0037f31e6008ffd4f30047fca798023fd53cc011fe29e6008ffd0f30047fc8798023fd43cc011fe21e6008ffd8b30047fcc59801efe62cc011feb166000bf58b30047f8c598053ff52cc001ff2966000ff54b300a7f8a59804fff42cc001ff2166000ff50b3009ff88598023ff32cc011ff1966008ff4cb30047f8659802
  | 3 => 0xfb0a6202ffd4531017fca29880bfd514c405fe28a6202ffd0531017fc829880bfd414c405fe20a6202ffcc531047ee629880bfe314c405ef18a6202ff0c531017b8629880bf4314c405ff10a6202ff08531007fec098802ff604c43fff3026201bf98131007fac09887ffc604c4037e3026221ffd41310fffca09887ffc504c441ffa02621fff901310fff8809887ffe304c411fe182621fff881310fff8409880bff104c405fb8826202ff84131017f8209881fff65c840f7fb2e4207ff99721025fccb9081ffd65c84017eb2e4207ff1972103df8cb9081fff64c840f7fb264207ff9932101dfcc99081ffd64c84017eb264207ff1932103df8c99087bff54c843bff2a64200ff553210eff8a99081fff63c840f7fb1e4207ff98f21045fcc79081ffd63c84017eb1e4207ff18f2103df8c79087bff53c8401ff29e4200ff54f210f7f8a790877ff43c8401ff21e4200ff50f210eff8879080afe62c840fffa964207ff94b2103ffaa59081ffc52c840fffa164207ff90b2103ffa859081ffc42c840fff9964207ff8cb2103ffa659081ffc32c84057eb0e4202ffd4721017fca39080bfd51c8405fe28e4202ffd0721017fc839080bfd41c8405fe20e4202ffcc721017fc639080bfd31c8405fe18e4202ff88721017dc439080bf621c8405fe10e4202fb0872103ffec19081ffe60c84037f3064207ff58321005fac19081ffc60c84037e306421effd43210e7fca190873fc50c843bffa06421cff903210e7f88190873fe30c8439fe1864207ff8832103ff8419080bff10c8405ff0864202ff04321007feca90802ff6548437ff32a4204bf99521007faca90802fd6548437fe32a4204bf19521007fec890802ff6448435ff3224203bf99121007fac890802fd6448435fe3224203bf191210dffea89086bfe5448401feaa2421aff15121007fec690802ff6348401ff31a4208bf98d21007fac690802fd6348401fe31a4208bf18d210dffea690803fe5348401fea9a421bff14d210d7fe8690803fe4348401fea1a421aff10d21015fec49086fff524840fff2924200ff5492103ff8a49086bff424840fff2124200ff5092103ff88490803ff324840fff1924200ff4c92103ff8649080aff6148405ffa8a4202ff94521017faa29080bfc5148405ffa0a4202ff90521017fa829080bfc4148405ff98a4202ff8c521017fa629080bfc3148405ff90a4207fdc8521017fc429080bee2148405fe10a4202fb08521017e84290803ff60484017fb024219ff9812100dfcc090803fd6048433fe3024201bf181210dffea090867fe5048433fe282421affd01210cffc8090867fc4048433ff1824219ff0c1210cffc409081ffc2048405ff8824202ff84121017f82090806ff6554001ffb22a000bfd91500c7fcc8a800efe6454001feb22a018ff191
  | 4 => 0x89bfc65504097e32a8202bfd914101ffea8a080ffe5450407feaa28203ff15141007fec6a0802ff6350401ff31a8200ff58d41007f8c6a0822fc635044dffa9a8200ff94d41007faa6a089bfc5350407ffa1a8203efd0d4101ffc86a080ffd4350401dea1a8203ff10d41007fec4a0802ff6250401ff3128200ff58941007f8c4a081efc625044dffa928200ff94941007faa4a089bfc5250407ffa128203efd094101ffc84a080ffd4250401dea128203ff10941007fe64a0803fe3250401fe9928200ff0c941015fec2a080bff5150405ff28a8202ff54541017f8a2a080bff4150407fba0a8202ff905410177c82a080bfc4150405de20a8202fd10541017fc62a080bfc3150405ff10a8202ff08541007fec0a0802ff605044bff3028201bf98141007fac0a0897fc60504037e3028226ffd414112ffca0a0897fc5050407ffa028203ff9014101ff880a0897fe305044bfe1828225ff8814112ff840a080bff1050405ff0828202ff04141047fecb98822ff65cc411ff32e6204bf99731046fccb988127e65cc411feb2e6200bf59731046facb988027d65cc411fe32e6208bf19731047fec998822ff64cc411ff3266203bf99331047fac998802fd64cc411fe3266208bf19331127fea99888ffe54cc401feaa66223ff15331015fcc798823ff53cc411ff29e6208ff54f31047f8a798823ff43cc411ff21e6208f790f31047fa8798803dd43cc411fe21e6208ffd8b31047fcc59881efe62cc411feb166200bf58b31047f8c598893ff52cc401ff2966200ff54b31127f8a59888fff42cc401ff2166200ff50b3111ff88598823ff32cc411ef9966208ff8cb31047fa6598803dd32cc411fe1966202bf58731017fea39880bfe51cc405fea8e6202ff14731017fe839880bfe41cc405fea0e6202ff10731017fc639880bde31cc405fb18e6202ff0c731017b8639880bfe21cc405fe10e6208ffd8331047fcc198806fe60cc411feb066200bf58331047f8c198806fc60cc449ffa866222ff94331117f8a19888fff40cc445ff2066222ff10331047fc6198823fc30cc445ff1066222ff08331017fe219880bfe10cc405fe0866200ffd9531005feca98887fe654c4097f32a6200ff59531005faca98887fc654c4097e32a6200ffd9131005fec898883fe644c4077f3226200ff59131005fac898883fc644c4077e3226221ffd5131107fca898803fd544c441fe2a26202bfd8d3110ffea698823fe534c401fea9a6208ff14d31107fe8698823fe434c401ef21a6200ff50d31007ba8698823fc434c401ffb126200bfd8931007fcc498803fd624c401fe3126207bf1893110ffea498803fe524c401fea926221ff14931107fe8498803fe424c401fea126220ff10931047fe6498803df324c401ff1926200ff4c931007ba6498823fc324c4057
  | 5 => 0x493203ff8a4990bfff424c80fff2126400ff5093203ff88499023ff324c811f79926407ff8c93203fbc6499003ff614c8017fb0a642eff98532015fcc299003fd614c85dfe30a6402bf18532187fea2990bbfe514c85dfe28a642fffd0532177fc82990bbfc414c85dff18a6408ff0c532177fc429901ffc214c801ffb026400bfd813216ffcc099006fe604c801feb02642dff1813200df8c0990c3ff504c85bff282642dff1413217ffe80990b7fe404c85bfe202642dff8c132047f860990b7fe204c80ffe102642effc413216ffc20990b7fc104c80fffb286407bfd943203ffcca19012fe650c80fbf32864049f9943203ffaca19002fd650c80fbeb2864009f5943203ff8ca1901efc650c80fffb206407bfd903203ffcc81900efe640c80ffeb206400bf5903203ff8c81901efc640c859ffaa0642bff95032007faa8190affc540c8117f3186408ffd4c32047fca619023fd530c811fe2986408ffd0c32047fc8619023fd430c811fe2186407bf9883203ffea41901ffe520c80ffea906407ff1483203ffe841901ffe420c80ffea106407ff1083203ffe641901fdf320c80fff1906407fb8c83203ffa641901fdd320c811f69906407ffd843203ffcc21900afe610c80ffeb086400bf5843203ff8c21900afc610c859ffa88642aff94432157f8a2190afff410c855ff208642aff10432047fc6219023fc310c80fff1086407ff0843203ffec01901ffe600c8037f3006407ff58032005fac01901ffc600c8037e300642cffd403214ffca0190a7fc500c857ffa006429ff9003214ff88019023fe300c811fe1806407ff8803203ff840190abff100c853ff0806429ff04032015fecaa8803ff64544017fb22a228ff9915101dfcc8a8803fd6454451fe322a203bf19151027fea8a8813fe5454409feaa2a204ff15151007fec6a8802ff6354401ff31aa200ff58d51007f8c6a8822fc6354409ffa9aa204ff94d51027faa6a8813fc5354451ffa1aa200ff90d51007fa86a88a3fc4354401ffb12a200bfd8951007fcc4a8803fd6254401fe312a207bf18951027fea4a88137f5254409ff292a204ff54951006faa4a8813fc5254451ffa12a200ff90951007fa84a88a3fc4254401ff992a200ff8c951007fa64a8803fc32544057fb0aa202ffd4551027eea2a880bfe5154405bf28aa202ff14551016f8a2a880bf45154405ffa0aa202ff90551017f882a880bfe3154405fe18aa202ff88551017f842a8803ff60544017fb02a227ff9815100dfcc0a8803fd605444ffe302a201bf18151027fea0a88137f5054409ff282a204ff14151147fe80a889ffe405444ffe202a227ff8c15113ff860a889ffe205444ffe102a202ffc4151017ee20a880bfe1054405fe082a200ffd9541005fecaa089bfe65504097f32a8200ff59541005facaa0
  | 6 => 0x7ffa8a843aff945421d7f8a2a100fff4150807dfa0a8403ff9054201ff882a10ebfe3150875fe18a843aff8854203ff842a1003ff60508017fb028439ff9814200dfcc0a1003fd6050873fe3028401bf181421dffea0a10e7fe5050873fe2828403ffd014201f7e80a100ffe4050807fe2028439ff8c1421cff860a10e7fe205080ffe102843affc41421cffc20a10e7fc1050811ffb2e6408bfd9732047fccb99012fe65cc811feb2e6400bf59732047f8cb99022fc65cc811ffb266408bfd9332047fcc99900efe64cc811df3266403af99332047fac999002fd64cc811deb266400af59332047f8c999022fc64cc871ffaa66437ff95332007faa9990dffc54cc811ffa9e6408ff94f32047faa799023fc53cc811ffa1e6408ff90f32047fa8799023fc43cc871ffa966407ff94b32007faa59901ffc52cc86fffa166407ff90b32007fa859901ffc42cc811ffb0e6408ff98732015fcc399023fd61cc8017eb0e6408ff18732015f8c3990e3ff51cc86dff28e6436ff147321bffe83990dbfe41cc86dfe20e6408ff8c732047f863990dbfe21cc80ffe10e6408ffd8332047fcc199006fe60cc811feb066400bf58332047f8c199006fc60cc871ffa866435ff943321aff8a1990dfff40cc86bff2066435ff10332047fc6199023fc30cc86bff1066407ff083321b7fe21990d7fe10cc86bfe0866407ffd963203dfecb1901ffe658c8097f32c6407ff59632005facb1901ffc658c80f7e32c6407ffd923203dfec91901ffe648c8077f3246407ef9923201d7cc91901ffd648c8017eb246407ef592320057ac91901ffc648c80f7e3246434ffd523219ffca919003fd548c867fe2a46400bf58e321a7fea719023fe538c801fea9c6408ff14e3219ffe8719023fe438c801fea1c6408ff10e3203dfcc51901fff528c80fff2946407ff54a3203ff8a51901fff428c80fff2146407ff50a3203ff8851901fff328c80fef9946408fbcca3203ffec31901ffe618c8057f30c6407ff58632005fac31901ffc618c8057e30c6434ffd4632197fca3190cbfc518c867ffa0c6432ff90632197f883190cbfe318c811fe18c6407ff8863203ff8431901fff608c80fff3046401bf9823203ffac119002fd608c80ffe3046401bf182321a7fea1190c7fe508c863fe2846433ffd023218ffc81190c7fc408c863ff1846408ff0c23203ffc411901ffc208c865ff8846431ff8423218ff82119003ff654c8017fb2a6430ff99532025fcca99003fd654c8017eb2a6430ff19532025f8ca99003ff644c8017fb22642fff9913201dfcc899003fd644c8017eb22642fff1913201df8c8990c3ff544c85fff2a26400ff5513217ff8a8990c3ff534c811ff29a6400ff54d32047f8a6990bfff434c811ff21a6400ff50d32047f886990c3ff524c80fff2926400ff5
  | 7 => 0x2901ffe60948037f304a407ff58252005fac12901ffc60948037e304a404ffd4252027fca129013fc5094889ffa04a442ff90252217f8812910bfe3094885fe184a407ff8825203ff8412910fff1094885ff084a442ff0425203dfecaa9003ff64548017fb22a441ff9915201dfcc8a9003fd6454883fe322a403bf19152027fea8a9013fe5454809feaa2a404ff15152007fec6a9002ff6354801ff31aa400ff58d52007f8c6a9022fc6354809ffa9aa404dfd4d52027fca6a9013fd5354801bea9aa404ff14d5220ffe86a9003fe4354801fea1aa441ff10d52025fec4a9013ff5254809f7a92a407ff9495203efca4a901ffc525480fbe292a404fb1495220ffe84a901ffc4254801ffb0aa400bfd8552207fcc2a900afe6154801feb0aa440ff18552015f8c2a9013ff5154809bfa8aa404ff94552027f8a2a9107ff4154881ff20aa440ff10552207fc62a9103fc3154881ff10aa407ff08552007fec0a9002ff605487fff302a401bf98152007fac0a90fffc60548037e302a404ffd4152027fca0a90ff7e5054809fe282a404df1415220ffe80a90fffe405487ffe202a43fff8c1521fff860a90fffe205480ffe102a440ffc41521fffc20a90fffc105480fffb2c8407bfd964203ffccb21012fe659080ffeb2c8400bf5964203ff8cb2101efc65908077eb248403ffd524201ffca92100ffd5490807fe2a48407ffd8e4203ffcc721022fe639080ffeb1c8400bf58e4203ff8c7210fbff5390801ff29c8400ff54e421f7f8a72100fff4390807dfa1c8403ff90e4201ffa8721003bd4390807fe21c8407bf98a4203ffea52101ffe529080ffea948407ff14a4203ffe852101fbf4290807f7a148407ff10a4203fd8852101fff619080fff30c8402bf9864203ffac321002fd619080ffe30c8402bf186421f7fea3210f7fe519087bfe28c8403ffd064201ffc832100ffc419087bff18c843dff0c64203ffc432101ffc219080fffb048407ff9824200dfcc12101ffd60908017eb048407ff1824200df8c1210fbff5090879ff284843cff1424201ffe812100ffe4090807fe204843cff8c2421e7f8612101ffe209080ffe104843dffc42421e7fc21210f3fc1090801ffb2a8400bfd95421dffccaa1012fe6550801feb2a8400bf595421dff8caa1012fc655080f7fb228403ffd514201ffca8a100ffd5450807fe2a28400ffd8d42005fec6a1003fe6350801feb1a8400ff18d42045f8c6a10efff5350801ff29a8400ff54d421dff8a6a100fff4350807ff21a8400ef90d4201ffa86a100ffc4350807de21a8403bfd89421dffea4a101ffe5250801fea928407ff1494201ffe84a100fef425080fff2128407ef9094203ff884a101fbc4250807f62128400ffd8542005fec2a10ebfe61508057f30a8400ff585421d7f8c2a100afc615087
  | 8 => 0xf0c553267fc42a9933fc2154c01ffb02a600bfd815325ffcc0a9806fe6054c01feb02a64bff1815300df8c0a9813ff5054c09bfa82a604ff94153027f8a0a9937ff4054c97ff202a64bff1015325ffc60a9823fc3054c97ff102a64bff08153267fe20a992ffe1054c97fe082a608ffd9643045fecb21823fe6590c097f32c8608ff59643005facb21823fc6590c117e32c8603bf5924301ffea92180ffe5490c07feaa48603ff15243045fcc721823ff5390c11ff29c8608ff54e43047f8a721823ff4390c11dfa1c8603f7d0e43047f88721823dc4390c11ffb148608ff98a4303dfcc521823fd6290c017eb148608ff18a43257fea52192bfc5290c07ffa148603efd0a4301ff88521823ff6190c11ff30c8602bf98643047fac321802fd6190c11fe30c8602bf18643257fea321927fe5190c93fe28c8603ffd064301ffc832180ffc4190c11ff18c8608ff0c64324ffc4321927fc2190c11ffb048608ff9824300dfcc121823fd6090c017eb048608ff1824300df8c12192bff5090c91ff2848648ff1424301ffe812180ffe4090c07fe2048608ff8c243047f86121923fe2090c91fe1048649ffc4243247fc2121923fc1090c01ffb2a8600bfd954323ffccaa1812fe6550c01feb2a8600bf5954323ff8caa1812fc6550c117fb228603ffd514301ffca8a180ffd5450c07fe2a28603bfd8d4323ffea6a1823fe5350c01fea9a8608ff14d4301ffe86a180fdf4350c11ff21a8608ef90d43047f886a1823bc4350c07ee21a8600ffd8943005fec4a1803fe6250c01feb128600ff1894303df8c4a191fff5250c8ffe2928603ffd094301ff884a180fbc4250c01ffb0a8600bfd8543237fcc2a180afe6150c01feb0a8646ff18543015f8c2a191fff5150c8dff28a8646ff1454301ffe82a180fbf4150c07ff20a8603ff10543237fc62a1823fc3150c8dff10a8646ff08543007fec0a1802ff6050c8bff3028601bf98143007fac0a1917fc6050c037e3028647ffd414322ffca0a1917fc5050c07ffa028603efd014301ffc80a180ffc4050c8bff1828608ff0c14322ffc40a1917fc2050c8dff8828645ff8414322ff820a1812fd659480fffb24a407ff9925201dfcc92901ffd64948017eb24a407ff1925203df8c929013ff5494809ff2a4a404ff55252027f8a92901fff639480fff31ca408bf98e5203ffac729002fd639480ffe31ca404ffd4e52027fca729013fd5394809fe29ca444ffd0e52007fc8729003fd4394889fe21ca407bf98a5203ffea52901f7f5294809f7a94a407ff14a5203fd8a52901fff429480ffe214a407ffd865203ffcc32900afe619480ffeb0ca400bf5865203ff8c32900afc6194809ffa8ca404ff94652027f8a329113ff4194887ff20ca443ff1065221ffc632910ffc319480fff10ca407ff0865203ffec1
  | 9 => 0x701500a00001600100600900000400500400800a00000100000700000000100000f00000c00300800600600101000000300300800d00100b00000200200500600000200400100100a02500100000d00000700600000100600000502300200000a00500001300500000000e00300200400100101600000000300100500500200300400000100a00200d00000a00200100300400400400400500000100000200500400000200100a00000100200300a01dfecaaa00eff6455007ffaa2a804efd515401ffca8aa00f7e5455007fe2a2a803df1515401f78a8aa003ff63550017fb1aa800ff98d54007fac6aa003fc63550117e31aa804ffd4d54027f8a6aa00fff4355007fe21aa800ffd8954005fec4aa003fe6255001feb12a800ff1895403df8c4aa013ff5255009fe292a803ffd095401ff884aa003ff61550017fb0aa852ff98554015fcc2aa003fd61550a5fe30aa802bf18554027fea2aa013fe5155009fe28aa803ffd055401ffc82aa00ffc41550a5ff18aa852ff0c554297fc42aa14bfc2155001ffb02a800bfd815428ffcc0aa006fe6055001feb02a851ff1815400df8c0aa013ff5055009ff282a804ff1415401ffe80aa00ffe4055007fe202a851ff8c15428ff860aa147fe20550a3fe102a852ffc415428ffc20aa147fc10550097eb2ca608ffd9253047fcc92980efe6494c11feb24a600bf59253047f8c929822fc6494c09ffaa4a604ff95253027faa929813fc5494c117f31ca608ffd4e53046fea729813df5394c09afa9ca608ff14e53047b8a729823ff4394c11fe21ca608ffd8a53047fcc52981efe6294c11feb14a600bf58a53047f8c529813ff5294c09fe294a650ffd0a53287f88529823ff6194c11ff30ca602bf98653047fac329802fd6194c11fe30ca602bf18653027fea329813fe5194c09fe28ca650ffd065327ffc832993ffc4194c11ff18ca608ff0c65327ffc432993ffc2194c11ffb04a608ff9825300dfcc129823fd6094c017eb04a608ff1825300df8c129813ff5094c09ff284a604ff14253287fe812993bfe4094c9dfe204a608ff8c253047f8612993bfe2094c9dfe104a64fffc4253277fc212993bfc1094c117fb2aa600ffd9153005fec8a9937fe6454c077f322a600ff5915326ff8c8a980efc6454c09ffaa2a604ff95153027faa8a9813fc5454c097fb1aa604ffd4d53027bea6a9823fe5354c11bf29aa608ff14d53046f8a6a9813dc5354c9bffa1aa608ff10d53007fec4a9802ff6254c01ff312a600ff58953007f8c4a981efc6254c09ffa92a604dfd4953027f8a4a9937ff4254c9bfe212a600ffd8553005fec2a9933fe6154c057f30aa600ff58553267f8c2a980afc6154c09ffa8aa604ff94553266fca2a9813fc5154c09be28aa64dffd0553267fc82a9933fc4154c99ff18aa608f
  | 10 => 0x66314f1af00006b93d3a1d101600016000000000000000e3907a1c710400003ba00000000000260000000bc8000000000000000000017ba100000171365210400023e0000000000000000000000003323f000000000020e80000001763ec000019c00000007a800076f00019d508800000300000400000300400c00100000003000000100c00300100000600500700700501200202100500000100000f02100000300000000002700700000300000000001a00300200100b00100000e00500600000100000000200300000400400000e00200500400000200800c00800300100500000001400900000200000000f00100200200000500000000100000600900500300000b00000000100700000400301900700000701300000000000600000000000000000400200b00701b00100000200200000000f00500d00300200000100100500001e00000000400102c00000000f00300000700101400000000000000000500d00400000300301700300e00300000200100100000000000300000000e00900000700101100e00000b00900f00001600000000000000900100100000000500600900a00100200200000000600200000100000100002000000100101100200100000600000900100500000300000000000400200300b00000100100100500300301400800300000102301900200500100200501200700500303400000400900000a00c00a00000100400300300600100100000800000a00001400000400300500100100000100100200000000301b00500000100100200a00600100200100400300000700000e00300000400f00000100b00100000100300200300100400400601500600b00800600000800000100300800200100200100000100300300400300d00b00700000300500900000000000000000600500100000a00000400500900401001000200700201101100100100300000000000000500000b00100001600400500800300100b00000300300a00000000000100400100800600000700100200200000000100a00200100400d01600000000200700100000300700f00f00000000000600300100500001400a00300600200000600e00300000000100300300100c00000600200300000500600000500500401100c01200a00300000200000000100200000000200000100800000200500900200100000200100f00200300700200400300000000000200400100900200300900200000000500002600100800100100200000300400000001100000000100200000300800000000100100000500100800400100000401f00000000000001a01900000000900101e00000400000100000300000800300200200100000000100300800601900000500000b00000000600b00100000000200000300000e00400700200100300100000a00
  | 11 => 0xf19184a462c0252e09c3c0720843ab982cbce2553b89200f0c80c174908c11c0a40a806000004d02800d542086571f01788fd4195000161cba00002ac1b1009a0002e20eb4c4609f0ff90f87725dc22b167011e31735d8d1ca8a62227712948780000001f1800000000000000000000df80000002c10000260fd013d00021fc9a280400014e4e720000000f4c0000000000f703f205f00019f80000003f980001ea7ca0dd8e200000002611070f3200035f87809b855719e0a7c00025e00002f8a2c6ac00021e82de8592790d7000063729b8000bd600032e07140006ee0000e78a347311e69d780000002198d385c0000380084503061d1501f3c43a86d238157cc625a32261e5c7b282f24f0000b240001579148a901490561abc00086a3d000000003b80000f08b480000000b1061e2a63ba9a94d920fb07c9a0000037e000000035e000000000000066c2d3899805e15b3090c4800067b1190f1cc2a00019f00003e80c01b88228000000000000000000016521f000000000008d0b300232ca05a000000000000000001914151d807186431c501a8d900001571b34ee824f29a8000000000242a1e451857f0000000c4e27d03c85382ae2b23328bf40f06291d49590dae0000ba800032444400005d00000000001c9046e417307016c74a3f7174049cc568131bd15c49346711d519dcc061b220c013c8225290001ecc88424e015866c0003a8000000000082806f0000f6838126480000000000000000c0e6cf3db8f28c943b01398000c3041e21381d80000432910aa80005b7326800037c39539f9bd41d82210000d88000000182000047a0830000000a082d900005f4b940001e90188a0a71b2f00bcc47443d41995e800000037d1cb000000019c0000e9a742000000023000000005aca1026e0001a3cc421733cf214800000000000000000000000fd800000011aa1bc0002a90c60b2000078c018000000001200010fc0a40000530c900000b732c83cc0001060001894000856000000106a6e90000020e240002fe80002664ab34c19bc9d209104400006320c1000009000081e00019b4a4a0002459bdc4b44f60f7000015c7831c906841c032c08a992d0100000e91cf00004a210e02b4e207c81f88cac1346613448d9000000000000006ee3b43e100004302332c80e4000000000000000007db1f40c1c23475301f80006a217a27e80004de7ff06f84b80000000de00005627a52b680b06da0002f2000000084f28c067c4280ba0a597c0000406020a1b08a64072f885e0d6018f08099a470e0952df0ecc79e2e333e9d9ca5e40a16b97d017a000095127c8bc220054800064e00000000502a62782619b5441e6a7026000067600000000000006d12bf000057e75d43b80000000002d80b300006bd377a0187e069d14912080e858b25e800
  | 12 => 0x580000000ea1c082e074f1ca103828452c2fc8270bb282324699a87644291bd80000743e42638c782b20001f501540001e40e59c6007c0001941e4400000000000009c411400002a80000003798000a3655d424a0e800019d3a21f809c220c2358000d0c7063f79bac00005e0b29a381cc7052d30000d6a6580000ec4224565411167437a000000000000064e38089088d009000009200000000770c6056e2502a6a0d039057b1249ac87a025300000000006b438e84c89ac000373a120a9428829e0000000000126207000063e0000000e764ca2cd800000019015a00000004ce3c493746b61fc0001d000007ed12ca1a00004ea02580000006d30368000c027f100006645f063f2d68e44000000000079cc4c441000094400074323e1ae00381ca08e9c4cb640491db8000e3e2f932d2064a9806f00017fc17042e3228000f587fe0a40d6836e23c01304406f07f50bc8e8c59c0f73db0c6c41c1a63901c64a7c44604999305fe67803e0ba89c084d00003080001232f40000b9081f2009a987e65912af0ef825a7933041cf48405073548000e4c00000000006425bc000000000025c0a31e9814209b0b19efc00000000012910dc0000001cb40006130d00000000000345033c9ce0970000c200005cf2b600004da4d238580000002791121ddc4be0472e71df4fac15e3190ed80000003c51134f7c000260000051c1e62cb9394b262033729a2c1a60001859a7877e5de00003540000003760000000000266870836c00038480000007461eb215c12c7df3cc13100005b42871aa0d227640000fc88000db3b70b4c00000040a1924a840003780e3c00034b00010dca2000000000001ce67400000000000182330000c687dc3c800007765d60001e3cb960821818000b4000010500006dc29b000000089e3300590df4f9c00000000000002d20000000d320b539585dc0007fa3429f900007591ef8000a5a64800306600004720000b988ae5f30001e5400e1f70b3948c9c636f35885500002313fd8c7c60482e04f16bd0c20801af147489440923600000000fe0079c1c00000000000000002100aa8e14b7e73a439188102c47700e9ca900253430d00000000000001f144d25330001b5800087d00000000000c90fa83a81b80c723480005c239600000000004401580a44b2c0001dd175024a4b90001a5c1da74b10b1e102121880000a8d0a00003e0a12c0006c200000005200000e3118cfdc5b52169ab4cbe5d224c9040bf61d83168f7800017e257210c5966500c18f68d963a22b300000004fa000000000000000012bc0000000000000ce47883b516e4db41852901a547dc00000014c000000020f8f74db64b22c794ec7300000f09e38000000000212890e0b00000080ed60101970b1c0006de3c6800046c46230c90bc5a280524e1678f5627
  | 13 => 0x11806341e000021a80000005810be00003504b626996f40000000000bc0b5058000018cc32c53122703403fa6c53870b7063a69340888b87800480e19b8835602100000009e267c3e600002d282b36a0000000000000000000000039700008423331eb87c504c205000000053a00008f80d800000025e15d4f62027000000000083b12b000000000000007880000000000000312000349015000063c3a72090ca651c1a0a1980000001628000bca59a000000097e028216000045249800015f08105892f90e650f68380c20c400000003d9000010e34c40e80000000003b2800000046f22d9fac4d82772ae0000860000000000092c0002810618e6a8030a5185c7d67d02369ee10604e4115848402c00007591cc6c030c3820204b6257002b16b016c25b092140c4c837500018e86120000001a7c0007080000000a225d31420a0000005a1a29e047064280000a340004d926a0368f86283000199c1b251e2d58e5ca1280200012310841b921a1878000000000000014e2ed43a80007f652630791e4366000192904cb0c3893d49314c587280b680000d8638000158ca5441242e1d201943cb4318f88d42000378858019076800000000b017f156949c00049401100003d858400007a400000014d000028012830507b48443c100000000000000001dcc6860003178cd400000013d159c9d60000001d300e200034d03900001f02a18000526000000003400000e1aa00000001fe3d100000007140000a3cf780002b980000000000000000fae00000017b880872f0000000df8000000000000000000000007f40000000df0000449000000037000015e17bc0c813a35980000004050000000000562000124400010723e9be4ee48582869d8800080f00017d4f7653806291700000f22c118302b81662128dd88ba4ed2e8902c1d2077335a17c00001a0000904000000000000013206909a80007041e82301c5821e4b100001c800028a00019fc73e5c71a40e9907c53f06b02ac8563290870d7c0002c31cd94304022581b485880000000ce1d7c17e7e341f86e8ae874a1230cf42d85db18283e050e0fa2cf90500005ed36e9de00cc5ba1de081043c1aa00000dc55037032e898000078b3170000a2a15d42298590406f616d8d8c00085a000000000000000000008a80cb00493e403e2ec27a80a80003c31358000aa200027f80003020000ab0000aa46ba321000041a10a2eb8118fa42ac0f28d3c97011e00500000007e50309fe05d60453bf8a9cccc00000017e80ea55500012188e22fc23d86c40006e427e035ccc8350093000064400020791b85920002218724c5000000004d8000000391889450a595289014400000036714d81440001e4800000037300000006ae0000001f2c00000042f030c00000036300000004da09b90e833c7473049e
  | 14 => 0x92a13b0001f789de2700018000ffa0000e60000000000000000000023900000000006510001fa49d870300000d40ca76900006d10003d131a8000b924832c680b48485c00000b680000003511c541e200042a8710d6c0003ce1fd00001d60001f9c6880000728b183be0000518cd88e83ec3e39b4000000016c0f600622b5279876c26800038b800081a00041397e08aa0003d418a80004450c100ec00000000000000007a334e000000060206889500b800000004640002892538af8cb6000000145c00040c25801404760001011ec00006883300da87ea0c62c18348128600250a094f888393690c70db80002fb00000007663b609481e84d805c80a4eda61021501100000001d3850c91e81021c1cf8af00dd1391f6888e76331b00003a61ef0001bf4ea20000000000a5c84700016640005c200000000000004381490e3c2653b815a02048210ed0b587d21720a8869007a45137f87780041d100008b0bc600017a862cc280003d6927400000026f128cbba3bd1098f3823637218304bc4883e70d62024e8205d002173400000042321e05160fc00000008ec000308a0680003f400016b80000002b78f10bb000000007ec00000035500b8b1400010c8330022000000000000000000000000004c609585600003590668a6400000022f8e4c000000000000071a0000000000000000000000000003416f8000de4419000181000000025600000000000000000ff20000000a1800000000005145424aa2e280001c604029085ec39e21b41b1e005446fb1d20d6082c00008996946540004189de400000038e00008ce2a500009844ec07d1001e48db03e51049630caa37900001080004ad00013301880004399160fba0003f9098845400000000005e26d916e83fc28822822597181c281734d822c62656126400004d45473f812cc0000000b200006720004299d40aa800037a1a1c00061b00010c4f5400039b9b7c9ee5f700000000006ea26b8000bcc54600014c803200009880008d480d000000052848400000001762980250cfcb9811c0c994f400048a38880000000000000eac3280000001cc8b864930491d140000000528000ec231a00011e027c84e1d6066859e2f408b9ed42be0f6000087cc8e00043588e10c412233b0d940005fc019156c02a5bb1d78ae834a00000000000004920000c382580000002190d8e30100000000fe33225402d00006a30000af40000000001a08fb2000000000052c0000000000e52000000078cbc20000a684440005063ad99180002822f5097400078700016380003db3d783bc97c4b733c9e680d000003f21306002de2d095e4000490371800020a52b27300000001471b38000000000000000000070a000006cb440001a48000640851393828091010d2b5092c00010000012806fe0000000000c3e0
  | 15 => 0x6842c4000000048900000000001d00000000a88366265a19c93663d0741c300002e52781948aa66e83e882cc6628152679b3096a1eb1f319cc10a4e81b58000c0a3c509807007a838620d1d6835a30d28a1b84aee4bb3be01b84160b10f99958f280673ce8cbd0524750710d48c3863b2191cd00000003f10d4c000000312089800051f0d712d000075815b10e400008d3bb0c5400000000004580001dc13e000042e0001ab1adc00033a39c088878c7e109c9b8000066e09c13540002e715d88fccbc29522c807800071a00004205700002be993cc7200000000000005400000000b70000000000000018e171215027e1d70001168fee3403ae0000ae46c305e1aac00000000019c00003ff0a620c80000001f680010ca000152005c0007d32309d487fa47a0001a04d400002b48000000000318000015e32d0001e140006c0000000000000040500000006ae0001ccc00000002980007340002281d540005da0001a0c4940002409a90f7a00043b1b9831479b0001d586ba5ec40d80e00002f60fd00010d200000021743521d91178da0a9e000000000000000000000000002751c20e0098240321300005565aa0c38d8400036c30699007de00000017540003fe2a81298dda2ef0000a5c0007303e48d283f014f320944c4fc54900299102821973f30ff0aac00010a854906e13c03815ac4e22fa0fb16cc0b20000000d3501c16a00001cc5f65a94161af80003ae06a00004f67a40000fe400010c3908b340002fe3e69c88f5c5194091be00f443622400000000000430000aec000000119474212000017a4e4a54b00021c457200016101ac92e4db000000000085b000000000048e000000044e00016a800050240237f15b90fc1a2131905505a3cc000000000033400000000002d4403a18009c16100600000004ba000088c3e467a3dd00000002b31da9190fd847f1200000a9c56000000004d00000000d080000000000000d2c68c0000000d1a1a30ea80f03827a112280000000002ef82740000001fc036045a21a3cf86d4ca805727d8000a163743608000f727d429d0c987162471681df8d2077b0301fd840c3112ad05b84243d50d399a00c608908181ec9f077a0d8099cb6c30a2c292a45c824d27a090ccc429c21d8c509fc0002ff0000150736000023039c7821e40000d2815a00000000001cd2850e800007491f1981868c20720d9f54f800fd000095c738541386a0f0a025591f089d00005280008e740002ee0000000a1e000000000001610b000137c0007543fe000000000019b8
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd7654910004fc76549100067f65549100267c655491000dfa70549101ff7a505491003cff7690910004fe7690910004fd769091003cfc76909100067f65909101f67c6590910006bf649091001ebc649091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101de7c655091001ebe6450910006bd6450910005f77150910015f47150910044ff76cc910004fe76cc910004fd76cc910044fc76cc9100067f65cc9101c67c65cc91002dbe74cc910005bd74cc910006ef62cc91003eec62cc910015f671cc910005f571cc91003cff768c910004fe768c910004fd768c91003cfc768c9100067f658c9101a67c658c91002dbe748c910005bd748c910006df638c910046dc638c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101867c654c91003cff760c910004fe760c910004fd760c91003cfc760c9100357e750c9100057d750c9100067f650c9101667c650c910006df630c910046dc630c910006ef620c91003eec620c910015f6710c910005f5710c91000dfa700c910005f9700c91000df47654510026f4765451000cf47654510015f77554510017777554510007776554510026f66554510026f46554510037746554510005f77354510037775254510007755254510007f3705451000df6705451000df4705451013ff07054510016f76054510017f3605451013f77505451013ff2505451013f75505451013ff2205451000df4764c510046f4764c51000cf4764c510005f7754c510005f5754c51000777654c51000774654c510015f7734c510017d7734c510007d7634c510046f6634c510046f4634c510007d4634c510007d6434c510007d5434c510007d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100fff0704c510016f7604c510017f3604c5100fff2504c5100fff2204c510015f87654110026f87654110014f8765411000dfb755411000f7b75541100077b6554110026fa6554110026f865541100377865541100377b5354110007795354110005fb7254110007f37154110015fa7154110015f871541100bff0715411000efb615411000ff361541100bf7b51541100bff251541100bf795154110037f151541100077151541100bff23154110007f13154110015f8764811003ef87648110014f87648110005fb7548110005f975481100077b654811000778654811000dfb724811000feb7248110007eb624811003efa624811003ef86248110007e86248110007ea4248110007e94248110007ea3248110007e93248110007f37148110015fa7148110015f8714811004ff0714811000efb614811000ff3614811004ff25148110007f1514811004ff23148110007f13148110
  | 1 => 0x8d100067c6598d10006df6398d100fdf57198d1007df97098d10044ff7658d100057f7558d100357c7558d100067f6558d100067c6558d10005bf7458d1002dbc7458d10005ef7258d10005ec7258d10115f77158d10095fb7058d10004ff7558d100067f7558d100047f7558d10024fe7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d1001cfc7458d10006bc7458d1001cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d1003cec7258d10114ff7158d10006f77158d100fcff7058d10006fb7058d102acfe7618d100067f6518d100067c6518d1002dbe7418d10005bd7418d10046de6318d10006dd6318d10044ff7694d10004fe7694d10004fd7694d10044fc7694d100067f6594d100267c6594d100375f5394d10015f67194d10005f57194d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100267c6554d10015f67154d10267765154d10044ff7690d10004fe7690d10004fd7690d10044fc7690d100067f6590d102567c6590d10006bf6490d1001ebc6490d10015f67190d10005f57190d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1023e7c6550d1001ebe6450d10006bd6450d10005fb7050d1000df87050d1003cfe76d89100067f65d89100067c65d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d8910044fe73d8910004fd73d8910006ef42d8910006ec42d891000cff71d8910014fe71d891000cfd71d8910014fc71d89102a6ef21d89102a6ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d891029eef20d891029eed20d89100ccfd76989100357e75989100057d75989100067f65989100067c6598910006ef62989100cdf5719891004df9709891003cff76589100057f75589100357c75589100067f65589100067c6558910005bf745891002dbc7458910005df7358910005dc73589100e5f77158910065fb7058910004ff75589100067f75589100047f7558910024fe7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910044fc7358910006dc7358910044dc7358910006ef72589100e4ff7158910006f771589100ccff7058910006fb705891029cfe76189100067f65189100067c651891002dbe7418910005bd741891003eee6218910006ed621891003cff7694910004fe7694910004fd769491003cfc76949100067f65949100267c659491000dfa7094910005f97094910004ff7654910004fe7654910004f
  | 2 => 0x67f42d95100067c42d95102ee7f71d95103067e71d95102ee7d71d95102ee7c71d95103067f41d95103067e41d95103067d41d95103067c41d95103067f31d95103067e31d95103067d31d95103067c31d95103067f21d95103067e21d95103067d21d95103067c21d95102ee7f70d95102ee7e70d95102ee7d70d95102ee7c70d95102ee7f40d95102ee7e40d95102ee7d40d95102ee7c40d95102ee7f30d95102ee7e30d95102ee7d30d95102ee7c30d95102ee7f20d95102ee7e20d95102ee7d20d95102ee7c20d95102ee7f10d95102ee7e10d95102ee7c10d9510024ff76595100367c65595102f5f771595102fdfb70595102ecff75595100067f7559510004ff745951001cfe745951001cfc7459510004ff7359510044fc7359510004ff725951003cfc72595102f4ff7159510006f7715951013cff7059510006fb70595102ed7e76195100367e76195102ec7e76195100067e64195100067c64195102e77671195102df7571195102de7f61195102e77631195102df7a70195102e77970195102de7f60195102df7a20195102e77b10195102df7610195102df7410195102df78101951001cfe76d91100067f65d91100067c65d911002ebe64d9110024fe75d9110004fd75d9110024fc75d911012cfd74d9110044fe73d9110004fd73d911002ebc43d911003cfe72d9110004fd72d911002ebc42d911000cff71d9110014fe71d911000cfd71d9110014fc71d91102d6bf41d91102d6bd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d91102c6bf40d91102c6bd40d911001cff76591100057f75591100357c75591100067f65591100067c655911002ebc6459110005df7359110005dc7359110005ef7259110005ec72591102bdf771591102cdfb7059110004ff75591100067f75591100047f7559110024fe7559110024fc75591100067c75591100247c75591102c4ff7459110006bf7459110004ff7359110006df7359110004df7359110044fc7359110006dc7359110044dc735911002ebf4359110004ff7259110006ef7259110004ef725911003cfc7259110006ec725911003cec725911002ebf42591102bcff7159110006f7715911012cff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc76551100067f65551100267c6555110044fe76d8d100067f65d8d100067c65d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df43d8d10006dc43d8d1003cfe72d8d10004fd72d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d102b6df31d8d102b6dd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d102aedf30d8d102aedd30d8d100fcfd7698d100357e7598d100057d7598d100067f659
  | 3 => 0xc4350920057af4150920007eb705092000dee705092000dec70509201cfe8705092003eef605092003feb60509201cfaf40509201cfad40509201cfea105092000cfe76cc92000cfc76cc920055be74cc920005bd74cc920006df63cc920046dc63cc92000dfa70cc920005f970cc92014dee768c92003eee768c92003def748c92003fae748c920005ed748c92003fad748c920005ad748c92016ded738c920046ee638c920046ec638c92000dee708c92000dec708c92003eef608c92003feb608c92018fea108c920044ff764c92000cfe764c92016cfd764c92000cfc764c920006df634c920046dc634c920005fb704c92000df8704c92000dec764c920046ec764c92000cec764c920005ef744c920005ed744c92003def734c92003fcf734c920007cf634c920046ee634c920046ec634c920007cc634c920007eb704c92000dee704c92000dec704c92016fe8704c92003eef604c92003feb604c92016fea104c920014fe76d852004ef661d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d8520044fe73d8520004fd73d852000cfd72d8520014fc72d8520006f751d852004ef451d852004ef621d852000cfe70d852003cfd70d852000cfc70d85200e6f710d85200057f755852005d7c7558520005bf7458520055bc7458520005df7358520005dc735852004ef46158520004ff7654520004fe7654520004fc76545200267e65545200067d6554520005ef725452003dec7254520004ff7650520004fe7650520004fc7650520007ad4250520004fe76cc520004fd76cc520044fc76cc52005d7e75cc5200057d75cc52003dee72cc520005ed72cc520007cd32cc520004ff764c520004fe764c520004fc764c520007cd324c52000cfc7648520006f76148520016f46148520005fb704852000df87048520024fe76d95100367e65d951013cfd75d951001cfe74d9510004fd74d951001cfc74d95100367f54d95100067e54d95100367c54d9510044fe73d9510004fd73d95100367f53d95100367c53d951003cfe72d9510004fd72d95100367f52d95100367c52d951000cff71d9510014fe71d951000cfd71d9510014fc71d95103067f51d95103067d51d9510014ff70d951000cfe70d9510014fd70d951000cfc70d95102ee7f50d95102ee7d50d95102dd7e76d95100247e76d95100067e64d95100067c64d95102ef7771d95102ef7471d95103077631d95103077b70d95102ef7870d95102ef7a20d95103077b10d95102ef7610d95102ef7410d95102ef7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d9510
  | 4 => 0x9520014fc7159520006f47159520014f4715952005e7f51595201fcff7059520006fb70595201fe7e50595201fe7c50595201fefa105952001cfe76d9120056be64d9120024fe75d9120004fd75d9120024fc75d9120006bf54d9120056bc54d9120044fe73d9120004fd73d9120056bf43d912003cfe72d912000cfd72d912003cfc72d9120056bf42d9120014fe71d9120004fd71d9120014fc71d9120006be41d9120056bc41d912003cff70d912003cfd70d91201e6bf40d91201e6bd40d9120056bc6459120315ef7259120004ff7559120024fe7559120024fc75591201e4ff7459120006bf7459120004ff7359120044fc7359120314ff7259120006ef7259120004ff7159120014fe7159120014fc71591201ccff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc7655120044fe76d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20006df53d8d20006dc53d8d2003cfe72d8d2003cfc72d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20006dc31d8d2003cff70d8d2003cfd70d8d2018edf30d8d2018edd30d8d20055be7498d20005bd7498d20006df6398d2016ded7298d201adef7258d20004ff7558d20024fe7558d20024fc7558d20004ff7458d2001cfe7458d2001cfc7458d20006df7358d201acff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d2016cff7058d20006fb7058d2018cfe7618d2005d7e7518d200057d7518d20046de6318d20006dd6318d20044ff7694d20004fe7694d20004fd7694d20044fc7694d2005f5f5394d2003dee7294d20005ed7294d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200267e6554d200067d6554d20005fb7054d2000df87054d20044ff7690d20004fe7690d20004fd7690d20044fc7690d20006df6390d20046dc6390d2003dee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d2001ebc6450d20006df6350d20046dc6350d20024ff765492000cfe76549201fcfd765492000cfc76549200067f65549200267c6554920005fb705492000df8705492003fe8205492030dee769092003eee76909201cded749092001eee649092001eec6490920005ed7390920057af4390920007ad439092000dee709092000dec709092003eef609092003feb60909201e7ea109092001cff765092000cfe76509201ccfd765092000cfc7650920006bf645092001ebc645092003fac4250920005fb705092000df8705092003fe8205092000dec765092001eec765092000cec765092003def745092003faf7450920007af645092001eee645092001eec6450920057ac6450920005ef7350920007ae4350920057a
  | 5 => 0x14fc7158f2016edf3058f2016edd3058f20044ff7694f2003cfe7694f20004fd7694f2003cfc7694f200267e6594f200067d6594f200775f5394f2003dee7294f20005ed7294f20004ff7654f2003cfe7654f20004fd7654f2003cfc7654f200267e6554f200067d6554f20044ff7690f2003cfe7690f20004fd7690f2003cfc7690f202567e6590f200067d6590f2001ebe6490f20006bd6490f2003dee7290f20005ed7290f20004ff7650f2003cfe7650f20004fd7650f2003cfc7650f2023e7e6550f200067d6550f2032ebf6450f2001ebc6450f2003dee7250f2032fae4250f20005fb7050f2000df87050f2003def7650b20326ef7650b2003f6e6550b2003f6d6550b2003faf7450b2003faf6450b2001eee6450b2003eec6450b2003fac6450b20005ef7350b20007ae4350b2006fac4350b2006faf4150b2000dee7050b2000dec7050b201cfaf4050b201cfad4050b2003def764cb20006ef764cb2003f6e654cb2003f6d654cb20005ef744cb20005ed744cb2003fcf734cb20046ee634cb2003eec634cb2000dee704cb2000dec704cb20004ff7558720024fe7558720024fc7558720004ff745872001cfe745872001cfc7458720004ff7358720044fc735872000cfe7258720014fd725872000cfc725872003ef7715872003ef7215872003ef4215872003efa205872003ef920587200cef71058720004ff7654720004fd765472003cfc76547200267e65547200067d6554720005ef725472003dec7254720004ff7650720004fd765072003cfc76507201367e65507200067d655072001ebe6450720006bd6450720007ad4250720044ff76cc72003cfe76cc720004fd76cc7200757e75cc7200057d75cc7201267e65cc7200067d65cc720046de63cc720006dd63cc72003dee72cc720005ed72cc720007cd32cc720004ff764c720004fd764c72003cfc764c72010e7e654c7200067d654c720046de634c720006dd634c720007cd324c720024fe76d952005e7e65d952001cfe74d9520004fd74d952001cfc74d9520044fe73d9520004fd73d952003cfe72d952000cfd72d952003cfc72d952005e7f52d9520014fe71d9520004fd71d9520014fc71d95200067e51d952005e7c51d952003cff70d952003cfd70d95202167f50d95202167d50d9520216fa10d952005e7c6559520005bf7459520055bc7459520005df7359520005dc735952031def7259520005f7715952004df47159520214ff75595200067f7559520004ff7459520006bf7459520004bf745952001cfe745952001cfc7459520006bc745952001cbc7459520004ff7359520006df7359520004df7359520044fc7359520006dc7359520044dc735952005e7f535952031cff7259520006ef7259520004ff7159520006f77159520004f77159520014fe715
  | 6 => 0xd748c930006ef628c93003eec628c93000dfa708c930005f9708c93000cfc764c930006ef624c93003eec624c930005fb704c93000df8704c930014fe76d853007ef661d8530024fe75d8530004fd75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d853000cfd73d8530014fc73d853003cfe72d8530004fd72d853007ef631d8530044fd70d8530116f710d85300057f755853008d7c7558530005bf7458530085bc7458530005ef7258530005ec725853007ef46158530004ff7654530004fe7654530004fc7654530004ff7650530004fe7650530004fc765053000cfc764c530006f7614c530016f4614c530005fb704c53000df8704c530004fe76c8530004fd76c853003cfc76c8530004ff7648530004fe7648530004fc764853003e7f7559720004ff745972001cfe745972001cfc74597200767f54597200067e54597200767c5459720004ff7359720044fc73597200767f53597200767c535972003cff725972000cfe725972003cfd725972000cfc725972003e7e525972003e7c5259720004ff7159720014fe7159720014fc71597200767f51597200067e51597200767c51597201fe7f50597201fe7d50597200067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c73597200067f43597200067c435972003e7f725972003e7e725972003e7d725972003e7c725972003e7f425972003e7e425972003e7d425972003e7c425972003e7f325972003e7e325972003e7d325972003e7c32597200067f71597200067e71597200067d71597200067c71597200067f41597200067e41597200067c41597200067e31597200067c315972003e7f215972003e7e215972003e7d215972003e7c21597201fe7f70597201fe7e70597201fe7d70597201fe7c70597201fe7f40597201fe7e40597201fe7d40597201fe7c40597201fe7f30597201fe7e30597201fe7d30597201fe7c305972003e7f205972003e7e205972003e7d205972003e7c20597201fe7f10597201fe7e10597201fe7d10597201fe7c1059720004ff7559320024fe7559320024fc755932003ebf7459320004ff7359320044fc735932006ebc435932003cff725932000cfe725932003cfd725932000cfc725932003ebe425932003ebc4259320004ff7159320014fe7159320014fc715932006ebf41593201cebf40593201cebd4059320004ff765532003cfe7655320004fd765532003cfc76553200267e65553200067d6555320004ff7558f20024fe7558f20024fc7558f20004ff7458f2001cfe7458f2001cfc7458f2003edf7358f20006df4358f20006dc4358f2003cff7258f2000cfe7258f2003cfd7258f2000cfc7258f2003ede3258f2003edc3258f20004ff7158f20014fe7158f20
  | 7 => 0x873003cfc7258730046f77158730046f73158730046f431587300fef71058730004ff7654730004fd7654730044fc7654730005fb705473000df87054730004ff7650730004fd7650730044fc765073001ebe6450730006bd645073003cff76c8730044fe76c8730004fd76c8730004ff7648730004fd7648730044fc7648730024fe76d953008e7e65d953001cfe74d9530004fd74d953001cfc74d95300067e54d953008e7c54d9530044fe73d953000cfd73d9530044fc73d953008e7f53d953003cfe72d9530004fd72d953008e7f52d9530014fe71d9530004fd71d9530014fc71d95300067e51d953008e7c51d9530044ff70d9530044fd70d95302767f50d95302767d50d953008e7c6559530005bf7459530085bc745953033ddf7359530274ff75595300067f7559530004ff7459530006bf7459530004bf745953001cfe745953001cfc7459530006bc745953001cbc745953033cff7359530006df7359530004ff725953003cfc7259530004ff7159530014fe7159530014fc715953025cff7059530006fb705953001cfe76d9130086be64d9130024fe75d9130004fd75d9130024fc75d9130006bf54d9130086bc54d9130044fe73d913000cfd73d9130044fc73d9130086bf43d913003cfe72d9130004fd72d9130086bf42d9130014fe71d9130004fd71d9130014fc71d9130006be41d9130086bc41d9130044ff70d9130044fd70d9130246bf40d9130246bd40d91300057f755913008d7c7559130086bc6459130335df7359130004ff75591300067f75591300047f7559130024fe7559130024fc75591300067c75591300247c7559130244ff7459130006bf7459130334ff7359130006df7359130004ff725913003cfc7259130004ff7159130014fe7159130014fc715913022cff7059130006fb7059130004ff7655130004fe7655130004fd7655130004fc7655130024ff7654d3000cfe7654d3025cfd7654d3000cfc7654d300067f6554d300267c6554d30005fb7054d3000df87054d3001cff7650d3000cfe7650d3022cfd7650d3000cfc7650d30006bf6450d3001ebc6450d30005fb7050d3000df87050d3003cfe76d8930024fe75d8930004fd75d8930024fc75d893001cfe74d8930004fd74d893001cfc74d8930014fe71d8930004fd71d8930014fc71d8930006ee21d8930006ec21d8930044fd70d89301aeef20d893008d7e75989300057d7598930085be7498930005bd7498930006ef629893003eee6218930006ed6218930004fe7694930004fd769493003cfc7694930004ff7654930004fe7654930004fc76549300067f65549300267c6554930004fe7690930004fd769093003cfc7690930004ff7650930004fe7650930004fc7650930006bf645093001ebc645093000cfe768c930085be748c930005b
  | 8 => 0x4fe76cc940004fd76cc940044fc76cc94001dbe74cc940005bd74cc940006df63cc940046dc63cc940004fe768c940004fd768c94003cfc768c94001dbe748c940005bd748c940004ff764c940004fe764c940004fc764c94001dbe744c940005bd744c940006df634c940046dc634c940004fe760c940004fd760c94003cfc760c9400b57e750c9400057d750c94001dbe740c940005bd740c94000dfa700c940005f9700c940014fe76d85400aef661d8540024fe75d8540004fd75d8540024fc75d854000cfd74d8540014fc74d8540044fe73d8540004fd73d8540356bf43d8540006bd43d854003cfe72d8540004fd72d8540356bf42d8540006bd42d85400aef641d8540356f541d854001cfd70d85402bef710d85400057f75585400b57c7558540005df7358540005dc7358540005ef7258540005ec72585400aef4615854034dfb7058540004ff7654540004fe7654540004fc7654540005bf745454001dbc7454540004fe76cc540004fd76cc540044fc76cc5400b57e75cc5400057d75cc54001dbe74cc540005bd74cc5400079d43cc540004ff764c540004fe764c540004fc764c5400079d434c540004fe76c8540004fd76c854003cfc76c854001dbe74c8540005bd74c8540004ff7648540004fe7648540004fc76485400467f7559730004ff745973001cfe745973001cfc7459730044ff735973000cfe7359730044fd735973000cfc73597300467e53597300467c5359730004ff725973003cfc72597300a67f5259730004ff7159730014fe7159730014fc71597300067e51597300a67c515973025e7f505973025e7d5059730004ff7559330024fe7559330024fc7559330046bf7459330044ff735933000cfe7359330044fd735933000cfc7359330046be4359330046bc4359330004ff725933003cfc725933009ebc4259330004ff7159330014fe7159330014fc715933009ebf415933022ebf405933022ebd4059330004ff7655330044fe7655330004fd7655330044fc7655330005fb705533000df87055330004ff7558b30024fe7558b30024fc7558b30004ff7458b3001cfe7458b3001cfc7458b3000cfc7358b30046ef7258b30046ef3258b30046ec3258b30004ff7158b30014fe7158b30014fc7158b3016eef2058b3003cff7694b30044fe7694b30004fd7694b3000dfa7094b30005f97094b30004ff7654b30004fd7654b30044fc7654b300267e6554b300067d6554b3003cff7690b30044fe7690b30004fd7690b3001ebe6490b30006bd6490b30004ff7650b30004fd7650b30044fc7650b30346bf6450b3001ebc6450b30005fb7050b3000df87050b30004ff7558730024fe7558730024fc7558730004ff745873001cfe745873001cfc745873000cfe7358730014fd735873000cfc7358730004ff725
  | 9 => 0xf764c550004fe764c550004fc764c5500257e754c5500057d754c550006df634c550046dc634c550004fe76c8550004fd76c855003cfc76c8550006f761c8550016f461c8550004ff7648550004fe7648550004fc7648550024fe76d95400b67e65d954028cfd75d954000cff74d954001cfe74d954000cfd74d954001cfc74d95403867f54d95403867d54d9540044fe73d9540004fd73d95400b67c53d954003cfe72d9540004fd72d95400b67f52d9540014fe71d9540004fd71d9540014fc71d95400067e51d95400b67c51d954001cff70d954001cfd70d95403767f50d95403767d50d9540024ff76595400b67c655954036dbf7459540005df7359540005dc735954037dfb7059540374ff75595400067f755954036cff7459540006bf7459540004ff7359540006df7359540004df7359540044fc7359540006dc7359540044dc7359540004ff725954003cfc7259540004ff7159540014fe7159540014fc715954028cff7059540006fb7059540044fe76d8d40024fe75d8d40004fd75d8d40024fc75d8d4000cfd74d8d40006df53d8d40006dc53d8d40366de43d8d40366dd43d8d4003cfe72d8d40004fd72d8d40014fe71d8d40004fd71d8d40014fc71d8d40006de31d8d40006dc31d8d4001cfd70d8d40336df30d8d40006df6398d40085f97098d400057f7558d400b57c7558d4009dfb7058d40046de6318d40006dd6318d40004fe7694d40004fd7694d40044fc7694d400067f6594d400267c6594d4001dbe7494d40005bd7494d400b75f5394d40004ff7654d40004fe7654d40004fc7654d4000dbc7650d40046bc7650d4000cbc7650d4001dbf7350d4001f9f7350d400079f6350d40046be6350d40046bc6350d400079c6350d400469c6350d40005bf7250d4032ebc6250d40007bb7050d4000dbe7050d4000dbc7050d4022fb87050d4000db87050d4001ebf6050d4001fbb6050d4003cfe76d8940024fe75d8940004fd75d8940024fc75d894000cfd74d8940044fe73d8940004fd73d894035eee42d894035eed42d8940014fe71d8940004fd71d8940014fc71d8940006ee21d8940006ec21d894001cfd70d8940316ef20d89400b57e75989400057d7598940005de7398940005dd7398940006ef6298940055f9709894006dfb705894003eee6218940006ed6218940004fe7694940004fd769494003cfc769494001dbe7494940005bd749494000dfa7094940005f97094940004ff7654940004fe7654940004fc76549400067f65549400267c655494000dbc765094003ebc765094000cbc7650940005bf7350940346bc635094001dbf725094001faf7250940007af625094003ebe625094003ebc6250940007ac6250940007bb705094000dbe705094000dbc70509401cfb8705094001ebf605094001fbb6050940
  | 10 => 0x9150005df7359150005dc73591503adfb7059150044fe76d8d5000cfd75d8d5001cfe74d8d50004fd74d8d5001cfc74d8d503a6de53d8d503a6dd53d8d50006df43d8d50006dc43d8d5003cfe72d8d50004fd72d8d50014fe71d8d50004fd71d8d50014fc71d8d50024fd70d8d5033edf30d8d50006df6398d5008df97098d50005bf7458d500c5bc7458d500a5fb7058d50046de6318d50006dd6318d5000d7c7654d500467c7654d5000c7c7654d500257f7354d500275f7354d500075f6354d500467e6354d500467c6354d500075c6354d500057f7154d502667e6154d502667c6154d500077b7054d5000d7e7054d5000d7c7054d5025f787054d5000d787054d500267f6054d500277b6054d5025f7a1054d50004fe7690d50004fd7690d50044fc7690d500257e7590d500057d7590d50006bf6490d5001ebc6490d50004ff7650d50004fe7650d50004fc7650d5003cfe76d895000cfd75d895001cfe74d8950004fd74d895001cfc74d8950044fe73d8950004fd73d895039e7f53d89500067d53d895039eee52d895039eed52d8950014fe71d8950004fd71d8950014fc71d895039e7f51d8950024fd70d895031e7e50d895031e7c50d895031eef20d895031efa10d8950006ef629895005df97098950005bf74589500c5bc7458950005df7358950005dc7358950005f771589500bdf47158950075fb705895003eee6218950006ed6218950004fe7690950004fd769095003cfc7690950006bf649095001ebc6490950004ff7650950004fe7650950004fc76509500057f75509500257c7550950004fe76cc950004fd76cc950044fc76cc9500257e75cc9500057d75cc9500c5be74cc950005bd74cc950004fe768c950004fd768c95003cfc768c9500c5be748c950005bd748c950006df638c950046dc638c950004ff764c950004fe764c950004fc764c950004fe760c950004fd760c95003cfc760c9500257e750c9500057d750c950006df630c950046dc630c950014fe76d85500bef661d855000cfd75d8550014fc75d855001cfe74d8550004fd74d855001cfc74d8550044fe73d8550004fd73d855003cfe72d8550004fd72d85500bef651d8550396f551d85500bef421d8550024fd70d85502f6f710d85500bef4615855038dfb705855000d7c76545500167c765455000c7c76545500057f73545500067f62545500257f71545500277771545500077761545500167e61545500167c61545500bf7461545500077b705455000d7e705455000d7c705455013f7870545500267f60545500277b605455013f77105455013f7a1054550004ff7650550004fe7650550004fc7650550006bf645055001ebc6450550004fe76cc550004fd76cc550044fc76cc5500257e75cc5500057d75cc550006df63cc550046dc63cc550004f
  | 11 => 0xd6bf42d912103cff71d912103cfd71d91211eebf41d91211eebd41d912100cfe70d9121004fd70d912100cfc70d9121006be40d91210d6bc40d91210057f75591210dd7c75591210d6bc64591213bdef7259121004ff75591210067f75591210047f7559121024fe7559121024fc75591210067c75591210247c75591211ecff7459121006bf7459121004ff7359121044fc73591213bcff7259121006ef72591211d4ff7159121006f77159121004ff705912100cfe705912100cfc7059121004ff7655121004fe7655121004fd7655121004fc7655121044fe76d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d2103cff71d8d2103cfd71d8d21196df31d8d21196dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d210dd7e7598d210057d7598d210d5be7498d21005bd7498d21006df6398d21175ed7298d211b5ef7258d21004ff7558d21024fe7558d21024fc7558d21004ff7458d2101cfe7458d2101cfc7458d21006df7358d211b4ff7258d21006ef7258d21174ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21194fe7618d21046de6318d21006dd6318d21044ff7694d21004fe7694d21004fd7694d21044fc7694d210df5f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d210267c6554d21044ff7690d21004fe7690d21004fd7690d21044fc7690d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2101ebc6450d21024ff7654921014fe7654921204fd7654921014fc76549210067f65549210267c6554921005f77154921015f4715492101cff7650921014fe76509211d4fd7650921014fc7650921006bf645092101ebc6450921005f77150921015f47150921014fe76cc921014fc76cc9210d5be74cc921005bd74cc921006df63cc921046dc63cc921015f671cc921005f571cc921044ff764c921014fe764c921174fd764c921014fc764c921006df634c921046dc634c921005f7714c921015f4714c92100cfe76d81210cefa60d8121024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d8121044fe73d8121004fd73d8121014fd72d812100cfc72d812103cfd71d812100cfc71d81210cefa20d81210cefa10d81210057f75581210dd7c7558121005bf74581210d5bc7458121005df7358121005dc73581210cef8605812101cfe76d91500c6be64d915000cfd75d915001cfc75d91500c6be54d91503b6bd54d9150044fe73d9150004fd73d91500c6bc43d915003cfe72d9150004fd72d91500c6bc42d9150014fe71d9150004fd71d9150014fc71d91500c6bf41d9150024fd70d915036ebf40d91500c6bc645
  | 12 => 0xd74d813101cfc74d8131014fd73d813100cfc73d813103cfe72d8131004fd72d8131044fd71d8131006fb50d81310fef850d81310fefa30d81310fefa10d81310057f755813110d7c7558131005bf7458131105bc7458131005ef7258131005ec72581310fef8605813103e7f7559721004ff745972101cfe745972101cfc7459721004ff7359721044fc73597210f67f5359721014fe7259721014fc725972103e7e525972103e7c52597212067f51597212067d5159721004ff705972100cfe705972100cfc70597210067e50597210f67c5059721004ff7559321024fe7559321024fc755932103ebf7459321004ff7359321044fc73593210eebc4359321014fe7259321014fc725932103ebe425932103ebc42593211d6bf41593211d6bd4159321004ff705932100cfe705932100cfc70593210eebf4059321004ff765532103cfe7655321004fd765532103cfc7655321005f77155321015f47155321004ff7558f21024fe7558f21024fc7558f21004ff7458f2101cfe7458f2101cfc7458f2103edf7358f21014fe7258f21014fc7258f2103ede3258f2103edc3258f21176df3158f21176dd3158f21004ff7058f2100cfe7058f2100cfc7058f21044ff7694f2103cfe7694f21004fd7694f2103cfc7694f210f75f5394f21015f67194f21005f57194f21004ff7654f2103cfe7654f21004fd7654f2103cfc7654f210267e6554f210067d6554f21044ff7690f2103cfe7690f21004fd7690f2103cfc7690f2101ebe6490f21006bd6490f21004ff7650f2103cfe7650f21004fd7650f2103cfc7650f2132ebf6450f2101ebc6450f21005f77150f21015f47150f21004ff7558321024fe7558321024fc7558321004ff745832101cfe745832101cfc7458321004ff7358321044fc7358321014fe725832100cfd7258321014fc725832103efb705832103efb205832103ef820583210e6fa1058321024fe76d95210de7e65d952101cfe74d9521004fd74d952101cfc74d95210067e54d95210de7c54d9521044fe73d9521004fd73d95210de7f53d9521014fd72d95210de7f52d952103cff71d952103cfd71d952121e7f51d952121e7d51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210de7c50d95210de7c6559521005bf74595210d5bc74595213c5ef725952121cff75595210067f7559521004ff7459521006bf7459521004bf745952101cfe745952101cfc7459521006bc745952101cbc7459521004ff7359521044fc73595213c4ff7259521006ef7259521204ff7159521006f77159521004ff705952100cfe705952100cfc705952101cfe76d91210d6be64d9121024fe75d9121004fd75d9121024fc75d9121006bf54d91210d6bc54d9121044fe73d9121004fd73d91210d6bf43d9121014fd72d9121
  | 13 => 0x9131024fc755913124cff7459131006bf74591313d4ff7359131006df7359131004ff725913103cfc7259131234ff7159131006f77159131004ff705913100cfe705913100cfc7059131004ff7655131004fe7655131004fd7655131004fc7655131024ff7654d31014fe7654d31264fd7654d31014fc7654d310067f6554d310267c6554d31005f77154d31015f47154d31047d43154d313cdde7690d31046de7690d31235dd7490d3101ede6490d3101edc6490d31005dd7290d311079f4290d31015de7190d31015dc7190d31046df6190d31047d76190d3124fd71090d3101cff7650d31014fe7650d31234fd7650d31014fc7650d31006bf6450d3101ebc6450d310479c4350d31005f77150d31015f47150d31047d43150d31015dc7650d3101edc7650d31014dc7650d31045df7450d310479f7450d310079f6450d3101ede6450d3101edc6450d311079c6450d31005df7250d311079c4250d31007d77150d31015de7150d31015dc7150d31237d47150d31046df6150d31047d76150d312379f4150d312379d4150d311079f4050d31237d71050d3103cfe76d8931024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d8931006ef52d8931006ec52d8931044fd71d89311b6ef21d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d8931105be7498931005bd7498931006ef629893110d7e75189310057d751893103eee6218931006ed6218931004fe7694931004fd769493103cfc7694931045de7394931005dd7394931004ff7654931004fe7654931004fc76549310267e65549310067d6554931005f77154931015f47154931004fe7690931004fd769093103cfc7690931045de7390931005dd73909310079d4390931006ef629093103eec6290931004ff7650931004fe7650931004fc7650931006bf645093101ebc64509310079e4350931006ef625093103eec6250931155de76cc931046de76cc931045df74cc9310479e74cc931005dd74cc9310479d74cc9310059d74cc93103ede62cc93103edc62cc931015de71cc931015dc71cc931046df61cc931047d761cc9311b7d710cc931014fe768c931105be748c931005bd748c931175dd738c931006ef628c93103eec628c931015f6718c931005f5718c931014fc764c931006ef624c93103eec624c931005f7714c931015f4714c931015dc764c93103edc764c931014dc764c931005df744c931005dd744c931045df724c931047cf724c931007cf624c93103ede624c93103edc624c931007cc624c931007d7714c931015de714c931015dc714c931177d4714c931046df614c931047d7614c931177d7104c93100cfe76d81310fefa60d8131024fe75d8131004fd75d8131024fc75d813101cfe74d8131004f
  | 14 => 0x479f6450f3101ede6450f31046dc6450f310479c6450f31005df7250f3111f9c4250f31015de7150f31015dc7150f312379f4150f312379d4150f3111f9f4050f31004ff7558b31024fe7558b31024fc7558b31004ff7458b3101cfe7458b3101cfc7458b31014fc7358b31046ef7258b31006ef4258b31006ec4258b31046ef3258b31046ec3258b31176ef2158b31004ff7058b3100cfe7058b3100cfc7058b3103cff7694b31044fe7694b31004fd7694b310267e6594b310067d6594b31045de7394b31005dd7394b31004ff7654b31004fd7654b31044fc7654b310267e6554b310067d6554b3103cff7690b31044fe7690b31004fd7690b311f67e6590b310067d6590b3101ebe6490b31006bd6490b31045de7390b31005dd7390b310079d4390b31004ff7650b31004fd7650b31044fc7650b311de7e6550b310067d6550b31346bf6450b3101ebc6450b31045de7350b313479e4350b31005f77150b31015f47150b31045df764cb31006df764cb310475e654cb310475d654cb31005df744cb31005dd744cb31047cf724cb3103ede624cb3103edc624cb31015de714cb31015dc714cb31004ff7558331024fe7558331024fc7558331004ff745833101cfe745833101cfc7458331014fe735833100cfd7358331014fc7358331004ff725833103cfc7258331046f63158331046f53158331046fb7058331046fb3058331046f83058331116fa1058331024fe76d953110e7e65d953101cfe74d9531004fd74d953101cfc74d9531014fd73d953110e7f53d953103cfe72d9531004fd72d9531044ff71d9531044fd71d953127e7f51d953127e7d51d953100cfe70d9531004fd70d953100cfc70d95310067e50d953110e7c50d953127ef710d953110e7c6559531005bf7459531105bc74595313dddf7359531005ef7259531005ec7259531005fb70595310fdf8705953127cff75595310067f7559531004ff7459531006bf7459531004bf745953101cfe745953101cfc7459531006bc745953101cbc74595313dcff7359531006df7359531004ff7259531006ef7259531004ef725953103cfc7259531006ec725953103cec725953110e7f5259531264ff7159531006f771595312667e51595312667c5159531004ff7059531006fb7059531004fb705953100cfe705953100cfc7059531006f8705953100cf8705953110e7f5059531266f7105953101cfe76d9131106be64d9131024fe75d9131004fd75d9131024fc75d9131006bf54d9131106bc54d9131014fd73d9131106bf43d913103cfe72d9131004fd72d9131106bf42d9131044ff71d9131044fd71d913124ebf41d913124ebd41d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131106bc40d9131106bc64591313d5df7359131004ff7559131024fe755
  | 15 => 0xf625094103ebe625094103ebc6250941007ac625094103eac6250941007b77150941015be7150941015bc71509411d7b47150941015b4715094101ebf615094101fb76150941004fe76cc941004fd76cc941044fc76cc94101dbe74cc941005bd74cc941004fe768c941004fd768c94103cfc768c94101dbe748c941005bd748c941006ef628c94103eec628c941004ff764c941004fe764c941004fc764c94101dbe744c941005bd744c941006ef624c94103eec624c941004fe760c941004fd760c94103cfc760c9411357e750c9410057d750c94101dbe740c941005bd740c941015f6710c941005f5710c94100cfe76d814112efa60d8141024fe75d8141004fd75d8141024fc75d8141014fd74d814100cfc74d8141044fe73d8141004fd73d814134ebf43d8141006bd43d814103cfe72d8141004fd72d814134ebf42d8141006bd42d814101cfd71d814112efa40d814112efa10d81410057f75581411357c7558141005df7358141005dc7358141005ef7258141005ec725814112ef860581410467f7559731004ff745973101cfe745973101cfc74597311267f54597310067e54597311267c5459731014fe7359731014fc73597310467e53597310467c5359731004ff725973103cfc72597311267f52597311267c52597312667f51597312667d5159731004ff705973100cfe705973100cfc70597311267f50597310067e50597311267c50597310067f74597310067e74597310067d74597310067c74597310467f73597310467e73597310467d73597310467c73597310467f43597310467e43597310467d43597310467c43597310067f72597310067e72597310067d72597310067c72597310067f42597310067c42597310467f32597310467e32597310467d32597310467c32597312667f71597312667e71597312667d71597312667c71597312667f41597312667e41597312667d41597312667c41597310467f31597310467e31597310467d31597310467c31597312667f21597312667e21597312667d21597312667c21597310067f70597310067e70597310067d70597310067c70597310067f40597310067e40597310067c40597310467f30597310467e30597310467d30597310467c30597310067e20597310067c20597312667f10597312667e10597312667d10597312667c1059731004ff7559331024fe7559331024fc7559331046bf7459331014fe7359331014fc7359331046be4359331046bc4359331004ff725933103cfc725933111ebc4259331236bf4159331236bd4159331004ff705933100cfe705933100cfc705933111ebf4059331004ff7655331044fe7655331004fd7655331044fc76553310267e65553310067d6555331045df7650f313e6df7650f310475e6550f310475d6550f310479f7450f31
  | 16 => 0xc951145be748c951005bd748c951004ff764c951004fe764c951004fc764c951004fe760c951004fd760c95103cfc760c9510257e750c9510057d750c951006ef620c95103eec620c95100cfe76d815113efa60d8151014fd75d815100cfc75d815101cfe74d8151004fd74d815101cfc74d8151044fe73d8151004fd73d815103cfe72d8151004fd72d8151024fd71d815113efa50d815113ef830d815113efa10d815113ef86058151024fe76d95411367e65d9541294fd75d9541014ff74d9541014fd74d95414167f54d95414167d54d9541044fe73d9541004fd73d95411367f53d954103cfe72d9541004fd72d95411367c52d954101cff71d954101cfd71d95414067f51d95414067d51d954100cfe70d9541004fd70d954100cfc70d95410067e50d95411367c50d9541024ff76595411367c65595413fdbf7459541005ef7259541005ec725954140df77159541404ff75595410067f75595413fcff7459541006bf7459541004ff7359541044fc7359541004ff7259541006ef7259541004ef725954103cfc7259541006ec725954103cec7259541294ff7159541006f77159541004ff705954100cfe705954100cfc7059541044fe76d8d41024fe75d8d41004fd75d8d41024fc75d8d41014fd74d8d413f6de43d8d413f6dd43d8d4103cfe72d8d41004fd72d8d4101cfd71d8d413d6df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d411357e7598d410057d7598d41006df6398d41005ee7298d41005ed7298d41105f57198d4111df77158d41046de6318d41006dd6318d41004fe7694d41004fd7694d41044fc7694d4101dbe7494d41005bd7494d411375f5394d41015f67194d41005f57194d41004ff7654d41004fe7654d41004fc7654d410067f6554d410267c6554d41015bc7650d41046bc7650d41014bc7650d4101dbf7350d4101f9f7350d410079f6350d41046be6350d41046bc6350d410079c6350d41005bf7250d4132ebc6250d41007b77150d41015be7150d41015bc7150d41237b47150d4101ebf6150d4101fb76150d4103cfe76d8941024fe75d8941004fd75d8941024fc75d8941014fd74d8941044fe73d8941004fd73d8941006ef52d8941006ec52d89413eeee42d89413eeed42d894101cfd71d89413beef21d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d8941006ef62989410d5f571989410057f75589411357c75589410edf7715894103eee6218941006ed6218941004fe7694941004fd769494103cfc76949410067f65949410267c659494101dbe7494941005bd7494941004ff7654941004fe7654941004fc7654941015bc765094103ebc7650941014bc7650941005bf7350941346bc635094101dbf725094101faf7250941007a
  | 17 => 0x4ff765503203cfe7655032004fd765503203cfc76550320267e65550320067d6555032004ff7558432024fe7558432024fc7558432004ff745843201cfe745843201cfc745843203edf325843203edd325843203cff715843203ef77158432156f64158432046f73158432046f4315843203ef7215843203ef42158432004ff705843200cfe705843200cfc7058432156f71058432004ff7558032024fe7558032024fc7558032004ff745803201cfe745803201cfc745803203eee3258032046ed3258032004ff7158032014fe7158032014fc715803203cff705803203efb705803214efa4058032046fb3058032046f8305803203efb205803203ef8205803214efa105803201cfe76d9151146be64d9151014fd75d9151146be54d9151436bd54d9151044fe73d9151004fd73d9151146bc43d915103cfe72d9151004fd72d9151146bc42d9151024fd71d91513febf41d915100cfe70d9151004fd70d915100cfc70d9151146bf40d9151146bc6459151005ef7259151005ec725915142df77159151044fe76d8d51014fd75d8d5101cfe74d8d51004fd74d8d5101cfc74d8d51426de53d8d51426dd53d8d5103cfe72d8d51004fd72d8d514267f52d8d51024fd71d8d513de7e51d8d513de7c51d8d513dedf31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d514267f50d8d513def710d8d51006df6398d5110df57198d51005bf7458d51145bc7458d51005ef7258d51005ec7258d51125f77158d51005fb7058d5113df87058d51046de6318d51006dd6318d51004fe7690d51004fd7690d51044fc7690d51006bf6490d5101ebc6490d51004ff7650d51004fe7650d51004fc7650d510057f7550d510257c7550d5103cfe76d8951014fd75d895101cfe74d8951004fd74d895101cfc74d8951044fe73d8951004fd73d895141eee52d895141eed52d8951006ef42d8951006ec42d8951024fd71d89513c6ef21d895100cfe70d8951004fd70d895100cfc70d8951006ef62989510ddf57198951005bf7458951145bc74589510f5f7715895103eee6218951006ed62189510157c765495103e7c76549510147c76549510067f63549510257f72549510276f72549510076f625495103e7e625495103e7c62549510076c62549510077771549510157e71549510157c71549512077471549510157471549510267f61549510277761549510057f70549511fe7e60549511fe7c6054951207771054951004fe7690951004fd769095103cfc76909510257e75909510057d7590951006bf649095101ebc6490951004ff7650951004fe7650951004fc7650951004fe76cc951004fd76cc951044fc76cc951145be74cc951005bd74cc951006ef62cc95103eec62cc951004fe768c951004fd768c95103cfc768c9510257e758c9510057d758
  | 18 => 0xe7655132004fd7655132004fc765513203cfc7654d320067f6554d320267c6554d32005ef7254d3203dec7254d32047cc3254d3203cfc7650d32006bf6450d3201ebc6450d32005ef7250d3203dec7250d32024ff7654932184fd7654932044fc76549320067f65549320267c6554932005df7354932045dc735493203fcc325493201cff765093217cfd7650932044fc7650932006bf645093201ebc6450932005df7350932045dc7350932014fe76d8532176f661d8532024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d853203cfd73d8532044fd72d8532006f741d8532176f441d8532176f631d8532176f621d853200cfe70d8532004fd70d853200cfc70d8532176f4615853200cfe76d813216efa60d8132024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d813203cfd73d8132044fd72d8132014fe71d8132004fd71d8132014fc71d8132006fb40d813216ef840d813216efa30d813216efa20d813216ef8605813203cff755943203e7f7559432004ff745943201cfe745943201cfc74594321667f54594320067e54594321667c5459432044fe7359432044fc73594320467e53594320467c535943203cfe725943203cfc725943203e7e525943203e7c5259432004ff7159432014fe7159432014fc71594321667f51594320067e51594321667c5159432004ff705943200cfe705943200cfc70594321667f50594320067e50594321667c50594320067f74594320067e74594320067d74594320067c74594320467f73594320467e73594320467d73594320467c73594320467f43594320467e43594320467d43594320467c435943203e7f725943203e7e725943203e7d725943203e7c725943203e7f425943203e7e425943203e7d425943203e7c425943203e7f325943203e7e325943203e7d325943203e7c32594320067f71594320067e71594320067d71594320067c71594320067f41594320067e41594320067c41594320467f31594320467e31594320467d31594320467c315943203e7f215943203e7e215943203e7d215943203e7c21594320067f70594320067e70594320067d70594320067c70594320067f40594320067e40594320067c40594320467f30594320467e30594320467d30594320467c305943203e7f205943203e7e205943203e7d205943203e7c20594320067f10594320067e10594320067c1059432004ff7559032024fe7559032024fc755903203cff745903203ebf7459032044fe7359032044fc7359032046be4359032046bc435903203cfe725903203cfc725903203ebe425903203ebc4259032004ff7159032014fe7159032014fc715903215ebf4159032004ff705903200cfe705903200cfc705903215ebf4059032
  | 19 => 0x9232346bc315923203ebf215923203ebe215923203ebd215923203ebc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bc5059232346bf3059232006be3059232346bc305923203ebf205923203eaf205923203ebe205923203ebd205923203ebc2059232006bf1059232006be1059232006bc1059232004ff765523203cfe7655232004fd765523203cfc765523201ebe6455232006bd6455232046ef3258e3203ede3258e3203edc3258e3203eec3258e32024ff7654e3203cfc7654e320267e6554e320067d6554e3226ebe6454e32006bd6454e32005ef7254e3203dec7254e32047cf3254e3201cff7650e3203cfc7650e3201ebe6450e32006bd6450e32005ef7250e3203dec7250e32004ff7558632024fe7558632024fc7558632004ff745863201cfe745863201cfc745863203cfc725863203edf325863203edd325863203ef77158632196f6315863203ef7215863203ef42158632004ff705863200cfe705863200cfc7058632004ff7558232024fe7558232024fc7558232004ff745823201cfe745823201cfc745823203cfc7258232004ff7158232014fe7158232014fc715823203efb7058232006fb505823218ef8505823218efa305823203efb205823203ef8205823218efa1058232024fe76d95321867e65d953201cfe74d9532004fd74d953201cfc74d95320067e54d95321867c54d953203cfd73d95321867f53d9532044fd72d95321867f52d9532014fe71d9532004fd71d9532014fc71d953200cfe70d9532004fd70d953200cfc70d95321867c6559532184ff75595320067f7559532004ff745953201cfe745953201cfc74595321a4ff7359532006df73595321c4ff7259532006ef7259532004ff7159532014fe7159532014fc7159532004ff705953200cfe705953200cfc705953201cfe76d913217ebe64d9132024fe75d9132004fd75d9132024fc75d913203cfd73d913217ebf43d9132044fd72d913217ebf42d9132014fe71d9132004fd71d9132014fc71d913200cfe70d9132004fd70d913200cfc70d91320057f75591321857c755913217ebc6459132005f77159132175f47159132005fb705913216df87059132004ff75591320067f75591320047f7559132024fe7559132024fc75591320067c75591320247c755913217cff7459132006bf745913219cff7359132006df7359132346be4359132346bc43591321bcff7259132006ef725913232ebe425913232ebc4259132004ff7159132006f77159132004f77159132014fe7159132014fc7159132006f47159132014f4715913217ebf4159132004ff7059132006fb7059132004fb705913200cfe705913200cfc7059132006f8705913200cf8705913217ebf4059132004ff7655132004f
  | 20 => 0x46bc5359332006bf725933232ebe7259332006bd725933232ebc7259332006bf525933232ebe525933232ebc5259332046bf3259332046be3259332046bd3259332046bc3259332006bf7159332006be7159332006bd7159332006bc7159332006bf5159332006be5159332006bc5159332046bf31593320469f3159332046be3159332046bd3159332046bc315933232ebf2159332006be215933232ebc2159332006bf7059332006be7059332006bd7059332006bc7059332006bf5059332006be5059332006bc5059332046bf3059332046be3059332046bd3059332046bc305933232ebf2059332006be205933232ebc2059332006bf1059332006be1059332006bc1059332004ff7655332044fe7655332004fd7655332044fc765533201ebe6455332006bd6455332024ff7654b32044fc7654b320267e6554b320067d6554b3220ebe6454b32006bd6454b32005df7354b32045dc7354b3203fce3254b3201cff7650b32044fc7650b3201ebe6450b32006bd6450b32005df7350b32045dc7350b32004ff7558732024fe7558732024fc7558732004ff745873201cfe745873201cfc745873203cfc7358732046f77158732006f751587321b6f45158732046f73158732046f431587321b6f62158732004ff705873200cfe705873200cfc70587321b6f71058732004ff7558332024fe7558332024fc7558332004ff745833201cfe745833201cfc745833203cfc7358332046ee3258332046ed3258332004ff7158332014fe7158332014fc7158332046fb7058332046fb3058332046f830583321aefa205833203e7f7559632004ff745963201cfe745963201cfc74596321a67f535963203cfc725963203e7e525963203e7c5259632004ff7159632014fe7159632014fc71596321a67f5159632004ff705963200cfe705963200cfc70596320067e50596321a67c5059632004ff7559232024fe7559232024fc755923203ebf7459232006bf545923219ebe545923219ebc545923219ebf435923203cfc725923203ebe425923203ebc4259232004ff7159232014fe7159232014fc715923219ebf4159232006be415923219ebc4159232004ff705923200cfe705923200cfc705923219ebf4059232006be405923219ebc405923203eef2059232006bf7559232006be7559232006bd7559232006bc7559232006bf7359232346be7359232006bd7359232346bc7359232006bf5359232346be5359232346bc535923203ebf725923203ebe725923203ebd725923203ebc725923203ebf525923203ebe525923203ebd525923203ebc525923203ebf325923203ebe325923203ebd325923203ebc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf5159232006be5159232006bc5159232346bf3159232006be315
  | 21 => 0x771595421d5f47159542224ff75595420067f755954220cff7459542006bf7459542004ff7359542044fc7359542444ff7259542006ef7259542004ff7159542006f77159542004f77159542014fe7159542014fc7159542006f47159542014f47159542004ff705954200cfe705954200cfc7059542024fe75d8d42004fd75d8d42024fc75d8d4203cfd74d8d4219ede43d8d4219edd43d8d42346bc43d8d4243ebe42d8d4243ebc42d8d42014fe71d8d42004fd71d8d42014fc71d8d4219ebf41d8d4200cfe70d8d42004fd70d8d4200cfc70d8d4219ebf40d8d42006df6398d4217ded7298d420057f7558d421dd7c7558d421bdef7258d42005f77158d421d5f47158d42005fb7058d421cdf87058d42046de6318d42006dd6318d42004fe7694d42004fd7694d42044fc7694d420067f6594d420267c6594d421df5f5394d42004ff7654d42004fe7654d42004fc7654d42005bf7454d4201dbc7454d4203cbe7690d4201dbe7390d4201f9e7390d42346bf6390d420079f6390d423479c6390d4203dbe7290d42347ae7290d42347ad7290d4203dbc7290d4201ebf6290d4201faf6290d42005bd7190d42005bd7090d42024ff765494201cfe765494220cfd765494201cfc76549420067f65549420267c6554942005bf745494201dbc745494203fac4254942014fe76d85421d6f661d8542024fe75d8542004fd75d8542024fc75d854203cfd74d8542044fe73d8542004fd73d854201cfd72d8542006f751d85421d6f451d85421d6f641d85421d6f431d85421d6f621d854200cfe70d8542004fd70d854200cfc70d85421d6f710d85420057f75585421dd7c75585421d6f4615854200cfe76d81421cefa60d8142024fe75d8142004fd75d8142024fc75d814203cfd74d8142044fe73d8142004fd73d814201cfd72d8142014fe71d8142004fd71d8142014fc71d81421cefa40d81421cef830d81421cefa20d81421cef860581420467f7559732004ff745973201cfe745973201cfc745973203cfc73597320467e53597320467c53597321c67f5259732004ff7159732014fe7159732014fc71597320067e51597321c67c5159732004ff705973200cfe705973200cfc70597321c67f5059732004ff7559332024fe7559332024fc7559332046bf7459332006bf54593321bebe54593321bebc545933203cfc7359332046be4359332046bc43593321bebf4259332004ff7159332014fe7159332014fc71593321bebf4159332006be41593321bebc4159332046df3159332004ff705933200cfe705933200cfc70593321bebf4059332006be40593321bebc4059332006bf7559332006be7559332006bd7559332006bc7559332046bf7359332046be7359332046bd7359332046bc7359332046bf5359332046be5359332046bd5359332
  | 22 => 0x855201cfc74d8552044fe73d8552004fd73d8552024fd72d8552206f651d8552006f741d8552206f441d8552206f631d8552206f621d855200cfe70d8552004fd70d855200cfc70d8552006f610d8552206f410d8552005bf745855220dbc7458552206f4615855200cfe76d81520257e75d81521fefa60d81521ff7a50d815203cfd75d815203c7d75d815201cfe74d8152004fd74d815201cfc74d8152044fe73d8152004fd73d81520767f53d81520067d53d8152024fd72d8152014fe71d8152004fd71d8152014fc71d81520767f51d81521fe7e50d81521fefa50d81521fe7a50d81521fe7c50d81521fefa20d8152005bf745815220dbc7458152005df7358152005dc7358152005f77158152205f471581521fef8605815203e7f755964220e7f545964220e7d5459642004ff7359642044fc73596421f67f535964203cfe725964203cfc725964203e7e525964203e7c5259642004ff7159642014fe7159642014fc71596421f67f5159642004ff705964200cfe705964200cfc70596420067e50596421f67c5059642004ff7558e42024fe7558e42024fc7558e4203edf7358e4217ede4358e4217edd4358e4203cfc7258e4203ede3258e4203edc3258e42004ff7158e42014fe7158e42014fc7158e42004ff7058e4200cfe7058e4200cfc7058e42006de3058e42006dc3058e4203eef2058e42044ff7694e4203cfe7694e42004fd7694e4201dbe7494e42005bd7494e42046de6394e42006dd6394e421f75f5394e42004ff7654e42004fd7654e4203cfc7654e420267e6554e420067d6554e42046de6354e42006dd6354e42044bf7650e4201dbf7350e4201f9f7350e42046be6350e4232f9e6350e4232f9d6350e42046bc6350e4232dbf7250e42007af7250e4232fac7250e4201ebe6250e4201fae6250e42004ff7558642024fe7558642024fc7558642004ff7358642044fc73586420d6bf4358642006bd435864203cfe725864203cfc725864203ebf425864203ebd425864203ef771586421eef6415864203ef7215864203ef42158642004ff705864200cfe705864200cfc7058642004ff7558242024fe7558242024fc7558242004ff7358242044fc7358242056bf4358242006bd435824203cfe725824203cfc725824203ebf425824203ebd4258242004ff7158242014fe7158242014fc715824203efb70582421e6fa405824203efb205824203ef820582421e6fa1058242024fe76d95421de7e65d954203cff74d954203cfd74d95422267f54d95422267d54d9542044fe73d9542004fd73d95421de7c53d954201cfd72d95421de7f52d9542014fe71d9542004fd71d9542014fc71d95420067e51d95421de7c51d954200cfe70d9542004fd70d954200cfc70d95421de7f50d95421de7c6559542445ef7259542005f
  | 23 => 0x6fb50d814322ef850d814322efa40d814322efa30d814322ef820d814322efa10d81430057f755814323d7c755814322ef8605814303ebf7459252226be54592521debd5459252004ff7359252044fc7359252226bc435925203cfe725925203cfc725925203ebe425925203ebc4259252004ff7159252014fe7159252014fc7159252226bf4159252004ff705925200cfe705925200cfc7059252226bf4059252004ff7458e5201cfe7458e5201cfc7458e5203edf7358e52186de5358e52186dd5358e5203cfc7258e5203e7f5258e5203e7d5258e5203ede3258e5203edc3258e52004ff7158e52014fe7158e52014fc7158e52004ff7058e5200cfe7058e5200cfc7058e52044ff7690e5203cfe7690e52004fd7690e5201ebe6490e52006bd6490e5203dee7290e52005ed7290e52004ff7650e52004fd7650e5203cfc7650e520057f7550e520257c7550e52004ff745865201cfe745865201cfc7458652004ff7358652044fc735865203cfe725865203cfc725865203e7f525865203e7d525865203ef7715865221ef6515865203ef7215865203ef42158652004ff705865200cfe705865200cfc7058652004ff745825201cfe745825201cfc7458252004ff7358252044fc735825203cfe725825203cfc7258252004ff7158252014fe7158252014fc715825203efb7058252216fa5058252216fa4058252216f8305825203efb205825203ef82058252216fa105825201cfe76d915220ebe64d915203cfd75d915220ebe54d91521f6bd54d9152044fe73d9152004fd73d915220ebf43d9152024fd72d915220ebf42d9152014fe71d9152004fd71d9152014fc71d9152006be41d915220ebc41d915200cfe70d9152004fd70d915200cfc70d9152006be40d915220ebc40d915220ebc645915244def7259152005f77159152205f4715915203cfd75d8d5201cfe74d8d52004fd74d8d5201cfc74d8d521a6de53d8d521a6dd53d8d52014fe71d8d52004fd71d8d52014fc71d8d5200cfe70d8d52004fd70d8d5200cfc70d8d52006de30d8d52006dc30d8d5220dbe7498d52005bd7498d52006df6398d52185ed7298d52205f67198d52005f57198d521c5ef7258d52046de6318d52006dd6318d5203c7c7654d520257f7354d520275f7354d520075f6354d520467e6354d520467c6354d520075c6354d520076f7254d5203d7e7254d5203d7c7254d520076c7254d520267f6254d520276f6254d520057f7154d522667e6154d522667c6154d521fd7e7054d521fd7c7054d52004fe7690d52004fd7690d52044fc7690d520257e7590d520057d7590d5203dee7290d52005ed7290d52004ff7650d52004fe7650d52004fc7650d52006bf6450d5201ebc6450d52014fe76d8552206f661d855203cfd75d855201cfe74d8552004fd74d
  | 24 => 0xc73596430467e53596430467c5359643004ff725964303cfc72596432567f5259643004ff7159643014fe7159643014fc71596430067e51596432567c5159643004ff705964300cfe705964300cfc70596432567f5059643004ff7558a43024fe7558a43024fc7558a43044fc7358a43046ef7258a4317eee4258a43046ef3258a43046ec3258a43004ff7158a43014fe7158a43014fc7158a43046df3158a43006ee2158a43006ec2158a43004ff7058a4300cfe7058a4300cfc7058a43004ff7558643024fe7558643024fc7558643044fe7358643044fc7358643046bf4358643046bd4358643004ff725864303cfc7258643106bf4258643046f7715864324ef64158643046f73158643046f43158643004ff705864300cfe705864300cfc705864324ef71058643004ff7558243024fe7558243024fc7558243044fe7358243044fc7358243046bf4358243046bd4358243004ff725824303cfc7258243086bf4258243004ff7158243014fe7158243014fc7158243046fb7058243246fa4058243046fb3058243046f83058243024fe76d954323e7e65d9543044ff74d9543044fd74d95432867f54d95432867d54d954301cfd73d954323e7f53d954303cfe72d9543004fd72d954323e7c52d9543014fe71d9543004fd71d9543014fc71d954323e7f51d954300cfe70d9543004fd70d954300cfc70d95430067e50d954323e7c50d954323e7c655954345ddf7359543005fb705954322df87059543284ff75595430067f755954326cff7459543006bf745954345cff7359543006df7359543004ff725954303cfc7259543004ff7159543014fe7159543014fc7159543004ff7059543006fb7059543004fb705954300cfe705954300cfc7059543006f8705954300cf87059543024ff7654d4301cfe7654d4326cfd7654d4301cfc7654d430067f6554d430267c6554d43005bf7454d4301dbc7454d430479c4354d43024fe75d8943004fd75d8943024fc75d8943044fd74d8943456be43d8943456bc43d89431beee42d894332ebc42d8943014fe71d8943004fd71d8943014fc71d89431bebf41d894300cfe70d8943004fd70d894300cfc70d89431bebf40d8943006ef62989430057f755894323d7c7558943005f77158943235f47158943005fb705894322df8705894303eee6218943006ed6218943014fe76d8543236f661d8543024fe75d8543004fd75d8543024fc75d8543044fd74d854301cfd73d854303cfe72d8543004fd72d8543236f641d8543236f631d8543236f421d854300cfe70d8543004fd70d854300cfc70d8543236f4615854300cfe76d814322efa60d8143024fe75d8143004fd75d8143024fc75d8143044fd74d814301cfd73d814303cfe72d8143004fd72d8143014fe71d8143004fd71d8143014fc71d8143
  | 25 => 0x815428ef830d8154005df7358154005dc735815428ef86058154046bf7459253286be545925323ebd5459253044fe7359253044fc7359253046be4359253046bc4359253004ff725925303cfc7259253286bc4259253004ff7159253014fe7159253014fc7159253286bf4159253004ff705925300cfe705925300cfc7059253286bf4059253004ff7458a5301cfe7458a5301cfc7458a53044fc7358a530467f5358a530467d5358a53046ef7258a53186ee5258a53046ef3258a53046ec3258a53004ff7158a53014fe7158a53014fc7158a53004ff7058a5300cfe7058a5300cfc7058a53004ff745865301cfe745865301cfc7458653044fe7358653044fc7358653004ff725865303cfc7258653046f7715865327ef6515865327ef64158653046f73158653046f4315865327ef42158653004ff705865300cfe705865300cfc705865327ef71058653004ff745825301cfe745825301cfc7458253044fe7358253044fc73582530467f53582530467d5358253004ff725825303cfc7258253004ff7158253014fe7158253014fc7158253046fb7058253276fa5058253046fb3058253046f8305825301cfe76d915326ebe64d9153044fd75d915326ebe54d9153256bd54d9153024fd73d915326ebf43d915303cfe72d9153004fd72d915326ebf42d9153014fe71d9153004fd71d9153014fc71d9153006be41d915326ebc41d915300cfe70d9153004fd70d915300cfc70d9153006be40d915326ebc40d915326ebc6459153465df7359153005fb705915325df87059153044fd75d895301cfe74d8953004fd74d895301cfc74d89531c6ee52d8953014fe71d8953004fd71d8953014fc71d8953006ee21d8953006ec21d895300cfe70d8953004fd70d895300cfc70d895326dbe7498953005bd7498953006ef629895325dfa7098953005f9709895303eee6218953006ed6218953014fe76d85530257e75d8553266f661d85532677651d8553044fd75d85530447d75d855301cfe74d8553004fd74d855301cfc74d8553024fd73d855303cfe72d8553004fd72d85531267f52d85532667e51d8553266f651d85532667651d85532667c51d8553266f631d855300cfe70d8553004fd70d855300cfc70d85531267f50d8553005bf745855326dbc7458553005ef7258553005ec7258553266f46158553005fb705855325df8705855300cfe76d815325efa60d8153044fd75d815301cfe74d8153004fd74d815301cfc74d8153024fd73d815303cfe72d8153004fd72d8153014fe71d8153004fd71d8153014fc71d815325efa50d8153006fb40d815325ef840d815325efa30d815325efa20d8153006fb10d815325ef810d8153005bf745815326dbc745815325ef860581530467f755964326e7f545964326e7d5459643044fe7359643044f
  | 26 => 0x6802004200500b800400000700180000160000058088002001003003c0000050000010000003001801c01e000000800c004001001001c00400d0000028022005001800000000000b001400000400000080080000070000006008005800400800600000040080000008030044005000800800000000f800004a005001004c000005002000000e002000000802000000e8020012001000000000401c00f000000a00300b807c03200500180000220040008010002000000800c000000002002000400f001800000c002000801c00200d000800c01200a0000014010000003000000000000d80080080060030000018000000801c0060010038008004001001000400000300c8014002001000000c00800c014800000c02a0020000002029005000c0120180008058038000000800800400100b0034030002001002400c0000020000006001000004800200c006000001e005005000800e0000088004006000005800000a005005800400000e00380180000010008004012007000006800400400880040100000030028000001003002403800b0010088000000001002800a019000000001200000800000020010008008002002000000000a0030028020010001007802000c00000200080000000000008004000000000000200202b0000000000008800000400a0060000000005004800c000000000002000000000080040020010020000000002008807c0120000000000000022000000c0140090000018000019006801802c00200080000000020010004004002000801c000003000801c000004001000c00c000001807000e00000580ac0000000008030006017044fe76d8d5401cfd75d8d54024fd74d8d54466de53d8d5445ede43d8d5403cfe72d8d54004fd72d8d54014fe71d8d54004fd71d8d54014fc71d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54006de30d8d54006dc30d8d54006df6398d54005fb7058d5428df87058d54046de6318d54006dd6318d5403cfe76d895401cfd75d8954024fd74d8954044fe73d8954004fd73d895444eee52d8954446ee42d8954014fe71d8954004fd71d8954014fc71d8954006ee21d8954006ec21d895400cfe70d8954004fd70d895400cfc70d8954006ef6298954005f77158954295f4715895403eee6218954006ed6218954014fe76d8554296f661d855401cfd75d8554024fd74d8554044fe73d8554004fd73d855403cfe72d8554004fd72d8554296f651d8554296f641d8554296f421d855400cfe70d8554004fd70d855400cfc70d8554005ef7258554005ec7258554296f4615855400cfe76d815428efa60d815401cfd75d8154024fd74d8154044fe73d8154004fd73d815403cfe72d8154004fd72d8154014fe71d8154004fd71d8154014fc71d815428efa50d815428efa40d
  | 27 => 0x1800100b000000000b001003401e0030000038004002011000401a005004801401400100080040300000000024000001001803000000300b8014000001000803000a005000800c00c007000000002601200000040000000000058006001000804c0140110020018036000000003000001c0058008000006000800800e000002803c018001001800401600d004000001c015000800800601000200ac04802a000802401e000000000800400000480180140030050010004004000001c00000000080240000000010010022002001000c018006002000000400300000040320270000018010000000000401400d018801400200700b0008000002001000000e004000000403800300b8000002002003804000200001c80000000010040024016000000004000a004001800c000018000805000000e003003400000000000340020010090000008001000001c02600d0008008000000002000000000b0068000000004000802800400f001001001400a000006c0160000038004020003009000c012000004800c00000200480000820010080000000001011001000801500000000100020010030030001000000c0000170030008004002000000000600000000840100070010000002006004000c000000000000002400b005007c0000000018014038002006800000200000b0000012001000001800e0010148000026028001802800200000380000020000008000006000000802c00200200180080040010000004004005000801800200a0038000040000001006c0160000008018004017000000800c00200a800803a00000a000000a00400080000320030000000022001000000c00000100000000160010008018010001012000c00601b0018000020013001800c0020010018000006002000801800600000e000c00800e000000400a000000001c02804700000000120000000008006003000000401000d00080140020040030010008001000800c02a0220000014004002000001c00a029000001c000010002802402800b002805c002000001000c006008001803c00000100900080020050040008004002002801c02800e000800402200000300180000000010000008007001000002c0090008078058004000000c0040050000008002000001001000200000280a000a00d009804c0020030030024012001000000400001d00100040000060010014000001000801400400200c002000200300a803c012003000800800c00000001340140090038010026007000001002a00100400000020050000018008001000001400600001f00300020040030048002000000004c004003001000000600f004000400001b0000000002000002004000400200000000060040010018004009003000000a002007800803400b02780100060090050020000
  | 28 => 0xab06f118fa5f0034800000003830000000000000021ea80f991e38e14288cd0000024887c0000e3010700006741fd000000007af119e3be800000006e42ec80000000000000000000014c47099fb07dc892a000000015c80007ab0000000000047c80000000d0c8bb19a457604f489113f0297987c63c2028803123657983023d91be06078df86ab1e840538e2000000001a2a2860000000699a07a31c21c0000211239811f60e482dc6ef113049d8a607ba800000018b84b280000001a5882f98d60c400000000000000135e8580ab47fd85685820000002000000401c0090040000000001004800000a00200f003800000500000180020090028024022009000800c00001b006000c02a0060040008000000001004800600800000000000060000014008000001801c000002004800400c0060030014052001003800000c0040000004038004000000c02400c0000038004000000001000000b0000000008001000005c000000004004c00601a003005c00800000180040000000000000002000000000c004000005801400c000000000000e023000001c00400600000000000040000028000000000001400a000000800403800000000200000000100030004005003000800200b001000400600400c800c02a001001000c01000200000080160000020008002000000000000000200d8028010002002000c0000010068004000004000000000200600c00140060020070018022002003800000a03300b801000c0000000008002000005000000000100280000000000008000002012005806401201000b000c00c011001002c018000000000c00600a019000000a001005802800200000000000a2006000013000800200700240000030008028002007005800c00000000000000080030000008000000000009400a00400080000120040018000000007001004c000003002004c00400c00380c400a00c004000400801700100200020000000000000000000001c002004001005c00200100000340140010020000000000000000000401e0000000004000000800c0000030000000006002004804004600b000006400200201000040000000000018018005000000000c0000010050004033001000c002000001000400000000180240060060010000004001002001c0000010000044032000000000000401f000800c02000201200080040060018018006004000003c016002000801401401f0028008000003002002805c00d000001c032000000002c0000220008004016002000000000000b001803400a001003002400600500000180000110000010028009003800c00a002002001c0120060038020062009002800000400e0000014004003000800801201d006000000401600a80980040000010008004000007008800a005000000000e000000
  | 29 => 0x88f0000000047200007bc47618c8445886a00017982689ba2000000036480000000000000095e23d94740fe939e65984fe5d29ad43b200008c79e660f08000137a0c263604d682a9fa470791a248282f4000000078289501d2153c5e822d61df9264452803e6d40b3e25a96ce4188564008082633c8d165f2000069c980c623800050300007ef05de0e70fa647984bc32615f25008b44167073232286a8000062a836210c4f4036a13c0f8621b00000000b5250510506e2802400022bc00000000001f0e74d0c127598f6672f9afa3ae97604db000083384d85280d6c5de16782f7a2be5851c2885581a8449004a73816cc667928a58792004fd06ba6ed926604d89aa046946a17a14ec487973c43f98183c596b45158d323b1000029a125a66c8f8419a9a9258c8d4c0ca93b87b9000081903e63f5860226900ae6760000000194a0000000380800000000007db1e9a1d000000000ea80001cd86e50a7200005b00000000087041210f83ce76300000c514de0000cc800000000000000183800061480005e20dfa211a10604600000001f8032d91be3ca111014d804839006ac28e06d87a400562561ed80000c74000000011502764429cf008e0e4e25e9cb06b39cc02a31ca024c850260e02cc77c8e4a273150e08201e0851892465e807e70f86384d484c834e04a85fc05b44609f307781b162eb9edc7fa0a2e2dd00002aa02ba1ee96ac53808ea40702d04cc9c5a09c8af202680000210f605f8800087b19943e50000818a134000083e00015185d8a0e47bc10ce613a0da2a81e268889ef27ec911412c9a2e825819668300004d900003f304865251fa2775950c000048430280000000000000115e1d180001f7180215095288ab01e405004cc0000e0083280000000aec426000019e92cc0a5807600000002fe8000000179e57d8b700000b4e52a80004558000000026a0818050045021800001ca3ff17b465e00006b404245e880000bc800037800000000000000000081180000000fde02d00000000d9c000230658a0000000201400005ac00000004ae80000001b9000012123c191260000a1a0001ade00015dc0000000000160683c80000000000000113c82b09f666281ac01392d44a70dea6b29f3e26a112c4720b4861899a01a607044119e1a2c58d084cd03fc5870ed27d2055c29f8b0a0759d100089fe68a815063a016b807996305f1996227d211e50c1ede5f80000000019461400000001960158a2d42f910726ff938c059983a7a8180424e028a5a10bba474000084080000001b124358c7a7ae131201a9efe2200000000000027100001d91682000191c1e10a5221913625f5a0741b8167077995d61cf9ea887f94428089d3084513360e9821a0cca1d61a2028433506c44910250029905e6e30a464c3117408fa11c4251d364b60
  | 30 => 0x156800000000002610ea46df00003a292b8057041474502202c000001099040573053e5cd075471318d03e902fe000069e0cd94f03da19186e3800017094b06a80edc350000069a116e2b98452369217600000004c69568206099435c0e980251a1020d8f2c803a2140e818d200b12fc0000e8c65d80007058b3442b04347f7a27e3131d86000000000001c65271644000147c65000002d40000000000030a1f4482180003ee00000000000000000000013086ca881a000000006e980e69880000000ae446c800037214760e9035458800004e9101843a8e9054c935c0001664596800029f00000d9000027a870a0df19f000000000c612c456b0316407981c45804ee5bba32a2438036000020a49e000065908a60da1b5e52a0efc21ca0b20b484ac1dda14e3b310e650200002ed018200017d83ea0000155911c278800078b0e360001e2e6619e1800000000a0811060c8ece7650000536000081a92427bb80007040f8a768a00080c0d506bf03207d710e00001aa27fb223e528a1988c5220838a9bc65bc86622850e6e13d87be70f0f5641d800006f9d46255142222087e433994dc7fc80006d6209804309d47a183ea5650174126a2801b384c2451000000000000000000000182e84c18424c7835831010b282721248869f8e695165e397117e8178eb41e71ff01aa898e24e9f7e40e92a22e580e03b884e82df20b62ed9e5e2ea188641a00000000f243248f741619c0079a042e1530d3629b8eee3ec034238600000000000000000042d183e000000013c8fc42ca9f5800021c6000112e4310000000176827e80004d500000000fae0000000000000000000000001b5a11d00000e2972e6e9914e35a0d987bd111a08116102a28ea02a59648000070e0000b6e76f953a4a022120001674574000073a00003008ebe000000089a99ae0002234000098c00000000000c5c00019ec0001d264ca13dc000000073080000001d4000020c4054800071d1c7644800006100000000000056e935a00018f60001d4800016be8a40000000000027400002f815462d609223b1a1cc000123c883000053000002de000007a159a0d1800081f05bc018a2780000000000000051213a60000f46023a1381b99fce44e87903a7800000011b68bc9b7830f916200003f80001bcc20403da000169e2121aea79f085e5f394ac2a3800000019020001bb4000000054d000059a000011711da00022e81de1fe22fe000000000006b1800023f129a49a16806a6037000007ec65f13da0000000207000040aa0c049d0af008b80003a5000000000003c08fa2048800000000000000000434800030d81005cb0910216a0a03689bca7cd0000000000000016a68650dac57522ce7fa810447588705c70000201000055d0ce221396f400009145898f141f780000000e3e
  | 31 => 0x838880000001d8a799000080580006a221ca0479b7e8358eb88c08ff61dd1d9e856104c5dc1a4e7f7159e0000000000131c0001d6c3469a9010000005611db235f0ada00011ac63e1136000000072505181b2800018f022200010fc72e005800b80004b480007f01b8017500000001c52191900c00000000001f0015e800000000005a197aa6c713e001b983400008b203d01980000c20710800000009204e0a13a280015079496ca1bd0a7602a00005671b6600012ae2f30286000137803f0a644e202fc8ad986a0750bf085e8ed6253118a4478c2e0558fb600014b61d71c1a00005940e788500c002ce00000006bb21ce6d29fda000000000008b077d000011112ee62c82146e1096849c80005ea00004f08158523800000017ee2e99dfc2c680000001a2402e00002d7a07020b830e30581fa0001bce89b824800000000000af44c0904800021421e286ea0000a1e781800011600004308000000178000017b63ce88c400006300000fe44a090425cc80000001c2230980140000000000000075780d43aa8d30863800053200007e508525e480b68960ee00000000000000000021540768e2c33a8f442f006743fe09a0581000083e19fe819956600006107e3147a6048962000193c7cf00001249726000046e721140016280000001b5600000007a200008579f96330054e00000000fc182a00000000000192000000000000000001250000000052d0a10000149e0001b108a8800024084be7278000000000000011e81ec80006bf83d8000165824480002a696bc0e41f5a000000020f034a83d975a73a800051014668600fce48501fc1881ec889595200d991b4000137e5c485662ce1b4646a201015a800036a9f46557022865b800040e0d6400000003c9800000008602499c2e6040ed479c19d64931a5c00006fe7bf0d94013217c0aaa018000175c7b59484000000034fa03414a857600021b087696906dc026e3dc800000000000308f0c5ee87fe115926250f00000ba203800013208bb839400007c600000005550c7e01c800000005380001d803f51de204b06a6000083a3870fbc4641dec3621b6c806977c14689ac0001d620a500520000f760000bc45231c564639e487b10644798a04e3bd8d107eb8000000000000000002c5000089080003a196c46eb0cac8761844000000077a80001d408d65948c048410d002e083ac6c9817a027800005d84324151f5088c0c2212394f88548af837996fc00000000001c18374800058d800026e000068e800000000003571de87eb1f3a19a1982822952a70218544f90306000140a00011004280a5a0000292839800005b1aa42de85a04e39bba5f1034c6a306564a5000042420dc2e38e74000176e66584c63b0026482e96fe69588546f88b8c820190c2599f2c6398eea0749f4e6b9836c000
  | 32 => 0x785920be016e8379a7c6e59ca2134983c13ea2704c980000000a94000000000004ca00000000001b2c28d19fc091174679e176627593cc7a99ffc1f894c64c28e883ef8fee4fba25226081460ad812447e09162390afe43e90f212b8e1e5768cb24f60f402d2846a1d583d64f00730000000058a9cba30511581fa06d054c15c4062151c0b78cc42a11a000000cce30906a289895a837c00007ac89926fe114c7030bdc1718d06000000005e070c1819ce45498960545040224796a225c0c783160d1e3c60000000000025b21fa8c90000000000000010888c899c4000000000003e04d19cd2199000000000000a40a9200015ae82b8c6e0001bc00f1135825c803c54f810a4a107ce6e683ee2e884e02a408aa26d844a000000041b800064e800043e10524e41b88000015a75c0fec11e1dc200016026c9080600014f248317586468d743481e5887e00003490bda0001d6a073163c422800046722762241f866bc0d6a43c1f6a66e192820a8cc269a88027121d7447d03dc82d000000000002eb122c00005808c0000000014a4000000041b15704300bea662025846211ba62602262e0165c6dd8000472800048608ec1fb800046b985e584805c75a1aa6000000000018cc31f226c000027c384000000000005d30000735068078d8000000141000000006e80000165871a73980005c511b8569918441683528b20f5e1bd8a327ea196821a0f584bd84b652b9eda33f08b458399a6504849472a95a223e88b830e9bb00690ce850613ac1419cd6000000033906c20001c12489800034080006e480003b4000018e8b2c42ea2b457d00004211086845a2547db8fc85ff100a73e800024f1dbc5bb15385e1000035380000000eca419125800000003a4942a45a0c5625f83c6000000082f000000012ce000125e00003f236693aa0ae1006542000000000000000eae000000000003de000026c000000000017443c700001c48dc63569dd40000e347b8000000000003c89522000061a00008e28608762000096e0000d047e1000031d91fc02e99dc000000024f80000000000000007c000000000016e800000000dd0000129188a6881df607b16ba0001f9c4838e0830c0dba0001b982c800000000d2200007d60000c5a000000038f1ae00001d501ada06c2a00d1c8c30d525cd99263f28cfa2cb8df466719f600018e40000000000000000018a07c5800032e0b608a69cde0001a8400008ba0789d9012a91de6ea10321f99f925c380000001dc014900005a2921619797bc3cd15a45e9088850b0b0650d8d540bb205a1548ff451892d644e0e5a5a221a861a15502e28fd217b14321c19af4000045e48a00007d9800058680000eb8a4834f049e1e08c422ba92961a71a800169b005389b326f986043839c983ac98b0000000064800006bba1728cb16d
  | 33 => 0x6a0000cf8000174848a80000000000000036e00000000000000000000035080007f80f380000de232a1fba00012c07809d8e59f14bc84a09ba000a16c0001cae00008e84a38000000133e5fa800063d0b5a3f9838e2c400a465422fc0af95f035e80001980000877800003997f4000104a000032e690889654921905980000000132a0b5139281800000b1063648203be3d306dc5191b863b78eec1ae1c2c0020ca4072049c0000aba588800000009a651e000012880008781f200001f5223280008b1140657a00001b00b7e40923042a8a0540001d0000000000000000000000004b8f6e34e83ba5dea3185201a165080e4200000001d9800040395922170aee000000000005b20000000221a21c000061636a025c00009f23899c600f4000000003261259b0a1341adc737000043689743149a96556857e000124a17d060881f80000000000432820c6248ef0000186e00000002431c0232988a400005ae00006341e2231639303ca00010160000ade0000adc5fa0b28734061c534800021611342c38b5600018aa20280006d10000000000067294d66a71122564048287516b08a700008489bb80000e62051133041980002b29ed211200003d08c5011e80003c782ca36420fa7e780004ea00346c2000000007987c4000030b164c32f8c188b8189e0ab80000ab00000001ab83519a3c05aa174266800000000002dc917c000000000000008438e0a515000011a0cbc00000000f3043c71900006a1917203aa312138958a1d79d047aa8ff04ad8da0000141c80b1bd60000cde0001e1239590dc2cf00c6611830c44c800000016e67f10ad419e05a8000000069e91e02828c1e03018ae20897d01f281dc1039204313986440494ce10c173a5bc00006289e4e823922e00013ba09f800084020681c919904fb00000000006558050a54780000000d1416e14825d38936000065012c000a751000073d000006380008091b3e00001b6000000000021e454b851200000006888e823d502d82dd97f271b058c09000005950bc60689b4e0001fb4420970a00002bc331868c4c585aa7cb909231816a00001d243a39d546080a863e81dca8158090653954414417e454d80002368dd40000a7a85fa31011907261fc000080700001478a36028179a68a1a3e731889839109962380ba474e9c460001c247720b66213158216e81f224a06f25a3a2e20001ee213009985be9a6e606818487f0ca23e601a04f4800086b800072f000023207f469e000008c800017b8e7e00011a0756219a0000a421d4960c00019c22db00002ee000023f917069da24c4ab000040516b218f82300d0000000018be2f0800076a80000001e144f894f4000138000001ce76b95e08ba97f68b099f45dd878621e12c6000076000007cc7328f1287a1d0c29b1ab4486800076d143a09
  | 34 => 0x83046c000195a00000007ca800058e00000001be80000dd83f713ea00011c675f0f0a0000000744936e880185617e000089c80dc0e08e14396197e7f48be23e3a04c00007fa5b8000046609ae49c0e6a86980006930b4c54281d00001bde2cd93d61e318e0071101a06983980000fd07901e8a00015f801794340000dce60996ea7ee22b84dc800004d1706000055e2aa9d1672d0ac432d03761e79bae3f090aa1ce9a120b191c44c11a5233da2e485b9e9e34385f080f19ac5589dde6f5155800006768818000283a0a80a3911803382c07be93384ed06666c8902e00000001c4178e2e2000000000000000c3267200004a600008240f30000000070c1b747e6133a2471b54829154e1ac9e425aa0ad851a1e281eb9baa80201f82fba2880bea3208978f3e0ed958e7b41ce200002a41b8800032a9d9274b00642e69db01b30c9c63b9f646b91790022a1dc47f93608878d864e280bc264219226c010888a8820400990a4b086e84be02100000ad200006427469d2a000056c71408c26991d180000000000062875e9d8823316d2000000053a80005b5842862d0dc4000071400000d675f800000020824e68a083bd081684c81b42521774034a19e1f108f032407442e1891a5eb000042684041c01c362c9209e6b5876e57a90746210d4a60209dc66d00f02e4897c1cf18964aa06ee1500cd65f69958455176c45196c88381cf86e710a42f59d5633c1be43c2178a30195b62859b684438000473000038e9dfa0859a8e58d1616175894a42d8000442066c200117809d18c649820205fe9d386ad85307428086574855864f800020c8000386800000008840000d8c86101fe6d200000001588568192a15c00003e70000052000013a926a07d186c7c480000000d2a0f480000001796000137c09e099c5351cfe2e10a2c08d22460e20000000053a51c91c2000038453e800000000de0000000717801a18b9cc80000000336000000018ac7bb0eda70104dc00003e22f202980d694ee6fa8a9e070218a36f85ce03e00000001c9c00014cc312876c0001c6e67e824c6f700002b00000000202a36c18308171572098185a6491da634a09de05c1b407892294783977e51f86b02c6092c7ab8e548c21d784e59150503966c4d09f6067e0000000000045201d88cc088e00011dc42f1a305c10b4619493e88892166000187a61999ba52288f80b0939c5079a142768f1a250229e7dd92245c3064077ba2f487087702d888c014f1bbe12e00004d41186234872e60b051c0b9054442e1c7c72221f02110f904b21f026da85262b400001fd9d4e7170f1036980be423969c4bc861e81d800c0001b2e0000e0413984ba000026632e9db81c708f26be0e7c1781e2228e88ae8b4800020909e875c96c25fb119200000006c080000ac000042a00004cb800039491
  | 35 => 0x221e32000213e08a83f66af030a0000c1c000000000000000000612000047e000214a55590c613e0abe7530e727488d7e2988c82829880859d934c1860c345579dc400000004af94b205780001fe1702041a12c28a8b0c00000000001b0e79505220ce22f62e500008938bd40001dd2000000068b1e4c2cc85e24da000043da0447ed9ef67f209f800022b022887da00001ae04e00008a382e0000172074f00001a804b404091d4000190806714be68c867255302f05ef800078e22de3368254036800087c960a4598ebc00000000a895424b905ca0000ae26ac94160001f787661b1e7b398c4676969433d12022f4994206403ec882833a785980a000000000000000000bf479e8b30000000023383446578f321929d323769a8200000000b5928c4d38ab262d9b7274a000034ba298683952c58b000086880008521aaa8120d8e8a9084a66f804226d171051b8d8a640230a000072224d072022786fc56e037e6ff20b80001f4c1e383b027f929e6cf0d7600011ec6b480007691c6a17e86ae3791c9a000194444495780000f5a8aa12a600000002419946000210866f18fc3bc9a7e000022c5298000000000029598d4000165079d8c9e3001fee154000006a9ca60391c920a98d846ae8d667188bf2000115c0b880000000986000171a69d1e3086800007e98db6302090400000006781bd047a80000070000000127a57f868420b1a3639211d200000008330000826a14485a1a1c436066e22d85ea000000017611a6000072802b00002da00004bf8f9e01e00000001dba00000007cc8000000003a48180ca1609d6e1028000000000040819484e500007d0a1ac427818603212885d7a2ca00000000198c6669c035e35606d641c041a61306a41e9887a40f05345341dac8860e162960000000214033b9ec60001a0400018a6000164210e81de4f500004de9c4a800894e450a1ba55e9ea24c50856000218c104156a0628e6c0000d4436e00280001a6c00008927b0000073ca2f000000000001f9a36590be7ae88e600000000ec9290255800008ea0527439df064180005b5000000016467d78c6800000000001a18521918c7fe800000000003c0041e1369b3800002882351bf0166963a00002ea1621e987018000197000000000000001640000000000003785dc9cb64f780002b59ad879d00005cc134800015aa488098a24c0eb01e005d26af852c58b800008f000070c9e468b985b6859039a67b9b4c193119436f000000012da8b406b4524848037d800041a89ec3dc1ab0000056000012a07c8902c6b3059e0b69c7e26f89c032214b800022fe4a180000001ee844a86c63eaa2044b800000f000000000000000221010180007ce169a74f9c3a4e112e65d480547f594967a58a2800009e459c80002861a4443400005fe07a20059a941
  | 36 => 0x10e487419e679b14e638a062c5790f520002292281a0362b395ce8351d4a6829bfa1350a9864da23a1e818c20a79fca51b0758411095a666079a4f39e3a4a48fc63a98842626832c51793c87b098360259e8c87d00828348a0465aa1bc1a696e4143944440a12de4f99c96142044e000000011699e44ec1fd87218fba633958c7ff82ee3d280e886707c2899168c72306323b980000cc110480e800000010c800000003cb800027193244bb05165c2157c3890ab84ed993800003f423b8000303a27a5e189c2123062604585dc8540718682145a2b2052848d156e00002808100cd200021e617221ee370109c6fd800056190e24be877a4431254007800025184908ab92d06c68efe39c0fe23ca84161700cb073f1f4a1e49cce7f186f05400a200f522b24e88b9e000000000000006f21c820001dd85a91b7a00000006d90baa846800041e800000000005b199164600000616017c2318000671800032b800000020ee00000000948dfe1699a505789f2436b850c000000066d80002c499a889699e20000bd042b8aae0001f548ca19127870dd0673184a85aa0c643780004bd187229e00004dc232662900000000f9a65702363e20ffe2e8090a04f8c4400017fe0001e108aa96562269800000000000022665f3007000010968b6080e72a12a40ac85da00012aa000000079c800051c00004ef80000de95c045d80007c218ea000000000000001f216185170b082f39f1c30e0d187e0861400000004d9800051180000000f9681c9e1e000000000011408c700000001764000125c2a9000021897d4000083000001640d721be00000000448f206aa025a487031235c80005b717ca89f0aac000020200010b02d0800016919f200011aa342933c4ef0c0c53d96002b30e787569c385ee08be0000b64638a19661e21aa748000072019720000f82796949a139000043300008160a504da800046f01f66fc81540000c9a73b000056f80007e280006549b144af000019f8c9606e226088c9d4201b116c3a89cda00019100001e4a43d192c00015121ff1a9a0000000090800048e13ca000027037b09184001b302a080002f280000000f0e1b4894400016d000993a029504ec00000003580bd800020fc65c212621d83c8103000000617e677722160000000000009c54687167c315b484a99a281091ee84f14fc0000b1e15b841861d000020d0dee0dc80002be99b00000584000134a57f09ce3778224360086e89718144299f1a4841e3c0849a5e4ba1d027e8228a00013c614515bc1a091061faa004000089c6b1233209a1f744788f784231a4a00011f0797000077e000000017381950000000000000000985529c72834198c00000002b192b07081340000134467a000039d84360000000000000000022f878300000001ada1eb00000041f064ec8
  | 37 => 0x94ba87215ee798089484422ba2ef137631b032849f1e3e1f01d1c2c118c089296b659b9f1e6221d6086206002c998ca3730e6449b1c145e7174028f17c27d000005c91a0602c8f6a530912810a86de65d167a49180ec15f06be509230e2848fea50f8c46000000043b087411998823a58000513849801804c42370362689906047399800c89992723a14c38c82b45a6156c686800052408bc3d88d2c27f07b47a0917a3448bb075901686b89b06456800009e804010807d83a68ff2415a13674215de262113e51294da0530e12114058e7ea853236c8ccc0000396011857809885042b09cf600000000001b2806680001e501727c61bda79b9722228123269011522889e9429a9e502809dce39418162e6104e0000fac0d80a241020000000000082c22205728a6649ba2c04171ff871000006611f6200000000001c1c0000a5c3918d82338228c67a9eca00012481cb00742ef944c85700007f900002e7000079f86d40001b04357923e3b91b5c04e9bec3ba07726639dc66559f2817122961338462514a1b47ad8a0c79101bc000222649fa1a400000000001f566e7806831a9516000081e00007a835207b617f96da000018c000157603615b059a985c7c518f272b19544c00000782208400016920001c7a7e4000018280005c600000000000000000068780000001bb22ad84460ea1fc24c380002b80000000000000000001ec000024b8000155222e7c1201e0001b62080095c37285900ef000047ea2280bd80000000000000000000000002748e5e8788a1c1c09f7c40d80001f4154880c8000000000071a0cdc1ee01ee49486fa4c18c2a19f03e822b057432189ca8b7062402300000001f2640f800063680aa63a0bfe00000008a10520828800075486c85e0800058900802761564000202e4fe210a0ff800000013ae00017ae06000000001eb0532800025da32e691842c64c800015298287a91c44000000000005be6f49c8a0ee204a3ad8a9c83a0000151812883b00fa205101071c12b43281cee39a0a4e3211ed412200000001eb4000029a1a40f041298c1000001f027200fe5ca92562d704a067000006c30bf65261a028c685cc1799b526bd9b181c780f673300002bf167e32016c05f7108083f97002a99bee1da0ae86b21fcc71e11643d3976a62a18064c412227958e9c78812e27a38fda7768eac3cf02c85e994fe87da20288e137433b0130179000068a95b274ba1700001ba44fd800000007a400003a281b8a4a1be14887669058566050040d171613f01261130d341109fd472c82e68b3171e0508cca000000000000000000ec25aaa28200010ee78d1cc45928000000000000000001ca800000000004ac9b420929b3a0001d0661c1dd00001666000000047900007730c6400000006240a441a510e88b1859836d010e5e32248
  | 38 => 0x8b69f6814b9a341181b363cda1c43db000089400b000000000000000540a2fa86d942640c0ef85b8876a000000088380003ed13867160160000030819617503fea08c56598fe1a4800000000007b98fd84cb17287ef8b40409800005f94384408f505441d9c31c81621b680005d0868e26f000081e074e000000000000002231b8200000007fd03862900000000212061f800000008665011f3621f99d4861800037700000958000000222c000000000013fa37f1a5a57190a22fb000032320263e480008461af2236065a6749ae83178a88289800055f800000022740000e7a0000000779000000000000001322000073883200005a591a40001e92780000055480003ec9b60000000011f000e0000f486a79f7000014e82af188000000007c2800000000000000000000212e6410012000000000000000001aae0000000034090000000007a018bc7b300ee00019304fc80004c618ba57221b21c216ae323a1d20000c3c03310041a199225391c0a1cd0b3a29c000050ba2a666a80008028f7a20e1b34692000083a8f5c0000000260000005280322bd9196490145036785d00310b54000003070d06bc000194c000000031505f2645196c00011b00aa0bfc5501ac00a705fc26793fe000000009385f60cf907c29d17566fd000000018602f98d780000a3e03c800083d000000018ec35581b285e09b25938e842c71dfe6db9f880ed011c1bb0000001000004a80004089460724034e0000c1a27c00005bd8fe0318800007a9ebe23d000000000381df1a6033f88d04701a8a6120cd07039e0437a189c0001da8765800001e96623fa000070a8d6e4bc139857b200658f9458325158064d1bc25b7879628c05a268e07f211c190e3709d8411000000e300a2000209422a0000000208838180e27de843808399ce000080c00017b2011000057e800000018dc000074a2e4173e60913560000476000124e00a864e0000000000019e1cd9e2a00013c400009e000000002c880000a803aa20a187600009ee5ec013c1d089780000dd648c0f80000074c0c700008568000000000000012ea1ea8f7e5708d623120df229322367681e9c7608fc039993fc00003047479c4e64b9008210012025086965d500000e001c2279828c10897d21f81e6a46680006f6021e23792dc0000b6a506800041f80000cd00005f79d763df17940919db6000000000000001d690780c78d2675703e45be22687150be80000000000096400000006b0813200018de0c9062248e8000000033c0000000804895224207d23b607d483c1b203e320e260888120d5a0501521c668900e2e858a1b812290d406c0670824988c0d418941921ca4666831a541088a6779ef82c0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87c86dd562440010fd0fb2ac4880030f1d365589100043f438cab122000c3c74195624411b8eee232ac4880030fd9774589100061e32ee8b122000c5f65dcd62440018b8cbb9ac48800317d9473589100062e328e6b12200487e87dd5624400717d0fba2c4880030fdd774589100061e3aee8b122000c3f751d16244001878ea3a2c48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880032b1d372589100066639ee4b122000c7475dc562440031f50fb82c4880030f9d365189100061f3a0ca3122000c3f655d06244001878caba0c4880023be1d621891000556422c43122000acc8358862440bb8f4e1b2ca48800a3e21970949100043fc2aeca9220008bf845d9524400717908bb2a48800237e0d76549100446e41aeca9220008f7815d952440090f90a3b2a4880031e940765491003c3f43ecaa92200087f855da42440090f90abb4848800a3e21970909100243f42eeca12200087d85dd942440010ff0abb284880121f21576509100045fc22eca1220008df835d942440111b906bb284880023be09765091003c5e43ac8a122068a9c83591424400f55904b2284880063da1b71509100063a32ee2a12200087f855db32440090f90abb664880030f9d365cc9100061fb2ae99922000c3c655d3324400195ce9b1664880063d21971cc9100063a32ae3992200087f855da32440090f90abb464880030f9d3658c9100061fb2ae91922000c3c655d2324400193ce9b1c648800a3e219708c9100063c32ae1192200487e85dd932440010fb0bbb264880021fe15764c9100243e42aec99220008bf845d9324400717908bb2648800237e0d764c91000477c12ec99220038be841d9324400117b083b264880121f216760c9100043fc2aec192200487c855d8324400117f08bb0648800e2f211760c9100446e41aec19220078ec825d832440010f90cba864880021fe1f650c9100043ec3eca19220018f4865c432440051f10cb8064881771d1db65545100053a432a4a8a2004c74765495144001ae4a1baa62880063d219754c5102ee3a3b6ca98a205bc74761953144001caeca31a6288002e5610634c510005cac266498a2000ad4864c931440c18f0edb2aa0880029e21953541100263c3b2a6a822001b70875455044005ae10ea8aa088006dca19515411000db8432a2a822004e70865455044009ce6eca8aa08800b5c9d95154110016b83b2a2a822004e707654550440016e706a8aa0880035cdc95154110005b8c2a62a822000d7251dd520440051f10cbaa40881831e1db65481102e63c3b0ca9022000e6b651892044001753083124088002ea612324811000574432649022000d717554520440013e10e98a4088003f04c93148110
  | 1 => 0x50db82a6900223720d7690d2000c76432e521a400087f855d943480090f90abb286900023de057650d200147a40aeca1a40008fb805d9434801117d0fb22869000e37a1f6350d200063db2ee0a9240079ae8790d4248011938c6ba66490003275d363cc92003e57b02e91924007dab605d23248001b5420ba464900063b219744c9200063abaea3b0a400287c8759551480054e902b2aa2900063ba1b7254520006563b284a0a40018ec865cb31480090fd0a3b262900021f614764c520006663b26498a4000c3d74953654400187ae83a6ca880028fa1073d95100051ec20e7b2a2000c5d731cf65440bb4eb0239eca880028fa1072d95100051ec20e5b2a2060a79801cb654411f8eeebb8aca880021fa1f65591100043f438cab222000c5f65dcd64440018b8cbb9ac88800317d9473591100062e328e6b222000c9c641cd64440018decbb92c8880031b197725911000637b28e4b222000c6c651c96444001958c8392c8880121fa1f75591100446f43ee6b222000c5f75dcd64440018b8ebb9ac88800317dd473591100062e3a8e6b222000c9f741cd644400f1dd0fb92c8880031bdd77259110006363aee4b222000ccf73dc96444001998e7b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc72591100043fc2aecaa220008df835d954440111b906bb2a8880023be09765511003c76412ecaa2200387e87d95544400117f08b96c68800e2f21172d8d100043f43ecab1a2000c3c74d9563440010fd0e32ac6880030f1d06558d104763db80cab1a2000c3f65dd16344001878cbba2c6880031bd977258d100063632ee4b1a2000c6f651c963440018d8ca392c6880121fa1f7558d1001c5f43ee8b1a2000c3f75dd16344001878ebba2c6880030fdd47458d100061e3a8e8b1a2000c9c74dcd63440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880031e1d77058d100061f3a6ca31a2000c3e74194634400187ecaba0c6880030f1957418d100046fc3ac631a2000a9c8458c634400159904b18c6880029760f6594d103063b38ecb29a20018f4865c653440018eecab8ca6880021fe157654d100045fc22eca9a20038bc845d953440011df04bb2a68801e3b2097654d100047dc02eca9a2000c76511d953440110fd0fb2aa6880021fe157690d100243e42aed21a20018f4865c643440090fd0bbb286880021f6177650d100043fc2aeca1a200487c855d9434400117f08bb2868800237e0d7650d1000477c12eca1a20078ec825d943440111790eb228688022a720d6450d1032d56412c8a1a20028fa86dc143440018f0cbb8286880022fe1173d891001c5e422e7b12205d
  | 2 => 0xd744c94000cdc402e899280018bc865d0325000f1f10cb8064a00062fa1b745454000c5e432e998a8008c9c7650f3150001938eca1a62a00062f21974c85400063bb8ca2b2e60078bd84dd942cc0010ff0abb285980121f2157650b300047bc0aeca1660028f4815d942cc00117f08bb2a39800e2f211765473000477c12eca8e60078ec825d951cc0051790eb2283980030f5d254d95300063ab8ca3b2a60038be87dd1654c00187eea3a2ca9824717dd773595300064e3a6e6b2a6000cb874dc1654c00187aebaa6c8980121fa1f75591300061e3aee8b226000c5c75dcd644c0018f0ebb82c8980021fe1576551300045fc22ecaa260008df835d9544c0011f700bb2a898002b360c21d893000574c0043b1260008ef87588624c00f0fd0f2a2cb900030fdd254597200063bb8ca2b2e4000c3f749d165c800f4dd053a2cb900029b60a74597200051f424e6b2e4000a3d849cd65c80018bee739acb9001e9ba0a73597200053b40ce6b2e4000a75819cd65c800f4dd05a1acb900029b60b43597200063bb8ce2b2e4000a3f845c565c800147908b8acb9001e9b20971597200063ab88e2b2e403fa7a801c565c80014f30038acb9000297a0c41597200052ec1882b2e4007a6e8210565c80014db0420acb900028fa1031597200051ec2062b2e4007a6e820c565c80014db0418acb9001e1f21d655532003c6f43e86b1e400487e85dc563c80010fb0bb8ac79001e1fe1d6594f200052fc1acb29e4000c6d655ca53c800f0f90eb2aa79001f1b9c96590f2003c5fc3ac921e4000c6d655ca43c801117b09bb287900063ba0b7650f200063d32ee0a1e40019e8805d132c800f0f90bbb2a3900022fe11765472001c5e422eca8e40018ec825d951c80050f90eb2aa39000a9d205655472000636b2ee4a8e40028bc8759141c800f958eca1283900121fa1576cc7200043fc32eb98e400087f8759731c80010fb0eb2e639000a3721d634c7200063ab8ca3b2a4000a7980947654800717d0fba2ca9002237a1f73595200064fba6e6b2a4000c9c74dcd654800193ee839aca90003271d0735952048637baee4b2a40028f687dc5654800196ee9b8aca900032d1d371595200066bb9ee2b2a4000cd473dc565480018eeea38aca900032ddd071595200065a3a0e2b2a4000cd7731c565480019a8e638aca900030f5d754d91200045fc22ecaa240008df835d954480111b906bb2a8900023de0576551200147a40aecaa24000c5d75d4f63480010ff0ab8ec6900121f21571d8d200054ec2063b1a4008c9c635d2634800193ae9b1cc69000237e1d6318d2000c76432e529a40008bf845d9534800717908bb2a69000237e0d7654d200047bc0aeca9a40028f4815d953480110f90eb2aa6900229720d6554d202653a40acaa9a403fc7870595534800f1f
  | 3 => 0xcaa26200c7765dc5534c4018daeba96c4988021fe1570d89310243e42ae1b126200aad84083624c40f958c4ba4c4988032b5d3629893100477c3ac431262028dc865ce524c40f0f90eb2aa49881e9b20965549312663a38acaa92623fa7880595524c40f1d904bb4849880a372197390931044cfc3a8721262038ee87d89424c41193ec2ba6649882365d8574cc931006cb882e99926207cac625d2324c40195ae9b14649880a37219744c9310063cbaea1b026200c7b7094165c84111ef0cb8ca79081e1f21d6554f2103c5fc3ac921e42088bd84dd943c84010ff0abb287908121f2157650f210047dc02eca1e42018f8805d943c840187ae92a6ca9080e2fa1f74595210061fba8e8b2a4200cac74dc96548401968e9b8aca908030f5d754d91210243f43eeab224200c3c75dd164484018d8ebb92c8908031d1d771591210043fc2aecaa242008bf845d954484011df04bb2a8908023de05765512100566c1061b1a4200ad5810c363484011bf0eb18c6908022fe117654d2101c5e422eca9a42008ef825d953484011f700bb2a6908063e2017654d210443f43ecaa9a420087f855d943484090f90abb286908023de057650d210047dc02eca1a42018f8805d9434841117d0fb2286908031dd9771549210064e320e6b22a0008bf845cb635400717908b96c6a81761fe1571d8d500046fc3ac631aa000a9c8458c63540b70fd0db8aa6a80065e2037154d5000cbd43ee0a9aa00187c865d6435400187aebb2486a80022fe1173d895001c5e422e7b12a063a788054f62541278daebb14c4a80023be1d621895000c3f436eaa12a00187c865d7325400193ce9b1c64a801e1f216760c9500045fc22ec192a0038bc845d832540030f90cba864a8003175d7630c9500145f43ec8a0aa00887c859db315400117f08bb662a800e2f21176cc5500146e41aed98aa00187c865d731540032f100bae62a8003175d763cc55000c3e432ea98aa001978805d531540051bd0fb1a62a80022fe1176c855001c5e422ed90aa0008df835db21540111b906bb642a80031d5c651d95400062e328e6b2a8092c3f75dd165500111bd0fb9acaa000317dd473595400064fba0e6b2a8000cd873dc165500018baeba9ec6a00021fe1571d8d400243e42ae3b1a8000a9d840c763500011bf0eb18c6a0002972156318d400052ec1ecb29a80018bc865d2535000187ecaba4a6a00066e2017494d400454f436c6a1a808ac9c63dc943500033750fb8286a0002ab61021d894000574c0043b1280008ef8758862500031790cba4a4a001e3e21970949400445e424ed992800087f855db32500090f90abb664a001e3720d76cc94000c5e432e99928008c9c635d3325000337100ba664a0003275d363cc94003c5e424ed19280018bc865d232500031790cba264a01a32718
  | 4 => 0x50c80f4d904b8aca190029ea0071594320053cc00e2b286408a5e83105650c8014bb0620aca190028fe1170594320051e422e0b286408a5c835c1650c8014ed02382ca190029d604705943203d3741080b286400a6d82101650c8010fd0e082ca190021f61c105943203c3e43acaaa06400cac641c9645440117f08b96c6a880e2f21172d8d514be2ebaec731aa2008df8758c63544050fd0dbaa86a88022fe1173d895101c5e422e7b12a26087f855c362544011df0eb10c4a8802ab21162189513de3a38ec6a92a20297687dc552544b90fd0db82a4a880a5d20770549510143e432eb212a200c3d75d92425440195ce9b1664a880a1f219758c9510045fc22ec192a2038bc845d832544050f90cba864a88031b5d7620c9510063cb84a1b2a8200c6c651c9655052d87eebba2caa081e3ba1f725954100637ba8e4b2a8200caf741c9655052b8eeebb8acaa0803391cb71595410054ec2061b1a8200ad5810c363504011bf0eb18c6a080a2f2197494d410447a432e329a8200c6d75d4b62504010ff0ab86c4a08121f21570d894100556c2041b1282008ef8758862504014d90ab10c4a08029b60b65949410145e432e92928200c3f655d2525040536902ba4a4a0a1f2b18b735094103d57436c4a1282029b687dc542504051790cba664a08021fe15768c9410243e42aed19282078ec825da32504051790cba464a081f2b189748c941014da40ae91928200cad74d8a32504051790cba264a09972b189744c941014da40ae899282028bc865d0325040f1e90cb8864a08221fa1e54597310061fba4a8b2e6200c3f749d165cc4114bd073a2cb988029760e74597310051f424e4b2e6200a3d849c965cc4114bd07392cb988029ea0272597310053cc04e4b2e6208a5e83d0965cc4014bb07a12cb988028fe1170597310051e422e0b2e6208a5c835c165cc4994ed02382cb988029d60470597310063cb80e0b2e6208a5e8310165cc4014bb06202cb988029ba08405973100536c1080b2e6200a3e8408165cc40147b08102cb9882297a0c20597310052ec1840b2e620887c8759554cc4111dd0fa12c5988121fa177058b310043ec2ee0b166200c5d655ce52cc4118bce6b2c8598803175957390b3103c5ec26eca1662028de83dd942cc4018eccbb8a859880a75205744cb310053ac0ca1b2a6200c7970943654c40717d0fba2ca98a5317dd7735953103c7743ee4b2a6200caf74dc9654c401958e9b92ca988032bdd07259531006563a0e4b2a62018fa87dc1654c401976e9b82ca988032e1d3705953100675b96e0b2a6200ce872dc1654c4018f6ea382ca988032edd070595310065c3a0e0b2a6200ceb721c1654c4019d0e4382ca988030f5d754d91310045fc22ecaa262008ef825d9544c40f1d904bb2a8988023ee01765513100c7c402e
  | 5 => 0x10121f21571d8d420046fc3ac631a8400a5d83d96535080187ecbba2a4a10031d5d751d85420063bb8ca2b2e64088be87d5164cc80187eebaa2c999022a7a0f54593320454f41c82b266400c3f759d564cc81153d073aac999002a760e75593320051fc2ae4b266400a3c855c964cc80156f02b92c999002ad20572593320055dc02e4b266400ab8805c964cc81153d07a92c999002a760f52593320051f42ce2b266400a3d859c564cc81153d0738ac999002a760e71593320055d404e2b266400ab9809c564cc81153d0638ac9990dea760c71593320454f41ca2b266400a9d8394564cc801c6ea328ac999022a7a0c51593320054ec18a2b266400aba8014564cc8015730028ac999022a7a0e21593320054ec1c42b266400a3f855c164cc8014790ab82c999022a720d705933232d57410e0b266400aad821c164cc801972e0382c999022a7a0c50593320054ec18a0b266400ab68114164cc80156b02282c999022a7a0f10593320054ec1e20b266400a3e8504164cc80147b0a082c999022a7a0c10593320054ec1820b2664088bc8759154cc80193ac9b9a85990031ddd751587320063db84a0b2c64078be87d51648c80187eebaa2c91901eaba0b545923203d5741480b246400c3f759d5648c80f55d053aac919002ab60a75592320051fc2ae6b246400a3c855cd648c80156f02b9ac919002ad20573592320055dc02e6b246400ab8805cd648c8d1c3ca7a9ac91901eaba0b535923200556c16a6b246400a3f855c5648c8014790ab8ac91901eab20971592323454f418e2b246400a9d831c5648c80196ae238ac9190038dd46515923203d57410a2b246400aad82145648c8015750028ac919002ae60051592320051f42ce0b246400a3d859c1648c80f55d05382c919002ab60a70592320055b40ce0b246400ab5819c1648c80f55d04382c9190ceab608705923203d57414a0b246400aad82941648c80f55d04282c919002ab60850592320055b408a0b246400ab581141648c80f55d05182c919002ab60a305923203d5741420b246400aad82841648c80147d0a082c9190028f614105923203d5741020b246400aad82041648c80f1790eb22a9190032b5937250e320063dbaea0b046400c3d74953654c8090fd0fbaac89900a3da1f71591320063bbaee2b226400c7475dc5644c8018eeea38ac8990031d1d4715913200c7d43ee0b226400c7b75dc1644c8018f0ebb82c8990033cdc770591320067838ee0b226400c7b751c1644c8018f0ea382c8990033cdc4705913200678388e0b22640087f855d9544c8011ef02bb2a89900a3d20576551320047dc02ecaa264018f8805d9544c8018becbb9aa49901e1fa1e54594320061fba4a8b286400c7771945650c80187ee93a2ca190031ddc671594320051fc22e2b286400a3c845c56
  | 6 => 0x4391709931e2b8e11ed3662d113b046b626cef29c618a7998199004ab040322692af1a7add086304af1506aebb43b9020688cd369fb15e5b05233842869895aee22e001258d361c9d10b24346884c5f80000060c128c21a44c5070005a2ac13e8650507a5a5ab1508da80016e59e97082a214a479c9c8f95d66055c9dc65cd60000f43900014780048008c00164232c343187b53a46ca3000156560f412355cab46e95a064c84463056e0001aa820534038601c30003bc059520a6a5137800458aed9cab70bab341b8004f27155c0006047540e0c913c0000013348a47c2d01e24a00172a723b40008596800049996a566a00281e9a767a0004509601000000407003004008008020020040100100000c010000040040280e01a0500a8020060040e04000a00c0000300a0040000100600c00801002020010050160180f00400803c0200d0500000a8000040000b0040800041b80800c02c0180001c0000080100202c0180601205c000040040340000200001c078000040000000203001802001004000000080280000a00f00a000000000460340200e00a010070170000000200005a0140200200603c0200105002c2000f0000880381f0000180280500c020080050000000003403a0080102d028038118000040280280001a004000030000000401a0080480202100e0000000904a0080100f00a00807010008004230040060000381104801000815002004020000020040100505604c010600180080580100e0040300302005400023000004030050160000001505a0140000001e0d4010090120000381b02600c0001400c0040184500000c0700c0120040a000004000020000000000b80502000c0380003200c0080200602c000030020c800000002090030220020000000301e0e40700000000a5d850c3635500153b08186c6aa00237e1d6318d540056c402c631aa800a6d85087625500155b0810ec4aa0023be1d62189540057240ac4312a800ce4611c961550019b0c039ac0aa0028f61640d915300536c2843b12a600acd830876254c011df0eb10c4a98031ddc6515964300536c2842b148600aad840856290c1159d0610ac521802ba6002158a430051ec24a1b2a8600c79709436550d318beebb9acaa18063ea1f70595430063dba8e0b2a8600cbb741c16550c019b6e6382caa18030fd977454d430043fc2ae1b12860487c855c36250c011df0eb10c4a18031e5d750d8143004b6c16eaa1ca400a3d8590764548014bb0a186c6a9002b360830d8d520046fc3ac631aa4088ec865ca43548018f6e1282cb21002976143058e420054ec2060b1c8407ace820c163908015ab02182c72101e3721d6354e420051ec24a3b2a8400c757194765508051ed0fb8acaa10031ddd471595420065bba0e2b2a8400ce7721c565508010ff0ab8ec6a
  | 7 => 0x2adbcf13470e05288015117cd44003561acc2c27a116b4000001ea698608ab800354000de8034084193094d144150001c4264340f786b286b50743125c05255983a00066ca13541be2444d0cb5129ccae00000000093af64ea0000010f5e4134000004164a84a0071d21b0022fe11a001080000006317da8e0000203700c46e830e5b432f829400000300b8cda97745a051acb4d000cac0000042a00067b234f01bd848005ac2f0c40006841f56209f000d9c0007900000086000000ae800000000658000000000005eac91242a52c8331e60000e9290001e05384b0009915f0004a6a449703e18a0007fb6018c0018335c0769680011444c22d61a2b5e85e87aa9b1120fc9f95d55681db18d8346a08f81d312e550000000ce7f91c08158038c5d9d44dc6d8dd1852826443b2674461091803526c558642a42de9791c9d1000a18c51b4240bcc410ca000800fc0e4072b404e970056cbd6f3320e6d1123aa15648fd3f9ca6be4dc090310a24bc0026c40491030a0f29c24c6d2ec694a1cfa2af2d47c83e14f11e0a8b29e11cc875408015067d4d28f15ce6fc7511c28a19885248434045249ff48c928233685fe39c9693a2fe5ac472294d45995a1a45c44d441a25430c5cd02cb6dad05a9a7a5b6c990d95969004d87b34220ba44c2a547600128aea498954e3a422c6c404201500011d2728a00c7002d9160008f00000d35e65cfb2ca3780010f0fd2066c42c97323c3d8003352fad48e8000000001609a8000025b20455a6001b8a4d23a0159d86d1bc9ac9e94c0c41f8002f5000000df0001b20b8003694b00018b1f72d2001463296748d52a04c32a44c222412503891535e4020b0b383c5de9893db0063aa7ce60ba3aec442519f5b88f5a30db370000cf13c31ab68138b7666000270240320a4001bb0008f80d314000834108004e2b4866b2740a3f91428502e6603228d0d21d4c4b4e2701480016d4ee5ec1c11145e51cc9aa65fa0002b99c1e0588d580052cc69498b90005d53e3011aaa5c351e0000000002fc20252cec0ac4ec9405b19a67c648c71a946200000298150a2d941db0f43b4001eb00000000299000000000000aa214ca2600b8610568580007917c27001e5559b0a054e974000ee5ccb20000003a43807c0004383dd670000002e0000003582195aaa8000140a2000626000619535000016c8b36d600151b03000a48001ee474000e78c40003f0002666e4c81b311a11085c0015f260b1cfd1743ba4ec551792808c85906016a0417b9e31a88295127e598be8a4000000afc340000005e0003310006c8838002b606d6c1d91d687c3a0902e27059b8d109279912109044640c30fb55298c0000030e35d8f8184d20bcf60403cad8851b0a24405816a5f6583b03f99d344159781a13fa8214a8a63beb148909549e1c8131f3392
  | 8 => 0x21ad74d81cd6380000000003ec78fcae8316b7d72000630819b62f100033192a5757a285b70e53f87c42f8ce6480016bac65aa4f9440004d05f8001b900000101972554d9470976432a40841d668ad008200067e0018d8002c0a815b0006786b90903036e1791013400096c002095c22c5110dc62a000e712c2c2000790000002c0000000e2000000000900009080038cbe4002c218e99595000000105b092446c0008c09c10ec65838001f46b5840000000001b0002
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x460c00a280e100061c605701c165cc401077985c471597200061c5c5801c565c80032709661531541100151c2597554520440011719521d31481100067021d324c520440016c0964c93148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x81c2999521d3148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x94d
  | 6 => 0x94e
  | 7 => 0x3
  | 8 => 0x4
  | 9 => 0x98a
  | 10 => 0x98d
  | 11 => 0x98e
  | 12 => 0x150a
  | 13 => 0x150d
  | 14 => 0x150e
  | 15 => 0x9ca
  | 16 => 0x9cd
  | 17 => 0x9ce
  | 18 => 0x168a
  | 19 => 0x168d
  | 20 => 0x168e
  | 21 => 0xa0a
  | 22 => 0xa0e
  | 23 => 0xa4a
  | 24 => 0xa4d
  | 25 => 0xb09
  | 26 => 0xb0d
  | 27 => 0xb0e
  | 28 => 0x1549
  | 29 => 0x154d
  | 30 => 0x154e
  | 31 => 0xb49
  | 32 => 0xb4d
  | 33 => 0xb4e
  | 34 => 0x16c9
  | 35 => 0x16cd
  | 36 => 0x16ce
  | 37 => 0xb89
  | 38 => 0xb8e
  | 39 => 0xbc9
  | 40 => 0xbcd
  | 41 => 0x3c9
  | 42 => 0x3ca
  | 43 => 0x3cd
  | 44 => 0x3ce
  | 45 => 0xcc9
  | 46 => 0xcca
  | 47 => 0xccd
  | 48 => 0xcce
  | 49 => 0x15c9
  | 50 => 0x15ca
  | 51 => 0x15cd
  | 52 => 0x15ce
  | 53 => 0x1709
  | 54 => 0x170a
  | 55 => 0x170d
  | 56 => 0x170e
  | 57 => 0xd09
  | 58 => 0xd0a
  | 59 => 0xd0e
  | 60 => 0x1609
  | 61 => 0x160a
  | 62 => 0x160e
  | 63 => 0xd49
  | 64 => 0xd4a
  | 65 => 0xd4d
  | 66 => 0x1649
  | 67 => 0x164a
  | 68 => 0x164d
  | 69 => 0xe89
  | 70 => 0xe8a
  | 71 => 0xe8e
  | 72 => 0x1789
  | 73 => 0x178a
  | 74 => 0x178e
  | 75 => 0xec9
  | 76 => 0xeca
  | 77 => 0xecd
  | 78 => 0x17c9
  | 79 => 0x17ca
  | 80 => 0x17cd
  | 81 => 0x1049
  | 82 => 0x104a
  | 83 => 0x1409
  | 84 => 0x128a
  | 85 => 0x1449
  | 86 => 0x12ca
  | 87 => 0x1849
  | 88 => 0x1489
  | 89 => 0x180a
  | 90 => 0x130a
  | 91 => 0x2c9
  | 92 => 0x14a
  | 93 => 0x14c9
  | 94 => 0x19c9
  | 95 => 0x198a
  | 96 => 0x134a
  | 97 => 0x409
  | 98 => 0x1889
  | 99 => 0x1a09
  | 100 => 0x8d
  | 101 => 0xe8b
  | 102 => 0x18c9
  | 103 => 0x1a49
  | 104 => 0xd0c
  | 105 => 0x138d
  | 106 => 0x124d
  | 107 => 0x128d
  | 108 => 0x12cd
  | 109 => 0x1a89
  | 110 => 0x1949
  | 111 => 0x198d
  | 112 => 0x134d
  | 113 => 0x138e
  | 114 => 0x124e
  | 115 => 0x128e
  | 116 => 0x12ce
  | 117 => 0x180e
  | 118 => 0x130e
  | 119 => 0x188a
  | 120 => 0x1a0a
  | 121 => 0x58a
  | 122 => 0x18ca
  | 123 => 0x1a4a
  | 124 => 0x24d
  | 125 => 0x140d
  | 126 => 0x144d
  | 127 => 0x1a8a
  | 128 => 0x194a
  | 129 => 0x19cd
  | 130 => 0x14cd
  | 131 => 0x140e
  | 132 => 0x144e
  | 133 => 0x184e
  | 134 => 0x148e
  | 135 => 0x18cb
  | 136 => 0x1a0d
  | 137 => 0x188e
  | 138 => 0x188c
  | 139 => 0x1a4d
  | 140 => 0x18ce
  | 141 => 0x2d551
  | 142 => 0x15692
  | 143 => 0x19d4d1
  | 144 => 0x1a1651
  | 145 => 0x1a57d1
  | 146 => 0x1a9951
  | 147 => 0x1a0d51
  | 148 => 0x1a57d2
  | 149 => 0x19d4d5
  | 150 => 0x1a9952
  | 151 => 0x1a4ed2
  | 152 => 0x1a57d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2176
  | 6 => 4507
  | 5 => 883
  | 4 => 8
  | 3 => 1
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (89212+((h/725+packedAt gbK7 (80512+(h % 725)*12) 12) % 3160)*13) 13
  | 6 => packedAt gbK6 (235862+((h/1502+packedAt gbK6 (216336+(h % 1502)*13) 13) % 5949)*14) 14
  | 5 => packedAt gbK5 (55331+((h/294+packedAt gbK5 (52097+(h % 294)*11) 11) % 1060)*11) 11
  | 4 => packedAt gbK4 (568+((h/2+packedAt gbK4 (560+(h % 2)*4) 4) % 12)*4) 4
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff07c03fffc0ffc1fffffe0005c7639d1e73fc
  | 1 => 0x3f8003e07fffffe0f803fff1a78bce213fccf
  | 2 => 0xffffffc007ff03fff0003fffe380c0ffe38f0f
  | 3 => 0x3fffffff80003ffffffc000fc00ff03fc0ff0
  | 4 => 0x3fffffffffffc0000000000ffff0003fff000
  | 5 => 0xfc0000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x5501420a49c8a4c098a9b20600c3218d06315c
  | 1 => 0x422804168251c9520d02a4aa08582ca210d4c5
  | 2 => 0x9952da4044aa22a5a00519546380c055630b0a
  | 3 => 0x829caca59010433946560018bc00d602b80ea0
  | 4 => 0x13e73739e73c701084181060dfad0003dfe000
  | 5 => 0xe00038010020802108602180f776fbf8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeee0fac8eac0feeeeee0fac8eac0feeeeee0fac8eac0feeeeee0fac8eac0feeeeee0fac8eac0feeeeee0fac8eac0feeeeee0fac8eac0feeeeee0fac8eac0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37197
namespace PEqualNP.Outside.L_meta_37197
open PEqualNP.Outside.L_meta_37197.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 8 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 92 := (concat bs0_4_0 (concat bs0_4_32 bs0_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bs2_4_0 : Interval s2Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 2 := bs2_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 2 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 64 := (concat bs4_4_0 bs4_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 40 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 64 := (concat bs5_4_0 bs5_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 40 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 8 := bgb_4_0
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
theorem bgb_5_864 : Interval gbAtlas 5 864 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 883 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat bgb_5_672 (concat bgb_5_704 bgb_5_736)) (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)))))
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
theorem bgb_6_4480 : Interval gbAtlas 6 4480 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4507 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)))))) (concat (concat (concat (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344))) (concat (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472)) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632))))) (concat (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)) (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)))) (concat (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048)) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208))))))) (concat (concat (concat (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464))) (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752))))) (concat (concat (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880)) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)))) (concat (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168)) (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)))))) (concat (concat (concat (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456)) (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616)))) (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904))))) (concat (concat (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 bgb_6_4032)) (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)))) (concat (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 bgb_6_4320)) (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480))))))))
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
theorem bgb_7_1888 : Interval gbAtlas 7 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1952 : Interval gbAtlas 7 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1984 : Interval gbAtlas 7 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2048 : Interval gbAtlas 7 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2080 : Interval gbAtlas 7 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2144 : Interval gbAtlas 7 2144 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2176 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))) (concat (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)) (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))))) (concat (concat (concat (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312))) (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))))) (concat (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728)) (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 bgb_7_1856))) (concat (concat (concat bgb_7_1888 bgb_7_1920) (concat bgb_7_1952 bgb_7_1984)) (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 (concat bgb_7_2112 bgb_7_2144)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeee0fac8eac0feeeeee0fac8eac0feeeeee0fac8eac0feeeeee0fac8eac0feeeeee0fac8eac0feeeeee0fac8eac0feeeeee0fac8eac0feeeeee0fac8eac0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071584 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37197.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.and,[0,6]⟩,⟨.or,[3,4]⟩,⟨.or,[0,5]⟩,⟨.and,[8,9]⟩,⟨.or,[2,10]⟩,⟨.or,[1,7]⟩,⟨.and,[2,4]⟩,⟨.and,[3,13]⟩,⟨.or,[12,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37197

open PEqualNP.Outside.L_meta_37197 in
theorem PEqualNP.Outside.L_meta_37197 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
