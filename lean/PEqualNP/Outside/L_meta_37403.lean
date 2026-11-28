import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37403.Model
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


end PEqualNP.Outside.L_meta_37403.Model

namespace PEqualNP.Outside.L_meta_37403
open PEqualNP.Outside.L_meta_37403.Model
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

def SBf (j : Nat) : Nat := [6, 4, 4, 6, 7, 7].getD j 0

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

def mirrorSteps : List Move := [swapRows 33,swapRows 84]

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

end PEqualNP.Outside.L_meta_37403

namespace PEqualNP.Outside.L_meta_37403
open PEqualNP.Outside.L_meta_37403.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x81c900034300b3c510608a40c38100000033009be41bc41de31dc31ee21ec21be40bc40de30dc30ee20ec20fb10f610f410f810f010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x120092c26044434170003000003854cf58800d5001950401c000000a0200200439c06510431d220843c4310873080186a10020e41804172508436480086c10010e918021d030043c440087808010d920821b041043a46208740c410f110821e02104366a8086c15010e9a9821d053043c6a4087814810
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x40083105414c10c815052043405314810
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 25
  | 2 => 3
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
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (297+((h/5+packedAt s0K4 (272+(h % 5)*5) 5) % 23)*6) 6
  | 3 => packedAt s0K3 (723+((h/8+packedAt s0K3 (675+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s0K2 (117+((h/1+packedAt s0K2 (114+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffbf83ffffc00fffffffc03ffff0ff
  | 4 => 0xffffffffffdffc1ffffff003ffffffc03fff0f
  | 5 => 0xefffe0fffffffc00ffffffc03ff0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffff00884212c95264b12dd2d2d2d777
  | 2 => 0xffffffffff011084255264a95256e565656bbb
  | 3 => 0xffffffffff42790849bb48d2649b7039b9b0dd
  | 4 => 0x2423d08e238ee388e3b9b03e3d0e
  | 5 => 0x18421ef03c0f03f0fc3e3e303ee0
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xc0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37403
namespace PEqualNP.Outside.L_meta_37403
open PEqualNP.Outside.L_meta_37403.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 3 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x12108144220484901058a2a288a8a2154534d5
  | 2 => 0xa4aa528a51a9292a2e055511554455aa928a2a
  | 3 => 0x88c954d294a3b20aceac19d4467511c0d8d34c
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37403
namespace PEqualNP.Outside.L_meta_37403
open PEqualNP.Outside.L_meta_37403.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 3 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x12108144220484901058a2a288a8a2154534d5
  | 1 => 0xa4aa528a51a9292a2e055511554455aa928a2a
  | 3 => 0x88c954d294a3b20aceac19d4467511c0d8d34c
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xaa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37403
namespace PEqualNP.Outside.L_meta_37403
open PEqualNP.Outside.L_meta_37403.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x10a00000020b0090053c600704c40e343085180a3df43be43bc43dc439c43be42bc42de32dc32be41bc41de31dc31bf40bd40df30dd30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x714034001200000000000000e0000000405004c04423c40c900000c2c81900002800000610404794e438f290871e5110e3aa021c794e429b28c851e548caaca31947150328f29c832e529063ca918d394a318e2a0631c5350258a4a04d145408e2a6611c544c298a4985514530
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x64008000859865210e0e6294443831895010e146154043
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
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
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (297+((h/5+packedAt s3K4 (272+(h % 5)*5) 5) % 23)*6) 6
  | 3 => packedAt s3K3 (609+((h/7+packedAt s3K3 (567+(h % 7)*6) 6) % 46)*6) 6
  | 2 => packedAt s3K2 (156+((h/1+packedAt s3K2 (152+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffff03ffffffffffffff87ffff
  | 1 => 0xfc0fffc0fff80ffffc1ff03ff03ff81ff9ce73
  | 2 => 0xfff03fff03fff01fffe0ffc0ffc0ffe07e739c
  | 4 => 0x3ffffc00001fffff0000ffff00007f83e0
  | 5 => 0xffffc0000000001fffffffff000000007ffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x844108482092040400a5245124510a8a0294a5
  | 1 => 0x2922948649215a8b2c0a522a522ad055394a52
  | 2 => 0x30a4a5121a4542b355409a889a88e5415c6318
  | 4 => 0xa2cb3a2490766cdd9a730c30ef3c41866f83e0
  | 5 => 0xc30c3c38e3878f1ee39cef3c0c30861877fc00
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xe8e8a8a8a8a8a8a8e8e8a8a8a8a8a8a8e8e8a8a8a8a8a8a8e8e8a8a8a8a8a8a8e8e8a8a8a8a8a8a8e8e8a8a8a8a8a8a8e8e8a8a8a8a8a8a8e8e8a8a8a8a8a8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37403
namespace PEqualNP.Outside.L_meta_37403
open PEqualNP.Outside.L_meta_37403.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x1d52008002c01180442451800953801ab041f4c70d805600880481c7800078a00028092100082802e680000010aa80000180262c0000000c86003800018a81010b022410004000000000080ff43df43fe43be43fd43fc43bc43dc439c43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x9c78001ec006a3c8d48631061dcea7e2b000aa090011c001f0b9605e0b40074ae261f9f0d25302000cc0014140a80000000005e000000032320000000378001c3736000000021000001400134b27d11084a25b3804054001297c4000121fcda3e11970ca3a00130b45d0e0781006310000e000019c00410513ca43d39980806b2412cdc461d854661b098445c160d09c0074001d8042d3d0047863160141a00001c8303600000600000000c249250e470002203c0003388646829229a0242b03050309810904800302088000000182000001808201800004020000830006028400808101088081000287d794e439f29c871e5390f3a8621cf94c43cf298875e5410f3ca821e7d4843cf290879d5210f38a421e7d4443cf288879d5110f38a221e7d4043cf280879d5010f38a021e710f42af29c855d5390b3887215d94642baa8c855f5350ab8a6a16710d42ce218859c43cca7ca9194f55232ce21c6576518caeaa3194fd51329e2a2659c434cb3886196710f41af29c835d53907388720db94a41b6a94835f53506b8a6a0e710d41ce218839c43cc67ca918cf55231ce21c636e528c6daa518cfd51319e2a2639c434c7388618cf953219eaa6435e53c86baa790e710f219f2a4433d54886bca710d754e21ce21c439c43487388610f948421ce21e815e53902baa7206710e40afa9a815c535033886a05bd4940b6292817751502e8a2a06710c40ce21e613e548c27aa9186710e309faa2613c544c33886985bd4930b62926177514c2e8a2986710c30ce21e419c438827ea8904f15120afa9a415c534833886905dd4520ba28a413e540827aa8105794c20aea98419c43082eca2105d54420ce21e219c438427ea8884f15110afa9a215c534433886885bd4910b6292213e540427aa8085794c10aea98219c43042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x21b96028018a19e80001f8000001c800d8c110f050000079283a01a80000003100015209a1994109700000a800000138000058800001e168000070d00001c000680001780000880000015801b0018000e0f8006000b13049d91899d018a19120914800b80211f0c810e80840117000c0000a04006364c20812001801208080a59875210e9561d4843a59865210e956194843c35485210e8e62d4443a358b5110e8e6294443a358a5110f155114443a3d895010e8c6254043a5d855010e946154043a39885010e8d6214043a59845010e956114043c510e5190b144354642c510e518cb144354632c310e529070c4354a41c310e528c70c4354a318718d54c861c6454f2187d9443c861d6510f218718d548861c6454e2187d94438861d6510e21e110d210870c43d4940c310c525031443d4540c510c515021c6315130c310f524c30c4314930c510f514c31443145308798f544821e64d4d2087994434821c6510d20c510f514831443145208718d540821c6454c2087d94430821d6510c20c510e510831443544208798f544421e64d4d1087994434421c6510d10c310f524430c43149108718d540421c6454c1087d94430421d6510c10c310e520430c4354810
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (825+((h/15+packedAt s4K5 (720+(h % 15)*7) 7) % 72)*7) 7
  | 4 => packedAt s4K4 (3827+((h/43+packedAt s4K4 (3483+(h % 43)*8) 8) % 170)*9) 9
  | 3 => packedAt s4K3 (2738+((h/22+packedAt s4K3 (2584+(h % 22)*7) 7) % 108)*8) 8
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffffffffffffc0fffffffffffffff0fffff
  | 1 => 0x7f03ffe07ffc0ffff07c1e0ff83ff03ff44e73
  | 2 => 0x7ffc0fff81fff03fff801ff07fc1ffc0f8739c
  | 3 => 0x80000ffffe00003fffffe0007ffe0000ff83e0
  | 5 => 0xfffff0000000003fffffffff80000000fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x11040241048000002942410904215140194a5
  | 1 => 0x2a48a64324915d1cb0290a8d2a35a0aa744a52
  | 2 => 0x4c292a890d23456d550213a44e91ca82b86318
  | 3 => 0x68b2cd12483a69b669cf41087738830cde83e0
  | 5 => 0x70c30e1c71c38e3b8e739dce04210c30ef7c00
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37403
namespace PEqualNP.Outside.L_meta_37403
open PEqualNP.Outside.L_meta_37403.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x800f003a00119003932c56a0b00008d0804a911004e4948054001931420e0d36250070a5c81a3e54c0b22507810c00603106408003341142288149ff43df43fe43be43fd43fc43bc43dc439c43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xf41026008fa6a11820000702914f200051041a35239a000641c8001e000e8a434630d84c221200064000000000ae4e000c80200000f0e27e171e07e18000ace60000024a000349280038001246c001680c006018800ea1f00000b60037800ee4d14000006d0000000002e0000025000002e7c3a000dc0b020b0ec5f060584c0e1b93c66591f158387f0a91028611d0bc40512a9c0001e40178e46221994ce5a12108a6220009ca46610800ba48201b0f63b1e918a80003000604b358d054580203870280000d8b00098082818000838300000a85028009898c00818110000083918200148100800003805794e439f29c871e5390f3a8621cf94c43cf298875e5410f3ca821e7d4843cf290879d5210f38a421e7d4443cf288879d5110f38a221e7d4043cf280879d5010f38a021e710f42af29c855d5390b3887215d94642baa8c855f5350ab8a6a16710d42ce218859c43cca7ca9194f55232ce21c6576518caeaa3194fd51329e2a2659c434cb3886196710f41af29c835d53907388720db94a41b6a94835f53506b8a6a0e710d41ce218839c43cc67ca918cf55231ce21c636e528c6daa518cfd51319e2a2639c434c7388618cf953219eaa6435e53c86baa790e710f219f2a4433d54886bca710d754e21ce21c439c43487388610f948421ce21e815e53902baa7206710e40afa9a815c535033886a05bd4940b6292817751502e8a2a06710c40ce21e613e548c27aa9186710e309faa2613c544c33886985bd4930b62926177514c2e8a2986710c30ce21e419c438827ea8904f15120afa9a415c534833886905dd4520ba28a413e540827aa8105794c20aea98419c43082eca2105d54420ce21e219c438427ea8884f15110afa9a215c534433886885bd4910b6292213e540427aa8085794c10aea98219c43042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1b81800000000000091f911815000000001a00109d1680141e1aa0000d800000170311960a0019208e8000210f801f050019938980000d101c000000120881060294a1958b1e87078000059280001b00000c8f0c0a800008009c849786801302000400000000000000188000038000000b9d8000000e00020814002000c080000020100380000234101a59875210e9561d4843a59865210e956194843c35485210e8e62d4443a358b5110e8e6294443a358a5110f155114443a3d895010e8c6254043a5d855010e946154043a39885010e8d6214043a59845010e956114043c510e5190b144354642c510e518cb144354632c310e529070c4354a41c310e528c70c4354a318718d54c861c6454f2187d9443c861d6510f218718d548861c6454e2187d94438861d6510e21e110d210870c43d4940c310c525031443d4540c510c515021c6315130c310f524c30c4314930c510f514c31443145308798f544821e64d4d2087994434821c6510d20c510f514831443145208718d540821c6454c2087d94430821d6510c20c510e510831443544208798f544421e64d4d1087994434421c6510d10c310f524430c43149108718d540421c6454c1087d94430421d6510c10c310e520430c4354810
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (810+((h/15+packedAt s5K5 (720+(h % 15)*6) 6) % 55)*7) 7
  | 4 => packedAt s5K4 (3827+((h/43+packedAt s5K4 (3483+(h % 43)*8) 8) % 170)*9) 9
  | 3 => packedAt s5K3 (2738+((h/22+packedAt s5K3 (2584+(h % 22)*7) 7) % 118)*8) 8
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffffffffffffffc0fffffffffffffff0fffff
  | 1 => 0x7f03ffe07ffc0ffff07c1e0ff83ff03ff44e73
  | 2 => 0x7ffc0fff81fff03fff801ff07fc1ffc0f8739c
  | 3 => 0x80000ffffe00003fffffe0007ffe0000ff83e0
  | 4 => 0xfffff0000000003fffffffff80000000fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x11040241048000002942410904215140194a5
  | 1 => 0x2a48a64324915d1cb0290a8d2a35a0aa744a52
  | 2 => 0x4c292a890d23456d550213a44e91ca82b86318
  | 3 => 0x68b2cd12483a69b669cf41087738830cde83e0
  | 4 => 0x70c30e1c71c38e3b8e739dce04210c30ef7c00
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37403
namespace PEqualNP.Outside.L_meta_37403
open PEqualNP.Outside.L_meta_37403.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x540225ca43005050b006a10000309dc2f00dc983785de81767c0345684508003802400080070000280740062a007201100f96807201b4360021333c8d31a58412b240480006200e80000000000041020010000061c90102046010a0048300ff95001fd5400ff15003ff43007f90c01fd4300ff10c05ff51007f94401fd51017f14403ff41007f90401fd4100ff10401ff31007f8c401fd31007f0c401fe21007f48401fc2100ffd0001fe40007f50003fc40007fcc001fe30007f4c001fc30007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a20009fd9510047fcca8800afe6544001feb2a2000bf59510047f8ca8800afc6544001be32a20029f19510007fec888002ff6444001dfb222000afd911003ffcc888006fe6444001feb222000bf5911003ff8c888006fc6444001de3222001af19110047fea88801ffe5444001feaa22007ff15110007fec688002ff6344001efb1a2000b7d8d10007fcc68801afe6344001feb1a2000bf58d10007f8c68801afc6344001ee31a2000b718d10047fea688003fe5344001fea9a2008ff14d1003ffe8688003fe4344001fea1a2007ff10d10007fec488002ff6244001f7b122000bbd8910007fcc488002fe6244001feb122000bf58910007f8c488002fc6244001f63122000bb18910047fea488003fe5244001fea922008ff1491003ffe8488003fe4244001fea122007ff10910007fe6488003fe3244001fe9922000ff0c910047fea288003fe5144001fea8a2008ff1451003ffe8288003fe4144001fea0a2007ff10510007fe6288003fe3144001fe98a2000ff0c510007fe4288003fe2144001fb10a2000ff48510007ea4288003fc2144011ffa822003ff94110007faa08800ffc504400fffa022003ff90110007fa808800ffc4044001ff9822003ff8c110007fa608800ffc3044001ff9022003ff88110007fa4088003ff1044001fd8822003ff8411001fec208800fff65040077fb282003ff99410015fcca0800f7e65040053f3282003ff59410005faca0800f7d65040013eb282003ff1941001df8ca0800fff64040077fb202003ff9901000dfcc80800fbe64040035f3202003ff59010005fac80800fbd64040015eb202003ff1901001df8c808017ff5404009ff2a02000ff55010027f8a80800fff63040077fb182003ff98c10035fcc60800fde63040016f3182003ff58c10005fac60800fdd63040016eb182003ff18c1001df8c608017ff5304001ff2982000ff54c1002ff8a608013ff4304001ff2182000ff50c10027f8860800fff62040077fb102003ff98810005fcc40800fee6204001773102003ff58810005fac40800fed620400176b102003ff1881001df8c408017ff5204001ff2902000ff5481002ff8a408013ff4204001ff2102000ff50810027f88408003ff3204001ff1902000ff4c810007f86408002fe610400bffa882000ff94410007faa208017fc5104009ffa082000ff90410007fa8208013fc4104001ff9882000ff8c410007fa6208003fc3104001ff9082000fdc8410007fc4208003fd2104001fe1082000fd0841001dfcc00800fff5004007ff2802003ff5401001ff8a00800fff4004007ff2002003ff5001001ff8800800fff3004007ff1802003ff4c01001ff8600800fff2004007ff1002003ff4801001ff8400800fff1004007fb8802003ff8401001ff4200800ffd1004007fa8802000fe44010
  | 1 => 0x7fc540c00d7f3186006ffd0c30037fc861801bfd430c00dfe2186003ffd843001ffcc218002fe610c007feb086000bf5843001ff8c21803bff510c001ff2886000ff54430077f8a218037ff410c001ff2086000ff5043006ff8821801bff310c00dff1886000f78c430037fa621801bfc310c00dee1886000ff88430007fa4218003fc210c0077f3006003ffd003001ffc801800ffd400c007fe2006003ffcc03001fbe601800ffe300c007fd1806003ff4c03001fba601801bf9300c001ffb2e2000bfd9710067fccb8800afe65c4001feb2e2000bf59710067f8cb8800afc65c4001ffb262000bfd931005ffcc988006fe64c4001feb262000bf5931005ff8c988006fc64c4019ffaa6200bff95310007faa98802ffc54c4001ffb1e2000bfd8f10007fcc78801afe63c4001feb1e2000bf58f10007f8c78801afc63c4019ffa9e2000ff94f10007faa788033fc53c4017ffa1e2000ff90f10007fa878802ffc43c4001ffb162000ff98b10005fcc588003fd62c40017eb162000ff18b10005f8c588033ff52c4001ff2962000ff54b10067f8a58802fff42c4001ff2162000ff50b1005ff88588003ff32c4001ff1962000ff4cb10007f86588033ff51c4001ff28e2000ff54710067f8a38802fff41c4001ff20e2000ff5071005ff88388003ff31c4001ff18e2000ff4c710007f86388003ff21c4001ff10e2000fd88710007fa4388003f521c4001fe10e200cffd431001ffca188003fd50c4007fe286200bffd031001ffc8188003fd40c4007fe2062000ffcc31001ffc6188003fd30c4007fe1862000ffc831001ffecb0800eff6584007ff32c2002bf9961001ffacb08002fd6584007fe32c2003bf1961001ffec90800eff6484007ff3242001bf9921001ffac908002fd6484007fe3242003bf19210057fea908027fe5484001feaa42009ff1521001ffec70800eff6384007ff31c2006bf98e1001ffac708002fd6384007fe31c2003bf18e10057fea708003fe5384001fea9c200aff14e1004ffe8708003fe4384001fea1c2009ff10e1001ffec50800eff6284007ff3142000bf98a1001ffac508002fd6284007fe314200affd4a10007fca508003fd5284015fe2942009ffd0a10007fc8508003fd4284013fe2142000ffcca10007fc6508003fd3284001fe1942000bf58610057fea308003fe5184001fea8c200aff1461004ffe8308003fe4184001fea0c2009ff10610007fe6308003fe3184001fe98c2000ff0c610007fe4308003f72184001ff10c2000ff48610007f84308003f421840077f3042003ffd421001ffca10800ffd5084007fe2842003ffd021001ffc810800ffd4084007fe2042003ffcc21001ffc610800ffd3084007fe1842003ffc821001ffc410800fff1084007fb8842000fec4210007feca88002ff6544001bfb
  | 2 => 0x40007fec6a0002ff6350001ff31a8000ff58d40007f8c6a001afc635002bffa9a8000ff94d40007faa6a0057fc5350003ffa1a8001ff90d400077c86a0007fd4350003fe21a8001ef10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0002fc625002bffa928000ff94940007faa4a0057fc5250003ffa128001efd094000ffc84a0007fd4250001dea128001ff10940007fe64a0003fe3250001fe9928000ff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0002fc615002bffa8a8000ff94540007faa2a0057fc5150003ffa0a8001efd054000ffc82a0007fd4150001dea0a8001ff10540007fe62a0003fe3150001fe98a8000ff0c540007fe42a0003fe2150001fe90a8000ff0854000dfec0a0057ff5050007ff2828000ff5414001ff8a0a0007ff4050003fda028003ff9014001f7c80a000ffc4050007de2028001fe10140037fec99801aff64cc00dff3266001bf99330037fac998002fd64cc00dfe3266006bf1933009ffca998003fd54cc027fe2a66006ffd0f30037fc879801bfd43cc00dfe21e6006ffd8730037fcc398002fe61cc00dfeb0e6000bf58730037f8c398053ff51cc001ff28e6000ff547300a7f8a39804fff41cc001ff20e6000ff5073009ff8839801bff31cc00def98e6006ff8c730037fa6398003dd31cc00dfe18e6000ff88730007fa4398003fc21cc027ffa066003ff90330007fa819800ffc40cc007ffb246003bfd923001ffcc918006fe648c007df3246001af9923001ffac918002fd648c007deb246000af5923001ff8c91800efc648c023ff2a46000ff5523008ff8a918002fd638c023ffa1c6006ff90e30007fa871801bfc438c007ffb0c6003ff98630005fcc31800ffd618c0017eb0c6003ff18630097fea318003fe518c001fea8c6012ff1463008ffe8318003fe418c001fea0c6011ff10630037fe6318003fe318c001ef18c6000ff4c630037f86318003dc318c001ff10c6000ff48630007f8431800efe608c007ffa046003ff9023001ffa811800ffc408c007ff9846003f7cc230037f66118003ff644c0017fb22600fff9913000dfcc898003fd644c0017eb22600fff1913000df8c89803ffe544c001feaa2600fff1513007ffe869801bfe434c001fea1a6006ff10d30007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c021ffa8a6000ff94530007faa298043fc514c01fffa0a6000ff90530007fa829803ffc414c00dff98a6000f7cc530007fc6298003fd314c001ee98a6006ff0c530007fc4298003fd214c001fe10a600fffd013001ffc8098003fd404c007fe2026006ffcc130037f6609800ffe304c007ef1826003ffd903001dfec81800ffe640c0037f3206003ff59030005fac81800ffc640c0077e320600dff95030007faa81803
  | 3 => 0xfa144200ff90a21007fa851086ffc4288401ff9944200ff8ca21007fa6510803fc32884017f30c421cffd4621007fca310803fd5188439fe28c421bffd0621007fc8310803fd4188437fe20c4200ffcc621007fc6310803fd3188401fe18c4200ffc8621007ee4310803ff6088401ff3044203bf98221007fac110802fd6088401fe304421cffd42210e7f8a11086fff4088437fe2044200ffd9121005fec890867fe64484037f3224200ff59121005fac890867fc64484037e3224219ff95121007faa890867fc5448401ffb1a4200bfd8d21007fcc69081afe6348401feb1a4200bf58d21007f8c69081afc6348433ffa1a4200ff90d21007fa8690867fc4348435ffa8a4200ff94521007faa29086bfc5148433ffa0a4200ff90521007fa8290867fc4148401ff98a4200ff8c521007fa6290803fc3148401ff10a4200fb88521007fec090802ff6048401ff3024200ff58121007f8c09080efc6048433ffa024219ff10121007fec810802ff640842fff3204201bf99021007fac810802fd640842ffe3204201bf190210bffca810803fd540842ffe2a04200ffd8c21005fec610803fe630840d7f3184200ff58c21005fac610803fc630840d7e3184217ffd0c21007fc8610803fd430842ffe2184200bf984210c7fea210803fe5108401fea884218ff144210bffe8210803fe4108401fea084217ff10421007fe6210803fe3108401fe9884200ff0c421007fc4210803f62108401fe9084200fd48421007ca4210803ff6008401ff3004203bf98021007fac010802fd6008401fe3004217ffd00210bff8801080fff65900077fb2c8003ff99640015fccb2000ffd65900017eb2c8003ff1964001df8cb20006fd6490003ffaa48001ff9524000ffaa920007fc5490007ffb1c8003ff98e40035fcc72000ffd63900017eb1c8003ff18e400b7fea720003fe5390001fea9c8016ff14e4000ffe8720007fe4390003fea1c8001ff10e4001ffec52000ffe62900017f3148003ff58a40005fac52000ffc629002dffa948000ff94a40007faa52005bfc5290003ffa148001ff90a400077c8520007fd4290003fe2148001ef10a40007fe6520003fe3290001fe9948000ff0ca4001ffec32000ffe61900017f30c8003ff58640005fac32000ffc619002dffa8c8000ff94640007faa32005bfc5190003ffa0c8001ff906400077c8320007fd4190003fe20c8001ef10640007fe6320003fe3190001fe98c8000ff0c640007fe4320003fe2190001fe90c8000ff0864001dfcc12000fff5090007ff2848003ff1424001ffe812000fbf4090003fda048003ff1024001ff08120003ff65500017fb2a8015ff99540015fccaa0003fd65500017eb2a8015ff19540015f8caa000eff6450003ffaa28001ff9514000f7ca8a0007fd5450001deaa28001ff151
  | 4 => 0x887ff418c401ff20c6200ff5063110ff8831881bff318c401ef98c6206fdcc631007fec118803fe608c4077f3046200ff58231005fac118803fc608c445ffa846222ff1423110ffe8118887fc408c401ffb2a6200bfd9531006feca988027f654c441ff32a6202bf99531007faca98802fd654c441fe32a6202bf19531006f8ca9880a7c654c401ffb226200bfd91310077ec898802bf644c43fff3226201bf99131007fac898802fd644c43ffe3226201bf1913100778c898806bc644c441ffaa2621fff95131007faa89887ffc544c441ffa9a6206ff94d31007faa69881bfc534c43fffa1a6206ff90d31007fa869881bfc434c401ffb126200bfd8931007fcc498803fd624c401fe3126200bf18931107fea498803fe524c401fea926220ff149310fffe8498803fe424c401fea12621fff10931037fe6498803fe324c401ef1926200ff4c931107fea298803fe514c401fea8a6220ff145310fffe8298803fe414c401fea0a621fff10531037fe629881bf7314c401ff18a6200f78c531007fec098802ff604c401ff3026200ff58131007f8c09880efc604c441ffa826220ff141310fffe809887ffc404c40dffb286206bfd9431037fcca1880afe650c40dfeb286200bf59431037f8ca1881afc650c40dffb206206bfd9031037fcc818806fe640c40dfeb206200bf59031037f8c81881afc640c43dffaa0621dff95031007faa818877fc540c40d7f3186206ffd4c31037fca61881bfd530c40dfe2986206ffd0c31037fc861881bfd430c40dfe2186206ffd8831037fcc418802fe620c40dfeb106200bf58831037f8c41887bff520c401ff2906200ff548310f7f8a418877ff420c401ff2106200ff508310eff8841881bff320c40def9906206ff8c831037fa6418803dd320c40dfe1906200bf984310f7fea218803fe510c401fea88621eff144310effe8218803fe410c401fea08621dff10431037fe621881bdf310c40dff1886206fd8c431037fa6218803dd310c40dfa9886206ffd8031037fcc01880efe600c40dfeb006200bf58031037f8c01887bff500c43dfe280621dffd00310eff88018803ff65884017fb2c421cff99621015fccb108037e65884053f32c4200ff59621005facb108037d65884013eb2c421cff19621015f8cb10803ff64884017fb24421bff9922100dfcc910803be64884035f3244200ff59221005fac910803bd64884015eb24421bff1922100df8c910873ff5488437ff2a44200ff552210dff8a910803ff63884017fb1c4200ff98e21035fcc710803de63884016f31c4200ff58e21005fac710803dd63884016eb1c4200ff18e21035f8c710873ff5388401ff29c4200ff54e210e7f8a71086fff4388401ff21c4200ff50e210dff88710802fd6288439ffa944200ff94a21007faa510873fc5288437f
  | 5 => 0x4e41137f8a720807ff4390403ff21c8200ef90e4100ffa8720807fc4390403de21c8200ffd8a41007fcc520802fe6290401feb148200bf58a41007f8c52089bff5290401ff2948226ff14a4100ffe8520807bf4290403ff2148201ff50a410077a8520807fc42904037f30c8226ffd4641007fca320803fd519044dfe28c8201ffd064100f7e8320807f74190403fe20c8201fd10641007fec120803fe60904077f3048200ff58241005fac120803fc609044dffa848226ff1424100ffe8120807fc4090403de2048200ffd9541005fecaa0897fe65504057f32a8200ff59541005facaa0897fc65504057e32a8201bfd914100ffea8a0807fe5450403feaa28201ff15141007fec6a0802ff6350401ff31a8200ff58d41007f8c6a081afc635044bffa9a8200ff94d41007faa6a0897fc5350403ffa1a8201ff90d4100ffa86a0807fc4350401ffb128200bfd8941007fcc4a0803fd6250401fe3128200bf1894112ffea4a0803fe5250401fea928225ff1494100ffe84a0807fe4250401df2128201ff5094100ff884a0807bc42504037fb0a8225ffd4541007fca2a0803fd515044bfe28a8201ffd054100fee82a0807fe4150401df20a8201ff1054100f7882a0807f44150401ffb028200bfd8141007fcc0a0803fd6050401fe3028203bf1814112ffea0a0897fc5050403ffa028201efd014100ff880a081bff65cc40d7fb2e6206ff99731015fccb9881bfd65cc4017eb2e6206ff19731035f8cb9881bff64cc40d7fb266206ff9933100dfcc99881bfd64cc4017eb266206ff19331035f8c998893ff54cc447ff2a66200ff5533111ff8a99881bff53cc40dff29e6206ff54f31037f8a79881bff43cc40dff21e6206ff50f31037f8879881bff62cc40dff3166200bf98b31037fac598802fd62cc40dfe3166224ffd4b31007fca598803fd52cc449fe2966223ffd0b31007fc8598803fd42cc447fe2166206ffccb31127fea398803fe51cc401fea8e6224ff1473111ffe8398803fe41cc401fea0e6223ff10731037fec19881bfe60cc4077f3066206ff58331005fac19881bfc60cc449ffa866224ff1433111ffe819888ffc40cc401ffb2c6200bfd9631117fccb1880afe658c401feb2c6200bf59631117f8cb1880afc658c401ffb246200bfd923110ffcc918806fe648c401feb246200bf5923110ff8c918806fc648c445ffaa46221ff95231007faa918887fc548c4017eb1c6222ffd4e31037fca718803fd538c40dfe29c6221ffd0e31037fc8718803fd438c40dfe21c6200ffd8a31007fcc518802fe628c401feb146200bf58a31007f8c51888bff528c401ff2946200ff54a31117f8a518887ff428c401ff2146200ff50a3110ff8851881bff328c401ef9946200ff8ca31035fcc31888bff518c401ff28c6200ff54631117f8a318
  | 6 => 0x5fe28c8601ffd064300ff88321807bc4190c0dffb048606ff9824301dfcc12181bfd6090c017eb048606ff18243157fea1218abfc5090c03ffa048601efd024300ff88121803ff6550c017fb2a8600dfd9543004fecaa18a7fe6550c057f32a8600ff59543005facaa18a7fc6550c057e32a8600df19543014f8caa181aff6450c03ffaa28601ff9514300f7ca8a1807fd5450c01deaa28601ff1514300dfec6a18a7ff5350c0dff29a8600ff54d43037f8a6a1807ff4350c03efa1a8606ff90d430377c86a181bfc4350c0dde21a8601f710d4300f3886a1803ff6250c017fb128600ff98943007fac4a1803fc6250c017e3128629ffd494314ff8a4a1807ff4250c03fe2128600ffd8543005fec2a1803fe6150c01feb0a8600ff18543005f8c2a18a7ff5150c53fe28a8601ffd054300ff882a1803ff6050c017fb028600ff98143007fac0a1803fc6050c077e3028629ffd414314ff8a0a1807ff4050c03fe2028602bf59651007fec9288a3fe64944037f324a200ff59251005fac9288a3fc64944037e324a202ffd5251016fea92880bfe5494405feaa4a200df55251017f8a928803ff6394401ff31ca206bf98e51007fac728802fd6394401fe31ca202ffd4e51017fca7288037e5394405fea9ca202ff14e51016f8a7288a3ff4394401ff21ca200ff50e51147f88728803ff6294401ff314a200bf98a51007fac528802fd6294401fe314a202ffd4a51016fea52880bfc5294451ffa14a200ff90a51147f8852880afe6194405ffa8ca202dfd4651017eea32880bfc5194405fa28ca228ffd0651147f88328803ff6094401ff304a203bf98251007fac128802fd6094401fe304a202ffd4251017f8a12880b7c5094451ffa04a228ff10251015fecaa8803ff64544017fb22a227ff9915100dfcc8a8803fd645444ffe322a201bf19151017fea8a880bfe5454405feaa2a202ff15151007fec6a8802ff6354401ff31aa200ff58d51007f8c6a881afc6354405ffa9aa202ff94d51017faa6a880bfc535444fffa1aa200ff90d51007fa86a889ffc4354401ffb12a200bfd8951007fcc4a8803fd6254401fe312a200bf18951017fea4a880bfc5254405be292a227ffd0951007fc84a8803fd425444ffe212a202bfd8551017fea2a880bf75154405ff28aa200df94551017f8a2a880b7c5154405fa28aa227ffd055113ff882a8803ff60544017fb02a200ff98151007fac0a8803fc60544077e302a202ffd4151016fea0a880bfc505444fffa02a227ff10151007fecb20802ff659044dff32c8202bf99641007facb20802fd659044dfe32c8202bf1964100dfac920807ff5490403ff2a48201ef9524100ffaa920803bd5490403fe2a48200ffd8e41007fcc72081afe6390401feb1c8200bf58e41007f8c72089bff5390401ff29c8200ff5
  | 7 => 0x100300000000000000600000200600000000000200200100100100200200c00500600000000100300200100000100000000000000100000000100000100000000000000000600200000400301400000100100000000000000300200100400000100000000200100000400200000300400400300000300000000000200400500500000500000300100400500301300400700300000200000600100300200000000000500100400000000000600000000100800300000200000000000601b00400100100000500100200000000000100000100c00a00001300000000100600800000600500900100000300500000600200000200200100100100400300000000400000500400000100100000300100100100100000300000200300000100300700000100000100000000100000000000000000500000500400700600200000300400500100400000100700000000500101900200500000200800000300000a00900200500300000400000000000300000100000400000000000000000100000000100300301700000000001000500000000400000200200100000400000000000000000000e00200200100000100000400400000000100000200000100000100200000000800100200100000300a00000500001200800500000100100000c00400000000200000400400200000200600000100200000e00000100900200100200200100000400200200000200000100200200000000100100600200300000000701300000000100000000200000300300300000000200b00000000200300000000000000600100400200000000500000200100300b00000100100000100000a00000000500200100100000d00200000200200000000500100000000000100100000000dfec8aa007fe5455003bf2a2a801ff1515400f78a8aa0073c5455001ffb1aa800bfd8d54007bec6aa002df6355001ff31aa800ff58d54007f8c6aa01afc6355001ee31aa800b718d5400ffe86aa007bf4355003fe21aa800ffd8554005fec2aa003fe6155001feb0aa800ff18554005f8c2aa00bff5155005fe28aa802df1455400ffe82aa007fc4155003de20aa800ffd8154005fec0aa003fe6055001feb02a800ff1815401df8c0aa007ff4055003dfa02a801ff10154037fecb2181aff6590c0dff32c8602bf99643037facb21802fd6590c0dfe32c8606bf1964300dfac921807ff5490c55dfaa48601ff9524300ffaa921807fc5490c03de2a48606bf98e43037fea72181bfe5390c0dfe29c8606ffd0e430377e8721807df4390c0dfe21c8606f710e43037fec52181bfe6290c017f3148606ff58a43005fac52181bfc6290c55ffa94862aff14a4300ffe8521807fc4290c03de2148606ffd8643037fcc321802fe6190c0dfeb0c8600bf58643037f8c3218abff5190c5
  | 8 => 0xea42184434c676562000c5220d7d00006f20000000000000005b60000000000006ca9bb4861fa00000099a0000001b2000000c54972a8ca1000047d49a825000000048502354ae10000000007260000d69f34c89dfba4a0200000095a0008f4c3ca9e0000001aca3093e7bc000baca24c8d0000006a90000000000000000006de00087042826ea3460ebba46d0001310f464bbde0000000000000000000000004400000000004667ae0000000008df00000000064c4ea276000cbcbe0616358444605888898000336000000000000192040000bbe4470000002b2beabee50616c2c96ef5ae08c9d08acb2c00026a1440e289400040fc44196ba00000004b69e86702f640809cbc010ca4a000b6045f08e282ae00128140005c46905910008b6a3900000029a5a82f03cf00094a000cb20000007fabd300061a92616d000aeeb6e4de87e5600150006449847a841bca43c00002847ec000000000b5a23e0000006c4000000000cbb7d800000000000040100000000042c0000000000000000000590005ac49711e25e000be2668000cbd3994c20000000000000000000000006820000007a100028002e00000099852479a49b00092a2fc352000c2056ea0812600000000067d2c05b415e1e081b0001e90000000000000000000000000000006045c591a3bf00045e0000003bb000aa83af84c74c57a0000000000000003daa628225f4aea8645fa00027e0dca68b0e0004e9a00000a420000000007c67b400005000021c0000000000008d04006148680002ba0003c400087512abf650a10021834a320b2a0000000000000007feb167d2000b5537c3d43700006ae00073e000aca01e00057e00800100000400100300000400100000100100100000000100000000300000000600300100100f00f00000a00000000500000000d00000400b01100000b00000600000000100200800200000000000000300000300000000200900100200000000500200000000000300000000000000200100400000000400000000000100700000800100300500100100400500200000500400300400000200400d00200000000100000000300100000200400100000000100000100100000300300000500000200000000100000000400000200100a00200100000100100000200000700100800000100800000500500000100100f00200100000100000200100800000000500100400200b00200400000200200100000100000000000000000000100100500000000000800000000300000300800800300000500e00800000000000100000600200100600500400100100100400200000100500400300000000200100000000500300000200000901200900000100200800000100000200800500000000100700400300000000200000000600200000200
  | 9 => 0xc18000bb60000008620000a40003abb78bf80002d00008c1026000198000a7c65e43ab5e0000000741a03ad0000000da2e72ff94072160b701000b06c98000172704210000164c7e21a9201a4ba205200043e0003b427a00000000000000000024c600bb4000b1052200000038344aa6e9e40002f400005eae6398ad800000087c44b5bc55e000200620a800000020003460000000000002e800000047a0000009de00081f0008ea77c1d80004760000006b02ca0000000000001463650009bd5dc493aa41431209464896a069d000000c1029265169ca1e156b324b4848570b94b8c49c3420000340000007c77bdac682ca960005aaab4533000000000000aa60000005720006ee00067a0001cc60a00000052e00037241900000000000000000000000042b0aa6eab6c50e708000675132c934f87724530000004fe0000000000000000005a75cc7b80002a4a58c3a0004fa6a8000000000000000c9210e68e2fa3df3dc8235920007227e2000000000a5a3fd33a7ba0000000007fc20b5369420006b22ac2d4806000000000469c900003330000007d40003f368a0000160005380003c60000000004750000000000000007a6c34bb80000009baacc00035c80e00000000000000000000000027d0000ec00039f000000bc21ed000a44774380a160009bc000000c46092c8335700040b882a22ca2b7006a96a48e6341c88d61b82b02863871ee000be800011a5ef417c88000c48032000000000304000000000c9abc40000000000a000000000000000000000000000000000061e812c4a72c24156a72423d4ff0000000009f20000009d6730000ba87ac33e82d43258600000000064f00000049d619000a1c0000008c400053a00000000000000000000089e0000000009100007840003a10000007500000420008ca0000000000000000000000000000e00002980006810003d70000009ea92e6710ca000000a9a20a602477000a040006c200075604ab9048f0000005e2000000000000000000000bfa00093200000081d0000006ba3a93160000000000572aa0000007f600097e00000000022c9164c000094c000104000ace00000000091e00000400000000000000000093d000000000000000000a9480c43362e58c0970004e212ea8d2429c0000b7455804e039000000000000b4a0225fc66a9d200000000000045a06e0000009aa36f9886847c413847b353582ab6000000000000000798598494000bd490600007c2a2295c9f00033c67298a6b6bfe2e2000000000874aba7320006fa59a00000000017e000516000a8a0000000000000006560003c83fe000076736093b3880243f2e40000001c9c5eb26000518b1e0000002668421105080007d60000006277900000005423ae000000b88615c12000c75000230
  | 10 => 0x39e0000007917e60009ec0000001900b424e000c6044236600016b18b0004072e04520000190000000000001d20000001940001ea394409000446000000000000000000000000351aec6da00000000000000000001384015a09e0005f10000004100001d400035d0c4c0c52600041a00095c00000090200a5d28b259f0003900c87460000bcb1c3f28ce0000e3aa01862cc75a3d0000a529fa000000b182a603c5d70000005c30006473b76e92c32240c07c26133780001d0bfca549a279352878687a41d00025064900030a00082e0006990000000de2f85b294800021480861f3e100064391279638c0007409a40000006c000029d70e0009b2c9716e2d200000000000000015c2b80000000009823a70000008f2000c95b6900000017a1ce8c6ae23db6545c688028d63e83a4be0002940a893c384000000000000000b6b818b5300020e0000002080008d2000000000000000664000ac8000c0493800000038879b08a10abda17600031e0007dc000000000b685e0b802818a000000053c37943545988e000000000c1c000c2a9da0000001e551f3cbb4255ca9878c5352d8000000000962bdc00000007a9dcb7c7520f76dc660c2c000000000c7a00021d00000014200023a000c0e000000000000b3e0000003fb00006c13e2a027fa865406a70004e80000445e60005ea0f10000000000009b93440005a60000004aa00000063f000c9400000000073c14a0005a2ac02700000000000000000000006803d9a6400000000000090a1b6cb418c0000007f4000098000000afa45b0000000005f84200003970000000000008fc0580000000007becb7000000000000af45d8314000000bbc0000003de0007a276c9f87120000000009611de964959000c6e0000000003e3000baec3e000608673beca12000000c854633ff3e2b4600000000000000066c0001bc9940008e0000a4e22e0007e938ec8a000000000c72b9abf014c3c5000ca89ae0d077000000000000000000036e00000096e0000003b928aa3c000c746f6b8400c9c5000000000000510434000a707889e600000000018e000a3e37a9860006677760000312b4216bd60007f06cc0005c851280400088ac624caca624d00000003e000c4ca787e0000af65da0692bea6300009ab0439500000077e3d23553ca4cc000816a7a000000000000000bdb62600000000034e0000000000004826a11820008ec0000001dc10f2528c082062a000b642da2320008fa000000000000a200001180000000000000006a48bc0003600000001ec4680000008362289f029600035e0000300009760007de0000000007820009b800034700000000056800000061738a424b8e0009520008346404e40006100000008e870a00074200066600000000019e000000000000000000000b58c8f00000040a0
  | 11 => 0x3fa1409e10000000d4000000000000a32762000a74000000935c2e5960000001281540060008c86e03aa01bac427b34150166536300048a5a43eea76308a560003c20000005f62266580000001020004710000005ca5540005b04ec8baaae0960001f657c8380003b2000b52000000000000000c580000000000000007ca000a1a000a923ea55694413d0002483dd766000832000000000a8e42e1fe91c4185046070000002eec260862934130f664a4ed700461000000c9c000b22cac9cc98cc400000000002ea8e68d400000069f00000000000000011704631cb4ec9e51ebcc0e83b60000003450003964950000ce1790009a600076a9b46a22029b00004dc40584abcec9b2d623b10793f0002530000000549040004991d65a1c5aa460002bd6e3a40000c089b60007f80000000000002900000007070000000004856a5000000000000000c5c00000078d4028e20008f6a2a000000bf2a75000c0a0fb60160900032456767c3680000000000007f20000004a0000a0e00000000000000000049f0000000000000000000002c84b200000065c66e0007e88b40004270000000000000f20002c4000116000000272b300000008be0000000000f9a88000000000c917b67e485682a85a000a6617d0000002c13e00006e78a63b000079528f00074a5660000000008260004510000003e50000003003210000006e88860000000000003e40000b80001fc0000942444f7000000000b48000b6a32600036a73bc800000003f10000000007344394f6000ad200000085069e0003c76320a269b58a0000007a4000000000000350720000778c700727389144bf1e2b8200049000054a13069a6f83a6000000000000532638000a6ab7e0006beab85143ce02c0001524730910b1892000b140009ee4b00007991f44965346224f359037e9e000075e0003c964d0000005449c447c1cd23600000055200000078e0003e60000000000006a6000612302cb60006832cb37d0006f168c15506871b23872841500044f1c697c54617c00048c937064000484000000000c14cb8000000bd8000000852000000000c32b34af3afc1aa3a8adf68894e6f49fc000000000000000c16a480000000000002750000000000000003efb24b120006e20000004416535d00b242600092286022a00000047f6ec430000b62000084000b0a6e129e0002bb0000000000000000004ee000000c6c0001b08e70003e80008dd9a80000006d20000008493714fc9830000007a331276e0000002ce71666fb00ac20001609680000000006ac00000000058e00000000031a4d400000067b00071a3b8000000000465aac000bca000ad41220003433f42f90005b84ac4670000000003810003397eac760000000000009ac000000000204bdda50000403392bd06980003d646e62957400
  | 12 => 0xfe6d40f58284785643698da0ab46c20c65a0784a62ec28899cc71b86b2802802b0610b60000b04d608800020f2f224a0000008104060000004a8491000000000754000792000c89038c8cb9cb760000000000000000fa7ee8b58ee25c178b5c3c100000018840e62500000000000000013a000679c8b000baa0005de27c00068600000000010daf047037f00045000000089a0000000000000005d43370001740d80007bf000abc59ca2e0000000001c49f60000003a496c0f8000000000000000a4c000000a0a00036400000000000000000000000052c4bb0000001347cc64595867e6960001f2412a0ca8250c3f00003bd7144376ce05c35f8546610000000000001370008f80000000000000005948b95610667b206b0000000000007066418580000000000000004ce00035b00000004c0000000000008aa0e4af8caa0000001ba77a000000b4c32214800086600099200000000000000000000000000000016a0241b432acbf0000002781e46c6a3663086a08229cb5088400000021746a000000000000ade0eea72000a380005973355c20002466fc376c2436cb9e5f200000000000005b000c782b932e61d4c466b6df00001839313b9806feb5410985e91800000000051a1ef76058800000066d000000000000000000000cb0c4240c000000aaa0003823bac571dabd251c000c6a000008000674a77a610001dd0000004b90008c30004600009d80000001088e43b520663c6243860002ed88c6524880008b869200093654e0000002b6584483000000000a9c000cbe00072a59db0276421255a349a180000005e40000000000001d100076870c00072e00000099e00043640400034d0e678f7440000000000000000000000000007c09a09c600042a39c74ea604ef34f0c2a6c8b00009609500004e642300000000000000000000000013c0001804250001cf0ba14535659e0144621e80c6000b088ae00003ac990003a3c38c8600043d000b980000003384790009906d60be0000001c0abe6b860fc665a00004e000075c0000005fe97400000082b31006300064e0000000000000006110004d8000000ae810600000018aa14ab041f6aa1628dc31803b86e7ce0004a219c0000000000000006180005ba4f5328000c4e3bc0001358b35a93c3af27a04b3000ad64a40005d60000000005f04bc4727b00000000000a62dc93079c0000000001ca297b660290003d8000000080000056663000000abf93a0006b4b72170000000000ae43cdbe42602a800000064683c3b139a1b13a292808344c1ae00049852a0004580000007c8595c0630e71e23c000000c7c000414a3a00000000001d90e6e625800021e00080a4f200000000000000044eaa24450001e60000004228bb5301360000000000000000000004f487800000049e0000000003ec
  | 13 => 0x481036b3a81c648621b2ec96000000361000b576d80000001cb00036b3fc0008de85c25400000000e0004ae000000000000bb20000000200000008c200000080054c000000924000000000996000306a266e42e64daad060cbc600000000000000041e0000000000000000005216286785e89d4c9d0f31123625ec44dc56a28bc89ce0000004f079400000084601c0000000000000004920ae6236bc0ac1e779e000000000000000060b92b8a474970650133000000000000b3607e53e54866243b0003d50000007800001240009ca00089c00057662cc82a0600015046fc2847e3ed035000896b40954c874ba01a758bb0000c73000000000256b96a2cc8428eb7a5781be9ff0004160008a400005a00000095600000048000021190014e00000000000000073a000b3c7aa00035a8cc0009fe6420004110007180005932400000000000000007da0004560003a095b0d200000011c6940005ce71c1c284f000c8e1a8847166677385c30000000000332000978000000000340000a3b90986cb5600045d0001f056c8a8000000168890000c00c1a0000902c20f0017000ada5be000000000cae0003f861c334000702367000000000c02cba2648f0010afeadc97a3beca06695c06f06366a30000002154439e28241df000be60000000000000000000000000000000000005ee000000000c5000060600028c330b1a5200002de2fec1e753000000876500374c680000000000003cc000033000000a3700035992ca7e748000ba64b80000000000cc0000000000004eb000bf400000084e00083e00026298e30c2b702a67f6dd9c823400048700046b438000b2090c8fe22232c00045cc220000000000000000006c826c11196600000000000045400043c8a225a34b00000019a63a0003b31a200005d000a5c0004480003ac9c261b0000004c600012c6bf6d01587100004d042900037b0004491a63482749be00040da5e22000000000021f0000000001f80009080002bc070000c368304d2ab23f65800000620008720000000fc81a1840000002c600011446400041c3a52e926801138995e60d78a9f4c6456300000081e36db0c934703a842aeb44000000a900000005508d80
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe658c4100067d658c41010ebe648c410006bd648c410036de638c410006dd638c410006ee628c410006ed628c41001dfa708c410005f9708c410004ff764c4100057f754c41002d7c754c4101067e654c4100067d654c410005bf744c410025bc744c4100febe644c410006bd644c410036de634c410006dd634c410006ee624c410006ed624c410034ff760c41001cfe760c410004fd760c41001cfc760c4100f67e650c4100067d650c4100eebe640c410006bd640c410036de630c410006dd630c410006ee620c410006ed620c410007d5310c41001dfa700c410005f9700c410004fd76c841002d7e75c84100057d75c84101767e65c84100067d65c8410025be74c8410005bd74c841016ebe64c8410006bd64c8410005de73c8410005dd73c8410006de63c8410006dd63c8410006ee62c8410006ed62c8410165f576c8410006f576c8410004f576c84100077675c84100077575c84101677665c84101677565c8410007b674c8410007b574c8410167b664c8410167b564c8410007d673c8410007d573c8410167d663c8410167d563c8410166f762c8410167e662c8410006f562c8410167e562c8410006e562c8410165f770c8410165f570c8410166f660c8410167f260c8410167e720c8410167e520c8410004ff7688410004fd768841002d7e75884100057d75884100e67e65884100067d6588410025be7488410005bd74884100debe6488410006bd6488410005de7388410005dd7388410006de6388410006dd6388410006ee6288410006ed628841015df67188410006f6618841001dfa7088410005f97088410004ff76484100d67e65484100067d65484100cebe6448410006bd6448410006de6348410006dd6348410006ee6248410006ed6248410006f66148410004ff760841001cfe7608410004fd760841001cfc76084100c67e65084100067d65084100bebe6408410006bd6408410006de6308410006dd6308410006ee6208410006ed6208410007e5210841001dfa7008410005f9700841015df57608410006f57608410004f5760841015f76650841015f75650841015fb6640841015fb5640841015fd6630841015fd56308410165f67208410007e6720841015ef7620841015fe66208410006f5620841015fe56208410006e5620841015df7700841015ff2700841015df57008410007f1700841015ef6600841015ff2600841015fe6200841015fe4200841001dfb7644010006fb7644010004fb76440100077b754401000778754401001f7a654401001f796544010007bb7444010007b8744401001fba644401001fb96444010007db7344010007d8734401001fda634401001fd96344010007eb7244010007e8724401001fea624401001fe9624401001dfb714401001ff37144010006fa614401001ff26144010
  | 1 => 0x481001cfe7654810004fd765481001cfc76548100167e65548100067d65548101cebe6454810006bd6454810006de6354810006dd6354810006ee6254810006ed6254810005f77154810005f47154810004ff769081001cfe7690810004fd769081001cfc76908101c67e65908100067d659081000ebe6490810006bd6490810006de6390810006dd6390810006ee6290810006ed6290810004ff765081001cfe7650810004fd765081001cfc76508101be7e65508100067d655081000ebe6450810006bd6450810006de6350810006dd6350810006ee6250810006ed6250810005f77150810005f47150810034ff76cc81001cfe76cc810004fd76cc81001cfc76cc8101b67e65cc8100067d65cc8101aebe64cc810006bd64cc810036de63cc810006dd63cc810006ee62cc810006ed62cc810005f671cc810005f571cc810004ff768c81001cfe768c810004fd768c81001cfc768c8101a67e658c8100067d658c81019ebe648c810006bd648c810036de638c810006dd638c810006ee628c810006ed628c810004ff764c81001cfe764c810004fd764c81001cfc764c8100057f754c81002d7c754c8101967e654c8100067d654c810005bf744c810025bc744c81018ebe644c810006bd644c810036de634c810006dd634c810006ee624c810006ed624c810005f7714c810005f4714c810005fb704c81001df8704c810034ff760c81001cfe760c810004fd760c81001cfc760c8101867e650c8100067d650c81017ebe640c810006bd640c810036de630c810006dd630c810006ee620c810006ed620c810014fe7598410064fd7598410014fc759841000cfe749841005cfd749841000cfc7498410034fe7398410004fd7398410004fd729841001cfe719841001cfd709841001ef6109841001efa109841001ef41098410064ff769441001cfe7694410014fd769441001cfc76944100167e65944100067d6594410146be6494410006bd6494410006de6394410006dd6394410006ee6294410006ed629441002f77519441001dfa7094410005f97094410064ff76544100167e65544100067d655441013ebe6454410006bd6454410006de6354410006dd6354410006ee6254410006ed625441005cff769041001cfe769041000cfd769041001cfc76904101367e65904100067d659041000ebe6490410006bd6490410006de6390410006dd6390410006ee6290410006ed629041001dfa7090410005f9709041005cff765041012e7e65504100067d655041000ebe6450410006bd6450410006de6350410006dd6350410006ee6250410006ed6250410027b44150410004fd76cc4101267e65cc4100067d65cc41011ebe64cc410006bd64cc410036de63cc410006dd63cc410006ee62cc410006ed62cc410004ff768c410034fd768c4101167
  | 2 => 0x36de6390c10006dd6390c10004ff7650c1001cfe7650c10004fd7650c1001cfc7650c100057f7550c1002d7c7550c1014e7e6550c100067d6550c1000ebe6450c10006bd6450c10036de6350c10006dd6350c100279c4350c10005f77150c10005f47150c10014fe7598810004fd7598810014fc759881000cfe7498810004fd749881000cfc7498810034fe7398810004fd739881001eee7298810006ef5298810006ec5298810006ef4298810006ec429881001cfe709881001eee209881001eec2098810006ef7598810006ee7598810006ed7598810006ec7598810006ef7498810006ee7498810006ed7498810006ec7498810006ef5498810006ee5498810006ed5498810006ec5498810006ef7398810006ee7398810006ed7398810006ec7398810006ef5398810006ee5398810006ed5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec4398810006ee7198810006ec7198810006ef5198810006ec5198810006ef4198810006ec419881001eef709881001eee709881001eed709881001eec709881001eef509881001eee509881001eed509881001eec509881001eef409881001eee409881001eed409881001eec409881001eef309881001eee309881001eed309881001eec309881001eef109881001eee109881001eed109881001eec1098810004ff7558810014fe7558810014fc7558810004ff745881000cfe745881000cfc7458810004ff7358810034fc735881001eef7258810006ef5258810006ec5258810006ef4258810006ec425881016cff71588100ccfd7158810006f4715881001cff705881001cfe705881001cfc705881001eee205881001eec205881001ef7105881001ef51058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810006ee7158810006ec7158810006e47158810006ef5158810006ec5158810006ef4158810006ec415881001eef705881001eee705881001eed705881001eec705881001eef505881001eee505881001eed505881001eec505881001eef405881001eee405881001eed405881001eec405881001eef305881001eee305881001eed305881001eec305881001eef105881001ee7105881001eee105881001eed105881001ee5105881001eec1058810004ff769481001cfe7694810004fd76948100167e65948100067d65948101d6be6494810006bd6494810006de6394810006dd6394810006ee6294810006ed6294810004ff765
  | 3 => 0xf305901001ebe305901001ebd305901001ebc305901001ebf205901001ebe205901001ebd205901001ebc205901001ebf105901001ebe105901001ebd105901001ebc1059010004ff765501001cfe7655010004fd765501001cfc76550100167e65550100067d655501000ebe6455010006bd64550100273c5455010005df7355010005dc7355010005f77155010005f47155010036df7598c10036de7598c10036dd7598c10036dc7598c10036df7498c10036de7498c10036dd7498c10036dc7498c10006df5498c10006de5498c10006dd5498c10006dc5498c10036df7298c10036de7298c10036dd7298c10036dc7298c10006df5298c10006dc5298c10006df4298c10006dc4298c10036de7198c10036dc7198c10006df5198c10006dc5198c10006df4198c10006dc4198c1001edf7098c1001ede7098c1001edd7098c1001edc7098c1001edf5098c1001ede5098c1001edd5098c1001edc5098c1001edf4098c1001ede4098c1001edd4098c1001edc4098c1001edf2098c1001ede2098c1001edd2098c1001edc2098c1001edf1098c1001ede1098c1001edd1098c1001edc1098c10004ff7558c10014fe7558c10014fc7558c10004ff7458c1000cfe7458c1000cfc7458c1001edf7358c10006df5358c10006dc5358c10006df4358c10006dc4358c10004ff7258c10004fc7258c10034ff7158c10034fd7158c1001cff7058c1001cfe7058c1001cfd7058c1001cfc7058c1001ede3058c1001edc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006dc5258c10006df4258c10006dc4258c10006de7158c10006dc7158c10006df5158c10006dc5158c10006df4158c10006dc4158c1001edf7058c1001ede7058c1001edd7058c1001edc7058c1001edf5058c1001ede5058c1001edd5058c1001edc5058c1001edf4058c1001ede4058c1001edd4058c1001edc4058c1001edf2058c1001ede2058c1001edd2058c1001edc2058c1001edf1058c1001ede1058c1001edd1058c1001edc1058c10034ff7694c1001cfe7694c10004fd7694c1001cfc7694c100167e6594c100067d6594c101e6be6494c10006bd6494c10036de6394c10006dd6394c1002f5f5394c10004ff7654c1001cfe7654c10004fd7654c1001cfc7654c100167e6554c100067d6554c10005bf7454c10025bc7454c101debe6454c10006bd6454c10036de6354c10006dd6354c10005f77154c10005f47154c10034ff7690c1001cfe7690c10004fd7690c1001cfc7690c101567e6590c100067d6590c1000ebe6490c10006bd6490c10
  | 4 => 0xc11007ebc644c110006df634c110036dc634c110006ef624c110006ec624c110005f7714c110005f4714c110004fe76c81100067f65c81101fe7c65c8110006bf64c81101f6bc64c8110006df63c8110006dc63c8110006ef62c8110006ec62c8110005f671c8110005f571c8110007e521c8110004fd7648110004fc7648110005bf744811003dbc7448110006bf64481101eebc6448110006df6348110006dc6348110005f77148110005f47148110007e521481100067f65c41100667c65c4110006bf64c411005ebc64c4110006df63c4110006dc63c4110006ef62c4110006ec62c411001df671c411001cfa76c41100077b65c41100077865c4110007bb64c4110007b864c4110007db63c4110007d863c4110007eb62c4110007e862c411001dfa71c411001ff361c4110007f221c4110007f121c411001e7f7559410004ff745941000cfe745941000cfc745941002e7f54594100067e545941002e7c5459410004ff7359410034fc735941002e7f535941002e7c5359410004ff7259410004fc725941002e7f525941002e7c5259410014ff7159410014fd715941002cfc715941002e7c515941001cfe705941001cfc705941001e7e505941001e7c50594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067c425941002e7f71594100067e71594100067c71594100067f41594100067c415941001e7f705941001e7e705941001e7d705941001e7c705941001e7f405941001e7e405941001e7d405941001e7c405941001e7f305941001e7e305941001e7d305941001e7c305941001e7f205941001e7e205941001e7d205941001e7c205941001e7f105941001e7e105941001e7d105941001e7c1059410004ff7559010014fe7559010014fc755901001ebf7459010006bf5459010026be5459010026bc5459010004ff7359010034fc7359010026bf4359010026bc4359010004ff7259010004fc7259010026bf4259010026bc425901000cff715901000cfd7159010024fc7159010026bc415901001cff705901001cfe705901001cfd705901001cfc705901001ebe405901001ebc4059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006bc5259010026bf7159010006be7159010006bc7159010006bf5159010006bc515901001ebf705901001ebe705901001ebd705901001ebc705901001ebf505901001ebe505901001ebd505901001ebc505901001eb
  | 5 => 0x5f970cc510004fe768c5100067f658c5101167c658c510006bf648c51010ebc648c510006df638c510036dc638c510006ef628c510006ec628c51001cfc764c5100057f754c5100457c754c5100067f654c5101067c654c510005bf744c51003dbc744c510006bf644c5100febc644c510006df634c510036dc634c510006ef624c510006ec624c510005fb704c51001df8704c510004fe760c5100067f650c5100f67c650c510006bf640c5100eebc640c510006df630c510036dc630c510006ef620c510006ec620c51001cfe76c85100457e75c85100057d75c85100067f65c85101767c65c851003dbe74c8510005bd74c8510006bf64c851016ebc64c8510005de73c8510005dd73c8510006df63c8510006dc63c8510006ef62c8510006ec62c851001dfa70c8510005f970c8510004fe76885100457e75885100057d75885100067f65885100e67c658851003dbe7488510005bd7488510006bf64885100debc6488510005de7388510005dd7388510006df6388510006dc6388510006ef6288510006ec6288510005f67688510006f67688510004f67688510007767588510007757588510007776588510007746588510007b67488510007b57488510007b76488510007b46488510007d67388510007d57388510007d76388510007d46388510005f57288510007e76288510006f66288510006f46288510007e46288510006e4628851001df6708851001df4708851020fe6208851001cfc76485100067f65485100d67c6548510006bf64485100cebc6448510006df6348510006dc6348510006ef6248510006ec6248510005fb704851001df8704851001cf47648510007776548510007746548510007b76448510007b46448510007d76348510007d46348510007e77248510007e76248510006f66248510006f46248510007e46248510006e46248510007f3704851001df6704851001df47048510007f07048510004fe76085100067f65085100c67c6508510006bf64085100bebc6408510006df6308510006dc6308510006ef6208510005f67108510007e52108510014ff7654110044fd7654110014fc76541100067f65541100167c6554110006bf6454110206bc6454110006df6354110006dc6354110006ef6254110006ec6254110005f77154110005f4715411000cff765011003cfd765011000cfc76501100067f65501100ae7c6550110006bf645011000ebc6450110006df6350110006dc6350110006ef6250110006ec6250110005f77150110005f47150110004fe76cc1100067f65cc1100a67c65cc110006bf64cc11009ebc64cc110006df63cc110036dc63cc110006ef62cc110006ec62cc110005f671cc110005f571cc110034ff764c110004fd764c110034fc764c1100067f654c1100867c654c110006bf644
  | 6 => 0xf501891015eee501891015eec5018910006ef401891015eee401891015eec401891015eee301891015eec301891015eee101891015ee61018910006ed101891015eec101891015ee41018910004ff7694910004fe7694910004fd7694910004fc76949100067f65949100167c6594910006bf64949101d6bc6494910006df6394910006dc6394910006ef6294910006ec6294910005f67194910005f57194910004ff7654910004fe7654910004fc76549100067f65549100167c6554910006bf64549101cebc6454910006df6354910006dc6354910006ef6254910006ec6254910004ff7690910004fe7690910004fd7690910004fc76909100067f65909101c67c6590910006bf649091000ebc6490910006df6390910006dc6390910006ef6290910006ec6290910005f67190910005f57190910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101be7c6550910006bf645091000ebc6450910006df6350910006dc6350910006ef6250910006ec6250910034ff76cc910004fe76cc910004fd76cc910034fc76cc9100067f65cc9101b67c65cc910006bf64cc9101aebc64cc910006df63cc910036dc63cc910006ef62cc910006ec62cc910004ff768c910004fe768c910004fd768c910004fc768c9100067f658c9101a67c658c910006bf648c91019ebc648c910006df638c910036dc638c910006ef628c910006ec628c910005f6718c910005f5718c910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100457c754c9100067f654c9101967c654c910005bf744c91003dbc744c910006bf644c91018ebc644c910006df634c910036dc634c910006ef624c910006ec624c910034ff760c910004fe760c910004fd760c910034fc760c9100067f650c9101867c650c910006bf640c91017ebc640c910006df630c910036dc630c910006ef620c910006ec620c910005f6710c910005f5710c910054fe76945100067f65945100167c6594510006bf6494510146bc6494510006df6394510006dc6394510006ef6294510006ec629451001cfc76545100067f65545100167c6554510006bf645451013ebc6454510006df6354510006dc6354510006ef6254510006ec6254510005fb705451001df8705451004cfe76905100067f65905101367c6590510006bf649051000ebc6490510006df6390510006dc6390510006ef6290510006ec629051001cfc76505100067f655051012e7c6550510006bf645051000ebc6450510006df6350510006dc6350510006ef6250510006ec6250510005fb705051001df8705051001cfe76cc51001cfc76cc5100067f65cc5101267c65cc510006bf64cc51011ebc64cc510006df63cc510036dc63cc510006ef62cc510006ec62cc51001dfa70cc510
  | 7 => 0x8910006ed71d8910006ef51d8910006ec51d8910006ef41d8910006ec41d8910006ef70d891020eee70d8910006ed70d891020eec70d8910006ef50d891020eee50d891020eec50d8910006ef40d891020eee40d891020eec40d891020eee30d891020eec30d891020eee10d891020eec10d89100457e75989100057d75989100067f65989100067c659891003dbe7498910005bd7498910006bf6498910006bc6498910005de7398910005dd7398910006df6398910006dc6398910006ef6298910014fe75989100067e75989100147e7598910004fd75989100067d75989100047d7598910014fc759891000cfe7498910006be749891000cbe7498910004fd7498910006bd7498910004bd749891000cfc7498910034fe7398910006de7398910034de7398910004fd7398910006dd7398910004dd7398910006f57198910006f97098910166f610989100057f75589100457c75589100067f65589100067c6558910005bf745891003dbc7458910006bf6458910006bc6458910005df7358910005dc7358910006df6358910006dc6358910004ff7458910006bf7458910004bf745891000cfe745891000cfc7458910006bc745891000cbc7458910004ff7358910006df7358910004df7358910034fc7358910006dc7358910034dc7358910006f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc6318910006ed6218910014fe7518910004fd7518910014fc751891000cfe7418910004fd741891000cfc7418910034fe7318910004fd7318910006ee7218910006ef5218910006ec5218910006ef4218910006ec42189100bcfc711891001cfe701891015ef6101891015ef41018910005ee7618910006ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910007e5711891015fe6101891015fe41018910006ef7518910006ee7518910006ed7518910006ec7518910006ef7418910006ee7418910006ed7418910006ec7418910006ef5418910006ee5418910006ed5418910006ec5418910006ef7318910006ee7318910006ed7318910006ec7318910006ef5318910006ee5318910006ed5318910006ec5318910006ef4318910006ee4318910006ed4318910006ec431891015eef7118910006ef5118910006ec5118910006ef4118910006ec4118910006ef701891015eee7018910006ed7018910006e
  | 8 => 0x6dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10217d61018d10217d41018d10036df7518d10036de7518d10036dd7518d10036dc7518d10036df7418d10036de7418d10036dd7418d10036dc7418d10006df5418d10006de5418d10006dd5418d10006dc5418d10036df7218d10036de7218d10036dd7218d10036dc7218d10006df5218d10006dc5218d10006df4218d10006dc4218d10036df7118d10036dd7118d10006df5118d10006dc5118d10006df4118d10006dc4118d10036df7018d10036de7018d10036dd7018d10036dc7018d10006df5018d10216de5018d10216dc5018d10006df4018d10216de4018d10216dc4018d10216de2018d10216dc2018d10216de1018d10006dd1018d10216dc1018d10034ff7694d10004fe7694d10004fd7694d10034fc7694d100067f6594d100167c6594d10006bf6494d101e6bc6494d10006df6394d10036dc6394d100475f5394d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100167c6554d10005bf7454d1003dbc7454d10006bf6454d101debc6454d10006df6354d10036dc6354d10034ff7690d10004fe7690d10004fd7690d10034fc7690d100067f6590d101567c6590d10006bf6490d1000ebc6490d10006df6390d10036dc6390d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100457c7550d100067f6550d1014e7c6550d10006bf6450d1000ebc6450d10006df6350d10036dc6350d1003f9c4350d100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910014fe75d8910004fd75d8910014fc75d891000cfe74d8910004fd74d891000cfc74d8910034fe73d8910004fd73d8910006ef52d8910006ec52d8910006ef42d8910006ec42d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d891020fe771d891020fe610d891020fe410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d891020eef71d
  | 9 => 0xc7259110004ec725911004cff7159110006f7715911005cff7059110006fb7059110005be761911003ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110226bf6119110227b61019110227b41019110004ff7655110004fe7655110004fd7655110004fc76551100067f65551100167c6555110006bf645511000ebc645511003f3c5455110005df7355110005dc7355110034fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10014fe75d8d10004fd75d8d10014fc75d8d1000cfe74d8d10004fd74d8d1000cfc74d8d10006df53d8d10006dc53d8d10006df43d8d10006dc43d8d10004fe72d8d10004fd72d8d10034fe71d8d10034fc71d8d1001cfe70d8d1001cfc70d8d10034de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d1021fd610d8d1021fd410d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006dc52d8d10006df42d8d10006dc42d8d1021edf71d8d10006dd71d8d10006df51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df70d8d1021ede70d8d10006dd70d8d1021edc70d8d10006df50d8d1021ede50d8d1021edc50d8d10006df40d8d1021ede40d8d1021edc40d8d1021ede20d8d1021edc20d8d1021ede10d8d1021edc10d8d100457e7598d100057d7598d100067f6598d100067c6598d1003dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10005ee7298d10005ed7298d100057f7558d100457c7558d100067f6558d100067c6558d10005bf7458d1003dbc7458d10006bf6458d10006bc6458d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d1000cfe7458d1000cfc7458d10006bc7458d1000cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d10004fc7258d10006ec7258d10004ec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10036de6318d10006dd6318d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10
  | 10 => 0x95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067c42d951023e7f71d95100467e71d95100067d71d95100067f41d95100067c41d95100067f70d951023e7e70d95100067d70d951023e7c70d95100067f40d951023e7e40d951023e7c40d951023e7e30d951023e7c30d951023e7e20d951023e7c20d951023e7e10d951023e7c10d95100467c6559510005bf745951003dbc7459510005df7359510005dc7359510005ef7259510005ec7259510044ff75595100067f7559510004ff7459510006bf7459510004bf745951000cfe745951000cfc7459510006bc745951000cbc7459510004ff7359510006df7359510004df7359510034fc7359510006dc7359510034dc7359510004ff7259510006ef7259510004ef7259510004fc7259510006ec7259510004ec7259510054ff7159510006f77159510064ff7059510006fb70595100057e76195100467e76195100047e76195100067e64195100067c64195102367f611951023776101951023774101951000cfe76d91100067f65d91100067c65d911003ebe64d9110014fe75d9110004fd75d9110014fc75d9110006bf54d911003ebe54d911003ebc54d9110034fe73d9110004fd73d911003ebf43d911003ebc43d9110004fe72d9110004fd72d911003ebf42d911003ebc42d911000cfe71d911001cfd71d911000cfc71d911003ebf41d911001cfe70d911003cfd70d911001cfc70d911003ebf40d911003dbe76d911000cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d911022fb610d911022fb410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006bc52d911022ebf71d911003ebe71d9110006bd71d9110006bf51d9110006bc51d9110006bf70d911022ebe70d9110006bd70d911022ebc70d9110006bf50d911022ebe50d911022ebc50d911022ebe30d911022ebc30d911022ebe20d911022ebc20d911022ebe10d911022ebc10d91100057f75591100457c75591100067f65591100067c655911003ebc6459110005df7359110005dc7359110005ef7259110005ec7259110004ff75591100067f75591100047f7559110014fe7559110014fc75591100067c75591100147c755911003cff7459110006bf7459110004ff7359110006df7359110004df7359110034fc7359110006dc7359110034dc7359110004ff7259110006ef7259110004ef7259110004fc7259110006e
  | 11 => 0x167c6594a10004ff7654a10004fd7654a1001cfc7654a100167e6554a100067d6554a10005f77154a10005f47154a10004ff7690a1001cfe7690a10004fd7690a10256bf6490a1000ebc6490a10004ff7650a1001cfe7650a10004fd7650a1001cfc7650a1000ebe6450a10006bd6450a10005f77150a10005f47150a10034ff76cca1001cfe76cca10004fd76cca1001cfc76cca10036de63cca10006dd63cca10005f671cca10005f571cca10004ff768ca1001cfe768ca10004fd768ca1024edf638ca10036dc638ca10004ff764ca1001cfe764ca10004fd764ca1001cfc764ca100057f754ca100557c754ca10005bf744ca1004dbc744ca10036de634ca10006dd634ca10005f7714ca10005f4714ca10034ff760ca1001cfe760ca10004fd760ca10246df630ca10036dc630ca1001ef61058610044fd769461023e7f65946100167c6594610057775194610014ff765461001cfc76546100167e65546100067d6554610005fb705461001df8705461003cfd769061022ebf649061000ebc649061000cff765061001cfc765061000ebe6450610006bd645061004fb44150610005fb705061001df87050610036de63cc610006dd63cc61001dfa70cc610005f970cc61021edf638c610036dc638c610034ff764c6100057f754c6100557c754c610005bf744c61004dbc744c610036de634c610006dd634c610005fb704c61001df8704c610216df630c610036dc630c610007d5310c6100557e75c86100057d75c861004dbe74c8610005bd74c8610005de73c8610005dd73c8610006ee62c8610006ed62c861001dfa70c8610005f970c86100077675c86100077575c8610007b674c8610007b574c8610007d673c8610007d573c8610167e662c8610006f562c8610167e562c8610167f270c8610165f570c8610007f170c8610167e720c86100557e75886100057d758861004dbe7488610005bd7488610005de7388610005dd738861020eef6288610006ee6248610006ed6248610005fb704861001df87048610007e5210861015df57608610006f57608610007e6720861015ef7620861015fe7620861015ee76208610006f5620861015fe4620861015df7700861015df5700861015fe6200861001df976c4210006f976c421001ff271c4210014fe76d95100467e65d951000cfe74d9510004fd74d951000cfc74d95100467f54d95100067e54d95100467c54d9510034fe73d9510004fd73d95100467f53d95100467c53d9510004fe72d9510004fd72d95100467f52d95100467c52d9510014fe71d951001cfd71d9510014fc71d95100467f51d9510044fd70d95100467f50d95100457e76d95100147e76d95100067e64d95100067c64d951023f7610d951023f7410d95100067f74d95100067e74d95100067d74d95100067c74d
  | 12 => 0x66288710007e56288710006f4628871001df67088710007f27088710007f1708871001df47088710005f77648710006f77648710007e77248710007e76248710006f66248710006f46248710007e46248710006e4624871001df6704871001df4704871001cfd7608710006ee6208710006ed6208710007e5210871001dfa7008710005f97008710014ff76543100167e65543100067d6554310005f77154310005f4715431000cff765031000ebe6450310006bd6450310005f77150310005f47150310036de63cc310006dd63cc310005f671cc310005f571cc310034ff764c310036de634c310006dd634c310005f7714c310005f4714c310005f671c8310005f571c8310007e521c831001e7f7559610004ff745961000cfe745961000cfc74596100567f5459610004ff7359610034fc73596100567c5359610004ff7259610004fc72596100567f52596100567f515961001cfc705961001e7e505961001e7c5059610004ff7559210014fe7559210014fc755921001ebf745921004ebe5459210004ff7359210034fc735921004ebc4359210004ff7259210004fc725921004ebf425921004ebf415921001cfc705921001ebe405921001ebc4059210004ff765521001cfe7655210004fd765521001cfc76552100167e65552100067d655521000ebe6455210006bd645521004f3c5455210005df7355210005dc7355210005f77155210005f47155210004ff7558e10014fe7558e10014fc7558e10004ff7458e1000cfe7458e1000cfc7458e1001edf7358e10004ff7258e10004fc7258e1001cfc7058e1001ede3058e1001edc3058e10034ff7694e1001cfe7694e10004fd7694e1001cfc7694e100167e6594e100067d6594e100575f5394e10004ff7654e1001cfe7654e10004fd7654e1001cfc7654e10005bf7454e1004dbc7454e10005f77154e10005f47154e10034ff7690e1001cfe7690e10004fd7690e1001cfc7690e1000ebe6490e10006bd6490e10004ff7650e1001cfe7650e10004fd7650e1001cfc7650e100057f7550e100557c7550e1004f9c4350e10005f77150e10005f47150e10014fe7598a10004fd7598a10014fc7598a1000cfe7498a10004fd7498a1000cfc7498a10034fe7398a10004fd7398a1001eee7298a1001cfe7098a1001eee2098a1001eec2098a10004ff7558a100067f7558a100047f7558a10014fe7558a10014fc7558a100067c7558a100147c7558a10004ff7458a10006bf7458a10004bf7458a1000cfe7458a1000cfc7458a10006bc7458a1000cbc7458a10004ff7358a10006df7358a10004df7358a10034fc7358a10006dc7358a10034dc7358a1001eef7258a1001eee2058a1001eec2058a1001ef71058a1001ef51058a10004ff7694a1001cfe7694a10004fd7694a1025e7f6594a10
  | 13 => 0xf100057f7550f100657c7550f1005f9c4350f100657e75d8b100057d75d8b1005dbe74d8b10005bd74d8b10005de73d8b10005dd73d8b100657e7598b100057d7598b1005dbe7498b10005bd7498b10005de7398b10005dd7398b10006ef6298b10014fe7598b100067e7598b100147e7598b10004fd7598b100067d7598b100047d7598b10014fc7598b1000cfe7498b10006be7498b1000cbe7498b10004fd7498b10006bd7498b10004bd7498b1000cfc7498b10034fe7398b10006de7398b10034de7398b10004fd7398b10006dd7398b10004dd7398b10166f61098b10166f41098b10004ff7558b10014fe7558b10014fc7558b10004ff7458b1000cfe7458b1000cfc7458b10004ff7358b10034fc7358b10006ed6218b1000cfe7418b10004fd7418b1000cfc7418b10034fe7318b10004fd7318b10006f67118b10006f97018b10004ff7694b10004fe7694b10004fd7694b100167e6594b100067d6594b10005f67194b10005f57194b10004ff7654b10004fd7654b10004fc7654b100067f6554b100167c6554b10004ff7690b10004fe7690b10004fd7690b10004fc7690b1000ebe6490b10006bd6490b10005f67190b10005f57190b10004ff7650b10004fd7650b10004fc7650b10006bf6450b1000ebc6450b10034ff76ccb10004fe76ccb10004fd76ccb10006df63ccb10036dc63ccb10004ff768cb10004fe768cb10004fd768cb10004fc768cb10036de638cb10006dd638cb10005f6718cb10005f5718cb10004ff764cb10004fd764cb10004fc764cb100057f754cb100657c754cb10005bf744cb1005dbc744cb10006df634cb10036dc634cb10005fb704cb1001df8704cb10034ff760cb10004fe760cb10004fd760cb10034fc760cb10036de630cb10006dd630cb10005f6710cb10005f5710cb1001cfd76947100167e65947100067d659471001dfa7094710005f9709471002cff76547100067f65547100167c655471001cfd769071000ebe6490710006bd649071001dfa7090710005f97090710024ff7650710006bf645071000ebc6450710006df63cc710036dc63cc71001cfd768c710036de638c710006dd638c71001dfa708c710005f9708c7100057f754c7100657c754c710005bf744c71005dbc744c710006df634c710036dc634c71001cfd760c710036de630c710006dd630c71001dfa700c710005f9700c7100657e75c87100057d75c871005dbe74c8710005bd74c8710005de73c8710005dd73c871001cfd76887100657e75887100057d758871005dbe7488710005bd7488710005de7388710005dd7388710006ee6288710006ed628871001dfa7088710005f9708871001cf57688710007767588710007757588710007b67488710007b57488710007d67388710007d57388710006f66288710007e
  | 14 => 0xebe6450430006bd6450430005df7350430035dc7350430006f66150430006f56150430035dd768c430006dd768c430004dd768c430005de728c430006dd628c430035de718c430037d6718c430006dd618c43021ddd708c43021ede608c430037da608c430004ff768843001cfe7688430004fd76884300757e75884300057d758843006dbe7488430005bd7488430035de7388430005dd7388430006f66188430006f56188430004ff7648430004fd764843001cfc7648430005df7348430035dc7348430006f66148430006f56148430005fb704843001df87048430004ff760843001cfe7608430004fd7608430005df7308430035dc7308430007e521084300667e65d971000cfe74d9710004fd74d971000cfc74d97100667f54d9710034fe73d9710004fd73d97100667c53d9710004fe72d9710004fd72d97100667f52d9710006f671d97100667f51d9710006f970d971023e7e50d971023e7c50d97100667c65597100067f7559710004ff745971000cfe745971000cfc7459710004ff7359710034fc7359710004ff7259710004fc72597100667c525971001cfc71597100667c51597100667f505971005ebe64d9310014fe75d9310004fd75d9310014fc75d931005ebe54d9310034fe73d9310004fd73d931005ebc43d9310004fe72d9310004fd72d931005ebf42d9310006f671d931005ebf41d9310006f970d931022ebe40d931022ebc40d931005ebc6459310004ff7559310014fe7559310014fc7559310006bf7459310004ff7359310034fc7359310004ff7259310004fc725931005ebc425931001cfc715931005ebc415931005ebf4059310004ff7655310004fe7655310004fd7655310004fc76553100067f65553100167c6555310006bf645531000ebc645531005f3c5455310005df7355310005dc7355310014fe75d8f10004fd75d8f10014fc75d8f1000cfe74d8f10004fd74d8f1000cfc74d8f10004fe72d8f10004fd72d8f10006f671d8f10006f970d8f1021ede30d8f1021edc30d8f10006df6398f100057f7558f100657c7558f10005bf7458f1005dbc7458f10004ff7558f100067f7558f100047f7558f10014fe7558f10014fc7558f100067c7558f100147c7558f10004ff7458f10006bf7458f10004bf7458f1000cfe7458f1000cfc7458f10006bc7458f1000cbc7458f10006df7358f10004ff7258f10004fc7258f10036de6318f10006dd6318f10034ff7694f10004fe7694f10004fd7694f10034fc7694f100067f6594f100167c6594f100675f5394f10004ff7654f10004fe7654f10004fd7654f10004fc7654f10005bf7454f1005dbc7454f10034ff7690f10004fe7690f10004fd7690f10034fc7690f10006bf6490f1000ebc6490f10004ff7650f10004fe7650f10004fd7650f10004fc765
  | 15 => 0xc7650530005de76cc530036de76cc530004de76cc530005dd72cc530006dc62cc530006dc61cc53001dde70cc53001ddc70cc530036df60cc530037db60cc53001cfe768c530005dd738c530006f7618c530006f4618c53001dfa708c530005f9708c53001cfc764c5300057f754c5300857c754c530005bf744c53007dbc744c530006f7614c530006f4614c530005fb704c53001df8704c53001cdc764c5300075f754c5300075c754c5300079f744c5300079c744c530005df724c530006dc624c530035df714c530037d7714c530007d7614c530006dc614c530007d4614c530006d4614c530007db704c53001dde704c53001ddc704c530007d8704c530036df604c530037db604c530004fe7688530004fd7688530004fc76885300857e75885300057d758853007dbe7488530005bd7488530035de7388530005dd7388530006ef6288530006ec6288530004ff7648530004fe7648530004fc7648530035de7348530005dd7348530004fe7608530004fd7608530004fc7608530035de7308530005dd7308530006f76108530006f46108530007e5210853000cff765013007cfd7650130034fc7650130006bf645013000ebc6450130005df7350130035dc7350130004ff7559030014fe7559030014fc755903001cff745903001ebf745903006ebe5459030034ff7359030034fe7359030034fd7359030034fc7359030036be4359030036bc4359030004ff7259030004fc725903006ebf4259030004ff7159030004fc715903006ebf415903001cfe705903001cfc705903001ebe405903001ebc4059030004ff765503001cfe7655030004fd765503001cfc765503000ebe6455030006bd645503006f3c5455030005df7355030035dc7355030014fe7598430004fd7598430014fc759843000cfe7498430004fd749843000cfc7498430004fe7298430004fd729843001ef67198430036f73198430036f4319843001ef6109843001ef41098430004ff75584300067f75584300047f7558430014fe7558430014fc75584300067c75584300147c7558430004ff7458430006bf7458430004bf745843000cfe745843000cfc7458430006bc745843000cbc7458430004ff7258430004fc7258430036dc325843001ef77158430036f73158430036dc3158430036f4315843001edf305843001edd305843001ef6105843001ef41058430004ff769443001cfe7694430004fd769443023e7f65944300167c6594430006f66194430006f56194430004ff7654430004fd765443001cfc76544300167e65544300067d6554430005df7354430035dc7354430006f66154430006f56154430004ff769043001cfe7690430004fd769043022ebf649043000ebc6490430006f66190430006f56190430004ff7650430004fd765043001cfc7650430
  | 16 => 0xc63001df8704c630215dd760c630036dd760c6302175e650c6302175d650c6302179e640c6302179d640c630005de720c630006dd620c630037d6710c630006dd610c630035df700c630215dd700c630037da600c630004ff768863001cfe7688630004fd76886300957e75886300057d75886300e67e65886300067d658863008dbe7488630005bd74886300debe6488630006bd6488630035de7388630005dd7388630006f66188630006f56188630004ff7648630004fd764863001cfc76486300cebe6448630006bd6448630005df7348630035dc7348630006f66148630006f56148630004ff760863001cfe7608630004fd76086300bebe6408630006bd6408630005df7308630035dc7308630007e5210863000cfe76d913007ebe64d9130014fe75d9130004fd75d9130014fc75d9130006bf54d913007ebc54d9130034fe73d913001cfd73d9130034fc73d913007ebf43d9130004fe72d9130004fd72d913007ebc42d9130004fe71d9130004fd71d913007ebc41d9130034fd70d913007ebf40d91300057f75591300857c755913007ebc6459130005ef7259130005ec7259130005f77159130005f47159130004ff75591300067f75591300047f7559130014fe7559130014fc75591300067c75591300147c755913007cff7459130006bf745913007ebe545913008cff7359130006df7359130266be4359130266bc4359130004ff7259130006ef7259130004ef7259130004fc7259130006ec7259130004ec7259130004ff7159130006f77159130004f77159130004fc7159130006f47159130004f4715913009cff7059130006fb7059130004ff7655130004fe7655130004fd7655130004fc765513000ebe6455130006bd645513007f3c5455130005df7355130035dc735513001cfc7650d300057f7550d300857c7550d30006bf6450d3000ebc6450d300379c4350d30005fb7050d3001df87050d30014fe75d8530004fd75d8530014fc75d853000cfe74d8530004fd74d853000cfc74d8530004fe72d8530004fd72d8530006f751d8530006f451d8530006f741d8530006f441d8530006f761985300057f75585300857c7558530005bf745853007dbc7458530005ef7258530005ec7258530006f56118530014fe7518530004fd7518530014fc751853000cfe7418530004fd741853000cfc7418530004fe7218530004fd7218530006f75118530006f45118530006f74118530006f44118530216de3018530216dc3018530004fe7694530004fd7694530004fc76945300067f65945300167c6594530035de7394530005dd7394530004ff7654530004fe7654530004fc7654530004fe7690530004fd7690530004fc7690530006bf649053000ebc6490530035de7390530005dd7390530004ff7650530004fe7650530004f
  | 17 => 0x8ebc4259230004ff7159230004fc715923008ebf415923008ebc415923001cfc705923001ebe405923001ebc4059230006bf7559230006be7559230006bd7559230006bc7559230006bf7359230266be7359230006bd7359230266bc7359230006bf5359230266be5359230266bc5359230006bf7259230006be7259230006bd7259230006bc7259230006bf5259230006bc5259230266bf3259230266bc3259230006bf7159230006be7159230006bd7159230006bc7159230006bf5159230006bc5159230266bf3159230266bc315923001ebf705923001ebe705923001ebd705923001ebc705923001ebf505923001ebe505923001ebd505923001ebc505923001ebf305923001ebe305923001ebd305923001ebc305923001ebf205923001ebe205923001ebd205923001ebc205923001ebf105923001ebe105923001ebd105923001ebc1059230004ff765523001cfe7655230004fd765523001cfc765523000ebe6455230006bd645523008f3c5455230005df7355230035dc7355230036fb3058e3001ede3058e3001edc3058e3001ef83058e3000cff7650e3001cfc7650e300057f7550e300957c7550e3014e7e6550e300067d6550e3000ebe6450e30006bd6450e300379c4350e30005fb7050e3001df87050e30014fe7598630004fd7598630014fc759863000cfe7498630004fd749863000cfc7498630004fe7298630004fd729863001ef6719863001cfe709863001ef6109863001ef41098630004ff7558630014fe7558630014fc7558630004ff745863000cfe745863000cfc7458630004ff7258630004fc725863001ef7715863001cfc705863001edf305863001edd305863001ef6105863001ef41058630004ff769463001cfe7694630004fd76946300167e65946300067d6594630146be6494630006bd6494630004ff7654630004fd765463001cfc76546300167e65546300067d655463013ebe6454630006bd6454630005df7354630035dc7354630004ff769063001cfe7690630004fd76906301367e65906300067d659063000ebe6490630006bd6490630004ff7650630004fd765063001cfc765063012e7e65506300067d655063000ebe6450630006bd6450630005df7350630035dc73506301167e658c6300067d658c63010ebe648c630006bd648c630006f6618c630006f5618c63001dfa708c630005f9708c63021f5e658c63021f5d658c63021f9e648c63021f9d648c630005de728c630006dd628c630035de718c63021fd6618c630006dd618c63021fd5618c63021fda708c63021ddd708c630007d9708c630036de608c6300057f754c6300957c754c6301067e654c6300067d654c630005bf744c63008dbc744c6300febe644c630006bd644c630006f6614c630006f5614c630037d4314c630005fb704
  | 18 => 0xe76c8540004fd76c8540004fc76c85400ad7e75c85400057d75c854000dbe74c8540005bd74c8540005de73c8540005dd73c8540006f761c8540006f461c8540004fe7688540004fd7688540004fc76885400ad7e75885400057d758854000dbe7488540005bd7488540005de7388540005dd7388540006ef6288540006ec6288540004ff7648540004fe7648540004fc764854000dbe7448540005bd7448540004fe7608540004fd7608540004fc760854000dbe7408540005bd7408540006ef6208540006ec6208540006f76108540006f46108540007e5210854000cfe7654140204fd765414000cfc7654140005bf745414000dbc74541400073d5454140004ff7559330014fe7559330014fc7559330036bf745933009ebe545933001cfc7359330036be4359330036bc4359330004ff7259330004fc725933009ebc4259330004ff7159330004fc715933009ebc415933009ebf4059330004ff7655330034fe7655330004fd7655330034fc765533000ebe6455330006bd645533009f3c5455330005df7355330035dc7355330014fe7598730004fd7598730014fc759873000cfe7498730004fd749873000cfc749873001cfe739873001cde7398730004fe7298730004fd7298730036df3298730036f67198730036df3198730036f73198730036f4319873021ede3098730036dc3098730004ff7558730014fe7558730014fc7558730004ff745873000cfe745873000cfc745873001cfc7358730004ff7258730004fc7258730036f77158730036f73158730036f43158730004ff7694730034fe7694730004fd76947300167e65947300067d6594730035de7394730005dd7394730004ff7654730004fd7654730034fc7654730004ff7690730034fe7690730004fd769073000ebe6490730006bd6490730035de7390730005dd7390730004ff7650730004fd7650730034fc7650730035df764c730006df764c7300075f754c7300075c754c7300079f744c7300079c744c730005df724c730006de624c730037d7714c730006de614c73001dde704c73001ddc704c730004ff7688730034fe7688730004fd76887300a57e75887300057d758873009dbe7488730005bd7488730035de7388730005dd7388730006ee6288730006ed6288730004ff7648730004fd7648730034fc7648730035de7348730005dd7348730005fb704873001df87048730004ff7608730034fe7608730004fd7608730035de7308730005dd7308730006f66108730006f56108730007e5210873000cff7650330034fc765033000ebe6450330006bd6450330005df7350330035dc7350330004ff7559230014fe7559230014fc755923001ebf7459230006bf545923008ebe545923008ebc545923008ebf4359230004ff7259230004fc725923008ebf4259230
  | 19 => 0x8940276bf4218940276ee4218940276ed4218940004fe7118940004fd7118940276bf411894026ebe401894026ebc4018940004fe7694940004fd7694940004fc76949400067f65949400167c659494000dbe7494940005bd74949400073d5494940004ff7654940004fe7654940004fc765494000dbe745494001cbc7650940005bf7550940005bd7550940265bc735094000dbf725094000faf7250940007af6250940006bc6250940007ac6250940006ac6250940005bf7150940007bb705094001dbe705094001dbc7050940007b8705094000ebf605094000fbb6050940004fe76cc940004fd76cc940034fc76cc940265bf74cc94000dbc74cc940006ef62cc940006ec62cc940004fe768c940004fd768c940004fc768c94000dbe748c940005bd748c940006df638c940036dc638c940004ff764c940004fe764c940004fc764c9400057f754c9400ad7c754c940005bf744c94000dbc744c940004fe760c940004fd760c940034fc760c94000dbe740c940005bd740c940006df630c940036dc630c940006ef620c940006ec620c940014fe75d8540004fd75d8540014fc75d854001cfd74d8540034fe73d8540004fd73d8540004fe72d8540004fd72d8540006f751d8540006f451d854004ef641d854004ef541d8540006f7619854003df970985400057f75585400ad7c7558540005df7358540005dc7358540005ef7258540005ec725854005dfb7058540006f56118540014fe7518540004fd7518540014fc751854001cfd7418540026be5418540006bd5418540034fe7318540004fd7318540006be4318540026bc4318540004fe7218540004fd7218540026bf4218540006bd4218540006f75118540006f45118540026bf4118540026f64118540026f54118540226be4018540226bc4018540004fe7694540004fd7694540004fc76945400067f65945400167c659454000dbe7494540005bd74945400073d5494540004ff7654540004fe7654540004fc765454000dbe745454001cbc7650540005bf7550540005bd7550540265bc7350540005bf7250540006bc625054000dbf715054000fb77150540007b76150540006bc6150540007b46150540006b46150540007bb705054001dbe705054001dbc7050540007b8705054000ebf605054000fbb6050540004fe76cc540004fd76cc540034fc76cc540265bf74cc54000dbc74cc540006f761cc540006f461cc540004fe768c540004fd768c540004fc768c54000dbe748c540005bd748c540006df638c540036dc638c540004ff764c540004fe764c540004fc764c5400057f754c5400ad7c754c540005bf744c54000dbc744c540004fe760c540004fd760c540034fc760c54000dbe740c540005bd740c540006df630c540036dc630c540006f7610c540006f4610c540004f
  | 20 => 0x6ee6248640006ed6248640006f66148640006f56148640004ff760864001cfe7608640004fd7608640005bf740864000dbc7408640007e52108640014fe76d95400ae7e65d954001cff74d954000cfe74d954001cfd74d954000cfc74d954028e7f54d954028e7d54d9540034fe73d9540004fd73d95400ae7c53d9540004fe72d9540004fd72d95400ae7c52d9540004fe71d9540004fd71d95400ae7c51d954000cfd70d95400ae7f50d95400ae7c6559540005df7359540005dc7359540005ef7259540005ec7259540005f77159540005f47159540285fb7059540204ff7459540006bf7459540004ff7359540006df7359540004df7359540034fc7359540006dc7359540034dc7359540004ff7159540006f77159540004f77159540004fc7159540006f47159540004f47159540284ff7059540006fb705954001dbc7655140016bc765514001cbc765514000dbf755514000f3f75551400073f6555140016be6555140016bc65551400af3c65551400163c65551400079f7355140265bc73551400079c73551400059c73551400af3f5355140005bf72551400af3c5255140005bf71551400af3c5155140007bb705514001dbe705514001dbc7055140007b8705514000ebf605514000fbb60551400af3f5055140014fe75d8d40004fd75d8d40014fc75d8d4001cfd74d8d4008ebe54d8d40006bd54d8d40006df53d8d40006dc53d8d4008ede43d8d4008edd43d8d40266bc43d8d40004fe72d8d40004fd72d8d40004fe71d8d40004fd71d8d40006df6398d4007df97098d400057f7558d400ad7c7558d40005ef7258d40005ec7258d40005f77158d40005f47158d4009dfb7058d40036de6318d40006dd6318d40004fe7694d40004fd7694d40034fc7694d400067f6594d400167c6594d4000dbc7494d401e73e5494d400af5f5394d40004ff7654d40004fe7654d40004fc7654d40005bf7454d4000dbc7454d400073d5454d4001cbe7690d40265bf7590d40005bd7590d40156be6590d40156bc6590d4000dbe7390d4000f9e7390d40266bf6390d400079f6390d402679c6390d40005bd7290d40005bd7190d4001dbe7090d40267ba7090d40267b97090d4001dbc7090d4000ebf6090d4000fbb6090d40014fe75d8940004fd75d8940014fc75d894001cfd74d8940034fe73d8940004fd73d8940006ef52d8940006ec52d894027eee42d894027eed42d8940004fe71d8940004fd71d8940006ef62989401edf970989400057f75589400ad7c7558940005df7358940005dc7358940005f77158940005f471589401f5fb7058940006ed6218940014fe7518940004fd7518940014fc751894001cfd7418940276be5418940006bd5418940034fe7318940004fd7318940006be4318940276bc4318940006ef5218940006ec521
  | 21 => 0xf7358a40034fc7358a4001eef7258a401eeee4258a401eeed4258a401eebc4258a40004ff7158a40004fc7158a401eebc4158a4001cfc7058a4001ebf4058a4001ebd4058a4001eee2058a4001eec2058a40004ff7694a4001cfe7694a40004fd7694a400167c6594a40004ff7654a40004fd7654a4001cfc7654a400167e6554a400067d6554a40005bf7454a4000dbc7454a40006bd6590a4029ebe6390a4000dbe7290a4000fae7290a40257ae6290a40006bd6290a40257ad6290a40005be7190a40257ba7090a40255bd7090a40007b97090a4000ebe6090a4000fba6090a40034ff76cca4001cfe76cca40004fd76cca4000dbe74cca40005bd74cca40036de63cca40006dd63cca40004ff768ca4001cfe768ca40004fd768ca40004ff764ca40004fd764ca4001cfc764ca400057f754ca400b57c754ca40005bf744ca4000dbc744ca40036de634ca40006dd634ca40034ff760ca4001cfe760ca40004fd760ca40014fe7598640004fd7598640014fc7598640034fe7398640004fd7398640004fe7298640004fd729864001ef6719864005ef6419864005ef5419864001cfe709864001ef6109864001ef41098640004ff75586400067f75586400047f7558640014fe7558640014fc75586400067c75586400147c7558640004ff7358640034fc7358640004ff7258640004fc7258640006be425864003ebc425864001ef7715864003ef6415864003ef5415864003ebc415864001cfc705864001ebf405864001ebd405864001ef6105864001ef41058640004ff769464001cfe7694640004fd769464023e7f65946400167c6594640004ff7654640004fd765464001cfc76546400167e65546400067d6554640005bf745464000dbc745464022ebf6590640006bd6590640296be6390640005be7290640006bd629064000dbe719064000fb6719064022fb66190640006bd619064022fb5619064022fba709064022dbd7090640007b9709064000ebe609064000fba6090640034ff76cc64001cfe76cc640004fd76cc64000dbe74cc640005bd74cc640036de63cc640006dd63cc640004ff768c64001cfe768c640004fd768c640004ff764c640004fd764c64001cfc764c6400057f754c6400b57c754c640005bf744c64000dbc744c640036de634c640006dd634c640034ff760c64001cfe760c640004fd760c640004ff76c864001cfe76c8640004fd76c86400b57e75c86400057d75c864000dbe74c8640005bd74c8640005de73c8640005dd73c8640006ee62c8640006ed62c8640004ff768864001cfe7688640004fd76886400b57e75886400057d758864000dbe7488640005bd7488640005de7388640005dd7388640006f66188640006f56188640004ff7648640004fd764864001cfc7648640005bf744864000dbc7448640
  | 22 => 0xc421006dd630c421005ee720c421005ed720c4210c57e75884210057d75884210bdbe7488421005bd7488421005de7388421005dd7388421007767588421007757588421007b67488421007b57488421007d67388421007d57388421005f57288421005e57288421006f66288421007e6628842115df67088421004ff7648421005f77648421006f77648421004f77648421005f77248421006f66248421007e662484212afe75248421007e65248421007e552484212afe452484212a7e74248421007e64248421007e542484212a7e44248421007e73248421007e63248421007e53248421007e4324842115df47048421007e77648421005e77648421006e77648421007e774484212a7e67448421007e574484212a7e47448421007e764484212a7e66448421007e564484212a7e464484212a7e65448421007e554484212a7e45448421007e77348421007e67348421007e57348421007e47348421007e76348421007e66348421007e56348421007e463484212a7e74348421007e64348421007e543484212a7e44348421007e77048421007e67048421007e57048421007e4704842115de470484212a7e740484212a7e44048421007e521d8021007e52198021006fb6098021005bf74580210bdbc7458021005df7358021005dc7358021007e52158021004ff7458021006bf7458021004bf745802100cfe745802100cfc7458021006bc745802100cbc7458021004ff7358021006df7358021004df7358021034fc7358021006dc7358021034dc7358021006f62158021006f52158021006e521580210bdbe7418021005bd7418021005de7318021005dd7318021007e5211802101efa6018021006f9601802101e7f75596402067f54596402067d5459640004ff7359640034fc73596400b67c5359640004ff7259640004fc72596400b67f5259640206bc4259640004ff7159640004fc71596400b67f5159640206bc415964001cfe705964001cfc705964001e7e505964001e7c505964001ebf405964001ebd4059640004ff7558e40014fe7558e40014fc7558e4001edf7358e40006df5358e40006dc5358e4007ede4358e4007edd4358e40004ff7258e40004fc7258e40004ff7158e40004fc7158e4001cfc7058e4001ede3058e4001edc3058e40034ff7694e4001cfe7694e40004fd7694e400167e6594e400067d6594e400b75f5394e40004ff7654e40004fd7654e4001cfc7654e40005bf7454e4000dbc7454e40014fe7598a40004fd7598a40014fc7598a40034fe7398a40004fd7398a4001eee7298a401f6ee4298a401f6ed4298a40004fe7198a40004fd7198a4001cfe7098a4001eee2098a4001eec2098a40004ff7558a400067f7558a400047f7558a40014fe7558a40014fc7558a400067c7558a400147c7558a40004f
  | 23 => 0xd57e75885210057d75885210cdbe7488521005bd7488521005de7388521005dd73885210076e75885210076d7588521007ae7488521007ad7488521007ce7388521007cd7388521007e76188521005ed708852100cfe74d8121004fd74d812100cfc74d8121034fe73d8121004fd73d8121006fb6098121005bf74581210cdbc7458121005df7358121005dc73581210cdbe7418121005bd7418121005de7318121005dd7318121166f7611812101efa6018121006f960181210bebe64d9021014fe75d9021004fd75d9021014fc75d90210bcfd74d90210bebe54d9021034fe73d9021004fd73d90210bebc43d902116cfe72d9021006ee72d90210bebf42d90210dcfe71d9021006f671d90210bebf41d902101cfe70d9021004fd70d90210bebc40d902100cff76590210bebc6459021004ff7559021014fe7559021014fc7559021006bf7459021004ff7359021034fc73590210bcfc72590210bebc42590210bcfc71590210bebc4159021004ff705902101cfc70590210bebf4059021004ff7655021004fe7655021004fd7655021004fc7655021006bf645502100ebc64550210bf3c5455021005df7355021005dc735502100cfe74d8c21004fd74d8c2100cfc74d8c21004fe71d8c21006f671d8c2101cfe70d8c21004fd70d8c21004fd7698c21006df6398c21034ff7658c21005bf7458c210bdbc7458c21004ff7458c21006bf7458c21004bf7458c2100cfe7458c2100cfc7458c21006bc7458c2100cbc7458c21006df7358c21004ff7058c2101cfc7058c21036de6318c21006dd6318c21034ff7690c21004fe7690c21004fd7690c21034fc7690c21006bf6490c2100ebc6490c21004ff7650c21004fe7650c21004fd7650c21004fc7650c210057f7550c210c57c7550c210bf9c4350c21014fe75984210e67e75984210147e75984210e4fd75984210067d75984210047d7598421014fc759842100cfe74984210debe749842100cbe74984210dcfd7498421006bd7498421004bd749842100cfc7498421034fe7398421006de7398421034de7398421004fd7398421006dd7398421004dd73984210e4ff7694421014fd76944210167e65944210067d6594421005ee7294421005ed72944210e4ff76544210067f65544210167c65544210dcff769042100cfe769042100cfd76904210bcfc769042100ebe6490421006bd6490421005ee7290421005ed72904210dcff7650421006bf645042100ebc6450421004fd76cc421006df63cc421036dc63cc421004ff768c421034fd768c421036de638c421006dd638c421005ee728c421005ed728c421004ff764c4210057f754c4210c57c754c421005bf744c4210bdbc744c421006df634c421036dc634c421034ff760c421004fe760c421004fd760c421034fc760c421036de630
  | 24 => 0xd63d82210067e65982210067d6598221006be6498221006bd6498221006de6398221006dd6398221006fb60982210067e65582210067d6558221006be6458221006bd6458221006de6358221006dd6358221004ff7558221014fe7558221014fc7558221004ff745822100cfe745822100cfc7458221004ff7358221034fc7358221006ef21582210e57e75182210057d75182210067e65182210067d65182210ddbe7418221005bd7418221006be6418221006bd6418221005de7318221005dd7318221006de6318221006dd631822101efa6018221006f9601822100cfe76d91210cebe64d9121014fe75d9121004fd75d9121014fc75d91210cebe54d9121034fe73d9121004fd73d91210cebc43d91210ccfd72d91210cebf42d91210ccfd71d91210cebf41d912101cfe70d9121004fd70d91210cebc40d91210cebc6459121004ff7559121014fe7559121014fc75591210ccff7459121006bf7459121004ff7359121034fc73591210dcff7259121006ef72591210cebc425912116cff7159121006f771591210cebc4159121004ff705912101cfc70591210cebf4059121004ff7655121004fe7655121004fd7655121004fc7655121006bf645512100ebc64551210cf3c5455121005df7355121005dc7355121005f77155121005f47155121034fe76d8d2100cfe74d8d21004fd74d8d2100cfc74d8d2101cfe70d8d21004fd70d8d21006df6398d21005bf7458d210cdbc7458d21005fb7058d21005f87058d21004ff7458d21006bf7458d21004bf7458d2100cfe7458d2100cfc7458d21006bc7458d2100cbc7458d21006df7358d21004ff7158d21006f77158d21004ff7058d21006fb7058d21004fb7058d2101cfc7058d21006f87058d2101cf87058d21004fe7618d21036de6318d21006dd6318d21034ff7690d21004fe7690d21004fd7690d21034fc7690d21006bf6490d2100ebc6490d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210d57c7550d210cf9c4350d21005ef7250d21005ec7250d21005f77150d21005f47150d21174fe76945210167e65945210067d65945210d7775194521014fc76545210067f65545210167c6554521005ef7254521005ec725452116cfe769052100ebe6490521006bd649052100cff76505210ccfd765052100cfc7650521006bf645052100ebc6450521005ef7250521005ec72505210cfb44150521004fe76cc521006df63cc521036dc63cc521005ee72cc521005ed72cc521004fe768c521036de638c521006dd638c521034ff764c521004fd764c521034fc764c5210057f754c5210d57c754c521005bf744c5210cdbc744c521006df634c521036dc634c521005ef724c521005ec724c521004fe760c521036de630c521006dd630c521007d5310c521
  | 25 => 0xe21005f47150e210d4fd7694a210167e6594a210067d6594a211d6be6494a21006bd6494a21006de6394a21006dd6394a21014ff7654a210167e6554a210067d6554a211cebe6454a21006bd6454a21006de6354a21006dd6354a21005f77154a21005f47154a210ccfd7690a211c67e6590a210067d6590a2100ebe6490a21006bd6490a21006de6390a21006dd6390a2100cff7650a211be7e6550a210067d6550a2100ebe6450a21006bd6450a21006de6350a21006dd6350a21005f77150a21005f47150a211b67e65cca210067d65cca211aebe64cca21006bd64cca21036de63cca21006dd63cca21005f671cca21005f571cca211a67e658ca210067d658ca2119ebe648ca21006bd648ca21036de638ca21006dd638ca21034ff764ca210057f754ca210e57c754ca211967e654ca210067d654ca21005bf744ca210ddbc744ca2118ebe644ca21006bd644ca21036de634ca21006dd634ca21005f7714ca21005f4714ca211867e650ca210067d650ca2117ebe640ca21006bd640ca21036de630ca21006dd630ca21014fd76946210167e65946210067d6594621146be6494621006bd6494621006de6394621006dd6394621005ee7294621005ed72946210e7775194621007e721946210c4ff76546210167e65546210067d655462113ebe6454621006bd6454621006de6354621006dd6354621007e7215462100cfd76906211367e65906210067d659062100ebe6490621006bd6490621006de6390621006dd6390621005ee7290621005ed72906210bcff765062112e7e65506210067d655062100ebe6450621006bd6450621006de6350621006dd63506210dfb441506211267e65cc6210067d65cc62111ebe64cc621006bd64cc621036de63cc621006dd63cc621034fd768c6211167e658c6210067d658c62110ebe648c621006bd648c621036de638c621006dd638c621005ee728c621005ed728c6210057f754c6210e57c754c6211067e654c6210067d654c621005bf744c6210ddbc744c6210febe644c621006bd644c621036de634c621006dd634c6210f67e650c6210067d650c6210eebe640c621006bd640c621036de630c621006dd630c621005ee720c621005ed720c621007d5310c6210ddbe74c8621005bd74c862116ebe64c8621006bd64c8621006de63c8621006dd63c8621005f576c8621006f576c86210077675c86210077575c86210077665c86210077565c8621007b674c8621007b574c8621007b664c8621007b564c8621007d673c8621007d573c8621007d663c8621007d563c8621007e652c8621007e552c8621166f660c86210e57e75d82210057d75d82210067e65d82210067d65d82210ddbe74d8221005bd74d8221006be64d8221006bd64d8221005de73d8221005dd73d8221006de63d8221006d
  | 26 => 0x75e6598e210065e6598e21006dd6598e210075d6598e210065d6598e21006dc6598e21006df6498e21006de6498e210079e6498e210069e6498e21006dd6498e210079d6498e210069d6498e21006dc6498e21036df7598e21036de7598e21036dd7598e21036dc7598e21036df7498e21036de7498e21036dd7498e21036dc7498e21006df5498e21006de5498e21006dd5498e21006dc5498e21036df7298e21036dd7298e21006df5298e21006dc5298e21006df4298e21006dc4298e21036de7198e21036dc7198e21006df5198e21006dc5198e21006df4198e21006dc4198e21036df7098e21036de7098e21036dd7098e21036dc7098e21006df5098e21006dc5098e21006df4098e21006dc4098e210067e6558e210067d6558e21006be6458e21006bd6458e21004ff7558e21014fe7558e21014fc7558e21004ff7458e2100cfe7458e2100cfc7458e21006df7358e21006df5358e21006dc5358e21006df4358e21006dc4358e21004ff7058e2101cfc7058e21006df7658e21006df6558e21006de6558e210075e6558e210065e6558e21006dd6558e210075d6558e210065d6558e21006dc6558e21006df6458e21006de6458e210079e6458e210069e6458e21006dd6458e210079d6458e210069d6458e21006dc6458e21006df7558e21006de7558e21006dd7558e21006dc7558e21006df7458e21006de7458e21006dd7458e21006dc7458e21006df5458e21006de5458e21006dd5458e21006dc5458e21006df7258e21006dd7258e21006df5258e21006dc5258e21006df4258e21006dc4258e21006de7158e21006dc7158e21006df5158e21006dc5158e21006df4158e21006dc4158e21006df7058e21006de7058e21006dd7058e21006dc7058e21006df5058e21006dc5058e21006df4058e21006dc4058e210e57e7518e210057d7518e210067e6518e210067d6518e210ddbe7418e21005bd7418e21006be6418e21006bd6418e21036de6318e21006dd6318e21034ff7694e21004fe7694e21004fd7694e21034fc7694e210167e6594e210067d6594e211e6be6494e21006bd6494e21036de6394e21006dd6394e210e75f5394e21004ff7654e21004fe7654e21004fd7654e21004fc7654e210167e6554e210067d6554e21005bf7454e210ddbc7454e211debe6454e21006bd6454e21036de6354e21006dd6354e21005f77154e21005f47154e21034ff7690e21004fe7690e21004fd7690e21034fc7690e211567e6590e210067d6590e2100ebe6490e21006bd6490e21036de6390e21006dd6390e21004ff7650e21004fe7650e21004fd7650e21004fc7650e210057f7550e210e57c7550e2114e7e6550e210067d6550e2100ebe6450e21006bd6450e21036de6350e21006dd6350e210df9c4350e21005f7715
  | 27 => 0xc73596210e67f53596210e67c53596210e67f52596210e67c5159621004ff705962101cfc70596210e67f50596210e67c50596210e67f76596210067e64596210067c64596210067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067c43596210067f72596210067d72596210e67c72596210067f42596210067c42596210e67f71596210067e71596210067c71596210067f41596210067c41596210067f70596210067e70596210067d70596210067c70596210067f40596210067c40596210e57e75d92210057d75d92210067e65d92210067d65d92210debe64d9221005de73d9221005dd73d9221014fe75d92210067e75d92210147e75d9221004fd75d92210067d75d92210047d75d9221014fc75d9221034fe73d9221006de73d9221034de73d9221004fd73d9221006dd73d9221004dd73d9221006ed72d9221006f671d922101cfe70d9221004fd70d9221006bf6599221006be65992210073e65992210063e6599221006bd65992210073d65992210063d6599221006bc65992210067e65592210067d65592210debc6459221004ff7559221014fe7559221014fc7559221006bf7459221006bf54592210debe54592210debc5459221004ff7359221034fc73592210debf43592210debc43592210debf42592210debc4159221004ff705922101cfc70592210debf40592210debc40592210debf7659221006bf6559221006be65592210073e65592210063e6559221006bd65592210073d65592210063d6559221006bc6559221006bf7559221006be7559221006bd7559221006bc7559221006bf7359221006be7359221006bd7359221006bc7359221006bf5359221006bc5359221006bf7259221006bd72592210debc7259221006bf5259221006bc52592210debf7159221006be7159221006bc7159221006bf5159221006bc5159221006bf7059221006be7059221006bd7059221006bc7059221006bf5059221006bc5059221004ff7655221004fe7655221004fd7655221004fc76552210167e65552210067d655522100ebe6455221006bd64552210df3c5455221005df7355221005dc7355221005f77155221005f471552210e57e75d8e210057d75d8e210067e65d8e210067d65d8e210ddbe74d8e21005bd74d8e21006be64d8e21006bd64d8e21014fe75d8e210067e75d8e210147e75d8e21004fd75d8e210067d75d8e210047d75d8e21014fc75d8e2100cfe74d8e21006be74d8e2100cbe74d8e21004fd74d8e21006bd74d8e21004bd74d8e2100cfc74d8e21006ed72d8e21006f671d8e2101cfe70d8e21004fd70d8e210067e6598e210067d6598e21006be6498e21006bd6498e21006df6398e21006df6598e21006de6598e21
  | 28 => 0x90310eebf4059031004ff7655031034fe7655031004fd7655031034fc76550310167e65550310067d655503100ebe6455031006bd64550310ef3c5455031005df7355031035dc7355031014fe7598831004fd7598831014fc759883100cfe7498831004fd749883100cfc7498831036ee7298831036df3298831036ef3298831036ec3298831036df319883101cfe7098831004fd7098831036dc3098831004ff7558831014fe7558831014fc7558831004ff745883100cfe745883100cfc7458831036ef7258831036ef3258831036ec3258831004ff705883101cfc7058831004ff7694831034fe7694831004fd76948310167e65948310067d6594831035de7394831005dd7394831005f67194831005f57194831004ff7654831004fd7654831034fc7654831004ff7690831034fe7690831004fd769083100ebe6490831006bd6490831035de7390831005dd7390831005f67190831005f57190831004ff7650831004fd7650831034fc7650831035df764c831006df764c831004df764c8310075f754c8310075c754c8310079f744c8310079c744c831035df724c831037cf724c831006de624c831005df714c831037d6614c831215dc704c831014fe7598431114fd7598431014fc759843100cfe749843110cfd749843100cfc7498431036df3298431006dd3298431036df3198431036f73198431036f43198431114ff7694431034fe7694431014fd7694431034fc76944310167e65944310067d6594431035de7394431005dd7394431114ff765443110cff7690431034fe769043100cfd7690431034fc769043100ebe6490431006bd6490431035de7390431005dd739043110cff7650431035df764c431006df764c431004df764c4310075f754c4310075c754c4310079f744c4310079c744c431005df724c431006de624c431035df714c431037d7714c431006de614c431037d6614c431007d6514c431007d5514c431007d6414c431007d5414c431215dc704c431004ff7558031014fe7558031014fc7558031004ff745803100cfe745803100cfc7458031004ff7258031004fc7258031036df3258031006dd3258031036df3158031006dd3158031036fb7058031036fb3058031036dc3058031036f830580310e67e65d96210ddbe74d9621005bd74d9621005de73d9621005dd73d962100cfe74d9621006be74d962100cbe74d9621004fd74d9621006bd74d9621004bd74d962100cfc74d9621034fe73d9621006de73d9621034de73d9621004fd73d9621006dd73d9621004dd73d9621006ed72d9621006f671d962101cfe70d9621004fd70d96210067e64996210067c64996210e67c65596210067f7559621004ff745962100cfe745962100cfc74596210e67f54596210067e54596210e67c5459621004ff7359621034f
  | 29 => 0x1d6bc6494931004ff7654931004fe7654931004fc76549310067f65549310167c6554931006bf64549311cebc6454931005df7354931035dc7354931004fe7690931004fd7690931004fc76909310067f65909311c67c6590931006bf649093100ebc6490931004ff7650931004fe7650931004fc76509310067f65509311be7c6550931006bf645093100ebc6450931005df7350931035dc73509310067f658c9311a67c658c931006bf648c93119ebc648c931006ef628c931006ec628c931005f6718c931005f5718c9310075f658c9310075c658c9310079f648c9310079c648c931035de728c931006df628c931007cf628c931007cc628c931005de718c931007d6718c931005d6718c931007d5718c931037d7618c931005dd708c93124edc608c931005bf744c9310fdbc744c931006bf644c93118ebc644c931005f7714c931005f4714c931037d4314c931124fe76945310067f65945310167c6594531006bf6494531146bc6494531107775194531014ff7654531104fd7654531034fc76545310067f65545310167c6554531006bf645453113ebc6454531005df7354531035dc735453111cfe76905310067f65905311367c6590531006bf649053100ebc649053100cff76505310fcfd7650531034fc76505310067f655053112e7c6550531006bf645053100ebc6450531005df7350531035dc73505310ffb441505310067f658c5311167c658c531006bf648c53110ebc648c531035f6718c5310075f658c5310075c658c5310079f648c5310079c648c531005de728c531006df628c531035de718c531037d7618c531005dd708c5310067f65d81310067c65d8131006bf64d8131006bc64d8131014fe75d8131004fd75d8131014fc75d813100cfe74d8131004fd74d813100cfc74d8131004fe72d8131004fd72d81311057e75981310057d75981310067f65981310067c65981310fdbe7498131005bd7498131006bf6498131006bc6498131006fb60981310057f75581311057c75581310067f65581310067c6558131005bf74581310fdbc7458131006bf6458131006bc6458131005ef7258131005ec72581310067f65181310067c6518131006bf6418131006bc641813121edf631813101efa6018131006f960181310367f7559431004ff745943100cfe745943100cfc74594310f67f5459431034fe7359431034fc73594310367e53594310367c5359431004ff7259431004fc72594310f67c52594310f4fc71594310f67c5159431004ff705943101cfc70594310f67f5059431004ff7559031014fe7559031014fc7559031036bf74590310eebe5459031034fe7359031034fc7359031036be4359031036bc4359031004ff7259031004fc72590310eebc42590310ecfc71590310eebc4159031004ff705903101cfc705
  | 30 => 0xd71d91310febf41d913101cfe70d9131004fd70d91310febf40d91310febc40d91310fdbe76d913100cbe76d9131006bf65d91310073f65d91310063f65d9131006be65d9131006bd65d9131006bc65d91310073c65d91310063c65d9131297b731d9131297b431d9131006bf75d9131006be75d9131006bd75d9131006bc75d9131006bf73d9131296be73d9131006bd73d9131296bc73d9131006bf53d9131296be53d9131296bc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006bc52d9131296bf32d9131296bc32d9131296bf71d91310febe71d9131006bd71d9131006bf51d9131006bc51d9131296bf31d9131296bc31d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006bc50d9131296bf30d9131296bc30d91310057f75591311057c75591310067f65591310067c65591310febc6459131004ff75591310067f75591310047f7559131014fe7559131014fc75591310067c75591310147c75591310fcff7459131006bf745913110cff7359131006df7359131004ff7259131004fc725913111cff7159131006f77159131004ff705913101cfc7059131005be76191310febe7619131004be7619131006bf65191310073f65191310063f6519131006be6519131006bd6519131006bc65191310073c65191310063c65191312b6bf61191312b7b731191312b7b43119131004ff7655131004fe7655131004fd7655131004fc76551310067f65551310167c6555131006bf645513100ebc64551310ff3c5455131005df7355131035dc7355131014fc7654d310067f6554d310167c6554d31005bf7454d310fdbc7454d31006bf6454d311debc6454d310375c5354d31005f77154d31005f47154d31037d43154d3100cfc7650d310057f7550d311057c7550d310067f6550d3114e7c6550d31006bf6450d3100ebc6450d310379c4350d31005f77150d31005f47150d31037d43150d310067f65d89310067c65d8931006bf64d8931006bc64d8931014fe75d8931004fd75d8931014fc75d893100cfe74d8931004fd74d893100cfc74d893101cfe70d8931004fd70d89311057e75989310057d75989310067f65989310067c65989310fdbe7498931005bd7498931006bf6498931006bc6498931006ef62989310057f75589311057c75589310067f65589310067c6558931005bf74589310fdbc7458931006bf6458931006bc6458931005fb7058931005f870589310067f65189310067c6518931006bf6418931006bc6418931006ed6218931014fe7518931004fd7518931014fc751893100cfe7418931004fd741893100cfc741893101cfe7018931004fd7018931004fe7694931004fd7694931004fc76949310067f65949310167c6594931006bf6494931
  | 31 => 0x4a310167e6594a310067d6594a31035de7394a31005dd7394a31004ff7654a31004fd7654a31004fc7654a31004ff7690a31004fe7690a31004fd7690a3100ebe6490a31006bd6490a31035de7390a31005dd7390a31004ff7650a31004fd7650a31004fc7650a31005dd76cca31036dd76cca31006de62cca31005dd71cca31037d661cca3121dde70cca31005f6718ca31005f5718ca31034fd76946310167e65946310067d6594631035de7394631005dd73946311177751946310f4ff7654631034fd769063100ebe6490631006bd6490631035de7390631005dd73906310ecff765063110fb44150631005dd76cc631036dd76cc631005dd72cc631006de62cc631037d661cc631007d651cc631007d551cc63121dde70cc631006fb6098231004ff7558231014fe7558231014fc7558231004ff745823100cfe745823100cfc7458231004ff7258231004fc7258231006df3258231006df31582311157e75182310057d751823110dbe7418231005bd7418231005ee7218231005ed721823101efa6018231006f96018231014fe76d95311067e65d953100cfe74d9531004fd74d953100cfc74d95311067f54d95310067e54d95311067c54d9531104fd73d95311067f53d9531004fe72d9531004fd72d95311067f52d95311067c52d9531034fd71d95311067f51d953101cfe70d9531004fd70d95311067f50d95311067c50d95311057e76d95310147e76d95310067e64d95310067c64d95312c77731d95312c77431d95310067f74d95310067e74d95310067d74d95310067c74d95310067f73d95312c67e73d95310067d73d95312c67c73d95310067f43d95312c67e43d95312c67c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067c42d95312c67f32d95312c67c32d95312c67f71d95311067e71d95310067d71d95310067f41d95310067c41d95312c67f31d95312c67c31d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067c40d95312c67f30d95312c67c30d95311067c6559531005bf74595310fdbc7459531104ff75595310067f7559531004ff7459531006bf7459531004bf745953100cfe745953100cfc7459531006bc745953100cbc7459531114ff7359531006df7359531004ff7259531004fc7259531124ff7159531006f77159531004ff705953101cfc70595310057e76195311067e76195310047e76195310067e64195310067c64195312be7f61195312bf7731195312bf74311953100cfe76d91310067f65d91310067c65d91310febe64d9131014fe75d9131004fd75d9131014fc75d9131006bf54d91310febe54d91310febc54d91310fcfd73d91310febf43d9131004fe72d9131004fd72d91310febf42d91310febc42d9131034f
  | 32 => 0x2c67f65947310167c6594731014ff7654731034fc76547310167e65547310067d6554731005df7354731035dc73547310fcfd7690731296bf649073100ebc649073100cff7650731034fc765073100ebe6450731006bd6450731005df7350731035dc7350731004ff7558331014fe7558331014fc7558331004ff745833100cfe745833100cfc7458331004ff7258331004fc7258331036fb7058331036fb3058331036f830583311167e65d963110dbe74d9631005bd74d9631005ee72d9631005ed72d963100cfe74d9631006be74d963100cbe74d9631004fd74d9631006bd74d9631004bd74d963100cfc74d96311167f54d9631006dd73d96312c67e53d96312c67c53d9631004fe72d9631006ee72d9631004ee72d9631004fd72d9631006ed72d9631004ed72d9631006f671d963101cfe70d9631004fd70d96311167c65596310067f7559631004ff745963100cfe745963100cfc74596310067e54596311167c54596311167f5359631004ff7259631004fc72596311167c5259631034fc71596311167c5159631004ff705963101cfc70596311167f50596311157e75d92310057d75d923110ebe64d9231005ee72d9231005ed72d9231014fe75d92310067e75d92310147e75d9231004fd75d92310067d75d92310047d75d9231014fc75d923110ebe54d9231006dd73d9231296be43d9231296bc43d9231004fe72d9231006ee72d9231004ee72d9231004fd72d9231006ed72d9231004ed72d9231006f671d923101cfe70d9231004fd70d923110ebc6459231004ff7559231014fe7559231014fc7559231006bf7459231006bf545923110ebc545923110ebf4359231004ff7259231004fc725923110ebc4259231034fc715923110ebc4159231004ff705923101cfc705923110ebf4059231004ff7655231004fe7655231004fd7655231004fc76552310067f65552310167c6555231006bf645523100ebc645523110f3c5455231005df7355231035dc7355231036f73158e31014ff7654e310167e6554e310067d6554e31005bf7454e3110dbc7454e31005f77154e31005f47154e31037d73154e3100cff7650e310057f7550e311157c7550e3100ebe6450e31006bd6450e310379c4350e31005f77150e31005f47150e311157e75d8a310057d75d8a3110dbe74d8a31005bd74d8a31006ef6298a31014fe7598a31004fd7598a31014fc7598a3100cfe7498a31004fd7498a3100cfc7498a31006ef5298a31006ec5298a31006ef4298a31006ec4298a3101cfe7098a31004fd7098a31004ff7558a31014fe7558a31014fc7558a31004ff7458a3100cfe7458a3100cfc7458a31006ef5258a31006ec5258a31006ef4258a31006ec4258a31004ff7058a3101cfc7058a31006ed6218a31004ff7694a31004fe7694a31004fd769
  | 33 => 0xf745494100dbc7454941006bf6590941006bd659094129ebc639094100dbe729094100fae7290941006bf6290941007af6290941007ac6290941005be7190941007b67190941005b67190941007b5719094100ebf619094100fb76190941005bd7090941256bc60909412d4fe76945410167e65945410067d659454112f775194541014ff765454100cfe765454113cfd765454100cfc76545410067f65545410167c6554541005bf745454100dbc7454541006bf6590541006bd6590541296bc6390541005be7290541006bf629054100dbe719054100fb6719054100ebf619054100fb76190541005bd7090541014fe75d8141004fd75d8141014fc75d8141034fe73d8141004fd73d8141004fe72d8141004fd72d814105efa40d8141006fb60981410057f755814112d7c7558141005df7358141005dc7358141005ef7258141005ec725814112d7e75181410057d751814122ebf641814101efa6018141006f960181410367f7559731004ff745973100cfe745973100cfc74597311267f5459731034fc73597310367e53597310367c5359731004ff7259731004fc72597311267f52597311267f5159731004ff705973101cfc70597311267c5059731004ff7559331014fe7559331014fc7559331036bf745933111ebe5459331034fc7359331036be4359331036bc4359331004ff7259331004fc725933111ebf425933111ebf4159331004ff705933101cfc705933111ebc4059331004ff7655331034fe7655331004fd7655331034fc76553310167e65553310067d655533100ebe6455331006bd645533111f3c5455331005df7355331035dc7355331014fe7598b31004fd7598b31014fc7598b3100cfe7498b31004fd7498b3100cfc7498b31036ee7298b31036ef3298b31036ec3298b3101cfe7098b31004fd7098b31004ff7558b310067f7558b310047f7558b31014fe7558b31014fc7558b310067c7558b310147c7558b31004ff7458b31006bf7458b31004bf7458b3100cfe7458b3100cfc7458b31006bc7458b3100cbc7458b31036ef7258b31036ef3258b31036dc3258b31036ec3258b31036dc3158b31004ff7058b3101cfc7058b31036df3058b31004ff7694b31034fe7694b31004fd7694b312ce7f6594b310167c6594b31006ee6294b31006ed6294b31005f67194b31005f57194b31004ff7654b31004fd7654b31034fc7654b310167e6554b310067d6554b31005df7354b31035dc7354b31006ee6254b31006ed6254b31004ff7690b31034fe7690b31004fd7690b3129ebf6490b3100ebc6490b31006ee6290b31006ed6290b31005f67190b31005f57190b31004ff7650b31004fd7650b31034fc7650b3100ebe6450b31006bd6450b31005df7350b31035dc7350b31006ee6250b31006ed6250b31104fd7694731
  | 34 => 0x4a410073d5494a41005bf7550a41295bc7350a4100dbf7250a4100faf7250a41006be6250a41007ae6250a41006ae6250a41007ad6250a41005bf7150a41007b77150a41007b47150a4100ebe6150a4100fb66150a4122dbc7050a4100cff7694641014fe769464100cfd76946410167e65946410067d659464100dbe7494641005bd74946410073d5494641137775194641147b741946412dcff765464100dbe745464113fb74154641006fb6098241004ff7558241014fe7558241014fc755824103ebe5458241006bd5458241004ff7358241034fc7358241006be435824103ebc4358241004ff7258241004fc725824103ebf4258241006bd425824103ebf415824103efa405824122ebc40582411357e75182410057d7518241005de7318241005dd7318241005ee7218241005ed721824101efa6018241006f96018241014fe76d954112e7e65d9541144ff74d9541144fd74d95411467f54d95411467d54d9541034fe73d9541004fd73d954112e7c53d9541004fe72d9541004fd72d954112e7f52d9541146bc42d954100cfd71d954112e7f51d9541146bc41d954101cfe70d9541004fd70d954112e7c50d9541146bf40d954112e7c6559541005df7359541005dc73595412ddf77159541144ff75595410067f755954113cff7459541006bf7459541004ff7359541006df7359541004df7359541034fc7359541006dc7359541034dc7359541004ff7259541004fc725954112e7c525954113ebc42595412dcff7159541006f7715954112e7c515954113ebc4159541004ff705954101cfc705954112e7f505954113ebf4059541014fe75d8d41004fd75d8d41014fc75d8d41006df53d8d41006dc53d8d4110ede43d8d4110edd43d8d41004fe72d8d41004fd72d8d4101cfe70d8d41004fd70d8d41006df6398d410fdf57198d410057f7558d4112d7c7558d4111df77158d41036de6318d41006dd6318d41004fe7694d41004fd7694d41034fc7694d410067f6594d410167c6594d4112f5f5394d41004ff7654d41004fe7654d41004fc7654d41005bf7454d4100dbc7454d4112d7e75d89410057d75d8941014fe75d89410067e75d89410147e75d8941004fd75d89410067d75d89410047d75d8941014fc75d8941034fe73d8941004fd73d89410deee42d89410deed42d89410debc42d89410debc41d894101cfe70d8941004fd70d89410debf40d894112d7e75989410057d7598941005de7398941005dd7398941006ef62989410cdf5719894116df77158941006ed6218941014fe7518941004fd7518941014fc7518941034fe7318941004fd73189410beee42189410beed421894101cfe7018941004fd7018941004fe7694941004fd7694941004fc76949410167e65949410067d6594941004fe7654941004fc7654941005b
  | 35 => 0x6fb6098151005bf745815113dbc7458151005df7358151005dc7358151005ef7258151005ec725815123e7f651815113dbe7418151005bd741815101efa6018151006f960181511367e65d9641005de73d9641005dd73d9641005ee72d9641005ed72d96412d5f671d964113cfd75d9641006bd74d9641034fe73d9641006de73d9641034de73d9641004fd73d9641006dd73d9641004dd73d9641004fe72d9641006ee72d9641004ee72d9641004fd72d9641006ed72d9641004ed72d96412d4fe71d9641006f671d964101cfe70d9641004fd70d9641014ff76596411367c65596410067f755964113e7f545964113e7d5459641004ff7359641034fc73596411367c5359641004ff7259641004fc72596411367c525964100cfc71596411367c5159641004ff705964101cfc70596411367f5059641135bf7655241016bf7655241014bf765524100dbf755524100f3f7555241016be65552411373e65552410163e65552410073d6555241016bc65552410079f7355241295bc73552410079c73552410059c73552411373f5355241005bf72552411373c5255241005bf7155241007b77155241007b4715524100ebe615524100fb661552411373c515524122dbc70552411373f50552411357e75d8e410057d75d8e41005ee72d8e41005ed72d8e410edf671d8e41006df6398e41004ff7558e41014fe7558e41014fc7558e410febe5458e41006bd5458e41006df5358e41006dc5358e410fede4358e410fedd4358e41296bc4358e41004ff7258e41004fc7258e41004ff7058e4101cfc7058e41036de6318e41006dd6318e4110df67118e41034ff7694e41004fe7694e41004fd7694e410167e6594e410067d6594e4100dbc7494e411e73e5494e411375f5394e41004ff7654e41004fd7654e41004fc7654e41005bf7454e4100dbc7454e410073d5454e41295bf7590e41005bd7590e41156be6590e41156bc6590e4100dbe7390e4100f9e7390e412979e6390e41296bd6390e410079d6390e41005bd7290e41297b67190e41005bd7190e41297b57190e4100ebe6190e4100fb66190e4122dbe7090e411357e75d8a410057d75d8a41005de73d8a41005dd73d8a410bdf671d8a41006ef6298a41014fe7598a41004fd7598a41014fc7598a4116ebe5498a41006bd5498a41034fe7398a41004fd7398a41006be4398a4116ebc4398a41006ef5298a41006ec5298a4116ebf4298a4116eee4298a4116eed4298a4116ebf4198a4101cfe7098a41004fd7098a4116ebc4098a41004ff7558a41014fe7558a41014fc7558a41004ff7358a41034fc7358a41006ef5258a41006ec5258a410ceee4258a410ceed4258a41004ff7058a4101cfc7058a41006ed6218a410ddf67118a41004fe7694a41004fd7694a4100dbe7494a41005bd749
  | 36 => 0xd5450e511479c4350e51145be74d8a51005bd74d8a51005de73d8a51005dd73d8a51006ef6298a5100cfe7498a51004fd7498a5100cfc7498a511767f5498a510067d5498a51034fe7398a51004fd7398a510067e5398a511767c5398a511767f5298a51176ed5298a51006ef4298a51006ec4298a511767f5198a5101cfe7098a51004fd7098a511767c5098a51004ff7458a5100cfe7458a5100cfc7458a51004ff7358a51034fc7358a510d6ee5258a51006ef4258a51006ec4258a51004ff7058a5101cfc7058a51006ed6218a51004fe7690a51004fd7690a5100ebe6490a51006bd6490a510073d5490a51006fb6098251004ff745825100cfe745825100cfc74582510467f54582510067d5458251004ff7358251034fc73582510067e53582510467c5358251004ff7258251004fc72582510467f52582510467f5158251046fa505825123e7c5058251145be7418251005bd7418251005de7318251005dd7318251005ee7218251005ed721825101efa6018251006f9601825100cfe76d915113ebe64d915113ebe54d9151136bd54d9151034fe73d9151004fd73d915113ebc43d9151004fe72d9151004fd72d91511367c52d915113ebf42d9151014fd71d91511367c51d915113ebf41d915101cfe70d9151004fd70d91511367f50d915113ebc40d915113ebc6459151005df7359151005dc73591512e5f7715915100cfe74d8d51004fd74d8d5100cfc74d8d51116de53d8d51116dd53d8d51006df43d8d51006dc43d8d51004fe72d8d51004fd72d8d5101cfe70d8d51004fd70d8d51006df6398d51105f57198d51005bf7458d5113dbc7458d51125f77158d51036de6318d51006dd6318d51004fe7690d51004fd7690d51034fc7690d51006bf6490d5100ebc6490d51004ff7650d51004fe7650d51004fc7650d510057f7550d510157c7550d5113f9c4350d5113dbe74d8951005bd74d895100cfe74d8951006be74d895100cbe74d8951004fd74d8951006bd74d8951004bd74d895100cfc74d8951034fe73d8951004fd73d89510e6ee52d89510e67c52d89510e67c51d895101cfe70d8951004fd70d89510e67f50d895113dbe7498951005bd7498951005de7398951005dd7398951006ef6298951006ed621895100cfe7418951004fd741895100cfc7418951034fe7318951004fd73189510c6ed521895101cfe7018951004fd7018951004fe7690951004fd7690951004fc769095100ebe6490951004fe7650951004fc7650951006bf645095100ebc64509510067f64945512c67c63945510057e72945510067f62945510157e71945510177671945510167f61945510177761945510057d709455100cfe74d8151004fd74d815100cfc74d8151034fe73d8151004fd73d8151004fe72d8151004fd72d8151066fa50d8151
  | 37 => 0x8543004fe72d8543004fd72d854311ef641d854301cfe70d8543004fd70d854314d7e75985430057d75985430067f65985430067c659854310f9c4398543005ee7298543005ed7298543006f761985430057f755854314d7c75585430067f65585430067c65585430ff9c43585430067f65185430067c65185430ef9c4318543006f56118543014fe7518543004fd7518543014fc7518543034fd74185430eebe5418543006bd54185432b6be43185432b6bc4318543004fe7218543004fd72185430eef5411854301cfe7018543004fd70185430067f65d81430067c65d814309f9c43d8143014fe75d8143004fd75d8143014fc75d8143034fd74d814309ebe54d8143006bd54d81432f6be43d81432f6bc43d8143004fe72d8143004fd72d8143004fe71d8143004fd71d814309efa40d814314d7e75981430057d75981430067f65981430067c659814308f9c4398143006fb60981430057f755814314d7c75581430067f65581430067c655814307f9c4358143005ef7258143005ec7258143005f77158143005f471581430067f65181430067c651814306f9c431814301efa6018143006f96018143146be64d9251005de73d9251005dd73d9251005ee72d9251005ed72d92512edf671d925100cff7659251146bc6459251146be545925112ebd5459251004ff7359251034fc7359251146bc4359251004ff7259251004fc7259251146bc4259251014fc7159251146bc4159251004ff705925101cfc7059251146bf40592511457f765525100e7f765525100c7f76552510157f74552510173f745525100e7e64552511473e645525100e3e64552510073d645525100e7c64552510075f73552512c57c73552510075c73552510055c73552511473f43552510057f72552511473c42552510057f71552510077771552510077471552510167e61552510177661552511473c415525123d7c70552511473f4055251145be74d8e51005bd74d8e51005ee72d8e51005ed72d8e510f5f671d8e51006df6398e51004ff7458e5100cfe7458e5100cfc7458e511067f5458e510067d5458e51106de5358e51106dd5358e512c67c5358e51006df4358e51006dc4358e51004ff7258e51004fc7258e51004ff7058e5101cfc7058e51036de6318e51006dd6318e51115f67118e510057d7494e511e67e6494e511e67c6494e510157e7394e510175e7394e512c75e6394e512c67d6394e510075d6394e510065d6394e510057d7294e512c7767194e510057d7194e512c7757194e51005757194e510167e6194e51017766194e5123d7e7094e51034ff7690e51004fe7690e51004fd7690e512c57f7590e510157c7590e5100ebe6490e51006bd6490e511573f5490e51004ff7650e51004fd7650e51004fc7650e510057f7550e510157c7550e510073
  | 38 => 0x34ff74d9543034fd74d95431e67f54d95431e67d54d954300cfd73d954314e7f53d9543004fe72d9543004fd72d954314e7f52d954314e7c52d9543004fe71d9543004fd71d954314e7f51d954314e7c51d954301cfe70d9543004fd70d954314e7f50d954314e7c50d95433057e76d95430147e76d954331f3f74d95431e73c74d95431e75f43d954331f3e43d954331f3c43d95431e75c43d95431e71c43d954331e7f74d95431e67e74d95431e67d74d95431e67c74d95431e67f73d954331e7e73d95431e67d73d954331e7c73d95431e67f43d954331e7e43d954331e7c43d95430067f72d95430067e72d95430067d72d95430067c72d95431e67f42d95431e67e42d95431e67d42d95431e67c42d954331e7f32d954331e7c32d95430067f71d95430067e71d95430067d71d95430067c71d95431e67f41d95431e67e41d95431e67d41d95431e67c41d954331e7f31d954331e7c31d95430067f70d95430067e70d95430067d70d95430067c70d95431e67f40d95431e67e40d95431e67d40d95431e67c40d954331e7f30d954331e7c30d954314e7c6559543315df73595431df9c43595431dcff7459543006bf7459543314ff7359543006df7359543314df7359543004ff7159543004fc7159543004ff705954301cfc70595431e57e761954314e7e76195431e47e76195433073e741954314f3d741954330e7f641954330e3f64195433067f63195433065f63195433075f431954330f3e431954330f3c43195433075c43195433071c4319543035bc7655143016bc7655143034bc765514300dbf755514300f3f75551430073f6555143016be6555143016bc655514314f3c65551430163c65551430079f7355143035be7355143035bc73551430079c73551430359c735514300ebf635514300f9f635514314f3f535514314f3c525514314f3c515514314f3f505514300cfe7654d431dcfd7654d4300cfc7654d43005bf7454d4300dbc7454d430073d5454d430379c4354d430067f65d89430067c65d89431af9c43d8943014fe75d8943004fd75d8943014fc75d8943034fd74d89431aeee42d8943004fe71d8943004fd71d894301cfe70d8943004fd70d894314d7e75989430057d75989430067f65989430067c659894319f9c4398943006ef6298943005f67198943005f571989430057f755894314d7c75589430067f65589430067c655894318f9c43589430067f65189430067c651894317f9c4318943006ed6218943014fe7518943004fd7518943014fc7518943034fd741894317ebe5418943006bd54189432febe43189432febc431894317eed4218943004fe7118943004fd711894301cfe7018943004fd70189430067f65d85430067c65d854311f9c43d8543014fe75d8543004fd75d8543014fc75d8543034fd74d
  | 39 => 0xd75d85542de7d75d8554014fd74d85542e6bd74d8554034fe73d8554004fd73d8554004fe72d8554004fd72d85542e67c52d85542debc42d85542e6f651d85542e67c51d85542def641d85542debc41d855401cfe70d8554004fd70d85542e67f50d85542debf40d85541473c5498554005de7398554005dd7398554006df6398554006dc6398554005ee7298554005ed7298554006f7619855413f3c5458554005df7358554005dc7358554006df6358554006dc63585542d73c5418554006df6318554006dc6318554006f5611855400cfd7518554014fd7418554034fe7318554004fd7318554004fe7218554004fd72185542eef551185542d6f5411855401cfe7018554004fd701855401cfe76d81542873c54d8154006df63d8154006dc63d8154014fd74d8154034fe73d8154004fd73d8154004fe71d8154004fd71d8154286fa40d815428f3c5498154005de7398154005dd7398154006df6398154006dc6398154006fb60981542073c5458154005df7358154005dc7358154006df6358154006dc6358154005f77158154005f471581543273c5418154006df6318154006dc631815401efa6018154006f960181540367f75596431de7f5459643156bf54596431563f54596431de7d54596431debc5459643034fe7359643034fc73596430367e53596430367c5359643036bf4359643036bd4359643004ff7259643004fc72596431debc4259643004ff7159643004fc71596431debc4159643004ff705964301cfc70596431debf4059643014fe7598a43004fd7598a43014fc7598a43034fe7398a43036ee7298a4319eed4298a43036ef3298a43036ec3298a43004fe7198a43004fd7198a4301cfe7098a43004fd7098a43004ff7558a430067f7558a430047f7558a43014fe7558a43014fc7558a430067c7558a430147c7558a43034fc7358a43036ef7258a4318eee4258a4318ebc4258a43036ef3258a43036ec3258a43004ff7158a43004fc7158a4318ebc4158a43004ff7058a4301cfc7058a4318ebf4058a43014fe7598643004fd7598643014fc7598643034fe7398643004fe7298643004fd7298643036f6719864310ef54198643036f73198643036f4319864301cfe7098643004fd7098643004ff75586430067f75586430047f7558643014fe7558643014fc75586430067c75586430147c7558643034fc7358643004ff7258643004fc72586430febc4258643036f771586430fef641586430febc4158643036f73158643036f43158643004ff705864301cfc70586430febf4058643004ff7558243014fe7558243014fc7558243034fc7358243004ff7258243004fc7258243004ff7158243004fc7158243036fb705824307efa4058243036fb3058243036f83058243014fe76d954314e7e65d95431e79c43d9543
  | 40 => 0x3002000000340040000000000800d0068002000c00000000100018000000000700080000004002000006c000c002001001200c8015003400700140070000001000400400080080038009000404e000c0170008015000000b00140030010050004400c00000100000000000000a000000e00040270038005000804e000c0140028009001c000008c016002800e0024008002c0000048001000801b00140000000000001800000b0003000c0010068002010c001003000600140000004001000000e00240010020003008c00a010c000000000600040030000002003c0010004000001000c0008000000c0130000000002400000100230010002005000100540230008003000400100a00020000016001000200040060024000002c001002800000100060050007000c00300a800400000000000001000800200100060034000004c0010014004005400000880010050001000c000000000000000350010008001c034008c00400580020060025003c016003c006000400700400080000006004c002000000000140150024004000000000180010038000000800300180000094002001800a003c0010010007034fe76d8d543173c54d8d54014fd74d8d54316de43d8d54004fe71d8d54004fd71d8d5401cfe70d8d54004fd70d8d54034de76d8d5433f9f74d8d543179c74d8d543175e54d8d543179c54d8d543171c54d8d5433f5c51d8d543179c41d8d543179f40d8d54316df74d8d54316de74d8d54316dd74d8d54316dc74d8d54316de54d8d54316dc54d8d54006df71d8d54006de71d8d54006dd71d8d54006dc71d8d5433edf51d8d5433ede51d8d5433edd51d8d5433edc51d8d54316df41d8d54316de41d8d54316dd41d8d54316dc41d8d54006df70d8d54006de70d8d54006dd70d8d54006dc70d8d54316df40d8d54316de40d8d54316dd40d8d54316dc40d8d54336bf6498d541e73c5498d54006df6398d541df3c5458d54336bf6418d543073c5418d54036de6318d54006dd6318d54315de7618d54006de7618d543079e7418d5432f9d7418d543075e5418d543079c5418d543071c5418d5432f5c5118d543079c4118d543079f4018d54036df7418d54036de7418d540369e7418d54036dd7418d540369d7418d54036dc7418d54306de5418d543065e5418d54306dd5418d54306dc5418d543069c5418d543061c5418d54036df7118d54036de7118d54036dd7118d54036dc7118d5432edf5118d5432ede5118d5432edd5118d5432edc5118d5432e5c5118d54306df4118d54306de4118d54306dd4118d54306dc4118d543069c4118d54036df7018d54036de7018d54036dd7018d54036dc7018d54306df4018d543069f4018d54306de4018d54306dd4018d54306dc4018d542df3c54d8554006df63d8554006dc63d855400cf
  | 41 => 0x20004000403a006003c0008000004800c001c021000000000000000074002000000b001000f002800f000401300180010008008000c02900140000028001002400000800070024001007800000000160018001001c0030000004001000100000010024001000c00700a00000010004003801a004c002003c00200280030000021003c001005401e00340000064010004400300100000004004000002c00040250048003000400700200040004002001400200040000000007001c0000000009001000000000000018001001802c000c025003000b00d000b002c007005801000580060040008003c000000001000280010000003000000b0070000000c01b0000000000c0260004001000c0080000000002000d00000040004001001401b004c0050020005000400000a4000010c002000802200500020000000000800a00200000000020000000000040010030002000800000ac003011c004001000000b40000008030000400500b0000000000b000400400980000014000000001100000070000001000402d0068000000000e0008000006402c00000380008005000000b00080110008000013000100340050004003000000e000400700380020008002000400400940040058005000c0070034003000401300c0001000401d0004006001000f000401c00140030000010000c0130004000000400400600050000001006400000140040020008001c00300100010004023000800800000030034005000c00200040250000005004000e000000900200050034002000800100000010008004002002700cc00d002c00400000010000008000400a0008006001c001001c02b000c001002c000000c003000801d00dc062000c02201200120000011000c0020008029000c0000000004002c000000000100d4003001800400080040004002001c00e007000600000230014000006400500000010000001000800000000030008018008c0010028000002000a00080170010028008800200540030000011002c009000401300000000000002002c0050030004004c00000000010010004003800800240000008017004c003000000f001c0010000012000000d00000020048021003800b00140000044021000000f000c00d0000000000000100140000000002002400f000400000d000000000040010000003000200100010074002000c000000c001006001d0008004000c0030000006000000d0004002009401600080480000000002400c000000000000250028002000005000000000000001004000000080000004000000400000000010004000000000000e4000001c00500a00180008001001c004000c009000000100000020000001002c0060048000000000100000020000000001400c00080120000000006400600000000000002002400100000
  | 42 => 0x100168000001000c00000020008005002400000380010000009000c001003400600040000008009005800200000000074013000803a0004000000c00700100090030028004000d0010000000c0120008003005000a0000007000000200440060008001001400a002c00000b405d0018001000800300040010028005002002200180100000002000000100300070000000000400700100120010011019401100000040000011001800000040010020002002c00d00dc00000580100000000001c000005c003000400a00000170004002004000a0008002006000300040000010003000000a002c013000801b00000010090002002000100680030000001000001700540000024008000401a0050008002c00a001400b0060000000400900500000020008003000b000c0010004005001000200180140014001010c0000000005002400000080000010001001800100a0022001002c0020002001c00000200030044000007000000080010000002000c01000100060008008000800b006c004000800500140060040001000400200280180018000001006a0008005001400200ec02e0084004000002e0000000000800f001c0340020007004000200000010000000000400200280180010001002000c00180020004020000c00000340010008002001401000100010004005000000000040170004000001000a002000400140000000004002c00100340060034000000000b006000e0028006006400300e80010000000000800d000001600000040000005000c0010038001004800700080000040005003c01c00000080008003008000b000000e0010002001c0060014000001c001001000800b000000180030000003003800e0000038000000400140240000006003c006000c0110000005005000000e8000000c005001401900280040074001000c00e0014007001400000280020000000000000200940210010000002000200e00080018000008c00300080170018000001402b0048000001401c000000200040010038000002000f0004004000c0000018004000800300040000004005000000300640000008002001c00a000800100080090034003001401300280040008000000800f000c007000000600300240020009000000f001c00900a800d0000000000400200040000004002007800000000110000001000000f00040010000001000c000000000800000020034004002c004000400a00c800e0000017000000000380020040000000400700c401500180060008023000c00c000000b0014000000c0050014000005400000040000004000000c03d0044004000000000e40020158000000c0000008009010800b002c016001c001000c0050008011000000700000000010000000000a00000070000003000400000000040014000000401c0
  | 43 => 0x2000c001800000700030000016000800900080070024013002c000000800b0004000001c01600e8002000400c00000000030020006000000000010000000003c01c00780100010009000c00700000000008000000800c0024001000c002000c01c0024008002000e000400201440000000000003000e0004001000000200300020000002005000b000c004002c00b001c0050038000000000100140290048005000800d009800200080000024006002c00300a800f006400200180010018000001c000001800300000000020002000c0000000000000400e00340020020005001c01a0008007003800200140050074010002000700f800b00000070000001001400500ac00b000400f0028014001000b00040000024000005c00500280190028000001c00b002000700200050034005000c0050000014003c01a002400c000000000080060000002000c0000028003000c037000804e0020012004400c001c000000800d0024002008000f0078000003000d0000005000400000000020020004000001a0014001000c00400000010008001002c000006c0130000018002c00100000000098000002802e00ac00b00240000010000000000000000010004001002c01c00100060004004004c00a000000e000801c000400000000000044000001c0000000007000c00d0024000000000a000c000000000300000150000006000c008005c012001000800d000100c80000000000000c011003c001022400500500040014008001400b002000700140060004001004800000040000000002000400a003c0000020018001c0020014005000c000001800100800030000000000c036000800800000040000000005c002000000500400010004026004c0030008000000001a000c000000c0010008000008402d0008020000c00e0034001003400400000000000018002807200000000020002003400400540000008003000803a00240060004006005c00a00000000038001001c00d0064000001800c0008009000c005000000a003001400000010000000002800a00000020004000000800e00c00070010004000401f00000290088004000000700000000080000000000b00440030008009000c000004800c001400e01040030004000001401500000050000001000000a000c0000050001001800500740280018003000c005000800300380000000004000000000140090128003007c00b000401700040000014003001c00300000010000001000c007007c006001c0080094013000800a0004000001c001001c0160000001003c008000001800000170000008003c0040010000000c0060000002000001800240000008003000400a011000a003400a0038008002000e007000700040080004004001000a0040002009400500300060068006018800c009c
  | 44 => 0x40190040000000c006001400b00180000024003000c0000000001003401900240000000005003402e000800a0098015000c0130004017000000100000010004000003c04100000000000017003c0010024002000000000040010014000004c00e0028002000c0060000004000000e00180100000002005c083000c0080014000003c0000018044000c001009c000006401a000c0320064018000001c001c00000040000008000001800200100020030003000400a0018001000001b0024000001001b003c008000000e00640040028011000c0040050005000400000000030030000009c0000000003000400200080050004001002c01700a8008008000d002c021000800c000801e001800a0000001000800a001400a006800000d40080000001000400b001c001001800a0084000007400f0000017003801c000000300000040008003002c006000c0020094001000c002006c00000d0020002400100040160000003001c0060014031001003a0040000001c0010068013001c00000080040000000001c001001c00000000120000006000400000480000054002000000100040080000000004405f01000190070002000c015000c0030004005002c04a0010002001000b007800300140100000000001400b01180170004018000c0000058008000000e00000020004009002400e00600000008000001400a000000b000800e003804000480020010000000800d0050004002400100f800100040000000015000c00200180010000002000c000000000e004800c0008002001000000040010008007001800000240170028037000801c000400a002c02400580000038004000000e004c065004c000000001600000240000003000400000100070000000002400000240000114007001001700600140000000005400f000c008002c00400dc00300400000004023004c00000080000010000006c000003400100040010008004002001c0004000005801900900000000000002401f0008001000000b007c00800700000010006000c0220038014006000000100000020001002400300a0022002400d004c00e00080050020015013800300c40280000004001802b005c00100300010000006000000000040020050012001c004000002b0034000000c01d001c001001c071009c00d002800000180010064000002c00000040040004003000400400040040000005005400100dc008005000d00a4009000000300040030008001001000700280060008008002000300040090000004000000100040290004000006c0070008003001400b00ac003003800000900080004015004c009006c008002400000540010014010007403400100010004009000c00300380030004006003400200200030004011000c002002000100b40160028000000002e00b4000
  | 45 => 0x11a4aae94d00000f7486f2344c950c08363976ccd6244c42530645e42c1a0000000692a5fe95335f700024a80001ab69e85f1e7de05b2b531c32d5590360570e8d82e267ed08042025831bc77f00004ef80005d8000000020181270000d110f6c081404ebb29d34452000021000000001240be0c0007fcb106000039a4b7275465aa11e2b62dce9b886f6c908000426b56c81e09c6c2e1c5ed63208cac06c0007cb29c41e000057131d23d70168a4910f800028265e204e06a01229d8230328ea27aeb54db909271ae64eea62b9b496444605308234164ecf332741e6d8ce8925d822faaf4e7b1571cbc6202c30a8688575059a90e169027884380fd1724944aece80f01590169a2ab9c35ba6ee9166526ac862b298ccaf0a3bf4ac16129a2179c823517c1a2aa8a83d28c02a611625ff20a0245262202e800040c942c026350462c8e7ac4311017a79ea08968000b7c80000cf00005e60b8c000000000004f40000eb479100d22d59d3abeaa3b80e80f9a016dccec3c2a1ea1ca6fa04396ea95589786c2aeda0d9000000000000001130328861ecc09dc2948116e636a65e34b2164000000043b9bec012045200026c000015a0d30215e0000000a5516e053909da68787a780d000043d000073cae782468a220ea1182610000043200004e80e304b1c86e557342291b5caa0001d71b53d28a62ead4155de4ba4bc8e5e26b26cc4e605d60ee8f49c052ed76859a2ec990328b1991e43b7165059707e868a25505f414ad248948714d02822be00dcc43800019e44d6aba00005991e8c9849bca5c3896eadc8a4845feaaa4a68000590a05cd2e1b2a4d78000536227138d977cc8ca92e49599de10a9e80575a9f8d71a78c93f2b8abcb95a46510ff8b431c7fc28293a6f69e4d010a94eac16500ba8a502c7e8ce87591e9acda848ab90806a828cc5c93fb20c46a0000bae2afa5ed26d65a29958267a342d4db4da35b00003d00fa2b6f00007c9abee177996287b90840000bb203335ff74dd780642cd304ec04fc8df94a207c1b284bc27c000018908f0179664372c062180007ad9f32929b18260b18f20000e5450c857a00000000be477e5119daa6a8953ec7f35a28559b5439d8f8c8472237d2380000000f46a8fa5de00020fa9d4b484838192e99a800000008d26528d7ac424f1236da65c34986ff0000000000178c0002e9384880005acacb4a4d35f0a8c03446dd2c14262b52068daecc83c00000001fc8c7d308000000000000000cc688bd00001a66672c02127a4cc9da91d0c77000000035603bd618400012700000000000273c0000fac0001dfe0000000a9e5974000342623d860e4829d5a5a046588fc80160014004008800800200040004003007400000080060008000000c00300000000010002003c004000800100080070000000000
  | 46 => 0x6aedebfb0fbe073b0f6d0706e69551302ccdc0008db8000d500000000089c634aaea00000009bf00000374b3e39417740002a0600006e40001a88000000085b0000ca480007f91a653a122bc000166a1ad353e23b00bc793f4c89581a84c331f771b0a2406a9c04c000190500005b49b82e6844a8000bfa0f3e0001018a9e091cabf800000003529c00000d7ede6038a952663a14a0d66c87cd44dcf4d62129000032dc69092e4d13045a000000042f1dba352169e2dc1272cfa800062a81207369ed8c35a080a9796724c5339ec248a649825d965cc82d07c39b7a75998888a25a62baa8c748da0fe673481d598e8c26d6ae52a33b2fa02b528eeb7e14e73a3861fac896480a5b56a50235c08dcacb814d80003102be02179a507f2a152582a82caea34ee259b1ba9b707140000392650230a2d228dec8d1a1a68f000000003165c18000adf0000b62800068900000001fcc00000000002c9233897f0039a51475234fa11b92e2d18b27861f2b1800000004d535f80a8b5c72011c293ac0832386267cd0f91424015d5e3ec828c1d680000000000a1901dea9b0000ad78952101a6a492f8254b64ac9a7c20234becb4660000ea25630c0a3e74ab8000125a00000001622bc029f9f841ba6e6a87f069887f9fe300025ea0001e5000021c01fd8d383582ff400019b400027998c816005bdab6cb071e1ab5d26b2612886300f9748264a0470c7842c104c938c8e2a816132186992b418b7321d600016ce4940bdc0000814017df492f2071096d321ec120d821aeb5de000185fb28180a11411680bdea2282640000000000d231b0c47e9d134d8b582b1e8e92000269a4c11cfe3c87202d4af11477aaa446c692ce381020648174b2cfb0bbeb992d086b80cb0a34a5c03ce269c692139c000149c8afb53875cac567528068626876a640c0007b90000000001e9fb9c288f280008e0b04a6491f5c1041d7eb0f1f2a34f86a2503051e8bf1c2713913ae8d31fd730f88e0ceb800000027ec95c0000282400000026b400020b411d800039380003fc073d6a9800070080000000ed20000899000000056b27ce7d1a6530000ac6d4880004c8deaa1ace97c98e000000005e014999d4466347200003b03fdad00b901e29b240f2d5e882759398a740002d42a01031aafe69ce9a828149709af061a000013b98460cc86925fb9a9715d30fe12d9f7000027609511738664008acbb1d8053221f01698c04c15061b80edd0c69e136c5c213e89eca4ec57e1e5895ba9e44260a30cc8095086d0fd733cc0cd0d32fb8d77c4947ea870a38ca3d437328d04f330de2f7932c531800017ba0027aa0cf68512e28000339c00014ee298ad328cbb186b0e01b20000000a279516270151ac8f34bacb5041fa870e3882b2c980000000a44800000011f0d592020bdf1dee7f9800
  | 47 => 0xc1575deba0741312362a0062480dde9a9800059fb19e8e4166c4ec8d02b6d15cc000319055480000001684000000000026492de000049813060002956000297400033f85d8ac60c48a70abf926f2d7257aa47609480002446745800086726a2a3b0cba0fb9073925056000000000a506e23dc000000024b0bfb835c00016e83bfc00000030d0000000000007a20001e6cc9106f2b0cc30000026685b2000057b277c2910000c0dab24150b26e8b4d2f4abc154a6678c589bdae2ebd62dfa94a1638b2c800089c00009c40000bcd81b6a47000000014b400028248c913c8bf1178a3ab1f96d81da7207144ba7058000b5e8cc27050000000000003a0000bbb0000ac497be52e0000d1406762a10000000189c9b90130b8420a22532d020638000000000000018270000000241800000000000000664000118a00000bb0708000000000027e2bbc4128046000324c0001dc84c400009ae00000001178a542d9869b433f31824d06fa2b5c622a7187ac8000d13a8380002f8800000000001676d6b47fc00000f85dc2dca00000007468000d79df7c00000000521d8c8cd0abe14800000002c247b280000001de85d5800018900008fa1522471800000000005b88000c1eb4c6d54ad2a160a42277f683e484a3560001a8c2cc08c80000e9e5d1092e00000003ba97a0a2aab5a0002e2c6cea9be00000000002f260000ca6994317b7780bba3e10000018d14e2091a897a580a8055253cb7630986a80000d7d74aa000032aa98946800008b2d5c5d5299d19497644356000165413732aa0e5090c12c80004fac0000001c10c91a87d68822c02ff8e806e99b42000000a6da5020cfea48a1ba97fecb29a322ac00002f68000d3a40bea5eb5bc28fd17d1b587764408f22098aed0000083041dcfe3c220000864521c37480000000000afe1f0b7398c323372596075800000000004f800007482f3464e1f7e39011147a60000589845eba0a3fa492cfe231e83b63e946c8bf484f80f896bc861e91a0088b7c0ef00efa7095f43f40000000000000013e65f68f1c48a1c52219b51600030087cd40004bf0000d4c026e172ad627f426288cf0db0d7daafcb0c2c74b3206faa5287d8381a8cc51797d669d000000000005b5152a0000f3a14b150a00011271794000855240e000012389ae79e8a419a64800468c929b94c1b9b3044f2a00834000000021ba15aa65a7aa5120228849a2f335cb3fb22cab3ba5ba70d0f25b9404e29e74f2e0632436d41a818a259622651cdf96ac1ed48c220da8e2a108b3d8a60800c0007e298d70568a3223b87a46279ef6000178ed221af28620000c6d80007f3e0b1b83952e75b075c00031a08664d620d6b3f04d583080000000d79a0380000ed690a22160001d3c9c8074600011ea5cb8000c47251a6318529a5913f0aa59ed2a2
  | 48 => 0x4a9b8e73bd63bc0715d08ba00e276c0e1a75a1f4d66a9d27bb53424498ae5ebaa2bf269bafc062f2316cc01fb666faf5200001b449a000000000009f42816aca0000c28886981c11e098b0000000000083f2486b98b59000013b851c000000000005ddb4280a2241c2b00000790c0001f1b61847fe5718853375d6b0f07269a4d200028128398000ab9b1047cdcd4200025be9b7800065c0e10a8d0b680000000193864053e10b45bd28f671395b2d478000afaa7d4a3c207c73c0f3009c35797f4ad444641eacb94b48a0002dd600000000000000000224abc900008890e5a896e69e18180005b3054e00003ce0002ef24089bc010f95bcb6a00d8d440cbe9af81466602d9c9ee8e78adeaae265099722bf04a471432300000000c78b0e06530000621022e2aba9a700006822f2a88eb149b008938f040000c8000031a6a6e00009430000d8680003328000b3c2732b30894e0428f489838000000000029580000000000b2100000c080000002d287fea6ce2aa65f412806380f70a3ec75b5bd43021d0826c5f804d0dae351b0207d2dcec120075d4cbc24672782ae8ff05ce7ff3102000000000016d2b5f81706263486d39a9bc94d09d0b1fa42e000073a3df0008a7301ae39f2ec2000330419d0000000270200022b2aa91050d3492e84f768e074a8fcad3617e000000006bf800038f0260102220e7440b5ed3a2d30a3cae0604f2c0ab3e8856b8689f689a9f2200025741988cb4bc282ba6738d9e094b4a609c888c5e0828d00007398161c641031a3400031b7ba984563238b8e00012fe05f000051d1ff644e127e000166e6d6073045194508e190d44486ac0d6549ca5eb95c88b91a8679d5b77c6690ab8ba8000b38858e4e11dec6e941c4a65351873504ded7eafa47f09234191b19325c305a51882a46fe2d64a4623a661f800000032e43cce40688729c480110f20b98c3004c95e89fc02c24de31f219ed332463a9a2962078cb450e2664507ee109976a15220ee749338ea408b28454a8b67360bc26ec244236a9c2567b808464207158182de85ea1550625745a32415745c5ac18c6bb5ca31c2f8a3d61a0e0000000be4054463933ba00006f80000000000000000013d60000ef6d1217c403e8e290000324c242e0431b9a496d1344600027f400000006edee7c71d228626ea490cb60dd84d6980e035ab8c763ab2184b000036b0628467a6ee9421be18272eba2759baecb186d477d0242c118ab211700ac6b39a632fe18449f9000081e80007c1cfd39e42d24851ae72a84800ec4b1f4f30b2eab2cd950c0000000c2330b219408d85c88b9647adc786651202105a2e082c24241f5b34800023b027521c89cfa23553695925d922993470320af48572c93b31178095984819d7a0a28390c47ae6c3c2a74458ab1523a420510e2a632c3b00
  | 49 => 0x458c630350abe1f0f283a810d455c68ca7a83a937c66e97bb10bc6d245ecfe4c86a152a48b17933888ea756bd99de5d0d8000c321e87ae9ab4e1691f4cadb807f7d5c71e4a800000000b0448d80004ef456c0448000524b6030002158bf4000021d17ea08f71c80000000699000000000008cb2d3994baf1a3380000000005e000000095db06c28f00f600000007e9a12600024c68379390c01b1d35b909b49ce161e22d15020002eaec3e07cebc2000053f253a047851ca60000058e857c594800000000000001b480002e92a0209a4cee2614798c00064f8000af58034c3ca5a232625e091a9d425d50000000191ec29aef368f50ea0000b0a24d0000cc92c684d289b89641a8a1fa8244c5fde2b0ab022c22da0765e98500ce9b236d27ab56c6e2e24339abe205ba3c4962b09a52c83821b9e4a001740000001246c77800000019e819dcdf200008bc30d31802f180fdb300000693a6b646e1d985b4099c4438f8a541918654118ac07f699836012d042fa4320000000c0100005c765320001c7a0001f65000000000014e075dab92a6d890851f216a00019884785674a1b06f90002fde9aa1c2480940006e8733803930aa0000a6e0001e3c654eb0a0000e33595c69081598be0000000000000078bb2e6add03785fca3643f522c300009e608280006e6a95aaef9e0aa2e0166ac45bd07649f1722b85ba000228bd5a285680aa53ed14804910db2b2995adbd3c8e9d21c20f543f594cc0de84a2a1c29a42e70e7e3ea1acc6d79e2094188fc7b38be66ab2bf0240966256107de7a88ca0750038814e9dce6b595120d614e8d618fbd086af40bdf50080fc82166639c2a37015767daeea77902930819c74870399d8a0694333932786b0b5d4c8fa883c63f0e4603dd08873a11d2b7b8458c96b54e623025632b1f9044584d02942a8f1462c390000a2100000000000ccc00021660f52c8098b803222e47e684c13706539f9a282104cb231f8e4c7907dc5a974a129a3e233fb2c4718092623023762e36c5cba30bd0020b2b89a080000000a683430a173110000000130a207313200000003d2a78aa389536420aa907a08d860000e3e5fd301200010861641b3669f99a000e800047217ac1750b240bf8000758ad1ea5fabacad12f3c45e8b728f92972c92204a3c7c000510084c250937a9d314ce09d80007f3b5cc7e795e23039954c19a646c6fa2e614c9150d10a6361578000baca9321ac000000019986fe954cab600008658adc0002504000157c0002b06b339042651608bcd1990eb6b53bb0000f7ec871ad44610f62ced947ad56041482e9de26149048a4984ac604a7bf9b61d6e949988d00a3034310a6e8be60ba8b4fa75066b98438950ec082745b6b0187028948a4a8a782c69b4e2604271358d4e87901d080000966bc400021e422990d8c
  | 50 => 0xd51000000031d0cc19834097802000032f407a823a9e6c55aac3afb60000140a17997e720800077e93f800033a2b9b9bbe67d928289fa241744426c91f9c08bc8400083300003b100002112a9a55d6012ce48000586ac4c0001ef43fb9bb801880005a61cee000160c8ca0e2e4f8800000e1f1d0002f7a00000000001f1600013963c097e26930eca3c045fcd522766d33c00007966540aa5a7d0000000d471b2400001f6359055471500000bba0e2a7b9a5ed815c8800028ba000123e00016eb000359ebef1f75bd31f2ca41970400000006d7000000005244b30fb8000000048682a51350dfc1ccabf626c91cf3a933703bb12c6b1e303eae02d3c14496968f4b25ecd9e884cf40f43d5f63d80e10ba20002bce46f800055c80000002d6011eb4a464a000033c906c000000000000002ff02e4a6087a8b2780000001b6205100007a982084a31110000316cb6c80006ecc000881a24c3ae128e0002088000000023a4736d20b4305bea0c4bd891c4000079f532c0000be28f8c8805c249911367f614b07c68c7249ab328c4490871ef8e9c9fa806ebfc000079b8000b8000000001f1276e0a1c78a8000c7b9bdd00000006c3b60c10a285a9f7005000025486bf1f67ca00cfa8c60bb41df0b763da000000030704b46dc08c497146f7b5d70000de20001854000027acd7864845b000064980007d46378c8002f41886f321ad9f3c48a855601f62aa0001b4c4339476d448b608350c0295f839c98680002859b9da7d1cf839c97b8c278c1c7ceb0e6b63132acca8000b587528322315e8eba76e44680006790528908000007f0da2000185a41ba8b4b88164c9e9af9c6ad17c82038be2d8243d80a1a7a40b023461db872ca23450869c0af608826e12a8203ebaef563599a6ca65420c6bc4b0b4ca521a41129e8b2e18a6c973068e3bba5d04bb12d670286800000f3cc5d00001c8c0001038e6a0a805661d36cecb7f80000002322299a7ef58dabb200003341b00000a3f0000000333a50d239c08032e210116b80000a0c1a1c706613809e9871f047fd1b522240f95abd10a031a0e12000121861ead76bef819e0001f600002b384328a962d1800061c34ca2211b18c22ca03c15ad548aea2dcadf800000000008c380006ecaa166b60000b0ee16e00034322ef2f8c0002e3a0751f8058f347c5db75a66658354ab93583740452b8c792ea5071472c5626029ff98625cfa28a153352c92a8000000017ed5cd34c35280009d68000cbe9294000000006a80002fa000000025240000000b931db67108cae43f904450e06ac9e0c0006f1284c000113a699b27c48ec0009a5a426ad892802778a3491598e000008ba3fd162c72e0f11ad80000d6c0000619843a2a9a2de830264ea00a75e0000d220000000a658b1a01b2a880000868744aaa210280000001
  | 51 => 0xe662d4f10f03120000999956e00ba1da000000000021d85038e64b8780008d49ac8d24076c74b67e2d5d4772290350e0001ee92bd1b683ccad3a200b5aed3887546e5b2bed5caa5874104ae000220b8bf80008c03562c2093860001e051260a41000000018e82f00000221cecb3dea2240003c3497278a0024533cacc4c0342ace62118bed204b0000ede3568000000110039d0000785aeee7610a120f1858ab2a306000008e2bb98a1bb851bc8000000000017ce9960ddccdb1874b9e92d8000068449100009dd94a64fd34de9e4d5b085e8000d2500009bc03a2000055883e241a00015ea32313a6477e81e000000020d8000000048c00000000002f1021eaf5e5708c1400031fe1139fbecd02a9e12f870047f0a0291685a05a1a3b2370a8e88e5a64f0000ea837d54fe57784adb2900004aa8ececf9b3cad351cdcae10a3a8d0107c9de922605831666df649ab3f2fce1c5827853cb18a10714f021b003c3189e698750d88b3e000057020af80f72b6a8513ee1a8121ea08a62a1d91b78b02430a0001eec92d0f667831d460fb0000b4109f4260331c81522c403f0430197067c19ca44e8be8891769242c706245076429867948c828960ee0000000098335f1c5ca63cd2680003e18a1442b4000c842f860001be64672640000268c00000000000e0a63b92329ef4000000351a4309d0e447e094891ad7c82ff1928aa22320002bc800000000000000784041e00032d6000179ace200000002f06b7b1254000000000000009845e6100005c4b0800000000000d4980000000a1e0001b896098097644800000000002a89a1000024d6000354a950a61b0000598d2f2ada96f151e8ef222a5ae9fa2d3e18aeaab27a942924de98a58780672ad00701bb40001b2600007920002c62af426048f227c600019d00000000b0da480000000072804eabc5a366a83000000014ec0000000072127a03d74ec00020a82c700000000000a899818d675f2d8e68ed05728000000271c78b000000000000002d46a3700008f3800088400000002ebc0270000000135064183cc81b850ec820d18b77139200006f070f8000ad1ad50743c00035e23be00029a88b6cba436119a47f89e66aa70916bfa853b235196e23d2f720002a5470e98f8c71a4140000000b8a80000000000bce01526178d442d605b000000002aeb57e91c000075f2ba2b2280374e8ab4c06b22f06a7a2f2014909270c0000ad2985c00014ac3d81c92605a36064420fed7393649002c17cab2d7b6c1a02e01eb076311af54b9206be0442796bb905ac5a51c0ca61248eaec2a5678209849572eb36481e7a53ddb6491208649649f54a8ca259c030f455c7a1ec3191bdc074921400014264d99fb08279e1ebd19a0a97d8d106070602256000081c9f0652307880001a6b00018c2a5300000000000
  | 52 => 0x436f0342bb820d3c532538648956b0002dac0000a9abf2144c0000000ae81c8000000005900000c5e000017c8a5242003e0b2aac151308f39b07ad59c900086c4680006dcad880001028a3e9c2c1468668273183a0fe9d9c1199da286d80003e9b440cccb26219e9b4a5e78e1e57708ac3f9217f6be8d4c8362d6e8625c98cea325209633f4d15180cc0a000069820a5a11a58627f1850748800000000000003100464acd661a8000ac680355d7818630880001322ac282cb1f0cfc843c41c0e1c52535190890caa895b21a37e245981de2929910000ca98bf600022943c4182a6711016c891810c5c279420422ce028800025aa7a0aa500003a0890ac5badb38b30770d2d1570bf60418d66a7b47e0ade22e200793e38af077b60ce84f80000fc358042a00008d3a87c06499f4ca12ffc00027bccc53480513a72c60a0f416b09f53be69ade0aa32f64a7983636d0000cb83272779f31012ac292104815e7d99f0a166ea50a7610e418435a855f80000002b342650158610b15a7eb842e9e3a66c25f27cf00000008b580000000000d1b242ac1d33296a623500e980766252b64000034853e9fec000211400013bc4004000000191c00026519ee00000002179cc4800028a2d6c0000dba0000baccf48dd600000005170b14ae08f90753800032106da811a9b20000a5c0e906ae00000009e8f43abd58b4077ede769a61896c4d1aeab5e251036400006c100006cb16692db33220000000b238000ae380004dbb168c509dbc0eb829a8a3862279bde6279c0000863f29697983fe9698a3640522c8a9d897a00014891ebb16464e95ce9e10000b34a8c8000321645700000000740d85739a3bfacac0000000202b162b681f9cc69287f7945ffe7c50766c8180000003354349291000007dc2e7a9a600016781191d0d0000ebc1832aae4a72f94b49800035b8b82aeb8d0640b2a18154a652000320400000007b3000096cac6c631318800024ac0000b6e37db50000007acb53a630d690b0e7711aa80001fdc5c300000000000ce31f4e6cf30a43550860122267a0001eee9931d005a9300e3f12f28555898cbc08cea000039ec8a80004adb3e28661d0675c1efe3c3aab4a8b939381031a82d98bae0002b020000c3a00036120001aee2960000c23b2a28bb16de76b863c862a23e9c212c46808250000230c0fe01981bf82b8bdd268e0000578c4f00000000f1e000343405e95d2606a7823cb169980ae0dc74b8000856800000010797e268ac3d310ffbb581e8000000037385924d3a98ca6ba0300002f5a0002ab0b120000d6c843f2414f009f787f81aa15c6411800010ef5b40001532000320e5b58000cec0a2c4b0d3e47669bf00000000ce42f041bb9ef30002b0485c151344baaad27c000076f9c86d812e380002f6ea108cdad258d1e399a834087
  | 53 => 0x48f16a429f59841124121f952c19c35d0357a46e06134165042bc60df1e34428ae3cd7854c4d7c945608cb502902b57f51834be902359fa1e17580d833660871b6aa9b878e5ec882ab8d020254e8f5037216143ca87949598000566874aa26094000016aaca327e6580801c39b965f05a93f2a635fb816892ac504923c5cf11e34a100ca3e588de8109118b84a1b03692e32aa085be9e94ca406a0dd4888302e0000000887b1cc7b40000aae1a4f1ca92d2ba43270000000000017bcb999a460001ec0475a4caa680854b329508c1410b283a8e810f29da0a51a9fe00031a200000006f49e5d11090c493097ec00034d09f0b32e864a08a00000003ef031441580e000000000002a7ab8fb3da0f9a2b05cd8000681336067c946e0000000000224800035a197916b4838e7263353214d6be2002f59fde00017dc6ac8000523a6ba00010ae00029fa8729655c2fa5c89e89131bbd2305038e116b3d0e0cba79cd64e384bcb9721cc57929c8a1a90ccd5f0000b3688aad450ec5c9b1b2e7470c66132aef6ceb21d271687ec7756bb80db0cd8097cefa22e0786b442a5a923352a1d894b1c5e9a4424600002c2170a0002894cd0400014aabca5651c360895cc478d8000b46032c00022f86af9dca9f743b82d124ce6a401ba892c35e3e214962d69c2e00017302b98088c09482e7ea4000000221a4ea000017f80008fd2028047000022958b83152aee9439eae932252c31f2fac04aab0850522f30a61cfcc558000b7d896cbac064296926b058426392358e96c2ba14c42f4aa897f641ed635a5679797a4365b4b647b2e360ff0000291a06a45468b25ab800c6e8a27289d13c6a59a704479ec9c786e7ac3e52c507abe32a08c1786cbf29683ecc620b8333a000015b600c00000001a684b2ab54c4a0f56b371c4c000041a00018a283200ee4ed28ae671a74805335fe87191cc509200a255c00017be39887da692d839ebe04eb276a6b228810a6a98ab5000000034ebc898ac453aab000002af6d42103a00011aa2e822efd766da663da06691569d017aa568b561eb09baa46440d01820000000c6c800063e8956244881819526489c32c328d2b6143422af21619a5d47c8c9c64b11f657680000002baa0000000000010255800006b1a12e000000000000003c8073e8fbb6068fe0291000143ca7990107c06daa2d52f00761a642bda28be000000050c0000485aa4a0171fa0cc2b40c877801280b60d67921b13d542ca6ce5936017a08ca46db3e800007202cc82188a573505c0807c000226e00031d902a80b00001cb6118893e678026624c00007cd9144d5c0dc60c31344bc3a4e2840a0367c0237c7d5600f44f80000000000d59511e18a9eb5000297033d29d6159153d92d882650124e80000c064ce9cf600035570002d5657e80006c793165968b6
  | 54 => 0x48c32b34435f864c68888fed50ac128fc05a83d7b4060000da80001066cad0f9cb9826063f674e0cf19cbcb0b06230291f682b5962e0773126cff183890115b84f711124592da40da8000000000002418b02640000ce100f44f40efc000204c00000000f4000000000007a28de034b8cb6b0a8346aca903035cb42e0002ea431fa9fc0000000a64979200000002af2d12ba68f2800000002d08000000000000000009878000a33b47437428a50000000000000000000000001e5c00015ee0002eb6c1a12237000000ba5de4900000009eae462c7380009061c966e070ce4c7060a84d2a522b480000c40896caf00000002b520003611c99af648088921b0206940b102d871c03e4a750a7602800008f73029a45aa709bd1ba480c80fea7c03aa7408000000021438b0cb8488884ea351a330000000c000000000299c00002c800000000000cc644722d200025faa2c0e56899134274e103ca5a893619cc70c96c24ee8a809245639fb4898ae9825d89cebe10cd2c0e901e2f0086219822a23f21484c061e46b45acd468b04444d221e63e8183c04a0dee87a08be3e7959037eb29aba18a4cac5a981c3727123fc4000cd69d365d01e7e206aa72ad416f700007289f04da6abb007899bb4f44f28000cdd00005fe81f4bab2392b6c154ea2841e431316065f93030000217706e0000000000030f1d2c0001c7200001e373796c41c6aec00001e8600000000d88ad000021292cf19605a096ee03b0996adc0000081ec442fc30da89a58ec71a921173902aa36fadc4794dce1a7cadc66bd0b18783ac541fe9d74a76a8a88a318204df2b9b6f387825b187b7b1600006f88d1a9da108e3042eb479a000000034f3cab87c8a77117215c22c60003616aa8e29cd03969c01d19b2a5e143e66b28803e492477c81ca49fe2abe2fd1e2d312814a36317d440a8de858d35e2cac2db8c4c314ebfda25ebfe231a18ca0ae99929000aca67217b000009280000000b1e8789b98d64e76c51213de1b49d140000ea01c70b02000313605d1ceb0002fda2a1a91e00032862e600000000000000085c00000000001454d69754c00026070098000b82347e4e519f800000009d6340082d49ea00000000002b9ca67986e7a418eaa80869eb1c96dc23933aa73021782deaf230002d824000ec69fa6cba389247400033c44c9a6190040000a6c000012d2ac8413ab686d692a40001a5cad9837ecd09d1e7cbe60028ab4bb0602430ac4135282aa5ca1f5357633d400000018a872a000000000006a4a5b8799d32480982640a11230690c800c70180277682747f362b48ad824094c315c0001992946db4026d800018b87f4cd285aa92780005519f9d000000025a00004af0000000330e64c895a92cb01a00003de826260815188a41e83250ba55c6c0000f2408100009cd800022
  | 55 => 0x4a204a0306fc00000009e9c8a300024dc7ef0a1fac3274e167920c9dc282ac318df486a21a64811a3891f337e068986c51b307e48e924227375e41ef30727c92ce67071db28d7874e14b9b7e5d48d16c9a8c2385f933c00025da61054b68e78fae2d700004d1905ac05a3a0c3e95347ddaf5052ab51b3b983181ee9d8a4842610a579b8cac998fe7dcad910000000c9eaa80a0c8000b16910692f15a6181197ccb400005da308a93db34ca1da2ae7d23414b2d96610002aca7be0290000000052f279cbc51aaa0000e34c70838060102933e9d4ae07e88085d3137240e360000000001de304e00000001d80576864de56ac2c0000000774afeaf70ccbcfc3707a1dc94587a6ad620749f4aa9217c2abc2e02580c244e0256b950079a8066b2b9c916f90c768c08000bbf235ac490d368ba5778b0d095c4c61794d1709b0c0b16b07f55ca256580005c80bd20f1219e5622840024a8ca6bdb31eb3a9d83406b3863c325d40b3b60a69e82032e69188ab8121f045ae568688ade08f8d9ca12962072e8fdc2a308d1508a8e456f80000000000000092301c800092496c0d7aa2330000fe84a58000951907ebde6e0a00000008e0223c97e22428c5016c000000000000000f4b4641ec1dd41e10425d6489543c2f0ac11fa064c9a088234f1286000000000009ee2d281d8be7839678068e622380a634a1fa700011c26b151965d69eea3d49789bb134702fb86c464a45f63cd19668860ac87f7d81e1a9900a2592e88893464474c0e9816e0000ba72f2ab340b34cf016e621d8a268211d15b80ab1e48914f46610136466965851108cc8dc19b07d08932d7f054a16f23b4b4d2f7e711a0f5c3f04f01a690dc914a51e32c8828a6a8d7c68026169289a960ba5b3e871308618c096276a0000d605a9a22025ec07f98f047d71f81248000226aaa6c519c20196aedc42c0e587e340009771b56c9715182e45514092325895023394ac8aee0ac00006d1a637d599c66000000000034a26a3927460180008eaaace05cacbe2a01b9358c125c1399e77bffa0504fea43a90d01ca26fa3e63ac8ae83aa820e88e1ec457da9ba5672bec0000000b599a3ea0c201f83c91fe7b1dfac0725ae200000000c9acde6eb00005471717ce534dc984d60b30e1b923069df2b9132d2af627142a2337267b02431e019683f3b5aa92e033a71f2676bd82f808e20ffe8da91b073c4db846f00008dd248400000009fc8000366ad553ff26c89d89ab80b32d5200035dbb23c2e8b25af8e0001dde00029223d6b5be000115677fc0000250000a93b0ee0000000d762ac468e4756a5000007328b2e000226c13daa6627123ba24b0dda2318f356fd1f03d615368b3c996c5229bc67759b6f0d2a9c60000000708afa800000c63a6ad0e20880000001a941c89cf99e020914e3400000029
  | 56 => 0xbd861800b5bbc004a5569490acf9f50556075839280c045a88fa612086ad5797c60680e44a43a00e8ff94bad1a8d9861902ecba5acd87ad236c472800073434ac9dc8b2200000009d700004bdad9a168c9e842a8c780000100282ad6818f9e03059238e0002c0f84e000000011eea0f153c2a4ab07000258eaf31e785579fd4792d1e210d006400000b200000000000aaa00032fe4b9b578567924ec284000cde26d0742010c3dbb365ade30bc07180000002d06bf3000040900003de0b06d3b400000000000002c42a2413dad3580000e38340cd5879a0cee594539a6789462dd250db4c2d3935e07c667fcc098b4eb8c0da044a02fa45f87ca275ddd0be9900c67c262574a1fb279c495e7beac432a9084a3aea684cba99cc380182555ab5d2d4b8596911c3764b7b35badaa8447b8938ad67281c096a858b5e5f6c0351f6988a27ca635000007b80000002cc455226ae0000304a582b32a0a03dad1580002eaa1811c9b23a000000004531204920381000213600030242c3216800000009172280b601486a7a95fe00000005a38fc90000910599c000bbe84b00000fc02d48000cf148f26f096acbf5a296d1783680e36d6b89a08f1d4d103e6f308061d7aee2b6ba2826eaab9848c6c46bf70496d7084aa3a229e88169382aff27cc98926ac242702a9bb110c72b0eb6469a2d095485302dfac1f29a9d0a7b696a2344ad8e3fe90645191ed125d068c1a6db02a8ab50cc7a0e5249b84f26be0ca8ac51e3e878230691a132e5860a4ecc223b68c711c09dd14c091526946fcb3e056d15f20cfaf6a61d800000017056ea0704ca2ab204a206f46519fba11aadda4d717cc0641c8c660abdc5919544741e29a751350aa1b87c480926da6fb83f621096f23af8f42b89992a0bd9b82a880ee48654894d2b8b6f83db108939004b98829b4b6f95e04e20b1267990606e7c4ec904816210c99ba882ac2e4aa0e484798f08916307811d225c5440e4252fa862adda9ecc1022086298a9e2280d4ed0e2942832a6c29301d581d4a0160110e146c80fa108304602bc827ec777410a5b25f08d630b019d46a4c4287e0b3924ea28930f47d90ab491b118589f0d2d0879eb30001a18500b0c4a0db318d75a09aa8915a2c981b7cd5d15625108372628000081200008b7711818d000000180009e226c63b080002f38c4ed56400056e800000000007a70000000000000024e00159a1c0000000000000000026fe7b8c0000001c38c5200005812a5c2812410000000060fa96e0f0c000079ace87730000c88a598cfb8b7b01802d6d734ae47a224769cb9e0f7069ada4b6acfe3cd8470501b58e473800000008121c6e8934071fe14b081220e18685d18288cb28a55e8572a4c327939a6aea08224e95a84948550ca0abfe29c1632222998a0000cc4d2c270697f1656d
  | 57 => 0xc8b000035405944eb0000802c14e50632987719076424176e4172e76bcfa7304ca13c295c800077ac504455195209c707c53502fc9a42b400001f3e538b41e0000be07c0a08e24dc00020f907a61561246536cb0753577a0002202a3d0f80000319c335a7981f88e8ccf6288f0001a8b537235c50025228c11fb944b33be2ce91f39af10fccbc94207fa800052003b4ae914d2a2218d97f589dc0001ea79ca80000b8a2b89cd20b616b80004689be01c062d80001068592960e00012ae6ce14280db8000c768018b471334ba52b361ecb5f41b288787db6ea00000000c43d4a80000000000000000034feb48957a000280e51e00008ce9aecbbe2d2eb8882685df80b90a7909602fd13462d07985ee973400017263031b84701000000017420001a6c00029047b0b4f60001ac496ba40c456964d450000007b1eed0b50796a828b9284a0402000000000000001ac8deac390000000000000000000000000a3100000002ab62168000c580000104400057654c20001f5a813800095e00000001d780000440000079c00029441610000888952433c09c88f781cc2749e7217ea1a08e115681d10000c35000018616ec00011a0000000003a80003a28000a026a9900004fe00123c230da095000208617300004979f5e806a4139f615e684aa9886d41b9bb7f1814d84da58ace8c6c64f05c8506aadc5fdb45899c0750314182e3c994a479f211a9a5663e3f60aac0dd306266e341a848046c47e264585f2722a72b364b7a8000cb68241c1797e81fc990ca6280dea9f893b661ac94b91a1ce95e853ed7f6f1e7adc040bf8a1825a488722a50ef2247b13a3792df4620000248cde4a3c1869c00027422da9cb224388a13b620909ca311039b277e8a8f47800ed6bb184aa400e300008cc00002d417b000000001b3336f0b7a362797cb2624030e2cb20d1989daf2058701421899edcc7b0867011ddf8b20922c085da544c802ea20e1e143b5337c5d392d598edeb80c723d6448a4d4638a84833f27a821f73262338c16123a5a02a671ea4298d04b610bb80af2c40005b5dc0f09d183be13b61af0e08aa1a93e53250d0982827c26bab8623705c092ba478b4b1f868001d8800021128c99cbec7da2365a300008ce1aae49d800012e138c3fce5f9d8406e8824eeb129ca74623a85dc79d11dc7af2764bf29dac46b17c04da9b700bc8000000171a0000ace00000003f6800000024f00ecad3595b0fe00a7337100002a6a2915387f1add039805c61bedc2dd5dddf000000002620077342b33000004000000000507800083a0ac20001cb4074f3c2bb48000a9a217456a927c2142de000018ca0000339519af0c6af1f9473e81a922625f2784b5e31dfc0000000000439abb47cd222e042222c8bba87a8cd9d6a5220000d7ceaff6a34138a0025ac14f34086770
  | 58 => 0x3ea6b4dc584cd99bcb56c000d346c0e0ad0e8694d824c0002a60b79b3625ceb218000017667e82daa4d872ed5b8b8a62d88ed55e15200355c337f116682c034ceb08a7e8d1bb4eaab5b1e60ce129202ddfa8339237ab31a68ad65ec04d681586d1d9bbc3dc9b4e00009c26e1a7e07b5b37a00000000000000c7533f68b8a1f87b82e8a49e21facbb80003450e166cd205e000000097109d84ae2920041af1c8b0ae743f1d0ec20b1124c610000ac6c000bdfc9a05bc09e49c7a57c6db19da31a932d789355a296a09600032a865eb23e5f4a0bc71b800024f17ca78631940001b2b00033d40003044195b36848241be000000089e5c623b26a1a0668000ca900002866fe0960ace00001e47075c00000000000dc00002fc9a6a44f40b66900a8abb21bd4d272ade000169a8528cf835db17c3ebdce09d000009561e543798f7a158ae9100000009de00003a5199a2ce2ec6cc3246013a284e44a563f71733c83648080ba00000000241600029c788982e0641190082fa92a72991d90002d20a0b800025f90e8c08944a11e34a0000165ed66108aa9ec0005cb5e42aa81ba300000005a00000ca3b43cb571d56c259830bd12b3cbe081501301b9cc1313f64afa82035580005fe206869d85daa83a58c062b3dcaf79efb87d0000d00b058000091f7e200007ba008c288d220b9fac473cfd09e5590a8e2e516f80000000c6a80000000000ccd8d0e0000a1000011800000000afa1d54c348031a7daa360000a829a1a2663178b2c90fabe64f61dd8808c8c424a8580000141d0e6229819f633259f154065e03e82081c4a21612387570e5f036806719aa8a6c72a2a623bc98e00022a41ce000013180007b349fe0000000cf924fa6c71e384eaa1ea006b5e5d4926186b90f6478cb49233212c00898058535ad3fce2ac16a5d826a966b33e27b0f76d2a1ef243d815610897255f7af6cd80819485008166dee1421431a2d8f31c3c69ff55c78c000086f86363fe5b8a60928feb0a273a00035b648640009c58000400b40a0001c120001f185b69f101503352aa315f00000fb504100000002069bf500000000059ae6b5ed637800040107f02b80000aa135a7d3c25d65d99a9c7819976c3a00000000000b709b146689feeb1d8000d7a5ff00afe27a06f000034a51ed000194867206ecbcc00003f0a70e63992c1a84312e266a8d68e3259cc17000041d178408e0ef400000000000f8289e2ed80000d5c9f6afc6448f29092580000001266d71358982b747a403926c0000000cbe00000000b4c3d135947f686dc3f7c00018233bc0002f4a43590d200030d87ca18c03501902a9905d2d4c80007bd5c7e7d01712a4205e2281a85200519d239a09aa37c31d86c5ad5aa21915eb4e213c3e633167d288da45813c0c0783663ed2c8822c0e226ba0000c6b33a4
  | 59 => 0x2a24a440c458000d61d1749220f8d4b3d0e0124142a45da2342ed9efc00b315033016a8197a74a35a1b60000067e84e80004dfa7fa96a8000a31b1983faaa2c02e1ec81a24210157146a63428d8b08d39e0000a189ff40000001fc758fad7080e8000bf0800099816c26e78000bcb07da0b7288a0001b17c5007d072380002fe8000000271a4dd94520000ef053d914a0002449261a01e5ca8054a4b01b055b1c567b180000000881000206c7fa30940000ded3eda54a7a508e8d330fd2c270000b46abf49111e9201f803d4c32f5c5d19ac035a87aa8070000d68c1da185254e978b1d757608a848387c20001f2e730b554c8a1a264fb12e054a13fc9738f6a69f09e02d89b67d6e0d52884a04486a9b3215a07b8ca203beac707a93972c3a69686b8d7523a2aaa2ac6c3aaa4238d501213493ea3001de49591bea97fd4e9cb39c4893d193460001e227cad72cd724d8ccd2dd444b4b7413399182bb083a4562e1c45c193612a168dcb784724e91892306073498d12a613113405bf26800cbb5f98bd29c0be5aad266d8f18297878a072efa22e406d06db8b207f01b128b5061c0c1978703409bc0938f1a678b55d7018000a63a7be824a9e25ad81880ad800072714982950000646b196325156668c09446fda8a08308cd071d81780001adbb640000b619e648cfad969ec333c796ab9400010de8940c1e0001bd8974a7b6bbf90ba8630fcc0000000582000000021b87a39885030924a86caff2c551d2600000005af8000b6780001408000b861e078f1800000025d8d5e9054227b3fe1f48a904cc3191cba0eda359b36e842af2283b1ccc388322e8651dc0c5f8fde8eb0c8abf9b5291741832bd2175071019566e032c23248888789c096900ab881b3b06a858b5dad714d3ab96a197919a498a431d949b104da891210c1e795307d5848630a1c9aad0873c449a59e552e868d1a0d5867080dbd62b17677db2cc00000e51090df164c0dfe01c28ea00033190001e00b031298142800020d0f14c08c000b1a99c00cd9728c638c12bee80004b5300a0780bc4000000071104cc2caaf7878117c2cae9ad2120a1760d380003ba00004160000230a100a2705f40000b1024a000084ca87486ba19a00018f456000000000c9a6b72bd4ad233b4207a95c0002a8900000007f8108b48b958a7a11321d3c9aa458a2d947dba4a4000012e473691400002d23fc8dc4c2d90721458fed7388ab68e52dc8d7b93337cc0ec8bd0830e1d31f524c6904084429521de92b400da6aa08a9b1d000235418b2990b33256a0000cbc337ab961ed9a826360c560971ea47fe00002f932a0508e87e8600e28d5ee51c620a14e67aa15008f2a74be4a17200e530e76040f285821900000c5a36c8d2a000000072c243c0002c100001071b951258032133e4a8a4f889fc236475
  | 60 => 0x6b28322c21122bb52943ac9592fa7b987fe0a38000000250a000000035c31a7000296246bb5eb2030000000000013ea00c1da2a3a00034fcb6d894a8020000d5be4da30826e69b50dec2660000c30967a0001f38b5780d30a0172c07e13802e10bd40002c642881660000000004680000002ead000000072523f655500000cc108cacb00008fb0846ae7857ed57c000000000061c92ba8ab1a12acb80000002ebe00011de00033ce17991e800017e6000248221c161609742ca912a7244be1f1caa75e4519fec705bfa230cc4e052615b038260a7aa00aa10604980004650b160002b9019b00007de8652d0b0a00997400095680000002c6e8348000a8a0b7765700003ee80001b80dcaa81013e1c90000a9aa791bcea8dac4e2a46842d42ed6c5f0981f80000001e1c989eb3011319fe6ff280a4018f4e26a21487d89b22286906a68232121aa844846fdc902410f37722809a30b9e269f11c265c00f3114e110a8e907187938000136190a95880000002fb074c98dc4189caed7a349842e01a40000afa28b80005eda9285344000aa3a5c659c2ab2165df8c033a8bc5b60fc6c0416a03259dd2b09b376532a309268aeea45320c13b3000043eaa0834810c62b68aead7b05141f026236e2247a6579e3a6161bedb79303c02b9de64f4800000013d4346e7c87322472502a1f21f30c24656abb6801f002cbc0fa408497d8414949e000145a8290ae268ead4825180b42bf8000c4f8000cc94000bdd800044c8d744c8847c8f40000000000000018226e82be41b7ae4e3ec340467585109fda2843ea9f5819e00002a70666c8288e63bceda2758124c60229de78463da6ed9a5246e9da6a8f2795d311624a19a792c7909fa6290e700002ffa00006007b7a78182dc8f8186b5994bbb5dd5dc800000000002fb1f6a290abda51f85066ffad0a29e8f2f5a9ae4acf5a850c780d0011501189e5cfbf74f90e22ec354693cab1d1929ddc000344a00000000002df0545685c550a806aee88f05a2137429f02bea9f16ca5b4c6968d204466ed4e3a1f911043988616b4ed8c8560af1d0f58124a5621c25059c84a288000a66808ece010260000228148800096a3042b778000a4f0484829a010000171896daf35c528312a4e00c40a25faf4f3870e00012490001e4c0001f741bf51b46358ba673a91dad658852b1f088604147b40002cbc04b2e8e463361743699649612860485e2f6b0f9108681b1b000000003b894de00035c8d584686843a98b1762acc623ae5847d00009be2d6a97a1208383ae847bf542d80503c82120712b4da3e05439f983ab8a1d68310ac16706711b61b087bc1e194ffae168391cc6cd39b1003c220c34d068b36500000001ee798c400000000001ebc0000001b76a20b0527d12c4e788a4c4aeaf0bab12a2da00000000000d3
  | 61 => 0x7e92dbabeb9916767902e0eb1e7915bb02fb5031c4a780ceec300000a8e19a867f1f9286b332c0f00ea6d61175c00012c829e00004178222ce0a8c2c2a058c7541a140954cce9f599ca7c3279a00005e476d000042da097000000000026260000000000198c6d993c400000000003144000327e83551b231486c6bba171028e14826f5a3106b4218e64755fc1d64000818819600
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xcad7498b210400199ce73164208003335ce62c8410006373aac59082000c6d7558b210400195ce8b1642080032b5d162c84100066739ac59082000ccd7358b21040018ed0abb642080031d61576c84100065b422ed9082000cb5845db21040019ad06bb642080033560d76c841000673412ed908202cce5825db21040599ce40bb642080b33948176c84100063abb4eb9082000c75765d7210400196aed3a642080034d9d674c84100065abb2e99082000cd5769cf2104001aaceb39e4208003659d273c84100066abb2e79082000e667558b2104001ccaeab164208003a99d162c841000752ba2c59082000ec67358b2104001d8ae6b1642080b339dc162c841016672b82c5908200287e85dda21040010fb0bbb442080062fa1376884100045ec26ed10820068de83dda21040011bb07bb442080ae3da0776884100143f42aed10820018be845da21040010ff0cbac42080030f99175884100043fc3acb108200087d87596210400187ce8b2c42080022fe1974884100061f32ae91082000c3d655d2210400117f0eb2442080022f61d64884100061f3aac91082000c3d7559221040011bb0d39c42080031799673884100062eb2ce71082000c9e649ce210400193ac939c420800237e1973884100062f32ae71082000c5d655ce210400193cc8b9c42080032759173884100346fc3cc710820008dd8798e21040018bceb31c4208003175d663884100064f3a4c71082000c9d7498e21040011bf0eb1c42080023761d63884100062f3aac71082000c5d7558e210400193ce8b1c4208003275d16388410006373acc51082000c6d7598a210400195ce931442080032b5d262884100066739cc51082000ccd7398a21040018dceab1442080031b5d56288410006573a2c51082000cad7458a210400199ce6b144208003335cd628841000674b12e110820038ec82dd921040591ed0f30a420800e3b609760841034572c0ac41082000ce77648421040019caec908420815799995210841000732b2a421082054ea6644842104001d4ac89084208003b198d210841000762b1a421082000cea625c021040575cb04bb042080af39609760841015e73102ec108202bce4205d821040015cb0d3904208003395da72084101647bc3ac4108202cce67258821040015cf0eb1042080b339e1d620841015d73402c4108202bae48058821040579cee0b1042080af395c16208410006f1392e01082000c7b85dd910040018f10bbb220080032ee1376440100065c426ec8802000cdb83dd910040019b107bb220080033ae0b764401000674416ec8802000c7b76dd510040018f6ec3aa20080032eddb74440100065dbb0e88802000cdb76dcd10040019b6ec39a20080033addb724401000675bb0e48802000dc8731c91004057bc6e2392200800e3ea1e6144010
  | 1 => 0xac438a840800e3be1d62cc8100347ac34e39902000c75659c7320400196ac938e64080033958a71cc8100063ab2ae39902000cb5645c7320400d9acc6b8e64080033958971cc81001c6fc3ac719020038ed8798a32040050f90bbb264080062f213764c8100043fc2aec990200287c855d9320400117f08bb264080062f211764c81001c7c402ec990200087d86dd5320400187cc9baa64081671798f754c8100043f43aca990200087c875953204001878e8b2a64080022f61b744c8100061f32ee89902000c3d65dd132040a793cc7ba264080022fa1d644c8100045e43ac89902000c3f755913204001878eab22640800e3721d634c8100062fbaac69902000c5c7558d320400193ee8b1a6408003271d1634c81000637bacc49902000c6c75989320400195ee931264080032b1d2624c81001c7643ac49902000c6f7558932040018d8eab1264080032bdd1624c810006563a2c49902000cd563dc532040019cac5b8a64080023d618714c81000672b10e29902000cd963dc132040019d2c5b82640800e3b61e620c8100043fc2ae7308200287c855ce610400117f08b9cc2080062f21173984100071ba8ac92882000e575158e5104001ccea2b14a2080031e59570944100065cb22e12082004ab4815914104001d2882b1a8208003a910562504100066cb1ae1188200287c85dd9310400317909bb2620800e3720f764c4101043ec36ea9882000c3e64dd531040b18bcc7baa62080021fa1d654c41002c3e43aca9882000c3c74595310403f17b0dba262080030f997744c4100061eb2ee89882052c9e63dd1310400117d0eb2262080122f21d644c4100061fbaac89882000c3c7559131040018beeab1a6208003171d5634c4100064fba2c69882000c9c7458d31040018deeb31262080031b1d6624c41000657ba4c49882000cac7498931040018deeab1262080031b1d5624c41000657ba2c49882000cac7458931040071bb06bb06208003355d9310c4100072ab2a621882000e95644c43104001d8ac4988620801b3698d700c4100143f42aed90820018be845db210405d0ff0cbae42080030f99175c841002c3fc3acb908200087d87597210400187ce8b2e42080b62fe1974c84100061f32ae99082000c3d655d3210400917f0eb2642080022f61d64c84100061f3aac99082000c3d7559321040018bccb39e42080031759673c84100064f324e79082000c9d649cf21040018bccab9e42080031759573c84100064f322e79082000c9d645cf210400d1bf0f31e42080023761e63c84100062f3acc79082000c5d7598f210400193ce931e4208003275d263c84100046fc3ac790820008dd8758f21040018bceab1e4208003175d563c84100064f3a2c79082000c9d7458f21040018dceb31642080031b5d662c8410006573a4c59082000
  | 2 => 0x87154c1001c5fc3ac9218200287c85dd9430400193887bb286080021fe157650c100143e42aeca182000c9c435d943040010fb0dbaa86080f30f9937550c1031e2f31eeaa18200087e8759543040010f90eb2a86080038710d6550c1001c5e43ac8a182000c3f755914304001878eab22860801aa720d6450c1001c6e43ac6a182000c5f7558d43040018b8eab1a8608006a72116350c100065ab26e2a182000cd563dc543040011eb0c38a86080021fe1573988100143e42ae731020008bf845ce620400317908b9cc408002aba13529881000556c26a531020038ed8714a62040014dd0ba14c4080029b617429881001c76c38853102000aae849d6620400155b093acc4080029ba16749881000536c2ce93102000e2f54952620400159f06aa4c408002b320d549881000716aa0a93102000a6f855ce62040014d90ab9cc408002abe11739881000556422e73102000e4f5394e620400155f08a9cc408002ab211539881000557420a73102000aad8414e62040014df0aa1cc4080029b215439881000537428873102000a6d8510e6204001d1a8621cc4080029ba16719881000536c2ce33102000aae849c6620400155b0938cc408002b3a0e719881000566c1ce33102000aae84d46620400155b09a8cc4080029ba17419881000536c2e8331020038ee87d49620400155d09a92c408002ab61352588100057340ea4b1020038ee87d0962040014dd0ba12c4080029b61742588100057340e84b102000aae849d5620400155b093aac408002b9a06755881000572c0ceab102000ae4815d562040014dd0b3a2c4080029b61674588100057340ce8b102000ae5819d162040015c902ba2c4080038bd52545881000567c1aa8b102000acc8355162040015cf02aa2c408002b9205545881000716aa0a8b102000ae6819cd62040014df0ab9ac4080029b215735881000557c22e6b102000aac845cd62040015c902b9ac40800eba201735881000727a9ca6b102000aaf8454d620400155908a9ac408002b9e0553588100057240aa6b102000aae8414d620400155b0829ac4080029be1543588100053642a86b102000ae78150d62040015c902a1ac4080029ba14435881000536c2886b102000e8d4310d62040014dd0b38ac4080029b616715881000557424e2b102000aad849c5620400159d0738ac408002b360e715881015e73380e2b10202bce4701c5620400155d09a8ac408002ab61351588100053742e82b102000a6d85d0562040070ff0eb2ca40800e3b61e629481001c3e42eeca9020038ec8758952040018eacbb8aa4080033958b71548100047ac30e2a902000ce5621c5520400717f0eb24840800e3b61e629081001c5e426eca1020038bc8759142040071d90eb1284080032d593715081000672b16e2a1020008f5861c542040019c
  | 3 => 0x8b282000a5c835d165040014e902ba2ca080030f5d074594100062fb9ce6b282000a3f845cd650400147908b9aca080029d20573594100051f420e6b282000a3d841cd65040010fd0e21aca080021f61c43594100051f426e4b282000a3d84dc965040014e902b92ca080021fa1f42594100043ec3e84b28200587e87d0565040010fb0fa0aca0800e2fa1f54590100061fbaea8b20200287e85dc964040010fb0bb92c8080030fdd675590100054fc1aeab202000a9c835d5640400156902baac8080030f5d475590100051fc2ae6b202000a3c855cd640400156902b9ac8080028fa1473590100051ec28e6b202000c9d731cd640400117d0e29ac8080022f61c53590100051f42ee4b202000a3d85dc9640400156902b92c8080022fa1f52590100045ec3ea4b2020048be87d45640400117b0fa8ac8080030f15376550100061e2a2ecaa020008df835d9540400d1b906bb2a80800e1f21d655501000d1e422caaa020038bc8759154040054790ab22a8080023761b735501033e2f32ee6aa02000c5d65dcd54040c593cc9b9aa8080032759373550100046ec30e6aa02065c5e651cd54040018baca39aa8081832799073550100064eb20e6aa02069d1c541cd54040018eacbb8aa8080032d59371550100047ac30e2aa02000e1f5495263040011bf0eaa4c60801a3721d5498c100070eaa0a93182000a9e84d4a630400153b09a94c60800297a174298c100052ec2e853182000a9e84d46630400153b09a8cc60800297a174198c100052ec2e8331820038de87d4d63040018beeba9ac608002a7a105358c100054ec20a6b1820038de87d0d63040014bd0a21ac608002976144358c100062fbaceab182000a9f845d5630400153908baac608002b52057558c100054f420eab182000a9d841d563040014bf0aba2c608002972157458c100056a40ae8b182000a5e851d163040014bb0a3a2c608003275d07458c100070faa4a8b1820008df8755163040011b90eaa2c608003875505458c100052fc2ae4b182000a5c855c9630400153f08b92c608002a72117258c100056a40ae4b182003ad8805c9630400153d09a92c608002a76135258c100056b40ea4b182000ad581d4963040014bd0ba12c608002976174258c100056b40e84b182000ad581d09630400153d09a8ac608002a76135158c100052f42e82b182000a5d85d0563040018bea6bb4a60800e1fe1d6594c100052fc1acb2982000e1f5359253040054bd0ab1ca6080062f2137654c100045fc22eca9820018bc845d953040070f90eb2aa6080030f1d16554c100045ec36e8a98202ac3e65dd1530400187acbba2a60819b2798f7454c100045f43ac8a9820008bc8759153040071b90eb1aa60800327dd16354c100064e3a2c6a982000c7565dc553040019aac7b8aa6080023d61
  | 4 => 0x144001ca8ca31c4288003a51906388510006733b6c510a202bce67618a2144001cceca314428800399194628851000753b20c510a2000ea46418a2144001d8ec63144288003b118c6288510007333a8c510a2000e657518a2144001d4ce83144288003a95d0628851000763398c510a2000ec57318a21440579cce031442880af391c062885102166c380c690a2041ce870d8921440019b0c7b82428811f1d1db65485102363a3b0ca90a2045cb476d912144089968ec32242880038d194644851021e6a3b6c690a2042cd47618d2144001ca8ca31a4288003a5190634851000573436e490a2041ce476d8921440011ed0e312428800399d94624851000732328c490a2000ea7641892144001d48c83124288003b1d8c624851000762318c490a2000ae68718921440019cd0e312428810778dc8704851015c7b434e210a2000e676548421440abcc8ca9084288003a9d9121085102a7523224210a2000ec7634842144001d88c690842880031dd9771541100065a326e2a822000cd463dc550440019c8c5b8aa0880031dd9471541100065a320e2a822000cd4631c550440019c8c438aa0880031d19771501100066a31ee2a022000ce462dc540440018e8ca38a80880032dd9071501100066a318e2a022000ce4621c5404400d9a8c738e60880033918a71cc1100366a31ae39822000ce4625c730440010ff0abb2608800a1f215764c1100045fc22ec98220018bc845d930440011df04bb260880031d197714c1100065a326e29822000ce462dc530440018e8ca38a60880032d190714c1100066bb18e29822000ce4621c530440571ed0d38e40880033918a71c811000672312e39022003ae486487204400117f08bb240880062f21176481100046fc1aec90220068dc835d92044003179083b240880022fa1b74481100061fb2ee89022000c3c65dd1204400117d0fb2240880022f21f64481100061fbaec89022000c3c75d9120440011bd0fb1a40880023721f63481100062fbaec69022000c5c75d8d204400193ee9b1a4088003271d363481100046f438c690220068dc8718d20440018beea31a4088003171d463481100064fba0c69022000c9c7418d20440018eecbb8a40880031d19771481100065bb26e29022000cb464dc520440019aec7b8a40880033518f71481100063bb28e29022000c74651c5204400196ec838a40880032d19071481100066bb18e29022000cd4631c520440019cec438a40880af39188714811001d72432429022000ce47648520440077c10090a408811f1e9db65c41100163d3b0cb8822045cba76d931044003974ec326208810f369db63c41100366d3b0c78822041cea76d8b1044001d90c6316208800e1fa1e54594100061fba4a8b2820018be84dc9650400117b09b92ca080030fdd274594100052fc1ae
  | 5 => 0x80030fd97744c5100061e32ee898a2052c9c63dd131440ad17d0fb2262881162f21f644c5100061fbaec898a2000c3c75d9131440018beebb1a6288003171d7634c5100064fba6c698a2000c9c74d8d31440879b0e1b1a62880031bdd7624c510006363aec498a2000caf74d893144001958e9b1262880031bdd4624c510006363a8c498a2000caf741893144001958e831262880af3a1c0624c51000674316e098a204687c865d72144001878c8bae428811e1fe1f65c85100043ec3ecb90a2000c3e74d9721440891790cba642880030fd9574c85100061e32ae990a20458bf87d93214400117b0fb2642880030f9d764c85100061ebaec990a20438de869cf21440018becb39e42880031719673c85100064fb24e790a2000c9c649cf21440851b90cb9e428800317d9573c85100062e32ae790a2000c9f645cf2144001938c8b9e428810e37e1f63c85100046ec3ec790a2000c5e75d8f21440018baebb1e4288003279d363c85100064eba6c790a20068df8718f21440011bb0e31e4288003179d463c85100062eba8c790a2000c9e7418f214400193ae831e42880031b9d762c851000636baec590a2000cae74d8b214400195ae9b164288003339cf62c851000666b9ec590a2000c6e7518b21440018daea31642880032b9d062c851000656ba0c590a2000cce7318b214400199ae631642880af3a9c062c85100143e42ced10a20018bc849da21440390f90cbac42880030f19175885100043fc3ecb10a200887d87d96214400187ce9b2c428806e2f21974885100061fb2ae910a2000c3c655d2214400117f0fb24428801e2f61f64885100061f3aec910a2000c3d75d9221440018becb39c42880031719673885100064fb24e710a2000c9c649ce21440018becab9c42880031719573885100064fb22e710a2000c9c645ce21440011bf0fb1c42880023761f63885100062f3aec710a2000c5d75d8e214400193ce9b1c4288003275d363885100346fc38c710a20008dd8718e21440018bcea31c4288003175d463885100064f3a0c710a2000c9d7418e21440018dcebb1442880031b5d76288510006573a6c510a2000cad74d8a214400199ce7b144288003335cf6288510006373a8c510a2000c6d7518a214400195ce831442880032b5d0628851000667398c510a2000ccd7318a21440018ef0b3b442880031d21676885100065bc24ed10a2000cb4849da21440019af073b442880033520e768851015e73c14ed10a202bce6209da21440579c8413b442880031d9da75885100063b3b2eb10a2000c7676d9621440018ecec32c42880032d9da74885100065b3b2e910a2000cb676d92214400196cec32442880038d19464885100066b3b4e710a2000cd6765ce2144001aaaeab9c4288003655d173885100066b3b6c710a2000cd67618e2
  | 6 => 0x557c22e03122000aac845c0624400159f06b80c488002b320d70189100057340ea03122000ae581d4062440015cd03a00c488002b9607401891000537c2a203122000a6c85440624400155f08880c488002ab211101891000567c1a203122000acc83440624400317d09bb4a4880022f61376949100346f41eed29220008dd83dda524400117f08bb4a4880062f21176949100046fc1aed29220068dc835da52440051db0e314a4880031dd9671949100065a324e32922000cd4639c652440019c8c538ca4880031dd9571949100065a322e32922000cd4635c652440019c8c4b8ca4880062fa1376549100045ec26eca9220068de83dd952440011bb07bb2a48800a3ba1f62549100143f42eed212200087d85dda424400d1bd07bb484880023760f76909100043fc2aed212200287c855da42440011bf06bb4848801a3720d769091000c76c38c52122000c74659c6424400196ec938c84880033518e719091000672314e32122000c74655c642440019a8c6b8c84880033918971909100143f42eeca12200087d85dd9424400d1bd07bb284880023760f76509100043fc2aeca12200287c855d942440011bf06bb2848801a3720d765091000477c12eca1220008f7815d942440031dd0fb1284880021fe1576cc9100143e42aed99220008bf845db324400317908bb6648800a1fa17768c9100043ec2eed19220018be84dda324400117b09bb464880021fe15768c9100143e42aed19220008bf845da324400317908bb464880031d196718c9100065a324e31922000cd7639c632440019c8c538c64880031d195718c9100065a322e31922000ce4625c632440050fd0bbb264880021f617764c91000c5f426ec99220008bd84dd932440050fd0b3b264880021f616764c91000c5f424ec99220008bd849d9324400117f08bb264880062f211764c9100047dc02ec992200287c851d93244003179083b264880021fa1b754c9100061e326ea9922059c5c63dd532440010fd0fb2a64880021f21f654c9100061e3a6ca99220008be86dd1324400187ecbba264880030f197744c91029e4e31ee899220008be87d9132440011790fb2264880030fdd7644c9100061e3aec89922000c5f75d8d32440018b8ebb1a648800327dd3634c9100064e3a6c699220068ee87d8932440018deebb1264880031b1d7624c91000657ba6c49922000cac74d8932440018deea31264880031b1d4624c91000657ba0c49922000cac7418932440010ff0abb0648800a1f215760c9100045fc22ec19220018bc845d8324400d9a8c738864880033918a710c9100366a31ae21922000ce4625c4324408f8f0e1b2aa2881172e1c364505102343f436ea98a2000c3c64dd531440b18b8c7baa628815e1fa1f654c51023c3e43eca98a2000c3c74d95314408917d0dba2628
  | 7 => 0x9c74dcd624400193ee839ac488003271d073589100063bbaee2b122000c7475dc5624400196ee9b8ac4880032d1d371589100066bb9ee2b122000cd473dc562440019b0e7b82c4880023be1d621891000537c2ac43122000a6c85588624400155f08b10c488002ab211621891000567c1ac43122000acc8358862440010ff0ab98c48800a1f21573189100045fc22e631220018bc845cc62440014dd0b390c4880029b616721891000557424e43122000aad849c8624400159d07390c488002b360e721891000557426a43122000aad84d4862440015cb02290c4880029ba17421891000536c2e843122000ae58110862440018dcedb28c4881bf99843651891037f32086ca31220008ed87994624400155d09328c488002ab61265189100056741cca3122000acd8399462440011df0eb28c488002abe11651891000556422ca3122000acf83594624400159906b28c4880031b9d8651891037733080ca312206ee6410194624400195cedb20c4880038bd9764189100071632ec8312206dea610d9062440dbd4821b20c4880023b61e64189100053742cc83122000a6d85990624400159d07320c488002b360e641891000477c3ac83122000a6f8559062440014d90ab20c488002b3e0d64189100056641ac83122000cae761906244001c5eca320c4880038b194641891036753080c8312206cea410190624400199cedb18c48800393d9763189100072632ec63122000e8f64d8c6244001d18c9b18c4881afb1843631891035f62086c631220008ed8798c62440014dd0b318c4880029b616631891000557424c63122000aad8498c62440011df0eb18c4880029be1563189100053642ac63122000aaf8458c624400155908b18c488003339d8631891000727b28c63122000e4c6518c6244001d1ec8318c488003a3190631891035763080c6312206aec41018c6244001ccecab88c48800399195711891000753b22e23122000ea4645c46244001d8ec6b88c488003b118d711891015d72c0eea3122000aae849d4624400155b093a8c488002b9a04751891015d72c08ea312202bae581dd062440014dd0b3a0c4880029b616741891000573408e8312202bae5811d06244001c5ea92a0c488002b3e0d54189100056641aa83122000e2d5415062440575cb03b98c4880029be1573189100053642ae63122000aaf845cc624400155908b98c4880aeb9604731891000727a9ca63122000aaf8454c624400155908a98c488002aba10531891000556c20a63122000ae68114c62440015cb02298c4880029be1543189100053642a863122000a6e8510c62440014db0a218c488003a350c431891000573408863122000ae58110c624400155d09a88c488002ab61351189100053742e823122000a6d85d0462440014df0ab80c4880029b21570189100
  | 8 => 0xb326c488002b3a0e64d891000566c1cc9b122000a6f8559362440014d90ab26c488002b3e0d64d89100056641ac9b122000e2f651936244001c58ca326c48800393d9763d89100072632ec7b122000e8f64d8f6244001d18c9b1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec48800393d9463d891000726328c7b122000e8f6418f6244001d18c831ec488002aba1075d891000556c20ebb122000a6e851d362440014db0a3a6c4880038bd5254d891000567c1aa9b122000acc835536244001c5aa82a6c4880029ba1773d891000536c2ee7b122000aae84dcf624400155b09b9ec48800393d4e53d891000557c22a7b122000aac8454f624400155d0829ec488002ab61053d891000537c2a87b122000a6c8550f62440014dd0a21ec4880029b61443d891000746a1887b122000a6f855c762440014d90ab8ec488002abe1171d891000556422e3b122000acf835c7624400159906b8ec488002aba1351d891000556c26a3b122000a6e85d0762440014db0ba0ec4880029ba1770d891000536c2ee1b122000aae84dc3624400155b09b86c488002b3a0f70d891000566c1ee1b122000c3e74d96624400187ce832cc4880030fd9574989100061e32ae93122000c3e75d92624400187aebb24c4880030f9d464989100061eba8c93122000c5f659ce62440018b8cb39cc48800327d9273989100064e324e73122000c5f655ce62440018b8cab9cc48800327d9173989100064e322e73122000c5e75d8e62440018baebb1cc488003279d363989100064eba6c73122000c5e7518e62440018baea31cc488003279d063989100064eba0c73122000c6e75d8a62440018daebb14c4880032b9d3629891000656ba6c53122000cce73d8a624400199ae7b14c4880030f9d674989100061ebace93122000c3e755d2624400187aeaba4c488003179d673989100062ebace73122000c9e749ce624400193ae939cc488003179d573989100062ebaae73122000c9e745ce624400193ae8b9cc4880021fa1f65589100061e3a6cab12200087e871956244001878e832ac4880030fd9774589100061e32ee8b1220008be87d91624400187eebb22c4880030f1d764589100045f438c8b122000c3f751916244001878ea322c48800317d9773589100062e32ee6b122000c9f64dcd6244001938c9b9ac48800317d9473589100062e328e6b122000c9f641cd6244001938c839ac48800237a1f63589100062fbaec6b122000c5c75d8d624400193ee9b1ac488003271d363589100046f438c6b122000c5f7518d62440018b8ea31ac48800327dd063589100064e3a0c6b122000c3f75dd1624400187eea3a2c4880030f1d474589100064fba6e6b122000c
  | 9 => 0x7158d1000674396e0b1a20008df8758c63440014bf0ab18c688002972156318d100054fc22c631a2000a9c8458c634400159f04b18c688002b32096318d100062f3b6ca31a20008dd87994634400153d09328c688002a76126518d1000567414ca31a2000acd8299463440011bf0eb28c688002a7e116518d100054e422ca31a2000acf82594634400159904b28c688003179d86518d1038f2b080ca31a2071e5410194634400193cedb20c68800387d976418d100070e32ec831a20008dd8799063440014bd0b320c688002976166418d1000567414c831a2000acd8299063440011bf0eb20c68800297e156418d100052e42ac831a2000acf82590634400159904b20c688003279d86418d100070fb28c831a2000e1c6519063440e1d2c20320c6881c3a50406418d100070faa4a831a20008df87550634400d1b90eaa0c688003875505418d100054f426a431a2000a9d84d4863440014bd0ba10c688002976174218d100054f426a231a2000a9d84d4463440014bd0ba08c688002976174118d100052fc2a2031a2000a5c85440634400153f08880c688002a72111018d100062fa9ced29a20008bf845da534400317908bb4a68801a3720d7694d1000477c12ed29a20008ec825da53440014bb07b2ca68800387d4f6494d100152e42ec729a20018be84dd9534400117b09bb2a6880023ba0b7654d1000476c16eca9a20018be849d9534400117b093b2a6880022fe117654d1000c5e422eca9a20008df835d953440011df04bb2a6880023b2097654d100047bc0aeca9a20018bc841d9534400d0fd0fb2aa6880030f1d36554d100045f436e8a9a2000c3f65dd15344055878cbba2a68819b2718f7454d100045f43ec8a9a20008bc87d9153440051bd0fb1aa68800327dd36354d100064e3a6c6a9a200087f855da43440050f90abb4868801a3720d7690d1000477c12ed21a20008ec825da43440050fd0bbb286880021f6177650d1000477416eca1a20008ed82dd943440050fd0b3b286880021f6167650d100064e21ceca1a200087f855d943440050f90abb2868800237e0d7650d1000477c12eca1a20008ec825d943440011ef02bb2868800a1f2147650d100064e218eca1a200087e86dd54344079878c9baa868818f1718f7550d100043f43ecaa1a200087c87d954344001c3887b2a868801a2fa1f6450d100061fbaec8a1a2000c3c75d91434400d53d07b22868800637a1f6350d100062fbaec6a1a2000c5c75d8d434400353d09b1a8688002aba1352d891000556c26a5b122000a6e85d0b62440014db0ba16c488002aba1265d891000556c24cbb122000ace83997624400159b0732ec488002abe1165d891000556422cbb122000acf83597624400159906b2ec4880038bd9764d89100071632ec9b122000a6e8599362440014db
  | 10 => 0xaa220068dc835d954440011df04bb2a8880023b20976551100047bc0aecaa22000c3c541d954440030fd0fb2aa8880068fa1365551100145f43ec8aa22002a3e85d9154440011bd0db9aa88800317d97735511033e2e32ee6aa22000c9f64dcd54440c5938c9b9aa88800237a1873551100062fb28e6aa22065c5c651cd544400193ec839aa8881832719073551103968e2a0e6aa22000c5d75d4f634400153d0829ec688002a761053d8d100052f42887b1a2000a5d8510f634400153d0932ec688002a761265d8d1000567414cbb1a2000acd82997634400153f08b2ec688002a721165d8d1000567c12cbb1a2000acc825976344001c3ecbb26c6880038719764d8d100052f42cc9b1a2000a5d85993634400159d05326c688002b360a64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100070fb28c9b1a2000e1c65193634400153d09baec688002a761375d8d100054f424ebb1a2000a9d849d763440018baea3aec68800297a1774d8d100052ec2ee9b1a2000a5e859d363440014bb0b3a6c68800327dd274d8d100070faa4a9b1a20008df8755363440011b90eaa6c6880038755054d8d100052f42ee5b1a2000a5d85dcb634400153d09b96c688002a761372d8d1021d6ac08e5b1a2000a9e84d4b634400153b09a96c68800297a1742d8d100052ec2e85b1a2000a9e84d47634400153b09a8ec68800297a1741d8d100052ec2e83b1a2006c5c635d6634400187ce9b2cc6880030f9d06598d100061fb2ae931a2000c3c655d2634400d938c6ba4c6880030f9d76498d100061ebaec931a2000c3e75192634400187aea324c688003179d76398d100062ebaec731a2000c9e74d8e634400193ae9b1cc6880031bd967298d100063632ce531a2000caf649ca6344001958c9394c68800333d8e7298d100366631ce531a2000c6f655ca63440018d8cab94c6880032bd917298d1000656322e531a2000ccf635ca634400d998c6b94c6880021fa1f6558d100061e3a6cab1a200087e871956344001878e832ac6880030fd977458d100061e32ee8b1a20008be87d91634400187eebb22c6880030f1d76458d100045f438c8b1a2000c3f751916344001878ea322c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880031bd947258d1000636328e4b1a2000caf641c96344001958c8392c6880030fdd77458d100061e3aee8b1a2000c3f751d16344001878ea3a2c68800317dd77358d100062e3aee6b1a2000c9f74dcd6344001938e9b9ac6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c68800333dcf7258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a2000c7475dc56344001968e9b8ac688003391cb
  | 11 => 0x440018bae639eca880021fa1c43d95100043ec3887b2a2000a3f845cb654400147908b96ca8811e9d60472d95100043f43e85b2a200087d87d0b654400147f08b8eca880028f21171d951023c3f43e83b2a200087d87d076544001878cbba2ca880031719773595100062e328e6b2a2000c6c65dc965440018d8ca392ca880062fa1f74595100061fbaee8b2a2000c3f751d1654400d1bd0fb9aca8800317dd773595100064fba6e6b2a2000c9c74dcd65440018beea39aca8800327dd073595100064e3a0e6b2a2000c6f75dc9654400195ee9b92ca880032b1d3725951000667b9ee4b2a2000ccc73dc965440018deea392ca880032bdd07259510006563a0e4b2a2000ccf731c96544001998e6392ca880032d1d371595100066a39ee2b2a2000ce472dc565440014bd07320ca880029760e641951000537414c832a2000a6d82990654400187aebaa6c8880021fe1572d91100143e42ae5b222000a9e83997644400153b0732ec888002aba0a65d911000556c14cbb222000a9f83597644400153906b2ec888002abe0965d911000556412cbb222000a9e83dd7644400153b07baec8880030fdd675d91100061eba8ebb222000a3e85dcf644400147b0bb9ec8880028fa1673d91100051ec2ce7b222000c9f739cf644400117d0e29ec8880022f61c53d91100051fc2ae5b222000a3c855cb644408b56b02396c8880022fa1f52d91100045ec3ea5b222000a3f855c764440014790ab8ec8881162fa1f51d91100045ec3ea3b222000c3c64dd564440010fd0fb2ac8880021fa1c65591100062fb2ee6b222000c5c65dcd6444001938c9b9ac88800317d9473591100062e328e6b222000c9c641cd64440018decbb92c8880031b197725911000656326e4b222000c6f651c964440018d8ca392c8880032b19072591100143f43eeab222000c3f75dd16444001878ebba2c88801a37a1f73591100062fbaee6b222000c5c75dcd644400193ee9b9ac88800317dd473591100062e3a8e6b222000c9f741cd64440018deebb92c8880031b1d7725911000657ba6e4b222000ccf73dc96444001998e7b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc72591100063a3aee2b222000cd473dc564440019c8e5b8ac8880030f9db65191100045ec3cca3222000a3e85994644400153d07328c888002a760e651911000557414ca3222000aad82994644400117f0eb28c888002a7e0d65191100054e41aca3222000aaf82594644400155904b28c8880028fa1865191100061f3b0ca3222073e361019464440e7c6820328c88801a37a0f76551100046ec1eecaa220008ee82dd954440011db05bb2a8880030f15276551100346f41cecaa220008dd839d954440010ff0abb2a8880022fe1176551100046fc1aec
  | 12 => 0x30f5d57498b100062f3ace73162000c5d759ce62c400193ce939cc588003275d27398b100062f3aae73162000c5d755ce62c400193ce8b9cc588003275d17398b1000477c3ac431620008bf845cc62c400317908b98c5880062fa137694b100045ec26ed29620068de83dda52c40011bb07bb4a5880062fa137654b100045ec26eca96200287e85dda42c40010fb0bbb4858801a37a0f7690b100046ec1eed2162000cb5649c642c40050fd0bbb285880021f6177650b1000557416c8a16200087f855db32c40050f90abb665880022fe1176ccb1000c5e422ed996200287e85dda32c40010fb0bbb465880062fa13768cb100045ec26ed1962000cd5639c632c40010ff0abb2658800a1f215764cb100045fc22ec99620018bc845d932c400159d05b1a658800237e1d630cb1001c3f43ecaa8e20038be87d9141c40011bf0eb186388003555d57388710006caba2e710e2000be180d8921c40011ed0e312438800279a1c624871000573438c490e2000ce68718921c4001dc30031243880af399c0624871015e72380c490e2000de1215c021c400196ac838a818810e37e1d63cc3100066ab18e2986202c8f7865c720c40011bf06bb2a90801a3720d765521000477c12ecaa420008ec825d954840070f90eb2aa9080068f211655521001c5e43ac8aa42002a3c8559154840cb8bcca39aa9080031759473552103064f320e6aa42000c9d641cd54840e9a38a839aa90800e1fe1d6594e100052fc1acb29c20008bf845d9538400317908bb2a7080023be097654e1000476412eca9c20038bf8759243840010ff0abb2870800a1f2157650e1000477c12eca1c20008ec825d943840010ff0ab9cc50800a1f2157398a100045fc22e731420018bc845ce62840050fd0fbaac5080062fa1f7458a100061fbaee8b142000c3c75dd1628400187eea3a2c5080030f1d47458a100062fbaee6b142000c5c75dcd628400193ee9b9ac508003271d37358a100062fba8e6b142000c5c751cd628400193ee839ac508003271d07358a100045fc22eca9420018bc845d952840011bf06bb2a50801a3720d7654a100043fc2aeca14200287c855d942840011bf06bb2850801a3720d7650a1000556412c8a1420488df8758f32840010ff0abb2650800a1f215764ca100045fc22ec99420018bc845d9328400159904b1a650810a37e1d63cc6100069b3ace990c2000d56759cf2184001b2ce939e43080ae3de1d62c8610006b8baae190c202bbe08048421840577c50139043080030f5d254d95100045fc22e5b2a20018bc845cb65440014bd07326ca880029760e64d951000537414c9b2a2000a6d8299365440014bd07ba6ca880029760f74d95100061fba4e9b2a2000c3d741d3654400147d09b9eca880028f61373d95100051f424e7b2a2000a3d849cf65
  | 13 => 0x55b426a3b0a6000a7685d07614c0011ef0eb08c2980029d21561185300055a422c230a6000ae482584614c00156d09a88c298002b560c51185300053b42e8230a6000ad583104614c0018becab9ca298003335c862cc5300063a3aec298a6000cb474d85314c0018e8ea30a62980032d1d0614c5300068e3a8e898a60488de86dc9314c0011bd0e312629800333dc8624c5300056b438c298a6000cd687185314c001caeea30a6298003951d4614c5300074bba0c298a6000e9474185314c0050fd0a3b442980021f614768853000c5f420ed10a60008bd841da214c00d1bd063b442980031b9d76288530006573a6c510a6000c6e7518a214c00195ce83144298003335cc628853001c6e432e690a60039d8805cd214c00117f08bb042980062f21176085300066ab98c210a6000ae582184214c0015cd0c9084298002b921921085303146fc1aecaa060068dc835d9540c0071790eb22a81800a8f21564550300364e39ac8aa0600287e859ca610c0010fb0b394c2180062fa1272984300045ec24e5308600287e87dd5610c0b18b8e7baac21815f171cc755843000c5f43ee8b086000c3f75dd1610c001878ebba2c21814b271cf74584300061fba8e8b086000c3c751d1610c0ad938e63a2c21800e3d61e61944300153a42ac328860008bf845d9510c00317908bb2a21800e3d21d615443001c7ac3cc32086001ab484586410c0010ff0abb2821800a1f21576504300364e39ac8a0860038f487585410c00199ce4b14621800a1fa1776884300043ec2eed10860018be84dda210c00117b09bb442180023760d76884300063abacc31086000cb574986210c0018eaeab0c42180032d5d161884300366b39ac310860008bf845d9210c00317908bb242180023761b734843000572412c290860008bf845d8210c00317908bb042180023761b730843000673bb2421086000ce576484210c0577c10090842180062fa1372597100045ec26e4b2e200287e85dc964c40010fb0bb92c98801a37a0e76553100046ec1cecaa620008ee829d954c40011db053b2a98800237e0d76553100346e41aecaa6200187e87d9554c400347d09b2aa98800a2fa1f64553100151f42ec8aa62000c5f651cd54c40cb8b8ca39aa98800327d9073553103064e320e6aa62075d1c541cd54c400187eebba2c7880030f1d77458f100061fba8e8b1e2000c3c751d163c40011bf0eb18c7880022fe117694f1000c5e422ed29e2000a5d83d9653c400317d093b2a7880022f6127654f1000477414eca9e20008ed829d953c400117f08bb2a7880062f2117654f100043fc2aed21e200287c855da43c40050fd0b3b287880021f6167650f1000477414eca1e20008ed829d943c40010ff0abb2878800a1f2157650f100061f3ace93162000c3d759d262c400187ceaba4c588
  | 14 => 0xd85dc9648c00153f06b92c9180032b5c872592300045f43ea4b2460008bd87d49648c00147d0bb8ac9180028f61771592300054fc1ae2b246000cb5711c5648c00117d0fa8ac9180022f61f51592300061e2a6ecaa46000c3c545d9548c0071790eb22a91800a8f21564552302664e39ac8aa46000c5d65dcd548c0c593cc9b9aa9180021f61b7550e301e61f326eaa1c603c87e87595438c0c10f90eb2a87181db8710d6550e300061fbaac8a1c6000c3c75591438c001972c9b82871800a1fa1672986300043ec2ce530c60018be849ca618c00117b09394c31800a1fa1772586300043ec2ee4b0c60018be84dc9618c00117b09b92c3180029de0565946303b62e39acaa8c6000c5d65dcd518c00193cc9b9aa31800e2f21376506302664e39ac8a0c6000ab481591418c0018bccbb9a83180023761a728c6300046fc3ac518c6000cce7258a318c0010fb0dbaa63180030f993754c6300043e43aca98c6000c3c74595318c0edca862b2a63180022f61b744c6300061f32ee898c6000c3d65dd1318c0011790eb2263180030fdd5644c6300061e3aac898c604ce9431591318c00199ce4b10631800a1fa1776886300043ec2eed10c60018be84dda218c00117b09bb4431800a1fa15768863000c5f422ed10c600087f865d6218c00187cc8bac43180021fe1d65886300043ec3acb10c6000c3e74596218c0ed8bce6b2c43180022fe1974886300061f32ae910c6000c3d655d2218c00117f0eb2443180022f61d64886300061f3aac910c6000c3d75592218c09993ce6b2443180031799573886300062eb2ae710c6000c9e645ce218c00193ac8b9c4318003355cd618863000572412c290c6000ce776484218c0019caec9084318153a9991210863000752b224210c6000c3d75d53644c0010ff0ab96c89800a1f21572d91300043fc2ae3b22600287c855c7644c001958c8392c8980032d19071591300143f43eeab226000c3c75dd1644c0018b8ebb9ac8980031bdd77259130006363aee4b226000c6f751c9644c0018d8ea392c8980032bdd0725913000667b98e4b226000cae541c9644c00195c86392c8980032b10c72591300063bbaee2b226000c7475dc5644c0019cee5b8ac898003391cb71591300063bba8e2b226000c74751c5644c00196ee838ac89800335dcc715913000673b90e2b226000ce4721c5644c00196ca838ac8980032d90c71591300065a218e2b226000c3c549d9544c00117f08bb2a89800237e0d76551300047bc0aecaa260008f4815d9544c001878a83b2a89801a3720c76551300145e43ac8aa26002a3c85591544c099938e6b22a898002ab20964551300055a40ac8aa260038de86dcd544c001878ebb22869801aa7a0f6450d300043fc2ae5b0a600287c855cb614c00117f08b96c2980062f21172d853000
  | 15 => 0x4b08c2a000b0f1d554185400054e41aa830a8000ab78155061500010ff0ab98c2a000a1f21573185400064e21ae630a80008bf87508615000156f02a10c2a0002ad61351185400055ac20a230a8000e3554144615000187ecaba4a2a00064fe1d54945400151e432a928a8000c3e76552515000163906aa4a2a000e2f2197550540264ce41aeaa0a804d8be86dc9415000127b0bb9282a00022fa1c625054000657b90c4a0a800b8be87185415001756d0e30a82a00032da1c61505400065a398c2a0a80038bd849db315000196ee830e62a000a1fa16764c5400043ec2cec98a80018bc841d931500010ff0abb062a000a1f215760c54000477c12ec18a80008ec825d8315000d938c6ba062a00032d5d0610c5400143f428ed90a800087d851db215000317d083b642a001a37a0c76c85400046ec18ed90a8000c7675d8721500019ace7b0e42a00031d9d461c85400065aba0c390a8000cd67318721500050fd0a3b442a00021f614768854000c5f420ed10a80068de831da21500011bb063b442a00031b9d762885400066739ec510a8000c6e7518a215000195ae831442a0003339cc628854001c5e432e890a80039b8805d121500010ff0abb042a000a1f21576085400046fc1aec10a80068dc835d8215000195ae831042a0002b960462085400065aba0c210a8000ae58218421500015cd0c90842a0002b921921085400061fb2ee8a828003a3c865515050003878ecaa2a0a0002c720d545414001d9c402a8a82800287e85dc964cc0010fb0bb92c99800a1fa1771593300043ec2ee2b2660038dc835d954cc00d1790eb22a99800a8f21564553300364e39ac8aa6600287e85dc961cc0010fb0bb92c3980062fa1372587300045ec26e4b0e60018be84dda51cc00117b09bb4a39800e37a0f769473000477416ed28e60008ed82dda51cc00d8bce6b2ca39800a1fa1776907300043ec2eed20e60038de83dda41cc0011dd05bb483980023b60b76907300364f39ac920e6000c5f76dd531cc0018beec3aa639800327ddb744c7300064fbb0e898e6000d1c751d131cc00199ee53126398002b5a06624c7300143f42eed10e600087d85dda21cc00317d09bb443980022f613768873001c6f41eed10e6006cce7398a21cc00d99ce6b14439800e37a0f764873001cec402e690e60038de83dd821cc0015cb053084398002b9e19210873000572c324210e602bbe08048421cc00d938e6b22819800e2fa1f54592300061fbaea8b24600287e85dc9648c0010fb0bb92c9180032b50872592300143f42ee2b24600087d85dc5648c00187eeb3aac918002a7e0d75592300061eba8eab246000a3f855cd648c0014790ab9ac918002abe09735923000556412e6b246000ab7815cd648c00156902b9ac9181338794f53592300051f42ee4b246000a3
  | 16 => 0x2906402245fc3ac320c8000a3f85586419000d93cc6ba663200021fe15764c6400143e42aec98c8052c9e63dd131900018b8eab1a6320002b5205634c6400143f42eed90c800087d85ddb219000d1bd07bb643200023760f76c864000656ba2c590c800287e85dda21900010fb0bbb4432001a37a0f76886400046ec1eed10c8000cb57458621900010ff0abb2432000a1f21576486400057240ac490c8000ae48258521900010ff0abb0432000a1f215760864000673bb24210c8000ce576484219000317908b96caa00062f21171d95400062e328e6b2a8000c6c651c965500018e8ca38acaa000327dd073595400066bb9ee2b2a8000cd473dc565500019cee5b8acaa00031ddd471595400065bba0e2b2a8000cd7731c565500019a8e638acaa000339dc8715954000672390e2b2a8002a3e86d95545009933d0fb9aa8a019f271db735514033f0e32ee6aa28065c9c761cd54500c1a3eea39aa8a01978719473551402664f430e6aa2804cc9d861cd5450099a3d0a39aa8a01334761473551400068fb28e6aa28065c9e651cd54500cb938ca39aa8a01e347194735514032e0e328e6aa28078d1c521cd54500f1a38a239aa8a017b27d807355140306cdb00e6aa28078d1f501cd545009b17d0db92a8a01122fa1b7155140006cc39ee0aa280658bf875536350005878eaaa6c6a0132a720d54d8d400062ebaea7b1a8000a9d84d4f6350001c3aa9a9ec6a0002a761053d8d403bf0f2a0a7b1a80008df8758c63500014b90ab18c6a0002b32096318d400056a40ac631a80038bd849da53500014bb07b2ca6a00062f2107654d4000c9e43aa8a9a8000c3c76551535009963906aa2a6a01362f2197290d400049fc2ae521a80448bc865c6435000127f0ab8c86a0002ab61352d89400043fc2ae3b12800287c855c762500011bf06b8ec4a001a3720d71d894000477c3ac43128000a6c85588625000159906b10c4a0002b920562189400161e3aaa83128000a9c83550625000155f04aa0c4a00021fe1573189400143e42ae63128000c9c435cc625000155b09a90c4a0002ab610521894000716aa0a43128000c3f655d2525000327f0eaa4a4a000a8f21954949400061f3b2a92928000b1c8355252500071790cbaa84a01326720d755094027557436c4a12803e8be87189425007d55d0e31284a00032ba1c625094000656398c4a1280448be86dc5425000127b0bb8a84a000e2f61276cc94000657ba0c5992800287e859d932500010fb0b3b264a00062f210764c9400043fc2aec192800287c855d832500011ef02bb064a00023d205760c9400364e31ae81928000cad7418832500010ff0ab96c2a000a1f21572d85400046fc1ae5b0a80068dc835cb615000156b09a8ec2a00023de1d61185400053a42ac230a8000ad48358461500015c90
  | 17 => 0x84255b64854c9210840174f089924210952e921132484212a5d3426ec9084200ba584dd9210840178d07bb24210802f160f764842100672c36ec9084200ce765dd921084019cacbbb2421080369a137648421006d2c26ec9084200dc683dd92108401b8b07bb242108ae79a0376484210067343eec9084200ce775dd921084019caebbb24210803a9a13764842100752c26ec9084200ec683dd92108401d8b07bb24210802b9603764842100573c32e890842009e687d9121084d1d48c8b224210802b9e19544842100572432a89084254f2454551210840178f06aa24210802f120d544842100572c34e69084200ae7865cd210840174f08b9a4210952e92117348421005f1c02e69084200be0805cd21084013cd0fb1a4210802e9e1163484212a5d2422c690842009e68718d2108401d8ac631a4210802b9e19434842100572432869084200b678550d21084ab6c90aa1a4210953e110d434842100572c34e09084200ae7865c1210840174f08b824210952e92117048421005e3c1ae09084200bc4835c121084a974d083824210802e96107048421005e3418e09084200bc5831c12108457bc4e0382421080279e1d21d802115cf243a43300422bbe08048660084573c90e90ac01080369dd121580212a6d23a242b004200dc7734856008401b88e690ac0108aef820121580210061fbaee8b004200c3f751d16008401878ea3a2c01080327dd373580210064e3a6e6b004200c9f741cd6008401938e839ac0108aebca02215802115c7a43a42b00422baf08048560084019cf0e90ac0108aeb921d21580210067243a42b00422b8e4874856008401d4ee890ac010803a91d1215802100763b9a42b004200ec4734856008401dc70090ac0108aeb9a01215802115d7240242b004200ee08048560084575c10090ac01080279e1d21180212a6d33a2423004200da5744846008401b8ce6908c010803715cd21180210047dc3ac03004200c5f75d4d639000153b0829ac72000297e0d6594e400043fc2ae7314800287c855ce62900050fd0b38cc5200021f6167198a400346f41ce331480008dd839c662900050fd0fbaac5200030f10b7558a400061e20eeab14804bc3f40dd5629009787a81baac5200030f5977454a4026c5fc3ac52148000a3f8558a429000117b0d38c852001b2798d74cca400043fc2aec994800287c855d932900a793cc7ba26520003171d5634ca4000566412c6994800087f855ce61900050f90ab9cc32000a1fa1672986400043ec2ce530c80068de839ca61900011bb07394c32000a1fa1f75586400061e216eab0c8000c3c41dd5619008f87e81baac32011f0f50375586400045f43c84b0c8000c3f75909619000156d03212c3200030f59774546400045ec34e520c80008bf8758a419000147f0ab1483200032b9c96
  | 18 => 0x840193cc9398c1108032759273182210062f32ae63044200c5d655cc608840193cc8b98c1108032759173182210046ec3cc63044200c5e7598c60884018baeb318c110803279d263182210064eba4c630442008df8758c60884018bceab18c110803175d563182210064f3a2c63044200c9d7458c60884011f70eb00c11081a37a0e76551210046ec1cecaa242008df835d9544840d1b906bb2a8908023ee01765512101c7c402ecaa242028be87d91544840547d0bb22a89080327d9073551213064e320e6aa2427ad1c541cd54484011ed0db8aa89080279a0b71551210061fbaee8b1a4200c3f751d16348401878ea3a2c6908032edd37058d210065c3a6e0b1a4200cbb741c16348401970e8382c69080336dcc7058d2100679b88e0b1a42008df8758c63484015b100b18c6908021fe157690d210143e42aed21a420287e859d943484010fb0b3b286908021fe157650d210143e42aeca1a42008fb805d943484071f100bb286908023ba1b7250d21004f340ee4a1a42008f686dc543484013cd05b8a869090eb6201638c5210045fc22ec98a42018bc845d931484011bf0eb18629090ab6201630c521006973ace910a4200d4e759ce2148401b1ce939c42909073a18170885210045fc22e7b0242018bc845cf60484011f70eb00c090802b620d60181210055b40ee8b2042068de839d954084011bb073b2a8108023da0676550210046fc1aecaa042068dc835d9540840517d0fb22a81080a8fa1764550210064fb20e6aa04260c9c641cd54084f3a38a839aa8108062fa1f7458c210061fbaee8b184200c3f751d16308401878ea3a2c61080237e1d6318c210043fc2aed218420287c855da43084050fd0b3b286108021f6167650c2100477414eca1842008f6819d943084010ff0abb2861080a1f2157650c210045fc22eca184200c3e745d6610840187ceaba4c2108030f5d574984210062f3ace73084200c5d759ce610840193ce939cc210803275d273984210062f3aae73084200c5d755ce610840193ce8b9cc210803275d1739842100656b24e5208421bab681d9141084010ff0abb6621080a1f21576cc4210045fc22ed98842018bc845db31084050fd0bbb462108021f617768c42100c5f426ed18842008bd84dda310840199ac73946210802b5a07634c4210046fc3ac6188421cc75765d6210843796aecba44210803555d57388421006caba2e710842008f58798a210840317d09bb242108022f61376484210346f41eec90842008dd83dd921084018ed0bbb242108031d61776484210065b426ec9084200cb584dd921084019ad07bb242108033560f76484212adb342cc49084200b658598921084a974d093124210802e96126248421005e341cc49084200bc58398921084019ceed292421080339dd95248421005b3c2a649
  | 19 => 0x32d59171cca210366b31ae3994420087d86dd5328840187cc9baa65109671798f754ca212cc3f43aca994427b87c875953288401878e8b2a65108022f61b744ca210061f32ee89944200c3d65dd132884a793cc7ba2651094e2fa1d644ca212fc5e43ac89944200c3f755913288401878eab22651080317dd5634ca210062e3aac69944200c9f7458d3288401938e8b1a65108033558f714ca210071ba8ac928c4200e575158e51884018dacb394a3108032b99272946210066731ce528c4200c6d655ca518840195cc8b94a3108033398d729462100572c364328c4200ae586c8551884018dccb39483108032b59272906210066731ce520c4200c6e655ca418840199cc6b948310803a510563506210063732ce518c4200cae649ca318840199ac739463108031b995728c62100657322e518c422087d86dd5318840187cc9baa63109631798f754c6210e43e43aca98c4200c3c74595318843f17b0dba263108030f997744c6210061eb2ee898c4252c9e63dd131884371790eb2263108030fdd5644c6210061e3aac898c4200c5f7558d31884018b8eab1a631080327dd1634c6210064e3a2c698c4206cce639c8318840d99cc6b90631080395595310c6210074ab226218c422d8bf865d3218840187ccaba643108030f59574c86210dc5fc3ac990c4200c3e75593218840187aeab264310803179d663c86210062ebacc790c4200c9e7498f218840193ae931e431080237e1d63c86210062f3aac790c4200c5d7558f218840193ce8b1e4310803275d163c86210063abb4eb90c4200c75765d721884018eaed32e43108031d5d965c86210065abb4e990c4200d36759d3218840196aecba643108032d5da64c86210065abb2c990c4200cd5769cf2188401aaceb39e4310803659d273c86210066abb2e790c4200cd57698f21884019aaecb1e43108039559563c86210074ab22c790c4200c3e74997608840187ce8b2ec1108030f99574d82210061eb2ae9b044200c3e75993608840187aeb326c1108030f9d564d82210061ebaac9b044200c5e659cf60884018bacb39ec1108032799273d82210064eb24e7b044200c5e655cf60884018bacab9ec1108032799173d82210064eb22e7b044200c5e7598f60884018baeb31ec110803279d263d82210064eba4c7b044200c5e7558f60884018baeab1ec110803279d163d82210064eba2c7b044200e6a2059560884050fd0bb9ac1108021f617735822100c5f426e6b0442008bd84dcd60884831dd0f90ac110906baa0321582210043ec3cca3044200c3e7499460884010ff0eb28c1108030f9d165182210061f32ae83044200c3d655d0608840117b0f320c1108030f9d664182210061ebacc830442008bf87590608840187ceab20c1108030f5d564182210062f32ce63044200c5d659cc608
  | 20 => 0x6f43ec8b1c4200a5e85d9163884014bb0bb22c710803879966458e210070eb2cc8b1c4200e1e655916388401c3acab22c71080237a1c6458e210052f428c8b1c4200a5d8519163884018beeb3aac710802a7e117558e210054e422eab1c4200ad4815d5638840153d083aac710802a76107558e210052fc2ae8b1c4200a5c855d163884015a902ba2c71080297a147458e210052ec28e8b1c4200c9d741d16388401c3ea92a2c71080237e1d5458e210046e43aa8b1c4200e1d5415163884014bf0ab92c710802972157258e210054fc22e4b1c4200a9c845c963884015b700b92c710802b62017258e210054f426a4b1c4200a9d84d4963884015ad03a92c710802b56075258e210052f42e84b1c4200a5d85d0963884015ad03a12c710802b56074258e210054f426a2b1c4200a9d84d4563884014bd0ba0ac710802976174158e210052f42ce0b1c4200a5d859c1638840153d09382c710802a76127058e210056b40ce0b1c4200acf825c1638840153d08282c710802a76105058e210056b408a0b1c4200ad58114163884014bd0a202c710802976144058e210056b40880b1c4200ad581101638840d8bcc6ba8c7108021f61e6518e210061f3a4ca31c420087f87594638840187ce8b28c7108030f9957418e210061eb2ae831c4206c9e635d0638840117b0f320c7108030f9d66418e210061ebacc831c42008bf87590638840187ceab20c7108030f5d56418e210046fc3ac631c4200c5e7558c63884018baeab18c710803279d16318e210064eba2c631c42018be849da538840117b093b4a71081a37a0e7694e210062fa9aed29c4200a5f835965388401c3ea6b24a71080a97a156394e2100c5e426eca9c42018be849d9538840117b093b2a7108023760e7654e210045fc22eca9c42018bc845d9538840317d083b2a7108022f6107654e210343e43acaa9c4200c3c74595538840117b0dba2a7108ab0f9977454e210061eb2ee8a9c4266c9e63dd1538840117d0eb22a7108022f21d6454e210146e43ac6a9c4200c9f7458d5388401938e8b1aa7108031d5977154e210066ab1ee2a9c420287e859da43884010fb0b3b4871081a37a0e7690e210143e42eeca1c4200c9c43dd943884050fd0b3b287108021f6167650e210046ec1ceca1c420087f855d943884050f90abb287108032710d7650e210143f428eca1c420087d851d943884010fb0dbaa87108f30f9937550e2131e2f31eeaa1c420087e8759543884010f90eb2a87108038710d6550e210345e43ac8a1c4200c3f755914388401878eab22871081aa720d6450e2100c6e43ac6a1c4200c5f7558d43884018b8eab1a8710806a72116350e210065ab26e2a1c4200cd563dc543884018eacbb8aa5108032d5937150a210063ab2ce39944200cb5649c732884018eacab8e65108
  | 21 => 0x875d764884018bceb39ec910803175d673d92210346fc3ae7b244200c5e755cf64884018baeab9ec9108031b9d572d92210066739ae5b244268ce5729c7648840153d07b2cc910802a760f65992210054f418cb3244200a9d83196648840147d0bba2c9108028f61774592210054f41ee8b244200a9d83dd1648840187eebaa2c9108022fa1f65592210054f41ecab244200a9d83d95648840187eed32ac9108022fa1c65592210054f418cab244200a9d83195648840187eeb3aac910802a7e0d75592210054e41aeab244200ab4815d5648840187aea3aac9108028fe1573592210051e42ae6b244200ab4815cd648840147d0a39ac9108028f61473592210064eb98e6b2442008be8714d648840117b0e29ac9108028fa1772592210051ec2ee4b2442008be87d49648840117b0fa92c91086e2fa1f51592210045ec3ea2b244200ab6819c1648840155f04b82c9108028fa1470592210051ec28e0b2442008be87141648840117b0e282c9108030f15376552210043ec2cecaa442008bd849d9548840d1bd073b2a9108023760e76552210061e2a2ecaa442008df835d9548840d1b906bb2a91081a37a0c76552210046ec18ecaa4420187c87595548840347908b2aa91080a2f21d64552210151e42ac8aa442008dd86dcd54884cf8bccbb9aa9108031759773552213164f326e6aa44200c9d64dcd54884011bb0c39aa9109971799473552210062eb28e6aa44260c9e641cd548840193ac839aa9109f34715073552210063ab2ee2aa44200cb564dc5548840187ce932ec7108030f9d165d8e210061f32ae9b1c4200c3d655d3638840187ceb326c7108030f5d664d8e210061f3aac9b1c4200c3d75593638840187ceb3a6c7108030f5d674d8e210061f3aae9b1c4200c3d755d363884018dceab96c7108032b9d172d8e2100672b94e3b1c4200a5e85d8e63884014bb0bb1cc710802a7a136398e210054ec26c731c4200a9e84d96638840153b09b2cc710802a7a106598e210054ec20cb31c4200a5e85d9263884014bb0bb24c710803879966498e210070eb2cc931c4200e1e655926388401c3acab24c71080297a146498e210052ec28c931c4200e1f5495263884011bf0eaa4c71081a3721d5498e210070eaa0a931c4200a9e84d4a638840153b09a94c71080297a174298e210052ec2e8531c4200a9e84d46638840153b09a8cc71080297a174198e210052ec2e8331c4200a9e84142638840153b08284c71080297a144098e210052ec288131c4200a5e85dcd63884014bb0bb9ac710802a7a137358e210054ec26e6b1c4200c5f75d4d638840153d0829ac710802a76105358e210052f42886b1c4200a5d8510d63884011bd0fb2ac710802a7a136558e210054ec26cab1c42008de87195638840153d0832ac710802a76106558e21004
  | 22 => 0xb2aa29880317d9773545310064e326e6a8a6252c9c73d91414c4018b8cbb9a829896395d87658c5310070e328c918a62068dd87d8a314c40199ce5b14629881a37219708c53121e6c302e118a620287e859cb604c4010fb0b396c0988062fa1272d81310045ec24e5b026200c3e74d96604c40187ce832cc0988030fd9574981310061e32ae93026200c3e75d92604c40187aebb24c0988030f9d464981310061eba8c9302625887c86dd5604c4010fd0fb2ac0988030f1d365581310043f438cab026200c3c74195604c4a51790dba2c0988030fd9774581310061e32ee8b0262008be87d91604c40187eebb22c0988030f1d764581310045f438c8b026200c3f75191604c401878ea322c0988031bd9772581310063632ee4b026200caf64dc9604c401958c9b92c0988031bd94725813100636328e4b026200caf641c9604c401958c8392c0988023ee1d601813100574412c030262018be84dc9650c40117b09b92ca1880a1fa1772590310043ec2ee4b2062068dc835d9540c40d0f90eb2aa8188068f21165550310362e39acaaa062068bc87591540c4054790ab22a81881b271cd645503100c5f426ed29062008bd84dda520c40d8bce6b2ca41880a1fa1776908310043ec2eed2106206c9e73592420c40196ac938c841880317ddb754c8310062fbb0ea9906200c9f76dd1320c40193eec3a26418803471d4744c8310362f39acb2886206c9e73592410c4018beedbaa621880317dd8754c4310064fbb6e89886200c9f761d1310c401a38ea3a2621880333dca624c4310066bbb4a29886200cd776545310c4851b90e992c018803331c932580312146e43a62b006242ad8804c5600c40187ccaba6cb108031799673d96210062f32ae7b2c42018bf875d3658840193ce939ecb10803275d273d96210346fc3ae7b2c4200c9e745cf658840193ae8b9ecb108032b9d172d96210066739ae5b2c427dce5729c765884014bd06324cb108029760c64996210051f426eab2c4200a3d84dd565884014bd07baacb108029760f75596210061fba4a8b2c4200a5e8319165884014bb06322cb108030fdd274596210052fc1ae8b2c4200a5c835d165884014e902ba2cb108030f5d074596210062fb9ce6b2c4200a3f845cd658840147908b9acb108029d20573596210051f420e6b2c4200a3d841cd65884010fd0e21acb108021f61c43596210051f426e4b2c4200a3d84dc965884010fd0fa12cb108021f61f42596210e43f43e82b2c420087d87d0565884014ed03382cb108029be0970596210051f420e0b2c4200a3d841c165884010fd0e202cb108021f61c40596210061f322ebb24420087d8799764884010ff0eb2ec9108031799673d92210062eb2ce7b244200c9e649cf64884018bccab9ec9108031759573d92210064f322e7b24420287f
  | 23 => 0xd913100557416e7b226200aad82dcf644c4a5c3ca7a9ec898802a760f72d913100657b94e5b226200a3f855cb644c4014790ab96c8988022fa1f52d91310045ec3ea5b226200a3f855c7644c4014790ab8ec89894a2fa1f51d91310045ec3ea3b226200a3e859c3644c40147b0b386c898802a760c70d91310045f438a1b2262008bd87143644c401878c9baac8988021fa1f65591310043f438cab22620287e87dd5644c40187eebba2c8988030f1d774591310062e3aee6b226200c3e76d94644c40117b0f328c8988028fa1665191310045fc3aca3226200a3e86194644c40187cec328c8988030f15276551310043fc2aecaa262008bf845d9544c4011bf06bb2a8988030f150765513100c3f43ecaaa26201a3e84d95544c4b18b8e7b2aa89880a2fa1f64551310151f42ec8aa26252c9c73d91544c4011bd0db9aa89880317d97735513133e2e32ee6aa26262c9c64dcd544c4013ad03b9aa8988030f1d36554d310045f436e8a9a6200c3f65dd1534c455878cbba2a69899b650c77454d3132c5f43ec8a9a622a8bc87d91534c4018eeca38aa6988021fa1b7550d311e61e326eaa1a6263d5431dd5434c4c10fd0fb2a86988f21f21f6550d312c70e21ecaa1a6200c3f75d91434c401878ebb2286988032dd907150d310061f3a6cb3126200c3e74196624c40187ecaba4c4988030f19574989310061f3aec93126200c3d75d92624c40187cea324c4988030f5d464989310043f43ecab126200c3c74d95624c4010fd0e32ac4988030f1d065589310061fb2ee8b126200c3c65dd1624c40117d0fb22c4988030fdd764589310061e3aec8b1262008be87191624c40187eea322c4988030f1d464589310063db2ee0b126200c7865dc1624c401976c9b82c4988032e19370589310063db28e0b126200c78651c1624c401976c8382c4988032e190705893100477c3ac43126200ae880588624c4010ff0ab80c49880a1f21570189310045fc22e031262018bc845c0624c40117f08bb4a4988062f211769493100536c16cb29262018be84dd9524c40117b09bb2a498963171cf65549310062fb2ee6a926200c9c64dcd524c4013ad03b9aa4988021fe1576909310143e42aed212620287e85dd9424c4010fb0bbb2849894b271cf645093100557416c8a126200c5c65dcd424c4013ad03b9a84988031d196718c9310065a324e31926200c74655c6324c401968c8b8c649880387194648c93100727b2ec519262009d6869c6324c4019ad0d38c649880355d96718c931006aa32ce31926200d97649c6324c401b28c938c649880237219708c9310045f436e89926200c3f65dd1324c401878cbba2649894f650c7744c9310045f43ec89926200c3f75d91324c401878ebb22649894ba30cb644c9312c53ac0ecb28a6200e3751d92514c4b18b8e7
  | 24 => 0x6620287c855c262cc40117f08b84c5988062f2117098b310143f43eeab166259c5c73dd562cc4f78b8e63aac5988062fa1f7458b310061fbaee8b166200c3c75dd162cc4a7938e7ba2c5988030fdd47458b310061e3a8e8b16625fc9c731d162cc40d1db0f314a59880a9b2156294b3100673312e329662008bf845d952cc40317908bb2a59881a3b21d6254b3103476c3cc52166201aac8458a42cc40196ec938c8598803399897190b310043fc2aeca16620287c855d942cc40d938e6b22859881a3b21d6250b310364e39ac8a0e620287e851c960cc4010fb0a392c1988062fa1072583310045ec20e4b066200c6e659cb658c40317f0eba6cb18803279d173d9631006573a4e5b2c6200cad749cb658c40199ae7396cb188031bd5272d96310063729ce5b2c6200c6c539cb658c40195ce8b96cb188032b5d172d963100672b94e3b2c6200a3e84dd5658c4014dd05baacb188030fdd2545963100c5f426e4b2c62008bd84dc9658c40195cc9396c91880a1fe1d75d92310062f3aae7b246200c6e759cb648c4018daeb396c918803335ce72d9231006572a4e5b246200cae439cb648c40195887396c9188031b9d572d923100636baae5b246200ce5729c7648c40147d0bba2c918802aba0b74592310061fbaea8b24620287e85dc9648c4010fb0bb92c9188030f15376552310043ec2cecaa462008bd849d9548c4011dd053b2a9188023b60a76552310061e2a2ecaa4620187e87d95548c40347d09b2aa918963171cf655523100537416caaa462028be87d91548c40547d0bb22a91894b271cf645523100557416c8aa46200c3c74595538c401878eab2287188029ba176298a3100557426c53146200aae84d4a628c40159b06294c5188029ba174298a3100566c18853146200aae84d49628c4015cd03a92c5188029ba174258a310057340e84b1462008ef87588628c4018bacab9ca51880317595739463100666b94c598c62438de87cc9608c4871bd0f98ac11890eb6a0331582310047dc3ac03046200c3d74953654c40117f08b96ca988062f21172d95310052ec1ee9b2a6200c3f749d3654c40187ae83a6ca988028fa1373d95310051ec26e7b2a6200a6e82dcf654c4014db05b9eca98963171cd73d95310052ec1ee5b2a6200a3f845cb654c40147908b96ca988031b5c872d95310043f43e85b2a620087d87d0b654c40147f08b8eca988028f21171d95312c43f43e83b2a620087d87d07654c40147d09386ca988028f61270d95310052ec18e1b2a620087e87103654c4010fb0e206ca988030f197745953100c5f43ee8b2a6200c3f75dd1654c40187eea3a2ca98803271d373595310061ebaea9b22620087f855cb644c4050f90ab96c898802a760f75d91310061fbacebb226200c3d751d7644c40147d0bb9ec8988028f61773
  | 25 => 0x4019cae538ecb2080297a0f755964100537416eab2c8202a3f8659554904a533d0fb9aa92099f27ddb735524133f0f32ee6aa48265c9f761cd54904c1a3eea39aa9209978799473552412964f430e6aa48252c9d861cd54904a5a3d0a39aa92094b47614735524132e4f328e6aa4827fd1e651cd54904cb83cca39aa92080347594735524132e4e328e6aa4827fd1c521cd54904ad93cc239aa9209836598473552413fe8e288e6aa4827fd1f501cd549040117b0db92a92089e2f61b7155241006ca398e2aa48200a5e85d8e639040159d05b1cc7209962f21d5458e410161f3aaa8b1c8252a9c8355163904018beeba9ac720802a76135358e410070eaa6a6b1c8200a9d8414d63904fdc3ca829ac72080237e1d6318e410052fc1acb29c820193c87551539040187eecaa2a72094ac720d5454e410045fc32e521c820093f855ca43904ad17f0cb8c87208024fe157190e410053742ec53148200ace83d8a6290405878eaaa4c520802a720d5498a4100557c12a9314820087f855ce62904050f90ab9cc5208032710d7398a4100556c26a53148200aad8414a6290401c5aa8294c520802ab6135258a4100477c3ac43148200c3d655d2529040547f0caa4a5208030f5d95494a410058e41aa929482178be87989429042f55d0f31285208032ba1e6250a410065739cc4a148200cac73989429045b55f0cb1285208662f61b7150a410049ec2ee2a148200c3d655d2519040327f0eaa4a32080a8fe19549464100e1ebb2a928c8200b1c83552519040166f02aa4a32080b0f9d554582410054e41aa8b04820287e85dcd60904010fb0bb9ac1208032710f73582410045e43a84b0482008fb8758060904018b8ca39acaa080317dd473595410064fba0e6b2a8200c5d75d4f635040153b0829ec6a080237e1d6318d410052e42ac631a8200a5d83d9653504050ff0ebaec4a08030f10975d89410061e20aebb128200c3f405d762504011df0eb10c4a08021fe1573189410143e42ae6312820087f855c062504050f90ab80c4a080237e0d70189410346e41ae03128259a5c83596525040187ecbba2a4a094ea720d65909410cc5ec3ec52128200a3d85d8a425042f17d0d38c84a085e6da1a71909410065b434e32128200cb4639c642504011790cb8484a08061fe1d65945412c52e41acb28a8200c3f65dd1515040517f0eb2c82a094aa720d659054100c5ec3ec520a8200a3d85d8a415040195ce5b1482a08062f219709054122e5c302e120a820087f855cf60504050f90ab9ec0a080a1fa1672d81410043ec2ce5b0282068de839cb60504011bb07396c0a09170fd9175181410047dc3ac030282068dc835d954cc40d0f90eb2aa9988068f21165553310362e39acaaa662068bc8759154cc4054790ab22a99881b271cd64553310043fc2ae131
  | 26 => 0x23b60a71d81430068e21aeb3028683c5d731966050cefc388632cc0a198e1f21b75581430068e21eeab02860087e87d956050c010fd0e32ac0a19df17dcc655814341f0e218cab028600c6f65dc96050c018d8cbb92c0a18036310f725814300637b28e4b028600c6c651c96050c01b1886392c0a18031dd9771581430063a32ee2b028600d9443dc56050c018eeca38ac0a18031d1947158143006ca218e2b028682e1c431946050c011f70eb00c0a18032799273d925100657324e5b24a201a3f8659154944b12bd0fb9aa92898b17ddb73552513170f326e6aa4a260c5f761cd54944cba3ee839aa9289838799073552512c62f430e6aa4a258c5d861cd54944b1a3d0839aa9289634761073552513062f320e6aa4a281d1e641cd54944c183cc839aa9288034759073552513062e320e6aa4a281d1c421cd54944af8bcc239aa92899755984735525140e8e208e6aa4a281d1f401cd54944010fb0db92a9288961f61b7155251006abb9ee2aa4a200d54731c5549440153d09b1cc728802b3a0b6398e513043e43aa8b1ca201c3e7455163944b14b906aa2c728802976174358e510070eaa686b1ca200a5d8510d6394501c3ea821ac72880237e1d6318e512c52fc3ac729ca200c5f8758e53944010ff0cb94a7288024fe117294e512bc3fc32e329ca20093f845c653944492ef0cb8ca72895f1de197194e510069bc22e329ca200d34845c6539440193887bb287288032710d7650e51004bac0eeaa1ca20293c87551439440187eecaa28728962c720d5450e5100557426c5314a200ace83d8a6294403878e8aa4c5288029720d5498a5100537c12a9314a2008bf845ce629440317908b9cc5288031714d7398a5100536c2e85314a200e2d5410a62944014db0ba12c5288023be1d6218a510061ebaac9214a201a3f86552429440187aecaa48528802c720d5490a5100e1f3a2a8b04a200a5c83551609440317d09b9ac1288022f61373582510062e29ee6b04a200c6f521c960944011f70eb00c1288032719073591510052ec2887b1aa2008df8758c635440153908b18c6a88032710e7650d510064e218eca1aa2018bf875d36254401878a4ba6c4a88030f14574d89510061fa82e9b12a2008ef87588625440117f08b98c4a88062f21173189510045fc22e0312a2018bc845c062544011bf06b80c4a881a3720d70189510061fbaec8a12a20287d87d8a515440147b09b14a2a88031b9cb62945510143e432e128aa247c78605c2515440117f08b9ec0a88062f21173d815100c5f424e5b02a2008bd849cb605440d1bd07396c0a88023760e72d815123e1fb2ae8302a2008fb8758060544018bccb39ecb208031b99672d96410064eba4e7b2c8200cad749cb659040199ce7396cb20803335ce72d96410066739ae5b2c8200ccd735cb6590
  | 27 => 0xe2a6e6b0aa800d1c541cd61550011bd0fb1ac2aa00237a1c635855440e2fba8c6b0aa87fc9f7418d6155127c38a831ac2aa24b8715063185540047bc3ac230aa8068de839c861550011bb07390c2aa00237e0d70185540346e41ae030aa8008ef825c061550011d904b80c2aa2478715063d81540346f41ce3b02a8008dd839c760550011dd0538ec0aa0023b60a71d81540068e2a4e7302a800d1c545ce60550f193ae831cc0aa2438715063981540068e2a6e6b02a800d1c541cd60550011bd0fb1ac0aa00237a1c635815447e4fba0c6b02a88ee1c5418d6055001a68a9b8ac0aa00335d8f71581540066a31ee2b02a800d34541c560550019aec638ac0aa0033518c715815446f0e2a0c6302a8008fb8758060550050fd0fbaac5218030f10b7558a430061e20eeab148600c3f40dd56290c050fd0fbaac3218030f10b75586430061e20eeab0c8600c3f40dd56190c018dca4b96caa18031e94170d95430051fc22e5b2a863ca3c845cb6550c018dae4396caa18028fe1171d95431e51e422e3b2a8600c75711c76550c7947d09386caa18028f61270d95430063cb80e1b2a868cc5f75dcd6550c0547d0db2aa8a198f0f1db655514331e8e39ecaaa2860699e87dcd5450ccf938edb9aa8a199f8719773551433364fbb0e6aa28606c9c761cd5450cc7a3eea39aa8a19838719473551430061fb2ee8a9a862ac3c65dd15350c0d4790caa2a6a18070f1d95454d430358e41aa8a9a868be1c431976250c010ff0ab8ec4a180a1f21571d89430068e21aeb3128689c5d731966250d15c388632cc4a18031dd9671989430063a32ce33128600d94439c66250c018eecab8cc4a18031d1957198943006ca21ae33128600ce7625c66250c01a3887baac4a18021fa1f65589430043f438cab12868ac5f731956250d13c388632ac4a1a238710c651894300477c3ac43128602c3c755506250cbf53906aa0c4a180a1fa1671189430043ec2ce2312860087f855c06250c050f90ab80c4a18023de0570189430047a40ae03128687e1c431976150c010ff0ab96c2a180a1f21572d85430068e21aeb30a867ec5d731966150d0dc388632cc2a18031bd9672985430063632ce530a8600d8c439ca6150c018decab94c2a18031b1957298543006c621ae530a8600ce572d866150c01a3887baac2a18021fa1f65585430043f438cab0a8686c5f731956150cfdc388632ac2a1a178710c65185430047bc3ac230a8602c3c755506150cad53906aa0c2a180a1fa1672185430043ec2ce430a860087f855c06150c050f90ab80c2a18023be09701854300476412e030a8684e1c431976050c05878eaaa6c0a197aa720d54d81430143f42ce5b02860087d859cb6050c011ed03396c0a18023d60672d81430143f42ce3b02860087d859c76050c011dd0538ec0a180
  | 28 => 0x10000002001000001c000006000001800400100d001c00401d005800800000f00080200020040058018006004000000000e001001000002c0050040000000008005000001a006001000c0000560030000008003000000000200a0000008000003000000000a01d000000000400b001801000000100d00180080030058004026001000000401000100000040000000028000024000001012001e005000800800000400b800800c0050028004000000003800000a002000004801200100780040080020060034000003000000000000300780040000020000000022002000000001800100800000000060020004000006003800001e00a00280080060000038008000005000809c00a002002801c0000010000044004000002033c00001a0000018008001000801400802c003002c006002003805000e0020030004002000004803400e0040020018004001003000c002000003001800200200600040120010010008008001001800400400400b803401000b0030008000000000000001401100080100000120030010006000012005c00c000001000000600700280000080040070058068000000807400003a001800c0000130108000014004000000400000100480000060000008008026001012802c012004003800c0000090030008002000003008000c00e0000060004003000000401a003000807400a00000000000080090000010000002000000c00800100300740020030050010008001000000002c0020068008004009000002c00e001001001001400000100100080040068000006000002800c006002003000000c000000002003c00100600200040010000000006000008002c000005000800400c0000028000024001004801800400000200040100020008000000003003000800e00700c0008022003005000000000700100180000000000000008000002000002c00400b80040040020000000004007001000401a000000002c0040030020068004002000001c0100020008000004023000001c0000050000000000001002000004c001002000800000700080240080000000028000002000000000a01f008800000c00000100080000030040008002006000006000c001000007800000001a8018000001002001400201d006000400600d001002401600000400000020003152ec2ee3b1aa867a9d84dc763550019aee338ec6aa19ea761070d8d540046fc3ac631aa866a9f8458c635512fc38a8b18c6aa01aa72127618d544b70e2a4ec31aa895e1c5418f61550011bf06b96c2aa01a3720d72d85540068e2a4e730aa800d1c545ce61551278baea31cc2aa253275d0639855440f0e2a0c730aa800d2c549ca615500199ec7394c2aa0033318e7298554006962a2e530aa800ccf635ca6155001998c6b94c2aa003395cb61985540068
  | 29 => 0x60020008008000000001008c000004000000c00a01b005000400403900000000340020010008000003000000400200a004800000e00800c8000000000000003c000009001000000a0190008008014000001802c00c006006000000e006000000000800500c0008000001002003400000900280000220050020000004000005000400a00100100000060090000000000014005800000000700000000080000020008000012001800400200500e0028000017001001c0020000058010004004001804801200f001002c00800f001800000000600380080020050058000010004001801001800000280140020050018010000002005000c000011000000c00600b00780480540090048008006002002005800000c00000040040020020004008001000001400a00400000ec00400c00a800000200700400b0016001001804000600a00080000020020080014000024000800000a00600c800800c00c0028014002000001800400e00000000080000020038010002000000000400400c0038010002001001000c00002b0038004016000014001802600c001800400800100080040000050030044010000003000400e00d003001400200600080080340000048068000008000000000a000001000000001a000801003c00001b8044002003003003005c0060008000000001003803c000000000800002600b0090014002000000000c00000102a80280000010050018004002000800000400300800000260050010024004003007001800c000000007800a011000000000000100b0000004003008000c006002000008400c001000804c006005000803000e006001801c0040080010040000000003808000e0000048020014004000000400000700000000100020038010002002000806c000000000000800600800780000440000028000004017004800000e002000802400600300000040040000048014056000001000c00a00300280000040020010004000000005800802e007004800c006008003801c000003000005c0340070000018004001000800801e000005000000200c00000000320090008000006011006000000a000001802800201700680f00040020068004002012001000402800d001807c002006003001400000f000000003800100000000060010010004028000003800400401a0020028000004005001000000f000002000e00900b001000000300e8010000004008805c00800100200000040000038004000001001802001800a0040008000000003800c03a0010028038014003011005c004002001800003600b00680600000000050000026001001000802e0030018010002000000803400602400500600000020050054002000000800800e00000080000040010010014000000003802400000d000803800e00c000008c01a003
  | 30 => 0xb089a00287258200000000000000001314000000000000000000000079a8da92a2ed20002b380000004d7efec9048ca8e2045d716c4042a20b01f46ff2cf3024000000000000000000006400008640000d7b8e10ff5084eaf91008600034d2f341249c81708000ebc68800011790bc91c014c0005d89b8f2909d82f60004be85bd37c1ca2750000b0cd61425a255e5474351e04533e07514640158b1a0001868001e12000000046d1607555091da042831f396af546b60002f6a71b50e19b6e483dc000b510002b179fcde94fb60e075ae060e6bc385a4a5943600001d61b76714c03c400003899cfca6e8c4316b74e0000000001d609261828002af85683f9608b5a17f0bcf25300010ae5ca73cbbcc4a61238000000b2c3726f415c42688f7c6128952cf4b70d38e64000c5b0e33c36cb89270f799d43869dcaa525e0b8cf3a4c7a05996e4534eb0afcfffa6204444587e8b486061a0c76c0ed4079b3559ae2b39897c40004b300026952a832c0d52c8d006b641918054024af64c819e7cfe02965db6a856462500021f84fe0000000000000cdd23d800001eb1a7563bb81720002ce13500001390003ae00005913278ba041eb6d3623968aba38f924a7b0000b4b3bb9c5826000048d0f3d3e448101c37040000e236b16940b2000280b11d8cc0002b5a9dd08440566d18581400b7258e68861c57d6b80958af850a167a3480005740002ed967858b342825947200060d05746227c9122046a000abc00fca70bc81b2568990d2f608e56b03f4000000096800000022c1e221280001a09583b9d93a0002358000000eab00000019946570000004001000800400a0060008010020001002800001400000080000040010000000000016001801c02c0000000000004006001000400a000003000000200000b00c00000070048000000003006800800400100600040140000008018012001000008c000010000000002c006002002400a0090008024026002006800000a0000008028002000000000801e006001004800a00100100d00040170008000014000001802c0040010008060016009009000c0020000020004004001000001400a0060000000036012006800000a00000180000040010000000018006000801c0000000090018016001000009402c01600080f400400400800640020020028048004006001800401a02a0008008024000000800000000f0000018020002001001000600b000802801c001000003c000002004000c00000d00080a800200a00000000000030010004000000000000c008006000800800e00400000000000000018004006011000000400a0090020000000010001001400200d000005c00a0050018048004002000000001600000600140000040000008006001003800003600800400280020010098000000002002002
  | 31 => 0xe800025ebcb4318a50000cd48000f2d2195d03d1eb4c0205c7772a801d5222531c28b886c6271aa334c4e68f666ca15498c5d64f19aa40000004f9f4d9d0e13230f938522c1648000001ad469229d8ea0a8496f67100000000000000630a50e0757298c555a28f6c90330c06de63b878ddcc2ea74328b1ce9855722002e88ac11fd3a87a0a0c5dd6cc2340d72b8e27daad1a4c3de3b888d68a2ed54689901a2a5524711f2ce85d8349a0f5c1928360a918517ae2090e40684e668ef256b5d9ace218e0098612d40244101631576470494b6c1e2cc2e1430fb94620001e4a1b949e00000026f16b852f5bd8c68000a70385b288f4ddf400000000000820c0047400001480023300000000000000950f30788621188800071b254c4c900000023f2e4c000000000167a00069d8fb0d8e00000000002b633353d39782460003220000000af200000004269e10c33b21418637357017533c944717b0f10f743d4e789f00000000001ffce564076c7af7c2500000003849df61150fe95416ee4b038e30a8de0ef0512087c00015f000000097c84d1310000a2400050337415e7e62051000153e1822cb8160868af70cc261d97c2cd000174c0c30000000f98000bc300026fa000d0a6fb35e400026c00036716d00005f1978519a0007161561790c9456800019c2f1579938204ba19d791b15000006580035a59cedc01e0806ba8c3fb00019208cc000000084400012c00000000005842588000b3aa298000000000c5267db524df856e4abb9dcfe290144b2cf8462206244316539157b6b296288c4ada7138001b0000048b8d3004e9d34af2f149ded13000000000008551a2365140a177059504000ed9310800136c56400030499ac5853db01f557400067922f800000000000000000000000ca40000006838000216bf24201ce862806778093b8f820fc3a0b2200000006e428786320000000f32a3a14600013d45ec06b07c800000035c44eace1e2e0001bbb67c3ae7b81f880012aa5ee74a022af7a5c83d2000005827a1acb49d5c0bf169c081013643913c996d90c76fcb2a160000cb40000001b120000998001d8c00056100000004a218db43877a00000000000000420002cb9bc21c21702ef00000000003d040008fc74900008a3d084e200014dcbc66f3a0680000000000001d2e6f700019504d40000e2873135a0004b49c7833874538c1ce077e00036ea23c7c69c7a46000000037f744345d589000638000000000000000000000003051d64a7c2fb0003a54000ee253fa170000e3212b8000000da3000203000092f21abb1426cf023300d38000dea0101c54f4e81b00008bc14653d130884827a14c0c9b1bd29e59800009378067f909da47878ac1e71a9c6c00086000000f98700002c718a1a54a0b3768cf000047c28ab085102635000377910
  | 32 => 0x504fe61cbce41706765850b5a60052030e3cf0656e3e000297061091439a80000000007648aec2aae244e8949400000000018a90fe55e63ab4f1610000451230ce3e0000000de4852ecc0be345000000035783780009d901280002cbb862a99525ac49d753d921560a0005bc00000c1b2608616ed83a1a32f1093031416054d337d376a9836b6a1a9ae6800532fbd154c8e01ba24dcca9594fd072c3da487424b2647aaba30000979c3a6053d88000000000000286d3d4c206a02a5ce04d67a0bb5b530700002510694d80744e0e8d5aeec070000000000000000236800000000000000000004c68000592b150000000000db85d080000009310012b8c000c7f0000000000b4f0000001a1600000014100000730ae0e2c0000000001f6d0ecdb9180c001387adf0002ba4d98e4ae76ad49708dcb269ab9ccb02aa759b2256507e0000000092c0000000a1c95c000311800000030c472000178e15900000016b03b325027980000006eeca6c57400c11e00000009b25d626107babf500001e40001f600037ac0003e9000000044800021213085967a872c27084a28c1c3da14d7100ea59c90a96bca043e69de743edff000018c2a8a9156e1d9901af366599e744d278a79580000a208a1fe80016560002c03a38916576652a5901b83b919b02bd0d4280699063d17e0003700765178000210800006cdd100000000000000000da40000002d080007b4a22368800067e0006352dcc0009460003d0cf289956d5a5f80000003b8c0000002d7a29fc8077436d4872bc1410b1650889f8d646b60f196ccd767d84c13739bb22338b1e1c04b860e71c8a9c008ecd495a2410cee16369b6d8a069de49cb5cc6b463b18173303b65e7060a361221edf7188698d389604b692f026aa4662c36a439eb5b65416b9d3c41c3da00016c637674110ac9d28bb4ef4001089201378b9f02a20002c4a3742f200016c91b52e10b16411dcdaccc1452d82fd7771c175aabe5ae45dc325b22c88200014c8a108b43d60ef844ef327bb60a96bc82092a5b016e9d3a19970f000156674a0001c1c0000000000087ab0a8c00000012eebff433400154899a00000013c0bb12268000958d4e1a887f90820000386698000000141000000000038a00004da27107919c914ea731330f30194d9e5553abcd9e00a4748348a3293a4ecc59e81600072300007b6b2c0000e5c660000732305c000b0cdaa11d020251665e8a200000002e0b49148200504ea7774de9710ef0e580004c50001330000164789c0017a60003ae3444776d2d000000189e2a61971da4ec680400017f5bca00000000003d67e4000000180a8b965706345940006491170f429dc25e84e0876c2b24c8fac780d8747a18242a0999000119442a5ac7a16b2542f1a400000001ca01e3618000000bca3868b7413c9301c
  | 33 => 0x78b466814cd82f78000000f1a6040001b50ac744b9a38000c160000f0c8a48591c138d06e8bdc16bb14cae6d9b00000015362be4dd11a199beb65e08b682b4e4715725c603402139491a419e93e0000000e766460a52718000b7f1821295748665095b71c000ad500000000001771cc0000000918dd4ba24bd2add0000ef95bbf2d090ab8471800055926a53c163880f4000f4f0004d80d580000001e440000002eb00004aafac50b4c6f7897ee071ca6a3e063c18e17b98cc5c41f35044399cecafe68200003f8e016249a61bf43cd44880012ac0444b91a90000a070000000000000000378c000a20000000000000000000000000000002c059a551df2993656ec42f64380000001ce6948e2116ea2cb2e98680e08b2000000000000000034bdcbe000000000071a00017a8d2c0007280000ea9496a4c5458c74000b8d68f8e4586800009fb24045c00054308f70bed0640a1108f1a0003bf1acc00044e5d40c5c000ae663a0001a2000045a0d9c22dd0d0000cd4000afb5999479886d86000013006a9c96db8b6ce6c0004adb7d4000dcc15b800000000061a8c52000b4a00000000005c41ec00000001682c7b04c53af106c584a800009967b1e20e4279600017d43d7d1241e1df03c00000949c40faa5b06b621f59cc8662681c5d166a1900037bc00000000000000002e70000000a42e21000166860e8ba1ea1caaf2a3934fd86fc00057f0002ad40009073c330d20560000f81cf000000000000019c63904e68000db04095ccb608000000126b6440000005989fc0b2a54664b80018f660168606e000000000021dc0289a03bb0abc0009150000001c1eb560e9a7d90663a352a8b5723e6592d0059c0008f270da32ccbc46a000332594e00063ba88d49aaea576094000000057c25e60000005b3b7ccd7eb1c3b11a6c0000db00017a90e4a8e800000004583050b40badb60000001d90b36000000258da34000339a351b780000000534b10bcc5d81f3200000000013740000000001ba40000004ce9114000c91f2a0000bb201d51680005fa0000000000cfe00060508dd0d62c34220c3cdeadae441800100409444d8000a4e00000000000004e33e8a2f5dc20002b4823caca6962b6a1307a06aa5049008e9230b72e3d01d00bde49fa5e8af262f5f5dd956547fa000000065441500033040000006371c8c000809000017a3bad35000000000000032fb1e8000a6b027a7b84e0dda36bb7c4e242609c1a7fc00000d5f0800103203a4ae82d4000d780002b0177200000038e80000000000001e66d9300032d80000000000001ab600015699e59eea2c72eb7ec0000001fe2b7365ecdc0f735c4ed40000001049a3c42d51ebd1400047a5acac7d84e1d82e88000000131000000151224214f05f5d6415ac280000a9623a00019d08c00005a21075c
  | 34 => 0xbf053824c227c0005be437b2ac5fd1530bd0ffdce8708665a4a101ca2136f1b200009243cd00017045836b5aa0c58c0001ae85c1c804ec00024f195236800000017b29d4000398c000000684a76b4f0ddc361239cefae6b0001a181310006eb0828000052634a6dd3ea0001528000f180d61fd00010146f434802944dc60b1a80000ae4491000000000074865000000000000000001b767c7000328526a00000000016d4790279099000099800039580008510430000000f2817897010c2b4620f00000000000000000000000670270c13e3813450300350d997451450eb400048280000005d70000000000b550000000000e593e628bc000000330ae7d76ebd4000037e0000000000072fb400012f9c94000000607031d32339f640af45469aa76a9bc3052a66b72b8bf6942bdd2f41538ed620c1e9845113202d95c32fd94c79f72da8e03407d456f280475eafd2ac8981d422f855ca9d0d5899c36d23ad58fe7354229c5de3000000000000087510dad340005a20002aac0000410002a09546dcf000000000016b72795a950004d000307e0004e2480000051427559a9a5e00074f1da17ce0005610d8079cf1e83700012e4b78be76a58dd580c81c0000cbc000428388b131ade0d36ac8000000000784318529b00039efcb80003f00000000380ca40002eb80006ce5ca00015b00000000a15e304cf6df85b9023aac3a5b75c57a6ab3603999cc53b22aaa3fc0007c2000000017a4794df85a3852b80323811d4d29386bd9a512e68a61a3a941cd890280030c508c1bd37d1f991e2bfc4c24001c12b030000001deab0f6a18000f904aed5301e635210aafb80003f00bb569f8c18dab2769bad38fbca5a3a036056fc0000c203cd4a46f817502b1da0a31d57244e00000000000016180007170000ec00190348e706510001f136914ec35749680000000003f407c8ca0000091307c0592bc0f630bc87eb830002dac0aa0001cd343c00000000000000000003878be88740872a897d8090edc07719edbf2a9d000000000000000000000000b5e49800111c7fb0000f18dfc00054514d8c58dfc4d3a42592c8c716b3d120003f856500010460004cb09e0000f130000000f264381ecafcd5f86c90000001844000630113a34420b4a42db020e937000000000000034f19de9f063e5513af46889a86360f8000056867e80010760000b626508ba35541504ae000a6510cacd905aa535f019f1540ee05810bb80000003a980006ca000000004fe4c17177bb0d800000049987d0eacd345dfa95d0e66846be80016b4000000037400000062400000006e82258869258b4303600008ab1fb00000015200006d88b99d620003cc3b7849c2480a41371900c3e50eb8b4a363633f9b5795fec9130006b97306a3179ba994015db4a1ab6c1f0ee600000002244767
  | 35 => 0x5cb24600005932ae2f2448297eed61c3012ac781928ba589a9911883b6d1dc6643d4815d022457bef91bcd4a00038192b773605f6740c24b281912dea2911c6b0978fa3995d6000656193800096b0b6aa58000da13901848bccefd3e8210cc2a56653413008b239500002700009256b180011ee0000e4aef58fa13a39e80010640000001cbd6cad606fe906c0000000fca5c08d82b14028c09c1a84e5659a2c1a023435b911109e9c9b51173c2d252335f2f411344d600027488eed973d4c00188c0006d10e859a4e99740b104bbc5ec00015e136a14e6c401192f73891560a61d2043c5caafc03f406f24026ff73a54f24da040e83e3302d35312ea271e62b9d400000045c0000a0e40f3d50000d9400016c7aa07940001be321087c92111dc0bd83270a694263200075d00000011806f9000116c000000000000157e0265368ed4000000000000149000035e002400008baffb829204c9a081a6b8c0c296124c001964370514bc001d0000594b0ec47ebb30c80285cdccff79ba5f15c427d26411cc20a5132df87a9a5c9d4b438000baa49e054ab1000000049002200006b50e880013129b79184000996a645768000d22cc000000000003e7227800000033119400c96f2000008800186494a5d2b3cd41e1612040001dda7044a1116692e4d1457194ce9ae170000e9c00000071ea8cde4e0000000000caa000775000067600000029752a085d6e18a4c8a09da0bb01d42226c4cec23ec00082149d97c0dc6a7c777c001138b9765a88e49daa80e90b91484000008480000000001500d84000000000389474487177b000000003f3fc34fd92a000000000000010412d94a97140006748000d4e000000000000000014080008fe0004c300000005454a00000f780001bd01f8fda3bc578b3b03acb110001d51c222f414d1f2e40402d635ab3c5f85d81a100017b00000dcaa49c3eb064b35b776824eb307892d5dc83a254ac65616a49145822d99ca1a1af92fd3fc68153016ad1ae6f6752a1680005df39f3cec7be0034ad0bfebfc4922ab14acd3e5096988200f3c00054f0f1c3589f100e1125d1a0003250741b0a3a022a80cdd8eba6444000167449d09710b800008300000000005a900034620000000001fb13fd00041426c3d967797948b4ce589064cfb6c804400050280010c438a10f099c9ec02e000039da305e02597b5019a6171875f11bf053c45283906729926ae8e1904ac6863b25884e40000b524ae00063d3263d1020c68f00008c000000035080010b6c1837e8f45e22e224843b6800088900001fd56067d1d62d88f8056070803187ca36c3980477c2833711bc655a3a42729728aea0a9ac6c619a1b341e608409acf665b63ba9b2d6485f45309f292149662a41b41bbe79b5e10b94a660003c7244d51a43338160f4db8f24071a5ea
  | 36 => 0x127a0000002738000b9000013d102e01f3a80000d3227b000243c00000000000010300f00003ae5194a854159060dc4064800000016856334ea9a9aac6e6037000000086d00013dc7e49790001b48fd4c6400021d00008396811b194fa7000000000c7828e5b48fbc69400000000001780b625907d47700000a287680000002cf85780000004d0fb447ea0003fa97358c4cf500000015270000000c8a4bb000000000000000000033e4a3f00077cac403bdb0d6ec00013362d873e9af40008a11f530c0c0e06539107a45a200056bb40cb5099c8000d245fccba000161c0001be10c00000001894f219a96be7e971db174cb715800b80000006d40c59f8400000e57a800157a6e56d98d48000829522a11d23a7466ff059591a00000008d4ef6bb52af800000000000000018460625330000aee636317000155e0006640c857a43718003a8c000c046120961c00d953583641764cd44c9baedd802c800039c924c245159adc0fa663a1d8223bcda1737432df42c618371f8241016414583da4d1d4040b73849862c11851b15c199a2270cb9cfbcaa4f3038ad15542c5e55c1eb49542772f917edcf0a33c79b6b42147ef00017241e8bfd00000000c7662715280800000000000016f80280002bbdb2c38006c80003020b36ba00000008e8c6f8b54d820001203ac1d86b9a6d7b4715380003f29f710f49cb1d708885b8d4f5f68001d3ead46160001c1c91149b245279b38ed4a804c1de0000af60484a800000018211b8f340baae4ca2ed457910000000d164fc8000bc65a40000001300b142fe082002c01b61f800000022862d000095f6290002e24000a400000b099330005138000808cd7772000069e00002d800000000073f1ba8000301000016a00000000017cc0000004c1b81000000026a9cdcf0400000000000c50000000870000000000000000000067e00000000000d9ad987a42b6110835d68400074580000000004588000000a3680013a05da2590000000f440e08003c84000ebc0000001a823c9a9c800000064d3c0a6f5a7a5025f5a3b40000c3000000149cd63cb6330c0006631829c1800000053c8000000b3f0000001b68c7200019f82fe5b14d087851524cd6fb9eb105c3a4774f75575e00016a031563620d5ce1aa17182362bd1dfd62665a4d1bc32c3c000631865159000020c869507c00024a972ce72be66dea86a6fa4af5b70ad408f62664f9270fa4ab157422d40009a400033b800000000037b40007193778001a9a00000000019e8f0a000367493e7834038929e0eb610001a8118242357a000012266f07a80013f000000000019d40005177c1089f7af1342fa01f60004438000000000501fb7400062200000013ef000000087468cdcd6f92ee981683499235e89860b014072792247f20b300008a5e64b80ab05642000
  | 37 => 0x603d21a51ea748cc4000091c0b262fb5b947cb071ac2642f8c911853a464d4cbe240aa34d29c2a1146049600000050699dc00046e3fe8001978a0fc63000000000000580000000001cf008cb04000025a83ab700004a4b0b40000000000000d62b720000ce800048900036340d4bb800008edb4a000137800024e3400002504000345547b311398ee85ba33e00000005dd52d82cd3e108f25a00629c100ad4380000003bc351cc080007719cc87dab1e000000000047e777974831000000005e1d5aed325d80015e600019f000086282678a3379972c560a0b1444e8eae16600016a600000035f8000cef40f196a0000004e5451044c53f38299097dc62b57238140c253404c00003eef1c61ba89e0003f63df8000d0400071e1f14440e4e000386890cc45638a2a195498e0c909548f07853449441c96dd23db8ec4544827049b5d532e1dc22f8170000c8f4429030000a1c0001e2c9a44b09118b93e2400046b2f389829d04da3681cf60e13d58b1035666d6a11fdd2feecf0465834f64c2864281f14287523f5b931962f03523b9bd21a093e82ad1c22651a246a4c83747be1b23bd0ad81563332020000acc45b15bc0006e40b93c149fe7a60cf2158e68e9a482319c1087445440ce0c482650523319d7c39b5968918000bec58e85253de4fa69597e4daac3d50b3a451b642566380ed9a090acd5a7dc06036028c315c5e49b374c14b4ab40ff14ba44b04441f54085f87c84fd77f25f21e238e2dc81b478456231006681b07cf422a829d1e10d24d238503e3dc5bd272ee345ad4e38001000162233a7156986b800002a9d08cf01a400008e2000667800068600051bae14000d3e5484000000c100003be0000000027000042e9c0151800000000004d000000000051d80000005a60000e95c8200061980f13fac8a00001800004033fe400000044a1bc000000000022a5241aae14b32483f8c20c0f2a0000000081d7a047951d0774000312811b0003190000000cdb6b23ba542a5b575a0001bc01192910000f4ac000d6f1cc0000ae2788000000ac6dd03540572a9938480000000000002c800002fce4c00000007a053f1db8fb2ddd2da0d4de4a9eb1168fcddd650047630e9e1f1e46e994d4c360004700a8a00000062e36e8d2b0000000fdcee00005644001ca2d19000231400031c00026288220000000001ce00007418d346bc0d42c924b9b841006a54c55c3200070e115c000667375a84c0000000000e1dd485320002cec0000000000b40000054800148a0000000001949dd82633762e1d6baf3d087b7115b22ab1003be8fc619f730118cb8a76f085c94e092a81d89000070a000625a018000f3f47e9118000dee0000000000bad0000000a4803d38ea979a000003381665460834798a728eda6e1000055c0002477429f75430c42651800
  | 38 => 0x1122d75f2c801000008a30003488000000000277440a00000000014a20000000000369f0b48da208522baa0da2e3da900d5417a2609ca4474c60e996eaa323010000000cb00003a8853e8f958ba473302076146a004a74295ab3a961e8e3e86bf81e0452b2509e096828e9e74578b7c58a7842240001de4000721b89956e5a759a2aa48a800000001eceb699b9191d9c00054717803ae00009700000006246df3c3947d3f8e4a582032ca1a5e50001378968d5f26da7a4ff818700000003760000000859cf46968a780014c6000346800000000000000001a19580002e45e325aa43c8c980007b900000005a90002a222b46ccbbb6a909860000e000000000000007242b1400033d1ad40012a4ceb724b1550c86695014000000a9300000000007b524782311e02a970a903800096708827cc24863f3952ead8ca30a5fd0001984a0300000000005fa05f35285bddbe3c003080bfe0c68dafe53e8a5411e800000000000012e847074e0003bf184c0000002f691fc4c45b797e638ef3827205fe9cc7b034a6cc0010bdb5fa14b03fe945189a9100006b43180000f2400076ba958f128803d71dc8000d2548bed0024080e8cb3141d6e3840de0409bd8b0008719b68266511c79bb846697400027880007ee65780009945f8800204c000020800168c5de6c530c9531216cf8e9f76280e99d530ea5d8cf1d5478eb2b44870000002cdc752c4e0003c784540004dc06d43aa25896cf06d9cad333973c6d12450c7099098e036455b88ff96a07fe2c080005f22432bf1131a2fdca48615d465a5307831d8566451c2423a4c52490311a42a1702da700006d8238ec164e2f01158a2a4c58a9151c000000225000066c00000012dc40600000000007c36aaa22db28c1c2739c91244d5c6128179d38077034080c000da600008f8000232e9835680000da5a480009bed8e5f23afdd2c140446150d07e52658c10dcaa84b5000000136200056918d0914000521a234d2e9471e437910f88245fb13619aaf3e726af957aca3f32b3a804db9db70c050c00ce505210001804ec44a583d99180000321bcc23792302800017244610009c3840e6713eb82ac0007e75070000000c7c000326c4209a0ebe0000000e6a5082a5086079c0228b8c79ca4a668b6d4f9ca5f561bb29dac36e294800066808d06fbb0956c46425c0000000e0300028a00000000ba0e50000a159b8400119e0000000000cdc4a7455ae9dc8400000000000007970f10000068f0d6a89fd11aa5c300019e83e25b276c00005bc3b734634e50f0aa51991d08000f2c00011c823e3ab5da120d1ca2891482ef98fc95c3f123249e0e2363c874882c0d12a6bc6628455b6ed8e48b6e4a41b88000362d4406223e8844ece4880dad13c7a335d279511477a0000d897d40004d50001a460000000001a747f
  | 39 => 0x3a3a77dd3695f35693e400000000013f064e0530390001a400000748c0c00006614194c5c526132f5a37947484859133e88eabfe072420581aa0596020d4000e684b0a2f373c0001a0915a81a5c223e9a550d036f563214899c4ab00018e56ae0001bd8000000ce4000000000032058714446fceff1911d5d3d0a2665c1bc9456dc6263a6bccf042c5d106b5ce22e43b61161a0237326d37c041c5ce3c884dc00e9ed7979845c040ad0003610072be94dc81e227c7ba443093cbb401b80000005fea670003ae8000f4224a0750112f460000001550000000000106260c36c8000000018200815059c02a2ea34b099212508d128dcd250f0002b9e630a726ea08ac1d898506728ab9e22527462530000b938000001cce000393b20c8866fb57d173000000000037149c06411830000550000787baa8000066c67000030a0000002f
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x4cb41e95d9073550210066161183dd92108401a2685a137648421006a1a1283dd92108533b045420d544842115e381c1869c121084019c0801cd21580210062921f744856008401aa080dd121580210062921c744856008401c24751d12158021006a82007448560084018c487dcd2158021006b02037348560084018c4871cd2158021007211d0734856008401ac0801cd215802132d07a5b651cd545013121f9855353d8d4032d07e5d54d4f635000181c831d95454d4032e071d483550625000141d9510d731894032e07214435cc625000160c935505218940006079d88355252500cb81c7520d541854000507654435cc61500cb81c8510d73185400058524d54144615000181e7620d5494540306071d883551505000103f985d4755923032d0724d751d5648c00103e9815376552300050764c54dd9548c00103e9815176552300050b654641c9644c0014359519071591300050b654431c9644c0014359510c71591300040f660549d9544c00103d98150765513030e0720c541d9544c00188c732096455130006251cc81591544c0c381e831d76450d30007051d474185314c0578e0805d9210843030507a53651cd54c40cb41e95d90735531000638a1d8018921c40c141c94594735521032d07255641cd548400141e93dd274d95100040fe61741d3654400141e93dd675d91100040fe61751d7644400141e95dce73d91100040f660549d954440c381e8315276551100040fa60541d9544400181c54a18735511030507a53651cd54440cb41e95d90735511000507a57749d3634400121f9855054d8d1000507e5d54153634400121f985505418d1030d0725d5415063440cb81e8510e7650d1032e07214431d9434400181e8710f6550d1030e07a0c75d9143440c181e841d76350d100048be6154153624400160c9355054d8910005832554310f624400122f9855054189100058324d54150624400160c9550c4318910007115d57318a2144001c85745cc628851015e381c286dc921440570e4981d9214811015e3820076485204400103f985d074594100050724d741d1650400103f985d475590100050724d751d5640400141c955cc73590100040fa6054dd9540400103e98151765501030e0720c545d9540400181c54618735501030507251651cd54040cb41c95590735501000487e615415263040c341c975505498c1000507255741d1630400121f985505458c100050725d5415163040cb81c8510f7650c1032e07214435d9430400181c8710d6550c1030e0720c7559143040c181c841d56350c100048be6154152620400160c935505498810005832554310e620400122f9855054588100058324d54151620400160c9550c4358810007099d67458b2104001c46759cd62c8410007219d27358b21040014e1969c97008410
  | 1 => 0x200461d4829758884b800000048600052f81ea42b2287e291518cae3d5c3215a9d0000000001d1d1781926949467f5d80010a532b1986003e8898e9f08afc00a2378cd6893002a800c1409f0003b0c1ed0ac91e270c2715a8e0be4844af54e73bb0d412662c000004a168bc000027a4516006589404140d990726b32c00585d001f800b0340008c273c849521e02a3ca2a135000e6006115400602c8813c00368c800c03389800074a02c3ab622054186c3d0dc20235c87c0c5a0684c6c71c703898000414081b0701001703220008030f00000a0202000d0004000200012d1802010330020b010215010700020b010002000001000027070904000e07150e0307030d0800081100507a58549ce615500141e9615173985540050ba58549ca6155001c0c5418e72985540050ba58545ca6155001c0c5418d729855400507a5854dcd615500141e96150735855400507a58549ce605500141e96151739815400507a5854dcd605500141e9615073581540050da5854dc56055001c145418f71581540050da58541c56055001c145418c715815400705194439c66250c01c146510d719894300703194439ca6150c01c0c6510d72985430070319443dc96050c01c0c6510c72581430070519443dc56050c01c146510c715814330507e59641cd549453721f985534358e513050725d54d0d639440181c83dd95450e51306071d083552629440141d9414d7398a5130607210535ce629440160c935504298a51006075d88355242944c181e7420d54582510050765053dcd60944c181e8414f735825132d07e59651cd549053521f985535358e4132d0725d54d4d639040181c83dd95454e4132e071d483552629040141d9510d7398a4132e07214435ce629040160c935505298a41006075d88355252904c181d7620d549464132e079d483551609040141d9510f735824132e07a1443dcd609040142d9499672d96310050b650539cb658c40142d9599272d92310050b654439cb648c40103d9815376552310040fa60545d9548c40184c73a0b6555231006231ce82d91548c4c141e93dd274d95310040fe61741d3654c4cb41e93dd675d91310040fe61751d7644c40103d9815276551310040fa60541d9544c40141d93150765513100705194649c6324c40103f985d074596210050724d741d1658840103f985d475592210050724d751d5648840141c955cc73592210040fa6054dd9548840103e98151765522130e0720c545d9548840181c54618735522130507251651cd54884cb41c95590735522100487e615415263884c341c975505498e2100507255741d1638840121f985505458e210050725d5415163884cb81c8510f7650e2132e07214435d9438840181c8710d6550e2130e0720c7559143884c181c841d56350e2132d07a57641cd5448
  | 2 => 0xd25b1f259882e2f1c90800298598a1c55a9904005d0012a6e000691a0000221306200114689b4d1095890572c80699201c0564743a4848503b8c5404b0200000833c218a800003280000402a09c00142cd6eaf0b8c09
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x49c2618088008038141080c100e5432829ae7314a260807ea19414f735825132c03950ca886b9cc52099601fa865443dcd60904c100e543262a0ecaa26200e081d4801d12158021007100e8400e690ac01099601ca8654435cc62500cb00e5432a21ae630a80608072a1931537655230
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x1
  | 4 => 0x4d
  | 5 => 0x4e
  | 6 => 0x4
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x124d
  | 10 => 0x124e
  | 11 => 0x138d
  | 12 => 0x138e
  | 13 => 0xcd
  | 14 => 0xce
  | 15 => 0x9cd
  | 16 => 0x9ce
  | 17 => 0x12cd
  | 18 => 0x12ce
  | 19 => 0x168d
  | 20 => 0x168e
  | 21 => 0xa0e
  | 22 => 0x130e
  | 23 => 0x20d
  | 24 => 0x20e
  | 25 => 0xb0d
  | 26 => 0xb0e
  | 27 => 0x140d
  | 28 => 0x140e
  | 29 => 0x24d
  | 30 => 0x24e
  | 31 => 0xb4d
  | 32 => 0xb4e
  | 33 => 0x144d
  | 34 => 0x144e
  | 35 => 0x16cd
  | 36 => 0x16ce
  | 37 => 0xb8e
  | 38 => 0x148e
  | 39 => 0xbcd
  | 40 => 0x14cd
  | 41 => 0xe8e
  | 42 => 0x178e
  | 43 => 0x209
  | 44 => 0x1549
  | 45 => 0x154d
  | 46 => 0x154e
  | 47 => 0x3cd
  | 48 => 0x3ce
  | 49 => 0xccd
  | 50 => 0xcce
  | 51 => 0x15cd
  | 52 => 0x15ce
  | 53 => 0x170d
  | 54 => 0x170e
  | 55 => 0xd0e
  | 56 => 0x160e
  | 57 => 0xd4d
  | 58 => 0x164d
  | 59 => 0xecd
  | 60 => 0x17cd
  | 61 => 0x98d
  | 62 => 0x150d
  | 63 => 0x150e
  | 64 => 0xa4d
  | 65 => 0x1409
  | 66 => 0x249
  | 67 => 0x1449
  | 68 => 0x289
  | 69 => 0x1489
  | 70 => 0x2c9
  | 71 => 0x14c9
  | 72 => 0x3c9
  | 73 => 0x15c9
  | 74 => 0x1609
  | 75 => 0x1649
  | 76 => 0xa0c
  | 77 => 0x409
  | 78 => 0x8d
  | 79 => 0x128d
  | 80 => 0x198d
  | 81 => 0x134d
  | 82 => 0x148c
  | 83 => 0x160c
  | 84 => 0xb0215
  | 85 => 0xb0216
  | 86 => 0x28c
  | 87 => 0x2cc
  | 88 => 0x14cc
  | 89 => 0x164c
  | 90 => 0x2cd
  | 91 => 0x19cd
  | 92 => 0x184e
  | 93 => 0x28e
  | 94 => 0x180c
  | 95 => 0x40c
  | 96 => 0x5cd
  | 97 => 0x74c
  | 98 => 0x1a4d
  | 99 => 0x194c
  | 100 => 0x14d
  | 101 => 0x58e
  | 102 => 0x1a8c
  | 103 => 0x18ce
  | 104 => 0x20b15
  | 105 => 0x5c055
  | 106 => 0x24211
  | 107 => 0x144211
  | 108 => 0x28211
  | 109 => 0x148211
  | 110 => 0x2c211
  | 111 => 0x14c211
  | 112 => 0x28251
  | 113 => 0x2c251
  | 114 => 0x5c955
  | 115 => 0x2c291
  | 116 => 0x5d255
  | 117 => 0x5d395
  | 118 => 0xa4c
  | 119 => 0x5d2d5
  | 120 => 0x58a16
  | 121 => 0x5c215
  | 122 => 0x5cb15
  | 123 => 0x44c
  | 124 => 0x5d415
  | 125 => 0x20b16
  | 126 => 0x5cb55
  | 127 => 0x59496
  | 128 => 0x58b56
  | 129 => 0x5d4d5
  | 130 => 0x5c0d5
  | 131 => 0x5c9d5
  | 132 => 0x5d695
  | 133 => 0x5c255
  | 134 => 0x5d455
  | 135 => 0x5d6d5
  | 136 => 0x5c3d5
  | 137 => 0x5ccd5
  | 138 => 0x5d5d5
  | 139 => 0x5d715
  | 140 => 0x1a57d5
  | 141 => 0x5c155
  | 142 => 0x5ca55
  | 143 => 0x59316
  | 144 => 0x5d355
  | 145 => 0x5d995
  | 146 => 0x5c2d5
  | 147 => 0x5cbd5
  | 148 => 0x58b96
  | 149 => 0x5d9d5
  | 150 => 0x1a45d5
  | 151 => 0xec5d5
  | 152 => 0x12c5d5
  | 153 => 0x5cb021d
  | 154 => 0xb45d5
  | 155 => 0xb4596
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 34
  | 7 => 1632
  | 6 => 6926
  | 5 => 3912
  | 4 => 204
  | 3 => 10
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
  | 8 => packedAt gbK8 (1024+((h/20+packedAt gbK8 (884+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (68760+((h/698+packedAt gbK7 (60384+(h % 698)*12) 12) % 3680)*12) 12
  | 6 => packedAt gbK6 (369058+((h/2615+packedAt gbK6 (332448+(h % 2615)*14) 14) % 9417)*14) 14
  | 5 => packedAt gbK5 (249203+((h/1415+packedAt gbK5 (230808+(h % 1415)*13) 13) % 5605)*13) 13
  | 4 => packedAt gbK4 (14832+((h/69+packedAt gbK4 (14280+(h % 69)*8) 8) % 249)*9) 9
  | 3 => packedAt gbK3 (825+((h/3+packedAt gbK3 (810+(h % 3)*5) 5) % 19)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff807ffffffffffffffffff3c3c3ff0fffff
  | 1 => 0x3ffff81f80f01ffc0fff00ffd3cfd13f44e73
  | 2 => 0xfc07fffe000ffe03ff03fff00e3f3e1cf8739c
  | 3 => 0x7fffffff00003fffc00000fc03fe0ff83e0
  | 4 => 0x7fffffffffffc000000000fffc000fffc00
  | 5 => 0xfff8000000000000000000000fffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8508000a2a12428481041545404140650194a5
  | 1 => 0x22d3a5815085116948eba02aa51c9d12744a52
  | 2 => 0x6845cad40109b4227a23caa02a2e2e18b86318
  | 3 => 0x4086f3679da02043bcf080c0cf8037a0de83e0
  | 4 => 0x83077c79e7cef9f0104103030ff7c000ef7c00
  | 5 => 0xf3e060410600c18020820c0c0ffbfbdf000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeae8eaa8eaa8a8a8eae8eaa8eaa8a8a8eae8eaa8eaa8a8a8eae8eaa8eaa8a8a8eae8eaa8eaa8a8a8eae8eaa8eaa8a8a8eae8eaa8eaa8a8a8eae8eaa8eaa8a8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37403
namespace PEqualNP.Outside.L_meta_37403
open PEqualNP.Outside.L_meta_37403.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 3 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 17 := bs0_4_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 21 := bs3_3_0
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
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 68 := (concat bs4_3_0 (concat bs4_3_32 bs4_3_64))
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
theorem bs4_4_128 : Interval s4Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 129 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 45 := (concat bs4_5_0 bs4_5_32)
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
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 68 := (concat bs5_3_0 (concat bs5_3_32 bs5_3_64))
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
theorem bs5_4_128 : Interval s5Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 129 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 45 := (concat bs5_5_0 bs5_5_32)
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
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 10 := bgb_3_0
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
theorem bgb_4_192 : Interval gbAtlas 4 192 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 204 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192)))
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
theorem bgb_5_3904 : Interval gbAtlas 5 3904 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3912 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672))) (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928))))) (concat (concat (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152))) (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 bgb_5_1664))) (concat (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792)) (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 bgb_5_1920)))))) (concat (concat (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 bgb_5_2144))) (concat (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 bgb_5_2272)) (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 bgb_5_2400)))) (concat (concat (concat (concat bgb_5_2432 bgb_5_2464) (concat bgb_5_2496 bgb_5_2528)) (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 bgb_5_2656))) (concat (concat (concat bgb_5_2688 bgb_5_2720) (concat bgb_5_2752 bgb_5_2784)) (concat (concat bgb_5_2816 bgb_5_2848) (concat bgb_5_2880 bgb_5_2912))))) (concat (concat (concat (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008)) (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 bgb_5_3136))) (concat (concat (concat bgb_5_3168 bgb_5_3200) (concat bgb_5_3232 bgb_5_3264)) (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 bgb_5_3392)))) (concat (concat (concat (concat bgb_5_3424 bgb_5_3456) (concat bgb_5_3488 bgb_5_3520)) (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 bgb_5_3648))) (concat (concat (concat bgb_5_3680 bgb_5_3712) (concat bgb_5_3744 bgb_5_3776)) (concat (concat bgb_5_3808 bgb_5_3840) (concat bgb_5_3872 bgb_5_3904)))))))
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
theorem bgb_6_6240 : Interval gbAtlas 6 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6272 : Interval gbAtlas 6 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6304 : Interval gbAtlas 6 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6368 : Interval gbAtlas 6 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6400 : Interval gbAtlas 6 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6464 : Interval gbAtlas 6 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6496 : Interval gbAtlas 6 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6560 : Interval gbAtlas 6 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6592 : Interval gbAtlas 6 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6656 : Interval gbAtlas 6 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6688 : Interval gbAtlas 6 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6752 : Interval gbAtlas 6 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6784 : Interval gbAtlas 6 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6848 : Interval gbAtlas 6 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6880 : Interval gbAtlas 6 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6926 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608))) (concat (concat bgb_6_640 (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832))))) (concat (concat (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024))) (concat (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)))) (concat (concat (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472))) (concat (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)) (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)))))) (concat (concat (concat (concat (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792)) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112)))) (concat (concat (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)) (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336))) (concat (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)) (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560))))) (concat (concat (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752))) (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976)))) (concat (concat (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072)) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 bgb_6_3200))) (concat (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)) (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 bgb_6_3424))))))) (concat (concat (concat (concat (concat (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616))) (concat (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712)) (concat (concat bgb_6_3744 bgb_6_3776) (concat bgb_6_3808 bgb_6_3840)))) (concat (concat (concat bgb_6_3872 (concat bgb_6_3904 bgb_6_3936)) (concat (concat bgb_6_3968 bgb_6_4000) (concat bgb_6_4032 bgb_6_4064))) (concat (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160)) (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 bgb_6_4288))))) (concat (concat (concat (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384)) (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480))) (concat (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576)) (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 bgb_6_4704)))) (concat (concat (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800)) (concat (concat bgb_6_4832 bgb_6_4864) (concat bgb_6_4896 bgb_6_4928))) (concat (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024)) (concat (concat bgb_6_5056 bgb_6_5088) (concat bgb_6_5120 bgb_6_5152)))))) (concat (concat (concat (concat (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)) (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344))) (concat (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)) (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568)))) (concat (concat (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)) (concat (concat bgb_6_5696 bgb_6_5728) (concat bgb_6_5760 bgb_6_5792))) (concat (concat bgb_6_5824 (concat bgb_6_5856 bgb_6_5888)) (concat (concat bgb_6_5920 bgb_6_5952) (concat bgb_6_5984 bgb_6_6016))))) (concat (concat (concat (concat bgb_6_6048 (concat bgb_6_6080 bgb_6_6112)) (concat (concat bgb_6_6144 bgb_6_6176) (concat bgb_6_6208 bgb_6_6240))) (concat (concat bgb_6_6272 (concat bgb_6_6304 bgb_6_6336)) (concat (concat bgb_6_6368 bgb_6_6400) (concat bgb_6_6432 bgb_6_6464)))) (concat (concat (concat bgb_6_6496 (concat bgb_6_6528 bgb_6_6560)) (concat (concat bgb_6_6592 bgb_6_6624) (concat bgb_6_6656 bgb_6_6688))) (concat (concat bgb_6_6720 (concat bgb_6_6752 bgb_6_6784)) (concat (concat bgb_6_6816 bgb_6_6848) (concat bgb_6_6880 bgb_6_6912))))))))
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
theorem allgb_7 : Interval gbAtlas 7 0 1632 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))))) (concat (concat (concat (concat bgb_7_800 (concat bgb_7_832 bgb_7_864)) (concat bgb_7_896 (concat bgb_7_928 bgb_7_960))) (concat (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)) (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)))) (concat (concat (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)) (concat bgb_7_1312 (concat bgb_7_1344 bgb_7_1376))) (concat (concat bgb_7_1408 (concat bgb_7_1440 bgb_7_1472)) (concat (concat bgb_7_1504 bgb_7_1536) (concat bgb_7_1568 bgb_7_1600))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 34 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 28, 30),(inputs.getD 2 zero, 26, 30),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 14, 30),(inputs.getD 5 zero, 14, 46)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 38, 54),(inputs.getD 5 zero, 22, 54)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeae8eaa8eaa8a8a8eae8eaa8eaa8a8a8eae8eaa8eaa8a8a8eae8eaa8eaa8a8a8eae8eaa8eaa8a8a8eae8eaa8eaa8a8a8eae8eaa8eaa8a8a8eae8eaa8eaa8a8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941132968 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37403.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,2]⟩,⟨.or,[4,5]⟩,⟨.and,[4,5]⟩,⟨.and,[3,7]⟩,⟨.or,[0,6]⟩,⟨.and,[9,10]⟩,⟨.and,[6,8]⟩,⟨.or,[0,12]⟩,⟨.or,[1,2]⟩,⟨.and,[13,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132968 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132968 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37403

open PEqualNP.Outside.L_meta_37403 in
theorem PEqualNP.Outside.L_meta_37403 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132968 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132968 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
