import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37007.Model
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


end PEqualNP.Outside.L_meta_37007.Model

namespace PEqualNP.Outside.L_meta_37007
open PEqualNP.Outside.L_meta_37007.Model
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

def SBf (j : Nat) : Nat := [6, 7, 7, 4, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37007

namespace PEqualNP.Outside.L_meta_37007
open PEqualNP.Outside.L_meta_37007.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x400025a809184a031c800c7be42bc42de32dc32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1180c400940418c420ca58a4a0ce14141a7294632e5290298a4985514530
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (208+((h/4+packedAt s0K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s0K3 (197+((h/2+packedAt s0K3 (189+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffe07fffffe07fffffffe03ffff1ffe3f
  | 2 => 0xffc0fffffffffffff81ff80fffffffffe38fff
  | 3 => 0x3fff01fff80fe03fffe0fff03ffc0f80fcf3cc
  | 4 => 0xc00001fffff0003fffff00003ffff000ff03f0
  | 5 => 0xfffffe000000003fffffffffc0000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4a4414423122490a01652a544a2194aa0d3615
  | 2 => 0x909228a442449414580a510a94c629546288ea
  | 3 => 0x230a4d2890e90566aaa09d6227688e06b4d34c
  | 4 => 0x3a2cb1d12481d9bb34d3064c39b3c418df03b0
  | 5 => 0x3c30c1e1c70e1e3dc71ce78f01c30860fbec00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37007
namespace PEqualNP.Outside.L_meta_37007
open PEqualNP.Outside.L_meta_37007.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x100009419240101b5e9d50e562c888285800918291802678380300c004441920f008402c029801c0000b9f1a954ad2a14eae348c0200100081382046045286ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x83098000000300a03a001180d0a151d9f4d8002e94028473b1a902683b8d42e063f17c0000219ec002b0d800004c21000123a3f800a671378f0626d001e40000001549c801c8a8e61a13178f8070f18c4a2c00000cc001e9d0000400000000b0c800884a0109c0000201700a6700000008200000005911000c4003d1e0a8453585800000f8205a0a008c0202100190660f348bc3052090b800201f10400462400096653913d08321a000ae002b000525b00000000030838220000000000c28890923f380e0dc00268d8385a0000000003a8001a3700160000000004080408040004040000140c101c0400380c000c0400001ce40c00180c08000020040824000000180c5804067ca5a1cf547439f286873d5490edea4a1db14943cfa9a87af5250e78a4a1eb1494396292873f5150e78a0a1cf950439ea9c853e5290a7aa3214f942429ea98853e5210b5ca4214f544429f280853e54cca7aa9996b10b32bb28e657551cca7ea9194f152329faa2653c544ca7ca8194f55032d6210653d53d067ca5a0cf943419eaa4836f52506d8a4a0cfd4d41d7a92833c5250758a4a0cb14941dba8a833c505067ca820cf953319eaa6636e52cc6daa598cf952319eaa4636e528c6daa518cf951319eaa2633e540c67aa818f54c4319faa6433c54c867ca910cf55221af29c435d53887588510cfd51219e2a2433e540867aa810eb10821b7294816d529027aa7204f94a40d7294812e529035aa5204f546409f284813d531027ca4204f544409f28081ba501027ca9984f553309faa4613c548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320d6216413e548827aa9104fd51209e2a2415f53482b8a6906b10920bba8a4174514827ea8104f150209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xa8080e4080009800247000000025000062806840000000000000280160306007800008b2012000b0cb800001000420000038b18951d0e2e6294343c910a51cca3561152328b594420ca8d63108328b18953d062e62943418b189544c63860551318b189540c61d6315321c394c428862d6510821a9584420862c6254c408b189511022c62553308b98b548c30c5310920c9108514822e62d50208758c540823561150208b18954c422e62d5210
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s1K5 (864+((h/16+packedAt s1K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s1K4 (3970+((h/44+packedAt s1K4 (3618+(h % 44)*8) 8) % 194)*9) 9
  | 3 => packedAt s1K3 (1036+((h/8+packedAt s1K3 (988+(h % 8)*6) 6) % 58)*6) 6
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xe0ffffc0fe0fffff0783e0fffe1e07ffd23e4f
  | 3 => 0xff03ffff000fc1fff803ff07ffe00781e3cf8c
  | 4 => 0x3fffffff001fffffc0007fffff801fc0ff0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x20080888240200002904a108802290a404d095
  | 2 => 0x4a3191064894b0cb02a148d332142558d2264a
  | 3 => 0x865aa2921d29135558427a45d540560d634b8c
  | 4 => 0x14a344249181a5a694e8108669996011b80d60
  | 5 => 0x18c38738e1ce39f8e7739ce071118461ffb000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37007
namespace PEqualNP.Outside.L_meta_37007
open PEqualNP.Outside.L_meta_37007.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xd100000a007cb2a0a013173c456801c4c4ac3a941280e500153200e2420000001e1862934ac900408d1211610c01069cd960031400080c10052400deff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x6410000000000000070000241e2c2a625b38720000005637514e2600000000004d05000e03000d400000490000000071424f570000000043004b00125c00003b654c0000310c063a2160290000746f276b1c687000002e472d00341400001900000000000035586723636c2f0b53001b000000006600001f00444500330000000a000000160008005500004152004a610000000000000100000004001d2b0000002502001318006a3c6d005f54362017111a3f32395e503e005a15466e69280f732200485930005d000009003d000a000500000000008001000382870002010100800000810288000680000009800300008001805b94a43b6a9487765190eeaa321dd94742baa8e853e5290aeea2a15d14542af298855d5310b3ca6216754c429f29085ae5210a7ca9994f55332bb28e657551ccb5885194fd51329e2a265ac424caeea2995d14532bda826578504cadea4a0db14941daa08833e54cc67aa998db94b31b6a9663b642c87688590cf952219eaa443ac42886eca310cfd51219e2a2435e53086baa610eb10821eb29843d553086eca410f994821f3a1043b642087688410f910821d221043e632087ca6410d794f40aea9e815f53502b8a6a05bd4940b6292817751502e8a2a05d94440baa88819e428c338851875c8630ea10c615e508c27ca8184f55030b7290616d520c2eca2185d54430cf2a0619d540c39ca4187354830cf210619c420c3aca2187554430eb90861d4210c2bca0187694030af29e415d53c83b061904f952209eaa441ac42882eca3105d54620f210c413f5448278a89057d4d20ae29a417751482e8a2906b10820f210841d830082bca7885754f109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x400688070022868092e00a60e42048009e5a6314aac00b004c432c9108514cb284214132a9189411070d5310821a998a42086c56310821e198c42087856310821e194c42087855310821a919132086e0604c8219918951103844208630c3551520c21d6510830d1549510c2556508430e1108210c3244294620c99502188388420c020f0084300822c6255010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xa6000a0aeb3188410c857694c4208682ba88410861815944208430
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | 2 => packedAt s2K2 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (826+((h/15+packedAt s2K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s2K4 (3471+((h/39+packedAt s2K4 (3159+(h % 39)*8) 8) % 205)*8) 8
  | 3 => packedAt s2K3 (952+((h/8+packedAt s2K3 (912+(h % 8)*5) 5) % 29)*6) 6
  | 2 => packedAt s2K2 (199+((h/1+packedAt s2K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xff01ffffffffffe07ffffe03fffffffe3f1fff
  | 1 => 0x7ffe07f01fc07fff83e07ffc1f07e03fd9e267
  | 3 => 0x7fffffffe0007ffffc007ffffff8003fe1ff87
  | 4 => 0x800007ffffff81ffffff80001fffffc1fe03f8
  | 5 => 0xfffff800000001ffffffffffe0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x14c11124488104014a49641230a29a20b0cab
  | 1 => 0x2a14b321c91aa4e5816c2ad50d4742b4d96265
  | 3 => 0x4c28644483a3492aac104d1a56d1051960b786
  | 4 => 0x68b1468912320db34a59019218e59611f40350
  | 5 => 0x70c1870e1c3c71dc739e71e380861821bfd800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaee00aaaa8800eeaaee00aaaa8800eeaaee00aaaa8800eeaaee00aaaa8800eeaaee00aaaa8800eeaaee00aaaa8800eeaaee00aaaa8800eeaaee00aaaa8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37007
namespace PEqualNP.Outside.L_meta_37007
open PEqualNP.Outside.L_meta_37007.Model
def s3K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*4) 4
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (5+((h/1+packedAt s3K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xdbf19f3f1c3f8d9c
  | 2 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 1 => 0x24ac285909932594
  | 2 => 0x1101502242244a0a
  | 4 => 0xe091ab493064f40
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 23 s3Pos s3Neg, 0xeaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37007
namespace PEqualNP.Outside.L_meta_37007
open PEqualNP.Outside.L_meta_37007.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xa4820006000be43bc43bf42bd42df32dd32
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x225aa421e350932
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (104+((h/2+packedAt s4K4 (96+(h % 2)*4) 4) % 9)*4) 4
  | 3 => packedAt s4K3 (56+((h/1+packedAt s4K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3ffc0ffffc1fc1ffc1ff07fc3ffc0fd8f33f3
  | 1 => 0xfc0fff03fffe0fe0ffe0ff83fc3fff02f1ccfc
  | 2 => 0xfffffffc1fffffff0000ffffffc3ffff01ff1f
  | 3 => 0xfffffe0000fffffff0003fffc0003fe0fe0
  | 5 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x48644628849284052d093424c0664258871171
  | 1 => 0x19248a19091094a0552854a1442a9608b144b4
  | 2 => 0x208910405221094a0210894a2a8128a300aa0a
  | 3 => 0xb2ca249243a52a739a520843b3100c335a0fc0
  | 5 => 0xc30c38e39c39cf9ce39cee70222230c3edf000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeee0eee0e8e0e8e0eee0eee0e8e0e8e0eee0eee0e8e0e8e0eee0eee0e8e0e8e0eee0eee0e8e0e8e0eee0eee0e8e0e8e0eee0eee0e8e0e8e0eee0eee0e8e0e8e0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37007
namespace PEqualNP.Outside.L_meta_37007
open PEqualNP.Outside.L_meta_37007.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc817e52902faa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c53502fea4a05f14940dfa1281bd42502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881bf411037a82205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef18e61dc31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa518778ca30ee194617e518c3eca3185d94630bea8c61f5518c2eaa31877cc630ee98c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930ef99261dd324c2fea2985f14530ef18a61dc314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861df430c3b886185f94830bea9061de320c3b864185f94430bea8861df310c3ba62185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483dc84907b50920bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2105f94020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10ef29c215e53842faa7087754e10aea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fb98a21f431443ec42887d48510fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe5390bbca7215794e42bea9c85dd5390abaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332efa1e65dc43ccafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7197790e32eea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132efa1a65dc434cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0995f14132bfaa0657e540cafaa8195f15032bf29865de430cbba86195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7b88718df94a31bea9463de328c7b86518df94631fb20c63f5418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7bc8698f750d31bfa92637c524c7be6498f74c931fb20a63f5414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fb20e43f541c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e51087ec8210fd50421fb98843f431087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40dfa1681bd42d02fca3a05f54740beaa4817e53902faa7206f90e40de21
  | 2 => 0x20c188002960011a9d148e608578dc1206e49716600047c0000034c96c00000174644000000f460c118b13dc478000001e86f03a00021a97c00169126000f99130000000016707e6c00000022c9f80024d0008e11286b428520000000000000000400072400000288140000000009080004503c00055000418000000002208a8000004080000000000028c001fc000000000e120c3bc000d9000000000003bc6844a8001968dc0015503e00000000000518d61a54765e0000004404481e8b222e130001500009a800000526154002292600000019d3c60013aa6800020800000182000ea80051a3a0ba2700009885a8003120003988f000885358bc00043c000003ea9cc0006449c10402a2b000330bd8000000012e800000000001f652e98cf813b160000631752941fc001b6000000a68795060dc0014000095c0000033223400000000000e18000000013a0702de0ac9e9423b0374f7800000000001081d60009111952a99d2624a3022642fa613684000028a00081c000c03409bd29921374a10cd82622a6000000000049c000000006ac0019600029000000004000000000000008200001c00012000000a442400029200000000036000d90cf0000008e0383b60013e02e06c3081106f3ee4e0e400a3cc7b4dc000000000000000000000017d0002a06d00020e5dc7fa5a37e17800000000424000000000008580008c5680017124a6b40023f1940480000000100002002000002000010000060100180002c000010020020000000000800801805014000000000000040000000001402006002000018000000000980200c00400002002000020000020180000300a00001000004000000000120100080a00000402800000020000010000100080300001c0080e0040100000200002c0100100001004007014008010000280140080200e000020080060000080300000000004006008030010000040500800600000804000000000090000080300200000400002000008028010060000680100a00004006000008028020060000080000e00002005004000020040020340180600000c000050080140780000000c018000060240081d0020000000000e0080000a004014010020000040080000000000004000004040020060200080000200000000bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf28887f65110eeca221df54443faa8887755110efca021df54043bf29e85de53d0abca7a15f54f42eea9e855d53d0b7c87a16f10f42bf28e85f651d0aeca3a15f54742faa8e857551d0afca1a15f54342beaa4857
  | 3 => 0x1683e8940a7000000da8330008691f000112000001312b60003f000000110000000002ccfa21700000000212000000000083a4000850004a0565388002e61680009f13654d3d9cd3148047c9203ba8900a1f1218a3cec9be1ca38d2c00016e00000000000000000000001b4e98004f00000000000000c000000ce000000520000c03c00000000000000000000000000000013c800096000000004609011a0f5000000002280000004600034e770c98a6000000000003380002100012c288000003ce5ac000720740000017a21c1a8298810000001f152228320002600009b11d0004b84ac799bd2bc9e85f1af00040ceb89d0c61d9471a936646c0007d02e2100e1c400000000213052000000003fe324250001cc5c00005c3ca4440c8fc01a9190c0473d28c48d2720645f800000000000508000000006b2650000014600028a9240016e1520ece000029e61c10a1d0409541c800000000e09a30008e416800034000000001dc001330002ae000001da00000000000204000702903c486d348cd2f869030000000000000003983f4b005715aa50e389a0d80000012300000000000000000000000002b94424f0001740009145a100c28011703549925900082c9f800414000ae1393203906ba5419c7f5220000008449e0000000000024b0005e52b0062ac188b2a10000001070003d0000978713e4000aa0691ee378a8818000000000001d489c7d8000006dc3e02700000144935384000ca18b18e000000a039c0009216c0ee000af8002300014921540a000000150000004299740c3c8001e1000000000002ec150128fe00000000000258000000003d4a1cd500047a000a08e93500000014e03a3602c8003c07b0000ab3f40013b0160000000000048a000000000000000013e000820bfa2f1b68640018e13c0a8340df0000000000000004c000f809c03c00137128000000001a42e496a48000634000002d077c038000000000000000088d3b947396728000001a62ec0000026c0b0089ae4c8000000000005a80498f0209fd4b164186000331bb14a7e4e300012e001068280005c8ac0981163103aa1f00000000000504220c90610000000000050c824a1a1620aa2cfc03c000000e295d0009b41a8001c400000000000218628000008d8000000002005607b4bc14400000000610e78000007ec000f101800000000000001370000000005f9261a8000c30000000000000000000000000000000248002984a8000003d680cca8000000005e8003a05b4001880b039c000000002380000000000094a320000000028133c0000002f4445842b13444c3c000000000248cc2333a83d9162850009f49984d00000121a801380005b03447867d078653c8405170001d800000000114000000000000000016200021c3711d016668002411da8700000000
  | 4 => 0x16c2180036200027a512c64e9001fe31887868000000759290d1344000000000008080000000000000000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5520c274615483097596320c29e648c83097d95310c25f654c030a7191300c27b654c0309798f54c825d63d53209798e54c825d63953209d98654c827561953208f99353c823d64d4f209dd8553c82746154f2097d8d51c825c635472097d8d548825c63552209798c548825d63152209d984548827561152209d987538827561d4e208fd91538823c6454e208f992518823d64946209798e518825d63946208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120cb588544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534832c54909209b195424833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c514837160145209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510832d54c8020dc546200826f6548020cb551200827b6548020dc545200825e63d53109758f54c433661953109798c54c425d63153108f99353c423d64d4f10c795253c431d5494f10c795153c431d5454f10d518553c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c425e6314b109758c52c43555390710cd95141c42d46350710d554d41c435553cc710ad59031c42d463487109798f548425d63d52109798c548425d63152109b988548426d62152109798f528425d63d4a108f990528423d6414a109798c528425d6314a10d594f21843565308610bc58021842f06148210d594f108425f63551109718d544426f62551109b189544425e63151109758c544423f6454d108f191534426f6254d109b189534423f64549108f191524425f63549109718d524427761549108f990524423d64149109798c524425d63149109d19541442d46350510bc181414427665cc510ad590314427665885109d19521442d463485109e19520442d6638411097d8d540425c63550109798c540425d63150109b988540426d62150109d984540427661d4c108f990530423d6414c109b988530426d6214c1097d8d520425c63548108f990520423d64148109798c520425d63148109d984520427a60148108f992510423d64944109798e510425d63944109d59721042756508410bc580210425e63940109758e500427965840109dd95100427b6544010
  | 1 => 0xc79743506319b98a544c66d629513197d8d544c65e6590d3197195434c65e65cc931b5185324c6746550531e550d414c63d6595031c718d540c63e64150319798c540c676611503197597430c71d54d0c3197594430c71d5410c31b5584430c65d658c831a7992320c71d548c831c7550320c71d54cc431cd552310c65f654c431c7551310c677654c431cd551310c65e63d53219758f54c865e63953219758e54c863e64d4f218f59353c86d46350721ad59031c863f64543218f19150c865f63543219718d50c865f63552219718d548865e63152219758c548863e6414e218f590538865e63942219758e508865e63951219758e5448675619512197d8d544865c63551219ed81544867860551219798e53486776154d2197994534875453c85219798f540865d63d50219e983540867960d50218f596540873661950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c21d5185530863e6414c218f590530865e6314c219e98053086796014c219d59641087555390421cd95141086d46350421d554d410875553cc4219d59431086b5640c4219bd9521086776548421b518d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50087724154021dc50550087733154021dc0c550087722154021dc485500865e6394b409758e52d025f63547409718d51d02b56110e4097d8d529025c6354a409dd8552902746154a40a798e429025e63946409758e519029c63506408f997425031c53d0940c714d425031c5390140c754e43102b56110c40d394e521034d5394840d394d521034d5354840cb90d521032c43548408f596421029e6390840cb54a421032d5210840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440c754f411032d52d0440a718d411031d5350440cb54941103365150440cb54b401023f6550040a718d401032d52500409ed95401027661153309d58454cc23e6494b308f59252cc2d4614cb30a759031cc27661d52309d587548c26e62152309b588548c27661152309d584548c2d56110e30a7992328c23e64946308f592518c3366494630cd592518c3574394630d510e518c3563294630d50ca518c35651cc630d5945318c35651cc2308f992544c25f63551309d984544c27561151308f994544c31d6315130cd984544c335611513097996434c31c5490d3097195434c31c5450d3097997324c31c54cc930c7151324c2d4614c930c7152314c25e650c530a7590314c31c540c530c7152304c2d6618c1309798c540c26e62150309b588540c27661150309d584540c25d65d0c3097594430c2d56110c309dd8
  | 2 => 0x370000772607680002e0cc000c4a19000000000002b2284c50000000e8000ad0c0000000bb0000003c8000fc244461b73aa28ca183b3de4241e1f800000000024000000df00010a0008d8002cc4700004441e0006c00029012cbb8000000003186f000000001a3000000740000004f47a8300001acc10004203d8b10000dc0647f0003c00001180021a000e804a248000be8000006b4f7000000000000000ec52c00000000000111b511a62c4a87409e21cb40521c60005a800000264cb8df000000a8165000428000003724dc8180821e440aa0411622e8fea16028414871b43827d08c9aa3a209800000000304dd9dc39a6390916c000380f39b30007acfb0f90005a400000000000421d7244078938940000000009f2800000000000001c02004030080000c000000000000020020080b00002038050080000c0000c0203401000020000100001038060140000000004030080a00406000000000c03404004020080b0041200800030080000b0000b004010100201806008030000000004000020100701002010010000a05c050040000c000400400c0101c040000001809004020000e008010080000400004030000200001004020440e0000201c0901c000340401c030040000000010080040e0101a00001004000040500003018000040301c000040300c0b0000200400008000080a00000000010080000000002776154a439d1855290e7661942439d5865090e3f6550c4397d954310f374354443d590d5110f354354443d550d5110f1d5390f42ad58443d0b565394742d554e51d0b565354742d554d51d0b1e53d0a42ad5844350a9e63909429798c5150a5d63145429798c5050a5d63141429d9845050a7561141428fd954210a6f655084297d8d5110a5c635444297d8d5010a5c63540429d98454cca756115332b558443cca7661943329d58650cca7661952329d586548cb1d6395232cd986548cb356195232c7952438cb1e5450e32c7953328ca5d63951329d986544ca7561951329dd85544ca7461551329ed81544ca78605513297997434ca5e6510d32b5584434ca9e648c9328f990514ca3d6414532cd990514cb356414532d5d0c514cb544314532d58c8514ca5e63d50329d984540ca7561150329e980540ca79601503297596430ca5f6550c328f992520ca3d649483297d95320cad4614c8329bd95320ca3f64540328f191500ca5e6394b419758e52d069d63d0b4197d8d50d065c635434197d8d529065c6354a419798e509065d6394241d5584535071c53d0d41a758f425071c53d0941ad987425071c5350941cb149425071d53d0441d554e411063f6550441c754d41106776550441d554d411063e6494b318f59252cc6d4614cb318fd9150cc63c64543319e983548c67960d5231b5584438c69e648ca31b518d418
  | 3 => 0x560004c09b3e600090a082e27483980038a054bf186374804c98a74302b8de0000703983d988022070001fa0000009902c00072c028002ac0000015c000000188002547c02d00f20e330eb00002c2f4059b10c8204472171aa548c783d400134aa90c00000000000000458478f71d4000511ea0000000014600010000000000000b38d20060000014c000000ca8542821b000000000478001af000000000000004ec4901d25c0002280004269c7a0a90a0000139730d47b4391020ba0a8678c4052418611601a806c098ab13c2ccb21762520000001019a6a0820b93061a0400002da0e4002130000007e9e23c24e8649390025c8769e8000000000d100066cc204222e5e400000000068001d80000001b00000042c00000148000000430b60000000000031c00191000184a29a000024000000000000000002f800000000352000001ae406400650e41d2658c3957330000000001b4000d200037e3cc00000000000ce9b20000000000033c19423846000444bd20a2bc6880000000000000000064000cd0000002d0001db1065109f1d40003e0000fa3ca4744401833e7009305709c00000000000000580000000007e142342000311c80b20000014d18a0000012c000000000d900e0004494a10c4b4b08000aa6c0ee8ef41a000db1cc3383acfe1f50f8000241510001245f1df0d200000000000000000170000305916b3fe469038000000940f98c3f24bc640e512c5d0ca13f1582f03d20b3e40a0000931f669845133134010de856000298000000007180015b0000005f8750000004b8d30007dc000122027a4000000b03c8a980000036c00113000338c811f18c179049ca1e0001070090be614ae8b71bc7788c0e1000480f889c14a5fc9b1e329257c00114000000001cf15e83000206000664000002dc000001c305e4ad011c4278814000003023000012338e000789081d8000288d7000000000353705600000e000028068ff39c51c770e21164d0001ac0002a000000434080c00340b84486e9700e0000000671702744114e34a1b4001c900058cff0d63d80003c1d300000000000000494e120400000000000000000989380004a05b000098000001921a00003f8000000000016f31a7641f1153f6854f20aa0004d4000000001f400000000000bc0c32b4798000000008440000000000029800000000a78cb35600073a14000000000002ea008000002d40b4bd80606e1c4198a007e0000000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x751558b00001101300500000100034000928048c0040003830004002000000000000000065c00003d8080001001820018558d6195232a2ae32a28719516748c8514ca4aba0c299263855516110c3183eecaa46418d1574185530862a3b2a6a0843541cd4154021a62e818aa010d50734855008692b8886a90818398d5290840c18c6a92822060c63549401028b3a46528c61455d2514c630c2ac6b08a89851571151434c30a2a0c299261075d8540c530c28a930c60985157418553c422a3b2a6a0e219494d6008610
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x800000340815869d23214532815869d2329463081587150614c93081587152618c130
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1164)*11) 11
  | 4 => packedAt s5K4 (22272+((h/179+packedAt s5K4 (20482+(h % 179)*10) 10) % 860)*11) 11
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 57)*6) 6
  | 2 => packedAt s5K2 (244+((h/1+packedAt s5K2 (240+(h % 1)*4) 4) % 13)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x83ffffc0fffe1e0f0fff0ffff87fe07c39f3f3
  | 1 => 0xfc0f87ff07ffe3f00f87f1e07f8fff8226ccfc
  | 2 => 0xfff007fff87ffffff007fe007ff0ffffc70f1f
  | 3 => 0x7ffff8003fffff800007fff0003f80fe0
  | 4 => 0xfffff800000003ffffffffff80000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x88610046100420010189022318112118085171
  | 1 => 0x19224c8a3229065086c391452c8a4b0a22c4b4
  | 2 => 0x20841110415000a61004240841209460c50a0a
  | 3 => 0x72cb6624a51d4b3bab508112764c0633780fc0
  | 4 => 0x430c4438c66193cccc66c99c04081843b7a000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfaeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37007
namespace PEqualNP.Outside.L_meta_37007
open PEqualNP.Outside.L_meta_37007.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x129c72b000c6247e800000064a263cb5806005802a34d96004441f0224d4505502079778e0f847494d8064343800084a9102f58805201a2300cc01c76e40000001b8b5c000005e4ce9801000800112180821400b800005280140040001ffd5007fe5401ff55007fc5401ffd4c07fe53005f94c07fd5301ff14c077c53007fd0c01fe43007f50c01fc4301ffd48077f52017f94807fd52005f54805fc52007fd0805fe42007f50805fc42007fcc805fe32007f4c805fc3201ffd4403fe5101ff54403fc51007fd0403fe41007f50403fc41007fcc403fe31007f4c403fc31017fc8403fe21007f48403fc2101ffd4007fe5001ff54007fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30017fc8001fe20007f48005fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24004ff08120027d8409000bf82048015ff8824004ff04120027fecb08012ff6584009ff32c2003bf99610027facb08026fd6584009fe32c2004bf19610027fec908012ff6484009ff3242007bf99210027fac908002fd6484009fe3242004bf1921004ffea908027fe5484013feaa42009ff15210027fec708012ff6384009ff31c2000bf98e10027fac708002fd6384009fe31c2004bf18e1004ffea708027fe5384001bf29c2009ff54e1004ff8a7080277c5384001ffa1c2000ff90e10007fa8708003fc4384009ffb142004bfd8a10027fcc50800afe6284009feb142000bf58a10027f8c508012fc6284013ffa942009dfd4a10047fca508027fd5284001bea942008ff14a10007fe8508023fe4284001fea142008ff10a10007fe6508023fe3284001fe9942008ff0ca1000dfac308007ff5184003ff28c2001ff5461000ff8a308007ff4184003ff20c2001ff5061000ff88308007ff3184003ff18c2001ff4c61000ff86308007ff2184003ff10c2001ff4861000ff84308012fe6084009ffa842004ff94210027faa108013fc5084009ffa042004ff90210027fa8108013fc4084009ff9842004ff8c210027fa6108013fc3084009ff9042004ff88210027f44108013fd2084001fc9042004ff08210027fe2108013f71084003fd8842004ff04210027f0210801bff654400d7fb2a2000dfd9510004feca8801bfe65440077f32a2006ff59510035faca8801bfc65440077e32a2006df1951001cf8ca88003ff64440017fb222000ff9911003dfcc888003fd64440017eb222000ff1911003df8c88801bff544400dff2a22006ff55110037f8a888003ff63440017fb1a2000ff98d10005fcc688003fd63440017eb1a2000ff18d10005f8c68801bff534400dff29a2000df94d10037faa68801bfc534400dbe29a2000ffd0d10007fc8688003fd4344001fe21a2000ffd8910005fec488017fe62440057f3122000ff58910005fac488017fc62440057e3122006ffd4910036fea488017fe524400dfea922000df5491002ff8a488003ff424400bff2122000ff5091002ff88488003ff324400bff1922000ff4c91002ff86488012ff6144003ffa8a2001ff9451000feca288007fd514400dfaa8a2001ff1451000ffe8288007fe4144003fb20a2001ff50510007ea8288007fc4144003ff98a2000fdcc51000ffc6288007fd3144003fe18a2001fd0c51000ffe4288007fe2144003fb10a2001ff48510007ea4288007fc21440037fb022006ffd4110027fca08801bfd5044009fe2822000ffd0110027fc8088003fd4044009fe2022000ffcc110027fc6088003fd3044009fe1822005ffc8110027fc4088003fa2044001fe9022000fe48110027f84088007ff1044003fd8822004ff84110027ec2088013fc1044009fa0822001fe04110
  | 1 => 0xbfe310c001fe988600eff0c43007ffe421803bfe210c001fe908600eff08430025fcc018013ff500c009ff2806004ff54030027f8a018013ff400c009ff2006004ff50030027f88018013ff300c009ef9806004ff8c030027f46018013fd300c009ee9806000fe4c030027fe4018013fc200c009ff8806004ff04030027fecb10012ff6588009ff32c4003bf99620027facb10036fd6588009fe32c4004bf19620027fec910012ff6488009ff3244007bf99220027fac910002fd6488009fe3244004bf1922006ffea910037fe548801bfeaa4400dff15220027fec710012ff6388009ff31c4000bf98e20027fac710002fd6388009fe31c4004bf18e2006ffea710037fe5388001bf29c400dff54e2006ff8a7100377c5388001ffa1c4000ff90e20007fa8710003fc43880057eb144002ffd4a20016fea51000bfe5288005fea944002df54a20017f8a51000bff4288005ff2144002ff50a20017f8851000bff3288005ff1944002ff4ca20017f86510013ff6188009ff30c4001bf98620027fac310002fd6188009fe30c4004bf1862006ffea310033fe518801bfea8c400cff14620007fe8310033fe4188001fea0c400cff10620007fe6310033fe3188001fe98c400cff0c620017fe431000bfe2188005fe90c4002ff08620025fcc110013ff5088009ff2844004ff54220027f8a110013ff4088009ff2044004ff50220027f88110013ff3088009ff1844004ff4c220027f86110013ff2088009f79044002fec8220027f84110013f82088009ff8844004ff0422005ffeca9002eff6548017ff32a4003bf9952005ffaca9002efd6548017fe32a4003bf19520007fec890002ff6448001dfb224000afd9120007fcc89001efe6448001feb224000bf59120007f8c89001efc6448001de3224000af1912005ffea89002ffe5448017feaa2400bff15120007fec690002ff6348001ff31a4000bf98d20007fac690002fd6348001fe31a4000bf18d2005ffea69002ffe5348001bf29a400bff54d2005ff8a69002f7c5348001ffa1a4000ff90d20007fa8690003fc43480097fb124002ffd4920016fea49000bfe5248005fea924002df54920017f8a49000bff4248005ff2124002fb90920017fa8490003ed4248005fe2124002ffcc920017fc649000bfd3248005fe1924000ffd8520005fec29002bfe61480037f30a4000ff58520057f8c290006fc6148017ffa8a400aff9452005ffaa29002bfc5148001ffa0a400aff90520007fa829002bfc4148001ff98a400aff8c520007fa629002bfc3148005ff90a4002ff88520017fa429000bfc21480057fb02400bffd4120027fca09002ffd5048009fe2824000ffd0120027fc8090003fd4048009fe2024000ffcc120027fc6090003fd3048009fe1824002ffc8120017f64090013fe2048009f71
  | 2 => 0x30007fe851805bfe428c001fea146016ff10a30007fe651805bfe328c001fe9946016ff0ca30027fec318013fe618c0037f30c6004fd9863000decc318013fd618c0017eb0c6004fd58630005eac318013fc618c0097e30c6017ffd46300affca31805ffd518c02bfe28c6000ffd06300affc8318003fd418c02bfe20c6000ffcc6300affc6318003fd318c02bfe18c6016ffc86300affc4318003fd218c02bfe10c6004bf98230027fea118013fe508c009fea846004ff14230027fe8118013fe408c009fea046004ff10230027fe6118013df308c001fd9846004ffc8230027f84118013ff108c009fe0846014ffd95300a5feca980037f654c0013fb2a6014ff9953001dfcca98053fd654c0297eb2a6014ff1953001df8ca980537c654c0073e32a6000ffd9130005fec898003bf644c0015fb226000ff9913003dfcc898003fd644c0017eb226000ff1913003df8c898003bc644c0015e3226014ffd51300a7fca898053fd544c029fe2a26014ffd4d300a7fca6980037e534c029fea9a6014ff14d300a6f8a698003ff434c001ff21a6000f790d30007fa8698003dd434c001fe21a6000ffd8930005fec49804ffe624c0057f3126000ff5893009ff8c49800afc624c029ffa926014dfd493009ffca498053fd524c001bea926013ff14930007fe849804ffe424c001fea126013ff10930007fe6498003df324c027ff1926000ff4c930007ba649804ffc324c001ffb0a6000bfd8530097fcc298006fe614c001feb0a6012ff1853000df8c298053ff514c025ff28a6014ff54530097f8a298003ff414c025ff20a6000ff50530097f88298003ff314c025ff18a6000ff4c530097f8629804fff214c025ff10a6000ff48530097f84298053ff504c009ff2826014ff54130027f8a098003ff404c009ff2026000ff50130027f88098003ff304c001fd9826004ff8c130027bc609804fff204c009fe1026012ffc4130027f82098013ff650c0097fb286004ff9943001dfcca18013fd650c0217eb286004ff19430025f8ca18013ff640c0097fb206004ff9903003dfcc818013fd640c0017eb206004ff19030025f8c818043ff540c021ff2a06010ff55030087f8a818046fe630c021ffa986010ff94c30006fca618043fd530c021fe2986010df14c30007fe8618003fe430c001fea186000ff10c30027fec418013fe620c0057f3106004ff58830005fac418013fc620c0097e3106010ffd4830086fea41803ffe520c021fea906000df5483007ff8a418003ff420c01fff2106000ff5083007ff88418003ff320c01fff1906000ff4c83007ff86418013ff610c009ff3086001bf98430027fac218002fd610c009fe3086004bf18430087fea21803bfe510c021fea88600eff14430007fe821803bfe410c001fea08600eff10430007fe621803
  | 3 => 0xfa98801cff94c40006fca620073fd5310039fe298801cdf14c4003ffe862001ffe4310001df2188007ff50c4003ff8862001fbc4310009ffb108004ff98840015fcc420013ee6210005773108004ff58840005fac420013ed621000176b108004ff18840025f8c420073ff5210039bfa90801bff948400e7faa4200037d5210037fe2908007ffd084003ffc842006fbe421000ffea108007ff1084003f788420003ff3210037ff1908000ff4c8400dff86420013ff6110009ff3088001bf98440027ecc220006f66110009feb088000bf58440027eac220002f56110009fe3088004bf184400e7fea22006bfe5110039fea88801aff1444003ffe822001fbf411000fff2088007ff504400077a822001ffc4110001ff988801aff8c440007fa622006bfc3110037ff908801aff88440007fa422006bfc21100097f3008004ffd4040027fca020013fd5010009fe2808004ffd00400277e8020013fe4010009fd2008004ff500400277a802001ff94010009ff9008004ff08040027fe2020013fc1010023ffb2e6011bfd973008ffccb9800efe65cc023feb2e6011bf5973008ff8cb9800efc65cc001ffb266000bfd9330007fcc99801efe64cc001feb266000bf59330007f8c99801efc64cc023ffaa66011ff9533008ffaa998047fc54cc023ffa9e6011ff94f30006fca798047fd53cc023fe29e6011df14f30007fe8798003fe43cc001ef21e6000ff50f30007ba8798003fc43cc001ffb166019ff98b30015fcc598003fd62cc0017eb166019ff18b30015f8c598047ff52cc023bfa966019ff94b3008ffaa5980037d52cc033fe2966000ffd0b300cffc8598003fd42cc033fe2166000ffccb30007be6598067fe32cc001fe9966000f74cb300cff86598003ff61cc031ff30e6001bf98730007fac398002fd61cc031fe30e6001bf1873008ffea398063fe51cc023fea8e6018ff14730007fe8398063fe41cc001fea0e6018ff10730007fe6398063fe31cc001fe98e6018ff0c7300cffe4398063fe21cc001fe90e6018ff0873008ffea198013fe50cc023fea866004ff14330007fe8198013fe40cc001fea066004ff103300cffe4198013fc20cc031ff8866004ff04330027fecb18012ff658c009ff32c6003bf99630026fccb1800e7e658c009feb2c6017bf59630026facb180027d658c009fe32c6004bf19630027fec918012ff648c009ff3246007bf99230027fac918002fd648c009fe3246004bf192300bffea91805ffe548c02ffeaa46017ff152300a5fac71805fff538c02fff29c6000df94e300bffaa71805ffc538c02fbe29c6000ffd0e30007fc8718003fd438c001fe21c6004ffd8a30027fcc51800afe628c009feb146000bf58a30027f8c518012fc628c02fffa946017dfd4a300b7fca51805ffd528c001bea946016ff14a
  | 4 => 0x1ffc41d0001ff98e8023ff8c740007fa63a008ffc31d0049ff90e8023ff88740007fa43a008ffc21d004bffa868004ff9434012ffaa1a0013fc50d0049ff9068004ff0834011ffe21a0013fc10d0009ffb2c8004bfd9640027fccb2000efe6590009feb2c8022bf59640027f8cb20012fc659003f7eb248022ffd524003ffca92008bfd549000ffe2a48004ffd8e40027fcc720002fe6390009feb1c8000bf58e40027f8c72008bff5390045ff29c8000df94e40117faa72008bfc5390045be29c8007ffd0e40007fc8720003be4390001fea1c8007ff10e40007788720013ff6290009ff3148002bf98a40027fac520002fd6290009fe3148004bf18a40117fea52008b7f5290043ff2948022ff54a40006faa520087fc529000fffa148021ff90a4010f7c8520003fd429000ffe2148021ef10a40007fe6520087fe3290001fe9948021ff0ca40027fec320013fe61900037f30c8004ff58640005fac320013fc61900097e30c8022ffd4640107fca32008bfd5190041fe28c8007ffd06400077e8320083fe4190001fea0c8000ef5064003ff88320003ff3190041ff18c8000ff4c640107f86320087ff2190041ff10c8000ff48640107f84320012fe6090009ffa848004ff94240027faa120013fc5090009ffa048004efd024003ff68120013ff2090009fe1048004ffc4240027f8212007fff655003f7fb2a801fff9954001dfccaa007ffd655003f7eb2a801fff1954001df8caa007fff545000fff2a2801fff5514003ff8a8a0003ff63500017fb1a8000ff98d40007fac6a0003fc63500017e31a801fffd4d400fffca6a00037e535003ffea9a801fff14d400fef8a6a001fff4350001ff21a8000ff50d4003ff886a0003ff62500017fb12801eff98940015fcc4a0003fd625003dfe3128002bf189400fffea4a007f7f525003dff292801fff54940006faa4a007bfc525000fffa128000efd09400f7fc84a0003fd4250001dea128007ff10940007fe64a007bfe3250001fe992801eff0c940007fec2a0002ff615003bff30a8001bf98540007fac2a0077fc61500037e30a801fffd45400effca2a007ffd515003bfe28a8007ffd05400effc82a0003fd415000ffe20a8000ffcc5400effc62a0003fd315003bfe18a801effc85400effc42a0003fd215003bfe10a801fffd4140027fca0a007ffd5050009fe2828007ffd014003ff680a0013fe4050009df202801effc8140027f840a0077ff1050009fe0828004ffd9440025feca20013fe65100077f3288004df9944001cfcca20013fd65100397eb288004df59440004faca20013fc65100097e3288007bf9904003ffea82001ffe541000ffeaa08007ff15040027fec620013fe63100017f3188004f798c40005bcc620013fd63100017eb188004f758c40005bac620013fc6310039f
  | 5 => 0x5131147f8a898806ff634c451ffa9a6228ff94d31006fca6988a3fd534c451fe29a6228df14d31007fe8698803fe434c401fea1a6200ff10d31007fec498802ff624c44fff3126202bf98931007fac49889ffc624c4057e3126228ffd4931146fea49889ffe524c451fea926200df5493113ff8a498803ff424c44fff2126200ff5093113ff88498803ff324c401ef9926227ff8c931007fa6498803dd324c44ffe1926201bfd853100ffea298807fe514c403fea8a6201ff1453100ffe8298807fe414c403fea0a6201ff1053100ffe6298803f7314c403ff18a6201f78c53100ff86298807dc314c403fa18a6201ffc853100ffc4298807fc214c401ffb026200bfd8131007fcc098803fd604c401fe3026204bf18131147fea0988a3fe504c451fea826228ff1413113ffe409889ffc204c403ff8826201ff04131137feca9089aff654844dff32a4203bf99521137faca9089afd654844dfe32a4203bf19521007fec890802ff6448401ff3224207bf99121007fac890802fd6448401fe3224207bf19121137fea89089bfe544844dfeaa24226ff15121007fec690802ff6348401ff31a4200bf98d21007fac690802fd6348401fe31a4200bf18d21137fea69089bfe5348401bf29a4226ff54d21137f8a69089b7c5348401ffa1a4200ff90d21007fa8690803fc43484037fb124202ffd4921016fea49080bfe5248405fea924202df54921017f8a49080bff4248405ff2124202ff50921017f8849080bff3248405ff1924202ff4c921017f86490806ff6148403ffa8a4201ff9452100ffaa290807fc5148403ffa0a4201ff9052100ffa8290807fc4148403ff98a4201ff8c52100ffa6290807fc3148403ff90a4202fdc852100ffc4290807ee2148403fe10a4201fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc60484097e3024226ffd4121137fca09089bfd504844dfe2824202ffc8121017f84090807ff1048403fb8824201ff0412103ffecba001eff65d000fff32e8003bf9974003ffacba0096fd65d000ffe32e8007bf1974003ffea9a001ffe54d000ffeaa68007ff1534003ffec7a001ffe63d00017f31e8007ff58f40005fac7a001ffc63d004bffa9e8025ff94f40006fca7a0097fd53d004bfe29e8025df14f4003ffe87a001ffe43d000ffea1e8007ff10f4003ffec5a001ffe62d00057f3168007ff58b40005fac5a001ffc62d00057e3168025ffd4b4012efea5a0093fe52d004bfea968000df54b40127f8a5a001fff42d000fdfa168007ff90b4003ffa85a0003bd42d000ffe2168000ffccb40127fc65a0003fd32d0049fe1968007ffd874003ffcc3a0006fe61d000ffeb0e8000bf5874003ff8c3a0006fc61d004bffa8e8023ff9474012ffaa3a008ffc51d000fffa0e8007ff9074003ffa83a0
  | 6 => 0x3fe28e8201ff9074100f7c83a0807f641d0403fe20e8201ef1074100ffc63a0807fc31d0403ff90e8201ff8874100ff843a081fff60d040fff3068204bf9834103ffac1a0802fd60d040ffe306822effd4341177fca1a08bbfd50d045dfe286822dffc834116ff841a0807ff10d0403fe086822cffd9541165fecaa08b3fe65504077f32a822cff59541165facaa08b3fc65504077e32a8201bfd9141167fea8a081ffe5450459feaa28207ff15141007fec6a0802ff6350401ff31a8200ff58d41007f8c6a0802fc6350459ffa9a822cff94d41006fca6a08b3fd5350459fe29a822cdf14d4103ffe86a0803bf4350401ff21a8200ff50d410077a86a081ffc4350401ffb128200bfd894115ffcc4a080afe6250401feb12822bff18941015f8c4a08b3ff5250459bfa92822bff94941167faa4a08037d5250457fe2928207ffd09410077e84a08affe4250401fea128200ef5094103ff884a0803ff3250457ff1928200ff4c94115ff864a0806ff6150403ffa8a8201ff9454100ffaa2a0807fc5150403ffa0a8207fdd054100ffc82a0807be4150403fe20a8201ef1054100fe882a0807fe3150403fe18a8201ffc854100ffc42a0807fc2150401ffb028200bfd8141007fcc0a0803fd6050401fe3028204bf18141167fea0a08b3fe5050459fea82822cff1414115ffe40a08affc2050403ff8828201fdc414100ff820a08abff65cc4557fb2e622aff9973101dfccb988abfd65cc4557eb2e622aff1973101df8cb98803ff64cc4017fb266200ff9933103dfcc998803fd64cc4017eb266200ff1933103df8c9988abff54cc455ff2a6622aff55331157f8a998806fe63cc455ffa9e622aff94f31006fca7988abfd53cc455fe29e622adf14f31007fe8798803fe43cc401fea1e6200ff10f31007fec5988a7fe62cc4057f3166200ff58b31005fac5988a7fc62cc4057e316622affd4b31156fea5988a7fe52cc455fea966200df54b3114ff8a598803ff42cc453ff2166200ff50b3114ff88598803ff32cc401ef9966229ff8cb31007fa6598803dd32cc453fe1966201bf5873100ffea398807fe51cc403fea8e6201ff1473100ffe8398807fe41cc403fea0e6201ff1073100ffc6398807de31cc403fb18e6201ff0c73100fb86398807ff21cc453fb90e6201ff8873100ff84398807f421cc401ffb066200ff98331025fcc198803fd60cc4017eb066200ff18331157fea1988abfe50cc455fea86622aff1433114ffe41988a7fc20cc403ff8866201fdc433100ff821988a3ff654c4517fb2a6200dfd9531004feca988a3fe654c4077f32a6228ff59531145faca988a3fc654c4077e32a6228df1953101cf8ca98803ff644c4017fb226200ff9913103dfcc898803fd644c4017eb226200ff1913103df8c8988a3ff544c451ff2a26228ff5
  | 7 => 0x99002fd64cc801fe3266407bf19332197fea9990cbfe54cc865feaa66432ff15332015fcc7990cbff53cc865ff29e6400df94f32197faa7990cbfc53cc865be29e6400ffd0f32007be8799003fe43cc801fea1e6400ff10f32007b8879900afd62cc805ffa966402dfd4b32017fca59900bfd52cc805bea966402ff14b32017fe859900bfe42cc805fea166402ff10b32017fc659900bde32cc805f71966402ff0cb32017b86599003ff61cc863ff30e6401bf98732007fac399002fd61cc863fe30e6401bf18732197fea3990c7fe51cc865fea8e6431ff1473218ffc83990c7fc41cc863ff18e6431ff0c732017fe439900bfe21cc805fe10e6400ffd8332007fcc199012fe60cc801feb066400bf58332007f8c1990cbff50cc865ff2866432ff54332197f8a19900bff20cc805fe1066431ffc433218ff821990c3ff654c8617fb2a6400dfd9532004feca990c3fe654c8077f32a6430ff59532185faca990c3fc654c8077e32a6430df1953201cf8ca99003ff644c8017fb226400ff9913203dfcc899003fd644c8017eb226400ff1913203df8c8990c3ff544c861ff2a26430ff55132187f8a89900aff634c861ffa9a6430ff94d32006fca6990c3fd534c861fe29a6430df14d32007fe8699003df434c801ff21a6400ff50d32007f88699003dc434c8057fb126402ffd4932016fea49900bfe524c805fea926402df54932017f8a49900bff424c805ff2126402ff50932017f8849900bff324c801f79926402ff8c932017bc649900bfc324c805ee1926402fb0c932007fec299002ff614c801fbb0a6400bdd853217ffcc299006fe614c801feb0a642fff1853200df8c299003f4614c8037a30a6430ffd453217ffca2990c3fd514c85ffe28a642fff9053217ff882990bffe314c85ffe18a6402ffc8532017fc429900bfc214c801ffb026400bfd8132007fcc099003fd604c801fe3026404bf18132187fea0990c3fe504c861fea826430ff14132017fe409900bfc204c85fff882642fff0413203ffecba081eff65d040fff32e8203bf9974103efccba080e7e65d040ffeb2e822ebf5974103efacba08027d65d040ffe32e8207bf1974100dfcc9a081fff54d040fff2a68207ff5534103ff8a9a081fff63d040fff31e8200bf98f4103ffac7a0802fd63d040ffe31e822effd4f41177fca7a08037e53d045dfea9e822eff14f41176f8a7a081fff43d040fdfa1e8207ff90f4103ffa87a0803bd43d040ffe21e8207ffd8b4103ffcc5a080afe62d040ffeb168200bf58b4103ff8c5a080afc62d045dffa96822edfd4b4116ffca5a08bbfd52d0401bea96822dff14b4103ffe85a081fbf42d040fff2168207ff50b410077a85a081ffc42d0401ff996822dff8cb41007fa65a08b7fc32d04037eb0e8201ffd474100ffca3a0807fd51d040
  | 8 => 0xf180431d7fea0218ebfe5010c75fea80863aff140431cffe40218e7fc2010c71ff8808638ff04043006fec8a90037e6454801beb22a400df19152006fec6a90037e6354801beb1aa400df18d52004f8c6a90037f4354801bf21aa400df50d52006f886a900b7f62548053fb12a403dbd8952016fc84a900b7c4254805bf192a402df0c952006fec2a90df7e6154801beb0aa437df185521befc82a90df7c415486fbf18aa437df0c552016fe42a900b7e2154805be10aa400dfd8152006fcc0a90037d6054801be302a402dfc8152016f840a90df7f105486fbe082a407ffd974203dfecba101ffe65d08077f32e8407ff597421b5facba101ffc65d080f7e32e8402bf9934203ffea9a101ffe54d080ffeaa68407ff1534203ffec7a101ffe63d08017f31e8407ff58f42005fac7a101ffc63d086dffa9e8436ff94f42006fca7a10dbfd53d086dfe29e8436df14f4203ffe87a101ffe43d0801df21e8407ff50f4203ff887a101fbc43d08057eb168402ffd4b42016fea5a100bfe52d0805fea968402df54b42017f8a5a100bfe42d0805df2168402fb90b42017f885a100bbc42d0805ff1968402ff0cb4203ffec3a101ffe61d08037f30e8407ff58742005fac3a101ffc61d08037e30e8436ffd47421affca3a10dbfd51d086bfe28e8407ff9074203ff883a10d7fe31d086bfe18e8402ffc8742017fc43a100bfc21d080fffb068407ff98342025fcc1a101ffd60d08017eb068407ff183421b7fea1a10dbfe50d086dfea868436ff14342017fe41a100bfc20d086bff8868435ff043421a7fecaa10d2ff6550869ff32a8403bf995421a7facaa10d2fd6550869fe32a8403bf19542015fec8a10d3ff545080fff2a28434ff5514203ff8a8a1003ff63508017fb1a8400ff98d42007fac6a1003fc63508017e31a8434ffd4d421a7fca6a10037e5350869fea9a8434ff14d421a6f8a6a101fff4350801ff21a8400ef90d42007fa86a101ffc4350801de21a8402bfd8942017fea4a100b7f5250805ff2928402ff54942016faa4a100bfc5250805ffa128407fbd0942017fc84a100bbe4250805fe2128402ef10942017d884a100bfe3250805fe1928400ffd8542005fec2a10cffe61508037f30a8400ff5854219ff8c2a1006fc6150869ffa8a8433ff945421a7faa2a10cffc5150867ff20a8407ff1054219ffc62a10cffc3150805ff90a8402ff88542017f842a1003ff60508017fb028400ff98142007fac0a1003fc60508097e3028434ffd41421a7fca0a10d3fd5050869fe2828402ffc8142017de40a100bfc2050867ff8828433ff04142197fecb990caff65cc801bfb2e64009fd9732197fccb9900efe65cc865feb2e6432bf59732197f8cb9900efc65cc865be32e64039f19732007fec999002ff64cc801ff3266407bf99332007fac9
  | 9 => 0xc017eb068607ff1834321ffea1a190ffe50d0c87fea868643ff14343217fe41a190bfc20d0c83ff8868641ff043431dffecb218eeff6590c77ff32c8603bf996431dffacb218eefd6590c77fe32c8603bf196431f5fac9218efff5490c0fff2a4863bff5524303ff8a92181efe6390c77ffa9c863bff94e43006fca7218effd5390c77fe29c863bdf14e4303ffe8721803bf4390c0fefa1c8600ffd8a43207fcc52180afe6290c01feb148600bf58a43207f8c52180afc6290c77ffa94863bdfd4a43207fca5218effd5290c81fe2948640ff90a4303ff88521903fe3290c81fe1948600ffd86431fffcc321806fe6190c01feb0c8600bf586431fff8c321806fc6190c77ffa8c863fff946431dffaa3218fffc5190c7fff20c8607ff106431fffc63218fffc3190c81ff90c863fff886431fff84321803ff6090c01ff3048604bf98243007fac121802fd6090c01fe304863bffd42431dffca1218effd5090c77fe2848640ffc8243207f841218ffff1090c7ffe084863effd95431f5fecaa18037f6550c013fb2a863eff9954301dfccaa18fbfd6550c7d7eb2a863eff1954301df8caa18fb7c6550c073e32a863effd514303ffca8a18fbfd5450c0ffe2a2863effd4d431f7fca6a18037e5350c7dfea9a863eff14d431f6f8a6a181fff4350c0fefa1a8600ff90d430077c86a1803ff6250c017fb12863dff98943015fcc4a1803fd6250c7bfe3128602bf189431f7fea4a18fb7f5250c7bff292863eff549431eff8a4a18f7fe4250c0ffe212863dff8c9431eff864a1803ff6150c017fb0a863cff9854300dfcc2a1803fd6150c79fe30a8601bf185431f7fea2a18f3fe5150c7dfea8a863cff145431e7fc82a181ffc4150c79ff18a863cff0c5431effe42a18f3fe2150c79fe10a8600ffd8143005fec0a1803fe6050c01feb028600ff18143025f8c0a18fbff5050c7dff282863eff541431f7f8a0a18f7ff2050c7bfe102863cffc41431e7f820a181fff6510c0f7fb288607ff9944301dfcca2181ffd6510c757eb288607ff1944303df8ca2181efe6410c0fffaa08607ff9504303ffaa82181ffc5410c777f318863affd4c431d7fca6218037e5310c75fea98863aff14c431d6f8a62181fff4310c0fdfa188607ff90c4303fbc862181ffd4310c01dea188607f750c4303ffec42181ffe6210c057f3108607ff58843005fac42181ffc6210c057e310863affd48431d6fea4218e7fe5210c75fea908639ff1484303ffc842181ffc4210c73ff1908639ff0c84303ffec22181ffe6110c037f3088607ff58443005fac22181ffc6110c037e308863affd44431c7fca2218ebfd5110c71fe2888607ff9044303ff882218e3fe3110c71fe1888639ffc84431c7fc42218e3fc2110c0fffb008607ff98043025fcc02181ffd6010c017eb008607f
  | 10 => 0x600200000800400000400601e00002a00800000e03000001c02600000000201e00800601c00200200200a00600401800001a00000a00400600400e00600001a00001000e00200000000002001a00000000600202400800800000400e00200400400000200a00200601000000000200000600a00000400e00200400000000400000201800004200000200000000200001600200602201201201200000e00000200800600000e00400400c00a00601200003e00400600000400000000000c00000800000000200000001803200200000e00400600800400000000000400200200000000000800c00200a00400000000a00400000800a00000c00200400a01000400000801000e00800000600000000000400c00400000000402000000001800000000000400400000200000c00600600001400000800400001e00a00600800000000000601000200400200200200200000200400000000000e00000400200200000600000600200600401200600200800000400000400200400402800a00800000400000200602e00001000000604c00200000000401000002201200201200400000000000001000000000000000002e00600600205401400200a00000000600200200e00a00600400000000e00a00600000200600000200201e00200a00000a00800400000000200800400000e00a00000401000000200400000000400800000000200200000000200e00e00c00200000000e01000600000002a00a00000200200001200c00402401800a00c00000000800200e00200a00001a00000800000000001600000200000dfd9253006fcc9298037d6494c01be324a603df98e5301cfcc72980f5e6394c01bfb14a645df98a53006fac5298027d6294c8bbe314a645df90a5322ef885299177e3294c8bbe194a600dfd8653226fcc3298037d6194c89be30ca644df90653226f883299137e3194c89be18ca645dfc8653226fc43299137c2194c01bfb04a600df98253006fac1298037c6094c8bbf904a645df08253226fe21299137c1094c0fffb2e8607bfd974303ffccba180efe65d0c0fbf32e86039f9974303ffacba190efd65d0c0fbeb2e86009f5974303ff8cba181efc65d0c0fffaa68607ff9534303ffaa9a181ffc54d0c87ffa9e8643ff94f43006fca7a190ffd53d0c87fe29e8643df14f4303ffec5a181ffe62d0c057f3168607ff58b43005fac5a181ffc62d0c057e3168643ffd4b4321efea5a190bfe52d0c87fea968642ff14b4303ffc85a181ffc42d0c85ff1968642ff0cb4303ffec3a181ffe61d0c037f30e8607ff58743005fac3a181ffc61d0c037e30e8643ffd474320ffca3a190ffd51d0c83fe28e8607ff9074303ff883a1907fe31d0c83fe18e8642ffc874320ffc43a1907fc21d0c0fffb068607ff98343025fcc1a181ffd60d0
  | 11 => 0x86ce4f239d8adc04688637b1914826499000160ca060001d10f380003ad3c200003281e818d216066c4c10000000c523892d104bc7525a03b515904902550ab8000000162103000000000000000005320000001f640000002f4954d0440002a282450cc1e935089c84f881b0001e1400026d00006383543c711b8bd04c20002538be0cde0000000000ab645a000180908e3462060000cf800043880007ca000201000000000006910b0cce0003f38000ca400000017f800000020d9e1876a56b06d0000ed04df00000003880220cd1aa8c120000260bb800000043a08380002e7000000000000a241800000000000000000000000000ca800002c00000009627ba00000008ae00023093f420a00000002d41f622535c00003640003a991fc4603fe08e9cf8204115048109c000000000000024c47000797e42287880000e4000070800001ec0005e244980007be61e04b80000007730e980000000000000000afa2da47f800000000019600000000e50001288548034000175830e0000000fa11ce45402ba2703b8432276020098673523d0c80e688ca07c0000e5a13000000000007ac08c1cfcc0800000000003ba0000001bc8e3e00000000000dc000000195c000000000000001e00200201401800200001600401000800400400000200200600400800000a02400000000000003000200200400401a00201800600800000600000000000000a00000000600000600800c01000201200600000200000c00000400202400000002201000000a01400000000002600a00200200002200000402000400c00600000e00000e00000200c01601600000000001001005600200400200000400000200200200000200600200200000200600801e00200200400400200800401401002a00400000000400800a00200000000000200400400000200000400400e00801802800400600000200000202a00000a00800a00200202800600400800c00000a00c00202200000000000400200200a00400003a02600601000000000000000800e00600a00000200400401600001000a00800800000000001e00000000800004a00201e00600001003200200000400001600200200000800001000200000a00801600000000401c00600000000800801000000000200200000801200401200600200400400a00c00200401400400a00000400400c00e00e00200200000a00200400001c01000800200200400c00a00200202600000200000c00400200000000200000000000200000000000401600000000600000600000000600a01200001400200e00000000000000200000600000600200400000200000000a00601200000400000201200002401a00201a00000200200000000400200000000202600600000200000000800600000000c00200e00600602203a016028002
  | 12 => 0xb2000000000014b9108000000000000020512f800004828e27c99e51a85223a7868ca6200000000ec7c68390ae0000ce000030a884c31047d233980c2165d40449f6000047e000000000011c40f046c2680002df8a0c91027809400000000000000554b7659318600005640002ef800000075d0dc0d2800000026380001485e60000000fbe5ce1c6000110a0000a781680004ca0000c3400000032e198c218000338a15120800000005d4000000000000101e6d419e094c0003293778000000000418000100c3c54011c28d2249a00008f8e4e5680b200000007c20002408e0a6362db8000a7c5d90001cc04b66993819c5841200000000012067ff1dd15c00000000ab0000fda5862d61c691363d12c2a3dc7a0000000000000058b0000f6c96a1ad000105503400300010640000002ff9b6c0001b31c18000a220000001bd11f013c00016a85a6000000000000000046b00004740002d080007100000000d500000000000828e8a80400022481c400043099d40002f500000006ae0cf36b066109e4202be10390ee15f000a29c000000000170835c8b63dd9a908d46af0708438c565ae2371f280001121a4125c92a74927084b8000000000000000003802a23b10f0000317a27c0da814027000009e4ef26ca0580003ff35a016c00000000007dc0001680001be8000144000000000000000017e864c19f251918c000000083833414200011088c4eb23420bb8fe466a0004361b9c00000022f80001700b71068af00006c645693fc00000010b20c818800010409a0ee81d40000e090ca6cc00001c4b386100e514e000069409d87c0c147520d889a427277d44895c90480000dd86b093c3bd00015d8d9c0001e08000df80000000000d8864f000114000000007a0000c6a00045d89e4f226e340a80000000000001eb400000000023740000000000000000000000000020200041e800000000000000000000000000000ad83f81db00003fa0000001f4c0001350001974e6e35f00010a0bee00000000000006be000164800000e00007c42ba3f23639e78d6e1853140a30c785dc00010040005d80001318bd87380001e945885e317913d0dcc000000000000000d3a500e86143093fe80006cc30e01f121d1b47c4000000000000013707247f800000001fd0707e528f8e8cabe47b079913d0de11900000000000052d28000a3c0001748000fb80a73d00c607c82b90c7800071a0bf22b03e80fc0a347883091f80352068184000848000000084200000000002de019000000000031e47296f40000000ff8000b287cf07192b827a00000009bc0ea6f1416800000070400019a80000000b880000000001b0800000000004f1394d0200034f9d303400000000c0105c00020823ec0001a43931ed8a306690000c94ea8462035091d1da10627b228
  | 13 => 0x900004910000000e8477700000003ae0003c3932495600000000000002240000000702000379800000000027809480000002591c84d2a627193a15d14089432009f4b685742a8000000053f2d48000d7e2cb000021077e89032a2304a32000391800000054e02100002cc1db3039bac00039b00a000001227600000000003a4000000000000032f800000000000000000000590cd800000000018980006fe00000000004e02d800000000000001bf00007ce8ab10c13ec970000000000053420314494e4000000000021400007a0000000000000000000000070d00000000006a938a06f476238609f9b00ca02632e4077c0007e000000000005cc0001f580006e501e1fe91e867d113a3f82f600000b9d0400000000009dc85a0003d400000007e802b0c0c2fc000221000019c0d80000d14c5c50721e0094000697009093000000031b800107e5c121717d059c15000000000000001b582b4c1a65b2038000000000116000014a0002a91cf43dc78f0cb000000000040814000007d4000022017a22e00013881067f42f202489003c41bc0478ede1cf0000d30ce628000014ec0000000b1a3bc000000167800000051b31c1ac0198779000047c3a24813b912dd1860e40299e650462bb000000000000000000000005b200012cc000000000000099a61300000000006ec0000000a8e00019d0e440007c11f880000004c400017545d000000000006f2000000000043a78900000001fe2120000000000000000000053800046c8ccd02e020434150849a41636c000038414322480000000003e7092cec60043ae179c36e80d2bd80003f25880c681b07a64b03aa800000032d00016a050a4c817b19fc58678e4390b481d81ed00000006b684647580007a800031116240000000000000cac2db11e0b345fe85900011acbb600043d0000a0a000000043c000000000000000400000009000000004260000000000000000092c0003800000b746ba0000f686682a000000011f40000000000b5a25e3ed00000000cb0000000d0c2c000014380002af2cd98487ac0d54320000f52000307000000027e00001d00a2632387000000000000012e8f2c53200020240004a521ea354c422740001cb00000be000000000040b163153c73800045b80000006ab00013a80a45132e022f8000000000000002000045c800067e6d2274000045400000015110ba2b320419281745730000bf80003be45f94540000000000000d924223471830be674700018b000017a1730a5000075700000010fe00005d8d380000000000204fe428722f000000000000000000006b600019dc00000000016444b069d0002384d247f73131048a6a659000000052c00000010a88564230000d74bec13a09c000000043537c9b2800000044b8060a142024599f149f806945621f000000
  | 14 => 0x19880000002010000000000000000000107401b47302500000001a780000000003d597f049472e1a093405f24743fc0ae06e61a20001e8ce9c7f92cf8e80ffc1c7004017828a87528e8d783d838f2b31348c4878d3b59bec75623947821acab40002e8000000088b02080dc6c000000000007783840bc8000bdc00029280010fa3dd000000000058d0ac8f2400061c0001a880720c70be81e42ca00000000000006410000db800033d000000000000000020f800000000000740000000b0138c14045d33400000000003880000000000466238d04052815b0000bc086900000002640000000000d8a85100000001440001c71af49e28a10a48480e126c81f519b897800039202b04d42a6403807cbc26e026593309b00000180b74bae8ea19182f000019c02a80003de86236a9c040000000000aa400000002e94308721920b610f80000000001ca0e3219911ea2d07ee00042b142c5d800018080006643520001a108742711b11f2c000000000026400044504708810a00e0000000000068800000000006bb2481dec3c07eb00000010147e636d0f8818c36818895b400086338600004a07440b4800000065100000000003b00330a10000000241169cf302f106e800000044e1bd83c80002f31c500000000003f48000000000000000000041f27722780007180001f84e90000000000000000039d172442e09b000234ccc86a81118508aa25304641e704b4000000000000063935307200000001ca186068e0002bd00000001bc0c50840ebe6313ca0c5400063b17e98c0a962b100004b40008250001ad44ce0000b58afc0000000190d8c0000000da81acd844be0b0882cf4882b30001803026461711f489846f70688b5d1480001f688c81ce178275a0847660002ae04f81a884232703287421af3a80c4000072a41a000004e1a5000075400083300000010527750451cf09d25ed348052c0005cf0000000f6e8c947480000004b900000000001903de8ad40e60001088c5c6d80000af18200005960000bf02f8000311800000052100000006e00e80000000b5600c000000103e0003ad80000001b60000c1400083c00000011be0003b4836c65c417000000000000000000000008881f8000000052418e80001621f42131fd887e39600000007f45593ea80001ae00025600840001ea03e800028221a42d000000000009991dd1301f60001fb918c0002999a708762a20000d0c000000195a030b8a000000000000023609080002a81bf1ec986c8d81100b717741fc61f436a17cece2a504797781d666607317a089029f26e22991040f52288f54db28e41cc0bbcdd000040c800000000000000000000000fe1b740006831e508d0000000336192d15e00028200000000000ca8000c280000000000d644e60000000470013017a2040006ac0000c
  | 15 => 0x44400000000000000008360e596680007924178000d627a631d21cc44c0000341c2c9247dd10e0000cbc8a926b2180a4e6cd12310bc2ce00032c1fa8ac049b0001b78dbe3a53219130dc800000008d4ed84c037680001e00003c19d883820493c810003ce2ca1c3800116200026a142000039e48080003b0778256840c40e30f1728000000000000150c00000000010d03fc0000000000e86000000000000000000009e8bde5da2a608645503990f90d604821ab05913f80000001ae18940c85a32ba8f011ae8f60000a04000000000000000031400011540001be3b00a341f20000001a1cefc8e00f1000083400043d9e88a1e000000000000000000000000008a8013000000000000012d8d3400000000006a25b13e01984ab00001000e7c000000000000000000000011c891e000000000000000000e00000004f8237865c91800006fa1d88ea13704980011dc0003a68a44342000000000067c000000000022622b10780540000af000000000000030e97940000000001fec0000003ad00f462c60b0b806300001230c002305f65fb0bf8738d9e3a819c08ec368000369958c8e60004208000e5e0003fe00000008402f88c08e660653f88000000086000000108a0000000000a123fd12b00010ce000000007814c0002af0000638000378143480a00012e92500007950001e7ce044413658af4000707000000000034b45e000000000045914f420052b13120600000000001fbc0008cf00016600000d000015dcd4600043700007848c40468000a380000000d94e2a00023300001ee4533dc00008703eb000000000000016e06188b84ce0000000f8e3e1000000000002b19b8a406de00000000000be0000000a08822000283000055807035c849400000026780011603d70e28d000000003f20b5453a00044394990d4493000129882800027aa36c0000003390000000000136052000048b04b1988d262d034598044ae8b509580fc67671c0001bf828e0c117b890c2ec68011f85c8b9477c32384248ca2c527b95e42085b605803244fe4dd06b01210927402d30d4054e0ed44e97d474c5611fb13b43c20000d480004188311dc91a0000000086800093800020182ac0001e43c00b58f788fd00000009ce0000000000cc000034282a00003b21890d24a2428f36e05b515458a2b51d449f44370d8000000000000000000006bc00000003bc000000099905835325f800043c0003d721c0000000319800072e000000000000058e0000ee07bc0442b791605266f532691341e20fc1ab18a8b2a84d31a0768ec81c32bf91a4a6e7af4131d9825827524692285be74600000008ec00046e00a0516546095000000000047a8568000000000209c0005713210eec83c0000002074cd6676203000000000000000000007b0350000000065a00006240000
  | 16 => 0x14c00000000950000000ca600005a000000053a29007e80c47f3000000000066503396e40000000030c88aa80001f790cc29c6173ab237800000006f0d10000000000000000012733d80000004a9322167422e36923c9a589688554470f200000000001c3c06c00006191f000000000d195453c3e610f84685d60770000b848080000000fb00004da000231400030b0000000c7c0001451e5c6e8377000000000044700003a85f40000988000d8622f2e6869800000020e232c13e2330ba093c0c60001ba9b5d0a408b0e90000c2c5994528b3000088c000000000000037f800000019d31f80008b277600022342a21d600003f40007b441d856c32648530c85300002de0001e4c00000000008a460c53c4088fa44b20ae44c8888d4e4a42c08f300000000002338e0c57e00000007c073221b14500000002c21fd479e4e446694a8eda5290e6800000071238ba34872a52f000214cf860003ac0c64d3000000015347345550000000c0a0004418000000000000000078c00018f8b2488860f1981b84ba40dc42e0a5442a40900010c41a66e20001868b8800013000000000001550eb09121291559f34b667db31e80005605673e880000003590058bc03740000000b50000000000000000075e00000000004c500019e000000037c012800000000000000000000000000d1468943c80000000000269a3cb2000044a862c0004a001680000000000f980000f85eb000000063600000000000000000000000f364de02c1ba402c00000000003ea0000000a18e720b32e192600000003900000fe000000015204a800000002d800054a2f80e4cb180003910000d5c2142df042810e5c6121109000003143f1acc0003dc0a01e7408c2c141a83000de25c0f18000aac8133680ae905419110d9dfc9540290dc800101651600000000000c84610000a342a100000011701fb000000091c000238870000000000010740007610001284000000000081112c47804d000000000008b02a830419e09b0000b2e7b145d0000b785b0377192035029b38e8000e2690045e971ca20297421800000000039b16e008e2c70c184887f614a00388a00005ea00000000000000001cac0000000000d34000844000000000005c00000000003f429b0c108c04a81610000bf01cc33d18b44a20001aa8000cfc308000150400037246c0a480006c11b50dc40ec4183a581e0f6659e3989148be43801f70b4515c8082431c445102ea28083d91120c51909028a46000000010c9a27c63e400006f40004450f2c7161f83b719d0b0088f0000000000000225934cf7c00000000001de6060a900000000000001fb00002e330880000000000000000308771223000000000034f20480007cc00009ec7ea00000003a488000037e8000000173000000000000044d11b506e1240000
  | 17 => 0x2b482744c88d00000ed0f6440f42f1594b0e68247c8ea87e61d91e9000008a0000000994eca52c0001f780000000000f0cd4a5780001ba8000000000000000035a000110c0000d94400db500216a1978b64aba52d47923446ec58f1838518c983280d38ce493e7a72da8000fc485b00000000007b53d500005c084a4070000a684640000ab421007200000008940002b103b80003a70002014b043cd3f197f40000002578af8f16000000054c00071b0ac0ab800000000000010380000e309ac0002e401980000000002700000d1802e000169118e0000001e680a03af0000a8c000620000172cc923d80000000ba600011681000004f3000145cd1a84b1be1efc4882454518740a922491768e480227d73c1135ce4a1e625d82709b65023e81b44f727a104c0ad01724303949e04f1884e3bd0794d5a8c040023a03d60a9000000076e5af22d95b80004d500000a800039d2ab800105024e401812c29a27324e95011e600000000000000000000000f144bd1b200006fa08238f00000007c93b81a6c0004250000000ba20000000e151c400033692100000001d70000852
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x6405051026fb44050510025f676cc510006f676cc510024f676cc510265f775cc510265f575cc5100077765cc51025f7465cc510005f774cc510005f574cc51000df673cc51000fd673cc510006f763cc510007d763cc510006f563cc510007d463cc5100077653cc51025f7453cc510005f572cc51014ef662cc51014ef462cc51025f7752cc5100077552cc510007d732cc510007d532cc510025f670cc510007f270cc510007f170cc510025f470cc51000ef760cc51000ff360cc510025f47648510016f47648510024f47648510255f77548510255f5754851000777654851024f746548510005f77448510005f57448510005f67348510005f4734851000776534851024f74534851000df7724851000fe77248510007e76248510016f66248510016f4624851002fe4624851002f77524851002f755248510007f37048510025f67048510025f47048510007f0704851000ef7604851000ff3604851000cfe76d011000cfc76d01100067f65d011012e7c65d0110006bf64d011003ebc64d011000df671d0110005f571d0110027f010d011003cff765011000cfe76501100ecfd765011000cfc76501100067f65501100fe7c6550110006bf645011003ebc6450110005f7715011000df4715011000cfe76cc11000cfc76cc1100067f65cc11008e7c65cc110006df63cc110006dc63cc11000df671cc110005f571cc1100c4ff764c11000cfe764c110094fd764c11000cfc764c1100057f754c1100357c754c1100067f654c1100a67c654c110005bf744c110005bc744c110006df634c110006dc634c110005f7714c11000df4714c110245fa7688110026fa76881100077b658811023f7865881100077a538811023f785388110055f97288110016fa6288110016f8628811002f7b528811002f795288110027f3718811000dfa7188110025f87188110027f07188110026fb6188110027f36188110067f2518811023ff15188110067f24188110007f14188110007f33188110067f03188110067f2218811002ff12188110014ff764811000cfe7648110054fd764811000cfc76481100067f654811005e7c6548110005bf7448110005bc7448110006ef6248110016ec6248110005f7714811000df47148110027f0104811000df87648110016f8764811000cf876481100077b6548110237786548110007bb7448110007b874481100077a5348110237785348110025fb7248110027eb7248110007eb6248110016fa6248110016f8624811002fe8624811002f7b524811002f79524811002fea4248110007e94248110007f3714811000dfa714811000df87148110057f07148110026fb6148110027f36148110057f25148110237f15148110057f24148110007f14148110007f33148110057f03148110057f2214811002ff12148110
  | 1 => 0x89100067c75d891001c7c75d891003cfe74d8910004fd74d8910004fe73d8910004fd73d89100067e53d89100067c53d891002e7f52d891002eec42d891002eec32d8910024ff71d891000cfe71d8910024fd71d891000cfc71d8910066ef21d8910066ed21d8910024fe70d891000cfd70d8910024fc70d891002eef20d89100057f75589100357c75589100067f65589100067c6558910005bf7458910005bc7458910005df7358910005dc735891002eec625891029dfb7058910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf745891003cfc7458910006bc745891003cbc7458910004ff7358910006df7358910004df7358910004fc7358910006dc7358910004dc73589100067e53589100067c5358910064ff7258910006ef725891002e7f5258910054ff7158910006f7715891029cff7058910006fb70589100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c76549100067f64549102967e64549100067d64549102967c64549100057c73549100067f63549100067e63549100067d63549100067c635491028d7f72549100376f725491002e7f62549100167e625491002e7d62549100167c62549101bf7671549100077571549102867f61549101bf7641549101bf7431549101bf7621549101be7f60549101bf7b10549102877610549102877410549101bf78105491003cff76d0910004fe76d0910004fd76d091003cfc76d09100067f65d09101b67c65d091003ebe64d0910006bd64d0910006ef62d0910016ec62d091000df671d0910005f571d0910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101a67c655091003ebe6450910006bd645091000df67150910004ff76cc910004fe76cc910004fd76cc910004fc76cc9100057f75cc9100357c75cc9100067f65cc9101967c65cc910006de63cc910006dd63cc910006ef62cc910016ec62cc91000df471cc910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100357c754c9100067f654c9101867c654c910006de634c910006dd634c910005f7714c91000df4714c910025f4765051003ef47650510024f4765051027df7755051027df5755051000777655051027774655051000df7745051000fb77450510007b7645051003ef6645051003ef46450510007b46450510005f47350510007765350510277745350510007b74350510007b54350510005f77250510277775250510007755250510007b74250510007b54250510007f37050510025f67050510025f47050510007f07050510025f0705051000ef7605051000ff3605051026fb
  | 2 => 0x4fd7598d100067d7598d100047d7598d1001cfc7598d1003cfe7498d10004fd7498d10074fe7398d102ae7c5398d10014fe7298d10004fd7298d10014fc7298d100067f5298d100c4fd7198d10006f57198d10094fd7098d10006f97098d100057f7558d100357c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10005ef7258d1002dec7258d100c5fb7058d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d1003cfc7458d10006bc7458d1003cbc7458d10006df7358d100067c5358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d100067f5258d10094ff7158d10006f77158d10096f43158d100c4ff7058d10006fb7058d100acfe7618d100357c7518d100067f6518d100067c6518d10006dd6318d10004ff7518d102ae7f7518d1001cfe7518d10004fd7518d1001cfc7518d102ae7c7518d1001c7c7518d1003cfe7418d10004fd7418d10006de7318d102ae7c5318d10014fe7218d10004fd7218d10014fc7218d100067f5218d10006de3218d10006dc3218d10024ff7118d1000cfe7118d10024fd7118d1000cfc7118d10076df3118d10076dd3118d10024fe7018d10024fc7018d102ae7f7694d100057e7694d100067e7694d100047e7694d100067d7694d100057c7694d102ae7c7694d100047c7694d100067f6494d102be7e6494d100067d6494d102be7c6494d102b57e7394d100375e7394d100067f6394d102ae7e6394d100067d6394d102ae7c6394d100057d7294d1022e7e6294d1022e7c6294d10007777194d10227747194d102a67f6194d10227764194d10227743194d10227762194d102267f6094d102277b1094d102a7761094d102a7741094d10227781094d1003cff76d0d10004fe76d0d10004fd76d0d1003cfc76d0d100357e75d0d100057d75d0d100067f65d0d1021e7c65d0d10006df63d0d10006dc63d0d1000df671d0d10005f571d0d10004ff7690d10004fe7690d10004fd7690d10004fc7690d100067f6590d101de7c6590d10006bf6490d1003ebc6490d1000df47190d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100357c7550d100067f6550d101f67c6550d10005f77150d1000df47150d10005fb7050d10025f87050d1003cff7610d10004fe7610d10004fd7610d1003cfc7610d100067f6510d101d67c6510d10006bf6410d1003ebc6410d10006df6310d10006dc6310d1000df67110d10005f57110d10014fe76d89100357c75d89100067f65d89100067c65d891002eee62d8910004ff75d89100067f75d891001cfe75d8910004fd75d891001cfc75d
  | 3 => 0xe62d95100067c62d95102c77771d95102cf7471d95102cf7641d95102cf7431d95102cf7621d95102cf7b10d95102c77610d95102c77410d95102cf7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100047e73d95100067d73d95100067c73d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067e42d95100067c42d95100067e32d95100067c32d95102c67f71d95102ce7e71d95102ce7d71d95102ce7c71d95102ce7f41d95102ce7e41d95102ce7d41d95102ce7c41d95102ce7f31d95102ce7e31d95102ce7d31d95102ce7c31d95102ce7f21d95102ce7e21d95102ce7d21d95102ce7c21d95102ce7f70d95102c67e70d95102ce7d70d95102c67c70d95102c67e40d95102c67c40d95102c67e30d95102c67c30d95100067f20d95102c67e20d95102c67c20d95102ce7f10d95102c67e10d95102ce7d10d95102c67c10d951003cfe76d91100067f65d91100067c65d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110004fe73d9110004fd73d91100067c53d9110014fe72d9110004fd72d9110014fc72d91100067f52d9110006be42d9110006bc42d9110024ff71d911000cfe71d9110024fd71d911000cfc71d9110106bf41d9110106bd41d9110024fe70d9110024fc70d91100357e75991100057d75991100067f65991100067c6599110006bf64991100edf970991100057f75591100357c75591100067f65591100067c6559110005df7359110005dc7359110005ef725911002dec725911011dfb7059110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110006df7359110004df7359110004fc7359110006dc7359110004dc73591100067c5359110004ff7259110006ef7259110004ef7259110014fe7259110014fc7259110006ec7259110014ec72591100067f52591100ecff7159110006f7715911011cff7059110006fb705911026ebe405911026ebc4059110104fe76191100067f65191100067c651911003ebe6419110006bd64191100357e75d8d100057d75d8d100067f65d8d100067c65d8d10004ff75d8d1001cfe75d8d100067e75d8d1001c7e75d8d10004fd75d8d100067d75d8d100047d75d8d1001cfc75d8d1003cfe74d8d10004fd74d8d100067c53d8d10014fe72d8d10004fd72d8d10014fc72d8d100067f52d8d10006de32d8d10006dc32d8d10024ff71d8d10024fd71d8d10006f571d8d100aedf31d8d100aedd31d8d100aef431d8d100357e7598d100057d7598d100067f6598d100067c6598d10006df6398d10095f97098d10004ff7598d1001cfe7598d100067e7598d1001c7e7598d10
  | 4 => 0x8e1003cfc7458e10026df7358e10006df5358e100067c5358e10006dc5358e100065c5358e10004ff7258e10014fe7258e10014fc7258e100067f5258e10096df3158e10096dd3158e10024ff7058e10024fe7058e10024fd7058e10024fc7058e10026de3058e10026dc3058e102ae7f7694e102a67e7694e100067d7694e102ae7c7694e102a67f6494e102be7e6494e100067d6494e102a67c6494e102f57e7394e1004f5e7394e102a67f6394e102ae7e6394e100067d6394e102ae7c6394e100057d7294e102a67f6294e1022e7e6294e102a67c6294e102267d6194e102a67e6094e102a77a2094e102a7771094e102277b1094e102a7781094e1003cff76d0e10024fe76d0e10004fd76d0e10024fc76d0e1004d7e75d0e100057d75d0e10004ff7690e10024fe7690e10004fd7690e10024fc7690e10006de6390e10006dd6390e10004ff7650e10024fe7650e10004fd7650e10024fc7650e100057f7550e1004d7c7550e10006de6350e10006dd6350e10005fb7050e10025f87050e1003cff7610e10024fe7610e10004fd7610e10024fc7610e10004ff7558a1001cfe7558a10004fd7558a1001cfc7558a10004ff7458a1003cfc7458a10004ff7358a10004fc7358a100067e5358a100067c5358a10026ef7258a100467f5258a10046ee4258a10056ef2158a10056ed2158a10024ff7058a10024fe7058a10024fd7058a10024fc7058a10026ee2058a10026ec2058a10026f71058a10026f51058a100067f7654a102867e7654a100067d7654a102867c7654a102867f6454a102967e6454a100067d6454a102867c6454a100057c7354a102867f6354a100067e6354a100067d6354a102867c6354a102ed7f7254a1004f6f7254a102867f6254a100167e6254a100467d6254a100167c6254a10007777154a101bf747154a101be7d6154a102867e6054a102877a2054a10287771054a101bf7b1054a10287781054a1003cff76d0a10024fe76d0a10004fd76d0a10024fc76d0a1003ebe64d0a10006bd64d0a10004ff7650a10024fe7650a10004fd7650a10024fc7650a1003ebe6450a10006bd6450a10016ee6250a10006ed6250a10004ff76cca10024fe76cca10004fd76cca10024fc76cca100057f75cca1004d7c75cca10006de63cca10006dd63cca10004ff764ca10024fe764ca10004fd764ca10024fc764ca100057f754ca1004d7c754ca10006de634ca10006dd634ca10005f7714ca1000df4714ca10025fb76482102e6fb7648210007bb7448210007b874482100077a53482102df785348210027eb7248210016fa6248210026f862482100477b5248210047795248210047ea4248210007e9424821000dfa714821000df871482102d57e76d95100367e76d951001c7e76d95100057e73d95100057d72d95100067
  | 5 => 0x7ac64509200076e53509203076c5350920007ae4350920007ac4350920007eb7050920025ee7050920025ec7050920007e87050920016ef6050920017eb605092000cfe76d8520006bf64d8520006bc64d8520056f661d8520004ff75d852001cfe75d8520004fd75d852001cfc75d852003cfe74d8520004fd74d8520004fe73d8520004fd73d85200067e53d85200067c53d8520024fd72d852000cfc72d85200467f52d85200467d52d8520006f751d8520056f451d8520056f431d8520056f621d8520046f521d8520024fe70d8520014fd70d8520024fc70d8520056f710d85200057f755852005d7c7558520005bf7458520005bc7458520006bf6458520006bc6458520005df7358520005dc7358520056f461585202fdfb7058520004fe76d0520004fd76d052003cfc76d052005d7e75d05200057d75d0520006bf64d052003ebc64d0520015ee72d0520005ed72d0520007ad42d0520004ff7650520004fe7650520004fc7650520006bf645052003ebc6450520007ad4250520004fe76cc520004fd76cc520004fc76cc520006bf64cc520006bc64cc520006f761cc52000ef461cc520004ff764c520004fe764c520004fc764c5200057f754c52005d7c754c520006bf644c520006bc644c520014fe76d0120014fc76d0120006bf64d012003ebc64d0120015ee72d0120005ed72d0120007ad42d012003cff7650120014fe76501200f4fd7650120014fc7650120006bf645012003ebc6450120005ef7250120015ec7250120007ad4250120014fe76cc120014fc76cc120006bf64cc120006bc64cc120006df63cc120006dc63cc120015ee72cc120005ed72cc1200ccff764c120014fe764c12009cfd764c120014fc764c1200057f754c12005d7c754c120005bf744c120005bc744c120006bf644c120006bc644c120006df634c120006dc634c120005ef724c120015ec724c120027e8204c120004ff755921001cfe7559210004fd755921001cfc7559210026bf7459210004ff7359210004fc73592100067c5359210004ff7259210014fe7259210014fc72592100067f52592100eebf41592100eebd4159210024ff7059210024fe7059210024fd7059210024fc7059210026be4059210026bc4059210026f71059210026f51059210004ff7598e1001cfe7598e10004fd7598e1001cfc7598e1003cfe7498e10004fd7498e10026de7398e10006df5398e102ae7c5398e10006dc5398e100065c5398e10014fe7298e10004fd7298e10014fc7298e100067f5298e100c6df3198e100c6dd3198e10024fe7098e10024fc7098e10026de3098e10026dc3098e10026f71098e10026f51098e10004ff7558e100067f7558e100047f7558e1001cfe7558e10004fd7558e1001cfc7558e100067c7558e1001c7c7558e10004ff745
  | 6 => 0xd32d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20006de31d8d20006dc31d8d20005be7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d2009df97098d20004ff7598d2001cfe7598d20004fd7598d2001cfc7598d2003cfe7498d20006be7498d2003cbe7498d20004fd7498d20006bd7498d20004bd7498d2007cfe7398d202ae7c5398d200ccfd7298d20006ed7298d200ce7f5298d200ce7d5298d2000cfe7198d20004fd7198d2000cfc7198d2009cfd7098d20006f97098d200057f7558d2005d7c7558d20005bf7458d20005bc7458d20006bf6458d20006bc6458d20005f77158d20055f47158d200cdfb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d2003cfc7458d20006bc7458d2003cbc7458d20006df7358d200067c5358d2009cff7258d20006ef7258d2009e7f5258d2009e7d5258d20004ff7158d20006f77158d20004f77158d2000cfe7158d2000cfc7158d20006f47158d2000cf47158d200ccff7058d20006fb7058d200b4fe7618d20006bf6418d20006bc6418d20006dd6318d200075c5318d20004ff7518d2001cfe7518d20004fd7518d2001cfc7518d2003cfe7418d20004fd7418d20006de7318d20006df5318d202ae7c5318d20006dc5318d200065c5318d20024ff7218d20014fe7218d20024fd7218d20014fc7218d2007e7f5218d2007e7d5218d2007edf3218d2007edd3218d2000cfe7118d20004fd7118d2000cfc7118d20006de3118d20006dc3118d202ae7f7694d200067e7694d200067d7694d202ae7c7694d200067f6494d200073f6494d200063f6494d202be7e6494d200067d6494d202be7c6494d200073c6494d200063c6494d2030d7e7394d2005f5e7394d200067f6394d202ae7e6394d200067d6394d202ae7c6394d2022d7f7294d2022d7d7294d202a67f6294d2022f6e4294d202267e6194d202267c6194d2022e7f6094d2022f7b2094d202a76e2094d202a76c2094d2022f782094d2003cff76d0d20004fe76d0d20004fd76d0d2003cfc76d0d2005d7e75d0d200057d75d0d20006bf64d0d2003ebc64d0d20015ee72d0d20005ed72d0d20004ff7690d20004fe7690d20004fd7690d20004fc7690d20006bf6490d2003ebc6490d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d2005d7c7550d20006bf6450d2003ebc6450d2003cff7610d20004fe7610d20004fd7610d2003cfc7610d20006bf6410d2003ebc6410d20015ee7210d20005ed7210d20025fa7010d20005f97010d20025ec765092003eec7650920024ec7650920015ef7450920017af7450920007af645092003eee645092003eec6450920
  | 7 => 0x912010e3f52d912010ebe52d912010ebd52d912010e3d52d912010ebc52d912010ebf32d912010ebe32d912010ebd32d912010ebc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006be31d9120006bc31d912010ebf21d912010ebe21d912010ebd21d912010ebc21d912010ebf70d912031ebe70d912010ebd70d912031ebc70d9120006bf50d912031ebe50d9120006bd50d912031ebc50d912031ebe30d912031ebc30d912010ebf20d912031ebe20d912031ebc20d9120006bf10d912031ebe10d912031ebc10d9120006bf64991200f5f97099120125fb7059120004ff755912001cfe7559120004fd755912001cfc7559120006bf7459120004ff7359120004fc73591200067c53591200f4ff7259120006ef72591200f67f52591200f67d5259120004ff715912000cfe715912000cfc7159120124ff7059120006fb705912010cfe761912005d7e75191200057d751912003ebe6419120006bd641912010dbe7619120006be761912010cbe76191200073e75191200073d7519120006bf6519120006be6519120006bd6519120006bc65191200073c53191200dfae7219120007ad72191200df3f52191200df3d5219120006be6119120006bc61191200dfbb2019120317ae2019120317ac20191200dfb8201912003ebf751912003ebe751912003e3e751912003ebd751912003e3d751912003ebc751912003ebf731912003ebe731912003ebd731912003ebc7319120006bf5319120006be5319120006bd5319120006bc53191200063c531912003ebf721912003ebe721912003eae721912003ebd721912003ead721912003ebc72191200debf52191200de3f52191200debe52191200debd52191200de3d52191200debc52191200debf32191200debe32191200debd32191200debc321912003ebf711912003ebe711912003ebd711912003ebc7119120006bf5119120006be5119120006bd5119120006bc5119120006be3119120006bc31191200debf21191200debe21191200debd21191200debc211912003ebf701912003ebe701912003ebd701912003ebc7019120006bf5019120316be5019120006bd5019120316bc5019120316be3019120316bc30191200debf2019120316be20191200debd2019120316bc2019120006bf1019120316be1019120316bc101912005d7e75d8d200057d75d8d20006bf64d8d20006bc64d8d200075c53d8d20004ff75d8d2001cfe75d8d200067e75d8d2001c7e75d8d20004fd75d8d200067d75d8d200047d75d8d2001cfc75d8d2003cfe74d8d20004fd74d8d20006df53d8d200067c53d8d20006dc53d8d200065c53d8d20024ff72d8d20024fd72d8d200b67f52d8d200b67d52d8d200b6df32d8d200b6d
  | 8 => 0x26de3058e20026dc3058e202ae7f7694e202a67e7694e200067d7694e202ae7c7694e202a67f6494e202be7e6494e200067d6494e202a67c6494e202f57e7394e2006f5e7394e202a67f6394e202ae7e6394e200067d6394e202ae7c6394e2022d7f7294e2022d7d7294e2022e7d6294e202267e6194e202a67c6194e202a67e6094e202a76f2094e2022f7b2094e202a7782094e2003cff76d0e20024fe76d0e20004fd76d0e20024fc76d0e2006d7e75d0e200057d75d0e20004ff7690e20024fe7690e20004fd7690e20024fc7690e20336bf6490e2003ebc6490e20006de6390e20006dd6390e20004ff7650e20024fe7650e20004fd7650e20024fc7650e200057f7550e2006d7c7550e20006de6350e20006dd6350e2003cff7610e20024fe7610e20004fd7610e20024fc7610e2032ebf6410e2003ebc6410e20025fa7010e20005f97010e20004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff745862003cfc7458620004ff7358620004fc73586200067e53586200067c535862002e7f525862002e7d5258620026f77158620066f65158620006f55158620066f64158620066f43158620066f6215862002ef52158620024ff7058620024fe7058620024fd7058620024fc7058620026f61058620026f4105862003cff76d0620024fe76d0620004fd76d062006d7e75d06200057d75d0620326bf64d062003ebc64d0620004ff7650620004fd7650620024fc765062026ebf645062003ebc6450620005ef7250620015ec725062000ef66150620006f56150620004ff76cc620024fe76cc620004fd76cc62000ef661cc620006f561cc620004ff764c620004fd764c620024fc764c6200057f754c62006d7c754c620005ef724c620015ec724c62003cfe76d9120004ff75d912001cfe75d9120004fd75d912001cfc75d9120006bf54d9120006be54d9120006bd54d9120006bc54d9120004fe73d9120004fd73d91200067c53d9120024ff72d9120014fe72d9120024fd72d9120014fc72d912010e7f52d912010e7d52d912010ebf42d912010ebd42d912000cfe71d9120004fd71d912000cfc71d9120006be41d9120006bc41d912003cbe76d9120006bf65d9120006be65d9120006bd65d9120006bc65d91200073c53d912031faf72d912010fac72d912010f3f52d912010f3d52d9120006be61d9120006bc61d912010fbb20d912031fae20d912031fac20d912010fb820d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d91200063c53d912031ebf72d912010ebe72d912010ebd72d912010ebc72d912010ebf52d
  | 9 => 0xd305483003cff76d0830024fe76d0830004fd76d083003ebe64d0830006bd64d0830004ff7650830004fd7650830024fc765083003ebe6450830006bd6450830016ee6250830006ed6250830005fb7050830025f87050830014fd76cc8302ad7f75cc8302ad7c75cc8300cede63cc830016ee62cc830006ed62cc830025fa70cc830005f970cc8300ccff764c8300057f754c8300857c754c8300cede634c830005f7714c830075f4714c830004ff75584300067f75584300047f755843001cfe7558430004fd755843001cfc75584300067c755843001c7c7558430004ff745843003cfc745843000cfd73584300067e53584300067c5358430004ff7258430014fe7258430014fc72584300067f52584300067d5258430026f77158430076f65158430006f55158430076f64158430076f43158430076f62158430024fc7058430026f61058430026f4105843003cff76d0430024fe76d0430004fd76d04300857e75d04300057d75d043003ebe64d0430006bd64d0430004ff7650430004fd7650430024fc765043003ebe6450430006bd6450430005df7350430005dc735043000ef66150430006f5615043000cfd76cc4302af5c53cc43000ef661cc430006f561cc430025fa70cc430005f970cc4300c4ff764c4300057f754c4300857c754c43034f5c534c430004ff7648430004fd7648430024fc7648430005df7348430005dc7348430016ee6248430006ed624843000ef66148430006f56148430025fb764c030006fb764c030004fb764c0300077b754c03033f78754c030007bb744c030007b8744c030025fb734c030027db734c030346fa634c030027da634c0302af7a534c0302af78534c03033f7b524c03000779524c030004ff755922001cfe7559220004fd755922001cfc7559220026bf7459220004ff7359220004fc73592200067c53592200f67f52592200f67d52592200f6bf42592200f6bd4259220004ff715922000cfe715922000cfc7159220024fe7059220024fc7059220026be4059220026bc4059220026ef2059220026ed2059220004ff7598e2001cfe7598e20004fd7598e2001cfc7598e2003cfe7498e20004fd7498e20026de7398e202ae7c5398e200ce7f5298e200ce7d5298e200cedf3298e200cedd3298e2000cfe7198e20004fd7198e2000cfc7198e20024fe7098e20024fc7098e20026de3098e20026dc3098e20004ff7558e200067f7558e200047f7558e2001cfe7558e20004fd7558e2001cfc7558e200067c7558e2001c7c7558e20004ff7458e20006bf7458e20004bf7458e2003cfc7458e20006bc7458e2003cbc7458e20026df7358e200067c5358e2009e7f5258e2009e7d5258e2009edf3258e2009edd3258e20004ff7158e2000cfe7158e2000cfc7158e20024fe7058e20024fc7058e20
  | 10 => 0xc530097d4314c530005fb704c530025f8704c530004ff7648530004fe7648530004fc76485300067f65485301367c6548530006bf6448530006bc6448530004fe76d01300067f65d013012e7c65d0130006bf64d013003ebc64d0130005de73d0130005dd73d013003cff7650130004fd765013003cfc76501300067f65501300fe7c6550130006bf645013003ebc6450130005df7350130005dc73501300067f65cc13008e7c65cc130006bf64cc130006bc64cc130025de73cc130026df63cc130024fa76cc1300077b65cc13036f7865cc130007bb64cc130007b864cc130025fa73cc130026fb63cc130027db63cc1302af7a53cc1302af7853cc130007da43cc130007d943cc13036f7b52cc1300077952cc130007db32cc130007d932cc130004ff755903001cfe7559030004fd755903001cfc7559030026bf7459030006be5459030006bd545903003cff735903003cfd73590300067c5359030004ff7259030014fe7259030014fc72590300067f5259030004ff715903000cfe715903000cfc7159030024fe7059030024fc7059030026be4059030026bc4059030026df3059030026dd30590302ae7f7694c302ae7e7694c302ae7d7694c302ae7c7694c302ae7f6494c302be7e6494c300067d6494c302ae7c6494c302ad7e7394c302af5e7394c302ae7e6394c300057d7294c3022e7e6294c302ae7c6294c302267e6194c302ae7c6194c302af7a7094c302af797094c302a67e6094c302af5f3094c302af7a3094c302a75d3094c30004fd76d0c300857e75d0c300057d75d0c303675c53d0c30004ff7690c3003cfd7690c3003ebe6490c30006bd6490c3035ede6390c30025fa7090c30005f97090c30004ff7650c300057f7550c300857c7550c30356de6350c3003cff7610c30024fe7610c30004fd7610c30024fc7610c3003ebe6410c30006bd6410c302af5c5310c300079d4310c30025fa7010c30005f97010c30004ff755883001cfe7558830004fd755883001cfc7558830004ff745883003cfc7458830014fd73588300067e53588300067c5358830026ef725883007e7f525883007eee5258830006ed525883007eee425883007eec3258830004ff715883000cfe715883000cfc715883007eef2158830024fc7058830026df3058830026dd3058830026ee2058830026ec20588300067f76548302867e76548300067d76548302867c76548302867f64548302967e64548300067d64548302867c64548300075f73548302ad7c73548300075c73548300055c73548300ce7e63548302ed7f72548300876f72548302867f62548300167e62548302876e62548300166e625483007e7d62548302876d62548300066d62548300167c62548301be7e61548302867c61548302867e60548302875f30548302877a30548302875
  | 11 => 0x9d7f72549300a76f725493009e7f62549300167e62549300167c62549301be7e61549301be7c61549302875e3054930004fe76d0930004fd76d093003cfc76d09300067f65d09301b67c65d0930006bf64d093003ebc64d0930005de73d0930005dd73d09300079e43d0930004ff7650930004fe7650930004fc76509300067f65509301a67c6550930006bf645093003ebc64509300079e43509300b4fe76cc9300057f75cc9300a57c75cc9300067f65cc9301967c65cc930006bf64cc930006bc64cc9300075e53cc93038f5c53cc930005de76cc9300b6de76cc9300075f75cc93038f5c75cc9300075f65cc93038f5c65cc930005df74cc930005dd74cc9300079f64cc930386de64cc930386dc64cc9300079c64cc9300069c64cc93009ddd72cc930016de62cc930016dc62cc93009f5f52cc93009f5d52cc930025de70cc930025dc70cc930024fc764c9300057f754c9300a57c754c9300067f654c9301867c654c930006bf644c930006bc644c9300075e534c93037f5c534c930006ef624c930016ec624c930005f7714c930095f4714c930005fb704c930025f8704c930025dc764c930016dc764c930024dc764c9300075f754c93037f5c754c9300075f654c93037f5c654c930005df744c930005dd744c9300079f644c930376de644c930376dc644c9300079c644c9300069c644c93009ddf724c930007cf724c930007cf624c930016de624c930016dc624c93009fcc624c93009f5f524c93009f5d524c930007d7714c930007d4714c930007db704c930025de704c930025dc704c930007d8704c93000cfe76d85300067f65d85300067c65d8530006bf64d8530006bc64d8530096f661d8530004ff75d853001cfe75d8530004fd75d853001cfc75d853003cfe74d8530004fd74d8530024fd73d853000cfc73d85300067e53d85300067c53d8530014fe72d8530004fd72d8530014fc72d85300067f52d85300067d52d8530006df32d8530006dd32d8530096f631d8530006f721d8530096f421d8530096f710d85300057f75585300a57c75585300067f65585300067c6558530005bf7458530005bc7458530006bf6458530006bc6458530005ef725853009dec7258530096f46158530004fe76d0530004fd76d053003cfc76d05300a57e75d05300057d75d05300067f65d05301767c65d0530006bf64d053003ebc64d0530005de73d0530005dd73d05300079d43d0530004ff7650530004fe7650530004fc76505300067f65505301667c6550530006bf645053003ebc64505300079d43505300acfe76cc5300067f65cc5301567c65cc530006bf64cc530006bc64cc53000ef661cc530024fc764c5300057f754c5300a57c754c5300067f654c5301467c654c530006bf644c530006bc644c530006f7614c53000ef4614
  | 12 => 0xe5119130006bd5119130006bc5119130006be3119130006bc3119130006bf2119130006be2119130006bc211913003ebf701913003ebe701913003ebd701913003ebc7019130006bf501913032ebe5019130006bd501913032ebc501913032ebe3019130006bd301913032ebc3019130006bf201913032ebe201913032ebc2019130006bf101913032ebe101913032ebc10191300057e7694d300be7e7694d300bc7e7694d300067f6494d300073f6494d300063f6494d302be7e6494d300067d6494d302be7c6494d300073c6494d300063c6494d300a57e7394d300a75e7394d300057d7294d3022e7e6294d3022e7c6294d302267e6194d302267c6194d302a75e3094d30024fe76d0d30024fc76d0d300a57e75d0d300057d75d0d300067f65d0d3021e7c65d0d30006bf64d0d3003ebc64d0d30025fa70d0d30005f970d0d30004fe7690d300067f6590d301de7c6590d30006bf6490d3003ebc6490d300075e5390d303a75c5390d30005de7690d30006de7690d300075f6590d303a75c6590d303addd7490d300079f6490d3003ede6490d3003edc6490d300079c6490d3003e9c6490d30005dd7290d303a75f5290d30025de7090d30025dc7090d303379e4090d303379c4090d30024fc7650d300057f7550d300a57c7550d300067f6550d301f67c6550d30006bf6450d3003ebc6450d300075e5350d3039f5c5350d30005fb7050d30025f87050d30025dc7650d3003edc7650d30024dc7650d300075f7550d3039f5c7550d300075f6550d3039f5c6550d300079f7450d300079f6450d3003ede6450d3003edc6450d300079c6450d3003e9c6450d30005df7250d3039f5f5250d30007db7050d30025de7050d30025dc7050d30007d87050d30004fe7610d300067f6510d301d67c6510d30006bf6410d3003ebc6410d30395de7310d30014fe76d89300a57c75d89300067f65d89300067c65d8930006bf64d8930006bc64d893009eee62d8930004ff75d89300067f75d893001cfe75d8930004fd75d893001cfc75d89300067c75d893001c7c75d893003cfe74d8930004fd74d8930024fd73d8930014fc73d89300067e53d89300067c53d893009e7f52d893009eee32d893000cfe71d8930004fd71d893000cfc71d8930006ee21d893009eec21d893009eef20d89300057f75589300a57c75589300067f65589300067c6558930005bf7458930005bc7458930006bf6458930006bc645893009eec6258930005f77158930095f471589300067f76549300057e76549300067e76549300047e76549300067d76549300057c76549300067c76549300047c76549300067f64549300073f64549300063f64549302967e64549300067d64549302967c64549300073c64549300063c64549300057c73549300075e43549300075d4354930
  | 13 => 0x9130006bf54d9130006be54d9130006bd54d9130006bc54d913003cfe73d913003cfc73d91300067c53d9130014fe72d9130004fd72d9130014fc72d91300067f52d9130006be42d9130006bc42d913000cfe71d9130004fd71d913000cfc71d9130006be41d9130006bc41d913003cbe76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91303379f73d91300073c53d9130006be62d9130006bc62d91300073f52d9130006be61d9130006bc61d91303379e30d91303379c30d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130336bf73d9130006bd73d9130006bf53d9130006be53d9130006bd53d9130006bc53d91300063c53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d91300063f52d9130006be52d9130006bd52d9130006bc52d9130006be32d9130006bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d9130006be31d9130006bc31d9130006bf21d9130006be21d9130006bc21d9130006bf70d9130336be70d9130006bd70d9130336bc70d9130006bf50d9130336be50d9130006bd50d9130336bc50d9130336be30d9130336bc30d9130006bf20d9130336be20d9130336bc20d9130006bf10d9130336be10d9130336bc10d91300a57e75991300057d75991300067f65991300067c6599130006bf64991300057f75591300a57c75591300067f65591300067c6559130004ff75591300067f75591300047f755913001cfe7559130004fd755913001cfc75591300067c755913001c7c7559130006bf7459130004ff7359130006df73591300067c5359130004ff7259130014fe7259130014fc72591300067f5259130004ff715913000cfe715913000cfc7159130004ff7059130006fb7059130004fe76191300067f65191300067c651913003ebe6419130006bd6419130005be7619130006be7619130004be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c65191300079d73191300073c5319130006be6219130006bc62191300073f5219130006be6119130006bc611913032f9e301913032f9c301913003ebf751913003ebe751913003ebd751913003ebc751913003ebf731913003ebd731913003e9d7319130006bf5319130006be5319130006bd5319130006bc53191300063c531913003ebf721913003ebe721913003ebd721913003ebc7219130006bf52191300063f5219130006be5219130006bd5219130006bc5219130006be3219130006bc321913003ebf711913003ebe711913003ebd711913003ebc7119130006bf5119130006b
  | 14 => 0xaef47358630006f75358630006f65358630006765358630006f55358630006f45358630006745358630006f74358630006f64358630006f54358630006f44358630006f77258630006f67258630006f57258630006f47258630006f75258630006775258630006f65258630006f55258630006755258630006f45258630006f74258630006f64258630006f54258630006f44258630006f73258630006f63258630006f53258630006f43258630026f77058630026f67058630026f47058630026f75058630026f65058630026f55058630026f45058630026f74058630026f64058630026f54058630026f44058630026f73058630026f63058630026f53058630026f43058630026f72058630026f62058630026f52058630026f4205863003cff76d0630024fe76d0630004fd76d06300bd7e75d06300057d75d06301767e65d06300067d65d0630326bf64d063003ebc64d063000ef661d0630006f561d0630004ff7650630004fd7650630024fc76506301667e65506300067d655063026ebf645063003ebc6450630005df7350630005dc735063000ef66150630006f56150630094fd76cc6301567e65cc6300067d65cc6303c75c53cc63000ef661cc63000cff764c6300057f754c6300bd7c754c6301467e654c6300067d654c6303bf5c534c63000ef6614c630006f5614c630005fb704c630025f8704c630004ff7648630004fd7648630024fc76486301367e65486300067d6548630005df7348630005dc734863000ef66148630006f56148630025f976cc230006f976cc2300277a65cc2300277965cc230027da73cc2302af7a53cc2303b7da53cc2300075a53cc2303b7d953cc2302af7853cc2303b77b52cc2300077952cc230027f261cc230027f161cc2300a57e76d95300a67e76d953001c7e76d95300a57c73d95300057d72d95300067e62d95300067c62d95300067e61d95300067c61d95302a75e30d95302a75c30d95300067f74d95300067e74d95300067d74d95300067c74d95302a67f73d95300a67e73d953001c7e73d95300a67d73d95300a67c73d953001c7c73d95300067f72d95300067e72d95300067d72d95300047d72d95300067c72d95300067e42d95300067c42d95300067e32d95300067c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067e41d95300067c41d95300067e31d95300067c31d95300067f21d95300067e21d95300067c21d95300067f70d95302a67e70d95300a67d70d95302a67c70d95302a67e40d95302a67c40d95302a67e30d95300a67d30d95302a67c30d95300067f20d95302a67e20d95302a67c20d95300067f10d95302a67e10d95302a67c10d953003cfe76d91300067f65d91300067c65d9130004ff75d913001cfe75d9130004fd75d913001cfc75d
  | 15 => 0xd7294e3022e7e6294e302a67c6294e302267e6194e302a7766194e30226766194e302a7756194e302a67c6194e302ae7e6094e302a75f3094e300bd7e75d0e300057d75d0e3021e7e65d0e300067d65d0e3003ebe64d0e30006bd64d0e303d75c53d0e3020ef661d0e30025fa70d0e30005f970d0e301de7e6590e300067d6590e30336bf6490e3003ebc6490e301fef66190e3003cff7650e300057f7550e300bd7c7550e301f67e6550e300067d6550e3003ebe6450e30006bd6450e301e6f66150e30005fb7050e30025f87050e301d67e6510e300067d6510e3032ebf6410e3003ebc6410e303cf5c5310e300079d4310e301c6f66110e30004ff7558a3001cfe7558a300067e7558a3001c7e7558a30004fd7558a300067d7558a3001cfc7558a30004ff7458a3003cfc7458a300067e5358a300067c5358a30026ef7258a300b67f5258a300b6ee4258a300b6ee3258a30004ff7158a3000cfe7158a3000cfc7158a30024fc7058a30026df3058a30026dd3058a30026ee2058a30026ec2058a302857f7654a300067f7654a300047f7654a302867e7654a302857d7654a300067d7654a300047d7654a302867c7654a302867f6454a302967e6454a300067d6454a302867c6454a300075f7354a300057c7354a300075c7354a300055c7354a3009e7d6354a302ed7f7254a300bf6f7254a302867f6254a300167e6254a300b67d6254a300167c6254a301be7e6154a30287766154a301be766154a30287756154a302867c6154a302867e6054a302875f3054a3003cff76d0a30024fe76d0a30004fd76d0a301b67e65d0a300067d65d0a3003ebe64d0a30006bd64d0a301aef661d0a30004ff7650a30004fd7650a30024fc7650a301a67e6550a300067d6550a3003ebe6450a30006bd6450a30016ee6250a30006ed6250a3019ef66150a3009cfd76cca300057f75cca300bd7c75cca301967e65cca300067d65cca3018ef661cca30014ff764ca300057f754ca300bd7c754ca301867e654ca300067d654ca30016ee624ca30006ed624ca30005f7714ca300adf4714ca3017ef6614ca30005fb704ca30025f8704ca30004ff755863001cfe7558630004fd755863001cfc7558630004ff745863003cfc74586300067e53586300067c5358630004ff7258630014fe7258630014fc72586300067f52586300067d5258630026f77158630006f751586300aef65158630006f551586300aef451586300aef641586300aef441586300aef63158630006f721586300aef621586300aef42158630024fc7058630026f61058630026f41058630006f77558630006f67558630006f57558630006f47558630006f77458630006f67458630006f57458630006f47458630006f75458630006f65458630006f55458630006f45458630006f57358630
  | 16 => 0xcb30386dc64ccb30016de62ccb300cfce62ccb30007cd62ccb30016dc62ccb300cf5f52ccb300cf5d52ccb30025de70ccb30007da70ccb30007d970ccb30025dc70ccb3007cff764cb300057f754cb3008d7c754cb300075e534cb303df5c534cb30005f7714cb300c5f4714cb30005df764cb3007edf764cb300075f754cb303df5c754cb30005df744cb30005dd744cb30376de644cb30376dc644cb30007cf724cb30016de624cb30016dc624cb300cf5f524cb300cf5d524cb30007d7714cb30007d4714cb30025de704cb30025dc704cb3008d7e75d87300057d75d87300c6f661d873000cff76587300c6f46158730004ff755873001cfe7558730004fd755873001cfc7558730004ff745873003cfc7458730024fc73587300067e53587300067c5358730004ff7258730014fe7258730014fc72587300067f52587300067d5258730006df3258730006dd32587300c6f431587300c6f7105873003cff76d0730004fe76d0730004fd76d073008d7e75d07300057d75d073003ebe64d0730006bd64d0730005de73d0730005dd73d07300079d43d0730004ff7650730004fd7650730004fc765073003ebe6450730006bd64507300079d4350730024fd76cc73000ef661cc730006f561cc730025fa70cc730005f970cc730074ff764c7300057f754c73008d7c754c7300c7d4314c730004ff7648730004fd7648730004fc764873003ebe64d0330006bd64d0330005de73d0330005dd73d033003cff765033003ebe6450330006bd6450330005df7350330005dc73503300067f74596300067e74596300067d74596300067c74596300be7f73596300be7e73596300067d73596300be7c73596300067f72596300047f72596300067e72596300067d72596300067c72596300067e42596300067c42596300067e32596300067c32596300067f71596300067e71596300067d71596300067c71596300067e41596300067c41596300067e31596300067c31596300067f21596300067e21596300067c21596300267f70596300267e70596300267d70596300267c70596300267f40596300267e40596300267d40596300267c40596300267f30596300267e30596300267d30596300267c30596300267f20596300267e20596300267d20596300267c20596300267f10596300267e10596300267d10596300267c1059630004ff755923001cfe7559230004fd755923001cfc7559230026bf74592300067c5359230004ff7259230014fe7259230014fc72592300067f5259230004ff715923000cfe715923000cfc7159230024fc7059230026be4059230026bc4059230026df3059230026dd30592302a57d7694e300a67d7694e300a47d7694e302a67f6494e302be7e6494e300067d6494e302a67c6494e302f57e7394e300bf5e7394e300057
  | 17 => 0x6ed624844000ef66148440006f56148440004ff75d933001cfe75d9330004fd75d933001cfc75d9330006de73d93302ae7c53d9330014fe72d9330004fd72d9330014fc72d93300067f52d933000cfe71d9330004fd71d933000cfc71d9330006f970d9330336be40d9330336bc40d9330004fd769933008d7e75993300057d7599330006bf649933003cff7659330004ff755933001cfe7559330004fd755933001cfc7559330006bf74593300067c5359330004ff7259330014fe7259330014fc72593300067f5259330006be4259330006bc4259330004ff715933000cfe715933000cfc715933003ebe6419330006bd64193302ae7e7694f302ae7d7694f302ae7f6494f302be7e6494f300067d6494f302ae7c6494f302ad7e7394f302af5e7394f300057d7294f3022e7e6294f302ae7c6294f302267e6194f302ae7c6194f302af7a7094f302af797094f3008d7e75d0f300057d75d0f30024fd7690f3003ebe6490f30006bd6490f302af5e5390f302af5c5390f30025fa7090f30005f97090f30025dd7690f3003edd7690f30024dd7690f3003ede6490f300079e6490f300079d6490f3003edc6490f30005dd7290f3035f5f5290f30025de7090f30007da7090f30007d97090f30025dc7090f303379e4090f303379c4090f300057f7550f3008d7c7550f300075e5350f303575c5350f30005df7650f30006df7650f300075f7550f303575c7550f300079f7450f3003ede6450f3003edc6450f30005df7250f303575f5250f30025de7050f30025dc7050f30024fd7610f3003ebe6410f30006bd6410f30025fa7010f30005f97010f30005be74d8b30005bd74d8b300ceee62d8b30014ff7658b300ceec6258b30004ff7558b3001cfe7558b30004fd7558b3001cfc7558b30004ff7458b3003cfc7458b30024fc7358b300067e5358b300067c5358b300ce7f5258b300ceec3258b30004ff7158b3000cfe7158b3000cfc7158b300ceef2058b300067f7654b300067e7654b300067d7654b300067c7654b300067f6454b302967e6454b300067d6454b302967c6454b302ad7c7354b300075e4354b300075d4354b300cd7f7254b3008f6f7254b300167e6254b300ce7d6254b300167c6254b301be7e6154b301be7c6154b3003cff76d0b30004fe76d0b30004fd76d0b30006bf64d0b3003ebc64d0b30005de73d0b30005dd73d0b300079e43d0b30004ff7650b30004fd7650b30004fc7650b30006bf6450b3003ebc6450b300079e4350b30005fb7050b30025f87050b30024fd76ccb302ad7f75ccb302ad7c75ccb302af5e53ccb302af5c53ccb30016ee62ccb30006ed62ccb30025fa70ccb30005f970ccb30025dd76ccb30016dd76ccb30024dd76ccb302af5f75ccb302af5c75ccb30005df74ccb30005dd74ccb30386de64c
  | 18 => 0xc744c840006de634c840006dd634c8403779c434c840016ee624c840006ed624c840005f7714c8400d5f4714c84017ef6614c840005fb704c840025f8704c840004ff755844001cfe7558440004fd755844001cfc755844000cfd7458440004ff7358440004fc73584400067e53584400067c5358440004ff7258440014fe7258440014fc72584400067f52584400067d5258440024ff7158440026f77158440006f751584400d6f65158440006f551584400d6f4515844003ef7415844003ef441584400d6f631584400d6f43158440006f721584400d6f621584400d6f42158440024fc7058440026f61058440026f41058440006f77558440006f67558440006f57558440006f4755844003ef7745844003ef6745844003ef4745844003ef7545844003ef6545844003ef5545844003ef45458440006f77358440006f67358440006f57358440006f47358440006f75358440006f65358440006765358440006f55358440006f4535844000674535844003ef7435844003ef6435844003ef5435844003ef44358440006f77258440006f67258440006f57258440006f47258440006f75258440006775258440006f65258440006f55258440006755258440006f4525844003ef7425844003ef6425844003ef5425844003ef44258440006f73258440006f63258440006f53258440006f43258440026f77058440026f67058440026f47058440026f75058440026f65058440026f55058440026f45058440026f74058440026f64058440026f54058440026f44058440026f73058440026f63058440026f53058440026f43058440026f72058440026f62058440026f52058440026f4205844003dbf765044011ebf765044003f3e655044003f3d6550440005bc735044003f9e6350440006bd635044003f9d63504400069d63504400073e53504403e73c53504400ddbe72504400ddbc725044003fae6250440006bd625044003fad6250440006ad62504403e73f52504400073d525044003dbf715044003fb7715044000ebe615044003fb6615044000eb6615044003fb5615044000ebc615044026dbf705044026ebe605044003fba605044026fb71050440004ff76cc440024fe76cc440004fd76cc4401567e65cc4400067d65cc440005bf74cc44003dbc74cc440006de63cc440006dd63cc44014eee62cc440006ed62cc44000ef661cc440006f561cc440004ff764c440004fd764c440024fc764c4400057f754c4400e57c754c4401467e654c4400067d654c440005bf744c44003dbc744c440006de634c440006dd634c44013eee624c440006ed624c44000ef6614c440006f5614c440004ff7648440004fd7648440024fc76484401367e65484400067d6548440005bf744844003dbc7448440006de6348440006dd6348440016ee6248440
  | 19 => 0x884001c7e7558840004fd75588400067d755884001cfc7558840014fd7458840004ff7358840004fc73588400067e53588400067c5358840006be435884003ebc4358840024ff7258840026ef72588400de7f5258840006ef52588400066f52588400deee5258840006ed52588400deec525884003eef42588400debe425884003ebc425884003eec425884003eac42588400deee32588400deec3258840004ff715884000cfe715884000cfc715884003ebf41588400deef2158840006ee21588400deec2158840024fc7058840026bf4058840026bd4058840026ee2058840026ec2058840006ef7558840006ee75588400066e7558840006ed75588400066d7558840006ec755884003eef74588400deaf745884003eee745884003eec745884003eef545884003eee545884003eed545884003eec5458840006ef7358840006ee7358840006ed7358840006ec7358840006ef5358840006ee53588400066e5358840006ed5358840006ec53588400066c535884003eef435884003eee4358840006ae435884003eed435884003eec435884003eac4358840006ef7158840006ee7158840006ed7158840006ec7158840006ef5158840006ee5158840006ed5158840006ec515884003eef415884003eaf415884003eee415884003eed415884003eec4158840006ee3158840006ec3158840026ef7058840026ee7058840026ec7058840026ef5058840026ee5058840026ed5058840026ec5058840026ef4058840026af4058840026ee4058840026ed4058840026ad4058840026ec4058840026ef3058840026ee3058840026ed3058840026ec3058840026ef1058840026ee1058840026ed1058840026ec10588402857f76548400067f76548400047f76548402867e76548402857d76548400067d76548400047d76548402867c76548400073f74548402973c74548401267e64548400057c73548400067e63548402875e63548400065e63548400067d63548402875d63548400065d63548400073e43548402973c43548402ed7f72548400e76f72548402867f62548400167e62548402876e62548400166e62548400de7d62548402876d62548400066d62548400167c62548400df3e42548400df3c42548401be7e61548402877661548401be7661548402877561548402867c61548402973f41548402867e60548402873f40548402877a40548402873d4054840297794054840004ff76cc840024fe76cc840004fd76cc8400057f75cc8400e57c75cc8401967e65cc8400067d65cc84003dbe74cc840005bd74cc840006de63cc840006dd63cc8403879c43cc840016ee62cc840006ed62cc84018ef661cc840004ff764c840004fd764c840024fc764c8400057f754c8400e57c754c8401867e654c8400067d654c840005bf744c84003db
  | 20 => 0x26de5098c40026dd5098c40026dc5098c40026df4098c40026de4098c40026dd4098c40026dc4098c40026df2098c40026de2098c40026dd2098c40026dc2098c40026df1098c40026de1098c40026dd1098c40026dc1098c40004ff7558c400067f7558c400047f7558c4001cfe7558c40004fd7558c4001cfc7558c400067c7558c4001c7c7558c40026df7358c40006df5358c40006de5358c40006dd5358c400067c5358c40006dc5358c400065c5358c4003edf4358c4003ebc4358c4003edc4358c40004ff7258c40014fe7258c40014fc7258c400067f5258c40006de3258c40006dc3258c40004ff7158c4000cfe7158c4000cfc7158c4003ebf4158c40006de3158c40006dc3158c40026de3058c40026dc3058c40006df7558c400065f7558c40006de7558c40006dd7558c40006dc7558c400065c7558c4003edf7458c4003ede7458c4003edc7458c4003edf5458c4003ede5458c4003edd5458c4003edc5458c40006df7258c40006de7258c40006dd7258c40006dc7258c40006df5258c400065f5258c40006de5258c40006dd5258c40006dc5258c4003edf4258c4003ede4258c4003edd4258c4003edc4258c40006df7158c40006de7158c40006dd7158c40006dc7158c40006df5158c40006de5158c40006dd5158c40006dc5158c4003edf4158c4003e9f4158c4003ede4158c4003edd4158c4003edc4158c40006df2158c40006de2158c40006dc2158c40026df7058c40026de7058c40026dc7058c40026df5058c40026de5058c40026dd5058c40026dc5058c40026df4058c40026de4058c40026dd4058c40026dc4058c40026df2058c40026de2058c40026dd2058c40026dc2058c40026df1058c40026de1058c40026dd1058c40026dc1058c402a57f7694c402ae7f7694c400047f7694c402a67e7694c402a57d7694c400067d7694c400047d7694c402ae7c7694c402be7e6494c402f57e7394c400e75e7394c402ae7e6394c402a75e6394c400065e6394c400067d6394c402a75d6394c400065d6394c402bf3c4394c400057d7294c4022e7e6294c402a76e6294c4022e6e6294c402a76d6294c402a67c6294c403f73e4294c402bf3c4294c402267e6194c402a7766194c40226766194c402a7756194c402a67c6194c402bf3f4194c402a67e6094c402a73f4094c402a77a4094c402a73d4094c402bf794094c4003dbd7690c40006bd7690c4003f3e6590c4003f3d6590c4003dbe7390c4003f9e7390c4003f9e6390c40006bd6390c4003f9d6390c400069d6390c400073e5390c403ef3c5390c400ddbe7290c400ddbc7290c4003fae6290c4003fad6290c403ef3f5290c40005bd7190c4003fb66190c4003fb56190c40335bd7090c40336be6090c4003fba6090c40004ff755884001cfe75588400067e755
  | 21 => 0xc74d8540004fe73d8540004fd73d85400067e53d85400067c53d8540014fe72d8540004fd72d8540014fc72d85400067f52d85400067d52d8540006bf42d8540006bd42d85400eef641d854003cfd70d8540326be40d8540326bc40d85400eef710d85400057f75585400fd7c7558540005df7358540005dc7358540005ef72585400f5ec72585400eef46158540024fc7650540006f7615054000ef46150540005fb7050540025f87050540004fe76cc540004fd76cc540004fc76cc540004ff764c540004fe764c540004fc764c5400057f754c5400fd7c754c540004ff7648540004fe7648540004fc764854003e7f745944003e7e745944003e7d745944003e7c74594400067f73594400067e73594400067d73594400067c73594400047c735944003e7f435944003e7e435944003e7d435944003e7c43594400067f72594400047f72594400067e72594400067d72594400067c725944003e7f425944003e7e425944003e7d425944003e7c42594400067e32594400067c32594400067f71594400067e71594400067d71594400067c715944003e7f415944003e7e415944003e7d415944003e7c41594400067e31594400067c31594400067f21594400067e21594400067c21594400267f70594400267e70594400267d70594400267c70594400267f40594400267e40594400267d40594400267c40594400267f30594400267e30594400267d30594400267c30594400267f20594400267e20594400267d20594400267c20594400267f10594400267e10594400267d10594400267c1059440004ff7598c402ae7f7598c4001cfe7598c40004fd7598c4001cfc7598c402ae7c7598c4001c7c7598c40026de7398c40006df5398c40006de5398c40006dd5398c402ae7c5398c40006dc5398c400065c5398c4003edf4398c4003edc4398c40014fe7298c40004fd7298c40014fc7298c400067f5298c40006de3298c40006dc3298c4000cfe7198c40004fd7198c4000cfc7198c40006de3198c40006dc3198c40026de3098c40026dc3098c40006df7598c400065f7598c40006de7598c40006dd7598c40006dc7598c400065c7598c4003ede7498c4003edd7498c4003edc7498c4003edf5498c4003ede5498c4003edd5498c4003edc5498c40006df7298c40006de7298c40006dd7298c40006dc7298c40006df5298c400065f5298c40006de5298c40006dd5298c40006dc5298c4003edf4298c4003ede4298c4003edd4298c4003edc4298c40006df7198c40006de7198c40006dd7198c40006dc7198c40006df5198c40006de5198c40006dd5198c40006dc5198c4003edf4198c4003ede4198c4003edd4198c4003edc4198c40006df2198c40006de2198c40006dc2198c40026de7098c40026dd7098c40026dc7098c40026df5098c40
  | 22 => 0x8d400067d75d8d400047d75d8d4001cfc75d8d40006df53d8d400067c53d8d40006dc53d8d400065c53d8d40014fe72d8d40004fd72d8d40014fc72d8d400067f52d8d4000cfe71d8d40004fd71d8d4000cfc71d8d40006de31d8d40006dc31d8d40006df6398d400057f7558d400fd7c7558d40006dd6318d400075c5318d40004ff7518d4001cfe7518d40004fd7518d4001cfc7518d40006df5318d402ae7c5318d40006dc5318d400065c5318d40014fe7218d40004fd7218d40014fc7218d400067f5218d4000cfe7118d40004fd7118d4000cfc7118d40006de3118d40006dc3118d4032ebe4018d4032ebc4018d402ae7f7694d400067e7694d400067d7694d402ae7c7694d400fd7e7394d400ff5e7394d400067f6394d402ae7c6394d400057d7294d4022e7e6294d4022e7c6294d402267e6194d402267c6194d402bf7b4094d402a73e4094d40024fe7690d40006df6390d40006dc6390d40025fa7090d40005f97090d40024fc7650d400057f7550d400fd7c7550d40006df6350d40006dc6350d40005fb7050d40025f87050d40014fe76d89400f6ee62d8940004ff75d894001cfe75d8940004fd75d894001cfc75d8940024fd74d8940014fc74d8940004fe73d8940004fd73d89400067e53d89400067c53d89400f67f52d89400f6ee42d894000cfe71d8940004fd71d894000cfc71d8940006ee21d89400f6ec21d894003cfd70d89400f6ef20d89400f6ec62589400067f76549400067e76549400067d76549400067c76549400057c73549400067f63549400067c63549400f57f72549400ff6f72549400f67f62549400167e62549400167c62549401be7e61549401be7c61549402977b40549402873e4054940005be76d094003ebe76d094010cbe76d0940006bc63d09400073e53d09404073c53d09400f5bd72d0940016be62d0940016bc62d09400f73f52d09400f73d52d0940025be70d0940025bc70d094003ebf60d094003fbb60d0940024fc7650940006ef6250940016ec625094003fac4250940005fb7050940025f87050940025bc7650940016bc7650940024bc7650940006bc63509400073e53509403ff3c535094003dbf725094003faf7250940007af6250940016be6250940016bc62509400f7ac62509400f73f52509400f73d5250940007bb7050940025be7050940025bc7050940007b8705094003ebf605094003fbb60509400f7af2050940004fe76cc940004fd76cc940004fc76cc9400057f75cc9400fd7c75cc940006df63cc940006dc63cc940004ff764c940004fe764c940004fc764c9400057f754c9400fd7c754c940006df634c940006dc634c940005f7714c9400edf4714c94000cfe76d85400eef661d8540004ff75d854001cfe75d8540004fd75d854001cfc75d8540024fd74d854000cf
  | 23 => 0x67e5358a400067c5358a40006be4358a40006bc4358a40026ef7258a4010e7f5258a4010ebe4258a4010eee4258a4010ebc4258a40004ff7158a4000cfe7158a4000cfc7158a40024fc7058a40026bf4058a40026bd4058a40026ee2058a40026ec2058a400067f7654a402867e7654a400067d7654a402867c7654a400073f7454a400073c7454a400f67d6454a400057c7354a400067e6354a400067d6354a400073e4354a400073c4354a402ed7f7254a401176f7254a402867f6254a400167e6254a4010e7d6254a400167c6254a4010f3e4254a4010f3c4254a401be7e6154a402867c6154a402867e6054a402873f4054a402977b4054a40014ff7650a4031dbf7450a40016ee6250a40006ed6250a40005fb7050a40025f87050a40004ff76cca40024fe76cca40004fd76cca400057f75cca401157c75cca4003dbe74cca40005bd74cca40006de63cca40006dd63cca400079c43cca40004ff764ca40004fd764ca40024fc764ca400057f754ca401157c754ca40005bf744ca4003dbc744ca40006de634ca40006dd634ca400079c434ca40005f7714ca40105f4714ca40004ff75586400067f75586400047f755864001cfe7558640004fd755864001cfc75586400067c755864001c7c7558640004ff7358640004fc73586400067e53586400067c5358640004ff7258640014fe7258640014fc72586400067f52586400067d5258640026f77158640106f65158640006f55158640106f64158640106f43158640106f62158640024fc7058640026f61058640026f41058640325bd76d064003ebd76d064003f3e75d064003f3d75d0640005be73d0640006bd63d06400073e53d06404173c53d064010dbe72d064003dbc72d0640006bd62d06404173f52d06400073d52d064000ebe61d064000ebc61d064003dbf70d0640325bd70d064003fba60d064000cff765064000ef66150640006f56150640005fb7050640025f8705064026dbf765064000ebf765064000cbf7650640005bc7350640006bd63506400073e535064040f3c535064010dbe725064010dbc7250640006bd625064040f3f52506400073d525064003dbf715064003fb7715064000ebe615064026fb6615064026fb5615064000ebc615064026dbf7050640007bb705064026fb8705064003ebe605064026fb71050640004ff76cc640024fe76cc640004fd76cc640005bf74cc64003dbc74cc64000ef661cc640006f561cc640004ff764c640004fd764c640024fc764c6400057f754c6401157c754c640005bf744c64003dbc744c640004ff7648640004fd7648640024fc7648640005bf744864003dbc744864000ef66148640006f561486400fd7e75d8d400057d75d8d400075c53d8d40004ff75d8d4001cfe75d8d400067e75d8d4001c7e75d8d40004fd75d
  | 24 => 0xf7254b4012f6f7254b401267f6254b400167e6254b401267d6254b400167c6254b401273f4254b401be7e6154b401be7c6154b4003dbf7650b400debf7650b400dcbf7650b40006be6350b400073e5350b404373c5350b4003faf7250b4003faf6250b40016be6250b40016bc6250b4003fac6250b401273f5250b401273d5250b40025be7050b40025bc7050b40127af2050b40004ff76ccb4003cfe76ccb40004fd76ccb400057f75ccb4012d7c75ccb40004ff764cb40004fd764cb4003cfc764cb400057f754cb4012d7c754cb40005f7714cb4011df4714cb40005fb704cb40025f8704cb40004ff755874001cfe7558740004fd755874001cfc7558740024fc7458740004ff7358740004fc73587400067e53587400067c5358740004ff7258740014fe7258740014fc72587400067f52587400067d525874003ebf4258740006bd425874003ef7715874003ef7415874003ef4415874026ebe405874003ebc405874011ef71058740004ff76cc74003cfe76cc740004fd76cc740004ff764c740004fd764c74003cfc764c7400057f754c74012d7c754c740004ff7648740004fd764874003cfc7648740004ff7598e4001cfe7598e40004fd7598e4001cfc7598e40026de7398e402ae7c5398e40014fe7298e40004fd7298e40014fc7298e400067f5298e4000cfe7198e40004fd7198e4000cfc7198e40024fe7098e40026de3098e40026dc3098e40004ff7558e400067f7558e400047f7558e4001cfe7558e40004fd7558e4001cfc7558e400067c7558e4001c7c7558e40026df7358e400067c5358e40004ff7258e40014fe7258e40014fc7258e400067f5258e40004ff7158e4000cfe7158e4000cfc7158e40024fc7058e40026de3058e40026dc3058e402ae7f7694e402a67e7694e400067d7694e402ae7c7694e400fe7d6494e402f57e7394e401175e7394e402ae7e6394e400067d6394e400057d7294e4022e7e6294e402a67c6294e4042f3e4294e4042f3c4294e402267e6194e402a67c6194e402a67e6094e402a73f4094e402bf7b4094e40006de6390e40006dd6390e40025fa7090e40005f97090e4003dbe7390e403379e6390e40006bd6390e403379d6390e400073e5390e404273c5390e4010dbe7290e4010dbc7290e404273f5290e40005bd7190e40337ba7090e40335bd7090e40007b97090e4003ebe6090e400057f7550e401157c7550e40006de6350e40006dd6350e4003f9c4350e40005fb7050e40025f87050e4032dbd7610e4003ebd7610e4003f9e7310e40006bd6310e400073e5310e4041f3c5310e4010dbe7210e4003dbc7210e4041f3f5210e40005bd7110e4003dbf7010e4032dbd7010e4003fba6010e40004ff7558a4001cfe7558a40004fd7558a4001cfc7558a40004ff7358a40004fc7358a40
  | 25 => 0x8d2100cff7218d2100cfd7218d2144e7f5218d2144e7d5218d2144edf3218d2144edd3218d21014ff7118d21014fd7118d21446df3118d21446dd3118d2144ef72118d21446f42118d21024fe7018d21004fd7018d21446f71018d212ae7f7694d210067e7694d210067d7694d212ae7c7694d210067f6494d212be7e6494d210067d6494d212be7c6494d212b57e7394d211375e7394d210067f6394d212ae7e6394d210067d6394d212ae7c6394d2122d7f7294d2122d7d7294d212267f6294d212267f6194d2122f772194d212276e2194d212276c2194d21227742194d212a67c6094d21227771094d2103cff76d0d21004fe76d0d21004fd76d0d2103cfc76d0d211357e75d0d210057d75d0d21004ff7690d21004fe7690d21004fd7690d21004fc7690d21006df6390d21006dc6390d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d211357c7550d21006df6350d21006dc6350d2103cff7610d21004fe7610d21004fd7610d2103cfc7610d2100df67110d21005f57110d21024fe76d8121004ff75d812101cfe75d8121004fd75d812101cfc75d812103cfe74d8121004fd74d8121004fe73d8121004fd73d81210067e53d81210067c53d812100cfd72d81212fe7f52d81212fe7d52d8121014fd71d81212fefa20d812129efa10d8121006fb60981210057f75581211357c7558121005bf7458121005bc7458121005df7358121005dc73581211357e75181210057d7518121026fa6018121006f96018121004ff7598f4001cfe7598f40004fd7598f4001cfc7598f40024fe7498f4003ede7398f402ae7c5398f4003edf4398f4003edc4398f40014fe7298f40004fd7298f40014fc7298f400067f5298f4003ebf4298f4000cfe7198f40004fd7198f4000cfc7198f40336be4098f4003ebc4098f40004ff7558f400067f7558f400047f7558f4001cfe7558f40004fd7558f4001cfc7558f400067c7558f4001c7c7558f40024fc7458f4003edf7358f400067c5358f4003edf4358f4003edc4358f40004ff7258f40014fe7258f40014fc7258f400067f5258f40004ff7158f4000cfe7158f4000cfc7158f402ae7f7694f402be7e7694f400067d7694f402ae7c7694f4043d7e7394f4012f5e7394f402ae7e6394f400067d6394f400057d7294f4022e7e6294f4022e7c6294f402bf3f4294f402267e6194f402267c6194f40004ff7558b4001cfe7558b40004fd7558b4001cfc7558b40024fc7458b40004ff7358b40004fc7358b400067e5358b400067c5358b4003eef7258b401267f5258b4003eef4258b4003eec4258b40004ff7158b4000cfe7158b4000cfc7158b40126ef2058b400067f7654b402967e7654b400067d7654b402967c7654b400057c7354b400067e6354b400067d6354b401257
  | 26 => 0x14fe72d8131004fd72d8131014fc72d81310067f52d81310067d52d8131006df32d8131006dd32d8131006f731d81310c6f431d81310c6fa10d81311457e75981310057d75981310067f65981310067c6598131006fb60981310057f75581311457c75581310067f65581310067c6558131005bf7458131005bc7458131005ef725813113dec72581310067f65181310067c6518131026fa6018131006f9601813103cfe76d9121004ff75d912101cfe75d9121004fd75d912101cfc75d9121004fe73d9121004fd73d91210067c53d912100cff72d912100cfd72d912146e7f52d912146e7d52d912146ebf42d912146ebd42d9121014ff71d9121014fd71d9121466bf41d9121466bd41d9121024fe70d9121004fd70d9121466f710d912119cfd76991211357e75991210057d7599121006bf6499121005de7399121005dd739912119ded729912115df5719912103cff76591211adef725912116df77159121004ff755912101cfe7559121004fd755912101cfc7559121006bf7459121004ff7359121004fc73591210067c53591211acff7259121006ef725912115e7f525912115e7d525912119cff7159121006f77159121004ff7059121024fc705912119ef71059121464fe761912103ebe6419121006bd64191211357e75d8d210057d75d8d210075c53d8d21004ff75d8d2101cfe75d8d210067e75d8d2101c7e75d8d21004fd75d8d210067d75d8d210047d75d8d2101cfc75d8d2103cfe74d8d21004fd74d8d21006df53d8d210067c53d8d21006dc53d8d210065c53d8d2100cff72d8d2100cfd72d8d2145e7f52d8d2145e7d52d8d2145edf32d8d2145edd32d8d21014ff71d8d21014fd71d8d21456df31d8d21456dd31d8d21024fe70d8d21004fd70d8d2117cfd7698d21006df6398d2117ded7298d2113df57198d21004ff7598d2101cfe7598d21004fd7598d2101cfc7598d2103cfe7498d21004fd7498d21444fe7398d212ae7c5398d2117cfd7298d21006ed7298d2114e7f5298d2114e7d5298d2118cfd7198d21006f57198d2114ef72198d2118ef42198d21024fe7098d21004fd7098d2118ef71098d210057f7558d211357c7558d2118def7258d2114df77158d21004ff7558d210067f7558d210047f7558d2101cfe7558d21004fd7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d2103cfc7458d21006df7358d210067c5358d2118cff7258d21006ef7258d2113e7f5258d2113e7d5258d2117cff7158d21006f77158d2114cf77158d21004ff7058d21024fc7058d21454fe7618d21006dd6318d210075c5318d21004ff7518d2101cfe7518d21004fd7518d2101cfc7518d2103cfe7418d21004fd7418d2118cfe7318d21006de7318d21006df5318d212ae7c5318d21006dc5318d210065c531
  | 27 => 0xc6590d314975c5390d311ffd43190d3103cff7650d3100cfe7650d311e4fd7650d3100cfc7650d310057f7550d311457c7550d310067f6550d311f67c6550d31006bf6450d3103ebc6450d3148f5c5350d31005f77150d3100df47150d311e7d43150d311fcfe7610d310067f6510d311d67c6510d310079d4310d31014fe76d89311457c75d89310067f65d89310067c65d893113eee62d8931004ff75d89310067f75d893101cfe75d8931004fd75d893101cfc75d89310067c75d893101c7c75d893103cfe74d8931004fd74d893100cfd73d89310067e53d89310067c53d893113e7f52d893113eee42d893113eee32d893118eef21d8931024fe70d8931004fd70d893113eec20d89310057f75589311457c75589310067f65589310067c655893113eec62589310067f76549310057e76549310067e76549310047e76549310067d76549310057c76549310067c76549310047c76549310067f64549312967e64549310067d64549312967c64549310057c73549311be7f635493128d7f72549311476f725493113e7f62549310167e62549310167c62549311be7f61549311bf5e31549311bf5c31549311bf7431549312867c6054931004fe76d0931004fd76d093103cfc76d09310067f65d09311b67c65d0931006bf64d093103ebc64d0931004ff7650931004fe7650931004fc76509310067f65509311a67c6550931006bf645093103ebc6450931006ef6250931016ec6250931444fe76cc9310057f75cc9311457c75cc9310067f65cc9311967c65cc9310075e53cc9314875c53cc931445de76cc93145ede76cc9310075f75cc9314875c75cc9310075f65cc9314875c65cc931386de64cc931386dc64cc93117ddd72cc931016de62cc931016dc62cc93113f5f52cc93113f5d52cc93100dde71cc93100ddc71cc93118edf61cc93100cfc764c9310057f754c9311457c754c9310067f654c9311867c654c9310075e534c93147f5c534c931006ef624c931016ec624c931005f7714c93100df4714c93100ddc764c931016dc764c93100cdc764c9310075f754c93147f5c754c9310075f654c93147f5c654c931376de644c931376dc644c93118ddf724c931007cf724c931007cf624c931016de624c931016dc624c93113fcc624c93113f5f524c93113f5d524c931007d7714c93100dde714c93100ddc714c93117fd4714c93100dd4714c93117edf614c9310077765cc5314777465cc53100df673cc53100fd673cc53100ef763cc53100fd763cc5312af7653cc5312af7453cc53114ef662cc53114ef462cc5314777752cc5310077552cc531007d732cc531007d532cc5310067f65d81310067c65d8131004ff75d813101cfe75d8131004fd75d813101cfc75d813103cfe74d8131004fd74d81310067e53d81310067c53d8131
  | 28 => 0xcb3117fd7104cb311557e75d83310057d75d83311557e75983310057d7598331006fb6098331005bf7458331005bc7458331004ff755833101cfe7558331004fd755833101cfc7558331004ff7458331006bf7458331004bf745833103cfc7458331006bc745833103cbc74583310067e53583310067c5358331004ff7258331014fe7258331014fc72583310067f52583310067d5258331006df3258331006dd3258331096fa1058331026fa6018331006f960183312b57e76d95311467e76d953101c7e76d95312257c73d95310057d72d95310067e62d95310067c62d95312275e31d95312275c31d95312277431d95310067f74d95310067e74d95310067d74d95310067c74d95312267f73d95311467e73d95312267d73d95312267c73d95310067f72d95310067e72d95310067d72d95310047d72d95310067c72d95310067e42d95310067c42d95310067e32d95310067c32d95312267f71d95312267e71d95312267d71d95312267c71d95312267f41d95312267e41d95312267d41d95312267c41d95312267f31d95312267e31d95312267d31d95312267c31d95312267f21d95312267e21d95312267d21d95312267c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f20d95310067c20d95312267f10d95312267e10d95312267d10d95312267c10d953103cfe76d91310067f65d91310067c65d9131004ff75d913101cfe75d9131004fd75d913101cfc75d91310067c53d9131014fe72d9131004fd72d9131014fc72d91310067f52d91311fcff71d91311fcfd71d91311febf41d91311febd41d9131024fe70d9131004fd70d91311457e75991310057d75991310067f65991310067c6599131006bf64991311e5dd739913113dee7299131005ed72991310057f75591311457c75591310067f65591310067c655913120ddf7359131004ff75591310067f75591310047f755913101cfe7559131004fd755913101cfc75591310067c755913101c7c7559131006bf745913120cff7359131006df73591310067c5359131004ff7259131014fe7259131014fc72591310067f52591311e4ff7159131006f77159131004ff7059131024fc70591311fcfe76191310067f65191310067c651913103ebe6419131006bd64191312b57e7694d3149e7e7694d312b47e7694d310067f6494d312be7e6494d310067d6494d312be7c6494d312b57e7394d311475e7394d312267f6394d310057d7294d3122e7e6294d3122e7c6294d312ae7f6194d312275e3194d312275c3194d312af743194d31227543194d312a67c6094d3100cfe76d0d3100cfc76d0d311457e75d0d310057d75d0d310067f65d0d3121e7c65d0d31006bf64d0d3103ebc64d0d3100df671d0d31005f571d0d311c4fe7690d310067f6590d311de7
  | 29 => 0x1557e75193310057d751933103ebe6419331006bd64193311fdde73193312ae7f7694f312ae7e7694f312ae7d7694f312ae7c7694f312ae7f6494f312be7e6494f310067d6494f312ae7c6494f312ad7e7394f312af5e7394f312ae7e6394f310057d7294f3122e7e6294f312ae7c6294f312af767194f312af757194f312275e3194f312af763194f31227563194f312af5c3194f314b7772194f31227742194f312a67e6094f31227771094f311e4fd76d0f311557e75d0f310057d75d0f31006bf64d0f3103ebc64d0f3100cff7690f3100cfd7690f3103ebe6490f31006bd6490f312af5c5390f3100df67190f31005f57190f3120cff7650f310057f7550f311557c7550f31006bf6450f3103ebc6450f314af5c5350f3100cff7610f3100cfd7610f3103cfc7610f3103ebe6410f31006bd6410f310079d4310f3100df67110f31005f57110f3114eee62d8b31014ff7658b3114eec6258b3100df47158b3114fe72158b31004ff7558b3101cfe7558b31004fd7558b3101cfc7558b31004ff7458b3103cfc7458b3100cfc7358b310067e5358b310067c5358b3114e7f5258b3114eec3258b3114ef77158b3117eef2158b3114ef72158b3117ef42158b31004ff7058b31024fc7058b3117ef71058b310067f7654b310067e7654b310067d7654b310067c7654b310067f6454b312967e6454b310067d6454b312967c6454b312ad7c7354b311be7e6354b3128d7f7254b311576f7254b310167e6254b3114e7d6254b310167c6254b31007777154b311bf747154b311be7d6154b311bf5e3154b311bf763154b311bf5c3154b3114f772154b311bf742154b312867e6054b311bf771054b3103cff76d0b31004fe76d0b31004fd76d0b31006bf64d0b3103ebc64d0b3100df671d0b31005f571d0b31004ff7650b31004fd7650b31004fc7650b31006bf6450b3103ebc6450b31005f77150b3100df47150b3100cfd76ccb312ad7f75ccb312ad7c75ccb312af5e53ccb312af5c53ccb31016ee62ccb31006ed62ccb3100df671ccb31005f571ccb3100ddd76ccb31016dd76ccb3100cdd76ccb312af5f75ccb312af5c75ccb31386de64ccb31386dc64ccb31016de62ccb3114fce62ccb31007cd62ccb31016dc62ccb3114f5f52ccb3114f5d52ccb3100dde71ccb3118fd671ccb31007d571ccb3100ddc71ccb3114fd721ccb3118fd421ccb3118fd710ccb31454ff764cb310057f754cb311557c754cb310075e534cb314a75c534cb3114df7714cb3100df4714cb31455df764cb3144edf764cb310075f754cb314a75c754cb31376de644cb31376dc644cb31007cf724cb31016de624cb31016dc624cb3114f5f524cb3114f5d524cb3114fd7714cb3100dde714cb3100ddc714cb3117fd4714cb3100dd4714cb3114fd7214cb3117fd4214
  | 30 => 0xc75d894100cfd74d8941004fe73d8941004fd73d89410067e53d89410067c53d894115e7f52d894115eee42d894103cfd71d89411aeef21d8941024fe70d8941004fd70d894115eec20d89411aef710d894115eec62589410067f76549410067e76549410067d76549410067c76549411be7f64549410057c73549410067f63549410067c63549410073f43549410073d435494128d7f72549411676f725494115e7f62549410167e62549410167c62549410077771549411bf7471549411be7f61549412977741549411bf3e41549411bf3c41549411bf7441549412867c60549411bf7710549414cdbe76d094103ebe76d0941005bd73d0941006bc63d09410073e53d09414c73c53d094119dbd72d0941016be62d0941016bc62d094115f3f52d094115f3d52d094100dbe71d094100dbc71d094103ebf61d094103fb761d094126dbe70d09411afb710d094100cfc7650941006ef6250941016ec6250941005f7715094100df4715094100dbc7650941016bc765094100cbc7650941005bf7350941006bc63509410073e53509414bf3c535094103dbf725094103faf7250941007af6250941016be6250941016bc625094115fac6250941016ac625094115f3f525094115f3d5250941007b7715094100dbe715094100dbc715094119fb4715094103ebf615094103fb7615094126dbc705094115faf205094119fb71050941004fe76cc941004fd76cc941004fc76cc9410057f75cc9411657c75cc94103dbe74cc941005bd74cc941006df63cc941006dc63cc9410079f43cc941004ff764c941004fe764c941004fc764c9410057f754c9411657c754c94103dbe744c941005bd744c941006df634c941006dc634c9410079f434c941005f7714c94100df4714c941004ff75d814101cfe75d8141004fd75d814101cfc75d814111ebd74d8141004fe73d8141004fd73d81410067e53d81410067c53d8141014fe72d8141004fd72d8141014fc72d81410067f52d81410067d52d8141006bf42d8141006bd42d814103cfd71d814111efa10d8141006fb60981410057f75581411657c7558141005df7358141005dc7358141005ef725814115dec72581411657e75181410057d7518141026fa6018141006f960181411c5de73d9331004ff75d933101cfe75d9331004fd75d933101cfc75d93311c4fe73d9331006de73d93312ae7c53d9331014fe72d9331004fd72d9331014fc72d93310067f52d9331006f571d9331024fe70d9331004fd70d93311fef710d93311e4fd7699331006bf649933103cff7659331004ff755933101cfe7559331004fd755933101cfc7559331006bf74593310067c5359331004ff7259331014fe7259331014fc72593310067f52593311e6bf41593311e6bd4159331004ff7059331024fc70593311e6f71059331
  | 31 => 0xcb411967e65ccb410067d65ccb4103dbe74ccb41005bd74ccb413879f43ccb41016ee62ccb41006ed62ccb41004ff764cb41004fd764cb4103cfc764cb410057f754cb411757c754cb411867e654cb410067d654cb4103dbe744cb41005bd744cb413779f434cb41005f7714cb4100df4714cb41004ff755834101cfe7558341004fd755834101cfc755834100cfc745834103ebc745834100cbc7458341004ff7358341004fc73583410067e53583410067c5358341004ff7258341014fe7258341014fc72583410067f52583410067d525834103ebf4258341006bd425834103ef6415834103ef5415834103efb705834103efb405834103ebc405834103ef840583410eefa10583411657e75d8d410057d75d8d410075c53d8d41004ff75d8d4101cfe75d8d410067e75d8d4101c7e75d8d41004fd75d8d410067d75d8d410047d75d8d4101cfc75d8d41006df53d8d410067c53d8d41006dc53d8d410065c53d8d41014fe72d8d41004fd72d8d41014fc72d8d410067f52d8d4103cfd71d8d4120edf31d8d41024fe70d8d41004fd70d8d41006df6398d410057f7558d411657c7558d41006dd6318d410075c5318d41004ff7518d4101cfe7518d41004fd7518d4101cfc7518d411c6bd7418d41006df5318d412ae7c5318d41006dc5318d410065c5318d41014fe7218d41004fd7218d41014fc7218d410067f5218d4103cfd7118d411c6dd3118d41024fe7018d41004fd7018d411c6f71018d412ae7f7694d410067e7694d410067d7694d412ae7c7694d410073e7494d410073d7494d412267f6494d412b57e7394d411675e7394d410067f6394d412ae7c6394d410057d7294d4122e7e6294d4122e7c6294d41227767194d41007757194d412267f6194d412bf774194d412273e4194d412273c4194d41227744194d412a67c6094d41227771094d411c5be76d0d4103ebe76d0d4103f3e75d0d4103f3d75d0d41006bc63d0d410073e53d0d414df3c53d0d41005bd72d0d414df3f52d0d4100dbe71d0d4100dbc71d0d4103ebf61d0d4103fb761d0d4126dbe70d0d4120fb710d0d4100cfe7690d411e5bd7490d41006df6390d41006dc6390d4100df67190d41005f57190d4100cfc7650d410057f7550d411657c7550d41006df6350d41006dc6350d4103f9c4350d41005f77150d4100df47150d4103fb44150d4100dbc7650d411e6bc7650d4100cbc7650d410073f7550d414d73c7550d4103dbf7350d4103f9f7350d410079f6350d41006bc6350d410079c6350d410073e5350d414d73c5350d41005bf7250d414d73f5250d41007b77150d4100dbe7150d4100dbc7150d411e7b47150d4103ebf6150d4103fb76150d4126dbc7050d411e7b71050d41014fe76d894115eee62d8941004ff75d894101cfe75d8941004fd75d894101cf
  | 32 => 0x67e70597410067d70597410067c705974103e7f405974103e7e405974103e7d405974103e7c40597410067f20597410067c20597414fe7f10597414fe7e10597414fe7d10597414fe7c1059741004ff7598f412ae7f7598f4101cfe7598f41004fd7598f4101cfc7598f412ae7c7598f4101c7c7598f4100cfe7498f4103ebe7498f4100cbe7498f4103ede7398f412ae7c5398f4103ebf4398f4103edf4398f4103edc4398f41014fe7298f41004fd7298f41014fc7298f410067f5298f4103ebf4298f41006de3298f41006dc3298f411fedd3198f41024fe7098f41004fd7098f4103ebc4098f41004ff7558f410067f7558f410047f7558f4101cfe7558f41004fd7558f4101cfc7558f410067c7558f4101c7c7558f4100cfc7458f4103edf7358f410067c5358f4103edf4358f4103edc4358f41004ff7258f41014fe7258f41014fc7258f410067f5258f41006de3258f41006dc3258f411e6df3158f41004ff7058f41024fc7058f412bd7f7694f412ae7f7694f410047f7694f412be7e7694f412bd7d7694f410067d7694f410047d7694f412ae7c7694f412bf3e7494f410073d7494f412267e6494f412b57e7394f411775e7394f412ae7e6394f410067d6394f412bf3f4394f410057d7294f4122e7e6294f4122e7c6294f412bf3f4294f412267d6194f412273e4194f41227764194f412273c4194f412a67e6094f4103dbf7650f41006bf7650f410073f7550f414f73c7550f4103f3e6550f4103f3d6550f4103f9f7350f41006be6350f410073e5350f414f73c5350f41005bf7250f414f73f5250f4100dbe7150f4100dbc7150f41325bc7050f41004ff7558b4101cfe7558b410067e7558b4101c7e7558b41004fd7558b410067d7558b4101cfc7558b4100cfe7458b4100cfc7458b41004ff7358b41004fc7358b410067e5358b410067c5358b4103eef7258b4116e7f5258b4103eef4258b4103eec4258b4116eec3258b4119eef2158b41004ff7058b41024fc7058b4116eef2058b412957f7654b410067f7654b410047f7654b412967e7654b412957d7654b410067d7654b410047d7654b412967c7654b411be7e6454b410057c7354b410067e6354b410067d6354b412973f4354b410073d4354b4128d7f7254b411776f7254b4116e7f6254b410167e6254b4116e7d6254b410167c6254b4116f3f4254b411be7d6154b411bf3e4154b411bf764154b411bf3c4154b412867e6054b4103dbf7650b414eebf7650b4103f3e6550b4103f3d6550b41005bf7350b41006be6350b410073e5350b414e73c5350b4103faf7250b41016be6250b41016bc6250b4116f3f5250b4116f3d5250b4100dbe7150b4100dbc7150b41325bc7050b4116faf2050b41004ff76ccb4103cfe76ccb41004fd76ccb410057f75ccb411757c75c
  | 33 => 0x775d8532006f675d8532006f575d8532006f475d8532006f774d8532006f674d8532006f574d8532006f474d8532006f754d8532006f654d8532006f554d8532006f454d853214ef773d853217ef673d853214ef573d8532006f753d8532006f653d85320067653d8532006f553d8532006f453d85320067453d8532006f743d8532006f643d8532006f543d8532006f443d853214ef772d853217ef672d853214ef472d853214ef752d853214e7752d853214ef652d853214ef552d853214e7552d853214ef452d853214ef742d853214ef642d853214ef542d853214ef442d853214ef732d853214ef632d853214ef432d8532006f770d8532006f670d8532006f570d8532006f470d8532006f750d8532006f650d8532006f550d8532006f450d853214ef720d853214ef620d853214ef520d853214ef420d85320057f75585321857c75585320067f65585320067c655853217ef4615853214df6761853217ef67618532006f76518532007776518532006776518532006f66518532006f56518532006f4651853200774651853200674651853217fb6741853217fb57418532006f76418532006f66418532006f56418532006f4641853217fd57318532456f76318532007765318532007745318532007d74318532007d4431853218ef7621853244f77521853244f755218532007e7321853244fd6321853244fd4321853244fe432185320067f65d81320067c65d8132006f761d8132006f461d8132004ff75d813201cfe75d8132004fd75d813201cfc75d813203cfe74d8132004fd74d81320067e53d81320067c53d81320ce7f52d81320ce7d52d813200cfe71d8132004fd71d813200cfc71d81320cefa20d81321857e75981320057d75981320067f65981320067c659813217df67198132005f57198132006f76198132006f46198132006fb60981320057f75581321857c75581320067f65581320067c6558132005bf7458132005bc7458132005f7715813217df47158132006f76158132006f461581320067f65181320067c6518132006f76118132006f46118132026fa6018132006f9601813203e7f745974103e7e745974103e7d745974103e7c74597410067f73597410067e73597410067d73597410067c73597410047c735974103e7f435974103e7e435974103e7d435974103e7c43597410067f72597410047f72597410067e72597410067d72597410067c725974103e7f425974103e7e425974103e7d425974103e7c42597410067e32597410067c32597414fe7f71597414fe7e71597414fe7d71597414fe7c715974103e7f415974103e7e415974103e7d415974103e7c41597414fe7f31597414fe7e31597414fe7d31597414fe7c31597414fe7f21597414fe7e21597414fe7d21597414fe7c21597410067f7059741
  | 34 => 0x91320067f65191320067c651913203ebe6419132006bd641913230d7e7694d3251e7e7694d3230c7e7694d320067f6494d322be7e6494d320067d6494d322be7c6494d3230d7e7394d321875e7394d3222e7f6394d3222d7f7294d3222d7d7294d322ae7f6294d3222f5e3294d3222f5c3294d322af6c3294d3222f4c3294d322267e6194d322267c6194d32226746194d322a67c6094d32014fe76d0d32014fc76d0d321857e75d0d320057d75d0d320067f65d0d3221e7c65d0d32006bf64d0d3203ebc64d0d320075e53d0d325175c53d0d32015ee72d0d32005ed72d0d3220ef461d0d32015de76d0d32216de76d0d32014de76d0d323775e75d0d323775d75d0d320075f65d0d325175c65d0d32376df64d0d320079f64d0d32376dd64d0d323779c64d0d32015de72d0d32217ce72d0d32377cd72d0d32015dc72d0d32216df62d0d322175f52d0d322175d52d0d32005dd71d0d32005dd70d0d321ccfe7690d320067f6590d321de7c6590d3203ebe6490d32006bd6490d321cdde7390d321fef46190d3203cff7650d32014fe7650d321ecfd7650d32014fc7650d320057f7550d321857c7550d320067f6550d321f67c6550d32006bf6450d3203ebc6450d32005ef7250d32015ec7250d321e6f46150d32204fe7610d320067f6510d321d67c6510d3203ebe6410d32006bd6410d320075e5310d3250f5c5310d320079d4310d321c6f46110d32205de7610d32376de7610d320075f6510d3250f5c6510d32215de7410d323779e7410d32376df6410d323779e6410d32376dd6410d320079d6410d32015de7210d32015dc7210d321cedf6210d321cf5f5210d321cf5d5210d321cf9f4210d321cf9d4210d32005dd7110d32005dd7010d322af6f75cc9322af6c75cc9320076f65cc9325076c65cc932015ee73cc932017ce73cc932016ef63cc932017cf63cc9322af6e53cc9322af6c53cc932007cf43cc932007cc43cc93200cfe76d85320067f65d85320067c65d853217ef661d8532004ff75d853201cfe75d8532004fd75d853201cfc75d853203cfe74d8532004fd74d8532014fd73d85320067e53d85320067c53d853214e7f52d853214e7d52d8532006f751d853217ef651d8532006f551d853217ef451d853217ef641d853217ef441d853217ef631d853217ef621d8532024fe70d8532004fd70d853217ef710d853217ef410d853217df676d853200cf676d8532006f765d85320077765d85320067765d8532006f665d8532006f565d8532006f465d85320077465d85320067465d8532006f764d8532006f664d8532006f564d8532006f464d853214fd773d85320077653d85320077453d8532007d743d8532007d443d853214f7752d853214f7552d8532007e732d853214fd632d853214fd432d853214fe432d8532006f
  | 35 => 0x1cfc75587320067c755873201c7c7558732004ff745873203cfc7458732014fc73587320067e53587320067c535873213e7f525873213e7d525873218ef4315873218ef62158732004ff7058732024fc70587322ae7f65d83322ae7c65d8332005be74d8332005bd74d83321957e75983320057d75983320067f65983320067c659833218df67198332005f57198332006fb60983320057f75583321957c75583320067f65583320067c6558332004ff75583320067f75583320047f755833201cfe7558332004fd755833201cfc75583320067c755833201c7c7558332004ff745833203cfc74583320067e53583320067c535833209e7f525833209e7d5258332004ff715833200cfe715833200cfc715833209efa20583322ae7f65183322ae7c6518332026fa6018332006f9601833230d7e76d95321867e76d953201c7e76d953222d7c73d953222f5e32d953222f5c32d953222f6c32d95320067e61d95320067c61d95320067f74d95320067e74d95320067d74d95320067c74d953222e7f73d95321867e73d953222e7d73d953222e7c73d953222e7f72d953222c7f72d953222e7e72d953222e7d72d953222c7d72d953222e7c72d953222e7f42d953222e7e42d953222e7d42d953222e7c42d953222e7f32d953222e7e32d953222e7d32d953222e7c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067e41d95320067c41d95320067e31d95320067c31d953222e7f21d953222e7e21d953222e7d21d953222e7c21d95320067f70d95320067e70d95320067d70d95320067c70d953222e7f20d953222e7e20d953222e7d20d953222e7c20d95320067f10d95320067c10d953203cfe76d91320067f65d91320067c65d9132004ff75d913201cfe75d9132004fd75d913201cfc75d9132206dd73d91320067c53d9132204ff72d9132204fd72d91322067f52d91322067d52d9132206bf42d9132206bd42d913200cfe71d9132004fd71d913200cfc71d9132024fe70d9132004fd70d91321857e75991320057d75991320067f65991320067c6599132006bf64991321eddd739913217df67199132005f571991320057f75591321857c75591320067f65591320067c6559132215df7359132005f7715913217df47159132005fb7059132005f87059132004ff75591320067f75591320047f755913201cfe7559132004fd755913201cfc75591320067c755913201c7c7559132006bf7459132214ff7359132006df73591320067c53591321ecff7259132006ef72591321ee7f52591321ee7d5259132004ff7159132006f77159132004f7715913200cfe715913200cfc7159132006f4715913200cf47159132004ff7059132006fb7059132004fb7059132024fc7059132006f87059132024f87059132204fe761
  | 36 => 0xe21d973222e7c21d97322ae7f70d97320067e70d97320067d70d97322ae7c70d973222e7f20d973222e7c20d97320067f10d97320067c10d97322ae7f65d93322ae7c65d93321cdde73d9332004ff75d933201cfe75d9332004fd75d933201cfc75d93321ccfe73d9332006de73d93322ae7c53d9332006ed72d93322067f52d93322067d52d933200cfe71d9332004fd71d933200cfc71d9332024fe70d9332004fd70d93321ecfd76993321957e75993320057d75993320067f65993320067c6599332006bf649933203cff76593320057f75593321957c75593320067f65593320067c6559332004ff75593320067f75593320047f755933201cfe7559332004fd755933201cfc75593320067c755933201c7c7559332006bf7459332006be5459332006bd54593321eedc73593320067c53593321ee7f52593321ee7d52593321eebf42593321eebd4259332004ff715933200cfe715933200cfc7159332004ff7059332024fc70593322ae7f65193322ae7c651933203ebe6419332006bd6419332205de73193322ae7f7694f322ad7e7694f322ae7e7694f3201c7e7694f322ae7d7694f322ae7c7694f322ae7f6494f322be7e6494f320067d6494f322ae7c6494f322ad7e7394f322af5e7394f322ae7e6394f322ad7f7294f322af6e7294f3222d7d7294f322af6d7294f320056d7294f3222f5e3294f322af6e3294f3222f4e3294f322af5c3294f322267e6194f322ae7c6194f322a67e6094f321ecfd76d0f321957e75d0f320057d75d0f320067f65d0f3221e7c65d0f320075e53d0f325275c53d0f321eddd76d0f32386dd76d0f323875e75d0f323875d75d0f320075f65d0f325275c65d0f32386df64d0f32386dd64d0f32015de72d0f32015dc72d0f322175f52d0f322175d52d0f32005dd71d0f32005dd70d0f32014ff7690f32014fd7690f322ae7f6590f322ae7c6590f3203ebe6490f32006bd6490f32015ee7290f32005ed7290f32214ff7650f320057f7550f321957c7550f320067f6550f321f67c6550f32014ff7610f32014fd7610f3203cfc7610f322ae7f6510f322ae7c6510f3203ebe6410f32006bd6410f322af5e5310f322af5c5310f320079d4310f32015ee7210f32005ed7210f32015dd7610f321cedd7610f32014dd7610f322af5f6510f322af5c6510f323879e7410f32386df6410f323879e6410f32386dd6410f320079d6410f32015de7210f321cfce7210f32387cd7210f32015dc7210f321cf5f5210f321cf5d5210f321cf9f4210f321cf9d4210f32005dd7110f32005dd7010f322ae7f65d87322ae7c65d873218ef661d873200cff76587320057f75587321957c75587320067f65587320067c655873218ef46158732004ff75587320067f75587320047f755873201cfe7558732004fd7558732
  | 37 => 0x8d42004fd7518d4201cfc7518d422ae7c5318d4203cfd7218d421ce7f5218d421ce7d5218d421cedd3218d4200cfe7118d42004fd7118d4200cfc7118d42024fe7018d42004fd7018d422ae7f7694d420067e7694d420067d7694d422ae7c7694d4222e7f6494d4230d7e7394d421a75e7394d420067f6394d422ae7c6394d4222d7d7294d4222e7f6294d422bf6f4294d4222f3e4294d4222f3c4294d4222f6c4294d422267e6194d422267c6194d422a67c6094d4222f6f2094d42014fe7690d42006df6390d42006dc6390d42015ee7290d42005ed7290d42015be7690d42206be7690d42014be7690d4203dbe7390d42006bf6390d420079f6390d420079c6390d420073e5390d425373c5390d42015be7290d42207ae7290d42007ad7290d42015bc7290d4203ebf6290d4203faf6290d422073f5290d422073d5290d42005bd7190d42005bd7090d42336bc6090d42207af2090d42014fc7650d420057f7550d421a57c7550d42006df6350d42006dc6350d4203f9c4350d42005ef7250d42015ec7250d42215be7610d4203ebe7610d42205be7310d4203f9e7310d42006bf6310d420079e6310d420079d6310d420073e5310d4252f3c5310d42015be7210d42015bc7210d4203ebf6210d4203faf6210d421cf3f5210d421cf3d5210d42005bd7110d42005bd7010d4232ebc6010d421cfaf2010d4200cfe76d85421a57e75d85420057d75d854219ef661d8542004ff75d854201cfe75d85420067e75d854201c7e75d8542004fd75d85420067d75d85420047d75d854201cfc75d8542014fd74d8542004fe73d8542004fd73d85420067e53d85420067c53d854203cfd72d854216e7f52d854216e7d52d854219ef641d854219ef431d854219ef621d8542024fe70d8542004fd70d854219ef46158542004ff75d814201cfe75d8142004fd75d814201cfc75d8142004fe73d8142004fd73d81420067e53d81420067c53d814203cfd72d81421267f52d81421267d52d814200cfe71d8142004fd71d814200cfc71d8142126fa20d814231ebf6498142006fb60981421a57e75181420057d751814231ebf6418142005de7318142005dd731814219df67118142005f57118142026fa6018142006f960181422ae7e76d97322ad7e73d97322af5e73d973230d5e73d97322af6d72d973222f5e32d97322af6e32d97322af5c32d97320067e61d97322ae7c61d97322ae7f74d97320067e74d97320067d74d97322ae7c74d97322ae7e73d973230c7e73d97320065e73d973222e7d72d97320066d72d973222e7f42d973222e7e42d973222e7d42d973222e7c42d973222e7e32d97322ae7c32d97322ae7f71d97320067e71d97320067d71d97322ae7c71d97320067e41d97320067c41d97320067e31d97322ae7c31d973222e7f21d973222e7
  | 38 => 0x2877671181521bd7671181520057d71181522877571181520057571181522857c71181520067e61181520067c61181522857e70181522867f60181522877a60181522867d60181520077960181522877a2018152547792018152004ff7598f4201cfe7598f42004fd7598f4201cfc7598f42014fe7498f4203ede7398f42006df5398f422ae7c5398f42006dc5398f420065c5398f4203edf4398f4203edc4398f422067f5298f422067d5298f42206dd3298f4200cfe7198f42004fd7198f4200cfc7198f42006de3198f42006dc3198f42024fe7098f42004fd7098f42004ff7558f420067f7558f420047f7558f4201cfe7558f42004fd7558f4201cfc7558f420067c7558f4201c7c7558f42014fc7458f4203ebc7458f42014bc7458f4203edf7358f42006df5358f420067c5358f42006dc5358f420065c5358f4203edf4358f4203ebc4358f4203edc4358f421ee7f5258f421ee7d5258f421eedf3258f42004ff7158f4200cfe7158f4200cfc7158f4203ebf4158f42006de3158f42006dc3158f42004ff7058f42024fc7058f422ae7f7694f422be7e7694f420067d7694f422ae7c7694f4222e7e6494f4230d7e7394f421b75e7394f422ae7e6394f420067d6394f422bf3c4394f4222d7d7294f4222e7d6294f4222f3e4294f4222f6e4294f4222f3c4294f422267e6194f422267c6194f422a67e6094f4203dbd7690f42006bd7690f4203f9e7390f42006bd6390f420073e5390f4253f3c5390f42015be7290f42015bc7290f422073f5290f422073d5290f42005bd7190f42005bd7090f42336be6090f42004ff755874201cfe7558742004fd755874201cfc7558742014fe7458742014fc7458742004ff7358742004fc73587420067e53587420067c535874215e7f525874215e7d525874203ef77158742006f751587421aef4515874203ef7415874203ef441587421aef431587421aef62158742004ff7058742024fc70587421aef71058742004ff755834201cfe7558342004fd755834201cfc7558342014fc7458342004ff7358342004fc73583420067e53583420067c53583420f67f52583420f67d525834203eee425834203eed4258342004ff715834200cfe715834200cfc715834203efb705834203efb405834203ef840583420f6fa20583421a57e75d8d420057d75d8d42004ff75d8d4201cfe75d8d420067e75d8d4201c7e75d8d42004fd75d8d420067d75d8d420047d75d8d4201cfc75d8d42216bd74d8d420067c53d8d4203cfd72d8d422167f52d8d422167d52d8d42216df32d8d4200cfe71d8d42004fd71d8d4200cfc71d8d42024fe70d8d42004fd70d8d42006df6398d420057f7558d421a57c7558d42005f77158d4219df47158d42005fb7058d42005f87058d42006dd6318d42004ff7518d4201cfe751
  | 39 => 0xf4350d520073e4350d521ed7f7250d520157e7250d520157c7250d521ee7f6250d521f76f6250d520057f7150d521bd7e7150d521bd7c7150d520057f7050d522857c7050d522957f7610d520057e7610d520057d7610d522957c7610d522157e7410d522057e7310d522ae7c6310d522973f4310d522975e4310d520073d4310d522975d4310d521cd7f7210d520157e7210d521cd7d7210d520157c7210d521ce7f6210d521d76f6210d521cf3f4210d521bd7e7110d520057d7110d521bd7c7110d522857e7010d520057d7010d521bd7e76d85522957e74d85520057d74d85520057e73d85520057d73d85520067e63d85520067c63d855201d7f72d85520157e72d855201d7d72d85520157c72d85525867f62d855258f6f62d85521bd7d71d85521be7e61d85521bf7661d85521be7661d85521be7c61d85521bf7641d85521bf7431d85521bf7621d85525877521d85522857e70d85520057d70d85521bf7410d85521bd7f76585520057f74585522957c74585520057f73585520075f73585520055f73585520057c73585520075c73585520055c73585520067e63585520067c63585525757f72585520076f725855257d6f72585525767f62585521376f62585521bd7f71585520077761585521be7e61585521be7c61585521bf7461585521be7461585520057f70585522857c70585521bf7710585522957e74d81520057d74d81520067f64d81520067d64d81520057e73d81520057d73d81520067e63d81520067c63d815201d7f72d815201d7d72d81525567f62d815256f6f62d81521bd7e71d81520057d71d81521bd7c71d81520067f61d81520067d61d81525577a20d81525577920d815255d7d76981522957e74981520057d74981520057e73981520057d73981520067e63981520067c63981525657d72981522876d729815205d6d72981522ee7f629815206f6f62981521bd7e71981520057d71981522857c71981520067e61981520067c61981522857e70981522867f60981520077b60981520067b60981520057f74581520073f74581520053f74581522957c74581520073c74581520053c74581520067f64581520067d64581520057f73581520075f73581520055f73581520057c73581520075c73581520055c73581520067e63581520067c635815255d7f72581520076f725815206d6f725815255e7f625815205f6f62581520057f71581520077771581520057771581521bd7e71581521bd7c71581520077471581521bd7471581520067f61581520067d61581520077b60581522867e60581525557e76181522957e74181520057d74181520057e73181520057d73181520067e63181520067c631815201d7f72181520157e721815201d7d72181520157c72181522ee7f621815254f6f62181521bd7e7118152
  | 40 => 0x8d520075c31d8d522857e70d8d520057d70d8d525a57d7698d522957e7498d520057d7498d520067f6498d520067e6498d520067d6498d520067c6498d5230d7e7398d520067f6398d520075f6398d520065f6398d5222d7d7298d520076d7298d521856d7298d5222e7f6298d521976f6298d521bd7e7198d520057d7198d521bd7c7198d520067e6198d520067c6198d522857e7098d520057d7098d520057f7458d522957c7458d520075f6358d520067e6358d525a57f7258d520076f7258d521956f7258d525a67f6258d521876f6258d520057f7158d52007777158d52005777158d521bd7e7158d521bd7c7158d52007747158d521bd747158d520057f7058d522857c7058d5259d7e7618d522957e7418d520057d7418d520067f6418d520067e6418d520067d6418d520067c6418d5222d7e7318d520067f6318d520075e6318d520067d6318d520075d6318d5201d7f7218d520157e7218d5201d7d7218d520157c7218d5230e7f6218d525976f6218d5230f5f3218d5230f5d3218d521bd7e7118d520057d7118d521bd7c7118d520067e6118d520067c6118d520075e3118d520075c3118d522857e7018d520057d7018d522ae7f7418d520067e7418d520067d7418d522ae7c7418d522ae7f7218d5230e7d7218d5201c7d7218d5230e7f4218d5230e7e4218d5230e7d4218d5230e7c4218d5230e7e3218d5230e7d3218d5230e5d3218d522ae7c3218d522ae7f7118d520067e7118d520067d7118d522ae7c7118d520067e4118d520067c4118d520067e3118d520065e3118d522ae7c3118d520065c3118d5230e7f2118d5230e7e2118d5230e7d2118d5230e7c2118d522ae7f7018d520067e7018d520067d7018d522ae7c7018d5230e7f2018d5230e7e2018d5230e7d2018d5230e7c2018d520067f1018d520067c1018d522957f76d0d520057e76d0d522967e76d0d520047e76d0d520057d76d0d522967d76d0d520047d76d0d522957c76d0d520067c63d0d522157f72d0d520157e72d0d522157d72d0d520157c72d0d522167f62d0d5221f6f62d0d521bd7e71d0d520057d71d0d521bd7c71d0d522857e70d0d520057d70d0d520057f7690d520057e7690d520057d7690d520057c7690d521ed7d7490d521cd7e7390d520075f6390d522ae7c6390d520075c6390d520065c6390d520073f4390d522975f4390d520157e7290d522076e7290d520156e7290d522057d7290d520076d7290d520056d7290d520157c7290d522067f6290d521df6f6290d521bd7e7190d520057d7190d521bd7c7190d522857e7090d520057d7090d520057f7650d520067f7650d520047f7650d520057e7650d520057d7650d520057c7650d520067c7650d520047c7650d520075f6350d520067c6350d520075c6350d520065c6350d522975
  | 41 => 0x2ae7c6294c432267e6194c432ae7c6194c432a67e6094c4303dbf7650c43006bf7650c43004bf7650c430073f7550c435df3c7550c4303dbf7350c4303f9f7350c435e6be6350c4303f9e6350c432af3e5350c435df9e5350c430071e5350c435df9d5350c432af3c5350c43005bf7250c435df3f5250c4332dbc7050c43004ff755884301cfe7558843004fd755884301cfc75588430067e53588430067c535884303eef72588431ce7f525884303eef425884303eec42588431ceec3258843004ff715884300cfe715884300cfc7158843004ff7058843024fc70588431ceef2058843004ff755844301cfe7558443004fd755844301cfc75584430067e53584430067c535844303ebf4358443006bd4358443004ff7258443014fe7258443014fc72584430067f525844303ebf425844303ef77158443006f751584431c6f4515844303ef7415844303ef441584431c6f431584431c6f62158443004ff7058443024fc705844303ebc40584431c6f71058443004ff755804301cfe7558043004fd755804301cfc75580430067e53580430067c535804303ede435804303edd4358043004ff7258043014fe7258043014fc72580430067f525804303ebf4258043004ff715804300cfe715804300cfc715804303efb705804303efb405804303ebc405804303ef840580430057e73d91520057d73d915201d7f72d915201d7d72d91525c67f62d91525d76f62d91525c73f42d91525c73d42d91521bd7e71d91520057d71d91521bd7c71d91520067e61d91520067c61d91522857e70d91520057d70d91525cd7d76991525ad7e74991522967f64991520073f64991520063f64991520057e73991522975e73991520055e73991520057d73991522975d73991520055d73991525bd7d72991522976d72991521a56d72991525be7f62991521b76f62991521bd7e71991522977671991521bd7671991520057d71991522977571991520057571991521bd7c71991522857e70991520057d70991520073f64591522967e64591520057f73591520057c73591525cd7f72591520076f72591521b56f72591525ce7f62591521a76f62591520057f71591521bd7e71591521bd7c71591520067e61591520067c61591520057f70591522857c70591525c57e76191525bd7e74191522967f64191522973e64191522967d64191520073d64191520057e73191520057d731915201d7f72191520157e721915201d7d72191520157c72191525ae7f62191525b76f62191525af3f42191525af3d42191521bd7e71191520057d71191521bd7c71191522857e70191520057d70191522957e74d8d520057d74d8d5201d7f72d8d5201d7d72d8d5259e7f62d8d5251f6f62d8d5259f5f32d8d5259f5d32d8d521bd7e71d8d520057d71d8d521bd7c71d8d520075e31d
  | 42 => 0xc73d95432be7f43d95431f67d43d95432be7c43d95430067f72d95430067e72d95430067d72d95430047d72d95430067c72d95432be7f42d95430067e42d95432be7c42d95430067e32d95430067c32d95430067f71d95430067e71d95430067d71d95430067c71d95432be7f41d95430067e41d95432be7c41d95430067e31d95430067c31d95430067f21d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95432be7f40d95432be7c40d95430067f20d95430067c20d95430067f10d95430067c10d95430057e7694d4321e7e7694d4321c7e7694d431f57e7394d431f75e7394d432bf5f4394d430057d7294d4322e7e6294d4322e7c6294d432267e6194d432267c6194d432a67c6094d430067f6590d431de7c6590d4303dde7390d4303edf6390d430073f6590d435ef3c6590d4303dbe7390d4303ebf6390d4303f9f6390d432af3e5390d432af3c5390d435ef3f5290d43005bd7190d43014fe76d89431f57c75d89430067f65d89430067c65d89431eeee62d8943004ff75d89430067f75d894301cfe75d8943004fd75d894301cfc75d89430067c75d894301c7c75d894303cfd73d89430067e53d89430067c53d8943386df43d8943006be43d8943386dc43d89431ee7f52d89431eeee42d89431eeee32d894300cfe71d8943004fd71d894300cfc71d8943024fe70d8943004fd70d89430057f75589431f57c75589430067f65589430067c65589431eeec6258943005f771589431e5f47158943005fb7058943005f8705894300cfe76d85430067f65d85430067c65d85431e6f661d8543004ff75d854301cfe75d8543004fd75d854301cfc75d854303cfd73d85430067e53d85430067c53d8543014fe72d8543004fd72d8543014fc72d85430067f52d85431e6f641d85431e6f631d8543006f721d85431e6f421d8543024fe70d8543004fd70d85431e6f710d85430057f75585431f57c75585430067f65585430067c65585431e6f461585430067f65d81430067c65d8143004ff75d814301cfe75d8143004fd75d814301cfc75d81430067e53d81430067c53d8143014fe72d8143004fd72d8143014fc72d81430067f52d814300cfe71d8143004fd71d814300cfc71d8143006fb20d8143006f820d81431f57e75981430057d75981430067f65981430067c65981431e5f67198143005f57198143006fb60981430057f75581431f57c75581430067f65581430067c65581430067f65181430067c6518143336bf6418143026fa6018143006f960181432ae7f7694c432ae7e7694c432ae7d7694c432ae7c7694c432af3e7494c432af3d7494c432be7e6494c432ad7e7394c432af5e7394c432ae7e6394c432af3f4394c432af5e4394c432bf5d4394c430057d7294c4322e7e6294c43
  | 43 => 0x8b4301c7e7558b43004fd7558b430067d7558b4301cfc7558b430067e5358b430067c5358b4303ebc4358b4303eef7258b432167f5258b4303eef4258b4303eec4258b43216ee3258b43004ff7158b4300cfe7158b4300cfc7158b4303ebf4158b43006ee2158b43216ec2158b43004ff7058b43024fc7058b43216ef2058b43004ff755874301cfe7558743004fd755874301cfc75587430067e53587430067c5358743004ff7258743014fe7258743014fc72587430067f525874303ef7715874303ef7415874303ef4415874320ef63158743006f7215874320ef42158743004ff7058743024fc705874320ef71058743004ff755834301cfe7558343004fd755834301cfc75583430067e53583430067c535834303ede435834303edd4358343004ff7258343014fe7258343014fc72583430067f5258343004ff715834300cfe715834300cfc715834303efb705834303efb405834303ef840583432ae7e7694e432ae7d7694e432af3e7494e432af3d7494e432ad7e7394e432af5e7394e432ae7e6394e432bf5f4394e430057d7294e4322e7e6294e432ae7c6294e432267e6194e432ae7c6194e432a67e6094e43005bd76d0e4303ebd76d0e4303f3e75d0e4303f3d75d0e4303f9e63d0e432af3e53d0e435f79e53d0e430071e53d0e435f79d53d0e432af3c53d0e43005bd72d0e435f73f52d0e43335be70d0e43206ee62d8a43014ff7658a43206ec6258a43004ff7558a4301cfe7558a43004fd7558a4301cfc7558a4303cfc7358a430067e5358a430067c5358a43376df4358a43376dc4358a432067f5258a43206ee5258a43006ed5258a43206ee4258a43206ec3258a43004ff7158a4300cfe7158a4300cfc7158a43004ff7058a43024fc7058a431fef661d864300cff76586430057f75586431dd7c75586431fef46158643004ff75586430067f75586430047f755864301cfe7558643004fd755864301cfc75586430067c755864301c7c755864303cfc73586430067e53586430067c5358643006bf4358643004ff7258643014fe7258643014fc72586430067f52586431fef641586431fef43158643004ff7058643024fc70586431dd7e75982430057d75982431fdf67198243005f57198243006fb6098243004ff755824301cfe7558243004fd755824301cfc75582430067e53582430067c5358243004ff7258243014fe7258243014fc72582430067f5258243004ff715824300cfe715824300cfc7158243026fa6018243006f960182431f57e76d95431f67e76d954301c7e76d95431f57c73d95432bf5f43d95432bf5c43d95430057d72d95430067e62d95430067c62d95430067e61d95430067c61d95430067f74d95432be7e74d95431f67d74d95432be7c74d95432be7f73d95431f67e73d95431f67d73d95431f67
  | 44 => 0x67d62d86532257d71d86532267e61d86532af7661d86532ae7c61d86532a57e70d86530057d70d86532277710d86532257f76586530057f74586532bd7c74586532ad7c73586531467e63586531475e63586530057f725865322d7e725865322d7c72586530067f62586530067d62586532af7761586532267e61586532267c61586532af7461586532267461586532277641586532af7431586530057f70586532a57c70586532bd7e74d82530057d74d82532ae7f64d82530067d64d82532ad7e73d82532af5e73d82530855e73d82532ae7e63d82532af5e63d825322d7e72d82530057d72d82532ad7c72d82532ae7f62d82530067d62d82532257e71d82530057d71d82532ad7c71d82532ae7f61d82530067d61d82530a57d76982532bd7e74982530057d74982532f67e63982530bf5e639825322d7e72982530057d72982532a57c72982530067f62982530067d62982532257e71982532a77671982532257671982530057d71982532a77571982530057571982532a57c71982530067e61982530067c61982532a67f60982532af7b60982530057f74582532bd7c74582530067f64582530067d64582530a67e63582530a75e63582530057f725825322d7e725825322d7c72582530067f62582530067d62582530057f71582532257e71582532257c71582530067f61582530067d61582532af7b60582532a67e60582532bd7e74182530057d74182532ad7e73182532af5e731825308d5e73182532ae7e63182532af5e631825322d7e72182530057d72182532ad7c72182532ae7f62182530067d62182532257e71182530057d71182532ad7c71182530067e61182532ae7c61182532a57e70182532ae7f60182532af7a60182532a67d60182532af79601825300679601825303e7f745974303e7e745974303e7d745974303e7c745974321e7f735974321e7e73597430067d735974321e7c735974303e7f435974303e7e435974303e7d435974303e7c43597430067f72597430047f72597430067e72597430067d72597430067c725974303e7f425974303e7e425974303e7d425974303e7c42597430067e32597430067c32597430067f71597430067e71597430067d71597430067c715974303e7f415974303e7e415974303e7d415974303e7c41597430067e31597430067c31597430067f21597430067e21597430067c21597430067f70597430067e70597430067d70597430067c705974303e7f405974303e7e405974303e7d405974303e7c40597430067f20597430067c20597430067f10597430067c10597432bd7d7694f431f67d7694f431f47d7694f4343d7e7394f4321f5e7394f430057d7294f4322e7e6294f4322e7c6294f432267e6194f432267c6194f432a67e6094f43004ff7558b4301cfe7558b430067e755
  | 45 => 0x3800300240010028004000800000000000004002001c0020058001001000100000070000000000800400140000064004000000000000020030006001c00300140010004001000400a001c0040000002002c00300480000008000000400200280020008001000000000040072ad7e73d92532af5e73d92531d55e73d92532ae7e63d92532af5e63d925322d7e72d92530057d72d92532ad7c72d92532257e71d92530057d71d92532ad7c71d92530067e61d92532ae7c61d92532a57e70d92530057d70d92531f57d76992532be7f64992532af3f649925343e7e639925321f5e639925322d7e72992530057d729925322d7c72992532257e71992530057d71992532257c71992532a57e70992530057d70992532af3f64592532be7e64592531f67e63592531f75e63592530057f725925322d7e725925322d7c72592530057f71592532257e71592532257c71592530067e61592530067c61592530057f70592532a57c70592532bd7e74192532ae7f64192532af3e64192532be7d64192532af3d64192530063d64192532ad7e73192532af5e73192531dd5e73192532ae7e63192532af5e631925322d7e72192530057d72192532ad7c72192532257e71192532af7671192532257671192530057d71192532af7571192530057571192532ad7c71192532a57e70192530057d70192532bd7e74d8a530057d74d8a532ae7f64d8a530067e64d8a530067d64d8a532ae7c64d8a532ad7e73d8a532af5e73d8a535955e73d8a532ae7e63d8a532af5e63d8a5322d7d72d8a5322e7e62d8a532af6e62d8a532ae7c62d8a532257e71d8a530057d71d8a532ad7c71d8a530067e61d8a532ae7c61d8a532a57e70d8a530057d70d8a5322d7f7658a530057f7458a532bd7c7458a530067f6458a530067e6458a530067d6458a530067c6458a532ad7c7358a531867e6358a531875e6358a532af6f6258a5322e7e6258a5322e7c6258a532af6c6258a5322e6c6258a532af6c3258a530057f7158a532257e7158a532257c7158a530067e6158a530067c6158a530057f7058a532a57c7058a530067f7458a530067e7458a530067d7458a530067c7458a531867e7358a5322e7c7358a5301c7c7358a5322e7e4258a5322e7c4258a5322e7e3258a5322e7c3258a5322e6c3258a530067f7158a530067e7158a530067d7158a530067c7158a530067e4158a530067c4158a530067e3158a530067c3158a5322e7f2158a5322e7e2158a5322e7c2158a530067f7058a530067e7058a530067d7058a530067c7058a5322e7f2058a5322e7c2058a530067f1058a530067c1058a532bd7e74d86530057d74d86532ad7e73d86532af5e73d86535fd5e73d86532ae7e63d86532af5e63d865322d7e72d86530057d72d86532ad7c72d86532ae7f62d8653
  | 46 => 0x3000c00000000010000000000400000000000004001000c001001000800080000008002000000a0000000000000100000020000006001c00700180000004001002000300000000000012001400200000120004002000800500080000010000000400000000040000002000c0000000003000800e0018001000400000000000000000001c0000010001004000100000040010005000c0040004005000000400000000000003002000200500010004000001c005001000000040040000006000000000000000010003000000000000000004001000000100080000000005002800000140030000001000000300040000000003000c00200000030000007001800a004800800040020008000000000000140020000005001000b0000002001c0010004002000c00100080050008005000000100080030000001000400000000080000000000000a000000000080090000000000800000040030000010000400000000020008002000c00000040010004002000c0010000001000c0060000000001800200040050000001000000100200030000000000400000000000010000001c0000000002000000d001c00400040010058002001c000001c00200040010004000001c0060000000000400000000090000000001000100000030000004000000c002c009002400000040000000000003c00000040000004001000000000040000000000000c000000c00100080120000001000000100040000000001000c00100000060004000000000900140000004002001000000000000004001000000000080030018001000000000100000004006000000100040000014000000800100040000018002000000200000010000001000000900000040000000000400000040010000000000800700040030010001000400100000000000000000000100000050004000000000100100000004004000400f0004003001400900000000014001000400e000c006000400d000000100000000000000001c018000c00300200020000003000400300000000000000000400000080030000000001c0030028000000000000000030000001001c002000000000000000004001001800400040000004009000000500280000018004000c00400200000004003001800300200000008007000400000140060000004000000200000020000000000000a001c001001800100040000000003001800000140010000000000800f0000000000000100040030000007001c00400100050018000000800a00000020018005002c000000400a000c000000c0000000004000800000000000004000000c0030004004000000000180030004001002c000000801d000400100040030004001001400c0000004000400400040050000000000400000040040004000000000000040020018000
  | 47 => 0x1000000c00000010004001004c00c0000003001000000040060004000006c005000000200000030018004000000a000000100000000018003000000000040040014003000c00e000000000040000004001002c001000400000000000008003000000000000000004001002c00000080000000004005800000040090008000003000100000000004002000c000000800000480000010004000000600100070004000000c003000000000040000004000000000d000000000080020004002000000000040000018000000000100000000044001000000000200000028000000000100040000004003000c00000040040000000003c001000c0000014000000000500000010020001000000200240050000001001c00000080000018000000000e000c000000000a001c00a00100080000005000000000040010020001000000000140010008009002800200000000000001001000000080010020001000c0000008008000000100300000000000000000f000801e00140030000001000000000200020004014000c00e000800000040160004001000000500680000010001000400000000030004005001800200000030038000000c008000400200240020030001001400100000000000000000400000040010010003004c00000240030028000000400200000010000001000400400040000000005000400300200000014001000c00100000000000005000400300100000000011000000000040030000002000000300000000000006000000d0000000000c001000400000040040000011000000000200000000001001c0170000006000000200000010078009000400100200000000001000800500000000018000000000300080030018002000400700000090004000001c001005c0050000001000000000000010008000000000100340000004001000000000080000008000000c000001c000000400400040070000005000000000dc007000400c00280030004000000800300000020000000000400000000000010003000000100040030008004000c00100000020004006001000000100000004001000000600080120020005000000700180000008000000c0030000003001400100000030000000000000900040010000000000800d0018000000000000000000004010000c0210008000000000500080060000000003400400040060008000000001000080000004003000000100080010008001000800400340000000000000000c001c0090000001000400100340030000003002400000080010008005000c00200100010000003000400b002c0000000000000000100100020008000000c001000400f0008006000800000100020010002000000a00100000034005004000000000010000000000800200080070000001003c0010000000000
  | 48 => 0x140060034001000000b00080000004000000000100200020004001000800500140000018000000400000000000014006000c00700040000000004000000000000020000000000000200040030008001001400000000000010004000c004002000000000000000005000000a0000000000000900000050018005002800000000030004005000c0020018000000c00500040030008000000c00000000040000003000c0090000001000800000100010000004000c00400000010000002001c00b000000000380000008003000c001001c00f0000005000000000040000000002000400a001400100000010000000000800900380000004000000c0020000000000000000000010000000000c0010000000002000100000060018000000000000040030008001001400600080000004000002800000080010014005007400400000040000000000000000000070004004000c00000080000004001000400000100040000002001800000000000004002001400500000000008000001000f00080020000003001001500000000000000002001800200000008006000000800180010000000000800600080000000000000000100040030004001001800c000000000040010000000000800000000000004004000000200040020000000001c00000580020004000000800000080000004000002400e000000100000010000000001800000000020000001005c00100000000000000000000700140010000006000c00f00680000004002000000e001400100000010000000000400200040010000001001400000040050008000002800100000000000000000801a001800200080020008000000c00300140020000000000400f001800300140020000003000000000180010008001000c00000040010008000001c0040030000000c003000c00000040030004000000400100000080000000004400000000010004002000c0030000001000800000000010020000000400000000020000002000000100000000000000001c00000000010000001000000a0008004000400100000020028004000000300480020004002001400000200000014000000c0180028000000c00100000010000003000000500000000000001000c0050020009000400900080000004000000800100040000000000000000200000000008000000400100080030008009000000b000c000002800e00000030014008000c00000040010004000000000200000060000006000400600100010000001000400100000040008001002000600000040000002000000000000020004004000000000040030010001000c00000040020004000000c00100000020040000000000e000c002004000a0014003000000000000020000000000400300100010008000002400100000010004001000000
  | 49 => 0x14001000400700180000000000000000200040020000006000c003000400200100010004000000000400040000004000000c00100000000004034000c0020004002003c002005c00200000040014001000000000080030000000002000100000000000000000400a0000000000800900000040000000000c0000008000000c0010004005004c00000080020004001000c00000000010000000000800e000c00000000010000000000000200080000000001000000000040050000004000c000000000900000040000001000000200040030000001000000400040060000000000000100000000004005009000c000c00100040010000001004400400080000004000000400000000000004006000400200100000004000001c00000180010004000005c0000004001000000000000000000000000c000000000200080000008003001c0000060006000000000080030004000000c00e0004003000400900080020000000002c00000380010044000000000c00000010020002002c00000000010008000000000500200110004000000c00200000080000000001000400000010000005000000200040010008003000400000100000008002001000000040010000001000000000000070000000000c000000c0000004002000c0010004002000000100000000000002000c00100000010004000000000200040090004002000c001002c00100080010000000000400100080040000000000c00000040050000000001400000080030014000000400400000010000000000c00000280020020000000c00000000030004003000000000000000000004000400200100050004001000000000000040000002000400000000000014009000000000480080034006000400400200010000000005000000000080010002000c00000000000000001000800600240000000000001c000003c007000000000000000000004000800000000080004002000c00500000010000000001000000080040014002000c000000001100040030008000000400000040000000000001800100180050000000000400000240050004000001c00000040040010002000800100280020024001000000200040000008001000c00100140010004000000800500080000004000001c001000000300040090008000000400000000080000001001000000000000000000000c0010004001000c0000018000000c0090008007000c001000000c0000002000c00a00040020024003000000200080040000003001c0050000001000000000040030004000000800f0000008001c0010000002000000d000800300000010010006001c001000400800000020000002000000400040010004000001c0020000003002400000000040000004000800d000001000000010008007000000500
  | 50 => 0xdf800000000003b1bcac7861598ea10d129a90764000152000001c200000000000000f4180003e0800000016865612e9ccd1000000035fc0000000723005600013ba6d3865a0000000670b14e51b973e108000088694b00000000000000000025c6b87a114e3cbb30bc72dd472500000000000e338000000362466785fa33d958c28b05f09db0000cd180000000a4640200003aba36225600004fe9a302698e2cebd86de41a00002fdbad40000aeedb91d9077800002e3b7ce00000000002bba2198000715267c27e874c00010b25838f08000000000000000000624cc6214000002dc0001852c7f0000a4486ee00000000000ed0000000000000000003cd200001e20000000c7e14ba748800096f00000000000000128e000000000000000003bb41f9000000022a6df2000000034ba0b2800000000005b700009862c4e00000001d68000810800022180000000000daca1580000000000000039a800000022ac839000000034a2000000000000006ac26942758000d8b0000000079800001e600031dc38db216000214c000296ce4c80004b337d6000036e9a40d406f6a99eeae80003482f2682d000000000000003278000000000000000000ee074c8000908bc2e71f000000000003430b74610a4607a5a8bc000295201397ea000207e000136e2b800000000000000000000000007ba000050b916c07cb67e54f00000001b080563aa4e6f3b4c57900004e231f62e100000000414622818800000008228000e0e80000000000c898fea0003c9ec3da0f600010860000000000000000039fe00034ec2190000000038200020e88dc982e0000000aa49e14000000081800008d2355ec36ae10000000000034e60000cb80002c2c5a7b15625f96b000005d600013f802b334296d12a000006586021a2e0001dbe00000000004001000c00000000080014002001400300000020000002000000000000000000001000400300080010000003000000a001000100000000010000001000a000000b0000000001c0000004004001400000000000000006001c002000000200000030000001000400f000c00200040040000007000000000000000000000000000100340010028004001800100040000000002000c000001800000080030000001000c0000024001004c000001c0020000000002c000001800500100070000007001000000040000004003003400000040000018002000000c0000004000c000000800100040000020008002c0010010000000400000100030018000000000300240020000001001400000100010034001000000000000000004000000000500040030000000001c00000040070000012000000000340020034001003400600000020000004000000b000000300000000004002000400400180020000001000c017000c00000000
  | 51 => 0x5740a32a8825b18c0e22a99400000000002a8a2848000e72800000000000002c0607a84fa25780005e691ba6b1800000000000000000b3a800095f000051719520000000cb8000000000005903be225700008ac2abe4d1000000020e2d5b86b60000000000000038d36f000000000002d529569baa00000009e58000d7dbbaea4c044800000000002d6c34db5d22a780001b480000002ff47e29db200000000003b0400000004e40000c6b00000000000cb8800000010f24a1800000000006958000c75ae0c5e6000000026980001f6039f3a3c25a085e3a132681f21b220000000c8e8000eae3c9a00000000001bba41826c4c0a000000036762da04c800013a8f28b5caacb953e000104805a34149ac233800023925f0b1a467a80000000000a0000003c499bc12b32f05c29ed6a2788c2d53835e000000000021902c4b014a36000079700000100000100a00c0000e40b9c0c280001fe05609f0e00025e0d4d8970e679fd477e9d6c61426d85350000b6980000000000000000000000000000000173000003400000002b28000266e0000000000292077e000082f00006e700004f3800033900008882d7a000268c1129cf0d1880000002cd83f8152ada70000000204c55e800000013d62b082a2e7580e80000ee4000000000000007e500004110098ed280ba00038c400000004638000d68076e00000005930000d270000000000000000007c400000000000593800007120d80d88c1e000000000000000000000b7a800000000002c83906465b2dc9d0308c28c9dce3fe800056b0b6e7f0895aa9483f800034e000010d000023144eb80000000000000000000000000001b689d4ab1483205e800000006dd2b3ad46b1c053c00000dc019e000000000000009850000b3400000003058000225e628011e00000000001bbe00000000e524c60000000854163e0001d4c69505d25f180000002abccbd8000627b130000214a7b300000002f0a6b2aa2a43aaefc34700009402dcc74f91c800000c6000000000007d809e2464000000087580000003c4c0002bfa000000008d80000000000000000000000000001afc000000000000008613c880002fa600000000000aae00000005578000000288200021700000000a220000000071c000010800000000000000000073a1f1800092e98840000000657b9b40000000dd58d5ec752a163dbafae4f4849cc8f9280048800000000000000000a2f8000000270a0000000000000032f0f3200007d2000000094c046a0001bfaadb187ad8e1a949918d9e52983ec00000002ec8b66000250a78d800000000003ddaeb0000341ec9b1bca6fe34e84dfb3540000000000000000000000002ee2000000042410fe3440000000000085f000000014b4b5a2e14cb912e6794b2768dd0170e02a6626a49ca0dcc95f8b
  | 52 => 0x34c0000000000000000000008ba3a760000000e6187c06d4000000011a00002e82000240c14280003880fa60000000000137600000001889af600003868ec00004c080000000000000000000000000001a74ed1ad5c00037e600018620000000ae0283695980000000000a128c4471c0e90b25b67000028c40123bf200000000001dd45b80000aa3371e558a1dcc37042c31d0f540000ff6a460fc00000d680000000000000000009ae0000000000000000000004f732b00000000060800000032040000000e0b92e00000000000283adb4b68c83798000001c3600000000f88000000000000000003a00000af3800000000000000000000295000029ac000089eb9034dc10da650000041e6e1000098700000000000ab2bad69f40000000250e000000000008742e500002fc000000000000003b96ac6114a0000000de6827cb602f7a000084e00024e42fb0000b8cb61a0001a604a98fba26e848eb2700000d803e40000000738197c000000000000000000f6c000148eb02873000031e40002310df48000d6a8fce09080000a280008de1cecdb780005553c509e10ea600000003dc800054300004f280000002c5031422c8e40baa8c310000000000000000006318000764a8d4f090f3a087800000019da0000000e2306aa03fb3c645580000000000ba280000000000000040c00000009712db063380a000037760000738e61228c3cb3abe02f2aa413c000000036a200034c4db28000000000080b2fd60000000000139a00000000000000867800063088545180000000053846f800000000009750a24d6480004e6206800000007be27cc0000000000000000010d62cd1f3800000000002d1e1ae8caaabaa29c31512aa0000000000000075f80000000000a0d251cc0d0000cf0800000000003cb8000e5a8000dbd00009aca71c0002a905508000793a6f431b000070d016a8ce8b5aa4f0000b43165000007be0002c1e29c83065f39f8c3c5296a0001fec00038b000000000001d587198000baaa35a000000000000007b500000001c9200018945a30000000000062a090a466000000023ca55b8000000000000000000002d9e000000026f8000df52b32000331e2998940000000000034762c4373a3e4abca954983672f1c30dd90cd462c000084c80a8000048a9150000b880000d0115b40000000000093aa7227d6000089c00022ce000000017b000000022080000000000000000000009fe8000191000000000003550000b2f95060000000ab92492a9e800017da5466601a1a68e2da80002f380000000a228000c9f0b8800000007668000000033c000273275c8000b37072840728921c203dc94f9f40360a6f6a4300009273a2860c104a93525c000021624232e0000000000002e688af00008a61c5c0000252bcc38c83ebadda9c20
  | 53 => 0x91402f6000000000000000000000000260801c8000000265a5c99a321e33926ba680000003b76000373012caca45b080000000ce20000786d9394840ef9b243512ba60003a10000000000000000002c5200021e8d369680acf9ed800030d80002058f3900000000000000000000000008e88000000000009a00000002128db80000000142a0000000dd82df200007220001a680ce2e220000000c8d00007e4800000016c00000000930367800000000001368000061ca020fc49382d463290000cfcaa6e0000000b4b80000000b2aceb00000000000b2d8000040aa600001a40000137c000000000000000000f88e42000043a000010e8000a5582c2000334ebda80000002f9e42ebbfede8ba620740000279000000000000000a384e3000095f800000000000003c5438980000002e0abaca34e30525ba00000006638f18ac313ecc2182867138000e341938000298ac1f000089aa1b6000241674db7deafba2fe9a6ba08a8d00dc2f9a2d400e13620001ba649800003ca80009398000779800000696340000000a37b5be5f80000000000000014ee0000ef8c0b117600000006e380000003b80346bb560000000000024c00000000000bdea830000000279e00f21980000b3800000007f0000000028d230c80000000142000000000000007a0aab022c2b5876200000001aba00025dc000000000000000000000d821864e7f0ea4000140200000005a500001a80830ef80c4686900002b48746743314234e000044523e6000353000000000003b7c423aba2c6400009cf0e5eee791a400000005dc2f84000236aba1800000004e85760d582832ad046c17860003374d3498146a89afacc722c298825d65a4b8b8af90000c2e9af4a30bd1e0003c4ab15800000000000000000ed93126c292c460000000a180000e0a020c0000dbaf0f05b2c8a32bcb6e831ea31b12cab300007c193c639100006d8800000010c0d498000b4b00001379a1e020121200011a675e34fa000000092393c40002f4400010be0000000000000000000000000000be527d8a4e254c1d6000000000000001ec4dd60acc40b9e1e11d07889ff348690a9298a9707b63649a2a9e9349e1df1f6a1f52e0e05825b6c4c8000f2a9206e812d54afa8000ab50780c683568a938fb678112a40001f1283e866e000000000000005eb000058e000066ab32835b981e00000004f88d040001296765029e93eab125b3057a3aaa972b253a2ef2e925c0002712cf22fda2210a700000c8cba786b8000000020fa00e0000000345ac6a91ca3200000000000307a0002b3800000009582630d99aa760002474dcd80003688000000000000000008b4baacd1900000000000d77a24400018c800028060000000000000000000002042a7c0000a001a7800000036da3760bf400000000000000
  | 54 => 0x16400000000000a5b80005c19c0c9d50f58075003200000007662884000149c0000000000113e3ac906c0c4b8942411db80bf00004e8b8fadbdbc6a31fabd60003d2c000000000015000001986a2c000000000004e134d0ae8348295c800000000000ca000000006c473096a0a2a1c280d21a90c2014787410aac00015ba0000bc400036d600000000ff18567d535d880fb2805cbb9c400011b40000b561a5000087894480000000a07000098d213c00000008831df20002b620001c1c11800000000000603b418d883d2a85d0632a8f2aa239616463619996c668da8ce4800025d00000003d12c5480008bb800073fa022814078ec6c2894a7e80008100cc800006a4000270eb89817612d0000d48109e00000000003ae2369800000000007dc3b08a33984088880004fc00000000f8ca58b96c00000000001b4aca3b030000142649a2ef88318d88d4b251400000006cc194829b8a140001858000000000000000001088000000000000000000000000000000000005ed00003498000cc6af8c000379e55c3afe5d91310000000000004fc00033aa00034fc000187c000237aa3a0000000000000000002ae8f000001762000025c0000000000138e000000000000000000000ea3800000000000000000000000000000000000000cd2a23200000000002498365000000000000002680b3a1cfa01a00003730000c22b66255627fe41485b80c9800064c076c63e000000000000000000000000000036ead3d800037834ce64d800000026840000000000000000000000bc0000000173c5fb0000b0500003b5260c9f0ba180f0894cba48f94b7480008e10000128a5ec00007c20001e5e000000019c00000000000968000000000000000000815800000011a2653800000025de0000bd200000000000000c4435dc000000000000000000000000243808c800082e01d600027e0000223600025026a080007c6800092980000001e080002890441800012b9dac00000008781530cc28baa00026a09de8dca3610000cabb032a5300000002bf600017e87d4800035e1fc8689000003a95b65dd80002a2b30810fa7b6b97ba9c72fa7bcede24a440d9100d09b1ea0873b1e6cb09e60001efe68a0000000000000000000000000c7800003598000000235200012c2913800000000000000000c9d000000000002471aea00030707142e840002b86e0480000002fa4c73000059d00000003d26d4528dc0000b760fbb182a8db4c60f028a47cc8000ce980004470000000121022000000003800308000000000000000000000071a0000000d24a08445e00008b5a3d80000000674a7da0002c1a000000000010000002b0830ea09288a00000ca80008040000000043000000000000000000000000000000000000ee4289cc5d000000000000000f5ce7a
  | 55 => 0x18065d4800051a168ec11af4c000000098b80007009a6e6b9800006aafd400020ae03000002b18000383198200025a253db35caff800000000000000000000391e5d1b6fa9ceb90a0c5900ef480e827273708af49da8261987e000000000011c005ca34401715943c70d6ad08203063400000591a6a44b080071e08b62409c90000000018fa01400012920003bbe00000000000000d9b0000000000049cb7b800000009ee800000000000000ae40000000745a1b04b1af8e8ca00004ee0000d701058000000000000000000a0e3df962aefa000017e23223a78000bb300000001124000000000013b6742000061381040000000997902000021c6bb9000000035e8f33bba400000000001f4e87aaae200008900003992000169a913000047e0000ce60d5215b00004e7a4f8c500000000187000000009f1000000028220000000000000095b2eca1048000000000000005628e80000000000000000000000000483815e673800000000000000a7e00000004c60000f02800000000000002cf0871104c0000000bcb37ae7aa25848c7ae760002cca3c68000e55811a8dfab0009e8000000000000000000001846f0a800000017e61dd800049480000ddba4c0001fb0d500000000000000000000002c00c9805a800000001e7ae9694dae6600037c40000d4a8c700000000000a738f74cd800008201648042a6e00001518a8a00003718ba40003c62ab18718acdad8827b28f200039888c9223029a1e120001c98c9f800056400008d93aaae068000ee2a130a6ca41edfd82c60001de46d5afe400004163af80007de800000000002bd0d48de138a0000220e6c28000000000000034c8820b5120001480d58024e0001f464429e10ece80005582076a8e80000000000c890f026a720ea0e200007b0a1a20002186bd209bc5be87ce2f5181274711b8e60b958e72353845f81bc3400712aee1e3c9708000ef6800084300000000ab0b71b7e800037fc000274a1dc8000b1f80009dc1f0c0002a1a0001b3c39e1fc63bbb8a8bb8383645ba3da2a830f0000276a25e2ec2dd2279a000000099f8000e6c186e000000075535c2ce59a2248a190e368000000000003cd8226c5cac184d0b7160000000000262a00008ba0002ed21d1000084e8fb8000000061a8000000000000000000000000c1500000003a220000000e60094e000000000025187d1000062e018a1cfa122000224a000000000026d000000000002de2000278a0002f2000000000000b520000000322000000000002680000f3c0000efe80003072bb299a35e2be411184b38000106ab820003c8cf1e1b5e00000000001e3a098191e07937526b0000000000000000000000000000000000002d365a99ef07b3aae84de119c559248058680000b300005378000259000000000000001f2a000000
  | 56 => 0x9209df0a1c8514339800000023a61708000ea18000eb3b8e2ce70000f1c000000000000003d0a48b800098180009eb1e320000000bae9248b7704d80003c7406c80000003ba600000000000000e8e0000da2235e159a9d487c2d300000a58ac130f44f68000a2b800000011dc73d000058e89a200023b630e1444f18328200000000000000e3ab53a0000b02334a7063740000000000000000007a5000000012f20000000000040e045adbc0392a3eae90000ad5000000000000001ec068800c2000315449f014a0000000923304c91f2a129f280000000a4c000283e9ec80000002d2000000007d91cd4d73a6c600001d8000000000027740000000000000000035ba000155ce9c3496659bcfc4188000000210aa4d8000000000076880004eb0fd20002a5000000f42249eeecf4aa9edd12576732303e0722f069ea8d2800000005e780004e0182002a8000ef5885a000311c3ff0000b1880000000000cbd13c200000000000cbe4f2050094a80000002710637000000038f89d38e980451f42cf900009060000770000000022061148caed61a39620d0000000000001d885200015ee00000000001d600001fde0000000000000066e201200014fe37f05880000000993235400000002881a042a99300000055e7c700000000000000000072c000054e00464468eb688f8000b3036281a695a896e3bccd8fa9a4e3604bac621190d9e80000001a482b980000e323d60003936000000000006f4b0490e0ed7285848223127ed0000e0f0000a58000000000000000000e97abf4000361600010fa5f2800000000000003c5a4f60d4e32b18760002e983d699ca1700000000095400000000000000bc680000003ad8284000000000001718000cfe800000006b2000000000000000001c7a5ae800000031800000000000000000007160003472a86372e254ad8e22b38e8178a99c0000000e3980003488000151800099a80002a72ed000000002f212900000000ad583de417000000000000000000e86b0e0ac705bcab80000a9294560000594ef1123a68580007523c527502160120b640add80000001d0277b281a0001510000000000039d200000006d70c5ec411fe2e458a42b3f8b5ee17a32a000000091e8000b618000000386c350b5581fca9fc2510c18afa36e6792b60a1863b842f88000dc2b3ccb4a3aa29d2197ac3403f20003c6c66c0000a95b848091b14aad7000005f0e70d06917263680000000000000000000015dac10b6600000f4600000000000000000107400033bc00021c8ec5800000034ac1b8b340e6314faec89e3e1bb0000a3d00001f3000000000000000000c1e000085c800000000007d2323cb72800000024ca00000007829308a383c9299c000000030c2000299826400000002304000000034fabc64fa31e800025ac00
  | 57 => 0xe83ab02933944600000000001d5a97d023cb7080000001a1260cb69200000000f102480c0a4a85bd803a4928000dc697740000000da90000000313c000000000000000000000000197e000346800007a21cbb3fc0000000000000000000002f0800046337ee81280f6000152e000000011904e200006029bf000019800006390e4c0000000000006680aabf05d9acbc5bc1f1600001b40002c4c9e4000002e000097c935a6c08000e1db830d6d000000000000000334a3d8000000160602280000000000000383e4ab3ac60001740a2380000002200000000008c0000a0a000000000004378000a8082e200023a80000000000358e00032ec000000000000000000610000000091480000000000000000000000007ea0938000183cc7d0000e3d3b440000000226000000000000003c5e000000056200000002da00000000b580000aad82d400034fe09880003eb14525f42bbe462bc14c910000000306e000357a0000000000310200000000000000000000000000000001c8200008187e100002bc26a80000000000000000013863a70f4a1a700000000000840377a0000000000057600000000000000000307400011740001ae400028684260400697800000000000000000a4b33a824da67600000000000000000123e0000fe20001076ebc00000000000414231865300001ff37b0e8700002c88000000000000000006261dc24f81d960002aa6cc0a9aa7c880007332f586d51b3a9f0054c0000000d6531588493ba84e49e2007738c0e5f21660eb000075c00004b1000000031b800000000002098ea58000209adc0000000080e97b005230f20001bd059a89140001bb8000000000000001be8dde00036ac0000f9c7f3a660282800091d8000000245e9fa00000000000ca1934a51cb7ec2540e249cc09e8000062ce35000000004c40000000d9580e20000000000000000000008b780000003ba2000000014100008e199a69042a4248e298600022e4000185e00000009caa3348a288d0ca69a524bc0274000287400000003c38000530000073a0000107386a7da00008b690706fc9fe6ed6a0beb4400007bca628c2486f07bb3b060002e52698941e9dca41a26a0b0e2c32daa45e9d0eef9a5fa3df1b5acfb00000002d246c698100002ef26cab02e87280000000bf8d87800089e0000000000000000000000000000000000026ee000000000000009468000a0f0000b3f0ba815580000003654990800000034caa012d3c6778e74580000087b3b600888000000221e0000000e0cab200002d5ecfe0ff000000000001872be5b46eeac11460000d8c0000000eeb310ed4ca188c1a0c4828c00000000a9802400000003c34000034ada8390e57ca3584cc800029800003822b8a3d217b6edab86809628c04f78000bcd000077225aabb600
  | 58 => 0xb6c000286a66715f48849df65c21aee4af2ce200000002078000831226200000000000000eee1d345ab80009010c360001b46000000000004f2e413cb400014420001dd6cd59b0ecec00009ad0000acb2d38807b824207229476311b6dc0966eb0c239aba82a081f800000000b1c0000000000000000029029f200000000410c84b9d000000006cd8000d9c8000000384a0002df40000000af4000000000000001b8a09c8888a03b62e78a8000f32000064a0000c880042b64000032c27943690c1ad0ab942ed636480000000deb0000000391a0000000b1d80000000000000000000008ca00039c20002a7e0000000000000000000000000bdce4317d6e53981a5dea870aff000000005180000000a989cc620800003850f40eec19aca03230c56fb4287a634ee000000072b800028980000002cc2000320e5363adc80915a6c14b51e0000000000389800009240002468081b35e0f30a2800000009482a400003c1600000000003b36006056a000000020080000000000d5500001693562e1d260ec4a00000000000000398a0f60b608d308220002c4a0001fe80001288000000000000000000000000000003b00002d439480002a940002d5a000000027f800000017a200000000003b625f5000000000007ff800000000000000000b1e800000016180001186000000030d000042494e60000000044000000000000001d1265b80007ef80000000000a4004d6c51a32cec4832c000000000180009ce00000002e7c0001dbc00023060be9c9600000000002afc52180000000c40e1688466233b0c000158e0001f5c000055a83ca4586ad204400019d46eba028b350b8000000000000f4e00010b0b168a866e01548972061411c0000eb014982b4000000000000fd800000003ca00001c636b00000000000c000000000000000000006829b4899112b0139baf2c30392295eaaf60000d62582a9b864f1b8c6411d5c000000000027de59b000000029d600000000002e8000003460000000d308d70b68800000012eea3e006ebef80a40000000000249a054aff6278ae180000648a7ab6ec0000000b85954a000000000000001b18e4200013700000000000316211e90aa5488704a4204c60000000f03b00a4a887a800023cee1986fc00000000f224ead1d0254000356a134932a67c00005cc8b9c6fb8000adc04280002fb4e6600000000000000385481d00000000000000000032d17564f922700000000000000076d3a60c41800000000000002688b55ac9e0002bc40000000556a56a00020dcc710000d658e6827f0748cf11dc40001c62e32800000000005332f020001be2e7ba2b80000000000000015a11d065e0000a648404166000048d9e2c280800029e852a0000000c6e8000a7bb59e6f6000000000000000000e061d8048037e45bd00000
  | 59 => 0x21d00001adccde8000974000073ababc0002b9453680004201efcb95a03c0000a1600032c8860a76600036687eb30665393c26197238c0cd800000000000000000c0f0000585000000025b2e0709b0000000000027f600000007718fee085219200000000000000000000014486c0007800000000000002ac09b7800000002a024f800002680000000000000000000028ea000000000000000000656d26800068f800000000008188000bd4000000000000001c2c1b31e8c0000000000000077f0cfa000000075b80000000000000003e000037271d21c20000c16eac9346000114c00000001681f3e65d9b448d800002bf92fe00021d400000004668b7e637b60c48c00000000000b2b800051a80000001b143970000e1400000000000a56800000032ee00000000002440d3925240002b240f48000000000052b1424000000000000000001e540000000464800000013e600000000001c200338000ddbb974ce094a8a3f0726000000000000008d9800000005600000fa864280007e200000003a6c000000000006ac3c1000078300000001e7c26e1cf621b00700000b464f41046000026cd7baada33380008020000d2c0000000000000011b200012e20001dee0000ec22173b02699b9c6000000074f0a6c00001a00000000386184a3a8100c50c80001a3000081b80006a6ab105d62cda6ef3b0e0001c7e1d7a0acd600ee600027b8bb00476000000000036180002d3a0000000000000000000000000000000000000011540000000000000000037266688000000000047d201a00000000000000666b2368e400008122d4400010f08190e22d43b25ea7600000002648000000095639a800033b40000000a7f922408b81f40002a0a0001b6a42d0000000000000000000000a1c7be9c080002a72e7017a61bd80006c7077ec27bd220000000e89064c0298000b54000000000006198b3c00000007a3a1ae1952d58000000058a2f820000b8ab6bb432f2400000860f22945a8b80003c986550000b9b11c4e5c15b02019d7654b28a268eae6a8f08c0c7a6b69e1a9823a26b24b40000000838000000000000003a200000384e5105de52d800000000000000000000313e0000000000312a00002e8ee380000000cf800000004d62c7800000002baae88d8aabe2a51800000000002bf1d8203b9aec00000000003116b67000009400285fb80000000000000000009f80000000000000000099533906840e465b500000000000733839a452271a0000f70143badeb5c8000ea280007e600000000000000000000000000000ce00003060e2a8000ca8ab98428000000000005e11644362b30c9e08000000037800000003d90000000000000000000000000785800000035a800038f64bb3808adc8526948ba88bcf1b208f700008970dbc0001b9a6358
  | 60 => 0x8000ccfb48e08fbc0400000002e4800019b0b041ad35d400032ce5efa006000000026024c40002c2627c800000001fe23a000000000000001df40000000efd000026300000002e5800000005eba0da00000000002948b660000e4e329e000000079b34220003d100002c1cc7fb65009900006d80000559ae42345000000000009afaae600034540000714460800037a000000004e000000000002f62000000000000003938000c4890cc7398962597384e7de2a480598000994b7101ab8690cc40000000207a1ec0000000085844a80000e3a6ea0001482000162cdaa2f229080000c4d800000000000000000000000000000000fe8000318800000037ccc9312940001b060000aa88f10000a109f28cb6045400000007fb800009280000001f3c00000000002a9a2fb800093a000000019d000004ce000000000000000002d64c0738f05f328dab5b9d8ae3b80f233d0000f3a8000a4100000003a5000032982fa800000035081cda07c00000000002a0e1ca80009c800002a934c03800000ad480000002ccc0000f620000000c658000000000000000000000000bc613f2ae20000000000078993728908fb000000004392d787e70000edf86e63248034e73000000024480000b0000017fce8795f048300b63d99dd207f3ac246f10da00026c20001924da10000000369a0000000b0a800000000000002678b3b10a400003e86e19ee20000988cce8e8e12f8000000000016d33f00000000db1084242100000002c9200000008e280000000000000000000005e029abb6eaac800000000000000000000000000000000000b28a6980007a800000002a78c5990f4d40b3645d5000000022c02f38b640002de83c580006821e905c78c249d439242a6b21cd2caa44925000000034e2e0099ee44992de3fe0cd805880007148960a4783a4844002a847a77659f000033b08829159490dc618220b60000000000000000008c68000000000000000ca00003965061662f1180007fc8662000150e7e88014b7900000000ff2e918000000000000016d60001cf83ae0000e29a2fa99580000000000000302a0001e0653a2570d33097a39800000000000000000000000005ba354821c80000d519900001cba9f9000000007da00000000000000830a424d9d15b2000000061b0f30000000000000005908000000382a0001014000000000000000003524000000023a8aa2def1f2610f000000000008628c60be200000000000000282a0001ca2db21d389d1a3febfc91ca00000006839d00566b4a68b706b0b5d067e67718e80001ae24d580000003cd6000000095002fe62f00003788000000347c0001f18aaeaaac1603a8211684c0dd71d56da98000000000000034f40000000634841832412e85998000a09000014ba08c9da39fa9020ea8bc580000001e78
  | 61 => 0x281e0a48000f0a00007a929825558000229080a0001e42900abc89b89d6200000009b380000001b6e00013b0bc32c24000000000000000000000000372c8f40d0a00000008ee133c2eb80000000000000000059e9b760000000ba43cf800000002ef15d2e9122865a900000000000eda0cb60000000d9180000000e480000000000000000000000002da4ecf800067f0000f3f80000000732000345084b000018a000010c80001fd15680000000e368630000000000000000000000603217e90700000000000eb92538c4d1c7275a9b4c43229c60000000b2617e4000000000000000000000def9ca6680a9a20eab9ae5d12b7c0003a9a3211c1a691159e79988b4ca302b20000000ec90000000286ee2792400449f62000000098f078219e2eda8d09a7e000014400000000001f0037c9c228e700000000000000000000000000003cbe00000007160000000000000008a82e7b19c000190c773038a0000000a00b4ea3f9b796c9500000000000e5980004a2800037681e0bba00002c580001ef123c00880009b996a841e929ad418634c6fa430a788086e7dae3a3660ca2bb1861ab5303a80000eca0002394a439e8400039f8b5c0e161d98ce8d1fb1d02ee09a4545340c5821f362f0059602f85d8acc0a9017b80008290000000000000000000001b7200038c2952000046a800009a800000012d2000000004b80008ad9adaca817da322994634f1e6a000183e66eb300dae0f5e5dc8000c428e92e210000000000000000002968000000120a00000005a10daa00029800002f42000000000014c2d5b0e5000039900003b26000337ed019142976000009c147c0001968702a840000247e3018000000363aae5a54a77626fa9bb3b660000d6485110c24ce00000000000d4600003e180000000000ee702b6000000000009b4000000000000000000c4a67b000000000001da00001f9800000000000001eae0003cfa6d0a2820000000c571a805dfbb7a0003b3200016049f50000518a63ea2000000001d7cb012eb8b7b2f3a04f1414a890e7608a83e08a804dad6b2c6cd712d6600ba12ae6683fe000193aac688f0691ba2c8d035889692ed6c9b9bcc2aa9150a7dabaa742a850be63724a59b22279baeaedecbd0433a9320eee80007158f80497ab486b497d8d22317a0001edc00025ce00015fe00000000000c8200000b284200001430000337000000033d64041f76eb8035835324a00000000000368000019262b0169603100002398eea00025620000000d0b02eaee6b0486f7800099e800037200000000b7042db1fa000063ad79b59a687000087d93f4b0bbcca0000000dea8000000000075420a00000000000000000000000002196904a05e099b9280080000000151600000006ab94f289901ba261165a49591020000ceee68b544992
  | 62 => 0x7b40002e280000000000088a00039e0c698e3c055ae740000f4499623462cc8000a4506a831691ac0001bb40002598e18893c000000000039d40003882125800003c0000117a22c00032ca0f68000021000000000002f60000000000002480000001942bdd24b63422fc0641b2520002ad600013a4000000000017a4ad081a82ff224c95ba23875180000000000000000085b8f8ec09024000000009cd80000000000a1e0000a66b9dc0000458a9b03183cd2eb6cee1e680013aca0000c1055100008fe800094780003b49ab852f8cc62059656c4b9fdc97a0000737b890a32941aa280916a48a3e80002b4c000000000015d000024c80000000000000003980fc00000000001db600030fa000000098e800000008a00000000c008000000000000000000000000000000090c8dd48b63b54405ac220153b52c523542000000000000002d8b1149fc000080c99fa000029c000176a00025eecdc00001820000afb3c2c0003aa000000000001be6000082ec11000000010043f600000000000e0d3a900000016aed0d5c16a9fc47e59f1e00032a853e1710000000030fb77e57b0b980f4000000000000e400004049f901c03bde54c80003d49cb61a60000a050eb040c1f6c000000041a95ae50e908a64d00009cb8000000000013a80000000c0400000001138000000000000000000dfa846d1133d01de800000380001e48000f458000000000000017960000e061541c6ee8c0000d6d81da5a2800076c21da00015e01d42fca0000000f1c8e3e000268a0001ebebc90000000000000000000000000e8516aa0c4014e64c8000d12a4fc0002702c7612c80002066000246e00032c0757800000000000000000000042687f000000038b400000005d73cdc85e864ad13000057a1f0a3b78000a2aa5cce010b6aab600000000000e898000cb9b5700000f8a4ff33b20000000c2db1a200000006440000bea2fcc000030eb6b0000854a258cdb8000cc39c3abf42672c1c80000001802000298800029d0000000009d88c4000000000011e0d2e30846b7a25a63d380e0000000000000028229b0cb09e6281532887cea368121b25a5af9deae28800078c000097f34a015c88ec30380005e51242000368a0000000000000000000005f8b6ae0002a465e284dcaf52e62ab78000bb22e3c319000006d8000000a41400020cc570800000000007c080000000000000000000006f222a800000029320001dda00014c6000350400025ca6e880000000000b29800016b3038000145000000007670000a5d800000020d0e8ca284259b8380d402c47178650cf7394a9c79096dc19bb6aa1a85c000005a00000000003912e53000054d88ee000000098680000000000a97bcf6f079c4600033ce64700000000000000198c9b2a000cf60000000000046ba3bc35fb84
  | 63 => 0xb200000000000000000000000025ea0000c2245102ae00000000000000000072c0000f4c00000000000000000126c627000000000000000000cbaa1fa2e680000001f8600000001720000000000000000000000000000000000032180002cb01d596fe3838000102ab66000063c0000000000000000000000002f680002a0683500000841c10c7c00006e200000d0000000017481c4000000000000ab000000000006c41922400800090e800000000000002c840000000e83254253b37e294a000000000000000f38e2c800017400000001f346850000000000000000000000000000000038c00004b900000000000cf500000000000000335000000001d2991847320e600030767bda0f8ba98000000000087d03301560000dc0000000000007f691de22ca2880001bb247180000001bf600008d4f06875200000007213872e3b0000c928000474b934ef2a7ea2aca8b64ac9b2e000066600000000002e2ac95800040cae8e68d351042a1e40d8184bc8732704e4c0000000000057232d6c272e4eb37a95c662b8de0000000ebab6f8000327264f800000000000000e7ada600000d3b7220000000000310c0002382eca2f7880d0000d5c9eb6000276e59caac41570000aaaaaecdd1918494d24440000000000180a0001f043c18eb4d54387e235906e21b96324d3341cbeeb2ccce78790e6b381481e00001b3800000038fc7058000c8bb79800000000001660d8480005fc80000001cd000029f00003a3a0003ce00130000000000098e13eeeb4b03a7fc25269a1b5c604d8616c0999fe394b6e83ea84f47b1800000019e4c6ca60a181234a2a082de000275659c0b5c00008aee9a213e1b6031a0000000004000000031ec0001ca40002e46b8d1578a9637423aeafc4340a33e0000000562974e5670000000000063f00002c20000df8321a00027606220af8f283964e82aba8025a8e4b650976190b68e00034ae00000000001f4c60e2c440778000000000075982440000000000000000000000000000000000074926d48a4800000037a0000000012d8000c0394ae0000000000000000000002a3903e00000000002c1649880000002ef6432866820c8d96736985c000000000022eae1b95ce0001d2c0003a74a811b7a00011dacda000001100000000000000025a00000000000000000000000037f2000126a00000000000c2e431800097d9636b400000a6f00000002b687b2000000023be133053e851a350d690000009bc08000156a505936400000000003a36000370c00000001ffa582000000000000001ee00006fa800038e00008f78000a7d2588000232e0002254ad6bca8000000092f000072aafe60652c3a45001320000ef491a81b0dbf8c80568afb6d548a4e47aa762d1e3b7411b00007c212160002e54000026eded00000000000be
  | 64 => 0x800000000000000019be00021a650db1083a223acc3b000000000006aaa8c8000000000000009c300007358000efc26c8000105a00000000002ca80e02734572931aa7a3a5c000191600004c27239c9a0a01fe45b2a2cc1c29a5c3c30a3a00022ca564ba8000000000002e78000372a82d8000000000000032f200000000000000e4b203800000000001a7c8dd86c27b43284cba3330000000078b97f432a0a9400000000002616959000000000000000442575047278a1a8400000000003b40e1100002e8a2a45af00009890ab600006dcb3e9d9e0001d7a77a000016100003642944b5f09cab73800000001340000000ee4973a00000000000000db0b9720002c60613347a00008f2000000000000000000000dae800090f000000039e6a4196acbfeb7f0370992eb3c80000551eba00019e800000000000620ef9289a0002d4000000000003af4000258e325a682000348000037d80140000035ba660001274eadb9e470503a20000000e80af460000fbee5e30fc000000000011ee00000080001ad4000088c0000000ade17ba9c8b3ae7539350d0e8bd0000000000000005c002e47ef274200005ae0002e38000000000032b223d00001af000000027920000000a3c1acc06b800000010540000000000000000000000000000f301e64bf780004f50000a5781b8083800051500000003a34ef40ebc6bfb4020000000a5280000002cb2be6839211f27f4f1a13ea0000000e27000000028103490000e6d80000e8037c309836ca778440527ba56953afb0aae176e8d73d0800003140003c6e0001a5000003080000000cef8000000128c00010c400035f848835000000000000060a0002a1000035e0c2e00000003634c3abac4f00baee4e0a4d20000b1e943000000000000c024cce6e01a4000000000003203d080000000e64ac58000b420000ee200000000fc80880000000129c00005fe00000000000ab428880007cc2f6400028d63f4321400014a01e58000bdc8000a53800081a800000032960000f56000000000000000000000000000000000004bd000000000006d6000000022028ad0000ddb16680d4800048b266c4ad8d7a000287c0003b2c67e2854abe056e7360000ccd00004fd80000001312dbb800002b95cc3021fd0f2ba2a2d17009c88902d28e92830bc7b01023eb8d60ac1e7ab22b9f4095ad424068eec52f169014a30f8bc4b70ea06301e00000000002640903ba7ebb71d7468d9eb42af887c24d018ed60800031300004208ac87f5860c891b2da000219a00038b61230e3ac240000000000000000006b6000000003f0b0fb602db3000050816e400021de0d92728d4aad4842880000000592bbeb58ce3300009ec2510f2900009df2a14b039c06cb13720a0280009ab2dfc000205a0002ce40000000000262c5168ad885a8c
  | 65 => 0x8b408480000000000000161200000008d586c8f3a24aa000000034d00000fa849ed640cda3ef0000e76a60200004fe83f319200000000000b440000000855b85894eacc80001be000000000000000cf2a490d148ef286010664448f5044e9c0e833a27402205be699365a00030620001fb620a000000000006fd31ce00000001638000064000000031aa69e000000000004abb064a1300000000000000000069e800054d1eb293d1d4ac3392f8000196200035a6000000000000006b580008dc35fa00002024939e60eb6800015000000000000bf384ec000316ccc535cc00000000002e647e98000000000000038100000000000000000029b40002ece0a3800000000007a724460001f7e000000096000000003826000000057f013ed36135c215b95c0001722000176c0002de60000ece000000043f053a00038ac000000000000000000a786ab1eaa000269e000348a9af0000daf0000240016c9fb000000000000000000e15b6b40ae08da0000000eba1bc843e34f814800000000000b1d16c8d94bad06f90532023b40ab2880000002cf800000000002fdc314800000000000ae943800000000000000000000000019a434c2832000000000000001490000000000000000000003d02000057cbdb13540002dc800000000003c22000000000000000001fcc0001630c8c000000000007c800000000000863800073280d80002a6a000000000000000002c9a00028ba5703cbc00000007b8067600000b48fc3a120000000000019800000007ee00000001bdcc3914ce0000000bab000000000000000000000000084e1d3a000381ece2170e0003664cf00000693a5f08999742a500000b2b143e3bd97041eb0000000022800000004b6a36e0002204791810c70f80240dab24e000083a0003584119b7a42b28564c5c00002bb030c000000000000000000c86000000000000000000000749ae02000124c9a71cee90f867c0892f606cc80000002e4800000000000000546b57cba8800000000000000fd4000000000032d2000040800000008f210400000000000194402316542ed343c2b79ac8000000000000000002b64dafae4a2679b9000008f666480004a10000a29a4b000017fe00000000003c3a8149d060002ffe00c1ff46aa052224ba838d0b9ea633408fc242350a00006f8000000056180009b00a5400010944e525da24639de000000000002d0afe09920001028de00000db4323849e0406000259e000000078086745bf0000c748000bf48000ac1a0d6277000024c000000000007d6000044f00003702dfa00034bc92c8d2ad4b9bc2d4fb2a40000000d80076abff23f4ee0800003e97b8b9fb0c65549b26a7c902c5719ba800000000001994000000000011e667880000000000ab080003958000000349044b88fe00017aa49e80001
  | 66 => 0x9b580000002104aa8171a000000000000000000000b7d80002b714961e9800008e0000d0f800068980000001580000147ab96a5e451d800089f2cceec72ad2ec600000000a4a0001970dcfa0d25e3b4f000000000001ba00000000000000000000000001ebc000000000000004b500000000d9c000110e2cd857e30080000000000000053c0000000000062a00029e0000000000000004d998cc000000050d045000000006c5b9209c5259000025320000000000000000000002e18000d489daa5b3b00ca8c80000d5954e000000032399b66e0a2342c280007b2b16a9d78720000000091b00004ff80006908000ade930600026f831bafee30b000071100007dc80000000000000127000000002ed9408b6680000c880000000000000000000000007e6af76d688554be28cd64cd0000000000000002c0966800084d00000000bd62d08d60bf892182e3000000000007d296820002302c26bbd284bb576000000031eabd8a7717c8abf913200000001d0b8e400000002318000e58851e6758000eec8000825000025b903abd49e2200025fe2991a76b4cabacf2380000001602000039e000000025f000000021d800000001c309229a499e000000000001c9e565a61000003d6e222c5c0000000000195a0000000000000086a094a0002a5a7a239f2aab80006570000b231956000370400000002f321f8f0c373c29700008ea8000dda0000000000000000000000000000000000000003b88000c5f1e480001430d000e5a4653bb68480de4ca70000605b32a00000000003c7c00019c68278000000105e6e7b4168aa00620002e1a83c17c08bf00002cc1bd4281b0caa899e74000052cc6f16f20570c12cbe0000392bbec00024ec2b680000001da6d7c37a6150819a00000000003120000245a0000000a79992a000148c3de8000a9a30d6e920b82000374c1739cf2e218000a3e8000c8000000000000191bcc654eb65c0000000000000000036c00001d1a7310cfe000000000000007618000117338a00015bc57d9b045ec80007dba98e0001c485533914000266400000000000000000000000000000000000000377423700000001d307a78000000000000000000002b92e2900008e78000000118081c8332000289691e29da0000000c71a0a68521b40a14b2acbfb2ea4380892a40e09ee0001914e26b55ac80b2ba45719886a38778000000000032460ce9b3e0000000626909ab2a80000000124b53a10600017120000000508835a64220b289b97f800013240001cd20da00006a237c20001466486a58a49d879a0b9939600000000000000000000000000000000000267000000026740000abc0d9a93e0002f5c0000000000000021e8db00002b6a2132f320af337200001460000000000000029dbc3800000000002a8e1a2b33617100002f6a
  | 67 => 0x3a9468b10dcc9c0ab898da7645e484462b5a1bc3da9eea8ed3c8ac6a262287c8ed8183831cbfa800000027ae39b82aa0001a065f72afadb71f7424a00001261eda0003b6c809a2b200004d00000000000185a000000000005100000000aa000000000e6c00010b8c77800000008be0000000c17800089fbc1c000000000000000001b7e74a265cc6d8184b848ffe0000bfedf0328a04621ba840848087980002238fc6d1008f812916da00012fcbe897360000000000334c0000000dde0000000000037d8000a18ad0a9b309e0c818a7c4e833ea87380000e633767961d68721b7b6cce29ca35585e63028000b448b96d1180009a8b7140003150000018c38c9ce20000000f15b07e60980000001ac400025e61feb9eaa5082e01e8000019aafb800028eeccbaf9239fb79c57a8000000201687b80000cb80003a500009f88ef00000000e2f8000000151e1a180000000000dfab3ee83280005312020bcd800037e0000000292a4b2800000000000001688000000000018a64678000961bc860000000a38a1260000000000069600000004812e1ca5f33e0e57a9ec124899a0000000f2c80000000000bf20000a0480000000000bf08000000211600000000000000000000091729c2000000062380006bc800000000000000000cbe80004d4b168000000063c3d248b1b9a4d963842b2e30b21b922ecb311e1c00009ea0e71778b890000c51172847f1c1e0c100007a8abb60000000c7880006af82a6d1683bceab94e22d3000051d3cb844e30de0000d0e3fb146c17ca9340002eec02780005c60000000132cb9b800000014f4000000072c8b78d740000894800000000008ec9b7cb348324dd437c6c6d3738bd3800000015e641f95aa000117c70021fe00016e60002d0e1471e340000000243000000000006500c700003b5ee08141caaa0000139206c435273e000000000000005e400008f800006c624ee0000000d7d0000000000000026ae0003a42a398000c4e9bf0bfa000000000000000000710b7286de34f20000000000000000000001ec8000000000000000000000000000000037b14b200016c40000c300002c320000000341bc1004b08e077f800000000000001b1200030aa0000af20002dbeb030000c3f8a52e380ec8d6e0456c9aa0fe4cd8836f0818b40003210cff974a00000000002cf600009b600000000000b90d7b0ec01b8000068300000000db40000000af70d3a0000000adb80000f9875400038bc000000001fa33ccb43516c9e8000a2caa70ef39ba4b23b6fc1c08000aec076000000000001c4cab3a00225c9fb20003bea14580000002d340000c2aa120ff400000000000000ecf000000000004950876b1c81a2e961f50cc811f2e11995000011522e83accc1285dc05f889600000000000000e9f00000003b20c0818f2
  | 68 => 0x9223a9200000003e900000000000612255c0001aa001e00520f500009d33290ef1935e000000000000005048000b0a3546e2bb9a07453322ed234b6c9008a670104d40000000abb9c24930a7ee4091250e5000000003098999b71c000170241382eede3800055c80005cd378aaa124663ca0000cd68000a112e5cc568bb06ec282007b800024c8000526867a000000000000000002e3e0003366c388000000000000000008c98000de20000000000000000000003d1c000000095d000000000003cf000059280000002d06a61087e95135c800000001ea921c19900000002ac800000000000bac0001ffc000218c3f68000e371720d0db9e20500a183f0ad821b51f660c2ba2a796a970dbca3809e2221600024625b480000000a48d6c820a14200007cb000000000000001fd867236d400000000001ee65251d8e000000000000000000000000000000000000000000f2704a643d8000000000000030d40002db800023ea0000000000000015c07d00000ace0001072e55111e828800000003ba0003c6400000008fe0dfe000000078e064ebd0000046a00000000000000000000019740000cc226ab4b4ee62db2000137400000004b00000a55000000030ccc3b80000000cc496c15500002090bcb8d7400000005bb8000000000000030e600000000000000c99000000004ca0000000e5dbbaa0000000000000000000008448000000000066b8000632800000007700002eee585ab5000020c000000004ae00000001fba0003cee00000002438a34034b456000000000018a40ee000000031c2000000000000003a5800000000000000000ecd35289adb58a07013b4c2b000000009949aa80000002cc6000000000000000002f280000000add00007940000dcd26e4000286400012d08ab86fe0be0000000000072a00000a218280001dca6be15a0007291086f8484033000000005b0661111000021d2000000000039f000015e237e8ccc21c0000000000000000000001768433bd0e3f7b9ec7911958856800000036d800016ec2049c8a44c2a2c000145e0b38afa692bc7ad1c357eb5fab2a000378c0000cf200009d8457a9d23b68000000000000037dc000080e0003a06000181c2068000cee9652000142cdb8926474b80006ff89cc8cc00000000000000382c0000000000057843880002ef80000000000e1e8000c9737703d80000dfd0000f3b292411a000080280008650be88e2000010ba2f20000ec400032fc000364c5b60000000000080ba87ea09800000000000000000000033e00000000003bc8c28af6eb2e933a1cf0000c578eac85d98860000000000000000000004590638bb10d2e00000000000000000037400000006eb2d7600000006402e30777b87047d82da8fd8488b21932e0a58fcc1c3a4e2886174c8bc0d1ec20a5d2a34
  | 69 => 0x608a2deeb57800013040ec15743cfb36ad8c07e2aeba11c2710fa000000000000000000320a6dc0000360178c2ba27a670aaaf00002724a26098a000090600000009e8092c65280000000f0a91087f0ac899c000001a6086800082c18e28222d269ae885000034660001b640002db40003484c490000000000058300000000efc0eda256000000010d00000000bca13e0192597b38e6db00001e725540b580004580a8000010d200023ec00021c0503b37c038261eb20934811e23ee036a29a238800000011280000000000350ccdb39be16da0ec20e2260ae4268e00000000820b187d6b9b20000000821aff84b580003b5b864d7ca9b68a782940002ebc0000000882b80c0001a986ff000064b27580000000d8da786c593b4e92b0a2a96985d41848000b409e861522d3e6681ddc68f3ce60001964363a0ba00001280001504ec0144e88e9878000000000000005ad8000d0c240a01600000000000000000072000000000000000399604e80000000ca00000000000000000000004cf8000b7f80000000000000086af461ef4e73800018b949200011ce967000018db892b8b0000000130e00024f606b2b4e5b78df02479a5a98ca85a646923201eab1e35d8000000000086cb54ced40000b412a540000dd658900001e9236c000387885701009f1800000032424422b3c0001698000047eb628e103bfab7e0000000172800000017bc000000000029cc000000011880000001ace618182400009d2bd5022cf378000000365e34c8d720001360000324854a081407c14640000000000000000000000000000000000082398e000000000000000286800085e0000c2f00003160000000242c0000000000000000036940003b1a0000000ce900000000000868138abd7b98e000196c00000000000000e4f8f90000000000000000001c183ba00002c1972c45a00009fe1322000000000000000000000072a6b88f8b8d2000029855b39ba00000000003a4a000000000000000003a985e0a5067ae361c0000000410800093c09da59f8b2435f1e005b40000000338c588b3780000000c468000d0200003f90000000000057e89c890980000003cf41f100000002dd6f20bc765d78fd600006d600014b800010786208174abc961c00000000002276000000063a989200013140002ef4e859b0c921a9263c790e621a0000000317ee3f944040d0000000000088bb0a617d00009a58000b52aeea5be35fe5b18444049800000000000000000ab700000001162250af5693719f614d8f68c1582b400000000002f140000fb40001a5800007ca50f0000d250000ecb8000dd8b46c67d2c66becb96eb8212f60002c08000397e000275c1cd00000000000b46301a0000000000000000000000000000db380000000000000000038700000001b660000000000000
  | 70 => 0xa138000a4ba7be0003c4267309109c60000b120000df2af2a5fe80006f10000000140a3378d500000000cfa16780000544c961880d048b2eb4aa296097880892e0c7297880000001470000000000000002cf800063f8c6a40619729f480000002bc2000000000000007ab0000b6480000000000e93a52e00000000000df400000000000000000000000003b200000000000000e96ae8c000000000000000000000000121e000000000000000000000000238ee760000000179c000322a624000094b3598e9522400001576f19b6c6000399c44830120000000f121a8cc2f868e29004ee379800001806e800013269e722680002a2e00026e8000053400000000000000a4580000001bd28be000000023d400025040000000921180400000000001aa432687d6d6c0000000000000000000000000000019cae380008b8308e000000015480005c32c90d2300007508000000000000000000003362b1f24340000dc4000000062d9f140002a820002df058b891a62f91d80d72e040001b00000000051294282f802340000a5031f00000000000000000000021680003ce24eca9c04c280000003740000161e00006ca5c7000087924700000e2e66a34dee5e9c5a2b8b20ca1ebb2ac8c80008b98000f1100000000000d8435740000000000309400027a2000305a000000000022722bd9bc0eff18962a10000beaa036a1980000001c6c00003c6aa5846e4c7ae2ed0d21425429658b5886da000340e00023c620f22bee650db8167b6326c7806a00022500000b140470000212957e00000007ea80009341f8ee25800000000000000000000115a00001f600000001eb8000000000000000005ac8000709a78ccadb13883b80000aa00007c9054ab5a98740000000e4f2b2600033a00000438ad10000000318cbfc0be40001c2e980049a42f0824de514c8295a1641630000441015093600000000000cb52a98cd2000000000002f1936a37a800000000006a296a200000000000e1e000000000000000000000048000000000000000b54f36bbc2dd28000a2b0000a65ae94bf614d65ad3c960351cb400015125df2f0ef0d8000bafa5943fa32be00000002a3068000039689d123cc32e98ba000277ea6a10aea6826f228f8000b6d8000000107c0001a860000000ca5000000009200ebafe00002c682df0000dd7800000000000000000bc23d2886d3a6edc494cad9a967600000000003cd8f201fa0b081d64754bafcf31000000000000001e2400030c87a000000178000b6580000000000c1b00000000000000000000000000003ab400000007eb800c00000006d48dce448a2e2f1380001f7054e12e22f4b16000000000000001ab200019f20000000628815a000000000000000000000cf98000caa9da403207ea6798344462360e34
  | 71 => 0x843800000033b6000244a000124400014040003c40000321ea05800000000000002de0000000040280008c2230e398a86cd8980000000fca0003b381c1b02227780002a2285e7a28000000253c000058616980000002a200000000d10af700003c125779c380001abcd6700000001fa4000163c141aea80002bde45618c4522800000000000003af800000002d01c881f7b56463d8ca6c023534a8e377200001e800000004b63ac83c82406000000000000000003448ac28000f4511e80000000c5e1ac2000196000024d688aac1000000002390000000000000000000000000000000000000000003b7200000000000000a5f80000000000000000000000000000e12b610000000000000000000001e70e8f940c7d79a70be197808ff0000c0180009d68e860001b9600032fe811b686c66272c000000000000001d8972a00000000d08dae92887ee00019d80000000000000000000000002c8028f2f3e00031120002c64c2b800000018b2e4b80000000db64f336225d80000000000070c800047b002c00000009e00000efb80000002cd60000cf0ea993301902700000098e5c537fa00034d6f400000b1787f800000000000000000000000000000000b480658000000214e0002c40d768000000318e00005fc000000000000008ee906493cb8ba179333229880000000000da422ba42b23ae0002e0600000009c5b556de4bbf6000319e4888000000000000000000001716000000000000000002c5449b800000014060002a9c0003950315aa741c900006f18000f1f92a80001aa60002b8c0001de29ed29c4000110c0000000c98891214c000092fa3c00debd0c4270fa253808b8000305cd528000255800071a92660000000000004ad8f2ddede09eb010a8000ccb310017a8844210300412c1170000006caf3000000011c24790948e238860cfd80000000ac44f015245f489b27302bf200000007740000cf6aa30000000056e0a0489b19b400026a600000000003c8400000000000000dea374e0002436599258cb7128cc0000000c820c782d63960f2d800000000000001d44c65000000017de0000000025000000031862913bc04d3925a43b9dba737000000010ec9fc80006f5860651fa64ed57000070f3a8c000000004a88de00000001a8914e7b90000000000082aacb4000122ae5694dc6ba3d1a00020a8a88a97a40f000000dacee00000000000e04e8034d40000000374a3003b7305013d8000df40000d6f3afa606393af3cb642c7b8000f3514aae6ab160beb05a22a58a5ebf1bbd800000000003cb09e3b644dd680007df00009bc007c0000bba3002d224750000e44204e0000000319901ee9e06becc1878a60d00000ed2ab400000000000000d470b1a00000000002b4acb1a508000000069301d22fc80000000e2a00000
  | 72 => 0xd2a000151cbef00000003d2e6b408c812a00007e01f82ccf000069b16b8957b4be00020040001d100002eb400000008df000000000000001458a3f80004019226b742df8399851a63eabda1fb1a7200000000003b8c0000fdca4a2604e1713bc037ad8c7839fd200009c0671000000000000a6939c000000000029780002f10be721182033a9ed1a80000002ce0000339416714a4f163312000129edfe0000c28000079f89823a88ad400015c4ca986525d6ac3cce000000000000d85343860e91fa1b41d1eae68a2e3e79a18da5800010900007b797f60f3800007e000000031ca0003a40c0580a2c6b800000011f0000000000000009f73790000000007380008a3b8c6dda800000000006350000125248a80700000000000c798000b1b80000003c3e5d43b7020a97a038a01066f3a91c22680000001b92e9eaf040002c345770000af03c1800025f800000007048000b7600000000000000000000000000000000000182c1a234a8a0ba21c0002d142d28000da0800000000003c9800016e800000000007b487f6b2226dc4c306720001ffa000000005e0fb23e6000040a80000000000218800061a00000003a6a0000000000058298980642ceb7daad19258f030e9ab940490c8b30a88b1301863bae4c8c2aef0d262990bb5000000003f402c17f00002964000000022f0000480b4580000000513196a0438000cc900000000c3c4b71c4aee530408a0000000035ea408b95200000000000000000000000009980000000000311e00002be9e60000f018d46e4aaca04c717a8ca480001a1224e575b0969f98000000075c589a23cbd2954633f306ad6b80000003aec03e0946000148807b0000944800000014000000c7600000009c998ae6b80000000000000000004c5b3040000c684bea210540b45e66cb14c000000000002f262b1fea000000000000006ce000061111360000000528800055f0000e69a974bd9abe00003b0a76b8784a0b0000000242800011e25841c400000e8c3beb18a8cda214761000032500000000282cf788d80000000b8d80009b68e1a4ad0f10a46ba520000b4e0001ff60001af0a5a1e920000000e993c5c00008cc35b3b105500000000384c00018ec0001e720533bf81eea4000bb0216a7e00000001b98d7937fedaab3e2000000000001864baa9bed042ce6d59a6fe5498000b9c800000004aa00000000000000cfd077429d2be6937896aa4e8c9c00034a40001c68e01b816000000000032b8acd0000000353c5040cc00000000c61082c000000000032b42879be8abd13be639982acb7b1180001cfcf34162074611fed812856000000000000000003c0000008ce00028ec39c8000000249e0001246cd60ddc0000f240002cf447580000000000c0d800000000000002c420000f960000000000000000013a60
  | 73 => 0x2a40002c38436209a3568000d13865ea7900126e50ba67cba90a867259200009f80001328366b6b6c2c00000002a1cce1058a128000027db16e8ccaf7c00033a200017300000000ed0b1c80000000ac3a98c00002841768000000000000006927190000636000032780000000000be802040000926a998c4eee805026fb00740000000ad78000000000064480000002d1c000000000000004a0800093f9e4c0000000000000000004228aa8000eef080486b2496c2d24da739018027500000e9a0705b8b424d75b0880001026000000000014d04ea80001fa00001d037860000000ee181ccef7331696a1ff800023169de000000000008578000000000000023d200019980001cac00000000000dee9559a96000000000023f2aef00000000ccaf3095a400037540000000ae1000000029ae4db09d000000007e78000000061e0003918000000034b31da0000000000116a0000000b912a4c00031f20000000000059aa80017a27c1c768b43352000000095e211a05b80004afa13600021549b4800000000000000b72c3a1c60534884879d99200a400000000000e470000000000000024ae07e800053aaf00b00b04e0028c4253f1340f33339a85b1788bbf91669ea2e7a1130b7a44580001899a9e0002edeb7ba0961c79fca0000f9a9f3bca6bb989960000000000317600000000b20000000000000000000000682ae700000000dbe270b64a615224895a2398000367ca6e8000e1f00007d58000234800095400000000000000000000034aa0000000000000000009f462a80005a709c63b30000748089496b9da0d1825964deb3868bd99024158c5cc9981302a480007869234f0c8878f2500003261b34000113449fbb140001a008f900006ad96eaeb9ad1addf2f5a3a28a36e51800000020f4000000086a8e54a56227aa218000e9ca2260001508ad83860000000000002f40000000000376600000003de1cb800010a6000000000000003e1000000000000000000a991b28000288c000008290b8000000074eb0d8000984ac702fe9214ae7ad1600006ea80632508a43bd4e2036b000008c00802b400002a1e0003326e08813800000007958794d9b80005f109ce2cb0000e4030d2000000036c800000000000000000b98000000021b882717244ae8000000000000000000000e0a000000000000005ce0000e14a05c96f80000000b2606f8000000000000028760001
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa6c8258d52440ab0f90e31aa488157171cc635491001537410c6a922000a6d8218d52440a14e90cb8aa4880031d1d97154910005aa41ae2a9220c0b67825c5524400517d093b684880021fe1576d091001c3e42aeda1220008bf87593424400153906b26848800aab20964d09100247a432e3a122000c74655c742440093e100b8e848800e1fa1776509100043ec2eeca12200087f855d942440070f90abb284880022fe1176509100046fc1aeca1220008dc835d942440011df04bb2848800a2f21d64509100054e41ac8a122002aac8259142440070fd0bbb664880021f61776cc91003c5f426ed99220008bd84ddb32440011bd07bb6648800e1fa1676cc9100043ec2ced992200087f855db32440070f90abb664881561f21476cc9100043f436eb992205587e87d9732440ab0f90fb2e648815697a0f65cc9100146ec3cc799220008df8758f32440e153908b1e648800ab320963cc91001c3f42eec992200087d85dd932440070fd0b3b264880021f616764c9100043fc2aec992200387c855d9324400117f08bb2648801e2f211764c9100046fc1aec99220008ef825d932440011ef02bb2648800e1f214764c91000c7a408ec992200087e86dd532440010fd0fb2a64880021f21f654c9100052f41eca9922059c7471d9532440011bd0f31a648800a3721d634c9103754e422c69922002acc8258d32440091ed0db8a64880031dd97714c9100063a32ee29922058c7476d9541440b1ae0e1b2a82880038dd946450510006aa298e6a0a2000a768694d41440a98e8ed29a82881535c1c2535051000cda43a86a0a204dbb08050d41440014e90ca9282881431d1d95250510286b8382a4a0a2000ab48650941440093e50fb8282881631d9db65cc5100247b436e998a20049f280dd331440251eb0fb1e628800395d9763cc5100247bc3ac798a2029ae48258f31440014ed0d29e62881531d9da53cc5100072bb1ca798a2000a748654b31440a18ececa966288002b5a1b32cc51014f623166598a2000ad4864cb31440b18e8edb2a42880039918b65485100247a432e890a20049f0805d121440091ed0d39a42880035514c73485102a63a3b4a690a204d8bd87d9340440b50fd0dbaa60880021fa1f654c1102cc3e43eca9822000c3f65dd13044001878cbba260880030fd94744c1100061e328e89822000c9c74d8d3044001938e831a60880127c21d4188110005f1c12831022000c3f65dd12044001878cbba240880030fd9474481100061e328e8902201bcac621d120440c5b60203a240880032b1d362481100247b436e29022000c7465dc520440b38f0edb2a40880039a18b654811010e5c3b6e8902201bcb8761d12044001b60e23a240881131e1da5348110005744328490220009f0875052044001f4284a0a40880073c1db3148110
  | 1 => 0x904bb2868800e1f2147650d100043f436eaa1a200087e87d9543440010f90fb2a868800297a0f6550d100247b436e2a1a20018fa86dc143440010ff0abb0868800e1f2157610d1003c5e422ec21a20008ef825d843440051d904bb086880023761c6310d100247a432e221a2000c74655c4434400f968c8b8886880033518d7110d1000536c16ebb122000a6d821d762440010ff0aba6c48800e1f21574d89100046fc1ae9b1220008dc835d362440070fd0b39ec4880021f61673d89100043fc2ae7b12200387c855cf624400117f08b9ec48801e2f21173d89100043f43ca7b12200087e8714f62440070fd0dbaac4881621f21b75589100043f43ecab12200087e87195624400187ecbba2c4880030f19774589100061fb28e8b122000c3c651d16244001958c43a2c48800317d9773589100062e32ee6b122000c5f651cd62440018b8ca39ac48800333188735891001c3f43eeab12205587e83dd5624400117f08baac48801e2f21175589100046fc1aeab1220008dc835d562440011ef02baac4880021fa1c755891003c5f43ee8b122000c3f75dd16244001878ebba2c4880030fd4b74589100061ea96e8b122000c3f751d16244001878ea3a2c48800e1fa1773589100043ec2ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5e85dcd62440018bb0bb9ac48800317d4b73589100062ea96e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122055c5f851cd62440ab8b90a39ac48800317d4873589100062ea90e6b12200087e8794d62440ab0f90f29ac4880030fdd253589102be1e3a4a6b122000c5f7394d62440ab8b8e729ac4880021fa1c53589102ac3e438a6b122000c3f7414d624410f878e829ac48800317dcc53589102ae2e398a6b122000a6d8214d6244001958e9b92c488003331cf72589100063a3aee2b122000cd473dc562440010fd0d3b2a4880029b60a76549102ac3f41ceca92200087d829d952440018db053b2a4880028fe1176549102951e422eca922000a5f835d952440014b906bb2a4880029be0976549100053bc0aeca92200087e861d952440ab0fd063b2a48800e1fe08765491001c3ec10eca922000c76811d952440018eb023b2a4880031d90476549100063a188eca922000c76211d952440018ea423b2a4880031e88076549100063c900eca922000c76101d952440018e8203b2a4880021fe1d64549100043e43ac8a922000a5f8359152440014b906b22a4880029be09645491001536412c8a92200087e861cd5244001aa86239aa4880021fa1f63549100043ec3ec6a922000c5c73d8d52440010fd0f31aa4880021f61e63549100043fc3ac6a92200087c8758d524400147f08b1aa48814a8f211635491000537c12c6a922002
  | 2 => 0xf52591100062fb9ea4b222000c5c73d4964440018dee5a92c88800b1b1cb525911061e3ab88ca32220008bf87590644400153906b20c888002ab20964191100343ec3ecbb1a2000a5e83d9763440014bd0632ec68830f1d5c465d8d100247ac0eebb1a200087d879d763440070ff0ebaec6880021fe0975d8d102f63ab88a7b1a200387f87d4b63440010fb0fa96c68800297a0f52d8d102ee3ab8ea5b1a2000a9e848cb63440018eceab8ec6880031d5d571d8d100043ec3ceb31a200387f875d663440010ff04bacc68800e1fe1f5298d100043ec3ea531a200087e87d9563440018d8e5b2ac6880021fa1c6558d1000636390cab1a2000c3f65dd16344001878cbba2c6880030fd947458d100061e328e8b1a2000c6f65dc963440018d8cbb92c68800e1fa1f7558d102ac3f41eeab1a205587c83dd563440010fb05baac6880022fe117558d1003c5e422eab1a20008ef825d563440051d904baac6880021fa1c7558d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100064e3a6e6b1a2000c3f7414d634410f878e829ac6881871b1c85358d100147743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000c6f85dc963440018d90bb92c6880031b14f7258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a200087e87d4963440070f90fa92c6880030fdd35258d106161e3a6a4b1a2000c6f72d4963440058d8e5a92c688003391cb7158d102ad2f41eca31a2055a5e8319463440011bf0eb18c688002a72116318d1000566412c631a200087f855d063440070f90aba0c6880021fe157218d1001c3e42ae431a205587e87d4863440ab4bd07a90c688002a7a123218d102ac3f434ed29a205587e839da53440ab0f9073b4a6880021f60a7694d100063b40ced29a2000c75819da53440018ec833b4a6880031d0c67694d100043f430ed29a205587e831da53440ab8bd063b4a6880021f6087694d100043fc3ac929a205587c8759253440014bf06b24a6881569720d6494d1000537c12c929a2045a6c8259253440010fb0fb1ca6880021fe1d6394d100051fc22c729a2057a3c8458e53440014df04b1ca6881169b2096394d100043e432e529a2054a7686dc653441836ad07b8ca68800e1f21676d0d100043fc2aeda1a200387c855db43440010f90cbae86880021fe1f65d0d100043ec3ecba1a20048f4865c743440070fd0bbb486880021f6177690d1001477416ed21a20008ed82dda43440010ff0abb4868800e1f2157690d102ad2f41ecb21a200387e85dd943440010fb0bbb2868800e1fa167650d100043ec2ceca1a200087f855d943440070f90abb286880022fe117650d100046fc1aeca1a20008ef825d943440051d
  | 3 => 0x6b1c205487e8714d63840018beea29ac70815297a1c5358e100062f438a6b1c2000a5d8214d63840010fd0fa92c70800e1f21f5258e100062f39aed29c205e87f8758e53840bd8bce6b1ca7080123761e6390e100043fc2aeca1c200387c855d943840091f100bb28708003171d66350e100246e43ac6a1c2000c5c7558d438400f53908b1a870800e1fa177358a100043ec2ee6b142000a6d8214d62840014df04bb2a508157171ce6354a100043fc3ac6a94200087c8758d52840018b8e6b1aa5080031d5db7154a100245e43ac8a1420048ec87589428400f17d09bb665080022f61376cca100043fc2aed994200387c855db32840091bb0f31e6508157171d663cca100062e3aac7994200087f855d932840070f90abb26508003171d6634ca100246e43ac69942000c5c7558d32840019acc7b8a6508003550c673d95100343ec38c5b2a2000a3e8418b654400147b08316ca8800297a0c62d95100052ec18c5b2a2000c6d7218b654400187ae83a6ca8800297a0c74d95100052ec18e9b2a2059a76811d365440b14eb023a6ca881669da0773d95102c53ac0ee7b2a200087d829cf65440018bc6339eca88157170c673d95100062f184e7b2a2055c5c309cf65440018bae639eca881561f20d72d95100051f420e5b2a2000a3d841cb65440014bd06396ca880029760c72d95102cd3b408e5b2a2058a75811cb65440b14f500396ca881669e60072d95100043f43c85b2a200087d8790b65440014bd07216ca880029760e42d95100043f43885b2a200087d8710b65440010fd0f196ca880021f61e32d95100051f42465b2a2000a3d848cb65440010fd0e196ca880021f61c32d95102cc3f43e41b2a200087d87c8365440010ff0ab9ec88800e1f21573d91100054f41c85b22200087e87d9564440018d8e5b2ac8880021fa1c655911000636390cab222000c5f65dcd64440018b8cbb9ac88800317d9473591100062e328e6b222000c6f65dc964440018d8cbb92c88800e1fa1f75591102ac3f41eeab22200087d82dd564440011bf06baac8880023720d755911000477c12eab2220028ec825d564440010fd0e3aac88800e1fa1773591100043ec2ee6b222000c5f75dcd64440018b8ebb9ac88800317a1773591100062ec2ee6b222000c5f751cd64440018b8ea39ac88800327dd073591102ae2fc28e6b222055c5c851cd644400193c8039ac8880032710073591100043f438a6b22205587c8714d64440018bee629ac888157171cc535911030e36390a6b2220028ee87dc964440018deebb92c8880031b1d7725911000667b9ee4b222000ccc73dc964440018df0bb92c8880031b21772591100063629ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c964440010fd0fa92c88800e1f21
  | 4 => 0x3481914bb04298c690157936085318d2000526c10a631a400087f855c463480070f90ab88c69000297a163118d200062f39ced29a4000a3f845da53480af47908bb4a69015e8fa1b6494d2063e1f39ec929a4000e1e73d92534818d87ee5b24a69031b0f5cb6494d2042d1f430c929a4057c3e8719253480af87b0e324a69021f0f9cc6494d200070f398c929a4057e2e8219253480afc5b04324a6903170fdc86494d2062e1eb90c929a400087d87d8e53481898bce7b1ca6900021fe1d6394d200051fc22c729a4057a3c8458e53480014ef02b1ca6901129d2056394d2003c5e422eda1a4007c3c645d7434800187cebb2686900030f5d764d0d2002476432e5a1a400387e859da43480010fb0b3b4869000e1fa167650d200043ec2ceca1a400087f855d943480070f90abb286900022fe117650d200047bc0aeca1a40018f4815d943480011f700bb2869015f0f1937550d200045f43ec8a1a4000c3f75d914348001878ebb22869001e2f2117610d2002476432e421a40028f8865c043480c7958edb22849001f2b1d864509202a6363b4a6a124007cac7690d424800f958ec21a8490002ea600435092031ed5ba0e0a124000be1811c1424800f17d0939ec2900022f61273d85200043fc2ae7b0a400387c855cf61480014db0429ec2900031d5d751d85200045f43ec8b0a4000c3f75d916148001878ebb22c2900022fa1c64585200061fba8c8b0a4000c3c75191614800193ec9b9ac2900032719373585200064fb20e6b0a4000c9c641cd61480019a8c239ac29018e2fe1176d052000c5e422eda0a4007c3c645d7414800187cebb2682900030f5d764d052003e56322e5a0a4007aac8650b41480070fd0a3b282900021f614765052003c5e420eca0a40018be87d91414800f5590ca1282900032b1d9425052001c3f42ced98a400087d859db314800117f08bb6629001e2f21176cc52003c5f426ec98a40008bd84dd931480070fd0b3b262900021f616764c5200061fbaec898a4000c3c75d91314800187eea32262900030f1d4644c52031cd7c3a85a024004aac8650b4048043958e5b2280900126b21d42501200255643284a024004ba88050940480a9ad041baa609006e2fa1b744c12010c5f430e898240008be87d9130480431790fb2260900030fdd7644c1200061e3aec898240008be87191304800f1790e32260900030fdd4644c1200061e3a8c89824000c5c75d8d30480018b8ea31a609000e1fa1773592100043ec2ee6b242055a5e85d4e63840091bb0e29cc708012b6a005398e102ae2f438a731c2055c5d8714e63840014bb0429cc70815796a005398e102af2cc00a731c205ee571014e63840bdcaa2029cc70800e1fa1f7558e102a62ec1eeab1c200087d82dd563840a90fd0e3aac70801237a1f5358e100062fbaea
  | 5 => 0x86ae60071d91200071ba8ca3b224000a3e858c7644800147b0b18ec8900022fa1c31d91200045ec3863b2240218be87c43644800117b0f886c8900022fe1175591200046fc1aeab2240008dc835d564480011ef02baac8900063d205755912001c3f42ee6b22400087d85dcd64480018bee629ac890157171cc535912003e1e322ea32240008bf87590644800f559053b0c8900030f9da75191200061f3b2ea32240008bd87994644800117f0eb28c890002a7e0d65191200054e41aca3224000ab781594644800156902b28c890002cb60853191200051f428c23224000a3d851846448001c3ea7298c89006eaba08531912000556c10a63224087a3f8714c644810f47b0e298c89032a8fe08531912065f17410a632240caa3d8214c6448001c5b04298c8900028b608531912043f17390a63224087e2d7214c6448001c6ea3288c89018aaea0051191200055cc00a23224000a3e858c4644800147b0b188c89018aaea0231191200055cc046232240078be870c4644800117b0e188c89001e2fa1f10191200045ec3e203224000c3e75d93634800187aebb26c6900030f9d464d8d200061eba8c9b1a4000e1f6414f6348001c38c829ec690002d360853d8d200043ec3cebb1a400387f875d763480018bf06baec6901761fe0975d8d202843ec12ebb1a4000c5d75d4f63480018baea29ec6900029761c53d8d200062ec38a7b1a40c4a5f8214f63481894bb0429ec69000297a1631d8d2003c5f426eb31a40008bd84dd663480031ed03bacc6900023d6077598d202ae1f29ae931a4055c3c535d2634800187ea4ba4c6900030f5497498d200045f43ec8b1a4000c3f75d916348001878ebb22c6900032d1c76458d200045f438c8b1a4000c3f751916348001878ea322c6900032d1c46458d2064e5db80c8b1a4000cb764dc56348001968c9b8ac69000e1fa1f7558d200043fc16eab1a400087d82dd5634800117f08baac69001e2f2117558d200046fc1aeab1a40008f7815d563480031e902baac6900021fa1c7558d200061fbaee8b1a4000c3c75dd1634800187ea5ba2c6900030f54b7458d200061fba8e8b1a4000c3c751d163480018b8ebb9ac6900030fdd05358d2043e1e3a0a6b1a4056c747114d63480031ed0fb8ac6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900031d14f7158d200063ba96e2b1a4000c7552dc563480018eeea38ac6900031d1d47158d200065bba0e2b1a4000cb4741c563480019aee638ac69000339dc87158d200065c3a6e0b1a40008df8758c63480014b90ab18c690002b52056318d200070fb20a631a4000e1c6414c634800169b04298c69015697a175318d200046ec38a631a4000acd8214c63480ab8bd0e298c6901571761c5318d202ad2fc10a631a4055e4e8214c6
  | 6 => 0xbd3a40aeca90605595e87dcd520c0014bb0c39aa41815717a1873548302ae2ec30e6a906055c5f641cd520c0018bac839aa41815717d8873548302aea7310e6a9060cdc5d621cd520c0aba9ac439aa4180031798473548302ae2e308e6a906055d5a801cd520c0abab30039aa4183331798073548302aead300e6a906003a6e87589520c0074d90eb12a41800393dcd62548302ae3639ac4a906000e4c73589520c0a1c9e60b12a418143934c162548300247c402eca1060048bc87591420c0099d0e0b1284181571bdd562cc83002675382c5990600387e87dd5610c0010fb05baac2181621fa1c755843049c3f43ca6b08600087e8714d610c0010fd0fa92c21800e1f21f52584300043f43aa4b08600087c87549610c0091e90ea8ac21801f0f99175d04302acae41aeba086000c3d75593410c0010ff0abb2821800e1f21576504300245e43ac8a086000cd473585410c0010ff0abb2421800e1f21576484300247643ac490860048f487585210c0019a8e6b0a42180031e1d7764c0302ae3d29eec9806055c7853dd9300c0018f6a5bb260180031eddb754c0300065dbb6e89806000cbb761d1300c0018f6eca92601800237e0d75592200046e41aeab24400387e85dcd64880010fb0bb9ac91000317dcc53592202ae2e398a6b24400387e87dd5638800117f08baac71001e2f2117558e202a43f438eab1c4000c3f75dd16388001878ebba2c7100030fd4b7458e200061ea96e8b1c4000c3f751d16388001878ea3a2c7101521fa1c5358e200061fba0a6b1c4087c3c7414d63880bd0ff0eb1ca7100028fe116394e202bd1e422c729c40048dd8798e438800f53908b1c87100021fe157650e2001c3e42aeca1c40668bf845d943880091b90eb1a871001ea72116350e2003c5e422ec21c400387e87dd561880ab0fd07baac3101621fa1c755862001c3f42ee6b0c400087d85dcd61880010fd0f29ac3101561f21e53586200043f438a6b0c405587c8714d61880091e90ea8ac3100062f21176d062000c5ec26eca0c400087f855d941880070f90abb2831000237e0d76506200046e41aeca0c400387e85ddb31880010fb0bbb663100022fe1176cc62003c5e422ed98c400087f855d931880070f90abb263100022fe11764c62003c5e422ec98c4000c3d75d53644800717f0eaa6c8900021fe1573d912001c3e42ae7b22400087f855c764480070f90ab8ec890002a7e0d65d91200054e41acbb224000ab781597644800156902b2ec890002cb60853d91200051f428c3b224000a3d85187644800187aea3aec8900028fa1773d91200051ec2ee7b224000a3f855cf64480014790ab9ec89000387d4e53d912063d1fc10a7b2240c7a3d8214f644800147f0ab8ec8900028f21571d91200051f428e3b224000a3d851c764480c75750038ec89
  | 7 => 0xdc865d3324c0e1938c8ba6649800387d9464cc9300070e328c99926070c9e87193324c0e193b0e326649800387dd464cc9300070e3a8c99926070e8e82193324c0e1d1b04326649800387d4864cc9300070ea90c9992605e87e86dd5324c0c30fd0fb2a64981521f21f654c9300063a38eca9926000c3f75d91324c001878ebb2264980032d1c7644c9300061fba8c89926000c3c75191324c001c38a632264980032d1c4644c93032e5c380c89926054c5c7694d324c001c38c929a64981179318a534c9302a6ac384a69926000ce471d89324c0018eecbb8a64980031d197714c9300065bb26e29926000cb464dc5324c001970c9b826498117171db754c9302a62e3b6ca9926000e4c62d95324c0dd938c9ba2649801237219744c9303764e322e899260049d8805d1324c0dd53d0db22649819b271db644c93032e4e3b0c89926000e1f65191324c001c38ca32264981bb27a1c644c9303764ec38c89926000e1f75191324c001c38ea32264981c327dc8644c9300070fa90c89926000e1d52191324c001d18c9b926498003a3193624c93014e6a3b6e29926000e9464dc5324c1139a8ec38a6498003551d4714c9300074a320e29926000e9864dc1324c001ab6ea3826498003a6190704c93001c3f436eab0a600087e87d95614c0018d8e5b2ac2980021fa1c655853000636390cab0a6000c3f65dd1614c001878cbba2c2980030fd9474585300061e328e8b0a60008be87d91614c00187eebb22c2980030f1d7645853000656396c8b0a60008be87191614c00187eea322c2980030f1d4645853000656390c8b0a6000c6f65dc9614c0018d8cbb92c2980032bd93725853000656326e4b0a600387c859db414c0010ff0abb6829800e1f21576d053000c5e422eda0a600087c865d7414c00f878c8bae82980021fe1f65d05300043ec3ecba0a6000c3e75d93414c00187aebb26829801f2719273d053003e4e322e7a0a6007a9c8650f414c0070fd0bbb282980021f617765053000c5f43ec8a0a6007a9c8650d414c001938eca1a829817a1fa1b754c5302b43f43eca98a605487c87d95314c001ca863b2a62980030fdd7644c5300061e3aec898a6000e9431d91314c00187eea32262980030f1d4644c53001c3f42eec90a600087d85dd9214c00f17d09bb242980022f613764853003e4e324e7a026007c9c645cf404c0010ff0abb2809800e1f21576501300062e32ee6a026000c5c651cd404c00193ec839a80981531e9db65cc1302a72db1ecb9826066cba76d93304c00f974ec326609800b1e9d952cc1300046e41aeab2060048bc87551640c0018b8a6bb686181571714d7610c300047bc0aeab1060018f4815d5620c0051bb07ba2c4180029b60853588300247643aa4b106002a6c82dd9520c0014df04bb2a4180029de0576548301
  | 8 => 0xec324a69815f8760c6494d3043e1f398c929a6000e1e73192534c08b0f90cb94a6980030fd917294d300061e322e529a6045c6c625ca534c0bd0f90cbae869801f0f19175d0d302a43fc3ecba1a600087d87d97434c00187cebb2686980030f5d764d0d300062e29ced21a6057e1c6494e434c0018b8cb3b4869801ea7a1b6490d300064f3b6c921a6000e1f65192434c001c38ca32486981bb271917290d302f43f436eaa1a6057c3c64dd5434c10f0fd0fb2a86981521f21f6550d300061fbaec8a1a6000c3c75d91434c0cd970e1b228698153171da5350d302bf0e324a6a1a6057c5c76dd5434c0afc38c9baa8698153171db6550d300054f436e8a1a6007c9c76dd1434c00f53d0db22869819b271db6450d3003e4e3b0c8a1a6000e1f65191434c001c38ca32286981c3271937250d30336cdba0e0a1a6000c3c75d93624c001878ea326c4980029b60b75d893000536c10ebb12600087f855d3624c0070f90aba6c49800a3720d74d89300043f43ca7b126000a6d8294f624c0010fd0e29ec4980029b60853d89300043fc2ae3b12600387c855c7624c0010fd0fb2ac4980031d1c765589300043f438cab126000c7471195624c00187ecbba2c4980030f19774589300061fb28e8b126000c3c651d1624c00117d0fb22c4980030fdd764589300061e3aec8b126000cb471d91624c00117d0e322c4980030fdd464589300061e3a8c8b126000cb471191624c0018eecbb8ac4980031d19771589300065bb26e2b126000cb464dc5624c0a547d09bb2a4980028f61376549300043f434eca926000a6d829d9524c0018db053b2a4980028fe1176549302951e422eca926000a5f835d9524c0014df04bb2a4980029de0576549301bd3a40aeca92605587c831d9524c0070ff043b2a49800e1f60876549300062f990eca926000c5d321d9524c0018bc603b2a498003170c076549302951f436c8a926000c3e76d91524c001878edb22a4980030fdcb645493000717b96c8a92600087f87591524c0010f90eb22a4980028fa1864549300061f3b0c8a926000c3c76191524c0a5c3b06322a49830b0fdc8645493000717b90c8a92600087e861cd524c00187ec839aa4980030f19073549300062e3b486a926052e1c6490d524c00169b0521aa4981429721943549300062e3b286a926052e1c6450d524c0010ff0abb6849800e1f21576d09300145e422eda126000c5c659cf424c00f938c939e84980031719573d093003e4e322e7a12600387e85dd9424c0010fb0bbb2849800a2fa1f64509300064e3b486a12600087e86dd7324c0ab0fd0fb2e64981561f21f65cc9300061fbaec99926000c3c75d93324c00187eea32664980030f1d464cc9300070e298c99926000e1c6494f324c0018b8cb3b6649800297a1b75cc930005a6c16eb99260708
  | 9 => 0x61d91300061eba8ebb226000a3f855cf644c0014790ab9ec89800387d4e53d91300051ec10a7b226000a3e859cb644c00147b0b396c8980028fa1472d91300051ec28e5b226000a9e831cb644c0cd53b06396c8980028fa0f52d91300045ec3c65b226000a3e858cb644c00147b0b196c8980028fa1432d91300051ec2865b226000a3f855c7644c0014790ab8ec8980038dd4651d91300051f42c63b226000a3d858c7644c00117d0e18ec8980022f61c31d91300051f42e43b226000a3d85c87644c00117d0e10ec8980022f61c21d91300051f42843b226000a3d85087644c00153d0610ec898002a760c21d91303355d40043b226000ab980087644c0cdc74a1a86c8980028fa1720d91300051ec2e41b2260008be87c43644c00117b0f886c89801f0f19175991300061f3aec93226000c3d75d92644c0010fd0fb2ac8980021fa1c65591300043ec16eab2260008bf845d5644c0011bf06baac8980030fdd774591300061e3aee8b22600387e85dcd644c0010fb0bb9ac898003171d773591300043f438a6b226000c5f7314d644c0010fd0fa92c89800e1f21f52591302f62eb98ca32260008bf87590644c00147f0ab20c8980028f21564191300061f3b6ca3226000a3d82d94644c00117b0f328c8980022fe1d65191300061f3b0ca3226000a3d82194644c19dc3c60328c89833b870c065191300070fb2ae63226000e1c655cc644c00147d0c298c8980028fa1662191300051ec2cc43226000a3e85188644c00147b0a310c8980028fa1b52191300051f42cc23226000a3d85984644c001c3ea7298c89821f879cc531913043f0eb98a63226000a3d8214c644c19dc3c60298c89833b870c053191300051f41ea432260c2e1e73d48644c185c3ae7a90c898002a7a0e52191300054ec1ca43226000a9e83148644c00153b06290c8980022f61e32191300051f42c643226000a3d858c8644c00147d0a190c8980028f61432191300071ba8ca23226000a9f83544644c00153906a88c898196aea0051191300055cc00a23226000a3e858c4644c00147b0b188c8980038714e311913032d5d404623226000ab9808c4644c00f17d0e188c8980022f61c31191300070e298623226000a3e85c84644c00147b0b908c898002a7a0f21191300054ec1e4232260078be87084644c00117b0e108c8980028fa1421191300051ec28423226000a9e83084644c00153b06108c898196aea0021191300055cc00423226000a9f83540644c00153906a80c8980028fe1530191300051e42a603226000a3e85c80644c00147b0b900c898002a7a0f20191300054ec1e4032260078be87c40644c00117b0f880c8981571ed827694d302bd1f436c929a6000c3e76d92534c00187ce7b24a698003879cf6494d300043fc3ac929a6000a3e86192534c00187c
  | 10 => 0xb0c6000a7685d0d618c0014eb0ba1ac3180029de1543586300053a42a86b0c6000af38050d618c0095e100a1ac318003a550c43586300053b42ce4b0c6000a75859c9618c0015af06b92c3180029da1472586300053ac28e4b0c6000ab6841c9618c00156b08392c318056b5a0c72586300056ac18e4b0c6004af2801c9618c02b5e300392c3180029da0f52586300053a41aa4b0c6000e6782549618c0014ed0b212c3180029d61642586300056b41c84b0c6000ad583909618c0014ed0a212c3180029d61442586300257940084b0c6000af180109618c0014ef0b992c3180029d21732586300053b42c64b0c6000a75858c9618c00156d09192c318002ad61232586300257940464b0c6000af1808c9618c0531ef0e992c3182263d21d32586300053bc2a64b0c6000a74854c9618c0014ed0a192c3180029d614325863001c3f42aeda0c60018bc845db418c0010ff0cbae83180025720d75d06304fe3b30aeba0c600087f87597418c0010fb0eb2e83180031d9d561d06300063abaac3a0c60018bd84dd9418c0018bccbb9a83180031799473506300066a39ac2a0c600087d86dd5318c0898ecc3baa63181121fa1d654c6302b43e43aca98c6000c7775585318c0018e8eab0a63180033c587704c6300247a40eec90c6000c5e65dcd218c0018bcca39a43180123d21d61486300066a39ac290c6054b598694f308c0abcb30d29e6118153565da53cc2302af2cbb4a79846054f526194f308c0a9ea2c329e61180028fa1262d95300051ec24c5b2a601487d8718b654c0018dae4316ca980028fa1261d95300051ec24c3b2a6000c3d741d3654c0e54bd063a6ca981529760c74d95300053b408e9b2a6000a75811d3654c0ab0f906b96ca9834297a0c72d95302a52ec18e5b2a600087e8790b654c0010fb0f216ca9800297a0e42d95300052ec1c85b2a600087e8710b654c0010fb0e216ca980021f61e32d95300051f42465b2a6000a3d848cb654c0010fd0e196ca980521f61c32d953067d2f41ee3b2a6054a5d83dc7654c0018eae238eca980021f61e31d95300051f42063b2a6000a3d840c7654c0010fd0f90eca980021f61f21d95300043f43843b2a600087d87087654c00147d0810eca980028f61021d95300052f41843b2a6000a5d83087654c0a94f50010eca980029e60021d953033d2f41ee1b2a600087e87c83654c0010fb0f906ca980028fa1310d95300051ec2621b2a6000c3d75d53644c007878eb2a6c89800e2fe1d54d91300051f42c85b226000a3d8590b644c00147d0a216c8980028f61442d91300043fc2ae3b22600387c855c7644c00147b05b2ec8980028f60865d91300051f430a7b226000a3e8598b644c00147b0b316c8980028fa1462d91300051ec28c5b226000a3e86d4b644c00147d0b30ec8980028f616
  | 11 => 0xcc0014df04bb2a59800a9ba0b6454b3000536c16c8a966050a5d8690d52cc00169b0521aa59800a2f21176d0b300045ec3ec9a16600387e85dd942cc0010fb0bbb2859800a2fa1f6450b300064fbb486a166066d987090d42cc0091bb0dba665981c32799174ccb302aeadbace1996606e8dd86dd132cc0dd93cc9ba2659801276201744cb306ae6bbb0e29966000d54751c532cc00317d093b6839800e1fa1776507300043ec2eeca0e60018bc8759141cc0070fd0bbb243980021f61776487303345fc3ac9a066000c9d641cd40cc00187ee93a2cb1800297e0d74596306a52e41ae8b2c6000a3f845cd658c00147908b9acb1834e9ee0173596300052fc1ae4b2c60d2a5c835c9658c0010fd0f212cb180021f61e42596300052f41c84b2c6000a5d83909658c0010fd0e212cb180021f61c42596300043f43c64b2c6000a3e848c9658c00147b09192cb1805e1fa1c32596300043ec3864b2c6000a3e849c5658c00147b0938acb1834697a0e71596300052ec1ce2b2c6000c77719c5658c0010fd0f18acb180028fa1031596300051ec2062b2c600087e87c85658c0010fb0f90acb180021fa1c21596300043ec3842b2c6000a3e84085658c00147b0810acb1800297a0c21596300052ec1842b2c6004a7a80085658c0014f30010acb1800e1fa1771592300043ec2ee2b24604587f865ca538c08b8dcc4b94a7180031d9857294e300043fc32eba1c6000c76615d7438c0010ff0eb2e87181962fe1d64d0e300043ec36eaa1c6000c7661dd5438c0af0fd0eb2a871821e1f21d6550e300070eb2a8621c6050a6d829d5628c0bb4df04baac51800e1fa177458a300043ec2ee8b14600087d8794d628c0014db0529ac5180021f61c5358a3000536c10a6b14600387e85dc5628c0010fb0bb8ac51800e1fe0b7654a3001c3ec16eca946000a6f825d9528c0018bf06bb2a5180031be097654a300062ebb6e6a946000e5661dcd528c0018ecc239aa518003175d87354a300072b308e6a94600095d861cd528c0018bb0c39aa51800317d907354a300062eb20e6a9460ccc5f621cd528c1998bac439aa518003179847354a30006ab308e6a946000c56611cd528c001aaac239aa518003171847354a300245e43ac8a146000c7661dd7328c0010fb0dbaa65180031d987754ca3022c3f43aca994606187c87595328c0018e8e2b2a65180023d61b714ca300063b32ee29946000c7565dc5328c0018eeeba8ac3180123d21d51586300053b42e42b0c6000a7585c85618c0018eeeb3aac3180029da1674586300053ac2ce8b0c6000ad7835d1618c001c6ea92a2c3180029de1573586300053a42ae6b0c6000ab7845cd618c00156908b9ac318002b9e09735863000572412e6b0c6000e575394d618c0014eb0529ac31800395a0c53586300053ac10a6
  | 12 => 0x1f2b1d1624c8403774621ac49908000ce47158932100011eb0db8a64200031d997714c8400063ab2ee29908000cd663dc532100019aac7b8a64200a73998b714c84000672b16e29908000cd963dc132100019d2c5b82642000e1fa1773584400043ec2ee6b0880018bd841cd61100091ed0fa8ac2200031ddd751584400247a43aa2b088000a7685c8561100014eb0b90ac2200031ddd675584400053b42ee6b088000a7585dcd61100014ef0ab9ac2200029d215735844003d5a422e6b088007ab6841cd611003556b0839ac22000395d4e53584402f53b41ca6b088000a758294d6110001cad0629ac2200029d60853584400053b42ce4b088000a75859c9611000f56908b92c2200029da1472584400053ac28e4b088007ab6841c9611003556b08392c220002b5a0c72584400056ac18e4b088004af2801c961100355e300392c2200029da0f52584400053a41aa4b088000e678254961100bb4ed0a292c2200029de1732584400053a42e64b088007ab684cc9611000156b09992c2200029da1632584400053ac2c64b088007ab6848c9611000156b09192c2200023de1d32584400047a43a64b088000a77854c961100014e90a992c2200029da1432584400053ac2864b088000d1c531cd4110001c38a6b1a82200032721d63504400070fc2ac6a088000e1c8558d4110001c3ea4b1a822001fa5dc5635044026f4b882c6a08804de951058d411000147b0d29a82200038758e53504402271b30ca6a08801b8bc875894110037958e4b1282200038bd4962504400de57c3ac4a08801bcac875894110001c5d0ab1282200038b61562504400065639ac4a088000e2e535894110001c58a6b12822001fa9dc5625044026e57b82c4a08804dcad70589411009bd4e20b128220137a944162504400070eb1aa4a088000e2d62549411006fc6cc2a9282200123760d76cc4400246ec3cc79888000c9f7458f311000195ee8b16622001f2b1d162cc44001c3e42eec98880048dc83dd931100010ff0abb2622000e1f215764c4400043ec36ea9888000c6e62dd531100898ecc3baa62200021fa1d654c4400043e43aca9888000c5f7598d31100018b8eb31a62200123721d634c4400062fbaac69888000c5c7558d311000193ee8b1a62200031bdd5624c440006363aac49888000caf74589311000f958e8b1262200031ddd5614c4400063a3aac29888000cb77458531100091d905bb242200123d20776484400247643ac49088000caf74589211000f958e8b1242200123d21d61484400065bba2c29088000a9e8390964cc0070fd0bb8ac9980021f61771593300045fc3ac83266055d4f325ca53cc0018b8ebbb2879800e1fa177158b300043ec2ee2b166052a3e849d952cc00147b093b2a5980029b60a7654b301bd3b40ceca966000a75819d952
  | 13 => 0xf16218a6b108087e2f4114d62100bdc5e8029ac42017b8b50053588400dd5743c86b10801baac8790d6210001c5ceb21ac4200038b5d6435884003f4741c86b108000e2e5390d6210001c58a721ac420002ab606435884033557c0486b108066aad8090d62100cdd1e6121ac42019ba34c243588400053742ee2b108000a6d85dc5621000f55909b8ac42001eaba12715884000556c24e2b108007aac845c562100014dd0a38ac4200029b614715884003d57420e2b10801baad841c5621000159d0638ac420002b360c715884002575400e2b10801bae9801c5621000f55d0928ac420002ab612515884000733a8ca2b108007aae84145621000155b0828ac420012baa00515884000574c00a2b108000a6e858c562100014db0b18ac42001eaba12315884000556c2462b108004aea808c562100015d30118ac42001eaba10315884000556c2062b108002a6c82dd952100018dee5bb2a4201561fa0f765484001c3fc16eca908000c6f82dd952100070fb05bb2a4201431b20b76548402951e422eca908000a6f825d952100018dee4bb2a42014b0f21176548402ac3e41aeca90805d87f825d952100018df04bb2a4200030f5db74548400043ec30e6a908061c6e621cd52100018ecc239aa4201561f21e63548402ae2e39cc6a908055c5f8798d52100ab8b90f31aa42017717dca635484000727b94c6a90800087f8758d52100010f90eb1aa420003171cd63548400062fc3ac6a908000c5c8758d52100bb8bee4b1aa42000393dc963548402970fa0ac6a908000d1c7390d5210001c3ac721aa42006ecba0a435484001d3743ac4a90805dc6e8758952100a18db0eb12a42000e9b21d62548400df17c22c4a90801be2c845895210001c5ee8b12a42014b8b1d162548400063639ac4a908000e2e4358952100a5c5886b12a42014b8bd05625484028717a02c4a908050e2d4058952100ab0f90bbb664200021fe1576cc84001c3e42aed990800087d86dd7321008b8dcc5bae64200031d98775cc8402ac3f43acb990805587c87597321000f87ce8b2e64200030f59574cc8400dcce41ae999080048dd8798f32100ab8beeb31e6420157171d663cc8400064eba4c79908000c5f7558f32100018b8eab1e64200031bdd562cc840006363aac59908007cae7458b321000195ae8b1664201c3a310d62cc84001c3e42eec99080018f481dd932100010ff0abb2642000e1f215764c8400047bc0aec99080018f4815d932100010fb0dbaa64201171b98b754c8400063b30eea990800087e8759532100010f90eb2a64200031d1c5654c8400062fbacc69908000c5c7598d32100019a8e331a64200123721d634c8400062fbaac69908000c5c7558d321000193ee8b1a6420003351c5634c84000637baac49908000c6c75589321000195ee8b126420
  | 14 => 0xd85c85631000f53d0910ac620002a76122158c400046f43842b1880008dd8708563100014bd0a10ac620002976142158c4003d4f42042b188000a9d8408563100095b50010ac620002b66002158c402ac3f41eed2988055c5e83dda53100010fb05bb4a620003179cd7694c402ac3f41aed2988000c5e835da53100a98bb06bb4a6201561f20d7694c402be1e21aed298800087f825da53100af87e82bb4a62015697e1e6394c402ae2fc3cc72988055a5d8798e53100ab8b90f31ca62017a1fe1d6394c402f62f39ac72988057e1c4358e53100014bf0eb1ca62017b17e1d6394c402bf0fa0ac7298800087f865ca53100018bcc6b94a6200031758d7294c4022e37312e52988000c76615ca5310001c38a6b1c862000387e156390c400070e42ac72188000e1f5258e431000147b0d29c86200038758e5390c400064eb1ae3218805087d879d56210185878e93aac4201429b60a755884061716214eab1080078bc845d562100a5878e8baac4201769be09755884029716212eab10800387e85dcd62100010fb0bb9ac42000a2f613735884001c3f428e6b10800087d851cd62100010fb0f29ac4200029b60a53588402bf16214a6b10800087d8714d62100014db0429ac42021f8b10853588400dc5f43c86b10801baae8290d62100091dd0fa92c42001eaba1352588402ee3743ea4b1080c2e2e84d496210001c5b09a92c42006f8bdd352588400df163a6a4b108000a6e83d496210001c5c87a92c42030b8b10f525884061717a0ea4b10805de2f40d4962100bbc5a81a92c4200123b21d525884003d56422a4b10800387e85dc562100010fb0bb8ac42001eaba12215884003d57424eab108000aad849d56210185c5d093aac4200038b612755884000717ba4eab1080c2e2c749d562100014dd073aac42030b8b10e755884061717a0ceab10805de2f409d562100bbc5a813aac420002abe11755884003d56422eab108000c6f875d56210001c5f08baac42014b8b211755884000717ba2eab108052e2c745d562100014d906baac42014b8b10d755884029717a0aeab108050e2f405d562100a1c5a80baac4200029ba17735884000536c2ee6b108007aae84dcd621003755b09b9ac42001eaba1273588403874621ce6b108000a6f855cd62100014d90ab9ac42001eab21173588403774621ae6b108000ae7815cd62100015c902b9ac420012ba201735884000537428e6b108000a6d851cd621000f5590839ac42001eaba13535884000556c26a6b108000e4f5394d62100014df0f29ac4200029b61e53588403f717ba4a6b10805ea6e8394d62100afc588729ac42015f8bd0653588402a717a04a6b108054e2d4094d621000155f08a9ac42001eab211535884000537c38a6b108000a6d8714d6210197c5ee829ac42000393a0c535884043
  | 15 => 0xb29cc62015697e155398c400246ec38a73188055c5e8714e63100ab8bb0e29cc620002976085398c400043fc2ae5318800387c855ca63100011ef02b94c6200063d2057298c402ac3f43ea53188055a5e83d4a63100014bd0b194c620002976163298c4003d4f424653188000a5e850ca63100014bb0a194c6200021fe157198c4001c3e42ae33188000a5e858c663100014bb0b18cc6200029760b7598c400062fbaceb3188055c5e871d663100014bb043acc62001ea7a137298c400052f42ce53188000a5d859ca631000f53d09394c620002a76127298c400052fc2ae53188000a5c855ca63100015af02b94c620002b52057298c400052f428e53188000a5d851ca63100ab4bd0fa94c6201569721f5298c400052f42ce33188000a5d859c663100014bf0ab8cc620002972157198c4003d4f420e33188000a9d841c66310001caea328cc62000297a172198c400052ec2e4331880008de8708663100011bb0e10cc62000297a142198c400052ec28433188007a9e84086631000153b0810cc620012b6a002198c400056cc0043318800387e87dd563100af878e9baac6201531760f7558c400043ec16eab1880078bc845d5631010f878e83aac62001237a1f5358c400062fbaea6b188007a9e84d4d63100078bceb29ac62000f171d65358c400246e43aa6b18805487e8714d63100018beea29ac62015297a1c5358c400062f438a6b188000a5d8214d631010fc3e8229ac6200021fa1f5258c4001c3e43ea4b188000a5e83d4963100014bd0b192c620002976163258c4003d4f42464b188000a5e850c963100014bb0a192c62000297a163158c400052ec2c62b188007a9e848c5631000f53d0818ac62015f871d37558c400052ec16eab188057e1f41dd563100bd4bd0b3aac62000317dd67558c4003d4f424eab188000a9d849d5631000153f08baac62001ea72117558c402a52f438eab188000c5e871d5631010fc38e83aac620002976087558c4043f0fa08eab188070c9c74dc963100014bd0b392c620002976167258c4003d4f424e4b188000a9d849c963100014bf0ab92c620002972157258c4003d4e422e4b188000ad7815c963100015a902b92c620012b62017258c400052f428e4b188000a5d851c9631000f53d09a92c620002a76135258c400052f43ea4b188000a5c87d496310185c3d09a92c620003876135258c406170fa0ea4b188007a9c84dc563100014bd0b38ac620002976167158c4003d4f424e2b188000a9d849c563100095b50138ac620002b66027158c400052fc2ae2b188000a5c855c5631000f53908b8ac62001ea7a107158c400054ec20e2b188007a9e84945631000153b0928ac62000395d465158c4003d4f420a2b188000a9d8414563100095b50028ac620002b66005158c400052f42e42b188000a5
  | 16 => 0x64ca400246e43ac6994800387e87dd561900ab0fd07baac3200021f60b75586402c43f438eab0c800387e85dcd61900010fb0bb9ac3200021fa1e53586402ac3e43ca6b0c800087e8714d61900ab0f90e29ac3200021fa1f525864001c3e43ea4b0c800087e8754961900010f90ea92c3200123d21d515864010c5fc3ac5a0c800093f8754b41900099e0e0b0a83200034714c73506402261fbb4a6a0c8037c3f7654941900070fd0bbb663200021f61776cc6400043fc2aec98c800387c855d931900011df04bb2632000a3b209764c6400043fc2aec90c800387c855d921900011bf06bb243200023720d76486400247a43ac290c8000c5f835d763500010ff04baec6a0003175d753d8d400062eba8a7b1a8000a5d8714f63500018bb0e29ec6a00029760853d8d4001c3fc3ea5b1a800087d87d4b63500014bd0b18ec6a0002a761031d8d400046fc3ac631a8000a5c8558c635000153b08298c6a015717a1c5318d402ae2ec38a631a8055e1e8414c63500abc3b08298c6a0002976085318d406770f200a631a80cee1c4014c63500010ff0ab88c6a000e1f2157118d400052f42c6231a8000a9d840c463500019aae2188c6a0003179ce7694d400062e3aec6a1a8000c5c7518d43500010ff0ab9ec4a000e1f21573d89400145e422e7b128000a6d8214f62500010ff0ab8ec4a000e1f21571d894000536c14eca928000a3f845d952500014bf06bb2a4a00029720d765494000537c12eca928000a77815d9525006f4e902bb2a4a00021fa1f63549400043ec3ec6a928000c5c73d8d52500ab8b8e631aa4a00038714c63d094042e1f3b4a7a128000e1c5318d42500a9878ed29a84a000e1fa1676cc9400043ec2ced992800087f855db32500070f90abb664a0003171d763cc9400146ec38c79928055c5c7518f32500070fd0b3b264a00021f616764c94000c7b40cec99280008f5819d932500051bd0fb1a64a0003171d7634c9400066a38ec69928000c5c7518d32500019a8e231a64a00062fa1273d85400043fc2ae7b0a800387c855cf61500070fd0b3b262a00021f616764c5400062fb9ce6b2880d8a3f845cd651000f47908b9aca200021f60873594402ac3f41ee4b2880d7a3f845c9651000f47908b92ca200021fa1e32594400043ec3c64b288007a3e848c9651000147b09192ca200021fa1c32594400043ec3864b288007a3e849c565101ad47b0938aca200031ddc671594400043f43c62b28800087d878c5651000f47d0818aca200028f61031594400043f43e42b28800087d87c8565100010fd0e10aca200021f61c215944003d1f42042b288000a3d8408565100014bd0610aca200029760c21594400253d40042b288000a798008565100ab0ff0abacc62015697a175398c400062fbaea731880048dd8794e63100078bce
  | 17 => 0x1a420087d879d763484070ff0ebaec69080317e0d75d8d2128c3fc12ebb1a423787d825d763484018baeba9ec690803175d453d8d210052ec38a7b1a4200c5d8714f63485c14bf0429ec690b829760853d8d2101c3f43eeab1a420087f82dd563484010fb05baac69080237e0d7558d210047bc0aeab1a420087e871d563484018b8ebb9ac690b7f1ddc45358d210063bbaee2b1a4200c7475dc563484011bf0eb18c690802972156318d216f56bc0ac631a4200b4d8214c63485bb5ab03398c69095697a175318d210046ec38a631a4200acd8214c63484ab8bd0e298c6909571761c5318d212ad2fc10a631a4255e4e8214c63485b94bb04298c690957936085318d2100526c10a631a42dbe572114c63485b5ca842298c690b6b95c405318d210043fc2ae031a420387c855c0634840117f08b80c69081e2f2117018d210062f39ced29a420087d87d8e53485b38bce7b1ca6908021fe1d6394d214b53bc0ac729a420087f855da43484070f90abb4869081e3761c6390d2101c3f42ceca1a420087d859d943484010ff0abb2869080e1f2157650d210047bc0aeca1a42008fb805d943484091f100bb2869081e37a1f6350d210062e3aec6a1a4207a9e84d8d43484018b8ea31a869080a3d2197110d210043fc2ae7b02420387c855cf60484014db0429ec0908023ee1d60181210043fc2ae331e800387c855c663d00070fd0fbaac7a00021f60b7558f402bc3f438a6b1e800087e87d4963d00070f90fa92c7a021e1fe1d6394f4001c3f42ee6b16800087d85dcd62d00070fd0bb8ac5a00021f6177158b4000537c12eca968055c5c7398d52d00054dd0531aa5a00029b60a6354b400043fc3ac6a96800087c8758d52d00018b8e6b1aa5a01fb0fdda5350b400043fc2aed996800387c855db32d00051b906bb665a000a3760f764cb400043fc2aec996800387c855d932d00011ef02bb265a00063d205764cb400046fc1aeab0e80008dc835d561d00070fd0bb9ac3a00021f61773587400062fb98a6b0e8055c5c7314d61d0005958e4a12c3a00021fe15764c74001c3e42aec98e800387e87dd563900010fb05baac7201521fa1c5358e400043f43ea4b1c800387c87d4963900bd0ff0eb1ca7200038758e5390e400046fc1aeab1480008dc835d562900011ef02baac5200063d2057558a4001c3f42ee6b14800087d85dcd62900018bee629ac520157171cc5358a4000536c10a6b1480218be8710d62900014bf06bb2a5200029720d7654a4000537c12eca948000a77815d9529006f4e902bb2a5200030f5db7454a400043fc3ac6a94800087c8758d5290001a38e721aa520086cba0a4354a400043fc2aed994800387c855db32900091bb0f31e65200866761c43cca400043fc2aec994800387c855d932900011ef02bb265200063d2057
  | 18 => 0xc40147b09196ca988021fa1c32d95311443ec3865b2a6269a5e83dc3654c4894bb07b86ca989129da0670d95310053ac0ce1b2a6200c79701c3654c4010fd0f906ca988021f61f20d95310043f43841b2a620087d87083654c40147d08106ca988028f61020d95310052f41841b2a6200a5d83083654c4894ed02106ca988029d60420d953100637396cb3226200c6e72196644c4018decab94c8988031b195729913100657b22e53226207cac645ca644c4010fd0fb2ac8988021fa1c65591317262fb98cab22620387e87dd5644c4010fb05baac89880237e0d75591310043f438eab226200c5c75dcd644c4010fd0e29ac898b9317dcc53591310043f43ea4b22620387c87d49644c40117f0eb20c8988021fe1d6494d3122c3e432e529a6245c6c625ca534c4ad0f90cbae86989121fe1f65d0d310043ec3ecba1a625687e86dd5434c401aa863baa8698a1e1fa1f6550d312243e43ecaa1a6200e1f6550c434c4014db05baec4988029b60875d89310043fc2ae9b12620387c855d3624c4010fd0f29ec4988029b60a53d89310043f438a7b126200a6d8214f624c4010ff0ab86c49880e1f21570d89310043f43ecab12620087e87195624c5c78bee632ac4988021fa1a765493100536c14eca926200c6d829d9524c4014bf06bb2a4988029be0976549310053bc0aeca92620387f821d9524c4070fb043b2a49880317cc876549310062e990eca926200c5e311d9524c4018b8623b2a4988031d0c476549310043fc3ac8a92620087c87591524c4010fd0c39aa498b8b17d8c73549312aeaa188e6a92620087f855db424c4070f90abb6849880a2f21176d093101c3f42eeca12620087d85dd9424c40517d0fb22849881e3ba1f62509310043f436eb9926200a5e86dd7324c40169b05bae649895a1fa1b754c93130c3f43eca992624487c87d95324c4898e8e3b2a6498913171da534c93122f26314a69926244d547194d324c4018eecbb8a64988031d197714c93114e72316e29926245c5c76dd5324c401aa8e3baa6498913171db654c93100726316ca9926244d5471d95324c4033ad0fb8a64988bf351db714c9312272bb1ecb98a6200a748654b314c5153af0e9966298806b521932cc53114f623126598a62018dd83dd7604c4ad8bae629ec098b87175cc659813101c3f436eab02624487c86dd5604c4010fd0fb2ac0988031b1cb65581310043f438cab026200c6c72195604c40187ecbba2c0988030f19774581310061fb28e8b026200c3c651d1604c4018decbb92c0988031b19772581310047dc3ac0302620087f855cf64484070f90ab9ec89080237e0d75591210046e41aeab2242008fb805d564484091f100baac89080e1fa1773591210043ec2ee6b224200c5f7314d64484ab8b8e629ac8908022fe1d6419121005a6c10a7b
  | 19 => 0x5697a175318d410054ec20a631a8255c5e8714c63504ab8bb0e298c6a095787a105318d412af0ec20a631a8255e1d7414c63504014bb04298c6a0ba795c405318d4128e1eba6a431a820087f855c063504070f90ab80c6a0803179ce7694d412ad1e432e929a8255c3c765d25350401a6ce2ba4a6a09569d2197194d412ae3a3b2e329a8255e1c5318f43505d127b0f29e86a095f4d1077550d410062e3aec6a1a8200c5c7518d4350401878edbaa86a08034d1c77550d4173c9f43ca6a1a8255c3c7694d43504abc38c729a86a081e3d60775d89410043fc2ae7b12820387c855cf62504014db0429ec4a08021fe1570d894101c3e42ae1b128200a6d829d952504014bf06bb2a4a08029720d765494100537c12eca928200c74715d952504014f700bb2a4a09429e20176549410043f43ec6a92820087d87d8d52504018b8e7b1aa4a0957171cc63549411bd1e43286a928200d1c7350d52504a54ed0db8aa4a08031d9db71549410068e29ae7a1282008bd8718f4250401c38a631e84a08038714c63509412261e3b4a6a128245e2c6294d425040555d0db1284a080e1fa1676cc9410043ec2ced992820087f855db32504070f90abb664a08062f21974cc9410062e3aec799282028dd8718f32504ab8b8ea31e64a080e1fa16764c9410043ec2cec99282018bc865d1325049b37100ba264a080a37a1f634c9410062e3aec69928200c5c7518d32504019a8c7b8a64a08062f61375d81410043fc2ae7b02820387c855cf60504ad87ae829ec0a09470f5d352d814126c5ec3e85b02821b8bf8750b6050405958e4a16c0a08023ee1d60181410046f41eebb2662008bf8759064cc4aba9e64b94a7988022fe1d6410f3103e5b322e221e620387e85dc162cc4010fb0bb82c59880297a0e7654b3100536c14eca966200c74719d952cc4014df04bb2a59880a9ba0b6454b3100536c16c8a966200c7576dc552cc40517908bb6859881e3de1971d0b3101c3f428eca16620087d851d942cc40517d0fb22859880aaba0b6450b31226aa38ca69966200d5471dd532cc4ab2b906bacc1988022fe11755833103c5e422eab0662018dc835d560cc40187ee929ac19895f0f1d253583310061fba0a6b066287c3c7414d60cc4ab8b8e629ac1988030fdd352583316161e3a6a4b066200c3f7454960cc4a5878e8a92c1989c3271d332583313764e3a264b0662008fb8758060cc40147d09316ca988028f61262d95311443ec38c5b2a6200c6d7218b654c40187ae83a6ca98b9a97a0c74d95312252ec18e9b2a6244a76811d3654c4014eb023a6ca98b9697a0c72d95312252ec18e5b2a620087e8790b654c4010fb0f216ca9880297a0e42d95310052ec1c85b2a620087e8710b654c4010fb0e216ca989121fa1e32d95310043ec3c65b2a6200a3e848cb654
  | 20 => 0x3f43864b2e820087d870c965d050547f08b82cba081e8f21170597410052fc1ae0b2e8200a5c835c165d053f4ed02382cba08029d60470597410043f43e40b2e820087d87c8165d04010fd0e102cba08021f61c205974103d1f42040b2e8200a3d8408165d04014bd06102cba08029760c20597414fd3b40840b2e8200a758108165d040317d09bacc7a09561fe157598f410043fc2ae531e820387c855ca63d04ab0fd0fa94c7a09470f9d35298f412ad2f41ea531e826e8dd878ca63d040f53d09194c7a08021fe157098f4101c3e42ae131e820387e87dd563d04010fb05baac7a095e1fa1c7558f412bc3f438a6b1e820087e87d4963d04070f90fa92c7a080297a0f5258f4103d4f42464b1e82708de870c963d04ab87d09bb4a7a09561fa0f7694f412ae2f41eed29e820087d82dda53d04ab0fd06bb4a7a09561f20d7694f410043fc12ed29e8257c76415da53d04af8ea82bb4a7a09570fdd97494f4143c3fc3ac729e820087f865ca53d050f27d0f29a87a094a1f61e7558b4129536c14eab1682c2a6f825d562d04070fd0bb9ac5a08021f6177358b4101c3f428e6b16820087d851cd62d04010fb0f29ac5a08021f61c5358b4101c3f42ee0b16820087d85dc162d04ab0fd07bb2a5a080e1fe0b7654b4101c3ec16eca968252c3f42dd952d040187a85bb2a5a094b1d9077654b412963aa0eeca968252c3c40dd952d04014df04bb2a5a09561f20d7654b416143fc12eca968200c6f825d952d04010fb0c39aa5a09561f21e6354b411bd1f424c6a968255c5c7398d52d04054dd0531aa5a08029b60a6354b410043fc3ac6a96820087c8758d52d04018b8e6b1aa5a0803471cd4354b410045f43cc6a16825587c85ddb32d040317d09bb665a08021fe1576ccb4101c3e42aed99682028dc835db32d04010fb0dbae65a09561fa1d65ccb412ac3e43acb9968207c3e7459732d04ab4b906b2e65a08030f59574ccb4103e573a2c5996820387c85dd932d040317d09bb265a080a3760f764cb410043fc2aec996820387c855d932d04010fb0dbaa65a08021fa1d654cb410043e43aca9968200a5c8359532d053f8e8e2b2a65a08066d205744cb41324dc402e89968200c7665dc532d04018eacbb8a65a08062f21175583410046fc1aeab0682008dc835d560d04070fd0bb9ac1a08021f61773583412261e3a4a6b068256c3c7414d60d04018bee629ac1a0957171cc535834128e1e3a6a4b068237c3c7454960d04c91790ea12c1a0992ae20142583410043ec3cebb1a820387f875d763504018bf06baec6a08021fe0975d8d410062ebaea7b1a8200c5d7514f63504014bb0e29ec6a08031761c53d8d410052ec10a7b1a820387f87d4b63504010fb0fa96c6a080237e1d6318d410052e42ac631a82018bd84dd4635040f1eb03ba8c6a09
  | 21 => 0x80590434c88bc9ec7b2e64990031d5d751d853201c7bc3aa3b0a64008bf845c3614c80f17908b86c2990029da1664d85320053ac2cc9b0a6400a7785593614c8014e90ab26c299002bce0164d853200578402c9b0a64f2a768694f614c92de886529ec2993ce9da1853d853214d6b43687b0a6400e956410f614c8018eaea3aec2990a6b560f74d85320053b428e9b0a6400a75851d3614c801c6ea92a6c29900395d4e53d853279d3bc14a7b0a64f3a758294f614c801cad0629ec2993ca9de0853d85327953ac10a7b0a6400a7685d0f614c8014eb0ba1ec2990029de1543d85320053a42a87b0a6400e954310f614c8014ed0bb86c2990029d61770d85320053b42ce1b0a6400a75859c3614c80156f08b86c299002ad21170d853214d6ac18e1b0a64008f687143614c8011eb0e286c2990031d18775585320043f43ecab0a640087e87195614c9c58bee632ac29925b1d9db65185320071b3a6ca30a6400e3574d94614c9dfcaae7b28c2993ba9de0b65185327753ac16ca30a64008f587994614c9b94ed0b328c2990023de1d651853278d6bc1aca30a64eea7686194614c9bf8ecec328c2990038d9d065185320071aba0ca30a6444a7683194614c8ad4e906328c299003959cc65185326df2ab98ca30a64dca7782194614c9b94eb04328c29936f958c865185326df2a190ca30a64008f587990614c8014ed0b320c2990029d61664185327856ac1cc830a6400ae582990614c8011ef0eb20c2990029de1564185320053a42ac830a6400af380590614c8015e100b20c2993729da1a531853277fa2194a630a64eea768614c614c9c7caec6298c299226b5a1b43185320072a32e8630a64edad68610c614c801ca8ca218c2990031d9c765981320063b388cb3026400c77655c6604c8018e8cab8cc0990031d9d761981320063abaec33026400c7675186604c8018eaea30cc09900e1fa1b755813222c3e436eab02640087e87d95604c8018e8e3b2ac0990021fa1c65581326662fb98cab026400c7471195604c80187ecbba2c0990030f19774581320061fb28e8b026400c3c651d1604c85f1e90db8ac0990031dd9771581320063a32ee2b0264008f687d85604c8018eeebb0ac0990031d1d761581320065bba6c2b026400cb474d85604c8011ed0e30ac0990031ddd461581320063a3a8c2b026400cb774185604c801968e830ac0993b335dcc615813230e2eb98ca30264008fb87580604c80157108b00c09901e8fa12735974175d1ec24e6b2e8200c5f739cd65d04ab8bc8639acba0a1f1750c73597410043ec10e6b2e8200c5e311cd65d04ab8b86239acba09561fa0f725974103d1f424e4b2e82eaa3d849c965d04014bd07392cba08029760e72597410043f43c64b2e820087d878c965d040f47d09192cba08028f6123259741004
  | 22 => 0xa18879915787d956410f322acaf41eeab0e640087e87d9561cc8010fd0e32ac39900e1fa1f75587322ac3f41eeab0e640087e871d561cc9270fd0f29ac3991561f21e53587320043f438a6b0e645587c8714d61cc8014db0429ac39901e2fa1370587320045ec26e0b0e6455c3f659d360cc8ab878cb3a6c1991570fd9574d83322ae1e32ae9b0664c4a5e83d9660cc8ab8bce7b2cc1990031d9c765983322ae2f398cb3066400c767119660cc8018eecab8cc1990031d19571983322acaf41eeab06640087e87d9560cc8010fd0e32ac19900e1fa1f75583322ac3f41eeab06641787e8794d60cc8ab0f90f29ac1990021fa1c53583322ac3e438a6b066400a6d8214d60cc8011f70eb00c1990028fa1061d95320051ec20c3b2a64f5a5e83dd3654c88b4bb07ba6ca990030f5d074d95320051f420e3b2a6400a3d841c7654c9294bd0638eca991169760c71d95320063ab88e3b2a644587e878c7654c8010fb0f18eca990028fa1031d95320051ec2063b2a6400a76819c3654c8014eb03386ca991ee97a0c70d953222d2ec18e1b2a6400a3e84c43654c80147b09886ca990021fa1c10d95320043ec3821b2a6461c5d73197644c8051bb07baec899187175cc53d91320043fc2ae3b22640387c855c7644c8018ece3b2cc8993d3175cc65991320063b388cb3226400c77655c6644c8018e8cab8cc8990021fa1f65591320063a38ecab22640087e87195644c8018e8e232ac8990031dd9771591320063a32ee2b226400c7b65dc1644c8018f0cbb82c8990031ed9470591320063c328e0b22640387e87dd5644c8010ff05baac8990021f60b75591320047bc0aeab2264018f4815d5644c8011f700baac8990123e20175591320043f438eab22640087e8714d644c8ad8e8e229ac89917b1e1c0535913200c7b43ee2b226400c7775dc5644c8018e8ebb8ac8990031d14f71591320063ba96e2b226400c7552dc5644c8018eeea38ac8990031d1d471591320063dbaee0b226400c7875dc1644c8019e6e3b82c8990033c1c770591320063c29ee0b226400c7b52dc1644c8018f2a5b82c8990031edd470591320063c3a8e0b226400cbb741c1644c8019e6e2382c8990033c1c470591320045fc3ac83226400ab880590644c8010ff0eb24a6990029de056494d322253a40ac929a6400a7b80592534c8a94f100b24a6991861f21975d0d320063a30aeba1a644587f87d97434c8010fb0fb2e8699117179da53d0d320070fb24a7a1a6445d4e7294f434c8ddb1886b968699117179db65d0d320070fb2ec9a1a6466ab880592434c8c30fd0dbaa86990031d1877550d3243c3f43ecaa1a644587c87d95434c80117f0eb208699196ae2016410d320070eb24a621a6400e1f6550c434c80133f0eb20869900387d956410d32005c7c12c821a6400b98
  | 23 => 0x98f4200526c10a731e840087f855c663d08070f90ab8cc7a100297a163198f4201c3f43eeab1e8457c3c74dd563d08af8bb07baac7a100a2f2117558f422bc3f438eab1e8487c3c741d563d080f1bd0fa9ac7a100317dd75358f4203d4f426a6b1e845787e8714d63d08c3878e829ac7a100317dd45358f422bd2f438a6b1e8400c5e8714d63d090fc38e829ac7a13da97e085358f427b52ec10a6b1e8487e1f4114d63d08014bd0b18ac7a101ea7a123158f4203d4f42062b1e8400c5e735da53d090f0ff0eb1ca7a11168f2116394f4243e2f39ac729e8457e1c4358e53d0801c38a6b1c87a119a2fe197090f4201c3f42ee6b0e840087d85dcd61d08014db0429ac3a10031ddd7515874200c5ec26e0b0e840387e85dcd60d08010fb0bb9ac1a10063da0773583420047ac0ee6b068400a6d8214d60d080517b09baec6a10021f61e75d8d420061eba4ebb1a840387f875d7635080187ae8baec6a130a1fe0975d8d422943ec12ebb1a8461c3d7414f63508011bf0eb18c6a11ba3761f6390d4222e1f3b4a721a8400e1f6394e43508371790cb8486a11c237a1c6350d42014cec3cc621a846eb8d8298c435080133f0eb1886a11c2e3e096310d42014d6412e221a84658bc865c043508010fb0f3aec2a100e1fe1d75d85422ac3e41aebb0a840087f855cf61508070f90ab9ec2a11561fe1e53d85420043ec3ca7b0a845587f8714f61508010fb0e29ec2a10062f21170d85420043fc2ae7b02840387c855cf60508011ef02b9ec0a10063d20573d81420047dc3ac03028463abb8458060508ab4bd0730ecb99383179ce61d97322af2b98cc3b2e6455c3f749d365cc8ab878e8ba6cb9915717dd273d97320062eba4e7b2e64f7c5d729cf65cc8ab8b8e339ecb991571b9cd72d97322af2739ae5b2e6400c5e739c765cc8ab8eee338ecb991571d1c571d97320062f39ce1b2e6400a76819c365cc8014eb03386cb991571e1c170d97320051f42621b2e6400a3d84c4365cc8ab0fd0e086cb990021f61c10d97320043fc2ae3b26640387c855c764cc8ab2b906bacc9990029b60865993320043f43ecab2664f6a5e83d9564cc8ab8b8e7b2ac9990021fa1c65593322ae2e398cab26640387e87dd564cc8018b8e7baac9991561fa0f75593320146e41aeab26640087e871d564cc8018b8e63aac99900f0f1d6545933201c5e43aa8b26640087e8714d64cc8ab0f90e29ac999157171cc53593320045fc3ac8326644387f8759253cc8ab0f90eb24a7991569720d6494f3222e37c32e529e6455c6c865ca53cc88ba9f06b94a7991575320d7294f322ae3731ae529e6455d4e635ca53cc8aba9886b94a7990021f61f65d0f32004aec3ecba1e6400b4d82d9743cc8ab8decab9487990021fa1f6550f327b52f41ecaa1e6455e1e5359043cc8abc3eca
  | 24 => 0xaa45293c845c361548018e8c3ba2c2a90039518773585520062ec36e6b0aa400c5f62dcd6154801a9ec5b9ac2a90031d18473585520072a308e6b0aa455c5f861cd61548018bec439ac2a900353d8873585520062f308e6b0aa400c5c611cd6154801aa8c239ac2a9003151847358552006ab880e6b0aa400c5f7398d61548ab8b8e731ac2a90de9da0663585520062fb98c6b0aa455c5c7318d6154801a9ee7b92c2a9003531cf72585527f73230ee4b0aa437a7686d85615486f8eeedb0ac2a9003551cf61585527eeb3b96c2b0aa45087d87d9360548a587ce9b26c0a91429ea0364d8152184b6c14e7b02a400977815cf605486f2e902b9ec0a91421f61c63d81522ae2f398c7b02a400c5d7318f60548a14f50031ec0a91421f61f61d81521be3b38ec3b02a450a7a80d8760548014b906b0ec0a90df1d1c561d81522ae2f39cc7302a400c5d7398e60548014f30131cc0a90031d5c661981520053cc04c3302a400c777118660549f9ad2e5b04c0a91429e61f60981520063cc3ec1302a4fbc7972d8260548a1cd2e5b04c0a90030fd8b745815200697b16e8b02a4c2c3f621d16054801a5ec43a2c0a914b0f1d364581520063a38ec8b02a452c3c7459160548018e8e2b22c0a91429e20164581520068fba6e6b02a400d1c74dcd60548018bec5b9ac0a900353d8b73581520068fba0e6b02a400d1c741cd60548ab8bf0c39ac0a900317d9073581520062eb20e6b02a400c5f621cd6054801a9ec439ac0a90031798073581520062e300e6b02a400c3f7498d6054801878e931ac0a900317dce63581522ae2e39cc6b02a400c747198d605480187ee831ac0a90030f1d063581520062fb98c6b02a400c747118d6054801a5ee9b92c0a90034b1d37258152006a7b9ee4b02a400d4c73dc9605486f2ed0fb8ac0a90034ddd371581520069a3a6e2b02a400d5773dc56054801aa8e7b8ac0a900359dcb71581520063b31ee2b02a400c7463dc560548018eec5b8ac0a900359d8b71581520063bbb0e2b02a400d37741c56054801a68e838ac0a900355dcc7158152006aa398e2b02a400d67721c560548010fd0fb0ac0a9003171cf61581521be3a38ec2b02a45087c8758560548014b906b0ac0a9003171cd61581521be3a38ac2b02a450c7b76d8160549f5ad6e5b02c0a90031d9c663181522ae2f398c6302a400c767118c60548018ecc6b88c0a90031d18d71181522ee3bb12e2302a400d67625c460548a18eec0b88c0a91431d5817118152286b9102e2302a400d71205c460548010fb0f308c0a90031d5c661181520063ab88c2302a40097b8758060549f36d704b00c0a915697a175398f4203c6ec38a731e8400acd8214e63d08ab8bd0e29cc7a11571761c5398f422ad2fc10a731e8455e4e8214e63d09f14bb0429cc7a11579360853
  | 25 => 0x8018ecc7b8ac6a90031dd8b7158d52006b3b16e2b1aa400c77761c56354801aaee638ac6a900359dc87158d522943ec3ec831aa452c3e74d9063548ab4bd07b20c6a90029760e6418d520053b40cc831aa400a7581990635480187ae8320c6a915697a0c6418d520052ec18c831aa503c5e7698c6354a0569b05318c6a90021fe1d6318d520053bc0ac631aa400a748158c63548012bf0eb18c6a915697e196318d5280da7c12c631aa400b548158c63548ab4bd06308c6a90031d5c46118d520052ec346231aa400b1d840c4635480169b04188c6a9003951843118d520049fc22e031aa45293c845c063548ab87ee93a0c6a91570f1d17418d522ae3bb8ce231aa455c74715c463548ab4bd06208c6a90029760c4118d520052ec3c6231aa400c5d878c463548014bb09188c6a938a97e0a3118d527152ec146231aa455a5e818c463548014bd01188c6a915787a103118d520052ec206231aa455e1d840c4635480143b08188c6a915697e083118d522af274106231aa4dba5d820c463548abc9b04188c6a915795a043118d522af2b3886231aa455e55710c463549b9cae42188c6a9373950843118d520052f4006231aa455c7b709c0635480147f08b80c6a90028f2117018d520051f4262031aa400a3d84c4063548ab4bd07880c6a90029760f1018d520072a18e2031aa45587e8704063548010fb0e080c6a914b1790e76d0d522962ea1ceda1aa40387f829db43548070fb053b686a900317cca76d0d520062e994eda1aa40096f825db43548018df04bb686a90025b60b7690d52004b7c12ed21aa400977815da435486f2e902bb486a914a5761c6390d522ae2ec38c721aa455e1e8418e43548abc3b0831c86a915717dc86390d522af27390c721aa500c5d7218e4354a01c3e8431c86a9403875086390d520062f388c721aa455c5c7118e43548018bce031c86a900a5be1d7290d522af2631ae521aa40396e865ca43548072d90cb9486a900353d8d7290d522ae3631ae521aa400d4c635ca43549ffa9e86b9486a93ff5310d7290d520043fc32e321aa40087c865c643548012db05bb286a90031760f7650d5200636c16eca1aa40087e869d943548012df04bb286a90025de057650d521bcba40aeca1aa40097b805d943548a12f100bb286a900e1fe087650d5201c3ec10eca1aa45295e87d8d43548018beedb1a86a914ac7a136350d520062fbb0c6a1aa400a5e8718d43548018bd0e31a86a915717dd06350d527a62fb90c6a1aa4f4c5d7218d43548018bce231a86a9003171c46350d520062e380c6a1aa455e1c6390d43548012df04bb086a90024fe1d4310d52014b7414e7b0aa43096d829cf615486f4e90331ec2a90de1f61c63d85522ae2f398c7b0aa400c5d7318f615486f4ed0231ec2a9003950c463d85520049fc22e1b0
  | 26 => 0x21fa1f21d95430043ec3e43b2a860087e870876550c010fb0e10ecaa195e8fa1021d95430051ec2043b2a8600a5e830876550c014bb0610ecaa18029ea0021d95430053cc0043b2a8600a76819c36550c014eb03386caa19aa97a0c70d95432bd2ec18e1b2a8600c79701c36550c010fd0f906caa18021f61f20d95430043f43841b2a860087d870836550caf47d08106caa18028f61020d95430052f41841b2a8600a5d830836550c014ed02106caa18029d60420d95432bd1f42621b2a8600a3d84c436550c010fd0e086caa18021f61c10d95432ae1fb24ed29a864587c865ca5350c8b8d8c4b94a6a195f87d8f6590d4300536c16ebb128600a6d821d76250c010fd0f29ec4a18029b60a53d89430043f438a7b128600a6d8214f6250c010ff0ab8ec4a180e1f21571d89430043fc2ae1b12860387c855c36250c010fd0fb2ac4a18031d1c765589430043f438cab128600c74711956250c018eecbb8ac4a18031d19771589430063db2ee0b128600c7865dc16250c018f6ca382c4a18031e19470589430043f43ecab0a860087e871956150c0157308106c0a1802b660c20d814300578c0841b028600c7671d966050c018ece232cc0a18031dd9571981430063a32ae33028604cf0605c66050c019e2e3b04c0a180e1fa1b75581432bc3e436eab02860087e87d956050c010fd0e32ac0a1a1f175cc65181430047dc3ac03028600c3c75dd94310cab87ca7bb286218032794f7650c430064ea9eeca188655c3c53dd94310c0187ea5bb286218030fddb7550c432ad8e41eeaa188687b1e8794d4310caba3d0f29a862195747dda5350c430070fbb4a6a188600c1f7694d4310c0163b0529a86218034794f7250c4301c3f42ee2b10860087d85dc56210cabca86229ac2218031ddd751584432943ec38c3b22a452a3e8418764548018eae230ec8a942b4b5cb64991522951ec3ec9322a400c3d87d9264548a5c3ce7b24c8a914b875cf649915284e1eb96c9322a452e2d72d9264548a5c6ce3b24c8a914b8d5c764991522ae2fc34e7322a452c5f649ce64548a58bac939cc8a930b17d8a7399152006a7b14e7322a4c2c5f625ce6454801a9ec4b9cc8a930b1dd897199152006b3b12e3322a452c3f76d916454a11a5ee9b92c8a90031ddc661591520049fc3ac8322a507b2f8259064548612db05398c8a90da5be0974d8d520052ec3463b1aa400b1d840c7635480169b0418ec6a90030f5d26498d522ad2f41cc931aa400a5d8399263548014ed03324c6a90029d6066498d522961f3a2c931aa400a5f8359263548ab4b906b24c6a941b535cb6398d520052ec3ec731aa400c5d87d8e6354a0b8bae5b1cc6a900393d8d7298d522ad2f41cc331aa400a5d8398663548018eae330cc6a941353dcf7258d521bcbb43ee2b1aa400d6772dc56354
  | 27 => 0x7b12e5b0ca64487c875896194c018dee4b12c3299171b1c962586532253a40ac4b0ca655c6f625cb6094cd38bce6b0ec129b4a97a0f62982530063b38ec5304a64587f8758a6094c8b8dce4b14c1298031b5c962982530063b38ac5304a65ec76635c66094c01aacc6b8cc1298031dd8971982530063ab12e3304a654c77605c66094ca98eac0b8cc1298031d5c661982530053cc04c3304a6d1a5e831866094c018eae230cc1299521f21d64582532be1e3a2c8b04a654a78805916094ca90f90eb12c1298031bdc9625825322e36392c4b04a654a78805896094c010fd0fb0ac129b3e97a0f61582532a43e43ac2b04a644c74715856094ca94f100b0ac1299571bd8972182533de2f39ac4304a655c74615c46094c010fb0f308c129c37179ce61182532ad3dc3ac0304a600c7b875806094cab8f4e6b00c129957969cd60182535f51fc22e6b2e86a4a5e839c965d0c014bb07392cba18021fa1e325974303d1f42464b2e8600a3d848c965d0c870fd0e192cba18021f61c325974303d1f424e2b2e869ba3d849c565d0c018eee338acba180297e0d71597438652e41ae2b2e860087e878c565d0c0f47d0818acba18028f61031597430043f43e42b2e860087d87c8565d0c010fd0e10acba18021f61c215974303d1f42042b2e8600a3d8408565d0c014bd0610acba18029760c21597430053d40042b2e8600a798008565d0c014bf06b82cba19b29720d70597430053b408e0b2e8600a75811c165d0c010fd0f902cba18021f61f20597430043f43840b2e860087d8708165d0c0f47d08102cba18028f61020597430052f41840b2e8600a5d8308165d0c014ed02102cba18029d604205974303d1f42620b2e8600a3d84c4165d0c010fd0e082cba18021f61c105974322c3fc32e529e8645c6e625ca53d0ca54db053aac5a1b0a9be097558b430043ec3ca6b168600a6d8294d62d0c010fb0e29ac5a18029b6085358b4301c3f42ee2b16860087d85dc562d0c070fd0bb82c5a18021f6177058b432bd8ec3ca7a1c8655d1d8794f4390caba3aed29e872195f875da53d0e430047bc0aeab1486018f4815d56290c014db0429ac52180e3b21d5258a4301c3f43eeab0c860087d82dd56190c010fd0e3aac321a4e1fa1e53586430043f438a6b0c860087e87d496190c070f90fa92c3218023ee1d60182431f43ec38c5b2a8600c6d7218b6550c014f50130ecaa18029e60261d95435dd2f41ee9b2a870ba5e83dcb6550caf4bb07b96caa18031b5c872d95430043ec3c85b2a8600a5e8390b6550c014bb07216caa18021f61e32d95432bd1f42465b2a8600a3d848cb6550c010fd0e196caa18fa1f61c32d95432bd1f420e3b2a8600a3d841c76550d2b4bd0638ecaa195e9760c71d95430063ab88e3b2a860087d878c76550caf47d0818ecaa180
  | 28 => 0x40000000010000000000002800000a00000f000c0000070000020000010000805801a000000001006400100000a000a00000c000805a00000180240240010080040008012006801400c014003800000000000502880000280000044006008008001800607000380100000080020000004000000003800c038002004000600e0000000002022013000003000000000340120000008020000000000000000c001000000c0120000048000000001003001001e0050008000004013002800400200300200040000000000008004001007000003e003002000801c00600080a4000000011800400000700100140080000110000000003004000800000a004002003400d000800c002004000800c00600000180140000280020060002001000000000800000100a801400c00d002402c01a0010004002020002000000401900000200180130020018002003002800400800200e8028010023000000801000d00e803c00001f01f000401402d00a8044016020006804405e00600800a800e0060018020002000020000c008000003000400800200180000400070028028002001001800402e014003001400000500b000001000c000802002400c000800002603e00500000000020000014146004001800401600d00c00040000000018024022000000807400600400080000000022ae37b12e5b24a655c74615c76494e1f8bce730ec92995e1fa1e61592532bd1f424c2b24a657a3e841856494d2b4bd0630ac9299568fe1d64192530061fc3ac8324a655c3e735906494cabc3ce6b20c9299578d9c564192532af1ab8ac8324a655c6f625c86494caba6cc8b88c9299574d59171192532ae3b31ae2324a655d56635c46494cab8eec4b88c9299570f19174d8a5385e2f39ac9b14a655c74615c76294e1d8bce730ec5299571e18170d8a532acaf41ee8b14a6f5a5e83d916294c8b0fd0f322c5298030fdd26458a5322d37414c8b14a64587c875916294caf878e8b22c5299169b2096458a530053b408c8b14a600a75811916294c8b0fd0f30ac5299169ba0a6158a530063bb8cc2b14a600a3e841856294c0147b0830ac529a5297a0c6158a537ad2f41ee8b14a645a5d83dd16294c0187ee93a2c5298029b60a7458a5300537c12e8b14a600c3d741d16294c014db0538ac5298031ddc67158a530051f420e2b14a600a3d841c56294d294bd0638ac5299169760c7158a530063ab88e2b14a64587e878c56294c010fb0f18ac5299169ba0a3158a5300536c1462b14a600a3e840c56294c0147b0818ac5298029da067058a530053ac0ce0b14a600a3f845c16294c0147908b82c5299ee97a0c7058a5322d2ec18e0b14a600c79701c16294c0147d09882c5298028f6131058a530043f43820b14a60087d870416294c8b4dd04082c5298029b6081058a532ae3
  | 29 => 0x9003007c002006011000405200200780080140130078008002002000000800000b000000001a0010000000000000000001401400000b004404c0390058028000017002003802e00000a805400000300880e410c00500b803c0000110058004024000000001400001c00000040480020010050062000002801400400000680000000020010038000000000000804600801c805400a0000090008002001005800c01c002012005000a00601f800006200c000805c06e0030018018050008003808800000f000000000800f006000c00c002000001401401100c800400000000e0044000003001800c0000030000004000000000000400600a0008000068005000002c01400100c000800e00404f0008004000000000400e00b0000014000002001800801a002005000c03400300c800c01200000a802c014005004806c00c008002000000201d001800c004037000004802600100180000060050018008000005000801801202a002000c00a000000016800201700480280080040008070000005000000802e00d001003407e00c0150058004001000000c00600200b000000e002000000000002a000002006800000000c40040090108010024008001002002400c0028048012006000801400a00e0020000028003001800801200500c003800a00001d0008016001000003002400300b000000600c001000000a011001801002000f00080740000060000004002004009800000e023000002400000000d8074002009000002c000009001000000400900380b40040030028000002001000001800000a0470080048001002803001a0230028010002010006004002000c0000038002004001806c00e001000800000003e0000000016000000801c00800000c80100060010008000010004008804c028012000000000002a000801000000c0080000000001001807400201c006000001600d00000ec050004000806c02e0020018078016000001000003c003000006400a004000000000201600b805c004018000000403601f001003000400000800240020000018040070000002000801c000000000800a003004002c0a20010120004004014004000400a0050040018000001000000c03c0010010040004003005801c00c003002802000a00c0050000010000003000400200e000005c00000000080000000090038040014003000000001000000000a00000830060010028000000001c00000000a8000036001001800000000700080000140070000044004006000001400600f005002c002001000000000000200000a40000020068014038000001001408200000d000000c00e01800040000000018054004004001000800200c005800c006000009800011802a000002404a001000000000800400000000480180030000000000000000400000b010002
  | 30 => 0x148400044fb2e03440000002f8465ca7b2250b35164c204f525b014cacd61187087149380b8a8d929e51f0d725acb3617068e1bec2367317a29a484420f876623dd98a8c4000000119ebe4162a7fd39c00000000015f000047f8ab988af3800002a80000000002900000000651acc04027e850aa6c141eb007023bd8000ded00024498bea4646915f5e90ecf73a06a5a9af6531b2471e0ec3e6a700284222d90029facfe282c1d2b1707fada538d9cd891ed053aa8fc4eb0ef95853b74682c770dc1175804000228bb340002282549700000000000399cd961000001ee40000003a40000000472524a139cde3d1048b324256f19231221880e6875e3ba9809ac7800032211ea6c06352c15a1a50545c0000628e913138310da067a48805ac51c73d55298cdc9eb377768d884f67c84401a6809668457097f49e41ac35c2baca7ec753d02710656ba320a8bad77c7b1603819515a0e80431a913a43be6fd1a2c00092f6430000e080ef13d0c65508b645ed23cc10e92c0003699a865b6059a34c04600000032315e20020008008000008006c000001008800c01200000000200040380010030032001004008402200f000800c01801700080040000100010000000005011000400c001006002803a00001180000260020068050004006036800002601e00000540220030018004004002004801400c00a009804801400e002000000200000400040000080038034002000028800001e00500280a4000064000011401200000100000040030000178002000006800000c0050060014008011000800000e001000004400c004002805401a02b0048000000003013800414200600a800c00e007001000002e006000801c02600800600500000010008000004026003800000e000004800006200a009808801c00a003000c000000005825c002009000008c00000e002004c00a00000780100040340190000004000011800000600a000001005a000000000400000700000f8020000002000802a005011008802200b003000c05c002007000402400800e8004082003002001001200d00b0000006013003809000200a002009c00a005004000800000e0078030032000000800800200b00c003c0020060008028008001011000002400b0018004004000004800000000700180080000000018004034017000000000000c0018010000005002800400800000080040aa006004800c064002000000000c002004016c00a001000001408e0020028000000001000805c00200c0130004018020005000001a006004000806000000100000140020050000000000019000c0160000000004000009000801c002002012800800200500580000040040030024026017000802400000502a804c01a00500000600000110080014002001000800c026000003000003202
  | 31 => 0xce424170b249a2a8f22841b111b800060f2ab1bbc1f4246862deec1bb7a321287665e4021a1b12f40f71661c3c1785420122e043180a55bd9438e3e000759285c0e665775e01bc9ca4c9244a6ad1b6cbd000118d3bae4c3a0bdb08ec7061f7afd80cee7b760083524a25157d15a96e87085fea6554547701c0800094447503fa97970aa1d50e1b993be88528c99d5b80cc471139e1e566cd2ce0ff118000074a257800016035fb7c8000000795341de127987a1bdd1d90dd844e344800000066b994c25201850111b936474f31d89a4000ec203b2b411ca0004169cec0280000001ea1d0e7c610908542f08162818301e622f429808dd858f0146499fc00064e23d8261496db32a9238084e7f645a80016a8000000000010891154580e00000001f10000d764b800013719fe00012b000071ae2a55d1bd07768a05e003c0a9c63714d3a29d8c8cb6c005643b8d35618a1c4436d53149b358beaf60734853d8ac00034f1c240e88143753b15a56d3f6b6a8c863ee540fb82b955c4f505ba680cd699907ebc4997c8a9555a0c592201e3a5af9dd2605a428af885820ca25806f87361da58717cca2c6a64723c0cde29fd6b795fd2640002d33db412c5c800026b400081b59c0d7890226252881996440003973bbc5a6e5153b3a7400000000006a0bde9fe690ac09d427d85eabcd82120000001399512000000000183ea0a6388048ef69f907f07ecb50000000329152e1cc02bb2c9d885ec4499e40b0c6a328d38e87780e5004aa005804354c61428fda7f479015d5ea6b735e303d08aa4866a52375b2e14903d8b8d2a888a0902db12808722488324f4aad45a98df47c00a36a3050400034937b142ca540000000001a02649000000186800012d1fa519885277da68553c0752c500007248680b900011660003c11ad91820007479b4c00000066fb23511635713f97114780000001e49be89d543b0000000af72f5a9c00000006820000ab245300000002c834f3799025d5e1865c6322ddc80cb6c5a9883cea65619925c00008c0003321a8200048a36405e012a65a861c18211c42f0e514942807250000fa271d4988bd9e16c1b2b09484d205cb000138d458a443400000000a831a1a9b400033f00016500000001f61e89afebf02a40c70f9c4bf1eb9d8887036f0001168ff03d01ff98744187871350778e32597014b2286ea10135ba3b1e300002d19011dbcad739fb918718ceb34baab59e2e131a3088155400049ab105c5800012c2bcc294e336a0301490a8a85b5231543c0bb0001400f0055105a2ead1aca566d70b5524e881516aecc410d9629c082901c507591b2ad5c620f67324d93a2da251c29ac9106942888e198fa1cf729800079e7fd05122a8e3423359aa3e1e669930000a08000eb13e7b1b9aac7bf701916c00002158696f89fc11300
  | 32 => 0x36a95d49a6fa0000001cb2aa0066ba4150212750f9f0ce4861b00038944e63b848b00019420001683390a740515c33d640a6576018a0fca94f6a06187e5c1c9670cba4dc9404264eb99f40003da1d0230c00000041780000007b672585e40005573cc800137663243a800056ac3600023c12d42531a019780a00001eb0001674e980000000cc66423512164c5876d04829ccc682ac5ce3bd5aa04eb693a2611725f75a1a96c0003f23d533640009da6f819a5ab00522cc32940000016c52ae102adab0b687f000000057639e419cd2d0001b71a660006032018000db569f2fc40000006eb02f5d5866a7440665b4e4b26f78228946bd800000000005b83cf000176ed6100000000000000873808000dfb0000000128000000000170800000000000c27af0000001124e345118e0cc001ba5478ddcbaa44649528640000007301941628d994de0629b1cc3a1382a283822a4374282027290368b25c00000006992fb119cc130000415a9e2ad0000001b54f3f4d3273577800023caf717e45d048c2be597e00032aa2dc0000003019e50facbfe24ea2ac5aedd26da02c4ab64e4446b9792a081a3b015504746dd0003dc0000df53639de157e0000002dfd48a1d83f10675ad8e770f280000006e777703cc9909ae782afa914a0002628001afa0000d880000002840003c280006e06790894c82ed441e885086000027c2779462a5d0000001c1e25e3f800000eecd101d174cbd415a09f0b100000003c42020000d2972410a40003373da258c00033001c80000007bd0a005d48b85de5cf35c506e3ae0000001a366070000374ce20004e6000000000000000000000005678000000d0e2b99900a1e0b847680f03ea0002da80000003b523f9bd4590411549ac217fe29f4ae0be46ca44e0c4091cae251238721140009770000000000c6858bba11534cc633738c40000ed3da80010a8c593560000e3cd2821e8039c362326349a81ab8c44513b9c5b0a0005c3b42929622265b3c40bb2a215b583fc2b89a31d3839991ec2400fb8bc9300de12bac44c468af51d3cb48e075a25aa51cd78b122e1ac5989e2811d8abc834abd057a11513847e731c334c460133295a0b936c32221b1de94f472b677b4601d23470003b2c00033201717eccb8dd46381dd80c6b9b4a1a28429087c6b5034db309640ee9dc995a726220806c7da00056eaf353ac000615856d1dccdd1358d68098f39202a480000e050000c00a526180000000e58f0c0001185de8408415bb6487220267f0d814ced100ab8a6468474e1b489e07104e203483080007d06b220e1e0416a7aa8bc4076ba6779b208ffec9e4a910e938200062328d4a129f458db91d204ad83882ed4a8c928111b30d5f8c037a51b9504059325f395d2b613167b309c5cadfe00009b141a0ab0139f916faea758fae644
  | 33 => 0xc64ccf2a239cca6e96e59d9c08a78f6726fb4911ece7c1139a6d8f4c4a633a581da0e525730f18dae1156ef890d12a2b7366376c000ed60062048f168666f23b057b61fe0003724958bc4267a0a1e529bd559036c17edbf5f722f548e0000002ca0000000000171c82e99812012ccca400000000000000005d81cf0000f4d30915f08e8c2d3ce9f1ceacdb907717615aa60c6e1bb7c0000000c80ce4ad8a2554800000005d70002dd415866800015a0eca00034ca81de642a7004182474c7336c336501aa0b0614316c0001ca1a222b10be9a50000000de4000448ad5c0000000003bfd29ccd25dc01082701ed06f906400000068422c000867c1aaab3801e54d63988109faa3d00000000001760002d60000d600a984b40009210000001958cae0003cd40009223978000000006000283800055a27b98f994cdc77af0ba940800012f9e9d1b23f84b2acf00007e147d366c0003f77ab220c0008b64d4000055600010b277000066d18905b01ac6be144936d3d82100d800008d434d00000000000000001a14000dba66092858fe81f0e6a120ecc2ce125a0902ee2343a101292664d73e924697ba8f93e52b800009760002ebc2aa61142585350e675d2ff91e8e44e170000a994c8d0f2709d5c2969b11db99649143df08fb425d600001868f09e1011702e9f3000000041180007080006dc3d40000e14000000000056900026680003710003af81f2e26424b8b5d4611276b88a9300e4200010514e403e4368c74000b4e29701a8000cd03c7080cbc0e230f9a9f9c6e00043fbb38000f426e61454dd8a613e6a7ecf348fd3220bd5952c2e2c915edbf8bf77462290a5e17c4ce1ce0544da46e721f581e88c2150be90f62b41dcb8597cab507b183904f85df27c8d8db821fa649a558bac5c51c89974d14c8744b30d46f42a843a23f88fa4f13952ba5602c5a6bb34313928012129a55dd29844c506dc16a5323c6952dc9213a31d00cc82409708d1b9054649618b87c1e4cd7c53887b94b2de91cf01f46da7d40111b5801aefd11b14d92a2bef435931daba7113fc9b8d0b662b2c080d4b06f620e32d1975a5dd65793b8744b8e75d8495698cf077910ec23261f5090d38af049344daf2152474701a22118fc3e936187487527327708459ba66154b131f0458f1b24c900da9656b527bdc593ad3153c22e8c508bc47505f485abc25ce9e999e6dbe4193151c48c326978b894262de2d7b56442e213390197c3c421928985457a4b83050000083e0005deae90e38000463a65dacc7180003878cd800040280000004456bf28a12aeeb82cf2355724864605a1894fe37208c278051a74d6a1077cf78b9a2031008000b2b00000d9e2aeab075a1a57821bf0000008000e0700000000000000002e4d394a9c0000b9800023f6c99e8c00001960c32057f6c0d1
  | 34 => 0x225c00000024a0d719080000000fd0a3859618310f800003058f00015b29044f89ca40004f35178001586ad624e27f1620e9b3383985d7a7970003aa1cc69785440f64a0c3cd4a2a18533cf245510000f2675e00031bd65294c255891092a00000000009a205b0979fdc30a92e000203c53a39954a9d7c6b284266d12b407e0ba0002a14c725840000da98a43610390001bca0000002ba11286b5543b55506c8c619383d8bfc12c3bf21000000001ee185c7a60004ea215804cf410f8b0a567a03214b8604b7e1bd0a706440000000591c585709246ee23c5884a6e7082700b4eb264731f81d66eb4314a2401104ff28c2e40b8c0005e8b845944ab56040824fd8d0b5b884b8000b0f3801c14022ce706e0f1d99aafe787b531c801cb501bd49ce05ed3eb980488624d48d80013a61a40b1a98c00004900000018d64697af8facc5e0470ba2d341ea64b5b4b63c67cec768eb0544340076afade45dc39c1bda5fc21000b6218ea90ee268086a851bd61bc02401f828c7b25c006cca18bcf791134d8386aa06c8a7942260d6d4bd991342dc4ca26d4d101062f80d98d5c5ba64b2824bf8d340000001e2895326f0bdc0003f511c38f589abf50000001b40e6b4e82135dee0001f9887d6bee0119087506d64a41b70441ac6f371cd313000026e625800000000036d800000037e14e0000e8c18036ca09400000061f8000a20000585ad956da00054610614d235b19216756262be1d18001eee00039a2d550c00da00000003cc000494bd687c88e2000000000029b1c03400000000000031dabc1c723b92dc00090006324e4a4ac655411da4fb68d8630abd8a46000187a520f380002d90000e2e934726ad89bb211e0002998ed6b335d49d240007a915d04fcdb0f7209d98593360005c7b6b0fba86f70634f04de2dd7490511278cbb78f912c9205661942eb0782dee40bacd1d2a3bf53e37e47945704281c298b05345861e6db6489d33a39d84fcb2f041b1382be2aa1612aa12fa00078b18c5c76d2a3c18e142500000002609c40f4f529243cd740d12ae1a445a87c1196ab488e64ef0002eb9b3a7d318380000000006c40000878d670000dc12b0000000065921aaaf78ba831812e5011ca798662e1c76d3c359bcb6770584740004d52afb44537e39542aa7cc9542b15b7af0c31cd9169db90411242c4e58000000aef274b67931220548f2b1c000c9b79794b12e698d0002f29cda6ce3dd1c2c00097241a1ae59f89816771a243380133232b20c8e9b37939a090660000002e8400022f00027d97f40c56281d4c9ce000362a8d1baedc200036dc00000051f090848cee34e3841c000000000023800000005c8000000de60003bb00000000000da15dc00000000002280000001211c142884e18000000cdc000395502236455e07f460a06868d28cd
  | 35 => 0x4bf04204f28001e9669d6089fd5b5af75644b87cbe24b433105592020f1000237958c3250fc39d434e7be401b24172c0f26832af80bed791c7211044c5ee6750000f8aa5c5e98000ddef515f4b0e000034c50039a0d901b976e035c4fad8c40980000001c8000166942c2951aeb040cc8f6441d8001adc8ca78d38543560005d91e046a600044794793ce2f804d3bc14409f20a91b7cee6e8d453b9e9dd0143309a7a53b26a72d6b8206023e667c8a40a3a4d656121940000005f3000163a58c3f32e7c5f806e25e25f8bc4de3596b40c16c707340a6a9a74000000103dbd00001b62e8985e0005508aec9a8cfb5ca2d08d06e3f000000000010442c0754a8a00063a0000000af05d8b74015e15464a2dc1d2e6f911eba78788bf44be1a3c52469f27b16ed68aced2002d04000000000070059ec720001da8c32c493beb4e1eb6e8550d24ede00f3b5af13185faab048580016c09a40001b1907249f0e20000000587536132d8cc3905ae25187c298756496917684342742c253163d23a2371593e6ee68a01596088a628104c85e6a10493351dbc2d7a00000000005b001b9ca08e2df1000223800042f000000077ac7b12e043c0004da67d000105490537eb4dcf84085386800063c3e56d7b60cc6000000033812840000000f8c0000001a400000003ac0001dc5d0cab90002f7c00000000008b5e7a49e1b99088ccc02c0f909c54d400000005a4998ee046f92300000001793594ca200000004446a000015f800094a62d0000274000d132f335e1bc400079713e9776d2034b039c00045072b0fe938cc1910c05884623fe15e193156684f046ab293f4c6430e33b1d16b8872295c8b5293e4380941de2a9461816450869883f93bf14be45800028dc31e00073f361d562ade57ab03957a8040a13635ae01d162e93283a6eb63e484d04e47f327a15ddc72e9c3ed1dbcb588cd0ed980936eeb76428000adc2ca2ed90c800000065515f9358f54067b3dc6a8a2b000106ded2bd702c978c1c025400038d899a38718d91bd21428c2c011f16ba38f0491acc5acbbf6e20b6c1429c83f53c101902df31219e40001e918483f0a8e7fa431b68cc1ef212c2b011aa45642e4b51595033c00023ac67684132c2cb8000b767333a054d0e2e6e31ee04b276831ea2fd69e23e4ad181878a122181a511b7a4f00ff8f6c1161ea45a28c0b446983b60389d5244c13b38344ba28a54ea7b950c4dd75f85789a40005f032cc00039d18c1810b3e6456dda3bc0f02c600026e91e855022100a947200060b33296888bb235ae098ae1e00818001ee6eae1c5a47cb0400074caa38f4268c40e8000ce600000000000005f97b411101263b465e14a1ba22a5413005d932cc00d6b6702e6468148a889a46a4c52c19e10f0b1c02e0f0c50c2fb59287d990633a5c4800167c41c
  | 36 => 0xe00023ec97acb14f419c98ecdca0cd093049c0990d50a2ce46f3c33f3308616d824dc05a088e78f0b7881cc0ab8d2493c8c8d8567270278c0e26212ba2524dc2e216500001d486a82ac38a4478aa41bf9d9c6a26863862c1c5fce1d36d2ee40000006e78001ab474c00001b4726ed35d500003c80003710000c4af401319404c907454fc2040b68ba5744a418000ddd6b43394000be32f0998400000002a0000000000000146c0006a500000001c6d4953a2208fbe6ad00000015ce0000001bf80000001fb1035bc0c121eeac5547e8e34f7b8d545c6ab0000fedcfeb481591dd0000beb735000031a0000000000a6656f00037a8e2a0003eaa4c00003e744400000000000001cd56f80000001b4841c000208059809e8be52701b0e72ed825786d00000000d00000be863c0c1922ccf61d01821d45814d51258800d3d6e7d31000589f600011711487d08d00cfb55d9c200061b8000000dff3ae00000009a700e325cbb8f576961cf8e9419874d000000000075c8000f22d895b43479a32000321ab00dfe0cc0002d2c386bc5000335535e0002620000a8690943385ec000000367864ce80b400000b0d4fae5d7503c7034c000576a46588e5650c49bb48922552c69db8ff67146369df06f280c0003255cbe7b7640372d662f5d2750000c34d6b2a99eccb9cc22667347cf48f1155a15b56c2ce314b2bf56a4a1b5db1751d8640e11200001d48072533910b20c3d0d0ae5cb12bf95d4332cea483c0a625d00409710858a1c328a5350298fc8146670ae89818181b6486282d9b0e061d0bdad324c986fc18510ae1e83112e8159645f0f5af30b66b9502f2fb5ce4f5865a08ecbce9901292d1d4b42e93300000364aa315839698bc75046b9d84f0c6a168baaa4bca67759b1cdd6c61956f39b780000001fc800053002f32b263c000c7900000007800006ada5847509db0eb9ac52bee6210e0abc0000005ef2078000a3b636000084600025c8000000c390000000a1a52210e80008169a243d2a5977496947e14119e85bd000208994e0444448c800003260001558658f3e380800000043f0200ba137c80a035b388f7646641f2b7db7820b6e6b144e861583f2a28c99ced23e5a071588a6f6ca8bfc00027475d0e0875e0004e78428c3c9d81840b4800077762980541046083473a38856e430233ad5af62cb4cfb4f4ac6045194930d000d846ba1ce80c4d9225737d805aacc127a3094827850f6173cf3e8e809e3d71e3a00012d8155ac4200697150450665a375a45533ad363d5b31c0f20d0000000026e46d3749cc15764334c1bca1730b56751227890091701e8f208ce7646d8318d6b4b324841194ac07955c597498c00003613b890d464d5bb834843ccb0405bd84b989e458cb0a8d92c0100038004520005b718989a05316200b803c209c22bad4
  | 37 => 0x28000bfc19e80000000002de061083c41d1508d14c94f3a1e5b068d682da34e1178000a9f44c800140cd7508100002ceaff0000000000000718073800062a76a8f55b507de2d29a3525a55e32780018aace900026e46acdb600007bc8fc00000020a46ec00075284993e0991546b8f1bfae4e130abed722edb05224ad4aaa241cc121c5662c74e2b768000a915d380000008192f90c8d9743ad000389d6b60007730514ef296d1873bac0000003d83be80005d10001525ae6b2125d80009f83160000fa96cc0003782c0dd5a16e26113611446106cf8000b1e0002e512d8ea8a751d586797b23b20000f78000000210bd1d29aa437980000000d25593800120ed5413b800086ecb90001d8c3c61210000e5de580002d0875954c0000000b9c000e58000000158a15000030949800000003c39b345cd489b408000f252268c686947ef06c336d5a6db1553905893693f3e00c55e0c0a71af84d979ce1a1f827b428eb59020ad2848a9792063d31c2435877f24e949093d08608d59d040156d9c4826a0000002b7000048e4260cd108cb2a43f10b8bec1653f701911906a976497a479c4ec6eaa0d438ae9f79a0b600002ef1cb2599934e8078980006e800060bbaa800000000000018760003173b28af407a704a3500005c200032700004a73ac8000ff85ab24d0000000000120b8644eacf800006bd6e400000034c0b820ad14a0000da8d3967aa06121c6bd2cc8f50c1c5ae737162013617e6f9835004a6b22b11574fb285c0000764000eea0001ac00007ad00002a0000f4400000002c20000000000aaa1a34138001e92b200000000a6a00025438a000000052a149000000000000000002850000001a440004748bb55ca9854aaa7892949a9443a5ed6f40005e49bf1800a984108ed8000ab60002ba80000005c50cd56fc1b50761655cd800073214815c44c11720fb8efe313214278523a66533b3121ae47e300d25bce4a8790001ff88c800053000000009410000490c14dec0001dd5aee0002419e240000002413330a8053b54d800000000000000acd26413115b0f0e4ee182bca6d09da5fa1a935a55c82ec38980014524ba401000057ae5b10318d400000056d05e800041a0002c6800098659f8000bb4b491850000862338164823c1c200000027d532c32f32a0b440000000000f30c16f6e71c048c4ca00000000000f8d2604aab052ea78c0003994b626c1429949931cdf703800010b45e81cf83e90ba3023c2000013e0000001bdca287c40001b299a82664ac95302606f8199ac60f5824800038f8da27211500180102dc83d711017f0e821a5afa15a253936a8000000000772a9400b0cb7768913c6f8c6213c8724eb665b4572cb13ee0002c730750dc0003ee04f59fa3d81b380a17a8703147b6846540001dd066c622a014689680b54f4
  | 38 => 0x1c5600046d2adc1f652d357bb9c9b219200020c017cb3922c80000008e74b40000000d485bc2f59d0695d1e4a86107480951302797e600053bb051e3c1823cb16e5d2c0a923c01395322646a20ae400051700029e591cd812a7a2c4a7c01000e8aa4492527470962c000c210402f2c66c66f59205fc6f0f6f491bbe0e5a80d00016dc0003b00000e246202b6224115984ce5c583000074853d3c50c3108e00023009
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x3a5a421c7200189eb45e907044c2be30006c1a467c26c45000880800001628ae00000038b864781494000052000686bc002a408a8c008236560eac48a8aa002e762c7e7496b024a60ca210340a92604a6e689cc8206202b64c6a4e800028000011000010180af80040408b0010700242d30a0800b0e000448402b40103f985d07458a530041de61711c56294c01856839c762982532ae131cd8214d6290cab41e93d4b7650c432ae0720f76dd54310c0150d9294f7250c432ae07a0d749926354801a15841843118d5200691608610c46354801615940c71018d5200515a467018e435480145a909c46350d52005856503118f615480145697187735855200515a5c611cd6154801455901847358552005152457318f60548018547120d61d815200515a4f711866054801870801c5645815200516241641cd6054801455911807358152006151c48358560548ab05c981cd6158152006159ce819c365cc801856839c7659833200507e5d6494c434c80181f87d956410d322ac1b25d8298d52d04018547120d654cb410061520c715d95250401870801c576549412ae072187350d5250401075989db71549410060761c5318f425040160d9214c63d094100615a0c719d952cc401077985db7154b3100515245321d9524c40144d920c476549312ae139d98214f63485b7a47616085318d2100691e458214c6348401a44916085318d2100691c418214c63484ab84c736085358a40005836485318f425000182c4261c53588402948b663749d5621000160e93dd275588406148ba63745d5621000160e93dd175588400060ba1d7590d621000160c935d64358840005076587390d521003722e9890d6254840007031ce43589521003748c935d162cc84000507658531cd411000181c872156350440007031cc53589411000145691d907354a3000507652611cd528c001c16949847354a3000705652611cd528c0018568398775cca3000615984835d7418c00181d8714c311913000513648301d9524c1ffa0c6460a43549300058364b75193324c00160d921d464cc9300070514c71191324c001c1475190714c9302ad16a4f52dd9300c19782e7660853d91200048be5d8214c644800122d9760853191202ae139d98214f6348001a0c6460853d8d2000683d918214c6348001a0c646085318d202ac1724d851d94148001077985db7154a1000545650319cf6544001456918c273d951000523648401cd644400143594a067694d100050d650319da534400182c7460853589102ae131cd8214d6244001435940c476549100041d660101d95244001515940c473549102ac1b25d8218d52440018547620d7154910006151c683d95324400187070219525051000551648531cd2144001531951c474481100066821d4250520440016a0965094148110
  | 1 => 0x1200ca840054b266008e1ea42200a0cc985c04003e32ba3c7a00c09a0058c6
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa90680916085318d21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x94b
  | 6 => 0x94e
  | 7 => 0x5
  | 8 => 0x124b
  | 9 => 0x124e
  | 10 => 0x98a
  | 11 => 0x98e
  | 12 => 0x128a
  | 13 => 0x128e
  | 14 => 0xca
  | 15 => 0xcb
  | 16 => 0xce
  | 17 => 0x168e
  | 18 => 0x9ca
  | 19 => 0x9cb
  | 20 => 0x9ce
  | 21 => 0x12ca
  | 22 => 0x12cb
  | 23 => 0x12ce
  | 24 => 0x168a
  | 25 => 0x168b
  | 26 => 0x10a
  | 27 => 0x10b
  | 28 => 0x10e
  | 29 => 0xa0a
  | 30 => 0xa0b
  | 31 => 0xa0e
  | 32 => 0x130a
  | 33 => 0x130b
  | 34 => 0x130e
  | 35 => 0x180a
  | 36 => 0x180b
  | 37 => 0x180e
  | 38 => 0xb0e
  | 39 => 0xb4b
  | 40 => 0xb4e
  | 41 => 0x16cb
  | 42 => 0x16ce
  | 43 => 0xb8b
  | 44 => 0xb8e
  | 45 => 0x184b
  | 46 => 0x184e
  | 47 => 0xcca
  | 48 => 0xcce
  | 49 => 0x170a
  | 50 => 0x170e
  | 51 => 0xd0a
  | 52 => 0xd0e
  | 53 => 0x188a
  | 54 => 0x188e
  | 55 => 0xd4a
  | 56 => 0x58a
  | 57 => 0x58b
  | 58 => 0x58e
  | 59 => 0x178e
  | 60 => 0xe8a
  | 61 => 0xe8b
  | 62 => 0xe8e
  | 63 => 0x178a
  | 64 => 0x178b
  | 65 => 0x18ca
  | 66 => 0x18cb
  | 67 => 0x18ce
  | 68 => 0x17ca
  | 69 => 0x17cb
  | 70 => 0x98956
  | 71 => 0x128956
  | 72 => 0x8a
  | 73 => 0xb0956
  | 74 => 0x94b16
  | 75 => 0x16c956
  | 76 => 0x956d6
  | 77 => 0xb89
  | 78 => 0xb8956
  | 79 => 0x94b96
  | 80 => 0xd49
  | 81 => 0x1a0a
  | 82 => 0xd4d
  | 83 => 0x150a
  | 84 => 0x17c9
  | 85 => 0x4
  | 86 => 0x5ca
  | 87 => 0x17cd
  | 88 => 0x14c9
  | 89 => 0x134a
  | 90 => 0x14a
  | 91 => 0x99256
  | 92 => 0x4b
  | 93 => 0x1a09
  | 94 => 0x5c9
  | 95 => 0x138b
  | 96 => 0xd0996
  | 97 => 0x5cb
  | 98 => 0x409
  | 99 => 0x1609
  | 100 => 0x1849
  | 101 => 0x589
  | 102 => 0x1789
  | 103 => 0x9c0d6
  | 104 => 0x9d696
  | 105 => 0xb40d6
  | 106 => 0xe9696
  | 107 => 0x179696
  | 108 => 0x18c0d6
  | 109 => 0x1689d6
  | 110 => 0xccd
  | 111 => 0xcc9d6
  | 112 => 0x170d
  | 113 => 0x1709d6
  | 114 => 0x9d796
  | 115 => 0xe89d6
  | 116 => 0x1789d6
  | 117 => 0x9ce96
  | 118 => 0x1692d6
  | 119 => 0xb52d6
  | 120 => 0x16d2d6
  | 121 => 0x592d6
  | 122 => 0x18d2d6
  | 123 => 0xcd696
  | 124 => 0xb8116
  | 125 => 0x178116
  | 126 => 0x17c113
  | 127 => 0xd0a16
  | 128 => 0x188a16
  | 129 => 0xb9316
  | 130 => 0x185316
  | 131 => 0x59316
  | 132 => 0x179316
  | 133 => 0x17d313
  | 134 => 0xd1816
  | 135 => 0x5cd
  | 136 => 0x3ca
  | 137 => 0x24b
  | 138 => 0x15ca
  | 139 => 0x144b
  | 140 => 0x160a
  | 141 => 0x148b
  | 142 => 0x16cb56
  | 143 => 0xccb56
  | 144 => 0x170b56
  | 145 => 0xe8b56
  | 146 => 0x178b56
  | 147 => 0x144e
  | 148 => 0xcd6d6
  | 149 => 0xe96d6
  | 150 => 0x17d6d3
  | 151 => 0xd0b96
  | 152 => 0x188b96
  | 153 => 0x40a
  | 154 => 0xe8b96
  | 155 => 0x18cb96
  | 156 => 0xd1856
  | 157 => 0x28b
  | 158 => 0xe9856
  | 159 => 0x104a
  | 160 => 0x170cd6
  | 161 => 0x58cd6
  | 162 => 0x18ccd6
  | 163 => 0x15ce
  | 164 => 0x18d716
  | 165 => 0x58d16
  | 166 => 0x178d16
  | 167 => 0x179896
  | 168 => 0x14b
  | 169 => 0x8e
  | 170 => 0x198b
  | 171 => 0xa4b
  | 172 => 0x134b
  | 173 => 0x150e
  | 174 => 0xbcb
  | 175 => 0x140e
  | 176 => 0x19cb
  | 177 => 0x154e
  | 178 => 0x3ce
  | 179 => 0x1a4b
  | 180 => 0xecb
  | 181 => 0x74b
  | 182 => 0x40e
  | 183 => 0x194b
  | 184 => 0x1a8b
  | 185 => 0x104b
  | 186 => 0x160e
  | 187 => 0xe8596
  | 188 => 0xe9796
  | 189 => 0x178e96
  | 190 => 0x18d796
  | 191 => 0x24e
  | 192 => 0x95416
  | 193 => 0x94256
  | 194 => 0x1a0d
  | 195 => 0x2c9
  | 196 => 0x12c5d3
  | 197 => 0x117d3
  | 198 => 0x1317d3
  | 199 => 0x1305d3
  | 200 => 0xc5d3
  | 201 => 0x11693
  | 202 => 0x105d3
  | 203 => 0x5c113
  | 204 => 0x5d2d3
  | 205 => 0x5c0d3
  | 206 => 0x5c591
  | 207 => 0x9c256
  | 208 => 0x9d716
  | 209 => 0x12d6d6
  | 210 => 0x12c3d6
  | 211 => 0x12d696
  | 212 => 0x12c596
  | 213 => 0x240d3
  | 214 => 0x10b96
  | 215 => 0x11616
  | 216 => 0x11796
  | 217 => 0x15c5d2
  | 218 => 0x5c3d2
  | 219 => 0x5c253
  | 220 => 0x245d3
  | 221 => 0x24b53
  | 222 => 0x256d3
  | 223 => 0x5d6d3
  | 224 => 0x1445d3
  | 225 => 0x5c9d2
  | 226 => 0x5d453
  | 227 => 0x5d5d2
  | 228 => 0x5d8d2
  | 229 => 0xb5716
  | 230 => 0xb5796
  | 231 => 0xb98d6
  | 232 => 0xb8e96
  | 233 => 0x5c592
  | 234 => 0x184d16
  | 235 => 0x184e96
  | 236 => 0x252d3
  | 237 => 0x25793
  | 238 => 0x257d3
  | 239 => 0x17c253
  | 240 => 0x24e93
  | 241 => 0x25a53
  | 242 => 0x16c5d3
  | 243 => 0x16d7d3
  | 244 => 0x5ce93
  | 245 => 0xcc596
  | 246 => 0xe85d3
  | 247 => 0x5d7d3
  | 248 => 0x1785d3
  | 249 => 0x9296
  | 250 => 0x151296
  | 251 => 0x199353
  | 252 => 0x150996
  | 253 => 0x155416
  | 254 => 0x1a0d52
  | 255 => 0xccd55
  | 256 => 0x5d793
  | 257 => 0x3d716
  | 258 => 0x3ccd6
  | 259 => 0x17da53
  | 260 => 0x1715d6
  | 261 => 0x1a57d3
  | 262 => 0x15ccd6
  | 263 => 0x41896
  | 264 => 0x189616
  | 265 => 0x1a9953
  | 266 => 0x160d16
  | 267 => 0xe83d6
  | 268 => 0x18c256
  | 269 => 0x145696
  | 270 => 0x1443d6
  | 271 => 0x144596
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 2309
  | 6 => 7832
  | 5 => 3960
  | 4 => 103
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (94661+((h/769+packedAt gbK7 (85433+(h % 769)*12) 12) % 3687)*13) 13
  | 6 => packedAt gbK6 (412476+((h/2610+packedAt gbK6 (375936+(h % 2610)*14) 14) % 13758)*14) 14
  | 5 => packedAt gbK5 (250800+((h/1320+packedAt gbK5 (233640+(h % 1320)*13) 13) % 4753)*13) 13
  | 4 => packedAt gbK4 (7448+((h/34+packedAt gbK4 (7210+(h % 34)*7) 7) % 124)*8) 8
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7f0780fff81fffff83ffe01fc09f63cc39f3f3
  | 1 => 0x81f800f83fe1f807fc3fffe0076cbc7226ccfc
  | 2 => 0xffffff003ffe0007ffc1fffff870c07fc70f1f
  | 3 => 0x1ffffffc0000007fffe00003f80ff83f80fe0
  | 4 => 0x1fffffffffffff8000000003fff0003fff000
  | 5 => 0xfe00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x1200801848028a3180632049800521c4085171
  | 1 => 0x9128086a1b21d052a4354ac0832c2c5222c4b4
  | 2 => 0x64533100245400844a8095161850c028c50a0a
  | 3 => 0x219ddab681004127731801832d80d683780fc0
  | 4 => 0x41e66cc7379965c02010060437fa0003b7a000
  | 5 => 0x7800700406118600422118183efffb7c000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeee0faeae8e0feeaeee0faeae8e0feeaeee0faeae8e0feeaeee0faeae8e0feeaeee0faeae8e0feeaeee0faeae8e0feeaeee0faeae8e0feeaeee0faeae8e0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37007
namespace PEqualNP.Outside.L_meta_37007
open PEqualNP.Outside.L_meta_37007.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 7 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 12 := bs0_4_0
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
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 26 := bs1_3_0
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
theorem bs1_4_96 : Interval s1Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_128 : Interval s1Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 134 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := (concat bs1_5_0 bs1_5_32)
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 24 := bs2_3_0
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
theorem bs2_4_96 : Interval s2Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 117 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 46 := (concat bs2_5_0 bs2_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
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
theorem bs4_3_0 : Interval s4Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 2 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 6 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
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
theorem bs5_4_512 : Interval s5Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 539 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96)) (concat (concat bs5_4_128 bs5_4_160) (concat bs5_4_192 bs5_4_224))) (concat (concat (concat bs5_4_256 bs5_4_288) (concat bs5_4_320 bs5_4_352)) (concat (concat bs5_4_384 bs5_4_416) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 664 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 (concat bs5_5_512 bs5_5_544)) (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
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
theorem bgb_4_96 : Interval gbAtlas 4 96 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 103 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_3936 : Interval gbAtlas 5 3936 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3960 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 bgb_5_576)) (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704))) (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832)) (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960))))) (concat (concat (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184))) (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)))) (concat (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696))) (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 bgb_5_1952)))))) (concat (concat (concat (concat (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 bgb_5_2176))) (concat (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 bgb_5_2304)) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432)))) (concat (concat (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560)) (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688))) (concat (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816)) (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944))))) (concat (concat (concat (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040)) (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168))) (concat (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 bgb_5_3296)) (concat (concat bgb_5_3328 bgb_5_3360) (concat bgb_5_3392 bgb_5_3424)))) (concat (concat (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552)) (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 bgb_5_3680))) (concat (concat (concat bgb_5_3712 bgb_5_3744) (concat bgb_5_3776 bgb_5_3808)) (concat (concat bgb_5_3840 bgb_5_3872) (concat bgb_5_3904 bgb_5_3936)))))))
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
theorem bgb_6_6912 : Interval gbAtlas 6 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6944 : Interval gbAtlas 6 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6976 : Interval gbAtlas 6 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7008 : Interval gbAtlas 6 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7040 : Interval gbAtlas 6 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7072 : Interval gbAtlas 6 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7104 : Interval gbAtlas 6 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7136 : Interval gbAtlas 6 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7168 : Interval gbAtlas 6 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7200 : Interval gbAtlas 6 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7232 : Interval gbAtlas 6 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7264 : Interval gbAtlas 6 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7296 : Interval gbAtlas 6 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7328 : Interval gbAtlas 6 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7360 : Interval gbAtlas 6 7360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7392 : Interval gbAtlas 6 7392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7424 : Interval gbAtlas 6 7424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7456 : Interval gbAtlas 6 7456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7488 : Interval gbAtlas 6 7488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7520 : Interval gbAtlas 6 7520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7552 : Interval gbAtlas 6 7552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7584 : Interval gbAtlas 6 7584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7616 : Interval gbAtlas 6 7616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7648 : Interval gbAtlas 6 7648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7680 : Interval gbAtlas 6 7680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7712 : Interval gbAtlas 6 7712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7744 : Interval gbAtlas 6 7744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7776 : Interval gbAtlas 6 7776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7808 : Interval gbAtlas 6 7808 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7832 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672))) (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800)) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928))))) (concat (concat (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 bgb_6_1152))) (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 bgb_6_1408)))) (concat (concat (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664))) (concat (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792)) (concat (concat bgb_6_1824 bgb_6_1856) (concat bgb_6_1888 bgb_6_1920)))))) (concat (concat (concat (concat (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016)) (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 bgb_6_2144))) (concat (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400)))) (concat (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624))) (concat (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880))))) (concat (concat (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104))) (concat (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)) (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360)))) (concat (concat (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488)) (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616))) (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872))))))) (concat (concat (concat (concat (concat (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 bgb_6_4096))) (concat (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 bgb_6_4224)) (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 bgb_6_4352)))) (concat (concat (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448)) (concat (concat bgb_6_4480 bgb_6_4512) (concat bgb_6_4544 bgb_6_4576))) (concat (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 bgb_6_4704)) (concat (concat bgb_6_4736 bgb_6_4768) (concat bgb_6_4800 bgb_6_4832))))) (concat (concat (concat (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928)) (concat (concat bgb_6_4960 bgb_6_4992) (concat bgb_6_5024 bgb_6_5056))) (concat (concat (concat bgb_6_5088 bgb_6_5120) (concat bgb_6_5152 bgb_6_5184)) (concat (concat bgb_6_5216 bgb_6_5248) (concat bgb_6_5280 bgb_6_5312)))) (concat (concat (concat (concat bgb_6_5344 bgb_6_5376) (concat bgb_6_5408 bgb_6_5440)) (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568))) (concat (concat (concat bgb_6_5600 bgb_6_5632) (concat bgb_6_5664 bgb_6_5696)) (concat (concat bgb_6_5728 bgb_6_5760) (concat bgb_6_5792 bgb_6_5824)))))) (concat (concat (concat (concat (concat bgb_6_5856 (concat bgb_6_5888 bgb_6_5920)) (concat (concat bgb_6_5952 bgb_6_5984) (concat bgb_6_6016 bgb_6_6048))) (concat (concat (concat bgb_6_6080 bgb_6_6112) (concat bgb_6_6144 bgb_6_6176)) (concat (concat bgb_6_6208 bgb_6_6240) (concat bgb_6_6272 bgb_6_6304)))) (concat (concat (concat (concat bgb_6_6336 bgb_6_6368) (concat bgb_6_6400 bgb_6_6432)) (concat (concat bgb_6_6464 bgb_6_6496) (concat bgb_6_6528 bgb_6_6560))) (concat (concat (concat bgb_6_6592 bgb_6_6624) (concat bgb_6_6656 bgb_6_6688)) (concat (concat bgb_6_6720 bgb_6_6752) (concat bgb_6_6784 bgb_6_6816))))) (concat (concat (concat (concat bgb_6_6848 (concat bgb_6_6880 bgb_6_6912)) (concat (concat bgb_6_6944 bgb_6_6976) (concat bgb_6_7008 bgb_6_7040))) (concat (concat (concat bgb_6_7072 bgb_6_7104) (concat bgb_6_7136 bgb_6_7168)) (concat (concat bgb_6_7200 bgb_6_7232) (concat bgb_6_7264 bgb_6_7296)))) (concat (concat (concat (concat bgb_6_7328 bgb_6_7360) (concat bgb_6_7392 bgb_6_7424)) (concat (concat bgb_6_7456 bgb_6_7488) (concat bgb_6_7520 bgb_6_7552))) (concat (concat (concat bgb_6_7584 bgb_6_7616) (concat bgb_6_7648 bgb_6_7680)) (concat (concat bgb_6_7712 bgb_6_7744) (concat bgb_6_7776 bgb_6_7808))))))))
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2176 : Interval gbAtlas 7 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2240 : Interval gbAtlas 7 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2272 : Interval gbAtlas 7 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2309 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))))) (concat (concat (concat (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248)) (concat (concat bgb_7_1280 bgb_7_1312) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)))) (concat (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536)) (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 (concat bgb_7_1664 bgb_7_1696))))) (concat (concat (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824)) (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 (concat bgb_7_1952 bgb_7_1984)))) (concat (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 (concat bgb_7_2112 bgb_7_2144))) (concat (concat bgb_7_2176 bgb_7_2208) (concat bgb_7_2240 (concat bgb_7_2272 bgb_7_2304)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeee0faeae8e0feeaeee0faeae8e0feeaeee0faeae8e0feeaeee0faeae8e0feeaeee0faeae8e0feeaeee0faeae8e0feeaeee0faeae8e0feeaeee0faeae8e0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809440 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37007.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,4]⟩,⟨.or,[0,2]⟩,⟨.and,[3,5]⟩,⟨.or,[2,8]⟩,⟨.or,[4,9]⟩,⟨.and,[3,6]⟩,⟨.and,[1,9]⟩,⟨.and,[7,11]⟩,⟨.or,[0,12]⟩,⟨.and,[10,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37007

open PEqualNP.Outside.L_meta_37007 in
theorem PEqualNP.Outside.L_meta_37007 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
