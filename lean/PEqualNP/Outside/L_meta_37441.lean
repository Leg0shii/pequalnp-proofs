import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37441.Model
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


end PEqualNP.Outside.L_meta_37441.Model

namespace PEqualNP.Outside.L_meta_37441
open PEqualNP.Outside.L_meta_37441.Model
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

def mirrorSteps : List Move := [swapRows 67]

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

end PEqualNP.Outside.L_meta_37441

namespace PEqualNP.Outside.L_meta_37441
open PEqualNP.Outside.L_meta_37441.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xbdaa4a938002d3602580ec14c40b110004b21000000391aa22e0164188809ab0009dc02d7a85cc553cc00401601020810430c3082fe43fd43fc43ff32fe32fd32fc32ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x441fe30883fa61107f0c220ff90441ef20883f641107fd4d20bfa9a41df53482bea6907f94d20bf29a41fd53482faa6907f14d20be29a41dc53482b8a6907f90d20fea1a41fc43483fe64907f8c920f719241fd32483da64907f0c920ffa8a417f51483eea2905dd4520ff28a41fd51483f8a2905f14520fa28a417451483fe62907f8c520fe98a41fc31483fe42907f88520f710a41fd21483f842907b08520ff98241fe30483fa60907f0c120ff90241fb20483fc40907b88120ffa98417f53083fca6105f94c20fea98417d53083f8a6105f14c20ff21841fd43083f886105f94820ff99041fe32083fa64107f0c820ffa8841fe51082fca2107f54420bea8841fc51083fe62107f8c420fe98841fc31083fe42107f88420f710841fd21083f842107b08420bf28041ff30083fc60107f4c020fe18041ff20083de40107f88020fd10041fd20083da40107e48020ffa9e217f53c43fca7885f94f10fea9e217d53c43f8a7885f14f10ff21e21fd43c43f887887fd4b10bfa9621fe52c42fca5887f54b10bea9621fc52c42f8a5887fccb10ff19621fd32c43f865887fcc710ff18e21fd31c43f863887fc8710ff10e21ee21c43fa43887f08710f610e21ff30c43f661887f8c310fe98621fc30c43f061887fc8310ff10621fd20c43f841887fd4e10bfa9c21fe53842fca7087f54e10bea9c21fc53842f8a7087f90e10fea1c21fc43843fea5085fd4a10ff294217e52843dca5085b94a10fea94217d52843daa5085b54a10fe294217c52843fe65087f8ca10fe99421fc32842faa3087fcc610ff18c21fd31843f863087fc8610fb90c21fe21843dc43087f48610fe10c21ec21843e843087908610bf28421ff30843fc61087f4c210fe18421ff20843fc41087f48210fe10421ff10843ee21087ec4210ffa9a217f53443bea68857d4d10ff29a217e53443faa6885f54d10fe29a217c53443b8a6885714d10ff21a21fd43443f886887fd4910bfa9221ef52442dea4887f94910bf29221fd52442faa4887f14910be29221ec52442d8a4887fcc910ff19221fd32443f864887fcc510ff18a21fd31443f862887fc8510ff10a21ee21443fa42887f08510f610a21ff30443fc60887f4c110fe18221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff53042fea6087f94c10bf29821fd53042faa6087f14c10be29821fe43043fa86087f10c10ffa90217f52043fca4085f94810fea90217d52043f8a4085f14810ff99021fe32043fa64087f0c810bf28821ff31043fc62087f4c410fe18821ff21043ee42087f88410f710821fd21043f842087b08410fa10821e421042fca0087fcc010fd98021fe30043fa60087f0c010fc18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xe50087daa010fb14021ffaa661fe54cc2fca9986f953309f2a661fd54cc2faa9986f553309eaa661fc54cc2f8a9987fd0f30ff21e61fd43cc3f887987fd4b30ff296617e52cc3faa5985f54b30fe29661ff42cc3fc85987f50b30fe21661ff32cc3fc65987f4cb30fe19661ff51cc3fca3985f94730fea8e617d51cc3f8a3987fd0730ff20e61fd41cc3f883987fcc730ff18e61fd31cc3f863987fc8730ff10e61ee21cc3fa43987f08730f610e61ff40cc3fea9185fd5230ff2a4617e548c3faa9185f55230fe2a4617d538c3fe87187f90e30ef21c61fd438c3ba87187f10e30ffa9461fe528c2fca5187f54a30bea9461fc528c3fe85187f90a30fea1461fc428c3fe65187f8ca30ef19461fd328c3f86518770ca30ffa8c61fe518c2fca3187f54630bea8c61fc518c3fe83187f90630fea0c61fc418c3fe63187f8c630ef18c61fd318c3f86318770c630ff90c61fe218c3dc43187f48630fe10c61ec218c2fca1187fd0230ff20461ff308c3be61187ecc230ffaa2617f544c3fca8985f95130feaa2617d544c3f8a8985f15130ffa1a61fe434c3fa86987f10d30ffa92617f524c3fca4987f54930fe292617c524c3fe84987f90930fea1261fc424c3fe64987f8c930fe99261fc324c3fea2985fd4530ff28a61fd514c3f8a2985f14530ffa0a61fe414c3fa82987f10530ff98a61fe314c3fa62987f0c530ff90a61fe214c3dc42987f48530fe10a61ec214c3fe80987f90130fea0261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061fd540c2faa8187f15030be2a0617e530c3fe86187f90c30ef21861fd430c3ba86187f10c30ffa9061fe520c2fca4187b94830b729061fd520c2faa4187b54830b6a9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830ef19061fd320c3f86418770c830ffa8861fe510c2fca2187f54430bea8861fc510c3fe82187f90430fea0861fc410c3fe62187f8c430ef18861fd310c3f86218770c430ff90861fe210c3dc42187f48430fe10861ec210c2fca0187fd0030ff20061fd400c3f880187fcc030ef98061fe300c3f460187f4c030ee98061f9300c3fea7905fd4f20ff29e417e53c83faa7905f54f20fe29e417c53c83fc87907f50f20fe21e41ff32c83fc65907b8cb20fe99641ed32c83f865907fd4720ff28e417e51c83faa3905f54720fe28e41ff31c83fc63907f4c720fe18e41ff21c83fc43907b88720fe90e41fc21c83d843907fcc320ff18641fd30c83f861907fd4e20bfa9c41fe53882fca7107f54e20bea9c41fc53882f8a7107f90e20fea1c41fc43882faa5107fcca20ff19441fd32883f865107fd4620ff28c417e51883faa3105f54620fe28c41ff31883fc63107f4c620fe18c41ff21883fc43107b88620fe90c41fc21883d843105f94220ff98
  | 2 => 0xc6faa198ff14331ffaa4637f548c7fca918df95231feaa4637d548c7f8a918df54e31ffa1c63df438c7fc8718ff50e31fe21c63dc438c7fea518ff94a31bf29463fd528c6faa518ff14a31ffa1463fe428c7fa8518ff10a31ff99463fe328c7fa6518ff0ca31bf28c63ff418c7fc8318ffcc631ef98c63f7318c7fea118ff94231bf28463fd508c6faa118ff14231ffaa2637f544c77ea898cfd5131ff2a2637e544c7faa898df55131fe2a2637c544c778a898cf15131ffa1a63fe434c7bc8698ff50d31eea1a63fc434c7fea498dfd4931f7a92636f524c7fca498ff54931fe292637c524c7d8a498db14931ffa1263fe424c7fa8498ff10931ff99263fe324c7fa6498ff0c931ffa0a63fe414c7fa8298ffcc531fb98a63fe314c7bc6298ffd4131bfa8263fb504c6f6a098ff94131fea8263fc504c6f8a098fe14131bc28263ff540c6fea818ff95031bf2a063be540c67ca818ff55031beaa063bd540c67aa818ff15031be2a0637e530c7fe8618f7d0c31ff21863fd430c7f88618f710c31ffa9063fe520c6fca418ff54831bea9063fc520c7fe8418ff90831fea1063fc420c7fe6418ff8c831fe99063fc320c6fca218ffd0431ff20863fd410c7f88218ffcc431ef98863fe310c7ec6218ff4c431ee98863f5310c7fea018ff94031bf28063fd500c6faa018ff14031ffa9e437f53c87fca790df94f21fea9e437d53c87f8a790df14f21ff21e43fd43c87f88790ffccb21ff19643fd32c87f86590ffcc721ff18e43fd31c87f86390ffd4321ff286437e50c87faa190df54321fe28643ff53886fea710ff94e21bf29c43fd53886faa710ff14e21be29c43fe43887fa8710ff10e21bea9443ff32887de6510ff8ca21f719443fd32887da6510ff0ca21f6194437e51887fe6310ff8c621fe98c43fc31887fe4310fbc8621fb90c43ff50887fca110df94221fea84437d50887f8a110fbd4e21f729c43ed53887d8a710fb90e21f6a1c43ec43886dca310fbcc621f718c43ed31887d86310fbd4221f728443ed50887d8a110ffd4d21bfa9a43fe53486fca690ff54d21bea9a43fc53486f8a690ff90d21fea1a43fc43487fe6490ff8c921fe99243fc32487fe6290ff8c521fe98a43fc31487fe4290fdc8521ff10a43ee21487fea090dfd4121ff28243fd50487f8a090df14121ffa98437f53087fca610df94c21fea98437d53087f8a610df14c21ff21843fd43087f88610df94821ff99043ef32087fc6410fb8c821fe99043ed32087f86410fb0c821bf28843ff31087fc6210ff4c421fe18843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010ff54021bea8043fc50087dea610fb94c21f6a9843ec53087dc8610fb50c21f621843ee51086dca210f994421f798843ee31087da6210fb0c421f7a8043e
  | 3 => 0x1400000c00000c02000401000800c00000000000401000000003001c03000002400000c00000000401001400000001800000000000400002401400000801800000000401001001c00002400800800001002400800002404400800403002000000000001400000400007c02000400000400000000405800001800400c00400c00400000800800402400800800802000800c02000800800400000800800000001800002c00000000801c00003800400400001801c00800800c00000800000401000002001c00401800801000400002000400000401400400000c00000802c00800400400000002800800000000001c03400000002400401400003000000402000400000403c03000000c03afaa921df94e43ffa1c87df4390ffea521ff94a43bf29487fd5290efaa521ff14a43ffa8c87fe5190efca321ff54643bea8c87fc5190ffea121ff94243bf28487fd5090efaa121ff14243ff21a87be4350ffea4a1dfd4943ff29287fd5250ff8a4a1df14943ffa8a877f5150ffca2a1ff54543fe28a877c5150ffea0a1dfd4143ff28287fd5050ff8a0a1df14143bf29887fe4310fbc8621ff50c43eea18879d4310ffea421ff94843bf29087fd5210efaa421ff14843ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043ffaa665fe54ccafca9997f55332beaa665fc54ccaf8a9997fd0f32ff21e65fd43ccbf887997fd0b32ffa8e65fe51ccafca3997f54732bea8e65fc51ccbfea1997f94332bf28665fd50ccafaa1997f14332ffaa4657f548cbfca9195f95232feaa4657d548cbf8a9195f54e32ffa1c65fe438cbfa87197f10e32bf29465ff428cbfc85197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe86997f90d32fea1a65fc434cbfe84997f90932fea1265ff324cbde64997f8c932ef19265ff514cafea2997f94532fea8a65fc514caf8a2997fd4132bfa8265fe504cbfaa0997f14132be28265ff540cafea8197f95032bf2a065fd540cafaa8197f15032be2a0657e530cbfe86197f90c32fea1865fc430cafca4197fd0832ff21065fd420cbf884197fcc832ef99065fe320cbdc64197f4c832ee99065ed320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea998ff95331bf2a663fd54cc6faa998ff15331be2a663ff43cc7fc8798f790f31fea1e63dd43cc7f88798ffd4b31ff296637e52cc7dca598db94b31fea96637d52cc7daa598db54b31fe29663ff42cc7fc8598ff50b31fe21663ff32cc7fc6598ff4cb31fe19663ff41cc7fea198ff94331bf28663fd50c
  | 4 => 0xdd0030000000001899e20001664000000001bf800167db50580000000bb8000ed1940000001d702480000002b1c98c74001ff8000001b391e0001c18000000000001c04000330b711ac000ad91d8a74001514002214000d0800000052835149db588507f8345e340009900011b08809c22280000000000019a0000000000000000000000000001880cb1ad14c80b80000005192e87f400062d4c07ed0e93e00687c00002c01a9640000000000000000000000e38000000000000000b200012d9020000000800561289ea13980005900018b00000b00017c40014e92584e430d30c0001080015743b9178001c70000001df0bb15ed8321700010b97f08c977049000144156d8e80000000000005d1a3cd80b74000398000001270000000fd4e34199d34849cbc9a01890d96380019fc625908969894a015f5fa0000001d11498000001fa96dc698001cd8b34000934f2d0f40013300000000015b0001838000000688d20e18cf8000998000e48001494000000000628000a100005716292b06b81b84f96b053871a3108f40013416ec0000001f8000a6d3b0f90be80000016714f9e41729419df9668c004d817a1a1a080ecb09c22110000600000000000000a8800175c001ae85692e00000fa1c8f99600e053b9eb11ea2505b0000001d380011f00008a8000001238505c500005c8ce205c001e8800044400000000000000000000000802805802400000001000c01800801c00000002400400000802c00000802c00400406000000000000001400800800401400801000000000000000c00800000000400001000002000000400401401001000000401800400400000400000800004800800c02400400000400000c01000000400000400400000400001001400000000400400800801c00c00400c00800000800c04800000400803c01c00800000401001403400800000000001c00800400002800400c00401c00800001402000800400001803401801c00000400801000401400000002c00001c00800001c00000002800403000400c00000400000400400c00800401404c02400800001c02000004400000c00001404400002c00000000400000401000401c00402002000000c0000300000200100080000040000100140000040b800000401000800400000400401400000001401400000000004401c06003000c00001800001000800400000001402c00c00c01002800000000000800000000000000000001000402001c02001c01002c01400400800800400000401400400001801c00000800000000000c00400800400008c03c00003400c01000401801400400c00800000400000800000800001c0140080000080e800c00000001000000000000c01001002000400003800000c00c01400000000000c00400c00000403c00000000800000
  | 5 => 0x13616c9ca90e4f256193500017b9769d54000a1c000000730000000c280015e800000032c42531000000190c0022f040cbc0fe000000000000000005c001338001a484de1617b542e2c1a30000001dd904807db9800070c0000015880008599500008a49286f534cc202d2108b008885bc3080016d9b60cd0fa8000fd06548bdc38000678001d28000a08000000640f18b32120000000000000000000264000002124000d4800044c36000015118800024d0f1d50002230000000861408000001a000022a0af4000890001c80002322090f107bc00075d4745a8adcba9d980000019c8002271014040e64000cb96861789480000000e4000001e9169dccd55482800230a2d0001fd8000ee00018a5754000000001b10d6800154c000001300284000000001e5c0017a81c800052c000000000002354000000001d8800000000054c000c800015244fc0018c8b54335889a40000000001f404c0000001b28001570000000f7a338000000140001b700c138184000164985c001679568eb07c83149c6031d2c1841ad090001f1800196d24a0a07780000003798ec000169f89f80001bd2158b10000001810001580808000000f70838001511790f49f6d3e40015799e843c0009e8001d69ac818de016e60382f8000000a705110317b0128002280d8c1c013800059439e0f000000181874dbb80001d80009a8001fba00928400069c3b4b68000f4210e1b00003907b80000016f4000000001960000070be0000000000000000000000000000fd92990c04413c02746906b6050a39658000000d30000000000000000000bf0000000000000000bf80000000000000000000000000005787e81fcb3daa14518608199315b40000007518b9848e68000bc8a640002143c0da9971c693781f0000a8cc10104da2258610001f44879ba400000171090220c811c0937198226976caa497221041a0d15f9fb0ce91314fc4b02790591d08b0a28d060784681b0769a2c00000122c70000000029223935dac0002358c68001f10fb8b49f08ff10617f97a18a8001a604c4000659f9160490df99228000e31e820116f80017cc7949e1ba9d40000000540000001f71f78f64000a6877c000a0e1b95d96300d1f55590000258000f2a068c854d80000000000012500013f80000011bd6901a02e90d0ae8190d6514800000079970cb9000140da200000011f800000017d42526c0015380582fc002318b58000000000000001f58000001ada3685adb90e98000001610000845550ed4002260b8a034b6cf02040000db8fc90ee0f95480490958f8788f58de04080001200000000000022e09b1560001cca058000130a5c0020199780000012a0000c880000a8d380022f8181d200e12a86506f1400c70fc2348001ec93d0f50000000001751ef8001070908000c09558
  | 6 => 0x1e896541c002131f480012121a96f00900012d06687b4fb4508e15a2800000000000097c000174c1c001d08000db09591a0002188221cf9ea8250fe80e85b50acc7cca8eec8ac0000000000000005357580009311641600011b4001430ab01d0a18001e3a2c8ae102ce7d5e1788dcc93ca840003e8000000f307e09394840003a05545203184a8c7800000000142979d7d0a6000035c001a100008fc000000001318000af88980006d8c40001da80006a1541f622199b03e086a1518908b85b9d80078f680014784380884d400168dcb09c800146c000000000000001488ed80000000000000014686d0a30000ea8230001ab8980000748c2d6e04f13e820000019cc31a70bf4a459d0001749ce117544864cf6151e330ac19d8e08d19a59c5a1f1a90a91f39d58d711c0228c245980d80000004d1fe160945d1aa1d1dc99386087b0cfc271bf40004280002e0000001698dc116e072140ab8ec08c4000000000000001224000ea0000000000000b3861c7a8000760000000000001c1c000000001051bea2a800229800126041cd41521f2800000000000131c000000000001f20000000001bc1eade49305232278000bd0000548000a7c9b8e500015b9cd60b00002880017406607058adff19a94708a0000b9d5d05e1a9ca58000f20001a258656a40010f9990001465c91480000b8d460000000000001de97e18213d80015e5500000000001b89530000a50f3800000025c64478e04d8680000000020c9434002240001f50cf0489a505884615440023617e8000000000aec001c487d000000091c000000000dea100000000001681f69b0800221c000000002290000000b803b0000001278000001cd1bb5c780000000000000000000019040010a00000000000017bc000000000791e580000000006b0000e4136400110c060000000f3c0003ac3a40021918080022880000000003f8000bac0021e0000c395a90780000000012205d95840006ac34800000000000083d34a1f81586a557c3d1af5b687800000000004f40000002114f1879fd0c04000000001988914001bfe2b40021680014b21180000010691504480000000006c0aa1b780080003282a800000020c000204000000001d480015f0000420000000000000458ff94149612087580022d8000000000000000820a9c000a94000000950a4821965de29b00709dba1c0c143c9ce8738c18c51f4df949d8000c90cc0ee4ef80008d9d610a515e088c98d0c114aa8369cc0281921aa577d6e80000002b853170000000065c000149aa8000000000479234b502a01b426064a0e8000c8c001198001422198018000000000ef00000012680000021e91c400030547c000000001714af00007ac00185a0200000000018e4e74001019359024001355138195241be09101012807f0000001b180
  | 7 => 0x31dc880007405f88cde4566cd8918059c8f8002209518000a800016b9654000000001128001e300000c807406c0020600000002d84cc002029cb8001d3d704e3e350fdccf5ae0000b180018f5dd0d6c000268000001c40001fe921c0000000004e80000021800a00009440000000000020b80000000000013c8000940000b28000000000000000000000978000d116b4000118b963289040000004c80000000015bc00191a1d9bb07a1780e71e111621140f1b30000974b852b98d9029c2a04519096c8e0c4863c381011760000000001abc0017197c8415a897ac00136c0985f1fc1505ef1bad720550000989ee8000fbd998e1d38901ce6c0019b86700006fc001dc0000dd9d18000000000000000000000d580280000000000000022e854453db80a200008b6220000000000ca00021fd3089d0000000a55e516d00020d879d0a80002541e07847e40017303f0000000001438001ee1ed0558001e69a191c8a79e79e19af87fc000001bf00013f12f87d9171ed8000000ae45c0df19e22b8ba5fc86e04b9949c10000000000481ec0001eb80000018d00000000005a08c0000000000000e911198a16940f4e2cfcc635a357dc340771168df8e000000dc0000021280017653685e8000239202301d00d90c3400174c000000000000000001cf1f5dd909f8000001a8117ce10d28000fc4e24710b99100ac83214e02f109c3a8000edd59a080d758280000000018700008416a8ec99f5bd811d2740000000000013a80000000000016a0000b608d00006a80000000015c0001411a94d980009255c89d4638e580017860484ec0009bc0014a88e40000015290992c0d510382094a1d78d798e1321621f31e71e6ca4c4353f50b0001af19f92c95093dc000bfdca1900000000000001855c311ba1480019116605a40015642984517c0fa0a980000017a474400000155d3a16c20c000058c00000000000000000092c0000000018c0000000000a243380000017d9c00002248000000000e890816d6200f8835800000026da3834c17000000000002000112143d3140008308ec000b784980000017992f0400470001c622bc3240000020008707a4d00002138b2c5c40018501a4630e80039e995c4001bbc9f0b45b49000000001d300018006e9958000e780015ac000e60000000cd8f08001e3c10c000728000001b740000002c83010e00000000000017740015fda68000010001cc550d48c0657d60a9de0a420e00011094f4388240000cc8000c3d928084ba0500001e0965000189c000050001b40001184000000001bc8fa4e0cad0dc8c59458b7c3d9969ab16ac4e0680411ba16fc720ee8000000f800000018f0110000000000001e54000001159779c14a146186c8000000000370001da0918001b200000006f80000008e800152c000001a7800
  | 8 => 0xb40000000bda340310fb000000121800000000000000173835484d0c8001140000000e28000000001f007548340000010880000017080000000000020980000000010400015a00009cc000000001db0001009a99e614900014d0c60e206222b000129000033d4b800168800043132827d110eb93904a13ec920d614059f00000000000000000019c00800008f0b4c000000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x421043e63108410f94c421043e43108410fa98021043e96008410dd59421042756508410bd98821043e66208410ddd4821043e65208410dd54821043e55208410f9cc821043e63208410f94c821043e43208410fc98021042f56008410fc58021043e66508410d999421043e56508410d959421043e76308410f998c21043e56308410f918c21043e75308410f994c21043e55308410f914c21043e64308410f950c21043e44308410f9d8021043e66008410f898021043e56008410f858021043e460084109f98e500427d63940109f98a500436e62940109b98a500427d6294010db58a500426d62940109f58650043772194010db886500436c2194010dd086500436421940109f59730042be64cc010af59330043e421cc010be597300437965cc010be99330043ba64cc010ae99330043b964cc010be193300437b53cc010de54f30042f961cc010de94730043f321cc010fa88730043e821cc010fc08730043e021cc0109fd96300427d658c010d794e300435d538c010bd98630042f5618c010f908630042fa608c0109fd9530043e4214c0109fd94300427e650c0109f594300427c650c010d794c300435d530c010bb98830042ed620c010bd98430042f5610c010f908430043d9300c010be5943004379650c0109e59430042fa640c010be19030042fa630c010f698c300437b530c010f694c3004379530c010f654c30043da430c010f650c30043ea620c010fa58830043da320c010f60c830043f2610c010be58430043f1610c010de94430043da310c010f60c430043f3210c010fa88430043e8210c010fc08430043e0210c0109f597200436f52c8010db14b20043e421c80109fd96200427d6588010db94a200436d5288010bd98620042f56188010f9086200427f6548010b7d8d20042dc6348010dbd49200436c5248010bdd8520042f46148010f9085200427f65080109f994200427d65080109f194200436e5208010db54820042f66108010bd58420043e42108010f988710043e421c4010dd59710042f662c4010bd18b10043f330c4010fc0c310042ee6284010bb58a10042f56184010dd94610043e42184010be596100437965840109e59610042fa6384010be18e10043ea6284010fa58a10042f96184010de94610043f25184010fcc8610043ea2184010fa08610043f02184010f8086100427f6544010b7d8d10042dc6344010bbd8910042ec6244010f988510043e42144010bdd95100437765440109dd9510043d76344010f518d10043e76244010bd98910042f46244010f918910042e46244010bdd8110043765044010bed95100437b65440109ed9510043db6344010be98d10042f86344010f618d10042d86344010fad8910043e86244010bed8510043f36144010de94510043f25144010fa88510043e82144010
  | 1 => 0x43e66284110f958a10443e75284110dd94a10443745284110f914a10443645284110fcd42104427e64d4c109f593530427e62d4c109f58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10de18153042be6414c10af590530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109fd96430427e6590c109f596430427c6590c10d794e430435d5390c10be98243042f96090c109fd95430427e6550c109f595430427c6550c10d794d430435d5350c10bdd8543042f46150c10bed8143042f86050c109fd94430427e6510c109f594430427c6510c10e750c430427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810dbd4a520427e63948109f58e520427f63548109f18d520436f62548109fd85520427d6154810dd185520427f60548109f58152042de6314810b758c520436d52148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109f984520437661148109f980520437a60148109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc810bd98732042f561cc8109fd96320427e658c8109f596320427c658c810db94a320436d528c810be98232042f9608c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810db949320436d524c810bdd8532042f4614c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c8109f98e510427d63944109f98a510427d62944109f59731042ee62cc410bb58b310427f658c4109f596310435e538c410d754e31042fa608c410be582310427f654c410afd9131042bc644c410bbd8931042ec624c410bed81310427f650c4109f59431042be640c410af590310435e530c410d754c31042fa600c410be580310427d65c8410bd597210437565c8410ddd4b210437552c8410bd583210427f65884109f596210436e5288410db54a21042f66188410be98221042f96088410dbd96210436e6588410db596210436c6588410dbd4e210436e5388410db54e210436c5388410bb98621042e66188410db94621043ea6088410fa582210427f65484109fd94210427d6508410db948210436d5208410f948421042fa6008410be580210436f6508410db994210436d6508410db194210436f5308410db94c210436d5308410db14c21042ee6108410f9984210436e5108410f9cc
  | 2 => 0x52cc9109fd96324427e658c9109f596324427c658c910cfd52324433c548c910d7d4e324435c538c910dbd4a324436c528c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c910d7d4d324435c534c910dbd49324436c524c9109fd94324427e650c9109f594324427c650c910cfd50324433c540c910d7d4c324435c530c910dbd48324436c520c910be98032442f9600c9109f997314433f54cc510cf153314435f53cc510d714f31442ee62cc510bb58b314436f52cc510db14b31442fa60cc510be583314427e658c510cfd52314433c548c510d7d4e314435c538c510dbd4a314436c528c5109f19531442bf644c510af191314433f544c510cf151314435f534c510d714d31442ef624c510bb189314436f524c510db14931442fb604c510be181314427e650c510af99031442bd640c510cfd50314433c540c510d7d4c314435c530c510dbd48314436c520c5109f997214435f53c8510d714f214436f52c8510db14b21442fa60c8510be583214427e6588510d7d4e214435c5388510dbd4a214436e5288510db54a214436c5288510bb996214436e65885109b996214436f5388510f3d4e214434f5388510db94e214436d5388510db14e21443cc5388510d314e21442ee61885109f195214435f5348510d714d214436f5248510db14921442fb6048510be181214427e6508510d7d4c214435c5308510dbd48214436e5208510db548214436c5208510bb994214436e65085109b994214436f5308510f3d4c214434f5308510db94c214436d5308510db14c21443cc5308510d314c21442ee6108510f9984214427e65cc110af99330442bd64cc110cfd53304433c54cc110d7d4f304435c53cc110dbd4b304436c52cc110bd98730442f561cc1109f996304433f548c110cf152304435f538c110d714e304436f528c110db14a304427f654c1109f595304427c654c110cfd51304433c544c110d7d4d304435c534c110dbd49304436c524c110bdd8530442f4614c1109f994304433f540c110cf150304435f530c110d714c30442ee620c110bb588304436f520c110db148304427e65c8110d7d4f204435c53c8110dbd4b204436c52c8110bd98720442f561c81109f996204435f5388110d714e204436f5288110db14a204427f65481109f595204427c6548110b7d8d20442dc6348110d7d4d204435c5348110dbd49204436c5248110bdd8520442f461481109f994204435f5308110d714c204436f5208110db14820443e92008110d7d4f104435c53c4110dbd4b104436c52c4110f6d4f104437a53c4110de14f10443d853c4110d614f10443eb52c4110fa14b10443ea21c4110fa087104435f5384110d714e10442ee6284110bb58a104436f5284110db14a10443e62184110f908610443d75384110f514e104
  | 3 => 0xd10d7d8b534435e62d4d10d758b534435c62d4d10d7d87534435d61d4d10d7d83534435d60d4d10af99253442bd6494d10cfd52534435f5394d10bb98a53442ed6294d109f992534433e6494d108f992534427d6494d10cf592534423d6494d109f98e534425e6394d109f98a534436e6294d109b98a534427d6294d10db58a534426d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10cfd5153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109ed81534427e6514d10cfd50534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d109f184534427e6014d109f18053442de6514d10d7994534425e6514d10d7d50534439f5414d10c7d50534435e5414d10d7550534435c5414d10e7150534431c5414d10d7d90534435e6414d10d7590534435c6414d10d7d88534435e6214d10d7588534435c6214d10d7d84534435d6114d10d7d80534435d6014d10d7440534427f6590d109f996434427d6590d109f196434433f5490d10cf152434435f5390d10d714e434427f6550d109f995434427d6550d109f195434435f5350d10d714d434427f6510d109f994434427d6510d109f194434435f5310d10d714c434439d4310d10bd98443442f56110d10d7d4f524435c53d49109f98f524427d63d4910dbd4f52443cf53d4910d3d4f524436e53d4910db54f524436c53d4910f314f524434c53d4910dbd8f524436e63d4910db58f524436c63d4910db90f524436d43d4910db10f524436f61d4910db587524436f60d4910db58352442de6394910b758e524435f5394910d714e524436f52949109f98e524435e63949109798e524427d6394910d758e524425d63949109f98a524426e62949109f586524437561949109f58252443796094910b7d8d52442dc6354910d7d4d524435c53549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427761549109fd81524437b60549109f994524435f5314910d714c524436d52149109f98c524427d6314910db988524427e61149109f184524427e60149109f18052442ee6514910db994524426e6514910dbd4c52443cf5314910d3d4c524436e5314910db54c524436c5314910f314c524434c5314910dbd8c524436e6314910db58c524436c6314910db90c524436d4314910db10c524436f61149109b984524436d61149109b184524436f6014910db580524436d10149109fd97324427e65cc9109f597324427c65cc910cfd53324433c54cc910d7d4f324435c53cc910dbd4b324436c
  | 4 => 0xb585528436e6054a10db181528436d5214a109f98c528427d6314a10db98852843756114a10de980528427f65cca109f997328427d65cca109f197328436e52cca10db54b32842f661cca10bd587328427f658ca109f996328427d658ca109f196328436e528ca10db54a328427f654ca109f995328427d654ca109f195328436e524ca10db54932842f7614ca10bd185328427f650ca109f994328427d650ca109f194328436e520ca10db54832842fa600ca10be580328435e53cc610d754f31842ee62cc610bb58b318436e52cc610db54b31842fa60cc610be583318435f538c610d714e318436e528c610db54a31842bf644c610af191318435e534c610d754d31842ef624c610bb189318436e524c610db54931842fb604c610be18131842be640c610af590318435f530c610d714c318436e520c610db548318436e52c8610db54b21842fa60c8610be583218437565c8610ddd4b21843e652c8610dd54b21843e552c8610fc98321842f560c8610fc583218436f5288610db94a218436d5288610db14a21842ed6588610db596218436f5388610db94e218436d5388610db14e218436e5248610db54921842fb6048610be181218436f5208610db948218436d5208610db14821843e52108610bb594218436d6508610dbd4c218436e5308610db54c218436c5308610f998421843e73108610f98c421843e53108610f90c421842f56508610dd59421843e66208610ddd4821843e75208610f994821843755208610f954821843655208610f914821843e73208610f98c821843e53208610f90c821842f56008610f959421842e56508610d959421843e76308610f998c21843e56308610f918c21843e75308610f994c21843e55308610f914c21843e64308610f950c21843e44308610f9d8021843e66008610f958021843e46008610af99330842bd64cc210db94b308436d52cc210f9087308435e538c210d754e308436e528c210db54a30842f6618c210bd58630843e4218c210db949308436d524c210f9085308435e530c210d754c30842ee620c210bb588308436e520c210db54830842f6610c210bd58430843e4210c210db94b208436d52c8210f9087208436e5288210db54a20842f66188210bd58620843e42188210b7d8d20842dc6348210db949208436d5248210bdd8520842f46148210f9085208436e5208210db54820842f66108210bd58420843e42108210fa480208436e52c4210db54b10843e621c4210f908710842f565c4210dd59710842f662c4210bd18b10843e652c4210f954b10842f965c4210de597108437a53c4210de14f10843ea52c4210fa54b10843ea21c4210fa087108427e64d4d109f593534427e62d4d109f58b534435f54d4d10e7d53534431f54d4d10d7d93534435e64d4d10d7593534435c64d4
  | 5 => 0x31c42bc644c710bbd8931c42ec624c710be18131c42be640c710af59031c435e530c710d754c31c42fa600c710be58031c436e5288710db54a21c42fa6088710be58221c436e6588710db59621c436f5388710db94e21c436d5388710db14e21c43ea6088710fa58221c436e5208710db54821c42fa6008710be58021c436e6508710db59421c436f5308710db94c21c436d5308710db14c21c43e66108710fa98021c43e96008710af99330c42bd64cc310d794f30c435d53cc310bd98730c42f561cc310be59730c437965cc310be99330c43ba64cc310ae99330c43b964cc310be19330c437b53cc310f694f30c437953cc310f654f30c43f261cc310be58730c43f161cc310fa88730c43e821cc310d7d4e30c435c538c310d794d30c435d534c310bdd8530c42f4614c310d7d4c30c435c530c310bb98830c42ed620c310f64c030c42f9650c310de59430c42fa640c310be19030c43da630c310ded4c30c43db530c310de54c30c43d8530c310f690c30c43d9430c310fa98830c43e9620c310f68c830c43d8320c310be58430c43da310c310f60c430c43ea210c310fa08430c436e52c8310db54b20c42f661c8310bd58720c436f5288310db14a20c42df6348310b718d20c436e5248310db54920c42f76148310bd18520c436f5208310db14820c42be64d4e10af59353842ee62d4e10bb58b538427e64d4e10cf993538423e64d4e109f593538433d64d4e108f593538427e62d4e10db98b538426e62d4e109f58b538436d62d4e109b58b538437561d4e10de98353842be6494e10af592538435f5394e109f992538433e6494e108f992538427d6494e10cf592538423d6494e109f98a538427d6294e109fd91538427c6454e10d7d8d538427f6254e109f189538435d5314e10bb98853842ed6214e109f990538427d6414e10d798c538427e6214e10db988538426e6214e109f588538436d6214e109b58853843756114e10de980538427f6590e109f996438427d6590e109f196438433e5490e10cf552438435f5390e10d714e438427f6550e109f995438427d6550e109f195438435f5350e10d714d43842f76150e10bd185438427f6510e109f994438427d6510e109f194438435e5310e10d754c438439d4310e109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6394a109f58e528436f5394a10db94e528436d5394a10db14e52843e76194a10dbd8e528436e6394a10db58e528436c6394a10db90e528436d4394a10db10e528436f6194a10db586528436e6094a10db182528427f6354a109f18d528436f6254a10ddd85528436f6554a10dbd4d528436e5354a10db54d528436c5354a10f9d85528436f6354a10db98d528436d6354a10db18d528436e4354a10db50d528436c4354a10dbd8552843676154a10d
  | 6 => 0x36d6588420dbd4e210836e5388420db54e210836c5388420bb986210836d5188420bb582210827f6548420db94821083765108420dd54421083e52108420be98021082f96008420dbd4c210836e5308420db54c210836c5308420bb98421083e66108420db94421083e65108420d9944210836d5108420f954421083ea6008420bb58021083e96008420ba580210827e63940209f58e500836e2194020db086500827d65cc020af99330082bd64cc0209fd96300827d658c020d794e300835d538c020bb98a30082ed628c0209fd95300827f650c0209f994300827d650c0209f194300835e530c020d754c30082ee620c020bb588300836f53c8020db54f20082ee61c8020db94720082ed6288020db94a20082f96288020de94a20083ea5288020fa88620083e821880209fd9520082df6348020b718d20082f76148020bd18520082ef6548020dbd95200826f6548020f3d8d20083cc6348020dbd4d200836d5348020f9d8520082ec6148020f918520082e46148020db94520082ef6048020db94120083eb3048020fa0c120082fb6548020ded95200827b6548020f6d8d20083d86348020bed8920083eb6248020de94920083ea5248020facc920083e83248020fcd8520083f06148020fac8520083e921480209f99353c427d64d4f109f98b53c427d62d4f10dd98753c437960d4f10d7d4e53c42ee6294f10bb58a53c427e6494f109f59253c427e6294f10db98a53c426e6294f109f58a53c436d6294f109b58a53c427f6454f109f19153c435f6354f109fd8953c427c6254f10ded8153c42be6414f10af59053c435d5314f109f99053c433e6414f108f99053c427d6414f10cf59053c423d6414f10d798c53c427e6214f109f58853c43766114f10de58053c427f6590f109f99643c427d6590f109f19643c435e5390f10d754e43c42fa6090f10be58243c427f6550f109f99543c427d6550f109f19543c435e5350f10d754d43c42fb6050f10be18143c427f6510f109f99443c427d6510f109f19443c439d4310f10bd98443c42f56110f10b798f52c42dd63d4b109f98f52c435e63d4b109798f52c427d63d4b10d758f52c425d63d4b10dd98752c437960d4b10dbd4a52c427e6394b109f58e52c427f6354b109f18d52c436f6254b10db54852c427e6314b109f58c52c436e6214b10dd98452c43796014b109fd9732c427e65ccb109f59732c427c65ccb109fd9632c427e658cb109f59632c427c658cb10d794e32c435d538cb10dbd4a32c436c528cb10be98232c42f9608cb109fd9532c427e654cb109f59532c427c654cb10dbd4932c436c524cb10bed8132c42f8604cb109fd9432c427e650cb109f59432c427c650cb10d794c32c435d530cb10bb98b31c42ed62cc710d794e31c435d538c710be98231c42f9608c710afd91
  | 7 => 0x348520d714d21483775148520dd14521482fb6048520be181214827e6508520d7d4c214835c5308520ddd4421482ee6508520db99421482ef6308520bb58c214836f5308520f3d4c214834f5308520db94c214836d5308520db14c21483cc5308520d314c21482ee6108520f9984214836f5108520f9d4421483675108520f914421482ee60085209f99730482be64cc120af593304833f54cc120cf153304835f53cc120d714f30482ee62cc120bb58b304837751cc120dd147304827e658c120cfd52304833c548c120d7d4e304835c538c120f38ca3048377518c120dd146304827f654c1209f595304827c654c120cfd51304833c544c120d7d4d304835c534c120bbd8930482ec624c120ddd453048374514c1209f994304833f540c120cf150304835f530c120d714c30482ee620c120bb58830483ce320c120ddd443048374510c120f64c0304835f53c8120d714f204837751c8120dd14720483db53c8120f614f20483ea32c8120fa4cb20483f351c8120fc14720483ea21c8120fa087204835f5388120d714e20483775188120dd14620482ef6388120bb58e20483cf5388120f314e20482ee6188120f9d46204836c5188120f914620483645188120fad4220482be64d4c20af593530827e64d4c20cf993530823e64d4c209f593530833d64d4c208f593530827e62d4c20db98b530827e61d4c209f587530827e60d4c20de983530827d6594c20d7d4e530827e6494c209f592530827e6194c209f586530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20d754c530827e6414c209f590530827e6314c20d798c530827e6214c20db988530826e6214c209f984530827d6114c209f980530837a6014c209fd96430827e6590c209f596430827c6590c20cf952430833d5490c209fd95430827e6550c209f595430827c6550c20bbd8943082ec6250c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c20d794c430835d5310c20e750c430827e63948209f58e520827d65cc8209fd96320827d658c820d794e320835d538c820db94a32082fa608c820be582320827f654c820db949320827f650c8209f594320835e530c820d754c32082fa600c820be580320837751944209f98e510827d6394420db18a510827f63544209f18d51082de6314420b758c510837551144209fd97310827e65cc4209f597310835e53cc420d754f31082ee62cc420bb58b310827f658c4209f996310827d658c4209fd95310827d654c4209f19531082bf644c420af191310835e534c420d754d31082ef624c420bb18931082fb604c420be181310827f650c4209f994310827d650c420af99031082bd640c420dd947210837551c8420be98321082f960c84209f596210836e5288420bb5962108
  | 8 => 0x20e750c43482ee6210d20bb588434827e65cc920cfd53324833c54cc920d7d4f324835c53cc920be98332482f960cc9209f996324833f548c920cf152324835f538c920d714e32482ee658c920db99632482ef648c920bb59232483af548c920eb15232482ed638c920f3d4e324836e538c920db14e32483cc538c920d314e32482ee618c920bb982324827c654c920cfd51324833c544c920d7d4d324835c534c920bed8132482f8604c920db195324826c654c920bbd9132482ed644c920ebd5132483ac544c920f3d8d32483cf534c920db94d324836c534c920f314d32482ec614c920fad8132482ec604c920fa18132482e8604c9209f994324833f540c920cf150324835f530c920d714c32482ee620c920d7d4f514835c53d45209f98f514827d63d4520ddd4f51483d753d4520d5d4f514837653d4520dd54f514837453d4520f514f514835453d4520f958b51483e632d4520f94cb514837763d4520dd98f514837563d4520dd18f514837643d4520dd50f514837443d4520ddd8b514837732d4520dd8cb514837532d4520dd0cb514837760d4520dd58351482de6394520b758e514835f5394520d714e51483775194520b7d8d51482dc6354520d7d4d514835c5354520d7d4c514835c5314520dd544514827e63145209f58c514836f6214520db8c8514836d3214520bd99451483766514520ddd4c51483d75314520d5d4c51483765314520dd54c51483745314520f514c51483545314520f9d8851483e63214520f94c851483776314520dd98c51483756314520dd18c51483764314520dd50c51483744314520ddd8851483676214520ddcc851483763214520d98c851483753214520d94c851483743214520ddd8051483756014520dd480514827e65cc5209f597314827c65cc520cfd53314833c54cc520d7d4f314835c53cc520bb98b31482ed62cc520ddd47314837451cc5209f996314827d658c5209f196314833f548c520cf152314835f538c520d714e3148377518c520dd146314827f654c5209f995314827c654c520afd9131482bc644c520cfd51314833c544c520d7d4d314835c534c520bbd8931482ec624c520ddd453148374514c520bed8131482f8604c5209f994314827d650c5209f19431482be640c520af590314833f540c520cf150314835f530c520d714c31482ee620c520bb5883148377510c520dd14431482fa600c520be580314827e65c8520d7d4f214835c53c8520dd147214835f5388520d714e21483775188520dd14621482fa6088520be58221482ef6388520bb58e214836f5388520f3d4e214834f5388520db94e214836d5388520db14e21483cc5388520d314e21482ee6188520dbd4621483e75188520db14621483e45188520d914621482ee6088520fa98221482ea6088520fa582214835f5
  | 9 => 0x14e328835e534ca20d754d32882fb604ca20be181328835f530ca20d714c328837751946209f98e518827d6394620dbd8a518827f63546209f18d518837551146209fd97318827e65cc6209f59731882ee62cc620bb58b318827f658c6209f996318827d658c6209fd95318827d654c6209f19531882bf644c620af19131882ef624c620bb18931882fb604c620be181318827f650c6209f994318827d650c620af99031882bd640c620be98031882f9600c620dd94621883755188620be98221882f96088620dbd4e218836e5388620db54e218836c5388620db94621883e65188620d9946218836d5188620f954621883ea6088620bb58221883e96088620dd94521883755148620bed8121882f86048620f948421882ed6508620db594218836f5308620db94c218836d5308620db14c21883e66108620f9d44218836d5108620f914421882ed6008620af99330882bd64cc220d794e308835d538c220bb98a30882ed628c220d794c308835d530c220bb98830882ed620c220f64c030882ed65c8220db597208836f53c8220db54f20882ee61c8220db94720882f965c8220de597208827e64d4d209f593534827e61d4d209f587534835f54d4d20e7d53534831f54d4d20f3d8b534835f64d4d20d7993534835d64d4d20d7193534835f62d4d20d758b534835f61d4d20d7987534835d61d4d20d7187534835f60d4d20d758353482be6494d20af592534833f5494d20d7d4e53482f66194d20bd586534827e6494d20cf992534823e6494d209f592534833d6494d208f592534827e6394d209798e534827d6294d20db58a534827e6194d20dd98653482766194d209f58653483756194d209d586534827d6094d20de58253482bf6454d20af191534833f5454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20cfd50534835d5314d209f990534827d6414d20d798c534827e6214d20db588534827c6214d209f984534827d6114d20b7994534835e6514d2097994534835f5414d20e7d50534831f5414d20d7950534835d5414d20d7150534839c5414d20c715053483cd6214d20d7d90534835e6414d20d7590534835c6414d20d7d88534835d6214d20d3588534835f6114d20d7984534835d6114d20d7184534835f6014d20d7580534835d2014d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d20d7d4e434835c5390d20bb98a43482ed6290d20be98243482f96090d209fd95434827e6550d209f595434827c6550d20d7d4d434835c5350d209fd94434827e6510d209f594434827c6510d20d7d4c434835c5310d
  | 10 => 0x3c827d61d4f20de58353c835f5394f209f99253c827d6494f20db98a53c827e6194f209f58653c827f6454f209f19153c835f6354f209fd8553c827c6154f20af99053c82bd6414f20d754c53c827e6414f20cf99053c823e6414f209f59053c833d6414f208f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9643c827e6590f209f59643c827c6590f20d794e43c835d5390f20bb98a43c82ed6290f209fd9543c827e6550f209f59543c827c6550f20d794d43c835d5350f20bed8143c82f86050f209fd9443c827e6510f209f59443c827c6510f20e750c43c82ee6210f20bb58843c835e538cb20d754e32c82fa608cb20be58232c836d658cb20bbd9232c82ed648cb20db94e32c83ce538cb20f354e32c836c538cb20bb98632c82ee608cb20fa98232c83e9608cb20bbd9532c836f654cb20bbd9132c82ed644cb20f3d8d32c836e534cb20db14d32c82ec614cb20bb18132c835e530cb20d754c32c82fa600cb20be58032c82de63d4720b758f51c837751947209f98e51c827d6394720db18a51c836e3294720db4ca51c827f63547209f18d51c837551147209fd9731c827e65cc7209f59731c82ee62cc720bb58b31c827f658c7209f99631c827d658c720d794e31c835d538c7209fd9531c827d654c7209f19531c82bf644c720af19131c82ef624c720bb18931c82fb604c720be18131c827f650c7209f99431c827d650c720af99031c82bd640c720d794c31c835d530c720bb98831c82ed620c720dd94721c837551c8720be98321c82f960c8720bb59621c836d6588720bbd8e21c82ed6388720dbd4e21c836e5388720db54e21c836c5388720db54621c82ee6088720dd94421c83755108720be98021c82f96008720bbd8c21c82ed6308720dbd4c21c836e5308720db54c21c836c5308720f998421c836e5108720f994421c83665108720db54421c83e55108720d954421c82ee6008720fa98021c83e96008720af99330c82bd64cc320d794f30c835d53cc320bb98b30c82ed62cc320d7d4e30c835c538c320f38ca30c835e534c320d754d30c82ef624c320bb18930c835f530c320d714c30c82ee620c320bb58830c83ce320c3209f993538827d64d4e20db58b538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd96438827e6590e209f596438827c6590e20be98243882f96090e209fd95438827e6550e209f595438827c6550e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20e750c438835e53cca20d754f32882fa60cca20be583328835f538ca20d7
  | 11 => 0xfb604c430af990310c2bd640c430db948310c36d520c430dd944310c375510c430be980310c2f9600c430b7d90310c39e640c430b7590310c39d640c430a7590310c35e540c430d7150310c2de620c430f3948310c3cd520c430b7984310c3d6610c430f5944310c35d510c430f5544310c3da600c430b7580310c3d9600c4309fd97210c27e65c84309f597210c2de63c8430b758f210c36e52c8430db54b210c2fa60c8430be583210c27f65884309f996210c27d6588430b798e210c2dd6388430db94a210c36d5288430f38ca210c3cc3288430bbd96210c36f65884309bd96210c36e6588430bb596210c36d65884309b596210c36c6588430dbd52210c36e5488430db552210c36c5488430f398e210c3cd6388430db94e210c3ce4388430f350e210c2ee6188430db946210c36d5188430f38c6210c3cc31884309fd95210c27d65484309f195210c2df6348430b718d210c36e5248430db549210c2fb6048430be181210c27f65084309f994210c27d6508430b7d8c210c2dc6308430db948210c36d5208430f38c8210c3cc3208430bbd94210c36f65084309bd94210c36e6508430bb594210c36d65084309b594210c36c6508430dbd50210c36e5408430db550210c36c5408430f3d8c210c3cc6308430db94c210c3ce4308430f350c210c2ee6108430f9984210c36e5108430db544210c3ce3108430f30c4210c27e64940309f592500c35e4394030d750e500c35e3294030d70ca500c35e3194030d70c6500c36e2194030db086500c27d65d0030b798f400c2dd63d0030db94b400c36d52d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030e750e400c36e5290030db54a400c27f6550030db949400c36d52500309f994400c27d65100309f194400c2de6310030b758c400c39d4310030db948400c36d5210030af993300c2bd64cc030db94b300c36d52cc030b7d93300c39e64cc030b7593300c39d64cc030a7593300c2de62cc030f394b300c3cd52cc030b7987300c3ce21cc030f3087300c2dd638c030d794e300c36e528c030db54a300c2f9638c030de94e300c3da538c030f690e300c3d9438c030fa94a300c3e9528c030f68ca300c3d8328c030be986300c3da318c030f60c6300c3ea218c030fa086300c27f654c030db949300c36d524c030b7d95300c35f654c03097d95300c2df644c030b7591300c2dc624c030f3949300c3cd524c030b7185300c3ce214c030f3085300c2df604c030d7941300c3db404c030f6101300c2fb654c030ded95300c27b654c030bed8d300c3db634c030de94d300c3da534c030f6d0d300c3d8434c030fa949300c3e9524c030f6cc9300c3d9324c030be185300c3da314c030f60c5300c3ea214c030fa085300c27e64d4f209f59353c836e62d4f209f9875
  | 12 => 0x548309f185520c36f6554830dbd51520c36e5454830db551520c36c5454830f318d520c3ce4354830f350d520c2ec6154830dbd91520c36e6454830db591520c36c6454830db98d520c36f4354830db90d520c36d4354830db10d520c36f6154830db985520c36d6154830db185520c26c6154830db981520c36c6054830db0c1520c2ee6214830db548520c27f65d08309f997420c27d65d0830b798f420c2dd63d0830db94b420c36d52d08309fd96420c27e65908309f596420c36e5290830db54a420c27f65508309f595420c27c6550830b7d8d420c2dc6350830db949420c36d5250830bed81420c2f860508309fd94420c27e65108309f594420c2de6310830b758c420c36e5210830db548420c2fa6010830be580420c36e52cc830db54b320c2fa60cc830be583320c27d658c830db54a320c2dd658c830d7596320c2df648c830b7592320c2de628c830f394a320c35d528c830f354a320c34d528c830b7986320c2dd608c8309fd95320c36e524c830db948320c36d520c830be980320c2f9600c830b7d90320c2dd640c830b7988320c3ce620c830f3948320c35d520c830f3548320c2de610c830f6980320c2dd600c830f6580320c2d9600c830bb98b510c2ed62d4430db94b510c36d52d4430db94a510c36d5294430ddd46510c27e64944309f592510c36f62944309f98a510c27d6294430db18a510c2bf6454430af191510c2ef6254430bb189510c36e5254430db549510c27f6454430cfd91510c23f64544309f191510c33c64544308f191510c35e4354430d750d510c27f6254430dbd89510c26f62544309f189510c36c62544309b189510c3786054430af990510c2bd6414430bb988510c2ed6214430db948510c36d5214430dd544510c27f65d04309f997410c27d65d0430cf953410c33d54d0430b798f410c2dd63d0430e750f410c2ee62d0430bb58b410c36e52d0430db54b410c2fa60d0430be583410c27f65904309f996410c27d6590430cfd52410c39e4390430db94a410c36d5290430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c39d4350430bbd89410c2ec6250430db949410c36d5250430dd945410c3755150430bed81410c2f860504309fd94410c27e65104309f594410c33f5410430b798c410c2dd6310430e790c410c36e5210430db548410c2ee62cc430bb58b310c36e52cc430db54b310c37651cc430dd547310c2fa60cc430be583310c27d658c430db94a310c36d528c430b7596310c35d658c430b7d92310c2dd648c430d7952310c35c548c430b798a310c3ce528c430f354a310c2de618c430d7546310c3db608c430b7582310c3d8608c4309fd95310c2bf644c430af191310c2ef624c430bb189310c36e524c430db549310c2
  | 13 => 0xbe582314c2bf644c530af191314c2ef624c530bb189314c377514c530dd145314c2fb604c530be181314c27e650c530af990314c2bd640c5309f997214c27d65c85309f197214c37751c8530dd147214c27e65885309f596214c27c6588530dbd4a214c36c5288530dbd96214c36e6588530db596214c36c6588530dbd52214c36e5488530db552214c36c5488530bb986214c36f5188530db146214c27f65485309f995214c27c65485309f994214c27d65085309f194214c2de6308530b758c214c36f5208530db148214c3775108530dd144214c2fa6008530be580214c36f6508530db994214c36d6508530db194214c36f5408530db950214c36d5408530db150214c3ce6308530f358c214c2ee6108530f9984214c36f5108530f9d44214c3675108530db144214c3e45108530d9144214c3ea6008530fa580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130cf952404c27d65501309f195404c2df6350130b718d404c2be64cc130af593304c3ba64cc130ee593304c37851cc130fa887304c3e821cc130d7d52304c35d548c130d714a304c35c518c130f3886304c3cc218c130f6d42304c2ee62d5030bb58b540c35e63d50309f98b540c36e62d50309b98b540c27d62d5030db58b540c26d62d50309f987540c27d61d5030de983540c27d6595030cfd52540c35e63950309f98a540c27d62950309f986540c27d6195030cfd91540c27f63550309f58d540c27f62550309f189540c27f61550309f185540c33d5415030bb988540c2ed6215030bd984540c2f561150309f98c540c35e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a6015030cf992530c27d6494c30cf592530c23d6494c309f597430c33f54d0c309fd96430c27d6590c30cf952430c33d5490c30be982430c2f96090c30d7596430c25d6590c30b7592430c35e5490c30e7952430c39d5490c30d7152430c2de6290c30b7986430c3da6090c30b7582430c3d96090c30b6582430c27f6550c30cfd51430c2df6550c30d7d95430c39f6450c30e7d51430c35e5450c30d7151430c39c5450c30c7151430c2dc6250c30b7185430c2df6050c309fd94430c27d6510c30cf950430c33d5410c30b798c430c39d4310c30be980430c2f96010c30dbd4a520c27e64948309f592520c27e61948309f586520c36f5494830db952520c36d5494830db152520c3cc6394830f390e520c3cd4394830bb986520c36f6494830db992520c36d6494830db192520c36c6394830dbd0e520c36e4394830db50e520c36c4394830dbd86520c36e61948309b986520c36d6194830db186520c36e6094830db182520c27f64548309f191520c27f61
  | 14 => 0xe218c36e5188630db546218c3ce3188630f30c6218c27f65486309f595218c27c6548630b7d8d218c2dc63486309fd94218c27e65086309f594218c2df6308630b718c218c36e5208630db548218c3ce3208630f30c8218c2fa6008630be580218c36f6508630db994218c36d6508630db194218c36f5408630db950218c36d5408630f3d8c218c3cc6308630f390c218c3cd4308630f9984218c36e5108630db544218c3ce3108630f30c4218c3ea6008630fa580218c2de63d0230b758f408c2de6390230b758e408c39d4390230af993308c2bd64cc230b7597308c35d65cc230e7993308c2dd64cc230e7593308c29d64cc230b798b308c2de61cc230f3887308c3cc21cc230be597308c37965cc230ee993308c3b964cc230de947308c3ea21cc230fa087308c27e62d51309f58b544c27e61d51309f587544c33f5495130d758e544c27e62951309f58a544c27e61951309f586544c3796095130bbd89544c2ec6255130bdd85544c2f46155130d7d8d544c27f6255130dbd89544c26f62551309f189544c36c62551309b189544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27e6515130cf550544c33e64151309f18c544c27e62151309f588544c27e61151309f584544c33f54d0d30cf153434c2fa60d0d30be583434c27e6590d30cfd51434c33c5450d30bed81434c2f86050d309f994434c39d4310d309f993524c27d64d49309f987524c27d61d4930dbd4a524c2bf6454930af191524c2f76154930bd185524c36d52149309f990524c27d64149309f984524c27d61149309f997424c27d65d09309f197424c36f52d0930db14b424c27e65909309f596424c27c6590930cfd52424c33c5490930b798e424c2dd6390930be982424c2f960909309fd95424c27e65509309f195424c27e65109309f594424c27c6510930cfd50424c33c5410930dbd48424c36c52109309f997324c36f528c930db14a324c2fa608c930be582324c36f524c930db149324c2fb604c930be181324c27e650c930bb98b514c2ed62d45309f993514c27d64d45309f98b514c36e62d45309b98b514c27d62d4530db58b514c26d62d4530ddd46514c2bf6454530af191514c2ef6254530bb189514c37551145309f990514c27d64145309f988514c27d62145309f997414c27d65d05309f197414c2ee62d0530bb58b414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c54905309fd95414c27e65505309f195414c2df6350530b718d414c2ef6250530bb189414c2fb6050530be181414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530ddd44414c37451105309f997314c2ee62cc530bb58b314c377518c530dd146314c2fa608c53
  | 15 => 0x8c33f64552309fd89548c27c62552309fd85548c27c6155230cf550548c2ee6215230bb588548c33e54d0e30cf553438c2fa60d0e30be583438c2dd6590e30d7596438c35e5490e30b798a438c2de6190e30b7582438c33e5450e30cf551438c2fb6050e30be181438c35f6550e30e7d91438c35e5450e30e7951438c31e5450e30e7551438c2dc6250e30b7185438c2df6050e30f6d81438c3d86050e30e750c438c36f5294a309f992528c27d6494a309f986528c27d6194a309fd91528c27c6454a309fd85528c27c6154a30af990528c2bd6414a30db548528c27f65d0a309f997428c27d65d0a30cf953428c33d54d0a30b798f428c2dd63d0a309fd96428c27e6590a309f596428c36e5290a30db54a428c2fa6090a30be582428c27f6550a309f595428c27c6550a30cf951428c33d5450a30b7d8d428c2dc6350a30db949428c36d5250a309fd94428c27e6510a309f594428c2de6310a30b758c428c36e528ca30db54a328c2fa608ca30be582328c2df648ca30b7592328c3ce528ca30d754a328c3cd528ca30b7986328c3da608ca30b7582328c3d9608ca30db949328c36d524ca30bed81328c2f8604ca30b7594328c35d650ca30b7d90328c2dd640ca30f3988328c35d520ca30b7984328c2dd600ca30af993518c2bd64d4630bb98b518c2ed62d4630ddd46518c27e64946309f592518c27e62946309f58a518c2ef6254630bb189518c27f64546309f191518c35e4354630d750d518c27f6254630dbd89518c26f62546309f189518c36c62546309b189518c37551146309fd97418c27e65d06309f597418c2de63d0630b758f418c39d43d0630bb98b418c2ed62d06309fd96418c27e65906309f596418c33e5490630cf552418c39e43906309fd95418c27d65506309f195418c2df6350630b718d418c39d4350630bbd89418c2ec6250630bed81418c2f860506309fd94418c27e65106309f594418c33e5410630cf550418c2de6310630b758c418c39e4310630bb98b318c2ed62cc630dd946318c375518c630be982318c2f9608c630b7d92318c2dd648c630d7952318c2de628c630f5946318c35d518c630f5546318c3da608c630b7582318c3d9608c630afd91318c2bc644c630bbd89318c2ec624c630dd945318c375514c630bed81318c2f8604c630af990318c2bd640c630b7594318c35d650c630b7d90318c39e640c630b7590318c39d640c630a7590318c35e540c630b7988318c3d6610c630d7544318c2dd600c6309fd97218c27e65c86309f597218c2de63c8630b758f218c27f65886309f996218c27d6588630b798e218c2dd6388630db94a218c36d5288630f38ca218c3cc3288630dbd96218c36e6588630db596218c36c6588630dbd52218c36e5488630db552218c3ce6388630f358e218c3ce4388630f35
  | 16 => 0xc6154b30af99052cc2bd6414b30cf95052cc33d5414b30db54852cc27f65d0b309f99742cc27d65d0b30cf95342cc33d54d0b309fd9642cc27e6590b309f59642cc33e5490b30cf55242cc2de6390b30b758e42cc27f6550b309f59542cc27c6550b30cf95142cc33d5450b30bed8142cc2f86050b309fd9442cc27e6510b309f59442cc33e5410b30cf55042cc2fa6010b30be58042cc33e54ccb30cf55332cc36e52ccb30db54b32cc2fa60ccb30be58332cc33e548cb30cf55232cc33e544cb30cf55132cc33e540cb30cf55032cc36e520cb30db54832cc2fa600cb30be58032cc2be64d4730af59351cc33e54d4730cf55351cc2ee62d4730bb58b51cc33e5494730cf55251cc37751947309f99251cc27d64947309f98a51cc27d6294730cf95151cc33d5454730bbd8951cc2ec62547309fd9151cc27c64547309fd8951cc36f62547309bd8951cc27c6254730db18951cc26c6254730ded8151cc2be6414730af59051cc33e5414730cf55051cc37551147309fd9741cc27e65d07309f59741cc33e54d0730cf55341cc2ee62d0730bb58b41cc2fa60d0730be58341cc27f65907309f99641cc27d6590730cf95241cc33d54907309fd9541cc27d65507309f19541cc33e5450730cf55141cc2df6350730b718d41cc2ef6250730bb18941cc2fb6050730be18141cc27f65107309f99441cc27d6510730cf95041cc33d5410730b798c41cc2dd6310730cf95331cc33d54cc730bb98b31cc2ed62cc730dd94731cc37551cc730be98331cc2f960cc730cf95231cc33d548c730afd9131cc2bc644c730cf95131cc33d544c730bbd8931cc2ec624c730be18131cc2be640c730af59031cc33e540c730cf55031cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730cf95321cc33d54c8730dd94721cc37551c8730be98321cc2f960c87309fd9621cc27e65887309f59621cc33e5488730cf55221cc36e5288730db54a21cc36f6588730db99621cc36d6588730db19621cc36e5488730eb95221cc32e5488730db55221cc3ad5488730cb55221cc36c5488730db94621cc36d51887309fd9521cc27d65487309f19521cc33e5448730cf55121cc2fb6048730be18121cc27f65087309f99421cc27d6508730cf95021cc33d5408730b798c21cc2dd6308730db94821cc36d5208730dd94421cc3755108730dbd9421cc36e6508730db59421cc36c6508730db95021cc3ae5408730cb95021cc36d5408730eb55021cc32d5408730db15021cc3ce6308730f358c21cc3e66108730db94421cc3e65108730d994421cc36d5108730f954421cc3655108730b798f40cc2dd63d03309f98b548c27d62d52309f987548c27d61d5230de983548c33f5495230d758e548c27e62952309f58a548c27e61952309f58654
  | 17 => 0x4421db10e51087666194421db982510876d6094421f959651087e76394421f998e51087e56394421f918e51087e75394421f994e51087e55394421f914e51087e64394421f950e51087e44394421f9d8251087e66094421b998251087e56094421f918251086ed65cc421db597310866d65cc421bb99331086ed64cc421bb19331087ce43cc421f350f310876e51cc421f994731087e741cc421bb98331086ed60cc421bbd9631086ed658c421bbd9231086ee648c421bb59231086ed638c421f394e31087cd538c421f3d0e31087cc438c421bb986310876e518c421f994631087e6418c421f3cc631087e7318c421bb98231086ed608c421bbd95310876f654c4219bd9531086ef644c421ebd9131086af644c421bb99131086ed644c421bb19131087ac644c421ab19131087ce434c421f350d310876e514c421f994531087e6414c421f950531087e7314c421f38c531086ef604c421fad8131086eb604c421bb18131087e8604c421ba18131086ef650c421bb99431086ed650c421bb19431086ef640c421bb99031087ae640c421ab99031086ed640c421eb59031086ad640c421bb19031086ee630c421f394c31087cd530c421f3d0c31087cc430c421bb984310876e510c421f994431087e7410c421f910431087cf310c421f98c431087cd310c421f94c431087c5310c421bb98031086ed600c421bb98f50086ed63d4021dbd4f500876d53d4021f998750087e651d4021bb59650086ee6394021bb58e50087e46194021db94650087e65194021dbd4250087eb5094021bbd8d50087cf6354021b3d8d50086ec6354021f318d50086cc6354021dbd4d500876d5354021f9185500876e5154021f994550087eb5054021db94150086ee6314021f398c50086ce6314021bb58c50087cd6314021b358c50087e66114021f994450086ee6014021dbd4050087ea5014021db54050087e95014021da540500873f54953309f98a54cc27d62953309f98654cc27d6195330cf18e54cc33f6295330cf98a54cc33d6295330cf18a54cc33f6195330cf98654cc33d6195330cf18654cc33f6095330cf58254cc27f62553309f18954cc27f61553309f18554cc33f6555330cf98d54cc33f6255330cf98954cc33d6255330cf18954cc33f6155330cf98554cc33d6155330cf18554cc33f6055330cf58154cc33d5415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cf55343cc33e5490f30cf55243cc2fa6090f30be58243cc33e5450f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc2be64d4b30af59352cc33e54d4b30cf55352cc2f661d4b30bd58752cc33e5494b30cf55252cc36f5294b309f99252cc27d6494b309f98652cc27d6194b30cf95152cc33d5454b309fd9152cc27c6454b309fd8552cc27
  | 18 => 0xbb99132086ed644c821bb19132087cf634c821db94d320876c534c821bbd8532086ef604c821bb181320867f650c8219f594320875e530c821d754c32086ee620c821bd98432086f5610c821db594320866d650c821bbd9032086ee640c821bb59032086ec640c821bb98c32087ce630c821dbd4c32087ce530c821db54c32087cd530c821f998432086ed610c821f958432086ee600c821bb580320867e63944219f58e510876f3294421db8ca510876d3294421db0ca510867d65cc421bb98b31086ed62cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c4219fd9531086bf644c421af19131086ef624c421bb18931086fb604c421be181310867f650c4219f994310867d650c4219f19431086be640c421af590310875e530c421d754c31086ee620c421bb58831087d5310c421bbd8f21086ee63c8421bb58f21086ec63c8421bb98321086ed60c8421bb58a210876e5288421bd58a21087765288421f994a21087e73288421f98ca21087e53288421f90ca21086f660884219fd9521086ef6548421dbd95210866f6548421bbd8d21086ee6348421bb58d21086ec6348421bbd85210876e5148421bbd8121086ec6048421bdd95210877765484219dd9521086f76248421f9d8921087765248421f994921086f46048421ded42500867e63940219f58e50086df6354021b718d500867f6354021d7d8d500865f63540219f18d500875c63540219718d500876e3254021db4c950086de6314021b758c50087795014021bb99353086ed64d4c21bb98753087e661d4c21b998753086ee60d4c21bb58353086ed6594c21bb99253086ed6494c21dbd4e53087cf5394c21bb98253086ed6094c21bbd9153086ec6454c21f3d4d530876e5354c21bbd8153086ec6054c21bb99053087ae6414c21ab99053086ed6414c21eb59053086ad6414c21bb98c530876f5314c21f394c530876d5314c21f354c53086ee6114c21f998453086e66114c21bb98053087ea6014c21ba98053086ed6014c21fa58053086e96014c21bbd9643086ee6590c21bb59643086ec6590c21bb59243086ee6390c21f394e43087cd5390c21f3d0e43086ee6190c21bb58643086ee6090c21bb58243086ef6550c21bb99543086ed6550c21bb19543087ce5350c21f354d43087ae4350c21bbd8543087e76150c21b9d8543086ec6150c21f918543086e46150c21bbd8143086ec6050c21bbd9443086ee6510c21bb59443086ec6510c21bb98c43087ce4310c21f350c430878d4310c21bb98443087e66110c21b998443086ed6110c21f958443086e56110c21bb98043086ed6010c21bb98e51086ed6394421dbd4e510876e5394421db54e510876c5394421bb98251086ed6094421dbd8e510876e6394421db58e510876c6394421db90e510876d439
  | 19 => 0x3534875f5394d219f992534867d6494d219f98e534867d6294d21db58a534866d6294d219f58653487756194d219f982534867d6094d21afd9153486bc6454d21bed8153486f86054d219fd91534873f6454d218fd91534867c6454d21cf191534863c6454d21d7d8d534867f6254d21dbd89534866f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f6590d219f996434867d6590d219f196434873f5490d21cf152434867f6550d219f995434867d6550d219f195434867f6510d219f994434867d6510d219f194434875f5310d21d714c434879d4310d219f997324875f53cc921d714f32486f661cc921bd587324867e658c9219f195324875f534c921d714d32486f7614c921bd185324867e650c9219f997314875f53cc521d714f31486ee62cc521bb58b314867e658c5219fd95314867d654c5219f19531486bf644c521af191314875f534c521d714d31486ef624c521bb18931486fb604c521be181314867e650c521af99031486bd640c521dbd4e214876e5388521db54e214876c5388521f9d46214867e63d41219f58f504876e21d4121ded4250486df6354121b718d504877950141219f98c504867d6314121ddc84504876e21141219f993530867d64d4c219f98b530876e62d4c219f987530877661d4c219f983530867d60d4c219f596530875f5394c219f992530867d6494c21db98a530867e6094c219f582530867f6454c219f191530875f6354c21db189530867f6054c219f18153086be6414c21af590530875d5314c21be98053086f96014c219f990530873e6414c218f990530867d6414c21cf590530863d6414c219f98c530875e6314c219f988530876e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd96430867e6590c219f596430867c6590c21d794e430875d5390c21bb98a43086ed6290c219fd95430867e6550c219f595430867c6550c21d794d430875d5350c21bbd8943086ec6250c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c21e750c43086ee6210c21bb58843086f66110c21bd584430867e63948219f58e520867d65cc821bb597320876d65cc821bb99332086ed64cc821bb193320876f53cc821db54f32086ed61cc821bb98332086ed60cc8219fd96320867d658c821d794e320875d538c821bb98a32086f6618c821bd586320876d658c8219b59632086ef648c821bb99232086ed648c821bb58e320876e538c821f394e32087cd538c821db14e32087e6618c821bb58632087e5618c821bb98232086ed608c8219fd9532086ef654c821dbd9532086ef644c821
  | 20 => 0x87cd534ca21db14d32886ef614ca21f9d8532887e4614ca21bbd8132886ec604ca21bb594328876d650ca21bbd9032886ee640ca21bb59032886ec640ca21f398c328876f530ca21db54c32886ed610ca21bb98032886ed600ca21bb98b31886ed62cc621d794e318875d538c621bb98a31886ed628c621afd9131886bc644c621bbd8931886ec624c621bed8131886f8604c621af99031886bd640c621d794c318875d530c621bb98831886ed620c621bb597218876d65c8621bbd8f21886ee63c8621bb58f21886ec63c8621bb98321886ed60c8621bd597218877565c8621b798f50886dd63d4221ded42508867e63942219f58e508877721942219fd8d508867c6354221db8c9508876d3254221de54050886ee64d4e21bb59353886ee61d4e21f998753886e661d4e21bb98353886ed60d4e21bb99253886ed6494e21dbd4e53887cf5394e21bb98253886ed6094e21bbd9153886ec6454e21f3d4d538876e5354e21bbd8153886ec6054e21bb99053887ae6414e21ab99053886ed6414e21eb59053886ad6414e21dbd4c53887ce5314e21db54c53887cd5314e21bb98453887e66114e21b998453886ee6014e21bb58053886ef6590e21bb99643886ed6590e21bb19643887ce5390e21f354e43887cf4390e21bb98643886ed6190e21bb98243886ed6090e21bbd9543886ee6550e21bb59543886ec6550e21f394d43887cd5350e21eb90d43886ef6150e21bb18543886ef6050e21bb18143886ef6510e21bb99443886ed6510e21bb19443887ce4310e21f350c438878d4310e21bb98443886ed6110e21bb98043886ed6010e21bb597318876d65cc621bb99331886ed64cc621bb19331887ce43cc621f350f31886ee60cc621bb58331886ed658c621bbd9231886ee648c621bb59231887ce538c621f354e31887cf438c621f310e31887cf318c621f9cc631886ee608c621bb58231886ef654c621dbd9531886ef644c621ebd9131886af644c621bb99131886ed644c621bb19131887ac644c621ab19131887ce434c621f350d31887e7314c621f38c531886ef604c621fad8131886eb604c621bb18131887e8604c621ba18131886ed650c621bbd9031886ee640c621eb99031886ae640c621bb59031887ad640c621ab59031886ec640c621f394c31887cd530c621f3d0c31887cc430c621f3cc431887e6310c621f34c431887e5310c621bb98031886ed600c621bb98f50887ce63d4221b398f50886ed63d4221f358f50886cd63d4221dbd4f508876d53d4221f998750886ee6394221bb58e508876f5094221fad42508876b5094221bbd8d50886ec6354221dbd4d508876d5354221fad41508876e5054221bb98c50886ed6314221f9984508876f5014221fa940508876d5014221fa540508867e64d4d219f593534867e60d4d219f58
  | 21 => 0x634c431f5d8d310c776534c431f594d310c7e7624c431f9189310c7d6324c431f50c9310c7f3604c431fc181310c6be64d4031af593500c73e54d4031cf553500c73e5494031cf552500c77b50940319f992500c67d64940319f98a500c67d6294031cf951500c73d54540319fd91500c67c64540319fd89500c67c6254031af990500c6bd6414031cf950500c73d5414031bb988500c6ed6214031de540500c6be64d4f21af59353c86fa60d4f21be58353c867e64d4f21cf99353c863e64d4f219f59353c873d64d4f218f59353c876e62d4f21dd58753c867e60d4f21de98353c867a60d4f219f58353c877960d4f219e58353c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c875d5314f219f99053c867d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f6590f219f99643c867d6590f219f19643c873e5490f21cf55243c867f6550f219f99543c867d6550f219f19543c86f76150f21bd18543c867f6510f219f99443c867d6510f219f19443c875e5310f21d754c43c879d4310f21bd98443c86f56110f21d794e32c875d538cb21bd98632c86f5618cb21d794c32c875d530cb21bd98432c86f5610cb21d794f31c875d53cc721bb98b31c86ed62cc721afd9131c86bc644c721d794d31c875d534c721bbd8931c86ec624c721bed8131c86f8604c721af99031c86bd640c721f54c431c86de63d4321b758f50c877b50943219f98e50c867d63943219fd8d50c867c6354321de54050c867e64d4e219f593538876d62d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e21db58a538867e6094e219f582538867f6454e219f191538875f6354e21dbd89538867f6054e219f18153886be6414e21af590538875d5314e219f990538873e6414e218f990538867d6414e21cf590538863d6414e21d798c538876d6214e21dd984538867e6014e219f580538867f6590e219f996438867d6590e219f196438875e5390e21d754e43886ee6290e21bb58a438867f6550e219f995438867d6550e219f195438875e5350e21d754d43886ef6250e21bb189438867f6510e219f994438867d6510e219f194438879d4310e21bb98843886ed6210e21d794f328875d53cca21bd98732886f561cca21db59732886ee64cca21bb59332886ec64cca21dbd4f32887ce53cca21db54f32887cd53cca21f998732886ed61cca21f958732886ee60cca21bb58332886ed658ca21db59632886ef648ca21bb99232886ed648ca21db94e328876c538ca21bb58632886ee608ca21bb582328875e534ca21d754d32886f7614ca21bd185328876f654ca21bbd9132886ee644ca21bb59132886ec644ca21f3d8d328876e534ca21f394d328
  | 22 => 0x319f984540c77661150319f980540c67d60150319f592530c76e6294c31db58a530c67d65d0c31cf953430c73d54d0c31b7597430c75d65d0c3197597430c75f54d0c31e7953430c75d54d0c31e7553430c71d54d0c31b7587430c6de60d0c319fd96430c67d6590c31cf952430c73d5490c31b798e430c75e5390c31bd986430c6f56190c319fd95430c73e5450c31cf551430c75e5350c319fd94430c67d6510c31cf950430c73d5410c31e750c430c6f66110c31bd584430c75d6510c3197594430c6de6410c31e7990430c75f5410c31e7950430c75d5410c31e7550430c71d5410c31f5984430c6dd6110c31f5584430c6de6010c31af993520c6bd64d4831cf953520c73d54d4831cf952520c73d5494831dbd4a520c67e64948319f592520c67e60948319f582520c73e5454831cf551520c67f64548319f191520c67f60548319f181520c6be6414831af590520c73e5414831cf550520c76d5214831be980520c6f960148319fd97420c67e65d08319f597420c73e54d0831cf553420c67f65908319f996420c67d6590831cf952420c73d5490831b798e420c6dd63908319fd95420c67d65508319f195420c73e5450831cf551420c6df6350831b718d420c6f76150831bd185420c67f65108319f994420c67d6510831cf950420c73d5410831cf953320c73d54cc831db94b320c76d52cc831bd987320c6f561cc8319f596320c73e548c831cf552320c67f654c831cf951320c73d544c831cf950320c73d540c831db948320c76d520c831bd984320c6f5610c8319f992510c67d6494431d7d0e510c75c43944319f597410c73e54d0431cf553410c79f43d0431bb98b410c6ed62d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd6390431e710e410c67f6550431cf951410c73d5450431b7d8d410c6dc6350431e7d0d410c6ef6250431bb189410c6fb6050431be181410c67e65104319f594410c67c6510431b798c410c6dd6310431e710c410c73e54cc431cf553310c6ee62cc431bb58b310c6de64cc431b7193310c75f54cc431e7953310c75d54cc431e7553310c71d54cc431f398b310c7cd62cc431b7983310c73e548c431cf552310c6dd638c431d794e310c7b6548c431ed552310c6f5638c431dd94e310c7d6538c431f5d0e310c7d4438c4319fd95310c6bf644c431af191310c73e544c431cf551310c6ef624c431bb189310c6fb604c431be181310c6df654c431d7d95310c65f654c431e7d91310c6de644c431b7191310c79c644c431a7191310c75f544c431e7951310c75d544c431e7551310c71d544c431f3d89310c7cc624c431b7d85310c75e514c431f6d81310c6dc604c431f6181310c6d8604c431bdd95310c777654c4319dd95310c7b7644c431ed191310c7b6544c431ed551310c6f7
  | 23 => 0xbd4b314c76c52cc531edd53314c7b454cc531f590f314c7d543cc531f998b314c7e562cc531f9d4b314c7e452cc531cfd52314c73c548c531dbd4a314c76c528c531b7d92314c6dd648c531e7d52314c75e548c531d7152314c79c548c531c7152314c7cf528c531f314a314c7d7518c531cfd53504c73c54d4131dbd4b504c76c52d41319f993504c67d64d41319f98b504c67d62d4131ded53504c7bb54d4131ced53504c77a54d4131de553504c77854d4131ee153504c73854d4131f690f504c7d943d4131ded4b504c7eb52d4131dad4b504c77a52d4131de54b504c77852d4131fa14b504c76852d4131fccc7504c7da31d4131ded93504c77a64d4131de593504c77864d4131ded8f504c77b43d4131de90f504c77943d4131de10f504c77b62d4131de98b504c77962d4131de18b504c77b42d4131de90b504c77942d4131de10b504c77b32d4131de8cb504c77932d4131de0cb504c77b61d4131ded07504c77a41d4131de507504c77b31d4131de8c7504c6be6494131af592504c73f5494131cf152504c6ee6294131bb58a504c76f5294131db14a504c77b5094131afd91504c6bc6454131cfd51504c73c5454131bbd89504c6ec6254131dbd49504c76c5254131cfd50504c73c5414131dbd48504c76c5214131de540504c67e64141319f590504c75e4314131d750c504c67e62141319f588504c75e3114131be994504c77a6514131ded50504c7bb5414131ced50504c77a5414131de550504c7785414131ee150504c7385414131f690c504c7d94314131ded48504c7eb5214131dad48504c77a5214131de548504c7785214131fa148504c7685214131fccc4504c7da3114131ded90504c77a6414131de590504c7786414131ded8c504c77b4314131de90c504c75a4314131de50c504c7594314131de10c504c77b6214131de988504c7796214131de188504c77b4214131de908504c7794214131de108504c77b3214131de8c8504c7793214131de0c8504c77b6114131ded04504c77a4114131de504504c77b3114131de8c4504c75a3114131de4c4504c75e63d50319f98b540c67d62d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c63d6595031e718e540c73e6395031cf18e540c73f6295031cf98a540c73d6295031cf18a540c73e6195031cf186540c73f6095031cf982540c73d6095031cf182540c73f6455031d718d540c67f62550319f189540c67f60550319f181540c73f6555031e718d540c73e6355031cf18d540c71c6355031cfd89540c73e6255031cf589540c73c6255031cf985540c73c6155031cf0c5540c73f6055031cf981540c73d6055031cf181540c6be6415031cf550540c67e6315031d798c540c65e63150319f988540c67d6215
  | 24 => 0x544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c6be6515131cf994544c63e6515131e758c544c73f6315131cfd88544c73e6215131cf588544c73c6215131cfd84544c73d6115131cf4c4544c73f6015131cf980544c73d6015131cf180544c73f54d0d31cf153434c6f661d0d31bd587434c67e6590d31cfd52434c73c5490d31b7996434c75e6590d3197996434c6dd6490d31e7d52434c75e5490d31d7152434c79c5490d31c7152434c6de6190d31cfd51434c73c5450d31bdd85434c6f46150d31e7d91434c79f5450d31d7951434c75c5450d31e7151434c71c5450d31f5d85434c6dc6150d31f5185434c67e6510d31cfd50434c6de6310d31e750c434c73f54d4931cf153524c67e64d49319f593524c67e60d49319f583524c76f54d4931ebd53524c72f54d4931db953524c76d54d4931db153524c7ac54d4931cb153524c7ce43d4931f350f524c76f64d4931db993524c76d64d4931db193524c76f63d4931dbd0f524c76e43d4931db50f524c76c43d4931dbd87524c76d61d4931dbd83524c76e60d4931db583524c76c60d4931af992524c6bd6494931cfd52524c73c5494931dbd4a524c6fa6094931be582524c6bf6454931af191524c73f5454931cf151524c6fb6054931be181524c73f5414931cf150524c76d52149319f990524c67d64149319f980524c67d6014931bb994524c76e6514931dbd50524c7af5414931cbd50524c76e5414931db550524c76c5414931eb150524c72c5414931f390c524c7cd4314931dbd90524c76e6414931db590524c76c6414931dbd8c524c76f4314931db90c524c76d4314931db10c524c76f6114931db584524c76d3114931dbd80524c76e6014931db580524c76c60149319f997424c67d65d09319f197424c73f54d0931cf153424c6de63d0931b758f424c76f52d0931db14b424c6f661d0931bd587424c67e65909319f596424c67c6590931cfd52424c73c5490931dbd4a424c76c52909319fd95424c67e65509319f195424c73f5450931cf151424c76f5250931db149424c67e65109319f594424c67c6510931cfd50424c73c5410931b798c424c6dd6310931dbd48424c76c52109319f997324c73f54cc931cf153324c76c52cc931cfd52324c73c548c931dbd4a324c76c528c931bd986324c6f5618c931cfd51324c73c544c931dbd49324c76c524c931bdd85324c6f4614c9319f994324c73f540c931cf150324c76f520c9319f997414c73f54d0531cf153414c6de63d0531b758f414c79d43d0531bb98b414c6ed62d0531dbd4b414c76c52d0531cfd52414c73c5490531e790e414c76f5290531db14a414c67d65505319f195414c6df6350531b718d414c79d4350531dbd49414c76c5250531cfd53314c73c54cc531bb98b314c6ed62cc531d
  | 25 => 0x6f561ccb31db54a32cc76e524cb31db94832cc76d520cb31bd98432cc6f5610cb31b798f41cc6dd63d0731e750f41cc76e52d0731db54b41cc6be64d4331af59350cc6ee62d4331bb58b50cc76e52d4331db54b50cc76e5294331db54a50cc77b50943319f99250cc67d6494331d790e50cc75d43943319f98a50cc67d6294331db94950cc76d52543319fd9150cc67c64543319fd8950cc67c6254331bb98850cc6ed6214331db94850cc76d5214331de54050cc67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f64552319fd89548c67c62552319fd81548c67c6055231cf550548c73e54d0e31cf553438c6f661d0e31bd587438c79e54d0e31d7553438c79d54d0e31f5987438c6dd61d0e31f5587438c6de60d0e31cfd52438c73e5450e31cf551438c6f76150e31bd185438c79d4310e31b7594438c75d6510e31e7990438c75f5410e31e7d50438c71f5410e31d7550438c79c5410e31b7584438c6de6010e31dbd4a528c67e6494a319f592528c67e6094a319f582528c67f6454a319f191528c67f6054a319f181528c76d5214a319fd97428c67e65d0a319f597428c6f661d0a31bd587428c67f6590a319f996428c67d6590a31b798e428c6dd6390a319fd95428c67d6550a319f195428c6df6350a31b718d428c67f6510a319f994428c67d6510a31db94a328c76d528ca31bd986328c6f5618ca31db949328c76d524ca31bdd85328c6f4614ca31e7d0f418c6ee62d0631bb58b418c6de6390631b758e418c79c4390631bb98b318c6ed62cc631b7597318c75d65cc631b7993318c6dc64cc631d7d53318c75d54cc631f398b318c7cd62cc631b7983318c6f565cc631dd597318c7e662cc631f958b318c6ee6294231bb58a508c77b50942319f992508c67d64942319f98a508c76e62942319b98a508c67d6294231db58a508c66d6294231afd91508c6bc64542319fd91508c73f64542318fd91508c67c6454231cf191508c63c64542319fd89508c67c6254231de540508c67e62d51319f58b544c67e60d51319f583544c79f63d5131cfd8f544c73d63d5131cfd8b544c73e62d5131cf58b544c73c62d5131cfd87544c73d61d5131cfd83544c73e60d5131cf583544c73c60d5131cfd52544c6ee6295131bb58a544c6fa6095131be582544c75d63951319f98a544c76e62951319b98a544c67d6295131db58a544c66d6295131dd586544c67e6095131de982544c67a60951319f582544c77960951319e582544c6ef6255131bb189544c6fb6055131be181544c75f63551319fd89544c76f62551319bd89544c67c6255131db189544c66c62551319fd85544c77761551319fd81544c77b60551319ed81544c67c6055131de181544c67860551319f994
  | 26 => 0x490c32bb98a430caed6290c329fd95430ca7f6510c329f594430cb3e5410c32cf550430cb9d4310c32bb988430caed6210c329f992520ca7d64948329f597420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420ca7f65508329f994420ca7d65108329f194420cade6310832b758c420cade60cc832b758e320cb5e538c832bb58e320cb6e538c832f394e320caee618c8329fd95320cadf654c832d7d95320ca5f654c832b7d89320cb5e524c832f3d09320cbcc424c832b7181320caef654c832dbd95320ca6f654c832bbd8d320cbcf634c832db94d320cbce534c832f3d0d320cbcc434c832bb185320cb7751944329f992510ca7d6494432db18a510cb6e3294432db4ca510ca7e60944329f582510ca7f64544329f191510ca7f60544329f181510cabe6414432af590510cb755114432be980510caf96014432af993500cabd64d4032ded42500ca7e64940329f592500ca7e61940329f586500ca7f64540329f191500cb6e3254032db4c9500ca7f61540329f185500cb795014032bb98b54cc6ed62d5331be98354cc6f960d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc67f62553319f18954cc67f60553319f18154cc73d5415331bb98854cc6ed6215331d798c54cc67e6215331db98854cc66e62153319f58854cc76d62153319b58854cc77561153319f98054cc67d6015331cf95243cc73d5490f31bd98643cc6f56190f31d795243cc79e5490f31e755243cc75c5490f31b798643cc7d66190f31f558643cc6df6550f31d7d9543cc79f6450f31e7d5143cc75e5450f31d715143cc79c5450f31c715143cc6dc6150f31cf95043cc73d5410f31e750c43cc6f66110f31bd58443cc76f5294b319f99252cc67d6494b319f98252cc67d6094b31dbd5252cc76e5494b31db55252cc76c5494b31f390e52cc7cd4394b31dbd9252cc76e6494b31db59252cc76c6494b31db18e52cc76f4394b31db90e52cc76d4394b31db10e52cc76f6194b31db58652cc76f6094b31db98252cc76d6094b31db18252cc67f6454b319f19152cc67f6054b319f18152cc76f6554b31dbd5152cc76e5454b31db55152cc76c5454b31f390d52cc7cd4354b31dbd9152cc76e6454b31db59152cc76c6454b31db98d52cc76f4354b31db90d52cc76d4354b31db10d52cc76f6154b31db58552cc76f6054b31db98152cc76d6054b31db18152cc76d5214b319fd9742cc67e65d0b319f59742cc6de63d0b31b758f42cc76e52d0b31db54b42cc67f6590b319f99642cc67d6590b31db94a42cc76d5290b319fd9542cc67d6550b319f19542cc76e5250b31db54942cc6f76150b31bd18542cc67f6510b319f99442cc67d6510b31b798c42cc6dd6310b31db94842cc76d5210b31db94b32cc76d52ccb31bd98732cc
  | 27 => 0x32af99051ccabd6414732dd54451ccabe64d4332af59350ccaf661d4332bd58750ccb7b50943329f99250cca7d64943329f98650cca7d61943329fd9150cca7c64543329fd8550cca7c6154332de54050ccb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cafa6015232be580548cb3e54d0e32cf553438caee62d0e32bb58b438cb3e5450e32cf551438caef6250e32bb189438cb9d4310e32b798e428cadd6390a32b7597328cb5d65cca32b7983328caed65cca32db597328caee61cca32bb583328cabe64d4632af593518cafa60d4632be583518cb7751946329f992518ca7d6494632db18a518cb6f32946329f982518ca7d60946329fd91518ca7c64546329fd81518ca7c6054632dd544518cb7b50942329f992508ca7d64942329f986508ca7d6194232afd91508cabc64542329fd91508cb3f64542328fd91508ca7c6454232cf191508ca3c64542329fd85508ca7c6154232af990508cabd6414232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f5495132d758e544cb6d62951329f986544ca7d61951329f982544ca7d6095132bdd85544caf46155132bed81544caf86055132d7d8d544ca7f6255132dbd89544ca7f6155132ddd85544ca7761551329f185544cb7461551329d185544ca7f6055132ded81544ca7b60551329f181544cb7860551329e181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d6015132cfd53434cb3c54d0d32bb98b434caed62d0d329f996434cb3f5450d32cf151434caef6250d32bb189434ca7e6510d32e750c434ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d09329f595424ca7c6550932b7d8d424cadc6350932bb987324caed60cc932f3d4a324ca7e64d45329f593514ca7e60d45329f583514cb775194532afd91514cabc6454532bed81514caf86054532dd544514ca7e64145329f590514cb6f6214532dbcc8514ca7e60145329f580514ca7e64d41329f593504ca7e61d41329f587504cb7b5094132afd91504cabc6454132bdd85504caf46154132de540504ca7e64141329f590504cb5e32141329f984504ca7d6114132be983540caf960d5032d798f540cb6e62d50329f987540ca7d61d50329f983540cb7a60d50329e983540ca7d60d5032de583540ca7960d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3d54150329f98c540cb5e63150329f988540cb6e62150329f984540ca7d61150329f980540ca7d60150329f592530ca7d65d0c329fd96430ca7d6590c32cf952430cb3d5
  | 28 => 0x1895190e6c62546439fd815190e7c6054643dd5445190f7b5094243cfd0e5090e7e62942439f58a5090e7e61942439f5865090e7f62542439f1895090e7f61542439f1855090eee6214243bb5885090f795014243e7d4e4350ebd6190d43af9824350e7e61d49439f5875250e7e60d49439f5835250f6f5294943bdd855250ef46154943bed815250ef86054943db5485250e7e61149439f5845250e7e60149439f5805250eee62d4543bb58b5150e7e62d4543db98b5150e6e62d45439f58b5150f6d62d45439b58b5150e7e60d45439f5835150f775194543bbd895150eec6254543bed815150ef86054543dd5445150f3e43145439f9885150e7d62145439f9805150e7d60145439f98b5050e7d62d41439f9875050e7d61d4143ded425050eef6254143bb1895050ef76154143bd1855050eee6214143bb5885050f7950141439f9885050f6e62141439b9885050e7d6214143db5885050e6d62141439f9845050e7d6114143b75924310e9d6490c43d79524310f9e5490c43b79864310e7f6550c43b7d954310f5f6550c4397d954310edf6450c43d79514310f9e5450c43b71854310f9f6550c43a7d954310f1f6550c43e7d894310f9e6250c43e75894310f9c6250c43e7d854310f9e6150c43e75854310f9c6150c43a71854310f9f6050c43e79814310f9d6050c43e71814310f9d43d4843bd9875210ef561d4843e750e5210f6f52948439f9865210e7d61948439f9825210e7d6094843e750d5210e7f61548439f1855210e7f60548439f1815210f9d4314843db5485210f9d43d4443bb98b5110eed62d4443e750e5110f7751944439f98a5110e7d62944439f9825110e7d6094443e750d5110eef6254443bb1895110efb6054443be1815110f5e4354443d750d5110f1d43544439fd895110f6f62544439bd895110e7c6254443db1895110e6c62544439fd815110f7b60544439ed815110e7c6054443de1815110e786054443e750c5110f755114443e750f5010f9d4394043ded425010f5e4394043d750e5010f1d43940439f98a5010e7d62940439f9865010e7d6194043e750d5010e7f62540439f1895010e7f61540439f1855010f9d4314043bb9885010eed6214043bd9845010ef56114043de5405010f3f54953329f98654cca7d61953329f98254cca7d60953329fd8554cca7c61553329fd8154cca7c6055332cf55054ccaf66115332bd58454ccb5e6315332db58854cca7e6115332dd98454cca7661153329f58454ccb7561153329d58454cca7e60153329f58054ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32b798f42ccadd63d0b32ddd4651cca7e64947329f59251ccb6f62947329f98251cca7d60947329fd9151cca7c64547329fd8151cca7c60547
  | 29 => 0x80000024001003c000004000301b800d00040000034000001000200040110000001001400100000140020000000800800000000000012001c00000040000004012001000000c8000001400100040120008029000000000000010028002002c00800000020008000004c000001001100400000000003000402c002800b0000002000000700280010004007001c006000c019003400a00040090000011001c000000c004000400600600090018002002000100fc002000000000100060018002000c001001002100100100054006000400a0000002002c0000004015000000d002c0000010001001000900b8009002c009007000600e4009000800f000c017000000d0024002000c02500000030040002000c00200000020000015001800000a400800200000024004000400a00000000000006000c000000000300000000000003000c00b002801b000000900100060008010000c000002000100000010004000000c00100040040000005000400900040000008005000c0000004000000c00c000400f0000002003c000001400000100040000000002400d000400c0000002000400800b8009001000300a80020008010002800900000110020000000c00000000000018004001000000000010028005000000100040000008029000000f0010009000c000000400400040010000002000400100000090000004001801500180060028007003400200000020010003000800e000000500000000000002000000100040030000005000402500000260000001000001a001c0010004000000000f0000000000401c0028000006800300440010004009000c001000c0000010007000c000005800a000c001000c000000400d006400a00040000014000000000900000090048004000400600000110000004003400d0004000000401500040000004000001000f000000100240000008002000c0020004000003c00400080040008000001400300c0001000000c00280060068001000c000001c00300100020000006000000b002400000040150018000000000d0014000000400700200000004001002000100e0000001c000000000700a8005000000a000000300080000000009000c022000000100000340004015000800700080060004008000000100240050030005002c005000c00c000000b00140000010004000000c00080100004000001400d002c00700000110052dd65d0e43d75974390f6f5294a439f9865290e7d6194a439f9825290e7d6094a439fd855290e7c6154a439fd815290e7c6054a43db5485290efa6014a43be5805290eee62d4643bb58b5190efa60d4643be5835190f775194643d7d0e5190e7e62946439f58a5190e7e60946439f5825190eef6254643bb1895190f3f43546439fd895190f6f62546439bd895190e7c6254643db
  | 30 => 0x6000c0040018000000c00100140060058000000c00f007800300580010004002002800200000020000000000401200000050000006000801800100000030000000800b0018003001800f0040000002000300240060020009001400c0000001000000000000030020010002c001002000a000000100240120000000000404b00080020004007003000f001800100540000008000008800100100130000007001401000040010000000001c001000400d001000000d40020070000000400500a40000000000000c01b002004200040040008005000c00900040070024004001800500000100004006006800000000000004014001401800000000034000000000e000000800080000000000000000500040010000015002c00200480130004013007000500200120004004001c008000000e008c02400180000004000004001b001c000007c00e0000000000c000000000e0014001001c0010000001002800100180000008001000000200080010020000000800500600020004000000802a000c00100000290000006000000000000080044002000400200000110020000000000400500050000007000000100000000058019000c01c0000008002800400000000008007000002300080000084000001c02c00000020014001000000a0000007004000000040010010005000000000080000000018001000100000020028000001000400240120000006001c00c000800a0010000001800800440000000006003c00800000060000001000000a000c001003c00000a40060004000002800600000020010001002400d00380010038000000000a0094001002400100080010080001002c0040000000000800c000000000180060028012000400000100110000002002800000040000000002008801300040000008005001400000a400c00080000000002000000900180030030000000000100080000000008000800000040100000000000000c000400200180050014018000000b000c00300000020000009001c00600040010000009000400a000c0030000011002800a0000000003000100000000030001000000200000080020008001c002015800100100090000003001c01300200050004000004c002003c00a001400c000000300040000000001000c00200000000004001001c00000100020008000002801800040080004000000000400140010004000001400300240000054002002400a0010000000400200000020068002000c000000800c0000002001400000140030000000002c000000800b001000c0000003000000d002c0000018000000000200040050018000002803e0014010000000000080050008001001c0010010000004c008005800000480000004003003c00000140050018025000000a00000000008022000400a002000900
  | 31 => 0x20000000003401f001000d00000000024000015000700000000028003000000a00080220004000000000300440030074001000800b00040020008006000c00000180000018004002000700000160024000000c004000c0000000000001c0010024000000c005004401200000100004003001000a0024000000000200b802700100030004003000000a002001000000270000000000000d0044000000000300200030018000000000800000000024013000c0050004000004800200000000000000000400f001400900100060024000000001100000000014000000002e00080090028003001800e00a8004000800e00480070040014003c005003c0040050000000800f000400f0004000002400d00040000004004001c000000000700080000008000000400b00140000050006005c00000000000000000000400b0028000000800900000000000001000000000000000000003000c008000000b0010000001800b000000000980000088000000800f0004000000801a00500040000000002000d00840020000002000c002000c00b001001a000c000000800600000000004002002000c000002d002c000001c0010040008002c00600040020010004004c00a001000000000020048007000c004002c0000004000000800100300010008007001c003000c00600200020000002001400000000180000001001000100040010008005001c00d00080000038001000c0010010010000400100040000000027001800000080000014002001400100040010008007000400e001800c005c000002c002000c00800140060008004000400a0008001000000e0010008004c0050014000000c02c00540070044000000c020000c00f00040020000003001c00100380010008004006400e002c00200280000040004001802d0040002000001100040060000000001c00300340000008000000000000b40000068000002c00000e001c00040060000002000000f0018018003c00100a400700140150000000000c00b0000004000c000000c00300140010000002000c00f0000000000400100000110000019001c008000800100500070000011000400b0000006000400100040010000010000400000080000038001000000600000090008001001000900000030008001002c00600000000000002001800700e8002001c000002800000000000018004000000100380010004005002c007004c00900180270018000002400100000050010000000000500140100000000000800100100190014015001800a0008008000000f00040030004005002c0000138003001800500000140058004000c00c0008000000800100000010000002004400e0024006000400400000000000009001400100000010044000005402b000c004001c0020000011008000400080
  | 32 => 0xc000000d000800b003004f00000120048004005400000000040048006000000100040000030015000c006001800000d000400640010004002003c0060000000001800900040050008004004000000180040008002000400a000000000000000020001004c0190064000000c000000000000280000000000000400100500020004005001400f002400a00000000014000000000200080130004006005400200040020004002001c011000c003000400b0000001000000000040000058002002400000000050008000002c001000000400040490000000000000c0000001001c00101b0000001400d0000003000800c00040000084001002000200080000010005000c009002801c0004001001000c001c00000700000010008002c01d00040000030000000800500380000004002002c00200140020004001002000000140060004001000c001000c000001801400000070024000002c000001c00300080050000001000400100c001500140000000002001800900000010054000000000900000090004000002c0010064004003c005000000100040030000000001800d0000006000c006000800000100050000005000000f003400a0054009002c005000000b00000010054001002000000040080008002000400000140090038003002800500000010004021001c000000400200180060010000000c03700280030004009001400c0004000000c003003c0060008000000c004000c00c0000007001c000001c0080004000000000200440070004015005000000b0034002000d000000900180060004000004800100000060000002000000e00000000014008000400000280020000004000000200000010000002000c004000400c000c0000008000003c001002000300080000000005000c0040004000002000700280030020006001c0030010000002800a00080000064000000c0080008008000002600880040004006000000901000020010000000c002004c00000000000000001000400d000c001000400500100040004001001800000280040000000005400f0014000000001100040050034000000400000040100014008008800900000020000008000000a00740000000000000800000140000050003001800000200000030001006400d0004004000800900000000020000000000400000010004003001c008000c000000000e00500040000059007405f00000110008000003c0000000006001800b000000a00100000004001000800000340000008001001400300000000004012000800100100070014004000000000780050020000004c00500240000028001001c002003000200000030000001001400100080010034003001000100000030004018000400600080000010003001401c0058001000402f000c001000000200000010
  | 33 => 0xb96c9867da80000000000af20000b28000079f2fb2000042a00716270d12aea39ccfec5b00f835bc175200016cc34740007812d10000000000000003a64356bb595ea000195400017145b98f10a64000000000003720194294000000000000001e4400026d600003e000000000000000000000000000007feaa2e000000073a0000a3e8000042452a24f80007828000a98000014ec000ac1d8503111f109460000624037e0001aba000000008da89e05b6a08238c000ad01e8e662000029b8d2719f0000000000098c231814f176c2c5a9de65f000024980006450000292c00037fda7c213145b00000000000cd23c0400000018a840d8000844931000000002d5000069aaee100000000002b2c000000019383c4000000000030d600001b9069a04033ba62800010a23d6194e206980606b88e2530d100a6d9fac43007be337c0007d9600c7f0a6605510b47843277a47240009090de87dec000bd04b200b217af9b080000105a128bc0c3259b8000b4c81427f4c00039642544a291645ca92aa0000faa9206f760002bb674c2d260002b0c0001e9fba8125a69b58461390de59b68cf4c381480a2a306446318960001ffc36b55ac000000048b2b4893e04f296b096d1a2800000000006ad400200040010000001000c0010004006005000500080010000000000800200000060008003001c00f000000c000402000000040024001001800a002800c000400000140000024000002c000000000100000140050000001400b00080070000001000400000440000018000001000c0008008000400400040000010007000c008001c002004c00b0014035000c00e001c0010000003008c014000001b00040070000000001c0060010000001000700000030000006000001600040050000006000800d00040070008004000000000040080018002002c013000c00100040000014001000000000140020004005008c000001c0000014005003400500080010000005008000000000110014006000800100080000018002000000400c40000010009001002500100010010000000402600140040004000001c0260000002001c00300000020010001001c000000c000000c0070020000003002e000c00200ac003000001b0018004004400000000000008000000801d002c00b00080000010000004c000000000800040020004024001c0030000000008c004001000000000070014008001000300140000008000004c00e0000009000800000140090000018002800000740150004002002400c00080050004002000800000000010098001007c00000280010004010005c0030004006000000f002c004000000f0020000000400100000000004005005c00c00040260000009000001900000060004001006001b0000000003c009000001b00ac001002c0000000
  | 34 => 0x779118e5a517267540cc7875a6b8724c2ea4b0a37e000001205400000002f49000199c9898f6644497d625e8ab0b3380007ef4825832c0008310000893800000001f80f584ec00005450000b80bc5050a8b20b68a7e8000092000000000001d7000000021cd00002691db5ab9290a0fe0000000985000024eb0b4c2280000000563a9f8000a5327b45d031100c3000044f000011df016000284800014a208ba662a8f80005f80b8a878c0006ce00007a000009260772c20800088b8000000108a6ac70c84ca2e646c51dba00011caaa280004480000000000058c000021e5a100d79a4a99f90d836f9b2eb4e05430af236826d1eb04266b9a7070cdaa99a370522832884fafa630004b419096b08a68265b30aa1c30642413840000108e79a87419c80aa8a2000023c8ada94ce9972d06b728f6e00021802bb11fc56f800027d0000930210685ea25c000034800000000002c9a4d199e80001f4e00004aa8cc8e840000000aab80140002a9e0001ee8a0919c4c2e08a79849e582650b710000000a3919fd0000000000000048f0000000102f157000000000000000000598c2d70000c660002d7a1b71024100d21c68e80008bbb068805045a3bd12ec7660000715000024a13ab40c1b9c6fda4b600000000000422bc1149a87211f81fc2ac04a791be1a7191b2938ad69bd00003eb8a0c7ed62f64c093fc3c6a72454c2f604659efe4b81af61e494487ce8ba44c380ac5fa17f61540a621dea5c060809ec0f95c720000c540000e32632a5b66501f6e9076cb37cb54781a5099a54da4580a2a8e0000129880f00003b922f1a3a0f51681930814648a11859ee04dd87de54483007652b5876330f24e8400000000000002d9c0000d6900000000001ef00000c4817fc492b6ac00038e4a7fa2c14ae3d380006f2157421ca03a17780bb36c00009a4d458000156eb00800058a07fa7ca00005a6000065d80009f91ec6acfc87ab5aaa247601760000000058280008a505ed87f2d240e20000b5fe23095bac380ece43c2508b4e58226a22aa1be8b148e5e9d580000000e498cf1c66a231cf600023ce0000c5e49581107225ad47d8ee6600004240fb85600e840000002a70ba12cc67922a944b40a5108f00006de00009aca68490e872886880003640000912aefe0002ce800001bd7f9437c886057c93390310002a18000033696ee19c982092e6782ada0b61fbc9732fa887312d86ca1d00b0600004b7151484d11d31e68eaa00006240001338150804498713393058e9f17b0a340002782a0982ec00020380000000000014445dd450b6e935d4718a76b85a97a0001dc8bda8b727b38e6d00000000001e13ab740000000000af4a90c00005393e6ab205412b9039e4000b92996c000187476766ae0000c89bcd2d8ca72c0006c180000c70000abf0000
  | 35 => 0x6787861aa4b05f816fc0004cddf1825f51403f0000000000006f0168c00003861e65df2000152e1e2996e00018a20b488b04e6c0001258000bd0914c00017e20000000c28000036e800038a073c8795a14b1b000000025a500001f003715d287280005d240725242c80bf70f3a0000fdc6a2dd0403c03087648026000059675d8b5c4832c4c00021887a70378bff157a6c65a840002f560000000abb8d7962b80005119af26adca57000029a000231cb7a16d991f0048ab31e45a7c30d8000136fb56098420f9ecc1f985e275e150c85124ea356c5c50001750782ec34957a6b0b7981823109d7e4ab1e502e7b01c7711dce2b696c875d2b860340334bf519c29bf041208904861408282b6d2b92981c48c2e619f946240000ec87b2ac50000000139200005d2681131a000018f9cf800011221fb1278b0f95180000a3a4bc00003a00fa29ca4d15c8e9ad0000000085281800003b52944af5d0e85342fc0315a2caa1817093af951ca7e0f4465c5d0c2d48aa1c290eabc4220d0a110ca8b2099cc6d008398bd222889158f82680cf20000700529000025a09ee1e8449f6411b581df632e402a7ea52600009fd0da6795c0002c484fe000234ca334eda0ce05810f79274046220e6dd25f45c604826baa8bab3903f63ef1b6c91d90ce6948d934c9a54c4099b460001f2e33ac1d04dd251246100003df83b89dd10564071a54bb9870f6e599d919c8ee0440d6acbcc1e37b66800000000000000cfc1b7a3fa0000000000039609786d23fa8bf86f307c80000000000000000025a276bc00000000f4189c3efa078a8158fa13879640000000bdc3601c0e74b92067eb94c520411261e70000000000011ac0000000000798e32001717ce15dc00000000007bd800086821df00022fc000000000000000000000000000000000002ea58ec000192c571aed700021589d99250000167400029622ed0000b2fb10c000107e464a150000087c0001d9500008d230ccbb200000006d6950ea8f00000000c1009980b200000005ac800091680000001b540000944326800046e80003914c41000107a4e68d44000125ca248000aa411580002d46216263e6a680000000000000266977e40009ccc0000001f4d000046abeb26736e600000000000000228e000000037823260000e5f73e88b5000000000005b000020647aa8000615235873b89cc83c23fc85500003d40000000000000025bc18829f6000224800024e0971c0004838b3b00009fe0002b3d7ca4b8e0000682ae101880102d6900029a83561b7a5509fbb67c840228a2e256c3a076aaa867a2312ca44eee5943140c3875488096741ce607706c29e90e274261e920000fe539a011941f4000000000042f9a4c30b0c284aa2a7a348124818287e9b6217d283584d200024b02d90000a0580007ad0000736
  | 36 => 0x1884670b131e5fe80002dae128b93ae12603a40a35ea66400002676c08000000095e3a8dbcea352b52750c0004a6ad94c0ecfc603f016a8784f12a598936ab5800048e80000003028785cdce00020ae09e084f58110d660b141600006482d213f8b3f8000463c98e06e8b5a86117280000000bfd8f2e000172ea3080000000000a60000000017d95c7916e179ae8648c24e4b53c00072a800000028103f266f2c2f18f944e02f07c6ad728ae8c640be2a7c64485c184a9b629d21d3fb1c9bef92aa32a68f2ac44b1006e00000000b5a088bb317a22cd8000000260c5d580d32a9800000faa680000ad04551b8fa919ba000012347df0522000000000000001fa8000000089f00000000000000c2c00003e5000023ba5640000ede000000018e80001c511e6975800000000008c2800000000000001738000308ea4d21480001fba8c8ab02145df42304cbeab040932a9b28f47d3d35c0360ea7962979e4420a60c24800e62d22044fca8fc59e61ea0001b806dc230491c88308ba88140000000000176300018585ba707496700005d39ad600024789a30000000000080c9e3f4100d642e9c0009e700003a811684ff417922617e642109003ee2be196a9ba481f97b6363c00000000000000000000253026c9db5b6b08968b9ad2900011cc0cb0c2017fa3769800000499877000000000002ff00001018521a5a8bd970e62108da22de0b04744aff236f49ae04194443f99b507f79629000205600016d0b7108f2abcc000697000029f65d20001dd639fcac82c65ff800008be6b8000058e997a71c10960001d79000206652aa5c900003583e22df8a71d1e456300008338ce086b81d61ec24d03de0df513a07a84ea1d0ac19af7a00019ed156283417200000002cd000000000001b183968000677d48c000000095b0dc9a6f2d0c38d23e6bfb0a94660a01e02700000002c20acd0000000136e8b5967cbb898b011d85620000000bc9000000000007d7aafa1ca40003421f02250026f1eb9d8600000009d6aa84007a23e37f4ebd4738000a989bc7440ad640128000ab0ac22000235a53f9c847fdafb880a8d256461d32c4488746cb16864b2a04a41315832241d668bbd16d73ca5afb4685f257a0aeab0aada6490969d3bfd6ce82eaec84f4a1ec6bc6c86a31aad9676c2740f7ed6397785fc6e495fe5fb252093c0d549b4848a2a19b81162a6907c95b7e0b720dabab976f1bda042ad7a4060001dc097fc77b45f80005be9c787c19fbea14050c1d38000066195e7a5000038d9bfc0000000683000016e00006f58000b9780007368fe30001e8600011060000cd8be1868eabdc6ec905ad9e2c710386f5d470abca9f40000000776f0fe811800011b80000ac400034f8000c1b000033d800000006b071b08264f285b2a162ef20000000a5f2be279b0d8
  | 37 => 0x7400000006c008c300001522a28bf211f400000025e83558f3500000008de912aac120dc8f714c4000162eb811b4a383800071d00000000f84ad730945220000276ac5e77f2d820cf41c874daeba6ec8000be004d1000131fb60cf0228897da33e8000a3e21a4000307e00008006879b0b0002dfa2d6292e69920332c94e9108281be0002c9612a4f0400aae2c2d7c9f600000000000c8b9e9908059ce3c150f857f35c879694e97a79bf8747af6e610420e6e06ac80c800021cb2d0206974ee77216b9b5e22b99360eda1ce350aeb050194172ae95d43f482801b1aab638500003c1ae0e9bea2888252c0c0002922900838cad3ccf3a40000077e04dd35980001fb99ba42aa96e10388e69ec874464fabe4c2daa4f1eda388729000018a293034e0c5885d21d289180000002f8299da72200020822e2d45509ca10226a19a80a4ad6728424b85538000aaca4b200d25be1114d6a75ea0b600011e00d8add24b9a532aaf97b73af217e0001e707949dd028e226e799cfa86ed8b7e895083a000154a2eb00000000000000041e000164878da6a68280d0180292266bf087d47e9d1476bae9060b6cde6a29ea0b968be11898e2976c983278f01f4a789e228429d1e117110c046c5248200763a188dee7ab0fc80000d4e00019fab3e0e0277480000000000864800051f9f7294b00000000ec6abec00050d8c6386319841111f51a4699068489dea3da2a6a53a2e1fab9083f00007040000ac42f0466078e008800000009fd851405906c96d2c00000017ae0902c949c3a1088b6b02e28525285cb2299078071e74720727c1171f1e8c0004f32cb41e744e364c0c743816896b8adf2029103b07b4000056247673010b8ca6e0000000000000000005d5c23e0001dad6ab083c703014e1d7997e7552746960039e554ab3039c163510e94100000ea8c2188138d2d82800016784bc8000914a0680001566b489880be6965aa6c1c100dc5a0a9869e3012545945462fe2ad2afda5ce41240001eb837f2196925000000023c25bb07f20001a4455c62f2b198b7f0002c140001a405ea19f627610605b19afe5686124907c0005df800006c15cc5e58000000000078922fa00be33039d0180140dd5cb3c00007eda736764000076128eabaa9c8628c08de26a6178ac9acbc132a07097ee46ca5d1f8fbe417c400019ae607049a79588c65ad703e9500000000000000001140001adc00028be653130f00000006fd49e8adf1b537d62554941ad5486d80f80dc0ef000000000e9c8f8808a9f26481c806fd0000999cb2e70a07fc244af7491303720f1b0e2aa0846c44cae6f41a80000f60000000186f7278a06b461e81306879e1324b44a3997f063ea88e0003044a8a041bbb367de38ac4b8952178aa26d06c6d205800fc89623c62cee602a74aacdc0008c3a00454
  | 38 => 0x2bac9c6f4dc988554acca67800061a893461d80000001d60519800000005e815d10ac23da5b500000003e00000000276a84100000000000ae8006f9df2176adb23d397f863560e25a60000000788109e12b8f303b4282cc14854b144212022151e776c11906540458a149a5e28eacc8476e4041238b3499bed6c15ecce814fc59e0000000079dfb70002f4a0001590000040b0000000000241a8291bf2542172292f96f805b00bc84525366d98494377185c05f5e2a6f67038b86dbe4b8841460001692a22c0007d50dc000014e27e0ad28bd689a2a3bafbc6116ca60000dc780b00000000000789800000023900fc285aa62800000010d270ca874ba580001b58000181000000006346a90000000073233b00000708f2b4761b6b2daad5aaf184989686582b3c93da415120809e9e155af20e29f9880415c8dfb58e48803aec3fc00b82e6096c000658823a97906c0000000089b00001ad9c7f2e180007488c9029691760002888491224c00002a40000f6c05b95995eb0d4a51f0835a270000000000082728d063c16c4540000043f495d00007f43c8a738983c000000268a0002b032078d8c0000abe000000000029e819e0a805c36364167d74c99005c6c3840000001e5a000099c8d7932e45d0000000086c0001f4689f08a8000000000020869f5800022447aa0e39dcb6b100000002ade0002d55ad516642ae40005c710cc04722850000e4e42300000000dd000000000c11e01471136a36d9e760002b780850cb2000000000027281666afe7f580000000000592800055693487a12ae2078c0000002e4c0a600008aa0fcc0f480000000000557064c8e7800009700002ee019000012100ff86be06a24f400024c40404f9599980004a20000000000099a8b246c69f3e8cd00000000cc247b000000000001e200008c3c00059f80006f880005ae23a48a1e5f600000000001fb99c121bc0000000867800000009ceb34863e69c8f622c30000a242a1b00000007f2000006680005d70060713208e3521a75614931b1d1800017015ba1e180000000ce38d98ad40001826a4122d0084021c3a34a2a33200000000327a7496ca0002e6c000096000013640000000c221a6648793320fdc59d09811a03995acbb94000000000001dd8000000189c344b03c697d14629a8000972800041fd4d42cdc00000000007258a590001eee48dc000a3e400051b27e8a2d9d6800019f057c800000000000000000000000000000007089a809a5800068680004209e6e00007d000000003b3245e0000e06165c00062b00000002d6f83f0000000000000004e68e1a3747ea80003d3e62c5618ce19c0a0d8000173c105c11a00001b2000000062308b8a85289539f265eb1dc000672a3e00000e5b00000006bef00aa7181de00016e4be7a3bf047400064a8e9515384
  | 39 => 0x1f96df0f8b7a92f526e797827e6861c7ead49bbf9803670207e00a1a6ca2a169d8439250801919020000000baa0000730000083bc2f210b8547bdfaad42b0aaf83bae59f2e504464e3a562be80c784d7a2439750e3c05298147f5089c6be90224d2a0f5c1b8000b2b81af00000007f885370fc70dc27290f07ca80000001cd20f3938a000086100000008a41e1a0e4c10ea1d63ba9240f4c02c02509ec2e1927a86d0bb0a4641b29e8cafd8000779a3cc1d41c1464728860f880003660b0a056c000b6fa69573d13560001122151841c398178c21e08d84960000000094ab5426d45002b493a78000229653426d80000001d570000000917c0002d5a5da6700000b1f8000700800042b800000000004c89ed65ea8c8c6be2e0927010e60000c98000000000000000000b709b917bc99c4d2a6735c4800019d414ccc6a000088cc0095a35d62400000242e75100000000b1a0c599e4aea80529e50e209e10e2c303d90cb585f8b70f27c66618e725fa963789e181e96794fc9c20ec4ba5261740c9c94000203043d08fc5f1810247580000000000636ab9c166ceb3928874805c57f461ac0001969accb899ef282f2e3eb844cb822211481b384ba01599ac7dd6de25861252c120c7d6e8aa805daa479532c9dda2b2edc000268b102a56a8ed0e4a208a4dc89c165b9bcd58e064db7232f055a61caab81d98416bcf95dc9ee9bcf00000006a62216bd92a346df400085040001db0595c36a4341e9a6546f15cfe1368b840001178a64af7c7ad856c63622960c2a2fd5720a6c9ce9a20000000000000008a7d7079716c6a9eaa1a73c3875fb81809b0000000115ec7c37180009b0c5c92a72b1c000000000000009118765b8f4000b8b45e4b5307682d990445c30e7893ba686c129f608b48b46a60800057e800063bc4880000406763693600002fc17547333d494143fe0200a6dd6f4c0c0bee5f31ba683d8f869e42136af6000000000d69dba01a91d309653bb0c0ba92d5b0002aa2bc200009771cce52644d60aa2ab4000026c37c8000ad1a9ce3df1f6600000000002c1655aa8a06f70000a440000c0508e8a562960274800010b2a649fb000000029181159f4a0f1e4d4171c000507800081e1ac50000d2b1d6163116a12540000bc00003104b3d000002914a00001ea219b8e511ba8a040000000000000000008062b619488ee2ddc1bb983cbbea80e09fac6470ba84e00028365f0873aae8800000026ceb759db87d2133300020362bf8adc000087685b00001d25b442ac84b287e2f9c77629ee36ae1100e6302c6229092928160047a45ee7f693c623b0fb42519d9e38ea72eaae853ac1aa1e481528cc3730790096184270907604322e9886b10507048fe00daaebc46617fc8058e9665c000066c9866a939d9a03fac48b439cb6b3513fa7421f740
  | 40 => 0xa27c00068722c039103201b6982a0a455721f280001c354da8140f9fb57a8209c788e751921f417d06a878580bd56d804c5ee12de4305fb255f9062445035a66e2b6432d059061ce6740d85bae0061c0414d15829442bdc3bf44c6affa43846151ad2158000918400098292be4a0aaa80cc2115539ac4a61124480002ba444c057a52e0000bcd800075b58e000028a497dc000283a52e83505a30b542daa2618d48e80d94c0d86a600000009df8f00b03ad92271221c00015b800024f6710a338a0f800000000003d80000000227e3274000b741c6a0000000000000000005d4000191e86e27da07e8d052ea2c7a000000037f98620000aaa65a92180001f9188bd42ea0e8485000000071900008570fd6727144289900000001cc62c5293c000144e20e0dec0002acac232eec9408eea897888770e19f8660036067d5c5245c906e0002a72331aeda2205b9ab4b2cec26b104a54087359e0267912c4288a6306a47be0e3058704d900000a246b041f8f88a67b51eda884686e834f0abc36cecb2b45ab881cc22e09218000a0280aa254afb6432850e1a0290684c9e748ea9df492723721c41c7e0000b395dcacea5eceb6e69184357708000b96024e00026558af0d9bb8d26368a09ff0b58aec627e81301c0ab5dbe11d0e9ba88701e560c60820156a63aca29540322b54a83c7c2a3ec9d392a26f813bf404a8563d34a2c6f76220951177c1bcac6e888afc61df9ddec3aa50c7461b946db85e19ab000a209de5b5689d82bc98f90920a584809041da29824799121e9aed69ea6a48c295ee5296a902bec9d493e20e2ea9830a98c6a9203e7a1998fc4b1e5162ef1bd87b518b887b8a880be8d579f3a9c0105192e9478a123831c635b0583a5caddbe508198e42509b07a588944a10d164db0c7e42e002c91880000003020a76aeacb5f43bc1830652220900e0729bd56dd8d14a1c053ebb8000028fe592ab1c00012920cc9c2b0fa7c5c0000e0eb29a4505e00001c30650a42200007bfa5e205a4e980006c8acd620590640000000a018000a060000aef89e0812294e16f6b729a49d3a480924e285ac44506838a21280000000d6eaec98315150a71000269165d049098802ce56b999894a93c413316febb4a4c22cf1cc700000000000af4272000041f0e220000000898000000000008138d044891e0279fde61ac0164e8b380000001730a79e4cc1b500000000000000000000000002a61ebd45c14c85580000000000077280000e0880a86c0000000000000028cf695a5ae38fc6a28cdb0ba1ee8c4ac288fc418f30f4c240e81bbe000078023e80000734c0ac64b0000d6872f12b205d41910002bb9211088e69e8000afa013c00029d533fccd52f167ac47d000019012364f3a5ab0000e160c8c000000000097040000f9a2746dbca66b8e208c1502
  | 41 => 0xc68c5ef639234c30dea07005d386982355de421bcb2b7498b96405f620748ff9a749711cec0d294f85bb8000a170cb0c0a4ffeaa711ee665b04e63a8000793891699606fcb9c85ba88e0000a6b924678e8a921c598b200000000389e3e18141226719b865ed44be4119daa076a1f20001db4b3e86fa7b789ab7d92598bb4c70829a159e376545a00003b51ce002030080000000000637109aa6b2fb0a88a3d486fa49e8002f40bf59581679a7269402e107f4a5f80fb253e0168a1a9a703a380fa2764ce8864357d6203751e2c8c48c96b5b9c903280fe239d87f77231a82bb7557645696b681a889e0dd1f8a9fc933dbd881ac2e490788d81e5eb9b595a3802b3664e8cca00007bc7e380007539e88000000000009c6000252289c444f95e00a86e0d05bbac815e04e462e96817b0b7b2d489c183c10d02f6e651935899ac000845e1cf00000000ed000000000000001de83f68cc4188a7320848c0b0000b628ae1160000185e0e890a06220cdc00001179862c908328000a7f8000ae02257bef80002be92c00000000afe047008b11dc040ec30377831239503214cd96a69654eac07924f225e003869bd9c55d6aff847013e68391f368f79c3e2429f1e3cc9ca20b830ca9e603c84618000c2a04e598f08ea1462fc49bd80008f1af000002d913cf21eb778a71474e04a19be2ed0542ada0ad0400099c977000007ce0ac80003392bf424e0000c3dab4ca1d886e488215646892a660ec0003799720620a1a8000145c00000000000000000000052a309c000000000000008538e6600000000001fb013d400061e0000000000000025680001e7a000178600000767c9979000000000242a2c048eed400000000000000773c90462240a622fea208c080007f02a4a83dc000675578457416e00ae8000756862500026c0c2fa1d48bb0e4c0e4a3b63a29ebc3b28e6b35ddc5021006dd05dda7bb1c07e87d680007d70d264078a0835700000001cb40a742e901aa1983288908a6110de2c18d51001ad1e4350bc3141800007a9ced000051e000134e606309ab2a81584d500006e280001de3054000000098a8bdeaba302d010de551a4f1140000000000233e000000000000008018000bbd2c4200022f33cd998a00015504a7257e658094c03a95fc297a4de26080004c0000000023b07b0c00033a878ca11acdc640d4b70a540003e480000000ab49b980005f90000000000088a80008d88000006667db951f7e73122b4985934b319445e0000ea1000174652ed1b60c19780262a3e454a00001f31cd65c0235c6a5862b7a74c3ead114760001532445a3989b72a0a00018246474000b0f857962ea95e60c004259791342b8a3bc00014a62a1c000000088a00000005e954ac69414c28e089661ed02680879840b4c2f720002e224ef82ab1a12a5ec42a0e3
  | 42 => 0xea698000000000021043906b98f38a21d79a9e886db000269e00000000000000160a8e772a25cb9bb8ef89760000aff2d800b291fe06e1cfc0fd00000000000666808a4148000a35e7b820aa16263411044ed8000ba7a95c00000005600000871800000011807564d6200000000550d8a64898a6c3c215390b2f9863883500000696769ac3c81880000000000000257a9a600004fac2d415526591991e180311b1c00000000000e40205542a59f53666772b2857123d83574e829eba266c0314b6a9405300001cc800000000a7800000000000001ee248f80004ee0dbc37e8172b8c96fc75ac0000002b2b6d3516f847a97200017322d298c06985cf06042de415a9fcc0001f16112c08c0001f7818aa4284239eeabd38cac00025740000e3731d80003fb9951b5b400019580e0407400006d1fd05a7146e0000325389011fb9e166223d0db835014ec5cfb01a58fd3a43712daa5e501049bc205874906683c300004471bd0bd14afca2a91f650929866858eae6b6aa1608889f251ea34010f08320c3aae636b9614804abb80dfcd9629c8000000000000003a500028fe00026c60002e526d38000000094e00000023bc904200000006cf0e5c000149407b00000001ab45a790b0bba0000879ce15000000000014b076580004fa10ea4f5800000030d20868cba6ef04ee00007e2000069e000000050880007529fe600000000000000000135b00029a2450a71172b80004c1273c000000017ec47936a1aaabf208b375b8cc0361224221de2cc15946e21420851b95a92644e9a88af025ad00012d400020b451482f66339a9e29e047f00009240001d885650000033800000024303dc000015c10c5134c0009b60a560002df2000000077f800026a80008470ee9861800074a1b8c8a81f524e410bb0002c0a130a5588d593180d904ab69da2243fd24e672084eaab5eaf65a0a64eb69127e329000098cad8a36b28de1cb1cc9c18a8ae000045223685a207508ce000000015900000002c2e2fd5090000278659999eea75a5ee8de069166a84782bd800000030267a6243600014c000019c17be8dca798000040f1e661d31cd4363a292097479f772460045780004bf8e7a018af0c038684243e2b0a46700006e11b828c19d4206f0b7404e2c2cb76177888f11e265100000000000aec20f90002750889a7d8b7db0406a39bfa06de1947e9281a3d010c6bf6083ba7ac21874685363a74000a652bee969020c346018c5d7800030d800038b9e62600aa5d61b2da295fdac82c61baabe847c199183d34ff80549b787bb15d59085c844f3021a28cab413789c587d6883c9062a0d90a1e51388b0219cea3004348ab13c29de1c6d6fdc252303a96c3e05b9007fafcca8e25ea4c70cce93b2ac9ac7976420600b4b07ae1345408685a0028d1ae0c6120b2bb4367
  | 43 => 0x5a0000000000000000001fb400000000000000b18924f00002620001a557bb1f216c24df048b8000b90055f5ddaf542cc8000a6c9c92b0d8c5a214c2e20f328b2630b0003389aceb181a6eb9d1d556ae165011818c40002a307db0e857cb259b0001a620000e642c380007dde4a4000000000009480a582280968000321800062c4e8e7182ace5980f3e000095042a52ccae9a010356440c1bc09d43c22d76b244cb66a4082090f910e4d6876a2ce9ab0a691ad25636882a3220ac16994b49f72ad29da10e094697f87fb61c449c8246852abfb82e222c43c805b3e616128f65e3b3c7c77c5c4aa52859113e0571b084c2a3ae45cd074141423d393528e67f00006fe42af0000d5258880007b7e432716000088506908e312fac1da54e00015540000000a8e5ee6000000000003c90001d8f81e9386184234a10c8000bcba85e000000034406a7000230885080000000000a73138c77dc0009e32e8e77cc37b8ac0f34acd5f4000002b075624fa54884c06ff8f57c0d1f5362f8eb424313f613d9cc26b7a20000028223a52ce000017d30001f5f764ec010002dc08e5000000000000002034a101c4652f14ca04f941ca722d656238000367ae148b90ae6663202b0000000403000041780002acc0006b600001a680000000000373c00000000003ee800000000000000fb2000067700000003220000aecc0001a217cb7da2e3a6b4113617c0eaf3dc8000166132c0000000a66800037610080000000ab60000000000000025040002ed864e1f0eb0480006ca81760000000b40ace2553213c5c385925a8087e50602a6c2a8f7a3ff001507a2e4405f2f3d0000f5c000000056c0bfd71e8a24000000059b0000000206c173dec4a0518e4223d2ae00016ae8a91e9a1fda622c3e0000b6c80665660000000255600020ea170d4ea05e0c8e60bdac94f5564623eab820002e7a30f00002e20e62000189450c85ac00028802442e0a1ab800061d400075c04a03468d4c4d80000b1d1724c1e108800000000002fca0000b02000272a0000bca07111dd00001055a88b7c0002d8e83b2b0d00007b8429047a6909b4c4d8834e3a3202e00030e47e10d363c780000e028e2239411eb53b00e21a87c653c8a5c000236e37aa8f25d5073e4299fec6c7a946a55133510a0cdeba8adb0924ad40bb45f327734a464eea9bf63d63f02b800002ea971ab1505835ff946a42701688d186cc3ae83c0230800096413ee0fe0aac3962f7800023a800000007e8073900000001910ec20000dd6207049c50080004901990c2019eca1f4f4a01e08c07e32a7d00027d2287a94200000004752ed5000010c00000000001382000000000000005d09d6c00002f400000000001eb23df4a320000c0a0001fd850e9a4819d93d00000000a1f20280002c7300000000000000000055
  | 44 => 0x368137000026bc4d49367a0a0670af7c9b8ba08000af2800002e257ca83800093f0000bbd8000a00800027e160200022e8acf20526d80c7c4dcaf8e000000000025ce5bd93b972e800000009020000099a9700000000aa40000000000000000000003e880000068000000000000001bb0001a2430e8000892842603480000001ecaac460be732c51268b000089be412b9d8b226ad97bebca11c20000f7f0fb5b2d8e8800042c90f64c580009ef9188297c000a5900000ef80006a156aa00c45c200000000000000000287e72b00007c6c00094930c438219c39fea84f34080820002b565af800040f800083c4000a70937b45f1dcc98e988400000006778daa00015848b096701c813060b91aee16ee0e10c68d7498e05dc5e708ed1ab2d982f69fffb482682ba2a6216bc00003949d4514c8c152020000000258e3b61751a8795f48ca2a0c9709adba244d46391d64bc2b81a400000000fae5600002b5000000005f0d8000000000702afc900c2c50a3dc74b118a4504d32a784a313506b093de109400034653b0061176723919564bb87a28d1041972997d0332d312234e67893194089e4962a43e8fa4ab2120a83794c78968d7878b9c734f02b7001d09e461b96722f40cccbdb08d5b800d1b74b0a0282480b62120bab027a27a667ac8a6a80d5a0c6289785baf883d0a2620db00000000000000000000004500001d0b8a888d42bb8000000000055187d42a2423059e80000239fc639045c40000be6ad1d6dc0000e8390614cc0001b260001c2000454de994028c30b962f3dd8f54645eb4e4e7a8d8000199200000001cfc752278485a712a7b622bcf74172c0000000d2800000000001b5600010200000000000000097887245d22f3cab1ad42c0fe7006139a939720c6299fc1ab0eeaa9a0000706b57ef16000000000004ed0000c4081f400098780000002fce0000000749800053e8000864194a194247a3c459d1b8a4000000020e000065ebb28000a4a00004b90e070000000000000000000002ef8ba000003249fc06d811f22a513e23090001bbe2d81a18af520e600023ee693a48e8070c6c00009f55c100008080186854800022aaa8817280001c3851a1128000a81823200012ba00025c300000000000000bda0d00675c000000206e4c6400025aabc20002d446158270bd783f9b98177a02d6877ad6b01872c0ccd256c5eb16dce133ca43aa355544c54e8bae963efc26af8c94290596883a69dc000000091994685188638000000000023f20002d4a000250e00000003b72601915876100013e400015bc7d58134b3f2eee0000000acf80007b6ab3225f0c7ab0013420000d6199e800808e0000000132476288c88f5834264144bc7bf04e096ca41c7e79bb09b899d6000170f50102e897c95a8abe40000fa8016000000000
  | 45 => 0xbe4a9600000003f280000000d910e6a408000000034297ba0ae097e7fb89db03a16a845e80007a281aa9358a361ff854a34bad7034e4000000023457000008be00001fb04f90000e752e362dcba009df406a05c00010bf000000077e8000b072420ba98ffa82a0010000276c0000000b2e00000000410696300839df0c60000000000096457b0000000008022b03a659088ca0000e1c00000000002f3f4d3436600026aa447901026f03d068caaac0002e2ea250a2e000007e000258c5818000309017e8a780000002314000000001a24ac50f176e1d0810a66daa565f223f69f2986487a1dee0002ff40001c3a04da2837b4800012ed30c00011448afae087ce00000000000677441a93205aa00000000001ce4000000052725880a10000b3d9e7222f0421174d51a75061700000c5c47400006282f126f291d7ae500001dac000000218275440000000c0c67d000000000006f5000000000004c840000001b0a00022560c5000000000006fa96e82d24112674f07c2d84c849ae8c60a76532aa4819e561a4b0d68a2a3a1e4c5ea000264a71a050076d8000000048486a80001cd80000002e30b7b8a3931b80002561b31bc71c650001bda00000007c90000334d06864d5066aea2bf381f0000000005016210281e5d3d8b2e98d693f98083d2264c4ad970525db03235c077716128ce25ba86800027fc3e826e82b4a5ec2fda754000236c00001cc3d655f8b13800069c00002658000569cb1e9c60000669acd8656000000029e02f104ce1083056000000000002ee7d416969039e353a996343f0a9682a6a8b400008830002440afc00005bc8000000000062d8000000187a0d51b0c0001ccc849a083161d5a41531f887a0c50db4201489d7aa96000147f00000000002fb44629214c079a6022f4b28485958bb9f89d071e54f6b6422e20002f180002a54454891c18e4453abd00008f4853552e9ccab2d95a0a7a400078497d50001c620002b2ac27800084b8eb52a1148509f23ea22ca15e0002268c0aa9fc3d79e0c767271200002de88793ef320078085680003f7800011a6b570003058be7ed1cb5a075649f11c8b11904e47c1d5d3fa05be69a1834b15af432e98e2a739c43022d9b044e015b471700000ab5be31c491e3a12ac0488cad4932b8000063aee453c266e00000004589212000057899f1f969429bec525400000000001146f500001b127e020e087c0f9e96eaf3a0000a26431f0701d2a6ab00025bd8d483462cb199406713bc965b050b65800064f084ec0400000de8f0a4a4abe09a80eb10161da4a011f316320dc24b4adbf365c8668868ae47de5596235a2ff9452a6e49b051653d08244bdaa8c782214c06593ec28f27c220b80009d0025673aa8bcab7e9b4147225016325523eb175dbe497a0000186865e2c9e0000000a4a80
  | 46 => 0x9e000063600000000002e1e6bd0e97875c084b7a9e5c5d29f2f30fcdf33791b42b1fe04c47793479c058e67fa23b28438e213542c9894707e7332400000000000001dbc00014d200000009220d0e24805d78060000210e0fa0002bbcb4ba37c0000000000000082980004df8b2a52594260000da104a01e6000000091a072140e95ce0002d3c7f712d65c200003b5c61e201cc2615a00008aca597ab80a3b208d79207840000000e6900007bd33e2396311afe001b0000000104800000240000d241989456b7f22aa562ab60000000049a800000010a861f1652586800058e1b5200011bd00013c89d08000000000000012e809280009cd00000351aca3c3c0006555be6a960a3e79305d6a3b0d3a5c5a6680cb800049e0000000149200000000001658000160c0000468121c70cb7510bab332c6f8f28e3b269000022484e20ea180cb2b0000a714e123a19c880000a9faa384db96740b700000002b3ae9c4009ea10000e1e000000004b00000002f200001bde000000000000000000000149800000000000000000904252612cc0002282faea5aadbc34b2ecf0000e112961fa6534e8ca200a884733c0007f8196400000007951e6455e50b44e7c0002fe8eec30d0279000000000026d000018f6a7916752ec07648831e78c088e0aa268fd439fa36a7ee0000000029c75198920000000634a2f7000260d00011a6b768000000000074f5d755f7800093a00003efa1d95e611d298d0000afa835c58419101525848ada22d8547a39c771800034d28c40001e4a00007a099b1a2283b94308301d3e7cae23a85a8c525392b0116e6d538760658a520ea2081a8932bc00004205865040000000008b49a868f65959c000002f8cc18029446500fd2380eb80000000307000049c17f2b6b926400013aa32a8f1d0000d6b24601592d7ab229f8111aa1b2f9459a0000b4a9a6c92690ec25ac0cc2172a003bfae2a72cabde02f80005ce9fce64a11b22b7adfe6a1919e64999a45a7d654b870000659c3da000003a1522a1074a91a83ed97626260bba2e0b0cc4310e53486a2c475ed7dca4f9fca2ce2f3203d94bd2b1ab2e6acee420b320f222c6f0e5798ac091de0b06a7038135f2eea76a139c97f6bfd2a415de22acf4672802d071f0ee83d903101cdc000abc000010f86f8b862c7933c16ea9a6b0ac0000000aac00000000000246800004e8df40002902000000000000000001f4c18617b400000000c7a15783a244457d9aa68268ea943f8db152045a95c18000000226a00019bc7018000aeecbfc2ed90b145a8d2db9aa22384009220001f905a912228ce87262269da07111cbe492a5769b150dc000000051ec00017eabba0002c2800000003c580007780000b8f04180000c8a0000df80f52670c4004e7169c6f4182027f5b780005b8866c36700008
  | 47 => 0x995c000a1ba1dd000000013413b230eeec40000000000137d0f55a30be286e43f904363ec1a5a6eea0a25128000b9c09fc4bc2b1ab36969a3a6a09b525df98b6192b862193b4754d89a0001b34bea833a7fc856600000000000a7a000000031c0000394000000000009969b5c2218000000063b000140c87980000000bd84acc00055607c2000119a0000b9c0003098000000018f4000bad142873880003a702be4daef0a66f800000000009138b96570922827c0bc68cb2be60002c5cb59a95aa4e02513f42e46415c6b485aebfa01c000000000000002286267807a00007840000db424a800091c112885198f73e45d067c8817ab311a780002d3a000000054b04de0000a7e68da1609d8902c2332a9255742ae58d8f2c0b063489818192981080e5788aca2cd45bcbf1e1b400007da0001d727818000073b046000000058b2e0b8f1000000000009ff98121b2183600020d29a5159a263022a5930c72beea298341c0004fa812600004a83a42d1200001e259c710243897361ac82040000000a3594d818b4ed62d080006cda4a60001edc00000009f00000000000000010c282100000000e613c98000b41195cc1700001005dda0000000013aa425b6a20873700003b4800075782769b113ac0000000a8a8e4b0001f1c89608ba5522c325699ed8110ce881a81ffe344c00030445f6b1c50ee1bf9744a6ad40e60580003048d9d0000000bc1a8da000257d33b56445b6095421240004da13f42f8a9be461c1d214a2d780002e282771c4e000173500004a60e545201c600007871534790901489c80008c3000066cd6670002b8c9af9632091246a2a793ae1c29440c34000067c542c9ca4a821619e6a558843843403fa9d61b883ca80008d08000000126082a9cf81dbae8c0000000174283063c80009908f8e2db99e2839d676280213a3b8a4265da075d217895c4d240000001df00002dc8000155e96347f975880009ea000050d00006f08000c1c80007d84000008862f8f015400000c0800000717cc05b4806eb420000000a4e882d294987eaf103945a100006a50a1c0000c14000000068019004010c4c2fa0000a458000b64c00096c0000000184c6bb079843f25f087e8e4f3fc9570000000000000004442f70a02000068d00000dbd9f700000000000000737a7cc00000000001d4c001303ab4da4845892c24910833c7842760000173400000000002b3a0000000a5580003920000c3f00b900000000001f2387d87d23418000aaf1a7dbbc0d6c191afa4857491e00026ec7078f563c811f28b798bc329968a48126c100016c523700006da9eae15f8bd66548000a931addb3984fc2d313e0995a688228cdbb1201a2a0001fc4000000063b93cd7772f46af68bd40001b3e005ea32b7d0000000000078a010b35d8fa12c8c2c200000000002
  | 48 => 0xaf5c14badcc8e0000012c00000252f1074d00000000000110b0ee4c9c50409326800002e2400017a61caad57000308400000000e128f06fb9d7c4a91c2a197064a6fe24ae74f17795278cbe961a53c0002d7e2e88cd000000006f488c56abafe891fa384b24b07a66c1ae40a5d2bc1fe2c5852f8d32000000025c000000002a2bf900008d399240ad8d95395ac8e0001f0c071aa0225b00008c410b62fc300600029706eb064d44b8ab8000017025c8376000000091820020000eb6335a46e0458000996d12c000000033526482930a0a7c5304260f90864de860738d61c200005415238ef69c69b3000009ba376dd6a2640a75000279e07028a213ea91c18c8b6f8c6ab693078be43e70f8aa0e01fca4499433c70da411f9d7759a87400000000167050129500000002edb00000003a499ea00015382f20eee00000003d6ad564fc00009c740001b11d0203b872e3810875722b05e5994000000000068f800000000004ba80000002ebe311c6127440d600000000076000064b47740001286000036e575800008c665295c2776379c585c30960ea4c8e8f0002adc000086000c80000001f8600000005aea30b6458140000275c51f4000000000078c8000000000000011d97458812131d23800014c600000006330d5eb400000000000000003dc32080faaf55171a911eba84fc0003664000000159c00012c6000242a000000000000000002f661321bc60000000a899d97bbc40e400000008e392909cc138437dadb8b58066a62ee18e4a51c16462ef580000a3300005a55bee41ea5d9e65154800017f6d5c3062d843648e18ac5ab38c092aa04bf00002c6e300a1512b400004664be0762176297e00021da84c0c2b4769e41c298d3739b145e55f5df56e39dfb0309dd449e8f8268e0d170001d5f8e280006c4277076453dc05800000001dac00000000001e6900016d23acae6239bdbdb0001b3a068a1c0a78e14033c40f2131143856c82c05440a486182a5a024ae1a0000d530bf800083ee3f4715a5a3826286a55e116c0e929c4a52a864a6ea8ff48ca2b6000228a1691bb87e89fb38322e204d5ee152dd80001289737bb7aaec00000006ea1c817c6639a4b8a45c790c1624b687ac49b872778e61e207c800096e18a43e14bce3a90000a500000a22a8d27c014a379ae0b296645159c3400000015564bd009a5048d1e000152a0000b5000004374784000c3b22107c140003e999130000000388df1f6da1f926b19c36b77800020d00004f500000000b10522400060ba04b870ecca96d0000c0490589f530cb53591560ca80000000b309f88f6a05d2d3e6c58000089ac1a0cf98e8bff89e6100185a00000003fda54200009e2000016f000000029c2e923e1c7e40002f220002d340002bcc601000000000008a00000000071a0000bf4b1a0000
  | 49 => 0xa7b0000c338000a6807d80000ec84c825660002b0800000000002c848241fe47178a4966d0d1177d9e140001e6800000007901bb4894a952a04860e5c40000b45074192300003f39334af9c2935a40f37245014c1e3a1181a4a4d89fe087b1191d483114bc26438f8c0002a0400012355eec33296e4000a1c800000000000afd1820f90a8c143c0009f108a20000a7c000232400025d09c3063142f2fea0000000a7e40966aa305a4b392a08c58000ae38000000000004c8f2800022360001ac0039a0c27afa3be000177414f46e004807c4bce000000025fcab6e7d06d1c992a54000060cc55d67f895a0001f7aa032b0b3b3a66daf3abd020a003c9b8cb2661dd1aa8aba59a41d800015da2068c34884000000000000000002e5c6fc0a180001a26000217294e13a0add8a404690cfe09bafd03a6000000002b48598000979ac8c030000000000000000630be8957c00000008a7000000000ba003103424b18f1031abac4a0242384580000001f08000217c8eb0b3e2fb2429791817baa19bc415f63da2ba1a7e00000004da40005ad000031ac00000000000001ae20000e3ea6cc12a0002e7c0002fd285a000000001e52150e808fe0e93266093029bca4aad0df9c00018703be91e80000000a824be000001a96c900005274000909c000bfeac06000050b00000009c800000000000000241400007dc0002a361aea1dc00014e04f2d48b000118d31a06660000b7a000000086288d00c994b30000000000067e5b0b0277ddaf487e501adb2a182b6fce6777fd2c40339818d45386e6ad89ef43b99f27bd303ac1a1956f32707229f4d4b10001da245297b200026d510217d44e623690d488627dc1d5b7c48000ac40def16393304ac1a0234324e28259fea7004000a75000012d8000a9d276415115aa36c8c0686e9ac73620ed50002b961c70000000000046f000000004d80000000000002800013a2353da8c9a5c4590678121262170a589480cb1da3a681340008bb578e0002b8a71d95da45d47c058994840f0e008113687a63cecc018b21b29c719d27ea00003ab507000011ae00018220000000000000025d000063d00002ab800087fab4d1de40000b10d7e65ca74c00001ee366800056213942f1e7c84e145da40b8000000278e96c4dd20422f2a8f40000b2c00007cf2df0b83000029d00007c745b65cc5b647168166000247b000102a4e59482229af961808000bae03ddbc7855618def0200000a00000000000000000000000000000000290e27e40006769ae19ef03070000c9e0f0b106000000000000000001a2e000208a000000000000002bc8ab6b09a84c000000046d29aa00017034b219f35649472adf9d6428b4000a42000000026a863780003908000a79800077b0000a67126200000002708000000000000000002698000b71
  | 50 => 0xe88a4000000000024ba4c5287b000000000000000002e3631394b2004d05911cade0532400064c9a0862a89569fbaeb6706800022b40001d5181a48009809892aa408585cd97ea6b67501ec200000000000c92980a1de00000000000000000290900019668829a8900000000000000000000038e0000000206b000268ea4280005bf4000417219a00000002e41249a6206985fb984a0000404389800004bab7a00000000a6dee4579005e00000005971d2019d08596af2f4444913f113716d683d100091500ef09a95f000000000c097020001ec00000eb0b80aa12880991a1350000147ec5a9b8404605cc000000083664d2ece9e2035f1731460983b0d492a0000000235406288f02f33004b5d1c6eac612768039f441131526af59474545abf200000002a380005e2000088d2fee0a3c0da4df062973824d200029014d008fe0000c1ba6d66650001c40000133e46e04f400000007aa000000023503a9415a27cc0001101d560000e25a47ae880a4000000008503dede9000000009368000000000054f89de27dc00000024966ba26a400010da000105a00000008b500ec46c000057806bca658000891000002603ca000000000000006c81e9e0000f140000000ac4a48a000000047a9cd09b32899000000020cc000218d711000000014e0000aeb8000099282aa0000000880aa0000133c000000041740c3360ad7c0000ff9ac900004598f96b73a82e0000000956a2fe49a0000000090e000000066800001d6a2404058000c43a5e03b016d429a589e7a0af1aad99e341739e3da49274438f4bfeae780005372dc23bf18fe7a99c2612b26c866884fbad66fde3fc18a784b1e7e2c21e0e1139db3442a7a05762c888112d0a8724fd819503ae48a80000000000000000095706142758b00ac1a1c1000307110265720001cb8000039c5878e464460dda0d30455177eb9800021a6683a2129cb1616a1e07a44018af8726a1e0000000024f0000809800039ba48013bc3688a128f37cd03893088aa2ba6a7105480000000000000000002e6852ca371b3200000000a80a640000ba541c80004d11aa25028000181800049315ee30c04bdc3a0493a86a05e339654a9e2968800028325f2ac78378a796a2e156815b8000000000057280009acc1b600017663471eb35590b6c71c4f24bbf01f600002191744e671e080000df40000001c180000000a7404540000000000000000019d800000006abc000000023f000059a01f02c683e0bd200000de00000000001fdb2a2eec04572e48971876926fb0b254f2b0e13c02ac70d240c090a2a669946aa5e91e538c780007b2152400000000000e6a000156c932ab4bb9b80ca58f22c6a6602ef000000034880000000202094d68e5f02aa629cd25ec130000a9d81a00002e680001f627638000b6da4b4000000
  | 51 => 0xb0
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x85c57318021042f1380c0108210f9d2639401087ae931ca0086677158a500422fb9ac328021171cd61940108dee4b0ca00846c725865004236bb443280211b5d82194010ccac410ca008565760865004332bb043280219959421cc010d4cc810e60086a564087300423cbb4a3980218e99251cc010d64c990e60086aa6488730043553204398021b858421cc010d64c810e60086e2760873004370bb04398021b859421cc010ec2ca10e60086e26408730043d13204398021a899021cc010f42c810e60086e06408730043e13984398021f05cc21cc01087ce9b2c600843d74d963004237396cb180211b5cb658c0109c8e4b0c6008667650853004237396ca180211b5cb650c01087ce8328600843d741943004237390ca180211b5c8650c010c9ca6b10600864d53588300427238ac418021391c9610c0109ceec10860084e57608430043e010a60180211e5d4640c010b32e9318600847b7654c300426cbb48618021565d6430c010cb2cb21860086596550c300434c3228618021741c5430c010cd2cb31060086696558830042f038ac418021565d4320c0108f6eab0860084b87458430042f0392c21802196596310c010cb2ca1886008599740c43004274bb442180219a596210c010bc4e310860084e9760843004334b284218021f08c4210c010f806210860087c23208430043e0190421802178dd8210c010dc4ec10860085e1760843004370bb04218021b8594210c010dc4c810860086e06408430043e1b984218021f01cc210c010dc4c610860087c26308430043e12984218021f054c210c010f848610860087c14308430042a6b98a5900219959421c8010acaea10c400847771d9520042b5386a4900211b9d85248010a9ae62924008667521852004332290c29002199d942148010d8ec610a40086c463085200422f398ca10021175cc65080108deeca90400856575084200433332842100211d5d462c4010b64e9986200847576946100425d3a4c7080211e5d46384010cd2cb31420086696558a100423cbb4a3080219a5962184010cd2ca10c20085e1760861004370bb04308021d85942184010dc4c610c20086e0630861004272388c488021399da2144010ccecb10a2008667650851004363b184288021b118c2144010caecbb1a20086576518d100434a320c68802199d9762440108eaeb31220084e6729891004333b28c488021b1d8c6244010d88c6312200866462941100432db2ec6880211e5d66344010974e931a20084da7398d100432db28c688021a6d906344010d30c831a200866b65d89100436431ec4880219ad946244010d90c631220086e062d85100423d3b4a2880219618e5144010da0c728a20084ea768851004335b2c4288021b218e21440109d4ec10a200866b6508510043643184288021b8d842144010
  | 1 => 0x104438a2a0a708221d1d4c5284110e88a6294208846e729835304236b94c1a98211b9cb6154c108dae5b0aa60843f74585530421e3a2c2a98211bdc96154c108d8e4b0aa60843e74d81530421eba6c0a982117dd95314c10c3ac8a98a60864d53588530430eb24c6298218b9926214c10c5ac9310a60862e645885304316b22c4298219398d6214c10c6ac9308a608669629805304237390cb218211b5c86590c108f2eb304860846f725954304236392caa18211b9c86550c108dae432a860851c7454d4304273396c2a18211d5d46150c108f2ea3028608659531814304237390ca218211b5c86510c108ece2328860861f6550c430430eb2a8621821651c54310c108bee6b02a40845c735815204237bb2a4290219358d5214810c3cc9318a40861e6458c520430eb22c6290219358e6214810cb2c7300a40843e74197320421eba0cb990211d5d661cc81087ce832c640843d74196320423cbacc1190212e1d1608c81087ee8b2a640843c74595320421f3a0ca990210f5d0654c8108eaea30a640865553185320423cba8c0990219a548604c81087ce8328640843d74194320423d380ca190211b9ca63944108dae531ca2084b874582310421f3a6ca188210f5d3650c410c3ac9298620861d6454c310422f39ecb10821175cf6588410cd2a5304420854e73d9621042a6b9ecb10821539ce6588410a9ae732c42085667119621042373b0a7108211b5d85388410a5ce829c420852d7414e2104335b2cc110821361cd6008410a9ce6328420854d7319421042b3388ca108211b9d853084108daec298420852e7414c2104296ba0a610821595d66108410ccacb3084208565758c421042f0b84621082169dd13108410b48e898842085e3704c421042b2ba86210821699d03108410b4ae81884208745530c4210433432ac010821721cd60084108eeeca904208665658c821042f13846410821785c23208410ccaca99042085e3704c821042f038264108211ddd56008410ba0e6b0042085e27099421042b3384ca10821d89c26508410accebb18420856575d8c2104332b2ec610821789c36308410bc2e1b1842086656558c21042f1b82c610821781c16308410accea31842085657518c21042d33a0c610821695d06308410bc4e031842085e17018c21042f1386a610821699d05308410b4ae829842087455314c21042f1380a610821789c24308410bc2e121842085677550c21042b23aa861082178dc14308410bc0e0a1842085667510c21042b2ba88610821e150c4308410acaebb0042086656598021042f0bb4c010821b8d966008410dc2cb30042085e27398021042b3baac01082171dcd6008410b88e6b0042086e37658021042f1baac010821d8dd56008410f86e6b0042085e07358021043e039ac010821701cd6008410b8ce630042
  | 2 => 0xa498a211b1db524c510c5ec9a92628862c64d4931442373b0a498a211b1d8524c510c5ec8292628862c64149314431daa6c098a218e153604c510cb0a7b02628866b52d813144334296c098a218ed50604c510c70a8302628865b53181314432c298c098a219ad48604c510cd0a4302628843f76d50314421ebb6a818a210fdd8540c51087aec2a0628861e64d4c314430eb26a618a2187990530c510c3ac8298628862e64d483144316b26a418a218b990520c510c5ac82906288658539832144334294c190a219614d60c8510a9ce7294428854d7394a21442a7b9aa510a21531cd5288510c9ccba9c428870f54d4e2144236bb4a710a214b9d25388510a5ae929c428846f7654e2144297ba2a710a214b1d15388510ad6e0a9c428864e6514e2144387aa0a710a21c315053885108dcec292428865853d81214432c298c090a219ad486048510a9ce7290428854d7394821442b2b8ca410a211bdd95208510a9ee6a90428854c7354821442b3b8aa410a21591c66508510c9ccba98428870f54d4c2144236bb4a610a214b9d25308510a5ae9298428854e7394c21442b2b8ca610a211bdd95308510a5ee8a98428852c7454c21442b3b8aa610a215adc15308510a9cea298428864e6514c2144387aa0a610a21c31505308510c9ea7308428864c5398421443a3a9cc210a21d114e610851087ceb326608843c75593304421fbb6a9982210f5db54cc11087eec2a6608843d76153304430f326a7982218759353cc110c3cc829e608861d6414f3044317326a5982218b59352cc110c5cc8296608862d6414b304432a29cc3982219914a61cc110cc8a4b0e608843e74d95304421eba6ca982211b9cb654c1108dae5b2a608843f74595304421e3a2ca982211bdc9654c1108d8e4b2a608863454d853044332296c2982218d150614c110caea630a6088664521853044317aa4c4182218b152620c110c9ea7310608864c539883044317aa2c4182218b151620c110c9ea6b10608864c535883044237bb6a4182211b5db520c1108deec290608846d761483044332294c3902219914961c81108bce7b2a408845d73d95204422fb9aca90221171cd65481108bcebb1a408845e7518d204422f3b6a690221171db5348110c3ec9a9a408861c64d4d204422f3b0a690221171d85348110c3ec829a408861c6414d2044327b1ea4902219318f5248110c9ec6292408864c63149204432ba9ec2902219514f6148110cc8a5b0a408865753185204432a298c29022199d486148110cc8a430a40885687548020443a429a40102214e9d253c4110e36a829e20887185414f10443a429ea588221d214c52c4110ad4eb10e20887485388710442b53a84388221d214c21c4110c9ea7314208864c5398a1044327a9ac5082219314d6284110e8ea610c208874453086
  | 3 => 0x975414d108baed2a0a68854e7295053442a6b94a829a2117dd95414d10a9ee4aa0a68854c72550534430eb20c829a21555c46414d10ab2e0310a68854e72d8453442a6b96c229a2147dd16114d10a38e8b08a68854f7258453442a6392c229a21479d36014d10a3ae9b00a68851f74440534428e3a22029a211b9cb6590d108dae5b2c868847970d964344237b92cb21a211b1c96590d108dce5b2a868846d72d954344237b92caa1a211b1c96550d108eee2b2a868847b70595434428f3a6a6a1a211b9cb6510d108dae5b28868846f725944344236392ca21a211edc16510d10a3ae8298868851e7550c434428e3aa8621a21879954310d10c38caa18868865453984434423a3aac221a21a550d6110d10e1ea9a9ea48852e7494f5244296ba4a7a92214bdd153d4910a58e8a9ea48870f5414f52443862a0a7a9221c350c43d4910a9ce7b06a48854d73d83524430f326a729221875935394910c3cc829ca48861d6414e524432731ea5292219358f5294910c3cc931ca48861e6458e524430eb22c7292219698d60949108bceda9aa48861f64d4d524430e326a6a9221179d85354910c3ec829aa48861c6414d524430fb26c6a922187d906354910c38c831aa48864f63d89524432631ec4a922195d8f6154910ca8c7b0aa48865863d815244237bb2a42922153dcd5214910a98e6a90a48854e7398852442a6b9cc429221939975314910e1ea9a98a48846d7694c52442973a4a6292214b5d253149108deeca98a48852f7454c52442963a2a629221939945314910e1ea8298a48870c5414c52442b4b80c629221c350c4314910acce2218a4885657110c52442a7b9ac029221531cd6014910a9ee6880a48854c73440524421f3a6cb992210f5d365cc9108eae3b2e648843f74597324421e3a2cb992210f9d3658c91087ae9b2c648847970d96324421fba2cb192210f1d1658c91087ce9b2a648843d74d95324421fba2ca992210f1d1654c9108eee2b2a648847b70595324421f3a6ca192210f5d3650c91087ee8b28648843c74594324431c2a4c0192219614e600c910cd0a5300648847875580324431c2a2c0192219614d600c9108dceb316628862f5498b31443162a4c598a2193d4e62cc510c98a7316628846c7558b3144317aa2c598a218b15162cc510c9ea6b16628864c5358b3144237bb6a598a211b5db52cc5108deec296628846d7614b314431c2a4c198a219614e60cc510c70a8b06628865853583314421f3aec898a210f9d4644c51087cedaa2628843c76d51314421f3b0a898a210f1d8544c510c3ec9a9a628861c64d4d314430fb20a698a2187190534c5108dcebb12628862f54d8931443162a6c498a2193d4f624c510c98a7b12628846e751893144317aa0c498a218b150624c510c9ea6312628864c5318931442373b6
  | 4 => 0xdaea312630846e769493184317b24a498c218b192524c6108d8eca92630862f645493184316322a498c219a94b604c610cd2a5b02630865a53181318432ca98c098c219a948604c610cd2a4302630845d76d4c318428f3a6a618c2187593530c610c3ac8298630862e649483184316b24a418c218b991520c610c5ac8a90630866a525832184236bb6a710c214b9d35388610a5ae9a9c430852e7494e2184296ba4a710c211b5d853886108dced292430866952d812184236bb6a410c211b5db5308610a5ce9a98430852d74d4c21842973a4a610c214b5d253086108daec29843085a7744c421842d23a26210c21d194d3108610b4ce818843085a5740c421843a3a986210c211d5db52086109caeda9043085e270d482184332b2ca410c21789c05208610acaeb1904308565750c821842f13806410c21595d76308610acaea31843085a67418c21842d2ba0c610c21789c06308610bc2e031843084e576d4c21842d33a6a610c21695d35308610bc4e1a9843085a67494c21842d2ba4a610c21d1d4e53086109caec29843085e27014c21842b3baa8610c21591d54308610accea21843085657510c21843c2a188610c21995966008610b8ee6b0043085c4735802184332b28c010c21719cc6008610b8ae630043086e1601802184317324a5984218b59252cc210c5cc8a96610862d6454b30843533204398421a959021cc210a3ae929c61084e472586308428eba4a6184211b5d6620c2108deeab1061084e4715883084236bb4a4184211bdd9520c2109c8e4b0861084e7760843084272bb042184219954a6188210c9ec7292410864c639492084327b1aa4904219318d5248210ccca5b0a4108666521852084332a90c290421b1d8c2148210d88c610a41086665298420842f0b804210421781c52008210ccacb29621086656554b108429d3a4a7884219a59652c4210cd2caa96210861f64993534428f3a6c3a9a21475d361d4d10a9ce5b0ea68854d72d8753442a7b92c3a9a21531c961d4d10a3ee8b06a68851c74583534430f326a729a21875935394d10c5ea9314a68864f5398a5344317aa2c529a2193d4d6294d10c5cc9314a68862d6498a5344317322c529a218b5916294d108dee4b0ca68846c725865344333312c329a218e9916094d10c5ea9b12a68862f54189534430fb26c6a9a21871936354d10c5ec9b12a68862c64d895344327b1ec4a9a218bd906254d10c58c8312a68864f631895344237396c2a9a211b5cb6154d10c68c9b0aa68866462d85534431db26c0a9a218e1936054d10cd6c5b02a68866862d81534422fbb2a629a2147dd15314d10a38e8a98a68854f7254c53442a6392a629a21479d26314d10a3ae9318a68854e7298c53442a6b94c629a210f9d06114d1087ae8308a68846e721805344236b90c029a21879
  | 5 => 0x846e72d9643c4236b96cb21e219694d6090f108dce5b2a878846d72d9543c4237394caa1e211b5ca6550f10a38e8a9a878846e72d9443c4236b96ca21e2187d954310f10c3acaa1887886954358443c4278382c221e218799263d4b10c9ae531ea58861e6458f52c430eb22c7a96219598e61d4b10caac730ea58846f7654852c421f3a0cb996210f5d065ccb1087ce9b2c658843d74d9632c421f3a4cb196210f5d2658cb10a9ae529c658854e73d4a32c425c3a2c1196210f9d2654cb1087ae932a658866b5218132c421f3a0ca196210f5d0650cb10970e8b04638861d6494c31c430eb22a618e211b5da5388710a5ce829c438852d7414e21c426c39ac010e219a9496008710a9ce7328438854d7399421c4236bb4a610e214b9d05308710a5ae829843885c87358021c430eb24a7986218759153cc310c72cb32661886396559330c4359324c398621aa99221cc310d54c810e618851d7414e30c422f3b4a698621175db530c310a3ae829861884f17119030c42ccba4c6186211e5db530c3109b2eda9861885d271d4c30c42ccba0a618621749c4530c310ab4eb21861886986450c30c4334b2ac418621569d4320c310970e8b086188599740c430c4274bb442186213a5d8210c3108dced29241886665218520c4332a90c2906211b5db5208310c5cc9316a70862d6498b5384317322c5a9c218b59162d4e10c74c9306a708639649835384335314c1a9c219a58a60d4e10a3ce9a9ca70861d64d4e538430e39ac929c21479d36354e108beeca98a70851d7498c5384237394cb21c211b5ca6590e108dce432c870846d72196438428eb9ca921c21479d35390e108dce532a870846d729954384237390caa1c211b5c86550e10a3ce9a9a870845e7614d4384273396c2a1c211b9ca6510e108dae5328870846e721944384236b90ca21c21475d25310e108beeca98870851f7550c438428ebaa8621c21879954310e10c38caa1887085947150c43842973a6a7294214b5d35394a10a5ce929ca50852d7494e52842973a0c7294214b5d06394a10ad4e031ca5085677150e52842b238a8729421c350c4394a10a9ce7b0ca50854d73d8652842a7398c129421535cc6094a108dceda9aa50852e74d4d5284296ba6a6a94214b9d25354a10a5ae929aa50846e7614d52842973a4c6a94214b5d26354a10acae331aa5085677158d5284386a1886a942153dcd6154a10a98e6b0aa50846f76548528421f3a6cb994210f5d365cca10ccaa530e650843e74196328421eba0cb194210f9d2654ca1087ae932a650866552185328421f3a6ca194210f5d3650ca10cd4a4b00650851d7494f3184236bacc598c211bdd562cc6108daed296630846f7654b318428f3a6a718c21179da534c610a3ae929a630861c6494d318430e322a698c211b5d7624c6108
  | 6 => 0x1482a73a8a610a41c3d505308520e18a8298429064e7614c2148326bb0a610a4193d4e6108520c98a730842907475398421483a229cc210a41d1d4f5108520e88a7a8842906666514421483a3a98a210a41d114c510852087ceb326609043c75593304821fbb6a9982410f5db54cc12087eec2a6609043d76153304830f326a7982418759353cc120c3cc829e609061d6414f304832629cc5982418d99351cc120c6ac9a8e609063664147304831ab20a3982419998851cc120ccac428e609064e658ca30483a3190a3182410f9d3654c12087ae9b2a609043f74595304821e3a2ca982418b153624c120c58a8312609064f531893048333b10a29824199188514c120c5ea9310609062c549883048327a9cc4182419314e620c120c5ea8b10609062c545883048327a9ac4182419314d620c120c9ccb190609066662d443048332b16a21824199988510c120ccac428860907463214430482ac3aa6018241c6151300c120b90e49806090750514c0304838c2a0a790241d414c51c8120e18a829c40906666114620483a3a98a310241d114c5188120ccec628c4090665631462048316b24c5a98418e59260d4c20a3ce9a9ca61051e74d8d530821f3a0c2a98410f5d06154c208beeca98a61046e72196430823d380cb218411ddc56550c208e8e2b2a861046e721954308236baec4a18411b5d46250c208f2ea302861046e72194430823b388ca218411d5c46510c20a3ae9298861051f7550c430828ebaa86218419654e608c82087ce9b28641043d74d94320821fba2c7288410f1d163944208eeeca88a21043e74997310821eba4cb988419354e62cc4209d2e1316621043f74595310821e3a2ca9884187192534c420c38c8a9a621064e53189310832d298c0988419654c604c42087ce9b28621043d74d9431082973a6a7108414b5d353884208daec29c42105677548421082973a6a6108414b5d35308420acce3a9842105667114c21083b128cc010841d894560084209d6eab00421066b755802108365b9ac010841b21cd6008420cd6a6b00421066953580210833528ac0108411bdd5628c02087ce9328601043d749943008326a9cc4180414b5d353c8020cccc328e401046d7694a200823cbb4a5100411b9c76548020c9ecbb1a401064f6518d2008346320c6900411b9db5348020a5ae9a9a401066765d852008333b28c290041b1d8c6148020d88c630a4010667751852008333a98c2900419954c6148020dc2e030a401046c76945200833230ca2900416a9d33048020dc0c39824010569750c120083a4a986090041b81843048020cb6cbb1a401065b6518d200834c320c6900415a5d73248020ce6cbb0a4010673651852008368318c290041b8d8861480209d4ed90a401056b75485200822fbb2a629e21875915314f10c3ac9318a78
  | 7 => 0x428a41c91523214520e8ea7190a290744538c85148393aa26428a41c91513214520e8ea6990a290744534c851482f03826428a41595ca6314520a6ee8b18a2905347458c51482b3b92c628a415cdc16314520a6ce8318a2905357418c51482b2b90c628a415c5c06314520acce5218a2905657290c51482b93848628a415c5c24314520e2a86218a2905667210c51482b2b908628a41595cf6214520ec4e1b10a290566768c851482b3ba46428a41595d23214520acce1190a290573704c851482b83826428a41599d93214520ac8ec990a290567744c851482b2ba26428a41d1dcd3214520ec6e0990a290564704c851483b03826428a41581c13214520aaee6b00a2905547358051482abb9a4028a41551cd201452087ee8b2e629043c745973148317aa4c598a418b15262cc520c9ea7316629064c5398b3148317aa2c598a418b15162cc520c9ea6b16629064c5358b3148274382c598a419998b51cc520cccc428e629066562147314821fba2cb18a410f1d1658c52087ce9b2a629043d74d95314821f3a4ca98a410f5d2654c52087cebb22629043e75191314821f3b6a898a410f1db544c52087cec2a2629043c76151314830fb26a698a4187193534c520c3ec829a629061c6414d3148317aa6c498a418b153624c520c9ea7b12629064c53d893148317aa0c498a418b150624c520c9ea6312629064c53189314831bb26a298a418d193514c520cc8c5a8a629063764145314831a320a298a4199d88514c520cc8c428a629063b54d81314831c2a6c098a419614f604c520ce0a3b02629063b54181314831c2a0c098a4196d4c604c520cb0a63026290673511813148338288c098a410fdd1650c520878e8b28629043e74194314821eba0ca18a410f9d6640c520878eab20629043f76d50314821ebb6a818a410fdd8540c52087aec2a0629061e64d4c314830eb26a618a4187990530c520c3ac8298629064c53988314831b326a218a418d593510c520c6cc82886290635641443148333310a218a4199588510c520cb0a7300629067051980314833828cc110a413a9c36388520e1ea9a9c429052e7494e2148296ba4a710a41599c65388520a5ee8a9c429052c7454e21482b238aa710a419358c5388520e1ea829c429070c5414e21483273b0a710a41935d85388520e8ea628c4290744531462148333b18a310a419958c5188520cc8a330442907605198221482753acc110a419a9d66088520d96a730442906c8539822148371a8cc110a419a1466088520dc0a330442906605198221483b028ac110a419614f6048520cb0a63024290673511812148274382c610a41c3d535308520a5ce9298429052d7494c21482a739ca610a41599c65308520acae3298429052f7454c21482963a2a610a4159dc55308520ac8e2a98429046d7614c2
  | 8 => 0x36154d20c68c9b0aa69065763d855348332b96c2a9a418dd906154d20c68c830aa690657631855348333b10c2a9a4199dc86154d20c70c9b02a69067061d81534822fbb2a629a4147dd15314d20a38e8a98a6905577154c53482aa38aa629a41479d26314d20a3ae9318a6905567198c53482aab8cc629a410fdd16114d20878e8b08a69061e65d50534822ebb4a829a41559c65414d20aaae32a0a69045f7655053482abb8aa829a41551c55414d20e1ea8b10a69070c5458853482a6b96c829a41565c36414d20c3ac8320a69054d7219053482a638ac429a41535cb6114d20a3ee8b08a69051c7458453482a7b92c229a4156dc16114d20a3ce8308a69051d7418453482a6b90c229a41565c06114d20a3ce9b00a69051d74d80534828fba24029a41471d12014d208ece3b2c869047571d96434823bb8acb21a411d1c56590d20c5ea9314869064c5398a43482363aac521a419314d6290d20c76a9304869065853982434823c3aac121a419614d6090d208ece3b2a869047571d954348237b92caa1a411ddc56550d208e8e2b2a869047b70595434828f3a6a6a1a411d9c76510d208eae3b28869047771594434823a38aca21a41475d05310d20a3ceaa18869051c7550c434830f32a8621a41871954310d20c98a7310869046c755884348274382c421a419614e60cc9208dcebb2464904e8705923248317328a91924193997538c920acce329c649070f5414e32483862a0a7192419314e618c9209d4e130c649063854d81324831c2a0c09924196d4c604c9208d8eab2264904e4715913248274382c89924193197634c920acce329a649046e7614d32483862a0a6992413a9d4604c920cd4ea30264906ab5418132483542a0c099241b2d4c604c920d90a6302649064c53988324821f3a4c7a8a410f5d263d4520e2ea9a9ea2905367494f514829aba4a7a8a414ddd153d4520a68e8a9ea2907175414f514838a2a0a7a8a41d15c853d4520e8ea6b16a2907445358b51483a229c65a8a41781c132d4520a6ce9b1ea29053574d8f51482b2b96c7a8a415c5c363d4520a6ce931ea2905357498f51482b2b90c7a8a41c550c43d4520aace7b06a29055573d83514830f326a728a41875935394520c3cc829ca29061d6414e514832b31ea328a419558f51945208bceda9aa29061f64d4d514830e326a6a8a41179d85354520c3ec829aa29061c6414d514823bbb2a228a4155dcd5114520aa8e6a88a29043f7458c514821e3a2c628a41599c63214520ac8e2990a290568704c8514832b32ea628a41c5d535314520e8ee5a98a2904757694c514829b3a4a628a414d5d253145208eeeca98a2905377454c514829a3a2a628a41959945314520e2ea8298a2907145414c51483a2b90a628a41d1d4f6214520e88a7b10a290566758c85148393aa46
  | 9 => 0xee8a88421852c74544210c326b2c6210861935943108430b1ae81884218745510c4210c30f3228728061475d03194030c9cc7296801864d6394b400c32731aa5a00619358d52d0030c3aa931c801864e6354a400c326b1aa5200618719543100308daed290801846f76548400c317324a5980618b59252cc030c5cc8a96601862d6454b300c346b24a598061a359152cc030d1ac910e601854d75087300c346b204398061b198421cc0308baed29c601851d7494e300c23cbb4a718061665d2538c030da4c318c6018599740c6300c2b4ba8431806117dd5644c030998e4b2260184d471591300c327b2ca49806193d95524c030c9ecb10a601854d75085300c327b284298061b1184214c03093ae9b0260184da76d01300c34cb208098061725c8404c030b34e929a60184da7610d300c335b2ca4980619ad95524c0309b4ed99260186d0618c5300c2cd3a062980619ad96214c030ad2ea10a601866b65085300c37030842980619a98960d4f2087ee8b0ca79043c7458653c822fbb2a629e41875915314f20c3ac9318a79063a6458053c823b38ccaa1e411d5c66550f20a38e8a9a87904e97218143c823b38eca21e411d5c76510f20c3ecaa18879061d6550c43c827238ac8996413a1c1644cb208dcec29a659065a5358032c82a6b98c528e41591c5329472087ce831aa39043d7418d51c823bbb2a228e410f9d2658c72087ae932c639043f7459531c821e3a2ca98e410f9d3650c72087ae9b28639061d6494c31c830eb22a618e411b5da5388720a5ce829c439052d7414e21c82b338ea610e41595c75308720a5ce8298439052d7414c21c82b3388a610e41595c45308720aceeca8843906677654421c83b128cc010e41d89456008720c3ac929e619061d6454f30c828eba0a718641179da534c3208baeda98619051d7414c30c8334b14c1a9c4117dd95314e208ece332a871047571995438823b388ca21c411d5c46510e208bced29a651045d76d4c328823bbb2a228c410fdd1654c620878e8b2a631043e74d94318821eba6ca18c41599c75388620acce229c43107625198221883b128ac110c41599c65308620ac8e2a98431046d7614c2188272bb6a210c41789c35108620bc4e0288431064d53588308833330ca3904410f9d261d4d2087ae930ea69061f6499353482a6b90c9a9a41565c064d4d20a3ce9b0ea69051d74d8753482a6b96c3a9a41565c361d4d20a3ce930ea69051d7498753482a7b92c3a9a4147dd160d4d20a38e8b06a69061e64d4e534830eb26a729a418dd526194d20caea730ca69063754586534832ba9ac329a418d9926194d20c6ac930ca690665629865348333b94c329a418d9916194d20c6ac8b0ca69066772586534831baa6c2a9a418dd506154d20c3ec9b1aa69061c64d8d5348316326c4a9a418dd9
  | 10 => 0x46f72595410c236392caa08611b9c865504308dae432a821861e5418d410c30eaa0c6a08618719543504308daebb12821846d75189410c2373b4a4a08611b1da5250430c9ec7292821864c63949410c2373b2a4a08611b1d95250430c9ec6a92821864c63549410c32a31ca2a0861c550d5150430cd4a5b02821866952d81410c31d2a0c0a08618e5506050430d3286302821866a52181410c334a90c0a08619c94460504308dce5328821846d72994410c21ebb6a820861365c26310430c3ea8b18821849d7690c410c30eb2c86208619398e5210430c9ac7290821864e63548410c326b1aa420861591c552104308daeb316621846f7558b310c236bb4a5988611bdd952cc43087ee8b2c621843c74596310c2b238aa51886127dd1658c430a38e8b2c62184db70592310c22ebb4a918861175d8548c430c3ec82a4621855571152310c26cb84c51886193595528c430b88e2a94621851c74546310c2acbaec11886127dd1608c4308d8ed292621862f64949310c316324a4988611b9d9524c430c5ec8a92621862c64549310c2b238aa4988619a94b604c430cd2a5b02621862e64948310c316b24a4188618b991520c430c5ac8a90621863564944310c31ab22a2188619a54a600c430cd2a4b0062184d970d90310c24ebb4c81886187dd5640c430c38eab20621845d76950310c30eb24a81886187590540c430aaae22a0621868d64948310c346b22a418861a5592510c430a38e8a88621861d64544310c34ab22a218861d1949510c430d32c9300621869a64580310c21f3a6cb908610f5d365c8430c9ac7296421866a52583210c26cb84c7108619398d5288430c9ac6a9442185c9700ca210c2b338ecb10861939cf6588430ccce3b2c421852e74196210c296ba0cb108611b9db54884308daedaa4421846e76152210c236bb0a910861599c45488430acae22a4421864f6598e210c2e4b84c71086193d956388430a5ae929c421854d7590e210c326b2c8710861725c24388430c9acaa1c421870c5450e210c297ba2a3108614b1d15188430c9acb18c421864d650c6210c2c6ba063108610fdd16548430878e8b2a421864f63549210c334a96c090861175d7630843093ae831842184d97018c210c326b2c6410861935943208430b92e0190421856671d94210c33338eca108611b5da6508430c98e6b28421852e74194210c296ba0ca108615a9c065084308dcedaa0421846d76d50210c2b3b8aa810861591c554084308dcec2a0421846d76150210c2b3388a810861595c45408430a9aebb18421864d65d8c210c2e338ec610861535d46308430c9aca318421858d7418c210c2e3388c610861725c06308430a5ae9298421854d7590c210c326b2c8610861725c24308430c9acaa18421870c5450c210c2e238a86108611b5d66108430a5
  | 11 => 0x4c2a6392a918261551c5548c130e88a210c609846e7198b540c32731ac5aa0611b1c562d50308dee4b0ea81846c72587540c334b14c1aa0611bdc961950308d8e4b0ca81846e72d85540c236b96c2aa0610fdd95415030c6aa8b08a81846e71988540c23638ac42a0619998a6115030ccac5308a81866772984540c332394c22a0611bdc961150308d8e4b08a81865663584540c333312c22a061995896115030ccee4b08a81866472584540c338382c22a061555c45490c308beeab0486184db75582430c32dbaac121861361c56090c30b34e1aa2861845e76151430c2aab88a8a1861279d85450c30b2ae22a2861851e76151430c30f3b0a8a1861c39c85450c30e1ae42a2861871671151430c28eb88a8a1861c55c45450c30a2ae22a2861851e70151430c38d380a8a1861365c06250c30c38a830a861843f76550430c28eb9aa821861a650e6010c30acce22a4a41856571152520c2c6ba0c729061725c24394830e18a8a1ca41854e73192520c2b5380c9290614b9d06394830a5ae831ca41870d4310e520c2973a6c3290614b5d36194830a9ce7b0ca41856a70d86520c2973a0c1290614b5d060948308dcedaa2a41846e76151520c2b3388a8a9061595c45454830b92e121aa41854f7550d520c3862a286a9061539ce6454830a98e6b22a41856771591520c2b238ac8a90615a1c16454830a5ce931aa41852d7498d520c2b338cc6a9061595c66354830ad4e121aa4185697090d520c386a1886a9061539ce6154830a5ee8b0aa41852c74585520c2a639ac2a90615a1c161548308deeca90a4184d97098f420c326b1aa5a10611ddc565508308e8e2b2a841864f63549420c32631aa4a10619a54b6050830cd2a4302841864d63948420c335292c0210619a54960cc8308baebb2464184db70592320c326b2ca51906127dd1608c830cd4a4b0064184d970d90320c26dbaac01906196dd5600c830d94a4b0064186c952580320c26c38ac0190611b9ca64944308dae5324a21846f72592510c236392c928861599c76294430acce2314a21862f64949510c316324a4a8861599c65254430c5ec8a92a21862c64549510c2b238aa4a8861879cc6454430c3ae6322a21863571191510c22f3b486a8861871924354430c38c8a1aa21862f64d89510c316326c4a88618bd906254430c58c8312a21863b64181510c31c320c0a88619ad886054430cd0c4302a21846d76948510c317324a4288618b59252144308deeca90a21862e64548510c316b22a4288611ddd95114430c6ac8a88a21846e72d97410c236b96cba08611b9ca65d04308dae532e821846d7598b410c237baac5a08611bdda52d04308daed296821846f7654b410c236bb2a5a0861591c552d0430d3287306821846e72996410c236b94cb208614d1d15190430e2c86a8c8218
  | 12 => 0xa14611d5c765d0a30c3ca8b1e85184d873582428c24fba2c119461365c3640ca308dce5324a31846d72992518c22e3b286a8c611ddd951146308dce5b2e831846d72d97418c30fb2a87a0c611b9ca65906308dae532c831846f72595418c236392caa0c6187d954350630d3286302831861e5458c418c30eaa2c620c61275da43106308baed2a4631861f64952318c24fba2c118c619c944604c630c3acab20631861f75590318c34db82c818c61a61c1640c6308baed2a0631861d64950318c30eb22a218c610f9d3658863087ae9b2c431843e74996218c21eba4cb10c614b9d36588630a5ae9b2c431856671d96218c2973a4cb10c614b5d26588630e1ca8a1c431858d740c6218c24eba0c610c61365c063086309b0e6b0043186ca32580218c2b338eca10c614b9d06508630a5ae8328431856671d50218c2b2b8ea810c61599c65408630acae32a043185c671d8c218c2c6ba0c610c61719c46308630b92e0318431870e5450c218c2e238a8610c61635d03108630cd0cab0043185c873580218c365b1ac010c618759664cc230c3acab26611868d64887308c346b204398461b198421cc230c72cb326611863965593308c237b92c3aa2611b1c961d51308dee4b0ca89846c72586544c23738ec4aa26193d8c62551308dce2312a89846e72d85544c236b96c2aa26199d8b6155130cc8c5b0aa89866672d85544c332b96c2aa26195d8c6155130ccec430aa89866462185544c333b90c2aa261991c86155130cd0c5b02a89867061d81544c21fbb2a82a2614b1c95415130a68e2aa0a89846f72584544c236392c22a2618e15160d0d30c3ccaa18869846f76548524c2963a2a429261591c552149308bceb31c849847771594424c23a38aca212611ddd95114530a68e8a88a29856472544514c237b92c828a611b1c964145308dce432e829846d72197414c333316a3a0a619998851d05308dce532a829846d72995414c237b92ca20a611b1c96510530c3ea8b18829861c5458c414c26c382c620a619558f5110530c68c9a8a629866462d45314c31a320a298a6199188514c530ce0a3b02629852e74d96214c296ba6cb10a61599c465885308deecaa4429846c76552214c2b3b8aa910a61591c5548853087ee8b28429843c74594214c21f3a0ca10a610f5d065085308bceb318429856572d44214c334292c010a614bdd16508530a58e8b28429854f73594214c2973a0ca10a614b5d06508530acce2328429856671950214c2b2b8ca810a611bdd954085308d8ecaa0429856771550214c2b238aa810a61539d66308530acceb308429856576d44214c332bb6a210a6159dd85108530e8cc6288429874563144214c3b028cc010a615a1d56008530cd0cab0042986c963580214c3b028ac010a6187d5163d0130c38a8b1e80987605108730
  | 13 => 0x61953308d8e4b0ca99852e7218e54cc296b90c72a6614d9c46395330a6ae231ca9985397018a54cc297396c32a6614b5cb6195330a72e1b0ca99851c7358654cc297b92c32a6614b1c96195330a76e0b0ca99851e7318654cc237396c2aa6611b5cb6155330a5ce531aa99852d7298d54cc28f39cc4aa6614edc16255330a5ce5b0aa99852d72d8554cc28e39ac2aa6614bdc96155330a58e4b0aa99853b7058554cc28f398c2aa6614bdc96055330a58e4b02a9985377158154cc29a38ac0aa6610fdd954153308dee4b08a99846c7258454cc31caa4c121e618e9526010f30c6ca930ea5986355498752cc31b2a2c3a96618d55161d4b30acce3a94a59843d7695052cc21fbb2a8296611bdd95214b30c3aa931c859861d5458e42cc31caa0c0a16618e9526010b30c74a8b00859863a5498032cc31d2a2c0196618b95262d4730c5aa9316a39862e5458b51cc316aa2c5a8e61599cb5194730c5ca9b12a39862d54d8951cc3172a0c4a8e618b5506254730cd6c5b02a39866862d8151cc21ebb4a828e610fdd954147308eeeca88a39846e72d9741cc236b96cba0e618b95262d0730c5aa9316839862e5458b41cc316aa2c5a0e618e95260d0730c74a8b06839846f7259541cc236392caa0e61879536350730c3aa9b1a839861e5418d41cc30eaa0c6a0e618b9536250730c5aa9b12839862e5418941cc316aa0c4a0e618e9536050730c74a830283986395418141cc30eaa4c620e61879516310730c3aa8b18839862e5498b31cc316aa4c598e618b95162cc730c5aa8b1663986666294731cc333312a398e618e95260cc730c74a8b06639862e54d8931cc316aa6c498e618b950624c730c5aa8312639863a5418131cc31caa0c098e610f5d6640c73087eeab20639843d7695031cc21fbb2a818e610f9d265c873087ae932e439863a5498321cc31d2a2c190e610f9d2658873087ae932c439856671d9621cc2973a4cb10e614b5d26588730a5ce832c439852d7419621cc21f3a0ca90e610f5d06548730c74a9b02439863a5418121cc21f3a4ca10e610f5d26508730c3aa9318439861d5458c21cc2b3b92a210e61599c76508730a5ce9328439852d7499421cc2973a0ca10e614b5d06508730acce22a043985657115021cc386aa4c610e61c35516308730acaeb30843987265498421cc392aa4c210e61c99525108730e4aa928843985677694421cc3a331ca210e61d158e5108730e4ca8a8843987255454421cc2b3bb2a210e6199dd95108730ec6e0a88439861e5458f40cc30eaa2c7a06611bdc961d52308d8e4b0ea91846f72586548c236392c32a4611b9cb61552308dae5b0aa91843f76550548c316aa2c42a4618e5506050e30a3ced2a2871861e76951438c28eb8ca8a1c61879506150e308deeca90a51862d64548528c23b38ecb
  | 14 => 0xeca1ca210ce67610e5108672bb08728843e150c4394421b8ce7b04a210dc573d825108636ba8c9988439359643cc421c9acaa1e6210e8c6450f31086e238a8798843e150f41cc4218deeab1c6210e8f6410e31086e2b88871884399596518c421f088720c6210d4d75cc63108636bacc1188432bdd1608c421958e8b046210e2f65d913108636bacc8988433a9c2644c4219d2e13226210c6f755913108673b8ac8988433adc1644c4219d0e0b226210cae761913108717b28c898843a95c4644c42199ced21a6210e4f6590d3108746324869884393d95434c421d18c8a1a6210dc47150d3108717b24a2988438b192514c421d4ec928a6210ea46494531087523248298843e190e414c4219c8eca0a6210dc47350531087c2a1a8298843a9193314c421c9ecb18a6210e8c648c53108735b2ec098843aad93604c421d50c9b026210ee251d813108735b28c098843aad90604c421d50c83026210eca431813108764a18c098843b8dc4604c421dc4a23026210ee2411813108770a08c098843b8cc4604c421d94623026210cae74d943108656ba6ca188432b9d0650c42195ae83286210ce6711943108656bb4c818843a31cd640c421d48e2b206210cce731903108673388c8188431b5d6630c421d1ac92986210e8d6454c3108666bb68618843a3593430c42199aec2186210e8d6410c31086e2b8886188438b992510c421c5ac92886210ce5769443108732b2ca218843a9992510c421d4ac92886210dc5739443108672bb68218843a9593410c421f0e87a086210ce57610431086e2b988218843e110c410c421a9aeb9886210e8d64cc43108752b246218843715ce310c42199eec9886210d4f754c431086c63a26218843a3591310c421b90e09886210ce7764c431086d23a26218843a9591310c421bc0e09886210dc7764c43108763bb2621884371dd5310c421e8eea9886210f87744c431086e33a26218843711d1310c421f08e89886210d84744c43108763b226218843e1991310c421d8ac89886210f85644c43108742b226218843f0dc1310c421b88e09886210fc0704c431086e038262188432b9d2639402195ae931ca010de2709465008747b26c6a8043a3d906354021d18c831aa010ec97018d500872631ea6a80435a1c15354021d8ec630aa010ec4631855008727b1ca2a80439318e5154021ad4e128aa010ec763945500876231ca2a8043789c25154021d1cc9318a010e8e6458c5008746b22c628043b198e6114021d8ac7308a010ec6639445008762b1ca2280439358f5014021d92c7280a010c6f765405008726b1aa0280433add95014021d92c6a80a010d6b765405008735bb2a028043d2dcd5014021e90e6a80a010f4a635405008734b1aa028043d258d5014021c92c6a80a010f607154050087b130aa0280431bdc9
  | 15 => 0xe5711933208673b8ac1990430f9d3658c82187ae9b2c6410c6d75d923208672b8ec9190435a5c0538c8218deeab0c6410caf7458232086563a2c11904339dc5608c8219cee2b226410ceb705913208674382c8990431b9d8534c821ad2e029a6410ce571d813208636baec8190433a9c3640c8219d2e1b206410c6d751903208672b88c8190431bdd9530c8218deeab086410ce771580320861f3a6ca188430f5d3650c42187ce83286210c3d74194310870eb24a61884387591530c421b28e89886210e95644c431086e838262188432b9d363c842195ae9b1e4210cea70d8f2108674b86c7908431b5da52884218eaed2944210c6d7598d2108637baac6908432bdd16348421958e8b1a4210ceb7058d2108674382c6908430f9d2639402187ae931ca010e1f64d8d500870fb20c6a8043871906354021c9ce431aa010e4d7218d500872cb80c6a80439318e3254021ad0e0992a010c7b76540500872cb1aa028043399c261d4c2195ee8b06a610cac74583530867238ac929843719c75394c219c8e2b04a610ce67119153086e338ea6a9843399c76054c21d1ac9298a610c6f7654c5308667bb2a629843a35915314c21d4cc9308a610ea564984530876329cc229843b154e6114c219cce1308a610eaa649805308754b24c029843b89866014c21dc0e3300a610eaa645805308754b22c029843b89856014c21cd6a6b00a610eca535805308734a9ac029843b254d6014c21dc0e2b00a610ce6719964308673388cb218433a9c06590c219d2e032c8610c6f755864308673b8ac121843391c56090c219cce332a8610ceb705954308674382caa1843399c46550c219d4e032a8610ce970195430872632aa6a1843631d15350c218daebb0a8610ce575d854308732baec2a1843399c36150c219caea30a8610ec6531854308762a98c2a1843a990c6150c219cce030a8610ce671d814308672b8ec0a18431b9d46050c218daea3028610ce6719944308673388ca218433a9c06510c219d2e03288610d8d7490c4308667bb28621843711c54310c21b1eeca188610e8f7650c4308747b2a8621843a35954310c21f0ee2a188610d8c7150c43087c238a8621843611c54310c21f0a873088610ce5759844308673384c2218431bdd56110c21d1a86b088610ceb705844308674382c221843e150d6110c21bc0e0b088610ce7755844308733baac221843b190d6110c21d8a86b088610e85435844308771b82c221843391c16110c21dc0e0b088610ce0705844308746a1cc02184339dc56010c219c8e2b008610d2e7414e5108696ba0a7288435a9c05394421ad2e029ca210d2e7418e5108696ba0c728843c350c4394421b4ce831ca210da57418e5108762b18c728843699d05394421b4ae829ca210de27014e51086f0b80a72884339dd943944219c8
  | 16 => 0x8746b24a629c431bdd95314e2199eeca98a710e8d6454c5388753324c229c43a95926114e21d8ca7308a710ec5539845388675386cb21c433a5c36590e219cce332c8710ce671196438872732ca721c43399c66550e219d4e132a8710ce9709954388673388caa1c43631d15350e218dcea3028710c6d75181438867338cca21c43399c46510e2199eeca188710d8f7650c4388747bb28621c43a3d954310e21d1acaa188710d8c7150c4388746a1ac221c433adc16110e219d0e0b088710e8d4398043887463228798c43a3d90438c6218daeb3046310caf7458231886563a2c118c438bd97644c6219d4e13226310ce9709913188675b82c898c433a1c1644c621c5eca3226310cce7690d31887463248698c43a3191434c621d18c918a6310e6b65d813188755b26c098c43aa193604c621cd6ca3026310eab641813188754320c098c43b290c604c621d92863026310eca31181318874639ac818c43a3592530c621d1ac8a986310ccd76d0c3188746b268618c43a3590430c621d1ac99886310ccf764c431886c63a26218c43a3591310c621b90e09886310ce7764c43188747324c7a8443a399163d4221d1ac8b1ea110d6a70d4f508872731aa7a8443b198e61d4221d8ac730ea110cae7498e5088656ba4c7284435a5db5094221cd2eda84a110f4a73d4250887a4b9ea128443d89c750942218deeca80a110ceb76540508861fba2c1a9a430f1d160d4d21c38c9b1aa690e2f64d895348716326c4a9a438d1936154d21c76c9b02a690e3864d815348735b16c0a9a438ed906054d21c70c8302a690e5b631815348735b10c0a9a439cd846054d218beeca98a690d1c7454c53486ac382a629a431b5cb6590d218f4e1b2c8690c7970d964348637b92cb21a431b5cb6550d218dee4b2a8690c7771595434863db82caa1a431e1c16550d218dae5b288690c7571d944348637b92ca21a431edc16510d218f0e0b288690d1d7414c434868f3aa8621a43471d54310d21ca8a6b0e6490e4f5358b314861fba2ca98a430f1d1654c521c38c9a9a6290e1c6414d314872629ec498a4396d4c604c521cb0a63026290d2f7454e21486963a2a710a435adc15388521ad0e0a9c4290c7b7654050486ac39aa0282430fdd160d4c21878e8b06a610c5f7654c530870eb22a6298439654d6014c21c3ac9318a610e3a64980530871cb24c0298438e9916014c21c72c8b00a610e5a635805308735312c0298431e9c06590c218f2e032c8610c6d7598a430863db82caa18431e1c16550c218f4e032a8610c7970195430868e3a2a6a18431b5d46250c21c9aa63128610ce572d85430863aba8c2a18431e9c06510c218f2e03288610e1f6550c430870eb2a8621843651c54310c218daeb3108610c7575984430874aa1ac22184339dc96110c219e0e0b088610c
  | 17 => 0x88638b55162cc4318beecaa66218e1e64553310c70fbb2a998863871d954cc431e1aa93166218f0d5458b310c70eaa4c198863175da538c4318eaed29c6218c3e76951310c61e3b4a8988630f9d9544c431c5ca9b126218e2d54d89310c7172a0c4988638b550624c431c74a9b026218e3954d81310c71d2a0c0988638e550604c431c3ee9b2a6218e1c74d95310c70fb2ec898863175d6644c43193ce93226218cda70991310c70fb28c898863875d4644c4318bcedaa26218e1c64d51310c64e3b4a898863475d6544c431c3ecb2a26218c5c76551310c70e322a898863271d9544c431c3ecaaa26218e1f76551310c68f3b2a898863471d9544c431c38ecaa26218c1c76551310c727b2ec498863a3193624c431e1aa9b126218e4f65189310c746320c498863c3550624c431c3aa9b0a6218e1c64945310c72db2ec098863a6193604c431e32a9b026218e1d54181310c72db28c098863a6d90604c431d30c83026218f1954181310c765b10c098863b2188604c431cb6a83026218e9a54181310c72caa0c098863a6550604c431c32a83026218e3774d95310c71a3a6ca988638dd97644c431c6eca3226218e3765951310c71bb2aa898863a5193634c431e2aa929a6218dc67294d310c733b2ec49886399d94624c431d48c83126218e7365d81310c739b28c098863ac190604c431da6c63026218ee062181310c61fba2c5280630f1d1629403187aed2a0a018c3f76550500c7172a4c4280638b5526214031c5ca8b10a018e2d54588500c63dbb2a0280639a5895014031c5cc9316a790e2d6498b53c871d324c1a9e438e59260d4f21cd4c5306a790e3a6458353c871cb22c1a9e439a98960d4f21a3ce9a9ca790d5a70d4e53c868f3a6c6a9e43569c36354f2187ce9b02a790c3d74d8153c862fbb2a629e431e9c06590f218f2e032c8790c7a7099543c863cb84caa1e431e9c26510f218f2e13288790d1d7494c43c868fbaa8621e43475d54310f21b28e2a188790e954358443c8678382c221e439354e62cc721c38c929a6390e1c6454d31c8727298c498e439694c604c721cb2a63026390d94744c431c874ab226218e43741c1310c721ab4e7a84a190c7b7654050c861f3a6c0a9c430f5d36054e218beeca98a710e1d6454c538870eb24c629c438d5926114e218f4e1b2c8710c7970d96438872729ac521c431e9c26550e218f2e132a8710d1c7454d438870fb2a8621c43875954310e2195ee8b046510cac74582328872aa98c2994433adc1644ca219d0e0b226510c6e7694d3288675386c8194433a5c3640ca218daeda986510e1d6494c318870eb22a618c432b9d363c862195ae9b1e4310cea70d8f2188674b86c790c430f9d2639422187ae931ca110c7b7654050886e338ea729c43719c75354e2195ce9b02a710cad74d81538
  | 18 => 0x214131a72e9290a098c7b76548504c69dba2a4282634e1d15214131cd4ca290a098f2b54148504c7942a0a428263d290c5214131e9286290a098f3054cc4504c7b02966228263c6d523114131e30a9188a098f4b528c4504c7a42946228263565ce6414131ab2e6320a098d6a72190504c6b4b90c8282635c5c46414131ab4e3218a098d737150c504c6b838a8628263c6dd14314131e36c8a18a098f186450c504c7a9b8a8628263561c54314131ea0e2a18a098f194310c504c69dba2c4282634e1d16214131ab6e6b10a098d7371588504c6acb98c428263569cf4214131ab2e7a10a098d7271d08504c6b8b8e8428263569cc4214131ab2e6210a098d73714c8504c6b838a64282635a9cb6114131ad2e5b08a098d5a73d04504c6acb9e8228263c650f4114131ad4e5a08a098d6972d04504c78d21c82282631edd94114131ab6e6a08a098d5873504504c78ca1a82282635adc94114131ad0e4a08a098d6a72cc4504c6b4b96622826356dd23114131ab2e9188a098d3b744c4504c69c3a262282635adc93114131ad0e4988a098d2e7218e540c696b90c72a063479cf6095031a5ce4304a818d2d72182540c71cb00c12a0631b9c860550318dae4302a818d2e7298d540c696b94c6aa0634e9c26355031a72e131aa818d1e7018d540c68f39cc4aa063471cd6255031a68e2b12a818d3b70589540c69c382c4aa0638718e6155031c38c630aa818d1e73d81540c68f39cc0aa063471cd6055031a5ee4b02a818d2c72581540c69a38ac0aa0634b9c86055031a5ae4302a818e3960181540c61fbb2a82a063879d165d0c31c3acb2a68618e1d54587430c70eaa4c1a18638d5516190c31c3ecaa188618e1d6550c430c71b2a2c221863475d66410c31c3acb3208618d1d75950430c62fbb2a821863879915410c31a3eecaa08618e1f76550430c62fbaac221863875516110c319b0e0b088618e1d54980430c61fba2c1290630f1d1609483187aed2a0a418c3f76550520c637bb2a4290638e9526014831c72a9300a418e3a54580520c71caa2c0290639a5496014831c3aa931c8418e1d5458e420c63db82caa10631e1c16550831c3aa9b1a8418e1d5418d420c71aaa6c2a10638d5506150831c6aa930e6418e3554587320c62ebb08728863475d743d0431c3acba1e8218e2e5498b410c716aa4c5a08638b95162d0431c5aa8b168218e1d5498e410c62fbaac720863875516390431c3eca21c8218e1e54d8d410c70eaa6c6a0863879506350431c3aa831a8218c9e76d0d410c68ebae86a086387d974350431c5ca9b128218e2d54d89410c7172a0c4a08638b5506250431c74a9b028218e3954d81410c71d2a0c0a08638e5506050431d36863028218e1e5458c410c70eaa2c620863875944310431c5ca93166218e2d5498b310c7172a2c59
  | 19 => 0x8b00a498e2e65d50524c636bb4a8292635a9c25414931ad2e12a0a498c6f76550524c6b5b82a8292635a1c15414931c5cca2a0a498f0d73150524c6a73ac8629263c31524314931e18a8a18a498d4d73190524c6b3b8a8629263591c54314931e1a86218a498d2f744c4524c6963a262292634bdd16014931a58e8b00a498d4f73580524c6b3b8ac029263535cc60149318f6e0b2e8498c7870597424c70e2a4c7a12638715163d0931c9cc7a968498e3454987424c733a94c3a12638d15161d09318f6e0b2c8498c7870596424c63d386caa12631e5c365509318f6e0b288498c7870594424c70e2a4c621263871516310931c9cc62908498e6452986324c71a2a6c2992638d150614c931ccea430a6498e1c5498f414c70e2a2c7a0a631b9d662d0531c5ea93168298e2c5498b414c6363aac5a0a638bd5162d0531c58a8b168298c6d76d4b414c636bb0a5a0a63479d64390531c3ea831a8298e1c5418d414c70e32a86a0a631b9db5250531c9ec7a928298e4c63d49414c6373b0a4a0a6393d8c5250531c98c62928298e2f5498b314c7162a4c598a638bd5162cc531c58a8b166298f245414b314c6ad384a918a6387590548c531c3aec2a46298f0c54d4a314c7862a0a518a631b9ca64d41318dae5326a098d6a72953504c6b4b94a9a82635adc954d4131ad0e4aa6a098f1973153504c6ad3ac87a8263c615243d4131e30a8a1ea098f2b54d4b504c7942a6a5a82634e9d252d4131a72e9296a098d3b7454b504c69c3a2a5a8263cad5052d4131e50a8296a098f18548c7504c6b5394c9a82635a5ca64d4131ab2e6326a098f194310f504c69d3a6c5a82634e5d362d4131ab2e7b16a098d7171d8b504c69d3a6c3a82634e5d361d4131ad4e5b0ea098d6972d87504c6b539683a82635a5cb41d41318f6eca0ea098d5b73507504c6ac39a83a82635adc941d4131ad0e4a0ea098d6a72cc7504c6b4b9663a82638bd526294131c58a9314a098e2f5458a504c7162a2c5282638b9935294131c5ac9a94a098e2e6414a504c716b20a5282638e9935094131c72c9a84a098e6a62d42504c734b16a1282630f9db545413187cec2a2a098e2f54d89504c7162a6c4a82638bd506254131c58a8312a098c6e76d49504c717b26a4a82638b19352541318dcec292a098e2f64149504c716320a4a82631edd95014131a76e8a80a098d3874540504c6b5b92a0282635a1c9501413187ee8b10a098c3c74588504c71d32ea828263c6dcf54141318f2ed2a0a098d6a72950504c6b4b94a8282631edd95414131ad6e4aa0a098d6872550504c71d328a828263c65cc5414131ab4eb218a098f1b5490c504c78c2a48628263c6d514314131e30a8a18a098e6a65d48504c795aa6a428263ca1535214131e9487a90a098f4943d48504c63cbb4a4282634e9d25
  | 20 => 0xf7550d52cc7862a286a9663539ce6454b31acee2b22a598d2e7498d52cc696ba4c6a9663c350c4354b31a5ee8b0aa598d2c7458552cc6b5b82c2a96635a1c16154b31a5ee8b02a598d2c7458152cc6a639ac0a966359dc56054b31cd2c0302a598c6f7654852cc726b1aa5a1663995486150b318f4e1b288598c7970d9442cc726b1ca4216639954a61ccb31ccca53086598c6d7694b41cc637bb2a5a0e638b99252d4331c5ac9296a198e2e6454b50cc716b22a5a86634e9d35094331c3cc8a1ca198c6e7219150cc636b90c8a86631b5da52143318deeca90a198c7b7654050cc637394c1aa4631b5ca60d523187eecaa0a918c5d76d50438c64ebb6a821c63659c75410e31a3aedaa08718e1d76d50438c78b38ea821c63659c45410e31c3ea8b088718cd870584438c70faa4c021c631bdd95214a318f4e1b2c8518c7970d96428c64e3a2cb98c6347dd165cc631c38c9aa66318e1e64553318c726b2cc598c639359562cc631ccacb3166318e656558b318c6b238ac52846393dcd6294231c98e6b14a118e677158a508c73238ac5284631edd950142318dce5306a898c6d72983544c697396c3aa2634b5cb61d5131a74e1b0ea898d3970d87544c697b92c3aa2634b1c961d5131a5ce5306a898d2d72983544c68fb9ac1aa2638bd526295131c5ea8b14a898e3b54982544c71daa2c12a2639658e6095131cd4c5304a898e6962982544c735312c12a2639a5896095131c9ec7b12a898e4f63189544c732316c2aa26396d8f6055131cd6c5b02a898e6862d81544c72db18c0aa2639ad886055131cd0c4302a898e7361181544c61fbb2a82a2634bdc95415131a58e4aa0a898d3b70550544c69c382a82a2634b9ca6415131a5ae5320a898d3a70990544c69cb84c82a263475cf6215131a6ae3b10a898d1d73188544c697396c22a2634b5cb6115131a5ee4b08a898d2c72584544c69db82c22a2634e1c16115131a3ae7b00a898d1d73180544c697390c02a2634b5c86015131a6ae2300a898e3454987434c70fba4cb21a63879975490d31ab4e12a48698e1c54986434c71baa0c2a1a63479d76450d31ab4e12a28698c5e76151434c68f3b0a8a1a63879d85450d31a3ce02a28698d6a70953524c6b4b84a9a92635adc154d4931ad0e0aa6a498f0d73153524c6a73ac87a9263c315243d4931e18a8a1ea498d4d73193524c6b2b88c9a9263c350c43d4931a5ce9b06a498d2d74d83524c6a6b9ec1a9263595c760d4931c5cc9a94a498e2d64d4a524c71daa4c1292638e1526094931cd6a5304a498e3b54582524c71c2a2c1292639ad49609493187cedaa2a498c3e76151524c71daa6c0a92638e1536054931c76a8302a498e3854181524c637bb2a4292634bdd15214931a58e8a90a498d6b70548524c6b4382a4292630fdd16014931878e
  | 21 => 0xf4ca18c0a8887559c64354443aa8e2a1aa221e1f7650d5110e8e3b286a8887871d94354443e2ee2a1aa221d1c7150d5110f8a38a86a8887c350f6254443e1a86312a221f1943d815110f35b16c0a88879a18b6054443c3a86302a221f19431815110f35b10c0a88879a1886054443cb486302a221e59431815110f0ca18c0a888727dd943144438eeeca88a221c9f7650f5010f0fbb28728087871d94394043a38e2a1ca021f1b7050e5010f8c38287280871ddc562940438e8e2b14a021e1d435865010e37b92c3280871b1c961940438dce5b0aa021c6d72d855010e4fbb28628087a350e6214043d1a86b10a021e95439845010f4aa1ac2280871edd9501404387eecaa0a9996355458454ccb32b14c22a66599dca6115332cacc6b08a9996677258454cca1fba2c128e650f1d160947328eeeca88a3996356454451cca3dbb2a0286651edc161952328f0e0b0ca91943f76550548cb1caa2c02a4658b5506250e32ad2e0314a31956671cca518ca3bbb2a228c650fdd16194232878e8b0ca11962e72191508cb16b90c8a84651edd95014232c72c8a80a11966572d85544cb2bb18c2aa26599d886155132ccee430aa89967361d81544cb3830ec0aa26596d8c6055132cd6c4302a89967361181544cb38308c0aa2659a5c8605513287eecaa0a89953471550544ca9c382a82a2651edc161151328f0e0b08a89962c5458b434cb0e2a2c7a12651ddd95114532a68e8a88a29957070544514ca3db82c828a651e1c16414532acce3990a29943f74580514ca1e3a2c028a651edd95014132a70e8a80a09957071540504ca1fba2c2282650f1d16114132cb4c6b06a81966a62583540cb2c39ac1aa0654e9c35495032a74e1b22a81943f76550540cb0eaa4c721065175da538c8328daed29c641946e71d95320ca3db82c9288651e1c16494432acce3194a21946c764ca510cab238a65288650fdd16094432878e8b04a21947776544510ca9d3a6a1280651edd95014032a74e1aa4a998c6e7218154cc636b90c0aa6630fdd95415331cccc4b08a998d9571d5143cc6cd386a8a1e63179d85450f3193cec2a28798d1e7615143cc70f3b0a8a1e63c39c85450f31e1ae42a28798f157115143cc68f380a8a1e63871506150f31d2a86b088798c3f7458252cc61e3a2c1296635a9c35494b31ad2e1aa4a598d4f7550e52cc7862a28729663539cc6494b31ad4e0324a598d697019252cc6973a0c7296634b5d06394b31ad4e031ca598d697018e52cc786a188729663599c44394b31acae221ca598d2e74d8652cc696ba6c3296635a9c36194b31ad2e1b0ca598d2f7458252cc6963a2c129663531cd6094b31acee2b04a598d2e7418252cc696ba0c129663539cc6094b31cd2c0304a598c6e76d5152cc6b5386a8a96635a5c35454b318dcec2a2a598d4
  | 22 => 0x800000280000008000000000200080060010000000000000080000000000003000000100060000006000000c00200000010004000800200300000000000000000000200000008002001800200180040008008000000200000000000002000800200000000000000000000000600000010012003000200000000008000001800000080020028000000800000000000000000001000400000040000000000001000000000020006000001400080060008000000000000000000000004000800800080020000000000800400780000000002001800200180000000006000000000080000018002000000200000020000000001000a002000c00000000020000000000e00000040000002001800e0010000001000000000040000002000000800080020000000000000400100060030000000000000100000000000003800c000800000180000018000000000000080020020000000000000000020000000000000c001800c00000000020000001800000180000000008000000000180000000002004800400080000000000003000600000000000000003000400080000000000000800a000000000180040010000000000000000000008008001800000000060000006001000a0000004000000000000051bdd95214a43cd2a4b00a521c6e729825190e36b94c128c874d9c743546438eeeca88a321c6f725865090e36392c3284871b9cb61542438dae5b0aa121c7b765405090f34b12a0284871bdd95214943ac8e2a90a4a1d68705485250e3bb8ac0292871d1c560149438eeeca88a2a1d64725445150eb8382a228a874d5c643145438dee4b00a2a1c6c725805150e37b92c3a82871b1c961d41439c8e2b10a0a1c7b765405050eb4392a0282875c1c550141438dce3310a0a1c77715885050e3a38ac428287591c56214143c9ee6b10a0a1e4c735885050f33b8ac4282871b1c56214143cc8e2b10a0a1c64715885050e37b92c2282871b1c961141438baed2a48621e1d75d954310e4f38ecaa1887879db6550c43a3ae3b2a8621d1e70d954310e8ebacc4a188747dd56250c43b2ee2b128621d94715894310ecdb82c4a1887661c16250c43d1ac43128621d8e72d854310ec6b96c2a1887475d66150c43a3eeab0a8621d8f725854310ec6392c2a188766dc16150c43b30e0b0a8621e1d751854310e8ebacc0a188747dd56050c43b1ee4b028621d8c725814310ecbb8ac0a1887651c56050c43b1ce43028621d8d721814310f4cb00c0a188727dd943d4843d2a8730ea421e95435875210eb338ea52908727dd943148438deeca90a421c9f7650f5110f46a1cc5a8887a350d62d4443938eca1ca221d947150e5110eb3396a3288871b9ca60944438dae5304a221c9c7650d5110eca38a86a8887a350f6254443d1a86312a221e9943d815110
  | 23 => 0x4000200000080008018000000a0000000001800000000000018000000000400000020000000000000000000080000000000800600000040008000000800400080000000008000000200100000008000002000200200000008000000000000080000008000000000600200020008000002800000080000028000000000a000000a000000200000060010002000000200000000020002001000000000000000002002801400380020000000000000200080080000000000000000000000008000000000a00200040000000000000a00000040000004001000a00400020008006001800400080020028000001000000000080018002001800400000000068000000000e000000000080000000004000000200080000000000000000200280000008000000000c000000800000000008008000000c0018006000800600000080030000000800600080040000006001000000200000000000002000000000060000000000000000200000018002000000200280020000000000800000100020010000000000400000040000008000000200080020000004004000000200020010000001800000000060000000006800600200040000004003800a001000000000020018002001800000080060010000000000000000000018006001000200000020000002000000000000000000006004000000000000000000000000400100000000002000000000080000010008000000200000000000000003800600080000000002000000e00000020000000000000000000040010000000000000080020068000000000000000000000000000000000200000018000000000400100000030002000000600000080008006001000a000000000080000000000002800a00100060008000000800400080020008006000800000180000038000001800600000080008006000000000300040000008000000000000040020000000000600000020000000001000000100000028000000000400380000008000000800000180000010000001800a0008000000800e00000040000000000000000080020000000000800000000020008000000000000580000010002002000200000000000000000000000000020000000000800000080000000000000000a00100020000000000000000080040000002000000400000000000002001800000180020008000000000200000000000002000800000000020010000000000000000000010014000000600100000010000000000600180020030000000000400100000000002000000200000000000006000000600000000010004001000800000000008008001800c00000020000008000800000000000008008001800200280000000004000800000000000010002000800a0008000000000200100000028000000000400100040008
  | 24 => 0x20000002000000800080000018000000800000180000000000000000400180000000004000000000080000008000000000400100020018000000000400080000000000002000400000060000000000000800000020028000000000000000000000000002000000000060020008001800200080060008000000000e00180000030002000000200080000010004000800000000000000008000000000000020028000000800800100020000000000000600080060010010000800000380020020000000000000000020008000000000600000000008006000000000200040000000001000a000800e0010002001800e0008002000800200100000000002000000000080000000002000000600000000000000003000800300060000000000800000080060018002002800000080000008000002000000180060000006001000000100000010000000000200000060018000001000000000000008000000800400000000000000000800e000800200000000008014001000400100000058006001000000280000010002002000200000000008000000000a001800000080000010000000000000000000008000000000000000020008002000000600080000030002000800600280000008002000800a0000004001000200100000048000000000000080040000000001000000100000028000003800600000020000000000000400100020000004001000c000800200180040008014000000400000000008000001000200300000020002000800200000000008002000000000000080000008002000200200000000000000800400080120008000000000000180000000004001800800080080008002000000000000020020000001800000000000008002000800200000000030008000000400000040000000001000000080020000002000000c0008000000000400000060000000000000000000020018002000800000000020020000000000200000000000000002800a0000000000800000100020008000000800c00180000020002000800000000000000008001800200080040018000001000c0000002000000000000000000000000001400000020000000000800000200000000000000000200100000000006002000000000040000000000000000000000000006002000200000000000004000800600080000010004000800400000020008000000800000080080010000000000e001000000000000008000000000200000000000004000000a0000006000000000300140000000002800200180000018000000000000080000018002000000200080020000000000000600000000008000005000200000020010000000800200080000000006000000200000000008000000000e00000020018002002000000000180008002
  | 25 => 0x350000538000000102600000000003fe000000275d8c05ed4ec0000e2f8c10000adc00000051e0001b9811d5d72bf40000000001f3c498e8e1560000370000002000000000047f00000000000002a140000003410000000601000000000000031a2540000000000000130b000000015c0000004258000000000000000000000000003154c67570000b8800000000008f07ea0000000000000000000000000000021980000001ec80000002361a60000000000ea717e8000dfb00000000008090006649b51c6c8eb0002a04000000000000180000059f8000b3e000000014000058670d0000000000038000000070b0000000f5e0001ee000171800069b785c000ead2a076a40007bd705352c00000065a80000000000000001c2a0004b5800000000000000000000000001fbb15e0000000000000000000000083322e230000000000000000000000001e80000000d2e0000000000301222c0003e80000a2720c0000000001348b90000256d83c0002d10000000e72589000000000000029d8ba40a8640000000000000000000000000000000001776b126d580000001f221d1aa4d7c00000000015a6b923fb1d743341c318a89bc00000035de85400000000011d800000016f9ae563e00000007c000008e8000000000000495501000066280001340000000001abcee6000000000000000000037a000000042a80012c400000000000000000000000000000000000000000000018408fc000051c00000000000000000000003068001632000000239989c4afd95000000000000000016820000000000000000000270425a1606a080018610005e100000000003e28001c4a0000000000000000000000051e19f8000b980000007261174cd20005d06a38c12a8c2acb960db897a749880800000037696e8746bda50c0398a6a0004fe0550000e3966c0000000000000000000088d558840200000000000000000001c536fc000cf800015aa0000000002c3a000d8a58e268000000000000000000006cc80000007dd3db044ce320000b342570b601100000b119000000000000000000a95fdce4c000000339400096e00022b85b79531670001ba6332747b1ac55aaf9000006d4220003f1a4be16a00067d00000000000000588f9847b00000014664ac8000fa0f160000002d48000000000000095e00000000007e800024c0000000000000000000000000000010c800000036196dc000000099e0000002d2c001ccc000000263c0000000000000c7639b0000000ea20001d8800000000025e8d54000b085ce800000000071f883096600000000003000000002094000000299800000000000000002d053a7379ba02488070002159c7000064b2ab0000000000000000000001380000000004c72e09202da861089a55561410008000
  | 26 => 0x4ffe00000000000000003d7355c0000004048000000d1a64fea800006a4000000000031002317c8000cdb80000000007f50000000578bdc019000000036848e05e83662ee23f895000000028c80012f8a72000000000000000000000001c14bbda3a0003c100000000000007350000000000620260e6e200000025308a044000000000000000001558b5c808707b079c800000001dd00000006170000000000000000154890c29100019760000000000000eab000000000000000000000000000003aa400035b800000000000000000000009c30000001014000498cf4400000033a8000000c41340e52c00000000000017f13c5668ace0fae26a800000065e000000121000000000000000000002aac0000000000002f6200000055f250600000045f800000000000036c00000005dfb8b80003fd00026a8da40002258af8b56e1015b2cec000000709225c0008cb0000dd4b940abcc0a7909280006b39b14f1e000000000000055812fa73939a00068e00000000000000000596a2c49fa06151e000000000000027c00000000000000000000000000000000018000000003ca04a00000000000000000000000000000312b2b0000ce400000013980000002964000e9b18980008525e860599b57326511c386ac0000000828000000000000000000077b00020bc0000000002278000ad6319000000000016b0001c95000000069000000000000000002da000000000000000000001e80000a64328e387532c9800000018e0000001c9c000000285a0003f90001130fb4942d398000c9688c00000000000003f384cee6025040f3278ce250cf25c60db400006830000000bbc00000004380181be00000000001a02d55ad60000b63a195b80ef5852eb0a42c82000000000037232c39a42acc8c0000ce5d220002ef95d0ba298400000000009000000000000000342adddc54000000000129c56000011ad32000054d800000000000009820000000000000000000000000000088700000000000000000884aea30a0002362000cb10000000000000000033ae5167914f6f5000004a0001ec8c460002f700007cec8a27c0001564000000165800000000009d05bc00014732820000000980fc6ddc00039e89960000000002c5400021b000000000000000000000000002f1ae1c00007800012e0000000617ea8200079a00009fc000000632255400000000000000000000000000000884a8a800000000000018fc0000000000000000000000000000021f28208b051a25780000000004b000000004c80000002c692fc00052a80000000000000c440000002eb121cafe00030320c800000000000000000000000000000000000116cb6000000000000003d800000000000005078751208bbc80000000000000000000000ba20000001b2c1281628000e244f1
  | 27 => 0xb5400080400000000000003ab000000000000000000000000000000000389eff80007f60001d396717283ec06712c439641680000015ba0001bda340000000618ab040000003ac1aea00000000000001e0000441000000022f13c3668000bef6bcafb40e8000000000000000065f80006fa0004590000000e77000000050000000000000000004e2800000083569f80004cdad0c5102a392000027d2bd0cc8000520800000000000000004178ba000000102c0000f78001b3c6a212b1001bc0e09000000000043648f000000000000011bc000000000000063c00002dc000000000000000095c0e924cccec00000000005c8bb60000ed96640002a7000014400000000027d4e802f800000000000000000a5c000a5600000001dc000000250c000c430000000d340002af9ab000000000000000002ab0000001a2ca6613f18b14a60002068000000e320000000cd014837a8000a64dfd00000002978a30000000000ca70002d64073466536b6dd6300001eb000000000000000000000006e88000e2a00000003ee0000006d79688750b5100000000000000000000e8a000000000000092d0000c5c0000000000000000000018902ac001a74cf19bc00000000000000000000000ae80004566e78000000c060cc1e5504e0000000000000000000000198847f8000001aca000728000003c00000000002ba7380000000fc20001d0000119700000000000000000000000000000000000000000024680001480000000f340000000000000000e900000000000000000308cc3608c00000001a23b3000000000000035e80019acc890000001c520005b40000c7800000000012600001df800127d0005ae35c84c7000710b4c8a260000001a9c0000004acae3d5c2d5a4b1b00600000000034d80007d880000013be0000000000000817000000000000000002601c200000021ec0000000000f5c00000000000000000000ce0000a020c76f28319278000000000000000000000002560000001dc8000000000000000000019a8000000e1e00000018ded0f27a89660000005c7d80c2e90003b18001c29a64013379800000000000009e8000000000000000e6d60928000c10000000000000000000000000000000000d860000000a668a800014f85be0000000c68f214360004623a08000000000000000000000020a200000001000001ae00000000000007de00000017f096800000000000000001ef800000063e233c00000000000010720000000daaf760000001be4000000146000000000000000000005500000000000a3d00000000000005e6800000087e02d00010dc00021b92380000000000000000000000249d291000122800040d2161b200002280001ed0aa177c000000000000000000010ac0005fe5d380011e8091143148c460bde6e2005
  | 28 => 0xb00000000000000000000000000104600000000012640000a7d09d0d04e200000019f64a162d1527be0518800000014d000000000000018c145b7dd50e00029bb5ec000cd400000000000003cf000000000000000000000000000001b180215d82016ed0190000321400000032d4ddd67c0002790e98000000000070148a00062a9c080000f572e00000000000000000000bab000000000044f5a32f1463258a481172400000075b000131a0a500024cec18b4b6a100016d40003720c90000000350b07c00000006b0cb800092ccba8000917d260000454e2290500017503d6d7015c8000d26ab18001b5c000ac600000008260005a8000169c1d6800093c0008f800000001ee00014b41d40000000000000d0600000000000008fa00000000005eb0001ec1722b2c000000136a0bc00000000000000000354000785000344c000c011265524ef43be0000d8800025e0003330000ced000000000000000000006a80000000000000000000000000000069800012c200070880c000000000000000005f40ca0000a5497b4fc1dda0004ef0001b69ca489a0000001d28000329800000000000008443aa000000000000000000000000005cd0000001ab60006b0000062800000009c0000dde7124f74ca8c2b00000008df00000008e8000000000000000056b8000000000046800000000000000000000008f100034340000003dbc00000000000024ec52cb27000059ee443da800331c1da41380015c14760000000001220d9403480000003b416e6c18000b794c880004adb980dd8001516a8d00018c000071a2d61fb000008d000000000000000016fc1fc0bf28e1c42dc0000387000113e0000001b2879ed478b5eb5db680000000000000dca6e584100000000000000000000000000000000000019e09949fa1c19d10825000000093a5e8000000000000000000000000000000001550000c7646a000000000000000002e6000647bad0000dbb0000000758000272ba94000935bd200000000000000000000000000092c00000006e800000000000022b136e000000000000000005556d86f2d2f37f95ac0001a5000000000021700009920000000001e58000000000000000000030c27c0000000000059c000095000000000033700025a4b4f0000001ab80000006430001c000006ac0b700920003393378510d0a00029622da00000000000000003d48001764979c6e3221a1883a0000000000e60640a2d4000000000100cc4800000000000008bb00002a8c9800000000019b68060000001a6a00054e80000002d2000293cd92000208b00b26e0000000000926df8000000108400040100001610002970000000d4a00000010fa8373bb0000000dc200000005a809251580000000000000000000000000000000000059fdf94ea800000000000c000
  | 29 => 0x14c400073f8a11924000000000000000000008600000000000000000800000000085a0000000000d3c4745d48000b220000000000b1600025100011b69472a29edc0000002affa740000000001a20000000015318c7fc80b00039740007ce000000152e86a36780007aab710001ee0000c8b0000000000000000000093f89200018f400091344188380002153330000f490003a7af2a000000422afc5c7a0002ca80000000000000438aa10004cc905fa360006cc30e1bac00000005e013400000000000008d680005ba000d0330b000082847132e206c4a30001769dbc000000000041c000000000103c0000005e8c0007b20000000506d62000000394c0000000000000000d1f5ab29b0000000000000037e1d92af2fdc00026b0000000000c595ee4000000ae00000001c339b580003f4610928c2d026c000000000000000000000000013410794360001b5400055d04e80009ab0000001148000000000000000000000001760004d26ce4a1b000000000000075262880010680004a7800000000000000000003fc00000000000006021ee80000003c98000000c283b30000000479000284c00015000008fc00085f80000000005d00000000000000000000000000012c8000000000403c00036800040728f8000000025ed7400029b000000000000027800018ee000000000054c000000000000099401fc3d83ba2b84f0a8d00000006b40596544e61596a1e403818dcd4aa08fe620f57187440ec59d244c000aa6b7212540000000006d9800001295e00030d000000000020fc000000000000000054f759800117052d1ea339c4c500000000000000000003a59806000000000000000068480000000002fc800000000000000011aa5274ea00000004cb671400000000008ba3a4a1a12a02718200009f10002815ade00028281040000001ab000049a000000338958e0725b5b7e9b4600000000000003e000039ad0800000000000000c1500021b521c0000001acc00000074680015eab3200000004bd0002d8a5c0e5e46a3493ad212e00062f15c9490e0800fa455b480001248000000000000261e000000000000000083000000000000003ce80000005c2000116871e46929c800000000000019e83ca0000000000f56dea000000082e000113096cbcc000000000069e00000000004a10000002b0050e7c4000037d8dc0000001508000b340000000000e6449a2a000000000001838000bd80de0000f45d2a5432298d9603c7340000000000000000164600000000000000003e0a71d9804b500026f10a642a000000000000000000000009986331575438a5e54500018f6bc7000140c0000000001a600000000000001bc6d2b00000000007f80000000000000000037ae280002d514740000ae45501b805c2378000001934d0800009
  | 30 => 0xe76089124600016a8001a386d30000000fb495a0000fd8000000000000000181a0000001e080004c800000004b875c000000000000000000003cc0005252e9e00000000025282e1945302b80cd0800050a000000000044880000000001cc0001a240000000b34000000654000145a00062400000006a60000000000c05000115c76e0005d400008ce56900019fc00000013b800023256a000000000000000000000000004d880001860000000001c8c00000030f800000053a80000003730b30000000000000000000000072528c8c3c40bd1b00008c50004f780003749e71028b6c000821000000000000011f3ac400000000000000001d30000000bfa00000000000000000000d6586aa5b0f502f5c0429300000002b100000000000000005dbaea81704914f30000794dbd4568000000000000000000000057700000000646132fd4dc600000000002c90cf5c09a7d54e000000364000000043a20980004c54028000000000000000106200006c96ed0920000000001a7c000000388c00000000000013ba00000004bc0001ca4a100014ca00000000017c47ea44280012ec0005bb21841054650000000f720000002ff959f120d998000398a880c39a58e58000000000000000800029f000000055184fc00000000000000003310002b98000483000000000000055980008160001bf00004710002c8058c92ce075af80000000005768001c28e7a000000000000000000000002fa800000000000000028360000000000000000a0800000000000004c60e84000000000266c00000000000000000004804e554c0e0c09caa1147300007f80000001440000001cb6e284de8000bc4e4970f80007f000000000000000000002e980006c20003a8d38c00065184600000000001f4db360004fe9b9c00000000000005de000639309c000000465000155e00000000000008524d70001700cda00000000000000000000000000000000000000bc2f00006c2000000125d1da59229600005aebc8d9e39d553407307980000000000002dfc5b00000000000000d84481978400078a0002654000b5400030480000004b6c000000000000073400000040f80000000000000000000639000000000082400000000008d100003e046d6f200000000000000002ffb4095186a78000000acb0ec0000000109000000043c162c3c053a0000000002f98000cd50000000da600055e8c6da89a2775300000000000001dac00001201d637c00000000017ec64aae94080c992e3dd9105b6f9083dc84b2000000000000000000000000000001c36000062000000000035f800029200056880000008dd5259330000000204000139000072400000000000000c3c00000000000000009ec000000000005d0000000f0c8950500000000bd6000000000000000000000000
  | 31 => 0x44b0000d12000583af4b48600004f8000000338000000126ce89000005600000000014300000000dfc001a2a7d600000000007170002a940000000000000000000000000000072a800000000000000000000000000000000b8077000000001b80005a4afe400000000024b81c400000010c80000000000000000227000000000000020a8000000000037800000000000000005ee0006a480000000000002a44000000000000000000003f80000000000000000000384272000032603880000000000000000e34e0ae7c0e800000cc55c0693328000000000372489c239166000156a510000278e000d1e32d9b99c0243d1f880001422fb4474000f6a1be3eaf4400006fb000000137cbfda4600009ba0000fb0000000391514a7b989200000012f00000000001dd400000063f1a400000030be00000000000000bcd3c951a000159400000000034e80000002ad8000daab752de0000698000281143a000557000000000086505d00014c200021800001a3afa029800000029880000016560000001b35d34abb000000000000000000000000000000000bf82c25c1827400000061200006120000001974000868e0c8000e4000047800000000005e9ac00000be83210000000000000000000000000000006780004b90000a6c0000002b30000000000371400078925b800000000063c06ae00000000000000004378000000000000000000000076a0000000000000000000000047c30a000000000043802b182900069ba0340000000000000000254b308001652de900000006bcb100000000000a0b3140000000000000000000000000000000000000001cfdadae7b000000000000000000000003e6000358400000035e0614000000000000000000043f8000db7aef00c5bad30455980000000000002b08000000161cd280000001ee0000000000000000000000000000000000004c3123854400000072d00000000000002950fc431d45f00013bc00007e036f22e00033700004ba49b2a0236800000018280000000000000000000c3c00033c90340000388000000a0015a8000000b165692a0c0000000001c300000810000000b000002fb000000081500000000009ff00000000002c61fb40016b60000000000a10000000011400000000000007f40000dddc0c000c0a66bc57c0000000000000f4059a0f2000028600000000000000000003698000000000000068e00072a8470f280000000000000000075000000000000031195b01c22be0000000597000299d4540000000a7e00000007d0458000000000000000000000000000000000000000de800000026fd4e20874eb7ab19ea8fc0000000000000000085000072d000000133e4485f63535c880000000000000bc10002f8c0000000000000000000000000000000062b00003c30000000
  | 32 => 0x1062b8289b0000000018416000048bb385ab83f18b40001d39068000000000399ac780000000568001242a7a2608000000e1900000014d400000008d400007b0000000a1e3db00025600000001ef0000cf8924000071979230e000023cb3c00000380000000000000d19aea5a344094ffb1d00054a9178da24a68000001a86157454800161a0000001b180000000000000162000000000000000000005286ae00000000000003925fb000130c00000000000000000000000000cd88002f32712406346067800000180000000000001ccb5fd4b402f0430001bc40000000000000aa18000748604a5c00000000000000000000000af800000000000000003128e0e0000002c100000000001128df900000000000005d7000000000000000000003f85fa00000000002a3000000000000000006ca0000002b7800069a8f30cd922a1d079c4c14000000e78000000000000000000000000000000000000000006a941275292000025000048200031a4000cab000029c0000000002d800000000001dfc00000014e80014740000000404000428000000000070132f80000009975a791656da00026300000bea0449d328400000000000003080000000000000841000005e00000000000f8dd4240000000083855e97040018fe0001a9069e00058e000255800000064ca1ac0000006b30000000000000000000000011fc0000000000000000000000270800000000000011358cee052189a640000000000000000000285b64c0007c70002700884e6c000000000c27200000000000000002220b860000000000000000245000111c4fd5ba000000002689c00000005674e52d4c8880006dc9929d162fe5a3a7700000000002f312f10004ed8000000410000000000000000000000009ae800000000000000000000000000001e7c00000041d8270de6000000000000066a21e0000000000000000000000000032b80000000de8001d10bdd00012e8000b9f36e80000000002e58000000a1a6580eb5a8b0002f5218000084300000007d40000000000000a418000000000000472363400000008600017b60000000000e465e96c351a0e620004d98000644000036c0000000004c4400000056e800185c68400000000000001d180000000000000001627996eaf00000000000001e70000000000000000000000000007e83544d90003400bf0c3d000000000000000000014ff0000c8aff0000000000107d19a9388002aa82aa4ee000000028400000000000000003fea829b1e0000d0c0000000000000000c8a000000000000000003e80000001a900000014880006c936c4000000124c00000046c8002f3a0000000000001c08cb700000019bd0001ec400000000000000000004fe72f2b28e52000000268c0000000001232d7400000000001500000000000d16
  | 33 => 0x200000000000000000001b040000004ad99dc153000000000099a7d20000000000b2f00000000000000002ab40000000001b84000000000000000000027603c4000000671800000000000000000001d48001fc80008f909d800000000074c000036eb262e440000000000000001aac10000000000005c6b9e0000000000010dac98e20005f20000000000000000000000000000000000002f380000000004bdc000e868c05384000af6004b5c30bc00014580006d80000000000c80000000000010c0000000000000280000240c0000aabd944c0db400025342380000000006ae400000000023ba33000000000000000000000000c9c000cce000388986eb57000000000000048a000000000000000000000000001bc4000a492aa869b3123e27199ab5b7800000024340000005e580000000004bc047c00000003d000186c000000000016e00039a0001648bb900000000d43ff26480000000000ba80000000006328000c4400000000000000003fa00000000000001be8cc6a5f00032f5a8e000000000025c95d57400000003f000000000000004e5800000000040e00000000003240000000000000000020c000000111af420470fa80000000006b1000000045c00028802d4000000000059eb85344e890c167811dd4001986d870000a68000191800000000000011590d0000000000000195252f51b960400036f36000000000006531a1c80a0000001e8c0000004f93ad433e00000035a83eeba500000000000003e300019f81a3000000169000000000018a8436800000184a00000032f0000af76a36986206000000000000000014180002207c80000001b2a5f3000000000000064f80013880000000efe0009a580000000000004950001ab30002a0800000080c43b9d6800015200000000000004d333dc0770000000000000000000000000000000000000000000000000000000618c000000ca500000009320003052b243c41960000ad14de00000034fa000000000000000010f0000000000000340a06400000000029444ea2f00d40001cfa00000000019480000002bc800032b26a000000000015800000000000aa65680007fc22f84b1156cb65bc26686b800028a000034b000609c00000000000000000000000000000e2000072f80008c8d8260b05f855c00012e5c18f50aff1c9a8d400000000000002780000000000023000000000000000000000000000005f980011ae5305a1000000035d014800081400000000001c100000000000000000000001bdc0000e2a81a0000000000e79adc159694800000083e000000118403b00000000000004478001150000000281c0000000000000000000000000000000000023fc00000018e00000000005b8042cc5e99300000001320000000001af8c3234a703daa01b9497974c000000000
  | 34 => 0x97900032100000000000000452000000000000000035ba7cd09c0001c4000000000000013791a1000000086800017700000000000000000000ce028509905fc7720000000000000ab03dc4000e9cc3a000000000000000000000000000000000000000000000000000007c8000000be1000000000000000034840000134d2109800073b4918000000d250e70b900000d0000000000025800000006520000000000528000000000000084a322379cada0001f2000038300000006297bd0000001d3000004800000000000001d70000000000669000000000000000004640003ad800000051f1ebc648484000000000000000000000000000001232754b7218f084000060800000012fc0000000001cdc92a5b7615000000000000015e543e93d81228c47c6000075a2749d08ea6760000000000450afff59c00000000004dae978000001b0623862580000008b0094a59c3321cf5940000000000439050e0000000001c2000072a0c480005f400054f80018d4d805b399abc5654d00000000000000000000000d4800018d862c0006fb00001b6000000000106600000000010e200000024c4000000000000037d1488002d60000c020001a94c348c6750800000000000000000000003ed8000000dd80000000a400000000001a501310001a008e429b9ad1ad400075e000000028f00057f0fbc00088a0000000000b860003a6400064935580017fe00000000007442eb5509079b8e0000000000afb027c338b20ac8a56ab639f800047500000000000000ceaed00000003bf0fde000e70000088c120000284aaa18aeb436fa03fa0000852ad0000924e3700000004400000d24000a4100000003c800064d42c1d9400000000025d0000000000000000000000000000000000000000000000181b3a00000002458000000b6c4458000000000000000000000000000000000005e346c53f6000000034c88c5c2800000000000000008757082480003890000c7d0000710fdc0000000000000a9000037b0be24190001c2400000069109c4e3b00000032a800015680005e4000000000000092100000000015d60005d2000000080f3ea807e0000004af80000000000000b0d57e98d94c800000000030a800000000000000000000000001844000000000000000000000000000000000002a8800000000000008923f700000000005c9c638000a0e00000000000006e2000000000000000000000000000000c8c0000000000000000000236c00000000000000016bc000000156221abcf250717000000058611e800000000000000006d6000000000000000000018e6b8b1a50000000000000017800000057297dc2370000000000000000000250200010a00000000002b3000000000000000000000000000001b7c0003c700003347d
  | 35 => 0x9f92e385d14a40000000c3400000049f131000000000000000000000000a540000002c100000000001ae600d47e00000000000000000a6b880000000000000000071b0000000000c0e0918000000000000000000038500007a00000000000be20000000003044000a0300000000000000000001c5f00000000000006fe00000000008b756200000000000000000000000000000000000000036d99d40000002744f5800000034b40007a6000145c000000000078487e50e2538d41ab8bdf80000000000006888000d1eb1300018640000000000b291d8c22000000000000000000002960000001df18f22e18f880000000005989d88000000000000129200025b04d4468d5d00000000000000000c180000000000000000000000000000000000011b80000001d9000000000000036c96fc95c0000000000000000000040900009559d1b02ada636b7b4bba03a74ba4a73c4000000000075200010437400000001c58001a5834837e000088a0000002cd800000000000000000000000000a520000000001a706860000000000000000000000000000000000001d280000014fc91900000012a80003b8a0a0000000000000000042028b000000000000000016e60001ada3d8000000000306a000000125c5193440006678000000b9a1d525b0000e2c00000000000004d3412c2d1da756fa612a732330000000000658d8e80000008e501c94f8eb20024890b843aec0c0f68905b100000000000ffcc8000000000f72f52de8000000000713afa463498830f8000d88b3a4d08000f20573000000000044fd611d90000000000356493e01ece91db8b8b9acca203ec00043900000002bb00074180001b48cf800000000000026d37ed8be0000003511be600000002bec400000000000000000000000000000000000000003918000000000000000242000000041133040000005ea8a900000000000000000000000151dbea00a5d00a85282d64800338400000026780019fed1d0ae05b80006730000000000d19000000000000072b249e6f0000000000096700052cd6d4000000055b2e8000eb0000000000000000ca809128a1d62920a80f50006af4000000000000000000000000027d0948d7100b000000000000000000000000003874000000000198e00000000000009a222500000000000000000000000000000000000000000000014809e81b4701cb1a0004a1c0004ce32c00014f475e00030e9c5942c00020d0000ac400000026e16ca33e24f000087015326c0a600004be3de1a70000e0d00000010249c7a958e3958a000675a7dc0000003df40000000208d00d7c0000002fa958d0a20364c937ac000ab9000000000000064700007880001550390000000000000000000000000012cc03300015996c470ea44800035300000000000007b180
  | 36 => 0x71e44990b00000002376f4400000000000008a60001039f240000000bb34d04ae0003f328a0f66bd7389863b5cea765db40012c000041b1f40e7451b2c9e47c87c000000078ce960000360001d706aa00037e400036c255000032a0005ef8001aa2000000000060e0000000c7c0000004bf93acb640000000000b9e00000007580000000001a6c0000001528000e8200062121a721248f2f7a121d4400000000000002fc4f28f48000830800399c0006bb0000000b890000000000000000000195caa200000026e56f844e800321ccd6000000000068a00000024980000000b58000000000000000116200061980000003f64aba4e553c0ec00004d0a0c0a60000001cae00000002933ec77d00002521430000000000000bfa0000620000a121f7000000000000000000000000000000a9f00000025b400000037800000000000000000cce0006e7000000000043300003d8000000000000000000000001600000000000d680006222ebc98400000000016360001cb18dc0000000000001266cb80000000000000000000000000013d80000007aa0000000848d050000a83418ab48000cfdce672e000000000000011400000000004f495c40000562a180000007eb0000000000000000000030c381243d428000d39000000000054b00000015d439f5d1ab877740003e88e300000000028000eced0e47911c1bf78d60f480000000004160aa406ea4d7450000000eae36800000009da000000000000000034900000003a8000000000000000000003f3000140183a000000318941a3a51e98001be40001330001d40d5f80000000000000000000000000604acd4000b110000001a080000bac000000000000358c000000000000000000000000000007ef0000000000d9700000000004ac0220e0a0000000000001c9a00000000000000005cf4001780ca24089e64b066352a92ab85c50000000000836d731ce81b40000000001904796bb500024decbc04f263aae1cb21518c58000000e9c31d00000000000002d28000b93000367c0000006c580000000000458000000e6e00000007f10004398000000000000000000000000000005760006ce80000000000001c3e0005a7091e1517e4dda000039c2850002798000000c931290000ec200000034500002c70000780c9c0001bb1074412d020000bfd44ca222d78000000000000000000000023136e0b660003d6956f2deaf6000000043200036700000002240000001b5c3bec95d521524bc358109a04027424d40d100004a78000000000ae400024d5b8c0004f194ef9ec00000029be000000000000000000021100000000000000000f967f00000000b8800032a8001216d4e0002974000000000000038b000000093f19c0003f019d8c0e00060b80000000000000c60000a9365a12d00
  | 37 => 0x261435c0000000001140b443fc800000000066cac240000000001ecbbe284d6c49d800000000000000000c140000000c087df02d9c01c840000000000a3c57a0000000000000000393d08c0a0a74ba0000000000000000000000000000000000000000000074a3218a811ce0004b8a9a128c00000019b00000005f38000000a701c312c8000627374ab410020006f21cce23d0001de880c0000000002f8200000000002c8000000000288c88e0000ad8000000000064a71ab0d4a963a80000009656fe000000000008f000185a0005c5000000000000030ec144000000353148e535800000130000000015f5a0200021da3156020000442fa8fda2636101e6013c022393ba9085c000220a4194d280480035b0000000000088800029d81400000004d70000000d8ec58000000077400016c800024e00000000003fc0000000000000da500032440000003b6000000000000000000005785dfd152fb200022c000000000026d8000000000317139d8100000000000f1c0000000000b8c00000020ffc0cc5b5cd800000000000000000000000000000166000000000000000000000015f60cc0a340000000000000000000ad52e600008e100000000016fa8f70318000000e0e00000000000000000000000000000000000000048c000000000000005300004f66a2b3980002f90000000e337a244ca6f6000b214be80010a00002cd82d9ba800049400000000000000000000150930800036000024e12ac000000000000000000019800000000000000a1a0008fb0410b01baf00000000014af0004348000f18000517956abd800000000000007f14770a5e11cbd27259359383010000000000000000000000001254960000000bc780031740000000000000000b300000a6b269acd000000000098a0000000ed24508001a5593ae7400000000000000000ef000000000037f8000c9c469000000000067480000b000003400000000003fd000051426e00000fc8aad52000000000000026e00000000e06669e1dabc0000000001b820000d79de18a60000000001cf200000033f800000000000011c0aa62a2000000000000000000009b4000000000000000000011a6000319800090900000000000000005b080019e0650709bac97ab5538000000000cb200036391bc0006eb9a5024c0000bbc00000000000013b4c244184db000000000000013413a000000006b40009ba07ec00000000000000000000002f80fc80000000000f189fe0cb36c8000000000000000000000000009390ea1e7000000105212100000000000000002eb50ae7e800000000002c90000000000c2c5170e400002c408d00000a7c6839215280000000000000b309253a680000000000002c0c000b902c2ba145027a0800000000000060e00000003341b280000007280
  | 38 => 0x1c94c4258800000013062bd3c200017fa00000033203bf8b66d08000ca40000000000000e3b0001ddc000000000000000000000000000000000000000000a5869980004a500000000001000000000000000000000000000000000000000000002928000dbf36601a1e9ccca6ec5fbf90416562b6e6a69c682b2000006de3fabe000024f4000068800000000000071f22cc0eead42d2aecc00000022935d8000158587a8e00003693540000000d2300000000008844f02b645d00000000000000cee060b460d3ab6f000262d69ac4c54c8000946c450b2100200073e000000000000000016a000000000032e4046d88800000000058f1e0f54d95ab2e6ee80000000000ef9d18000169800000000000000000000000000002a50000b4029f8000dde00037c0d2440c9ea12d2ad00000000002f10000000254000000048000035906860001398000000b880001e0000000038c351800000000000019ba00000000000000000000000e6400000010d4a229480000000bca00000033c571a00019e9f09bf30006ba0000000000080efc0d1ac7a5f7051cc4c2b203e11f46c67a524d000080700f00034e60000000002170e42b1400000000000007238000000ac30000000000c8d00036d400000000000019a600000021ae2445a63e180004a200000020b930e6d856f0cb42de3970003a78dfab174ceb7bcd2e39c0000000000e950003554000dba72880009760000000a246749b011680001bc797471901dabe0000ee0b750701696d108f400000000000017f990755b83ce0111f90000000c73000722908d71c4866798c2c94c30c000000001600005f0000000880000000000000064b984da6271d43b04d8000d200000000000e354eb16e00000001f2800172e000000000000000004984812340001e1977800000043789f40000000000001b5a000000387000033607a53f00000005640000000000000030800023600000000000000001f0000084f1f58000000000000000000036b0000724000000000000029c0b953e80006423c000000000000004e484dc0008e853b800160a6475798c48000c294310000000e3c00012ba00000012185b317800020488280840003189b6dbb800051ca80579000000000000000000002337280d69000000000000000002251ea00047e80012d466481e800000000039a9fec12ccc224082281075ad00000000000002f000019e80a90002388000a9653fa4596b400029a000093a0000000000000b694a692940000007388e50aec00029c5630fa900000035f45c0000000000135ec94000207400000026a80001b01f369d8000000bfb00000000000000000000000000000221800000000006eaadc6c800000014127ca0000000000acab2d1d7d95e0128000000000000000068800000000000000000000000fee
  | 39 => 0x33129187009d5c9c0000000000000000000000000016100000000000000cc00000003185d080002b4355000000061f80008da00041e9f349c6b6600016a400013d0003060000dc300022719ae8a71081a8c00000000000000003c957600003025d563a000050482000000000000000000000000bb800000000000000000000000d7a74b40005d4a1e00013800000000000000e29000000000000000000000004d4000000000000000000000015c4000452800000000000000000000000000000000000000000006a0000bb400000000000000000000001f09685c2c4c000031c1af00001db1768e6c2d0244618c000000026110ce149fe5f58000000000000285c0000000000000b8aafc0000001cc4cf900000007600000001339bbe0003ec2c948182618da80006b0000000304c0000004b98000028000000000000017d00000000000000000000f060001e6000000000000013e5c3000000000000000000000000000000000382c0004a00fc0000c54084100073e00065900000000004b90001764a50bb15e818e124403841582d000000000000000000000000000d22b6352700000000000000000000000000000000000000010840000000000d440005dc00000013b22e3de300000000001daa9ec0000af6f04000aa500000032cc000000000000000000062380000000000002bc44c01700000000000000000000000000027518a4b0e488000099400000031f000000016107e60f0c8ccbe0000000b635ce0003898f2487a000000000000000000000000003c8800000000002c80000000000000000000000022c0000000000002a1a6000005e700006dc36700000000000000000000000cc600000000000000002816000a782df1ac08c667d395957623954c20138d0e1e6f7000000000000075400000000007490000000000041800000000036609d8000000000000000000029e4001a80000236019ca2400038200000000003d8b3400000001950e9183400000000000000000000a4020900009980005c6000124667a66636000000000000610000001214000386a8853da5b4512a32400000000000007340000000000000e301a70001b0a10580008e6000000000000000000000031b00000000002b6c000a1000000000000000000eecbb000017dc0000009291b80a44000192bbc8849a16c953452de959ed7700000000005260000afc00000000000000000000b880000000000000de9578000000000000000000000015e000045c800000000000000008c20000001f47d6e0000000000000000000000000000000029b80000005c480003a100000005140000000bda74cc38dd513d00001ca13e0000000b8f29c000028ca78e810001e6c00000000000017942e706be5dc3850000ad000085ed3d0e406b0000000
  | 40 => 0xdb900000000000000000acc000000d3c000390d484ddb58593dda4e7dc3501749168594000000000000000000013d600012d4d2c0c40006e90000000000000b5f84626e500000000000000000000000000000000000021300038b4c9e95200039b48f0c3950c800019000000026c80000004ce0000000000000000000078d64db3bc00000000000000007480000074000c3000000017ca9510000000000b95102000167a000000000121e00000006c814f2f6000000038dbf42399efd23a007800000000000000000000000001ba000000041200000019fa0000000dfc00000000017fd112000000000000000060d800159315bb8f800000000000000000005a03a39e2000000037d40000800001efb9500000000000000a48bd38000000000a7400000b40000000001db532c00000021ea304e6500000000009ad000014956c000000000002e00052b800000000000008a99be401800000000055c80026b000000000000000000005db000173c7b40000000a6200000000000000000000000000000000137c000dc012a800166eb220003370000000000000077000000010945e40000002d300000000000000000451c3e00000006023ea062a00000db47c0000000000000000000000194000000000000000002ca0002bf0000000000000000000036b8002d140002ec0000000ea500000028c000085f000000000000000000011b2e9f000000022200000000c200000000023bc000000000000177a000000000000000002e39c84810001728001d0e000000091090b00071880000001da33f00014f2000000000032eca0000155a000000000000000085900019580000007550bc46a600000000004f282d587000000053480000000000000000000000920000143e00000013109ca00000000016901c6000000000000000000000013f11a100029ac021000000230d6f62b1000224000000000000006d4d8c8001b79c749bb0003a315a9b8ee4c2e700004512d4c0000000004708e080007e449581ad9c0a0e6268b4c0000000001fa4aee0005d0a3616c867b0158eac0004e60000001512000000057972c00000000000009cf145400000000054e000000000000000013843c26f08778dec8bd0000000000000000000000000011d8001a2ea4c35b000000000000000000008144260000000d91422000090a00054ac000000000662a4db40c00000038bc0000000000000000000000000000000014f00000000000001d55236000000000000001a0000000000000000000055e0650000000000000000398c0000002a7313c2a72f7a4800000000000000000355000000040846e0002070b0400000000000000005e40002aa522200042e8000000000200b41c29e1c700025be0000003a48001a6f54600000009f6000000000
  | 41 => 0x2a6000000062800009a6000000000000000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1310c421ac0815c06354021d08741cd5014021e0a6458d5014021e096458d5014021a4a8758d5014021a488758d5014021e0b7458d5014021e087458d5014021c63761c55014021d40731c55014021e41631c55014021b05819514308630d06541c54308630a29841956008630a29841956008530e41631456008530c60721c16115030d06725c45450c30d05725c45450c30c14865c45450c30d07825c45450c30d04825c45450c30d10805c45450c308d0815c06250c30b05811514394830b05811514354830c24641c552544309168790d5190430c45631c55210430c17645c4548c430c45651c5528c430c24641c5524c430c15645c4540c43081c87591510c430e0564949510c430a4681d956388430a0d861514388430b05811514388430c0d655d03188430c49655c03208430c0d655d06308430c49655c06308430c49655c243084309c0815c24308430a0d861514308430b05811514308430d04541c54308430c0d655d03108430b04845443108430d05745443108430c0d7559021cc030c457598421cc030c4575184214c030a8882590404c030a9081590404c030c6175184214c030a1581d954310f20e085414c604c920d23541c13214520d20541c13214520d43531c13214520d40531c13214520960805c84314520962809da3214520960805d23214520960805d13214520a608058851cc520a6280d8c5188520e085414e6088520e43531466088520e40531466088520d08541c9300c120d4072145300c120914815d54310c20c88741cd6008420a2984d4d6008420a2584d4c6148020ac0835c06148020ca2741873048020e41531843048020c91431c16110f10a9181191430c31081e879954310e10b048150c4394a10a198494c604c61081f87593530c610b058494d3108610d047494d3108610b0684d4c3108610d0574d4c3108610b0684d4e5308610d0574d4e5308610b4280d4e5308610b078550c4308610d067550c4308610cc1735806008610c15645c46414d10a148550d6110d10c147550d6110d10d05435c443149109a0845c23108410d057454c3108410a498319560084109a0845c23208410c61651c132084109a0845c36308410c61651c16308410d057454c5308410865861d54308410d057550c43084109a2849ce6008410d83741cd6008410d80741cd6008410aa2849d821cc010c45531c5620c010a1985191430c010c90641c5430c010c61651c5620c010c19655d0310c010cc1760c4210c010e41650c4210c010b81840c4210c0108e187190210c010a6185190210c010ac186dcc210c010ac1861cc210c010cc1761cc210c010b41851cc210c010b81841cc210c010cc17698c210c010b818498c210c010ac18690c210c010e806450c210c010a6280d486148010a45831486148010aa28498c2184010
  | 1 => 0x2010502004040007c0402000180000c47731c56214143c44731c56214143a84815886250c43a88805886250c43984815c86050c43a88825806050c43a90815806050c43a848150c6254443a908150c6054443a1a80dd94354443b0682dc54354443a0c8650f6254443a0c8650c6254443a188650f6054443a188650c6054443e0943d886054443e09431886054443a508150c6054443e138150c6054443a188150c6054443e108150c6054443a60815c86055132d06725c45450f31d05435c44394b31c29745806094b31c1b541c16110e31c47731c56294231b11811914314131924815c86055031a28825806055031a30815806055031c19541c16110c3181f87d974350431a1985d0c6050431a1a80dd9544c43181e869d9544c431a0c86553624c431a0c86550624c431a1886553604c431a1a86550604c431a1886550604c431e0954d88604c431e0954188604c431d05549ca534c431a178550d6110f21c91431c16110f2189487591310c721c91641c1310c721a848150d6110e21c89431c16110e2188c87591310c621c89641c1310c621d0a749cf5094221d42739c75094221d41739c75094221c15651c54310c21c91431c16110c2189487591310c421c91641c1310c421a49801955350c21a848454c6150c21c85861c54310c21c87651c54310c21c85651c54310c219848750e6110c21c0f7550d6110c21c89431c16110c219848750d6110c21d81431c16110c21c878750d6110c21a848750d6110c21c848750d6110c21c877550d6110c21e077550d6110c21e8143dc16110c21c85431c16110c21e81431c16110c21cc2431c16110c21cc1431c16110c21c81431c16110c21a848150e6010c21c857458c6394421c857650c4394421a0d8519143cc421c84641c543cc421c87645c4438c4219c0805c4438c421aa0805c4644c421a868690e414c421c84641cd414c421c847650d414c421ac08150c604c421e8243904604c421ac083504604c421e8143504604c421c84731c5640c421c85645c4430c4219c0805c4430c421c85645ce510c421a8586d0f410c421c8576d0f410c421c85645cc410c421c857610c410c421c0d75593310c42188c87591310c421c0f75591310c421c89641c1310c421ca1641c1310c421986849d1310c4219c2809d1310c421c85861d1310c421c8474d91310c42198487991310c421a8586991310c4218c487591310c42198487591310c421c8787591310c421a8687591310c421a8487591310c421c8487591310c42188487591310c421c8775591310c421e0775591310c421d8074dc1310c421e8164dc1310c421c85641c1310c421cc3761c1310c421d83741c1310c421d80741c1310c421e81641c1310c421cc3641c1310c421d82641c1310c421cc1641c1310c421d81641c1310c421c81641c
  | 2 => 0x37c6e000002ba85b3505000000001b0000f000001bc001940027218050000000000000000000007e00000000000010b41c0000000000838000000092174461fc000000000000000ed8003a80000280ba3100000102070954282e062782ac0000048000000a42d00000000000006915c2a000560e8003510616800084d12384180000338000004d1d4380001601c3043600004001dd0017c003b8cc000272d003000e034c61000a736c97000a540c0000021ab4630b000000e52de9d00073000b8bccf6000018008b000000d8430f8bf000000440000000038000ad0c2ae861600d19889284f225000000e8000002d8003000505c000000026455000d8390000000027c523e8e732cd01046a114d9c34c92047d190d512c4430c1f320c093c060c4af8caac404004109e0cc002683d36204800f5000003483502c000000000000000511c0de304203709008c000000017800000a40000000000000003a800000341f6fc054002c0fe3e48c0dc1e04c003ec67000eb088000ec3c000002cc24438b69c4881a0000008d26ced000ef0000017000000930007b0004c3c083208723a4c7314d7228ec000f414c870000030600000001d800010e1206b91c2500000abf467800003fc00000000002600091000002c8000001210a0c000a828c0028a00200d900000000000bc4e028593be0000000000b8000aa2986b23cb0bc4a900000100002d50e80028000002ec00358002f447040493e0d3b285b31896289091e4ae150aa864ad928cf0e400180320681d368af188bc260f730800214000a2740fce60246d420080009c000002dc7a000000000000084202dd000e3388b11fa420946c00800000002767c000be00c0e0700800000100004180000008040a000081c0100000060b0080000070600406010080006030c81c1400030000200000100e01000100001080081e00020000000040080c00008100010038141401008080600000080a020000000010301c040700040
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x5003260280131c0123a000000000000253c000026c5823c70a0e262420c2c8089a2a00418a118f801a400032e000000000000000826801024000906580a4b8150c6054443a09caa86382c221e434809150c705844388690521c3a86b088610d2025d43dc16110c21a404ba86382c221843405951907150f31087106c8402e221c6210e20590805c4430c421a414870eb22621884308697a1d644c4310869012eb26e09886210d20a5d641c1310c421a404bac83826218843808871d163540500868812eb18e2a80a010f001d1631c55014021c0243104b88a8a18618108620171151430c320104402e22a28618610594815c24308430a02cb0a838a8610861104985d1510c4210c220f30ba6a618843086405d280d4e53086108834c4eaa188610c21881766103108430043402cac206210860086105d9851cc210c010c40bb30839842180218817661263084300429032e3228610860085806546450c210c010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 29
  | 6 => 1134
  | 5 => 6283
  | 4 => 3769
  | 3 => 271
  | 2 => 33
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
  | 7 => packedAt gbK7 (548+((h/14+packedAt gbK7 (464+(h % 14)*6) 6) % 56)*6) 6
  | 6 => packedAt gbK6 (36846+((h/519+packedAt gbK6 (30618+(h % 519)*12) 12) % 2489)*12) 12
  | 5 => packedAt gbK5 (274846+((h/2578+packedAt gbK5 (238754+(h % 2578)*14) 14) % 10211)*14) 14
  | 4 => packedAt gbK4 (204827+((h/1439+packedAt gbK4 (184681+(h % 1439)*14) 14) % 10092)*13) 13
  | 3 => packedAt gbK3 (17187+((h/103+packedAt gbK3 (16260+(h % 103)*9) 9) % 496)*10) 10
  | 2 => packedAt gbK2 (2415+((h/12+packedAt gbK2 (2343+(h % 12)*6) 6) % 58)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff01fff80ffffc0ffffff81ffc0ffcff1e3f
  | 1 => 0xc07ffffffffffffff03f01ffffffffff11ffff
  | 2 => 0x7ffe03fff01fffffc001ffe0fff07fe1e3c7
  | 3 => 0xff800003ffffe03ffffffe0000ffff83fe03f8
  | 4 => 0xfffffffc0000003fffffffffff000003fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x43094c2888e2448c02cb2a59092c84e4670e1b
  | 1 => 0x9522145111248910b01540aa325519091074ed
  | 2 => 0x2a4c289aa241d22d5540a935489aa472e1a346
  | 3 => 0xc68b163448903b669a6cc0610e3ce23ba03b0
  | 4 => 0x3070c183870e1c3b8e38f1c79c030843ddd800
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeac8c880eac8c880eac8c880eac8c880eac8c880eac8c880eac8c880eac8c880eac8c880eac8c880eac8c880eac8c880eac8c880eac8c880eac8c880eac8c880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_37441
namespace PEqualNP.Outside.L_meta_37441
open PEqualNP.Outside.L_meta_37441.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_32 : Interval gbAtlas 2 32 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 33 := (concat bgb_2_0 bgb_2_32)
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
theorem bgb_3_256 : Interval gbAtlas 3 256 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 271 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 bgb_3_96)) (concat (concat bgb_3_128 bgb_3_160) (concat bgb_3_192 (concat bgb_3_224 bgb_3_256))))
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
theorem bgb_4_3744 : Interval gbAtlas 4 3744 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3769 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416)))) (concat (concat (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)) (concat (concat bgb_4_544 bgb_4_576) (concat bgb_4_608 bgb_4_640))) (concat (concat (concat bgb_4_672 bgb_4_704) (concat bgb_4_736 bgb_4_768)) (concat (concat bgb_4_800 bgb_4_832) (concat bgb_4_864 bgb_4_896))))) (concat (concat (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat (concat bgb_4_1024 bgb_4_1056) (concat bgb_4_1088 bgb_4_1120))) (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 bgb_4_1376)))) (concat (concat (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472)) (concat (concat bgb_4_1504 bgb_4_1536) (concat bgb_4_1568 bgb_4_1600))) (concat (concat (concat bgb_4_1632 bgb_4_1664) (concat bgb_4_1696 bgb_4_1728)) (concat (concat bgb_4_1760 bgb_4_1792) (concat bgb_4_1824 bgb_4_1856)))))) (concat (concat (concat (concat (concat bgb_4_1888 (concat bgb_4_1920 bgb_4_1952)) (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 bgb_4_2080))) (concat (concat bgb_4_2112 (concat bgb_4_2144 bgb_4_2176)) (concat (concat bgb_4_2208 bgb_4_2240) (concat bgb_4_2272 bgb_4_2304)))) (concat (concat (concat bgb_4_2336 (concat bgb_4_2368 bgb_4_2400)) (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528))) (concat (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656)) (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784))))) (concat (concat (concat (concat bgb_4_2816 (concat bgb_4_2848 bgb_4_2880)) (concat (concat bgb_4_2912 bgb_4_2944) (concat bgb_4_2976 bgb_4_3008))) (concat (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136)) (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)))) (concat (concat (concat bgb_4_3296 (concat bgb_4_3328 bgb_4_3360)) (concat (concat bgb_4_3392 bgb_4_3424) (concat bgb_4_3456 bgb_4_3488))) (concat (concat (concat bgb_4_3520 bgb_4_3552) (concat bgb_4_3584 bgb_4_3616)) (concat (concat bgb_4_3648 bgb_4_3680) (concat bgb_4_3712 bgb_4_3744)))))))
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
theorem bgb_5_6272 : Interval gbAtlas 5 6272 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6283 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))))) (concat (concat (concat (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304))))) (concat (concat (concat (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496))) (concat (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)))) (concat (concat (concat bgb_5_2720 (concat bgb_5_2752 bgb_5_2784)) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880))) (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104))))))) (concat (concat (concat (concat (concat (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200)) (concat bgb_5_3232 (concat bgb_5_3264 bgb_5_3296))) (concat (concat bgb_5_3328 (concat bgb_5_3360 bgb_5_3392)) (concat bgb_5_3424 (concat bgb_5_3456 bgb_5_3488)))) (concat (concat (concat bgb_5_3520 (concat bgb_5_3552 bgb_5_3584)) (concat bgb_5_3616 (concat bgb_5_3648 bgb_5_3680))) (concat (concat bgb_5_3712 (concat bgb_5_3744 bgb_5_3776)) (concat bgb_5_3808 (concat bgb_5_3840 bgb_5_3872))))) (concat (concat (concat (concat bgb_5_3904 (concat bgb_5_3936 bgb_5_3968)) (concat bgb_5_4000 (concat bgb_5_4032 bgb_5_4064))) (concat (concat bgb_5_4096 (concat bgb_5_4128 bgb_5_4160)) (concat bgb_5_4192 (concat bgb_5_4224 bgb_5_4256)))) (concat (concat (concat bgb_5_4288 (concat bgb_5_4320 bgb_5_4352)) (concat bgb_5_4384 (concat bgb_5_4416 bgb_5_4448))) (concat (concat bgb_5_4480 (concat bgb_5_4512 bgb_5_4544)) (concat (concat bgb_5_4576 bgb_5_4608) (concat bgb_5_4640 bgb_5_4672)))))) (concat (concat (concat (concat (concat bgb_5_4704 (concat bgb_5_4736 bgb_5_4768)) (concat bgb_5_4800 (concat bgb_5_4832 bgb_5_4864))) (concat (concat bgb_5_4896 (concat bgb_5_4928 bgb_5_4960)) (concat bgb_5_4992 (concat bgb_5_5024 bgb_5_5056)))) (concat (concat (concat bgb_5_5088 (concat bgb_5_5120 bgb_5_5152)) (concat bgb_5_5184 (concat bgb_5_5216 bgb_5_5248))) (concat (concat bgb_5_5280 (concat bgb_5_5312 bgb_5_5344)) (concat (concat bgb_5_5376 bgb_5_5408) (concat bgb_5_5440 bgb_5_5472))))) (concat (concat (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664))) (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856)))) (concat (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))) (concat (concat bgb_5_6080 (concat bgb_5_6112 bgb_5_6144)) (concat (concat bgb_5_6176 bgb_5_6208) (concat bgb_5_6240 bgb_5_6272))))))))
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
theorem bgb_6_1120 : Interval gbAtlas 6 1120 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1134 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 29 := bgb_7_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeaeaeaeaeac8c880eaeaeaeaeac8c880eaeaeaeaeac8c880eaeaeaeaeac8c880eaeaeaeaeac8c880eaeaeaeaeac8c880eaeaeaeaeac8c880eaeaeaeaeac8c880
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941264072 * 2 ^ 32 + 3939035776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37441.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[4,5]⟩,⟨.or,[3,7]⟩,⟨.or,[1,8]⟩,⟨.and,[1,2]⟩,⟨.or,[6,8]⟩,⟨.and,[10,11]⟩,⟨.or,[0,12]⟩,⟨.or,[2,11]⟩,⟨.and,[13,14]⟩,⟨.and,[9,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264072 * 2 ^ 32 + 3939035776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264072 * 2 ^ 32 + 3939035776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37441

open PEqualNP.Outside.L_meta_37441 in
theorem PEqualNP.Outside.L_meta_37441 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264072 * 2 ^ 32 + 3939035776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264072 * 2 ^ 32 + 3939035776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
