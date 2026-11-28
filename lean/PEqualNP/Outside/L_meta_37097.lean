import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37097.Model
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


end PEqualNP.Outside.L_meta_37097.Model

namespace PEqualNP.Outside.L_meta_37097
open PEqualNP.Outside.L_meta_37097.Model
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

def SBf (j : Nat) : Nat := [7, 7, 5, 6, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37097

namespace PEqualNP.Outside.L_meta_37097
open PEqualNP.Outside.L_meta_37097.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x160c080119334046a62c0c0213018800622151e1e00a1514480242ebc880040000000883b0009c02d3a145a836b9000129401f327000052015801c002c4800c2010116000062600000ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x12590f00000000000092001c801400000000ee20090204c722a1ac8403000fc4a6d3d288c89e1f14c8c8d0c12814003f290c0653f8012a5f24275269f001343a5003a58f8000b0005c340003cb47b0d115040015111146a261a51c9044031363346200568314938ec13030002e002005142571e8d4e000190b4c43c4e198f227000452e023a870b85d059c4326f11a1c8e31279d0a2910692c5e5b448151e28218003e3620810d0844d20470860d9781c551d94874241b96130993c0000000318002aa3458000010371f4002c491580021308050a304a00000730019c446c000e010380060207801203800002800006020001840c80078102848d80050d04028c830088850280000a82840208850181070081018484cf54b439f28e873e50d0e7aa921ddd4543ba28a879f5350e7ea4a1edd45439e28a87b45150e68a2a1cf141439f2a0875e53d0abaa7a16794f429ea9e859d53d0a3aa7a14f947429f286853d5490a7ea6a16bd49429e28a853c5050a7ca8214f953329eaa6653e548ca7aa9196750e32bb28c6575518ca7ca8994f551329f2a0653d540cb3a86195794f41aea9e833d539067aa520cf946419f284835f53506b8a6a0cf54c419ea90833e511076ca220cf940419f2a6633d54cc7688398cfd52319e2a4639f438c73a8718e7d5231ce2a4639f428c73a8518d794631cf20c639c418c67ea898cf151319f2a0633d540c73e8618e750c31da208639e540c73aa818e7d0831cea10635e510c7aca218f5d0431cf208639c410c7a88218e5104319f2a6433d54c86bca790d754f219faa4433c54887a86310cfd51219e2a2435f53486b8a690f50c521bda824378504867ca810cf550219ea9c813d529027ca320678c640ce18c813e50902bca6205754c40cf298813d531033aa6204754c409ea90813e511033c6220670c4409f28081ba501027ca9984f55330cea1e613f548c278a9184fd51309e2a2619d434c2dea4985b14930bba8a6174514c27ca8184f550309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ca9084f55210af29c215d53843a863084fd51109e2a2215f53442b8a6885bd4910b6292213f5404278a808750c410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x75c9500840294a00f2d000170000000200000000701c59700e80940028037008db2700bc0001200000004960c4c4d58662ed9181a0120000002000a88c801ca801a0640d803e440006a599a80021a00043d800380c140000e00080140040000001820004004c5d4c5150f1763145439518553d0a346154f42a518553d0b176154f428718553d0b146154f428518553d0a1d6314142a5185438cb1543946328758e544ca3461551328e181544ca946150c3287d8d529061d63942418b588548c69661d5231a3588548c696611523187997428c635651043187597420c6946150831a5986410c6976510431a5594410c6956210431a5980410c61d6315221c51503188714540c521d40c4504861d639502187d8d5290316510c6409518553102346154c40a518553103176154c408718553103146154c4085185531021f658c4408759431102946150f308d987548c21c6550d30a5185434c30d4314930c550c514c21d63953208758c548821d6395310c5950318421d63150108b5885404314540c410
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x60800810c00000050000449c300283396c628a87051c5631414290ae5b288218c147158e540860b38ec6a9481411c54314930828e2b1ca9904147158c548820abb0a818821415c8540c410
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
  | 4 => packedAt s0K4 (4895+((h/55+packedAt s0K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s0K3 (2420+((h/20+packedAt s0K3 (2280+(h % 20)*7) 7) % 96)*7) 7
  | 2 => packedAt s0K2 (505+((h/3+packedAt s0K2 (490+(h % 3)*5) 5) % 22)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xf01ffffe03ffe07fe0ffe07fffc1ff01ce7e7c
  | 3 => 0xffe07ffffc0fffffff03ff81fffe0ffff38f8f
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x1142108c48824810052ca8a25012915414b0b5
  | 2 => 0x24c52914392484a960556454b6412a0cca565c
  | 3 => 0x42894a209069144aaa0255112aa40ca9630b0a
  | 4 => 0xb1674492241d974d3981861cd39c031bc0de0
  | 5 => 0x8c187871c38e1e7f1ce39e780e3188c1ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37097
namespace PEqualNP.Outside.L_meta_37097
open PEqualNP.Outside.L_meta_37097.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x195a016000078ea640a0a803e389a9421c108445808a2e4159a0000c23180000f000128b1a002090c709244ea829b280c8953c004c1000c02c0146042ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21ee21fd21fc21ec21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x490624002e221400006a7200006e5b25424f273900450b4d00031d093b54351f6521122a07576c2d3123081b2c00000000361c603e002851406f4317640f480c520070200011623456005e1e5971192602154c470038675f7400186600584e6d4a2f6101040e3d3a4133304b63503f05556816696b133c00105d0d29375c4600322b001a0073440000535a0a00020001878303810984808d0085050500000002018000800483871d81008380060200860c01965b94b43b6a96877651d0eeaa3a1d794f42aea9e857651d0aeaa3a15dd4532ba28a65cd320cabca7a0d754f41b7296836d52d06bea6a0d714d41b7a92836c52506f6a0a0de14141b7296636d52cc6bca318dbd4931b6292633e540c67aa818e795031ceaa0635e510c7aca218f590431eaa08635e53c86baa790f50c721b728c43ce31887986310d7d4d21ae29a433e540867aa810f50c421d72a043ad54086dca210f994421f320843e541087ce6210f38c421e618843e431087886210e78c640ce18c81ae219035843204f94240af298815d53102dca4205b54840bb2888175511033ca6206754c40d729081ad521036ca2206d54440cf188819c311035c42206b084409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520af298415d530827ca9884f55310dc206215e53842baa7085b94a10b6a9421d431843c843084fd51109e2a2215f53442b8a6885bd4910b629221d431043c842086e10010
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2c08c11242a5801ae70a92622850000001800e00069e8a04a00004ca2b1185320cac46250431b4181410c715540c421b118d41086e06050421b198631086a5640c421e19903108785640c421e19503108785540c421e10c421903155354440c9549511021d650c4408b5942110384310844099185520c2546154c20d194831843465308610e40c440043a02110010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x60200020000a0aeb3206210c85769503108682ba86210881815943108440
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
  | 2 => packedAt s1K2 (200+((h/1+packedAt s1K2 (196+(h % 1)*4) 4) % 15)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 2 => 0x7f01fc07ffffffff83e07c0f80ffffffc933ff
  | 3 => 0x7ffe0007ffe07ffffc007ff000fff83ff1c3c7
  | 4 => 0x80000007ffff81ffffff800000ffffc1fe03f8
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x914284011c104200c628c508e2c425212561b
  | 2 => 0x224c518b224a28c581a8350d12558ca4c930ed
  | 3 => 0x4c289ad54487516ab4125b64249ad23971c346
  | 4 => 0x68b1636689141db35adb024848e36711be03b0
  | 5 => 0x70c183870e1861dc631c638e70038421eda800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37097
namespace PEqualNP.Outside.L_meta_37097
open PEqualNP.Outside.L_meta_37097.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1fffffe03ff81c1ffffe0fffff81ff007cfe7c
  | 1 => 0xe07e07ffffffffe0f81ff0780fffffff9333ff
  | 3 => 0xff8007ffc1ffffff001fff800ffe0fffe3c38f
  | 4 => 0x7fffe001fffffe000000ffff001fc03f0
  | 5 => 0xfffff80000001ffffffffffff0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc30c40238410a40318a60288e390990c24563c
  | 1 => 0x49108a4490a208a06a0a905124a322549130d5
  | 3 => 0x842554890d44954d04952b0249548ca962c30a
  | 4 => 0x1659e7122876de76b6c18a448e79c831fc03e0
  | 5 => 0x1861861c31871b98c719cc67006100c1dba800
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37097
namespace PEqualNP.Outside.L_meta_37097
open PEqualNP.Outside.L_meta_37097.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x8de43dd43
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
  | 4 => packedAt s3K4 (34+((h/1+packedAt s3K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x81ffffff80fffe07ffff81fffffc0ffcf8fe3f
  | 1 => 0xfe03f81fff03fff83e0ffe0f80fff07f4f33c7
  | 2 => 0xfffc001ffffc0fffc00ffff000ffff838fc3f8
  | 4 => 0x1ffffffffffff0000000fffffff003ff
  | 5 => 0xffffffe000000fffffffffffff000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8c2850808e082200c61188528e2c429418561b
  | 1 => 0x1498a2a9123946581a86aa4b125552594b32c5
  | 2 => 0x285134d22450eaab410b4d62249a6b128dc368
  | 4 => 0x7162c71c48a28d35ada0610848e38c63f001b6
  | 5 => 0x4183061870c30dc631cc718c70030843e6a800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae8e80000eaeaeaeae8e80000eaeaeaeae8e80000eaeaeaeae8e80000eaeaeaeae8e80000eaeaeaeae8e80000eaeaeaeae8e80000eaeaeaeae8e80000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37097
namespace PEqualNP.Outside.L_meta_37097
open PEqualNP.Outside.L_meta_37097.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x5e4402600fc0003ef859d42b89ab0019a0034a878012c519b5a000006a6002214340000000801005de39000190776a00000001c244a00c8328b003a0000e120a38f006e302332ca41156c218207a0002710020800608041800a041090a0c0810000081b7a92876c5250eeea2a1dd14543bda8287785050edca421db54843bda8285785050abca6215754c42bba8a6574514ca7ca8194f55032af29e835d53d06dca5a0db54b41b7294836d52906f4a120de54241b7a92636c524c67ca818cf55031b7290636d520c6f4a018de54031afa9a435c53486f4a010de54021b7a92816c52502bca6205754c40b7290816d52102eca2205d544409f2a6613d54cc2dca5985b54b30b7294616d528c2eca3185d546309faa2413c54482eca2105d544209faa2213c54442bea6885714d10b7a92216c52442dca4085b54810
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
  | 4 => packedAt s4K4 (1875+((h/21+packedAt s4K4 (1728+(h % 21)*7) 7) % 92)*7) 7
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffe03ff8307fc3fe0fffff83fe0138fe7c
  | 1 => 0xf01f83ffc1ffff83fc3ff0780ffc1ffecf338f
  | 2 => 0xffe003fffe003ffc003fff800fffe0030fc3f0
  | 3 => 0x3ffffffffffffc000000ffffffff003ff
  | 5 => 0xfffffc0000003ffffffffffff0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x614510238411500cc04642a8e590aa2818563c
  | 1 => 0x24c214448ca11281441a523122948c984b3285
  | 2 => 0xc28b5a891875b5b4222d6b224b5ac8530dc3d0
  | 3 => 0x8b1463122144295aaa8108048c631163b0016a
  | 5 => 0xc18421c31862e6333318c4700420183e6a800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaec00ec00eeeaeeeaec00ec00eeeaeeeaec00ec00eeeaeeeaec00ec00eeeaeeeaec00ec00eeeaeeeaec00ec00eeeaeeeaec00ec00eeeaeeeaec00ec00, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37097
namespace PEqualNP.Outside.L_meta_37097
open PEqualNP.Outside.L_meta_37097.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x243ec42487dc6490fb4c921fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d02fca3a05f54740beaa4817e53902faa7205f94a40bea9481be429037885205f94640bea8c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa9281ef52502dea4a05f14940f6292816c52502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52102faa4206f90840de210817e51102faa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c617e528c2faa5185f94630bea8c617e508c3f481187e50230ef98461fb308c2fea8985f95130beaa2617c544c3bc86987750d30bfa92617c524c2fea2985f14530fd20261f9404c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c2faa4185f94430bea88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720fda0641f840c83f461907e4c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef42883d885105f94620bea8c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107bd0820f6210417e51083eca2105d94420bea8841f551082eaa2105f94020fda0041f840083f460107e4c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c43f641887e08310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f681087e10210fd18421f930843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec42887d48510fda0221f840443f460887e4c110fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021fe94043bd280877d5010ff2a021de54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42f7a1285be4250afea2a15f14542bfa8285fb5050af6a0a15f14142fc28285785050afca8215f94c42bea9885bf4310b7a86215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332f7a1665ec42ccafca3995f54732bf28665fa50ccaf4a1995f54332fca86657950ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cafaa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d06fca1a0df54341beaa4837e53906faa720df94a41f7294836e52906faa520fb54a41b6a9483be42907788520df94641dfa0c83f741906fca120fe94241bd284837d50907f2a120de54241bfa9a837c535077e86a0ef50d41bfa92837c52507ee82a0ef90541bfa82837c50506fca820df94c41bea98837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831f7290636e520c6faa418fb54831b6a9063de320c7b86418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f7a1643ec42c87dc6590fb4cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f7a1
  | 2 => 0x12ca361b270c278ae0e24182417a05a2e419099000214cc800000000598390004600012011200059141000000f000036a01800000000548b583305c814df1700007983805a4542c41f82812e5f8409b231236c5f9f812a428fe0c81cc50087a5117a8342d9cb0487c02a0000009500008d25c7852093c30c2a8638ac3b6000021e93909906e9652a25f4f79e3260468000001d2840000564ac3ec95808020138a41572ec7accf16e31e6e44a09d0000009c80043482c8f9634c0000ee93a074534001ec0985d400000310494000c90008b40000038c000750000004b4000420006ec7c95d2d40011c20235a68ce9a002188883ba491c20708221302423cc58b80f8210c609e0820dc6799339a04c670720006692d9290800005b0001e602c45a483f4074001963fa000000000008444d20f04c05c0a09220e001038c44ca24d2b8cb000000000eb0de0384fa1b0000652914c000614001d8000604d480032275cde17f2bc954028a114c0243d9fe262674000804681a50a83d3a48285213d00000039a0e21c01c3a0d0044000138c3472649308000182944e2254cc4c8000d129650ce88003a0738ac2500580004606c3588f0a514236294c6b1f4000660828000000000020c000000d52302d2564001b33ac350fb03c1fa26d0f178000190f70000004a8000000d63b04b0000a43fc8aa5d292488001fb3e21d4a208e14e790e08f03bc2280518239e404fa83438e124650013da40c6c1ab29e8b8ce0302c46dcba1ca0000d4b200d0003308e0c123c00000000000580000da4b47cd0b8000002201184d29c0000000200034c000000000005b876062000df8000001405495b00091c0000047a000701ba4563c87a24e18a000d01a40000012598335e8cc100c00006b8411dc32a00c431351ec0008a1272240011900032810c12a1400054cc813e4525b1138df0963e92f9264bc4fc369613366d9230e3000864858584081f4000000002a11f21d19a8c50c154174610a39b847e820f90be0b257015004000000000002c09000000280601c000580a01802010020180700001050060e4000200100003054010180000008010000080c000060040900c0c0000102001018070100e00012010060001900000030050040501803038000000a000010340601000040030040000801018020000302c000240402002000000000501c070000800000020000080002419000010140500001020030180000002040000000402c02030020200305c030000001c010580000001004040180a040000180100012004000100100c0000c0a07800024000440200c0b000000000a00403004020240000805000000f4000040300012004040381b01000004000000000809054020601dbf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x420ea80044000097a454ce0540000000011886800000000000dc474110bd9c003c9084c11d0345191b8002a05bc000004241e0e295a03e0000011901e600000001de0000000034a35c5a0fe37a65c0001b15a4b0000f80005dc0c07e02c884d09110000011780040279c001a7000000438381783b504a620be98d1180022e555278660c4000e61001a444c0011600000000000388930000002040441b1563f2170582240ce1e4919284500000000034461d1603b2f8000108004861788d8900aa000001363d400017853000000b88d53c40009ba4d0c26340005d122180328633842ecd31680008190e24a0009700007f46a67cec98a28a7dc72851000000001331ee000001790d4114739ff000000500004763182b8680002d4ed13408e5ccef9a83608988812131c288848002701285587a276000610002cc000000001dc000001670005c8711241ea87c371b414657d222580000ac1f000000000419d4480724000000005b46f1e51d02bc000e4000858002033d00a4000f11f8000000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x540867a60d4c219e583530863e6414c218f590530866e6214c219e98053086796014c219bd9521086776548421dac8550087722154021da48550087712154021ae18143d026e62947409b58a51d032f4314940cb50c525036852d0140cb14a40503586054c40c754e421031d5310840c754f401035953900408fd95401031d5350040ab189401027b6550040d654d40102e862500409b98b54cc26d62d5330b618143cc39943d0330b658c40cc26e62d52309b58b548c27661d52309d587548c23f6454a308f191528c2e862502309bd89544c26c62551309dd85544c27461551309ed81544c25c6550d309b988514c26d62145309e996404c2786550130e650d404c2e862501308f596540c26f62550309b189540c32f6255030cb189540c33860550308f990540c25e63150309e980540c27965d0030ce553400c2796510030ce550400c2d96310030c7553300c339548c03097d95300c31d544c0309ed95300c339544c0308f99253c823d6494f20ba18121c82d963103209798c548825d63152208f990538823d6414e208f992544826f62551209ed81544823e65151208f992534823d6494d209e582534823f6454d208f19153482776154d209d185534832c54c8520cb151214833854c8120cb152204827661d50209d587540825e63150209758c540827661150209d584540827661d4c209d587530823e6414c208f59053082766114c209d584530826d6510820d9d0951083644254420dc181510837151d00209e59440082d96310020ea108400837151100209e59630082e9628c020dc5463008371514c020d9547200837151880209bd9520082ac6448020d9545200827b6548020ae191200837151480209b98b54c426d62d53108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b10bc18121c43e121c8310bc58420c426f62552109b189548425e63152109758c548423e6414e108f590538423e64d4a108f593528425e63d4a109758f52843395410210b658c40842b8644821097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d108f990534423d6414d108fd91524423c645491097d8d524425c63549109ed81524427465485109e99740442d963101109e1953044358534c110bc185304427a65881109e19520442b86448110f8485204426e62d50109b58b540427a60d50109798c540425d63150109b988540426d62150109b98b530426d62d4c108f990530423d6414c109b988530426d6214c109e980530426d65948108fd91520423c6454810cbd91520432c6454810da181520426e62148109d984520427a60148109e597200436952c80109e59420043695208010bc584200436552c40109e596100436952840109dd95100436552440109ed9510043695244010
  | 1 => 0x2400020180000000686c0800020040a01058040811048108400088000c0600004349b01040220200004080e0400000101205010100106408080b008063b0000004170500000040d02c60010287404019ed8152d0e786054b439b98a51d0e6d62947439e98251d0e796094743d9d4b5150f6452d4543d9d485150f645214543dad4b5050f6852d4143dcd475050f7051d4143dad485050f685214143dcd445050f7051141438fd954310e5f6550c43ced0d5010f5a4354043ce50d5010f5943540439e98251d0a7960947429e9825390a796094e42c794d4390ab46150e42ae1814390b6b4214142ce9085050aaf6250c42ad1854310ab86050c428fd954210ab860508429bd954210ae860508429e98354cca7960d5332cbd8954cca7a60153329e58054ccb2d5410b32ce95250ccb395494332dad0a50ccb684294332ce95150ccb3954543329d987548ca7561d52329e983548ca7960d52329bd89544ca7761551329d185544ca7b60551329e181544ca7a60145329e580514ca7b60550329e181540ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca6d651083297d95320ca6f654c832ad18543d072d5210a41da94a50907695294241ce90a50907384294241da949509076952542419e98053506796014d41c714d435067b60548419e181521063f65504419dd95411066f62553319b18954cc67b60553319e18154cc67a60153319e58054cc66e62d52319b58b548c67a60d52319e583548c63f6454a318f191528c67b6054a319e181528c66f62551319b189544c67761551319ed81544c67860551319b98b540c66d62d50319e983540c67960d50318f596540c73461550318f990540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c72e5454831cb551520c74d528c831cd553410c675651043197d95310c677654c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c76952540319ed8154c867860553218f99253c863d6494f219e98253c86796094f219e983548867960d52218f990538863d6414e219e98053886796014e21cb58b544863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219ed81544867860551218f994544871f54d4d21c7153534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219ed8153486786054d2197994534871f5414d21c7150534874d6214d219b997424874c53d0921b9987424872f5410921d314c424874c538c9219b19532486e4614c921ced53504873854d4121d6d4f504875853d4121ced5050487385414121d6d4c50487585314121dad08504876842141219b98b540867a60d50219e583540865e63150219758c540867a60150219e58
  | 2 => 0x48ad09a220b62ca4f0d28ead2230004f8ec181dea1a4e2f94a1985a001ae6f80e069043d3028c80c1000028194c121c248ba5b0a822800be800398000c82e1fa247e800998d60004a331aaacab02a8981612e3a80001aa29083eaf8007009e00000968009b0548ba7e979bc8d9ee611305d2906700000318000443e00000280049accc272ad000b82d64333609800958000028e728008d27a5b92a1d22c252e2a7964c8b240f1a82b326cb2cec48d4559cc270905c25098000000f6002aead9b600274cb8da4e1b8000003200070a020d872500200000000a82900006c9d43782868a88370005884c0017669000521a0a82d4530007c0007a800002447809a54a528398a85ac8001c41a97c5e80000292c00386630c6d00074850b18421e1e4a2a08b79e8439fe8310276000052f05602a3a2f21b146771289c26a87910c512c000000d15400000002640000000052000000000088af89713a342a4001088000060810b31a61c29c50a1a0033815800000f29d96a85000c18c4000005980056ae6000ca401d600086cd2dc472fe190ee0010a64000a69f4383082bb20860bc47b280022a458248198e2c080288008f000001fc120f0a12bc7423e3900abd1865fb2a0029600000453100022679ac06e8fa6225449ae83617230aa606160072e45415c4d30ec683aa30b4cc8761a31cbf1249b992810fe92918c79f8c2ab86581e84b160b11a9886eb0a942c94eaa0b6960304d944631ce57978448c0290162982291a9878ada17008222c44188e669689307c20a7c7c87a25800602ba7daecbb80001228bda1082800118b876aea718c6000849e0e28e2aa481c8178ce8c062ce9320004e0019e7b2486c0fcab0000d010380803000040c1009808080206800200f0d0583e021d0507c04028000006090001a000081c1a00078340203260000a030082800000d80416000180400010a808000202018040
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x800135072d25c404038f3486000064400d628015524c40b309800411465c25350e42a32e029a86a0ce1709874248670b80c2992438354c6250040c92a6312802068943189404c314310c0aa0614a1c95410030c32a8b188018689631084008328b1aa220041c81095110020950e8b146010661625463008312322a2900418c1915148020a50e4aa081086195458c408428cba0a698221385c8614c110d40c890a40886286418152042943a2a410021985496108010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x400008620a08825516310030e01631095110020a2084589518c020a08825516310210a20845496108010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s5K5 (18682+((h/205+packedAt s5K5 (16632+(h % 205)*10) 10) % 814)*11) 11
  | 4 => packedAt s5K4 (16974+((h/138+packedAt s5K4 (15732+(h % 138)*9) 9) % 497)*10) 10
  | 3 => packedAt s5K3 (1265+((h/8+packedAt s5K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (304+((h/1+packedAt s5K2 (300+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf03ffff01fff060fc3e1f87fff0ffc0448fe7c
  | 1 => 0xffc07fffe07ffff003ffff83fff07ff87f1f8f
  | 2 => 0xffff81ffff8007fffc01fffc1fff80078fe3f0
  | 3 => 0x1fffffffffffffe00001ffffffff003ff
  | 4 => 0xfffffe00000007ffffffffffe0000007fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x15851511c512ae02e0f05a56ab4ad454486e3c
  | 1 => 0x20930822432422500122aa90c55219301b1685
  | 2 => 0x430a2c448a0e32b544013318966310a18da3d0
  | 3 => 0xa2c518910488529aa540042188c62c6e0016a
  | 4 => 0x8c30610e1c70c5ce3399c4630008430776d800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfce8ec00fce8ec00fce8ec00fce8ec00fce8ec00fce8ec00fce8ec00fce8ec00fce8ec00fce8ec00fce8ec00fce8ec00fce8ec00fce8ec00fce8ec00fce8ec00, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37097
namespace PEqualNP.Outside.L_meta_37097
open PEqualNP.Outside.L_meta_37097.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001027fd5007fe54027f55007fc54027fd4c09fe53027f54c09fc5301ffd0c01fe43007f50c07fc43027fd4809fe52027f54809fc5201ffd0801fe42007f50807fc42007fcc801fe32007f4c801fc32027fd4405fe51027f54405fc5101ffd0405fe41007f50405fc41007fcc405fe31007f4c405fc31007fc8405fe21007f48405fc21027fd4003fe50027f54003fc5001ffd0003fe40007f50003fc40007fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x64001fb0832000ffe2190007fe10c8003fe086400affd9520055feca900037f65480013fb2a400aff99520025fcca9002bfd65480157eb2a400aff19520025f8ca9002b7c65480093e32a4000ffd9120005fec890003bf64480015fb224009ff9912001dfcc890003fd64480017eb224009ff1912001df8c890003bc64480075e322400affd512004ffca89002bfd5448013fe2a24000ffd8d20005fec690003fe634800f7f31a4000ff58d20005fac690003fc634800f7e31a400affd4d20057fca69002bfd5348015fe29a4009ffd0d20007fc8690003fd4348013fe21a4001bfd8920057fea49002bfe5248015f7292400aff54920057daa49002bfc5248013ffa124000ff90920007fa8490027fc4248001ff9924000ff8c920007fa6490003fc3248001ffb0a4000bfd8520047fcc29000afe6148001feb0a4008ff18520015f8c29002bff5148011ff28a400aff54520047f8a290027ff4148011ff20a4000ff50520047f88290003ff3148011ff18a4000ff4c520047f86290003ff2148001f790a4008ff88520007fa4290003ed2148011fe10a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe4090003fb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fa1048003fe0824005ffd951002dfeca880037f65440013fb2a2005ff99510025fcca88017fd654400b7eb2a2005ff19510025f8ca880177c65440093e32a2000ffd9110005fec88801bfe64440077f3222000ff59110005fac88801bfc64440077e3222005ffd5110037fca888017fd544400dfe2a22000ffd8d10005fec688003fe634400f7f31a2000ff58d10005fac688003fc634400f7e31a2005ffd4d1002ffca688017fd534400bfe29a2006ffd0d10007fc8688003fd434400dfe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e3122005ffd491002ffca488017fd524400bfe2922006ffd0910007fc8488003fd424400dfe2122000ffcc910007fc6488003fd3244001fe1922001bfd8510017fea28800bfe5144005fb28a2002ff5451002feaa28800bfc5144005ffa0a2002ff90510017fa828800bfc4144005ff98a2002ff8c510017fa628800bfc3144005ff90a2002ff88510017ec428800bfd2144001fa90a2002ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003ff2022001ff5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fd51cc025fe28e6013ffd0730097fc8398003fd41cc025fe20e6007ffcc73003ffc639801ffd31cc00ffe18e6000ffc8730097fc4398003fd21cc025fe10e6001bf5833000ffea198007fe50cc003fea866001ff1433000ffe8198007fe40cc003fea066001ff1033000ffc6198007de30cc003fd1866001ff0c33000fb86198007fe20cc003fe1066001ffc433000ffc2198007fc10cc023ffb2a6011bfd953008ffcca98012fe654c023feb2a6011bf5953008ff8ca98012fc654c001ffb226000bfd9130087fcc89800efe644c001feb226000bf59130087f8c89800efc644c023ffaa26010ff9513008ffaa898043fc544c0037fb1a6011ffd4d3003ffca698047de534c023fea9a6011f754d3003ff8a698043ff434c00fff21a6000f790d30007fa8698003dd434c00ffe21a6000ffd8930005fec498003fe624c001feb126000ff18930005f8c498047ff524c023ff2926011ff5493008ff8a498043ff424c001ff2126000ff50930087f8849801fff324c001ff1926000ff4c93003ff86498003ff614c0017fb0a600fff98530015fcc298003fd614c01ffe30a6002bf1853008ffea29803ffe514c023fea8a600fff14530087fe829803ffe414c001fea0a600fff1053003ffe629803ffe314c001fe98a6007ff0c530007fe429803ffe214c001fe90a600fff0853000dfec098007ff504c003ff2826001ff5413000ff8a098007ff404c003ff2026001ff5013000ff88098007ff304c00ffd9826001ff8c13000fbc6098007fc304c003ee1826001fe0c13000ffc4098007fc204c003ff8826001ff8413000ff42098007fc104c017ffb2e400ebfd9720077fccb90012fe65c801dfeb2e400ebf5972005ff8cb90012fc65c8017ffb264000bfd932006ffcc99000efe64c8001feb264000bf5932005ff8c99000efc64c801dffaa6400dff95320077faa990037fc54c8017ffb1e4000bfd8f20007fcc79001efe63c8001feb1e4000bf58f2005ff8c79001efc63c801dffa9e400eff94f20077faa79003bfc53c801bffa1e4000ff90f20007fa8790037fc43c80037f316400effd4b2005ffca59003bee52c801dfea96400efb54b2005ff8a590037ff42c8017ff2164000ff50b2005ff88590003ff32c8017ff1964000ff4cb2005ff8659002fff61c8019ff30e4002bf98720007fac390002fd61c8017fe30e4002bf18720077fea390033fe51c801dfea8e400cff1472006ffe8390033fe41c8001fea0e400cff10720007fe6390033fe31c8001fe98e400cff0c72005ffe4390003ef21c8019ff10e4000ff48720007da439002ffc21c80037eb064001ffd432000ffca190007fd50c8003fe2864001ffd032000ffc8190007fd40c8003fe2064001ffcc32000ffc6190007fd30c8003fe1864001ff8832000fdc4190007fa20c8003fe1
  | 2 => 0x21005b8c690867ff5348433ff29a4219ff54d210cff8a690863ff4348401ff21a4200ff50d210c7f8869080aff6248433ffa924219ff949210cffaa490867fc5248431ffa124200ff90921007fa8490863fc4248401ff9924200ff8c921007dc6490803fd3248401f69924200ff0c921015fec29080bff5148405ff28a4202ff54521017f8a29080bff4148405ff20a4202ff50521017f8829080bff3148405ff18a4202ff4c521017f8629080bff2148401fb90a4202ff88521017dc429080bfc2148405f610a4202fd08521007fec090802ff604842fff3024201bf98121007fac09085ffc60484037e3024219ffd41210bffca090867fd504842ffe2824218ffd01210bffc809085ffc404842fff1824217ff0c1210bffc409085ffc2048405ff8824202fdc4121017fc209080bfc104842dffb2a8016bfd95400b7fccaa0012fe655002dfeb2a8016bf595400b7f8caa0012fc65500037fb228003ffd514001ffca8a000fbe5450007feaa28016ef5514001ff8a8a0003ff63500017fb1a8000ff98d40007fac6a0003fc635000f7e31a8016ffd4d400b7fca6a005bfd535002dfe29a8003ffd0d4001f7e86a000ffe4350007fea1a8000ef50d4001ff886a0003ff62500017fb128000ff98940007fac4a0003fc62500017e3128016ffd49400b7fca4a005bfd525002dfe2928003ffd094001ffc84a000ffd4250007fe2128000ffcc940007fc64a0003fd3250001fe1928000ffd8540005fec2a0057fe61500057f30a8000ff585400aff8c2a000afc615002dffa8a8015ff945400b7faa2a0057fc5150007ffa0a8003ff9054001ffa82a000ffc4150001ff98a8015ff8c540007fa62a0057fc3150001ff90a8015ff88540007fa42a0057fc21500037fb028001ffd414000ffca0a0007fd5050003fe2828001ffd014001ff680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff1828001ff0c14000ffc40a0007fc2050003ff8828001ff8414000ff820a001fff65cc00f7fb2e6007ff99730025fccb9801f7e65cc0093f32e6007ff597300a5facb9801f7d65cc0013eb2e6007ff1973003df8cb9801fff64cc00f7fb266007ff9933001dfcc99801ffd64cc0017eb266007ff1933003df8c998053ff54cc027ff2a66014ff5533009ff8a998006fe63cc00fffa9e6007ff94f3003fbca79801ffd53cc029eea9e6007ff14f3003ffe879801ffe43cc00fef21e6007ff50f30007ba879801ffc43cc00fffb166007ff98b30005fcc59801ffd62cc0017eb166007ff18b300a7fea598053fe52cc029fea966014ff14b3009ffe8598003fe42cc001fea166013ff10b3003ffe659801ffe32cc00ffe9966007ff0cb3003ffec39801ffe61cc0057f30e6007ff58730005fac39801ffc61cc0057e30e6014ffd4730097fca39805
  | 3 => 0xe2866221ffd0331107fc8198883fc40cc40fff1866207ff0c331107fc4198883fc20cc405ff8866202ff84331017f8219887fff654c43f7fb2a621fff99531025fcca9887ffd654c43f7eb2a621fff19531025f8ca98803ff644c4017fb22621eff9913101dfcc898803fd644c4017eb22621eff1913101df8c89887fff544c43dff2a2621fff551310f7f8a89880aff634c43fffa9a6207ff94d310fffaa69881ffc534c43dffa1a6207ff90d31007fa869881ffc434c401ffb126200bfd8931007fcc498803fd624c401fe3126200bf189310fffea49887ffe524c43ffea92621fff149310f7fe8498803fe424c401fea12621eff1093103ffe6498803fe324c401fe9926207ff0c931015fec29880bff514c405ff28a6202ff54531017f8a29880bff414c405ff20a6202ff50531017f8829880bff314c40ffb98a6202ff8c531017bc629880bfc314c405ee18a6202fd0c531017fc429880bfc214c401ffb026200bfd81310effcc098806fe604c401feb02621dff1813100df8c09887fff504c43bff282621fff541310eff8a09887bff404c43bff202621dff101310effc609881ffc304c43bff102621dff08131017fe209880bfe104c405fe082620bffd97210e5fecb90873fe65c84097f32e421cff597210e5facb9082ffc65c84097e32e420bffd9321005fec99086ffe64c84077f3264200ff59321005fac99082ffc64c84077e326421cffd53210dffca990873fd54c8437fe2a6420bffd8f21005fec790803fe63c840f7f31e4200ff58f21005fac79082ffc63c840f7e31e421cffd4f210e7fca790873fd53c8439fe29e421bffd0f21007fc8790803fd43c8437fe21e4202bf98b210e7fea59082ffe52c8439fea96420bff14b210dffe859082ffe42c8401fea16420bff10b21007fe659082ffe32c8401f71964200ff4cb21007da659082ffc32c84057eb0e4202ffd4721017fca39080bfd51c8405fe28e4202ffd0721017fc839080bfd41c8405fe20e4202ffcc721017fc639080bfd31c8405fe18e4202ff88721017dc439080bf621c8405fe10e4202fb0872105ffec19086bfe60c84037f3064200ff58321005fac19082ffc60c84037e306421cffd43210d7fca190873fd50c8435fe286421bffd03210d7fc819086bfc40c8435ff186421aff0c3210d7fc419082ffc20c8405ff8864202ff84321017f82190867ff65484337fb2a4219ff99521025fcca90867fd65484337eb2a4219ff19521025f8ca90803ff64484017fb224200efd91210057ec890863fe64484077f3224200ff59121005fac890863fc64484077e3224200ef1912101d78c890867ff5448431ff2a24219ff551210c7f8a890803ff63484017fb1a4200f7d8d21005bec690803fe634840f7f31a4200ff58d21005fac690803fc634840f7e31a4200f718d
  | 4 => 0x1ffc530c80fffa186407ff90c3203ffa861901ffc430c8537f3106428ffd483205ffca4190a3fd520c817fe2906427ffd083205ffc8419003fd420c817fe2106407ffcc83203fbe641902ffe320c80ff71906407ff4c832007ba641901fed320c817ffb086407ff98432015fcc21901ffd610c8017eb08640bff18432015f8c2190a3ff510c84dff2886428ff54432137f8a21909fff410c84dff2086426ff1043203ffc621909bde310c80ffe1886407f70c432137fc421902ffc210c817ffb006407ff9803200dfcc01901ffd600c8017eb00640bff1803200df8c0190a3ff500c84bff2806428ff5403212ff8a01909fff400c84bff2006425ff1003203ffc601901ffc300c84bff100640bff08032137fe2019097fe100c84bfe0806424ffd9541125fecaa0893fe65504097f32a8224ff59541125facaa0893fc65504097e32a8202bfd914101ffea8a080ffe5450407df2a28203ff551411277aa8a080ffc5450401ffb1a8200bfd8d41007fcc6a0803fd6350401fe31a8207bf18d41127fea6a0893fe5350449fea9a8224ff14d4101ffe86a080fbf4350407ff21a8203ff50d410077a86a080ffc4350401ffb128200bfd8941007fcc4a0803fd6250401fe3128200bf18941127fea4a0893fe5250449fea928224ff1494101ffe84a080ffe4250407fea128203ff10941007fe64a0803fe3250401fe9928200ff0c941015fec2a080bff5150405ff28a8202ff54541017f8a2a080bff4150407fba0a8202ff905410177c82a080bfc4150405de20a8202fd10541017fc62a080bfc3150405ff10a8202ff08541007fec0a0802ff6050447ff3028201bf98141007fac0a088ffc60504037e3028224ffd414111ffca0a0893fd5050447fe2828203ffd014101ffc80a080ffc4050447ff1828223ff0c14111ffc40a088ffc2050405ff8828202ff84141017f820a081fff65cc40f7fb2e6207ff99731025fccb9881ffd65cc4457eb2e6207ff1973103df8cb9881fff64cc40f7fb266207ff9933101dfcc99881ffd64cc4017eb266207ff1933103df8c99888bff54cc443ff2a66222ff5533110ff8a99880afe63cc40fffa9e6207ff94f3103ffaa79881ffc53cc40fffa1e6207ff90f3103ffa879881ffc43cc40fffb166207ff98b31005fcc59881ffd62cc4017eb166207ff18b31117fea59888bfe52cc445fea966222ff14b3110ffe8598803fe42cc401fea166221ff10b3103ffe659881ffe32cc40ffe9966207ff0cb31015fac39880bff51cc405ff28e6202ff54731017f8a39880bff41cc405ff20e6202ff50731017f8839880bfe31cc405ef18e6202fd8c731017f8639880bdc31cc405ff10e6202ff0873103ffec19881ffe60cc4037f3066207ff58331005fac19881ffc60cc4037e3066222ffd4331107fca19888bfd50cc441f
  | 5 => 0x87321a7fea3990cbfe51cc869fea8e6432ff1473219ffe83990cbfe41cc865fe20e6407ff8c73203ff863990cbfe21cc865fe10e6407ffd833203ffcc199006fe60cc80ffeb066400bf5833203ff8c199006fc60cc869ffa866431ff943321a7faa1990c7fc50cc867ffa066431ff9033218ff8819901ffe30cc80ffe1866431ff8833218ff841990cbff10cc863ff0866431ff0433205ffecb190a6ff658c853ff32c6404bf9963214ffacb190a6fd658c817fe32c6404bf1963205ffec919002ff648c861ff3246403bf99232007fac919002fd648c817fe3246403bf1923214ffea9190c3fe548c853feaa46430ff1523216dfac7190a7ff538c80fff29c6429ff54e3203ff8a7190c3ff438c80fff21c6400ff50e3203ff8871901efe628c853ffa94640bff94a3214ffaa51902ffc528c861ffa14640bff90a32007fa851902ffc428c80fff9946400f7cca3203fde651902fff618c85fff30c6402bf98632007fac319002fd618c817fe30c6402bf1863214ffea3190bffe518c853fea8c642fff14632187fe83190bffe418c85ffe20c642fff8c63217fbc631901ffc318c85fee18c642fff8863205ff8431902fff608c85dff3046401bf98232007fac119002fd608c817fe3046401bf1823214ffea1190bbfe508c853fea84642eff14232187fe81190bbfe408c85dfe204642eff8c23203ff861190bbfe208c817fe104642fffc4232177fc21190bbfc108c85bffb2a642dbfd953216ffcca99012fe654c85bfeb2a642dbf5953216ff8ca99012fc654c801ffb226400bfd9132167fcc89900efe644c801feb226400bf59132167f8c89900efc644c85bffaa2642cff9513216ffaa8990b3fc544c85bffa9a6407ff94d3216ffaa69901ffc534c859ffa1a6407ff90d32007fa869901ffc434c85bffa92642dff9493216ffaa4990b7fc524c859ffa126400ff90932007fa84990b3fc424c80fff9926407fbcc932007fc6499003de324c801ffb0a6400bfd853215ffcc29900afe614c801feb0a642bff18532015f8c2990b7ff514c857ff28a642dff5453215ff8a2990b3ff414c857ff20a642bff1053215ffc629901ffc314c857ff10a642bff08532007fec099002ff604c855ff3026401bf98132007fac0990abfc604c8037e302642dffd4132157fca0990b7fd504c855fe282642cffd0132157fc80990abfc404c855ff1826407ff0c132157fc40990abfc204c857ff882642aff84132157f8209902fff650c80f7fb286407ff99432025fcca1901f7e650c8093f3286407ff59432145faca1901f7d650c8013eb28640bff1943203df8ca1902fff640c80f7fb206407ff9903201dfcc81901ffd640c8017eb20640bff1903203df8c8190a3ff540c84fff2a06428ff5503213ff8a81901efe630c80fffa986407ff94c3203ffaa619
  | 6 => 0xbfea82863bff1414301ffe80a180fbf4050c07ff2028603ff101431dffc60a181ffc3050c77ff102863bff081431e7fe20a18effe1050c77fe082860bffd96421d5fecb210ebfe65908097f32c843aff596421d5facb2102ffc65908097e32c8403bf5924201ffea92100ffe5490807df2a48403ff552421d77aa92100ffc5490817ffb1c8400ff98e4203dfcc721003fd63908017eb1c840bff18e421d7fea7210ebfe5390875fea9c843aff14e4201ffe872100fbf4390807ff21c8403ff50e420077a872100ffc43908077f314843affd4a4205ffca5210ebfd5290817fe2948403ffd0a4201f7e852100fef4290817fe2148403fb10a4205ffec3210e7fe61908057f30c8400ff58642005fac32102ffc61908057e30c843affd46421cffca3210ebfd5190873fe28c8403ffd064201ffc83210e7be4190807fe20c8403ef106421cffc63210e7fc3190873ff10c840bff0864205ffec1210e3fe60908037f3048400ff58242005fac12102ffc60908037e304843affd42421c7fca1210ebfd5090871fe2848403ffd024201ffc81210e3be4090807fe2048403ef102421c7fc61210e3fc3090871ff104840bff082421cffe21210e3fe1090871fe0848437ffd95421bdfecaa10dffe65508097f32a8437ff595421bdfacaa10dffc65508097e32a8403bfd914201ffea8a100ffe5450807feaa28403ff15142007fec6a1002ff6350801ff31a8400ff58d42007f8c6a101efc635086fffa9a8437ff94d421bffaa6a10dffc5350807ffa1a8403ff90d4201ffa86a100ffc43508077fb128437ffd49421bffca4a10dffd525086ffe2928403ffd094201fde84a100ffe4250801df2128403ff1094201f7884a100fec4250801ffb0a8400bfd85421b7fcc2a100afe6150801feb0a8436ff18542015f8c2a10dfff515086dff28a8437ff545421b7f8a2a100fff4150807ff20a8403ff105421b7fc62a10dbfc315086dff10a8436ff08542007fec0a1002ff605086bff3028401bf98142007fac0a10d7fc60508037e3028437ffd41421affca0a10dffd505086bfe2828403ffd014201ffc80a100ffc405086bff1828435ff0c1421affc40a10d7fc205086dff8828435ff841421aff820a101fff65cc80f7fb2e6407ff99732025fccb9901ffd65cc8697eb2e6407ff1973203df8cb9901fff64cc80f7fb266407ff9933201dfcc99901fbe64cc8075f3266407ff59332005fac99901fbd64cc8015eb266407ff1933203df8c9990d3ff54cc867ff2a66434ff5533219ff8a99901fff53cc80fff29e6407ff54f3203ff8a79901fff43cc80fff21e6407ff50f3203ff887990d3ff52cc869ff2966434ff54b321a7f8a5990cfff42cc801ff2166400ff50b3219ff8859901fff61cc80fff30e6402bf9873203ffac399002fd61cc80ffe30e6402bf1
  | 7 => 0x300000000200500000600100001000300200200e00100100a01600200000001701200000000000200300000001500000100000300000300300300000000000000700200000100700000100300100200600900000000600000500401300000601a00000000000400000300400200900503200201500700000300500800000000300800b00400000000100400000000500200000600000000100a00300100400500300700700100400800400c00000701300100100c00d00000300100100100501500000000100700500900200200300000f00602e00200800000000500400000400402701500900200100601700000500100200000000600000001000000800300000200002100500200000600100000800700700400000200700000900100100600600100200000100000100400301000000400700000600400100b00201000300400000300600000300000300000000500900300000700000a00100600400200100600500000000000100803ffecb2181eff6590c0fff32c8604bf9964303ffacb21902fd6590c0ffe32c8607bf1964301dfac92180fff5490c07ff2a48603ef9524301ffaa921903bd5490c07fe2a48607bf98e4303ffea72181ffe5390c0ffea9c8607ff14e4303ffe872181fbf4390c07efa1c8607ff10e4303fb8872181fff6290c0fff3148600bf98a4303ffac521802fd6290c0ffe3148640ffd4a43207fca521903fd5290c81fe2948603ffd0a4301ff8852181fff6190c0fff30c8602bf9864303ffac321802fd6190c0ffe30c8602bf18643207fea3218fffe5190c81fea8c863fff1464301ffe832180ffe4190c07fe20c8607ff8c64303ff863218fffe2190c7ffe10c8607ffd824303ffcc121806fe6090c0ffeb048600bf5824303ff8c121806fc6090c81ffa84863eff94243207faa1218fbfc5090c07ffa048603ff9024301ff8812181ffe3090c0ffe184863eff882431f7f841218ffff1090c7dff084863eff042431effecaa18f6ff6550c7bff32a8604bf995431effacaa18f6fd6550c7bfe32a8604bf1954303dfec8a180fff5450c07ff2a28603ff5514301ff8a8a180eff6350c7bffa9a8607ff94d431effaa6a181ffc5350c07ffa1a8603f7d0d4303ffc86a181fbe4350c0ffe21a8607ef10d4301fb886a1803ff6250c017fb128600ff98943007fac4a1803fc6250c017e312863dffd49431effca4a18f7fd5250c7bfe2928603ffd094301ff884a180fbc4250c01ffb0a8600bfd85431e7fcc2a180afe6150c01feb0a863cff18543015f8c2a18f7ff5150c79ff28a863dff545431e7f8a2a180fff4150c07dfa0a8603ff9054301ff882a18f3fe3150c0ffe18a863cff885431e7f842a1803ff6050c017fb02863bff9814300dfcc0a1803fd6050c77fe3028601bf181431effea0a18effe5050c7
  | 8 => 0x94027842ea7a0a4760aaa058d180008f254c0005e200031600016e930c1883aa3400045633c9dcd0c52e00038038c00088a00048c99a61aad43b8c4a00000029404200000084a00061c7420004e228e000000ca6612000aea0001d600061448800020439c634000802a1415c0008e07b813e16c1425da6821a800069cb380004b4000a2203082231ecdec04252650b962b23505a00002008340000007f6924a0492c9d074e88c000b32c744fc4fe0a259619e2da32c8268f0040bcea6a0005bcab814ca32046c1600000000000091e89c72e59813ac6cc10cba000000a2e8ec000762b686580f600000000068a000000b4e9cc0004c83360000000621ba09876c000000b44000cac0000009b200000000a0000007f00000000004ba0007ce7ca0000006521741fe00000000000089447ca0e938bb0bf400058cbc834ea7284c758756646670000ac23489bc5ca00000077a56e0ae14e6f21906fa9b800000000000071e45851c7d80009600000000000000005a836c0000008685ac000a401d800042a81e20a00c000bba0004b0c52b0e55c000000000000cbe0000009040004669e496c00011ecb00001c65c4394000188cee5f0000000b3e640000000bf83020002c64be00000019200000049253400048e25a64800000000050c00000012a00000011274a000712126000000a6c3dc2dc8400009946560000008ca00000025ed300000008826061de0000000000000002aec48000000000aa8000caa00000300000700400200000501200100100300500a00e00100f00900000900500300100000700a00000700100f00000000000401000400600400500000000200500000000100600300e00000100501c00300000100100100200a00000601800100400000000300200000600200000100100401600000300100300000700f00000100800200700500f00000000500700000601000400200000500000c00000000200200000800e00000000000000600000c01800100000201200600a00600200100001500100e00000000100000100500100800200300200000000f00000a00000100200800400000700b00200800000400601400100000200500000101501600c00200500000300100000000000400000e00102600900001100000300100100100100100000901000a00400200400b00a01500800000000000300600000000000000500600000300200300000000300000000f00300100000700800001000000b00000000000100000a00600101100000000900600200300000b01300200300000000100000000000000201c00b00300800100000400000100000901400000000300700000100200200a00100000900000200001700000600700600200100100600c00300700000b00200300100000700100100000100300000500000500000400
  | 9 => 0xc07a8000b08778a42cec97e1720007bcc821406d28880004eca8c88089e35226e8bab8896e05cb9846490627a952000054870000706154688d1eab2aa200018e0000000000000000dcd1a00000000000000035ecea100236000000812000bde36498e5483de54400000000054600089225419cc8a6d6a9295898a5fe47e600486428bea47421c3c2ad600059a0000b4786aba3d238818659c8465b20000000000008dca0c0007f81ee00041e000c0670ab628e28787cc000a246d4424000b460007e40000debd00000007689d8b820320000000001324a8adc5be3ca87e7dc5ba8cec9232824e8bc8867a21b824cd36000704ae00fecd4000974c54bbe7924683f60560000b00004445663066962ac0000f8d0e2fa00031a6664f2804000000b720000005403380b2000ac40000009680000001cc0000000002a20000005240000000000000000000000000002a80006721205a6860b06000afc0000000007360008487800006cecc466e46c8fcc9e00000014800ec3458e332560000700000b5c866ba28be274c80c76948790ad871486ac7095090eb80a8ac24322a5002005e1f4c2a44800078ca820000000008d0000000774608adaa0857450a79a03e5201c4c32304b70504000000c222320c487290cbfeaca2f8b6a3d8000a4e0004600007e0a9a9f0000d0acf20344a00000000000d47a63ec3ee6d03b40000003660003c0514a009da64241ca202ec3e8c026dea3c00000022a8de7d4c6202243209c00000000057c74cbac00000084200021400000035c00099e5f47241300006b400000022eb040005f23620b89a22105c0a4400073e0000000000000009647340000002721648c095e0c237c0005a4494ace9788b42e481c0000009c69fa9006ea3fe334324590b109f843e00000000000073c0000d200021e0000002a00008743f20000002080000002b600063000064c47a14a00060a02a0000001c800000000030a000196ab044e3be11c00058206a3b260cac809acd22426740000000000008303d045e258000000000c3c6d818c4ee0b63a092a000000000a62000a7cc60000000cd8000942412000bfc00086c00087a25ccdcc2e0e455a17cb24000908a4a17a64464e6e8b7c27e7fa01a9b4cbc914a98c4e4faa5640e6e4220b3abd22fe0004f600038440406c5d0d1c7b02c06368447d60002d26f85860fa9ec000532bdc49a00008a000c26bd81f02562e2000bc256839e000bb83f8710626b1c80a7700008360002768060000000006282f02c403aba835a2961821a272cc0a0000000000003700000000003a6000408cc68e64de4101b0a281e4922c7c1fcaf8cb880c8100741f80001aa000a8612200094c0003c463a0004c60000009e858092e0009d2000be8bf0000be40000000f2002d24000000a121605d2000c5eb50680000
  | 10 => 0x4000b5883e00000087c0009fcafe7c027c8280006f6000c2c1521b2110562b4c95a26211831cc8c40200000000062ca94b9c0000000000007a42be6e600076e0000000005b4baa000000000000728000b5498008200044013cb4800000000059e168000cf85d435482ca9c0008c600000048a00063c6c000051ab2e00000063823e29c194000cca794000000000c088e4000326a3ec64cd600024a3cc000a26ce6000c503da4dcb74b1883c4f481a17e6e06c600040c2880c800091c7aa838000c4409472a75e000668a5e000cfe000000a460000e00000004529660000d8adeb8ad200006843f0744708070820000000a3a00000097a000b564ca53a8f87c87ba7fe90233a228000bd6000b4ac1eb4200004a000ca8000b400008c80009b012e88e3a205a000342aa6bfa4b61dc000d109f2c0e1f6378c4626cb7a4008ea9ea6c81bc732a2c2c2538454280526292b520000000009ca8140aa0ac5080c60000a82d6000cf600055800000000046e0009acbeccb45ec7ead023562860d6000000518bda000000b226fe7820008c27183f40000000000000000000000000280000000005d64c200050200000000001c97c5b0346b5e6a600067600076418a8081c0af216676aba611a99c2840888b645c15e3e29a0234cc2000000a30c12b2a8eec282d8212542b6c0006029ae000000c56ca2934000a6e10ed2a0009c46ec2f24ae2ca0eca644360a6050226116604ce82ea0000d0000a1a0000000004ce000000000686cb277c00000001e1d20008a69aa9a40000000908c46fc4bc0006f4caeb260007024c06640000da34c000422c0c5508e8000000a2a0006b02e08907e66ca5fa564936390000b0ca706b67fc5fc0007ae344510b120860007f20ee752720bd4baec726ae000000414282a7e3a89442e6b8e8b89e21b480049c4f08fe5e8bca0ce0bcd340002baaac000b1a08c7ac32e8181ae0000680645b69a607c9c253e4203408b03580009b60000008aeb8c75a0001d0c84426a9e1ca5920002a6392000c5c000a7800000000093ecc89706cc77e0000000000000000006b83ac00007200000000000044a594b0a000024b5a6da000480000000b860000000000000009182980001f255e0008d200021ac40a5a0008626984a41560ba0000002a492613666a000d262aa20c178c6e0009f6c9410a984bf257292039abb48ac4961a61245e45c816a9ee07a5ce6a24cc00053ca1000086e00000000000000000000027000000000000033e000000a1e000000000000000308000af02ce0009e03fa3860008a2374000c1ad120005d80008f4a360000002c8000c98c301389980009900009ce00000000040a000cf029e52875069ecfa2400007de8da36051269aafabf6484c6667e04c0eaa4c90aaf696231067a8d470c876000162000000ae2748b
  | 11 => 0xa74aecc580968aab9204851ed040002cc00008e00000093a0003a4000482bb63000005306b27c21047462904d07220007bebe203c982b3c000726000462abe000a02cf4478000044b9e0c00000002440000e2264b9a1c23bc62e8b29be8cc18080e406000b8400051660e000c9cc860000002e8218b163d6956c88a8e6108fa730a90954396be64da004000000000cdaa66b3622c56a82e0000008506165ee0003ea0003686182b40000004f89960003e6d066ac4a60003185ae450c8e0184723e400000044c000776ce05e60000e67960002fc0009c8000988000ba45c25524e40000000000000bec20222b760007543c83c600020600000012c0000005aa000000622000816000cb662400045a00079c00000033037a7b63ba0000000000006a8202b20912000bee2604c4c3800000034a7e2a54576442b941061fa0005067f432028a660ccc2f6690000ae82d06a02d4000c00000af4c7a57094a108aa0a84d2cbcc4e0b3470e9724e8c141e607800085e8a87840f400098c19800000076600000065c8a0000000d163ceb6000023c9d495c000a181be0385000002de36e7c446a0004d805271a01452c2487161d400000000085a0007ee000000000aae28c61eba062a000000d32000a803b694600010c692000c96932bc6446d2242c620000ac60009860000000007982240001e200000082a1eab2c00054a000000382000000b662f465e8d69d6000928b78000b020fcc7820ea60ca443400078a4389e65dec5a134a7601614493c000b1e1761a4c9a23a0004b29c085c6ee0000925e065a4aaa96ad25a23b07c679e06638a38ec4c0004d60001840005b8000000000000852010000490000000000000000000a16858000076000250ce41ac0000f02b0cfc9de75c398a487720a000000000000000000002e0000000004d20000000000001460000005f600068e000000000158ac0aa4ab49ba78ea0643c5f857e1b615a2bc37e0000005362b80006541707d0000000000000b6e4168d832a66c26a000cd000089889a5ea012bb2a527b26dc56cd140003aaae6ad0c360085568540cc0000000005cca1cacc3ae52aabc910ce2080498b908640004ea74000015071c00052202c7384e6c425dc000788d0091ac68a5c7a099209ecceb002ee246026b6455458a26673a6627d25c6a586c2476c3e0003e00006f09161286ba4a200019ab146320007ec1a000029a0006940009760000000000006a49a8000ca036a0000003fc0000003d467cbc41da04ecc00000008321ec4acd282381140ca6e231264a00068c0000604702308a4d2e43a31406e07e00008457896ab7e0003760008840000007da9f41e03720e800000063e000a6800000000000041a1026be6c4ab61e8ae4896584bbc41854e0006bcc6ac1c5880008f6000000a3800000000082
  | 12 => 0x7e8856aee000b309fe84e000678000000000000000036b280004b8c3a6aa000be057ac7e94ea0ac901ce50e4d47b4268a8830ed0800049e00000000000000043030c006216
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe7218910006ef421891005eec421891000cff7118910014fe711891000cfd711891005ef57118910014fc711891005eef211891005ef62118910236ed2118910014ff701891000cfe7018910014fd701891005ef9701891000cfc701891005eef201891005efa201891022eed201891005cff7690910004fe7690910004fd769091005cfc76909100067f65909101d67c6590910006bf649091001ebc6490910015f67190910005f5719091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101be7c655091003cff76cc910004fe76cc910004fd76cc91003cfc76cc9100067f65cc9101a67c65cc910035be74cc910005bd74cc910006ef62cc910006ec62cc91000dfa70cc910005f970cc91005cff768c910004fe768c910004fd768c91005cfc768c9100067f658c91014e7c658c910006df638c91003edc638c910015f6718c910005f5718c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91016e7c654c91000dfa704c91005cff760c910004fe760c910004fd760c91005cfc760c91002d7e750c9100057d750c9100067f650c9101467c650c910006df630c91003edc630c910006ef620c91005eec620c910015f6710c910005f5710c91000dfa700c910005f9700c91000df476485100bef4764851000cf47648510225f77548510225f5754851000777654851021f746548510007b77448510007b47448510007d77348510007d47348510015f77248510017e77248510007e7624851005ef6624851005ef46248510007e46248510007e63248510007e53248510007f3704851000df6704851000df470485100bff07048510016f76048510017f360485100bff230485100bfe720485100bff220485100bfe52048510015f8764c11003ef8764c110014f8764c1100077b654c11021778654c11000dfb734c11000fdb734c110007db634c11003efa634c11003ef8634c110007d8634c110217da534c110217d9534c110007da434c110007d9434c110005fb724c110007f3714c110015fa714c110015f8714c11007ff0714c11000efb614c11000ff3614c11007ff2514c110217f1514c11007ff2214c110007f1214c110015f87648110046f87648110014f876481100077b754811020f7875481100077b654811020f786548110007bb7448110007b87448110005fb7348110005f9734811000dfb724811000feb7248110007eb624811005efa624811005ef86248110007e8624811020fea524811020fe95248110007f37148110015fa7148110015f87148110047f0714811000efb614811000ff36148110047f2514811020ff15148110047eb2148110047f22148110047e92148110007f12148110007e12148110
  | 1 => 0x8d1002d7e7598d100057d7598d100067f6598d100067c6598d10006df6398d100edf57198d1007df97098d1003cff7658d100057f7558d1002d7c7558d100067f6558d100067c6558d10005bf7458d10035bc7458d10005ef7258d10005ec7258d10105f77158d10095fb7058d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d1001cfc7458d10006bc7458d1001cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1005cfc7258d10006ec7258d10004ec7258d10104ff7158d10006f77158d100ecff7058d10006fb7058d1024cfe7618d100067f6518d100067c6518d10035be7418d10005bd7418d1003ede6318d10006dd6318d1003cff7690d10004fe7690d10004fd7690d1003cfc7690d100067f6590d102067c6590d10006bf6490d1001ebc6490d1000dfa7090d10005f97090d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d101ee7c6550d1001ebe6450d10006bd6450d10005f77150d10015f47150d100067f65d89100067c65d8910004ff75d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d891003cfe73d8910004fd73d8910006ef42d8910006ec42d891000cff71d891000cfd71d8910246ef21d8910246ed21d8910014ff70d8910014fd70d891023eef20d891023eed20d89100bcfd769891002d7e75989100057d75989100067f65989100067c6598910006ef62989100bdf57198910045f9709891005cff7598910024fe759891005e7e75989100247e7598910004fd759891005e7d75989100047d759891005cfc759891001cfe7498910004fd749891005cfc749891003cfe7398910004fd739891005cfe72989100bcfd719891005ef5719891005ef621989100d4fd709891005ef9709891005efa20989100057f755891002d7c75589100067f65589100067c6558910005bf7458910035bc7458910005df7358910005dc73589100d5f77158910065fb7058910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df735891003cfc7358910006dc735891003cdc7358910006ef72589100d4ff7158910006f771589100bcff7058910006fb705891023cfe76189100067f65189100067c6518910006ed621891005cff7518910024fe7518910004fd751891005cfc751891001cfe7418910004fd741891005cfc741891003cfe7318910004fd731891005cfe721891005ee
  | 2 => 0x7b864c812000dfa72c812000fea72c812000efb62c812000feb62c812005fea52c8120297e952c8120005f971c812005feb21c8120007e921c812028d7e76d951002e7e76d95100247e76d95100067e64d95100067c64d951027f7771d951027f7471d95102877621d951027f7a30d951027f7a20d95102877b10d951027f7610d951027f7410d951027f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067c42d951027e7f71d95102867e71d951027e7d71d951027e7c71d95102867f41d95102867e41d95102867d41d95102867c41d95102867f31d95102867e31d95102867d31d95102867c31d95102867f21d95102867e21d95102867d21d95102867c21d951027e7f70d951027e7e70d951027e7d70d951027e7c70d951027e7f40d951027e7e40d951027e7d40d951027e7c40d951027e7f30d951027e7e30d951027e7d30d951027e7c30d951027e7f20d951027e7e20d951027e7d20d951027e7c20d951027e7f10d951027e7e10d951027e7d10d951027e7c10d951001cfe76d91100067f65d91100067c65d9110036be64d9110004ff75d9110024fe75d9110004fd75d9110024fc75d911011cfd74d911003cfe73d9110004fd73d9110036bc43d911005cfe72d9110004fd72d9110036bc42d911000cff71d9110014fe71d911000cfd71d9110014fc71d9110276bf41d9110276bd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110266bf40d9110266bd40d911001cff76591100057f755911002d7c75591100067f65591100067c6559110036bc6459110005df7359110005dc7359110005ef7259110005ec725911025df7715911026dfb7059110004ff75591100067f75591100047f7559110024fe7559110004fd7559110024fc75591100067c75591100247c7559110264ff7459110006bf7459110036be5459110006bd5459110004ff7359110006df7359110004df735911003cfc7359110006dc735911003cdc7359110036bf4359110004ff7259110006ef7259110004ef725911005cfc7259110006ec7259110004ec725911025cff7159110006f7715911011cff7059110006fb705911003cfe76d8d100067f65d8d100067c65d8d10004ff75d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df43d8d10006dc43d8d1005cfe72d8d10004fd72d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d10256df31d8d10256dd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d1024edf30d8d1024edd30d8d100ecfd769
  | 3 => 0xf645092001ebc6450920005fb705092000df8705092000cfe76cc92000cfc76cc9200067f65cc9201a67c65cc92004dbe74cc920005bd74cc920006bf64cc92019ebc64cc920006df63cc92003edc63cc92000dfa70cc920005f970cc92012cfe768c9200067f658c92014e7c658c920006bf648c920186bc648c92003cff764c92000cfe764c920154fd764c92000cfc764c9200067f654c92016e7c654c920006bf644c920166bc644c920006df634c92003edc634c920005fb704c92000df8704c920174fe760c9200557e750c9200057d750c9200067f650c9201467c650c920006bf640c92013ebc640c920014fe76d85200067f65d85200067c65d8520006bf64d8520006bc64d8520046f661d8520004ff75d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d852003cfe73d8520004fd73d852000cfd72d8520014fc72d8520046f431d8520046f621d852000cfe70d852000cfc70d85200d6f710d85200057f75585200557c75585200067f65585200067c6558520005bf745852004dbc7458520006bf6458520006bc6458520005df7358520005dc7358520046f46158520004ff7650520004fe7650520004fc76505200067f65505201267c6550520006bf645052001ebc6450520004fe76cc520004fd76cc52003cfc76cc5200067f65cc5201167c65cc520006bf64cc52010ebc64cc520006f761cc520016f461cc520004ff764c520004fe764c520004fc764c5200067f654c5200fe7c654c520006bf644c5200f6bc644c52022cfe76c85200067f65c85200e67c65c8520006bf64c85200debc64c852000df870c852005fe820c852022dee76c8520246ee76c85202b5ef75c85202b5ed75c85200076f65c85202af6c65c8520007af64c8520007ac64c8520006ef63c8520006ed63c85200bded71c8520016ee61c8520016ec61c852005feb70c852000dee70c852000dec70c852005fe870c852005eef60c85200d7ea10c852000cfc76485200067f65485200ce7c6548520005bf744852004dbc7448520006bf64485200c6bc6448520005df7348520005dc7348520006f76148520016f46148520047e42148520005fb704852000df870485200bfe8204852000dec7648520016ec764852000cec76485202a5ef75485202a5ed75485200076f654852029f6c6548520007af7448520007ac7448520007af6448520007ac6448520007cf7348520007cc7348520006ef6348520006ed63485200d5ef7148520007e77148520007e76148520016ee6148520016ec6148520047e46148520007eb704852000dee704852000dec70485200bfe870485200beef60485200bfe710485200bfea104852000dfa76c812000efa76c812000cfa76c81200077b65c81202977865c8120007bb64c8120
  | 4 => 0x91201c6bf50d91201c6be50d91201c6bd50d91201c6bc50d91201c6bf30d91201c6be30d91201c6bd30d91201c6bc30d91201c6bf20d91201c6be20d91201c6bc20d91201c6bf10d91201c6be10d91201c6bd10d91201c6bc10d91200057f75591200557c75591200067f65591200067c655912004ebc64591202c5ef7259120004ff75591200067f75591200047f7559120024fe7559120004fd7559120024fc75591200067c75591200247c75591201c4ff7459120006bf7459120004ff735912003cfc73591202c4ff7259120006ef7259120004ff7159120014fe7159120014fc71591201acff7059120006fb70591201c5be761912004ebe76191201c4be7619120006bf65191200073f65191200063f6519120006be6519120006bd6519120006bc65191200073c65191200063c65191202bebf6219120007ae5219120007ad5219120006be6119120006bc61191202bebf60191202bfae20191202bfac20191202bfb820191202bfba101912003cfe76d8d200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d20004ff75d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d2005cfe72d8d2005cfc72d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20006dc31d8d2005cff70d8d20174fd70d8d20176df30d8d20176dd30d8d20176fa10d8d200557e7598d200057d7598d200067f6598d200067c6598d2004dbe7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d20155ed7298d200057f7558d200557c7558d200067f6558d200067c6558d20005bf7458d2004dbc7458d20006bf6458d20006bc6458d2018def7258d20005f77158d20045f47158d20004ff7558d200067f7558d200047f7558d20024fe7558d20004fd7558d20024fc7558d200067c7558d200247c7558d20004ff7458d20006bf7458d20004bf7458d2001cfe7458d2001cfc7458d20006bc7458d2001cbc7458d20006df7358d2018cff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20014fe7158d20014fc7158d20006f47158d20014f47158d20154ff7058d20006fb7058d20156fa1058d20174fe7618d200067f6518d200067c6518d20006bf6418d20006bc6418d2003ede6318d20006dd6318d2003cff7690d20004fe7690d20004fd7690d2003cfc7690d200067f6590d202067c6590d20006bf6490d2001ebc6490d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d201ee7c6550d20006bf6450d2001ebc6450d20005ef7250d20005ec7250d202bcfe76909200067f65909201d67c65909201c6bf649092001ebc649092001cff765092000cfe76509201acfd765092000cfc76509200067f65509201be7c6550920006b
  | 5 => 0x5fea70c872005fe970c872000dec70c872023cff7648720005bf744872006dbc7448720005df7348720005dc7348720016f4614872005fe4214872023def7648720236ef76487202ddef75487202dded7548720007af7448720007ac7448720007cf7348720007cc7348720006ef6348720006ed634872005fe7714872005fe76148720016ee6148720016ec614872005fe4614872000dee704872000dec70487200bfe710487202d57e76d95200567e76d95200247e76d95200067e64d95200067c64d95202cf6f72d95202cf6c72d95200067e61d95200067c61d95202cf6e20d95202cf6c20d95202cf7820d95202cf7a10d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067c43d95202ce7f72d95200567e72d95202ce7d72d95202ce7c72d95200067f42d95200067c42d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067c41d95200067e31d95200067c31d95200067e21d95200067c21d95202ce7f70d95202ce7e70d95202ce7d70d95202ce7c70d95202ce7f40d95202ce7e40d95202ce7d40d95202ce7c40d95202ce7f30d95202ce7e30d95202ce7d30d95202ce7c30d95202ce7f20d95202ce7e20d95202ce7d20d95202ce7c20d95202ce7f10d95202ce7e10d95202ce7d10d95202ce7c10d952001cfe76d91200067f65d91200067c65d912004ebe64d9120004ff75d9120024fe75d9120004fd75d9120024fc75d9120006bf54d912004ebe54d9120006bd54d912004ebc54d912003cfe73d9120004fd73d912004ebf43d912004ebc43d912005cfe72d912000cfd72d912005cfc72d912004ebf42d9120014fe71d9120004fd71d9120014fc71d912004ebf41d9120006be41d912004ebc41d912005cff70d91201c4fd70d91201c6bf40d91201c6bd40d91202bdbe76d912001cbe76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120007ae52d9120007ad52d9120006be61d9120006bc61d91201c7ae20d91201c7ac20d91201c7b820d91201c7ba10d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d91201c6bf72d912004ebe72d91201c6bd72d9120006bf52d9120006be52d9120006bd52d9120006bc52d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006be31d9120006bc31d9120006be21d9120006bc21d91201c6bf70d91201c6be70d91201c6bd70d91201c6bc70d
  | 6 => 0xe74d8530004fd74d853001cfc74d853000cfd73d8530014fc73d853005cfe72d8530004fd72d853007ef631d853007ef421d853003cfd70d8530106f710d85300057f755853008d7c7558530005bf7458530085bc7458530005ef7258530005ec725853007ef46158530004ff7650530004fe7650530004fc76505300079d435053000cfc764c530006f7614c530016f4614c530005fb704c53000df8704c530004fe76c8530004fd76c853005cfc76c8530006f761c8530016f461c8530004ff7648530004fe7648530004fc7648530005bf7448530085bc7448530005df734853003ddc734853005cff75d9320024fe75d9320004fd75d932005cfc75d93201acfd74d932006ebe54d9320006bd54d932003cfe73d9320004fd73d932006ebf43d932005cfe72d932005eee72d9320014fe71d9320004fd71d9320014fc71d932005ef970d93201c6be40d93201c6bc40d932001cff765932005ebc6459320004ff7559320024fe7559320004fd7559320024fc755932005ebf7459320004ff735932003cfc735932001cff725932000cfe725932001cfd725932000cfc725932005ebe425932005ebc4259320004ff7159320014fe7159320014fc71593201aebf40593201aebd405932005cff75d8f20024fe75d8f20004fd75d8f2005cfc75d8f2001cfe74d8f20004fd74d8f2005cfc74d8f2005cfe72d8f2005eee72d8f20014fe71d8f20004fd71d8f20014fc71d8f2005ef970d8f20154fd7698f2006dbe7498f20005bd7498f2005edf6398f2005edc6398f2003cff7658f2005edc6358f20004ff7558f20024fe7558f20004fd7558f20024fc7558f20004ff7458f2001cfe7458f2001cfc7458f2005edf7358f2003cff7258f2000cfe7258f2003cfd7258f2000cfc7258f2005ede3258f2005edc3258f20004ff7158f20014fe7158f20014fc7158f20156df3058f20156dd3058f2003cff7690f2005cfe7690f20004fd7690f2005cfc7690f20004ff7650f2005cfe7650f20004fd7650f2005cfc7650f20006bf6450f2001ebc6450f20005ef7250f2005dec7250f202c4ff7650b20154fd76ccb2006dbe74ccb20005bd74ccb2018cff764cb20014ff765872005ef46158720004ff7558720024fe7558720004fd7558720024fc7558720004ff745872001cfe745872001cfc7458720004ff735872003cfc7358720014fd725872000cfc725872005ef7215872005ef421587200befa20587200bef71058720004ff7650720004fd765072005cfc765072003cff76cc72005cfe76cc720004fd76cc720004ff764c720004fd764c72005cfc764c72000ded76c8720016ed76c872000ced76c872005def75c87202e5ed75c872005eef63c8720006ed63c8720016ee61c872005fe661c872005fe561c8720016ec61c872000dee70c8720
  | 7 => 0x7300079d435073005cff76c873003cfe76c8730004fd76c87300e67e65c87300067d65c873005eee62c8730006ed62c8730004ff7648730004fd764873003cfc76487300ce7e65487300067d6548730005bf744873009dbc7448730005df734873003ddc7348730006ee6248730006ed624873001cfe76d9130086be64d9130004ff75d9130024fe75d9130004fd75d9130024fc75d9130086be54d9130006bd54d913003cfe73d913000cfd73d913003cfc73d9130086bf43d913005cfe72d9130004fd72d9130086bc42d9130014fe71d9130004fd71d9130014fc71d9130006be41d9130086bc41d913003cff70d913003cfd70d91301f6bf40d91301f6bd40d9130086bc645913030ddf7359130004ff7559130024fe7559130004fd7559130024fc75591301f4ff7459130006bf745913030cff7359130006df7359130004ff725913005cfc7259130004ff7159130014fe7159130014fc71591301dcff7059130006fb7059130305de7690d3003ede7690d3003ddf7590d302fddd7590d301dddd7490d3001ede6490d3001edc6490d300879e5490d302f79d5490d3000dde7090d3000ddc7090d3003edf6090d3003fdb6090d301f7da1090d3001cff7650d3000cfe7650d301dcfd7650d3000cfc7650d30006bf6450d3001ebc6450d3003f9c4350d30005fb7050d3000df87050d3003fd83050d3000ddc7650d3001edc7650d3000cdc7650d302eddf7550d302eddd7550d3003ddf7450d3003f9f7450d300079f6450d3001ede6450d3001edc6450d300879c6450d300879c4250d300879f4150d30007db7050d3000dde7050d3000ddc7050d301dfd87050d3003edf6050d3003fdb6050d301df9f4050d301df9d4050d301dfda1050d30004ff75d8930024fe75d8930004fd75d8930024fc75d893001cfe74d8930004fd74d893001cfc74d8930014fe71d8930004fd71d8930014fc71d8930006ee21d8930006ec21d893003cfd70d893018eef20d893018efa10d8930006ef62989300057f755893008d7c7558930005bf7458930085bc7458930005f7715893007df47158930006ed621893005cff7518930024fe7518930004fd751893005cfc751893001cfe7418930004fd741893005cfc7418930014fe7118930004fd7118930014fc7118930006ee211893005eec211893005cff701893003cfd701893005eef201893012eed2018930004fe7690930004fd769093005cfc7690930006bf649093001ebc64909300079d4390930004ff7650930004fe7650930004fc765093000cfe768c930006ef628c93005eec628c93000dfa708c930005f9708c93000cfc764c930006ef624c930006ec624c930005fb704c93000df8704c930014fe76d853007ef661d8530004ff75d8530024fe75d8530004fd75d8530024fc75d853001cf
  | 8 => 0x4fc7648540005bf744854001dbc7448540005df7348540005dc73485400067f74597300067e74597300067d74597300067c745973003e7f735973003e7e735973003e7d735973003e7c735973003e7f435973003e7e435973003e7d435973003e7c43597300067f72597300067e72597300067d72597300067c72597300067f42597300067c425973003e7f325973003e7e325973003e7d325973003e7c32597300067f71597300067e71597300067d71597300067c71597300067f41597300067e41597300067c415973003e7f315973003e7e315973003e7d315973003e7c31597300067e21597300067c21597303267f70597303267e70597303267d70597303267c70597303267f40597303267e40597303267d40597303267c405973003e7f305973003e7e305973003e7d305973003e7c30597303267f20597303267e20597303267d20597303267c20597303267f10597303267e10597303267d10597303267c1059730004ff7559330024fe7559330004fd7559330024fc755933003ebf745933003cff735933000cfe735933003cfd735933000cfc735933003ebe435933003ebc4359330004ff725933005cfc725933009ebc4259330004ff7159330014fe7159330014fc715933009ebf41593301debf40593301debd405933003ddf7650f3031edf7650f30315df7550f30315dd7550f3003f5e6550f3003f5d6550f3003f9f7450f3003f9f6450f3001ede6450f3003edc6450f3003f9c6450f3009f9c4250f3009f9f4150f3000dde7050f3000ddc7050f301df9f4050f301df9d4050f3005cff7598b30024fe7598b30004fd7598b3005cfc7598b3001cfe7498b30004fd7498b3005cfc7498b3000cfe7398b3000cfc7398b3005eee7298b30006ef4298b3005eec4298b3003eef3298b3005eec3298b30014fe7198b30004fd7198b30014fc7198b3005eef2098b30176ed2098b30004ff7558b30024fe7558b30004fd7558b30024fc7558b30004ff7458b3001cfe7458b3001cfc7458b3000cfc7358b3003eef7258b30006ef4258b30006ec4258b3003eef3258b3003eec3258b30004ff7158b30014fe7158b30014fc7158b30156ef2058b3005cff7690b3003cfe7690b30004fd7690b301d67e6590b300067d6590b3001ebe6490b30006bd6490b300079d4390b30004ff7650b30004fd7650b3003cfc7650b301be7e6550b300067d6550b30004ff7558730024fe7558730004fd7558730024fc7558730004ff745873001cfe745873001cfc745873000cfe7358730014fd735873000cfc7358730004ff725873005cfc725873003ef7715873003ef7315873003ef4315873003efa305873003ef930587300eef71058730004ff7650730004fd765073003cfc76507301267e65507300067d655073001ebe6450730006bd645
  | 9 => 0xa20d81210befa10d81210057f75581210cd7c7558121005bf74581210c5bc7458121006bf6458121006bc6458121005df7358121005dc7358121006df6358121006dc63581210bef8605812103cfe76d8d40004ff75d8d40024fe75d8d40004fd75d8d40024fc75d8d4000cfd74d8d40356de43d8d40356dd43d8d4005cfe72d8d40004fd72d8d40014fe71d8d40004fd71d8d40014fc71d8d40006de31d8d40006dc31d8d4001cfd70d8d4030edf30d8d400b57e7598d400057d7598d40006df6398d40005ee7298d40005ed7298d40085f97098d4009dfb7058d4003ede6318d40006dd6318d4000dbc7650d4003ebc7650d4000cbc7650d4034dbf7550d4034dbd7550d4001dbf7350d4001f9f7350d400079f6350d4003ebe6350d4003ebc6350d400079c6350d40007bb7050d4000dbe7050d4000dbc7050d401dfb87050d4001ebf6050d4001fbb6050d40004ff75d8940024fe75d8940004fd75d8940024fc75d894000cfd74d894003cfe73d8940004fd73d8940006ef52d8940006ec52d8940346ee42d8940346ed42d8940014fe71d8940004fd71d8940014fc71d8940006ee21d8940006ec21d894001cfd70d89402c6ef20d8940006ef629894004df970989400057f75589400b57c755894006dfb7058940006ed621894005cff7518940024fe7518940004fd751894005cfc751894000cfd741894033ebe5418940006bd541894003cfe7318940004fd731894033ebf4318940006bd4318940006ef521894005eec521894005eee421894033eed4218940014fe7118940004fd7118940014fc7118940006ee211894005eec211894005cff701894001cfd70189402bebe40189402bebc401894005eef20189402beed2018940004fe76cc940004fd76cc94003cfc76cc94001dbe74cc940005bd74cc940004fe768c940004fd768c94005cfc768c940006ef628c94005eec628c940004ff764c940004fe764c940004fc764c940006ef624c940006ec624c940004fe760c940004fd760c94005cfc760c9400b57e750c9400057d750c94001dbe740c940005bd740c94000dfa700c940005f9700c940014fe76d85400aef661d8540004ff75d8540024fe75d8540004fd75d8540024fc75d854000cfd74d8540014fc74d8540336be54d8540006bd54d854003cfe73d8540004fd73d8540336bf43d8540006bd43d854005cfe72d8540004fd72d85400aef641d8540336f541d854001cfd70d854025ef710d85400057f75585400b57c7558540005df7358540005dc7358540005ef7258540005ec72585400aef4615854032dfb7058540004fe76cc540004fd76cc54003cfc76cc54001dbe74cc540005bd74cc540004ff764c540004fe764c540004fc764c540004fe76c8540004fd76c854005cfc76c8540004ff7648540004fe7648540
  | 10 => 0x8d21006df4218d21006dc4218d2103edf7118d2103ede7118d2103edd7118d2103edc7118d21136df5118d21136de5118d21136dd5118d21136dc5118d21136df4118d21136de4118d21136dd4118d21136dc4118d21136df2118d21136de2118d21136dd2118d21136dc2118d2103edf7018d2103ede7018d2103edd7018d2103edc7018d21006df5018d21006de5018d21006dd5018d21006dc5018d21006df4018d21006de4018d21006dc4018d21006de2018d21006dc2018d21136df1018d21136de1018d21136dd1018d21136dc1018d2103cff7690d21004fe7690d21004fd7690d2103cfc7690d21006bf6490d2101ebc6490d21006df6390d2103edc6390d21005ee7290d21005ed7290d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2101ebc6450d21006df6350d2103edc6350d2135cfe76909211cebf649092101ebc6490921006df6390921006dc639092105fe4219092101cff7650921014fe76509211b4fd7650921014fc7650921006bf645092101ebc6450921006df6350921006dc6350921005f77150921015f471509211b7e42150921014fe76cc921014fc76cc9210c5be74cc921005bd74cc921006bf64cc92119ebc64cc921006df63cc92103edc63cc921015f671cc921005f571cc921197e421cc921134fe768c921006bf648c921186bc648c92117edf638c92103edc638c921135ee768c921006ee768c921007af648c921007ac648c92115ded738c92117fcf638c92103eee638c92103eec638c921007cc638c92103ecc638c921015ee718c921015ec718c92105eef618c92117fce318c92117fcc318c921005ed708c92117fe7108c92103cff764c921014fe764c92115cfd764c921014fc764c921006bf644c921166bc644c921006df634c92103edc634c921005f7714c921015f4714c921015ec764c92103eec764c921014ec764c921007af644c921007ac644c921007cf734c921007cf634c92103eee634c92103eec634c921007cc634c921007e7714c921015ee714c921015ec714c92115fe4714c921015e4714c92115eef614c921005ef704c92115fe7104c92117cfe760c9210cd7e750c9210057d750c921006bf640c92113ebc640c921006df630c92103edc630c92117dee720c92105fe4210c921007b764c8521007b464c8521007d763c8521007d463c8521015f672c8521017e672c8521016f762c8521017e762c852105fe632c8521007e532c8521005f570c852100cfe76d8121006bf64d8121006bc64d8121006df63d8121006dc63d81210befa60d8121004ff75d8121024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d812103cfe73d8121004fd73d8121014fd72d812100cfc71d8121006fb50d81210bef850d81210bef
  | 11 => 0x4fd74d8d2101cfc74d8d21006df53d8d21006de53d8d21006dd53d8d21006dc53d8d21006df43d8d21006dc43d8d2105cff71d8d2117cfd71d8d2117edf31d8d2117edd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d2103cde76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d210079f64d8d210069f64d8d21006de64d8d21006dd64d8d21006dc64d8d210079c64d8d210069c64d8d2117fcf72d8d2117fce21d8d2117fcc21d8d2117fd421d8d21006de60d8d21006dc60d8d2117fd710d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d2117edf72d8d2117edd72d8d21006df52d8d21006de52d8d21006dd52d8d21006dc52d8d21006df42d8d21006dc42d8d2117edf71d8d2117ede71d8d2117edd71d8d2117edc71d8d2117edf51d8d2117ede51d8d2117edd51d8d2117edc51d8d2117edf41d8d2117ede41d8d2117edd41d8d2117edc41d8d2117edf21d8d2117ede21d8d2117edc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dc40d8d21006de20d8d21006dc20d8d2117edf10d8d2117ede10d8d2117edd10d8d2117edc10d8d210c5be7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d2115ded7298d21005bf7458d210c5bc7458d21006bf6458d21006bc6458d21195ef7258d21004ff7558d21024fe7558d21004fd7558d21024fc7558d21004ff7458d21006bf7458d21004bf7458d2101cfe7458d2101cfc7458d21006bc7458d2101cbc7458d21006df7358d21194ff7258d21006ef7258d2115cff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d2117cfe7618d210cd7e7518d210057d7518d21006bf6418d21006bc6418d2103ede6318d21006dd6318d2117dde7618d21006de7618d2117cde7618d210075e7518d210075d7518d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d210079f6418d210069f6418d21006de6418d21006dd6418d21006dc6418d210079c6418d210069c6418d21137cd7218d21137ce2118d21137cc2118d21137d42118d21006de6018d21006dc6018d21137d71018d2103edf7518d2103ede7518d2103e5e7518d2103edd7518d2103e5d7518d2103edc7518d2103edf7418d2103ede7418d2103edd7418d2103edc7418d21006df5418d21006de5418d21006dd5418d21006dc5418d2103edf7218d2103edd7218d2103ecd7218d21006df5218d21006de5218d21006dd5218d21006dc521
  | 12 => 0xe638cb2105fcd638cb2105eec638cb21015ee718cb2105fe6718cb2105fe5718cb21015ec718cb2117fce318cb2117fcc318cb21005ed708cb21194ff764cb21195ef764cb21006ef764cb2105fcf734cb2103eee634cb2103eec634cb21015ee714cb21015ec714cb21005ef704cb2100cff765832105ef86058321004ff7558321024fe7558321004fd7558321024fc7558321004ff745832101cfe745832101cfc7458321004ff735832103cfc7358321014fc7258321046f6215832105efb205832105ef820583210d6fa105832101cfe76d91210c6be64d9121004ff75d9121024fe75d9121004fd75d9121024fc75d9121006bf54d91210c6be54d9121006bd54d91210c6bc54d912103cfe73d9121004fd73d91210c6bf43d91210c6bc43d9121014fd72d91210c6bf42d912105cff71d91211ccfd71d91211cebf41d91211cebd41d912100cfe70d9121004fd70d912100cfc70d91210c6bf40d9121006be40d91210c6bc40d912135dbe76d912101cbe76d9121006bf65d9121006be65d9121006bd65d9121006bc65d91211cfae21d91211cfac21d91211cfb421d9121006be60d9121006bc60d91211cfb710d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bd53d9121006bc53d91211cebf72d91210c6be72d91211cebd72d9121006bf52d9121006be52d9121006bd52d9121006bc52d91211cebf71d91211cebe71d91211cebd71d91211cebc71d91211cebf51d91211cebe51d91211cebd51d91211cebc51d91211cebf31d91211cebe31d91211cebd31d91211cebc31d91211cebf21d91211cebe21d91211cebc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bd50d9121006bc50d9121006be30d9121006bc30d9121006be20d9121006bc20d91211cebf10d91211cebe10d91211cebd10d91211cebc10d91210c6bc6459121005df7359121005dc7359121365ef7259121004ff7559121024fe7559121004fd7559121024fc75591211ccff7459121006bf7459121004ff7359121006df7359121004df735912103cfc7359121006dc735912103cdc7359121364ff7259121006ef72591211b4ff7159121006f77159121004ff705912100cfe705912100cfc70591211cdbe76191210c6be76191211ccbe76191210c73e75191210c73d7519121006bf6519121006be6519121006bd6519121006bc651912135ebf621912135ebf611912135fae211912135fac211912135fb42119121006be6019121006bc601912135fb7101912103cfe76d8d21006bf64d8d21006bc64d8d21004ff75d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21
  | 13 => 0x893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d8931006ef6298931005bf74589310f5bc7458931006ed621893105cff7518931024fe7518931004fd751893105cfc751893101cfe7418931004fd741893105cfc741893105eee5218931006ed5218931006ef421893105eec421893105cff711893103cfd7118931136de3118931136dc311893105eef2118931136ed211893100cfe7018931004fd701893100cfc7018931006ee201893105eec2018931004fe7690931004fd769093105cfc7690931006bf649093101ebc6490931004ff7650931004fe7650931004fc7650931014fe768c93117edf638c931006ef628c93105eec628c931015f6718c931005f5718c931014fc764c931006ef624c931006ec624c931005f7714c931015f4714c93100cfe76d81310eefa60d8131004ff75d8131024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d8131014fd73d813100cfc73d813105cfe72d8131004fd72d813103cfd71d81310eefa30d81310eefa10d81310057f75581310fd7c7558131005bf74581310f5bc7458131005ef7258131005ec72581310eef8605813105cff75d9321024fe75d9321004fd75d932105cfc75d93211b4fd74d93210debe54d9321006bd54d932103cfe73d9321004fd73d93210debf43d932105cfe72d932105eee72d932105ef571d93211cebe41d93211cebc41d932100cfe70d9321004fd70d932100cfc70d932101cff765932105ebc6459321004ff7559321024fe7559321004fd7559321024fc755932105ebf7459321004ff735932103cfc7359321014fe7259321014fc725932105ebe425932105ebc42593211b6bf41593211b6bd4159321004ff705932100cfe705932100cfc705932105cff75d8f21024fe75d8f21004fd75d8f2105cfc75d8f2101cfe74d8f21004fd74d8f2105cfc74d8f2105cfe72d8f2105eee72d8f2105ef571d8f2117ede31d8f2117edc31d8f2100cfe70d8f21004fd70d8f2100cfc70d8f2115cfd7698f210ddbe7498f21005bd7498f2105edf6398f2105edc6398f2103cff7658f2105edc6358f21004ff7558f21024fe7558f21004fd7558f21024fc7558f21004ff7458f2101cfe7458f2101cfc7458f2105edf7358f21014fe7258f21014fc7258f2105ede3258f2105edc3258f2115edf3158f2115edd3158f21004ff7058f2100cfe7058f2100cfc7058f2103cff7690f2105cfe7690f21004fd7690f2105cfc7690f2105dee7290f21005ed7290f21004ff7650f2105cfe7650f21004fd7650f2105cfc7650f21006bf6450f2101ebc6450f21005f77150f21015f47150f21364ff7650b2115cfd76ccb210ddbe74ccb21005bd74ccb21015ed768cb2105eed768cb21014ed768cb2103eee638cb2105fc
  | 14 => 0x5f5710c94100cfe76d814111efa60d8141004ff75d8141024fe75d8141004fd75d8141024fc75d8141014fd74d814100cfc74d814132ebe54d8141006bd54d814103cfe73d8141004fd73d814132ebf43d8141006bd43d814105cfe72d8141004fd72d814101cfd71d814111efa40d814111efa10d81410057f75581411257c7558141005df7358141005dc7358141005ef7258141005ec725814111ef86058141004ff7559331024fe7559331004fd7559331024fc755933103ebf7459331014fe7359331014fc735933103ebe435933103ebc4359331004ff725933105cfc725933110ebc42593311e6bf41593311e6bd4159331004ff705933100cfe705933100cfc705933110ebf405933105cff7598b31024fe7598b31004fd7598b3105cfc7598b3101cfe7498b31004fd7498b3105cfc7498b31014fe7398b31014fc7398b3105eee7298b3103eef3298b3105eec3298b3117ede3198b3103edc3198b3105eef2198b3117eed2198b3100cfe7098b31004fd7098b3100cfc7098b31004ff7558b31024fe7558b31004fd7558b31024fc7558b31004ff7458b3101cfe7458b3101cfc7458b31014fc7358b3103eef7258b3103eef3258b3103eec3258b3115eef2158b31004ff7058b3100cfe7058b3100cfc7058b3105cff7690b3103cfe7690b31004fd7690b3101ebe6490b31006bd6490b31004ff7650b31004fd7650b3103cfc7650b31005f77150b31015f47150b31004ff7558331024fe7558331004fd7558331024fc7558331004ff745833101cfe745833101cfc7458331014fe735833100cfd7358331014fc7358331004ff725833105cfc725833103efb705833103efb305833103ef83058331106fa105833101cfe76d91310f6be64d9131004ff75d9131024fe75d9131004fd75d9131024fc75d91310f6be54d9131006bd54d9131014fd73d91310f6bf43d913105cfe72d9131004fd72d91310f6bc42d913103cff71d913103cfd71d91311febf41d91311febd41d913100cfe70d9131004fd70d913100cfc70d9131006be40d91310f6bc40d91310f6bc645913136ddf7359131005ef7259131005ec7259131004ff7559131024fe7559131004fd7559131024fc75591311fcff7459131006bf745913136cff7359131006df7359131004ff7259131006ef7259131004ef725913105cfc7259131006ec7259131004ec72591311e4ff7159131006f77159131004ff705913100cfe705913100cfc705913101cff7650d31014fe7650d311e4fd7650d31014fc7650d31006bf6450d3101ebc6450d31005f77150d31015f47150d31004ff75d8931024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d8931006ee52d8931006ed52d8931006ef42d8931006ec42d893103cfd71d8931196ef21d
  | 15 => 0xf764c832004df764c83205f5e654c83205f5d654c83205ddf724c83203fcf724c83205ede624c83205fce624c83205fce524c832397cd524c832135de714c832135dc714c832004ff7558432024fe7558432004fd7558432024fc7558432004ff745843201cfe745843201cfc745843203eee325843203eed325843205ef77158432136f6415843203ef73158432136de315843203edc315843203ef4315843205ef7215843205ef42158432004ff705843200cfe705843200cfc7058432136f71058432004ff7558032024fe7558032004fd7558032024fc7558032004ff745803201cfe745803201cfc7458032004ff7158032014fe7158032014fc715803205efb705803212efa405803203efb305803203ef8305803205efb205803205ef8205803212efa105803203cfe76d8d41004ff75d8d41024fe75d8d41004fd75d8d41024fc75d8d41014fd74d8d41006de53d8d41006dd53d8d4138ede43d8d4138edd43d8d4105cfe72d8d41004fd72d8d4101cfd71d8d4136edf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d41006df6398d410f5f57198d41005ef7258d41005ec7258d4110df77158d4103ede6318d41006dd6318d41015bc7650d4103ebc7650d41014bc7650d41385bf7550d41385bd7550d4101dbf7350d4101f9f7350d410079f6350d4103ebe6350d4103ebc6350d410079c6350d4103e9c6350d41007b77150d41015be7150d41015bc7150d411e7b47150d4101ebf6150d4101fb76150d41004ff75d8941024fe75d8941004fd75d8941024fc75d8941014fd74d894103cfe73d8941004fd73d8941006ee52d8941006ed52d894137eee42d894137eed42d894101cfd71d8941366ef21d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d8941006ef62989410c5f57198941005df7358941005dc73589410ddf77158941006ed621894105cff7518941024fe7518941004fd751894105cfc7518941014fd7418941376be5418941006bd541894103cfe7318941004fd7318941376bf4318941006bd431894105eee5218941006ed521894105eee4218941376ed421894105cff711894101cfd711894135ebe411894135ebc411894105eef211894135eed211894100cfe7018941004fd701894100cfc7018941006ee201894105eec2018941004fe76cc941004fd76cc94103cfc76cc94101dbe74cc941005bd74cc941006ef62cc941006ec62cc941004fe768c941004fd768c94105cfc768c941006df638c94103edc638c941004ff764c941004fe764c941004fc764c941004fe760c941004fd760c94105cfc760c9411257e750c9410057d750c94101dbe740c941005bd740c941006df630c94103edc630c941006ef620c94105eec620c941015f6710c941
  | 16 => 0x9132004ff7559132024fe7559132004fd7559132024fc7559132164ff7459132006bf7459132184ff7359132006df735913219cff7259132006ef7259132166bc4259132004ff7159132006f77159132004f77159132014fe7159132014fc7159132006f47159132014f47159132004ff705913200cfe705913200cfc705913201cfc7650d32006bf6450d3201ebc6450d3203f9c4350d32005ef7250d32005ec7250d3219cfe769093201ebe6490932006bd649093201cff7650932164fd765093203cfc7650932006bf645093201ebc6450932005df735093203ddc735093203dee728c93203eef628c93205dde728c93205edf628c93203fcf628c93217ede618c93217edc618c932014fe76d853215ef661d8532004ff75d8532024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d853203cfd72d853215ef651d8532006f551d8532006f741d853215ef441d853215ef631d853215ef621d853200cfe70d8532004fd70d853200cfc70d8532006f610d853215ef410d8532005bf7458532165bc745853215ef4615853200cfe76d8132156fa60d8132004ff75d8132024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d813203cfd72d8132014fe71d8132004fd71d8132014fc71d8132156fa30d8132156fa20d81320057f755813216d7c7558132005bf7458132165bc7458132005f7715813215df47158132156f860581320067f74594320067e74594320067d74594320067c745943203e7f735943203e7e735943203e7d735943203e7c735943203e7f435943203e7e435943203e7d435943203e7c43594321467f725943205e7e72594321467d725943205e7c72594320067f425943205e7e425943205e7c425943203e7f325943205e7e325943203e7d325943205e7c32594320067f71594320067e71594320067d71594320067c71594320067f41594320067e41594320067c415943203e7f315943203e7e315943203e7d315943203e7c315943205e7f21594320067e215943205e7c21594320067f70594320067e70594320067d70594320067c70594320067f40594320067e40594320067c405943203e7f305943203e7e305943203e7d305943203e7c305943205e7f20594320067e205943205e7c20594320067f10594320067e10594320067c1059432004ff7559032024fe7559032004fd7559032024fc755903205cff745903205ebf745903203cfe735903203cfc735903203ebe435903203ebc435903205cfe725903205cfc725903205ebe425903205ebc4259032004ff7159032014fe7159032014fc715903213ebf4159032004ff705903200cfe705903200cfc705903213ebf4059032184ff76508321be7e65508320067d655083205ddf764c832006d
  | 17 => 0x6be5059332006bd5059332006bc505933203ebf305933203ebe305933203ebd305933203ebc3059332006be2059332006bc2059332006bf1059332006be1059332006bc1059332164fd7690b3201ebe6490b32006bd6490b3201cff7650b3203cfc7650b3201ebe6450b32006bd6450b32005df7350b3203ddc7350b32004ff7558732024fe7558732004fd7558732024fc7558732004ff745873201cfe745873201cfc745873203eee325873203eed325873203ef7715873203ef7315873203ef43158732196f62158732004ff705873200cfe705873200cfc7058732004ff7558332024fe7558332004fd7558332024fc7558332004ff745833201cfe745833201cfc7458332004ff7158332014fe7158332014fc715833203efb7058332006fb505833218ef8505833203efb305833203ef8305833218efa205833218efa105833205cff75d9232024fe75d9232004fd75d923205cfc75d9232184fd74d923205edd73d923205eee72d9232014fe71d9232004fd71d9232014fc71d923200cfe70d9232004fd70d923200cfc70d923201cff765923205ebc6459232004ff7559232024fe7559232004fd7559232024fc755923205ebf7459232186be5459232006bd5459232186bf435923205cfc725923205ebe425923205ebc4259232004ff7159232014fe7159232014fc7159232004ff705923200cfe705923200cfc705923201cff7650e3205cfc7650e3201ebe6450e32006bd6450e32005ef7250e3205dec7250e3213cff7650a3205ddd76cca3203edd76cca3203f9e74cca3203f9d74cca3205fce62cca3205fce52cca3239fcd52cca3217dde71cca3203ddc71cca32014ff765863203ddc735863205ef4615863217fd63158632004ff7558632024fe7558632004fd7558632024fc7558632004ff745863201cfe745863201cfc745863205cfc725863217ede315863217ef6315863217edc315863205ef7215863205ef42158632004ff705863200cfe705863200cfc705863217ef7105863200cff76582320057f755823214d7c755823205ef86058232004ff75582320067f75582320047f7558232024fe7558232004fd7558232024fc75582320067c75582320247c7558232004ff745823201cfe745823201cfc745823205cfc7258232004ff7158232014fe7158232014fc7158232176fa305823205efb205823205ef82058232176fa105823201cfe76d9132166be64d9132004ff75d9132024fe75d9132004fd75d9132024fc75d9132166be54d9132006bd54d9132164fd73d9132166bf43d913203cfd72d9132166bf42d9132014fe71d9132004fd71d9132014fc71d9132006be41d9132166bc41d913200cfe70d9132004fd70d913200cfc70d9132006be40d9132166bc40d9132166bc6459132005f7715913215df4715
  | 18 => 0xf705864200cfe705864200cfc70586421cef7105864200cff76582420057f75582421d57c755824201dbc745824205ef860582421c7ba4058242004ff75582420067f75582420047f7558242024fe7558242004fd7558242024fc75582420067c75582420247c755824204ebe5458242006bd5458242004ff735824203cfc735824204ebf4358242006bd435824205cfc7258242004ff7158242014fe7158242014fc71582421c6be40582421c6fa40582421c6bc405824205efb205824205ef820582421c6fa1058242004ff75d8d42024fe75d8d42004fd75d8d42024fc75d8d42186de43d8d42186dd43d8d42186bc42d8d42014fe71d8d42004fd71d8d42014fc71d8d42006de31d8d42006dc31d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006df6398d42165ed7298d4219def7258d42005f77158d421b5f47158d4203ede6318d42006dd6318d423a6bf65909423a6bd6590942006bf639094205dbe729094205fae729094205ebf629094201faf62909421cebe61909421cebc61909421c6be60909421c6bc6090942014fe76d85421b6f661d8542004ff75d8542024fe75d8542004fd75d8542024fc75d854203cfe73d8542004fd73d854201cfd72d85421b6f641d85421b6f431d85421b6f621d854200cfe70d8542004fd70d854200cfc70d8542005df7358542005dc73585421b6f4615854200cfe76d81421aefa60d8142004ff75d8142024fe75d8142004fd75d8142024fc75d814203cfe73d8142004fd73d814201cfd72d8142014fe71d8142004fd71d8142014fc71d8142006fb50d81421aef850d81421aefa40d81421aefa20d81420057f75581421bd7c75581421aef86058142004ff7559332024fe7559332004fd7559332024fc755933203ebf7459332006bf545933219ebe5459332006bd545933219ebc545933203cfc735933203ebe435933203ebc435933219ebf4259332004ff7159332014fe7159332014fc715933219ebf4159332006be415933219ebc4159332004ff705933200cfe705933200cfc705933219ebf4059332006be405933219ebc4059332006bf7559332006be7559332006bd7559332006bc755933203ebf735933203ebe735933203ebd735933203ebc735933203ebf535933203ebe535933203ebd535933203ebc5359332006bf7259332006bd725933219ebc7259332006bf5259332006be5259332006bd5259332006bc525933203ebf325933203ebe325933203ebd325933203ebc3259332006bf7159332006be7159332006bd7159332006bc7159332006bf5159332006be5159332006bd5159332006bc515933203ebf315933203ebe315933203ebd315933203ebc3159332006be2159332006bc2159332006bf7059332006be7059332006bd7059332006bc7059332006bf5059332
  | 19 => 0x864300cfc7058643004ff7558243024fe7558243004fd7558243024fc7558243086be5458243006bd545824303cfe735824303cfc735824303ebf435824303ebd4358243004ff725824305cfc7258243004ff7158243014fe7158243014fc715824303efb70582431f6fa405824303efb305824303ef830582431f6fa1058243004ff75d8943024fe75d8943004fd75d8943024fc75d894303cfd74d8943006ef52d8943006ec52d894319eee42d894319ebc42d8943014fe71d8943004fd71d8943014fc71d8943006ee21d8943006ec21d894300cfe70d8943004fd70d894300cfc70d8943006ef6298943005f771589431e5f471589431ed7e75189430057d7518943006ed621894305cff7518943024fe751894305e7e75189430247e7518943004fd751894305e7d75189430047d751894305cfc751894303cfd7418943006ef521894305eec521894305eee421894313eed4218943014fe7118943004fd7118943014fc7118943006ee211894305eec211894300cfe7018943004fd701894300cfc7018943014fe76d85431e6f661d8543004ff75d8543024fe75d8543004fd75d8543024fc75d854303cfd74d854301cfd73d854305cfe72d8543004fd72d8543006f751d85431e6f451d85431e6f641d85431e6f631d85431e6f421d854300cfe70d8543004fd70d854300cfc70d85431e6f710d8543005ef7258543005ec72585431e6f4615854300cfe76d81431ed7e75d81430057d75d81431defa60d8143004ff75d8143024fe75d81430067e75d81430247e75d8143004fd75d81430067d75d81430047d75d8143024fc75d814303cfd74d814301cfd73d814305cfe72d8143004fd72d8143014fe71d8143004fd71d8143014fc71d8143006fb50d81431def850d81431defa40d81431defa30d81431def8605814305edf6398e4205edc6398e4205edc6358e42004ff7558e42024fe7558e42004fd7558e42024fc7558e42006de5358e42006dd5358e42166de4358e42166dd4358e4205cfc7258e4205ede3258e4205edc3258e42004ff7158e42014fe7158e42014fc7158e42004ff7058e4200cfe7058e4200cfc7058e4203cbf7650e423adbf7550e423adbd7550e4201dbf7350e4201f9f7350e4203ebe6350e420079e6350e4203e9e6350e420079d6350e4203ebc6350e42005bf7250e42007af7250e42007ac7250e4201ebe6250e4201fae6250e421cdbe7150e421cdbc7150e421c5be7050e421c5bc7050e42014ff765864201dbc745864205ef461586421cfb64158642004ff7558642024fe7558642004fd7558642024fc75586420c6be5458642006bd5458642004ff735864203cfc73586420c6bf4358642006bd435864205cfc72586421cebe41586421cef641586421cebc415864205ef7215864205ef42158642004f
  | 20 => 0x200e002800000400200000400100000008000006008000000000000100c80000000030058024010000001000000c0010028004000003000000000e00000000240080010028000010003004001800800000000000020070030004002007001000000400b00000000040040000024002000000000c01e0000008000008005000800001c0060000000002001004000401c0030008004002006000000000000b009000400401500000000000010008048012002002000000000b000001c0000020008000006000000800001200a003000400a003000804400600000000280060060018014000000000000800200a0010000006000000000400600000000080040000010000012001000000000200100180080080000018000012003000000400c00000280140000000000014000000000000c0020000070000008001000000c00200b0000018004000002000c00c004000000c00400700b0008000000000000800a00300080380080050000008000001013801400000200000140080020000004000000007000000c00000080040000010000000000002000000400000100080200000020030000000009002001c002002001001000000100280200020050010030002001000800001000000080080060030010000010001000800c00600b00100000000010008018006001000000800200100280440040010038030002003002801c002000000802c0080020000000008003000800400000900200000000010000000008002000000c000000000001400200300100000000010008000006007000000000a001002000c00200200080000040030008000014000001000000c0020000000000006006800000600c000000000a010000001c0020000008008004004001001401c00b000000000400005cff7598a43024fe7598a43004fd7598a4305cfc7598a43186be5498a43006bd5498a4303cfe7398a4305cfc7398a4303ebf4398a4303ebd4398a4305eee7298a4305eee5298a43006ed5298a4305eee4298a43186ed4298a4303eef3298a4305eec3298a43014fe7198a43004fd7198a43014fc7198a4300cfe7098a43004fd7098a4300cfc7098a43006ee2098a4305eec2098a43004ff7558a43024fe7558a43004fd7558a43024fc7558a4303cfc7358a4303eef7258a43006ee5258a43006ed5258a43166ee4258a4303eef3258a4303eec3258a43004ff7158a43014fe7158a43014fc7158a43004ff7058a4300cfe7058a4300cfc7058a43006ee2058a43006ec2058a43004ff7558643024fe7558643004fd7558643024fc75586430f6be5458643006bd545864303cfe735864303cfc735864303ebf435864303ebd4358643004ff725864305cfc725864303ef771586431fef6415864303ef7315864303ef43158643004ff705864300cfe705
  | 21 => 0x280300000010000018004002003003c006004000800c02e000000002000200100080000020050088004002018002001800400b0000004000001002000c0040040000010002000001001400600000200100100010008018006001003800400a0020020008002004003800801200200000000000010008008002000001000001800000200000000130038000002001000800400c00400000180040000000000000000003801c000002001000800000000880140420010000000006002000000000000100080000000000018018002005000000800000800000000000000000008002000004001c00400400080040000000008010002000000000400000e000000400000b0040014000001000000c00c002000800c0020060008014002000000800400e002000800000000200000000020010018004006000002800c01000000100880000040020000002001001000800000200000240020020020004000000000000800e00100480080080000000004000000000800000200700300000100010030018006005000800000e008000000400000000280200020040010000000004001000800000200d00140020070008008000000003003400400400000300000020020008014001002800c0060010000014000000004000800c000000002c000001003000000c008000801800400b003003c004001001003400c000000000001200e005800800e000000001800000200200080000010060000006003003800c000005001802000000f001000000200700280040000000040018002000002800000000200380000020000000000000005003001c000002001800002600a002800800200a00580000060020010008002000001801001400000080200040030000008000004007000c000000000002c0000000000050002000000000400000000180000000040000004012006001801000000100000000000000000000000000000800c0000010018000000003003800c0000000008020002003002800801a0160138014016002004001c00000200000080060010000018000003001000000400a001000000600300000000140020008000000000000000001200200000040080010050000000005001800400e000000000000a00a00680040000030008000000001000000000200a001800000a001000000c002008004800c00600a0018004006000002001c004001000001000000a00000040000000008000000002003800000000000080300020000008008004000000800000000100380440000200000008002001000000400c00100a80240060000018004000001003000c0000000028004000002000000c002001003800802600500000000060000028004000002002001c00400000200000000000050000000000001000c00e00a000000000000c00000
  | 22 => 0x13ccbf2988285239c73200000033ad83c0003da0000000881401346d4f60005b380000006d100034210e607209880000000000000000000b486441bd4c6042f4500001442d351bc11340005f3000000099c5720002a2406400007e0000a849c91952edc88403a18eb4fc1585c44a706552a0000261142c49c00002ba3d4dcec733a20eb46ae24700022a0000cde32800002ee22d68c25b80a61390000000d7a00000000000008ed42217956cc11d0002910e0a000503a128780000069a28400000062f000189000000003e400000000012a526416c20a0000000000000236028c0002b080016147b3426882c4260001f524fc00000056929300de6bf5f3b61c3caad9685194cf52b915a0a44484a18c36e000097008300025cd36800000034a16b8a325ca8000000afe1789490dcc123307800159cb511ea00000004ec14f03d00007cc5ee8d8c73800000005216c20003f8000000020000015900002c218b05c00001e9000000000000000020986ea000000000000000000008d400000000031f40000000000d4c00000000000006e80005fa0001216adb240869ce7c2424aa8200eb6b2834318197140c04b3afbd85e5266541e2000011700c1e4c00055c079b6292b60e3688803122ec1339a0a90000000000130c000b175e780002a6000000000000002c00000000000001d60000cba70a6741d60336bca0d1184c00000000022a8000b1e0001f785d800000031f83900003332515068d0c00001f4000a4f00032007f2cd7453000000000034a04a189800033d0000ade000000000000000062d2998000c69296aa1c26666932000017604eb0000000000000403800115ab4b0001c4d6bc47728b016cb4400032393980005020002660000aa1000154916c0d54cf0c8c7969aa3d406102260006b30000a06000256800079c00000016ad8823eb0000000000cd466e0000d8eb532bd82206645323b6878509e7a300000013f400068a09515c61f343d89e9a822d91fc31acddc7b10000f5d2c2d0524d00000004e400033dd610c6a3ca80440000004d6000000070317385d457cb161afa8f40003ca00000000008fb50e000076819712485c492037e2831c48b2e0004bdaa3800000040b2630ad04ac079314cae80000000006003000800800a00000300000040010020004002000000801000a000000800800200a0008000000001001000000200800480080040010038010004000003800000000600100040000010058014000007001801801a0000008000002011000002c0040010020040000006000801000000a00200000060050000004002001000001800200000100000020080000068002001001000000e019000000c00400600000100000040010008000000000000000a0050030000000004000005c000000000000000200000180000020
  | 23 => 0xa9400052a8be0000bc01b820205a00001ed9e6490a46900022415c400043a800000000000000000000000000000000a021428324e7200000000005da55f0c880001880004e6800000000015680000000005728fc4000beb57c000000068f00035948eca62000000002a0000001324000d450ad0464756000000055000000046d9784000a584ae28a4d1a0c34d200002ac91b0000894a0a00000000011766c20001d2ca788333e51f9c000a6864d8818ffe0eb000007898c9573f5ace8b0822c26b92100000005988000000cb200000000000001b3a4909b61360000000a4e00000000015f6ac60000000d20644133111000000005d25b01762b769f2bac00069a5df133076e9f30679a7535217e5770388000000000215d59ab335d118ec000ab45c800000000006362c6d786a6a0000000ca46925c20001424870134000168ec29395b2e8000576000000073e0914ba02114560d642e031d0ee7560001dd8000b9659692008060000001de98b80b1174a55905e4f900013e1a3e00066c150093200000005d92761930000000000000000062d1c48d10000000000000000000000000036a000112640c00000000004a82be00000001f649380013980004148000234000516b1e40001e300031d40004fd129000dac04741260b246c80003820000000a300002e7c6c095a2918001594b4e0001c246580000001ca870000051b24b80000006500000000a82000000000000027d800971e38745d03788fcd6a4c90cf91ccaac1c700000000000003340000a0f000000078e92513a844528c12f00000000000ea000128c000c5d06700000c200028e23b00000002158c6c4de2574420da546e00051a98157e28540000000000000000000000000000001e000a00013f00006169e83050000b980001ef8d60202d1c42300ecc3c00000007040cc000433b2280004d144495e8f7050900000008fa52507833e977e2b55de00000000b74908000000000000000062800000000011524e70002ae0000000000296400000000000003845965ccae5db2093900028944c475a436111d42849c23a857da7246c000127c00036100020644869280f4286d4f200000004dcc5455900005b800000014b1c843ae01d36194a8d580000000000b6ea540000001130d5315008c800006a669a9408c0417401b324df6d4b4070000d520d90848b546945202149d0c0001d663d00000003c900025b400000000000003640006b40000ec64f100006f400026a00000000000003068000000000000214400000000018f40000000001524ec40000001378190bf900000000008b7352000000000000021a0d4200000000000004cb542800005c0003c0a6d80000005ce00013da0bd0000000e40a092780a2197ecaa44a182cceed360002df07f885f4bd2b5c6ca51400000010c40000
  | 24 => 0x44d8cb800030762b16bd53e6ed00015a560e6cc60090ed198000257000012600025e07b00000003782905b0000004100018de77b0002afc0002970002dbda6e00018e045800027c0002264242864000349d4260290000fc09549b00000000b66d2258e0000000000000000000040957600000006262dd82896e6c901460aa4a9600061d0000f1c00068112cc814cdf5d001798a464d39900000000000000000b480001499300b0ec9852595fc2747e25991aa0b106f100031c1486000000272d7fe6cb2230000904903159a4f4fb269329085bd822cb30628000000000388800000086600000000000000000b1d9a4d6900004894700000000001ae68eb000196c0009540002bc433000000023d0000a9800008840009202792fc86ac00000000000000000000d00000cf031480009fe6b6000000000269b64ba0b4684ccc1dd1d94ce42e80000000000543000000000039049580008048d649f2ee40000000de218400077133787547aa0005a320e029e3c106900014fc0006600df0000562000172990800000000dc0000000000000c48cef63f97a846c25a000212cfb000000000019c2000000000001e317387000000059b000000000033048e80008b898d0000000000cc82f69980000267000000000000000015ac000b3e68700006925710000c940000002041c7cc5026d03680000000006ae0f6879a79600027d135600021eaeb8000000000310835e0000b5000143c2a6497a8289748921408910fb86f30f780010f443126280000000000000000f3c9844c0a7ec000c496b68000c744525b48000aa20001b68000000c0d62a0000000239095999400031a4a18000da4000000000000000024d80000009090d98001170ad61c58b798b6b0e393315496ea510038000c1c0230872034e4a00035107e4000d2c5e080018cc2e422eb558e4e0740002d6d7f00000229b81838b2c00000000009163021e1c000b5f00000000004be14c800000000000030d87d81fc13db2b189cd173b5ac0893aa773d2800000000000000001c008d656abc13e0a3a0001c0800000d1678000000bd553a8000288a601f6ae1400025b30e0000ff80001ca80000000006be86c00000003a8312c80e822526b21842866a13b0000bf80144a7800000046d211800173cbb50002378dc200021106d000000000000000000000001c911ca00057e00000000006b811e590617d5dd80001b80a900028f8f28a223d70001ace05436a800043ed5f030000140c0260000e684780000000e04a260003678000b1a81f1b5000010a2ae40d054434ccee000154c00031000014fc0006a362b8000cf2614000000102045b4a932e0a0e00054e800176825519ca6cc00000000021c87ce0273fe894c0000002fd80000009331959788f004431e12bcd6180000001efd6aa9fc1f20000
  | 25 => 0x5634bd204c94c4d5e2f468ab0e59243fb23715f44b85db56096f80001f560c8ab02545c90000000278a2300029c4000ca707d00000004d2239800000035e000279c7ccb2a1920ea40000000001c540000004053288bbc0002b39a5c374000000000024a0081ad9970000d4e22f344d38600041889ac406000138878868a1d90ed9a0847a39e187a1f0aeeac042608555545fa0770ddcab660c1a81b2833ac9605a09c9806d8b61ead40f4c20a000266cef8c470001c70000000269b42d072000000000030a00019c04b4050000000000000040027b852c00066700002d4000bab000203185a12c30880000000000000000f14cc40001df974c35c0000000000000000000000060117c9915478000000000127494900000000000000000e740003cf01f21c48320005e4b02134e0000858000db0090000222d1c0300150a7609c62b82da30396122890000bf82c6000000000000000000003918d067e4608e4d8dc0004c51c6c9940000000a2cbd0b3d274a6c400027861816c960875940e8000000000000000012c0002e400000000004538e84000b260001304000c34000000000054c0000e80000a6b000340d72800000000004121276c200019e876841280000000000001e44000000000000000092d23084c80000000000838ce21ac32b00000000982eb8000000d8f115047991e3d90f900000000003f79ad110c0000002820abc8f20001ab800000034600000008c8025000000000066292900607421f42e301da9852800ef541c00067d9f5089279d5aca7880005f20002970d6e6961790000000094145000000010302436380000004208dd88a80003fd00013a60002d1800087000062c00000000001829a2498e78c000244c0002e325c80000006ba60b00000000000000f0c6048172d8b1940000000000a385fe0000002de4000bf7130ae1cba0cff12f0d4402c4c848a05f00000000000000a9e6df00022f82d200000000001540005db36353e4a7869a0bd49a0bcc43a26f400089f5468e3c000d2b065800000000000021209d01e700028cd63062d19e93d805e2381830ef8db2701000000000048d26a903c00000017b800194c9c200023380005f712780010864a20001a1447e6b903e0f58766000094ab4160a50147185e98440003112318000ba50000b3043ac176ad839c2400000000001100c25222951c3e251f0000dec5a839825a8000a82baa1e81fb013c00000000000005a03c58e980a0b3533e2df40000004ec8efc00027f0002478000d2357b33d48d000000011440000000002b4c5fab6a300000000000020216799a2000000265596e5d6000000000084511a00018485b656a8e48d62b274bf9e9d48cc2a0279e6115e3205a2850d59842e25e823d0f287f08610cc23e00018909e443600000000000000492580000000000
  | 26 => 0x90002f580005c700000019aa0003ce11e03543a71fd187c00000000000018c235416200000000000001c3c65055500000000000001b599cc4ee5ee5b682040009c60000d200000000002e2ca3c0005510000858a5f38a000103c00054f000037000000000000003bc0000001258368000000000000018a891400034f00faba4be800000000000007c100000013aac8b0000001a326be63ba100d06b40445000000000050fb13c0005d3000000186485a0cd1864dee0000890cc55389e96b5a48caba00000000015329265bf00000000000002e35948000000146caf22bb0001b402680001bfa8553c0d1d0a0000044c2a30ad9eb01b00001e60231886a3b5ba80001e293500033681f09020ef80010367c83918000000ab32aa247012e72f00000000000002e18001500cae61380017ec00000018e40003f700027019e4d50506a6f0000000000000144c0001a60a7000074d2ab1bf4000cb600000fc0009af005314400097e628220c00000001a924421464e000000155c1c000030b8f40372363000045e94a5c0b5183962aa0001e883b40e62c8800137200060f94d8e6ed3c1a3b5f00000002c1000197ca5a0002370a6028d000206123ec2c0ee16b81a825856580000007545bb98b179643600000000000002700694bd28c900032d41faa2f0000000000190000273c4c000033600000000000000f1000000024195946a45dd000000040a00040a8f84338bad31388312d2cc345f80000d01dd00000000d6cf60002840000ca525faf945220442c7b25555ea4059bac4cd8a248670068d21a78329c0f818dac1263900000008dd42f000000034445a0000c4a8ab407800192600062c8000000615374a8b800016b5b900000000000000000000be152728b0000426225800072c8b00e20000000000000000000032758c8001a66000000000089e000553a83151e0001c691400000001821c5d54a00033e80012e00004fc0068000000000000000000000000017d413d16e8000754d3063181c15fe83b00000000002ce3450000c62c1b4b227b815638300022f4a24d1a4cfa9b90644e500000000003b221d00000002012878000000000000000130e0000000c64000c0a1c89ca50a499d2940a488fe0003e68000000a570000000000cfe0000000000d6341ba77163a00007fb52129ace50000000000000220800000000016000012cc01b2a3266956e37a0a498e01986de05924547ba09b5568000000ce30000f140008552dc800000000035a8000d10d7f0000d6864c0a84e0800000000003109c061acaf000000158a97900034412320000002ae570c00015e3578000311000000000000000010d0ce869140200f1a9e0004c720b8b7073f0272bf52e42160002b90b163af000000000000053e268c10c5782c822c8fac8650ea05d0fda88e5c990b
  | 27 => 0x38afcb6854500000006fa0fba18c42252b0000000000c26000137c20c3790000000000b8e5558bd800000008c0000000000000332c000000178000000000000010858127e51141d38c5c000000333400030a0c084c0c5e00033700000001781710001876b4434f0001894b220000b04e8e29b32500000086610000000000000000000000000000009d0000b5600000000000000002ee005a0001c223e0ad40004e3985c2c295e0ec000000044000000000000000002b2413a7fe0b40000fec66809c34c80007081daacc000079200030400000000e7b5d00ac90a2ea0000000000575251c0009596a902d88226ec0000000ee80000001ead43acbd54a800008c00000013d1ab04cf000177c86eb060002ac4c128580709c880008d900000005a65fe271000100c000000037c000bba1c634a40004ea4fea80ca663b65a6b44800030100005b59048f60000000000cdd1c100000009a247505340007da00000000000000002b1000086f000160044658a5900000c42786000000000000003c80016c0d4a12b28615341802f7af68e0e0000d403b0f9200014104201aeb9d0d8800033c9d10001fe4e6c06c55a88200000004cb31e07a6623032a1b4da607657c80013a4000000012d1ae85963a26180003590000ec400000004f9e14000000620000000000042390f97fa00000029fc8c8a933bf8368aa04b405f1b94d5aabd000000090e66249480000000004ae9be40009075e39220000000000000000097c0b29eb4f749df2768000000c313fbb590506b0d00000014626580001a98b7a2b900000000000003aa80000000004c800000000000000000324104000295947249e32d0cb40005e7487b1d800000048922559da0005d79ba10a000053b00017047ee22c800000018a522936043c00000000000000004fb80000207f20ca24dc57a2dc0e389a599c87d434a88027cc370f58f6067610709f9f8567654d4a11ac13949996471918cc84180002844e70a49638b508e8c00037b047131e1fb00000000000002071f3c000b360e680014ca0000000000372227115a3097129402ce00013002c30fa00000000005f4a5c4000000328b0d4cb2000000000000082a00034b8000abb3d923f4d541d02389cb59826ef3b000000babc2000000047400020b2c54000ca3009aa5d642968000000000000027a80000000000001e680001a42d293580000002b80000c30000320ad68000000000000000000069d2e480000003d0acf03401e060a9158c865e05b5988191288826e83d800075c000093400008b0000f8daaaad40000000000000000000051e9c526680012c60002970e5c7482d8021260da12a1a5702f1400000000000017525d51fb0000e7a00000003d47c40005cc1298000d910c480004a28915ea0a88000603405a75c000d54452b61863cd8
  | 28 => 0x3e4b28001ab2cbc00000017904fe6409bf8f5e80925082b5956cc63daabdc000c4520ab4bd28847c0000454db6000000036ce6a7414b516a94de0000001c411e2d6200023690ac2ee500294d3ba000472000000025900000d0000b6400007e80000b306514b0000b230ef1af0a5e9085a496e949400045200013d400039824c4000222000058178c00063d8eec0000003b3000118ab010000cd084e2ea12814395ce0005c180007460000000001a0e21248c00a92a6000000000092ea730072b2109c0b90000000b1c5634770000e74d610318304000b580002fb575017f61f800183a00014d35b80002c65bc000000000000000005a40000000000000a946a494880fc0001be90f0cc600000000002bc0e55bd00004fabec000201466e98934700008ce5fd0000a54000d7e5f42db8c687521c32ac00007f322c01d41342800000270f8ebfe0000b28000000000101400061b000000000040b65a27680004065792fc000086a0001655746b433fa80000005a90002dc40007e00920000000000000056400023b00000000000b80000001a3c00000000000003090000ea000010050c9660bb265f02f8000000000000000000000031baa980000000002ce10602242c080008c448b00034f400078944e04150c028656c1b8c00090e3c207e00004940002b3c00015d0000a6191a00000010354bc0003a9800042ed790000000d9c00046a801934c48600000000009db1100000000c9900000000aa00016400000002c5000000188c05c3b7935000015244b800000000068b00000009100c72dc000019f2ab800162200066100000000001b7181c00000015fa8d15ea0001c5074cf96000000299d7c098b000265cb583a200025800007640000000bc800000000000000003b482fcd40bb10001b88c205943f524d80000002cd0fc8f1a5da00000000dc0001aaa310000811018b3a48b400000007b9736885244b50161600000000012ec0003528000b9e00036b00001602b146a1665764b0f3ed80e400000060307f43cc6330dba3cc00000000029e892c8f73e90000342a8c4f18000bfe91a40088c400036f47480006ba0005ed9411548904658a9487fad2139400000420002ee1d5ce580e920e23f1a5a0003f406a54b600003390d4ec28ef34fb36468234e00000000000003bc800000000000000000000006baa7d8000000000000000088c69880019cca1600014e4f84d82474327897600053480000000002c31fd0a101c328ca8a8dd651d00028a04c6c0c00008a4ed4b9a00020f81783dc0000e14ebe6021b999ad50c7970002259376000551b40537cb4f0c12ac980e03d5f192280447bb00000000000000000000000b621b3281400000000031811a014e49e209d7a2c3c00027d57f800065d80000000000001ddc00047b20f2f6400015c00002
  | 29 => 0x2751f259d5f2124cee09fe000000000000052eaeb07109754bb9e6c6740005bb05cc9b4abc05719514e4b544e70ffca1ac9f25b08dd9d4371386aae88aa0005de8919af63363d80000cf60003cf80000002af0000000000000137000165e0002c29db930426c4ca00e119600000032c0d764010000000be07bd000000083e2402539868fae000000010000000000000002b0be6000339cc7c1ca0000b84000000000264c0000000000000000635000328526800000000000000000b90000000a240000000000abe0001a1cb6a29d15400000007185c40000bf058c255a52000061d0002ba118e2da16694d4e760003fc2ce58ce3f458913854e8c0f69334359e66491ef031841a9f13c807fc0f66486bb000069a1d106e80002aa0002a40001a86c0522980000007495e700015b80000000000000c6400033c400000000000000007b724c00014c81ed4d01b108600000c78000d388b940e31348d6000061022840e7e909720484082d1107b5100006a70e6237c02e0ef0b200005ae32f08825bc83acca1b6282c00000000023000006dd486087120c5a1447b55d84639b0df80000009bf052119800000000000000000004800001698d2500008680008210001e084ba9e15802ca57a663600000005ca0000002984e000002f321d95066c93259cc4000000000000000086b00031110ba00000000000000000002ded5c21ce000000113c6cd58a06599f2d476c60148ef01454ea285c0a205a1f4800091c4ef29d800120a8b30000001a54a4764280018c40000669f4d6209ff3e218219386da5f98620e16092039b56847ca883600cfcdf0a70000164800000000014448f49010002d74000264000000134a5b015a1f38b8cd4d00001dd90e6b3000228804010d00000000008b10000bacdfea902b68001a980000000000142000000059c00000038f1230c2c9ad0000000b9c3a520db648dae53a54b0294000b340001c180000000000bf1a0c0000000001508b4a2ad05e463e00000000008e430e465034068630300002814020000000000a2041200023340000000001ef8cda00000025058286120000c8468c8a30000000000000000000000000000016fcd1600000008cc00000000012487a200000017adaf00001860fbc0003fe000257d63e7e30740000508b5756d20f40004dc00000017ae00000005982a0719143a2b0b3e00015380007ea1ea00000000009b80000a50000c0000020801ee00056e972d15c7aa00000019ac0004eb0000a7c94b00000017ea000000298c000000000000000074a2a700008ca00005307191a4d240bda6b8760c914f315b98347c60001c580000003c792544942b60000000efabfb0120000000cb94da90800003ee0e923f910e6b22e2a0d80005f500000000000003b919fd6067fb6b920015504246c296a07cac
  | 30 => 0x4a00000000e6600037e000006c86e67e21080000000000d2c9f40000001120000b805ee000000000000029f5322d830d6a2340f40fe0000e500001fe000000028400056f00000008240d5b5e8e7813b00023fc00000000027e4d0800052400017b0000672000165643269d8b80ac025f57d1a6414e000663800000063f0000d88ba20000048000a6e000000000005633c0cc861822883f41e26c800042a0002e9d05893011700007722655ba000000020200000000d200000000005be0000000000898000000274000081457780011a687e2b980000003b82e9348054a44a45aac90fccba1005810d9280190000000cbc0000000000e180000000000000000000000094a0000000000000000000000107400023780700006704a880009f89ef00029b0bc646a2ba80014086320000000f7200000017d80009e400000000004d900000015221b64db80000002ef66d8b59b1045f00000012b00006760000d707e41483230000000000004800044e2e68000000cf834027211787d509a94d199e6570df00019525580a09ba80000642380000eea50c57300000006c1000308049600060200000000fb59718f164a7bc1c4809400000019100000000000001460000230000227552496b6198864dc8d0000001c51e0ce262fa670f80cfd1f99cb8666d0f0001624e8ad6c023993c6520a3000204c112b42615a38415ed5d5d20000872ab64118528a347c555480003e0000000000000062b29ead480000003b98000000000000000000000000000000001473e8a7b17bc5454f5800000014c00000000000000000000000000000000000000000006ed3cac211658b980005bc19a923cd560000001d203060000000001816000000360400000049c14a48c69a838d1d31244457189a124000000545800010ebfa3e18000f6c000000046c09a5f16bb80012981c538eaa04b845c13a7855c75c740614000012a1b517dab7c0667d04e2164c9646420000000000b3f64d0f20000b632b314552f0000461a0d40000000000000ebc00069c0000a885170000000000000379000053e000000000000000000012bc4308785ef99312fa00020d000042000060c000179a41347d19d80000005e22dfcfba102576af88ece3d200000016d800002c000119e0000000000b06a4215580000007515638be954042816d80010a60001209fc4d9000000035bc0000000000130d0200000015b0000308068aecc9dc75d00026e97a00003d2000021e0414b124a97dc9a133aa2690503c600005889884b1139a9b544e6984ef1955aa26780c6b1f1104000000000087e1e40d730095e807f0001700fbe00061c00000000000001db0000a3f00000000002b215820ac0b2ad1561169c00000068217b05e6b650931a548200002d30000b5aa9b00000000000000c39760630ac337a3
  | 31 => 0x1c942db5c4574
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8f686dc543440018e8cbb8a86880121fa1b755891027c3e436eab12200087e87d956244001878e9b2ac4880021fa1c65589100061e3a0cab122079c7b70195624400187ecbba2c4880030f19774589100062fb2ee6b122000c5c65dcd62440018beca39ac4880031719473589100243f43eeab1220008bf845d5624400717908baac48800237e0d755891003c6e41aeab1220008fb805d562440010fd0e3aac48800e2fa1f74589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fba8e6b122000c5c751cd624400193ee839ac488003271d07358910006563a6e4b122000ccc73dc962440019a8e7b8ac4880063ea1f70589100063c3aee0b122051c757119462440f18f2e0328c4880023be1d621891000556422c43122000acc8358862440171d904ba0c4880021fe1576909100243e42aed21220018f4865c642440051f10cb8484880121fa1776509100043ec2eeca12200087f855d942440090f90abb284880022fe1176509100046fc1aeca1220078dc835d942440011df04bb284880021fe1576cc9100243e42aed9922000c3e74d97324400187ecaba664880030f19574cc910006573a6c59922000cae7418b32440051f10cb8664880031e19570cc9100043fc2aed192200487c855da32440031e90cb8c648800a3e219708c9100243f42eec992200087d85dd932440010ff0abb264880121f215764c9100045fc22ec99220038bc845d932440011bf06bb264880023be09764c9100047bc0aec992200487c859d832440010ff0abb064880121f215760c9100045fc22ec19220038bc845d8324400f1b906bb0648802e3b209760c9100043e432ea192200087f87d9432440010fb0fb2864880063d219710c91003e6a31ae219220028f8865c0324400f9b0c6b80648813f1d1db65485100065a3b6e890a2000cb4761d121440019a8edb9a4288003351d87348510006ca3a0e690a2000e676518921440017c3011924288002b921932485102863c3b6ca9822000e586518d30440017330831a608800378887724c1100063c3b6ea9022050c7876d952044001970edba240880032e1d874481100069c3a8e890220028f8865cd20440035e10c90a408800b3c1d9214811005f70312429022001be0874852044005bc10e90a4088006f8a19214811000df0432429022017ee0864852044017dc6ec90a408800b789d92148110016f03b2429022008ee07648520440ef7c70a90a40881def86152148110007b1baa429022076f60754852044001ec6ca90a40881dbd81952148110007d1c22429022000fa0844852044001f46e890a4088003e81d12148110007e1c1a429022000fc0834852044001bc6e690a4088003785cd2148110
  | 1 => 0x8ca39a429000327d9073485200064e320e690a4026cd4611cd21480019a8e7b0a42900031e19770485202ce363b6ca90a4000e6461d952148073958edba242901af2b1d874485201c6563b6c890a4000ea461d9121480af958ec32242900038b194644852017e663b6e690a4026ccc761cd2148001b18e839a429000a3b21d63485200157240ac690a4059c7a76d9720480b3cd6c5b2e40900e32e9db64c812001e5d3b0c99024000e38651932048017bc642b8e409013e9ea0374d95102853cc06e9b2a2000c3d741d3654400147f08b9eca880028f21173d95100051f420e7b2a2000a3d841cf65440018bae639eca8813e9ea0073d95102853cc00e7b2a2000a3f845cb654400147908b96ca880031b5c872d95102853b408e5b2a204fa75811cb654409f4f500396ca881429e60072d95100043f43885b2a200087d8710b65440051f301baec8880021fa1f65591100043f438cab222000c5f65dcd64440018b8cbb9ac88800317d9473591100062e328e6b222000c9c641cd64440018decbb92c8880031b197725911000637b28e4b222000c6c651c96444001958c8392c8880121fa1f75591100046fc1aeab2220078dc835d564440011df04baac88802e3b20975591100043f438eab2220048bc8755164440f5938e6aa2c88801e37a1f73591100062fbaee6b222000c5c75dcd64440018beea39ac888003171d473591100064fba0e6b222000c6f75dc964440018d8ebb92c88800333dcf72591100066639ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c9644400195ca8392c8880032b550725911000657a18e4b2220008bf845cb634400717908b96c6880021fa1f6558d100061e3a6cab1a200087e871956344001878e832ac6880030fd977458d100061e32ee8b1a2000c6f65dc963440018d8cbb92c6880031bd947258d1000636328e4b1a200487e87dd5634400117f08baac68800e2f2117558d1000477c12eab1a200b8ec825d563440010fd0e3aac68800e2fa1f7458d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100064e3a6e6b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440019c8e5b8ac6880030f9d36518d100061f3a0ca31a2078c7970194634400187ecaba0c6880030f1957418d100046fc3ac631a2000a9c8458c634400159904b18c6880021fe157690d100243e42aed21a20028f8865c243440090fd0bbb286880021f6177650d100043fc2aeca1a200487c855d9434400117f08bb2868800237e0d7650d1000477c12eca1a200b8ec825d9434400f1790eb22868801ea720d6450d1000556412c8a1a2001
  | 2 => 0x661191200051ec2cc23224000acd820c763480015b30018ec6900030f9d36598d200061f3a0cb31a4000c3f655d26348001878caba4c6900030f9d76498d200061ebaec931a4000c3e75192634800187aea324c6901f72b5c86498d200043f43ecab1a4000c3c74d9563480018e8e3b2ac6900021fa1c6558d200061e3a0cab1a4000c7471195634800187ecbba2c6900030f1977458d200045f43ec8b1a4000c3f75d916348001878ebb22c6900032d1c76458d200045f438c8b1a4000c3f751916348001878ea322c6900032d1c46458d200063bb2ee2b1a4000c7465dc5634800196ec9b8ac6900032d1937158d200243f43eeab1a40008bf845d5634800717908baac6900023de057558d200147a40aeab1a400087e871d5634800717d0fba2c6900030fdd77458d200061e3aee8b1a4000c3f751d16348001878ea3a2c69000a3da1f7158d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200063bba8e2b1a4000c74751c5634800196ee838ac6900032d1d07158d200066bb98e2b1a4000ce7721c563480011bf0eb18c690002b52056318d200043fc2aed21a400487c855da43480090fd0bbb286900021f6177650d200043fc2aeca1a400487c855d9434800117f08bb286900023de057650d200147a40aeca1a40078be87d91434800f53d07b2286900063ba1b7250d200063632ee4a1a400096d851c943480018d8ca39286900032bd907250d201c65c386c8a124000c7865dc1424800187ce9b2e649015e2f21974cc9200061fb2ae99924000c3c655d3324807117f0fb2664900022f61f64cc9200063c32ae1992402887c865d43248001878c8ba864900021fe1f650c9200543ec3eca1924000c3e75d90324800187aebb2064900121fa1b75585200043f43ecab0a4000c3c74d9561480010fd0e32ac2900030f1d065585200061fb2ee8b0a4000c3c65dd1614800117d0fb22c2900030fdd764585200061e3aec8b0a40008be87191614800187eea322c2900030f1d464585203e657b90c8b0a4000c5f65dcd61480018b8cbb9ac29000327d9373585200064e326e6b0a4000c5f651cd61480018b8ca39ac29000327d9073585200064e320e6b0a4000cd4611cd61480090fd0bbb282900021f61776505200145f43ec8a0a400087f855db31480090f90abb662900022fe1176cc52001c5e422ed98a400487e85dd931480010fb0bbb2629000e2fa13764c5200045ec26ec98a407bcae761932148001c58ca32642900023be1d63c85200157240ac790a4000c3c74d952148001cc843b2a429015e2fa1b74485200061fb2ee890a4000c3c65dd121480d717d0fb2242900e22f21f64485200075210ec890a4000c5f65dcd21480018b8cbb9a429000327d9373485200064e326e690a4000c5f651cd21480018b
  | 3 => 0xa90e6007c5c7359521cc00187ccbba243980030f59774487300062f32ee690e6000c5d65dcd21cc001958e9312439801f331ce62487300147643ac490e6000cac7458921cc00f998e6b12439800ab920562487300245fc3aa9b2260008ef825d5644c0171d904baac8980023de0575591300147a40aeab2260008fb805d5644c00f1f301baec498002ba60021d893000477c3ac43126000ae481588624c00117f08b88c49800e2f21171189300043fc2aed212600487c855da424c0075390ca1c8498003279d9439093000672308e4b0a6000c9c7650d414c0051dd053b6429800e2fa1276485300045ec24ec90a60078dc831d9214c0031bd0db9a42980122fe1d54d932000c76412eca1e40008f7815d943c80051e902bb2879001e2fa1f6450f2003d4f41ec8a1e4086caf761d121c810b99eec39a4390003631d073487200047743ec690e4002ae48158d21c800147d0930eca900028f61261d95200061eba0e9b2a4000a3f845cf654800147908b9eca90003175cc73d95200043f43885b2a400a87d8710b654800147d0938eca900028f61271d95202b537410e3b2a4059a6d821c765480b34f50038eca900029e60071d95200043f43883b2a400087d8710765480010fd0e18eca900021f61c31d95200051f42063b2a4000a3d840c765480014dd0418eca900029b60831d95202cd3d40063b2a4000a79800c765480b34f50010eca900030f5d754d912000556c16a9b2240048bf875536448101c5b0432ec8900038b19652d91201c556432a5b224000a3e85987644800147b0b30ec8900030f5d475d91200054f418ebb224000a9d831d7644800155d043aec8900e2ab60875d91201c556c16e7b224000c9f739cf644800117d0fa9ec8900022f61f53d91200070fa9ca7b2240388be87d4b644800117b0fa96c8900038bd4a52d91200051f42ce3b224000a3d859c7644800155d0438ec8900e2ab60871d91201c55d400e3b224000ab9801c7644800117d0e28ec8900022f61c51d91200045f43863b2240008bd870c7644800147d0a18ec8900028f61431d91200055741063b224000aad820c764480715750018ec890002ae60031d91201c55d40043b224000c3c64dd564480010fd0fb2ac8900021fa1c655912042637b90cab22400487e87dd5644800117f08baac8900023be0975591200047dc02eab22400087e871d5644800187eebba2c8900030f1d77459120006363aee4b224000c7875dc1644810787cedb28c8900022f61e65191203f51f42cca32240008bf87594644810555f04b28c890002aee01651912040d1f430ca3224080c3e7619464480ffc5b04328c8901ff8b88065191203ff16100ca322407fe382019464480ffc7420328c8901faaba1a52191200071632ca43224057aac865486448001c58caa90c8900028fa1
  | 4 => 0x3484014bd0ba00c690802976174018d21005674148031a4200acd82900634844d5ad03200c690802b56064018d2103c6f4388031a42008dd87100634844d5ad02100c69081e3720d7690d2100657b24e521a4207ccc639ca43484051d90cb94869081f3318d7290d21014f240ae521a42008bf845d943484011bf06bb286908023be097650d210047bc0aeca1a420487e851d943484010fb0a3b2869081e2fa1f6450d2101c6f43ec6a1a4239cb471d91424844d9a8e231a84908033518f715092135c5e432e99924207c9c635d33248401b4842ba664908e62fe1f64cc9210045ec3ec99924200c9e74d8f324840193ae9b1e649081eb320e768c921456573b0c91924200e8f6418e3248401d18c831c64908bf351c7634c9210065a326e29924239cac76d913248473b48e3b2264909af2b1d8644c92135ed2388c89924207ccc76dcd324845fb88e3b9a64908bf331db634c92117ee238ec69924207ccc7618d3248401d18c831a649089b711c4634c921014f343ee299242029e481dc13248401878c8ba8649081f1718d750c92105eb210aea1924200c3e75d90324840187aebb206490803179d7630c9210062ebaec61924200e946418f21484653cf0e996429082f78c8170c85211cc5e436e8b0242008be87d91604840187eebb22c0908030f1d764581210045f438c8b024200c3f751916048401878ea322c090a272bdc864581210064fb26e6b024200c9c64dcd604840193ec839ac0908032719073581210046f43ec6b024200c5f75d8d60484018b8ebb1ac09080327dd363581210064e3a6c6b0242008de8718d60484018beea31ac090803171d463581210064fba0c6b024200c9c7418d604851199ee431ac090802a761031d8d400056cc0063b1a80008df8758c63500018daeba96c4a0002ab61352d894000574c0043b1280008ef8758862500014d90ab10c4a021eabe11621894005c76412ea3128004c3e75550625000155b09a90c4a00038b55352189400046fc1ae231280078dc835c462500179c842b88c4a001e2f21276cc94000c5e432e9992800087f855da32500090f90abb464a00062f219740c94005c7c432e019280018bc865d3315000f1bd073b242a00023760e764854001c5e420ec90a80018be86dd1215000187ee93a2cb9801e97a0e74597303152ec1ce8b2e6000a7b805d165cc0c94f100ba2cb980028fa1372597300051ec26e4b2e6000c6f729c965cc0010fd0e212cb980021f61c42597300051f420e2b2e6000a3d841c565cc0010fd0e20acb980021f61c41597303253d40042b2e6000a798008565cc0171d904ba4c59801e3ba1f4258b3003d6741e84b166007c9e7650e42cc0051790eb22839801f271d943507300045fc22ec90e60038bc845d921cc05f1bf06bb243980063720d76487300061e3a2c
  | 5 => 0x8022f61e65191210054f41cca3224200a9d83994644852755b05328c8908022fe1d65191210054fc1aca3224200a9c83594644840157700b28c890802ae20165191210054f41cc03224200a9d8398064484018baeba9ec690802a7a1353d8d210054ec26a7b1a42048df8754f63484010ff0ab86c6908121f21570d8d210054f42061b1a4200a9d840c3634840153d0932ec690802a761265d8d210054fc22cbb1a4200a9c8459763484015b700b2ec690802b620165d8d210052f428c9b1a4200a5d851936348401c3d0a326c6908038761464d8d210054f424c1b1a4200a9d8498363484018baea3aec690802a7a1075d8d210054ec20ebb1a4200a5e851d363484014bb0a3a6c69080387d5254d8d210054f426a5b1a4200a9d84d4b6348401c9ea5296c69080297a1442d8d210052ec2885b1a4200a9e849c3634840153b09386c69080297e1570d8d210052e42ae1b1a4200ace821c3634845f59b04386c6908beb5a0470d8d210056ac08e1b1a42008de8714363484011bb0e286c690802a7a1050d8d210054ec20a1b1a4200ace82143634840159b04286c6908beb5a0450d8d210056ac08a1b1a4200a5e85d0363484014bb0ba06c69080237a1c40d8d210046ec3881b1a422fad681083634840f938c6ba4c690803279d36398d210064eba6c731a42008be87d91634840117d0e322c690a4b2bdc86458d210045fc22eab1a42038bc845d563484011bf06baac6908023ee017558d2100c7c402eab1a42038be87dd1634840193ee9b9ac690803271d37358d21006563a6e4b1a4200cb474dc5634840f8b8c6ba8c6908030f9d76418d210061ebaec831a4200c3e75190634840187aea320c69080237e1d6318d210054fc22c631a4200a9c8458c63484018bced3a8c690803179d97518d210046ec3cca31a4200a9e84994634840153b09328c690a46b360a6518d210046fc3aca31a4200a9f84594634840153908b28c690802b6e016518d210056c402ca31a4290c9e76d906348401c3cebb20c690803875d76418d2147f46b96c831a42008dd87990634851d53d09320c69080237e1d6418d2146d67c12c831a4200a5e8519063484014bb0a320c690a32a7a186418d2145e4f3b0c831a4200e1e851906348401c3b0a320c690803879d46418d210070eba8c831a428ae8d721906348515d1c42320c690a2ba30846418d214574a108c831a428ae9710190634840153d09300c690802a76126018d210070faa4a831a4200acf82550634840159904aa0c690802a7a135218d210054ec26a431a4226ad681d4863484015ab03a90c69080393d4a5218d210052f4288431a4200a5d85108634840f1bd0e280c6908023761c5018d210054f420a031a4200a9d84140634840159d04280c690802b36085018d211356b408a031a4200ad5811406
  | 6 => 0x536c1480b286407a5e83101650c8014bb06202ca1901e97a0e10594320052ec1c20b28640ba6e82041650c8014db04082ca1902e3b20975590320047dc02eab2064018f8805d5640c8090fd0bb82c8190021f617705903205e67296ec9906400ccd52dd9320c80f1b906baac21901237e1d53d8d410043fc2ae1b1a820487c855c3635040153b08186c6a080237e1d6318d4100566412c631a8207a9e86d8d43504091df0ea96c4a0802b960420d894100477c3ac43128295aaf84588625040159906b10c4a08130f9d5541894100716aa2a4312820087f855c062504090f90ab80c4a080a2f21974cc94100656ba0c59928207c5c635d432504178d8c4ba864a080a2f219740c94103e4e31ae81928200c5d75d8c32504018daebb1064a082e3d219710c9410261f3aaa9b0282008ef825d564cc4171d904baac9988023ee01755933100c7c402eab26620487e85dc164cc4010fb0bb82c9988021fe157098b310243e42ae131662048bf87553644c4010ff0ab86c8988121f21570d913100656320e4b2262008ef825d5644c4171d904baac8988023de0575591310047dc02eab2262018f8805d5644c40195ee8392c89880333dcc725913100672396e2b2262048ef8754b624c4014db0a216c498802b960420d893100477c3ac43126200aac84588624c52959f06b10c49882e3b20974189310043fc2ae0312620487c855c0624c40117f08b80c49880e2f211701893105e72312e319262048bf8755364c84051d904baac9908023ee01755932100c7c402eab26420487e85dc164c84010fb0bb82c9908121fa177058f210043ec2ee0b1e42078be87d9143c840f53d07b22879080a3b60b75d91210061ebaea9b2242048bf8755364484010ff0ab86c8908121f21570d91210054f41ccbb224200a9d83997644840153f06b2ec890802a720d65d91210055dc02cbb224200ab880597644840153d07306c890802a760e60d912100557416ebb224239aad82dd7644840187aea3aec8908028fa1473d91210051ec28e7b224239aad821cf644840117d0fa9ec8908022f61f53d91210070fa9ca7b2242398be87d4b644840117b0fa96c8908038bd4a52d91210054f41ce1b224200a9d839c3644840147f0ab86c8908028f21570d912100557410e1b224239aad821c3644847356d02386c890802ad60470d91210045f438a1b2242008bd87143644840153d06286c890802a760c50d912100557410a1b224200aad82143644847356d02286c890802ad60450d91210045f43861b2242008bd870c3644847356d02106c8908032719373591210064e320e6b2242008bf845d564484011bf06baac89081e3720d75591210047dc02eab2242018f8805d5644840f1bd0fb9ac89080327dd373591210064fba0e6b224200ccc73dc964484019a8e7b8ac89
  | 7 => 0x40080700001c0100000c08c038000220000082b0000c4038050000240600100c0100100900400800849012010000010020700300400407c0280300001c018030020740200702203c0300f01203c0a0040000000581f00204c3e755526290c01c5aa8a94c5218021fe157098a430243e42ae131486078ec875496290c015cb02102c5218130f1d5545824300636baea5b128600aad84d4b6250c015d30010ec4a18023be1d62189430057240ac4312860bc6c825d46250c178de40ba8c4a18031b5d7521894300556c26a43128600c7575d476150c019c8c2392c2a18021f61e75d81430243fc3aebb028600c7b805d76050c018f100baec0a18031e5d750d814305c6e43aa6b1c8407a9f8658d439085917b0db9287210121fa1f75582420061fba6eab04840087e871d5609080187ee83aac1210130f1d554582420054ec2063b1a8400acd820c763508010ff0ab86c6a10121f21570d8d420046fc3ac631a8400ad48158c63508019a8c239ac2a10031e5d750d814203c5f43ea8b266400c3f75d5164cc80f53d07aa2c99901e2f21d54593320243f42ee0b26640087d85dc164cc80187eeb3aac99901ea7a0e75593320054ec1ceab266400aaf825d564cc80155904baac999002ade0572593320055a40ae4b2664008be87d4964cc80117b0fa92c9990038bd4a525933200557c12e2b266400a3e851c564cc80147b0a38ac9990022fa1c51593320045ec38a2b266400aba8008564cc8015730010ac9990028fa1770593320051ec2ee0b266400aae829c164cc80155b05382c999002ada0670593320055ac0ce0b266407a9e831c164cc86753b06382c9990022fa1c50593320045ec38a0b266407a9e8314164cc80153b06282c999002aba08505933200556c10a0b266400ab68114164cc80156b02282c99901ea7a0e20593320054ec1c40b266400ab68108164cc80156b02102c999002aba08105933200556c1020b266400c9d64dcd42cc8010ff0ab86c9190121f21570d923205c5e43aa8b24640487e87dd5608c8010fd0e3aac1190122fe1d54d91320043fc2ae1b22640487c855c3644c8011df04baac8990023de0575591320147a40aeab2264008fb805d5644c8031f100baac89900a3da1f71591320065bba0e2b226400cd7731c5644c8019cee438ac89901e2fe1d64909321cd5a40ac921264048f787547614c80187ee93a2ca1925e9be09745943205d36412e8b286400a7b805d1650c8014f100ba2ca1925a97e0d715943203d2e41ae2b286400a3e841c5650c80147b0838aca190021fa1c41594320043ec3882b286400a3e841c1650c80147b08382ca1901e97a0c70594321452ec18e0b28640ba6e821c1650c8514db04382ca190029da0470594320053ac08e0b28640087e87d01650c8010fb0fa02ca1902e9ba0a40594320
  | 8 => 0xfc00001c06830c1c819c36400020f2643552f70ba09405d23927828d2a828135100026f3de2b70a00004161000f62750000a703717919b34133a25136e14300042900016935d05e0b70a43b717229a10c1f62b10002320000f93c710f0003fc14a0cc35e2501a03aa0593d01ef41515c11338f4371a30792843710802e834819431542b19542631042110131c1420ad12a00326d2412df36326515023814612144a3623e92bb07d38e4250a20772890000000000090cd34631f2a13840000423bf34535400030f1122ef0003d41c30000d70071fe00001800044813f0003a40830a532d42d0001742e90003ea3980e04063850002a734a14421f35f1b40472a015d02230e0012a31ea1c11603e31f90e60be2c029727a17b22f39436c31914003f2f006433137f0412f40020440002f11242c711a33f3f30312d306301f17d2e60782071f238a30523b13801710436009c2883fb2f82132f32493390d83bb2a60980003162c13330bc2bd3c440939f00013b3dc0cf34220d11f06128e3113652851e31591192af04f37b13102323539b1b00213db3803241d13fa3ba2191ae3680562fc11c27f07b39a0d90fe2ec2732cb3922582453f81dd1540c82ea11e4323c54300463742790b40572560f405543a39d19a0c21160bd1932663ff3cc12d23e1d32863c21a22910002d10c52b43ec11d0933573873a908a19e13403900500034c4180002023961ba2221840ab0000662d94422ca0ef0d03303e41681c411510e03d0fd19928328a3911902fd20b19d2c21a10f000001636a43d0c742722b18a0ff2823b60d50000000e332f0ac0003da07503c30700025a4340003a70000000020280383400000800800000058010020180301080200003c000000520180d80d0060280903d000004058500020740400e00c0880c00605c000048050000140000300401c0100400a000060010040000000902c0280c00404400405000000070078410000000f0050000000482b01c0d80480a0000000000100801400007000010018070000080101c0160000000a0000041780b002070108030080081780601a0b00b000014004040040500040a0000020040580b0061581280d00a0100883900001c0e839004034010140020080001700202c0180a0000340080600c0000200100200c0280a000000068240240ac000100000180000104e00c06800040000008040300280100401802c0203b0020000200b00202409803010000388150000140f800010030148040020000e0020000c401000004114018010020700001900c0300380c00a054028020040000400700000401009000010008000000000000a0260300200202a004028080060000080a0040040000501000423806000010000030000100300100201003013054008000000000180000108e0440081a00001
  | 9 => 0xaa00002e35b0000e108535a40119f1111050882473001610b51482cf0000003c30000003810000000fa1e90da24d08f3a00000001e20001060003290000000000001641b516e3f62b90002d01810000c329313300423a03237309d00006b0973270001700000000142b30003cb00042f41f0ea00041c1d517f0000000b61bf3ad0381652620ee31d21a36f12f1493893991320002d60003781c900041418600000002f2f20c125e00036b1c50001e701e2442ac2de1f020827142c3bc0f33b822c15b15340b37e4351ec3ae4133f23f00cb0eb4281eb3d20000004051bd0001dc3672ce13a1ab3660000000001bb3322542e02181bc3773d62d40bf40f25d3f410b3b000004c00023c1a91a50000000001b62cc0130002c51521963c60a83c10f81393a329233428b07e34426e17c03b2262e31af28f1cc0000003d11a40b92d81b200000023627209f1f70af1cf0003231ac2ab11b1c612624640c43e38827642e1f506743933800014700004020122830b0000993613ce0e41b80363763bd3b533b0000000000003e02da00b22100000007a0000004400001c71453b11364033831850334203580a93df21e39c2aa15800000021200011800000800a0000002fa04a22a0341301201a801d08c05400014b3e80273fd42a07c2ed2603cd00624326c3b40e944538b4461352270df2e40c01e42c917e0d208e2ee1d40000003170000db4080960152962b00ce06015f1413ca2fe1be3f92204042ba01920c16208b22900017834e3200e52101032403a504e2171f31f121524f3360260741fd3cf3e700000031200000005100014e00000038d2b200000040e1e81802063af3d91de2242161e00003e512726b3ed4233021e60f13dd00c4430722ae1d611412219742418d1cd12b2bc16600000030932e2610bb34f09e0002be00014d32b3e228c1cb0b300004834d0c61f408d07634331e03041724b2ff00014f00015a02000000000000029f05c31422d32139302435229c18c0e200000029e0b200000009a0000702b83263f73ab27c06d01a2cd08718b3821fc07340016a3252a90ae0502771562fb32a1a62f526910a2ad1ff0d63182dc1092032302990892a521129d2040b040a1fb0491d23b937a2310a61772534383d343b27e31a3eb2e21730003472943d83f531b0000dd16b4101d90001f830100006c0001ca0000e800000041b3b30003951ad1290710d133720a0000002232c615e3690581253ef0000692e74472d523d33c4411513041d741a2bf1b904b4112dd29b3d50f706521c18339e2740ed2c40952eb0000002e12002d20d403e0003e635c00031300020530d05a2952c341900000000040d0ec2db00f25b0431da1e51a73c823f2d728717133e3c004d3080624490ca18232839711702a18812c24a16c1df4443c926a35900007f3a1
  | 10 => 0x3e133d00043629037536d41d13e40717624812e00010800038600024c00002521b3be00e25c2520b12140a11d014c0c90003491d820e2f91b137c2343ac0003500290000001fa0000003030000002422a21871c20c40101e100013c1ed0003a202c19237d1553222251980de1b71ee3353721c006e27b32c00009b00005b02d05302b0843f100000000003512300024e38c2700f21aa16f3060000002b61b30001ce00000025f0000000d300000000000000016340200018f37927d0000001890453560003fe21d01b3a80f500000000037000d26817a43f3900000283ee43c2090900b83a601200043300011005f0821072980001910002332550812803401374120002c830a0fb03a25706f13d1752f60e73b200000009222e41e00043134b2e52a40003d70911022b508642210d0dc06a2370a300000016d0000000002670000001db18e1573530111670000001280000000520000002632590
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x71008b2a06602920004020300040f66275190634840121d989d46418d2100568640215d33248515c8471190634c9210041b660651c94348001a1865610634c110007181db7548520440a1c6076d952148110007281db744852044001d20751d12148110006e02108348520440054e0965cd2148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x94e
  | 6 => 0x94d
  | 7 => 0x4
  | 8 => 0x98a
  | 9 => 0x98d
  | 10 => 0x98e
  | 11 => 0x3
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
  | 23 => 0xb09
  | 24 => 0xb0d
  | 25 => 0xb0e
  | 26 => 0x1549
  | 27 => 0x154d
  | 28 => 0x154e
  | 29 => 0xb49
  | 30 => 0xb4d
  | 31 => 0xb4e
  | 32 => 0x16c9
  | 33 => 0x16cd
  | 34 => 0x16ce
  | 35 => 0xb89
  | 36 => 0xb8e
  | 37 => 0x3c9
  | 38 => 0x3ca
  | 39 => 0x3cd
  | 40 => 0x3ce
  | 41 => 0x15ce
  | 42 => 0xcc9
  | 43 => 0xcca
  | 44 => 0xccd
  | 45 => 0xcce
  | 46 => 0x15c9
  | 47 => 0x15ca
  | 48 => 0x15cd
  | 49 => 0x1709
  | 50 => 0x170a
  | 51 => 0x170d
  | 52 => 0x170e
  | 53 => 0xd09
  | 54 => 0xd0a
  | 55 => 0xd0e
  | 56 => 0x1609
  | 57 => 0x160a
  | 58 => 0x160e
  | 59 => 0xe89
  | 60 => 0xe8a
  | 61 => 0xe8e
  | 62 => 0x1789
  | 63 => 0x178a
  | 64 => 0x178e
  | 65 => 0x98956
  | 66 => 0x9c956
  | 67 => 0xb0956
  | 68 => 0x94b16
  | 69 => 0x209
  | 70 => 0x8a
  | 71 => 0x1409
  | 72 => 0x128a
  | 73 => 0x1449
  | 74 => 0x12ca
  | 75 => 0x1849
  | 76 => 0x1489
  | 77 => 0x180a
  | 78 => 0x130a
  | 79 => 0x14c9
  | 80 => 0x134a
  | 81 => 0x2c9
  | 82 => 0x150996
  | 83 => 0xb0996
  | 84 => 0x98b16
  | 85 => 0x154996
  | 86 => 0x99556
  | 87 => 0x409
  | 88 => 0x1889
  | 89 => 0x1649
  | 90 => 0x449
  | 91 => 0x150b16
  | 92 => 0x151556
  | 93 => 0x9ce96
  | 94 => 0x1789d6
  | 95 => 0x9d796
  | 96 => 0x589
  | 97 => 0x18c9
  | 98 => 0x168e96
  | 99 => 0xcd
  | 100 => 0xec9
  | 101 => 0x138d
  | 102 => 0x124d
  | 103 => 0x8d
  | 104 => 0x128d
  | 105 => 0xa0e96
  | 106 => 0x12cd
  | 107 => 0x40a
  | 108 => 0x188a
  | 109 => 0x18ca
  | 110 => 0x20d
  | 111 => 0x140d
  | 112 => 0xb8e96
  | 113 => 0x144d
  | 114 => 0xcc3d6
  | 115 => 0x1715d6
  | 116 => 0x160d16
  | 117 => 0x160e96
  | 118 => 0xb09895e
  | 119 => 0x9894b1e
  | 120 => 0x14a
  | 121 => 0x15512
  | 122 => 0x104c
  | 123 => 0x40211
  | 124 => 0x41411
  | 125 => 0x40cd1
  | 126 => 0x40451
  | 127 => 0x44411
  | 128 => 0x45611
  | 129 => 0x41651
  | 130 => 0x41a11
  | 131 => 0x165611
  | 132 => 0x45891
  | 133 => 0x3c092
  | 134 => 0x40092
  | 135 => 0x41611
  | 136 => 0x3d292
  | 137 => 0x41292
  | 138 => 0x403d2
  | 139 => 0x415d2
  | 140 => 0x3d612
  | 141 => 0x3d892
  | 142 => 0x3c412
  | 143 => 0x1603d2
  | 144 => 0x1615d2
  | 145 => 0x3cd52
  | 146 => 0x41712
  | 147 => 0x40d52
  | 148 => 0x3d5d2
  | 149 => 0x41612
  | 150 => 0x3d456
  | 151 => 0x3d896
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1692
  | 6 => 3475
  | 5 => 1099
  | 4 => 12
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (69372+((h/564+packedAt gbK7 (62604+(h % 564)*12) 12) % 2457)*12) 12
  | 6 => packedAt gbK6 (181854+((h/1158+packedAt gbK6 (166800+(h % 1158)*13) 13) % 5550)*13) 13
  | 5 => packedAt gbK5 (68867+((h/366+packedAt gbK5 (64841+(h % 366)*11) 11) % 1319)*12) 12
  | 4 => packedAt gbK4 (856+((h/4+packedAt gbK4 (840+(h % 4)*4) 4) % 16)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfff83f01f03f03fffe0ffe00067a71fc48fe7c
  | 1 => 0xc01fc001fffffc0ffff03fff19a59e607f1f8f
  | 2 => 0x1ffffe003ffff03fffc000e1c61f878fe3f0
  | 3 => 0x1fffffffc000003ffffffffe07e007f003ff
  | 4 => 0x1fffffffffffffc0000000fff80007fffc00
  | 5 => 0xffe000000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x43d80b10720b115556456a0a020830ac486e3c
  | 1 => 0x84494000945554498a510ca608a096601b1685
  | 2 => 0x88ad56200269a612d69881461461b818da3d0
  | 3 => 0x1114a6b52a800104318e3158b6076006e0016a
  | 4 => 0x221738d9cf38e38e00042060dff8000776d800
  | 5 => 0x3c0000e00c00c20801080180fdf7cd50000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafce8ec00feeaeeeafce8ec00feeaeeeafce8ec00feeaeeeafce8ec00feeaeeeafce8ec00feeaeeeafce8ec00feeaeeeafce8ec00feeaeeeafce8ec00, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37097
namespace PEqualNP.Outside.L_meta_37097
open PEqualNP.Outside.L_meta_37097.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 12 := bgb_4_0
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
theorem bgb_5_1088 : Interval gbAtlas 5 1088 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1099 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)))) (concat (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))))))
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
theorem bgb_6_3456 : Interval gbAtlas 6 3456 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3475 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608))) (concat (concat bgb_6_640 (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832))))) (concat (concat (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024))) (concat (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)))) (concat (concat (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472))) (concat (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)) (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)))))) (concat (concat (concat (concat (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792)) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112)))) (concat (concat (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)) (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336))) (concat (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)) (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560))))) (concat (concat (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 bgb_6_2784))) (concat (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880)) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 bgb_6_3008)))) (concat (concat (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232))) (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456)))))))
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
theorem bgb_7_1664 : Interval gbAtlas 7 1664 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1692 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))) (concat (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800))))) (concat (concat (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)))) (concat (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 (concat bgb_7_1504 bgb_7_1536)) (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafce8ec00feeaeeeafce8ec00feeaeeeafce8ec00feeaeeeafce8ec00feeaeeeafce8ec00feeaeeeafce8ec00feeaeeeafce8ec00feeaeeeafce8ec00
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4243123200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37097.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[0,2]⟩,⟨.and,[0,5]⟩,⟨.and,[6,7]⟩,⟨.or,[3,9]⟩,⟨.and,[3,4]⟩,⟨.or,[0,11]⟩,⟨.and,[2,12]⟩,⟨.or,[1,8]⟩,⟨.or,[13,14]⟩,⟨.and,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243123200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243123200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37097

open PEqualNP.Outside.L_meta_37097 in
theorem PEqualNP.Outside.L_meta_37097 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243123200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243123200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
