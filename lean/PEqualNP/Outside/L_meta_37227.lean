import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37227.Model
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


end PEqualNP.Outside.L_meta_37227.Model

namespace PEqualNP.Outside.L_meta_37227
open PEqualNP.Outside.L_meta_37227.Model
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

def SBf (j : Nat) : Nat := [7, 6, 6, 7, 6, 6].getD j 0

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

end PEqualNP.Outside.L_meta_37227

namespace PEqualNP.Outside.L_meta_37227
open PEqualNP.Outside.L_meta_37227.Model
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
end PEqualNP.Outside.L_meta_37227
namespace PEqualNP.Outside.L_meta_37227
open PEqualNP.Outside.L_meta_37227.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x986021500100e010bf42bd42f731de31dc31f431d431be40bc40
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xc0a000802006e400ab28c6396540c72aa818e5d0831caa106394319025aa420650c440
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x100c020a158a540c61565d0831855943110305520c440
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
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
  | 4 => packedAt s1K4 (156+((h/3+packedAt s1K4 (144+(h % 3)*4) 4) % 11)*5) 5
  | 3 => packedAt s1K3 (224+((h/2+packedAt s1K3 (216+(h % 2)*4) 4) % 16)*4) 4
  | 2 => packedAt s1K2 (156+((h/1+packedAt s1K2 (152+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffe07fffffc0fffffffffe07fffe3ff1ff
  | 2 => 0x80fc0fff81ffc1ff0f83c1f03ff87f81d2ce7c
  | 3 => 0xff000ffffe0ffffff003fe003fff87ffe30f8f
  | 4 => 0xffffff001fffffc00003ffff801fc0ff0
  | 5 => 0xfffff000000001ffffffffffc0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8a10002304008000118442118a0088940450b5
  | 2 => 0x262996451ca512cb06a1d1a296c8550cd2c65c
  | 3 => 0x144aaa88286a31556042b48425550669630b0a
  | 4 => 0x58b34d125143a5a6bb68210939a66031bc0de0
  | 5 => 0x60c38e1c618c39f8cc7339ce01c44441fba000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37227
namespace PEqualNP.Outside.L_meta_37227
open PEqualNP.Outside.L_meta_37227.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x130000000055010000880000004800038c0b0000005040df43dc43df32dd32f741f441de31dc31df30dd30f710f510
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x26010a6a908754514ca9aa5984d15110
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (216+((h/4+packedAt s2K4 (192+(h % 4)*6) 6) % 33)*5) 5
  | 3 => packedAt s2K3 (111+((h/1+packedAt s2K3 (108+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfe0fffffffffff03fe07fc1ffffffffe631fff
  | 1 => 0xfff01f83e07e07fc3ff83fe1e07c0f81bceccc
  | 3 => 0xffffe003ffffffffc0003ffe007fffffc0f0ff
  | 4 => 0x3ff8007ffffffc000007ff001ff00f0
  | 5 => 0xfffffffc000007ffffffffffff800001ffff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x122142202104210046214402a3149494210555
  | 1 => 0x3464c52447286b2c1a691ca0c52d8d0cac6ccc
  | 3 => 0xa882894a8a51465581442ad4084b2a69c0b0aa
  | 4 => 0xb1cb1673141d779aed7582909273cc31f700f0
  | 5 => 0xc10c1842186184e3318633191c0200415ada00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaaa00aa00eeeeeeaaaa00aa00eeeeeeaaaa00aa00eeeeeeaaaa00aa00eeeeeeaaaa00aa00eeeeeeaaaa00aa00eeeeeeaaaa00aa00eeeeeeaaaa00aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37227
namespace PEqualNP.Outside.L_meta_37227
open PEqualNP.Outside.L_meta_37227.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x93090e9260942102c299a1000038050f4094520000b10ad500766c0310000aae000010000ddb19188d7ad005d32034f0f391ed46857e7193e5845a22704c71f069c33a0f226820e002810925200003e015040811802bda8287785050edca421db54843afa9a855c5350aeea2a15d14542bda8285785050abca6215754c42bba8a6574514ca7ca8194f55032af29e835d53d06dca5a0db54b41af29c835d53906f4a120de54241b7a92636c524c6f4a018de54031afa9a435c534867ca810cf55021af298435d53086f4a010de54021afa9a815c53502bca6205754c40b7290816d52102eca2205d544409faa2613c544c2eca2185d544309f2a6413d54c82bca7905754f20af29c415d53882eca3105d546209faa2213c54442bea6885714d10b7a92216c52442bca6085754c10
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (718+((h/13+packedAt s3K5 (640+(h % 13)*6) 6) % 53)*7) 7
  | 4 => packedAt s3K4 (1875+((h/21+packedAt s3K4 (1728+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7ffffe03ff8307fe0ff87ffff83fe018cfe7c
  | 1 => 0xf81f83ffc1ffff83ff07f8780ffc1ffef3338f
  | 2 => 0xffe003fffffffffc0007ff800fffffff03c3ff
  | 4 => 0x3fffe003ffffff800000fffe003fc03f0
  | 5 => 0xfffffc0000003ffffffffffff0000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x30c320238411500c642980a8e3a1321884563c
  | 1 => 0x524424448ca11281a522883124a514a8b13285
  | 2 => 0xa1094a891144253410855502494a495302c15a
  | 4 => 0xc59673122875b9dad6b044248e739063dc03e0
  | 5 => 0x618421c31862e6318c66647004201836ba800
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeae0e0c0c0eeeeeaeae0e0c0c0eeeeeaeae0e0c0c0eeeeeaeae0e0c0c0eeeeeaeae0e0c0c0eeeeeaeae0e0c0c0eeeeeaeae0e0c0c0eeeeeaeae0e0c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37227
namespace PEqualNP.Outside.L_meta_37227
open PEqualNP.Outside.L_meta_37227.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x8ee21ec21
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (34+((h/1+packedAt s4K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffe07ffff083fc3fc3fffe1fffe0113f3fc
  | 1 => 0xf07c3ff83e1fffc3fc3fc381fe1c0ffeeccccf
  | 2 => 0xff803fffc01ffffc003ffc01ffe00fff0f0f0f
  | 3 => 0x3fffffe00fffffc00001fffff003f00ff0
  | 5 => 0xffffc00000000ffffffffffe00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x6108023084001004404c048c6024621801515c
  | 1 => 0xa5104451902a0141c4144114a208a4a864c4c5
  | 2 => 0x422aa8a20d548a9c222aa829554149530b0b0a
  | 3 => 0x8a5331052906aceaaa82204199938063b00ea0
  | 5 => 0xc6221c63198cf333333327011020183dea000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37227
namespace PEqualNP.Outside.L_meta_37227
open PEqualNP.Outside.L_meta_37227.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x600008402a02be42bc42bf41bd41f721f421
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2258a4a0e910821
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (104+((h/2+packedAt s5K4 (96+(h % 2)*4) 4) % 10)*4) 4
  | 3 => packedAt s5K3 (56+((h/1+packedAt s5K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1ffc0fffffe0c1f0fffe0ff0ffffe003e73fc
  | 1 => 0xfe0fff03f07fffe00f83ff0ff1f01ffe338ccf
  | 2 => 0xfffffffc007ffffff003fffffe001fffc3ff0f
  | 3 => 0xfffffff800ffffffc000fffffe003fc0ff0
  | 4 => 0xfff0000000000ffffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4c244628a410940502a4e8930294d21816315c
  | 1 => 0x14ac8a190ca58ca085e1398591a154aa3284c5
  | 2 => 0x284114406148014b1002422a24028950c15b0a
  | 3 => 0xb14a2092480d2a72a948100cc94b0063680ea0
  | 4 => 0xc18c38e38e71cf9cce739cc0818c1183bfe000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfae0eac0fae0eac0fae0eac0fae0eac0fae0eac0fae0eac0fae0eac0fae0eac0fae0eac0fae0eac0fae0eac0fae0eac0fae0eac0fae0eac0fae0eac0fae0eac0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37227
namespace PEqualNP.Outside.L_meta_37227
open PEqualNP.Outside.L_meta_37227.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001007fd5001fe54007f55001fc54007fd4c05fe53007f54c05fc53007fd0c05fe43007f50c05fc43007fd4801fe52007f54801fc52007fd0801fe42007f50801fc42017fcc801fe32007f4c805fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41017fcc401fe31007f4c405fc31007fc8401fe21007f48401fc21007fd4003fe50007f54003fc50007fd0003fe40007f50003fc40017fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24001fb8812000ff84090007ec2048003fc1024001ff8412000ff42090007fc1048007ffb2e2003bfd971001ffccb8801efe65c4007feb2e2000bf5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc98801afe64c4007feb262000bf5931001ff8c98800efc64c4001ffaa62000ff95310007faa988003fc54c4007ffb1e2003bfd8f1001ffcc78800afe63c4007feb1e2000bf58f1001ff8c78800efc63c4001ffa9e2008ff94f10007faa788023fc53c4001ffa1e2008ff90f10007fa8788023fc43c4007ffb162003bfd8b1001ffcc588016fe62c4007feb162000bf58b1001ff8c58800efc62c4001ffa962000ff94b10007faa588003fc52c4001ffa162000ff90b10007fa8588003fc42c4011ff9962000ff8cb10007fa6588023fc32c40037f30e2003ffd471001ffca38800ff651c4007fea8e2000fd5471001ff8a38800fff41c4007ff20e2003fd9071001ffa8388003f541c4007fe20e2003ffcc71001ffc638800ff631c4007fe98e2000fd4c71001ff8638800fff21c4001fb90e2003ff8871001ffa438800ffc21c4007fa10e2001bf5831000ffea188007fe50c4003fea862001ff1431000ffe8188007fe40c4003fea062001ff1031000ffe6188007fe30c4003fe9862001ff0c31000ffe4188007fe20c4003fe9062001ff0831000ffc2188007f610c4003fd0862001ff0431000fe82188003ff65440017fb2a2000dfd9510004feca88003fe654400f7f32a2000ff59510005faca88003fc654400f7e32a2000df19510004f8ca88003ff64440017fb222000ff99110035fcc888003fd64440017eb222000ff19110035f8c888003ff5444001ff2a22000ff55110007f8a888003ff63440017fb1a2004ff98d10015fcc688003fd63440017eb1a2004ff18d10015f8c688003ff5344009ff29a2000ff54d10027f8a688003ff4344009ff21a2000ff50d10027f88688003ff62440017fb122000ff9891002dfcc488003fd62440017eb122000ff1891002df8c488003ff5244001ff2922000ff54910007f8a488003ff4244001ff2122000ff50910007f88488013ff3244001ff1922000ff4c910027f86488006ff6144001ffa8a2003ff94510007eca288003fd5144001faa8a2003ff14510007fe828800ffe4144001fb20a2000ff50510007ea828800ffc4144009ff98a2003ff8c510007ec6288003fd3144001fa98a2003ff0c510007fe4288003f72144007ff10a2000ff4851001ff84288003f421440037fb022001ffd411000ffca088007fd5044003fe2822001ffd011000ffc8088007fd4044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044007fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3ff414c001ff20a6000ff50530007f8829800bff314c005ff18a6002ff4c530017f86298003ff214c001ff10a6000ff48530007f84298006ff604c003ffa826001ff9413000ffaa098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9826002fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007fe204c003fe1026001ff8413000ff82098017ff65c800b7fb2e4005ff9972003dfccb900177e65c80013f32e4005ff59720005facb900177d65c80013eb2e4005ff1972002df8cb90017ff64c800b7fb264005ff99320035fcc990017fd64c80017eb264005ff1932002df8c990003ff54c8001ff2a64000ff55320007f8a990017ff63c800b7fb1e4005ff98f20015fcc790017fd63c80017eb1e4005ff18f2002df8c790003ff53c8015ff29e4000ff54f20057f8a790003ff43c8015ff21e4000ff50f20057f88790006fe62c800bffa964005ff94b2002fdca590017fd52c8001f6a964005ff14b2002ffe8590017fe42c800bfea164005ff10b2002ffe6590017fe32c800bf71964005ff4cb20007da6590017fc32c800bffb0e4005ff9872001dfcc390017fd61c80017eb0e4005ff18720007fea390003fe51c8001fea8e4000ff14720007fe8390003fe41c8001fea0e4000ff10720057fe6390003fe31c8001fe98e400aff0c72002ffe4390017fe21c800bfe90e4005ff0872000dfac190007ff50c8003ff2864001ff5432000ff8a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1864001ff4c32000ff86190007fe20c8003f71064001fe8832000ff84190007ec20c8003ff0864001ff04320007feca90002ff6548001ff32a4007bf99520007faca90002fd6548001fe32a4007bf19520007fec890002ff6448001ff3224006bf99120007fac890002fd6448001fe3224006bf19120007fea890003fe5448001feaa24000ff15120007fec690002ff6348013ff31a4002bf98d20007fac690002fd6348013fe31a4002bf18d20007fea690027fe5348001fea9a4009ff14d20007fe8690027fe4348001fea1a4009ff10d2000dfec490003ff524800bff2924000fb94920007faa490003ed524800bfe2924000ffd092002ffc8490003fd424800bfe2124009ffcc92002ffc6490003ee3248001fe9924000fb4c92002ff86490003ff61480017fb0a4000ff98520007fac290003fc61480077e30a4000ffd4520007fca290003fd5148001fe28a4000ffd0520007fc8290003fd4148001fe20a4009ffcc520007fc6290003fd3148013fe18a4005ffc8520007fc4290003fd214800bfe10a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe4090017fb2048003ff1
  | 2 => 0x40037fe87a001bbf43d000dff21e8006ff50f400077a87a001bfc43d000dffb168006ff98b4002dfcc5a001bfd62d00017eb168006ff18b40007fea5a0003fe52d0001fea968000ff14b40037fe85a001bfe42d0001df2168006ff50b40037f885a001bbc42d0019ff9968000ff8cb40007fa65a0033fc32d000dffb0e8006ff9874001dfcc3a001bfd61d00017eb0e8006ff18740007fea3a0003fe51d0001fea8e8000ff14740037fe83a001bbf41d000dff20e8006ff507400077a83a001bfc41d0019ff98e8000ff8c740007fa63a0033fc31d0001ff90e8000ff88740007fa43a0003fc21d00037eb068001ffd434000ffca1a0007fd50d0003fe2868001ff9034000f7c81a0007fa40d0003fe2068001ef1034000ffe61a0007fe30d0003fe1868001ff8834000ff841a0007fe10d0003fe0868000ffd9540005fecaa0003fe655000f7f32a8000ff59540005facaa0003fc655000f7e32a8001bfd9140007fea8a001bfe5450001df2a28000ff551400077aa8a001bfc5450001ffb1a8000bfd8d4005ffcc6a000afe6350001feb1a800bff18d40015f8c6a0003ff5350017ff29a8000ff54d4005ff8a6a001bff4350001dfa1a800bff90d40007fa86a0003bd435000dfe21a8000ffd8940005fec4a0003fe6250001feb128000ff1894002df8c4a0003ff5250001ff2928000ff54940007f8a4a001bff4250001ff2128000ef90940007fa84a001bfc4250001de212800bffcc940007fc64a0003fd3250017fe1928000ffd8540005fec2a0003fe6150001feb0a8000ff1854001df8c2a0003ff5150001ff28a8000ff54540007f8a2a001bff4150001dfa0a8000ff90540007fa82a0003bd415000dfe20a800bffcc540007fc62a0003fd3150017fe18a8000ffc8540007fc42a0003fd2150001fe10a8001bfd814000ffea0a0007fe5050003fea828001ff1414000ffe80a001bfb4050003ff2028001ef9014000ff880a0007bc4050003fc2028001ffcc14000ffc60a0007fc3050003ff1028001ff0814000ffc20a0007fc1050001ffb2a6000bfd9530007fcca9801efe654c001feb2a6000bf59530007f8ca9801efc654c001ffb226000bfd9130007fcc89801afe644c001feb226000bf59130007f8c89801afc644c001ffaa26000ff95130007faa898003fc544c0037fb1a6002ffd4d30017fca69800bde534c005fea9a6000f754d30017f8a69800bff434c005ff21a6002ff50d30017f88698003ff624c0017fb126000ff98930007fac498003fc624c00b7e3126000ffd4930007fca498003fd524c001fe2926000ffd0930007fc8498003fd424c001fe2126002ffcc930017fc649800bfd324c005fe1926000ffd8530005fec298003fe614c001feb0a6000ff1853001df8c298003ff514c001ff28a6000ff54530007f8a29800
  | 3 => 0x79084203ff8842101fec421080ffd2108407f69084205fd4842101ffec01080ffe60084037f3004203fe9802100df4c01080ffd60084017eb004203fe58021005f2c01080ffc60084037e300420fff9402107ff8a01083ffe400841ffe2004210ffcc02107ffc601083ffc300840bff1004205ff0802101ffc201080ffc10084037f32ea007ffd935003ffcc9a801afe64d400ffeb26a000bf5935003ff8c9a801fff54d400fff2a6a007ff5535003ff8a9a801fff63d400fff31ea002bf98f5003ffac7a8002fd63d400ffe31ea002bf18f5003ffea7a801f7f53d400fff29ea007ff54f50006faa7a801ffc53d4001ffa1ea00eff90f50007fa87a803bfc43d400fffb16a007ff98b5002dfcc5a801ffd62d40017eb16a007ff18b5003ffea5a801ffe52d400ffea96a007ff14b50007fe85a8003fe42d4001fea16a000ff10b50077fe65a8003fe32d4001fe996a00eff0cb5003ffec3a801ffe61d40077f30ea007ff58750005fac3a801ffc61d400fffa8ea007ff9475003ffaa3a801ffc51d4001ffa0ea000ff90750007fa83a8003fc41d401dff98ea000ff8c750007fa63a803bfc31d4001ff90ea000ff88750007fa43a8003fc21d40037eb06a001ff9435000efca1a8007fa50d4003fe286a001df1435000ffc81a8007fc40d4003ff986a001ff8c35000ff861a8007fe20d4003fe106a001ff8435000ff821a8006ff6554001ffb22a000bfd9150007fcc8a8003fd6454001fe322a006bf1915003ffea8a8003fe5454001feaa2a007ff15150007fec6a8002ff635401bff31aa002bf98d50007fac6a8037fc63540057e31aa007ffd4d50006fea6a8037fe5354001fea9aa000df54d5003ff8a6a8003ff435401bff21aa000ff50d5006ff886a8003ff62540017fb12a000ff98950007fac4a8003fc625400b7e312a007ffd4950007fca4a8003fd525400ffe292a000ffd0950007fc84a8003fd4254001fe212a00dffcc950007fc64a8003fd325401bfe192a000ffd8550005fec2a8003fe6154001feb0aa000ff1855001df8c2a801fff5154001ff28aa000ff5455003ff8a2a8003ff4154001ff20aa000ff50550007f882a8037ff3154001ff18aa000ff4c55006ff862a8003ff2154001ff10aa000ff48550007f842a8006ff6054003ffa82a007fed415000ffca0a80077e5054003fe282a001df1415000ff0a0a8007fe4054003fe202a001ffcc15000ffc60a8007fc3054003ff102a001ff0815000ffc20a8007fc105400dffb2e8006bfd9740037fccba001efe65d000dfeb2e8000bf59740037f8cba001afc65d00037f3268006ffd5340037fca9a001bbe54d000dfeaa68000ef55340037f8a9a001bff63d000dff31e8002bf98f40037fac7a0002fd63d000dfe31e8002bf18f40007fea7a0033fe53d0001fea9e800cff14f
  | 4 => 0x853fe5388401fea9c4214ff14e21007fe8710853fe4388401fea1c4214ff10e21005fac510803ff528840bff2944200ff54a2102ff8a510803ff4288401f7a144205ff90a21007fa8510817fc4288401f62144214ffcca2102ffc6510803fd328840bfe1944203bf9862101ffea31080ffe5188407fea8c4203ff1462101ffe831080ffe4188407fea0c4203ff1062101ffe631080ffe3188407fe98c4203ff0c62101ffe431080fef218840bfb90c4203ffd822101ffcc110806fe6088407feb044200bf5822101ff8c110806fc6088427ff2844213ff1422109ffc811084ffc4088429ff9844213ff8c22109ff8611084ffe208840bfe1044203ff8422101ff82110803ff65484017fb2a4200ff9952103dfcca90803fd65484017eb2a4200ff1952103df8ca90803ff64484017fb224200efd91210057ec890803fe644840d7f3224200ff59121005fac890803fc644840d7e3224200ef1912100578c890803ff5448401ff2a24200ff55121007f8a890803ff63484017fb1a4212ff98d21015fcc690803fd63484017eb1a4212ff18d21015f8c690803ff5348425ff29a4200ff54d21097f8a690803ff4348425ff21a4200ff50d21097f88690803ff524840bff2924200ff5492102ff8a490803ff424840bff2124200ff5092102ff8849084bff324840bff1924200ff4c92102ff86490803ff5148407ff28a4200ff5452101ff8a290803ff4148407ff20a4200ff5052101ff8829084bff3148407ff18a4200ff4c52101ff86290817ff214840bfb90a4203ff8852101fdc4290803ff60484017fb024211ff9812100dfcc090803fd6048423fe3024201bf1812108ffca090847fc5048423ff2024211ff10121097fe6090847fe3048423fe1824211ff8812102ff84090847fe1048407fe0824203ffd942101dfeca1080ffe650840f7f3284203df99421004fcca1080ffd65084017eb284203df59421004faca1080ffc65084077e3284203ffd902101dfec81080ffe640840d7f3204203ef990210057cc81080ffd64084017eb204203ef590210057ac81080ffc64084077e3204200ffd5021007fca810803fd5408401fe2a04203ffd8c2101dfec61080ffe63084057f3184203f798c21015bcc61080ffd63084017eb184203f758c21005bac61080ffc63084077e3184200ffd4c21087fca610803fd5308421fe2984200ffd0c21087fc8610803fd4308421fe2184205bf9882102ffea410817fe520840bfea904205ff1482102ffe8410803ef420840bff2104205ff5082102ff88410817ec420840bff9904205ff8c82102ffa6410817fc32084077f3084203ffd4421007eea21080ffe5108407fea884203ff1442101fe8a21080fff4108407ff2084203ff5042101ff8821080fff3108407ff1884203ff4c42101ff8621080fff2108407f
  | 5 => 0x463101ffaa31880ffc518c407ffa0c6203ff9063101ffa831880ffc418c407ff98c6203f7cc631017ee631880ffc318c407fa18c6203ffd823101ffcc118806fe608c407feb046200bf5823101ff8c118806fc608c431ff2846218ff142310c7fc8118863fc408c405ff9846202ff8c231017f86118863fe208c431fe1046203ff8423101ff82118803ff654c4017fb2a6200ff9953103dfcca98803fd654c4017eb2a6200ff1953103df8ca98803ff644c4017fb226200ff99131035fcc898803fd644c4017eb226200ff19131035f8c898803ff544c401ff2a26200ff55131007f8a89880eff634c405ffa9a6202ff94d31017faa69880bfc534c405ffa1a6202ff90d31017fa869880bfc434c401ffb126200bfd8931007fcc498803fd624c401fe3126205bf18931007fea498803fe524c401fea926200ff14931007fe8498803fe424c401fea126200ff10931017fe649880bdf324c405ff1926202ff4c931007ba649880bfc324c4057fb0a6200ffd453101ffca298803fd514c407fe28a6200ffd053101ffc8298803fd414c407fe20a6202ffcc531017ee629880ffe314c407ef18a6203ff0c53101fb8629880bf4314c401ffb026200bfd81310bffcc098806fe604c401feb026217ff1813100df8c09885ffe504c42ffe2826217ff901310bff8809880bff304c405ff1826202ff0c1310bffc409885ffc204c42fff0826203ff0413102ffecb90816ff65c840bff32e4207bf9972102ffacb90802fd65c840bfe32e4205bf1972102ffec990816ff64c840bff3264206bf9932102ffac990802fd64c840bfe3264205bf19321007fea990803fe54c8401feaa64200ff1532102ffec790816ff63c840bff31e4202bf98f2102ffac790802fd63c840bfe31e4205bf18f21007fea79085bfe53c8401fea9e4216ff14f21007fe879085bfe43c8401fea1e4216ff10f2102ffea590817fe52c840bfea964205ff14b2102ffe8590817fe42c840bfea164205ff10b2102ffe6590817fe32c840bfe9964205ff0cb21007fea390803f751c8407ff28e4200ff5472101ff8a390803f451c8401ffa0e4203ff90721007fa839080ffc41c842dff98e4203ff8c721007fa639080ffc31c840bffb064205ff9832100dfcc190817fd60c84017eb064205ff1832100df8c190857fe50c842bfe2864215ff903210aff8819085bff30c842bff1864215ff0c32102ffc4190817fc20c842bff0864203ff0432101ffecb1080eff6588407ff32c4207bf9962101ffacb10802fd6588407fe32c4203bf1962101ffec91080eff6488407ff3244206bf9922101ffac910802fd6488407fe3244203bf19221007fea910803fe5488401feaa44200ff1522101ffec71080eff6388407ff31c4202bf98e2101ffac710802fd6388407fe31c4203bf18e21007fea710
  | 6 => 0xbff2048206ff102410f7fe6120877fe309043bfe184821dff882410eff8412080ffe1090407fe0848200ffd9541005fecaa0803fe655040f7f32a8200ff59541005facaa0803fc655040f7e32a8200ffd51410077ea8a081bfe5450401feaa28206ff1514100778a8a0803ff63504017fb1a821cff98d41015fcc6a0803fd6350439fe31a8202bf18d41007fea6a0873fe5350401fea9a821cff14d41037fe86a0803bf4350439ff21a8200ff50d410077a86a081bfc4350401ffb128200bfd8941007dec4a0802ef6250401ff3128200ff58941007f8c4a0816fc6250401f63128200bb18941007fea4a0803fe5250401fea928200ff14941037fe84a0803bf4250401ff2128200ff509410077a84a081bfc4250439ff9928200ff8c941007fa64a0873fc3250401ffa8a8203ff94541007faa2a080ffc515040dffa0a8206fdd054101ffc82a080fbe4150439ff98a8203ff0c541007fec0a0802ff6050437ff3028201bf98141007fac0a086ffc60504037e302821bff941410dff8a0a086ffe405040dfe202821cffcc1410dffc60a086ffc3050437ff102821bff081410dffc20a080ffc1050407ffb288203bfd944101ffcca2081efe6510407feb288200bf5944101ff8ca2080efc651040d7f3208206ffd5041037fca82081bfd541040dfe2a08203ffd8c4101ffcc62080afe6310407feb188200bf58c4101ff8c62080efc6310401ffa98821aff94c41007faa62086bfc531040dffa188206ff90c41037fa862081bfc4310407ffb108203ff9884102dfcc42080ffd62104017eb108203ff18841007fea420803fe5210401fea908200ff14841037fe842081bfe4210401df2108206ff50841037f8842081bbc4210435ff9908200ff8c841007fa642086bfc32104077f3088203ffd444101ffca22080ffd5110407fe2888203ffd044101f7e822080ffe4110407fb2088203ff5044101f7a822081bf54110407ff9888203ff0c44101ffec02080ffe60104037f3008203ff58041005fac02080ffc60104037e3008219ff940410cff8a02081bfe401040dfe200821affcc0410cffc6020867fc3010433ff1008219ff0804101ffc202080ffc1010407ffb2c6203bfd963101ffccb1881efe658c407feb2c6200bf5963101ff8cb1880efc658c407ffb246203bfd923101ffcc91881afe648c407feb246200bf5923101ff8c91880efc648c401ffaa46200ff95231007faa918803fc548c4057eb1c6202ffd4e31017fca71880bfd538c405fe29c6202ffd0e31017fc871880bfd438c405fe21c6203ffd8a3101ffcc518816fe628c407feb146200bf58a3101ff8c518803ff528c401ff2946200ff54a31007f8a518803ff428c401ff2146200ff50a31007f8851880bff328c405ff1946202ff4ca31017f8651880efe618c407ffa8c6203ff9
  | 7 => 0xa888ffc2054447ff082a203ff0415103dfcca2880fff6414407ff320a206bf9905101ffac828802fd6414407fe320a207ffd505103ffca82881ffd541440ffe2a0a203ffd8c5101ffcc62880afe6314407feb18a200bf58c5101ff8c62880efc631440fffa98a207dfd4c5103ffca62881ffd5314401bea98a207ff14c51007fe862888bfe4314401fea18a222ff10c5101ffec42880ffe621440b7f310a203ff58851005fac42880ffc621440fffa90a207ff9485103ffaa42881ffc5214401ffa10a200ff90851007fa8428803fc4214445ff990a200ff8c851007fa642888bfc32144077f308a203ffd445101efea22880ffe5114407fb288a203ff5445101efaa22881ff55114407ff988a203ff0c45101ffec02880ffe60144037f300a203ff58051005fac02880ffc60144037e300a207ff9405110efca02881ffc501440fbe280a221ff9005110ff8802888bff3014443ff180a221ff0c05110ffc4028887fc2014407ff080a203ff04051037fecba081aff65d040dff32e8207bf99741037facba0802fd65d040dfe32e8206bf19741037fea9a0803bf54d040dff2a68206ff55341037f8a9a081bbc54d040dffb1e8206ff98f41015fcc7a081bfd63d04017eb1e8206ff18f41015f8c7a0803ff53d0441ff29e8200ff54f41107f8a7a081bff43d040ddfa1e8206ff90f41037fa87a0803bd43d040dfe21e8206ffd8b41037fcc5a0816fe62d040dfeb168200bf58b41037f8c5a0803ff52d0401ff2968200ff54b41007f8a5a081bff42d040ddfa168206ff90b41037fa85a0803bd42d040dfe2168220ffccb41007fc65a0803fd32d0441fe1968200ffd474101ffca3a0803fd51d0407fe28e8220ffcc74101ff863a081bff60d040dff3068201bf98341037fac1a0802fd60d040dfe3068201bf183410fffca1a087ffc50d040dff2068206ff10341107fe61a087ffe30d043ffe186821fff883410fff841a087ffe10d0407fe0868203ffd964101dfecb2080ffe659040f7f32c8203ff59641005facb2080ffc65904077e32c8200bf59241007fea92081bfe5490401feaa48206ff1524101ffec72080ffe63904057f31c8203ff58e41005fac72080ffc63904077e31c8200ffd4e410f7fca720803fd539043dfe29c8206ffd0e410f7fc8720803fd439040dfe21c8203ffd8a4101ffcc520816fe6290407feb148200bf58a4101ff8c520803ff5290401ff2948200ff54a41007f8a52081bff4290401ff2148200ef90a41007fa852081bfc4290401de214821effcca41007fc6520803fd329043dfe1948203bf9864101ffea32080ffe5190407fea8c8203ff1464101ffe832080fbf419040dfba0c8203ffcc64101ff8632080fff6090407ff3048201bf9824101ffac120802fd6090407fe3048201bf182410effca120877fc509043
  | 8 => 0xf98132007fac0990a7fc604c8037e3026429ff9413214ff8a0990a7fe404c853fe2026402ffcc132017fc609900bfc304c853ff1026405ff0813214ffc20990a7fc104c80fffb26a207ff99351035fcc9a881ffd64d44017eb26a207ff1935103ffea9a881ffe54d440ffeaa6a207ff1535103ffec7a881ffe63d44057f31ea207ff58f51005fac7a881ffc63d44057e31ea207ffd4f5103ffca7a881ffd53d440ffe29ea200ffd0f51147fc87a8803fd43d4451fe21ea207ffd8b5103ffcc5a8816fe62d440ffeb16a200bf58b5103ff8c5a881fff52d440fbfa96a207ff94b5103ffaa5a88037d52d440ffe296a200ffd0b51007fc85a8803fd42d4401fe216a228ffccb51007fc65a8803fd32d4451fe196a228ffcc75101ff863a881fff60d440fff306a201bf9835103ffac1a8802fd60d440ffe306a201bf1835103ffca1a881ffc50d444fff206a227ff10351147fe61a889ffe30d444ffe186a227ff8835113ff841a889ffe10d4407fe086a200bf5965101ffec92880ffe649440d7f324a203ef992510057cc92880ffd64944017eb24a203ef592510057ac92880ffc649440fffaa4a200ff95251007faa92881ffc5494407ffb1ca203ff98e51015fcc72880ffd63944017eb1ca203ff18e5101df8c72881fff5394401bfa9ca226ff94e51007faa7288037d539440ffe29ca200ffd0e51137fc8728803fd439444dfe21ca203ffd8a5101ffcc528816fe6294407feb14a200bf58a5101ff8c52881fff5294401ff294a200ff54a5103ff8a528803ff4294401ff214a200ff50a51007f8852889bff3294401ff194a200ff4ca51137f8652880efe6194407ffa8ca203dfd465103feea32880fff3194407fe18ca203ffd825101ffcc128806fe6094407feb04a200bf5825101ff8c128806fc609444bff284a225df9425103ff8a1288977c509444bff204a225ff10251137fe6128897fe309444bfe184a225ff8825112ff8412880ffe1094407fe084a200ffd9151005fec8a8803fe6454401feb22a200ff19151035f8c8a881fff5454401ff2a2a200ff5515103ff8a8a8803ff63544017fb1aa224ff98d51015fcc6a8803fd6354449fe31aa202bf18d5103ffea6a8893fe5354401fea9aa207ff14d51007fe86a8893fe4354401fea1aa224ff10d51007fec4a8802ff6254401ff312a200ff58951007f8c4a8816fc625440fffa92a200dfd4951007fca4a8803fd5254401bea92a207ff14951007fe84a8803fe4254401fea12a200ff10951127fe64a8803fe3254401fe992a224ff0c95103ffea2a881ff75154407ff28aa203df94551127fe62a880ffc3154401ffb02a200bfd815111ffcc0a8806fe6054401feb02a223ff1815100df8c0a888ffe505440ffe282a223ff9015111ff880a8893ff3054447ff182a223ff0c15111ffc40
  | 9 => 0x85dfe18a8400ffd8142005fec0a10b7fe60508037f3028400ff5814216ff8c0a1006fc605085bff282842dff1414216ffc80a101bfc405085dff982842dff8c14216ff860a10b7fe205080bfe102842dff8414216ff820a1017ff651080b7fb288405ff9944203dfcca210177e65108013f3288405ff59442005faca210177d65108013eb288405ff1944202df8ca2101afe641080dffaa08400efd5042037fca82101bfd541080dfe2a08406ef1504202ffec621017fe63108057f3188405ff58c42005fac621017fc631080b7e3188400ffd4c42167fca621003fd5310859fe2988406ffd0c420377e862101bfe431080dfea188400ef50c42037f88621016fe621080bffa908405ff9484202ffaa421017fc521080bffa108405efd084202ffc8421017ee421080bfea108405ef50842037da8421017ff321080bfe1908405ffd844202ffcc22100efe611080bfeb088400bf5844202ff8c2210b3ff3110859fe1888405ffd804202ffcc021006fe601080bfeb008400bf5804202ff8c021006fc6010857ff280842bff14042037fc802101bfc4010859ff980842bff8c04215ff86021017fe201080bfe100842bff8404215ff82021017ff658c80b7fb2c6405ff9963203dfccb19017fd658c8017eb2c6405ff1963202df8cb19017ff648c80b7fb246405ff99232035fcc919017fd648c8017eb246405ff1923202df8c919003ff548c801ff2a46400ff55232007f8a91900afd638c805ffa9c6402ff94e32017faa71900bfc538c805ffa1c6402ff90e32017fa871900bfc438c80b7f3146405ffd4a3202ffca519017fd528c80bfe2946405ffd0a3202ffc8519017fd428c80bfe2146405ffcca3202fbe651900bef328c80bfe1946405fb0ca3202ffec319017fe618c8077f30c6405ff58632005fac319017fc618c805ff98c6402ff0c63202ffec119017fe608c8037f3046405ff58232005fac119017fc608c8037e304642aff94232157f8a1190abfe408c855fe2046402ffcc232017fc611900bfc308c80bff1046405ff08232157fc21190abfc108c801ffb2a6400bfd9532007fcca9901efe654c801feb2a6400bf59532007f8ca9901efc654c801ffb226400bfd9132007fcc89901afe644c801feb226400bf59132007f8c89901afc644c801ffaa26400ff95132007faa899003fc544c80b7fb1a6402ffd4d32017fca69900bfd534c805fe29a6402ffd0d32017fc869900bfd434c805fe21a6402bfd8932007fea499017fe524c801fea926405ff14932007fe8499017fe424c801fea126405ff10932017fe649900bef324c80bff1926405f78c93202ff86499017dc324c805f61926400ffd8532005fec299003fe614c801feb0a6400ff1853201df8c29900bff314c805ef98a6402ff0c532007fec099002ff604c853ff3026401b
  | 10 => 0xc629017fe63148057f318a405ff58c52005fac629017fc631480b7e318a407ffd4c5203ffca62901ffd531480ffe298a400ffd0c521a7fc8629003fd4314869fe218a405bf9885202ffea4290177f521480bff290a405fb9485202ffaa4290177d521480ff6a90a405ffcc85202ff86429017ff611480bff308a403bf9845202ffac229002fd611480bfe308a434ffcc4521a7f86229017ff601480bff300a401bf9805202ffac029002fd601480bfe300a401bf1805203ffca02901ffc5014867ff200a433ff100521a7fe60290cffe3014867fe180a405ff8805202ff840290cffe1014867fe080a406ffd9742035fecba101bfe65d080f7f32e8406ff59742005facba101bfc65d080d7e32e8406ffd5342037fca9a101bfd54d080dfe2a68406ffd8f42037fcc7a100afe63d080dfeb1e8400bf58f42037f8c7a100afc63d0801ffa9e8432ff94f42007faa7a10cbfc53d080dffa1e8406ff90f42037fa87a101bfc43d0801ffa968405ff94b42007faa5a1017fc52d0865ff9968405ff0cb42037fec3a101bfe61d08077f30e8406ff58742005fac3a101bfc61d0865ff98e8432ff0c742037fec1a101bfe60d08037f3068406ff58342005fac1a101bfc60d08037e3068431ff9434218ff8a1a101bfe40d080dfe2068432ffcc34218ffc61a10c7fc30d0863ff1068405ff0834218ffc21a10c7fc10d080bffb2c8405bfd964202ffccb2101efe659080bfeb2c8400bf5964202ff8cb21016fc65908017eb248400ffd52420077ea92101bfe5490801feaa48406ff1524200778a921017ff639080bff31c8402bf98e4202ffac721002fd639080bfe31c8405bf18e42007fea7210c3fe5390801fea9c8430ff14e42037fe8721003bf4390861ff21c8400ff50e420077a872101bfc439080b7f3148405ffd4a4202ffca521017fd529080bfe2948405ffd0a4202f7e852101bef429080bff9948405ff0ca4202ffec321017fe61908077f30c8405ff58642005fac321017fc6190861ff98c8430ff0c64202ffec121017fe60908037f3048405ff58242005fac121017fc60908037e304842fff9424217ff8a1210bffe409080dfe2048430ffcc24217ffc61210bffc309080bff1048405ff0824217ffc21210bffc1090801ffb2a8400bfd9542007fccaa101efe6550801feb2a8400bf59542007f8caa101efc6550801ffaa28406ff95142007faa8a101bfc5450801ffb1a8400bfd8d42177fcc6a100afe6350801feb1a842eff18d42015f8c6a1003ff535085dff29a8400ff54d42177f8a6a101bff435085dff21a8400ff50d42037f886a1003ff525080bff2928400ff5494202ff8a4a101bff425080df7a128405ff9094202f7c84a10bbff325080bfe1928400ffd8542005fec2a1003fe6150801feb0a8400ff1854201df8c2a10bbff3150
  | 11 => 0xff1854301df8c2a180bff3150c05fe18a8600ffd8143005fec0a18effe6050c037f3028600ff581431dff8c0a1806fc6050c77ff282863bff141431dffc80a181bfc4050c05ff9828602ff8c143017f860a18effe2050c77fe102863bff841431dff820a181fff64d480fff326a406bf9935203ffac9a9002fd64d480ffe326a407ffd535203efea9a901ffe54d480ffeaa6a400df5535203ff8a9a901fff63d480fff31ea402bf98f5203ffac7a9002fd63d480ffe31ea402bf18f5203ffea7a901f7f53d480fff29ea407ff54f52006faa7a901ffc53d4801ffa1ea43aff90f52007fa87a90ebfc43d4875ff996a405ff0cb5203ffec3a901ffe61d48077f30ea407ff58752005fac3a901ffc61d4875ff98ea43aff0c75203ffec1a901ffe60d48037f306a407ff58352005fac1a901ffc60d48037e306a407ff943521cefca1a901ffc50d480fbe286a439ff903521cff881a90ebff30d4873ff186a439ff0c3521cffc41a9017fc20d4873ff086a439ff04352005facb29017ff649480bff324a406bf9925202ffac929002fd649480bfe324a407ffd5252007fca929003fd549480ffe2a4a405ffd8e5202ffcc72900afe639480bfeb1ca400bf58e5202ff8c729016fc639480fffa9ca438ff94e52007faa72901ffc5394801ffa1ca438ff90e52007fa87290e3fc439480b7f314a405ffd4a5202efea52901fef529480bff994a405ff0ca5202ffec329017fe61948077f30ca405ff58652005fac329017fc6194871ff98ca438ff0c65202ffec129017fe60948037f304a405ff58252005fac129017fc60948037e304a437ff9425203ff8a1290dffe409486ffe204a438ffcc2521bffc61290dffc309480bff104a405ff082521bffc21290dffc1094801ffb22a400bfd91520077ec8a9002bf6454801ff322a400ff59152007f8c8a901afc6454801de322a400af1915203ffea8a90037f5454801ff2a2a400ff55152006faa8a901ffc5454801ffb1aa400bfd8d521b7fcc6a900afe6354801feb1aa436ff18d52015f8c6a901fff5354801bfa9aa436ff94d52007faa6a90037d535480ffe29aa400ffd0d521b7fc86a9003fd435486dfe21aa407ffd495203fdea4a9017fe525480bbf292a436ffcc95202ff864a9003ff61548017fb0aa400fdd8552005eec2a9003fe6154801feb0aa400ff1855201df8c2a9003f461548017a30aa436ffcc5521b7f862a9003ff60548017fb02a435ff9815200dfcc0a9003fd605486bfe302a401bf181521affca0a90d77e505480ffe282a435df141521affc80a90d7fc405486dff982a435ff8c1521aff860a90d7fe205480bfe102a435ff841521aff820a901efe651480bffb20a405ff99052035fcc829017fd64148017eb20a405ff1905203ffea82901ffe541480ffeaa0a407ff1505202ffe
  | 12 => 0x1500dff300a801bf98054037fac02a002fd601500dfe300a801bf1805403ffca02a01ffc501500dff200a806ff10054207fe602a0fffe301507ffe180a83fff880541fff8402a0fffe101507ffe080a802bf9975303ffec9a981ffe64d4c0d7f326a607ff59353005fac9a981ffc64d4c0fffaa6a607ff9535303ffaa9a981ffc54d4c057eb1ea602ff94f53016fca7a980bde53d4c05af29ea602ff14f53016f8a7a980bfe43d4c05fe21ea607ffd8b5303ffcc5a9816fe62d4c0ffeb16a600bf58b5303ff8c5a980bff32d4c05fe196a607ffd875303ffcc3a980efe61d4c0ffeb0ea600bf5875303ff8c3a980bff31d4c05fe18ea607ffd835303ffcc1a9806fe60d4c0ffeb06a600bf5835303ff8c1a9806fc60d4c0fff286a607ff143531f7fc81a98fbfc40d4c05ff986a602ff8c353017f861a98fbfe20d4c7dfe106a63eff843531f7f821a980aff6554c01ffb22a600bfd9153007fcc8a9803fd6454c01fe322a606bf1915303ffea8a9803fe5454c01feaa2a607ff15153015fec6a980bff5354c0fefa9aa602ff94d53016fca6a980bfc5354c05be29aa602f714d53017fc86a980bfc4354c01ffb12a600bfd8953007fcc4a9803fd6254c01fe312a605bf18953017fe64a980bfc3254c01ffb0aa600bfd8553007fcc2a9803fd6154c01fe30aa603bf18553017fe62a980bfc3154c01ffb02a600bfd81531effcc0a9806fe6054c01feb02a63dff1815300df8c0a98f7fe5054c0ffe282a63dff901531eff880a980bff3054c05ef982a602ff8c153017f860a98f7fe2054c7bfe102a63dff841531eff820a981bff65d0c0d7fb2e8606ff9974303dfccba181bfd65d0c017eb2e8606ff19743035f8cba180afe64d0c0dffaa68606ff95343037faa9a181bfc54d0c057eb1e8602ffd4f43017fca7a180bfd53d0c05fe29e8602ff90f430177c87a180bde43d0c05fe21e8602ef10f43037fec5a181bfe62d0c0b7f3168606ff58b43005fac5a181bfc62d0c05ff9968602ff0cb43037fec3a181bfe61d0c077f30e8606ff58743005fac3a181bfc61d0c05ff98e8602ff0c743037fec1a181bfe60d0c037f3068606ff58343005fac1a181bfc60d0c037e306863cff943431e7f8a1a181bfe40d0c0dfe2068602ffcc343017fc61a180bfc30d0c79ff106863cff083431e7fc21a18f3fc10d0c01ffb2a8600bfd9543007fccaa181efe6550c01feb2a8600bf59543007f8caa181efc6550c057fb228600ffd5143037fca8a1803fd5450c0dfe2a28602bfd8d43017fea6a180bfe5350c05fea9a8602ff14d43017fe86a181bdf4350c05ff21a8602ef90d43017f886a180bbc4350c05ee21a8600ffd8943005fec4a1803fe6250c01feb128600ff1894302df8c4a180bff3250c05fe1928600ffd8543005fec2a1803fe6150c01feb0a860
  | 13 => 0x3001000000800000080200020000000014000003000003400c00200580040100000030004004000000003402600d003001000000000000180060000000024002001004004800600000200040080000010000012000011000c038003000000c00400d00000000000050050008004004004000800000a000802000c00000100480080020048000000001006001c03800800000000020050000018022001000001800800e0010000002002000001c00c004000000800200f03ffec7aa01ffe63d50057f31ea807ff58f54005fac7aa01ffc63d50057e31ea807ff94f5403ff8a7aa11bfe43d500dfe21ea807ffd8b5403ffcc5aa016fe62d500ffeb16a800bf58b5403ff8c5aa11bff32d508dfe196a807ffd875403ffcc3aa00efe61d500ffeb0ea800bf5875403ff8c3aa11bff31d508dfe18ea807ffd835403ffcc1aa006fe60d500ffeb06a800bf5835403ff8c1aa006fc60d500fff286a807ff1435422ffc81aa01bfc40d508dff986a845ff8c35422ff861aa117fe20d508bfe106a845ff8435422ff821aa002fd659500d7f324a806ffd5254036fea92a01fbf54950019faa4a806ffd8e54037fcc72a00afe639500dfeb1ca800bf58e54037f8c72a00afc6395089ff29ca807ff14e54037fc872a01bfc439500dffb14a806ff98a5402dfcc52a01bfd62950017eb14a806ff18a54227fe652a113fc329500dffb0ca806ff9865401dfcc32a01bfd61950017eb0ca806ff18654227fe632a113fc319500dffb04a806ff9825400dfcc12a01bfd60950017eb04a806ff1825400df8c12a10ffe509500ffe284a806ff90254037f8812a113ff3095087ff184a843ff0c25421ffc412a10ffc2095087ff084a843ff0425403ffea8aa01fbf545500dff2a2a806df95154007fec6aa002ff6355085ff31aa802bf98d54007fac6aa10bfc63550057e31aa842ff94d5403ff8a6aa10bfe435500dfe21aa800ffd8954005fec4aa003fe6255001feb12a800ff1895402df8c4aa10bff3255085fe192a800ffd8554005fec2aa003fe6155001feb0aa800ff1855401df8c2aa10bff3155085fe18aa800ffd8154005fec0aa107fe60550037f302a800ff5815420ff8c0aa006fc6055083ff282a807ff1415420ffc80aa01bfc4055085ff982a841ff8c15420ff860aa107fe2055083fe102a841ff8415420ff820aa01efe651500d7f320a806ffd5054036fea82a01bfe541500ddf2a0a806ff55054036faa82a01fbd541500dffb18a806ff98c54015fcc62a01bfd63150017eb18a806ff18c54015f8c62a01ffe531500ffe298a806ff90c54037f8862a01bff621500dff310a805bf98854037fac42a002fd621500dfe310a840ffcc854207f8642a01bff611500dff308a803bf98454037fac22a002fd611500dfe308a840ffcc454207f8622a01bff60
  | 14 => 0x12001000000000000200080080000000000004000003001801800000000100240120000080038000005003800000a002000000002c0010008014000009001800000000000000080020000000014008002002000c00a000000800800000000000000040070080000008002002000000000000280040160090008014012001003802c0060080030008004000000000000a000001000001c0000008018002001000800000000800000040000070040000000002002800c002002000000000e0060000000004006004000400000000100180280010068008006001001801c01a00d0038000000002009800001e0040000004000003001800c00a000001000400200500000040000010008004000000000800002200100080080020000000000010007003801000000000180040040030028000002004000000002200300080080140040088000006005007001c002003005801000200e0000004010001000001c002005002000000800700280000000230008014000000000802c0120000000008000000003800c0000090000000000000000003800601a000000000600d0008004016001002000000e0000038038020000003000401e0000040000000000004000400a000000001800a0060018000000006000800000c001000802400600400680080060070000000008000004801400201a001000401400c000000000200200100080020000088004002006002000801e00500000000000020040000000004002000c002003001800c00000c003000000000400180440140020000004002001002001400e0340070000004003000800000800100100100020030020014020002000800000400500180040360000058004000001005000400a000002800400000f008002c004004003003c010000000005801200000080040260080028018000006006000400200600380600000070020008000004000000c00000200080500000000008010000016000800c0000010000004026005006000400a00e000002400e000002000001a000000000001600700d0014000000000003000c005000000803400d005002000a0010008004004001002002c00a000000000400200b0030010002000000000c000000000000800000b000000c00001600b000000200000e800401e00400000580060030008028000001001800400200c00680580220000010040000000000803400000100b8000004001004000000000b000000c01a0070008008002000003000c008001002801800a003006000000200100080000060030000000000000004000002a000001000c000002003000000c00000080040180070018018002005000000401201c0028000000008000000000200500800040460020050078002010007802000000000280000000040000018002005003000c004
  | 15 => 0x128a0f303b07140a04bd0000000000000000198030615d0000db06e02ea000000150828a0d9af400d800058f003400000004e8b8c67400000027f00000003d71f94f1a0000001820000105298000000085f00028e5002535148271c0008674ad800173c6af3c5a6b51960001230000000b7e000147c0000720d71b113f07542b00000c807d956786d40000002610000e6c8c603f1a64abc000012a7dce90000000175c0003d500012b48620005caa548dcc0000710c4c2aa0fd00000000005310000000000b3112a800097067035a8ec13fa7a00e30ac930ca1b0001d916e880e1998000156b10094000081aa6127400006b20000a518340005fd4211acce0c5c05510000e6425b5738bc126a8075e49e3970617134e0ae152c3641099fe82743ea58b0000c220000000000e7498b22f800088aa850002d003460002ea2da8d100dc0000001496000234800040e3da0001c4cda28fd00024412e40000429a886b69b0536937080e8451d0a94466295e3942c392c2aa13bf16d852622e44288d048658a3b802b44c29300ef0e407560000000af55ee000000135c000000000000116c19126f000093e30b00000002c4000000126400000000000000000004fb0000222b80562a4a069200009085415fabe50c829c00000000001a9942817200000012e00001e617140000000001a4c00045b00000000000000001438852a5427d8e147882210001d4400000018e8001030000000209c02e0004318000d5aa2729d156c00088d106a2b4e4c1890a9235400000000000000008ef5860000ff0004800000800d0010004000006001800c000000001000c000002004000000a000009804000a004002000401a002005802000a0090070000008001000004c002006000000000400200000180020000030004000000000000002000100100240140090038000008000002001c018004000000000200400000000160070010014008000000800000200100080140000000010000006002000000000c0060068048006008000000001c005003000000200e00a0000002002003803c0040020030018000000000000c0000010028004002002000002c01c00200600000020020020024016009000000000c0000000000000000001800401000d0048004006009000003000200c002000c000009009800c0060020010010002002002806000e00c00300200040030010000002010001002000400100400040040020050000002000000800000e0000068010006010000000800000000000080040080018004002001003000c02c02f0068054000002000000c0080040000000000000000000000000d004000000c00000380000020050010004002000000000000a0000038004000006000800c0020000000000000000002800400c003002800c004000000004c000004003
  | 16 => 0x94cc90200580002432d60000070474000000000000000000007de000079039aa261470120c9c4d40000ea04200000000000ef45950000000000a6b00000000f60001b394288228a61518e54000b5207680000002fc3242208f647953a99a5558e000027000167023100000000005c8302ae2478e0000002d300000005f0a2254ce4d65a09570000b791c42cf91ae0001c122815a0bd600000000002c25a98f616a06dd2b48440000bd93ff91ccc160003c500014f20005728000d200000000a714c00000000000d2e0804c71390f3200000006bc0000001c209088aca881d200000000000002c8800099100009c000046411980008901f13920ecd54a3eb000113cb3e5512f70b30f8c94c4511a6c1a87ac0002aa07a490b51a80000003570000d38000bf041498391d426433c8a7498a9203f88b04aec3fc23c1729224a6c1a2940d5da72a004811d63a6f92f49eb429228b000000000042a00000010e87d00b18b9046086b1f100006a692700000014745e8000000101e00029900014d018f191165068091700000011e6a5909c80014605a60180cfca124623628f914c60350ff0000d04074103238541400016b24512640004a3af3167400033a13f94405ef0c295002d80883b72274ab08802a228bd18600e0000000000000000000000027e23fad3c24800016c87dc0004170000d1d1227f41fc000169226a38513d4e2ea46409892858e9a15f7a39c00076a0189f48c0e22b13628dd1280004190000bbc00038f8cf00008d20510ef84a46ba5b310d80001d42280f7cd1c51046420ccfa68b32771644e5805f4e929953c240b000000155c5c200020353760000001ac09641e20000e3cec6000000152c0002c9142a55400024e5cc05303c2a5d46c091d0820f625380000000003c29898bcc00052d269c12c5062c687f4b3200055e9ec0000a6400021d562200013f800013252e4e68af05b427d2a3a8216d656e0000000fd6b0919f00000000eb0b7800000020900029887907cb000151974e0004b22b516dc6832e81730c364c05ed83691ee38c517124c00011252b1a951b66bb0001f9d4d232e00000790fa324000000056e1b812d2a6ccf676f30ea4ad1d206202202dcfcc4c62a600000000001af2bc80000004cf0001512000000264800000000000000007183a917352220000d6a0a0c9832500013d096e0000000000fd83cd0649a841225244458000074bc7000000000000031f0740e8000c06718e82062e900000000000005280d504720f10000de80000004ba205c000ae65e6800024068a2879324f3c00002980000000002d19e68aee00023b8000000000147aa38000649565a65c0000003a395e8000000009000000047c40ea70400000057e14fc30459a301235000000028280014ae1c34082a78c9a0383a0800088800a2a2a05
  | 17 => 0x4dab5f24d0ca56a281955300000002ca38c940549e4ec1ed9fbce3c00050022f8000bd11c6800000057c0000000ece0001a5000000000045080001260004c1800000000000000000007b90002b580000004251ac50d0aa0000000135e57e000037d5f685749b00000000831eea8796d0bc80000000218a980001bcd4bc17309880013464235110000a4a3660c02f1000098739c106000000105802a40005c73a700013ba05e2cdabc17b0000238000075e94b11297b00006544121cfc7d0b7b11799c40cc0002470d086f0b0a5d915206400e50ad08d400053c5a505997bab6f06a8f0060c86442797700008fa00007b08ec81f3b99bac39840c45ba308c5c00008500000000000002e482805f64d10000000a495191fa0000a43000266013c21901c83800007e13b3085479400009622404460003ca27b43ce455000000000066e019217097215b561022ce9838e1d619650440004e98dcc5ea00000000000001a722c11e400065e5b0a7d40002510002a8c0007d610d0e80000a915459884e6226312e0728de02bf4ca159540cb565a2017157c8060c40be8000000047a48935000000000001e80000000000c2e0000000000000b4e5ee000000090800006840000003c90a4400000001101a44acac8126afc8f926a852a8acd5ba0001e1800000006d0958000000000321a05413e5bf41d1d0854e2f614414b12c02403be91a8000bb917f0b84aaa56a37225ed5bca9c3bbaaa800069d0e0119ca9262821e1794f561b643f8000000000000216c00000000000008da3f15391f1d6c6000580a930dbe0be36111000b42fb3112edd7be9771dc11c80f416153dac9ceb00003f49e300004ff4bb267085e5d50f80000548b69000000000060300000014940000000000000000000105400000000000000009f957c118400000000005ad3643320002189034bf13b400000008cd1330000000000000000058660a4be2071648a450800e6c00000000000011e800024a26340006300341e1c000000000000084422a1e29b9431c0000002d800002500000000fee0005b615480000000002e1028800017b8e0000039700000000000003360d18b5a0000bf136872c0001e58211164bde0751c244000004bf041146c16900012a0278489000263c19ea86489a4684647034330c6c7ac0002d8000077812d000000000002d47600011c859042726e8e72a3e05413bcb7a13f5a10360ee800025f9230738ad90000a5951880c46517f132a2274ba86040000004d7000051aadb5db103824c10d1e71e100000004c42f5d6500140f6a454358966506238869a22052f813478400000b026978a72e0fd18b525265d40192842a63520001960e3aaab5b2800106a5393c1a25d7425854ffa7e8a4274f3b6209400000028200000003ff522067151e6ef22e99289c404
  | 18 => 0x2d02b547de7bd1d380008364053d9a6280000001e9aed51c041958d2ad87540000000aec02214b00019d495800036a88750000004c8108550e0000bfa21c00000000023c129400051e80000000000000000000000385a9dd3de16a423800107800028d80001620004e48001548ab44bc000000096f00000000006b93f6aa4800000000000000008cf3a2142c000000000238c0000000000000cc228200021340000005f02ba4ba251e1492378f8422900027ec04e2450738e8c5d600004110917543720002d741d2b34000148c2340000001944000acc2fa22c0ade0003fe8cbc90e00000000000000000000000dce00043816385b64eb37423580e6a2d1392d642a22d113b0a0022c5e3366195cec00f90230c64bc20580000000dfc391428214818839800020c09cc60f537800030e11512a07cc00041600002983526ee000126c000000000077c00023f41606ad68c92105e1ad902220e53f239557e42e3009d6cfe694835e061897499d2dc99f16320943031d684ee4e908d99692f267e1690000f4ea3809b20ac3b2af437106ec672646563276400062b00026a400056256b800083a36a000000061c1d8262000177000000e2d70348bc300027380006f12b4000000000050b9e8c92033d3b10a313d66b8418800000024b466000000000000001480c80000001e8953400004312080c29e427923240001e0511810d16200000000003b88490000ef4000000000237c00053656480000008d126c1a2c0949de05f91080780000000000a101c20118000000000189000049ebd55e580000007a80002218f6c48407615687321144471cf826037d000000090056b20180000000003ed9b8cbf20000000001714000000194c000a7f00000000000004c02cf400000010f1aa43cc7594e3000000018d40b10dd5be4910000d40000000083af688006ea00003ed3ca82a3b280004ca00006c8af956400000000011ba00000005f527848a21ca90400000000012cc000302000243450e0000eb85e45c00e128d2b0428c04f209000118a00000319b42900003d080010aa25f46e1a9c84c4753a498c400006b10f80000000001f000017a845100003f0000000000000000070400024e037a9373608d20f820001019b700003b60ac071c2ea0560001ca462e564000234ce8a70f1fe9e3c40a0005be88f40542de43b0348a0e28400022f42e83f221a2498d541bf485012cbb25eb41ca3c40000000002dd40004e1000000000000000000000000c21eb8000ccc00026508e127a2170001bd866a2590df0000682000585800170417a43d993c56c00040908dd1721370950000d7e0004d8961ce2200000028c400000051491b80009b4000153c00000004600000008b82fba7c400000012f1a1000000032200009827861f38000d4036b000000000041e11f00
  | 19 => 0x1790dc79d00000000000002900000c8200000000017485b428c800113e0004a18d7400056100007d40007ba21a800000000052e23980005a40002dc0abe04c31298d46120004a3047c1360000001c48d1e3180c20280e7a00000000000000f74ea00003187c05c60d9423000000000000b672700000014240003651ff972051c03c8098e462861ec9a1c0005d200006603d644a00000004a62df00000008ae3a647f18791147d82a68d88490a282d898680000003ae8270c463bf0dc91940006004e78cc118e4aa3d48fb92a01d3417000162a00041f80015d86c03e2a3e40000002672740f8621c4368904000b2a0000000000000000076c0000000a68000b9236f0002d9c0008f800026688822f32f8ac7c00042b21e9fecc3e0002d28ca001634c5b11dc417abbf190ac10f4a1d5000172c00000000009ac6dc1a22181f3c00020a27e000059017600011a12727da4681b5126600047f91e80006765d88c8c2dc90f000000000000000000000003ec1cf94540000005bb00010c20002318000000000000267c0005ed4eb1374f704f83868aa12dc000083004c006baf04490c90b2ba008ea1116f400011d2b452d84f71e488b08e23440002cc00ce000000000160cab90000bfd7d87bc54995e000000000022d0b5c0cc45d24b93b84ae51a19a563049841d80007fc43e1d715c4000000000116885095d00014dc0004fd18f00000000003319c00000a8a449264d1886e05f529f0b1e3b705280015c03de43c87492d2b1347b01dcff2000000042c0006fa00000000006cb15000000000000000000000b353ee00016ae00000000000004200000b540009df0000000000000000000071252d2da975818c3564d22e6d5b401a293a5600fa74d54faa64c54b0559287c80008230ab2b48410be32978c54960bac49d22b06ec000185028c000af616985dc000000000160800039e426284ccd41cb5f70000f949b300000000000005f3974d4fa2a110901e0b542aa5be28109ecb5b3a303c84286622ba26a8d6e29e2861c047647201801e4d43e7612dd15296da00000009e0476000000000000047d0002ac4c4e000000000128817c000034d3b0b07359249517665613121f8dda4b4187937c0009c21dd8a685e4361272a2100000002951fa96c87b516a2ddc000609000206c1200000000aacb12aeb42014a17d2a1809390057220000da112400000048700d930a29514f80000002740001024000583167aeb4a867721e80bb51183c13698c04080bed56229d85280c03b6807d7683cf3e69380e428363490bb06765925f30000c3086c25480000000000001b84000af33d500012fa9e70b2a80c00000014d8000d9c000000129161000028b0000aae1d63280f180001e552000016906cd00029c4ace00017a0000000000590000000000054800013360
  | 20 => 0x295acc92d4a3b1089990316a240b6a948d1a000000000000000055a800158600000002b93964d32aeaecc6b495a5ce87a0c5221b0cb962000000034d0c712326fb32114480004a50000e0d0708fc37c00008580002e784f80000000cf9598bbeafe4c61bdc6c000029f00000001080000ab811a03d19699e171044b26aac9854a3100000328000a2b000178134000002a2b4cb86a4717e9e200000000001270000194078262400095f36d253c3f2a190001f8c000b3c2db814484ab1b3a500000000634102ae95284e348f2e38000000000225800002f26d83140000002ba9b7970c0001b185140000002469248a6630c00000009f41c80000000000a7a157a8354f0a0f000000083827b5cb2854000000428a54c00079629315b4f38a05000000000400022f0000364000000099c0004590721e4088e15c0001f5c4022c452c0fe56f000000017ece5654137a000164600042e923d09013505d2ea474464744d8c10f9801000015643e83e35f58dd43deb0200000000002ee0001dd90127341b4afcc0000001fa996c5f0297441a1a8db627c144a4b40004f11fa0000a22a1d1712abc0000004de0b5c19a16000006580001233e41bc8000534000288434cb2d2ed00015e235c4d280000004bb00c89e51566521ba11ace78a800f51aac64c6cf00a997d5587f5361800060a9b73488d5481e93f1fd0cd95946733c01009666b7104c1ba54e600030b26d8eae0002f900013e80d702a968823c40a0001b1cc32b8509280005f25184e19c94b02abb3ea1c20aa80c71e880000000004540000000a485960b607169fe000000000000003f95b0826ab0541000137cac033d1efc00062f2dc000010227a1510000b6400005c00009020003b5abb80000004bd2cd90680003da2e94000000000000126200000000000000002b180012540000b39edc7a84ea2fa8c1d3e01e31378df8e1809705a05ec1dc000581906859a63b138969c92e6d80038fcc29e0b350816306860003448a600000005f427a0feca812780c3470201d1778000d587b10f4800115400000025fc44800000000007d20005de8000af2a33505a608d9053d50b0ed541c87330e00017766371f2a2b92ca8434df82e4bce20c554845c21e5bb36826d52188ee31b17054b65fe1cd000159c000000000006e000000000092aa0953a2a0c36091d0001c4028696d02100001823110002e5d65e0004aa00003a275002ea0b49e61c14e21a04c78acd22e2c50eb87e250d0dec2384743c480007cc826000133c00000059480015c80000002c700000000329b240006d91b8acac0005e446700000561da000000039c0000ff800049200000026ac0007970000000d300004f12e04a042440002d54a260004a48b01134881000256405c0004ed8000f48b9c00412141643ba49200000ea0000002
  | 21 => 0x25cc45a59c00021589a25564dc00013cc0000000000e3600000029d40000000000000faa000397800000000031fa010c8a32b5c380000008b547696ac00000044421bcb3043a2be85786d019321f800122c1090000df0196101000000033a0004f184e01fe7222cb800000000000027695d408700000000000004109258362bae0000e955b896b475896062c24c48e0b9c56a51d0000000ef61422082e980009633a58000d8c0570000e4d74600030225883ec6d60001674cfa43b00003e00009a6000184011c7fc00000000008931f0aa7416a88f05387253d27c434f82a952e5141fb80000003b400007f000071407d00856864e7000105149c9f23c894eca44901097000125e000000154123e66746c80006da89931c19ac4c014700017a800038a2418000574bb0000214c0007bb57120f55786fd22a12ac17662c481241470c70200006e82327f23f826e555a9ca57d057c32a7e001400009a085800000000005a111b0ddd14e00000000000006a42c30811478be200006f000000000019a0158bd307a9658030a01000294c00089c2d60000ebe00536b8000000000000000105e4af000000085a5be41ba4f807c0005df1bfc0004c71d6800173295600006806f2192000000000000000000003ba0000002f0000000054a95fc94c57b553abfc4040000001610000b3900000000007a62fc00012300000000e1d2120005aa0254276000000000036e4460000000000466000000016c10e000000000013306e853869e0000002d355b00005cfa7000006122b800008d818a5e700cc6fe0003f22f080000000000000b001f85352780b8ca3f5e9000000002000000000000004ae0e5000000000017cce60b8d10593310d26391afa50400010244a80002d08050cd00fc0009c51ce80000000001f6800000000000027b88c05e24eb954c000443000000033c5000000000000af500000001ccb730001a300004b601207b92e29680000000762a07213a6b044c8fb18f8a04e38b47000000000041f33900000002dc00000000001573be0001148000000000000065c01a0aa50ca90059f976d1e44b1134a028e6a77538380005ca2c60ac80009440000000180000000000037800000019b80008f6b9335e84bc00000009a212c0009f34f524100001a8000085913cab7219922c0debab1ee2998000000000000000054e25e00009a449e59d91f927666f3c0967937a2185ca05e13aa4cd483803d2a200024e8000724614000173824465500000000002e60002c48c647053ab09756fe5c434a23009f20002c5a16854c2b93f7034096ab9a23780012ae00027680000001544918cb00000000000000996000251800000023c41f21f080c0a40001bb1284000000000000000018d0000000000351a8b008a3385e3000117894e0000000000000000164cd2c
  | 22 => 0x1cf0002a349b28a34cb2894000b00050800114a000000000033200047a80000009403ef8010568a0243d03584ae0410000000000b173cc2ae0e1c164045083c4d063457780000b200000017fc07679f0000b14e5a7af1fd8710df80e300008a08a4be45152d2ca705a80000ca966e613000189161e0000000000deaba82d48c9d1b480245780a4d3c5f0000246c6962223a1930d0a88c120210e0a2e2832442180282a4d357066c89cb2e39992f971e06a3af0ba0fba4a00948b7501077843b9da517e06e00011341fc0003aa800000000003e0000000a6e000259c00098432580000000e85af1ef8000af900022a434a77900000003f6ab34392720d7c000000000000001b31e8000560b4544c114d744529286ac844e60002de19dd0162ce3e8af290e29ec0001dfc55868509eab84b5e4c80001830e6e90349600000005dd00000005a000031000004eabc12b92419398b0d064000062871a3e700000000925ad0000d006650000000b661aa00003450f0000000000000079b000000000073b5de000143800035a2604a8481e14c99fce2c5d85e78fc0bf494d1fb0c213a23a9158a4d00003033c10000c2abba17881c42e02ad0002ba0e2a84600018cc000573061800171600019a0d447720db000284400000000000004dc00034300008980000000d601deb72521000015e1325718b2c000113369
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x6705051000df470505100dff0705051001ef7605051001ff360505100dfb740505100dfb540505100dff22050510255f6768c51001ef6768c51001df7758c510005f5758c51000777658c51000774658c51001df7748c510005f5748c5100bdf5738c510016f6638c510016f4638c51023df6728c51000df6708c51000df4708c51001ef7608c51001ff3608c5100c7f2208c510014ff764c51000cfe764c5100bcfd764c51000cfc764c5100067f654c5100067c654c510006df634c510016dc634c510005fb704c51000df8704c51000df4764c510016f4764c51000cf4764c510005f7754c510005f5754c51000777654c51000774654c510005f7744c510005f5744c51001df7734c51001fd7734c510007d7634c510016f6634c510016f4634c510027d4634c51023df4724c510027d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100bff0704c51001ef7604c51001ff3604c5100bff2204c51000cfe76c851000cfc76c85100067f65c85100067c65c8510006ef62c851002eec62c851000dfa70c8510005f970c851000df676c85100aef676c851000cf676c851023df775c8510005f575c85100077765c851024ef665c851024ef465c85100077465c85100067465c851023df774c8510005f574c851023df773c8510005f573c851001df672c851023ef762c8510007e762c851023ef562c851023fe462c851000df670c85100aff270c851023ff170c851000df470c851001ef760c851001ff360c85100aff220c851002cff764851000cfe764851008cfd764851000cfc76485100067f65485100067c6548510005bf7448510005bc7448510006ef624851002eec6248510005fb704851000df8704851009df6760851001ef6760851001df7750851001f767508510005f5750851001f757508510005757508510007776508510246f66508510246f4650851000774650851000674650851001df7740851001fb67408510005f5740851001fb57408510005b5740851001df7730851001fd67308510005f5730851001fd57308510005d573085100adf6720851001fe6720851023ef7620851023ef56208510007e7420851023fe4420851000df6700851001ff2700851000df2700851001ff1700851000df4700851001ef7600851001ff3600851007ff2200851001df8764811002ef8764811001cf876481100077b654811000778654811000dfb724811000feb7248110007eb624811002efa624811002ef86248110007e86248110007ea5248110007e95248110007ea3248110007e93248110007f3714811001dfa714811001df87148110007f0714811000efb614811000ff36148110007f25148110007f15148110007f24148110007f14148110007f23148110007f1314811023ff3214811023ff02148110
  | 1 => 0x9100067f65909100067c6590910006bf6490910036bc649091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc76509100067f65509100067c6550910005f7715091001df4715091002cff7610910004fe7610910004fd761091002cfc76109100057e75109100057d75109100067f65109100067c6510910006bf6410910036bc6410910006ef621091002eec621091001df67110910005f5711091000dfa7010910005f9701091002cff768c910004fe768c910004fd768c91002cfc768c9100067f658c9100067c658c910006df638c910016dc638c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9100067c654c910005f7714c91001df4714c91000cfe76d451000cfc76d45100067f65d451003e7c65d451000dfa70d4510005f970d451010df6769451001ef6769451011df5759451012f77659451003ef6659451003ef4659451000774659451003e74659451001fb67494510005f5749451001fb57494510005b57494510005f5739451000777539451000775539451023df6729451000df6709451000df4709451001ef7609451001ff3609451012f76509451012f74509451012ff2209451003cff765451000cfe765451011cfd765451000cfc76545100067f655451003e7c6554510005fb705451000df8705451000df4765451003ef4765451000cf4765451001df7755451001f77755451000777655451003ef6655451003ef46554510007746554510005f77454510005f7735451023df47254510007775254510007755254510007f3705451000df6705451000df4705451011ff0705451001ef7605451001ff3605451011ff2205451000cfe76d051000cfc76d05100067f65d05100067c65d0510006bf64d0510036bc64d051000dfa70d0510005f970d05100cdf6769051001ef6769051001df77590510005f575905100077765905100077465905100ddf57490510036f66490510036f46490510005f5739051023df67290510007b64290510007b4429051000df6709051000df4709051001ef7609051001ff360905100eff22090510034ff765051000cfe76505100dcfd765051000cfc76505100067f65505100067c6550510006bf6450510036bc6450510005ef7250510005ec725051001fb44150510005fb705051000df8705051000df47650510036f4765051000cf47650510005f77550510005f5755051000777655051000774655051001df7745051001fb77450510007b76450510036f66450510036f46450510007b46450510007b75450510007b45450510005f77350510007b74350510007b54350510007e7725051023df47250510007e47250510005e47250510007b74250510007b54250510007f3705051000df
  | 2 => 0x6bf7458d10004bf7458d10034fc7458d10006bc7458d10034bc7458d100c4ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1002cfc7258d10006ec7258d1002cec7258d1025cff7158d10006f77158d100bcff7058d10006fb7058d1003cff76d4d10004fe76d4d10004fd76d4d1003cfc76d4d100067f65d4d1003e7c65d4d100275e53d4d1001df671d4d10005f571d4d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1003e7c6554d10005fb7054d1000df87054d10034ff76d0d10004fe76d0d10004fd76d0d10034fc76d0d100067f65d0d100067c65d0d10036be64d0d10006bd64d0d10006df63d0d10016dc63d0d1001df671d0d10005f571d0d1000dfa70d0d10005f970d0d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d100067c6550d10036be6450d10006bd6450d1002cfe76d89100067f65d89100067c65d891003cfe75d8910004fd75d8910034fe74d8910004fd74d8910014fe73d8910004fd73d8910014fc73d8910006ef32d8910006ec32d891001cfe71d891009ef571d891001cfc71d891001cff70d891000cfe70d891001cfd70d891000cfc70d891009eef20d891009eed20d89100057e75989100057d75989100067f65989100067c6598910006ef629891008df571989100057f75589100057c75589100067f65589100067c6558910005bf7458910005bc7458910005df7358910025dc73589100adf77158910004ff75589100067f75589100047f755891003cfc75589100067c755891003c7c7558910004ff7458910006bf7458910004bf7458910034fc7458910006bc7458910034bc7458910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc7358910006ef72589100acff7158910006f7715891008cff7058910006fb705891009cfe76189100067f65189100067c651891002eee6218910006ed621891003cff76d4910004fe76d4910004fd76d491003cfc76d49100067f65d491003e7c65d491001df671d4910005f571d491002cff7694910004fe7694910004fd769491002cfc76949100067f659491003e7c659491000dfa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc76549100067f655491003e7c6554910005bf7454910005bc7454910005f7715491001df4715491002cff7614910004fe7614910004fd761491002cfc76149100067f651491003e7c651491001df67114910005f5711491000dfa7014910005f97014910034ff76d0910004fe76d0910004fd76d0910034fc76d09100067f65d09100067c65d0910006ef62d091002eec62d091001df671d0910005f571d091002cff7690910004fe7690910004fd769091002cfc769
  | 3 => 0xc72195100067f32195100067c321951003e7f711951003e7e711951003e7d711951003e75711951003e7c71195102667e41195102667c41195100067f31195102667e31195102667c31195102667e21195102667c211951003e7f701951003e7e701951003e7d701951003e7c701951010e7f401951010e7e401951010e7d401951010e7c401951010e7f301951010e7e301951010e7d301951010e7c301951010e7f201951010e7e201951010e7d201951010e7c201951010e7f101951010e7e101951010e7d101951010e7c1019510034fe76d91100067f65d91100067c65d911003cfe75d9110004fd75d9110014fe73d9110004fd73d9110014fc73d9110006be43d9110006bc43d911002cfe72d9110004fd72d911001cfe71d911001cfc71d911001cff70d911000cfe70d911001cfd70d911000cfc70d91100eebf40d91100eebd40d91100057e75991100057d75991100067f65991100067c6599110006bf64991100ddf571991100057f75591100057c75591100067f65591100067c6559110005df7359110025dc7359110005ef7259110005ec72591100fdf77159110004ff75591100067f75591100047f755911003cfc75591100067c755911003c7c7559110006bf7459110004ff7359110006df7359110004df7359110014fe7359110014fc7359110006dc7359110014dc7359110004ff7259110006ef7259110004ef725911002cfc7259110006ec725911002cec72591100fcff7159110006f771591100dcff7059110006fb70591100ecfe76191100067f65191100067c6519110036be6419110006bd641911003cff76d5110004fe76d5110004fd76d511003cfc76d51100067f65d511003e7c65d511001df671d5110005f571d5110034ff7695110004fe7695110004fd7695110034fc76951100067f659511003e7c65951100073f549511001df67195110005f57195110004ff7655110004fe7655110004fd7655110004fc76551100067f655511003e7c6555110034ff7615110004fe7615110004fd7615110034fc76151100067f651511003e7c651511001df67115110005f5711511000dfa7015110005f97015110014fe76d8d100067f65d8d100067c65d8d10026de63d8d1003cfe75d8d10004fd75d8d10034fe74d8d10004fd74d8d10026dc43d8d1002cfe72d8d10004fd72d8d10026dc32d8d1001cfe71d8d1000cfd71d8d1001cfc71d8d10026df31d8d1001cff70d8d1000cfe70d8d1001cfd70d8d1000cfc70d8d100c6df30d8d100c6dd30d8d100057f7558d100057c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10026dc6358d10005ef7258d10005ec7258d1025df77158d10004ff7558d100067f7558d100047f7558d1003cfc7558d100067c7558d1003c7c7558d10004ff7458d10
  | 4 => 0x471000df6705471000df4705471001df77650710006f77650710005f77550710005f5755071001fb7745071001fb76450710036f6645071001ef4645071001fb46450710007b75450710007b45450710005f77350710007b74350710007b54350710007e77250710275f47250710007e47250710005e47250710007b74250710007b5425071000df6705071000df470507100dfb740507100dfb5405071001df7764c71027ef7764c710005f7754c710005f5754c710005f7744c710005f5744c71001fd7734c710016f6634c71001ef4634c710275f4724c710047d7324c710007d5324c71000df6704c71000df4704c71001df576c8710276f576c8710275f775c8710005f575c871024ef665c871001ef465c8710275f774c8710005f574c8710275f773c8710005f573c871001fe672c871001ef762c8710276f562c871000df670c871000df470c871003cfe76d9510034fe74d9510004fd74d9510014fe73d9510004fd73d9510014fc73d95100067e53d95100067c53d951002cfe72d9510004fd72d951001cfe71d951001cfc71d951001cff70d951000cfe70d951001cfd70d951000cfc70d951012e7f50d951012e7d50d951003c7e76d95100067e63d95100067c63d951012f7771d951012f7a20d951026f7b10d951012f7610d951012f7410d951012f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067c32d951012e7f71d951026e7e71d951012e7d71d951012e7c71d951026e7e41d951026e7c41d95100067f31d951026e7e31d951026e7c31d951026e7e21d951026e7c21d951012e7f70d951012e7e70d951012e7d70d951012e7c70d951012e7f40d951012e7e40d951012e7d40d951012e7c40d951012e7f30d951012e7e30d951012e7d30d951012e7c30d951012e7f20d951012e7e20d951012e7d20d951012e7c20d951012e7f10d951012e7e10d951012e7c10d95100067f659951011df5719951013df771595100067f7559510004ff7459510034fc7459510004ff7359510014fe7359510014fc7359510004ff725951002cfc725951013cff7159510006f7715951011cff7059510006fb705951012cfe761951003e7e65195100067d651951012d7e76195100067e761951012c7e76195100067e63195100067c631951010f75711951010f7a20195102677b101951010f76101951010f74101951010f78101951003e7f741951003e7e741951003e7d741951003e7c741951003e7f731951003e7e731951003e7d731951003e7c73195100067e43195100067c431951003e7f721951003e7e721951003e7d721951003e7
  | 5 => 0x1df67115310005f57115310004ff7558f1003cfc7558f10004ff7458f10034fc7458f1001edf7358f10046dc5358f10046de4358f10004ff7258f1002cfc7258f10046df3258f1001cff7158f1000cfe7158f1001cfd7158f1000cfc7158f1001ede3158f1001edc3158f100bedf3058f100bedd3058f1003cff76d4f1001cfe76d4f10004fd76d4f1001cfc76d4f102a67f65d4f1003e7c65d4f10016de63d4f10006dd63d4f100475e53d4f1001df671d4f10005f571d4f102a77651d4f10004ff7654f1001cfe7654f10004fd7654f1001cfc7654f1029e7f6554f1003e7c6554f1001df67154f1029f765154f10034ff76d0f1001cfe76d0f10004fd76d0f1001cfc76d0f10036be64d0f10006bd64d0f1001df671d0f10005f571d0f10004ff7650f1001cfe7650f10004fd7650f1001cfc7650f10036be6450f10006bd6450f10016de6350f10006dd6350f1001df67150f10004ff7558b1003cfc7558b10004ff7458b10006bf7458b10004bf7458b10034fc7458b10006bc7458b10034bc7458b10004ff7358b10014fe7358b10014fc7358b1001eef7258b1001cff7158b1000cfe7158b1001cfd7158b1000cfc7158b1001ef47158b1000cf47158b1001eee2158b1001eec2158b1001ef42158b1008eef2058b1008eed2058b1001efa1058b1001ef91058b1003cff76d4b1001cfe76d4b10004fd76d4b1001cfc76d4b1003e7e65d4b100067d65d4b1001df671d4b10005f571d4b1002cff7694b1001cfe7694b10004fd7694b1001cfc7694b1001df47194b10004ff7654b1001cfe7654b10004fd7654b1001cfc7654b1003e7e6554b100067d6554b10005bf7454b10005bc7454b10005f77154b1001df47154b1002cff7614b1001cfe7614b10004fd7614b1001cfc7614b1001df67114b10005f57114b10034ff76d0b1001cfe76d0b10004fd76d0b1001cfc76d0b10036be64d0b10006bd64d0b1001df671d0b10005f571d0b10297e421d0b1002cff7690b1001cfe7690b10004fd7690b1001cfc7690b1028ebf6490b10036bc6490b1001df47190b1028fb64190b10004ff7650b1001cfe7650b10004fd7650b1001cfc7650b10036be6450b10006bd6450b10005f77150b1001df47150b1002cff7610b1001cfe7610b10004fd7610b1001cfc7610b100057e7510b100057d7510b10286bf6410b10036bc6410b1001df67110b10005f57110b10287b64110b10287e42110b1002cff768cb1001cfe768cb10004fd768cb1001cfc768cb1001df4718cb10004ff764cb1001cfe764cb10004fd764cb1001cfc764cb10016de634cb10006dd634cb10005f7714cb1001df4714cb1001df77654710006f7765471001f77755471003ef6655471001ef46554710005f77454710005f77354710275f4725471000777525471000775525
  | 6 => 0xc634c92004fcf314c920007eb704c92000dee704c92000dec704c92014fe8704c92002eef604c92002feb604c92014fea104c92001cfe76d852003cfe75d8520004fd75d8520034fe74d8520004fd74d8520014fe73d8520004fd73d8520014fc73d852000cfe70d852002cfd70d852000cfc70d85200aef710d8520006f761985200057f75585200057c7558520005bf7458520005bc7458520005df735852004ddc7358520005be7418520005bd741852001ef66118520006f56118520004fe76d4520004fd76d452003cfc76d452002dee72d4520005ed72d45200076d52d4520006f761d452001ef461d4520004fe7694520004fd769452001cfc76945200067f659452003e7c6594520005be7494520005bd749452000dfa7094520005f97094520004ff7654520004fe7654520004fc76545200076d5254520004fe7614520004fd761452001cfc76145200067f651452003e7c651452002dee7214520005ed7214520006f7611452001ef4611452000dfa7014520005f97014520004fe76d0520004fd76d0520034fc76d0520036be64d0520006bd64d0520004fe7690520004fd769052001cfc7690520006bf6490520036bc649052000dfa7090520005f97090520004ff7650520004fe7650520004fc7650520036be6450520006bd6450520005ef725052002dec7250520004fe7610520004fd761052001cfc7610520006bf6410520036bc641052000dfa7010520005f97010520004fe768c520004fd768c52001cfc768c520006df638c520016dc638c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c520007cd324c52000cfe7688520006f7618852001ef4618852000dfa7088520005f9708852000cfc7648520005bf7448520005bc7448520006f7614852001ef46148520005fb704852000df8704852001e7f7559710004ff7459710034fc7459710004ff7359710014fe7359710014fc7359710004ff725971002cfc725971001cff715971000cfe715971001cfd715971000cfc715971001e7e515971001e7c515971011e7f505971011e7d5059710004ff755931003cfc755931001ebf7459310004ff7359310014fe7359310014fc7359310004ff725931002cfc725931001cff715931000cfe715931001cfd715931000cfc715931001ebe415931001ebc41593100debf40593100debd405931003cff76d531001cfe76d5310004fd76d531001cfc76d5310036be64d5310006bd64d531001df671d5310005f571d5310034ff769531001cfe7695310004fd769531001cfc76953100073f549531001df67195310005f57195310004ff765531001cfe7655310004fd765531001cfc765531001df67155310034ff761531001cfe7615310004fd761531001cfc7615310036be6415310006bd6415310
  | 7 => 0x5120004fd7615120034fc7615120006bf6415120036bc641512002dee7215120005ed7215120014fe76d8d2004ede63d8d2003cfe75d8d20004fd75d8d20034fe74d8d20004fd74d8d2004edc53d8d2004ede43d8d2002cfe72d8d2000cfd72d8d2002cfc72d8d2004edf32d8d2001cfe71d8d20004fd71d8d2004edc31d8d2002cff70d8d2002cfd70d8d20156df30d8d20156dd30d8d2004edc6358d202b5ef7258d20004ff7558d2003cfc7558d20004ff7458d20034fc7458d20154ff7358d20006df7358d202b4ff7258d20006ef7258d20004ff7158d2001cfc7158d2014cff7058d20006fb7058d2003cff76d4d20004fe76d4d20004fd76d4d2003cfc76d4d2003e7e65d4d200067d65d4d20006df63d4d20016dc63d4d2004f5e53d4d2002dee72d4d20005ed72d4d20004ff7654d20004fe7654d20004fd7654d20004fc7654d2003e7e6554d200067d6554d20034ff76d0d20004fe76d0d20004fd76d0d20034fc76d0d20006bf64d0d20036bc64d0d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d20036bc6450d20006df6350d20016dc6350d2000cfe76d492000cfc76d49200067f65d492003e7c65d492000dfa70d4920005f970d492019dee769492002eee76949201aded759492003eee659492003eec6594920005ed739492000dee709492000dec709492002eef609492002feb60949201bfea109492003cff765492000cfe76549201acfd765492000cfc76549200067f655492003e7c6554920005bf7454920005bc7454920005f77154920005f47154920005fb705492000df8705492000dec765492003eec765492000cec765492002def755492002f6f75549200076f655492003eee655492003eec65549200076c6554920007af7454920007ac74549200076f54549200076d5454920005ef73549200076f53549200076d5354920007e77154920007e47154920007eb705492000dee705492000dec70549201afe8705492002eef605492002feb60549201af6e50549201af6c50549201afea105492000cfe76d092000cfc76d0920006bf64d0920036bc64d092000dfa70d0920005f970d0920034ff765092000cfe765092016cfd765092000cfc7650920006bf6450920036bc6450920005fb705092000df870509202adee768c92002eee768c92002def758c920005ed758c92014ded738c920016ee638c920016ec638c92000dee708c92000dec708c92002eef608c92002feb608c920157ea108c920014ff764c92000cfe764c92014cfd764c92000cfc764c920006df634c920016dc634c920005fb704c92000df8704c92000dec764c920016ec764c92000cec764c920005ef754c920005ed754c92002def734c92002fcf734c920007cf634c920016ee634c920016ec634c92004fc
  | 8 => 0x3e7e65d47200067d65d472002dee72d4720005ed72d47200076d52d472001cff769472002cfe7694720004fd769472003e7e65947200067d6594720005be7494720005bd7494720004ff7654720004fd765472002cfc765472003e7e65547200067d65547200076d525472001cff761472002cfe7614720004fd761472003e7e65147200067d651472002dee7214720005ed7214720034ff76d072002cfe76d0720004fd76d07200067e65d07200067d65d0720036be64d0720006bd64d072001cff769072002cfe7690720004fd76907200067e65907200067d6590720004ff7650720004fd765072002cfc76507200067e65507200067d6550720036be6450720006bd6450720005ef725072002dec725072001cff761072002cfe7610720004fd76107200067e65107200067d651072001cff768c72002cfe768c720004fd768c7200067e658c7200067d658c720004ff764c720004fd764c72002cfc764c7200067e654c7200067d654c720016de634c720006dd634c720007cd324c72003cfe76d9520034fe74d9520004fd74d9520014fe73d9520004fd73d9520014fc73d952002cfe72d952002cfc72d952001cfe71d9520004fd71d952002cff70d952002cfd70d95201be7f50d95201be7d50d95200067f65995201aded7299520005bf7459520005bc7459520005df735952004ddc73595201cdef7259520005f77159520005f471595200067f7559520004ff7459520006bf7459520004bf7459520034fc7459520006bc7459520034bc7459520004ff7359520006df7359520004df7359520014fe7359520014fc7359520006dc7359520014dc73595201ccff7259520006ef7259520004ff7159520006f77159520004f7715952001cfc7159520006f4715952001cf471595201acff7059520006fb70595201ae7e50595201ae7c50595201bcfe761952003e7e65195200067d6519520034fe76d912003cfe75d9120004fd75d9120014fe73d9120004fd73d9120014fc73d912002cfe72d912002cfc72d912001cfe71d9120004fd71d912002cff70d912002cfd70d912017ebf40d912017ebd40d9120006bf649912004dde7399120005dd739912016ded729912018def7259120004ff755912003cfc7559120006bf7459120004ff7359120014fe7359120014fc735912018cff7259120006ef72591202bebe42591202bebc4259120004ff715912001cfc715912016cff7059120006fb705912017cfe7619120036be6419120006bd641912003cff76d5120004fe76d5120004fd76d512003cfc76d5120006bf64d5120036bc64d512002dee72d5120005ed72d5120034ff7695120004fe7695120004fd7695120034fc76951200073f5495120004ff7655120004fe7655120004fd7655120004fc7655120034ff7615120004fe761
  | 9 => 0xc21597201ae7f70597201ae7e70597201ae7d70597201ae7c70597201ae7f40597201ae7e40597201ae7d40597201ae7c40597201ae7f30597201ae7e30597201ae7d30597201ae7c305972002e7f205972002e7e205972002e7d205972002e7c20597201ae7f10597201ae7e10597201ae7d10597201ae7c1059720004ff755932003cfc755932002ebf7459320004ff7359320014fe7359320014fc7359320006be4359320006bc435932002cff725932000cfe725932002cfd725932000cfc725932002ebe425932002ebc4259320004ff715932001cfc715932016ebf405932016ebd405932003cff76d532002cfe76d5320004fd76d532002cfc76d532003e7e65d53200067d65d532002dee72d5320005ed72d5320034ff769532002cfe7695320004fd769532002cfc769532003e7e65953200067d65953200073f5495320004ff765532002cfe7655320004fd765532002cfc765532003e7e65553200067d6555320034ff761532002cfe7615320004fd761532002cfc761532003e7e65153200067d651532002dee7215320005ed7215320004ff7558f2003cfc7558f20004ff7458f20034fc7458f2002edf7358f20056dc4358f2002cff7258f2000cfe7258f2002cfd7258f2000cfc7258f2002ede3258f2002edc3258f20004ff7158f2001cfc7158f20056df3158f2014edf3058f2014edd3058f2003cff76d4f2002cfe76d4f20004fd76d4f2002cfc76d4f2003e7e65d4f200067d65d4f200575e53d4f2002dee72d4f20005ed72d4f20004ff7654f2002cfe7654f20004fd7654f2002cfc7654f2003e7e6554f200067d6554f2002dee7254f20005fb7054f2000df87054f20034ff76d0f2002cfe76d0f20004fd76d0f2002cfc76d0f200067e65d0f200067d65d0f202d6bf64d0f20036bc64d0f20016de63d0f20006dd63d0f20004ff7650f2002cfe7650f20004fd7650f2002cfc7650f200067e6550f200067d6550f202cebf6450f20036bc6450f2002def7654b20006ef7654b2002f6f7554b2003eee6554b2002f6e6554b2003e6e6554b2002f6d6554b2002eec6554b20007af7454b20007ac7454b200076f5454b200076d5454b20005ef7354b200076f5354b200076d5354b20007e77154b20007e47154b2000dee7054b2000dec7054b201af6e5054b201af6c5054b2002def764cb202c6ef764cb20005ef754cb20005ed754cb2002f6e654cb2002f6d654cb2002fcf734cb20016ee634cb2002eec634cb20057cf314cb2000dee704cb2000dec704cb20004ff755872003cfc7558720004ff7458720034fc7458720004ff7358720014fe7358720014fc735872000cfc725872002ef7715872002ef7215872002ef4215872002efa205872002ef9205872008ef7105872003cff76d472002cfe76d4720004fd76d4720
  | 10 => 0x4530004fd769453001cfc76945300067f659453003e7c6594530005be7494530005bd74945300075d5394530004ff7654530004fe7654530004fc7654530004fe7614530004fd761453001cfc76145300067f651453003e7c6514530015de7314530005dd73145300075d531453000dfa7014530005f97014530004fe76d0530004fd76d0530034fc76d0530036be64d0530006bd64d0530004fe7690530004fd769053001cfc7690530006bf6490530036bc6490530004ff7650530004fe7650530004fc7650530036be6450530006bd6450530005ef7250530005ec7250530004fe7610530004fd761053001cfc7610530006bf6410530036bc6410530004fe76c8530004fd76c853002cfc76c8530004fe7688530004fd768853001cfc7688530006ef628853002eec6288530004ff7648530004fe7648530004fc7648530005bf7448530005bc7448530004fe7608530004fd760853001cfc76085300057e75085300057d7508530005be7408530005bd7408530015de7308530005dd7308530006ef620853002eec620853000dfa7008530005f9700853003e7f749972003e7e749972003e7d749972003e7c749972003e7f739972003e7e739972003e7d739972003e7c73997200067e43997200067c439972002e7f729972002e7e729972002e6e729972002e7d729972002e7c729972002e7f429972002e7e429972002e7d429972002e7c429972002e7f329972002e7e329972002e7d329972002e7c329972003e7f719972003e7e719972003e7d719972003e7c71997200067f31997200067c319972002e7f219972002e7e219972002e7d219972002e7c219972003e7f709972003e7e709972003e7d709972003e7c70997201ce7f40997201ce7e40997201ce7d40997201ce7c40997201ce7f30997201ce7e30997201ce7d30997201ce7c309972002e7f209972002e7e209972002e7d209972002e7c20997201ce7f10997201ce7e10997201ce7d10997201ce7c109972002e7f7559720004ff7459720034fc7459720004ff7359720014fe7359720014fc73597200067e53597200067c535972002cff725972000cfe725972002cfd725972000cfc725972002e7e525972002e7c5259720004ff715972001cfc71597201ae7f50597201ae7d50597200067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c73597200067e43597200067c435972002e7f725972002e7e725972002e7d725972002e7c725972002e7f425972002e7e425972002e7d425972002e7c425972002e7f325972002e7e325972002e7d325972002e7c32597200067f71597200067e71597200067d71597200067c71597200067f31597200067c315972002e7f215972002e7e215972002e7d215972002e7
  | 11 => 0x67c755913003c7c7559130006bf74591301e4ff7359130006df7359130004ff725913002cfc7259130004ff715913001cfc71591301dcff7059130006fb70591302ecfe7619130036be6419130006bd641913003cff76d5130004fe76d5130004fd76d513003cfc76d5130006bf64d5130036bc64d5130015de73d5130005dd73d5130034ff7695130004fe7695130004fd7695130034fc76951300067f659513003e7c65951300073f5495130004ff7655130004fe7655130004fd7655130004fc7655130034ff7615130004fe7615130004fd7615130034fc76151300067f651513003e7c6515130006bf6415130036bc6415130015de7315130005dd731513000ddc7654d3003edc7654d3000cdc7654d30015df7554d300175f7554d300075f6554d3003ede6554d3003edc6554d300075c6554d30007db7054d3000dde7054d3000ddc7054d301efd87054d3000dd87054d30016df6054d30017db6054d301ef5f5054d301ef5d5054d3002cfe76d8930005be74d8930005bd74d893003cfe75d8930004fd75d8930034fe74d8930006be74d8930034be74d8930004fd74d8930006bd74d8930004bd74d893000cfd73d89302e6ee32d89302e6ed32d893001cfe71d8930004fd71d8930014fd70d89302b6ef20d89300057e75989300057d7598930005be7498930005bd7498930006ef629893004df97098930055fb705893002eee6218930006ed6218930004fe76d4930004fd76d493003cfc76d49300067f65d493003e7c65d4930015de73d4930005dd73d49300075d53d4930004fe7694930004fd769493002cfc7694930004ff7654930004fe7654930004fc76549300067f655493003e7c6554930005bf7454930005bc74549300075d5354930005f77154930005f47154930004fe7614930004fd761493002cfc7614930015de7314930005dd7314930004fe76d0930004fd76d0930034fc76d0930006bf64d0930036bc64d0930004fe7690930004fd769093002cfc7690930036be6490930006bd6490930004ff7650930004fe7650930004fc7650930006bf6450930036bc6450930004fe7610930004fd761093002cfc76109300057e75109300057d7510930036be6410930006bd6410930015de7310930005dd731093000dfa7010930005f9701093001cfe76d853003cfe75d8530004fd75d8530034fe74d8530004fd74d853000cfd73d853002cfe72d8530004fd72d85302def631d85302def531d8530014fd70d853025ef710d8530006f76198530025f970985300057f75585300057c7558530005bf7458530005bc7458530005ef7258530005ec7258530045fb7058530005be7418530005bd741853001ef66118530006f56118530004fe76d4530004fd76d453003cfc76d4530015de73d4530005dd73d4530004fe769
  | 12 => 0xc65d0540005bd73d0540006bf63d05402bdbe72d0540006bf62d054001ebe61d054001ebc61d054000dbe70d054000dbc70d0540036bf60d0540037bb60d054000cfe76905400ddbd7490540006f7619054001ef4619054000dfa7090540005f9709054000cfc7650540005ef7250540005ec7250540006f7615054001ef46150540037b44150540005fb705054000df8705054000dbc765054001ebc765054000cbc7650540005bf7550540005bd755054030ebe655054030ebc6550540005bf7350540006bf6350540007af72505402bdbc7250540007ac7250540005ac7250540006bf6250540035bf7150540037b77150540007b7615054001ebe615054001ebc6150540007b46150540007bb705054000dbe705054000dbc70505400dfb87050540036bf6050540037bb6050540004fe768c540004fd768c54001cfc768c540035be748c540005bd748c540006df638c540016dc638c54000dfa708c540005f9708c540004ff764c540004fe764c540004fc764c540035be744c540005bd744c540004fe76c8540004fd76c854002cfc76c85402bdbf74c8540035bc74c8540004fe7688540004fd768854001cfc7688540035be7488540005bd7488540006ef628854002eec6288540007ac4288540004ff7648540004fe7648540004fc7648540005bf7448540035bc7448540004fe7608540004fd760854001cfc76085400057e75085400057d7508540035be7408540005bd740854005dde7308540005dd7308540006ef620854002eec62085402bfac420854000dfa7008540005f9700854003cfe76d9530034fe74d9530004fd74d953000cff73d9530014fe73d953000cfd73d9530014fc73d95303067f53d95303067d53d953002cfe72d9530004fd72d953001cfe71d9530004fd71d9530014ff70d9530014fd70d95302fe7f50d95302fe7d50d95301ecfd76995300067f65995301eddd739953006df9709953003cff7659530005bf7459530005bc74595301f5df7359530075fb70595300067f7559530004ff7459530006bf7459530004bf7459530034fc7459530006bc7459530034bc74595301f4ff7359530006df7359530004ff725953002cfc7259530004ff715953001cfc71595301ecff7059530006fb70595302fcfe761953003e7e65195300067d6519530034fe76d913003cfe75d9130004fd75d913000cff73d9130014fe73d913000cfd73d9130014fc73d91302f6bf43d91302f6bd43d913002cfe72d9130004fd72d913001cfe71d9130004fd71d9130014ff70d9130014fd70d91302eebf40d91302eebd40d91301dcfd7699130006bf64991301dddd739913005df97099130034ff76591300057f75591300057c75591301e5df7359130065fb7059130004ff75591300067f75591300047f755913003cfc7559130
  | 13 => 0xd4005f9c6350d400169c6350d402bdbc7250d402cebc6250d40005bf7150d40007bb7050d4000dbe7050d4000dbc7050d401dfb87050d40036bf6050d40037bb6050d4002cfe76d894003cfe75d8940004fd75d894018ebd74d8940014fe73d8940004fd73d8940014fc73d894001cfe71d8940004fd71d8940034fd70d894018eef20d89400057e75989400057d759894005dde7398940005dd7398940006ef629894002eee6218940006ed6218940004fe76d4940004fd76d494003cfc76d49400067f65d494003e7c65d4940035be74d4940005bd74d49400073d54d4940004fe7694940004fd769494002cfc7694940004ff7654940004fe7654940004fc76549400067f655494003e7c6554940005bf7454940035bc74549400073d5454940005f77154940005f47154940004fe7614940004fd761494002cfc7614940035be7414940005bd741494000cfe7690940006ef629094002eec629094000dfa7090940005f9709094000dbe769094017ebe769094000cbe76909402bdbf7590940005bd7590940326be6590940326bc6590940005bd7390940006bf6390940035be72909402bebf6290940007af62909402bfac6290940005bd719094028ebc619094000dbe709094017fba709094000dba70909402bfb9709094000dbc7090940036bf6090940037bb609094000cfc7650940006ef625094002eec6250940005fb705094000df87050940037b8405094018dbe7610940036be7610940035bf75109400373e7510940005bd75109400373d75109400053d751094031ebe651094031ebc6510940005bd7310940006bf631094017dbe7210940037ae72109402bebf6210940005bd7110940286bc611094000dbe701094000dbc7010940036bf6010940037bb6010940004fe768c940004fd768c94002cfc768c9402bdbf748c940035bc748c940004ff764c940004fe764c940004fc764c940005bf744c940035bc744c940006df634c940016dc634c94001cfe76d854003cfe75d8540004fd75d8540014fe73d8540004fd73d8540014fc73d8540006bf43d8540006bd43d854002cfe72d8540004fd72d8540034fd70d85400fef710d8540006f761985400057f75585400057c7558540005df735854005ddc7358540005ef7258540005ec725854001ef66118540006f56118540004fe76d4540004fd76d454003cfc76d4540035be74d4540005bd74d4540004fe7694540004fd769454001cfc76945400067f659454003e7c6594540035be7494540005bd7494540004ff7654540004fe7654540004fc7654540004fe7614540004fd761454001cfc76145400067f651454003e7c6514540035be7414540005bd741454000dfa7014540005f970145400cdbe76d0540036be76d0540035bf75d0540005bd75d0540316be65d0540316b
  | 14 => 0x34fe76c8740004fd76c8740335bf74c8740035bc74c874001cff7688740034fe7688740004fd7688740035be7488740005bd748874033fac4288740004ff7648740004fd7648740034fc7648740005bf7448740035bc744874001cff7608740034fe7608740004fd76087400057e75087400057d7508740035be7408740005bd7408740065de7308740005dd7308740337ac420874000dfa7008740005f9700874003cfe76d9540034fe74d9540034fc74d9540014fe73d9540004fd73d9540014fc73d95400067e53d95400067c53d954002cfe72d9540004fd72d954001cfe71d9540004fd71d9540034ff70d9540034fd70d954021e7f50d954021e7d50d95400067f659954020dbd749954022dbf7459540005df735954005ddc73595400067f755954022cff7459540006bf7459540004ff7359540006df7359540004df7359540014fe7359540014fc7359540006dc7359540014dc7359540004ff725954002cfc7259540004ff715954001cfc715954020cff7059540006fb705954021cfe761954003e7e65195400067d651954000cfe76d514000cfc76d51400067f65d514003e7c65d51400373e54d514000dfa70d5140005f970d51401fdbe7695140036be769514020dbd759514003ebe659514003ebc6595140005bd73951402bdbe7295140005bd719514000dbe709514000dbc7095140036bf6095140037bb609514003cff765514000cfe765514020cfd765514000cfc76551400067f655514003e7c6555140005fb705514000df8705514000dbc765514003ebc765514000cbc7655140035bf75551400373f75551400073f655514003ebe655514003ebc65551400073c6555140005bf73551402bdbc7255140005bf7155140007bb705514000dbe705514000dbc705514020fb87055140036bf6055140037bb6055140014fe76d8d4005ede63d8d4003cfe75d8d40004fd75d8d4000cfd74d8d40014fc74d8d4005edc53d8d4005ede43d8d4002cfe72d8d40004fd72d8d4005edf32d8d4001cfe71d8d40004fd71d8d4005edc31d8d40034fd70d8d401e6df30d8d400057f7558d400057c7558d4005edc6358d40004fe76d4d40004fd76d4d4003cfc76d4d40035be74d4d40005bd74d4d40006df63d4d40016dc63d4d4005f5e53d4d40004ff7654d40004fe7654d40004fc7654d4032dbe76d0d40036be76d0d40035bf75d0d40005bd75d0d401ddbd73d0d40016be63d0d40016bc63d0d402bdbe72d0d402d6bc62d0d40005bd71d0d4000dbe70d0d4000dbc70d0d40036bf60d0d40037bb60d0d4000cfc7650d40006df6350d40016dc6350d40005fb7050d4000df87050d4000dbc7650d40016bc7650d4000cbc7650d40005bf7550d40005bd7550d40035bf7350d400379f7350d400079f6350d40016be6350d40016bc635
  | 15 => 0xc4258f40066dc3258f40004ff7158f4001cfc7158f40036bf4158f40066df3158f401dedf3058f4003cff76d4f40034fe76d4f40004fd76d4f40035be74d4f40005bd74d4f400675e53d4f40004ff7654f40004fd7654f40034fc7654f40035be7454f40005fb7054f4000df87054f40035bf7650f40346bf7650f40005bf7550f40005bd7550f400379f7350f40016be6350f40016bc6350f40335bc7250f402cebe6250f40005bf7150f4000dbe7050f4000dbc7050f40004ff7558b4003cfc7558b4000cfc7458b40036bc7458b4000cbc7458b40004ff7358b40014fe7358b40014fc7358b40036ef7258b40036ef4258b40036bc4258b40036ec4258b40004ff7158b4001cfc7158b40036bf4158b4016eef2058b4003cff76d4b40034fe76d4b40004fd76d4b4003e7e65d4b400067d65d4b40035be74d4b40005bd74d4b400073d54d4b4002cff7694b40034fe7694b40004fd7694b40035bc7494b40004ff7654b40004fd7654b40034fc7654b4003e7e6554b400067d6554b40005bf7454b40035bc7454b400073d5454b40005f77154b40005f47154b4002cff7614b40034fe7614b40004fd7614b40035be7414b40005bd7414b40035bd7690b40336bd7690b40335bf7590b40005bd7590b40326be6590b40036bc6590b40005bd7390b40006bd6390b40037ae7290b40036bf6290b40336bd6290b40005bd7190b4028ebe6190b4000dbe7090b4000dbc7090b4002cff768cb40034fe768cb40004fd768cb40335bf748cb40035bc748cb40016de638cb40006dd638cb40004ff764cb40004fd764cb40034fc764cb40005bf744cb40035bc744cb40004ff755874003cfc755874000cfc7458740004ff7358740014fe7358740014fc7358740036bf4358740006bd4358740004ff725874002cfc7258740036f77158740036f74158740036f441587400def7105874003cff76d4740034fe76d4740004fd76d4740035be74d4740005bd74d474001cff7694740034fe7694740004fd769474003e7e65947400067d6594740035be7494740005bd7494740004ff7654740004fd7654740034fc7654740035be745474001cff7614740034fe7614740004fd761474003e7e65147400067d6514740035be7414740005bd7414740035bf7650740006bf7650740005bf7550740005bd755074030ebe6550740036bc6550740005bf7350740006bd6350740007af7250740335bc7250740007ac7250740005ac7250740006bd6250740037b77150740037b7615074001ebe615074001ebc6150740037b4615074000dbe705074000dbc705074001cff768c740034fe768c740004fd768c740035be748c740005bd748c740004ff764c740004fd764c740034fc764c740035be744c740005bd744c740016de634c740006dd634c74002cff76c8740
  | 16 => 0x8950005df735895006ddc7358950005f77158950005f4715895002eee6218950006ed621895000cfe7694950006ef629495002eec629495000dfa7094950005f9709495000cfc76549501ae7f6554950005bf7454950005bc7454950006ef625495002eec6254950005f77154950005f47154950005fb705495000df87054950004fe76d0950004fd76d0950034fc76d0950004fe7690950004fd769095002cfc7690950006bf6490950036bc6490950004ff7650950004fe7650950004fc7650950004fe7610950004fd761095002cfc761095003d7e75109500057d7510950006bf6410950036bc6410950004fe768c950004fd768c95002cfc768c950006df638c950016dc638c950004ff764c950004fe764c950004fc764c95001cfe76d8550034fe74d8550004fd74d8550014fe73d8550004fd73d8550014fc73d855002cfe72d8550004fd72d855003cfd70d855013ef710d855012e7f6598550005be7498550005bd749855006dde7398550005dd7398550006f7619855010e7f651855001ef66118550006f5611855000cfe769455012e7f6594550005be7494550005bd7494550006f7619455001ef4619455000dfa7094550005f9709455000cfc7654550006f7615455001ef46154550005fb705455000df8705455003f785054550004fe76d0550004fd76d0550034fc76d0550006bf64d0550036bc64d0550004fe7690550004fd769055001cfc7690550004ff7650550004fe7650550004fc7650550006bf6450550036bc6450550005ef7250550005ec7250550004fe7610550004fd761055001cfc761055000dfa7010550005f97010550004fe768c550004fd768c55001cfc768c550004ff764c550004fe764c550004fc764c550006df634c550016dc634c550004fe76c8550004fd76c855002cfc76c8550006f761c855001ef461c8550004fe7688550004fd768855001cfc7688550004ff7648550004fe7648550004fc7648550005bf7448550005bc7448550004fe7608550004fd760855001cfc760855003d7e75085500057d7508550005be7408550005bd740855006dde7308550005dd7308550006f7610855001ef4610855000dfa7008550005f970085500367f7559740034ff745974000cfe7459740034fd745974000cfc74597400367e54597400367c5459740004ff7359740014fe7359740014fc7359740004ff725974002cfc7259740004ff715974001cfc715974020e7f505974020e7d5059740035bf7655340006bf76553400373f755534003ebe6555340036bc6555340005bf7355340335bc7255340005bf715534000dbe705534000dbc7055340004ff7558f4003cfc7558f4000cfe7458f40014fd7458f4000cfc7458f40036df7358f40036df4358f40036dc4358f40004ff7258f4002cfc7258f40036b
  | 17 => 0x2cff768cb5003cfe768cb50004fd768cb50004ff764cb50004fd764cb5003cfc764cb50005fb704cb5000df8704cb5000cfc7558750004ff7458750034fc7458750004ff7358750014fe7358750014fc7358750004ff725875002cfc725875003ef7715875003ef7515875003ef4515875011ef71058750034ff76d075003cfe76d0750004fd76d0750036bc64d075001cff769075003cfe7690750004fd7690750004ff7650750004fd765075003cfc7650750005ef7250750005ec725075001cff761075003cfe7610750004fd761075001cff768c75003cfe768c750004fd768c75000dfa708c750005f9708c750004ff764c750004fd764c75003cfc764c75002cff76c875003cfe76c8750004fd76c875001cff768875003cfe7688750004fd7688750004ff7648750004fd764875003cfc7648750005bf7448750005bc744875001cff760875003cfe7608750004fd760875003d7e75087500057d7508750005be7408750005bd7408750075de7308750005dd730875001ef4610875000dfa7008750005f97008750034fe76d9150014fe73d9150004fd73d9150014fc73d9150006be43d9150006bc43d915002cfe72d9150004fd72d915001cfe71d9150004fd71d915003cfd70d915022ebf40d9150006bf6499150005df735915006ddc7359150036be6419150006bd641915000cfe7695150006bf6495150036bc649515003f3f549515000dfa7095150005f9709515000cfc7655150006bf6455150036bc6455150005fb705515000df87055150014fe76d8d5006ede63d8d5000cfd75d8d50014fc75d8d50034fe74d8d50004fd74d8d5006ede53d8d5006edc43d8d5002cfe72d8d50004fd72d8d5006edc32d8d5001cfe71d8d50004fd71d8d5006edf31d8d5003cfd70d8d501f6df30d8d50005bf7458d50005bc7458d5006edc6358d5034d7e76d4d5003e7e76d4d501ed7d73d4d500167e63d4d500167c63d4d502a67c61d4d5000d7e70d4d5000d7c70d4d5003e7f60d4d5003f7b60d4d5000cfc7654d50006df6354d50016dc6354d5003f5c5354d50005fb7054d5000df87054d5000d7c7654d500167c7654d5000c7c7654d5003d7f7354d5003f5f7354d500075f6354d500167e6354d500167c6354d5006f5c6354d5029e7c6154d500077b7054d5000d7e7054d5000d7c7054d501ef787054d5003e7f6054d5003f7b6054d501ef5f3054d50004fe76d0d50004fd76d0d50034fc76d0d50006df63d0d50016dc63d0d50004ff7650d50004fe7650d50004fc7650d5002cfe76d8950034fe74d8950004fd74d8950014fe73d8950004fd73d8950014fc73d89500067f53d89500067d53d895001cfe71d8950004fd71d895003cfd70d89501ce7e50d89501ce7c50d89501ceef20d8950006ef6298950005bf7458950005bc745
  | 18 => 0x662d442135f7752d442135f7552d4421007e742d442135fe442d4421005f570d442101ff260d442101ff160d4421004ff755802103cfc7558021004ff7458021034fc7458021004ff7358021014fe7358021014fc735802100cfd725802100cfd715802101cff705802101efb705802107efa505802107ef8505802107efa405802107ef84058021006fb305802107efa305802107ef8305802102efb205802102ef8205802101efb105802101ef81058021006fb7558021006fa7558021006f97558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb5458021006fa5458021006f95458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f8435802102efb725802102efa725802102ef8725802102efb525802102efa525802102ef9525802102ef8525802102efb425802102efa425802102ef9425802102ef8425802102efb325802102efa325802102ef9325802102ef8325802101efb715802101efa715802101ef8715802101efb515802101efa515802101ef9515802101ef8515802101efb415802101efa415802101ef9415802101ef8415802101efb315802101efa315802101ef9315802101ef8315802101efb215802101efa215802101ef9215802101ef8215802100cfc755935003ebf745935003ebf545935003ebc5459350004ff7359350014fe7359350014fc7359350004ff725935002cfc7259350004ff715935001cfc715935020ebf405935000cfe7558f50014fd7558f5000cfc7558f50004ff7458f50034fc7458f5003edf7358f5003edf5358f5003edc5358f50004ff7258f5002cfc7258f50004ff7158f5001cfc7158f501eedf3058f5003d7f7654f503567f7654f5003f5f7354f5003f5f6354f500167e6354f500167c6354f5003f5c6354f5029e7e6154f5000d7e7054f5000d7c7054f501ef5f3054f50034ff76d0f5003cfe76d0f50004fd76d0f50004ff7650f50004fd7650f5003cfc7650f50005fb7050f5000df87050f5000cfc7558b50004ff7458b50006bf7458b50004bf7458b50034fc7458b50006bc7458b50034bc7458b50004ff7358b50014fe7358b50014fc7358b5003e7f5358b500067d5358b5003eef7258b5003eef5258b5003eec5258b50004ff7158b50006f77158b50004f77158b5001cfc7158b50006f47158b5001cf47158b501ae7e5058b5003e7c5058b501aeef2058b50034ff76d0b5003cfe76d0b50004fd76d0b5002cff7690b5003cfe7690b50004fd7690b50004ff7650b50004fd7650b5003cfc7650b5002cff7610b5003cfe7610b50004fd7610b5003d7e7510b500057d7510b50036bc6410b50
  | 19 => 0x8c21086dc5358c21086de4358c21086dc4358c2102cfe7258c2102cfc7258c2102ede3258c2102edc3258c2101cfe7158c2101cfc7158c2101ede3158c2101edc3158c21004ff7058c2100cfe7058c2100cfc7058c21086df3058c21006de3058c21086dc3058c2101ef71058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c2102edf7258c2102ede7258c2102edd7258c2102edc7258c2102edf5258c2102ede5258c2102edd5258c2102edc5258c2102edf4258c2102ede4258c2102edd4258c2102edc4258c2101edf7158c2101ede7158c2101edd7158c2101edc7158c2101edf5158c2101ede5158c2101edd5158c2101edc5158c2101edf4158c2101ede4158c2101edd4158c2101edc4158c2101edf2158c2101ede2158c2101edd2158c2101edc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006de5058c21006dc5058c21006de4058c21006dc4058c2102edf2058c2102ede2058c2102edd2058c2102edc2058c2101edf1058c2101ed71058c2101ede1058c2101edd1058c2101edc1058c2103cff76d4c2101cfe76d4c21004fd76d4c2101cfc76d4c2103e7e65d4c210067d65d4c21006be64d4c21006bd64d4c21016de63d4c21006dd63d4c210875e53d4c2102dee72d4c21005ed72d4c212a77451d4c211f6fa60d4c21004ff7654c2101cfe7654c21004fd7654c2101cfc7654c2103e7e6554c210067d6554c21006be6454c21006bd6454c21016de6354c21006dd6354c21005f77154c2101df47154c2129f745154c211eefa6054c21034ff76d0c2101cfe76d0c21004fd76d0c2101cfc76d0c210067e65d0c210067d65d0c21036be64d0c21006bd64d0c21016de63d0c21006dd63d0c212d7ac42d0c211e6fa60d0c21004ff7650c2101cfe7650c21004fd7650c2101cfc7650c210067e6550c210067d6550c21036be6450c21006bd6450c21016de6350c21006dd6350c21005ef7250c2102dec7250c212cfac4250c21005f77150c2101df47150c211defa6050c2102ded76d0821366ed76d082102f6e65d082102f6d65d082102dee74d082102fae74d082102eef64d082102fae64d0821366ed64d082102fad64d0821006ad64d082102fce63d082102fcd63d0821295ef71d0821295ed71d0821296ee61d082102fe661d0821297e451d0821297af41d0821297ad41d082102fea60d082102fe960d082101df576d4421246f576d442101df675d442101f7675d442101ef765d442101f7665d4421246f565d442101f7565d44210067565d442101fb664d442101fb564d442101fd663d442101fd563d442135df772d442135df572d442135ef662d442101fe
  | 20 => 0x1ebc719902101ebf519902101ebe519902101ebd519902101ebc519902101ebf319902101ebe319902101ebd319902101ebc319902101ebf219902101ebe219902101ebd219902101ebc2199021036bf7099021036be7099021036bd7099021036bc7099021006be5099021006bc5099021006bf3099021006be3099021006bc309902102ebf209902102ebe209902102ebd209902102ebc209902101ebf109902101ebe109902101ebd109902101ebc1099021004ff755902103cfc755902101cff745902101ebf7459021004ff7359021014fe7359021014fc7359021006be4359021006bc435902102cfe725902102cfc725902102eec725902102cec725902102ebe425902102ebc425902102eec425902101cfe715902101cfc715902101ebe415902101ebc4159021004ff705902100cfe705902100cfc7059021006be4059021006bc405902101ef71059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006be5359021006bc535902102ebf725902102ebe725902102ebd725902102ebc725902102eac725902102ebf525902102ebe525902102ebd525902102ebc525902102ebf325902102ebe325902102ebd325902102ebc325902101ebf715902101ebe715902101ebd715902101ebc715902101ebf515902101ebe515902101ebd515902101ebc515902101ebf315902101ebe315902101ebd315902101ebc315902101ebf215902101ebe215902101ebd215902101ebc2159021006bf7059021006be7059021006bd7059021006bc7059021006be5059021006bc5059021006bf3059021006be3059021006bc305902102ebf205902102ebe205902102ebd205902102ebc205902101ebf105902101eb7105902101ebe105902101ebd105902101ebc105902103cff76d502101cfe76d5021004fd76d502101cfc76d502103e7e65d50210067d65d5021036be64d5021006bd64d5021236de63d502102dee72d5021005ed72d5021377ac42d502122efa60d5021034ff769502101cfe7695021004fd769502101cfc769502103e7e65950210067d6595021036be6495021006bd64950210073f5495021226de639502101df67195021005f5719502121efa6095021004ff765502101cfe7655021004fd765502101cfc765502103e7e65550210067d6555021036be6455021006bd6455021216de6355021005ef725502102dec7255021005f7715502101df4715502120efa6055021034ff761502101cfe7615021004fd761502101cfc761502103e7e65150210067d6515021036be6415021006bd6415021206de631502136fac42150211fefa6015021004ff7558c2103cfc7558c21004ff7458c21034fc7458c2101cff7358c2101edf7358c21086de535
  | 21 => 0xc7558121005bf7458121005bc7458121006bf6458121006bc6458121005df7358121095dc735812108ef8605812103e7f749942103e7e749942103e7d749942103e7c749942103e7f739942103e7e739942103e7d739942103e7c73994210067e43994210067c439942102e7f729942102e7e729942102e7d729942102e7c729942102e7f429942102e7e429942102e7d429942102e7c429942102e7f329942102e7e329942102e7d329942102e7c329942101e7f719942101e7e719942101e7d719942101e7c719942101e7f419942101e7e419942101e7d419942101e7c419942101e7f319942101e7e319942101e7d319942101e7c319942101e7f219942101e7e219942101e7d219942101e7c219942103e7f709942103e7e709942103e7d709942103e7c70994210067e40994210067c40994210067f30994210067e30994210067c309942102e7f209942102e7e209942102e7d209942102e7c209942101e7f109942101e7e109942101e7d109942101e7c109942101cff755942101e7f7559421004ff7459421034fc7459421004ff7359421014fe7359421014fc73594210067e53594210067c535942102cfe725942102cfc725942102e7e525942102e7c525942101cfe715942101cfc715942101ef4715942101cf4715942101e7e515942101e7c515942101ef45159421004ff705942100cfe705942100cfc70594210067e50594210067c505942101ef710594210067f74594210067e74594210067d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067e43594210067c435942102e7f725942102e7e725942102e7d725942102e7c725942102e7f425942102e7e425942102e7d425942102e7c425942102e7f325942102e7e325942102e7d325942102e7c325942101e7f715942101e7e715942101e7d715942101e7c715942101e74715942101e7f415942101e7e415942101e7d415942101e7c415942101e7f315942101e7e315942101e7d315942101e7c315942101e7f215942101e7e215942101e7d215942101e7c21594210067f70594210067e70594210067d70594210067c70594210067e40594210067c40594210067f30594210067e30594210067c305942102e7f205942102e7e205942102e7d205942102e7c205942101e7f105942101e77105942101e7e105942101e7d105942101e7c1059421036bf7599021036be7599021036bd7599021036bc7599021036bf7399021036be7399021036bd7399021036bc7399021006be5399021006bc539902102ebf729902102ebe729902102ebd729902102ebc729902102ebf529902102ebe529902102ebd529902102ebc529902102ebf329902102ebe329902102ebd329902102ebc329902101ebf719902101ebe719902101ebd7199021
  | 22 => 0x8d21006bf64d8d21006bc64d8d21096de63d8d2103cfe75d8d21004fd75d8d21034fe74d8d21004fd74d8d21096de53d8d2101cfd72d8d21096df32d8d2102cfd71d8d21096df31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21096dc30d8d21005bf7458d21005bc7458d21006bf6458d21006bc6458d21096dc6358d21004ff7558d2103cfc7558d21004ff7458d21006bf7458d21004bf7458d21034fc7458d21006bc7458d21034bc7458d21094ff7358d21006df7358d210a4ff7258d21006ef7258d210b4ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d2103cff76d4d21004fe76d4d21004fd76d4d2103cfc76d4d210067f65d4d2103e7c65d4d21006bf64d4d21006bc64d4d210975e53d4d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d2103e7c6554d21006bf6454d21006bc6454d21006df6354d21016dc6354d21034ff76d0d21004fe76d0d21004fd76d0d21034fc76d0d21006bf64d0d21036bc64d0d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d21036bc6450d2101cfe76d492101cfc76d49210067f65d492103e7c65d4921006bf64d4921006bc64d492102f6e52d492101df671d4921005f571d492101cfc76549210067f655492103e7c6554921005bf7454921005bc7454921006bf6454921006bc6454921005f7715492101df4715492102fe4215492101cfe76d092101cfc76d0921006bf64d0921036bc64d092101df671d0921005f571d092102fe421d092101cfc7650921006bf6450921036bc6450921005f7715092101df4715092101cfc764c921006bf644c921006bc644c921006df634c921016dc634c921005f7714c92101df4714c92102cfe76d452102cfc76d45210067f65d452103e7c65d4521006bf64d4521006bc64d452102dee72d4521005ed72d452101f7651d452103cff7654521004fd765452102cfc76545210067f655452103e7c6554521006bf6454521006bc6454521005ef725452102dec725452101fe4215452102cfe76d052102cfc76d0521006bf64d0521036bc64d052102dee72d0521005ed72d052101fe421d0521034ff7650521004fd765052102cfc7650521006bf6450521036bc6450521005ef725052102dec7250521014ff764c521094fd764c52102cfc764c521006bf644c521006bc644c521006df634c521016dc634c521005ef724c52102dec724c52100cfe76d8121006bf64d8121006bc64d812108efa60d812103cfe75d8121004fd75d8121034fe74d8121004fd74d8121014fe73d8121004fd73d8121014fc73d812101cfd72d812100cfc72d812102cfd71d812100cfc71d8121276f721d8121276f421d812108efa20d812108efa10d81210057f75581210057
  | 23 => 0x34be76d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121006be63d9121006bc63d9121387b721d912128fae21d912128fac21d9121387b421d9121006be60d9121006bc60d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006be53d9121006bc53d912128ebf72d9121386be72d9121006bd72d9121386bc72d9121386be52d9121386bc52d9121006bf32d9121386be32d9121386bc32d9121386bf71d912128ebe71d9121006bd71d912128ebc71d912128ebe51d912128ebc51d9121006bf31d912128ebe31d912128ebc31d9121386bf21d912128ebe21d912128ebc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006be50d9121006bc50d9121006bf30d9121006be30d9121006bc30d9121386bf20d9121006be20d9121386bc20d912128ebf10d9121006be10d912128ebc10d9121006bf6499121296ef6299121004ff755912103cfc7559121006bf7459121004ff7359121014fe7359121014fc7359121004ff7259121006ef7259121004ef7259121004ff7159121006f77159121004ff705912100cfe705912100cfc7059121004fe7619121036be6419121006bd6419121286ef6219121005be7619121006be7619121004be7619121006bf6519121006be6519121006bd6519121006bc6519121006be6319121006bc631912137fb72119121287ae2119121287ac211912137fb42119121006be6019121006bc6019121036bf7519121036be7519121036bd7519121036bc7519121036bf7319121036be7319121036bd7319121036bc7319121006be5319121006bc5319121036bf7219121036be7219121036bd7219121036bc721912137ebe521912137ebc5219121006bf321912137ebe321912137ebc3219121036bf7119121036be7119121036bd7119121036bc7119121286be5119121286bc5119121006bf3119121286be3119121286bc311912137ebf2119121286be2119121286ae2119121006bd2119121286bc2119121286ac2119121036bf7019121036be7019121036bd7019121036bc7019121006be5019121006bc5019121006bf3019121006be3019121006bc301912137ebf2019121006be201912137ebc2019121286bf1019121006be1019121286bc101912103cff76d5121004fe76d5121004fd76d512103cfc76d5121006bf64d5121036bc64d5121034ff7695121004fe7695121004fd7695121034fc7695121006bf6495121036bc64951210073f5495121004ff7655121004fe7655121004fd7655121004fc7655121006bf6455121036bc6455121034ff7615121004fe7615121004fd7615121034fc7615121006bf6415121036bc641512102dee7215121005ed7215121014fe76d
  | 24 => 0xf3258e2101cfc7158e2101ede3158e2101edc3158e21004ff7058e2100cfe7058e2100cfc7058e2103cff76d4e2101cfe76d4e21004fd76d4e2101cfc76d4e212a67f65d4e2103e7c65d4e210a75e53d4e2102dee72d4e21005ed72d4e21004ff7654e2101cfe7654e21004fd7654e2101cfc7654e2129e7f6554e2103e7c6554e21034ff76d0e2101cfe76d0e21004fd76d0e2101cfc76d0e21036be64d0e21006bd64d0e21004ff7650e2101cfe7650e21004fd7650e2101cfc7650e21036be6450e21006bd6450e21005ef7250e2102dec7250e2102ef72158a2101eee2158a2101eec2158a2101ef42158a2103e7e65d4a210067d65d4a2101df671d4a21005f571d4a2103cff7654a2103e7e6554a210067d6554a21005bf7454a21005bc7454a21005f77154a2101df47154a2102fe72154a21036be64d0a21006bd64d0a2101df671d0a21005f571d0a21295ed76d0a2133eed76d0a2102dee74d0a21296ef64d0a21297ae64d0a2133eed64d0a21297ad64d0a21297e671d0a21295ed71d0a2133fe571d0a2102eee61d0a21297af41d0a21297ad41d0a21034ff7650a21036be6450a21006bd6450a2102fac4250a21005f77150a2101df47150a21285ed7610a2102eed7610a2102f6e7510a2102f6d7510a2102fae7410a21286ef6410a21287af6410a2133eed6410a21287ac6410a21007af5410a2133fac5410a2133faf4310a21007ad4310a2102def7110a21285ed7110a2102fe66110a21287ae4110a21287ac4110a21014ff764ca2101cfc764ca21016de634ca21006dd634ca21005f7714ca2101df4714ca21004ff75582210067f75582210047f755822103cfc75582210067c755822103c7c7558221004ff7458221034fc7458221004ff7358221014fe7358221014fc735822101cfc715822123ef7215822101ef4215822101efb705822109efa205822101efb105822101ef8105822103cfe76d9521034fe74d9521004fd74d9521014fe73d9521004fd73d9521014fc73d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210067c50d95210067f6599521005be7499521005bd7499521095de7399521005dd739952135ef76199521005bf7459521005bc74595210067f7559521004ff7459521006bf7459521004bf7459521034fc7459521006bc7459521034bc7459521004ff7359521014fe7359521014fc7359521004ff7259521006ef7259521004ff7159521006f77159521004f77159521004ff705952100cfe705952100cfc7059521004fe761952103e7e65195210067d651952138ef76119521034fe76d912103cfe75d9121004fd75d9121014fe73d9121004fd73d9121014fc73d9121006be43d9121006bc43d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d9121
  | 25 => 0x5321004fd761532102cfc761532136ebf6415321036bc641532102dee7215321005ed7215321004ff7558f2103cfc7558f21004ff7458f21034fc7458f2102edf7358f2101cfc7258f2102ede3258f2102edc3258f210b6df3158f21004ff7058f2100cfe7058f2100cfc7058f2103cff76d4f2102cfe76d4f21004fd76d4f2102cfc76d4f2103e7e65d4f210067d65d4f210b75e53d4f21004ff7654f2102cfe7654f21004fd7654f2102cfc7654f2103e7e6554f210067d6554f21005f77154f2101df47154f21034ff76d0f2102cfe76d0f21004fd76d0f2102cfc76d0f212d6bf64d0f21036bc64d0f21004ff7650f2102cfe7650f21004fd7650f2102cfc7650f212cebf6450f21036bc6450f21005f77150f2101df47150f2103e7e65d47210067d65d472102dee72d4721005ed72d472135df576d472124ef576d472101df675d472135ef765d472135f7665d472124ef565d472135f7565d47210067565d472135fe672d472135df572d472124fe572d4721005e572d472101ef662d472135f7752d472135f7552d4721005f570d472103cff765472103e7e65547210067d6554721005ef725472102dec725472101fe6215472138df5761472101ef5761472101f76751472138ef7651472124ef5651472124f77531472100775531472101df7721472138df5721472101fe66214721005f5701472139776501472124f745014721036be64d0721006bd64d072102dee72d0721005ed72d072101fb641d0721034ff7650721036be6450721006bd6450721005ef725072102dec725072101fb44150721014ff764c72102cfc764c721016de634c721006dd634c721005ef724c72102dec724c721004ff755832103cfc7558321004ff7458321034fc7458321004ff7358321014fe7358321014fc735832101cfc725832102efb705832102efb205832102ef820583210aefa105832101e7f7559621004ff7459621034fc7459621004ff7359621014fe7359621014fc735962101cfc715962101e7e515962101e7c5159621004ff705962100cfe705962100cfc7059621004ff755922103cfc755922101ebf7459221004ff7359221014fe7359221014fc7359221006ef725922101cfc715922101ebe415922101ebc4159221004ff705922100cfe705922100cfc705922103cff76d522101cfe76d5221004fd76d522101cfc76d5221036be64d5221006bd64d522102dee72d5221005ed72d5221034ff769522101cfe7695221004fd769522101cfc76952210073f5495221004ff765522101cfe7655221004fd765522101cfc7655221005ef725522102dec7255221034ff761522101cfe7615221004fd761522101cfc7615221036be6415221006bd6415221004ff7558e2103cfc7558e21004ff7458e21034fc7458e2101edf7358e210a6d
  | 26 => 0x2cfc7694931015de7394931005dd7394931006ef629493102eec6294931004ff7654931004fe7654931004fc765493103e7e65549310067d6554931005bf7454931005bc7454931006ef625493102eec6254931005f7715493101df47154931004fe7614931004fd761493102cfc7614931015de7314931005dd7314931004fe76d0931004fd76d0931034fc76d0931006ef62d093102eec62d0931004fe7690931004fd769093102cfc7690931006bf6490931036bc6490931015de7390931005dd7390931004ff7650931004fe7650931004fc7650931004fe7610931004fd761093102cfc76109310057e75109310057d7510931006bf6410931036bc6410931015de7310931005dd7310931006ef621093102eec621093101df67110931005f5711093101cdc764c931015df724c931017cf724c931007cf624c93102ede624c93102edc624c931007cc624c931007d7714c93101dde714c93101ddc714c931007d4714c931016df614c931017d7614c931014fe76d4531014fc76d45310067f65d453103e7c65d4531015de73d4531005dd73d453101f7651d453103cff7654531014fe7654531124fd7654531014fc76545310067f655453103e7c6554531005df7354531015dc735453101fd43154531014fe76d0531014fc76d0531006bf64d0531036bc64d0531015de73d0531005dd73d0531034ff7650531014fe76505310e4fd7650531014fc7650531006bf6450531036bc6450531005df7350531015dc7350531005ef7250531005ec725053101fb4415053100cfe76d81310befa60d813103cfe75d8131004fd75d8131034fe74d8131004fd74d813101cfd73d813100cfc73d813102cfe72d8131004fd72d8131014fd71d81310befa30d81310befa10d81310057f75581310057c7558131005bf7458131005bc7458131005ef7258131005ec72581310bef8605813102e7f7559721004ff7459721006bf7459721004bf7459721034fc7459721006bc7459721034bc7459721004ff7359721014fe7359721014fc735972101cfc725972102e7e525972102e7c5259721006f77159721004ff705972100cfe705972100cfc70597210067e50597210067c5059721004ff755932103cfc755932102ebf7459321004ff7359321014fe7359321014fc735932101cfc725932102ebe425932102ebc4259321004ff705932100cfe705932100cfc705932103cff76d532102cfe76d5321004fd76d532102cfc76d532103e7e65d53210067d65d5321376bf64d5321036bc64d5321034ff769532102cfe7695321004fd769532102cfc76953210073f549532101df67195321005f57195321004ff765532102cfe7655321004fd765532102cfc765532103e7e65553210067d6555321005f7715532101df47155321034ff761532102cfe761
  | 27 => 0xf7614a3101cfe7614a31004fd7614a31034ff76d0a3101cfe76d0a31004fd76d0a31036be64d0a31006bd64d0a3102cff7690a3101cfe7690a31004fd7690a3128ebf6490a31036bc6490a31004ff7650a31004fd7650a3101cfc7650a31036be6450a31006bd6450a3102cff7610a3101cfe7610a31004fd7610a310057e7510a310057d7510a31286bf6410a31036bc6410a3101df67110a31005f57110a31004ff755823103cfc7558231004ff7458231034fc7458231004ff725823102cfc725823101cfe715823101cfc715823101efb70582310c6f850582310c6fa40582310c6fa30582310c6fa205823101efb105823101ef8105823103cfe76d9531034fe74d9531004fd74d953101cff73d953101cfd73d95311367f53d95311367d53d953102cfe72d9531004fd72d953100cfe70d9531004fd70d953100cfc70d95310067e50d95310067c50d95310067f6599531005be7499531005bd7499531005ee7299531005ed7299531125f57199531145f771595310067f7559531004ff7459531034fc7459531124ff7359531006df7359531004ff725953102cfc7259531144ff7159531006f7715953129e7e515953129e7c5159531004ff705953100cfe705953100cfc7059531134fe761953103e7e65195310067d6519531034fe76d913103cfe75d9131004fd75d913101cff73d913101cfd73d91310f6bf43d91310f6bd43d913102cfe72d9131004fd72d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d9131006bf64991310e5f57199131005ef7259131005ec7259131105f77159131004ff755913103cfc7559131006bf74591310e4ff7359131006df7359131004ff7259131006ef7259131004ef725913102cfc7259131006ec725913102cec7259131104ff7159131006f77159131004ff705913100cfe705913100cfc70591310f4fe7619131036be6419131006bd641913103cff76d5131004fe76d5131004fd76d513103cfc76d5131034ff7695131004fe7695131004fd7695131034fc7695131006bf6495131036bc64951310073f549513101df67195131005f57195131004ff7655131004fe7655131004fd7655131004fc7655131006bf6455131036bc6455131034ff7615131004fe7615131004fd7615131034fc7615131015de7315131005dd731513103cfe75d8931004fd75d8931034fe74d8931004fd74d893101cfd73d89310a6ee32d89310a6ed32d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d8931006ef6298931095f57198931005bf7458931005bc74589310b5f771589310057e75189310057d751893102eee6218931006ed6218931004fe76d4931004fd76d493103cfc76d493103e7e65d49310067d65d4931004fe7694931004fd7694931
  | 28 => 0x884100cfc705884103cff76d484101cfe76d4841004fd76d484103e7e65d48410067d65d4841035be74d4841005bd74d484102cff769484101cfe7694841004fd769484102eee6294841006ed6294841004ff7654841004fd765484101cfc765484103e7e65548410067d6554841005bf7454841035bc745484102eee6254841006ed6254841005f7715484101df4715484102cff761484101cfe7614841004fd7614841035bd769084137ebd7690841004bd7690841326be6590841036bc6590841006bd6390841035be7290841037ae7290841036bf629084137ebd629084128dbf719084128dbd719084128ebe6190841037b6619084102cff768c84101cfe768c841004fd768c841004ff764c841004fd764c84101cfc764c841005bf744c841035bc744c841016de634c841006dd634c841005f7714c84101df4714c841004ff755804103cfc755804100cfd7458041004ff7358041014fe7358041014fc7358041004ff725804102cfc7258041006be4258041036bc425804101ebf415804101ef6415804101ebd4158041036f5415804101cff705804101efb70580410cefa5058041036fb4058041036f84058041006fb30580410cef830580410cefa205804101efb105804101ef8105804101e7f7559631004ff7459631034fc74596311267f53596311267d5359631004ff725963102cfc725963101cfe715963101cfc715963101e7e515963101e7c5159631004ff705963100cfe705963100cfc705963101ef71059631004ff755923103cfc755923101ebf74592310e6bf43592310e6bd4359231004ff725923102cfc725923101cfe715923101cfc715923101ebe415923101ebc4159231004ff705923100cfe705923100cfc705923101ef7105923103cff76d523101cfe76d5231004fd76d523101cfc76d5231036be64d5231006bd64d5231015de73d5231005dd73d5231034ff769523101cfe7695231004fd769523101cfc76952310073f549523101df67195231005f57195231004ff765523101cfe7655231004fd765523101cfc7655231034ff761523101cfe7615231004fd761523101cfc7615231036be6415231006bd6415231004ff7558a3103cfc7558a31004ff7458a31006bf7458a31004bf7458a31034fc7458a31006bc7458a31034bc7458a3101eef7258a31096ee3258a31096ed3258a3101cfc7158a3101edf3158a3101edd3158a3101eee2158a3101eec2158a31004ff7058a3100cfe7058a3100cfc7058a3103cff76d4a3101cfe76d4a31004fd76d4a3103e7e65d4a310067d65d4a31015de73d4a31005dd73d4a3102cff7694a3101cfe7694a31004fd7694a31004ff7654a31004fd7654a3101cfc7654a3103e7e6554a310067d6554a31005bf7454a31005bc7454a31005f77154a3101df47154a3102cf
  | 29 => 0x36be76d0941004be76d094130dbe75d0941035bc75d0941005bd73d0941007af62d094102ebe62d094102ebc62d0941007ac62d094102eac62d094101dbe71d094101dbc71d0941036bf61d0941037b761d0941005bd70d094101cfe7690941005bd7490941006ef629094102eec629094101df67190941005f57190941037b4419094101cfc7650941006ef625094102eec6250941005f7715094101df4715094101cbc765094130dbe755094130dbc7550941005bf7350941035bf7250941037af7250941007af625094102ebe625094102ebc6250941007ac625094102eac6250941007b7715094101dbe715094101dbc7150941007b4715094101db47150941036bf6150941037b76150941005bf7050941004fe768c941004fd768c94102cfc768c941035be748c941005bd748c941006ef628c94102eec628c941004ff764c941004fe764c941004fc764c941035be744c941005bd744c941006ef624c94102eec624c941034fe76d4541034fc76d45410067f65d454103e7c65d4541035be74d4541005bd74d4541006ef62d4541006ec62d454101f7651d454103cff7654541004fd7654541034fc76545410067f655454103e7c6554541005bf7454541035bc7454541006ef6254541006ec625454101fb4415454100cfe76d8141006ef62d8141006ec62d81410defa60d814103cfe75d8141004fd75d814101cfd74d814100cfc74d8141014fe73d8141004fd73d8141014fc73d8141006bf43d8141006bd43d814102cfe72d8141004fd72d8141034fd71d81410defa40d81410defa10d81410057f75581410057c7558141005df73581410e5dc7358141005ef7258141005ec7258141006ef6258141006ec62581410def8605814101cff755944101e7f7559441034fe7459441034fc74594410367e54594410367c5459441004ff7359441014fe7359441014fc7359441004ff725944102cfc725944101cfe715944101cfc715944101e7e515944101e7c5159441004ff705944100cfe705944100cfc7059441004ff7558c4103cfc7558c4101cff7358c4101edf7358c410d6de5358c41036df4358c41036dc4358c41004ff7258c4102cfc7258c41036bc4258c410d6df3258c4101cfc7158c4101ebf4158c4101ebd4158c4101ede3158c4101edc3158c41004ff7058c4100cfe7058c4100cfc7058c41006de3058c410d6dc3058c4103cff76d4c4101cfe76d4c41004fd76d4c41035be74d4c41005bd74d4c410d75e53d4c41004ff7654c41004fd7654c4101cfc7654c41016de6354c41006dd6354c41004ff755884103cfc7558841004ff7358841014fe7358841014fc735884101eef7258841036ef4258841036bc4258841036ec425884101ebf415884101ebd415884101eee215884101eec2158841004ff705884100cfe705
  | 30 => 0xe75d8941006ed75d8941006ec75d8941296ef74d894133eee74d8941006ef54d894133eee54d8941006ed54d894133eec54d8941006ef73d8941006ee73d8941006ed73d8941006ec73d8941006ef53d8941006ee53d8941006ed53d8941006ec53d894133eef43d8941006ee43d8941006ed43d894133eec43d894133eef71d8941296ee71d8941006ed71d8941296ee51d8941296ec51d894133eef41d8941296ee41d8941296ec41d8941006ef31d8941296ee31d8941296ec31d8941006ef70d8941006ee70d8941006ed70d8941006ec70d8941006ee50d8941006ec50d894133eef40d8941006ee40d894133eec40d8941006ef30d8941006ee30d8941006ec30d8941296ef10d8941006ee10d8941296ec10d894128ebf6498941006ef62989410057e75189410057d7518941286bf641894102eee6218941006ed6218941005ee7618941006ee76189410076e75189410076d7518941006ef6518941006ee6518941006ed6518941006ec6518941007ad7418941007af5418941007ac5418941006ef6318941006ee6318941006ed6318941006ec6318941007af4318941007ad4318941367e74118941287ae4118941287ac4118941367e44118941006ee6018941006ec601894102eef751894102eee751894102e6e751894102eed751894102e6d751894102eec751894102eef741894102eee741894102eec7418941006ef5418941006af5418941366ee5418941006ed5418941366ec5418941006ac541894102eef731894102eee731894102eed731894102eec7318941006ef5318941006ee5318941006ed5318941006ec5318941366ef4318941006af4318941006ee4318941006ed4318941006ad4318941366ec431894102eef711894102eee711894102eed711894102eec7118941286ee5118941286ec5118941366ef4118941286ee4118941286ae4118941006ed4118941286ec4118941286ac4118941006ef3118941286ee3118941286ec311894102eef701894102eee701894102eed701894102eec7018941006ee5018941006ec5018941366ef4018941006ee4018941366ec4018941006ef3018941006ee3018941006ec3018941286ef1018941006ee1018941286ec1018941004fe76d4941004fd76d494103cfc76d494103e7e65d49410067d65d494130f3f54d4941006ef62d494102eec62d4941004fe7694941004fd769494102cfc7694941035be7494941005bd7494941006ef629494102eec6294941004ff7654941004fe7654941004fc765494103e7e65549410067d6554941005bf7454941035bc74549410073f5454941006ef625494102eec6254941005f7715494101df47154941004fe7614941004fd761494102cfc7614941035be7414941005bd7414941006ef621494102eec6214941005be76d0941
  | 31 => 0x9541004ff7359541014fe7359541014fc7359541004ff7259541006ef7259541004ef725954102cfc7259541006ec725954102cec7259541004ff7159541006f77159541004ff705954100cfe705954100cfc7059541004fe761954103e7e65195410067d651954101cfe76d514101cfc76d51410067f65d514103e7c65d51410373e54d514101df671d5141005f571d514101dbe76d514130ebe76d514101cbe76d5141035be75d514130ebf65d51410073f65d51410063f65d514130ebd65d514130f3c65d5141005bd73d5141005bd72d5141376bc62d514101dbe71d514130fb671d514101db671d514130fb571d514101dbc71d5141036bf61d5141037b761d5141005bd70d514101cfc76551410067f655514103e7c6555141005f7715514101df47155141037b44155141005be7615141036be761514130dbe75151410373e751514130ebf651514130ebd6515141005bd7315141005bd721514136ebc621514101dbe711514101dbc7115141036bf6115141037b76115141005bd7015141014fe76d8d410e6de63d8d4103cfe75d8d41004fd75d8d4101cfd74d8d410e6de53d8d410e6de43d8d4102cfe72d8d41004fd72d8d41034fd71d8d410e6df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d410e6dc30d8d410e6dc6358d41005ef7258d41005ec7258d41004fe76d4d41004fd76d4d4103cfc76d4d410067f65d4d4103e7c65d4d410e75e53d4d41004ff7654d41004fe7654d41004fc7654d410067f6554d4103e7c6554d41005bf7454d41035bc7454d41006df6354d41016dc6354d41005be76d0d41036be76d0d4130dbe75d0d41035bc75d0d410e5bd73d0d41016be63d0d41016bc63d0d41005bd72d0d412d6bc62d0d4101dbe71d0d4101dbc71d0d41036bf61d0d41037b761d0d41005bd70d0d4101cfc7650d41006df6350d41016dc6350d41005f77150d4101df47150d41037b44150d4101dbc7650d41016bc7650d4101cbc7650d4130dbe7550d4130dbc7550d41035bf7350d410379f7350d410079f6350d41016be6350d41016bc6350d410e79c6350d41005bf7250d412cebc6250d41007b77150d4101dbe7150d4101dbc7150d41007b47150d41036bf6150d41037b76150d41005bf7050d4103cfe75d8941004fd75d8941014fe73d8941004fd73d8941014fc73d8941006ef32d8941006ec32d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d8941006ef65d8941006ee65d8941006ed65d8941006ec65d8941297af74d8941007af54d8941007ac54d8941006ef63d8941006ee63d8941006ed63d8941006ec63d8941007af43d8941007ad43d894133fe741d8941297ae41d8941297ac41d894133fe441d8941006ee60d8941006ec60d8941006ef75d8941006e
  | 32 => 0xcfc705964101ef71059641036f7415924101ebe415924101ebc415924101ef4415924103e7e65d52410067d65d52410373e54d524101df671d5241005f571d524103cff765524103e7e65552410067d6555241005f7715524101df47155241037b74155241004ff7558e4103cfc7558e4101edf7358e410f6de4358e41004ff7258e4102cfc7258e410f6df3258e4101cfc7158e4101ebf4158e4101ebd4158e4101ede3158e4101edc3158e41004ff7058e4100cfe7058e4100cfc7058e4101ef71058e4103cff76d4e4101cfe76d4e41004fd76d4e41035be74d4e41005bd74d4e410f75e53d4e41004ff7654e41004fd7654e4101cfc7654e41014ff7650e41016de6350e41006dd6350e41005f77150e4101df47150e41004ff7558a4103cfc7558a41004ff7358a41014fe7358a41014fc7358a4101eef7258a4101cfc7158a4101ebf4158a4101ebd4158a4101eee2158a4101eec2158a41004ff7058a4100cfe7058a4100cfc7058a4103cff76d4a4101cfe76d4a41004fd76d4a4103e7e65d4a410067d65d4a41035be74d4a41005bd74d4a4102cff7694a4101cfe7694a41004fd7694a41004ff7654a41004fd7654a4101cfc7654a4103e7e6554a410067d6554a41005bf7454a41035bc7454a41005f77154a4101df47154a4102cff7614a4101cfe7614a41004fd7614a4102eee6290a41006ed6290a4101df67190a41005f57190a41037b74190a41326be6590a4128ebc6590a41006bd6390a41035be7290a4128ebf6290a4128fae6290a41386bd6290a4128fad6290a4128fb67190a4128dbd7190a41387b57190a41036be6190a4102cff7650a4102eee6250a41006ed6250a41037ac4250a41005f77150a4101df47150a41285bd7610a41036bd7610a410373e7510a410373d7510a4131ebe6510a41286bc6510a41006bd6310a41037ae7210a41286bf6210a41287af6210a41386bd6210a41287ac6210a41035bf7110a41285bd7110a41037b66110a41287ac2110a4102cff768ca4101cfe768ca41004fd768ca41004ff764ca41004fd764ca4101cfc764ca41005bf744ca41035bc744ca41016de634ca41006dd634ca41004ff755824103cfc7558241004ff7358241014fe7358241014fc7358241004ff725824102cfc7258241006be4258241006bc425824101cfc715824101ebf415824101ebd415824101efb70582410eefa40582410eefa205824101efb105824101ef8105824103cfe76d9541006bd74d9541014fe73d9541004fd73d9541014fc73d954102cfe72d9541004fd72d954100cfe70d9541004fd70d954100cfc70d95410067e50d95410067c50d95410067f65995410e5de7399541005dd7399541005ee7299541005ed7299541005ef7259541005ec72595410067f7559541004ff7459541006bf745
  | 33 => 0xa305805110efa205805101efb105805101ef810580510367f755974101cfc7459741036bc745974101cbc74597410367e54597410367c5459741036bc5459741004ff7359741014fe7359741014fc7359741004ff725974102cfc7259741004ff705974100cfe705974100cfc70597410067e50597410067c5059741036bf4059741035bd76d5341316bd76d53410373e75d5341036bf65d5341316bd65d5341005bd73d5341005bd72d5341376be62d534101dbe71d534101dbc71d5341005bd70d5341004ff7558f4103cfc7558f4101cfc7458f41036df7358f41036df4358f41036dc4358f41004ff7258f4102cfc7258f41106df3158f41004ff7058f4100cfe7058f4100cfc7058f41036bf4058f4103cff76d4f41034fe76d4f41004fd76d4f4103e7e65d4f410067d65d4f41035bc74d4f411075e53d4f41004ff7654f41004fd7654f41034fc7654f4103e7e6554f410067d6554f41005bf7454f41035bc7454f41035bf7650f410d6bf7650f41315be7550f41315bc7550f410379f7350f41016be6350f41016bc6350f41005bf7250f412cebe6250f4101dbe7150f4101dbc7150f41005bf7050f41004ff7558b4103cfc7558b4101cfc7458b41004ff7358b41014fe7358b41014fc7358b41036ef7258b41036ef4258b41036ec4258b41004ff7058b4100cfe7058b4100cfc7058b4103cff76d4b41034fe76d4b41004fd76d4b4103e7e65d4b410067d65d4b41035bc74d4b413173f54d4b4102cff7694b41034fe7694b41004fd7694b41035be7494b41005bd7494b41004ff7654b41004fd7654b41034fc7654b4103e7e6554b410067d6554b41005bf7454b41035bc7454b410073f5454b41005f77154b4101df47154b4102cff7614b41034fe7614b41004fd7614b41035be7414b41005bd7414b41035bf7650b41006bf7650b41315be7550b41315bc7550b41005bf7350b41037af7250b4102ebe6250b4102ebc6250b4101dbe7150b4101dbc7150b41005bf7050b4102cff768cb41034fe768cb41004fd768cb41035be748cb41005bd748cb41004ff764cb41004fd764cb41034fc764cb41035be744cb41005bd744cb41005f7714cb4101df4714cb4103e7e65d47410067d65d4741035be74d4741005bd74d474103cff765474103e7e65547410067d6554741005bf7454741035bc745474101fb64154741004ff755834103cfc755834101cfc7458341004ff7358341014fe7358341014fc7358341036bf4358341006bd4358341004ff725834102cfc7258341036f64158341036f54158341036fb7058341036fb4058341036f840583410fefa105834101e7f7559641004ff7359641014fe7359641014fc7359641004ff725964102cfc725964101cfc715964101e7e515964101e7c5159641004ff705964100cfe7059641
  | 34 => 0x951006bf6410951036bc6410951006ef621095102eec6210951004fe768c951004fd768c95102cfc768c95103d7e758c9510057d758c951004ff764c951004fe764c951004fc764c95100cfe76d815111efa60d815101cfd75d815100cfc75d8151034fe74d8151004fd74d8151014fe73d8151004fd73d8151014fc73d815102cfe72d8151004fd72d815103cfd71d815111efa50d815111efa10d815111ef8605815101ebf745905103ebf545905103ebc5459051004ff7359051014fe7359051014fc7359051004ff725905102cfc725905101ebe415905101ebc4159051004ff705905100cfe705905100cfc7059051004ff7458c51034fc7458c5101cff7358c5101edf7358c5103edf5358c5103edc5358c51116de4358c51004ff7258c5102cfc7258c51116df3258c5101cfc7158c5101ede3158c5101edc3158c51004ff7058c5100cfe7058c5100cfc7058c51116df3058c5103d7f7654c511467f7654c5103d7f7354c5103f5f7354c510167e6354c510167c6354c5129d7f7154c5129e7e6154c5103f766154c5110d7e7054c5110d7c7054c511175f3054c51034ff76d0c5101cfe76d0c51004fd76d0c51036be64d0c51006bd64d0c51004ff7650c51004fd7650c5101cfc7650c51036be6450c51006bd6450c51016de6350c51006dd6350c51004ff7458851006bf7458851004bf7458851034fc7458851006bc7458851034bc7458851004ff7358851014fe7358851014fc735885103e7f53588510067d535885101eef725885103eef525885103eec525885101ef4715885101e7f515885101e7d515885101eee215885101eec215885101ef4215885101ee42158851004ff705885100cfe705885100cfc70588510067e505885103e7c5058851034ff76d085101cfe76d0851004fd76d0851036be64d0851006bd64d085101df671d0851005f571d085102cff769085101cfe7690851004fd769085102eee6290851006ed6290851004ff7650851004fd765085101cfc7650851036be6450851006bd645085102eee6250851006ed6250851005f7715085101df4715085102cff761085101cfe7610851004fd761085103d7e75108510057d7510851036bc6410851287e4211085102cff768c85101cfe768c851004fd768c85102eee628c851006ed628c851004ff764c851004fd764c85101cfc764c851016de634c851006dd634c85102eee624c851006ed624c851005f7714c85101df4714c85100cfd7558051004ff7458051034fc7458051004ff7358051014fe7358051014fc735805103e7f53580510067d5358051004ff725805102cfc725805101ef6515805103ef5515805101ef4215805101cff705805101efb705805103efb505805110e7e505805103e7c505805103ef8505805103e78505805110efa405805110ef
  | 35 => 0x36be6450a51006bd6450a5102cff7610a5101cfe7610a51004fd7610a5103d7e7510a510057d7510a51036be6410a51006bd6410a5102cff768ca5101cfe768ca51004fd768ca51006be648ca51006bd648ca51004ff764ca51004fd764ca5101cfc764ca51006be644ca51006bd644ca51016de634ca51006dd634ca51004ff7458251034fc7458251004ff7358251014fe7358251014fc73582510067f53582510067d5358251004ff725825102cfc725825101cfc715825101efb705825112e7e505825112efa505825112e7c5058251006fb305825112ef8305825112efa205825101efb105825101ef81058251014fe73d9151004fd73d9151014fc73d915102cfe72d9151004fd72d915100cfe70d9151004fd70d915100cfc70d9151006bf6499151005ef7259151005ec7259151036be6419151006bd641915101cfe7695151006bf6495151036bc649515103f3f549515101df67195151005f5719515101cfc7655151006bf6455151036bc6455151005f7715515101df47155151014fe76d8d51126de63d8d5101cfd75d8d51034fe74d8d51004fd74d8d51126de53d8d5102cfe72d8d51004fd72d8d5103cfd71d8d512a67e51d8d512a67c51d8d51126df31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d51126dc6358d5101cfc7654d51006df6354d51016dc6354d5103f5c5354d51005f77154d5101df47154d51004fe76d0d51004fd76d0d51034fc76d0d51004ff7650d51004fe7650d51004fc7650d51034fe74d8951004fd74d8951014fe73d8951004fd73d8951014fc73d895100cfe70d8951004fd70d895100cfc70d8951006ef6298951005bf7458951005bc745895102eee6218951006ed621895135ef761189510057e76d495103e7e76d49510067f64d49510067f63d495102e7e62d495102e7c62d495101d7e71d495101d7c71d495103e7f61d495103f7761d49511ce7e60d49511ce7c60d495101cfe76949510057d7594951006ef629495102eec629495103f6f529495101df67194951005f5719495101cfc7654951005bf7454951005bc7454951006ef625495102eec6254951005f7715495101df4715495101c7c76549510073f74549510073c74549510067f64549510067f635495103d7f725495103f6f72549510076f625495102e7e625495102e7c62549510076c625495100777715495101d7e715495101d7c715495100774715495103e7f615495103f7761549511ae7e60549511ae7c6054951004fe76d0951004fd76d0951034fc76d0951006ef62d095102eec62d0951004fe7690951004fd769095102cfc769095103d7e75909510057d7590951006bf6490951036bc6490951004ff7650951004fe7650951004fc7650951004fe7610951004fd761095102cfc761095103d7e75109510057d751
  | 36 => 0xd755925130ebc7559251006bf7359251006be7359251006bd7359251006bc735925130ebf5359251006be535925130ebc5359251006bf7259251006be7259251006bd7259251006bc725925130ebf525925130ebc5259251006bf3259251006bc325925101ebf715925101ebe715925101ebc715925101ebf515925101ebe515925101ebd515925101ebc515925101ebf315925101ebe315925101ebd315925101ebc315925101ebf215925101ebe215925101ebd215925101ebc2159251006bf7059251006be7059251006bd7059251006bc705925130ebf5059251006be505925130ebc5059251006bf3059251006be3059251006bc3059251006be2059251006bc205925101ebf105925101eb7105925101ebe105925101ebd105925101ebc1059251036be6495251006bd649525103f3f549525101df67195251005f57195251034ff7655251036be6455251006bd6455251005f7715525101df4715525103f775155251004ff7458e51034fc7458e5101edf7358e51136de5358e51004ff7258e5102cfc7258e51136df3258e5101cfc7158e5101ede3158e5101edc3158e51004ff7058e5100cfe7058e5100cfc7058e51006de3058e51136dc3058e5101ef71058e512a57d76d4e5103e7d76d4e512a73e64d4e512a73d64d4e510167e63d4e510167c63d4e5103d7f71d4e512a57d71d4e5103f7661d4e5112d7e70d4e5103d7c70d4e51014ff7654e51006be6454e51006bd6454e51016de6354e51006dd6354e51005f77154e5101df47154e5103f775154e5129d7f7654e510167f7654e510147f7654e5129f3e6454e5129f3d6454e5103d7f7354e5103f5f7354e510167e6354e5129f5e6354e510165e6354e5129f5d6354e510167c6354e5129d7f7154e51007777154e5129f747154e5103e7e6154e5112d7e7054e5112d7c7054e511375f3054e51034ff76d0e5101cfe76d0e51004fd76d0e51036be64d0e51006bd64d0e51004ff7650e51004fd7650e5101cfc7650e51036be6450e51006bd6450e51004ff7458a51034fc7458a51004ff7358a51014fe7358a51014fc7358a510067f5358a510067d5358a5101eef7258a5101cfc7158a5101e7f5158a5101e7d5158a5101eee2158a5101eec2158a51004ff7058a5100cfe7058a5100cfc7058a510067e5058a510067c5058a51006be6494a51006bd6494a5102eee6294a51006ed6294a5101df67194a51005f57194a5102cff7654a51005bf7454a51005bc7454a51006be6454a51006bd6454a5102eee6254a51006ed6254a51005f77154a5101df47154a5103f775154a51034ff76d0a5101cfe76d0a51004fd76d0a51036be64d0a51006bd64d0a5102cff7690a5101cfe7690a51004fd7690a51036be6490a51006bd6490a51004ff7650a51004fd7650a5101cfc7650a51
  | 37 => 0x8f5103e7c5158f51146df3158f51004ff7058f5100cfe7058f5100cfc7058f51146df3058f51034ff76d0f5103cfe76d0f51004fd76d0f51016de63d0f51006dd63d0f51004ff7650f51004fd7650f5103cfc7650f5101cfc7558b51004ff7458b51034fc7458b51004ff7358b51014fe7358b51014fc7358b5103eef7258b5103eef5258b5103eec5258b51006ef3258b51006ec3258b51006f77158b51004ff7058b5100cfe7058b5100cfc7058b5103d7f7654b510067f7654b510073f7454b510073c7454b510067d6454b510067d6354b5103f6f7254b5102e7e6254b5102e7c6254b51007777154b5101d7e7154b5101d7c7154b51007747154b5101d747154b511ae7e6054b5103e7c6054b51034ff76d0b5103cfe76d0b51004fd76d0b5102eee62d0b51006ed62d0b5101df671d0b51005f571d0b5102cff7690b5103cfe7690b51004fd7690b5103d7e7590b510057d7590b51036be6490b51006bd6490b51004ff7650b51004fd7650b5103cfc7650b51005f77150b5101df47150b5102cff7610b5103cfe7610b51004fd7610b5103d7e7510b510057d7510b51036be6410b51006bd6410b5102eee6210b51006ed6210b5102cff768cb5103cfe768cb51004fd768cb5103d7e758cb510057d758cb51016de638cb51006dd638cb51004ff764cb51004fd764cb5103cfc764cb51005f7714cb5101df4714cb5101cfc7558351004ff7458351034fc7458351004ff7358351014fe7358351014fc7358351004ff725835102cfc725835103ef6515835103ef5515835103efb705835103efb505835103ef8505835113efa105835103ef7515965101e7e515965101e7c515965101ef45159651036bf7599251036be7599251036bc7599251036bf7399251036be7399251036bd7399251036bc7399251316bf5399251006be5399251316bc5399251036bf7299251036be7299251036bd7299251036bc7299251316bf5299251316bc5299251006bf3299251006bc329925101ebf719925101ebe719925101ebd719925101ebc719925101ebf519925101ebe519925101ebd519925101ebc519925101ebf319925101ebe319925101ebd319925101ebc319925101ebf219925101ebe219925101ebd219925101ebc2199251036bf7099251036be7099251036bd7099251036bc7099251316bf5099251006be5099251316bc5099251006bf3099251006be3099251006bc3099251006be2099251006bc209925101ebf109925101ebe109925101ebd109925101ebc109925101ebf7459251004ff7359251014fe7359251014fc7359251006be4359251006bc4359251004ff725925102cfc725925101cfc715925101ebe415925101ebc4159251004ff705925100cfe705925100cfc7059251006be4059251006bc405925101ef71059251006b
  | 38 => 0x6ef7259532004ff7159532006f77159532004f7715953201cfc7159532006f4715953201cf47159532004ff7059532006fb7059532004fb705953200cfe705953200cfc7059532006f8705953200cf870595321c4fe761953203e7e65195320067d6519532034fe76d913203cfe75d9132004fd75d913202cff73d913202cfd73d9132186bf43d9132186bd43d913201cfe71d9132004fd71d913200cfe70d9132004fd70d913200cfc70d9132006bf6499132175ed7299132195ef7259132005f77159132005f47159132004ff755913203cfc7559132006bf7459132174ff7359132006df7359132194ff7259132006ef72591322cebe42591322cebc4259132004ff7159132006f77159132004f7715913201cfc7159132006f4715913201cf47159132004ff705913200cfe705913200cfc7059132184fe7619132036be6419132006bd641913203cff76d5132004fe76d5132004fd76d513203cfc76d5132006bf64d5132036bc64d5132015de73d5132005dd73d513202dee72d5132005ed72d5132034ff7695132004fe7695132004fd7695132034fc76951320073f5495132004ff7655132004fe7655132004fd7655132004fc7655132034ff7615132004fe7615132004fd7615132034fc7615132006bf6415132036bc6415132014fe76d4932014fc76d49320067f65d493203e7c65d4932015de73d4932005dd73d493202f6e52d493203cff7654932014fe76549321b4fd7654932014fc76549320067f655493203e7c6554932005bf7454932005bc7454932005df7354932015dc735493202fcc3254932005f77154932005f47154932014fe76d0932014fc76d0932006bf64d0932036bc64d0932015de73d0932005dd73d0932034ff7650932014fe7650932174fd7650932014fc7650932006bf6450932036bc6450932005df7350932015dc735093203cfe75d8532004fd75d8532034fe74d8532004fd74d853202cfd73d85320b6f631d853200cfe70d8532004fd70d853200cfc70d8532006f76198532005bf7458532005bc7458532005be7418532005bd741853201ef66118532006f5611853200cfe76d813214efa60d813203cfe75d8132004fd75d8132034fe74d8132004fd74d813202cfd73d8132014fd72d813201cfe71d8132004fd71d813214ef850d813214efa30d813214efa20d813214ef8605813201cfc755935103ebf745935103ebf545935103ebc5459351004ff7359351014fe7359351014fc7359351006be4359351006bc4359351004ff725935102cfc725935103e7f5259351004ff705935100cfe705935100cfc705935101cfc7558f51004ff7458f51034fc7458f5103edf7358f5103edf5358f5103edc5358f51146dc4358f51004ff7258f5102cfc7258f5103e7f5258f51146dc3258f5129e7e515
  | 39 => 0xc7550c420373e6550c420373d6550c42035bf7350c420379f7350c42016be6350c42016bc6350c422cdbf7250c422cebe6250c42037ae6250c42285bc7150c42005bf7050c42004ff755844203cfc7558442006bf5458442036bc5458442004ff7358442014fe7358442014fc7358442036bf4358442006bd435844202ebf425844202ebd425844202ef77158442036f74158442036bc4158442036f4415844202ef7215844202eec215844202ef42158442004ff705844200cfe705844200cfc7058442036bf4058442004ff755804203cfc7558042004ff7358042014fe7358042014fc7358042036bf4358042006bd4358042004ff715804201cfc715804202cff705804202efb7058042036fb4058042036f8405804215efa305804202efb205804202ef8205804215efa105804202e7f7559632004ff7459632034fc74596321b67f53596321b67d535963202cfe725963202cfc725963202e7e525963202e7c5259632004ff715963201cfc7159632004ff705963200cfe705963200cfc70596320067e50596320067c505963202eef2059632004ff755923203cfc755923202ebf7459232176bf4359232176bd435923202cfe725923202cfc725923202ebe425923202ebc4259232004ff715923201cfc7159232004ff705923200cfe705923200cfc7059232006be4059232006bc405923203cff76d523202cfe76d5232004fd76d523202cfc76d523203e7e65d52320067d65d523202dee72d5232005ed72d5232034ff769523202cfe7695232004fd769523202cfc7695232036be6495232006bd64952320073f5495232004ff765523202cfe7655232004fd765523202cfc765523203e7e65552320067d6555232036be6455232006bd6455232034ff761523202cfe7615232004fd761523202cfc7615232015de7315232005dd7315232004ff755863203cfc7558632004ff7458632034fc745863202cfc725863202edf325863202edd325863202ef77158632096f6315863202ef7215863202ef42158632004ff705863200cfe705863200cfc7058632004ff755823203cfc7558232004ff7458232034fc745823202cfe725823202cfc7258232004ff715823201cfc715823202efb7058232156fa305823202efb205823202ef82058232156fa105823203cfe76d9532034fe74d9532004fd74d953202cff73d953202cfd73d95321c67f53d95321c67d53d953201cfe71d9532004fd71d953200cfe70d9532004fd70d953200cfc70d95320067f65995321b5ed7299532005bf7459532005bc74595321d5ef7259532005f77159532005f47159532005fb705953214df870595320067f7559532004ff7459532006bf7459532004bf7459532034fc7459532006bc7459532034bc74595321b4ff7359532006df73595321d4ff7259532
  | 40 => 0x944202e7f329944202e7e329944202e7d329944202e7c329944203e7f719944203e7e719944203e7d719944203e7c71994420367f41994420367e41994420367d41994420367c41994420067f31994420067c319944202e7f219944202e7e219944202e7d219944202e7c219944203e7f709944203e7e709944203e7d709944203e7c70994420367f40994420367e40994420367d40994420367c40994420067f30994420067e30994420067c309944202e7f209944202e7e209944202e7d209944202e7c20994420067e10994420067c109944202cff755944202e7f7559442034fe7459442034fc7459442036bc7459442034bc74594420367e54594420367c5459442036bc5459442004ff7359442014fe7359442014fc73594420067e53594420067c535944202cfe725944202cfc725944202e7e525944202e7c5259442004ff715944201cfc7159442004ff705944200cfe705944200cfc70594420067e50594420067c5059442036bf40594420367f74594420367e74594420367d74594420367c74594420363c74594420067f73594420067e73594420067d73594420067c73594420367f43594420367e43594420367d43594420367c435944202e7f725944202e7e725944202e7d725944202e7c725944202e7f425944202e7e425944202e7d425944202e7c425944202e7f325944202e7e325944202e7d325944202e7c32594420067f71594420067e71594420067d71594420067c71594420367f41594420367e41594420367d41594420367c41594420067f31594420067c315944202e7f215944202e7e215944202e7d215944202e7c21594420067f70594420067e70594420067d70594420067c70594420367f40594420363f40594420367e40594420367d40594420367c40594420067f30594420067e30594420067c305944202e7f205944202e7e205944202e7d205944202e7c20594420067e10594420067c1059442035bd76d504231ebd76d5042035be75d50420373e75d5042036bf65d50420373e65d504231ebd65d50420373d65d50420063d65d5042005bd73d5042375bf72d5042375bd72d5042376be62d5042037ae62d50423773f52d50423773d52d5042285be71d5042005bd70d5042004ff7558c4203cfc7558c4202cff7358c4202edf7358c42036df4358c42036dc4358c4202cfc7258c4202ede3258c4202edc3258c42004ff7158c4201cfc7158c42166df3158c42004ff7058c4200cfe7058c4200cfc7058c42036bf4058c42166df3058c4203cff76d4c4202cfe76d4c42004fd76d4c4203e7e65d4c420067d65d4c42035bc74d4c421675e53d4c42004ff7654c42004fd7654c4202cfc7654c4203e7e6554c420067d6554c42005bf7454c42035bc7454c42035bf7650c42196bf7650c4231dbe7550c4231db
  | 41 => 0x2ef7215864202ef42158642004ff705864200cfe705864200cfc7058642004ff755824203cfc7558242004ff7358242014fe7358242014fc7358242006bf4358242006bd435824202cfc7258242004ff715824201cfc715824202efb705824217efa405824202efb205824202ef8205824217efa105824203cfe76d9542014fe73d9542004fd73d9542014fc73d954201cfe71d9542004fd71d954200cfe70d9542004fd70d954200cfc70d95420067f6599542376bf6499542005f77159542005f471595420067f7559542004ff7459542006bf7459542004bf7459542004ff7359542014fe7359542014fc7359542004ff7259542006ef7259542004ff7159542006f77159542004f7715954201cfc7159542006f4715954201cf47159542004ff705954200cfe705954200cfc7059542004fe761954203e7e65195420067d651954236ebf641954202cfe76d514202cfc76d51420067f65d514203e7c65d51420373e54d514202dee72d5142005ed72d514202cfc76551420067f655514203e7c6555142005ef725514202dec7255142037ac4255142014fe76d8d42176de63d8d4203cfe75d8d42004fd75d8d4202cfd74d8d42176de43d8d42034fd72d8d422d6be42d8d422d6bc42d8d42176df32d8d4201cfe71d8d42004fd71d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42176dc6358d42005f77158d42005f47158d42004fe76d4d42004fd76d4d4203cfc76d4d42035be74d4d42005bd74d4d421775e53d4d4202dee72d4d42005ed72d4d42004ff7654d42004fe7654d42004fc7654d4202cfc7650d42006df6350d42016dc6350d420379c4350d42005ef7250d4202dec7250d42034fe76d4942034fc76d49420067f65d494203e7c65d4942035be74d4942005bd74d494202f6e52d494203cff7654942004fd7654942034fc76549420067f655494203e7c6554942005bf7454942035bc745494202fac4254942005f77154942005f4715494203cfe75d8542004fd75d8542014fe73d8542004fd73d8542014fc73d8542006f731d8542006f431d854200cfe70d8542004fd70d854200cfc70d8542006f7619854228ebf6418542296ef621854201ef66118542006f5611854200cfe76d814216efa60d814203cfe75d8142004fd75d814202cfd74d8142014fe73d8142004fd73d8142014fc73d8142034fd72d8142336be42d8142336bc42d814201cfe71d8142004fd71d814216efa40d814216efa20d814216ef860581420367f74994420367e74994420367d74994420367c749944203e7f739944203e7e739944203e7d739944203e7c73994420367f43994420367e43994420367d43994420367c439944202e7f729944202e7e729944202e7d729944202e7c729944202e7f429944202e7e429944202e7d429944202e7c429
  | 42 => 0xf7454b42035bc7454b4202fae4254b42005f77154b42005f47154b42004ff755874203cfc755874202cfc7458742004ff7358742014fe7358742014fc7358742036f77158742036f74158742036f44158742004ff705874200cfe705874200cfc7058742004ff755834203cfc755834202cfc7458342004ff7358342014fe7358342014fc73583422bebe4258342036bc4258342004ff715834201cfc7158342036bf4158342036fb7058342036fb4058342036f8405834218efa205834202e7f7559642006bf7459642004ff7359642014fe7359642014fc735964202cfc725964202e7e525964202e7c5259642004ff715964201cfc7159642004ff705964200cfe705964200cfc70596420067e50596420067c5059642036ef425924202ebe425924202ebc425924202eec425924203e7e65d52420067d65d52420373e54d524202dee72d5242005ed72d5242375bd76d5242326bd76d5242035be75d5242376bf65d52423773e65d5242326bd65d52423773d65d52420063d65d5242005bd73d5242377ae72d5242375bd72d5242327ad72d5242005ad72d5242036be62d52423773f52d52423773d52d524228dbe71d5242005bd70d524203cff765524203e7e65552420067d6555242005ef725524202dec7255242037af425524236dbd7615242036bd76152420373e751524236ebf6515242326bd6515242005bd7315242035bf721524236dbd7215242037ae621524228dbe7115242005bd7015242004ff7558e4203cfc7558e4202edf7358e42186de5358e42186de4358e4202cfc7258e4202ede3258e4202edc3258e42004ff7158e4201cfc7158e42186df3158e42004ff7058e4200cfe7058e4200cfc7058e42006de3058e42186dc3058e4203cff76d4e4202cfe76d4e42004fd76d4e4203e7e65d4e420067d65d4e421875e53d4e4202dee72d4e42005ed72d4e42004ff7654e42004fd7654e4202cfc7654e4203e7e6554e420067d6554e42005bf7454e42035bc7454e42016de6354e42006dd6354e422d5bd76d0e42036bd76d0e42325be75d0e42035bc75d0e42016be63d0e42016bc63d0e42035bf72d0e422d5bd72d0e42037ae62d0e4228dbe71d0e42005bd70d0e42014ff7650e42016de6350e42006dd6350e42005ef7250e4202dec7250e422cdbf7650e42016bf7650e42014bf7650e42325be7550e42325bc7550e42035bf7350e420379f7350e42016be6350e422cf9e6350e420169e6350e422cf9d6350e42016bc6350e422cdbf7250e42007af7250e422cfac7250e42036be6250e4228dbc7150e42005bf7050e42004ff755864203cfc7558642006bf5458642006bc5458642004ff7358642014fe7358642014fc7358642006bf4358642006bd435864202cfc725864202ebf425864202ebd425864202ef77158642
  | 43 => 0x8552246f45018552006745018552006f64018552006f44018552006f73018552006f63018552006f4301855238ef72018552006f6201855238ef4201855200cfe76d815203d7e75d8152006bf64d8152006bc64d8152006f761d8152006f461d81521aefa60d81521af7a50d815202cfd75d815202c7d75d8152034fe74d8152004fd74d8152014fe73d8152004fd73d8152014fc73d81520067f53d81520067d53d815203cfd72d815201cfe71d8152004fd71d81521ae7e50d81521aefa50d81521ae7c50d8152006fb30d81521aef830d81521aefa20d8152005bf7458152005bc7458152006bf6458152006bc6458152005df73581521b5dc7358152005f77158152005f47158152006f76158152006f461581521aef8605815202ebf745905203ebf545905203ebc5459052004ff7359052014fe7359052014fc7359052006be4359052006bc435905202e7f525905202e7d525905202ebe425905202ebc4259052004ff715905201cfc7159052004ff705905200cfe705905200cfc7059052004ff7458c52034fc7458c5202cff7358c5202edf7358c5203edf5358c5203edc5358c521a6dc4358c5202cfc7258c5202e7f5258c5202e7d5258c5202ede3258c5202edc3258c52004ff7158c5201cfc7158c521a6df3158c52004ff7058c5200cfe7058c5200cfc7058c521a6df3058c52034ff76d0c5202cfe76d0c52004fd76d0c52016de63d0c52006dd63d0c52004ff7650c52004fd7650c5202cfc7650c52004ff7458452034fc7458452004ff7358452014fe7358452014fc735845202e7f525845202e7d525845202ef7715845203ef7515845203ef4515845202ef7215845202ef42158452004ff705845200cfe705845200cfc7058452004ff7458052034fc7458052004ff7358052014fe7358052014fc735805202eee525805203eed5258052004ff715805201cfc715805202cff705805202efb705805203efb505805203ef8505805202efb205805202ef8205805219efa10580520367f755974202cfc74597420367e54597420367c5459742004ff7359742014fe7359742014fc7359742004ff715974201cfc7159742004ff705974200cfe705974200cfc7059742004ff7558f4203cfc7558f4202cfc7458f42036df7358f42196de5358f42036df4358f42036dc4358f422cebe4258f42036bc4258f42196df3258f42004ff7158f4201cfc7158f42036bf4158f42004ff7058f4200cfe7058f4200cfc7058f42006de3058f42196dc3058f4203cff76d4f42034fe76d4f42004fd76d4f42035be74d4f42005bd74d4f421975e53d4f42004ff7654f42004fd7654f42034fc7654f42016de6354f42006dd6354f4203e7e65d4b420067d65d4b42035be74d4b42005bd74d4b4203cff7654b4203e7e6554b420067d6554b42005b
  | 44 => 0x36bc6450d52006bf64d8552006bc64d8552034fe74d8552004fd74d8552014fe73d8552004fd73d8552014fc73d8552006f731d8552006f431d855200cfe70d8552004fd70d855200cfc70d8552006f610d8552006f410d855235f7775d8552006f764d8552007b764d8552006b764d8552006f664d8552006f564d8552006f464d8552007b464d8552006b464d85520077754d85520077554d8552006f763d8552006f663d8552006f563d8552006f463d85520077753d85520077553d855224fe752d855235f7652d855235f7452d855224fe452d8552006f660d8552006f460d85520077650d85520077450d855235ef775d855224ef675d8552006f774d8552006f674d8552006f574d8552006f474d855224ef754d8552006f654d8552006f554d855224ef454d8552006f773d8552006f673d8552006f573d8552006f473d855224ef753d8552006f653d8552006f553d855224ef453d8552006f743d8552006f643d8552006f543d8552006f443d855224ef772d855235ef672d855224ef752d855235ef652d855235ef452d855235ef642d855235ef442d8552006f732d855235ef632d855235ef432d8552006f770d8552006f670d8552006f570d8552006f470d855224ef750d8552006f650d855224ef450d8552006f640d8552006f440d8552006f730d8552006f630d8552006f430d855235ef720d8552006f620d855235ef420d8552005be7498552005bd7498552006bf6498552006bc6498552006f76198552005bf7458552005bc7458552006bf6458552006bc6458552006bf6418552006bc641855201ef66118552006f56118552005f67618552006f67618552007757518552006f76418552007b76418552006b76418552006f66418552006f56418552006f46418552007b46418552006b46418552007775418552007755418552006f76318552006f66318552006f56318552006f46318552007775318552007755318552247e7521855238f76521855238f745218552247e45218552006f66018552006f4601855200776501855200774501855201ef7751855201ef6751855201ef4751855201ef7741855201ef6741855201ef5741855201ef47418552246f75418552006f65418552006f55418552246f4541855201ef7731855201ef6731855201ef5731855201ef47318552246f75318552006775318552006f65318552006f55318552006755318552246f45318552006f74318552006f64318552006f54318552006f4431855201ef7721855201ef6721855201ef47218552246f7521855238ef65218552006f5521855238ef4521855238ef6421855238ef44218552006f7321855238ef6321855238ef4321855201ef7701855201ef6701855201ef5701855201ef47018552246f75018552006f6501855200676501
  | 45 => 0xf5319152006be531915231ebc5319152036bf7219152036be7219152036bd7219152036bc721915231ebf521915236ebe5219152006bd521915236ebc5219152006bf321915236ebe321915236ebc3219152036bf7119152036be7119152036bd7119152036bc711915231ebf511915231ebc5119152006bf3119152006bc311915236ebf211915236ebc2119152036bf7019152036be7019152036bd7019152036bc701915231ebf5019152006be501915231ebc5019152006bf3019152006be3019152006bc301915236ebf2019152006be201915236ebc2019152006be1019152006bc10191520057e76d515203e7e76d51520073f64d51520367e64d51520367c64d51520073c64d51520363c64d51520057d73d515202d7e72d515202d7c72d515203e7f62d515203f6f62d51520057d71d51521ad7e70d515203d7c70d515202cfe76951520057d7595152006bf6495152036bc649515203f3f549515202dee7295152005ed729515202cfc7655152006bf6455152036bc6455152005ef725515202dec725515202c7c765515203d7f745515203f3f74551520073f64551520367e64551520367c64551520073c64551520057f73551520076f725515202d7e725515202d7c72551520076c725515203e7f625515203f6f62551520057f71551521ad7e70551521ad7c7055152014fe76d8d52006bf64d8d52006bc64d8d521b6de63d8d5202cfd75d8d52034fe74d8d52004fd74d8d521b6de53d8d5203cfd72d8d521b6df32d8d5201cfe71d8d52004fd71d8d5200cfe70d8d52004fd70d8d5200cfc70d8d52006de30d8d521b6dc30d8d52005bf7458d52005bc7458d52006bf6458d52006bc6458d521b6dc6358d52005f77158d52005f47158d52005fb7058d521adf87058d520057e76d4d5203e7e76d4d520057d74d4d520073f64d4d520073c64d4d521b57d73d4d520167e63d4d520167c63d4d5202d7e72d4d5202d7c72d4d5203e7f62d4d5203f6f62d4d520057d71d4d522a67c61d4d521ad7e70d4d5203d7c70d4d5202cfc7654d52006bf6454d52006bc6454d52006df6354d52016dc6354d52005ef7254d5202dec7254d5202d7c7654d520167c7654d5202c7c7654d520057f7454d520073f6454d520073c6454d5203d7f7354d5203f5f7354d520075f6354d520167e6354d520167c6354d521b75c6354d520165c6354d520076f7254d5202d7e7254d5202d7c7254d520076c7254d5203e7f6254d5203f6f6254d520057f7154d5229e7c6154d521ad7e7054d521ad7c7054d521b75f3054d52004fe76d0d52004fd76d0d52034fc76d0d5203d7e75d0d520057d75d0d52006bf64d0d52036bc64d0d5202dee72d0d52005ed72d0d52004ff7650d52004fe7650d52004fc7650d5203d7e7550d520057d7550d52006bf6450d52
  | 46 => 0x925202e7d525925202ebe425925202ebc4259252004ff715925201cfc7159252004ff705925200cfe705925200cfc7059252036be6495252006bd649525203f3f549525202dee7295252005ed7295252034ff7655252036be6455252006bd6455252005ef725525202dec725525203f6f5255252004ff7458e52034fc7458e5202edf7358e521c6de5358e5202cfc7258e5202e7f5258e5202e7d5258e5202ede3258e5202edc3258e52004ff7158e5201cfc7158e521c6df3158e52004ff7058e5200cfe7058e5200cfc7058e5202eef2058e52014ff7654e52016de6354e52006dd6354e5203f5c5354e52005ef7254e5202dec7254e5203f6f5254e52034ff76d0e5202cfe76d0e52004fd76d0e5202dee72d0e52005ed72d0e52004ff7650e52004fd7650e5202cfc7650e52004ff7458652034fc7458652004ff7358652014fe7358652014fc735865202cfc725865202e7f525865202e7d525865202ef7715865202ef7215865202ef42158652004ff705865200cfe705865200cfc7058652004ff7458252034fc7458252004ff7358252014fe7358252014fc735825202cfc7258252004ff715825201cfc715825202efb70582521befa505825202efb205825202ef820582521befa1058252014fe73d9152004fd73d9152014fc73d9152006be43d9152006bc43d915201cfe71d9152004fd71d915200cfe70d9152004fd70d915200cfc70d9152006be40d9152006bc40d91523773f75d9152006be63d9152006bc63d9152327af52d91523773e52d91523773c52d9152327ac52d9152006be60d9152006bc60d91520073e50d91520073c50d9152376bf75d9152326be75d9152006bf73d9152006be73d9152006bd73d9152006bc73d9152326bf53d9152006be53d9152326bc53d9152326bf72d9152376be72d9152006bd72d9152326bf52d9152376be52d9152376bc52d9152006bf32d9152376be32d9152376bc32d9152006bf71d9152006be71d9152006bd71d9152006bc71d9152326bf51d9152326bc51d9152006bf31d9152006bc31d9152376bf21d9152376bc21d9152006bf70d9152006be70d9152006bd70d9152006bc70d9152326bf50d9152006be50d9152326bc50d9152006bf30d9152006be30d9152006bc30d9152376bf20d9152006be20d9152376bc20d9152006be10d9152006bc10d9152006bf6499152005f67199152005f57199152005f77159152005f47159152036be6419152006bd6419152005be7619152006be76191520073d7519152006be6319152006bc631915231faf521915236f3e521915236f3c521915231fac5219152006be6019152006bc60191520073e50191520073c5019152036bf7519152036be7519152036bc7519152036bf7319152036be7319152036bd7319152036bc731915231eb
  | 47 => 0x14fe76d5143014fc76d51430067f65d514303e7c65d51430373e54d5143015de73d5143005dd73d514303cff7655143014fe7655143214fd7655143014fc76551430067f655514303e7c6555143005df7355143015dc73551430379c435514303cfe75d8943004fd75d8943196bd74d8943034fd73d8943196ee32d894301cfe71d8943004fd71d894300cfe70d8943004fd70d894300cfc70d8943006ef6298943005f77158943005f471589430057e75189430057d751894302eee6218943006ed621894303cfe75d8543004fd75d8543034fd73d854302cfe72d8543004fd72d8543106f631d854300cfe70d8543004fd70d854300cfc70d8543006f76198543005ef7258543005ec725854301ef66118543006f5611854300cfe76d81431defa60d814303cfe75d8143004fd75d8143014fd74d8143034fd73d814302cfe72d8143004fd72d814301cfe71d8143004fd71d81431def850d81431defa40d81431defa30d81430057f75581430057c75581431def8605814302cfc755935203ebf745935203ebf545935203ebc5459352004ff7359352014fe7359352014fc7359352004ff715935201cfc7159352004ff705935200cfe705935200cfc705935203d7f76553520067f765535203f3f74553520367e64553520367c64553520057f735535202d7e725535202d7c72553520057f71553521cd7e70553521cd7c705535202cfc7558f52004ff7458f52034fc7458f5203edf7358f5203edf5358f5203edc5358f521d6de4358f521d6df3258f52004ff7158f5201cfc7158f521d6dc3158f52004ff7058f5200cfe7058f5200cfc7058f521d6df3058f5203d7f7654f521a67f7654f520057f7454f5203f5f7354f520167e6354f520167c6354f5202d7e7254f5202d7c7254f520057f7154f5229e7e6154f521cd7e7054f521cd7c7054f521d75f3054f52034ff76d0f5203cfe76d0f52004fd76d0f5203d7e75d0f520057d75d0f52036be64d0f52006bd64d0f52004ff7650f52004fd7650f5203cfc7650f5203d7e7550f520057d7550f52036be6450f52006bd6450f52016de6350f52006dd6350f5202cfc7558752004ff7458752034fc7458752004ff7358752014fe7358752014fc735875203ef7715875203ef7515875203ef45158752004ff705875200cfe705875200cfc705875202cfc755835202c7c7558352004ff7458352034fc7458352004ff7358352014fe7358352014fc735835203e7f53583520067d535835203eee525835203eed5258352004ff715835201cfc715835203efb705835203efb50583521ce7e505835203e7c505835203ef850583521cefa205835203eef525965202e7e525965202e7c525965202eec525965202ebf7459252004ff7359252014fe7359252014fc735925202cfc725925202e7f525
  | 48 => 0xd70d915300cfc70d9153006be40d9153006bc40d9153006bf6499153005fb70591531edf87059153036be6419153006bd6419153014fe7695153006bf6495153036bc649515303f3f5495153015de7395153005dd739515303f5c5395153014fc7655153006bf6455153036bc6455153005df7355153015dc7355153034fe74d8953004fd74d895303cfd73d89531d6ee32d895301cfe71d8953004fd71d895300cfe70d8953004fd70d895300cfc70d8953006ef6298953005bf7458953005bc7458953005f77158953005f47158953005fb70589531edf8705895302eee6218953006ed62189531467d75d8553034fe74d8553004fd74d855303cfd73d855302cfe72d8553004fd72d8553146f631d855300cfe70d8553004fd70d855300cfc70d8553005be7498553005bd7498553006f761985531edfa7098553005f9709855301ef66118553006f5611855300cfe76d81531eefa60d8153014fd75d8153034fe74d8153004fd74d815303cfd73d815302cfe72d8153004fd72d815301cfe71d8153004fd71d81531eefa50d81531eef840d81531eefa30d81531eef820d81531eefa10d8153005bf7458153005bc74581531eef860581530367f7559743014fe7459743014fc74597430367e54597430367c54597432167f53597432167d5359743004ff725974302cfc7259743004ff715974301cfc7159743004ff705974300cfe705974300cfc7059743036bf4059743004ff7558b4303cfc7558b43014fc7458b43036bc7458b43014bc7458b43036ef7258b43036ef4258b43036bc4258b43036ec4258b43176ee3258b43004ff7158b4301cfc7158b43036bf4158b43004ff7058b4300cfe7058b4300cfc7058b43004ff755874303cfc7558743014fc7458743004ff725874302cfc7258743036f77158743036f74158743036f441587430e6f63158743004ff705874300cfe705874300cfc7058743036bf4058743004ff755834303cfc7558343014fe7458343014fc7458343004ff725834302cfc7258343036bc4258343004ff715834301cfc7158343036bf4158343036fb7058343036fb4058343036f840583431e6fa30583431e6fa105834303cfe76d9543034ff73d9543034fd73d95432267f53d95432267d53d954302cfe72d9543004fd72d954301cfe71d9543004fd71d954300cfe70d9543004fd70d954300cfc70d95430067e50d95430067c50d95430067f6599543215bd7499543235bf7459543005fb70595431ddf870595430067f7559543234ff7459543006bf7459543214ff7359543006df7359543004ff725954302cfc7259543004ff715954301cfc7159543004ff7059543006fb7059543004fb705954300cfe705954300cfc7059543006f8705954300cf87059543224fe761954303e7e65195430067d6519543
  | 49 => 0x8954006ed6218954316bf54d8554316bc54d8554014fe73d8554004fd73d8554014fc73d855402cfe72d8554004fd72d855400cfe70d8554004fd70d855400cfc70d8554006f76198554005ef7258554005ec725855401ef66118554006f5611855400cfe76d815420efa60d8154034fd75d815403cfd74d8154014fe73d8154004fd73d8154014fc73d815402cfe72d8154004fd72d815401cfe71d8154004fd71d815420efa50d815420efa40d8154006fb30d815420ef830d8154005df7358154215dc735815420ef86058154034ff7358c54036df7358c5403edf5358c5403edc5358c54036df4358c54036dc4358c54004ff7258c5402cfc7258c54036bc4258c54206dc3258c54004ff7158c5401cfc7158c54036bf4158c54206df3158c54004ff7058c5400cfe7058c5400cfc7058c54206df3058c540367f54588540367d5458854004ff7358854014fe7358854014fc7358854036ef725885403eef525885403eec5258854036ef4258854036bc4258854036ec4258854036ac4258854006ef3258854006ec3258854004ff715885401cfc7158854036bf4158854004ff705885400cfe705885400cfc7058854004ff7358454014fe7358454014fc7358454004ff725845402cfc7258454036f7715845403ef7515845403ef45158454036f74158454036f44158454004ff705845400cfe705845400cfc7058454036be545805403ebd5458054004ff7358054014fe7358054014fc7358054004ff725805402cfc7258054036bc4258054004ff715805401cfc7158054036bf4158054034ff7058054036fb705805403efb505805403ef85058054036fb4058054036f840580541fefa1058054014fc755935303ebf745935303ebf545935303ebc5459353216bf4359353004ff725935302cfc725935303e7f5259353004ff715935301cfc7159353004ff705935300cfe705935300cfc7059353014fc7558b53004ff7458b53006bf7458b53004bf7458b53034fc7458b53006bc7458b53034bc7458b5303eef7258b5303eef5258b5303eec5258b531b6ee3258b53004ff7158b5301cfc7158b53004ff7058b5300cfe7058b5300cfc7058b53014fc755875303e7c75587530147c7558753004ff7458753034fc7458753004ff725875302cfc725875303e7f525875303ef7715875303ef7515875303e7c515875303ef45158753126f63158753004ff705875300cfe705875300cfc7058753014fe7558353014fc7558353004ff7458353034fc745835303ede535835303edd5358353004ff725835302cfc7258353004ff715835301cfc715835303efb705835303efb505835303ef850583531f6fa3058353034fe76d915303cfd73d9153236bf43d915302cfe72d9153004fd72d915301cfe71d9153004fd71d915300cfe70d9153004f
  | 50 => 0x14fc7358b5403eef7258b5403eef5258b5403eec5258b54004ff7158b5401cfc7158b54004ff7058b5400cfe7058b5400cfc7058b54034fc7558754004ff7358754014fe7358754014fc7358754004ff725875402cfc725875403e7f525875403ef7715875403ef7515875403ef45158754004ff705875400cfe705875400cfc7058754034fc755835403ebe545835403ebd5458354004ff7358354014fe7358354014fc7358354004ff725835402cfc7258354004ff715835401cfc715835403efb705835403efb505835403ef8505835422efa405835403ebf54596540367e54596540367c5459654036bc54596540373d76d52540353d76d525403e3d76d525403f3f73d525403f3e73d525403f3d73d525403f3c73d52540373f63d52540373e63d52540373d63d52540373c63d525403f3f72d525403f3e72d525403f3d72d525403f3c72d52540373f62d52540373e62d52540373d62d52540373c62d52543a73f32d52543a73c32d525403f3f71d525403f3e71d525403f3d71d525403f3c71d52540373f61d52540373e61d52540373d61d52540373c61d52543a73f31d52543a73c31d525403f3f70d525403f3e70d525403f3d70d525403f3c70d52540373f60d52540373e60d52540373d60d52540373c60d52543a73f30d525439f3e30d525439f3c30d525439f3e20d525439f3c20d525439f3e10d525439f3c10d5254034fc7458e54036df7358e54226de5358e54036df4358e54036dc4358e54004ff7258e5402cfc7258e54004ff7158e5401cfc7158e54004ff7058e5400cfe7058e5400cfc7058e54036bf4058e54034fc7458a540367f5458a540367d5458a54004ff7358a54014fe7358a54014fc7358a54036ef7258a54036ef4258a54036ec4258a54004ff7158a5401cfc7158a54004ff7058a5400cfe7058a5400cfc7058a54034fc745865430ebf5458654036bc5458654004ff7358654014fe7358654014fc7358654004ff725865402cfc7258654036f77158654036f74158654036f44158654004ff705865400cfe705865400cfc7058654036bf4058654034fc7458254004ff7358254014fe7358254014fc7358254004ff725825402cfc7258254004ff715825401cfc7158254036fb705825421efa5058254036fb4058254036f84058254014fe76d8d54216de63d8d54034fd75d8d5403cfd74d8d54216de53d8d54216de43d8d5402cfe72d8d54004fd72d8d5401cfe71d8d54004fd71d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54006de30d8d54216dc30d8d54216dc6358d54005fb7058d5420df87058d54014fe73d8954004fd73d8954014fc73d895401cfe71d8954004fd71d895400cfe70d8954004fd70d895400cfc70d8954006ef6298954005f77158954005f47158954376bf641895402eee621
  | 51 => 0x180080000000000100000002000800100010000000c00180000002000000000000000000800080030000000000000020004000800200020004000000280050004000000580000000000800000020010000800080000000000000880010000000000000010002000000080010000000800780010008000c0010010000000000000001000000000000001000200000000001000200100010004000000000000001000000080000000000a00080000000000600180000001000800040000000000c00100010005000e000000000000002000000180030000001400000000000000400080000002000800000010000000800000000012000000000010000000400180000000000000000010000000400280000000000c00080010000000000000010000000400080040000002000000000004001400000000008000000080010008000400100000000000000000000006000c0010002000000000020000000a00000010000000c00000040002000600140000000000400000010001000600000018003000a000400080000004000400280070004000400880100004000000180010004000400000000002000c0000002000400000010001000000000008000000200000060001000200000000004002600080000002000400000010001000600000000001000000040018002000000040000000000400040000001000400000018001000000040060002000200080000001000200000038005000000040008003000000040000005000400040008002000c0018001000b000e000800280000002000800080000000000000100010004000000500000004000400000000000001000000000014003000300000000001000000010000004400080010004000400000010002001000080000002000400a8002000200040018000000000100008000000000040000000000c000800480000000000800000040004000400180030000000000000010002000000480060008000000000000004000c0048001000200000000002000400000008001000000040010000000400080000007000000000028000000a000000500000010000000480020002000000580010008000000000000006000000000010000000800000070000000000000000004001c0040000000000000008012000200040010003000200000000005000000080010001000000100050002000800040008003000000000028000000400140008000000000080000008000400000000000000000000018000034fc7558f5403edf7358f5403edf5358f5403edc5358f54236de4358f54004ff7258f5402cfc7258f5403e7f5258f54236df3258f54004ff7158f5401cfc7158f54236dc3158f54004ff7058f5400cfe7058f5400cfc7058f54236df3058f54034fc7558b54004ff7358b54014fe7358b54
  | 52 => 0x8001000000040008000000000000000001000600000028000000400040000000000200040018000000800000000004000000080008000000200040000000000e000000000030000000800180040004000000000000008001400000000000001c0000000000800040000000000000000008002000e00000000008000000000060000000000140010002000000000030005000000080008003000000000018003000200040010000000400000000001000200000010002000400080018003000800000020000000200000018001000000000018000000200200018002000c000c0000003000800040030004000000040018000000000040028000000400040000001000000000008000000000000008000000200000000000000400180000000000000000030000000c00000008000000200140008000000400040008000000200080010001000400000020000000400300000000000000000000002000c000000100040000000000000060000000000080030008001800600020000001000000030002000c00080070000000000000030002000c00080010004001800000000006000000000010000000000100080006002000000000004001400000020002000c00000000004000c0028000000200000000001000c000000180030000001000380040000000400100000006000c0020003000000000020007000000140020010000000000000002000400000000003000200080008002000a0014000800200000004000000700000010000800d0000000000100000008000400000000010001000080010000000c00080040000000000000070002000400180000002000000080010018000000000070010000400000010000000000000000000001800000080000000400580000000000000000000000000000000050000002c00080000000000c00080080000000c00000020000000400000020008000000080020002000000080010002001800080010000001c00000000000000800100010014000000500010006000800000000002000c000800000080020001800500080000006000000040000002000000020008003800000000000000800400000000001800100040000000000b0002002c0010001000000000018000000000080028002000e000000080000000002000000030000000400080010002000000000010002000000000000000000c00000010000000800500000006001400100000000001800300000000000c00000040002000c0000000000400440018001000600040040000000200400000002000000000000000000600100000001000000000000001000c000c00380010008000800080050000000000080020000000400000010002002000200030002000000080040000000000080000000000400080030000000000
  | 53 => 0x100020004000400200000000000400000010004000000180010008002400080000004000000100010000000c0008001000200000008004000e00140038001000e0000001800f000e00000010000000000040038000000800040000000000000000030000000200000000006000200000060003000200040010000000200040000003000400040038000000200000010000000000080000000000c000000080020000000400000030004000000000010002000400280180000001000000020004000400200000000001400000000000000000100000000000400000080002000400000000000000000080060002000000000000000000000180010002000000200010002000400000000002000000080000000000000280000004001400000000000000c00000030016003c00000020000001800200000000003c000000200080004000800d000c000800080010000001800180010002000c0000000000600000000000000200000030000000000000040002000000040000002001000040008001000000000000001000000100010000000600080000000001a000c00100000000000000000010000002000a00020012000400080020002000000480050004000c0060001000200000010001000400000008001000600040028000000000040018004000600000020001000600040000000000000000030007000000040008001000800040000001000000000000002000000180000001000000000028001000c000000200000004000000000080006000c00000010000001000280000004000000100000008000000280090006000000000010002000400000030000000000000000000000c0000003000000280000003000600000000001000000240000000000400040008000000000000000001000200000010000000200000048003000200000000009000200100000001001200000028001000000000000005000000040000000001a00000010000000c00180000002000000000020001000800000058000000000000000001000a00000000000000800000000001000a000000080000002003c00000000008000400200000000001c0000004000200000008000000200180010007000200040000004000600000008002000c001400000000000000000000030000000400100000002000000000030004000000100070000000400000000000000000100020000000800000000010000c00000000006000400000000004000400180040002000400b8007000400040028000000200000028000000c00140008000000600100008004000c00000090000001400000030000000800000020000000200180018000001200000000000000200080030002000600140038000000400000018000000000040000001000c0000006000300160000001800c00
  | 54 => 0x200080000008000000000000000000200040008000000400140000000000000180000000000200000000000000400080000000000000000040008000800100018001000200040008000000200000040000000a000400000000008000000080000006000000000000000000000080010002000800080010002000000080000002000c000000100020004001800b0002001c003800100020008000800000000000005800000020000000000e000000000030000000200000000000000000080000003000000080008000000a00000000001000000040008002000800040000000000200040000003000e001400180020000000000080000000000000300000008000000080030000000000080000000001c001800000000000000800e00100008000000200000004000000000000008000000100060008001000000000000000800000020000000800a000000000028001000c000000a00000000000000080020000000400280010002001000100000010000000000000006001400100010002000800080010000000000000010000000400000000002000400000000000000400000010004000c00100020000000000000000002000000000000002000000180010004000000080000002000c009000200000004000000200020010002000000040004000000700000004000800c000200040000002000200180008005000000000040001000000040000000000c004c0018000000800000008000000c00300000000000000040008006000a00000000004000200000008001000800000000001001000000000000000000000000000000600000000000000600040010001000800000000007000000040020000000200100000000000000000000000000c000800180030004000000000000002000000180010002000400000010004000400200010000000000000000008000000500000000000c00000000002001800000060000000800280000000000000000030004000000000020006000c0000003000600000030003000600000018000000a000000100000000000000000000002000c0000000000600040018000000800000000001000200040010002000000000000000000000000000001000000040040001000a0018000800e000000040000000000400040010001000000040000002000a000400000070000000400180000014001800100000002000c00100000000000800180010000000000180060000000000100000000000000000010000000800000020000001000000010006000400380010004000400080000000000000000020004000400000000008000000100010002000000300000002000400000000002000000100000004001400000000000000400b8001000600000000000000a00080000000000000040008001000000280
  | 55 => 0x60000000c00000000000000000000000000000000000000000001c0000000001400040000000001600040000002000000000000002000200040000001000000200028001000200240020000000000200008000000400040008000000000140000000000000000010000000000000000000000200000000007000800040048002000600000018004000800000020000000600080000000002e0008002000e0000000400180030000000000600000000000000900000004000000280010008000c0008001000e000000100020002000c0000002000600080000001000a002000080000002000000000000008000000080000004001000000000000000000080010002001800080050004000c000800b0018000000500030000000800080030002002000000060002000000200000000000000200000002000c00000020008000000080000000000400080040000000400900010000000000080000002000c00100000000000000180030000001000000000000000c00000010000000c000000300020000003000000040000000000700100050000000100020014000000e000600100030000000200000000000000000000010001000200100000000000800040008001000000040010006000000080048001000c000400000050002001c00180030004001000100000004000400100020004000000000000000000000000000002000800000000000000c0000005000200080010000000e000c0010000000000040000006000200080000002000a000000000000004000000100000000002000000000000000800000010000000000080000002000000180000000000000400020002000000180010000000800600000000000000080030000000000000000004001c0010000001200000008001000a000000000050000000000280000006000000000000000000800500030004000000180000008000000000000000000000000000000001400100000002000000000030000000400000000000000000000010000002c00000010000000000100020002000400200010000000000000000004000000300000004002c0000000000200040000000000e00040008000000000000028000000000040018000000000000008000000200040020000000400040000001000200040008001000000040000002000000000008000000000040050000000000340020001000e000400000010000000800280010002000800000000000000400080090000000400080000002000000000020000000400000000002000c0008000000e000000000030006000000000040002000000300000006001000280010000000000080000000000000080040000000800000060008000c00080010002000c00200010006000400000020000000000000000008000000100020
  | 56 => 0x6f9cf03000000002f8889983730550422c0f88d6a0ed64d9806184810ae400001672082399a874803f80002d760000246800036ac000000000000000000060d000000000000000000018d40000b4b00000000831c000149f43324eac95b9ff50000000028600000000000095600002be4409c000056a38e80c88cd70d6b379222b492e899d0000597048500001eae000061d0ddc2d225f7800005fd0000000010e8000277c8184b891a54000000000001d403e96139108b0000000019f42a080000000000000008de000000000000000000000000000000215c07bc0000745000000003569724381e63840001f7200005eb80001dff0fa40000e0f00000a425ebc8a70376000087bc5bd83fd00000000000158a214a11e8c9c874103a00000a2c09c3000051b053280000000000000000000000000028c0000000000000000000435046100001ae83fae3adc26f0d6e234472450b1a0b12d3c0000f55000000000000e7a1960000000000000000000014240001c930000192106f0c7013287760000207434a648944e896c800004950873000000001758f810770000000004a38000000000000000cbd0000000000000004346000000000003fa0000063a11543d462b2cada800000003d1c0000000000000000000000000000001998934000000004508000000017000000000106c346c00005762d7a000082300000000000000000002ed85ad4000209629fc2e880000d84000032a0000000032a052c4713957440f47bf000000001f1e0000000000005200b40c2b19ba000000000000000095054dc00000008000000000040000003000600040000001001c00040020000000400000018001000200000008002000000000000001000000040028000001200040008004000000180010000000a000000000040000000000000020006001000000010002000000200040000000400080000000000000000000006000400000000002000800400030024000400000010000001c0028001002c001800100000000000000080030004000000100020002002800000010002001000000060000001800200020002001c00100080004000000300010004000400100040000000400080050004001000080000000000000180000010000400380000004000000480080000000c00600000000000800080000000000400100000004000800180000000000000280010000000000000000000000400800000000000c0068001000e000400000040000002000300040000000000080010000000800180000000000800000000000000c00680000002000c0000000000400140008000000000140000004000000200038015000200000000005000000100050001001400040008002000a001c0000001000000080000000000000000000003000a0000001000100000000
  | 57 => 0x1fcd0c7a0000ca6959b426a2ff47550000000000003210b313dc40000a2f000000003530000000008ac4078bed8000000000000000000185e000106680002bd40000ac30000208205bc00007af000074c4000000000002df50b88000326e0000b350000000007789940000225a3238d3800000000358c0000000000000010df000043860000400000036d800000000000000031ac00000000000806c00000000000000000001da00005840000000008744b5c000017621d64b30d108a4c2ce000000001c7f31b400000000144096c00004f4036905026258bd49743328e5c08427109e2ad047f9108999900000000000203100000000efa07f10000000000000002cfa0000000035c000000000000000000010c0de3829c0000497c0000000035e5a2c00011ae000000000000010000000000f68000000088387b29cd404025408000000034ee7368f829b9b35305e7400010da3450380c981868400000000c258d9e10420e8000000001cec4134000000000000000000093a10b40000eac06e000000000967000016d8385800007c40a8c0000603800000002c18923059200001410800000019a820349c9957243b4000000008d8155285e4253832a253e45a40001a7117160000000000000001fb40000000000018c46d9800000004c1c03c9e943d8669b800009ca00002ad4000000000004f30d580d800f3a6094000000024e40000e59800013fe000000000004064783c0000000005c71900001bd200000594000000005ec0000000000005f20000000000000000000000177f000000000000000000000000000f5a0000512c9f0938c1e684f08f999318000049c40000cb200000db800000003bc40000000000001685540000000000001a44000000015ae000054b800010380000a0681f4000000000000000000000005b221ae034a000000009a82b8600001ae9b7f0000305c7a1000000000000000039d41b00000000000000001c68a12135d345200000001e2c000000000000000000000000001b4e00006a540000000000000000000000000055e4ff499d5000023380000000394e000055b819c1eb67870eb680ba20d83e04000130e2cec1eb000000003a2c000000011a700000000000145c000025b80a9020500000000000031d000000000000000000008c0df0050d0180376801b8c29000000010201a790d2e5260822039526d22840c319d74000000000000795000085e86f510df3624377cb419cb63e500000ad20000370a58c10028e10000056c800016e30000000000004081eaa00001f100000000000000018033fa600000001cef000000007a880003ff400006320215000000000000000000000000000000000000000000000000000004218000000000000000000422a0000000000000006f6000015ce1a7230e42fa0c3b0000
  | 58 => 0xb22870e17a20000adf8781000000008ad00000000643c00006a200000f6400000d800006f8c0001c4630b800007210000000000000001d6e00008175093178d01564d6c51f98933dde2d5c2501bff206c4d080000000396432a40000000322435ec8ab0acf02642e34710860b2d0e67950471cde333c2574cd795961e061cc895f800000000000a5c00002fc852bd0c900001f8472c00000000000000000001dbb23f027344f100003bd4581c7c400000000524c0000000000006000000000199e1f7800010f1078a00000001fc11eda36d8ba5940b3ed26cf40000000000000000000950000033a4000167800000d04515000000004face03800002d21f340000e6e000000000000000000000001e880000000000000011970000134c0ef80000c6e00000000000000078940000f13298a7cb46da17373b2e5cc03b98dd100000000c7380004034705800016730000000000021122ca41b247fba1bd311e440025196da1af2737ceef80000f3e7f509fb1f5100004048aa4800012a200000001348000000000000000000085200000000000000000000000000083180000000000000001e3000000000000000000000002898000000039461f04c029e032f5423840001a8000004948e908000032a76f817d1ab640506808a80073f01f404e800019954118000000000000000000082e20b600b800000001ae112300000ad48000000027c4b6200003c2840c011980003d4a0a9000007bc3bc21038000172d3b543df508b8138000000007e0075c0be05fa8879056e1dcc76a004394560000000050791ba000019040000f1e1be600005fd00000000000087800000000000000000002670000000020ae2d6e165c6d185962e9a13f0c7b10720f6000000001b74000000001679604000000000001c9515dc00000000f3b1aee0000b5781bb176200001bd004c000000002f192ea000000000001edb27de1ea400019d710241c28bf9800000002f40208055600007b203fa1bf62b18425c00000002f50000000000002b9e276824802190b9c06a0000066a00000000000000000005f147a980000000000000000000000000000000000000000000000000000000000000002e146de011d171b0000000021b8664254600002c08e2632aa6c8000003c9308665d10a00000000021d000000003bf20000000025f20388784000067100004b9400021854060000081d8e8235580aa869513a02f94553c00004d23dee6a7c8718216102c1490882099e3aa250cc000119c0b5439f0000000015a06938b07800007ca0000603000024b605600000000182000000000efe226200000000000000053c83eb800043088268000072b00000000b2b20c500000000000000022aa00000000000439280b00d8855800004e08eff01f000000000000
  | 59 => 0x8201e000000000000908000000000000ed60000000082919a4000034680000dc71c967e648740c21320473d4c3a905b373275f400003f335ba000000000000000584d01b000000002a94ea580001cf4883d01e1e1b2ac220ac0000c1c00003fc8fc708aa00003d8000016be00002a1cdf21aca0ed07568000000000000000000000040823a50000000000005a7455c0ecf04c26fb4469800026d60014571800000002cdc00011700df222f800012a63e1e000000009c43528000000021113e7a0000694800009600000323839800000000f248000225226c00001a5d00000000e52059923500000030164c05d25e843a51b893b0e0000000062a136c0000a0a018700000bc05fd8000000000010c9800000000000000000000000000000000000000000f6900000f6a000000000001c9400009639e013c0832544f58d461488000054480000000000014315af028e000108e800000002a2871d88b80000000008b0000000076680000b33000032cc8fd000000007ce400000000ec4610800000000000000047493a910ee17082f61d611aca0cf00001d1912ea000000005380452000000004a500001104b1a98ca249a49a8000181302ea0a6400007a000006b6c000000016c043800001bca19d40000dab80002aa23a0c000000010880000c3480000000000000000000000000000000000000000000000001c5246ccade05ab40b00000d9b815a3c24000059f923c0dee366c86618dd21600000a42a1a400b200000000cd30000302906c800000000000000000000000000000000013b80000000000000000000000096529c400000001763080a0000000000000000000e5d00000bb23f2048b0ceb1b7c4de83c80000040652680000000401614e8000000000004b5879b00001956429cf6a20ca16b40000000066b0e2a5b24a4405f941f23f44000000000000a800000000000000000000000183c000000013d5253c5d5436b80000000000000000000e4e0000000013500007318000000042ba000000000001d9056dc00000000976000000021b700000000000000017c25fc45e194c800000000000000033146dcca8195bb00000000000000000000000000184c000000011050000000049f800000000000000048e800000006be9078033a00006f38000000011c80000c6700002fd000000000000262a00000000000000000000001f800000000017912a83ed600000000000261800000000000104e6ca80000000130c2b38d7b9c7c10304f9400013a1000041b865a178108a40000c24800023d400000000000000000007f18a1d00007cf8f938000217c000000000fd00004becd0b8000000000005ab206b268c00000000c2a000000000931b75086800000001b4f276800007989de839fa0000000136400000000df495d4253000000000297000
  | 60 => 0x499c00000000000000000000002a5e6d9c3dc13e7000081cc00980000000000000012f1183a000000000002bbc12d4e1d800000000000000159e0000784000000d40000791800005400000000000004740000000000000000000677cf0112500000742500880000526878c076800000000000000000000000000000000000000000000000000000000ce90000221c000017300001d8603689b1911e000082742a29df01686000000012c4243a0000d8895e308805e2407918150000000012d17fd40b26f64f9a9542190e614c00019d624b4063c34d21ce1cb2000068607ba00000000cc68000251a654800000002260000018b0a8f00000000000000000004a64000000000005df03ae8304000000000000000000000000000000391400010580e7e054a00000000000000000000000000199c000037480001b8802ecfe40ade000000000000000000019fc000000025e6000000013f3265a0000488869300001b705728000150a73f000000001718000000016411ae433f82cc0588061a0000000000006580000bda9a52000000000000000380815fc000134016027b9c00008e50e4a0ed8000000032b0000000004c028be065000012c23d5678ac9048291046c0000ebb1cec0438000099e8000000000009400000000000009ae000000000000000000000005aa47178ea23d78819c00000004318484c000202300000000000000000000000000000035982c90000000037f0447c3671157218a1fb06250c6c00000000e3f00000000273c00000000000869451000000000470419a00000000464000006490000141c00000000000571c5030000000000000000000000000000000000000000000000c90000000000000000409a72580000f7929f00000000000000002e1d0a6986500d200010108000000026e465213021ae25c4c00000000164625c8f01c080000000003e000000600000000199100000000db292d441564430d51048604685490fe600000000000054600000cce0000bba9fc600000000000895813226134000000016822518c62991100006998000017400000000000011b00005ae80000000000086e872c00000a4a000000018a8379a56e46cc96f21db40000a4000000baa862c00000002a100000eea8fac3efa000000015e6409e00001a198e4000056b8524850f2d6600005298d28391858740b90000195417dca3d80002e325cec000000018fe4c04000011d000033f00000cf2105200c8f8f00000000000000020bb0000000000000040000784c0000ed3000069780000000000078dcc7b8000000000000000c1900000000000000000004bc0000000000004fe061402f400000000a2a98c729a657c0293071e000000000000f593a3400006fd00001fbc00003eb000000007d340000a14000000000000e6100003f1030
  | 61 => 0xc8880e09ee7cd85a71229195815d01da9c5322106ea056203f1000051a400000001790058c00013d9425a280400000003b2400002f21ff9335600000000000000000007ed800030220000d33886000000000a970d2e1e9600010cc0000000000007b7000021864e8800000003932000000007141812782426396741380263c0fe17173c4e26d4596000000005aa0000000000007ceccb70000000053ac0002210000054a00001ee5000000003ea024900000000a5980000000485c402800000004c700000bff00006790000210906c2000000000004360000012e8000000000001b200000000000000008f61b9e0000c790000291e35241e19ad61abc7e0400000000266269000014a128e000008cf111d23b600004ef80002c4249dca9f00000000000000006091a0e014c0001afb201a00000000000339200000000000000000004b5800027f8425400000000000419437d914004e265b00001e11381a6f3cb85843c0000000103a800034ea6e3475b00002cb24fb0ffb800040a47cb80000000000000006a6800017ee3fe08c280000bde7dc0ed800000000352d0cb9e17315e0b780000000000037b09eb800000008794000000035d2154c0000000000082640000136000055f8f431b17000000000000000000000008a9800015da00000001adf20e60000a3380000a980000000000020d64664cd3094f000000003168000000008882f10fb6154839347489a870000000000000002c7c3dc80000000000032f837715f624442de000003190fc66bf4000176a0000000000004d800006d845b080001e107db8a4b86690000000000018b4118a173466c8000000030c00000000000019289fa800025cc5b44794000000000000f5c0000417067a8ad500003c94053004620d418e414dc49396ca0000000000010b126e661402d105a32e7471c50400edf05fe66945598d02020844443708abc1a666bf027f1ec6159032b47d58863293a172c00019eb111028a0bb380002edc0000cad0af800003c2c88114b93bfa000059a000000000000000000000000000cbe00000000132c00000000000000038c00003d400000000197f0000201800000002a52000031f802d000000000000000217a50706dc1d73103a16680000000252c0000000000000002b8092e000025fc0f9c92193da18c409f800018ea0000155c65180003944541c000080a00000000000000000006ab82d20000000000000ea00001164846d07a99f300000000da390a900002a6c503800000006a08b9c0e7201701cb889d00001c2619a09b68b0a437e0000000000000004d7cf2700000000423429980000000000000005ae0000000055b0000000062d8358800005a40bdc0000e953f885ba84cc97f936520000000000000000000000000000000000c6194250000000000016ec00
  | 62 => 0xe2c00000000450000021a4238882d000000004f20000000075e40000c3813a4633c3898000000087805ef0000078826b8b1f913500007e34d8a8536431a0000ff505ad061206a899a000000004504000000000003920000213a180073a45de1b8a123279f40002186435688240000b7c2a440000000000006a63d38dd7800000000000b7d000000000000961800034b02508000140000007364c240000000000009938000000000000000b83307c731cd2200000000000021680001ccc50a8fb7927c000008345ec18d9427c0ca4000029f00000000000000000007b740e58442000000000001cfb1a38180c000205400001d90000000000000000e248000000033fc0001310391c0598e1b0000198879b0f17800037c484380001a1600000000c8280002aaa10584b31e7f0000000047f8000252e000000000001bc8705c9c3800003d40000000000041845ee800003bb000064d433900000000276c00000002ce2000105a00000000000053d0000334600000002078000000009f8000000000000000136000000000acaa13c1df0043024b9e480e8c83b09c7837f14124f700001269261400000000000030474006c81f4f324000c437200c8091821ed0ff8fd000000000e0f900b13560000000000000000000d151b00390c68900001e19360e665cfc91e7800000000222800000000000000000000008684d0c80003236418862880000000000041e832d00000acc9831e68000039a00ff08592fe400000000000257660380000000000000000000f6c1cde0000aeb908f00003b78c83a1c0239446610718fc5416a5710c139608000012280000e9200007448000000013784770bee19ad389600000000000000000000000000063800000000000000029e40001dbc2f0000000001de00000000083518bb36f25e6c3200000000000000001b1a00008194dbe800000000000cd100002d2801000000000000000003480c5f2c6e4b3c3e480001cae7200ed580001f0e6b2c4bc8dc100000000120926e34a0197c5f3820000000000ded9d2e1f7c48a80000eaf00002610000027f2c8800010f21e3b000034340001948000000000000b44000000000000000000000000000000000000000000c0b00006b88d6e0eab266660c0bdc80002abc81c107720373d5e369000002c7276e4d0487b17a00000000000000000c5200005da1620174200004c000000f8400000000000274c00000001ecf00000000b090c3100001ca4c5b800000006ad04fc920a0f980000fc10000000046bc00018e600006c3800015bd000000003b4868523022b68d8d80000ce00000dee9c2b327875540000000000000009e00faf0cb400006fc000000000000000000011f6000062b851520fc5358c6f95ba1b5c501506b92de403a2bd800004eb28e8690cb2e8fb900000a28f
  | 63 => 0x84c00001c921e70cce00003c3a0a9c000000000000000d7f838c2e440140023881f227e2660fcf8000227600000000cef3000665816121bc3bec08a84519a5a261246dc0ea80391cb6841036d8bf11f2658710cd9e5b3cae2eb8be19d2739500000000000015f62e04207951e000000000000000000000000000267319606ccd6a0000326c5e2c00006a33dd60000000000000001bc07af9bf932ec840c33f110a1eea000017a9b9e174c000008a00002e38445c34b0000000082807070000191000003fb8c1b2f1e188400000000000426858e8368000062e00000000194a2184dfa0000000000000001d5600004a108621edf09ac00001fc9d480e781df00001c2530241eb8000075b30201a340000eef068048ac0000b6b0000000000000003aea0000000000000003134ac1843b00006d0441c800000007d0c96e80002fbe000000009ce37d4000000015c20000789000016ab0000427c9e1800000000000918800013340000c4d8d7600000000e841a5f23ce13d01229a4708900000000000000000000fb10000015e0000dc1000026fc31480000a4d00000000000000010fc000000000003e8800009f680000000000000000000000746c8c9000013180000e370000019201b0e0984ba000000000000000000000000000f3f165234ac000012e00000000eb58c4336ba00002e91f460000000000000002b245f4000000002c1a5e38e648000000023e03a20df9000082fc0001741000000000001bc600000000000122700000000d6c0f8235ca3d1456c00003a520000777000000003e900000000000000005591b25000069541ca1e3100004b70c8f808f29940860000202d113e1a1c00020b300003eb806600003a4c68e8b3d80000fc4544800000000cca000029a800029127e3cc5e9f52175e6accb130000199413b8b63188d0bec0d3cd1580003f062a0cc1188bb0994000000003372734777000000000000000000019303ee25b84e2d0000337a000000002fe0000000000000003cf647fc27193212760000092b000000003734000000000000000aab1d0600003f3c61a131e1d4218bcfd480f30000000000000003d9634c4000010929e60000000181f0e12167c51700000b407ba4000000000002a3800013d40000440c000000000003ed00000000000000000000000127c0000000000000006aa08e600000000240c68884c607841ea8861125129f60000ea48d503ae46e4800002ee00000000000015d0000616c798221200000000e859a35408c1be8924043f09e47160aaa01eb00000000cea000000004480000131a11d61b5800000002a900000000000000000000a3b0ca100000000000000000005bdc9430000000077740000000000015ac00000000f943e8c00000000000000000000000000357449180004352000000009371
  | 64 => 0x263679c863e9f2a02400000000000000000000f1015890ade55e000001b50000071451b019126de544d0a611fc36a668cc739940c0000000000021fa0000000057897cf0000599c9bf800000005e5c0000a19000051900001bbd1dce000000000000000226853e906f0000043ca72800041460000ea70db941f6000107f0fe000005d409088f64378021d80000b07000055ac0001c33343672f40001d6f0a58000000003380000558835a800000000000000000000007328ddf1d020000000000015f41d1600000000000000000000000000000052e800000202ab45a690fa1d41000074803538000000000010739a3e42ee30600000000000000000001e5f00000000000013f390a80240000000338a4a700000b2009a800006720000150c6bc40001fb400000000000000000002a4c00000000000795800010292d2679340000dd6386203c024780000000803ca66062b41cc0000000000034fa37d0000186f00000000b7100000000000000006a8121e249885d9128056800000000cc9085277487a800f90e7c7194a559eb02aae5eeca9b000029be00005c2000036be656c091800001820000f4203b83f7a0000000000013744d34000000021060000728800029ae41a1007132900007bd02ad000000006848000000000007f640000000000000008e693df007c3a24000000000000000f6a9c8742e8000068711752cc04074000069b00000000b7009560f1c3b000000000000000000001cd7421000000000d2c0000587851e0000000000000000000000000008bf102f1cd462100bc847f0000823c63a9bc2000000010348000000000000001541000000005d69a8a00000000000061b1b1c151c0000f040c7c00007fc9b3f22343724000051929047ff4ebb800000000000dea10aa051c0000c5818a229763f2c71f21f1000072d05d290d7000000000e017bd00000000872867700003fa8000000000000000c9590903eee57acfe88e3a112a0380d49800027780000a0300002cc218c01838cfa25d80000b50983100007cf0c508fa50a5200000000000000000000000e7833e8000000000000000000000003b700000000000000000000000fb28f94433a000046d988642b82230eeb000001dc000099b000017b80000774885000000000bb80d86048c79b400018f10000000000000002a604f480000bdb00000000000000000000000000181d0000779000000000000012c00000000000000000002d300000000000000000000000000000042c0000000017a500005864f3188c300007e400000000000045bcc0a000000000000000196d00000000998000039f050809330000372a22fc0000872000060f09910000113800000000cee000000003b709af000000000000a9e000047f5076848e00007e14fc9800000000000000000000005770
  | 65 => 0xc6431aec0000000000018291fdc5d184079a2219c43ad40000000000000004d28fe8091200003dc8000000042b479d0325000000000000a6400000000d1c99342d3200005f5035f0000000000000000000150cd6380000000000000000001b6a6fc0ce109b1000000000000000000016a0c83159800005008bed14dd14844e2c00000cf03360000f770f52247a295cc778c6840ee8324911800006046174a788000000028281238000000000000000000000057a0ca0081a1e6a2de8c7190c004366d141331527391057b0a8c80002aca00000001f5f31d255bc535000021a200007bf000000007fd0fa600b50000000079e00000cc40318000017800000b808ec886200007444112869e12023a30e3805e63c8256700ac8a182e4200000000cb50daa0000df2800000000000145a16e00001344000000000002ac00000000000048000000000063057200000000029206740000000000000000000000000000000000000000000000de00000000000000000000000000000003063f6e000000000001fa800000000e45000000000000000334200004481f1300000000e6e00002f681248000000000002224ed1818b4128000000000001ad802703b78000000000a000000001442000000000000000720c1fd80003a5a0dc4e861b2c0a5c117c187800000000000c9380001c7e372c7d10c7700000000584800007d21e308a189b415a600000000000037000000000000000000000000000244c0000000000000000000000000016b61bd4846084c388200003ee8000170c5ddc0000000000000000000d830c5000000000000417250ec000000000000000869933100007570eed000037be4210f4680001678751400019da0000160c000000004de00000001e2d2d96000087a1ac3000061a0000000006ca00000000000000016140000000365c0000000000039ec7d280000000000000002ce059b000086681d200000ce65f0110411eb31dc51a070c0bf61e3e5704000000003080664e721c4e00000000089800027328010d50017700000001097a1ad11e613d8d55099c1f76518833791d200000000000022d00000000000132f00005b30b000d8100006cac6798bf22ab6645c8a909d929362f9471689382ac07fa00000000000043e8000123700003dcc419000031042d9c0001f5e00004ba0ac1000040326a9c3cf0ef2286421f0c851bae3c100000000000000000000fb300000000000000006eb3ab64c440000e0900000d280001ad3000000000001d05000c00004a700000ea80e04cac85e10bbc0000a60811514b40f6c1b68000000040ac000000039c4000000019ac022200000000000000016e0b6a0000000000006f400000b5800000000000381800000000000438e3a4cdb8856d00000000527191d00002bc0ce3a16124aa5e981010000
  | 66 => 0xe1a2400000000000141a630000011232a780000cb88000000060c80000000000019f0000000000001d7800007a23a2660dcef5800000000000000000000002f3000000004228000000012e9000032600001490258a27c8794931f21d465186d8213f0ffe1998d2e1f3f3ea60000c30800015f8000000000000000000000021e614e27c880000000000000000001419056440fc104800023c82f488be8000019a2030a4711a91abe8718a5100001b9c000000390ec12ce000000000000000000078603ec292a000026f9fc32df200000000000000000005df80000000000109c950c364c1200000201627c400000000000000000003c3000010fe79d4000000000005ce4b9f000000002578460a04539d43a6c00012a42424000062a98b210ae2a8000014130000000000012f2282200000000000000000000000000000063790318000180426543729e0c0000120c0000000000000010a89d433f505d7c8cb01e633c041007aa000038423af881180000172773089207cf26480000ebc19b039781520000000000000000297800000002eac00000ea00001034fac0e8103c2000000000000000000000000002ca24f38000086d00002970000000037880000000000007440000000000027e26e6044500000000160800000000000000039a92d900004530000000014480deccae00000000416800000000000000000000003d124d8459d80003e280000000000029bc582c0001d4200007aa400000001a7a5f2c000170f163460acf6100002c64296c00016fe0000000000009de0000000000009540000000000000000000000046c800000006ed8477800041263954d0c1de70000000000005750000000000000001bca5f9c00001ae0000000006d80002ae060bd0a117ec19ee78f46199a11000000000000e0c00000000000000013ee77080000000000076380001af6111c0000211011a081854e0e65800033663ac04ad87482af4394c6dd0d14003e719ca398000034e00000000000000015e8d1b80000d16000035a000031480cfc00000000000000035480003f7e0000000000000005c000000000000000005e480000bf468e00178b1214de0000731976400ec1dd00001b5a00000000000000025ee36500000000000052fcd7580003b0800010340adc00003c6c00000002d402c0072e97c918106274666000000007f7800000000000000000000004322759400000000000000000005650000000023c84e90f1400004351ad53db06d50b4517a315cc00000000f66379800000000000000057f81ee911c000000000000000178a1ccc0000000000000000000fef000000000000000350a000000007c00000536ce0e8000010a000000000000c1c5278d7700000000000000020bc00007024cc1932e0a46000000009a3000000000001852076279a
  | 67 => 0x192cca2800036e0000000003570000000000006c4000000000001cff3caa5e106138000247618e40000cdf00000000000000028c60000dd9000000000da8000000000000001049000000001254000000000000000000000000000000a20000036307a3c44e9ae72430596c00021361d400000b6780000044000000014601272861cbc90000000000000000000000045b40000000405274f4abe800000000000ba880001af000000000000192c00000001ba909f01a20f5a800000000000c6a800000007798000046d000017ec31d17ab00007a4c69319bb000000000000cae431e00000001db90000000000000001f2c410c000000000000000bea96f620d28514000172e18f22cd40001c60000029fc5ea9da400004b800001e4f0ab20000000152100000000000000000005a150af8def31b600007bb000000000000f6694ce3c884354000000027386ee400000002f842198e7f014336720000d3c0000000000004ae0000269400008b3800000000000c758000121a44e40001624000046d000000000000000000022053c5400000050ba900002ef8000000033a00000000000000001638000000000000b6004100001d72000084b00a800000000a208f060ef47e1c5c78000000074783b18d3f000013fcbc3187b0b3c406cf228b2806fa000000009440000717000016db052c00009a1800000001fe0000067600005a5c00004c30b881fec000000003a40000000000000000000b2a0f1929a00000000000000002100252195133da3104000000012c622040001fa3218c1e60c1c917138ba75640000a6600002da8ee207e7399e0000df09240000078cc00000002c9a02290958bb200002b5800000001592000000000004300822ca0e800010480000000000000000000bb99a3612a60000000000000000000d6280000f2e138400000001dba0000000000036ec00000000c3239dc2bacb5f80003c7e000000000000000000091f80003a600000000000000000000914000000000000dfd04aa000000000000000099800000000000000005a110312440000000000000000000102400000001fb200000000c4b00007198000000000000000fce851f0000441cbec9e51173267c058709bf00000000eec894900000000155800023f284c0000000000001388000068300007eb8000000000000000340934e00005ca8000000000740fb4000096100000000c47140418de532507f800000000000158179c0f8a57680000000000000000001fe3019400003a385320b1a0000291074e1db6000000003de00000000000000000001db40000a381a5a3b5c8289345000000000000000000000000000e2312ec1b9caa30daa2bf271ccdad93b318d261c01b11e9d1262611ca5e9d471d4a2be89cc043d0d5425a50010000000000009c91fb
  | 68 => 0x35c03c9436c8e99380a048423b00000f2612dc00013cb00004d10aa9115e0000044000000003f44000000017572e5e0000668957b13901028edd00000000000089c0000000000005899fbc0000836806e05c90000000000000001a4600000000000000078f0f848de938ec3cc90e880000b08000000000003c70000000000000000000000001462aba00000001b640000575867d803c000038d0836800000006d78000020a0000490830b0cd6000045cc0000b020000421c1b58eb2000070380000000000000000000000128a491ce0d0fcd0000000000000001b80000000005b000007b1c00000000000000000000000000000000021661f82610481c0b9b092c2ec0d5c0dab41b85248fe48ed001662d340000000275e000096d800000000000000135804ca00000000000000070640000000145665c0ce609731efe5f30000182601ea46fc00000000000000000000000f0002f0000000016d071a015899791a940000dae051000006e00a220c110000661800010790700000000006af3a3e78b84f488ac00006508ed08ffd21c47ff800019380000000000000002d2038d449796f33746828800004021e8c0b1803a0000193a0000000000019240000000045c00000920000000025644a6cae98527000030d80000000000033f45f58000420e000051980000000000000008d2000015c00000000000000000001386000028c80000000000000000e4958e000023e841b800000bc63f0771800012160000d7680000e3e6784d6d210d000000003c397d101ca3c70000000000007028c4f80000000000000000002be600000000af400007ec00000000348a0000000000000000000e1681b6000040e80000103157209ac000096f000000000001c560000000000000001bb0000070a11d71e1a75f00000c120000464400000001238000009680003a386fa0000000000000000b0a00000000000012a80e1000000000000000017a000000007b40000023800006a5000033b067c800024c254380000000000000000a980e831405d0800021f5000024fd03680003ce20000000000000000000000167e0eee336c778800034d652d00000000165a09a4c858b0b324608b03d900a41898000000009f8051e0000000000005da0c14000000009e0085c00000b60f50725c8978000228a23c4000051e112c74dc9d1a14300000000000000035a400008fa9cb700000000682000035420000ac6883c00002e1400000000000000000006de04ec0000156210224580000000000009d4147000014073d060000000000000000000000087d0fcc3500d35207900aa6ae878d04a600007900000000000000000000000001ba000000000000aee000072383dc000064a40000000000067600001f4e0000000000000000000213400017d7000000000000000000000
  | 69 => 0x2044000000000000000000017141d61220393a09641a2000000000de40000000000000000000000393e24380000be600007fc800000002f9001c4000000000008300fa80000269e6afc00c0ba40000859c0000000000072a86ca8b1b08b24bd8014800013ce60a067c214e2c563f18000081b3b300000000067a1ae86de80000000000000010f384d5000000000f713fa2c860a7854c869f0fd21e8ca1f990c34c03014fad8ff10000000000000000c4a3094dda800013e600000000000000000000000ce5154c47c0a4c800008ee87ec94a01c7000080ac0ff800033dc5e440001969000000000000000356a65f400000000ba231d82c48000000000000000468164400000001b1000000f5c0001db1000008487fe00002a2200000000000000000000329a1d04da7488000000000000708048862002c000008dc9c7d00006af43a496e530c800006ff000018f8000032d996f3f4826b06589818372e71a8b870b1400003994ee300000000000000000000000000000001000e9800000000000000000000000eb4368c24c8000000000002d48ed384311f120000000150d0c1a44550be9e07141c0000957209c00000000000000000000000000000039587d700000c710a0200005218000000000000000dd0000000000001f15000000000001f4731ac2a3400000000000000090d000035061dc8ed9984e2cb44f5820c95d00000000000007d0391a5bf10db0000000087147df800000005ca400000000000000000013b8182c5c68a5e15e242346d280000b5c00003cb072b000000003804000000000000000000004d0588109400000002c6c0eb870d00001298202401d80000000000073d99651664084495500003d2c0000959a1d00000000000000002ede282c0000d5a0000572806291e63d362dc1102000000008524c56000041860000df9a12c33123e1800018743b187540000000000007bc4cb100000000000002d000000002320e688000172e37c80000000074c0000000000010a2000057088980000000000000001d88000094d0000177a00000518d872072529415c000000001c040000000000000006c7800013de51f0b8c00000ffa00004b90be429d06400000000040c04ae0f140bb301102a70d98861523ca63d4da586cc000000000001682031200000001c751daa4dec000000e00000001066000000006ff8000000000004e788e000003a0871080000000000000000710000000000008049558267e0000000051a2d4c000000000001156852c00006750000621c15fa02438d65760fd8a00a00546ee8000157534d0000000008ea1ed4237c77083832d181e24b18800014d219b509883ef23a80000ce19d9b41960000000000000002a607088ddd000000000000000000000000000e791c5c000000000000000034404f00
  | 70 => 0xad7000000000000000000000000000000000010d400000002d4645c88e88a1a35e41cf400006ed000000006e11d81000000000001e8b3c860000a1600000000000000000002cd8092800e1efb39861fac0001a740000000000002c900005cfc010800000000000000000015a460e8000000000000000000000000000000000000000001bf80000b74164c48e0000031a288e47746e6189c0000631800000000b760000e5ca0261f540000000000043442fcc000204c0000245079000001ed200002100dfb382271b400000004000000000000000000000000000000a2c3bd400019c12d4a617c07d8000009c2878bd100000000747400000001e0400005e780003b9486e400000000000000000004cf271200001f18a9506260000180000017c00d780000d6819704520000000000004f187ec141008fa6e9000017883ef2000000000000000804c0e6800023f60000f7f0000334e6e7400005c3000086c46b680001e30000017094a300000000000000021f8090c00004980000000000010b200001e580000000000000000000c14059a46a816a80a6083a06200000af200c660d400000000f8c232c298926f000000003091ce62b9273b452a000000002b6400000002bf8000050184bd39b00000000000029fa000000000001bee0000000000018ac000000017071c8c00000000000000054d000009c20000000000000000000000000000001d58000000000003a7222a037115c500000000ed6800020ea0000000000020b008680001177000000000001c2f0000000000000000eb46a98000000002720000bdf8000229e2f3816194ed00003a3c00000000000000100680002fea00003680000000040f00000000000000009440000260a0000bd9000000002b300000000000044a862e1195000000000000a122d446abc7e180d221b05b009448000000000010ce000028d40000000121b28c270d4df60000000024b870b8000000000000001dec0000000028a1c5e00000000000000000003c8800000000000000000006320f22000080c0000000000006d9140a23aa0948ac8050b3b3800007920000278a00000000000000000001e5000000008788000126300003d2026e80002140000000014ee27623afc9b280000000022c000000027c81570350800000003ee800000000e2c61450bb1a9e000000000000000000020780000000000000000000000000000000000000000000000059f880000000000000000000079cd6f1b0608240a8c000000018ba0bbc01180660000462832194712a2c60a8b5606f13b2c2580f7c9037117a5134e6706c323760b2c74d12d000002dc4000000000004544c1f9c9e17fc00006ce18ec000052180001a8f000000000000107000000000000c232c3662f03df88d50070000000000000000050800013e900000
  | 71 => 0x8928000014003980000000000072c400018940000688000014ef0000880000000002b4440d40000f12000000000001c2900000000d45800031840000b40800024f01e6434919e3362602180001d4a15440000b4418e500008490ed0000000000000000000000000000c2780000000000000000000000546c00000000000000000000001f600000000189911a800000000ff5000000000000000154200000000000000000000000000241a000000006df09ae59f0000203b000000008cf98b1367600000001bbb31520000ff2815c2d5a000005706ff0000000000011ab000000000000000151061b000000000d84000031b000042d600000e99a4c06220000237800000000000924a03a02d60000d8192353b166c500cf8000352c000000000000000000098b000000006090000000000000000e4d8adf3efc3a580001427000053100000db134b6000000000002b4668c8ee1882c3ea8117800000002c702e50d0a00000000000000008a4000000000fc84c20000102c000000037060000edb108e000004a0000183b0000000000016eb1f781dfc000000000000000748000000007e9400000000b6c0000000160935480000b5800003b9240280001e5800000b00a6587712eb47298000000000000000cf3800000000000f3a000000006718143969c35847b980000000116230fc0001ebd000070a0000000014a200000000000000009500000000000068fcb331dbf2b3a03c45ea000040dc702c000162d425400000000000105c0000d180000289c29d400006d800000000d9098730000000099a8e6721723fd00001859391e6a9417211f40000000000016110c9800000000000254a20c09a800001d78000000000000000000107284b10000000103e009400000000de5918900000000000014d0d126b8c04d80000b141b1c00014d114d80000a83000000002e4000000003df000000000000077c7f1c73f800025b0457415a93753c2a2f64bca00002e0200004f000003c34796816c869800000000000000000000000000000000000000000172c2ae240a0bcb000000001b48cbd07e82008577c19e9f1b00002e088a8000000000000ff79ee30000377827312ab00000d640510e25000000007758000000000000000000000000000000000000042840001c3900006764c3f81d910460000a3f8c7e23160540b9288e6000078346cc1e3a216600000001ec907780000b24000037701dd46840000000036fc000149c0000000000000002bdc19384c1060000000cc4000000000000000b818000000000000000000440270a8000000000004db9099886b32bc0000b340000000000009501602000000000000000000000000000d522fdc3be400000000000041400013fe000023dc0000000375600000e70000000000000000000000000000001
  | 72 => 0x800011d000009779e293ed0000000000002cae00000000000000000000001d8800001860006800000007974000000000000000eda000000000000000000000000000f33800008080958d310097000035e8000020740107f480000000421629c0a520000000000009a89fcb3dbc510c5760a55000015744b608c6415820c4eb1800020342604f300891062873e8f988ead00002064000000013364ab40001b6d000000004378aad02dc4dd8000007240c85fd00000000000000000000000000000000000a9a000018640000000369a00000001d8a28427fd80001d4c28944a0400000002e4000006d78886432a2d40a539961000051ac000000026c40000676800000000000f85849f000006ac58c8000000000000000c940af6563c72f93fb00000224dfe800036e40000ced800006e45d5000000000e2000007fb000043b8506c770000000005da50b418550f4a000012e0bb543f26c1084980000000000000017e025e80b04d58881100003f9c02200a53340000000000000000000000000001db81394fdd0000000000000000000000000004820f8300007384000000000007ac80001bd1000000002578000000000000001f7600000000abf8b5500000000000000000000000000000042023a5c000088200006168d3616aa0000000000014e307100b70905818d2a540000000000011940000bb300001d5c219442e0b5838f60c5c91a000006600e68000000031b86da8000000022cc00006a7a1b800000000000089431da000000008c9371800004a5171e25f00e7096321a02242815c00021c111e80000d278da100000000a4a00000000000035d80000000000077e883a1f624efcce5000034204f7800000002bda0000000000007d6000000000000000000000007b100000001069800009522de42c0039e2cca767c0f28000426e15cc1da1fdf1fc8681883b20cf000000000000000000000008df00003fce0000000000000000000000000000004be400000000000000000000000000000047187020ff400000001f4928124424000000000000000b280fc9000000000000000055c00000000000000000000000ca000000000000044322580000b6c9c81000067a0000000000005c340000000000035f90750b3a1878000000005be26d4245c4d4800000002ea88a58000000000fc0000f6300000000dfa9984178c000104480000fe40000000046c0ad862cc000000000006820d3080003f4200000000000000087a00000d53138a2d8800008343ef86f144ad025e1e705b08f4d174742a8000000000002a02172000009fd1f1c0000000000000001954ac40b2b00000000000110b219c00000000000000000002a68cf500007a145fa163d317419602420b6f1d7608c849a9f0c2b628004fcb11d02dde1364000000000000000deb1b1f26ac
  | 73 => 0x5f84b9e8000000000000000000000000000001faa000070608d6135900000cc8a928000000000000000000093c0000000208a33105cd4eeb80000000000000008171fe6000000011ec023800000000000189e00000000000129079780cc0c8506c6000000000000000000102880002c0c73c84761c32000000000000000000009f4000000034f4554c0000000000000002830000000038e400003aa0000792c2f880002a4601b4000033e407a00001cfa17500000000000179a0000093400000000e440000000000005d000000850f4c2b4c5c1490281b0000000008f088c7064e42d90861cf7111e000000006cf14f0000104b873408e04a2c00000000000436400000001a6016dc2952087000038d80000000000000000cd1fac16902638af8800000008204a420000000027a80001f7516606254c3c800000000000da110b7298e2ba8000013141f07260000138e3e383584000000024ea38cc00000002bde3beca74869c21ea000095a0d36139241740000f4f36681ba82488b4f3f4c0000d968000000000000000000000032e849290d621bc3f1c00000000000000000000000000000032b9e6611323bccb2380000000000102f0c7a000029c8e291332198a1ff008700000000000000000003a7c31080001e470cd800009a90000344633749e68000314e000000000003ca00000000000025c21184ddf8000000000000001f7b148c0000e1e0b4700000f98a1b800000003bb003e800007800000a018000372000000000000089400009489c3f12043c147520000306600000000c4000007294b78000030da7664a1c000004a2000000000000000000015b106643dc04f00000000193800000000000374c000000005eb0000000000000000000000000011ed30ae528000010db00000000563890500000000f5d00003b220000000135300004b2800000000000347415780000720000003d800001ee000000018d80000000000010c1000070e800005fc041051940000e0b249400008bd0a000000000000000002b9a00002c3985e00000000b6386ab058a0cac2818000322c1958afe8000000000000001e910000000032780000000000020194391da82e7c000202f24c02e48c661264016000000000000000000000000cf000000000000000024bc0000b1d9d932ee257e8e54a0d5000048c897180003abe6c3c19b046e0a2277e87c8024f000000000000bd6347629b459797a70abc0840a0f838d000039d43c78000281e47d9054000000005dd80001339000000000000e9f43d4300c0000000000000000000000000067c4f9a000028840000000000010200000fda800029cc21e0000000005e60000000000000000000b4a9f9c0000000000000001c3c000000000000000194c89700000000000000010630000000000000000000547cb7e
  | 74 => 0xa80000d3200000001eca000000000000000272800000001a3c00000000000000008c61ae400000000000000000000003434550c000000002e200000000000000000002e8184600002334f9200001d0c0000000000017381ac800000001e0e000000013a80000000000000001794000000000000000000000010643af4000023e000000000efc1d480000000000041100000000722ce8a08e704a60aa4a3b84fd08ea6eccf8300000000165000019c831a67070259859334e6000000010e42b9600000001f7800000000000000000100cd4f521201000000000001e9000000000000000037784120000000035242118259183400000000000118200000264827800000006fac00000000000000000008dc00000000000181e000007749d60dc50000000000004873ca4456c0001c570efc0000e86958525f46a4057a93fd00000ee44bf956d3d8215845d61f121d0e20bc1e080000eaa00000000000000053700000000000025e000011d6000000006c61daf000000008ef000038460000000000041d6157c00015770000159823d92c10aaa2d00e1f0add1a7c0000000085f3d7200000000000131053d4000000006e0000000000000e400000d240000000000000000000000073306478000020c16a42c780000000000014e80000000000000021ed186e00000000000000000004a01d152c147c5cbe995c629a46ba87348000000028b4000000008667a8904404b400000000000000000000a1400001f600008290000084200003454a7200002eac00000000000000053dc000061d1e86000000002ca16a879f077f83d5123e21580001e39000062a800000003d0e4ac0613074b20a629b8000070000000000000198b088c86500000f442dac48847358d5c0000000013a0f4d2b3e00000000e050f48000075480000000451000002771aa800004e6219000006d3000000001f221b8c0000000000079cc66e000000000000f028000336400005258000283447bd0ea017c3dfa15105e39230039e13206ab023b00000000caa1b492de20000075990e3af616f4000000024280000000000030165b7400000001cbc22f00000c6e00003414b0b000030f400000000000000054ec21c00002e102ad039c8bc1150405a80001c0600006320cdc979e00000000ab31e69242c7a00ba480000000000000021a62714000000017d600007ecc001000000000000131800000007404000000006d845e0000211922b05f341cb80001e7c000000000003702469074c1c78409c85685bf1b88414c0000b619f552cf421b0f3503523e32745c506037e3e9000000000c8c00000000e9e20380d182c150391e1f238621b82e0880800001208000148d0000031c53b0da800002abc0001abe0d7000000000f01072c3e10000000000007fe00000000000000006658000000
  | 75 => 0x6ca000023748e5991000006b4437a0108122400004800000000000000000a3d000000000000000408e000000001a200000000cef0000152c7548000000024a600000000000000041280000000244822d000000ef0000000000000001d3c000000018e200002418d2b8a4a03f014e4ada0abf0000673c4c9000041ba00000000000000000007bc00003eb450a49cd80001a2e000000012393ce04ad8000000004b66fbc0000062000083c40000b6930d42a0013e0b3e28da81d80000000000000000000ca7035a1e68000098700001fa80000000000000000000000095a00000001eda1de0716c00019be0fb64d300001b7b08b64a1c1cc80001f420000d0f000043880000000000000000000e3c95643dec00000001fb6371600000000000000064a80000b210000471000000000000000000000000000000000018e000000000000212e0fc2837c0001e0a30dc000020000001fbe0000fb20b980000000020e102c0000209460600fc07be54e414c12ed1c106daceea00002bf6000077b98720000452909e822f3b3c03b10790c0e029600006cd00033e3443e4a40962710020000000000036603848f320000000072b872d000000000000000000000004e40368920221a000000000000000050780000000000000000000e0600000ae400007be000000000000000259a00000000000000000008560a04434e00009539a6f201e10a8f3d00001cda000003980000000771c2e307d9138200f45538000000047cc00000000cc000009b41b5000000000000000024ae56040000000000042f000000000000000000012b500000000000147805d8115cc7986072002122c000000000000000bdb000000000000b0b800000000000000000000000000000000018c000000000b1e000000000000000000000010b81e790000065c0000c990000000000000002f7c0000c2000000d1c49cc0000000000000000000000000083489fa000006400e44000000000004594495000006500000094800000000000000000000560000d82979f3286000038b8000000000003988000000031780000000000029740001317264600000000000000000009e80df5039026881a3a14f348277b8a1880002fda00000001ae40000000000000000000000080b98f4000000006408000235a78f862d80001a8a0001074961500000000000000000000000000153a037c06e48f701240000000082f0000424444f45a117f600003ba8000000000003de80000000000017fc00009b22f14000000014cd00007964000000000003a0101a1f1f00a20000000000004980b8c0000000000000008228000000071c80001e2200002d94995000032103edc00001550000000000002f81f3004608b1872600000000000000006a06700c42800032947c800000000287c0000e2
  | 76 => 0x2130000407c81a0000000000000000d200000000016f80000358284c7930d6600000000c9880000000000000000002a8e734c0000000000000000000000197e0bf09d209fc2fd600000001c4804420000000000002027b64000000022d40000c1b00001dc82b900001bb132ac3d9c0eb80001ca8000000001b439207d64c68977a000059dcf6883601e12010c302220b35ea4d780001f63000030f8f7d126c31f6000095d1b2f0000450824d0000109600000001fda000000004c4800000007f3800006a400003608a0b15a0000068248108a6000007db0dcd00003cec12f800000004220411c0000000000002b49e78b4643be0000bdc00001bc27970e0a80001c3e461c11e10ba000020cc5bf800010f42754000000028ea433c6909d6036780000d440000000000006c88c2e00007624000147d36d0512091b00000000000000000000000000059ca1cb36645130000017e074e00000000000000025a00000ce7313400000000a2500007b5c16e91743a9a0d98000174c00005f9800000000000665000000001f3440380001a26000000010640000000048f80000000000000000000000000000001a6000000000000fea8f0e2a9a0000000000000004ce80001c2231f400000000b5321220000e131bee17124878000000000000000bdb8b490000000000000003d3200000000a9400000000000000000005d940000000266e0000dd121553f2e3dbc00000001438202c0a7000015ce435061018441fba0000ed4a0e22ea609c000000002cc601245628a45062a0000000000029aa289cf8e91260000000000002683f3c233c6ac8cc629fe33083478000000000007f6802426320a4800021593880631029400003eac335c7d6853b1404000000009d3127a71301b780bf0000020ccbd8000143609c8280000029e801d46280f9f36807ce81931fad3e0230ac56a0ded0000000103f000000001d6000008d000000000000000000001de000000000000777868000000000000000000000c48000000000000000000105d154529c05694000000006205c989db0000324c30880e200001c1e5d782f50000254200002260000410672680000000091002540000cc83d88000000013f9000000000000b180000000000011f70000000025c80000000000000000000fa23f94d5697fa3ace7438d0a88451a64000000000000000000032300000e5e76f4000000000000001101861710a6491455ea1fd00000000c4098b529842614b3c913238583f285e20d5700000fb8000005d31465bb86c49cd23d5c0000e6d8000000000000000da6339a000040211a31c321f80000089300000000000000000001d4053d8000000000010258000000024c00001d3400a40000ab617450000000000000003dea5744478015b3f644a74b29800000
  | 77 => 0x1723888d4d056434020310000095f41ec005826086d300000000000192c00006324000000000000fa00000e641b9000006a080003ffe000045009c700000000000000012560000000000000000a880000a8b0000088c0000000000056e000011c54314000000000000bca4b20000000000005a480001a6507e000004909d3b0d6061e06318084123400000001bd300006c8c48619b62adc00000001d2a060200000000000000061803db000042f836f508e0f8520e23748000000014764620bc395ad00005c8c000020b30d6646800000000000000002fa010000029480001f3000000000000000008fc346000000002ee400010a38868000000000000fd7000000000001a0700002f7c000000000004e34000000032ba06a4ab18000057c0190000137700000000000000000000000e4480000000000000000001a8e00006249011238400000001b5200000000000000000001b181ea00001d940000000000040920000ec299b100000000000000000004c9400000000000000042500000000000009d9998000076880000000000000000001cc21908000000000003a143234a7d0000000072ec000159a0888113cdd601ca0e180000f1a800000001ae800000002c0a000039da12900000000000000000002e00331800000000000b3480000000342c000000000007eac0000000005800001bc0000000000008c607421b4e1a7400014aa2918404000004b8000035bcc5f0000000007a4d25096d000082400001aa3407c37800f1044e27100000000000010ce0000000109c011a00000000a81000045f00001ba100000ff857785cf00003e340000ca6249c75fc000000000000000000000000000000000000038682368c45957c304400001ed20ad137c1d4467001813b0c000000014ac1a6a6cd46d014013e4c000000000002a160000000220c19c20000000000000003b601c500000000042c13121230000000000013e300000000000000000000000191954c00005888490000000005ba473b8000100686bc000177d19003d24fd385c7000077e097e90e10000000000011c90000000069e18e8000019ec3669b600a92293c00000000000000101f8000000084800000000000000000000a162c021d647531c50000053e40000d85341a71109c080000000000000000000000000000000000000000000000000000000093d9642000060e00001a9b00000000cfe091500ac1428d4880001a3c00000000000000071bc0000000000004a800016d00b645e540000000000000010e4000022260000ee70000000048b84f70c61267c6e702ca8e3d428200006b20adb3ec037ac00000d0071c55d84a08f0f370e000030e0000000000005b18e15000000000000000000000000000ec12ef67310b999c02000067d40000000000000002a50000176e00000
  | 78 => 0x641180f3d6e1a18ff7042700002e380000000341e000002d97c132e465f88b008800000000009285500000000000003ba000084e0b24800007f84a38ae0000000005410dc300000000089cbc19a0300005c3000010ff2cea00000000000000000002160000000000000000000000000000000000000000000000b1c041c0000000000000000bac00000001c004d68d2899ce21de00004b11a7f13ae00009e08fbd00003fc059b1f2b2e280000000000014fc00005310000275457dc3b3000000000000000000000004184b15000000004020ff80275083e00000000b3d0000721000000000000682c000130d00002a8c0000000000000009ee800000000000d23000000000000000000000000a244bb94cf02585538d8e8a92340a5e0801b19f6000000000868b2e000000002b485a60b4a1c9014014da03c800000001544000000010420000000000000000ec91b44664c31e13ff14580000000000006aa5ec4f119759359a331c000169f0000564c9b6000000007ac4b57000000000f48000180900000d68000211f0000000000aa19e29b2480c657892d217e0000633825039e26ce0000116e0000154448d8000274e41f02299bf1000054c8f41000030a81eb48cd16b6000019e0000126800000000b67001a000075f800000001fa409e80000000000000001a7000025524f2460680000b4e38f008f93b2289e235cbb69540000051bca1a923a272e1c3c0001d8d43e477a4b9388ae1b8c432800000003ff600000000000000000000000000000000000000000000002400000000106a0000000162c0000000000003cb2e6416bc5b3191443e6478c22d000000000000000000011ac000000008b3192e1a54d7f1bf700000000a1d000000006ed0000000026e8341832e88410e0e5b4800000002c78860c00020e0000001ac0000000000000000000226000027e8025000000007a990ac00003c4200000000027000056f80001d2300004baca280000402850d8c691aa9000020e10b98a350000000083385fe28b20000322207d1f52590066d0000000000000001e8800360000000000000007f0800009f036ee00002ed111900000000cb98f4000007f2893f8000008a0000000000000007ab00000000000051c902d800000006aec0000d6700002ac4d46000000000d148f100cb3fcc72bcca5800020267c580000d0342c836482a794a818f049040000000270a1e985d18f2e000077d400019d134da000001a107f19ec6e4c4ab80d632c60e0800000000000000000000003de61068ba91f89000000000000000173c0000db300000000105044f00002a40000096882d6120e0044977000011c43a7070500000000000000004da2efc1fe4795800014d0000000012e200002fe4ccf9c590000713c00000001fb400000000000000000008c307f01
  | 79 => 0x10bc18672eba49e400007da00000000000000000005168037000000000000db4800000000000a568000000000000002132000000000000000327a0001089951a00001af8c0e0e8a08720000000000029c2164400021253cee8754000216224b20000f4a800000000000000000032d47bc8a930000200e0000423800000000000d39068213ea28c444209bb00006d0cc4c1b8f000063040000ba0000000003c20000000000000000b95209c4154000000000000000dbf166d0bba000074400001d7a00003050bd70000000000006fc000000002628fd3000000003918000000000006848a91329c1f0ce9a8000330400000000000000000000000000330259600000d62000035f000000001d0a0000ec18000417c00000000000205a7c1c0001cf000000000a33012f00003cdc00000000d1446010b280002098000033c801743ee0000a8497e22d7800010b78000003a231000007c8000057480001a69000000005ac800037b823f83161ac823600000e0a04f3000008e400000000000287c0000000000028c000000001b3a000045b00000000000038e000009de23b87ae96b1349a0000fd00000000000001fb80000000000000000003538000084e9c01000054cc00001ec00000000000075300000c7c0000761124800003fb000000000000000046200004450d061a2d3e8218e0ee8998f2f5a3ce400010570efa32440000000000006fcef88000186a000000000002cde8834e878c7b0000000000000003be6633400019f9400667bc00000000000115438400001ba60000a5312d300001508000000000000000c928de300002f4c01980000000000000005e908642920000000000003b1cf840d4200000000cff1c200000000000000000000000000000000000039000007f32062000011c0000193400004539dd31d8c00000000000000000000000d1300000160b468000000000000000000000013c40000000000000000000000015800000000a231d8400000000000388a29f0f5b0000000000008d8800040940000e3d00001c5600000001b591ff63ccc8d0a056000000000000b4532a605ecd8591610000215400020a11f40000000000001e461630000000000000000000000024ec0000000176002bc0000117000014c670000000d5122fe000055f0000290e00008958f8c0000144800019dc000000009600000264c0000357000000000000000180a1b6e50550d90a730000000100300000000000006f800000000000da8959108f039c079793843d4e0000c99000000007a04000000000000000e1c06bc00000000907953f0578000066f000017762a7c6a18d960000530000000002d12000000006450000000000000003d3000004c198f93e0600006fb0000135a099089b0000075a1935087955c00000000000000000006248
  | 80 => 0xb94000000000000000624013d14ac000000000002496000000006fd0000000000013492c1c0000000000000000000000145d110a00007f3020f00006600f8694531c8800008f485bf28dc52d4c5707382fe0773c0f98096300c0000000085b000000000000fb20000000000000000000782c7190000000043dc0001d3200000000000000004b07c0078e80000bda00000000d2f115e4e744b2192e00001b6841d92650000443c0000000000000007ca8000000000010ee81402ab242d400021fc329e4a28e9799cb00000000000191500004404623800000000000000000018a614b40cb018e000031cc000000000002dd8883089712504df4102195f000000000000000123c764000020ef000000000001fcf000051500001fd60cdc84180c313d13a480000dca0000284600000000000000061c40959fec000072080000000000000000000807000010d8eb41b0100005fa4d0706f2302e00000000467000062240001785000063c05dc1cc8000000000000000389a0000000000000002b28000000033d25f10c91000000000000000000000000000000000000008778000000000000000f4e0000000000001c90000102a0000000000000000000c41800007ea4a300000000043e836cb4d8294304027b039d19b52a2e00004248000000066a80000224000011c80bd0000000021cc2ec0000333a0000b8212e4363800000001e650f9660b40000000227c2c7c9b907561422627831980002d720000731000000007b8053a0000000035d40000000202874a0000000005b42dd40000a580000000000000000000000015d80003b4c2a7400000003324364c4db947e2e5000000000000000000007951821000000010c70000002800006dd9a592f5800009f4000000000000e18118f00000678234a1810dde3a8c00000000c440000000205300000000000000000006b000001b0d000000000000000000000000000000000076c87660f9d000000000000000000010a0aca1a8d0a3a00000002055000000000002150000000000000000000000006c684c9300269080000000000000000001f0e22d61c6c00000000000000000017f809582fa43a780000000573038e800000001408a1e208d000000309d7171f0000000000015ac2f20188c000061400000000f4b8ac200007dccf1a0cf117c613d40001990000064600000000200a49b4a618308320286d40000e0d415e22d4000177906b66e9cbd219a83e081b140001bd500006a5c000041300002db895e9ebb000009b800003ce00003df04700000000083f0c03912738060000cb59f250000124c3a68000338800000001dc500000000aea996626ce0000000004800000000000023d000042bd0af000009d0319859385a1000000010d9800000000000b39000000003a740000000
  | 81 => 0x311400005ee000011a800000001a4800000000000000000006f88bec089601e80001a3d0000597c90e0ef43610559c813176b000076e0000000000004094ea300000000000000016d50000000000000000000269c000000000002e4c2e5094b330a00003a9037c00000000e360000000000000000000000000000000000000000003c9127d1a4454b40000000000000000000f7400006c0908280000000000000000002c3e00000000ef6000025ec000000000000000dfe031e2b00000000003f800000000c060000000034dc16b8d1f034c303c0fb81a403260000e9d196737bc0000000000000008140b7206ec2e9e052800000003ad400001ff924f000000003fa858b000083f46231ebe000067ec0000000177200009e2096a350c472015e89901e940000000000043681ecc0000b080f1068bc00000002c9600000000000000000000001bf200001380000000000003754819987c0000035c000000043d80000000172b000023d4000103d3dc24e44000000000000000af382200000000000000003650821800009d4359c22c011f800036dc45d825e000000002978a17a0c400000000e1713d800003f8400000000000000000011c61c9e0000b538f923532145c3f21a270d80655cec1198c35e62bf85d3800000000000000093600000000a1680003588000000020a9376e432c0001fe10000000000000003ca6000081f0b5f00000000000000000007eec00021213690511400000000000000000000000000000087c000000000d08de0910d00000000000120438ee695878b80000bbe00002da09d83b582b54bea09e1375a55289e3826c15ee0000dcf80000000744000014122156000051f1dc80000000000001e008b0640c0000cc1424e000031700540ad00104f5a0000198000000001ca000000000a5b895200000000438000000000000a8c0156000041ec9fb80000000698c000000000000000000000023be11250378000145e0000000000000000000000000000000000eca11bc0a365118b6080002dea63f8641a00c0ba80001055000000000000000023542a42798bd98be800000000000000029520000a88100600000000000164e000000006ad8000000000000000000317e000095f11160000677400007ce000047c80000d8b05040000000000000002fe0e60800000000000bff80001a1e09e0f9180000000000017d84dc000000003ea9b3e2c4607e8a5f1a8e42f60000ab50ac60000000000000000000741c00004ed00000000f9c03f43c1c00003820fa624b04fc849d97ef06ac85fc10f1f98000049310c1070339aa7e54308927a406a21900e0800022c41eac56180000000000000001c62578000000012f5000062400001c12000040a8f76177809f403d000f1219000081a884080000ac4109
  | 82 => 0x204e3000039420ae80001ec5000005148380dd427dc810c00001b701341ad800010501106000083c000000000000000152b2f3000003c595d943a63e6c1fd1f8421a4711c00000003fc841dc0000000200662ad0e7898b1c6082f46cb870b0ba67afc00003e000000000000000029d400010cf8d19172204d000011b62420078cef298fd0000000066a8000251e00000000000000000000001968000000007800000000062940000c2c000014f4e2f8000000000000000000384e288873894c600000000fae8000002400001c3071222924151067205f301007c80000000000079bc186000026ae0000000000000000000b27800000000000000000011f82ed800000001fc400000000c130000381c0000000000081ec00000003bb600002870000000000000000ce8000000000001016000064e800014570ef6144ce9613120000000076c9dc000007c840000000000015e00002202000016e4c978000000050b800015a700001f4c08b9c54000000000001b192eb8875cc9200f82d8a0000a1310ed00004a0c360800000007860000111800003bf000000000000000000014492a7a2d30f4910a30000000000000000000000000019330ce828a400020e1416400000001cbf36481d9c5fe00001da467f400000000000000000020b700006df0000041b196e2fd4000000000001c141aa0000000004c062708793db81b98ee58ca2000014f000000000000000000000001eb04b9cc9f800000003e2c0001891343e35cc00000001b782e28103147a0ace3ecc000000000004c509f313961faa28147121e610000000000000003d9c0000000159917500000e250c010000000101c8000000000000000ea800000000000000018b46f6844380002b0e14144fa1acf43b279f8e5a9d53051802049aa800000000000fbd192803ea54c41d085f343e02aa8afa9ee80000000064f85cc00000000000202e02fe03fc000098d29a80000000000010545c24000000039ba00000000000000080a8c0d00000000827800000002a0a000010a085d0000000000000000000000084a00001e7a543c59c000003a24158873800000007cb0000000000000000235800000000000000108515fe2bcc6e516d70000520c87996393da076010bf00003a882c40e30800010a80000acb8000000000000000000000076dc0000000000069000000d8a000000007cb80001cd877f08ed00000000000000016d323d010182ce90223b1e0000000000000000fd8a288000000000000000000000076d4000205a255e1c64eaea0a511fa2ba4000000000002740000000000000000ca48000000000000000cf4000000002841ac63b3a059c0d009e500000000000000034f6000000002830000000000020851d9a22dc0001a00000067b0c31000000003b1400000003e6e0001009130
  | 83 => 0x23080001dcd0000577499d97dd25f87d5c0000000000075b00001f7f0000000040a0df014ce72484d512820000264c0001f401926000030780000000473cfc300000000000000000002e684f2829805200000000000000000000000062220f33ec269f8491143d0d0073ac000000000000000000000035827e2ca6c19a907604f6cdc70dfc00007f74bad8000114a00008bd800000000000200800000004cf039b9d5700001ab0f948000000000009e403c800000000788800024666b240000000022400009dd17c62dfe0000ab9809d085e0000067049c29ec0000000109200000000000168600006010b740ee503d00000f310000268e3808000042e00000000bd80000000039300000000073613401f2000000008170f4f00000000000000010c8113685b000018f80000349431a9da50bea54b06d611a632324ef503f8d60336826588a68421196000000001d3816227e3090300000000854ce4a0000301a13b00000bba000000010a5130827a662306d69d0312861d5cca2132b0000000000002c813c616f00000711345c07581a4166404f6000000006512c680000000166b1e42000000002e21d9c00000000000421400010eb000016e4000101980001ae00e2400001cc3fe200008ae0000000000007e70000075e00000000f5c3f72000070d800000000000b8801bd000000008ec17363fb651e43bc9a8123360000fb380000e0c2b04a738000000000000000b9600003b889cfa0e81ec40000d5580003208000109a000021d210607f480000000000014d97742d1c1618bc99122374087f800015ff000000000000b2333c40000000000033a662280000000161a0f1c3d380000000000096a800000000260000122d1c9c7908000135435cc85a8ba21d62227800000af800000005b346ff800026f2000000006f8000000000000000000000004e58000323870f41bb902006e800010dd8000000000005e5806f15083ae8000046600007e28000000009ce1288b1280d5000000000000efa3abc00000001d2522c8000000000000000000000021ac00000000000000000000000000000000000000e62800010e2805c2f900001c54038c0001320000082601c7861f000000000001b16000053f0000000010ea72700001cb800001edc13501020e8642a100a8b6d00002c100001762000024cc0001dd03d98000074700003d6600000000240000000000000000000000000001e26000000003a00000000000006e1800013f62330c3e8000107c127400010fb0000562c000000000000000000000000005088df300000af854746eb9168439a6008073816424c40000b250000000000000000000000000006f3000034966ec000000002d000000d9d1395000000000000000000000006021fc50456000000002a111e402c471415b6412a05
  | 84 => 0x5dc000196440e2612800000001574000000000000756481c0000000236450383308000125200000000000000000000000000000074fc0000d9f20be126c000000014102e7400012950d4c000042c1af90000000084480003d3e847906890990aa83dac153151c3fb80000000000000004dc09498534000032e48a38f7100000000000000033f47ebcbb080001a202ab0bb406dd42b60000e0800002d081b5000010b8023c684c71b85600000070c42f0da929d88390f2614912dbc000058180000000000000012083a9e0000000000035a00000c898000000074ac00000003fd63ff8e5f0000000000000001bc80000000000000000000338c00000000000179c00000000124229800000000000000107d044d00005d00000078200000000000165e0afa0e94000000000000000ad980000d9600004490000296c352000000000000000000000000000000000000000000000083e8e4342880000882823700e0058400480000000000000014b02bc8000000007c7233a000000004643b2a00002d8930400005f8c0000828000000002a9000020f42e6834a1e6e1696108c7b80ac008a844d07468000000058bc877078303422684d860000104c3ae0b2a80000000000000000001b4a018405b852b29160000000053f3d5a000000000000000054409f00000000000095c8c8a000000000000a470000000000000003f70000000002b73ee80001068053e07c283580001ab73334635c4ba173100000000000000000000000379800022b249c04240afd307a00010f491bd2d1e00003968000261e00000000000000028e80001112000069240000c5841ee2f6803f0a401848000064597f73dfe000009b8cc32a96000089b8000000002f830d0f8a1ad25cf0a290000000012acb5c178c36140ef4e2180003c0028e452081541dd01eec08c800008c0000000000000f1a38c4f8c1a042706000107a21880000000000012ff162c1f7024a038516ba1144a5905d7333677dc555a1d842767d08b7c0b7303b80b6c7e615e001522b8806c915f321a16e90b91a3419a07ba800000000000000007b084f0000000035e9b09000024f000000002168000000000002d485b603138000000085b431d8d3a000000000000000000078d8b31042b3ae00000685000004e622a451b800011da0000e73800030cc00000000000000000000000000000025540001ee4030a000000007bd00f034ec00006b7000010448c6970601bc29acd9999f700001fbc000076c000000000000000000000005a5181b00000000c0c80004384000051a016c0000000000017c7000000000001fc000006424eaa0367000000000000e741f4e00001978000000024b000005dc2d640000ffe000000007bc0f97825717806200395000000006a2400000000000611400000000000840000000
  | 85 => 0x7d8418275a439600000ec07db400000002b500000000000000003980000191e353a00000ec0d580000000000000000000000015680000000000060a80000000268000000002ff8000058b82ea0d6600000000000331c1b200001c6300004cb093a11d3219200007101d711e5a7bb47768000000000001e6000000002964000088b3f360000000095938485610b8e9dfb2f32778ced70c5939ac00010cb026000000000b0180000ae23ffc0001fe000005f9400017ce0eca3f700000d7d0000000000005b30000000007498882eb0000000018773ac805f4dc200000000505c0001748000000010b48a9014a08108000000020b243f4942800000000000000000029140000000041e3ed4307c0001ba50a9c05041e6800000000ce410600000000000000000000000000000016ed000000000000000302c412464f0f7b3d180000ee0800017de3d847dc06a0000000000000eb1000000000001fd8000000002428606088e4220304000039ca000086e000015500000aed900c000000001f50cb62d6818987538000000000000000d383e14635000000003d5000000000eb30000000000000001bfa483000004bf0000000000021cc00002774000000031fe0d2cd1280000000009821f1ce307640000000130b00007c4400007a1000000008bc80001bb600000b80077000022343ca187600000000a1a03121c580938aaf82d400003224a9a80000000000084000000000827c666899f03b60000788201820484df109400003d1c000000000000000000078a9e3235787d1414a80000000000000009d63fe60000000000000000000000023e048407ec0001a840ebe0000144015739a00000000000000000f3c0000b5e2f7800000000000000040640000c2d1e4e61f80000a150000184c0001e1e099a4a40000109b40d846800338b8809f25ff8c681af43172027c9070e7d02e64e94000000000000c0c2621d33000000001e819b8364e000000000002cdc00009359a7600006e44c1600000000105c0000000214411944d320910000000058a8f0a219a1950dac00000314000078a0bee2de8000000000000000000000000000746000000000000000809c0fe8000000000000000000000034d04bd07280000000023980003282000000000000000180800010860000000000000002856244cd7c0000337e54280000000000029841850000000000000000000209647389179bc326266dbce311f103dac000000000000000000055d80000b200000d78197800000910dfd8000000000003bb1cf300004e0045100000000881c329000036c6000000000000000000000000000000000009100000000000000000000000000000000000000208063280002c187e50000000017845784853174a080e56ac00000002e9c187800015141c3870dcf5080001a2c6
  | 86 => 0x808000000001976092cdb1000000007f8800000000fdc0000b888000107e0000000055b000013ec000000000003a100001df21bb20000a4b182e2dcc09e40000000069a00000000000000000000000f56242a013c0001bd700005f60e8c000034c800000001aef000037b800019b7000000009dd800000000000000000036aa000000000000000000005506340000000000004db0000000000000000000648500e00001f50465014206592dbe000000000002d307e68000030e21480f4c118a1ca000000000000f7700000f60000097c0000000050b8000231c000080a908a000000000000f9900007598958865001fc17a0e289a311bce000000000a700000000ff68000275a0000000000000000000b3f800000001cc00000000000025350fb09b30000000000000003564000000000001ed073a04fb04ae00004de10ed8e5219363fe8863897d19a4152c000202543d64a8837400000000000035f929207160000b1d0ce61f0056840001a0a0000000002305f81e8235388e393e02326000000008ba3bda0000000000013da502000012d20e6c74d8484a04800000000000000017ba000086e8000131467c8000000015f20d181a89cc012e268b00000aae030624400000f9c11a2851853b80002c52855c000000000005b9c0000e5c395a00000000000000000000000000000000001ac11b533cc000000000002592000000000d305a26cd800000000000000000000000000661c000038739f200000001e3006ea00000000000000058cc00000000000000000000000000000100f8000000000000001e8a25be0000409800000000000ef78000065c1da8000012700002f3400004ce00000000000000000000e100c8000000000000a2d83b300000000d0e0bed00002c3c00006f60cb8000000015f800002ddc18580003276000000015b020c01c844dc10fe006a00000000000100400008f8904200000bf4000000002c4000000012cb4354265c0000d7f2c503d780001b9600d000002509032034600000000e4042ac0000000000000001054000000041367b0000000003e6450600000000000000007eb0000000000000000000084c000000013b923705c580c6000000001c34000000005340000000000034f80000000118300003ed4178911001000000d8f0cbc0000015c0000c6d00005c54af28ae827d4000047c800020e818041d420a71ca0487cb0d00000bc040089da9ad9014261602bc800010a40c6c1660000000040b8586097e000000000000d443688362000000000b6a55a4765832100000000be90de201263554de80fec07e45bec0002118051a73804601baa22d8297cf0b07e5263a0cec0000acd0c180e4c3cd992d16a230f4000000032ea4d2c00c98a62db80d2400019ff09320000af494f0000000003ef860525b481885950
  | 87 => 0x1011000f43f05fec0000000000072ac00000c2000050c0000000000006530a570000000000000000000000067e000000000000000000011461c3a000088d80000084000000000000000000000000000000819800019bc05ce176c0000000000039040000000037400000c90cd8000000008d2800000000000000000000000000c56845d1fd63e7801281b2000000000b68000000000000000000327c0c90f2a000000000000000000000000000768800000000000000137113fc00000001082164a08a0568951500000000d5c8e041a0225c04de96460000000071c00000000000000000000000000000020072850053c00000000000000000000000000000000000000f0a00002bf0bf0000000000000c5400007b4c69387fe43121978e3483d60ac66c88000006a2c3058b800000003836
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87c855d9324400117f08bb2648801a2f211764c9100046fc1aec99220008ef825d932440998e8e232a64880063da1b714c9100063a32ee29922000d37655d25144001a68caba4a28800f2dd81749451001ed9b02e928a2000db2205d251440014e90ca9ca288096dc201539451012e3c386caa8a2025c7476d95514400f8e8ec32aa28801f1d1db525451001cba43aa4a8a2000a7486549514400f8e8eca92a2881378d107655051000637b2ee4a0a2000c6c65dc941440018deca39282880031b194725051000657b20e4a0a206ccac641c941440a1b488239282880063d219755051023cf2412eaa0a2025c7476d9541440438e8ec32a82880038dd94645051001cdb43ea8a0a2000ab686d514144001a6eebaa28288002ec6005450510005d8c0686a0a2067ce476dc941440d99c8ec392828814369dd0725051023eb3428e4a0a2047d65851c94144001aceca3928288003591947250510006d3b20e4a0a2000da4641c94144001b4ea83928288003691507250510006d3a18e4a0a2000da5431c9414408fbc500392828811f78600725051028673b00e4a0a2050de3601c94144001b4e803928288003695007250510004db43e84a0a2047da472d0941440073690ea128288002ad219425051023ed239284a0a2000de072dc141440031e90cbaa62880971d1db654c5100072a31eca98a2021c747619531440031e90cba2628811e79209744c51001cea43a6498a2000ad4864c931440938e8cabae42880026de1175c851012e3b3b6cb90a2021c76761972144001cc8c432e42881271da1c65c851024e3ac38cb90a2000e6765d8b214400187ecbba242880030f19774485100061fb28e890a2000c3c651d121440df958c43a242880032b1d3624851000c7d436e090a20488f4865d421440918ef0cba842880031d219750851001e3bb02ea10a2003d73605d4214408fae440ba8428811f5c4817508510004bbc3eca10a204ca7686d94214404bae4e1b2842880025d61c650851010eb9380ca10a204ca778719421440998ed0e32842881329d61c65085102463ac38ca10a2000875871942144099c6ce832842881338d5d065085102672b398ca10a204ce55731942144091ccd04328428812399608650851024e3b390ca10a204ce66721942144001cc88432842881339c9c0650851026738b80ca10a20479e4825d02144001a6ecaba042880034d195740851023ed2412e810a2003cb7605d02144007b66c0ba0428811f6c881740851023ed8902e810a2000d57655cc2144001aa8cab98428800f35d81730851001ee9b02e610a2047dd2205cc214408fba240b984288003991974208510006d2ba68410a204dc7876d9520440998f0ec32a4088002ec6107148110005d8c24a29022000f6152545204408f7c104a0a4088003f04c93148110
  | 1 => 0xeea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c68800a1f21576d4d1000c7a432e3a9a200087f855d9534400117f08bb2a68801a2f2117654d1000477c12eca9a20058ec825d953440050fd0fb2aa68800a97a0f6554d1012e3c386caa9a20038fa86dc1534400517d093b686880021fe1576d0d1003c3e42aeda1a20008bf87593434400553906b26868816aab20964d0d1000c7a432e3a1a20038f8865c3434400f0fd0bbb286880021f6177650d100043fc2aeca1a200787c855d9434400117f08bb2868800237e0d7650d1000477c12eca1a20058ec825d943440051790eb22868800aa720d6450d102cd56412c8a1a2000aae84ccb62440010fd0fb2ac488003171cf65589100043f438cab122000c5c7319562440e58eee232ac4880030fd9774589100061e32ee8b122000c3f651d16244001878ca3a2c48800317d9773589100062e32ee6b122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b1220028de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001958e9b92c488003331cf72589100063a3aee2b1220008ef87588624400155908b10c488002b320d621891002c3e42aeda9220018f4865c7524400f8e8cab8ea4880063d606769491012e3d386cb29220038f8865c252440018f6cab84a48801a2fa1276549100045ec24eca92200087f855d9524400117f08bb2a48801a2f21176549100046fc1aeca9220028dc835d952440011ef02bb2a48801e1f214765491001c7a408eca92200587e87d95524409b8e8e3b2aa4880030fd9774549103261e32ee8a922000c3f651d152440c7878ca3a2a4880063da1b71549100063bb2ee2a922049c7465dc5524404b0ff0abb0a48801e1f215761491000c7a432e229220038f8865c052440010ff0abb6848801e1f21576d09102663b388cba1220018f4865c742440018e8cab8e84880063d60676909100043fc2aed212200787c855da42440071f10cb84848801e1fa1776509100043ec2eeca12200087f855d9424400f0f90abb284880022fe1176509100046fc1aeca1220028dc835d942440011df04bb284881331d1c4655091000c7b436e2a122000c7465dc542440010ff0abb0848801e1f21576109100345e422ec21220008df835d842440051b906bb084880163b20976109100043f434ea212200087c865d442440010ff0fb2884880021f61f651091003c3fc38ca212200087d8719442440031e90cb88848800e3e21970109100365c322e02122005ce8625c042440031eb033b464880021fe15768c91003c3e42aed19220038f8865c2324400f0fd0bbb264880021f617764c9100043fc2aec9922007
  | 2 => 0x56450b100345e422ec21620018f4815da32c400117f08bb2658801a2f211764cb1000c7a40aec99620038dc8758d32c40079a8e2b1a658800f1ddd77654710274f2412eaa0e2003ab686d5141c4001a6eebaa2838814369dd07250710276b3428e4a0e204ed65851c941c40a1b4b08392838814369d907250710286d2320e4a0e2000da7541c941c4001b48a8392838800369d0c7250710006d2a18e4a0e2000da7401c941c4001b4a8039283881426da1f4250710276d239684a0e2003ab48650941c409db48e4a12838813a79209744c71024c7bc32eb90e2049c76655d721c400136f08bae4388003175ce53d95100053ac0ca7b2a2000a3e8418f654400147b0831eca880030f5d074d951012d3ac08e9b2a204da7980dcf65440018bee739eca880028fa1073d95100051ec20e7b2a2000c5d731cf654409b4ed0239eca880969d60473d95100051f426e5b2a2000a3d84dcb654404b4eb03b96ca881369e60072d95100051f42665b2a2000a3d84ccb65440010fd0e196ca880021f61c32d951012c3f43e63b2a200087d87cc765440eb8eeebb8aca880021fe1d651951003d3a40cec32a2000a3e8418c654400147b08318ca881329da0443195100053ac088632a2000a3e84cc8654400147b09990ca881329da0732195100053ac0e6432a200787e870c865440010fb0e190ca8801e1fa1f31195100043ec3e6232a200087e87d9564440018b8e7b2ac8880021fa1c65591100062e398cab222000c5f65dcd64440018b8cbb9ac8880031bd9772591100063632ee4b222000c6f651c964440018d8ca392c88800a37a1f73591100062fbaee6b222000c5c75dcd64440018beea39ac888003171d473591100064fba0e6b222000c6f75dc964440018d8ebb92c88800333dcf72591100066639ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c9644400117f0eb20c888002a720d641911000556412c8322200687c855db54440031e90cb8ea8880028f613659511026e3b38ecb2a220018f4865c654440018eecab8ca8880021fe1576551100046fc1aecaa220028dc835d954440011df04bb2a8880163b20976551100343f43ecaaa2200787c855d854440031e90cb88a88800e3e21970151100045fc22e5b1a20068bc845cb63440010fd0fb2ac6880021fa1c6558d100061fb2ee8b1a2000c3c65dd1634400187eca3a2c6880030f1947458d100064e318e8b1a2000c6f65dc963440018d8cbb92c6880031bd947258d1000636328e4b1a2000ccc631c9634400f0fd0fbaac68801a2fa1f7458d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100064e3a6e6b1a20058ee87dc963440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc963440018d
  | 3 => 0x928e4061c3e655d251c800187acaba4a3900161f217765472000637bb2a4a8e400587d855d851c800f8dccab90a39014a3be09765072000c76412eca0e4005c6c7299541c800b8d8e4b2a83900172b1c9645072001d5a40ac8a0e4000c6e65dc941c80018dacbb92839000a37a1f73595200064fba6e6b2a4000c9c74dcd654800193ee839aca90003271d073595203b637baee4b2a4000cb774dc56548001968e9b8aca9000335dcf71595200066a39ee2b2a4000c77751c5654800196ee838aca900032d1d071595200066bb98e2b2a4000cd4731c565480019b0e7b82ca900021fe1d65195200053a40aca32a4000c9f645ce644800d938c8b9cc8900022fe1d64191200046fc1aedaa240028dc835db544800147b0bb26a8900063b21972d512000657b22e5aa240008bf845d954480011bf06bb2a89000a3720d76551200047bc0aecaa240038f4815d9544800d17908bb0a8900063b219721512003656322e42a2400087f855c7634800f0f90ab8ec69000a1fa1676d4d200045fc22eda9a40068bc845db53480054b906b2ea6901529d20565d4d200052ec2ec7a9a40018ec865cb534800199ec6b96a6900022fe117654d200345e422eca9a40008df835d953480011ef02bb2a69000e3d2057654d200047dc02eca9a400287c8759553480054b906b2aa69014e9d2056554d200145e422eda1a400087f855d9434800f0f90abb286900023de057650d2001c7a40aeca1a40028be87d91434800d1bd0fb1a86900031dd9471549202463a328e2a924064cac76dd152480c7958ec3a2a490127391db7154920246723b0e2a924000da4741c552480af17b0fb2684900063b219754c9200045fc22ebb0a40068bc845d761480011ef0eb08c2900029d215611852000c76432e5a8a4000ce572d87514800117f08bb0a29001a2f21176145200046fc1aec28a40028dc835d851480071e902bb0a2900063b219721452001e7230ae428a4007c78655c0514800717d093b6829000237e0d76905200146e41aed20a40058ec821d941480071790eb22829015f2b1c9645052001d5a40ac8a0a40018ee86dc9414800117b0fb2082900022fe11768c5200345e422ed18a4000ccc764c9314808f1eb0fb0c429000e2fe1d64d53100051fc2ac9aa62003cb67159354c40031ed03bb2a98800a1f21576d4f1001c6fc3ac7a9e2000a5f8558f53c40079ace2b1ea78800a1f6177654f1000c7b40eeca9e2053c7651dd953c40031ed03bb2878800e2f21d6450f1001c6e43ac6a1e2051cb471dd162c40a1968e23a2c5880063d2057694b100045fc22eca9620068bc845d952c40d71ef02bb2a5880063d2057654b1001c3e43acaa962003c747159552c40a117f0eb2685880063d2057690b1028c5fc22eca1620018f4815d942c40071790eb22858800f2d1c
  | 4 => 0x44c0033b50fb82a6980023be1d621893002c3e42aeda9260008bf845db524c00d17908bb6a4980063721973d493003e2e32ae7a9260019d8805cf524c00f4b90ca9ea4980e6d620153d49300345f424eca9260008bd849d9524c0071ed033b2a4980023d60676549300061fb28e8a926063c3c651d1524c00f4b90ca9aa498003171d953549301adac402a6a926000c77651c5524c0918e8ca38aa4980035554c715493000c6e432e6292600087f855db424c00f0f90abb684980162f21176d09303251e42ac921260008bd849d9424c00d17d093b084980022fe1d641093031d1e42ac821260018dc865cc424c00b1f10cb8084980022fe1175d85300345e422ebb0a60008f787584614c0031b90cb9ea2980067620173d45300061fb2ce928a6062c3c659d2514c00f4b90ca9ca298003179d9539453012dac402a728a60008bf845d8514c00d17908bb0a29800637219731453003e2e32ae628a6007a5c8654c514c0436b100a98a29800e3e219701453003e3c32ae028a6000d59535c0514c00717d093b6829818a8f21564d053002c77414eca0a60008ed829d9414c0071790eb2282981868f215645053036657320e4a0a6000cad641c9414c0010ff0abb0829801e1f21576105300045ec3ec820a60068be849db214c00117b093b642980021fe15768853003c3e42aed10a60008bf845da214c00d17908bb4429819eaba1362885300345f424ec90a60008bd849d9214c0071b9073b042980063e202760853000c6e432e610a606caae84d88214c00199ae7b10429800e3e219700853000675b12e010a600787e87cc665c80010fb0f98ccb900028fa1031997200051ec206332e400587e8794d65c80018bee729acb900030fdd274597200053b40ce8b2e4000a75819d165c800147d0939acb900028f61273597200062fb9ce6b2e4005a6e829cd65c80014db0539acb900029da0673597200053ac0ce6b2e4000a7b805cd65c80018bae639acb900169ba0a435972000536c1486b2e4000a3e849c565c800147b0938acb900021fa1f31597200043ec3e62b2e4000a3e840c565c800147b0818acb900169ba08315972000536c1062b2e40058be8790d64c80b517d0e21ac99001f1b99572d532002c3fc3acb2a64000a3f8459654c800b0f90eb2aa99001f1b995721532003c3f42ee2b1e400087d85dc563c800f8dccab96a7900063ba0b7654f2002c3e43acaa9e4002a5c8359553c806b8f0e0b2aa7900031e5977054f200145e422eda1e40058df8758f43c800517b09bb287900169b2177654b2002e37baeeca964064e2e65dd152c80c7c5cca3a2a5900029be195454b2000537c32a6a964035b688054d52c8093ccccbb8aa590123999947154b20006d23a0e2a9640019e8805d532c800f8dccab96a39018b0f99674947200061eb2ce
  | 5 => 0x1432b984725074028656308e4a0e8066daa801c941d00cdb530039283a019a2f21d625074033656392c4a0e8003ab48158941d000317d09bb263a00022fe19744c740334d6412e898e80018bc845db21d00a317f08bb243a00062f211764874001c5ec22ec10e8000a3d8494f65500018bae729ecaa01cf0fdd774595400146f43ee6b2a8000c5f751cd655000193ee839acaa0003361cf70595400043fc3aca32a8000a5c83594655000d47909b2ea8a000a2f21172d8d400043fc2ae3b1a800787c855c763500018b8c63aac6a00062f21974d4d400052ec2ec7a9a8000c9d74d8f53500031790cbaa86a00066e2017550d400154f436c6a1a80008ef87588625000b0f90abb6a4a000237e0d76d49400146e41aeda9280018bc865d3525000f878caba6a4a001e8f21954d494000c5ec24ed29280038f6819d952500011eb033b2a4a001a2f210765494000c5f436e8a928000c3f65dd152500c9878cbba2a4a001a4f21d545494003d1e432a8a928000c3c7655152500018eeca38aa4a01231d194715494000c5e432e82928064c3c655d642500c71790cba884a018f0fe1975109400061e432ea2128006c3f605d4425000da76c0ba884a01422f219711094000c5ec24ed19280018be86dd1325000193ee9b1a64a00023de1d611854000c5e432e9a8a80038bc849da51500031790cba4a2a00030fd95749454030e1e32ae928a80008df835d851500051b906bb0a2a00062f219741454003e1e32ae828a8007c78655c051500c51790cbae82a015e2f61f62d054001d5b40ec5a0a8061c3c65dd541500031790cbaa82a015e6b2097550540296563b6e4a0a8000da870dc941500a1958ec39282a015f2ba1872505402be56c30e4a0a8057d2e851c941500afa5b0a39282a00032b994725054000656328e4a0a8000caf631c941500a195cc239282a01432b184725054033657b00e4a0a806cdab601c941500a117d0fb1282a015f2b1cb6250540006d4396e0a0a80018bc865d2315000193ae9b1c62a00062f219744c5402bcd6412e898a80018bd849db21500010ff0abb442a001e1f21576885400046fc1aed10a80028dc835da21500031790cba442a001a2f210764854000c5f436e890a80038bc849d821500031790cba042a015e6b209740854000656ba6c410a8000ceb625c0215000187eea3a2ca981df17dd773595300064e3a6e6b2a6000cb874dc1654c0010ff0eb28ca980028f21165195300061e3aee8b226000c5c75dcd644c0018f0ebb82c8980022fe1d64191300051e42ac83226000a3d85d93544c0031b90cb9ea89800327d9173d513000cec402e7aa26000a3d84d96544c0010ff0abb2a8980022fe1176551300046fc1aecaa260008fb805d9544c00f0f90abb0a89801a2f211761513000c6e432e62a26006c9c645cc5
  | 6 => 0x9753882c9a104203a778759751084078ef0eb2ea2108031d59570d442101d7840aeab004200aba841d56008401573083aac010802b6a0c75580210056cc18eab004205aea821d5600841f5d3043aac01080ebca04755802107d78c08eab004205ae8825d160084075e5023a2c01083ebc604745802102d75416a8b004200ae982d516008401c76a92a2c01080ebca06545802100578c0ca8b004205ae8825cd60084014f50a39ac0108029e61473580210055d420e6b004200ab9841cd600840b5d50439ac01083eba608735802101d79408e6b00420faf1811cd600840b5d505a9ac010802ba60b53580210072da9ca6b004203af28194d60084015e30329ac010816baa0a435802100574c1486b00420287d85dc563d40012f30bb8287a800b171cd5358b5029e3a38aa6b16a000cb774dc562d4001968e9b8ac5a80032ddd07158b500065a3a0e2b16a0648bf845d942d40011ef02bb285a800e3d2057650b5002c3ec2aec216a0068bc845d842d400117f08bb265a801a2f211764cb500047bc0aec996a0038f4815d932d40012f30bb8265a800e2f21176d075001c5ec26eca0ea0008ef825d941d400b1d904bb283a80022fe1176c87500345e422ed90ea0008bf845d921d400d17908bb243a81263de05764875001c3ec2aec10ea0038f4815d821d400147b0b21ec8a80022fe1d64191500054e41ac8322a0008bf845cb635400d17908b96c6a800a1f21571d8d500064e318e8b1aa078c6d75d8a625409b8eeca38ac4a80023be1d621895026e3bb28e2a92a00587c859d842540011bf06bb084a800a3720d761095000c3e432ea212a000c3d75d9042540011ef0eb08c2a81369de15611855001c5e422eda0aa0008df835db41540051b906bb682a80163ba0a765055000476c14eca0aa003ab681d91415400195ec839282a81b32b19072505500045fc22ed90aa0068bc845db21540011bf06bb642a800a3720d76c855026c3fc2aed10aa0068be849d9215400117b093b242a800e1f216760855000c3e432ea10aa000c7575d8421540019e6c2b8042a801b0fdd776553400145ec26e4b1e800787e85dc563d00010fb0bb8ac7a00062fa137654f400045fc32eaa1e80019b8805d543d000317908bb4a5a01ba2fe117654b4000c5e422eca9680008f7815d952d00071e902bb2a5a001b0f1d16554b402463b328e2a968000c75651c552d00c917f0cbac85a01930f9957590b4028c5fc32e321680018bc845da32d000317908bb265a00023de05764cb4001c7a40aec99680038bd845da51d000d87ce8b2ca3a00062fa13765474030c5ec36eaa0e8061c3e65dd541d00cd35904baa83a00032bdd8725074033657430e4a0e8066cad861c941d00cda5d0a39283a019b4b614725074000657328e4a0e806ccac651c941d000195ac639283a
  | 7 => 0xb681101640840187eeb3aac810816aba0a755902137656394eab204205aac825d5640840756902baac8109b72b1c875590212d656396e6b204205aae829cd640840155b0539ac810816ab20973590212ce56392e6b204203ab4815cd640840756d0329ac810802ad606535902133656396e0b204205aae829c1640840155b05382c81080eada0670590210055ac0ce0b204205aac825c1640840756d02382c810802ad604705902101d5b40ca0b204200ab581941640840117d0e282c8108022f61c50590210054f418a0b204200a9d83141640840b55d04282c810802ab608505902101d5b408a0b204200ab581141640840756d03182c810802ad60630590210045f43860b2042008bd870c1640840147d0a182c8108028f614305902102d5741060b204200aad820c1640840756d02182c810802ad604305902101c5fc3ac9aa04200a3f8559354084dd55904b26a8108172b9c964d502103e3732ae5aa04200cad645cb54084070ff0eb2ca8108028fe11659502103d1fc36a92a04200a3d86d52540840d87eedaa4a8108030f5db54950213a70f31ea92a04273e3a60d5254084018eacab8ca81081b2d991719502102c76412ecaa042038f4815d954084070f90eb2aa81080e2f21d645502100636b2ee4aa04200cad64dc954084018eacbb8aa8108032d593715502136e56212ec2a0426daac8259054084075ad03182c61080317dd67558c2102d67414eab184203ad4815d5630840b59904ba2c61080eb52057458c2102d67416a8b184200acd82d516308401c3ea92a2c61080eb5a065458c210056ac0ca8b184203ad6819c163084015ab03382c610816b32097058c210052f428e0b184200a5d851c1630840153d08382c610802a76107058c2102d67410e0b184210acd821c163084075ad02382c610842b56047058c2101d6b40ca0b184200ad58194163084011bd0e282c6108023761c5058c210054f420a0b184200a9d84141630840b59d04282c610802b36085058c2101d6b408a0b184200ad581141630840b59d05202c610802b360a4058c2101d6b40c80b184200ad58190163084075ad02202c610802b56044058c210062f29aeda984202a5e8359753084a94e902b2ea6108038794e64d4c210070f29ac9a984205cae7259353084071bf0eb1ea61080297e1563d4c2102e67392c7a984207c6e655cb53084d935908b96a6108032b59172d4c2100666b1ae5a9842038f4815d953084070f90eb2aa61094e9d2056554c2101c6e43ac6a984200c7565dc553084019aac7b8aa61096aab20964d0c2101c6fc3ac7a1842058ec825d943084071e902bb2861080e2f21d6450c212cd56412c8a1842038dc8758d430840195ac9b9286108033358f7250c210065ab26e2a184200cd563dc5430840b55f0eb2684108172be1d64d08212
  | 8 => 0x8bb6a6908038794f64d4d210070f298c9a9a42068be84dd9534840117b09bb2a6908022fe117654d210345e422eca9a42008f7815d953484011f700bb2a6908063e2017654d210143f43ecaa9a42078de87d8d534840517908bb686908022fe117650d2100477c12eca1a42008f7815d9434840517d0fb2286909c38b94b64d49212845f436e8a9242518be861d152484dbb48423a2a49098e2fa1f645492128c5e43ec8a924251cb471d9152484c917d0e322a49081a2f21c64549212865a388c8a924249c7465dc5524840196ec9b8aa4908032d19371549210365a322e3a124251cb471d91424840196ec9b8a84909432d1c4644c9210065a326e29924251e3651d9351484df95ce4326a2908032b19172d452135e73b0ae5a8a42008bf845d9514840d17908bb2a2909bf2b1c8645452100656326e4a8a4206cac645cb41484e1958e5b22829099f2b193725052137e56390c898a4200cac64dc931484938eec23aac0908022fa1f64581210061fbaec8b024200c3c75d916048401938e7b22c0908022fa1c64581210061fba8c8b024200c3c751916048401938e6322c09080327d9373581210064e326e6b024203a768110265084014eb02204ca1081e1fa1c30994210043ec38613284200a3e840c2650840147b08184ca108169ba08309942100536c10613284203a76810c265084014eb02184ca1080e1fa1e53594210062fb9ca6b284203a7681941650840147d08282ca108028f61050594210052f418a0b284200a5d83141650840b4dd04282ca1080e9da0450594212663a388a0b284200c3f749d165084074ed033a2ca108169b209745942101d3a40ae8b284254c7471dcd65084018bee739aca1080e9da0673594210053ac0ce6b284203a74815cd65084a78e8e2b9aca108169ba0a435942100536c1486b284203a7481dc165084074ed03382ca108029d606705942126e3a38ce0b284203a74815c1650840147d08382ca108028f61070594210052f418e0b284200a5d831c1650840b4dd04382ca108029b608705942101d3b408e0b284200a75811c165084998e8e2382ca108169ba0a405942100536c1480b284203a768190165084014eb03202ca1080e9da0440594210053ac0880b284203a76818c165084014eb03182ca108021fa1c30594210043ec3860b284200a3e840c1650840147b08182ca108169ba08305942100536c1060b284203a76810c165084014eb02182ca1081a2fa1c50990210045ec38a13204200a9e83142640840153b06284c810816aba08509902100556c10a13204203ab681142640840156b02284c81081a2fa1c30990210045ec38613204200a3e850c2640840147b0a184c810816aba08309902100556c10613204203ab6810c2640840156b02184c81080e2fa1e435902101d5b40c80b204203a
  | 9 => 0x71597210053ac0ca0b2e4200a3d8414165c84014bb06282cb908169ba0850597210053ac08a0b2e4206a3c8459754c840d1ef0cb8ca9909ba2fe11765532102c3e43acaaa64200c7565dc554c840d17908bb0a99081b2b19172153210045fc22eda9e42068bc845db53c840117f08bb2a79081a2f2117654f210047dc02eca9e42018f8805d953c840b0f90eb2aa79080a9720d6554f210063ab2ee2a9e42028bc845db43c840517b09bb287909269de1d65d472138e3bc3acba8e4200e378459751c8401c6908b2ea3909ae79e1972d472124673c32e5a8e426bc777159551c8493ae0a0b80a3909462fe1d64d072129477c32e5a0e4205cac7259141c840717f0eb26a9108028fe1564d522103c77c32e5aa44200cad645cb54884050f90abb6a71081e3be1972d4e2133cd6422e5a9c420287d85dd953884071790eb2287109ae3de1971d4a212845fc3ac9a144203cb471591428840f0fd0fbaac1108029760c50d952100536c10a1b2a4200a758114365484018becab9cca9081f171957399521006563a6e4b2a4200cb774dc56548401968e9b8aca908021fe1d65195210055ac0881b224200a9e83997644840153b0732ec8908028fa1663d91210051ec2cc7b224200c3d751d764484a317d0f996c8908022f61f32d91210051f42e63b224200a3d85cc764484a356d03386c890802ad60670d91210045f438a1b2242008bd87143644840153d06286c890802a760c50d912138557410a1b224200aad8214364484a356d02286c890802ad60450d91210045f43861b2242008bd870c3644840147d0a186c8908028f61430d91213855741061b224200aad820c364484a356d02186c890802ad60430d91210045ec3c41b224251ab681883644840156b03106c8908022fe1d64191210045ec3cca3224200a9e83994644840153b07328c8908022fe1d65191210051f42cc63224200a3d8598c64484df55d04298c890802ab60853191210345f43e6432242008bd87cc8644840147d0b988c8908028f617311912137d57416623224200aad82cc464484a155f04908c89081a2fa1c50191210045ec38a03224200a9e83140644840153b06280c8909beaba08501912100556c10a03224250ab681140644840156b02280c89081a2fa1c30191210045ec38603224200a3e850c0644840147b0a180c8909beaba08301912100556c10603224250ab6810c0644840156b02180c8908022f61e20191212855b40c403224200ab58188064484df55d05080c890802ab60a10191210051ec2ec9aa242068bc845da54484011df04bb2a8908023de05765512103c5f43ec8aa242038ec865c8544840d958c8b90a8908022fa1f6458d210045f438c8b1a42068be87dd16348401958e9b92c6908032d1d37158d210143e42aeda9a42008bf845db534840d179
  | 10 => 0x3128200aad84cc062504d955d09180c4a0802ab61230189412857340c603128200ae5818c0625040b1dd0e180c4a08023b61c301894100537428603128200a6d850c062504d955d08180c4a0802ab610301894128573408603128200ae5810c062504d955d09080c4a0802ab612101894102c3f42ceda9282038bd849db52504c387ea93b6a4a08169b20965d494100536c2ec5a9282058ec825da525040b958c4ba4a4a080e6d205749494102c3e43acaa92826ecac62dd15250401878edaa2a4a09bb8b18b545494133e563a6c4a928252ce471d8952504d79c8c5b8aa4a08172b18974149410365bb0ceda128250caf829db42504a195c433b684a09432b08676d09412ce56312e7a128200cae76d8b42504a195cec31684a095f2b18970d094102e72312e32128252ce471d8942504b5958c5b9a84a0816aba1b6250941296563b6c4a128252da471d8942504a195cec31284a0943691c4625094101cdb43ee2a128252da7721c542504cd958c5b8284a08163b209768c94102e56312e919282039b4815d232504071790cba264a09672b189744c94101cda40ae899282028ee87d8932504a5ccca3b16a2a09b32b9d062d454100656ba0c5a8a8200c3f65dd1515040195ee8312a2a09b32b1d0625454100c5e422e5b0282008ee87d8960504018deebb12c0a08031b1d7625814100667b9ec4b028200ccc73d8960504011dd0e312c0a08031bdd46258141006363a8c4b028200ccf731896050401998e6312c0a098a2fe1974d4c413145fc32e9a908203c7471595521040117b0dba264208062f613725804101c5fc3ac9aa46200a3f85593548c40f1bf0cb9ea9188032759173d523103e2f32ae7a9462008bf845d9528c40d17908bb2a51880e3d2057654a312845fc3ac9a1462018f581dc9608c4014bb06286ca988029d60450d95310043fc3aca32a6200ab581103644c40195ee8392c898803391cb71591310045fc3ac83226200aac82590644c40d17908bb4a8988023be09769513102c76412ed2a262028f4865c6544c4011df04bb2a8988163b20976551310047dc02ecaa262018f8805d9544c40f17d0fb22a89880e3721973151310043fc2ae1b12620787c855c3624c40155d09106c4988023be1d621893100556422c4312620587e859db524c40117f08bb4a49881a2f211769493102c76412ed29262068be849d9524c40117b093b2a4988161f21d655493136e56310e8a926200cac74d89524c4051ed0db8aa4989af3918b71549310361e322ea2126205c6c625d4424c40187aebb20849881b27191731093102e66312e62126200c6d75d88424c40b1e90cb88849894e1f61f65d45310062fb2ee6a8a6200caf641c9414c4d9958c839282988022fe1172d81310345e422e5b0262018f4815cb604c40196ee9b8acb908032d1d3
  | 11 => 0x504010ff0ab86c4a081e1f21570d89410056741ccbb128200acd8399762504a555d0daa6c4a08038bd9754d8941295d340ea9b128200a6e8598f62504014db0b31ec4a094aab21943d89410074631a87b128252aad84dd762504cf5cb03baec4a08031b5d475d894133f172a6a9b128200a6e859cf62504014db0b39ec4a099eaba1073d894129556c20e7b128200e4f5394f62504014dd0b98ec4a08029b61731d894100537c2ae1b128200a6c855c362504cf55d08386c4a094aab61070d894129573408e1b128267ae5811c362504011dd0e286c4a08023b61c50d894133d57420a1b128200aad84143625040159d06286c4a0802b360c50d894129573408a1b128200ae58114362504011dd0e186c4a08023b61c30d89410053742861b128200a6d850c362504cf55d08186c4a0802ab61030d89412957340861b128200ae5810c3625040b8d8c53a8c4a08171b189751894100477c3ac43128200c6e769d462504e1c5ec93a8c4a08031b9d9751894138717b22ea31282008ed87994625040159d07328c4a0802b360e651894100477c3aca3128250aae86d506250401c5ecbaa0c4a08038b1975418941285d340ea83128200aae8615062504011db0f318c4a08029ba16631894100536c2cc631282008ef8758c625040155d0da18c4a0942ab219431894100747b1a86312826ce2e54d5062504dd55b0faa0c4a09bb8b9d7541894137716baea83128200aad83d5062504a155d03aa0c4a0942ab207541894100556c06a83128200ae78155062504a15c902aa0c4a09b6abe1c541894136d56c38a8312826ce2e8515062504dbc5cea2a0c4a09b78b5d4541894100556c18a83128250aae8115062504a1559022a0c4a0802ab600541894136557424a63128200aad8494c6250401c9ea7298c4a0942b9a06531894100572c0ca63128200aaf8454c62504d955908a98c4a09b2aba10531894100556c20a6312825aaaf87d0c62504b555b0fa18c4a0802aba1743189413655642e86312825ae2e75d0c62504b5c5aeba18c4a096ba39cf43189412d746b9e863128250aae81d0c62504a155903a18c4a0802ab603431894100573c0a863128250ae48150c62504b355f0ea18c4a0802aba1543189410055642a863128259e2e7550c62504b3c5aeaa18c4a09b3a3e0d431894100753c0a863128250aae8150c62504a155902a18c4a0803a9205431894100557c02863128250aaf8450462504014dd0b988c4a08029b617311894136557426623128200aad84cc462504d955d09280c4a0802ab61250189412857340ca03128200ae581940625040b1dd0e280c4a08023b61c501894136557420a03128200aad84140625040159d06280c4a0802b360c501894128573408a03128200ae58114062504a15cd03200c4a0802b960640189413655742660
  | 12 => 0x802ab608305925101d5b40860b24a200ab5810c1649440117d0f102c9288022f61e205925101d5b40c40b24a200ab581881649440756d02102c928802ad60420592510365b322e32a4a261d37545c6549440196ac9b8aa92881a2fa137258e510045ec26e4b1ca2038bc8759143944014bb06282c5288029d6045058a5138c7bc32e3294a2008bd86dd152944c9a6ea3ba2a5288022f6187454a513745f43cc8a94a203cb47199152944db1790eb22a52880f2d1c56454a510065b326e2a94a200cb564dc5529440b55904b22852881b0f9917510a5130e1f3aac8214a200c3d75590429444b0fd0fa9ac12880b179cd535825112d3c402a6b04a2068be84dc9609440117b09b92c1288029e61730582510072ca9e60b04a2008bf87590645440155904b20c8a89862f61f64951510045fc22e5b1aa2068bc845cb63544011df0eb10c4a8802ab211621895136e56310e8a92a200cac74d8952544d79c8c5b8aa4a89bb0f1db745495136e1e3b0e8a92a26be676118952544d78e8edb8aa4a88034ddd071549510061ebaec9212a200c3d75d9042544018daebb1084a88022fe1172d81510345e422e5b02a2038bc8759143144a3968e3ba2c428947a908774588512865a388e8b10a250ea4211d162144058b8e6a9ac42894f99085535885126f3210ca0b10a2508bf87593421440d55908b14842880f2d1c5645085101e7238ac4a10a250ce4215d8421440117f08bb2642881a2f211764c85101e6a38ac6990a2038ec8758932144079c8e2b1264288861f21d535805110d3c402a6b00a206a3e8414165d04014bb06282cba08029b60850597410053ac08a0b2e826e8bf865cb54d04dd95cc4b96a9a080e6d20572d534101c5e422eda9e82038bc845d953d04011f700bb2a7a08063e2017654f410143e43acaa9e8202a5c8359553d04b317b0db9287a081e1fa177058b410043ec2ee0b1682038bc845db52d040717908bb2a5a09271d9977154b410063ab2ee2a9682038be84dd932d040736902ba265a080b271cd435834101c7a40aeca948264c3e65dd1529040187acbba2a5209423be1d6290a4101e7238ac4a148200a3d84943655040147b08286caa08029760c50d95410053ac08a1b2a8200c5f655ce655040f8b8cab9ccaa08032bdd0725954100672396e2b2a820087f8759465504c347b0fb2ea8a08030f61f65d51412845e432e5aa2826ecac625cb54504c387ee9b2aa8a081b2dd86761514136c5e432e42a2826dcac625c8545040736902b90a8a080e2f61276d4d410143e42aeda9a82008ef825db535040b1d904bb6a6a08163ba0b7654d4100476c16eca9a820287e87d95535040187ecbba2a6a080e6da077454d412d45e432e5a1a825acac625cb43504a117d0db9286a09672b18b7250d410053742865b128200a6d850cb62
  | 13 => 0x53b40860b288400a75810c1651080d47d09082ca210028f612105944202d3741420b288400a6d82841651080d47d08082ca210028f61010594420351fc3acbaa08406c3f87597541080187acab86a82101e1fa177158c420043ec2ee2b1884068bc845db53108011f700bb2a6210063e2017654c4202c3e43acaa988406c3c7459553108054b906b2aa6210030f5977454c422845f43ea8b088450ab681d5161108a11790ea1ac22100b271cd43580420051ec20a0b2c6400a5d83141658c80b4dd04282cb190029d60450596323345f43880b246400ab581101648c80b0f90eb2aa9190162f21d64552320346fc32e62a46400cb774dc5654c801968e9b8aca990032ddd071595320065a3a0e2b2a64018fa87dc1654c801976e9b82ca990032e1d3705953200679b8ee0b2a6400cf071dc1654c801976e8382ca990032e1d070595320066db98e0b2a6400cf3711c1654c8019e0e2382ca990021fe1d65195320065bba0e2b226400ce7721c5644c80117f0eb20c899002ad20564191320051ec2ec9aa264058dc865cf544c80193ec8b9ea89900a3b21972d513200657b22e5aa264008bf845d9544c8011ef02bb2a89900e3d20576551320047dc02ecaa264018f8805d9544c80d17908bb0a8990023de05761513201c7a40aec2a26407c5c655cf524c8018becbb9aa4991662f61f64d09320045fc22ebb0a64068bc845d7614c8011ef0eb08c299002ad21161185320345f426e4b1ea2008bd84dc963d440155d09992c5a8802b96073258b5103d3742864b16a253c747158d52d44018eeedb8aa5a88034ddd07154b510069a3a0e2a96a200ce5625c742d44012eb0bb8a85a881f0f9d56410b5103e373aac4216a20097585dc532d440d17d09b92c1a88022f61372583513170fa9ca7324a2068be87cca649440117b0f994c92898a8fa1432992510051ec2865324a2068be870c2649440117b0e184c92898a8fa1430992510051ec2861324a200aae820c2649440155b04184c92880eada0430992510055ac0861324a2068be87882649440117b0f104c92880eada0620992510055ac0c41324a200a3d8590d649440756d03202c92880eada04405925100557c12eab24a200aac825d564944c347d0b39ac9288028f616735925100557414e6b24a200aad829cd64944c3c3ea729ac92880eada0653592510055ac0ca6b24a200a3d851c9649440195ae4392c9288022fa1f32592510045ec3e64b24a261a3e850c9649440147b0a192c928802aba0a705925100556c14e0b24a203ab6819c1649440156b03382c9288028fe15705925101d5b408e0b24a200ab5811c1649440756d03282c928802ad606505925101d5b40c60b24a200ab5818c1649440117d0e182c9288022f61c305925130d1f42860b24a200a3d850c1649440155d04182c928
  | 14 => 0x58290061548071ed0e200c2a90023d61c40185522453b42e6030aa400a7585cc06154801caaa7980c2a90029de1630185522453a42c6030aa4038f6870c061548011eb0e180c2a91229da1430185520053ac286030aa400ab6840c0615480156b08180c2a91c6b9a08301855200572c106030aa4008f587880615480156d09100c2a9002ad61220185523761ebaec9b02a400e3a50d9360548db87aea326c0a91af1d5d761d815238e3aba8c3b02a43587d87d4f60548058b8e6a9ec0a90d69e20153d81520053cc2e61b02a400e5953cc3605480117d0fb22c0a9003271cf64581520045f438c8b02a400c9c73191605480193ec9b9ac0a90032719373581520065bb26e2b02a400cb464dc5605480196ec838ac0a90032d19071581520047b43ec2b02a400cb774d856054801968e9b0ac0a900335dcf61581520066a39ec2b02a4008f687185605480196ee830ac0a90032d1d061581520066bb98c2b02a400cd47318560548c717f0cba6a7a11ba2fe1974d4b420051ec24a0b2c8400a3d8414165908014bb06282cb210169ba0850596420053ac08a0b2c8464a3f8759754908db87f0eb2ea9211ba6be1972d524231e57c32e5aa4846ec3f74595549080d35908b96a7210161f21d6554e420061eb2ee8a9c84518be8715161908a356d022a2c3211462fa1f43586420065bba6e2b2a8400cb7741c565508019cee438acaa10021fe1d651954237657b22e5aa28451cb7641c563508c917f08bb6a6a101a3b21972d4d420061fb2ee8a928464c3c65dd152508e3b488438aa4a10029da1731d85420055ac2063b0a84008f787584615080f0fd0f98cca210021f61f31994420351f420633288400a3d840c6651080f0fd0e184ca210021f61c30994420351f420613288400a3d840c2651080b4dd04184ca210029b60830994420053b408613288400a75810c2651080d47d08084ca210028f61010994420062fb9ca6b288406a3e84941651080d47d08282ca2100297a0c50594420052ec18a0b288405a6e8214165108014ed02282ca210029d60450594420351f424e6b288400a3d849cd65108018bee739aca2101a8f21173594420053dc02e6b288400a78805cd65108018bae639aca2101a8fa1271594420351e422e2b288405a6c825c565108010fd0f98aca210021f61f31594420351f42062b288400a3d840c5651080d47909b82ca2101a8fa1270594420051ec24e0b288406a3c845c165108014bf06b82ca210029720d70594420351f420e0b288400a3d841c165108014bd06382ca210029760c705944202d37410e0b288400a6d821c165108014ed02382ca210029d60470594420351f42460b288400a3d848c165108010fd0e182ca210021f61c30594420351f42060b288400a3d840c1651080b4dd04182ca210029b608305944200
  | 15 => 0xb98ec2a9002ada1031d85520055ac2063b0aa400ab684043615480156b08086c2a90038d61464d85520071a326a9b0aa46ba7486553615480156d0931ec2a9002ad61263d85520055bc22c7b0aa400ab48458f61548015e700b1ec2a9002bc20163d855235d3a432a7b0aa400e546354f615480156d09306c2a9002ad61260d8552004bb438a1b0aa400b358414361548016ab06286c2a91aed9a0850d855224d72c16e9b0aa46ba75851d36154893c6ea92a6c2a9126b960b73d85520055b424e7b0aa400ab5849cf61548934ed0a39ec2a91ae9d61473d855224f2ba9ca7b0aa400ab684ccb615480156b09996c2a91ae9d61770d85520055b424e1b0aa400ab5849c361548d75cd04386c2a9126b960870d85520047b43881b0aa4008f58710361548011ed0e186c2a90023d61c30d855224d3b42861b0aa400a75850c3615480156d08186c2a9002ad61030d855235d7341061b0aa400ae5820c361548011eb0f106c2a9002ada1220d85520055ac2441b0aa403cb4619d26154807968c2ba4c2a90032d9d361985520065aba6c330aa4008be87d91615480117d0e322c2a90023de1d61185520055bc22c230aa400ab484584615480196cedb20c2a90038d5d764185520047ac3cc830aa4008f787590615480196cec320c2a90038d61464185520071aba8c830aa479ea75219061548f3d48a4320c2a90038d193541855238d3a432a830aa4008f58798c615480156d09318c2a9002ad61263185520047bc3ac630aa400ab78458c615480156908b18c2a9002bce01631855200578402c630aa400e3764d4c6154801c68c9a98c2a91c69d21953185520071bb22a630aa400e346454c6154801caec6a98c2a90039518d53185520055b424c030aa400ab5849806154801c6ec9280c2a90038d192501855200738304a030aa40097587140615480166b08280c2a90038dd9050185520071a320a030aa400b558314061548e36cd04280c2a91238dd52541855200573c12a830aa471ae48255061548a94ef0fa98c2a91529d61f53185522a72b39ea630aa454e5573d4c61548014ed01a98c2a912395d4e531855229d3bc3aa630aa448e578354c61548014e900a98c2a91229da1643185520053ac2c8630aa471ae68290c61548015cb05218c2a91229da1443185520053ac288630aa400ab784548615480156908a90c2a91229da1732185520053ac2e6430aa400ab684cc8615480156b09990c2a91369d61e50185520053ac1ca030aa44ca778714061548998ed0e280c2a91329d61c50185522463ac38a030aa448e36841406154891c6b08280c2a912395a0c50185520053ac18a030aa448e558314061548014ab06280c2a912399a08501855224732c10a030aa448e72801406154899ce4e0280c2a91339c5c0501855238d734148030aa400ae
  | 16 => 0xd95430063cb84a1b2a8600a3d841436550c014bb06286caa19d30fdd7745954300c7d43ee0b2a8600c7b751c16550c01976e8382caa180336dcc70595430043fc3aca32a8600a78805946550c0f8b8cab9ea8a180317d9773551430043fc2ae1b12860787c855c36250c011df0eb10c4a1802b920562189430047bc3ac230a8600ae4825846150c011ef02b96c0a180e3d20572d81430063c300eab028607c3f74dd954d48a70fb0db8aa7a90161fa177650f521ccbc402eaa1ea4028bc8759143d48730f90ea9ac1a90e69e201535835236c5fc3ac92a4a400a3d8590f645480156d02206c8a9002ad60440d91520055b40cc7b22a400ab58198f645480156d03306c8a9002ad60660d91520049f438a1b22a400b1d8314364548dd65d04286c8a9002cd60450d91520064fb9ce7b22a464a3e851cf64548dd47b0a39ec8a91baaba0873d915232556c10e7b22a464e1f5394f645480117b0f996c8a9192ab60b71d91523751ec28e3b22a464a3e85cc7645480147b0b98ec8a90022fa1c31d91520045ec3863b22a46ea3d85dc3645480156d03386c8a9002ad60670d915237557410e1b22a464aad821c364548c9c76a1286c8a90022fa1c30d91520045ec3861b22a464a3e850c3645480147b0a186c8a91baaba0830d915200556c1061b22a400ab6810c3645480156b02186c8a90022f61e20d91520055b40c41b22a400ab581883645480117d0e086c8a90022f61c10d91520065bb24e3322a406cb4649c6645480196ec8b8cc8a901b2d19171991520045fc3ac8322a400ab781590645480156902b20c8a9002ada0663191520055ac0cc6322a400ab681980645480156b03300c8a90024f61c50191520058ec18a0322a46db2e82140645480166b02280c8a918f87d4e53191520045ec3e64322a463a3e85cc4645480147b0b988c8a901a2fa1c31191520045ec3862322a4068be870c0645480117b0e180c8a918e8fa1430191520051ec2860322a46daae820c0645480155b04180c8a9002ada0430191520055ac0860322a4008bd87880645480156d03100c8a9002ad606201915236d5741420322a400aad82840645480d17d0e080c8a90022f61c10191520061f3b6c9aa2a46ecac72d9154548dd878edb22a8a91bb4bdd072551520045f43ec8b1aa400cb870d91635480117d0e322c6a90032e1c06458d520065bb26e2b1aa400cb464dc5635480196ec838ac6a90032d1907158d520065db26e0b1aa400cb864dc163548a90f90cb8ea6a91bb0f1db6454d520070e31ec8a9aa46dc3c761915354801c38c6322a6a900a97a1b6354d5229e3a30ee2a9aa4028bc845db43548011ef02bb686a900e3d20576d0d5201c7b40eeca1aa4008f581dd9435480b0f90cbaa86a90d65e2017550d520145f43ec8a1aa402a9e83d9143548014eb0
  | 17 => 0x400005e00000006400800200001a00000000001c0020a800601201001000002200800600a00200000000004405400401000800000802400000000a00001c00400000000600200000200600003401600000000200000001006200201c01200800a01201200000200600400000e00400600200a03600000200800c00601c01000400401208e00200e01c01200800402400200600e00a00200c00001400a00600200000e00001a00200600c00800000000200e00000003600600000800a00e02600000200c00600001e00200200000800000405c00200200000602800c01000200200402600602a01a00001000400200a05c00205200a00000000c00000400e00200200200c00000602e00e00001400000a00000401000c00c00800000000000801601000001800000200e00000000a02a00400400201200601006000200004000600801200a00201401e00000007200200000203600001c00600806602c01600400602200e00a00e02e01402000200000a00400000000e00601204200602000000201402600800000000005600000404002000000a00400200000000002401000a00000200400000000800c00002600600a00200400400800c00400400a00000a01c02200a00003000000200a00600800000600001200200001400801a00002800000000603a04a00400400801a00000201801c00000601e00000c01a04600c02601201200e00800200600000e02e02e00a01800e00000400000000402605000803800000000801000001200000402600200c03a00e00c00c00200401601400201000201000800000002405a00800800000000000400000600000a01400003e00001800002600000200801000000000200801c00c00201400201200001201000201200c00600e02600000001004400000e00000200001400601000600000400000000600400001601c00203200200400800400a00201c02800200600804600003c01201200601602201202001000200200200e00000400c00000400000000603600401a00200400c01000606801800e00200e00c00a00400000002000c01000a01600205401001400c00400003604000000200000e0060c800000600000e00800402000000400001400a00001200000200003600000600c04200401a01200000400005000602800e05200204400400002401400000600e00c00a038f681dc960950011eb03b92c12a0023be1d62189540057240ac4312a86ecaf641c961550011ef0eb08c2aa002b920961185540047bc0ae5b02a8038f4815cb605500d55d09992c42a01e9ba1432588540051ec2c81b22a600ab5811036454c0117f0eb20c8a9802ae201641915300477c3ac4312a6008f7875846154c0117f08b96c0a981a2f21172d81530047bc0ae5b02a6038f4815cb6054c01970c03a2c0a98028f6125
  | 18 => 0xe2c3f01580191e705421eb27a08c85e6554131800026084a1f790206ba6b43b093f4dd224c1d9000074056c38180000000000000b40000000000192c00000015f800022000035e90f462675f2079ccc26a2a817899185283c846c24e00005c013aa2cce8e2262690000000618008083c00061d2a5195000072d2cd0224e680001f30000a6c06c30215f07800000000170c908a21cc1dc030a0000398ae852a0000eb00000004e7000000052c0003869cf45bc5b54270288b0a0000ab80009de3200000ba80003d02838000fba1b703c00000000000001fd0c4e04f03e872518674a00a9a085ce8000b400000008f91e61f2039a473017952087e1cb0ee9e5413e0503589a048504c64288708d2c4ab41503106726ac1da1274b542500531f34f5456900002c872449e00014b117a0000890000c188cb0a4936ce5083a25724503444392060e1cbc24b8000000006e0000001044410088416800039e4e926705b829e4162188da428e0ef31c8c502ac82510915a8a2200034000000bc0f639b215c00023e191968510000041f00009960000b68d8020803a03a145800032131b0000ab63f70001690e26000000143cf227cb01f177000000000008803aa00000000000008c91c6a4248924962338ed88343191ef0294d7e0004578bfd04c01f1b30e40ff63011cc800076001342021503f665b477944c38200023b95fcd860642ef9fc46fa43846806cd2220003e01eb00000000000000000000026126000070e0000000e0a6f724d95484d600025e0000dd84f001e16211ee77225000011420000001ad80000000d021c8b6c00043480000000000000000fce6060e70fa40000000bf1d1877e60920e96b81686f403e0d2c00033300018c00048442da1f8d0488e800003306983ac000021481a7732f422ac70a5251f211a48c089c280187cc5e2a20b21a88a544a718922d00000003ed1db000201001200e00600200401200200000800600000203800001000e00008403c02001000401000600400000000000000000400800a00400a00000000a00200e00200201400800200200400600800600200000000200400200000800200801600200400200200a01a00c00200000600a00000001000400603c00200800000800200000a02000402600000000a00a00e00203400000000201e00001800000000400000001400400e00000c00200200000200000a03002401400800000400000000200404a01601200401601201600c00c01c00000000000200000001e01200001e00000a00601800000000600a01401800803000600401a01001401c00000200800201a00e00000800200000400000000000c00001400400000200e00a00000400400600000400000200400600000000a00000401204600001200801a00400400000000200e00c00c00400601c0020
  | 19 => 0x37d95c04444154241e207a242100000003c23d800f1aa4be8000000000000000000009c45c268731181a0c346ed39003585121a347d800097e0002c382a475671700007181f400036820e51ca0000001cc00002d900013340008343c380000000002ba18144c8000000032cfe04dd44093f89246d13a594e00c60002dc912877841823a22780841fa31a8ad4a9e4354851a9810e261000000039482b247124000025e000000000000047e8c687fe2110a61da90c86b53b100004d012112c98787940004999e391dc08d33c8000caa0000000000000760000000013a00048c01bc3ce8f142f9760e520000000c4400000027c13ed0a41230bd936065820d2181b840702062a321f4aea79309900000007d83e3200c62000033da0180006f13840001062000000015d18a8e21b50628000000000157402c0000f709545b66374178000f8e00046a84045647773be9930ea05a71800654b360001058d9400075b0a81eacf5270003ca11c96c3e51e680000583760000d04cf40bb2850c9800053730789d0430464000198c0002282af04d05d05b1000000000000c019800054047b44f857895845e06486c433213f093a0f4cb453e3f68fb112833b36e880c89800039280000be00000017b00006a536d21d4d1836243300000b68f0000208c76e2bd00020445d65a9491a4f11727ee0640714e2c000402011c88c14b1588200b226a82ed0ee4ac286a28f800075c52d0001e9446c4064538bec0004ba15b0000c360001a996780003c200007c80000000000000a8041217d1cf81c812a48d1f2451e8500b38698d967b747a90b8b1c759096118cbce2b713c971404e4ea2a1800119a4f92281840b3800049e8138ba21af1bf800100e8cc07523d90323670421764aac5f125d9640ffc1981cb0cd0e746420ba0b950c65ba0001cfca0a00000004940005f812f83f07ec0d200892f40009072638fc0c6201d33b0000dc600005b10d8fd25a017a0b4906a2520000000b4a82c320000091a0004561ed51063e02c580005a219d05f16284740004248a28d9a3b824280004427df15c07d4c8a00000017500000001c40fe480e8a800002a80000003d9000000000046c90240002860000968e381c336f86500b05d345d00002043fc2dc09ec6ac5e6165800000000036e000000081b0b180001d6900000093800000000005500000000000000a180000a500000003ce27b99783a800034f067d10a7f847c0ab8e844883ca1b182741dc0970000e14480202925ceec91027094a4e16070419129490672e182826ca826643cf80a0bee2cf000000000065913b21b818c1f634d1eb400000030985fc9840003d40000d90602069a03926e11d29588b8fa600006f233823671214896340004ed0000a0400046f07380012861e6139800065454d0b99d490c43f30d49
  | 20 => 0x8000fe688e30b1a3c96a66c1d88000cc257e0fc980000038041d80009b4325191076c5f078600002cc1b07a300011b4cf8000125a22c75e43314c252800000033904ac0004eb4830000c9c0000000b901e26c549a07000000ff000246510e0001f3800030c0520870000acc52318e9fd822e0290001e04950710319071049262647680005163f149688386625fa28e8e0c9905c30f880002282e029d02f11360c33b200000000001551e88000745000000000000043c21ecc285022bda2c52987e21d99e304de3032d11c04bda7753158e2867e53d22008d427812628400c081401203d9b64b2c64f098a0089985bc1651354fb224f382086cc0e69233e93a0f3c91c00011f400076523aa1fd0e6931136878008c6e74430f147281623c28de400039b0000dbc68c29000010a81cc8611f685e8a440000001f087f00002bc15e84461ea1ad19b80003d62609b1c0006a70001888e3445d2df83b00006d634a000000013617c96740008d31b88cacda855718a9a440002ab00000000004de13f09a8e5847e1010000e545d0041a0c0a928d42b580000c4000000000000084f08d03c854643a19a9ee06a80002c480003420713ed8000486000049175916048204b0ef872624112b85c8f4090817783852425b00001f4472a7c33e284780a88ca38111140006b01178bb896e63d0ff80003d800000014e400000000000010524df0b523a81400000000f684d80e800493891e681528a82b4d7035f39921c0f1a592000000108a2be000065c3ca577269943471e4840221cc45840fb00000000008b848999807865501598a106921aa10a2104cb81b508c1b6c3e000000012a4ec61ac1d1000079e00314c833485805518400005806ae1cd08f000088205719886781bf48900009641753ab9dbcda48d63d09884d126e818f84f885a3a5287116c1e669d470960800079a34f923c00005d0208a682d60002eaa2dc5189163cea4549f8603213a4808680df3b4091468e7b10ac917d1b46f503699c0ade48a0f40314ef80f90a68604d5475c4301f7002e3cb00000000004be00024b0a020ca3779958912665120240400002605c904cce62472530d348c20003f30ea0648000122000078817630ca16d21a93206b97bc000000245995c00018e2d580003b0856000000086e7e5405197400085921016ec41837709c243101662545300008ae17826b000000008600015891b842f482800000000000000000002602a715103c40003d38000000615000000000029b38386f000000046919fcb580002d78000c50805000000033c6740be087c40a4871569eb8aa24e3289243820c87e44c00012601412a580fcff4000000000058e1e427a8c60f8804543b8a38f1e5ad2b8856ca769444a008b49cc4c523c18803160a832fa3081b800027b23f000020400002d51ae
  | 21 => 0x66af3a99b110342f512e0a1c84c77808880005980001b804ed1321482649d351e835845b0000e120000001470c7c706211810c0000002f51c7800022c448045468023d0000338aa60003059fe41c4000000204c00089a0b31fd49c800022b0000bd631c0999b04c2e66900006e899400017f11480000003ac21e40000000169fa00005f21b600000004320370bb09ae00003399341ea92a16214400002c51a886343367794550020b9a6bc43884a090c0e330520a0c7404a45f8fac2a27672b906ec000000000078d29a88416d15a0a0800010b800000000003b0c3459a0002c00a9800000000003dc0000003cc1c4413c1f714017ed13a9260001cf0d083e800008ec32072f31d800115a2c9000000000000000000001228160ef8c7901e3682fc92690b000034d800000047900021ac4e00002e117244b009946f92d05242104719e10eba27d33a9604ca210900799b483221c48d96ccd0c0981e39738ee894b4688430ab04953de223014632712a146847082708f8014d160001978af000000002d000000019c1000000d4000000004f400072b3b69794f364171aa98b80000ac3731ff40001b20a00ca4a6a4811f701802d80002df1a380008e63089df80000bf0000ca025a0000000000de4506350800073e08a000000000037400024f80007832498f1800000040e14800006432328000000000000239c00031b00000000000002128464e325091a78a743ae77f15783042e200000011382be00026180009384423599730ac002221211f0d6436d0002168fae364447800000000000006ac0000000000de8c8e68d000034000016011497ccea88a500013b000000042e00000001882819b08000251173165048c7d21051ab4df08dd3ef1c9d03e83c2cb9bcc9a05cf2f216a000000032206688fe000000107062e5ff4341dec31200041b88583a06680000e2d1822f61ec92840000004548ea4b822c10fa23200001133b58aec8b20001fd000000000039c97b8b065260000a700002883f780000004af22d23190e86fc2a600012740000768000dc892400022b81a893b0c900003b400003a800012e0000002178b941241c10000cce0000000d1000071431a00e40961ed00021d88d022b0dc800066000000000000000000000e9c18e30a0000000abe0000000000a62000000118800000000000803220000000000e9c000158251c8a800031c09e0f6c00021d8000d560000840000f240003450000e4c2a7207212cbae0da25501e90306de1da83442867f729825380d200d43602ac0000770001a611fe0ee47011540001b400009c8d4672324600005be38627988c4000000000000021400000000000003ba0000f54d0a7d000000000002c60000000f7c0003910000000751033117010200044a80002ca0000000000f5e00048200002b800031f
  | 22 => 0x180005680494a4194d0de75a26e1610b464ad19f0f504f48221a422c90428a42999f3000000033f1b0040e0e040ea034fe40240eca14c2f212f18117a435c3ad3df9cd4f0430408e1ee853c0000001db8fd482e3c01ae44600000001b2400000025980000004f2074964c0001a40000dac6f852f0002508ac81d34500ba4b2a0000000000e4284c3d31de8b7a00000002dc484000000000106c0000000ae4f720002b19ff107e00000000011fc0001f500004fe658000000000047203582540001452148000c020944720eed2560fd2920f5d23a0bd0020000c1a00014680008864c000000001b27410000000bbc6d324c907cbc600033b927c0000000000414a7e37e1cf18f0000142000100866c66f1d51e585a62193a609b8c5a76638c2078dc075e1d21698dfa5470d284809b25272fe913ceaa00a1410bf4d263323cb8b5444e1530802048c107e13f617486ae87c43d23e8b187484a09c74b888cf16b1c6c7c681004e19249dc01c35d96604a604005c1a64e9e23f1870f2469490b1e99a5c4340dd00381f86ea3e212ea3011d253226a0b0cb0c0000070000a300002bc81a83e67d53ab0db871c4a22e381648208141e0872065c00000015b8cf000028c96641e01de1fda2d461e7bd00005c03047b400ca51843a6a441c029cf601d21528c5900240b2f02118ab81bd04d23106c208220f18b0ab200038aa24c24459f30905f48882dc09b87f47ea14421f06a096008b000217400000032513108060000000001122000000000000092e39d924400000013e000000088d3cca3ac00000000000000006cc2be9f90216266235800000056723800f4e1e267057884cc5218029a0b20a4282048f0cb453e35c40482380ac66601885a41b676913b80007b80001ac81c8ce245101a93943a26e20158000cd603b2ed80a81e800000000000000610c6000000037837f1f292525e21e915b46706411ad814d110293112869c00000028da4e474c0a107f0050be009036b8fd05c63a30170e045528f20000e44a3c1cc3729a5512c39d1c48d4921e00023d07f05da7242a10ef4272000211043cc1c2852a299a86e66fa0ad10ac32c51700000008dc35e00000004680002240e310aa000058205c00094915217d8000048000030806c73849a8ff42de8082008b5cd9c000375064cdb07714198d14dfe16120025141181552208f7400055a0db225d14665005888a835a4b92fe1b3c14844b3150000000269000000122e00000014f0f82000000000111428300000012061ef344113469c84349b000000058f010a3b11bc000000133cb8c2652330e70bba0001a8249d2448db17800d0f9c5fe29701446f600027885dcdf2000000098925e00000010506121c700001950ce6240000000b9618700000000002333eb000096292828a0000000000426942cae
  | 23 => 0x40600007c274912d88e45c446a27d0068b6425622c04a4f6655526897d400033a00c1fac0001fe0a9082400000023894a00006ee36522ec11e146000219422c21e1251cdc00071f3c48bc852e000000041c0000001ff16dc49a00000080000000001cb8c1c00030c1241010e8021522388900000000dc24fcdaa0000001e903d20000000000000000375808c0004530ae9bd831e0000c18b3812614e00006f84020001a18000fa84a405d1c3000000027fa31c36084224a00005ba0000268cf40160001560000f764760000000ffe3421f91d0c0000000129af923e30b30e0f6c00000007280180000003c5000112465200d8e110da3df2360c18f2010d21e18cc1aa9020c2106cfc023745f1bc0d20683000033caec07f00000005a80002700cdd24a0001b91f3c5f80c00819add1120001d08b60d742f70001594b9069c3a20d8d1780f825
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x28050002e024100780030000a8c0006a6380a12822b1c0181800000005800000022100001002001c0000183587d9050185520048d66064140615480183587190501855200685d91831406154801a146460c50185520041d65c8054c6154801a527060c5018552006945c183140615480105f985cc7359442284a9a468550c62504018547160c70594212441d25d818c165084d90ac9859172d4c2124515259531c5524c0015509054c715493010c56261535c0514c00f4589654d70145300050b255641c9414c00105f985cc73597203cf09994741c552c800105f985cc73d951000568640541c941440015a190d0c72505102641da5b87d942144001265981086508510
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x8546a09054c7154930
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x2
  | 4 => 0x94c
  | 5 => 0x3
  | 6 => 0x5
  | 7 => 0x6
  | 8 => 0x138c
  | 9 => 0x98c
  | 10 => 0x150c
  | 11 => 0xa0c
  | 12 => 0x180c
  | 13 => 0xa4c
  | 14 => 0x198c
  | 15 => 0x209
  | 16 => 0x20c
  | 17 => 0xb09
  | 18 => 0xb0c
  | 19 => 0x1409
  | 20 => 0x140c
  | 21 => 0x1549
  | 22 => 0x154c
  | 23 => 0xb49
  | 24 => 0x1449
  | 25 => 0x289
  | 26 => 0x28c
  | 27 => 0xb89
  | 28 => 0xb8c
  | 29 => 0x1489
  | 30 => 0x148c
  | 31 => 0x1849
  | 32 => 0x184c
  | 33 => 0x2c9
  | 34 => 0x2cc
  | 35 => 0xbc9
  | 36 => 0xbcc
  | 37 => 0x14c9
  | 38 => 0x14cc
  | 39 => 0x19c9
  | 40 => 0x19cc
  | 41 => 0xcc9
  | 42 => 0x15c9
  | 43 => 0x409
  | 44 => 0x40c
  | 45 => 0xd09
  | 46 => 0xd0c
  | 47 => 0x1609
  | 48 => 0x160c
  | 49 => 0x1889
  | 50 => 0x188c
  | 51 => 0x449
  | 52 => 0x44c
  | 53 => 0xd49
  | 54 => 0xd4c
  | 55 => 0x1649
  | 56 => 0x164c
  | 57 => 0x1a09
  | 58 => 0x1a0c
  | 59 => 0xe89
  | 60 => 0x18c9
  | 61 => 0xec9
  | 62 => 0x1a49
  | 63 => 0x749
  | 64 => 0x74c
  | 65 => 0x1049
  | 66 => 0x104c
  | 67 => 0x1949
  | 68 => 0x194c
  | 69 => 0x1a89
  | 70 => 0x1a8c
  | 71 => 0x94b
  | 72 => 0x20e
  | 73 => 0x154e
  | 74 => 0x249
  | 75 => 0x16c9
  | 76 => 0x14a
  | 77 => 0x134a
  | 78 => 0x138b
  | 79 => 0x4c
  | 80 => 0x40a
  | 81 => 0x160a
  | 82 => 0x188a
  | 83 => 0xeca
  | 84 => 0x1a4a
  | 85 => 0x3c9
  | 86 => 0x1709
  | 87 => 0xa0b
  | 88 => 0x8c
  | 89 => 0xe8b
  | 90 => 0x18cb
  | 91 => 0x124c
  | 92 => 0x128c
  | 93 => 0x1789
  | 94 => 0x130c
  | 95 => 0x17c9
  | 96 => 0x134c
  | 97 => 0xb8e
  | 98 => 0x184e
  | 99 => 0x40e
  | 100 => 0x160e
  | 101 => 0x589
  | 102 => 0x180b
  | 103 => 0x140d
  | 104 => 0x10c
  | 105 => 0x5c9
  | 106 => 0x14c
  | 107 => 0x19cb
  | 108 => 0x20d
  | 109 => 0x74b
  | 110 => 0x1a8b
  | 111 => 0x28b
  | 112 => 0x148b
  | 113 => 0x2cb
  | 114 => 0x2d551
  | 115 => 0x1a9951
  | 116 => 0x1a9954
  | 117 => 0x19d4d1
  | 118 => 0x1a1651
  | 119 => 0x1a57d1
  | 120 => 0x1a0d51
  | 121 => 0x40216
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 3060
  | 6 => 8723
  | 5 => 2383
  | 4 => 25
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
  | 7 => packedAt gbK7 (126480+((h/1020+packedAt gbK7 (113220+(h % 1020)*13) 13) % 4444)*13) 13
  | 6 => packedAt gbK6 (462309+((h/2907+packedAt gbK6 (418704+(h % 2907)*15) 15) % 16856)*15) 15
  | 5 => packedAt gbK5 (150125+((h/794+packedAt gbK5 (140597+(h % 794)*12) 12) % 3146)*13) 13
  | 4 => packedAt gbK4 (1798+((h/8+packedAt gbK4 (1750+(h % 8)*6) 6) % 48)*6) 6
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe0f80ffff03fe0fffff80016344fc3e73fc
  | 1 => 0x7807f000f81ffc1ff0f807ffc6bcbb32338ccf
  | 2 => 0x8007ffff001fffffff0007fff8c0c3c3c3ff0f
  | 3 => 0x7ffffffe0001ffffff8003f00fc03fc0ff0
  | 4 => 0x7ffffffffffe0000000003fff0003fff000
  | 5 => 0xfff8000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa872028029272126014934818021005416315c
  | 1 => 0x309650085b09650a90d0552a822c19323284c5
  | 2 => 0x120a5b100128a552a00a25518c0c2c0c15b0a
  | 3 => 0x205395a96404019cca6c0062f00ec03680ea0
  | 4 => 0x2447ce6ce79cf38080c3041837f70003bfe000
  | 5 => 0x4780007004008201080400603ddaf7a8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeeeafae0eac0feeeeeeafae0eac0feeeeeeafae0eac0feeeeeeafae0eac0feeeeeeafae0eac0feeeeeeafae0eac0feeeeeeafae0eac0feeeeeeafae0eac0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37227
namespace PEqualNP.Outside.L_meta_37227
open PEqualNP.Outside.L_meta_37227.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 9 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 4 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
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
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 64 := (concat bs3_4_0 bs3_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 40 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 2 := bs4_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 2 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 6 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 25 := bgb_4_0
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
theorem bgb_5_2368 : Interval gbAtlas 5 2368 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2383 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992))) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)))))) (concat (concat (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)))) (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))) (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760))))) (concat (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)))) (concat (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208))) (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)))))))
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
theorem bgb_6_7808 : Interval gbAtlas 6 7808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7840 : Interval gbAtlas 6 7840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7872 : Interval gbAtlas 6 7872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7904 : Interval gbAtlas 6 7904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7936 : Interval gbAtlas 6 7936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7968 : Interval gbAtlas 6 7968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8000 : Interval gbAtlas 6 8000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8032 : Interval gbAtlas 6 8032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8064 : Interval gbAtlas 6 8064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8096 : Interval gbAtlas 6 8096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8128 : Interval gbAtlas 6 8128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8160 : Interval gbAtlas 6 8160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8192 : Interval gbAtlas 6 8192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8224 : Interval gbAtlas 6 8224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8256 : Interval gbAtlas 6 8256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8288 : Interval gbAtlas 6 8288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8320 : Interval gbAtlas 6 8320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8352 : Interval gbAtlas 6 8352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8384 : Interval gbAtlas 6 8384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8416 : Interval gbAtlas 6 8416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8448 : Interval gbAtlas 6 8448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8480 : Interval gbAtlas 6 8480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8512 : Interval gbAtlas 6 8512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8544 : Interval gbAtlas 6 8544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8576 : Interval gbAtlas 6 8576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8608 : Interval gbAtlas 6 8608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8640 : Interval gbAtlas 6 8640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8672 : Interval gbAtlas 6 8672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8704 : Interval gbAtlas 6 8704 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 8723 := (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))) (concat (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896)) (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)))))) (concat (concat (concat (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312))) (concat (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))))) (concat (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856))) (concat (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984)) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))))))) (concat (concat (concat (concat (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400))) (concat (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688))))) (concat (concat (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944))) (concat (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 bgb_6_3072)) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232)))))) (concat (concat (concat (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360)) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488))) (concat (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616)) (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776))))) (concat (concat (concat (concat bgb_6_3808 bgb_6_3840) (concat bgb_6_3872 bgb_6_3904)) (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 bgb_6_4032))) (concat (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 bgb_6_4160)) (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320)))))))) (concat (concat (concat (concat (concat (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 bgb_6_4448)) (concat (concat bgb_6_4480 bgb_6_4512) (concat bgb_6_4544 bgb_6_4576))) (concat (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 bgb_6_4704)) (concat (concat bgb_6_4736 bgb_6_4768) (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864))))) (concat (concat (concat (concat bgb_6_4896 bgb_6_4928) (concat bgb_6_4960 bgb_6_4992)) (concat (concat bgb_6_5024 bgb_6_5056) (concat bgb_6_5088 bgb_6_5120))) (concat (concat (concat bgb_6_5152 bgb_6_5184) (concat bgb_6_5216 bgb_6_5248)) (concat (concat bgb_6_5280 bgb_6_5312) (concat bgb_6_5344 (concat bgb_6_5376 bgb_6_5408)))))) (concat (concat (concat (concat (concat bgb_6_5440 bgb_6_5472) (concat bgb_6_5504 bgb_6_5536)) (concat (concat bgb_6_5568 bgb_6_5600) (concat bgb_6_5632 bgb_6_5664))) (concat (concat (concat bgb_6_5696 bgb_6_5728) (concat bgb_6_5760 bgb_6_5792)) (concat (concat bgb_6_5824 bgb_6_5856) (concat bgb_6_5888 (concat bgb_6_5920 bgb_6_5952))))) (concat (concat (concat (concat bgb_6_5984 bgb_6_6016) (concat bgb_6_6048 bgb_6_6080)) (concat (concat bgb_6_6112 bgb_6_6144) (concat bgb_6_6176 bgb_6_6208))) (concat (concat (concat bgb_6_6240 bgb_6_6272) (concat bgb_6_6304 bgb_6_6336)) (concat (concat bgb_6_6368 bgb_6_6400) (concat bgb_6_6432 (concat bgb_6_6464 bgb_6_6496))))))) (concat (concat (concat (concat (concat (concat bgb_6_6528 bgb_6_6560) (concat bgb_6_6592 bgb_6_6624)) (concat (concat bgb_6_6656 bgb_6_6688) (concat bgb_6_6720 bgb_6_6752))) (concat (concat (concat bgb_6_6784 bgb_6_6816) (concat bgb_6_6848 bgb_6_6880)) (concat (concat bgb_6_6912 bgb_6_6944) (concat bgb_6_6976 (concat bgb_6_7008 bgb_6_7040))))) (concat (concat (concat (concat bgb_6_7072 bgb_6_7104) (concat bgb_6_7136 bgb_6_7168)) (concat (concat bgb_6_7200 bgb_6_7232) (concat bgb_6_7264 bgb_6_7296))) (concat (concat (concat bgb_6_7328 bgb_6_7360) (concat bgb_6_7392 bgb_6_7424)) (concat (concat bgb_6_7456 bgb_6_7488) (concat bgb_6_7520 (concat bgb_6_7552 bgb_6_7584)))))) (concat (concat (concat (concat (concat bgb_6_7616 bgb_6_7648) (concat bgb_6_7680 bgb_6_7712)) (concat (concat bgb_6_7744 bgb_6_7776) (concat bgb_6_7808 bgb_6_7840))) (concat (concat (concat bgb_6_7872 bgb_6_7904) (concat bgb_6_7936 bgb_6_7968)) (concat (concat bgb_6_8000 bgb_6_8032) (concat bgb_6_8064 (concat bgb_6_8096 bgb_6_8128))))) (concat (concat (concat (concat bgb_6_8160 bgb_6_8192) (concat bgb_6_8224 bgb_6_8256)) (concat (concat bgb_6_8288 bgb_6_8320) (concat bgb_6_8352 (concat bgb_6_8384 bgb_6_8416)))) (concat (concat (concat bgb_6_8448 bgb_6_8480) (concat bgb_6_8512 bgb_6_8544)) (concat (concat bgb_6_8576 bgb_6_8608) (concat bgb_6_8640 (concat bgb_6_8672 bgb_6_8704)))))))))
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
theorem bgb_7_2304 : Interval gbAtlas 7 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2336 : Interval gbAtlas 7 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2368 : Interval gbAtlas 7 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2400 : Interval gbAtlas 7 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2432 : Interval gbAtlas 7 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2464 : Interval gbAtlas 7 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2496 : Interval gbAtlas 7 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2528 : Interval gbAtlas 7 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2560 : Interval gbAtlas 7 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2592 : Interval gbAtlas 7 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2624 : Interval gbAtlas 7 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2656 : Interval gbAtlas 7 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2688 : Interval gbAtlas 7 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2720 : Interval gbAtlas 7 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2752 : Interval gbAtlas 7 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2784 : Interval gbAtlas 7 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2816 : Interval gbAtlas 7 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2848 : Interval gbAtlas 7 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2880 : Interval gbAtlas 7 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2912 : Interval gbAtlas 7 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2944 : Interval gbAtlas 7 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2976 : Interval gbAtlas 7 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3008 : Interval gbAtlas 7 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3040 : Interval gbAtlas 7 3040 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 3060 := (concat (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat bgb_7_672 (concat bgb_7_704 bgb_7_736))))) (concat (concat (concat (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928))) (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))) (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)))))) (concat (concat (concat (concat (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600)) (concat bgb_7_1632 (concat bgb_7_1664 bgb_7_1696))) (concat (concat bgb_7_1728 (concat bgb_7_1760 bgb_7_1792)) (concat bgb_7_1824 (concat bgb_7_1856 bgb_7_1888)))) (concat (concat (concat bgb_7_1920 (concat bgb_7_1952 bgb_7_1984)) (concat bgb_7_2016 (concat bgb_7_2048 bgb_7_2080))) (concat (concat bgb_7_2112 (concat bgb_7_2144 bgb_7_2176)) (concat bgb_7_2208 (concat bgb_7_2240 bgb_7_2272))))) (concat (concat (concat (concat bgb_7_2304 (concat bgb_7_2336 bgb_7_2368)) (concat bgb_7_2400 (concat bgb_7_2432 bgb_7_2464))) (concat (concat bgb_7_2496 (concat bgb_7_2528 bgb_7_2560)) (concat bgb_7_2592 (concat bgb_7_2624 bgb_7_2656)))) (concat (concat (concat bgb_7_2688 (concat bgb_7_2720 bgb_7_2752)) (concat bgb_7_2784 (concat bgb_7_2816 bgb_7_2848))) (concat (concat bgb_7_2880 (concat bgb_7_2912 bgb_7_2944)) (concat bgb_7_2976 (concat bgb_7_3008 bgb_7_3040)))))))
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
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 40, 42),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 34, 50),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeeeafae0eac0feeeeeeafae0eac0feeeeeeafae0eac0feeeeeeafae0eac0feeeeeeafae0eac0feeeeeeafae0eac0feeeeeeafae0eac0feeeeeeafae0eac0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071594 * 2 ^ 32 + 4209044160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37227.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.or,[3,5]⟩,⟨.and,[5,6]⟩,⟨.or,[0,3]⟩,⟨.and,[4,9]⟩,⟨.or,[1,10]⟩,⟨.and,[1,8]⟩,⟨.or,[0,12]⟩,⟨.and,[7,13]⟩,⟨.and,[2,11]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4209044160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4209044160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37227

open PEqualNP.Outside.L_meta_37227 in
theorem PEqualNP.Outside.L_meta_37227 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4209044160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4209044160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
