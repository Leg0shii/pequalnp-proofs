import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37347.Model
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


end PEqualNP.Outside.L_meta_37347.Model

namespace PEqualNP.Outside.L_meta_37347
open PEqualNP.Outside.L_meta_37347.Model
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

def SBf (j : Nat) : Nat := [5, 5, 7, 8, 6, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37347

namespace PEqualNP.Outside.L_meta_37347
open PEqualNP.Outside.L_meta_37347.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 2 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 3 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xc22231451041240529272126048a690c26315c
  | 2 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 3 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 4 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37347
namespace PEqualNP.Outside.L_meta_37347
open PEqualNP.Outside.L_meta_37347.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfc07ffc07ffc0783fffffc0ffe07ff007f9e7c
  | 2 => 0xfff81ffffffffffc0fc07ff03fffffff98e3ff
  | 3 => 0xffffffff81fffffff0007ffffff81fffe0ff8f
  | 4 => 0x1ffffe0007ffffff80003fffe001ff03f0
  | 5 => 0xffffe000000007ffffffffffc0000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2530c4471448a980b2ca9c854e43390c2b8e3c
  | 2 => 0x88524c892091831405582594128e525498a0d5
  | 3 => 0x30a111120d2224a950224a29a5510ca960570a
  | 4 => 0xa2c59a24483b36ce69b3030939e58831f503e0
  | 5 => 0xc3061c3871c3c7738e3c73ce018610c1def800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000faaafa00f0a0f000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37347
namespace PEqualNP.Outside.L_meta_37347
open PEqualNP.Outside.L_meta_37347.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2a4c540220038d052e64200003d1804a903002c7c01d4e010005a000105245614002469b0000180000009e00005080e00c00160099204ace28188404180080040112200010200683ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20ee20fd20fc20ec20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x30001834009e8a8c00bc602876ae0056783a58006c002068b62e00ba047a029046a0368822743800529c24000e5c721e00aa065a266e7e007008bea6a29a320098004a926a2a842c000010009414a8001a5e4400b4121c00000a86b266acc07c9664503ec282428e4e3c40b0000c4cb8804854a462c416021018ba00001e00043020020181040828106000000a0000a064c30a016e5290edaa521de94243bca84876e5210edaa421ded4142bc282856d538cadca11973d4d32b6282656e520cabea6a0d714d41b7a92836c52506f6a0a0de14141b7290836d52106dca598db54b31e6994633e540c67aa818db94831b6a9063cd320c6f4a018de54031af29e435d53c867ca810cf55021b7296816d52d035c65206b4ca409f284816f52502d8a4a06b8c840d6990813e5010374a0204f953309eaa6616e52cc2daa598734cb30dc204613f544c278a8985bd4930b629261cd324c2eea2985d14530dc202616e520c2daa4184f953209eaa641b840c82dea7105b54e20b728441ae408835881104fd51209e2a2415e53082baa6106e10020b7a9841ce53082daa6107354c20a6a98416e50083d4a0107ad0020d720041ac40083d080106a100209f2a6213d54c42dca5885b54b10dc206213f5444278a88857d4d10ae29a216f52442d8a4886e10010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x701000e0450131003513002c308920001200f5062800882302b4932540318e18154086a8604c840d14c8514c3285210130e24c8404c3305110130c654c400824d6594c20d254f400830d5390020aa982400830d5310020d254c400832b5310020e294c40083295310020e254c400830953100209358e52c432a5210310
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x801070132144404c284baca620041425ce5210310
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s2K5 (841+((h/15+packedAt s2K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s2K4 (2904+((h/33+packedAt s2K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s2K3 (833+((h/7+packedAt s2K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s2K2 (150+((h/1+packedAt s2K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffff01fc0ff83ff83ffffff03c07ccffe67
  | 1 => 0x1f80fffffffffffc0ffc1f81ffffffff311fff
  | 3 => 0x1fff03ffe000fffff0001ffe1ffc007fc1e387
  | 4 => 0xe00003ffffff03ffffffe0001fffff83fe03f8
  | 5 => 0xfffffc00000003ffffffffffe0000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc48a2811c4852880b380a58a2b224524466e63
  | 1 => 0x412611224910411404a40aa1454493491114ad
  | 3 => 0x96145b4483b693ad5062936d16ea0a73c1a386
  | 4 => 0x1458a28912241aca694ac04818b32c22ea0350
  | 5 => 0x1860c30e1c38e3738e731c7180c03043bdd800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeaa88cccc8800eeeeaa88cccc8800eeeeaa88cccc8800eeeeaa88cccc8800eeeeaa88cccc8800eeeeaa88cccc8800eeeeaa88cccc8800eeeeaa88cccc8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37347
namespace PEqualNP.Outside.L_meta_37347
open PEqualNP.Outside.L_meta_37347.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81bf439037a87205f94a40bea9481be429037885205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a05f14d40bfa9281ef52502dea4a05f14940f6292816c52502fea2a05f14540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf29661ee52cc2dca5985f54b30f6a96616d52cc2fca3985f54730fda0661f840cc2fea9185f95230beaa4617c548c2faa7185f94a30f7294616e528c2faa5187b54a30b6a94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c2fea2985f14530fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea90617e510c2faa218778c430ee188617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bd0a20f621441ee32883da65105f94620bea8c41ee21883d843105f94220fd98441f830883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42483de64907b0c920bfa8a417c51483de42907b48520fd98241f830483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef42083d884107b8c820f6990417e51082faa2107b88420f6108417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd98621f830c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fda0421f840843f461087e4c210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fda0221f840443f460887e4c110fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xd51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1197e94232bd284657d508cbf2a1195e54232bfaa2657e544cafaa8995f15132f721265ed424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d06fca1a0df54341beaa4837e53906faa720ef90e41de21c837e52907dca520db94a41bea9483ed52906daa520efd0a41dea14837e519077e8320fdd0641bf28483fa50906f4a120df54241fca84837950906fea6a0df14d41dfa1a83bd43506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498fbd4931b7a92637c524c7d8a498db14931fb98a63de314c6fea098fed4131bda82637c504c7f0a098de14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf298637e520c7dca418db94831bea9063ed520c6daa418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21f7a1643ec42c87dc6590fb4cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f7a1243ec42487dc6490fb4c921fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010fe94021bd28
  | 2 => 0x2c80000a00010891c080e5398001291090be15d260001367a8059f10321c50f10b1549c1338a2128000de8003321a0e193f10e5e07726a16c2b9210c8230038c88312d09e8430e01046f0be0f44745a81b22f4aa000000002ca4f8fb0561585980019814ca053c80007e0007c2393928747f2070001f016a783c8a39308424a24bce00002c27e0c301f44c0481a0c44dc6acc6000014710000000009880000001a0f86b0110000000015f3405c0f011e0c844cee0004b208c00000000000ce8a9000094108480a49788a81e3cc000000590000004080011e24c00000092704c52970001a8000002b60010000050e9c400204000000000000000000000049a688ae9f20000000022434e144f59c8000000000000000000023f4800cc900af000000d785509a0000011b000000d49ad000001270a4000000001803667ec971a441831c9407b0c68dd298a10f40000000046000000000224431358003043049ca3b19e014000ab43e45037a49000000db9bb1660004600024c314c1a2c2b4838c818128ea502c1dd2a6940bd92b138414e5a3316e5b0001b62ce2b4a88f50c42202805c48a0a8f7054096668e8949000000419922149c8bd0f30e6340faa14056860f80d413c385139be2420005818504e7643b000000000000000008ad3d9322da5080018b000000469ef24e9a5450000000009c06b3360ed3e0ca1ba000bf80000032c00000000000a3000000000989f41a6000fc8000001740d95c080000a5800000494000003c248c000070041705804004000100600006004020000205800000010040a0000100402000120000c02c1500011024000040e010000040100c0000400018120000002400020000000001805000020040900800008090040000002004000000c00000000000280800003000010000b04c000041100c02004050000000c020100000400000020440702401008030900100400000000000202007048020140c0080200c000040204c0e004040040100c10000000040d000000000000000000040181d040000280700c0301007014000180d0002e0000001c0500807020010040604c04004020040300c0600403048000000704401000000000a000000c401008010081500c01000010000000c0002c030100101c0f0000000000bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857
  | 3 => 0x4a4f487e16a00148a2e17e95800000000000000003680011b0000b625896800000828000000000001e2060000010c9b11803689e9db11400081a6d50619d0889d02e1940098e00c3c1220690042e817216266070140000b410400000000058001ed0008f13a13c2e20000013a46800087000000000001521241392790d00084c8e1c548641c9b0000004084f9e50fa2607923807a0980c1a33ee760b99ba2766a0f19b240239925a890da8c4661874cc97d440612dc7f0000003f40012b974000000001004202c8000000005780e8000003086a9943be11cbea1a2ee390b122500004c0007042a2e452a2112247c3013050c54119043454a30ac1552ec0013e906000758002122ac3e904000000000000771fe198000f11002e0e81225201e000220000000649c7234000120460000006ba3d000000ea800000214b78000001fc6e228000000002640005a41a80022c4900000050a0c000000000000739b5000000001342540000000045a994d3254000520c980000055c001440000008200031a000d514a094000880a852c9cc6f10802a3e41b8321d285ca0a3e38c3f4000001ec6b0c48bd0ea6c00000031e65c0006e2864650e0e83ce709231b82d69754a9a50e847400000000264000000006e4e9a760405814028429e000a626c00067c0000000000027a0d4ee55068a0200000000203000980000002f20013a98446a7a0000000003b0000003382240010f000024000db2020014900012a000f113512e5352d2934520e92c0003b4000670001b273c000bc4d00000604551a000000002b29047185e1f630ca701a39422d24196000500000720520014580035c3a8002050000000000f1341b0539bf0007f4001ff2fc00c7688e4dea3d0480018c000588e21ee778501ec4940013f25c4362ed3180032a000b90000000b0001d70000bcf98073a47393f9171d6000000000003bc001d40000000013741600096223222000000080002402600007200000000444001078b41f858c6682200037c5f1fe4b60003c9750000006904400828d4100028a6840000039a6202983833c0006c00
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x9544c26c62551309dd85544c27461551309ed81544c26e62151309b588544c26e62145309b588514c26f62550309b189540c26e62150309b588540c27661150309d584540c23e6494c308f592530c23f64544308f191510c26f62544309b189510c2796510030b658c400c2e96210030ba58a300c25f654c0309ed95300c25e63153209758c54c823e6414f208f59053c82e86050b20ab59032c82ad64c8720ba58840c83aa42103208f992538823d6494e20ba582328823f64546208f19151882e96008620ba98b308823e64951209bd89544827b60551208f994544832d62151208f992534823d6494d209b58a534823f6454d208f19153482776154d209d185534826e6590920cb152424826c6550920cb15142482e860509209b997324832c54cc9209b99432482ad640c920cb150324826e65c8520ab593214832c54c8520cb151214827a65cc120ce1533048338540c120ce153204832c54881209d987540827561d50209b988540826e62d4c209e983530823e6414c208f59053082766114c209d584530826d65d08209b594420826d658c820ba582320826f654c8209b59621082e960084209e59440083a842100209bd9520082ac64480209ed9520082b864480209b98b54c426d62d53109b98a54c426d62953109bd8953c426c6254f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b109bd89548426c62552109b988548426d62152108f993538423d64d4e109b98b538426d62d4e108f992538423d6494e109b98a538426d6294e108f990528423d6414a10ba58840842e9628c210ae191208433960d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534427b6054d1097994534431f5414d10c715053443596014d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524427a65d0110d614f404436852d0110ced5040443585310110ba588404436852101109e9963044358538c110ba58a3044278654c110d614d30443585388110da14a20442786548110ae19120443585348110d614f104426e62d50109b58b540427a60d50109798c540425d63150109b988540426d62150109b98b530426d62d4c108f990530423d6414c109b988530426d6214c109e980530426d65948109b988520427a60148109e597300436952cc0109e5943004369520c0109e596100436952840109dd95100427b6544010b618d10043695244010
  | 1 => 0x6786054c418f59643106ad6210c41ae18142106ad62d04418fd95411067765504419bd89501066c62540419bd8954cc66c62553319ed8154cc67860553319b98854cc66d62153319e98252cc6796094b319b98a50cc66d62943319b98b548c66d62d52319e983548c67960d52319b98a548c66d62952318f992528c63d6494a318fd91508c63c64542319bd89508c66c62542318f992544c66e62951319b58a544c67a60951319e582544c66f62551319b189544c67761551319ed81544c67860551318f994544c72f54d4931cb153524c72f5414931cb150524c73454cc531ced53504c73854d4131dad4b504c76852d4131ced50504c7385414131dad48504c7685214131d68c4504c66e62d50319b58b540c67a60d50319e583540c63d6595031cd185540c63e64150319b988540c66d62150319e980540c6796015031cb952520c72d5494831cb951520c72d5454831cd553410c675651043197d95310c6d8604c4319dd95310c6b4644c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c76952540319ed8154c86786055321cb18954c873b6055321ce18154c863e64d4f218f59353c867a60d4f219e58353c863e6414f218f59053c872d54d0b21cb55042c872d548cb21ba58232c872d544cb219e983548867960d52219ed8153886786054e218f990538863d6414e219e98053886796014e21ba18142886ad640ca21ab593218866d629512197d8d544865c63551219ed81544867860551218fd91534863c6454d219bd89534867b6054d219e181534863e6414d218f590534866e65d09219b994424866e658c921ba582324866c654c9219b98b540867a60d50219e583540865e63150219758c540867a60150219e580540867a60d4c219e583530863e6414c218f590530866e6214c219e98053086796014c218f992520863d64948219b596420866f6550821ba181420866d65cc8219b59432086ad640c821ab593210866f65484219dd95210863f64540218f191500873b6454021ce191500876a4254021da509500876b3254021da0c9500876b2154021da485500866f6254f409b18953d026e62947409b58a51d026e6294e409b58a53902ac6250e40ad185439026f62546409b18951902ae6290640da14b405032c5290140ab18943102b46150c40aed81431032f4354840cb50d52103686054840cb54a42102ae6290440cb54a41102b96090440cb548411033551104408fd9540102ac62500409ed9540102e862500409b98b54cc26d62d5330ced8154cc26e62153309b58854cc32e5494b30cb55252cc3696094b30cb95152cc32d5454b30da94b40cc3395410330ba58840cc36a52103309b98b548c26d62d52309d987548c27561d52309b988548c26d6215230b6580318c36952cc2309bd8
  | 2 => 0x33424904e97b02a40cc61d140a5dcf18d817a5c4391a03aa0e4211892a8000ab1c22d86b0e29f72580903da081343a4080d9216070720db25645c1504900004c108bc0007c0f50744265ac000000d675c0000034452c000df1723ec8404f2a2300001393d62b8139aa0003880013330e4188113531e7980017d35a0cc740bf3745a40013e0900988e9153a42607b8b70003547a19e2f408c511af41a0010d1f6166000001c307e1800000006a440001cd00280c0003a33000000132000000e58c816a6582600000076c2c08624257015a060d83f49d0562920002816d000000000000002c041a0e3ce564461453f20000a0b80004bcbc0003688544e1fc22c000b190f3de540eb00021c1d4168dc1ea554801603d20001414d000000002173100040400c050000301000008020301105001030050e8020000b004000000203c1700000008070000b0180103420080040000104c0a014060040a0700000c15020110780a008080040a070030080300407220020a40100c0f0240c01c03058001100600c0703c2100c080001900000008150102100802018140580501000024080082f0180a00000000060040000004018020200100002020040001101c4e11006024030001300c000401a00c720000500c1b0001200801080020480001c030080108c17004000001700c0b0441a03802000020041700000040000080200c0001e6e62947439b58a51d0e7a60947439e58251d0e6f62543439b18950d0e6f62546439b1895190e6e62942439b58a5090f6752d4543d914b5150f675214543d91485150f364314543dad4b5050f6852d4143dcd475050f7051d4143dad485050f685214143dcd445050f7051141438fd954310eb46150c4397d954310f2f4354843cb50d5210e7b6054f429e18153d0aac6250f42ad18543d0a7a60947429e58251d0ab46150d42ced0c5050b394314142dad085050b3a42141428fd954210ab860508429bd954210ae860508429e98354cca7960d53328fd9151cca3c64547329d987548ca7561d52329e983548ca7960d52329e980548ca796015232ba181428ca3f64542328f191508cb3b6454232ce191508cb6a4254232da509508cb6b32542329bd89544ca7761551329d185544ca7b60551329e181544ca6e65909329b195424cae860509329e980514ca7960145328f596540ca7b60550329e181540cb2c6255032ced81540cb3860550328f990540ca6e62150329b597420cb2d54d08329b594420cb2d5410832cb552320cae9608c83297d95320ca6f654c832cb551320cab46150f41cbd0d52d072d4354b41ab588439072e52d0a41ae18142906ad62d0641da94a50907695294241da949509076952542419b988535066d6214d418f99743506b46150d419b988505066d62141419bd89531066c6254c419ed81531
  | 3 => 0x21b90003688493021403c00000000508b91ee3c481c17097232178ee18a18a2907e2040c4318699820f42c4718c92b6008000003f64a4f200b0002a0a41b0278780e39a5224000000ac0000b0930a33a651c22000000864420192ba1a87d0382b43780002f000470000002b00006800000017c000001ce174b217f14a3802a2113b4344e51fd39c4a87515f1f06acdf936164600669223920c0ef05c1220d8ec18d16c1c4f2800168114ef800000255060c70fa00000197294304808ce302028b095e2e06f05d21236a000971232ec358001f5388774001ed0000dc00166000000a91b210a1dc370f936e15cbf07901c7b0869cf08c374d301f036668d18681da8003f88b0802403f0002340002a8940000009880026e5cc620000007cc3b0f60000747f19300041c8a0aa286000c21530826f8d99b803c000001c100000c348000005e4a00ef24a3086505a00033c000a92ae000e60000002ac0007000000000000230000729342980000004b02211c0006d36c3fcb703c1e40003e08f3e83490488809c2348f19b316690b500c2de650ff8633520809000015e0d0a31ae2221cca78003e424c2886600046ccf9b12ea6544c9281dc718a084329c1341118330c7841e8e60524ec040810620ec7617c23e648e00be25a6ec618a11e2330b3a161ae750938f310e5d0ce90c0b2208cca0f0a4128d38531001bc0b03e0c2644470d44282484f1900301e0128ad00a6a08213d37a258658892ca828321fa3e25a0f41d031c8604d9384040343381a1d627d008320ca228780bb390614fc01200c7f8708a700001c048a64202810585b27e414ec99c2c45100b91
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xd3801523c00565c000b0020000064400c00150003130181091c80102805008c00000000f491c54354843a60e2a18a0a162862181540ca94382a8210658a551608c832a48e2a1aa5a0e286218154c8694382a8216438a551608cb21a52e8192a010d2974c85500869238a86a90814a1d16094b308d2ed2908198628541814248216bb0a8192410b5d854c8520950e8b0464104a87458021082943a2c0292219214d62101108d2ec29080886485358a304430c320a6902219218d5244010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x101a082887551608c83282887551608cb21828865d03254021828865d32154021
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (20138+((h/221+packedAt s3K5 (17928+(h % 221)*10) 10) % 963)*11) 11
  | 4 => packedAt s3K4 (22272+((h/179+packedAt s3K4 (20482+(h % 179)*10) 10) % 647)*11) 11
  | 3 => packedAt s3K3 (1273+((h/8+packedAt s3K3 (1225+(h % 8)*6) 6) % 40)*6) 6
  | 2 => packedAt s3K2 (243+((h/1+packedAt s3K2 (240+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffe07ff80fff8383ff87ff03ff07fe019f1e7c
  | 1 => 0x3fffffff03ffffc0ff83ffffff81ffe63ff8f
  | 2 => 0x3ff81ffffc003fff0003ffc1fffe00383e3f0
  | 4 => 0xfc0001ffffffffffffffc0001ffffffffc03ff
  | 5 => 0xfffffe00000003ffffffffffe0000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x182b1488e2891580b3824b52ab22aa288f0e3c
  | 1 => 0x484108112192109404881514c5288c98217685
  | 2 => 0xb2862da245075bad504626da96b6c85383a3d0
  | 4 => 0x221451448824424a6954808018c5116354016a
  | 5 => 0xc31861870e3863738e6738e300860183fad800
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeec8c8ecec0000eeeec8c8ecec0000eeeec8c8ecec0000eeeec8c8ecec0000eeeec8c8ecec0000eeeec8c8ecec0000eeeec8c8ecec0000eeeec8c8ecec0000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37347
namespace PEqualNP.Outside.L_meta_37347
open PEqualNP.Outside.L_meta_37347.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x80fa20f920
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
  | 4 => packedAt s4K4 (34+((h/1+packedAt s4K4 (32+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe07ffc07f03fe0f83fffe07ff07c07d3f1e67
  | 1 => 0x3fffffff8003fff003f07ffffff8007e23ff87
  | 2 => 0x3ff80ffffffc0ffffc007ff81fffff83c3e3f8
  | 3 => 0xc0000fffffffffffffff80001ffffffffc03ff
  | 5 => 0xfffff00000000fffffffffffe0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x82b0a4471254a603a0b496a2ab2545150f0e63
  | 1 => 0xa45148890e994a7041582b2cd5a90a5a217785
  | 2 => 0x822651224506694a4044cb28635931143a2a8
  | 3 => 0x21458a24488209294a69010418c22c62b40156
  | 5 => 0x31860c3870e38dce738e71c700843043fad800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfac8fac8f800f800fac8fac8f800f800fac8fac8f800f800fac8fac8f800f800fac8fac8f800f800fac8fac8f800f800fac8fac8f800f800fac8fac8f800f800, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37347
namespace PEqualNP.Outside.L_meta_37347
open PEqualNP.Outside.L_meta_37347.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x94e000062cfd8000000000000001700b400076040000888000000000000f560000017290000000002d1b80000014063d9000e65880008400054000003a449af3e4828c1a90000300080000992b75055e203cf9d0000d40330001b005600d9a0001a1c1c00539042000002002c000020c282002c00200000030200183b7a92876c5250eeea2a1dd14543bda8287785050ef4a021de54043af29e855d53d0af4a1a15e54342bb28c85755190af4a1215e54242bda826578504ca7ca8194f55032bb2886575510caf4a0195e54032bda82837850506bca620d754c41b7290836d52106f4a020de540419f2a6633d54cc6f4a198de54331b7294636d528c6f4a118de542319faa2433c54486bea690d714d21bda82437850486f4a010de54021bba8a817451502bca6205754c40b7a92616c524c27ca8184f55030afa9a415c53482eca2105d544209faa2213c54442dca4085b54810
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
  | 4 => packedAt s5K4 (1875+((h/21+packedAt s5K4 (1728+(h % 21)*7) 7) % 122)*7) 7
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ff83e07f07f0f87c3e1ff80f87c07e49f267
  | 1 => 0xf83fffff8007ff007fffe0fffff8007c7e3f87
  | 2 => 0xffc003fffff83fff803fff000fffff838fc3f8
  | 3 => 0x3ffffffffffffc000000ffffffff003ff
  | 4 => 0xfffffc0000003ffffffffffff0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xb285562712aab03c2e1695a925a5455648f263
  | 1 => 0x518a10410e311300144aa430eaa90a181a1785
  | 2 => 0x2113188a24219548802cc622433193108f42a8
  | 3 => 0x462c631448842a955a8010848c462c63700156
  | 4 => 0x8430421870c62ce6633118c700043043e5a800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfcecf800fcecf800fcecf800fcecf800fcecf800fcecf800fcecf800fcecf800fcecf800fcecf800fcecf800fcecf800fcecf800fcecf800fcecf800fcecf800, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37347
namespace PEqualNP.Outside.L_meta_37347
open PEqualNP.Outside.L_meta_37347.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5001fe54007f55007fc54017fd4c05fe53017f54c05fc53017fd0c05fe43017f50c05fc4301ffd4803fe52007f54803fc52007fd0803fe42007f50803fc42017fcc803fe32017f4c803fc3201ffd4401fe51007f54407fc51007fd0401fe41007f50401fc41017fcc405fe31017f4c405fc3100ffc8401fe21007f48403fc2101ffd4001fe50007f54007fc50007fd0001fe40007f50001fc40017fcc005fe30017f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42000ff50210007f28108013fc4084013ff9842004ff8c21004ffa6108013fc308401fff9042004ff88210007f44108003fd2084001fc9042004ff08210007fe2108003f71084001fd8842000ffd9510005feca880037f65440013fb2a200eff9951001dfcca88003fd65440017eb2a200eff1951001df8ca880037c65440073e32a2000ffd9110005fec888003bf64440015fb222000ff9911005dfcc888003fd64440017eb222000ff1911005df8c888003bc64440015e322200effd5110007fca888003fd544401dfe2a2200dffd8d1006dfec688037fe63440057f31a200dff58d1006dfac688037fc63440057e31a200dffd4d1006ffca688037fd534401bfe29a200dffd0d1006ffc8688037fd434401bfe21a2000ffd8910005fec488033fe62440037f3122000ff58910005fac488033fc62440037e312200effd4910067fca488003fd5244019fe2922000ffd0910067fc8488003fd4244019fe212200dffcc910067fc6488037fd3244019fe192200effd4510007fca288003fd514401dfe28a2000ffd0510007fc8288003fd4144001fe20a200dffcc51006ffc6288037fd314401bfe18a200cffc8510007fc4288003fd2144019fe10a200effd4110007fca088003fd504401dfe2822000ffd0110007fc8088003fa4044001fea022000fe50110007f88088037ff304401bff182200dff4c11006ff86088033ff2044001ff1022000fe88110007fa4088003f92044019fe1022000ffc4110007f62088003fe1044001fb0822004ffd9410005feca08023fe65040077f3282000ff59410005faca08013fc65040077e3282004ffd9010005fec808003fe64040177f3202000ff59010005fac808013fc64040177e3202008ffd5010007fca808003fd5404011fe2a02004ffd8c1003dfec60801ffe63040057f3182007ff58c1003dfac608013fc63040057e3182007ffd4c1003ffca60801ffd530400ffe2982007ffd0c1003ffc860801ffd430400ffe2182004ffd8810005fec40801bfe62040037f3102000fb9881000ddcc408003fd62040017eb102000fb58810005dac408013fc62040037e3102008ffd4810037fca408003fd520400dfe2902000ffd0810037fc8408003fd420400dfe2102007ffcc810037fc640801ffd320400dfe190200abf98410047fea208017fe5104001fea882005ff14410007fe8208017fe4104001fea082005ff1041003ffe6208017fe310400ffe9882005ff0c410037fe4208017fe2104001fe9082005ff0841004dfcc008023ff5004009ff2802000ff54010027f8a008003ff4004009ff2002000ff50010027f8800801fff3004009ff1802007ff4c010027f8600801bff2004009ff1002000ff48010027f84008017ff1004001fb8802004ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0x7fc4248003ff9924001ff8c92000ffa6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf185200a7fea290003fe5148001fea8a4014ff14520007fe8290003fe4148001fea0a4000ff1052009ffe629004ffe3148027fe98a4013ff0c52000ffe4290007ef2148003ff10a4001ff48520007da4290007fc21480037fb024014ffd4120007fca090003fd5048029fe2824000ffd0120007f68090003fe4048001fea024000ff10120007f0809004fff3048027ff1824013fe8c12009ffa609004ff93048027fe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f8204800bffb2e2000bfd9710097fccb8800efe65c4001feb2e2000bf5971002ff8cb8800efc65c400bffb262000bfd9310007fcc98802efe64c4001feb262000bf5931002ff8c98802efc64c4025ffaa62000ff95310007faa98804bfc54c400bffb1e200abfd8f10057fcc78800afe63c4015feb1e200abf58f1002ff8c78800afc63c4015ffa9e200aff94f10057faa78802bfc53c4015ffa1e200aff90f10057fa878802bfc43c400bffb162000bfd8b1008ffcc588006fe62c4001feb162000bf58b1002ff8c588006fc62c4025ffa962011ff94b10007faa588047fc52c4001ffa162011ff90b10007fa8588047fc42c4015ff9962011ff8cb10057fa6588047fc32c4025ffa8e2005ff94710007faa388017fc51c4001ffa0e2005ff90710007fa8388017fc41c4015ff98e2005ff8c710057fa6388017fc31c4023ff90e2005ff88710007fa4388017fc21c4025ffa862000ff94310007faa18804bfc50c4001ffa062000ff90310007fa8188003fc40c4015ff986200aff8c310057fa618802bfc30c4023ff9062000ff88310007fa4188047fc20c4009ffb2c2000bfd9610087fccb0800efe6584001feb2c2000bf59610027f8cb0800efc6584009ffb242000bfd9210007fcc90802efe6484001feb242000bf59210027f8c90802efc6484021ffaa42000ff95210007faa908043fc5484009ffb1c2009bfd8e1004ffcc70800afe6384013feb1c2009bf58e10027f8c70800afc6384013ffa9c2009ff94e1004ffaa708027fc5384013ffa1c2009ff90e1004ffa8708027fc4384009ffb142000bfd8a1007ffcc508006fe6284001feb142000bf58a10027f8c508006fc6284021ffa94200fff94a10007faa50803ffc5284001ffa14200fff90a10007fa850803ffc4284013ff994200fff8ca1004ffa650803ffc328401b7eb0c2010ffd4610007fca308003fd5184021fe28c2000ffd0610007fc8308003fd4184001fe20c2009ffcc61004ffc6308027fd3184013fe18c200fffc8610007fc4308003fd218401ffe10c2007bf98210087fea108013fe5084001fea842004ff14210007fe8108013fe4084001fd2
  | 2 => 0x400c5fac62002fdd63100016eb188004ff18c40015f8c620063ff5310031ff2988018ff54c400c7f8a62002fff4310017ff218800bff50c4005ff88620013ff6210017ff3108001bf9884005ffac420002fd6210009fe3108001bf188400cffea42005ffe5210001fea908017ff1484005ffe842002ffe4210017fea10800bff108400c7fe642005ffe3210031fe9908017ff0c840027fec22002ffe61100017f308800bff58440005fac220013fc6110033ffa888000ff94440007faa220067fc5110017ffa08800bff904400077c822002ffd4110017fe208800bef104400c7fe6220063fe3110031fe9888018ff0c4400bffe4220003fe2110001fe9088017ff084400d5fcc020067ff5010009ff2808000ff54040027f8a02002fff4010017dfa008004ff9004005ff4802002ffd4010001dea00800bfe500400c7fe6020013fe3010031fe9808004ff0c0400bffe4020013fc2010009ffb2c4000bfd96200b7fccb1000efe6588001feb2c4000bf59620027f8cb1000efc6588009ffb244000bfd9220007fcc91002efe6488001feb244000bf59220027f8c91002efc648802dffaa44000ff95220007faa91005bfc5488009ffb1c4015bfd8e200affcc71000afe638802bfeb1c4015bf58e20027f8c71000afc638802bffa9c4015ff94e200affaa710057fc538802bffa1c4015ff90e200affa8710057fc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944004ffd8620007fcc310002fe6188001feb0c4000bf58620027f8c31005bff5188001ff28c4000ff546200b7f8a310003ff4188001ff20c4000ff50620007f88310057ff318802bff18c4015ff4c6200aff86310007ff2188003ff10c4001ff4862000ff84310006fe608802dffa844004ff94220007faa110013fc5088001ffa044000fed0220027fc8110003fd4088009fe2044000fe102200affe6110013fe308802bfd1844015ff4c2200aff26110013fc3088003ff9044001fbc822000ff64110013fc2088003fc1044000ffd9520005feca900037f65480013fb2a4014ff9952001dfcca90003fd65480017eb2a4014ff1952001df8ca900037c65480073e32a4000ffd9120005fec890003fe64480177f3224000ff59120005fac890003fc64480177e3224014ffd5120007fca890003fd5448029fe2a24013ffd8d2009dfec690003df63480016fb1a4013ff98d20015fcc69004ffd63480277eb1a4013ff18d20015f8c69004fdc63480056e31a4013ffd4d2009ffca69004ffd5348027fe29a4013ffd0d2009ffc869004ffd4348027fe21a4001bfd892000ffea490007fe5248003f72924001ff54920007daa490007fc5248003ffa124001ff9092000ffa849000
  | 3 => 0xf30e8000bf9874005ffac3a0002fd61d0017fe30e8022ffd4740007fca3a0003fd51d0045fe28e800bffd074005ffc83a002ffd41d0017fe20e8021ffcc74010ffc63a0087fd31d0043fe18e8020ffc8740007fc43a0003fd21d0041fe10e8022ffd4340007fca1a0003fd50d0045fe2868021ffcc34010ffc61a0087fd30d0043fe1868020ffc8340107f841a0013ff65900017fb2c801fff9964001dfccb20003fd65900017eb2c8004ff1964001df8cb20072fd649003fffaa4800bff95240007faa92002ffc5490009ffb1c801abfd8e400d7fcc72000afe6390035feb1c801abf58e40027f8c72000afc6390035ffa9c801aff94e400d7faa72006bfc5390017ffa1c801aff90e400d7fa872002ffc4390009ffb14801eff98a4000dfcc520003fd62900017eb148004ff18a4000df8c52007fff529003dff2948000ff54a400f7f8a52002fff429003dff2148000ff50a4005ff8852006bff329003dff194801aff4ca400f7f86520013ff6190001ff30c8000bf98640007fac320002fd6190009fe30c801fffd4640007fca320003fd519003ffe28c800bffd0640007fc8320003be4190001fea0c800bff1064000778832006bff3190035ff18c801aff4c6400d7f8632007bff2190001ff10c8000ff486400f7f8432002efe609003fffa848004ff94240007faa120013fc5090017ffa048000efd024005ff6812006bff3090009ff184801aff4c240027f8612007bff2090009fe1048000ffd9540005fecaa0077fe65500077f32a8000ff59540005facaa0077fc65500077e32a801dffd514005ffca8a0003fd5450017fe2a2801cffd8d400e5fec6a0073fe63500057f31a801cff58d400e5fac6a0073fc63500057e31a801cffd4d400e7fca6a0073fd5350039fe29a800bffd0d400e77e86a0073fe4350039fea1a801cef50d4005ff886a0003ff62500017fb12801bff9894000dfcc4a0003fd6250037fe3128001bf189400effea4a006ffe5250001fea92801bff1494005ffe84a006ffe4250001fea12800bff109400e7fe64a006ffe3250039fe992801bff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0002fc615003bffa8a8000ff94540007faa2a0077fc5150017ffa0a8000ff90540007fa82a002ffc4150039ff98a801cff8c5400e7fa62a0073fc3150037ff90a8000ff88540007fa42a006ffc215003bffa828000ff94140007faa0a0077fc5050017ffa02800bfed0140007fc80a0003be4050039ff982801cff8c1400e7fa60a0073fc3050037ff902801bff08140027feca2002eff6510017ff3288003bf9944005ffaca20002fd6510009fe328800bbf1944005dfcc82002fff5410017ff2a0800bff5504005ff8a820013ff63100177fb18800bff98c40015fcc62002fde63100056f318800bff58c
  | 4 => 0x2efe6494001feb24a000bf59250027f8c92800fff5494007bfaa4a003ff9525001ffaa9280037d5494007fe2a4a004ffd8e50135fec72809bfe63940057f31ca026ff58e50135fac728013fc63940057e31ca003ffd4e5001efea72800ffe5394007fea9ca026df54e5001ff8a72809bff439404dff21ca026ff50e50137f88728013ff629404bff314a001bf98a50007fac528002fd6294009fe314a001bf18a5001ffea52800ffe529404bbf294a003ff54a5001ff8a52800f7c5294001ffa14a025ff90a50007fa8528097fc429404dff994a025ff8ca50137fa6528097fc3294009ffb0ca000ff98650005fcc328003fd61940017eb0ca004ff1865001ffea32800ffe5194001bf28ca003ff5465001ff8a32800f7c5194001ffa0ca000ff90650007fa8328003fc419404dff98ca026ff8c650137fa632809bfc319404bff90ca000ff88650007fa4328097fc21940077f304a003ffd425001efea12800ffb5094009fe284a003fe14250137fe6128013fe309404dfe984a004ff0c25012ffe4128013fc20940077fb2aa000ffd9150005fec8a8003fe6454001feb22a000ff1915005df8c8a800fff5454007ff2a2a003ff5515001ff8a8a8093ff63540497fb1aa024ff98d50015fcc6a8093fd63540497eb1aa024ff18d50015f8c6a800fff5354007ff29aa003ff54d5001ff8a6a8093ff4354049ff21aa024ff50d50127f886a8003ff62540017fb12a023ff9895000dfcc4a8003fd6254047fe312a001bf1895001ffea4a800ffe5254007fea92a003ff14950007fe84a808ffe4254001fea12a023ff10950127fe64a808ffe3254049fe992a023ff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a8002fc6154007ffa8aa003ff9455001ffaa2a800ffc5154001ffa0aa000ff90550007fa82a8003fc4154049ff98aa024ff8c550127fa62a8093fc3154047ff90aa000ff88550007fa42a808ffc21540077fb02a003ffd415001ff6a0a800ffe5054001bf282a003ff1415001ef8a0a800ff85054049ff982a024ff8c150127fa60a8093fc3054047ff902a023ff0815005ffecba002eff65d0017ff32e8003bf9974005efccba000e7e65d0017feb2e8000bf5974005efacba00027d65d0017fe32e800bbf1974005ffea9a002ffe54d0017feaa6800bff1534005ffec7a002eff63d0017ff31e8002bf98f4005ffac7a0086fd63d0017fe31e8002bf18f4010ffea7a0087fe53d0043fea9e8021ff14f4005ffe87a002fbf43d0017ff21e800bff50f4010f7a87a002ffc43d0017ffb16800bff98b4000dfcc5a002ffd62d00017eb16800bff18b4000df8c5a008bff52d0041ff2968000ff54b40107f8a5a002fff42d0017ff216800bff50b4005ff885a0087ff32d0041ff1968021ff4cb40107f865a002fff61d0017f
  | 5 => 0x484115ffca420803fd5210457fe290820bffd084105ffc842082ffd4210417fe210822cffcc84115ffc64208b3fd3210457fe190822ebf9844116ffea220817fe5110401fea888205ff1444105ffe822082fbf411040bff208820bfd9044105ffa8220803bd4110417faa08822cffcc44102ffc62208b3fd311040bfe188822bffc844102ff84220817ff6010417ff3008200bf9804105ff4c020802fa6010417feb008200bf5804105ff2c020802f9601040bfe300822dffd404116ff8a0208b3ff3010459ff180822cff4c041167f860208afff2010457fe1008205ffd9621005fecb108abfe65884077f32c4200ff59621005facb10817fc65884077e32c4205ffd9221005fec910803fe64884177f3244200ff59221005fac910817fc64884177e324422affd5221007fca910803fd5488455fe2a44205ffd8e2114dfec7108a7fe63884057f31c4229ff58e2114dfac710817fc63884057e31c4229ffd4e2114ffca7108a7fd5388453fe29c4229ffd0e2114ffc87108a7fd4388453fe21c4201bf58a2100ffea510807fe5288403fea944201ff14a2100ffe8510807fe4288403fea144201ff10a2100ffe6510807fe3288403fe9944201ff0ca2100dfcc3108abff518840bff28c4200ff5462102ff8a310803ff418840bff20c4200ff5062102ff883108a7ff318840bff18c4229fd8c62114ffa63108a7f5318840bfe18c4201ffc862100fde4310807f7218840bfe10c4201fd0862102ffec110803fe60884017f3044200ff58221005fac110817fc6088455ffa84422aff1422114ffe61108a7fe3088453fe9844229ff0c22100ffe4110807fc2088401ffb2a4200bfd9521147fcca9080efe6548401feb2a4200bf59521147f8ca9080efc6548401ffb224200bfd9121007fcc89082efe6448401feb224200bf59121007f8c89082efc6448451ffaa24200ff95121007faa8908a3fc544844fffb1a4227bfd8d2113ffcc69080afe634844ffeb1a4227bf58d2113ff8c69080afc634844fffa9a4227ff94d2113ffaa69089ffc534844fffa1a4227ff90d2113ffa869089ffc43484037fb124201ffd492100ffca490807fd5248403fe2924201ffd092100ffc8490807ee4248403fea124200fb5092100ff88490807ff3248403ff1924201ff4c92100ff86490806ff6148451ffa8a4200ff94521007faa2908a3fc5148401ffa0a4200ff90521007fa8290803fc414844fff98a4227ff8c52113fec629089ffd314844ffa98a4227ff0c52100ffe4290807f72148403ff10a4200fb8852100ff84290807ec2148403fa10a4200ffd8121005fec090803fe6048401feb024200ff18121005f8c0908a3ff5048451fe2824227ffcc12113ffc609089ffd304844ffe1824201ffc812100fde4090807fc20484077eb2ca004ffd9250007fcc928
  | 6 => 0xbfe98e8235ff0c7411a7fe43a08d3fc21d0417ffb06820bff98341005fcc1a082ffd60d04017eb06820bff183411b7fea1a08dbfc50d046bff9868235ff8c3411affa61a08d7fc30d0469ff9068234ff0834102ffecb20802ff6590467ff32c8203bf99641007facb20802fd659040bfe32c8203bf19641185fac9208cfff5490417ff2a48200ff5524105ff8a920817ff639045d7fb1c822eff98e41015fcc7208bbfd639045d7eb1c8205ff18e41015f8c7208bbff539045dff29c822eff54e41177f8a72082fff439045ddfa1c822eff90e41177fa87208bbbd4390417fe21c8205ffd8a41197fcc520806fe6290401feb148200bf58a4102ff8c520806fc6290467ffa948232ff94a41007faa5208cbfc5290417ffa148232ff90a41007fa852082ffc429045dff9948232ff8ca41177fa65208cbfc32904177f30c8233ffd464102ffca320803fd519040bfe28c820bffd06410077e832082ff7419045dff98c8205ff8c641177fa6320817fc3190465ff90c8205ff0864102ffec120803fe60904017f3048200ff58241005fac120817fc6090467ffa848233ff14241177fe61208bbfe309045dfe984822eff0c241197fe41208cbfc2090401ffb2a8200bfd954118ffccaa080efe6550401feb2a8200bf5954118ff8caa080efc6550463ffaa2820bff95141007faa8a082ffc5450461ffb1a8230bfd8d41187fcc6a080afe6350461feb1a8230bf58d41187f8c6a080afc6350461ffa9a8230ff94d41187faa6a08c3fc5350417ffa1a8230ff90d41187fa86a082ffc4350401ffb128200bfd894117ffcc4a0806fe6250401feb12822fff1894100df8c4a08c7ff525045fff2928200ff5494117ff8a4a082fff425045fff2128200ff5094105ff884a08c3ff325045fff1928230ff4c94117ff864a08c7ff5150401ff28a8200ff5454118ff8a2a082fff4150417fba0a8200ff905410077c82a08c3ff3150461ff18a8230ff4c541187f862a08bfff215045ffe10a8200ffd8141005fec0a0803fe6050401feb028200ff18141005f8c0a08c7ff5050463fe2828230ffcc141187fc60a08c3fd3050461fe182822fffc814117ff840a0817ff65104177fb28820bff9944101dfcca2082f7e65104073f328820bff59441005faca2082f7d65104013eb288205ff1944105df8ca2082efe6410417ffaa0820bff9504105ffaa82082ffc541040bffb18820bbfd8c4105ffcc62080afe6310417ef3188202b798c4105ffac6208b2fd6310417eeb188200b758c4102ff8c62080afc6310459ffa98822cff94c41167faa6208b3fc5310417ffa18820befd0c4105ffc862082ffd4310459dea18820bff10c4102ffec42082ffe62104037f310820bfb9884100ddcc42082ffd62104017eb10820bfb58841005dac420817fc62104037e310822dffd
  | 7 => 0xa1007fc2150801ffb028400bfd8142007fcc0a1003fd6050801fe3028400bf181421e7fea0a10f3fc5050877ff982843bff8c1421dffa60a10effc3050803ff9028401ff0814201dfacb28817ff6494401ff324a20bbf99251007fac928802fd649440bfe324a203ffd525101ffca92880ffd5494407fe2a4a205ffd8e511d5fec7288ebfe63944057f31ca23aff58e511d5fac728817fc63944057e31ca203ffd4e5101ffca72880ffd5394407fe29ca23affd0e511d7fc87288ebfd4394475fe21ca205ffd8a511cffcc528806fe6294401feb14a200bf58a5102ff8c528806fc6294407ffa94a203dfd4a5101ffca52880ffd5294401bea94a203ff14a51007fe85288e7fe4294401fea14a239ff10a511d7fe65288e7fe3294475fe994a239ff0ca5101dfcc32880fff5194407bfa8ca203fdd465102ff8a32880ff45194475ff98ca205ff8c6511d7fa6328817fc3194473ff90ca205ff0865102ffec128803fe60944017f304a200ff58251005fac128817fc6094407ffa84a203ff1425101ef8a1288ebff3094475ff184a23aff4c2511d7f861288e7ff2094473fe104a203bfd9551007fec8a8802ff6454401ff322a200ff59151007f8c8a882efc6454407ffaa2a203dfd515101ffca8a880ffd5454401beaa2a203ff151511c7fec6a88e2ff6354471ff31aa202bf98d511c7fac6a88e2fd6354471fe31aa202bf18d5101ffea6a880f7f5354407ff29aa203ff54d511c6faa6a880ffc5354471ffa1aa238ff90d511c7fa86a88e3fc4354401ffb12a200bfd89511bffcc4a8806fe6254401feb12a237ff1895100df8c4a880fff5254407ff292a203ff5495101ff8a4a8803ff425446fff212a200ff509511bff884a88e3ff325446fff192a238ff4c9511bff864a880eff6154407ffa8aa203fdd455101ffca2a88037e5154407fe28aa203df1455101fe8a2a88e3ff3154471ff18aa238ff4c5511c7f862a88dfff215446ffe10aa200ffd8151005fec0a8803fe6054401feb02a200ff18151005f8c0a880fff5054407fe282a238ffcc1511c7fc60a88e3fd3054471fe182a237ffc81511bff840a882fff65d04177fb2e820bff9974101dfccba082ffd65d04017eb2e820bff1974105df8cba082fff54d0417ff2a6820bff5534105ff8a9a082fff63d04177fb1e820bff98f41015fcc7a082ffd63d046b7eb1e820bff18f41015f8c7a08d7ff53d046bff29e8235ff54f411aff8a7a082fff43d0417ff21e820bff50f4105ff887a082fff62d0417ff3168201bf98b4105ffac5a0802fd62d0417fe3168201bf18b411b7fea5a08d3fe52d0401fea968234ff14b4105ffe85a082ffe42d0417fea16820bff10b411affe65a08d3fe32d046bfe9968234ff0cb411b7fea3a0803fe51d0401fea8e8236ff147411affe63a08d7fe31d046
  | 8 => 0xfd415401ff8a0aa00f7c5055083ff982a841ff8c15420ffa60aa107fc3055081ff902a840ff0815400dfecaa9003ff64548017fb22a400ff99152007fac8a9003fc64548177e322a403ffd515201efea8a900ffe5454807feaa2a400df5515201ff8a8a90ffff635487f7fb1aa43fff98d52015fcc6a90fffd635487f7eb1aa43fff18d52015f8c6a900fff5354807bfa9aa403ff94d5201ffaa6a90ff7d5354807fe29aa43fffd0d521fffc86a90fffd435487ffe21aa401bfd895200ffea4a900fef5254803ff292a401df9495200ff8a4a90077c5254803f6292a401ff9095200ff884a9007ff3254803ff192a401ff4c95200ff864a9003ff61548017fb0aa400ff98552007fac2a9003fc61548017e30aa403ffd455201ff8a2a900f7c515487fff98aa43fff8c5521fffa62a90fffc3154803ff90aa401ff08552007fec0a9002ff6054801ff302a400ff58152007f8c0a9002fc6054807ffa82a403ff141521fffe60a90fffe305487ffe982a43fff0c15200ffe40a9007ef2054803fe102a40bffd974205dfecba102ffe65d08077f32e840bff59742005facba102ffc65d08177e32e8401bf9934205ffea9a102ffe54d0817feaa6840bff1534205ffec7a102eff63d0817ff31e8402bf98f4205fbcc7a100ade63d0817feb1e843dbf58f4205fbac7a1002dd63d0817fe31e8402bf18f421effea7a10f7fe53d087bfea9e843dff14f4205ffe87a102fbf43d0817ff21e840bff50f421ef7a87a102ffc43d08037eb168401ffd4b4200ffca5a1007fd52d0803fe2968401ff90b4200f7c85a1007ee42d0803fe2168401ef10b4200ffe65a1007fe32d0803fe9968401ff0cb4205ffec3a102ffe61d08017f30e840bff58742005fac3a102ffc61d087dffa8e843eff147421effe63a10f7fe31d087bfe98e843dff0c74200ffe43a1007fc21d0817ffb06840bff98342005fcc1a102ffd60d08017eb06840bff183421f7fea1a10fbfc50d087bff986843dff8c3421effa61a10f7fc30d0803ff9068401ff08342007fecaa1002ff6550879ff32a8403bf99542007facaa1002fd6550879fe32a8403bf1954200dfec8a10f3ff5450817ff2a28400ff5514205ff8a8a10efff63508777fb1a843bff98d42015fcc6a10effd63508777eb1a843bff18d42015f8c6a10efff5350877ff29a843bff54d421dff8a6a102fff4350877dfa1a843bff90d421dffa86a10efbd4350817fe21a8401bfd894200ffea4a1007fe5250803fea928401ff1494200ffe84a102fef4250803ff2128401ef9094200ff884a1007bc4250803f62128401ffcc94200ffc64a1007fd3250803fe1928400ffd8542005fec2a1003fe6150801feb0a8400ff18542005f8c2a10f3ff5150879fe28a843bffcc5421dffc62a10effd3150877fe18a8401ffc854200fde42
  | 9 => 0x100300500000000700200200300100200000300300000100600100200700500200500400200100900200000600300000000100100100100400000000000000000200000000300100200100600500301600100000200800100500200500700200300600100200100000700100100000000100300500000000300200000100100100000600400100000000100000000900400000800100200100100200000000800101100000000200800000300000000000200000000000c00000300000600200000100100000400000000200400300000400000f00000000500000100900100000800100900200000100000500000400400200100000100300000700000000200a00800400000100000000500000000000000000000100100000000900100200000000200100100400100300700100400100100300300200300100000000000600001500100100f00000b00100000200100000000100001200100100400900500800300000000400300100000000100400000200100500300000200000800400100100000100000400000000000000200100200200200100600000800000000601dfacb2a02efe6495017ffaa4a80bdfd525401f7ea92a00f3f5495017fe2a4a80bef1525405ffec72a02eff6395017ff31ca802bf98e5405ffac72a10efd6395017fe31ca802bf18e5401ffea72a00ffe5395007fea9ca803ff14e5405ffe872a02ffe4395017fea1ca80bff10e5405ffec52a02ffe62950037f314a80bff58a54005fac52a02ffc62950037e314a803ffd4a5401ffca52a00ffc5295017ff214a80bff10a5421ffe652a10bfe3295087fe994a842ff0ca5405ffec32a02ffe61950017f30ca80bff58654005fac32a02ffc6195007ffa8ca803ff1465421ffe632a10ffe3195087fe98ca843ff0c654217fe432a10bfc2195017ffb04a80bff98254005fcc12a02ffd60950017eb04a80bff1825401ffea12a00ffc5095087ff984a843ff8c25421ffa612a10ffc3095085ff904a842ff0825405dfecaaa00eff6455007ffaa2a803efd515405ffca8aa02f7e5455017fe2a2a80bdf1515401f78a8aa107ff63550837fb1aa841ff98d54015fcc6aa107fd63550837eb1aa841ff18d54015f8c6aa00fff5355007ff29aa803ff54d5401ff8a6aa02fff4355083ff21aa841ff50d5405ff886aa003ff62550017fb12a840ff9895400dfcc4aa003fd6255081fe312a801bf1895401ffea4aa00f7f5255007ff292a803ff14954207fc84aa02ffc4255083ff992a840ff8c95420ffa64aa103fc3255001ffb0aa800bfd8554007fcc2aa003fd6155001fe30aa800bf1855401ffea2aa00f7f5155007fe28aa841ffcc55420ffc62aa107fd3155083fe18aa840ffc8554207f842aa003ff60550017fb02a800ff98154007fac0aa003fc60550017e302a803f
  | 10 => 0x2f6230000000046800003c80000000000cc458e0000000000fde0b200000002ea0000001e780000002971cbc0946723e791b01140000a89f080003b10fd00000000000a919441525f032284a817000000000002cc63a00000003780000001718c2e7443b08000a6037913f0cdc00051038520ccf0a3620000000c3000019200000000000000000c567290000000bee27400013e4fda00001807c80007a24100f94abc54e0a9910c0001082120f44e0840b0000808d44566000000104c4eb000060c938341000000000000000005f8000000000000000000023b00000005f93d380000000000001864000000000000000000000000000000001b78000c9a0001dc000000000007385f46a600000000007720000000af0000000000000000000000000009ba3d02eb883ca902e23b013f40fe0003f0126c8341a43b900008624bd1320eb4cc24b0369800000000023b800099200000000000280e40a29a9c33a000000000000000000000004140000000cb42f600100500100400400001500200400700100100000300200000800200200100300000800000201500600000001300000000100000000800000a00100700400101000700000000400200700000000100b00000300100800100100000000000100000000002600700001200000600200100000100600000b00400100000000000000f00000400200200300200000500000400100300200000000000000000100400400000d00500000100000000000700000000300100300300000000a00200000200100100000b00900100400400000000e00300700000000000300000600000b00400000400300100700900000200100000000200000f00300200200100000000000000000000800400100000100900000400400100000800000000000200100400300000000000600500700400100300000700100000000000200000100000000200000200000000400100100300500100200100000000300000900200800000000000000100000100500a00900100000000200500300500400200000300500000100100100000000300400100500000200200300100000100000000200100100000000700100000200000100100800100000300600400600101100200600400000a00200000000000300200200100100500f00100400200300101a00000000300800001e00500100200000300500200100400100100c00000000700700000000000200000500000100600100700000000000f00000100100000000300b00900d00600000600500100b00000300200001100700000300000100300000300200100100600100000300000000400000000200000500000000300300200000f0050030000000000030060030000000030020060010000130000040020030000010010020010010
  | 11 => 0x284065447a0da0eb81642465252a489584421c50001fd4e7e7270358a544405f81459438fd028633c86788fa07311706343c83940000bf80000000000000b5644913006a8a042503c480000401f1422800000000000000004d80000000000000537000000000000011c9cd40005d600000000ba344000000071655c0a100000ca0000000b3c03668100000000002220001cc4778000000000091200000000000000000001ab8bb860c0000000000042170961876e24a23c040027273a000070500237f16d1b240000003c6800000000000000000000003a106c8d08000000025c00000000000000000003d48000a24000000000000036c31a87d008c13c215827800000031980000000de41517502e800000000000002463e30acc90400000000009d014a271800000000020a9dec00033a0dc065c340077107078400000031c80004f4058408898461e0000000000606505000000000061000000000004a6000000063674719c9dac17c5a00888ccc86a0001e19d740002ec1e0000000000000000000001733f200000005f33a48000c980000a582a0eb06673d18e384364fc3ca00000006cf3a0800000000021e000000050134f8000c7060500012a435c7232f312e400064100002bc4e06110001284a0e04423287b89da0000000074d380002cd000000000000000000004ac0000000000027000121c000703000000000077d33603200000001ad000000059800000000000000001e4c1f80000000000b862d600007ec7ec0000000000000000000000100c0003bb80000004011e9800108c09333b80c87a875c1838ca40003100ca202c0000003b60f9c00000000000000002fa00000000000002e800000000000000000d6e000000000000000028a00d000000015488710601e6000000000022c0a00ec800023810f136023279239d94e4d3a000090800000000000014f89220000000000abe0000001f0c7aa3a90000154b447510000000cf851a265000063e0000c100000003f9323000000000000000001862fb000000000000001a950cdb200014980001d220500000000001c2000000057c00041e800000000010e9ba4504000000000000078a0be000000000004098d80000000001f580000001fd18d0ef46c80000f747540000fa9d2c1be0091ee00000005be35f8ad470671114400000000000000000000196365920c71400012c0f04e2a07815509040002b80000000e5a5871bb051c6c20e20a20e886b27b408e1c6800017a000000086e0000000bdcb6c36b0e720fc0000f100000009e483203d8000fcc72516320d0c1c7751a782ccaf41cc20500dc0004001528a48a8280a40b02240005160001ec882800010d0000ef800035903309620002f88e6400060629199b80000003aa80000005c53210000e8a5e9000000050811b38d8408
  | 12 => 0x4a1878b3e69d9895000033a872c6e40000000000ca82e71671f5c85e2910000000000000000197494000000020b000075b24993885140000001b440003da00000000000000001efc0000003ee8000fd60000ad93a44167183c8000003e0002f0800000051704e9a2074851b3da80002a000000004fc90a0d70e80000cd0000000167055e16e2280000000000000000000069718580000006161a191d44be0703fe9f9c40257200000006e80380000000dc00002cf0374cd400036c0764000000000000000029f00017d40005b105e80000000002331d300002682c9800040800000001d839a000191800000000011e00007d42a40a6084c0006b40001f6000000000000000004c32aa98209c0000000125c0006be0000000a5000036b965cdb80001fe0c006800000001338c242491fd8000000000294800000000015380380006e20000000a8400000019fc07e000000000009e00000000000007f8000000047600000000000000000638000000000000000030a2140001bdc37c12f26c94e8000000000000097600000004d850000000000000000002b013d00000001eb05ace3e5092f61e38a5415d000010c00045a0d580a80004db06e000000073800009b40002e30f500002142ee0000000d063470000d280cc7da18b89cc0000ce03a9a38dd80e50000bc01ac2f934615d00005951bf0ae80000a115700003260ac07782f00000001791528c4206f1cb0b1002c07d2bf0cd4bba70b000000000000000000000000000438000052000000046000069409019c4b605bc00010a40001580001da800000020e8000a305d90000000000000000002800071039e0000b1045f0001e200000002e10000c3c00000012f80003be104800000016f41100000000003f500009560003730000000000000092c00032f09c00000000000000000b146a9000000000065c00000000000000000000000000000000013800000000006bc18f3b4901c0000c618e00000002a3128800000005b333018000000012380000007f907c09d83e62d20730aecb5a16901d0000d6a2b40cf80000000002108ed811e70e1fa9bf87fa5500259ee04ae80724501f8b745191f60fc05340000001e5878c5061f598b820a8432339ae08b26ab04d0000ddc797000032c7de5cc27a800022e39a3d291d00007402b080000000003790e4801a3f11f9144441a24820e08400000003901b90000000000000000056e0da03cc00000027f800000000016400000003f40000000d7854f21f212ca7e0001a40f1c0006c10458550a4c5a741d1938db670500000000000000f61f6cd400002c71a4ce0400005b80000004c23990a6000e000000171c0005a91d30000c345f6230935c8643040001c1c0000002c8004c000000000000000000037980003f20d200000000000000001e70eec39c
  | 13 => 0x40480000002650298000b7000000006bc5380000269ae400000013a800004827100000000000000000000000637229a0bc67e7c80000000f0200028f0000000000235000000000010f9928a567de10000000002083d81310000000000000000065f14c8dc4380000259800036600007e87500002810000000f8271e2bb0b5c0a400000000000006fc0000600c886310129dbc1287520000000386000000000000000037f80005fe72a1419c3ce6c000000000000000000000002ac83c1d400000000001ad93e8ba2650000000082c00025500009be21500000000000000001344bd6000000000000078f2760524a9661c00000000000003fe000052e00000010083d611f3de816867a0003b70001018314000000000000022500000000000001e746ae82e190000049a0000000000c5e0e10ef000000000015b95a025a01740100005da34e25a98886ba44201d81e907c3fe2680f8cc808310c50bbc9fc1fd02f1dd01b651507a996075c0ab1dd000101000008a82ec0004cf0f18cc07884bf2028bc4f8800000017600e84af29200680000004070000c8e46d122000000036900000000004840000000e2c5fb3a3000000033225b8000220000378000000000000000009326850001600b2800017580000007aa0001db400000000000007300000000d90f80551209108014e814000000000000000015502666430000000000000000000000056a0001f1c0005200000000bca77e000000070c227324826c7180001e6000000040d2b11accee60c500017fd02e0003542104000000000000000000022a00000000002bf80000000002dc8000000438380207c2b47820000e447a401e00000000003bb41a863800055300007fc234564010911800000026e0bd479e5211931e600001811e7000000043d00000000004b204c9b84e940b1030800000000000000005ba83900000000000003e81e68ada1bd00018c820800000019483e00003e609fcbde00011880000001160000000000000000000000060724a9fc07420000000000000000000000000000025719cc0003c817200009cc0c025a1240d2050f38600000000003899be800043000000000000002b787b442e0543fa000000000036d0b60cf084700003f8a700cf3451aec71e02c3b3800026e69a1b300000005de01680004524482a30000000370022858849806804a98c0c465672639ebc4ee7860781b8cad83cd09f0b148741320f4066844640f3a786100006c70a420dcba46f912e2064c4e03d00002208366dd3e50c380006eb091034503a60930517f82d469b4020e002b800000001580005c424d00b80002540000bf40004c00000aa00d40000000cb83ca387226a120000000000000000000001b158c7044f70000000b1642c31000009bc00000000000007b60000000fe40003e915a
  | 14 => 0x2000000000000003de5b4208187ca9841324c00000000001210000d9c0ed16100010340002d200010420000000670000000000000000000000000004bc57b00014f0f4c2e004286d800000012c944c00000000009e000000000000001d050300000000008230d1000057a30628e8e7c7c045b0c61294c7a008098000007c0001279d6800000f1ef820000000020c842c0002250000b94fa633808f0de8b460000001cc00001290000c94ebc37b000195472057c2de800014445500000003ce44e42488640003422c79158258212421043c6506ed23210945d45df3bc8000d2a33c000209ccae42641400000002cb34696448765fa119800014c00022e9ae8ab20012bba0e00002de00007f0000000000000000032237400006f8114000000000006300017900000000000d5080800000014cc9280000199da000065a00000000000004028c340003e900000000004e72138c20d127e13488000a4e0002390c9c0006620001c740000000001f8847c0000000000cc60000001bc4fe66980c889480003ab181000046c01138c99d80000000000000000000000000000038414f11ac990000000131421a2e83a983a80007213729c90000680000000057e16c00000006d00f40e79c7000048b052000102a3a316482089f61b1000041c3f00000c400009745222169ef849c0480461990cfa0002279f2c2aa5e21f99d348223460cca128b7e00012d800102000040d8000000000247849c9460ff2e400000000000001a8437e2d90000d4800000030d8000a8e2dc00000003ac6f400000000807a100002580000ae1d99b080005e827801402027633c200000001d23bc1bf45b600000000000001a8000000017e5d32698000b4200000009a49a800004c0a980000002491f5000000000000009c2575000000060a000363195805e00000018f887e1a31ae0000baa0000000f60000000000000000000009d80004c6000000000000000032580a000060400000000000000001d5800050d0e30000806000000033418400026a9b5851848d000203478a2182cd9dfc8dc55618091e47dc0000000f78e7c7bc337819c7da3780f48c2800038d0e5035031200028e07f80000003d58000ec412500008c852052f0000000cd600000018fccf422a3959e0c0da44421a0000b4a4392ab85a03c000041b081c42258221187d80004963caa094f8a00024300005e8000000160c48a360362165800053500e1920d460000000000c5a00018c000000000000000000000000001aa86ee000000131891000000000000000000000000000000000203c00000028505b400040800000000003581ab1fb80000120000c48bb605c0001fc48444f13b800010486ef3ef9610d6c53100015140000000000000ce80000000000cc00000000cec34a1c81ff85c80983af00a97d051c00
  | 15 => 0x35527c1a90fec0003ec94d0afa3e418d00000000000000e1431600039a0000cf65700001b4100000000003b0b76544214078893a000160a0a49780003a41114250170000000000047e0000fa0000397000000010817723f88d49446a6000136800042a2471d5c594000000000000073900000009d400000000000005c100000000000000001cf43be00000006980000000d480000007bb1350d144cc00000000000000570000000000000000000000000000004d0da80003f1800020631137d800000000035792040007c933280000000000000d9400041e3a71ac074055200000000000000001b14c0000c2c61ccc00000000000000000000000000c7604e34780000005ea09584b81b24472070000562750000000000000000000009c881834f115c3203bf1f30000000000000163400062503902a83b813a38a17f00000001e48a6c5440000000000d620000dc99782f258913d9e646be1ba00014f4b6627c000000073c00025b180820c1c923884240000000000b4421836d1478b981ee7dc0fb979c30c0002ce80006680000000000fa252d1ec80007361260a3000014644c18c8c5411c0ad32980000001602cf80003a6000000105c00000000013cc0000001ed935903851f00017803767ad2e588900000e313e89c8f4039d0a08000d98000000207800000015c800048636e352800000000000003d80002d0000000000007c3fd0000b3200037b0000528163305800000044b2ae8e9c00008d3931060ab00d5401801055a0102d61ea00007d523796d469a03c0b89a1c0000000001728c500c1000000808206e0b39170a6c6590000000000000002800059843300c00005120000000ca801600037a8cac0001dd33f069ca805af133942c04433e0000aac46862c1ca80000000000001898e0c2030001fdc3880ba3dc80000000002460000a7600000013042485320000000d0c4622c291f00000d300000000000000000000000000000000000000000000000006960001ecca082f300000000005a603617b800032c00000000000001b180000000000000000d040000000000bb400000002d8000000000000000000000000000005a814280008bc000000000000000031e08c0818165089850c0000d8000000000000023d93bc1942b011f8000d867e938916dcd5a14d00000000e24cb000000046e0000c9101800062a30680009ec25322c00ac0003ca1e5806400000000016c8ce000000000001a06132d50000000389000000062c0620001e6cae6000000061c2ae50000000005580000000000d32161000012400000000013b80000e0000071c1400000349ab000000015b0000e444cc0db9be06a036a13c987447415914680006ce0790001d7c0000000002048b5c78000000000006920000098e023d7000000093e7ac0001c
  | 16 => 0xdaa0030000660000000386896886c4b82ad9b34c1e22b0000900000000327914800000039600000000000000578d8000000002e40000000000190f480000cd8000d7a6d23c380007100002f68974f221db0000000cb60000001e30ff622f1508cd800005f0d60000000000000011c1d626e24f0b001dc0001619ca00726df1a880000000000000dcce2e3b534580002ec7710000000f6e592000021810600005a80000000000da9cb800000000000000000002b8800090056509a8000af00000000e041925c00ed134800031300011a435a0000000a800000002b59eb8af20001d802c074a1121379290f3e00030080004aa0000000000000000000000085c00014e80000000004168000a5800000000010560000000000000000184814423a0001908be000020c2a68dd48a216407ca11099a7ce0a79cdc45a26b05a18903b02d307d0eb05a81b023188182fe76504f885821c4e51860000882000174824052c34c3148ed0cda6152f90244f620002048a1c7f0393000000014a00018e9d507ee7ec1f09b2894e7e52e680000003e200005e000013d0000000b9c6690a700000000003dd178cffe2260ea80001f60000000000b0244023811cc0007433ac8b5400c00041d8744c0600030a0f08b922fc4099c2434234909882480000311a59ff845000020f89880000000000000dd42b218f1b78188000000000000000000000005be5cf0af8000bfa6e72ad0b3477a000011800000084023d000095a00000000000000000000df4ec80
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810036ef715881002eee715881002eec7158810006ef515881002eee515881002eec515881002eee415881002eec4158810006ef315881002eee3158810006ed315881002eec3158810036ef7058810026ee7058810026ec7058810006ef5058810026ee5058810026ec5058810026ee4058810026ec4058810006ef3058810026ee3058810006ed3058810026ec305881002eef1058810026ee1058810026ec1058810004ff7654810024fe7654810004fd7654810024fc765481000eee6254810006ed6254810005fb7054810025f8705481005cff76d0810024fe76d0810004fd76d0810024fc76d081003dde73d0810005dd73d081000eee62d0810006ed62d0810004ff7650810024fe7650810004fd7650810024fc765081000eee6250810006ed6250810005f7715081002df47150810094ff76544101beee6254410006ed6254410004fd76d04101a6ee62d0410006ed62d0410004ff765041017eee6250410006ed625041002fb4415041008cff764841000eee6248410006ed6248410084ff765401011eee6254010006ed6254010004fd76d00100457e75d00100057d75d0010106ee62d0010006ed62d0010004ff76500100deee6250010006ed6250010226fa6050010027b8405001007cff76480100057f75480100457c7548010005df734801003ddc734801000eee6248010006ed624801007efa604801002ef576c4010027e662c4010027e562c4010025f570c4010026f660c4010025f97684010026f9768401000cf97684010026fb6484010006f96484010026fb6284010027ea6284010006f96284010027e96284010006e9628401002df9718401002efa6184010027f26184010004ff76440100057f75440100457c7544010005bf7444010005bc7444010066ee6244010006ed6244010025f77644010006f77644010004f77644010007777544010007747544010007b77444010007b47444010027e66244010027e56244010025f77044010026f66044010027f25044010007f15044010007f34044010027f04044010027f22044010007f1204401002dfb7644010006fb7644010004fb76440100077b7544010007787544010007bb7444010007b8744401002efb6444010006f9644401002efb624401002fea6244010006f9624401002fe96244010006e96244010025fb7144010027f3714401002efa614401002ff2614401002ff25144010007f15144010007f3414401002ff0414401002ff22144010007f12144010
  | 1 => 0x9410014fc73594100467f53594100067d5359410004ff725941000cfe725941000cfc725941001cff715941002cfe715941001cfd715941002cfc715941002e7e515941002e7c515941001cff7059410024fe705941001cfd7059410024fc70594100267e50594100267c505941001cfe75d9010004fd75d9010024fc75d9010024ff73d9010014fe73d9010004fd73d9010024fc73d901000cfe72d9010026ee72d901000cee72d9010004fd72d9010026ed72d9010004ed72d9010024fc72d901002cfe71d9010026f671d9010024fe70d9010026fa70d9010004fd7699010026bf6499010026bc649901005cff7659010026bc6459010004ff755901001cfe755901001cfc7559010024ff7459010026bf7459010004ff7359010014fe7359010004fd7359010014fc7359010006bf4359010006bd4359010004ff725901000cfe725901000cfc725901005cff715901002cfe715901005cfd715901002cfc715901002ebe415901002ebc415901005cff7059010024fe705901005cfd7059010024fc7059010026be4059010026bc405901005cff7695010024fe7695010004fd7695010024fc769501005ebe6495010006bd64950100473f5495010216ee6295010004ff7655010024fe7655010004fd7655010024fc765501001e7e65550100067d655501005ebe6455010006bd6455010206ee6255010005f7715501002df47155010005fb7055010025f8705501001cfe75d8810004fd75d8810024fc75d881005cfe74d8810004fd74d8810024ff73d8810014fe73d8810004fd73d8810024fc73d8810034fd72d881002cfe71d8810026f671d8810024fe70d8810026fa70d8810004ed7698810026ef6598810006ee6598810006ed6598810026ec6598810026ef6498810006ee6498810006ed6498810026ec6498810026ef6398810006ee6398810006ed6398810026ec639881002eee6198810026ee609881000cff7658810026ec6258810004ff755881001cfe755881001cfc7558810004ff745881005cfc7458810004ff7358810014fe7358810004fd7358810014fc7358810024ff7258810026ef7258810006ef5258810036ee5258810036ec5258810036ee4258810036ec4258810006ef3258810036ee3258810006ed3258810036ec325881000cff715881002cfe715881000cfd715881002cfc715881002eee215881002eec215881000cff7058810024fe705881000cfd7058810024fc7058810026ee2058810026ec2058810025ef7658810036ef765881000cef7658810026ef6558810006ee6558810006ed6558810026ec6558810026ef6458810006ee6458810006ed6458810026ec6458810026ef6358810006ee6358810006ed6358810026ec6358810006ef7558810006ee7558810006ed7558810006ec7558810006e
  | 2 => 0x778659011025df97490110007bb649011005efa649011005ef86490110007b8649011005eb86490110005f9729011002dfa7190110026fb6190110007ba4190110007b8419011005cff7650110004fd765011005cfc76501100067f65501100ee7c6550110006bf645011005ebc6450110005f77150110005f47150110005f8765011005ef8765011005cf876501100077b6550110007786550110007bb7450110007bb645011005efa645011005ef86450110007b8645011005eb86450110257bb4350110257b94350110005fb7250110007f3715011002df87150110007f07150110005f07150110004fe76101100067f65101100ce7c6510110006bf641011005ebc641011006dde7310110005dd731011024dfa701011008cfe76881100067f65881100b67c6588110006bf6488110006bc6488110005fa768811008efa76881100077b6588110007786588110005fb7488110005f97488110007bb6488110246fa6488110246f86488110007b86488110006b8648811023efb638811023ef96388110065f9728811000efa628811000ef8628811002dfa7188110026fb618811000cff7648110064fd764811000cfc76481100057f75481100757c75481100067f65481100a67c6548110006bf6448110006bc6448110005df734811006ddc7348110006ef624811000eec6248110005f77148110005f47148110067e82048110065f8764811000ef8764811000cf876481100077b75481100077875481100077b6548110007786548110005fb7448110005f97448110007bb6448110236fa6448110236f86448110007b86448110006b86448110007db734811022fd8734811022efb634811022ef96348110065fb7248110007eb7248110007eb624811000efa624811000ef86248110067e86248110067ea5248110007e95248110007f3714811002df87148110007f07148110067eb2148110007e921481100067f65c41100967c65c4110006bf64c4110006bc64c41100077b65c41100077865c411002dfb74c4110005f974c4110007bb64c4110007b864c411002dfb72c4110005f972c41100067f65841100867c6584110006bf6484110006bc6484110065f67684110007776584110007746584110007b76484110007b46484110007f36084110027f24084110007f14084110027f22084110007f12084110044fd75d941005cfe74d9410004fd74d9410024ff73d9410014fe73d9410004fd73d9410024fc73d941000cfe72d9410026ee72d941000cee72d9410004fd72d9410026ed72d9410004ed72d9410024fc72d941002cfe71d9410026f671d9410024fe70d9410026fa70d941001cff76594100267c6559410024ff75594100267f7559410004ff745941005cfc74594100467f5459410004ff7359410014fe7359410004fd735
  | 3 => 0xf73d8910014fe73d8910004fd73d8910014fc73d8910006ef32d8910066ec32d891002cfe71d8910064fd71d891002cfc71d8910066ef21d8910024fe70d8910064fd70d8910024fc70d8910066ef20d89100057f75589100757c75589100067f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc6458910005df735891006ddc7358910066ec6258910004ff75589100067f75589100047f755891001cfe755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf745891005cfc7458910006bc745891005cbc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc7358910064ff7258910006ef725891007cff7158910006f7715891008cff7058910006fb7058910004ff7654910004fe7654910004fd7654910004fc76549100067f655491001e7c6554910006bf6454910006bc645491005cff76d0910004fe76d0910004fd76d091005cfc76d09100067f65d09101f67c65d0910006bf64d091005ebc64d091006dde73d0910005dd73d0910005fa70d0910005f970d0910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101e67c6550910006bf645091005ebc6450910084fe76945100067f659451001e7c6594510006bf6494510006bc649451001cfc76545100067f655451001e7c6554510006bf6454510006bc6454510077745154510005fb7054510005f87054510004fe76d0510024fc76d05100067f65d05101b67c65d0510006bf64d051005ebc64d0510005fa70d0510005f970d0510004fe76905100067f659051019e7c6590510006bf649051005ebc649051005cfc76505100067f655051018e7c6550510006bf645051005ebc6450510005fb7050510005f87050510004fe76105100757e75105100057d75105100067f651051016e7c6510510006bf641051005ebc641051006dde7310510005dd7310510065ee7210510005ed7210510005fa701051007cfe76885100067f65885101567c6588510006bf6488510006bc648851000cfc76485100067f65485101467c6548510006bf6448510006bc6448510006ef624851000eec6248510005fb7048510005f87048510094fe76941100067f659411001e7c6594110006bf6494110006bc649411001cff7654110074fd765411001cfc76541100067f655411001e7c6554110006bf6454110006bc6454110005f77154110005f47154110004fe76d011002cfc76d01100757e75d01100057d75d01100067f65d01101167c65d0110006bf64d011005ebc64d0110005f671d0110005f571d0110004fe76901100067f65901100fe7c6590110006bf649011005ebc6490110005fa7690110006fa76901100077b6590110
  | 4 => 0x9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d9110006bd71d9110006bf51d9110006bc51d9110006bf31d9110006be31d9110006bd31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d9110006bd70d9110006bf50d9110006bc50d9110006bf30d9110006be30d9110006bd30d9110006bc30d9110006bf20d9110006bc20d91100757e75991100057d75991100067f65991100067c6599110006bf64991100057f75591100757c75591100067f65591100067c6559110004ff75591100067f75591100047f755911001cfe755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110014fe7359110004fd7359110014fc7359110004ff725911000cfe725911000cfc7259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c651911005ebe6419110006bd641911006dde7319110005dd7319110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c65191100079e73191100079d7319110006bf6319110006be6319110006bd6319110006bc6319110006be6219110006bc6219110007b9701911005ebf751911005ebe751911005ebd751911005ebc751911005ebf731911005ebe731911005e9e731911005ebd731911005e9d731911005ebc7319110006bf5319110006be5319110006bd5319110006bc531911005ebf721911005ebe721911005ebd721911005ebc7219110006bf5219110006be5219110006bc5219110006bf3219110006be3219110006bd3219110006bc321911005ebf711911005ebd7119110006bf5119110006bc5119110006bf3119110006be3119110006bd3119110006bc3119110006bf2119110006bc211911005ebf701911005ebd701911005eb97019110006bf5019110006bc5019110006bf3019110006be3019110006bd3019110006bc3019110006bf2019110006bc2019110006bd101911005cff7695110004fe7695110004fd769511005cfc76951100067f659511001e7c6595110006bf649511005ebc64951100773f5495110005fa7095110005f97095110004ff7655110004fe7655110004fd7655110004fc76551100067f655511001e7c6555110006bf645511005ebc645511000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910066ee62d891001cfe75d8910004fd75d891001cfc75d891005cfe74d8910004fd74d8910004f
  | 5 => 0x27eb7248210027eb624821000efa624821000ef86248210027e8624821007fea5248210007e9524821002df8714821007feb2148210007e92148210025f576c4210006f576c4210005f976c421002ef976c421002dfb74c4210005f974c421002dfb72c4210005f972c421001cfe76d95100767e65d951005cfe74d9510004fd74d95100767f54d95100767c54d9510004ff73d9510014fe73d9510004fd73d9510014fc73d95100767f53d95100067e53d95100067d53d95100767c53d951000cfe72d9510004fd72d951000cfc72d95100767f52d95100067e52d95100767c52d951002cfe71d9510074fd71d951002cfc71d95100767f51d9510024fe70d9510074fd70d9510024fc70d95100767f50d95100757e76d951001c7e76d95100067f63d95100067e63d95100067d63d95100067c63d95100067e62d95100067c62d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067e42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d95100767e71d95100067d71d95100067f31d95100067e31d95100067d31d95100067c31d95100067f21d95100067c21d95100067f70d95100767e70d95100067d70d95100067f30d95100067e30d95100067d30d95100067c30d95100067f20d95100067c20d95100767c6559510005bf7459510005bc7459510074ff75595100067f7559510004ff7459510006bf7459510004bf745951005cfc7459510006bc745951005cbc7459510004ff7359510014fe7359510004fd7359510014fc7359510004ff725951000cfe725951000cfc7259510084ff7159510006f77159510094ff7059510006fb70595100057e76195100767e76195100047e76195100067f63195100067e63195100067d63195100067c63195100067e62195100067c621951005cfe76d91100067f65d91100067c65d911001cfe75d9110004fd75d911001cfc75d9110006bf54d9110006bc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d9110006bf43d9110006be43d9110006bd43d9110006bc43d911000cfe72d9110004fd72d911000cfc72d9110006be42d9110006bc42d911002cfe71d911002cfc71d9110024fe70d9110024fc70d911005cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d9110006be62d9110006bc62d9110007bb70d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d
  | 6 => 0xd4359210004ff725921000cfe725921000cfc7259210026be4059210026bc405921005cff7695210024fe7695210004fd7695210024fc76952100873f5495210025fa7095210005f97095210004ff7655210024fe7655210004fd7655210024fc76552100067f655521001e7c6555210005f77155210005f4715521001cfe75d8a10004fd75d8a10024fc75d8a1005cfe74d8a10004fd74d8a10024ff73d8a10014fe73d8a10004fd73d8a10024fc73d8a1007cfd72d8a10026f571d8a10026fa70d8a10026ef20d8a1000cff7658a10026ec6258a10004ff7558a1001cfe7558a1001cfc7558a10004ff7458a1005cfc7458a10004ff7358a10014fe7358a10004fd7358a10014fc7358a10026ef7258a1007eee5258a1007eef2158a10026ee2058a10026ec2058a10004ff7654a10024fe7654a10004fd7654a10024fc7654a1001e7e6554a100067d6554a1000eee6254a10006ed6254a1005cff76d0a10024fe76d0a10004fd76d0a10024fc76d0a1004dde73d0a10005dd73d0a10025fa70d0a10005f970d0a10004ff7650a10024fe7650a10004fd7650a10024fc7650a10005f77150a10005f47150a10074fd76946100067f659461001e7c659461008777519461001cff7654610024fc765461001e7e65546100067d6554610005fb7054610025f8705461005ebe64d0610006bd64d0610025fa70d0610005f970d0610006bf649061005ebc649061005cff765061005ebe6450610006bd6450610005fb7050610025f870506100857e75106100057d7510610006bf641061005ebc641061004dde7310610005dd731061007dee7210610005ed7210610007b54110610005f97010610064fd768861000cff7648610024fc764861000eee6248610006ed6248610005fb7048610025f87048610044ff76542100857e75d02100057d75d0210025f97690210026f9769021005cf9769021005efa6490210027ba6490210027b96490210026f86490210005f9729021002dfa7190210027f27190210027f17190210007ba4190210007b84190210005fb7650210006fb7650210027bb745021005efa645021005ef86450210227bb4350210227b94350210005fb725021002df87150210025f97688210026f9768821000cf97688210025fb7488210005f97488210246fa6488210026f86488210026fb638821026ef9638821000efa6288210027ea6288210027e96288210026f8628821002dfa7188210027f27188210027f17188210034ff76482100057f75482100857c7548210005df734821004ddc7348210026ef6248210026ec6248210027e82048210005fb7648210036fb76482100077b7548210007787548210005fb7448210005f97448210236fa6448210236f86448210007db7348210267d87348210266fb6348210266f96348210
  | 7 => 0x5310004fd769531002cfc76953100973f5495310004ff765531002cfe7655310004fd765531002cfc765531001e7e65553100067d6555310005fb7055310005f8705531001cfe75d8b1002e7e75d8b1001c7e75d8b10004fd75d8b1002e7d75d8b100047d75d8b1002cfc75d8b1005cfe74d8b10004fd74d8b1002cff73d8b10014fe73d8b1002ede73d8b10014de73d8b10004fd73d8b1002edd73d8b10004dd73d8b1002cfc73d8b1008cfd72d8b1002ef671d8b1002eef21d8b1002ef970d8b1000cff7658b1002eec6258b10004ff7558b1001cfe7558b1001cfc7558b10004ff7458b1005cfc7458b10004ff7358b10014fe7358b10004fd7358b10014fc7358b1002eef7258b1008eee4258b1002eee2158b1002eec2158b1008eef2058b10004ff7654b1002cfe7654b10004fd7654b1002cfc7654b10005fb7054b10005f87054b1005cff76d0b1002cfe76d0b10004fd76d0b1002cfc76d0b10055de73d0b10005dd73d0b10004ff7650b1002cfe7650b10004fd7650b1002cfc7650b1000eee6250b10006ed6250b10044ff765471002f745154710034ff764871002eef624871002eec6248710074fd76943100067f659431001e7c65943100977b509431001cff765431002cfc765431001e7e65543100067d6554310005f7715431002df471543100957e75d03100057d75d031005ebe64d0310006bd64d031002df671d0310005f571d0310006bf649031005ebc649031005cff765031005ebe6450310006bd6450310005f7715031002df47150310006bf641031005ebc6410310055de7310310005dd7310310007b94010310064fd768831000cff764831002cfc76483100057f75483100957c7548310005df7348310055dc734831000eee6248310006ed6248310005f7714831002df47148310084fd75d961005cfe74d9610004fd74d96100867f54d9610024ff73d9610014fe73d9610004fd73d9610024fc73d96100867f53d96100067d53d961000cfe72d9610004fd72d9610024fc72d9610026f571d96100867c51d9610026fa70d961001cff76596100267c65596100267f7559610004ff745961005cfc7459610004ff7359610014fe7359610004fd7359610014fc7359610004ff725961000cfe725961000cfc72596100867f52596100867f51596100267e50596100267c505961001cfe75d9210004fd75d9210024fc75d9210024ff73d9210014fe73d9210004fd73d9210024fc73d921000cfe72d9210004fd72d9210024fc72d9210026f571d9210026fa70d9210004fd76992100857e75992100057d7599210026bf6499210026bc649921005cff7659210026bc6459210004ff755921001cfe755921001cfc7559210026bf7459210004ff7359210014fe7359210004fd7359210014fc7359210006bf4359210006b
  | 8 => 0xcfe76d012000cfc76d01200a57e75d01200057d75d01200067f65d01201167c65d0120006bf64d012005ebc64d0120006df63d012010edc63d012000dee72d0120005ed72d012000dfa76d0120106fa76d012000cfa76d01202377a75d01202377975d01200077b65d01200077865d0120236fb64d0120007bb64d0120236f964d0120237b864d0120235fb73d0120295f973d0120007db63d012028fd863d0120237bb43d012028fb943d012000dfa72d0120107ea72d0120237e972d012000df872d0120106fb62d0120107ea52d0120007e952d0120005f971d0120107eb21d0120007e921d01200bcfe76901200067f65901200fe7c6590120006df63901200d6dc63901200bdfa709012005cff765012000cfe76501200dcfd765012000cfc76501200067f65501200ee7c6550120006bf645012005ebc6450120006df63501200e6dc6350120005ef725012000dec72501200f4fe76101200067f65101200ce7c651012009dde7310120005dd7310120006df63101200c6dc63101200f5fa7610120236fa76101200077b6510120007786510120105fa7410120237ba7410120236fb6410120236f96410120235fb7310120237da7310120285f97310120237d97310120005d97310120007db631012027fd8631012000dfa721012000df87210120026fb62101200bfea5210120007e95210120005f97110120007ba4110120237b841101200bfeb2110120007e92110120025ef7588120005ed75881200076f65881200076c6588120007cf6388120277cc6388120005ed7188120025ee7088120027ea7088120026ef608812000feb6088120007eb4088120027e84088120027ea3088120277e93088120094fd75d971005cfe74d9710004fd74d971002cff73d9710014fe73d9710004fd73d971002cfc73d971000cfe72d9710004fd72d971002cfc72d971002ef671d971002ef970d97100967c50d971001cff765971002e7c655971002e7f7559710004ff745971005cfc74597100967f5459710004ff7359710014fe7359710004fd7359710014fc73597100967f53597100067d5359710004ff725971000cfe725971000cfc72597100067e52597100967c525971002e7e515971002e7c51597100967f505971001cfe75d9310004fd75d931002cfc75d931002cff73d9310014fe73d9310004fd73d931002cfc73d9310006bf43d9310006bd43d931000cfe72d9310004fd72d931002cfc72d931002ef671d931002ef970d9310004fd769931002ebf649931002ebc649931005cff765931002ebc6459310004ff755931001cfe755931001cfc755931002ebf7459310004ff7359310014fe7359310004fd7359310014fc7359310004ff725931000cfe725931000cfc725931002ebe415931002ebc415931005cff769531002cfe769
  | 9 => 0x8705492000eef605492000feb60549202afea30549202afe930549200067f65d85200067c65d8520006df63d8520006dc63d852001cfe75d8520004fd75d852001cfc75d852005cfe74d8520004fd74d8520004ff73d8520014fe73d8520004fd73d8520014fc73d852007ef621d852007ef521d85200a57e75985200057d75985200067f65985200067c659852009dde7398520005dd7398520006df6398520006dc6398520006f76198520065f970985200057f75585200a57c75585200067f65585200067c6558520005bf7458520005bc7458520005df735852009ddc7358520006df6358520006dc635852008dfb70585200067f65185200067c6518520006df6318520006dc6318520006f5611852001cfe7518520004fd751852002cfc751852005cfe7418520004fd741852002cff7318520014fe7318520004fd731852002cfc731852002eef211852002ef62118520036f5211852002ef97018520004fe7694520004fd769452002cfc76945200067f659452001e7c6594520006df63945201d6dc639452000dee7294520005ed72945200076d5294520005fa7094520005f97094520004ff7654520004fe7654520004fc76545200067f655452001e7c6554520006df63545201c6dc635452000dee7254520004fe76d0520004fd76d052005cfc76d05200067f65d05201b67c65d0520006df63d05201aedc63d0520006f761d0520006f461d0520004fe7690520004fd769052002cfc76905200067f659052019e7c6590520006bf649052005ebc6490520006df6390520176dc639052000dee7290520005ed7290520005fa7090520005f97090520004ff7650520004fe7650520004fc76505200067f655052018e7c6550520006df6350520186dc6350520005fb7050520005f87050520004fe7610520004fd761052002cfc76105200a57e75105200057d75105200067f651052016e7c6510520006bf641052005ebc641052009dde7310520005dd7310520006df6310520166dc631052000dee7210520005ed7210520006f7611052002ef46110520005fa7010520005f97010520005ef7548520005ed75485200076f65485200076c6548520006ef6448520006ed6448520007cf63485202a7cc634852000def714852000fe77148520007e7614852002eec6148520007e461485202a7e631485202a7e53148520007eb7048520025ec7048520007e8704852000eef604852000feb60485202a7ea30485202a7e9304852029cfe769412012e7f659412001e7c6594120006df6394120136dc6394120025ec729412012f6e52941200a77b5094120027e8209412001cff765412000cfe765412011cfd765412000cfc76541200067f655412001e7c6554120006df6354120126dc6354120005ef725412000dec725412011fe82054120
  | 10 => 0x9120004ff73d9120014fe73d9120004fd73d9120014fc73d9120024ff72d912000cfe72d91200f4fd72d912000cfc72d91200f6bf42d91200f6bd42d912002cfe71d9120004fd71d91200f6ef21d91200f6f970d91200a57e75991200057d75991200067f65991200067c6599120006bf649912009dde7399120005dd7399120006dc63991200ddf970991200057f75591200a57c75591200067f65591200067c6559120005df735912009ddc7359120006dc6359120005f77159120005f47159120105fb7059120004ff75591200067f75591200047f755912001cfe755912001cfc75591200067c755912001c7c7559120006bf7459120004ff7359120006df7359120004df7359120014fe7359120004fd7359120014fc7359120006dc7359120014dc7359120006bf4359120006bd43591200dcff7259120006ef7259120004ff7159120006f77159120004f7715912002cfc7159120006f47159120004f471591200deef2159120104ff7059120006fb70591200f4fe76191200067f65191200067c651912005ebe6419120006bd6419120006dc631912005cff7695120004fe7695120004fd769512005cfc76951200067f659512001e7c65951200a73f549512021edc6395120004ff7655120004fe7655120004fd7655120004fc76551200067f655512001e7c655512020edc6355120005fb7055120005f870551202bdde76d8d2009ede76d8d20014de76d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006dd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d20006de64d8d20006dd64d8d20006dc64d8d202b7ce52d8d202b7cf21d8d202b7db70d8d202b7d870d8d202b7db20d8d202b7cc20d8d202b7d820d8d20006df75d8d20006de75d8d20006dd75d8d20006dc75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d202b6df72d8d202b6de72d8d202b6dd72d8d202b6dc72d8d202b6df52d8d202b6de52d8d202b6dd52d8d202b6dc52d8d202b6df42d8d202b6de42d8d202b6dd42d8d202b6dc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df51d8d20006dc51d8d202b6df21d8d202b6de21d8d202b6dd21d8d202b6dc21d8d202b6df70d8d2009ede70d8d202b6dd70d8d202b6dc70d8d20006df50d8d20006dc50d8d202b6df20d8d202b6de20d8d202b6dd20d8d202b6dc20d8d200a5ec765492001eec765492001cec765492000def755492000f6f75549200076f655492001eee655492001eec65549200a76c65549200a76f54549200076d5454920007cf63549202afcc63549200a76f53549202af6d5354920005ef71549200a76c5154920007eb7054920025ec7054920007e
  | 11 => 0x246f976d02202477a75d02202477975d0220246fb64d0220246f964d0220245fb73d02202ddf973d0220247bb43d02202d7b943d022000dfa72d022000df872d0220005f971d0220104ff7650220025f97610220026f9761022000cf97610220027ba7410220026fb6410220027ba6410220246f96410220027b96410220025fb7310220027da73102202cdf97310220027d97310220005d9731022000dfa7210220027ea7210220027e97210220025f87210220005f97110220007ba4110220247b8411022001cfe76d95200a67e65d9520006dc63d952005cfe74d9520004fd74d95200a67f54d95200a67c54d9520004ff73d9520014fe73d9520004fd73d9520014fc73d95200a67f53d95200067e53d95200067d53d95200a67c53d9520024ff72d952000cfe72d952012cfd72d952000cfc72d952012e7f52d952012e7d52d952002cfe71d9520004fd71d95200a67f51d95200a67c51d952000cfd70d95200a67f50d952029d7e76d952001c7e76d95200067f63d95200067e63d95200067d63d95200067c63d95200075c63d95200065c63d95200076f72d952012f6c72d952012f6f21d95200077a30d95200077930d952012f7b20d952012f6c20d952012f7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d952012e7f72d952012e7e72d952012e7d72d952012e7c72d952012e7f42d952012e7e42d952012e7d42d952012e7c42d952012e7f32d952012e7e32d952012e7d32d952012e7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067e31d95200067d31d95200067c31d952012e7f21d952012e7e21d952012e7d21d952012e7c21d952012e7f70d95200a67e70d952012e7d70d95200067f30d95200067e30d95200067d30d95200067c30d952012e7f20d952012e7e20d952012e7c20d95200a67c6559520005df735952009ddc7359520006dc63595202c5fb705952012cff75595200067f7559520004ff745952005cfc7459520004ff7359520006df7359520004df7359520014fe7359520004fd7359520014fc7359520006dc7359520014dc735952011cff7259520006ef7259520004ff715952002cfc71595202c4ff7059520006fb705952012d7e76195200a67e761952012c7e76195200067f63195200067e63195200067d63195200067c63195200075c63195200065c631952029f6e72195200a76d721952029e7f621952029f6f211952029e7f60195200077a301952000779301952029f7b201952029f6c201952029f78201952005cfe76d91200067f65d91200067c65d9120006dc63d912001cfe75d9120004fd75d912001cfc75d
  | 12 => 0xa5050040007b95050040027ba30500402e7b9305004011cfd75d962005cfe74d9620004fd74d96200b67f54d9620024ff73d9620014fe73d9620004fd73d9620024fc73d96200b67f53d96200067d53d9620026ed72d962012e7e52d962012e7c52d962002cfe71d9620004fd71d96200b67c51d9620024fe70d9620026fa70d9620026ef20d962001cff76596200267c65596200267f7559620004ff745962005cfc7459620004ff7359620014fe7359620004fd7359620014fc735962011e7f525962011e7d5259620004ff715962002cfc7159620024fe7059620024fc70596200267e50596200267c505962011eef205962001cfe75d9220004fd75d9220024fc75d9220024ff73d9220014fe73d9220004fd73d9220024fc73d9220026ed72d922002cfe71d9220004fd71d9220024fe70d9220026fa70d92200dcfd76992200b57e75992200057d7599220026bf6499220026bc649922005cff7659220026bc6459220004ff755922001cfe755922001cfc7559220026bf7459220004ff7359220014fe7359220004fd7359220014fc7359220006bf4359220006bd43592200debf42592200debd4259220004ff715922002cfc7159220024fe7059220024fc70592200def87059220026be4059220026bc405922005cff7695220024fe7695220004fd7695220024fc76952200b73f5495220004ff7655220024fe7655220004fd7655220024fc76552200067f655522001e7c6555220005fb7055220025f87055220026f7619862001cfe7598620004fd759862002cfc759862005cfe7498620004fd749862002cff7398620014fe7398620004fd739862002cfc739862002ef6219862008ef52198620024fe709862002efa7098620024fc7098620026f61098620026f410986200057f75586200b57c7558620026f46158620004ff75586200067f75586200047f755862001cfe755862001cfc75586200067c755862001c7c7558620004ff745862005cfc7458620004ff7358620014fe7358620004fd7358620014fc7358620066f62158620066f52158620024fc7058620066ef2058620026f61058620026f4105862002cff7694620024fe7694620004fd76946200067f659462001e7c6594620025fa7094620005f97094620004ff7654620004fd7654620024fc765462005cff76d0620024fe76d0620004fd76d062002cff7690620024fe7690620004fd7690620025fa7090620005f97090620004ff7650620004fd7650620024fc7650620005fb7050620025f8705062002cff7610620024fe7610620004fd76106200b57e75106200057d75106200adde7310620005dd731062000dee7210620005ed7210620025fa7010620005f970106202c4ff765422011feb20542200dcfd76d02200b57e75d02200057d75d02200ddf976d0220
  | 13 => 0x8c4005edc5458c40006df7258c40006de7258c40006dd7258c40006dc7258c40006df5258c40006de5258c40006dc5258c4005edf4258c4005ede4258c4005edd4258c4005edc4258c40006df7158c40006de7158c40006dd7158c40006dc7158c40006df5158c40006dc5158c4005edf4158c4005ede4158c4005edd4158c4005edc4158c4005e9c4158c40006df2158c40006dc2158c400c6df7058c40026de7058c400c6dd7058c40026dc7058c40006df5058c40026de5058c40026dc5058c4005edf4058c4005e9f4058c40026de4058c4005edd4058c40026dc4058c40006df2058c40026de2058c40026dc2058c40026de1058c40026dc1058c40004ff755884001cfe755884001cfc755884000cfd7458840004ff7358840014fe7358840004fd7358840014fc7358840024ff7258840026ef72588400beee525884005eef425884005eec4258840004ff715884002cfc71588400beef2158840026ee2058840026ec2058840004ff7654840004fd7654840024fc765484001e7e65548400067d65548401fede6354840006dd635484000eee6254840006ed625484001cfe7598440004fd759844002cfc759844002cff7398440014fe7398440004fd739844002cfc739844000cfe7298440004fd729844002cfc7298440024fe7198440026f6719844005ef7419844002ef44198440026f61098440026f41098440004ff755844001cfe755844001cfc7558440004ff7358440014fe7358440004fd7358440014fc7358440004ff725844000cfe725844000cfc7258440026f7715844005ef7415844005ebc415844005ef4415844005efa405844005ef94058440026f61058440026f4105844002cff7694440024fe7694440004fd76944401d6de6394440006dd639444002ef66194440006f56194440004ff7654440004fd7654440024fc765444001e7e65544400067d6554440005bf745444005dbc74544401c6de6354440006dd6354440006f66154440006f56154440005fb7054440025f8705444005dbd7690440006bd769044005ebf639044005f9e63904402f6bd639044005f9d63904400069d639044005dbe719044005fb67190440006bd6190440005bd70904402eebe609044005fba609044002cff7688440024fe7688440004fd768844014ede6388440006dd638844002ef66188440006f56188440004ff7648440004fd7648440024fc7648440005bf744844005dbc744844013ede6348440006dd634844000eee6248440006ed6248440006f66148440006f561484400fcff7654040126de6354040006dd6354040025bf7650040006bf7650040004bf7650040026bf63500400279e63500402e6bd63500400279d63500400069d6350040005bc7150040025bf705004005fbb7050040026be6050040027ba6050040027b
  | 14 => 0x114ff7059540006fb70595400ee7c505954001cfc76551400067f655514001e7c6555140005fb7055140005f8705514005fb8405514000cfe76d89400deee62d894001cfe75d8940004fd75d894001cfc75d894000cfc74d8940004ff73d8940014fe73d8940004fd73d8940014fc73d8940006bf43d8940006bd43d89400deee42d894002cfe71d8940004fd71d894005cfd70d8940246fb40d8940246f840d89400deef20d89400057f75589400ed7c7558940005df73589400e5dc73589400deec6258940005f77158940005f47158940004ff7654940004fe7654940004fc7654940005fb7054940005f8705494000cfc7650940006ef625094000eec6250940005fb7050940005f8705094001cfe75d8540004fd75d854001cfc75d8540004ff73d8540014fe73d8540004fd73d8540014fc73d854000cfe72d8540004fd72d854000cfc72d8540006f751d8540006f451d8540006f631d8540006f531d8540006f721d8540006f421d8540006f761985400057f75585400ed7c75585400ddee7218540005ed7218540006f5611854001cfe7518540004fd751854002cfc751854002cff7318540014fe7318540004fd731854002cfc7318540006bf4318540006bd431854000cfe721854002eee721854000cee7218540004fd721854002eed7218540004ed721854002cfc7218540006f7511854002ef4511854002ef63118540006f53118540006f7211854002ef4211854002ef97018540004fe7694540004fd769454002cfc76945400067f659454001e7c6594540005fa7094540005f97094540004ff7654540004fe7654540004fc7654540006f7619054002ef46190540005fa7090540005f9709054005fb84090540006f76150540006f46150540005fb7050540005f87050540004fe7688540004fd768854002cfc7688540005fa7088540005f97088540004ff7648540004fe7648540004fc764854000eee6248540114fe769414001e7e65941400067d65941400ef7b509414001cff76541400ecfd765414005cfc76541400067f655414001e7c6554140005bf745414005dbc745414005dfa709014005efb6090140025bf73901402fdbd7390140006bc6190140025be7090140026bf609014005fbb6090140024ff75594400267f755944005cff745944005cfe745944005cfd745944005cfc745944005e7e545944005e7c5459440004ff7359440014fe7359440004fd7359440014fc7359440004ff725944000cfe725944000cfc72594400ce7f5259440004ff715944002cfc71594400ce7f5159440024fe7059440024fc70594400267e50594400267c5059440006df7558c40006de7558c40006dd7558c40006dc7558c4005edf7458c4005ede7458c4005edd7458c4005edc7458c4005edf5458c4005ede5458c4005edd545
  | 15 => 0xf7358a40004df7358a40014fe7358a40004fd7358a40014fc7358a40006dc7358a40014dc7358a400f6ee5258a400f6ee4258a40006ef3258a400f6ec3258a40004ff7158a4002cfc7158a400f6ef2158a40024fc7058a40236fb4058a40236f84058a40026ee2058a40026ec2058a40004ff7654a40004fd7654a40024fc7654a4000eee6254a40006ed6254a40005fb7054a40025f87054a4000cff7650a4000eee6250a40006ed6250a40005fb7050a40025f87050a40026f7619864001cfe7598640004fd759864002cfc759864002cff7398640014fe7398640004fd739864002cfc739864000cfe7298640004fd729864002cfc7298640024fe709864002efa7098640026f61098640026f41098640026f46158640004ff755864001cfe755864001cfc7558640004ff7358640014fe7358640004fd7358640014fc7358640004ff725864000cfe725864000cfc7258640024fc7058640026f61058640026f4105864002cff7694640024fe7694640004fd7694640025fa7094640005f97094640004ff7654640004fd7654640024fc7654640005bf745464005dbc745464002ef66190640006f56190640025fa7090640005f970906402eebf63906402eebd639064005dbe7190640007b66190640006bd6190640007b56190640007ba7090640005bd7090640007b9709064005ebe6090640006f66150640006f5615064005fb44150640005fb7050640025f87050640005bd761064005ebd761064005f3e751064005f3d751064005f9e731064005f9d731064030ebf631064030ebd631064005fae721064005fad721064005fb67110640006bd611064005fba7010640005bd701064005fb97010640005b9701064005fba601064002cff7688640024fe7688640004fd7688640025fa7088640005f97088640004ff7648640004fd7648640024fc7648640005bf744864005dbc744864000eee6248640006ed62486400ccff7654240025bd76d024005ebd76d024005f3e75d024005f3d75d0240026bf63d0240306bd63d0240005be71d0240027ba60d0240027ba50d0240007b950d024001cfe76d95400ee7e65d954005cfe74d95400ecfd74d954005cfc74d95400ee7f54d9540004ff73d9540014fe73d9540004fd73d9540014fc73d95400ee7f53d95400067d53d954000cfe72d9540004fd72d954000cfc72d95400067e52d95400ee7c52d954002cfe71d9540004fd71d95400ee7c51d954005cfd70d95400ee7f50d95400ee7c6559540005f77159540005f471595400ecff75595400067f75595400fcff7459540006bf7459540004ff7359540014fe7359540004fd7359540014fc7359540004ff725954000cfe725954000cfc7259540004ff7159540006f77159540004f7715954002cfc7159540006f47159540004f47159540
  | 16 => 0x974005e7c43597400067f72597400067e72597400067d72597400067c725974005e7f425974005e7e425974005e7d425974005e7c42597400067f32597400067e32597400067d32597400067c32597400067f71597400067e71597400067d71597400067c715974005e7f415974005e7e415974005e7d415974005e7c41597400067f31597400067e31597400067d31597400067c31597400067f21597400067c21597400067f70597400067d70597401167c705974005e7f405974005e7e405974005e7d405974005e7c40597400067f30597400067e30597400067d30597400067c30597400067f20597400067c2059740004ff7558b4001cfe7558b4001cfc7558b40004ff7358b40014fe7358b40004fd7358b40014fc7358b4005ebf4358b40006bd4358b4005eef7258b4005eef4258b4005eec4258b40006ef3258b40106ec3258b40004ff7158b4002cfc7158b40106ef2158b40106ef2058b40004ff7654b40004fd7654b4005cfc7654b4001e7e6554b400067d6554b4001cfe7598740004fd759874002cfc759874002cff7398740014fe7398740004fd739874002cfc739874005ebf4398740006bd439874000cfe7298740004fd729874002cfc729874002ef6719874005ef7419874002ef4419874005ebc4098740004ff755874001cfe755874001cfc7558740004ff7358740014fe7358740004fd7358740014fc7358740004ff725874000cfe725874000cfc725874005ef7715874005ef7415874005ef4415874005efa405874005ef9405874002cff769474005cfe7694740004fd769474001e7e65947400067d6594740004ff7654740004fd765474005cfc765474001e7e65547400067d6554740005fb7054740005f8705474002cff768874005cfe7688740004fd76887401567e65887400067d6588740004ff7648740004fd764874005cfc76487401467e65487400067d654874000eee6248740006ed62487400ecfd769434001e7e65943400067d659434001cff765434005cfc765434001e7e65543400067d6554340005bf745434005dbc74543400fcfd75d9640026bd74d9640024ff73d9640014fe73d9640004fd73d9640024fc73d964000cfe72d9640004fd72d9640024fc72d964002cfe71d9640004fd71d9640026fa70d964001cff76596400267c65596400267f75596400fe7f5459640004ff7359640014fe7359640004fd7359640014fc7359640004ff725964000cfe725964000cfc7259640004ff715964002cfc7159640024fc70596400267e50596400267c505964001cff7655240024fc765524001e7e65552400067d6555240005fb7055240025f8705524005fbb405524000cff7658a40005df7358a400d5dc7358a40026ec6258a40004ff7558a4001cfe7558a4001cfc7558a40004ff7358a40006d
  | 17 => 0x2cff7688650024fe7688650004fd768865001d7e75886500057d758865002ef66188650006f56188650004ff7648650004fd7648650024fc76486500057f754865001d7c754865000eee6248650006ed6248650006f66148650006f561486500febe54d91500febd54d9150004ff73d9150014fe73d9150004fd73d9150014fc73d915000cfe72d9150004fd72d915000cfc72d915002cfe71d9150004fd71d91500fe7c50d9150006bf64991500edf97099150005f77159150005f47159150115fb705915005ebe6419150006bd641915000cfe76d895011eee62d895000cfc75d895005cfe74d8950004fd74d8950004ff73d8950014fe73d8950004fd73d8950014fc73d895011eee52d89500b6ed52d8950006ef32d895011eec32d895002cfe71d8950004fd71d895001cfd70d895011eef20d8950005df7358950125dc735895011eec625895031dfb7058950004fe76d0950004fd76d095005cfc76d0950125de73d0950005dd73d0950004ff7650950004fe7650950004fc765095005cfe74d8550004fd74d8550004ff73d8550014fe73d8550004fd73d8550014fc73d855000cfe72d8550004fd72d855000cfc72d8550086f651d8550086f551d8550006f76198550075f97098550005bf7458550005bc7458550095fb7058550006f5611855005cfe7418550004fd741855002cff7318550014fe7318550004fd731855002cfc731855000cfe7218550004fd721855002cfc721855002ef65118550046f551185500467c5018550004fe76d0550004fd76d055005cfc76d0550006f761d0550006f461d0550004fe7690550004fd769055002cfc7690550006bf649055005ebc6490550004ff7650550004fe7650550004fc7650550004fe7610550004fd761055002cfc761055001d7e75105500057d7510550006bf641055005ebc6410550125de7310550005dd731055011dee7210550005ed7210550006f7611055002ef46110550005fa7010550005f97010550004fe7688550004fd768855002cfc7688550004ff7648550004fe7648550004fc76485500067f64941503167f63941503167d639415012e7e629415012e7c62941500067c61941500257e70941500277a70941500267f609415001f7b609415005e7f755974005cfc745974005e7e545974005e7c5459740004ff7359740014fe7359740004fd7359740014fc73597401167f53597400067e53597400067d53597401167c5359740004ff725974000cfe725974000cfc72597401167f52597400067e52597401167c5259740004ff715974002cfc71597401167f51597401167c51597401167f505974005e7f745974005e7e745974005e7d745974005e7c74597400067f73597400067e73597400067d73597400067c735974005e7f435974005e7e435974005e7d435
  | 18 => 0xc7458121005df735812113ddc7358121006f9601812101cfe7518121004fd7518121024fc751812105cfe7418121004fd7418121024ff7318121014fe7318121004fd7318121024fc7318121006fb5018121026f85018121026ef2018121026fa2018121036f92018121026bf6499250026bc6499250026bc64592500eebe54592500eebd5459250004ff7359250014fe7359250004fd7359250014fc7359250006bf4359250006bd4359250004ff725925000cfe725925000cfc7259250004ff715925002cfc7159250024fc7059250026be4059250026bc405925005c7f765525001d7f745525001f3f745525005e7e64552500073e64552500073d645525005e7c645525032d7f735525032d7d735525012d7e725525012d7c72552500057c71552500057f70552500077b705525000778705525001e7e605525001f7a605525000cff7658a5001d7c7558a50026ec6258a5012f6e5258a50004ff7458a5005cfc7458a500a67f5458a500067d5458a50004ff7358a50014fe7358a50004fd7358a50014fc7358a500a67f5358a500067d5358a5012e7e5258a5012eee5258a5012e6e5258a500a6ed5258a5012e7c5258a50004ff7158a5002cfc7158a500a67c5158a5012eef2158a50024fe7058a50024fc7058a50026ee2058a50026ec2058a5005cff76d0a50024fe76d0a50004fd76d0a5001d7e75d0a500057d75d0a50135de73d0a50005dd73d0a50004ff7650a50004fd7650a50024fc7650a500057f7550a5001d7c7550a50026f7619865005cfe7498650004fd749865002cff7398650014fe7398650004fd739865002cfc739865000cfe7298650004fd729865002cfc729865002ef65198650096f55198650024fe7098650024fc7098650026f61098650026f41098650026f46158650004ff745865005cfc74586500767f54586500067d5458650004ff7358650014fe7358650004fd7358650014fc73586500767f53586500067d5358650004ff725865000cfe725865000cfc7258650076f65158650076f551586500767c5158650024fc7058650026f61058650026f410586500057d74946503257f73946503257d739465012d7e729465012d7c72946500067d629465001d7e719465001f7671946500077661946500067d61946500077561946500077a70946500057d709465000779709465001e7e609465001f7a609465005cff76d0650024fe76d0650004fd76d065001d7e75d06500057d75d065002cff7690650024fe7690650004fd76906500057f759065001d7c7590650004ff7650650004fd7650650024fc76506500057f755065001d7c755065002cff7610650024fe7610650004fd761065001d7e75106500057d7510650135de7310650005dd731065012dee7210650005ed7210650025fa7010650005f97010650
  | 19 => 0x9521005fb7059521005f870595211ccff75595210067f7559521004ff7459521006bf7459521004bf745952105cfc7459521006bc745952105cbc74595211467f5459521004ff7359521006df7359521004df7359521014fe7359521004fd7359521014fc7359521006dc7359521014dc73595211467f53595210067d53595211bcff7259521006ef725952134cff7159521006f771595211467c5159521004ff7059521006fb7059521004fb7059521024fc7059521006f87059521004f870595211beef205952105cfe76d912101cfe75d9121004fd75d912101cfc75d9121006bf54d9121006bc54d9121004ff73d9121014fe73d9121004fd73d9121014fc73d9121006bf43d9121006bd43d912102cff72d9121194fd72d9121196bf42d9121196bd42d9121024fe70d9121004fd70d9121006bf649912113dde7399121005dd739912117df571991211a5f77159121004ff755912101cfe755912101cfc7559121006bf7459121004ff7359121014fe7359121004fd7359121014fc735912117cff7259121006ef72591211a4ff7159121006f77159121004ff7059121024fc7059121194fe76191211457e75191210057d751912105ebe6419121006bd641912105cff7695121004fe7695121004fd769512105cfc76951211473f549512100dee7295121005ed7295121004ff7655121004fe7655121004fd7655121004fc765512101e7e65551210067d6555121005f77155121005f4715512105eec765092105cec765092100def745092100faf7450921007af645092105eee645092105eec6450921007ac6450921347af4350921347ad4350921007e7715092102dec7150921007e4715092100eef615092100fe76150921347e63150921347e53150921005ef705092133cfe769452101e7e65945210067d659452114777519452101cff765452100cfe76545211bcfd765452100cfc76545210067f655452101e7c6554521005ef725452100dec725452100cfe76d052100cfc76d0521006bf64d052105ebc64d052100dee72d0521005ed72d052115cfe769052102dec729052105cff765052100cfe765052117cfd765052100cfc7650521006bf645052105ebc6450521005ef725052100dec7250521194fe76105211457e75105210057d751052113dde7310521005dd731052100dee7210521005ed7210521005fa7010521005f9701052102def7488521005ed748852102dee718852102fe6718852102eef618852100fe7618852102fe63188521337e53188521005ed708852101cfe75d8121004fd75d812101cfc75d812105cfe74d8121004fd74d8121004ff73d8121014fe73d8121004fd73d8121014fc73d8121006fb50d8121006f850d812108efa20d8121006fb60981210057f75581211457c7558121005bf7458121005b
  | 20 => 0x6f97258041006f87258041006fb5258041006fa5258041006f95258041006f8525804105efb425804105efa425804105ef9425804105ef84258041006fb3258041006fa3258041006f93258041006f8325804102efa7158041006fb515804102efa5158041006f9515804102ef8515804105efb415804102efa415804105ef9415804102ef84158041006fb315804102efa3158041006f9315804102ef83158041006fb215804102efa215804102ef821580411bcfd75d962105cfe74d9621004fd74d962102cff73d9621014fe73d9621004fd73d962102cfc73d962102eed72d962102cfe71d962102ef671d9621024fe70d9621004fd70d962101cff765962102e7c655962102e7f7559621004ff745962105cfc74596211567f5459621004ff7359621014fe7359621004fd7359621014fc73596211567f53596210067d53596211be7f52596211be7d525962102cfe715962102cfc715962102e7e515962102e7c5159621004ff7059621024fc70596211567c505962101cfe75d9221004fd75d922102cfc75d922102cff73d9221014fe73d9221004fd73d922102cfc73d9221006bf43d9221006bd43d922102eed72d922102cfe71d922102ef671d922102eef21d9221024fe70d9221004fd70d922117cfd769922102ebf649922102ebc649922105cff765922102ebc6459221004ff755922101cfe755922101cfc755922102ebf7459221004ff7359221014fe7359221004fd7359221014fc735922117ebf425922117ebd425922102cfe715922102cfc715922102ebe415922102ebc415922117eef2159221004ff7059221024fc705922105cff769522102cfe7695221004fd769522102cfc76952211573f5495221004ff765522102cfe7655221004fd765522102cfc765522101e7e65552210067d6555221005f7715522102df4715522134cff76546211bfe7215462117cfd76d06211a4ff765062102efb609822101cfe7598221004fd7598221024fc759822105cfe7498221004fd7498221024ff7398221014fe7398221004fd7398221024fc739822102cfe7198221026fa209822107ef9209822102efb1098221026f8109822102ef86058221004ff755822101cfe755822101cfc7558221004ff745822105cfc7458221004ff7358221014fe7358221004fd7358221014fc735822102cfc7158221066ef2158221066fa205822102efb105822102ef8105822101cfe76d95211467e65d952105cfe74d9521004fd74d9521004ff73d9521014fe73d9521004fd73d9521014fc73d952102cff72d95211ccfd72d95211ce7f52d95211ce7d52d952100cfd71d95211467f51d9521024fe70d9521004fd70d95211467c50d95211ceef20d95211467c6559521005bf7459521005bc7459521005df735952113ddc735952134df7715
  | 21 => 0xc1058841004ff7654841004fd765484102cfc765484101e7e65548410067d6554841005bf745484105dbc74548411fede6354841006dd635484100eee6254841006ed625484119cff765444101e7e65544410067d65544411c6de6354441006dd63544411beee6254441006ed625444102f74515444102dbf7650441006bf7650441004bf765044102f3e655044102f3d6550441355bf7350441355bd735044102f9e635044102f9d635044102fae625044102fad625044102dbf715044105fb7715044102ebe615044102fb6615044102fb65150441007b55150441005bc705044102fba605044102fb9605044101cfe7598041004fd7598041024fc7598041024ff7398041014fe7398041004fd7398041024fc739804100cfe7298041004fd7298041024fc7298041026fa7098041006fb5098041026f8509804105efb4098041026f84098041006fb3098041026fa3098041006f93098041026f83098041006fb2098041026f8209804102efb1098041026f81098041026fb7598041006fa7598041006f97598041026f8759804105efa749804105ef97498041026f8749804105efb549804105efa549804105ef9549804105ef85498041026fb7398041006fa7398041006f97398041026f87398041006fb5398041006fa5398041006f95398041006f8539804105efb439804105efa439804105ef9439804105ef84398041026fb7298041006fa7298041006f97298041026f87298041006fb5298041006fa5298041006f95298041006f8529804105efb429804105efa429804105ef9429804105ef84298041006fb3298041006fa3298041006f93298041006f83298041026f87198041006fb519804102efa5198041006f9519804102ef8519804105efb419804102efa419804105ef9419804102ef84198041006fb319804102efa3198041006f9319804102ef83198041006fb219804102efa219804102ef82198041004ff755804101cfe755804101cfc7558041004ff7358041014fe7358041004fd7358041014fc735804105ebf4358041006bd4358041004ff725804100cfe725804100cfc725804102efb7058041006fb5058041006f8505804105efb405804105ebc405804105ef84058041006fb3058041006fa3058041006f93058041006f83058041006fb2058041006f8205804102efb105804102ef81058041006fb7558041006fa7558041006f97558041006f8755804105efb745804105efa745804105ef8745804105efb545804105efa545804105ef9545804105ef85458041006fb7358041006fa7358041006f97358041006f87358041006fb5358041006fa5358041006f95358041006f8535804105efb435804105ebb435804105efa435804105ef94358041006b9435804105ef84358041006fb7258041006fa7258041
  | 22 => 0x94410067c725944105e7f425944105e7e425944105e7d425944105e7c42594410067f32594410067e32594410067d32594410067c325944116e7f715944102e7e715944102e7c715944105e7f415944102e7e415944105e7d415944102e7c41594410067f315944102e7e31594410067d315944102e7c31594410067f215944102e7e215944102e7c21594410067f70594410067e70594410067d70594410067c705944105e7f405944105e7e405944105e7d405944105e7c40594410067f30594410067e30594410067d30594410067c30594410067f20594410067c205944102e7f105944102e7c1059441006df7558c41006de7558c41006dd7558c41006dc7558c4105edf7458c4105ede7458c4105edd7458c4105edc7458c4105edf5458c4105ede5458c4105edd5458c4105edc5458c41006df7258c41006de7258c41006dd7258c41006dc7258c41006df5258c41006de5258c41006dc5258c4105edf4258c4105ede4258c4105edd4258c4105edc4258c41166df7158c4102ede7158c41166dd7158c4102edc7158c41006df5158c4102ede5158c4102edc5158c4105edf4158c4102ede4158c4105edd4158c4102edc4158c41006df2158c4102ede2158c4102edc2158c41006df7058c41006de7058c41006dd7058c41006dc7058c41006df5058c41006dc5058c4105edf4058c4105ede4058c4105edd4058c4105edc4058c41006df2058c41006dc2058c4102edf1058c4102edc1058c41004ff755884101cfe755884101cfc7558841004ff7358841014fe7358841004fd7358841014fc735884105ebf4358841006bd435884102cff725884102eef7258841006ef525884115eee525884115eec525884105eef425884105eec4258841006ef325884115eee3258841006ed325884115eec325884102eee215884102eec2158841004ff7058841024fc705884115eef205884115eec2058841006ef7558841006ee7558841006ed7558841006ec755884105eef745884105eee745884105eec745884105eef545884105eee545884105eed545884105eec5458841006ef7358841006ee7358841006ed7358841006ec7358841006ef5358841006ee5358841006ed5358841006ec535884105eef435884105eaf435884105eee435884105eed4358841006ad435884105eec435884115eef715884102eee715884102eec7158841006ef515884102eee515884102eec515884105eef415884102eee415884105eed415884102eec4158841006ef315884102eee3158841006ed315884102eec3158841006ef7058841006ee7058841006ed7058841006ec7058841006ef5058841006ec505884105eef405884105eee405884105eed405884105eec4058841006ef3058841006ee3058841006ed3058841006ec305884102eef105884102ee
  | 23 => 0xcfe725824100cfc725824102cfc715824102efb105824102ef8105824101cfe76d954118e7e65d954118cfd74d954118e7f54d9541004ff73d9541014fe73d9541004fd73d9541014fc73d95410067e53d954118e7c53d954100cfe72d9541004fd72d954100cfc72d954118e7f52d954105cfd71d954118e7f51d9541024fe70d9541004fd70d954118e7c50d954118e7c6559541005fb7059541005f8705954118cff75595410067f755954119cff7459541006bf7459541004ff7359541014fe7359541004fd7359541014fc7359541004ff725954100cfe725954100cfc72595411b4ff7159541006f77159541004ff7059541006fb7059541004fb7059541024fc7059541006f87059541004f8705954101cfc76551410067f655514101e7c6555141005f77155141005f4715514105fb4415514100cfe76d894117eee62d894101cfe75d8941004fd75d894101cfc75d8941004ff73d8941014fe73d8941004fd73d8941014fc73d894117eee42d8941006ef32d894117eec32d894105cfd71d894117eef21d8941024fe70d8941004fd70d894117eec6258941004ff7654941004fe7654941004fc76549410067f655494101e7c655494100cfc7650941006ef625094100eec6250941005f77150941005f471509411b4fe769454118f77519454101cff765454118cfd765454105cfc76545410067f655454101e7c6554541005bf745454105dbc745454105df6719054105ef7619054135ebf639054135ebd639054102dbe719054102ebf619054105fb7619054101cfe75d8141004fd75d814101cfc75d8141004ff73d8141014fe73d8141004fd73d8141014fc73d814100cfe72d8141004fd72d814100cfc72d8141006fb50d8141006f850d8141006fb30d8141006f830d8141006fb60981410057f755814118d7c7558141006f9601814101cfe7518141004fd7518141024fc7518141024ff7318141014fe7318141004fd7318141024fc731814100cfe7218141004fd7218141024fc7218141006be4118141006fb5018141026f85018141006fb3018141026f8301814102cff755944102e7f755944105cfe745944105cfc745944105e7e545944105e7c5459441004ff7359441014fe7359441004fd7359441014fc735944116e7f53594410067e53594410067d535944116e7c5359441004ff725944100cfe725944100cfc725944116e7f52594410067e525944116e7c525944102cfe715944102cfc715944102e7e515944102e7c5159441004ff7059441024fc705944116e7f505944116e7c505944105e7f745944105e7e745944105e7d745944105e7c74594410067f73594410067e73594410067d73594410067c735944105e7f435944105e7e435944105e7d435944105e7c43594410067f72594410067e72594410067d725
  | 24 => 0xc72597411b67f52597411b67f5159741004ff7059741024fc70597411b67c5059741004ff7558b4101cfe7558b4101cfc7558b41004ff7358b41014fe7358b41004fd7358b41014fc7358b4105eef7258b4105eef4258b4105eec4258b411a6ef2158b41004ff7058b41024fc7058b41004ff7654b41004fd7654b4105cfc7654b4101e7e6554b410067d6554b4118cfd769474101cff765474105cfc765474101e7e65547410067d6554741005bf745474105dbc74547411b774515474101cfe7598341004fd7598341024fc7598341024ff7398341014fe7398341004fd7398341024fc739834100cfe7298341004fd7298341024fc729834105ebc4198341026fa709834105efb4098341026f84098341004ff755834101cfe755834101cfc7558341004ff7358341014fe7358341004fd7358341014fc7358341004ff725834100cfe725834100cfc725834105efb705834105efb405834105ef8405834119cfd75d964102ebd74d964102cff73d9641014fe73d9641004fd73d964102cfc73d964100cfe72d9641004fd72d964102cfc72d964119e7f52d964102ef671d964102e7f51d9641024fe70d9641004fd70d964119e7c50d964101cff765964102e7c655964102e7f755964119e7f5459641004ff7359641014fe7359641004fd7359641014fc735964119e7f53596410067d5359641004ff725964100cfe725964100cfc725964102cfc715964102e7e515964102e7c5159641004ff7059641024fc705964101cff765524102cfc765524101e7e65552410067d6555241005f7715524102df4715524105fb7415524100cff7658a4102eec6258a41004ff7558a4101cfe7558a4101cfc7558a41004ff7358a41014fe7358a41004fd7358a41014fc7358a41006bf4358a41006bd4358a41196ee4258a4102cfc7158a4102eee2158a4102eec2158a41004ff7058a41024fc7058a41196ef2058a41004ff7654a41004fd7654a4102cfc7654a410067f6554a4101e7c6554a41005bf7454a4105dbc7454a4100cff7650a4100eee6250a41006ed6250a41005f77150a4102df47150a4116cff765464102e7f655464102e7c655464102dbd76d064105ebd76d064105dbf73d0641365bd73d064102fb661d064102fb651d0641007b551d0641005be70d064102efb609824101cfe7598241004fd7598241024fc7598241024ff7398241014fe7398241004fd7398241024fc739824100cfe7298241004fd7298241024fc729824102cfe719824102efb1098241026f810982410057f755824119d7c755824102ef86058241004ff75582410067f75582410047f755824101cfe755824101cfc75582410067c755824101c7c7558241004ff7358241014fe7358241004fd7358241014fc7358241006bf4358241006bd4358241004ff7258241
  | 25 => 0x825105cfe7498251004fd7498251024ff7398251014fe7398251004fd7398251024fc739825100cfe7298251004fd7298251024fc729825102cfe7198251026fa5098251086f95098251006fb3098251026f8309825102efb1098251026f8109825102ef86058251004ff745825105cfc7458251004ff7358251014fe7358251004fd7358251014fc7358251004ff725825100cfe725825100cfc725825102cfc7158251076fa50582510767c5058251006fb3058251006f8305825102efb105825102ef8105825119ebe54d915119ebd54d9151004ff73d9151014fe73d9151004fd73d9151014fc73d9151006bf43d9151006bd43d915100cfe72d9151004fd72d915100cfc72d9151006be42d9151006bc42d9151024fe70d9151004fd70d9151006bf649915118df571991511b5f77159151005fb7059151005f8705915105ebe6419151006bd641915105c7c765515101d7f745515101f3f74551510073f645515105e7e645515105e7c64551510073c645515137d7f735515137d7d735515100777715515102d7c715515100774715515100574715515101e7f615515101f77615515100cfe76d89511beee62d895105cfe74d8951004fd74d89511567f54d89510067d54d8951004ff73d8951014fe73d8951004fd73d8951014fc73d89511567f53d89510067d53d89511beee52d8951156ed52d895101cfd71d89511567c51d89511beef21d8951024fe70d8951004fd70d8951005bf7458951005bc7458951005df73589511c5dc73589511beec6258951375f77158951005fb7058951005f87058951004fe76d0951004fd76d095105cfc76d095101d7e75d09510057d75d09511c5de73d0951005dd73d0951004ff7650951004fe7650951004fc76509510057d749455102d7f739455136d7d73945510067f629455102d7e719455102f76719455102e7f619455101f77619455105cfe74d8151004fd74d8151004ff73d8151014fe73d8151004fd73d8151014fc73d815100cfe72d8151004fd72d815100cfc72d8151096fa50d8151006fa30d8151006f930d8151006fb20d8151006f820d8151006fb6098151005bf7458151005bc74581511bdee7218151005ed7218151006f9601815105cfe7418151004fd74181510467f54181510067d5418151024ff7318151014fe7318151004fd7318151024fc73181510467f53181510067d531815100cfe7218151026ee721815100cee7218151004fd7218151026ed7218151004ed7218151024fc72181510067e51181510467c5118151026fa5018151046f95018151026fa3018151006f93018151006fb2018151026f8201815105e7f755974105cfc745974105e7e545974105e7c5459741004ff7359741014fe7359741004fd7359741014fc7359741004ff725974100cfe725974100cf
  | 26 => 0x5cfd72d95422167f52d95422167d52d954202cfe71d9542004fd71d9542024fe70d9542004fd70d95421e67c50d95421e67c655954238dbf7459542214ff75595420067f755954238cff7459542006bf7459542004ff7359542014fe7359542004fd7359542014fc7359542204ff7259542006ef7259542004ff715954202cfc7159542004ff7059542024fc705954201cff765514200cfe7655142204fd765514200cfc76551420067f655514201e7c6555142005ef725514200dec725514205fac425514201cfe75d8542004fd75d854201cfc75d8542004ff73d8542014fe73d8542004fd73d8542014fc73d854205cfd72d85421a6f621d8542024fe70d8542004fd70d8542006f76198542006f56118542005fa7018542005f9701854201cfe7518542004fd751854202cfc751854202cff7318542014fe7318542004fd731854202cfc7318542006bf4318542006bd431854205cfd721854202eef211854202ef6211854215ef52118542024fe701854202efa7018542004fa7018542004fd701854202ef97018542004f9701854201cfe75d8142004fd75d814201cfc75d8142004ff73d8142014fe73d8142004fd73d8142014fc73d8142006bf43d8142006bd43d814205cfd72d814202cfe71d8142004fd71d8142106ef21d8142106fa20d8142006fb60981420057f75581421e57c7558142005df73581421dddc7358142005f77158142005f47158142006f9601814201cfe7518142004fd7518142024fc7518142024ff7318142014fe7318142004fd7318142024fc731814205cfd721814202cfe7118142004fd7118142026fa20181420bef9201814202ebf649925102ebc649925102ebc645925118ebe545925118ebd5459251004ff7359251014fe7359251004fd7359251014fc7359251004ff725925100cfe725925100cfc725925118e7f525925102cfc715925118e7f515925102ebe415925102ebc4159251004ff7059251024fc705925118e7c505925100cff7658a5102eec6258a51004ff7458a5105cfc7458a51004ff7358a51014fe7358a51004fd7358a51014fc7358a511ceee5258a51146ed5258a511ceee4258a51006ef3258a511ceec3258a5102cfe7158a5102cfc7158a5102eee2158a5102eec2158a51004ff7058a51024fc7058a511ceef2058a511cd7f7654a5100e7f7654a5100c7f7654a510067d6454a513867f6354a513867d6354a5101d7f7254a5101f6f7254a5100e7e6254a511cf6e6254a510076d6254a5100e7c6254a510057f7154a51007777154a51007747154a5101e7e6154a5101f766154a510057c7054a511cf6f2054a5105cff76d0a5102cfe76d0a51004fd76d0a511d5de73d0a51005dd73d0a51004ff7650a51004fd7650a5102cfc7650a5100eee6250a51006ed6250a5102efb609
  | 27 => 0xd741815239e7f54181520067d5418152024ff7318152014fe7318152004fd7318152024fc731815239e7f53181520067d531815201cfd7218152026ed721815229e7e521815229e7c521815202cfe7118152004fd711815239e7c5118152026fa501815239ef95018152006fb3018152026f83018152026ef2018152026fa201815229ef9201815205e7f755974200cfe745974200cfc745974205e7e545974205e7c5459742004ff7359742014fe7359742004fd7359742014fc73597422067f52597422067d5259742004ff715974202cfc71597421f67f5159742004ff7059742024fc70597421f67c5059742006df7558f42006de7558f42006dd7558f42006dc7558f4205edf7458f4205ede7458f4205edd7458f4205edc7458f4205edf5458f4205ede5458f4205edd5458f4205edc5458f42396df7258f42396de7258f42396dd7258f42396dc7258f42396df5258f42396de5258f42396dd5258f42396dc5258f4205edf4258f4205ede4258f4205edd4258f4205edc4258f42006df7158f42006de7158f42006dd7158f42006dc7158f42006df5158f42006dc5158f4205edf4158f4205ede4158f4205edd4158f4205edc4158f42396df2158f42396de2158f42396dd2158f42396dc2158f42006df7058f42006de7058f42006dd7058f42006dc7058f42006df5058f42006dc5058f4205edf4058f4205ede4058f4205edd4058f4205edc4058f42396df2058f42396de2058f42396dd2058f42396dc2058f4201cfe7598742004fd759874202cfc759874200cfe749874202cfc749874202cff7398742014fe7398742004fd739874202cfc739874205ebf4398742006bd439874202ef6719874205ef7419874202ef4419874202ef62198742196f52198742024fe7098742004fd7098742004ff755874201cfe755874201cfc755874200cfc7458742004ff7358742014fe7358742004fd7358742014fc735874205eee425874205eed425874205ef7715874205ef7415874205ef4415874217ef62158742004ff7058742024fc705874201cfe7598342004fd7598342024fc759834200cfe7498342024fc7498342024ff7398342014fe7398342004fd7398342024fc739834202cfe7198342004fd7198342026fa7098342006fb5098342026f8509834205efb4098342026f84098342026fa20983420f6f92098342004ff755834201cfe755834201cfc755834200cfc7458342004ff7358342014fe7358342004fd7358342014fc735834205ebf4358342006bd4358342004ff715834202cfc715834205efb7058342006fb5058342006f8505834205efb405834205ef840583420defa205834201cfe76d95421e67e65d954200cfd74d95421e67f54d9542004ff73d9542014fe73d9542004fd73d9542014fc73d954205cff72d9542
  | 28 => 0x855400cfe72d8554004fd72d855400cfc72d85541b6f651d8554006f731d8554006f431d8554024fe70d8554004fd70d8554006f76198554005fb7058554005f8705855420dde7318554005dd7318554006f5611855405cfd751855402cff7318554014fe731855402ede7318554014de7318554004fd731855402edd7318554004dd731855402cfc731855400cfe7218554004fd721855402cfc721855416e7f521855402e7f511855402ef6511855416ef55118554006f7311855402ef43118554024fe7018554004fd701855416e7c501855405cfd75d8154004ff73d8154014fe73d8154004fd73d8154014fc73d815400cfe72d8154004fd72d815400cfc72d815402cfe71d8154004fd71d8154116fa50d81541167c50d8154006fb30d8154006f830d8154006fb6098154005f77158154005f47158154006f9601815405cfd7518154024ff7318154014fe7318154004fd7318154024fc731815400cfe7218154004fd7218154024fc721815402cfe7118154004fd7118154026fa50181540cef95018154006fb3018154026f8301815405cfe76d915200cfd75d91523b6be54d91523b6bd54d9152004ff73d9152014fe73d9152004fd73d9152014fc73d915201cfd72d915238ebf42d915202cfe71d9152004fd71d9152024fe70d9152004fd70d9152006bf64991521fdde7399152005dd73991521e5ed7299152005fa7099152005f970991521f5ef725915205ebe6419152006bd641915200d7c765515205e7c765515200c7c765515201d7f745515201f3f74551520073f645515205e7e645515205e7c64551520073c64551523ad7f73551523ad7d73551520076f725515200d7e725515200d7c72551522076c725515201e7f625515201f6f62551520057c71551522076f205515200cfd75d855234e7d75d855205cfe74d8552004fd74d85523767f54d85520067d54d8552004ff73d8552014fe73d8552004fd73d8552014fc73d85523767f53d85520067d53d855201cfd72d8552376f651d85523767c51d855234ef621d8552024fe70d8552004fd70d855234eef20d8552006f76198552005bf7458552005bc7458552005df73585521fddc7358552005fb7058552005f87058552006f5611855200cfd751855205cfe7418552004fd741855202cff7318552014fe7318552004fd731855202cfc731855201cfd721855202ef651185523a6f5511855202ef6211855233ef52118552024fe7018552004fd701855200cfd75d815205cfe74d8152004fd74d8152004ff73d8152014fe73d8152004fd73d8152014fc73d815201cfd72d815202cfe71d8152004fd71d815231efa50d8152006fb30d8152006f830d81522c6fa20d8152006fb6098152005df73581521fddc7358152006f9601815200cfd751815205cfe7418152004f
  | 29 => 0x6006001000000400000200140060000000004000004000800c0200020018030000005001002c000006001002400c00b00000580000010028018002000002000c0180000010024000001000800000400000f00680000000058008000001000803401c000000800000000000a0008020004000000001c00000a8004006002000002c0000160060058000000001001000400a0018004038002000000000400000180100000070008008006000001000c0000000000018006021006800000200000280080040000020008004000002000c002009000800002e000000800400200700e80000100020038014028005008805801000200a0014006000001004000e00200200000160020060000008001005000801a00000300040000000000028014009000800800c00000000040100060010000020000008801c002000007000400200200000080080080080044002000000002800c0010028014000000000000000800005cfe7458a5405cfc7458a5405e7f5458a5405e7d5458a54004ff7358a54014fe7358a54004fd7358a54014fc7358a5405eef7258a54216ee5258a5405eef4258a5405eec4258a54004ff7158a5402cfc7158a54216ef2158a54004ff7058a54024fc7058a5405cfe749865402cfc749865402cff7398654014fe7398654004fd739865402cfc739865400cfe7298654004fd729865402cfc729865402ef6719865402ef6519865419ef5519865405ef7419865402ef44198654024fe7098654004fd709865405cfc745865405e7f545865405e7d5458654004ff7358654014fe7358654004fd7358654014fc7358654004ff725865400cfe725865400cfc725865405ef7715865418ef6515865405ef7415865405ef44158654004ff7058654024fc705865405cfe7498254024fc749825405e7f549825405e7d5498254024ff7398254014fe7398254004fd7398254024fc739825400cfe7298254004fd7298254024fc729825402cfe7198254004fd7198254026fa7098254026fa50982540fef9509825405efb4098254026f84098254026fa3098254006f93098254006fb2098254026f8209825405cfc7458254004ff7358254014fe7358254004fd7358254014fc7358254004ff725825400cfe725825400cfc7258254004ff715825402cfc715825405efb70582540eefa505825405efb405825405ef84058254006fa3058254006f93058254006fb2058254006f8205825400cfe76d8954206ee62d895405cfd75d895401cfd74d8954004ff73d8954014fe73d8954004fd73d8954014fc73d8954206ee52d8954206ee42d8954006ef32d8954206ec32d895402cfe71d8954004fd71d8954024fe70d8954004fd70d8954206ec625895405cfd75d8554004ff73d8554014fe73d8554004fd73d8554014fc73d
  | 30 => 0x800c000007001800800a000000800000000000080040000030010004000003000800c006003005800402400d001800401800000c8008002001005801000000400800000060000018000000003000800c0060030010000000008006801c000002000008801600b00100100000000040008000000001000400a0000098000004001002000000e0070000024006008002002400000200a800001200000000000020110020004016000000800000400100000080040000000000008001000801c00c0010008004000018000800800000300400200060030018010032008009800000800200000000040040000000000001001800000000000700240020060000004000001005000001c0010030008000001005000401600100000000220000018010000000002800c00000000e800000e02f0038024000000002800000000000100040000010020034002001001002801800e00280080000060000000008001000001c00c00000180080120010000000006001000802000000600000040040120000008004002000801400000d000800000e000002804800200100000080040040000008002000002800803200900000180000010010020006000005001001a00000a801000a000003002801c0030000098000000003000001a0000010000004005000000000000d0000008008002000003001400200180080000030008004000000000001c002018009002c01200400000040140040158000004000000801c01a001000806402a000002804000200000680000020000010020008001000801400000400f80200040000050038014000000001c00e000000000c018001005000c00a0000000010000000001001c00001a0010000006006003001c00000a0008040002014000001400600100000300240000008018002001000801c000002000800000a00800180240020060070008000009001001800a000002800000000f0008000004005000800000000300000140040000000000006003008001000600000080040080040018004004000001001c0000130028004006002000000003000300180000060010070000006001000000000000000d00240040020008008002005001000400a000003800802e00200a800800000b00000cc006000000000000000d002802000001c0030018004001001000001000b000000400000000100180040150048000000001000000400e006000000400e0040000000026003004800400200000680000000050010008006002002000800000f003802800e0010068004004001000000800400000000140000090058000014006000800401c0000010014008000004000000000000a001c018003000800401400000680080000050018008012008008000000000400880080000000000004000003000000003600100080180
  | 31 => 0x6020001801401e00a00080040000000038004002000000000400800b0000000038005000000003000400100080000020000000000001002000c00c0020008024000001000000800000b0040000000000000000800400300500040040060008000010000001800000601400100080100030000034000002007000c00800000000780040000038058000002004800800000200080200000010058004008006000000000400400000040040050020000004008001801800000c004000000e000003801400400000180040180010010000002009001800000a000000800c0000000010008000005000800400a002003000000400300080400080000008060010000000000000a00000200040180020018000008001000000c02a0010010008004006001802c008002000000400e0020000000000003001000800000000100000020060070010004000002002401600b001801000a0150008034008000001803400000f00500040000060008000002001001000000000a000804400c000000004000800a00080000040040000018002003000000c00800000000040020000000000000002002000c00e00f0000014002001003006c000003008003000400000000000080050038010002001000001400800100180000000010018000000000000000000200e0048014016000000000000000900080000000010050084000001003800c006003000004c000000000004c00a0160028000002006001000000e000001002c02e00500680180000000000000000004000800800600200000000040070008028020001000800400e0040010010006009000801c00000b0000018006000002802800000001880000020030000000002000000000002a000002000000000b002800000a000009800800000200680140000040040000000000000000000e000002800c0040010010000018001005800401000b001000400000f000000c0020000030014006002000800c00200000a8040010001002001400600000080000080030000004006000001800802c0000030008004008004802401000500200040020000018048010001002000400a011002801c01c0020000008014009000000c00c003000800002400100080280180000008000000002005000800000000000080040000000010004006003000801a000003000401a006001800400600100200100020000000000008005000801400a00700580000080000018000004005002803802c002000000000a0020020008000001004004c0000090010004016001000800c00a00000000180220000048004000000000801400a000001800000200000000080220020010004004000001002c00000000400000000010058008002000008005c00c0010000004022000004800800a00300a801000a008000800800000a0
  | 32 => 0x2806800002608c520000c36295a00c3a31a1600015d200000004a6000020f8000271160273182127d000f2554000088f983c0001fc27920d981eb089632488b605e929a6ac045a996901612d9fa41fa950c7120e9651689dc000000055f80000001946432245000000000000000000067000023c400027660000ee885283005c0227853ba3bc0800c1000004f2000000000000006208d7e4078000000000000d80000000606000219c0948ce000000a00e40ede2f6232a71924b887f00003ff800000008e24b900001730000000135831f0c24300846015680f42f987126279c8a05507a856625c697009689d8800035380002c500000000000000000000020640001ce227d19a42cf0f50767018095a9a8651900000e28000000130a08da2c0000000000000008fc8668000000000009460001fe662fa31a0000000000000081aa23c0000d72000000000026e21bf0000973000000000008d800006d9103200000009470ada0da9d6400000001ba042000023e2000000030c000083103f2899a5988008e702efa2d087519c836b0daa983229265fa51425ca2f6684136634f0320230800000000000001c0e98388262570b2400021f8000000000008ac5ad000000000009dc9bd607386d6000012893d9f0a36700008ee80007ef964a0000f046761498852081c000000010482347fb000055b8000522853000026284c49108000193c0002134020099c761800042a16c6000000091d80009d29ee400005f00000e047df0b4e4d89e0c1c604d60a319668f6000000010345cb800018683e05859b1e9ca00006b4a0724e20e900558920272000096ba1c4368000044b139a0001dac74a00003b50000841880c0781e7041617903450000000057000000007ef152031f80000710f3c61398c4000000050f1f8a0001abc853215e8de000000000000000000000239a50212de00000000000a9253a800a01a0010008008001000000400200a000000c00e000000805800800400c0034004000006001000000000100500000030010008000000000000000c005001000000001700000040020040000000004009001007800000100100000220000008010000002006800800a004002800400a000009806000000e000000c00400000280000100020008030000009003001801600a001000000e00400080140000060010000000002000800000e006000802001800600180040060000058024000002001000c018006000000000e003000800000600100000000140000038004022000001000000c002000002c000004000800002c0020008054028008001000000000500000000180000010010000003002001000000200b801c02a003000803c00200400180380140110038038000001002807400002400580000000010050008000013004800800000f0010014
  | 33 => 0x2b98861f69e1669900002ef13fe03480007c8892a00022b84ba12b40001c0a000000000009ca7f703ce8a181244da0000000171e06c9ba400000000000000000237294899840000e3e0821ee6000000003680001ab16f064016e65d180009db181400000006808000689a08609994d0492269c47480000000e2000025ce6fe117846d8ad06c60000051a71e77288980000000000020e00000007329b8e00005804cb174400000003fc910033c1ef800015c2000236a7258e4a3cc04f405e17e237a8000393082c0ed00004aa000000000000001d789c0800000000007108c44000091e000236c0000000000166e7df800084680ae11c0000000235028b0fbe4ef10406ac830c5d8192089182f02ab02828d31e325ed86f204280002ea858800008b02510ce29538f9082d8000845800000000007e5917e2ed8dfc00010760001ebc77a80000000d3873c048a21a1d6a000053e57718b07f9126a00027065299bb042b000061500000000ac476e9f085eaa11e14304ba77782ee8f30f8e93280b29b509f673813ca72d884000001f45c7025e0f501ac0000df800000000001e7c000000087180000000000000000000000000000000000000000012ce000000033500001da000000000003a880007079c58120a018326a0ca69d04b81d29e8600589900d424a080888f8090140279e8afe000000000006dc00018327e49ff60efa1de84617a000000000001110000008e0001b6c36f1ca6000096c4119fce3b6157c000185871b0d441ff9f321b196244c89efe31d06f8746888400025a20002290894023878509ea00022f08fb04fc0000c3c0000c0000019e4000033048f000092300007b29dc273e16c27b709a8000000000000002fd00003d88000000000036480d06b3a08a27400000000000000000052a00003d29dd4000000025d0d8400000000000122000115e00018480c8800098980002ee27400001fc61cb9aa2681992293780000001d4c0a880009b980001e6944600025465608bf88dd257a7721f2a9371af44ce1bd24a18b7c07da10a2a1957200009240cb940c00020700001eb88ea17ba00000868ca1a7a1940480000000021d9124000000073f800053825885cc8000959800055381600001c3c0000a6c00000001aa1d0e00000003d8121600023481398b846838000810151036e80002f82248141a5f28c70aa86d317f6000218e42100006fd800000012b879800007058b9c9d7000000019a60000f780001c54000000033b000014e26bc000000020b800000022ec00000009d79a247a790be34a890e0001f1e000249a0001e742de000000000000000000197231248a8000000000000013ce922a0360001eee13a969e5b297bc1fb8fc0858a5ea0bb19e8960a64a5c1a4342bb990e79513747cea13e51a13de22b8000036006e00010
  | 34 => 0x5f5000000000000f1a0bc000238e8f592cc000046a0000000000250c00000000001db4000000095c0000000017400000000000b8c088800000000000e99a6e519830847091fa0000d905969632000009c000093a3c905c80001fd800020f8423009686811fc2b724083df9096002a70e698817c9c504686032392000193e373994807e097843014f64b5169697b8e9213887ca41713ea1258c5e412918c00000007340000000089400000007ac088a7d417581b28fde00025c8066992c19826a2305000024880001268446594a640255125a0000000323800096c00001b1059c1d6000082b000091c00007c10fcc99914b63f204e008600e86eb1d484c206a26be22e26e60ac846b0c8c7748d8698e000020200004159a2c000202e0000eb40000f86000050a62822ce36c831a00023ac1b60000377800000000000000000000000002c0216000000000019dc07a11c001898527cb23580000000000000067309be1c0906c488245452f92ba0000000933800028980004d4242e01317ce707000044619f83770f680001d76164800017799b8577873a0001c8c0000000000196c2c58000000000000000000000d5a9678d100000b2257c000000000000001a786930000841000063804c6000214e1790dda0b400004e1000000000007351d3c2681d30000000000000003ea00001dc84fa2d312e64581b86489827697700004ff241001780009088de24710ae08128000652a0347a70bc487fa74235f25da00025403c797560000000000000000006fa006800000000001e11c36000100e0000000000000005a80007498000000000000002c00000abe405000092a9c4a4ed0e1833d93161ad1f9a0000e7a0000e6834d086a1f1099230987480c99d740001b9e0cd92ea8438ece28180008829d0a00017fc0001f447cd02720000000000000000008a0325000000000000000000000079c86513ec1c80000586173a4b1159a7a1016c578895a00000006c90000000000012199e01198f147e509ec85486820d715ba26e9d06957079474e115623100002960f3811012a031a850431e91b4000178e54700005b5982c80b0a7423e90ee91222b600016b01161af2000059623900000001052182a0048d91f143ab19980000ee0000224204d8e241bb227e93b9fa67678088181000000c03b234f894a17b803c1d51986978833c536966a67097ca12100001378c8617681c600000006ff9484000221c19000007cc266c00026da22321725648000229810889d98aa67196427a09270000000000000008b21fc4000239c2ee8abc39ca3b0012a5ba25a800071f8ac62d289024938e3a2c186221fa1e1e474139e8748de48181264450208c3a780007b824bc69da0f494f9a602330d000000000000000000000004d083b642e8dd857900000001c6e00000009
  | 35 => 0x1d8894a258096700c28e314160001f1060680006b980006bf06965af000000007dc50d800068a8f7487da4628258aec4618000676a712105a5ec0921158000028a73981aa00012c846f1ae44c00e7400007602929cc03850b30146800000010e48cd25367838000864057626b0f0e65a000010b8000000000000001da838800059e1cac00008d6000054c000000081d1baa8bd1e4e418000067c800000000002d880000000ebc21f8c72342011600000008ab800036d0c2a000026274a8dcc000000040209044cd8000151a1c00000000000201c000032a000000000000000000000000000000000000000000830a5206f6885a5572166000182a7a591880bd18ca00000000000000000175a0000d2c21e00000000f3689f1e56450898800000001cc8000000195a55d0dd20001a360001c627e7850000012020000000744a2bc4d2000019296d85c5000060823e4315000000000000000000000251600000009d425f41d0000080a0cb661f83165cda5240000000555813823614c421d13644b58d422eb24ba3990cbc886a23a560086638b95bc1c894c25590000000000003ea27a2e7888200006ea3b422c40001b060000ac024c10d694f1b36000245600000001c68bde000185e21900009bca2587e8000000000000b80cb04961ca8000201e00000006b8231852b827a00026c034a1cc41871faa51d936a00000002b2995e0f01d6200021966180a207ed80003b68690791960090e025855e000000000003c9a5265b8000000000000158000000000000000003fba2dc349152600000009e0090c47a1d6c6fc9bf44270cd6000000058d9b0451b86da71e9e1a981035e000066692c023c0c19ad69c9198e1de26f0000167434c188e490076a66d9b0e5251b8010d24e400019305f8139696f800091781d091a041420010aa2658186000000000008122fc858a06214c08e28b6c5238c4832880000001b2c1e880000002548000000000000000000000000000056d800059f1b2651f907c39095629058e54569260291080009409d5643392785469ce830b258677f9b50804811a0001d0c00022280001ac62f48914000121279b908e84d8e5635c01d22cf800000006167da00007ee839e000109a3d1082053f00001dd11ea3330000000000029a17da00024ec87b8d1887d103e8990c883a2152a5b0083043983282cb19ac71da0b206f0b446010ef4927958e5c6a11c12326e85b3918a1cc244e89a010e227958a5291e2c0001ee2000000000000005c4231e71682b006900002f320087d48000000195600000008731d9000000004b080004730fa4745926e8e202805e0a6360698c6000008a200000000b08f121e5929e98218ce69118c61e4800098827206d603f6000204e48e000021700000001b0a557800000015ac397800079780000000
  | 36 => 0x8000000247415d0b46000057e5ee00002f68000000000000000007dd80000000e088f1a29a00000000088a5c02626108949500000123e8d101643aa1f908e0046489308f25fc181e002000000000c4479800000000000002496000000049880009c68000000276e0001f4c44a89e486ea5001ef03d80b39c3210391f86298c843579dc000013d4000209e89121e297e152218c8a3076f162a000002e51e8ab02f88000000000007b80008629c0200000000000ab645a15168d70b568be03ba880983464e201a0b6000041b80001a68f066dd1c9413616f60000a043b21db053700000001f248a2a20633f05b67eb08e82781c600001acc09a000028d1154000214078c061072493d60d51cce0000ee403f01842b500000e49e2e000000086796e47fba69e1d397fe39200ba96c8b8a2e590384b818ec07e843e0d884106739e4a6451cc88a806349cf986427989ce89c00c052e814486a95842598000000000068895b89ab00000f925e0000077e00025563cb9dbe00018987d918a885418120001c1029f9dce7568e7c7d226ba372010c9b7a63c5aa0832227000098d00004db9eaa475807810926fc00000005c280000000c0c1f38b9400027822c400000000ec4000187a000000062400ea000126c04b80000001c2c0000000000000000000008bb80007e3a7308b0801007014621dea5900001ef61b88000000000062680004ca0b5e000080e00000006aba032751239093a822e00017c46a59940000000000017ac00004ce76a8000000000000000000000000171800069a000024b9bb2630145c00022b26cc9a0a0000ade11c97e63a617627d1a6943b0224e0e502a6000000000000008fb8000587800057398ae00019ec6f7800000000000001e3e9e10bb2000000033220920001490213082a7a600000000acc38a2186258895666595f25e1209c27613c000001fc3d99a8064ca3ca7f2800098b80008fd9e665bd2734000000000000003b98000916a1244029c20000000031d80005dc243a0000f346e69e4c15c8ab49208a76491912666a21da89808fc3101de25c49f1a934a6761d416942c3034a46910da02280000ab000000026a6000000000011a00000c201930000000000000000000981982000000098c81988608000000047e66200000000e80000000000015460001c4c485230095f134a00020789530cfa88300002050000000005a00f895e2e98ff47c189060001de88af80002fb00009340a5e8f2000099d0000000000018f00000000000000231000020fe000000046e800000000000001cba00000000002052000149c47ca6c800022fe59e80003ce841800009c200017309be15da5258b1c01600000eb8000056a4240ab9884154906a237132a00001183e61ada8770000000207a109800000b0ca8000000034700000001dec
  | 37 => 0x6000217c5a3184c84b1c9c753a0902d422e43bb9cb846c92724c99438000153888604f07508d4a5a90fd62c4800000009420000b6a0000564000000001a00000001aca85a00003f6000025f0ae8000000000000000000a1238006481ec884e1bd9d826df015211319be91a8000000240c0001f4200013140000be8026873c0f10000000264c00001ca39600000000f3230d0000000242c0001a4e00000005200dc00001fa85159d8e000000000000000000182000000066a81de00000005761594200a5d88cd81420001b5c11292a66f100000000f6e52e116c18a8f02813259a19a800066007cc9330000000000000013c2261240600003880a81a1c0b880002d80000000000043f816e000001e26907f474b92c6000116200027680002704000000000011d46a6000065e800000000003bc117a36e054e6ae8d1200011e20001bce5d400001738000090885e1f5256e00000262968374623000c5f4a0d600025380001644070a34a00000007a406a600005d49aa080a0bca74e33d18f49c31b62196800085c0b3a000207c000000050506986aa1d32747800061700006df8a1c00000000d3800002b000091b8f9c76e00004f8902a7a000245c300003808aae65c80000a120de7139b4a5a9851200013cc00e800010180000002274086994c12f00004601bfa881111a4fd9bb683e80f61dc0cee24da77639a80005b104c08cc80003061a38000264684e80009a0a5744e80dfe23a821c885a5a04a3000079d8cbe286012600003ca000151260700001c501e6779049c1f480007680000756145091600a697f107000000001789cfc859000072c21b657b8ea448b13723c60fac44299b425480000001288494000040103669a204ac0001c7c4d6867e5ae105a0001f580001e580001d2078700e060421bc06d0d361588a1a35e190a6c89ea41b40b707bca49400004c246a8f5242c8ab28b31ede2c0915c40e9c3a000102600000003a287f63501ff476481dc0000000000020400000000d920261f79dcc419a1ae0000000220000000020006a70000000150e14d800034680008f404f690c9bea6ca000097f8000000000053500008a9a4a8962a154000000000000005fb267a0b1000011200000001902000000000000005f79aa400020a0223985600000002b380005d09ee81c9800061c88ba0000000000267c9c026c6799000000005a08889fc8134a1302a2192a0001e9235b2418236a08e4c118b28791f5e9219442143945e42920cc6a49bba063023e9cb000000014f482e80000000000000225a808249c0000d9a565800060a16fa00000003f5049e7e1800000000005b890d05041ec49798822668a3a47cb8b863a9a2d606da16c089068e13402d26248efe00008869ac07d64219a04268862e79fa2267d886523fc23fe37d8a3259a113e1fc
  | 38 => 0x924908559e8c77994f20cd232e4db1ac870120549a58cac23481665ea12960061d7a00000003ee80006f0a29e3398d20000000015500007d396da71597165a29f60834000000000000001a2e59780004ea8d9651800002700bd609b8dee000013a19783a0000034600000000000c507f318fe00000fe3d580009d61a9a094046c5358a167c4800096525964f4006c00020681a30c789da907e463a4b40000c9e766000000000001f60000000160400000007c3000043c800000526aa1d19e6c8d4a1be82988062c10f840e0034048ca2c613917f45551cae5db078c57302aa000179855a1e520001cf49af87b01f18000140a39e6288000240213868c80003898c3e16aa12a062800038d800000000005b799a0000277c000205c0000f9e7899e880000f583bd82b21b395fe727944887c91909a697541b51b5628d8ce478e17225e925602a6119416c8e6e4950e605460d643dd887a9d201d4000141c0001f362678000000152491e800036a00000000510000000028005a40001be80c7182200019360ba144c3798a8473926227451bfc00000004fe80000002056000000000014b47e894b055d9d3a000000026280403f7102030680003c026e48faa73246100000000000168a29c3ed800000014a000019d05a3800000000004d800002df80001eb85ca000000061b97e800000006e80dd05531ffa64624f2000241a21b00002059d2c363148c51aa67265e00006a784f800000005699332554800044e0e62000083442f247c6f31330000156a51106305dd88501ff0b9a117144e2121bdc00013ae7c9935c77419243b3046282c05ea00000004ce8a6248c0d3239e0b340000b0e955040456fa19862e000000000007dd09d229180000002284000000000001be95e1440000177a45100009cea4e6986000036505e686e0dc600001e22ea11c652a98749de94d80638000919a71600000003370000000225694b00003f6800000000001ea878600026787d983ee2830594451914c50a80004f608ee0000c4e9131f3c5ba025c0000000000000000001fe4041bca102a0245e580002500e1c00005c4000000025d838200000001a7014a98280003e0993a00001763ee0f429511ff860180008f000007f4a3f427680005938f4055807820ce98d24bb914e000251a0001f6c33495d61bc00007a6889a37a12ac000000000011741740000148040812223da000000000000001b9000086016906dea40a99710d23ec8e5245a94787a5016201914b266c244a64b93c64ea00000001c2a2601c785348cf812c22883a380002be80007861660308860e6b084a00650dd497597e427f909270489b2000137c00000000000c0e13a056656c80000919cde00001000001752000000000000007ec9f6e77f0000332a05096104ae22200004060fce00013340000b2
  | 39 => 0x46680006a38000000143e0001a5e0001ef09b71b4658292228ce80004de8000000161a00013e482a151491800000001b8c5a48000000041a00000000000000438000089a80008de800000024fa00000003ae20b467c000029080006f8036c00000009b4023000000000731f0006585480df8bce4c60d7a40c13ac00000000000000000067600000000000000000000066f00002c2907a4bf000086d00009de000098521ea656000000022ac000057c2d4a3706e59b902a806560001ece58814e84a4081e09f8000000265000007e00001d7200000000000a8e757939c28a024c00000001cf894894200000ff95c0400800047c10e200000009008b4200011be00000005f716a005fa6c200000002f283d08ef872889c8d9e0be90806da24047fa007a0af865450499287bf0e1600013b0765029065a82565bf8000000931e0000ad86749df011103fa1a79aa074098ee88017b4000125c00020e43109868430979a14a800000019e69320294000000000001a8000159c00010ea17088603e002f82ae1a40000000000000003ff12bc397230a000248e6c80000000128e47ba30844f15300000000000000000015040000cd000000009300780000141831b80008a9000097409f800000007bb08aa4e6154260e8000000000000000007ff800000002b82460000664800000019ae000271c3e294068ad1b0279aa0ce3c417ae0108a7a000131028f800066720c8295044213207b6481a22c42411fe6431b3c00012f459005b03531afa479261a0000f943ada17653f9fb05249eb224ca3fa15006383128fa6879a5585e990de50782861288000000063a0001686000000000023b800026d837800000000f6a2a921421d307e20f4940a7b3000000000009cda00602f00000001082503974a75c23b618f8672000012a59325343299df676b96764a1160c8f50000360037c3459a3e0000eaa00009cc82a98f00b29aea6dc015c7aea4da653800000000000000000000022004b00000001cd619e8a6e8aa0000736102428f00000000ac24b6221e7f7a6ea16b800000001720000bea000000000000000000ca05f41d7e147a3e000012520b7927a00021b200000008dd80000000716000000009100000000000000247e00000000000000000180e5388a8a69400004de00000000000000000008c9cea1fe066c00018b40001e044448214816142470e14204b28692000000000025ca00000000d69650000000000013f8000000058e854a4f70b2a000150a91700006c00b5474200001878e223fa80000001af652225aa8bc80002119d1c6ca92085a7000075800000001ec2175952c87583f40f59e400001130000138e07221224f480004a91aa6000234606784500a498004e009380000000719a4be09680002e822da0bd8c6642d000096e000060ba34e65
  | 40 => 0xf71e060001a6673b00000001c280001eb6911800000024c428500004c700000002262275800024418ac5de23b40000fec48e81580001e8e00013ee4e3127c97a04ec14992fa0002652993800084a00000000a82748962e0000000000000000006c200000002dd00000000e107ee05b800000000001b721c280000320e327f0235e98b13a26468312872037867aa63e5ae80003ba93f40001826000187000000000000cae3be80001c400002d98c1e5da96148c800009190d2600000001ae800089724a600026560000000210800000014ca052037000010b000000007fa800000018f2000251200006d261083107ca13762428000714a3aa5a0a1a84659908355843a83c9a520240e0a7549adc3f806c040892aa393800000021d050d0000044000000000000002698123961002d9482630852800000003bc80000000faa00000008f3a6fa5e1940000027648210000000268c0000fae00000327091b420c919b28d882b66cc222420404384000386483928047700002fd800000000000000d6e4a2800000001b8000228200000000001b1200016286129c8000006e683709c66d014e47829e2067d0000811056059980000000000299249242625e4775829826d983080c229800011526d50d6a00001069b811e07e0800050100000d08e1e000000033097720001aac54d027800000000001be43158c6483d968800010d800000ca76c80003a1800029325b627a000000007904bb23e86570e44498167e71013029ad15e837c1b6600021a47fc1ad456c000030700000000d0681b0000000000042e01e48881788000011c1f99ab40e5a46c000000000000000001fae00000a80000dbe43d0000000000000821920f6979263e149e0d609fa2e6277e163000000018f63a08000000150800000000b5000014c800045c000044d97f200000001dd9ea287800007a818d40001422150800099fa326000000000000004288c8025311984ee14c600186027ab190452b12742de90f82cb800002f800083b9f888cf1b840f980006b400009a1052c4f814867261c9a533978c2808ea05cb10363d51e3478d9a8a7b1904e1a29cfa00010ec547a786539a07e287800094400000001f3e32e80002b9a43c469800076983a299c12d200000005c21f4a70688e600000003b4800000005f60761b1c4928fe80000f4800000002e0911c00000760c39b086368000000000000000000000000000000072f98e800025bc1298bc088e05fc00000928c102da193906446c000000000000000000000254a00000000818000000000000011ca0001ec04cf93940000f164bf9a48000191c19e000000000002dd98fc00000001e2800001707ec00000007d7000085e00000001f986bb8c5a10d84a400000007628eb2684800061aa4265818c0867d800000024a20001f7894380
  | 41 => 0x99e59612948c880003f19e420000000000015000000003b700005678d8a431a2ea50c234258492920530b5815a000000000000dd870c18d97b0000257e84c800088498ba88a9d7c0002112486814e744105e6290bb464483c200000001f416ea26f020c970826c01412ae2540af64ac029e299a66844d00003318c0a98180747712680000000024b0854407000048308b2805238400000003fd86bc52880005d385508570a9059519060000fd200008360000000460822c8bf1da215602cc4a88b18113a6863551d3e000000000008f46f619d49c288e0000000065f224a2cc8fb4000000099600001d48bfe000145800007340e395068e98f9a18a1d3688c80004689bc800000000001c183d3205a83a922808093408620f46311a6ce4e2825469621084c800008d0000065d0000000000000000005528000000000000021607a280008e880008c180000c08afc4150000000000016080000b20da60001b3a00020a4467141a000000000000000001454369024a0de80b85cd252e3de80000000000000191e51c9c304fc032c0000000000000079886fe0000e1a9848bfc866a03805027708cb205e84f135e1f91c889d59f9c370802890d916638d0f5c282933c4438ba23570d0458209089aca0d82b58db67529eea0000a7c08a800000015c80000dfa2f1800000000004ec93a616f80005871b440001fe200000001a01bbc61117fa4c39f0e4bd9bf0822228c2f099fa22d1cb257411d80b9859a00d0000729000050e80000001dc66eb9fb45f1800000000004188b7283f1cf21e8000000024f8826800038e235400000000000000000152800000000001b2e0001748000093e4ed8d468cf80d600004300000000000154800000002a500001d90870107916e00008f656400000002294214800078080008398000100a478224861200e22348b802a46141eae4049c148b780aa0001b3e1470000637272600000009cf000070f98d8000000000000000000082618a1fa0da000023000009a809de1a113f200000000001664368a11487a0bd43408eca98a8000290258c00008ce7211d9a3bf03b0627102e00001b05aa85f80ba976e000010488d80001e213ba4d5a6163011d8020e930c40b084a6a400007018b3878880003b19bc600017cc6508b926a226ca9460dc457d87a60c61a8c8a89888000000049d93c82060d5204c22d20070000000078e2c0000069c0000000215a95a1cc29ca852e000000085a80000000000000038c957800037d1e4433a22e6695a06e0f7953e00022fa8e092b2000000030c80006ae1a0000000007dc000000010ca000000000000001ac222e93c004e00007b48288000533000000017d82a59ae27f405fe135000000012da145028e4878000000198a4e19b0c9bb8000031a74c00019d66640000820800041300000
  | 42 => 0x5f4991172496a19ba93184c432c80001c380002aaa0e803380004458fc47118d2e000000057e000000016a277d06a02379b6e33a9e502a00d82746000009a821e5d7210272f000019891483e807068ac179c3b8a03c4d30c9072d18402b4874468f2100754111e1af84564c1a17456180003df1a1836b80000000f4e00000001db862c40f000095c9bd079e142e304a3565c388720001e5c4f690420001b822eb904817b132e224049075b86b64b8a6007fc8dd6003a066512872a0b71f204e09540861034864d0fe63ac122e76d97a243e84540001a08000000000000008f7956c7780aea80e80006c40000000142687c23c25ab80004b40d0c59c1c0c58f93e6672800079c800001206ee33ca21026b9f1616b10fc34892be2ec00008039684000000004d0f64000062000000000000000000000000000000000cd82d688620000000048000077c8b8e749000000008a4000000000000000001da46a517c2000000039400000f30000000128299800008e19d96256061463410dc5fe142c5688b5c011897a433000024495a0448a07629c1094000000000000003ec00000001c6a00021d80a5800069a800041d11ce0001e121640e6c9c6199a2a705bc289060896d11ae84800005f201ec9c8997663e80005bb1ddc57b000000024000001c74000150230a18e200003c8464801276a000086c036e000000000024443fe1dee32296d29ae0f22000252a000000032d00f07da80e60000e5a4fa0e1248400006b123f05148cb80001afe3c7000000005e86e21d5c00025a40002662326220e0000000849a7083a1000078f1fda4c909f060d9aaa67f8df268c10ae4bc855673489a652f1cee000241c00017020c281ae45d80002cd980a7820b085ec85864721ca015700007ad1a726d7a5de869989400005dc5c81fd478e99de71794f0000153c78a85d80000000166183e3c298806f9a4d800024d6000274637b0304406800090aa0625fba6d2751828824d1eda14600d469091ec0000c9650c858408400001178000532185a67b8e0617ea0da7f800002a31b1600024f4440a66e00007c068e9f021d89c346cd276008289fc97c00000000000000000044b800053780000000000029000000005f233680006f000003058bd061b06a43a723301861e688318c82441845280f840c4be124c987a5ac5d3000000000006d680002ae80004031b6a0000a0800a9b7893a000025c000091c807000011f40001cdc00013c40001dfa1a185240001068000000000000005b50eae018178a0000000000169a26e236699a9c9057e89aa19925925621b140001698000000000001ea0000f8c658027030e977e22e000000000cc00020d21c7a0980000e460a7243e00008ec359800006715663fe8b8868516725c6004449996be11b908889b000012c9
  | 43 => 0x25fa068800077e1cda6a09f7200019267de84be5e525303cb03a83f8a12e0c7850880aa41e55c17ea1c715c435d9b4e5bf16620fa1638651135208e958c206929c1a221ac6d8251e000013e25f81025dd08d406402746062414293887c5728a7841c80007172504000039c10a000060081ba9d1000000025d41749af05df0ca4000075a4ef81923ef25769a91be23e205b4602060047da6fe3e580004b702bc0001b7600018380cfa3fc7a99ed8000000090c0aa69a424fe000000002d1caa3dc80005caa5060001f8069b06e083c0000000000000000007e300008c30a2e8b60af038f041c5f0000068d00005be2692551039a13300005ca1b5200021100000000189094e021000000000529c41ade57f00002d900000990a9a0000000856195443da0421961a1a0000a38000042212600000fc0432895070800000007ce000000009f20d58000000263a99787c21000f700e90000930800048d00000001c440001ba83c20000830000000018ea8a39646000000053b210c9568b9083502fc3c68a228f995c636c18963c300e200018bc3a68cce9290e2a3379ebe1ae0d5832a9a4a702055e1ac9ea80000c4c36387362e9000007c1ba269f8000347949a82519fc9dd0000399a4e0588964848291145898a2a2750f3e98907c826d1c0005c000000000005d9995029817681250d88000242012d00000001a1e6e99a5a48105a63b5800000026d600016b2000034c00000006d200009ce00002498bfa72395e049093469d5163c7d519620b593929ab827c8aaa65446a12f085ea4405a00af40ae896000022ca00000000ad231600015ae9591ed4000080429219160000000124800000000000000000000011e00024b600000001d58000954024e01a8e0c145965c6701efa6ee0e3049f98cc29108580390a6a316275a0000af8245856a0d81cf65b7067400020ae00008f004500002839ae815105c01c0162c000000000004da92626ec8a59f56000000078a0fc2000000071c80001a5075e35880001cb00005bc99522b8925e11d8d4868800ec969813c44c87420a6908a7208000000000000020b824680004d11d3448da04870b987808a0d3a39f80662111c22632134e343979e97da648000098e8eb800000012248d680004140d6800000000000000000000068a000068303ea0898000000066e39d80001e90fe400006c882013900e6007c2db87b894c914a1c124288708c681919f5a38b13546f513700000000000100663786de000000000000000001d548c080000000ebe2662214904a18c71c16c8000096467100002f20f6c00027520b1957a6ada3d200000000001b8a942800000000000001704000000000003fc0000000000197000000001fc00003188000000117c8fe0000000000000000000000000000099a759800059580007140d0a
  | 44 => 0x26323dc7500000000000031b15f48da09e20cc847c5d9198c55690c48df88d090380000000f5a03700008c9121c75a0e403be056e000000061d97403d79abe1b322809a3a4840000b281bd00720000ec200000000000000000000043c1ed288c1b381e60a725cf0d507e11fd622a04aa851831430e00002e0047a0000e940000f2a4b004745839b944df8000000079e92b16b600008566ed000072197be15e8e0e0250000330011248015ea1c91e249870cfe7bd000051c03f81ab82a89b100007400eba00011da8e816ee00000002a783ac61183848e5059e284263044303e28b500547ff000016e97263e483445f5843c9998000301a6cc27b80000000000897800003791b861f15a89a2915a93500a261983ec00021ec8dba3b2000217e44a000069f199424a00001df000000004dc5e0000024709940ea88be8689ec803e086e000000082f80000000f280000000804042c8ae919e372800000007fa92c80005d7907826c10d4495952e95484ee000113a2c79ac00ef166c0000d608380b20000000053e11201d9800000000000000a524111aec00007be28e9bee000067c00010a6000146c000009e54c9bec2318000697064200000000001a46000042a000153679681d62b90fd0761188a50a13a48e61ed60000000000000000018e467880006091d043bb18d6882126871a200a70980002bc800000000000000000427800056a9d8c0000000851000093f15d435d15b43e8853a963a26e0001738639a30e9ad80000001b9c0000c5c000052200000000010000163833895b000085b8000209000000021ce000245214f00000001ad80000aa297488381ee85e0000000020a233893881f21aa80005b420160000000958800000005349cba04622f0000000000042d80006951ccc1db0b4843a000000016340b900004860fca644000015b0bdc477800024f1b9230b9e002fc23965cfa6f429408fe000060c7c700ee51d116405a25c451f04fe920008c0ee15e67c6062689026427b40738000117253e91042d0155819100000000000327231458c007e000196e11e16ac25b800033105780dc9ca2000000000002fe20f000000022e8000237c950800026192447768b1a83b1dd804c80002fba4880001e100001816000075c31c1bbe9bda53a2320b6887280006a100000000000454000000000004c690a05b30f200000000000000000004a8000153a62d800000000006c683524ad80002f9000023284ca16a00000578000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xcb864dd1204400b1f10cba2408811b2e191744811002cf840ae89022046aba86d912044001970edb2240880032e1d864481100071db28c89022000e3865191204408d9750e322408811b2e61c64481100071dba8c89022000e3875191204408dd3506322408811ba660c64481100074c398c89022048cbb721912044001d54a43224088003aac8464481102b66c3b6e69022000e9864dcd2044001d50c9b924088003aa193624811000754322a49022000eb064dc52044001ae6ea38a4088003ac190714811002e743b2429022000ea864485204400bbc0e290a40880038e19464c41100763b3b6cb0822003c7676196104400196cedb24208802f2d9d864841100071a328c9082200487c8754d65040099d420b96c8080173a44172d90100247c402e6b2020048bc8750d640400b1e902bb2a8080123e20176550100243e43acaaa02005c747159554040091790eb22a8080063e60374588100247743ea4b102000c6f75d4962040091dd0f992c4080123b21d325881000637baceab102000acf835d5620400159906baac408012ba201755881002575406e8b102006ae980dd1620400159d073a2c408002b360e745881002d7240ae8b102000a6e851d162040014db0a3a2c4080038bd52545881000573c0aa8b102005ae48155162040015d700aa2c408012ba201545881000537428e6b102000a6d851cd620400155d0839ac408002ab610735881002d73408e6b102006ae5811cd62040095d50039ac40801aba600735881000727a9ca6b102004aea8094d62040015d30129ac408016b9a06435881000572c0c86b102000aeb8050d62040095d100a1ac4080179994751588100055742662b102000aad84cc56204009cd4a1a82c4080029ba17305881000536c2e60b1020008df835d952040051b906bb2a4080123e20176548100247643ac4a902004ce87058952040019d2c5b82a4081cb3398973d081002477c3ac5a102000cce7358b420400199ae6b1684080123b20b765081002c7a40aeca1020048ec8758942040019cac5b8a84080031b98975d0010006373aac5a002000c6d7558b400404b8dcc5baa400815b3398b734801000637baac49002000c6c75589200400199ee6b124008003331cd624801002e74b8ac50802000c6e62dd5100400195cc5ba220080032b988744401000637baac48802000c6c75589100400195ee8b1220080032b1d162440100063bbb6ea8802000c77761d5100400196eedba220080032ddd874440100069a3a8e88802000af186d0110040016e30ba022008002dce1520440100063dbb6ea8802000c7b761d51004001976edba220080032edd874440100069c3a8e88802005af0815911004001cd6eab1220080039a1d5624401000755ba2c48802000ea87458910040099d6e2b122008013b8dc56244010
  | 1 => 0xd0bbb284880021f61776509100043fc2aeca12200387c855d9424400117f08bb2848800237e0d76509100146e41aeca1220008f7815d9424400317d0fb2284880038d14464545100063db2ee0a8a2000cb864dc151440018f6ca382a2880032e1907054510004f4c10e0a8a200bcb8649c34144017970c8b8682880163e60276905100063c32ee0a0a2000c78651c14144001976c8382828800e1f21676105100247c404ec20a202d87c865d44144017878c8ba882880175c04175105100043fc3eca20a200e87d87d9441440018bce7b2882880031b9cb65105100061f3aec820a2000c3d75d90414400193ce7b2082880032b9cb64105100062fb2ae620a2000c5c655cc414400193ec8b98828802f27191731051000637b2ae420a2000c6c655c8414400195ec8b90828802f2b191721051002ef0082e420a2000c7b659c041440018f0cb38082880032ed92701051005e5c324e020a2000c7865dc121440018f0ca38242880031dd9771541100065a326e2a822000c77651c55044001968c838aa08800e1f21676d01100043e432eba02200bc3c645d740440010ff0fb2e80880021f61f65d01100061f3aec9a022000c3d75d934044017968c938e808802f2d19171d01100063d3b0cb202200baba86d924044001974edb2480880038ed9464901100071c328c92022046cb8645ca40440015750d20c8088002aea1841901100043fc2aeca02200387c855d940440018e8cbb8a80880031d19471501100065bb20e2a022000c7876d9540440018f0ec32a8088002aea1b745011005e5c3b6e8a02200baba86d914044001970edb22808802f2e1d864501100071db28c8a022000e386519140440017330632280881232e1937250110006d9ba0e2a0220009f2861c5404400b9e50c38a80880035cd947150110006b8328e2a022000db3641c54044001b60c838a80880036cd0c7150110006d8a18e2a022005de2821c5404400bbc30438a8088003179cf65101100064f39ec82022000c5f655cc40440018b8cab98808800327d91731011005e4e322e62022000c7a7619620440911f10cba440881232e19174881100071db28c91022000e386519220440919750e32440881232e61c64881102474d418c91022048e99831922044091d55043244088123aa60864881100043f436ea902205387e87d95204404b0f90fb2a4088003171cf654811000734106ca9022000c3f75d912044001878ebb224088003271cf64481100061fba8c89022000c3c751912044001938e6322408800317d9773481100062e32ee69022000c9f64dcd2044001938c9b9a4088003331cf62481100247b436e29022000cb464dc52044001968c838a40880971e1db754811029e3c3b0ea9022000d58731d520440018f0edb2a40880039a18b65481100063c3b0ca9022046
  | 2 => 0xd63191100051fc2ac63222000a3c8558c644400155f04b18c888002ab20963191100051f42cc43222000a3d859886444001c76cab80c8880038e1957019110006ccb9ae03222000e1f5394c644400157700a98c888002ae20153191100055b408a63222000ab58114c6444001c5ea5290c888002ada0652191100055ac0ca43222000aba80948644400157301290c888002aea0052191100055cc00a43222000aba808c8644400157301190c88802e2fa1c32191100045ec38643222000a3e850c8644400147b0a190c888002ada0432191100055ac08643222000aba800c8644400157300190c888002a7a0c51191100054ec18a2322200b8be87cc4644400117b0f988c888002aee0131191100055c402623222000a3e850c4644400147b0a188c8880028fa1721191100051ec2e423222000aba80c84644400157301908c888002aea00211911000557410a03222000aad82140644400147d0b980c8880028f61730191100055b40e603222000ab581cc0644401717d0e180c8880022f61c30191100051fc2a203222000a3c85440644400187ea93b4a88802e2f21176951100051ec26cb2a22003a3c85d9254440018f6cb384a88802f2e192709511002c7c432e12a22000c7b655c25444017970c8b84a8880167c20570951100045fc22ecaa220008f7815d954440011f700bb2a88802e1fa1f655511001c5f43ec8aa220048f8805d362440010fd0fb2ac488003171cf65589100043f438cab122000c5c73195624400187ecbba2c4880030f19774589100061fb28e8b122000c3c651d1624400117d0fb22c4880030fdd764589100061e3aec8b122000c9c73d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c9c7319162440018becbb9ac4880031719773589100064fb26e6b122000c9c64dcd62440070fd0fbaac48802e2fa1f74589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100146f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b12200087f855cd62440070f90ab9ac4880022fe11735891005c5e422e6b1220008ef825cd62440011bd0e39ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac488003331cf72589100065a3a6e2b122000c7875dc1624401717d09bb2a4880022f61376549100043fc2aeca9220008bf845d9524401717908bb2a48800237e0d76549100146e41aeca9220008fb805d952440030fd0fb2aa4880021fe1576d091001c3e42aeda1220018bc845db42440018bce7b2e8488003279cf64d09100062fb2ae7a122000c5c655cf424400193ec8b9e848802f2719173d09100063c32ce1a12200bcb8649c3424400b1f10cb8684880031e19570d091005e5c322e1a1220059f0815c342440070f
  | 3 => 0x9b2a2000a7a80dcf65440014f301b9eca88003175cc73d951000636b90e5b2a2000a76811cb65440014eb02396ca880029ea0072d95100053cc00e5b2a2000a7a8090b65440014f301216ca880021fa1c42d95100043ec3885b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a2000a76810cb65440014eb02196ca880029ea0032d95100053cc0065b2a2000a3e84cc7654400147b0998eca880021fa1c31d95100743ec3863b2a200087e87c8765440010fb0f90eca880029ea0021d95100043f43e61b2a200087d87cc3654400147d08186ca880028f61030d95100061e32ee8b2a2000c3c651d1654401717d0fba2ca880030fdd774595100061fba8e8b2a200087f855cd654400117f08b9aca8802e2f211735951000477c12e6b2a20018ec825cd6544001968e9b8aca880032e1d370595100043ec3cc632a2000a3e8498c654400147b09318ca880029e60263195100043fc3ac632a2000a3f8458c654400147908b18ca880029be09631951000536412c632a2000a3e84988654400147b09310ca880030f5d754d91100145fc3a87b2220008df835cb64440051b906b96c8880028fa1442d91100051ec2885b222000a3e8598f644400147b0b31ec8880028fe1563d91100051e42ac7b222000aaf8258f644400155904b1ec8880028fa1662d91100051ec2cc5b222000c3d751d76444001c3ea729ec8880028fa1672d91100051ec2ce5b222000a9f835cb644400153906b96c888002aea0072d91100055cc00e5b222000e2f5294b644400117d0e196c8880022f61c32d91100051f42865b222000a3d850cb644400156d02196c888002ad60432d91100055d40065b222000ab9800cb644400153d0628ec888002a760c51d91100045f43e63b2220008bd87cc7644400147d0a18ec8880028f61431d91100051f42e43b222000a3d85c8764440015750010ec8880028fe1570d91100051e42ae1b222000aae82143644400155b04286c8880028fa1730d91100051ec2e61b2220008be870c3644400117b0e186c88802f0f19175991100061f3aec93222000c3d75d9264440010fd0fb2ac8880021fa1c65591100061fbaee8b222000c3c75dd164440010ff0ab9ac88800e1f21573591100045fc22e6b2220008ef825cd64440031d904b9ac8880023ee0173591100063a3aee2b222000c7875dc164440018bce7b28c888003179cc65191100045fc3ac83222000a3f8559064440014790ab20c88800317d9573191100062e32ae6322200bc9c645cc644400187cedb28c8880022f61e65191100045fc3aca3222000c3e76194644400193ced398c88800387d9673191100070e32ce63222000c9e765cc6444001c3ecab98c8880038719573191100045ec3cc63222000a3e8598c644400147b0b318c8880022fe1
  | 4 => 0x14800b1d9053b082900021fe15761052001c3e42aec20a40008df835d841480051b906bb082900021f21975105200062e31aea20a400087f87d9441480010fb0fb288290003179cf651052012e37396ca20a40008dc865cc41480018becab9882900031719573105200046fc3ec620a40008dd87d8c41480018bcebb188290003175d763105202b667396c620a4000c6f655c841480018d8cab9082900032bd91721052000667b1ae420a4000ccc635c841480019cae5b0882900031ed9670105200063c32ce020a4000cdb639c041480019b0c738082900163e21970105200063db2ae020a4000c78655c04148001976c8b80829000336d8d70105200066c31ae020a4000cf3615c041480091d90cbaa42900039318c654852002c7643ac890a4000e67651852148001cb6a1b1ca0900971b1cb655412000637b2ee4a824000ccc63dc950480a70f90cbae80900031718d75d012012c3fc3ecba02400087d87d9740480018bcebb1e8090003175d763d01200066631ae5a024025c7a76d9740480a78f4ec32e80900039618c65d01200071db2ec9a024056cda76d8f40480039d4ec90e8090003179cf65101200c46e432e62024000c5f655cc40480018b8cab98809011b66d0173101200046fc3ec620240138dd87d8c40480f18f4ec32880900039618c6510120284ec432e62024000d5b655cc4048001ab0cab98809000372e097310120006e4412e62024004cdb625cc4048009b96c4b988090003729497310120236cc20ae62024000dcb215cc40480013b70fb188090003725cd5210120006ccb9c822024000dc9734844048001bc2e290880900971b9db658812012f35b06cb1024003c6e761962048001c98c632c409015b339db6388120004b7c2ae31024004de2105c6204800b0f90ea9acb880161fa1e525971000637b94a4b2e20028bf8750f64c40011df04b9ac9880063b20973593100146f41ee4b2620008dd83dc964c400b0f90eb2aa9880163b21d6250b1002e5a38ac8a0620008bd87d9040c400193ec8b98818802f2719173103100143fc3aa7b2c20008ef825cd65840031d904b9acb080123e20173596100245e43a86b24200b87e87d9554840018eeca38aa9080121f21d6554a100247643ac4a9420048fa80dd942840013e30038a85080132e1c164506100045ec3ec820c2077c7b761d52084001ab0e63aa410811a3e61b74482102365d326e890420059f0815d1208400b1f301b9eca88003175ce53d95100143fc3aa7b2a2000a7b8054f65440018dae5296ca880029d60652d95100053cc04a5b2a2000a3e8498f654400147b0931eca880028fe1163d95100051e422c7b2a2000a6f8258f65440014d904b1eca880028fa1262d95100051ec24c5b2a2000c3d741d365440014bd063a6ca880029760c74d95100053cc00e
  | 5 => 0xb271cf43591200145e43a86b224000c7775dc564480018e8ebb8ac89000335dcf71591200066a39ee2b224000c77751c564480018e8ea38ac8900032ddd071591200066bb98e2b224000cd4731c5644800196e8638ac8900032d50c715912002e73410e2b224005ce5821c5644800b9e30038ac8900022fe1d64191200055a40ac832240008df835da54480051b906bb4a8900028f61365951200146f41eecaa240008dd83dd954480010ff0abb2a89000237e0d76551200146e41aecaa240008f7815d9544800b1e902bb2a89002e1fa1f655512000c7d436e0aa24000cd863dc154480018f6ca382a8900033618c70551203f62f3b6cbb1a40008dd8799763480fb4bd0b32ec69000237e1d65d8d203e52f430cbb1a407bc5e7619763480f5c9d0432ec6900039360865d8d200046ec3cc9b1a4000a5e8599363480014bb0b326c69000237e1d64d8d200052fc2ac9b1a4000a5c8559363480015af02b26c690002b520564d8d200062eba8ebb1a4056ace821d7634800159b043aec69015ab3a0b74d8d2000566c16e9b1a4050ada80dd363480ad5b301ba6c69000387d5254d8d200052f42ce3b1a4000a5d859c7634800153f08b8ec690002a721171d8d202b567410e3b1a4000acd821c763480995b50038ec69015ab660071d8d200046f438a3b1a40008dd8714763480ad59d04286c6900531b1db655492001e363b2a8a924000ccc76d8d52480a7ad6ea382a490003179cf65985200062f398cb30a4000c5f655ce61480018b8cab9cc290003179d763985200062ebaec730a4000c5e7518e61480018baea31cc2900021fa1f65585200062e39ecab0a400087e8719561480018b8e632ac2901e71edc065585200061fb2ee8b0a4000c3c65dd1614800187eca3a2c2900030f19474585200146f436e6b0a4000c5f65dcd61480018b8cbb9ac29000237a1f63585200062fbaec6b0a4000c5c75d8d614800193ee9b1ac290003271d363585200046f438c6b0a4000c5f7518d61480018b8ea31ac29000327dd063585200064e3a0c6b0a4057cd97018c61480011ef0eb08c290002ad21161185200046fc1aed28a40028dc835da514804b8dce5b2ca2900031bd9572945200066631ae528a400196f8754a51480074d90ca94a2900031ed9670945200066c31ce128a40058f8865c251480019b0c6b84a29000a37a0f76545200046ec1eeca8a40018f9809db41480010ff0abb6829000e1f21576d05200046fc1aeda0a40028dc835db41480010ff0abb4829000e1f21576905200046fc1aed20a40028dc835da414800b1f10cb84829000e1fa1776505200043ec2eeca0a40028de83dd941480011bb07bb282900063ea1b70505200063c32ee0a0a4000cd863dc141480018f0ca38282900033618c705052001c3e42cec20a40028dc839d84
  | 6 => 0x5c5e422e6b0880008ef825cd61100031d904b9ac22000327dd1635444005e4e3a2c6a888004cd87058d51100091e90eb0aa2200033658f705444005e4f38ac7208800be967158e411000193ac6b84822000327dd1634844005e4e3a2c690880048f4875852110009974a1bb2802001327dc1635004005f4db82c6a008000c9d631c54010001976eca82802000a1fe1d53d96200162f39aa7b2c40048f8805cd64880091790ea1ac9100023de05765522002c7a40aecaa440048f8805d954880170fd0fb2aa91002e8fa13655522001c3f43eeab0c4000c6f20dd561880010ff0ab9ac31000e1f21573586200247c402eda0c400087f855da41880070f90abb483100021fe15765062001c3e42aeca0c40048f8805d94188009b34c8b9881100136659173102202366cb12e62044048d98415cc4088001b32e72088110003175ce53d95200053cc04a7b2a400287f8754f654800147d0831eca900028f61063d95200070f420c7b2a4000e1d8418f6548107cb30031eca900039618e30d952012d3c43261b2a4025b68824c3654804b4f301ba6ca900030f5d074d95200051f420e7b2a4000a3d841cf65480018bae639eca900029ea0073d952012d3cc00e7b2a4000a5e839c765480014bb0738eca900029b60871d952012d3cc00e3b2a4000a3e84cc7654800147b0998eca900021fa1c31d95200043ec3863b2a402587e87cc365480010fb0f986ca900028fa1030d95200051ec2061b2a4000c5c65dcd65481059b6e031aca9000a37a1f73595200062fbaee6b2a400087f855cd65480011df04b9aca900023ee0173595200046f438e6b2a4000c5f751cd6548001998e7b92ca90003361cf70595200043ec3cc632a400087f8758c65480014df04b18ca902069ee0163195200051f420c632a4000a3d8418c6548001c3d08318ca9000387610631952040727390c632a4000e4d7218c6548101c9e42318ca902039660063195204072d900c632a4080e4c2018c6548101cb040318ca901ee9ea1a30195200072c31c6032a4053a78864c06548001cb0c6980ca9014eda20930195202be6cb80c7b2240048ed82dcf64480031f301b9ec890003179cf65991200062f398cb322407fc797019664480018becab9cc8900031719573991200062f3a8c73224000c5d7518e64480010fd0fb2ac890003171cf65591200043f438cab224000c5c7319564480018becbb9ac8900031719773591200062fba8c6b224000c5c7518d64480018eecbb8ac8900031d19771591200066a31ee2b224000c77651c564480018e8ca38ac8900033518c715912001c3f43eeab2240028de87dcd64480018beebb9ac890003171d773591200043fc2ae6b22400387c855cd64480011ef02b9ac8900163d20573591200046f438e6b224000c5f751cd64480018b8ea39ac89
  | 7 => 0x79800c965d00014f700b8acba000297a0c71597400052ec18e2b2e8000c75711c565d001747d0998acba00028f61331597400043f43862b2e800087d870c565d00010fd0f90acba00021f61f21597400053d40042b2e8000a798008565d00014ef02b82cba00029d20570597400043f43e60b2e800087d87cc165d001747d08182cba00028f610305974005d1f42640b2e8000a3d84c8165d010fd1864a1ac5a002e3ba1f3258b4001c3f42ee2b16800087d85dc562d00030f90eb2aa5a002e1f217765474002d3a40acaa8e8000c7965dc151d00018f2ca382a3a00027a60870547400061eb2ee8a8680028de87dcd629000199d05b9ac5200033360b7358a400046f438e6b1480008df835d952900051b906bb2a5200123e2017654a400247643ac4a9480468f986dc142900099e0e0b0a83200032ed8d70106400065cb1ae020c80008df835d921900051b906bb2432000a1fe1d53d954000636b94a5b2a8000c74651c565500011df04b9acaa00063b20973595400047bc0ae6b2a80058f4815cd65500011f700b9acaa00031ddd471595400065bba0e2b2a8000c74501c565500019e0e3b82caa000b279cd43d89400043fc2ae3b12800387c855c762500171f50db82a4a01223ea1870509400056ac18a3b0a80028f7874c761500014ed0b90ec2a0002bc60021d85400047bc3ac230a8000a74855846150017972e1a18c2a000b279cd431854005e5cb828630a8000caf435c8615000195a86b90c2a0017398c5721854002e75082e430a8005ce9105c86150001d2a86988c2a0003395c931185400053b42e4230a8000ce572c84615001737108b84a2a00173c185709054005c3fc3acb2828000a7481596505000187ecbba2a0a00023be09735944000c76412e6b2880048f8805cd65100018beeb3aac620002b3e097558c4000566412eab188086adb805d563100095b100baac620012b6a027258c4027d6cc04e4b188000a5e851c963100014bb0a392c62002ea7a107258c400c54ec20e4b188000ad6811c963100015ab02392c620012b6a007258c400c56cc00e4b188000e4f5294963100095b501292c620002b66025258c4005d4f420a4b188000a9d8414963100095b500292c620002b66005258c4005d4f426e2b188018a9d84dc563100014bf0ab8ac620002972157158c4042d4fc22e2b18800ba9c845c5631000159f04b8ac620002b32097158c404256dc02e2b188004ad8805c563100014bd0a38ac620002976147158c4005d4f426a2b188000a9d84d4563100011bd0e28ac6200023761c5158c400052f42e42b188000a5d85c85631001753d0990ac620002a76132158c400256d40642b188000ad980c8563100095b50010ac620002b66002158c400243e43acaa9080048ec8758952100010ff0ab9ac22000e1f21573584400
  | 8 => 0x9992c020802ae61332580410074ca1c64b0082008fa870c960104011f30e192c0208029ea1432580410053cc2864b00820baba840c9601040157308192c020803a650c325804102d7940864b008200af1810c9601040bce0a2a8ac02082eaea1331580410055cc2662b008200e9943cc56010401d328698ac0208029ea1721580410053cc2e42b00820587c8754d658840517f0ea1ec9108023ee0173592210247c402e6b24420387e85dc164884010fb0bb82c9108163d20576552210047dc02ecaa442048f8805d9548840b0f90eb2aa9108171d1c5655522102c76c16e7b2a4200c78651c1654841717d0fba2ca9080a37a1f73595210064fba6e6b2a4200c9c74dcd654840117f08b9aca9082e2f21173595210047dc02e6b2a42048f8805cd65484011bd0e39aca9080327dd073595210064e3a0e6b2a420287c8754d65484058b8e6a9aca908032edd370595210065c3a6e0b2a4200cdb73dc165484019b0e7b82ca908031edd470595210065dba0e0b2a4200cb8741c165484019b6e6382ca90803361cc70595210063daa0e0b2a4200c7b531c165484018f2a6382ca908133aa08705952102674c10e0b2a4200c78511c1654840187aebaa6c89080a2fe1d43d91210043fc2ae1b22420387c855c3644840193ec8b9cc89082f2719173991210043fc2ae6b22420387c855cd64484011df04b9ac8908023ee0173591210247c402e6b2242008bf87590644840b1d90cb94a8908022fe1176551210046fc1aecaa242028dc835d954484011f700bb2a8908123e201765512105c3e43acaaa2420ba3c8459554484014f100b2aa8908063da1b71551210063ab28e2aa242009d5831c554484030ff0eb2ca2908029e201659452100637b2ee4a8a4200ae98214360484011f70eb00c0908029e21560181210245e43a86b24a00095d831c5549403b0fb0db82a9280025e6037550a5000477c12e6b0ca0018ec825cd619404b8dce4b14a3280421fe1d61946500943fc32e128ca005c76615d621940012f700bac43280031bdd562486500247a43ac290ca0008df835cb64540051b906b96c8a80022fe1d64191500055a40ac8322a00187c855c762540011ef0eb08c2a8002ad211611855002c3e42cec20aa000c3d75d9041540018eaebb0882a80163e21970105500065db22e020aa000cf3615c041540170fd0f29acba000317dce53597400143e43aa6b2e8000a7b8054d65d00018dee5292cba00029e602525974005d1f424e6b2e8000a3d849cd65d00018bee739acba00029ee0173597400053c402e6b2e8000c6f729c965d00014ed03392cba00029d60672597400053d404e4b2e8000a79809c965d00010fd0e192cba00021f61c325974005d1f42064b2e8000a3d840c965d00014ed02192cba00029d60432597400053d40064b2e8000a
  | 9 => 0x525884102c7743e64b10820baae84cc9621040b1d90e992c4208031bdd6755884105d56422eab10820baae849cd621040155b0939ac4208029ba14735884100536c28e6b10820baae841cd621045755b0839ac420816b9a04735884115d72c08e6b108200aea801cd62104015d30039ac42082eaba12535884100556c24a6b108200e4f5394d621041755d0829ac420802ab610535884102d73408a6b108200ae58114d621041755f06a1ac42082fa3e0d435884100747b9a86b108200e8c7350d621041755d0998ac420802ab613315884100746a1e62b108200e8d434c562104014df0ab82c4208029b215705884105d56422e0b108200acf835c1621040159906b82c420816b9205705884105d57426a0b108200aad84d4162104011dd0e282c4208023b61c50588410053742e60b108200a6d85cc1621041755d09982c420802ab613305884100746a1e60b108205ae681cc162104015cb03982c420803a350d305884105d5742060b108200aad840c1621040b0f90eb2aa4208030f597745484102c7643ac4a908200caf74589521040b4e902b2aa2208172d94776504410065bbb2a2a0882048f8805d660104091f100b9cc0208021fe15729804101c3e42ae530082008df835ca60104051b906b94c0208123e20172980410053d42e613008200a7985cc260104014f50b39cc0208029e61673980410072da9ca73008200a7b855ca60104014f10ab94c020802b6e0d72980410056c41ae53008200e6b5294a60104091f50e194c0208023e61c32980410053d428653008200a79850ca601041757508194c020802ae610329804102d79408653008200af1810ca60104175750998cc020802ae61331980410053d42e433008200a7985c86601040593ce6a1ac02082eaea13505804100575410a0b008200ae982141601040b1f50f982c0208029ea1730580410053cc2e60b00820baba84cc16010401d3287982c0208163e21d30580410074ca1a60b00820baba840c16010417575093aac020802ae612755804105d5c422eab008205af0815d560104015d5043aac020802ba608755804105d5c426e6b008200a7a859cd60104014f30b39ac02082eaea1273580410055cc24e6b008205af2819cd60104015e30339ac020802aee11735804105d5c422e6b00820baba841cd60104015730839ac02082eaea1253580410055cc24a6b008200e5b5394d60104175750829ac020802ae610535804102d79408a6b008200af18114d60104015710ea1ac02082fa6e0d43580410074d39a86b008200e997350d6010491970e9b92c02082eaea1272580410055cc24e4b008200a7b855c960104014f10ab92c02082eae21172580410056dc1ae4b008200ad8835c9601040b5e102b92c0208039ad4a525804102d7940ca4b008200af1819496010417575
  | 10 => 0xb04a2028bf8750f64544011bf06b96c8a880a3720d72d91510055d40485b22a200a3d8510b645440117f0eb20c8a8802ae201641915119cbb430e2aa2a205c76861c5545440baad0638aa8a88175560c71551510047dc02e9b12a2048f8805d362544014e902aa6c4a880a3ee1d30d81510047dc3ac0302a200ab88458060544014e902aa0c0a880237e0d72181510146e41ae4302a204ce8205c860544018df0ab90c0a88031b215721815100637aa2e4302a200c6d545c8605440199f06b90c0a88033320d721815100637a9ae4302a200c6d535c860544018d8a2b90c0a88133a101721815102675182e4302a204cea105c860544018dae5288c0a88033a5c9301815100674b9640302a2008ef825cd65d04031d904b9acba08023ee0173597410247c402e6b2e820187c8759552d04011bf06b94c1a080a3720d729834102c3e43aa6b2c8205c74715955490405938e6a1ac52080237e0d7654a410146e41aeca9482008fb805d952904091f100bb2a5208061fa1f6554a410043fc2ae6b04820387c855cd60904011df04b9ac1208063b20973582410062eb9ca7b2a8200c78651c165504010ff0ab9acaa08023be09735954100c76412e6b2a82008f7815cd65504011f700b9acaa08123e20173595410063dba8e0b2a8200cbb741c165504019e6e2382caa08061fa1f65549410061fb2ee8a8a8200ae98214360504014f50b986c0a0802ae61030d81410047dc3ac03028200a788558060504014f50b980c0a08163d205735944102c3f43ca6b288200c5f7394d651040b0f90ea9aca208031bdca525944105d1f424e6b288200a3d849cd65104018bee739aca208029de05735944102d3a40ae6b288200c6f729c9651040b4ed03392ca208029d606725944105d1e422e4b28820087e870c965104010fb0e192ca2082e8fa1032594410051ec2064b288205a76810c965104014eb02192ca208029ea0032594410053cc0064b28820ba3e84cc5651040147b0998aca208b61fa1f21594410043ec3e42b28820ba3c845c1651040b4e902b82ca208029ba08705944100536c10e0b28820087e87cc165104010fb0f982ca2082e8fa1030594410051ec2060b28820ba3e84c81651040147b09902ca2080317dd67558c4144d6bc0aeab188205ad4815d563104014bd0a392c620802976147258c4105d4f420e4b18822ca9d841c9631040b5ad02392c6208b2b56047258c410056d400e4b188200ad9801c96310401c9ea5292c620816b5a065258c410056ac0ca4b188200a5e85c8563104014bb0b90ac62080297a177058c410052ec2ee0b188261a9f845c1631041753908b82c62082ea7a107058c411654ec20e0b188200ace82141631040159b04282c62082ea7a132058c410054ec2640b188288e8e3250d6210511d1864a1ac4208031bdd7
  | 11 => 0x80000200d0960240000000400c020150160a8160280040fc0400001a08c0380000404800811002008010000180100700d008004040000100000100401e028000190020840180100e000160050020000003503c004000150020600380900201c088000080080200200202400004004004018060020080900b00e1500080d0020480101300a0201e8080100d8050000060000000600c0b40203c0060240100e00404c078040040340380000002800804000000010040040440080200c0500000e0000000000001a00c0180300403c038000120600280800000c0200200a000000090060000001304a014008140021000c00900003c0002b014044028010900080000b00000400800006010018130000000f80d0020100002e01600c038060020140800100e0000280d0040040200203a0d40c0000220100100600e010080000000040200000e0100181e000080030000260b00881600200002830000008ef825cd61950031d904b9ac32a00237e0d72982540146e41ae5304a8028f8874c160950014eb0a18ec2aa0023de1d611855400578402c230aa800c5f525cc615500b9a902b98c2aa01717d45731855402e2ea8ae630aa805cd6215cc61550018b8a0b98c2aa002ad61331185540066ab9e6230aa800a7985cc3605500157308186c0aa0023ee1d60181540057840ac0302a800a7985cc0605500117f0eb20c8a90025760c715515200c3ec2ee7b0aa4038ed82dcf61548058b8e6a9ec2a90023de1d61185520053cc2e61b02a400ab9840c360548011f70eb00c0a922e9ee1560181520056c41ac0302a4048f8805cc60548078dae4a98c0a90022fe11711815205c5e422e2302a400c74515c460548099e020b88c0a90029e61730181520062fbaceab1e8400acf825d563d08e559904baac7a102ea7a137158f421ed4ec26e2b1e8400a5f855c563d08014b90ab8ac7a1002b3e097158f4239566412e2b1e8400a5e851c563d08014bb0a38ac7a100237a1c5158f420046ec38a2b1e8400a5e85dc163d08014bb0bb82c7a11cab3a0a7058f4200566c14e0b1e840ba9e841c163d087b53b08382c7a11cab3a085058f4200566c10a0b1e840087f855c261d08070f90ab84c3a10021fe15735874201c3e42ae6b0e8402c9e7350d60d081757509a82c1a1002ba60850583424561fbaee8b2a84008ef825cd65508011ef02b9acaa10163d20573595420047dc02e6b2a84048f8805cd65508018decbb92a8a10023de1d61185420164f39a8630a840bcad7250c61508010ff0ab80c2a100e1f21570185420063dc2ae030a8400c78855c0615080197708b80c2a10032e21170185420065da1ae030a8400cb9435c0615080b9d642b80c2a10173a48570185420047dc3ac0302842887d86dc552944014f30b984c1288029e61730582510055cc2060
  | 12 => 0xc8378e4019823a590fc004a989ed991a139501f99139221bc19023c981a8b8372b90d005a2522cd0560309cf9939889362722d02f49b4adc9a62ca9cf2c12c4008a4393528db0e06f90f8001d22f114a90c8489af13096e9ee88c9272c60bda8c00021e1bea2d9538479e4a4e18ba382c686d83c83c14583897aa4f168a50b0b8f114d90d2611c78dc03f1068942a1206980029a550ab1249098f917890a91c06a8af2f180b9c3ab490881c288ad9156800173a9f93a90204e05e2de1b1a31aec9af97b89518dad3b05a1a9e207c802928a0422fafc2e81f118997508008d85b02d287aab2e11bd84a8000e0946a990de0000002ea85ea791e71cc1a29fa8d925da292f6a4b832a86a58a0ba2b2220600872c78001e329180000016f2e1855885077aa49c50001338d32d188b1f888c1a72160d200030c074b1c9ffaba9e40101c01d5884126946045af5831190a63aab8ea13180010280022c2730651ab0f40002cc04101d00019d104318a9aaae1f482025c80000022a8001e023918ca83ad419aa799ae25d20c01f0508000000000000580000000c62282f2222a5f2b79b32c50003249322148aa10800001584f2169b88510e1ac894100010501122c8788611ce2d4a7c0a5a95a6d03420391491116788630002123d9e10c2800245200194984a541e629227caed03210c2bb2309f1ab28000d4825800000000012ad98d380016c0142788dd29d24715e800182aff8ae0d88e124080022e8003101b700018680598f2e480000000c80020581b0000a615f0ce8002fb8000ffa7024400000024d8001438fa1f7039003aafaa08001671aa00f252800257a110002a6b1e15793b00991612a800199260109121aac8c40b1a0216496d000007000000000150080080102a0180040e00b0440400480300805000020002024000020000100204b008198028000080000102c00000401832004058058010020000000c02400404808000040020140240400c8010000000181400000800019000010040010000ac0102f04e0580280b00000c000000080440000000009c020070000740101f0081540783300c0000d81207e034000000460280480000e0000880500001c0000200200001802000028000090100101080004a008000270420400080100000c00008000078030000060100280d01e080008040740000380102800001804010000000030000200000000c008020100100000180100009c000020020000000b0120100080505e008010010140480280a004030000080040f000000002014008270040080200301200403825004000000000340040000d01e05c000000040300080302404c00009006008000180a200000810006028008000020400000d0140180080000002400807022008000040560080e01400a0080500007002c0081900200007801
  | 13 => 0xa408300031f1a981881f8e29b618f9bb8fb29b88f2459c42749cd0000000002178fd00004c0e98001db1932df04cb26970acb2fb00000029b1480000001f92b52d79bf80008192912f31c134000000321a741a09dd26500012f85b96aac388589a3171fda8ca0a2708001771a8a1880022d0b38002ad2048fd94c25a29626e11987b2f31001d19d50e3ac2acf8000d7084b1d1760002f80cc8690429bd2678922158a919f121320ac487410b27b06987f2890bf0eeb0987f8719859550dead8a448002320433031b78bf8001c924b230039a079239b68f5af028f0cda030409102549b5a3b854800117b1b1de13d21700021c0d68002e9958af51402a7057800323000000082a1b0358888b0a32a5e8369548a11108781fe01eb1999b1f22f89049421d106304d8e8a41212ac8000294a71820b0a220aa00000ee2330cba7f8000fb824b179781ed25380032896915bb10a6888a8000002b08001a43050000108001602ceb020a1a84a1d2a515d247ae304a2f2ae407311a9620efa1c95331a01691402da132482510e21192deab20978000569a5289b011e09b100020a87d1cb1fe8a696080c13d80e9f41c5afc8000b627382b8000000000002912bf80026c80032924ea2880019400000080002518e96d8ac99ba3aae60e923f24c3220882e68eb0000c5a311d680000000004fa4d05f000226b119d48060b68278001570ac1c88000000002b12eb824201859acf15a19982680000014f8001b3ab72ad97306d0cd2009dc8992fa1fc8fe22120600030fb008ec00001b9841a68e78000a315b0001be2b680014a107a6f9ec80023b0000ae93e8002fe0c006e27ba9508e00000000000019726c065a5e0000002771ef0288001d78002ca0000f71d9963a6604027280017f868a232a40be80a8000292070ec8000001f621012a1261a184b80305d1310000002a780d8002092a8a7d87a9da80029e04eafe9981749408160d2ac9137046aee0018c68751b900012321f8002d291e2a3248a65a36800041a691ceabc9ad10e9e6a6a285a0e8002e2094a401eb1e78640000001cc83d000000101000000076b141b50fc8c3000284290a1d8001d80000003110b200023fab38808221da1911f0ace2618bb861b042fd90389698a0aa88220d8cb06698528ea3c062a6495faf9a758190af97e28a9a91839349db8cc10e26aa6da969152b8ad61662f78e31ad8180b91860bc9a32c59fd27e2d71642be2e08001332671451ee26f0fa8ce0000d52cb8350d42f9142b202c9aef9168b4a572db8f031aa4a8608ad1c080022a16329002eb1f82a82c11e8e6a582201e19768001121388708c8155b038caae280000000012980019ea2e17a0eba7d1061e28000002252432cc89d97211daa204525a9ca2120f796caee8fe90ba9f08a0b98f6a8d32811ca971f51b
  | 14 => 0x44a141df1d08a00b80a8900951b2708b97c18a94e3162a987e86b2aa1252e7a7683f8c38770303150422f614705905503e8cf16fa2619a0738c901e2361fb01a280a631698b5b1d94187b936a46a398e71dd9f5aeb27792099d9128002ea0b101ca42a781b29758811e52ef17e8a0a249b0064b0489c87992baba2dfaa28000002358001442e50001058001628638000e4ad107d80000023eac22a183aaae8bd17b2da0ab9df8f4abc1398da8c981186c9bf00000000018b237a0c8570980000681812422ff1890e800000011b3192b306c0c512000d0970002d68001e91489c63261f680032396a25f82f80028807e1ac00e14e80000029eafa8000000ca09895a8b41a113791187a1b420d18d13b99217ca080c70002940541ae8ba8000000001f780000028320b000132a49a6219cb07a979b81c2a931cb9d41cdb128a48052271a0083b0919e1c1915a7e8471c80e51c11ea9960228000c09492b993e159000009187817a0e00014f0002e3b14827327b0f1a80001e9a62a109eb89d03a0001d00000002c729991809306f09e18815c000166a829ac82c91f1c211a15808fac012d949abd0c19a5ae71ab9c30001968bb20fb068000002598000000000000000000f81710000000963130bc2f38000001f30002bd8531d70c20c786b95e10a00f89084626428f8f88f08071c4a9c2dd13ca5c1799560121aa80000021f04b00a1a22af12e93028211b9a493813f13a0001f2a8b00030d30da4f85c86795429a0df8000a980100028184d093aed80023701ab08000161a9380000005c2bf00006a0000d10000000000000000002a3b0e8000170002c18d79512ec3250918000898000e009c0001e5b12000171a558d6013806a0f30c800198800076033a8a000122a1a2490000000b2a56ae90000000f314b8002b59a39929d398e1de9e3852853afd043b241b20d58001d92d82152f42aa8002d500000006200000022380012c8001188000000000000588001ea11d0b00868002c3209800195a0880012e1131359e8ab18498a2a180da0a78db834a801832418792a902e1c68710ed04482829299fa608b50000ad8001d60000003138000000000000149792cda3a2e887c2340003211728df2b600030b0891fb9dc0670ba13f9951fa165a34a29a8e05a8000f9895ab81ba91f8ff0c123382f125b1e8a820295d8000759d32f716109b31b8d0af0a668380f50151ca8c490198c0f60000b88522519a780019c0000002560000041280000218003071d890dada8728002d0a9cab41030360700e58000000000000001f80000000000001f00002d31520000000000000000000082532762bb8002b011700003b90f25b1bb1740d1aa60878b71c994d28116b83312b1b980003b0003168000ef0490000002460001870000998000000000002a589f8a7235
  | 15 => 0xcf8f221196509ba3e14c8079702e012d26b000051ae584403da7526828618225b95ca7aa871478a3b181681072d20b3127aa80929430f3abe8262c0a9d8e6322aac150977b0a92c0b789e9b089a9ec0dc9fc0c895285026ba710eab259c70d98000a52d589116e29802b0002698dd88e80022580000000000000027a00000022ba1b80023880028503e00006614b16b02a12430897d17f01327f15989f2012ddadb26e9efa3d3061ff08d2052218f1adc1f380b21e831b02a2f2500ed99780024ca198d809024a05db1597d98093906e93c0db30181da279ba1e805fa241d28f2a190be0480230720a20021
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x3a00a10c10025841d346c70c445459c2644b99420c48a00780230000024000868f00003140048f8168010201b3cd089000144d92141731855400515644505cc61550014559314571181520052664c845c061508014649155172181510051364c515c86054511685911cd4358841005a26407350d6210401a85436073058841005a46467350d60104018998750c3258041006a450d810c960104014599314470595210051c241651c55448401c85435c93118540006866018418f6548001a1980610631952000586650634c06548101a488218d301952000616218655cc404800154995209731012000570644825cc404800154995c85731012000706d95735c06444001c18655cd70191100058564c5119151440018a864608705451005e261d9831914044001a186560c64501100070c194641c5404400159193190715011000427660731912044001299981cc6448110007061d47319120440016a19194864481100058a657211912044001c28751d16244010
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x10800320882650634c06548001a0832b26320e2a022000c06660751cc6448110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x2
  | 6 => 0x4b
  | 7 => 0x4c
  | 8 => 0x4e
  | 9 => 0x124c
  | 10 => 0x138c
  | 11 => 0x5
  | 12 => 0x94b
  | 13 => 0x94c
  | 14 => 0x94e
  | 15 => 0x124b
  | 16 => 0x124e
  | 17 => 0x138b
  | 18 => 0x138e
  | 19 => 0x98c
  | 20 => 0x98e
  | 21 => 0x128c
  | 22 => 0x128e
  | 23 => 0x10b
  | 24 => 0x10c
  | 25 => 0x10e
  | 26 => 0x130c
  | 27 => 0xa0b
  | 28 => 0xa0c
  | 29 => 0xa0e
  | 30 => 0x130b
  | 31 => 0x130e
  | 32 => 0x180b
  | 33 => 0x180c
  | 34 => 0x180e
  | 35 => 0xa4b
  | 36 => 0xa4c
  | 37 => 0x134b
  | 38 => 0x134c
  | 39 => 0xb0c
  | 40 => 0xb0e
  | 41 => 0x140c
  | 42 => 0x140e
  | 43 => 0x28b
  | 44 => 0x28c
  | 45 => 0x28e
  | 46 => 0x148c
  | 47 => 0xb8b
  | 48 => 0xb8c
  | 49 => 0xb8e
  | 50 => 0x148b
  | 51 => 0x148e
  | 52 => 0x184b
  | 53 => 0x184c
  | 54 => 0x184e
  | 55 => 0xbcb
  | 56 => 0xbcc
  | 57 => 0x14cb
  | 58 => 0x14cc
  | 59 => 0xd0c
  | 60 => 0xd0e
  | 61 => 0x188c
  | 62 => 0x188e
  | 63 => 0xd4c
  | 64 => 0x104b
  | 65 => 0x104c
  | 66 => 0x194b
  | 67 => 0x194c
  | 68 => 0xa1254
  | 69 => 0x98954
  | 70 => 0x98d
  | 71 => 0x128954
  | 72 => 0x128d
  | 73 => 0x95314
  | 74 => 0xa0954
  | 75 => 0x94a14
  | 76 => 0x99254
  | 77 => 0x129254
  | 78 => 0x128994
  | 79 => 0x10994
  | 80 => 0x98114
  | 81 => 0x180994
  | 82 => 0x99814
  | 83 => 0x14b
  | 84 => 0xb0994
  | 85 => 0xd4994
  | 86 => 0x12cb
  | 87 => 0xcb
  | 88 => 0x198b
  | 89 => 0x128114
  | 90 => 0x181294
  | 91 => 0x129814
  | 92 => 0xa0114
  | 93 => 0x149314
  | 94 => 0x148114
  | 95 => 0xa1314
  | 96 => 0x181314
  | 97 => 0x29314
  | 98 => 0x134a54
  | 99 => 0x150e
  | 100 => 0x1354d4
  | 101 => 0x135054
  | 102 => 0x140b14
  | 103 => 0x2cb
  | 104 => 0xd0b14
  | 105 => 0x19cb
  | 106 => 0x28b94
  | 107 => 0x148b94
  | 108 => 0x149854
  | 109 => 0xbd4d4
  | 110 => 0x154e
  | 111 => 0xbd054
  | 112 => 0xd54d4
  | 113 => 0x1a8b
  | 114 => 0xe8b
  | 115 => 0x8e
  | 116 => 0x20e
  | 117 => 0xd5054
  | 118 => 0x160e
  | 119 => 0x14053
  | 120 => 0x15313
  | 121 => 0x15393
  | 122 => 0x152d3
  | 123 => 0x140d3
  | 124 => 0x12d353
  | 125 => 0x12c153
  | 126 => 0x1340d3
  | 127 => 0x14a13
  | 128 => 0xc153
  | 129 => 0x15693
  | 130 => 0xd993
  | 131 => 0xd353
  | 132 => 0x11394
  | 133 => 0x11494
  | 134 => 0x11994
  | 135 => 0xe9813
  | 136 => 0xe8293
  | 137 => 0x299d4
  | 138 => 0x1a9953
  | 139 => 0x15353
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2124
  | 6 => 5060
  | 5 => 1619
  | 4 => 37
  | 3 => 3
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
  | 7 => packedAt gbK7 (87084+((h/708+packedAt gbK7 (78588+(h % 708)*12) 12) % 3730)*13) 13
  | 6 => packedAt gbK6 (264798+((h/1686+packedAt gbK6 (242880+(h % 1686)*13) 13) % 7348)*14) 14
  | 5 => packedAt gbK5 (101450+((h/539+packedAt gbK5 (95521+(h % 539)*11) 11) % 1943)*12) 12
  | 4 => packedAt gbK4 (2662+((h/12+packedAt gbK4 (2590+(h % 12)*6) 6) % 45)*7) 7
  | 3 => packedAt gbK3 (245+((h/1+packedAt gbK3 (243+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff0f81f03e0fff007c1f803f0d9d3f1e49f267
  | 1 => 0xfff001fffff01fffffe0003f326223fc7e3f87
  | 2 => 0x3fffe003fffe0007fffffc0c383c3e38fc3f8
  | 3 => 0x3ffffffc00000007ffffffffc03fc03f003ff
  | 4 => 0x3ffffffffffffff80000000fffc0003fffc00
  | 5 => 0xfc0000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x570390b21646b5092c9a8295048d0f0e48f263
  | 1 => 0x993000544a50864756a20526102221741a1785
  | 2 => 0x5154a2002d6cc41218d32984438143a08f42a8
  | 3 => 0x82a9556e80021024630c5638bc02b403700156
  | 4 => 0x2ce798b318b18b800081810ef540003e5a800
  | 5 => 0xe000600c010c00c002106020fbfbfad8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefac8fcecf800feeefac8fcecf800feeefac8fcecf800feeefac8fcecf800feeefac8fcecf800feeefac8fcecf800feeefac8fcecf800feeefac8fcecf800, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37347
namespace PEqualNP.Outside.L_meta_37347
open PEqualNP.Outside.L_meta_37347.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
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
theorem bs2_4_96 : Interval s2Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 99 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96))
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
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
theorem bs3_4_512 : Interval s3Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 539 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96)) (concat (concat bs3_4_128 bs3_4_160) (concat bs3_4_192 bs3_4_224))) (concat (concat (concat bs3_4_256 bs3_4_288) (concat bs3_4_320 bs3_4_352)) (concat (concat bs3_4_384 bs3_4_416) (concat bs3_4_448 (concat bs3_4_480 bs3_4_512)))))
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
theorem bs3_5_640 : Interval s3Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 664 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 (concat bs3_5_512 bs3_5_544)) (concat bs3_5_576 (concat bs3_5_608 bs3_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := (concat bs3_6_0 bs3_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 37 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1600 : Interval gbAtlas 5 1600 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1619 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))))) (concat (concat (concat (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960))) (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184)))) (concat (concat (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280)) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376))) (concat (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 bgb_5_1600))))))
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
theorem bgb_6_5056 : Interval gbAtlas 6 5056 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5060 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))))) (concat (concat (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)))) (concat (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056))) (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)))))) (concat (concat (concat (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376))) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696))) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))))) (concat (concat (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016))) (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)))) (concat (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336))) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496))))))) (concat (concat (concat (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656))) (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)))) (concat (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976))) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136))))) (concat (concat (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296))) (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456)))) (concat (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616))) (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776)))))) (concat (concat (concat (concat (concat bgb_6_3808 bgb_6_3840) (concat bgb_6_3872 (concat bgb_6_3904 bgb_6_3936))) (concat (concat bgb_6_3968 bgb_6_4000) (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)))) (concat (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256))) (concat (concat bgb_6_4288 bgb_6_4320) (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416))))) (concat (concat (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576))) (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736)))) (concat (concat (concat bgb_6_4768 bgb_6_4800) (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896))) (concat (concat bgb_6_4928 bgb_6_4960) (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056))))))))
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
theorem bgb_7_2112 : Interval gbAtlas 7 2112 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2124 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568))))) (concat (concat (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696)) (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824))) (concat (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 bgb_7_1952)) (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefac8fcecf800feeefac8fcecf800feeefac8fcecf800feeefac8fcecf800feeefac8fcecf800feeefac8fcecf800feeefac8fcecf800feeefac8fcecf800
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074632 * 2 ^ 32 + 4243388416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37347.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,5]⟩,⟨.and,[0,5]⟩,⟨.and,[0,2]⟩,⟨.or,[1,8]⟩,⟨.or,[3,6]⟩,⟨.and,[2,10]⟩,⟨.and,[0,10]⟩,⟨.or,[7,9]⟩,⟨.or,[4,12]⟩,⟨.and,[13,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4243388416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4243388416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37347

open PEqualNP.Outside.L_meta_37347 in
theorem PEqualNP.Outside.L_meta_37347 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4243388416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4243388416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
