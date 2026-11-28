import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37131.Model
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


end PEqualNP.Outside.L_meta_37131.Model

namespace PEqualNP.Outside.L_meta_37131
open PEqualNP.Outside.L_meta_37131.Model
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

end PEqualNP.Outside.L_meta_37131

namespace PEqualNP.Outside.L_meta_37131
open PEqualNP.Outside.L_meta_37131.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x3229e00001988400001ae00000028567000000000480d0000c000000000aad60002901402fe4000880003190001b0ab00000070602c016000000000000c00000966cc0dae010397000000000001000c3810004001fe43fd43fc43ff32fe32fd32fc32ff31fe31fd31fc31ff21fe21fd21fc21ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x241fe30483fa60907f0c120ff90241fb20483fc40907b88120ffa98417f53083fca6105f94c20ef298415e53083faa6105f54c20eea98415d53083f8a6105f14c20ff21841fd43083f886105f94820ff99041fe32083fa64107f0c820ffa8841fe51082fca2107d94420bb28841fd51082faa2107d54420baa8841fc51083fe62107f8c420fe98841fc31083fe42107f88420fe90841fc21082fca0107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fc87887f50f10fe21e21ff52c42fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff32c43fc65887f4cb10fe19621ff31c43ee63887f8c710fb18e21fd31c43ea63887f0c710fa18e21ff21c43ee43887f88710fb10e21fd21c43ea43887f08710fa10e21ff30c43fc61887f4c310fe18621ff20c43fc41887f48310fe10621f753c43eca7887d54f10fa29e21f643c43ea87887d10f10fba9621f652c43eaa5887d14b10fb99621f632c43ea65887d0cb10fb98621f630c43ea61887d0c310fb90621f620c43ea41887d08310ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ff21c21fd43843f887087fd4a10bfa9421fe52842fca5087f54a10bea9421fc52842f8a5087fcca10ff19421fd32843f865085f54610baa8c21ff31843fc63087f4c610fe18c21ff21843fc43087f48610fe10c217e50843fe61087f8c210fe98421fc30843fe41087f88210fd10421fd20843f241087f08210ff88421f710843f621087fd4d10bfa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887f90d10fea1a21fc43443fea4885fd4910ff292217e52443faa4885f54910fe292217c52443fe64887f8c910fe99221fc32443fe62887dcc510ff18a21f631443fa62887d4c510fe18a21f431443fe42887dc8510ff10a21f621443fa42887d48510fe10a21f421443fe60887f8c110fe98221fc30443fe40887f88110fd10221fd20443f240887f08110ff88221fb10443fc20887d84110fba9a21f653443eaa6887d14d10fb21a21f543443e886887dd4910fb29221f552443e8a4887dcc910fb19221f532443e864887dd4110f9a8221f730443ec60887d4c110fa18221f720443ec40887c88110fa90221f120443e840887fd4c10bfa9821fe53042fca6087f54c10bea9821fc53042f8a6087f90c10fea1821fc43043fea4085fd4810ff290217e52043faa4085f54810fe290217c52043fe64087f8c810fe99021fc32042fca2085d94410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xf31cc3fc63987f4c730fe18e61ff21cc3fc43987f48730fe10e61ff40cc3fea9185fd5230ff2a4617e548c3faa9185f55230fe2a4617d538c3fe871877d0e30ff21c61fd438c3f887187710e30ffa9461fe528c2fca5187f54a30bea9461fc528c3fe85187f90a30fea1461fc428c3fe65187f8ca30fe99461fc328c3fea3187f94630bf28c61f6518c2eca3187f54630bea8c61f5518c2eaa3187f14630ffa0c61fe418c3fa83187f10630ff98c61fe318c3fa63187f0c630ff90c61fe218c3fa43187f08630bf28461ff408c3fc81187fcc230ef98461fb308c3fea8985fd5130dfaa2613f544c3fca8985f95130feaa2617d544c3f8a8985f15130de2a2613c544c3fe86987f90d30ef21a61fd434c3ba86987f10d30ffa92617f524c3fca4987f54930fe292617c524c3fe84987f90930fea1261fc424c3fe649877cc930ff19261fd324c3ba64987f0c930ffa8a617f514c3fca2987f54530fe28a617c514c3fe82987f90530fea0a61fc414c3fe62987f8c530fe98a61fc314c3fe42987f88530fe90a61fc214c3fe80987f90130fea0261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061be540c27ca8187f55030beaa061bd540c27aa8187f15030be2a0617e530c3fe861877d0c30ff21861fd430c3f886187710c30ffa9061fe520c2fca4187b94830b729061fd520c2faa4187b54830b6a9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830fe99061fc320c3fea2187f94430bf28861f6510c2eca2187f54430bea8861f5510c2eaa2187f14430ffa0861fe410c3fa82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ff21e41fd43c83f887907fccb20ff19641ee32c83fa65907b4cb20fe19641ff51c83fca3905f94720fea8e417d51c83f8a3907fcc720ff18e41fd31c83f863907fc8720ff10e41fd21c83f843907fcc320ff18641fd30c83f861907fd4e20bfa9c41fe53882fca7107f54e20bea9c41fc53882f8a7107f90e20fea1c41fc43882faa5107fcca20ff19441fd32883f865107fd4620ff28c417e51883eca3105d94620fea8c417d51883eaa3105d54620fe28c41ff31883fc63107f4c620fe18c41ff21883fc43107f48620fe10c417e50883fe61107f8c220fe98441fc30883fe41107bc8220fd90441ff53482fea6907f94d20bf29a41fd53482faa6907f14d20be29a41fe43483fa86907f10d20ff99241fe32483dc64907f4c920f699241fc32483fea2905fd4520ff28a41fd51483f8a2905f14520ff98a41fe31483fa62907f0c520ff90a41fe21483fa42907f08520ff98
  | 2 => 0xc7fa6598f74cb31fe19663ff41cc7fea198ff94331bf28663fd50cc6faa198ff14331ffaa4637f548c7fca918df95231feaa4637d548c7f8a918df54e31ffa1c63fe438c7fa8718ff10e31ffa9463fe528c6fca518ff54a31bea9463fc528c7fe8518ff90a31fea1463fc428c7fe6518ff8ca31fe99463fc328c6fca318ffd0631ff20c63ff318c7be6318fdcc631ffa8463fe508c6fca118ff54231bea8463fc508c7fea898dfd5131ff2a2637e544c7faa898df55131fe2a2637c544c7fe8698ff90d31fea1a63fc434c7fea498dfd4931ff29263fd524c7f8a498df14931ffa1263fe424c7fa8498ff10931ff99263df324c7fc6498ff4c931ee99263fc324c7fe8298ff90531fea0a63ff314c7ee6298ff8c531ef18a63ff504c6fea098ff94131fea8263fc504c6f8a098ffd5031bfaa063fe540c6fca818ff55031beaa063fc540c6f8a818df94c31ffa1863fe430c7fa8618ff10c31ffa9063fe520c6fca418ff54831bea9063fc520c7fe8418ff90831fea1063fc420c7fe6418ff8c831fe99063fc320c6fca218ffd0431ff20863fd410c7f88218ffcc431ef98863fe310c7ec6218ff4c431ee98863f5310c7fea018ff94031bf28063fd500c6faa018ff14031ffa9e437f53c87fca790df94f21fea9e437d53c87f8a790df14f21ff21e43fd43c87f88790ffccb21ff19643fd32c87f86590ffcc721fb98e43fe31c87fa6390ff0c721fa18e43ff50c87fca190df94321fea86437d50c87f8a190ffd4e21bfa9c43fe53886fca710ff54e21bea9c43fc53886f8a710ff90e21fea1c43fc43886faa510ffcca21ff19443fd32887f86510df94621ff98c43fe31887fa6310ff0c621ff90c43ef21887ee4310ffd4221ff284437e50887faa110df54221fe28443ff53486fea690ff94d21bf29a43fd53486faa690ff14d21be29a43fe43487fa8690ff10d21ff99243fe32487fa6490ff0c921ff98a43fe31487fa6290ff0c521ff90a43f721487fc4290fb88521ffa82437f50487fca090ff54121fe282437c50487fea610dfd4c21ff298437e53087bca610d794c21fea98437d53087baa610d754c21fe298437c53087fc8610ff50c21fe218437e52087fe6410ff8c821fe99043fc32086fca210ffcc421fb98843fe31087fa6210ff0c421fa18843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010fe94021bd28043fd50086faa010fe54021bca8043fc50087fea9987f95330bf2a661fd54cc2faa9987f15330be2a661ff43cc3fc87987790f30fea1e61dd43cc3f887987fd4b30ff296617e52cc3faa5985f54b30fe29661ff42cc3fc85987f50b30fe21661ff32cc3be65987f8cb30fe99661dd32cc3f865987fd4730ff28e617e51cc3faa3985f54730fe28e61ff41cc3fc83987f50730fe20e61f
  | 3 => 0x2401400800402402801000c00800800000000000000002c00805400801409000000000000000400000000001001401800c00000400405800000800402003800000800c04800002002400001c00c00000001001801400000400401c01800003000001400800c01c00c00003c00c01c00400401000800000000401001000401000c00c00000400400401c00000005800003003000002c00402006000400000000009802800000005403800800000801000400800400403806400000004002c00000c04400c00001401002400000c00002400400400800000004c00c00400003400000800c02000400401001000001004c00002800001400000000400002001000001c01c00000000800003001efaa921df94e43ffa1c87df4390ffea521ff94a43bf29487fd5290efaa521ff14a43ffa8c87fe5190efca321ff54643bea8c87fc5190ffea121ff94243bf28487fd5090efaa121ff14243ff21a87be4350ffea4a1dfd4943ff29287fd5250ff8a4a1df14943ffa8a877f5150ffca2a1ff54543fe28a877c5150ffea0a1dfd4143ff28287fd5050ff8a0a1df14143bf29887fe4310fbc8621ff50c43eea18879d4310ffea421ff94843bf29087fd5210efaa421ff14843ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043ffaa665fe54ccafca9997f55332beaa665fc54ccaf8a9997fd0f32efa1e65fe43ccbfa87997f10f32ee21e65ff42ccbfea3997f94732bf28e65fd51ccafaa3997f14732ffa8665fe50ccafca1997f54332bea8665fc50ccbfea9195fd5232ff2a4657e548cb7ca9194f95232feaa4657d548cb7aa9194f55232fe2a4657d538cbfe87197f90e32fea1c65fc438cafca5197fd0a32ff21465ff328cbbe65197bcca32ffa8c65fe518cafca3197f54632bea8c65fc518cbfea1197f94232bf28465fd508cafaa1197f14232ffaa2657f544cbfca8995f95132feaa2657d544cbf8a8995f15132ffa1a65df434cbfc86997f50d32fe21a65dc434cbfe84997f90932fea1265ff324cbde64997f8c932ef19265ff514cafea2997dd4532bba8a65fe514cbfaa2997f14532be28a65f4514cae8a2997fd4132bfa8265fe504cbfaa0997f14132be28265ff540cafea8197f95032bf2a065fd540cafaa8197f15032be2a0657e530cbfe86197f90c32fea1865fc430cafca4197fd0832ff21065fd420cbf884197fcc832ef99065fe320cbdc64197f4c832ee99065ed320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea998ff95331bf2a663fd54cc6faa998ff15331be2a663ff43cc7fc8798ff50f31fe21e63ff52cc7fca598df94b31fea96637d52cc7f8a598ffd0b31ff21663fd42cc7f88598ffccb31ef99663fe32c
  | 4 => 0xfb87b849c6b87188f21a8addad41400000012f1d60b389a1a886f12e8dd06e000207000000000000000113dab9835e40001510000344804589fd8268001fa82a07ad734f71f240000000e49403da1501f5699528d200008f80010640000017b5728000001564c30000b995310158a9f50c98000001b89ca1ce51a00000693f076c46c921554828dc8aade39f981bc9680018045a9d20000000000001504000000000000000174001c9c0000021106bc9a4318c7c0002580020d8000001f700003f0d69f04ea14517bc001a90ca9569120491710ad0928e940012fda10290d48d501d1621678551a0c3dc1e1a04f90bda004000cc61700000d93296e8000001d10000001600002250000e24000ba00000000007f51361a097d4600007613d80180000011e90020c82b8cb05bd16c000000000001be00000000020502057a08588f40014f800031d9a8f4a1b800011912d4e8000c747080f05e1361708c6a169a0045ca9c0016640015f40021f9b2000219800000223a2319116d499a2406a8e79938a7a10c5588380004040008fc00081874157c000001661ef0000000000000821d80860850000325a18000001eb0f682cd5ba001cf8001e0c255849821420fc2098000000001584f95831f81899ce84a1bd0ae0cd0d996397a5cdded0001c8cac0001c200010d22e1f1c000489d78b88e19a9cac8480000000c6000000000000000000000c00c01c00c00000c00c00000c00800800002402000c00c0000340040000080a400000000803c01000400400000801000800000400000000c01c00803c00c00005000401401400800400000000c00401800000c0040080180540040380d000004000002400c01002000000400001002c00c06408c00802403400000400001000003400400803400800003006000000c00000000400000000c00801001801801001c00003400000000001000003c00408006400800800000c00004000000c06002000c00400400002400800000002401c00403801800804c00400000400000000401400802400001000400000003800401c01403c03000800005001400400403800000c00000001800000400001400c06000000406800401801404800c02400400001000000000402008400000000007000c01000400001803c00c00010c00400802400800803800000000000003c00000001402001402400800401400800000000002801801800401003001000402402401000001009400801c00000000000402801c04000400800402400000c0000100040000a402002000402c00400001000c01401400400000000c01400000c00000c00400000402000c00400800400401401c00c00003402007400c00400000000000001800400c00000000000c0000000000000000a800001401c02400400802402400005401c00400000000
  | 5 => 0xb80000000000000001880020a9c4956df145c40009f5538000000001204000c39bcc0640009b1de8a40b280009b955c6e97e06d8000000000000000a5d95800000093c0000000008d0eadb840001a863400101026000000000000000000073923800000197235517a0c0f55da8f88000f808b1645afa328000000bd5f88e854a98091f902d5a0b78ef15998bd8c53e8531418614a340a8769ed81000000000000004e8001190000355a80ccdab0001691e70090a740000fa0e008972c000001180348b584d8338d2c311c790a0000001c954a138a12400108a20800025070d4c8b9c000e88c10898cb8000390169431ef8789399df2080cc0001314df13a8198001949490001400ee800174130c000000bf9a69100000668000000000bf1d722b00018e00020fc0020d0a283c5d299d1a3a1186081c0a55d417cce1c4f00003c800103124c000001618d28002261700a117b111a3601212417c17983157600020083a91f52a9aad58e2c9289d6a2a12085d0000000000a65bc4001070d90ba52122f1358000700001d380000000000bc000000409290cd9b7400194c25d4288c85f1ae87e8161488f0c000ffa2780000000000000000023380dc000001c288a0af95517fe0a03780011c9f119040000000003b800165c0000001d4774000a91d99f09168fa54e579cfadb28da2092310450000b7052817dec1218b48001fe8c24a083616581804c94fc7fc05c000001468000000ab00000013dc0015b1676320000c6c5640022c0300001e60809e68000000000000000001870000844249ca5a400016d99e138c0000010a84641656ecd45a4caa40300716d00799f0d61f0c14800181d6040017f1940000000000bcc000e50000fb1f640018d00000015f95f00000000000000020780004ac000000f28aec00096202c0017d9f606805a12b8a206000000ec0009f0000e2cbe000078c5c04222901c40007d065056daa8000000000398001764c6424d165d01259078001039b48000cf8000cf0001061769725264000fe16716359443e8e48270711fa164d371e80001074d8150d8b80009740005b4440000000000000b680c0c85e998f40014392000007312320f9025ac061c3d0830e403200ac0003522b4000bac2b0cd49b43b1f286dcf1a2582f1db8f41ad15720f22fa1312700011b80000002e07a9409548000ad97907c0001c505820b8000499a980022e8c14000001b40b314ccfa0002270d300018400013cc001f01b78001719c9162a1800021b1a2937c00014c2c4000e380007f04c1649770001c400000011d84322484105920589480016f80003fd610834d58fe8000000000000000ca5a5cd940017e8bb55d033daf0d9c0000000000000016a8cb40017c80000000000004586fca980014d8000000002178000280000000000000001378000
  | 6 => 0x539918000000b820b0002349b31059170549d300000000006b000000182d220000001459ff16400000000000000000000000000000007f80015c0001810000b5d1fc0008704dc1700000000000005200020300000013d4b403f400032c0000000000000000008e1950000001a08000001cf10c40017e5bda229099b7da48000000460c70aa00000000000016dc0000000000015fc000000000664fd8000001d90f4c8a86116f4110000a31b1160c000c50058a448e81281300019001ee300cca068000000000000d8dfe00000d00007c800000163d574d4d9817ac3419203317445d4001080d544d1688ce1cc1c10000a14381140b50000000620d409e0001dfcbc9519591ce195de312e22883d5499480c894f006c439b91bc800119999c9106d0470001f6a0389705b0000000c59021ddc00000106d2c00006a12c80b40003c000000069023c000001c700008c1b60000e0a101470001dc1739e28184f218d87851240396e0bbd1c17b97815589c09180007b0001750221161a58bdc0000017043662bc0000013f4001b000000000014d4a0c0016a05c8a0000000000161c000000000905a60c1c0017f8001e1231920c002028151b98810021ea05084293d0049ba82c19c9d880002080008e47e19c1759c00000000ff0000000000001cb0000002138728002048230001b8c0019f98fc00000090e0e9bf0000000ab80000000007994dc479110bc56cc8ec0004499280008b95ed801ec97dc1f87a00010c0000901310a88001ae1ea8a68b103586f40a00000009d00009f80000000000009e8000000000705fb13822204f913879c00201a060ba8e100002990e04e1dc8b61df451108c000d700000400280019ea159cd89093861c0d787d85754c1535bc0000000000001b5000065c000001e20001c5966cc08d34000000001988000000000001754000060001878dc1e4c0009c98189806780018580a4000000b19c315457d196095862459a214560bd0a80a398e83893b9aa2351e18670f4517d174ea9f90ee02198c9440500000001579630f517201561900007a5e08001a50010cdc2881d8a1a2d8bb22985d87793188894c5b44c42281b3975c000000000d088a5930c0c00057c1b9cd0241f41f582285e8db91a93909256fc84871621c8407500756145455a901d0082d9e893c0eda0891492602a8001c61f7990d6680008900001e86300003a19685684ccb4c00000000092d2bd130000a700004b1128e90002200af1b08b204aa040a6c000000ae8ec1339df8098368000000000cbe160000fc8000be48de1f13000022a99901cc6d40010c84b9478000e01582010000000000001321a21f30000000000000c29db1814cad7880018f125400139454d4b16f1cf43350e853c371608a4c001860934002368b85891f3cc018a0000000000000e
  | 7 => 0x96c000001dd00005adc98001778080308001b80000790000000000000000000000000000001a549500003e00500000000023580011f0000d18bb9ee8000000e8c000001880f38000000000001158159150e152d4000000000000f016c0000000794000ed00000e95e024620c001fc1ac8000000be80013e00009a80006c9188d11c380006593c8000758988699654688b9134983c84c9901796800000006f82382bddd400150973c0000021049140008acef9ad8f79c68001268001fd00003f9b591b0c800003e4e80000000000000000f618522b8ec98b44b61e8e28bc0f58001114af41fc0013b066d6c5824eb015c0010f80000c80007edde04d55e4b5400000180e1e1f4800077c0021fc91c32a021a7201c001a30000b8c6e41c9308771e90000000001f380002f8000000000f6d7496502e80000000012a06280004540006390b0801282128d89d50a940000013047498c1ff9a95cc9c19251068a5a331048932141a453505cd0d9d198f92cd53c0d52c4001eb9be80021d8000001e58001f344686ec9bcb000b91e01f00b04180006488bcb94aa8000000000000a497a8a04571331d4954000000000000000154cd8462c9394f41a00000016b95d99b83ec000000fa8001f21d08ea4e71050c5c0005540014b94e14d00021d00017319990180000004e4000964b64000000000c20c185a4000000145ee00000012d8000000de1fb86c1838000000000f1000152dde5e5211c83d340d2421035cb0834cc4a308db1c809799d9829b69868de8f9dba1bb2211bb8641c08e68e985b9e01ca8578ae5fc974e1c89fc61a149091cb8f662d10f0f5c000190c9cfd00099084a4e60a1e2696b1e79bf80008794bcf083ccdd8000001e48f30660000e20000001b18a609da0142b45f8001dd855c001410402120da92f86c45dc00013926e3400000000022180002d0880002188000000ce8a3d7c5d596c8000000d010b81b12497d40005419b15e80002c80e18b1245bdd3682791d10280000000000000000015215c8e58a515880000000000012280019a00000000008d8200518780c90000001500000ca12799792b09ad3a06cc0013f9298c78000000674d5c0008b5108001449041560df800036cd39f18000000720001889c88e30869b72108f99a792d0109da016c00
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe520427d63948109fd8d520427c6354810dbd89520427f61548109f585520427f60548109f58152042de6314810b758c520436d52148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109f984520437661148109d984520427e6014810de980520427a60148109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc8109fd96320427e658c8109f596320427c658c810af99232042bd648c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810db949320436d524c810bdd8532042f4614c8109fd94320427e650c8109f594320427c650c8109f98e510427d63944109f98a510427d6294410ddd8e51043766394410dd58e51043746394410dd90e51043754394410dd10e51043776294410dd98a51043756294410dd18a51043773294410dd8ca51043753294410dd0ca510427d65cc410dd947310427f658c4109f596310435e538c410d754e3104376518c410be98231042f9608c4109fd953104376514c4109fd94310427d650c410d794c310435d530c410dd94431042fa600c410be580310427d65c8410dd947210427f65884109f596210436e5288410db54a21043765188410be98221042f960884109fd95210437651484109fd94210427d6508410b798c21042dd6308410db948210436d5208410dd94421043e52108410be98021042f960084109f98e500427d63940109f98a500427d62940109f586500427561940109f597300437651cc0109fd96300427d658c010d794e300435d538c010bd98630042f5618c010dd946300427f654c010afd9130042bc644c010dd945300427f650c0109f994300427d650c0109f19430042be640c010af590300435e530c010d754c30042ee620c010bb58830042f6610c010bd5843004376510c0109f597200437651c80109fd96200427d6588010db94a200436d5288010bd98620042f56188010dd946200437a50880109fd9520043765148010de941200427f65080109f994200427d65080109f19420042de6308010b758c200436e5208010db54820042f66108010bd58420043765108010dd597100437753c4010dd94f100437553c4010dd14f100437752c4010dd94b100437552c4010dd14b10042f56184010dd94610042f96584010de59610042796584010ded4a10043795284010be586100437a5184010fc946100427f6544010dd94510042f76544010ddd9510042776544010ddd4d10043765344010dd54d10043745344010ddd4910043765244010dd54910043745244010bdd8110043765044010fc88110043f12044010bed95100437b65440109ed95100437b5244010de54910042fb6144010fcd85100437a5144010fc94510043725144010fc88510043f12144010
  | 1 => 0x43b6640c110ad99030442f5640c110ed59030442b5640c110bd19030442f6630c110f5d0c30443d4430c110bd98830443e6620c110b998830442f5620c110f958830442e5620c110bd98030443f3500c110fcd0030443f0400c110f5cc030443f2300c110f54c030443f1300c110f44c030442f665c8110bd19720442f763c8110bd98f20442f563c8110bd18f20443e752c8110f914b20443e632c8110f94cb20443f350c8110bd996204437665881109d99620442f76388110bd98e20442f56388110bd18e20442f56288110bd98220443f35088110fccc220443f23088110fc4c220443f03088110f9c8220443f32088110fc99620442f26588110dc99620443f36388110fc98e20443f16388110fc18e20443f35388110fc94e20443f15388110fc14e20443f24388110fc50e20443f04388110bc58a20443f35288110fc94a20443f15288110fc14a20443f33288110fc8ca20443f13288110fc0ca20442f76548110bd99520442f56548110bd19520442f76348110bd98d20442f56348110bd18d20443e75248110f914920443e63248110f94c920443f35048110fccc120443f23048110fc4c120443f03048110fcc8120443e62048110fc99520442f26548110fc19520442f06548110fcd8d20443f26348110fc58d20443f06348110fcd4d20443f25348110fc54d20443f05348110fc90d20443f14348110fc10d20443f36248110f8d8920443f35248110f8d4920443f25248110fc54920443f05248110f814920443f33248110fc8c920443e23248110fc4c920443e13248110fc0c920442f66508110dd99420442766508110bdd8c20442f66308110f598c20442d66308110bd58c20443d56308110b558c20442f46308110bd98820442f66008110bc98020443f35008110f9c8020443f22008110f948020443f120081109f993530427d64d4c109f98b530427d62d4c109f987530437661d4c109d987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10af99053042bd6414c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd98453042766114c109f980530437a6014c109fd96430427e6590c109f596430427c6590c10d794e430435d5390c109fd95430427e6550c109f595430427c6550c10d794d430435d5350c109fd94430427e6510c109f594430427c6510c10e750c430427e63d48109f58f520427e61d4810dd987520427661d48109f983520437a60d48109f596520436f52948109f98
  | 2 => 0x6394910bd58e52443765394910dd14e52442f66294910ddd4a52443e75294910bd58252443f16094910bc58252442f76354910f5d8d52442d76354910bd18d52443d46354910b518d52443e75254910dd94952442f76054910fcd8152442f36054910bd99452442f66314910f598c52442d66314910bd58c52443d56314910b558c52443765314910dd14c52443775214910f994852443755214910f954852443655214910fc58052442f765cc910bd99732442f565cc910bd19732442f664cc910bd59332442f464cc910f594f32443d553cc910f5d0f32443d443cc910f9d4b32443e452cc910bd98332442f560cc910bdd9632442f6658c910bd59632442f4658c910bdd9232442f6648c910ed99232442b6648c910bd59232443b5648c910ad59232442f5638c910f5d4e32443d4538c910bd98a32443d7328c910f9cca32442f6608c910fc98232442f2608c910bd58232443f1608c910bc58232442f7654c910ddd953244277654c910bd99532442f5654c910bd1953244374654c9109d19532442f7644c910bd99132442f5644c910bd19132443d6534c910f554d32443d7434c910f510d32443e7324c910f58c932442f7604c910bd18132442f7650c910bd99432442f5650c910bd19432442f7640c910bd99032442f5640c910bd19032442f6630c910f5d4c32443d4530c910bd98832443e7520c910f914832443d7320c910f98c832443d5320c910f94c832442f6600c910fc98032442f2600c910bd58032443f1600c910bc58032442f663d4110bd58f504437753d4110dd94f504437553d4110dd14f50442f662d4110bd58b504437752d4110dd94b504437552d4110dd14b504437265d4110fcd8f50443f263d4110fc58f50443f063d4110fcd4f50443f253d4110fc54f50443f053d4110fc90f50443f143d4110fc10f50443f362d4110fc98b50443f162d4110bc58b50443f062d4110fcd4b50443f252d4110fc54b50443f052d4110fcccb50443f232d4110fc4cb50443f032d4110bd99730442f465cc110bd99330442f564cc110bd19330443d753cc110f514f30443d643cc110f550f30442f662cc110bd58b30443d732cc110f54cb30443f350cc110fcd0330442f6658c110dd9963044276658c110bdd9230442f6648c110bd59230442f5638c110f5d0e30443d4438c110bd98a30442f5628c110bd98230443f3508c110fc90230443d7308c110fccc230442f7654c110bd99530442f5654c110bd19530442f7644c110edd9130442b7644c110bd99130442f5644c110bd19130443b4644c110ad19130443d7534c110f514d30443d6434c110f550d30442f7624c110bd18930443d7324c110f54c930443f3504c110fc90130443f1404c110fccc130443d6304c110bd9943044376650c1109d99430442f7640c110bd990304
  | 3 => 0x510be98021442f66508510dd99421442f76308510bd98c21443d66308510b598c21442f56308510f558c21442d56308510bd18c21443765308510dd14c21442f66208510f998821443775208510dd54821442f66008510fc98021442f26008510fc580214427e65cc110d7d4f304435c53cc110bd98730442f561cc1109f99630442f6618c110bd586304427f654c1109f595304427c654c110afd9130442bc644c110d7d4d304435c534c110bdd8530442f4614c1109f99430442be640c110af59030442ee620c110bb58830442f6610c110bd58430443d9300c1109f997204436f52c8110db14b20442f661c8110bd587204427e6588110bd98620442f56188110be996204437a6588110be58a204437a5288110de14a20443f36188110be98620443f26188110bc98620443f16188110fc18620443f33188110fc8c620443f13188110fc0c620443f32188110fc88620443f12188110fc086204427f65481109f595204427c6548110dbd49204436c5248110bdd8520442f46148110be195204437865481109e19520443eb6248110fad49204437a5248110de14920443e85248110fa8c920443e93248110fcd8520442f86148110fc18520443f33148110fc8c520443f13148110fc0c520443f32148110fc88520443f12148110fc085204427e6508110b798c20442dd6308110bd98420442f56108110be98020442fb62c4110be58b10443f331c4110fc8c710443f131c4110fc0c710443f321c4110fc88710443f121c4110fc08710442f76384110bd98e10442f56384110bd18e10442f76284110bd98a10442f56284110bd18a10443f35084110fc88210443f12084110bd99353442f564d4d10bd98b53442f562d4d10bd99253442f56494d10bd98e53443775394d10f5d4e53442f66294d10bd58a53442f56094d10fc58253442f16094d10bdd9153443b76454d10add9153442f46454d10ed19153442b46454d10f5d4d53443765354d10bdd8953443e76254d10b9d8953442f46254d10f918953442e46254d10bdd8153443f36054d10bcd8153442f66514d10bd99053442f56414d10ddd4c53443d65314d10dd54c53443d55314d10bd98853442f56214d10bdd9643442f66590d10bd59643442f46590d10bd59243443b75490d10ed15243442f66390d10f5d0e43442f66290d10bd58a43442f66090d10bd58243442f76550d10bd99543442f56550d10bd19543443b64350d10bdd8943442f46250d10bdd8143443f36050d10bcd8143442f46050d10fc18143442f06050d10bdd9443442f66510d10bd59443442f46510d10bd98c43443d75310d10f514c43443d64310d10f550c43443954310d10bd98843442f56210d10bd98043443f26010d10bc98043442f56010d10fc58043442f16010d10bd98f52442f563d4910fcd8352442f6
  | 4 => 0xd587524436f52949109f98e524427d63949109f98a524427d6194910dd586524427d6094910de58252442df6354910b718d524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109fd81524437b60549109f99452442de6314910b758c524436d52149109f98c524435e63149109798c524427d6314910d758c524425d6314910db988524427e6114910dd584524427c61149109f980524437960149109f180524427f65cc9109f997324427d65cc9109f197324435e53cc910d754f324436f52cc910db14b32442f661cc910bd587324427f658c9109f996324427d658c9109f19632442be648c910af592324435f538c910d714e32442f6618c910bd58632442fa608c910be582324427f654c9109f995324427d654c9109f195324435e534c910d754d32442f7614c910bd185324427f650c9109f994324427d650c9109f194324435f530c910d714c324436f520c910db14832442f6610c910bd58432442fa600c910be580324427e65cc510d7d4f314435c53cc510be98331442f960cc510dd997314427665cc510bd99331442f564cc510bd193314437753cc510f5d4f314437553cc510f514f31442f662cc510bd58b314437652cc510dd14b31443d732cc510f54cb31442f660cc510fc98331443f160cc5109f99631442f6618c510bd9963144376658c510bdd9231442f6648c510bd59231442f5638c510dd94e3144374538c510bd98a31442f5628c510bd982314427c654c510d7d4d314435c534c510bed8131442f8604c510dd1953144274654c510bdd9131442f6644c510bd59131442f4644c510f5d8d31443d7534c510dd94d3144374534c510f514d31442f7624c510bd18931443d7324c510f54c931443f3604c510bd18131443f0604c5109f99431442f6610c510bd9943144376650c510bdd9031442f6640c510bd59031442f4640c510bd98c31443d6630c510ddd4c3144375530c510bd98831442f5620c510dd9483144374520c510bd980314427e65c8510dbd4b214436c52c8510be98321442f960c8510dd997214427665c8510bdd8f21442f663c8510bd58f21442f463c8510dd94f214437453c8510ddd4b21443e752c8510dd54b21443e452c8510bd98321443f260c8510bc98321443f160c85109f99621442f66188510bd99621443766588510bdd8e21442f66388510bd58e21442f46388510bd58a21443765288510dd14a21443f36088510bd98221443f060885109f195214436f5248510db14921442fb6048510be181214437465485109d19521442f76348510bd98d21442f56348510bd18d21443e76248510f9d4921443765248510dd14921443e45248510d914921443f36048510bd18121443f060485109f99421442de6308510b758c21442f66108
  | 5 => 0x438427f6510e109f994438427d6510e109f194438439d4310e10be98043842f96010e109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6394a109f58e528437a6094a109fd8d528427c6354a10dbd8952842de6314a10b758c528436d5214a109f98c528435e6314a109798c528427d6314a10d758c528425d6314a10db98852843756114a10de980528427f65cca109f997328427d65cca109f197328435e53cca10d754f328427f658ca109f996328427d658ca109f19632842be648ca10af592328436e528ca10db54a32842fa608ca10be582328427f654ca109f995328427d654ca109f195328435e534ca10d754d328436e524ca10db54932842f7614ca10bd185328427f650ca109f994328427d650ca109f19432842fa600ca10be580328435e53cc610d754f31842fa60cc610be583318435e534c610d754d31842fb604c610be181318436e52c8610db54b21842fa60c8610be583218436e5248610db54921842fb6048610be18121842de6308610b758c21843e52108610be580218435e538c210d754e30842f6618c210bd58630842bf644c210af19130842be640c210af590308435e530c210d754c30842ee620c210bb58830842f6610c210bd58430843d9300c210db94a208436d5288210bd98620842f56188210be59620843796588210de94a20843ea5288210fa54a20843785288210be98620843f26188210fc58620842fb6548210ded9520843eb6248210de94920843785248210fa8c920843e93248210be18520842de6308210b758c208436e5208210db54820842f66108210bd58420842f565c4210dd597108437753c4210dd94f108437553c4210dd14f108437752c4210dd94b108437552c4210dd14b10842f965c4210de59710842fb62c4210be58b108427e64d4d109f593534427e62d4d109f58b534437561d4d10d7d4e534427e6494d109f592534427e6394d109f98a534427d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f98453443756114d109f184534427e6014d109f180534427f6590d109f996434427d6590d109f196434433f5490d10cf15243442f66190d10bd586434427f6550d109f995434427d6550d109f19543442f76150d10bd18543442fb6050d10be181434427f6510d109f994434427d6510d109f194434435f5310d10d714c434439d4310d10bd98443442f56110d10be98043442f96010d109f98f524427d63d4910d
  | 6 => 0x2f565ccb10bd19732c42f664ccb10bd59332c42f464ccb10f594f32c43d553ccb10f5d0f32c43d443ccb10bd98332c42f560ccb10bdd9632c42f6658cb10bd59632c42f4658cb10bdd9232c42f6648cb10ed99232c42b6648cb10bd59232c43b5648cb10ad59232c43d7328cb10f9cca32c42f6608cb10bd58232c42f7654cb10ddd9532c4277654cb10bd99532c42f5654cb10bd19532c4374654cb109d19532c42f7644cb10bd99132c42f5644cb10bd19132c43d6534cb10f554d32c43d7434cb10f510d32c43e7324cb10f58c932c42f7604cb10bd18132c42f7650cb10bd99432c42f5650cb10bd19432c42f7640cb10bd99032c42f5640cb10bd19032c43d7320cb10f98c832c43d5320cb10f94c832c42f6600cb10bd58032c42f565cc310bd99330c42f564cc310bd19330c43d653cc310f554f30c43d643cc310f550f30c42f662cc310bd58b30c43d732cc310f54cb30c42f5658c310dd59630c42f7648c310bd99230c42f5648c310f5d0e30c43d4438c310bd98a30c42f5628c310f5cc230c43f3308c310bdd9530c42f7644c310edd9130c42b7644c310bd99130c42f5644c310bd19130c43b4644c310ad19130c43d6534c310f554d30c43d6434c310f550d30c42f7624c310bd18930c43d7324c310f54c930c43f3304c310f58c130c42f5650c310dd59430c42f7640c310bd99030c43b6640c310ad99030c42f5640c310ed59030c42b5640c310bd19030c43d7430c310f510c30c42f6620c310f998830c42e6620c310bd58830c43e5620c310b958830c43d7300c310fc8c030c43d5300c310fc4c030c42f565c8310bdd8f20c42f663c8310bd58f20c42f463c8310f994b20c43e552c8310f98cb20c43e532c8310bd59620c43756588310bdd8e20c42f66388310bd58e20c42f46388310f9c8220c43f32088310bdd9520c42f76348310bd98d20c42f56348310bd18d20c43e65248310f954920c43e63248310f94c920c43f32048310f988120c42f56508310dd59420c42f76308310bd98c20c43d66308310b598c20c42f56308310f558c20c42d56308310bd18c20c43e72008310fc88020c43e52008310fc48020c427e64d4e109f593538427e62d4e109f58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e109fd91538427c6454e10d7d8d538427f6254e109f18953842be6414e10af590538435d5314e10bb98853842ed6214e109f990538433e6414e108f990538427d6414e10cf590538423d6414e10d798c538427e6214e10db988538426e6214e109f588538436d6214e109b58853843756114e10de980538427f6590e109f996438427d6590e109f196438435e5390e10d754e438427f6550e109f995438427d6550e109f195438435e5350e10d754d43842fb6050e10be181
  | 7 => 0x30c710d754c31c42fa600c710be58031c4375650c710bdd9031c42f6640c710bd59031c42f4640c710f598c31c4377530c710f594c31c4375530c710f554c31c42f6620c710bd58831c4376520c710dd14831c42f6600c710fc98031c43f1600c710bd59721c437565c8710bdd8f21c42f663c8710bd58f21c42f463c8710dd94f21c437453c8710ddd4b21c437552c8710bd98321c436e5288710db54a21c42fa6088710be58221c43756588710bdd8e21c42f66388710bd58e21c42f46388710dd94a21c43e65288710f954a21c43745288710bd98221c43f26088710fc58221c42f76548710ddd9521c42f76348710bd98d21c42f56348710bd18d21c43e76248710dd94921c43745248710bd18121c42de6308710b758c21c436e5208710db54821c42fa6008710be58021c43756508710bdd8c21c42f66308710f598c21c42d66308710bd58c21c43d56308710b558c21c42f46308710dd94c21c43745308710f998821c43775208710f994821c43755208710f954821c43655208710bd98021c43f26008710fc58021c435e53cc310d754f30c42f661cc310bd58730c42f6618c310bd58630c42bf644c310af19130c435e534c310d754d30c42f7614c310bd18530c42be640c310af59030c42ee620c310bb58830c42f6610c310bd58430c436e52c8310db54b20c42f661c8310bd58720c42f66188310bd58620c436e5248310db54920c42f76148310bd18520c42de6308310b758c20c42f66108310bd58420c42f664d4f10ed99353c42b664d4f10bd59353c43b564d4f10ad59353c42f662d4f10bd58b53c42f560d4f10fc58353c42f160d4f10bd99253c42f56494f10ddd4e53c43d75394f10bd98a53c42f56294f10bdd9153c42f46454f10f5d4d53c43765354f10bdd8953c42f46254f10bd99053c42f56414f10ddd4c53c43d65314f10dd54c53c43d55314f10bd98853c42f56214f10bd58053c43f16014f10bc58053c42f76590f10bd99643c42f56590f10bd19643c43b65490f10ed55243c43d74390f10bd98a43c42f56290f10bd98243c42f56090f10bdd9543c42f66550f10bd59543c42f46550f10ed90d43c42f76250f10bd18943c42f76050f10bd18143c42f76510f10bd99443c42f56510f10bd19443c43d65310f10f554c43c43d64310f10f550c43c43954310f10bd98843c42f56210f10bd98043c42f56010f10bd98f52c42f563d4b10bd58352c43f160d4b10bc58352c42f66394b10bd58e52c43765394b10dd14e52c43775294b10f9d4a52c42f76354b10bd18d52c43e75254b10dd94952c42f66314b10f598c52c42d66314b10bd58c52c43d56314b10b558c52c43765314b10dd14c52c43775214b10f994852c43755214b10f954852c43655214b10bd58052c43f16014b10bc58052c42f765ccb10bd99732c4
  | 8 => 0x20dd544300835e53c8020d754f200837651c8020dd547200836f53c8020f394f200836d53c8020f354f200834d53c8020f994720083e551c8020d794e200835d5388020bb58a200836e5288020bd98620082f56188020dd94620083755188020f694e20083d95388020be58a200837a5288020fa94a20083f26188020fc58620083f25188020de54620083f15188020dc546200827f6548020d794d200835d5348020dd94520083755148020bbd95200836f65480209bd95200836f5348020f394d200836d5348020f354d200834d5348020f994520083e55148020bbd81200836e5048020bed95200837b65480209ed9520083da5348020f654d20082fb6248020fad89200837a5248020fa94920083f25148020de54520083f15148020dc54520082be64d4f10af59353c427e64d4f10cf99353c423e64d4f109f59353c433d64d4f108f59353c427e62d4f109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f10dd98653c427f6454f109f19153c435f6354f109fd8953c427c6254f10dd18553c435d5314f109f99053c427d6414f10d798c53c427e6214f109f58853c43766114f10de58053c427f6590f109f99643c427d6590f109f19643c433e5490f10cf55243c42f66190f10bd58643c427f6550f109f99543c427d6550f109f19543c42f76150f10bd18543c427f6510f109f99443c427d6510f109f19443c435e5310f10d754c43c439d4310f10bd98443c42f56110f109f98f52c427d63d4b10dd98752c437960d4b10dbd4a52c427e6394b109f58e52c43766194b109fd8d52c427c6354b10dbd8952c43746154b10b798c52c42dd6314b10db54852c427e6314b10d798c52c425e6314b109f58c52c435d6314b109758c52c436e6214b10dd98452c43796014b109fd9732c427e65ccb109f59732c427c65ccb10d794f32c435d53ccb10bd98732c42f561ccb109fd9632c427e658cb109f59632c427c658cb10af99232c42bd648cb10bd98632c42f5618cb109fd9532c427e654cb109f59532c427c654cb10d794d32c435d534cb10bdd8532c42f4614cb109fd9432c427e650cb109f59432c427c650cb10bd98432c42f5610cb10bd59731c437565cc710bd99331c42f564cc710bd19331c437753cc710dd54f31c42f662cc710bd58b31c437652cc710dd14b31c43d732cc710f54cb31c42f660cc710d794e31c435d538c710be98231c42f9608c710dd59631c42f7648c710bd99231c42f5648c710dd94e31c43d6538c710f554e31c4374538c710bd98a31c42f5628c710bd98231c43f2608c710fc58231c42f7654c710ddd9531c42f7644c710bd99131c42f5644c710bd19131c43d7634c710dd94d31c4374534c710bdd8931c42f4624c710f5cc931c43d5324c710bd18131c435e5
  | 9 => 0xd8143082f86050c209fd94430827e6510c209f594430827c6510c20d794c430835d5310c20e750c430827e63948209f58e520827d65cc820cf953320833d54cc820d794f320835d53cc8209fd96320827d658c820af99232082bd648c820cf952320833d548c820d794e320835d538c820db94a32082fa608c820be582320827f654c820cf951320833d544c820d794d320835d534c820db94932082f7614c820bd185320827f650c8209f594320833e540c820cf550320835e530c820d754c32082fa600c820be58032082de63d4420b758f510835e53d4420d754f510835e5394420d754e510837751944209f98e510827d6394420ddd4e51083765394420f594e51083565394420dd54e51083d55394420d554e51083745394420ddd8e51083766394420dd58e51083746394420dd90e51083754394420dd10e51083746294420ddcca51083763294420dd4ca51083743294420dd98251083746094420d794d510835d53544209fd8d510827c6354420ddd9551083775354420dd94d51083d65354420d594d51083755354420f554d51083555354420dd14d51083776354420dd98d51083756354420dd18d51083764354420dd50d51083744354420dd98951083773254420dd8c951083753254420dd0c951083766054420dd18151083742054420b798c51082dd6314420d794c510835d5314420bd984510837551144209fd97310827e65cc4209f597310833e54cc420cf553310835e53cc420d754f310837651cc420dd547310827f658c4209f996310827d658c420cf952310833d548c420d794e310835d538c420dd9463108375518c4209fd95310827d654c4209f195310833e544c420cf551310835e534c420d754d31082ef624c420bb1893108376514c420dd545310827f650c4209f994310827d650c420cf950310833d540c420d794c310835d530c420dd9443108375510c420d794f210835d53c8420dd947210837551c8420be98321082f960c84209f596210835e5388420d754e210837551884209fd95210835e5348420d754d21083765148420b798c21082dd6308420d794c210835d5308420dd94421083755108420f948421082fa6008420be580210827e63940209f58e50083766194020dd586500827d65cc020cf953300833d54cc020d794f300835d53cc020dd947300837551cc0209fd96300827d658c020cf952300833d548c020d794e300835d538c020bb98a30082ed628c020bd98630082f5618c020dd9463008375518c0209fd9530082bf644c020af191300833e544c020cf551300835e534c020d754d3008376514c020dd545300827f650c0209f994300827d650c0209f19430082be640c020af590300833e540c020cf550300835e530c020d754c30082ee620c020bb58830082f6610c020bd5843008376510c0
  | 10 => 0x24836e534c920db14d32483cc534c920f3d0d32483cc434c920f9d8532483e4614c920fad8132482ec604c920fa181324827e650c920bb98832483cd320c9209f98f514827d63d4520ddd4651482df6354520b718d514837551145209f98c514827d6314520de580514827e65cc5209f597314827c65cc520bb98b31482ed62cc520f34cb314837751cc520dd147314827e658c5209f596314827c658c520d7d4e314835c538c520be98231482f9608c5209fd95314827e654c5209f19531483cd324c5209f994314827d650c5209f194314835f530c520d714c31482ee620c520bb5883148377510c520dd14431482fa600c520be580314827e65c8520ddd4621483745188520be98221482f96088520ddd4521483745148520bed8121482f860485209f99421482de6308520b758c21482fa60085209f997304835f53cc120d714f30482ee62cc120bb58b30483cd32cc1209f99630482f6618c120bd586304827f654c1209f595304827c654c120afd9130482bc644c120d7d4d304835c534c120bbd8930482ec624c120f34c9304827e650c120af99030482bd640c120bb98830482ed620c120bd98430482f5610c120fa8cb20483e932c8120be58720482f66188120bd58620482ef6388120bb58e20483e66188120f958620483eb5088120af99353082bd64d4c20bd98753082f561d4c209f993530833e64d4c208f993530827d64d4c20cf593530823d64d4c209f98b530836e62d4c209f987530837661d4c209d987530827d61d4c20dd587530827561d4c209f983530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530839e5494c20c7952530835f6494c20d7992530835d6494c20d7192530835e6294c20d718a530835f6194c20d7986530835d6194c20d7186530835e6094c20d7182530833e5454c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f185530835f6554c20d7d51530835e5454c20e7951530831e5454c20d7551530839d5454c20c7551530835f6454c20d7991530835d6454c20d7191530835e6254c20d7189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20af99053082bd6414c20cf950530833d5414c20b798c530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209798c530827e6214c20db988530826e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd96430827e6590c209f596430827c6590c20cf952430833d5490c20d794e430835d5390c209fd95430827e6550c209f595430827c6550c20d794d430835d5350c20be
  | 11 => 0x746394620dd90e51883754394620dd10e51883776294620ddcca51883763294620dd4ca51883743294620dd98251883726094620dd182518827f63546209f18d51883776554620ddd4d51883765354620dd54d51883745354620fc98151883776354620dd98d51883756354620dd18d51883764354620dd50d51883744354620dd58951883773254620dd8c951883753254620dd0c951883766054620dd181518837551146209fd97318827e65cc6209f597318837651cc620dd547318827f658c6209f996318827d658c620dd9463188375518c620be98231882f9608c6209fd95318827d654c6209f19531882ef624c620bb1893188376514c620dd545318827f650c6209f994318827d650c620dd9443188375510c620be98031882f9600c620dd94721883765188620dd54621882fa6088620be58221883765148620dd54521882fb6048620be18121882de6308620b758c21883755108620f948421882f96008620d7d4f308835c53cc220dd947308837551cc220d794e308835d538c220bb98a30882ed628c220bd98630882f5618c220dd9463088375518c220afd9130882bc644c220d7d4d308835c534c220dd9453088375514c220af99030882bd640c220d794c308835d530c220bb98830882ed620c220bd98430882f5610c220dd9443088375510c220dd947208837551c8220bb597208836d65c8220dbd4f208836d53c8220f994720883e551c8220be597208837965c8220be58720883f251c8220fc547208827e64d4d209f593534827e61d4d209f587534835f5394d209f992534827d6494d209f98e534827d6294d20db58a534827e6194d209f586534827d6094d20de58253482bf6454d20af19153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534835d5314d209f990534827d6414d20d798c534827e6214d20db588534827c6214d209f984534827d6114d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d20bb98a43482ed6290d209fd95434827e6550d209f595434827c6550d209fd94434827e6510d209f594434827c6510d20d7d4c434835c5310d20e750c43482ee6210d20bb58843482fa6010d20be580434827e65cc920d7d4f324835c53cc920be98332482f960cc9209f99632482be648c920af59232482ee658c920db99632482ef648c920eb99232482ed648c920eb59232482ad648c920bb58e324836e538c920db14e32482ee608c9209f195324835f534c920d714d32482f7614c920bd18532482fb604c920be181324836c654c9209b19532482ef644c920bb59132483cf634c920f3d4d3
  | 12 => 0x90f20bb58a43c827f6550f209f99543c827d6550f209f19543c82fb6050f20be18143c827f6510f209f99443c827d6510f209f19443c835e5310f20d754c43c839d4310f20bb98843c82ed6210f20d7d4f32c835c53ccb20af99232c82bd648cb20d794e32c835d538cb20be98232c82f9608cb20db59632c82ef648cb20eb99232c82ed648cb20eb59232c82ad648cb20db94e32c83ce538cb20f354e32c836c538cb20bb98232c83ea608cb20fa58232c835f534cb20d714d32c82f7614cb20bd18532c82ef654cb20dbd9532c82ef644cb20bb59132c83cf634cb20f3d4d32c836e534cb20db14d32c83cc534cb20f3d0d32c83cc434cb20f9d8532c83e4614cb20bb18132c835e530cb20d754c32c83cd320cb20be98032c82f9600cb20ddd4651c827e63947209f58e51c827f63547209f18d51c82de6314720b758c51c837551147209fd9731c827e65cc7209f59731c835e53cc720d754f31c82ee62cc720bb58b31c83cd32cc7209fd9631c827e658c7209f59631c827f654c7209f59531c827c654c720d794d31c835d534c720f34c931c827f650c7209f99431c827d650c720bb98831c82ed620c720dd94721c837551c8720be98321c82f960c8720b798c21c82dd6308720dd94421c83755108720be98021c82f96008720d794f30c835d53cc320bb98b30c82ed62cc320f34cb30c82f6618c320bd58630c82bf644c320af19130c835e534c320d754d30c82ef624c320bb18930c83cd324c320af99030c82bd640c320bb98830c82ed620c320bd98430c82f5610c320bd98753882f561d4e209f993538827d64d4e20db58b538827e61d4e20dd987538827661d4e209f587538837561d4e209d587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f58653882bf6454e20af191538827f6454e20cfd91538823f6454e209f191538833c6454e208f191538835f6354e209fd85538827c6154e20af99053882bd6414e20d754c53882f66114e20bd584538827e6414e20cf990538823e6414e209f590538833d6414e208f590538835e6314e20db588538827e6114e20dd98453882766114e209f58453883756114e209d584538837a6014e209fd96438827e6590e209f596438827c6590e20cfd52438833c5490e20d794e438835d5390e209fd95438827e6550e209f595438827c6550e20d794d438835d5350e209fd94438827e6510e209f594438827c6510e20d7d4c438835c5310e20e750c43882fa6010e20be580438835e53cca20d754f32882fa60cca20be58332882be648ca20af592328835e534ca20d754d32882f7614ca20bd18532882fb604ca20be181328837751946209f98e518827d6394620de98251883775394620dd94e51883755394620dd14e51883f26094620ddd8e51883766394620dd58e51883
  | 13 => 0xdd547210c27f65884309f996210c27d6588430cf952210c33d5488430db94a210c36d5288430dd946210c37551884309fd95210c27d65484309f195210c33e5448430cf551210c2df6348430b718d210c36e5248430db549210c3765148430dd545210c27f65084309f994210c27d6508430af990210c2bd6408430cf950210c33d5408430b798c210c2dd6308430db948210c36d5208430dd944210c3755108430be980210c2f960084309f992500c27d6494030d7d0e500c35c4394030dd986500c37561940309f597400c33e54d0030cf553400c39f43d0030db94b400c36d52d0030dd947400c37551d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030e710e400c36e5290030db54a400c2f66190030bd586400c3765190030dd546400c27f6550030cf951400c33d5450030b7d8d400c2dc6350030e7d0d400c36e5250030db549400c3765150030dd545400c27e65100309f594400c27c6510030b798c400c2dd6310030e710c400c36e5210030db548400c3765110030dd544400c33e54cc030cf553300c36e52cc030db54b300c37651cc030dd547300c2de64cc030b7193300c35f54cc030e7953300c35d54cc030e7553300c31d54cc030f394b300c35d52cc030f354b300c34d52cc030f5947300c3d551cc030cf952300c33d548c030b758e300c35e538c030db94a300c36d528c030bd986300c2f5618c030dd946300c375518c030ee952300c3b9548c030be58e300c37a538c030f694e300c3db438c030f610e300c3ea528c030fa54a300c3f2618c030fc586300c3f2518c030fc546300c27f654c030afd91300c2bc644c030cf951300c33d544c030db949300c36d524c030dd945300c375514c030b7d95300c35f654c03097d95300c39f644c030b7991300c2dc644c030e7191300c29c644c030d7d51300c39e544c030d7551300c39d544c030c7551300c3ce524c030d7549300c3cd524c030d3549300c3d6514c030f5545300c2df604c030d7941300c2fb654c030ded95300c27b654c030eed91300c3b8644c030ee951300c3b9544c030bed8d300c3db634c030de94d300c3da534c030fa949300c3e9524c030fc945300c3f1514c030f6cc5300c3d9314c030af99353c82bd64d4f209f99353c833e64d4f208f99353c827d64d4f20cf59353c823d64d4f20db98b53c827e61d4f209f58753c837960d4f20d7d4e53c827e6494f209f59253c836e6294f209f98653c827d6194f20bdd8553c82f46154f209fd9153c827c6454f20d7d8d53c827f6154f20ddd8553c82776154f209f18553c83746154f209d18553c835d5314f209f99053c827d6414f20d798c53c836e6214f209f98453c827d6114f20de58053c827f6590f209f99643c827d6590f209f19643c833e5490f20cf55243c82ee62
  | 14 => 0x96320c2be648c830af592320c33e548c830cf552320c36d528c8309fd95320c33e544c830cf551320c35e534c830db949320c2f7614c830bd185320c33e540c830cf550320c36e520c830db548320c2fa600c830be580320c2be64d4430af593510c33e54d4430cf553510c2ee62d4430bb58b510c36e52d4430db54b510c33e5494430cf552510c36e5294430db54a510c37751944309f992510c27d64944309f98a510c27d6294430ddd52510c3765494430ed952510c3365494430dd552510c3b55494430cd552510c3745494430f5d0e510c3d44394430ddd4a510c3765294430f994a510c3665294430dd54a510c3e55294430d954a510c3745294430ddd92510c3766494430dd592510c3746494430dd18e510c3774394430dd90e510c3754394430dd10e510c3776294430dd98a510c3756294430dd18a510c3774294430dd90a510c3754294430dd10a510c3773294430dd8ca510c3753294430dd0ca510c3766094430dd182510c33e5454430cf551510c36e5254430db549510c27f64544309f191510c27f62544309f189510c3776554430ddd51510c3765454430ed951510c3365454430dd551510c3b55454430cd551510c3745454430f5d0d510c3d44354430ddd49510c3765254430f9949510c3665254430dd549510c3e55254430d9549510c3745254430ddd91510c3766454430dd591510c3746454430dd98d510c3774354430dd90d510c3754354430dd10d510c3776254430dd989510c3756254430dd189510c3774254430dd909510c3754254430dd109510c3773254430dd8c9510c3753254430dd0c9510c3766054430dd181510c3743054430af990510c2bd6414430cf950510c33d5414430bb988510c2ed6214430db948510c36d5214430bd984510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c36e52d0430db54b410c37651d0430dd547410c27f65904309f996410c27d6590430cf952410c33d5490430b798e410c2dd6390430db94a410c36d5290430dd946410c3755190430be982410c2f960904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c36e5250430db549410c3765150430dd545410c27f65104309f994410c27d6510430cf950410c33d5410430db948410c36d5210430dd944410c3755110430cf953310c33d54cc430db94b310c36d52cc430dd947310c37551cc430be983310c2f960cc4309f596310c33e548c430cf552310c36e528c430db54a310c375518c4309fd95310c33e544c430cf551310c36e524c430db549310c376514c430cf950310c33d540c430db948310c36d520c430dd944310c375510c430be980310c2f9600c4309fd97210c27e65c84309f597210c33e54c8430cf553210c36e52c8430db54b210c37651c843
  | 15 => 0xc27f62550309f189540c27f61550309f185540c33f6555030e718d540c33e6355030cf18d540c31c6355030cfd89540c33e6255030cf589540c33c6255030cfd85540c33e6155030cf585540c33c6155030cf981540c33c6055030cf0c1540c2be6415030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6315030d798c540c25e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f592530c27d65d0c30cf953430c33d54d0c30b7597430c35d65d0c3097597430c35f54d0c30e7953430c35d54d0c30e7553430c31d54d0c30b7583430c27f6590c309f596430c33e5490c30cf552430c2de6390c30d794e430c2fa6090c30be582430c27f6550c30cf951430c33d5450c30d794d430c27f6510c309f594430c33e5410c30cf550430c39d4310c30be980430c2f96010c30d7594430c25d6510c30b7990430c39e6410c30d7d50430c39e5410c30d7550430c39d5410c30c7550430c3da6010c30b7580430c3d96010c30af993520c2bd64d4830cf953520c33d54d4830bd987520c2f561d4830cf952520c33d5494830dbd4a520c27e64948309f592520c27e61948309f586520c36f5494830db952520c3ae5494830cb952520c36d5494830eb552520c32d5494830db152520c3cf4394830f310e520c36f6494830db992520c36d6494830db192520c36c6394830dbd0e520c36e4394830db50e520c36c4394830dbd86520c36e6194830db586520c36c6194830db982520c36c6094830cf951520c33d54548309fd91520c27c6454830d7d0d520c35c43548309fd85520c27c6154830dbd95520c36f5454830db951520c3ae5454830cb951520c36d5454830eb551520c32d5454830db151520c3cf4354830f310d520c36f6454830db991520c36d6454830db191520c36e6354830dbd0d520c34f4354830db90d520c36d4354830db10d520c34c4354830dbd85520c36e6154830db585520c36c6154830db981520c36c6054830db0c1520c2be6414830af590520c33e5414830cf550520c2ee6214830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830e710f420c36e52d0830db54b420c27f65908309f996420c27d6590830cf952420c33d5490830b798e420c2dd6390830db94a420c36d52908309fd95420c27d65508309f195420c33e5450830cf551420c2df6350830b718d420c39c4350830db949420c36d5250830bdd85420c2f46150830bed81420c2f860508309fd94420c27e65108309f594420c33e5410830cf550420c36e5210830db548420c33e54cc830cf553320c35e53cc830db94b320c36d52cc830be983320c2f960cc8309f5
  | 16 => 0xf544c930cf151324c36f524c930db149324c2f7614c930bd185324c2fb604c930be181324c2df644c930b7591324c39f544c930d7951324c35c544c930e7151324c31c544c930f3d89324c3cf524c930d7149324c3cc524c930f5d85324c3d4614c930f6d81324c2dc604c930f6181324c27e650c930cfd50324c33c540c930b798c324c3cd320c930cfd53514c33c54d45309f993514c27d64d45309f98b514c27d62d4530d7ccb514c35d32d4530af992514c2bd6494530cfd52514c33c5494530ddd46514c2bf6454530af191514c33f5454530cf151514c2ef6254530bb189514c33f5414530cf150514c37551145309f990514c27d64145309f988514c27d62145309f997414c27d65d05309f197414c33f54d0530cf153414c2de63d0530b758f414c27e65905309f596414c27c6590530cfd52414c33c54905309fd95414c27e65505309f195414c33f5450530cf151414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530be980414c2f960105309f997314c33f54cc530cf153314c33f548c530cf152314c377518c530dd146314c2fa608c530be582314c33f544c530cf151314c377514c530dd145314c2fb604c530be181314c27e650c530cfd50314c33c540c5309f997214c27d65c85309f197214c33f54c8530cf153214c2de63c8530b758f214c37751c8530dd147214c27e65885309f596214c27c6588530cfd52214c33c5488530dbd4a214c36c52885309fd95214c27e65485309f195214c33f5448530cf151214c27e65085309f594214c27c6508530af990214c2bd6408530cfd50214c33c5408530b798c214c2dd6308530dbd48214c36c5208530ddd44214c3745108530be980214c2f960085309f997404c33f54d0130cf153404c2de63d0130b758f404c39d43d0130cfd52404c33c5490130e790e404c2f66190130bd586404c27d65501309f195404c2df6350130b718d404c39d4350130cfd53304c33c54cc130eed53304c3b854cc130f690f304c3d943cc130f6ccb304c3d932cc130cfd52304c33c548c130bd986304c2f5618c130b7d92304c2dd648c130e7d52304c35e548c130d7152304c39c548c130c7152304c2dd628c130f5986304c3d5618c130f6d42304c2ee62d5030bb58b540c2f661d5030bd587540c35e63d50309f98b540c36e62d50309b98b540c27d62d5030db58b540c26d62d50309f987540c37661d50309d987540c27d61d5030dd587540c27561d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c23d6595030e718e540c33e6395030cf18e540c33f6295030cf98a540c33d6295030cf18a540c33f6195030cf986540c33d6195030cf186540c33e6095030cf182540c33f64550309fd8d540c27d6355030d718d54
  | 17 => 0x86309f996218c27d6588630dd946218c37551886309fd95218c27d65486309f195218c2df6348630b718d218c3765148630dd545218c27f65086309f994218c27d6508630af990218c2bd6408630b798c218c2dd6308630dd944218c3755108630be980218c2f96008630e7d0f408c37651d0230dd547408c2de6390230b758e408c39c4390230dd946408c3755190230dd947308c37551cc230b7597308c35d65cc230b7993308c2dc64cc230d7d53308c35d54cc230d754b308c3d651cc230f5547308c2f965cc230de597308c3f251cc230fc547308c27e62d51309f58b544c27e61d51309f587544c39f63d5130cfd8f544c33d63d5130cfd8b544c33e62d5130cf58b544c33c62d5130cfd87544c33e61d5130cf587544c33c61d5130cfd83544c33d60d5130cfd52544c35d63951309f98a544c27d62951309f986544c27d6195130de582544c35f63551309fd89544c27c62551309fd85544c27c61551309fd81544c37b60551309f994544c33d5415130cf990544c27c63151309f988544c27d62151309f984544c27d6115130af994544c33e65151308f994544c39d6315130cfd8c544c33f6215130cf988544c33d6215130cf188544c33f6115130cf984544c33d6115130cf184544c33f6015130cf580544c33d3015130cfd53434c33c54d0d30be983434c2f960d0d309f996434c33f5490d30cf152434c2de6590d30d7996434c25e6590d30b7592434c39f5490d30d7952434c35c5490d30e7152434c31c5490d30b758a434c2de6090d30cfd51434c33c5450d30bed81434c2f86050d30e7d91434c39f5450d30d7951434c35c5450d30e7151434c31c5450d30b7d89434c3db6050d30b7181434c3d86050d309f994434c33f5410d30b798c434c39d4310d30cfd53524c33c54d49309f993524c27d64d49309f987524c27d61d4930af992524c2bd6494930cfd52524c33c5494930dbd4a524c2bf6454930af191524c33f5454930cf151524c2f76154930bd185524c33f5414930cf150524c36d52149309f990524c27d64149309f984524c27d61149309f997424c27d65d09309f197424c33f54d0930cf153424c2de63d0930b758f424c39e43d09309f996424c27d65909309f196424c33f5490930cf152424c2de6390930b758e424c27f65509309f995424c27c6550930cfd51424c33c5450930e790d424c2f76150930bd185424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930be980424c2f960109309f997324c33f54cc930cf153324c2de65cc930d7997324c2df64cc930b7593324c39f54cc930d7953324c35c54cc930e7153324c31c54cc930d714b324c2de60cc930af992324c2bd648c930cfd52324c33c548c930b758e324c36f528c930db14a324c2fa608c930be582324c33
  | 18 => 0x9f986548c27d6195230cfd91548c27f62552309f189548c27f61552309f185548c33d5415230bb988548c2ed6215230bd984548c2f56115230cf953438c33d54d0e30be983438c2f960d0e30e7953438c35d54d0e30e7553438c3da60d0e30b7583438c3d960d0e30cfd52438c33e5450e30cf551438c2fb6050e30be181438c39d4310e30b7594438c35d6510e30e7990438c35f5410e30e7d50438c31f5410e30d7550438c39c5410e30b7580438c2f661d4a30bd587528c36f5294a309f992528c27d6494a309f986528c27d6194a309fd91528c27c6454a30d7d0d528c35c4354a309fd85528c27c6154a30af990528c2bd6414a30db548528c2f66114a30bd584528c27f65d0a309f997428c27d65d0a30cf953428c33d54d0a30e710f428c27f6590a309f996428c27d6590a30b798e428c2dd6390a30db94a428c36d5290a309fd95428c27d6550a309f195428c33e5450a30cf551428c2df6350a30b718d428c39c4350a30db949428c36d5250a30bdd85428c2f46150a309fd94428c27e6510a309f594428c2fa6010a30be580428c2be648ca30af592328c36e528ca30db54a328c2fa608ca30be582328c36e524ca30db549328c2f7614ca30bd185328c2fb604ca30be181328c37751946309f992518c27d64946309f98a518c27d6294630ddd52518c3765494630dd552518c3745494630f5d0e518c3d44394630ddd4a518c3765294630dd54a518c3745294630ddd92518c3766494630dd592518c3746494630ddd8e518c3774394630dd90e518c3754394630dd10e518c3776294630dd98a518c3756294630dd18a518c3774294630dd90a518c3754294630dd10a518c3773294630dd8ca518c3753294630dd0ca518c3766094630dd182518c27f64546309f191518c27f62546309f189518c3776554630ddd51518c3765454630dd551518c3745454630f5d0d518c3d44354630ddd49518c3765254630dd549518c3745254630ddd91518c3766454630dd591518c3746454630dd58d518c3774354630dd90d518c3754354630dd10d518c3776254630dd989518c3756254630dd189518c3774254630dd909518c3754254630dd109518c3773254630dd8c9518c3753254630dd0c9518c3766054630dd181518c37551146309fd97418c27e65d06309f597418c37651d0630dd547418c27f65906309f996418c27d6590630b798e418c2dd6390630dd946418c37551906309fd95418c27d65506309f195418c2df6350630b718d418c3765150630dd545418c27f65106309f994418c27d6510630dd944418c3755110630be980418c2f96010630dd947318c376518c630dd546318c2fa608c630be582318c376514c630dd545318c2fb604c630be181318c375510c6309fd97218c27e65c86309f597218c37651c8630dd547218c27f658
  | 19 => 0x550087793154021de0c550087703154021dec85500877a2154021dc88550087792154021dc48550087782154021b798c50086dd6314021d794c500875d5314021be98050087795014021cfd5254cc27e62953309f58a54cc27e61953309f58654cc27f62553309f18954cc27f61553309f18554cc33d5415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cf95243cc33d5490f30be98243cc2f96090f30d795243cc39e5490f30e755243cc35c5490f30b758a43cc2de6090f30f698243cc3d96090f30b7d9543cc35f6550f30e7d9143cc39f5450f30d795143cc35c5450f30e715143cc31c5450f30b7d8943cc2dc6050f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc2be6494b30af59252cc36f5294b309f99252cc33e6494b308f99252cc27d6494b30cf59252cc23d6494b309f98652cc27d6194b30bdd8552cc2f46154b309fd9152cc27c6454b309fd8552cc3776154b309dd8552cc27c6154b30dd18552cc2746154b30db54852cc27f65d0b309f99742cc27d65d0b30b798f42cc2dd63d0b30e790f42cc27f6590b309f99642cc27d6590b30b798e42cc2dd6390b309fd9542cc27d6550b309f19542cc39e4350b30bdd8542cc2f46150b30bed8142cc2f86050b309fd9442cc27e6510b309f59442cc2de6310b30b758c42cc36e52ccb30db54b32cc2fa60ccb30be58332cc2df64ccb30b759332cc35e54ccb30d715332cc35e52ccb30f394b32cc3cd52ccb30b798332cc3da60ccb30f658332cc2be648cb30af59232cc2f7614cb30bd18532cc2df654cb30d7d9532cc2df644cb30b759132cc35e544cb30d715132cc3cf624cb30f3d4932cc35e524cb30f314932cc3d7614cb30f518532cc2dc604cb30db94832cc36d520cb30f34c832cc2fa600cb30be58032cc37751947309f99251cc27d64947309f98a51cc27d62947309fd9151cc27c64547309fd8951cc27c6254730d7cc951cc35d3254730dd54451cc27f65d07309f99741cc27d65d0730b798f41cc2dd63d07309fd9641cc27e65907309f59641cc2fa6090730be58241cc27f65507309f59541cc27c65507309fd9441cc27e65107309f59441cc2de6310730b758c41cc37651cc730dd54731cc2fa60cc730be58331cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730b798f21cc2dd63c87309fd9621cc27e65887309f59621cc27f65487309f59521cc27c65487309fd9421cc27e65087309f59421cc2be6408730af59021cc2de6308730b758c21cc2fa6008730be58021cc2de63d0330b758f40cc39d43d0330bd987548c2f561d52309f98b548c27d62d52309f987548c37661d52309d987548c27d61d5230dd587548c27561d5230de983548c33f54952309f98a548c27d6295230
  | 20 => 0x873d548c821d794e320875d538c821bd98632086f5618c8219fd95320873e544c821cf551320875e534c821d754d32086f7614c8219fd94320867d650c821cf950320873d540c821d794c320875d530c821f34c832086f6610c821bd584320867e63944219f58e510867d65cc421cf953310873d54cc421d794f310875d53cc421bd597310877565cc421bd99331086f464cc421ed95331087b554cc421ddd4f31087d653cc421dd54f31087d553cc421d554f31086f562cc421dd94b31087d732cc421f54cb31086f560cc4219fd96310867d658c421cf952310873d548c421d794e310875d538c421bb98a31086ed628c421bd986310867f654c421cf951310873d544c421d794d310875d534c4219fd94310867e650c4219f594310867c650c421cf950310873d540c421d794c310875d530c421bb98831086ed620c421bd5943108775650c4219d59431086f6640c421bd19031087b6540c421ed55031086f6630c421f598c3108777530c421f594c3108775530c421f554c31087e6620c421bd58831087e5620c421b95883108776520c421bd580310875e53c8421d754f21087ce53c8421f354f21087e731c8421f90c7210875e5388421d754e21086ed6288421db94a21086f66388421bd18e21087d65388421f554e21086f56288421dd94a21087e65288421bd582210867f6548421d794d210875d5348421bbd95210876f65484219bd9521087ce5348421f354d21086ef6148421db94521087e63148421f94c521086f76548421ddd9521086776548421bd98d21086f46348421f594d21087d55348421bdd8921087e76248421dd94921087e65248421f98c921087e53248421bdd8121086de63d4021b758f500875e53d4021d754f500875e5394021d754e500877b50940219f98e500867d6394021ded4e500877a5394021f694e500875a5394021de54e50087d95394021d654e50087785394021fc98650087f33194021fc0c650087eb2194021fc88650087e92194021fc486500877b6394021de98e50087796394021de18e500877a4394021de50e50087784394021de18a500877b3294021de8ca50087793294021de0ca50087786194021decc6500877a3194021de4c650087783194021dec86500877a2194021de486500875e5354021d754d500867f63540219f18d50087766154021ddcc550087743154021dd88550087752154021ded95500877b5354021de94d50087da5354021d694d50087795354021f654d50087595354021de14d50087f26154021fccc550087f03154021fac8550087f22154021fa48550087f12154021ded8d500877a6354021de58d50087786354021de90d50087794354021de10d500877a6254021decc9500877a3254021de4c950087783254021de98550087726154021decc550087733154021de8c
  | 21 => 0x6254d219fd8553487776154d219dd85534867f6054d219f181534867e6514d21d754c534867e6414d219f590534875e6314d219f980534867d6014d219fd96434867e6590d219f596434867c6590d21d7d4e434875c5390d219fd95434867e6550d219f595434867c6550d21d7d4d434875c5350d219fd94434867e6510d219f594434867c6510d21e750c43486ee6210d21bb58843486f66110d21bd584434867e65cc921d7d4f324875c53cc921bd98732486f561cc9219f99632486be648c921af592324867c654c921d7d4d324875c534c921bdd8532486f4614c9219f994324867e65cc521d7d4f314875c53cc521bb98b31486ed62cc5219f996314867f654c5219f595314867c654c521d7d4d314875c534c521bbd8931486ec624c5219f994314877653c8521dd14f21486f560c8521f9d46214867e63d41219f58f504877761d4121ddc87504877b5094121b7d8d50486dc6354121de540504867e63141219f58c50486be64d4c21af59353086fa60d4c21be583530867e64d4c21cf993530863e64d4c219f593530873d64d4c218f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c21de983530867a60d4c219f583530877960d4c219e583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530865d6594c21d7d52530875e5494c21e7952530871e5494c21f5186530875f6494c21d7992530875d6494c21d7192530875e6294c21d718a530875e6194c21d7186530875f6094c21d7982530875d6094c21d7182530873e5454c219fd91530867c6454c21d7d8d53087746154c219fd81530867c6054c21d7d95530875f5454c21d7951530879e5454c21c7951530875d5454c21e7551530871d5454c21f5185530875f6454c21d7991530875d6454c21d7191530875e6254c21d7189530875e6154c21d718553087546154c21d7085530875f6054c21d7981530875d6054c21d718153086be6414c21af590530873e5414c21cf55053086de6314c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530865e6314c219f988530876e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd96430867e6590c219f596430867c6590c21cf952430873d5490c21d794e430875d5390c21bb98a43086ed6290c21bd98643086f56190c219fd95430867e6550c219f595430867c6550c21d794d430875d5350c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c21d794c430875d5310c21e750c430867e63948219f58e520867d65cc821cf953320873d54cc821d794f320875d53cc8219fd96320867d658c821af99232086bd648c821cf952320
  | 22 => 0x31de540500c6be64d4f21af59353c867e64d4f21cf99353c863e64d4f219f59353c873d64d4f218f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c87776154f219fd8153c867c6054f21d754c53c867e6414f219f59053c875e6314f21db98853c87756114f219f98053c867d6014f219fd9643c867e6590f219f59643c867c6590f21cf95243c873d5490f21bd98643c86f56190f219fd9543c867e6550f219f59543c867c6550f21bdd8543c86f46150f219fd9443c867e6510f219f59443c867c6510f21d794c43c875d5310f21e750c43c86ee6210f21bb58843c875f53ccb21d714f32c86be648cb21af59232c875e538cb21d754e32c86f6618cb21bd58632c875f534cb21d714d32c86f4614cb21d794c32c875d530cb21bd98432c86f5610cb21d794f31c875d53cc721bb98b31c86ed62cc721bd59731c877565cc721bd99331c86f464cc721ddd4f31c87d653cc721dd54f31c87d553cc721f998b31c86f562cc721f958b31c87d732cc721f54cb31c86f560cc721d794d31c875d534c721bbd8931c86ec624c721bd59431c8775650c721bd99031c86f4640c721f598c31c8777530c721dd54c31c86f5620c721bd58031c877b50943219f98e50c867d63943219fd8d50c867c6354321dd58550c87773154321dd0c550c86de6314321b758c50c877950143219f993538867d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21d754c538867e6414e219f590538875e6314e21db58853887766114e219f980538867d6014e219fd96438867e6590e219f596438867c6590e21bb98a43886ed6290e219fd95438867e6550e219f595438867c6550e219fd94438867e6510e219f594438867c6510e21e750c43886f66110e21bd584438875e53cca21d754f32886f661cca21bd58732886be648ca21af592328875e534ca21d754d32886f7614ca21bd18532887cd320ca21d7d4f318875c53cc621d794e318875d538c621bb98a31886ed628c621d7d4d318875c534c621d794c318875d530c621bb98831886ed620c621bb597218876d65c8621bd597218877565c8621dd94f218877453c8621bd583218877b50942219f98e508867d63942219fd8d508867c6354221dd98550887772154221de540508867e64d4d219f593534867e60d4d219f58353486be6494d21af592534875f5394d219f992534873e6494d218f992534867d6494d21cf592534863d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f582534867f6454d219f191534875f6354d219fd89534876f
  | 23 => 0x7151324c7cf624c931f3d49324c75c524c931f3149324c74c524c931f5d85324c6dc614c931f5185324c67e650c931b798c324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d05319f595414c67c6550531b7d8d414c6dc6350531dd14b314c7d732cc531f54cb314c6f560cc531b758a314c7d7518c5319f993504c67d64d41319f98b504c67d62d4131d7ccb504c75d32d4131ddd87504c77731d4131ded42504c6bf6454131af191504c6ef6254131bb189504c77950141319f990504c67d64141319f988504c67d6214131d798f540c67e62d50319f58b540c77661d50319f983540c67d60d50319f596540c73f54950319f98a540c67d62950319f982540c67d6095031cfd91540c67f62550319f189540c67f60550319f181540c73d5415031bb988540c6ed6215031be980540c6f960150319f98c540c75e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f592530c67d65d0c319fd96430c67d6590c31cf952430c73d5490c31bd986430c6f56190c319fd95430c67f6510c319f594430c73e5410c31cf550430c79d4310c31bd984430c6f56110c31dbd4a520c67e64948319f592520c67e60948319f582520c67f64548319f191520c77461548319fd81520c67c6054831af990520c6bd6414831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d0831b798f420c6dd63d0831bd987420c6f561d08319fd96420c67e65908319f596420c6de6390831b758e420c76e5290831db54a420c67f65508319f595420c67c6550831cf951420c73d5450831db949420c76d5250831bdd85420c6f461508319fd94420c67e65108319f594420c75e53cc831db94b320c76d52cc831bd987320c6f561cc8319f596320c6be648c831af592320c67f654c831d794d320c6f7614c831db948320c76d520c831f34c8320c6f6610c831bd584320c67e64944319f592510c67d65d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd63904319fd95410c67e65104319f594410c67c6510431b798c410c6dd6310431d754b310c6dd638c431d794e310c6f5638c431dd94e310c7d6538c431bd98a310c6f5608c4319fd95310c6df654c431d7d95310c65f654c431d7549310c6df614c431d7945310c7d6414c431f5505310c6f7654c431ddd95310c677654c431bdd8d310c7d7634c431dd94d310c7d6534c431f590d310c7d5434c431bd189310c6f7604c431ded42500c67e64940319f592500c67e62940319f58a500c67f64540319f191500c67f62540319f189500c7766154031dd8c5500c7753154031af990500c6bd6414031bb988500c6ed6214
  | 24 => 0x50cc67c64543319fd8950cc67c6254331d7cc950cc75d3254331dd58550cc6be6414331af59050cc6ee6214331bb58850cc7795014331be983548c6f960d52319f98b548c67d62d5231dd987548c67e60d5231de983548c67a60d52319f583548c77960d52319e583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c67f62552319f189548c67f60552319f181548c73d5415231cf953438c73d54d0e31bd987438c6f561d0e31cf951438c73d5450e31bdd85438c6f46150e31e750c438c76f5294a319f992528c67d6494a319f982528c67d6094a319fd91528c67c6454a319fd81528c67c6054a31af990528c6bd6414a31db548528c6fa6014a31be580528c67f65d0a319f997428c67d65d0a31cf953428c73d54d0a31b798f428c6dd63d0a319fd96428c67e6590a319f596428c6de6390a31b758e428c67f6550a319f595428c67c6550a31cf951428c73d5450a31bdd85428c6f46150a319fd94428c67e6510a319f594428c6f66110a31bd584428c6be648ca31af592328c76e528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c7cd320ca31b798e418c6dd6390631b7597318c75d65cc631d754b318c6f565cc631dd597318c77652cc631bd583318c6be64d4231af593508c77b50942319f992508c67d64942319f98a508c67d62942319fd91508c67c64542319fd89508c67c6254231dd985508c7773154231de540508c67e62d51319f58b544c67e60d51319f583544c73f5495131bb98a544c6ed6295131d758e544c67e6295131db98a544c66e62951319f58a544c76d62951319b58a544c77561951319f982544c67d6095131d7d8d544c67f62551319f189544c67f6155131ddd85544c67f60551319f181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d6015131cfd53434c73c54d0d31bd987434c6f561d0d319f996434c73f5450d31cf151434c6f76150d31bd185434c67e6510d31e750c434c67e64d49319f593524c67e60d49319f583524c6be6494931af592524c76f5294931db548524c67e64149319f590524c67e60149319f580524c67e65d09319f597424c67c65d0931cfd53424c73c54d09319f996424c67d65909319f196424c6de6390931b758e424c76f5290931db14a424c67f65509319f995424c67c6550931cfd51424c73c5450931dbd49424c76c5250931bdd85424c6f461509319f994424c67d65109319f194424c6de6310931b758c424c6f66110931bd584424c67e65cc931b7997324c75e65cc931d7953324c75c54cc931d714b324c6de61cc931af992324c6bd648c931b758e324c76f528c931db14a324c6f6618c931bd586324c76f524c931db149324c6f7614c931bd185324c75e544c931d
  | 25 => 0xb3e5410c32cf550430cb5e5310c32e750c430caee6210c32bb588430ca7e6494832cf992520ca3e64948329f592520cb3d64948328f592520ca7d65d0832cfd53420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420ca7f6550832cfd51420caf76150832bd185420ca7e65108329f594420ca7c6510832b798c420cadd6310832d7953320cb5c54cc832af992320cabd648c832b758e320cb5e538c832eb992320cbad648c832bb58e320cb6e538c832f394e320ca7f654c832bdd85320caf4614c832b7d95320cb5f654c83297d95320cb5e544c832d7151320cadf624c832d7949320cbce424c832f3509320cbd7614c832f5185320caef654c832dbd95320ca6f654c832bbd8d320cbcf634c832db94d320cbce534c832f390d320cbcd434c832f9d85320cbe4614c832ddd46510ca7e64944329f592510ca7e60944329f582510ca7f64544329f191510cb5f3254432d74c9510ca7f60544329f181510cabe6414432af590510cb755114432be980510caf96014432bd986500caf56194032ded42500ca7e64940329f592500ca7e6194032dd986500ca7661940329f586500cb7561940329d586500ca7f64540329f191500cb5f3254032db8c9500cb5d3254032db4c9500ca7f61540329f185500cabe6414032af590500caf66114032bd584500cb795014032bb98b54cc6ed62d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc67f62553319f18954cc67f60553319f18154cc73d5415331d798c54cc67e62153319f58854cc77561153319f98054cc67d6015331cf95243cc73d5490f31bd98643cc6f56190f31cf95043cc73d5410f31e750c43cc6f66110f31bd58443cc6be64d4b31af59352cc6be6494b31af59252cc76f5294b319f99252cc73e6494b318f99252cc67d6494b31cf59252cc63d6494b319f98252cc67d6094b319fd9152cc67c6454b31ddd8552cc67f6054b319f18152cc76d5214b319fd9742cc67e65d0b319f59742cc76e52d0b31db54b42cc6f661d0b31bd58742cc67f6590b319f99642cc67d6590b31cf95242cc73d5490b31b798e42cc6dd6390b319fd9542cc67d6550b319f19542cc6f76150b31bd18542cc67f6510b319f99442cc67d6510b31cf95042cc73d5410b31b798c42cc6dd6310b31db94842cc76d5210b31db94b32cc76d52ccb31bd98732cc6f561ccb31d795332cc75c54ccb31d794b32cc7ce52ccb31f354b32cc6de61ccb31f598732cc7d561ccb31af99232cc6bd648cb31bd18532cc6df654cb31d7d9532cc75e544cb31d715132cc7cf624cb31d794932cc7d7614cb31b718532cc7d4614cb31b518532cc76e520cb31db54832cc6f6610cb31bd58432cc6de63d0731b758f41cc77b50943319f99250cc67d64943319f98a50cc67d62943319fd91
  | 26 => 0x2d0d32b398b434cbcd62d0d32b7587434cadd60d0d329f996434cb3e5490d32cf552434cade6390d32cfd51434cb3c5450d32bbd89434caec6250d329f994434cb3e5410d32e750c434cade6510d32d7994434cade6410d32e7990434cb5f5410d32e7950434cb5d5410d32e7550434cb1d5410d32b7988434cadd6110d32b7580434ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d0932e710f424cade6390932b758e424ca7d65509329f195424cadf6350932b718d424cb9c4350932f3d0f324cbcc43cc932bb583324cabe648c932af592324cade648c932e7992324ca9e648c932e7592324cbcf528c932b7586324cadd608c9329f993514ca7d64d45329f983514ca7d60d4532ddd53514cb7654d4532dd553514cb7454d4532f5d8f514cbd743d4532f510f514cbe732d4532f58cb514caf560d4532ddd93514cb7664d4532dd593514cb7464d4532ddd8f514cb7743d4532dd90f514cb7543d4532dd10f514cb7762d4532ddd0b514cb7642d4532dd50b514cb7732d4532dd8cb514cb7760d4532dd983514cb7560d45329d583514cb7460d4532ddd46514cb7551145329f990514ca7d64145329f980514ca7d6014532bd994514cb766514532ddd50514cb765414532dd550514cb745414532f558c514cbd74314532f510c514cbe73214532f58c8514caf56014532ddd90514cb766414532dd590514cb746414532ddd8c514cb774314532dd90c514cb754314532dd10c514cb776214532ddd08514cb764214532dd508514cb773214532dd8c8514cb753214532ddd80514cb766014532dd580514ca756014532dd180514cb7751d4132dd147504ca7e64d41329f593504cb7761d41329f987504ca7d61d4132dd187504caf66194132bd586504cb775194132dd146504cb7b5094132afd91504cabc6454132bdd85504caf46154132ddd45504cb745154132af990504cabd6414132bd984504caf56114132ddd44504cb745114132de540504ca7e6414132cf990504ca3e64141329f590504cb3d64141328f590504cb5f4314132d710c504ca7e6114132dd984504ca7661141329f584504cb7561141329d584504cb5e63d5032db98b540ca7e61d50329f587540ca7e60d50329f583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540cb3f64550329fd85540ca7c61550329fd81540ca7c6055032cf550540caf66115032bd584540cafa6015032be580540ca7e6315032d798c540ca7e6215032db988540ca7e6115032dd984540ca7661150329f584540cb7561150329d584540ca7e6015032de980540ca7a60150329f580540cb7960150329e580540ca7d6494c329f597430cb5e53d0c329fd96430ca7d6590c32cf952430cb3d5490c32bb98a430caed6290c329fd95430ca7f6510c329f594430c
  | 27 => 0x32b798f42ccadd63d0b32e710f42ccabe64d4732af59351ccb7751947329f99251cca7d64947329f98251cca7d60947329fd9151cca7c64547329fd8151cca7c6054732dd54451ccaf66194332bd58650ccb7b50943329f99250cca7d6494332d7d0e50ccb5c43943329f98650ccb7661943329d98650cca7d6194332dd58650cca7561943329fd9150cca7c64543329fd8550cca7c6154332af99050ccabd6414332bd98450ccaf56114332de54050ccb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f6395232cf58e548cb3e6295232cf18a548cb3f6195232cf986548cb3d6195232cf186548cb3f6095232cf982548cb3d6095232cf182548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cfd95548cb3d6355232cf989548cb3c6255232cfd85548cb3e6155232cf585548cb3c6155232cfd81548cb3e6055232cf581548cb3c6055232cf550548cb3e54d0e32cf553438caee62d0e32bb58b438cb3e5490e32cf951438cb3d5450e32bbd89438caec6250e32cf950438cb3d5410e32e750c438cb3e54d0a32cf553428cade6390a32b758e428cb3e54cca32cf553328cadd65cca32d7597328cb5e54cca32e7953328cb1e54cca32e7553328caed65cca32db597328cbae54cca32eb553328caed60cca32af993518cabd64d4632cf953518cb3d54d4632cf952518cb3d5494632ddd46518ca7e64946329f592518ca7e60946329f582518cb3e5454632cf551518ca7f64546329f191518cb5f32546329fd81518ca7c6054632af990518cabd6414632cf950518cb3d5414632dd544518cafa6014632be580518cabe64d4232af593508cb3e54d4232cf553508cb3e5494232cf552508caf66194232bd586508cb7b50942329f992508ca7d64942329f986508cb7661942329d986508ca7d6194232dd586508ca756194232cf951508cb3d54542329fd91508ca7c6454232d7cc9508ca7f61542329f185508cabe6414232af590508cb3e5414232cf550508caf66114232bd584508cb795014232d758f544ca7e61d51329f587544ca7e60d51329f583544cb3f5495132bd986544caf56195132d758e544cb6d62951329f986544cb7661951329d986544ca7d6195132dd586544ca7561951329f982544ca7d6095132bdd85544caf46155132bed81544caf86055132d7d8d544ca7f6255132dbd89544ca7f6155132ddd85544ca7761551329f185544cb7461551329d185544ca7f6055132ded81544ca7b60551329f181544cb7860551329e181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d6015132cfd53434cb3c54d0d32bb98b434caed62d0d32d7997434cb5f54d0d32e7d53434cb9c54d0d32b798b434cbce6
  | 28 => 0x98a5090e7d62942439f9865090f7661942439d9865090e7d6194243dd5865090e756194243cfd0d5090e7f62542439f1895090e7f61542439f1855090eee6214243bb5885090ef66114243bd5845090f795014243e7d4e4350ebd6090d43cf90f5250e7e61d49439f5875250e7e60d49439f5835250f6f5294943bdd855250ef46154943bed815250ef86054943db5485250e7e61149439f5845250e7e60149439f5805250e7e62d45439f58b5150e7e60d45439f5835150f775194543be9825150ef96094543dd5445150e7e62145439f5885150e7e60145439f5805150e7e62d41439f58b5050e7e61d41439f5875050ef66194143bd5865050f7b5094143bb9885050eed6214143bd9845050ef56114143de5405050f3e43141439f9885050f6e62141439b9885050e7d6214143db5885050e6d62141439f9845050f7661141439d9845050e7d6114143dd5845050e756114143b75924310e9d6490c43d79524310f9e5490c43b758a4310ede6090c439fd954310edf6550c43d7d954310e5f6550c43b7d914310f5e5450c43e79514310edf6250c43b71814310f9f6550c43a7d954310f1f6550c43e7d894310e9f6250c43e79894310f9d6250c43e71894310f9f6150c43e79854310f9d6150c43e71854310f9f6050c43e79814310f9d6050c43e71814310e9c6050c43e750f5210f9d4394843dbd4a5210e7e61948439f5865210e7e60948439f5825210f9d4354843bdd855210ef461548439fd855210f7761548439dd855210e7c6154843dd1855210e7461548439fd815210e7c6054843e750c5210f6d5214843bd9845210ef56114843be9805210ef96014843e750f5110f9d4394443ddd465110e7e62944439f58a5110e7e60944439f5825110f9d43544439fd895110e7c62544439fd815110e7c6054443e750c5110eee6214443bb5885110f755114443be9805110ef96014443e750f5010f9d4394043bd9865010ef56194043ded425010e7e62940439f58a5010e7e6194043dd9865010e7661940439f5865010f7561940439d5865010f9d4354043d790d5010f5d4354043c750d5010e7f62540439f1895010e7f61540439f1855010f9d4314043bb9885010eed6214043bd9845010ef56114043de5405010ef661d5332bd58754ccb3f54953329f98654cca7d61953329f98254cca7d60953329fd8554cca7c61553329fd8154cca7c6055332cf55054ccb5e6315332db58854cca7e61153329f58454cca7e60153329f58054ccadd65d0f32d759743ccb5d54d0f32b798b43ccadd61d0f32b758343ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32e799043ccb9e5410f32d755043ccb9d5410f32c755043ccade6210f32f398843ccbcd6210f32b758443ccadd6010f
  | 29 => 0x2003c003000000700240020000003003c00f00b40070000017000801f0020007000000f001800b00740050000004000002e000c011001c0020010007001800200040000024002000001100080270000002000002d0008000001800000540020008004000000000000020004000000800200040060008004001800100bc002002c01e000000000040060020008009c0060040009001c0010010002000400c001c00000040010008002001c0080020015001c006000c003000000600280010018027001c000003c0010020001000000000300040088000000400100140030004000000c0040004004000400200940030038000002c0000020013000800000000000010001000400c003000100000000044000000800d002000900040000004001000c00000000030000000000000f0004006000c006003000200540050000016000c02600b8027000800c0004014000c0200040003001c0000018002000000200000000038015001000a0008001001400200140010004006001401e000000000740090000002000000000300070018001000000000680050000004001800a0008005002400100440090000002004c0060000000000400000300010030006001001e0020004000001d000c000002000e000c00d002c000001c001001801200040150028007003400c00000000024003000c0170004000002c001000000d0010007001c000000400200700050000004001c000001400900040070030005002400000180060000004000c00e001800000440160020015000000300040000020024001000a00000000000006000800100380050008001000800e000000c00340010014010003000b00100110064000001000500100000004007002800200080100004001001c0000000001005800c001000200080000038003001c003000c000000c00400080030000000000003a0004006000000000000010000003001400900340060010000000000f001800400d4000000000c000800b0008009001800700000010000000000000300080090000000005000900480060004000000c00000580020000000000000700040040048003001000900000050004015000001e0000002003402d000001a00480000000005000400a0000003000000a0014001000400100080010034008000c0050004003003800100000010008006000800b003400500000030000005000c02b0002dd65d0e43d75974390ef661d4a43bd5875290f6f5294a439f9865290e7d6194a439f9825290e7d6094a43d7d0d5290e7f6154a439f1855290e7f6054a439f1815290f6d5214a43bb98b5190eed62d4643ddd465190e7e62946439f58a5190e7e60946439f5825190e7f62546439f1895190e7f60546439f1815190f755114643bd9865090ef56194243ded425090f5f43942439f
  | 30 => 0x10004000001000600100000014000000000b0004000002c00f005c00600300040010008000400b000000800080000000001001c0000000000000800200000030000001006c0000000002000c00000a000600000000040008000000100080010054007001000000100040000005000000100080020010008001400000000020008007006c000007c00100080060004001000c009004c0040008000005800000000010004000000000000880060018003001c00e0008003001400400200050000002000801100040010018005000c000002c00100000050000000000c01b00080050004000001c00000040010000006001400300000040000003000c00100400050000008004803f00080030000000000000200000090000003000800800000010014003000800000100000010000000400000180000000000002c0000004007001000200100040018000002800500140000004000000000b00100040000000004c000000000100040040000000000400000480120018004001000100600000000009001c000000001f003c0040000002000400c000000000280070088000000c001000400700580000008000001800100080010004000000400000000090090016000000100000020000002000c000001400500000040004000000c0020000000002400600740000024035001c000000c0030004014000000e005c00200480000018000005801000040060004017000800100740020018006000000200040070008002000000b00180010018000000c011000000000000010064002000400200040000004004000401a0000000000800900000010018001003c00d000400000080070008000000000300640040050003000000500240100000004000003200100000028008002400300040000090009000000000240000000038000c0080094000004c0000004005001c0010004000002000000240000004005002c00000180010000002000000100180000004000002c002006400400000030024010004c0000010005000c000000400300000020018000000000e0000002000000000580000008000000c00300380000004016000400200100000014000001000900000000018000004c00000300110000000000c0220000003000400a002c00a008800600180020040000002c0000000001002c00c000c01700000020010007000000100080000014000001400100ec01f000c001000c00a00040010020001000c003000800100180000040000001c000005800c0024023000c001000000b004400900000040010015003c021002c00e002c01b000000000100010004007000000700180000000002000400000440050004016000000500100020014000000c002000000700600050000003004c00a0000013000000700480040014000000c000001800d00
  | 31 => 0x4008003c00200000040034000000002a0000001000400000040060008001001000a0010008002c00c00000040008004000000200000010000000002000100280070024007000800d0004007007000900180020000001000800000080150018000000400b000000000080090000007000000000100020000000000c01c0010008000000000300000000000000002300000010030000005c00100040200004000006c00400040070088016000400c000000600200140000004002401500040000014005000000000080000000000000000c0028001000c004000400000000010014003004800500000000008002005800c0024005000c0080000002002c0160000002007000600640000004000001c0000004001000000a000001100040030008003000800000000140018000000800200000020038005001800200000020078001000000000440100000005000c00700040000004004005c001000400c000800a0020002003c00f0000002002800000000000000000002800200040150008001000800200040070014000001000b001400900140160020000001c000000402900000010000001005400000440130010006001c00400040010008004000800e000400b001400c0000000000c00e000c01a003000b000400500440010004018001402c0000003000801c00000040004001001400100080000044000002c0030024000000000100040000074011000000000000050000000003000900080090010002000800300000050000000000401000000050054010000c0180008000001400500040070000000000000400040070018000000801000340020024000000400a00000590000020000000800040000004002000000300000060010000000c000000c0000068004003000100580040058002007c015000000d000c00000640000024000002000900000000098001001000b0004005000c0110010007003000100000020000037000000000140000058002000801a00000050020006001000200180180020006002800100040090054001007400d0018001008c006000001a000800600000000018000001800100300000008000000800400340080030000000001600080050000000000800000040000034000000000000400080008001001000300340000058001009c000000c001000001f000000200200020008000001c000000001300000120018004000000000100140018002002c000001c00500000290000000002400000000050014006000000f0000000000c0010000015001c02400340000028001000000700100010008000000800f0008006003800000000010048004001801c000c00200000060028011001000700a00010004001000400000000000010001004000400200040020000004400300000000018001000c00100000
  | 32 => 0x10000001000c0020008000001400300080000034002005000100000030038003000000400bc00000000050000000001c0070000000000000b001c0010004005000c00c001000000000040004002000000900240020010009002c007002c00a001c003000000000000000004010001400a000800a001001b00380000008008000c0020054001001800c00100000030005001802d000405b001000a00000030000004001c000000001600100020008000000c01e00200010014002003400600080080004014005c0000048001000c001000000000400030000000001402300500060010000002c00100040220024000002000000040000000000003800000480020014002000c0000010004003000c000000b0004000000c007001400a0000001000400100000020050003000c00000000260000005003c001000801200300010010000004400000480060004018000c00000440020048000000c0020004004001801e000400c00080030008000000000000040050004001002000100080040008005001000b001000f001000300000040000000002000500000000044002000400000180090020009008c006001c0010010000000000f0028006001800300140030004002000c000000800500080000014000001c00a0000002001c000000c0000004001001405300e0003000400200580030000009008c0000044000000000d0028001000001e001400200040010008001000000000080000004005000800a000400e000400000540020028001005400200080000000011001c003000c001000000900140070014000002000e001c02300040000008022000800100780010004000000800200040000000001002c002003c010000000500000080028001000400c002800000000040044009002c000000001b0014000006800a000c0030004001001c007000401f0018000003400000100000004004000000c00080050000007001402800080040080003000002300080040000003003c00100140060008004000400f005c000003000b0038007000000900040010028011000000500040010000004003c005000001b000c00700100000020013000c004000400c0018003000000000600070000000001000d00000010044000000402c00100000010001000000500000000008001000000600000010000003000800000080030000002009c0000010001000000d0000003000c0020004001003000000200020000001000000800000030000000001c0060108002001800200340000000000000000100d8001001c00100180020048000001800200000090008003000400100040050004010000800c0014003003400500000050000006000800100000050038004000c007002c00500000000000000000c0010008007000400700040030008014000800c0
  | 33 => 0x46504d90002950000143722600000000000000000026b1d7434200de0f640000002e875e5892dbf528c05b500000002ec75a60000000000000000002099394495a03691f4de6588249600003840000ced0cc0000a4b88d280f45a6b159ea496a00006e4ac0a3bc800087300005e319740d35a7f000251699eaeac8aa1262a35aec88979b8e1e99f8e75b2a504f9d05600019ac769a3800000f5103712b00000bb0aa90ab9000170e35a1eec213511400003da401c350b431308000000082e9b895ea131a000092e1788000688a9b6a464000371abe8324000071d0000882289657b299c0544a1449bc4be000000095467780000000000234200029b20001c4c370a5bc930883d34a2b2c46f24b2c0a000076f29d15ef03ea703c0005c11dbe222226e3430bfc01490a45da022c3e75cee0000a9e9d493a9a2912d2a468bf61d00000c359f5705e0c9e2cbc000000155a282c4dd0e898d29f70ca2a0011f66a586d26040000000192a3b400003564afe0002acc305e58ea430d767d7439934bcac933a0aaa1829d5d0001a592a080000dc8000b23e30a4d5853e7e3c11b429825f000000080c1c782b9a29900000009c680000000000bb2ad7181da81e280a8660ea40000070002002c003001c000007400100000040018000001800100d80020000019000000300000000058021001c000002400b0010001002002400140060038009000c003000000000080000028002002002d000000b0008002004c004000401c000400a0020003002000500000000004000001c00900140020000000000801500000000024003001000600040000004000001400b00080020050004000000e0014000001c00e00040000000005000c0050024005006803d0000000000000000cc00c000400e0040007000402300000020000000003400a000400000000000000000003c00000b8001000c0060014000004400400180090040001002c0060040002000c008000400000040000004002001c01900280030000001000800a001000f0000003000800300080120048000000000e00000090000006001800100a0000003c004000800100000090000008002c002002800c00080000008000001c000002c003000400b0008001000c0000014000000c00200500010004000000c00d000000a0048004000c005000000d001000200100000004009000001900180020004002001c001000000a000401800f80040020002000000900000100010001003c00c004c007000c004000c0000004000000400100300000028028001c0000010001001c01f0000005000001f000400900140060008000000c001000c000002400f0000005002400700140000014000001000000100000030001000000000300000010000000400000100000014009000000500480000028003002c0000004
  | 34 => 0x8471b84041a193030e9b1a2e0000000050f218269242e83ef244e0000000283289c7ab2d682439082b67aac0646a7b44a8187412b2f506a3048017f248c0c117c684f2b345a1825e642b004ba4062400000ca0002e8ca9716e079b30b00001d830002df400002f23ea176cb46981100026100630b8e080950c08502e5114026064d973c00021db0a2c2bf0e5ccb28050000000289000000000000000000000000000000001b1577a58ee1016343979a2ce5a00f643831ca69ecde0800000000000a9a10912866ee16220cd8f27ae68dfe44fa553020907c9d95f901d90d7c95889b260b4c30ba80ada8ae30af0001dc89aa8b18b4f1a5e8a09e8c000294cbbf09d75114d29798229aaab2ee298f904c0edb0bcb3ba2749f128aa76b23108f16b8098d03299188b7874013448990fed0001d30952caf006bc636616a34168024891e2861e9c1234c0b1a4aa6c7ac70334a81a1ac09bc6209678058da8a3d283ae5fe91d847d297d245b0865452a3fb4a072121b5d498af207192780004e906e43151c9c7a01e3021a9ab90890f689a217aebd1951a3be9830bcac442000292c34aae747e59e9120761668086618565ab6258a9c646f92b8a11462c99f9a930a8b0000a635fd964197c2000000000013be000234a8ff85ea00000002e282751aa9d7045f222a606e9249ae80000000000000074813907be661842c9c70a840f20f5914b68a82be68f699c9aa887fe26d0221d1ebf005c479e18da9da04b69b50000b549e5e8cd89b456e000000006d67c397674d808c60d9a70c00025f2bed20f209aa0906ea000023a80003d3945c058400000011cd0001a62bfb00000001dfc00000000001bde00012de63c91020002900000139e3a680004df40000a105481670e6e03580001040000266a303561154464100342898ebea2c85cbc18a7f89ab9c9018d4b8d9e299129ef979aaec2a4e2f9926829d9e54bfa00005105b4c49549580002bf689890fe3dc91d475a0eac3d8127200029632300b58a3d14f439f2d605281be2a8f22f2029c39a5af8f1a39a97f218e843a02d1cdcb2290f34442ab0598951ea58a22879c1c5800024667d4171c495232aa2c0000000000058380000000b65a2b165a0000c8c1501a5300012a2000071275825720000f9249080008c05abd7239cca59f1c0800000000000512a3080000000a9c31b80000002c6871f000000028135272e583ca0ebf7489d2622b15ee0002ba00000000bab82dc24297a0c0500002046f6a7da813a0002a59793ed360cd2328bdc2e750001c00000046700b2fe01c6af140da906b2332134bb6affc5054d24000168ebb997520d9099c75919bec162034a699b6236c8ea000023e018c07e2b000000a7d1b02b6500ab1f5052c54600002282838054c328b8507aeb59e5e92ba40a445080008c48656
  | 35 => 0x69b213ea227df4451f0000b56af97000236f7410ac27a0925d27948109fe8dda78600001c42bfe4c58e521a92cc4767000000012e4000021c64780000000f6a2af28d03870000ad400000001f1647282d8192a7a94d7c0000002b4ca688000bd46ba398303d518a92230b681a09dbabb80001e3600017165b08000c42233eb78d4161eeacfa0001d36c2e93120001e27739d5e60001081acd9b812b32548708d0cc83304725c428ea9201754a871f4e8db560abb4a0640000c2aae39c100040c0b36f26986fd9fbc4ea13aaa509c987778230744ab2262fa8641eb1e7157915ebb9c70a26b482972db1a7054aa50c4f808f426c17640fe633cb478f5096729443704a600d28000000000044182739a9238b34b400086a963889a6298571a02e8dba05ca72921aaf7a3dd4030000ab480000000000000000031909500000a2e00029c2000000000000008b1299410f272d9f280000000000a4d93a6bca624049694253c8a9c82212fe4aca9fc400003dbb5d000095c21a80001bbc8a6c9bb2aea9c76352bcb98f1307c1487a07a5ac520000000ba500000000000272924e06d8b167cd00007b71a14536917897d8df089c9c36c13a3db6a8a696750817404aa88a4f582ff2da80008a5946034c2508ac209e974e11e87df0000970a8563bbaac64d74000000219b1db8e659a380002a7c3940000d92000243f17700001b1142691580004ab9c120000ec1290303068b231e40b8b0e5c1a3e488eb0060fdefdaa8826666d28000033ebbcaf7105a012a84854953ae879d025a67d3483ba800022a8f230001a326b880000000784a3a5a6d40c000000018367a7106a6099ee69a98bd6a64d2bc0001a4c000000041f887600000000ea800000021f50000cd60002b2e0001fc000028e7789000041b02efa98291203800001f1a2300001cf24ff89e8bd52c02352d9ce000293a1a724be000245000019ee07fad2b0000bff4999d140000948739aa4892ba59aa1e03c231480000138000a28103dbd95a5b0000000b6c00006ae800000000002b281c260710d024b000031e8000000102f0001239000296e000127d0002dac00029ec91500009bb80009821b8c1720cb633200006ab8000ad9000033f93f418f25490001a6eb8380e428c9bd24a5028d6e520e0830858033dcfb85f99950b9ee9f037b40002a5a0446f100004f7d028a61800000008722bb23c125715f10029f38c3426711c806399b88000b4d6dfc998a448336100692dad450001eb25540169000000097103df847800036114b63b0840cb7e09407830000674ad8821bc0001af14fa46f93e8ac099c809be576b3d04ce22a2660146ab6800011cf00018222c2d66c0591ea256e81e00000f9c286a93c16b000073f19f687ac7f4a4124744580000000246400003d86d128823a9865ea604ba09c3
  | 36 => 0xda9d33b1072e89f07d829f96f421883f48e199880000658921d5de16f9a9a0000000957b1025a283de95e87420002a460001ab8890c0000002b887ae80006b60000000002d1d2c7b800023849fd9270000000000000008ad2e180000f7c1a3000005004b8ab3800025780000000d6e4ba00000001ece44e8000000145a34e8338399af8839c00006d6095675724d89761e3e70c80000001c181b669b00409a126ab12360000000ae45790000000053400005650000000237b87f40006430ec0926847e901cf7075bcb22abeaedc13f17c85c3dc501e5abe27ad060850ae6a888a4f254f24c50320a30c02692457f86ad09cc23c6000079ca151b770de862cb9f516213e400042591a8000182a81183748cce2b139b4320147000000000000000000c39aada80d6a2897a0000494014c01318f40000000000000000014242d40000000172000030de09b2400316005dc3109269408f26650a29d89e40007988c4a000176e93880000ef40001e382d40002d643e000000000000947800000016fe0001ee40001dc70000942000000000000008b00000c05a77eb9581bf40d59d8ae7c000000000075683110001ec87e3000035580000000af63ae800e00000008df800006c17fc0002dd83cfaee8000243d8aae3540002d004699fda00028ca15a1446476acfe6d180009041b7aa5485a80b980000022084950245a07623511ad933eba0914409f00000c58000bbb00ba657414572fd78e65d811c000099200021d00000000000298a9881ecc27719166e1ae6c815a77150824fe2886c1a0002d73b110d7a16a948aa0c05587531a380656868907258c0e282889381c70b290000524af62c038c8817ec004c33198c89542740001314000262800000005c8e41d8bba5459cf234fbaa9ae66f1989a945002e9d2841fb6305220a587cabdf26b67cb102095601a6959a5c8141800046882b6089a3ca0f75b505932ed04481dd603526ccb4991ac2df30c8a551a643ef8e098e8c432b0c0c389cb00000001cc48fe9c2a2d380009f3a47c000000000022b263e00009011aaa00004d30000000917289a7ae00000000000000119e9c0aa023d122ec2c7a9d6b8a94dc1ca00a2aa996c05bbad70398934211d800081426a20fb2f6e5e72d430c35aa68e86294547293e78a975c1088aa170300000001f80c2b174f0001b424cc8000265090c2c219dc1d89eaa0b025420000000b58400020d2103af0e0fb8bd0000b1b04fa366084c00000009dd84f29d026ec0000d5000030660000fff0abccc2000190e44900009b5800000007db0418000747138ca2c4000157c86800000000000aa20000000b68869a7e480000002d2e00000008259276839400000028ec0000000000000000023f61cca6043578e54a2100000c9614219c010c0002ff41cda5cab1210382c480e
  | 37 => 0xa817fad30b19252a41859ec34787d3a9f2f3603605d850a40000001c9a2c300000002bd90000a1e0002fb683a924bb2e28506fc1d0259912aa1d38fa63cc1034000256a0001b3a7220d7ea48000000009d2bcb8e280000000b44af9a3115512246d2209ccabb64d421611851d94bea104a5759bb28f710093c2172d7248000be0a0b803faef2390026330bd0360d58df8533073e8e28bba38513d80002fc41e230202ea309627692f420d8000b4b40008da83b28b8c00091180000000e4cb77a6de229d2b829d19620001e25a2e5d280a0ad5b787ad6c00018660000000b4de9ce99525648e4132c05a000085100008c200000002723af2800000012d33268dea144155400000008880000990000048d2d0800015c000005fd000143b4c60f545c4803853380001c20000c1723884e20000000000000022e100020000000000aaf8dd98da28ba55ea3ba7c7927e1d800007669a3000028e297e000093e9fd2298800028811fe388708407ea01fb33ad3308d03e83ee8000a9d07c83416dd600c1b16b6280002196d3ba8180000000cda95189d4ba2124c9128f409e92b263cdc00094b89b13e09a52000302e0002318bce9b0cb9e9cd3833c7bc0000d40b30a5e233c61e6122eb9b977c77ea9cee52434a98017c2f950000b8f691937c3f7e6eabe9800055600009e4834240ea02d27440bf94f148075197aac3aab143530c680a1900a095696400008a987ddc3cc1522a78e6268c00000000002416c1b125ca201db499207350000000000000002c80000001f2600000008c5000000000003fc1eb6449a664000000000001968780b5c2275b8d3640000c0b2a7eb22049017e156444b9f480528c060990c8e4e5a38e80ad39c00000000000000716ae8a00000000002477342844e9dc80008f000000001bd078692826358b7637287e8b4587fa6a0203ca11e9ac3d980005c9c0aa0000622509ee5c8c0800000000006a909003b7b0f453598282f490de24486c641cad3e8758000000214529c00002080000b952f4100015ce0001a5000000002164970848096600007180000000bc8901661f8bde3d58f6900014f2a69000049b071d00000000001f9a0001aa0000000028f8854be580002f28000362800000000000002f0e000000000000003c753cc13d400055480640002c763879d9e2ecaaaa715118888c81d4af080000000000000000000002f08d7d6b69bda9aa00015383ca80000000000a1166ac423800000000003e22974910143338180001dc4802873d3f27fb0cf53d30cb8000146a95727d800000005bc400015e0000c1e000066caf276e92c24aefdf0c822833ba6143e448269224500000a7b9fca1d444aa0aec000c3cae72a4a800074ca3b2344000017a1ade8d745db101225c0001c8b00000005dd9e3c000308c7874af20002cf27c
  | 38 => 0x2a84568df1d0cace1f46309830050e2b18268000069c8000081a84600000007fe80000000000000038cb492722b40a3a048b2b980aad99a8d188e62a1a23c8dea77f84b10e80002d792ca92be9bd16567442e800ff94a86310eb25af0c0c3ab81989dbe8860002f80b9a800000021e91fc26be5de10582a9800036527cc5042dda7f88f1566900009c940009dd459a0000000966284ec10c0000001616a7980008ac1d3c897400000020f36dcac200002c6a028d5720fee378457ac2a6d52b0024e8000000173e0000000153a13fb1502fe000000053a0474000000084a80001b207588bda33a4432c1e997a17abee881e3fb0000000264c000000000014c682800009b90000000211220b151665b99c46c1168c93b452a8310000659ec9292523240000441911211c89dae2853922aec0ae10b000000000004e67608380ac3000057c00002f1e0b322080000002216000000061380006a214300000db65a5800000006ccb34118a50a98d84f0c00082c2b9e37c8ece454c00000024709a51a65aaa0df92ad2107b78848a3eaa0f90159ffc2c99e92182456422ea3d9add08589f88000abb1c8c0000c4292e000068211c4895039017790970001cc838bc3be132a0a25292f20b90aa83c112bf0a3c53745a6a40e5e3d77e272c000696112caf753640940d645149fe844dac4ebe102984e48ca013d21748fc09ea000026d000301e3f646019de70221d523beb91b0ee1a9c0000000d74c22a77cb62606200023735fb013419899de4648e8c000191c3c64000a418c10b9df0fe507516678dc6ba37426925cb1a6870e859e91b9e9710847b0bcc89b600000000000e260001f630002fd822f400000000000000000000000035380006ba00000000000aec86948948f956f59d5737d89fba611c84479b0beb8da28e54d8b680a49d7ca9aac0841bd918b671fd48661640562139ba5c22ca2fa2fc6a56028f0002ac407a98e68c8112d0ac0352532000000028620000000000242800028320002a0a02324de1776c38bac088038c8ba4000000000000002b51c26a0aa4c6bee0e6499b0f4552104860000000000000067e000043f30105b880000000808b9bd010000000027140000002e4e07780000000000bcf602499da286000000027080da06f1afa15da6c2a162c3405100007dd0058000204a0002dcc40fad9839215660001c5643e18ce3680416000268200000004e896100002472a008000c3912c4a14800025aa5017b100000000000aefb0465d36ac30001e7482bd0c57ac2bae3c91e680002bc400000005618000000000000003f238741b85d79844b989148c1a2334ba682464f025963e829787cf8cce9c9a22c00000000000aada04974e58e90491e4800005629e367880000ea251c00000005e9304a452c000bd58b7eb562f9e000046653d81
  | 39 => 0x9e800035611c82dba2d200000c4874974c0001ef07db000029b13cd7af2568ae4b10c76200000001a2e5ab8ab63fb9f9c8f0800000008f0000044a3fe872a000232f00014f00001de812791850000000aeaa64669e498c8231ae10002a6ea87800000001ba5bc30f02475f7a2af953e88d82903f3043b71287c0b2400b3000162e0af50ee1519f849d6abec00000000000000bf30216b0a1cf4000070a8d72fe6174ae0a17b03e600010acb5f04a20001f8885615e98f582f8000156994b1f4006b8000afe113c205814baf62cd47c2000010485a08cb40006808000766000000000000002dfaae34b1b16c2a3e1de98ac97ad11a000251a50b947045daf04b81825699d0d04c2bafce46d2a2453e0e1b8ed035c0ee1c1679a9668156815a910a6f8697504baebebf46171b2e84081f68a815da3dac57a229a1c6bec006220ceb789e09c941ba10943a50d020b885426c2057e131097d1a053ba9fa20526e29f5c48e9718a9489a333c06bf9d585ed5ec21864ac90ec932915851a112335c1caa0000e08c2423566cb15343dd106700030989ec8000c0fa3f21e9c2b40001745000148b0000000beb0fc821222a989444066ca800094c00000000000a1a8bea70c0000000000000031065e7a06b4cd2f582018cea95486a93621210095c00000008ee0001f6200000000000000b9121978540b06837c00000000000001057897c000000299a0dc5ad400000c25f317804b71ae3088077821f95b27f2ce35a254000881000000024608fd11f210b80008f2214dad22af20000bbe3cc80008bf8000718126029a80003392d0e80a9e7e8a2ee0c0f12fd06a716de00000005230e68102800055d00001300f7800011386bdd16c453800033880000000a28a77a25816bee167c6930077284463a3a1284c280000000000bd38b4c791998a000000018c8000b330afa0f59ce400011648d896a4aa660b4765953c00000000000136387d0220001dc6000000000000009d562fc28d9e024bb428000005f29af08370001ec26568e4a56c17ac5b1174272d0c4619a0000606ad6ead00000063800072b8e1620f0f36969860b0001760124627f0002a00b2395e709c52f09286168429d6c88581f6675f68feaf5a860b0b434636aa89d290ac2279c920c413d22f4821dfa27da7d0226a6326cf2d665309b5eaedcc5e8bcc648a5c90e482ca7886842a10ae9ab1c2420e5e25a286e80604dc59181884789e522b02d551dc24da34ac231203ccaa937cc4d9eb6f40a3798721a8ada81ab425b87c282c1e31a846cd1b6e700d04800013ac00016905640f143e1a1d8178400000021400ec2d0600024a4662f0928908000000247611b8f42be7215c481867a9fc9a7e86322225ba1d018a109f873d47d2617852f5972c9c83d0f0200001c4bcd1d2e7009dec00022f1b
  | 40 => 0xb2f1fee0001e28a9b1443130add3af1a10a33cc1e22038d5aaba8000542912200025a26ba97498418ac15a4a07830504d417bd8e259eac427f786725faa81c86d15ae44391ba000000000000000b4aeb4abd0bbb25187e0996811917011f141b4aa42fd4a8a87eaef450456f67a525c00000000000000000000000001f82a7a0a4c000000000016181a2a1e23e8825d45b92389b3a7bc000000000000002a3103931c18073cb0d5c000000059800009e680001810000351de9e37d0b4a5060000bbc01da7d904b16da80000001acc000000010759610001c42000000000000000000000758c00082f2e0800021cb0002f0a3bd1fe3b619f2462819a6b9b8a464fa4fd6000000042dc000435000000000002e7ae920002524a7180003dea3e82118f730000000000000003d27fe00009ce00023d800024917fd8a8b00019b80001448000174813cc00017500008dd557d6dfd7662ff91543e8c000b930c4400002c828e8ab58a8c0009e1a7fc0001d6aae51b9e00014bcb460e670000bfa695673897b40000000420217b0da071933800017f65e8aa8f9f9c7e164b214a6b7102ba662c9886f0c1c8faa759389c4e89ce9722158a9cd7f18799b230b8432903e27af90130619a763ce28d2b8f0440634242e29901544b39c7a99550f692888142ca0acdb161358a49d56384e1c4853b056a453c87d0af0c16935a976a571b8b0321bdc27cee5e3860bb81658d154da652281223d419b8000ad6a06600028980608be96ebd15100028e30ff000012e8000ab9023c05200000000b467112bfa34b00004175a3c7bcabff09859a261b183cc3a1e00b48800038028eda7688dc000056cc0c400027203444050362000000000000009dc0b80000000002a5bab18680003839f6e51b4000b649978ab580004134000bcb6170b27800000005bc00000004be959e000000000004d04962cf01ad00004038bc46b12e30939107683e16ac43a9d78bd28000adacba2b39927c0001d0e0a723b85e1adce7f0d2fca3d652830e8000a52a96c00012f6b1f000000021000001b4890240004f780002eb0ab2117800000012b60d4400017405b483b45091c78bda000000000010626ea68b783c2d1c57367620001e9a00023de056cc2021b94120002dca385d1160246d448082eb866012da00000000002961a519da3811e67c6968000b87a02292f265262000005dec0007f92ae80ba938900000006d8164e000164abde8000a760b8c752d3908e5000007f1ff815aede090094fc2d9e9f8247907778e2d4daf6a5e017d2a708b99510961a5f42661bc207c14a2bb000c600001cd23f0cc659c1834375a42600010630d8087c42a28ee3402f3c6d687c442d8fddbd1272920bc00099ecd9a7df886046680002fb4000506cf395b480000002e780d389e74bcec1c29580009f68
  | 41 => 0x872c0000bc66148000000087080c40006ff0b2d000248e00005383e9400000014fe000000084911c000000009eac00000000005c9221300022ba59d0bb44ae9bb65b91802a9a5449bb30000906809800001070000cca8e930b6000000061e12969da83080000f349f040001450000c45000000000000002fea0002d901fb9c7e572a8a11e34c018cc0e7400027100002dc22f70000066d108000000000000005278000a680000460097c7ba1e046131a4578ea7661b7254436786da55ba364a3cc000416e2148d8238c5669cd000999989c20c48853af681a591839db2ad825f8a7c04c8db00000000834000084e983289e0000a8300000001d5831c8b700002be10001cc0bbe2ece581a54c0001a4a0c7800074e9fce389000087d30940f182fd41403c095b148640640ae1e88beba8d22505bc9e16000000000017281f59dc278c8c7cb20a5da1bd21960000000ab500000001d41ad7160271a0e501572c960000de40000000b038c1e4398be200000bc776800025ea764000049a99fb0a800000000002e8e4048000bd4c00000023aa0001d8a00000002b0c000344eb240001a5c00013e211c00006bb00000000000000000000006a0000010a98e00005e84000000284a37e9c5c8548000893800054b067e6b92e4074d266e723e2019c5dea08a2af310000cf83c02259b751d502b10146b6e95d290f8e3e00017b25801cb800009d66ea80000002f8c000219400005cc91e82ec5388b7989dd77263298086f81d0514ac00006700009322fbe66c1f7800017462a51029bc1aacbb1ca20db2b09f9016507973cc70c9f585863939dd224f21a482da87c8a706fe9a01b3811603019a10e194b295e23c12288537a13d00000001ac800000028c7b0fafde66f240c5f40000aad172941a49ae143690e9751b363ff265c0002a8e883a78413def160000b64116d33c5c78000198177c000000000000007639ea80000d44868800069380000000000b6c800000014b2000275c29216aaa0d03220002f1e000288eb7980000000ae25a0800083500000f1ed4246409be0228000000056eab1e4140cb86ac4a68c41000000070e000000000000caa458b9a122581762cd00000002d808be000000048f11b0015f03a97eacd687214ae00000000002374215c00c0000000805955cbb797114dfc5ce89810ae93a000000006ce1bc1f0a17344d85b18000a788000000071b0180000a25c51e00013c6b05af8a3ba05299d784ef6f1dee0024800000000000000e38000000039f809c5920574000082800000000000a5800000d279326dc5035d5420a8000746000099390549e79be61331c2472f00003690fb73b314d8914ae34163297e0001cd41d18e4400022cb553233841380fa1fb43ee0c50f84a4200002eb5c401f90484000080c41c280a86da1e8aa04000
  | 42 => 0x80147e000234e884821a4270000ac4800000006ab00027c61b78000023ae3a000271d0000cec000136c3d78f3a07f5a7479ec000325306149d00002d10000af3094c0002db60000b540e813fa35b00000000000a75d6cac3000000000e3400011c284100000a6c00000007440001acd0000910b1baffe000030f2f9249f5c350179c48d0e2ce000013689c64ef000000000003f9549a1e680009ad00004ba40006550000a960cc02169ec077aaa4c41e22394101f5e934a22e480aa665112be6a1b40001ea80006a626440001c6a75c86f830bac9495f0917184a65789ac85500006d40090bcc19700009d100007e50000000000000014964f540f89cb82b23fc927840b0000bd68370785688c0eac048c008000757c000000188850d22561940000bb5000017e800041a1f60b18288809f9ae00c8c368149cb24000157027bc2be04880001bfc0001a984f609200000000000000000000030e01d0c9e49ec2a770001cc20001dee84886023f7834c9bf8000000000066a192e0000000baa0e25bfc9543501d66a71c8f6f410674c92e80003cb94765c52a8a136c984254ac1016e229281defa4522677a1f380001b5db3200000004d29963736ac06aaf00002289b8400008f289bc53a000143994980223fd9a0e8cb25c62f8c00027b0610bfb8ad62698fe82510000738902d1950b000001b3015f005a5089b7e7d5152700010aa2e0c000000006a6f3939843d0000b4a8e966a064f65730588be811e0255075e00d8de0507847c0002bab935120e2b3adf023e8000b31a74e33798420002594b8800004d500000c4800039800000000000329800000008c20e540000001ca0aff0000000000011b000000028d80000ee27338a6e02998b20504000969300c00026e07354fc969002acb5fa98840f09e22b4997a4ec052803767d27ef8b14000000000025ba0002b567c88000000062068fa0424da07220ba545601ad100a5a80009090ae70001af26c461cd60faa12a22c000ba7000000005ee000100b000180e411111239e2d5600014d262310150000000a4e25340000d2059d8426000283600000c07b6800000027a85a7015e9cc5cb23e0d46e58d2a86748143a00024c00002736c4100006cfa6c009700000a79d1a13f8d3e00017d64c180001df000000000000000000000222500002eb000282e0aa8000a59af1819929601d4307aa4c8000a750920488954e0000000414ad8e1220000b5ec000000000000016f3226ec500572f0078884df213800000010310000d661900be716380000001e3400000003f180000002dc6129c090a7f1d4e04115fa9f1c8868040c74b51c1e615581c13dd90ed25b90c33eba6e6961041b7078000000189e07496428b8800095e0b029f7800097f940400000005be4a91c3f137616c8ef65c750218dd9f56980
  | 43 => 0x480000001b9c88ec0000002bdb1e78f125a8a7ecbd80752b0f1f3a0000000073e99d0000e2a000000032b0dd2285b0a6aa52bee489a1563630418410c00000026e8000262411cc400b0b2e9ea97a2d0199a78c00019900000bae3e3a1b9b4c9b5c7e9015d30296ba28184a13d0e85125c9aca00016fb0000d9c0000d1a00027e5a8c155b3fe02a490e0ed200018e45cb8000365800040cc5a2a16977a89b15fc3d4a8fc1d68388b8e0000270c0000d019240000000377ef6689242400000e42000215a3b50b2e48a022e308a55629a2db859122a69441a920a51e2e90c8000692073400000002f9605821b2e12b9800000c0acb011724ce00000000d61d4d4dc831800000002cfa1ba00013b67da00001be64066c00692000000000023a503a8e8294398a494d9f760001540bef01cc9858d601729d080000000a7316e60000000000263aba192a89e427210790170c062e983b4de2c2451414aef66f20f306fa1581854053a075454987c0002e5a8ab501a55a8642c179c823cfef128801f1269ea5ab88543f80bf006dbe8a3a61ea1ba23d241d6b21897471ba257c142e4ab9f92f95ff9a83a462ebe00030120b9d01e9c50e6c5caa6da00e851635228f07f08000b6667b19ee0000000063e0dbc0000d84fb54e198386f290189bf00006ff80000001a1a66b95f2000000084513ee1dd800088fc0007631b8809280ec215a20a00008ec87fab284a30000bc08c0400000000000b926a6c0000000000000000000000000001ba0c400000aa01db80000e5c0000000000115a000301a61a055083da43c59fa2d61c12110138800040dcd4188864367d64ab80001a8d54804b416eb0fa1f784eeae4ebc1539a6225742396c3495aa0df981886be0040000d78000209c000000000000000002f763e91faa422d95e2a4036c0000430ad7a0e8a24ae6439e928a0002f2a000007000012000002e2e7e0eee0000000000000000000000398e9162a4800004ec2e0c33a1b2902924d5582a849ac0aab449400017680008c7c0007f5e31a7d2844900026588d1d5be8e4800000000007e6044c0001f203dc547900012ac28280002b60000000000000019c29e70000000254e81d000060480002145098000153a00000000001f86000178286c00009179ab6000822a658261a0052a8826bc2a682b800000000000e580009faaed800000000000ef0000000000000008c740002b3e16a000183a3fc69f20001d6e9f089eb20ec8b603a298c863936296943ad8b18c9c000070261623b60000000aa688af55f812c8864000738ccf23db1ca2000133f35240000002b162cc125e2f7da1e28400001baa75800000000a32b580d3c000000000000000007d684d7b1726f0af240d07012ddc0000000000000000009f44b20b5e311c00003c984a1a970ec01f0000000000
  | 44 => 0x2161900000001da294c8924b3b1e58000000068905945f7006811a80006140ed7bf580004779ab412fde7388613b25e11b835869b8201b02ee1532209906000000027e000029bc504e1b8ab700006dc2d4a000156748481ac9679f2e8eb0a980c9ad0473e08da000114a3b807945439d403f38a2f000226a0001f9ebe4a8f215100009ae0c7e76a13220559b648dc1f524e80fc700003e07a1980630f88922528b1a6dd87a49f90184b085f7f3cf0000000000096c90e961e800002527480001d7683e80005661fa64d1a4a8c1c00002110e042938000b0c800000020d67dc005c30482ad752000004deefa877c40200016940000000000087a964a1d400006fd0198000064a2683e6115dbc4000000000005fe56ce51bd53989186769e99b1c2d6800000025e12101ff052501919e3ac2e88d1cb00001c864212ef68bc0fd23a186e6abc0310b19961e835450c0001e7ca6e309e8729fb06608fca00000005cc000065b6d7a690adae407000000018480002a7a809489e4be21840e18000318201ea6f84146510ab71fd9d7a5498000000138a00006ca000000064c00000000000142a0723b6934c20e000000000001ae0000b5d42b37f9a3bc2ab1ce065c287400008223eb1504781e8559c91db68499ada0002d3aae74850b6f1b0e166042a97bdafe889103f5492f3f1e0111e6bf17f79a71fa254ba2e577e2d80007107426a9efa1322bd2391c00064e9dce42f673434700008c3a3e6a2f800000018aa44a08de2b2e26665a81e30000143625800035509ddc3e00000002bc0000000032e8fc40001c0ebca0439be51e5c0000000621937e49fc0001a600003b615560001e8500007741c8c0000001c769e8ab3a0001086a8dab7005f00004b00000b5ac00000027466eba1dcb2f930428f00002948392316800000816fcba356b0c42800000000005a81f69000000000023a834d800000000000c90f0c42797b80000000000013500020120000000615800019a9f061a100000000dce83bab7c000000073a80000002a320000278759a2178200000241a1720000c561bda4b0c3625de1ad5f8a58f8000831a7d496e1a0a0001e400000000ac380008038000000284fa7102ce27ea17b0000000000000006b6ff637100007a0c0006730000a9c8354b7221180002340000108a0002188a4d00008c595cb00002c43848ae48b7aa985941d8600000002870000ad8efae000189236f800000000001c019382825bf275f800000019660000f0d134800000013a7000097800000000ded5b40000f0a1239bec0002dc400000000000000000174024caa7b36e2da00001c07a888f9e00029e09ca974433800000001e1212516ea7b400000e62f6400000002deabf23090000ab2a82439da2dc0000000170935eab140001528000a61c000000229777100009b
  | 45 => 0x12406fa206a58108e07958000837a8c45e4811f0001fc10002ce875787da59c80008fe220693cc507aeb195c00000001d28d435519c66b3d80003130dff903682637625889e1d6eca6e870e7edce460000a872b7000010a24f44bf6eee00015c80002d410002db447be80c161231c24d000000000000000a089b400000000000afa800000021e1000000000005a4201272899a80003be1cf08018000000253a58b0016000000000015a40480c366011e660000000000013c296908d000000000022440002a62000132023d8000000000000000000001a06ba240006b590c05161daa4618000826143e99e17e26528d621a1810e6b2000000000000000000a56a8bd00000000001127c10957c1608000341800031888b80000000aea13dd000000000be2ac83f295e297af5e284800076e881c00013100000eec56f13e60a4c35e0000d8662d930c00013d06480d4542b43b449225cc4f94c4324f833d29c88e2c328d26426acde000023e7870fef00001ca6fba23e00000002f859e649bafdc7caad3d63730f68932dd12800a0ebc966b200024cc000000000028b600000000002b72000302a96b800000004af9105d628aaa5ec0000000aac918786eed77666ded84ed00008291c0a000297b0002b767330000c1580000000000000058a000000000018b0363c000b658000b608000164000026280000849d246c6108c69f2c4681e94546c4843884230aa42d12d02702b7e0ee80008b601113248bb62a9d47898b97360b929481598000bf22a2a1d599aa67a946200019a0000163087967ac1ed21ac3c3dc294d980006f68000bfe95610000000000081808cac010001eea000000032a1b9848ca98202000001a408f5acfa2cc0000f970000eb6046a84200030b400005925602b6a8ada1c73731cac5025e8835bcfe7596000000024860e84000016e2da15483d20000000836a4ee4518bc0000196f7f590260000000000033a734586079294175e2116868e94900000e9c0e3a84d77300003548112339531e3000ec65c2d0422fe000000004f1456cd1151b1a180001a280002322ba9ae700002f08568800040c80007f61b90c1d9fb492d261ea6b80009d09cec2c402b577f8b96951d1040de10590002a9c4b50ff400023ab8c99b6c9b292d1000140e0001ff22c1000019100002c2a10c6028000000216e66da03297b8a549f0c18d20c86789640e98660dad03f700000000d18aada44d0862d87464c01e4381d2c0001b100aa52652731af600025e440230c249aaca85d29bba38c2ba28f8997e944888c00000000001fc800000000e08000aa317d2ab229ea9c2800073c47ea2390da806409805b58000292a0fea3815a05950fda77920860c7000081b29e49be93c2ad9816f86fd09d7bb862e887888a0001f6b72d80004bc9e060000abba8a5b
  | 46 => 0x19800020e20002c0c902d9fe00015d887000001d70bd800008c446e00000aa000000010a2987180cc270b8894190bf000003c4e0807eadb8b200a461c4191809e02d80000002804000144a345929c152589c0002e242cda49886f96da47386388d79b8012ca2d421d049c47a8116442d2eac0f05cf86acc1b32b80008151a049c807981c65c1400026750000000a318ce933f00000000000a01ea1a00027ba04e4000422240557117d4af165d035cacdc000262a000000000018bc894e538000264a3d200005c6c000000061c1ecac1286a5798a3914be38b4000ad10000000214858a00003c3ad840000000c2c80000002f0c0000000a0f800067c01c80000000b58800000025ce00011a00002e8426780009d80aea000000080eae22348973862b800000017ce31380006e1c00000004821b0484facc158e00009e6000000084b862800000000a2898600011fa2e69d44000000000028bc050a1ec000001a876914c45aa002808dcfea9020654db8000c442b3c2892f2f417e09a6450842a741ab2b0eb00a711824c08280006bd2088a0500005f0155e45725a002598fe1abd20a4a008abb70023848c21470001898276000078515060002aa00000e496f508a4a4280007d0aa3a7a425f0523a20c5d8d1ee0000eb4a1700000002430144ef980bc433e23594d4000000038f1b7806fae509d51a0c06af08200012fe29e81625aa1c272a0268a3c42d388322bb365dc43405a8dac762cbfb3b70772519abe0604d10f80b032c499184000001f20002d6d2cb2996bd201aa00011b6ae9edec0bda07c4a792a43e308b09582eb179658ecb8b0db4a89a97a3172eb2b2ba0e41eda77459b845a396ab4aa298000725800093c800058f1761b66af3e67c8b82b1880760b0800070c55228ba193c4362ed62b194354090fbd0002a147a100008b205c642e204e8beae3e000214c60b11d00eb1bacc268bf03b586168591b74b2820ce000268600000005d889b800003ff010819d8a05afd00007e648117ee2bba132085ca95058000053a88fe8dc80007a8476c7bd220b02f9da00000b3400025d6bdf800000000000000000691c00000013f74878000000000067e915092216b29c1a78000025dc00021bd000000078cd54a2db4000a1eacda77440000832210bae907f0000000ad385e41acc0006f022480001fcc00008a550290fa19b0000b4e6ade8e250d97a4cdee0bb4000000279600013f800010bc8db2f724c380008181ffb42c9fd0b572fc25bbecc88a78c663880511a89cfc036091848e8a130ba598620a81c281b627949fd1df4538222637220e15c01e313d1e10e497eff8887035a63c00000000b90000287055a000007e2e48599824400000008601a561314000a1116523de70080000044000159c7dceb0a0002cb25be10731f30fd4b299a340
  | 47 => 0x9521c26b082a2a038a30a6d00000e9af38570800026e80001462b46b7a239cbb091c527c271e3f82a8233aeaae2a24000000000000029d200013f938b82ba0001a2a8028000067800000000000001fae962a6f395d00007ecb060a8580008698000540800008670805d4283a0bd26420000a2c77700002d59a16b36c0003a8800060900004862500a63800000030407549e0965c58f60001a3600024a08648ce700000007435cba01c80002d00000000000069859924638f2002b00004b99efe6a5ef523340be069aaea4183199350fd9560001e0e0000b624f2800081ec00005b914d00000005fa041746c80001968000000000000000003200f5c6f66fd23f9224a0000d57b062300a478000816de0a653273e58d99da4b3000087a94050002cc08a943bc29e28994c080000001b5609db0a073587f8bc99db00000ee43211c2c32d000000000000c2800000000287a1e42a45d306a000039c7ff8fd3000148d048400000000007a299320001ef800023d0aeeb0d427d660a834ac80952800000016d01fb000002c026600000002b819815bd40005a101a400000008eb970213c10c84fbd3da8790000470c17b000000080f827253b844b13780007fa944eb440e10c44acd8042033c033120799cece40ff4d8e95ba2c2b99b04c3701f6d140104676c8cef73143d4bceca8d4caa77b7f252247d3289e0b2e75b557c52091febc8436ccc42488ee52cca0ec21ee06eb16a09e427df879df4f966e5e9a76d3ad0a08890be000000000000004ce90a062e0e3a2320800000304881001336d6d8fcad49c01654aa78b52056500004ae0000b72abba3c40002ca28208e8461b80004d6a65000015f40000853b870000288800088f48678c1a1f2908909064217c44ff4b1cb5a4fb0bb1655a50710718af82cc96d91653ed959240000000000f944dac2523f404984bb2a9696b00000ccb07c532aa0e0001ca465900f0913243a8131ac05c68d3c9801290b7428940001a6b00018e085f12b460508b27a393d47df40004fd933600000000000000000000003890ebb7910c90002f5cb0d80001b811aa00000008de43f600014b8000002a000178a5ed0930000000077416dca502daa000000026a00000001e6e3df80ce16b932e921007a83bdc8a83017d8000082e2ef269027ca4080334000b5409ed00000001cdd25294108b46fe1a9ec0ccfb184142288abc16cc3702ae00000005e980007e800006331ed6212c000b51800070f8125ba055081f091d6b5e00006af144098d8e2cb698000000000014da20f00000ee46708cead517f40001e177178c6cb2d046288e2816607aab800006eec16a8060b05884465a14667a19400478e0a000207e8c10000b74922e0001fdc4e2e8b49429b52000004000000000000b3a000037cb5306372068f5a00009e087e1
  | 48 => 0x800000002e104c1626b21000086cd7b60002b2068800ff6ec199c77c012458200003e145d651901a927f9b932aa1ca817440003075f0409a033f9c607684c91f61665158c50c954251e8dfc735ded2485a7ee25699100000c084e64000846a8c8000094ea020830671a1b100000000000d322f0800042e800000000000000f4f7f3edea7bda358a28de109480ea8158400000000004a600002a4ccfa824a8fa436a2ea5dd1926af917ff7c6217ec23828e77146e256b0ade06d211630080a03efe27a91fa28c3b9d58a0628da243184601b02f4530d048c000038b4a982042689747bc727164de0e360ae18c24e3b0e2a452ce0101ee32000206116d8da633d8730ab7c0000002ea205f98a600004c63a286a3597821b981a99242462e44202270a9111f03af25e3c11cbce1ab88528c1ebb174a94a615c8000000247973618c800023ee5ae000069e00000304d465da918262d04f85f7975627b9a661af87240000000000091c880aa3800000000b468280001b2800015a620c4000891c90228d246cb38a523622adf24f4800000021990002e7c6639b260000000a330000432ce90601476a82b01b2b58d7be7f35b249272f428fb21ce0dda0281aa03f000000006b190b04fec00022f2dee93a80000b2800024a04a000001769898b9400012eb0002926ae330348d10000ad09c9e637800061c0a50bf28962017a84c000132800008caa9ae1ae0001060a44c0003ecc0004d38bec3dec000648800000025be1411bcc3bf186a2be00000001e440002580908069e19fcff710fa0261c52fb280700005d6af6c00000006e98ae8552c0000f41cfd00000008a000001021370886ad347605c1aa04000017d8000383e4dc0001ec644724c455dacd2c0c973200015d43ff80006f200006af8baa0002cf8742873c65b03ca107a36600009384d702086288000000126947715b68f4a2f8b4b0b66b32a0d8485000000017080000bb30000e9e0002233889caa9048cc1abe18f062170c2c7dcaa9e1bb11ec1fc800087f1c808f6800052a9f287eb290289f975828a973d3bf4c9600006fb000162400000000001876000216c000061800027aa4428ab0701800085e253e0000936866879022599d64460a1f04a14c4260803eb09a1ad11e88ae46b81ec0c6829955e09640001f1c9eda13bae125b400015826239c522a216327070afc00018fa05d59460001cdf6f60af47781a540f71bfa20d4d424f10a3831008d000000005b7c9b942bc00063a80000001e7a000239e92081e800029cb0003074000000030a16fa0002d76b5000000001fd56de53ec0000000a0622b58f31f3220240006b3ad53340ded400027150001fb80000c9700000000000000b6dc53c000141a6da2143c190e5823e01cea72464e05c80002a80e3d13549d06d9a05ac070606c0b58ba
  | 49 => 0x6149224f503010000029c003d8a045fc290500004b34d480007f9e2f7a1b269a000225a37b071f09607ef4015d90a82098e2f412e2000224ba66547b6a0af7847e2195093921c679000081a1408788c803552091887240009f000002778000a1f825a4328ec81ce80004e028401ff99d400000004b19d1623a0000b0110d60f381ee84fa18a4a38f1c611a0383958fb43e6ea64b86800015f4dbf000157f6df12d88a25244ab826d82dd0000524c00050a02cf7d61b8fab080008a90fb243c8f8a31a907a0000cf40001e4e7418000631ad5400001d06c82176124a19ca968000000000034b8401000000000000006efaaa296c0b7757aa2eb000197c09669fe000000031d800000022a2c1c8000bb100a83ca64fc49e80000c2d023258053205ea07071b124a99c23320000ac824cd26b33ba5d2a959fbaae09a601a3979439c9dc02271ee2a3384a62d0ec14a642876000000065600000000000000000000024dd054a4f80498114000170c82faf24c31dcd251d00b84e1235237a2412194aa9176921fb8cb8feab1d000093b000011a19e0a9e6ba4000091a776107b3bfecbab8114c0000000000017010c9c3a400009190003024a2884b05c2956c149a9f64a1000000006dd0000c0eb128eca064cc192e1917214394884918a44a8100000000000b1f89ff52e98c0084193454a06fc929800000000003d6000000001f4b80018f25b145e00000002fc800065c8d345f2829a8a4193e5dc13262e604647c0080a20928d420f8de221286f222528dcbbf8d6a2998f5bb2d90e22f20150204a0dc753c437380a5ea0000e1a6e5400019d01dd6c1a6c437ae46a2411fe00001a1c0000000c0bc3fa0e78000000216212f241e4e6800000000003f62b8657a00000000c9932f000054c0000000000081b68720000000000249076145541258000037db2200020a60be9e645eea39a00000007abab990001df6878f0a43d19f308e0800029714500000ea40b8e99e98384e03c5999e5d2d9bab5c80002a3eeb633307dc0002d6a00000003a2251887d87a9b3aaee47c520e90e8dbb46a50ed94da99650002f4c5008f18857ae7f417173f0001532abd9d803e413c14ff0bb90001e4300000000db8eb826a4000087abce000011800000000001cfa34e0000000000077882cd584ad830000000337000000017eb000000000ca7ae6058000aae800008540006a40bf34bb8000000169e44d20e6ac18000c0d8a355a987d01c18012a9a0194000050b56a2a4265a1562a5a117e695c000065c76600009a40001b3db576ec61e08f17baf040e1a0819a0002c4c706d7da20b608e0002b9c5830fe66fd1900c222468000045224c4138498c634bcb0000600205e00000005850bfdb4500003ac12d60c300000000f91718a1de8fac000000235a7969bbb2b40000a7e
  | 50 => 0x3c89012904a88906b1a1a20817577266852b2bb90002a9241b800000029a831e00503752b3248f80000000000be3a3b0a0f07165b60000177eba53bf80004310000000041c00000005ad00004a4853041f40000000000ae580003b440000000e3f95f9e26b8999b43fe40007a61ab000000000000d80a8b8dde1e1800009ac000790a750000209400006d00000000ab880000000000764852e689a8ae178118c4cc2d4ec3192e025d84190002c9a4f70000bc6a6a03aa994e79da33569b045497965aa7c41b0aac799967bf2c7a47f144cb4817e4083a85eb578c182f34e800000000b61400060800861d304eab178fc58f3a47863a2b900000000000201a87b800098480005a20d4a00000001386c7809b89fc000000000000006e58f6e32600003218000b3f20aa48aa15464a08666d02df6ac4105e0001c22000000000000008640000400a820c1b813e0000b52699d40684d93c87fd000067d031d14224ac4de80004ee06dba9d8ddcc1f9a447a98a18bf8b026708055e2ab800057f80001b080002190a012a380004a9c0000b58000000000000000000001c05868002b83299ca00184ad45c11c67b28cb0044249287b624562a295652c08d832f800051081c02e7000098b00005208084000000000010274f2c00043c242c01180000000000388af7400002deb8080006242f4f000045d09891a48ff02420b400000000633867a9dc512e582a5393ce0000c3c000043600020f15ce91300000ed5788000000013f000011567cf07d541923679fc1498a3699c006000000002c4000017e0000000088d50cea655ede6522f90c2e27002f51abb44aa5fc5c94f1b30c8e335400fe21c723481122afca86098867f067c000006e4198000ab992887eda893a9282953a485ff7559a5f90d2550a5f0c092fba61479410c27751ce8b9daafe72f80786be0f932659b9a76dc4782fd14003c7a0ff7ea310e57d83486bc1c2e20e823a00a41a2183a91c156d0dc9553038ad8248a24a81090000600888e2e9a4a2b041112f3093c0dae5b75cc63228000752972600014721c9800082a1c3467410656a1942c3451fd301527c8100cd1287657396c5140b6bbaaf88c3dbea3350236ade91320c0c99050da8e8a441d3e0c1a4e69cbd0923d884d6aa2c62677c8b4880300fc3b994b458700004f915f83f08000b7f8000995ab6c00000000001cde9a791e47799004c002da4aa407fc2d0a8f85cd1d73af40b3c60b956536e9a8e7611984af50000923ebb4a089f024b08fd514d189479224d0b6f892ba95087880228b825ee7a004b95e06bcc1661a00000a399e1b22389c4473000098c1c4e0000f9a00001dc4d02ff015c235001d00000000000000117a1ac40002e985021ce1ce59e6131c1798000000001876b800000011d20c6c000bba80000000000740cce
  | 51 => 0x4ec00000006c680005fe00005b30000000190200020ebbea902a0001cf609c08d434
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x866562984530431cb24c0298219a58a6014c108ece332c860846e721964304236b90cb218211d9c46590c108ece332a860847a709954304237390caa18211b5c86550c108ece232a860851c7454d430423b38cca218211b9c86510c108dae4328860847671194430423d380ca2182187d954310c10c3acaa1886084747158e5204237bb2a4290219358d5214810c3cc9318a40861e6458c520430eb22c6290219358e6214810cacc7308a40865563984520432d31cc0290219658e6014810ce4e3300a40847671997320421f3a0cb990210f5d065cc8108ece232e640843e74d96320421eba6cb190211d9c6658c81087ce832c640843d74196320423b388cb190211e9c0658c810c5ac9294640862d6454a320423b38cca990211ddc5654c81087ce832a640843d74195320423b388ca990211d5d7614c8108eaea30a6408656531853204333290c2990211d9c6650c81087ce8328640843d74194320423b388ca190211e9c0650c810a6ce9b1ca20853574d8e510438aa188728821559cc6294410aaae6314a2086656218a510429b3a465288214d5d232944108eeec994a208474764ca510421f3a6cb188210f5d3658c410cb2a7304620867251582310433928ac0188211edd56088410ce4a2b04420845e73d94210422eb9eca108211e5c16508410c9ac7290420864d63548210432b31ca2108219558e5108410acae52884208567754842104334a94c0108219c94560084108eae2b2c600865653986300423bbaac3180211d5da518c010c6ec928a600863464945300421f3a6ca180210f5d3650c0108dce5b28600846d72d94300423ab8aca180210f9d0650c01087ae8328600846e721943004236b90ca1802187592530c010c3ac8a98600864e535883004326a9ac4180219554e610c0108eeeab08600847576944300431b324a2180218d592510c010cccc5288600866562944300423ab8acb100219994a61880108eeeab0c40084757694620042b8b8ca110021179cf65080108bae7b28400847571594200422f398ca10021175cc6508010c9ac7290400864d635482004332a94c2100211ddd561080108eaed288400865663944200432ab1ca2100211d5db53c40108eaec29e20085367414f100429aba0a788021599c853c4010acae429e200847576d4b100423abb0a588021559cc52c4010aaae6296200847576946100423cbb6a5080211e5da51840108eceda9a20084767614d100429b3a0a6880214d5d05344010acce429a20085657214d100423b3b6a4880215c5c152440108ecec29220085567314910042aab98a4880215c9c05244010ae2eb10220087615288110042b838eca880211e9db5244010ae4e3a92200847a7694510042b93b4a2880219c9da5144010ae2e528a20085737588510043b0a9442880215cdd52144010
  | 1 => 0x20442b9baa65102215c1d532881109aee6b2a40884d4735952044279b82ca902211ddd563481108e8eab1a40884b77458d204425a3a2c690221995945248110b8ae629240885a5748c920442f13846490221391d93248110ac8ea99240884f276d4120442793b66090221789cb3048110f826598240884f0764c120442d9ba260902216c1d13048110da0c698240887c1324c120442d93a060902216c5d03048110bc4e418240885667588120442f0b94ca90221b85ca6548110ce4ea32a40885e17298d20442b83aac6902216cdd16348110b60e8b1a40885e37258d2044368b18c6902213c9da53481109e2ed29a40886706594d20442f1394a690221785ca53481109e6eca9a40884f07654d20442d9ba2a6902216c1d15348110bc6e4a9a40885e07254d2044338328a690221789c85348110bc2e429a40885e27290d20442f0b9486902213cdd943481109e0eca1a40884f27610d2044278bb08690221e450c4348110bc4e421a40885e17210d20442b93aec490221789d76248110ec4ebb1240885e173d89204433832ea490221d81975248110bc2e7a9240884f27694920442f1394a490221d8d4a5248110ce0caa9240885d37354920442e839aa4902213c9d85248110ba4e629240885d17314920442f13b0a490221b89d85248110bc4ea29240887627514920443e1398a490221785cc5248110f82e629240885c17314920442793b464902216c9d23248110b62e919240885e2768c920443713b46490221789d63248110bc0eb19240885e3748c920443d13a46490221785d23248110f42e919240885a1748c920442f0b9c6490221f0d4e3248110f80a71924088573754c920442b83aa6490221789d93248110bc0ec9924088763754c920442f13aa6490221781d53248110ec0ea99240885e3744c920442f0ba26490221f0dcd3248110f86c699240887c0634c920443e129a6490221f054d3248110f868699240887c0434c920442793b06490221789c83248110f8264192408847675d8c204425b3a6c6102212d5d363081109e4e1b1840884d57698c204432b32cc610221a59926308110caccab1840886966458c204434ab22c6102211d9d4630811096ce831840884b57418c204426b398c610221399c863081109e4e03184088672759802044278bb6a010221b498f5008110da2c7a80408866665c802044362b1e4010221b498e2008110da2c710040884e776480204433332a4010221b158d2008110dc4c090040884f376480204436931a4010221b458d200811087ce9314a60843d7498a530423a38ac5298210fdd16054c10878e8b02a60845f7654c530430eb22a6298219354d6214c10c3ac9318a60862e649885304316b24c4298218b9916214c10c5ac8b10a60864e63588530431b324c2298218d5926114c10cccc5308a6
  | 2 => 0xc5982211d1d562cc110aa8ea996608879143d03304423b3aec91822195997438c110cacca21c60886976410e30442e8b808718221e410e408c110caccb98460884b674995304425aba4ca982212ddd1654c110968e8b2a60884e7725953044272392ca982213cdc1654c1109e6e0b2260884b6761913044358b80c898221a5193534c110d28c829a60884d67690d304434a3248698221a5191434c110ba0e0a1a608869464cc930442aa3aa6498221a5191324c110ba0e099260884f276d413044359b26a098221ac193504c110ba4e7a8260886b06490130443c921c80982213c1d9404c110ba0e6a0260887914350130443583266098221559d6304c110d28c9182608847675d903044273396c818221395cb640c11096aed320608863665990304431b32ac818221a51cd640c110d60e0b20608847675190304426b398c818221399c8640c1109cae432060884f270190304426abb6861822195997430c110d2ac9a1860884d57610c304432b3288618221a5590430c110ba2e02186088666659883044353324c418221a9592620c110dc4e13106088666655883044353322c418221a9591620c110d8e86b1060886c4435883044371382c418221ac993500c110d62c9a8060886e262d403044370b16a0182213c5db400c110d62c9a00608879343d003044370b1680182213c5d8400c110ba2e62006088790431003044370b10801822195997300c110d2ac998060886c562cc03044358b246018221745ce300c110dc2c518060884d7764c0304432b32a6018221651d1300c110d2ac898060886c5624c03044279bb260182216c1d1300c110d62c898060886e1624c030442e9bb26018221b4dd9300c110da4ca9806088752654c030443c9ba26018221749d1300c110ba0e89806088790744c030442c83a26018221b4d91300c110f24c898060886d1644c030443c8b226018221a4591300c110f84c498060886d1624c030443e0b126018221b0589300c1109ace632e40884d573197204425b3a6c7902212d5d363c81108e8eab1e40885c57314b20442d2ba46590221591d532c81108ecebb1c40884b77458e204425a3a2c7102211d9d4638811096ce831c40884b57418e20442d9ba261102216c1d13088110da0c698440885b2740c220442d8ba06110221b458c3088110ccccb904408857275d8e20442f0b96c7102216cdd16388110b60e8b1c40885727518e20442d93a0c7102216c5d06388110da2c631c40885e17218e2044278bb4a7102213cdd95388110b66e8a9c40885b07454e20442f1b92a710221781c953881109e6eca1c40884f07650e20442793b087102213c5d84388110f228621c408867265d4a204433932aa51022174dcd5288110ba0e6a9440885d27314a20442e8b98a510221d85485288110b64e919440885b1748ca
  | 3 => 0xc252149108eeeca90a488554735485244273bb2a429221711cd5214910bc6e0a90a488567765485244333bb2a429221d1dcd5214910ac8e6a90a4887447354852442a239aa429221d198d5214910e8ac6a90a4885677054852443b1b82a429221b498d6014910da2c6b00a48876152580524425b3a6cb992212d5d365cc9109e2e1b2e64884f3705973244279b82c9992213c1c164cc9109e4e032664884f17019332442e8b84a799221651d153cc910b88e4a9e64885d37054f324434ab208799221745c043cc910cceca29664885c57314b32443a3298a5992211d9d660cc91096ce9b2c64884b574d963244278b86cb192213cdc1658c91096ce832c64884b5741963244279386c9192213c5c3648c910d2cc9a9c64886966414e324434b32665192211d9d6608c910d64c930464886b16498232442793acc1192219c9d6608c910d64c8b0464886b16458232442783aac119221b4d4d608c910da0a6b0464886d3325823244278b86ca992211d5c3654c910ce2e1b2a648847675995324425bba2ca992212d1d1654c9109e6e0b2a648865573195324423b3acc8992211d5d6644c9108eeeab226488474755913244279b82c8992213c1c1644c9109e4e032264884f170191324426b3b4a69922195196534c910ba2e129a64884d47654d324432a32aa699221651d1534c910b88e4a9a64885d37054d324432a32e8699221719cb434c910ca8ca21a64886956410d32442e8b80869922199197324c910ca8cb1926488596748c932442e8b8464992211d9d4604c91096ce830264884b5741813244278b86ca192212ddd1650c910968e8b2864884f370594324425b3a0ca192212d5d0650c9109ace632864884f270d903244278b86c8192211d9d4640c9108eaea32064884f2701903244278b80c819221355db530c91096ce931064884b5749883244332b28a419221d114c520c9109aeec9906488554754c83244273bb26419221591d5320c9108eceb30064884f27598032443393acc0192213c1d5600c910da6a6b0064886d0535803244371a92c019221b8149600c910da664b0064886e2325803244368992c019221b84c9600c910a6ee8a9ea0885347454f50442b3b92a7a8221591c953d4110aaee6a96a0885547354b50442ab398a5a8221555cc52d4110ccac4296a0885b274d8f50442d8ba6c7a8221b4d8e63d4110b66e8a9ea0885b07454f50442f1b92a7a8221781c953d41109e6eca1ea0884f07650f50442793b087a82213c5d843d4110f228621ea0885d27318b50442e8b98c5a8221b858b52d4110ba6e6a96a0885d07354b50442e9398a5a8221745cc52d4110dc2c4296a0884f2768cb5044278bb465a82216c9d232d4110b62e9196a0884f2760cb5044278bb065a8221a519143cc110ba0e0a1e60884b67498b304425aba4
  | 4 => 0xe4cab0042886d2635802144368b1ac010a210fdd1654c110878e8b2a608846f725953044236392ca9822187193534c110c38c829a6088598744c0304434cb226018221b2589300c110a9ae6296408866452587204433932ac3102215c9d461881109e2ed98c40884f3764c620442f1b9263102215c1d52188110ec0a490c40885d27308620442e8b98431022117dcd65481108b8e6b2a408854d73149204423d3b0a490221725cc5248110b52e9192408867065cc520442f13966290221785cb3148110f826598a40887c1324c520443383286290221789c83148110bc2e418a40884f276c85204433832c42902215c1d52148110ce0ca90a40884f27608520442e93984290221745cc2148110dc2c510e20885d27308710442e8b9843882212d9d0638411096ae831c20884e67218e1044272b90c708221359cc62841109aae631420886e1628821044278b84c9a9a213c5c262d4d1096ce9314a6884b57498a5344369a9ac129a213cdc96094d10d28c9a9aa6886a764d895344352326c4a9a21b8dc36254d10d4ec8312a6886a4641895344363a98c4a9a219994c6254d10dc2e0312a6886b364d815344358326c0a9a21b8d8b6054d10dc0c5b02a6886d353d815344278b96c0a9a213cdc16414d10ba2e1298a6884777654c53442b2392a629a2135dd95314d10b28e8a98a6885c47254c53442e9b82a629a213c5c26214d109cce5b2c86884e572d964344278b86cb21a213cdc16590d109e4e131486884f17098a434423b3acc121a213c5c36550d109cee4b2a86884e4725954344279b82caa1a213c9c06250d109e2e031286884f275d814344278b96c0a1a211d9d46050d109cce430286884e57218143442f0b90c0a1a213c9d46050d10ce4ea30286886b2431814344371390c0a1a213c5c86050d10dc2e430286884e1721814344278b86ca21a2139dc96510d109c8e4b2886884f3705944344273390ca21a21395c86510d10caaca29886885957414c43442caba48621a2135dd94310d10ba0e0a1886885977650c434434bbb28621a21659d54310d10b28eaa1886885977250c43443c9b828621a21651c14310d10f20e0a1886885907050c4344279384c421a213c5c26210d108eeeab10868847475588434423b3acc021a21e450e6010d109e4eb3008688672759804344278b94c021a21a550d6010d10f2286b0086884f0755804344369a9ac021a21b414d6010d10da486b0086886d1435804344348a1ac021a213cdc96010d109e2e131ea4884b77458f524425a3a2c7a92213cdc163d4910dc6a4b04a48869764d8d524434bb20c6a9221a51906354910d88c7a92a488654639495244369b1ec0a9221b418f6054910dc6a5b02a4886966498c524434b322c629221a55916314910d88e4b18a4886556394c52442b2b90a629221785
  | 5 => 0x862f64d895344316326c4a9a218bd906254d10c58c8312a68864f631895344332316c2a9a2117dd95314d10a38e8a98a68854c7254c534421f3a0c029a210f5d06014d108dce4300a68846d721805344237396cb21a211b5cb6590d108e8eab0c868846f725954344236392caa1a211d9d76150d108f4ebb0286884e9721814344279388c0a1a211bdc96510d108d8e4b28868846e721944344236b90ca21a21475d05310d10a3ceaa18868851c7550c43442cc3828621a211d1d56110d10ca8a6b0886884f271980434423c3aac021a21a650d6010d1087ee8b1ea48843c7458f524430fb26c6a922187d906354910c38c831aa48864c63d89524432a31ec2a92211bdd95214910a98e6a90a48861e6498c524430f322c629221875916314910c98e4b18a4886577158c524432a38ac6292219598d6114910caac6b08a48845e73184524422eb98c2292219698d6014910cb2c6b00a48867161580524422f398c029221175cc601491087ce9b2e648843d74d97324428e3a2a799221531c953cc910a9ae6296648847475587324421f3a6cb192210f5d3658c91087ce832c648843d74196324430f326a71922187990538c9108e8eab0c64884f271982324423c3aac1192210fdd1654c910878e8b2a648847771595324423a388ca99221179da534c9108b8eca9a648851c7454d32442a6392a6992211d9d7614c91087ee8b28648843c74594324421f3a0ca192210f5d0650c9108bce6328648845d76d4c324423a3aac21922199149610c9109e4e3300648847875580324423b3a8c998a213c9c064cc510ac8e4a9e62884b67498b314425aba4c598a213c9c262cc5108eaed29662885557314b31443a22966598a21551d532cc5109e4e1b2462884f27098a314423b3acc898a21399ca644c5109cae53226288474755913144278382c898a211d9d8534c5109e4e03126288554754c931443623126498a21399c8640c5109cae432062884f270190314423bbb2a618a21591c9530c5109e4e13106288475761483144332b10a418a211d9d763c851096ce9b1e42884b574d8f2144279386c790a211d9d463c85109e4e031e42884757694f21442aa39aa590a213c9d660c8510ce4eb306428847675d8e21442b93a8c110a211d9d6634851096ce931a42884b57498d214423a3aac690a21599d76248510acce529242884767614921442b33b0a490a21999d85248510e8ce62924288745731492144333318a490a219918c5248510ec2e029242884b674d8c214425aba6c610a213c9c363085109aaed31842886966498c214434b322c610a21a55916308510ca8eab1842884b67418c214425aba0c610a21359cc63085109e4e031842886556394c214423abb0a610a21595c853085108eeeca90428855473548214436931cc010a21b458e6008510c
  | 6 => 0x2c423b3acc8996211d5d6644cb108eeeab2265884747559132c4279b82c8996213c1c1644cb10ca8cb29a65886546554d32c42e2392a69962195d97434cb10b8ce5a1a65886576510d32c434ab208699621659d2324cb1096ce830265884b57418132c4278b84ca196212d9d0650cb1096ae832865884f17019432c423b3a8c8196211d5d4640cb109e4e032065884f17019032c426bbb2641962139dd9320cb10d28c8a1e61884b67498b30c425aba4c5986211ddd562cc310aaeea99661886976410e30c434a324a698621a5191534c3109aced21a61886946490d30c434a3228698621a5193324c310aaeea9926188694644c930c434a3246098621399cb640c3109cae5b2061886356599030c431ab2ac818621a51cd640c3109cce432061884e57219030c426abb68618621a5593430c310d2ac821861886656598830c4353324c418621a9592620c310ccacab1061886a66458830c4352b22c418621b1d0d620c310d8886b10618869564cc030c4362b16601862135dd9300c310b28e89806188695644c030c4362b1260186213cdd9300c31096ce9b1e41884b574d8f20c423bbaac790621695d232c8310aceea99641884b77458e20c425a3a2c7106212d9d0638831096ae831c41884b77458d20c425a3a2c690621695d23248310aceea99241884b674d8c20c425aba6c610621955966308310d2cc931841886556558c20c434b322c610621a5591630831096ce831841884b57418c20c4362b1e401062139dd92008310d8ac690041884f37648020c421f3a4c529c210f5d26294e108beeca98a70861d6454c5384326a9ac429c21875926314e10c5cc9310a70862d649885384317322c429c218b5916214e10c9cc6b10a70863664584538431ab22c229c21999896114e10ccac4b08a70846e721964384236b90cb21c211b9c86550e108dae432a870851c7454d4384274b90c0a1c211b9c86510e108dae4328870861f6550c438430eb2a8621c21661c14310e10d3286b00870846f765485284326b1aa429421879926314a10c3cc8b18a50861d6458c5284326b1cc4294219598d6114a10caac6b08a50867161980528421f3a0cb994210f5d065cca1087ce9b2c650843d74d96328421f3a0cb194210f5d0658ca10c5ac9294650862d6454a328421f3a0ca994210f5d0654ca10caca7b0a650866652d85328421f3a0ca194210f5d0650ca10caca6b0c610861d6494c308430eb22a6184219394d620c210c9aa6b1061086555358430842cc3a26018421a6591300c210d92c49806108666525862084338b2ac3104211e9d85248210b52e9192410864d639482084326b1aa410421995496108210a6ce829e21085357414f10842b3390a788421595c853c4210aace629621085557314b108421f3a4c529a210f5d26294d10c38c9b1aa68
  | 7 => 0x290041d8d895148020c74c8b06a78851e74d4e53c421f3a4c529e210f5d26294f10a3ce9b1aa78845f7654c53c4237396cb21e211b5cb6590f10c6aa930c878846e7219443c4236b90ca21e21475d25310f10a3eeaa18878851d7550c43c421f3a6c6a96210f5d36354b108deeca90a58861e6498c52c430f322c629621875916314b10ca8e2b18a58865a6358052c432cb1ac0296219c9856014b1087ce9b2e658843d74d9732c421f3a4cb996210f5d265ccb1087ce9b2c658843d74d9632c421f3a0cb196210f5d0658cb1087ce932a658843d7499532c42a6392a6996219594c614cb10caaa630a658843e7419432c421eba0ca196212d9d262cc71096ae931663884757694b31c42aab98a598e21399ca644c7109cae532263884767614d31c43623126498e219694d600c7109cce432063884e57219031c423bbb2a618e2199588520c71096ce9b1e43884b574d8f21c423abb4a790e212d9d2634871096ae931a43884767614921c4334a92c010e212d9d3630871096ae9b1843886556598c21c434b324c610e21955956308710d2cc8b1843886956458c21c432bbaac610e21951d5630871096ce831843884b57418c21c432ab1ca610e21595c853087108eeeca9043885677654821c4333bb2a410e21d198d5208710e8ac6a9043887615298021c4338b2ac010e21b498d6008710da2c6b0043887615258021c430e324a69862187191534c310ccaa430a41886b26458353c4358b22c1a9e21659d35394f10ba2e1a9ca7884b67498a53c425aba4c529e21659d35354f10ba2e1a9aa7884777654c53c426bbb2a629e21b494d6014f10da2a6b00a7884e672d9643c4272b96cb21e213c5c26590f109e2e032c87886366555243c4278b84caa1e213c5c06550f109cce430287884e57218143c4278b84ca21e21399c86510f109cae432887884f17019443c42caba4a621e2135dd94310f10b2eeca1887886977650c43c42cbbaa8621e21655d54310f10b2ee4a1887885947050c43c423bbaac421e211d1d56210f10d2a86b0087885e170d4a52c425b3a6c6a96212d5d36354b10bc2e1a92a5886966498c52c434b322c629621a55916314b10caac7298a5885657214c52c423bbb2a42962139dd95214b10aceeca90a5886677654852c43a331aa429621d158d5214b10ccaa4b00a5886d26358052c4368b1ac029621d85496014b10ce4a6b00a5886705358052c4371292c0296219c5496014b10dc2a4b00a5886615258052c425b3a6cb996212d5d365ccb1096ce932e65884b57499732c4278b84cb996213c5c065ccb10d2ac821e65884b674d9632c425aba6cb196213c5c2658cb1096ce832c65884b57419632c4278b80cb19621a5993328cb1096ce932a65884b57499532c4278b84ca996213c5c0654cb10caae632a6588671701953
  | 8 => 0x85354420a6ce829aa2105357414d51082b2392c6a88415cdc14354420ae0e0a1aa2107154310d510829b3a464a88414d5d23254420ae4e1192a210571708c9510823bbb264a88415c9c03254420ae2e0192a2105567308151082aab9840a8841175da5314420c3cc9298a21061d6494c510822fbb2a628841879915314420c3ac8a98a21065653984510832aa9cc2288411ddd95114420cacc6a88a21065563544510821f3a4cb988410f5d265cc42087ce932c621043d74996310821f3a0ca988410f5d0654c420c5aa9b12621064d53d893108316aa0c4988419354c624c420ccec4a8a621043e74994310821eba4ca188419c54560c84208baeb318421045f7558c210822ebb4a610841879925308420c3ac9298421045f7654c210830f322a610841875915308420cacc7288421065563944210832b31aa2108419558d5108420e8aa6908421065a53980210832ca9cc0108419c5466008420cb4a6b00421065953580210833928ac0108410fdd16394020878e8b1ca01062d5498a3008326a9cc5180411bdd5628c020c5aa8b14601064d5358a300823abacc3180418d952618c020c6aa930c601065653986300832aa9cc3180411ddd5618c020c6ca8b0c601063554586300832b29ac3180419554d618c0208eaed28c601047776546300821f3b4a8980410f1da544c02087cecaa2601043c76551300830fb24a69804187192534c020c3ec8a9a601061c6454d300831bb24a2980418d192514c020c6ec8a8a601063464545300821f3a6ca180410f5d3650c02087ce9328601043d74994300821f3a0ca180410f5d0650c02087aeb320601043f75590300821fbb4a8180410f5da540c02087eecaa0601043d76550300830f324a61804187592530c020c3cc8a98601061d6454c30083172a4c4180418b552620c020c9aa7310601062e545883008316aa2c4180419394d620c020c9aa6b10601047575984300831b2a4c2180418d552610c020caca7308601065553984300823bbaac2180418d951610c020c6aa8b08601065653584300832aa9ac2180411d5da510c020c6cc92886010635649443008333314a2180419958a510c0208eeeca88601063664544300831ab22a21804199989510c020ccac4a88601052d74d4f20083872a2a790041c355153c8020e8aa728e4010745535472008236bb4a5100419594e6188020caaa730c401065653586200832aa9ac310041c655153880208f2ed29440107525354620083a8a9aa3100411b9db5348020a5ae9a9a401054d7594d2008327b2ca69004193d955348020e1ca8a9a401070d5454d2008333b2ca290041d154e5148020ccecaa8a4010745535452008326a9ec09004196d965348020cb6caa9a40107195454d20083a4a9ca4900419cd965148020ce6caa8a40107525354520083a8a9aa
  | 9 => 0x8cbb0a64906646518532482f0b80c2992412b5d0604c920bc2e230264904ad74988324823bbb2a228a41551cd511452095ae9316629064c654c9314821fba2ca18a410f1d1650c52087ce8328629043d741943148332b10a218a419614d600c52095ae9316609054c754cb304821fba2ca982410f1d1654c120c38c9a9a609061c6414d30482a63aa6498241a3191324c120b52e919640904af7458e2048316b24c5a98418d99261d4c20c6ac930ea61063664587530831ab22c3a98419c58660d4c20a3ce9a9ca61051d74d4e53082ab38ea729841555c75394c20aace3aa4a61055571d52530830eb20c929841479d26294c20a3ae9314a6105567198253082aab8cc129841479d06094c20a3ae8304a6105567118253082aab88c129841479d36354c20a3ae9b1aa61055671d8d53082aab8ec6a9841559c75454c20aaae3aa2a61055870591530830eb20c8a9841479d26254c20a3ae9312a61054c7258553082ab38cc0a9841555c66054c20a3ce8302a61051d7418153082ab388c0a9841555c46054c20a3ae8102a61043d76950530821fbb2a829841879526314c20c3aa9318a61045f7654c530830f322a629841875915314c20c6ca9308a61063554984530832aa9cc2298418d9516114c20c6aa8b08a61065553584530830f324c629841875926314c20c5cc9310a61062d64988530831b324c2298418d5926114c20cacc7308a61066662984530831b322c2298418d5916114c20cacc6b08a61066662584530831cb24c0298419c5866014c208ece332c8610475719964308237390cb218411d9c46590c208eae232c861047671995430823ab8ccaa18411b9c86550c208ece232a861047571195430828e3a2a6a18419654f6050c208f2ea302861047671994430823ab8cca218411b9c86510c208ece2328861047571194430823d380ca21841475d25310c20a3eeaa18861051d7550c430830fb2a8621841875954310c20b30e0a18861043e74d96320821eba6cb190410f5d6648c82087eeab24641043f76952320821ebb4a9190410fdd9548c82087aecaa4641061e6494e320830eb24a71904187991538c820c3ac8a9c641062d6494a320832ca9ac1190418d953614c820c6aa9b0a641065653d85320832aa9ec2990418d950614c820c6aa830a641065653185320832aa98c2990418e552600c820c72a8b00641065a53580320830f324a7a88418759253d4420c3cc8a9ea21061d6454f51082ab39ea328841555cf5194420a6ce9a9ca21053574d4e510838b2a4a728841c59515394420e2aa8a9ca2105367414e510829aba0a728841c550c4394420aace6314a2105557318a510829b3a465288414d5d232944208e8ec994a21047676d4d510829b3a6a6a88414d5d35354420e2ca929aa2107165454d510838aaa2a6a88411d9d
  | 10 => 0x61d6498c5388317322c429c418b5916214e20c6cc9308a710635649845388332b14c229c418d9916114e20c6ac8b08a71066562584538823b38ccb21c411d5c66590e208ece232c871047571196438828eb98a921c41471d15390e208ece332a871047571995438823b388caa1c411d5c46550e208bced29a871051c7454d438823b38cca21c411d5c66510e208ece2328871047571194438822ebb6a621c41475d05310e20a3ceaa18871051c7550c438830fb2a8621c41875954310e209e2e3300871069943580438828e3a2a7994413c5c660cca20a38e8a9a651047575d85328823aba8c2994413c5c0614ca209e2e230265105377454e518829a3a2a728c414d9d05394620a6ae829ca31053674d8e518829aba6c728c415c9c36394620ae4e031ca3107154310e518829b3a46528c414d5d232946208eeec994a3105567318251882aab98c128c411d9db5354620a6ee8a9aa3105347454d518823b3b0a6a8c414d9d05354620a6ae829aa3105377458d518829a3a2c6a8c4159dc96354620e2a8621aa3105727010d51882b8b8086a8c4155dcd6254620aa8e6b12a310536748c9518829aba464a8c411d1d93254620aace7302a31055573981518823bbb2a228c410f9d3658c62087ae9b2c631067251582318821fba2ca98c410f1d1654c620cc8c4a8a631067251580318833928ac110c419c5476048620cacc6a884310655635442188338a8ac010c41b84856008620a3ae829e611051c7454e308823abacc3184411ddd5618c2208eaed28c611047776546308830e326a698441179d8534c220a3ae829a611061c6414d308831bb24a2984418d192514c220c6ec8a8a611063464545308830eb24a61844117dd9530c220a38e8a98611061d6454c308832729ac4184419354d620c2208eaeb308611047775584308823abb4a2184418d992510c220c6ac92886110666629443088332b14a2184411ddd9510c220c6cc8a886110635645443088333312a21844199589510c220a5ee8a9e4110665659472088332b2aa3904419c59651c8220ce2caa8e411061c64d8d534831bb26c2a9a418d1936154d20c6ec830aa69063464185534832bb18c2a9a4199d886154d20c70c9b02a69045f7654c534828e3a2a629a41551c55314d2087ce9310a69043d74988534823b38ecb21a411d5c76590d208d8eab14869047771595434823a38acaa1a411edc16550d208eee2b28869047471594434823b388ca21a411d5c46510d20a3ae8298869051e7550c434828e3aa8621a411b1d56210d20c98a6b1086904f171980434823c3aac021a41a650d6010d209e2e3306649065753185324832a298c2992413c5c4604c9208d8eab22649058e74d8d32482373b0a699241539d7434c920c98cba1a649064c6510d3248346b208699241725c0434c920cc
  | 11 => 0xc326b1aa420061c310d52100308eaed288801865663944400c32ab1ca2200619998a5110030ccac5288801847776544400c32b31aa2200619558d5110030cccc4a88801866562544400c2a6b96a99806117dd954cc030c3cc8aa6601861f76553300c30e3b2a998061c355252cc030e1ca8a96601870d5454b300c327322a5980619319152cc030e2aa928e601874552947300c38aaa2a398061d154951cc0308baed29c601863654986300c31aaa4c3180619994a618c030ccaa530c601863654586300c31aaa2c31806199949618c030ccaa4b0c60184797694e300c394aa2a518061cc551518c030ec2a4a8c601843e76951300c21e3b4a8980610f9d9544c030c5ec9292601862c64949300c317b22a4980618b191524c030c6ec928a601863464945300c31bb22a2980618d191514c030c3ee9b2a601861c74d95300c30fb2ec898061175d6644c03093ce9322601861f65191300c30eba8c898061179db544c030c38c9aa2601854d72d51300c24e3b4a898061475d6544c030c3ecb2a2601845c76551300c30e322a898061271d9544c030c3ecaaa2601861f76551300c28f3b2a898061471d9544c030c38ecaa2601841c76551300c327b2ca498061a3192524c030e1aa9292601861c64549300c327b2aa498061a3191524c030e1ca8a92601870d54549300c387b22a49806193991524c030c98c8a92601870c64549300c306322a49806195d96514c030d28c928a601871554945300c3a2a94a29806195d95514c030d28c8a8a601871554545300c3a2a92a29806187553604c030c38c9282601863b74d95300c31c3a6ca980618ed97644c030c76ca322601863b65951300c31db2aa898061a6193634c030ba2e3b1a60187195494d300c335b2ca4980619ad95524c030e52a8a92601874a53549300c339b2ca2980619cd95514c030e62a8a8a601876152545300c28f3a6a729e41479d36354f208beeca98a79047671d9643c823ab8ecb21e418b5526290f208eee2b2a87904747159543c8274b90c0a1e411ddc56510f208e8e2b2887904767119443c823ab88ca21e41475d25310f20a3eeaa18879051d7550c43c82cc3828621e41479d353ccb20c3cc929c659061e6454e32c8316b2cc9196418b595648cb20d52c8b04659051e74d4d32c822f3b0a6996413a1c1644cb20b1ce9b1a659058e74d4d32c82e4b86a6996411b9d8534cb2099cec29a659054e75d0d32c8346b20869964199d94614cb2095ae8302659045f7654c32c8364992c0196411ddd9511472087ce9b2e639043d74d9731c821f3a4cb98e410f5d265cc720aa8e2a9e63904ad7498b31c832632a6498e419c545600872095ae9316619061c6494d30c830e322a698641a3191324c320c38c9b1aa71045f7654c538828e3a2a629c41875915314e20c38e6b20a710
  | 12 => 0xa88615c5c04354430aa8e6b12a21853674189510c29aba0c4a8861559cc6254430ae4e0312a21855673909510c2aab9c84a88611ddd942544308e8eca12a218536748c9510c29aba464a88611ddd93254430ae4e0192a218571700c9510c29b3a060a88614d5d03054430acce4182a218565720c1510c21ebb4a8288610fdd95414430c5ca9310a21862d54988510c3172a2c4288618b55162144308daed290a21862e64948510c316b24a4288611bdd95214430c5cc8a90a21862d64548510c31b2a4c2288618d5526114430ccca5308a21866552984510c23bbb2a2288618d9915114430c6ac8a88a21866662544510c332b12a2288611b9ca65d04308dae532e821846e72996410c236b94cb20861875526390430c3aa8b1c821864e6354a410c326b1aa5208619558e5190430c72a9304821866952982410c31caa2c1208619a5496090430ce4a2b04821846e72195410c236b90caa0861875536350430c3aa831a821864f63549410c32631aa4a086195d8d51504308dce5328821846d72994410c338a8ac1988618e552600c430cd2a5300621863954580310c334a92c0188619c945600c43087ce932e421843d74997210c21f3a4cb108610f5d2658843087ce832a421843d74195210c30eaa6c690861875506348430c9ec6a92421864c63549210c32bb1aa2908610f9d3650843087ae9b28421843e74994210c21eba4ca108610f5d6640843087eeab20421843f76950210c21ebb4a8108610fdd9540843087aecaa0421861e5498c210c30eaa4c610861879516308430c3aa8b18421862e64948210c316b24a4108619358e5208430c5cc8a90421862d64548210c32731aa4108619358d5208430c6cc9288421863564944210c32b31ca2108619558e5108430c6cc8a88421863564544210c32b31aa2108619558d5108430c74a9300421863954980210c334a94c0108619c5466008430c74a8b00421863954580210c335292c0108619a5496008430ce4a2b00421867151580210c22ebb08728061475d743d0030c3acba1e801870f4354b400c30eaa4c72006117dd56390030c3aa8b1c801861f6510e400c32731aa5200619358d5290030e1886a94801847575986400c31b2a4c3200618d5526190030ccca530c801866552986400c23bbaac3200618d9516190030c6aa8b0c801866652586400c332a92c3200611d5da51900308eeeca8c801861e54d8d400c30eaa6c6a0061879506350030c3aa831a801849e76d0d400c28ebae86a006187d974350030c9ec7292801864c63949400c327b1aa4a00619318d5250030e1e86a92801865763945400c32a31ca2a006195d8d5150030ca8c6a8a801861e5458c400c30eaa2c620061875944310030b32e0218801846d76948400c32731ca4200619358e52100308deeca90801864e6354840
  | 13 => 0x6454830ac8e2b22a41856870591520c2a6b8686a9061c350c4354830ad4e021aa4185697010d520c3873a086a9061c39904354830e1ac821aa41874a7010d520c2a6b8086a9061d25c04354830a98e6b0aa41852e74185520c296ba0c2a9061539cc6154830ad4e030aa41856671981520c2b2b8cc0a90614b9d06054830a5ae8302a41856671181520c2b2b88c0a90614b9d03054830a5ae8182a41843d76950520c21fbb2a8290618b9526214830c5aa9310a41846f76548520c317322a4290618b5915214830c6ca9308a41863554984520c332a94c2290618d9516114830c6aa8b08a41866552584520c23b38ccba10611d5c665d0830a3aea21e841861d6510f420c38621aa5a10611d9c665908308eae332c841861e5498e420c30eaa4c721061879516390830c3aa8b1c841864d6394a420c32731aa5210619358d52908308eee2b2a841847471595420c23b388caa10611d5c465508308baebb1a841861d54d8d420c30eaa0c6a1061475d44350830c3aca21a841864f63549420c32631aa4a1061c310d52508308eaebb0a841863654d85420c31aaa6c2a10619994b6150830ccaa5b0a841847575185420c31b2a0c2a10618d5506150830ccca430a841866552185420c31caa6c0a10619a54b6050830d3086302841847671994420c23ab8cca210619a54960cc83087eed2a4641843d76952320c21fbb2a9190610f5d9548c830c5cc8a94641862d6454a320c31b2a6c2990618d553614c830ccca5b0a641863654185320c31aaa0c29906199948614c8309e2e030a641863954980320c31caa2c0190619a949600c830c5ca9316a21862d5498b510c3172a2c5a88618b55162d4430c5cc9296a21862d6494b510c317322a5a88618b59152d4430a6ce9a8ca21853574d46510c2b3396a328861595cb5194430acce5aa4a21856572d52510c38a39aa928861599c85494430acae42a4a21855575d0e510c38aaa68728861c55504394430a6ce9a94a21853574d4a510c3932a4a528861c95525294430e4ca8a94a2187255454a510c3a3a1aa528861d110d5294430a6ce8294a2185357414a510c2ab39ec9288615c9c36494430e2a8621ca2185367418a510c29aba0c528861559cc6294430ae4e0314a2185567390a510c2aab9c85288611ddd942944308e8eca14a218536748ca510c29aba465288611d1d9329443087ce8312a21843d74189510c23b3b6a8a8861599cb5454430acae5aa2a21871473551510c23b3b0a8a8861599c85454430acae42a2a21855575d0d510c38aaa686a8861c555043544308eceda92a21853674d49510c29aba6a4a8861c99525254430e4aa9292a21872654549510c392aa2a4a8861d1d0d5254430e8886a92a21847676149510c29b3a0a4a88614d5d05254430aa8e6b22a2187154310d510c2b938086
  | 14 => 0xe8328429843e75990214c21e3aac810a610fddb540853087aedaa0429843f76150214c21ebb0a810a6187d526308530c38a9318429861f5458c214c30e2a2c610a619358f5208530caac7a88429863b54980214c31c2a4c010a618ed516008530c70a8b00429866b52580214c339a8ac010a619c1456008530c38a931e809861c5458f404c28f3ac87202618dd526190130c68a930c809863754586404c31a2a2c32026187d506350130c38a831a809861c6550d404c2cc38286a02618dd52618c130c68a930c609863754586304c31a2a2c31826187590548c130c3aec2a4609861c5458a304c38a2a4c318261c5151618c130c9cc6b16a81866662987540c332b14c3aa0619998961d5030ccac4b0ea81852e72d52540c296b96a92a0614d9c75495030a6ae3aa4a8184777158a540c23a38ac52a061479ce6295030a6ee2b14a8185347158a540c29b38cc12a0614d5c66095030a5ce4304a81852d72182540c29b388c12a0614d5c46095030a5ce5b22a81852d72d91540c29b38ec8aa0614d5c76455030c38c7b12a81851e73989540c28e39ac4aa0618718d6255030a6ee2b12a81853471589540c29c382c4aa061479ce6155030a74e130aa81851c73585540c30e31cc0aa0614d9c66055030a6ae3302a81861c63181540c297390c0aa0614b5c86055030a6ce2302a81853571181540c21fbb2a82a0618b5526215030c5aa8b10a81863554984540c31aaa2c22a0619398e6215030c9cc6b10a81865663984540c333314c22a0619958a6115030cacc6b08a81866662584540c332b12c22a0619a58a6015030ce2c3300a81861e74597430c2a6b96a9a18618759654d0c30c3aa8b06861863954582430c28eb9aa82186187d954310c30c3acaa18861863a54580430c28ebacc821861875966410c30a9ae5aa0861851d75950430c22fbb2a821861879915410c30a3eecaa0861861f76550430c28fb92a82186117dd56010c30c3aa8b00861869a64580430c31b2a4c3a90618d55261d4830c6ca8b0ea41863554587520c2973a6a5290614b5d35294830acce3a94a41856571d4a520c23bb8ac9290611d1c56494830acce3aa4a41856571d52520c38639aa929061599c45494830acae22a4a41854d75d0e520c386aa68729061c35504394830a9ce7b24a41856771592520c2b238ac929061c350c4394830a5ce830ca41852d74186520c2a7398c3290615a9c06194830acce3304a41856571982520c2973a0c1290614b5d06094830acce2304a41856571182520c21f3a0c2a90610f5d061548308dcedaa2a41856671d51520c2b2b8ea8a9061c31ce5454830e18e6aa2a41846e76151520c2b3388a8a9061595c45454830a9aeba1aa41870e54d0d520c386aa686a9061c39504354830e1aa821aa41854e73d91520c2a639ac8a906159dc5
  | 15 => 0x3c74595218c32a31aa290c61591c9514863087ce9b28431843d74d94218c31b324a210c618d5925108630cacc7288431865563944218c2b2b94a210c618d9915108630c6ac8a88431865663544218c32ab1aa210c619c5466008630ce4a2b00431867151580218c23abb4a3204611ddd95190230938e8b2e611851f74597308c30e326a9984618799154cc230caacb28e611865565547308c338b2ca3984619c59551cc230a6ce3b1ea89853571d8f544c29b38ec5aa2614d5c762d5130c5ec5316a89851d7318b544c21fbb2a82a2611ddc562151308e8e2b10a89852e72d8c544c296b96c62a2614d9c76315130a6ae3b18a89851d73d88544c28eb9cc42a2614ddc56215130a68e2b10a89851d73188544c316b10c42a2614d9c46215130a6ae2310a89853970188544c28eb9ec22a261475cc6115130a5ce4308a89852d72184544c29cb80c22a2618e15260d0d30c3ee932c869861e65d52434c30e2a2c521a61871526090d30c76a8302869851e75d91434c22f3b0a8a1a61479d85450d30c3cec2a2869861c54d89434c266b90c0a1a61a6d906050d3087ce930ea49843d74987524c21f3b6a8a92610f9d85454930c6ea9b0aa49863454d85524c31baa0c2a92618d15061549308deeca90a49856471548524c30e2a4c7a12618715163d0930a3ceb21e849861f5498e424c30e2a4c7212618715163909308ece332a849847571995424c297396a8a1261479d64350930c38cb21a849863754d85424c31a2a6c2a12618dd506150930c68a830a84984f170185424c23b388ca212611d5c46510930a5ae42a0849861c5498c424c30e2a2c6212618e15260109308bcebb26649861d64153324c30f328a999261879d854cc930c3aec2a6649870e72153324c386b90a9992618715260cc93087ceb324649843c75592324c21ebb6a9192610f5d8548c930c6ea9b0a649863454d85324c31baa0c2992618d150614c930ccea430a649866452185324c31c2a6c0992618e150604c9308bcebb2264984d870591324c2a7394a89926187d90544c930c3ac82a2649861e76151324c3862a6c499261c3153524c930e1ea8292649871454d85324c38a2a0c299261c6153604c93093ae8302649861c54181324c38c2a0c099261b4d84604c930e1ea8990649843e7498b514c21eba4c5a8a610f9db545453087cec2a2a29862f54d89514c3162a6c4a8a618bd506254530c58a8312a29847776544514c2b2392a228a618715263d0530c38a8b1e829846e72194414c236b90ca20a61871526310530c38a8b18829863854980414c31c2a2c020a618e152608c530c70a8b04629843f74597214c21e3a2cb90a618715263c8530c38a8b1e429843f74596214c21e3a2cb10a610f9d3654853087ae9b2a429843f74594214c21e3a2ca10a610f9d0650853087a
  | 16 => 0xc28f3b0a8a1e61879d85450f30e32e02a2879861c54d8943cc30e2a0c0a1e61335c86050f30d3286b0087985717018552cc32b398c2a9661955cc6154b30ce4e030aa5986717018552cc237bb2a4296611d9c765d0b308eae3b2e85984777159542cc23a38acaa1661365cc6050b30d3486302859845f7559332cc30eb20a999661479d252ccb309e2e030a659849d74d9532cc28f3a6ca99661361c1644cb30a9ce52a2659861d6415132cc2e4b86a499661479d2524cb3099cec29265986576518532cc2e8b80c299661275d0604cb30d9264b00659864c624c951cc23bbb2a228e611b9cb65d07308dae5b2e839843e74d9721cc21eba6cb90e610f9d3650873087ae9b28439867161983548c23bb8ac52a4611d1c5629523087eecaa0a91862d54588548c22ebb6a821c61275db5410e30b34e1aa0871851d76d50438c30ebb6a821c61475cb5410e30e2ce3aa0871871571d50438c38d386a821c61635c85410e30b34e02a0871861f54580438c23bb8ac9294611d1c56494a30c3ec821aa51846f76548528c316b22a4294611d9c665d0a308eae332e851861e6510f428c23b38ccb214611d5c66590a30c9ac7294851864d6354a428c23bb8acaa14611d1c56550a308ece232a851847571195428c38621aa4a14611d5d76150a308eaea30a85184f170185428c23b38cca214611d5c66510a30c5ac9294651862d6454a328c23abaec2994611d5d4614ca30acce42a4a31856572152518c2aaba88728c61c5d504394630a6ce8294a3185357414a518c2aab9ec928c615c9c06494630a6ce9b1ca31853574d8e518c38aa188728c614d9d06294630a6ae8314a3185557318a518c332b10c528c615c9c06294630aace7214a3185557390a518c23bbb28528c611d1d94294630a6ce9194a318535748ca518c23bbb26528c614d9d06094630a6ae8304a31856672182518c2b2b90c128c610f9d0625463087ae8312a31847676d51518c23b3b0a8a8c61599c85454630acae42a2a3185557510d518c38baa086a8c611d9db52546308ecec292a31853674149518c29aba0a4a8c6155dcd6454630acee4b22a31856472591518c29bba2c6a8c614d1d16354630acee4b1aa3185647258d518c2b9b8286a8c615c1c14354630e2a8621aa31853774589518c29a3a2c4a8c6155dcd6254630a6ce8312a31853574189518c2aab98c4a8c61995886254630ae4e0312a31855673909518c2aab9c84a8c611ddd942546308e8eca12a31857270109518c2b8b8084a8c614d9d23254630a6ae9192a318572708c9518c2b8b8464a8c611d1d93254630a6ce9302a31853574981518c2b3394c0a8c61595ca60546308eeeca88a31865663946418c237b92caa0c611b1c96550630ca8c6a8a831867251580418c33928ac118c619c547604c63087ee8b2a43184
  | 17 => 0x8843a9951620c421d4aa8b106210ec6535883108762a9ac418843c355153c84218daed2944210f155454e210863abb4a51084393d965348421c9ecaa9a4210f0d5454d21086733b462908431d5c365484218eaeb31a4210cb67498d210872bb2ca69084395d955348421e2aa8a9a4210da5748c921086723b26490843b118d3248421c3cc929ea010e1d6494f500870f322a7a80438759153d4021ab4e7a84a010d5973d42500861fba2c7280430f1d16394021a74e9a9ca010d3974d4e500878d2a4a728043c69515394021e32a8a9ca010f507154e500869d3a0a7280434e5d05394021ea4a730ca010f515398650087a8a9e6328043785c83194021ad6ea90ca010d737548650086b938ec7280434edd16394021a70e8b1ca010d3a7418e500869cba0c7280435a9c86394021ae4e231ca010f194310e50086ad398c528043565cc6294021a74e9194a010d39748ca50086b9b8a65280435c1c5329402187ce831aa010c3d7418d50086b8b8662a8043595c83154021ae2e018aa010d7170885500863bbb242a80435cdc121540218f4eda9aa010d3a74d4d500869cba6a6a8043c69525354021ea0e329aa010f1a5454d500878caa2a6a8043d41c553540218f4ec29aa010d3a7414d500869cba0a6a8043d494e6154021ea2a730aa010d7175cc550087992a662a8043cc5533154021ea4a798aa010f5153cc550087992a062a8043cc5503154021ea4a618aa010f51530c550086f0b9062a8043d254f2154021ea4a710aa010f515388550086b5baa42a8043d254d2154021ae6ea90aa010f525348550087a8a9a42a80435c9c76354021a76e8b1aa010d387458d50086b4392c6a80435c1c56354021a74e831aa010d397418d50086b5390c6a80435c9c46354021ad4e521aa010d697290d50086b938c86a80435c5c64354021ae6e2a1aa010d707150d500878ca1886a80434e9d23254021a72e9192a010d72718c950086b8b8c64a80435cdc53254021ae0e2992a010f49320c950086b938864a80435c5c43254021ae4e730aa010f617298550086b8bb662a80435c9d33154021ae0e998aa010d7172cc550087a999662a8043d44cb3154021ad4e418aa010d69720c550086b9bb062a80435c5d83154021ae4e818aa010d70740c550087a939862a8043d89c83154021ae2e418aa010f61720c550086b0b9062a80435c9ce2154021ae0e710aa010d737648550086b939a42a80435c1cd2154021ec6e490aa010f623248550087b099242a8043569cc2154021ab2e610aa010c5d7694c500870f324a6280438759253140218beeca98a010e1e6454c500870eb22a6280439694e6014021cb2a7300a010c7b76540500872d31aa0280439658d501402187eecaa0a9984777158854cc23a38ac42a661665c35450f308bcec2a2879849e7615143c
  | 18 => 0xd4c21c74c8b06a610e3964583530873930ac1a98439c9c560d4c21a3ce9a9ca610d1d74d4e53086ad386a729843565c35394c2187ee8b04a610c3c7458253086ad386a929843565c35494c21a9ce5b24a610d5671d92530870eb20c929843479d26294c21a3ae9314a610d5671982530868fba2c129843471d16094c21a3ce8304a610d1d7418253086a7390c129843559c46094c21a3ce9b1aa610d1d74d8d53086ad386c6a9843565c36354c2187ce8302a610c3d7418153086ad386a8a9843565c35454c21e2ca830aa610f155418553086a7394c8a9843559c66454c21aa8e2b22a610e1d64191530868f3a4c4a9843475d26254c21aaae030aa610d1d7408553086ab38cc0a984347dd16054c21a38e8b02a610d4c7258153086aa38ac0a9843479d06054c21a3ae8302a610d4e7218153086ab388c0a98430f5da5414c2187eecaa0a610e1e5498c530870eaa4c62984317dd95314c21c3cc8a98a610e1d6454c530871d2a4c0298438e5526014c21cb2a7300a610e3a54580530871caa2c0298439654d6014c21c3cc9318a610e1d6498c5308716b24c4298438d5926114c21c74c9300a610e3964980530872d31cc0298439c9c66014c21c74c8b00a610e3964580530872d31ac0298439a9896014c21ce4c2b00a610e7271580530863d384cb218431e5c26590c218f4e032c8610c79701964308636bacc5218438b5526290c21c5aa8b148610e4e5358a430863abacc3218438d5526190c21c6aa8b0c8610e5653586430863d384caa18431e5c26550c218f4e032a8610c7970195430868e3a2a6a18439554f6150c218eaea30a8610ce572185430863d384ca218431e5c26510c218dce43288610c7671194430863d380ca218431e5c06510c21a3ae92988610d1f7550c430868ebaa862184387d954310c21c3acaa188610c3e74d96320861eba6cb190430f5d6648c82187eeab246410c3f76952320861ebb4a9190430fdd9548c82187aecaa46410e1e6494e320870eb24a71904387991538c821c3ac8a9c6410e5553586320871b2a6c2990438d553614c821caca7b0a6410e5553d853208726b2a6419043c3551320c821c6aa93086410e3554584320872b29ac219043b14c9610c8219cae53266210c7575193310871ab2aa9988435c5c353cc421caacb29e6210f165454f310878aaa2a798843555d732cc421aaeea9966210e55535833108673b92c1988439354d628c42187ce93286210c3d74994310861f3a0ca188430f5d0650c421c5aa93106210e2d54588310872729ac4188431d5d4640c4219cae43206210cf170190310871ab2ca8188438d595540c421caacb3186210d7170d4c310872ab2ca6188431ddd9530c421cacc6a986210e556554c310878aaa2a6188431ddd5620c421d8cc6b106210ce7755883108733baac41
  | 19 => 0x2b06a918e7271583548c69d386a92a4634e9c3645523187eecaa0a918c6f76548528c63d384cba14631e5c265d0a31c3ca8b1e8518d2c72551428c71b2a0c2a146399948614ca31a74e9a84a118c3e74189508c61eba0c4a84635c5c331542318f6eca80a118e2f5458a544c726b1cc52a263935ce6295131cccc4b0ca898c3f76550544c696b94c82a2638b59352949318deeca90a498e4d63d4a424c726b18a5212638d1536150931cc8a5b0a8498c7a70194424c63cb80ca21263175da54cc931a9ce52a66498e2d64d4a324c716b20a5192639914b614c931a9ce52a26498d4e75d89324c6a73b0a499263939d8524c931a9ae02926498f4452d85324c7a2290c2992638715163d0531e88a49966298c6e72993504c636b94c9a82630f9d262d413187ae9316a098d7170cc7504c63dbb2a0282631b9c860550318dae4302a818c3f76550540c716aa2c42a0638e5516015031c9cc6b10a818e6471588540c732b14c22a0639a98a6015031cd2c5300a818e7271980540c72d31ac02a0639a9896015031cd2c4b00a818e7261580540c73938ac02a0638d5526190c3187ce8302a418c3d74181520c637bb2a4290638b5915214831cd2a4b00a418e4e6354a420c63d380caa10631e5c06550831c6ca830a8418e3554185420c733290c2a1063995486150831c3aa931c8218c5d7694e310c63abb4a7188631d5c3654c4318dce4322a018c6d72191500c61f3a0c4a80630f5d06254031ae2e118aa018c77764c5500c6b9b8262a80631edd95014031c72c8a80a018e6962540500c716b24c5a9e43479d35394f21a3ce9b1aa790c3e7418153c861eba0c0a9e4317dd95314f21cccc4b08a790c7b7059543c863c382caa1e431e9c06510f218f2e03288790d1d7494c43c868fbaa8621e43475d54310f219c8e2b108790d1e74d4f32c870f324a71964387991538cb21a3ce9a9a6590c5e7614d32c862fbb2a6196439354c624c7219cae43206390cf17019031c863abb6a618e430fdd16394321878e8b1ca190d547358550c86b8b8062a86431edd950143218beeca98a710e6562984538863d384caa1c431e5c26550e218f4e03288710c7970194438872b298c299443179d8534c6218beeca986310d7170c85508863dbb2a028443875935394d21c5cc8b14a690e3664586534862fbb2a629a43475d26314d2187ee8b00a690c3c745805348636b96cb21a431d5c76590d218eee2b2a8690c7b70595434863c382caa1a43479d35350d218eee2b288690c7a70194434863cb80ca21a43879954310d21c38caa188690c6c75588434863b3acc221a431d1d56110d21ca8a7b0a6490e4c5358b314861f3a6ca98a430f5d3654c521a6ce929e4290c3e7498f504861eba4c7a82435c5c321d41218f6eca80a090e3a64983530871cb24c1a98439c9c66
  | 20 => 0xc5458f424cb0eb2886a1265a3993528c932ae6e0aa6a29957070553514cacb3a6c7a8a65719cb43d4532e2aa821ea299596748cb514caaab9ec9a8a65595cb64d4532a6ce9b1ea29953574d8f514cb8aa1887a8a654d9d362d4532a6ae9b16a2995567390b514caaab9c85a8a651ddd942d4532a6ce9196a299535748cb514ca9b3a0c1a8a654d5d060d4532aaae6306a29956572183514ca3bbb2a228a651d5da54145328eeecaa0a29957370550514cab8382a828a65719cb4314532aacea218a2997155410c514cacb3a46428a65555cf6414532aaae6320a29956572190514cab9380c828a655c5c06414532a6ce9b18a29953574d8c514cab9386c628a655c5c36314532acce5a18a29956572d0c514cb8aa188628a65559cf4214532aaae7a10a29955673908514caaab9c8428a651ddd94214532a6ce9190a299535748c8514caaab9ec028a654d9d06014532a6ae8300a29955573180514cab2b90c028a651d9c664d41328eae3326a09947771593504ca3a38ac9a82655c5c361d4132ae2e030ea09947676d45504cb1bb26a2a82658d19351541328ecec28aa09963764145504cb1a320a2a82658d9935114132c6ac9a88a09957170d44504cb1b320a2282658d5905114132ae2e0288a09947b76540504ca9c3a2a02826587dcd6414132c38e6b20a09963870590504ca2ebb68628265875934314132c3ac8218a09963664984504cb1ab24c2282658d9916114132c6ac8b08a09947671983540ca3ab8cc1aa0651d9c660950328eae3304a81947671181540ca3ab88c0aa0650fdd95415032c6aa8b08a81963954580540ca3ab84c22a0659598d6115032cccc4b08a81947770584540ca3b38cc02a0651d5c66015032ce4c3300a81967161980540cb3938cc02a0659c5c66015032cb4c6b00a81966a62580540cb3930ac02a0659c5856015032ce4e2b00a81967171580540cb16aa4c521865475d25310c32a3eeaa18861961e5498e420cb0eaa4c72106517dd56310832aaae22a6641955970153320ca2ebb4a71906587992538c8328daed29c641945e76151320caaab88a899065565c0544c832a3ce9292641954d75909320cb862a28499065711c5424c832caecbb0a641965765185320cac6ba6c69906553dd5434c832ccecbb0a641966765185320ca3bbb2a2288658d5915114432ce2a2b00a21947671191500ca3ab88c8a80651edd95014032c72c8a80a01967161540500ca97396a92a6631b9c860553318dae4302a998c3f7655054cc71b2a2c221e634b9d35294b31c6ee2b24a598e347159252cc61f3a0c0a96630f5d06054b318deeca90a598d2d7494b42cc70f2a4c721663875526390b31a3ce92966598d4e7295132cc62f3b0a899663479d2524cb31caecbb0a6598d647258550cc63dbb2a0286639c9c660d5231ce4c
  | 21 => 0xf46a1cc428887a350d62144438eeeca88a221f15435445110f32b12a228887a650e6014443d3286b00a221e71515805110e4fbb287a8087271d94394043b30e0a1ca021e95439865010f4aa1ac328087271d94354043b30e0a1aa021d5a7090d5010eac38286a808787dd94354043a38eca1aa021e1c7650d5010e8fb9286a8087c6dc14354043a38e0a1aa021f187050d5010e8c38286a80871d9c462540438eae2312a021c9f7650c5010f46a1cc428087a350d6214043d2a87308a021e95435845010e3dbb2a0280879a5895014043ce2c2a80a021d3671d5254cca3b38cc12a6651d5c660953328ece2302a9994757118154cca1fbb2a82a6651d9c660153328eae3300a99962e5458843cca8fbb2a821e6587dd95410f32a38e0aa0879961d5458043ccac739087a16654d9d351947328eeeca88a39945d7610e50cca3b38ec8a86651d5c764543328f6eca80a19947671983548ca3ab8cc1aa4651d9c660952328eae3304a91953671d8e548ca9ab8ec72a4654d9c46295232a6ae2314a91953a7018a548ca9cb80c52a465475cf6195232a5ce430ca91953671982548ca9ab8cc12a46547dcd6095232a3ae6304a91952e72182548ca9b388c12a4654d5c460952328ece2302a91947571181548ca9bb8ac6aa4654d1c56355232a76e0b1aa9195387058d548ca96392c2aa4654b9ca6055232a6ce3302a91953571981548ca8fb9ac0aa465475cc6055232a5ce4302a91953671181548ca9ab88c0aa4650fdd95415232c5ca8b16871962d54d89438cb0f2a4c721465879516390a32c3acb2a6651961d65553328cb16b2ca9994658b59554cca3287aed2a0a31943f76550518ca3bbb2a228c658e9526014632c72a9300a31963a54580518cb1caa2c028c659c5456014632c6ca930ca11963554986508cb1b2a2c3284658d551619423287aed2a0a11943f76550508cb1b2a4c2284658d5526114232c6ca8b08a11963554584508ca3dbb2a0284659c58550142328ece3306a89947571983544cb2ab1cc32a2659958a61951328eae130ca89947770586544ca3b38cc12a2651d5c660951328eae1b0aa89947570185544cb39b0ec0aa2659c1876055132ce6e3b02a89967071d81544ca3b388c0aa2651d5c46055132cb6c6302a89967361181544cb38308c0aa2659a5c86055132ce4e2302a89967171181544ca1fbb2a82a2654e1c154151328ece3300a89947571980544ca673acc5a1a65939d662d0d3299ae1316869953870552434ca1f3b0a8a1a65635ca5410d328beecaa0869955870550434ca4fbb2a821a6563dc95410d32b30e0aa0869951f76550434cb0fbb2a821a6547dc95410d32e1ee4aa0869971771550434cb8a38aa821a65c6dc15410d32a38e0aa0869971870550434ca8c382a821a65331c96110d32c3aa8b00869961
  | 22 => 0x200000080000060000008000006004000001000000a0020008010000000000c002001003801001400200200000040090000008000000003000004000000000040000000010014028002007003400c0020008030018008002800c00000d00180040040010028004004000000000000400d0008004002000001001c000000000801000a00b0020014000003003000000c0030010004000000002001c00200900000540100020010004002002000800400000000080000020020170010002000000001800200400000100040110000038000001002001000000100100280040000070000000000002000000c0000000000006000001800000a000003800800600100100180020000008004006000000800c002001006002400200300300040000030000000000000006000000000a000000000200200080200080030000000002002006800800000d0068004000000000001402200b000000400a000002801400800400080280000000008000000000001801c0060000008004004005001801000000000300080040000010008000007000000000000800100280080070018008005599c75294a438ece3304a521c75719825290e3b388c0a94871d5c46054a438deeca90a521d6672d465190e3bbb2a228c874e9c343542438ece3b12a121c7571d895090e3dbb2a0284871e9c261d49438f2e130ea4a1c76719835250e3ab8cc1a92871bdd952149438ece3300a4a1c75719805250f39a8ac128a871ddd951145438eee2b16a0a1c747158b5050f38b0ea1282871edd95014143a72e1218a0a1e2e435885050f33314c2282879958a6114143cccc4b08a0a1e65625845050e2ebb4a921887335c86050c43c3aebb2a8621c9d72d954310e4f386caa1887879db6550c43a3ae1b2a8621c9e70d894310e8ebacc4a188747dd56250c43b2ee2b128621d94715894310ecdb82c4a1887661c16250c43a3aeb30a8621d9a709854310eccb84c2a188747dd56150c43a3aeb3028621d96719814310ecab8cc0a188747dd56050c43b1ce43028621d8d721814310ecb388c0a1887655c46050c43c3aea3028621e8e721814310e4eb90c0a1887a35c86050c4391ae43028621e96711814310f4ab88c0a188727dd943d484393eeca1ca421d8f7250e5210e3b38cc1290871d5c6609484393eeca1aa421d8f7250d5210f4aa1ec2a9087a550c61548439e2e030aa421c7570d855210e3d380c2a90871e5c06154843ae2e030aa421e56731855210f2ab98c2a90879c9c061548438eae030aa421e71701855210e38b80c2a90871d9c460548438eae2302a421c9f7650c5210e37bb2a429087c350d5214843d2a87308a421e95435845210f32a92c229087a650e6014843d3286b00a421e69525805210e4fbb287a88871e9c062544438f2e0312a221c9f7650c5110
  | 23 => 0x1001000000000300700040000000000034004002000801802800100100000020020028000004002000000000200000100280000010000048002000001000000800d0040004002000006001800000e00380200000070088008000003001802000400100a800000200000000140060000020000000002000000c00400a002801400401200480000080000000004004006003000000c000001000000400900000000000010008008004000001800000000200000000000000000008002002000000000000100000000080000000004006000004800c000002001000000000000000000040010018000000000001000400000600000000000060008004000001001000c000005000800c00e0040000010000007000000800000000100180000010000008008000000800c000001000000800000400000080000030000000004000000802000200000000180000000000004000001000800400800100000180160010008000002003000800000200400000100000000000004006000001002c00000000180000020020058004002001002000401600300080000000060038008008001002800c00200b001000800a000000001400c00000100000020030000008000000003000000600a0008000000001000000400c0140000010000000001800000000100100100020000000004000014000000000800200000100060090008024000001007000001600000080140080010070008004000003001400a009003000400800f000006c0000040000020012002000800400600000100000060010008000000000002004800800000000340020000038008008001000800801a00000100000000000000000006003000000c002002000000400c0040008008000002000001000000400700080000000008004002009000001800200500000240020020018000000000004000000000b004000c004008000001c002002004800c0140030008004004000003000001a004001800000800000100040020000000004006000003002400800700000100080000018028004000002800000200100180000100000000004000009001800000800a0008004000000002000000000000280080180030018014008000000007c000000002000000e002000001800400200200380100000008000000002000000c00200b00080080040070010000000000009000c00400c0050000010001001801402200000180040020020008004000005000800800200600100000140000058000000000004000000400000000000000010000058006002003001c0020030050000022000005001000000000b0014000000000000000000000200240000010020000010002000800000400100000180040000000000000000002800400000200000000000040000068000004004002800c001000800
  | 24 => 0xf1f444c4bb11a24000ca8141092b705588358d4a9ac0cb615067f0e6e4401150000cb2684803aba0cd00004e039c19949f1bfe49516b60000000000000140961698879c7dc9355a680002ae3385361d40b6600057f2aa5480a070000648000779000373c00000000000000000006812c6c0000000002e35bc945400080040000000000000000002800001000100300000020000000000002001007002400000300080100060030058004000003005000001800a002000800000b001000400600000000040080010008020000002000001c0080000000004004007000000c004000002800000e00100100380040050018000000000003001c00200000180040040000008008006009000001400000800080000000000000008000005000000000a0010028008002000000000c008000000000000000700200180040010008004008000000801c008001002001000000c001001c012004000000401c0020000000000001000002c000006005800801c001001800401400500080040000010010000022000000800400000000280000000040000000000000001000000200300080180040090000020002002000000000a00600400240000000020008000001006004800400c002000400600000200000040020000004000000005800c01c003001801000e0000008000008002000800000600b0090000004000003001000a00100000040000000008048000000000000400000200080000000000000000000002001800000000200280080080140000014006005002800800a000006800c00000200500080020010008004002000000800802800c000800800000a000802400c004001000400000000000080040010030000000000000001c00000a0000000006000003000800000000100040000000000000004001001000000000a00300140000010008008008006001000400800300000000080030010000000002000000800000500200000000010000010006000001000800a002000000000800000c000000e00400000000000020000000004001000000000000b0008004002005003001c0020030030010000001000000400a0000000004006000000800800a001002000800000100100080040000008028014004000800000000000000000000000000004000001000000801600300100000000040000018006000001000000e0010008000002000000800000000000000080080080008000004001000800000000500100080000000018028004001002804000e00100280140000020000030004000000000401000500180040000000010000000016003800800a000000003000600000b802c00200300200040020020068000010000000800002200100400080000030000020000000000000c00400500000000000000058008010001001001c00600
  | 25 => 0x337e9b55c0f6e0001cf0000000cdf0001522de09d35a08001a32376578b779948b300000f10000553bbba5100001f900000000003be00010d85539360001f34b369050000000000bb20443678c8600000005bc0004da37e1eb15de5323068001a850000001641d4cb20b0800000000001e0b494000609000000155c00000023318b20000000000a367cfd4f9badbf60004db8000000a7a00000017e60000000000000b73d780000047064e2f2e74ff66a780005dc91e3026ea1a1cb8d000556227400086f00000000000c824a02d0760e0b000000000031236700009d00004af400000000000025e56c40000000a3e000db10e327054c2e47483189c00021a2e18000d86000000231c000c1514a400000060e85e469000000000031f400000000030ce00000037080005500003f4a06c2da657550ae6c00000027657e47c6e2b0000000284000301a701c480006a5f2fc5170000000001a880002148000d4e000000000000000000036883cf4d6575a16589ccaf02f15ed896a7400000000009d600000018e14aebc5800000000065a0c909c40006163479a7a0000000001c5872f00039acbc20fa5b508c800007700000002c4000396b7bc000000000286189e00000007e80000001eb0000000000000000000037400008740001ba80000015c0317608c00176abbb05ff4e03ae2168626c5dcde8960000225b9a00012a000000041b000353881e0914b780016c00000000374000ea74b140018981a1afaac991a248400036e829c00063d000000000040837007e8470000012a66ec41000000142c0000858000dea0000001f851a500000009c40000000000c866aa0005cb25b11dac27127868943869027be7b8dfc00000034d4000ba11b8a2300009cf72825a05109608000000e00ab9274b17505857d800327546800000000010a800069700000000005610d58000b7f0000274c5c000000298d1c25a757fa1856b00001be34e83fe0001dda690fc638804b83c8a8600030b0001ae0bc60000000000000000000081a24a0000000d08e7e0000078000000000190f2ce883000000000000000009940005d2015e50dc9a0000075871d4a0000001e084fe00051b2e7cb401e90000dbc00000000000000000000002f1567c8df5804f0851e0e1524000012c00031b00000f6cad00000000005df2f90000000a8a0782ff118490725436a10c6b4400000018fe9aa0001650b057c514b1a60ddc00005d24851e30ea1ace7e4016b0414583cc000e4847d3524b3e3180000001b526121b00000000c7063b0ff40005220000001d48000373800199e0005630001698000000000074e0000d68ce48f800000039e0000000000000159500012d80018bb038bbd0bb9659e6e3c8064da181ce382863530422eb81a7d15087c05694879b2cbfa87
  | 26 => 0xcec000420090000270c9bed5017d35b8b44ac800022ad2c75d85351a90000af9498b56c8200004a480000000000001850000000295800139acf50001566fe40000002b1d2b4b880504000418d5223338840000000f441c000031d3058712e8d9e62fceb50ffe84034b9fe800086410aba44000000000000026a66412083bc0ce1e280000000000000002a395a073a0000000000c6257b33c800000000000000000000000000e0e72c000000095e0000000000000c3016e068e4f20002a0aa9400092600000016d6000000000017c0f3cdadbb400041480000010607fc631a069a5e000000000000034300000018b49e106dcf06b45000107a5889d796fd9a800000000057519521926eb80000000000000000000000bea12e9da1272aee660cf7b35c066308c00000042a63000007631286f61cc141a93b0d08000e20b292a60000b48c31cf200001969b17388260c9c000000204453000000000007ca0b000020b87720000000000000a1000034a15b87ec0000000000d9c3252fe1b5ad38ef80000d05000121b71eea80000c214961a2000000000000003768385340003f15abb4d2982bee000000009e0ac000216c00000000017d11722490000001a360000f0c0000000001968b8c13200000006996d100000000a000072e00010dfb40798f182d440000000000001a2b00009187342fe7d90000000914bc90000228000a9d093b7443000000000b2cd404440000000000000000284c2040000000000000ca10000d7d93c2406c20000699daf0001769bbe2803028001d5c000051290c0000000ce2e8200000029c0000000000159c0007640006429d5c0000000f98000000000000324c00000003780019b600000011ed1242a158d3710000299000000141000000000000002c51378a159a87910001e040000000000000e43000025224ca720006b980001d800000000017b431900000000007fe0002d70f4c9142461a0c2e60003cf8000e3e533221800132b0004458001aa95d76418000000a2d6749564c5e33b02b800000027c5558000000000000105ecfabac13d8000b72e083f683fc00068e1e5c000000000606b5fc85c94d6e919d117c000135a250968ae838a8000c624fb58300000000d0000054afbc000000000036200000000000000000000000daec1415c820878a0c5000000000000000000000006e62921e39a820000001d000009966789c44d7e3a20ed93f01f55918000000c70d3900000000007e50000fd7d700000002f1d8937b92e6b9fcaf09dd595c00011600015f000195000000000015ac00011ba8d651a9f23761028f2e00024c800145e0001e145f81cc39f5fc80beb2ee310000c14012c8d5880072b6c0000000000000cc900000000005ac8002f5a0d46bd6eba0710a22124bf540c7540001e300000000005c634d80
  | 27 => 0x5b067300880012084b3000000000000000016203a4c395e226a12cc2cd0002fac00090b1015fce0004cc4712ee400000016a000059cb5a1aa0d0174c5cedfb5cdc1767c5b3c19a0214000000252c2a2bc815d332800000068530c87382ae43c8000878000546000000061e71a00000007390000001b06e5b74f8000000000000234d680cf3000000044ee6601f84a48d8e0039884e56e6ebe05c000000000000000000005838355ae4d8c9fad2d00000000004280001982dd626134c899ad80244ac14000a9071294981a654d484100c63800013c303f1860000000cb80003b4ab89aa4f9000000000000000000000000000000715134987c0007020000000000000000159c00000000001d2000284357807a00000023388c96c425547b7b910000002cf04ee84e35b80001f00001dc40008808242388001626a97647ac3c000230025eafdcd400018d199c1170000000000d92000000000097a7e2000000000085f3cfee400000000000af4000b37000000000070a00030ac000bc318222405ce0000000000a5851f6ed00013604380ad8f3d62ce920001b282ea00000000000000000b90c3000000051c80000001260001c4c1fb53c3ebb854000cf85118d799ae01214c400004c000443800164a6c500000000006605fd8d4f9fa94f2b5a23c000000000000188d000702973e0006925ebea9d3b0b56636000000000000035dc0006210002570000e2621db02c1020001c339500000002778941c0ec044538001d0c1e154b000000000000020d1443000000000000000000000000600000001be0e40000000000000000000000000000e80000000000dc20002cd20001de0310d2c00000000036902247b048826f54880003a10000304903598e390db00f90000000000eb920b068cd1651a3cc8001ce48012928000000de5e32000000052000007f80000004c09079d089f003436492980004ff0036ef0c81e1a000000000045000000000003b6800000026c00000010145be2e2aa6400000045f87d000004259990bc5b6cc700001560002035d11ebda73e630032cc2f14cc862894ea4468170002564bbce8f6661068e9a2ca0000000322a810001ff400000000015750dac010000001746000000000000006129824812ac3c933b14a00000001c529bc0000001680000ce90003f6c00132ae5a0002021910c15b59b4f12dc7a3255c8349427ea273000000000074e89858260000000e58b04cab0000000000000224265272a0d920201869e024b457b0a8fa62d600000006120002d34000000089cb5000019a55b0002630000bca0000000f42dc6c0615f92da1c3b80b7ddc78a6e3248001194102da78dac8469f305588080001f20ed0000ee60000000d10e2e40670480011e865d00014f8ba300021f9ac54be10691993e15f800016211680000001
  | 28 => 0x1688000000e8d629800129c00061880000000004c380005f00a41e50000bd6000000000090681f1b400003720000000000000d550002971c4e000086076000086e000180188e00050d0001d260000000000b5f8d0000000000000000016780000000000000000b346e4c00000000046bd7400000143f700001ca0000000fdc21ed6300000017220000000000000c21000267c0000000e8f1a1248c75603b3646ce6b50000c041e80006250aad3c0dd7c0c0000fee4eb2800fa147c00000000000001a6af2b03c546b0b5489548d38d3ebd5aa24d8083d276b3913d600018881a43a8da73e82ca016c0002b9b7f00005790001ee924e5b085cd22c0000ca19d228c5de0004d035740a08076cd321c000a980e39d9113e31b66b000052a0000001e80ebc0006c8afbd39c143aa3000145477b2a740003280004d1c00054000067780000003252f8a44424d0e351bb51254c1866dcb420ca7d7900000004f7c587100474000000000000010e000118800000000000016a800000070b8001bd40002681a30ea200000000003323e08000c797bbb550002828280b680000000000c9513233c000000000000000000000000df9d1c00067380016ea00028980015da536000352133247d0002454000c8a00000bc000000000271db209b306940006ccd0d0001e553de26e2cea88400061b3a732022aa5ea2c519b119a075075b3e4db700000000000000000001eeccb422e59934b42a3a5d4d695407c802c32935a42a91d162ab5c40000006290cb000000017b0dec92ecda1163a9a4223d33ab17505b400000000007fc0000000bb6c90015141ba2cf0ccec067d125c3c00000000000004470001e0c00000000000000008ae0000000a30e695d38000000cf4b6380000000004c192380000002f3ae25cba0000001bd17aa00031e8152498e1319f1b2003e16e16380016499904fb800000093f0532824000816540000000082b000000000000041a80006210005658ebc00000000000002c02e2095a55c00063058a29ecca6e8a00019d41be0001a28001b28a5951e40000008ff0000000e8e56115e1590000d29588a62db305341ded3e8656cd30000000000000000304066a46f00000014d60000001e580005cc5de000000000043b27a16147a51e5800000056500030a41f99b600008d4000c4d5e0151329098a2ad16dc48a20e02600009a8b2b38db1b994e1435f488fd18091900031c982700000ddd111fc000000143800000042f3195766000262189467a0000002a15bf200029f80016e27756da00000000005e8b770089b070003158b580002ab58ecaf40006fb1cac000b4300036dc98e9ca00037b8248af501684051ceb5b5eae1c9224e186113618a22a012708000dac5fd28814878dac9b08b800016254239e90306c620a0a20001c055f8d660000
  | 29 => 0x4242c0531589e82ac69d69a17e11b60000001a141885aede135a018e6d908d9df8cf84b000000000000004bd602c00000000026480000b353819657e20000000000478ac900000000000001fa8000000d06000000000061f51eb5d10fa48615b80000009a56e5b3e95f6000149759c00000047722340007f315a80000000fb800000191cc7c00011446c269a11b157800098e039000000000000023f00000003be80004e8eb000000017ac000000149d71c2df104394400000000000000000005868c4d4920000000c21bca000000000114806d24824bc75c0001ba8000a900001b52e4c3983217149a201152ea1bc39ed10897f366af78aa646a0000000fe2daa5ebba6440ceab4c7aacc000c114cd8001a989ac1ad89a542e5992c6b964f7a5a800005840000000000000000000000000000002100033480000006420c5a000db03a32ea10ac61500000005bc57505400019a26e46bc2cb582c0001d08000000cbc000190405b0005b488a54986f600000007584cb36a9bcc08a060000000000000000000017f40006631bf40007bc0a400000000000003aa9d626261a9828e0002a69f83918c14000349aabc54b0006e71248db5000000000117046b66f10e996a7b4060c0017e754f47ca9f4cc20005e797bc0008a600000e0e948650001f1c7660bc000000037000075c40010b800046205e4e500000000000000000000383100900067e14f60000000003698000c6b31613b94066010b30e7400043e800000000017e8001a2f52847a3b08edc7b80000002c8ecde7deee5c0012d60004ea9a9a3065b10000569a7f00000029c8444581800000027eb2c01b00000000000d72e484b4df242d07b17b2c6149986206ca0003e08000000d51000000000017c6a1000000000000000001c44be0000db530089119fb585629000012e37808b0003168008b64c3f395231963ada31c783ec074b842b6344cfac20100009c848ce320b88190b5a0bf00000000000004d4881402078c0000bdd13200000000f1d00245b8c38d8ea4000000000000000a419b25d632e2f69998fd1d479b00025a4000bbf2a28000000000198000000000014a14c40000221a5335400000000010b0a4500000023d3284237a8214dc152ae100039d8000b540a6000032e088ae51d8d2fa09b5a2b22c0009935b8000092c00048997040000002048f3029e95b0000bc40008360000628000bb88000f200003ef91689993bcd0100017f11cc00000014bcbdc770422a68c6577ca089818c0007430000000f924d115940000000002b4000000000000000000000000002dd03946aa0cb00000000a160cb4dc0003f6d458000000c784c400007d400045e00000004e44be326025a0b3b8d00000006f14e6000005600000000000001aa0000000816c3d00019196e12922a04e0c000000
  | 30 => 0x716d66e05e4b64985000000000000000000000002e4c00000074100024b4000000000000000024e00011d8000722000178b9b0e2e50b4000c1ecf623b9d3154879d0000168bd000000000000f0e3500000000006892402ea85fe5a64de09d802c4de480000007300056eb97d4369b90472f40d114c80293730ef80005d48eda32a17b0000eb4fa4cf388200000000000000c500000004c680017ba2c3000000000065f2c382f43ee0004f1ac1670300023f17440000000001450698e112792d3877a0005b90000d00cc075780011823c065b0000e4ee3280037e0b420005bb9ec55f41b31d2a7515e47554a31ae96a075318ac001af82636b317d6030b0c66100c5c9200000000007b7828000380c00000000028a5afc5854991602000d218002459d3c9606e31089abe094000000000000039188e000000058f800056200054e0000a935d900004d954060c42497709260002aa78cdc961300f0000172a70652780013b6c1e0bfd1d148a6b84d96e500004cf33da1ecc880002ce0000000a110002d940003f267f8000000b1e6f204c5218000421800000029e0000afc00039040722e96700f100033ac000551d58000000000005b941da8697bda3c000000b09000000109000000019c16cf6d132b00000000006ed871000000001980010a400037480000000000000001a080000000418b605950000d640000006b900000003936e19c200000000e4133928a000000016508205680000000be9541f4823c0005fa406a470000606a3c34589d40002de80000002340000000000cb03f5400192c0000000000000ded3350000000a605f0800182400042212c4bd85a508fb3b4b5300002a163c6b8ce54e4ade000020400028e8000604000390412a1c940a1b780009fa21cc1e20000004428000cc60002dc0001a223c4dc500019046e7b94800183443769bd17c000c7b3740294000df109638fc89811d8001b753be8b06b6000000094100000000007c474bb3a8b960d52f10415084189216841d80c22666bc000000e280002f53c80000033c00000000000002439c4ad956003d5b8ec0247b84454d077161402d585ce5c5b8faf07ce0ed0002ba6eca584b56aedfbc604720ceb7e8ae7ae0606848ebe3df20e1dbc2d000000022200000001c10001c285b5454113967682100020f111c11e0002e360000000000001b6600000000000000000000000a9500015780000001f6000000089600044b80003de0000000000000000242a8ec0003c30fc1db000093800022f40000005760c80569d2264d0000d040000000c2c0003b38001d2d4080000e0afdc59800000000000002bb0000c1c94e000000206400000000020ec67f4ec1b921d160f0006e2bab09482210000000244000000128800021580000004485b1d13000188c0a32290d3525c3b7b77986
  | 31 => 0xe00004ad6c781f4b8495d64a214c00017a0000efefde0000001510afe1540000001aea049d1a8a0808282a0d5a75d1ac3fa1dad004000aca68f95a4980cc3b51000000095273e380e00000017800003baad6e7d80000003700fbf63000000009901d0bd500033584a8f2800000000000001cf000000019800000000015620004c0d8e8000b9c00000009a615d00000015ae00009f155947e14900027149581a95fa1d9c84829f1ffb9581c8875673312100a0e88360000000d2000000019725a7914000096e084393033965eb7a0002b44000000000000000018e25b3994f38bc10e000001bcbc5b05c0001872142d1d9340000006b7acf42a69af08680013c40002088000f242e800000b20005d2bfc0a9d55aa933200000ecc1fb29516483da08c29d23d5546c9c729a0b5653a620da15d9ca46809c610d40000000000000000450063000000000062106fd974d850000fcd1a30000001da40000000000001d38bce4e322ed970e956bb05f46c4dbe0b60ddc0aa49b36d05700000000002d9b3ce1370002fd8f08ade1ea9fd965c2730e1a054d843d174380017630004100000ba68f13ec18a60000000000d5cf5256f000000068500054114b90f8b338000000000b1c00033d000004e00015ea000000000000000019d000000000000000037540003990000001800e9a392a87449d000000191c000000000000000014be1020000000000000000ce4e0091d000000000060e998e000e026ecb87400002a986981c2be068c7dc0016460003c6b0984f9de700000000000000001f7d8be2eb2be01e93a48cf0e9a0a40c17dc000066ca2a69b31500019ed000090344995492870680000006e000000000000000000000000d3a800302800000000000000000000e0c0012b90000000000dca000328800000000028518820000000001190000cce1a040000007ebad5c0017c64a30c8000116aba6849325a00061a000328c0000005ee0000000d95233aef54ce4e512ba4f81690000002eb800000045b2c045205f7000043a000000294800000000060c09119880000000000000ea080000000000006ff00000000004cb8001bf400000036ece48b6e5550030aaa00067180000007d496080000002e450719f85180002f680755440003cf29c47162070002a980000002341588000105800000009104d3558ec4046e620001ab916e0006e25a5856600073ab02474027012c25e15769cb0db0da594411c56abad000000000000009c664b0b1800000000055c000168400022132c800010871d8000b0241380000012ec0001a7800077ed7b6a0608c000a5155f1999a1c9578000000000787149a79400000027a800010c0002b0297800000000025dc000691000063c00070c00000001b40248000000eb00000002b980007cc00000014647ad1730000000ab
  | 32 => 0x6de000000000044d000011a000000000124aa06390ae3c0000000000001311c2352b9d89d741d61d84e9144eacf73951e4633b980001c7167bbfd20c00014940006b5366c0000003d50000baccdc0003a411ed8dc0001a98c268780000001ce60006e4000000000000014040000003b902b8000000210b5296f23f65a407b967215e0003a0c00035bb6d86600002a46200000000da126b8001a8c267000000008800000010940001df0f22088fe04fe18a8000000000000130c0000000001c51c2400008b0000000000000351400000054918c85c28da0000000c78b26800000028ab317408e6800000028b00017a600000030d20002d563caf8079c4052f9b6b936f2b21b61c6508c4260000f5c8dcd810000aa9bcc030800000000010b8000000000000038800193200000000005b28a20ecb2940002059a32f9c00000059200008320000002ec2000000000000176cdca0000000000ac538dc0000000001a0c000522000000000000000000000002a72cfb99b280e7c0000000c3fa4c428153ebdc87a70f12e0db934286b000000000000006c4000000e1b68c000000046300000000000000078ca91680002beaf2cd3e1034e1023bc94c500002b4855a24816b800137e7f892469f1c9c0006ce85eb0f42872ac2c2177cd002311fd110405600032dd74f00067ed17064e0000ba072c552d3ccba000134499d4fc364cf6a8ac32a95c882800012ca0fd920d271511415bfa10e367b2cc0000cedf322cc0000005b7913c00050646293fc95c97246421fcdf22019ae800000097e0feb1c40007d400000013b8bf0587296d87064c589c000df68f2000000000071e1efc0013ea97300000019a38324cf19e89d18f09c48ff12ca0000001ecd6c53d41b98d200006a38f139b00fe3d003e08be0b0185327b9d1caea0f3d200001a40000000f1c000deb0c582a974821490bd9d6f970002c99d2400032200037a400045e00000010745966df80018880000000001737000000035c00028e25a89a00000005db9eba00002e09980000005fb3d100000003fb30c2a0c66271d0003198000000000000000000000000000000001798978000d9f000060400056e00000015b00000002c6e00000006789f53b2cc34fe0ab045e83934651356d9d5a50016380721e32f2082c164c6706c1916da60730000001c1eae500021741b58376ccb5340b8a204a398882781091ed901c00000072f225475266d000000000022b5944000000000000000000000060b8000724bab000000108e00070f8000f101f172200000001b7607000000099400027fc000000000000000000000000000000005af363800070928ba9a45680000978f6990241f2d72cba00078535e1be904ca31ee80001a423f82d19ddefcc369aabc000b08138218b4240002c600038
  | 33 => 0x3a5800000018800000000000000000a8300025cc0000002c00001dd80000003ffc000000000622800000000000006c80000002a52579aa825f0000bf1196000303172121493d000000070e0003662e5c0000001d18001cda1af6402b8994c1cfdfce6ad70e00036e0000cd2ae78000000000206d208166b1819f69212042d2c7e1bfa36545890f0002ba473081e3ba00000002135a9b2a479ad624aed235236c575afa95402656320400005970006acb3a18a86170001a28000000000000000000000009d55b4000000271170cde1308800000000075fa5d200a000584573256c0002dd80017990000003a145491ea12b05a8d32bd86c398cd9e1cc682e8679bc0646e2da5cb95c8d874424d074cdb500020e000026d354016ceb438061d84001a87c6057b4325f6b9e4a8b8e97bebb434080052e7d1a3f031d1866db823900016cc23b255800145c00000000009fa4530001370000db631a8cd8000be24cd1470efebf2019198850c2390001c08a3ca02000000165439380000000009ec0038000df500000019e4000000000000000073500036c800079825927216408022e791154a8413000000162a8e859b0d1a00000053f24ad26050d55d0000acc000000000000000000033ee0006ec94d0a4600073c0001270e1a5c60200bf828e00075e80009709b20000000d681dc16e8000000539ea9aee000000044080015c60000000001338a3c00000000000005bb00000005b39351500ce20000de00002e01f56e4939e000000000292d811afd5b0c000eba00000000014e6a500001a854ecb6d523213c7dd09e54d000ca04d562ff0f48a8e6bb5b6c0000005ba01f321881c000638c000000ea8000258c000b9aeb200000006628000001d04a56559000148e0c11760001c9e487474521e961a65056ad18dbe8e00000001c7a0000000000000000000000000032375db9a0000a306a580018b9a381c8868000000070c91a509a5e66d5810c000000476247ca7a00000000000008130002ee800043e00010f72526581fc80009b200000016bc10a000000000057017801d8a6c0000001f3032600000000014b501e1765ae8d4400032680027a8172ea930952795f000014e8001be86af32281e4dc40465912bd174ab25821da510cc50f000160000000000000000000000000000a9cb215f229d47ba5f7832e35167e000000012c1345dd19540940009891f02278000000000105683a56a3d3800111475b145345db4a0dc68e255579ae7700003467787c2000000063edf35ff8000bd70002e3800000013a5a49c5825ca19000000000000073e8a956c64910001a540000000002a1c0000000000001a0ab64000000000000000031700000004c22df193e00044e09540002473990f7893e43200005640000656a7a2180a6e556668001a2a0
  | 34 => 0x9500000001c38187169961800000069503b694a000000197811900026480013740f749b95360000fc6ff81d923c7eb4fda4b0000c6940eb4ad7d02fd0003b00000b7d000147409fd8869600000000001728000000b670000000be100035180015be34e7593889c4686000007992748e375030e861c9fd00d28a0000c6a000000068b00000000016fc00000000000000004262a3c0000003013474cdc46027d40000000003bc6f6c0007e4000226c0103d85a9163b162cbb2e000000002890a300014da0003e596d1ada9b56dc40007de62943f00000005892198000b92000150c52800000035630d964300073800004a400000000000000000000000e8a000000357100c200814a9e40000000000000000203ac1aad57600000002a348b0a208138000972e4c24e8a70e0800014b8d04b6900022b22a542850b1bc8b48100000000171e00000036a03014660001c28308000a52072c0000001e51ac1efccb8000000000000000037363a4e1c00052c17a4040a5300000003e000000033754fe0a711f19400000006c4b85800021f167b634d4a35a0073a603b71ac0000001757004291b2454ccb4b3b72fb4e9e00029db4f80484ca4a9904800000022a81acc1cde86c5135400053525e0001700b99258e8c4f7c9644d3800000009c3eea3945f2cb15819430fea4982891254000e1000006c0000dd873d00014183e1f508ccc88238108d18a07da0005b625e83d0284035cfac0000000f580017190000000000000000140a2946a476a12896fc00000015ac00022800000033151120340000e3965b13d365869d5a6ab614d4b2491073b00000019dcbd42158eac000290a5000000000003ea8cbaf2632f624427c0006978000001a8e7343ac95440007f90000000b3039700000011aa8f62010000000d3042ab9814161b50002049aca5770003a244fc0006ac00000001b7c0186f451911023680000000005c0800034a37a71f2af149c350262800060000000000015c86f2000243800000000000004549d14cc000000000000011d40007e73c497c0bed5bc59d000000047300005955ce00054300000000003751890664e0a2000001448000000359a0000002ea80000900000000000000000756a6f8b52e3700000000000004690000b97bcc0002d6440000000035f48814f460190e4d7c000028a1cd46f2e94ab63e1d6add3000391459068d0000000000cd034f00000007b84b880000000000000000000baa80000000000003c780015b600000017100000000000000000b7aaaf80015360000000000d1ecf748d000000000069d87144a6547b1b83b953ca781b212fc04d0004fb00017160000df1129d66b0237193dcf9e3166ab80000006d24b8000037656d74d800082e0000003a311de91710e38180001520000c620006d01daa6c2fa167f4020
  | 35 => 0x104a000000006c0000004338000000000000261400078001a800000021700035e8000862000155c00098600000000008270000001b166ff0000f840009d00000001c8400000035ad4847e9c34000107cab463b8001582d973e1af482d60000002460eb80005f28001a068fb3d412680000000000000c68000000086400037d6d6172a9e61d03a424892046f9cafa15c00015847e800000006e4ac040e4c04db5ba6b355e6a05438248dc72000000000170a0002e7000000014aaf1a42495490d0002fb11428d75d4c000c46019589378871a0005c1a8540001c200000000002b0223000082a97d800310c768ea30000000484c374f6937484eb82290a7c460c000738c8583740e07070a4e0005f6480800000088000b80003aa0000d4430c0000000000000000c1f00023740000001dc0d463189a64360ca35860db3cb459c1ec000475b020106d400b228adcb0c73273b381d6e63e000000000000028498756c20000002aa0000bad000000000091d4c8b0f0000e7900000017ea97c90c0001a33c2d1048cb6000000593800000000000000000000000000000000ea20000f649043262180d1c1ac70b435000144a1fc5cd01f82320fd68580000383e21f600000002c20000001912e6700023248fe00068800005ea4ad800046073679a0000000000e4309d8b80606000254a12d57a9b44a02d28000ddd2d276f4ace0004798000000d235a39d81beaa2249e13c58de38422c8ea10127c8c55000000058b6461fa13b47b20000000aa5871049886ca96cfc91ea26143e00000000000920005bd8ca4deec351a480a80004f9716a1dc00000000014fe00068626315708404a60000ed9cc2000232b070a326b26061f380008584251dad84acbe4da60c51e0dca8000000d8205780004d19969e92ffb4fd751cbd6b00000000cac0000000774eb66879ad9c02000649150a0000003ed182097445d1ad706ce7eb180e3c000e248ad732188000054961200000005db6c11184b567b62aa21a40007ca80030bc9ec5aab212528728d05dd7a2c849a45b0000000bc07db2cd0c3d892ba021a25ec9b00004ba800000000000000001ce33c417ba519c2a4d00000000b567739b00000009bb58000000000002fa46a0000e1a00000000002ed2c88001510000000000000019a05c40005e863900692eda2800050f1616000a770000ca044a14b397c0014c8
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x14310d10d81821c14310d10981821c14310d109908750e6010d10a908050d6010d109908750d6010d10a918414d6010d10c938750d6010d10a908750d6010d10c908750d6010d10a928550d6010d10a908550d6010d10a938250d6010d10ac1801c96314910d07741cd5214910d04741cd52149109448798d5214910d047498d52149109448758d5214910d047458d5214910e056458d5214910a63865496014910b40835496014910e41635496014910a908059043cc910c91645c043cc910a2684d9452cc910c14651d1534c910c44651c9534c910c44659cb434c9109c1809cb434c910a1485590434c910a9080590434c910c91645c0434c910c14659d2324c910c50655c2324c910a2484594520c910e4053149600c910a50854c9600c910a60854c9600c910a9284d8e63d4110a938650c43d4110c90641c143cc1109c1821c143cc110a1685d90438c110c93645c0438c1109c1821c1434c110c1475191324c110991841c1324c110c90641c1324c110c90649cf504c110a928690e404c110c90641cd404c110c907650d404c110c1675192304c110c90731c1640c110aa1821c1640c110c91645c0430c110ac18010d620c110a9186d0f400c110c9176d0f400c110e834358b400c110c91645cc400c110c917610c400c110cc173588400c110e8043588400c110c16651d1300c11089487591300c110c8474589300c110ca074589300c110992849d1300c110c91861d1300c110c92651d1300c110d12651d1300c110c9074d91300c110ac182d91300c11099087991300c110a9186991300c1108d087591300c11099087591300c110c9387591300c110a9287591300c110a9087591300c110c9087591300c11089087591300c110d8074989300c110e8164989300c110c9074589300c110cc376589300c110d8074589300c110e8264589300c110e8164589300c110e8374589300c110cc274589300c110cc074589300c110e8074589300c110c8074589300c110a918418d3088110c907418d3088110a908458c3088110c917458c3088110a908458c6388110c917458c6388110cc1635c86388110a908650c4388110c917650c4388110b40835485288110a448359452481109a1849cb3048110c907418d3048110ac0864c93048110b40854c93048110d80744c93048110a508558c6348110a908458c63481109a1849ca5348110c60655c85348110870855d84348110a908650c43481109a3845cf62481109a3845cf5248110c50651cd5248110d82745cc5248110d81745cc52481109a1841d632481108e0865d13248110960855d13248110d4075dcd3248110b8284dcd32481109c28794d32481109c08754d3248110ac08654d3248110d407554d3248110b808454d3248110d817410d32481109a1849c83248110a61829456008410
  | 1 => 0x391a861c14354043c1a861c14354043d0a821c14354043919821c14354043d09821c14354043909821c14354043d12811c14354043d11811c14354043a18805516010f32c61725c46055132c0f76dc95410d32d13711c15410d32d10711c15410d32c19861c15410d32d09821c15410d32d12811c15410d32d11811c15410d328c9801c96110d32a18805516010d32b108055043d4532b10805504314532c31645c05114132b0581151424c832b0980151424c832a61801c56215031918805d54310f21a19801954310d21e05544c9610c821e055454d620c421d22545c83154021d21545c83154021d42535c83154021d41535c83154021961821c54354021d41325c43254021963825db3154021961829d33154021961821d03154021d42735c83154021932849cd2154021b21848c92154021d40734c92154021c1a765c05450f30c0c545c86050f30c52735c06154b308998790c6050b30a1880590544cb30c53655c0614cb30c19769c35410e30d11719c35410e30b108050c4354630a24845886254630a61829456008630931801c56215130c25625c46215130c29625c06215130a1a85d906050d30c30545c0615093081d87150604c930e1054d84604c930989821c14350130c18631c16255030c0c635c86055030a19859916010c30b08805904354830d0a745c04354830c31545c0614c83081f87d974350030a0e86d0d5250030c19655c04310030b098010d5210030c0c645cb544c03081e869d9544c030a0c86552524c030a0c86951524c030a0c86551524c030a1486552514c030e046454a514c030a1486551514c030e0464549514c030c90645c7634c030989821c14310f20a8880590434cb2081c875954310e20a188550d6010e20d11435c0435462081c87591530c220a0c8454d620c220a188550d6010d20a0c85590434c920c89645c0434c920c60655c0614c920c0c75191324c120a18805906454c20919851c14310c20c19651c14310c20b108050c4354420e056458d5208710e42635496008710e41635496008710985821c14310f10a908050d6010f10e056458d5214b10e42635496014b10e41635496014b10a618214d6014b10a5180196534cb10a1785590434cb10a9080590434cb10c1775191324c31089487591300c310c8474589300c310c19651c14310e10989821c14310e1089887591300c210c8874589300c210989821c14310d10a188550d6010d10c4475189324c510d05745cc5248510a268498c5248510d41735c0524851089887591300c110c8874589300c1109a1849cb3148110c60655c83148110ca2435c86050d10a44825945310d109c1821c14310d10916851c14310d10985821c14310d10b81821c14310d10c91861c14310d10992851c14310d10d12851c14310d10d82821c14310d10991821c
  | 2 => 0x3680056c0000000002380000000000000eb001702b8004e000001533480075800000008692f00000088000e000214000023e000000000000000799148a1be240060022e0000000000001ce001542518c0001c0004000000000008c980928442a9d00010252820000ab5e8003947889000180e483058258245f00e88000920165c8005b8000000000000000008d110561ba3100000000410bb00000001dc0f5da0024012920220005983c000003f0fa0023070800000006c9ca75000810000a800001c000000679fc4d0c0871ee7800000000468b8000006aa10000a6000008600078a466e000001d80008a8d916320004c000266164a800020000001a00000779ea808ca0023c651ec001a78a87e000a8544e85003b000002802e0003a6b8a13b000000000005c001f083800330d0001121dd21495a62d89e6189b271f4000e0379bc4b0001b9e47a1468510e00000661083083626000479523b90c1185635052541680021e1c0f84d93e00126238620d01050800401ff0007600188000e2000f40007c15122398dc00084001c800000000005d4ba57400000000f803000a3000002c0006420a360e31b000000003c80000000000008e8f051000889ac538002088048c74000f6358a20000090800000006d0000000064a006a000000d5000001e9c67f83259042001d2000007e89f8196200048520fe5a8002d4be000a4898000b00c670003bc000005a5d1956581f0000000000000000785e711f2001560015a53000820182c800001f65b00a0012821a124c80003450570126298223160000001323b001a5000000009a000b4730004e8003c4002b00000244000c60a0720c0140751c7e06a338646d866461245f80269026680753a88f2493c00000610001a0003d5b04280071d5e13978000002f19a0118e68a3d8b12e5d906000000100100003014000100200005008010100600c030040700000008010080000800004070080000012000000100c000010140004c01008000000100401010000040200c00010010000500000000000080401c0002400000000000100000010020040400404058000180000000024040180103802000010000101402004000100200004004020241601001c0d759c86050c43c0d755c86050c43c15759c46050c43c85729c46050c43c15755c46050c43c85725c46050c43c91435c06154843c52735c06154843c51735c06154843e05435496114843e09435496014843e05435895114443e1143545601444388d821d94394043989821c14394043a908050d6194043989821c14354043949821c1435404390d821c14354043b09821c14354043b11811c1435404
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xc0001a0e2c0112c5c9800000000004801c1e08a903a2608d1f504203224f8c361520a2b60bc0460110e067908000109be6020001840801000ca06488050d6194043c80c150238286a8087901826047050d5010f0130cc10e0aa08699604619811c15410d32c80c1302382a821a65408955917010d324825032440286b008788602595821c14310e10c40c35043828621a21881866087050c434423032443a8730086884a06488050d6010d10c0243ac8b1aa4292212409858d525805244340108b1aa4b00a488610195809cb434c910a084aac8b808699221880646087050f304428252bb22e021c6088424660641c1324c110c4039b04382c8182218807460b644c0304421252f43ac8980608852025d64989300c110a404bcc8b12601822148097591624c03044212130ba2c61844088520251635c863881108484c2eca188710221880861d1324c1204432010a3a26498240886401d684dcd3248110c20430eaa9a649022190075211534c9204429012cba08699240885402557410d3248110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 29
  | 6 => 1134
  | 5 => 6283
  | 4 => 3777
  | 3 => 294
  | 2 => 37
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
  | 7 => packedAt gbK7 (562+((h/14+packedAt gbK7 (464+(h % 14)*7) 7) % 96)*6) 6
  | 6 => packedAt gbK6 (36858+((h/520+packedAt gbK6 (30618+(h % 520)*12) 12) % 2267)*12) 12
  | 5 => packedAt gbK5 (274916+((h/2583+packedAt gbK5 (238754+(h % 2583)*14) 14) % 10228)*14) 14
  | 4 => packedAt gbK4 (203819+((h/1442+packedAt gbK4 (185073+(h % 1442)*13) 13) % 6911)*13) 13
  | 3 => packedAt gbK3 (18750+((h/111+packedAt gbK3 (17640+(h % 111)*10) 10) % 535)*10) 10
  | 2 => packedAt gbK2 (2705+((h/13+packedAt gbK2 (2627+(h % 13)*6) 6) % 55)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff83fffc1ffff1c1c78fc7ffe3fff03c09f3f3
  | 1 => 0x7fc1e3fe0f1fe3e07f1f8e0fc707fc076cd9c
  | 2 => 0x7ffe03fff01fffff801ff00ff807fff870e1f
  | 3 => 0xf800003ffffe003ffffe0000ffff8003f80fe0
  | 4 => 0xffffffc00000003fffffffff00000003fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x108840044200020000824122209110880050b1
  | 1 => 0xb1194448c642a04a0390c8466423258832c594
  | 2 => 0x4220889108254014c801120889044a31850a0a
  | 3 => 0x6072952214a064a755240010d24e0312d80f40
  | 4 => 0x8443180398c98939a649a49c00080c236fa000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0feeaeae0, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_37131
namespace PEqualNP.Outside.L_meta_37131
open PEqualNP.Outside.L_meta_37131.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_32 : Interval gbAtlas 2 32 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 37 := (concat bgb_2_0 bgb_2_32)
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
theorem bgb_3_256 : Interval gbAtlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_288 : Interval gbAtlas 3 288 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 294 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128))) (concat (concat bgb_3_160 bgb_3_192) (concat bgb_3_224 (concat bgb_3_256 bgb_3_288))))
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
theorem bgb_4_3744 : Interval gbAtlas 4 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3776 : Interval gbAtlas 4 3776 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3777 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416)))) (concat (concat (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)) (concat (concat bgb_4_544 bgb_4_576) (concat bgb_4_608 bgb_4_640))) (concat (concat (concat bgb_4_672 bgb_4_704) (concat bgb_4_736 bgb_4_768)) (concat (concat bgb_4_800 bgb_4_832) (concat bgb_4_864 bgb_4_896))))) (concat (concat (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat (concat bgb_4_1024 bgb_4_1056) (concat bgb_4_1088 bgb_4_1120))) (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 bgb_4_1376)))) (concat (concat (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472)) (concat (concat bgb_4_1504 bgb_4_1536) (concat bgb_4_1568 bgb_4_1600))) (concat (concat (concat bgb_4_1632 bgb_4_1664) (concat bgb_4_1696 bgb_4_1728)) (concat (concat bgb_4_1760 bgb_4_1792) (concat bgb_4_1824 bgb_4_1856)))))) (concat (concat (concat (concat (concat bgb_4_1888 (concat bgb_4_1920 bgb_4_1952)) (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 bgb_4_2080))) (concat (concat (concat bgb_4_2112 bgb_4_2144) (concat bgb_4_2176 bgb_4_2208)) (concat (concat bgb_4_2240 bgb_4_2272) (concat bgb_4_2304 bgb_4_2336)))) (concat (concat (concat bgb_4_2368 (concat bgb_4_2400 bgb_4_2432)) (concat (concat bgb_4_2464 bgb_4_2496) (concat bgb_4_2528 bgb_4_2560))) (concat (concat (concat bgb_4_2592 bgb_4_2624) (concat bgb_4_2656 bgb_4_2688)) (concat (concat bgb_4_2720 bgb_4_2752) (concat bgb_4_2784 bgb_4_2816))))) (concat (concat (concat (concat bgb_4_2848 (concat bgb_4_2880 bgb_4_2912)) (concat (concat bgb_4_2944 bgb_4_2976) (concat bgb_4_3008 bgb_4_3040))) (concat (concat (concat bgb_4_3072 bgb_4_3104) (concat bgb_4_3136 bgb_4_3168)) (concat (concat bgb_4_3200 bgb_4_3232) (concat bgb_4_3264 bgb_4_3296)))) (concat (concat (concat bgb_4_3328 (concat bgb_4_3360 bgb_4_3392)) (concat (concat bgb_4_3424 bgb_4_3456) (concat bgb_4_3488 bgb_4_3520))) (concat (concat (concat bgb_4_3552 bgb_4_3584) (concat bgb_4_3616 bgb_4_3648)) (concat (concat bgb_4_3680 bgb_4_3712) (concat bgb_4_3744 bgb_4_3776)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafeeaeae0feeaeeeafeeaeae0feeaeeeafeeaeae0feeaeeeafeeaeae0feeaeeeafeeaeae0feeaeeeafeeaeae0feeaeeeafeeaeae0feeaeeeafeeaeae0
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276808416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37131.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,4]⟩,⟨.or,[0,6]⟩,⟨.and,[3,7]⟩,⟨.and,[1,2]⟩,⟨.or,[4,5]⟩,⟨.or,[2,10]⟩,⟨.and,[1,3]⟩,⟨.or,[0,12]⟩,⟨.and,[11,13]⟩,⟨.or,[8,9]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276808416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276808416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37131

open PEqualNP.Outside.L_meta_37131 in
theorem PEqualNP.Outside.L_meta_37131 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276808416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276808416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
