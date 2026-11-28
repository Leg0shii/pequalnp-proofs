import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36282.Model
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


end PEqualNP.Outside.L_meta_36282.Model

namespace PEqualNP.Outside.L_meta_36282
open PEqualNP.Outside.L_meta_36282.Model
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

def SBf (j : Nat) : Nat := [7, 7, 5, 5, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36282

namespace PEqualNP.Outside.L_meta_36282
open PEqualNP.Outside.L_meta_36282.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x344068000ace00000128352602222204024542119714007853a086283c593864c4c0093284f920050a8e00805873668300054300200128b2c4ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1c818011979a080000000b9a800000001900000017028002180000000022001024001b800c1d258b0c8000141f000018801580000eaaa600098000001496121100000a8e0d012a2c0896800000000000071f92a1a0998000038005a10d800000000f00000513a3802b8000000a000000000000000f890000000400001c24802510800000002913002ca2801e8007a7a680000006801b00000028a8008000201d83298015049e002b2706002300400080404101408040400042004040000000c000c0c04080030000400027ca5a1cf55243b7a92876c5250f3ea6a1ebd49439e29287ac5250e58a4a1cf950439ea9c853e5290abca6215754c42cf298853d5310b3aa6214754c429f29085ae5210a7ca9994f55332cea1e65ac42ccaeca3995d547329faa4653c548ca7ea8994f15132cea1a653e540ca7aa8196b10832b7a92836c52506bca620d754c419f2a6633d54cc73a8798db94b31b6a96639d434c67ca818cf550319f2a4433d54886bca710d754e21d6214433f5448678a890eb10821af29e815d53d02dca5205b54a409f2a6613d54cc33a87184f950309eaa0619d430c2dca4185b54830bb2886175510c35885904f952209eaa4413f5448278a89057d4d20ae29a41ac42482eea2905d145209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x2600078002c0003a442a000028502c1c29820c1a212e6a048058504e14a201030c6254c42a318943cca8d6310b32c910a51ccb15435473287195434ca2d6510832a318943cc70d4354b31a3189434c62c6255031a358c428870e5310a218758c544868d63108218b18954cc28c6250e30a3189430c30d4354830c550d510c28d6310b208758e548828d6310920c314c42483244214520
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xa811a000008282b988528e65411c9435473281aed2988510d047250d510c206bb0a621241415cc4214520
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 5 => packedAt s0K5 (788+((h/14+packedAt s0K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s0K4 (2670+((h/30+packedAt s0K4 (2430+(h % 30)*8) 8) % 172)*8) 8
  | 3 => packedAt s0K3 (998+((h/8+packedAt s0K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s0K2 (302+((h/2+packedAt s0K2 (294+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 2 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 3 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 4 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x2004088824020000a41280444022914810d095
  | 2 => 0x451891064894a12c0a852429921422b146264a
  | 3 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 4 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36282
namespace PEqualNP.Outside.L_meta_36282
open PEqualNP.Outside.L_meta_36282.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x320079200013a3260000038000000000a8a001802200413243a000023e004000001580020000000110970068c0e000c00050000250000d80163000500a4000001c000005801e0000011000069400a8020000000900000010002043800810001000c000ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3c803000386200000200601c840000a626aa0c96524400a082000000000000003a0014009aa2644a2e4c7c20042a907640945eac0a46749eae280e560022162c004e10425a08507288008a00067a5898006cb21a24686e324812b01e18006600003e0000a48c009ca88678000034008e366a7e54925c700e40204000010f0600100000028e00306840800180240c10102027ca3a1cf55243bba8a87745150f3ea6a1edd45439e28a87b45150e68a2a1cf95043bba8a85745150abca6215754c429f2a6653d54ccb3a87995d94732baa8e659d434ca7ca8194f550329ea9c833e51906bca620d754c41cf298833d531073aa620c754c419f28883b6511067ca998cf55331cea1e636e52cc6daa598ed107319faa4633c548c67ea898cf15131cea1a633e540c67aa818ed104319f2a6433d54c86bca790d754f21da20e433f5448678a890ed10421af29e815d53d02eca3205d546409f2a6613d54cc33a87184f950309eaa0619d430c2dca4185b54830bb2886175510c27ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb2884175510836883884f952109eaa4213f5444278a88857d4d10ae29a216f52442d8a4886d10510
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x91a02a00001210088aa16006026000b20014b8861e70ec0c40008204700024146946150f32c550d51cca946150d328d185540cb146154c41a518543cc70d4354b31a558c41cc726521073187195434c6356510431a558c41c871653107218758c544869563104218d18554cc2946150e30a5185430c30d4354830c550d510c29563107108758e54842956310510c514c41443245210510
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x280001180208028238a86a96638158e521073182aed2988390d047150d520c20abb0a620a218158c5210510
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 5 => packedAt s1K5 (802+((h/14+packedAt s1K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s1K4 (2640+((h/30+packedAt s1K4 (2430+(h % 30)*7) 7) % 119)*8) 8
  | 3 => packedAt s1K3 (998+((h/8+packedAt s1K3 (950+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s1K2 (302+((h/2+packedAt s1K2 (294+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 2 => 0xf03fffc07e0fc3fc3e0ffc3ffe1e07034e7ecc
  | 3 => 0xffc1ffff800fffffc00fffc3ffe007ff8f8f0f
  | 4 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x20800889100200008a1280444022914810b055
  | 2 => 0x658c91872494852c1685a429d21432194656cc
  | 3 => 0x831522120d29225541094a82a54044b28b0b0a
  | 4 => 0xca29c4244981ab9a65a0622339996023e00da0
  | 5 => 0xc31873871ce33e3b9ce7330311180c3fde000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faaaaa00faaafaa0faaaaa00faaafaa0faaaaa00faaafaa0faaaaa00faaafaa0faaaaa00faaafaa0faaaaa00faaafaa0faaaaa00faaafaa0faaaaa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36282
namespace PEqualNP.Outside.L_meta_36282
open PEqualNP.Outside.L_meta_36282.Model
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
  | 0 => 0x3ffc1ffe0ffff83fc1ff83fc3fc0fffece333f
  | 1 => 0xc0ffe07ff07c1fc3fe0ffc1fc3ff078173cdcc
  | 3 => 0xffffff80007ffffc000ffffffc0007ff83fe0f
  | 4 => 0xffffffff801ffffff0001ffffff801fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8244451094110808d092a124064254a4461115
  | 1 => 0x9648c32484a129415285a50c4296150c52c54c
  | 3 => 0xc910a0d294a12d421094a5aa80c2259816e0a
  | 4 => 0x28a21049080a54a6252042133128a011a80aa0
  | 5 => 0x30c39c71ce739f3bb9ce73822230c461ffb000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeeeee00eeeeaa00eeeeee00eeeeaa00eeeeee00eeeeaa00eeeeee00eeeeaa00eeeeee00eeeeaa00eeeeee00eeeeaa00eeeeee00eeeeaa00eeeeee00eeeeaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36282
namespace PEqualNP.Outside.L_meta_36282
open PEqualNP.Outside.L_meta_36282.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1ffc0ffe0ffc187fc1ff83fc3fc1ff80ce773c
  | 1 => 0xe0fff07ff07fff83fe0ffc1fc3fe07ff7389cf
  | 2 => 0xffffff80007ffffc000ffffffc0007ff83fe0f
  | 4 => 0xffffffff801ffffff0001ffffff801fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc244631494112814d093a12c0644b48c46331c
  | 1 => 0x4a48a12084a109015284a50442941524528145
  | 2 => 0x8491440d294a12ac21094a5aa8086259815e0a
  | 4 => 0x14a20849080a54ca2520421331294011a80ca0
  | 5 => 0x18c38e71ce739f73b9ce738222318461ffe000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeee0e0eeeec0c0eeeee0e0eeeec0c0eeeee0e0eeeec0c0eeeee0e0eeeec0c0eeeee0e0eeeec0c0eeeee0e0eeeec0c0eeeee0e0eeeec0c0eeeee0e0eeeec0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36282
namespace PEqualNP.Outside.L_meta_36282
open PEqualNP.Outside.L_meta_36282.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x8437c53086fca410fbd0821f6210437e51087ee8210fd10421fb98843f431087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5205f94640bea8c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730fda0661f840cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa5185f94630bea8c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c2fea2985f14530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f719641ed32c82fca3905f54720fd98641f830c82fea9105f95220df2a4413e54882faa9106f552209eaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620fb28c417651882faa3107d54620baa8c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f719241ed32482fea2905f14520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea88417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb90e21f421c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd20421f940843f661087e0c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443ec62887d4c510fb90a21f421443f480887e50110fd98221f830443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42f7a1285be4250afea2a17dd4542bba8a857c5150be8a2a15d14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa8265fb504caf6a0995f14132fc2826578504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520ef90a41de214837e519077e8320fdd0641bf284837d50906fea6a0df14d41df21a83bc43506fea4a0fbd4941b7a92837c52507d8a4a0db14941dfa1283bd42507ee82a0ef90541bfa82837c50506fca820df94c41bea98837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc6faa998df15331bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf28463fa508c6f4a118df54231fca846379508c6fea898df95131beaa2637c544c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fba0e43f441c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f6214437e51887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690df94d21bea9a437c53487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea9
  | 2 => 0x2b6001211ca0ea89c0019b00000057800000000549f803600085800000000020b20002f4880003c2320000000002f8090004628dc2b12d00049400223000298001853f48d80009326e0003d01810c92c078000808a4ae80017e050ad1281da8b4000fd20a000dd8000000000000000000000000272000870112100008d07c4904c80023800090c1383a38e2a043a623c423c0000000081c00224370000000441c6774001791ec1a00020d00057c0016e1c08a0449b5310844fe9e826869855a412de1ac0000039c6a87a873070000978004c6001110000be0012d0000000011a80000019d0b1ff000001131ab4600e4001382a66cd1911e3440000000000020c000000002891e00000000000000000000988004ac4a421000000000ac1fb000000489711b2000000001580ac99800000454001db34a3b000000000084ea000000000bf92e12c014e90d20aa0280001e28289510002000940001654026c51600049a2c0608003cc79030a4e39a944552330002600000005a000000cd20e80cdc80014600000176260000000a71ca7590aa5d46885ca212b1f02110c246000434a503d0fc2202499d398118c00660005b07d800000818be92104400123800312018000dc000000ba0f3000294d00ae140388b025e27439c181c500069c0019a0001e4951350009512fa53000000000970001640000036020129000230000db8002787a400000000000000000000002500001c8640015e3b8000000083be0000010f0009140000000000062000000000df8000000000000000032ca593d0e2490370000007400025c0005ccc78ce236765000003ee00000000000000000de314000000000007d0f614d000270a7800000000f7a1f00000000000000820228ad4740b89d95c2e45dd24a3d000000038002a4000002391ac0003b8000000000000000000000000000564001690a605c1b140000000000004b60000007f27c00000000000000e30e80005848c9430546f08b8000006b0e08a400059c698002085ec5080200c0202001010040080000401004050080200c0100c020000200c000000401404008030000000c0701c010040001c120080200008010000000000c00008030180101404004030080b00000018000000302c0800003004000040600c00018000000000416084010140d0000008c090000500c020000000000000000000a01002010050000000002000060100400400000050040802001008030000200c0002002010010240002c03030000000100801004000000000c060140200c01010030080000c030140402400004090080000c000142100002000030000001000000020000302c0000c0200405010060100500c000000101c000000102c010040200c1dbf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x17e1286052c0001920000008a3b07442b80017400005a0e33c000001930000012b8000de1790d0f40d8618000e6000690750c509e7c52008c27e240000000000001000033e000caa1e408444678001862ec721cf338034651833800000018218e850aa8db36c778b50f22380009180045c5e0000004aa5880000007e0010600037c000000003d6518da24410a000f71d520c99c7083c0386e8000b6332268cb0002c855cf99c8000000241480000ec00074066815048001aa808320fe2982cca70d7392928268b82446608919430e00000000178428130000b40002603708208d27a1d498000c7034000458000b513200000000000000800ff0000000000037a684f18000008f8000003f2000d680023a17000000000000fa8003f8000000001628708f88b0004502816341e344001da1f28fcb80d80964249b0001d65b4000003ce000cb80024c058001540120000023b000000000001021440020b0ca8280000000007c00260436000f28001d2000060002cc18cc800034604d2c8194261500000000037c001f00001d80003e322000000000000002d800000040e58002268a8188d02d63c41a8ef1801c8e1a66000000000700341a42381d4ca9900a8001e08851584304a6a46106a0f65147d1f211a278c59fe0ba6c8900f73d4138490321ba51c5b9ed2ea254861d335e4b130852202000009842f81e0c917a172000000fc0000000015100000014800000160001560005085a07d45e090000000006b8001490da0006d02c1dc780001d720440c0009b424000fb08e13e630000620508404e8cc24e0bcb400038400cc6860000000000002a00000000018c000001c41a8000001a8104000000
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x941d023e65d0d40c714f435031c5350d40ae181435031c5390940ae982425031c5310940c714f415031c5350540ab189415035853d0140c714e405023d6590c40cd90d51103344354440cd547401037151900408fd95401029c6350040cd545401027b6550040b618d401037151500408fd9152cc23c6454b309dd8552cc2746154b308f99251cc23d6494730bc58440cc27661152309d584548c23e649513097d8d544c27b60551308f994544c33854cc130c7152304c26e62d50309b58b540c27661d50309d587540c23d6595030c718d540c33860550308f990540c26e62150309b588540c27661150309d584540c31d54d0c3097594430c32e5494830cb552520c32e5454830cb551520c3686054830cd952510c3355494430d994a510c3655294430dc982510c3365454430cd551510c3665254430d9549510c33954d0030e6d0f400c2796510030e610c400c2f1611003097d95300c29c644c0309ed95300c2b8644c0309798f54c825d63d53208f99353c823d64d4f20ba18132c82e9620c3209d987548827561d52209d984548827561152208f993538823d64d4e209d987538827561d4e208f990538823d6414e209d98453882756114e20cd95251883355494620dc98251883365454620cd551518825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534827b6054d209b195324823e64145208f590514825e63150209758c540827661150209d584540823f6454c208f191530823e6414c208f590530826e6214c209d98453082756114c208f992500823d64940209e5943008359530c0209bd95200827b65480209798f54c425d63d53108f99353c423d64d4f108fd9152c423c6454b108f99052c423d6414b109798c52c425d6314b10b918941c42b5648c710ad59021c42d56308710d954821c426e62d52109b58b548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e64d4a108f59352842d86350210ae5903084359530c210ba58830842b9648821097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d108fd91524423c645491097d8d524425c63549109d19541442e46250510ad59231442f2608c5109d195314427665c8510ad59021442d56308510bc98021442786550110b618d40443b141501109e99730442b9640c110ba58830442f2610c110ae59220442f261881109e195204423d65950108f990540427661150109e980540423e64d4c108f593530427a60d4c108f990530423d6414c109b988530426d6214c109d984530423e64d48108f593520427661d48108f990520423d64148109798c520425d63148109e980520433554c40109e596100433954840109dd95100433554440109ed9510043395444010
  | 1 => 0x200000002008000000000000000000000000800000000000000000000080080000c0100000000200800802000004008000000000080000000402801006004000030000040000100600000000000000008049e9825190e7960946439d9845050e756114143d6d0c5050f3a4314143dc9845050f7161141438fd954310eb86050c4397d954310ed86050c439dd855210e7461548439d9865090a7561942429e9805150a796014542d9d085150b364214542dc9805150b7160145429ed815310a786054c42c754c4310aad6210c428fd954210ab461508429bd954210ae461508429d98754cca7561d53328f99251cca3d64947329e98251cca7960947329e983548ca7960d52328f992508ca3d64942329d986508ca7561942328f992544ca7661951329d586544ca7a60951329e582544ca7761551329d185544ca7b60551329e181544ca3e6515132cdd53514cb3454d4532cdd50514cb345414532ced53504cb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb7051141329d984540ca7561150329e980540ca79601503297d95320ca6f654c8329ed8153d06786054f41ad18542d06b66190d41cb90c525072c43149418f997425072c52d0941cb14942506b46150941d914b415072c52905418f596421063f6550441ab18941106776550441b9189411073a4254041ce109501073b4154041dc90550107394154041dc505501066e62d53319b58b54cc6d4614cb319e983548c67960d52319e980548c6796015231ce952508c7395494231ce951508c73954542319bd89544c66c62551319ed81544c67860551318f990504c63d64141319b988540c66d62150319e980540c67960150318fd91520c63c64548318f992510c63d649443197d95310c677654c4318fd9153c863c6454f219ed8153c86786054f21bc58041c863e64943218f59250c867a60152219e580548863e64d4e218f593538867a60d4e219e583538863e64951219bd89544867761551218f994544863e6494d218f592534863f6454d218f19153486776154d219ed8153486786054d21cd153214872c54885219798f540865d63d50219e983540867960d50218f596540872c6255021cd185540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c755153087546154c218f990530863d6414c219798c530867a6014c219e580530872d54d08219b594420873554d0421e9d0b41086756510421e910841086f16010421d554f3108675650c421b9588310866f6548421ab19121086776548421ad191210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50086b86050f409dd8552d02746154b40ab18
  | 2 => 0x44028b6000000032e2b80045000000000000000000000009a800000005e00819b360000000000ce0000024831a500000000000000007da6239960368000025c0000000000000005117c0000000000b78000000000000000003e962b5b10a4800000b0bd8000016e000000000000000000000b0000000000302000000000000214371302401c0000000000000005400070800001dcb8800000007ca765510c000004f8003d94e000000a80000000000000000000000001580001000112000000000000000000000000000000000000030a00000838000004a0000000186000000000000000000000000000000000000000000000001e80f8727e934000000000000000268000028600000000000001e7b80000000ab9b80000000000802e4000000000000000000007a80097800868005c99a63800002520018200000ca2162980000000000ee158300000000000000000d8765184c992f0000000028400000000000000086184002b000268000a8000a278800a20000000000000c1a447f22c00000000188f9aebb0e4cc1b61694c0029800000002ea8a000000008f0000029a000b800000002fc00000000000000000000000000000000000002ac0000010000a58004e326808002d00000000002fa758000000000000000003080000000001de0010400000a4000c480013a2e68800968009e8000000000000000007600000000000000000000280409a45580000000000000003c000001e8f8178000000000000000c06eaf80027800258819100007e00000001e472000bf8000000000170000000000000000b80000030ca28004a8000000000000cb2d000000000000004600106149c4000a400000001967d000cd0002c800000000000000000000000006a000002700019000000000000000000400380029e5a0000024e9080000000000aa000008c83a82126780c44208e14000c515e83000000003a07c8a800000000024a00000438ce000a000000998000020a24800000000030ebd000508005e8007c190000003300000000ae0000005cb70008c0004a000000ba160c800000a3800088000a0743f8bc00000000000000088800000000010a0012e000000025600000000006500000000950f09300000192092704d800a9000000000011c0000000000ae80000000000000000000000b697eb6324b20880000038800002cc000000000000000000000000000000000000000000000001800000000000000000000000000002a60000000000000000000003212000008010000040080c00400000001000000000000000040180200000000000000000028040020080080100001c00001000008010080020080080100000000801008000020010020040100000000000000002010008000060080000000400002000004000000010020000080100
  | 3 => 0x662240000000000000008e0700031e001c6000000000000116000009fac000000b98000000000000001180014a50000000006c00034000000009d000001520000000000000000000000000c5800001b2000000000000000ce8000980000000211bcb1a3a0000000000bc80000282000006700000000c70006a0ac00132c6000002e873802000624785467aa8b4800001aa21800000069f000002360000000000000000000000042730009c82e00000003220000000000002b600240622203a8807e2be0008c00000870001200000000000000026c000000d00000000980000000000020000000000000000ac8f2628000012c57000000001a0003d0164880000032000dec00000021e46800c20003f000000000000000000a7000000000000000000000007f800002aac80ca1baa00000000012000000033291800000000000000000000000016a000004e8000000000000001a600204001ac0000000000a5000001a000000b10000000000000000002600000000000000000000000250007528c00000000145d00000000b2ace000d2000000000000000000000001a00000002b4001c0000be591b463000000000000000210000000009e000008d000361d222abc7400000000000000006ca8b2a899da00120350000000000000bb80e000009b8000008279966b50e0182c200000000041e0000000000000000000016c5d9ec0012400000c10005231a3593c5680000000001be3b09600000728000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1420340d2402cc0010004823c60001534401c059500000000000e10a0185c020000002005461c15310c42948e2b1086214b170986435069338c86292832c5c06150941a50e4a0aa020d60725055010712310c2aa0434c5c06155021d4084b008210ca4745883108658b88c0a1a818614e6090940962e330484a060c53189415030a31aa2a00819418d5150040c30c6302a81853171181540c34821ac220061461d1530c020a48e8a9043885187454c308434831a82a0221681c94150110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x46208000921809c64314941c20625c06155021c10535c66090940c10635c46055030c80631c94150110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (i*5) 5
  | 6 => packedAt s4K6 (i*16) 16
  | 5 => packedAt s4K5 (i*27) 27
  | 4 => packedAt s4K4 (i*38) 38
  | 3 => packedAt s4K3 (i*49) 49
  | 2 => packedAt s4K2 (i*60) 60
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (18682+((h/205+packedAt s4K5 (16632+(h % 205)*10) 10) % 984)*11) 11
  | 4 => packedAt s4K4 (17250+((h/138+packedAt s4K4 (15732+(h % 138)*11) 11) % 1166)*10) 10
  | 3 => packedAt s4K3 (1273+((h/8+packedAt s4K3 (1225+(h % 8)*6) 6) % 40)*6) 6
  | 2 => packedAt s4K2 (304+((h/1+packedAt s4K2 (300+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf01ff81fffff841f1f0ff87f8ffffc008e73fc
  | 1 => 0xffe0ffe07e1fffe01ff0ff87f1e03ff8f38ccf
  | 2 => 0xffffffff801fffffe000fffffe003fff03ff0f
  | 3 => 0xffffffe007ffffff0007ffffc007fc0ff0
  | 5 => 0xffff0000000007fffffffff800000007fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x14c288c515044c0505893c498329a43086315c
  | 1 => 0x214a9143212944a00b984cc29142a950b284c5
  | 2 => 0x428422880c52014b20009115240512a3015b0a
  | 3 => 0xb1444124803127252220006489600c5580ea0
  | 5 => 0x8c18871c719c679c9ccce66001182306efe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfee0fee0eac0eac0fee0fee0eac0eac0fee0fee0eac0eac0fee0fee0eac0eac0fee0fee0eac0eac0fee0fee0eac0eac0fee0fee0eac0eac0fee0fee0eac0eac0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36282
namespace PEqualNP.Outside.L_meta_36282
open PEqualNP.Outside.L_meta_36282.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d02fca3a05f54740beaa4817e53902faa7205f94a40bea94817e51902faa3205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40dfa1a81bd43502fea4a05f14940bfa8a817c51503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461de328c3b865185f94630bea8c61df318c3ba63185f94230ef98461fb308c2fea8985f95130beaa2617c544c3bc86987750d30bfa92617c524c2fea2985f14530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa418778c830ee190617e510c3eca2185d94430bea8861f5510c2eaa21877cc430ee988617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83dc43907b08720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51883eca3105d94620bea8c41f551882eaa3105f94220f790441fb20882fea8905f95120beaa2417c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483dc84907b50920f719241ed32482fea2905f14520f710a41ec21483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb90e21f421c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10f7294216e52842faa5087b54a10b6a94217c52842faa3085f94210fd20421f940843f661087e0c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443ec62887d4c510fb90a21f421443f480887e50110fd98221f830443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc5150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e85de53d0abca7a15f54f42eea9e855d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350bde84a16f90942bfa8a85f75150aeea2a15f14542fa28a85745150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f721665ed42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7197790e32eea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6197790c32eea18657e520cbdc84197b50832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41dfa1683bd42d06fca1a0df54341beaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620df94841f7290836e52106faa420fb54841b6a90837e511077e8220fd90441dea0883f541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118fe94231bd284637d508c7f2a118de54231bfaa2637e544c6faa898df15131ef21a63dd434c6fea498fbd4931b7a92637c524c7d8a498db14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f721643ed42c87ee8390fd10721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f721243ed42487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410fbd0821f621043ef32087d86410df94421fba0843f441087de4210fd88421f690
  | 2 => 0x92d232690781b4919193e20e44106e050890250644c41453207f2e6838f191432096c439850ec0012e2451dc37523a4d26073c539404ae0dcf11fd1726c0a4a1d22c97c151471bc76c00122224000691240640e8bb10249e8ec000d90343acf71590d2628949c845e000001a32f8310001aa0008805d073302388e319c41a2540f87e0005d0079050e81e80085600069ce207b186188da0c92688c13790d0b0000b89c71a0298aa10e09031c9797230899c0000006a3589f93a0005205c26b000354520ea2b66910392d3365a4a10203d89a112a53000000e100029c230d61652820ad3a00032e0000020100027d1f84e3c00010f1600007442293d202494f28004388b4f48080009740008d0182891f0cb0000004b000000084428044e267800042380088118000008188d02d3509c8d32322942ed2894420822d1a17f000950ad04d4504c89703e332578930ce00039c2600010643ccb09b4b2850610b31d020119889102391308f44721a8301bc03a8d91d0003300249e21828c574540554aa59838a580be7e0ba9b60b68b87601b02a164941781822f0002210003984c00010810cec2522160513508e28a844de9de1ee064d899d1ca3f0b78002d45840024c000000001632f446d099270009211e2163ee7f85f0c5158168ee03f3128a92093335e5408a8384e62a41d9b74162ac3c8330ee380038d71be67cc00f63d60b89099305e8643595549289c7fa4a2102a9318d13d47349f0061803f4a98f03101f05b16701a4404a04b22e3a4591ae3da86cb214d32a90d2d09a1327d46c15c3e06185b8fb08c560fda0203c3f8c91a53e6444298ef0cc784df1f60f05b0e51000a88c4e2870088328ee83426280cc708f35257d2111c3cc5f48e8f947a368cd1b20062fc2e0413923181b0000bc4b0b721543e684860b500a52c71938344424a18b14dc0280002044080081e802000161fc1c0d00d0001d0000007c02024000200200c1d09003000010040000005164240141a1440b008020080902c0301004004020383b00c0a0242e094740a0010240001c06000060681f01001000030080c0000200c0003c0103400000070241b0286a02003000060001003403044050100104805000080041200019000000086f000000080101c0701819008010d017014020001f0240001c43000000043c0040107c11008000080602007010000000202c0f14408000340041c0cc0900801024040dc00000090002000c0100802004190041b0201f01012014020280202409000000041314801008010181c000060d40009005000120940100810bf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877
  | 3 => 0xef8612f66b4c58fa4ee7507a92a23c25c4509e35672d111b5000040e0a041221bcc617709e7300e1911b88d4000000fa0000000027600000000412001028670006e4200003c8000000002300009b000000995331d710c4d4e18bd4ea04c329d20a07e8578273040086d800000001060a337e0000009d31e8686a14c0ae3b520026000281271e80c6544000000008492b1bb000000000494bc754dd1f2206248b58522f22c0091831a69c00b97e19e7d0070000580000000000000136800000000aba2602c000001070000000000041400000000272418640003ce11d2809015c0000001146e5b52200b2e0294001d33fe1b04400a4520c5159fc1f0000a902530e2d0f78cd0ea980790002d03cc8f9944ec285040000000c000000000840e82381260000005d340000390000d0000c683d3b2000001d60008b0001da00000095a000007380000042e000000002409b0fc8003660001489c214588ab0ad19888c9b8f129e83c0011304800070818370
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xd544c27b605513097996434c25c6550d30b6181434c26e62d50309b58b540c27661d50309d587540c23d6595030c718d540c33860550308f990540c25e63150309b988540c26d62150309d984540c275611503097597430c31d54d0c30b398b430c25d6510c30c7550430c32e5494830cb552520c32e5454830cb551520c31d548c830d354a320c31d540c830b6580320c3365494430cd552510c3665294430d954a510c3726094430cd951510c3355454430d9949510c3655254430c7553310c34d52cc430c7551310c2cc624c430d3549310c356514c430ce553400c39b43d00309e594400c2f16110030c7553300c25f654c030c7551300c27b654c0309798f54c825d63d53209798e54c825d63953208f99353c823d64d4f20b918542c82ad6408720b358c21c827661d52209d587548825e63152209758c548827661152209d584548827661d4e209d587538823e6414e208f59053882766114e209d584538825e63946209758e51883566394620d558e51883726094620d9947208825e63951209758e544825f63551209718d544827761551209d185544825e6394d2097994534834d6214d20d314e424826c6550920cb151424834c5350920b9185424834c538c9209b195324834c5388520ab59021482cd6308520d314c21482ea6008520b9986204825e63150209758c540826e62150209d984540827561150208f990530823d6414c209b98853082766114c209d584530826f65480209ed95200825e63d53109758f54c425e63153109758c54c426e62153109b58854c43566194f109798f52c425d63d4b108f99052c423d6414b109798c52c425d6314b10b918941c4356534c710b918931c42b56408710b558c21c426e62d52109b58b548425e63152109758c548426e62152109b588548426e62d4e109b58b538423e6414e108f590538426e6214e109b588538436a6094a10b618d40842b9640c210ba58830842d86348210da949208436652c4210b698f108425f63551109718d544426f62551109b189544425e63151109758c544426e62151109b588544423f6454d108f191534426f6254d109b189534423f64549108f191524425f63549109718d52442746550510b918941442f2608c5109d19531442e4624c5109d99721442b56408510b558c21442f260085109e19540442d863501109e99730442b9640c110ba58830442f2610c110f44c430442f261881109e19520442d86348110f808520442da63c4110b998a104425e63150109758c540426e62150109b588540427661150109e980540427a60d4c108f990530423d6414c109b988530426d6214c109d984530427661d48108f990520423d64148109798c520425d63148109e980520425e63944109758e510426e62940109b58a500427965840109dd95100427b6544010
  | 1 => 0xca7a60d52329e583548cb1e5450e32b6181438ca7661942329d586508ca5d63951329b58a544ca7761551329d185544ca7b60551329e181544ca7661150329d584540ca7a60150329e580540ca5d6590c32b6181430ca6d6590832b9185420ca5f654c8329bd95320ca7b6054f419e18153d06b46150b4197d8d50d065c63543419bd89539066c6254e419b98a509066d6294241cb14b425076452d0541d394e521074d5394841d394d521074d5354841d9185521072d52d04418fd95411072d52504419dd9541106e46250441d694e50107595394041da94a50107695294041d694d50107595354041da94950107695254041dc905501077141540419b98b54cc66d62d53319b98a54cc66d6295331b618143cc67a60d52319e583548c66e62152319b588548c67a60152319e580548c66e62942319b58a508c76a6294231da58a508c75b31942319b98a544c66d62951319bd89544c66c62551319ed81544c678605513197195434c71c5450d31b6181434c74e4314931d350c524c74c52cc931b6982314c65e63150319b988540c66d62150319e980540c679601503197d95310c677654c4319798e54c865d6395321b918542c87a542d0721b958841c86f1601072197d8d50c865c63543219798c548865d63152219e980548867960152219e983538867960d4e21b398f428865e63951219758e544866f62551219dd85544863e6494d218f592534866f6254d219b996424866c6550921b9185424865e63d50219758f540867a60d50219e583540863d6595021cb189540873461550218f990540865e63150219758c540866e62150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530874c6254c218f990530863d6414c219798c530867a6014c219e580530866d65d0821cb55342086ce63d08219b594420872d5410821cb553320874d53cc8219b594320872d540c821b9584320873554d0421e9d0b41086756510421bc580410872d54c84219bd95210872d54484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50086b86050f409dd8552d02746154b409bd8951d026c625474097d8d529025c6354a409798e519025d6394640c714f435035853d0140d6181531034e5394840d354e521034e5354840d354d52103565394440d554e51103665294440d954a51103565354440d554d51103665254440d9549511031d53d0040dc546401023f6550040c754d401027b6550040b618d401037151500409b98a54cc26d6295330b618143cc26f62547309b18951cc39943d0330b658c40cc2f161103309b988548c26d62152309d984548c2756115230b398b438c2cc624c6309b98a544c26d629513097d8
  | 2 => 0x2e8c5220a33648b29e0e2e0381beea8000019a0022a002aa3712c901c427adca583029000003a4002d4000740007c1c13400000e126aa501219000b38f63a80001818339f265b7cab0109b9c077a5a013566ba38970ac3a228e5b027d322e4b06c48609f2a6de9c60d08ee093e6e0544812422a8600130b320c20a5828b4ac7a18ea2d83c348a608c64b36513045b014e185882020c932eb91507a01655066650bcb0a32269fa44a100a0de4c9a88fb38e81baeb14a108aa00116acb54c9a1a0026609370ab9fe51a5200248111624128ea40d84a8726119084876d78000039ca70007316e9a0005a9bc501986c8c092b900029209b3c4b8c624800e32cad62a8c00c2001ea8d8fc14a7a331ac7494cd6ae243b0c49ada000005db44581b48f000ba8b86db8e7b03cd98848589462ab05e18e4da0eb4164c28e2a91e0cfade0015246af0258004500a3c800462740021e3d242e8800b036ea00ba16b202c86e630007580080234001020015693800000000b17e0027200360002d63283e0c95aa285c913888e982a810adcaf23227e6201a08a9a2d0aee6bb01a36a5382ed40ecca2b43e99e002f6989701a87e133347687817b32072fe68108bf226de000401384197a57110d1a1c952f479000d30000208039b680383673b9e1591eb9afa78b3a8503a918480785059a0a000f8caac8368007d80098000d3862218022615ed026c002020a800893305a0d23438088a70433627f1d0b48884e8b697bae4898003282c70a869376811c8c69c20014200000b10009db74001dcdf93c000007c000003a6139585f0c4128007b8008c172a10beaf3181eaf89e38a0000081aeccb352000007e00079a503b9b035aa200310618900bc0800002008080081e0a40204000064100a83c0080000c000083200000008050001d078010001b0000000c04008000042003c120242303c0000c05000180040105401004050200000c1b0440000c030000a008010002c00c06038010000c06c0901000014000440501c07028080143c04800044010040a00013000010040103800040071402809c080081600400048000240a00c16018110a408078050000800003010040280004c0d00c00004090000e098040000e00c0501800060010900c064010c6ce62d0e439e9825190e796094643b398b4350e6e62141439b5885050e7661141439d5845050f5b4314143da9885050f696214143dc9845050f7161141438fd954310e5f6550c43b61814310e6f62544439b1895110ece63d0a429d9865090a756194242b398f4250a5e63145429758c5150a7a60145429e5805150b566314542d558c5150b674214542dc9805150b7160145428fd954210a6f6550842b91854210a5f63540429718d5010a7661d53329d58754ccb2e5450b32b918542cca7a60947329e58251c
  | 3 => 0x8b8009599cad8001b0a6001aaa20a0000d42c000c230e00394ae80000000ae000688000000072800753160000000342d7046b18fee6000002ee4709c7626400000000400024c698004a148db174af8e400
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x64448f14d2000d501101828039741b08004c1c070b4c625a51606088084a82007529cb4314143cc2c4b08a0a1d4673d085150b28b1ac028a85899506150b32c34a8302871956072505501070c2a0c0a1a63521c14314931a62e030aa810e0d5498f4208712aa2c219043495d742d0421ca0c6a8a802053171181540c306aa4c5a186186551600c830c1aa8312621851975d0f400c3122a0c2a12419114c615092089aec298429060d6414c2148348b226218221701c9310c110d82c498860885a17408520442e0b984290221b018c2148110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x408c81641c9310c1108c18718c2148110c817418c2148110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 5 => packedAt s5K5 (19164+((h/210+packedAt s5K5 (17064+(h % 210)*10) 10) % 759)*11) 11
  | 4 => packedAt s5K4 (19544+((h/157+packedAt s5K4 (17974+(h % 157)*10) 10) % 568)*10) 10
  | 3 => packedAt s5K3 (1475+((h/9+packedAt s5K3 (1421+(h % 9)*6) 6) % 35)*6) 6
  | 2 => packedAt s5K2 (182+((h/1+packedAt s5K2 (180+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe07fc7f07fff80f1c7e3f07fc7fff001733fc
  | 1 => 0x1ff87f8ff83c7ff01f8fc7f83f8e07fc69cccf
  | 2 => 0x1fff800fffc07fffe00ff8003ff007ff8e0f0f
  | 3 => 0xe000000fffff80fffff000003ffff803f00ff0
  | 4 => 0xfffffff0000000ffffffffffc0000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xc231088130880101041609118c12311803115c
  | 1 => 0x44511012118090100c824230948452282144c5
  | 2 => 0x88a2292462196067200c90432920a4d18e0b0a
  | 3 => 0x1c65248853032ba592000a43249c062f00ea0
  | 4 => 0x11046000c62244cc924924c6000100835ca000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeeeac0feeeeac0feeeeac0feeeeac0feeeeac0feeeeac0feeeeac0feeeeac0feeeeac0feeeeac0feeeeac0feeeeac0feeeeac0feeeeac0feeeeac0feeeeac0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36282
namespace PEqualNP.Outside.L_meta_36282
open PEqualNP.Outside.L_meta_36282.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x111500028d763169d5401b0000ccd1e00817b91285b801e0400a586402600183ae6a219343689480487c5ba0601c302a0022b289493c6240b964660e002639e804e181810110040002a004801008700263c18001ffd50077f5401ff95007fd5401df55007fc54027fd4c09fe53027f54c09fc5301ffd0c07fe4301ff50c07fc43027fd4809fe52027f54809fc5201ffd0807fe4201ff50807fc42007fcc801fe32007f4c801fc32027fd4405fe51027f54405fc5101ffd0405fe4101ff50405fc41007fcc405fe31007f4c405fc31007fc8405fe21007f48405fc21027fd4003fe50027f54003fc5001ffd0003fe4001ff50003fc40007fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x64001fb0832000ffe2190007fe10c8003fe0864009ffd952004dfeca90027fe65480097f32a4009ff5952004dfaca90027fc65480097e32a4008ffd9120045fec890023fe64480077f3224008ff59120045fac890023fc64480077e3224008ffd5120046fea890023fe5448011feaa24008df55120047f8a890003ff63480017fb1a4000ff98d20005fcc690003fd63480017eb1a4000ff18d20005f8c690027ff5348013ff29a4009ff54d2004ff8a690023ff4348011ff21a4008ff50d20047f88690006ff6248013ffa924009ff9492004ffaa490027fc5248011ffa124008ff90920047dc8490023fd4248011f6a124008ff10920007fe6490003fe3248001f71924000ff4c920007da6490003fc3248001ffb0a4000bfd852003ffcc29000afe6148001feb0a4007ff18520015f8c290027ff514800fff28a4009ff5452003ff8a290023ff414800fff20a4008ff5052003ff88290003ff314800fff18a4000ff4c52003ff86290003ff214800fff10a4000ff4852003ff84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001ff9012000ffa8090007fc4048003ff9824001ff8c12000ffa6090007fc3048003ff9024000fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007ff1048003ff0824001fe8412000ff8209001bff654400d7fb2a2006ff99510025fcca8801bfd654400d7eb2a2006ff19510025f8ca88017ff644400b7fb222005ff9911001dfcc888017fd644400b7eb222005ff1911001df8c888017ff544400bbfaa22005ff9511002ffaa8880177d544400bfe2a22000ffd8d10005fec688003fe63440017f31a2000ff58d10005fac688003fc63440017e31a2006ffd4d10037fca68801bfd534400dfe29a2005ffd0d1002ffc8688017fd434400bfe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e3122006ffd4910037fca48801bfd524400dfe2922005ffd091002ffc8488017fd424400bfe2122000ffcc910007fc6488003fd3244001fe1922001bfd8510017fea28800bfe5144005fb28a2002ff54510037eaa28800bfc5144005ffa0a2002ff90510017ec828800bfd414400bfaa0a2002ff10510017fe628800bfe3144005fb18a2002ff4c510007ea628800bfc3144005ff90a2000fdc8510017fc428800bfd2144005fe10a2002fd0851000dfec088007ff5044003ff2822001fe9411000ffaa08801bf95044003fe2822001ffd011000ffc8088007fa4044003fea022005fe5011000ff88088007ff3044001fd9822001ff8c11000ffa6088007fc3044003fc1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0xbff31cc023ff18e6000ff4c730097f86398003ff21cc023ff10e6000ff4873008ff84398006fd60cc003ffa866001ff9433000ffaa198007fc50cc003ffa066001ff9033000ffa8198007fc40cc003ff1866001f78c33000ff46198007fc30cc003ee1866001ff8833000ff84198007ff10cc003ff0866001fe8433000ff82198043ff654c0217fb2a6000dfd9530004feca98043fe654c0097f32a6010ff59530085faca98043fc654c0097e32a6010df19530024f8ca9803fff644c01f7fb22600fff9913001dfcc89803ffd644c01f7eb22600fff1913001df8c89803fff544c01fbfaa2600fff9513007ffaa89803f7d544c01ffe2a26001bfd8d30087fea698043fe534c021fea9a6010ff14d3007ffe869803ffe434c01fef21a600fff50d3007fba869803ffc434c001ffb126000bfd8930007fcc498003fd624c001fe3126000bf18930087fea498043fe524c021fea926010ff1493007ffe849803ffe424c01ffea12600fff10930007fe6498003fe324c001fe9926000ff0c930007fec298002ff614c01dff30a6002bf98530007fac29803bfc614c0057e30a6010ffd4530077fca298043fd514c01dfe28a600fffd0530077fc829803ffd414c01dfe20a6000ffcc530077fc6298003fd314c01dfe18a6000ffc8530077fc4298003fd214c01dfe10a6001bfd813000ffea098007fe504c003fea826001ff1413000ffe8098007fe404c003fea026001ff1013000ffe6098003fb304c003ff1826001f78c13000ff86098007dc304c003fc1826001ff8813000ff84098007ff104c003ff0826001ff04130057fecb90036ff65c801bff32e4004bf9972006ffacb90036fd65c8015fe32e4004bf19720057fec990032ff64c8019ff3264003bf99320067fac990032fd64c8015fe3264003bf19320067fea9900337f54c8019ff2a6400cff55320066faa990033fc54c8015ffb1e4000bfd8f20007fcc790002fe63c8001feb1e4000bf58f20057f8c790002fc63c801bffa9e400dff94f2006ffaa790037fc53c8019ffa1e400cff90f20067fa8790033fc43c80037f316400dffd4b20057fca590037fd52c8015fe296400cffd0b20057fc8590033ee42c8019fea16400cfb50b20057f88590003ff32c8015ff1964000fb8cb20007fa6590003ed32c8015fe196400affd872005ffcc39000afe61c8001feb0e4000bf58720057f8c39000afc61c801bffa8e400bff9472006ffaa39002ffc51c8019ffa0e400bff90720067fa839002ffc41c8001ff98e400bff8c720007fa639002ffc31c8015ff90e400bff88720007fa439002bfc21c80037eb064001ffd432000ffca190007fd50c8003fe2864001ffd032000ffc8190007fd40c8003fe2064001ffcc32000ffc6190007fd30c8003fe1864001ff8832000fdc4190007fa20c8003fe1
  | 2 => 0x21015fcc59086bff52c8415ff296421aff54b21057f8a590867ff42c8415ff2164219fb90b210cffa8590867ed42c8415fe2164200ffccb21057fc6590803fd32c8415fe1964202bf58721017fea39080bfe51c8405fea8e4202ff14721017fe839080bfe41c8405fea0e4202ff10721017fe639080bfe31c8405fe98e4202ff0c721017fc439080bee21c8405fb10e4202ff08721017d8439082bff60c8431ff3064201bf98321007fac190802fd60c8415fe3064201bf183210d7fea190863fe50c8435fea864218ff143210cffe8190863fe40c8433fea064218ff103210c7fc6190863fc30c8431ff106420aff08321017fe219080bf710c8405ff0864202ff043210bffeca9085eff6548401bfb2a42009fd95210bffcca90812fe654842ffeb2a4217bf595210bff8ca90812fc654842fbe32a42049f195210b7fec89085aff644842dff3224203bf991210b7fac89085afd644842dfe3224203bf191210b7fea89085b7f544842dff2a24216ff551210b6faa89085bfc5448401ffb1a4200bfd8d21007fcc690802fe6348401feb1a4200bf58d21007f8c690802fc634842fffa9a4217ff94d210bffaa69085ffc534842dffa1a4216ff90d210b7fa869085bfc43484057fb124217ffd49210bffca49085ffd524842ffe2924216ffd09210b7fc849085bee424842dfea124216fb509210b7f88490803ff3248401ff1924200ff4c921007f8649080aff6148405ffa8a4202ff94521017faa29080bfc5148405ffa0a4202ff90521017fa829080bfc4148405ff98a4202ff8c521017fa629080bfc3148405ff90a4200fdc8521017fc429080bee2148405fe10a4202fb08521017e84290803ff60484017fb024215ff9812100dfcc090803fd604842bfe3024201bf181210bffea090857fe504842ffea824215ff141210b7fe8090857fe404842dfea024215ff101210affc6090857fc304842bff1024215ff08121017fe209080bfe1048405fe0824212ffd97300a5fecb98053fe65cc0097f32e6014ff597300a5facb9804bfc65cc0097e32e6012ffd933009dfec99804ffe64cc0077f3266013ff5933009dfac99804bfc64cc0077e3266013ffd533009efea99804ffe54cc027feaa66013df5533009ff8a998006fe63cc029ffa9e6012ff94f300a7faa79804bfc53cc027ffa1e6012ff90f3009fbc879804ffd43cc027eea1e6012ff10f30097fec598003fe62cc0017f3166000ff58b30005fac59804bfc62cc029ffa966014ff94b300a7faa598053fc52cc027ffa166013ff90b3009ffa859804ffc42cc025ff9966000ff8cb30007fa659804bfc32cc025ffb0e6011ff98730015fcc398003fd61cc0017eb0e6012ff18730015f8c398053ff51cc023ff28e6014ff5473008ff8a39804fff41cc023ff20e6013ff5073008ff8839804
  | 3 => 0xfb2e6220ff99731025fccb98883fd65cc4417eb2e6212ff19731025f8cb9884bff64cc43f7fb26621fff9933101dfcc99887ffd64cc43f7eb266212ff1933101df8c99887fff54cc43fbfaa6621fff953310fffaa99887f7d54cc43ffe2a66202bf98f31107fea79884bfe53cc441fea9e6212ff14f310fffe879884bfe43cc43fef21e621fff50f310ffba879884bfc43cc425ffb166200ff98b31005fcc598803fd62cc4017eb166212ff18b31107fea598883fe52cc441fea966220ff14b310fffe859887ffe42cc43ffea16621fff10b31097fe6598803df32cc401ff1966200ff4cb31007ba659884bfc32cc4057eb0e6202ffd4731017fca39880bfd51cc405fe28e6202ffd0731017fc839880bfd41cc405fe20e6202ff8c731017bc639880bf631cc405fe18e6202f70c731017fc439880bfc21cc425ffb06621eff9833100dfcc198803fd60cc4017eb066212ff1833100df8c198883ff50cc43dff2866220ff543310f7f8a19887fff40cc43dff206621fff503310f7f8819887bfe30cc425fe186621eff883310f7f8419880bff10cc405ff0866202ff043310effeca98876ff654c43bff32a6204bf995310effaca98876fd654c43bfe32a6204bf195310e7fec898872ff644c439ff3226203bf991310e7fac898872fd644c439fe3226203bf191310e7fea8988737f544c439ff2a2621cff551310e6faa898873fc544c4057fb1a621dffd4d310effca698877fd534c43bfe29a621cffd0d310e7fc8698873de434c439fea1a621cf750d310e7f88698803ff624c4017fb126200ff98931007fac498803fc624c4017e312621dffd49310effca498877fd524c43bfe292621cffd09310e7fc8498873fd424c439fe2126200ffcc931007be6498803fe324c401fe9926200f74c931007f8649880aff614c405ffa8a6202ff94531017faa29880bfc514c405ffa0a6202ff90531017fa829880bfc414c405ff98a6200fdcc531017fc629880bde314c405fe18a6202f70c531017e8629880bfe214c405fe10a6200ffd8131005fec09886ffe604c4037f3026200ff581310dff8c098806fc604c43bffa82621bff941310effaa09886ffc504c439ffa02621bff901310e7fa809886ffc404c437ff182621bff0c1310dffc409886ffc204c405ff8826202fdc4131017fc209880bfc104c415ffb2e421abfd97210d7fccb90812fe65c8435feb2e421abf59721057f8cb90812fc65c8415ffb264219bfd93210cffcc99080efe64c8433feb264219bf59321057f8c99080efc64c8433ffaa64219dfd53210cffca990867fd54c8433beaa64219ff15321057fec790802ff63c8401ff31e4200bf98f21007fac790802fd63c8415fe31e4200bf18f210d7fea79086bfe53c8435fea9e421aff14f210cffe8790867fe43c8433fea1e4219ff10f
  | 4 => 0x2bff618c859ff30c6402bf98632007fac319002fd618c815fe30c6402bf1863216ffea3190b3fe518c85bfea8c642cff1463212ffe83190b3fe418c84bfea0c642cff10632167fc63190b3fc318c859ff10c640aff08632057fec1190affe608c8037f3046400ff58232005fac11902bfc608c8037e304642dffd423215ffca1190b7fd508c857fe2846425ffd023215ffc8119097fd408c857fe204642bff8c23215ff861190affe208c815fe104642cffc423215ffc21190affc108c855ffb2a642abfd9532006feca990027f654c855ff32a6404bf99532157faca990aafd654c855fe32a6404bf19532156f8ca990127c654c853ffb226429bfd913214ffcc89900efe644c853feb226429bf5913214ff8c89900efc644c853ffaa26429dfd513214ffca8990a7fd544c853beaa26429ff15132157fea6990abfe534c855fea9a642aff14d3214ffe86990a7fe434c853fea1a6429ff10d32157fea4990abfe524c855fea92642aff1493214ffe84990a7fe424c853fea126429ff10932007fe6499003ef324c801ff1926400f78c932007fec299002ff614c851ff30a6402bf98532007fac2990a3fc614c8057e30a642affd4532147fca2990abfd514c851fe28a6429ffd0532147fc82990a7fd414c851fe20a6428ff8c532147f862990a3fe214c851fe10a6400ffd8132005fec09909ffe604c8037f3026400ff5813213ff8c099006fc604c855ffa826427ff94132157faa09909ffc504c853ffa026427ff9013214ffa809909ffc404c84fff1826427ff0c13213ffc409909ffc204c851ff8826427ff8413213ff8209902bff650c8497fb286424ff99432025fcca19093fd650c8497eb28640aff19432025f8ca1902bff640c8477fb206423ff9903201dfcc81908ffd640c8477eb20640aff1903201df8c81908fff540c847bfaa06423ff9503211ffaa81908f7d540c847fe2a06426bf98c32127fea61904bfe530c849fea986412ff14c3211ffe861904bfe430c847ef2186423ff50c3211fba861904bfc430c84b7f3106424ffd4832057fca419093fd520c815fe2906423ffd0832057fc841908fee420c847fea106423fb50832057f8841904bff320c801ef990640aff8c832007dc6419003fd320c801ee9906400fb4c832057fec21908bfe610c8057f3086400ff58432005fac21902bfc610c8057e3086424ffd4432117fca219093fd510c845fe2886423ffd0432117fc821908ffd410c845fe2086422ff8c432097f8621908bfe210c815fe108640affd803210ffcc019006fe600c801feb006400bf58032057f8c019006fc600c849ffa806421ff94032127faa019087fc500c847ffa006421ff9003211ffa8019087fc400c843ff1806412ff0c03210ffc401902bfc200c845ff8806421ff8403210ff8201904bff65cc4417
  | 5 => 0x2000008020040000480100000400800006010020000060240580b004000000030000040000000e008000000040040080300200800009002000030000120000080c0040100380600000c0000000000c008020000000100300000c01808000008018020000000080000402c0600500000c0000a0000000280000400403001002008010010000000200100005c04800004004098050000080100a01a0000400100e01c00003002000000010020080000c0160080180001c0000180000200803005000000000010000100300301002c008000080080280000200c01000022000010000000100380000a0040000000000c060000020040000a000014008000100400200301000000000016020000000020080180700e004008000040040200000000000800004018008040000000000000200001802006008000040000280000400004800000004044008010020000180000a00400800000000000040040040080d000004020010040300f00200001c0000402c0000281200200003805006000008000000000080000200001804000024000000080180200600800001006014004000000080000080600002404001000010000010540100000000212ffd9732185fecb990c3fe65cc8097f32e6430ff59732185facb9904bfc65cc8097e32e6412ffd9332135fec99909bfe64cc8077f3266426ff59332135fac99904bfc64cc8077e3266426ffd5332136fea99909bfe54cc84dfeaa66426df55332137f8a9990c3ff53cc825ff29e6430ff54f32097f8a79909bff43cc825ff21e6426ff50f32097f887990c3ff52cc861ff2966430ff54b32187f8a59909bff42cc84dff2166426fb90b32137fa859909bed42cc84dfe2166412ffd873217ffcc39900afe61cc801feb0e6400bf58732097f8c39900afc61cc861ffa8e642fff94732187faa3990bffc51cc84dffa0e642fff90732137fa83990bffc41cc85fff18e6412ff0c73217ffc43990bffc21cc825ffb06642eff9833200dfcc199003fd60cc8017eb066412ff1833200df8c1990c3ff50cc85dff2866430ff54332177f8a19909bff40cc85dff2066426ff50332177f881990bbfe30cc825fe186642eff88332177f841990bfff10cc85dff086642eff04332057fecb190b6ff658c85bff32c6404bf9963216ffacb190b6fd658c815fe32c6404bf19632057fec919096ff648c84bff3246403bf9923212ffac919096fd648c815fe3246403bf1923212ffea9190977f548c84bff2a46425ff5523212efaa919097fc548c8537eb1c642dffd4e3216ffca7190b7fd538c85bfe29c6425ffd0e3212ffc8719097de438c84bfea1c6425f750e3212ff8871908efe628c85bffa94640aff94a3216ffaa51902bfc528c84bffa14640aff90a3212ffa851902bfc428c801ff9946400f7cca32007de6519
  | 6 => 0x85e800153824a17a3723186a03583e06f0830278c201092b96b8308070658869ba00000000000000016525380000000000000004b0000000000000000668001c98000de01211f8000c80002578000001a20000001600000d00000000001b924000000000014d00000000003900013c0558000000001331560000b526089b0fc86991007b8000001b600000000000015e80780019284080017d00000000010a0d2251041800000049800177000266a209c39d080000000000012e0000000119d206903e8001080f41ee0000000000000f280001ca0c0700000001fb8d680000000009800000000018e0000000000aa2129a60000000ef0818938b30001699399e608e854914a2600024e0a816f8478d09b700023781100007400013d8000e4a3823683120208ba0f00000003b8688000001448260301e995b0450f909d93a06d1a32660c610b0c100005980000004800000000003b18c00000000000016180012800000000023a23b22490c98b80000001a0000001820001838c000002c156a2a8000001b021d0000001dd00000000000001e03180024985e23f1648d39558000000000001c600000000000019d90900017e86119ba2403d00015f8191dc22c91e12f0200001a0a3d225142a310410f480f8000000000c280001b00003c9878840001f780000b0000001460000b70000e10f180022180000000011d0000581290a609400000001509700005d9a90000540000000000441cf9420d79a19de8c905b14908d80007e8609a28002100001ce1d58001431fd1c109a89281580023901680000007509900000000025c8000000d88000d480008a8000000001e71fe80013f0001230cb8960000000e995c81d00011780000000012700008200000025ba198b68001040718bc87618400013f8ca0000ea8000001e500008900000004580000003f00b80000006380017283298105a9d00001530fd0ee8000000000ba9e78000001d49c42520001451b40000001658000df00000008a0000000000ad00000000000025d80002b0cd91689b9af26322d2568001c5800000001a3e000135020957a152459fa80000016687c80016280000014b80100000020721e8000f31ae0000001c917903f8b08000000000000001670e18ec8a000000000000015e00000022a2130dd8000000000988000d59ce8870c3000046a0600005094990f8c180000017a13880000005117e1f41bd8001300000720389ff0a58001a80000000730000be25580100000001004003008008000030000240100100a000010000020000080000801001801000050050070000100080600600002002006000008020000040380400202c0080000000000005000000008020020100080000a0600100000400c020040000100600900404002800002008010020020200000700200800000
  | 7 => 0x5999c9021d38f780005c94c8000001309c22410001001db8fd8000000000e580d07a80015d1130ce0000000001ed8001278000fb9511f697111980017805b80020f9159c497f0801e81720000000ed88380010511c9b38000a88d615a0000000a18bf0c48000000000b119a80000000000010880000016d8002438000c5a3600000000000017b07398989000007f00002f8001e0a281f582e24188f2259c6a331be0619ab1db16896e85618f00000000000002901ba1f8000e925880025493c80000021b0430c70000000cf8001f3a5b1cf24683800000da0400010a8000001748889ea92510111c00000015500000000000000015889186e14e80006c8a980021803621c1642528001500250000081fc14398610c0b400f019a2d8000000000000001cda628001918000211e90cf00017b80000013680005180000018f80000000005525fa108c88000089c70000f71e680a1fd9ed1a422ea5a9cd0a91a724b2300c513393b2428000220001eb1378001788000de9948000001ad81aa2380000014a0e395f1219e48c410ba030348000001888fb20000000017c8cd01880007c11380004a20b03a0149f02059b49e118a8000000000af00000017594b0000000b18000000c99068001e00bc04f8000ec0b586b0000000000000002271258000001d320e00903d80004e9c50e62269e400000024b8a10ba141a5419921921da220002681cb1909249b28ae9ad00280aa38a050160b78228000000620be9fb0848af80005d00000019a0000ab970042a6500600016d0001f48f81481ec1baa0a00003a84f05a06a91180023ba3a8db0590339ca9e300020d1d60fe213876a479151da9349cb8238fc12622126000014000000000000000023f80018b0130000ac12200025f1c800008100015b83207893a91100000000000022f91826223d8f21740001aa9121b792d2119750000809998000b4826a160008000000140000000000000001a100000324f9f310e1470ca80e00009d01c13e0eb0000000f11f500000000008e02c8a50001d10001f118700007f80009099780000000000000023c00010e8f880005280008f80012a93e94c1b324f19688d257000131a5000012c800062800000239a188000651c00000001b20000000000098001140000002168000000000b804d05c20a8000038f380024c80000018180000009e19f22e0e80179a9806a09a148d722b00000004382190326400000021b80023209301e8000000000000879209a380e82805f1d69958000001340000000001bb9f922916918086482d8748330660448401320000000001580000000e419e9ff9e18001a585789a00000014a80000019f9189ac89200014680006700000003780014d9f88fe9370b29d2a4aa3ea490001f60000002448e7a0180019c1778588ad9f998321f220186
  | 8 => 0x69a50000000cb2110001708000000d90001df00010709ea231dd9390001939c08460000001009f28641fc9e8926a080000db800000018000000267a0112111a9229da15980006800006305016e1cc8001ef12380022f11e8861bc00024d8000790f992d8000d10ce8001038ee16a0001638370dc16f0000000e298d26480011b90604c1098000000001b50d40001410000001441fe0000000000ff1a488b24805380007993b80001d80006d80000024200000000000000018c800067800000152a1402580000000009c20b8002008cca5e04ba618000000c3856a5d0000001e380009784c80000000000016c8d500000024500000000002b9d18b00c0a5a19d20e8000000d180000006f9458488000bb97d9de00021c8002409df8128000728a69bb0000998ea0000000000000000001cc0e71f706e9608bb0001e20000d81e29dc8f08490968000000001240000000a293d1900000000898000002338a7a0d8000000859c18000000b887580000000000008c91d8299b105215d8002289af9128001eb98280023280015195c1931b80000a31c280000018910497a84e0001be95a86014f1ac028963208a639b98420b98002078000001d71730000bda2998e96100000012a0d99ee92c1981988f58d31b88f00000000ed105a04a5e8001799018000000000ae25c2349801768001191ea0570e21d8166197070a50a3507708c1d994e0950000001f180022c05f80002e84da488000001b5a1a83983c01f97c00024615700c8000001ca00000000000000000011a0000b38001200001aa0000000000000000000000a38002120000000000000000000a48000000aca53013950a4324715402a9109d50000000000000000002580001488da92e87103517f9b19960000000e516a93618513816209100000000022b9678781bf9171881c88041ae8001b69a00000000050fa16c04a8e301f2090002590002610000aa9940828da18a12b2279310000000f60000000000000000001fa10f102a0680000021e00000025191f00015900006c24e8000001efa670000f50000000000bd0779d40ab0002229911c799509582300014789f0000000170001f20001a68b20000a21288000000f689480016b09ca560000000001738e00001ec8000000001f09160001d90000e685310d0000000000242171a7a028341bca358048002440fa80024d00000586b94087d9ab80000018da6595203680000023412f9078efa1a0df91b10d8850a402f0c7a038e889f8e099e19b02a0000ff8d28001858000001a88eb8002308000000cc0a080c1c30b907d04712980007e1849d88270880100dca55132a158b61bf1f800024c0000000020000000a70000bf8000000001bd00000000000002d000154a3c80007a24a14f9719680dd00000020c9e58000000001d7976192135a
  | 9 => 0x7b0001b08c
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd2018910094ff76cc910004fe76cc910004fd76cc910094fc76cc910006ef62cc910006ec62cc910015f671cc910005f571cc91000df870cc910054ff768c910004fe768c910004fd768c910054fc768c910006df638c910006dc638c910015f4718c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100357c754c910005f7714c910015f4714c910005fb704c91000df8704c910054ff760c910004fe760c910004fd760c910054fc760c910006df630c910096dc630c910006ef620c910056ec620c910015f6710c910005f5710c91000dfa700c910005f9700c91000df4764c5100def4764c51000cf4764c510205f7754c510205f5754c5101fdf7744c5101fdf5744c5101ef77544c5101ef75544c510015f7734c510017d7734c510007d7634c510096f6634c510096f4634c510007d4634c5101efd6434c5101efd5434c510005f4724c510007d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100dff0704c510016f7604c510017f3604c5100dff2504c5101f7f1504c5100dff2404c5101eff1404c5100dff0304c5100dff2204c51000df676c85100c6f676c851000cf676c85101e5f775c85101e5f575c85101ddf774c85101ddf574c85101cf7754c85101cf7554c8510005f773c8510005f573c8510015f672c8510017e672c8510006f762c8510007e762c8510006f562c8510007e462c85101cfe642c85101cfe542c851000df670c85100c7f270c8510007f170c851000df470c8510016f760c8510017f360c85100c7f250c85101d7f150c85100c7f240c85101cff140c85100c7f030c85100c7f220c8510015fa76cc11008efa76cc110014fa76cc1101c5fb75cc1101c5f975cc1101bdfb74cc1101bdf974cc1101af7b54cc1101af7954cc11000dfa73cc11000fda73cc110006fb63cc110007db63cc110006f963cc110007d863cc1101afda43cc1101afd943cc110005f972cc110015fa71cc11008ff271cc110007f171cc110015f871cc11000efb61cc11000ff361cc11008ff251cc1101b7f151cc11008ff241cc1101aff141cc11008ff231cc110007f131cc110007f321cc11008ff021cc110015f8764811003ef87648110014f876481101a5fb75481101a5f9754811019dfb744811019df9744811018f7b544811018f795448110005fa7348110005f8734811000dfb724811000feb7248110007eb6248110056fa6248110056f86248110007e8624811018fea424811018fe94248110007ea3248110007e93248110007f37148110015fa7148110015f8714811003ff0714811000efb614811000ff3614811003ff25148110197f1514811003ff2414811018ff1414811003ff23148110007f13148110007f3214811003ff02148110
  | 1 => 0x8d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d10004fd7458d1001cfc7458d10006bc7458d1001cbc7458d100067f5458d100067d5458d10006df7358d10006de4358d10006dd4358d10004ff7258d10006ef7258d10004ef7258d10054fc7258d10006ec7258d10004ec7258d100f4ff7158d10006f77158d100dcff7058d10006fb7058d100def83058d1023cfe7618d10006dd6318d10094ff7518d10024fe7518d10004fd7518d10094fc7518d10094ff7418d1001cfe7418d10004fd7418d10094fc7418d100067f5418d100067d5418d10094fe7318d10096de7318d10054fe7218d10004fd7218d1000cff7118d10014fe7118d1000cfd7118d10096f57118d10014fc7118d10096df3118d10096f63118d10236dd3118d10014ff7018d1000cfe7018d10014fd7018d1000cfc7018d10096df3018d1022edd3018d10004ff75d8910024fe75d8910004fd75d8910024fc75d8910004ff74d891001cfe74d8910004fd74d891001cfc74d89100067f54d89100067d54d8910094fe73d8910004fd73d891000cff71d891000cfd71d891021ef571d8910226ef21d8910226ed21d8910226f421d8910014ff70d8910014fd70d891021eef20d891021eed20d89100acfd7698910006ef62989100adf5719891003df97098910054ff7598910024fe7598910004fd7598910054fc7598910054ff749891001cfe7498910004fd7498910054fc74989100067f54989100067d5498910094fe7398910004fd7398910054fe7298910056ee4298910006ed42989100acfd7198910056f571989100c4fd7098910056f97098910056fa20989100057f75589100357c7558910005bf745891002dbc7458910005df7358910005dc73589100c5f7715891005dfb7058910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe7458910004fd745891001cfc7458910006bc745891001cbc74589100067f54589100067d5458910004ff7358910006df7358910004df7358910094fc7358910006dc7358910004dc7358910006ef7258910006ee4258910006ed42589100c4ff7158910006f7715891003ef421589100acff7058910006fb705891021cfe7618910006ed6218910054ff7518910024fe7518910004fd7518910054fc7518910054ff741891001cfe7418910004fd7418910054fc74189100067f54189100067d5418910094fe7318910004fd7318910054fe7218910056ee721891000cff7118910014fe711891000cfd7118910014fc7118910056ef2118910216ed2118910014ff701891000cfe7018910014fd7018910056f9701891000cfc7018910056ef2018910056fa201891020ee
  | 2 => 0x10dee768c920006ee768c920275ef748c920275ed748c92026f6f548c92026f6d548c92013ded738c920096ee638c920096ec638c92026fce438c92026fcd438c92000dee708c92000dec708c920056ef608c92015fea108c920094ff764c92000cfe764c92013cfd764c92000cfc764c9200057f754c92004d7c754c920006df634c920006dc634c920005fb704c92000df8704c92000dec764c92013eec764c92000cec764c9200076f754c9202676c754c92025def744c92025ded744c9202576f544c9202576d544c920007cf734c920007cf634c920096ee634c920096ec634c920007cc634c920007eb704c92000dee704c92000dec704c92013fe8704c92013eef604c92013fea104c92015cfe760c92015dee720c920014fe76d852003ef661d8520004ff75d8520024fe75d8520004fd75d8520024fc75d8520004ff74d852001cfe74d8520004fd74d852001cfc74d85200067f54d85200067d54d8520094fe73d8520004fd73d852000cfd72d8520014fc72d8520006ee42d8520006ed42d852003ef621d852000cfe70d852000cfc70d85200c6f710d85200057f755852004d7c7558520005bf7458520045bc7458520005df7358520005dc735852003ef46158520004fe76cc520004fd76cc520094fc76cc520005ee72cc520005ed72cc520007cd32cc520004ff764c520004fe764c520004fc764c520007cd324c52020cfe76c8520016f661c852000df870c852000cfc76485200057f754852004d7c7548520006f76148520016f46148520005fb704852000df8704852000dfa76c812000efa76c812000cfa76c812024f7b54c812024f7954c812000dfa72c812000fea72c812000efb62c812000feb62c8120057ea42c812024fe942c8120057ea32c8120007e932c8120005f971c8120004ff75d8d10024fe75d8d10004fd75d8d10024fc75d8d10004ff74d8d1001cfe74d8d10004fd74d8d1001cfc74d8d100067f54d8d100067d54d8d10054fe72d8d10004fd72d8d1000cff71d8d1000cfd71d8d10246df31d8d10246dd31d8d10014ff70d8d10014fd70d8d10246f970d8d1023edf30d8d1023edd30d8d1023ef830d8d100dcfd7698d10006df6398d100ddf57198d10075f97098d10094ff7598d10024fe7598d10004fd7598d10094fc7598d10094ff7498d1001cfe7498d10004fd7498d10094fc7498d100067f5498d100067d5498d10094fe7398d10096de4398d10006dd4398d10054fe7298d10004fd7298d100dcfd7198d10096f57198d10096f63198d100f4fd7098d10096f97098d100057f7558d100357c7558d10005bf7458d1002dbc7458d10005ef7258d10005ec7258d100f5f77158d1008dfb7058d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c755
  | 3 => 0xe438cb20297cd438cb2000dee708cb20057ea708cb20057e9708cb2000dec708cb20174ff764cb200057f754cb2006d7c754cb20175ef764cb20006ef764cb200076f754cb2028f6c754cb20285ef744cb20285ed744cb2027f6f544cb2027f6d544cb20057cf734cb20096ee634cb20096ec634cb2000dee704cb2000dec704cb20014ff7658720056f46158720004ff7558720024fe7558720004fd7558720024fc7558720004ff745872001cfe7458720004fd745872001cfc74587200067f54587200067d5458720004ff7358720094fc7358720014fd725872000cfc7258720006ee4258720006ed4258720056f72158720056f421587200aefa20587200aef71058720094ff76cc720054fe76cc720004fd76cc720096de63cc720006dd63cc720055ee72cc720005ed72cc720007cd32cc720004ff764c720004fd764c720054fc764c720006de634c720006dd634c720007cd324c72021cff76487200057f754872006d7c7548720004ff75d8d20024fe75d8d20004fd75d8d20024fc75d8d20004ff74d8d2001cfe74d8d20004fd74d8d2001cfc74d8d200067f54d8d200067d54d8d20006df53d8d20006dc53d8d20006de43d8d20006dd43d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20006dc31d8d20054ff70d8d2015cfd70d8d2015edf30d8d2015edd30d8d20006df6398d2013ded7298d20094ff7598d20024fe7598d20004fd7598d20094fc7598d20094ff7498d2001cfe7498d20004fd7498d20094fc7498d200067f5498d200067d5498d20094fe7398d2013cfd7298d20096ed7298d20006ee4298d20006ed4298d20014fe7198d20004fd7198d20014fc7198d20174fd7098d20096f97098d20176fa1098d200057f7558d2004d7c7558d20175ef7258d20004ff7558d200067f7558d200047f7558d20024fe7558d20004fd7558d20024fc7558d200067c7558d200247c7558d20004ff7458d2001cfe7458d20004fd7458d2001cfc7458d200067f5458d200067d5458d20006df7358d20174ff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d2013cff7058d20006fb7058d2015cfe7618d20006dd6318d20094ff7518d20024fe7518d20004fd7518d20094fc7518d20094ff7418d2001cfe7418d20004fd7418d20094fc7418d200067f5418d200067d5418d20096de7318d20006df5318d20096dc5318d20096de4318d20006dd4318d20054fe7218d20096ed7218d20054fc7218d20006ee4218d20006ed4218d20014fe7118d20004fd7118d20014fc7118d20006de3118d20096dc3118d20054ff7018d2010cfd7018d20096df3018d2010edd3018d2010efa1018d2000cfe76cc92000cfc76cc920006df63cc920096dc63cc92000dfa70cc920005f970cc92010cfe768c920
  | 4 => 0x8530004fd75d8530024fc75d8530004ff74d853001cfe74d8530004fd74d853001cfc74d85300067f54d85300067d54d853000cfd73d8530014fc73d8530006de43d8530006dd43d8530054fe72d8530004fd72d8530076f631d85300f6f830d85300f6f710d85300057f75585300857c75585300067f65585300067c6558530005bf745853007dbc7458530005ef7258530005ec7258530076f4615853022cfe76cc5300067f65cc5301067c65cc530097d830cc53000cfc764c5300067f654c5300ee7c654c530006f7614c530016f4614c530005fb704c53000df8704c5300dfd8304c530004fe76c8530004fd76c8530054fc76c85300067f65c85300d67c65c8530004ff7648530004fe7648530004fc76485300057f75485300857c75485300067f65485300be7c654853000dfa76cc13000efa76cc1300077b65cc1302af7865cc1302a77b54cc1302a77954cc13000dfa73cc13000fda73cc13000efb63cc13000fdb63cc130097da43cc1302a7d943cc130006fb61cc130054ff75d8f20024fe75d8f200567e75d8f200247e75d8f20004fd75d8f200567d75d8f200047d75d8f20054fc75d8f20054ff74d8f2001cfe74d8f20056be74d8f2001cbe74d8f20004fd74d8f20056bd74d8f20004bd74d8f20054fc74d8f200067f54d8f200067d54d8f20006de43d8f20006dd43d8f20054fe72d8f20056ee72d8f20014fe71d8f20004fd71d8f20014fc71d8f20056f970d8f2013cfd7698f20056df6398f20094ff7598f20024fe7598f20004fd7598f20094fc7598f20094ff7498f2001cfe7498f20004fd7498f20094fc7498f200067f5498f200067d5498f2000cfe7298f20096ee7298f2000cfc7298f20006ee4298f20006ed4298f20056de3298f20056dc3298f20014fe7198f20004fd7198f20014fc7198f20096df3098f20176dd3098f20056dc6358f20004ff7558f20024fe7558f20004fd7558f20024fc7558f20004ff7458f2001cfe7458f20004fd7458f2001cfc7458f200067f5458f200067d5458f20056df7358f20094ff7258f2000cfe7258f2013cfd7258f2000cfc7258f20056de3258f20056dc3258f20004ff7158f20014fe7158f20014fc7158f2013edf3058f2013edd3058f20054ff7518f20024fe7518f20004fd7518f20054fc7518f20054ff7418f2001cfe7418f20004fd7418f20054fc7418f200067f5418f200067d5418f20094fe7318f20056de7318f20096de4318f20006dd4318f20054fe7218f20056ee7218f20056ee4218f20006ed4218f20014fe7118f20004fd7118f20014fc7118f20056f97018f2013cfd76ccb2000ded768cb20056ed768cb2000ced768cb20055ef748cb2029ded748cb202976f548cb202976d548cb20096ee638cb20057ce638cb20057cd638cb20056ec638cb20297c
  | 5 => 0x4ff7258730054fc7258730096f73158730096f431587300def7105873023cff764c730016f4614c73000dfa704c730054ff76c8730094fe76c8730004fd76c8730004ff7648730004fd7648730094fc76487300057f75487300a57c75487302bd7e76d95300867e76d95300247e76d95300057f74d95300057d74d95300067f64d95300067e64d95300067d64d95300067c64d95300075e43d95300075d43d95300067e61d95300067c61d95302b75e30d95302b75c30d95302b77830d95300067f74d95300047f74d95300067e74d95300067d74d95300047d74d95300067c74d95302b67f73d95300867e73d95302b67d73d95302b67c73d95300067f43d95300067e43d95300067d43d95300067c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95300067e31d95300067c31d95300067e21d95300067c21d95302b67f70d95302b67e70d95302b67d70d95302b67c70d95302b67f40d95302b67e40d95302b67d40d95302b67c40d95302b67f30d95302b67e30d95302b67d30d95302b67c30d95302b67f20d95302b67e20d95302b67d20d95302b67c20d95302b67f10d95302b67e10d95302b67d10d95302b67c10d95300067f65d89300067c65d8930004ff75d8930024fe75d8930004fd75d8930024fc75d8930004ff74d893001cfe74d8930004fd74d893001cfc74d89300067f54d89300067d54d8930006ee42d8930006ed42d8930014fe71d8930004fd71d8930014fc71d8930006ee21d8930006ec21d8930176ef20d89300857e75989300057d75989300067f65989300067c659893007dbe7498930005bd7498930006ef62989300057f75589300857c75589300067f65589300067c65589300067f65189300067c6518930006ed6218930054ff7518930024fe7518930004fd7518930054fc7518930054ff741893001cfe7418930004fd7418930054fc74189300067f54189300067d5418930006de4318930006dd4318930056ee4218930006ed4218930014fe7118930004fd7118930014fc7118930006ee2118930056ec2118930056ef201893010eed201893010cfe76cc9300067f65cc9301867c65cc930097d830cc93000cfe768c9300067f658c93016e7c658c930006ef628c930056ec628c93000dfa708c930005f9708c93000cfc764c9300057f754c9300857c754c9300067f654c9301567c654c930006ef624c930006ec624c930005fb704c93000df8704c93013fd8304c930174fe760c9300067f650c9301267c650c930014fe76d85300067f65d85300067c65d8530076f661d8530004ff75d8530024fe75d
  | 6 => 0xf7258d21144ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21164fe7618d210067f6518d210067c6518d21006dd6318d21094ff7518d21024fe7518d21004fd7518d21094fc7518d21094ff7418d2101cfe7418d21004fd7418d21094fc7418d210067f5418d210067d5418d21096de7318d21096de4318d21006dd4318d21006ee4218d21006ed4218d21054ff7118d21114fd7118d21096df3118d21116dd3118d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d21096dc3018d21014fe76cc921014fc76cc9210067f65cc9211867c65cc921006df63cc921096dc63cc921015f671cc921005f571cc921114fe768c9210067f658c92116e7c658c921057e4218c921094ff764c921014fe764c921144fd764c921014fc764c9210057f754c9210bd7c754c9210067f654c9211567c654c921006df634c921006dc634c921005f7714c921015f4714c921147e4214c921164fe760c9210067f650c9211267c650c9210077765c85212cf7465c85212c77754c85212c77554c8521015f672c8521017e672c8521016f762c8521017e762c8521057e642c85212c7e542c852100cfe76d81210067f65d81210067c65d81210aefa60d8121004ff75d8121024fe75d8121004fd75d8121024fc75d8121004ff74d812101cfe74d8121004fd74d812101cfc74d81210067f54d81210067d54d8121094fe73d8121004fd73d8121014fd72d8121006ee42d8121006ed42d812100cfc71d8121006f721d812105ef421d81210aefa20d81210aefa10d81210057f75581210bd7c75581210067f65581210067c6558121005bf74581210b5bc7458121005df7358121005dc73581210aef86058121096ef6298b30054ff7598b30024fe7598b30004fd7598b30054fc7598b30054ff7498b3001cfe7498b30004fd7498b30054fc7498b300067f5498b300067d5498b3000cfe7398b30006de4398b30006dd4398b30096ef3298b30056ec3298b30014fe7198b30004fd7198b30014fc7198b30056ef2098b3015eed2098b300057f7558b300a57c7558b30096ec6258b30004ff7558b300067f7558b300047f7558b30024fe7558b30004fd7558b30024fc7558b300067c7558b300247c7558b30004ff7458b3001cfe7458b30004fd7458b3001cfc7458b300067f5458b300067d5458b3000cfc7358b30096ef3258b30096ec3258b30004ff7158b30014fe7158b30014fc7158b3013eef2058b3013efa1058b3013cfd768cb3015cff764cb300057f754cb300a57c754cb30014ff7658730096f46158730004ff7558730024fe7558730004fd7558730024fc7558730004ff745873001cfe7458730004fd745873001cfc74587300067f54587300067d5458730014fd735873000cfc7358730006de4358730006dd4358730
  | 7 => 0xcb2100cff7658321056f86058321004ff7558321024fe7558321004fd7558321024fc7558321004ff745832101cfe7458321004fd745832101cfc74583210067f54583210067d5458321004ff7358321094fc7358321014fc7258321006ee4258321006ed4258321056fb2058321056f820583210c6fa10583212dd7e76d95210be7e76d95210247e76d95210057f74d95210057d74d95210067f64d95210067e64d95210067d64d95210067c64d95210076e42d95210076d42d95212d76e21d95212d76c21d95212d77421d95210067e60d95210067c60d95210067f74d95210047f74d95210067e74d95210067d74d95210047d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d95212d67f72d95210be7e72d95212d67d72d95212d67c72d95210067f42d95210067e42d95210067d42d95210067c42d95212d67f71d95212d67e71d95212d67d71d95212d67c71d95212d67f41d95212d67e41d95212d67d41d95212d67c41d95212d67f31d95212d67e31d95212d67d31d95212d67c31d95212d67f21d95212d67e21d95212d67d21d95212d67c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d95210067e30d95210067c30d95210067e20d95210067c20d95212d67f10d95212d67e10d95212d67d10d95212d67c10d95210067f65d8d210067c65d8d21004ff75d8d21024fe75d8d21004fd75d8d21024fc75d8d21004ff74d8d2101cfe74d8d21004fd74d8d2101cfc74d8d210067f54d8d210067d54d8d21006de43d8d21006dd43d8d21054ff71d8d21164fd71d8d21166df31d8d21166dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d210bd7e7598d210057d7598d210067f6598d210067c6598d210b5be7498d21005bd7498d21006df6398d21145ed7298d21094ff7598d21024fe7598d210967e7598d210247e7598d21004fd7598d210967d7598d210047d7598d21094fc7598d21094ff7498d2101cfe7498d21096be7498d2101cbe7498d21004fd7498d21096bd7498d21004bd7498d21094fc7498d210067f5498d210067d5498d21094fe7398d21144fd7298d21096ed7298d21006ee4298d21006ed4298d2117cfd7198d21096f57198d2100cfe7098d21004fd7098d2100cfc7098d210057f7558d210bd7c7558d210067f6558d210067c6558d2117def7258d21004ff7558d210067f7558d210047f7558d21024fe7558d21004fd7558d21024fc7558d210067c7558d210247c7558d21004ff7458d2101cfe7458d21004fd7458d2101cfc7458d210067f5458d210067d5458d21006df7358d2117cff7258d21006e
  | 8 => 0x14fe768c931145dd738c931006ef628c931056ec628c931015f6718c931005f5718c931014fc764c9310057f754c9310ed7c754c931006ef624c931006ec624c931005f7714c931015f4714c931015dc764c931146dc764c931014dc764c9310075f754c9312ff5c754c9312f5df744c9312f5dd744c9312ef5f544c9312ef5d544c931007cf724c931007cf624c931056dc624c931007cc624c931007d7714c931015de714c931015dc714c931147d4714c931146df614c931147d7104c93117cfe760c93117dde730c9312e77754cc5312e77554cc531015f673cc531017d673cc531016f763cc531017d763cc531097d643cc5312e7d543cc531097d732cc531007d532cc531005f570cc53100cfe76d81310defa60d8131004ff75d8131024fe75d8131004fd75d8131024fc75d8131004ff74d813101cfe74d8131004fd74d813101cfc74d81310067f54d81310067d54d8131014fd73d8131006de43d8131006dd43d8131054fe72d8131004fd72d81310defa30d81310defa10d81310057f75581310ed7c7558131005bf74581310e5bc7458131005ef7258131005ec72581310def86058131054ff75d8f21024fe75d8f21004fd75d8f21054fc75d8f21054ff74d8f2101cfe74d8f21004fd74d8f21054fc74d8f210067f54d8f210067d54d8f21006de43d8f21006dd43d8f21054fe72d8f21056ee72d8f21056f571d8f2100cfe70d8f21004fd70d8f2100cfc70d8f21166f710d8f21144fd7698f21056df6398f21094ff7598f21024fe7598f21004fd7598f21094fc7598f21094ff7498f2101cfe7498f21004fd7498f21094fc7498f210067f5498f210067d5498f21014fe7298f21014fc7298f21006ee4298f21006ed4298f21056de3298f21056dc3298f21096df3198f2117edd3198f2100cfe7098f21004fd7098f2100cfc7098f210057f7558f210d57c7558f21056dc6358f21004ff7558f210067f7558f210047f7558f21024fe7558f21004fd7558f21024fc7558f210067c7558f210247c7558f21004ff7458f2101cfe7458f21004fd7458f2101cfc7458f210067f5458f210067d5458f21056df7358f21014fe7258f21014fc7258f21056de3258f21056dc3258f21146df3158f21146dd3158f21004ff7058f2100cfe7058f2100cfc7058f21146f71058f21054ff7518f21024fe7518f21004fd7518f21054fc7518f21054ff7418f2101cfe7418f21004fd7418f21054fc7418f210067f5418f210067d5418f21094fe7318f21056de7318f21096de4318f21006dd4318f21054fe7218f21056ee7218f21056ee4218f21006ed4218f21056f57118f2100cfe7018f21004fd7018f2100cfc7018f21144fd76ccb21056df63ccb21056dc63ccb2117cff764cb210057f754cb210d57c754cb21056df634cb21056dc634
  | 9 => 0xd4258032006ee3258032006ed3258032004ff7158032014fe7158032014fc715803210efa5058032006f9505803210efa4058032006f94058032096fb3058032096f83058032056fb2058032056f8205803210efa1058032096ef6298b31054ff7598b31024fe7598b31004fd7598b31054fc7598b31054ff7498b3101cfe7498b31004fd7498b31054fc7498b310067f5498b310067d5498b31014fe7398b31056de7398b31006de4398b31006dd4398b31096ef3298b31056ec3298b31056ef2198b31166ed2198b3100cfe7098b31004fd7098b3100cfc7098b31096ec6258b31004ff7558b31024fe7558b31004fd7558b31024fc7558b31004ff7458b3101cfe7458b31004fd7458b3101cfc7458b310067f5458b310067d5458b31014fc7358b31096ef3258b31096ec3258b31146ef2158b31004ff7058b3100cfe7058b3100cfc7058b31015dd76ccb31096dd76ccb31014dd76ccb31095df74ccb31335dd74ccb3132f5f54ccb3132f5d54ccb31056de62ccb31097ce62ccb31097cd62ccb3132fce42ccb3132fcd42ccb31015de71ccb31097d671ccb31097d571ccb31015dc71ccb31144fd768cb31164ff764cb310057f754cb311057c754cb31165df764cb31006df764cb310075f754cb313275c754cb3131ddf744cb3131ddd744cb313175f544cb313175d544cb31097cf724cb31056de624cb31015de714cb31015dc714cb3100cff7658331096f86058331004ff7558331024fe7558331004fd7558331024fc7558331004ff745833101cfe7458331004fd745833101cfc74583310067f54583310067d5458331014fc7358331006de4358331006dd4358331004ff7258331054fc7258331076f63158331096fb3058331096f830583310f6fa1058331004ff75d8931024fe75d8931004fd75d8931024fc75d8931004ff74d893101cfe74d8931004fd74d893101cfc74d89310067f54d89310067d54d8931006ef52d8931006ec52d8931006ee42d8931006ed42d893117eef21d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d8931006ef62989310057f75589310ed7c7558931006ed6218931054ff7518931024fe7518931004fd7518931054fc7518931054ff741893101cfe7418931004fd7418931054fc74189310067f54189310067d5418931056dd7318931006de4318931006dd4318931006ef5218931056ec5218931056ee4218931006ed4218931056ef2118931116ed211893100cfe7018931004fd701893100cfc7018931006ee2018931056ec2018931116f71018931114fe76cc931115de76cc931006de76cc93130ddf74cc93130ddd74cc9313075f54cc9313075d54cc931056dc62cc931307ce42cc931307cd42cc931015de71cc931015dc71cc931096df61cc93117fd710cc931
  | 10 => 0x95320067f65cc9321867c65cc9320076f65cc93238f6c65cc932386ef64cc932386ed64cc9323876f54cc9323876d54cc932005ed70cc9320067f658c93216e7c658c9320075f658c93237f5c658c932376df648c932376dd648c9323775f548c9323775d548c932007cf628c932005dd718c932014fe76d85320067f65d85320067c65d8532146f661d8532004ff75d8532024fe75d8532004fd75d8532024fc75d8532004ff74d853201cfe74d8532004fd74d853201cfc74d85320067f54d85320067d54d8532006f741d8532146f441d8532146f631d8532146f621d853200cfe70d8532004fd70d853200cfc70d8532146f710d85320057f75585321557c75585320067f65585320067c6558532146f4615853200cfe76d81320067f65d81320067c65d813213efa60d8132004ff75d8132024fe75d8132004fd75d8132024fc75d8132004ff74d813201cfe74d8132004fd74d813201cfc74d81320067f54d81320067d54d8132014fe71d8132004fd71d8132014fc71d8132006fb40d813213ef840d813213efa30d813213efa20d813213efa10d81320057f75581321557c75581320067f65581320067c655813213ef86058132095df74cc83236ddd74cc8323675f54cc8323675d54cc832055dd72cc832056de62cc832057ce42cc832367cd42cc832055ef748c83235ded748c8323576f548c8323576d548c832095ed738c832096ee638c832057ce638c832097ce438c832357cd438c832004ff764c8320057f754c8321257c754c832055df764c832006df764c832004df764c8320075f754c8323475c754c83234ddf744c83234ddd744c83233f5f544c83233f5d544c832055df724c832056de624c832057ce524c832347cd524c832057ce424c83233fcd424c832095ef764c832006ef764c832004ef764c8320076f754c8323476c754c83234def744c83234ded744c83233f6f544c83233f6d544c832055ef734c832057cf734c832096ee634c832097ce634c832097ce534c832347cd534c832097ce434c83233fcd434c832014ff7658432056f46158432004ff7558432024fe7558432004fd7558432024fc7558432004ff745843201cfe7458432004fd745843201cfc74584320067f54584320067d5458432006de4358432006dd4358432006ee4258432006ed4258432006df3258432006dd3258432116f65158432006f55158432116f64158432006f54158432096f73158432096f43158432056f72158432056f42158432004ff705843200cfe705843200cfc7058432116f7105843200cff7658032056f86058032004ff7558032024fe7558032004fd7558032024fc7558032004ff745803201cfe7458032004fd745803201cfc74580320067f54580320067d5458032006de4358032006dd4358032006ee4258032006e
  | 11 => 0xd00d00700100600200600100000000200600000000600000000301d00000e00400002800300c00000000500e002002014ff7658732096f46158732004ff7558732024fe7558732004fd7558732024fc7558732004ff745873201cfe7458732004fd745873201cfc74587320067f54587320067d5458732006ee4258732006ed4258732096f73158732096f4315873217ef62158732004ff705873200cfe705873200cfc705873217ef7105873200cff7658332096f86058332004ff7558332024fe7558332004fd7558332024fc7558332004ff745833201cfe7458332004fd745833201cfc74583320067f54583320067d5458332006ee4258332006ed4258332004ff7158332014fe7158332014fc7158332096fb3058332096f83058332176fa2058332055dd76cca32006dd76cca323a5df74cca323a5dd74cca3239f5f54cca3239f5d54cca32057ce52cca32397cd52cca32005ed76cca32096ed76cca3239eef64cca3239eed64cca3239f6f54cca3239f6d54cca32097ce53cca32397cd53cca32005ed70cca32014ff7658632056f46158632004ff7558632024fe7558632004fd7558632024fc7558632004ff745863201cfe7458632004fd745863201cfc74586320067f54586320067d5458632006de4358632006dd4358632006df3258632166f63158632056f72158632056f42158632004ff705863200cfe705863200cfc705863200cff7658232056f86058232004ff7558232024fe7558232004fd7558232024fc7558232004ff745823201cfe7458232004fd745823201cfc74582320067f54582320067d5458232006de4358232006dd4358232004ff7158232014fe7158232014fc715823215efa3058232056fb2058232056f8205823215efa10582321557e76d95321567e76d95320247e76d95320057f74d95320057d74d95320067f64d95320067e64d95320067d64d95320067c64d95320067e61d95320067c61d95320067e60d95320067c60d95320067f74d95320047f74d95320067e74d95320067d74d95320047d74d95320067c74d95320067f73d95321567e73d95321567d73d95321567c73d95320067f43d95320067e43d95320067d43d95320067c43d95320067f72d95321567e72d95321567d72d95321567c72d95320067f42d95320067e42d95320067d42d95320067c42d95321567d32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320067e41d95320067d41d95320067c41d95320067e31d95320067c31d95320067e21d95320067c21d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067e40d95320067d40d95320067c40d95320067e30d95320067c30d95320067e20d95320067c20d95320067f10d95320067e10d95320067c10d
  | 12 => 0x2c6b20000000000009aac28000000790576c26018b7622000000000000000000000000056e0006ec000000000f540fabd471a23400100100400200200000900200000400100c00100000000200200a00000000100000500200300300000000702300d00700000301301300300000000000001300100b01000200000000800001600100e01100500100a00000600701200000400500300200c00400700500300200001100200200600000000100600500000200d00300100001c00000600300400600200002f00000000100000400000a00400000600300f00400100e00200d00400000100101300100100000302f00101100a00000000602d04100000200800100800003500f00000000203100200000100000a00600d00200002200400700400300202d00101500200100500300000600000300500000d00200200500000200c00200500800200f00700000001300000100601501202501100700300000500000300200700000000001000300300700500100400001400400500000000600400600300000702900300400200900000900000000200700100000600000100500400700c00200700600100f00000400602400100500002100000c00800101600000000c00100000c00700500100400200f01d00001100c00000200000000b00000400902000900400200900300000402500c00100300700100d00201f00c00d00600300400201400100400000300000700000800000000000100000800200c00003000b01001500e00800201a00200200100201400000600200000400000300700800500d00000a00100100600f00100700300200400500100000100400800200000202200200501c00700800100100000000401c00903200400100000200800000200600100000700200100100f00300e00001d00700400401201e00200b00001b00002500101a00000000000400000001900001300500400201b00000100000200a00000e00500d00000200000002c00500100000300500100000000000300c00000a00200400900000500f00a00200701a00400500003d00500201100c01800601103400100000f01100800101100a00800100000400600200500000200100000000000000900502a00101f00000900401000100000000300100a02900000001d00400000000400300000000200000000000000000000300200101d00600001400100a00100100e00300000b00600700100100201700100000700300300002400d00800700200100701100100200100200000000100700700300300201701000300700500f00000400300500200000400000e00000500400100501000000800100500500100000100200101200400c00100500202800000900b00b00000000000500a01e002001011002000005001000002011001000000006002001005015
  | 13 => 0x827c1b2000cbabc283c092066974000000df400000079e3be000000fbefa68e83ba5d284c944000fe064a9220000007848ce000000210df83700000622dcbbad78b84f3801c53e3a82767a8e247e2000988000000c5afb88d40002a40b8248570000a469a0fce0000000fc060a68708000000550000000a8686c30e68a23cad6b5abfa000f86122c7e940f823aa864728f0024681a55a52c3345282e4610e4a6a045064e4aa25848c89a740a843dc582e1c45c590d8292c3d6abc79ab940c429403866e0461b61b062e054340ad8170d2a000000f88d80c84000b4e9da000000ee00000006123ea75a000adc3d4000000bc4f722b0e147c4a5e782c44e7ecf85aabce97ec92000eaad2437aa8c5e600038439a000000000a4ed040002fcdfa000bf8388804dc4a52a30a34f50f8e1f000069a000dd00006e257a2f00004725e2000000000000000ce000c000f100000005d43de48ee4e98a0000000000001800000006980000009129f20000004367b28ecbc600070a00000006ec8e81c648ca29f6a928a68a8bee0000005fc000986b462cc0caeca382b7216ce68b3ce3c24c4ce446ab05a80d852020cc34ef458a07c6386ca462b044b43602de7bc8cc78c35e000c38bf24c09680200001b8d429180000000008bad3c03e5b20008589ba000000b7a000e360000000008b2840bae21800000000000022401639e000d3a00000061676c67ea1a7dc000a48000000a1c3e098c56cdec4ac3441762e8296f84000aaa786dfe000dcaf96d3ee4200083ebbe6a807ac7800030ce640000000005dc000182618f8c0000b000004a000fe8000716d884c6202da09d69bec4c5a4d4c0000ecfc8000978868000000022000000f5a2d0688650a600daee4c4084468c92e00080c40e214000a8201228abb052e8d06360000009c8ae00006c60007b83280002da078000000000000c8cc4a4d055869c000ca8baab40000d1c1d640087a88a44e8f8000b881f40005c6330d2ed90a9e72a73c58ccc0000ac0d5c00082ce3000000074caca00009a0004381c8000964000a38000000000a7aa9443ae7c0007e073291ae62e581a80000000009c2db4000a665f2768eba0dc030b669b2000dcc000000000000546000efa33c3142d8ee6e6a0005b40000002087aa00003c22eaba6608c465472426eeb0000000710e4647c2e6002b3409815aa9c97629e0000000e0000bd20004045a6eb4f1a3cee98d7224023e7ea8487b0f2e7ae0007760000008e477c6acb5ed926827346bc7ce29ca086c2bdc322a3a0d2b1ecd83f800063a4de8bed0e9de99e40246400008e3f4f12e8220ae54be200000000008400007e5c09ea000f300e2000b9e0001a693a9fe000000000c86c6ab287e89ecd2834c920000000d603face2e6cd38290a0261a54a4d4252366a62e50000930a742
  | 14 => 0x2f4000116f22db8f58894000f7e952764674000000792c5ec60de694af2c268c0ee80faeb82e6020024290a9a25de352c6ea14000f5e5b86fc000000000b96000926000f2a25ac0400000000017c5f61f8000f0c1480000002a255c000b2c5ec00000034a06a14e54001400000000000000038aa80000134f7a000d840000ae292000000e7600000000030000027a000e5a000146bf08d672c87c73a000d565601ec00016400028441280651e226324d1a3e6b02644e3a3a429a8aac8a588c2a4a0b2636ae26680000b48f24000de43da216fd24ae6badde6ccb1600062cf44074b14eda00efd00f0000e047d25f4c6281099235048a84a0000009cc1e0000000a20000e9c8b4f46e00000456114e86000000042e06942eec96c624f3a87eb2e9d4982dce59c722000000d9617814afa4000e90000000000000cda0000006b0000414fc00000000007943720000b400017245a30afec00064c000b980aa000000ed888c4e8ada1aec0094627044af022be66c0005a2aa28ae0002d621a69ebf44fc000b20e083260000008de00002cc10f4e000d68cc8000900c2cb3ec646b8fb011c23aaec6b4cd6cd4000ea6fbac94afc37600040c0008340826fe7c8bd8318000e70ad09d0c566ead4465ce3e882d7c0007583d20e8000896000000f4ac7c3c4466506628e88aea2fa874d06d8a3d0e8e38ccc200028e0009d88ee16a4e2b4222874e304788696090772c48b743ac5e4d8e93c2ec3ee24eecc3a294804c8240002fe0004b6000ade5c47487ccaf2eeef28d9e000c2200025ce0ac2e958662346000eb28ac678742668160b786a654c9560bacccc1e554de000456851c67c0765ea43e41caa46e6692d105804ea74a756000ca07de90ea1e542a241d0e022884d8d408803bc83846a7f039cfcc5086da0009f4bfcc5c52400043cf3cbde3c27bab8c910ba242ccf2a4220617a7fa598374d18256ab8b448360cc50a0008d2bb8a00ac21904fafd400079cb546c02741304d605ec80000f3e94e0000000007fee2e85c7d6cdcddcbe67501427f8420000434774b6a8f48e69b8ace000ae6714b58d1244cebcb1014ccb45b050000000097032a000000000000000e520000001000004323965a0f80cea0004a63b6000afefa8000000348358000f765660000006aef6eaf40005384eeed65484e000000000000030604e0006d20001e86aa8624a4c50e8a6faef036822afc2fd61549ce65eb9cac446e452f4cc908606d6be4cf6000828d52504744d2200000000067097a00082e904a0a0acf74a5063e00047632cfde57c39449a0003a626a5f0000928000a761d80000000000008e00005e081200045400000000015eaacabee20a2c822f181a49acda26426e44b065209c238194ec4278b1a000096332000000ef22303c8a569602bac14e0cba083a000d5
  | 15 => 0x300004600001a0f645260003c054e5c805a00035c000000000a5ae2c00011eaf895e000b4a82a000000000000000000808fee7cab6e272544a6cdeac7061cfea05c000000712efc000a2646c120bb40f4000f14e926f2040c54eeadda55226ce189b6d62260ee876a9b44a2a4a86a57e706dd680e18e980592fe48daa44e16254f087a4f709940a889ed8666410201aca68f665aece1c0e1e9e48c8eae28244406cc66a784b857213200036cb8ae720c27d40009145d6f34c5810c5cc99a15c298d7a7dac128a40941de5daf7cd3698efb4da8108ea8c0c34e6d45aed34a3e408aa6a3ca6e000480000110b5660a034f783c652284e000ce88300ce492cbe3b4dac3f23200004d2d080000003b8000c18000fe6a22502916e568f09fcacc000a8e00038650c26612abd03aea963e8000a5c9e8000000bb64f017e4f64f200081e174000000b187b6000000d0c498000c301cc71800090c000dc2c20000bca000000000000000000b624be000fdcf5c0000000006f859e0000000000004dadbc2e25d810e9540007f69c6000c9c032f66000cfc1c4000f986c8a180fe0d67548fc000000eb80000000000001fe2b488e00000024a00087200080a4104880000be2e09500a28d80009ca632ed200093e000bcc966c3e000ab2000000ab42caf32cc40001285965e818c1362620e4f9abe07c22369904e4d98e66886b323caac850e2aa000390482996000ca4000000000000000000cde0640000001cadf0000000a0616283259a45877e0000000007ee584000852000000998c4e000656df60000000066f0a28d9c0000007267c00007a6c989a6f360005ce0001da0000006c4fbc000000a88d500008b0000da46e00367e4b64778c24a12e749f07b4510422a7cb868c0468b382d200049e8923a0000000000854000000b9a0000a61e2000028000000d460001524865f860691c5d01c6000ec0b3a7020ee1bc25e518d6619e646eb608a9323fe244f0447eea2c429bccf013edfc308000b7e55e2ee32eef800096a000ce661ec6800041896e0d0000000af6a540de1061240720687967305caa4031e5ee85021e6dc3b0000db2056d161fce5c7d0f625629841ceefe4c408841e2220f671e8b61e6c82ec8000000e942f6000424c72d4a16862aa041d2ba8934a8a586c468182c2cc65644f4802704884856686d74b22f0a6908e2c1aa4c7bebec050d2cdd85be0000000005fe00800056a9a4fa0878d0270000028c1bad9aaa8b7cb24000e9aea000092416e1960008bc7622ce9ee6dec325b6a720000005ba000d5475c10ae28280a1657468400003aa6476ea2e00000071c1e4f425bc0007ac3d87f2cec4f87980b2f060704bac9ec961b49d2a7e9a81aa97c7200000004940006221eafb2738000bea000d2033e0000001accbcf6cb12bac91e634000cac
  | 16 => 0xdaad0018a31c67a0c04ccf900b675e3f00008466946006be7a08eabda3420002c6000d5e00073e1f6e84866000d7e000000ae800000072e99c000000000c9a000e100001fa47060438e000000826fb6000150000c521044c8814a9ac3a00042e0000005acd6e2649e282013c00031a09e428f1e95ad30000144026e9e3cc2c4caeee20000000000e6000000000f8a5783e2d645c219ab36000000000000b4c8fa876e6e77a000c7458e7fc3fc080db0cb8b2a000bb2000000c08ba6512000ae2000000faa00060c000000c1678e000ba46f49aeb60426df20bcda64a866a250d482f800027e052f6047a53c3f663cd6a9e06eeb08000302166f2086ea36766800184cf4eac000000b680007ec37e00037841a0000a0000000000000000a98aa00003e48a0286c6c000000fac2a0392c8801e52ace4bfeebe000cb06200002b2e38e48e7add26a4416ede19c49c406f9236e8dc8b8ad2b8ecb6c0a02ef682329360c86d0ed4e1ab52086448bc03b2000aee92a8f2316edc7520eafd8000fe2ea4c0694c0000006f69fa6e8dbabd6f9e8882a8000000b060000005342d400012cb922c8474310f260005fa53a000440126c1c000000000a0c0c621cd26d0a380e127c660e7f40f85169c4336d5abc8ac60004ca9c0c3cc76000de2fc4cfa000a2a4bce96b30000000dee42af0e000e4c95ca1070ecd0d8c20e000e322ae000f56000b0a000000f40b5000045eb0c0008a27a24fe0000000000005941be204db60000a4112484000bbc9f8672640f52dd4000602000514a58e40ec20002b6b1c7806ce058b704dcccaaae000000000a0e000000b6c00000035408c000000000f1c0008fe9060000006b612eb80666d1e0f2898760890c7acfe198158024870000b5c0002ea0000001d437c0000009382ac8caf6ad327364eca703622f26301f20004789dc000000a6a6583ecd761869e6490b90ec6010afa11a962156fca044af0f94d94f1633acd2dc8398e44d6c972cce1a2192cb2a32356daeb0ede8e78530e0e68e51a6766a2f48000000be8e8c89cf9c000000000000e222a636400035aad4000d70fc6000312dbe61404800081600a2b86089b00001dc0005360007700002bc0004b2000000caafdab0000070c0005327461ee138cee00085ae2a442bf60d4d1413a40a2c00007d88c2212000d4e00033800002a000000a901c2118ed0fa2842e34496ae414078aab685e7e6000556000902c028c6e5e6264e60004c2000dc0ef66d8000c36dc60009081880000000000004
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc3c74d5163440010fd0eaa2c6880021f21d5458d100061fba2a8b1a2003c3c745516344007938e921ac68800e3721d4358d1001e4e3a286b1a2000e1d5450d63440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc963440018dea9b92c6880031b5537258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a2000c6f541c963440018daa8392c6880033390c7258d1000666a18e4b1a20008df8758c634400159904b18c6881e31d5c75418d1001e1f3a2a831a2000c3d7455063440ef8eae2aa0c6880021fe157218d100243e42ae431a20018f581dd762440031eb03ba6c4881e31d5c754d89100061fba2a9b122003c3c7455362440ef8eae2aa6c48800f0f9d154989100061eba2a93122000e2d5450a62440090fd0fbaac4880021f61375589100045fc22eab1220038bc845d562440011bf06baac48804a3720d75589100043f438eab1220038be87dd1624400187eebba2c4880030f1d774589100061fc2ee8b122000c3c85dd162440010ff0aba2c4880121f21574589100046fc1ae8b1220128dc835d1624400117d0e3a2c4880030fdd474589100061e3a8e8b12200087e87d5162440090f90faa2c4880030fdd3545891001e1e3a6a8b12200087e8755162440010f90eaa2c4880030fdd1545891001e1e3a2a8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f54dcd62440018baa9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac48800317d5073589100062eaa0e6b122000ccc73dc96244007958e9212c488003331ce425891001c7643a84b122003cac745096244001c5aa8a12c488003331cd425891000c7d43ee0b1220008ef87588624400159906b10c4881db1e5c3541891001e1f3a2a83122000c3d7455062440eb8f2e0aa0c4880021fe1573189100243e42ae631220018f4865c732440051f10cb8464880121fa16764c9100043ec2cec992200087f855d932440090f90abb264880022fe11764c91001c5e422ec99220008df835d932440011df04bb264880063da1b714c9100147d436e0992200087f855d832440090f90abb064880022fe11760c91001c5e422ec19220128dc835d832440151d904bb064880063d219710c91005672312e219220028f8865c032440259b0c6b8064880067ca00724c510006f1100e498a20029d4874c931440031ed0db9e42880025de1573c851000cf8402e790a20078f587d8b21440031ef0eb16428806e3e61f63cc1100147dc3ac7982200097b855cb30440053e102b96608811e7ce1d31cc110004f8c3e4398220028fa869cd20440053e50239a4088003748c4734811000cf443a6490220009f0874c52044001f826498a40881067ca1f2148110
  | 1 => 0x61baa64980021fa1f654c9302b43e43eca9926000e1d5450f614c0090fd0dbaac2980021fa1f65585300061e3a6cab0a600087e87195614c001878e832ac2980030fd9774585300061e32ee8b0a6000c6f65dc9614c0018d8cbb92c2980031bd94725853000636328e4b0a600087f855db214c0090f90abb642980121fa1776485300043ec2eec90a600487e859d9214c0010fb0b3b242980121f21476485300043f436ea90a600087e87d95214c0010f90fb2a429815b1e9db65cc1302b72db1ecb982600087f845d763c800187d0aba6c7900030f61574d8f200243fc3ea9b1e400087d87d5363c800787ce9aa6c7900030f5d354d8f200043fc3aa9b1e400087d8755363c800787ce8aa6c7900030f5d154d8f2001e4f3a487b1e40038df8750f63c800793ce8a1ec7900038755143d8f203c637396a931e4003c3e7455263c800187ae8aa4c7901df1b9c95498f2000477c3a8531e4003cae7450a63c8001c5aa8a14c79000f0f9d15458f200061eba2a8b1e4003c3e7455063c800187ae8aa0c790003875514318f2000716aa28431e40018ec825d561c80090fd0bb9ac3900021f617735872000716aa284b0e40028dc8758d31c80018baeba9ec690002a761053d8d2001c6fc3a87b1a4003c9e7450f6348001c3aa8a1ec69000297a1631d8d2001e1f3a2a931a4000c3d7455263480071df0ea14c69000f2b9d14298d2000716aa28531a400487e87dd563480010fb09baac69000237e0d7558d200043f438eab1a400087f855d163480090f90aba2c6900023de057458d200147a40ae8b1a40008fb805d163480010fd0faa2c6900121f21f5458d200043f43aa8b1a400087c8755163480018b8ebb9ac69000237e1d6318d200052e42ac631a40128dc835d463480f18dae5aa0c69000f0f9d15418d200061eba2a831a4077c6d725506348001c3aa8a18c6900023b61e4218d2000716aa28431a4000a5e858c463480015b301188c690003171d7634c9200062e3a8c69924000c6c76dd532480031db05baec2900021fe1573d85200243e42ae7b0a40018f8805cf6148007958e8a16c2900038b55142d852000c76432e598a4000ccc764c931480051f301baec68800a3e60374d8d103b63cb86a9b1a2000c3f745536344007878e8aa6c6881d71e5c154d8d1001e1f3a2a931a2000c3d745526344001c3aa8a1cc6880121fa1f7558d100043ec26eab1a20008bf845d5634400717908baac6880023be097558d1005476412eab1a200087e871d5634400717d0fba2c6880030fdd77458d100061e3aee8b1a2000c3f85dd163440018790bba2c6880021fe157458d100243e42ae8b1a20008ef825d163440151d904ba2c6880022fa1c7458d100061fba8e8b1a2000c3c751d163440010fd0faa2c6880121f21f5458d100061fba6a8b1a2003
  | 2 => 0xf5458d210043f43aa8b1a420087c8755163484018d8ebb92c69080237e1d6318d2101e1f3a2a831a4200c3d745506348401c3aa8a18c6908038b5514218d210043fc2ae031a420487c855c063484259b060b80c69096e1fa1b754c9210043f43eca992425a87c87d953248401c5aa8a16c0908121fa1b75581212d43e436eab02420087e87d956048401878e9b2ac0908021fa1c65581210061e3a0cab024200c3f65dd16048401878cbba2c09080317d9773581210062e32ee6b024200c5f651cd60484018b8ca39ac09080f0f9d15498b300061eba2a93166003c9e7450e62cc001c3aa8a1cc5980121fa1f7558b300043ec26eab166000c7a10dd562cc0010fd0e3aac5980028f6107558b300043fc2ae8b16600487c855d162cc0011ef02ba2c59800a3d2057458b300043f43ea8b16600487c87d5162cc0010fd0eaa2c5980021f21d5458b3001e1f3a2a8b166000c3d7455162cc0011df04baac39802a3b209755873001e4e3a286b0e6000e1d5450d61cc0010ff0abb643980121f21576c87300043fc2aec90e600487c855d921cc0010fd0dba6ca980121fe1f64d95300061eba6c9b2a600087d87993654c0014dd05326ca980029b60a64d95300043fc3ac9b2a601087d87193654c00187ae8326ca9815a9721943d95300068fba287b2a6000e1c6450f654c0ad6b100a1eca980021f61e74d95300061fc22e9b2a600087e871d3654c00187ae83a6ca981ea97a0c74d95302b52ec18e9b2a605687e87d0f654c0010fb0fa1eca980030fdd343d95300053741687b2a6000a6d82d0f654c00187ee8a1eca980021fa1c43d95300843ec3887b2a6000e1d4310f654c00147d09396ca980028f61272d95300043f43e85b2a600087d87d0b654c00187ee9a16ca9800297a0f42d95300052ec1e85b2a6000c3f7450b654c0010fd0e216ca980021f61c42d95302b53d404e3b2a6000a79809c7654c0010fd0fa0eca980021f61f41d95300043f43883b2a600087d87107654c0014bd0620eca980029760c41d95300053741083b2a6000a6d82107654c0ad4f50020eca980029e60041d95302b43f43c63b2a600087d878c7654c0ad4f50118eca980029e60231d95300043f43843b2a600087d87087654c00147d0810eca980028f61021d95300052f41843b2a6000a5d83087654c0ad4f50010eca980029e60021d953001c77c3a85b126000e2d5450b624c00155b0810ec498002b360c21d893000574c0043b126000c3e74d96624c00187ce832cc4980030fd9574989300061e32ae9312600acac625d2624c00195ae9b14c4980021fa1f65589300043f438cab126079c5f73195624c0011df0eb10c49800f0f9d154189300061eba2a83126000e1d5450c624c001c5aa8a10c4980021fe1571189300243e42ae2312605787e86dd5324c001ab
  | 3 => 0xbb026203c9c7450f604c401c3aa8a1ec0988021fe1572d81310243e42ae5b0262018f4815cb604c40787ce8aa6c7908030f5d154d8f2101c6fc3a87b1e4203c9e7450f63c8401c3aa8a1ec79080f0f9d15498f210061eba2a931e4203cae7450a63c8401c5aa8a14c7908121fa1f7558f210043ec26eab1e4200c7710dd563c84010fd0e3aac7908028f6107558f210043fc2ae8b1e420487c855d163c84011f700ba2c7908063e2017458f210043f43ea8b1e420487c87d5163c84010fd0eaa2c7908021f21d5458f2101e1f3a2a8b1e4200c3d7455163c840787ce8aa0c7908030f5d15418f210070eaa28631e4200e2d5450863c84011bf06baac19084a3720d755832101e563a284b064200e2d5450960c84010fd0dba6ca908121fe1f64d95210061eba6c9b2a420087d8799365484014bd07326ca908029760e64d95210043fc3ac9b2a421787d87193654840187ae8326ca9096a9b21942d952100697ba285b2a4200e2c6450b65484010fb0f3a6ca908030fe1174d95210043f438e9b2a4200c3d741d365484f94dd043a6ca9096a9b60874d95210051f424e7b2a4200a3d849cf65484018bae639eca908021fa1f43d95210043ec3e87b2a4200c3f74d0f65484014dd05a1eca908029b60b43d95210061fba287b2a420087e8710f65484010fb0e21eca9096a1fa1f42d95210043ec3e85b2a4200c3f74d0b65484014bd07a16ca908029760f42d95210061fba285b2a420087e8710b654842f0fb0e216ca908038b50842d95212d53b40ce1b2a4200a75819c365484010fd0fa06ca908021f61f40d95210043f43881b2a420087d8710365484014bd06206ca908029760c40d95210053741081b2a4200a6d8210365484b54ed02206ca908029d60440d95210043f43861b2a420087d870c3654840147d08186ca908028f61030d95210053741061b2a4200a6d820c365484b54ed02186ca908029d60430d95212d43f43c41b2a420087d8788365484b54ed03106ca908029d60620d952101c6fc3a87b1a4200e1d5450f634840153b08186c690802b360830d8d210056ac0861b1a4200c3e74d96634840187ce832cc6908030fd957498d210061e32ae931a4212c9c635d2634840193ae9b1cc6908021fe117598d210061f42ae931a4200c3d855d263484090ff0faa4c6908021f61f5498d2101e1f3a6a931a4200c3d74d5263484010ff0eaa4c6908021f61d5498d2101e1f3a2a931a4200c3d74552634840795ce9214c69080e3be1d4298d2101e573a28531a4200e2d5450a63484010fd0fb2ac6908021fa1c6558d213de37b90cab1a420487e87dd563484010fb09baac6908023be097558d210043f438eab1a420087f855d163484090f90aba2c6908023de057458d210047dc02e8b1a42018f8805d163484010fd0faa2c6908121f21
  | 4 => 0x54c8010fd0e21eca990aa1f61c43d95320070ea1887b2a6468a5e83dcb654c8010fd0fa16ca990021f61f42d95320061fba685b2a6400a5e83d0b654c8014bb07a16ca990030fdd142d95320043f43885b2a642a87d8710b654c801c5a84216ca990029ea0271d95320053cc04e3b2a6464a5e831c7654c8014bb0638eca990021fa1f41d95320043ec3e83b2a640087e87107654c8010fb0e20eca9900297a0c41d95320052ec1883b2a6400a6e82107654c8014db0420eca990029ea0041d95320053cc0083b2a640087d878c7654c8014f50118eca990029e60231d95320043f43843b2a642a87d87087654c80147d0810eca990028f61021d95320052f41843b2a6400a7a80087654c8014f30010eca990029da0670d95320053ac0ce1b2a6451a6e821c3654c8014db04386ca990021fa1f40d95320043ec3e81b2a640087e87103654c8010fb0e206ca9900297a0c40d95320052ec1881b2a6400a6e82103654c8014db04206ca990029da0440d95320053ac0881b2a640087e870c3654c8550fb0e186ca990028fa1030d95320051ec2061b2a6400a6e820c3654c8014ed02186ca990029d60430d95320043ec3c41b2a6400a7681883654c8014eb03106ca990021fa1c10d95320043ec3821b2a6400e4f65d8a324c80147b0832ec29900f0f9d154d85320061eba2a9b0a640087e87d95614c8010fd0e32ac2990028f61065585320051ec20cbb026403c3e74553604c80187ae8aa6c0990121fa1b75581321543e436eab02640087e87d95604c8010fd0e32ac0990028f61065581320062e3aeec9906400c5f54dd9320c8018baa9bb2641902b3394b764c83200666a96ec9906400c5f76dd5320c8018d8ebbb264190031bd53764c83200636aa6ec9906412cce53dd9320c80199aa7bb264190031bddb754c83201e4e3a286b086400e1d5450d610c801c5aa8a12c21902a3d21d515843205572412a2b08640a8f487505610c801d4a84a0ac21900387551435803201e563a284b006400e2d54509600c8151f10ea82c01904ab620d50580320547c43a80b006400e9943501600c8ed8bce7aa4c59880f0f9d15498b310061eba2a93166275c5e7355262cc4011bf0ea1cc59880f279d14398b310070eaa2873166203c3e7455162cc40187ae8aa2c59880a3720d75583310070eaa286b06620487e85dc960cc4010fb0bb92c198802ab61052d893101c77c3a85b126203cae7450b624c401c5aa8a16c4988029ba1620d893100477c3ac43126200a6c85588624c4151d904ba8c4989db175cf541893101e1f3a2a83126200c3d74550624c4eb8bae6aa0c4988023761e43189310070eaa2863126200e2d54508624c4014dd0b100c498802b96062018931006363aec49926200c6c75189324c4018b8edbaa6498803551c7754c9310146ec1ee
  | 5 => 0xc2b02d95f08a9106b0f7244328ba2ac0ce0c4d50fb2608b10706939c004428591cc4b85706028a82c701a83244dc8692c07a35d699390d6810b7ab44de3f8e609241234cc014d45e310870f60d839c6d8ea3d88216c02b4202cc4503a0c2ae10ca453609c0378402827c9200e90b07144827e16830d4d8004c68f09496c00a8e95714c13e8d9280915620003ca6c1c600058ac925e4e8a59ea37a3202fabc0e40013c0da00064c7e0002fa80cff9080fe000dfa142e46e000000284000000be0002f1519b60a08a40020d07e4292d80742a96093a6d18c0015028d318000000000005fc001470004a00025c0009191723809c72d662340302c95ba21582220f89e806088c000171066a451a67000218c3823356a1c0000009e06c9892b0180dc8f28b0004193e1b50840011b9b200072960298206001188000083e4b28001289d80011b40c00082800000445672680527cc0002c3a86f9089074543b80000052464000000000934f705416a00000109000679470003029e51a9320001d8bd9891541d000173220000000000cc578000000fa130f191f01600000000000874000cf3280000029f2a87dc268003fa4d56916a092570e81ae3c00b5612af0ac7652ca3d248034468004cc0a83b92044a000040060000000006048100481e0084e000180283602834018020003e00800008140701e05800010020480e1b060010042380001802000f21c0200a804050160b8020b01c0680a05006028a40405a0702c0306800802000060280a1a02a010740080206804000240d000030000180400804000100d000018000003c01864040000081a000260a80a0001a078020c000018000000c0a80003032000581182a0387801800008001181e1300c000040301000040000000180e010000200603000000080180000826038542700e000000b01c020680400c018000101c010020080001004020020100400000050020001c1a8020b80a00000000020d8000d0000300000010030041b00602010008000680200036040080a000000121a8140001c000320082c018082580c0001a0000c0a80e0000f2b9d1425873200716aa284b0e6400e2d5450960cc801c3aa8a1ac31900f279d143582320070eaa286b04640087e86dd3654c8090ff0fb26ca990030f5d364d95320043ec3cc9b2a6400c3f74993654c8010ff0eb26ca990030fdd164d95320053bc0ac9b2a6400a7481593654c8014f700b26ca990029e20164d95321543ec38c9b2a6400c3d74193654c8014f50130eca990029e60261d95320053b40cc1b2a6400a7581983654c8010fb0f3a6ca990030fdd274d95320061fc22e9b2a640087e871d3654c80187ae83a6ca991a29ba0b73d95320043f43e87b2a640087d87d0f654c80187ee9a1eca990029ba0b43d953200536c1687b2a6400c3f7450f6
  | 6 => 0x1a2586700c2a1611e00089acf2f2b2820a410003600003c2dc3755100000075400000040210e32303304e1598003100480006328c49880ad52322ec00000444a786888e286430ad24a38269cb328f00005025889316a856682800054c0b01e0005b541a810682c00887534a830f78d903a3cd6b1782d0120dba1a000b1cd094856c84d39ac40f8930cd25a1bc75cfa9642f8094bb09915256c919a327a8782ea5e1381c565aa74641cc791211fa2312e8624847f14426100465d2983604c920999bb39ab20f81993fc0ed3f8f44ca4fc3c11a3bc7ecf105e4ee9a41792531e89d2781f15a000002050aa000d798a000000000a50000000010b3483e8002a92c03054207e1de5c47a912512b154b8000006e8000003a211c45983000018f20820008b4001404a42fd1c8c00006451d80f134000002940000000007b2a400000134000619100c9048a4481081014a711991c19c388001b300046096ab2000000000eb0002743700800076cb480043699149a86560450501b90f4000eb0f15ae4f8000441e079935a5147c2e0e49d24ea000e9880064655301fa49c634a816b1ca1289e1f453a800c700017a24cd6000044000cda7d13c7e4cb0130ae5385b8003884012a24b00000000000000258a50034e46d0cf9e73841a8ee087276954acaad3ec3e0e19493c2ae95a91d0e0680000001503b400000066055412804dc7a40028c378560aaad422e064ab0000a2024c22743f05c0f580004259c7400014ea40000004382841c09542e95c6629652a2893100014c0400000000000070a0219aa94c120f2c481d008b94f65e82917e1d8a903416148695887a6a1aa7b51229a16c67142aaa4142e86914f03410caea7a4be37d0c0392a2769388d40c8a28ec02e35aaf55403e3ca000720000a673c00027254308a224957e0001aaab57c4d9238460b8774ce8970dab184c0cb5a06c48a9a61483fd5cad101c8990905a2eea64000650008a057a1f1a0a991fa2b208000001573be71c6e0c515626cb1abb18e070e417522
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xcf182c006802800a9d0024011006400200882972000d00180400f0e84e121c28000004c0080000000360000b3e0030440084002008000005100903e98dd164d95320040fe6174193654c80103f985d074d95320060bdd182d0f654c80181f7460f42d95320050765075dd9320c80142d941d7764c83200607e1d5450e62cc40142d941d7624c9310050b65075189324c40781f8755143d8f210240f2617455163c840182f7460b43d952100607dd183d0b654840142f975514298d2101e0be1d5450a634840103d94a1f654c9210240f2617455162cc00182f7460b43d953000607dd183d0b654c00103d94a1f654c93000507e5d5450f63c800781f8755143d8f200060be1d5450a63c800782f875514298d200050765075d8d324800141d941d4634c9200050725d5450d634400781c875514358d1000703551431c9634400142c97551425891001e0b21d545096244001c0d541cd42589100045ce5587c8730440019c0874c93148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x94d
  | 6 => 0x94e
  | 7 => 0x98a
  | 8 => 0x98d
  | 9 => 0x98e
  | 10 => 0x3
  | 11 => 0x150a
  | 12 => 0x150d
  | 13 => 0x150e
  | 14 => 0x9ca
  | 15 => 0x9cd
  | 16 => 0x9ce
  | 17 => 0x168a
  | 18 => 0x4
  | 19 => 0x168d
  | 20 => 0x168e
  | 21 => 0xb09
  | 22 => 0xb0d
  | 23 => 0xb0e
  | 24 => 0x1549
  | 25 => 0x154d
  | 26 => 0x154e
  | 27 => 0xb49
  | 28 => 0xb4d
  | 29 => 0xb4e
  | 30 => 0x16c9
  | 31 => 0x16cd
  | 32 => 0x16ce
  | 33 => 0x3c9
  | 34 => 0x3ca
  | 35 => 0x3cd
  | 36 => 0x3ce
  | 37 => 0x15cd
  | 38 => 0x170d
  | 39 => 0xcc9
  | 40 => 0xcca
  | 41 => 0xccd
  | 42 => 0xcce
  | 43 => 0x15c9
  | 44 => 0x15ca
  | 45 => 0x15ce
  | 46 => 0x1709
  | 47 => 0x170a
  | 48 => 0x170e
  | 49 => 0x98955
  | 50 => 0x98956
  | 51 => 0x94995
  | 52 => 0x94996
  | 53 => 0x168955
  | 54 => 0x168956
  | 55 => 0x95695
  | 56 => 0x95696
  | 57 => 0x154955
  | 58 => 0x154956
  | 59 => 0x95555
  | 60 => 0x95556
  | 61 => 0xb4955
  | 62 => 0xb4956
  | 63 => 0x94b55
  | 64 => 0x94b56
  | 65 => 0x209
  | 66 => 0x8a
  | 67 => 0x1409
  | 68 => 0x128a
  | 69 => 0x249
  | 70 => 0xca
  | 71 => 0x1449
  | 72 => 0x12ca
  | 73 => 0x150995
  | 74 => 0xcc995
  | 75 => 0x98cd5
  | 76 => 0xcc996
  | 77 => 0x15c995
  | 78 => 0x995d5
  | 79 => 0xcd515
  | 80 => 0x150cd5
  | 81 => 0xcd516
  | 82 => 0x15d515
  | 83 => 0x1515d5
  | 84 => 0x1689d5
  | 85 => 0x1689d6
  | 86 => 0x17c9
  | 87 => 0x5c9
  | 88 => 0x154b15
  | 89 => 0x154b16
  | 90 => 0x164a
  | 91 => 0x44a
  | 92 => 0x16cb55
  | 93 => 0xccb55
  | 94 => 0xb4cd5
  | 95 => 0xccb56
  | 96 => 0x170b55
  | 97 => 0xb5715
  | 98 => 0xcd6d5
  | 99 => 0x16ccd5
  | 100 => 0xcd6d6
  | 101 => 0x1716d5
  | 102 => 0x16d715
  | 103 => 0xcc3d5
  | 104 => 0xcc3d6
  | 105 => 0x3ccd5
  | 106 => 0x15c3d5
  | 107 => 0x3d5d5
  | 108 => 0x1703d5
  | 109 => 0x3d715
  | 110 => 0x15ccd5
  | 111 => 0x15ccd6
  | 112 => 0x170cd5
  | 113 => 0x170cd6
  | 114 => 0x1715d6
  | 115 => 0x1715d5
  | 116 => 0x15d715
  | 117 => 0x104a
  | 118 => 0x1a8a
  | 119 => 0x1049
  | 120 => 0x1a89
  | 121 => 0x5d5d1
  | 122 => 0x9d796
  | 123 => 0x45712
  | 124 => 0xb1616
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1233
  | 6 => 2040
  | 5 => 729
  | 4 => 35
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (50142+((h/411+packedAt gbK7 (45621+(h % 411)*11) 11) % 1969)*12) 12
  | 6 => packedAt gbK6 (106080+((h/680+packedAt gbK6 (97920+(h % 680)*12) 12) % 2693)*12) 12
  | 5 => packedAt gbK5 (45441+((h/243+packedAt gbK5 (43011+(h % 243)*10) 10) % 875)*11) 11
  | 4 => packedAt gbK4 (2516+((h/11+packedAt gbK4 (2450+(h % 11)*6) 6) % 56)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe0f878387f0ff01ffc7ffff00166239c1733fc
  | 1 => 0xff07803f87f0ffe03f8f00fff2b83ce069cccf
  | 2 => 0xffffffc007ff00003ff000fffcc1c0ff8e0f0f
  | 3 => 0x7fffff80000003fffff000f01ff03f00ff0
  | 4 => 0x7ffffffffffffc00000000ffe0003fff000
  | 5 => 0xfff8000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xe84808080b0190498c1946906022218c03115c
  | 1 => 0x294080188110a4c0948a0aa4a0282ca02144c5
  | 2 => 0x52933a4006aa01032920144b44c0c0558e0b0a
  | 3 => 0x5d4b5500002843244b8018b015602f00ea0
  | 4 => 0x1086672664cc4b16000020020fd400035ca000
  | 5 => 0x9ce0060440888c180008c08c0fffbbf8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefee0feeeeac0feeefee0feeeeac0feeefee0feeeeac0feeefee0feeeeac0feeefee0feeeeac0feeefee0feeeeac0feeefee0feeeeac0feeefee0feeeeac0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36282
namespace PEqualNP.Outside.L_meta_36282
open PEqualNP.Outside.L_meta_36282.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 6 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 90 := (concat bs0_4_0 (concat bs0_4_32 bs0_4_64))
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
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 6 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 25 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 90 := (concat bs1_4_0 (concat bs1_4_32 bs1_4_64))
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
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 5 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
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
theorem bs4_4_128 : Interval s4Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_160 : Interval s4Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_224 : Interval s4Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_256 : Interval s4Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_320 : Interval s4Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_352 : Interval s4Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 414 := (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat (concat bs4_4_288 bs4_4_320) (concat bs4_4_352 bs4_4_384))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_64 : Interval s4Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_128 : Interval s4Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_160 : Interval s4Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_224 : Interval s4Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_256 : Interval s4Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_320 : Interval s4Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_352 : Interval s4Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_416 : Interval s4Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_448 : Interval s4Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_512 : Interval s4Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_544 : Interval s4Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_608 : Interval s4Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 616 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 bs4_5_512) (concat bs4_5_544 (concat bs4_5_576 bs4_5_608)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := (concat bs4_6_0 bs4_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_7_0 : Interval s4Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_7 : Interval s4Atlas 7 0 1 := bs4_7_0
theorem alls4 : ∀ k ≤ 7, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
  · exact alls4_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 29 := bs5_3_0
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
theorem bs5_4_448 : Interval s5Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 473 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 632 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 35 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_704 : Interval gbAtlas 5 704 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 729 := (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)))))
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
theorem bgb_6_2016 : Interval gbAtlas 6 2016 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2040 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 bgb_6_992))))) (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248))) (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760))) (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 bgb_6_2016))))))
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
theorem bgb_7_1216 : Interval gbAtlas 7 1216 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1233 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 (concat bgb_7_384 bgb_7_416))) (concat (concat bgb_7_448 bgb_7_480) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))))) (concat (concat (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 (concat bgb_7_704 bgb_7_736))) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)))) (concat (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056))) (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 16, 18),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefee0feeeeac0feeefee0feeeeac0feeefee0feeeeac0feeefee0feeeeac0feeefee0feeeeac0feeefee0feeeeac0feeefee0feeeeac0feeefee0feeeeac0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075680 * 2 ^ 32 + 4277070528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36282.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,5]⟩,⟨.and,[2,3]⟩,⟨.or,[2,4]⟩,⟨.and,[3,6]⟩,⟨.or,[8,9]⟩,⟨.or,[5,9]⟩,⟨.or,[0,7]⟩,⟨.or,[4,11]⟩,⟨.and,[12,13]⟩,⟨.or,[1,14]⟩,⟨.and,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4277070528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4277070528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36282

open PEqualNP.Outside.L_meta_36282 in
theorem PEqualNP.Outside.L_meta_36282 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4277070528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4277070528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
