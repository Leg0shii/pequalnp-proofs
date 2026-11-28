import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36220.Model
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


end PEqualNP.Outside.L_meta_36220.Model

namespace PEqualNP.Outside.L_meta_36220
open PEqualNP.Outside.L_meta_36220.Model
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

def SBf (j : Nat) : Nat := [6, 6, 8, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36220

namespace PEqualNP.Outside.L_meta_36220
open PEqualNP.Outside.L_meta_36220.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x3000c05016208120290e0020020000be43bc43bf42bd42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1101808e29a852d52d06b0a098cb54840
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => packedAt s0K4 (212+((h/4+packedAt s0K4 (192+(h % 4)*5) 5) % 20)*5) 5
  | 3 => packedAt s0K3 (111+((h/1+packedAt s0K3 (108+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x7ffc0ffffc0ff07ffffc0ff83ffe07e7f33f3
  | 2 => 0xffffff07fffffff81f03fffffc1fffff91fc7f
  | 3 => 0xf81ffff81fff07ffe003ff07ffe1ff81e1cf9c
  | 4 => 0x1fffffe00007fffffc0007fffe0001fe0fe0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x90c44621448941016524c8498123212c2711b1
  | 2 => 0x21088812091082280a41119224144a50906446
  | 3 => 0x52551240d2284d52a0a26a44cb419505618a98
  | 4 => 0x659a249483b2969cd3c8308772980619da0f60
  | 5 => 0x861c38e71c3ce7e71cf3bce063111861fdf000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0fcccf0c0fcc0f0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36220
namespace PEqualNP.Outside.L_meta_36220
open PEqualNP.Outside.L_meta_36220.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x40c092002b2984051c00203bf43bd43be42bc42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x100c0008008ea98852c525065ca5205554430
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (208+((h/4+packedAt s1K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s1K3 (112+((h/1+packedAt s1K3 (108+(h % 1)*4) 4) % 11)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 2 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 3 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8040888500808002904c02240229109408d131
  | 2 => 0x10891048252442502a11214921422528a22486
  | 3 => 0x895229034a480ca58426541654054a85454b18
  | 4 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36220
namespace PEqualNP.Outside.L_meta_36220
open PEqualNP.Outside.L_meta_36220.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x4817e53902faa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa9261ef524c2dea4985f14930f6292616c524c2fea2987dd4530bba8a617c514c3e8a2985d14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53882faa7105f14e20bea9441ee42883da85107bcca20f6194417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f7a1241ec42483dc64907b4c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107b90820f6a1041ef32083d864105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dcc610fa18c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb18a21f531443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f731043e862085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216f90c42de218857e5210b7e84217b90842dea1085ed4210b5a84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997bd0b32f6216657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cafca5197b90a32f6a1465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997b90932f6a1265ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32bf29065ef420cbd8841977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83be43d077887a0df94b41bea9683bf42d077a85a0df94341bea86837d54906fca720df54e41dfa1c83bd43906fca520df54a41df21483bc42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83be435077886a0dfd4941f7a92836f52506f8a4a0fb14941b629283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077e8620ef50c41bf29083ee52106dca420df54841f6a90836d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998df94b31f7296636e52cc6faa598fb54b31b6a96637e50cc6faa198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31bf29463ee528c6dca518df54a31f6a94636d528c6fca318f7cc631fb98c637e508c6faa118dfd5131bf2a2637d544c6f8a898dfd4931be29263f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863df310c7ec6218f74c431fa98863d5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f721643ed42c87de6590fb0cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ee32887da6510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21f721243ed42487de6490fb0c921fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53086faa610df14c21bf29043ef42087d88410fb8c821f6990437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf29681ee52d02dca5a05f54b40f6a96816d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x3073a2822c300001720004b4000f00f84a8001a031000000000128688a70875328f10b24f0c69f5288fb4dc33538157524118e61ba06e5e9050cc0000000000039a0000005e372419048981320013a9f7430760000002cc328000002a48ec0006f4fc244d980048284d02a3300a844da9094c8400001b40729813699e11e750c114c1bc9080e2882a21e5272503fc628551ea30c08099a0414a5589003e402a583b0f83e46240002800039000000186698530000000000018d12e49d3900000019cbe04811670800000000674a280007808d01a4a18a09c001670843585d2170d20448c9f52e8888d72301589b03b9c73e22cc15984508284f98700d64c8249c61dc32c309bb1be00000008000000ae975000784000894ac0000000052e000001ab2021291c0002b2000000361260012690e0004510a00000000000173000228648160000013e1ed0ae4a4cc16a000000ed0000160000003d4b67243e9ce0e64c07280d09a4e0c022100078c000000000000018f1ba0003d90f2140008b915000268191b02787751906515e808698ec36e964db04f000900b61903d63c54280043c000d783b000000eba1d000000e08000009ac0f09b2b0798209530006b0000f44f6978000004ca3080007a4a6114ad14f47a16c5480019c28c0d00000020400000000000002450008bcf20000625a0001c31b258092000388000b806420a44c462490307ec168c74b44989586047c0006080000092d47a772fc1b12226315c521338030080600c010900000005004060040600003000000000a01401000060240000800028020080000000004000040b0080000800000170380003400014000200100059054000040b0180100000000040081e04000034000080f004010000c00c0902404008000100800c01010010001700001004070080500c0801c00000060640f0400600c0e00c0104c0e0000001800000000180a00807010020000a0080104c0304c020000f01c0000c060201000c000000400c1f00c0c0080200404008040000000c000081500803004000300201810000110000100c0205c050b40a00000038000240801001000030080202000000000201205c0f018030100d0100401c070200200000040270000603012020050580000004002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa9287ef5250edea4a1df14943f6292876c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf29087ee5210edca421df54843f6a90876d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485e
  | 3 => 0x24821a1b490800520288201e04f43e4001bc4c27f4df2860005409d17f4867f09c8bd3a69bc0019f04a000001e7418000001041ea510b49a400097cb887416e3fc2aa064ba0bcd38004d01601600021611d00000000000d40003b2684000000003e803a31000000000e1472340001314464fc0011c000000b08155149d1291fa3360c0af8d84567d0121812369a4a599c0a482d4984314895400165000000ef89c0266f40521923e0001f9de3a0a44bd8880000014a00020641c001f61f8198000000180040010810c2105e0000001e07922a2ee318a50d71761640784b25c89c55928000011408000a6000f7800000000001a348c9d80024c000644be97929aa609618b3b67440016e244794000003707e4bb0000000000018c0000000019302e1111023f516000cb0003245254a8002c495ce90a0220000000720322082e09f000a1d038004364f875163230000b79d637e3ac000004c47b8e78000540000000016c838002892d6898f414123c48ca10cf0c40006a800000000ca0000008d123a780045780e8d40004f400003000970929f811c9cd1b9020e22c0281a50b4214ee0e03348b47b8e306661400258000000cb9ff0000e0642100445b4001641b650d2a20d45c7c014a822240000020f0003a0000003647209a23a0ea0000011d25e6a47f01f2aa7009da2517e998a01540ba72c3f09e0247886e0004589a8c3880000050ad8960008714028d4523bc7e9990422c84a8da3d287c288ed46a3984911a1889e4048b504c0b8c705406a3d8351350ac2e4c1a360007b10a87f000000002834e28685689d17c7280017826c2e08880628e001470002b84dc480b10002a000000000000e281b1061b8d68004fe1a0000d24108908605f5183a4ea8f301c5182703a0206c4468b432a344538000008481a0e23541
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x53c823d6414f20cb55342c832d5410b20cb55232c82ac644cb20cb55132c832d54c8720ab19121c832d5448720cb58a548823e64d4e208f593538823e6414e208f59053882766114e209d584538832e5490a20cb951428832e54cca20ab590328832e540ca20cb95221882ad6408620cb95021882ad64c8220cb953208826d629512097d8d544825c63551209dd85544827461551208fd91534823c6454d209bd8953482776154d209d185534823e6414d208f590534826e65d09209b994424832d54109209b996324826c654c920ab191324823e64145208f590514826e65c8520ab19121482ae64881209b98b540825e63150209758c540827661150209d584540823f6454c208f191530823e6414c208f590530826e6214c209d98453082756114c208f992520823d64948209b596420826f6550820cb151420826d65cc8209b59432082ad640c8208fd91510823c64544209b59621082ad64084208f992500823d6494020ab593200826f65480209ed95200826f62553109b18954c426e62153109b58854c423e64d4f108f59353c426e62d4f109b58b53c423e6494f108f59253c426e6294f109b58a53c423f6454b108f19152c423e6414b108f59052c4354534c7109b98b548426d62d52109b98a548426d62952108fd91538423c6454e109bd89538426c6254e108f990538423d6414e109b988538426d6214e108f993528423d64d4a108f992528423d6494a10d5d4c318423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d10d5584534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c5244276658c510d514e3144274654c510d514d314435453841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c755153043546154c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109d597310435553cc4109d5943104355530c410d554f100427965840109dd9510042d46344010d554d100427b6544010
  | 1 => 0xc63d64149318f990504c63d64141319b988504c66d62141319bd89540c66c62550319b988540c66d62150319e980540c67960150318f992530c63d6494c318fd91520c63c64548318f992510c63d6494431b558e310c65f654c4319dd95310c6d7654c431d5d95310c6d4604c4318fd91500c63c64540319bd89500c66c6254031d54c5500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c872c5450b21ab59032c863e64943218f59250c865e63d52219758f548863e64d4e218f593538863e6494e218f592538872f5410a21ab191328863f64542218f191508863e64951219bd89544863e6515121cb588544863e6494d218f592534866d6294d218fd91534863c6454d219ed8153486786054d219b996424872c54909219b195424872c54509219b997324872c54cc9219b99432486ad640c921cb150324872c54885218f596540872c62550218f990540866e62150218f993530863d64d4c219b98b530863e6414c218f590530867a6014c219e580530866d65d0821cb553420866d6510821cb550420866d658c821cb552320866f654c821ab191320872d544c821cb553210866f6548421ab191210872d54484219dd9521086ac6250f40cbd0d52d032d4354b40cb54a42d032d5210b40cb54b41d02ac6250740cb54941d02ad6210e40cb90e529032c4394a40cb94b429032e5250a40cb94a41902ad6210640cb94841902ad62d0240cb94b409026e6214d409b588535023e65d0d40ab189435023e65109409b988515026d62145408f99741502ac6250540ab98a405026f6254c409b189531023d6590c40ab588431023f65508409bd89511026c62544408f59641102ad6210440ab58b401023f65500409ed95401026f62553309b18954cc26e62153309b58854cc23f6454b308f19152cc23e64947308f59251cc26e62947309b58a51cc26e62d52309b58b548c26e62952309b58a548c23e6494a308f592528c23f64546308f191518c26f62546309b189518c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c32f54d4930cb153524c32f5414930cb150524c33754d4530cd153514c36752d4530d914b514c3375414530cd150514c3675214530d9148514c25e65cc530d5147314c354514c530d5146304c26e62d50309b58b540c27661d50309d587540c23d65950308f990540c26e62150309b588540c27661150309d584540c32e5494830cb552520c32e5454830cb551520c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c25d658c430d5546310c355510c430d5547300c25f654c030b5185300c355514c0309ed95300c32c62553208f99353c823d64d4f209d98753c827561d4f208f99
  | 2 => 0x683c9301d1d07dca10003440004204d1ae104d403b44c5240d06a3ae6e0a50db0980b42a9ed15820caa1c12146d00000a21000061115000000808493646f8b58004000000011b0000009686d3dc8307e92e07a000791ba240534069222f4514f605900e440211762be71400202192538000a30b8554a08a91e00380007d2ee00079a1813e00000000000000000dd3b07807690e3a02b4220380fc5c42580039a000000940660006192b3863a8e88003128500000042e63cea000320001068000006f0230001988645903f17c2582380019a3e4659752060001505b16619057205148000390180000008008070000001004058010140e00000048090040300824078050088e0001201000004050140000c0000400000050000000807000291201800400014140100000008068020000e0040608c020101800c0607c01000080240000012000090302b018180180000c06094000400a000020340406c0a00000008010040101405028000000a00c0c0340200001010000140300c010540f0140e0200000001004070143e0500003010038000c40a008480000003404000070100100409008000280a148110481300c02030000bc000200800000000020081102401028020500200e6f62547439b18951d0e6e62943439b58a50d0e6e62946439b58a5190e6f62542439b1895090f2e43149438fd954310eac6250c4397d954310f2f4354843cb50d5210eac6250f42ab5884390a3e65d0d42ab1894350a3d6590c42ab5884310aad64908428fd954210a6f6550842abd954210b2f6550842ab18d4210b2d5350842ab1854210aaf6050842cb5095110b2d42940429d98754cca7561d5332cbd5042cca3e64947328f59251cca3f64543328f19150cca7661152329d584548cb2c5450a328fd91518ca3c64546328f992508ca3d64942328f992544ca6f62551328f994544cb2d62151329b996424cb2c54909329b195424cb2c5450932cb153324ca3d6595032cb189540ca3e64150329b988540ca6d65d0832cb553420ca6d6510832cb550420cb2d548c83297d95320ca6f654c832ab191320cb2d544c8329bd8953d066c6254f41ab58843d066e62943419b58a50d066e6294e419b58a53906ac6250e419bd89509066c62542418f99443506ad6210d41cb90c525072c43149418f997425072c52d0941cb149425072c52905418fd9543106ac6250c41cbd0d521072d43548418f596421072d5290841cb548421072d52d04418fd9541106ac6250441cb549411067765504419b98b54cc66d62d53319b98854cc66d6215331cb95252cc72d5494b31cb95152cc72d5454b319b98b548c66d62d52319b988548c66d6215231cb952528c72d5494a31cb951528c72d5454a319bd89544c66c62551319ed81544c67860551319b988544c66d62151318f990524
  | 3 => 0x18a3ec7a4821c818062cc40300006787e0110a834872186372350b61ad266340c09800de140ac0910e24581280500439c4410b13872caba09406000fd0002c256c0000000025ca01390f6000700004241d0d2a24000394000170ce494988451362885c806000000001cf0580dc608bd0000d02189d03e804b50cf1de1d4049ca17e080981c435261ccd8002fa54cca8600468286b0bb2b40004480036a000fa105114520d78ce0001890b000000874b102b22e8205d02112018cdb01618e320d191930a21d0f8270006f4bc87c2a4200361910001447d0bc0806b80021100060c001fc0907e0df8002344600000000000086000426490d392a1324700600b332000fc8da3d6370810f82122787106800014c7f00023a000000de20e05027963242354002203d07ccb21c0000318d598421a2a06c83c2e41b8a183200267c3491f11a3b0bf15d3be0000c0571a624cf89dc1cc578f79e216a1e41494c3480004a800000000ee8000005643b9940941c08793509c4f0002210003d45b99331a7f89408f2f804cb30a52887680c9ac3766dc391650f42aced93b2a28182e946296310cb07f408078e10223aa854b71370b07a80016729e16905885398540f31c74386303b16d3e0048898b614c8941b12f0ac88c399741044e0140523fe070b40002286cc130e326c0c4308001fe81cec800224000ae1921be7840d898330738e986b0cc3d0e920e000684d00af072000508a7434758cd0ee2d26c02f13405c5fc4d0f71247c8f18ca020580020fb25284080000118778000000000002f97300067400000304000458000483acf218e27451c001e727a8883280027e7f4000f11627184710600065cbc0002f62a80016f3ea7ec748782583845c1c923c218040000008788888100079468a1b18a6a8079a62e02c0918151ec4f85a0002ac360ce13224e0001d1b106a2801f02f00
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x1602689e01c60000030000201a1884a000050040000028e9040000c1041c18c6a9a8421524715095110a9338ea821665495c45450a32858ecaa2641950d7315142c868739ea8214430b5d8540c921858ecaa26410c2c7655121086163b2a8996410b1d9544872085aed2a0651042d769502188216bb4a990441431cd5410920a48e2aa0849050d731514208292b88a8a1041151d95344010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 20
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (718+((h/13+packedAt s2K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s2K5 (20202+((h/222+packedAt s2K5 (17982+(h % 222)*10) 10) % 880)*11) 11
  | 4 => packedAt s2K4 (22768+((h/183+packedAt s2K4 (20938+(h % 183)*10) 10) % 662)*11) 11
  | 3 => packedAt s2K3 (1016+((h/6+packedAt s2K3 (980+(h % 6)*6) 6) % 40)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffc1fffffff03fe0fffffc1fffffc8ff1ff
  | 1 => 0xf83fffe07f0ffffc1ff0f83ffe1c0fff723e4f
  | 3 => 0xffc0ffff800fc3ffe000ffc3ffe00f0383cf8c
  | 4 => 0xfffffff003ffffff0003fffff003fc0ff0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x802044412020000a40128444025214804d095
  | 1 => 0x128c48832414a12c0a90522992084ab132264a
  | 3 => 0xa196d1490ea9275561889ea2f540ac1b834b8c
  | 4 => 0x8528a21248818a9a532a04032992c022d80d60
  | 5 => 0xc630c39c70ce33e39dcce730310308c3efb000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeeeaa88eeaa8888eeeeaa88eeaa8888eeeeaa88eeaa8888eeeeaa88eeaa8888eeeeaa88eeaa8888eeeeaa88eeaa8888eeeeaa88eeaa8888eeeeaa88eeaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36220
namespace PEqualNP.Outside.L_meta_36220
open PEqualNP.Outside.L_meta_36220.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x8c031300002b007c1004a18000002d2225884e9a08bc19700b4f001a986301454e20365872e0e50400520000920002800000000500138000000910000000006499200a878000080000b000410102244000c18000ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x812e12c6a1636138b46f0994caa0000000003f001f0bc000722c0e000624492153e81846174718444922f86d44003d9c808390015098011b14942374a9b4005d23918c4023000048420a21c9008221343c000e000829f201dc5c9a0e92868053c0a44e650810c42a31d801180a2b848a02b3c9f840000c24d40660787d380000000000000211482a42a001698480e8002800000066b169c4002f00274001a34000000013000003c338240000001652e2c0018c009900000d2740023c003d0c9d4e60d4b13c8a00000c40000199fc005b2c1e87c7041990ac51001d93c6a002080000452340000001b8609b4a21822881c0c9122500818000000001808481070000028180000082859900800105001102098280008102018102800082120000808202018206118002000886cf94e439ea94873e5190e7aa121db94843b6a90873e5310f3ca621eb948439ea9087ad5210e5aa421cf944439ea80873e53d0a7ca3a14f543429eaa4855e5390abaa7214f14d42d7a92853c5150a7ea0a14f95042af298855d5310a7ea9994f15332cf21e659c43ccb3ea9996715332cfa16659d42cca7ca9194f55232aea9c65ad428ca7ea8994f15132cf21a659c434cb5a849967d5132ce2a265cf524cb3e84997390932cea1265cd424cb1a84994f950329eaa0655e530cabca720d754e419f29c839e539063ca720e754e419ea94839f329073a6520cf946419ea84833e531067aa420e7cc841ce990833e511076ca220cf540419f2a6633d54cc7388798db94b31b6a96633e548c67aa918cfd51319e2a2639c434c67ea818cf150319f2a6433d54c86bca790d754f219faa4433c548879a6510cfd51219e2a2433e540867aa810d794c21aea9843cd32086f4a010de540219f29e813d52d033e65a0674cb409f28e813d54902bea6a05714d40cfa9a813c5350338a6a04714d409fa92819f325033a64a04f14540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f20e6996413e548827aa9104f951209eaa241cd324827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xcd39a00ec1802e70000280000000a1b92406d48b4a4180042c402d1ed00082c00c8018097910e980350054e8000009b6000053a00000803c1992a0801c8e307c038560160046b80051a900094400284000008303000820102381040000580c394d5210f0e63548438798e51d0a1c63543428d98754cca8d62d5332a598754cca8d62153328b195424ca8d6490932a3995424ca8c6550932a3185424ca8f60509329358a539062d6294e41a358a539070e6294e418758a539070d6294e418358a539061f65cca4187d95329070d524c8418718d501068d6210f31c310d52cc68d6210d318798f540c62d62150318e580540c61e63d5221c3d51328861e63d5121c355132087493254021c354932d021e639474093588535022d6214d40a3588535030e6214d4087588535030d6214d4083588535021c65cc94087195325022d6215330a3588438c21d6510c30a3588430c30c4354830c510d510c30d544cb208718d548821c63551208d185544830d544c9208798f54c421c6355210
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x290003990248c200101282b8cc6a9087219c6655093281ae431aa020c0d7298f5448606b94c728e81415c84354430818ecaa26490504715513248206b94c7aa621035c86355210
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | 2 => packedAt s3K2 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (912+((h/16+packedAt s3K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s3K4 (4895+((h/55+packedAt s3K4 (4455+(h % 55)*8) 8) % 218)*9) 9
  | 3 => packedAt s3K3 (2420+((h/20+packedAt s3K3 (2280+(h % 20)*7) 7) % 88)*7) 7
  | 2 => packedAt s3K2 (502+((h/3+packedAt s3K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 1 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 2 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 4 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x14000408402040004402404802504088045045
  | 1 => 0x212108848148040a0a20841220849414312512
  | 2 => 0x421251102a9220d4a1112a8554092941828a28
  | 4 => 0xb556225281aa96733542207992c0c45d80f80
  | 5 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36220
namespace PEqualNP.Outside.L_meta_36220
open PEqualNP.Outside.L_meta_36220.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x85580000000600000003e000020831600067402e00b52251a78aa6386c40e00003a90068009005000b0a0188a000102744000110258c8f5ea0900004d1aa20c001800000002e0000080041019508081000400000ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1c2626379d12a841793c7a103aa00e05b1e05c1c1c1f0950a82509551e3a3e228fea345950520000238004b0023126000000000004c060ae812f8000a00001cc980d3c96818490f8a83a913706c80761f800003200194001200158da501b018106604854a40f000012077430b0086010a7000281b91cc4002e088005321a787261520c05a0051250f4631a068ba20002212e3b4c801120b24160849634858f041221b1069f1199140450113936711221c3c2725050009a35044565e269f866003d8648c6b2c8000000050b8fa01001c8008d3380124684e8d400382880062030081800400078d95000381028483098281058900810080870c068803020100048002900b82000000820700808000010c81800108958004cf94e439ea94873d5190e7ca121dd94443baa88873e5310f3ca621cf54843db288873d5110f6aa221cd544439f280873e53d0a7aa3a14f943429eaa4855f5350ab8a6a167d4d429e29a859c5350a38a6a16bd49429fa8a853c5050a7ca8214fd53329e2a6653e548ca7aa9196710e329faa2653c544ca7ca8194f55032ce2186576510caeaa2195e94032bca80653e53d067aa5a0cf943419eaa4835e53906baa720cf14d419fa9283b75150678a0a0cf95041af298835d531067ea998cf15331cf21e639c43cc73ea998e715331cfa16639d42cc73e8398e7507319f2a4633d548c6baa718ed506319faa2633c544c73c8698e710d31daa0a639f544c738a898e7d0931cea1263d7514c73e8298f590531cea0a63d5414c72a8298cf950319eaa0635e530c67ca990cf553219f2a4433d54886bca710d754e21ea98c433e544867aa890f54c5219f2a0433d54086bca610d754c21bd280437950086bca7205754e409f29c819e539023ca7206754e409ea94813d519033e6320674c6409f284813e531027aa4204f54440cf988819d311027ca0206e940409f2a6613d54cc33887985d94730baa8e613e548c27aa9184fd51309e2a2619c434c27ea8184f150309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c42bca7885754f109faa4213c54843aa63084fd51109e2a2213e540427aa8085794c10aea98216e52042daa408754c410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xe034a015000024726000001600000000000d0072a0013364800b000198000000231e55b800000000000041400c4c8000ada351a000005a0001776b8f0000a410000c00000a1c000000121d22610ac74e000014000360000f800000022000062f0c0020000013b20080090000400001000c00106080000e082050008000c594d5110f1663544438798e50d0a556114d428d5845350a956114d42c59845350a1d6114d42c55845350a156114d428d58454cca956110e3287594430ca956110c32c510d510cb1843540328718d52d061e63943418e98354cc69561d5331a698354cc69561153318719542cc6346550531a5587424c61c6550931a5592414c6966550531a5195414c6976250531a5181414c61c6355321c5551318861c63551218e1815448715544c5219558653902356194e40a558653903166194e408758653903156194e4085586539021f65cc64087d95319021c6354840c554531102956110f30c510d51cc2956110d308798f540c22d62150308d584540c21c63553208798f548821e63d5210c5d51318421e63d5110c55513104345524c410
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x4948811800004670020288b84c6a8887055c66394342a22e221aa01949270995414c60a3b2a898a43441c1544c52182ae231aa4204157118d54c820ab8cc7aa441055c663d5110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => packedAt s4K5 (912+((h/16+packedAt s4K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s4K4 (4895+((h/55+packedAt s4K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s4K3 (2420+((h/20+packedAt s4K3 (2280+(h % 20)*7) 7) % 126)*7) 7
  | 2 => packedAt s4K2 (502+((h/3+packedAt s4K2 (490+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf0fffc1f0ffc3fc3c3ffc3fe1c1fc3fe3cf4cf
  | 1 => 0xff0fffe00fffc7fc03e1fc7fe01ffc3f2338f3
  | 2 => 0xfff07ffff0fff87ffc01ff87ffe1ffc1c3cf3c
  | 3 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1421044412284000c0a2408a044241940c5445
  | 1 => 0x22424882a4520c4c2150a45520949829212892
  | 2 => 0x40041108008000910401090049012200428128
  | 3 => 0xaab6252881a95666a74204792d8088db40ec0
  | 5 => 0x8ccc439ccee3267bb399f26103103331fbf000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfae8fae8f8e8f8e8fae8fae8f8e8f8e8fae8fae8f8e8f8e8fae8fae8f8e8f8e8fae8fae8f8e8f8e8fae8fae8f8e8f8e8fae8fae8f8e8f8e8fae8fae8f8e8f8e8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36220
namespace PEqualNP.Outside.L_meta_36220
open PEqualNP.Outside.L_meta_36220.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x41098006000028a54011922a9089a163c1a14e9401e2070600266c016321ca01008901f1c000021a00b8900a15800060e80520800ce2800c600e003001ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x4617c548c2faa7185754e30bf294617d528c37e85186f50a30bf28c617d518c2fca11877cc230fd984617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a261df434c3bc86987750d30ee21a617f524c2f8a4986fd0930dea1261df324c3bc6498774c930ee192617f514c2f8a29877cc530ef18a61dd314c3b862987ecc130ef18261df544c33ea8987795130eeaa261dc544c338a89877d4930ef29261dd524c3b8a49877d0930cfa1261de424c3ba84986750930ee21261df514c3bca2987754530ee28a61df414c3bc82987750530ee20a61df214c3bc42987748530ee10a61df504c3b6a09877d0130ef20261dd404c3b880985fd5030bf2a0617d540c2f8a8185f94c30af298617e520c2faa4186fd0830dea10617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20dfa1641ee42c837a85907b50b20d6a16417e51c82faa3907bc8720f690e41df30c83ba61905fd5220bf2a4417d54882f8a9105fd4e20bf29c41de53882bca7105f54e20eea9c415d53882f8a7105f54a20dfa1441bd42882fca3105f54620bf28441df30883f46110774c220fc98441d930883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20dfa1241ee424837a84907b50920d6a12417f51482f8a2907bc8520f690a41df30483f46090774c120fc98241d930483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf29041bf420837a84105f94420fb288417651082faa2107d54420baa88417e50083be6010774c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43ec83887d50710fb10e21f521c43be6188774c310bfaa4217e54842faa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10bfa94217e52842faa5085f14a10dfa1421bd42842faa3085f94210ef98421dd30843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c524437e84886f50910fb20a21f541443ec42887d48510ef98221dd30443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810bf288217e50043be6008774c010fb88021fa10043ea20087e44010
  | 1 => 0xc535077c86a0ef10d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea9083bf421077a8420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc7be8798f710f31bf296637d52cc77e8598ef50b31ef99663dd32cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c637e528c6faa518efd0a31dea1463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931dfa1263bd424c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418efd0831dea1063de320c7b86418df94431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c877e8590ef50b21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21dea14437e51887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21dfa1243bd42487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043bf420877a8410df94421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53903bca7205794e40bea9c81dd53902baa7206f90e40de21c817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940dfa1281bd42502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206fd0840dea10817e51103eca2205d94440bea8881f551102eaa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3be87987790f30eea1e61dc43cc2fca5985f54b30dfa1661bd42cc3be6598778cb30ee99661dc32cc2fca3985f54730ef98e61de31cc3ba6398770c730efaa661de54cc3baa9987715330efa9661de52cc3baa5987714b30efa16619f42cc3bc85987750b30cea1661dc42cc3bea3987794730eea8e61dc51cc3be83987790730eea0e61dc41cc3be43987788730ee90e61dc21cc3be81987790330eea0661dc40cc2fea9185f95230beaa
  | 2 => 0x100600e0000100100e018008030000100680100e004000060000000281300c0000680503c0080000400a0000001c0000200300003401408000000008008010100280000a0040001b8120800440200f00000002007028010018000020c40000000c0000480200a01000807016010098010020400c00500003400010016004040310080540000000401c00013042004028010040040080100a0000180000000c0c025002008000030000340000400600c00016016010008010000000180300a014000260120000001f00c0000000100800c0480500802c0000305200003800000024050010120480481902c008000090000040e00700c00005805016014028090000000280000002405803002018028040320040701700002c13000024028018130040040100400000c0080000a0240480fbf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f90f42dea1e85bc43d0afca3a15f54742bf286857d50d0b7ea7a16f94f42dea9e85bc53d0b7ea3a16f94742dea8e85bc51d0b7ea1a16f94342dea8685bc50d0afaa9214f55242bf29c857d5390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350bbea6a157d4d42be29a85dc5350ab8a6a16fd0d42df21a85bd4350b7886a17bd0942df212857f5150af8a2a15fd4142be28285bf5350b3ea6a16f94d42dea9a85bc5350b38a6a16fd4942d7a9285bf5150b7ca2a16f54542de28a85bf5050b7ca0a16f54142de282857e5410a7ca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccb7e85996f50b32bf28e657d51ccafca1995f54332bfaa4657e548cb7ca9194f95232beaa465bd548ca7aa9195f15232bea9c65df438cbb887195f94a32dfa1465bd428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132dfa1265bd424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832dfa1065bd420cbbe64197b8c832ee99065ed320cafca2197d94432bb288657d510cbeaa2195d54432bf28065fa500caf4a0195f54032fca806579500cafca7a0df54f41df21e83bc43d06fca5a0df54b41dfa1683bd42d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837
  | 3 => 0xa322220d82299b612ccc0011a4369d0008002881f8be1c9102000000f10000017c9fb37aa94910db60a9c43c90705c8e4000000ae9a16983100086000000000a00000cb0000f88780e6104a9318e10602e8000fa1be434318900002c87806e41a00075202418cc5920004c043000301408c600012d0cc0017223059e1e0000000000000030005a000f3ad800000000000000000000000000003aa9e42c924fa1f6000b6c7c0b90000008280054e608ed0704a23540008427a000a78004a6ae8000333380017f8003a85190f0e45e2a51238000006190c8a629aa618f25e000068002cd3b8b480016522858c9d00000068cbf80039028800000000990001cf4b4c4d282d15dc4c0881733503b93d81f1da4cd970fc4566a95aac1424000a013f64e9502516e49eac0979af5cabe80000c2a8af112000000554001ea0004541201c0006780000042600000291000000000000006582b0000009cc33afd5de0000001500076d482dd0006415f2114022d45fa4e64674565800000280000002d0000000000000000011d000000000000005d485aeb1583a0c5a3631e2b80031417023ca50e5000064000002100000000022e7cc0015d224774afb2d000000e08000006959905032e000a0a61126ad97907634cca1870ca622061501003020d0b7a760e6000042d9146c81810000000010031260c5ad7b11f5ceb1c000d4000a6400000000ac5429015c499c6323135c7b91c2694be521211671ec274589df510000000a80005f86880044c80d57137112b016308a000000a60c8000001978003d2178001a22f4000dc83c616c0c428e743410cf125600000061af038ebed0281e000000000002c47fc37a8e1920108f18c13422c5f1192b0c6c0584831201810b1739c9dd68161036888608cd5184f03dafe0009051a8001c6490c9b0709882c1d9493aa1542d24c33a870de058368aece81c01b04c44b95c2ac6fce992b19887537a811a44ecf29273082d13606d0585155c0831243ac1c0f72a6b28850b007e301948001c0125172ac000000ca8000007b1078000007f40000008e0000009f04a50c000006600002eaab18e7c58b2a344a6b00007d61a200b8800074c991f27850c1c455a660505e46baf809a4a40805c2400288996d5e65394e125000484848944fab854a8005060012c89b5f80500022d2c80993c98e000758d815b5e800017869000a2d0b9fc00029c112974e08f4830000003e557aa8000044002445ae00143adf4e4a849c1570466c8c29d71fec3d9102b272784e21b82d82358ca965488e8a39992cc3cd151bb1ba4b86e2ce0004b0000400001e83118d0030020100180e00e0180a02f000000050080200040001700600c0080b0040000080200c050000010240180001700c0000000201c01c0001400400c0080400401c000020000240
  | 4 => 0x9354900064a690a5b1f398728b901762aab44f220054839549ad00014c002dc0001443e2bf246294ec05b4b8628c02c50002455b9e33c8000a906548a000e5800000b780022916e0007913536c5f47a0005c02f123000000000f41f5306c10002272648200029351ea2546a9f2bc685768fb0d6648aca405640000023b0a8cb046000000358779b5000000ca000000b080026a00000025800000271958000009e8e30004ea8dc292ec3daca8d89263ee001311163f41b12eb0a1cc185259775a80496d1cd052ba94da1021c3f52527f1a646cfc29d15a61c8e1eb026b98551a94ae3383b8b33c08b07aa6b2e87c91a0724a476400000000001119880e80c89a2bd000308002485042556b0d9000000000000000015a0004865a8d38003de1a0079025900e4028005662ed19a141d223800000000000000442c07f974a06000000e900043ebdc6d000634c7400000588c850a8002d2001108000000000b0000404600026d0006f8001702f62bc002cc00021c6217800021800088534388a889633e4d82305920800067942414709329765546602725b00ebd46280303a6ad741e60c07140019a45e4f8000fe4dc0001b80d0c8024001280009542080007a00000000000c3000000148a880031c0005687609854c8fd619a0000540fc8825920001a86a0006dc00000142961719f04f81fc54a8a1328f1880b636664503ad5412008212280009f8818de3bc70c6828404e13c2f9ba000ae45e
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc53082766114c209d584530827a6014c208f992520823d64948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb94942083365494420cd55251083565394420d554e51083374294420cd50a51083365454420cd55151083565354420d554d51083374254420cd509510825e63940209758e500825d65cc020c7953300831d54cc020d5947300835551cc02097d95300831e544c020c75513008356514c020d5545300835a504c020cb553200836551c8020d654e200837151880209bd95200832d5448020d9545200827b6548020d654d200837151480209798f54c425d63d53108f99353c423d64d4f108f99252c423d6494b1097d8d52c425c6354b108f99052c423d6414b109798c52c425d6314b109798f548425d63d52109798c548425d63152109b988548426d62152108fd91538423c6454e10c7d91538431c6454e109798f528425d63d4a108f992528423d6494a108f990528423d6414a109798c528425d6314a10c794f428431d53d0a10c794d428431d5350a10cb949428432d5250a10d654e20843595348210ea509208425e63d51109758f544431e63d5110c758f544423d62d51108f992544423e65151108f588544433561151108f992534423d6494d108fd91534423c6454d109bd89534426c6254d108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d09108f995424423c6550910cd15241442746550510bc18141442746548510c7d53304431c54cc110c7d51304431c544c1109e19520443a94248110f8485204425e63d50109758f540426e62d50109b58b540423d65950108f58a540423f62550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530425f6054c1097581530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48108f992520423d64948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520432e5454810cb551520434e5354810d354d520432e6454810cb591520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d52508109798e500425d639401097597300431e54cc010c7553300434e52cc010d354b300425f654c010c7951300431d544c010d3949300434d524c010cd553100436552c40109e596100436952840109dd9510043355444010d954910043d130440109ed9510043695244010
  | 1 => 0xc31c54cc530a7992314c29d648c530c7151314c354514c530a758b544c29e6495130b6582544c2db6055130a7994544c31e6515130a7588544c29e6494930a7592524c31c5494930b6582524c29f6454930a7191524c2d76154930b5185524c2db6054930a7990524c29d6414930c7150524c2d66114930b5584524c29e65d0930a7197424c29d6490930b6982424c2d9609093097d95424c25c6550930c7d95424c29e6550930a7195424c31c655093087195424c38f6250930a7990424c2da6010930b6580424c31c54d4530a7992514c29d6494530b6582514c29f6454530a7191514c31c5454530b3d89514c2cc6254530b6d81514c355511453097996414c25d6590530b6d81414c2d86050530b6980414c2d96010530a7993214c29d64c8530b6983214c2d960c853097d95214c25c654853097994214c25d6508530a7990214c29d6408530b6980214c2d96008530c7d53504c31c54d4130e6d53504c39854d4130b658b504c39b42d4130e650b504c25e659013097994404c2ce6210130b3588404c2d66110130b5584404c39940101309798f540c25e63150309b988540c26d62150309d984540c27561150308f992520c23d6494830c794f420c31e5350830cb949420c32d525083097d95300c27b654c030d694d300c32e629532097d8d54c825c6355320c7d8d54c831c63553208f99353c823d64d4f208f99053c823d6414f209d98453c82756114f20cb95142c82af6550b20cbd9542c838f6350b20e318d42c825f63547209718d51c82ad64c8720c795330c831d54cc320e350b30c831e544c320c755130c838d424c3209798f548825d63d52209798c548825d63152209d98454882756115220d6982538823f6454e208f191538831f6454e20c7191538831e53d0a20c754f428831e5350a20c754d428823f64546208f191518835a534c220b6d95308835b654c220e6d913088398644c220e6d093088399424c22097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d20ab592424826c6550920cbd95424832c6550920e3d8d424838c6350920ead8142483a860509208f990514823d64145209798c514825d6314520ab593214838d42cc120b658e30483a9428c120e35093048278654c120ea509304835b654c120d6195304839b644c120e619130483cb624c120f2189304839b424c120f29093048399424c120f25093048389424c120f2c8530483c9214c120ea50b20483c930881209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798
  | 2 => 0x624c5218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530865d6094c21c7951530871d5454c2197d81530863e6414c218f590530865e6314c219d984530867a6014c219e580530863e64948218f592520863d65d0821c794f420871d53d08218fd95420871e5350821c754d420875553884219bd9521086776548421d554d21087a542484219798e500865d6394021ce95250087395494021d694e50087595394021d698e50087596394021ced0a50087394294021ce95150087395454021d694d50087595354021d698d50087596354021ced0950087394254021dac8550087722154021da4855008771215402197d8d52d025c6354b40cb54b42d025e63947409758e51d031d5310e40c794f429031d53d0a40a718d429031e5350a40c754d429032e5250a40cb549429029e6390640cbd49425023e65d0540c754e43102b96010c40d394e521034d5394840d394d521034d5354840cb991521032e4354840cb10d521031e53d0840c754f421032d52d0840a718d421031e5350840c754d421032e5250840d594e51103555394440d994a51103655294440cdd0a51103354294440d594d51103555354440d994951103655254440cd90d51103344354440cdd09511033542544408f596411029e6390440cb54a41103355190440cb54841103355110440cb54b401033551d00408fd95401032d5250040cd545401027b65500409d98754cc27561d53308f99252cc23d6494b30a799232cc29d648cb30a799032cc29d640cb30b598432cc2d5610cb308f99251cc23d6494730a799231cc29d648c730d554431cc2d661d5330b558754cc2d960d5330b658054cc2d960d4b30a799252cc29d6494b30a799052cc29d6414b30b598452cc2d56114b30b658052cc25f6550b309719542cc31f6550b30c719542cc38f6250b30a799351cc29d64d4730b658351cc29e6494730a759251cc3555114730b658051cc25e65907309759641cc29e64c8730a759321cc25f65487309719521cc25e65087309759421cc29e6408730a759021cc2da6008730b658021cc2ce6210330b358840cc2d66110330b558440cc26e62152309b588548c27661152309d584548c23e6494a308f592528c32e5250a30cb549428c31d63d51308f58b544c23e64951308f994544c31d63151308f588544c25e65d0d30c7152434c25c6550d30c7d50434c23e64149308f590524c27661149309d584524c23e65d09308f197424c23e65509308f195424c29e648c930a7592324c31c548c930b6982324c29e640c930a7590324c31c540c930b5984324c2d5610c930b6980324
  | 3 => 0xd42a798e5350aad6294d42abd895350a9e6514d42c79945350a9d6014d42c7d4f5250b1c53d4942e3d4f5250b8c53d4942ab5835250b1c53d4542a798e5150a9d6394542a7d8d5150a9c6354542c714d5150abb6054542ae1815150b355114542a798e5050a9d6394142c714e5050a9f6354142a718d5050ab76154142ad1855050a9e6314142a758c5050b1c5314142ad9845050ab561141428fd954210a6f6550842cb9514210a5e63940429758e5010a3e64947328f59251cca3f64543328f19150ccb1f6355232c7550438ca7661951329d586544ca5f63551329d987540ca7561d50329e983540ca7960d50328f596540cb1c63550328f990540ca7661150329d584540ca7a60150329e580540cb1d54d0c3297594430cacd6210c328f992520ca3d64948328f597420ca3f655083297d95320cb8d424c8329bd95320cb365494432cd552510cb374294432cd50a510cb365454432cd551510cb574354432d510d510cb374254432cd509510cb573254432d54c9510cb3a5494032ce552500cb725194032dc546500cb3b4294032ce50a500cb3a5454032ce551500cb725154032dc545500cb5a6354032d6d0d500cb584354032ced09500cb394254032d6cc9500cb593254032cb54b42d069c6350b419798e50d065d639434197582539065f6054e41c794f429071d53d0a41c794d429071d5350a41cb549429071e53d06419798e509065d6394241ad986435069c6350941cbd4942506b46150941a798e415065e63141419758c505066e62141419b588505065f63548419718d521072d52d0841ad587421063f65504419dd95411065e63940419758e501067a60d53319e58354cc63e6494b318f59252cc63d62952318fd89548c63e6494a318f592528c63f65d0a318f597428c63f6550a318f595428c71e548ca31c7950328c6d5610ca31b6580328c71e54cc6319b98a544c66d629513197997434c6d661d0d318f990524c63d64149319e980524c6796014931cbd49424c72c525093197997324c69e648c5319798f540c66e62150319b588540c67a60150319e580540c63e64948318f592520c72e5250831cb549420c65d658c831b5584320c6d9600c8318f992510c63d649443197d95310c677654c4318fd91500c63c645403197d8d54c865c6355321c7d8d54c871c63553218f99353c863d64d4f218f99053c863d6414f219e98053c86796014f219798e50c865d63943219798f548865d63d52218f993538863d64d4e219798e508865d63942218fd91508863c64542219798e544865d639512197d8d544865c63551219ed81544867860551218f993534863d64d4d21c7993534871d64d4d2197583534865e6394d219799453487556114d2197580534871f53d0921c714f424871f5350921c714d4248754538c5219d19531486e4
  | 4 => 0x4000000000000000e6de001a6800376220001ae52815400000570bdc00000000859ab800000868000000000016ba9b652d2d6ea7910a6354fa1f1b0ae93a8000000000000012a000001313c00a1b4800000001918000000000023b4a80010a94a05e32825000000000c624c1dc9c4002a500000000000000b380021c14400000000000000708000003d80011f64c000001a107ab24bf197000000000000009c800000000c50000000000018880000000184000000000dd28300000000000000000002f4000000000000005cc000963d20000000000000000000000b000014424a00000000000aa1860005b05555e2780000000000068c000000000000000b94f068850001ee5b40006a82903498139a8d4cc00195000270600000005c0cc4459df12692d3f800000001941f51289b5b983c19841518b560005b80020f000000002ed000000000000000018980000000000000000b193d2d9402000578000ea0017331000015c000003f60007aa050004b8000003ba0000000000000000224000398000c300000000000000000000002e0000e981b0001dc0017259e0001b800000784002be11a1580033f000000001db000b79a830b150c6c000000000000022d3b86c400000000000001cb00000000000000000024070000020000380f0000000b8000300140000100a008028010000080080600a014028020040080180400001c0080b024010000030040000200500004c0000000000c0080e0040000000b0060000000000000406812004000000000000040780100a0040680000e0000500e02000401001004014000010060100080001a0040480000200c0680000800c00000002000000000020100080300a0040200400000400008000000090000080040180a000000010090000200100000000402805006010000030060040000200c0300080000c000008000080100100f01600c008010060000000000000407000006004048000000000500000000000801004000028000040000000b00002c008040000000000100a000008030000000600100e0080700600005c0180100400400002004000018000300000000400e0140001300600c0700002c0040000c00000000800000004050020080000080300000409001006000000080020000100000a00802812000014008000000040300000200c010010000080380900000c0000800401c01800000008028008fd954310e5f6550c439798e51d0a5d63947429798e50d0a5d6394342ab58b53d0ab661d4f42ad58753d0aad6214f42a798f51d0a9d63d4742a798e51d0a9d6394742cd54451d0a9e6394342a758e50d0a9e6314342a758c50d0ab66114342ad58450d0a5e63942429758e5090a5d60d4d42975805350b1c53d0d42c7d4c4350a5e63141429758c5050a7661141429d5845050a9d60d4
  | 5 => 0x171105f25b0001c50002dc0029e27a2c05c00000014c0000000000000000000000000000006d80013c68e2ac002dc6380000034400071800061456000000000005fc001c121a001be20d0008e43f00000000085800284000e1018000bf00033e088000000003ee00062a21000c59bbaa40007d836a9a000c0d802d252a3bca4a041360014e0000001d000124302000f68b30000000022a00000400000000001420006f64f8280004b83819e34e00046d060002ca00192000000cbc4fae835e88c0000000060c6d9d800016550000000000000e3000cdc000003ae7e4000602f0000bc886450000af8e45ea520b2000554b58fc1ea2c6000dbb5a48e0014ca20106b0c5294b6ced84d51e81a82980021e0000f8fd0002b20b19393900059d8100001000000000000000000006844c09480028e00114aff0000009db390009dd901092d2d0c941916f0af4e70790deaac000006e496d8f966218b40b4000000b106bb7400000000222000000000000009b0c40000003442100046e9740000f00000000371000bc4a9000000d9800000000088000000002b400000256694001e6424b901ca080b61c4a334c67697800000572000c71233fa000001a018055c00000000001913350000000026b61a000d11d11901d8cfac8000000769a8412b7c000000000000016d00071cb10b9398c28002520009000f81547a104050450707bc00349000000048005e6001aeabb00000000000000000000004dcadca29c8000ac047b7d51c0001836d0000007ba022ea4d9440a135a5f0681ca0b40d53433400001c000004e8000000000002700008e0009bc000b42f600174800000558a88000000000000002248000000000568ffa51274740e200066cabccc2eb56a3f432b7922e1c953249000000620271fc408001d40000000000000000130a8100c000002d5000d7c2382b4fc001aaa6700a4cccf00009017c11a5837e6ccf60004be00038000000b30800680000011f19a55c2f99680000061c1d9d225e0840002a0000016a1900182248a8000008c8938d2000a6000000000c3950b1d0000006eae500000000000656000000000000000015c0001601f84b080000000000002ec000026600700a0ea0000000020e05a0002a00061e174b017400000160800336000001e30006c8d4800000000000003160011b176000be80004c1e8000be800000001018006c45510d94c09c73d9612c6dcd603187a478b89a99126c69c1822e1140c1d450c64c80783e1b92ee10ca6916392000000df0001ad7730100000000126040c95448f95f6000398b6522ce000213000489688000000000036c1b464c00000000000000000000000000020ed50002ca62ed44792190f08740003a000000da0006c8be00000000000000000000d14548001d0a5c000001e2001498000002f
  | 6 => 0x1b2a8f1b2000002a94608989680000029c9f80045e00132b754586e1312906b6000000000dc46903800000000002ad0000000000000037000000000840f3ad31f42e93490e182d481934016289d000922b6acd51aec3863cc0000000094c00000000c84fa0ac4664608400000077800000000de8000250000000000023c0000036b0009104c000000000001f153aad800000000000000e70c400000000000000002ac000a007e29612e0013db680208940009e31e0009ba2e000000000000000000010f0001b0519f332800183218694000000b54aa3ec0007f6746c1053322e2001461eb48c000fe000178934000006d409800000516bbc000000000009a903000b6cbd185132000000000a4b158c800000410451bc4b2338909b51d600000000000a1ceb000000818002340166598c1d9596664000bf268000ce00002600000000416958000000000000000015c93855141562d65b801948a85c7faea682230ed119612610b0b4f3566b1781a708c8e8122cd4ae00c489be3ca124e03481924c8699130d40002f1f049e9a8a18005fc000c1000000000a7000000000d3305202ad0000000004287616a00054caf000000909538de486334400001e0969bb1e21089d800000196bc8090d650ab095f950000000002920627540011162a290b5a500003e18927d6bc0000000000000000000000000000e550400000248000928ce8000000001b0000000002e2c73140003e91d0ce24000195000bd800000000bf4003604f88e0000c7254a8997000000ac8411f2634000002e72385004095d46accc0e989228790ff09a30c844831920d21ecb780d2b03880000013a68c199bd00021c002410002c8020644c60000000067a0002680047e000000660000000000039ab8d43000348000000000000000031e6b80006104f00033c288e902c
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x13800c80131f9980158680208001800a011a8000001d800e88808012128004000000179a098d0011001b880f8000140000109b0f00020a800b000b9c0014919d03850021059c9e16000780000321800d9f02970019000015002000168018090700188480000c0e1e8006100000000228003080000c020808402000800800380c30a6302a2a1530705445150a8cb80a6282858514d6114142a8ae421aa219705424c9510caa4b9086a8065c250932540328b2e031aa420d0d72950328c70b2a2c21946386951600ca31a52e02928498c2d72191500c60f3b6a6a1243385c0624c521e0aa6a124210f21424855008694b8086a9081265c06350840a62e021aa22051473509511024cb84c7208818398d5290440c2cc6a8c822041d76150324c286b90a81926185151610c930a1ae42a0a49861454584524c20f3accaa1261831506254530a88e4a88a2984c972181414c20e3aac990a61a25894010130d22c2a00809841c7655130c82463b28498641071d95350a20930eca12611060c6518d42482c4b80c6a1241625cc6050920d10c630284905a17118142482463b284982412a1d9424c120c30ca32260905897219130482c4ba0c498241a2190624c120b82e2312609058974909304824c3b28498241321d9424c120d16eca12609058a7650930482c43b28498241a21d9424c120910eca12609058974c85304820e3b2a6a1421c254d42482109c2e4302828841e76d513044388aa26088021d05493044010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1230382c0000d2016a3004741422a407a118014d6114142a0582951610ca31a0982951600ca31911801cd4254440a098098d5290440a118098d5190440a0582151610c930a05821516114930c08655c06350920c80635c46050920c08655c8644c120c80645c4624c12088a869d9424c120888865d3214c1209088754d4248210
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
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
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 58)*7) 7
  | 5 => packedAt s5K5 (25143+((h/273+packedAt s5K5 (22140+(h % 273)*11) 11) % 1083)*11) 11
  | 4 => packedAt s5K4 (37250+((h/298+packedAt s5K4 (33972+(h % 298)*11) 11) % 1569)*11) 11
  | 3 => packedAt s5K3 (3486+((h/22+packedAt s5K3 (3332+(h % 22)*7) 7) % 108)*8) 8
  | 2 => packedAt s5K2 (925+((h/5+packedAt s5K2 (900+(h % 5)*5) 5) % 20)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc7f8ffff078ff1f871e3e3ffe383f0fe0cf4cf
  | 1 => 0xf87f0f8ff80ffe3f81fc7c707c03ff1e7348f3
  | 2 => 0x7ff00ffff1ffc7fe007f807ffc7fe1838f3c
  | 3 => 0xff80000ffffe0007ffff80007fff8001fc0fc0
  | 4 => 0xfffffff000000007ffffffff80000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x50082101101022001020809120889044041445
  | 1 => 0x831242122124c04180c4242244112618314892
  | 2 => 0x242004244201000a2200490409204880828128
  | 3 => 0x1106ab4895086494d5690009725a024d5c0ec0
  | 4 => 0x2644cc00e64d89276992724e00600c91ebe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36220
namespace PEqualNP.Outside.L_meta_36220
open PEqualNP.Outside.L_meta_36220.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x24719000c6244e816804478a1d00bd906005892b34fd4000441f2e4cdc505582079778e4f8474000a3683439b4a84a9100f40335401b0000d401c76000290001c0b6000000624c01811000800104040821400b800004a031228900027fd5007fe54027f55007fc54027fd4c05fe53027f54c05fc5301ffd0c05fe43007f50c05fc4300ffd48037f5200ff94803fd5200df54803fc5200ffd0803bf4200ff90803fd4200ef50803fc4200ffcc803fe3200ff4c803fc32027fd4409fe51027f54409fc5101ffd0401fe41007f50407fc41017fcc401fe31007f4c405fc3100ffc8403fe2100ff48403fc21027fd4009fe50027f54009fc5001ffd0001fe40007f50007fc40017fcc001fe30007f4c005fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200eff59510075faca8803bfc65440097e32a200edf19510024f8ca88003ff64440017fb222000efd91100057ec888037fe64440077f3222000ff59110005fac888037fc64440077e3222000ef1911001d78c88803bff544401bff2a2200eff5511006ff8a888003ff63440017fb1a200cff98d10015fcc688003fd63440017eb1a200cff18d10015f8c68803bff5344019ff29a200eff54d10067f8a688037ff4344019ff21a2000ff50d10067f8868802fff62440177fb12200bff9891000dfcc48802ffd62440177eb12200bff1891000df8c48802fff5244017bfa92200bff9491005ffaa48802f7d5244017fe292200bffd091005f7e848802ffe4244017fea12200bef5091005ff8848802fff3244017ff192200bff4c91005ff8648803bff514400bff28a200eff5451002ff8a288037ff414400bff20a2000fd90510007fa8288003f5414400bfe20a200cffcc51002ffc6288003fd314400bfe18a200bffc851002ffc428802ff62144017fe90a200bfd4851002ff8428803bff504400dff282200eff54110037f8a088037ff404400dff2022000ff50110037f88088033ff304400dff1822000ff4c110037f8608802fff204400dff102200bfe8811005ffa408802ff9204400dfe1022005ffc411002ff6208801bfe104400dfb0822006ffd9410035feca0801bfe65040097f3282006df99410024fcca0801bfd65040157eb282006df59410004faca0801bfc650400d7e3282006ffd9010035fec80801bfe64040077f3202006ef9901001d7cc80801bfd64040017eb202006ef590100057ac80801bfc640400d7e320200affd501004ffca80802bfd5404013fe2a02006ffd8c10035fec60801bfe63040057f3182006f798c10015bcc60801bfd63040017eb182006f758c10005bac60801bfc630400d7e318200affd4c10047fca60802bfd5304011fe2982009ffd0c10047fc8608003fd4304011fe2182006ffd8810035fec40801bfe62040037f3102006fb9881000ddcc40801bfd620400f7eb102006fb58810005dac40801bfc620400d7e3102007ffd481003efea40801ffe520400ffea902007df5481003ff8a40801fff420400fdfa102007ff9081003ffa840801fbd420400ffe2102007ffcc81003ffc640801ffd320400ffe1902005bf9841002ffea208017fe510400bfea882005ff1441002ffe8208017fe410400bfea082005ff1041002ffe6208017fe310400bfe9882005ff0c41002ffe4208017fe210400bfe9082005ff08410035fcc00801bff500400dff2802006ff54010037f8a00801bff400400dff2002006ff50010037f8800801bff300400dff1802006ff4c010037f8600801bff200400dff1002006ff48010037f8400801bff100400dfb8802006ff84010037f4200801bfd100400dfa8802005fe44010
  | 1 => 0x7ff504c00dff2826019ff54130037f8a098063ff404c00dff2026000ff50130037f8809800bff304c005fd9826006ff8c130037bc609801bfc304c00dee1826002fe0c1300bffe409801bfe204c02ffd1026017ff481300bff2409801bfc204c00bffb2e2005bfd971002ffccb88012fe65c400bfeb2e2016bf5971002ff8cb88016fc65c400bffb262005bfd931002ffcc98800efe64c400bfeb262000bf5931002ff8c988016fc64c402dffaa62015ff953100b7faa988057fc54c400bffb1e2005bfd8f1002ffcc78800afe63c400bfeb1e2000bf58f1002ff8c788016fc63c402dffa9e2014ff94f100b7faa788053fc53c402bffa1e2014ff90f10007fa8788053fc43c400bffb162005bfd8b1002ffcc588006fe62c400bfeb162013bf58b1002ff8c588016fc62c4027ffa962013dfd4b1009ffca58804ffd52c4027bea962013ff14b1009ffe858804fbf42c4027ff2162013ff50b1009f7a858804ffc42c4027ff9962013ff8cb1009ffa658804ffc32c400bffa8e2005ff9471002ffaa388017fc51c400bffa0e2005ff9071002fec8388017fd41c4001faa0e2005ff1071002ffe6388017fe31c400bfe98e2005ff0c71002ffe4388017fe21c400bfb10e2005ff4871009fea4388017fc21c402dffa862006ff943100b7faa18801bfc50c402bffa062006ff90310007fa818801bfc40c4029ff9862006ff8c310007fa618801bfc30c4027ff9062006ff8831009ffa418801bfc20c400dffb2c2006bfd9610037fccb08012fe658400dfeb2c2012bf59610037f8cb0801afc658400dffb242006bfd9210037fcc90800efe648400dfeb242000bf59210037f8c90801afc6484025ffaa42011ff95210097faa908047fc548400dffb1c2006bfd8e10037fcc70800afe638400dfeb1c2000bf58e10037f8c70801afc6384025ffa9c2010ff94e10097faa708043fc5384023ffa1c2010ff90e10007fa8708043fc438400dffb142006bfd8a10037fcc508006fe628400dfeb14200fbf58a10037f8c50801afc628401fffa94200fdfd4a1007ffca50803ffd528401fbea94200fff14a1007ffe850803fbf428401fff214200fff50a1007f7a850803ffc428401fff994200fff8ca1007ffa650803ffc32840177eb0c2012ffd461002ffca30804bfd518400bfe28c2011ffd061002ffc8308003fd418400bfe20c2010ffcc61002ffc6308003fd318400bfe18c200fffc861002ffc430803ffd218400bfe10c2006bf98210037fea10801bfe508400dfea842006ff14210037fe810801bfe408400dfea042006ff10210037fe610801bfe308400dfe9842006ff0c210037fe410801bfe208400dfd1042006ff4821007ff2410801bfc208400dff8842006fdc421002ff6210803bff654401d7fb2a2000dfd9510004feca8803bfe65440097f3
  | 2 => 0x40007f8c2a0016fc615003fffa8a801fff945400fffaa2a007ffc5150007ffa0a8003efd054001ffc82a000ffd4150001dea0a8003ff105400f7fe62a0003fe3150001fe98a801eff0c5400effe42a0077fe215003bfe90a801dff0854001dfec0a007fff505000dff282801fff54140037f8a0a000fff4050007fda028006ff901400377c80a001bfc405000dde2028003fe101400f7fe60a001bfc305003bff9028006ff881400effa40a001bfc205000dffb2c6006bfd9630037fccb18012fe658c00dbf32c60049f99630037facb18072fd658c00dbeb2c60009f59630037f8cb1801afc658c00dffb246006bfd9230037fcc91800efe648c00dfeb246000bf59230037f8c91801afc648c039ffaa4601bff952300e7faa91806ffc548c0057eb1c6002ffd4e30017fca71800bfd538c005fe29c6002ffd0e30017fc871800bfd438c005fe21c6006ffd8a30035fec51801bfe628c0037f3146006ff58a300d5fac51801bfc628c00d7e314601affd4a300d6fea51806bfe528c035fea94601adf54a300d7f8a51806bff428c035dfa14601aff90a300d7fa851806bbd428c035fe2146002ffcca30017fc651800bfd328c005fe1946006ffd8630037fcc318016fe618c00dfeb0c6000bf58630037f8c318073ff518c039ff28c601cff546300e7f8a31806fff418c001ff20c6000ff506300dff8831800bff318c005ff18c6002ff4c630017f8631806bff218c035ff10c601aff486300d7f8431801afe608c00dffa846006ff94230037faa11801bfc508c00dffa046006ff90230037fa811801bfc408c00dff9846006f7cc230017f6611801bfc308c00dfc1846006ffc8230037fc411801bfa208c00dfe904601afe48230037f84118067ff654c0337fb2a6019ff99530025fcca98067fd654c0337eb2a6019ff19530025f8ca98003ff644c0017fb226018ff9913001dfcc898003fd644c0017eb226018ff1913001df8c898067ff544c031ff2a26019ff551300c7f8a89801aff634c005ffa9a6019f7d4d30017fca69800bfd534c005fe29a6002f714d30017fe869800bfe434c005ef21a6002ff50d30007ba869800bfc434c02fffb126017bfd89300bffcc498006fe624c02ffeb126017bf589300bff8c498006fc624c02fffa926017dfd49300bffca49805ffd524c02fbea926017ff149300bffe849805fbf424c02fff2126017ff509300bf7a849805ffc424c005ff9926002f7cc930017fc649800bfd324c02fee9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298016fc614c033ffa8a6019ff945300cffaa298067fc514c031ffa0a6000ff90530007fa8298063fc414c005ff98a6002f7cc530017fc629800bfd314c001ee98a6002ff0c5300bffe429805ffe214c02ffe90a6017ff08530015fec09806
  | 3 => 0xea1a6202ff10d31017b8869888fff624c4477fb126223ff9893100dfcc49888ffd624c4477eb126223ff1893100df8c49888fff524c447bfa926223ff9493111ffaa49888f7d524c447fe2926223ffd093111f7e849888ffe424c447fea126223ef5093111ff8849880bff324c405ef9926202ff8c931017fa649888fdd324c405fe1926202bfd853112ffea298817fe514c44bfea8a6205ff14531127fe8298817fe414c401fea0a6205ff10531017fe629880bf7314c40bff18a6205f78c53102ff86298817dc314c405fa18a6223ffc853102ffc429888ff6214c447fe90a6223fd4853102ff84298803ff604c4017fb026200ff98131007fac098803fc604c40d7e3026225ffd413112ffca098897fd504c44bfe2826224ffd0131127f8809880bff304c405ef9826202ff0c13111ffe409888ffe204c447fe9026223ff08131037fecb2001aff659000dff32c8004bf99640037facb2008afd659000dfe32c8006bf1964001dfac92000fff5490007ff2a48003ff5524001ff8a92001bff639000dff31c8002bf98e40037fac720002fd639000dfe31c8006bf18e40117fea720087fe5390045fea9c8021ff14e4001ffe872000ffe4390007fea1c8003ff10e40037fec52001aff629000dff3148001bf98a40037fac520082fd629000dfe3148006bf18a40107fea5200837f5290041ff2948020ff54a40106faa520083fc5290007ffa148003efd0a4001ffc852000ffd4290041dea148003ff10a40107fe6520083fe3290041fe9948020ff0ca40037fec32001bfe619000b7f30c8006ff58640005fac32001bfc6190045ffa8c8022ff94640117faa32008bfc5190007ffa0c8003ff906400077c832000ffd4190007fe20c8003ef1064010ffe6320003fe3190001fe98c8021ff0c640107fe4320083fe2190041fe90c8020ff08640035fcc12001bff509000dff2848006ff54240037f8a12001bff409000ddfa048003fed0240037f8812001bf8409000dff9848006ff0c240037fe412001bfe209000dfe9048006ff082400fffecaa007eff6550001bfb2a80009fd95400fffccaa0012fe655003ffeb2a801fbf595400fff8caa0012fc655003fbe32a80049f19540035fec8a000fff5450007ff2a28003ff5514001ff8a8a0003ff63500017fb1a801eff98d40015fcc6a0003fd635003dfe31a8002bf18d400fffea6a007bfe535003ffea9a801eff14d4001ffe86a000ffe4350007fea1a8003ff10d400effec4a0076ff625003bff3128001bf989400effac4a0076fd625003bfe3128001bf189400effea4a00777f525003bff292801dff549400eefaa4a0077fc5250007ffa128003efd094001ffc84a000ffd425003bdea128003ff109400effe64a0077fe325003bfe992801dff0c940007fec2a0002ff6150001ff30a8000ff585
  | 4 => 0x80fbc409045bff984822dff0c241167fe41208b3fe2090459fe904822cff0824115ffecaa08aeff6550457ff32a8204bf9954115ffacaa08aefd6550457fe32a8204bf1954102dfec8a080fff5450407ff2a28203ff5514101ff8a8a0803ff63504017fb1a822aff98d41015fcc6a0803fd6350455fe31a8202bf18d4115ffea6a08abfe5350457fea9a822aff14d4101ffe86a080ffe4350407fea1a8203ff10d4114ffec4a08a6ff6250453ff3128201bf9894114ffac4a08a6fd6250453fe3128201bf1894114ffea4a08a77f5250453ff2928229ff5494114efaa4a08a7fc5250407ffa128203efd094101ffc84a080ffd4250453dea128203ff1094114ffe64a08a7fe3250453fe9928229ff0c94101dfec2a08afff515040bff28a822bff5454102ff8a2a080fff4150407fba0a8205ff9054102f7c82a0817fc415040bde20a8203fd10541157fe62a0817fc3150453ff90a8205ff8854114ffa42a0817fc2150401ffb028200bfd8141007fcc0a0803fd6050401fe3028206bf1814115ffea0a08affe5050457fea82822bff1414101ffe80a080fbf4050407fe202822affcc141157f860a08a7ff2050453ff1028229ff4814114ff840a0817ff658c40b7fb2c6205ff99631025fccb18817fd658c4517eb2c6205ff1963102df8cb18817ff648c40b7fb246205ff9923101dfcc918817fd648c4017eb246205ff1923102df8c9188a3ff548c44fff2a46228ff5523113ff8a91880afd638c405ffa9c6202ff94e31017faa71880bfc538c405ffa1c6202ff90e31017fa871880bfc438c40bffb146205bfd8a3102ffcc518806fe628c40bfeb146226bf58a3102ff8c518816fc628c44dffa946226dfd4a31137fca51889bfd528c44dbea946226ff14a31137fe851889bbf428c44dff2146226ff50a311377a851889bfc428c405ff9946202ff8ca31017fa651880bfc328c40b7f30c6205ffd463102ffca318817fd518c40bfe28c6205ffd063102ffc8318817fd418c40bfe20c6205ffcc63102fbe631880bf7318c40bfe18c6205fd0c63102ffe4318817fe218c40bfb10c6205ff48631137ea4318817fc218c40bffb046205ff98231035fcc118817fd608c4017eb046205ff18231147fea1188a3fe508c451fea846228ff1423113ffe811889ffc408c405ff9846202ff0c231137fe411889bfe208c44dfe9046226ff0823112ffeca98896ff654c401bfb2a62009fd953112ffcca98812fe654c44bfeb2a6225bf5953112ff8ca98812fc654c44bbe32a62049f19531007fec898802ff644c449ff3226203bf99131007fac898802fd644c449fe3226203bf1913112ffea898893fe544c44bfeaa26224ff1513102dfec69880bff534c405ff29a6202f794d31017faa698897dd534c405fe29a6202ffd0d31127be869880bfe434c405f
  | 5 => 0x82a004000008730040f80380000204402024004000000030000100000300e0240180100a0000f00b01c01c0480e0080000000100e0180080600201c0000100600c0300800c00005806036000020000140040200100a02c0400601200c3a00103e0000000103a0000000807200c1c8010100200200e0060cc0080d0160800081e00607c0301900200002805010070000280040040300200e04400800002014000040561080380704200807002000098098000020040982200a0000180002202c0080100e0100300601430ffd9543185fecaa18037f6550c013fb2a8630ff99543025fccaa18c3fd6550c617eb2a8630ff19543025f8caa18c37c6550c093e32a8602bfd914301ffea8a180ffe5450c07feaa28603ff15143015fec6a180bff5350c05ff29a8602ff54d43017f8a6a180bff4350c07efa1a8602ff90d430177c86a180bfc4350c05de21a8602f710d4317ffec4a18beff6250c5fff3128601bf9894317ffac4a18befd6250c5ffe3128601bf1894317ffea4a18bf7f5250c5fff292862fff5494317efaa4a18bffc5250c07ffa128603efd094301ffc84a180ffd4250c5fdea128603ff10943017fe64a180bfe3250c05fe9928602ff0c943007fec2a1802ff6150c01ff30a8600ff58543007f8c2a1816fc6150c61ffa8a8630ff94543187faa2a18c3fc5150c07ffa0a8603ff10543017fe62a180bfc3150c5fff90a862fff8854317ffa42a18bffc2150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028606bf18143187fea0a18c3fe5050c61fea828630ff1414301ffe80a180ffc4050c05ff9828602f7cc143017f860a18bfff2050c5fff102862fff4814317ff840a1817ff659040b7fb2c8205ff99641025fccb208177e65904093f32c8205ff59641175facb208177d65904013eb2c8205ff1964102df8cb2080efd6490407ffaa48203ff9524101ffaa92080ffc549040bffb1c8205ff98e41015fcc720817de63904056f31c8205ff58e41005fac720817dd63904016eb1c8205ff18e4102df8c7208bbff539045bff29c822eff54e4116ff8a72080fff4390407ff21c8203ff50e4101ff88720817ff629040b7fb148205ff98a4100dfcc520817fd62904597eb148205ff18a4102df8c5208b3ff5290459bfa94822cff94a41167faa5208b37d5290459fe2948203ffd0a4101f7e852080ffe4290407fea14822cef50a4101ff885208b3ff3290459ff194822cff4ca41167f86520816fe619040bffa8c8205ff9464102ffaa320817fc519040bffa0c8205efd064101fee8320817fc419040bfa20c8205ffcc64102ff86320817ff219040bff10c8205ff4864102ff84320817ff609040bff3048206bf9824102ffac120802fd609040bfe304822effd4241177fca1208bbfd509045dfe2848203ffd024101ff88120
  | 6 => 0x8f751e87f4e00dc8e351680009391b0d344d4af4304090b740004dc9d0744dd49709454005f0001004000b7c000c9c000b044b800110479482c2f0d890c09f8de53191212f4d30c10000000000238ef49200011a0d48824000ee466c06897848019c57cc24508310a64ab44940002542711a800000109c000a94c59284b0c3d4b4400000043ceb90e49d40000013009e80005ac750cb047000000000004118d390ad46a81e0abd16d0b8f90168e0c294be0a049cc5b48e4070c1918500c9b8c3c1a03a4bbc1fd279210964e4c84d0607e93d50a0ae0a8ca5c2c86d8fd4a28de03444c41e5308ce809d3a511cd80ddc4e006c534001164f80ec400040087477c6aca3cbc4300981288b88d00f945e926c7b4e1c844fecc30d3c42cef13047bc37c7acdbc6cc7ec6a032c39c03012d084908988fe447c8501d9395324ebd19c868c0039023400c6e53c51884345b00342a8968fd85580846287c0fc4afd1fc55cac434c2f888065c2740dc70c9487d02591b4ff8b18fd07750fc7d4f40b280003bcf710d0000000000adc721378000500d6ccf88a50c4000001234900954a013e0000248a84d680009c437107ced892c0000002d88b404cf300003180d4d78c513390409ac000000c941040c4d751f426cf984f800099c0000000001bd2d00000000f4bdc4303e53700000d8001154c3861c000e24000cd9360e80cacf28e547f88d0cd4c2c80c000a2ce3c11cf18000000c449f4f507cd1ed37503410905cfc920023c9753b0f45108ca46e0b3cf391dc76c0f81c0924f2c580a743089504680000000cc5640000011f133d14887d0ccbec59c8f8f60210d70b589e0bf0d0cd106a432035ca7cff48481dc0010740012242453680000005c00000000000180000600a020040020000941783101400c0180002206c0500c00000800001002008030020020001683300a0cc030000000040501100002c0000001803037002000000000000280bc000370080040000000e0c4058000100000100200a0080000100001c00009008074020010180141100300002c000070a600003014006010050040180300f80800000000003000048000010120002b8020120001480001e00c0180100000c0b82d010000008110020180100001a018048060020000080300a040058540000000100300003c0b80100e01c0380100a0242380501c0200c822002008070000020180600603400c040090020000600001a004058100020000000300c048150060000600300001a010008030100300000b002020030050180440080400000c0000000006c0c806034040098000000fc1501d0060080000501c008068030000080002901e0000000100a0080080b00201c038000600180300500000000004002000000080ec000050000060000081700803800801034008000190040080b
  | 7 => 0x1ac2cccfcf68000f48000c80a2485c6884205ec0fd22c0011d8000edc000a40fcc0ec18cf88e041583b5380548d2c2b85d901c62c6f4d28bf8000a484a01701509603b85c84601a4d600003885dc784730000000120c7c000b900004e4e18d200001b08913dc1004c07e440817c051128df0b100b87e0910b080000000006113b827c9ec0f08c4668d5d274fa508c000000a181913b4f640012d50553851753547090dc1f4b380001a85d0424df5228144704818be8728458e848003d0000f0c478cf400013d1580008a02191d0000000000448000180a20594000000001294d44338000000da42c007d3e43588bc00133045cdc000000050400104cc64e5083530d1140002a0b4849134c20d3346ec1412640a81f8a1ca54e2033c148748554740c746f8ce40080001ecbb431cd9c798ecce38fa8ed06d00b04504fc001344014224540bccd8c8308950ad190000c782e05b8efcae8000000f4d020da07f120424c00000003886c4107011948291c0f042982ecc0800140d3e8dd826400065000096d0ec000a3889d1246b0000368b6046caa8c8800097d1000012c40011c80012c06fc58d029298000b50000b30001144854000378000e74608000d9465901104539923c8987348c80000000000e524ce9c7dc0acbe4aa09fc0000000610240004380000009e524471cb00644a900003dcd4cb2d0589bc3c85e4b943290bc8b13486c02d095d4102e92f86bc000aa50b10d8000000f00000c1c790ea8f9cc6cbd015ceac2212080e80002901b4000ad80010f4000684a991c400117c00098430d09851091d2a4c7010c0011b893d39cd7c0000004884d05a80006dc00000078c520000cf0000fe81f098cba40007880001ccea00000007c80006780007780009141288784640001b81612400a0ac80009b0bc80012a8250ff0904544ed52508d8e090a4000000991090111248a440813c0dd028088908051c4ec3a82c49187c46748041940941d1094fa05244f4f6c5cd0c8dcc0002fc94c604d040bce90e2d231311198428930538288000b9931c0189f0fbc5507801e8184a8129d3ec02c648630da8e4090c00005c590a08eb503c4b400060c000001140ee8000ba08103ac198000c903cd35820872508801c5c40011ac3400005780008d45f8618a6d2bc0011d4ad0000e14ec0bd8f10000e5818800000044c8b8000d640012ed2e92ac000e70314284000b20b9ccb4000928cc8000b14db80110480003c0000e613fc0004c81d4000fc0065130bd4aac7680d0f782313f03a022c2d46543d86906e86613acce00007a46d52fc6388f448c098c6836c7fd2f0131110d90d389a4f24f8d2a08848144443fc49907087136c4aceb0ffd320c28bb8614c2040ccdd3c8000ccc074000821180dac00054d0a8000c345bc00123868d20ceec73ccc4a70cec7b
  | 8 => 0xf200000013889a0e9400000008c0008a928c000000b1c9dc49c00127c528b4cb780007a11e4000710a607142400008e000000051851467ca693140000000000002780004051cc000000f54c150e8000ee0394b8475876493502cb5c81c4180b4754f3c634cbc8e8201000b6c0440582f51a4204de8c40a100000008404405d5030b54deca78348760c8c69d35112d06538c5611607386412dcc543b0e288f0f0825c2b45fc6c800000125ce98000c0c5a062506c838380e8cd410e0584ba8d18384c60398b34fe125400074cd5400000057411416c864001290bc079c21d2802ac680ca0860000000000e104e80003303500000000010080004f13a93d8000d840e0f5829c664f84ca93a0695271118d24fac63c75c6f00000005984b0cd03e8af00000002b000000101813521ccc0d08bb04548ecae4ea400000137c2e400041c00088cdb4000a0c4a4001068c98f34fb4001214000b400a42bcc84670000334c5c0010f0a30ab11f8568000000e453f41c4354b80ef8000000c040247b0c4c2a4a4c0003f87d85f4b8d340a34138acc048cb8d146012603e10140000012e053d2b5138001258d98415404d58ab8e5cdf864ca893f80004a8dc4e30570bf40002687a91bd35ce689d92d9078e492c8620808a581c89c92ccfb00c8f1cdfcaf8364054bac9593280288ccb707188c10d456c9c003ce7d0b50383601752b910d150164e6c3ec005364b6838cfb89a8020ec872c8ac9410f828c5a52188fcd509981190500c052c2292e42144bc5e0a511783c53d04cc4d883d2b0e7814ca14bfd1e0770484078aeca9c12450c3f513cac0db01785301546b89b4f7d14ce640892686b5408e886988dcf5c260589134994d1d1703753bcc486c4b6515c858b2532cf142dc0003f13cc474fdc325220
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe4358c10046dc4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c100067f5258c100067d5258c10006bf4258c10006bd4258c10046df3258c10006de3258c10006dd3258c10046dc3258c1002cff7158c1002cfe7158c1002cfd7158c1002cfc7158c1002ede3158c1002edc3158c10034ff7058c10034fe7058c10034fd7058c10034fc7058c10036de3058c10036dc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c100065f5258c10006de5258c10006dd5258c100065d5258c10006dc5258c10006df4258c100069f4258c10006de4258c10006dd4258c100069d4258c10006dc4258c1002edf7158c1002ede7158c1002edd7158c1002edc7158c1002edf5158c1002ede5158c1002edd5158c1002edc5158c1002edf4158c1002ede4158c1002edd4158c1002edc4158c1002edf2158c1002ede2158c1002edd2158c1002edc2158c10036df7058c10036de7058c10036dd7058c10036dc7058c10036df5058c10036de5058c10036dd5058c10036dc5058c10036df4058c10036de4058c10036dd4058c10036dc4058c10036df2058c10036de2058c10036dd2058c10036dc2058c10036df1058c10036de1058c10036dd1058c10036dc1058c10004ff7650c10034fe7650c10004fd7650c10034fc7650c100057f7550c100557c7550c101867e6550c100067d6550c1001ebe6450c10006bd6450c10016de6350c10006dd6350c1017eee6250c10006ef7558810006ee75588100066e7558810006ed75588100066d7558810006ec7558810006ef7458810006ee7458810006ae7458810006ed7458810006ad7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881002eef715881002eee715881002eed715881002eec715881002eef515881002eee515881002eed515881002eec515881002eef415881002eee415881002eed415881002eec415881002eef315881002eee315881002eed315881002eec3158810036ef7058810036ee7058810036ed7058810036ec7058810036ef5058810036ee5058810036ed5058810036ec5058810036ef4058810036ee4058810036ed4058810036ec4058810036ef3058810036ee3058810036ed3058810036ec3058810036ef1058810036e71058810036ee1058810036ea1058810036ed1058810036e5105881002ee91058810036ec1058810
  | 1 => 0x94100067e72594100067d72594100047d72594100067c72594100067f42594100063f42594100067e42594100067d42594100063d42594100067c42594100067f32594100067e32594100067d32594100067c325941002e7f715941002e7e715941002e7d715941002e7c715941002e7f415941002e7e415941002e7d415941002e7c415941002e7f315941002e7e315941002e7d315941002e7c315941002e7f215941002e7e215941002e7d215941002e7c21594100367f70594100367e70594100367d70594100367c70594100367f40594100367e40594100367d40594100367c40594100367f30594100367e30594100367d30594100367c30594100367f20594100367e20594100367d20594100367c20594100367f10594100367e10594100367d10594100367c1059410004ff7559010024fe7559010004fd7559010024fc7559010034ff7459010036bf7459010006bf545901004ebe5459010006bd545901004ebc5459010004ff7359010014fe7359010014fc735901004ebf4359010006be435901004ebc4359010004ff725901000cfe7259010004fd725901000cfc72590100067f52590100067d525901004ebf4259010006be4259010006bd425901004ebc425901002cff715901002cfe715901002cfd715901002cfc715901002ebe415901002ebc4159010034ff7059010034fe7059010034fd7059010034fc7059010036be4059010036bc4059010036f71059010036f51059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010004bf7259010006be7259010006bd7259010004bd7259010006bc7259010006bf52590100063f5259010006be5259010006bd52590100063d5259010006bc5259010006bf3259010006be3259010006bd3259010006bc325901002ebf715901002ebe715901002ebd715901002ebc715901002ebf515901002ebe515901002ebd515901002ebc515901002ebf315901002ebe315901002ebd315901002ebc315901002ebf215901002ebe215901002ebd215901002ebc2159010036bf7059010036be7059010036bd7059010036bc7059010036bf5059010036be5059010036bd5059010036bc5059010036bf3059010036be3059010036bd3059010036bc3059010036bf2059010036be2059010036bd2059010036bc2059010036bf1059010036b71059010036be1059010036bd1059010036b51059010036bc1059010004ff7558c10024fe7558c10004fd7558c10024fc7558c10004ff7458c1001cfe7458c1001cfc7458c10034ff7358c10036df7358c10006df5358c10046de5358c10006dd5358c10046dc5358c10006df4358c10046d
  | 2 => 0x757c7558d100067f6558d100067c6558d10005bf7458d1006dbc7458d10006bf6458d10006bc6458d10066dc6358d10005ef7258d1005dec7258d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d1001cfc7458d10006bc7458d1001cbc7458d10064ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d100067f5258d100067d5258d10006bf4258d10006bd4258d10066df3258d10006dd3258d10084ff7158d10006f77158d10006f62158d10006f52158d100a4ff7058d10006fb7058d10006fa2058d10006f92058d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100757c7550d100067f6550d101867c6550d10006bf6450d1001ebc6450d10005f6769051002ef6769051002f76759051002f7575905100077765905101bf74659051006df57490510007b7649051001ef6649051001ef4649051006fb4649051001eb4649051002fd6739051002fd5739051002df772905101b5f572905101a77752905101a775529051006fb742905101a7b54290510035f67090510035f4709051002ef7609051002ff360905101afb640905101afb440905101a7f220905101a7f12090510034fc76505100067f655051015e7c6550510006bf645051001ebc645051002fb44150510005fb7050510035f87050510035f4765051001ef47650510034f4765051000777655051019f74655051002df7745051002fb77450510007b7645051001ef6645051001ef4645051006fb46450510195f77250510195f5725051018f77525051018f75525051006fb7425051018fb54250510007f37050510035f67050510035f47050510007f07050510035f0705051002ef7605051002ff3605051006fb7405051018ff2205051018ff12050510034fc764c5100057f754c5100757c754c5100067f654c51012e7c654c510006bf644c510126bc644c510006df634c510016dc634c510005fb704c510035f8704c51002ff0104c51001cff765011006cfd765011002cfc76501100057f75501100757c75501100067f65501100fe7c6550110006bf645011001ebc6450110005f7715011002df47150110007b54150110014ff764c110064fd764c11002cfc764c1100067f654c1100ce7c654c110006bf644c1100c6bc644c110006df634c110016dc634c110005f7714c11002df4714c110037f0104c1100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067c43594100067f72594100047f725
  | 3 => 0xc62d91100073f52d91100073d52d91101afb771d9110007b621d9110007b521d9110007ba20d9110007b920d91101d7bb10d91101afb610d91101afb410d91101d7b810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110004bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d91100063f52d9110006be52d9110006bd52d91100063d52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d91101aebf71d91101d6be71d9110006bd71d91101d6bc71d9110006bf51d91101d6be51d9110006bd51d91101d6bc51d9110006bf31d91101d6be31d91101d6bc31d9110006bf21d91101d6be21d9110006bd21d91101d6bc21d91101d6bf70d91101aebe70d9110006bd70d91101aebc70d9110006bf50d91101aebe50d9110006bd50d91101aebc50d9110006bf30d91101aebe30d91101aebc30d9110006bf20d91101aebe20d9110006bd20d91101aebc20d91101d6bf10d91101aebe10d91101aebc10d91100057f75591100757c75591100067f65591100067c655911006ebc6459110004ff75591100067f75591100047f7559110024fe7559110004fd7559110024fc75591100067c75591100247c755911006cff7459110006bf7459110004ff7359110014fe7359110014fc7359110004ff725911000cfe7259110004fd725911000cfc72591100067f52591100067d525911006ebf4259110006bd425911008cff7159110006f771591100acff7059110006fb7059110005be761911006ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6319110006bc631911006dbf7219110005bd7219110006bf6219110006be6219110006bd6219110006bc62191100073f52191100073d521911006fb571191101cebf6119110007b62119110007b521191101c6bf6019110007ba2019110007b920191101c7bb10191101cfb610191101cfb410191101c7b81019110014fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10066de63d8d10004ff75d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d100067f52d8d100067d52d8d10006bf42d8d10006bd42d8d10006de32d8d10066dc32d8d1002cfe71d8d10034fd71d8d1002cfc71d8d10066df31d8d10006f621d8d10006f521d8d10034fe70d8d1002cfd70d8d10034fc70d8d10066df30d8d10006fa20d8d10006f920d8d100057f7558d10
  | 4 => 0x8e100067f5258e100067d5258e10006bf4258e10006bd4258e10086df3258e10006dd3258e10086df3158e10034fc7058e10036de3058e10036dc3058e10036fa2058e10006f92058e10004ff7650e10034fe7650e10004fd7650e10034fc7650e100057f7550e100957c7550e10016de6350e10006dd6350e1001cff7650610034fc765061001ebe6450610006bd6450610005fb7050610035f87050610014ff764c610034fc764c6100057f754c6100957c754c610016de634c610006dd634c61002fd4314c610005fb704c610035f8704c6100757e76d95100767e76d95100247e76d95100067e64d95100067c64d95100067e63d95100067c63d95100057f72d95100057d72d95100067f62d95100067e62d95100067d62d95100067c62d95100073f42d95100073d42d95100077621d95100077521d95100077a20d95100077920d95101e77b10d95101df7610d95101df7410d95101e77810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067c43d95100067f72d95100047f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f42d95100063f42d95100067e42d95100067d42d95100063d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95101de7f71d95101e67e71d95100767d71d95101e67c71d95100067f41d95101e67e41d95101e67c41d95100067f31d95101e67e31d95101e67c31d95100067f21d95101e67e21d95100067d21d95101e67c21d95101e67f70d95101de7e70d95100767d70d95101de7c70d95100067f40d95101de7e40d95101de7c40d95100067f30d95101de7e30d95101de7c30d95100067f20d95101de7e20d95100067d20d95101de7c20d95101e67f10d95101de7e10d95100767d10d95101de7c10d951001cfe76d91100067f65d91100067c65d911006ebe64d9110004ff75d9110024fe75d9110004fd75d9110024fc75d9110006bf54d911006ebe54d9110006bd54d911006ebc54d9110014fe73d9110004fd73d9110014fc73d911006ebf43d9110006be43d911006ebc43d9110004ff72d911000cfe72d9110004fd72d911000cfc72d91100067f52d91100067d52d911006ebf42d9110006be42d9110006bd42d911006ebc42d911002cfe71d9110034fd71d911002cfc71d911006ebf41d9110034fe70d911002cfd70d9110034fc70d911006ebf40d911006dbe76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110005bf72d9110005bd72d9110006bf62d9110006be62d9110006bd62d9110006b
  | 5 => 0x20edd654c530005df744c530005dd744c530126de644c530126dc644c530205df724c530205dd724c5301fedf624c5301fedd624c5301ff5f524c5301ff5d524c5301ff9f424c5301ff9d424c530015df714c530017d7714c530007d7614c53002ede614c53002edc614c530007d4614c53002ed4614c5301ffd6214c5301ffd5214c530007db704c530035de704c530035dc704c530007d8704c530016df604c530017db604c5301ffda204c5301ffd9204c53001cff7650130014fe76501300f4fd7650130014fc76501300057f75501300cd7c7550130006bf645013001ebc6450130005df7350130015dc7350130037b84050130004ff7559310024fe7559310004fd7559310024fc755931002ebf7459310004ff7359310014fe7359310014fc7359310004ff725931000cfe7259310004fd725931000cfc72593100067f52593100067d52593100aebf4259310006bd4259310034fc715931002ebe415931002ebc41593100aebf4059310004ff7558f100067f7558f100047f7558f10024fe7558f10004fd7558f10024fc7558f100067c7558f100247c7558f10004ff7458f1001cfe7458f1001cfc7458f1002edf7358f100a6de5358f10006dd5358f10006df4358f100a6dc4358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f100067f5258f100067d5258f10006bf4258f10006bd4258f100a6df3258f10006dd3258f10034fc7158f1002ede3158f1002edc3158f1002ef62158f10006f52158f100a6df3058f10004ff7650f1002cfe7650f10004fd7650f1002cfc7650f100057f7550f100b57c7550f1002df7765071004ef7765071002fb7745071002fb7645071001ef6645071002ef4645071002fb464507101f5f772507101f5f572507101ef7752507101ef7552507100afb742507101efb54250710035f67050710035f470507100afb7405071001cff765031002cfc76503100057f75503100b57c755031001ebe6450310006bd6450310005f7715031002df47150310007b54150310014ff764c31002cfc764c310016de634c310006dd634c310005f7714c31002df4714c310004ff75592100067f75592100047f7559210024fe7559210004fd7559210024fc75592100067c75592100247c7559210036bf7459210004ff7359210014fe7359210014fc7359210004ff725921000cfe7259210004fd725921000cfc72592100067f52592100067d525921008ebf4259210006bd425921008ebf4159210034fc7059210036be4059210036bc4059210036f71059210036f51059210004ff7558e10024fe7558e10004fd7558e10024fc7558e10004ff7458e1001cfe7458e1001cfc7458e10036df7358e10006df5358e10086dc5358e10086de4358e10004ff7258e1000cfe7258e10004fd7258e1000cfc725
  | 6 => 0x52158630034ff7058630034fd7058630034fc7058630036df3058630036dd3058630036fa2058630006f92058630036f61058630036f4105863002cff7690630034fe7690630004fd76906300e57e75906300057d75906301767e65906300067d6590630015de7390630005dd739063002ef66190630006f56190630004ff7650630004fd7650630034fc765063015e7e65506300067d655063001ebe6450630006bd645063002ef66150630006f5615063001cfe76d91300c6be64d9130004ff75d9130024fe75d9130004fd75d9130024fc75d9130006bf54d91300c6bc54d9130034ff73d9130014fe73d9130034fd73d9130014fc73d913010ebf43d913010ebd43d9130004ff72d913000cfe72d9130004fd72d913000cfc72d91300067f52d91300067d52d91300c6bf42d9130006bd42d913002cfe71d9130004fd71d91300c6bc41d9130014fd70d91300c6bf40d91300057f75591300cd7c75591300c6bc645913022dfb7059130004ff75591300067f75591300047f7559130024fe7559130004fd7559130024fc75591300067c75591300247c755913010cff7459130006bf74591300f4ff7359130006df7359130004ff725913000cfe7259130004fd725913000cfc72591300067f52591300067d52591300c6bf4259130006bd4259130004ff715913002cfc715913022cff7059130006fb7059130035dc7650d3001edc7650d30034dc7650d300075f7550d300cdde7550d300cddc7550d302275c7550d300cd5c7550d30015df7450d300179f7450d300079f6450d3001ede6450d3001edc6450d300c79c6450d3021ddf7250d3021ddd7250d302175f5250d302175d5250d300c79f4250d302179d4250d30005df7150d30007db7050d30035de7050d30035dc7050d30007d87050d30016df6050d30017db6050d30217da2050d30217d92050d30004ff75d8530024fe75d8530004fd75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d8530034fd73d8530004ff72d853000cfe72d8530004fd72d853000cfc72d85300067f52d85300067d52d8530006bf42d8530006bd42d8530086df32d8530006dd32d8530086f631d8530086f531d8530034fe70d8530034fc70d8530006fa20d8530006f920d8530006f76198530065f970985300057f75585300cd7c7558530005bf74585300c5bc7458530005ef72585300bdec72585300a5fb70585300cd7e75185300057d751853002ef66118530006f56118530004fe7690530004fd769053002cfc76905300cd7e75905300057d7590530006bf649053001ebc6490530015de7390530005dd7390530004ff7650530004fe7650530004fc7650530015de7350530034dc764c5300075f754c5300cdde754c5300cddc754c53020f5c754c5300cd5c754c53020edf654c530
  | 7 => 0x8540006bd42d854008ef641d854008ef541d8540006f721d8540006f421d85400fd7e75985400057d75985400067f65985400067c65985401aebf64985400f5de7398540005dd7398540006f7619854006df970985400057f75585400fd7c75585400067f65585400067c65585400adfb70585400067f65185400067c65185401cebf641854002ef66118540006f56118540034bc76505400073f655054024f3c6550540245bf7250540245bd725054023ebf625054023ebd625054023f3f525054023f3d525054001dbf715054001fb77150540007b7615054002ebe615054002ebc6150540007b46150540007bb7050540035be7050540035bc7050540007b8705054001ebf605054001fbb6050540004fe768c540004fd768c54002cfc768c5400067f658c5401467c658c54001dbe748c540005bd748c540006f7618c54002ef4618c540004ff764c540004fe764c540004fc764c5400057f754c5400fd7c754c5400067f654c54012e7c654c540006df634c540016dc634c540006f7614c54002ef4614c5400067f74596300067e74596300067d74596300067c74596302367f73596302367e73596302367d73596302367c73596302367f43596302367e43596302367d43596302367c43596300067f72596300047f72596300067e72596300067d72596300047d72596300067c72596300067f42596300063f42596300067e42596300067d42596300063d42596300067c42596302367f32596302367e32596302367d32596302367c32596300067f71596300067e71596300067d71596300067c71596300067f41596300067c41596302367f31596302367e31596302367d31596302367c31596300067f21596300067e21596300067d21596300067c21596300367f70596300367e70596300367d70596300367c70596300367f40596300367e40596300367d40596300367c40596300367f30596300367e30596300367d30596300367c30596300367f20596300367e20596300367d20596300367c20596300367f10596300367e10596300367d10596300367c1059630004ff7559230024fe7559230004fd7559230024fc7559230036bf74592300f6bf43592300f6bd4359230004ff725923000cfe7259230004fd725923000cfc72592300067f52592300067d52592300debf4259230006bd4259230004ff715923002cfc71592300debf4159230034fe7059230034fc7059230036be4059230036bc4059230036df3059230036dd3059230004ff7558630024fe7558630004fd7558630024fc7558630004ff745863001cfe745863001cfc7458630004ff725863000cfe7258630004fd725863000cfc72586300067f52586300067d5258630006bf4258630006bd4258630036f77158630066f63158630066f53158630006f62158630006f
  | 8 => 0x6ef6415864006ef541586401d6bc4158640006f62158640006f52158640034fc7058640036bf4058640036bd4058640036f61058640036f410586401d73e75906401d73d75906401d79e73906401d79d73906401d5bf729064027dbd72906401aebf6290640276bd62906402773f52906402773d529064001dbe719064001fb671906401aebf61906401afb661906401d6bd61906401afb561906401afba70906401adbd70906401d7b9709064001ebe609064001fba60906401afb7109064002cff768c640034fe768c640004fd768c640004ff764c640004fd764c640034fc764c6400057f754c6401157c754c640005bf744c64001dbc744c640016de634c640006dd634c64026d7e76d95400fe7e76d95400247e76d95400067e63d95400067c63d95400057f72d95400057d72d95400067f62d95400067e62d95400067d62d95400067c62d95402673f42d95400073d42d95402673f41d95402677b40d954025f3e40d954025f3c40d95402677840d954025e7f74d95402667e74d95402667d74d95402667c74d95400067f73d95400067e73d95400067d73d95400067c73d95402667f43d95402667e43d95402667d43d95402667c43d95400067f72d95400047f72d95400067e72d95400067d72d95400047d72d95400067c72d95402667f42d95402663f42d95402667e42d95402667d42d95400063d42d95402667c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95402667f41d95402667e41d95402667d41d95402667c41d95400067f31d95400067c31d95400067f21d95400067e21d95400067d21d95400067c21d95402667f70d954025e7e70d95402667d70d954025e7c70d95402667f40d954025e7e40d95402667d40d954025e7c40d95400067f30d954025e7e30d954025e7c30d95400067f20d954025e7e20d95400067d20d954025e7c20d954025e7e10d954025e7c10d9540014fe76d8d400067f65d8d400067c65d8d400f6de63d8d40004ff75d8d40024fe75d8d40004fd75d8d40024fc75d8d40034fd74d8d40014fc74d8d400f6de43d8d400dedd43d8d40004ff72d8d4000cfe72d8d40004fd72d8d4000cfc72d8d400067f52d8d400067d52d8d400debf42d8d40006bd42d8d40006de32d8d400f6dc32d8d4002cfe71d8d40004fd71d8d400f6df31d8d4001cfd70d8d400f6df30d8d400057f7558d400fd7c7558d400067f6558d400067c6558d400f6dc6358d40255fb7058d400067f65d85400067c65d8540004ff75d8540024fe75d8540004fd75d8540024fc75d8540034fd74d8540014fe73d8540004fd73d8540014fc73d8540004ff72d854000cfe72d8540004fd72d854000cfc72d85400067f52d85400067d52d854008ebf42d
  | 9 => 0xc30d95310067f20d95310067e20d95310067d20d95310067c20d953128e7f10d953128e7c10d953101cfe76d91310067f65d91310067c65d9131126be64d9131015de73d913102ddd73d91311279f43d9131004ff75d9131024fe75d9131004fd75d9131024fc75d913102cff73d913102cfd73d9131126dd73d913102cdd73d913116ebf43d9131126df43d913116ebd43d913116edc43d9131004ff72d913100cfe72d9131004fd72d913100cfc72d91310067f52d91310067d52d9131126bf42d9131006bd42d9131014fd71d9131126bf41d9131034fe70d9131004fd70d9131126bc40d913116edf30d91310057f755913112d7c75591310067f65591310067c6559131126bc6459131285f77159131004ff75591310067f75591310047f7559131024fe7559131004fd7559131024fc75591310067c75591310247c755913116cff7459131006bf7459131154ff7359131006df7359131126df4359131156dc4359131004ff725913100cfe7259131004fd725913100cfc72591310067f52591310067d5259131126bf4259131006bd4259131284ff7159131006f77159131004ff7059131034fc7059131156df305913101cff7650531014fe7650531154fd7650531014fc76505310067f655053115e7c6550531006bf645053101ebc6450531005df7350531015dc735053102fb4415053102fd431505310067f65d81310067c65d8131004ff75d8131024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d813102cfd73d8131004ff72d813100cfe72d8131004fd72d813100cfc72d81310067f52d81310067d52d8131006bf42d8131006bd42d81310a6df32d8131006dd32d8131006f621d8131006f521d81310a6fa30d813112d7e75981310057d75981310067f65981310067c6598131006fb60981310057f755813112d7c75581310067f65581310067c6558131005bf7458131125bc7458131005ef725813111dec72581310067f65181310067c6518131036fa6018131006f96018131004ff7558e40024fe7558e40004fd7558e40024fc7558e40036df7358e40006df5358e4010edc5358e4010ede4358e400c6dd4358e40004ff7258e4000cfe7258e40004fd7258e4000cfc7258e400067f5258e400067d5258e400c6bf4258e40006bd4258e4010edf3258e40006dd3258e40004ff7158e4002cfc7158e4010edf3158e40034fe7058e40034fc7058e40036de3058e40036dc3058e40004ff75586400067f75586400047f7558640024fe7558640004fd7558640024fc75586400067c75586400247c7558640004ff7358640014fe7358640014fc7358640004ff725864000cfe7258640004fd725864000cfc72586400067f52586400067d525864006ebf4258640006bd4258640036f77158640
  | 10 => 0x8d41006bd42d8d4101cfd71d8d41156df31d8d41034fe70d8d41004fd70d8d410057f7558d4115d7c7558d41156dc6358d412a5f77158d41004ff75d8141024fe75d8141004fd75d8141024fc75d814102cfd74d8141014fe73d8141004fd73d8141014fc73d8141004ff72d814100cfe72d8141004fd72d814100cfc72d81410067f52d81410067d52d81410aebf42d8141006bd42d81410aefa40d8141006fb60981410057f755814115d7c755814115d7e75181410057d75181411aebf6418141155de7318141005dd731814114dee7218141005ed7218141036fa6018141006f96018141004ff7559231024fe7559231004fd7559231024fc755923102ebf7459231006bf545923113ebc5459231156bf4359231156bd4359231004ff725923100cfe7259231004fd725923100cfc72592310067f52592310067d525923113ebf4259231006bd425923102cfe715923102cfc715923102ebe415923102ebc4159231004ff7059231034fc705923113ebf4059231004ff75582310067f75582310047f7558231024fe7558231004fd7558231024fc75582310067c75582310247c7558231004ff745823101cfe745823101cfc7458231004ff725823100cfe7258231004fd725823100cfc72582310067f52582310067d5258231006bf4258231006bd425823102cfc715823102edf315823102edd315823102ef62158231006f5215823102efb7058231066fa3058231006fa2058231006f9205823102efb105823102ef8105823129d7e76d953112e7e76d95310247e76d95310067e64d95310067c64d953128f5f73d95312975c73d95310075f43d95312975c43d95310057f72d95310057d72d95310067f62d95310067e62d95310067d62d95310067c62d95310073f42d95310073d42d95312975f32d95310075d32d95312977731d953128f5e31d953128f5c31d95312977431d95310077621d95310077521d95312975f30d95310067f74d95310067e74d95310067d74d95310067c74d953128e7f73d95312967e73d95312967d73d95312967c73d95312967f43d95312967e43d95312967d43d95312967c43d95310067f72d95310047f72d95310067e72d95310067d72d95310047d72d95310067c72d95310067f42d95310063f42d95310067e42d95310067d42d95310063d42d95310067c42d95312967f32d95312967e32d95312967d32d95312967c32d95312967f71d953128e7e71d95312967d71d953128e7c71d95310067f41d953128e7e41d953128e7c41d95312967f31d953128e7e31d95312967d31d953128e7c31d95310067f21d953128e7e21d95310067d21d953128e7c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067c40d95312967f30d95312967e30d95312967d30d95312967
  | 11 => 0x67e32596410067d32596410067c325964102e7f715964102e7e715964102e7d715964102e7c715964102e7f415964102e7e415964102e7d415964102e7c415964102e7f315964102e7e315964102e7d315964102e7c315964102e7f215964102e7e215964102e7d215964102e7c21596410067f70596410067e70596410067d70596410067c70596412ae7f40596412ae7e40596412ae7d40596412ae7c40596410067f30596410067c30596410067f20596410067e20596410067d20596410067c205964102e7f105964102e7e105964102e7d105964102e7c1059641004ff7558e41024fe7558e41004fd7558e41024fc7558e4102edf7358e41006df5358e4116ede5358e41006dd5358e4116edc5358e4116ede4358e41126dd4358e41004ff7258e4100cfe7258e41004fd7258e4100cfc7258e410067f5258e410067d5258e41126bf4258e41006bd4258e4116edf3258e41006de3258e41006dd3258e4116edc3258e4102cfe7158e4102cfc7158e4102ede3158e4102edc3158e41004ff7058e41034fc7058e4116edf3058e4116edc3058e41006df7558e41006de7558e41006dd7558e41006dc7558e41126de7458e41126dd7458e4116edc7458e41126df5458e41126de5458e41126dd5458e41126dc5458e41006df7258e41006de7258e41006dd7258e41006dc7258e41006df5258e410065f5258e41006de5258e41006dd5258e410065d5258e41006dc5258e41126df4258e411269f4258e41126de4258e41126dd4258e410069d4258e41126dc4258e4102edf7158e4102ede7158e4102edc7158e4102edf5158e4102ede5158e4102edd5158e4102edc5158e4102edf4158e4102ede4158e4102edd4158e4102edc4158e4102edf2158e4102ede2158e4102edd2158e4102edc2158e41006df7058e41006de7058e41006dd7058e41006dc7058e41006df5058e41006de5058e41006dd5058e41006dc5058e41126df4058e41126de4058e41126dd4058e41126dc4058e41006df2058e41006de2058e41006dd2058e41006dc2058e4102edf1058e4102ede1058e4102edd1058e4102edc1058e41004ff7558241024fe7558241004fd7558241024fc7558241004ff7358241014fe7358241014fc7358241004ff725824100cfe7258241004fd725824100cfc72582410067f52582410067d525824106ebf4258241006bd425824102cfc715824102ebf415824102ebd415824102efb705824106efa40582411aebc4058241006fa2058241006f9205824102efb105824102ef81058241014fe76d8d41156de63d8d41004ff75d8d41024fe75d8d41004fd75d8d41024fc75d8d4102cfd74d8d41156de43d8d4113edd43d8d41004ff72d8d4100cfe72d8d41004fd72d8d4100cfc72d8d410067f52d8d410067d52d8d4113ebf42d
  | 12 => 0xe76d95430247e76d95432bf5f43d95432b73e43d95432b73c43d95432b75c43d95430057f72d95430057d72d95430067f62d95430067e62d95430067d62d95430067c62d95432bf3f42d95430073d42d95432b75f30d95432b67f74d95432be7e74d95432b67d74d95432b67c74d95432b67f73d95432b67e73d95432b67d73d95432b67c73d95432b67f43d95432b67e43d95432b67d43d95432b67c43d95430067f72d95430047f72d95430067e72d95430067d72d95430047d72d95430067c72d95432be7f42d95432be3f42d95432be7e42d95432be7d42d95430063d42d95432be7c42d95432b67f32d95432b67e32d95432b67d32d95432b67c32d95430067f71d95430067e71d95430067d71d95430067c71d95432be7f41d95432be7e41d95432be7d41d95432be7c41d95432b67f31d95432b67e31d95432b67d31d95432b67c31d95430067f21d95430067e21d95430067d21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95432be7f40d95432be7e40d95432be7d40d95432be7c40d95432b67f30d95432b67e30d95432b67d30d95432b67c30d95430067f20d95430067e20d95430067d20d95430067c20d954302cfe76d85430067f65d85430067c65d8543004ff75d8543024fe75d8543004fd75d8543024fc75d8543014fd74d854301cfd73d85432a6df43d8543286dc43d8543004ff72d854300cfe72d8543004fd72d854300cfc72d85430067f52d85430067d52d85432a6bf42d8543006bd42d85432a6f641d8543286f631d8543034fe70d8543004fd70d8543286df30d85431857e75985430057d75985430067f65985430067c6598543006f761985430057f75585431857c75585430067f65585430067c65585430067f65185430067c651854302ef66118543006f56118543034fe76d81430067f65d81430067c65d8143004ff75d8143024fe75d8143004fd75d8143024fc75d8143014fd74d814301cfd73d8143004ff72d814300cfe72d8143004fd72d814300cfc72d81430067f52d81430067d52d8143256bf42d8143006bd42d814302cfe71d8143004fd71d8143256fa40d814322efa30d81431857e75981430057d75981430067f65981430067c6598143006fb60981430057f75581431857c75581430067f65581430067c65581430067f65181430067c6518143036fa6018143006f960181432ae7f74596412ae7e74596412ae7d74596412ae7c74596410067f73596410067e73596410067d73596410067c73596412ae7f43596412ae7e43596412ae7d43596412ae7c43596410067f72596410047f72596410067e72596410067d72596410047d72596410067c72596412ae7f42596412ae3f42596412ae7e42596412ae7d42596410063d42596412ae7c42596410067f3259641
  | 13 => 0x400000000000200001200900900100000000300400900000300700300000500500101300300200d00000301102000000000000201f00b00000002b01700900300b00300000200705000800001c00600d00100500100a02500100300401000100b00100300000200000f00100400800100000302000000000000500100000700003e06600500300103200000600200c02600301301400001e00000202e04800a00000200600301400103900001e00000400904701700000e00100000100001200600000200000300a00800600900000001e00400000100e00c03000100e00500900000204b00000500100f01003e00400001d00500000600001800200d00000300d04c00100100900c00b00000200800b00b00100d00200f00700600000400400300600b00000200100100000300400000003e00200300000303600100100400300703400200000000500000c00200000000c06500000000000500100200f00400600200300a00401500d00100e00300200100600200500000700802900a00001600800000100400000100000000000700900b00100600000300300700000d00000105000000100300900000700000700000400100002d00100000200b00400200000d04200601000400a00200001103c00100305d00000000000000100e00000e00300400100100300000301100100200000800200a00100400201b01500200400d00000000001500000000600300000000000600700502101201400800104100800400805b03000000000000101c07100700700000b00700a00301104000700000c00600000105e01200e00100400600000700000004600900900001800000100f01700000101000000000000000203b00000800d00200800100300400201a00500d00101b00000700000000a00000101400300600901a00000000000207c00000600103400200300300300000000400000000301100100302f00300400002a00500004e00600000f00c00700400101f00000000600602100d02800003300200f01300600000f00e00000f01400004800800600b00000300203a0040010050030000020130000ad00200f02100300400000d00407700800503d02100800000e00500200000000000d01400300400300003400a00000b00300500701300100000302002700907700000000500800702b00200c00005001e00600200f00c00200100100000100500200201600100300c00000101200203d00001002d00000d00000c00302a00301e02d00000100400400900100e00600000300000c01901300200300a00000000100800900000002e01200500000000301800200402700005b00000100100000501200302b00c02200a00702000500001a00001300700100300100c00100000a00500102800200c00e0050030000000030132c57e76d95431867
  | 14 => 0x1c30250000d008041e7875c48000023b1de0e8a5da000011c6fc0d80001eb045e88428214a095250f3d8116c6920003331cc46b20b52fd99f000000020810c443a00006a0a488be0000001d78d348773b60b9800030f08405942ba89809d11502506442f312ecd1c32400000cc6384ee0cc994821a0000b21c04da80000d799b41f26d90c299a481459b1dd22a0156000000161871a64711989544da62f14092a83e80002c51e4cc061d41cf1f4c58a2103c604b886a65b42f195890c1ad166926004e0151db800029e6b94410d34d2a6340000000be46140d221610f64d30b594e04526710c3226c7801be29011691122c91ca818452a2681e180009622580000000fde4900298fdc00020f40f87900f831b000132c6465ae13896c08d23112c783486ce25f005937c7e029022e9e1018019e0f9a25c5086053fd0a6400027f04080001163814070b0c41a0003ac8d0c33843f274a21885a00041c19d4e7a0201a00c3497c47d3f91358e660000000148fd677b34b8ef472c0e50329064dd45d20e480000002723ae1d9c0000c62a905309c82be27d81c00000000001fa44844e81660000d6e0001998000504577395121cd4e40432c88485825dc16990440008780000b510960000000d8411c6331fd009094845106b8c746de5ab36680004ac0000f6093c00001644a1c4cfa217c4468000f700000000a300007ae4318000ce82bf0001cec73600000008fc0b444f31d9f680006ad36598a064a0003da00010f410116f9c9c0001fa3e7140ce7829b0001c9414615a3f022046fe0000000000b9a76328580000000003ad00e000000028a14600007f022b17290947752bc0db8d822410f5a02ce7e27510f8c1ce285300c517ac3fa4d221e91287f88682911f3c4dc3763ad851c3602941c6073c1ce41432e00005b003b03a8d687d216c11a09a82f400000000000003e805c1d3000034129791acfc842831c04c8a9e0744028000000000000000000000041a1b2113408730e04f40f656320b21f09b05a60011224e6a60e10c0a80e0a3353b7170800065400005480000b20001d1c00000000005548fe52d0e097900004733d2099c0a8204209894801e593186135c56435d00006f0ea606f00000002c21b905382344e60ba0b014902ce4ea002145845c04f20f9b7803409f39ca02000075802308b073a57c00001b1056000231872c1be78e000217431a73703d14a886e33c0fb175c8f217739686cc5e88710a0128000200037c833865e80241218acdda00000010f8be223b25a17e50cc000000000074600000a00c00001f01000204400000000900500d01500000100000000000900000000301400300901e02c02b00400500301900c06c00000c00b00300001901100000e00000400100000200100800100100000e00000000003600502e00600
  | 15 => 0x105d04423360000000f242a64098000b1637a13792e4efe30b27097500008740000000a9a09d28000000000001228a18a727f73ff0000b0a0000000ce4142000000000113a79d13104441a005c15a032497e44d1381f9491663707800000000c53b88ee41283b21e80000608616000144c00009841814f03d07bf100000014807e00008e0d241a01bd861c1fe0002b000004b669800015140005fa0000e880c6000000141c5f000000011e038a42400008f4cb003e00006c902a0002f18e5c1d415844a914c3882bd3c39ab0d6a00024a00002d20c127e80000007ca337960c76c17f2a0a194ab62322e41d44d167b90000bf08fc0000000000b8c5b842883748060000f38d18e2a2e33b581a8b443c10000bbc5a01cc0e9972c00076831d000108a00001503f07520001810fac62c00037580005f600024400011067ad0000130a880002f09e844987743540c250d40000001310a04000000181806e62d000036cab21e3000089c0004b726420a0b007b33d01fb800042f23315f43b66c03d391dc08639230b86c4a0a61328a815493811423d1d0451047400017d01ea00000a000114069f00000010b23a51a7898c3e274a00000010361fc3a201742383fd00006d000087d0ce99fcdb800037d8000f020913ce194440a5bc3a79994e925c710b908c792274000103860c8a51f002a4f8c4f841e8a8cde40933cc93944860000001f84c3429e0f100003c20000210538f4c8932f61b54c5461011b8000d662f900016b503a27e00008f00000000e8115c43c6e60000000f844f000017c098e5753148f4400017e05280000002b314712943561200598000e103d534d86e8aa2657173858c3de7170000000a9c35719e9ac09944a800011380000001da8d10e0648516d800062a56b1af9878ba26f300000006e66f817d0c0400084636e800103209700000006c4172407970c00067d1e31c74dee18b0001244b085062ac000007400000020e485400037099c80004cc28e22306620b608595b8b7a2eb3d18228f2c0000f706208720002ff80000000001e58fb4a241ca00012642a875d26021c0be632d12c9f6015e3771898d3058854c00010c87c40003c283ac2722473a41f5105e10001300000600000000000f168a7395a290a806700ca80c50da37236d94f800000021d92589b461d02495c84947c5031198c5ac27a0a20a5c7987981439148d9400030020847c800004300000000000000000b3449221484f00000000ff1eed0d221c31005ccd325b715b81804066452d200b02246963c3086800055e25393780527cc39b150d0142d113e9bd04c842c115a110a920512af8084c9850836114648005dd000016d0784bd050027050a67e1798bb8f5e2c04249bd400001900003bc7c20d1000012cd6c000163901c83053d3a19ec45d249745514ac63
  | 16 => 0x8800d38600010206ff1cd06fc29618e294800070641d37287c0ea01622129f0ca140000cf9b8c00000010a9a34c7a3ca0fd8ea8ae24f42a99d387bc3283c10610b745d524215d827c08424710300a05730001ad08827732d90c5086057e0661e280005ed041214c0003c5152800107e00033720ec4445aa0001ef000077c17e80000002f60fc8000000706124976c5b86410001f74b3a2834429ca4f747b53488a74bf000021b11ecd3812603398b87b000005a208c0365be0000ae415860c01b0fe07425341a80000a8e42e0a4891067c04d1a40af02842a80229f7098670e42d83b80dc10920281209ec0001da05400005df000146c0e47f93f69bf498427916d22ac4723881c5001c51417906b1cbc5740222d404091427fc000206035800008d8df00000e333d80003124a6416007d0b800037e1684a74702000198800049f3e0000000000037396bc2d41f70000ab049052e41317a0c4c1ae000192461c4820000c884141ce36395a909800027f971034a84205f1ac41b28561129a140000002e79d90a3c00035f0f3829a0e11f51084d206bb3509f984962a41980b8041009512814945d80de4401cc83ac2ae18195e4faa10c2068a703fe11e40921fc74813f2fb21acde238f1f711109821060ba895cecc7ec21e0f48b6a4ce04785f4d4a4803c695203ca71909a01a0c046823ab21d8b7e26902b0f08d1e23035f8f942de3f509515584362651360e649608012d61ec881622436294403a459e1ff1188fbc89c0321df80384b818907d4f2257f2849c3cd987600a08520c6c7d61b801f47ae8353fa105c4ba5951c599a102e10a2e2845902862103c877c83c02e2c60b389d84a13e3805c0003793040a682305640089e20dd80002e9869842612f236168087400000020e8cee071081a1e4a185373a9169c3da4d008f80780da4bc1b6000075a00000017f40006f6000000000000016c8f8cc0210e00013350d870a42f80f01e27ff2f00320b200c2022095057066a1031fe09de5701b188986141d80002018e4c00c0000734c084830001c700006c931920f8fb20003bb800048c2e20820380b7684f3270ef849a81c0dd8f7c4f06bc32697010c06671b0096849c07611012bc6a66bd01a1b10dae55d3a588c48121e03db979c89672041b1dd90ae2dd3700c7cd264b214c0b8455a0fd37f2190bee31a3069aa4c7c0a203f8bc908e3db37794980003bf1d880007b21e63a103ed1201c209c208819a89e0cc1b48e583892498ec084c3850000de08d481e14b0464e442013039c5825a0000000000f504ed10600010065a50b410701d04db00002306d07f50271e005a470023899e111c6ae1a7189c24434a2cc9288d44192350165068458e2f51d34f3c03f1fc9b690340253f511b5144260009043ccbc6253a004a405a00016a99cc5e200a3f
  | 17 => 0x1f99d5000050111681640006394209550c3e0002bd02f488a000163030c68e13b17513e871c216445a10c6567574370cc822615c2798c20f063f630587a8d0235804d88d40006552ab87009ea4d41468aec4505d81401c60da688f042a13882a49e0000000d4c000000183c6a46482988bf80000002b100008560802ce0ca82f615e3fb006000023a3fd8d58ebe6aa3ca8558db071f3f19160a7e71e12e12cc6e27700a991184f83ab1b51d8472866c2e61e94ef25de2888240af62c213b0db4dd251729613f87d884d2918b280cc0e93518d447ac51f20307a46a802f1d70e9cd107be3881ea42580d308818b0c3018f20919001067df3230644f7a45918282242e21700541a0c7cc52702004d8aa00fa279137412405f43f00d4f3489933082b510e1d107a06dcade0132c108d8c6a8201e6928ccf28111ee848c4163ff220102026265f28710885260090a504cc9a20f2325919d0a082e1be9e7c38c5b1429139c56c3374548ac414c80d1559c6870862235c0d980005660000d70b2443400007e0b524f90c612690a86300c000001d863f02b8000b0e7211c111c807237508d0ebc6c800e2f71db4a641a84200000b460c40a196cc0000003280b200006e81c38c84c247a20ac800019400038697bc47c0e225a938865c1901d4032c00071b2e48e7cdc80000b6868c3267f122e000000049b1800e8093a69d22aa298df40b93d59a1c7ce22a04d060c40e5f54148a3c1fc67a4391f250b4832406000106e00023e1474d14891176908000000034302c054400000000000006ab090906d12c1c717b80007f66240000000cc83f121c02a80008072b400008c019a1d995b0bac55a3b29124e165b900000ac4ee6093b500003027283b78b2c0002661088220b684e643a9e400000000769a90e740002b08d784284612ec91a0d8c12527013142a232700000010de4700ef146880434b19d0e190aa53b1c89dc89142613250a24f8888a2e8076832c3b8158057c37a26b1ba12d89d661b08a9cc056a861311903ccc07c840484908981a71901e240005e50001a24b1000500004dc00045e00009ecddc0002cc109c74c68c3ed8824f824c6000123c0000000a31f2c95a3ef36780007383c80000f4cf547e736b1cf895c41a1011da4a9450d03c11200e609639c17f84468001b285d81c80b72198d5400615b0ee9c8c9aa4641ea0eec9b887330c959cbc43290d49518a6c0bc1721bc00000000001d88000000000008cab819b1c80000ae82ff232826441c00017815b4da21d900003e028a00015384c0f2e45000017a40002911cc1d180002de00000005d03dc000000091a3da05d8000000684000033cc628880ee0e4c0000001880e0051686712880006b63193920fc878e8a306d1c48c845974188ce102c825000159436c59130a80007
  | 18 => 0x36a66b19600000001c806a80000007042371e3c20e00014f800034459f19d839855e5ce000227c8020001678000b025fc267938c0007b60c100000003263618074e121940000864000734000190c4a600038394d40007d00000b5c000000093910c0008274310000d5e1a1000000023a069154841400013518b9b38aaa4473aaa0a899253305887c909064f03b86a80003f435d1f340005213051a509564813ca1ac82560dc08b9624e5c4fc23aa0b4ca67d23eb800000063c00000f4c220000ab99d800000000005e00000000dc15080b0000057000002079b18f16581e6000000000054203224a8178b1a7fd36811bc9581973be9c44cb44f10000018b8269e0b305b80000f600400a00003bc03582783aa7e81d616d817e2f532e8b946d26df0001fcd1246e2000110867e36b3bd03dc4bc83315515a49ee33425d000068a48c0638104a964d90
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe371054964040c1c6a20a92c8080022fa1c52590100045ec38a4b20205ea3e85149640400117d0f192c8080022f61e32590100051f42c64b202000a3d858c9640400117d0e192c8080022f61c32590100051f42864b202000a3d850c9640400b56d02192c808002ad60432590100355d40064b202000ab9800c9640400d1bd0fa9ac60801a3721d5358c100346f43e86b1820068de878c963040014bd0b192c608002976163258c100054f42464b182000a9d848c9630400d1b90e992c60800297e157458c100052e42ae8b182000a5e851d163040014bb0a3a2c60800387d525458c100052f42ce4b182000a5d859c9630400153d09392c608002a76127258c100052f428e4b182000a5d851c9630400153d08392c608002a76107258c1002d6b408e4b182008ad5811c9630400d5b500392c608022b66007258c103052ec2ca4b182000a9e84949630400153b09292c60800393e095258c102f52f428a4b182000a9e84149630400153b08292c60800387d4b4258c100070ea9684b182000a5e8590963040014bb0b212c60816ea76124258c1000747c1284b182000e1f525096304001c3aa4a12c60816fa3c814258c102df4690284b182000a5e8510963040014bb0a212c608166a7a104258c100243e42eeca1820068bc84dd9430400d1b907bb286080021fe157650c100243e42aeca18200087d86dd543040af87cc9baa860815b1798f7550c1000637316eaa18200087e8759543040010f90eb2a860801a2f21d6450c100061fbaac8a182000c3c75591430400d1b90eb1a860800317dd56350c100062e3aac6a182000aae84dd5620400155b09baac4081829b61e75588102f733884eab10205ee6a109d562040bdcca213aac4081879a442755881000637c3aeab102060e67105d562040c1cd420baac4081839944175588102ff34882eab10205ea6e851d5620400155d083aac408002ab61075588100053742ee8b102000a6d85dd162040b755b0f3a2c4080038b9d6745881000716bace8b102059ea7109d162040b3d54213a2c408167a944274588102ef54884e8b10205cae7815d1620400b5c902ba2c4080032be1d7458810007173aae8b102000e2d755d16204001d4f02ba2c40816ba920574588102de57b82e8b10205bcad705d162040b7d4e20ba2c40816faa84174588102df52882e8b10205aea9105d162040014dd0a3a2c4080029b61474588102cd57420e8b102000e2f5495162040014dd0bb9ac4080029b617735881000557426e6b102000aad84dcd62040014dd0a39ac4080029b614735881000557420e6b102000aad841cd620400b5cd0239ac40801eb9604735881003575400e6b102007ae9801cd620400b5cd0321ac408002b9606435881000537c2a86b102000a6c8550d62040014dd0a21ac4080029b6144358810
  | 1 => 0x90e992c688007331c93258d1000e7239442b1a20018f48748563440039c8e490ac6880073a1ca2058d1000c7c43a40b1a2000ea9424816344001dc242902c6880121fa177650d100043ec2eeca1a200487e859d943440010fb0b3b286880021fe157650d100243e42aeca1a20008bf845d943440011df04bb286880063b2097650d100243e428eca1a20038bc841d943440010fd0dbaa868815f0f1937550d100043f43ecaa1a200087c87d95434400517d0fb2286880030fdd76450d100061e3aec8a1a2000e3464d96414400756d0db2482880032d9db64905101ae5c386c8a0a203bc7476d954144077ae0e1b2a82880d72d1db64505101aed8386c8a0a20069f287dc1414406bb66e83828288002f8608705051031c3f436ea98a2000c3c64dd531440a3ae021baa628814e1fa1f654c5101dc3e43eca98a2000c3f75d913144001878ebb22628818a1fa1b75501102661e326eaa02204d87e87d9540440790f90fb2a80880030fdd764501100061e3aec8a02203acb471d91404400d3690ea0a808801aad2194150110035d840282a0220068f686dc5304400187ee93a2ca080169da0643594100053ac0c86b28200087e8710d65040010fb0e21aca081821f61e72594100051f424e4b282000a3d849c965040018df04b92ca0817a1fa1c72594100051f420e4b282000a3d841c9650400187ee5a12ca080030f5cb42594100043f43c84b28200087d8790965040b747b09212ca080038be0942594100061fb9284b282000c3d7250965040b7c5e40a12ca0816f8b48142594100043f43884b28200087d8710965040b347d08212ca080021fa1e32594100043ec3c64b282000a3e848c9650400147b09192ca080021fa1c32594100043ec3864b282000a3e840c9650400147b08192ca080169da0432594100053ac0864b282006a7a800c965040014f300192ca0801a2fa1f54590100061fbaea8b2020068bc87551640400d17d0f21ac808016ada06435901000c5e426e4b202000caf425c9640400b1e902b92c80801a2fa1e42590100051f42c84b202000a3d85909640400d1790ea12c8080032bdc9425901002d5a40a84b202000c3f759d5640400b56d0339ac808002ad60673590100051fc2ae6b202000a3c855cd640400147d0a39ac8080028f61473590102ce5b886e4b202059cb510dc964040b717b0f392c8080028fa1672590100051ec2ce4b202000ab7815c9640400b56902b92c8080032be0972590100065bc0ae4b20205acb4815c964040b796e20b92c80816f2d44172590102cc5f438e4b202000a3e851c9640400147b0a392c8080030fdcb52590100061eb96a4b20205ee3710d4964040bdc6a21a92c8080022fa1e52590100045ec3ca4b202060a3d859496404001c5f04a92c8080030fdc952590100061eb92a4b202060
  | 2 => 0xf52591100043f43aa4b22200087c8754964440031790ea12c8880030fdd542591103261e3aa84b222000caf72509644400117b053b0c8880030f9db65191100051ec16ca3222000c3f72d946444001c6ae3b28c8880022f61e65191100051f42cca32220008bf87594644400147d0c328c8880030f9d865191100051ec10ca3222000c3f721946444001c6ce2328c8880038d5c465191100051f42cc63222000a3d8598c644400156b03318c8880030fd9572191100061e32ae432220008bf87d88644400195ae5b10c8880022f61e62191100051f42cc43222000a3d85988644400117f0eb10c8880028fe1562191100051e42ac43222000a9f83588644400153906b10c888002ade05621911001c5f438c432220008bd87188644400147d0a310c8880028f61462191100054f418c43222000a9d83188644400195ae4310c8880028fa1b52191100051e436a43222000c3e76d48644400147d0ca90c8880028f21952191100061f3b2a43222000d2d72548644400156d0d108c888003695ca21191101cd5a432423222038ab8864806444001b52e4900c888003e8485201911000754a1241b1a2000ee12148363440090fd0dbaac6880ee1f21b7558d100043f43ecab1a2000c3c74d9563440018d8e5b2ac6880021fa1c6558d100061e3a0cab1a2000c6c72195634406b1790dba2c6880030fd977458d100061e32ee8b1a20008be87d91634400187eebb22c6880030f1d76458d1000656396c8b1a20008be87191634400187eea322c6880030f1d46458d1000656390c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d1000656326e4b1a200487e87dd563440010fb05baac6880022fe117558d1001c5e422eab1a20008ef825d563440031d904baac6880021fa1c7558d1001c5f43ee8b1a2000c3f75dd16344001878ebba2c6880022f60b7458d100061fba8e8b1a2000c3c751d163440031dd0fb92c6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031be177258d100063642ee4b1a2000caf84dc9634400195909b92c6880021fe157258d100243e42ae4b1a20008bf845c9634400717908b92c68800237e0d7258d1000477438e4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440010fd0fa92c6880121f21f5258d100061fba6a4b1a2067c3c74d4963440018dee5a92c6880071b1cb5258d100043f43aa4b1a200087c87549634400187ee8a92c68819b0f1d15258d1000637b92a4b1a2001c6c72549634400117d0fa12c68800e2f21f4258d100061fbae84b1a2065c3c75d09634400195ee5a12c6880072b1cb4258d100045f43a84b1a20008bc87509634400187eeaa12c6881930f1d54258d1000657b9284b1a2001cac7250963440031b
  | 3 => 0x5b2a200087d878cb654400147d09196ca880028f61232d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95101e53b40865b2a2000a75810cb65440774f500196ca880029e60032d95101dc3f43e83b2a200087d87d0765440770fd0f90eca880021f61f21d95100051f42643b2a2000a3d84c876544079cc84290eca880f21fa1f30d95100043ec3e61b2a203c87e87c8365440010fb0f906ca880028fa1320d95100051ec2641b2a2000e2d42c836544001c5a84906ca880ef9a08120d95100146f41eebb2220008dd83dd7644400187aebaa6c8880122fe1d54d91100051f42c85b222000a3d8590b644400317f0ea16c8880032b5c942d91100051ec16cbb222000a3d82197644400147d0b31ec8880028f61663d91100061fb2ee5b222000c3c65dcb644400187ecab96c8880030f19572d911000656b96c5b222000a3e8598b644400147b0b316c8880028fe1562d91100051e42ac5b222000a9f8358b644400153906b16c8880362f61c62d91100051f428c5b222000a3d8518b644400153d06316c888002a760c62d911000656b90c5b222000a3e86d4b64440014790da96c88819f0f9db52d91100051f432a5b222000a3c8654b64440cd87ceca96c8880d6ad21921d91100075231243b22203aab8864836444001b56e4906c888003e848520d91100054f41eebb222000a9d83dd7644400187aea3aec8880028fa1773d91100051ec2ee7b222000a3e859cf644400147b0b39ec8880028fa1672d91100051ec2ce5b222000caf825cb644400147d0a396c8880028f61472d91100054f418e5b222000a9d831cb644407556d02396c8880d6ad60472d91101ad5d400e5b22203aab9801cb644400187ee5a96c8880030f5cb52d91100045f43ca5b2220008bd8794b6444001c5f04a96c8880030fdc952d91100061eb92a5b2220008be8714b644400117b0e296c8880022fa1e32d91100045ec3c65b222000a3e858cb644400147b0b196c8880022fa1c32d91100045ec3865b222000a3e850cb644400147b0a196c8880eaada0432d91100055ac0865b222035aba800cb644400157300196c8880028fe1571d91100051e42ae3b2220358be87c87644400117b0f90ec8880028fa1721d91100051ec2e43b22203aea421487644400147d0b986c8880028f61730d91101d45f43e41b2220008bd87c83644400147d0b906c8880028f61720d911000657b9641b222000caf724836444001878c9baac8880021fa1f65591100043f438cab22200487e87dd564440010fb05baac8880030fd0b75591100045fc22eab22200087e871d5644400187eebba2c8880030f1d774591100043fc2ae4b22200487c855c9644400117f08b92c88800237e0d72591100146e41ae4b2220008f7815c964440010fd0fa92c8880121f21
  | 4 => 0x34c0af8b8edbaa8698003471d76450d30006ac3aee0a1a600087f855d3614c0090f90aba6c298003aa50920d85300047bc3ac230a60058dc839da414c00187cebb2482980932719173905300243f428eca0a600087d851d9414c0a72bd0fbaa6298147171db754c53028f2a30eea98a6024c9c64dd1314c00d1b90cba2629806657215744c530034ec402e898a6005ad686d85314c001ab0ebb82629800356dd4704c5300061e3aec8a0260058bc8750964c400195ee4a12c9880121fa1f7558f100043ec16eab1e205187e871d563c400b1b90ea9ac78801637a1f4358f1002d6b40e86b1e200087f855c963c40090f90ab92c7880021fa1f5258f100243e43ea4b1e200087e8754963c40010f90ea92c7880030fdd74258f1032e1e3ae84b1e2000c3f7550963c40c9878eaa12c7880032bdc94258f1000e5639284b1e20058dc874c963c40039c8e490ac7880021fe157650f100243e42aeca1e20069b48750540c40334b90ab1a6188017351c5634c3100243f43eeab24200087d82dd5648400187e85baac90812e1fa1c75592100043fc2ae4b24200487c855c964840011bf06b92c90800a3720d72592100043f43ea4b24200487c87d4964840010fd0ea92c9080021f21d52592100345e43a84b242000c3f7550964840c9878eaa12c9080032bdc942592100045fc22eab1c20038bc845d5638400d1bd0fa9ac70800317dd75358e100346e43a64b1c2000ea94248163840010ff0abb287080121f2157650e100346e43ac6a1c2000c5c7558d43840018b8eab1a63080028fa1263d95100051ec24c7b2a200087e86dcb65440090ff0fb16ca880031b5cb62d95100043ec3cc5b2a2000a3e8498b654400147b09316ca880021fe1d62d95100051fc22c5b2a2000a3c8458b65440014bf06b16ca880029720d62d95100743ec38c5b2a2000a3e8418b654400147b08316ca8800297a0c62d95100052ec18c5b2a2000c6d7218b654400147d0da16ca881970f9db42d95100051e43285b2a2064c3e7650b65440774e90c90eca880039918921d95101e53c43241b2a2000e68624836544001e5284906ca88003d848520d95100052f41ee9b2a2000a5d83dd3654400187ae83a6ca880f29da0474d95101dd3ac08e9b2a2000c5f739cf65440010fd0e21eca880021f61c43d95100043ec3ce5b2a2000a3e849cb654400147b09396ca880031be0972d95100043f438e5b2a2000a3e841cb654400147b08396ca8800297a0c72d95100052ec18e5b2a203ca76811cb65440774eb02396ca880ee9ea0072d95101e53cc00e5b2a2000c3f72d0b654400187ae5a16ca880021fa1e42d95100043ec3c85b2a2069a3d8490b6544001c5f04a16ca880030fdc942d95100061eb9285b2a200087e8710b65440010fb0e216ca881a28fa1042d95100043f43c6
  | 5 => 0x12e8f61071d95400043f43863b2a800087d870c765500010fd0f90ecaa00021f61f21d95402651f42643b2a8000a3d84c8765500010fd0e10ecaa00021f61c21d95402651f42043b2a8000a3d8408765500014bd0610ecaa00029760c21d954025d3d40043b2a8000a798008765500990fd0f986caa00021f61f30d95402643f43e41b2a800087d87c83655009947d09906caa00028f61320d954000716a1641b2a8000e2d4248365500010fd0fb2ac6a00021fa1c6558d400055ac2043b0a8000ad58308761500015e30010ec2a0003179cf65985400062f398cb30a8000c5f655ce61500018b8cab9cc2a00173518573985400066ab9ec330a800487e86dd561500970f90dbaac2a00021fa1f65585400043f438cab0a806bc3d7419461500011ef0eb08c2a012f0f1db65505400043fc2aed18a800487c855da315000b1e902bb462a00030f195748c5400243f42eec98a800087d85dd931500090fd0b3b262a00021f616764c5400243e428ec98a800087e86dd531500010fd0fb2a62a00021f21f654c5400147b43ec298a8000c3f749d1658c0c10fb0f392cb180028fa1272596300051ec24e4b2c6006a7a809c9658c0d54f301392cb180031be0972596302f43f438e4b2c6000a3e841c9658c00147b08392cb180030fdcb42596300061eb9684b2c600087e87909658c0010fb0f212cb1816e8f612425963000717c1284b2c6000c3f72509658c00187ae4a12cb1816f8bc8142596302df1690284b2c600087e87109658c0010fb0e212cb181668fa1042596302352f418e2b2c6000a5d831c5658c0010fd0fa0acb180021f61f41596300353d40082b2c6000a7980105658c0010fd0f90acb180021f61f21596300051f42642b2c6000a3d84c85658c0010fd0e10acb180021f61c21596300051f42042b2c6000a3d84085658c08d4bd0610acb180029760c21596300353d40042b2c6000a7980085658c00d1790ea12c9180032bdc942592300243f42ee2b24600087d85dc5648c0090fd0bba2c3180021f61774586300347a43a42b0c6000ea942481618c001dc242902c3180121fa1576906300043fc32eb20c600087f87596418c0010fb0eb2c831811b179cd65906300062f32ae720c6000c5d655ce418c0019aae6b0c831801a3d21d61506300346ec1eebb226000c3d75d53644c00317f0ea16c8980032b5c942d91300043fc2ae3b22600487c855c7644c0090fd0fbaac8980021f60b75591300061fa16eab2260008bf845d5644c0010fd0e3aac8980030f1d774591300043fc2ae4b22600487c855c9644c0011bf06b92c8980023de05725913002c7a40ae4b22600087e87d49644c0090f90fa92c8980021fa1d52591300043e43aa4b2260018bc87509644c00187eeaa12c8981930f1d5425913000657b9284b22605895e87dd54
  | 6 => 0x43f43881b2a620087d87103654c4a54bd06206ca988029760c40d95310053741081b2a6200a6d82103654c4a34ed02206ca988029d60440d95310043f43e41b2a620087d87c83654c40147d09906ca988028f61320d953100716a1641b2a6200e2d42483654c4010fd0e106ca988021f61c20d95310051f42041b2a6200a3d84083654c4a54bd06106ca988029760c20d953128d3b40841b2a6200a7581083654c4a38bae7b2ec89880387d0f65d91313662eb98cbb2262058dd83dd7644c40b1bb07b96c898987175cf52d91312fe2eb9aa5b2262018bf8750b644c4b593ae6a16c8988032b5c942d91310043f43ecab22620087e87195644c4090fd0fbaac8988021f60b75591310061fa16eab22620087e871d5644c4010ff0ab92c8988121f21572591310047dc02e4b2262068f8805c9644c4010fd0fa92c8988121f21f52591310043f43aa4b22620087c87549644c4031790ea12c8988030fdd542591313261e3aa84b226200caf72509644c403958e4a12c89881a3720d75d813100657b9285b026201cac7250b604c4039c8e490ec0988121fa1b755813128c3e436eab02620087e87d95604c401878e9b2ac0988031b1cb65581310043f438cab026200c3c74195604c4018d8e432ac0988030fd9774581310061e32ee8b026200c6f65dc9604c4018d8cbb92c09894f179cc65181313662eb98ca30262008fb87580604c4018beeba9ac72001a3721d3258e400243f43eeab0c800087d82dd5619000187e85baac3200021fe1572586400243e42ae4b0c80008df835c961900051b906b92c3200021fa1f52586400243e43ea4b0c800087e8754961900010f90ea92c3200030fdd542586403261e3aa84b0c80068f48748561900010ff0abb463200121f215768c6400043fc2aec98c800487c855d931900011df04bb263200063b209764c6400062e3aac698c8005ad48158d31900014ed0331ecaa00029d60663d95400043f436e5b2a800487f87d8b65500018dae5b16caa00021f61e62d95400043fc3ac5b2a8000a5f8358b65500014b906b16caa00029de0562d95400053a40ac5b2a801f87d8718b65500018dae4316caa012e8f21942d954026e1f3b285b2a8000e2f6250b6550001c58c4a16caa00030fd0b72d95400043ec3ce5b2a804ca3e849cb655000147b09396caa00031be0972d95400061fa12e5b2a800087e871cb655009947d08396caa012e8f61072d95402651fc1285b2a804ce2f8250b655000187ee4a16caa00030f5c942d95400043f43c65b2a800087d878cb655009947d09196caa00028f61232d95400043f43865b2a800087d870cb655009947d08196caa00028f61032d95400053b40865b2a8000a75810cb65500974f500196caa00029e60032d95400052f41ce3b2a8000a5d839c7655009947d0838ecaa
  | 7 => 0x5e851c963904014bb0a392c7208b6a7a107258e410054ec20e4b1c8205ad6811c9639045b5ab02392c720802b6a007258e410056cc00e4b1c8270e1f42d49639044953d09292c720802a76125258e4100727c12a4b1c826fe1f42549639044953d08292c720802a76105258e412ed4fc1284b1c8224e8f825096390401c3ea4a12c720803875494258e410052f42ee0b1c8200a5d85dc163904014bd0b382c720802976167058e4102d6b40ce0b1c8200a9f845c163904011bd0f282c7208023761e5058e4102d6b408a0b1c8200ad58114163904014bd0b902c720802976172058e411254f42640b1c8200a9d84c816390401d1a85902c720803a35092058e410046f43840b1c82008dd8708163904014bd0a102c720802976142058e411254f42040b1c8200a9d84081639040b5ad02102c720802b56042058e410146f41eeab0482008dd83dd560904090fd0bb9ac1208021f617735824100656b9284b0482058f8874816090401d5284902c1208021fe1570d8d410243e42ae1b1a820087f855cf60504090f90ab9ec0a08032bdc942d81411ae57b22e430282008fb87580605040b17d0faa2c9188030fdd7545923102c5e43a84b246200caf72509648c4090fd0fbaac11880317a0f75582310062ec1eeab04620087d82dd5608c4798be63baac1188f3174c775582310043fc2ae4b04620487c855c9608c4010fd0fa92c1188121f21f52582310043f43aa4b04620087c87549608c40187eeba12c1189970f1d742582310061fbaa84b046264c3c75509608c40b1f10e902c118803aa50920582310077090a40b046200a6e82993654c4014db05326ca98946d5a0743d95310043f436e5b2a620487f87d8b654c4018dae5b16ca988021f61e62d95310051f424c5b2a6200a3d8498b654c4010ff0eb16ca988961f61c62d95310051f420c5b2a6200a3d8418b654c4018dae4316ca988029ea0062d95310053cc00c5b2a6265c3e76d0b654c4c987ceca16ca988038bd8942d95310071631285b2a6251a5c864cb654c401c98c4996ca9894a9d21921d95310073231243b2a6252a5e83dd3654c4a34bb07ba6ca988030f5d074d95310043ec3ce5b2a6200a3e849cb654c40147b09396ca988031be0972d95310043f438e5b2a6200a3e841cb654c40147b08396ca9894a97a0c72d953128d2ec18e5b2a6251a76811cb654c4a54eb02396ca988029ea0072d95310053cc00e5b2a6200c3f72d0b654c40187ae5a16ca988021fa1e42d95310043ec3c85b2a626ea3d8490b654c401c5f04a16ca988030fdc942d95310061eb9285b2a620087e8710b654c4010fb0e216ca989b68fa1042d95312943f43e83b2a620087d87d07654c4a50fd0f90eca988021f61f21d95310051f42643b2a6200a3d84c87654c4a54bd06386ca989469760c70d95310
  | 8 => 0xc0060840100400c000030010020240083102a0087e86dcb6550c090ff0fb16caa18031b5cb62d95430043ec3cc5b2a8678a3d8498b6550c010ff0eb16caa18c21f61c62d954300636b90c5b2a8656a3c8650b6550ce387ceca16caa18038bd8942d95430071631285b2a8600c3f42dcb6550c010fb0f396caa195e8fa1272d95433c51ec24e5b2a8600c6f825cb6550c0187e84b96caa18021fa1c72d95432bd1f420e5b2a8656a3d841cb6550c018dae4396caa195e8fe0942d95432bf17c1285b2a8600c3f7250b6550c0187ae4a16caa195a97a0e71d95433bd2ec1ce3b2a8600c75711c76550c010fd0f90ecaa18021f61f21d95432bd1f42643b2a8600a3d84c876550c010fd0e10ecaa18021f61c21d95432bd1f42043b2a8600a3d840876550cad4bd0610ecaa18029760c21d95430053d40043b2a8600a79800876550cad4bd06386caa195e9760c70d95430063cb80e1b2a860087e87c836550c010fb0f906caa195e8fa1320d95430051ec2641b2a8600e2d42c836550c01c5a84906caa18021fa1c20d95430043ec3841b2a8657a3e840836550c0147b08106caa195a97a0c20d95430052ec1841b2a8600a76810836550c014eb02106caa180e3760f72d85433be2eb9ecb30a8676c3d741966150ceb8bae632cc2a19d3355cf61985430043f43ecab0a860087e871956150c011ef0eb08c2a18032bdc942d814339e2eb98cb302860487e86dd56050cad0f90dbaac0a18021fa1f65581430043f438cab028672c3f741956050cb18bce6328c0a19c7175cc65181430047dc3ac03028600c3f42dc965904bf0fb0f392cb209568fa1272596410051ec24e4b2c8200c6f825c9659040187e84b92cb209861fa1c72596412ad1f420e4b2c8200a3d841c965904bb47f04a12cb209578be0942596410061fb9284b2c8200c3d7250965904010fd0f192cb208021f61e32596412ad1f42464b2c8200a3d848c965904010fd0e192cb208021f61c32596412ad1f42064b2c8200a3d840c9659040b4ed02192cb208029d60432596410053d40064b2c8200a79800c965904014bd07382cb208029760e705964102d3b40ce0b2c8237a75819c1659040147f08b82cb209568f21170596410043f43e60b2c820087d87cc1659040b4ed02182cb208029d60430596410043f43e40b2c820087d87c8165904ab47d09902cb208028f613205964100716a1640b2c8200e2d4248165904010fd0e102cb208021f61c20596412ad1f42040b2c8200a3d8408165904014bd06102cb208029760c205964102d3b40840b2c8200a7581081659040b1b90ea9ac72080297a163258e410052ec2c64b1c8200a9d848c9639040b1b90e992c7208121fa177058e410043ec2ee0b1c8200a5e859c963904014bb0b392c720892a7a127258e410054ec24e4b1c8200a
  | 9 => 0xa91471c40040f689c8b1168a119f10520591bf95918c800217a5122d9510001ea04500006b04b86009d8bb867a5c89fa501361e49ff1fe86d9cd87585fa5c2441aa0ed0001f58608000b28820960001838638a89d903a8060580000000a70af9870ec8b18000000001121459b50d299d1ea80017e87d91986fa469258a11a126c1c100003e9ac87f17b2550ea0bc80000022aa3f00016906401987713c8571d59a516f00024f0188540be0001ae05125f83623297c1e40ee80001f83094b80003810a0000dda1f8b60000f80000de123a630000000ff8000001fa17a8000b51b28c4a6a8001bb0f58000490000088dd01d08d8001700001372368000e289d00009900000000000000017391380003a0629222190ca1629600f893b02b80024096482694119406a1e01971bc90d10f97b92f24c214931979a202258819e61558c186d213a260baa3b80020a1059e11379ac11b20e1e90b793d0dca0200013e02580021e83294a8a31e692312881f17313b8178190a4a42842832000226a3111c1860128000000001f9a598000000000eba4926580004aa5e8000cd21f0002218b88000000001641d40a40148000338350000c30dfa3c97400010a800002a6d83b0000a02400fa80e8be97a0a18000760a626b9200fb9ef19f01101c0180b40000501c0580301402c0d4000020200a0020110040640200100202c100000000001503e04c0100000000003c0180000603c0180e0220000b0020100c00900a0060280400200e0000080000c01800005000000008000040040880c03e03c000020020100002900401c050170080080000903807c0400000202c0000000a0000682700e0ec0000102002c0380100000c0580f00000c000000000080501100003c008000000000180900000c0b80500e0101280400000000006002004000000060042481e010074070000200c0000090020000000201c024020000000540000b0001040901800003c0280102c00c038000000140180c0000040280300e0201d008002004000010080000080103e0900b0050060280082e0040080182600202c0a80b046030068070461480d80200004c0a0000080000200500e01002030002028030000080580b807000000000000000180000101c0e80200002201c00802000014000030020b80100c0100080401101a02c0000007603011805000000030000000080700a00c004000130040000980900002c0380600203000000000000008150680e002002000000000020281cc0c8000080040980000c05c0b0000080180300102e0340682600801401004018004000120040000280d00004c008070080041900002005c0380005001c0080202603c0600601400c09800000000120000000100380200408007014000064010040000003181800606806800014010000010000040b
  | 10 => 0x204020508a0cd9ab0b59e29f71a00c88000001dea2806e9b215b81200018e0ba19e8001ee86700000020d12a2538001281a81d190000007890c9fd8000000000b81778001fd0001d008f24b0001dc8cb00005a0000001af0001d085d0f3a22167a5313a86c84216108b8e501e8df2670c9800000190046a0a951a4982700006b8660f082f94c1ef80000015b0aa0002249e09fc07c023a039a08d187200021717198582b0c72091300e691f8c914c92c8a6a0b1420b69099a221a8d49030000000d815e8ee22400019908814da4622f03da60a361a314999a0e31a48169f385e9ce0cf15f0fd94396522784f16396e04f98a16ba51a3917d01399a9e70461830e4a450db08900800f9391029ba95fa681540ce0828220f4a5702d9451d512c0742548001b8a1d1db1cb1c08da0619c3a02870a379911d104e0bd0a218a965a1a03717da2286896a98d9341308cc12d2611822621538a087c8c1071a420021be8f60f9041a6c83022c9e39da0980da9f31c29bf00192495da6d0dc1e31b619da3d0101c91b41b498c0311f68f7096a5617c93516f92788f884910111107115a5087e82a040a6e820112865053a2b8171489560b3a3a07284a23811521e0c820f0508ac23e0d5a56a23a3f83f9afa4e90c0000aaa5d89789a1468d0a5d119000258a3c1358970d200001a8001b680015280004d990a641219531de2389481548378d7192a4d9a585b96d944a081b58c28872699ba0838500000002338f112909f25a04107900110e08300005180004c00010d88793d8bb09c00020c9eb80000016d00011a0ec0851f2a0118d1ad88c0001891922520859930000e81dc1b724a92e16806f0de9e20001cf17500000000e20b8000001db941a1300000003698f95a0801b1099a088a389b9e1a4f95a9999868528001d78438d989e8000000000002128000000001e80e00b01299aaa1b00c044022878149104007a2080022e1749550000fe92b00aa558039ee0001f00000070000002690001ed8000000001b91fe07d17680021080a20080000000006911e80010780000000000015c8000000000001d311b80015c1a29ce8001588699df92518198518094419187a257a041a4010a5a8ea9f78001da98e8ac9349d99f082e8000000c699c9338001bc0cf9c01dd0b08000000d90000d523aa4a0001a90ca8658b70e61fc8001408611368241d8166a0d8e202f00018b80000000006a80002e0000001e590b00b1a192e98280c80013f9330fa1b98000001228d388c8e423d9c31b7a480af230a2a228a0f98b0c607f8209261050ae18887a80026a207a4b8809d68988551848b999683b9709381f619e06c1fb2098c084819894e07e264a4720713118f0d68140b209391089e2668e791c8a2a110ada5b05e0299df13c0860ed82112d96b09000311885b064800
  | 11 => 0xc415800008d00019826287516a00025b9f8a1994f82482c16187683f00020e8c010800008a94d0748001898b91a6926a0480b91f08880000000000014a2231f188404794f1131eb1f81e880024c80000007300015692fa2e9bb94b18403400014280000011d8000001672290f51ed0118bc1170e0a182150130470c39f90000630000e18000932300e913881503c08e06200000004ea618579aea430ab1fa8000001d481100022989b2638002068001ff8000ff00000000009a80017f0000000000000000d00001609ad0001dd844a478000a99271461958ef9791a891a9b023200000001585580020600013a00003980021b9a39e78f01f505c8e99c20001e98000000bf1bd05d8f785f231a6b07780f1148000059cf8001ab8fc8002542660000001c78cb80000519f9d70e3a4d1a61b3a418091760e70000b404586690f0430598d78fc0cc80008e828a1c1d221883d16226522f96990182d091201a001ca95711e07b2251d28000fe25810600000000013280003e1182161b300000018804d10919b81b1431810a7881106a6e1bd99505a8281d38c50f28e584880d99b14002c916a4597121c9010fb10ea2123312ba6f09282501c9d8a0c02aa43a2d1118bda5f11400001c12123583910b9be23e8000001c6800180252972a140000921c801e1b080016e8530ab9770a5a0317e03195d1720f31a999c0001ec15e1cd25e00080024e0ce8292102270f42411f20f9a688f18918568e88d60940ad07b8230b303c8499cba678ef0bf818058a39a3480026007018781b8278d30738fd2370908c21cc1e51c888b00d0a51500d89c60d105c16c1cc9631fb81a13e8c78681089a71f497593f1c59d615995093980011d0001c1903a5900014ea351c99661320d40348798959b805483316c84c821a1d9241c519788681d826009a15a3b17806e004957a489161f40f204b2059789209c492a8561c70001ca1048358c59478160898db9521ec9938068710e10950ae97fa2b2168389961b18b4894900917a122448a81a7a3422c1948eb0001
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1c68038429000200000050000081618c89221e606a610000058a6406250b654c4016619018921d95310058a2594248365440776609648520d95101e69821921483654400142d9219772d91101d6a821921483644400142d9219572191100060b61572188644400188d835c862191100060ba1972548644400182c865c9521911000629a197288464440018a8865c920191100052a25d4248163440038a8875092058d1000e3821d21481634406b9a3746087050510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x1
  | 7 => 0x4b
  | 8 => 0x4c
  | 9 => 0x4d
  | 10 => 0x4e
  | 11 => 0x94b
  | 12 => 0x94c
  | 13 => 0x94d
  | 14 => 0x94e
  | 15 => 0x124b
  | 16 => 0x124c
  | 17 => 0x124d
  | 18 => 0x124e
  | 19 => 0x138b
  | 20 => 0x138c
  | 21 => 0x138d
  | 22 => 0x138e
  | 23 => 0x9cb
  | 24 => 0x9cd
  | 25 => 0x9ce
  | 26 => 0x12cb
  | 27 => 0x12cd
  | 28 => 0x12ce
  | 29 => 0xa0b
  | 30 => 0xa0c
  | 31 => 0xa0e
  | 32 => 0x130b
  | 33 => 0x130c
  | 34 => 0x130e
  | 35 => 0xb4b
  | 36 => 0xb4d
  | 37 => 0xb4e
  | 38 => 0x144b
  | 39 => 0x144d
  | 40 => 0x144e
  | 41 => 0xb8b
  | 42 => 0xb8c
  | 43 => 0xb8e
  | 44 => 0x148b
  | 45 => 0x148c
  | 46 => 0x148e
  | 47 => 0xe8b
  | 48 => 0xe8e
  | 49 => 0xb8953
  | 50 => 0x94b93
  | 51 => 0xb8956
  | 52 => 0x148953
  | 53 => 0x1489
  | 54 => 0x95493
  | 55 => 0x148956
  | 56 => 0x10a
  | 57 => 0x289
  | 58 => 0x130a
  | 59 => 0x14c9
  | 60 => 0x134a
  | 61 => 0xb9393
  | 62 => 0x138b93
  | 63 => 0xb49d3
  | 64 => 0x9cb53
  | 65 => 0xb49d6
  | 66 => 0xe89d3
  | 67 => 0x9ce93
  | 68 => 0xe89d6
  | 69 => 0x180c
  | 70 => 0xa4c
  | 71 => 0xb8a13
  | 72 => 0xa0b93
  | 73 => 0xb8a16
  | 74 => 0x168d
  | 75 => 0x1949
  | 76 => 0x134d
  | 77 => 0x14d
  | 78 => 0x149313
  | 79 => 0x131493
  | 80 => 0x184c
  | 81 => 0x17ca
  | 82 => 0x14cc
  | 83 => 0x2cc
  | 84 => 0x16cd
  | 85 => 0xbcd
  | 86 => 0x194c
  | 87 => 0x17cd
  | 88 => 0x74c
  | 89 => 0x1889
  | 90 => 0xd0a
  | 91 => 0xd09
  | 92 => 0x5853
  | 93 => 0x188a
  | 94 => 0x1a09
  | 95 => 0xd4a
  | 96 => 0xd49
  | 97 => 0x1a0a
  | 98 => 0x14a
  | 99 => 0x2c9
  | 100 => 0xd0e
  | 101 => 0x188e
  | 102 => 0xd4d
  | 103 => 0x1a0d
  | 104 => 0x95896
  | 105 => 0x94d16
  | 106 => 0x12c996
  | 107 => 0x749
  | 108 => 0x5ca
  | 109 => 0x14d894
  | 110 => 0x14cd14
  | 111 => 0xd4b55
  | 112 => 0x1a0b55
  | 113 => 0x5cd
  | 114 => 0x75314
  | 115 => 0x5c9d5
  | 116 => 0x16cb55
  | 117 => 0x5cb55
  | 118 => 0x74b94
  | 119 => 0x17cb55
  | 120 => 0x194d14
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1285
  | 6 => 2220
  | 5 => 1247
  | 4 => 18
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (52253+((h/428+packedAt gbK7 (47545+(h % 428)*11) 11) % 1543)*12) 12
  | 6 => packedAt gbK6 (115440+((h/740+packedAt gbK6 (106560+(h % 740)*12) 12) % 2665)*13) 13
  | 5 => packedAt gbK5 (78138+((h/415+packedAt gbK5 (73573+(h % 415)*11) 11) % 1497)*12) 12
  | 4 => packedAt gbK4 (1290+((h/6+packedAt gbK4 (1260+(h % 6)*5) 5) % 26)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xf07f870783f0ffff0e03f81ffc28c79e0cf4cf
  | 1 => 0x7f87f807fc3f0e03f003ffe0fcd724667348f3
  | 2 => 0x7ff87ff8003ff003fffc3fff03183879838f3c
  | 3 => 0x80007fffffc00003ffffc00003e03f81fc0fc0
  | 4 => 0x7ffffffffffc0000000003ffc001fff000
  | 5 => 0xffff8000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x90088100804012890208480a4800418a041445
  | 1 => 0x2485180324110412901292c0b0432424314892
  | 2 => 0x49502248002aa02024a0251401180850828128
  | 3 => 0x4044d95ea80004bc95b00421ae036815c0ec0
  | 4 => 0x84076e6533cc9700060018423bd8001ebe000
  | 5 => 0x7e6600c06208818081820618c3feff7e000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefae8feeaf8e8feeefae8feeaf8e8feeefae8feeaf8e8feeefae8feeaf8e8feeefae8feeaf8e8feeefae8feeaf8e8feeefae8feeaf8e8feeefae8feeaf8e8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36220
namespace PEqualNP.Outside.L_meta_36220
open PEqualNP.Outside.L_meta_36220.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 4 := bs0_3_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 4 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 12 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 20 := block_range (n:=20) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 20 := bs2_3_0
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
theorem bs2_4_128 : Interval s2Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_320 : Interval s2Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_352 : Interval s2Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_416 : Interval s2Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_448 : Interval s2Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_512 : Interval s2Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_544 : Interval s2Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 551 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96)) (concat (concat bs2_4_128 bs2_4_160) (concat bs2_4_192 (concat bs2_4_224 bs2_4_256)))) (concat (concat (concat bs2_4_288 bs2_4_320) (concat bs2_4_352 bs2_4_384)) (concat (concat bs2_4_416 bs2_4_448) (concat bs2_4_480 (concat bs2_4_512 bs2_4_544)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_64 : Interval s2Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_128 : Interval s2Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_160 : Interval s2Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_224 : Interval s2Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_320 : Interval s2Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_352 : Interval s2Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_416 : Interval s2Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_448 : Interval s2Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_512 : Interval s2Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_544 : Interval s2Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_608 : Interval s2Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_640 : Interval s2Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 666 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 bs2_5_192) (concat bs2_5_224 (concat bs2_5_256 bs2_5_288)))) (concat (concat (concat bs2_5_320 bs2_5_352) (concat bs2_5_384 (concat bs2_5_416 bs2_5_448))) (concat (concat bs2_5_480 (concat bs2_5_512 bs2_5_544)) (concat bs2_5_576 (concat bs2_5_608 bs2_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := (concat bs2_6_0 bs2_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 60 := (concat bs3_3_0 bs3_3_32)
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
theorem bs3_4_160 : Interval s3Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 165 := (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat bs3_4_96 (concat bs3_4_128 bs3_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 50 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 60 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_160 : Interval s4Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 165 := (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 50 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 15 := bs5_2_0
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
theorem bs5_4_512 : Interval s5Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_544 : Interval s5Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_608 : Interval s5Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_640 : Interval s5Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_704 : Interval s5Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_736 : Interval s5Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_800 : Interval s5Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_832 : Interval s5Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 894 := (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)) (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 bs5_4_416)))) (concat (concat (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)) (concat (concat bs5_4_544 bs5_4_576) (concat bs5_4_608 bs5_4_640))) (concat (concat bs5_4_672 (concat bs5_4_704 bs5_4_736)) (concat (concat bs5_4_768 bs5_4_800) (concat bs5_4_832 bs5_4_864)))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_704 : Interval s5Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_736 : Interval s5Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_800 : Interval s5Atlas 5 800 20 := block_range (n:=20) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 820 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat bs5_5_96 (concat bs5_5_128 bs5_5_160))) (concat (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)) (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 bs5_5_384)))) (concat (concat (concat bs5_5_416 (concat bs5_5_448 bs5_5_480)) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576))) (concat (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)) (concat (concat bs5_5_704 bs5_5_736) (concat bs5_5_768 bs5_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_4_0 : Interval gbAtlas 4 0 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 18 := bgb_4_0
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
theorem bgb_5_1216 : Interval gbAtlas 5 1216 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1247 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))))) (concat (concat (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))) (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)))) (concat (concat (concat bgb_5_928 bgb_5_960) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056))) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216))))))
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
theorem bgb_6_2208 : Interval gbAtlas 6 2208 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2220 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)))))) (concat (concat (concat (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344))) (concat (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472)) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632))))) (concat (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)) (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)))) (concat (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048)) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)))))))
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
theorem bgb_7_1280 : Interval gbAtlas 7 1280 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1285 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefae8feeaf8e8feeefae8feeaf8e8feeefae8feeaf8e8feeefae8feeaf8e8feeefae8feeaf8e8feeefae8feeaf8e8feeefae8feeaf8e8feeefae8feeaf8e8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074664 * 2 ^ 32 + 4276812008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36220.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,5]⟩,⟨.and,[3,6]⟩,⟨.or,[1,7]⟩,⟨.or,[0,2]⟩,⟨.and,[8,9]⟩,⟨.or,[2,4]⟩,⟨.or,[3,5]⟩,⟨.and,[1,12]⟩,⟨.or,[0,13]⟩,⟨.and,[11,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4276812008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4276812008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36220

open PEqualNP.Outside.L_meta_36220 in
theorem PEqualNP.Outside.L_meta_36220 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4276812008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4276812008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
