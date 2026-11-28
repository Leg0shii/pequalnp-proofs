import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37021.Model
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


end PEqualNP.Outside.L_meta_37021.Model

namespace PEqualNP.Outside.L_meta_37021
open PEqualNP.Outside.L_meta_37021.Model
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

def SBf (j : Nat) : Nat := [6, 8, 6, 6, 6, 5].getD j 0

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

def mirrorSteps : List Move := [swapRows 50]

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

end PEqualNP.Outside.L_meta_37021

namespace PEqualNP.Outside.L_meta_37021
open PEqualNP.Outside.L_meta_37021.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xa00300c19000d0401ce14008f1082c9004a0000df43be43bc43dc439c43be42bc42de32dc32be41bc41de31dc31bf40bd40df30dd30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40000050000000531c02c20000000000000000cf00000600030824d000291394412002080000821c794e438f290871e5110e3aa021c794e429b28c851e548caaca31947150328f29c832e529063ca918d394a318e2a0631c5350258a4a04d145408e2a6611c544c298a4985514530
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x30420859865210e0e6294443831895010e146154043
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
  | 2 => 4
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
  | 3 => packedAt s0K3 (609+((h/7+packedAt s0K3 (567+(h % 7)*6) 6) % 46)*6) 6
  | 2 => packedAt s0K2 (155+((h/1+packedAt s0K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffff03ffffffffffffff87ffff
  | 2 => 0xfc0fffc0fff80ffffc1ff03ff03ff81ff9ce73
  | 3 => 0xfff03fff03fff01fffe0ffc0ffc0ffe07e739c
  | 4 => 0x3ffffc00001fffff0000ffff00007f83e0
  | 5 => 0xffffc0000000001fffffffff000000007ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x844108482092040400a5245124510a8a0294a5
  | 2 => 0x2922948649215a8b2c0a522a522ad055394a52
  | 3 => 0x30a4a5121a4542b355409a889a88e5415c6318
  | 4 => 0xa2cb3a2490766cdd9a730c30ef3c41866f83e0
  | 5 => 0xc30c3c38e3878f1ee39cef3c0c30861877fc00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37021
namespace PEqualNP.Outside.L_meta_37021
open PEqualNP.Outside.L_meta_37021.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x32007802400000480098036000000000a801418c2600411a53aa00003e0840000015800000001001109c005cd001c0000352000000001380002c60500a8000001c00000580003c00000004510d0050020000000012000000000002000608000000c000ff43fe43fd43fc43ff42ef42fe42fd42fc42ec42ff32fe32fd32fc32ff41f741fe41fd41fc41f441ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x6617d52cc3de85987b10b30bf28e617d51cc3ee83987d10730fda0661f840cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa5187bd0a30f621461de328c3b865185f94630bea8c61f7418c3e88318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa9261ef524c2dea4985f14930f6292616c524c3de84987b10930bfa8a61f7514c2eea2985f14530fa28a6174514c3ee82987d10530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4187bd0830f621061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861f7410c3e88218778c430ee188617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83ee83907d10720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bd0a20f621441ef32883d865105f94620bea8c41f741883e883107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f7a1241ec42483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483ee82907d10520f790a41ed21483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef42083d884107bcc820f6190417e51083eca2105d94420bea8841f551082eaa2107dd0420fa20841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10f7a1621ec42c43ee83887d10710fb18e21f531c43ec43887d48710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10f7a1421ec42842faa3087dd0610fa20c21f731843e863087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910f7a1221ec42443ee82887d10510fb18a21f531443ec42887d48510fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52043de84087b10810bf28821f741043e882087dcc410fa18821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf421077c8420ef10841f621083ac42106fca220efd0441fb20883bd41107ea8220df94041bea8083f654106eca820ed95041fba9883f653107eaa620fd14c41fba1883b743107ec8620fd50c41daa1883f443107eea420fd94841faa9083f452107ee8420f9d0841fb21083b642107ea8420fd10841da21083e442107488420fdcc841fb19083f532107e86420fdd4041fb28083f550107e8a020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998df94b31f7296636e52cc6faa598fb54b31b6a9663ef42cc7d88598fdd0731fa20e637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31bf29463ee528c6dca518df54a31f6a94636d528c7de8518fb10a31bf28c63f7418c7e88318f7cc631fb98c637e508c6faa118dfd5131bf2a2637d544c6f8a898dfd4931be29263ef424c7d88498fdd0531fa20a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831f7a1063ec420c6fca218fdd0431fa20863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fbd0b21f621643ef32c87d86590fdd0721fa20e43f631c87ea6390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52887de8510fb10a21f719443ed32886fca310fdd0621fa20c43f731887e86310fbc8621fb90c437e50886faa110dfd5121dfaa2433f54486fca890df55121be2a243bc5448678a890dfd4d21bf29a437d53486f8a690fbd0921f621243ef32487d86490fdd0521fa20a43f731487e86290fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821f7a1043ec42087dc6410fb4c821bf28843f741087e88210fd8c421fa98843ef21087ec4210fb48421fa90843e521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d03de85a07b10b40bf28e817d51d03ee83a07d10740beaa4817e53902faa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5207bd0a40df21481bc42903d885206b10a40bf28c81f651902eca3205f54640faa8c817551903ee83206f90640de20c81f4419036883205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40dfa1a81bd43502fea4a07bd4940b7a92817c52503d8a4a05b14940f7a1281ec42502fea2a07dd4540bba8a817c51503e8a2a05d14540fba0a81f441503f680a06f90140bf2a0817e53102faa6206f90c40de218817e52102faa4207bd0840df21081bc42103d884206b10840bf288817d51103ee82206f90440de20881f4411036882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf29
  | 2 => 0x8000010020040040080001c00401801002008000060000040000301e01006809008014130000200040001200200804003010000080090040480100c00001c00801006002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf29487ee5290edca521df54a43f6a94876d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa9287ef5250edea4a1df14943f6292876c5250efea2a1fdd4543bba8a877c5150fe8a2a1dd14543bfa8287fb5050ef6a0a1df14143fc28287785050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42bf28e857d51d0afca1a15f54342f7a9e85ee53d0bdaa7a17b14f42f7a1e85ee43d0bda87a17b10f42f7a8e85ee51d0bdaa3a17b14742f7a8685ee50d0bdaa1a17b14342beaa4857e5390afaa7216fd0e42dea1c857e5290adca5216fd0a42f7a14857e5190beca3215d94642bea8c85f55190aeaa3215f94242bea84857f5350af8a6a17bd0942df212857f5150beea2a15dd4542be28a85f45150ae8a2a15fd4142be282857e5410afca6215f54c42dfa1885bd4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0217b95042b72a085ae5410bdea6217b94c42f6a9885ec5310bde86216bd0c42f721885ed4310b5a86217b10c42f7a8885ee5110bdaa2217b14442f7a8085ee5010bdaa0217b14042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332f7a1665ec42ccafca3997d94732bb28e657d51ccbeaa3995d54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f7a1465ec428cbbe65197bcca32bf28c65f6518caeca3195f54632faa8c6575518cafca1195f54232bfaa2657e544cafaa8995f15132f7a1265ec424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cafaa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41f7a1683ec42d06fca1a0df54341fba9e83f653d07eaa7a0fd14f41fba1e83f643d07ea87a0fd10f41fba9683f652d07eaa5a0fd14b41fba1683e742d07ec85a0fd50b41fa21683e442d07ee65a0fd8cb41fa99683f432d07eea1a0fd94341faa8683f450d06faa920df94e41bea9c83bf439077a8720df94a41f7294836e52906faa520fb54a41b6a9483ef429077c8520ef10a41f621483ac42906fca320dd94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0fbd4941b7a92837c52507d8a4a0db14941f7a1283ec42507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083e
  | 3 => 0x7700b800214415992481c6d443700b08c69c002bc206001b508f2b6564920000268cc7800016abdcf40003c4db4bb8000009f4b5800000001050000005cc0002833865dab8000de0017c2e7216ad5932fa4ea9cc002a601a3d843102000878003753cadd0000b00007c8839dd344dad1a8006dc0254800015c575652255d4b38003605286a04f84d346dbd0c32c1bc1784e27204c8f8e7b6c2745101521b2709a5410ed0647456195131c404758966780d52cab224c7355201c14e3b06f936694764f717f46cae8090f76163e1629044be1583c0085be2c40000000060d701c438ec740018b1909e09a2705e693cdf0876480a43b963000bd4000be5fedc0002e357a725a30bc3d40e14232e3fa000001672a4778502010008196b8004700018d80050c3f8003020ae44c9632a2eada4000e407e000000144f674c0f917000240e332f66c92554ada58c519300d96029303100029057d870ac0000000000056200185036638a9c000002ac00000227000de126a301fa72c00000000000c8000424680cf29509e838f98c12b82c98ba4a4a48a80028a0006e5680003da501a28000007bc2fa3a000000000000000012b08004e0581d8002c04795f839186bb83a14a00000098823566a142d80012e170120000004259f0555da001800000002300021d27c0005088b266ab000283546880381e1428000af1420003850a911000cac72a7f000000000000c23258b12b00077cc7abb47879d439ff000ad923a9b5380013a1080f6a25ad80064054c732db502809b20006341400004e36c0007a9e6000790001e92644a096b5565a5e181b594cc3100027e00045868ae500022073a8d5cc269361640006150b96a3ae95c9e2cc53e6c1b28000000000000012a000ab80028a2cc70299000244d6800246c14002c44868b8b72eb3f4975b11354805383902033e9a8ccad245e1acd500081a0040280300000200c0080101e028010000000180900301a0040d80100e0480280802e0580080001c01801801006014030010100140080000a0100100f002004030000100000380300200000005006004008000020000000900e0000080001e0c40280a00a018050000100e40081c01402800000002004000000040040180f03604c1c802006070008010000380000f0020000a00000400407803050054018090020000700402e024068030000000380201401c0a804004018000060140040400100a004018000000000100702a0080080102a00009003002000038020000201580a00201c000020000000180201a00005806000020048150160380000300202001002002018008270060000001a004010000010020040480002c000000000040100000101a0000880000001001800006008010090040040980001a0000300e0000000680400206c01006002000018040
  | 4 => 0x5727f84189b0000002c0000d4661bb048036a21a7ae95d0c54cb0000009b97087a000130003300f86c4e08451984e4ea8695e20000000063e060950000ec91400000000000f88000002942934255eced460000008680f3096bc91132041300000bca9d0006053c8b9230000000000fe15000000000820002c71ae4c00035a3c0905a08ee6f2c44b09da542495571926a82ad65a7721e00055000000d40001db176180d28672e8a00341ab62006529a7a33a248002ef51c000aa000170000de0ff40e7ec1e9f623436c8e97c014001940e813a21000149000000000c64206c9310071685ed01b074b6a3c7d8cf0da18d9882d4a06ddae0dc37a000000e96e428d13318326c3d048af47a00d568000000045693d2ecb4d3e0a64720c1a726b1f21f4002d9000720bf0001f40387a2f05d85bc19a370000dc750d63ac9540000068e34d0622100010ca5a1c0ca738c89c5078001a68005bad756e3275fc00000059000aa0b6155696c88f625105e8a0011ac5403c41f29134c89166851352595b3261042335580005e80000023b00000133800342000000000000000001a000d00000040005306d000000c1017000114d7c000002f4000000341124510229e0e26353791b5922780000061000000343062620001b3088a948601d1260017c9716885a43600061a349918000000006aabe020dcd9fa54000014fe31e000000b81f0394a497225e4220003c8000000005e80018e5f400000544d24a18003ea93812a2d47ec310693b17eb016a04a16e175640c00009c5552c1674190b10000fc5600000065200046800000000000423c6000c600002a0000002c00047c0007300000000000000000871954848d149a225e40017e2320000001d3061847017b26d626a61059d2000b445d00643e84c511945ac2a4c512066603cb42d521a000000000001d58cb52000cd1001212b4000973563040ac002fb0007aca816d34851c710dd252918628006ce66c000004ec000ea0400008648e09830e0895a00c6c60002d0813860015b9b411c4551598966e9a1ac20516c8a4dfad8220859a425827e53c4a33d24e4dc0899a2cc611458823f28b0d7a4b4b461865296376bf5a9912196505b41d0000000000000007dc7e2c2000000003210cc401890d400000097800148d319ca3119c534259724ca3c8ec1c24c67316f0d020c6d442800244000001f8370001b08470000014d0000007d0d72b800097167800000001928000000007980000000107ae21506e80000052e0000000062836077b7166addd55a232322642485367
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x520082ac6448020b318d20082e46148020d9545200827b65480209798f54c425d63d53109b98b54c426d62d53109bd8954c426c62553108f99353c423d64d4f109b98b53c426d62d4f108f99253c423d6494f109b98a53c426d6294f108f99352c423d64d4b109798f52c425d63d4b10cb95042c432d5410b10cd95041c43355410710e910841c42e5628c710ad19121c436452487109b98b548426d62d52109bd89548426c62552109bd89538426c6254e108f990538423d6414e109b988538426d6214e108f993528423d64d4a10cb950428432d5410a10cd95341843345410610e910841842b664cc610b998b318436752086109b98b544426d62d5110cb98b544432d62d5110cd587544423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109dd85544427461151108f994544432f6215110cb18854443376115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b18953442776154d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d49109b993524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c53149109b990524436561149109b997424426c65d0910cbd53424432c54d0910d3d4f424434c53d09109b994424426c6510910cbd50424432c5410910d3d4c424434c53109109d997414433454d0510d5d4f414435453d0510d9d4b414436452d0510cdd5041443345410510d5d4c41443545310510d9d4841443645210510e91084144276658c510cd1523144354538c510b958a3144364528c5109d1953144334544c510d514d3144364524c5109d99621443345488510d514e214436452885109d19521442b46448510cd15121443545348510d914921443345484110d514e104436452841109b98b540426d62d50109d987540426f62550109b189540427761550109798c540425d63150109b988540426d62150109b98b530426d62d4c108f990530423d6414c109b988530426d6214c109d984530426d65948109b992520423f64548108f19152042ac6454810cbd91520426c6454810cb191520422c6454810d9185520426e62148109d984520426f65d08109b597420426f65108109b594420432f5410810cb150420436652d0410d954b41042756510410cd95041043665210410d954841043a442104109d59731042b664cc410b998b310436552cc4109d5943104365520c4109d597210436552c84109d59421043655208410d954b100427965840109dd9510042b46444010b518d10042e46244010d9549100427b6544010
  | 1 => 0xc2766494430d9d0a510c3644294430cd951510c3355454430d9949510c36552544309d191510c3674254430d9109510c27765d04309d597410c33654d0430cd553410c36652d0430d954b410c27765104309d594410c3365410430cd550410c3974310430d9948410c3655210430e9108410c2ce628c430d5546310c33954d0030e6d0f400c2796510030e610c400c3a84210030ec104400c25f654c030a7191300c2cc624c030b5185300c27b654c030ae191300c25e63d53209758f54c827661d53209d58754c827761553209d18554c823e64d4f208f59353c827661d4f209d58753c823e6494f208f59253c82766194f209d58653c832e5410b20cb55042c82e5618cb20cd95041c83355410720e910841c82ac64487209d987548827561d52209dd85548827461552209dd8553882746154e208f990538823d6414e209d98453882756114e20cb953428832c5410a20ab99332882e661cca20cd95041883355410620e9108418827661d51209d587544832d62d5120cd987544833561d51208f992544825e63951209758e544827661951209d586544825f63551209718d544826f62551209dd85544827461551209b188544823e6515120cbd8854483376115120cd184544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534825e6514d20c7d50534831c5414d20d3588534826e65d0920cb153424834f53d0920d314f424832f5410920cb150424834f5310920d314c424826e658c920cb152324834c538c920b9586324826c654c920cb151324834c534c920cdd53514833454d4520d5d4f514835453d45209d993514836742d4520d910b51483375414520cd15051483575314520d514c51482766414520d9d0851483644214520d98c8514836532145209d997414827465d0520cdd53414833454d0520d5d4f414835453d05209d99441482746510520cdd5041483345410520d5d4c41483545310520e9108414826e65c8520cb153214834c53c8520d914721482ac6448520cb151214834c5348520d9145214832c5488120d314e204836451881209b98b540827661d50209d587540826f62550209dd85540827461550209798c540825d63150209d984540827561150209d987530827561d4c208f990530823d6414c209b98853082766114c209d584530826d6510820cb950420826d65cc820ab99332082e661cc8209b59432082766494420d9d0a510836442944208fd91510823c6454420ad191510833764544209d191510833464544208d19151083674254420d910951083673254420d90c9510827765d04209d597410827765104209d59441083375410420cd15041083a442104209b59621083655188420d9544210836551c80209bd9
  | 2 => 0x5214540cdd0c51503354314540d9d08515036442145409d997415035753d0540d514f415036752d0540d914b41502766510540d5d4c41503545310540d9d4841503645210540e9108415035853d0140c714e405032c5290140cd146405026f6254c409b18953102776154c409d185531023d6590c40ab98a43102b66190c409dd8552102746154840ab98a42102b66190840cb54c42103aa6010840ea580421032c42944409bd89511026c6254440e910b41102ae6290440ad98641103a74210440e910841103355310440cd94841103b26010440ec580411032c4294040cd10650103a84290040ec106401023f6550040a718d40102ac6250040ad185401027b6550040b618d401026e62d53309b58b54cc27661d53309d58754cc26f62553309b18954cc27761553309d18554cc2766194b309d58652cc32e5410b30cb55042cc26e62947309b58a51cc3365410730cd55041cc3a44210730ea10840cc3b041103309b98b548c26d62d52309d987548c27561d52309bd89548c26c62552309dd85548c27461552308fd91528c23c6454a309dd85528c2746154a30cbd50428c32c5410a30e3d0c428c2d6618ca308fd91518c23c64546309bd89518c26c6254630cdd50418c3345410630e5d0c418c3a44210630b398a318c26e62d51309b58b544c27661d51309d587544c32e62d5130cb58b544c33661d5130cd587544c23e64951309b98a544c26d62951309d986544c275619513097d8d544c26f62551309b189544c27761551309d185544c27b60551308f994544c32f6215130cb188544c3376115130cd184544c32f54d4930cb153524c26e64d4930cbd50524c32c54149309b990524c26e65d09309b197424c32f54d0930cb153424c26e65109309b194424c32f5410930cb150424c33754d4530cd153514c36752d4530d914b514c27664d4530d9d0b514c36442d4530cdd50514c3345414530d9d48514c36452145309d990514c3674214530d9108514c27665d05309d197414c33754d0530cd153414c36752d0530d914b414c27665105309d194414c3375410530cd150414c3675210530d9148414c3a44210530ce153304c31c548c130d314a304c354518c1309b98b540c26d62d50309d987540c27561d50308f596540c32f6295030cb18a540c3376195030cd186540c26f62550309b189540c27761550309d185540c31c6355030cbd89540c32c6255030cdd85540c3346155030ce181540c23e64150309b988540c26d62150309d984540c2756115030c7553430c25d6510c30cb952520c32d54948309b992520c32e5454830cb551520c26c64548309bd97420c26d65d0830cb953420c32d54d08309bd94420c26d6510830cb950420c32d5410830e3d0c420c34d528c830b5986320c3365494430cd552510c3665294430d954a510
  | 3 => 0x1319e181544c72f5410931cb150424c67665d0531cd153414c6d663d0531cd950414c7a44210531ad993314c6e662cc5319b988504c66d62141319b98b540c66d62d50319d987540c66f62550319b189540c63e6494c318f592530c72e5410831cb550420c6756510431cd950410c7355410431b558c410c7a44210431b958a310c65f654c4319dd95310c63f64540318f191500c66f62540319b189500c65e63153219758c54c863e6414f218f59053c872e5410b21cb55042c86ae64ccb21b998732c873654d0721cd15041c87a44210721b958a31c865e63152219758c548863e6414e218f590538872e54d0a21cb15042886e5618ca21cd95041887355410621e910841886b664cc621b998b318872d62d5121cd587544863e64951219bd89544867761551218f994544872f6215121cdd84544863e6494d218f592534866d6294d219d586534863f6454d218f191534867b6054d219e181534866e65d0921cb15342486e661d0921cbd50424872c54109219b99732486ae64cc921cb15332486e661cc9219b994324872c540c9219d997414873454d0521b998b41487375410521cd15041487a442105219d99731486b664cc521cd15331486e662cc5219d9943148734540c521cd153214872c54885219b98b540867661d50219b98b530867661d4c218f992530863d6494c219b594420872e5410821b9584420866d658c821b9586320866f654c8219d59441087365410421b958841087a442104219d59631086e5628c4219dd9531086e562884219bd9521086ac64484219dd9521086b46448421b9d9521087676548421e9d9121086e66448421b919121087a46448421a919121087665448421d915121086e76348421b958d21087665348421d914d21086e460484218fd91500863c645402197d8d500865c6354021d9485500866e6294f409b58a53d02766194f409d58653d02b86050f409d98652d02756194b409b98a51d026d6294740e910841d02ae6290e40ad98643902b66190a40cb54842902ad6510a40cb594429032d5310a40cb10a51903665294640d954a51903a44294640d9d0a51903364294640cd10a51903644294640c910a51903665254640d954951903a44254640d9d0951903644254640d994b419036552d0640e910b41902ae6290640cb94a419032e5210640cd54441903665210640d954841903a74210640e910841902b56510640cd59441903355310640cd94841903a65210640c994841903a552106408f997435031c53d0d40c714d43502b86050d40d3d4f525034c53d4940d3d4c525034c5314940cbd0c525032d43149409b997425034f53d0940d314f425026e6510940d3d4c425034c5310940d5d4f515035453d4540d9d4b515036452d4540d9d0b515036442d4540d5d4c51503545314540d9d485150364
  | 4 => 0xb54c429076652d0641d954b419072c42942419b997425066e6510941d9d4b415076452d0541cb14a415066e6294c419b58a53106ac6250c41add8543106b86050c41ab98a42106b56190841cb54c42107a66110841e9584421072c4294441b998a41106e56290441e910a411063f6550441ab18941106776550441b9d8941106e46250441e9109411072c429404197d8d501065c63540419bd89501066c6254041cd99254106b56395041ad98a54106b66095041b998b53106e562d4c41b998a53106e56294c41d554c531079653d0c41e554f43106b662d0c41ad98343106756590c41ad59243106e66290c41b958a43106776550c41b9d8943106e46250c41bcd8143106f06050c41add9543107376550c41e5d8d43107a76250c41ad18943107a46250c41a918943107b36050c41ad18143107b06050c41ac18143106b66410c41b598f52106d563d4841d9548521076654d0841e995342107a743d0841e950f42106756590841b998a42106b56590841cd59642106b56390841ad98a42106a66290841ad98242106776550841e950842106b56310841ad98842107a66210841e994842107a55210841ad98042106e66410841e999042107665410841e995042107a74310841e990c42107a54310841e910c42107a76510841e999442107a56510841e919442107a76310841e998c42107a56310841e918c42107a75310841e994c42107a55310841e914c42107a76010841e998042107a56010841e9180421067665cc8419d59732106b664cc841ad59332107a442cc8419d9963210675658c841add9232106b4648c841e910a32106b7644c841ad19132107a4424c841ad99032106b5640c841e910832107a442d4041e910a50106d76354041b518d50106e76254041b918950107a44254041b598c50106d56314041b998850106e56214041e9108501066e62d53319b58b54cc72f6295331cb18a54cc73761953319bd8954cc66c6255331cbd8954cc72c6255331cdd8554cc66e62153319b58854cc72e5494b31cb55252cc66e6494b31d958652cc72e5454b31cb55152cc66c6454b319bd9742cc66d65d0b31cb95342cc72d54d0b319bd9442cc66d6510b31cb95042cc72d5410b31cd95341cc76652d0731d954b41cc7365410731cd55041cc7665210731d954841cc7a442107319b98b548c66d62d52319e983548c67960d52319bd89548c66c62552319b988548c66d62152319b992528c63f6454a318f191528c6ac6454a31cbd91528c66c6454a31cb191528c62c6454a31d9185528c66f65d0a319b597428c66f6510a319b594428c72f5410a31cb150428c76652d0631d954b418c7365410631d9948418c7655210631e9108418c6b664cc631b998b318c76552cc6319b98b544c66d62d51319bd89544c66c62551319dd85544c67b6055
  | 5 => 0x53d0ae76154f42b918553d0ae66114f42b958453d0ae66190f42b958643d0ae76150f42b918543d0aeb6050f42ba18143d0b8d4310f42d9d4651d0ace6314742b358c51d0ace63d4342b358f50d0ae661d4342b958750d0ae66194342b958650d0b1e5350e42ad1854390ab86050e42cdd0e5190b354394642d9d0a5190b674254642d9d0b5150b674214542cd9085150a766194c429d5865310aaf6250c42ad1854310ab86050c42b99864210ae561908428fd954210ab461508429bd954210ae76150842b91854210a5f63540429718d5010a7761540429d1855010b2e6495042ab58e5410aae6195042ab9825410ae661d4c42b95875310ae66194c42b95865310b4d5314c42e394f4310b8d53d0c42ab9874310aae60d0c429b5964310aad6490c42b99864310ae56190c429bd954310ae76150c42b91854310aeb6050c42ba1814310aaf6550c42cbd954310b8f6350c42e9d854310aac6150c42e91854310aa46150c42ead814310aac6050c42ea1814310aa86050c42ab9904310ace63d4442b358f5110b655114442b3d8d5010acc6354042b9d855010ae46154042b398c5010acd6314042b99845010ae561140429d98754cca7561d5332cbd8a54ccb376195332cd18654cca7761553329d18554ccb2f6255332cdd8554ccb3461553329d98454cca756115332cb95342ccb2e5410b32cb55042ccb365494732cd55251cca766494732d9d0a51ccb644294732cd95151ccb3554547329d19151ccb674254732d910951cca7661d52329d587548ca7a60d52329e583548ca7761552329d185548ca7661152329d584548cb2e5410a32ab993328cae661cca329d992518cb674294632d910a518ca3f64546328f191518cab46454632cdd91518ca746454632cd191518ca346454632d9d09518cb644254632d9cc9518ca7661d51329d587544ca6f62551329dd85544ca7461551329ed81544ca7860551329b997424cb2c54d0932b398f424cb2e5410932ab993324cae661cc9329d984504ca7561141329b98b540ca7661d50329d587540ca7761550329d185540ca3e6494c328f592530ca6d6510832cb950420cb2d5410832b358c420cae5618c83297d95320ca6f654c8328fd91500ca3c64540329dd85500ca7461540329bd8953d066c6254f419b98a50d066d6294341d5d4e53d06e76254f41b918953d06e66214f41b958853d06e66290f41b958a43d06e76250f41b918943d06f36050f41bc18143d07954310f41d9d4a52d06d66314b41b558c52d07a66410b41e9d0c42d07a54310b419d99732d067565ccb41ad99332d06b564ccb419d99632d0675658cb41b598f50d06d563d4341b998b50d06e562d4341b998a50d06e56294341c794d43906ac6250e41ae181439072f4394a41cb50e529072d5210a41ab594429072d6510a41c
  | 6 => 0xfa509b506f9ed016a320851ce9eea7c80005382ca189de1e385480000008100000119399522826e99004a2101a300028702987f8000c7a7e80017e8e29c787e0f49088cc17c84ca119f200009308000006d98d0000000d80ff0000001fd9fb8000ad91f80021a80026f0f18b885da8e0001fd16f0002220000001509528588000c024b00000000028a00006e80000009180aa6e1858fb21c11ca9a8000001b6a7d98827aa218ac8000c40000bc80009e25b004a7b13e941a2a8770001f68000000000240001a00200c00002002008060030060040380a028008008290000001181f00200800800004024058050140c0000000020040200e024014000010000000a80502e01c0000201c078010090180140381200e0000d80d00800000006044014000000220040780a0020080501701002004007006000020030020080100500a0080000a00a01801005038000000040220000500200000415000000010000010060040000800200c0000000e0000e0000080040280400a000000090000001400301000c0401b00206400003050020008000020340100500600000000010000000020000000800000002c0500b006010020000040840100000400c000010000040000300200800800000038008050040140080900200c0000700003c0100601000806800000000030000180280100100c01c0300500a0240180a0160000000500a03806800002078020010020000001c000000040000040000e8010000040100c036004078000160100580d00800405000002018010000040040000101002400002040010008000300000000400201800800000014070110040300300000c00c0000400008c0000b0080080180200800006000012000018010000040700100a0000580100403801003000000028000000400400400007c000010000040300501200008802000044030020140a8040100020280180002e00c0080502200800007004048008050080140180400000c0000600c00c010070040140282e00c004018040060000081d008000048000040640100000a0200001d0120000383600000400001002000078020000040000200002c000000060100100300e034000000060240000a9dd8552d0e746154b439bd8951d0e6c62547439b98a50d0e6d62943439d98650d0e756194343cbd0e5290f665294643d954a5190f374394643d99495190f655254643ab98a4350eb66190d43d9d4b5150f6452d4543d9d485150f645214543dad4b5050f6852d4143dcd475050f7051d4143dad485050f685214143dcd445050f705114143d6d0c5050f3a43141438fd954310eb86050c4397d954310ed86050c439d9865210e7561948439b98a5110e6d62944439bd895010e6c62540439dd855010e7461540439dd8553d0a746154f429d98650d0a756194342d3d4e
  | 7 => 0xa312b2891e49220619599ad1ca128800000006a6597915e00994396f9b08000000000000002940000000e48001378000248400819c707c8f624c00000000002e8000000968000000f900028400000c93293a10b1eaa3da9b2711c118f8af8000f31920000000200001a78000b80ab1988001421ee2528b70522361af1840001ac1e294485b0790368d902500019fa4b89a21a0000b900014500003389518280000010581094a0000640bb038a4683c83187404997398c2108c50000209279229e6a9717983f91110a86691a80000000005b9ab10903a0000000c4a9d0192431b800014b9ba82f0b58001129290a787b8a885089a8c30271691cc92817aa9880020b23b1919820000cd26d8e7869237926a7686586000000005f80000024295585c0f98001850000150000001d20fa1a381d81b8000001781990301db0001208caa552210689b19028ca00000000010123d0000488000001578000000000000278002900000000001079948001bb19d00000007181e00003d25804080028b14c93515380014b0000000fb96b8222319fe0002050aa80018984217b8001f1013a7c00026280d05a0ef1038e90000779b399111e2692639510001f8a6f97d80006e0000d61940e1a6d1e200f9e0a069bda479a680c07321f00009d0c2a08a258000d5294a0e80a07f0378fc8000000c12649e98219e624d17323f8c5a910d20e398c8a8138a1f874a621d5a3413f98d9969cc04b90d84686788c930a749ae9eb09b9cd0859db84900015ca4f80020313d0000000001998b600000000017e05306c80012e80006317582f8e61c006ba348879aa00009001100000010c9601962779ef0000da0af1bf99310522c9390001d68d480000006091922518000012589ca7006d1dd80004e00000000000010012c0000000001f395d8001610ce8db0000000000000001ea1158ffa8f0002801fc00021e8000fd16880000016319801c8000fd80026c20f8000002448001bd0000448470e415ba7b8001c92161d98000001a180000026700014406a000000000000000123a3e9770100dc00010a04c2330001178a20f7a831b60eda92a2e0431c4a861b283514f949a5d17099c17501aa979711af9b480000000025e9590000001698aba3c00000016c80000022ea889e31349c28e225c8002261888a08000002679468000eb299a56800208273a5212c95b00e0128848a60ad01e814822a1b0b6a0a29c1ec906867241a7e0b21b70309e8286a99136a8d1f298f01805985d0e30ae10e88d9fc981a8f940a6097fa2f09b166a229e50551502470948001a229195180026b87027f26812e1c193e14780508a8c980001f148a110000001f70001dea968d88e5a4e06482317892322904121e07600000007d0dc9761ac8cf8a01621fa0269568438bf219a788b021494c01b1f
  | 8 => 0x3b1bc0f6a159a012a80014d9d900400016399591b0020000a593700d8e693824100e84d9ab85680000000008c19da7f90315725880016429d8b10000000ea0000001ce18a9198dd8fa8000000001978000001be00010200000000017f2130000000b30000090000e50001971b791b9e4131802834a8b8000001f180027280020f0e00001fe9d48001ec17a2439d0235972003a59a759b42781a09019b5a298bd99f0000002201a708627203c22ba2b1bea1697782d1f4a3e11f00000005a9c895887580012da0010b80023800029c89821d07da688000880efa5a0001550001a6165a0202a0001a99769108000d310f1f51650392908621300c6005904a578d402583ba48800a828a48000b9a920140869e180005e80029a0b780000005c90602e00000015fa8c1161a405800000000000000000010c08908896089109898919e8ec1a80002611d102b16e8d9a1809c16d1338d18cf1f321c9c08000e895e94121281d00008f26a0000001eba809d706aa958000280611cf28a80000000000015a00024e8ba1eda5f80017000001191a1e12931740199a11458000210c70001a926504404a9ad8b19878ed13a8322510f000000000008e9070629040e80a994aa0386c1a487800788b84d0709f423506f06b2288c69da18e8559cd8710310fe0a19869bc9ff0c818e23123888708d174845a632040b288387200015d121a5c046042a120bf87c00024200015308fa5600003e1870be1b8a5580000028d8a423922d04802da0488a06980024503300000000003d80019b000217a3a82414e25a8f0807236a2a02a80000014f0001da84f2459100b08942399661310238171d813208e20da7415218b8959f0a7514603f01fa0a9839cb8d09541299b100020094d11d9dc1249490a71e700000008b00003400004b12b9e5a9b8c38d5a13a0c9bf2279ba0cd9d60000001c600000016c09280021515800012a15624d80000000024404523380007980008414e8fea2d980a8e97b1a29c52490d68ac076800154865284a85a5e0590002302818000a900007a8b4a762532798158be8ea8d019a0c90a389d9c31330922881f61138939618260d78cc8000c21c99aaa5d80000024a98b1f90001f01b903600025f0a50328a69d380000000016a13f00017d07398111212f1efa0599b93998313589f91500005793c8db8000bc22f8000418000cba0912fa0b8b52238ba8f40bd1252938160001f783e8002518fc09e8c88000002248002309f583700000023f0f39e00dd0510ae8f706621b88292d00002ba191fb0de14016e00000027185f1908ec8002600000680000000001861670002028000999df2409648dfa32a1713d9c68898000001ae2541d400000000016da771d789f23a0c19429172141b3254a8380019a80000b8f88ee26c8f80e9a0d0000d2800
  | 9 => 0x23b8000a10130e700f000000134000063a8ca5926b0978e085700020982893b07280b249a0180013c0ee88300020e11680000010e0f59678189dc8002820001c39189d28080e11141d88b38f524ca480da8d39caa1d9e908209622090824f0121d500000000002c285162839a4a27a1d098a2270f21b20030478000000560f29a525011c1b98df25702915a8380991d3281000206000253a2680000000001780000000000019c9211e8a2c27d078851800224270a5b85285000000016a91e8970358d1000000000264000000287a400002461929f99f80000001729b01430001180000eba7915c0002070000001680000000000000000aa080a230000000ce00000000000000020117c0000002980001c81240000bb80000000015f1bb9849df80000020787a00890f80011187b1a8a3c9c20000001719dd07514701c0541c596b1361260909a58d70b40c08f104ea618de9cfa6605e20c0001faa95127001800000266a8980004f80601a0cb1c407e90094810980000000003a8000000a28000000000001e78001d190d13b9cb26980011327323726aa9619e12000011d1148
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x20ca6761095010743b1884a8083a118c4254041d0cc6210a020e856310850106923a2c329663491c95410731a48e8a908398d277510841cc692ba88420e6389dc46454a31c48e2322a518e2464185528c695386a821463491d152d0631a48e8a908318d2775108418c6923a2a598c638999152cc631858e8b10a098d2472550410c712b288420863a158c4210431948e8b146218d157315041c86523a2c518e43435cc5410a21948e8b0c6510d0e73d88544868b39ec22a2438915261d092185eec2a66490e245498732487122a4c5a0a430ddd854cc521c48a93166290ca47458632086523a2c518843299d26448421c4eca3224210e27751912108712324a890843891905448421948e8b1a4210ce07058d21086333b4a690843499d25348421c48c929a4210e246414d21086923a242a8043891912154021c88c690aa010d287050c52502983828628a81499d44210540c4cca21082a07075310841503822988420a81491c55310840b10e6b0084205247254c41102c839ac0208810d1d16194b30a48e2aa0859842c7458a51cc292392a820e61499c75410a30a4ce5aa0831862662987544c312310c22a261499c75410930c4cc8216a29852672d50414c2933a6a420a61499d44210530a48ea210829862665108414c3123288420a61891886195030c48c430aa81861863181540c314310c0aa0618c1846055030a48e2aa0841860d65d0c420c31232084a8861491c95410430c2acba18821852474548410c293ba88420861495d44210430c4eca210821862565108410c314b2884200618c5944110030a48e2aa085904a47458632c821b3a6c2a9c41499c75410920948e8b0c649062454586324832229ac3192418999042d4520c4cca2108290624651084148383a988420a41c114c4210520c18c829a429062464145214821a3a2c3a984189dc86454420c48e4322a21062464d09510831232084a8841499d33254420c48c9992a210624640c95108293396a820841455cc5410420c4eca21082105247454621082923a2a210841491d151c8020a48e8a8a401062464545200832231aa290041491c95410710948e8b1463886246414921c42173a6c4a9c21499d35208610a48e8b08a488524711504244293396a820a21499d35210510a4cea2108288524751084144383a988420a21c114c4210510948e8b1462886245458a314432229ac518a21195d8528c510868ec2a242886146414d2144312320a490a210b1d162d4c10c4ee2322a408624711915204312320c2a9021499c7541081085aec2a0840850d7315042042923a2a5a0821491d15210410a4eea21082084677654b31042923a2a5988218999152cc410a48e8a9062085247454b21042923a2a410821491d152c40108c8eca922008524745491004312322a4880219118d5244010
  | 1 => 0x1e91d9cc81381408df00314000000074f459370e5ae10000452c726aa7562ba38b109cc932ac14e31478659a264a01c00b40db4000143b2c8e02d30009bcc15e85878881b80070000017092695438554b82d1b06c622aa683ebc240fd46da39909966663b75809e0c0c8a821410cc8a7514ab0c6566e2804ad329a3880ab30848145d32388d480688880000182450acf6c13416ae44948aeca16178cecc1d29586782800000d6630b97600498012ab93d800124c612f8066f258015e7c50b6d0e8c2883c2e002f88c000e179608800702188cb345aa55a7f20a0d6a0000800002800000006b0000000003bb64002000249208d000704884000194c000f3486a6d4d84c009c6a0ec102b4c000007e00034d07d25054b6001a25cf23e002280074002dc9e0c00291449f40800342a5fa6400b6218580b0000006050f830020301008080202834220f000200c0701018080b010040a07078240002008002402048a006030000006080280002000901008060080c00250000800050106c020400008260401804221000d2a7290c5050e9938c8628287621c14310f42c34a630287215307050e5190a5238ac72a085299c6609504294ce330686216a061d814310b15b28c0a1885a2d8c6050c42d46c230286216a0611814310a9238aa821665891904254732c4ee4322a31962472191518cb1232684a8c65499d33254632c48c9992a31943474584504ca9238aa821065291d1618c832b20e0a1887a0da07050c42d070d298c0a1c834a1c14394a41948e4b1ca820ca6729825410653394c1a1883a818b6050c41c66ca3028620e93631814310751b10c0a1883a81886050c41b40e0a1e8420ca57690c4210692bac862108368dc14310841b40e0a188420d8673d9442106c2b9eca21083619ce6510841b0ae73288420d2575d8c4210692bacc621083a158c631084194aed2988420f055314c4210693baac02108361dcd6010841b08e6b008420d867318042106c2b98c0210838999442cc841c4aca2166420cb270d9232107133288519083295d8420c841b0ae621064
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x960031a0018242a9233a0060480a0683dc86454632a0683dc46454a31a0683dd46448421827871925348421c047418d2154021c047414d618c920a0683dc86454420c047418d5148020c047414d628c510824845d8528c510a0683dc464548108248799152cc410824871915244010c047418d5244010
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 227
  | 2 => 14
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (i*5) 5
  | 6 => packedAt s1K6 (i*16) 16
  | 5 => packedAt s1K5 (i*27) 27
  | 4 => packedAt s1K4 (i*38) 38
  | 3 => packedAt s1K3 (i*49) 49
  | 2 => packedAt s1K2 (i*60) 60
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (6+((h/1+packedAt s1K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s1K6 (802+((h/14+packedAt s1K6 (704+(h % 14)*7) 7) % 99)*7) 7
  | 5 => packedAt s1K5 (27286+((h/296+packedAt s1K5 (24030+(h % 296)*11) 11) % 1175)*11) 11
  | 4 => packedAt s1K4 (55826+((h/446+packedAt s1K4 (50920+(h % 446)*11) 11) % 1769)*12) 12
  | 3 => packedAt s1K3 (11798+((h/75+packedAt s1K3 (11123+(h % 75)*9) 9) % 273)*9) 9
  | 2 => packedAt s1K2 (860+((h/4+packedAt s1K2 (840+(h % 4)*5) 5) % 18)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffff81ffffffffffffff0fffff
  | 2 => 0xfc07f03ffe03f80ffe0f83f03ff81f80f4c7cc
  | 3 => 0x7ffc0fffc000ffff003ffc0ffe000f8f8f0
  | 4 => 0xfff80000fffffffffffffc0000ffffffff00ff
  | 5 => 0xffffffff0000000fffffffffff000000ffff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x1430108202489040805284b14518a2a6015b55
  | 2 => 0x5952a58c643922d79605a155366a9b0a74c5cc
  | 3 => 0x52a4c316a89074ebaab0426d94b6ca14b8e8f0
  | 4 => 0x60c68a28d122468d4d29680820c71c58de00aa
  | 5 => 0x83070c30e1c3870e71ce738e38041060efb600
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0aaaa0000faaaaaa0aaaa0000faaaaaa0aaaa0000faaaaaa0aaaa0000faaaaaa0aaaa0000faaaaaa0aaaa0000faaaaaa0aaaa0000faaaaaa0aaaa0000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37021
namespace PEqualNP.Outside.L_meta_37021
open PEqualNP.Outside.L_meta_37021.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x140390280196512460000bf43bd43be42bc42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x180000014000008ea98852c525065ca5205554430
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
  | 4 => packedAt s2K4 (208+((h/4+packedAt s2K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s2K3 (113+((h/1+packedAt s2K3 (108+(h % 1)*5) 5) % 17)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 1 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 3 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8040888500808002904c02240229109408d131
  | 1 => 0x10891048252442502a11214921422528a22486
  | 3 => 0x895229034a480ca58426541654054a85454b18
  | 4 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaee88eeaacc88eeaaee88eeaacc88eeaaee88eeaacc88eeaaee88eeaacc88eeaaee88eeaacc88eeaaee88eeaacc88eeaaee88eeaacc88eeaaee88eeaacc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37021
namespace PEqualNP.Outside.L_meta_37021
open PEqualNP.Outside.L_meta_37021.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xa006288e30000a5a480600bf43bd43be42bc42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x403040008ea98852c525065ca5205554430
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s3K3 (112+((h/1+packedAt s3K3 (108+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 1 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 2 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8040888500808002904c02240229109408d131
  | 1 => 0x10891048252442502a11214921422528a22486
  | 2 => 0x895229034a480ca58426541654054a85454b18
  | 4 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37021
namespace PEqualNP.Outside.L_meta_37021
open PEqualNP.Outside.L_meta_37021.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x21a000094c43800301df32ee32dd32ed32cd32bf41bd41be40bc40
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x20ca0084e6000a6a9c658f544cb18a899634cb41c69928338505071a6520634c840
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x101060a2983544ca0c654c941c24c8505060f654ca40
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | 2 => packedAt s4K2 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (156+((h/3+packedAt s4K4 (144+(h % 3)*4) 4) % 15)*5) 5
  | 3 => packedAt s4K3 (224+((h/2+packedAt s4K3 (216+(h % 2)*4) 4) % 11)*4) 4
  | 2 => packedAt s4K2 (156+((h/1+packedAt s4K2 (152+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xe0fffe07e0fc1f87fe1ff0ffe0f0783ece7e93
  | 1 => 0xff07fffffffffff81fe0ff07ffffffff318fff
  | 2 => 0xfff83ff800ffe1ffe000fff8ff007fc1c1f31c
  | 3 => 0x3fffff0001ffffff0000ffff8001fe03e0
  | 5 => 0xffffc000000001ffffffffff00000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2a1182314528a881660530296891489c463691
  | 1 => 0x40400442004000100820410201241220108826
  | 2 => 0x8622a890d6928baaa1149ab0ba826585c15318
  | 3 => 0x14b53124941acdccd35608a0dccb4109ea03c0
  | 5 => 0x18c621c718e311771d98ecc4100c0631bdec00
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeee8eee8ccc8ccc8eee8eee8ccc8ccc8eee8eee8ccc8ccc8eee8eee8ccc8ccc8eee8eee8ccc8ccc8eee8eee8ccc8ccc8eee8eee8ccc8ccc8eee8eee8ccc8ccc8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37021
namespace PEqualNP.Outside.L_meta_37021
open PEqualNP.Outside.L_meta_37021.Model
def s5K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xcd32
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (i*5) 5
  | 3 => packedAt s5K3 (i*16) 16
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (6+((h/1+packedAt s5K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s5K3 (17+((h/1+packedAt s5K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffff03e0f83f0ff0ff0ffff83c1e0f667e93
  | 1 => 0xf07c1ffffffffff07f07f0703fffffff9993ff
  | 2 => 0xff801ffc00ffc3ff8007ff803fc01ff0e1e31c
  | 3 => 0x1fffff0003fffff800003fffe000fe03e0
  | 4 => 0xffffe000000003ffffffffffc0000000fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2119011845115101902902919a245226222691
  | 1 => 0x4002221004000202102102200490488089026
  | 2 => 0x622b5448d6a5175688a5ab04aea09962e16318
  | 3 => 0xcb53989294359b9b5ab08a093732d044f603c0
  | 4 => 0x8c6210e318c622ec6cc6cc4e04030188ddd800
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xeeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37021
namespace PEqualNP.Outside.L_meta_37021
open PEqualNP.Outside.L_meta_37021.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x84006280001094d20450131e0040b8600482e31c00e9c361002d1809386ac9a284d12c99956a7700028e3a492889d142b06a4007c0004b54000005000055600000fa13c0543c969230014000020000000144826608802020250a2e0001ff54007f95001fd54007f15001ff52007f94801fd52007f14801ff42007f90801fd42007f10801fe32007f4c801fc3200ffd44037f5100ff94403fd5100df54403fc5100ffd0403bf4100ff90403fd4100ef50403fc4100ffc8403fe2100ff48403fc21007fd4001fe50007f54001fc50007fd0001fe40007f50001fc40007fc8001fe20007f48001fc2000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x844002ff44220047f2211000bfc1088001ffb2a4000bfd9520006feca900027f6548001ff32a4000bf99520007faca90002fd6548001fe32a4000bf19520006f8ca900027c6548001ffb224000bfd91200077ec890002bf6448001ff3224006bf99120007fac890002fd6448001fe3224006bf1912000778c890002bc6448001ffaa24000ff95120007faa890003fc5448001ffb1a4000bfd8d20007fcc690016fe6348001feb1a4000bf58d20007f8c690016fc6348001ffa9a4000ff94d20007faa690003fc5348001ffa1a4000ff90d20007fa8690003fc4348001ffa924000fbd492001ffca490003fd5248007fe2924000fb14920007fe849000ffe4248001f72124000ff50920007da849000ffc4248001ff9924003ff8c920007dc6490003fd3248001f69924003ff0c92003ffec29001eff614800fff30a4001bf9852003ffac29001efd614800ffe30a4001bf1852003ffea29001f7f514800fff28a4007ff5452003efaa29001ffc514800fffa0a4007efd052003ffc829001ffd414800fdea0a4007ff1052003ffe629001ffe314800ffe98a4007ff0c52001ffe429001fef214800fff10a4007ff4852003fda429000ffc2148001ffa824002ff94120007faa09000bfc5048001ffa024002ff90120007fa809000bfc4048001ff9824002ff8c120007fa609000fff2048007fd9024002ff88120017dc409001fff1048005ff0824007fe8412003ffa209001ff91048005fe0824002ffd9420015feca1000bfe65080017f3284002ff59420005faca1000bfc65080057e3284002ffd9020015fec81000bfe640800d7f3204002ff59020005fac81000bfc64080057e3204000ffd5020007fca810003fd5408001fe2a04002ffd8c20015fec61000bfe630800b7f3184002f798c20005bcc61000bfd63080017eb184002f758c20005bac61000bfc63080057e3184000ffd4c20007fca610003fd5308001fe2984000ffd0c20007fc8610003fd4308001fe2184003bf9882001ffea41000ffe5208007fea904003ff1482001ffe841000ffe4208007fea104003ff1082001ffe641000ffe3208007fe9904003ff0c820017fec21000aff6108005ff3084001bf98420017fac210012fd6108005fe3084002bf18420027fea2100137f5108009ff2884004ff54420026faa210013fc5108009ffa084004efd0420027fc8210013fd4108009dea084004ff10420027fe6210013fe3108009fe9884004ff0c42001ffe421000ffe2108007fe9084003ff08420015fcc01000bff5008005ff2804002ff54020017f8a01000bff4008005ff2004002ff50020017f8801000bff3008005ff1804002ff4c020017f8601000bff2008005f79004002ff88020017f4401000bfd2008005f69004003fe48020017fe201000bfe1008005fe8804002ff04020
  | 1 => 0xafc6110015ffa88800adfd4440057fca22002bfd5110015bea88800aff14440037fe822001bbf411000dff2088006ff504400577a822001bfc4110015ff908800aff88440057fa422002bfc21100057f3008002ffd4040017fca02000bfd5010005fe2808002ffd00400177e802000bfe4010005fd2008002ff500400177a802001bf94010005ff8808002ff84040017fa202000bfc1010007ffb2e4003bfd972001ffccb90002fe65c8007feb2e4000bf5972001ff8cb9000efc65c8007ffb264003bfd932001ffcc99001afe64c8007feb264000bf5932001ff8c99000efc64c8001ffaa64000ff95320007faa990003fc54c8007ffb1e4003ff98f2002dfcc79000ffd63c80017eb1e4003ff18f2001df8c790003ff53c8001ff29e4000ff54f20007f8a790003ff43c8001ff21e4000ff50f20007f8879000fff52c8001f7a964003ff94b2001ffaa59000ffc52c8007f62964003ffd0b2001ffc859000fee42c8007fea164000fb50b2001ff8859000fff32c8007ff1964003fb8cb2001ffa6590003ed32c8007fe1964003ffd872001dfec39000ffe61c80037f30e4003ff5872004dfac39000ffc61c80037e30e4009ffd472004efea390027fe51c8013fea8e4009df5472004ff8a390027ff41c8013dfa0e4009ff9072004ffa8390027bd41c8013fe20e4009ffcc72004ffc6390027fd31c8013fe18e4003ffc872001fde439000ffe21c8007fe90e4009fb4872001ff84390003ff50c8005ff2864000ff54320017f8a190003ff40c8005ff2064000ff50320017f88190003ff30c8013ff8864002ff8432004ffa219000bfc10c8005ffb2c4002bfd9620017fccb10002fe6588005feb2c4000bf59620017f8cb1000afc6588005ffb244002bfd9220017fcc91001afe6488005feb244000bf59220017f8c91000afc6488001ffaa44000ff95220007faa910003fc5488005ffb1c4002bfd8e20017fcc710016fe6388005feb1c4000bf58e20017f8c710003ff5388001ff29c4000ff54e20007f8a710003ff4388001ff21c4000ff50e20007f8871001efd6288001ffa944003ff94a20007faa51000ffc5288001ffa144003ff90a20007fa851000ffc4288001ff9944003ff8ca20007fa651000ffc3288005ffb0c4002bfd8620017fcc310006fe6188005feb0c4008bf58620017f8c31000afc6188011ffa8c4008dfd4620047fca310023fd5188011bea8c4008ff14620047fe8310023bf4188011ff20c4008ff506200477a8310023fc4188011ff98c4008ff8c620047fa6310023fc3188007ff90c4008ff88620047fa431000ffc21880057f3044002ffd4220017fca11000bfd5088005fe2844002ffd0220017fc811000bfd4088005fe2044002ffcc220017fc611000bff2088005f79044003fec8220017fe211000bfe1088005fd0
  | 2 => 0x4000dfcc3a001bfd61d001b7eb0e8006ff1874000df8c3a0037ff51d001bbfa8e800dff9474006ffaa3a00377d51d001bfe28e8006ffd07400377e83a001bfe41d000dfea0e800def50740037f883a0037ff21d001bff10e800dff4874006ff843a0003ff50d0005ff2868000ff54340017f8a1a0037ff10d0005ff086800dff44340017f821a000bff65900057fb2c8002ff99640005fccb2000bfd65900017eb2c8002ff19640015f8cb2002efd6490001ffaa48000efd5240037fca920003fd549000dfe2a48000ef15240017fec52000bfe62900077f3148002ff58a40005fac52000bfc6290001ffa948000ff94a40007faa520003fc529000dffa148000ff90a400077c8520003fd429000dfe2148000ef10a40007fc6520003fd3290001fe1948002ffd8640015fec32000bfe61900037f30c8002ff58640065fac32000bfc61900057e30c800cffd4640066fea320033fe5190019fea8c800cdf54640067f8a32001bff4190019dfa0c800cff90640067fa8320033bd419000dfe20c800cffc8640067fc4320033fd2190019fe10c8002bf98240017fea12000bfe5090005fea848002ff14240017fe812000bbf409000dfda048002ffc4240017fc212000bfd1090005fe0848000ffd9540005fecaa00037f65500013fb2a8000ff99540005fccaa0003fd65500017eb2a8000ff19540005f8caa00037c65500013e32a8000ffd5140037fca8a0003fd545000dfe2a28000ffd8940005fec4a0003fe6250001feb128000ff1894001df8c4a0003ff5250001ff2928000ff54940007f8a4a001bff4250001ff2128000ff50940037f884a0003fe3250001fe9928000ff0c94005ffec2a002eff6150017ff30a8001bf9854005ffac2a002efd6150017fe30a8001bf1854005ffea2a002f7f5150017ff28a800bff5454005efaa2a002ffc515000dffa0a800befd054005ffc82a002ffd4150017dea0a8006ff1054005ffe42a002ffe2150017fe90a800bff08540007fea0a000bfe5050001fea828002ff14140037fe80a001bfb4050005ff2028002ef9014005ffe20a000bfe1050017fe8828002ff04140017feca2000aff6510005ff3288000bf99440016fcca200027e6510005feb288000bf59440016faca200027d6510005fe3288002bf19440035fcc82001bff5410001dfaa08006ff95040037faa82001bfc541000dde2a08002ffd8840017fcc42000efe6210005f73108000bb98840017fac420002fd6210005f6b108000bb58840017f8c420003ff5210001ff2908000ff54840007f8a42001bff421000dff2108000ef90840037fa842001bfc421000dde2108000ff8c840007fa6420003fc3210005ffb088002bfd8440017fcc220006fe6110005fb3088001bd98440017fac22002afd6110005fab088000bd58440017f8c22000
  | 3 => 0xe2a4a000df15250017fec52800bfe62940077f314a002fb98a50005dcc52800bfd62940017eb14a002fb58a50005dac52800bfc6294001ffa94a000ff94a50006fca528003fd5294001fe294a000df14a50007fe8528003fe4294001fea14a000ff10a50007fc6528003fd3294001fe194a002ffd8650015fec32800bfe61940037f30ca002ff58650095fac32800bfc61940057e30ca012ffd4650096fea32804bfe5194025fea8ca012df54650097f8a32804bff4194025dfa0ca012ff90650097fa832804bbd4194025fe20ca012ffc8650097fc432804bfd2194025fe10ca002bf98250017fea12800b7f5094001fda84a002ffc4250017fc212800bfd1094005fe084a000ffd9150005fec8a8003bf64540015fb22a000ff99150007fac8a8003fc645400d7e322a000ef1915000578c8a8003ff5454001bfaa2a000ff95150007faa8a80037d5454001fe2a2a000ffd8950005fec4a8003fe6254001feb12a000ff1895001df8c4a8003ff5254001ff292a000ff54950007f8a4a8003ff4254001ff212a000ff50950007f884a8003fe3254001fe992a000ff0c95008ffec2a8046ff6154023ff30aa001bf9855008ffac2a8046fd6154023fe30aa001bf1855008ffea2a80477f5154023ff28aa011ff5455008efaa2a8047fc5154023ffa0aa011efd055008ffc82a8047fd4154023dea0aa011ff1055008ffe42a8047fe2154023fe90aa011ff08550007fea0a8003fb5054005ff282a002df9415008ffe20a800bfe1054023fe882a002ff04150085fcca2800bff6414005ff320a006bf99050017fac828002fd6414005fe320a00fffd5050007fca8280037e5414001feaa0a00fff15050006f8a82800bff6214005ff310a003bf98850017fac428002fd6214005fe310a00fffd4850007fca4280037e5214001fea90a00fff14850006f8a428003ff4214001ff210a000ff50850007f88428003fe3214001fe990a000ff0c850017fec22800aff6114005ff308a001bf98450017fac22803afd6114005fe308a002bf1845007ffea22803b7f511401dff288a00eff54450076faa22803ffc511401dffa08a00eefd0450077fc822803bfd411401ddea08a00eff10450077fe422803bfe211401dfe908a00eff08450015fcc02800bff5014005bfa80a002ff94050017f4a02800bfd5014005bea80a000fe54050017fe202800bfe1014005fe880a002ff04050037fecba001aff65d000dff32e8000bf99740037facba0002fd65d000dfe32e8006bf19740037fea9a001bfe54d000dfeaa68006ff15340037fec5a001bfe62d00077f3168006ff58b40005fac5a001bfc62d0001ffa968000ff94b40007faa5a0003fc52d000dffa168006ff90b40037fa85a001bfc42d0001ff1968000ff4cb40007f865a001bff61d000d7fb0e8006ff987
  | 4 => 0xffc218c807ffb046403ff98232015fcc11900ffd608c8017eb046403ff182320affe2119057fe108c82bfe8846415ff04232007feca99002ff654c801bfb2a64009fd9532007fcca99002fe654c801feb2a6400bf59532007f8ca99002fc654c801be32a64009f19532007fec899002ff644c801ff3226406bf99132007fac899002fd644c801fe3226406bf19132007fea899003fe544c801feaa26400ff15132007fea499003ef524c807ff2926400ff5493201ff8a499003ec524c801ffa126400fbd093201ffc8499003fd424c807fe2126400fb1093201ffc649900fde324c829ffb0a6414bfd85320a7fcc299006fe614c829feb0a6414bf585320a7f8c299006fc614c829ffa8a6414dfd45320a7fca299053fd514c829bea8a6414ff145320a7fe8299053bf414c829ff20a6414ff505320a77a8299053fc414c807ff90a6414fbc85320a7fc4299053fd214c829f690a6403ff08532007fec099002ff604c801ff3026400ff58132007f8c09900afc604c829ff8826414ff841320a7fa2099053fc104c807ffb286403bfd943201ffcca19002fe650c807feb286400bf5943201ff8ca1900efc650c807ffb206403bfd903201ffcc81901afe640c807feb206400bf5903201ff8c81900efc640c801ffaa06400ff95032007faa819003fc540c8077f3106403ffd483201ffca41900ffd520c807fe2906403ffd083201ffc841900ffd420c807fe2106403ff8c83201fdc641900ffd320c80bf69906400f34c83201ffec21900eff610c807ff3086401bf9843201ffac21904efd610c807fe3086401bf1843209ffea21904f7f510c827ff2886413ff5443209efaa21904ffc510c827ffa086413efd043209ffc821904ffd410c827dea086413ff1043201ffe421900ffe210c807fe9086403ff0843201ffec01900ffe600c8057f3006403ff58032005fac01900ffc600c827ff8806413ff8403209ffa201904ffc100c81fffb26a000ff99350035fcc9a8003fd64d40017eb26a00fff1935007ffea9a80037f54d4001ff2a6a000ff55350006faa9a803ffc54d401fffb16a000ff98b5001dfcc5a8003fd62d40017eb16a00fff18b5007ffea5a8003fe52d4001fea96a00fff14b50007fe85a8003fe42d4001fea16a000ff10b50007fc65a8003fd32d4001fe196a00fffd8750085fec3a8043fe61d40037f30ea010ff58750085fac3a803ffc61d40037e30ea00fffd4750086fea3a8043fe51d4021fea8ea010df5475007ff8a3a8043ff41d4021dfa0ea010ff90750087fa83a8043bd41d4021fe20ea010ffc8750087fc43a8043fd21d4021fe10ea010ffc4350017fc21a8043fd10d4005fe086a011bf59650017fec92800bfe649400d7f324a002ff59250005fac92800bfc6494001ffaa4a000ff95250006fca928003fd5494001f
  | 5 => 0x4242007fecaa1002ff6550801ff32a8400bf99542007facaa1002fd6550801fe32a8400bf19542007fea8a101bfe5450801feaa28406ff15142007fec6a1002ff6350801ff31a8400ff58d42007f8c6a1016fc6350801ffa9a8400ff94d42007faa6a1003fc535080dffa1a8400ff90d42007fa86a1003ff5250807ff2928400ff5494201ff8a4a101bff425080df7a128403ff9094201f7c84a105fff615082f7fb0a8417ff9854200dfcc2a105ffd615082f7eb0a8417ff1854200df8c2a105fff515082fbfa8a8417ff945420bffaa2a105f7d515082ffe28a8406ffd05420bf7e82a105ffe415082ffea0a8417ef50542037f882a105fff315082fff18a8417ff4c5420bff862a100fff215082fff10a8417ff4854201ff842a1003ff60508017fb028400ff98142007fac0a1003fc60508057e3028417ffc41420bffc20a105ffd105082ffe0828403ffd944201dfeca2100ffe65108017f3288403ff59442005faca2100ffc65108077e3288406bf99042037fea82101bfe541080dfeaa08406ff1504201ffec62100ffe631080b7f3188403ff58c42005fac62100ffc6310801ffa988400ff94c42007faa621003fc531080dffa188406ff90c42037fa862101bfc43108077f3108403ffd484201ffca42100ffd5210807fe2908403ffd084201f7e842100ffe4210807f72108403ff5084201f7a842101bed4210807ffb088403bfd844201ffcc221006fe6110807feb088416bf5844201ff8c221006fc611082dffa888416dfd44420b7fca22105bfd511082dbea888416ff14442037fe822101bbf411080dff2088406ff504420b77a822101bfc411082dff9888416ff8c4420b7fa622105bfc3110807ff9088403ff8844201ffa422100ffc2110807ffb008403ff98042015fcc02100ffd60108017eb008403ff180420b7fe202105bfe101082dfe8808416ff0404201ffecb1900eff658c807ff32c6400bf9963201ffacb19002fd658c807fe32c6403bf1963201ffec91900eff648c807ff3246406bf9923201ffac919002fd648c807fe3246403bf19232007fea919003fe548c801feaa46400ff152320a5fac719003ff538c80bff29c6400ff54e3202ff8a719003ff438c80bff21c6400ff50e3202ff8871900efe628c807ffa946400fbd4a3201ffca51900ffd528c807fe2946403fb14a3201ffe8519003ef428c807ff2146403ff50a3201ff8851900fec428c807ff9946405fbcca3201ffec31900eff618c807ff30c6401bf9863201ffac319056fd618c807fe30c6401bf186320affea3190577f518c82bff28c6415ff546320aefaa319057fc518c82bffa0c6415efd06320affc8319057fd418c82bdea0c6415ff1063202ffe6319057fe318c82bfe98c6405ff0c63201ffe431900fef218c807ff10c6403ff486320afda4319
  | 6 => 0x57e302a41cffc41520e7fc20a9073fd1054839fe082a41bbf9945201ffec82900ffe641480d7f320a403ff59052005fac82900ffc641481fffaa0a400dfd5052007fca829003fd5414801beaa0a40fff1505201ffec62900ffe631480b7f318a403ff58c52005fac62900ffc631481fffa98a400ff94c52006fca629003fd531481ffe298a400df14c5201dfcc42900fff5214807bfa90a403ff9485201fdca42900ffd5214807bea90a400fb5485201ffec22900eff6114807ff308a401bf9845201ffac22906afd6114807fe308a401bf1845207ffea22906b7f5114835ff288a41aff544520d6faa22903ffc5114835ffa08a41aefd04520d7fc822906bfd4114835dea08a41aff104520d7fe622906bfe3114835fe988a41aff0c45201ffe422900ffe2114835f7108a403ff4845201ff8422900fec2114807ffb00a403ff98052015fcc02900ffd60148017eb00a403ff180520d7fe202906bfe1014835fe880a41aff04052037fecba101aff65d080dff32e8400bf99742036fccba10027e65d080dfeb2e8400bf59742036facba10027d65d080dfe32e8406bf19742037fea9a101bfe54d080dfeaa68406ff15342037fec7a101bfe63d080b7f31e8406ff58f42005fac7a101bfc63d0801ffa9e8400ff94f42007faa7a1003fc53d080dffa1e8400ffd4b4201ffca5a1003fd52d0807fe2968406ffd8742035fec3a101bfe61d08037f30e8406ff587420cdfac3a101bfc61d08037e30e8419ffd47420cefea3a1067fe51d0833fea8e8419df547420cff8a3a101bff41d080ddfa0e8406ff90742037fa83a1067bd41d080dfe20e8419ffcc7420cffc63a1067fd31d0833fe18e8403ffc87420cffc43a1067fd21d0807fe10e8406ffd8342037fcc1a100afe60d080dfeb068400bf58342037f8c1a1067ff10d0833ff0868419ff443420cff821a100fff65908077fb2c8403ff99642005fccb2100ffd65908017eb2c8403ff1964201df8cb2105efd6490801ffaa48406ff95242007faa92101bfc5490807ffb1c8403ff98e4202dfcc72100fde63908016f31c8403ff58e42005fac72100fdd63908016eb1c8403ff18e42007fea721003fe5390801fea9c8400ff14e42037fe8721003fe43908077f3148403ffd4a4201ffca52100ffd5290807fe2948403ffd0a4201f7e852101bef4290807ffb0c8403bfd864201ffcc321006fe6190807feb0c8418bf5864201ff8c321006fc6190831ffa8c8418dfd46420c7fca321063fd5190831bea8c8418ff14642037fe8321063bf4190831ff20c8418ff506420c77a832101bfc4190831ff98c8418ff8c6420c7fa6321063fc3190807ff90c8403ff8864201ffa432100ffc2190807ffb048403ff98242015fcc12100ffd60908017eb048403ff182420c7fe2121063fe1090831fe8848418ff0
  | 7 => 0x2a01bff621500dff310a803bf98854037fac42a002fd621500dfe310a806ffd8454035fec22a01bfe61150037f308a806ff584540f5fac22a01bfc61150037e308a80fffd44540f6fea22a07bfe511503dfea88a81edf5445407ff8a22a01bff411500ddfa08a806ff90454037fa822a07bbd411500dfe208a81effc84540f7fc422a07bfd211503dfe108a806ffd8054037fcc02a00afe601500dfeb00a800bf58054037f8c02a07bff101503dff080a81eff440540f7f8202a03fff64d4801ff326a406bf99352007fac9a9002fd64d481ffe326a40fffd5352007fca9a9003fd54d481ffe2a6a40fffd8f52007fcc7a9016fe63d4801feb1ea400bf58f5207ff8c7a903fff53d481fffb0ea41bbfd87520dffcc3a9006fe61d4837feb0ea41bbf5875207ff8c3a9006fc61d481fffa8ea41bdfd47520dffca3a906ffd51d4837bea8ea40fff147520dffe83a906fbf41d4837ff20ea41bff507520df7a83a906ffc41d4837ff98ea41bff8c7520dffa63a906ffc31d4807ff90ea41bff887520dfdc43a906ffd21d4807fe10ea41bfb0875207ffec1a9003fe60d48057f306a400ff58352005fac1a903ffc60d4837ff886a41bff843520dffa21a906ffc10d48397eb2ca403ffd925201ffcc92901afe6494807feb24a400bf5925201ff8c929003ff5494801bfaa4a400ff95252007faa9290037d5494801fe2a4a403ffd8e5201ffcc729016fe6394807ef31ca400b798e5201ffac729002fd6394807eeb1ca400b758e5201ff8c729003ff5394801ff29ca400df94e5201dfcc52900fff5294807bfa94a400fbd4a5201ffec32900eff6194807ff30ca401bf9865201ffac329076fd6194807fe30ca401bf186520effea3290777f519483bff28ca41dff546520eefaa329077fc519483bffa0ca41defd06520effc8329077fd419483bdea0ca41dff106520effe6329077fe319483bfe98ca41dff0c65201ffe432900ffe2194807fe90ca403ff0865201ffec12900ffe60948057f304a403ff58252005fac12900ffc609483bff884a41dff842520effa2129077fc1094801ffb22a400bfd9152007fcc8a9003fd6454801fe322a406bf19152007fea8a9003fe5454801feaa2a400ff15152007fec6a9002ff6354801ff31aa400ff58d52007f8c6a9016fc6354801ffa9aa400ff94d52007faa6a9003ff5254801f7a92a403ff9495201efca4a9073ff61548397fb0aa41cff9855200dfcc2a9073fd61548397eb0aa41cff1855200df8c2a9073ff5154839bfa8aa41cff945520e7faa2a90737d5154839fe28aa41cffd05520e77e82a9073fe4154839fea0aa41cef505520e7f882a9073ff3154839ff18aa41cff4c5520e7f862a900fff2154839ff10aa41cff4855201ff842a9003ff60548017fb02a400ff98152007fac0a9003fc605480
  | 8 => 0xc03000000c00c00403800002401c02800002800401405805000c02000804800002c01c06801400c00401800001000c08001002404402800000001401c00400400801c0180000080280440180280180280300040140a401403c09c01c02404401400800800002800000400800001809404002405001403800001004800800c01403801000000c00c00400c00000c04c01400400c03001800000400000801c0000040040c40100c400001c02001400007c01c00807c02400c04001000001c09804000001000400400800000802402400000002c00000000800c01001800001800800802c0040040080180180fc0b800400000400804c09c00000001c01000406c00009c00003400805801c01400802002000c02000c01800804008004005400c00c00405006003807c01002000000804402801002000401800803400800402000c0200180040ec06003800802008800000801003800409003001801002000408809400c02c01c12400401801401001c03000c0200000040000000100000481fffb16a800ff98b5401dfcc5aa003fd62d50017eb16a80fff18b5407ffec3aa07eff61d503fff30ea801bf987540fffac3aa07efd61d501ffe30ea801bf1875407ffea3aa07f7f51d503fff28ea81fff547540fefaa3aa03ffc51d500dffa0ea81fefd07540fffc83aa07ffd41d503fdea0ea806ff107540fffe43aa07ffe21d503ffe90ea81fff0875407ffec1aa003fe60d50057f306a800ff58354005fac1aa03ffc60d503fff886a81fff843540fffa21aa07ffc10d50417eb2ca806bf99254037fea92a01b7f5495001dfaa4a800cfd5254037fec52a01bfe62950077f314a806ff58a54005fac52a01bfc629500dffb0ca806bfd8654037fcc32a006fe619500dfeb0ca821bf58654037f8c32a006fc6195043ffa8ca821dfd465410ffca32a087fd5195043bea8ca821ff14654037fe832a01bbf419500dff20ca806ff5065410f7a832a01bfc4195043ff90ca821ff8865410ffa432a087fc219500dffb04a806ff98254015fcc12a01bfd60950017eb04a806ff1825410ffe212a087fe1095043fe884a821ff04254007fea8aa003bf545500dff2a2a806df95154007fec4aa002ff6255001ff312a800ff58954007f8c4aa00efc6255041ffb0aa820bfd8554107fcc2aa006fe6155041feb0aa820bf58554107f8c2aa006fc6155041ffa8aa820dfd4554107fca2aa083fd5155041bea8aa820ff14554037fe82aa083bf4155041ff20aa820ff505541077a82aa01bfc4155041ff90aa820ff88554107fa42aa083fc2155001ffb02a800bfd8154007fcc0aa003fd6055001fe302a802bf18154107fe20aa083fe1055041fe882a820ff041540fdfcca2a01afe641500dffaa0a806dfd5054037fca82a01bbe541500dfeaa0a806df550540077aa8
  | 9 => 0x700010fc002ce900a78bbad782d6a8a0dcb681ae988ad3e9a0002ffdef1e8aeb80011a0f38002511d7ad9ebc0db27813cae6ae0255000057a0a1868002b7f5baa90bf43a1361cd1c9ae4b414eb25c1660001a7bad52c31a4002629c2c002d100025ab6a00021080025f06321ab6190aada56fca393883118ab5f31a0d69148260d29e6b0cb2a8fd03692924c19bb3f9c800020500016f5cb13186a6401fc1d008e2b89579359048c78000050c2022c86cc452e40000038033780020eae51a300008c4002140500002ad3560003340000cd300d0f800331ae98e6000102879a8b827000002401800c01403801800c02800001404c00c0400000000200480cc00000800000c00000000002401c00005800400000000400805003002000004c00c00806802005c00400006803004c05c10800001c0080a000002c05800c01400c00003808c00c00400401000c00807000002000006000400001004400401000000005400001c02002801800401000000000005c00c00400801800001c00002800c01007c01c01c02400000402002803c01c00000009003001000802000000c00002402000c00802c04400809c06804403800400002007c00001817800c00403c00007004005400000800006c02c00001403c0140380000180000000140000000000280080000000180d000800000407801801c01401c04801005c01001c01000800800801401c02800001801401002400801001801800016c0000280000000bc00001c01c00c00c01001801800c01c00007008c0000000300080040180640040080000440e400c00802400c00001400000802403c00801400801401000800800000407800c00400001800407c00000001402401000400806000400000c0040040ec00002400001805400000003c01403000809003c00000c00401003000001007410000002c00000800000400000000c01000c00c00c01402800c01c00001001c00c00000402800400400000000000403400001402803404402400c01000002800c02c00c02c00005004800402800400000401001002000c03000000401800004401400001c0240a400000002800401000404400802001000c01801001408c05002c02400000000000002c0000bc02001400002800003801401c02015c01408401000c06c00000004c00002000802800016008c00000800c02801400c08805c00003401800001000000c0180000140000000000d000000000c00801c01400803808801c02c08001c07004c02400c06c00c04000c00401004404400000400000c00000001005400802800000401802400400400000000005800001000002402406800806c00000000400403401400800c00001000000000008400400005800400801801c0000000ec0400200880080200640600100080040000040000040c000c034
  | 10 => 0xda4992a323919d200036dbaddbdb70131c0016d128b79b44ba1bb41db00015d35d8de3a27806eab6c02359c31db45a6e083a831bf92b1718af1f3addbaab0d2b099452150cc980f59aca8186a9372cc03df2f2f29801d7151c000d558307516f19d8000f7834aca90ea2ba9f8000dda593a340c2b303789f2708002b7b69267363977b908da845830cdc1569424000b0a9794bbb85d05191e30002230fb12808504e5c6b25a7b0000000001700e507e3b9112526ac41fa8ff09923fc00215a68340dd6328a242a68a59715711599751821e22ff670e738d4147aa53af1492ee8cc0af9635b29cffa8973e26373c7322f9ecb0eb752f183bf74b3f31719a2b42748f2b1900675e31521833980a08b2124918a8a879b791e155c778439223062bd0028d7aec8001b5b033078bf1ba9d5c2cf8d9120eaeaba7f29eb772bda76b2a36d00008117080013f9a6ba201a1f8b06b311117a02092c81d140001300000014336400001bfa59b98c3c0000000000026594d12fb2fa213007a78fe22db6b2c13161f4a12c2c93d80011d1e091ab1f2982e29cd9b04e38791d31240e11726170080d3a11dfb1d504b1afc0017330504c82148029400000018e24d07eb470ebceca7d3142e22962a28dbab900ca9668eefd0224870002540001870c94000920576c603ec0014506184527000008f40000036f1da0d9b2c8000000001970001c38760b9037213dad8002462018001e73810fc9fd856b462288000a1f5d5a1008c0003222f0001163a109c7b58001224000601b1582a530699ef8d499420d038821edc84ec0e293732a1eaf6b7d86950a07b8c32a08000947023b4a2580943f800000266815103216800000335ac79434ea8f1b5c31f9e1a3e9b42fb8001be83581397d01c1c29e286b13503e7a0800000000330a7ea268aabab1541dfb912022a220f8f08c568b0dfa761b67610cab2eaf900b26d085a0591118258c9a39f70bba299b500018d93544f6bf0ba90689fad2075ab50fe9890cc4ecd642d58b52d7ad4e450c117474e2c0a2487f810ae8800187aff0178000001e262098fb39400123b8d00009687db1e4000001344000000000aea9337695291c3b9de909a000065932b7c8001819fea4aa93c0000000027525a094ebe2d92719e7ad97675f0a041a2b5b144aef8608000bca9995e949b650000fe6b63406ae28ddb745d0edeee28f13f00000008e51b0001ce80010539658481a8002bb3a82392490000000002341c79378e869880000a903b8336e10b8ed3058550ba1343730002faf0000000000013995701480026ecefae7b6ca870000001eec002b82840d5de4a538fd9720002613070002f4a45ade8000f68cf244ef580016c800000012a9025298e8000620000001c333693e00037800013b00000398087123d293ad98a513303afba84ea3
  | 11 => 0x1984a15c10d45292c8001bc99a925a95847b391f1965a851be15a8e7ba3c512ba3a4a162dd10eca4241c003b2ba2a888ff44d2c312a24f000191c6880000026e5ad1592331b32a422c14d8f303e8c40000001b95c1bb08fa89d87b0001d663194688f3120070ef2b3a23ad51f2c645e000038d55540027b800176edf80000000025012110c995639b102971f780029c800009f8233f45b10931aeb04fb84480029d963cd93aba82abcbb6000358ac49a20000001cf80000000015f8000000002cb80014200028125188426237b94cb4d8a26136ab0e5668b5d38890de640002ca32206a2f62b7485dce120f599b0e561531080000e45774002111d082400022eb8cc75dd1f1f40004f26da6a1d4541e0012e8000000101279b81d1b348000ee00003e0b2e9f354889272b95e220001b60c482992633e9d36a48c91c3c48aa62e73532fef8e99fa7e05940000011f8e6f43b7a9b20000000000d09735488002c726321444689b1ea0b9a9c2218a061188f80014700015d9653b794f32e3a300000038b36637e9934000003679afb9c9d118409300026b00000023285f46eb4c8001765742f426a4001ba00014100000039b1230b10e8b1d213242e6907d202a308bc3361b089c8000002e5a14de40000000b30001f46a1a14a36b498000000001442dab759769545b1a823a51d2400153b1fe05db1f3301e216c280d610f5a3c8b971c3b5b4579872acb3acf66b4ba803968994b0100345024b1995c8868727509b9d2d21560dace2b4b8f9ae0001272720002dc0000002b16c911f37080200011042a8390e0af000021380000000013484c095b0c1b10bbf1e80014e05d5918000ccab9c0009e0000000001150b1800398934d408293b89fcbb3b4a2a58a374eb900541bf08c92500011080001206129b3038b37b22e38d509565e1483130244169b3800215d33df28b4b041101cb8209eb996aa380021c0e2800007aed2b5b3c316b119b2f292dbb882c000014635a01b97bb2500005a65d00031488a36b8002d03a1cb6abaa3c0000690002e617a292df5290bad897bb697625710d8599860002bcf429c48b80bd26aa1d1efc2bd6d800093f15800000396fa2c000001728beacd18fd339e630b0a7b7905f8428199380000d31d3c78371b3d0000b3f2283a76718f42184a9964000000181128a2e423138003a737b00000000018b8a08001020003280001f0d74c000002fe80002eb7625fb7e3afa4a2174e3074c4d8da3048000499f075013a8b780033a30f22c81f0002060bd9ed82fabbb3fe449aa8a10482e828d977346970482ade0d01551f1d75990e0703310bf5aa83aef2383744770f42d3a8600406510b61b02d9d4eed9b7cd59d6c0d05b8341b4e7c233af3264a92a86b3b09092b8060003b5217f98366d7b2a7b26ad8ec502c43d041ad89b8
  | 12 => 0x2ab0ce5ea99853858911aa143b2717ab9519396a952c5e2fb1060e668480038a34104600024e1d6a73295164b60258800000383800072e89ad0a0e02b80020b17fa440570000002df193000b180c51c083b2464000002384b89c61a88002d37488001d41cc8949e50560188508ce0318f50e9faa16eae92fa3ad250994b7d131060ddeb570002302921a408980023e1f40f733ec988001013a40f9b9382f18d2068303522d80dd00030a9602d8568b2623f859f6f8679981fe020c000e9a0306c8e40001ca97eaacb9a238a56a7f8cb367cbe2ae85818c29bac8b41b1c0e1b8f02e35590f00b4000000680001511dd9f6267c0028e5369669c47ac0c3a68c000a717d8e588ec003b99a0b4b0000001ff2fc2228002404f2360a2819ea088e7241455af8ab738bf098998e755602c2f20000000001249a616a206553c171138002408000000e8c8c0d672796ba1f3240002358f885c8ac8ae2fe41ebb8c71b8912eea88000002a3119b95abfb490000003740000d11990ea75792dc40800038000000145a8c3322aab4d00003980023d8e6a6877341ac002582afc6f25e97c94f75417480000026026ba40c00081800206ca638e0bdf52a4f8d231c80af1ee439c5ba394ee661a46da33533e0c619200022a961bb80a1a9568a9cc37fe5db956f13659f69c20ec0861304eb5d399e3920962d1850e9abb12d45ee0e7c0039407082100039c0002479f3000064acd83f006b2b0c36af000338935c00248b02b9a80026f13c2363109b8a73f73892a7a887a4e857d141504031b680034f80000015e00022913238689d1d890e11c98a0aa2c388888d3ac8001f1401058e0816b0c98001c1117990516b852adafa88eaea39f00007a0000000cf8000001791ee9b3c3c6008ea152075572c73b0a32109fc2d35e97f36e9a5b8dc1b2cfb97921a7985861cb5cda0033c7408543d80015ba17adb2c229e24b97c38cadf562d950df368b809b4830958978afa4882494258ed8003ac4000000076c2afcb53ab232180014281c8000ec40012083cc0000004e0a83b30001d561d8202048048470e942201dbb198f00010c554b0b969a6f99c9de351a1900038b48d8001ff8734001bc02380000f3128003b700004fa918269ab96803b9b277a2ccbba3754003110000d700019f1d9b01a6500038280039b8089f000029d1902a714b0f90000000e485e8bec00141a311070401559fb8518000000001d29917999912710c281d0000000003a149a8001834eb8ed7b94003ae800000192c09163afe1dbb8b9f11f90000001ab194c6d90b1e127a2808002ec0000002121909f3c721f21f24a9b0e11e8002b2a7402b62a0b239f863780e85822ac9b6a9337a6a1b89e9b852a9959e340010c00010d0422694000bb000267a4a5d0e3b35808be4447672c0490f61400000002
  | 13 => 0x5fdda9eb027a57893b5900034f15196c33022516084b970c000003a600000028cc00000029e0c02acd1b7c0000d89c519d32008d79e0a22044520661181a2c003684001170000002128b2af94002771bd242b40a60880858a75853a0394c12fd2f60a8002f0a6c3442a834304307f028bba5a9b97173abeb2985a35dc73c9c0231a800031780035f8ca24db7f246b08b569b00aba8c63a0c4e5baaa1f4e3b8be6eb1a18161cf03c007c0e995c8cef986b94fc3d4d6d75c2b0b41d5ac1a413712e41ed32307451b9200000a00000748531632599c9392878a968c8a07a2d32da94ae188483c8000c080013e8c01926f721fa990a498b0000000000003a92891c70b628c81592d9a50000000000950003698000000000000000001962279f98672d2982e8e19781427c8593630c586c111e3a9f34000000192352d400035c90796220106d2434002c58001dc80014e9882ff92f0000003842f807cae0b5e7ae0b719b000130c099af1e2ca6930a1e13b8ee5f589bb1a8d8377a88189b2b823c0db5110e5a91326afb87a0ba27121cada41918b9d30d94f9d4af7b9eb7226aeac150afd8000cb910f1b0ac0350fecceab10b5950c9736203a8e91e9b338002a003291315b38aa09942c0028d34799885d95f193c5c152406de81300a31a7000033a0f0001581b911d82a00b87ab7fb993a989878c2d31059b70001839b5c001fa00000000000000026f6f3800175647011b009ec3420412d60001314e00000002455042b1cf00b54a90002201502480000000cd91196e3930000000001e39810000000000001670000002f5374f38234862a4997e28f80000000000005a8c872d00037f5b566988214a8bc5b6c0000022b2b00000b38440bd551509b863248059858001999dc0640fc33c8003373788000ff8003849d2e6e87689030100fa559f80e20c7320ab840039d9d80c19dd0a2a4d50887c0001629e580031e26c80034824b22e25b0fa063a379c37b00f49534ad3728a0ceea1506fa430bccf800008aa9107026ff4c32381a40002505ac831ac2f9f0825c9eab401c00ab38180a70fb3d800204dca28d7090c6983cf1000245d01854b1894a00000008dc0028e8a1794a7d8de93a396115a69c000000002b6b899624e824255a24cac6a792cf2d49c8a6182fce4f72d691e3ed70940002b980033a86069261640006e23f1bb96780026380000016fb4aa056521b34112e13871fd0934002549d9000132d54c0000000027780845f0669229298018ffeb8cbfa1896100021a21001f8001391c400023c9bb1df1a3764b1bb5512e38c6a120ca114000c82e303633bab193d36
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf2098c20016de2098c20016dd2098c20016dc2098c20016df1098c20016de1098c20016dd1098c20016dc1098c20004ff7558c200067f7558c200047f7558c2007cfc7558c200067c7558c200047c7558c20004ff7458c20034fc7458c20014ff7358c20016df7358c2001cff7258c2001cfe7258c2001cfd7258c2001cfc7258c2001ede3258c2001edc3258c20004ff7158c2000cfe7158c20004fd7158c2000cfc7158c200067f5158c200067d5158c20006bf4158c20006bd4158c20006df3158c20006de3158c20006dd3158c20006dc3158c20014ff7058c20014fe7058c20014fd7058c20014fc7058c20016de3058c20016dc3058c20016ef2058c20016ed2058c20006df7558c200065f7558c20006de7558c20006dd7558c20006dc7558c200065c7558c20006df7458c20006de7458c20006dd7458c20006dc7458c20006df5458c20006de5458c20006dd5458c20006dc5458c2001edf7258c2001ede7258c2001edd7258c2001edc7258c2001edf5258c2001ede5258c2001edd5258c2001edc5258c2001edf4258c2001ede4258c2001edd4258c2001edc4258c20006df7158c20006de7158c20006dd7158c20006dc7158c20006df5158c200065f5158c20006de5158c20006dd5158c200065d5158c20006dc5158c20006df4158c200069f4158c20006de4158c20006dd4158c200069d4158c20006dc4158c2001edf2158c2001ede2158c2001edd2158c2001edc2158c20016df7058c20016de7058c20016dd7058c20016dc7058c20016df5058c20016de5058c20016dd5058c20016dc5058c20016df4058c20016de4058c20016dd4058c20016dc4058c20016df2058c20016cf2058c20016de2058c20016dd2058c20016cd2058c20016dc2058c20016df1058c20016de1058c20016dd1058c20016dc1058c2007cff76d4c20014fe76d4c20004fd76d4c20014fc76d4c2002ede63d4c20006dd63d4c2002cff7694c20014fe7694c20004fd7694c20014fc7694c2011e7f6594c2011e7c6594c2002ede6394c20006dd6394c200075f5394c2001dee7294c20005ed7294c20004ff7654c20014fe7654c20004fd7654c20014fc7654c2002ede6354c20006dd6354c2002cff7614c20014fe7614c20004fd7614c20014fc7614c201167f6514c2007e7c6514c2002ede6314c20006dd6314c20034ff76d0c20014fe76d0c20004fd76d0c20014fc76d0c200057e75d0c200057d75d0c2002ede63d0c20006dd63d0c2002cff7690c20014fe7690c20004fd7690c20014fc7690c2002ede6390c20006dd6390c2001dee7290c20005ed7290c20004ff7650c20014fe7650c20004fd7650c20014fc7650c2002ede6350c20006dd6350c2002cff7610c20014fe7610c20004fd7610c20014fc7610c2002ede6310c20006dd6310c20
  | 1 => 0xc120005ed72cc120007cd32cc120004fd764c12001cfc764c1200067f654c1200067c654c120006bf644c120006bc644c120005ef724c12001dec724c120007cd324c120014fe75994200167e7599420034fe7499420004fd749942002cfe7399420004fd739942001cfe729942001cfc729942001e7e529942001e7c529942007cff719942000cfe7199420004fd719942000cfc719942007e7f51994200067d5199420006bf4199420006bd4199420014fe7099420014fc70994200167e50994200167c5099420016ef2099420016ed2099420014ff75594200167f7559420004ff7459420034fc7459420004ff735942002cfc735942001cff725942001cfe725942001cfd725942001cfc725942001e7e525942001e7c5259420004ff715942000cfe7159420004fd715942000cfc71594200067f51594200067d5159420006bf4159420006bd4159420014ff7059420014fe7059420014fd7059420014fc70594200167e50594200167c5059420004ff755902007cfc7559020014ff7459020016bf7459020004ff735902002cfc735902001cff725902001cfe725902001cfd725902001cfc725902001ebe425902001ebc4259020004ff715902000cfe7159020004fd715902000cfc71590200067f51590200067d5159020006bf4159020006bd4159020014ff7059020014fe7059020014fd7059020014fc7059020016be4059020016bc4059020016ef2059020016ed205902007cff76d5020014fe76d5020004fd76d5020014fc76d502007e7e65d50200067d65d5020034ff7695020014fe7695020004fd7695020014fc7695020036be6495020006bd64950200073f5495020004ff7655020014fe7655020004fd7655020014fc76550200067e65550200067d6555020036be6455020006bd6455020034ff7615020014fe7615020004fd7615020014fc761502002edf7598c2002ede7598c2002edd7598c2002edc7598c2002edf7498c2002ede7498c2002edd7498c2002edc7498c20006df5498c20006de5498c20006dd5498c20006dc5498c2001edf7298c2001ede7298c2001edd7298c2001edc7298c2001edf5298c2001ede5298c2001edd5298c2001edc5298c2001edf4298c2001ede4298c2001edd4298c2001edc4298c2002edf7198c2002ede7198c2002edd7198c2002edc7198c20006df5198c200065f5198c20006de5198c20006dd5198c200065d5198c20006dc5198c20006df4198c200069f4198c20006de4198c20006dd4198c200069d4198c20006dc4198c2001edf2198c2001ede2198c2001edd2198c2001edc2198c20016df7098c20016de7098c20016dd7098c20016dc7098c20016df5098c20016de5098c20016dd5098c20016dc5098c20016df4098c20016de4098c20016dd4098c20016dc4098c20016d
  | 2 => 0x1faf7450920007af6450920036ee6450920036ec6450920007ac6450920005ef735092015def715092015ded71509201576f51509201576d5150920157af4150920157ad4150920007eb7050920015ee7050920015ec7050920007e87050920015e8705092001eef605092001feb6050920157ea1050920157e91050920014fe76cc9200067f65cc9200067c65cc920006bf64cc920006bc64cc920006df63cc92002edc63cc92001fce32cc920015fa70cc920005f970cc920005ee768c92001eee768c920005ee758c92001dec758c9200076f658c920006ee658c920006ec658c9200076c658c9200066c658c92001def748c920005ed748c920007af648c92014eee648c92014eec648c920007ac648c920006ac648c92012ded738c92002eee638c92002eec638c92001def718c920145ed718c92013eef618c92013eed618c92013f6f518c92013f6d518c92013faf418c92013fad418c920015ee708c920015ec708c92001eef608c92001feb608c92013fea108c92013fe9108c920014fc764c9200057f754c9200057c754c9200067f654c9200067c654c920006bf644c920006bc644c920006df634c92002edc634c92001fcc324c920005fb704c920015f8704c920014ec764c9200076f754c920005ee754c920005ec754c9200076c754c9200056c754c9200076f654c920006ee654c920006ec654c9200076c654c9200066c654c920005ef744c920005ed744c920007af644c920136ee644c920136ec644c920007ac644c920006ac644c92001def734c92001fcf734c920007cf634c92002eee634c92002eec634c920007cc634c92002ecc634c920007cf534c920007cc534c920007cf434c920007cc434c92012def714c92012ded714c920126ef614c920126ed614c9201276f514c9201276d514c920127af414c920127ad414c920127cf314c920127cd314c920007eb704c920015ee704c920015ec704c920007e8704c92001eef604c92001feb604c920127ea104c920127e9104c92001cfe76d41200067f65d412007e7c65d4120006bf64d4120006bc64d412001dee72d4120005ed72d412007cff7654120004fd765412001cfc76541200067f65541200067c6554120005bf7454120005bc7454120006bf6454120006bc6454120005ef725412001dec7254120017e8205412001cfe76d012001cfc76d01200067f65d01200067c65d0120006bf64d0120036bc64d012001dee72d0120005ed72d0120017e820d0120034ff7650120004fd765012001cfc76501200057f75501200057c75501200067f65501200067c6550120006bf6450120036bc6450120005ef725012001dec725012001cfe76cc12001cfc76cc1200067f65cc1200067c65cc120006bf64cc120006bc64cc120006df63cc12002edc63cc12001dee72c
  | 3 => 0xf64d0d20036bc64d0d2001dee72d0d20005ed72d0d2002cff7690d20004fe7690d20004fd7690d2002cfc7690d200067f6590d200067c6590d20006bf6490d20036bc6490d2001dee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d200067c6550d20006bf6450d20036bc6450d2002cff7610d20004fe7610d20004fd7610d2002cfc7610d200067f6510d200067c6510d20006bf6410d20036bc6410d2001dee7210d20005ed7210d20014fe76d49200067f65d492007e7c65d4920006bf64d4920006bc64d4920015fa70d4920005f970d4920015ee76d4920006ee76d4920014ee76d492001dee75d4920006ef65d49200076f65d49200066f65d4920006ed65d49200076c65d4920005ed74d4920007af64d4920007ac64d4920005ed73d4920006ef63d4920006ed63d4920195ef71d4920195ed71d49200deee61d49200deec61d492019f6f51d492019f6d51d492019faf41d492019fad41d4920015ee70d4920007ea70d4920015ea70d4920007e970d4920015ec70d492001eef60d492001feb60d492019fea10d492019fe910d4920014fc76549200067f65549200067c6554920006bf6454920006bc645492001f6c5254920005fb7054920015f8705492001fe82054920005ee761492001eee7614920195ee751492001f6e7514920006ef65149200076f65149200066f6514920006ed65149200076c6514920005ed7414920007af6414920007ac64149200076f54149200076d5414920005ed7314920006ef6314920006ed63149200076e53149200076c531492001def711492018ded71149200d6ee61149200d6ec611492017f6f511492017f6d511492017faf411492017fad4114920015ee7014920015ec701492001eef601492001feb60149201876e50149201876c501492017fea101492017fe91014920014fe76d0920014fc76d09200057e75d09200057d75d09200067f65d09200067c65d0920006bf64d0920036bc64d0920015fa70d0920005f970d092001fe820d0920005ee769092001eee7690920005ee759092001dec75909200076f65909200076c659092015ded7490920007af6490920036ee6490920036ec6490920007ac6490920036ac649092001fce7390920005ed739092001fcd7390920005cd739092001def7190920175ed71909201676f51909201676d5190920167af4190920167ad4190920015ee7090920015ec709092001eef609092001feb609092016fae409092016fac4090920167ea1090920167e91090920014fc76509200067f65509200067c6550920006bf6450920036bc6450920005fb7050920015f87050920015ec7650920036ec7650920014ec7650920005ee7550920005ec75509200076f65509200076c655092001def7450920
  | 4 => 0x5120004fd76d512007cfc76d51200067f65d512007e7c65d5120006bf64d5120036bc64d5120034ff7695120004fe7695120004fd7695120034fc76951200067f65951200067c6595120006bf6495120036bc64951200073f549512001dee7295120005ed7295120004ff7655120004fe7655120004fd7655120004fc76551200067f65551200067c6555120006bf6455120036bc6455120005ef725512001dec7255120005fb7055120015f87055120034ff7615120004fe7615120004fd7615120034fc76151200067f651512007e7c6515120006bf6415120036bc641512001dee7215120005ed72151200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d2007cfe75d8d20004fd75d8d20034fe74d8d20004fd74d8d2001cfe72d8d20004ff71d8d2000cfe71d8d20004fd71d8d2000cfc71d8d200067f51d8d200067d51d8d20006bf41d8d20006bd41d8d20006de31d8d20006dc31d8d20006ef21d8d20006ed21d8d20014fe70d8d20014fc70d8d20006fa10d8d20006f910d8d200057e7598d200057d7598d200067f6598d200067c6598d20005be7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d200057f7558d200057c7558d200067f6558d200067c6558d20005bf7458d20005bc7458d20006bf6458d20006bc6458d20005f77158d2003df47158d20004ff7558d200067f7558d200047f7558d2007cfc7558d200067c7558d200047c7558d20004ff7458d20006bf7458d20004bf7458d20034fc7458d20006bc7458d20034bc7458d20006ef7258d20004ff7158d20006f77158d20004f77158d2000cfe7158d20004fd7158d2000cfc7158d20006f47158d2000cf47158d200067f5158d200067d5158d20006bf4158d20006bd4158d20006ef2158d20006ed2158d20004ff7058d20006fb7058d20006fa1058d20006f91058d20004fe7618d200067f6518d200067c6518d20006bf6418d20006bc6418d2002ede6318d20006dd6318d2007cff76d4d20004fe76d4d20004fd76d4d2007cfc76d4d200067f65d4d2007e7c65d4d20006bf64d4d20006bc64d4d2002ede63d4d2002cff7694d20004fe7694d20004fd7694d2002cfc7694d200067f6594d200067c6594d20006bf6494d20006bc6494d200075f5394d2001dee7294d20005ed7294d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d200067c6554d20006bf6454d20006bc6454d20005ef7254d2001dec7254d2002cff7614d20004fe7614d20004fd7614d2002cfc7614d200067f6514d2007e7c6514d20006bf6414d20006bc6414d2002ede6314d2001dee7214d20005ed7214d20034ff76d0d20004fe76d0d20004fd76d0d20034fc76d0d200057e75d0d200057d75d0d200067f65d0d200067c65d0d20006b
  | 5 => 0x7ba10d9120007b910d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d912016ebf72d91201b6be72d9120006bd72d91201b6bc72d91201b6be52d91201b6bc52d91201b6be32d91201b6bc32d9120006bf71d9120004bf71d9120006be71d9120006bd71d9120004bd71d9120006bc71d9120006bf51d91200063f51d9120006be51d9120006bd51d91200063d51d9120006bc51d9120006bf31d9120006be31d9120006bd31d9120006bc31d91201b6bf21d9120006be21d9120006bd21d91201b6bc21d91201b6bf70d912016ebe70d9120006bd70d912016ebc70d912016ebe50d912016ebc50d912016ebe30d912016ebc30d91201b6bf20d912016ebe20d912016ebc20d9120006bf10d912016ebe10d9120006bd10d912016ebc10d91200057e75991200057d75991200067f65991200067c6599120006bf64991200057f75591200057c75591200067f65591200067c6559120004ff75591200067f75591200047f755912007cfc75591200067c75591200047c7559120006bf7459120004ff735912002cfc7359120004ff7259120006ef7259120004ff715912000cfe7159120004fd715912000cfc71591200067f51591200067d5159120006bf4159120006bd4159120004ff7059120006fb7059120004fe76191200067f65191200067c6519120036be6419120006bd6419120005be7619120006be7619120004be7619120006bf65191200073f65191200063f6519120006be6519120006bd6519120006bc65191200073c65191200063c6519120007ad7219120005bf7119120005bd7119120006bf6119120006be6119120006bd6119120006bc61191200073f51191200073d5119120007af2119120007ad21191201afbb20191201a7ae20191201a7ac20191201afb82019120007ba1019120007b91019120036bf7519120036be7519120036bd7519120036bc7519120036bf7319120036be7319120036bd7319120036bc7319120036bf7219120036be7219120036bd7219120036ad7219120036bc72191201aebe52191201aebc52191201aebe32191201aebc3219120036bf7119120034bf7119120036be7119120036bd7119120004bd7119120036bc7119120006bf51191200063f5119120006be5119120006bd51191200063d5119120006bc5119120006bf3119120006be3119120006bd3119120006bc31191201aebf2119120006be2119120006bd21191201aebc2119120036bf7019120036be7019120036bd7019120036bc70191201a6be50191201a6bc50191201a6be30191201a6bc30191201aebf20191201a6be2019120006bd20191201a6bc2019120006bf10191201a6be1019120006bd10191201a6bc101912007cff76d5120004fe76d
  | 6 => 0xf719952000cfe7199520004fd719952000cfc719952007e7f51995200067d5199520006bf4199520006bd4199520004fd709952007ef97099520005bf7459520005bc74595200067f7559520004ff7459520006bf7459520004bf7459520034fc7459520006bc7459520034bc7459520004ff735952002cfc7359520004ff7259520006ef7259520004ff715952000cfe7159520004fd715952000cfc71595200067f51595200067d5159520006bf4159520006bd4159520004ff7059520006fb7059520004fe76195200067d651952007e7e7519520034fe7419520004fd741952002cfe7319520004fd731952001cfe721952001cfc721952007cff711952000cfe7119520004fd711952000cfc711952007e7f51195200067e51195200067d511952007e7c5119520006bf4119520006bd4119520014fe7019520014fc70195200057e76195200067e76195200047e76195201876f72195200057f71195200057d71195200067f61195200067e61195200067d61195200067c61195200073f41195200073d41195200076f21195200076d21195201bf7b20195201876e20195201876c20195201bf7820195200077a101952000779101952007e7f74195200067e74195200067d741952007e7c741952007e7f73195200067e73195200067d731952007e7c731952007e7f72195201be7e72195200067d721952007e7c72195201be7e42195201be7c42195201be7e32195201be7c321952007e7f71195200047f71195200067e71195200067d71195200047d711952007e7c71195200067f41195200063f41195200067e41195200067d41195200063d41195200067c41195200067f31195200067e31195200067d31195200067c31195201be7f21195200067e21195200067d21195201be7c211952007e7f70195201867e70195200067d701952007e7c70195201867e40195201867c40195201867e30195201867c30195201be7f20195201867e20195200067d20195201867c20195200067f10195201867e10195200067d10195201867c1019520034fe76d91200067f65d91200067c65d912007cfe75d9120004fd75d912002cfe73d9120004fd73d912001cfe72d912001cfc72d9120004ff71d912000cfe71d9120004fd71d912000cfc71d91200067f51d91200067d51d9120006bf41d9120006be41d9120006bd41d9120006bc41d9120014fe70d9120014fc70d9120034be76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d912016faf72d9120005bf71d9120005bd71d9120006bf61d9120006be61d9120006bd61d9120006bc61d91200073f51d91200073d51d9120007af21d9120007ad21d91201b7bb20d912016fae20d912016fac20d91201b7b820d9120
  | 7 => 0x4e2002cff7614e20014fe7614e20004fd7614e2007e7e6514e200067d6514e2002ede6314e20006dd6314e20034ff76d0e20014fe76d0e20004fd76d0e20014fc76d0e200057e75d0e200057d75d0e2002cff7690e20014fe7690e20004fd7690e2002ede6390e20006dd6390e2001dee7290e20005ed7290e20004ff7650e20014fe7650e20004fd7650e20014fc7650e2002ede6350e20006dd6350e2002cff7610e20014fe7610e20004fd7610e2007e7e65d4a200067d65d4a2001f6e52d4a20015fa70d4a20005f970d4a200067e6554a200067d6554a20005fb7054a20015f87054a200057e75d0a200057d75d0a20036be64d0a20006bd64d0a20015fa70d0a20005f970d0a20034ff7650a20036be6450a20006bd6450a20005fb7050a20015f87050a2002ede63cca20006dd63cca20015fa70cca20005f970cca2002cff764ca200057f754ca200057c754ca2002ede634ca20006dd634ca2001fcc324ca20005fb704ca20015f8704ca20005de73d9520005dd73d9520034fe74d9520004fd74d952002cfe73d9520006de73d952002cde73d9520004fd73d9520006dd73d9520004dd73d9520006ed72d9520004ff71d952000cfe71d9520004fd71d952000cfc71d95200067f51d95200067e51d95200067d51d95200067c51d9520006bf41d9520006bd41d95200075e73d95200075d73d95200076d72d95200057f71d95200057d71d95200067f61d95200067e61d95200067d61d95200067c61d95200073f41d95200073d41d95200076f21d95200076d21d95201cf7b20d95201c76e20d95201c76c20d95201cf7820d95200077a10d95200077910d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200065e73d95200067d73d95200065d73d95200067c73d95201c67f72d95201ce7e72d95200067d72d95200066d72d95201ce7c72d95201ce7e42d95201ce7c42d95201ce7e32d95201ce7c32d95200067f71d95200047f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200063f41d95200067e41d95200067d41d95200063d41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95201ce7f21d95200067e21d95200067d21d95201ce7c21d95201ce7f70d95201c67e70d95200067d70d95201c67c70d95201c67e40d95201c67c40d95201c67e30d95201c67c30d95201ce7f20d95201c67e20d95201c67c20d95200067f10d95201c67e10d95200067d10d95201c67c10d95200067f6599520005be7499520005bd749952007cfe75995200047e7599520034fe749952007ebe7499520034be7499520004fd749952007ebd7499520004bd749952002cfe7399520004fd7399520004fd729952007eed729952007cf
  | 8 => 0x5ee754cb20005ec754cb200076c754cb200056c754cb20006ee654cb2001eec654cb20005ef744cb20005ed744cb20136ee644cb2001eec644cb2001fcf734cb2001fcf634cb2002eee634cb2001eec634cb2001fcc634cb2001ecc634cb20007cf534cb20007cc534cb20007cf434cb20007cc434cb201ddef714cb201dded714cb2001eef614cb201d6ed614cb201d76f514cb201d76d514cb201d7af414cb201d7ad414cb201d7cf314cb201d7cd314cb20015ee704cb20015ec704cb2007e7e65d43200067d65d432001dee72d4320005ed72d43200067e65543200067d6554320005bf7454320005bc7454320005ef725432001dec7254320036be64d0320006bd64d032001dee72d0320005ed72d0320034ff76503200057f75503200057c7550320036be6450320006bd6450320005ef725032001dec725032001dee72cc320005ed72cc320007cd32cc3200167e7599620034fe7499620004fd749962002cfe7399620004fd739962007cff719962000cfe7199620004fd719962000cfc719962007e7f51996200067d5199620006bf4199620006bd4199620014fe70996200167e50996200167c5099620016ef2099620016ed20996200167f7559620004ff7459620034fc7459620004ff735962002cfc7359620004ff715962000cfe7159620004fd715962000cfc71596200067f51596200067d5159620006bf4159620006bd4159620014fc70596200167e50596200167c5059620004ff755922007cfc7559220016bf7459220004ff735922002cfc7359220004ff715922000cfe7159220004fd715922000cfc71592200067f51592200067d5159220006bf4159220006bd4159220014fc7059220016be4059220016bc4059220016ef2059220016ed205922007cff76d5220014fe76d5220004fd76d5220014fc76d522007e7e65d52200067d65d5220034ff7695220014fe7695220004fd7695220014fc76952200073f5495220004ff7655220014fe7655220004fd7655220014fc76552200067e65552200067d6555220005fb7055220015f87055220034ff7615220014fe7615220004fd7615220014fc7615220004ff7558e2007cfc7558e20004ff7458e20034fc7458e20016df7358e20004ff7158e2000cfe7158e20004fd7158e2000cfc7158e200067f5158e200067d5158e20006bf4158e20006bd4158e20006df3158e20006dd3158e20014fc7058e20016de3058e20016dc3058e20016ef2058e20016ed2058e20016fa1058e20006f91058e2007cff76d4e20014fe76d4e20004fd76d4e20014fc76d4e2002ede63d4e20006dd63d4e2002cff7694e20014fe7694e20004fd7694e200067e6594e200067d6594e200075f5394e2001dee7294e20005ed7294e20004ff7654e20014fe7654e20004fd7654e20014fc765
  | 9 => 0xc7359320014fc725932001ebe425932001ebc4259320004ff715932000cfe7159320004fd715932000cfc71593200067f51593200067d5159320006bf4159320006bd415932007cff76d532001cfe76d5320004fd76d532001cfc76d532021e7f65d532007e7c65d5320036be64d5320006bd64d532001dec72d532021f6c52d5320034ff769532001cfe7695320004fd769532001cfc76953200067e65953200067d65953200073f549532001dee7295320005ed7295320004ff765532001cfe7655320004fd765532001cfc76553202167f65553202167c6555320005ef725532001dec72553202176c5255320034ff761532001cfe7615320004fd761532001cfc761532007e7e65153200067d6515320036be6415320006bd641532001dee7215320005ed7215320004ff7558f2007cfc7558f20004ff7458f20034fc7458f2001edf7358f20014fc7258f2001eec5258f2001ede3258f2001edc3258f20004ff7158f2000cfe7158f20004fd7158f2000cfc7158f200067f5158f200067d5158f20006bf4158f20006bd4158f20006df3158f20006dd3158f2001eef2158f20006ed2158f2007cff76d4f2001cfe76d4f20004fd76d4f2002ede63d4f20006dd63d4f2001dec72d4f2002cff7694f2001cfe7694f20004fd7694f2001cfc7694f200067e6594f200067d6594f200075f5394f2001dee7294f20005ed7294f2020f6c5294f20004ff7654f20004fd7654f2001cfc7654f20005ef7254f2001dec7254f2002cff7614f2001cfe7614f20004fd7614f2001cfc7614f2007e7e6514f200067d6514f2002ede6314f20006dd6314f2001dee7214f20005ed7214f202076c5214f20034ff76d0f2001cfe76d0f20004fd76d0f200057e75d0f200057d75d0f2002ede63d0f20006dd63d0f2001dee72d0f20005ed72d0f2002cff7690f2001cfe7690f20004fd7690f2001cfc7690f20036be6490f20006bd6490f2001dee7290f20005ed7290f20004ff7650f20004fd7650f2001cfc7650f2001dee7250f2002cff7610f2001cfe7610f20004fd7610f2001cfc7610f20036be6410f20006bd6410f2002ede6310f20006dd6310f2001dee7210f20005ed7210f2001ded76d4b20006ed76d4b2001f6e75d4b2001eef65d4b20006ed65d4b20005ed74d4b20005ed73d4b20006ed63d4b201fdef71d4b201fded71d4b200deee61d4b2001eec61d4b201f76f51d4b201f76d51d4b201f7af41d4b201f7ad41d4b20015ee70d4b20015ec70d4b2001def7650b20006ef7650b20005ee7550b20005ec7550b2001faf7450b20036ee6450b2001eec6450b20005ef7350b201edef7150b201eded7150b201e76f5150b201e76d5150b201e7af4150b201e7ad4150b20015ee7050b20015ec7050b2001def764cb20006ef764cb200076f754cb20
  | 10 => 0x48400067d6514840035bc74148400073f5414840006de6314840006dd631484001eee6214840006ed62148400d6f66114840035bd76908401aebd7690840005be75908401adbc75908400373e65908400373d6590840235be73908401af9e73908400059e73908401af9d73908400379e63908400379d6390840035be7290840037ae7290840036bf6290840037ae62908401aebd6290840037ad6290840006ad62908401adbf719084022dbd7190840036bf6190840037b66190840226bd6190840037b561908402273f51908402273d519084016dbf709084016dbd709084016ebe6090840037ba609084016faf209084001cff768c840014fe768c840004fd768c8400067e658c8400067d658c840035be748c840005bd748c84002ede638c840006dd638c84001eee628c840006ed628c8401afac428c8400aef6618c840004ff764c840004fd764c840014fc764c8400057f754c8400057c754c8400067e654c8400067d654c840005bf744c840035bc744c84001eee624c840006ed624c840137ac424c8400a6f6614c84001cff760c840014fe760c840004fd760c8400067e650c8400067d650c8401adbf740c840035bc740c84001eee620c840006ed620c840007cd320c84009ef6610c840006f77558440006f67558440006767558440006f57558440006757558440006f47558440036f77458440036f67458440036b67458440036f57458440056b57458440036f47458440036f75458440006b75458440036f65458440036f55458440036f45458440036b45458440006f77258440006f67258440006f57258440006f47258440006f75258440006f65258440006f55258440006f45258440036f74258440036f64258440006b64258440036f54258440036f44258440036b44258440006f63258440006f53258440006f43258440016f77058440016f67058440016f57058440016f47058440016f75058440016f65058440016f55058440016f45058440016f74058440016b74058440016f64058440016f54058440016b54058440016f44058440016f72058440016f62058440016f52058440016f4205844001e7e7599720034fe7499720004fd749972002cfe7399720004fd7399720014fe729972001e7e529972001e7c529972001eee329972007cff719972000cfe7199720004fd719972000cfc719972007e7f51997200067d5199720006bf4199720006bd419972001e7f7559720004ff7459720034fc7459720004ff735972002cfc7359720014fc725972001eec7259720014ec725972001e7e525972001e7c525972001eec5259720004ff715972000cfe7159720004fd715972000cfc71597200067f51597200067d5159720006bf4159720006bd4159720004ff755932007cfc755932001ebf7459320004ff735932002cf
  | 11 => 0x1eed739884001eec7398840036ef4398840036ee4398840036ed4398840036ec439884001eef719884001eee719884001eed719884001eec7198840006ef51988400066f5198840006ee5198840006ed51988400066d5198840006ec5198840036ef4198840036af4198840036ee4198840036ed4198840006ad4198840036ec4198840006ef3198840006ee3198840006ed3198840006ec3198840016ef7098840016ee7098840016ed7098840016ec7098840016ef5098840016ee5098840016ed5098840016ec5098840016ef4098840016ee4098840016ed4098840016ec4098840016ef3098840016ee3098840016ed3098840016ec3098840016ef1098840016ee1098840016ed1098840016ec1098840004ff755884007cfc7558840004ff735884002cfc7358840016ef7258840036ef4258840036bc4258840036ec4258840004ff715884000cfe7158840004fd715884000cfc71588400067f51588400067d5158840036bf4158840006bd4158840006ef2158840006ee2158840006ed2158840006ec2158840016ee2058840016ec2058840006ef7558840006ee7558840006ed7558840006ec7558840036ef7458840036ee7458840036ec7458840036ef5458840036ee5458840036ed5458840036ec5458840006ef7358840006ee7358840006ed7358840006ec7358840036ef4358840036ee4358840036ed4358840036ec4358840006ef7158840006ee7158840006ed7158840006ec7158840006ef51588400066f5158840006ee5158840006ed51588400066d5158840006ec5158840036ef4158840036af4158840036ee4158840036ed4158840006ad4158840036ec4158840006ef3158840006ee3158840006ed3158840006ec3158840016ef7058840016ee7058840016ec7058840016ef5058840016ee5058840016ed5058840016ec5058840016ef4058840016ee4058840016ed4058840016ec4058840016ef3058840016ee3058840016ed3058840016ec3058840016ef1058840016ee1058840016ed1058840016ec105884007cff76d4840014fe76d4840004fd76d484007e7e65d48400067d65d4840035be74d4840005bd74d4840006de63d4840006dd63d484001eee62d4840006ed62d48400def661d484001cff7694840014fe7694840004fd76948400067e65948400067d6594840035be7494840005bd74948400073f5494840005de7394840005dd7394840006de6394840006dd639484001eee6294840006ed62948400eef66194840015fa7094840005f97094840004ff7654840004fd7654840014fc76548400067e65548400067d6554840005bf7454840035bc7454840006de6354840006dd635484001eee6254840006ed62548400e6f6615484001cff7614840014fe7614840004fd761484007e7e651
  | 12 => 0xd729944007cff719944000cfe7199440004fd719944000cfc719944007e7f51994400067e51994400067d519944007e7c5199440036bf4199440006bd4199440014fe7099440014fc70994400167e50994400167c50994400367f74994400367e74994400367d74994400367c749944007e7f72994400067e72994400067d729944007e7c72994400367f42994400367e42994400367d42994400367c429944007e7f71994400047f71994400067e71994400067d71994400047d719944007e7c71994400367f41994400363f41994400367e41994400367d41994400063d41994400367c41994400067f21994400067e21994400067d21994400067c21994400167f70994400167e70994400167d70994400167c70994400167f40994400167e40994400167d40994400167c40994400167f20994400167e20994400167d20994400167c20994400167f10994400167e10994400167d10994400167c1099440014ff75594400167f7559440034ff7459440034fe7459440034fd7459440034fc7459440036bc7459440034bc74594400367e54594400367c5459440036bc5459440004ff725944001cfc7259440004ff715944000cfe7159440004fd715944000cfc71594400067f51594400067e51594400067d51594400067c5159440036bf4159440006bd4159440014fe7059440014fc70594400167e50594400167c50594400367f74594400367e74594400367d74594400367c74594400363c74594400067f72594400067e72594400067d72594400067c72594400367f42594400367e42594400367d42594400367c42594400067f71594400047f71594400067e71594400067d71594400047d71594400067c71594400367f41594400363f41594400367e41594400367d41594400063d41594400367c41594400067f21594400067e21594400067d21594400067c21594400167f70594400167e70594400167d70594400167c70594400167f40594400167e40594400167d40594400167c40594400167f20594400167e20594400167d20594400167c20594400167f10594400167e10594400167d10594400167c1059440035bd76d5040006bd76d5040035be75d50400373e75d5040036bf65d50400373e65d5040006bd65d50400373d65d50400063d65d50401adbe72d5040037ae62d5040037ad62d504024dbf71d504024dbd71d5040036bf61d5040037b661d5040246bd61d5040037b561d50402473f51d50402473d51d504023dbf70d504023dbd70d504023ebe60d5040037ba60d504023f3f50d504023f3d50d504001eef759884001eee759884001eed759884001eec759884001eef749884001eee749884001eed749884001eec7498840036ef5498840036ee5498840036ed5498840036ec549884001eef739884001eee7398840
  | 13 => 0x95402573c401954025f78401954007e7f741954025e7e74195400067d741954007e7c741954007e7f72195400067e72195400067d721954007e7c721954025e7f421954025e7c421954007e7f71195400047f71195400067e71195400067d71195400047d711954007e7c711954025e7f41195400063f41195400067e41195400067d41195400063d411954025e7c41195400067f21195400067e21195400067d21195400067c211954007e7f70195402567e70195400067d701954007e7c701954025e7f40195402567e40195402563e40195400067d40195402567c40195402563c40195402567e20195402567c20195400067f10195402567e10195400067d10195402567c1019540014fe76d51400067f65d514007e7c65d51400373e54d5140015fa70d5140005f970d5140014fc76551400067f65551400067c6555140005fb7055140015f870551400067f65d89400067c65d894007cfe75d8940004fd75d894002cfe73d8940004fd73d8940004ff71d894000cfe71d8940004fd71d894000cfc71d89400067f51d89400067d51d8940006bf41d8940006bd41d8940006ee21d8940006ec21d89400057e75989400057d75989400067f65989400067c659894016ebf6498940005de7398940005dd7398940006ef62989400057f75589400057c75589400067f65589400067c65589400067f65189400067c65189401a6bf641894001eee6218940006ed6218940004fe76d4940004fd76d494007cfc76d49400067f65d494007e7c65d4940004fe7694940004fd769494001cfc76949400067f65949400067c6594940005de7394940005dd7394940004ff7654940004fe7654940004fc76549400067f65549400067c6554940004fe7614940004fd761494001cfc76149400067f651494007e7c6514940035be7414940005bd7414940014fe76909400067f65909400067c6590940005de7390940005dd7390940006ef629094001eec6290940015fa7090940005f97090940014fc76509400067f65509400067c6550940006ef625094001eec6250940005fb7050940015f87050940004fe768c940004fd768c94001cfc768c9400067f658c9400067c658c940006ef628c94001eec628c940004ff764c940004fe764c940004fc764c9400057f754c9400057c754c9400067f654c9400067c654c940006ef624c94001eec624c940004fe760c940004fd760c94001cfc760c9400067f650c9400067c650c940007cd320c940034fe76d41400067f65d414007e7c65d4140035be74d4140005bd74d41400177a50d414007cff7654140004fd7654140034fc76541400067f65541400067c6554140005bf7454140035bc7454140014fe75994400167e7599440034fe7499440034fc74994400367e54994400367c549944001cfe7299440004f
  | 14 => 0x15f87050a401a5bd7610a40036bd7610a40005be7510a40035bc7510a40285be7310a40037ae7210a401a6bf6210a401b6bd6210a40035bf7110a4027dbd7110a401a6bf6110a40276bd6110a402773f5110a402773d5110a40035bf7010a401a5bd7010a40037ba6010a4001cff768ca40014fe768ca40004fd768ca40035be748ca40005bd748ca4001eee628ca40006ed628ca401b7ac428ca40004ff764ca40004fd764ca40014fc764ca400057f754ca400057c754ca40005bf744ca40035bc744ca4001eee624ca40006ed624ca40007ac424ca4001cff760ca40014fe760ca40004fd760ca401b5bf740ca40035bc740ca40007cd320ca4001cfe72d9540004fd72d9540004ff71d954000cfe71d9540004fd71d954000cfc71d95400067f51d95400067e51d95400067d51d95400067c51d9540006bf41d9540006bd41d95400057f71d95400057d71d95400067f61d95400067e61d95400067d61d95400067c61d95400073f41d95400073d41d954026f7b40d95402673e40d95402673c40d954026f7840d95402667f74d954026e7e74d95400067d74d954026e7c74d95400067f72d95400067e72d95400067d72d95400067c72d954026e7f42d954026e7c42d95400067f71d95400047f71d95400067e71d95400067d71d95400047d71d95400067c71d954026e7f41d95400063f41d95400067e41d95400067d41d95400063d41d954026e7c41d95400067f21d95400067e21d95400067d21d95400067c21d954026e7f70d95402667e70d95400067d70d95402667c70d954026e7f40d95402667e40d95402667c40d95402667e20d95402667c20d95400067f10d95402667e10d95400067d10d95402667c10d95400067f659954007cfe75995400047e7599540004fd749954007ebd749954001cfe7299540004fd729954007cff719954000cfe7199540004fd719954000cfc719954007e7f51995400067d5199540006bf4199540006bd4199540004fd709954007ef9709954023ebe40995400067f7559540004ff7459540006bf7459540004bf7459540004ff725954001cfc7259540004ff715954000cfe7159540004fd715954000cfc71595400067f51595400067d5159540006bf4159540006bd4159540004ff7059540006fb7059540004fe76195400067d651954007e7e7519540034fe7419540034fc741954001cfe7219540004fd721954007cff711954000cfe7119540004fd711954000cfc711954007e7f51195400067e51195400067d511954007e7c5119540006bf4119540006bd4119540256be4019540256bc40195400057e76195400067e76195400047e76195400057f71195400057d71195400067f61195400067e61195400067d61195400067c61195400073f41195400073d411954025f7b40195402573e401
  | 15 => 0xd74d43400067e65543400067d6554340005bf7454340035bc7454340017ba40543400167e759964001cfe7299640004fd729964007cff719964000cfe7199640004fd719964000cfc719964007e7f51996400067d5199640006bf4199640006bd4199640014fe70996400167e50996400167c50996400167f7559640006bf7459640004ff725964001cfc7259640004ff715964000cfe7159640004fd715964000cfc71596400067f51596400067d5159640006bf4159640006bd4159640014fc70596400167e50596400167c505964007e7e65d52400067d65d52400373e54d5240015fa70d5240005f970d524023dbd76d5240006bd76d5240035be75d524023ebf65d524023f3e65d5240006bd65d524023f3d65d52400063d65d52401b5be72d52402b5bf71d52402b5bd71d524023ebf61d52402aebd61d52402af3f51d52402af3d51d524023fba70d524023dbd70d5240007b970d5240005b970d5240036be60d524023f3f50d524023f3d50d52400067e65552400067d65552400373c5455240005fb7055240015f87055240037bb4055240255bd7615240036bd76152400373e7515240256bf65152402573f6515240006bd65152402573c65152401b5be7215240035bf71152402a5bd7115240256bf611524029ebd611524029f3f511524029f3d5115240035bf7015240255bd7015240037ba60152402573e50152402573c5015240004ff7558a400067f7558a400047f7558a4007cfc7558a400067c7558a400047c7558a40004ff7358a4002cfc7358a40016ef7258a40004ff7158a4000cfe7158a40004fd7158a4000cfc7158a400067f5158a400067d5158a40006bf4158a40006bd4158a40006ef2158a40006ed2158a40014fc7058a40016ee2058a40016ec2058a4007cff76d4a40014fe76d4a40004fd76d4a40035be74d4a40005bd74d4a4001eee62d4a40006ed62d4a4001cff7694a40014fe7694a40004fd7694a401c67f6594a401c67c6594a40035be7494a40005bd7494a400073f5494a40005de7394a40005dd7394a40004ff7654a40004fd7654a40014fc7654a40005bf7454a40035bc7454a4001cff7614a40014fe7614a40004fd7614a401867f6514a4007e7c6514a400073f5414a4001eee6214a40006ed6214a40005de7390a40005dd7390a4001eee6290a40006ed6290a40015fa7090a40005f97090a40005be7590a401b5bc7590a40285be7390a401b79e7390a400059e7390a401b79d7390a40035be7290a4016ebf6290a4016fae6290a401b6bd6290a4016fad6290a401b5bf7190a40295bd7190a4016ebf6190a4028ebd6190a4028f3f5190a4028f3d5190a4016fba7090a4016dbd7090a401b7b97090a40036be6090a4016faf2090a4001cff7650a4001eee6250a40006ed6250a40005fb7050a40
  | 16 => 0x485007f6e721485007e7f621485007f6e62148501be7d621485007f6d62148500066d621485007d7f71148502cd7d711485007e7f61148502c67d61148502c73f41148502c73d41148502c76e21148501bf6c211485007d7f701485007f7a70148501857d701485007f7970148501867e601485007f7a60148501876f2014850034ff76d0850014fe76d0850004fd76d085007d7e75d08500057d75d0850036be64d0850006bd64d085001cff7690850014fe7690850004fd769085007d7e75908500057d7590850005de7390850005dd739085001eee6290850006ed6290850015fa7090850005f97090850004ff7650850004fd7650850014fc76508500057f755085007d7c7550850036be6450850006bd645085001eee6250850006ed625085001cff7610850014fe7610850004fd76108501bd7f751085007d7c751085001cff768c850014fe768c850004fd768c85007d7e758c8500057d758c85001eee628c850006ed628c8501bf6c528c850004ff764c850004fd764c850014fc764c8500057f754c85007d7c754c85001eee624c850006ed624c8500076c524c85001cff760c850014fe760c850004fd760c8501bd7f750c85007d7c750c850007cd320c850015fb7654050006fb7654050004fb7654050015fb75540500177b755405007efa65540500177a6554050007bb7454050007b874540502bfbb41540502bfb941540500367e7599740014fe74997400367e54997400367c549974001cfe7299740004fd729974007cff719974000cfe7199740004fd719974000cfc719974007e7f51997400067d5199740036bf4199740006bd419974023ebe4099740036bc40997400367f7559740014fc74597400367e54597400367c5459740004ff725974001cfc7259740004ff715974000cfe7159740004fd715974000cfc71597400067f51597400067d5159740036bf4159740006bd4159740004ff7558b4007cfc7558b40014fc7458b40004ff7358b4002cfc7358b40036ef7258b40036ef4258b40036ec4258b40004ff7158b4000cfe7158b40004fd7158b4000cfc7158b400067f5158b400067d5158b40036bf4158b40006bd4158b4007cff76d4b40034fe76d4b40004fd76d4b4001cff7694b40034fe7694b40004fd7694b400067e6594b400067d6594b40005de7394b40005dd7394b40015fa7094b40005f97094b40004ff7654b40004fd7654b40034fc7654b4001cff7614b40034fe7614b40004fd7614b4007e7e6514b400067d6514b40035be7414b40005bd7414b4001cff768cb40034fe768cb40004fd768cb4001eec628cb40004ff764cb40004fd764cb40034fc764cb400057f754cb400057c754cb4001cff760cb40034fe760cb40004fd760cb40007cd320cb4007e7e65d43400067d65d4340035be74d4340005b
  | 17 => 0x57e75d09500057d75d0950006bf64d0950036bc64d0950004fe7690950004fd769095001cfc7690950006bf6490950036bc6490950005de7390950005dd7390950004ff7650950004fe7650950004fc7650950006bf6450950036bc6450950004fe7610950004fd761095001cfc76109500057e75109500057d7510950006bf6410950036bc6410950004fe768c950004fd768c95001cfc768c950006bf648c950006bc648c950006ef628c95001eec628c950004ff764c950004fe764c950004fc764c9500057f754c9500057c754c950006bf644c950006bc644c950006ef624c95001eec624c950004fe760c950004fd760c95001cfc760c950006bf640c950006bc640c950007cd320c9500157e75d41500167f65d4150006bf64d4150006bc64d4150014fa76d4150015fa75d4150016fb65d41500177b65d4150007bb64d4150007b864d415007f7b54d41500077954d415007f7b51d41503277951d4150327bb41d4150327b941d4150016bf745905007ebf545905007ebc5459050004ff725905001cfc7259050004ff715905000cfe7159050004fd715905000cfc71590500067f51590500067d5159050006bf4159050006bd41590500167f50590500167d5059050016be4059050016bc4059050004fd769505007f3f54950502657d769505025e7d76950500047d769505007d7e74950502667f649505025e7d64950501bd7e729505025d7f719505031d7d71950502667f61950503167d619505025f3f41950503173d41950502657f70950502657d70950502667e60950502677a6095050004ff765505030e7e655505007f3c54550502657e741505007f3e741505007e7f641505007f3e641505025e7d641505007f3d64150501bd7e721505007d7f71150503057d711505007e7f61150502fe7d611505025f3f41150502ff3d411505007d7f701505007f7a70150502557d701505007f7970150502567e601505007f7a60150502573c4015050004ff7458850034fc7458850004ff735885002cfc7358850016ef725885007eef525885007eec5258850004ff715885000cfe7158850004fd715885000cfc71588500067f51588500067d5158850006bf4158850006bd4158850006ef2158850006ed2158850016ee2058850016ec2058850004fd7694850005de7394850005dd739485007f6f52948501c57d76948501be7d769485025d7e74948500067d64948502dd7e73948501bf5e73948500055e73948501bf5d73948502f67e639485007d7e72948501c67f62948501be7d62948501bd7f71948502ed7d71948501c67f61948502e67d61948502e73f41948502e73d41948501c57f70948501c57d70948501c67e60948501c77a6094850004ff765485025d7e74148500067d64148502dd7e73148502d67e63148501c57e721
  | 18 => 0xe10d9150006bd10d915023ebc10d91502667f6599150006bf64991502567f6519150036be6419150006bd6419150005be7619150006be76191500073d7519150005bf7119150005bd7119150006bf6119150006be6119150006bd6119150006bc61191500073f51191500073d51191502573e50191502573c5019150036bf7519150036bf7219150036be7219150036bd7219150036bc7219150036bf7119150034bf7119150036be7119150036bd7119150004bd7119150036bc7119150006bf51191500063f5119150006be5119150006bd51191500063d5119150006bc5119150006bf2119150006be2119150006bd2119150006bc2119150036bf7019150036be7019150036bd7019150036bc7019150256be50191502563e5019150006bd5019150256bc50191502563c5019150256be2019150256bc2019150006bf1019150256be1019150006bd1019150256bc1019150004fe76d5150036bc64d51500057e76d51500067e76d51500047e76d51500073f64d51500367e64d51500367c64d51500073c64d51500363c64d515021e7c62d515032d7f71d515032d7d71d51503467f61d51503467d61d51503473f41d51503473d41d51500157e70d51500157c70d515007e7f60d5150014fe769515033d7d7595150006bf6495150036bc64951500073f5495150015fa7095150005f97095150014fc7655150006bf6455150036bc6455150005fb7055150015f870551500147c76551500073f74551500073f64551500367e64551500367c64551500073c64551500363c64551502167c625515033d7f715515033d7d71551503367f61551503367d61551503373f41551503373d41551500077b70551500157e70551500157c7055150007787055150004fe761515032d7e7515150006bf6415150036bc6415150006bf64d8950006bc64d8950034fe74d8950004fd74d895002cfe73d8950004fd73d8950004ff71d895000cfe71d8950004fd71d895000cfc71d89500067f51d89500067d51d8950006bf41d8950006bd41d8950006ee21d8950006ec21d89501c67f6598950005be7498950005bd7498950006bf6498950006bc6498950005de7398950005dd7398950006ef6298950005bf7458950005bc7458950006bf6458950006bc64589501867f6518950006bf6418950006bc641895001eee6218950006ed6218950004fe76d4950006bf64d4950006bc64d4950014fe7694950006bf6494950006bc6494950005de7394950005dd7394950006ef629495001eec6294950015fa7094950005f97094950014fc7654950006bf6454950006bc6454950006ef625495001eec6254950005fb7054950015f87054950004fe7614950006bf6414950006bc641495001eee62149500076d5214950004fe76d0950004fd76d0950034fc76d0950
  | 19 => 0x4a5036e7d6194a5036f3f4194a5036f3d4194a501c77a7094a501c57d7094a501cf797094a5001cff7654a50006de6354a50006dd6354a5001eee6254a50006ed6254a50005fb7054a50015f87054a50006de6314a50006dd6314a5001eee6214a50006ed6214a501857d7614a501ce7d7614a5026d7e7414a500067d6414a503657e7314a502d67e6314a501875e6314a500065e6314a501875d6314a501cf6e7214a501867f6214a501876e6214a501ce7d6214a501876d6214a500066d6214a501cd7f7114a5035d7d7114a501867f6114a503567d6114a503573f4114a503573d4114a503576e2114a501cf6c2114a501857f7014a501857d7014a501876f2014a50034ff76d0a50014fe76d0a50004fd76d0a500057e75d0a500057d75d0a50006de63d0a50006dd63d0a5001eee62d0a50006ed62d0a5001cff7690a50014fe7690a50004fd7690a500057e7590a500057d7590a50005de7390a50005dd7390a50006de6390a50006dd6390a5001eee6290a50006ed6290a50004ff7650a50004fd7650a50014fc7650a500057f7550a500057c7550a50006de6350a50006dd6350a5001eee6250a50006ed6250a5001cff7610a50014fe7610a50004fd7610a501cd7f7510a501cd7c7510a50006de6310a50006dd6310a5001eee6210a50006ed6210a5001cff768ca50014fe768ca50004fd768ca500057e758ca500057d758ca5002ede638ca50006dd638ca5001eee628ca50006ed628ca501cf6c528ca50004ff764ca50004fd764ca50014fc764ca500057f754ca500057c754ca5001eee624ca50006ed624ca500076c524ca5001cff760ca50014fe760ca50004fd760ca501cd7f750ca501cd7c750ca5001eee620ca50006ed620ca50007cd320ca50015f976d425007ef976d42500177a75d425007f7b54d42500077954d425007f7b53d42500077953d4250017ea62d4250017e962d425034fbb41d425034fb941d425001cfe72d9150004fd72d9150004ff71d915000cfe71d9150004fd71d915000cfc71d91500067f51d91500067d51d9150006bf41d9150006be41d9150006bd41d9150006bc41d915023f3f75d9150005bf71d9150005bd71d9150006bf61d9150006be61d9150006bd61d9150006bc61d91500073f51d91500073d51d915023f3e50d915023f3c50d915023ebf75d9150006bf72d9150006be72d9150006bd72d9150006bc72d9150006bf71d9150004bf71d9150006be71d9150006bd71d9150004bd71d9150006bc71d9150006bf51d91500063f51d9150006be51d9150006bd51d91500063d51d9150006bc51d9150006bf21d9150006be21d9150006bd21d9150006bc21d9150006bf70d915023ebe70d9150006bd70d915023ebe50d915023ebc50d915023ebe20d915023ebc20d9150006bf10d915023eb
  | 20 => 0x26e7d761525026f3e74152502567f64152502573f641525026e7d64152502573c64152501cd7e72152502576e62152502576d621525026d7f71152503857d71152502567f611525037e7d611525026f3f411525037f3d41152502557f70152502557d70152502573c401525001eef7598a5001eef7498a5001eee7498a5001eed7498a5001eec7498a50006ef5498a50006ee5498a50006ed5498a50006ec5498a5001eef7398a5001eee7398a5001eed7398a5001eec7398a5001eef7198a5001eee7198a5001eed7198a5001eec7198a50006ef5198a500066f5198a50006ee5198a50006ed5198a500066d5198a50006ec5198a50006ef4198a50006af4198a50006ee4198a50006ed4198a50006ad4198a50006ec4198a50006ef3198a50006ee3198a50006ed3198a50006ec3198a50016ef7098a50016ee7098a50016ed7098a50016ec7098a50016ef5098a50016ee5098a50016ed5098a50016ec5098a50016ef4098a50016ee4098a50016ed4098a50016ec4098a50016ef3098a50016ee3098a50016ed3098a50016ec3098a50016ef1098a50016ee1098a50016ed1098a50016ec1098a50004ff7458a50034fc7458a50004ff7358a5002cfc7358a50016ef7258a50004ff7158a5000cfe7158a50004fd7158a5000cfc7158a500067f5158a500067d5158a50006bf4158a50006bd4158a50006ef2158a50006ee2158a50006ed2158a50006ec2158a50016ee2058a50016ec2058a50006ed7558a50006ef7458a50006ee7458a50006ed7458a50006ec7458a50006ef5458a50006ee5458a50006ed5458a50006ec5458a50006ef7358a50006ee7358a50006ed7358a50006ec7358a50006ef7158a50006ee7158a50006ed7158a50006ec7158a50006ef5158a500066f5158a50006ee5158a50006ed5158a500066d5158a50006ec5158a50006ef4158a50006af4158a50006ee4158a50006ed4158a50006ad4158a50006ec4158a50006ef3158a50006ee3158a50006ed3158a50006ec3158a50016ef7058a50016ee7058a50016ec7058a50016ef5058a50016ee5058a50016ed5058a50016ec5058a50016ef4058a50016ee4058a50016ed4058a50016ec4058a50016ef3058a50016ee3058a50016ed3058a50016ec3058a50016ef1058a50016ee1058a50016ed1058a50016ec1058a50006de63d4a50006dd63d4a5001eee62d4a50005de7394a50005dd7394a50006de6394a50006dd6394a5001eee6294a50006ed6294a500076f5294a50015fa7094a50005f97094a5026d7e7494a500067d6494a503657e7394a501cf5e7394a500055e7394a501cf5d7394a502f67e6394a501c75e6394a500065e6394a501c75d6394a501c67f6294a501c76e6294a501ce7d6294a501c76d6294a501cd7f7194a503757d7194a501c67f619
  | 21 => 0xd3258032006cd3258032004ff715803200cfe7158032004fd715803200cfc71580320067f51580320067d5158032006bf4158032006bd415803201efb705803201efb205803201ef82058032006fa1058032006f910580322667e659935007ebf6499350036bc649935007ebc6459350014fc755935007ebf545935007ebc5459350004ff725935001cfc7259350004ff715935000cfe7159350004fd715935000cfc71593500067f51593500067d5159350006bf4159350006bd41593500147d76d53500367e64d535007f3e64d53500363e64d535007f3d64d53500367c64d535021e7e62d535007d7f71d53503ad7d71d535007e7f61d53503a67d61d53503a73f41d53503a73d41d53500157e70d535007f7a70d535007f7970d53500157c70d535007f3f54953500057f76553500067f765535007f3f74553500367e64553500367c64553502167e625535039d7f715535039d7d715535030e7f615535030e7d615535030f3f415535030f3d41553500157e70553500157c70553501c67e6598b50005de7398b50005dd7398b5007eef6298b5001eec6298b5007eec6258b50014fc7558b50004ff7458b50034fc7458b50004ff7358b5002cfc7358b5007eef5258b5007eec5258b50004ff7158b5000cfe7158b50004fd7158b5000cfc7158b500067f5158b500067d5158b50006bf4158b50006bd4158b50005de7394b50005dd7394b5007f6c5254b50034ff76d0b5007cfe76d0b50004fd76d0b5007d7e75d0b500057d75d0b5001cff7690b5007cfe7690b50004fd7690b50036be6490b50006bd6490b50005de7390b50005dd7390b50015fa7090b50005f97090b50004ff7650b50004fd7650b5007cfc7650b5001cff7610b5007cfe7610b50004fd7610b5007d7e7510b500057d7510b50036be6410b50006bd6410b5001cff768cb5007cfe768cb50004fd768cb5001eec628cb50004ff764cb50004fd764cb5007cfc764cb500057f754cb5007d7c754cb5001cff760cb5007cfe760cb50004fd760cb50007cd320cb50016bf7459250004ff725925001cfc7259250004ff715925000cfe7159250004fd715925000cfc71592500067f51592500067d5159250006bf4159250006bd41592500167f50592500167d5059250016be4059250016bc4059250036be6495250006bd64952500073f5495250015fa7095250005f970952502667f64952502673e649525026e7d64952502673d64952500063d64952501cd7e72952502676e62952502676d629525026d7f71952503957d71952502667f619525038e7d619525026f3f419525038f3d41952502677a70952502657d709525026f797095250005797095250034ff7655250036be6455250006bd6455250005fb7055250015f87055250036bc64152500073d54152502557d7615250
  | 22 => 0x81320057e75981320057d75981320067f65981320067c6598132006fb60981320057f75581320057c75581320067f65581320067c6558132005bf7458132005bc7458132005f771581320a5f471581320067f65181320067c6518132016fa6018132006f9601813201cfe759943201e7e7599432034fe7499432004fd749943201cfe729943201cfc729943201e7e529943201e7c529943201eee329943202eed329943207cff719943200cfe7199432004fd719943200cfc719943207e7f51994320067d5199432006bf4199432006bd4199432014fe7099432004fd709943201cff755943201e7f7559432004ff7459432034fc745943201cfe725943201cfc725943201e7e525943201e7c5259432004ff715943200cfe7159432004fd715943200cfc71594320067f51594320067d5159432006bf4159432006bd4159432004ff7059432014fc7059432004ff755903207cfc755903201cff745903201ebf745903201cfe725903201cfc725903201ebe425903201ebc4259032004ff715903200cfe7159032004fd715903200cfc71590320067f51590320067d5159032006bf4159032006bd4159032004ff7059032014fc705903207cff76d503201cfe76d5032004fd76d503201cfc76d503221e7f65d503207e7c65d5032034ff769503201cfe7695032004fd769503201cfc76950320073f5495032004ff765503201cfe7655032004fd765503201cfc76550322167f65550322167c6555032034ff761503201cfe7615032004fd761503201cfc761503201fcf764c83201dcf764c832006cf764c832007cf754c8320074f754c832007ce754c832007cd754c832007cc754c8320074c754c83201fcf654c83201fce654c832006ce654c83201fcd654c83201fcc654c83201ecc654c832007cf744c832007ce744c832007cd744c832007cc744c83201fcf644c83201fce644c832136ce644c83201fcd644c83201fcc644c83201ecc644c832007cf544c832007ce544c832007cd544c832007cc544c8323bfcf714c8323b7ce714c8323bfcd714c8323b7cc714c83201fcf614c83201ecf614c83201fce614c83201fcd614c8323b6cd614c83201fcc614c8323b7cf514c8323b74f514c8323b7ce514c8323b7cd514c8323b74d514c8323b7cc514c8323b7cf414c8323b78f414c8323b7ce414c8323b7cd414c8323b78d414c8323b7cc414c832007cf704c832007ce704c832007cd704c832007cc704c83201fcf604c83201fce604c83201fcd604c83201fcc604c8323b7cf104c8323b7ce104c8323b7cd104c8323b7cc104c832004ff75580320067f75580320047f755803207cfc75580320067c75580320047c7558032004ff7458032006bf7458032004bf7458032034fc7458032006bc7458032034bc745803201eee325803202ee
  | 23 => 0x2cee76d493201dee75d4932006ef65d49320076f65d4932006ed65d49320076c65d4932135ee74d493202dee73d4932007ce73d493202dce73d4932007cd73d493202dec73d493201eef63d493201fcf63d49323f7cf53d49323fdef71d49323fded71d49320deee61d49320deec61d49324076f51d49324076d51d4932407af41d4932407ad41d4932407cf31d4932407cd31d4932005ed70d493207cff7654932004fd765493202cfc76549320067f65549320067c6554932005df735493202ddc735493201f6c525493201fcc3254932005ee761493201eee76149323fdee751493201f6e7514932006ef65149320076f65149320066f6514932006ed65149320076c6514932135ee74149320076f54149320076d541493201fcf731493202dee731493201dec731493201fcc731493201eef631493201fcf63149323f7cf53149322d76e53149322d76c53149323f7cc53149320074c531493201def71149323eded71149320d6ee61149320d6ec61149323e76f51149323e76d51149323e7af41149323e7ad41149323e7cf31149323e7cd3114932005ed701493202cfe76d093202cfc76d09320057e75d09320057d75d09320067f65d09320067c65d0932006bf64d0932036bc64d093202dde73d0932005dd73d093201fcc32d093202dee76d0932136ee76d093202cee76d0932005ee75d09321376e75d09320056e75d09321376d75d0932135ec75d09320076f65d09320076c65d093201dee74d0932136ef64d0932007af64d0932136ed64d0932137ac64d093202dee73d0932137ce73d093202dce73d0932137cd73d093202dec73d093201eef63d093201fcf63d0932007cf53d0932007cc53d0932137cf43d0932135ef71d09323dded71d09323d76f51d09323d76d51d0932137af41d09323d7ad41d09323d7cf31d09323d7cd31d0932005ed70d0932034ff7650932004fd765093202cfc76509320067f65509320067c6550932006bf6450932036bc6450932005df735093202ddc735093201fcc3250932005ee761093201eee7610932005ee751093201dec75109320076f65109320076c6510932135ee741093201fae7410932136ef6410932136ed641093201fcf731093202dee731093201dec731093201fcc731093201eef631093201fcf6310932007cf5310932007cc5310932137cf4310932137cc431093201def71109323cded71109323c76f51109323c76d5110932137af41109323c7ad41109323c7cf31109323c7cd3110932005ed70109320067f65d81320067c65d813207cfe75d8132004fd75d8132034fe74d8132004fd74d8132006ef52d8132006ec52d8132004ff71d813200cfe71d8132004fd71d813200cfc71d81320067f51d81320067d51d8132006bf41d8132006bd41d8132006ef21d8132006ed21d
  | 24 => 0xd715953200cfc71595320067f51595320067d5159532006bf4159532006bd4159532004ff7059532014fc7059532004fe76195320067d651953207e7e7519532034fe7419532004fd741953207cff711953200cfe7119532004fd711953200cfc711953207e7f51195320067e51195320067d511953207e7c5119532006bf4119532006bd4119532014fe7019532004fd70195320057e76195320067e76195320047e76195322d76f72195322075e32195322d76c32195320057f71195320057d71195320067f61195320067e61195320067d61195320067c61195320073f41195320073d41195320076f21195320076d211953207e7f74195320067e74195320067d741953207e7c741953207e7f72195322067e72195320067d721953207e7c72195322067e42195322067c42195322067e32195320067d32195322067c321953207e7f71195320047f71195320067e71195320067d71195320047d711953207e7c71195320067f41195320063f41195320067e41195320067d41195320063d41195320067c41195322067f21195320067e21195320067d21195322067c211953207e7f70195320067e70195320067d701953207e7c70195322067f20195322067c20195320067f10195320067e10195320067d10195320067c1019532034fe76d91320067f65d91320067c65d913207cfe75d9132004fd75d9132006ed72d9132004ff71d913200cfe71d9132004fd71d913200cfc71d91320067f51d91320067d51d9132006bf41d9132006bd41d9132014fe70d9132004fd70d91320057e75991320057d75991320067f65991320067c6599132006bf64991320a5f67199132005f571991320057f75591320057c75591320067f65591320067c6559132004ff75591320067f75591320047f755913207cfc75591320067c75591320047c7559132006bf7459132004ff7259132006ef7259132004ff715913200cfe7159132004fd715913200cfc71591320067f51591320067d5159132006bf4159132006bd4159132004ff7059132014fc7059132004fe76191320067f65191320067c6519132036be6419132006bd641913207cff76d5132004fe76d5132004fd76d513207cfc76d51320067f65d513207e7c65d513201dee72d5132005ed72d5132034ff7695132004fe7695132004fd7695132034fc76951320067f65951320067c65951320073f549513201dee7295132005ed7295132004ff7655132004fe7655132004fd7655132004fc76551320067f65551320067c6555132005ef725513201dec7255132034ff7615132004fe7615132004fd7615132034fc76151320067f651513207e7c651513202cfe76d49320067f65d493207e7c65d493202dde73d4932005dd73d493201f6e52d493201fcc32d493202dee76d4932006ee76d4932
  | 25 => 0x4e3201dee72d4e32005ed72d4e320067e6554e320067d6554e32005ef7254e3201dec7254e3202fcf3254e320057e75d0e320057d75d0e32036be64d0e32006bd64d0e3201dee72d0e32005ed72d0e32034ff7650e32036be6450e32006bd6450e32005ef7250e3201dec7250e3201ded76d4a32006ed76d4a3201f6e75d4a3201eef65d4a32006ed65d4a3214dee74d4a3202dee73d4a3202dec73d4a32425ef71d4a32425ed71d4a320deee61d4a3201eec61d4a3241f6f51d4a3241f6d51d4a3241faf41d4a3241fad41d4a32005ed70d4a3201ded76d0a3214eed76d0a32005ee75d0a3214f6e75d0a320056e75d0a3214f6d75d0a3214dec75d0a3201fae74d0a3201eef64d0a3214eed64d0a3202dee73d0a3202dec73d0a3214def71d0a32415ed71d0a3240f6f51d0a3240f6d51d0a3214faf41d0a3240fad41d0a32005ed70d0a32004ff755823207cfc7558232004ff7458232034fc745823201cfc7258232006ef525823201eec525823201edf325823201edd3258232004ff715823200cfe7158232004fd715823200cfc71582320067f51582320067d5158232006bf4158232006bd415823201eef2158232006ed215823201efb705823201efb205823201ef82058232006fa1058232006f91058232034fe74d9532004fd74d95320065f53d9532006ed72d9532004ff71d953200cfe71d9532004fd71d953200cfc71d95320067f51d95320067e51d95320067d51d95320067c51d9532006bf41d9532006bd41d9532014fe70d9532004fd70d95320076d72d953220f5e32d95322f76c32d95320057f71d95320057d71d95320067f61d95320067e61d95320067d61d95320067c61d95320073f41d95320073d41d95320076f21d95320076d21d95320067f74d95320067e74d95320067d74d95320067c74d95322f67f72d953220e7e72d95320067d72d95320066d72d953220e7c72d953220e7e42d953220e7c42d953220e7e32d953220e7c32d95320067f71d95320047f71d95320067e71d95320067d71d95320047d71d95320067c71d95320067f41d95320063f41d95320067e41d95320067d41d95320063d41d95320067c41d953220e7f21d95320067e21d95320067d21d953220e7c21d95320067f70d95320067e70d95320067d70d95320067c70d953220e7f20d953220e7c20d95320067f10d95320067e10d95320067d10d95320067c10d95320067f659953207cfe75995320047e7599532034fe7499532004fd7499532004fd729953207eed729953207cff719953200cfe7199532004fd719953200cfc719953207e7f51995320067d5199532006bf4199532006bd4199532014fe7099532004fd70995320067f7559532004ff7459532034fc7459532004ff7259532006ef7259532004ff715953200cfe7159532004f
  | 26 => 0x6bd4159442004ff7059442014fc7059442004ff7558c4207cfc7558c4201edf7358c42036df4358c42036dc4358c4201ede3258c4201edc3258c42004ff7158c4200cfe7158c42004fd7158c4200cfc7158c420067f5158c420067d5158c42036bf4158c42006bd4158c42006df3158c42006dd3158c42004ff7058c42014fc7058c4207cff76d4c4201cfe76d4c42004fd76d4c4202ede63d4c42006dd63d4c4202cff7694c4201cfe7694c42004fd7694c420067e6594c420067d6594c420075f5394c4201dee7294c42005ed7294c42004ff7654c42004fd7654c4201cfc7654c4202cff7614c4201cfe7614c42004fd7614c4207e7e6514c420067d6514c42035be7414c42005bd7414c4202ede6314c42006dd6314c4201dee7214c42005ed7214c42004ff75580420067f75580420047f755804207cfc75580420067c75580420047c7558042004ff735804202cfc735804201eee4258042036ed425804201eee3258042004ff715804200cfe7158042004fd715804200cfc71580420067f51580420067d5158042036bf4158042006bd415804201efb7058042036fb4058042036bc4058042036f8405804201efb205804201ef82058042006fa1058042006f9105804201e7e7599632034fe7499632004fd749963201cfe729963201e7e529963201e7c529963201edf329963201edd329963207cff719963200cfe7199632004fd719963200cfc719963207e7f51996320067d5199632006bf4199632006bd4199632014fe7099632004fd709963201eef209963201e7f7559632004ff7459632034fc745963201cfc725963201eec725963201cec725963201e7e525963201e7c525963201eec5259632004ff715963200cfe7159632004fd715963200cfc71596320067f51596320067d5159632006bf4159632006bd4159632004ff7059632014fc7059632004ff755923207cfc755923201ebf745923201cfc725923201eec725923201cec725923201ebe425923201ebc425923201eec4259232004ff715923200cfe7159232004fd715923200cfc71592320067f51592320067d5159232006bf4159232006bd4159232004ff7059232014fc705923201eef205923207cff76d523201cfe76d5232004fd76d523201cfc76d523207e7e65d52320067d65d523201dee72d5232005ed72d523221f6c52d5232034ff769523201cfe7695232004fd769523201cfc7695232036be6495232006bd64952320073f549523201dee7295232005ed7295232004ff765523201cfe7655232004fd765523201cfc76552320067e65552320067d6555232036be6455232006bd6455232005ef725523201dec72552322176c5255232034ff761523201cfe7615232004fd761523201cfc761523201dec721523207e7e65d4e320067d65d4e3202f5e53d
  | 27 => 0xf7459542006bf7459542004ff735954202cfc7359542004ff7259542006ef72595422167e52595422167c5259542004ff715954200cfe7159542004fd715954200cfc71595420067f51595420067d5159542006bf4159542006bd4159542004ff7059542014fc7059542004fe76195420067d651954207e7e751954202cfe7319542004fd731954207cff711954200cfe7119542004fd711954200cfc711954207e7f51195420067d5119542006bf4119542006bd4119542014fe7019542004fd701954201cfe76d51420067f65d514207e7c65d51420373e54d514201dee72d5142005ed72d514201cfc76551420067f65551420067c65551420373c5455142005ef725514201dec7255142037ac425514207cfe75d8d42004fd75d8d4214eef42d8d4214eec42d8d42004ff71d8d4200cfe71d8d42004fd71d8d4200cfc71d8d420067f51d8d420067d51d8d42006bf41d8d42006bd41d8d42014fe70d8d42004fd70d8d42006df6398d420057f7558d420057c7558d4202ede6318d42006dd6318d42004fe76d4d42004fd76d4d4207cfc76d4d42035be74d4d42005bd74d4d42004fe7694d42004fd7694d4202cfc7694d420067f6594d420067c6594d420075f5394d4201dee7294d42005ed7294d42004ff7654d42004fe7654d42004fc7654d42004fe7614d42004fd7614d4202cfc7614d420067f6514d4207e7c6514d4201cfe7690d42006df6390d4202edc6390d4201dee7290d42005ed7290d4201cfc7650d42005ef7250d4201dec7250d42034fe76d49420067f65d494207e7c65d4942035be74d4942005bd74d494201f6e52d494207cff7654942004fd7654942034fc76549420067f65549420067c6554942005bf7454942035bc745494201fac425494207cfe75d8142004fd75d814202cfe73d8142004fd73d8142004ff71d814200cfe71d8142004fd71d814200cfc71d81420067f51d81420067d51d8142006bf41d8142006bd41d8142006fb60981420057f75581420057c755814216ebf6418142005de7318142005dd7318142016fa6018142006f9601814201cfe759944201e7e7599442034fe7499442034fc74994420367e54994420367c549944202cfe7399442004fd739944201cfe729944201cfc729944201e7e529944201e7c529944201eee329944207cff719944200cfe7199442004fd719944200cfc719944207e7f51994420067d5199442036bf4199442006bd4199442014fe7099442004fd7099442036bc409944201cff755944201e7f7559442034fe7459442034fc74594420367e54594420367c5459442004ff735944202cfc735944201cfe725944201cfc725944201e7e525944201e7c5259442004ff715944200cfe7159442004fd715944200cfc71594420067f51594420067d5159442036bf4159442
  | 28 => 0x8e42006dc1098e42004ff7558e420067f7558e420047f7558e4207cfc7558e420067c7558e420047c7558e4201edf7358e4201cfc7258e42136ef4258e4201eec4258e4201ede3258e4201edc3258e42004ff7158e4200cfe7158e42004fd7158e4200cfc7158e420067f5158e420067d5158e42006bf4158e42006bd4158e42006df3158e42006de3158e42006dd3158e42006dc3158e42004ff7058e42014fc7058e4201eef2058e42006df7558e420065f7558e42006de7558e42006dd7558e42006dc7558e420065c7558e42006dd7458e42136dc7458e42006df5458e42136de5458e42006dd5458e42136dc5458e4201edf7258e4201ede7258e4201edc7258e4201edf5258e4201ede5258e4201edd5258e4201edc5258e4201edf4258e42136cf4258e4201ede4258e4201edd4258e4201edc4258e4201ecc4258e42006df7158e42006de7158e42006dd7158e42006dc7158e42006df5158e420065f5158e42006de5158e42006dd5158e420065d5158e42006dc5158e42136df4158e420069f4158e42006de4158e42006dd4158e420069d4158e42136dc4158e4201edf2158e4201ede2158e4201edd2158e4201edc2158e42006df7058e42006de7058e42006dd7058e42006dc7058e42136df4058e42136dc4058e4201edf2058e4201ecf2058e4201ede2058e4201edd2058e4201edc2058e42006df1058e42006de1058e42006dd1058e42006dc1058e4207cff76d4e4201cfe76d4e42004fd76d4e4202ede63d4e42006dd63d4e4202cff7694e4201cfe7694e42004fd7694e4220e7f6594e4220e7c6594e4202ede6394e42006dd6394e420075f5394e4201dee7294e42005ed7294e42004ff7654e42004fd7654e4201cfc7654e4202ede6354e42006dd6354e4202cff7614e4201cfe7614e42004fd7614e422067f6514e4207e7c6514e42035be7414e42005bd7414e4202ede6314e42006dd6314e4201dee7290e42005ed7290e42004ff755824207cfc7558242004ff735824202cfc735824201cfc7258242004ff715824200cfe7158242004fd715824200cfc71582420067f51582420067d5158242006bf4158242006bd415824201efb705824201efb205824201ef82058242006fa1058242006f9105824202cfe73d9542004fd73d9542004ff71d954200cfe71d9542004fd71d954200cfc71d95420067f51d95420067d51d9542006bf41d9542006bd41d9542014fe70d9542004fd70d95420067f659954207cfe7599542004fd749954207ebd749954202cfe7399542004fd7399542004fd729954207eed729954221e7e529954207e7c529954207cff719954200cfe7199542004fd719954200cfc719954207e7f51995420067d5199542006bf4199542006bd4199542014fe7099542004fd70995420067f7559542004f
  | 29 => 0x4ff7558f4207cfc7558f4201cfc7458f42036df7358f42036df4358f42036dc4358f42004ff7158f4200cfe7158f42004fd7158f4200cfc7158f420067f5158f420067d5158f42036bf4158f42006bd4158f42006de3158f42006dc3158f42004ff7058f42014fc7058f4207cff76d4f42034fe76d4f42004fd76d4f4207e7e65d4f420067d65d4f42035be74d4f42005bd74d4f4202cff7694f42034fe7694f42004fd7694f420067e6594f420067d6594f420075f5394f4201dee7294f42005ed7294f42004ff7654f42004fd7654f42034fc7654f420067e6554f420067d6554f4202cff7614f42034fe7614f42004fd7614f4207e7e6514f420067d6514f4201dee7214f42005ed7214f4207e7e65d4b420067d65d4b42035be74d4b42005bd74d4b420067e6554b420067d6554b42005bf7454b42035bc7454b4201fae4254b42004ff755834207cfc755834201cfc7458342004ff735834202cfc7358342036ee4258342036ed4258342004ff715834200cfe7158342004fd715834200cfc71583420067f51583420067d5158342036bf4158342006bd4158342036fb7058342036fb4058342036f8405834201e7e759964202cfe7399642004fd739964201cfe729964201e7e529964201e7c529964207cff719964200cfe7199642004fd719964200cfc719964207e7f51996420067d5199642006bf4199642006bd4199642014fe7099642004fd709964201eef209964201e7f7559642004ff735964202cfc735964201cfc725964201e7e525964201e7c5259642004ff715964200cfe7159642004fd715964200cfc71596420067f51596420067d5159642006bf4159642006bd4159642004ff7059642014fc705964207e7e65d52420067d65d52420373e54d524201dee72d5242005ed72d52420067e65552420067d6555242005ef725524201dec7255242037af425524202edf7598e4202ede7598e4202edd7598e4202edc7598e4202edf7498e4202ede7498e4202edc7498e42006df5498e4242ede5498e42006dd5498e4242edc5498e4201edf7298e4201ede7298e4201edd7298e4201edc7298e4201edf5298e4201ede5298e4201edd5298e4201edc5298e4201edf4298e4201ede4298e4201edd4298e4201edc4298e4202edf7198e4202ede7198e4202edd7198e4202edc7198e42006df5198e420065f5198e42006de5198e42006dd5198e420065d5198e42006dc5198e4242edf4198e420069f4198e42006de4198e42006dd4198e420069d4198e4242edc4198e4201edf2198e4201ede2198e4201edd2198e4201edc2198e4202edf7098e4202ede7098e4202edd7098e4202edc7098e4242edf4098e4242edc4098e4201edf2098e4201ede2098e4201edd2098e4201edc2098e42006df1098e42006de1098e42006dd109
  | 30 => 0xc7458052006bc7458052034bc74580520067f54580520067d5458052004ff735805202cfc735805201eee3258052004ff715805200cfe7158052004fd715805200cfc71580520067f51580520067d5158052006bf4158052006bd415805201efb705805207efb505805207ef8505805201efb205805201ef82058052006fa1058052006f910580520367e759974201cfe74997420367e54997420367c549974202cfe7399742004fd739974207cff719974200cfe7199742004fd719974200cfc719974207e7f51997420067e51997420067d519974207e7c5199742036bf4199742006bd4199742014fe7099742004fd70997420367f74997420367e74997420367d74997420367c749974207e7f73997420067e73997420067d739974207e7c73997420367f43997420367e43997420367d43997420367c439974207e7f729974221e7e72997420067d729974207e7c72997420367f42997420367e42997420367d42997420367c429974221e7e329974221e7c329974207e7f71997420047f71997420067e71997420067d71997420047d719974207e7c71997420367f41997420363f41997420367e41997420367d41997420063d41997420367c41997420067f31997420067e31997420067d31997420067c319974221e7f21997420067e21997420067d219974221e7c219974207e7f70997420067e70997420067d709974207e7c70997420367f40997420367e40997420367d40997420367c409974221e7f209974221e7c20997420067f10997420067e10997420067d10997420067c10997420367f755974201cfc74597420367e54597420367c5459742004ff735974202cfc7359742004ff715974200cfe7159742004fd715974200cfc71597420067f51597420067e51597420067d51597420067c5159742036bf4159742006bd4159742004ff7059742014fc70597420367f74597420367e74597420367d74597420367c74597420067f73597420067e73597420067d73597420067c73597420367f43597420367e43597420367d43597420367c43597420067f72597422167e72597420067d72597422167c72597420367f42597420367e42597420367d42597420367c42597422167e32597422167c32597420067f71597420047f71597420067e71597420067d71597420047d71597420067c71597420367f41597420363f41597420367e41597420367d41597420063d41597420367c41597420067f31597420067e31597420067d31597420067c31597422167f21597420067e21597420067d21597422167c21597420067f70597420067e70597420067d70597420067c70597420367f40597420367e40597420367d40597420367c40597422167f20597422167c20597420067f10597420067e10597420067d10597420067c1059742
  | 31 => 0x815202cfe73d8152004fd73d8152006ef52d8152004ff71d815200cfe71d8152004fd71d815200cfc71d81520067f51d81520067d51d8152006bf41d8152006bd41d8152005de7398152005dd7398152006fb6098152005bf7458152005bc74581521c67f6518152016fa6018152006f9601815201ebf745905207ebf545905207ebc5459052004ff735905202cfc735905201ebe425905201ebc4259052004ff715905200cfe7159052004fd715905200cfc71590520067f51590520067d5159052006bf4159052006bd4159052004ff7059052014fc705905201eef20590520347d76d50520367e64d505207f3e64d50520363e64d505207f3d64d50520367c64d50522d57e73d505247e7e63d505207f6e72d505221d7d72d505207f6d72d505221e7e62d505207f6e62d505207d7f71d50524757d71d505207e7f61d505246e7d61d505246f3f41d505246f3d41d505246f6e21d505221f6c21d50521857e70d5052004fd76950522157d759505207f3f5495052004ff76550522157f76550520067f765505207d7f745505207f3f74550520367e64550520367c64550522d57c73550524667e63550522157f72550522167e62550522176e625505245d7f715505245d7d71550522167f61550524567d61550524573f41550524573d41550524576e21550522176c21550521857c7055052004ff7458c52034fc7458c5201edf7358c5207edf5358c5207edc5358c5201ede3258c5201edc3258c52004ff7158c5200cfe7158c52004fd7158c5200cfc7158c520067f5158c520067d5158c52006bf4158c52006bd4158c52006df3158c52006dd3158c52004ff7058c52014fc7058c5201eef2058c52004fd7694c5207f5f5394c5201dee7294c52005ed7294c5220d7d7694c522d67d7694c520057d7494c520067d6494c5207d7e7394c5220e7f6394c522d67d6394c5220d7f7294c5220f6e7294c5220d7d7294c522d76d7294c520056d7294c5220e7e6294c5220f6e6294c5220f6e3294c522d57f7194c5244d7d7194c5220e7f6194c524467d6194c524473f4194c524473d4194c524476e2194c5220f6c2194c521857e7094c5211e7e6094c52004ff7654c5201dee7254c520067d6414c5207d7f7214c5207f6e7214c522057d7214c5207f6d7214c520056d7214c522067e6214c5207f6e6214c522076e3214c5207e7f6114c5243e7d6114c5243f3f4114c5243f3d4114c5243f6e2114c522076c2114c521167e6014c5201def7654852006ef7654852004ef765485201def755485201f6f755485207eee655485201f6e6554852005ef735485207f6f53548520076d53548520d5ee71548520d5ec71548524376e515485207f6c5154852437af4154852437ad4154852005ef7054852004ff7458052006bf7458052004bf7458052034f
  | 32 => 0x6de5458e52006dd5458e52006dc5458e5201edf7258e5201ede7258e5201edc7258e5201edf5258e5201ede5258e5201edd5258e5201edc5258e5201ecc5258e5201edf4258e5201ede4258e5201edd4258e5201edc4258e52006df7158e52006de7158e52006dd7158e52006dc7158e52006df5158e520065f5158e52006de5158e52006dd5158e520065d5158e52006dc5158e52006df4158e520069f4158e52006de4158e52006dd4158e520069d4158e52006dc4158e5201edf2158e5201ede2158e5201edd2158e5201edc2158e52006df7058e52006de7058e52006dd7058e52006dc7058e5201edf2058e5201ede2058e5201edd2058e5201edc2058e52006df1058e52006de1058e52006dd1058e52006dc1058e5202ede63d4e520075f5394e5201dee7294e52005ed7294e520067d6494e5220f6e7294e5220d7d7294e522f76d7294e520056d7294e5220e7f6194e524967d6194e524973f4194e524973d4194e5211e7e6094e5201ded76d4a5207eed76d4a5201f6e75d4a5207f6f54d4a520076d54d4a5201fce63d4a52006ed63d4a5201fcd63d4a52006cd63d4a5207f6f53d4a520deee61d4a5201eec61d4a5207f6f51d4a5248f6d51d4a5248faf41d4a5248fad41d4a52004ff7458252034fc74582520067f54582520067d5458252004ff735825202cfc7358252006ef525825201eec5258252004ff715825200cfe7158252004fd715825200cfc71582520067f51582520067d5158252006bf4158252006bd415825201efb705825201efb205825201ef82058252006fa1058252006f9105825202cfe73d9152004fd73d915221e7e52d915221e7c52d9152004ff71d915200cfe71d9152004fd71d915200cfc71d91520067f51d91520067d51d9152006bf41d9152006bd41d9152014fe70d9152004fd70d9152006bf6499152036be6419152006bd6419152004fe76d515201cfe7695152006bf6495152036bc64951520073f549515201dee7295152005ed729515201cfc7655152006bf6455152036bc6455152005ef725515201dec7255152004fe76151520073d5415152034fe74d8d52004fd74d8d52004ff71d8d5200cfe71d8d52004fd71d8d5200cfc71d8d520067f51d8d520067d51d8d52006bf41d8d52006bd41d8d52006de31d8d52006dc31d8d52014fe70d8d52004fd70d8d5220e7f6598d52006df6398d522067f6518d5202ede6318d52006dd6318d5201cfe7694d52006df6394d5202edc6394d520075f5394d5201dee7294d52005ed7294d5201cfc7654d52005ef7254d5201dec7254d5201d7e75d495201e7f65d495201dee75d495201eef65d495201f6f65d4952006ef63d49520deee61d49520deec61d495207f6f51d49524876d51d4952487af41d4952487ad41d4952034fe74d8152004fd74d
  | 33 => 0xc7158f520067f5158f520067d5158f52006bf4158f52006bd4158f52004ff7058f52014fc7058f521867e6598352005de7398352005dd739835207efb6098352016f8609835207ef8605835201cfc7558352004ff7458352034fc7458352004ff735835202cfc7358352004ff715835200cfe7158352004fd715835200cfc71583520067f51583520067d5158352006bf4158352006bd415835207efb505835207ef8505835201ebf7459252004ff735925202cfc735925201ebe425925201ebc4259252004ff715925200cfe7159252004fd715925200cfc71592520067f51592520067d5159252006bf4159252006bd4159252004ff7059252014fc705925221d7d76d52520067d76d52520367e64d52520367c64d52522f57e73d525247e7e63d525221f5e63d525221f5d63d525221d7d72d52524b57f71d52524b57d71d525221e7f61d52524ae7d61d52524af3f41d52524af3d41d52521c57e70d5252036be6495252006bd64952520073f549525201dee7295252005ed7295252034ff7655252036be6455252006bd6455252005ef725525201dec72552520347f76552520073f74552520367e64552522173e64552520363e64552522173d64552520367c64552522f57c73552524667e63552522175e63552522175d63552522157f72552520076f72552522176c72552524a57f71552524a57d71552522167f615525249e7d615525249f3f415525249f3d41552521c57c705525202edf7598e5202edf7498e5202ede7498e5202edd7498e5202edc7498e52006df5498e520065f5498e52006de5498e52006dd5498e520065d5498e52006dc5498e5201edf7298e5201ede7298e5201edd7298e5201edc7298e5201edf5298e5201ede5298e5201edd5298e5201edc5298e5201edf4298e5201ede4298e5201edd4298e5201edc4298e5202edf7198e5202ede7198e5202edd7198e5202edc7198e52006df5198e520065f5198e52006de5198e52006dd5198e520065d5198e52006dc5198e52006df4198e520069f4198e52006de4198e52006dd4198e520069d4198e52006dc4198e5201edf2198e5201ede2198e5201edd2198e5201edc2198e5202edf7098e5202ede7098e5202edd7098e5202edc7098e5201edf2098e5201ede2098e5201edd2098e5201edc2098e52006df1098e52006de1098e52006dd1098e52006dc1098e52004ff7458e52034fc7458e5201edf7358e5201eec5258e5201ede3258e5201edc3258e52004ff7158e5200cfe7158e52004fd7158e5200cfc7158e520067f5158e520067d5158e52006bf4158e52006bd4158e52006df3158e52006de3158e52006dd3158e52006dc3158e52004ff7058e52014fc7058e52006dd7558e52006df7458e52006de7458e52006dd7458e52006dc7458e52006df5458e52
  | 34 => 0x52544df3e10d52544df3d10d52544df3c10d5254004ff7358a5402cfc7358a54036ef7258a54036ef4258a54036ec4258a54004ff7158a5400cfe7158a54004fd7158a5400cfc7158a540067f5158a540067d5158a54036bf4158a54006bd4158a54006ee2158a54006ec2158a54004ff7058a54014fc7058a540367f54582540367d5458254004ff725825401cfc7258254004ff715825400cfe7158254004fd715825400cfc71582540067f51582540067d5158254036bf4158254006bd4158254036fb7058254036fb4058254036f840582540357e75d51540367f65d5154035be75d5154036bf65d51540373f65d51540363f65d515407dbf71d51544d5bd71d51544cebf61d51544cebd61d515407f3f51d51544cf3d51d515402cfe73d8954004fd73d8954004ff71d895400cfe71d8954004fd71d895400cfc71d89540067f51d89540067d51d8954006bf41d8954006bd41d8954006ee21d8954006ec21d8954014fe70d8954004fd70d8954005de7398954005dd7398954006ef6298954005fa7098954005f9709895401eee6218954006ed621895401cfe72d8154004fd72d8154004ff71d815400cfe71d8154004fd71d815400cfc71d81540067f51d81540067d51d8154006bf41d8154006bd41d8154006fb10d8154006f810d8154005ee7298154005ed7298154006fb60981542667f651815423ebf6418154016fa6018154006f96018154035bf7655054006bf7655054004bf7655054035bf75550540373f755505407ebe65550540373e65550544c5bf71550544c5bd7155054036bf61550544bebd615505407f3f51550544bf3d5155054255bc7055054004ff735885402cfc7358854036ef725885407eef525885407eec5258854036ef4258854036ec4258854004ff715885400cfe7158854004fd715885400cfc71588540067f51588540067d5158854036bf4158854006bd4158854004ff7058854014fc70588540367f54580540367d5458054004ff725805401cfc7258054004ff715805400cfe7158054004fd715805400cfc71580540067f51580540067d5158054036bf4158054006bd4158054036fb705805407efb505805407ef85058054036fb4058054036bc4058054036f8405805407ebf6499352036bc649935207ebc645935201cfc755935207ebf545935207ebc5459352004ff735935202cfc73593522167e52593522167c5259352004ff715935200cfe7159352004fd715935200cfc71593520067f51593520067d5159352006bf4159352006bd4159352004ff7059352014fc705935207f3f549535207f3c545535220e7e6598f5207edf6398f5202edc6398f5207edc6358f5201cfc7558f52004ff7458f52034fc7458f5207edf5358f5207edc5358f52004ff7158f5200cfe7158f52004fd7158f5200cf
  | 35 => 0x300040020000000002000200040120040006001000700000000008000000000200000020000001000c0010014004002c005003800300000000040004000000c000000000140100000001000400c002c00000000000000000000000400040040030002001400300000010010000000c000001000000080000014002001000100100030000000001c002000400300080030004000004800200ac00000300030000003000c000000000b0004003000800100100000014013001c00b00040000004002000c000003000a0008001000400300040080024006000000000040000014008000000100000000004000000000200040010004000001c001000800000080030018000000800200200110064005004400100200020004000000000500200130004000000400200180010000003000400e002c011000c001001c0020000000000c0070000000001c000000c0030008011004000a00140020004001000c006000400000000060004000000c0000014004000000000000000004000001000000100020008000003000600100000004000007400000080010000002000c0080000002000000100280030074004000000200400000000002000000000000010000000000400000080020028000000400e00000010010000001400000040030010005000000300200000038006003401400380050008018000400000080010000000000c00907eef6298b5401eec6298b5407eec6258b54034fc7558b54004ff7358b5402cfc7358b5407eef5258b5407eec5258b54004ff7158b5400cfe7158b54004fd7158b5400cfc7158b540067f5158b540067d5158b54006bf4158b54006bd4158b54004ff7058b54014fc7058b542567e6598354005ee7298354005ed729835407efb6098354016f8609835407ef86058354034fc7558354004ff725835401cfc7258354004ff715835400cfe7158354004fd715835400cfc71583540067f51583540067d5158354006bf4158354006bd415835407efb505835407ef85058354035bd76d525407ebd76d52540373e75d525407dbf71d52544e5bd71d5254036bf61d52544debd61d525407f3f51d52544df3e51d52544df3d51d525407f3c51d525423ebe60d52540373d76d52540353d76d52540063d76d525407f3f72d52540073e72d52540073d72d525407f3c72d52540373f62d52540373e62d52540373d62d52540373c62d525407f3f71d52544e53f71d52544df3e71d52544e73d71d52544e53d71d525407f3c71d52540373f61d52540363f61d52540373e61d52540373d61d52544de3d61d52540373c61d52544df3f21d52544df3e21d52544df3d21d52544df3c21d525407f3f70d52540073e70d52540073d70d525407f3c70d52540373f60d52540373e60d52540373d60d52540373c60d52544df3f10d
  | 36 => 0x180000000007004c00100000030004003001000000000080000057000000e0008007006c0060004002001000200140000004003000c00000300060008002006000100040000000002000c000002c003005000000000000048003000c01000000000000005000000200740000000000000c0000000001000800600840000060006005c0000000000001000b00680000000006003800000040000000005001c002001000000000030000001001c0160000002000c0000084003000400000100050000002000000c001c0050014001004c0000008006000800900100010000000000c000000c0040004001000000e0008002002800100440010040000001c0060000002000c002000400600000010010001000800000200000014001001c0020018001001000600080060030001000c00700040020050007001c004000c00100000030000003000c000000000800000000010008002c0040000000000800000000010000001003400e001400000080120008001000800f0000004000400000300030010000000c00100400040014006000000100080090000006001400700040030000001000000b00180000000000000400500840000008000000800e00080000028005000000600080030000000000000000d8000002000c000c00900340020014002000000c00000010010009000800b000400000100000000004001000000200010044001000800c0000000003000800340040028002004400100040020030000002400000040000024000000c0000004002003000000340020030000000801d00180040000002000400100000050040003002c0000018000000000000440000000006006000100100010004000003c00c000800500500020008002000000200040000000000000800700080000008000000c00800100000004002000000000040030018004000001000380000004000001c0070008000000000700200010000002004400600000070018000000400400000000008000001c00000040050024013000c00700080000018002000800000000000008003002000b00000070004000006000000240080018000000400e0004004000400000000030008001002c001004c0000010002002400a0014005000000600080020000000000c001000c00000040020004003000000e000400b00000000018000000400b0008002000400600000000010000000000800080000014000000400200000000018004002000c005c00200000000038005000400000000000004000000401e00000030024001001400000000150010000000400100180010004003000c00000140020008002000800000000030004000000000d00140040008000000000d004c01400000020044000004c00000000020018000000000a0004000006c006002000a0000
  | 37 => 0x4002001c00300000000008003000801200040050000010000c007000000b00000000000005003000400000000000006000000000100140080010001002f000c001000000500000030014000000400a002c001001c00b000400400000000024001000c000000400e00340010000002000400200140000008000000400200040000024003000c0000044000000c003000c004002400300340080000004000802a002400e00040000004001000400000140140000001000401700040000018001001800800040000004000000c003001c0040000003000c00200000030024003000c005000000b0020007001000600240050008000000000000000040004000000001300180030000001000000e0000004000c00000000070004008001c00300040030000003002000000000030004015000800e0000007001400200140000020000005000000440050000000008c00b0000001000800a0010000000000100280150024004000c015000802000000010000005002c00c0038001000000900040010000002004c00700040070014003002000000000000004000000000e0004002000800c000c003002400d00340040000000001000a0004002000c008000400000000010004000002800100080210000001000c00000080000000000001c005002400000080000010002000000400200070084008000c00000000000008007000000200080000034004004c00000180000000003002800500040010008000002000800000000014000001c007001000200000000004002001c00100000000018002002800000180000000015002000f000800100040010028001000401000100030054009002c004000000000580090008000000400a000800400000000074002000800b00000050038001000400b0048000001c009000c0090024000000000100080000004000005800000080040018000000000100300050004002001c00800000020010002000c00000140000018002000000b000000700040030000001006400000340040000005000000800000000004001000000b0014001005000a0004001000000c003400f004c00000240000038002000c0010008003001800000240050060000000400300000010000000000800300340130000001000c004000000d00000010034005000c00300080060014000000c006000000300040010000003000000000080020014001000c0010014001000400100040010004004004800700000030000001000c004000c001002400700000050008018004000b000400000480010008000001c014001c00400380160008002002403f000c00000080010004005002000a00340050000001003000400c0018000000100040000004006000400000240030014003000400e0018001002c00000080060000008001c008001c000
  | 38 => 0x1000200040060038000000000c000000200040060000002000001100180180018000001c0080008008000400900000080004002000c00100140000000002000000700140020000002000000300000000000003004400100140000008002000800e000000d000c000001000400080010010001000c002001800000100010004003000000000140010000007000c00300000060018003000c0070008003000000d0010002000400b001400000000060004000001800e000400c0000000001c00300240000000006000000c000801c006c00100040010000001000800c00080040000012000800000000010000008000001a0004001001800200040030028004000400000000000000006002c0150018000001800100000000024000000000f0008000000000a000000000000010028000000000a00100020000001000000100100020004000003c0000014007000000100240010004002000000600040000034006000000000000050008001000000200040000000004000c0130008000000c0000004000000000c003c00100000070000001002800800080010004000000000000000030008000001c0010018000007400b00dc0050000003001c01800080000000000000000a005c002002c00000240050000005000000000000030060003000000000680000004003000000400140000000005003c0040004001003c00d001c000001c001003400800000000000000000c0000010000003801d0014002000c00300080000004000000400000500000020004001c0020014002003c00500040040010004001400a0008000001400c000c000001001a000c0010008008002400000180090000001000000600240000000003000c000003c00200000000004002000c000000c002000c002000800f0004002003800a001400700000030000000002c000000c00e0008001001c0000000006002000b002800200000010008002000c000002800c00000010020001000800000000060004001001c004002800000040090024004001c005000000c000400a006c0040018000000000a0024007002000b0004001001000a00000000008000001c0000000002002c002000400000000000000013001c000000400300000010000001000c000000c00a0004001003400400040030008002000c0000014002000800400000020008001000400a000c002001c0090000000000000500140000024000001c000001000000340000000003000400000000010068001000000000040050008002001c01200180050028001000800400000040008001000000a001000200040000010003000400200040000024000000c00d005c001000c00400000000024003001000000080040014004000800700580000000010001000300000120000000000000000080030018000000
  | 39 => 0x9800000000009ea952a6230000b6e864c2b2800050e98a292f8874af3267048ea3f01482564933a1a85d8001cb4f9200b9ee64e2569c90ae6140cae98a1067a49e633e1d5e3a0a88480f00000001a6298200000001ae03bf00001744e9671400002d52538abf2e1811d132600001740000000a31000014a400000024c83a808cc37c0f9e0000000b1885c6000000013290840000f56343543c1bc000004bc0002b584181495d3d4d900007819f52873950081f0000000000000000007bd07a80000ba285d1ee200029c26912c90000228a33dac1e000000000000000000000aec03645398c2600018389418000174800000000000000000000000000000006c087fe0dec00008e80000001348000000059d8f0242200005c095ec9db257253825527af84cc67720964bba0e8ac182122138b6a60797102e1930098784307c10ad094325900fc8000a7ba7bc000000000002260000a7e3b780722f7000087e0b5e34f97767f88180000000000027a85b88d5c5d5814a640995900029062d38000000212c81bc2464da5be2000177052b2d3a1b000009dc15b2b939ca426a011453b2c6c00018ae613939e2019566729800088f226024692396e391010a4207616d8790a42940e60b611c00022a653780009fb8416580a32448d0e5456e0be8858a72aa4d2d189bd80004318faea388000842800000005ec78b000035300003a400008c2acb8000056c496c6442eda30e2fb00000002c240290f30369a84a04580006450f5c98a80000001a8c7a1015490b0de6a66ef3e5c31bf33aa943e99b8c76515c00097f8000000101c1a011e7000298e4ed0000b0f0f902e300000002cee0000e7c4166a5497383ae00000003f80472000035a80491a50000000a5e800000000009238a940000f7e78d9cc600280020034002006400000000020004000000400000000020004007000000500140010004002001400800140040000000002c0000008001000800000500000000005000400700040000008010001c001000c0000000005000c00000100010000000002c00600140000020005002400200180030000003000800800080040000002000c000002c0000018006001c00400000040000002001000000500060004000000000300000000024000001c00a000000300000000000006001c000000000c000000300180090028000003000b000000a0014003002c0020000002009c007003c00000180000008002002400700100320004001000000f0000001000000000200000000000004000e00100000004009001800200140000000017000c0030000003000c008006000000040010000005001c001000000700d000200380010000005000c0030024005000400d000c000000400100480030034005000000b000c0000000022001c00200080070024002003000
  | 40 => 0x940beab4000017de0000ef4749c0004169d9a0000c1e3f11aca00021cc0001cd481a178809aace048198fa6d028de28ed0da92e400000000000001e7796f0a349001edc00021c896d00007740f442f200004cb80004fd00005bd1124000000000000000000000000000068c15c80000f7a8591eb01b71bcd5ac000000d00004b90bd6290800072a0000a3500008848000abe000000004200002a4400000004f600000000e4043c800000020f58ad95a261f1a13000157d7b280004a18000000233220fa2047c0ab280002f303809a410c50000b658000639000000000001b419c24f980006171c885e6000000000002a880000002d5c7e95f24000298203080008beaf1206e1b7c000000050d28aeb9d80003a026ae8ac135c93900003ec2c5a000000000022ae830a31007a80000000d56b8901fc000032e00011f200000000002a14acb899a26c04263b0de940000f5e73b8a7b7d31d662858e2003f97969f91cbe159acbea920d1e0000456651000000000004ca95da0f513fe27d03f615269187059de8561977c0000ba6b6a94125438ea329e2bde000274629cdf1857500007799bae7bec0002bb87940000000085962600018302720e8447b80006fda5ba7fa4164072103d8f50000000055c53280002c52b4e000127c74a98ac6ba8000322c5e60000ea2000000018300007bb224a0002aa02dc1168000293800013db5129a5a5a42c680002ee571005cfa2a0ef86f1886c000050a96180001898000000253460b1bc0001a48400003106ab8f6a8a2619aafb9c7241ea31a8bc800000000003f2000073aaedd00000260000000000106ab190000ab84000a7e0db8449c24a0728a4a4e98000000055d0000000000129c0000000a9f80007fc00009c788ac7238a50a1a1114295057088680000001d163bc80005b0145a3ef10168950000431c0002c4df905640000a76a59a479a1bf4d25f120000000000000024a9bca0000000000000009890f0a8100000001be87fd61fc000277692a05340002d9800021d27ba8d2c0002d16a432c0e049ae08ab1d72a571add000027000001b3886d8c28a998ee25dc8000a89000000000006892c9e6db11d0457137e55c883c00018545c10c9ca8bc46c57ccbdb640d3020001a5691a228e0441ba61e9a298af01cbc8c98000bcd259e920950c7a89ec067b800000023a6000000092e84909348e14000205600003c00000000000000006800001c30000000000000000000000a9143824b152fcf500d65c48b8e8000014a2a334a8872602989c93b0000000100e00027827cd0550264800010928600000f2c91f80702e5132815bab8d36100008c500005880000169e9a1000000000000000000000000015a856c8c4000000000022b28f5a92096b8000304992a2640000779227a00000000000000000208e24
  | 41 => 0xf48746351000089fe82605b1a4e21e000019b80b446d677a00002c600027a054a02e8000265e76f0ac85488bd0000000000000000002f2101e80000eb2a6a0002df4000000000000003bac00000011560000b2e0001d9265629f20000000000206a7db67d8871958a9ee8000a6264506df996b406000075d18a60002f3893d000000000000000000000000000013303cf000000023d000017dc000000000011428a41d6063229b90000000a7f24321500f0800000007d70aa000000009061cc439a277eb9980000470c671619a8f0000000022112665a8a7c4968e3869184ac3622b2200015ccb3c2a40500000073a1a2a00001b42220ddc6399cda0001277000285c000000082706ec0001208000000000000007a280003c0000000000000000000000102890e053c00008fc4718bc408f85b441604fab1f00000001ec131852d600000009a4851851885fe3ca2cf664689fc82c1155a4a833c41d400049d8000aea000099b18f6667a3e85860d6c000000021f2c2c5b800007c700000df80009c09e566ca92c20001b60861800000000009980a93bb0d19c7eb0000000000012c9248b098dd700000000000c6228d8828000000041d27b85c7943185eeae62d300005fba7081bd929a1d22f0a8770558b41113a1a5957a2cd1b8ab9521b448da688000000000000007cca0408fc80000000000000000000000000002cd8000040250411640000000baf8000a4b8ca200027ac00024b61b62afea8f96741f085d60002172000094600001cc00011db5bf0000ad5291a000000085ea53e0002b2a00018950002da0b9404a267ec9860ca800004c25562fd94024bc80008799cae8038000906abb808c972b4df000001be82a57e9bd28bda2da00014d400000008a1147b0002f1400017b860640000000000000000055b0d424fc23cc9c4a45a1ed9b3e05302a95ce92e2000000000019a6000000000009520002f4e0001f56a94000000007860000a980001110b7e021a430912380718c2a079d0400000000638000000000044fa4b200002720000da24dac9741d9adac00b9c8a16c8f72687053e5a9261266f9ab8a1081bcacc918e9991bc4505056028504a86091a7959e02f07998c500ff0bf3299983eb130ffe5a600000001b4600000000001a52565927a3a99af25980000aa780000000bee043011a76810caa928dd39c2aee790c0e2200026004460898974000000000000000e326300d7c4a20000b9080007dc80000000000ad800002e10000a87ace213500005d6000043880004b2000000010785df681a28c80005a18000000077a07d80000a6598a4ce82c8944800051229e8000205e67d96c6b1a81312f1800046622a0000000002f0512937a19bb4925f8ba00abf4668000b4a8e622a640000000000819af426590000a75a0f71d1008442ca0
  | 42 => 0x6be26b800069c102600022883a90000273800000018780000000a65c5c40000d922822afa000006100011fc75b80000002f18000019600013547ce1ad71f296dc241451409a215c65c9ec400016509d40000000000067f800000000000002ac61199a3e000000083a884400024dc0001f482c0935e00000980001207000191800028be1e8158463700000000000b4080003d823aa0000000000154e0002c1a76b80008d2287c000000061c8ec70001e9e8335c5c72311df81e800000000000d6000078219940000cb400000004b38000296a642078a39000000005371be6590e3fa2b69a8e86a8c7cab110863c8a8b281897ac000000027280000000f740001fae00022c20002c2e0001df20000ddba7c0754a62c0000000ca31cd000093f84fcac5abe049a00000d0813542e2306ad11d1c0001f1597c80009e10000000000029a80000001e28000000043ac98aab269801858000385adfe0000000000001000000000002d8000017cd000295a680a9ba6ac836e00014b42f307f23ff096241996068db1c3a4e59ffa1c40dae9df29e03f3800083cc00000000002d1184400005fc91529320002a6c000000020aaeda862000000010384daa5400000208831141c616800087103943b69144afe000038a0000000000000005c500005ca6fa95a681b8000000207437a00006472e948b8800000000006b84000bce8000000227c1a1000030c8000977800074098600000257000000000006725b20ebc28dc00003500000002bfe44f05e08bf9c1258f299674413bda9b839690f97f85a5a74402188a2771874c3d38c8e23982201c900000068000362800080c168e26a9ef20701fba75a80009c724ac9fa1cfe00000008701970b0d1514b5900003a2000076095a00000000000008e56b01921a64ff84f2102a435088400000009bb1b3b3ad0000672ac84000253214c2dca9a086e4465296c4d002e462f8000000000050118aa00023b200013ac50d91580000cab4f1942e33a00001ae9f0600000000268c7401d0a20b6b85487809a400d98000000068a0000f180000000952a5580d384fe32c00000cc0e58000000006b0de212a86027301a7887c0c9e8345a5876000000000000000000025d80a80000000000000063e2ebf0000000000189e00000001fd80000002c2a0001c9a7f15688490110c89b944cb20982000009302c6235e0002638ade1fb023781b25ed13c05191a0866d2cfc595084a20b07dc5c4911a74f1a601508000000000000013a44dc93ee00020cc0002bb6176156846d95481b30ca8000054c3e0aa5ab00138464ba50e4291c27b46a844acd032f4a407be0001358746ab1c99605f8a33000000000008a892f40001c2a0002d380fa800000009c00001df00b506836a06330b532d6c000137160395d30002c72000000016294b23
  | 43 => 0xa08800000000002809bde56d8c860000ea898e9da4ab000003da14c28219e53000000000004949e5a1dabaa1f4ab0c25a0571000021a1ffd1c80e0e792800000000000000dea0001bfa308210400000000000000357a2c6000000062695785f8258047d18104f810dc0000000000000060480000002b8443b584624800008d92d0a7d9000030d1e337530dbe9078c3e60180002410000ab71ad2000083a6760d340000af254580000144000312000000000000000cce000123832240001e6833d000000000002a02530aaaa6c851774b9adc34720149d3a5926e7000054ca8363aac000b379bf8a7484ce7c316cca6c2b9312f8a2607e131c694103c000005c000280400013765cb8000b541c7e0000687000055a00006086599c93000278a8a3e1ec7fcaeb6bacae090001a140000cd00000000874045024b0000a5d2ec484c00007728be03010a0a000000053c97667b9407c000000000006ca000185082121a61e8aada00000009f700006f20a3a33c960400027cc0000ece0065d5691c2596506acf417d249b5f5697875d8aac63c200100000000000000b2225c5b73800000005025e712720002f3222c85c286ba80a00000008f1800000025e265e2374000164a882093c3c28000287ac5c0000000a36000071d0000111a58e18a9a3300000000598dd5000000000000000059ac401a00122ac9f4744e2b9181c8000000000041c08ba1b500000000000b7ca696455c0003711ea8aa9821c00028ba27c8000743129300029ae42f82cb0001a9c00000003f99996000288024d800000000dd000063a4b4a49219993a262180000001c369900000b8b0c01000109100000008191b58000000000000000000000000144f000000000025e60000000000000081f98ba5f09c54b432c2008c000000010bc9a2a16687d00009f00e5ab0d80000bbc0000001a11b5508964e610c02ed0000000000064f000000000000000000928000073d885460d806c67408ce8b9847a87aa69e0cd91e026983805db80000000ab60001f6c00028f0000009d8482be22f388feb42240866a99e06b89f3904d80000001e9c4488f9a68791a66b0a0091ac80000001ff88c89eb828fd4ba37604ee403064eba8990a52088f600000000000000000247ca9e800056a03d857480003192732973ca9e61a038c000094a6e82344000093e7b908663a48db20000c6c35cac7800000000002a4c0001e799790000019ac980001c6aae2000061893786102e1f000180097c058c718a20637ae56a4a011e474823008b6ed20b7bab7aa6487da0000000000000000000000000c9800000001af000000000000000000000000067b2ef80000a9a000000081e00002e60d9618512ac5872434000000000000009fa80000f6907e861000065d936c2020b126bb0d3a31a8630377e
  | 44 => 0x198808b13c200026e6a0e9e5a00025700001a766f90000648c000afc000000000000000000000000000006b44a580001e08000b562acc4c6a6fe425c7d2000198d000149c12294d6775a736ac692609cb2aae2a217e47a31bec7949f9a9b31950083866b40425b273ca3b8acf039015ca3c451481783ada04158d8cd840ca5b8187028c8e88000834207085da83e8e08a8ebd1aee626e2a3a0001c604c40000046242e3418d24ba49e1800001604181c86769ae002328000000210200024bc179000048121005392c60bb212288838000379c00000026b27bf52300000000000000083d8000ad18c08000187576a8fb8000000000000004948428679aa320c09b44a70412c00024fcab40000000000051f922a7c52252a689fff0001a280002c0c7fe61187f042881cc00001fc25b66c4aa3400018320000000704155e000221cb9a800098894ae0ea057f727000000000000000000000133941400008c78000000098e068a29e5faa0aa0001a12000000048ca098000029b1c1ad6f00000001309bb437b8000000177f000242a1840000837000000000000001ea4a895cb6b230000141810900020ba0001abc9759fbc8dc800000000000000000000000071b09e2038000015f977a0001dc447464428d31ed221c11f063bc26e00000006c102d23460e2600002282011f3c00029b60a5000083825aa0001299af69726158a650953813c338179261629720000abc9ffab263be8dfc0002b10039ad1227484b8b1200000000000a57a67647e0d3866f23f62cf84ba79b0e4900000009c6094000008c0259838a76e000013aa090612180b12f20c07c0002c7b52c583330000000077ebc409ea00000001788000575aa26000000029011703f78aa700000005428eb1250841a220000056300003d98371bd12d523ea000088d1e2d00012d4a61a228130000000025680002a5c00000004a5c000071291c000291000000a0ad70308000000075b060a659c0000ce295833997b5b6a00004d1000000000009e68e041868a5c40d00000002dfcb889e75083002032aa72054d1e1282b14d00002edc9b3800097ba57600000000001a3232f07ac30a8d11000000045f1f2c0ae97ecad400000002ec27d6c000000138e6030f123f2800004a0de90a60000000000000000005a3000016cd77800012736dc03000001b480df5852000000063c8000a0400007aeaabc79540002252b307b9c00091819de1fd0000a8800558fd000032e40009fc0000000085e0001ffb0002388376994ea63557e00023c83b28000000108e9c42b7003a00005a5000041c4714391026c2d007ba4739b064aa24c0ae6d72432b9634bc7c000000192c6c51ef8b1e80009be21f673300006bfa46ea1b1dba3a380000ef0c9a4fdc23646d00000000000000000000000000000000b990000
  | 45 => 0x104000061ba8469e981720b30af457f03f0517c0007a4950600000001c5953800000005f8ced59b686a00001d42567948410717182060c2e6e180006378b744d3c4eb3669c9b4abaf489e2129b9d30b809809282ae3cbf133f00000000000000000000000000002706a1ba67c511800010e909f00020030000000000025c24183f8000161a7388a520001bf00002b5e55eeca4971800000010480f319526424000000000046cce1e218108078599d7af0934a36e8000181a7240000000000235c39d0000aec95f00000000000261c00000000002b7e0001be0000279c6c8068e17c0b90301ae7e8dc22918e18640bb8198c74600000000eae440d6e60002f02000000000010931da1b5e000203a000080a82484d01682518000000037d0c4a3489f3349500000002bac5b41f980001e600001904000000055d00006cf1e1a4358000baaa1140002170000000000000005fc00000000000000201600028a42faa778000071caa88000000000000000000001bcb790000041480000000bfc000006a97a8000358aa6874a11723bf82b0459a98f613d46d0cc800044788da3752b8663292daa2093b01359f6353f8b8a8728000000006297318b890181a88f394bc8a58b6e63688525cb00006eb1b76bcd80301e7000054680008438000719000047105e881311259ce213497a43929e526b01be017631de3d20000ef3556800000002a22810000a2d9fa3b1d8648b6c8040000000000000000000000000119e00012625b5a806000000019b0000000000000019c6606ce4e0000d86000109415180000002dcc00007420000d8e03e00009b20000bcae48000004e405414a0a94800041897821e2958238b80003351fab2ffaa18b3a800052a80007d7c69e18c454e28f40000000000000000000000006e6000084f000059f800000013ea00000006b314d83ac00006d3000000000009882b000000cf45bb91d95c88000000244a0001eaa00016413f0aa4682a00005079b0e5e8a9542050000000000000000ca00028ca000118a273257c0000f8e000000000012a60000ad4872400070d000000013b90001f3100000007b300000001392a2600004fe2ed800000000000ec10001fa0079000000026045ac40005b50c8c0000a3035eab0cb949c20000000000000006d52bc48d39a2900000005feeaca0000f9406a8000441c000a3e00009110622000000039e072600018267b4000017500000002526000063e000000000000000af00000509a4800000000001b5c00000000000000662504c7f09cc28e3903a00012f034a1f4e8ade61600005a4b4ca1363518cdc2fe1e9804d29980c1289e30e0000000196292d12de0002c026a795624a5623a7832316440aeca4a38a243500a6460eacfe07180000000da9000000000009840112d3053b962847b
  | 46 => 0x7000000000000001e310002b1400000006834000035ae0e379484b0000000000030a00000000000bc28305b28408204226e9c0a18623eca26ad6200017200000000000000098c0000000129e00019a88b40000101ad06000295216a202a00024223740e1735c17405e10000517800000010080001c2489d9f6600000002672bd00002a020000ed00c7a25693c14fcb6923d8b4012c643309489838e7e00ca7fa5bb27cf5ca29aa48f80000001708a18800048320ee342a1549e400000000000793a40c9b4a502aff259c82d0000000032c000127e0000b500000000000000000027da7e2800000000007a20000000000000000008eb0000bd400000001eda37fa3660000000000000089f80005480000000000085200003bd83d00e2204448140000000fb2000255a00000007110000000000000fd07c00000007c0400000000000000000000000000026747c3400000018c44732d84b81a4862b2c00021302242c78e94151210603b21a1000226685283de000069200006aa5d7aa381238a8245219c0aac80000000b666c600005908000a458e46460840aa93800054e8000000112f000000000026e00001a206239c5706100008b54c3043b0ecca5086fe427201f5fe82d68574c5c4c502d08da0e560002a109fc934b0000000486000000011f6b2da19c00008c600012ec4ae81f24f49e5400017f49b72578000100a3292ce406c0000926af0c56693cc0001f885ea0000ad2800088280000ad00008aa85a64b2800000000004c19b908de14b0000000093eabaa0000000000206000000000000000000102e9ae85220f38000000000017ad29478b80003e119050e814f8b6deeb8000222000003c36c99d36b9bac1469b80ea1772080b68a99142d262e60d01f04750000000000030d80001a09f4d22900008a6628c1a40000a9f0df8360954500000008e7c00084740003368000471e4d06c88d1d4991d0e12310967e7827e157aca09970bca243995e15e20bc52385c8aef8c1c26800000000000b97800000000000000000a2380000000000a67a3da0000e15000000000000001a88d6400000000c9800000000000000e3a6be880078a8bfa90280000818cec000000036ac00059ea2d47e915a415ed3e8a8380003215422114a73064884d80ac9fe678e94cc75899927f21c9e29d800049b800054727422e0899400025be7af185e00000007b600008568526276a3dc040a5ed0e88c7f97a1c280ca0c908bf0c18732ae0a74ca8e6000095c0002472377414e0000000000000000000000000a625251d5882c8319242000000001dc86c805a42b24363ea884000007de74e0cd60002dfa5d11841638aade00028ce000000000028ac12727e62c90404a871a962aa19290aa98883c308d09f414900001cf88578000a75cbba0001ee32098000000000
  | 47 => 0x756800000000002ac194a00003350001e461586e1a00002666688000528865600013ce560c00000000002c38000a9c09281660000000103e082994800b400095b912a14224a4000235a6e010f454f1ec892200005581a0005b8c9683c29831f597f6b26a7a7a7f8e0c2c885f29120000a5c00dca76c0000000000000000000000009f10ce40000e1846c8000a511c5e474c8568f81d2c0000eec552938075f28d66fbcdd902aa29bb312d883a2836a90e9ace750062894a110627b1e0e72d00009ee400064d800063f24f69bd2ee17b380004009220306800216b2d42762036358900000000e2a424a9dc5c5a74aab099f800023ba0002766600818ca4880000000000b8980000002748b4babc85c7008228380000000000b9f2618aa00f8c0000f320ea80000000b1c000097e8ff0000000000000000001db10c46c28d5a000147a00014167870000000000056e919600000008c713b60db1bd00001d4600000000001cd200024e000000000000000b5c40008ce24cb5028000b510000000000000020380000496000297c240a3b06afaeb4998840e0c6aefc11f83c47d10a4193e0c8144d29486a200002551f2e000230400026362c0161080f83b40002cc20000aa4331a3be302af2e9cb9c7a660adb00000000702299c44480004e32eb0898800000000000001aa2a49000000000004dc2b04af5833343916a600007fa43780000000000000000016a8000671000089d15fe6ff035d00027b02ce861ea36800093300000000000000138600000000bc40003059e4cba5a00a35988a600007b20000e6caf4a51c1af800051e000005f0000b6d00009f4ad3c000000000000000002d4e00018703e71ede2ab859600006543199f91000139ca4086a92d280004dbd9160000c940000e9a00009222bb15b406eaf20000000056380007911c1843b8e0a4ce221665b94a890500009b1077000021baa7202c9000000051800000002c4eadc8ea5b029d5400000004db661000025240000000a6e000034c0b1077d22508fe22b425400005f38000000191079611880000756989aab4000000000000008ae8000000219d0001b7800016a000000000001ce03110000574000063b8000416c0009c30000000249e51a916000018424c5818a000238483bdd242fd61c702b12ccb39946800010228d500000000000000000074c00000002dd2025174e1fa108c34b8fa0000299900026e258381d000003a473700006d41d8a1048000ad31e6e061a0348a9eee900000004de97a648b80000000050000000074203dc57e045e000000042da2f0017987a3678bde3cd2848b81c00000025c40000000536800000027b20000f1ebb180008a91987000000000000000572d9469a8d9cb9c02547d462222d88008aba9ef7b1b896487043b0a34a634000179a749889a0c
  | 48 => 0x508218a6bda15008bacdaaa502be6f60da4080a82e57a9c3c00000000002b56aaf97fc71c00000000000000122c04a8000000000000022ed000000000006f4817000000011300000000544800000000000002350ae42a7632b14580000000000000026618149f5060e97e800002e0000000000025a8daa0000000000187788c01a400000000980000682aedf1cbac661dd2e162b60de447e8d081f8a1906a65d969f5973669529cf0000f4059b13f64f4000000000e4094c0000000000b0413fcb100000476a49818f2d340000000000237e0000000000285400000001d780006d6a70e82fce6076d80002bf8b425ecd79089ca0a600000001cc8f8a79f40005cc80002f980002a7244e0000000445ad8eb960000abb80004c2133c000039c588c00000026520a5cf6483e4000afb00000001f4256563a0000067300009dc6061039b84a25ea060000542255c0000000b77000026b000000000001f61212000195b000296a2ae8000000000000024b00d7c00025e26b866b800000022d60000000337a9a83562c329b0a1387942d760a2ad0e65180002fb40007e3800063f874a0001f49000039a2a5800075e80000000d0e3101794b3a00000c880009cd2a36000038ea1928dc3eb1a47088e010000134e0000000529918b08d00002e4e2409a903ca6035e7c9d5114c245acca32e8000b110000928925d227000057780000001042acb23e2a5d9c223b5c980bc7800080b2b8a66eeed00000eb80001d0000000009aa00009db91d200000002fcade200010fe00002ea000000044b9af4417407e20c8c6e0000000000190877ea45c4c809344e20000338800031cc112000019e000000000019ba0000000b7091cf4bf00000000080000000000000000002282000034a509800092768380001cce0000000853acba000226a0000c3a00021d47c380000000000000000000001fe000135a69e8d4e99e02ce9440f780299d095f9e94e1bf086a6570ea9ae48f2e70b9d480a4936eae50f4c4cc99e20091a38673a6fa19602ae0f19ae42caa73a4e4090a3a180009e1a88a8035424775000046a00004110000000059aaa22c700002226000000000000007a19db2aeea79e2eb12f8923045a8d280000000132993000000028700000f800001f9200014f5880800000000000002d5e3401c2900018e8000000015f0000340c0000002178000250866401df8df14563729c2c4f700008eee92c6842a9095e8ab449a8ba051d225a00dacd2b8c0f88b51a2a84e82ece70123627fb21fa35b929d2ee2e9ab36d752ae0800013b1b2e6d900003718af00000000b64803e76c251e0002bd84bfd2dd4ae05045bc0a3c0959bce814800090800007cd9f8c42a934620b8ec271484923bd5c780d85a983fb1eac0001c1e0ec80001e909705f893ca4e2ae2e2ec00
  | 49 => 0x9242228a1c3d49e7e7c580007de8000000000000014ea0000b9292850fcb2b000032e0f480002af2000000078f21de18b00000000000000047c0000fa2ab340000001c660000000893800029c1a420000000000022265b4620752a18223b9ac92cf0d35304235694a90d280caf222192e2163a976a0a75fb468d8cb62c15dc858e10ef4d98000102173e59bab6e00025fc7df019a6a81d060001aa40cc40000000cbe7320000000089e0002b7400019680d100000001deaa5800008350000482846e0001df611c1a8430099fa88b8e6455497babc71ed60562c5e13d1b6849e400000019206500238a5180002e3ac387052e7800018d03310a720dd0e5202c000a33e9ec27ea62eeb359656915868c56c1851236038212c1c3e20d1efcb020a8c1ad8d156de91fe11508ec9541b001b68ab81200fee0501d8ea681077bb9093a6d05ce4000249000018741892de67dba7bf0001fca000127436b03180002646206a9b4aa1abf63ce11366b66a8e35e22809f3800054d9498aaa813ea0b004a9b511c0237067083e0c2c1c6273eb1180009da190000027221b4a7e2a82959441cac42ab3874e3f5921e801998b3db0306159065c16c1e723b61a900e62eba46f00003ef80000000000a1d1f86000121a1739a92865000000000000e1000032100000000000ac080be0000a4600004687f1000007b17be0000000191800000000004b7cb2648917308d819e54325e9a000000053380000001ab600019c3000000000026fc76700000000000ae6a6aa6ef002f000173447780ba0000000ad6096c974a30c204ab666c6800000013c467c8000000000000000000000f460002cdcace9ffc00000008cb96ac0002c22ae880006ac1d980240ed25ae2b62329a2327882beababa18073588b07a39a264eada1fabc002a57700009b027c6223076a53a090c27a021f428153094b103b0001fa63d08000205ae1400002f2453800063380000000000000155c00000005d1af2aae7804e3582e5c10880000d2e3ea000234600000000000000000187e3039e24ba280002f65de066c25cb00021a091780000000f1a055983b9bc0cea5461cec1401ae68af800000010e6000000045e80007bfc0000001a3c000000000000000001ffe0c9000000000006b8d5ae92500000002f240002bf200000004708372ae300007d758b2000000000019d97ba1938ba084c4000000071a0000000093246308aea41000000017e61e0241c87a183c18480000002a30a9080000000c5b000120300000003ae80005e78000000223600000006aec000b3e9f62b792cd452d800004e80000519f958560a7407baa227a589880810cd2983232c725800068b0000629244600000009d72672000084871d904a00021ac00002eca3f0000000000097506b8000211b8518000000000089b00000
  | 50 => 0x11a991e13a067c36d8c4b77b19a414c87520ae2108b9a14084f6986a5ba1e3e0001c56bbaeaff0001322000000000000000000000808400000020ce00026a00001fa27cc000093c80000002624000223800021120002522000005409126d859f000097de48a00011a360baefe110075ab6e06a8a718000b80901426f1a0c5441a22308a3ee3b80000b7a9aee41b0351838a75a8e5a7cb58b07080002043891800023800007cfae5a4480e4abb51faa00009720d1810e0000000b2d193404213741b98fd06b680000002dc86b200000001680b56a0821f181900191bbabc69f4f5f25ba41269a161a9109e50c12a02b32d8c37014f684ea59885f00000000000a3d8e933d286e2000000000023c009e870e067201a6e318b42b723a40000000034a18c0000f2a0d4805881b03e4000000072a8d5200016de19e9b1eaa6000010000000000000000000000000000000000844000000005da0000a9200017aa0b60ba1000239c39d8c0000025a2000270400000007210c6000005a15f1096044b1444a1aa4da80b82965cf130a06dae4aae1caa63a71f7804ae54800018801620afc21899253052ef0a8000002b100006d2888600000007b98a680be1fe840b0000bd329a60001f50af295586b52bdc46889ee99299699ec47f84f8ab8e0000bb10000000000296233080007071aaa058a0ec0051ac04af2b7c69a000026d0000721e6d00000a8657d51b834d876224528c20000000a0f2458230a0d27f4087e46024bb80200005d40eac0002a845ff87ec3998688255924e81281de6ce81e05fcd2e031caec176897c80000000b872f5224e128c1b2000066100003d68000000000049d4000b5800000000cee2400000360000000000009a7070293ba56046a800084a000044ae00200011ea3872192b90097a57880000de8ddeae908d2000000079daef2bb31fd200000000000d32a6058e068d220c0001dc00002ec04be9d34aac258c6c58b766602392b5e8d741e7a93e00024c2bba0c5e0a1907338b24d813217f10002c7e36d0b481f0000000014920001d4e521aa2c00028e80002758000014445421fe000000005f98663f500a20000d3ca8f2244a0213128b3566885821269c58000b5b8000b450000699a0e60000590a0a18d2000000039207fc159cd760c4c0001ee06e04ee000051703ba136a5ec0b88f70610d1c55312be60002b487a0800e00002480001d788e624768991890194a38085a0ade5d4d2263f18eea394c0003df26f200009f819e2b5a61900004b00ace41a11e2a080000b9596408c22b765142dc60000000030069c00000000000000ae65cd800022700002e6c887820058c80006cfc311425400000026280000376000115a0522a167e71a7eb1480000001fdc7678ae09ba00001651334788942a0000a120001cba0000d90a979
  | 51 => 0xde5c5590f165aba8884078000a702c060a0a9361472e625739b9e463548a2e78df62008048ac289be1f3999a582214234ccc566010a8a7bd82feb2a27ae1646e2096101c298f04c64858fe879ea8581a180000da11ae00008907341c5953c1a8d6a1aae0b258903000105e000000000000000000000173000000004debc98aeaa1f8ca19c68a1800000005999c02000216c2df878e4ad25e78dd8fe4485c37060c63b48deaf3c3ae5e90739959b00000002a1000000000000001f54af396ba1caa1cb5f593ec5af80005d3000042980009b92a283e181a60000fba93aa656846526c58a800088a8000ad90e72adb012eaed00000000000203000081c400000000002d18000000000037440007bea2dc00025d800017420a98b30a2724d484153fa349d86c7bd43e20002e284aa90e92b9066a0d523400002b382f0000060200009608028aaea8bc000000000000000001f7418100001fb9c32000246600017c06bf0000000256c59c000071b800014588ea00000003b9400090429904ee816823d0000000136882208385b2a1bd47d5546b3cae444d89c000d02668ba42464a2d1298372008a0002e3800001380d813bb9bbad860001cf02f60f581689c46afe9f8000000001e30100a5fc00032280005e900000000000a0c80001b38f1400000000b7000080d97d2000000046b16598f79a180000e120000e8c80c4b6c060a0a40bd921c9d900000000000288800000025300000000b0e97540000000426800047717cc7da4000000000067a2d68bbda022320000014ed621000000071f0000000193e8060c5a83f000000000000002bc614680000001ba20d31570a65188a000048401d800094d92b656700001f32a0822da1161ba0b08686821e1778ae81c78b528644b6453d09d865d1fb5b251a9a00015a100000005aa8000000195a8c0aa9a75c00009a31a7c38c1d4400000002b009b610f0362aa094faac212b098b07c87fda99d5c027f454bab3e7749b9400023ae0000fe295d0000000041e3c1132483780000000000a9c8bd2855a7c88d601ae0f4a2bc03b865e0d5a9fa76b2210a1e99f49c9a1bc04280000002ad208602da89212d00001da8b29900600000000000c9200000000000000a5b800000000001d7264800000002b480d86fc4842000125c3bf4a8000000001ca000000008b4a9594804f90694aaa1f7000028127f81f7310b8000728a00400010ba15a10f8ad0a0460002b6a4c30000932a1072cb20fe1d90d2600029f4a30251aafd017a000254c0f09250b5c998e320aee341700000001ebf00000007bba65a000054d1f400003bb949e7c6a1d6326e21451b20be7f3a4783222be800009b2833c9e4755ee8828b0700b5f1318ba81e7b78be4c6246149a7908c788ba1c42238a90859626669589dc20d72e8e797ad4a86e02b6
  | 52 => 0x2cc8e009e888826f456737778da041ba36a00022583b50c0c7eb65448b00d6896a2e86a248e6e0000000480520266f40000000f760000f988b322de4341e516e209d680800000000d02000184a7c780002e900002359540ae580000000d8c000000000013600c580000000000000064200027f65d9000000008aa0000000000000083281200000d542eb86c604900005800432b6780fa0002d74b4b103672b0a3800022f46714000bbb065abaf49825ad00007da1e0458fc0968db800039c00006619f84194152778280007fdc00000000002f90000606904019d8000000000000000f45b909c66cc984c00016528cf19d4649859c00020f144290980001de2b3e00001d41b6a70690fa1ef091c816076e138a90ea8ba6bca62aa9c09c000000ea2b384c9b3488015e83c8130465f06ae67c1e6460700008229d292c5a8165410000000156a8e5000092991d8803ca837f6165a58300001e484489f2aeaca6f0000ba600002c6a9e400028a62df1b960000000515000055b80000000000000000055d4000ae54a5600028242041e1031a104e8890000000148c9e48000000284080bc5391f8123b31300006158baa11720547fb92e6b758000000000000000b22c10ec06b5a6948ab126600029e658280000000b0a3b903b8744800000011c800025c0000196c0001df84ef28507280ff47ab44e00000031af9025076429148a70a58344239a3fa96d228b850c4cde16e74e816a00329bd163c00064a2d22000169c0000dcf6ec1064000000003d815e7f780003cea94a2ea000056f0b06777000099a800000011e9b3269880000a8d000219609380009f66d6a5e19bcc461ab800ce887a8ef2aec49e168a203a3fe1bb96f20e9a2b863b400083600007d61dbe29e96b6048ac8a25606383d500786b18df26ffae1075700007ab80007c80bd400015f40000ae686fa5a6b8100000002a607d689fe00009de0001d3e41da51460ac5ae00000009721d1466b1d7278504e634113738f280000002c92000059e0001d1e14799548bb2890174273c000166400012b208a9f111220b952320000baf00000000dc23c188f83448320000000000003fe0000528748800000029ac0000d3700000f200013de635a4620000000a66ab12795df827c88dad06605249388000000169a00000000d7800000000ce00015be4a1000051f21b000000000000c423f6800000000000000000017c0005558000000112d0001256000197a57609d000000008a865c202300002ec87b400006d6b6f00008e30000631a928a3f95420368000bbe8000000212e00000000000dce0000f2642080007f5917e17b8bbe5798f6e1ab10546d09fc746e966201b9b6e1ce252e00017e8a070486b7a072c6580cc56bc062e6532268b3380008530b7a9f802581be80002bea9be251264447c
  | 53 => 0x28e443a2b200b0a47a05c0000655ad7828696da4416dbe2af9c583ed12ea6758912624a84c192ab11378643c389009c00025bfb3b1e383e4aede0bba10c53880004b60a4ea400d3b8cd14d24c0675610aa67ea039b0c7428264ba7ae3e38ac0000001f267131c77948132c00024e6207ad9c0002242ae740000000ff29d481e6269073e00011048cfa29a0001cfc000000095995f249600007f305560bd23360000000bca2b0e0000f0e0002011a5000b680305820000000b318a903e91321a73ac9c587973829ba61a0750dd6b2ba68e66e0e06b34164fa5a26800001cfa61d8af8bc2052a847a7b409f19da76523a714e1056b71000038400000001a0600000001df15936f68db00000210754086e588adda0000000000031200019b60002a1207d2d404548f3e24b8000126000094f13422d62a2a42b952ca5f9a310000000683e93a0002b1e9e020005df82a15f686b0270a7600000000000049e57baaa421240006ee1dfc0001bf40002ad19620000abd1e263482df0ab5212458e8ed600000001e11f404ba2dc071d40000e18000000000000003d69429a3a3bc0214709ab970001bbeb6089d469781d67ad909903897d0620800022f1e345dd085ab2c9816000219800012701550cc0000000000000000000000000227876d1fb10000000633c0004d4a50062800000a1000000568b00001a0745a9b3635f8de30cfa76a931c3e810d00005e380000001f5e00000000ef8000a1794c8a3d298c33200005c384911c12ed23d88000b3022c8832ce3400021eb00012fe00019e702b87b060891be0000000ae81bcfbc588e400000000000000ba909c400000000b0000000000000001108a3b00fc8a498bc247af060c32ca263d042c934675e76303f49b1aeea000246a5c2a80c82ac000a448000000000014420f40002e3660f453a0000000b321ef0000077655f00009270f3647a1f7556221e46ea2d7ea7d9c0c7dd8c541ce9fb2b2aadde00011406c4233a7d16e3c7f6aa0600000003452f2d43a80000000e3c00012f61e58d4a712800025a000031c17b0b5c199c00029e20002e321c4900000000001600c4654f8000000209a0c399d228a0fcc6f5a8fabbb804c475a9562579a7258c17a018ca3e6a751cde80a182a00028006d4a18f96b2866bb880001de000008f2886a57000039e8aab3749222447175c2fc0c5200000007200000597000012b8bda0000d1a2ace4126680000000000000028145551a6c870ce9e5a1000056600008ca00006ed800088b11295eb99fc551c00081684d250600005b6c0000002c743c9253ab4400007aad3d445e27ec00029d59850b5614392be03413be6a0add87879fb85c683651dc97066aa174aa531bb29410458913044c7ef8552a31a4aaa3422860cd000000001d8945800055d95aaa762872739df6
  | 54 => 0xc20fea0b8b15ad1e0000c2427800002ffee6021d9b728289c940000000a3c98285301d863f72a0c511400000000001188000000201e9b7920e9e315c0000189800019e48489c0e8d08ea143d946e950a8767caadd421199989ad2a5883200de575609e5e01cf4871482019800003fd8000a7b1e3086897cb7208cfe68108b827c2e84000152445d8240aa488fab4d8de04ea9d3fa1380001648576a28094e00004381d616250000000000000070e00000e795500002e72000029f0002c804cd87e629b0000ada2d2883ca31800018b61ab623e87c8b6819d0e1a02481ce18da5dd11da474000037c6b780004649210aa28fa6000000000011a1780025a798978c4ea5b245db134da98aaac8b2400000000009010000224800000016f803c1614000165e13c9ec63c0cbdd7019b4e1ea80007ad062f2cd800000029950001592b7b23208bc5748000289400000004ec95ca00022e42fe4f1c07e92a200011eb394400097718ec4d30d0f22f8bb3000052eba300000109f460002714692a3c2a3a9907976ac04000000000000000000000000000031fa7fc000000000026904691bdc16e85fa62c00007e59fc3a59101229790ce000000078c82780de0d940000a6000027740000d6a5af2a1a00024e80001cb042299066a004a4a779f2800000003eda0fa21714b800009a238b4e6a033267a5f29ad00001c300b800000000b9f000293072e18960002218000225c2e204b60000e597a800000079f084fca7a4ab6000042c00000000000673053638a411e978144092b8822b59800000000000f802748e280009098000281a050000000028022e0b059502000263e23a105f6e69f4310310c8b921b3d027aa9679a0350000193a5931132561d1a00652ea600020e4b9f470a7555884000000059c947238228343aec52c95188a80a3ab525ec8460011a9a400000002d721443139d840000000000000000027deabd9f6b96c16d81cf2312b062bbc5b1285aa4f20fbb78258a63616ea6a28e5050c8000914a5bd7c412440b100004930000216000000022ca28faab827d9dee699069815e80008c4c1d246100009dc84a000021a40000e3600000001e61c9846400001802a64a7a8000b2f096e9d8aad65ef00000000b2800000004f58000000000000010a800007883ba272851d94a400023524d42d26683800051980005bf87605da02e6000280200005f60001dcc000000027e9efe000098c7ebc4f0161000063300000000000492800030f00005e284421b100000001e805ed8000ae722cea2e2402000000000000003fe800000000004e500005bd80000000a4c8ed80003af800000002ca9579d7e1faa4287ac8000776836bb3318943b200001f905b844a1a7400620b68709e740000da70bf0ff0bc01644214208c00000000000000409246c48f000000
  | 55 => 0x2c1c5c5044e5aa1bee0000000000259400001064010b0c00019c80002ae80ed86a65d8868da740000724800060cc00090900003ac86340001496018217e00000006dd2b24000000000022f8000000082b95440aa02ac0089aac31e9b5650e1ad82ef2654000142817000007ed9bd415a800000000009b59174af520487d2c436809213ebc39e7024426ac8a528c87c280008ce604e3520fd807a00000a7147000f6ef47f187220fba950a14800052f80002fed64eaeb80006509dce93100000002a7847c698400000001052e4c440000000000002b1af2c8ea2e9c4e68000000000084a91b04a915800001a2e644800037300008b105ea00028ee4729214156cb60b6e6da65790efb000066400000000001c5a00008d445792460000e4c5859fd4a59881c5f6133e390a11a07684f80a00b78b2187c41129b1c64388a07da9b844854a2a9ad8000452800015dd121406800038f80004c780001baac5400013a879e23e44c8dae8a9d1ff42c828968ca9488a71000000000000010000a1e000000000009a88000000000000025c9a4785bebb5800036a17d422396482f883e6428a28b7592cb0bc1154c5a49c2565fa7981639e4800008249efa2d23459fea2bda8aa015966a062034f13716c295fae1e64c00c6713a0a09102e7492e21d7b0f80006a6d44e0001b306c20000054ae2a6d9867e000216a000125e00019b20000000090a6844eb80000000000000218e0000000043562e50b00000002554000000000000004a48ca041199eaa38219f881ed560000000000000019880007f0214000004b4000175a0000000000192700000000002b18a2882a74c39e7fb472496a7327f8000215287610d8570800000000000001ea698c8b7200000009038ae26aea1794240ec4a230000697219e0000000000000000014425a88000878800012569ca45880002fd27c21528b384438cf02e7000098188360000000000000097d00000000000000274000005a50000000ab91dd80000000000092423c17c645b2e340000000000000000000009a6000000000003978a330001a490001aa60000000000029a00000003541f7e00027b632ca5f60002830b8300002ff4fc03b9846400004a600000000000000000000037b0bdf0fb269a0000000836a2d858495296cb07ae3b756466d88000153dcb2acd81be42740007ea12422e68104a4980006e08000000000077fa416bd000006fc800000000000002db61b79f13000097c000000015d2d8a1a684440000000ab8990c97296fa975c0005b392dc29106f23e58000267a1e0b0a025e3b180007b82c4a0000482b66800037e94c60001fe43970d0c09d8000000163e2d68000000003862a1146754a39e3c40dbc54980005ac800019a2e460002d48000128a16f1e6a0002c1200004f61d024d6265843e6e49b
  | 56 => 0x21e99a987d433295f69e380000002ab687b99320001030000000000017f23b8da940000000bd2825200000000000ac200003c80002ac8000000075a024c3661baa28302a454795e087540009a1ac500000e9800016710a7800098280005a09a4c29226ca426c00000007360001ab489300004d5ad903b706c245b9af820c0348b2380004551f3a835ae7a00012c411e0c5887b40000b79a21000000000f0000809800000000c4a15a6eab7d94067e51382aa325a400020c600018d48ba8b9600008f28b7c71a000169e00000c80
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8ec825c563080010fd0fa8ac61003e1f21f5158c200043f43aa2b18400087c87545630800187eeba0ac6100030f1d74158c200061fbaa82b184000c3c7550563080051bd0f18ac61000297a163158c200052ec2c62b184000c5c758c5630800153d0918ac610002a76123158c200146e43a62b184003acc824c563080014bd0a18ac610002976143158c200062e3a862b184000a9e840c5630800153b0818ac61000eb3a083158c200156d40062b184003ace82dd56308083c9d05baac6100039360b7558c200052ec0eeab184023e4f20dd56308047c9a41baac61008a97a167558c200062fbaceab184023a5e871d563080018bd0e3aac61010317dc87558c202062eb90eab184000a5d811d563080458bee03aac61008b175c07558c2011727900eab184022e4d201d5630800759d05ba2c61000297a167458c200052ec2ce8b184000a5f855d163080014b90aba2c61000387d525458c200052f42ce2b184000a5d859c563080018b8eb38ac610002a7a127158c200054ec24e2b184000a5f855c563080014b90ab8ac610002b3e097158c2001d66412e2b184000a5e851c563080014bb0a38ac610003171d47158c200054f420e2b184000a9d841c5630800759d0438ac610002b36087158c200156d400e2b184000ad9801c563080014bd0fa8ac6100029721f5158c2050727906a2b1840a0e4d20d4563081434bb0b28ac610002a7a125158c200054ec24a2b1840008df8754563080011b90ea8ac610002b3e095158c2001d66412a2b184000c5f8754563080014bd0ea8ac6100029721d5158c200062e43aa2b18400085c875456308001c9f04a8ac61028b932095158c200072bc0aa2b1840a1e4f205456308143c9a40a8ac61028297a145158c200054f420a2b184000a9d841456308001c3eeba0ac610003871d74158c200070fa8e82b184000e1d51d05630813bd1e41a0ac610277a34834158c200052f42c82b184000a5d85905630813d53b0920ac610002b3e094158c2001d6641282b184000e1f755056308001c38eaa0ac610003a3e094158c204ff4641282b184000e97815056308001c3ea2a0ac610003875454158c204f74790282b18409ee8d20505630813dd2e20a0ac61027ba54414158c200052f42882b184000a5d85105630813b53d0820ac61000a37e1d63d4c200052fc2ac7a9840058ed825da530801f4b90ab1ca61000f339c96394c2002e6731ae52984000ccd635ca53080470ff0abb2a61000a3721d6354c2007c3e42aec2984000a5f8558c530811f8bcc73ae86102331798d75d0c200146fc3ac7a184000c5e7558f43080018baeab1e86100163b6097690c2001e67392c72184005cce635ca430800199ac6b94861000a3720f7650c200043fc2aeca18400f87c855d943080051b90eb1a861000a3760d7610c20
  | 1 => 0x8c9a9a6490016b3218534c9203f726328a69924000e8c6414d324800739d0fa1a6490002b3a1b434c920005a742e869924000e4c65d0d324804dd18c9a1a6490016b3218434c92000726328869924026e8c6410d3248001ad0ebb8264900035add4704c9201c43fc2aeca8240008bf845d9504800d17908bb2a0900e71b1cb65541201ac5f436e8a824000c3f65dd15048001878cbba2a0900da2fa1874541200061fb28e8a824000c3c651d15048095b50403a2a0900022fa1f64541201b45e43ec8a8240008be87191504800d1790e322a0900031bd9772541200043fc2aeca02400f87c855d9404805b17f08bb280900de1fa1b755012026e1e326eaa02403987e861d54048097878c83aa809012e1fa1f65501201cc3e43ecaa02404d87e87195404801f0f90e32a80900030fdd764501200061e3aec8a024036cac72d91404806f8dce432e60900d72b9c864cc1200063632ae59824000cac645cb304800b998c6b96609000ab321932cc12001e663b2659824000b4c854cb3048001c98ca9966090003a319132cc1200043fc2aec982400f87c855d9304800117f08bb2609001a2f211764c1200047bc0aec98240018f4815d930480b70fd0fb2a60900e61f21f654c1203643f438ca982400f87c87195304808d17d0fb2260900da2f21f644c1200061fbaec89824000c3c75d9130480a117d0e322609001a2f21c644c1200061fba8c89824000c3c7519130480051dd0db92609000ab3219324c12001e663b2649824000b4c854c93048001c98ca9926090003a3191324c120015e440264982400187d855c665080011bf06b8cca100163720d719942007e3ba8ae33284003a6c82546650801f8eee2a8cca100061f21771594200046fc1ae2b2840058dc835c565080371df04b8aca1000e3b20971594200143e43aa2b284003a6c8254565080018eee2a8aca100062f213715902001c76412e2b2040028bc87505640800196ee2a0ac81000a1f21d65550200145e43ac8aa04000e1f5495263081434bb0b28cc610002a7a125198c200054ec24a331840008df87546630800b1b90ea8cc610002b3e095198c2001d66412a33184000c5f8754663081478b90ea8cc61000393e095198c2051726412a33184000e578154663081414bd0a28cc610002a7a105198c200054ec20a33184000e1f51d066308001c3aa3a0cc61000297a164198c200052ec2c83318409ea9d849066308001d2f02a0cc61000387d454198c200070ea8a83318409ee9710506630813dd2a20a0cc61000297a144198c200052ec2883318409da9e8410663080071dd05baac61008f1760f7558c2020e37416eab184000c6d82dd563080010fb03baac61003f1760c7558c200043ec08eab184022c6f201d563080458da403aac6100021fe157158c2007c3e42ae2b184003
  | 2 => 0x764d092003557436c92124000cae76d924248001c5eca32484900038b1946490920004b642ae72124026cac645ce4248001a9f0ab9c8490003532157390920006a7b2ae72124000d4c655ce4248001b1ec8b9c849009b33991739092013666322e72124000d8c645ce424804d918c8b9c849000353d457390920006a6a8ae72124000d8f415ce4248001b1a82b9c849000f33d81739092001ee5b02e72124000dca105ce4248001b9220b9c84900b72e1c3645092001477434eaa1240029ea809d542480718d8edb2a84900e35a1c36550920186363b0caa124030d6870195424805b958edb2284900b76a1c36450920036563b0c8a124000e2f651914248069b50e0322849000a7aa1f705092016ed5ba0e0a124039e4e32d97324805355d0932c64900029be04658c92000536c08cb1924000e2f411963248001c5a8232c64900a63b219748c9200071632ec91924000e2f651923248001c58ca32464900d72ba1c648c92014e56c38c91924029e8e831923248053d1b0632464900a6abe04648c92000556c08c91924000e2f511923248001c5aa232464900c21fa1b754c9201c43f430ea992405a87e87d953248073c9865b2a649017a1fa1c654c9201bf26190ca9924000c3f75d913248001878ebb2264900dba30cb644c9200061fba8c89924000c3c75191324806bd1864322649000eb3a0b634c92000537436ea992405ec6c76dd532480bdc98c7baa649000a3ba1a754c920004b742cea99240029ea809d532480b58d8ec3aa649016b9318c754c9201c4b7430ea992400096f811d532480012db023aa64900034bd04754c92000696a08ea9924040c6f601d53248081ad6c03aa64900035a840754c920006b4880ea992400096e87d9532480718d8edb2a64900163ba1e654c9200053742cca9924026aae84995324800b59d0732a64900c31b1d8654c9202f537438ca992407ee4f8319532480fdc990632a64900df1bdcc654c9201bf27b98ca9924000a6f8119532480014db0232a64900038bd04654c92000716a08ca9924000e4f311953248001c9a6232a649009b2b193744c92001476432e8992400096c855d132480053d100ba2649009aaba1b644c92016e563b6c89924000d2c75d913248001c58cbb2264900d32b1d8644c920006963a8c89924000e2f651913248001c58ca322649009b2ba1c644c92013656c38c89924000e2f751913248001c58ea322649009ba3e0c644c92013746418c89924035caf73191324806bd1ee6322649009aabe04644c92000556c08c89924000e2f511913248001c5aa23226490003a3cc4644c92000746988c89924005ace86d8d3248001c98cbb1a6490003a3193634c92000727b28c69924000e4c6518d3248001d1ec831a6490003a3190634c92000567436a6992407ee4c65d4d3248001d1
  | 3 => 0x2b1a4001cb47150563480011dd0f90ac690007391c72158d2000c7643a42b1a4001ce47148563480039e0e3082c6900063e21d1058d2000758a0a20b1a40008df8758c63480015a902b18c6900161f21576d4d200045fc22eda9a40068bc845db534800b4bd07b2ea69000e3b20a7694d200045fc22ed29a40068bc845da53480014bb07b2ca6900e71b9cb6594d201be37390cb29a4036cae72d92534806b95ce4324a69000387d935394d200070e326a729a4000c6f655ca53480018d8cab94a6900032bd917294d2000656322e529a40068be84dd9534800117b09bb2a6900022fe117654d200345e422eca9a40008f7815d953480031e902bb2a69003e1f2147654d2002c3f43ecaa9a4039c6c72d9553480051dd0db92a6900031bd977254d200045fc22ec29a40068bc845d853480014bb07b28a6900d72b9c86414d2007e3632ae429a4000cac645c853480010ff0abb6869003e1f21576d0d2002c5e422eda1a400087e869d7434800d878c93ae86900021f21975d0d200361e322eba1a400087f87d9743480010fb0fb2e869003e1fe1c65d0d200043ec38cba1a4000c3e75d93434800187aebb26869000a3b21972d0d2001c76414ed21a400087f855da434801f0f90abb486900e71b9cb6590d201be37390cb21a4036cae72d9243480012d90ab9486900031bd957290d200063632ae521a4000caf645ca434804d958c8b94869003e1fa177650d200043ec2eeca1a400087f855d9434801f0f90abb286900023de057650d2000c7a40aeca1a40068bc841d9434800b17d0fb2286900021fe157610d2007c3e42aec21a4037c6e7219443480018d8cab90869001b2b1917210d2000566c1ecba924038d6a70d9752480014db0fb2ea4900031b61f65d49200072741ecba924000e4d83d975248001c5e83b2ea4900038b50765d4920186373b0cba924030d6a70197524805b95cedb26a4900038bd9764d492016ed5386c9a924034cae761935248001c5eca326a4900d36a9c064d492000477c3ac7a924000a6f8558f52480375c902b1ea4900c35a9d670d4920014f5c3ae1a924038c7870d9552480051db0fb28a4900031b9d7651492000566c1eca2924000b4e83d9452480614db0fb28a4900e31b61f65149200072741eca2924000e4d83d945248001c5e83b28a4900038b507651492000477c3aca2924039a6e8619452480018dcec328a49000a7a201741492000717b2ec82924000e2f6519052480014dd0daa0a4900c2da201541492000537c2ac6292401aae48158c52480014dd0d298a4900029ba18531492000726b18a6292403887e869d7424800d878c93ae84900c21f21975d09200361e322eba124042d68205d742480710ff0fb2e84900021f61f65d092007c3fc38cba12400087d87197424800187cebb2684900030f5d
  | 4 => 0x44800187ae2a88c89001a2fa1c51191200045ec38a232240a5a3e85144644806b55d05988c890002ab60b31191200345f43c6232240008bd878c4644800147d0b188c8900028f61631191200345f4386232240008bd870c4644800147d0a188c8900028f61431191201ad57410623224000aad820c4644806957500188c890002ae60031191200345f43c4232240008bd87884644800147d0b108c8900028f61621191200051fc2a403224000a3c85480644800d17d0f880c8900022f61f10191200051f42e203224000a3d85c40644800196ae3880c890002abe0910191201ad56412203224000cb571440644800d0f90abb6a89023e97a0f65d51200051ec2ec9aa240068bc845da544800147b09b2ca8900e71b9cb65951200051f436a92a2400fa3c86d52544800187cedaa4a89001b0f1db549512001476432e52a24000c6f655ca54480053d100b94a89001637a0e76551200046ec1cecaa2400687e87d9554481194bd07b2aa8900e71b1cb65551201c63c386caaa2400f8be87d91544806d958e5b22a8900b72e1c3645512001477436e4aa24000c6f65dc954480071f50db82a89000a3b219721512003656322e42a24000acd820c763480015b30018ec690003ac50510d8d200061fb2ce931a4000c3c659d2634800187ecaba4c6900030f1957498d200061f3aec931a4000c3d75d92634800187cea324c6900030f5d46498d200043f43ecab1a4000c7471d9563480010fd0e32ac6900031d1c46558d200061fb2ee8b1a4000c3c65dd1634800187eca3a2c6900030f1947458d200045f43ec8b1a4000c3f75d916348001878ebb22c6900032d1c76458d200045f438c8b1a4000c3f751916348001878ea322c6900032d1c46458d200063bb2ee2b1a4000c7465dc5634800196ec9b8ac6900032d1937158d2000636c16eab1a400087d81dd563480010fb023aac6900030fdd77458d200061e3aee8b1a40008bd81dd1634800187eea3a2c6900030f1d47458d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200063bc2ee2b1a4000c7485dc5634800196f09b8ac6900032d2137158d200043fc2ae2b1a400f87c855c5634800117f08b8ac69001a2f2117158d2000477c12e2b1a4000c77751c563480018e8ea38ac6900032ddd07158d200065a3a0e2b1a4000ce7721c563480010fd0fa8ac69003e1f21f5158d200061fba6a2b1a40a5c3c74d4563480018eee3a8ac6900071d1c75158d200043f43aa2b1a400087c87545634800187ee8a8ac6902930f1d15158d200063bb8aa2b1a4001c7471545634800117d0fa0ac69001a2f21f4158d200061fbae82b1a4000c3c75d05634800196ee3a0ac6900072d1c74158d200045f43a82b1a40008bc87505634800187eeaa0ac6900030f1d54158d200065bb8a8
  | 5 => 0xdaae60071d91200061fb8ea3b224000c3d71d47644800117d0f28ec8900022f61e51d91200054fc1aa3b224000a9c83547644800155f04a8ec8900daab20951d91200070fc1aa3b224000e1c835476448001c5f04a8ec8900038b20951d91200071bc0aa3b224000c3f71547644800187ae2a8ec8900022fa1c51d91200045ec38a3b2240008be878c7644800117b0f18ec8900028fa1631d91200051ec2c63b2240008be870c7644800117b0e18ec8900028fa1431d91200051ec2863b224036aae820c7644800155b0418ec8900b6aea0031d91200055cc0063b22402d8be87887644800117b0f10ec8900028fa1621d91200051ec2c43b2240368be87c43644800117b0f886c8900028fa1710d91200051ec2e21b224000cb771c43644800196ee2886c89001b0f19275991200361e322eb3224000c3e75d92644800187aebb24c8900021fa1f65591200043f438cab22400087d81dd564480010fb023aac8900030fdd774591200061e3aee8b22400087f855c5644801f0f90ab8ac8900022fe1171591200046fc1ae2b2240058dc835c564480011df04b8ac8900021fa1f515912007c3e43ea2b22400087e8754564480010f90ea8ac8900022fa1f41591200061fbae82b224000c3c75d0564480031790ea0ac8900030fdd541591200061e3aa82b224000cb771505644800117f0eb20c8900028fe1564191200051e42ac832240008bd819d8644800153d07b28c890002a760f65191200061f3b6ca3224000e1e83d946448001c3b07b28c8900038b60b65191200051ec0eca32240008bd87994644800117f0eb28c8900030f9d865191200051ec08ca3224000e2f655c86448001c58cab90c8900022fa1b71191200061fb2ee23224000c3c65dc4644800187ecab88c8900030f19571191200045fc3ec23224000cb571d84644800117b0f308c8900028fa1661191200051ec2cc232240008bf87584644800147f0ab08c8900028f21561191200054fc1ac23224000a9c83584644800117b0e308c8900028fa1461191200051ec28c23224000a9e83184644800153b06308c8900032d5c461191200051f436a23224000a3c86d44644800187ceda88c8900028fa1951191200051e432a23224000c3e76544644800155d0d908c890003695c721191201a556432423224035ab8864406448001b62e2880c89001a2fe0571191200365bc0ae23224000cb7215c4644800196842b88c8902978b9cb511912052f16b96a232240a5c3f71d44644800187ae3a88c89001a2fa1e51191200045ec3ca232240a4a3d85944644800153f06a88c890002a720d511912000557c12a23224035aac825446448001c3f06a88c8900038720d511912000717c12a23224000e2c825446448149c5ce4a88c8902938b5c951191200071bc0aa232240a4c3f715446
  | 6 => 0x51f424c232a4000a3d8498465480010ff0eb08ca900028fe1161195200051e422c232a4000a5f8358465480014b906b08ca900021f61c61195200051f420c232a4000a3d8418465480014bd06308ca900029760c61195200063ab88c232a4000a3e86d04654800187ceda08ca900028f21941195200061f3b28232a4000a6e86c8465480614d90c908ca900de9e219101952000798a0a2032a400fc3f749d0654801f8bee7398ca900029b60a731952007e36392e432a400087d879c4654800147d09388ca900028f61271195200052fc1ae232a4000a5c835c465480014df04b88ca900de9b20971195200062fc1ae232a4000c5c835c465480018df04b88ca900031b209711952007c3fc0ae232a400fc77815c4654806f4dd05a08ca900029b60b4119520007174168232a4000e2d82d04654800187ee3a08ca900030f5c7411952007c3f43c8232a400087d87904654800147b09208ca900038de0541195200061fb8a8232a4000c3d71504654801f0fd0e208ca900021f61c41195200051f4208232a4037a6e82cc465480014db05988ca9003e1fa1e31195200043ec3c6232a4000a3e848c4654800147b09188ca9003e1fa1c31195200043ec386232a4000a3e840c4654800147b08188ca900de9ba08311952000536c106232a4030a7a800c465480014f300188ca9003e1fa1e21195200043ec3c4232a4000a3e84884654800147b09108ca900028fe1170195200051e422e032a400f87e87c4065480010fb0f880ca900028fa1310195200051ec262032a4000e3541c4065480014df04880ca900de9b20910195200071aa0a2032a400087f855cf644801f0f90ab9ec8900028fa1641d91200051ec2c83b2240018bf87507644800196ae2a0ec8900028fa1441d91200051ec2883b224000a9e83d97644800153b07b2ec89000387a0f65d91200070ec1ecbb224000e2d82d97644800147b03b2ec8900028f60465d91200061fb2ee3b224000c3c65dc7644800187ecab8ec8900030f19571d91200065ab8ec3b224000a3e85987644800147b0b30ec8900028fe1561d91200051e42ac3b224000a9f83587644800153906b0ec8900028fa1461d91200051ec28c3b224000a9e83187644800153b0630ec8900032d5c461d91200051f436a3b224000a3c86d47644800147d0ca8ec8900028f21951d912016d5643243b224036ab8864436448001b66e2886c890002a7a0f75d91200054ec1eebb22402daad82dd7644806d57301baec8900030f5d475d91200051fc2ae7b224000a3c855cf644805b55b0439ec8900028fe1572d91200051e42ae5b224000a3e859c7644800147b0b38ec8900032de0571d91200051f428e3b224000a3d851c7644800153d0638ec890002a760c71d91201b557410e3b22402daad821c7644805b5750038ec89
  | 7 => 0x314144365480014bd07ba6ca900029760f74d95201c536c16e9b2a4039a7980dd3654800187ae83a6ca9000297a0c74d95200052ec18e9b2a4038a6d821d365480714db05b9eca9000317dd273d95200062eba4e7b2a405ac5e729cf65480bd8b8e539eca9016f179c273d95203662e384e7b2a4000c5f875cf65480018bae639eca900e29b60873d95200072739ae5b2a4000e4d735cb65480014bd07b8eca900029760f71d95200062f39ee3b2a4000c5d73dc765480734dd05b8eca900e29b60b71d952000636b96e3b2a4000c5e83dc765480018bb07b8eca900031ba0b71d952000636c16e3b2a4000a3e849c7654800147b0938eca90003179cd71d95200062eb9ae3b2a4000c6d725c765480018ef02b8eca900028fa1071d95200051ec20e3b2a4000a5e831c765480014bb0638eca900e69ba0871d95201c536c10e3b2a4038a7a801c765480734f30038eca90003879cf41d95200070eb9e83b2a4000e2d72d07654800187ee3a0eca900030f5c741d95200043f43c83b2a400087d879076548001c3ce6a0eca90003875cd41d952000716b9283b2a4000e3781507654800187ee2a0eca900030f5c541d95200043f43883b2a400087d8710765480010fd0f18eca900021f61e31d95200051f42463b2a4000a3d848c765480010fd0e18eca900021f61c31d95200051f42063b2a4000a3d840c765480734dd0418eca900029b60831d95201c53d40063b2a4000a79800c765480710fd0f10eca900021f61e21d95200051f42443b2a4000a3d8488765480730fd0f886ca900021f61f10d95200051f42621b2a4000a3d84c436548001c6a83886ca900038d50510d95200061fb2ce932a400fc3c659d2654800187ecaba4ca9003f0f19574995200045fc0ae932a400fc3f515d2654801f8eea2b8cca902930f9d151995200061eba2a332a40068bf87d06654800117b0fa0cca900022fe1d41995200045ec3a8332a4000c3f75dd1654800117b03ba2ca900030fdd474595200043fc2ae2b2a40008bf845c5654800d17908b8aca9000237e0d715952002c6e41ae2b2a40008ef825c565480010fd0fa8aca900030fdd3515952052e1e3a6a2b2a400187c87545654800187ee8a8aca902930f1d151595200063bb8aa2b2a40008be87d05654800d1790fa0aca900022fa1d41595200045e43a82b2a400087f87594654800147f08b28ca900028f211651952007c3e42ae232a40008df835c4654800b1b906b88ca9000e3b209711952007e3ba8ae232a400087d87944654800147d09288ca900028f61251195200052fc1aa232a4000a5c8354465480014df04a88ca9000297a0e76195200052ec1cec32a4000c5e839d865480018bb073b0ca900021f60676195200043f436e232a400087f87d8465480018eae3b08ca900021f61e61195200
  | 8 => 0xbb9ac9900062f21d41593200065bb8a82b26400687c855db54c80051d904bb6a99000e2fe1d64d53200051fc2ac9aa6404287d8799654c80070ff0eb2ca9900028fe1165953200343ec2eecaa640028ec825d954c80870ff0eb28a9901071b14b7558f200065bb8a82b1e4001cb47150563c80031b90e98ac79000a3b20976d4f200052fc2ac7a9e4041c6c525da53c80078dce532ca79000297e0d6594f2011d36412cb29e4003c6e7259653c80051d904bb2a7901031b1497614f2011536412ca29e4040e4c5258c53c811f8bcc73ae8790003179d563d0f2001e67392c7a1e4003cae7259243c80012d90ab94879000a3ba0b7650f2001477c3acba964041e4c63dd532c8081c98c63aa65900025be04754cb20004b6c08ea9964000d2f411d532c8001a5a823aa6590016b3a0e654cb2013476c36e8996400096c855d132c800759d0da9a659000eb3218534cb203f727328a69964003ace86d0d32c800169d0ba1a659000eb3218434cb201374732086996403887f8759750c80610fd0f32aa1900030f99474543200061eb28e8a86402d8bf8759340c809787cc83aa81900030f1d56450320005a642a65986400287c855ce658801f8eea2b8ccb100029720d519962000537c12a332c40008df835c5658800b1b906b8acb1000a1f21d51596200052e41aa2b2c4000c7771545658801f0fd0bb9ac9100021f61773592200046fc1ae2b2440058dc835c564880051790ea0ac9100032ddc541592200147c402ecaa4400287c87595548800d47908b2aa91000a3721d3158e2000567c1262b1c4000eb14144163880014bf0ab1ea71000a1fe1d6594e200052fc1acb29c40058ef865ca53880018dccab94a7100031b5957294e2002c77c32e521c4005cce635ca438800199ac6b9487100c21fe1d65d4a201c43f43ccaa9440348bf8759342880b58bcc63aa6510003171d5634ca200066739ae5b2a4000ccd735cb654800b1bd07b8eca900023760f71d952001476c16e3b2a40a8c5e73d4765480018bae7a8eca902831b5cb51d95200051f424a3b2a4000a3d8494765480014db0528eca900061fe1d51d95200052fc1aa3b2a4000a5c8354765481478bce6a8eca90003175cd51d952000537c12a3b2a40a1c6d7254765480018eae2a8eca900028fa1051d95200051ec20a3b2a40a7c9e73d07654800193ae7a0eca902772b5cb41d95205364f39a83b2a4000c9d73507654813d95ae4a0eca900031d5c761d95200051f424c3b2a4000a3d84987654800147f08b0eca900028f21161d95200052fc1ac3b2a4000a5c83587654800147d0830eca900028f61061d95200052f418c3b2a4000a5d8318765480018eae230eca900028fa1b41d95200051e43283b2a4038a6c864876548001cc8c290eca900e69e21910d95200073830a21b2a4000f
  | 9 => 0x754c84020e37316ea9908000c7661dd532100010fb0c3aa64201031b988754c8400063b308ea990800087e87995321001f0f90f32a64200021fa1d654c8400043e43aca9908000c6f7558932100018d8eab1264200032bdd1624c84002d6641ac499080028ed825d8321000159f0c9906420002b3619320c84001e67bb2641908000ccd764c83210001c9cca990642000393595320c8401aec63a2641908076ec6614c8321000d56d09baac22002aad61375584400355a424eab0880a5e34549d561101434eb0f3aac2200038de12755844052f1a424eab0880a5e36749d56110001c6ae93aac2202978d10a75584405071ba04eab0880a0e35409d5611009356f08baac22001aad21175584405271a2a2eab088000ae7825d561100015c904baac2202a6bce01755844001578402eab088000c77875d56110001c6f08baac2202938d21175584405271b3a2eab088000e35745d56110001ccf04baac2200039920975584405271a212eab088000e73805d56110143ce100baac2202878dd01755844050f1aa02eab0880a0a76851d5611000d56d083aac22002aad610755844024d5bc3ea8b088000ab587d51611000d56d0baa2c22001b8da1754584400071b3aea8b088000e3575d51611000156d05aa2c22011eade03545844023d5ac06a8b088047e3750d51611008fc6aa1aa2c2200029da1772584400053ac2ee4b088006ab684dc9611001556b09b92c22001aad212725844022d5bc22e4b088006ab4845c961100014ed0a392c2200029d61472584400355b420e4b08800aab5841c961100015ad06392c220002b560c725844001579400e4b08800aaf1801c9611000d56d09a92c220002ad61352584400355b424a4b088000ab5849496110001c6ea9292c220002b5a0e52584400056ac1ca4b088002af28094961100015e301292c220002ade1152584400355a422a4b088006ab4841496110001c6ea8292c220116ade1e42584400055ac3c84b088000ab68590961100015690b212c2200038d9d642584400071abac84b088000ab6839096110001d2d07212c220002a5a0e42584400074ac1c84b088006ab682909611000dd4d05212c2200b6ade02425844016d5ac0484b08802dea720909611005bd4a41212c22001aada1232584400055ac2464b088029ea4428c961100014ef0a992c2200029d21532584400055bc2264b088006ab4844c9611004dd4884992c220002ade1032584400355a42064b088000ec5320c961100070f90aba4cb9003f1dd4571997200052e41aa332e4003a6c8254665c80011bf06b8acb900163720d715972001476412e2b2e40a0c6c72d4565c80030f90ea8acb900029720d515972001d36412a2b2e40a1c6c7254565c80018eee2a8acb902772b1cb41597204f65639282b2e400f87e85dcd64c80010fb
  | 10 => 0x3108000ae9800c6621000b1bd07baac4200023760f75588400345e422e2b1080358bc8750562100051dd0f10ac4200029ba16215884000536c2c42b108006aae8488562100051d90e90ac4200029ba14215884000536c2842b108006aae84085621000159d0610ac420002b360c21588400157540042b108000ace83dd5621000159b07baac42001aaba12755884003556422eab108029cac74dcd621000d55d0939ac4200029be1573588400053642ae6b108006aac845cd621000199ae639ac42001aab21371588400053742ce2b108000a6d859c5621000d55d0938ac420002ab612715884000557c22e2b108006aac845c562100014dd0a38ac4200029b614715884003557420e2b108000aad841c5621000159d0638ac420002b360c715884001575400e2b108000ae9801c5621014bc5e83a8ac4202869b616515884003557424a2b108000aad8494562100011df0ea8ac4200023b21d515884000567c1aa2b108000acc8354562100018df0ea8ac4200031b21d515884000727c1aa2b108000e4c835456210001ccf02a8ac4202938bd05515884050537428a2b108006aae84145621000155b0828ac420002ab21d415884003557c0a82b108006ea7815056210001c5ea2a0ac4200038b54541588404f75388282b10809eea51050562100014dd0b18ac4200029b61631588400355742462b108000aad848c562100011dd0e18ac4200023b61c31588400053742862b108000a6d850c5621000d55d0818ac420002ab61031588400157540062b108000ae9800c5621001f87ccaba6a42001b279d163d48400064eba2c7a908006cae7458b521000195ae8b16a42001b0f9d165948400061eb2ae92908003cae625d252100011bb0d39ca4200031799673948400062eb2ce72908000d1f549ce521000799cc539ca4200033598673948400046fc32e72908000c5e655ce52100018bacab9ca42000f3398973948400066b30ae729080058df8798e52100011bb0f31ca42000237e1d63948400046ec3ac72908000cce7358a521000199ae6b14a4200031e59570948400069daa2e12908003cea625c252100050f90bbb2a4200030f597745484000657ba2c4a90800287d855d8521000187aedaa0a42011a67e1a739084042ccec34e72108085d1e659ce421010ba3acb39c84200d76398a739084042ec6b14e72108085c9f619ce421010bb2cc339c842000327586739084042ecab0ce72108000d1f519ce4210001a3aa339c84200db27982739084042ecd304e72108035e8e7358a421006bd1ae6b1484200d72bdc5629084000656b8ac52108000e2f5158a4210001c5aa2b14842001b0f9d1658c8400061eb2ae919080359ac825d2321000795cc4ba46420003275d1638c84001476416ec990800087f855d9321001f0f90abb264200021f61b
  | 11 => 0x100014bb07394ca202970fd07719944050c3ec3ce33288006a3e849c6651000147b0938cca200029be09719944000536412e33288000c6f825c665100018d904b8cca2003e1fe05719944007e3bc0ae332880a4c3f415c6651000d47f02a0cca2001b8de0541994400061fb8a833288000c3d71506651013dc6e20a0cca2027b8d441419944007c3f43c43328800087d87886651000d47d0910cca200028f612219944007c3f43843328800087d87086651000d47d0810cca200028f61021994400052f418433288000a5d8308665100054f50010cca200029e60021994400345e426e2b2880068bc845c565100011df04b8aca2000e3b20971594400147c402e2b2880a5c3c74d4565100018eae3a8aca2000a1fa1e51594400351f424a2b28800287c875456510149878e8a8aca200029be09515944000536412a2b288000c777154565101410fd0e28aca2001a8fa1051594400045e43a82b288006a3e849c965100014bd07392ca200029760e72594400153d404e4b288006a3c845c9651000d47909b8aca202970f1d371594400061fc26e2b2880a5c3c84dc5651014b87e83b8aca202861f61e71594400351f424e2b288000a3d849c5651000147f08b8aca2001a8f21171594405261e3a2e2b288000a6f825c565100014d904b8aca200029ee0171594400153c402e2b288000c3f845c5651014987908b8aca200031be09715944000636412e2b288000c77815c5651014987e82b8aca200031ee01715944050e3c402e2b2880a087e871c5651000d47d0838aca200028f61071594400051e43a82b288006a3f81505651000dc6f02a0aca200030fdc541594400061eb8a82b28809ee3710505651013dc6a20a0aca200021fa1e21594400043ec3c42b288006a3e84885651000147b0910aca200021fa1c21594400043ec3842b288006a3e84085651000147b0810aca2000297a0c21594400052ec1842b288002a7a8008565100014f30010aca2001a8f61576d50400345fc3acbaa08006a3f87597541000d87f0eb2ea8200028fe0565d50400051ec0acbaa08000c3f71597541000187ae2b2ea8202978bd07519884050d36c2ca33108006aae84946621000155b0928cc4200023be1d519884001c7643aa33108000acf83546621000159906a8cc4200031be1d51988405163643aa33108000e4f835466210001c9906a8cc42000399e05519884052717a0aa331080a0a6e85146621000d55d0828cc420002ab610519884003557c0a833108006ea7815066210001c5ea2a0cc4200038b54541988404f75388283310809eea51050662100014dd0b18cc4200029b616319884003557424633108000aad848c662100071dd0e18cc4200023b61c319884000537428633108000a6d850c6621000d55d0818cc420002ab61031988400157540063
  | 12 => 0x29b20951195400043ec0cec32a800087e86dc465500010ff0fb08caa00031d5c761195400043ec3cc232a800087f8758465500014df04b08caa00029b20961195400043ec38c232a8000c7571184655000147d0da08caa01370f9db41195402551e4328232a8000c3e765046550001c6ec2a08caa000297a0e72195400052ec1ce432a8000c3e40dc4655000187881b88caa00021f61e711954025d1f424e232a8000a3d849c465500014df04b88caa00029b209711954000637c12e232a8000c6c825c4655001f0ff02b88caa003f1de0571195400061f202e232a8000c3c405c4655000187ee3a08caa00030f5c741195402551f4068232a804aa3c80d04655001f0fd0f208caa00021f61e41195400051ec248232a8000a7b8050465500954f100a08caa012e8fe05411954025f1bc0a8232a8000c3f71504655000187ae2a08caa00038ee0141195402551f4028232a804aa3c805046550001c7100a08caa003e1fa1e21195400043ec3c4232a804ba3e84884655000147b09108caa003e1fa1c21195400043ec384232a804ba3e84084655000147b08108caa000297a0c21195400052ec184232a804aa7a8008465500014f300108caa012a8fe11401954007c3f43e2032a800087d87c40655009747d09880caa00028f61310195400071aa0e2032a8000a3f84440655009747908880caa00038d50510195400351e426cbaa28047cbb645c354500998f0e1b2aa8a0002ab61021d894000566c1843b128000ae980087625006d87ec93acc4a000317d9673989400062e32ce73128036c9f649ce62500018becab9cc4a000317195739894001e66312e73128000ccd73d8a62500010fd0fb2ac4a00021fa1c655894000477c3ac43128000c5f659ce52500018b8cb39ca4a000317d9573949400062e32ae7292800f87c851d9525001f878caba0a4a012b1e9c065909400062fb2ce72128000c5c659ce42500018becab9c84a000317195739094001e66312e72128000ccd73d8a42500018f0cab8484a000f3a18970909400043fc2aed192800f87c855da32500071d904bb464a003e1fa17764c9400043ec2eec992800f87e859d932500010fb0b3b264a00021fa1b754c9400043f430ea992800087e87d9532500010f90fb2a64a00021fa1c654c94007c3e438ca9928005ace83d8932500010ff0abb064a003e1f215760c940006673b2641928003ccc764c83250001c9eca99064a000393195320c94007e1e32ae9a82804c87f855d9505008f17f08bb2a0a01370f1d365541402561e3a0caa828000c3f65dd15050001878cbba2a0a000a1f21572994400143e42ae332880008ef825c665100071d904b8cca2003f1dd45719944050c3ec3ca33288006a3e8494665100014df04a8cca200029b209519944007e3bb8aa33288000a5e839ca65
  | 13 => 0x61eb8acbaa480479bb865c354900019770cb86a9200034ed4570d52400069ca8ae1aa4804c87e87995549008f87ceab28a92001637a0f7558a400046ec1eeab148000c5e83dd562900018bb07baac5200e31b60b7558a400043ec0eeab14800087d811d562900010ff0ab8ac52003e1f2157158a400046fc1ae2b1480058dc835c562900010fd0fa8ac52003e1f21f5158a400043f43aa2b14800087c87545629006d17d0fa0ac5200030fdd74158a400061e3ae82b148000c3f755056290001878eaa0ac52000a3b21d2158a4000537c2ac5a948000cad7458b52900018becb39ca520003171967394a400068faa4e72948000c3d76d5052900014df0ab10a52000f339897390a401b6c6212e72148000ccd7358a429000193ec339c8520003275867390a400068fa8ce72148000d1d519ce42900059d0e0b1285200029b215628ca400043fc2aec994800f87c855d932900011ef02bb265200063d205764ca4020637310ea9948000a6c8558932900018d8eab126520016b320d624ca400043fc2aec194800f87c855d8329000799eec9906520003335d9320ca401b6c63a26419480038ee82dc765500011db05b8ecaa00028f61251d954000c3fc3aa3b2a8000a6f8254765500014d904a8ecaa00031d5c551d95400051ec20a3b2a8000c7571d8765500014df04b0ecaa00029b20961d95400063ab88c3b2a804ca3c865076550001c6ec2a0ecaa00038d18541d95402661e3a2e9b2a8000a5e831cb65500014bb06396caa00029ba0b71d954000536c16e3b2a8000c6e82dc765500018db05b8ecaa01368fa1271d95400051ec24e3b2a8000c77815c7655009b47d0838ecaa01328f61071d95400061fb8e83b2a8000c3d71d0765500990fd0f20ecaa00021f61e41d954026f1a20a83b2a804de3781507655000187ee2a0ecaa00030f5c541d95400043f43c43b2a800087d87887655009b47d0910ecaa00028f61221d95400043f43843b2a800087d87087655009b47d0810ecaa00028f61021d95400052f41843b2a8000a5d8308765500994f50010ecaa00029e60021d95402663c382e1b2a804d87e87c4365500010fb0f886caa01368fa1310d95400051ec2621b2a8000e3541c436550001c6a82886caa012b0f102759954007e3ba8ae332a80018bf87506655000396ce2a0ccaa00032d5c541995400045ec0ee8b2a800087f855c5655000117f08b8acaa00023be09715954001c76412e2b2a80008fb805c565500010fd0fa8acaa00030fdd3515954000c3e43aa2b2a8000c3f7454565500018eee2a8acaa00022fa1f41595400045f43a82b2a80018bc87505655000196ee2a0acaa00021fe1d651954007c3e42ae232a80008ef825c465500071d904b88caa003f1dd4571195400043ec3ca232a8000a3d8494465500014df04a88caa0
  | 14 => 0xa70192525400193ec939ca4a80032719273949500064fb22e7292a000c9c645ce5254007998c4b9ca4a8003335cf62949500065c322e1292a00687c859db425400717908bb684a801b0f19275d09500361e322eba12a000c3e75d93425400187aebb2684a800327d92739095042e4e324e7212a000c9f645ce425404d938c8b9c84a80e61fa1a75109500361e324ea212a006c3c645d4425400117f08bb464a801a2f211768c95001c76412ed192a0068be84dd9325400117b09bb264a803e1f214764c95020e36316ea992a000c3f75d913254001878ebb2264a80030fdd4644c9500061e3a8c8992a000c6f75d89325400b59d07b1264a80022fe11760c9500345e422ec192a000cce764c83254007998ec99064a8003a3d91320c9500074632264192a04ac3e75193505408fc76cbb26a0a80023be09715905001c76412e2b20a04b87c8754564140014d904a8ac82800a2f21d41590500065bb8a82b20a00fc3f545da54140998f4a0bb4a8280021fe0576950500043ec0aed2a0a04bc3f415da541400187a82bb4a82800237e0d715885002c6e41ae2b10a03787c87545621406f4d904a8ac42800a3b21d215885007d3642a42b10a00fc6c525da521406fa98a4b9ca42812e1fe1d649485025e1f3a2c9290a000c5d649ce52140018bec339ca4280031758673948500068fa0ce7290a000d1d419ce52140738bcc139ca42800356982739485025e1f3a2c8290a00fa6f8758852140718df0eb10a42803f1bdc5621485000636b8ac4290a000e2f415885214001c5a82b10a42801a1f61576d085007e1f3aac9a10a003cce625ce421400199ae6b14842803f1b1d562508501be36292ed190a03796c825d632140830ff0abb2642803f1b1d5624c85002d6641ac4990a000c6f7614932140b5c9cc6292642800f33dd9320c85000666bb264190a037d4c754c8321400197683bb2a0280032e50776540500065dbb6e8a80a000cbb761d15014095a76ea3a2a02803f1dd45719974000536412a332e8001cb67150665d000196ae2a0ccba00023be09715974001c76412e2b2e800187c8754565d00014d904a8acba00031ddc551597400053dc02a2b2e8000cb77150565d000196ee2a0ac5a0003179967394b400062eb2ce72968000c79655c252d006b17f0cba0a5a000e3b209768cb4002c76c16ec996800087f855d932d001f0f90abb265a009b339d9320cb402643fc3acba8680478bf865d350d00950fd0f32aa1a001b0f1d265543400361e3a2caa86800fc77515c665900011df04b8acb2000e3b20971596400143e43aa2b2c8000a3f8454565900018eee2a8acb200022fa1f41596400051f42e82b2c804a87f87597549009517f0eb2ea9200028fe1d65d52402561fc3acbaa48000a3f81597549000147b02b2ea9200030fdc565d524000
  | 15 => 0x2a8ec8a80028fe1572d91500054f418e5b22a000a9d831cb645400147d0b38ec8a80028f61671d91500065bb8ce3b22a000cb7815c7645400147d0a38ec8a811e8f61471d91500061fb8ea3b22a000c3d71d47645408f17d0f28ec8a80022f61e51d915000557c12a3b22a000aac825476454001c5f04a8ec8a80038b20951d91500071bc0aa3b22a000c3f71547645400187ae2a8ec8a80022fa1c51d91500045f43c43b22a0008bd87887645400147d0b10ec8a80028f61621d91500045f43843b22a0008bd87087645400147d0a10ec8a80028f61421d91500054f41843b22a000a9d83087645408f5750010ec8a8002ae60021d91500045f43e21b22a0008bd87c43645400147d0b886c8a80028f61710d91500065bb8e21b22a000cb771443645400117f0eb20c8a80022fa1b711915026e1fb2ee2322a000cb571d84645400117b0f308c8a80022fe1d611915000557c12c2322a000aac82584645400117b0e308c8a80032d5c461191500051f436a2322a000d3571d4464540954790ca88c8a80038dd8551191500061f42ae2322a000c3d855c4645400d96f02b88c8a80030f94171191500061e282e2322a000cb571d44645414b47f0fa88c8a82968f61f511915052e1fb8ea2322a0a5e3671d44645400187ae3a88c8a82978d5c751191500061ab8ea2322a04aa3e80d44645409547901a88c8a801a2fa1e51191500045ec3ca2322a000aaf82544645400155904a88c8a8002aee0151191502555c402a2322a0a4a3f875446454001c5f04a88c8a80038b20951191500071bc0aa2322a0a4c3f71544645400187ae2a88c8a80038ee0151191502551f402a2322a04aa3c805446454001c7100a88c8a801a2fa1c51191500065ab88a2322a0068be87884645400117b0f108c8a80028fa1621191500051ec2c42322a0068be87084645400117b0e108c8a80028fa1421191500051ec2842322a000a9e83084645400153b06108c8a812aaea0021191500055cc0042322a04aa3f85540645400d17d0f880c8a80022f61f10191500051f42e20322a000a3d85c40645400196ae3880c8a80028fe1510191500051e42a20322a000cb571440645409587f093b6a8a80021fe0676d51500043ec0cedaa2a04dc3f419db545400187a833b6a8a812b0f90276d51502561e204edaa2a000c3e76d93545409587cec326a8a81368fa1b549515023e5c386c8aa2a000a3e86dd1545400d47d0db22a8a811f0f1db64551502561f3b0c8aa2a047d3b741c154540014db0b10ec4a80029b61421d895000566c1843b12a000ae980087625407387ecb3a4c4a80e717d9673989500064fb24e7312a000c9c649ce625400193ec8b9cc4a800327191739895001e66312e7312a000ccd73d8a625400117d0fb22c4a80022fa1c645895000477c3ac4312a04acb
  | 16 => 0x158a5000566c18e2b14a002aea801c562940015d30038ac5280029ba1f5158a5000557424a2b14a000aad849456294001ccea328ac52800abaa025158a5000574c04a2b14a01b8ef8754562940351d90ea8ac528002b3e0d5158a500056641aa2b14a01bc6f8754562940014d90ea8ac52806b1b21d5158a5000727c1aa2b14a000e4c835456294001ccf02a8ac528002aba105158a5000556c20a2b14a000e2f51d056294001c5aa3a0ac5280029ba164158a5000536c2c82b14a000ea7815056294001c5ea2a0ac5280038b5454158a504f75388282b14a09eea51050562940014dd0a20ac5280029b6144158a500053742c62b14a000a6d858c5629400155d0918ac528002ab6123158a500047743862b14a0008ed870c562940014dd0a18ac5280029b6143158a500055742062b14a000aad840c562940055d50018ac528002ba6003158a500046ec34e7294a003cce629ce52940011bf0cb9ca52800f339897394a501cea6292e7294a0008dd8798e52940011bf0eb1ca528003339cd6294a5000666b9ac5294a000e4d63d4a52940079d4c4b84a5280e75a1497094a50004aec34e7294a000c5d649ce5294073a9cc539ca5280035358a7394a500062fb0ce7294a000c5d619ce5294001a3e8339ca528003475067394a500052ec3cc7294a000c5f7198e52940018bae331ca52800387d066394a500070ea0cc7294a000ce962dc1529409b0ff0eb20a5281370f9d16414a502d727414c6294a05ae4d8298c5294001c9ce5318a52800317dc66314a500062eb8cc6294a000e1f4198c5294001c3a83318a528003938866314a500072610cc6294a030e4f2098c5294061c9a41318a5280e71bdc56214a5000636b8ac4294a000e2f415885294001c5a82b10a52810f1b98a75d0a5021637312eba14a000c5e7598f42940018baeb31e8528003179d563d0a500062ebaac7a14a000c6e7558b42940018daeab16852800f1b98a7590a5001e37312eb214a0008dd869ce429400799cc539c852800237e197390a5001e67312e7214a0058df8798e42940011bb0f31c852800237e1d6390a500046ec3ac7214a000cce7358a429400199ae6b14852800317dd66350a500062e3acc6a14a000c6c7558942940738d8a4bb4652800f1b98a758ca5001e37312eb194a000c5e7558e32940018baeab1c65280031758f754ca5020e37316ea994a040c6e621d532940018d8eab126528016b320d624ca5000637bb0a4994a05ae4e63149329400159f0c9906528002b3619320ca5001e67bb264194a000ccd764c83294073a98ea990652808e5ee1d53d42500051ec2c83b22a0018bf87507645400396ce2a0ec8a80032d5c541d91500051ec2883b22a000cb571d87645400155f04b0ec8a8002ab20961d91500065ab88c3b22a047a3c865476454001c6ec
  | 17 => 0x6400ccd325c5600c8010fd0fa8ac01903e1f21f51580320061fba6a2b0064a5c3c74d45600c801c9a65a8ac0190021fa1d51580320043e43aa2b006400c3f74545600c949878e8a8ac019003934c951580320045f43e82b0064068bc87d05600c80187eeba0ac0190030f1d741580320074699682b0064008be87505600c8011790ea0ac0190030fdd541580320061e3aa82b006400e8d32505600c801d9265082c0190063e21d10580320076499220b006400eb141441600c8031790ea0ac9a80032ddc541593500055dc0282b26a037c5e659ce62d40fd99ec4b9cc5a800f331897398b5042e4f324e7216a000c9d649ce42d4001972c8b8485a80de1fe197510b5001c76412ed196a07ecce764c832d409b0fd0fa8ac9281368fa13515925000536412a2b24a0028bc87505649400147f0aa0ac9280032ddc5415925026d1fc3ac92a4a04ac3f87592549400147f02b24a9280028f605649525026e1fb8ac92a4a000c3d7159254940992f70cb84a92812f1ee197095250266b5312e12a4a04cd69625c2549409ba7682b84a9280034e50570952500049fc3aa82a4a04ab38805505494001c5ea92a4c5280029ba0f5198a5000557424a3314a000aad8494662940371df0ea8cc52800e3b21d5198a5000567c1aa3314a000acc8354662940378df0ea8cc52806b1b21d5198a5000727c1aa3314a000a6c835466294001c9906a8cc5280029320d5198a5000733c0aa3314a000aae84146629400155b0828cc5280038bd474198a5000716a8e83314a000a6e8590662940014db0b20cc528003a9e054198a5000717a8a83314a000e2d51506629413dd4e20a0cc52827ba94414198a500053742883314a000a6d8510662940014dd0b18cc5280029b6163198a500055742463314a000aad848c662940014df0a98cc5280029b2153198a5001c7743863314a0008ed870c662940014dd0a18cc5280029b6143198a500055742063314a000aad840c662940055d50018cc528002ba6003198a5002c6f41ee8b14a0008dd83dd162940730fd0fa8ac5280e69b2095158a5000536c2c42b14a000aae84885629400155b0910ac52800a3b21d2158a5000536c2842b14a000aae84085629400155b0810ac528002b3a0c2158a5000566c1842b14a002aea80085629400155f08baac528002ab2117558a500056741ee8b14a000acd83dd162940014db0b3a2c5280029be157458a5000717aa4a8b14a000aeb8055162940055d100aa2c5280038b5505458a5000536c2ce6b14a000aae849cd629400155b0939ac5280029be157358a5000666b98e6b14a000a6e859c562940014db0b38ac528002aba127158a5000556c24e2b14a000a6f855c562940014d90ab8ac5280029ba147158a5000536c28e2b14a000aae841c5629400155b0838ac528002b3a0c7
  | 18 => 0xc81f8eea2b8cca1900e9b209519943201c76412e2b28640187c87545650c8074d904a8aca190031ddc5515943200c5e43a82b206400cb771505640c80d0f90abb6a81901a1f617765503201e6743eec990647eace85dd9320c84d59d09bb26419002b3e07764c83200566c0eec9906400cce71dd9320c801998e3bb2641900393d47764c83200726a8eec9906400e8f41dd9320c801d1a83bb26419002b3603764c83200667bb6ea9906441e4e86dd5320c801c9b0dbaa641910753ddb754c83200727bb6ea9906400c4f76dd5320c801c9cc9baa641910793193754c832005a7c0eea9906400b4d81dd5320c883c9ec3baa641900393587754c83200787a0eea9906400f0d41dd5320c80159b0d3aa6419102d3a16754c83200567c32ea9906400ccf765d5320c88369d0e3aa641900353a1c754c8323f727c30ea9906440e4c861d5320c881a9eec3aa641900393dd8754c83200727320ea9906440e4c641d5320c80169f023aa6419002d3604754c832006a7388ea9906400d4c711d5320c881c9ec23aa641900393584754c83200787a08ea9906400f0d411d5320c80159d0f32a64191fab321e654c83201d6742cca9906403e4e85995320c801c9eeb32a64191fb931d6654c83213567424ca990647eacf81995320c80159b0332a64191fb93d46654c83200726a8cca9906400e8f41995320c801d1a8332a6419002b3602654c83213566c36e89906426e8e64dd1320c80159b0d3a26419002d3a16744c832005a6c2ce89906476bc6819d1320c80178b033a26419002b3e19744c832005a7c2ae89906400b4c855d1320c84d59f0c3a2641900eb3218744c83213747320e89906403ace86d51320c80159b0daa2641910f93197544c83201d67434a89906400acd86951320c801e1ea92a26419002b3e19544c83201d66432a89906442e4c65551320c84d59f0c2a2641900eb3218544c83200667bb6e09906400d4c75dc1320c80159b0d3826419002d3a16704c832005a6c2ce09906400acf865c1320c80199eecb826419002d3e15704c832005a642ae09906400d4c755c1320c80171f08b826419002e3211704c832005e3c0ae09906476bc4815c1320c8738dd05baac0190031b60b75580320043ec0eeab006437c6e321d5600c8b78da643aac0190021f60475580320061fbaee8b006400c3c75dd1600c80117b03ba2c0190030fdd474580320061e3a8e8b006400ccf874c9600c8019990e992c01900393e1532580320072642a64b006400e4f754c9600c8fd998ea992c019003931d53258032006263aa64b006400e8f744c9600c84d998e8992c019003a31d13258032136463a264b006400ecb804c9600c801d9100992c01900fb2dc1325803200666996e2b00640087f855c5600c81f0f90ab8ac0190022fe1171580320345e422e2b
  | 19 => 0x9f2b5cb41d913200c5fc3a83b2264a6cad72507644c80196ae2a0ec8990031d9c765991320063b388cb3226400c77655c6644c8018e8cab8cc8990032dd9171991320365a322e3322640087e87d95644c8010fd0e32ac8990021f60775591320043ec08eab22640087f855c5644c81f0f90ab8ac8990023ee0171591320147c402e2b22640087e87d45644c81f0f90fa8ac8990021fa1d51591320043e43aa2b226400c3f75d05644c801878eba0ac8990062f21d41591320061fbaa82b226400c3c75505644c80196ee2a0ac8990072d1c541591320045fc3ac8322640687c855db544c80b1d90cb96a8990167320d72d51320051ec26cb2a26441c6e72d96544c80b1d90cb94a8990031bd95729513202ce641ae52a264028fa809d9544c8011f3013b2a89901a1fa1f65551320351f426caaa26400c5f73d95544c8838d8e5b2aa8990163ba1b725513202ce741ee4aa264058ed829d8544c80759b07b2ea4991fb93d4f65d49322f6a739ecba92645ac6e76197524c8b5a9ce632ea499107539d673d493202ce7c3ae7a92645ec5c73d95524c8018becbb9aa49900f33d8e761493201d66c1eca292647ee4f53d94524c8834db0fb28a49917b1b61f65149323f72741eca2926441e4d83d94524c801c5e83b28a4990038b507651493200477c3aca2926441a6e86194524c8018dcec328a499102d320c6514932134b6c3ea82926400a6e86d50524c84da5ce9aa0a49916ad3a0f54149322d5a641aa8292645ed4e7614c524c881c9cec298a49910353dc4531493255ea6b88a62926487e4e6114c524c90fc98c2298a4992abc3d04531493255786a08a629264269ac845c0524c80b39906b80a49917a1fa1a75d093221ea6194eba12645a87c865d7424c885a9864bae849917a1fe1f65d09320043ec3ecba12640f87f87197424c8010fb0e32e849917a5ba1a75d09323f6a7c1ceba12647ed4c839d7424c8878dec73ae849910f53d8e75d0932136a7a1ceba126426d4c439d7424c8012df033ae84990025b60675d093213697a0ceba126400d2d419d7424c801a9e633ae8499003534c675d0932004b6c3ecba12645ec6e76d97424c8bda9ce7b2e849916a5be1c65d09322d6373b0cba12645ad4e73197424c801c5ecbb2684990027361f53d09323f6a73aea7a126426b8e84d4f424c80b39f0e29e84991fb539d453d09320043fc2aeca12640f87c855d9424c80b39d073a8849900e73a1f53109323f6a73a8a62126426b8e8414c424c8012d90ab8084990167320d701093200726298a5b026400cb771507604c803968e2a0ec0990021fa1f65581320063a38ecab02640087e87195604c8018e8e232ac0990030fd9774581320061e32ee8b026400c3f651d1604c801878ca3a2c0990031dd9771581320063a32ee2b0264008fb87580604
  | 20 => 0x3bc0ae3b2a6400a3e841c7654c80147b0838eca991069ba0871d95322f536c10e3b2a6400c75711c7654c8014f50038eca990029e60071d953200716b9683b2a6400c3f71d07654c80187ae3a0eca990021fa1e41d95320043ec3c83b2a6400e2d72507654c801c6f02a0eca990030fdc541d95320061eb8a83b2a640087e87107654c8010fb0e20eca9917a1fa1e21d95320043ec3c43b2a6400a3e84887654c80147b0910eca990028fa1370d95320051ec26e1b2a645ea6d82dc3654c8bd4db04386ca990021fa1f10d95320043ec3e21b2a6400a3e84c43654c80147b09886ca990038d50710d95320071aa0a21b2a640087e87043654c8010fb0e086ca990028fa1010d95320051ec2021b2a6441a6e82043654c8014db04086ca9903f1dd45719953200e5b38a8332a6400cb571506654c8010ff0ab8aca990023be0971595320043f43ea2b2a640187c87545654c8018eee2a8aca990032ddc5415953200e5a38a82b2a6400c5f539d8654c8010ff0eb28ca9903f0f151741953207c3e42ae232a640fc77515c4654c8010fb0f288ca990028fa1251195320051ec24a232a6400a6f82544654c80117f08b80ca9901a2f21170195320043ec0cec32a640087e86dc4654c8010ff0fb08ca990031d5c761195320043ec3cc232a6400a3e84984654c80147b09308ca990021fe1d61195320043ec38c232a6400a3e84184654c80147b08308ca990031d5c461195320053d400c232a6400a7980184654c80187ceda08ca990030f9d941195320071bb0a8232a6400e3461504654c8014dd0d908ca9916a9b21921195322d5a641a4232a640fc3f749d0654c81f878e8ba0ca9903f1b1c972195320043ec3ce232a6400a3e849c4654c80147b09388ca9903f1ddc6711953200537c12e232a6440a6c825c4654c8018df04b88ca990031b209711953207c3fc0ae232a640fc77815c4654c80187ee3a08ca990030f5c7411953207c3f43c8232a640087d87904654c80147b09208ca990029be094119532205364128232a6400e2f82504654c801c5904a08ca990038de0541195320061fb8a8232a6400c3d71504654c81f0fd0e208ca990021f61c41195320051f4208232a640f87e87884654c8010fb0f108ca990028fa1221195320051ec244232a6400a5f83484654c8b54b906908ca990029b60a70195320051fc22e032a6400a3c845c0654c81f0fd0f880ca990021f61f10195320051f4262032a6400a3d84c40654c8018eae3880ca990038d5071019532205374142032a6400a6d82840654c8018eae2880ca990038d505101953207c3f4382032a640087d87040654c80147d08080ca990028f6101019532205374102032a6400a6d82040654c80b99ce6b96c89909b335cd72d913202c76c16e3b2264a8c6d72d47644c9478dae4a8ec8992
  | 21 => 0x635ca43508850fb0fb2ea4a110e1fa1c65549420061fb2ee8a928400cb77150760508011f70eb00c0a100e1f215739944207e3ba8ae33288400a5c8354665108074d904a8cca2100237e0d715944202c6e41ae2b2884038ec825c565108030f90ea8aca210029720d515944201d36412a2b288400c7771545651080196ee2a0ac6210063721d3158c420052fc2ac7a988403c6e7299653108014bf06b2ca62100f1b9c96594c4202c6f41eeab0084008dd83dd5601089b878e9baac02100317a0f75580420062ec1eeab008439c6e82dd560108018db05baac0210021f607755804226e1fa0eeab00844bc3c741d5601086f8dc643aac0210021f604755804225e1fa08eab008400c3e401d56010897878803aac0210021fe15715804207c3e42ae2b0084008df835c5601080b1b906b8ac0210021fa1f515804207c3e43ea2b00840087e8754560108010f90ea8ac0210d22f21d41580420061fbaa82b008400c3c7550560108031f10e882c021003ac505105804207e3ba8ae332c6400a5f83546658c8074d904a8ccb190022fe1170996320345e422e132c64038ec825c5658c95b8d8e5a8acb190061f21d51596320052fc1aa2b2c6403a6c82545658c9458d8e4a8acb190031ddc551596325665639682b2c649fcac72505658c8071d904b8ac9192b71b1cb515923251636392a2b2464accac72d05648c8031790ea0ac91927f2b1c941592320065bb8a82b246443a6c82597548c8071d904bb2a91900e1f21d655523221536412caaa464038bc87591548c8071d904bb0a9191021fe1d65d4e3202d2f41acba9c644187e87995538c80d87cc8bae87190030f5d564d0e32004b7c0ceba14640096d819d7428c853a5e833ae85190034b50675d0a321ce36296eab0464018f887441608c801d6282882c1190029761f53d95320062ec3ea7b2a6400ccd735cb654c801c9ea6b96ca990163b60b71d953254636b96a3b2a6400a3e84947654c80147b0928eca990029b60a51d95320063ab8ca3b2a640187f87547654c8014bf06a8eca9928f1b5c951d95320063ab8aa3b2a6400a3e84147654c80147b0828eca9900387d4f41d953253e56b9683b2a6400e1f53507654c94d95ae4a0eca990031d5c761d95320051f424c3b2a6400a3d84987654c80147d0830eca990028f61061d95320063ab88c3b2a6400a7a80187654c8014f30030eca990038dd8541d95320071a30a83b2a645ea6c86487654c8bd6990690eca990039918521d95322f536c16e9b2a6400a7a80dd3654c8014f301ba6ca990030fdd274d95320061eba0e9b2a645ea6d821d3654c8838d8e4b96ca99003935cd72d953220d37416e3b2a645ea6d82dc7654c8018dae5b8eca990031ba0b71d953200636c16e3b2a6400a3e849c7654c80147b0938eca990031b5c971d9532006
  | 22 => 0xba2c72109b879535458e4201d67416a8b1c8400acd82d51639080159f04aa2c72100eb32095458e420052f42ce2b1c8400a5d859c563908018b8eb38ac72109aa7a127158e420054ec24e2b1c8400a5f855c563908014b90ab8ac721002b3e097158e4201d66412e2b1c8400a5e851c563908014bb0a38ac721003171d47158e421354f420e2b1c8400a9d841c5639080759d0438ac721002b36087158e420056d400e2b1c8400ad9801c563908014bd0fa8ac7210029721f5158e4257f27a16a2b1c84ade4c42d45639095bc9e41a8ac72109aa7a125158e420054ec24a2b1c84008df8754563908011b90ea8ac721002b3e095158e4201d66412a2b1c8400c5f8754563908014bd0ea8ac7210029721d5158e420062e43aa2b1c840085c875456390801c9f04a8ac72128b932095158e4257727a12a2b1c84a2e4c425456390801caf02a8ac72128b93c815158e421354f420a2b1c8400a9d841456390801c3eeba0ac721003871d74158e420070fa8e82b1c8400e1d51d056390959d1e41a0ac72100297a164158e420052ec2c82b1c8403ace82905639080159b0520ac721002b3e094158e4201d6641282b1c849fe8c425056390801c3eeaa0ac721003871d54158e4200747c1282b1c849fe8c82505639084dd2f02a0ac72100387d454158e420070ea8a82b1c849fe8f2050563908018b8ebb82c72100297a167058e420052ec2ce0b1c8403ace829c163908014bf0ab82c721002972157058e420062e3aae0b1c8400a9f845c1639080759d04382c72100297a171058e420052ec2e20b1c8426a9e84c41639080153b09882c721003a55071058e4201d6741420b1c8400acd828416390801d2a82882c72100237a1c1058e420046ec3820b1c8400a5e8504163908014bb0a082c72109aa7a101058e420054ec2020b1c8403ace82041639080159b04082c72100297e1563d4e4207d2e42ac729c8403cce7258e539080b99cc6b94a7210033358d7294e4202e4f31ae829c8400a5f8558c539080b99cc6b94872101637a0f75582420046ec1eeab04842d8be87d05609080196ae2a0ac1210063e21d105824200758a0a20b0484058de83dc765508011bb07b8ecaa101a3b60b71d954200c3fc3aa3b2a8400a5c8354765508018eae2a8ecaa103f1dd45719954221d36412a332a84018bf87506655080396ce2a0ccaa10032d5c541995420046fc1ae2b2a84058dc835c565508011df04b8acaa10023ee0171595420147c402e2b2a840187c8754565508854d904a8acaa10031ddc5515954200c5e43a82b2a8400cb77150565508010ff0eb28caa103f1dd4571195420052e41aa232a8400a6f82544655080d1db05b8ec6a100237e1d6318d420052ec1ecb29a8400c6f655ca53508018d8cab94a6a109a3761f6390d4200667b1ae521a8405ccc
  | 23 => 0x597420043ec3862b2e8406a3e840c565d080147b0818acba110a9ba08315974200536c1062b2e8400a7a800c565d08014f30018acba10021fa1e21597420043ec3c42b2e8406a3e8488565d080147b0910acba100297a0e70597420052ec1ce0b2e8400a6d829c165d080d47908b82cba10021fa1f10597420043ec3e20b2e8406a3e84c4165d080147b09882cba10038d50710597420071aa0a20b2e840087e8704165d08010fb0e082cba101a8fa1010597420051ec2020b2e8400a5e8304165d08014bb06082cba110a9ba08105974200536c1020b2e8406a9e840c563d080159b0418ac7a1002b66003158f4207e1f32ae9a9e8443c6e7299653d08014bf06b2ca7a110b1b9c96594f420063732ae529e8400c6d655ca53d081f8dccab90a7a103f0f99574d4b420061eb2ee8a9684008df835c6659080b1b906b8ccb2103f1dd45719964201d36412a332c84008df835c5659080b1b906b8acb2100e3b209715964200c3e43aa2b2c8403a6c8254565908018eee2a8acb21217879535498e4242d4f424a331c8400a9d8494663908011bf0ea8cc7210163721d5198e4200567c12a331c8403acc8254663908018bf0ea8cc72128f1721d5198e4200727c12a331c84a2e4c825466390801caf02a8cc721216a7a105198e420054ec20a331c8400e1f51d066390801c3aa3a0cc721002a7a034198e420052f42c8331c8400a5d85906639090bd2f02a0cc72100387d454198e420070ea8a8331c8400a9c8050663908014bd0b884c721002976171098e4242d4f4262131c8400a9d84c426390801d2a83884c721002a7e111098e4242d4e4222131c8400e9541442639080b1bd0e084c7210023761c1098e420052f4282131c8400a5d85042639090b53d08084c721002a76101098e4201d674102131c8400acd8204263908838bb07baac7211071ba0b7558e4200636c16eab1c840087d81dd5639081f8bb063aac7210021f6047558e4220637900eab1c840087f855c5639081f0f90ab8ac72100e3b2097158e420043f43ea2b1c840f87c87d4563908010fd0ea8ac7210021f21d5158e420061fbae82b1c8400c3c75d05639080187eeaa0ac7210030f1d54158e420052f42c62b1c8400a5d858c563908018b8eb18ac721002a76123158e4200c6e43a62b1c8403acc824c563908014bd0a18ac721002976143158e420062e3a862b1c8400a9d840c5639080759d0418ac721002b6a003158e420056cc0062b1c8403ace82dd56390883c9d05baac7210039360b7558e4200727a16eab1c8441e4c42dd563908014bb03baac72110793c837558e422052f42ceab1c8400c5f759d563908834bd0e3aac72100317a1c7558e422062fb90eab1c8400e4f421d56390881c98843aac721002976047558e4220727900eab1c8400a5f855d163908014b90a
  | 24 => 0x8a400c6d615c85314801a5e82b90a6290034b5057214c522d6a7982e4298a400d4d305c8531481f8dea7bb2a4290032bd07765485200656a0eeca90a400c6f7654d521480117b03ba2c0291370fdd4745805226c3f43ea8b00a406c3c74d5160148610f90eaa2c02901b0f1d154580521853c402a8b00a4008bf845c5601480d17908b8ac02900237e0d715805202c6e41ae2b00a400c3f74d45601494b878e9a8ac0290c21f21d51580520061fba2a2b00a4a4c3c74545601480117d0fa0ac02901a2f21f41580520045f43a82b00a4008bc8750560148031f10e882c02900eba209105805200758a0a20b00a40687c855c665d08011bf06b8ccba10163720d719974207e3ba8ae332e84a487d8794665d080d47d0928ccba100297e0d51997420052e41aa332e8400a6f8254665d081f8bee739ccba10029b60a739974252e1fa0ee332e84a487d879c665d080d47d0938ccba10028f61271997420052fc1ae332e8400a5c835c665d08014df04b8ccba110e9b20971997420062fc1ae332e8400c5c835c665d08018df04b8ccba10031b209719974207c3fc0ae332e840fc77815c665d094987e82b8ccba101a8fe0541997420371bc0a8332e8400c3f7150665d080187ae2a0ccba110e9ba0b319974200536c166332e840f87e878c665d08010fb0f18ccba101a8fa1231997420051ec246332e840f87e870c665d08010fb0e18ccba101a8fa1031997420051ec206332e8443a6e820c665d08014db0418ccba10029ea0031997420053cc006332e840f87e8788665d08010fb0f10ccba101a8fa1221997420051ec244332e8400a5e839c265d08014bb07384cba10029b60a70997420351e422e132e840f87e87c4265d08010fb0f884cba101a8fa1310997420051ec262132e8400e3541c4265d08014df04884cba110e9b20910997420071aa0a2132e840f87e8704265d08010fb0e084cba101a8fa1010997420051ec202132e8400a5e8304265d08014bb06084cba110e9ba08109974200536c102132e84008df835c565d080b1b906b8acba101a1fa1e51597420351f424a2b2e840187c8754565d08014bf06a8acba10029720d515974200537c12a2b2e8400c777154565d094b0fd0e28acba101a8fa1051597420062fb9ce6b2e8400a6d829cd65d094b87e83b8acba12921f61e71597420351f424e2b2e8400a3d849c565d08014bf06b8acba10029720d715974200537c12e2b2e8442a6c825c565d08018bf06b8acba10031720d715974200637c12e2b2e8400c6c825c565d08018ef02b8acba12930fd05715974252c3f438e2b2e8406a3e841c565d080147b0838acba101a8fe0541597420371bc0a82b2e8400c3f7150565d080187ae2a0acba10021fa1e31597420043ec3c62b2e8406a3e848c565d080147b0918acba10021fa1c31
  | 25 => 0x80153d0918ac729002a76123158e5200c6e43a62b1ca400a5f854c563948014bb0a18ac729002a7a103158e520054ec2062b1ca403ace820c563948015b50018ac729002b66003158e5201d67416e8b1ca400a5d859d163948014bf0aba2c72910f9314b5458e520070faa4a8b1ca403ace82951639480159b052a2c729002b3e095458e5201d66412a8b1ca442e4c5255163948014bd0b38ac729002976167158e520054f424e2b1ca400a9d849c563948014bf0ab8ac729002972157158e520052f428e2b1ca400a5d851c5639480153d0838ac729002a76107158e5201d67410e2b1ca400acd821c563948015b50038ac729002b66007158e5256f26296a2b1ca400a5e87d45639480153d0928ac729002a76125158e5201d67414a2b1ca400acd8294563949631bf0ea8ac7292c23721d5158e5200567c12a2b1ca403acc825456394945c98a4a8ac7292c717e1d5158e520052e43aa2b1ca4b0c5c875456394801c9f04a8ac72928b932095158e520072bc0aa2b1ca400a9e84145639480153b0828ac7292b3a314b4158e520070fa8e82b1ca400e1d51d0563948014bd0b20ac729002976164158e524ff4629282b1ca400e97815056394801c3ea2a0ac729003875454158e520052f42882b1ca400a5d8510563948014bb0b382c72900297e157058e520054fc22e0b1ca400a9c845c1639480759d04382c72900297a171058e520052ec2e20b1ca400a9e84c41639480153b09882c729003a55071058e520074aa0a20b1ca4008de8704163948011bb0e082c72900297a141058e520052ec2820b1ca400a9e84041639480153b08082c72900eb3a081058e5200566c1020b1ca405cce635ca5394801a9ea6b94a72917b5314d7294e5220cb7c32e529ca45ac6f865ca5394883a9cc6b94a7291075358d7294e5220e37b0ae529ca400c6d615ca5394801a5e82b94a7290034b5057294e5201f273aac7a94a47ee4f5158f5294801c9aa2b1ea529003a3d0563d4a5200746a0ac7a94a43887e87d51609480d878e9aa2c12912e1f21d54582521c53c402a8b04a43887e87d4560948031f10e882c129003ac505105825221d36412a3b22a4018bf87507645480196ae2a0ec8a90022fe1d64191520049fc3aa82a2a400c3e7655054548014bb0b18ec6a90029761431d8d5200566c1063b1aa400ad9800c763548011bf0eb18c6a900333d8d7294d5202e6631ae529aa438c5f659ce60548011f70eb00c0a90029720d515905200c5e43a82b20a403aac82505641480196ee2a0ac82903f0fdd376550522d43e43aa2b18a4018dc874c563148075990498ac6291071b9497694c523f6a7a9ae5298a45ad4c535ca53148838dec2b94a6290031b5857294c5200697a0ae5298a400d2d415ca531481f2df0cb90a62917b1be197214c5207e37b0ae429
  | 26 => 0xe00240020020050008048016006000000c0020160028004015003800000c0030008058018001000000c06e008df835c562d500b1b906b8ac5aa10e1f21d5158b5421d36412a2b16a806c3c7550562d508f17d0fa0ac1aa11eaea03415835400e5b38a82b06a800cb57150560d501f87ee4bb6a92a0028fe0576d52540051ec0aedaa4a80fc3f715db549500187ae2bb6a92a03f0f1c176d52540061ebb2e5aa4a800c3d769c3549500165d05386a92a002cb60a70d525400536c2c42b14a800a6d85085629500d55d0810ac52a002b360c2158a5400574c0042b14a84c87e87d4560950994f501a8ac12a10a1f61f51d895421536412a3b12a806c3d7550762550014db0b10ec4aa0029b61421d895400556c2043b12a800acd8308762550015d30010ec4aa00f33189739895400666b9ec5312a800ceb625c262550079d0c4b84c4aa0023be1d62189540065bb8a83b02a800eb141c4360550014f30a086c0aa002ae61010d815400574c1021b02a802ce8605ca60550019d2e5b04c0aa0023ee1d60181540361fc2eecaa0a806c3c85dd9541501f87ea5bb2a82a0022fe0776550540045ec0eecaa0a80fc3f51dd9541500187aa3bb2a82a03f0f143765505400477c12e2b00a8038ec825c560150950f90ea8ac02a12a2f21d41580540046fc1ae2b26a4058dc835c564d48854d904a8ac9a90062f21d415935200557c1282b26a400cb77150564d48618bccb39cc1a90029720d515925200c5e43a82b24a400cb77150564948014bb03aa4c72900297a035498e520070faa4a931ca400e1f8455263948014bf02aa4c729002972015498e520052ec26a331ca400a5e80d46639480153d0928cc729002a76125198e5258c6fc3aa331ca4058dc87546639480159f04a8cc72900eb32095198e5258e2fc3aa331ca4b0c5c8754663948014bf08a8cc72900393e095198e5251726412a331ca400e578154663948014b900a8cc729002a7a105198e520054ec20a331ca400a5e85d0663948014bb0ba0cc72900387d534198e520070eaa68331ca400e1e85d066394801c3b0ba0cc72900387d474198e520070ea8e8331ca400a5e8590663948014bb0b20cc72900297a154198e520052ec2a8331ca400e1f545066394801c3aa8a0cc72900387a154198e520070ec2a8331ca400e97815066394801c3ea2a0cc729003875454198e520052f4288331ca400a5d8510663948014bd0b884c729002976171098e520054f4262131ca400a9d84c426394801d2a83884c72900297e151098e520052e42a2131ca400e9541442639480b1bd0e084c7290023761c1098e520052f4282131ca400a5d85042639480153d08084c729002a76101098e5201d674102131ca400acd8204263948bd0fd0fa8ac72917a97a0f5158e522f52e41aa2b1ca400a5d858c56394
  | 27 => 0x18000002802c00800e000003400000700a8000020001005000c0460010000000008003001003c032002000001002202700b803002805d000001004200000f800402200000300ac0000210008000000017005800000200f000810c00400000580140020050000000002001009800000c00c0000020000001001802801e01b011001400000b0030010000006000004400000003f000400a001000002c018083006000001c00000c002000000f00000b0002000008002800c009000002807201000000ac000000001000c000010013000401a0000530054002007001800c000005002000400200e00200140100000028014016005006801001a006009801400401b000002404c00000a000004800100680080460010008074006043019001c002006029801c00000e0068038008060003000000a00300580080020030018000002008000000003200400080080000020008018008000001801000007e0028000066014000001c008000000000c000009002802c00000000c8030004000000802803c033000800001e017001803c00800500d0000004000004800800a03a001800401000000000900000060018090012011000800801600700781ac0000000098000002000000000001e0080028000006003004803000e014003000000c001001812000001b0050008012000003800c0080070000000056000023804401c00200080c4000006005800c000005000003805a008000000001e017008000800e00f009807400000100c8000008006004801c00a00800200180060000058000032004003003403c033003000000a00000080940060070030008012006000000c00000000000f003a035004805000600a003800801005a01100080080020040008002003048003800800d003006c010001006000000e01b02900a800c000001000000004a0030010054009001000c00600500300040020020350004000008004800000a0050018004008000001800c00000a000001c000010000033801c000000007800200000080180360420028014000000001800400000300c0004000000000000400000700c800c00201200100240140050010004010000001001000000f001005c0040000130100000001000001000002000400480e8009029000c00200e026800000e000000803c14e00d00300000c200b000800801a03c0018014006000006801c05a0000008008000000000800400000c003006c008007008000c0320150028000014001000800001e000003800801a0010020010002000000800801602b006008400a00000a002401400600000c80000000010000008000005001000400100a00540a60000000010000000000800000e00000c802400601d0040020000004001000000205c0008000006072023802800400f001009400204e00100040020010
  | 28 => 0x60000000003000006000c000000001c000001012000801a014003801001000602101c800a0000000000002000000001c00c00b00480c400000000d000000202c00a000400a0010190078002005001806400800401d80a400e0070098000002000000000003c01f00480000000010018014052004000801c096010000802800c000001800c000003001800400c00400100440c4002000801402000100e81e8002004002001001200e006801400c00c00000000140000018004002008000001800201c0010178000001001800000004c0030070002003003808000000a01200080100050070000000016016802c00400100400c402a000002002801602900303c800000100a802809007e011800000e0060000014036001004800000201c000002002c002000818c0100040080018002009000000c028028002802c00000400400200a20050020000000000000800400000d000002001600a00100000080140050000024013000800000400200000200120020000018010002000800800200800180900060010008004000015002000403400b002000000200200380400040050018018000012001002000200001d800002202c012000800402a001001400c00b00680000e0000001807000200d00b801c02000900300140000000078000004077000801801802400700780000000060008022002000004002c01d0028000032011005009c00201c003001812c005001801405800c000000800e000000000001400000380480000510028014000008000000000200a0010478004012003800000400200400980c60020038014004006003000c002004005001c00200000000e4002000000004002200c005001400c00a04d8000006001002007001a00000b0000004000001001806400001300a0002007002001801c00d006001c00202f010801000000b0080024048001000000c000000001800c0000010040000018002010801c00401d00500140020000058018000003071808800400200000000100000058008046009008800000001e0008000194000006002007400c00000f8006004000802800c002000002000a008000800002600000000040060010088014010008008000400800b003802c004010004000c00a0070068108004002000801c000000007006801000f0000024002011001000000e012001000001e00000a804800e0360078020020002001000410400000b012402001f0020000004001001006000c001005001c014000005000800801c005002c01a000001802c006001001001802600f01e800801c003001800800000400e805407000300580480000000010028000000003002c00000700000d800a002003007802c002002000c032008001000401e003004801c004002008003c02800b003000c00c002000000000400500e0008
  | 29 => 0x1df551b00007c82b802c49e3b100000001c31b0b744a8e20c6a280f55be00000000008140005a4a626b3a80f39c110431802947a40000002e31a023f8de02d866f0001a5a4b257400000000cf2072b58000673000131c00080200000001280002eb0001cf8dce01936ed23a000000210c1682f900000016e00000281a5c4ba3bc0ab800088a12c0000a38000a8bf151df80000005c900014ac28d65100000000006178574cf900000000007f000028102140006d661c000090ca9a963ad196188c8000053058c0793aaa9ec1a708000ea138700adb2ad1f4935c4a829aab9c19911827d11c4ab080066b800109488a0000d940001d363f9f31942000000044c0008da04577198920590698264000c660eb8000000d2b00000017fcab20c7104c87600000000000000005bc3040cc037236eb2a52f40007461f4061cbba2d28000000c344bb3270000b9344a85c028c1fd0003710412d426b801f8e500000002599bbe00000000012d2ace374871bade6d9670836cd7439f5d719509c84cd2f98b591563c25bc8464d60c8241d8f942c0aad0cf86408369d129500000000002bf050c1de844505ac60228e6780031a59ba00000016f90cebd70fc95a9d1f57541590d0d8042a3358898000b6e46898c970a9746cc37eca860a644891e1060000064599473a49356314ee9d44e83ca25c8000000482a710b760000e892145b435c0a8ee8fcc4b3e000000098a00057d1c1529a7ed0001b392a400000000011c400022680002ea63138fb28c00054e5ab75a8564b440002ef14e60000000000000c4f1ad0256000378000000044e8dc07c00006fc0000001a21202d1f2dd27688b23b730a07dc2d476d0f9111054c9382dfb2c476020b2dc000184248a45a80000009d00342f942b80006cab18423c25bcc689ecf735864e900013b685214126f013edbd8aa81c4a92717608916cf84a21177aa04b20d915982aaa00035e0a88000d3c8182b98fc8b36c161621d6ccdcd8d41225bc000a8672f0000000a9921800015d800000000005aa00035fb355d26bdb4ebb530cd462f385b4cca20c4e055b4d0db63ef21236d931281ac2a80000001f1001000064a0005b4400086e00056292bc0008875b79d10540a225f1142280ed7e22433046d8b32474a760bdec096209bcc74e9126132b94d0920400c38cda4072c0e504fc9001dc2689ff1256c0c6660ff40dcab80bc31c44a286a05c36cd578685a7aa34dc2e00028e2408000d4069eb5b80000005838000000a8a6f3000108a0004963785a189b10470000f5800b0220030002005005406400b00000080060000050000014003000002800c00b0000018006008000001c0280020050000000000000001413a00000380080a2045005001c00000503c801403600900980080f6004000000000000801280fc01200b
  | 30 => 0xd2500009b8bae9900e006f47dc0000ba337c2fadca5d38a59b4a5995498c902b51e9e4c257d80aa6e2b0748488e7f212610f5212db9523b681d1b78f3ac800147a00024764288ae9e6607800140e9cc1c8a4c58a40f514e9644840d90143879d472000000091d7f0b4d6f42dce0000001ea800074ca0f0000000000ad30250d997dfc9d0001cbc34063c1440fa87d8e21284c00000079a00008b0b3e00045035e0ac557812b20d0d56ae24ff902486a38c54b227b6209d415d802c0000000000000a24a922c900019a80003180f400001800000001c8e000000000113f34929a000000077a00000016d589c0001ed81c86ec2c23468ed20002ee800000019b00012ca248d123e40000bc80002bd278250644343237d01488b148592c00000a060a05f91cf61b17e21d07d6d7419f8017757d9351927ac5364820001983534cfe00697547b668b2d101d9052a7d362963c19a0001651548200e54049000012ccba5d1485c14a63d15723dda44a1042b275466a1b224e3220e147ef3ea1c314d9ca43579139a82bd05b2ab08dde0fd2d0b84554a0262eda44cffc95167c2cbcc222b37282438f0c8ad1e30191c7ae8e29e05f114c000479800186ac3204102757ba016ecf21e8454721000000133763530927e0000000000026d694000188000000000000024840004ee5d280017643850000000000cb409a8000638bde54b4a881ce00c3d24000dea13800039080009810001510e238b6124af2c712318348b238000d9a3eaa8e0f4067a33f31880b4b1c41396a00001b3213000008ac896dba05400000025e32dce7e54680001b5b6295000000011f2ad9000072000003025c18b0ce443f623000021620f09a2b5000084060580016c289900028a5ac2a590000240524cdc541823482c5c973b00003629c70f4000077e00062000000008eb000034b5254733ad0a85794daf04c1854c4e9ea4d5b44532239940f9ab82f20000002b6e000000000199dcde6b83a7a6e81ee31609790449466500b213d137078807d82c9bd2aeb2a64000be098b5b76be4e40b2805da550754cc974297ddcc022d0000e386a2bb80339305b5829c0009c254ca787546872ca48d834288fd426e8210000841751000197b14c36c000000000017c10e2b79f1562e92a1a394ccf800fc34322741ba0005b19cd99867bcbe740019d60007240b79372ded25024cc9d27355cc8c81ba8a00290b5519565ec287192c6ec64162b10e43cbad7526756d54ebb1406292e000c7a58d0cb9a3a4250992845c141f50a9a3f052a77274bb72503ac763ba3895012d5865a9928112157e4aa5188c687facc2c040006cf52c086066056761f89717ebc5c678af55aa68897168a8d0d8b12228b344000afd800000000000000028503b270d00005322cc25971000007ce0b93c5218d8d827d000
  | 31 => 0x85ea80003630152e756e210c6fa8dec46883e1a30000f082e61cd9240186bcd0de24dc77ccc23b99c4d86260b43052b86b0d9f5a71e605c4998368287911ebf4371b295062a330000000000d2a4ff2a855da24f56ce186fba00000002a034203f5d59dbc7247cb1c33a0c2a55945c600002134965cb1f8d5f677b1aca3e80004bfd9e0000000a7c22d1c90f7fd7b5683765be2da627c81055fde510f621c55e1af27331ab5078d191b4237462e7bc5c11e90ba65291a2b529bd4cdb29298880006ea6ab23a2000754eb0157110c1ae0d4177172ae6d00000011da1d43218ad400000000000006540e150f80015fc000000326c0005e7000149cebb2e9186a9093c35264d42b015a495c34540010fc0005a8121c0003df064f5115ec0ee1e2000006c1525b1213c734ac10002ea54a4b6b4ec84240000006ee80010848b25f6000028a000000000000000040d112832430b017800023a0000001615456000000343c4d0c2a50901fc0003e318ab1cc79c8c001229e53e4e5b2b7c0000009b20002a4f62221b33e171800075e3c59f5c0006160c38754aa6c155aa0000e96a572162fc60005836658a4dc62ae78001e240003ac00039280007320002c6d8d62d732c8178d585a30000d9d17a26c296a6096a6a6829e79c15bac9f234b1f958e6a33a647a4996bfa15d154505e9b522c26d1b6a08865c0d6d3060c238243fd81c06b63a0654caf519491ab28026afd6aa9a405800e81608e0962689725d524435eb083d2d010f865952c4146d02ca3021e3610cb117f18e9789d0c04b338a9ac2ab2cc3d7955ce52ba83a3ab5ae6045c59526ed80820148895878947b750307254bc28648da45cb8e42e0a440002b0bf651daa5c2ac16c00005bc000000000038a00023a00000000000004172e9297201100d09b400003e60f263c82e33130299bc816d2f72925840004a100011e404673919d09686d2a5d1f69d260f8c91002b42127ac97581076985098653000010589d302039adb96a313b2cb6cac61111a900003020000002fa496de5a19d92dcda68ec67a20c99027f8168b395d3000019a24bd33200000001d041c4c6000191c0001cc33cd5ca03e7b859da314c8c0ad1cb00000005770002998f6800063c8628000908457a69c5e61b5312a9e8c2693e00012fd9c604f347b8d9c96deb711038c470b754469068b948ae1529b18eea000000000106c5d23a50f3c6a60003e8b09c0006d100000008da8393cca37c35f86f69bb41c9b64283769e89268c7d1349b206be9e050296299d4b5f2d599063bc8c6a86c8b99b2b4859bade93ac4ac54664e81184a26d100f0e307025560f73ccd0004e709fda3c1a73c0abcc728cec2af08d89f82e46d50db5cbe8225448498df4bea05eeb2c000000543b490000e9636d000002847d2110d510e400069db3d800
  | 32 => 0xa8b49dade7cd3bc73d037a01e9941b82589b249be01b0998360476b1950128394d74c348c39708c45706031add5bc1a610cacc57340000332d7f0666a50e91a144148a730408a71a491402e08dc000e890000784000a6f4bb80014923975da97ed4e234e3f70000000d0e0003595d223af1b8180db0e00000007740001e446f0dc4126b040bb0000f8eb55361091400000049b16b17f625f000000187400015c98056983c12a08000000b762ecab70a400005d113fc000c9437e0f2195ecf350a8e7000ed6c0958000000d98d5a31609c00005b3c0002b65e1350970167100059a0001cf266343b800167b0004766810000c720001190000b8100019a40008130001c940cfc2b1c5800191ac360001938cb819d521a3076b00000002558924876219800000000012191d40000000000000000be63dd1b5d1d30000000000a16000000178c0003506591840000b1480000000000ca00008a4f381f300035747a4379030000029e000000000117048b80000000000000001ea47f64f031c8000e2511500028b5b523f9496871e294012b789456368000000329d134d3c000284c000c6a0e298fcc4880308da3a82ca1e02e5a1a59084010002e980000003361a54f0650f000000089e9870000000984c425422c3539a7063cbb954bd29595721f61c187eb2425fb014e00000f30680000000e7800152fe8a42ea3b9afe65b3faabc0cf7abd48627e967080102a841998a9676242d5d9165fc5375c7567abd82efb2a0e5ca0a1d1a4e43f6b74327a1980f0d013f8b994f763f125dd51822e572256ae2d79c47024c0070e7caf424208ad9f6cc81e60ee524ca202062d3ca5674874e9e3824e99c0f59af91fa4f841fa118b90b5b4422ca4bcc2f4182a49c8803cd38b384dd00a483dddb7d77e6455bda911926d2e1deabe13ba27950607fc60457612a8b9ce0050044b041470e120029b8d415ee585133a484b604d3e30cf036058c03ea9d13544c82e892249d68b1cf89e492e6de222f9fe29fc3123d5a1a086ccbe37c1a083c44651b7243ca6c28a1740ed1ac641e46ba8913fa7b534a2010fcc1932b863111fe3551c7987048c5b02359f3d1ce1c62a42b458be7460e22dda634b972c5aa7427859e24a9eb4000cca2082d808bad9901b94c0a2e00000036574a209500238ed2ae27e4fb197d8bc5b900000000005560000000374c6720aaa2c5c00005b52bc51c000072ea4c0000bd30002c3942ec335318b4c0000000000000ada000000000000044b3794000000b260003440000be80f70b50000d28720b64a0000000d4b4c099800052ab8900003064c7e8fdace00002900000000006d681b03da42d713b94cd620fe6dea64816e00073493dd686b0a39e0d048e40583d7db91a4e4970000ee1ad0e284c997e0bea37c7068f757f800000003b4dd657900
  | 33 => 0x8d000159054c6ac84c5c7051100007d0e686dc22ab7d8e19811078a200e02b2d10f94e9800c9005088f840a0c6527a52081e8c730f2df84605e533682111e8d351350d349c6000566800768a95a000000101ca703b894f7b5c70de6d25e4913000000375d616692748000184a1075a58f284784c18d2320cd7269d05d03d800000074a00631608e170e1f581b20000cc98346fe89000029349ce9e83819418d060002778001174bb31e48e0562c79b30736e0c68aa85c443949bc97100025945ba00063825b5abc9254412a70c320eb12119d8dd00000002c79a5253240c800000004e60116f43a07c1087c000c801841c1b4e491be6d9d429c9aae6b468c0aa51762ad0e7395842298c0a39bd933462e3f22071b74dbcdb61ee4e1c00badbaec789ae0f19eb53d9ea71a0ca17e50927565cd8a0418884d70d96bdb575b554fdd7d3dc0fa6621f29780a280aa135429a6d5739c4850b649a1fe00007f4e6765f80019e412e1099dd8d6c4292e2840844416d4f8066929183868e2539a6468e6c60000000d8a7030000000000000247d4fe0004fd80019404d95d5673c0c2ba354c08cd6d0403058005cbe843e27e80016e90001942db4d64dd2000000065800034d330060200020e212c00068400035dd7867f94ca80016e40006d240013d80000bd8b840000006a39035d2bb09d7a84949920001e280000f406565e821cd142246218001294bacbd322150f800065d8000bfa4e21c415f00000005a1185c522642f398000000214082097849ca50000003fb8014211cb15d6eeaf724638acd6632155aba09b50329148306d17c94542d0e4d6ba3b53260d297a4752034a7b40ba9dc6c0890a2d00000001dfd66a14bebe9338d1a26b2d380cc482bdf1f1016c056d0d2c112d03c63ad3e565250be2895c0c2715f86f4f038d916062983400505b82c0108f94ed0ae75107933a0b2eb7d00c9ad578246656c0b640147ff584800080c0104ac33c1a92cd61e3aa03bca0003d0b720e5651a3b22489a2ead554c5aa8338760161ac5000000042ca0e85a00aa48b0000000b88000334175abd601a1a71aec780031aebb81aadef21afc07a8d726260848c34a626e800891b0b5e533967173e20d0edb7fc8a48ce5470081c0aada101a5101901d60a586ad366011b1da89504a15922619359eec4713c000099e8a2390652af62c96478a725126e1f00030ec012130000000000004c3912e2891a2b072492a86ba16300026102344000000000000caa00000007e6aa21379b98d327f037faa310cae290000c0143800000028640009bf000000055400007527a52bae0417b14e4cc34d26b4a6f54ea80b296eebd0b09626f20001182a9e00013001acd710000a3170c2f84df0054892e7837e9c4528edf73ef053e4a8148542b3b8d866cc01ab9eccf2d620a763291
  | 34 => 0x64cdb26ec0c6d0d6dbfa5f2cfb79822304f2e7120c8c310a8911240e3c021ac890101f0e9d2afd6b2dd32d51bdcceae7410b20dce977b2604158040e2df382158923846c70c00209a88e3051a68cc74b4058fa614ad2cb91eb068d9f86291eb857cdf6b396259d3136c0734b02daeb6222140a01c05b8b73536b00ce3faa6a179a8198e6625e427e4ed8d8e62219d054872333c0398c5029e25300017c631104d2e25721a69aec035dcd491e05eaffdc000e90c88c292fa47c56d5aec73c27c0408c657544d65847414a8ab4a8c185c4fc23b14a00f99d1697f3791d39ad6bbe691a705559d150d2833900ac3970098606c48c66ed1c786442bc25d17098c841f0d68d80fe84f35d093956cc25208515f38311626df0ae094a2ee7409a59a0002506a0af516893f15b23e0a506003ceb7bd348c370659184ff6e2e5d604a53862f01011ff54c83da5019958feeb7f666b2b040ce5938a0bac932d85541258cb8652212c0c8dd1a9debdf222d8488b370926b4dcadbf4cf93118b221e497196805ab8d0b9ba11a4c9190690ee810c4d857012d8f7a56813d32cc000cd362d0625c9aa9f2761cc513e0d04d28f61c803365ec8c780001aa4ad80014362c501cb2d80ae0621a4370c4a031452008712967936fe84355dc5ad19b840d6488ac3499435c5857d0638001536bef123c00031e0000002220b78000023927c1520006702930f9a0513e20e293c20001201c3c00000000030640009880002c853ce0c15298000a0e60f20e80015731972d317ada06e9a1041cdd178d977372ba90fa4e600031e1a14a2c2791ddc0004ab46688749028d04d6000000000067cb7e5200b0f51ba2fc2505180001475510b9800033f4a6e0000ec0aac0000003b3c500000e886961541824a9caff00007c89e41612adc0000005e219783049a139d32c02d2a91000159000000017d800091c00002fb4d983aa2364d00014024a71c80d3ca7cab4ce339f8f4e5cc3f28a7c61242700025f94740003693840f9c509079a1fb106689bf511d837caa60002ba40000006cea06c4340004a5dd660928f38b922a17e480623436d030a45300000008ee0002522fc4464211ea7088221e75ab79f808ecce87000000000012a4fb8000c92c8500014c43bea4131dd23c20266620a2658fb288122a0b494780005b3800025a28f4f12970cf64f632436c0ca4555000254dcfa9b700017c976e0001fb8048f2a0833ed87088049106810cf80004464038bdd0a60bc6d3b80ccc830f5478e8898f0ec55aed04224bb944e63bc000e1d71b8b2d4f08bfd85d5d0bec4fb45c894d57489dbc89fd840b7826cd8001c286700001508e20acf328ba789a637a0000e118c03ff41330f51e4000000308967ea5455b245400018d49aa17088475c40811e80629c02b59604000aa31d2b01d1303044
  | 35 => 0x8a0000c1769f17b4c3ea943c804580000211998000000000280a8a859208a5901d60a96df33cb296cbbcc2c3ee02cc292bf538c9ec1b9881753639908fe65d37a2678bb426029e95a2000d96534b9e95920ce89ea2857f200055800b0000b8e0c40bb000087b54811d1cd81f837024a183e515611a928b2655402333bd7ce5960003855b8a81e5588af995c51e00029facae6bd1ec8f455548e46a5b0b8074b6925cc2d911c3134f7935d33aacc3fae6bdc460006b304d8000e4e47d88c475c86263794b855ebc9393373daa2892411b670610c2906f34185f4cfa26d35180000421bbb839360d640002f3c00054f738aed8a580001f4a080a8b00000000000001088000000ed000028fb898e827da0000000ff4753430950118700025db2004c83f670c80008ce00000010480005233f3956c00023d00000000009784a118d91183750000000274338024363c30c000000000000063700038fc0000006f93060b881fa000000000000000025b0e92b1507a0000748d8200009dc0000005d800008dc5130000000000b641992354000de772783880000005a900007d06a800024f19b0c1306e2918fd00004238ab056274a9641de0b9ab7c722ab11192ba47390dac7e8cad4679a30000da155c842038e97c67123dab68c8a28629384c4cc635e03313bb06a6370ed9cee5fa00019098383a9000257824600028a0369c8ce6137ad1f85e4a1d56ff5b449a89b138b64e0005660079d408429a925eab9899700005887f04ce56ba8280000007f7ef0230973c74269f98f87b817a3011b10d446a438aa5a0bc0c6d00000000008e60fb000000015e1128a000003fe5d00cac3bbd4321d34580000002350001a9a6e245180015c258000000007660004b729a96a20cfb99b0c00000005854999552c541380e84bfebd12b600000000000001c480000006051880ac29fc5a3b7b92d400000029d965567f3d728bc000a5f3a689cd7eec770002504a70b8700034c57dcaa071c80000008b700033390da47b00003540002b40d61d140002e50002c14c881e50b700004aee8cc6b0000000e4c3aa1830af665815fa89cceebc20628ba80ac82d3c2ba650a83c34e41690000dec00005845daa5a2418a690901672d91f88000000000227970800000000000000001390a9d3e80002ac800007055e903f520862a614fa80000000004e1000000034b6d200000000002e81421ab478c2d480018f6d891b9ad833960df3f987be68403b2e79e8cd3682a00029dd0a0a8036a2cace4e98a145aadbd3632d3bc8001bc62940000e80cc21e61f8000cadc00e11014113286550000ce4aca6872f88000dc2dcd1a192f306aaffbbe38683166266c30440d8254a3c6a861d2ab5c1252f1d3367d369c2eed8ea54d59995751485ea56c4d319241961d5a8b96b47e04923648
  | 36 => 0x920f4aaae5e313403fc7633408f7859e00058078d1840a0968a1180000c505f9b37e0008414740dd0f5030c258e53dc2c80d4728001bbc2f10001db863e80a06039fdc888796c02e0fbac7d4c260289410dfa24db391286a3e4efb42c9e22ff1e0122c39a1395f0375553337d5802aecdfc69871d0a10e5a4dc439b410376c553840eec00000003ab8f946a6ca28180004e88a5000263927649d36f323d8d01bf53f33fd48ace7237800175f0000002e3e00067d3b824a4eaec3c6d5b770c70aef64619a07643570001d57700ce901724c98b6cd240163d48326d82442d591e01ea22b02453caac3616a554d9a4dd0ad05ddb16e0921928d0c790c901423d82764054b2354999ee320002ef57c2a165929ca885676a718272828890d11780013400005dad4fc0004086b9acd872a7c90001634e386335feb57d434418311b82190e08f2f414bc46adfc5b4cd10606743259938578a6c767318b42441c15475c6cdf2aab4c030f934c3076ae1824a147b359621c0eca0bf0cc318d161b8cac3a365cc6d094b810e1bfc69f15439d546c7675f22bca12ed7c30e99ebbb64b50dcaab67a6865d7f908c3de0726d19669c162976530018c0ed7a2e70344ec25d46de0022dce73b5ca219a59c5ae3ef87c10f096b05618849285b6430240d41a2fd4c75818000aaf57181dc0006a71f0962564eaa4315a2a471a14e45515fd90cd132d012d7c5e87f41e9c177b826359d346c8a0cbc6c40bd58cab236f82a54d520b50db8bf82a1027738e250c14b060001810c54000414265c0883cb63e371c47ee570000c9c0009040001b2c000516383800000000027af3b52f650782a241dcd07bf2d99a980002762f72d9227c28559700004c28c280037097a8bda1ab000119800000026880001c1bcfae0db282006a81fa42d69c500012a456e00043a9638000000622a92dc3ce8f07000017d619e2b89d000008cb6ba81ed0242cd14c9e788bc8eadd34da95cd75d13a9bb97da3e06fc2530b828db0000000496c99628ba706de4ed07800007300003298000000b8f64f0000d12136bb58541af255f3af6e4163a85e4f18193768000000000000086e559ae442387dd8000000000c5d000022d2ea0000002af8344265
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x84d88c844c971580323f61321d32d45600c96bc0c744cb51580320049326132545600c80184c874c951580325a7031d132545600c84d88c874cb4158032007031d532d05600c801435911d541580320062321d32505600c801c0c754c94158032004b226132441600c801e813250510580320060de0571592549410f84c8720d5198a500058324d51d06629400160c935454198a500048be61541516294095628905505458a5043e1321c83545629400184c52e197394a5000705585419ce529400124d989ca6314a50004936602198c5294001c45710866314a50005926402198c529400184c75e19320ca500068320c82547645414943591a15711915052d0de45855c464540014389061571191500050d646505c464540014359114171191500068320c82544645414b836855c451191500060da1571c40645409583870a1b745515000705585419ce5214001837815c565d52403f513255764c8329000184e83a0b71d95400050d64440dc4655000184c8320971195400050d644405c465500952349850510195400061320c825c6651000184c8320971594400061a200825c56510001837815c565d50400061321c83546621000184c8720d515884000705587519ce4210001c1561546739084000689e10825d56110001a4483209755844000698200825d56110167a3384e0175584400060d61e75d516110001624925d754584405958ce4175d516110001a1754a0e52584400068cd51809496110001296932164258440006859d6839096110001a1575a0e4258440136a1a098390961100532a692e103258440136a1211320c9611000184c7220d51597200058c25941443654800184e829cf71d952000613a0e82dc7654800184c8320971195200058364e82d046548001a0c8320951d91200052c640215c46448001a0c8320951191200052c25d4144163480038b0875051058d2043d912456314c524800144e96e15739092000703193855ce4248001c0c64215739092000453a63655ce424806b48e96d91739092000703d94645ce4248001c0c65191739092057f03193515ce424800114c98545739092000513259515ce424815dc0c64545739092000523259415ce4248001d814144173909200041b259811d5324800142c96504754c92000658605101d53248001d2141440754c9200041b25d81195324800142c97544644c9201368319285d0d32480fd24f98197434c9201bd1325c654c9304806b48c97191324c120007031d4644c9304800105d981d43158c2000515644750c56308001455911d47158c20006131d5821c56308001858756007158c2000417a5e87545630800184c8221d5158c2000613c8087545630800184d2021d5158c200061321f82545630800141c975474158c200050725d5150563080fd44c9558d7294c20
  | 1 => 0x14b5050b81241814488428a4c52563f20570be1f8dd3c0d9c075225f39885646e58001289727870a679272b85c9b3ea40003a80040da7a050451e650191cc7c14684c004d6040000003a8057f9f1fd5c0026000013800000001aad000a8d6004310d2a002f0015e465d8b50400000a172bc162dc00005589400005d000e80000000040000001445b800f4840025ad032661a28100003fa2d6c9d00258b0440016c3c0f5f988f8983d82065ac291a400b311229483e00154308c0a8c04e60001311223049242b163c0d94c204d00036a5190180000319682e64428001876001856277442a4745daa1286a0e2821d6a702c9bcce315e90466710d2a880992e920d8395429c78a1601145e724902c3e68470ac0e308228c76021e05023e000b01070801030008000f000057010002040009001b2d2700000200020303000802032c1107040144030018002c0a10030119080001002f0814184101220c0060de05715db549500182d7660a70d52540050be4951dd95415001258906154198e5200585646855066394801617916154198e520058624185506639480184c8320971997420061320c825c565d080105d981d43158e42006161d5800c5639080124d98d0b7558e4200515644751c5639080184c756087158e42006161d5801c5639080105e97a1d5158e420061320887545639080184f4221d5158e420061310887545639080184f2021d5158e420061321f82545639080141c975474158e420050725d51505639080105c976171058e42134a32518284163908fd44c9558d7294e420058c64061507654c80143a90dd274d95320040fe61741d3654c8018717160061195320058c64061504654c96d84c8320971195320041b259819d7424c80144d959c7764c83201c3366071dd9320c80144d951c7764c8320053264071dd9320c80144e97d47764c8320051325d51dd9320c801c8471507764c83201c3366376dd5320c88344d98ddb754c8320049366264dd5320c801c0f76d07754c83200703dd941dd5320c88384e87dd8754c8323f493a62641d5320c80114d981c4754c83200651604711d5320c801549901c4754c8320051325d611d5320c801c4471584754c832007411c5411d5320c8fd84c75a1e654c8323f61321f75995320c8010cc97606654c8323f691d4581995320c80144c97546654c83221c9325586d51320c8018c481dd9704c83200613ddb855c1320c801944811d5704c8323f513a57874c9600c84d48e94e1d325803200513a5f854c9600c801c0c74e153258032007031d0854c9600c80124e98dd5325803200513a60754c9600c8fd44c981d5325803200513644754c9600c801c0c75dd1325803200703dd4744c9600c801c0c751d1325803200692217804c9600c8010cc984c971580323f613215325c5600c
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x446011051a92700000080002851a11d5801c56390801640d00e2a0eec9906400c50605901c4754c832005a034038a823aa641900204ca8644754c9600c8018063a130992a2b006400b01684754c941580320055015099282882c019003441716402198c529400180632130a8ae72124000a14684756007158c20
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x20005005b11d0984c95158032004404b9684754c94158032
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x1
  | 3 => 0x3
  | 4 => 0x8a
  | 5 => 0x4
  | 6 => 0x5
  | 7 => 0x98a
  | 8 => 0x128a
  | 9 => 0x150a
  | 10 => 0x10a
  | 11 => 0xa0a
  | 12 => 0x130a
  | 13 => 0x180a
  | 14 => 0x14a
  | 15 => 0x6
  | 16 => 0x198a
  | 17 => 0xa4a
  | 18 => 0x134a
  | 19 => 0x3ca
  | 20 => 0xcca
  | 21 => 0x15ca
  | 22 => 0x40a
  | 23 => 0xd0a
  | 24 => 0x160a
  | 25 => 0x188a
  | 26 => 0x44a
  | 27 => 0x1a0a
  | 28 => 0xd4a
  | 29 => 0x164a
  | 30 => 0x74a
  | 31 => 0x1a8a
  | 32 => 0x104a
  | 33 => 0x194a
  | 34 => 0x5c9
  | 35 => 0x17c9
  | 36 => 0xcc992
  | 37 => 0x98cd2
  | 38 => 0xccd
  | 39 => 0x15c992
  | 40 => 0x995d2
  | 41 => 0x15cd
  | 42 => 0xd0992
  | 43 => 0x98d12
  | 44 => 0x160992
  | 45 => 0x1609
  | 46 => 0x99612
  | 47 => 0x44992
  | 48 => 0x449
  | 49 => 0x98452
  | 50 => 0x99a12
  | 51 => 0x1a0992
  | 52 => 0x409
  | 53 => 0x10b
  | 54 => 0x130b
  | 55 => 0x14b
  | 56 => 0x1649
  | 57 => 0x134b
  | 58 => 0xcd512
  | 59 => 0x150cd2
  | 60 => 0xd1512
  | 61 => 0x150d12
  | 62 => 0x1a1512
  | 63 => 0x151a12
  | 64 => 0x5cb
  | 65 => 0x17cb
  | 66 => 0x104b
  | 67 => 0x1a8b
  | 68 => 0x160112
  | 69 => 0x11612
  | 70 => 0x10c
  | 71 => 0x1a89
  | 72 => 0x1a8112
  | 73 => 0x11a92
  | 74 => 0x749
  | 75 => 0x14d
  | 76 => 0x1949
  | 77 => 0x134d
  | 78 => 0x41312
  | 79 => 0x130412
  | 80 => 0x130c
  | 81 => 0x161312
  | 82 => 0x131612
  | 83 => 0x75312
  | 84 => 0x130752
  | 85 => 0x1a9312
  | 86 => 0x131a92
  | 87 => 0xa4152
  | 88 => 0x44152
  | 89 => 0x14452
  | 90 => 0x44c
  | 91 => 0x14c
  | 92 => 0x164152
  | 93 => 0x15652
  | 94 => 0x164c
  | 95 => 0x74152
  | 96 => 0x14752
  | 97 => 0x105992
  | 98 => 0x194152
  | 99 => 0x15952
  | 100 => 0x198a52
  | 101 => 0xa5a92
  | 102 => 0x104a52
  | 103 => 0xa5052
  | 104 => 0x1a8a52
  | 105 => 0x199352
  | 106 => 0x45352
  | 107 => 0x134452
  | 108 => 0x134c
  | 109 => 0x165352
  | 110 => 0x135652
  | 111 => 0x75352
  | 112 => 0x134752
  | 113 => 0x195352
  | 114 => 0x135952
  | 115 => 0x199052
  | 116 => 0x1a9992
  | 117 => 0x199a92
  | 118 => 0xcc3d2
  | 119 => 0x3ccd2
  | 120 => 0x40cd2
  | 121 => 0xcc412
  | 122 => 0x188cd2
  | 123 => 0xcd892
  | 124 => 0x44cd2
  | 125 => 0xcc452
  | 126 => 0xcce
  | 127 => 0xcda12
  | 128 => 0x1a0cd2
  | 129 => 0x1895d2
  | 130 => 0x15d892
  | 131 => 0x1a15d2
  | 132 => 0x15da12
  | 133 => 0x170d
  | 134 => 0xd4452
  | 135 => 0x5c452
  | 136 => 0x17c452
  | 137 => 0x457d2
  | 138 => 0x104452
  | 139 => 0x45052
  | 140 => 0x104c
  | 141 => 0x1a8452
  | 142 => 0x45a92
  | 143 => 0x1a8c
  | 144 => 0x1a0d52
  | 145 => 0x1a1652
  | 146 => 0x17d652
  | 147 => 0x105652
  | 148 => 0x165052
  | 149 => 0x1a9652
  | 150 => 0x165a92
  | 151 => 0x104752
  | 152 => 0x75052
  | 153 => 0x1a9052
  | 154 => 0x105a92
  | 155 => 0x1a9952
  | 156 => 0x195a92
  | 157 => 0x1849
  | 158 => 0xb89
  | 159 => 0xb8b
  | 160 => 0x19c9
  | 161 => 0xbc9
  | 162 => 0xbcb
  | 163 => 0xbcc
  | 164 => 0xbcd
  | 165 => 0x19cd
  | 166 => 0xb8c
  | 167 => 0x184c
  | 168 => 0x19cc
  | 169 => 0x11992
  | 170 => 0x5c44cda
  | 171 => 0x5ccc45a
  | 172 => 0x184b
  | 173 => 0x19cb
  | 174 => 0xbccd5
  | 175 => 0x19ccd5
  | 176 => 0x5ca
  | 177 => 0x1a4a
  | 178 => 0x1a81199a
  | 179 => 0x19811a9a
  | 180 => 0xccbd5
  | 181 => 0xcd9d5
  | 182 => 0x445d2
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 47
  | 7 => 1910
  | 6 => 6058
  | 5 => 3743
  | 4 => 194
  | 3 => 11
  | 2 => 2
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
  | 2 => packedAt gbK2 (i*92) 83
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
  | 2 => gbHint (packedAt gbK2 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1369+((h/21+packedAt gbK8 (1222+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (80114+((h/787+packedAt gbK7 (70670+(h % 787)*12) 12) % 2835)*12) 12
  | 6 => packedAt gbK6 (322452+((h/2262+packedAt gbK6 (290784+(h % 2262)*14) 14) % 9853)*14) 14
  | 5 => packedAt gbK5 (238348+((h/1347+packedAt gbK5 (220837+(h % 1347)*13) 13) % 4851)*13) 13
  | 4 => packedAt gbK4 (14124+((h/68+packedAt gbK4 (13580+(h % 68)*8) 8) % 248)*9) 9
  | 3 => packedAt gbK3 (903+((h/3+packedAt gbK3 (891+(h % 3)*4) 4) % 15)*5) 5
  | 2 => packedAt gbK2 (186+((h/1+packedAt gbK2 (184+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfff0ff03fe07ffffc0f01e03f027b39f667e93
  | 1 => 0x3ff07fc0ff81e01fffffffff0da4c639993ff
  | 2 => 0xfc3ff8000fffe001ff001ffc0f1c707ce1e31c
  | 3 => 0x3ffffff0000001ffffe0000fe07f80fe03e0
  | 4 => 0x3ffffffffffffe000000000fff8000fffc00
  | 5 => 0xffc0000000000000000000000fffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x145019005200a28cc89052096000918d222691
  | 1 => 0x282024404881410012504a2804a0422089026
  | 2 => 0xd83568214b56c0257a80995827147054e16318
  | 3 => 0x5039b5ab60428049bccad0104ba07a80f603c0
  | 4 => 0x822ec6f38de71970100300608dff0000ddd800
  | 5 => 0xe30000c201841180200c01830effef7b000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeee8eeeaccc8feeaeee8eeeaccc8feeaeee8eeeaccc8feeaeee8eeeaccc8feeaeee8eeeaccc8feeaeee8eeeaccc8feeaeee8eeeaccc8feeaeee8eeeaccc8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37021
namespace PEqualNP.Outside.L_meta_37021
open PEqualNP.Outside.L_meta_37021.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 21 := bs0_3_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 14 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_64 : Interval s1Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_96 : Interval s1Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_128 : Interval s1Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_160 : Interval s1Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_192 : Interval s1Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_224 : Interval s1Atlas 3 224 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 227 := (concat (concat (concat bs1_3_0 bs1_3_32) (concat bs1_3_64 bs1_3_96)) (concat (concat bs1_3_128 bs1_3_160) (concat bs1_3_192 bs1_3_224)))
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
theorem bs1_4_128 : Interval s1Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_160 : Interval s1Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_192 : Interval s1Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_224 : Interval s1Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_256 : Interval s1Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_288 : Interval s1Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_320 : Interval s1Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_352 : Interval s1Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_384 : Interval s1Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_416 : Interval s1Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_448 : Interval s1Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_480 : Interval s1Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_512 : Interval s1Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_544 : Interval s1Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_576 : Interval s1Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_608 : Interval s1Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_640 : Interval s1Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_672 : Interval s1Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_704 : Interval s1Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_736 : Interval s1Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_768 : Interval s1Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_800 : Interval s1Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_832 : Interval s1Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_864 : Interval s1Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_896 : Interval s1Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_928 : Interval s1Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_960 : Interval s1Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_992 : Interval s1Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1024 : Interval s1Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1056 : Interval s1Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1088 : Interval s1Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1120 : Interval s1Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1152 : Interval s1Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1184 : Interval s1Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1216 : Interval s1Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1248 : Interval s1Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1280 : Interval s1Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1312 : Interval s1Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128))) (concat (concat bs1_4_160 bs1_4_192) (concat bs1_4_224 (concat bs1_4_256 bs1_4_288)))) (concat (concat (concat bs1_4_320 bs1_4_352) (concat bs1_4_384 (concat bs1_4_416 bs1_4_448))) (concat (concat bs1_4_480 (concat bs1_4_512 bs1_4_544)) (concat bs1_4_576 (concat bs1_4_608 bs1_4_640))))) (concat (concat (concat (concat bs1_4_672 bs1_4_704) (concat bs1_4_736 (concat bs1_4_768 bs1_4_800))) (concat (concat bs1_4_832 bs1_4_864) (concat bs1_4_896 (concat bs1_4_928 bs1_4_960)))) (concat (concat (concat bs1_4_992 bs1_4_1024) (concat bs1_4_1056 (concat bs1_4_1088 bs1_4_1120))) (concat (concat bs1_4_1152 (concat bs1_4_1184 bs1_4_1216)) (concat bs1_4_1248 (concat bs1_4_1280 bs1_4_1312))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_64 : Interval s1Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_96 : Interval s1Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_128 : Interval s1Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_160 : Interval s1Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_192 : Interval s1Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_224 : Interval s1Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_256 : Interval s1Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_288 : Interval s1Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_320 : Interval s1Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_352 : Interval s1Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_384 : Interval s1Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_416 : Interval s1Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_448 : Interval s1Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_480 : Interval s1Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_512 : Interval s1Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_544 : Interval s1Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_576 : Interval s1Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_608 : Interval s1Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_640 : Interval s1Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_672 : Interval s1Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_704 : Interval s1Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_736 : Interval s1Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_768 : Interval s1Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_800 : Interval s1Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_832 : Interval s1Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_864 : Interval s1Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 890 := (concat (concat (concat (concat bs1_5_0 (concat bs1_5_32 bs1_5_64)) (concat (concat bs1_5_96 bs1_5_128) (concat bs1_5_160 bs1_5_192))) (concat (concat bs1_5_224 (concat bs1_5_256 bs1_5_288)) (concat (concat bs1_5_320 bs1_5_352) (concat bs1_5_384 bs1_5_416)))) (concat (concat (concat bs1_5_448 (concat bs1_5_480 bs1_5_512)) (concat (concat bs1_5_544 bs1_5_576) (concat bs1_5_608 bs1_5_640))) (concat (concat bs1_5_672 (concat bs1_5_704 bs1_5_736)) (concat (concat bs1_5_768 bs1_5_800) (concat bs1_5_832 bs1_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_32 : Interval s1Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 44 := (concat bs1_6_0 bs1_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_7_0 : Interval s1Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_7 : Interval s1Atlas 7 0 1 := bs1_7_0
theorem alls1 : ∀ k ≤ 7, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi
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
theorem bs3_3_0 : Interval s3Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 4 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 12 := bs3_4_0
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
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 8 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 9 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 1 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1 := bs5_4_0
theorem alls5 : ∀ k ≤ 4, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 2 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 11 := bgb_3_0
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
theorem bgb_4_192 : Interval gbAtlas 4 192 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 194 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192)))
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
theorem bgb_5_3712 : Interval gbAtlas 5 3712 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3743 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768)) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896))))) (concat (concat (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344)))) (concat (concat (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696)) (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)))))) (concat (concat (concat (concat (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)) (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)) (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 bgb_5_2272)))) (concat (concat (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)) (concat (concat bgb_5_2400 bgb_5_2432) (concat bgb_5_2464 bgb_5_2496))) (concat (concat (concat bgb_5_2528 bgb_5_2560) (concat bgb_5_2592 bgb_5_2624)) (concat (concat bgb_5_2656 bgb_5_2688) (concat bgb_5_2720 bgb_5_2752))))) (concat (concat (concat (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)) (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 bgb_5_2976))) (concat (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104)) (concat (concat bgb_5_3136 bgb_5_3168) (concat bgb_5_3200 bgb_5_3232)))) (concat (concat (concat bgb_5_3264 (concat bgb_5_3296 bgb_5_3328)) (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456))) (concat (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 bgb_5_3584)) (concat (concat bgb_5_3616 bgb_5_3648) (concat bgb_5_3680 bgb_5_3712)))))))
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
theorem bgb_6_6048 : Interval gbAtlas 6 6048 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6058 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 (concat bgb_6_384 bgb_6_416)) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))) (concat (concat bgb_6_544 (concat bgb_6_576 bgb_6_608)) (concat bgb_6_640 (concat bgb_6_672 bgb_6_704))))) (concat (concat (concat (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)) (concat bgb_6_832 (concat bgb_6_864 bgb_6_896))) (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)))) (concat (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280))) (concat (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)))))) (concat (concat (concat (concat (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)) (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664))) (concat (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760)) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)))) (concat (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))))) (concat (concat (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432))) (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)))) (concat (concat (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720)) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816))) (concat (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008))))))) (concat (concat (concat (concat (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168))) (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360)))) (concat (concat (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456)) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552))) (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744))))) (concat (concat (concat (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840)) (concat bgb_6_3872 (concat bgb_6_3904 bgb_6_3936))) (concat (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032)) (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)))) (concat (concat (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224)) (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320))) (concat (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512)))))) (concat (concat (concat (concat (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608)) (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704))) (concat (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800)) (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896)))) (concat (concat (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)) (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088))) (concat (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184)) (concat bgb_6_5216 (concat bgb_6_5248 bgb_6_5280))))) (concat (concat (concat (concat bgb_6_5312 (concat bgb_6_5344 bgb_6_5376)) (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472))) (concat (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568)) (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)))) (concat (concat (concat bgb_6_5696 (concat bgb_6_5728 bgb_6_5760)) (concat bgb_6_5792 (concat bgb_6_5824 bgb_6_5856))) (concat (concat bgb_6_5888 (concat bgb_6_5920 bgb_6_5952)) (concat bgb_6_5984 (concat bgb_6_6016 bgb_6_6048))))))))
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
theorem bgb_7_1888 : Interval gbAtlas 7 1888 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1910 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat (concat bgb_7_224 bgb_7_256) (concat bgb_7_288 bgb_7_320)) (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 bgb_7_448)))) (concat (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672))) (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800)) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928))))) (concat (concat (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152))) (concat (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280)) (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)))) (concat (concat (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632))) (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760)) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 bgb_7_1888))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 47 := (concat bgb_8_0 bgb_8_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 44, 60),(inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 33, 41),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 5 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeee8eeeaccc8feeaeee8eeeaccc8feeaeee8eeeaccc8feeaeee8eeeaccc8feeaeee8eeeaccc8feeaeee8eeeaccc8feeaeee8eeeaccc8feeaeee8eeeaccc8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809448 * 2 ^ 32 + 4008365256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37021.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,4]⟩,⟨.and,[0,4]⟩,⟨.or,[1,7]⟩,⟨.and,[3,6]⟩,⟨.and,[0,8]⟩,⟨.or,[0,9]⟩,⟨.or,[2,3]⟩,⟨.and,[5,11]⟩,⟨.or,[8,13]⟩,⟨.and,[12,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4008365256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4008365256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37021

open PEqualNP.Outside.L_meta_37021 in
theorem PEqualNP.Outside.L_meta_37021 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4008365256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4008365256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
