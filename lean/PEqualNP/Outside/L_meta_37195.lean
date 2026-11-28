import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37195.Model
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


end PEqualNP.Outside.L_meta_37195.Model

namespace PEqualNP.Outside.L_meta_37195
open PEqualNP.Outside.L_meta_37195.Model
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

def SBf (j : Nat) : Nat := [7, 7, 5, 5, 7, 5].getD j 0

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

end PEqualNP.Outside.L_meta_37195

namespace PEqualNP.Outside.L_meta_37195
open PEqualNP.Outside.L_meta_37195.Model
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
end PEqualNP.Outside.L_meta_37195
namespace PEqualNP.Outside.L_meta_37195
open PEqualNP.Outside.L_meta_37195.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x340088028007804800a8038000004c00b8a181800000491253aa00003e084000001580000000108010800064d80200000352011800001380160068500a8000001c00000600003c00000004c00e0058020000000012000000102002000608000000c001ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x50d09801125018028060e9f000f801e9a0b02001a802b16a285a395a580002a0f27a926891ca204198b9421ad0c9012a8ac981711ada4ab961d1c0700000e29811080260a9480000323191380079e211520a4200c131d88868a120017ac00802a801f8027048288001b1880039b8d80011a2000c52480000040d00000400628000030824c020400101bba8a87745150e7ca1a14f55242afa9a855c5350aeea2a15d14542bda8285785050b3ea6a16714d42d7a9285b75150b68a2a16ed41429e28285b85050a70a0a14f95042bb28e657551cca7ca9194f55232bb28c6575518ca7ca8194f55032afa9a835c535067ea898cf15131ea988633e54c867aa990d794f21aea9e435e53886baa710cf950219eaa0435e53902baa7205d94640baa8c819e539033aa7204f54a40db28c81b5519027ca1204f548409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2eca2185d544309f2a6413d54c837081904fd52209e2a4413f5448278a89057d4d20ae29a417751482e8a2904f950209eaa0415e53082baa6105d94420baa8841b8400827ca9884f553109faa2213c54442bea6885714d10b7a92216c52442bca6085754c10
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x20406aec809c514c5150b1b5314142c614c5050b335114142cc1445050a94644c431c594e51902396510020
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 5 => packedAt s1K5 (802+((h/14+packedAt s1K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s1K4 (2694+((h/30+packedAt s1K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s1K3 (312+((h/2+packedAt s1K3 (304+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 2 => 0x3f80ffffe03f81ff83f03e0ffffc1f01d89fcc
  | 3 => 0x3fff03fffffffffffc003ff03fffffffe0e3ff
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x848a1008c489082014b14a114a2129540b2e15
  | 2 => 0x9526299143922ae58155168d96e51a0cd896cc
  | 3 => 0x22144aa20924614aa80825a4254a54a960c16a
  | 4 => 0x3458b34492074db34e6d810939b38831bd03b0
  | 5 => 0x3860c3871c3871dc738e39ce01c210c1f6f800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37195
namespace PEqualNP.Outside.L_meta_37195
open PEqualNP.Outside.L_meta_37195.Model
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
  | 0 => 0xfff81fffffffff81ffc07ff03ffffffe71e3ff
  | 1 => 0x3ffe03f01fc07fe0fff81ffc1f03f01be3ccc
  | 3 => 0x3fffffffffffffff00001ffffffffffc03fff
  | 4 => 0xfc00003ffe0007fffffffe0001ffc001ffc0f0
  | 5 => 0xffffffc0000007fffffffffffe000001ffff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x84a42912449228052d22a541252695430e155
  | 1 => 0x58d0c9921c916b960556a8b550b63a0cb62ccc
  | 3 => 0xa2a105244922452aa0244129a52c94a9c016aa
  | 4 => 0x32c59628903a75cd39a74c0921cf1831db40f0
  | 5 => 0xc3061830e1c38671ce3871ce380820c16dbb00
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeeeee00aa00aa00eeeeee00aa00aa00eeeeee00aa00aa00eeeeee00aa00aa00eeeeee00aa00aa00eeeeee00aa00aa00eeeeee00aa00aa00eeeeee00aa00aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37195
namespace PEqualNP.Outside.L_meta_37195
open PEqualNP.Outside.L_meta_37195.Model
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
  | 0 => 0xfff80fff01fc0783ffc0fff07ff03f00f1e7cc
  | 1 => 0x3fff03ffffffffc0fff01ff81ffffff3e38ff
  | 2 => 0x3fffffffffffffff00001ffffffffffc03fff
  | 4 => 0xfc00003ffe0007fffffffe0001ffc001ffc0f0
  | 5 => 0xffffffc0000007fffffffffffe000001ffff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x18ca61911c496b80b2d45a742a76390c70e3cc
  | 1 => 0xa850a4922491229405554894a0926a54362855
  | 2 => 0x52a1422449224529502091294d2c94a9c015aa
  | 4 => 0x62c58b28903a75ce69a69c0849cf1831db40f0
  | 5 => 0x83060c30e1c386738e38e1ce700820c1adbe00
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeee0e0c0c0c0c0eeeee0e0c0c0c0c0eeeee0e0c0c0c0c0eeeee0e0c0c0c0c0eeeee0e0c0c0c0c0eeeee0e0c0c0c0c0eeeee0e0c0c0c0c0eeeee0e0c0c0c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37195
namespace PEqualNP.Outside.L_meta_37195
open PEqualNP.Outside.L_meta_37195.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2126119001801d2000b95102a3cb06127071b020129e16895a72815c2d480de35001d63330f8fb76035fb65ee5a1722a40190420000000130000c519d00f5d8a5068012000a08203000000128082010aa804400c0105bda8287785050edca421db54843bba8a85745150abca6215754c429faa2653c544caeea2995d14532bda826578504ca7ca8194f55032b7a92836c52506f4a020de540419f2a6633d54cc6dca598db54b319f2a4633d548c6f4a118de542319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502eca2205d544409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f209f2a4413d54882eca3105d546209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
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
  | 4 => packedAt s4K4 (1875+((h/21+packedAt s4K4 (1728+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 1 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 2 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 3 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x309118a290425014a849d0930194d21886315c
  | 1 => 0x52922864129212816942528510a154a8b284c5
  | 2 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 3 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37195
namespace PEqualNP.Outside.L_meta_37195
open PEqualNP.Outside.L_meta_37195.Model
def s5K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (6+((h/1+packedAt s5K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x80fe07fffff81c1f07fff81e1fffff008fc3fc
  | 1 => 0xfffff81f81ffffe007c0ffffe1f01fff0cfccf
  | 2 => 0xffffffe001fffffff800fffffe001ffff0ff0f
  | 3 => 0xfffffffe001fffffff001fffffe001ff0ff0
  | 4 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa662314530432c0541593b061294d90c85c15c
  | 1 => 0xaa450c8529514a082e84d2b21a14a550c54c5
  | 2 => 0x1448a2032522094b48109254540294a8b0ab0a
  | 3 => 0x589104924034527294a20419894b00315a0ea0
  | 4 => 0x60e1c71c79c79f9ce73ce781118c18c1eff000
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xfac0eac0fac0eac0fac0eac0fac0eac0fac0eac0fac0eac0fac0eac0fac0eac0fac0eac0fac0eac0fac0eac0fac0eac0fac0eac0fac0eac0fac0eac0fac0eac0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37195
namespace PEqualNP.Outside.L_meta_37195
open PEqualNP.Outside.L_meta_37195.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001007fd5007fe54007f55007fc54007fd4c01fe53007f54c01fc5301ffd0c01fe43007f50c07fc43007fd4801fe52007f54801fc5201ffd0801fe42007f50807fc42007fcc801fe32007f4c801fc32007fd4405fe51007f54405fc5101ffd0405fe41007f50405fc41007fcc405fe31007f4c405fc31007fc8405fe21007f48405fc21007fd4003fe50007f54003fc5001ffd0003fe40007f50003fc40007fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x864001ff4c32000ff86190007fe20c8003f71064001fe8832000ff84190007ec20c8003ff8864001ff8432000ff82190003ff65480017fb2a4000ff99520005fcca90003fd65480017eb2a4000ff19520005f8ca90003ff64480017fb224006ff9912001dfcc890003fd64480017eb224006ff1912001df8c890003ff544800dff2a24000ff55120037f8a890003ff63480017fb1a4000ff98d20005fcc690003fd63480017eb1a4000ff18d20005f8c690003ff5348001ff29a4000ff54d20007f8a69001bff4348001ff21a4000ff50d20037f88690006ff6248001ffa924000ff94920007faa490003fc524800dffa124000ff90920007fa849001bfc4248001ff9924000ff8c920007dc6490003fd3248001f69924000ff0c920007fec290002ff614800bff30a4002bf98520007fac290017fc61480057e30a4000ffd452002ffca290003fd514800bfe28a4006ffd052002ffc8290003fd414800bfe20a4000ffcc52002ffc6290003fd314800bfe18a4000ffc852002ffc4290003fd214800bfe10a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe4090003fb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fa1048003fe0824000ffd9510005feca880037f65440013fb2a2000ff99510005fcca88003fd65440017eb2a2000ff19510005f8ca880037c65440013e32a2000ffd9110005fec888013fe64440077f3222000ff59110005fac888013fc64440077e3222000ffd5110027fca888003fd5444009fe2a22000ffd8d10005fec688003fe63440017f31a2000ff58d10005fac688003fc63440017e31a2000ffd4d10007fca688003fd5344001fe29a2004ffd0d10007fc8688003fd4344009fe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e3122000ffd4910007fca488003fd5244001fe2922004ffd0910007fc8488003fd4244009fe2122000ffcc910007fc6488003fd3244001fe1922001bfd8510017fea28800bfe5144005fb28a2002ff54510007eaa28800bfc5144005ffa0a2002ff90510017fa828800bfc4144005ff98a2002ff8c510017ec628800bfd3144001fa98a2002ff0c510017fe4288003f72144005ff10a2002ff48510017f8428800bf421440037fb022001ffd411000ffca088007fa5044003fea822000fe5411000ff8a088007ff4044003ff2022001ff5011000ff88088007ff3044001fd9822001ff8c11000ffa6088007fc3044003fc1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fd61cc0017eb0e600dff18730015f8c398003ff51cc019ff28e6000ff54730067f8a39803bff41cc019ff20e6000ff50730067f88398037ff31cc019ff18e6000ff4c73006ff86398003ff21cc019ff10e6000ff48730067f84398006fd60cc003ffa866000fed433000ffca198007fd50cc003fe2866001fe1433000ffe8198007fe40cc003fea066001ff1033000ffc6198007de30cc003fd1866001ff0c33000fb86198007fe20cc003fe1066001ffc433000ffc2198007fa10cc003fe0866000ffd9530005feca98003fe654c0017f32a6000ff59530005faca98003fc654c0017e32a6000ffd9130005fec89802ffe644c0077f3226000ff59130005fac89802ffc644c0077e3226000ffd513005ffca898003fd544c017fe2a26001bfd8d30007fea698003fe534c001fea9a6000ff14d3005ffe8698003fe434c001fea1a600bff10d30007fec498002ff624c001ff3126000ff58930007f8c498002fc624c001ffa926000ff94930007faa498003fc524c017ffa126000ff90930007fa849802ffc424c001ff9926000ff8c930007fa6498003fc324c001ffb0a6000bfd8530057fcc29800afe614c001feb0a600aff18530015f8c298003ff514c015ff28a6000ff54530057f8a29802fff414c015ff20a6000ff50530057f88298003ff314c015ff18a6000ff4c530057f86298003ff214c015ff10a6000ff48530057f84298006ff604c003ffa826001ff9413000ffaa098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9826000fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007fe204c003fe1026001ffc413000ffc2098007fc104c00fffb2e4000bfd9720007fccb90002fe65c8001bf32e40009f99720007facb90002fd65c8001beb2e40009f5972003ff8cb90002fc65c800fffb264000bfd932004ffcc99000efe64c8001feb264000bf5932003ff8c99000efc64c8001ffaa64009ff95320007faa990027fc54c800fffb1e4000bfd8f20007fcc790002fe63c8001feb1e4000bf58f2003ff8c790002fc63c8001ffa9e4000ff94f20007faa790003fc53c8013ffa1e4000ff90f20007fa8790027fc43c80037f3164000ffd4b2003ffca590003fd52c800ffe2964009ffd0b2003ffc8590003fd42c800ffe2164000ffccb2003ffc6590003ee32c8001fe9964000fb4cb2003ff8659001fff61c8011ff30e4002bf98720007fac390002fd61c800ffe30e4002bf18720007fea390023fe51c8001fea8e4008ff1472004ffe8390023fe41c8001fea0e4008ff10720007fe6390023fe31c8001fe98e4008ff0c72003ffe4390023fe21c8001fe90e4007ff0872000dfac190007ff50c8003ff2864001ff5432000ff8a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1
  | 2 => 0x50007faa8a8047fc5454001ffb1aa000bfd8d50007fcc6a8003fd6354001fe31aa000bf18d50007fea6a80037f5354001ff29aa000ff54d50006faa6a8003fc5354023ffa1aa000ff90d50007fa86a8047fc4354001ffb12a000bfd8950007fcc4a8003fd6254001fe312a000bf18950007fea4a8003fe5254001fea92a000ff1495008ffe84a8003fe4254001fea12a011ff10950007fe64a8003fe3254001fe992a000ff0c950007fec2a8002ff6154021ff30aa002bf98550007fac2a8043fc61540057e30aa000ffd4550087fca2a8003fd5154021fe28aa011ffd0550087fc82a8003fd4154021fe20aa000ffcc550087fc62a8003fd3154021fe18aa000ffc8550087fc42a8003fd2154021fe10aa001bfd815000ffea0a8003fb5054003ff282a001df9415000ff8a0a80077c5054003fc282a001ffd015000ffc80a8007fc4054003ff182a001ff0c15000ffc40a8007fc2054003ff882a001ff8415000ff420a8007fc1054001ffb2a8000bfd9540007fccaa0002fe6550001feb2a8000bf59540007f8caa0002fc65500037fb228003ffd51400077ea8a000ffe5450007feaa28003ff1514001f78a8a0003ff63500017fb1a8000ff98d40007fac6a0003fc63500017e31a8000ffd4d40007fca6a0003fd5350001fe29a8003ffd0d4001f7e86a000ffe4350007fea1a8000ef50d4001ff886a0003ff62500017fb128000ff98940007fac4a0003fc62500017e3128000ffd4940007fca4a0003fd5250001fe2928003ffd094001f7e84a000ffe4250007fea128000ef5094001ff884a0003ff3250001ff1928000ff4c940007f864a0003ff61500017fb0a800fff98540015fcc2a0003fd615001ffe30a8002bf18540007fea2a003ffe5150001fea8a800fff1454001ffe82a000ffe4150007fea0a8003ff10540007fe62a003ffe3150001fe98a800fff0c540007fe42a003ffe2150001fe90a800fff0854000dfec0a0007ff5050003ff2828001ff5414000ff8a0a0007ff4050007fda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffc60a0007fc3050003ff1028001ff0814000ffe20a0007fe1050003fe082800dffd9730005fecb98003fe65cc0017f32e6000ff59730005facb98037fc65cc0017e32e600dffd9330005fec99803bfe64cc0077f3266000ff59330005fac998037fc64cc0077e3266000ffd5330077fca998003fd54cc01dfe2a66001bf98f30007fea798037fe53cc001fea9e600dff14f30077fe8798037fe43cc001fea1e600dff10f3006ffec598003fe62cc0017f3166000ff58b30005fac598037fc62cc001ffa966000ff94b30007faa598003fc52cc01dffa166000ff90b30007fa859803bfc42cc01bff9966000ff8cb30007fa6598037fc32cc01bffb0e600cff98730015fcc39800
  | 3 => 0xba8e4202ff94721017faa39080bfc51c8405fa28e4202ffd0721017fc839080bfd41c8405fe20e4202ffcc721017fc639080bfd31c8405fe18e4202ff88721017dc439080bf621c8405fe10e4202fb0872103ffec19085ffe60c84037f3064200ff58321005fac19081ffc60c84037e3064217ff943210bff8a190863ff40c842fff2064217ff103210bffc619085ffc30c842fff1064207ff08321017fe219080bf710c8405ff0864202ff04321007feca90802ff6548401ff32a4200bf99521007faca90802fd6548401fe32a4200bf19521007fec890802ff644842dff3224203bf99121007fac890802fd644842dfe3224203bf19121007fea89085bfe5448401feaa24216ff15121007fec690802ff6348401ff31a4200bf98d21007fac690802fd6348401fe31a4200bf18d21007fea690803fe5348401fea9a4200ff14d210b7fe8690803fe4348401fea1a4216ff10d21015fec490803ff5248401ff2924200ff54921007f8a49085bff4248401ff2124200ff509210b7f88490803ff3248401ff1924200ff4c921007f8649080aff6148405ffa8a4202ff94521017faa29080bfc5148405ffa0a4202ff90521017fa829080bfc4148405ff98a4202ff8c521017fa629080bfc3148405ff90a4200fdc8521017fc429080bee2148405fe10a4202fb08521017e84290803ff60484017fb024215ff9812100dfcc090803fd604842bfe3024201bf181210affca090857fc504842dffa024215ff901210aff88090857fe304842bfe1824215ff881210aff8409080bff1048405ff0824202ff0412100dfccba8053ff64d4027ff326a003bf99350007fac9a8002fd64d4029fe326a003bf193500a7fea9a804ffe54d4001feaa6a014ff153500a7fec7a8003fe63d40017f31ea000ff58f50005fac7a8053fc63d4029ffa9ea000dfd4f50007fca7a8003fd53d4001bea9ea014ff14f5009ffe87a8003fe43d4001fea1ea013ff10f500a7fec5a8003fe62d40017f316a000ff58b50005fac5a8053fc62d4029ffa96a000ff94b50007faa5a8053fc52d4027ffa16a000ff90b50007fa85a804ffc42d4001ff996a000ff8cb50007fa65a8003fc32d4029ffb0ea012ff98750015fcc3a8003fd61d40017eb0ea014ff18750015f8c3a8053ff51d4025ff28ea000ff547500a7f8a3a804fff41d4025ff20ea000ff50750097f883a8003ff31d4025ff18ea000ff4c750097f863a8003ff21d4025ff10ea000ff48750097f843a8006fd60d4003ff286a001df9435000ff4a1a8007fc50d4003be286a001ffd035000ffc81a8007fc40d4003ff186a001ff0c35000ff061a8007fe20d4003fe106a001ffc435000ffc21a8007fc10d40037fb2aa000ffd9150005fec8a8047fe64540077f322a000ff5915008ff8c8a800efc6454001ffaa2a011ff951
  | 4 => 0x8027e65cc401feb2e6200bf59731006facb988027d65cc41bfe32e6200bf1973106ffec998802ff64cc439ff3266203bf99331007fac998802fd64cc41bfe3266203bf19331007fea998873fe54cc401feaa6621cff15331015fcc798803ff53cc41bff29e6200ff54f3106ff8a798873ff43cc41bff21e6200ff50f3106ff88798837ff62cc401ff3166200bf98b31007fac598802fd62cc41bfe3166200ffd4b31007fca598803fd52cc401fe296621cffd0b31007fc8598803fd42cc439fe216620dffccb31007be6598803fe32cc401fe9966200f74cb3106ff8659880afd61cc405ffa8e6202ff94731017faa39880bfc51cc405ffa0e6202ff90731017fa839880bfc41cc405ff18e6202f78c731017ec639880bfc31cc405ee18e6202ff88731017f84398837ff60cc437ff3066201bf98331007fac198802fd60cc41bfe3066201bf183310dffca19886ffc50cc439ffa06621bff903310dff8819886ffe30cc41bfe186621bff883310dff8419880bff10cc405ff0866202ff04331007feca98802ff654c401ff32a6200bf99531007faca98802fd654c401fe32a6200bf19531007fec898802ff644c435ff3226203bf99131007fac898802fd644c435fe3226203bf19131007fea89886bfe544c401feaa2621aff15131015fec698803ff534c401ff29a6200ff54d31007f8a69886bff434c401ff21a6200ff50d310d7f88698803ff624c4017fb126200ff98931007fac498803fc624c4017e3126200ffd4931007fca498803fd524c401fe292621affd0931007fc8498803fd424c435fe2126200ffcc931007be6498803fe324c401fe9926200f74c931007f8649880aff614c405ffa8a6202ff94531017faa29880bfc514c405ffa0a6202ff90531017fa829880bfc414c405ff98a6200fdcc531017fc629880bde314c405fe18a6202f70c531017e8629880bfe214c405fe10a6200ffd8131005fec098867fe604c4037f3026200ff581310cff8c098806fc604c433ff2826219ff141310d7fe8098867fe404c433fe2026219ff8c1310cff86098867fe204c433fe1026202ffc4131017ee209880bfe104c405fe0826207ffd9721005fecb90803fe65c84017f32e4200ff59721005facb9081ffc65c84017e32e4207ffd9321005fec990863fe64c84077f3264200ff59321005fac99081ffc64c84077e3264200ffd53210c7fca990803fd54c8431fe2a64207ffd8f21005fec790803fe63c84017f31e4200ff58f21005fac79081ffc63c84017e31e4200ffd4f21007fca790803fd53c8401fe29e4218ffd0f21007fc8790803fd43c8431fe21e4202bf98b21007fea59081ffe52c8401fea964207ff14b210c7fe859081ffe42c8401fea164207ff10b21007fe659081ffe32c8401fe9964207ff0cb21015fac39080bff51c8401f
  | 5 => 0x8b510a7f8c5a8853ff52d4401bfa96a200ff94b51007faa5a88037d52d4429fe296a221ffd0b51007fc85a8803fd42d4443fe216a200ffccb51007fc65a8803fd32d4401fe196a202bf58751017fca3a880b7e51d4405fb28ea202dd94751017f8a3a880b7c51d4405ffa0ea202ff90751017f883a880bfe31d4405fe18ea202ff88751017f843a880bf421d4429ffb06a220ff9835100dfcc1a8803fd60d44017eb06a214ff1835100df8c1a8883fe50d4429fe286a221ffd0351107fc81a8883fc40d4441ff186a220ff0c351107fc41a8883fc20d4405ff886a202ff84351017f821a880aff6554401ffb22a200bfd91510fffcc8a880efe6454401feb22a21fff1915101df8c8a8803ff545443fff2a2a200ff551510fff8a8a8803ff63544017fb1aa200ff98d51007fac6a8803fc63544017e31aa200ffd4d51007fca6a8803fd5354401fe29aa21fffd0d51007fc86a8803fd435443ffe21aa200ffd8951005fec4a8803fe6254401feb12a200ff18951005f8c4a8803ff5254401bfa92a200ff94951007faa4a88037d5254401fe292a21fffd0951007fc84a8803fd425443ffe212a200ffcc951007fc64a8803fd3254401fe192a202bfd8551017fea2a8803f75154405ff28aa202df94551017f8a2a880b7c5154405fa28aa202ffd0551017fc82a880bfc4154405ff18aa202ff0c551017fc42a880bfc2154401ffb02a200bfd81510f7fcc0a8806fe6054401feb02a21eff1815100df8c0a887bfe505443dfe282a21fffd01510f7fc80a887bfc405443dff182a21eff0c1510f7fc40a887bfc2054405ff882a202fdc4151017fc20a880bfc1054401ffb2a8200bfd9541007fccaa0802fe6550401feb2a8200bf59541007f8caa0802fc65504057fb228203ffd51410077ea8a080ffe5450407feaa28203ff1514101f78a8a0803ff63504017fb1a8200ff98d41007fac6a0803fc63504017e31a8200ffd4d41007fca6a0803fd5350401fe29a8203ffd0d4101f7e86a080ffe4350407fea1a8200ef50d4101ff886a0803ff62504017fb128200ff98941007fac4a0803fc62504017e3128200ffd4941007fca4a0803fd5250401fe2928203ffd094101f7e84a080ffe4250407fea128200ef5094101ff884a0803ff3250401ff1928200ff4c941007f864a080aff6150405ffa8a8202ff94541017faa2a080bfc5150405ffa0a8203fdd0541017fc82a080bbe4150405fe20a8202ef10541017e882a080bfe3150405fe18a8202ff88541017f842a0803ff60504017fb02821dff9814100dfcc0a0803fd605043bfe3028201bf181410effca0a0877fc5050407ffa028203ff9014101ff880a0877fe305043bfe182821dff881410eff840a080bff1050405ff0828202ff0414106ffecb98802ff65cc401ff32e6200bf99731006fccb98
  | 6 => 0x1feb0c6400bf5863203ff8c31900afc618c853ff28c6429ff14632157fe83190a7fe418c853fe20c6429ff8c63214ff863190a7fe218c80ffe10c6407ffd8232147fcc119006fe608c801feb046400bf5823203ff8c119006fc608c851ff2846428ff14232157fe81190a3fe408c851fe2046428ff8c232147f861190a3fe208c80ffe1046429ffc4232147fc21190a3fc108c801ffb2a6400bfd9532007fcca99002fe654c801feb2a6400bf59532007f8ca99002fc654c801ffb226400bfd913213ffcc89900efe644c801feb226400bf5913213ff8c89900efc644c801ffaa26427ff95132007faa89909ffc544c801ffa9a6400ff94d32007faa699003fc534c84fffa1a6400ff90d32007fa869909ffc434c801ffa926400ff94932007faa499003fc524c84fffa126400ff90932007fa849909ffc424c801ff9926400fbcc932007fc6499003de324c801ffb0a6400bfd8532137fcc29900afe614c801feb0a6426ff18532015f8c29909bfe514c84dfe28a6427ffd0532137fc829909bfc414c84dff18a6426ff0c532137fc429909bfc214c801ffb026400bfd813212ffcc099006fe604c801feb026425ff1813200df8c099097fe504c84bfe2826427ffd013212ffc8099097fc404c84bff1826425ff0c13212ffc4099097fc204c84dff8826425ff8413212ff8209901fff650c8017fb286400ff99432005fcca190037e650c8013f3286400ff59432005faca190037d650c8013eb286407ff19432005f8ca1901fff640c8017fb206424ff9903201dfcc819003fd640c8017eb206407ff1903201df8c819003ff540c849ff2a06400ff55032127f8a819002fe630c801ffa98640dff94c32007faa619037fc530c849ffa18640dff90c32007fa8619037fc430c8017f3106400ffd483203ffca419003fd520c80ffe2906424ffd083203ffc8419003fd420c80ffe210640dffcc832007be641901ffe320c801f71906400ff4c832007ba6419003ed320c80fffb086423ff98432015fcc219003fd610c8017eb086407ff18432015f8c21908ffe510c847fe2886424ffd043211ffc821908ffc410c847ff188640dff0c43211ffc421901ffc210c80fffb006422ff9803200dfcc019003fd600c8017eb006407ff1803200df8c01908bfe500c845fe2806424ffd0032117fc801908bfc400c845ff180640dff0c032117fc401901ffc200c847ff8806422ff84032117f8201900afe65d4429ffb26a221ff9935101dfcc9a8803fd64d44017eb26a214ff1935101df8c9a8853ff54d4443ff2a6a200ff553510a7f8a9a8853ff63d4401ff31ea200bf98f51007fac7a8802fd63d4429fe31ea214ffd4f51007fca7a8803fd53d4429fe29ea221ffd0f51007fc87a8803fd43d4443fe21ea214ffd8b51007fcc5a8802fe62d4401feb16a200bf5
  | 7 => 0x2101ffc219080fffb048430ff9824200dfcc121003fd60908017eb048407ff1824200df8c1210c3fe5090861fe2848403ffd024201ffc812100ffc4090861ff1848430ff0c242187fc412101ffc2090863ff8848430ff84242187f82121003ff65508017fb2a8400ff99542005fccaa1003fd65508017eb2a8400ff19542005f8caa100eff6450807ffaa28403ff9514201ffaa8a100ffc5450801ffb1a8400bfd8d42007fcc6a1003fd6350801fe31a8400bf18d42007fea6a1003fe5350801fea9a8400ff14d4201ffe86a100ffe4350801df21a8403ff50d4201ff886a100fbc43508077fb128400ffd4942007fca4a1003fd5250801fe2928403ffd094201fde84a100ffe4250801df2128403ff1094201f7884a100fec4250801ffb0a8400bfd854217ffcc2a100afe6150801feb0a842fff18542015f8c2a10bffe515085ffe28a8403ffd054201f7e82a100ffe4150807fe20a842fff8c54217ff862a10bffe215085ffe10a8400ffd8142005fec0a10bbfe60508037f3028400ff58142177f8c0a1006fc605085dff282842eff1414201ffe80a100fbf4050807ff2028403ff10142177fc60a10bbfc305085dff102842eff0814217ffe20a10bbfe105085dfe082840dffd9732005fecb99003fe65cc8017f32e6400ff59732005facb99037fc65cc8017e32e640dffd9332005fec9990b7fe64cc8077f3266400ef9933201d7cc999003fd64cc8017eb266400ef593320057ac999037fc64cc8077e3266400ffd533216ffca999003fd54cc85bfe2a66400ffd4f3206ffca799003fd53cc81bfe29e642dffd0f3206ffc8799003fd43cc81bfe21e6400ffd4b32007fca599003fd52cc801fe296642dffd0b32007fc8599003fd42cc85bfe216640dffd8732167fcc39900afe61cc801feb0e6400bf5873206ff8c39900afc61cc859ff28e642cff1473216ffe83990b3fe41cc859fe20e642cff8c73206ff863990b3fe21cc859fe10e640dffd833215ffcc199006fe60cc801feb066400bf5833206ff8c199006fc60cc857ff286642bff1433216ffe81990affe40cc857fe206642bff8c33206ff861990affe20cc857fe106642cffc433215ffc21990affc10cc80fffb2c6400bfd9632007fccb19002fe658c801feb2c6400bf5963203ff8cb19002fc658c80fffb246400bfd9232157fcc91900efe648c801df3246403af99232007fac919002fd648c801deb246400af5923203ff8c91900efc648c801ffaa4642aff95232007faa9190abfc548c8017eb1c6400ffd4e32007fca719003fd538c801fe29c642affd0e32007fc8719003fd438c855fe21c6400bf98a32007fea51901ffe528c801fea946407ff14a32157fe851901ffe428c801fea146407ff10a32007fe6519003df328c801f79946407ffd863214ffcc31900afe618c80
  | 8 => 0xf98252007fac129002fd609480ffe304a401bf182521c7fca1290e3fc5094875ffa04a438ff902521c7f881290e3fe3094871fe184a438ff8825203ff841290e7ff1094871ff084a438ff04252007fec8a9002ff6454801dfb22a400afd91521bffcc8a900efe6454801feb22a437ff1915201df8c8a9003bc64548075e322a400ffd51521bffca8a9003fd545486ffe2a2a400ffd8d52005fec6a9003fe6354801feb1aa400ff18d52005f8c6a9003ff5354801bfa9aa400ff94d52007faa6a90037d5354801fe29aa437ffd0d52007fc86a9003fd435486ffe21aa400ffd4952007dea4a9003fe5254801bf292a437ffd09521bff884a9003ff61548017fb0aa400fdd8552005eec2a90dbfe61548057f30aa400ff585521b7f8c2a900afc6154801fa30aa402bd185521b7fca2a90dbfc515486fffa0aa436ff905521b7f882a90dbfe315486dfe18aa436ff885521b7f842a9003ff60548017fb02a435ff9815200dfcc0a9003fd605486bfe302a401bf181521affca0a90d77e505486bfe282a435df141521bffe80a90d7fe405486bfe202a435ff8c1521aff860a90d7fe205486bfe102a436ffc41521affc20a90d7fc10548017f328a407ffd90521a7fcc82900efe6414801feb20a400bf5905203ff8c82900efc6414829ffaa0a434ff95052007faa829053fc541480fffb18a400ff98c52005fcc629003fd63148017eb18a407ff18c520a7fea629003fe5314801fea98a414ff14c521a7fe8629003fe4314801fea18a434ff10c52005fcc429053ff5214801bfa90a407ff94852007dca429003fd5214801bea90a400fb548521a7fe842901ffc421480fffb08a433ff98452015fcc229003fd61148017eb08a407ff18452015f8c2290cffe5114829fe288a434ffd045219ffc82290cffc4114867ff188a433ff0c45219ffc422901ffc211480fffb00a432ff9805200dfcc029003fd60148017eb00a407ff1805200df8c0290cbfe5014829fe280a434ffd0052197fc80290cbfc4014865ff180a432ff0c052197fc402901ffc2014867ff880a432ff84052197f8202901fff65908017fb2c8400ff99642005fccb21003fd65908017eb2c8407ff19642005f8cb2100efd6490807ffaa48400efd524201ffca92100ffd5490807fe2a48403ef1524203ffec721003fe63908017f31c8400ff58e42005fac72101ffc6390801ffa9c8400ff94e42007faa721003fc5390807ffa1c8403efd0e4201ffc872100ffd4390801dea1c8403ff10e4201dfcc521003ff529080fff2948400ff54a4203ff8a52100fff4290807dfa148403fbd0a4203ff8852100fec429080fffb0c8431ff98642015fcc321003fd61908017eb0c8407ff18642015f8c3210c7fe5190863fe28c8403ffd064201ffc832100ffc4190863ff18c8431ff0c64218ffc43
  | 9 => 0xc83ff30c8602bf98643007fac321802fd6190c1bfe30c8602bf1864320ffca321907fc5190c07ffa0c8603ff9064301ff88321907fe3190c1bfe18c8641ff8864320ff84321837ff6090c81ff3048601bf98243007fac121802fd6090c1bfe3048601bf18243207fca121903fc5090c07ffa048603ff9024301ff88121903fe3090c1bfe1848640ff88243207f84121907ff1090c81ff0848640ff04243007fecaa1802ff6550c01ff32a8600bf99543007facaa1802fd6550c01fe32a8600bf1954301dfec8a180fff5450c07ff2a28603ff5514301ff8a8a180eff6350c01ffa9a8600ff94d43007faa6a1803fc5350c07ffa1a8603f7d0d4301ffc86a1803be4350c07fe21a8603ef10d4301fb886a1803ff6250c017fb128600ff98943007fac4a1803fc6250c017e3128603ffd094301ff884a180fbc4250c01ffb0a8600bfd85431fffcc2a180afe6150c01feb0a863fff18543015f8c2a18fffe5150c7ffe28a8603ffd054301f7e82a180ffe4150c07fe20a863fff8c5431fff862a18fffe2150c7ffe10a8600ffd8143005fec0a18fbfe6050c037f3028600ff581431f7f8c0a1806fc6050c7dff282863eff1414301ffe80a180fbf4050c07ff2028603ff101431f7fc60a18fbfc3050c7dff102863eff081431fffe20a18fbfe1050c7dfe0828614ffd93521effcc9a900efe64d4801feb26a400bf593520a7f8c9a900efc64d4829ffaa6a43dff95352007faa9a9053fc54d4829ffb1ea400ff98f52005fcc7a9003fd63d48017eb1ea414ff18f520a7fea7a90037f53d4801ff29ea400ff54f52006faa7a9053fc53d487bffa1ea400ff90f52007fa87a90f7fc43d487bffa16a43dff10b520a7fec3a90f3fe61d48057f30ea400ff58752005fac3a9053fc61d48057e30ea43cff947520a7f8a3a90f7ff41d4879ff20ea43cff107521e7fc63a90f3fc31d4879ff10ea43cff087520a7fec1a90effe60d48037f306a400ff58352005fac1a9053fc60d48037e306a43bff943521defca1a9053fc50d4877be286a43dffd03521dffc81a90effc40d4877ff186a43bff0c3521dffc41a90effc20d4879ff886a43bff843521dff821a9002fd659480fffb24a43aff9925201dfcc929003fd64948017eb24a407ff1925201df8c929003ff5494875ff2a4a400ff552521d7f8a92901fff6394801ff31ca400bf98e52007fac729002fd639480ffe31ca400ffd4e52007fca729003fd5394801fe29ca43affd0e52007fc8729003fd4394875fe21ca400bf98a52007fea5290037f5294801f7a94a43affd0a5203ff8852901fff6194873ff30ca402bf98652007fac329002fd619480ffe30ca402bf186521cffca3290e7fc5194875ffa0ca439ff906521cff883290e7fe3194873fe18ca439ff8865203ff8432901fff6094871ff304a401b
  | 10 => 0xa92992bfc5494c017f31ca600ffd4e53006fea729803df5394c01afa9ca64affd0e5306ff88729837ff6294c01ff314a600bf98a53007fac529802fd6294c1bfe314a64affd0a53257f88529837ff6194c93ff30ca602bf98653007fac329802fd6194c1bfe30ca602bf1865324ffca329927fc5194c95ffa0ca649ff9065324ff88329927fe3194c1bfe18ca649ff8865324ff84329837ff6094c91ff304a601bf98253007fac129802fd6094c1bfe304a601bf18253247fca129923fc5094c95ffa04a648ff90253247f88129923fe3094c1bfe184a648ff88253247f84129927ff1094c91ff084a648ff04253007fec8a9802ff6454c01dfb22a600afd915323ffcc8a980efe6454c01feb22a647ff1915301df8c8a9803bc6454c075e322a600ffd515323ffca8a9803fd5454c8ffe2a2a600ffd4d53007bea6a9803fe5354c01bf29aa647ffd0d5323ff886a9803ff6254c017fb12a600ff98953007fac4a9803fc6254c017e312a647ffd095323ff884a9803ff6154c017fb0aa646ff98553015fcc2a9803fd6154c8dfe30aa602bf18553237fca2a991b7e5154c8dfe28aa646df1455323ffe82a991bfe4154c8dfe20aa646ff8c553237f862a991bfe2154c8dfe10aa600ffd8153005fec0a9803fb6054c017db02a645ff9815300dfcc0a9803fd6054c8bfe302a601bf18153007f0c0a9806f86054c8bff282a645ff1415323ffe80a9917fe4054c8bfe202a645ff8c15322ff860a9917fe2054c8bfe102a646ffc415322ffc20a9917fc1054c017f328a60dffd9053227fcc82980efe6414c01feb20a600bf5905306ff8c82980efc6414c29ffaa0a644ff95053007faa829853fc5414c017f318a614ffd4c53006fea629837fe5314c01ef298a600ff54c53006faa629803dd5314c89ffa18a60dff10c5306ffec429803fe6214c017f310a600ff58853005fac429837fc6214c89ffa10a644ff1085306ffec22990ffe6114c057f308a600ff58453005fac229837fc6114c057e308a643ff944530a7f8a229913ff4114c87ff208a643ff1045321ffc6229837fc3114c87ff108a643ff0845306ffec02990bfe6014c037f300a600ff58053005fac029837fc6014c037e300a642ff940530a7f8a029913ff4014c85ff200a642ff10053217fc6029837fc3014c85ff100a642ff0805321ffe202990bfe1014c85fe080a60dffd9643005fecb21803fe6590c017f32c8600ff59643005facb21837fc6590c017e32c8603bf5924301ffea921803bf5490c07ff2a48603ff5524301ff8a92180fbc5490c077f31c8600ffd4e4306ffca721803fd5390c1bfe29c8603ffd0e4301f7e872180fdf4390c1bfe21c8603f710e4306ffec521803fe6290c017f3148600ff58a43005fac521837fc6290c07ffa148603efd0a4301ff88521837ff6190
  | 11 => 0x600000280200000200680200000400300300380000100200580080380280d80000000000200080000080000580100000000400100280180000000000180080180000600780000980080300180100280000080100780080200580080080080000180b80400b80f00000100000080080300100280200000600101280080000180180180180100100000efe65d50077eb26a803ff9535401efca9aa00fbe54d50079f2a6a803ff1535401ef8a9aa053ff63d5001ff31ea800bf98f54007fac7aa002fd63d5029fe31ea803ffd0f5401ff887aa00fbc43d5029ffb16a800ff98b54005fcc5aa003fd62d50017eb16a814ff18b5401ffe85aa00ffc42d5007de216a814ffd875428ffcc3aa00afe61d5001feb0ea800bf587540a7f8c3aa00afc61d50a3ff28ea814ff1475401ffe83aa00fbf41d5007ff20ea803ff1075428ffc63aa147fc31d50a3ff10ea851ff087540a7fec1aa143fe60d50037f306a800ff58354005fac1aa053fc60d50037e306a850ff943540a7f8a1aa00fff40d5007dfa06a803ff9035401ff881aa143fe30d50a1fe186a850ff88354287f841aa147ff10d50a1ff086a850ff0435401dfecaaa00eff6455007ffaa2a800efd515401ffca8aa00f7e5455007fe2a2a803df1515401f78a8aa003ff63550017fb1aa800ff98d54007fac6aa003fc63550017e31aa803ffd0d5401ff886aa003ff62550017fb12a800ff98954007fac4aa003fc62550017e312a803ffd095401ff884aa003ff61550017fb0aa84fff98554015fcc2aa003fd615509ffe30aa802bf1855427ffca2aa13ffc5155007ffa0aa803ff9055401ff882aa13ffe315509ffe18aa84fff8855427ff842aa003ff60550017fb02a84eff9815400dfcc0aa003fd605509dfe302a801bf18154277fca0aa13bfc5055007ffa02a803ff9015401ff880aa13bfe305509dfe182a84eff88154277f840aa13fff105509dff082a84eff041540a7fec9a9937fe64d4c077f326a600ff59353005fac9a9853fc64d4c077e326a614ffd535326ffca9a9803fd54d4c29fe2a6a64dffd0f5326ff887a9853ff62d4c01ff316a600bf98b53007fac5a9802fd62d4c29fe316a64dffd0b5326ff885a9853ff61d4c99ff30ea602bf98753007fac3a9802fd61d4c29fe30ea602bf18753267fca3a99337e51d4c29fe28ea64cdf1475326ffe83a9933fe41d4c99fe20ea64cff8c753267f863a9933fe21d4c99fe10ea614ffd835325ffcc1a9806fe60d4c01feb06a600bf583530a7f8c1a9806fc60d4c97ff286a614ff1435326ffe81a992ffe40d4c97fe206a64bff8c35325ff861a992ffe20d4c97fe106a64cffc435325ffc21a992ffc10d4c017eb2ca60dffd9253257fcc92980efe6494c01feb24a600bf5925306ff8c92980efc6494c01ffaa4a64aff95253007fa
  | 12 => 0x100000080300000200000080a00380100200280480380880080880100000000280080000800000000080200000080100180200000000000080000080100200100000180000280980180180280080080000100d00080200000100080080000080380280080000300380480580080100000000180000280000000080080080800580080300080000180000080200080180e80300080000000300380280080201100b80380000000400100000180080600100180100e80000000000180100180080100380000000100000880300180300000480080000580100200180480080080080000100400280100100300580180380d80000100000c80100080500180000000000280280180700280280000080400180800b00180000c00000000380080600180200100400180000600980000080000000380080000180000380100100000180100380500e00000b00100080080400001180000400000300200780880200000300000380180000b00200180080080000900b80000080280000000180180080100380080700080100200080100900000000000000100b00180580080880180000200200000080080080000080000000a80300080200080000280280280180080300380180180300480500180100300200000980000080000400000000180400000200300580180080300080200200300780100200080000080300000700600000a80500100201a80500280980280000180000000100100100900180180100180100000000000180a80000000c80080080280300080180000000480000000180180000000200000100000080380200000000080200100180000100000000000280100000180480180000000080200280180080300000000000100280000200080000080180180000800100180080080580000100000000080100580100b80800000600000480000000600e00180300180400000000400000380000180080000100580080100280180000380080b00080b00100000000080080c00080000501680080080280680080180101080000000000280080100000780000100200080200000080000080400600100200680500400600e80380300680100180080180000000600400000280000280280080080400200300000000200100380080680280000100000000300200480a80100080000100580200400600300400200000000180080080100000000680000480080300180080000400480100200480280400180a80280000680200080380080300000000200100100100000200180900200000080200580500000101280000100480080000100080200400080000000180200f80100000580000280300280080280980000280000000c00400080080280400080780a804000800800804000000000801802000800000800001801800001000
  | 13 => 0x9fc398215052c7a34948000aaa5620001d0800000000e914c00059c00003200002de268037c000000147a40800000016d80000000000000d208ae00011e9f7800000049280011460d6094800059258300000000000004ee8d0c4fa0000000c7000050a418800000000009723dc000000453a2bc0000000000000cd08fe2b4000000000000010fc00000002980010843e20c4199d1f8526190a718d165a92db00007260000000b10b600000000000f3a7ff305130896a21c4dd8dd0f788eb00000003fa3170001960bf06962cea2154428364ae80006be8870c4974d2c69043bb25586f446200184880b28650da9e650fe000273087412e9194de19540000000280db80006770001a7cc5200043a1d9c1b005d000128c00067900024890681c005205700000002de12348400000000000f384a43f8800079803e00000010766060d813200000000001e280004720000000d2e1bd04911cd02600021300000004512a10e64fd80003e71bc8cec96900000000003d200000013d8000209000101c000000106c000000000000000000000000000000000f380000003c70bf185800063000000000000002c01d7d3a200000000000006b900000003be57f14418c8000000000141c9040002069720000a2400000000008f0173869823e000329243061a80017f1f803fe63a29d15a400095f4e4000000000000007383ee7bd000000000044600004ec0002c100000000000000000520b421f804400011ac84835a0cb52100004de8d5d2982cc121159916a72e1b293703c47683c61744a382321569a49430a3a0b39ad49bc92314e17412d87da296a2c54141a73499e78fd62ea15e066c1ca7a9044937cc287d84e7a53863282937c0e180fc29b00016f40008b3399149086a8b03d1132c0007e743d00011681060cd078c2c01d128d158009664020980000000002030dc09ee0b000028788fe0004c58ec00003bd00025a8b748830360000d128560001b74000a271cf22c8a064c621c16ccbf45632f78ef0608a1f37520b105e9674491d051dc6ae382a58836472f11b8f90be25724f3217c4340940940a48c68653388000000045900000008b664e00000000000002538d30faa000383000019400000010743e2000246000000044a00026c49824a83481f2826274800000000003c92a280000000000000000e2200000020e00008f20000bd0ab699f341a6d4a2c3290070000038000048000000010038000028098000000000000020010078018010000048010028000018038010000000000050010028070000020028010000018000008040028008018018000020000020000000000018000040000010010018060098000000000000020000000068020000000000000010000000068008010000000000000010038000008018010018000000008000008
  | 14 => 0x5c4830f9d2348e851a2008e140be21b8f1123697e0091e80f7e9ce418074cd361ca1f180253b60b245e8b208680000f080000000000001838ae0068102063800043a01628c40004bc00003e40008780002200e0881f3d8a57000025b1c200a4b5e89a0be0000a7c0000a69a147cc00039b966c0007ad01300000000270001c200000003878104000000000000000000041c9ebd2563bb000239518070908000ec6965f6075000000000034e09e054058413700000009e10000000c7a64a000000000059200000006780005180b8000000000020308f462234e8000c5668f00000000004602198ac066684900000005b8a374448000000a261ce84c800000012600005009da064925817452814a1e345202350001af133038c4760000650395224000049c000000000000091709c0000e4a0002948568ba8a3c3c78b7d3b201c284000037000010f9a8ceea0000000e983b22391f9139d38034505f8880f580cc32c83540c26a42cc00bc0001d71c0a4d80000f74af000016c8ca000233116e000000000072427101c910134c1434a58380e7e1fa000053cc261c711084707d815d27f82ad26473802890f8e92a1227e9ab0e280000000fa87ea000097800106678400000008fc00047517c885c7b238a8000c247f000003b00008a40000e38000000121800000800038691352380000c500008b83da0000000ed2000000151c00e0000f680000009e21838000e9e00000000000000000001c009e092151c800000060c00000012200000000000000000283048c0007c44c51ed4a9c0633142114f6e8084ef80000000000000000d5a40e11c1f0c7ec6b843980005c243100000010a032e25107d4514a3d0000bb147e1184b90d043d660429a0960df800000007d8b646b70000000000000172800050c56a000000000000023406f14500000001ccc00046e0001f5c00088e00000000006a50cca49c45098750b8b4c5e05764db85a40000000001d1c00009c4308e1d17c2894d99910abe54b00ca7a12e28a00001944cea4c001122fcd0c47b3509cb11ea81b07c05a828a00045504210945f347a28d4f260c50e91b980000b100000012dc84c000000067400044e27700005be2b619a80000d006e263ce3c18d48c11741c44cd084a79ca3c00021ca5ac53a9f019a192c0000004c8a10409a0694480f9400032b2e3a30d03c46600004d8f2e4d30249dac5b000042e00008f8723012995c00000020800000000003b691dc8d40003839a6142800000017180000000000000c460000001c850060d30000000000000112800000004c0b09fb80008283e00000000000000000092e89400021e53580000000000fcc27200016fcd3c000000000000006f00015013942140001510284000000000000072a00000000000000000bd800028b00000000
  | 15 => 0x8de0000001ea05c673e1ad9b14c2e1a835b0000aa40fd2418228c662000f9a83c71a000242000034200030c0c602c8a3840e0c30b9466d18a80004580002fb83d87306e531d82100004d524280002a82d728c840d3608cd1da08b43741aa3348c4c8c28530460a609dc9fe408a5cc3b867c0088dbc39800820516906d43fb31b1f18d667791b200001845a61928968ade99e10819f81e207f0dd92c943a36c257a6c8f9866c13197b8070181105a2b4e3a4aa0d8910ce306e122c25451de093367a7605b456e43307a918a3ef45e06b846c5b500000000160000480df92001ac12310700006c84a98000ff200000002384e83c846a9c653ae00000000005ac0000000000e1c0001a021ecbc20000c3071047499615a237d2820a8000164419e8c11e28000000000000105cdde5fb2fa80000d60001282500da0282000000000009a3b91474a1e5ed215816c000000157117c49688f1eba134a5c7fd4eb13f135e63535e9618f3e00049f9ee8000323296152029651b000000056c2ef09f9cd8d7c6c913a96080502c339480010c800012209a93d41a5000270c0002f9415127119c846509965d08e65f11220486f8a2909f26e81ba175074021c5345854ce8a34952751111a7053d277c2eb0000ac22bd01a9148ce2a2a00000011560003e68beca2e79533826a03f220c15d000095a000000043c384000000016057045624d000014c00000005589d27a541b800000000e0639cf0ba400000000011b66664c901b8000351000139507a00016810a51e200047d03cc7c26381040d5000000003028140003a02a6062cf220001ea919426676e4c325ec3260002eaa81c7f207347c80d800097000000000000000ca93a050607737d800006000000000000000000000000000000000000000000000000008029bf00025f11e649e0000000bfc04f4460000fda0002018ea800000000021113c6000000000000074028a144875a0fc0b8897844e77d3d5a2d8c4e9a40001b606841f440480006200000000000db425700021a104200000000009fc00000000000000000001be4fb88c82c59e08000000000047461c9792ca16240004a127d85b440400016716044c00d94020000e9c16c0000a640304500001bd0e980002450110f8200019800000005b12bf15040aa5f90000ba40002260d10cb000010c35492fc0000850ab80011a69933f49a9945c8d7133842ce7a0002a4a66854a2a32808d9cff656b2f194c89c23b748b1030f705a013228c8cd63893b79854e745da0a9918c1e877a1ce019465e262480a88c9e602024000000005711c2976526a00000000014660000ea222127a00027600009027d90599cd04f49822e784652940171f887bc1e050b470883c0001d0000000126200028a82bc9b69800001bdc7101850e6808c87652a00000000000000
  | 16 => 0x14f8d64cfe6004db2254000000000000059e17035415347143fd4e4800141885132e15510305c33c5a610b72000440800002619e4e5a10c0007d300025101044c50000f7d00a4ed3b1186c16800001a10d92726af4da07540008e94cb98682fa65044314dc4224a64b3102021a6b02ba000124c39f3af00009106c741690f000017b1d91344c1a1a02439e50eae5111910000b687c800005ac48e0003040000ee63e8000144023c57336fa1a4de65a842b96202e46483fa9d6400000017e1d2800022e08aa160bc0476000000096868a1381c2c0008990240000c0a37b34600000000004aa9d0c8e00002388000000000000000000010a05c000000098e00019d014a5ec00015b4000355000000058e29700000003820000001348aea00a00000000003b6000000141076a27117610ba33e00019580004eb000251800092f0cb00000002ab1590000d8c24500001e48500000002520000000171000000000000000000005c50000f5000000018a000132aa2d17980000000001f8109c80839747fa8f80002590000000cc675d00000000008101d700007fe9f31e9a5854800000001f2d0027714901b5538aa220000c7d2667be301076c6d698107d1b6c3040c113c800000000000000000000004540e6c00000000011b000000045ca86d0468d43f11564cf634f4fa000000005a22106b40002fd32da2a434808f000000000028516302f46f01261f7205800067d496000121622949d1d490b241943b05d8dac58e28fa234d7400008b0000d802cd2cb2434e2e56737200000001be0000f0cfa20001ab0280b5a320000000023400000000350aa6bb00d8a986366d30881060cc25e55049ba0f4c000376800084636229191d0bf85f046d13bc784a160cc0f3cd000ce0000cc80f819225ca6a80000000001afd10800020280006f265d4bc00e8bba20e22d00048f24320390dcc0003a8069256832e00000015ec0002ee03a8f789f463f00013d8da864110c86fce407581d7980c7160a22998310a1a8960da28bd0965df12996ec74854a04b1bd8db820951b26143cc28c05c931d3f600025f18400000004981094c161d60000ae460c0b5236a7b937c88b1e8a7f474441f32f14c0fe64553c48d292d03ba00009540000001e58000a188522f10001126424124173087a0000db8e40fbe0004f680009ae3d052100005940cb0c623447d259300000000000000001ea87e8000000000121200047c00000000a340ba299372000000000000070c1d29f14d880000000000fa400002315e455093b04d80010280000001fe800000000021f000000047b12388980001810e440009990002844d9451349e24b4a7e50500a9f3c4ee0002cf80005963440000b0000062c1888d1c39e0000270b9813e00005e1b0c00077725d94d907e24f3170cfcc621592a80000
  | 17 => 0xb181ee1ec911c766000000000101a0000001d705fe0000c880001de0710001e4000016800007c00000000001b30c386e037fa47400000007680000009cd000000055e3054c485780000000001c7d1ba000139800080005700000006b034d2ad13c820e0000001a8069c1e437a8ea40000003fa00000000000ec000000024d4138334000a0b000000033888a50aa0c85a25db36b98e47ba06d1b089b01a27ef27a27dd056897040017caf406a16924dc6a47b33230dd404286e3f4052525001e0b78ba08d298303b1894df459a156030ccc066e0001e6080e3a72900ee50de00025d1e5851c45400021f8fd400000017fd3523b10f29a381cc4e400007f000090e00016b91fa0000b3000000000046599344c200000014e40007463c30e8cdbc00000004b07560002e20a8934a0004b000013de53542722740e0609000000000044b2e584140000000000000dd2783389a56c00090326b00011f63a1000122ce480003b184dc00047800000012866d100008c400068109c8e3c0006c229c085400c8de0198000e960000000000e4c0000000d7800022b000010c0007d400000008fa2d938900001a83bf000000067a22f0002490554000000077800000000004d01ae642000000000000000005cd20a7c700008c000012a4d0155c13c0bb00a00000000003ad000000022a3690000000024000015000091e00000013a40002c380000000004d10ddce88000000000000000000000000000005002804b820001fd179089e0001cb000114a00000000000000003c009ecce600017b800000050e487a09024800000000005ea0000601f8c3b40004d6a03c6061b9000051c39631e1a3000000000012a09f00005ab4f0000000065400001780000005010d70a6232400012dcb2a000000052913c0e4000175c0004410001fdc00060f07380000008824ac23b49d40675160fb40000002529a500005432bc000003494930097d061485a2ef226d320a1040c8f3927c17812507a4a787163aa068cd9a37d46905d08bc8e721102188d67a442f154ceb600011d95dc81600030f1db13182492959d40c8600005392400001c308908f09ba6ce29e800000003c07d90a80000004bb80000006a22488438dc43b545088d0f681772f5a68c13200f26517a40000003a99e8407a000464800002c6073db17240004d4129000088a58d09380004440001eb0000e385a700000000006b119b8000cb47810000bb4222475000003022e0004a2a7c800066f35900000000000000000966000448800128e6a72b2957913025c180046c0000004620000000000000000000400000027c400016e4aa00013d68d0000000000000000022880005e719c80006c6331000000000049b0000000000000000000054e00048f8000bb800049709b4c2200027a8ac4d047031fc0001014914
  | 18 => 0x400019909e281a0000000366095310859430878800000006da42f00000007b80000001694a441f200020f87b6495323a870c3a07a332a3600000002589678e044cf00000000001af0f600c883c84009d0000000a41488923c1220003809c9c81e104109254879400029d8cec0006f100000000009c224498807ee63e20d00dd38849310c0368000000000000000000043500000005b84dc25fc41a9d3185800078c30f00012509c602b262219c000056000136813a000000000000052f00008cc00033500005fc0009650001bb8d960002fe9d80542000000000000097d0001c6c18c90716a897515c00000009440007a700001986d00000a88b50000000000000024071a000000057e0004631ce54320a100011100000000000000c8a57c26480003527921439cc40000000002080b3208b000000000000000008580007d63bc03b8fb600000000000008d914205880006aa34a95f40008dc0afa33cab000018e905118464f1848be857600000024a800000000000004d00001df26ac00000028490446920000001ff01fe13d2d123990e42913940a545027b94361f74ffc6844172074dd66263bf0bc4d1049f1a997353f40004368c484026ab3dd8dd800013000f9890a9e13c0080ff0f0e4d8002836d40c0002501738a8c7c90b1a74066c9f902505611c472243596b03280420db07ed47607424c25d0130619022a1c40004d925c1fd80000000001dd000000028c080c2f494200008fc2022eb2010000eac99b24309011583694ac9084c7884f31689041ea87000006ac7582b550d15587280000000f346709f80ce8bc805a5a3040a634c5462f00025d4000114000000000000000012b811a6d91051d90a4e7451b00000000000000000000012d000000118e27f1039930000000000105800095000009f800096d0c7800040a9ae48a93812ec00000000000000000001a440003c11dc1dec0000000000f809f000000009a400010210f2180dd88070311b0482a6370002670ab86722d50dc40003c000000000005e81930b1496c00014982dd04c26500017a80009cc4e3a7952ae7354ca0e683067e541126845482c2029162800069909a8000fc200000005310ee0001bf8000000590324800000089f1938c0425600025812ad3c8000471933815c1463bfa1d4ee00000188ff8000000172000104a72d02013e4f5c52542d87a00000e9000187c07e1fe5158780fc88e03d805393fe79a00027d80002b75128e0141a1c51ad1a6815218017c19889240e32f3000000012543ea839078761032000134e9f5000050405c00003e871940621b280067c1d67854ef1a34dc642c055020c000000281055400029e090a0e92f473b12f89bc2a43d8000000005407b2ae9bf40005c2373837885a350204919c6cc3eb37f24489989383c70540000000079281
  | 19 => 0x4ac22480012686f00238ca828800024c861c00000015980000002a907f1a1ce560001840000cf096f2dba01800000000000002f24c311f12f44d6755000202d22667a1f9a2e8000000290963c5ba0e13e11d9463400000000000008bb2a880008c89641c189d800000003c0000000113103000032038245c0d7400025641a87750c40003b30000000000056a75462c7f2000099839298848510c03905042e0218c57c0000ad8000e9a37247202b0ff094d2271e6d02a00024ea53c28021310b80000000004ea2880fa056
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd760c91003cfc760c9100057e750c9100057d750c9100067f650c9100067c650c910006df630c91006edc630c910006ef620c91003eec620c910015f6710c910005f5710c91000dfa700c910005f9700c91000df476545100f6f4765451000cf47654510015f775545100177775545100077765545100a6f665545100a6f46554510007746554510005f77354510005f47254510007775254510007755254510007f3705451000df6705451000df470545100f7f07054510016f76054510017f360545100f7f250545100f7f030545100f7f2205451000df4764c5100cef4764c51000cf4764c510005f7754c510005f5754c51000777654c51000774654c510015f7734c510017d7734c510007d7634c51006ef6634c51006ef4634c510007d4634c510005f4724c510007d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100cff0704c510016f7604c510017f3604c5100cff2504c5100cff0304c5100cff2204c51000df676c85100bef676c851000cf676c8510005f775c8510005f575c85100077765c8510006f665c8510006f465c85100077465c85100067465c8510005f773c8510005f573c8510015f672c8510017e672c8510006f762c8510007e762c8510006f562c8510007e462c851000df670c85100bff270c8510007f170c851000df470c8510016f760c8510017f360c85100bff250c85100bff030c85100bff220c8510015f87654110086f87654110014f8765411000dfb755411000f7b75541100077b65541100a6fa65541100a6f86554110007786554110005f873541100077b5354110007795354110005fb7254110007f37154110015fa7154110015f87154110087f0715411000efb615411000ff36154110087f25154110007f15154110087f23154110007f13154110007f32154110087f02154110015fa76cc110066fa76cc110014fa76cc110005fb75cc110005f975cc1100077b65cc110006fa65cc110006f865cc1100077865cc1100067865cc11000dfa73cc11000fda73cc110006fb63cc110007db63cc110006f963cc110007d863cc110005f972cc110015fa71cc110067f271cc110007f171cc110015f871cc11000efb61cc11000ff361cc110067f251cc110007f151cc110067f231cc110007f131cc110007f321cc110067f021cc110015f8764811002ef87648110014f87648110005fb7548110005f975481100077b6548110007786548110005fa7348110005f8734811000dfb724811000feb7248110007eb624811003efa624811003ef86248110007e86248110007ea3248110007e93248110007f37148110015fa7148110015f8714811002ff0714811000efb614811000ff3614811002ff25148110007f1514811002ff23148110007f13148110007f3214811002ff02148110
  | 1 => 0x89100057f75589100057c75589100067f65589100067c6558910005bf7458910025bc7458910005df7358910005dc73589100bdf77158910045fb7058910004ff75589100067f75589100047f75589100a4fc75589100067c75589100047c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df735891006cfc7358910006dc7358910004dc7358910006ef72589100bcff7158910006f7715891002ef421589100acff7058910006fb70589102a4fe76189100067f65189100067c6518910025be7418910005bd7418910006ed62189100a4fe7518910004fd751891001cfe741891003ebe741891001cbe7418910004fd741891003ebd7418910004bd741891003cfc741891006cfe7318910004fd731891003cfe721891003eee7218910006ef421891003eec421891000cff7118910014fe711891000cfd7118910014fc711891003eef211891029eed2118910014ff701891000cfe7018910014fd701891003ef9701891000cfc701891003eef201891003efa2018910296ed20189100a4ff76d4910004fe76d4910004fd76d49100a4fc76d49100067f65d49100a67c65d4910015f671d4910005f571d491000dfa70d4910005f970d49101df7a50d491003cff7694910004fe7694910004fd769491003cfc76949100067f65949100067c6594910015f4719491000dfa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc76549100067f65549100067c6554910005bf7454910025bc7454910005f77154910015f4715491000dfa70549101af7a505491003cff7614910004fe7614910004fd761491003cfc76149100067f65149100a67c6514910015f67114910005f5711491000dfa7014910005f9701491003cff7690910004fe7690910004fd769091003cfc76909100067f65909100067c6590910006bf649091001ebc649091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc76509100067f65509100067c655091001ebe6450910006bd6450910005f77150910015f4715091006cff76cc910004fe76cc910004fd76cc91006cfc76cc9100067f65cc9100067c65cc910025be74cc910005bd74cc910006ef62cc910006ec62cc910015f671cc910005f571cc91000df870cc91003cff768c910004fe768c910004fd768c91003cfc768c9100067f658c9100067c658c910025be748c910005bd748c910006df638c910006dc638c910015f4718c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9100067c654c910005f7714c910015f4714c910005fb704c91000df8704c91003cff760c910004fe760c910004f
  | 2 => 0xddf77158d10065fb7058d10004ff7558d100067f7558d100047f7558d100a4fc7558d100067c7558d100047c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d1001cfc7458d10006bc7458d1001cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d10004ec7258d100dcff7158d10006f77158d100ccff7058d10006fb7058d100cef83058d102c4fe7618d100067f6518d100067c6518d10025be7418d10005bd7418d10006dd6318d100a4fe7518d10004fd7518d1001cfe7418d1006ebe7418d1001cbe7418d10004fd7418d1006ebd7418d10004bd7418d1006cfc7418d1006cfe7318d1006ede7318d10006df4318d1006edc4318d1003cfe7218d10004fd7218d1000cff7118d10014fe7118d1000cfd7118d1006ef57118d10014fc7118d1006edf3118d1006ef63118d102bedd3118d10014ff7018d1000cfe7018d10014fd7018d1000cfc7018d1006edf3018d102b6dd3018d100a4ff76d4d10004fe76d4d10004fd76d4d100a4fc76d4d100067f65d4d100a67c65d4d10015f671d4d10005f571d4d102677651d4d1000dfa70d4d10005f970d4d1006cff7694d10004fe7694d10004fd7694d1006cfc7694d100067f6594d100067c6594d100075f5394d10015f67194d10005f57194d1000df87094d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100067c6554d10005bf7454d10025bc7454d10015f67154d10237765154d10005fb7054d1000df87054d1006cff7614d10004fe7614d10004fd7614d1006cfc7614d100067f6514d100a67c6514d10015f67114d10005f57114d1000dfa7014d10005f97014d1006cff7690d10004fe7690d10004fd7690d1006cfc7690d100067f6590d100067c6590d10006bf6490d1001ebc6490d10015f67190d10005f57190d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d100067c6550d1001ebe6450d10006bd6450d10005fb7050d1000df87050d100067f65d89100067c65d89100a4fe75d8910004fd75d891001cfe74d8910004fd74d891001cfc74d891006cfe73d8910004fd73d8910006ef42d8910006ec42d891000cff71d891000cfd71d89102a6f571d89102aeef21d89102aeed21d89102aef421d8910014ff70d8910014fd70d89102a6ef20d89102a6ed20d89100acfd76989100057e75989100057d75989100067f65989100067c6598910006ef62989100adf5719891002df970989100a4fe759891003e7e75989100047e7598910004fd759891003e7d75989100047d759891001cfe7498910004fd749891003cfc749891006cfe7398910004fd739891003cfe72989100acfd719891003ef571989100bcfd709891003ef9709891003efa209
  | 3 => 0xd41195102fe7c41195102fe7f31195102fe7e31195102fe7d31195102fe7c31195102fe7f21195102fe7e21195102fe7d21195102fe7c21195102fe7421195100a67f70195102f67e70195102f67a70195102f67d70195102fe7970195100a67c70195102f67f40195102f67e40195102f67d40195102f67c40195102f67f30195102f67e30195102f67d30195102f67c30195102f67830195102f67f20195102f67e20195102f67d20195102f67c20195102f67f10195102f67e10195102f67d10195102f67c101951001cfe76d91100067f65d91100067c65d9110026be64d91100a4fe75d9110004fd75d91100ecfd74d911006cfe73d9110004fd73d9110026bc43d911003cfe72d9110004fd72d9110026bc42d911000cff71d9110014fe71d911000cfd71d9110014fc71d91102eebf41d91102eebd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d91102debf40d91102debd40d911001cff76591100057f75591100057c75591100067f65591100067c6559110026bc6459110005df7359110005dc7359110005ef7259110005ec72591102d5f771591102e5fb7059110004ff75591100067f75591100047f75591100a4fc75591100067c75591100047c75591102dcff7459110006bf7459110026bc5459110004ff7359110006df7359110004df735911006cfc7359110006dc7359110004dc7359110026bf4359110004ff7259110006ef7259110004ef725911003cfc7259110006ec7259110004ec7259110026bf42591102d4ff7159110006f771591100ecff7059110006fb70591100a4ff76d5110004fe76d5110004fd76d51100a4fc76d51100067f65d51100a67c65d511001ebe64d5110006bd64d51100273e54d5110015f671d5110005f571d511000dfa70d5110005f970d5110004ff7655110004fe7655110004fd7655110004fc76551100067f65551100067c65551100067f65d8d100067c65d8d100a4fe75d8d10004fd75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df43d8d10006dc43d8d1003cfe72d8d10004fd72d8d1000cff71d8d1000cfd71d8d102cedf31d8d102cedd31d8d10014ff70d8d10014fd70d8d102cef970d8d102c6df30d8d102c6dd30d8d102c6f830d8d100ccfd7698d100057e7598d100057d7598d100067f6598d100067c6598d10006df6398d100cdf57198d10055f97098d100a4fe7598d1006e7e7598d100047e7598d10004fd7598d1006e7d7598d100047d7598d1001cfe7498d10004fd7498d1006cfc7498d1006cfe7398d1003cfe7298d10004fd7298d100ccfd7198d1006ef57198d1006ef63198d100dcfd7098d1006ef97098d100057f7558d100057c7558d100067f6558d100067c6558d10005bf7458d10025bc7458d10005ef7258d10005ec7258d10
  | 4 => 0x951030f7631d951030f7421d951030f7b70d95103077870d95103077830d95103077a20d951030f7b10d95103077610d95103077410d95103077810d95100067f74d95100067e74d95100063e74d95100067d74d95100063d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067c42d95103067f71d951030e7e71d95103067d71d95103067c71d951030e7f41d951030e7e41d951030e7d41d951030e7c41d951030e7f31d951030e7e31d951030e7d31d951030e7c31d951030e7f21d951030e7e21d951030e7d21d951030e7c21d95103067f70d95103067e70d95103067d70d95103067c70d95103067f40d95103067e40d95103067d40d95103067c40d95103067f30d95103067e30d95103067d30d95103067c30d95103067f20d95103067e20d95103067d20d95103067c20d95103067f10d95103067e10d95103067c10d95100f4fd76995100067f65995100f5f57199510085f970995100a4fe75995102f47e759951001cfe7499510004fd749951001cfc749951006cfe7399510004fd739951003cfe7299510004fd72995100f4fd71995100a6f571995100a6f65199510096f42199510104fd70995100a6f970995100a6fa5099510106f83099510105f77159510095fb70595100067f7559510004ff745951001cfe745951001cfc7459510004ff735951006cfc7359510004ff725951003cfc7259510104ff7159510006f771595100f4ff7059510006fb7059510304fe76195100067d65195100a4fe75195100a67e751951001cfe7419510004fd741951001cfc74195100067e54195100a67c541951006cfe7319510004fd731951003cfe7219510004fd721951000cff7119510014fe711951000cfd71195100a6f57119510014fc71195100a67f51195100a6f651195102fe7d51195102fef42119510014ff701951000cfe7019510014fd70195100a6f9701951000cfc70195100a67f50195100a6fa50195102f67d50195102f6f830195103057e76195100067e76195103047e76195100067e64195100067c64195102ff7671195102f77571195102ff7631195102ff7421195102f77a70195102ff7970195102f77830195102f77a20195102ff7b10195102f77610195102f77410195102f77810195100a67f74195100067e74195100067d74195100a67c74195100a67f73195100067e73195100067d73195100a67c73195100067f43195100067c43195100a67f72195100067e72195100067d72195100a67c72195100067f42195100067c42195100a67f71195102fe7e71195102fe7671195102f67d71195102f67571195100a67c71195102fe7f41195102fe7e41195102fe7
  | 5 => 0x194fe769492003fe820949200a4ff765492000cfe76549201acfd765492000cfc76549200067f65549200067c6554920005bf7454920035bc7454920005f7715492002df47154920005fb705492000df870549201afe820549201c4fe7614920314fe769092001cff765092000cfe7650920174fd765092000cfc7650920006bf645092001ebc6450920005fb705092000df8705092000cfe76cc92000cfc76cc920035be74cc920005bd74cc920006df63cc92006edc63cc92000dfa70cc920005f970cc920114fe768c920035be748c920005bd748c920115ee768c920006ee768c920007ae748c920007ad748c92012ded738c92006eee638c92006eec638c92000dee708c92000dec708c92003eef608c920147ea108c92006cff764c92000cfe764c92012cfd764c92000cfc764c920006df634c920006dc634c920005fb704c92000df8704c92000dec764c92012eec764c92000cec764c920007cf734c920007cf634c92006eee634c92006eec634c920007cc634c920007eb704c92000dee704c92000dec704c92012fe8704c92012eef604c92012fea104c920144fe760c9200057e750c9200057d750c920145ee720c920014fe76d852002ef661d85200a4fe75d8520004fd75d852001cfe74d8520004fd74d852001cfc74d852006cfe73d8520004fd73d852000cfd72d8520014fc72d852002ef451d852002ef621d852000cfe70d852000cfc70d85200bef710d85200057f75585200057c7558520005bf7458520035bc7458520005df7358520005dc735852002ef46158520004fe76d4520004fd76d45200a4fc76d4520006f761d4520016f461d452002f7651d4520004ff7654520004fe7654520004fc7654520005ef7254520005ec7254520004ff7650520004fe7650520004fc7650520004fe76cc520004fd76cc52006cfc76cc5200057e75cc5200057d75cc520005ee72cc520005ed72cc520007cd32cc520004ff764c520004fe764c520004fc764c520007cd324c520294fe76c8520016f661c852000df870c852000cfc7648520006f76148520016f46148520005fb704852000df8704852000dfa76c812000efa76c812000cfa76c812003f7a75c812003f7975c812000dfa72c812000fea72c812000efb62c812000feb62c812003fea32c8120007e932c8120005f971c8120025be74d9510005bd74d951001cfe74d9510006be74d951001cbe74d9510004fd74d9510006bd74d9510004bd74d951001cfc74d95100067e54d95100067c54d951006cfe73d9510004fd73d951003cfe72d9510004fd72d951000cff71d951000cfd71d951030e7f51d951030e7d51d9510014ff70d9510014fd70d95103067f50d95103067d50d95100073e74d95100073d74d95100067e64d95100067c64d95103077771d95103077471d
  | 6 => 0xe72d912000cfd72d912003cfc72d9120036bf42d9120014fe71d9120004fd71d9120014fc71d9120006be41d9120036bc41d912003cff70d9120184fd70d9120186bf40d9120186bd40d9120036bc645912031def7259120004ff75591200a4fc7559120184ff7459120006bf7459120004ff735912006cfc735912031cff7259120006ef7259120004ff7159120014fe7159120014fc7159120174ff7059120006fb70591200a4ff76d5120004fe76d5120004fd76d51200a4fc76d5120006bf64d512001ebc64d51200373e54d5120004ff7655120004fe7655120004fd7655120004fc76551200a4fe75d8d20004fd75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20006dc31d8d2003cff70d8d20144fd70d8d20146df30d8d20146dd30d8d20035be7498d20005bd7498d20006df6398d2012ded7298d200a4fe7598d20004fd7598d2001cfe7498d2006ebe7498d2001cbe7498d20004fd7498d2006ebd7498d20004bd7498d2006cfc7498d2006cfe7398d2012cfd7298d2006eed7298d20014fe7198d20004fd7198d20014fc7198d2015cfd7098d2006ef97098d2015efa1098d2015def7258d20004ff7558d200a4fc7558d20004ff7458d2001cfe7458d2001cfc7458d20006df7358d2015cff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d2012cff7058d20006fb7058d20144fe7618d200057e7518d200057d7518d20006dd6318d200a4fe7518d2006e7e7518d200047e7518d20004fd7518d2006e7d7518d200047d7518d2001cfe7418d20004fd7418d2006cfc7418d2006ede7318d2003cfe7218d2006eed7218d2003cfc7218d20014fe7118d20004fd7118d20014fc7118d20006de3118d2006edc3118d2003cff7018d20114fd7018d2006edf3018d20116dd3018d20116fa1018d200a4ff76d4d20004fe76d4d20004fd76d4d200a4fc76d4d200a67e65d4d200067d65d4d20006df63d4d20006dc63d4d2006cff7694d20004fe7694d20004fd7694d2006cfc7694d200075f5394d20005ee7294d20005ed7294d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067e6554d200067d6554d20005bf7454d20035bc7454d20005fb7054d2000df87054d2006cff7614d20004fe7614d20004fd7614d2006cfc7614d20006df6314d2006edc6314d20005ee7214d20005ed7214d2006cff7690d20004fe7690d20004fd7690d2006cfc7690d20006df6390d2006edc6390d20005ee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d2001ebc6450d20006df6350d20006dc6350d2000cfe76d492000cfc76d49200067f65d49200a67c65d492000dfa70d4920005f970d4920
  | 7 => 0xcb2000dee708cb2003fea708cb2003fe9708cb2000dec708cb2015cff764cb200067e654cb200067d654cb2015def764cb20006ef764cb200076e654cb200076d654cb2003fcf734cb2006eee634cb2006eec634cb2000dee704cb2000dec704cb20014ff76587200067e65587200067d655872003ef46158720004ff75587200a4fc7558720004ff745872001cfe745872001cfc7458720004ff735872006cfc7358720014fd725872000cfc725872003ef7215872003ef421587200aefa20587200aef710587200a4ff76d472003cfe76d4720004fd76d47200a67e65d47200067d65d47200477651d4720004ff7654720004fd765472003cfc76547200067e65547200067d6554720005ef725472003dec7254720004ff7650720004fd765072003cfc76507200067e65507200067d655072001ebe6450720006bd645072006cff76cc72003cfe76cc720004fd76cc7200057e75cc7200057d75cc7200067e65cc7200067d65cc72006ede63cc720006dd63cc72003dee72cc720005ed72cc720007cd32cc720004ff764c720004fd764c72003cfc764c7200067e654c7200067d654c720006de634c720006dd634c720007cd324c7202a4ff76487200067e65487200067d654872001cfe74d9520004fd74d952001cfc74d952006cfe73d9520004fd73d9520014fe71d9520004fd71d9520014fc71d95200067e51d95200067c51d952003cff70d95201c4fd70d95201c67f50d95201c67d50d95201c6fa10d95200067f65995201aded72995200a4fe759952001cfe7499520004fd749952001cfc749952006cfe7399520004fd73995201acfd72995200a6ed7299520014fe7199520004fd7199520014fc71995201dcfd70995200a6f970995201de7e50995200a67c5099520005bf7459520035bc7459520005df7359520005dc73595201ddef7259520005f7715952002df471595200067f7559520004ff7459520006bf7459520004bf745952001cfe745952001cfc7459520006bc745952001cbc7459520004ff7359520006df7359520004df735952006cfc7359520006dc7359520004dc73595201dcff7259520006ef7259520004ff7159520006f77159520004f77159520014fe7159520014fc7159520006f47159520014f471595201acff7059520006fb70595201ae7e50595201ae7c50595201aefa10595201c4fe76195200067d65195200a67e751952001cfe7419520004fd741952001cfc741952006cfe7319520004fd731952003cfe721952003cfc7219520014fe7119520004fd7119520014fc71195200067e51195200a67c511952003cff7019520194fd70195200a67f50195201967d501952001cfe76d9120036be64d91200a4fe75d9120004fd75d9120036bc54d912006cfe73d9120004fd73d9120036bf43d912003cf
  | 8 => 0x67e65553200067d65553200a4fe75d8f2003e7e75d8f200047e75d8f20004fd75d8f2003e7d75d8f200047d75d8f2001cfe74d8f2003ebe74d8f2001cbe74d8f20004fd74d8f2003ebd74d8f20004bd74d8f2003cfc74d8f2003cfe72d8f2003eee72d8f20014fe71d8f20004fd71d8f20014fc71d8f2003ef970d8f2012cfd7698f200067e6598f200067d6598f2004dbe7498f20005bd7498f2003edf6398f200a4fe7598f20004fd7598f2001cfe7498f2006ebe7498f2001cbe7498f20004fd7498f2006ebd7498f20004bd7498f2006cfc7498f20006df4398f2006edc4398f2000cfe7298f2006eee7298f2000cfc7298f2003ede3298f2003edc3298f20014fe7198f20004fd7198f20014fc7198f2006edf3098f2015edd3098f200067e6558f200067d6558f2003edc6358f20004ff7558f200a4fc7558f20004ff7458f2001cfe7458f2001cfc7458f2003edf7358f20006df4358f20006dc4358f2006cff7258f2000cfe7258f2012cfd7258f2000cfc7258f2003ede3258f2003edc3258f20004ff7158f20014fe7158f20014fc7158f2012edf3058f2012edd3058f200a4fe7518f2003e7e7518f200047e7518f20004fd7518f2003e7d7518f200047d7518f2001cfe7418f20004fd7418f2003cfc7418f2006cfe7318f2003ede7318f2003cfe7218f2003eee7218f20014fe7118f20004fd7118f20014fc7118f2003ef97018f200a4ff76d4f2003cfe76d4f20004fd76d4f2003cfc76d4f200a67e65d4f200067d65d4f2006cff7694f2003cfe7694f20004fd7694f2003cfc7694f200067e6594f200067d6594f200075f5394f2003dee7294f20005ed7294f20004ff7654f2003cfe7654f20004fd7654f2003cfc7654f200067e6554f200067d6554f20005bf7454f2004dbc7454f20005fb7054f2000df87054f2006cff7614f2003cfe7614f20004fd7614f2003cfc7614f200a67e6514f200067d6514f2003dee7214f20005ed7214f2006cff7690f2003cfe7690f20004fd7690f2003cfc7690f200067e6590f200067d6590f2001ebe6490f20006bd6490f2003dee7290f20005ed7290f20004ff7650f2003cfe7650f20004fd7650f2003cfc7650f200067e6550f200067d6550f20006bf6450f2001ebc6450f20005fb7050f2000df87050f201acfd76d4b200a67e65d4b200067d65d4b201dcff7654b200067e6554b201ae7d6554b20005bf7454b2004dbc7454b20005f77154b20045f47154b2031cff7650b200067e6550b200067d6550b2003ebf6450b2003ebc6450b2012cfd76ccb200067e65ccb200067d65ccb2004dbe74ccb20005bd74ccb2000ded768cb2003eed768cb2000ced768cb2003f6e658cb2003f6d658cb2003fae748cb2003fad748cb2006eee638cb2003fce638cb2003fcd638cb2003eec638
  | 9 => 0xd209972003e7c20997201de7f10997201de7e10997201de7d10997201de7c109972003e7c6559720005bf745972004dbc745972003e7f7559720004ff7459720006bf7459720004bf745972001cfe745972001cfc7459720006bc745972001cbc74597200067e54597200067c5459720004ff735972006cfc73597200a4ff725972000cfe72597201acfd725972000cfc725972003e7e525972003e7c5259720004ff7159720014fe7159720014fc71597200067e51597200067c51597201ae7f50597201ae7d505972003d7f76597200067f76597200073f74597200073c745972003e7f64597200067e645972003e7c645972003e7f635972003e7c635972003e7f61597200067e615972003e7c61597201af6e205972003f7a205972003f6c20597200067f74597200063f74597200067e74597200067d74597200067c74597200063c74597200067f73597200067e73597200067d73597200067c73597200067f43597200067c435972003e7e725972003e7c72597200067f425972003e7e425972003e7c425972003e7e325972003e7c32597200067f71597200067e71597200067d71597200067c71597200067f41597200067e41597200067c41597200067e31597200067c315972003e7f21597200067e215972003e7c21597201ae7f70597201ae7e70597201ae7d70597201ae7c70597201ae7f40597201ae7e40597201ae7d40597201ae7c40597201ae7f30597201ae7e30597201ae7d30597201ae7c305972003e7f20597201ae7e20597201ae7d205972003e7c20597201ae7f10597201ae7e10597201ae7d10597201ae7c10597200a4fe751972003e7e75197201dc7e751972001cfe7419720004fd741972003cfc741972006cfe7319720004fd731972003cfe721972003eee7219720014fe7119720004fd7119720014fc711972003ef970197200a4fe75d932003e7e75d93200047e75d9320004fd75d932003e7d75d93200047d75d9320174fd74d932004ebc54d932006cfe73d932003ede73d9320004de73d9320004fd73d932003edd73d9320004dd73d932004ebf43d932003cfe72d932003eee72d932003ebf42d9320014fe71d9320004fd71d9320014fc71d932003ef970d932001cff76593200067e65593200067d655932003ebc6459320004ff75593200a4fc755932003ebf7459320004ff735932006cfc735932004ebc435932001cff725932000cfe725932001cfd725932000cfc725932003ebe425932003ebc4259320004ff7159320014fe7159320014fc715932004ebf4159320176bf4059320176bd40593200a4ff76d532003cfe76d5320004fd76d532003cfc76d53200a67e65d53200067d65d5320006bf64d532001ebc64d532004f3e54d5320004ff765532003cfe7655320004fd765532003cfc7655320
  | 10 => 0x4930005dd7314930004fe7690930004fd769093003cfc7690930004ff7650930004fe7650930004fc7650930006bf645093001ebc6450930114fe76cc93005dbe74cc930005bd74cc93000cfe768c93005dbe748c930005bd748c930006ef628c93003eec628c93000dfa708c930005f9708c930147d8308c93000cfc764c930006ef624c930006ec624c930005fb704c93000df8704c93015cfe760c9300057e750c9300057d750c93006fd8300c930014fe76d8530056f661d85300a4fe75d8530004fd75d853001cfe74d8530004fd74d853001cfc74d853000cfd73d8530014fc73d853003cfe72d8530004fd72d8530056f631d85300def830d85300def710d85300057f75585300057c7558530005bf745853005dbc7458530005ef7258530005ec7258530056f46158530004fe76d4530004fd76d45300a4fc76d45300577651d4530004ff7654530004fe7654530004fc7654530004ff7650530004fe7650530004fc76505302b4fe76cc5300057e75cc5300057d75cc53006fd830cc53000cfc764c530006f7614c530016f4614c530005fb704c53000df8704c5300cfd8304c530004fe76c8530004fd76c853003cfc76c8530004ff7648530004fe7648530004fc764853000dfa76cc13000efa76cc130006fa65cc130006f865cc13000dfa73cc13000fda73cc13000efb63cc13000fdb63cc130006fb61cc13001cfe74d9720004fd74d972003cfc74d972006cfe73d9720004fd73d972003cfe72d972003eee72d9720014fe71d9720004fd71d9720014fc71d972003ef970d97201acfd769972003e7f659972001cfe7499720004fd749972001cfc74997200067e54997200a67c549972006cfe7399720004fd739972000cfe729972000cfc729972003e7e529972003e7c5299720014fe7199720004fd7199720014fc71997200067e51997200a67c51997200a67f50997201de7d50997201ac7d769972003e7f64997200067e649972003e7c649972003e7f639972003e7c639972003e7f61997200067e619972003e7c61997201df6e209972003f7a209972003f6c20997200a67f74997200067e74997200067d74997200a67c74997200a67f73997200067e73997200067d73997200a67c73997200067f43997200067c439972003e7e729972003e7c72997200067f429972003e7e429972003e7c429972003e7e329972003e7c32997200a67f71997200067e71997200067d71997200a67c71997200067f41997200067e41997200067c41997200067e31997200067c319972003e7f21997200067e219972003e7c21997200a67f70997201de7e70997201de7d70997200a67c70997201de7f40997201de7e40997201de7d40997201de7c40997201de7f30997201de7e30997201de7d30997201de7c30997201de7e20997201de7
  | 11 => 0x67f7559530004ff7459530006bf7459530004bf745953001cfe745953001cfc7459530006bc745953001cbc745953025cff7359530006df7359530004ff725953003cfc7259530004ff7159530014fe7159530014fc715953022cff7059530006fb7059530004fb7059530244fe76195300067d65195300a67e751953001cfe7419530004fd741953001cfc74195300067e54195300a67c541953006cfe731953006cfc731953003cfe7219530004fd7219530014fe7119530004fd7119530014fc71195300067e51195300a67c511953006cff7019530214fd70195300a67f50195302167d5019530216f8301953001cfe76d913005ebe64d91300a4fe75d9130004fd75d913005ebc54d913006cfe73d913000cfd73d913006cfc73d913005ebf43d913003cfe72d9130004fd72d913005ebf42d9130014fe71d9130004fd71d9130014fc71d9130006be41d913005ebc41d913006cff70d9130204fd70d9130206bf40d9130206bd40d91300057f75591300057c755913005ebc645913032ddf7359130004ff75591300067f75591300047f75591300a4fc75591300067c75591300047c7559130204ff7459130006bf745913032cff7359130006df7359130004ff725913003cfc7259130004ff7159130014fe7159130014fc71591301f4ff7059130006fb70591300a4ff76d5130004fe76d5130004fd76d51300a4fc76d5130006bf64d513001ebc64d513005f3e54d5130004ff7655130004fe7655130004fd7655130004fc765513000cfe76d4d3000cfc76d4d300067f65d4d300a67c65d4d3000dfa70d4d30005f970d4d30214fe7694d300075f5394d300a4ff7654d3000cfe7654d3022cfd7654d3000cfc7654d300067f6554d300067c6554d30005bf7454d3005dbc7454d30005fb7054d3000df87054d30244fe7614d30324fe7690d3001cff7650d3000cfe7650d301f4fd7650d3000cfc7650d30006bf6450d3001ebc6450d30005fb7050d3000df87050d300a4fe75d8930004fd75d893001cfe74d8930004fd74d893001cfc74d8930014fe71d8930004fd71d8930014fc71d8930006ee21d8930006ec21d893015eef20d89300057e75989300057d759893005dbe7498930005bd7498930006ef6298930006ed62189300a4fe7518930004fd751893001cfe7418930004fd741893003cfc7418930014fe7118930004fd7118930014fc7118930006ee211893003eec211893003eef2018930116ed2018930004fe76d4930004fd76d49300a4fc76d49300067f65d49300a67c65d4930004fe7694930004fd769493003cfc7694930004ff7654930004fe7654930004fc76549300067f65549300067c6554930005bf745493005dbc7454930005f77154930055f47154930004fe7614930004fd761493003cfc7614930005de731
  | 12 => 0xf6450f3006ebc6450f30075be7498b30005bd7498b3006eef6298b300a4fe7598b30004fd7598b3001cfe7498b3003ebe7498b3001cbe7498b30004fd7498b3003ebd7498b30004bd7498b3003cfc7498b3000cfe7398b3006eef3298b3003eec3298b30014fe7198b30004fd7198b30014fc7198b3003eef2098b30146ed2098b3006eec6258b30004ff7558b300a4fc7558b30004ff7458b3001cfe7458b3001cfc7458b3000cfc7358b3006eef3258b3006eec3258b30004ff7158b30014fe7158b30014fc7158b3012eef2058b3012efa1058b300a4ff76d4b3006cfe76d4b30004fd76d4b300a67e65d4b300067d65d4b301df7850d4b3003cff7694b3006cfe7694b30004fd7694b3000dfa7094b30005f97094b30004ff7654b30004fd7654b3006cfc7654b300067e6554b300067d6554b30005bf7454b30075bc7454b30005f77154b30065f47154b30005fb7054b3000df87054b301af785054b3003cff7614b3006cfe7614b30004fd7614b3006dde7314b30005dd7314b3003cff7690b3006cfe7690b30004fd7690b3001ebe6490b30006bd6490b30004ff7650b30004fd7650b3006cfc7650b30006bf6450b3001ebc6450b30005fb7050b3000df87050b3012cfd768cb30075be748cb30005bd748cb30144ff764cb30014ff765873006ef46158730004ff75587300a4fc7558730004ff745873001cfe745873001cfc7458730014fd735873000cfc7358730004ff725873003cfc725873006ef7315873006ef431587300cef710587300a4ff76d473006cfe76d4730004fd76d47300677651d473000df870d4730004ff7654730004fd765473006cfc7654730005fb705473000df87054730004ff7650730004fd765073006cfc765073001ebe6450730006bd64507302c4ff764c730016f4614c73000dfa704c73003cff76c873006cfe76c8730004fd76c8730004ff7648730004fd764873006cfc7648730005f976d4330006f976d433000dfa75d433000f7a75d4330006fb65d43300077a65d4330006f965d43300077965d43300067965d4330007da73d4330005f973d4330007d973d4330005d973d433000efa63d433000fda63d43300077b53d43300077953d4330005f971d433001cfe74d9530004fd74d953001cfc74d95300067e54d95300067c54d953003cfe72d9530004fd72d9530014fe71d9530004fd71d9530014fc71d95300067e51d95300067c51d953006cff70d9530244fd70d95302467f50d95302467d50d95300067f659953022ddd73995300a4fe759953001cfe7499530004fd749953001cfc749953022cfd73995300a6dd739953003cfe7299530004fd7299530014fe7199530004fd7199530014fc719953025cfd70995300a6f9709953025ef83099530005bf745953005dbc745953025ddf7359530
  | 13 => 0x854001cfd70d85402d6f710d85400057f75585400057c7558540005df7358540005dc7358540005ef7258540005ec725854007ef46158540335fb7058540004fe76d4540004fd76d45400a4fc76d454007f7651d4540004ff7654540004fe7654540004fc7654540005bf745454001dbc7454540004fe76cc540004fd76cc54006cfc76cc5400057e75cc5400057d75cc54001dbe74cc540005bd74cc540004ff764c540004fe764c540004fc764c540004fe76c8540004fd76c854003cfc76c854001dbe74c8540005bd74c8540004ff7648540004fe7648540004fc764854001cfe74d9730004fd74d973006cfc74d973006cfe73d973006ede73d973003cfe72d9730004fd72d9730014fe71d9730004fd71d9730014fc71d973006ef970d9730246f850d9730246fa10d973022cfd769973006e7f659973001cfe7499730004fd749973001cfc749973000cfe739973000cfc739973006e7e539973006e7c539973003cfe7299730004fd7299730014fe7199730004fd7199730014fc71997300067e51997300a67c51997300a67f509973025e7d509973006e7c6559730005bf7459730075bc745973006e7f7559730004ff7459730006bf7459730004bf745973001cfe745973001cfc7459730006bc745973001cbc74597300a4ff735973000cfe735973022cfd735973000cfc735973006e7e535973006e7c5359730004ff725973003cfc7259730004ff7159730014fe7159730014fc71597300067e51597300067c5159730006fb705973022e7f505973022e7d505973022ef8505973022efa10597300a4fe751973006e7e751973001cfe7419730004fd741973006cfc741973006cfe731973006ede731973003cfe7219730004fd7219730014fe7119730004fd7119730014fc711973006ef970197300a4fe75d9330004fd75d93301f4fd74d9330076bc54d933006cfe73d933006ede73d933006ebf43d933003cfe72d9330004fd72d9330076bf42d9330014fe71d9330004fd71d9330014fc71d933006ef970d933001cff765933006ebc6459330004ff75593300a4fc755933006ebf745933001cff735933000cfe735933001cfd735933000cfc735933006ebe435933006ebc4359330004ff725933003cfc7259330076bc4259330004ff7159330014fe7159330014fc7159330076bf41593301f6bf40593301f6bd40593300a4ff76d533006cfe76d5330004fd76d533006cfc76d5330006bf64d533001ebc64d53300773e54d5330004ff765533006cfe7655330004fd765533006cfc7655330005fb705533000df8705533022cfd76d4f3006e7f65d4f3006e7c65d4f3006f5e53d4f3000df870d4f3025cff7654f3006e7f6554f3006e7c6554f30005bf7454f30075bc7454f3000df87054f3022fda3054f3032cff7650f3006eb
  | 14 => 0x5bd7494d400075f5394d40004ff7654d40004fe7654d40004fc7654d40005bf7454d4001dbc7454d40005fb7054d4000df87054d40004fe7614d40004fd7614d4006cfc7614d400067f6514d400a67c6514d4001dbe7414d40005bd7414d40006df6314d4006edc6314d4000dbc7650d401f6bc7650d4000cbc7650d40005be7550d40005bc7550d4001dbf7350d4001f9f7350d400079f6350d4006ebc6350d400079c6350d400069c6350d40005bf7250d40007bb7050d4000dbe7050d4000dbc7050d401f7b87050d4001ebf6050d4001fbb6050d400a4fe75d8940004fd75d894000cfd74d894006cfe73d8940004fd73d894034eee42d894034eed42d8940014fe71d8940004fd71d8940014fc71d8940006ee21d8940006ec21d894001cfd70d894031eef20d89400057e75989400057d7598940005de7398940005dd7398940006ef6298940035f9709894004dfb7058940006ed62189400a4fe7518940004fd751894000cfd741894003ebd7418940006bf5418940346bc541894006cfe7318940004fd7318940346bf4318940006bd431894003ebf421894003eee4218940346ed4218940014fe7118940004fd7118940014fc7118940006ee211894003eec211894003cff701894001cfd701894003eef2018940316ed2018940004fe76d4940004fd76d49400a4fc76d49400067f65d49400a67c65d494001dbc74d4940004fe7694940004fd769494003cfc769494001dbe7494940005bd749494000dfa7094940005f97094940004ff7654940004fe7654940004fc76549400067f65549400067c6554940005bf745494001dbc7454940005f7715494007df47154940004fe7614940004fd761494003cfc761494001dbe7414940005bd741494000dbc7650940176bc765094000cbc7650940005be7550940005bc7550940005bf7350940006bc635094001dbf725094001faf7250940007af625094003ebc6250940007ac6250940007bb705094000dbe705094000dbc7050940177b8705094001ebf605094001fbb6050940004fe76cc940004fd76cc94006cfc76cc94001dbe74cc940005bd74cc940006df63cc94006edc63cc940004fe768c940004fd768c94003cfc768c94001dbe748c940005bd748c940004ff764c940004fe764c940004fc764c94001dbe744c940005bd744c940006df634c940006dc634c940004fe760c940004fd760c94003cfc760c9400057e750c9400057d750c94001dbe740c940005bd740c94000dfa700c940005f9700c940014fe76d854007ef661d85400a4fe75d8540004fd75d854000cfd74d8540014fc74d8540006bf54d854033ebc54d854006cfe73d8540004fd73d854033ebf43d8540006bd43d854003cfe72d8540004fd72d854033ebf42d8540006bd42d854007ef641d854033ef541d
  | 15 => 0xc764c550006df634c550006dc634c550004fe76c8550004fd76c855003cfc76c8550006f761c8550016f461c8550004ff7648550004fe7648550004fc764855000dfa76d415000efa76d415000dfa75d415000f7a75d415000efb65d415000f7b65d4150006f863d41500a77b53d41500077953d4150005f971d415000cff74d954000cfd74d9540376bd74d954037e7f54d954037e7d54d954037ebc54d954006cfe73d9540004fd73d954003cfe72d9540004fd72d9540014fe71d9540004fd71d9540014fc71d95400067e51d95400067c51d954001cff70d954001cfd70d95403767f50d95403767d50d9540274fd76995400067f6599540275bd749954008df970995400a4fe7599540274fd74995400a6bd749954006cfe7399540004fd739954003cfe7299540004fd7299540014fe7199540004fd7199540014fc7199540284fd70995400a6f97099540285bf7459540005df7359540005dc735954009dfb70595400067f7559540284ff7459540006bf745954008ebc5459540004ff7359540006df7359540004df735954006cfc7359540006dc7359540004dc7359540004ff725954003cfc7259540004ff7159540014fe7159540014fc7159540274ff7059540006fb7059540374fe76195400067d65195400a4fe75195400a67e751954000cff741954001cfe741954000cfd741954001cfc74195400a67f541954036e7d541954006cfe7319540004fd731954003cfe7219540004fd7219540014fe7119540004fd7119540014fc71195400067e51195400a67c511954001cff701954001cfd70195400a67f50195403667d501954000dbe76d5140286be76d514000cbe76d514001dbe75d514001f3e75d5140006bf65d51400073f65d51400063f65d5140006bd65d51400073c65d5140005bd73d5140005bd72d514000dbe70d5140287ba70d5140007b970d514000dbc70d514001ebf60d514001fbb60d51400a4fe75d8d40004fd75d8d4000cfd74d8d4035ede43d8d4035edd43d8d4003cfe72d8d40004fd72d8d40014fe71d8d40004fd71d8d40014fc71d8d40006de31d8d40006dc31d8d4001cfd70d8d4032edf30d8d40006df6398d4005df97098d400057f7558d400057c7558d40075fb7058d40006dd6318d400a4fe7518d40004fd7518d4000cfd7418d4006ebd7418d40006bf5418d40356bc5418d4006ebf4318d4006ede4318d40356dd4318d4003cfe7218d40004fd7218d40356bf4218d40014fe7118d40004fd7118d40014fc7118d40006de3118d4006edc3118d4006cff7018d4001cfd7018d4006edf3018d40326dd3018d40004fe76d4d40004fd76d4d400a4fc76d4d4001dbc74d4d40006df63d4d40006dc63d4d40004fe7694d40004fd7694d4006cfc7694d400067f6594d400067c6594d4001dbe7494d40
  | 16 => 0x4d5000cfe7694d5022d7d7594d50006df6394d5006edc6394d500075f5394d5000dfa7094d50005f97094d50247785094d5000cfc7654d50005bf7454d5008dbc7454d50006df6354d50006dc6354d50005fb7054d5000df87054d5000d7c7654d5022e7c7654d5000c7c7654d500073f7454d500073c7454d500075f7354d500075f6354d5006e7c6354d500075c6354d502367e6154d502367c6154d500077b7054d5000d7e7054d5000d7c7054d5022f787054d5000d787054d5022e7f6054d5022f7a1054d5025cfe7614d5025d7e7514d500a7785014d50004fe7690d50004fd7690d5006cfc7690d500057e7590d500057d7590d50006bf6490d5001ebc6490d50004ff7650d50004fe7650d50004fc7650d5001cfe74d8950004fd74d895001cfc74d895006cfe73d8950004fd73d89500067f53d89500067d53d8950014fe71d8950004fd71d8950014fc71d89501de7e50d89501de7c50d89501deef20d89501defa10d8950006ef6298950005bf745895008dbc7458950005df7358950005dc7358950005f77158950085f47158950006ed621895001cfe7418950004fd741895003cfc741895006cfe7318950004fd7318950014fe7118950004fd7118950014fc711895003eef2018950196ed2018950194fe76d49501de7f65d495000cfe7694950006ef629495003eec629495000dfa7094950005f9709495000cfc76549501ae7f6554950005bf745495008dbc7454950006ef6254950006ec6254950005f77154950085f47154950005fb705495000df870549501dcfe7614950004fe7690950004fd769095003cfc7690950006bf649095001ebc6490950004ff7650950004fe7650950004fc76509500057f75509500057c7550950004fe76cc950004fd76cc95006cfc76cc9500057e75cc9500057d75cc95008dbe74cc950005bd74cc950004fe768c950004fd768c95003cfc768c95008dbe748c950005bd748c950006df638c950006dc638c950004ff764c950004fe764c950004fc764c950004fe760c950004fd760c95003cfc760c9500057e750c9500057d750c950006df630c95006edc630c950014fe76d8550086f661d855000cfd75d8550014fc75d855001cfe74d8550004fd74d855001cfc74d855006cfe73d8550004fd73d855003cfe72d8550004fd72d8550086f651d8550086f421d8550106f710d8550086f461585502f4fe76d45500877651d455000df870d45500a77850d455000cfc7654550006f76154550016f46154550087745154550005fb705455000df870545500f7785054550004ff7650550004fe7650550004fc7650550006bf645055001ebc6450550004fe76cc550004fd76cc55006cfc76cc5500057e75cc5500057d75cc550006df63cc55006edc63cc550004ff764c550004fe764c550004f
  | 17 => 0x1c6ed2098b500a6ec6258b50005f77158b50095f47158b5000cfc7558b50004ff7458b5001cfe7458b5001cfc7458b50004ff7358b5006cfc7358b500067f5358b500067d5358b500a6ef5258b500a6ec5258b50004ff7158b50006f77158b50004f77158b50014fe7158b50014fc7158b50006f47158b50014f47158b501ae7e5058b501ae7c5058b501aeef2058b501acfd7694b501c77a5094b501c4ff7654b501ae7e6554b50005bf7454b5009dbc7454b50005f77154b50095f47154b5003cff7690b500a4fe7690b50004fd7690b50004ff7650b50004fd7650b500a4fc7650b500057f7550b500a57c7550b5006cff76ccb500a4fe76ccb50004fd76ccb500a57e75ccb500057d75ccb5009dbe74ccb50005bd74ccb5003cff768cb500a4fe768cb50004fd768cb5009dbe748cb50005bd748cb5000dfa708cb50005f9708cb50004ff764cb50004fd764cb500a4fc764cb50005fb704cb5000df8704cb5003cff760cb500a4fe760cb50004fd760cb500a57e750cb500057d750cb50014ff76587500a6f46158750014fd755875000cfc7558750004ff745875001cfe745875001cfc7458750004ff735875006cfc7358750004ff725875003cfc72587500a6f751587500a6f451587500f6fa50587500f6f830587500f6f71058750304ff7654750016f461547500a77451547500f77a5054750004ff7650750004fd76507500a4fc765075006cff76cc7500a4fe76cc750004fd76cc7500a57e75cc7500057d75cc750004ff764c750004fd764c7500a4fc764c750005fb704c75000df8704c75003cff76c87500a4fe76c8750004fd76c8750016f461c8750004ff7648750004fd76487500a4fc764875001cfe76d915008ebe64d915000cfd75d915001cfc75d915008ebe54d915006cfe73d9150004fd73d915008ebc43d915003cfe72d9150004fd72d915008ebc42d9150014fe71d9150004fd71d9150014fc71d915008ebf41d9150286bf40d915008ebc6459150005df7359150005dc7359150364fe76d515001ebe64d515008f3e54d515000cfc7655150006bf645515001ebc6455150005fb705515000df8705515001cfe74d8d50004fd74d8d5001cfc74d8d50006df43d8d50006dc43d8d5003cfe72d8d50004fd72d8d50014fe71d8d50004fd71d8d50014fc71d8d5025edf30d8d50006df6398d50005bf7458d5008dbc7458d50006dd6318d5006e7d7518d5001cfe7418d50004fd7418d5006cfc7418d50006df4318d5006edc4318d5003cfe7218d50004fd7218d50014fe7118d50004fd7118d50014fc7118d50216f85018d5006edf3018d50216dd3018d50216fa1018d50214fe76d4d502157e76d4d500067e76d4d5006e7c63d4d502667e61d4d502667c61d4d5000d7e70d4d5000d7c70d4d500a67f60d4d5025f7a10d
  | 18 => 0xf65549210067c6554921005bf74549210b5bc7454921005f77154921015f471549211ccfe7614921384fe769092101cff7650921014fe765092117cfd7650921014fc7650921006bf645092101ebc6450921005f77150921015f47150921014fe76cc921014fc76cc9210b5be74cc921005bd74cc921006df63cc92106edc63cc921015f671cc921005f571cc92111cfe768c9210b5be748c921005bd748c92106cff764c921014fe764c921134fd764c921014fc764c921006df634c921006dc634c921005f7714c921015f4714c92114cfe760c9210057e750c9210057d750c921006f665c8521006f465c8521015f672c8521017e672c8521016f762c8521017e762c852100cfe76d81210aefa60d81210a4fe75d8121004fd75d812101cfe74d8121004fd74d812101cfc74d812106cfe73d8121004fd73d8121014fd72d812100cfc71d8121006f721d8121046f421d81210aefa20d81210aefa10d81210057f75581210057c7558121005bf74581210b5bc7458121005df7358121005dc73581210aef8605812101cff76593500a6bc645935001cfd755935000cfc75593500a6bf54593500a6bc5459350004ff735935006cfc7359350004ff725935003cfc7259350004ff7159350014fe7159350014fc7159350276bf4059350374ff76553502777a50553500a6df6398f5000cfe7598f5006e7e7598f5001cfe7498f50004fd7498f5006cfc7498f500a6df5398f5006edc5398f5003cfe7298f50004fd7298f50014fe7198f50004fd7198f50014fc7198f5006edf3098f50246dd3098f500a6dc6358f5000cfc7558f50004ff7458f5001cfe7458f5001cfc7458f500a6df5358f500a6dc5358f50004ff7258f5003cfc7258f50004ff7158f50014fe7158f50014fc7158f50006fb7058f5022edf3058f5022ef83058f5000d7d76d4f500a67d76d4f5000c7d76d4f5006e7e63d4f500a75e63d4f500065e63d4f500a75d63d4f502667e61d4f500a67c61d4f5000d7e70d4f500a77a70d4f500a77970d4f5000d7c70d4f5025f7830d4f5022cfd7694f500a75f5394f5000df87094f50244ff7654f50005bf7454f5009dbc7454f5000df87054f5022f7a5054f502457f7654f500067f7654f500073f7454f500073c7454f500a75f7354f5006e7e6354f502367e6154f502367c6154f500077b7054f5000d7e7054f5000d7c7054f5022f787054f5000d787054f5022f783054f5006cff7690f500a4fe7690f50004fd7690f500a57e7590f500057d7590f50004ff7650f50004fd7650f500a4fc7650f50005fb7050f5000df87050f500a6ef6298b5000cfe7598b5001cfe7498b50004fd7498b5003cfc7498b5006cfe7398b50004fd7398b500a6ef5298b5003eec5298b50014fe7198b50004fd7198b50014fc7198b5003eef2098b50
  | 19 => 0x91210a4fe75d9121004fd75d91210b6bc54d912106cfe73d9121004fd73d91210b6bf43d9121014fd72d91210b6bf42d912103cff71d912118cfd71d912118ebf41d912118ebd41d912100cfe70d9121004fd70d912100cfc70d9121006be40d91210b6bc40d91210057f75591210057c75591210b6bc645912138def7259121004ff75591210067f75591210047f75591210a4fc75591210067c75591210047c755912118cff7459121006bf7459121004ff735912106cfc735912138cff7259121006ef725912117cff7159121006f77159121004ff705912100cfe705912100cfc70591210a4ff76d5121004fe76d5121004fd76d51210a4fc76d5121006bf64d512101ebc64d51210b73e54d5121004ff7655121004fe7655121004fd7655121004fc76551210a4fe75d8d21004fd75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d2103cff71d8d2114cfd71d8d2114edf31d8d2114edd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d210057e7598d210057d7598d210b5be7498d21005bd7498d21006df6398d21135ed7298d210a4fe7598d2106e7e7598d210047e7598d21004fd7598d2106e7d7598d210047d7598d2101cfe7498d2106ebe7498d2101cbe7498d21004fd7498d2106ebd7498d21004bd7498d2106cfc7498d2106cfe7398d21134fd7298d2106eed7298d21164fd7198d2106ef57198d2100cfe7098d21004fd7098d2100cfc7098d21165ef7258d21004ff7558d210a4fc7558d21004ff7458d2101cfe7458d2101cfc7458d21006df7358d21164ff7258d21006ef7258d21134ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d2114cfe7618d21006dd6318d210a4fe7518d21004fd7518d2101cfe7418d21004fd7418d2106cfc7418d2106ede7318d2103cff7118d2111cfd7118d2106edf3118d2111edd3118d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d2106edc3018d210a4ff76d4d21004fe76d4d21004fd76d4d210a4fc76d4d210067f65d4d210a67c65d4d2106cff7694d21004fe7694d21004fd7694d2106cfc7694d210075f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d210067c6554d21005bf7454d210b5bc7454d21005fb7054d210adf87054d2106cff7614d21004fe7614d21004fd7614d2106cfc7614d21005ee7214d21005ed7214d2106cff7690d21004fe7690d21004fd7690d2106cfc7690d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2101ebc6450d21014fe76d4921014fc76d49210067f65d49210a67c65d4921015f671d4921005f571d492119cfe76949210076f52949210a4ff7654921014fe76549211b4fd7654921014fc76549210067
  | 20 => 0x67d65d4f212677451d4f2106cff7694f2103cfe7694f21004fd7694f2103cfc7694f210075f5394f21015f67194f21005f57194f21004ff7654f2103cfe7654f21004fd7654f2103cfc7654f210067e6554f210067d6554f21005bf7454f210c5bc7454f21005f77154f21015f47154f21237745154f21005fb7054f210bdf87054f2106cff7614f2103cfe7614f21004fd7614f2103cfc7614f2103dee7214f21005ed7214f2106cff7690f2103cfe7690f21004fd7690f2103cfc7690f2101ebe6490f21006bd6490f21004ff7650f2103cfe7650f21004fd7650f2103cfc7650f21006bf6450f2101ebc6450f21005f77150f21015f47150f211b4fd76d4b2103e7f65d4b2103e7c65d4b2103f6e52d4b21015f471d4b211e4ff7654b2103e7f6554b2103e7c6554b21005bf7454b210c5bc7454b21015f47154b211b7e62154b2138cff7650b2103ebf6450b2103ebc6450b21134fd76ccb210c5be74ccb21005bd74ccb2103edf63ccb2103edc63ccb21164ff764cb2103edf634cb2103edc634cb21005f576d4721006f576d4721015f675d47210177675d4721006f765d47210077665d4721006f565d47210077565d47210067565d4721007e672d4721005f572d4721007e572d4721005e572d4721016f662d4721017e662d47210077752d47210077552d4721005f570d472100cff765832103ef86058321004ff75583210a4fc7558321004ff745832101cfe745832101cfc7458321004ff735832106cfc7358321014fc725832103efb205832103ef820583210befa105832101cfe74d9521004fd74d952101cfc74d95210067e54d95210067c54d952106cfe73d9521004fd73d952103cff71d95211ccfd71d95211ce7f51d95211ce7d51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210067c50d95210067f65995211b5ed72995210a4fe759952101cfe7499521004fd749952101cfc749952106cfe7399521004fd73995211b4fd72995210a6ed72995211e4fd71995210a6f571995211e6f4219952100cfe7099521004fd709952100cfc7099521005bf74595210b5bc74595211e5ef72595210067f7559521004ff7459521006bf7459521004bf745952101cfe745952101cfc7459521006bc745952101cbc7459521004ff735952106cfc73595211e4ff7259521006ef72595211b4ff7159521006f77159521004f77159521004ff705952100cfe705952100cfc70595211ccfe76195210067d65195210a67e751952101cfe7419521004fd741952101cfc74195210067e54195210a67c541952106cfe7319521004fd731952103cff711952119cfd71195210a67f511952119e7d511952119ef4211952100cfe7019521004fd701952100cfc70195210067e50195210a67c501952101cfe76d91210b6be64d
  | 21 => 0xe529972103e7c52997210a67f51997211e67d519972100cfe7099721004fd709972100cfc70997210067e50997210a67c509972103e7c6559721005bf74597210c5bc745972103e7f7559721004ff7459721006bf7459721004bf745972101cfe745972101cfc7459721006bc745972101cbc7459721004ff735972106cfc7359721014fe7259721014fc725972103e7e525972103e7c5259721006f771597211b67f51597211b67d51597211b6f45159721004ff705972100cfe705972100cfc70597210067e50597210067c50597211b6f710597210a4fe751972103e7e751972101cfe7419721004fd741972103cfc741972106cfe7319721004fd731972103cfe721972103eee721972103ef5711972100cfe7019721004fd701972100cfc70197210a4fe75d9321004fd75d932117cfd74d93210c6bc54d932106cfe73d9321004fd73d93210c6bf43d932103cfe72d932103eee72d932103ebf42d932103ef571d932100cfe70d9321004fd70d932100cfc70d932101cff765932103ebc6459321004ff75593210a4fc755932103ebf7459321004ff735932106cfc73593210c6bc4359321014fe7259321014fc725932103ebe425932103ebc425932117ebf415932117ebd4159321004ff705932100cfe705932100cfc70593210c6bf40593210a4ff76d532103cfe76d5321004fd76d532103cfc76d5321006bf64d532101ebc64d53210c73e54d5321004ff765532103cfe7655321004fd765532103cfc7655321005f77155321015f471553210a4fe75d8f21004fd75d8f2101cfe74d8f2103ebe74d8f2101cbe74d8f21004fd74d8f2103ebd74d8f21004bd74d8f2103cfc74d8f2103cfe72d8f2103eee72d8f2103ef571d8f2100cfe70d8f21004fd70d8f2100cfc70d8f2114ef710d8f21134fd7698f210c5be7498f21005bd7498f2103edf6398f210a4fe7598f21004fd7598f2101cfe7498f2106ebe7498f2101cbe7498f21004fd7498f2106ebd7498f21004bd7498f2106cfc7498f21014fe7298f21014fc7298f2103ede3298f2103edc3298f2106edf3198f21166dd3198f2100cfe7098f21004fd7098f2100cfc7098f2103edc6358f21004ff7558f210a4fc7558f21004ff7458f2101cfe7458f2101cfc7458f2103edf7358f21014fe7258f21014fc7258f2103ede3258f2103edc3258f21136df3158f21136dd3158f21004ff7058f2100cfe7058f2100cfc7058f21136f71058f210a4fe7518f2103e7e7518f210047e7518f21004fd7518f2103e7d7518f210047d7518f2101cfe7418f21004fd7418f2103cfc7418f2106cfe7318f2103ede7318f2103cfe7218f2103eee7218f2103ef57118f2100cfe7018f21004fd7018f2100cfc7018f210a4ff76d4f2103cfe76d4f21004fd76d4f2103cfc76d4f210a67e65d4f21
  | 22 => 0xd310a4fe75d8931004fd75d893101cfe74d8931004fd74d893101cfc74d8931166ef21d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d89310d5be7498931005bd7498931006ef62989310057e75189310057d7518931006ed62189310a4fe751893103e7e75189310047e7518931004fd751893103e7d75189310047d751893101cfe7418931004fd741893103cfc741893103edd731893103eef211893111eed211893100cfe7018931004fd701893100cfc7018931006ee201893103eec201893111ef71018931004fe76d4931004fd76d49310a4fc76d49310a67e65d49310067d65d4931006ef62d4931006ec62d4931004fe7694931004fd769493103cfc7694931005de7394931005dd7394931004ff7654931004fe7654931004fc76549310067e65549310067d6554931005bf74549310d5bc7454931005f77154931015f47154931004fe7614931004fd761493103cfc7614931005de7314931005dd7314931006ef621493103eec6214931004fe7690931004fd769093103cfc7690931005de7390931005dd7390931006ef629093103eec6290931004ff7650931004fe7650931004fc7650931006bf645093101ebc6450931006ef6250931006ec625093111cfe76cc9310d5be74cc931005bd74cc93111dde76cc931006de76cc9310079e74cc9310079d74cc93103edc62cc931015de71cc931015dc71cc93106edf61cc931167d710cc931014fe768c9310d5be748c931005bd748c931135dd738c931006ef628c93103eec628c931015f6718c931005f5718c931014fc764c931006ef624c931006ec624c931005f7714c931015f4714c931015dc764c931136dc764c931014dc764c931007cf724c931007cf624c93103edc624c931007cc624c931007d7714c931015de714c931015dc714c931137d4714c931136df614c931137d7104c931164fe760c9310057e750c9310057d750c931165de730c93106f7675cc53106f7575cc531015f673cc531017d673cc531016f763cc531017d763cc53106fd732cc531007d532cc531005f570cc53100cfe76d81310cefa60d81310a4fe75d8131004fd75d813101cfe74d8131004fd74d813101cfc74d8131014fd73d813103cfe72d8131004fd72d81310cef850d81310cefa30d81310cefa10d81310057f75581310057c7558131005bf74581310d5bc7458131005ef7258131005ec72581310cef8605813101cfe74d9721004fd74d972103cfc74d972106cfe73d9721004fd73d972103cfe72d972103eee72d972103ef571d97211cef451d972100cfe70d9721004fd70d972100cfc70d97211cef710d97211b4fd769972103e7f659972101cfe7499721004fd749972101cfc749972106cfe7399721004fd7399721014fe7299721014fc729972103e7
  | 23 => 0x4ff745833101cfe745833101cfc7458331014fc7358331004ff725833103cfc7258331056f6315833106efb305833106ef830583310defa105833101cfe74d9531004fd74d953101cfc74d953103cfe72d9531004fd72d953106cff71d953124cfd71d953124e7f51d953124e7d51d953100cfe70d9531004fd70d953100cfc70d95310067e50d95310067c50d953124ef710d95310067f6599531235dd73995310a4fe759953101cfe7499531004fd749953101cfc7499531234fd73995310a6dd739953103cfe7299531004fd7299531264fd71995310a6f571995312667e51995310a67c519953100cfe7099531004fd709953100cfc7099531005bf74595310d5bc7459531265df7359531005ef7259531005ec7259531005fb70595310cdf870595310067f7559531004ff7459531006bf7459531004bf745953101cfe745953101cfc7459531006bc745953101cbc7459531264ff7359531006df7359531004ff7259531006ef7259531004ef725953103cfc7259531006ec7259531004ec7259531234ff7159531006f771595312367e51595312367c5159531004ff7059531006fb7059531004fb705953100cfe705953100cfc7059531006f8705953100cf87059531236f7105953124cfe76195310067d65195310a67e751953101cfe7419531004fd741953101cfc741953103cfe7219531004fd721953106cff711953121cfd71195310a67f511953121e7d511953100cfe7019531004fd701953100cfc70195310067e50195310a67c501953101cfe76d91310d6be64d91310a4fe75d9131004fd75d91310d6bc54d9131014fd73d91310d6bf43d913103cfe72d9131004fd72d91310d6bf42d913106cff71d913120cfd71d913120ebf41d913120ebd41d913100cfe70d9131004fd70d913100cfc70d9131006be40d91310d6bc40d91310d6bc645913139ddf7359131004ff75591310a4fc755913120cff7459131006bf745913139cff7359131006df7359131004ff725913103cfc72591311fcff7159131006f77159131004ff705913100cfe705913100cfc70591310a4ff76d5131004fe76d5131004fd76d51310a4fc76d5131006bf64d513101ebc64d51310d73e54d5131004ff7655131004fe7655131004fd7655131004fc7655131014fe76d4d31014fc76d4d310067f65d4d310a67c65d4d31015f671d4d31005f571d4d3121cfe7694d310075f5394d3106fd43194d310a4ff7654d31014fe7654d31234fd7654d31014fc7654d310067f6554d310067c6554d31005bf7454d310d5bc7454d31005f77154d31015f47154d31237d43154d31005fb7054d310cdf87054d3124cfe7614d31394fe7690d3101cff7650d31014fe7650d311fcfd7650d31014fc7650d31006bf6450d3101ebc6450d31005f77150d31015f4715
  | 24 => 0xc755933106ebf7459331014fe7359331014fc735933106ebe435933106ebc4359331004ff725933103cfc72593310e6bc42593311febf41593311febd4159331004ff705933100cfe705933100cfc70593310e6bf40593310a4ff76d533106cfe76d5331004fd76d533106cfc76d53310a67e65d53310067d65d5331006bf64d533101ebc64d53310e73e54d5331004ff765533106cfe7655331004fd765533106cfc76553310067e65553310067d6555331234fd76d4f310a67e65d4f310067d65d4f3106f5e53d4f31264ff7654f310067e6554f312367d6554f31005bf7454f310e5bc7454f31237d63154f31005fb7054f310ddf87054f3139cff7650f310067e6550f310067d6550f3106ebf6450f3106ebc6450f310067e6598b310067d6598b310e5be7498b31005bd7498b3106eef6298b310a4fe7598b31004fd7598b3101cfe7498b3103ebe7498b3101cbe7498b31004fd7498b3103ebd7498b31004bd7498b3103cfc7498b31014fe7398b3103ede7398b31006ef4298b3103eec4298b3106eef3298b3103eec3298b3103eef2198b3114eed2198b3100cfe7098b31004fd7098b3100cfc7098b310067e6558b310067d6558b3106eec6258b31004ff7558b310a4fc7558b31004ff7458b3101cfe7458b3101cfc7458b31014fc7358b31006ef4258b31006ec4258b3106eef3258b3106eec3258b31136ef2158b31004ff7058b3100cfe7058b3100cfc7058b310a4ff76d4b3106cfe76d4b31004fd76d4b310a67e65d4b310067d65d4b3103cff7694b3106cfe7694b31004fd7694b310067e6594b310067d6594b3106dde7394b31005dd7394b31004ff7654b31004fd7654b3106cfc7654b310067e6554b310067d6554b31005bf7454b310e5bc7454b31005f77154b31015f47154b3103cff7614b3106cfe7614b31004fd7614b310a67e6514b310067d6514b3106dde7314b31005dd7314b3103cff7690b3106cfe7690b31004fd7690b310067e6590b310067d6590b3101ebe6490b31006bd6490b3106dde7390b31005dd7390b31004ff7650b31004fd7650b3106cfc7650b310067e6550b310067d6550b31006bf6450b3101ebc6450b31005f77150b31015f47150b31015dd76ccb3106edd76ccb31014dd76ccb3106f5e65ccb3106f5d65ccb3106f9e74ccb3106f9d74ccb3103ede62ccb3106fce62ccb3106fcd62ccb31015de71ccb3106fd671ccb3106fd571ccb31015dc71ccb31134fd768cb310067e658cb310067d658cb310e5be748cb31005bd748cb3114cff764cb310067e654cb310067d654cb3114ddf764cb31006df764cb310075e654cb310075d654cb3106fcf724cb3103ede624cb31015de714cb31015dc714cb3100cff76583310067e65583310067d655833106ef86058331004ff75583310a4fc7558331
  | 25 => 0x97310067d72997310a67c72997310067f42997310067c429973106e7f329973106e7c32997310a67f71997312667e71997312667d71997310a67c71997312667f41997312667e41997312667d41997312667c41997312667e31997312667d319973106e7c31997312667f21997312667e21997312667d21997312667c21997310a67f70997310067e70997310067d70997310a67c70997310067f40997310067e40997310067c409973106e7f30997310067e309973106e7c30997310067e20997310067c20997312667f10997312667e10997312667d10997312667c109973106e7c6559731005bf74597310e5bc745973106e7f7559731004ff7459731006bf7459731004bf745973101cfe745973101cfc7459731006bc745973101cbc74597310067e54597310067c5459731014fe7359731014fc735973106e7e535973106e7c5359731004ff725973103cfc72597312367f51597312367d5159731004ff705973100cfe705973100cfc70597310067e50597310067c505973106d7f76597310067f76597310073f74597310073c745973106e7f64597310067e645973106e7c645973106e7f625973106e7c62597312375e315973106f76315973106f5c315973106e7f60597310067e605973106e7c60597310067f74597310063f74597310067e74597310067d74597310067c74597310063c745973106e7e735973106e7c73597310067f435973106e7e435973106e7c43597310067f72597310067e72597310067d72597310067c72597310067f42597310067c425973106e7f325973106e7c32597312367f71597312367e71597312367d71597312367c71597312367f41597312367e41597312367d41597312367c415973106e7f31597312367e31597312367d315973106e7c31597312367f21597312367e21597312367d21597312367c21597310067f70597310067e70597310067d70597310067c70597310067f40597310067e40597310067c405973106e7f30597310067e305973106e7c30597310067e20597310067c20597312367f10597312367e10597312367d10597312367c10597310a4fe751973106e7e75197312647e751973101cfe7419731004fd741973106cfc741973106cfe731973106ede731973103cfe7219731004fd721973106ef5711973100cfe7019731004fd701973100cfc70197310a4fe75d933106e7e75d93310047e75d9331004fd75d933106e7d75d93310047d75d93311fcfd74d93310e6bc54d933106cfe73d933106ede73d933106ebf43d933103cfe72d933106eee72d9331004ee72d9331004fd72d933106eed72d9331004ed72d93310e6bf42d933106ef571d933100cfe70d9331004fd70d933100cfc70d933101cff76593310067e65593310067d655933106ebc6459331004ff75593310a4f
  | 26 => 0x3a6bf4318941006bd431894103ebf421894103eee42189413a6ed421894103cff711894101cfd711894103eef2118941386ed211894100cfe7018941004fd701894100cfc7018941006ee201894103eec2018941004fe76d4941004fd76d49410a4fc76d494101dbc74d4941006ef62d4941006ec62d4941004fe7694941004fd769494103cfc76949410067f65949410067c659494101dbe7494941005bd7494941004ff7654941004fe7654941004fc7654941005bf745494101dbc7454941005f77154941015f47154941004fe7614941004fd761494103cfc76149410067f65149410a67c651494101dbe7414941005bd7414941006ef621494103eec6214941015bc765094117ebc7650941014bc7650941005be7550941005bc7550941005bf7350941006bc635094101dbf725094101faf7250941007af625094103ebc6250941007ac6250941006ac6250941007b77150941015be7150941015bc715094117fb47150941015b4715094101ebf615094101fb76150941004fe76cc941004fd76cc94106cfc76cc94101dbe74cc941005bd74cc941004fe768c941004fd768c94103cfc768c94101dbe748c941005bd748c941006ef628c94103eec628c941004ff764c941004fe764c941004fc764c94101dbe744c941005bd744c941006ef624c941006ec624c941004fe760c941004fd760c94103cfc760c9410057e750c9410057d750c94101dbe740c941005bd740c941015f6710c941005f5710c94100cfe76d81410eefa60d81410a4fe75d8141004fd75d8141014fd74d814100cfc74d8141006bf54d8141336bc54d814106cfe73d8141004fd73d8141336bf43d8141006bd43d814103cfe72d8141004fd72d8141336bf42d8141006bd42d814101cfd71d81410eefa40d81410eefa10d81410057f75581410057c7558141005df7358141005dc7358141005ef7258141005ec72581410eef8605814101cfe74d9731004fd74d973106cfc74d973106cfe73d973106ede73d973103cfe72d9731004fd72d973106ef571d973100cfe70d9731004fd70d973100cfc70d9731234fd769973106e7f659973101cfe7499731004fd749973101cfc74997310067e54997310a67c5499731014fe7399731014fc739973106e7e539973106e7c539973103cfe7299731004fd72997310a67f51997312667d519973100cfe7099731004fd709973100cfc70997310067e50997310a67c50997312347d769973106e7f64997310067e649973106e7c649973106e7f629973106e7c62997312675e319973106f76319973106f5c319973106e7f60997310067e609973106e7c60997310a67f74997310067e74997310067d74997310a67c749973106e7e739973106e7c73997310067f439973106e7e439973106e7c43997310a67f72997310067e729
  | 27 => 0xf74595410febc5459541004ff735954106cfc7359541004ff7259541006ef7259541004ef725954103cfc7259541006ec7259541004ec725954127cff7159541006f77159541004ff705954100cfe705954100cfc70595413d4fe76195410067d65195410a4fe75195410a67e7519541014ff7419541014fd74195410a67f54195413ce7d541954106cfe7319541004fd731954103cfe7219541004fd721954101cff711954101cfd71195410a67f51195413c67d511954100cfe7019541004fd701954100cfc70195410067e50195410a67c5019541015be76d514128ebe76d5141014be76d514101dbe75d514101f3e75d5141006bf65d51410073f65d51410063f65d5141006bd65d51410073c65d5141005bd73d5141005bd72d5141015be71d514128fb671d5141015b671d5141007b571d5141015bc71d514101ebf61d514101fb761d51410a4fe75d8d41004fd75d8d41014fd74d8d413bede43d8d413bedd43d8d4103cfe72d8d41004fd72d8d4101cfd71d8d4139edf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d410057e7598d410057d7598d41006df6398d41005ee7298d41005ed7298d410d5f57198d410e5f77158d41006dd6318d410a4fe7518d41004fd7518d41014fd7418d4106ebd7418d41006bf5418d413b6bc5418d4106ebf4318d4106ede4318d413b6dd4318d4103cfe7218d41004fd7218d413b6bf4218d4106cff7118d4101cfd7118d4106edf3118d41396dd3118d4100cfe7018d41004fd7018d4100cfc7018d41006de3018d4106edc3018d41004fe76d4d41004fd76d4d410a4fc76d4d410067f65d4d410a67c65d4d4101dbc74d4d41004fe7694d41004fd7694d4106cfc7694d4101dbe7494d41005bd7494d410075f5394d41015f67194d41005f57194d41004ff7654d41004fe7654d41004fc7654d410067f6554d410067c6554d41005bf7454d4101dbc7454d41005fb7054d410edf87054d41004fe7614d41004fd7614d4106cfc7614d4101dbe7414d41005bd7414d41015bc7650d411febc7650d41014bc7650d41005be7550d41005bc7550d4101dbf7350d4101f9f7350d410079f6350d4106ebc6350d410079c6350d41005bf7250d41007b77150d41015be7150d41015bc7150d411ffb47150d4101ebf6150d4101fb76150d410a4fe75d8941004fd75d8941014fd74d894106cfe73d8941004fd73d89413aeee42d89413aeed42d894101cfd71d894138eef21d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d8941006ef62989410b5f571989410057f75589410057c75589410c5f77158941006ed62189410a4fe7518941004fd7518941014fd741894103ebd7418941006bf54189413a6bc541894106cfe7318941004fd7318941
  | 28 => 0x8951006ec42d89511e6ef21d895100cfe70d8951004fd70d895100cfc70d8951006ef6298951005bf74589510fdbc7458951006ed621895103e7d751895101cfe7418951004fd741895103cfc741895106cfe7318951004fd7318951006ef421895103eec421895119ef4511895103eef211895119eed211895100cfe7018951004fd701895100cfc701895119ef7101895119cfe76d495119d7e76d49510067e76d49510067f63d495103e7c62d49510157e71d49510157c71d49510a67f61d49511de7e60d49511de7c60d49511e77710d4951014fe76949511b57d7594951006ef629495103eec62949510076f5294951015f67194951005f571949511cf745194951014fc7654951005bf74549510fdbc7454951006ef6254951006ec6254951005f77154951015f471549510157c76549511b67c76549510147c76549510073f74549510073c74549510067f63549510076f72549510076f625495103e7c62549510076c62549510077771549510157e71549510157c71549511b77471549510157471549511b67f61549511ae7e60549511ae7c60549511b77710549511e4fe76149511e57e75149510a7745114951004fe7690951004fd769095103cfc76909510057e75909510057d7590951006bf649095101ebc6490951004ff7650951004fe7650951004fc7650951004fe76cc951004fd76cc95106cfc76cc9510fdbe74cc951005bd74cc951006ef62cc951006ec62cc951004fe768c951004fd768c95103cfc768c9510057e758c9510057d758c9510fdbe748c951005bd748c951004ff764c951004fe764c951004fc764c951004fe760c951004fd760c95103cfc760c9510057e750c9510057d750c951006ef620c95103eec620c951015f675d45510177675d4551016f765d45510177765d45510167765d4551006f462d45510a77752d45510077552d4551005f570d455100cfe76d81510f6fa60d8151014fd75d815101cfe74d8151004fd74d815101cfc74d815106cfe73d8151004fd73d815103cfe72d8151004fd72d81510f6fa50d81510f6f830d81510f6fa10d81510f6f86058151014ff74d9541014fd74d95413d6bd74d95413de7f54d95413de7d54d95413debc54d954106cfe73d9541004fd73d954103cfe72d9541004fd72d954101cff71d954101cfd71d95413d67f51d95413d67d51d954100cfe70d9541004fd70d954100cfc70d95410067e50d95410067c50d954127cfd76995410067f659954127dbd74995410fdf571995410a4fe759954127cfd74995410a6bd749954106cfe7399541004fd739954103cfe7299541004fd729954128cfd71995410a6f5719954100cfe7099541004fd709954100cfc709954128dbf7459541005ef7259541005ec725954110df771595410067f755954128cff7459541006b
  | 29 => 0xa76f5294b51015f47194b511cf765194b511ccff7654b51005bf7454b5110dbc7454b51015f47154b511b7765154b511cd7f7654b510067f7654b510073f7454b510073c7454b510067d6354b510a76f7254b5103e7e6254b51007777154b510157e7154b510157c7154b511b7747154b51015747154b511b7742154b511ae7e6054b511ae7c6054b5103cff7690b510a4fe7690b51004fd7690b510a57e7590b510057d7590b5118f765190b51004ff7650b51004fd7650b510a4fc7650b51005f77150b51015f47150b5117f765150b5106cff76ccb510a4fe76ccb51004fd76ccb5110dbe74ccb51005bd74ccb51015f671ccb51005f571ccb511677651ccb5103cff768cb510a4fe768cb51004fd768cb510a57e758cb510057d758cb5110dbe748cb51005bd748cb5114f76518cb51004ff764cb51004fd764cb510a4fc764cb51005f7714cb51015f4714cb5113776514cb5103cff760cb510a4fe760cb51004fd760cb510a57e750cb510057d750cb5111f76510cb5100cff76583510877651583510a6f86058351014fc7558351004ff745835101cfe745835101cfc7458351004ff735835106cfc7358351004ff725835103cfc7258351086f65158351086f421583510a6fb50583510a6f85058351106fa105835101cfe76d91510febe64d9151014fd75d91510febe54d915106cfe73d9151004fd73d91510febc43d915103cfe72d9151004fd72d91510febc42d915128ebf41d915100cfe70d9151004fd70d915100cfc70d91510febf40d91510febc6459151005ef7259151005ec72591513c4fe76d515101ebe64d51510ff3e54d5151014fc7655151006bf645515101ebc64551510ff3c5455151005f77155151015f4715515101cfe74d8d51004fd74d8d5101cfc74d8d5103cfe72d8d51004fd72d8d512667e51d8d512667c51d8d51266df31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d51266f710d8d51006df6398d51005bf7458d510fdbc7458d51005ef7258d51005ec7258d51005fb7058d510f5f87058d51006dd6318d5101cfe7418d51004fd7418d5106cfc7418d5103cfe7218d51004fd7218d5106edf3118d5121edd3118d5100cfe7018d51004fd7018d5100cfc7018d5121cfe76d4d512667f65d4d51014fe7694d51006df6394d5106edc6394d510075f5394d51015f67194d51005f57194d51014fc7654d512367f6554d51005bf7454d510fdbc7454d51006df6354d51006dc6354d51005f77154d51015f47154d51005fb7054d510f5f87054d51264fe7614d51004fe7690d51004fd7690d5106cfc7690d51006bf6490d5101ebc6490d51004ff7650d51004fe7650d51004fc7650d510057f7550d510057c7550d5101cfe74d8951004fd74d895101cfc74d895106cfe73d8951004fd73d8951006ef42d
  | 30 => 0xf764c83206f6e654c83206f6d654c83203def734c83203fcf734c83206eee634c83206fce634c83206fce534c832007cd534c832014ff76584320067e65584320067d655843203ef46158432004ff75584320a4fc7558432004ff745843201cfe745843201cfc7458432006df3258432006dd325843211ef6415843206ef7315843206ef4315843203ef7215843203ef42158432004ff705843200cfe705843200cfc705843211ef7105843200cff76580320067e65580320067d655803203ef86058032004ff75580320a4fc7558032004ff745803201cfe745803201cfc7458032006ee3258032006ed3258032004ff7158032014fe7158032014fc7158032116fa405803206efb305803206ef8305803203efb205803203ef82058032116fa105803201cff76593510a6bc645935127f765159351014fc75593510a6bf54593510a6bc5459351004ff735935106cfc7359351004ff725935103cfc725935127ebf4159351004ff705935100cfe705935100cfc70593513d4ff76553510a73c545535127f7651553510a6df6398f5124f765198f51014fe7598f5101cfe7498f51004fd7498f5106cfc7498f510a6df5398f5106edc5398f5103cfe7298f51004fd7298f5106edf3198f5124edd3198f5100cfe7098f51004fd7098f5100cfc7098f510a6dc6358f51237765158f51005fb7058f51105f87058f51014fc7558f51004ff7458f5101cfe7458f5101cfc7458f510a6df5358f510a6dc5358f51004ff7258f5103cfc7258f512367e5158f512367c5158f51236df3158f51004ff7058f51006fb7058f51004fb7058f5100cfe7058f5100cfc7058f51006f87058f5100cf87058f51234fd7694f510a75f5394f5124f765194f5124cff7654f512367e6554f51005bf7454f5110dbc7454f51237765154f51005fb7054f51105f87054f5106cff7690f510a4fe7690f51004fd7690f5120f765190f51004ff7650f51004fd7650f510a4fc7650f510057f7550f510a57c7550f511ff765150f510a6ef6298b511cf765198b51014fe7598b5103e7e7598b5101cfe7498b51004fd7498b5103cfc7498b5106cfe7398b51004fd7398b510a6ef5298b5103eec5298b5103eef2198b511ceed2198b5100cfe7098b51004fd7098b5100cfc7098b510a6ec6258b511b7765158b51014fc7558b51004ff7458b5101cfe7458b5101cfc7458b51004ff7358b5106cfc7358b510a6ef5258b510a6ec5258b51006f77158b511b6ef2158b511b6f42158b51004ff7058b5100cfe7058b5100cfc7058b510157d76d4b510a67d76d4b510147d76d4b510067d63d4b5103e7e62d4b510a76e62d4b510a76d62d4b510157e71d4b510a77671d4b510157671d4b510a77571d4b510157c71d4b511e77421d4b511de7e60d4b510a67c60d4b511b4fd7694b51
  | 31 => 0x94320067e40594320067c405943206e7f30594320067e305943206e7c305943203e7f20594320067e205943203e7c20594320067f10594320067e10594320067c10594320a4fe751943203e7e75194320047e751943201cfe7419432004fd741943203cfc741943206cfe731943203ede731943203cfe721943203eee7219432014fe7119432004fd7119432014fc711943200cfe7019432004fd701943200cfc70194320a4fe75d903203e7e75d90320047e75d9032004fd75d903203e7d75d90320047d75d9032124fd74d9032126bc54d903206cfe73d903203ede73d903206ebf43d903203cfe72d903203eee72d903203ebf42d9032014fe71d9032004fd71d9032014fc71d903200cfe70d9032004fd70d903200cfc70d903201cff76590320067e65590320067d655903203ebc6459032004ff75590320a4fc755903203cff745903203ebf745903206cfc735903206ebe435903206ebc435903203cfc725903203ebe425903203ebc4259032004ff7159032014fe7159032014fc7159032126bf4159032004ff705903200cfe705903200cfc7059032126bf40590320a4ff76d503203cfe76d5032004fd76d503203cfc76d50320a67e65d50320067d65d5032006bf64d503201ebc64d50321273e54d5032004ff765503203cfe7655032004fd765503203cfc76550320067e65550320067d655503206cff7598c320a4fe7598c32004fd7598c3206cfc7598c3206cff7498c3201cfe7498c3206ebe7498c3201cbe7498c3216cfd7498c3206ebd7498c32004bd7498c3206cfc7498c32014fe7198c3200cfe7098c32004fd76d4c320a67e65d4c320067d65d4c3206f5e53d4c32004ff7654c320067e6554c320067d6554c32005bf7454c32125bc7454c32005fb7054c32115f87054c3216cff7650c320067e6550c320067d6550c3206ebf6450c3206ebc6450c3203cff75988320a4fe7598832004fd759883203cfc759883203cff749883201cfe749883203ebe749883201cbe7498832154fd749883203ebd7498832004bd749883203cfc7498832014fe719883200cfe7098832004fd76d48320a67e65d48320067d65d4832004ff76548320067e65548320067d6554832005bf7454832125bc7454832005f7715483211df47154832154ff76508320067e65508320067d655083203ebf645083203ebc645083203f5e65cc83203f5d65cc83206f9e74cc83206f9d74cc83203ddd72cc83203ede62cc83203f6e658c83203f6d658c83203fae748c83203fad748c83206ded738c83206eee638c83203fce638c832004ff764c8320067e654c8320067d654c83203ddf764c832006df764c832004df764c83203f5e654c83203f5d654c83203ddf724c83203ede624c83203fce524c832007cd524c83206def764c832006ef764c832004e
  | 32 => 0x4fd74d943203cfc74d943206cfe73d943203ede73d943203cfe72d943203eee72d9432014fe71d9432004fd71d9432014fc71d943200cfe70d9432004fd70d943200cfc70d9432004fd769943203e7f659943203cfe759943201cfe7499432004fd749943201cfc74994320067e54994320a67c549943206cfe739943206e7e539943206e7c539943203cfe729943203e7e529943203e7c5299432014fe7199432004fd7199432014fc71994320067e51994320a67c519943200cfe7099432004fd709943200cfc70994320067e50994320a67c50994320047d769943203e7f64994320067e649943203e7c649943203e7f61994320067e619943203e7c619943203e7f60994320067e609943203e7c60994320a67f74994320067e74994320067d74994320a67c749943206e7e739943206e7c73994320067f439943206e7e439943206e7c439943203e7e729943203e7c72994320067f429943203e7e429943203e7c429943206e7f329943203e7e32994320a67f71994320067e71994320067d71994320a67c71994320067f41994320067e41994320067c419943206e7f31994320067e319943206e7c319943203e7f21994320067e219943203e7c21994320a67f70994320067e70994320067d70994320a67c70994320067f40994320067e40994320067c409943206e7f30994320067e309943206e7c309943203e7f20994320067e209943203e7c20994320067f10994320067e10994320067c109943203e7c6559432005bf7459432125bc745943203cff755943203e7f7559432004ff7459432006bf7459432004bf745943201cfe745943201cfc7459432006bc745943201cbc74594320067e54594320067c545943206cfc735943206e7e535943206e7c535943203cfc725943203e7e525943203e7c5259432004ff7159432014fe7159432014fc71594320067e51594320067c5159432004ff705943200cfe705943200cfc70594320067e50594320067c505943203d7f76594320067f76594320073f74594320073c745943203e7f64594320067e645943203e7c645943203e7f61594320067e615943203e7c615943203e7f60594320067e605943203e7c60594320067f74594320063f74594320067e74594320067d74594320067c74594320063c745943206e7e735943206e7c73594320067f435943206e7e435943206e7c435943203e7e725943203e7c72594320067f425943203e7e425943203e7c425943206e7f325943203e7e325943203e7c32594320067f71594320067e71594320067d71594320067c71594320067f41594320067e41594320067c415943206e7f31594320067e315943206e7c315943203e7f21594320067e215943203e7c21594320067f70594320067e70594320067d70594320067c70594320067f405
  | 33 => 0xc711953200cfe7019532004fd701953200cfc701953201cfe76d913213ebe64d91320a4fe75d9132004fd75d913213ebc54d913213cfd73d913213ebf43d913213cfd72d913213ebf42d9132014fe71d9132004fd71d9132014fc71d913200cfe70d9132004fd70d913200cfc70d91320057f75591320057c755913213ebc6459132005f77159132135f47159132005fb705913212df87059132004ff75591320067f75591320047f75591320a4fc75591320067c75591320047c755913213cff7459132006bf7459132154ff7359132006df735913213ebc435913216cff7259132006ef725913213ebc4259132004ff7159132006f77159132004f77159132014fe7159132014fc7159132006f47159132014f4715913213ebf4159132004ff7059132006fb7059132004fb705913200cfe705913200cfc7059132006f8705913200cf8705913213ebf40591320a4ff76d5132004fe76d5132004fd76d51320a4fc76d5132006bf64d513201ebc64d513213f3e54d5132005de73d5132005dd73d5132005ee72d5132005ed72d5132004ff7655132004fe7655132004fd7655132004fc7655132004fe76d4d320067f65d4d320a67c65d4d32005ee72d4d32005ed72d4d32004fe7694d320075f5394d32004fc7654d320067f6554d320067c6554d32005bf7454d3213dbc7454d32005ef7254d32005ec7254d32005fb7054d3212df87054d32004fe7614d32154fe7690d3201ebe6490d32006bd6490d3201cfc7650d32006bf6450d3201ebc6450d32005ef7250d32005ec7250d32004fe76d49320067f65d49320a67c65d4932005de73d4932005dd73d4932004fe76949320076f52949320a4ff7654932004fd7654932004fc76549320067f65549320067c6554932005bf745493213dbc7454932005df7354932005dc7354932005f77154932135f47154932004fe761493216cfe769093201ebe6490932006bd649093201cff765093213cfd765093201cfc7650932006bf645093201ebc6450932005df7350932005dc735093213dbe74cc932005bd74cc93206fae74cc93206fad74cc932005ed70cc93213dbe748c932005bd748c93203f9e748c93203f9d748c932007cf628c932005dd718c932014fe76d8532136f661d85320a4fe75d8532004fd75d853201cfe74d8532004fd74d853201cfc74d8532136f451d8532006f741d8532136f441d8532136f631d8532136f621d853200cfe70d8532004fd70d853200cfc70d8532136f710d8532136f4615853200cfe76d813212efa60d81320a4fe75d8132004fd75d813201cfe74d8132004fd74d813201cfc74d8132014fe71d8132004fd71d8132014fc71d813212ef850d8132006fb40d813212ef840d813212efa30d813212efa20d813212efa10d813212ef8605813201cfe74d9432
  | 34 => 0x5232004fd765523203cfc765523201ebe6455232006bd64552320a67e65d4e320067d65d4e3226ebe64d4e32006bd64d4e3203dee72d4e32005ed72d4e32256be6494e32006bd6494e320075f5394e320067e6554e320067d6554e32005bf7454e32155bc7454e3223ebe6454e32006bd6454e32005ef7254e3203dec7254e32005fb7054e32145f87054e32226be6414e32006bd6414e3213cfd7690e3201ebe6490e32006bd6490e3201cff7650e3201ebe6450e32006bd6450e32005ef7250e3203dec7250e3203cfc7498a3203e7f65d4a3203e7c65d4a321eebe64d4a32006bd64d4a3203f6e52d4a3203e7f6554a3203e7c6554a32005bf7454a32155bc7454a321bebe6454a32006bd6454a32005f77154a3214df47154a32124ff7650a3201ebe6450a32006bd6450a32155be74cca32005bd74cca3216ebe64cca32006bd64cca3203ddd76cca32006dd76cca320079e74cca320079d74cca3203f9e64cca3203f9d64cca3203fce52cca32007cd52cca32005ed76cca3206eed76cca3206fae74cca3206fad74cca32007ae64cca32007ad64cca3206fce53cca32007cd53cca32005ed70cca32006be6458632006bd645863203ef46158632004ff75586320a4fc7558632004ff745863201cfe745863201cfc7458632006df325863214ef6315863203ef7215863203ef42158632004ff705863200cfe705863200cfc7058632006be6458232006bd645823203ef86058232004ff75582320a4fc7558232004ff745823201cfe745823201cfc7458232004ff7158232014fe7158232014fc7158232146f85058232146fa305823203efb205823203ef82058232146fa105823201cfe74d9532004fd74d953201cfc74d95320067e54d95320067c54d9532014fe71d9532004fd71d9532014fc71d953200cfe70d9532004fd70d953200cfc70d95320067f65995320a4fe759953201cfe7499532004fd749953201cfc7499532004fd73995320a6dd7399532004fd72995320a6ed7299532014fe7199532004fd7199532014fc719953200cfe7099532004fd709953200cfc7099532005bf745953213dbc7459532005f77159532135f47159532005fb705953212df870595320067f7559532004ff7459532006bf7459532004bf745953201cfe745953201cfc7459532006bc745953201cbc7459532004ff7359532006df7359532004ff7259532006ef7259532004ff7159532006f77159532004f77159532014fe7159532014fc7159532006f47159532014f47159532004ff7059532006fb7059532004fb705953200cfe705953200cfc7059532006f8705953200cf87059532004fe76195320067d65195320a67e751953201cfe7419532004fd741953201cfc74195320067e54195320a67c5419532014fe7119532004fd7119532014f
  | 35 => 0x14fe7158332014fc715833206efb305833206ef8305833215efa205833201cfe74d963203ebe74d963201cbe74d9632004fd74d963203ebd74d9632004bd74d963203cfc74d963203edd73d963203eee72d9632014fe71d9632004fd71d9632014fc71d963200cfe70d963203efa70d963200cfa70d9632004fd70d963203ef970d9632004f970d963200cfc70d963203e7f659963201cfe7499632004fd749963201cfc749963203e7e529963203e7c5299632014fe7199632004fd7199632014fc719963200cfe7099632004fd709963200cfc70996320067e50996320a67c509963203e7c655963203e7f7559632004ff745963201cfe745963201cfc745963203e7e525963203e7c5259632004ff7159632014fe7159632014fc7159632004ff705963200cfe705963200cfc70596320067e50596320067c505963203e7e751963201cfe741963203ebe741963201cbe7419632004fd741963203ebd7419632004bd741963203cfc741963203edd731963203eee7219632014fe7119632004fd7119632014fc711963200cfe7019632004fd701963200cfc70196320a4fe75d9232004fd75d923203edd73d923203eee72d9232014fe71d9232004fd71d9232014fc71d923200cfe70d9232004fd70d923200cfc70d923203ebf6599232006be6599232006bd659923203ebc659923203ebe629923203ebf6199232006be619923203ebc619923203ebf6099232006be609923203ebc609923203ebc6459232004ff75592320a4fc755923203ebf7459232156be5459232156bc5459232156bf435923203ebe425923203ebc4259232004ff7159232014fe7159232014fc7159232156bf4159232006be4159232156bc4159232004ff705923200cfe705923200cfc7059232156bf4059232006be4059232156bc4059232156bf765923203ebf6559232006be6559232006bd655923203ebc655923203ebf6159232006be615923203ebc615923203ebf6059232006be605923203ebc6059232006bf7559232006be7559232006bd7559232006bc7559232006bf7359232006bd7359232156bc7359232156bf725923203ebe725923203ebc725923203ebe525923203ebc525923203ebc3259232006bf7159232006be7159232006bd7159232006bc7159232006be5159232006bc5159232006be3159232006bc315923203ebf2159232006be215923203ebc2159232006bf7059232006be7059232006bd7059232006bc7059232006be5059232006bc5059232006be3059232006bc305923203ebf2059232006be205923203ebc2059232006bf1059232006be1059232006bc10592320a4ff76d523203cfe76d5232004fd76d523203cfc76d523201ebe64d5232006bd64d52321573e54d523203dee72d5232005ed72d5232004ff765523203cfe765
  | 36 => 0xe71d9332004fd71d9332014fc71d933200cfe70d9332004fd70d933200cfc70d933206ebf6599332006be6599332006bd659933206ebc659933206ebe639933206ebf6199332006be619933206ebc619933206ebf6099332006be609933206ebc609933206ebc6459332004ff75593320a4fc755933206ebf745933216ebe545933216ebc545933206ebe435933206ebc435933216ebf4259332004ff7159332014fe7159332014fc715933216ebf4159332006be415933216ebc4159332004ff705933200cfe705933200cfc705933216ebf4059332006be405933216ebc405933216ebf765933206ebf6559332006be6559332006bd655933206ebc655933206ebf6159332006be615933206ebc615933206ebf6059332006be605933206ebc6059332006bf7559332006be7559332006bd7559332006bc755933216ebf735933206ebe735933206ebc735933206ebe535933206ebc5359332006bf7259332006bd725933216ebc725933206ebc3259332006bf7159332006be7159332006bd7159332006bc7159332006be5159332006bc515933206ebf3159332006be315933206ebc3159332006be2159332006bc2159332006bf7059332006be7059332006bd7059332006bc7059332006be5059332006bc505933206ebf3059332006be305933206ebc3059332006be2059332006bc2059332006bf1059332006be1059332006bc10593320a4ff76d533206cfe76d5332004fd76d533206cfc76d533201ebe64d5332006bd64d533216f3e54d533206dde73d5332005dd73d5332004ff765533206cfe7655332004fd765533206cfc765533201ebe6455332006bd645533206e7f65d4f3206e7c65d4f3226ebe64d4f32006bd64d4f3206f5e53d4f3206e7f6554f3206e7c6554f32005bf7454f3216dbc7454f3223ebe6454f32006bd6454f32005fb7054f3215df87054f32124ff7650f3201ebe6450f32006bd6450f320a67e65d4b320067d65d4b321eebe64d4b32006bd64d4b3206dde73d4b32005dd73d4b321d6be6494b32006bd6494b320067e6554b320067d6554b32005bf7454b3216dbc7454b321bebe6454b32006bd6454b32005df7354b3206ddc7354b32005f77154b32165f47154b321a6be6414b32006bd6414b3213cfd7690b3201ebe6490b32006bd6490b3201cff7650b3201ebe6450b32006bd6450b32005df7350b3206ddc7350b32006be6458732006bd645873206ef46158732004ff75587320a4fc7558732004ff745873201cfe745873201cfc7458732166f4515873206ef7315873206ef43158732166f62158732004ff705873200cfe705873200cfc7058732166f71058732006be6458332006bd645833206ef86058332004ff75583320a4fc7558332004ff745833201cfe745833201cfc7458332004ff7158332
  | 37 => 0x8d42004fe76d4d42004fd76d4d420a4fc76d4d4201dbe74d4d42005bd74d4d42005ee72d4d42005ed72d4d42004fe7694d42004fd7694d4206cfc7694d420067f6594d420067c6594d420075f5394d42004ff7654d42004fe7654d42004fc7654d42005bf7454d4201dbc7454d42005fb7054d42175f87054d42004fe7614d42004fd7614d4206cfc7614d420067f6514d420a67c6514d42006be6590d42006bc6590d4201dbe7390d4201f9e7390d42006bf6390d420079f6390d420079c6390d4203dbe7290d42007ae7290d42007ad7290d4201ebf6290d4201faf6290d42005bd7190d42005bd7090d4201cfe76d494201cfc76d49420067f65d49420a67c65d494201dbe74d4942005bd74d49421a4fe76949420076f529494203fac42949420a4ff765494201cfe76549421bcfd765494201cfc76549420067f65549420067c6554942005bf745494201dbc74549421bfac4254942005f7715494217df471549421d4fe7614942006be6590942006bc6590942005be7390942006bf639094203dbe729094203fae729094203ebf629094201faf6290942005bd7190942005bd7090942014fe76d854217ef661d85420a4fe75d8542004fd75d854206cfe73d8542004fd73d854201cfd72d854217ef451d854217ef641d854217ef431d854217ef621d854200cfe70d8542004fd70d854200cfc70d854217ef710d85420057f75585420057c755854217ef4615854200cfe76d8142176fa60d81420a4fe75d8142004fd75d814206cfe73d8142004fd73d814201cfd72d8142014fe71d8142004fd71d8142014fc71d8142176fa40d8142176f830d8142176fa20d8142176f8605814201cfe74d973206ebe74d973201cbe74d9732004fd74d973206ebd74d9732004bd74d973206cfc74d973206ede73d973206eed72d9732014fe71d973206ef671d9732014f671d9732004fd71d973206ef571d9732004f571d9732014fc71d973200cfe70d9732004fd70d973200cfc70d973206e7f659973201cfe7499732004fd749973201cfc749973206e7e539973206e7c5399732014fe7199732004fd7199732014fc71997320067e51997320a67c519973200cfe7099732004fd709973200cfc709973206e7c655973206e7f7559732004ff745973201cfe745973201cfc745973206e7e535973206e7c5359732004ff7159732014fe7159732014fc71597320067e51597320067c5159732004ff705973200cfe705973200cfc705973206e7e751973201cfe741973206ebe741973201cbe7419732004fd741973206ebd7419732004bd741973206cfc741973206ede731973206eed7219732014fe7119732004fd7119732014fc711973200cfe7019732004fd701973200cfc70197320a4fe75d9332004fd75d933206ede73d933206eed72d9332014f
  | 38 => 0x3cfe7614e42004fd7614e4201dbe7414e42005bd7414e42005be7550e42005bc7550e4201dbf7350e4201f9f7350e4206ebe6350e420079e6350e420079d6350e42005bf7250e42007af7250e42007ac7250e4201ebe6250e4201fae6250e421bcfd76d4a4201dbc74d4a4203f6e52d4a421ecff7654a42005bf7454a4201dbc7454a421bfaf4254a42005f77154a4218df47154a42014ff765864203ef46158642004ff75586420a4fc7558642006bf54586420b6bc5458642004ff735864206cfc73586420b6bf4358642006bd435864203cfc72586420b6bf425864218ef6415864203ef7215864203ef42158642004ff705864200cfe705864200cfc705864200cff765824203ef86058242004ff75582420a4fc7558242006bf5458242036bc5458242004ff735824206cfc7358242036bf4358242006bd435824203cfc7258242036bf4258242004ff7158242014fe7158242014fc7158242186fa405824203efb205824203ef82058242186fa105824203cff74d95421d4fd74d95421d67f54d95421d67d54d954206cfe73d9542004fd73d9542014fe71d9542004fd71d9542014fc71d95420067e51d95420067c51d954200cfe70d9542004fd70d954200cfc70d95420067f65995421bded72995420a4fe75995421ecfd74995420a6bd749954206cfe7399542004fd73995421eebc43995421bcfd72995420a6ed72995421eebc4299542014fe7199542004fd7199542014fc71995421eebf419954200cfe7099542004fd709954200cfc70995421eebf40995421edef7259542005f7715954217df471595420067f75595421bcff7459542006bf7459542004bf7459542004ff735954206cfc73595421ecff7259542006ef7259542004ff7159542006f77159542004f77159542014fe7159542014fc7159542006f47159542014f47159542004ff705954200cfe705954200cfc70595421d4fe76195420067d65195420a67e751954203cff74195421a4fd74195420a67f54195421a67d541954206cfe7319542004fd73195421a6bc43195421a6bc4219542014fe7119542004fd7119542014fc71195420067e51195420a67c51195421a6bf411954200cfe7019542004fd701954200cfc70195421a6bf40195420a4fe75d8d42004fd75d8d42156de43d8d42156dd43d8d42156bc43d8d42156bc42d8d42014fe71d8d42004fd71d8d42014fc71d8d42156bf41d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42156bf40d8d42006df6398d4213ded7298d420057f7558d420057c7558d4216def7258d42005f77158d4217df47158d42005fb7058d42175f87058d42006dd6318d420a4fe7518d42004fd7518d4206ede4318d42126dd4318d42014fe7118d42004fd7118d42014fc7118d4200cfe7018d42004fd7018d4200cfc701
  | 39 => 0xf52584520067d52584520a6f751584520a6f4515845203ef7215845203ef42158452004ff705845200cfe705845200cfc705845219ef7105845200cff765805203ef86058052004ff745805201cfe745805201cfc7458052004ff735805206cfc7358052004ff7158052014fe7158052014fc71580520a6fb50580520a6f8505805203efb205805203ef82058052196fa105805203ebd74d96421d6bc54d964206cfe73d9642004fd73d964203cfe72d964203eee72d9642014fe71d9642004fd71d9642014fc71d964200cfe70d9642004fd70d964200cfc70d96421bcfd769964203e7f65996420a67f54996421ee7d549964206cfe7399642004fd739964203cfe729964203cfc729964203e7e529964203e7c5299642014fe7199642004fd7199642014fc719964200cfe7099642004fd709964200cfc70996420067e50996420a67c509964203e7c655964203e7f7559642006bf74596421be7f54596421be7d54596421bebc5459642004ff735964206cfc735964203cfe725964203cfc725964203e7e525964203e7c5259642004ff7159642014fe7159642014fc7159642004ff705964200cfe705964200cfc70596420067e50596420067c50596420a4fe751964203e7e751964203ebd741964206cfe731964203ede7319642004de7319642004fd731964203edd7319642004dd731964203cfe721964203eee7219642014fe7119642004fd7119642014fc711964200cfe7019642004fd701964200cfc7019642006bd76d524201dbe75d524201f3e75d5242006bf65d52420073e65d5242006bd65d52420073d65d52420063d65d5242005bd73d5242007ae72d5242005bd72d5242007ad72d5242005ad72d524201ebe62d524201fae62d524203edf6398e420a4fe7598e42004fd7598e42006bf5498e4216ebc5498e4206ebf4398e4206ede4398e4216edd4398e4203cfe7298e4216ebf4298e4203ede3298e4203edc3298e42014fe7198e42004fd7198e42014fc7198e4200cfe7098e42004fd7098e4200cfc7098e42006de3098e4206edc3098e4203edc6358e42004ff7558e420a4fc7558e4213ede4358e4213edd4358e4203cfc7258e4203ede3258e4203edc3258e42004ff7158e42014fe7158e42014fc7158e42004ff7058e4200cfe7058e4200cfc7058e42006de3058e42006dc3058e420a4ff76d4e4203cfe76d4e42004fd76d4e420a67e65d4e420067d65d4e4201dbc74d4e4203dee72d4e42005ed72d4e4206cff7694e4203cfe7694e42004fd7694e4201dbe7494e42005bd7494e4206ede6394e42006dd6394e420075f5394e42004ff7654e42004fd7654e4203cfc7654e420067e6554e420067d6554e42005bf7454e4201dbc7454e42006de6354e42006dd6354e42005fb7054e42185f87054e4206cff7614e42
  | 40 => 0x8552006b46418552006f76318552006f66318552006f56318552006f463185520077753185520077553185521e6f76218552007e752185520077652185521b7f270185521b7f17018552006f66018552006f4601855200776501855200774501855200cfe76d8152006bf64d8152006bc64d8152006f761d8152006f461d81521aefa60d81521af7a50d815201cfe74d8152004fd74d815201cfc74d815206cfe73d8152004fd73d81520067f53d81520067d53d8152014fe71d8152004fd71d8152014fc71d81521ae7e50d81521aefa50d81521ae7a50d81521ae7c50d81521aef830d81521aefa20d8152005bf74581521bdbc7458152006bf6458152006bc6458152005df7358152005dc7358152005f771581521b5f47158152006f76158152006f461581521aef8605815201cfe74994520a67f5399452014fe719945200cfe70994520a67c509945201cff765905203ebc64590520a6bf54590520a6bc5459052004ff735905206cfc73590521a6bc435905203ebe425905203ebc4259052004ff7159052014fe7159052014fc71590521a6bf4159052004ff705905200cfe705905200cfc70590521a6bf40590521ecff76550520a73c545505203edf6398c5201cfe7498c52004fd7498c5206cfc7498c520a6df5398c5206edc5398c52006df4398c5206edc4398c5203ede3298c5203edc3298c52014fe7198c52004fd7198c52014fc7198c5200cfe7098c52004fd7098c5200cfc7098c5203edc6358c52004ff7458c5201cfe7458c5201cfc7458c520a6df5358c520a6dc5358c52006df4358c52006dc4358c5203ede3258c5203edc3258c52004ff7158c52014fe7158c52014fc7158c52004ff7058c5200cfe7058c5200cfc7058c52004fd7694c520a75f5394c52004ff7654c520067e6554c52005bf7454c521a5bc7454c52005fb7054c52195f87054c5206cff7690c5203cfe7690c52004fd7690c5201ebe6490c52006bd6490c52004ff7650c52004fd7650c5203cfc7650c520057f7550c520a57c7550c5201cfe7498852014fe719885200cfe70988520067d63d485203d7d72d485203e7e62d48521de7e60d485203e7c60d48520a5ed75948520a6ee659485203f6e6594852004ff7654852005bf74548521a5bc7454852005f7715485219df4715485203d7f76548520067f76548520047f76548520073f74548520073c74548520067d635485203d7f725485203e7e62548520077771548520077471548521ae7e605485203e7c60548520a5ef7654852006ef7654852004ef765485203def755485203f6f75548520a6ee65548520a76e6554852007af7454852007ac7454852007e77154852007e47154852014ff765845203ef46158452004ff745845201cfe745845201cfc7458452004ff735845206cfc73584520067
  | 41 => 0x5bf7454d521bdbc7454d52006bf6454d5223ebc6454d52006df6354d52006dc6354d52005ef7254d52005ec7254d52236f46154d52005fb7054d521adf87054d520073f7454d520073c7454d520073f6454d520073c6454d520075f7354d520075f6354d5206e7c6354d520075c6354d520076f7254d5203d7c7254d520076c7254d520057f7154d522367e6154d522367c6154d52236746154d520077b7054d521ad7e7054d521ad7c7054d52007787054d521ad787054d52004fe7614d520057e7514d52006bf6414d52226bc6414d5221ef46114d52004fe7690d52004fd7690d5206cfc7690d520057e7590d520057d7590d52006bf6490d5201ebc6490d52005ee7290d52005ed7290d5220ef46190d52004ff7650d52004fe7650d52004fc7650d52006bf6450d5201ebc6450d521fef46150d52006bf64d49521eebc64d4952007af64d4952007ac64d49520a76f53d49520076d53d49523e76e50d49520a76c50d4952006bf64949521d6bc64949520073f64949520073c64949520057d73949520076f62949520057d71949521ad7e709495203d7c7094952014fe76d8552006bf64d8552006bc64d85521b6f661d855201cfe74d8552004fd74d855201cfc74d855206cfe73d8552004fd73d85521b6f651d8552006f741d85521b6f641d85521b6f441d85521b6f631d85521b6f431d85521b6f621d855200cfe70d8552004fd70d855200cfc70d85521b6f710d8552006f610d85521b6f410d85521b5f676d8552014f676d85520077775d8552006f764d8552007b764d8552006b764d8552006f664d8552006f564d8552006f464d8552007b464d8552006b464d8552006f763d8552006f663d8552006f563d8552006f463d85520077753d85520077553d8552007e752d85520077652d8552006f660d8552006f460d85520077650d85520077450d8552006f775d85521b6f675d8552006f774d8552006f674d8552006f574d8552006f474d8552006f754d8552006f654d8552006f554d8552006f454d8552006f773d8552006f673d8552006f573d8552006f473d8552006f753d8552006f653d8552006f553d8552006f453d8552006f743d8552006f643d8552006f543d8552006f443d8552006f772d85521b6f672d8552006f752d8552006f652d8552006f742d8552006f442d8552006f770d8552006f670d8552006f570d8552006f470d8552006f650d8552006f450d8552006f740d8552006f640d8552006f440d8552006f630d8552006f430d8552006f620d8552006f420d8552005bf74585521bdbc7458552006bf6458552006bc64585521b6f46158552005f676185521b6f676185521b77575185521cef76518552006f76418552007b76418552006b76418552006f66418552006f56418552006f46418552007b4641
  | 42 => 0xc73586520067f52586521cef6515865203ef7215865203ef42158652004ff705865200cfe705865200cfc705865203ef86058252004ff745825201cfe745825201cfc7458252004ff735825206cfc7358252004ff7158252014fe7158252014fc71582521c6fa50582521c6fa40582521c6f8305825203efb205825203ef820582521c6fa105825201cfe76d91521bebe64d91521bebe54d915206cfe73d9152004fd73d91521bebf43d91521bebc43d91521bebf42d9152014fe71d9152004fd71d9152014fc71d91521bebf41d9152006be41d91521bebc41d915200cfe70d9152004fd70d915200cfc70d91521bebf40d9152006be40d91521bebc40d91521bdbe76d915201cbe76d9152006be61d9152006bc61d9152006be60d9152006bc60d91520073e50d91520073c50d9152006bf75d91521bebe75d9152006bf73d9152006be73d9152006bd73d9152006bc73d9152006bf72d91521bebe72d9152006bd72d9152006bf71d9152006be71d9152006bd71d9152006bc71d9152006be51d9152006bc51d9152006be31d9152006bc31d9152006be21d9152006bc21d9152006bf70d9152006be70d9152006bd70d9152006bc70d9152006be50d9152006bc50d9152006be30d9152006bc30d9152006be20d9152006bc20d9152006bf10d9152006be10d9152006bc10d91521bebc6459152005f771591521b5f47159152005be76191521bebe7619152006be6119152006bc6119152006be6019152006bc60191520073e50191520073c50191521d4fe76d515201ebc64d51521bf3e54d515228ef461d515201cfc7655152006bf645515201ebc6455152005ef7255152005ec725515227ef46155152006bf64d8d52006bc64d8d5201cfe74d8d52004fd74d8d5201cfc74d8d52014fe71d8d52004fd71d8d52014fc71d8d5200cfe70d8d52004fd70d8d5200cfc70d8d52006de30d8d52006dc30d8d521bdbe7498d52005bd7498d52006bf6498d52006bc6498d52006df6398d521b5f67198d52005f57198d52005bf7458d521bdbc7458d52006bf6458d52006bc6458d52005f77158d521b5f47158d52005fb7058d521adf87058d52006bf6418d52006bc6418d52006dd6318d5201cfe7418d52004fd7418d5206cfc7418d52014fe7118d52004fd7118d52014fc7118d5200cfe7018d52004fd7018d5200cfc7018d52006de3018d5206edc3018d52004fe76d4d52006bf64d4d5226ebc64d4d52266f461d4d520057e76d4d520067e76d4d520073f64d4d520073c64d4d5206e7c63d4d5203d7e72d4d520057d71d4d522667e61d4d522667c61d4d522667461d4d521ad7e70d4d521ad7c70d4d520057d7594d52006bf6494d52256bc6494d52006df6394d5206edc6394d520075f5394d52005ee7294d52005ed7294d5224ef46194d52
  | 43 => 0x4f520a75e63d4f520065e63d4f520a75d63d4f5203d7e72d4f520a76e72d4f520a76d72d4f520057d71d4f522667e61d4f520a67c61d4f521dd7e70d4f520a57c70d4f520a75f5394f52005bf7454f521edbc7454f52005fb7054f521ddf87054f520057f7654f520067f7654f520073f7454f520073c7454f520a75f7354f5206e7e6354f5203d7c7254f520057f7154f522367e6154f522367c6154f520077b7054f521dd7e7054f521dd7c7054f52007787054f521dd787054f5206cff7690f520a4fe7690f52004fd7690f520a57e7590f520057d7590f5201ebc6490f5206ede6390f52006dd6390f52004ff7650f52004fd7650f520a4fc7650f5201ebe6450f52006bd6450f52006de6350f52006dd6350f520a6f46158752004ff745875201cfe745875201cfc7458752004ff735875206cfc73587520a6f751587520a6f451587521e6f62158752004ff705875200cfe705875200cfc70587521e6f710587520a6f860583520a7785058352004ff745835201cfe745835201cfc7458352004ff735835206cfc73583520067f53583520067d5358352004ff7158352014fe7158352014fc71583520a6fb50583521de7e50583521de7c50583520a6f850583521defa20583521defa105835203ebc64592521d6be5459252004ff735925206cfc73592521d6bc435925203ebe425925203ebc4259252004ff7159252014fe7159252014fc71592521d6bf4159252004ff705925200cfe705925200cfc70592521d6bf40592521bcfd76d525201ebc64d52521d73e54d525201cff765525201ebe6455252006bd64552521d73c5455252005ef725525203dec725525203edf6398e5201cfe7498e52004fd7498e5206cfc7498e5203ede3298e5203edc3298e52014fe7198e52004fd7198e52014fc7198e5200cfe7098e52004fd7098e5200cfc7098e5203edc6358e52004ff7458e5201cfe7458e5201cfc7458e5203ede3258e5203edc3258e52004ff7158e52014fe7158e52014fc7158e52004ff7058e5200cfe7058e5200cfc7058e5206ede6394e52006dd6394e520075f5394e5203dee7294e52005ed7294e52005bf7454e521d5bc7454e52006de6354e52006dd6354e52005ef7254e5203dec7254e52005fb7054e521c5f87054e5206cff7690e5203cfe7690e52004fd7690e5201ebe6490e52006bd6490e5203dee7290e52005ed7290e52004ff7650e52004fd7650e5203cfc7650e520057f7550e520057c7550e5203d7d76d4a520067d76d4a520067d63d4a521de7e60d4a5203e7c60d4a523ef6e20d4a5203f6c20d4a52005ed76d4a520a6ed76d4a520a76f54d4a520076d54d4a520a76f53d4a520076d53d4a523ef6e50d4a520a76c50d4a5203ef46158652004ff745865201cfe745865201cfc7458652004ff735865206cf
  | 44 => 0x3cfc7259543004ff7159543014fe7159543014fc7159543004ff7059543006fb7059543004fb705954300cfe705954300cfc7059543006f8705954300cf87059543254fe76195430067d65195430a67e751954306cff7419543224fd74195430a67f54195432267d5419543226bc431954303cfe7219543004fd7219543226bc4219543014fe7119543004fd7119543014fc7119543226bf411954300cfe7019543004fd701954300cfc70195430067e50195430a67c5019543226bf401954301cfe76d4d4301cfc76d4d430067f65d4d430a67c65d4d4301dbe74d4d43005bd74d4d43224fe7694d430075f5394d4306f9c4394d430a4ff7654d4301cfe7654d4323cfd7654d4301cfc7654d430067f6554d430067c6554d43005bf7454d4301dbc7454d4323f9c4354d43005fb7054d431f5f87054d43254fe7614d43006be6590d43006bc6590d4306dbe7390d4306f9e7390d4306ebf6390d4301f9f6390d43005be7290d43005bd7190d43005bd7090d430a4fe75d8943004fd75d8943006be43d894316ebc43d894316eee42d894316ebc42d8943014fe71d8943004fd71d8943014fc71d894316ebf41d894300cfe70d8943004fd70d894300cfc70d894316ebf40d8943006ef62989430057f75589430057c7558943005f771589431fdf47158943005fb70589431f5f87058943006ed62189430a4fe7518943004fd751894303eee4218943126ed4218943014fe7118943004fd7118943014fc711894300cfe7018943004fd701894300cfc7018943014fe76d85431fef661d85430a4fe75d8543004fd75d854301cfd73d854303cfe72d8543004fd72d85431fef641d85431fef631d85431fef421d854300cfe70d8543004fd70d854300cfc70d85431fef4615854300cfe76d81431f6fa60d81430a4fe75d8143004fd75d814301cfd73d814303cfe72d8143004fd72d8143014fe71d8143004fd71d8143014fc71d81431f6f850d81431f6fa40d81431f6fa30d81431f6f820d81431f6fa10d81430057f75581430057c75581431f6f860581430a6bc64593520a6bf54593520a6bc5459352004ff735935206cfc73593521eebf43593521eebf4259352004ff7159352014fe7159352014fc7159352004ff705935200cfe705935200cfc70593521a4ff76553520a6df6398f5201cfe7498f52004fd7498f5206cfc7498f520a6df5398f5206edc5398f52014fe7198f52004fd7198f52014fc7198f5200cfe7098f52004fd7098f5200cfc7098f52005bf7458f521edbc7458f520a6dc6358f52004ff7458f52006bf7458f52004bf7458f5201cfe7458f5201cfc7458f52006bc7458f5201cbc7458f520a6df5358f520a6dc5358f52004ff7158f52014fe7158f52014fc7158f52004ff7058f5200cfe7058f5200cfc7058f5206e7e63d
  | 45 => 0xf545964323e7d545964323ebc545964306cfe735964306cfc735964306e7e535964306e7c5359643004ff725964303cfc7259643004ff7159643014fe7159643014fc71596430067e51596430067c5159643004ff705964300cfe705964300cfc70596430a4fe751964306e7e751964306ebd741964306cfe731964306ede731964303cfe721964306eee7219643004ee7219643004fd721964306eed7219643004ed7219643014fe7119643004fd7119643014fc711964300cfe7019643004fd701964300cfc7019643006bd76d524301dbe75d524301f3e75d5243006bf65d52430073e65d5243006bd65d52430073d65d52430063d65d52430079e73d5243005bd73d52430079d73d52430059d73d524301ebe63d524301f9e63d5243005bd72d524323cfd76d4e4301dbc74d4e4306f5e53d4e4326cff7654e43005bf7454e4301dbc7454e4323f9f4354e43005fb7054e43205f87054e4306eef6298a430a4fe7598a43004fd7598a43006bf5498a43156bc5498a4306cfe7398a43156bf4398a4303ebf4298a4303eee4298a43156ed4298a4306eef3298a4303eec3298a43014fe7198a43004fd7198a43014fc7198a43006ee2198a4303eec2198a4300cfe7098a43004fd7098a4300cfc7098a4306eec6258a43004ff7558a430a4fc7558a4306cfc7358a4313eee4258a4306eef3258a4306eec3258a43004ff7158a43014fe7158a43014fc7158a43006ee2158a43006ec2158a43004ff7058a4300cfe7058a4300cfc7058a43014ff765864306ef46158643004ff75586430a4fc7558643006bf54586430d6bc545864306cfc73586430d6bf4358643004ff725864303cfc72586430d6bf425864320ef6415864306ef7315864306ef43158643004ff705864300cfe705864300cfc705864320ef7105864300cff765824306ef86058243004ff75582430a4fc7558243006bf545824305ebc545824306cfc735824305ebf4358243004ff725824303cfc725824305ebf4258243004ff7158243014fe7158243014fc7158243206fa405824306efb305824306ef8305824306cff74d9543254fd74d95432567f54d95432567d54d954303cfe72d9543004fd72d9543014fe71d9543004fd71d9543014fc71d954300cfe70d9543004fd70d954300cfc70d95430067e50d95430067c50d95430067f659954323ddd73995430a4fe759954326cfd74995430a6bd749954323cfd73995430a6dd739954326ebc439954303cfe7299543004fd729954326ebc4299543014fe7199543004fd7199543014fc719954326ebf419954300cfe7099543004fd709954300cfc709954326ebf409954326ddf7359543005fb70595431f5f870595430067f755954323cff7459543006bf7459543004bf745954326cff7359543006df7359543004ff7259543
  | 46 => 0x8153006fa6218153006f96218153006f8621815322ff2711815322ff17118153006fb6118153006fa6118153006f96118153006f861181530077a511815300778511815301cfe7499453014fe71994530a67c519945300cfe709945301cff765905306ebc64590530a6bf54590530a6bc545905306ebe435905306ebc4359053004ff725905303cfc7259053226bc4259053004ff7159053014fe7159053014fc7159053226bf4159053004ff705905300cfe705905300cfc7059053226bf405905326cff765505301cfe7498c53014fe7198c5300cfe7098c5306d7d73d4c5306e7e63d4c532667e61d4c5306e7c61d4c530a5dd7594c530a6de6594c5306f5e6594c530065e6594c53004ff7654c53005bf7454c53225bc7454c53005fb7054c53215f87054c5306d7f7654c530067f7654c530047f7654c530073f7454c530073c7454c5306d7f7354c5306e7e6354c532367e6154c5306e7c6154c530077b7054c53007787054c530a5df7654c53006df7654c53004df7654c5306ddf7554c5306f5f7554c530a6de6554c530a75e6554c530079f7454c530079c7454c53007db7054c53007d87054c5306eef629885301cfe7498853004fd749885303cfc74988530a6ef529885303eec5298853006ef429885303eec429885306eef329885303eec3298853014fe7198853004fd7198853014fc719885300cfe7098853004fd709885300cfc709885306eec6258853004ff745885301cfe745885301cfc74588530067f53588530067d53588530a6ef52588530a6ec5258853006ef4258853006ec425885306eef325885306eec3258853004ff7158853014fe7158853014fc7158853004ff705885300cfe705885300cfc7058853014ff765845306ef46158453004ff745845301cfe745845301cfc7458453004ff725845303cfc72584530a6f751584530a6f4515845306ef7315845306ef43158453004ff705845300cfe705845300cfc705845321ef7105845300cff765805306ef86058053004ff745805301cfe745805301cfc74580530067f53580530067d5358053004ff725805303cfc7258053004ff7158053014fe7158053014fc71580530a6fb50580530a6f8505805306efb305805306ef83058053216fa105805306ebd74d9643256bc54d964306cfe73d964306ede73d964303cfe72d9643004fd72d9643014fe71d9643004fd71d9643014fc71d964300cfe70d9643004fd70d964300cfc70d964323cfd769964306e7f65996430a67f549964326e7d549964306cfe739964306cfc739964306e7e539964306e7c539964303cfe7299643004fd7299643014fe7199643004fd7199643014fc71996430067e51996430a67c519964300cfe7099643004fd709964300cfc709964306e7c655964306e7f7559643006bf745964323e7
  | 47 => 0x6bf64d8953006bc64d895301cfe74d8953004fd74d895301cfc74d8953014fe71d8953004fd71d8953014fc71d8953006ee21d8953006ec21d895300cfe70d8953004fd70d895300cfc70d895323dbe7498953005bd7498953006bf6498953006bc6498953006ef629895322dfa7098953005f97098953005bf745895323dbc7458953006bf6458953006bc6458953005f77158953235f47158953005fb705895322df87058953006bf6418953006bc6418953006ed621895301cfe7418953004fd741895303cfc7418953014fe7118953004fd7118953014fc7118953006ee211895303eec211895300cfe7018953004fd701895300cfc7018953014fe76d8553006bf64d8553006bc64d8553236f661d85532377651d855301cfe74d8553004fd74d855301cfc74d855303cfe72d8553004fd72d85532367e51d8553236f651d85532367651d85532367c51d8553236f631d8553236f421d855300cfe70d8553004fd70d855300cfc70d8553005bf745855323dbc7458553006bf6458553006bc6458553005ef7258553005ec7258553236f46158553005fb705855322df8705855300cfe76d8153006bf64d8153006bc64d815322efa60d815301cfe74d8153004fd74d815301cfc74d815303cfe72d8153004fd72d8153014fe71d8153004fd71d8153014fc71d815322efa50d8153006fb40d815322efa40d815322ef840d815322efa30d815322efa20d815322ef820d8153006fb10d815322efa10d815322ef810d815322dfa76d815300cfa76d81530077b75d8153006fb64d8153007bb64d8153006bb64d8153006fa64d8153006f964d8153006f864d8153007b864d8153006b864d8153007db53d81530077a53d8153006fb62d8153006fa62d8153006f962d8153006f862d8153006fb61d8153006fa61d8153006f961d8153006f861d81530077a51d81530077851d8153006fb75d815322efa75d8153006fb74d8153006fa74d8153006f974d8153006f874d8153006fb54d8153006fa54d8153006f954d8153006f854d8153006fb73d815322efa73d8153006fb53d8153006fa53d8153006fb43d8153006f843d8153006fb72d8153006fa72d8153006f972d8153006f872d8153006fb42d8153006f842d8153006fb71d8153006fa71d8153006f971d8153006f871d8153006fa51d8153006f851d8153006fb41d8153006fa41d8153006f841d8153006fa31d8153006f831d8153006fa21d8153006f821d8153005bf745815323dbc7458153006bf6458153006bc645815322ef86058153005fa761815322efa761815322f797518153246fb6518153006fb6418153007bb6418153006bb6418153006fa6418153006f96418153006f86418153007b86418153006b8641815325efb6318153007db53181530077a5318153006fb621
  | 48 => 0xc41d4e534075e21d4e534075c21d4e530a75f70d4e533ff5e70d4e530075d70d4e530a75c70d4e5306f5f60d4e533ff5e60d4e5306f5c60d4e5340f5f40d4e533ff5e40d4e533ff5c40d4e533ff5e20d4e533ff5c20d4e534075f10d4e533ff5e10d4e533ff5c10d4e530075f5398a5306eef6298a5301cfe7498a53004fd7498a5303cfc7498a5306eef3298a5303eec3298a53014fe7198a53004fd7198a53014fc7198a5300cfe7098a53004fd7098a5300cfc7098a530075f5358a5306eec6258a53004ff7458a5301cfe7458a5301cfc7458a530067f5358a5306eef3258a5306eec3258a53004ff7158a53014fe7158a53014fc7158a53004ff7058a5300cfe7058a5300cfc7058a530075f535865306ef46158653004ff745865301cfe745865301cfc7458653004ff725865303cfc725865324ef6515865324ef6415865306ef7315865306ef4315865324ef42158653004ff705865300cfe705865300cfc705865324ef710586530075f535825306ef86058253004ff745825301cfe745825301cfc74582530067f5358253004ff725825303cfc7258253004ff7158253014fe7158253014fc7158253246fa505825306efb305825306ef8305825301cfe76d915323ebe64d915323ebe54d915323ebf43d915303cfe72d9153004fd72d915323ebf42d915323ebc42d9153014fe71d9153004fd71d9153014fc71d915323ebf41d9153006be41d915323ebc41d915300cfe70d9153004fd70d915300cfc70d915323ebf40d9153006be40d915323ebc40d915323dbe76d915301cbe76d9153006be61d9153006bc61d91530073e51d91530073c51d9153006be60d9153006bc60d9153006bf75d915323ebe75d9153006bf73d915323ebe73d9153006bd73d9153006bf72d9153006be72d9153006bd72d9153006bc72d9153006bf71d9153006be71d9153006bd71d9153006bc71d9153006be51d9153006bc51d9153006be31d9153006bc31d9153006be21d9153006bc21d9153006bf70d9153006be70d9153006bd70d9153006bc70d9153006be50d9153006bc50d9153006be30d9153006bc30d9153006be20d9153006bc20d9153006bf10d9153006be10d9153006bc10d915323ebc6459153005fb705915322df87059153005be761915323ebe7619153006be6119153006bc61191530073e51191530073c5119153006be6019153006bc6019153254fe76d515301ebc64d515323f3e54d5153286f860d515301cfc7655153006bf645515301ebc6455153005df7355153005dc7355153276f86055153006bf64d4d5326ebc64d4d530079f64d4d530079c64d4d533f75e51d4d530a75c51d4d53006bf6494d53256bc6494d530073f6494d530073c6494d530075f6394d530057d7294d532357e7194d5306d7c7194d530057d7094d53
  | 49 => 0x855427ef641d855427ef421d855400cfe70d8554004fd70d855400cfc70d8554005ef7258554005ec725855427ef4615855400cfe76d8154276fa60d815401cfd75d8154006bf54d815409ebc54d815406cfe73d8154004fd73d815403cfe72d8154004fd72d8154014fe71d8154004fd71d8154014fc71d8154276fa50d8154276fa40d8154276f830d8154005df7358154005dc7358154276f860581540a6bc64593530a6bf54593530a6bc545935326ebf4359353004ff725935303cfc725935326ebf4259353004ff7159353014fe7159353014fc7159353004ff705935300cfe705935300cfc7059353224ff76553530a6ef6298b5301cfe7498b53004fd7498b5303cfc7498b530a6ef5298b5303eec5298b53014fe7198b53004fd7198b53014fc7198b5300cfe7098b53004fd7098b5300cfc7098b53005bf7458b5326dbc7458b530a6ec6258b53004ff7458b53006bf7458b53004bf7458b5301cfe7458b5301cfc7458b53006bc7458b5301cbc7458b530a6ef5258b530a6ec5258b53004ff7158b53014fe7158b53014fc7158b53004ff7058b5300cfe7058b5300cfc7058b530a6f461587530a7745158753004ff745875301cfe745875301cfc7458753004ff725875303cfc72587530a6f751587532667e51587532667c51587530a6f45158753266f63158753004ff705875300cfe705875300cfc7058753266f710587530a6f86058353004ff745835301cfe745835301cfc7458353004ff725835303cfc7258353004ff7158353014fe7158353014fc71583530a6fb50583530a6f8505835325efa305835325efa105835306ebc6459253256be545925306ebe435925306ebc4359253004ff725925303cfc7259253256bc4259253004ff7159253014fe7159253014fc7159253256bf4159253004ff705925300cfe705925300cfc7059253256bf405925323cfd76d525301ebc64d52532573e54d525301cff765525301ebe6455253006bd6455253005df735525306ddc735525306d7d76d4e530067d76d4e5340f5f43d4e5306f5c43d4e532667e61d4e5306e7c61d4e534075e31d4e5306f5c31d4e533ff5e30d4e5306f5c30d4e53005dd76d4e530a6dd76d4e530a75f54d4e5340f5e54d4e530075d54d4e530a75c54d4e534075e51d4e530a75c51d4e533ff5e50d4e530a75c50d4e530075d76d4e530055d76d4e530065d76d4e530a75f74d4e5340f5e74d4e530075d74d4e530a75c74d4e5306f5f64d4e5340f5e64d4e530075d64d4e5306f5c64d4e530a75f72d4e530075e72d4e530075d72d4e530a75c72d4e5306f5f62d4e5306f5c62d4e5340f5f42d4e5340f5c42d4e530a75f71d4e534075e71d4e530075d71d4e530a75c71d4e5306f5f61d4e534075e61d4e5306f5c61d4e5340f5f41d4e534075e41d4e534075
  | 50 => 0x200140060018008000001b2573e5498f540a6df6398f5401cfe7598f540a6df5398f5406edc5398f5406ede4398f54256dd4398f5403cfe7298f54004fd7298f54014fe7198f54004fd7198f54014fc7198f5400cfe7098f54004fd7098f5400cfc7098f5423f3e5458f540a6dc6358f5401cfc7558f540a6df5358f540a6dc5358f5423ede4358f5423ebc4358f54004ff7258f5403cfc7258f5423ebc4258f54004ff7158f54014fe7158f54014fc7158f5423ebf4158f54004ff7058f5400cfe7058f5400cfc7058f5423ebf4058f541d73e5498b540a6ef6298b5401cfe7598b5406cfe7398b54004fd7398b540a6ef5298b5403eec5298b5403eee4298b541d6ed4298b54014fe7198b54004fd7198b54014fc7198b5400cfe7098b54004fd7098b5400cfc7098b541bf3e5458b540a6ec6258b5401cfc7558b54004ff7358b5406cfc7358b541bebc4358b540a6ef5258b540a6ec5258b541beee4258b541bebc4258b54004ff7158b54014fe7158b54014fc7158b541bebf4158b54004ff7058b5400cfe7058b5400cfc7058b541bebf4058b54014ff76587540ff3e54587540a6f4615875401cfc7558754004ff735875406cfc7358754004ff725875403cfc72587540a6f751587540a6f4515875428ef64158754004ff705875400cfe705875400cfc705875428ef7105875400cff765835408f3e54583540a6f8605835401cfc7558354004ff735835406cfc7358354004ff725835403cfc7258354004ff7158354014fe7158354014fc71583540a6fb50583540a6f85058354286fa4058354286fa105835401dbe75d515401f3e75d515401ebf65d515401f3f65d515401e3f65d515426ede43d8d5403cfe72d8d54004fd72d8d54014fe71d8d54004fd71d8d54014fc71d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54006de30d8d54006dc30d8d54006df6398d54005fb7058d54275f87058d54006dd6318d54006bf5418d54226bc5418d5406ede4318d54226dd4318d5403cfe7218d54004fd7218d54014fe7118d54004fd7118d54014fc7118d5400cfe7018d54004fd7018d5400cfc7018d54006de3018d5406edc3018d5406cfe73d8954004fd73d89541eeee42d8954014fe71d8954004fd71d8954014fc71d8954006ee21d8954006ec21d895400cfe70d8954004fd70d895400cfc70d8954006ef6298954005f7715895427df47158954006ed6218954006bf54189541a6bc541895406cfe7318954004fd731895403eee42189541a6ed4218954014fe7118954004fd7118954014fc7118954006ee211895403eec211895400cfe7018954004fd701895400cfc7018954014fe76d855427ef661d855401cfd75d8554006bf54d855410ebc54d855406cfe73d8554004fd73d855403cfe72d8554004fd72d855427ef651d
  | 51 => 0x30004008001000a0068000001800400000010040003001000c000000b004400000040070038001001c000000000200380010030010001c005000000000500000008000000c0000048001000000000200000080000000000500080030004000000000000400020000002007000900100030034004002c0000004010000c007000000000380040008003002c000000c0040000000002000a001800200000030008001000800200040140000018004400300000010004005000400000300060020001001c002000c0010008003000c00800000000010000002800000480000020008000001000000090004000000000000000010008000000000000000010030000005401e0000000000000200380030020009000800b002800400140040034000001c00700340030010000000000700040000004000000400000040090004001000000100000010000001000c008000000500000000010001000c006003000100100020008000001800000180060004001000000200080000004000000c00200080070004000000000000080030000001004800300040050008003001000200040010000001000c0000004003001c0010000002001001500400030038027000800c00040000018002000c000000c005001800000000000000004000800000040030000002000400000240090048003002c00400000020028002001c006001400100040010008007002c0070000000000000700240030000001000400000100000000000000c004002400400000130010000001400200180030000000000000000000000008000000c0000000000000000600000160008002000000600140010004000000c00f002400300040000014000000c00200080000000002000400a00040080000009000c000000400100040000008000000c001000800e0000001001c0000020008000400000240010000002001400200000000000004001400100040020018007000000200000040008006003000000a00000000000003401200180000004005001400a0008008000800000000180004005000800000040020008005000000000080020000005000400000580000004006001c002002c0000000000001c009001c000000c0000000005004c000003c000000800b00000060000000006c007000400000000030008006000400400000010000001001002500200000000003000c00000000030000006001c000000000000000020000000000c00b0000000000400300180050030000000400300040020010000001c002000000900000010004000002c003000400000380010000004000002c00080020064006000400600000010020000002c0040008002000000000040120000001001c010000800700080010014003000c006000001200200040014000000000100140090090
  | 52 => 0xc000001c00600000190008005001c000006800600000060000003000000b000c00a00040080018000002000f0004000000000200040000000003000001500000050000000000000000000010040000001000000440130020002000c002000c0000014007000000b000800100000070008007000800a00000000030005000400000000010000000000800100040200020001000c004000c000002c0030000003000000600000000008000001000000000050000005000c00800080000034004000000a00040040004000000c0020004009000000100080090008000000c00100000070010012001c000001400e001400f0008002002800700000070020003000400000000000014005000c00400000000040004001c0020014002000400a000c017000000000080000008006000000100200000004000002c00600000020014006000800000200050028000000000f000c0000014009000000300080000008002000c0010000000000c0020000001000c005001800000080110004000000800d00180130010002000000a00040020058004001000500040010004000000000200040010004000000000300100000060000001000700000010000004000400200000010010000000400100000000000000000c008005c004000400000800010008003000c0000000003001c003000c00500000000010008000400700040000010003000400200000090008001001000300200000008000000400000040060000005000400500080040000005000c0050010000000c0010010000000800c003c0000024000000000a0000007000c001000c003009400d000000800040020004003000c00200040070010004000400000100020018000000800100000050018002004801500080010020005000c0010008000000c00000140150000008002c0000004008000400f00000080000000002000000bc00600180000000000000400e000000000180080004000005001200040000048000000000400000000060005000000000240010010000000000200340030010000000c0010054009000c00100000090000000000c000000c00200000010008000000c006002400b0008002000400a00000030000000001000a00040000004000000000400000000000033000c0010084000000400400000040024000000c0050000000000c0070000005003000c005800000400090004000000400000040000000001009c002000c00900000030000000000c001001c010006403000000060024000000400000080040004000000c0160018000000800b001400800000000004002001c0000010003001c013002400300040000004001000000200100020040003001800f00000000004005000000200000000000002000000100100050010003002c007004c00200780040008003
  | 53 => 0x1000c000000c000000400e00000010064000007c00000280050018002000000200300100010000000800000140010008007002c001000400200080000028000003800a0098002002001100000050010000000400000200000000005002400100000000000005000c0000000003001c0040000000000400a005c0010004005004c002001400200240020000000001c000001c00000100000020000000800900080020000001002800800200020014009001c01200300050004001000000000000040008006000800300140000000001000000400000010060009002000000000130000002000000000000100024007000000b000800b0090000000c00d000000000000020004008002c009002400100000000004013000c001001400300000050018005000000400000050000005001800b0010000000000700040030008004000c00000000090000000001c0020000000000000c00000060000000000400b001800100200040004000003c00000040000048004001400f0000000001400a000800900000000030003000003d0008000000000e0004005000c0030000002000000000000020010000000400000040080008000001800900300000000001000000000080020010001000c001002400000040040000001001c0070000003000800f0068004001800b002c000000400400000000034001000000000000000000003000800200100030010000000000000000000014000000000c0000009001c00400040010000001001400d000800000040080000006000000400000040008004000000700400000028000001800100000020018002000800200040060000010003400000040040008006001000c00100060020002000c000000000900000010000003001400a00040000030002000c000001c007002400100200180004006000c000000400100280030010001001400300100000008003000c000001800300000050000004000000400280000018000000400400040010018000001c005000800700380010000004000000700000010000000000400e00200060008011002c00b0004000000000000000010008001000000c002800000040010000004002000400080020008009000000100000080000000001400000180020004003001400100000060000000000c0050000001003400f00080010000000003400f000000200180020004000000c0020008001001800000080000000000000400000040000000001000400d00000060000011000c00200100050000000000000c002400000000020008005000000400080000010000000003d000000800000050004008000c00000040020000002000400000000000000002001000a00000020058000001400300140000000006000000e0000003000401d000000400040020038003004c003001
  | 54 => 0x1c01c006800000000000004005000c000001400b00040000018003002c0050014009000c0040028002000000a000400e000000a0010002000000600040020008007000800f00080060014006000001000000020004000000400000000000014011000000400000000004000000c001001c00000380020010000003000400340000004002001c0000000002000c000002000100000000000000000000100080080008002000400500040030008006001000e000800300340040004002000000c0004005000800d000c0010010006000c00200040010008000000000100000010008002000000a0008002000c0160000000001400a00080030010001000001b002c0000020000000000a0018000004400000040010058001001c003001400100100010008002000c00000040140030001002c00100640010070003002c00000040010010001000c0000008001001c00d00000010000000000800c00280050020002000c0020014002000c0020024000003800000100010000009000400c0000006000c000005c00300080050010003000000a002400000300000010003000000a000c00800140030004013000000400140000000001000400000040000000001000800000200000000000004c007000800600000010000001000000100000000004002000000600400060014000000401000000050018007001c00000000000004000000800a0008002000400200280020004005000800c0000000000000100000000004003004c0030000000001c002000400000100000050001001c00d00100010000001001401600000060010001005400000180000008000003400000080000000003001400100000000010001000c0030010005000800f000800500040050004016000000000380050024005000400900140020030005000400300180030008001000c012000400400300000054000000000c000000200f00000004000003c001000c00a00040030020003001c00200100070000000000000000100000048006003000100700120064002002800000080020000017003c0260000003000400600000050000006004c00300080000000006000000d00140020014005000400500000040008001000000b000c00000200020000025003000500ac00900000000000001002400000100050000002002c000000401200080010008006004000200000030040005001c00b0010003008c002000c000000400c000c0000010000002800300000080014005000400400000050048000000400100b8003000c000008000100100070028001001c000004000200000010008008000400f0000003003000b0000002000001b000c019002800800340050004000000800000780030010000000000000040000000003000400c000c000000400100240010008002000400
  | 55 => 0xc8000138400008c100f301cc6084000000000000c30000000006626bdc0000b6432c47de01d58e86000075800ac101e01f0715c5e000002ab40010009001401200100000000009000c000003c0070040005001400b002400000140010004002000c0000004000001000100000010004001001c00400140020000002000801400080000034000000c002004000100040040004001002000200000160024000000c00000380000014002000000c00180000000008001001100f00030014003006800000180020038004001800700080040004000000000000040050008004000000500000000000001000400000040010014000003800d0034006000000300300000000002008800200000000004007001000000040000020000004c0040008000000400800040110008007000800e001c00500000040010001002c0190004001000800200180060000000001800e0004007002400f001400000080000000001000c00a00000060010002005000000100000004000000c002001c000001400000080150008002001000f001000200040030014002000400000140100008004000000b000000200200010010000002000e001400300000010034002000000000000010000001000000400000040018001002001d000000000680050000001000800000380020000000001c0200014003000800c0008006001c005000800b0018002000c0050014007000c0020050011000000200000020000000001c000000400200080010000016000c000000800300000030000000003001400400000008011001400600100060000004000c001000000000200060020003000000000240000028006000400000000030000001000c0000000005000400100040000000001004800800000000004003000001000000020000002005c00400000000024005000400200240010020001006400d00100000060013000000000000010004012001c0030024003003400800100050000004000400200140000020015003c002000c0040044000000c028000c001000800100000000008011001000000080010010000000800100000000010007000401100200010010000000000100040000010019000c0090018000000000800040060000000000c00100000020000004003400b00100000000001002c001005800000000010014002000001a000c0060010002000800b00280060028001004c004000000100000020000019001c00000200080000009000c00c000000000080020008003000000300140000000002000000200240000000004000000d000c007000000600140080000000000400000040040010001002800600100000020006000000100080000004005000c00300a400100100050000001001400000180010000000003c01a000c0000000001001c000011c00100
  | 56 => 0x40313cfca000008fa82ec6fb00001ab0260c00007c4001c00000000000012c5e1c0b40ee13ea200000000000000000002fa967c18c01fc088d06b93b446df41ef8dce42783de8000000009660ffc411800014ea5130bf38df418465cf8d5c80001f2e74a051c06732c1e6380000000000000000d2e1db9000065344dd86b10450176863c9a0b1128013012e0c1642906e8c89a8000000000008c2928f00000000d5d0d12000002086f9800006880af400000003c4e00000000350000039850c602c30fd215e8787851d00e479acfce060300002688e5d0c2200001ff03b18000371880640a210db433a21d400000003d400624396000014da5b94943800008d20000cbd84a4416a2bbc3e9078f19725dd80000000196c3df400016242c7c000102684b41c0e0000a6780002a0884209f1a04138b21aac0000000336686ec0469aed00003b0c5b1062f000000000000000303677541918000000050e4f9f80000000000037e80001d3e1b40f6ea0fa24ec43450cc9d8416c040900960dfe04f8468c625971210f407c4ef511963d8439b000002071098000000007d6161c000014e00003b3e1f1437a21c2000000008d70b653b1033586c391ef00000000c460b4900540000e7c955d000000000000000000073ec000000015ba4828a698275407082509b000000c8800009ce8c392d2c50b4f9c9a9530da79f80001efd0000000086d0a9400003bb000000000000000000016d734fa000055d17f2000000006d202be38a23d7c4521c091bb0000106a9f8d0000000104400b70000000067d80000000382c121000007f20f980001d4733a20d0c000000000006b180000000110a297801e8f41000086b0e3a000023d2045c7c5842f01da514067701270000000000000001e7e000081f8000333800000000000000000000000d1a000065700000e4808a03a747e085f6000000000000000260225140000000000084180000da300000000b8b993f39887150e1e94371a4200004b6938c1d9a14c42a3043338604c0028880002bd400007758c0500002c4000004573e2e0000c778000000000010f0201301a231d000000003c3278007dd1f9f279848b10360000106069887b08000392800000001f31000003e8de0000005082b5400000001582000011b80000a866c3c000000004f2000000000002e8636fc000000000000000c23000012f4801c0001c670000465c0000e5e1afe00002df10d03322000000012ab3d5800002dc89cd36d640bc000000000000000000000013ec37740001ed025d80000108800042200000000000042542aa00000000000000000000000000000000b394fd00000000db6800036b02e980c3800000005d7c00000001b868148707000027da0000000159d00000000d388000000000006ad0000023800000000000334255d0cd
  | 57 => 0x4c000000000000000218838bc6e9400014ea000000004b3839d28c2162846990cf369600000000000000025480001006000070e41950000241c35c46aa0000193004847d0800002ec76d8f178dec000044540001ec100002fc4000000000004bccb1d81853dd229fd0db01d630c000000001093397800000000000000000000001440190463e8f858ccb137c5124599000024640000be20f7300006160fa609b700000000000000000000000000000043706394cb400001d6855ec000000022380000000051a000000002868000286227bcd6f91c43a70235800005f92f180000d7880003afa0afc000000006a40001097800015623b98296008901e213710008b0c18b68050e3c106615705af50210716325486b49f114a609ea6f347f8145236ae822c000102e33ca5a840001c5d3bbe6a28edf9d2636580000b7580003f762beca7b000025846cec1b3866e000067c4000178613c20bfc3cc93230000608079f12790c8079bc000003c2564404c5ab052b0e961a8893d8540297a000066c000000001c1800000000bce186c00002172a2a0000000000000004fb8130935a27320d1403b040929167d38fd615e6256220ec000000016ba3dd82de80a30000703c00000002abc45584268c4536c01f98fe291880000000000000002d6444c461e0e7d00006fd00000cc3315a809c1dda1ef3020090010112c943d280fc2569fad335c82e02f72149083c7fb80000dd7134e00006bd949c130004f42bb92a103d2861cd72874c3292000000005ab3b26000018c83f822e286bc00015b73de250d000000003fa20000f99139c1d16238c137992836c81a981d280000c74212ce1c00001d440000000000000007a28dec9e3c000000000001ba907fa4c60ff780001ea84088000000021480000ec30caa22560fe80000d5c12460000b258000000000000001673252018149430fb7056c83883e81a6d000014a86f79cb02b88000000000001d14776c602080e1334000000020dc230c1b68000000000000000fe08000044618a009700003c380000000124509d8000098b8000000000000000000392e299031100004234000000000000e4a00002bf1d1000000000f661874000020b83bc116400003b9c86e800027fa4718aa306d5126a192800003e83ef287a887480000000000015a012f0000000000005fd14ee000058b1eed00000000000000038d06ed90f60abd0a0e00006c180e81fa447c0000000020dc376c42b8eae2b865448a5b00001dd0138488e95e20000000000000000f56000000016f600000001082154b3f000000e909dbe28ee50e85d787900000000000000000000000016c0000000013b4000000000fa5f887339fd741744508b7c89ff1fc869580ff177e0fc87bac000000000006cac00007910dd800001bc983c33ee2d0849f00000e
  | 58 => 0xfc02dbc000000000005b5106480003eac0000f5300001f6a000000000000000443c000147600001d701f6000026ea48140000f0b000007dce98800030cc3a3c0000000000000001381e280cde2cd446794411c8027a40fc1098000000000000a040000264c000000000005cace0c8000000000007d204bb027e4110f2b9ed91a4039a8c6a075504e469fce19893741ce00006270b583bac1f2c00015341fc0829844180003a36554c00018e42ed418b8000114a0952778c76f84e941b2000000000002372294cc1b958015fc00008e18000053264340000301000068990ae8c3036040000000000000004ef05a58000004822e901d000000002820000000035dc00000001861355457687cc91b53446142cc839db73af41cc0e008000259c0a78572809e06b6129c00006bf0b3045c0e859ea5391226fc6d08ed7414a000064f0664181265a49790c2900000000000124a165e05d4fa91cc912f272d0825822940ac22f4ce296cd00007f68dcb000018d86f20cb5979332186c24767824f06cc2d985e31ade186200010c48627000041ccb06800000003fece708000000048dc000115a21da30bd03707d930be2bd0031091b385c413000006850000000006480002ed23ca00000000000000000000000319e80c45b180001f6830a04398000002e0000b5894900eec4d14d008fa22be26984f170fe10000000000005d2000009b8a8e986a00007ccc360800014be3b7404e835c074e0ca40001ac20c68000000012fe2d2433805e909e712ca3a5c00008440e8035000001661214626e482c9ee500002ae411e1551181c39d4cdd02b839003fc892480002fca17e000d166005c4015809e15b11e40802c5598c663ec85cc80ca9cf52baa6f7d07c800000005f84269000009b6000000008f404480000f440000414050443ed00000b747c1ca9a80000fd614e0f2f92b713660000000000000003c640000000227001e0019197d0378691012214c92d6665fc46708be2aca000000c1d7300000000000058200004e7c8aa9511309e15640000000000054e400020c8000017000001ecd000000000001f5a2668000108c8cc100007dc488a000023942b407ba038d10320000357a11127945280ecd027a12d01a0ca5a0b7c1a0c84c88e10152170e254c5768e0f06786ed454609c43734000000018aa00000000000000000000b9c000194343a64b50ade0c6b2e9a0b1881e85db1dfa13104b79a362c3878c891c800000003018fe68000000004cc297000000005540b608a31000000000001a1700005618c050000000004d000012942056215002d0000000000000001b900000618c00000000000000023515172166846c000000018a02300e9380003f245cb0cbb0f88328c1c4c90804de12fc299c82300000cae83d00000000362e00006650000253c65ccf
  | 59 => 0x16716a602801d88e0b01ca4014000000015e502906c000000000008800000001426000000000000308000000000bc800000004864a4c800000005bf0000000026d81640a040c7a000007ac00009d42e2265dc00005b1000000007658000385657b8e5c0000000085f88b98a561cae2cb8a0c133c12ea1cdc4c9192c18ea10eca8e0f273cac0458d2f00ad114042e82db0bfb35d87d2c000188d0b00000000003a415d021c051312722fe00ee08491065136a1954d500c5200000000dbc00d8295c000010202061ff800008f082d906d25e6800020fd000085e80000000302a7c6800000000000300c693215a00004fc89ea904815e400000001291246000007ce00002c040000e5f95f900000000000000042e800008b180001f2433b000021f92bbe4df40000fed0000596449d0852000025786de13b82f860000000165a00005e94f9a99ac3eaa7f74e041ab4404a11600591ff7282a04485d41f38179656d8f0b89ab00000f4400000001b1a642808300000000000107f80003d920000b1685b01e485274ba78000000025b018b800000005ce81ef07513b0a069cad103fe0ff47efced7800020ba315c7809e3f154800001e697ff25607d94003006f01841298c949108000069b90a30000117e0000c7c080d28160000891000000005220810821d2d6a3504f4f1a7c353e30949550dee08220dc86d7800000001e0c0000b45000000004fc8a2337987f9c264128b2e6800000000b8525f000000000a7c2712670c00a1250000084f4000118e195c5b74dd082ad1cd6000000016fb33065d08afa8b7807ee56a4fd2000000004f0803203bd00002450e610dfa3e3075002a59ba023e833a4eb19a0700002618000000014021f507e7071e3f6a42883689c0a3ff24e0c91e1e112d486774f028051000023682ff00000b2e341cdd3873930b63a78860128137d21f80ff90233000071c4fc51c7b068e000000021920000548c9ab92a636e25cf400e0ce700002370c6f1bff0d045dcc7958000000040c4000107f2ad053ece9b947e271e71f4ab9951b2fb207d0563800016ea0000aa39ac40c3200000000d340000000000000f61c321dc8acf0000000000000000000000000009c00000000060a089200003f94000007b8a6316dc106400000000000000000000003834272ca9e80002ba0599470f8ee234b0792cff302d2000000004a4857916a675bcadf08914008812901994ca0d3e730433000000f72000000000000eba1a580001421000001a4c4b82dd32107bbccdd82b000007694a721a9300004938a01032d1a008500492a1533fe234a4418870e000038e800019bd08ac10c50b791872c9c0000000196a000028282309a3818fe1f1800001ab00006178f0b13fb3fb67a001269b31123200000000000005e0000e65a06900006a8850d166d3
  | 60 => 0x1f2281bc000134b02d680a83c0000030fa0000e0f8ec5215c02acc8c800000002730c2210532bf62d506501bc32e301d8400019570000000098702ee00006ee4f9597c712dc000000015ad2978798054f831f0bb848e8ba313dd1c8e286c0000000000000000000000337038c50ab000002c80000000090a2c5c55ace70007400003a480aa01e702c259a00000b190c3e509000000000d302bc4e6315981c6c10601a11daa3ff8761cc6e98c10d0019f4b5c8da0021e2f1c45704e709c867707408d8602460000b4817d13346626cd1f083617264180811824506062c780000000000000000eb9de612780e241a09fa601f80000674027713cc3698e5a83d427822d6800011652b327d84ca28000276000004a51847129a2a25014852112ec5b244649a76188822841c509d30000000063e089f1cf24ea084d0a9e17b80464000133600007b809660b790c3c146c3cd17521cd27a04f6f84f81b3c4b14cb79c2d00000a24d4c0f8504fa000048e831d0cf803c000000001b000bf4373892622a608a846a00000c9618ccf23086b002014100000ba113b80000abf00003d0c48600000f2d0000000000000000bd00000ffe8e710000000020286f100001548535155706ee00006968a1e0000382000000000000283cba6000000007a340000000149200005d915ba00000000000000000002e500002061000079700001a57388a643c00019db1bb45d808f5800040d00000000000029644b20e0e19eb42c421ecdb7800000000000000000000000760316168c2c8a000000018f5219a0e7cb2f20e1266672444e28b9f0e244210f5d8000195e6a70a2f92461ae66de80e192d302da63b0da60a1922a40d8c17f000042b678d43d000000000000000005b816a20000000000025b438800000f3d2a74108800000002e3c74ac64a8000049c00008fe1dff000000006a41ceb1e2c35f86e5129b3256000000000000000112424f80653aba19c454c910538ea1b20805991c306a00000000941327600000d5000008f086d00001d672fda00004778000000000003db00000000000000000001d041dc4983800000005924dc51d03049254b00598a4c134826500000000000000000000000000000000000000156a40d800012952352515504c800000000000000010e2d3c00009d680001e720000000096a18d22664d24807a38ee4c840000000000014e4a009896235e6db0054000002c647045eb2034428204a05101a9624f40000f9100000dd471880000fe7277c12141978ab6354e45a44ad010800000580dbe00001aac39800001ad54348491c9a4171b1b2c639c38109fb0c48460cca509ee00c000000000e8c25dc70fc8550000301254ac3380e1c05c6000000181a52f984060cb3800043f016bc0001d9c25b6000027d00003a462bccbe0000000000000
  | 61 => 0x489d88fa170c3c8c66a930903e073e814604bf2bb23cdcfaa101c39940000dd9863b363a00006e80360095e5cecdb510170f7c67bc24ea1bf22da000000002d6132e1e50c9693d900001f3ce1d1d0a420017c091f86ed39e60000bdb00002c2c64c092012e62d0a6e3c6f5068907ce707418f1f281a9415b435994e611aa00006d880cf2f7411f103e1d24167e1d2800005c2335a47f8f390edb365c84ac3b3974513300000514000000000700e5103a8124245f50969762319c1ad8000000000008000214000000006c6c000121d21f6000000019e9140a000005f87882e443ef4ca9800025822facc5200373b9e631072d9d83209a0000000000020f60000788800000005dac0000000382a1f8800000000000075451e800000004c788fa80000000628c0000fd700007a4c000110703180000000000000000000ddf1bd425de35dc0001ee1000083d43cb00001276499c2289d5f21645bd039b08eb43380000da88f4d0cb6745400001e00d1481a840208bc0fe84240bc2208136c60000082000026060000b280000000026b000000002ea600001941f8b3384221c80a81070000113c3a79d503070444c239000000002874faf1d8c0e4e42e439c000010fa8710eb08aaa0000528ce4821fc2a76000104da0c114385b14f92836c0ab865e8a1c03991b1c5f488458a610304205c00012270000000000020e605e83671051156400005b88b029f4800005c00d7d9120372a2760dc286070de6133c5718de12f5263f8570843f0d266b5d080915c30d21be02658e4f1456852cade9ea734262d7cd5903d319a4725878a870a3ca4624471a910202e40d3044116e440981a6889785a42a0a00002f00f6500002570000000024cc00000001319254000000000bbb00005228000031117ec000019b15922ca42ef01908000130828080001c0d28f00000a1705bc343a1254000032e28cc4318caf0000141274381419128000054f8783000027b6728000000000000662800000000396000103c80023b580000dfe08d200006d0cc801b89375c0000209000000002a6cd49000000000000000000000000000fbea10e31cc09980000000000000000001c442a1c000000000000fd400000000000171c23f8000179b1c8434ace508fc63d24000074c000000001cec000000027526c687de0b73000000001d8800000006a15032800000001b0c00000000f5a62f42080000000024043998bb40000604800000000000729800000000a12511424b0d2e1a6200010b480000000000026a0f683b527e744c6945a0000000104119f30000000000007891aae00000001e4d2da67478000000000000000dbd9a1c417207b000000002c08459c00000003a524d5400003123f6475141300f0804141dc004513da000055b40b6177c25666698a12968600006afc4130000
  | 62 => 0x2201a02c05d5135000007588faba17c2b82370859c91fd00162f34c9b9b843ed216380d99f0d159867ecc2e9bcb000011c04e5045427360000e128000012800010900000000000000001cac0000733cdfd834a3f080000b9c9b3c0000000000000001fca00000001dd900007824c9c000002ee31245f20de23c7600000000c5339340000000000000005a4400000000000000000a800000000710ce71f1004c81630c909fcc000035ace09804a000018042a71087130400009308908173247b000020f2330e0a6800006490000000081c2016246a1914000175b2d348120000003f00004010d6c8f322ca200000000a3400006e50593019b0c3a68a48b30dc900000000db283320000040c435000018366504f2f0e18357000002ca800006e682b8000000004b4328800011bd3edc5c4066792e70b4e00000001c072e125da0c3b8b9629c000000000000000052440000000000000e40c7800013c662d8552914b2b400000d5090e71a466fa0c4f000012e200000000000000004d400000000000698000005a5426679dc0000315109c0bb4d6e8f5842bc5cf031590c805f03f58d0205cf342010582259432016a00001d11ce72fba0000a74000000004878b7f00001b6800009d2948d121e00000001d6630821b8cc7c950811c44ed102481e636ee8608f2400001cca7b9887b0000429e00007341f7e11fe585c000000007940000000071c042a0000a55898b000000001d900000fe40000f5b8f8c057256141bb0e1b3f8600000000a32192200000000000000079000000000347a000071f060c0000000000000000000000000000000842000000000002f2a34e80001c4f28ca59e42b71ff42cbe22a08ea000007025f14a521a8032960000012800012660000000078523300001063831a3344000033a19df000065c8d330000000017b42d70b0300000f908af89590a7a2df473d0cb80a0c43c821d10f525d45dfd093094b1ce6223c1801f2a000000010628cf30edc311c9148ebb039c46d8aa79d96317033d003e094712c62b6cb748a74000054980000000000000000001071000019781a400003298000002b983f1a4813ac0000000000000000000a8800000000000000032b200005699a253f6c0000a81936900002af908587f71a020000000162a14f63cd0000145c3af66318f4b00003d5a0e300898801097268543d1040d000031340000000000000000001c730000000000000001f2a000097203fb1216235c70607c738ac470000000000000313047080000a98322cb2201fc000055040000000000028a4000000025ae48a8cfc8f8d432a0000c3f800000000000000000000000000d71800000002cf0000085100005fb064a0000000036d4b35000041c63234a1f0f7000000000c68800000000000000073d3d8c835c0000000000023b
  | 63 => 0x4433598056c0001a4d0000336cbed99ee1ac63fb000017513e82324c79810c7000009c4cc78b6c2b1a07b40361fe80b7e5668a7f9cd22ad217c8fda044512c069bc92e1de0398e0aa400000003a4a7e250031d2f3b3c358474882b708de485800005de130e783c93f199d331803fc46c1fa0000000002a8800026367010000182e2f7628ec89811d51fb22c9c1488000251a0000dd4183a000000006e68000000000000001c6d000000000001f3600001f4c327800035ec00000000ea03aca0d78000000000001c40f2d00001ee48408a6e89c700006dd868d9c531974571c33b21a90d4a2f849651797417c3420671104a348c57440000000366648700000c24326814d0f46148229ea1f610dba02315ae57f0e38172900007e88b34800000000ae80988f98352018e0b0891f8216000000000c3700000000520050e0df28330c610b3a30ce1198000000026f412b0cdb146b3f3225500fe9e213d943ebc0a28500332a00000000000283881ccbf41393352e1d7c93e8000000000000001a43000024ac6e980000000095800018f0330462c8eb71fe33e2800000079b87194840580001d9b00005e7c4249d16098e00003ab827410a60d845bb1d1c2ea000007498000102a1b340000000000086a0a080000305411c40001733000071a80000af600007ac400000000000587cc55848900004284000000000000000c28813a00004e9c0000000000011e8df217c224d2180898a800033546818d8fa0aa205021bc97280001a9a00006b40000000000e060e07ed13f8000000000002fb87108000067b0000000037585d91f9a18fc0000000314400004dea05d1bf0317104380e03f5600000000000303e365c000201b00000000d74000000005c2d0928fa93670345c9419f400000534800010ee3f605fecbaf036810e400006c5000039a600009568a3f239c5558f6292a900006be02f995c8291e34fc0001efe23dc182c4af90f40000000089e000008d040e80000ba30000331843280000000000094f800000003ed80889f23092206b058d0e0531b48360eca0000208a85f432f800043b438f40000554000000006f40ca61f5a843046c87e718660000000000038982b8000000001fec8778be51284000029e800000000000000000000000000385c0000000125c00000001d2a28ae67d828a1e0b05a00000000000000000000000000034a64668104062606b44d190e69e49022800010580be80000810c84c81c62c02000000000003b9c0000ea5137b181649b4af02135259e49f08c688e42b2a345832c005e00760000d7e1b0836303b302018d6d415e064451503a30f9a81c8b8516153c5a602c7a40f360e860d94048020b02044314ff09bf7310e53ccccf00002ba400004f2158f00005718000000015867554bab8c771b3a75dca4701f
  | 64 => 0x81000000003101231000051d4f4812a3183e7f4c000000000003ae44ee9561049854a8334018017f25eb82608492018658e8c92a09c427e0d3c6db852d1b3e6e98b799fd51f9269900000212000086c0ab3882b00002ca024980c712e03ac87f110f1000064b8000037a000030d8bfe8000134061509601a510b263f0c00014f40000022cba393f50f7e43987ad9702040272481ba0e830000780472a8a520000000000021cb0000000000003040000000081a195f00006640000093d0638103c0001009415a000000013060000000096f0000000042202b08000000073dc00000000000000000000003e5e35c8ea614a905906bf80001d5c00b057910239bd53b1c5e242d5000000007f7c0000000169e00003fc8575356c2eacfdd000000002018c12800000006c8cda8122b00001c607be0fd105d064d4c8f10d919907a88b98919c1edc2da8e4e8701097068e89f98f6a000086f5094070b073c30e90bc80002e2c7954ada18b305306cdc9ae822d06ae29cd045005b03a00684556906c2dd07be90e298cb3ffe3a5428b15b0000000000001eb500006b5837f80000e18318c0a9969d0000434ce439eda30304a684151950000000001be8d980000866d08512542cd67b9000000002bba00000001b5f000047ecba5800000000000a18000026cc4e4832981b6299c3aa04d914b9398000007d98c1e09645174fb381e50a1e83e10a680003d1e0ecc000192432264fa0000105f420a6594e4f847b36025e48323036d256a0ff08b59ff3438662703d480000b8e0000a390000000081c4000000037ba5edcfc180001c7e07707e113ff0ff668646f18f80027200007580cad121a0000ac880000e06000042118be067a06b40000000000000000001bac0bc800000000000000051d0beb002d05f22840d66800006fc83f070319793f5c5c4d0b800000000315400000003496049084a0f430000000000016b60fd8873c862000000000000ab7020c000074fd0bb9e8500005a54000161a000068b8000024800000000daa0f9a0000314400000000b3451e400000001d1a7ebcb5b8a4f1cec0c38000172e2ab800000000ff73130000000000000ba00000000076f000064e80001d511cbe3fa4000000000007888df28000000000008218000000000000000bf33f4e0000ea1072200007d34da38c6a0000000056780000000735c2eb209f00002b8800020c3343408d82bd962829e257bc7cb156a2d285f2c243120d40c4000000019cb18e63a100000b8d000016d400004020000000000000000000583000013a10000000000007080ca283cc00009f700000000ab306a000000000000153300002dec00012121e547b78b619e3034ca0f308bc118000000000000000000003164000063219682be4444200d08263054a800000000000009ac8715422400
  | 65 => 0xfe901712bb000000006158d323a7a33e08ba8e7c37ec82a0cfa21dc371c1bf00000000414e00000000000345e00000001d4800000000ce980000000270477c13b900006d9cf9a0000198a833811607a60a6a821408518533e741ad0ecea1ce200a0284d5e9fc4045c0a88291217100000000bac00e4107064cce781c183eb60c2cabb800022d45bf43d20000306400002c586ce3b560000cf69e6838b813086a600000000000000000003ed800009620bef23ce5b985221c46199c3be90339b1238223e943d885df1ed63d78a8994d624e258cc4148943336a7850c758c3400002080501a06434d60abcbd900423d3401ac3b280002106066800010eb2b2600006dd1c34000046ac60680d40000000064806f72d52000048483ae00007950b568cbe154e83b8eac003e23e6849ca61115743807f90c3d0000233c000000021030000253cd1003cb40106020000000033340000000088d149400000000e9b000032210d98fff219c6af8000087913700000b5d18e30000320c175077b000000000d90000000000009bb14fe000000002540000125234347a000000000605000000003cb60000000000000003ea0000208e153a8488ea798f42d76268c3658a5804a86d6c00015820000872400000003a1a098c0001529351c7dec32600000000000000000001d9416849ee000000000000000000028244fb0000161000000000000188f00000000000000000006d6800000001ec478e8de81a1b115a0000642168b2f4009ec00017c83d3232a4251000043e81ee05a38b0519a20000000000000004de0e7114ed0d0e49dc0000fd525f2000000002393d9008fc5288000000000008ec028d072455000000f9342d0423000000002eea0000e779221375a2fb0000000008c64354aeb9f1500000000000000000005284000037100000000000116f31ac0000508800000003fbc00011b228d4095467b152124a2812c4e000003b50000000019c1244400000fc896400002b60e42165300002afd0d50d4e3b2412acf150dfc00005784ce48b953a881eb8eaf1682223644cc48c0fd300000000465135b1c205d8c31e8dc6000034290418bf23c461e7809b0118025a7da881392d018c849a84199b25270c0000abe9356179e7e090e90b2a046a00000000000000000000000c9c00001df506582100000000000000001ece310c7ef9cf1000066f0000000000005800e740fa003be865880d023a300218a80000b331ac467902979d141c1a10f050912fb2af2860c08e980e214e4e042169d7641ec218000006a800000000000089900006a3000014c8146e549c24a0000000073a41239d2e0000467400019a7000032ecdc1140f39b22970fc30f750f3a1940885858836422d84c9c940713bc67000ae93160cf25c74e7a0000293e4b0c02a2037288665d06ca10
  | 66 => 0x3aae00006f20000088c6b98b718404186429b80a8000008ea029cd990b770ce40000f690fd41770489109d000031600000b1a00000c5203a8820010d082800008ac9b6e1ede000000010ab43400000fe7136e00001750a5f9822362c7fc06728e281baa000000010e2086c82109e212ed10f809b0bb888e6136c255400001c100007bd081b80000000696c3660fb20000000000001fa00000f740000000424637c00000288072227406a896a03d7059d4e6e9bc13cfa00000000000434c7db4ce20e942a6c0000926080010d272b40000cff2eee000000000001d0e35e4f6a800006583d28a9797ee10785b100000db641640000000082111d251a02dd8dc511dc0000b0e8000000000000001c0300025fdc4a30f891c26624905e0d7831a68160e14800a10fc7c7c1159d1f15bc00002818c923b4e00001d6821621388230db4917e06700f401251ef305827420e20033905aa708089480001ca82230000056516d61e6000010ef00da00000000e2d00000000a70800000003adc0000f1e0faa000000000000ad20000000000000004a250f8800000000000000000000000d90b4c0ebf00000000d1da0d300004d4483398c025b2122c3351fcb01e84f98000057340fc2a6816100000000000062004d90000151c0000000406c0000000083e33360000fa1000030941230c1e88810d3279640001bd235d6771c56f8225002c000031f0000280a69d400000002b4a4af400007e80000556c900932832f86914b8200cc066a6a510c0106a17064f3ca2b00001d5400d0eca800000008044a7d00001cba0b5c1508000000025accb0800500006560399000039c829c87ee04ca073886f80000000000024bc02e9655329e0000a578e8e23da17e8c48000000003bd4e571bb400007730db107470a487f3cf74135e003a6a9028b9fa5000000000001cc525246b9c3ef00000e7e0000c828000000083bc000000034f6811000000000000876c0000f0e0000000000000000a907cf08ac0edc2edc023c000047600002efd0478bcc29b829f4000106923ae2dfcab186fa0000401c1f582431552553870b0f0a078e2c90978000018ec61585a80481038e0000db41e1204d0582035b9c4e159412600000000107200000000000413000000001bdc2dee38a80000c100b8245f00ff858300002f20ed1800000000000000000012e800009de8a4600006850f420000000000000000a9821b82ba43970151000006bc000081b0c2e000073f00002cc80fb8000211c0d6a03ec21e813200007bdc7c1908f2eb412f436f000024c0576ca91014234304934af59c6627ae730c6b80a3a3a7680f4c669f1d00003028d1c98803a9669c00000000000000000001a0d00000000000000026e200004ce916c000000000000000000016886d1118415fe73a883194b51df82
  | 67 => 0x43843270c78113a219d0761ea831aa5db0000000023926d18fa5000000004f58000000042280000929987541b6008093c000018b03b00000112e000000000a51c4b00003488b6599e000000000547000040180000000000008c44de4f67043832dc77a08e8872b0000444000000003466000000000b93dae0000000000000005dc80001a4100006890e4400001fe209402ec0d2c1a86000004d13d43eea326cd9800000000000089d16620fca010cc018cb50890047c693800000000000ad3937e41d4000000000003eec00000001df5033e000000000000000000024521d8000000000000390000021208939dc512cc0000000155203a40000faf800000003ea8b3b80002d9c0000a03000000000000000000000000000000000000003bd000000000d64207800000003032000003700000000000058e800000000000c0613eb3db67a74221000000002de83031944000047e8f7903f500000000dc68000366c147cfd495cc000000000001b1913d0000000000881018493c89f00d6000000009d30abc00000000000000004fe000000000003bda02c400003cf0f180000c0e0000043e1e34dc88c62269c329c489921141a8710c145a0e5369e0000d6d21170000814d083843500003594b78000022147a8c90b8000320453ac7ef019d18e037ecb9c0d6610b2000000011a71b2a5f38b091fdc42f60ccc44c11dd2da481dc6821a890046798cddb8e6e00000000000000000007aac12d80001af408700000a8600001480000000029240000000053a014c875400009160fa20000b139f0e152e00003d9869431406b84e51800023ac4f486be166f000000003b6167803c839389b9800c2ec20000ad0800000007710f2ea0dd38367e047260bad1cb4763c2a09a0819783f400330c01149c4cdc32d08622abe42380000876000000000000d25000000000000000000086680000a78000000008fb128e107e0000f619074312600009878e26000079b891d80002962000086111a6298a7cec8e9857f000058fc909886c15266e005aa9cf2391e07448340252000000000000cfa1b7a15340000000000087442ff92dc006c69f89a096de0000000000000000000000000011b8141c4c70e579eaf2a9268f07d80000000086881a980f510cc000000006dd0000597419d82263b4c0fc8f27075a3e868318257079c3dec5ee0e010d1d40aa0000a5980131a20451cd89968800005164506081a2bfe000000000002da200000000000032e277c9f000000ea4506d04d0000438e41f8810000000006a94df89b9829b41d4cb9389f5000070a800000000f765a5c000215527742160c2e16b83d6c78ac26d063105be317c3488c9f19840000b941c7c1c080a941be030a122a0000cef05ad02aa1af4372931d177c87941230b7e00002cc4f6218c73fca5fe8c388
  | 68 => 0x133e24aa520c6c98ef2281c00000001c8b0000698c4400a0b07b653789a01db500000c881e40251000025fc0001fb333c2000000000c11dfe4b7c3649e0d427c1d38b0189393926149409b8c9600000000f33000000000000ae517af23b6000000000000ff04a4c6041a4c258e0d88c43029410c27dcc8aa1c7f08e6443851121bc095466800001b4e000010b8000209e000045e4c258000000080a09a3a06d20fa66c80000a5010163db48ec8e9a06a86a44000013b3ee80000000142200003060ac090ad00004624f3a0499159210942ce9590063651fc000000000000000aa2000000000000000000010bc4330dcf8000000051b404e000012541800df788130bc6867c0001352000036083770a2e2f9a1b6c7c11e942ece75f036c0c5d3b9029b0a7288df33d054c8a429a3220b850ec69f02e4033c0000b5110b50aaa0c4c0cb05c418182ab00b984a1000000000000fa63c064a00c8c162600000000000009b00006e1889a00002bb863f4a43211616b20d1800016c20000604cf4188f21a601e4800000003eb00b442e40c7d1c9a78f50f71eba04280e841490fd8000057a439f14f92cc60000472969f000029341dd0b340c6a43045e5000031d00000000000000005b18000110c0000000083b140a2c985560b6b13250dae6c703549dc22e7e68dcead9f5313d46ca40001a2b102879a50e8118b3e9200007a712411024818c79da1cc2c440000fb105e9152c00005c91b343e4c0000fc411e500000c1cfdc87450c46000000000002c8e000000000000066120c000071400000000bb30000000015602580000082a0001069104700007cf85258ead0000000107b800033627edd0989845193a19b4cc203da000000000000000000000000001a3000006124000000035c43a70000130b0f6a1dfc2d9800005e20b000000afc000006a40000464069a0000afb000010747d700f18285195658c00000ef31fd048800002090379c000000015c91c760000075800031d40000d9d16be00003074d7a8b30196044a864d178d33b048180fa91d22ac435640000000000036ec0000000000003405c4803539b0000087b800000007724f09819012084920ff69ebc1ab60000a98928200000000feb000040b600000000b9d0000853829b1e9b34b40e0cd9a918f1abc10f8eed00000000622c0001519000000008648846000081402481df0438c185053ca00941a2280088f161b0974407400000003a2e6b602159ed3000026248051db1242a062c5f121540000708898d000004821a5430519f024a47ea8092943c00005f68b1080002d0233f00b28c2d23f200007b017aa00003eb8f6c14940000073cf3c02a7108646840b10acd09e8133800000002b120000000170623be2c547d588b61a666ab0000000027fc285c0001af30000
  | 69 => 0x211498980003246347800000952bbc54082f88d4f158a42d02841209004c2b641e1094027483464eba80000e48000000004fd0000875c0000e2e03401974cc70000210a000000000000000140400008ab0000000004982e000007e8c0002198000058d400c8aea16767994449800000002ac05c89cec084c49b00258000066055e85f0189400003d5c5c1042a1d6a000100909eb2b3e4ba0133946421220000fcd1ac5344255d430b156c21be14481498669039250a0a240000000000002ea800010be414054280004346285000021780b520000000000000006be800007b4000064f094c982c355600006719cdc0dc2057ccff13ce2b76445c0c700be084e13c8ef10d7d010a00002d013c00000303cda48000412e2e3053817010000017c0001de427c8712454782782dde50740a700d9000000000001f2d3c9e000073680000000236c00000001cf0000108a8ba50e8c02449e4021b00000000220800030ae78c4057114027f800000000d0b000033a8d090000245e5fa8c0218b70d18158901d86841792000000000000000859c9311ebf034c4ab0b739be12c8c3fa887f93203b740000a3d94d93e9e000035180003fea390cae58d6433c441e8b1780000e4200000001b2a169050ac6d4137414865bb8d8f09aa00000034b1186e20d70000000003590b3e00003cb800011e600008ff9b41334800008e600003ad2631416980c000002a8466f93b201947b000000ea90d847e3ccc400000868425c5cc1417246651080c0800000004db40001c8c12fa400852d000000004d7c000170d000000006af92a725301000000125a257c00000141b8800000610e828c6100c2729c3690ec206be000000001001c8c2d0c4a2085525fe05a85cb9ace0f361820d6e179000001fd860b82c43bd6001073d81861aa62994845000015144edc03a9b5d2eac00000000bf03bb8329400008b11b543eec7fa80002a125aac51e000038dc25380000296426804f8b8aa0b700003808b1e9d8a00000c50907974831080a985ce1d0728d846ec0000000321200003af0011000059b880011b00000374857390e000a06bd03f08af5000000000001dbc00000734e8d1f913dac8514efc8009377a28b4de490cb0780258844f001f36e81908d4c858d09b04f7c00000002f480c147ed9c230de423080000000000059fc478800000005b685d0203c00005e4477c820334be0578c3b04bc071e0000b6a80003a0c1e1c000212e3a04596c000201a19e400000000000000045040000000083e7030fe0057135fe0000c2902821a503b4c23700ce339424d00000000000072a059b00000000000101900003df84abcef999b72fc02e9c78394e23e8a000000000001d423bbc49c1e8b08be79900001a8f1d560eb044489fa03a600005ea12a509e61428195800000000000000
  | 70 => 0x19ea4012442990eb0d75022a0000000061133165a3c4550000000053c0ac71c6000004974c0117202e38048878f89c842e61f6c62412d501ba0000bde8000000000000a085a8000037b40e2963c00000000573000036fc3df8572000000000000000000034180000000000000005ad048d000000000000744915e1a8a59c449900003c840f890f81e500000694097487313a74229c0001a7240a88255066898e0000000050fa07a06d400000000dad0000807c9c1100f32c047a002282e5000004781bd966c066828d49ca1e20274400200001132283c000000000000ace17dc000000034ba00001398f5d0000000000000000d9e0000bae0000072600003d28000008c50d4925965c165a877c69b15f0000032fcd3511013ad022cc2e982380e881270a5119960cc20aa8af180000a9e190c62b1cee02cc45885c780001d4c1a9c9880bd31dda5cd405c0bd1138c6188548190e385e584c9658b4100005b6400018b924d618c054e000034f423f4b4e0f52210c00000000a21335081f4ee89ba439981ff8ebf97f13576199cec080002b3800008009f9734e806d4886800000001e08fdf1003000000006208156239e1478d540000417e352ce0b800000003540000093600000a000000c13434205c40000000215254b43430b520000000000017ef2ccc36e48db844d041e000075893b50888362ce4c984e282c000000000003c523c088f10000240852040000000360c667c8780000000005640000dff19a000000001c2c000000000002124317656bc46583a00000718c00001f30000000000002bc0000000000020f100006ef0f0380000f843ff40000000171600008211be700002ec40000000326200006e79c4a2e6030848d88d3c3c1c54180001f3718ce000000000000000000000010a5329c2508a0a119008b400000000a87000007b80be88af00821794f5e8000000081c00001dfe2644693cf410a7e051c43cce26869b0000672078980002a3e15bc81694ac2f2c35181bf9b0b08520c8076400003f26000000016ec000000002bb1144000063dc94b217500005a28d5a800000002c880000000016c02607cd9bea0b6485810680000247a000000011ac353a39140000f6c13da00001b70380025239fc00000000000053c0dd828700006b1c000000008f2000000000da00000000e9a99111c946c5437aa14200000000d2403dc0000000106200000d7623e50c980520000325cd011d39000015100000000361400000000000000038d0000055600005d282b5800015f0000034800000000000072c000000004cb0fc280000000799c0001f13000000000000000324c0d44aa4000000003f744d7800000000204d7780003b5c0b70000000000002dc0000202f2d8e000055d935c0000000000001101a1c000000000003dd800009cb98fb000
  | 71 => 0x220d2c3a4126f07ec44485e8000000002f143570f2f0ccc01cc00000003736805cd088fbf00001d08f5716251d4e4f4c0001b720000193422012d62f825eb0b269473000021900000fc42ea80000d608b1c38a002ecd411c3609c03ba4682944d000029a0757800028008474c5388ea08d83548c4e988a00000c34b8780002d368570000000042c268b4e8c987006ea5318000132d3c100000cd49bfd000058b053580fe27bc000000000001a2671487d6037800000000b3a11d00a4c0000c2a9cd409fe44d800002d400004d34000201812906cb42c3800000000000ce61da1000068246f8800000006ec45f500000dc024c04eb1d970000609000000000000850cd111dc02f382604828837028f4585044e05fc17cc32184be07b0112a00000001c141bfa46944fa064113e40bccde2940d0d5806d0b6c17c6324412f90da9c6921a886786bb177b384807a06590dde41620000000095615a400010ea039526f80000d1380001d74320400011bf132c1398d349f0200000000dcc8000000000003f99d540000332482a00001e44000066b8bbd295062fc00000004260051c916800002403b240bd89a827f46f801c58ec737d668b00bf0000000047980001e38411a5700a1b106f23c6779c26305910000472d0e50000356200006d98b2113c420bc0000000000000000000029000000003db876429f00000a3880db0eb632b00000542044e87b417807aa2bd8245c3be15ce082e00010b6800003de664c0001fd8000052a8f890e623a9a5750f308000164a22382529555289608c0b570000000060acfc7182724045ca8e190ee42a3075c00000d18000000000000a811710222c0000613000069e4bf480001d7a0000e6a800042583b640001780000000000001588309826b4bc50bf50000384400000000000037c45b9e733ba031286fba05a2f6069e0d0f86d600925030f8c9a551a8e41b499f82fb432877c42f305b7188c0bacd92076a14824a301d803262df07e58c321bc72b64000000006d4000004043d40ac40000000058b800018046f607b496aa1ccc0f5cdf61146322a125cfec8a33000086acec017b52b5000000c40bb739724e5800013d0314a000008d92b42ab20000c03000039b660d8000000000006ce4000179e000086c4000061c00001fbc4881a0036ea000000021f200003e40efe90620000000047e0000330a8784000000001ca00005c506810d785e84df980000eea5a4d0fb06fb104e00004eb9484000000010fe997e1006000000000000000000000012e11dee54f000000000a7c5880a1618d00000000000020b3102c19f803d8000000000004051a313112399000000002c6c0000b1c800010a07c6c000000000000000e41024b0000000097d0000000081d83479326000000000000000000001fcb790000000000010b
  | 72 => 0x38f000003b42572627c0001c7a00007d8c66f039800003f14000000000000000bac8d3827de4050cea80000000000000000002a700000000000000000000356800000000000000000000001358000063c000081190401bfe32360b1ccb80000199800000001c58215006e056e000000000000d88000000000001084862126280634adc000031f838a400004520a7e582c00017e41c2854780001caa12041b14c2c84b73da80000000023100000fa403810782f6887ec000000020ee000055a0b2000004ca806b80dc375e878c0001b3e076a85600708000000000001480f7b119a74880001d5203a81b989c28000000051f49cc000022ee0000d5188c5000074f0a6616a3314c166cb8617811dbc68d400016cc27963c410bb0f1d086e11f8b0f000000000000000000000000000caa0fcb00003ec400001490000000105b00000000000000000001c7200010d71b4a0c90515090d81b7033000002e88000290e2fd0905800000001f24660129c00003cf00001469315e7d740001d4600000000677891e3b045864bae976500003c984480000000000000001699000000002e50000059e6f1800000003dea00000000000000000000000000000014a477296fa35a25ff8b27a1c8107a1c4491c2086000019fcc570bde3c4800000001139000000000001df725704830000033e23b834a856b168415f40f8400011450e0e516cb650ec41ff4645c4f600001ef2265451f08a909be7b88d7800002f5048b800021470000656c6378000325e0000000165622e819e8000042c423e3610000000013680000358122300002da010720591d585068f0d082c361c1440ffd117f04ba2d28621193d1f807aa400000003bec0000e80800000007c4400013e71b803bb89828ad41eaa478019d013024ca7dfc2fd9e39267400000000b5c0000096438c8feb2344665068e18db315887cce0f1d980000000066c80001c5800002ce000000000000d2c9eff3af06b489bf80001d32247098f9dbd2f9e2f04bd586ca14ba013c3eb98653c3e7fd80000f12198856d4000167e1c020000cfe14ec09343d182af0000336000004088a710a3065740001d6a3bbc6b280000000000000007a480000cb85e384741c0e31c481ece1ba1d93bf81300e378c3d00000000c44157f1c0667588358de000002e04fd89bba40a2755800000003ada2f5c61380001f3a741000000001966000000000002cf4525c0001a67226e7a7c5f70654120c000046e872900000000000109d0b960000b92092207aa2d6cda2898800000664000158c32c60000a85872f000036f800018f61bcc3b442ba1e0200000c085a7000040ea0000000120324281fd4beb84820000000000014c1000000000001e7900001da4dfc002e2dda36450168b182656466c5331b9c044432dc93a92b63d
  | 73 => 0x198620c3c30e2340c002f4bef800731b216b0b90a0ca05b44dc0676984029361f8c0668324405849d0331000042b27664efd800002980000000005c0000083491f000031046908b240194000047a8ab910f80b1200000000000064a00006b6114824d000003de948c351635b845c00000000000097b094c000000007fc13bb061e000000000002b720000000000000003604f031fa100001ca800011c8222c06f88ed0109000022989851b423bc200006e88000000077e8531090e000054680001d6b20c800010610bb3271c6a6d001911f00002dc400000000d1c6014291800000001e840001f470e9a3e280000000000086941fa07f1167002a8cdf1273000000003b58bdb37542db4c6504c512d20000a5f000034a4000000010e307046264b3900000000270cb9781da11a05b3c22e860d1f3e673c00011111e1a00001de09f315d6000000000003890000000006f026720000cc009da35c800005b48000204c514c3e418c936900994000000000000000e108000000022c8000219000000000f0d80000000671c000000000003d44e8782ae0000031800013c60000674865188bb1b18000000000000000218ce1301b13f2a1d580000000430c00009b409db1c6e679800019550000343c1c2988500000001007038e2a4a79c00000eb3202037ad0508f05183478287a284880ee66f0887e047f1a720000ad30030411200001ae800027102f9cddc01bd3f0e71b04bc1ba215e05a1c9f099c617b01e102e4984208a652dc541090025c40ea8ff4949a0ca454dc000000000000000468965700001414b46a1ba125a0f1107481a41cde076c355084a08165d244838cbd0254000000017bf00007ddc000084f167c6f3cc001d49000079c47c09cda076e207cc58870509621a783bc9db800003e18594879f00004fe42f0800007860000000154a0000000084f0000069c00000001cd000003f280001658000083a003514d400000000f7c8000326c000000014fc00002b680000000384e0aec22e0000000000003ac88e7144e73fccc3085a2b080000ac500003c087400ddd895713425e8c0001c61223279e83d78f4c261875e4f208f31000063842368e63000000000001f163c207f78e7280003ee44b60fde18393f3c2008588938d298038480000d0936a44cb811f16830818513cb93138b1a18379cb818053139c2ff80001eea2fa8000061f0000000032c411a119324bc3f3101f19fd000045c87ff0193000000002c3000000002c04c2d13b31e0800010a895fa2c56295010c816e39be70f026e9444077c536cb401e441b4e4fc0dcf0e1e000070c4f860000000024fc000145804340000f9207a7000039c8000145e0a321c5c1db000033e43ba8dfd00000e4c75d0d4f19ea1f4e435cdfc94d00000817c298000000004800000187b12c2456c0
  | 74 => 0x7b20000040a4654f84829b000000000000000000012d474400e3000000000000c1921d800008de000035a873e023a12dd0000000000014ef04d21ba4000000023486c1495203ce00000000274101f00002bdc0000d9900002cb0000000000005bc400000003d380000000000000000000074972d1c4e45845659b281a846be4af40bc42322000109d800030fc0000000000000006d64000000000002dd00000000404072f81358b3d2c8604e0c1d8000000022d400016c80ef4000000009c901e43bec81e19e728325e144888f1817f84538f580553155c7190de984f703505f2492121361d8c3624c798c380000217400012ae1f3c3c68cad10fe373a4ce0992066532a483f8ef499061c564c48fe402a432ea38cc0000d5501f22430bbd0b04391a0b983ca8db80000000101a8de92b582c4c58912a2134a3f20d7e85ec1c2a0e510b71a682b663048247800008ee519c9a48d6a000039d03bb8000000007d85db001e274676347dc054a2f1e6c0c03b82182bee495caa60be53b960cdc8150f8400000acc0001f9831e40000463988e341e35bc0f081d90bae8610f7c136438503a1448916293e02072026990321912566c30c168901525dc00ad16702e10317907803e32f445d00a2514d124fe1d600002113278a000045197f90000055c53480003e587878382117a0fba38240001e2500006c80a6a825f3fa844b0cb89e451e706074f550000059a00000000000000000009d50000257e65e000007ff13ca6828771942f28545e7400006c723c815b00000eda236681d0ed68000401e00000000a4204d415e0ad59ae9158c55e0d361d1809e20ac4065800012a00ebc3778000000018b47e780310000000000000003f920000000209300006c8800000000000855cddf9bdb000065088091fc6156487880000837162853c80001ab7004400000dc9d5328060000b70867843ba0000646000033a00000000000000007df000000003756000089e800035c00000bfb1b111a047c28f8191ba237c6f8c8b400003d9637e4000000000005dd000002a026940000000139000000000b8f899b1ac04ec48579f6f0000716839680001f8e00001cd92ba14606c50c77000000000000174800000002074c8f8000000000007128000000061e40001c9c35b61eb058794e91c8200000000000409e750c00008960000276475b1c354168857c51c8dc827b033681cb002b08aa31500001106269e26440000ac000000000ae98c993bba00008ef10fd0b8a0000ff58527298800010a20000000000008e285642c0c0000000072341b420b4000000000000280db3000008b61d244340000035c000084fa19100000000000000000000960f2600000000000000002b5409c000028a80003ca26a0c00000001f1c57ccf4aa02128520000000000000003ccc5ea8d2f3
  | 75 => 0x3a580000b47000020aa582481d851c1b5c000000000001b0a00003020dc705f471044ea99a539665bd400000002688562c0001fc70b0a0000000000000000000000176d26766ba8c3c125b059244843b31a2a1c141340c078e771050403079284cc0a042f685c2177d36086fc01e4a024273c023097a19bf1bca1a205f48a80423c2ffd0f5930d20b072a436012d11190042ca23800000002294000000000007424000213741f60c5813b0000309048a07c7800007a42c2817b889b37880000de885962c1c000000000000af800000001288053e61bd01820bd3f2014f03c7008700002210000178809fc1ff41e29f06089467d4d408f7f25f87dac0000000274031ec9e19981292624900000000000054800a6957013181bd8df1121a2e6e2cac0000000209e573ced8218f32060000b528000120a5abc4fc023d27f0000000000001a76513800000000efc4cbc9ac105700001ce8000143d2486211c1ec8db01d4843787178c113b6639102009118283e1dd06ae90f9160e77c83869524080e068c4609642142a1e4cd860a47235a6078f829ecf31027e3108c1c85382045ecba09b403b7642f0c9f0aee01aa020c26a8a0d1a8821d0bc595c216882330b250ea500001f04bfa0bdd00004fa8a8a189510fe05bc00000fd0a8a8628000066b00006f2800000000000183c000000000007ea06b480c53e7a00009c8800000000000034000009f20f58000186b33247a8485c000043ea000000013f629c6561cb8d13951a220aacba2000012e487900000d671db07bb8000049b0a666f5cd5813840000216c00000003ba48638b918c870dfc00009129f60412456507f7202216bc775005283562bfc6a98b1c0da5000071c8d6810fa24881cf052405c631b85b6cd2388a2168048980000c652298537c7fa0000144a6f5800000000ea838c800014a510f047c43f70000000000002500a8b0e3631f8233908000005e60394150f360e87981c3001b179c5aa00001a88000000000001cab328e0000000000000000000dae1d710abe5c50e031af2275e60c0e5b898a1da829d85859b5e1b345080d9300003e884328bbc869c243e24808d005e2253a0000e529b27355233d46479d8b000066bc00019d700002cdc52a8f2c078c680c5b90b06146c0d548ca1bb20b864234fac83e01eac7568384905b00004f4481f1dee05d8508cf78092c2dd40b2cbdf0ac2217e4574f298447184085c8304a0392b5c0000000000000000708aec07c3260855bc7701da4159c652076b01ba40cc3d64f5f0f53000055d82ee98e917204d8427b0000000001f87dc8000187e717c438967d078285988249f68287e00000000a910000514400013870b6800000001dec0174649ce7b00003cd400000001aad33306034def1a732da003105641966186a82acffc1b92240e1664
  | 76 => 0xb9298d20360240c8d417bc0000295c2b31d1d1bea6ab8000000000000000c508b4600000efc151a14c00002310f36190b367a58c887290b10ae43524784800028f8000078a1dc6381608246720ec10000000098895d600006fb82f7829739ac0000cff948026e43284e028000000017a8000000039020000ad203a6000053b800000001774879c000000012b600000000000000000000000000365e6dc10c28000000072f44940cf9199a263c67582e1176a4ddc4c29d6432a2000044d0000191c000000000003240000000000002ede5e9c613117638f20000a8080000000156cc0b8000000083802668183000013445c000000c6e000016600d2000025dc9759df8000081e03b00000051e00006389302108223d40e610d231da7860b20161842421a8417b170e00000000f3d8dc1293c0164f1601ea3ef42ea400000003e8c000091b1462154432282cf112338d61854c80987c1d2c11785d11056399a00008380fbe0000168c00013e9000038e04b99335106a00002051c3e000002b0932189a210441c8a618e901a6a6750e1d8000000014a0000000009e023e0000000000002c7c0161a0e12a26b0cab0125f19ee0daca8b17643e088054cec82b2020a4da8f061acb32d80c401c2167605e400000000000000076d092c1aaf000000487f1991636f2426c261811a39fa42ec50c11aa0c72037905499fa18547680402881832c87b7072e216b292c000000001de000014dc1299de5140e509cbd9800000002adce7191b40476000075189fe0f020bf0b600cf00000102086c000000000000710800000005b7c40807a3432e60d0000000000000000aa1182f1ca44ed84371c981b9848d000014d817608074e2395452f2800000001c123d12000000020a3280855c400020e430d805180000000000020240000000396218947a21705252e6858000000000005904c0d04392b7e0bd4a5d80000000394000009b0258c0000000000000000000000110000005fe000000000000000000002c500008274576000000000000000000000000788212000000000000f738cd40000641000019b4000000003d9216a1e2e16047fc81a2000000000001f20000009781f81528000073f8000056a00003bc40000cc73c687fa885b81bf2fa674d84618bc30cea4e6800019cd00006a180001c86233e789834ea1f700000000000000000000ee4c6b899e154c00000001d3439cc0000a73936730863e1c6371e33403c5fac76704c9116051b89a18d901ea00b6cf9481dd08c05f60ee19bb02cce36209e39829232462e80388f4f1da02d9cc1696bc069200009a1000000000e20000000033f0000000000000000000021017f517b200000000d0317367acc00012851c007c20e7e0610000000009f898b400002c6c2ab9c8e0000144c6730f5c24ac00000000000
  | 77 => 0x81de02560e76800022860c9c0001583275600009701dcd3d2e5ee4ba70000000000007bb80001e1840d4819946000001e2c4d48cdd000016503b68000033827f4b2a00001426605801d00001ca67ee000016ac081c0218e990612350e20881c390b60000762443b95f4300e296c0001079000000000001c763ea010c026b800000006b2000007dc09d400010758000431a0000c1188560b1e000000000000000454411085ce00001ae90bf80002dfe0aa0a230000319086e4c39000011d8726cee5128a000027c000000000be8000000008b43a821a2c5a6848d41223de0c088dd6000037640000000000000004d300000000000000000000000231909c00000a187430000000000000000c1300003b2200000001c5536a6209468a0000000000003630000408000000000aaf00000000000000000004f9400000000000084cd1f9bf2000000000001cce000035d067e95e700006dcc80886921546337000000003d72716c00000002b9a0cfc0b8114d412c00008a8000000001f28000118c3cda5f400470bdf434e5eb4c269a771da40e5c4e9105a000077040000f5a180e2a0c9c516b0115802900bd03ef00007fb10a5000028e001381000000000000000001fd039a20000372000000000000000205e0e004dbc0001b8b000000005689f701f468604478200500005224c7f86df0ac647c90600e1d000005d080c9bf500006c348b70a243f36000000020d61daa019ca379783000022189948ba42974439000017a605144b348c0871a00002e78f7d818a00000000dc9843200000000c1f133019e20000000000000000000e99800002960000aa1848401a63fcc000000027e80000000000028260264299078a438205e084483ed000000000000000000023d8ccb8000000000000000000137474484e88a8416981cd016f057d3cec727800019ab00000000bbc1332185837c8000000002d200000001362000000003468000000077bc000000011f6815cced207f3a5a4258b3d880701783cd448f800002560000da685cd004211940000000080c5550e5b191d000041f05378bf80fbe791c1779cb213c05f785d612f518b4535d0b219890ea000006401fe2404c7b8c5cd1e43015e3890ec808de1ec662d47ca02203c2a00000641c953a265714728800019a60000c8a19e3060c0430efa092700000c600240b0224b22a490869d20000000000000000261049b8419000000001ef047b86562bda000012ba16c0000000014ea01008b209b481297e300003dc4f970000315019644e78f470cee0fa800008403e3c84a425b1a05299a2fb455000001e4272ec89280003e4211ac8270ddc1cb2000000000001c343050000000000000000000000025a417306ea116000003f9800000002662207041a000001080000f1f1c00000015802519dd70000202
  | 78 => 0x3c5e100000c8e03b000000000000774c00010612be469508291b831b881b6502e0c72215852e0f2c03d83e0005fc000000000003958afe8000000000000001498000000000000d9b00006d84baa80000000009c5468afd000018d873816a706805428eb9194025507f0883a8000203664406c91ec700000000ffd96373cf826f0a319d3042a026b8a4a96dc30dc5c1cdf69ca43a9c52c043694cb185c0f940fd98bc3d0e3f680001eb417ee6a1000017820000000000000000000000000000000000482020e839a09f815c0ebf01430000800844b8000111440a4000000000000000dbf971900000000acb09b108460000240017c00000000000044e2a2077605031e37045e0ab09789e62205873785fe84ef145e1cd4000041b00003c0005a17b126d6000075e000000000000307006325ee6448c2809f1372e1da0000114900002f8ce328aab1c602248b701a28224c630c2b4133d3d1c2eb800018d830d053dc000100e3c3a39250229d6c11c029140001db2000065b40001d113914453c97198a92b5422e433611993cfe531c00010d626c64f24c7880ee1338541c3878c6821404d30eac926335a61af8bcc8a59043c4d4cb188c6d07e61540a970000190a34dc0000000000000000001bda000000000000000000000000000000000000000001109000000010c580000000000000007cc1a7a83b454a86c441bc6938f25000042ca00000001eb2000000006c7859206126acc000000000007b4404f8000000000000001b3f294e00005800047257800009aa00000000000024f0f6633d824c4b5f80000000000075c000004fc0000cc68000217c000000000002a7e0000000000043f400000001f1c0000440c0000000000068d0e41a1391bbe7cc0000201c000000002770000000040c0cab04e3000000001ac0ce109c4637cbfe0000225a00007258f3a0f800000fe90ef6180052b5087960a1b520000d648f423cea1c7c000066343646af0000100812ba0000abe11c7415869009b280e206de347cacb8b23370257e079717e600aa41782d3061a05020000a19800003243c0c97e800038fc666486180791e363af814a9d3e20827ff85dc9be602b84f34000000000000000bea8000000036c82a48000000000002260000161a61cc00013f72c0e000000000a200003bf80000000000042f40000e801b9685486d58000024c0000000000000000000da21a4a19500a18516097b01ce2858d469fbd090e1f39067950c2208107004b97f33ecc78d881c954d00006d587a5855a000008c84cf80ef0000345400003f130662c20000183121d014ec61d800010b8203c00005eb000000002c2206b358000000000990405687a0daa83a916120000d4d0f2900007c9c0001a1e0d481b4ca048000227e139416511f7009a837cad18f1c0000473404006e
  | 79 => 0x9df848e0d2e2d5c875000008340000a86a0a4000033f83a090953e1e01006d6055d00004c9c38e84fb275c29808c507ba0db800009d615302e6c00000000262000000000000e2232642090938191a39906b
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xcae7418b32440031e90cb8e64880031d19571cc9100043fc2aed192201487c855da324400187ce9b2c64880030f9d0658c9102f63d380cb1922000c3f655d23244001878caba46488003279d3638c9100064f3a0c719220028f8865c232440018f0cab8464880521fa17764c9100043ec2eec992200087f855d932440290f90abb264880022fe11764c91001c5e422ec99220008df835d932440011df04bb2648800e2fa10764c9100045ec20ec992205fc747119532440bd8f0e032a64880063da1b714c9100063a32ee299220028fa86dc132440018f0cbb8264880021fe15760c9100a43e42aec19220008bf845d8324400717908bb064880363720d760c91003c76412ec192200087e869d432440010f90cba864880021fe1f650c9100043ec3eca192201487f8719432440010fb0e32864880063d219710c9100147c432e01922060c7476d9551440298e8ec32aa2880067ca03735451000cf9400e4a8a2014c7476d4951440052e90ea92a2880029d21952545101ae3a3b2a4a8a2000d7250dd531440031e90cbaa628800279209754c5103063a3b6ca98a205ec74761953144001caeca31a62880025d614724c51000cf9400e498a2000de2201c931440053a90e9926288002b5219324c51000c7b436eb90a2000d72505d721440c18ecedb2e42880023d61e65c85102fd3b42ccb90a2000ae58299721440018eaea32e428817b1d9d865c851041e3b438cb90a2000c758719721440bf8ece432e428817f999c865c851041f39400cb90a205fe71801972144107ce06032e42880063da1b73c851000cf8402e790a20058f587d8b2144001ccecbb1642880063de1d62c85100053a42ac590a2000e646518b21440c38f0edb2aa0880531e1d86554110014f9408e6a822014c7876d4d50440032f10ea9aa0880029e21953541102363c3b2a6a8220029f281dc950440035e10ca8aa08800b3c1d951541100a73832aa2a822000dd0734c550440059e0ed90aa08800a3ea1b75cc110006b928aeb9822061c7a76d9730440011f30f32e608817a9ea1665cc1100056cc1ccb9822000c797519730440bf8f4ec32e608820b1ea1c65cc1100063cc38cb982205ec7a7319730440bdcb4e632e608820b9ca0465cc1102f738c08cb9822082e702119730440331f30fb1e608800396d9763cc1100147dc3ac79822000a788558f3044001cb0ca31e608800a7c20572cc11000d78432a398220589f3874c730440013e30f90e60880039c19721cc110006b928eea90220028f8865d520440013b106baa40881871e1db65481102fe3c3b0ca90220028fa869cd20440012f30a39a408800a7ca047348110006e9188e69022000e6b6518920440033d10e9924088002ba2193248110005f0412a290220009f0874c52044001f826498a408814a7ca1f2148110
  | 1 => 0x908bb2a6880023be097654d1003c76412eca9a20008fb805d953440018eca23b2a6880063e2007654d1006c3f43ecaa9a2000c3c74d9553440c18f0e1b2aa6880030f1d06554d102f63c380caa9a2000c3f65dd15344001878cbba2a68800a3ea1b7054d100063c32ee0a9a201487c855d853440031e90cb88a68800a3e2197014d100043fc2aed21a201487c855da43440031e90cb8c86880521fa177650d100043ec2eeca1a200087f855d943440290f90abb286880022fe117650d100046fc1aeca1a20008ef825d9434400f1d904bb2868817b1e1c06550d1006c5e43ac8a1a200da9c83591434400155904b22868800a3ea1b7050d100063c32ee0a1a20008bf845cf624400717908b9ec4880022fe11759891001c5e422eb3122000c3f845d6624400187908bacc4880021fa1f65589100061e3a6cab12200087e871956244001878e832ac48820f1ddc465589100061fb2ee8b122000c3c65dd162440018becbb9ac4880031719773589100062fb28e6b122000c5c651cd62440018e8423aac48800e2fa1f74589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fba8e6b122000c5c751cd624400193ee839ac488003271d07358910006563a6e4b122000ccc73dc962440018e8ebb8ac4880063ea1f70589100061f3a6ca3122000c3e74194624400187ecaba0c4880030f195741891000477c3ac43122000aac84588624400159906b10c48801e3b209741891003e56412e83122000cad74d08624400717d093b6a4880022f61276d491003c3e42aeda9220018f4865c752440298e8cab8ea48800a3e21970d49103063d386cb292205fc747119652440051f10cb84a48800e2fa1276549100045ec24eca92200087f855d9524400117f08bb2a48800e2f21176549100046fc1aeca92200d8dc835d952440011ef02bb2a4880521f21476549100147a408eca922000c7a501d9524400f0fd0fb2aa4880030f1d3655491030e3a38ecaa922000c3c7419552440bf8e8e232aa4880030fd9774549100061e32ee8a9220018f686dc552440018eecbb8aa4880031d19771549103043fc2aec292201487c855d852440031e90cb88a48800a3e21970149100043fc2aed212201487c855da42440051f10cb8484880521fa1776509100043ec2eeca12200087f855d942440290f90abb284880022fe1176509100046fc1aeca12200d8dc835d942440011df04bb2848817f1d1c4655091003c5e43ac8a122000a9c83591424400f55904b2284880063da1b71509100063a32ee2a12200087f855db32440290f90abb664880030f9d365cc9100061f3a0cb992205fc7671197324400187ecaba664880030f19574cc910006573a6c59922000
  | 2 => 0x72d95100051ec20e5b2a2061a79801cb65441098eeebb8aca880021fe1d65195100045fc22e632a20038bc845cc654400117f08b90ca8800e2f21172195100051f424ec32a2000a3d849d865440294e9033b0ca880529e20276195100a61fba4e832a2014c5f739cc654400147f08b98ca880028f21173195104153dc02e632a2000c79705cc65440bd4f501a18ca880029e60343195102fd3b4088632a2000a758110c654400147f08b90ca880028f211721951041d3bc0ae432a2000c75715c865440bf4ed03a10ca880029d60742195102f53d4008432a2000a798010865440010fd0fb2ac8880021fa1c65591100062fb2ee6b222000c5c65dcd64440018beca39ac8880031719473591100064e320e6b222000c6f65dc964440018d8cbb92c8880031bd94725911000636328e4b222000cac641c964440290fd0fbaac8880030fa1375591100061ec26eab222000c5f75dcd64440018b8ebb9ac88800317dd473591100062e3a8e6b222000c9f741cd644401b93d0839ac8880032715073591100064fa10e6b222000c6f75dc964440018d8ebb92c88800333dcf72591100066639ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c9644400f95d08392c8880032b150725911000657a18e4b22200387c855db544400747d09b2ea8880028fe1564d51100054e41ac9aa22000aac8259354440031e90cb8ea88800a3e21970d51100045ec24ecaa2200087f855d954440011bf06bb2a8880363720d765511000477c12ecaa220078ec825d954440070fd0fb2aa8880022fe1172d8d1001c5e422e5b1a20008bf845d6634400717908bacc6880030fe117598d100061e422eb31a200087e87d956344001878e9b2ac6880021fa1c6558d100061e3a0cab1a2082c7b70195634400187ecbba2c6880030f1977458d1000637b2ee4b1a2000c6c65dc963440018deca392c6880031b1947258d100063c180eab1a20038be87dd1634400187eebba2c6880030f1d77458d100061fba8e8b1a2000c3c751d16344001938e9b9ac6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100063c3aee0b1a2000c3e74d94634400187ce8328c6880030fd957418d100061e32ae831a20008df8758c634400153908b18c688002b32096318d1006c6e41ae831a200dc9c835d0634400193ae9a18c68800e2fa1276d4d100045ec24eda9a200d87c855db53440031e90cb8ea68800a3e21970d4d100a63c32ae1a9a2000a5d83d9653440c38ece3b2ca68817b1e1c06594d1000c7a432e329a2000c77655c6534400717d093b2a6880022f6127654d100043fc2aeca9a20008bf845d9534400717
  | 3 => 0x8a1e4000c7a65dc143c8001878e932aa5900031d1c66554b200061f32ee8a964000c3d65dd152c80018eccbb8aa5900031d5977154b200061f3a4cb9964000c3e7459732c800187ccaba665900030f59574ccb2003c3ec2aeda8e400787c85dd951c800117f08bb2a39000e2f211765472000c76412eca8e400287c8759551c80054e902b2aa3900031b59772547200145e43ac8a0e400087d869d731c80010ff0cbae63900521fe1e65cc7200043ec3ccb98e400087f8759731c80010fb0eb2e639000a3721d634c7200063ab8ca3b2a4000a798094765480014f30028eca9000e2fa1f74595200064fba6e6b2a4000c9c74dcd654800193ee839aca90003271d073595200066d080e6b2a407dc6f75dc965480051ed0fb8aca900032ddd371595200065a3a6e2b2a4000cd773dc565480019a8e7b8aca900031ddd471595200065bba0e2b2a4000cb4741c565480019aee638aca90003351cc71595200066c39ee0b2a400087f8759465480014e902b28ca9000237e0d76d512006c6e41aedaa24000a3d85d93544800117f08bb2a89000237e0d765512006c6e41aecaa240008f7815d954480051e902bb2a8900021fe1571d8d200a43e42ae3b1a4000a9d840c7634801b938c6ba4c690003275d36398d200046fc3ac631a40008bf845d4634800717908ba8c6900030fe117518d200061e422ea31a400dc5c835d463480018f700ba8c6900031e2017518d200063d082ea31a4000ad9808c4634801b0fd0b3b6a6900022fe1176d4d2001c5e422eda9a400da5c8359753480994e902b2ea6900029761763d4d200052ec28c7a9a40018ec865ca534800717d093b2a6900022f6127654d200045fc22eca9a40038bc845d953480011bf06bb2a6900023de057654d200147a40aeca9a40008fb805d953480778f0e132aa6900361f21d6554d2006d2e41acaa9a4046a7481595534806b8f0e0b2aa69001e3ea1b7054d2006c6e41aec29a40018ec865c8534801b998c6b90a6900363720d7690d2000c76432e521a400087f855d943480290f90abb286900023de057650d200147a40aeca1a40008fb805d9434801b17d0fb22869000e37a1f6350d200063a38ecaa924000c747119552480018f6cbb82a4900372718d74cc9200064eba6c7992400dcd8635c3324800117f08baec29000e2f21175d852000c7c402e7b0a4000c74611d561480014eb0bb0ea2900063ba1b725452000c76432e598a4000ccc764c9314800717f0eba6ca880030f5d254d95100061eba0a9b2a2000a3d879d3654400187f0eba6ca880028fa1074d95100061eba0e9b2a2000a3e84dcf654400147b09b9eca881869e60373d95100051f420e7b2a2000a3d841cf65440018bae639eca881829d60473d95100051f426e5b2a2000a3d84dcb65440c14eb03b96ca880028fa1
  | 4 => 0x44c00147b0bb26a8980021fe1576551300045fc22ecaa260008df835d9544c0011f700bb2a8980369720f65d4d300a63c32ae1a9a6000c3c74d95534c001878e832aa6980031e1977054d300065db26e0a1a6000acd83087624c0015d30010ec4980023be1d62189300045fc22ea31260038bc845d4624c00117f08bb6a49800e2f21176d493001c5f424eca9260008bd849d9524c0051ed033b2a4980023d60676549300061e3a6caa926000c7471d95524c001878e832aa4980031d1c4655493000c6e432e629260008bf845d7614c00717908baec2981163e61e65cc13022d6cc1ccb982600787c855d265c800f0f90ab9ccb900022fe11739972001c5e422e732e4014c74515c665c800147d0928ccb900028f61251997200a61fba4e932e4014c5f739ce65c800147f08b9ccb900028f21173997200053dc02e732e4000a3e849c665c800147b0938ccb900531ddc671997200a63a38ae332e403ba7a808c665c80014f30118ccb900028fa1031997200051ec206332e40038be87dd165c800f0fd0f2a2cb900030fdd254597200061fba0a8b2e4000a3e8494565c800147b0928acb900031ddc651597200053cc00a2b2e4000c3f76dd165c800187eec3a2cb900028fa1274597200061fba4e8b2e4000a3e871d165c800187d0e3a2cb900028fa1273597200051ec24e6b2e4000c5f739cd65c800f4dd0539acb900029da0673597200053ac0ce6b2e4000a3f845cd65c800147908b9acb900029ee0173597200051f424e2b2e4000a3d849c565c80018eee338acb900028fe1171597200051e422e2b2e4007a6c825c565c80018eae238acb900d69ea0071597200053cc00e2b2e4035a7a808c565c80014f30118acb900028fa1031597200051ec2062b2e4007a6e820c565c80014db0418acb900030fe1175d93200061e422ebb26400dc9e849cf64c8001938a939ec99001f27d0a73d932003e4ea14e7b264003a3c8459754c800147b0bb26a990002a7a0f64d53200045fc22ecaa6400787c8759554c800187ce932cc79001f1b9ca6598f200061f3a2cb31e4007c6e7259663c800fc9c64b2cc7900030f9957498f200061eb2ae931e40078dc835d263c801b93906ba4c790003275d34398f2003c6f43e86b1e401487e85dc563c80010fb0bb8ac7900022fe117518f2001c5e422ea31e4000c3f845d463c800187908ba8c7900022fe1176d4f2001c5e422eda9e400787f8759653c80014bf06b2ca7900031b5957294f200045fc22eca9e40038bc845d953c8001878e932aa7900ef1e1c26554f2003c3e43acaa9e4000c3c7459553c806b8f0e0b2aa7900030f9977454f200061eb2ee8a9e4000c7a65dc153c80298dccab90a79001f1b9c96590f2003c5fc3ac921e4000c6d655ca43c80778f0e132a87900362fa1f6450f2006d4f41ec
  | 5 => 0x81225ee1d53d415000d3c432a7a82a000e586354f505400147b0928ecaa00031d5c651d95400053cc00a3b2a8085c3f75dd165500018beea39acaa000327dd073595400064e2a0e6b2a8000cd873dc165500010ff0eb28caa00029720d65195400051ec24a232a80118bd87d97545002347b0fb2ea8a00030f61f65d514000c5fc3acbaa28000a9c8359754500df47d0c32ea8a00021fe1571d8d400a43e42ae3b1a8000a9d840c763500011bf0eb18c6a0002972156318d400056cc046231a8000a5d85d8f53500014bb07b2ca6a00062f2197494d400061fb2ae929a80038bc841d9535000317d0dba2a6a000e3ea1b7054d4006c6e41aec29a80018bc865d0535001b938c6ba0a6a00062fa1a7550d4006d4f436c6a1a800ea9e8718d435001b93d0e31a86a0003279d46350d400064e3a8c6a1a8000c9c63dc9435000155b0810ec4a0002ba60021d894000477c3ac431280008bf8750c62500011bf06bb6a4a00363720d76d494000c5e432e929280078f8865c252500051ed033b2a4a00023d606765494001c5e420eca928000c7471d9552500018e8e232aa4a00062fa1b74549400061fb2ee8a928000c3c65dd152500031790cba0a4a00062fa1a755094000cdd404eaa1280008be8718d425001b179093b664a00021fe1576cc9400a43e42aed99280018bc865d3325001b938c6ba664a0003275d363cc94003c5e424ed19280018bc865d232500031790cba264a00024f215744c94000cdc402e89928000c9d7418d32500031790cba064a001e3e219700c9400145e422ebb0a80018be86dd151500031790cba662a00062f21974c85400045fc22e532e60038bc845ca65cc00717d0fba2cb980031ddc651597300053cc04a2b2e6000a798014565cc001976e9b82cb980032e1d370597300051ec2ec9aa660008bf845d954cc00117f08bb6a59800e2f21176d4b300045fc22eca9660038bc845d952cc0011ef02bb2a59800a3d2057654b300063a38ccaa966000c747159552cc0018f2cbb82a5980021fe157650b300a43e42aeca1660008f7815d942cc0051e902bb2859801e2fa1f6450b300045fc22eca8e60038bc845d951cc0011df04bb2a39801e3b20976547300145e43ac8a0e6045a798699750cc0911f70eb2ea1981229ee1d65d43300063dc3acba866000e3b8459750cc001c7108b2ea19812e3ee1973d433025cedc32e7a866000cdb865cf50cc08b4f30da9ea19812e9ee1953d43300061eba4a9b2a6000a3e84947654c0018eae328eca980029e60051d953001c5f43ee8b2a6000c3f751d1654c0ff8beebb9aca98003271d373595300065dba6e0b2a6000cb874dc1654c0010ff0eb28ca980028f21165195300051f424a232a6000c3c641d5644c0290fd0fbaac8980030f1d774591300062e3aee6b226000c7875dc16
  | 6 => 0xcd3bc3acba8e4200c778759751c8401c6f08b2ea3908038d21165d47211e47bc32e5a8e423c9e7865cb51c84019cf0cb96a3908da9d61b52d47211e53bc32a5a8e4200c3d74953654840147d09286ca908029d60450d952101c5f43ee8b2a4200c3f751d16548401958e9b92ca908032ddd371595210065a3a6e2b2a420087f87594654840147908b28ca908028fa1250195210061e320eab22421487e87dd56448401878ebba2c8908031b1d772591210063a3aee2b224200a3d85d9354484010ff0abb2a8908022fe11765512100477c12ecaa242008f7815d9544840159b04186c690802b560430d8d210046fc3ac631a42008bf845d4634840717908ba8c6908361f21576d4d210045fc22eda9a42038bc845db534840717d093b2a6908022f6127654d2100c7d404eca9a42008f9809d9534840117f08bb2a69080e2f2117654d2100477c12eca9a42008f7815d953484011f700bb2a6908063e2017654d2106c3f43ecaa9a4200c3c74d9553484018f0e1b2aa6908030f1d06554d210063c380caa9a42028ec865c853484010ff0abb286908521f2157650d210047bc0aeca1a42008fb805d943484031f100bb286908362fa1f6450d210a63a32ae3a924200c3c74d955248401878e832aa4908031dd9771549210063a32ee2a924200cb764dc5424846d1eb0f32e42908dab960a65c85210045fc22ebb0242038bc845d760484290fd0bb8ac7a80529761e63d4f5006e2ec3cc7a9ea000d3a50dd153d40298bee7bb2a7a80034e1c37454f500061fbb0e8a9ea000d38701d153d40032f50fb82a7a80031eddb7054f50004bcc2ee0a1ea04cc7471d4d62d408d8e8e2a9ac5a80d69e2015358b500147b43ee2b16a00187c855d942d40011ef02bb285a800a3d2057650b50004bdc2ae1196a0008f7815d932d40051e902bb265a801e1f615760cb5006c3ec2aed98ea00097985dc131d4001938c839ac8a80022fe1172d8d5001c5e422e5b1aa06087f855c763540011bf0eb18c6a8002a72116318d500064e3a6c6a9aa000c9c7418d53540019b0c7b82a6a80030f1db7454d500069c386e8a9aa000c3c761d15354001a70e03a2a6a80065ea1f7054d5022e3c3b6e0a9aa00187c865d6435400187aebb2486a80022fe1173d895001c5e422e7b12a03ba788054f62540f98daebb14c4a80023be1d62189501ae3db2ee0a92a00187e86dd542540030f90cbae64a8003279d3638c9500064f3a0c7192a00787c859d8325400117f08bb064a800e2f211760c95000c3e432ea192a000c5d75d8c325400517d0fb2282a80361f21676cc5500045fc22ed98aa0038bc845db31540051b906bb662a80061f21975cc55000cbc402eb98aa000c5d75d8f31540051bd0fb1a62a80022fe1176c855001c5e422ed90aa0008df835db215401b1b906bb642a
  | 7 => 0xec825d262cc40f95904ba4c5988032b5d34298b3106c7743e84b16621487e85dc162cc4010fb0bb82c5988022fe1176d4b3101c5e422eda966200c5d655ce52cc40117f08bb2a59880e2f2117654b310061e3a4caa96624cc747199552cc401878e8b2aa59891b1d1c56554b310061f32ee8a966200c3d65dd152cc4018eccbb8aa5988031d5977154b310a62f32ae6296620dc5e7359642cc4018bacab9c85989331d1c66550b3103c5f43ec8a166207aae82d9142cc4018eccbb8a85988030f9d2658cb310061f3a2cb1966200c3e655d232cc40187acaba465988029d60650d95310063cb84a1b2a6200a7581143654c40717d0fba2ca98a0317dd7735953100657ba6e4b2a6200cac74dc9654c40195ee8392ca988032b1d0725953100673880e4b2a6200ce472dc5654c4031f50fb82ca988032edd370595310065c3a6e0b2a6200ceb72dc1654c4019d0e5b82ca988031edd470595310065dba0e0b2a6200cb8741c1654c4019d6e4382ca988033a1c870595310043fc3aca32a6200a7880594654c4011df04bb6a89881e3b20976d51310051ec2ec9aa262008bf845d9544c4011df04bb2a89881e3b20976551310047dc02ecaa262018f8805d9544c4018f0e1b2aa6988031e1c06554d310063bb2ee2a9a620087f855c3624c4290f90ab86c498802ab61020d893103e56312e93126200cad74d8a624c4011df0eb10c4988022fe11751893101c5e422ea3126200c3f845d4624c40187908ba8c49881f1b20975189310063bc0aea3126200c74815d4624c4018ee20ba8c498802b9606201893103c3f42ceda9262008bf845db524c40717908bb6a49881e9b20965d49311dd3c402cba926200a6d85d8b524c4014db0a316a49880a37219739493101c5f424eca9262008bd849d9524c4998e8e332aa49881e1f21d655493103d36412caa926246c7471595524c46b4f100b2aa49881e3b20976149310146e432e62926207ccc625cc524c40f1d904bb4849880a37219739093101c7743ec4a126207cac625d2324c40195ae9b1464988022fe1175d813101c5e422ebb0262018f4815cb604c4018f0c03aac0988022fe11739972101c5e422e732e42038be87dd165c840196ee9b8acb908032d1d371597210053ac0ca0b2e4200c7b7094165c84014eb02282cb908028f61764d53210045fc22ecaa642008bf845d463c840717908ba8c7908030fe117518f210061e422ea31e42008bf845db53c840717908bb6a7908363de197194f210045fc22eca9e42038bc845d953c84011f700bb2a7908063e2017654f210063c384caa9e420787c8759553c84018f0e0b2aa7908031d5977154f2103c5fc3ac921e420087f855d943c84290f90abb287908023ee017650f2100c7c402eca1e420d8be87d9143c846d4eb0d32ea3908e63de1d65d47211
  | 8 => 0xeb2ea8a0802ab20965d51413dd1f430cbaa282029b7875c7545040153b08186c6a0802b560430d8d410046fc3ac631a82008ef825db535040f1d904bb6a6a080a2f2197494d4106c7a432e329a82018fa809d953504011f3013b2a6a08031e1c36554d410063c380caa9a82028be86dd1535040187ecbba2a6a08030f1977454d41014db40ee8a9a82028bc865d0535040517d0d3aa86a080a6da067550d410043fc2ae1b12821487c855c3625040155b08106c4a08023be1d62189410053642ac431282008bf8750c62504015cb03100c4a08029b61762d494100536c16cb29282028bc865d2525040187ecaba4a4a080a6d20574949410145f436e8a9282038f686dc5525040f1d904bb0a4a080a2f219741494103e56312e829282028be869d5425040536d033aa84a08022fa1c635094103d57436c4a128218aae87189425040f95d0e31284a08032b9d46250941006563a8c4a128200caf73189425040536d0fb8a84a080a2f21974cc9410043fc2aed192821487c855da32504051790cba464a081f2b189748c941014da40ae91928200cad74d8a32504051790cba264a08024f215744c941014da40ae89928200cad7418932504051790cba064a081e3d219710c94100c5e422ebb02820d87c855d265cc40117f08b94cb9880e2f21172997310a63c282e132e6200a3e8494265cc40147b09284cb988530fdd274997310051fc22e532e6200a3c845ca65cc4014ef02b94cb988028fa1270997310051ec24e132e6214c78705c265cc4994ed03104cb988029d60620997310051f4204132e6200a3d8408265cc40717d0fba2cb988361fa1e54597310061fba4a8b2e6200c3f7415165cc40147d09282cb988028f61250597310053ac08a0b2e6200c3f76dd165cc40187eec3a2cb988028fa1274597310061fba4e8b2e6200a3e871d165cc40187d0e3a2cb988028fa1272597310051ec24e4b2e620da5e839c965cc4014f501392cb988029e60272597310051fc22e4b2e6200a3c845c965cc4014ef02b92cb988028fa1270597310051ec24e0b2e6200a3f845c165cc40147908b82cb988369720d70597312353b408e0b2e6200a75811c165cc4018f2e0382cb9891a9da0620597310053ac0c40b2e6200a3e8408165cc40147b08102cb9883697a0c20597310052ec1840b2e6200c3f845d764cc40187908baec99881f2ba1272d9331006562a4e5b26620dcaf439cb64cc41b95a87396c99880e8f21165d53310051ec2ec9aa66200aae82d9354cc40117f08bb2a9988361f21d65553310061e3a4caa9e6200c787099553cc40187ccbba2a7988030f5977454f310063d32ee0a9e6200c7965dc153cc40187ce932cc598837179ce6598b310061f3a2cb316620dc5e7359662cc41bc9e64b2cc5988030f9957498b310061eb2ae931662078
  | 9 => 0x51594320051f424a0b286400a3d84941650c8014ed02282ca190029d60450594320061fbb6e8b286400c3f761d1650c80147d093a2ca190030fdd274594320051f438e8b286400c3e871d1650c80147d0938aca190028f61271594320063bb8ce2b286400a3f845c5650c80147908b8aca1901e9b20971594320053d400e2b286400a79801c5650c8014f50118aca190029e60231594320051f424e0b286400a3d849c1650c80147f08b82ca190028f211705943206d2e41ae0b286400a76811c1650c8014eb02382ca190029da0620594320053ac0c40b286400c3f845d7640c80187908baec81900e8f21165d50320051ec2ec9aa064008bf845d9540c80f0f90eb2aa8190022fe1176d4c3201c5e422eda986400c3c74995530c8018f0e132aa6190030f1d16554c320063c382caa986400c3e65dd1530c80187acbba2a6190031e9977054c320063cb2ee0a9864008bf845db520c80717908bb6a4190030f1d265548320063a38ccaa906400c3c74595520c8018e8e2b2aa4190030f99774548320061eb2ee8a906400c7665dc5520c8018eacbb8aa41900e2fa13764c8320045ec26ec9906400c9e84dd9320c80193b09bb2641901f3394b764c83200667bb2a49906400cae84dd9320c80195b09bb264190373394f764c83200667bb2a69906400d7251dc163d44031f50fb82c7a88034d9477454f51006b928ee0a9ea20287c855d943d44011f700bb287a88063e2017650f510a43f42ee0b16a23ba788058f52d4401a6ca3ba2a5a88034d1c77454b510061fbb0e8a96a200d34711d152d448d8e8e2b1aa5a88d69e2016354b51014bb43ee2a96a200c7776dc552d44012eb0bb8a85a88034d94574ccb51004bbc2ae3996a200d36515d232d44011f700bb265a88063e201764cb51004bac2ee2996a200cac641c9645440117f08b96c6a880e2f21172d8d513f62ebaec731aa2008df8758c635448d8eecbb8aa6a880a1fa1b7550d510045fc22e7b12a2038bc845cf62544c30ff0ab86c4a88023be1d621895100556422c4312a200cac74d895254401958e8312a4a88033918b71549510061e3b6e8a92a200d3471dd15254401878ec3a2a4a88034d1c474549512663a38ec6a92a20297687dc5525446d8e8edb8aa4a880a1f21975909510061ebaec9212a200cae74d8b325440195ce831664a880a1f219758c9510045fc22ec192a2038bc845d832544050f90cba864a88031b5d7620c9511ccbbc3aa5a8aa202a748654b5154401cc8c4a96a2a88028f61250d95410063cb84a1b2a8200a7581143655050f87eebba2caa08031bdd4725954100657ba0e4b2a8200cac541c9655050d8eeebb8acaa0803391cb71595410043fc3aca32a8200a6c82594655040147b09280caa087e2f61f65d51410fd1ec3ecbaa28200c3d87d97545040517f
  | 10 => 0xb246400a3e850c1648c80147b0a182c91901eaba08305923200556c1060b246400ab6810c1648c80156b02182c919002ada0620592320055ac0c40b246407aae82841648c80155b05082c91901e2fe1d64d52320051fc2ac9aa46407cae72593548c80195ac8b96a91901e2f21d645523203e57392c9a9c6400cad645cb538c903c3cc9a9ca719003875935394e320063c384caa9c6400c7870595538c80117b0dba2a7190022f21d6454e320065c382c8a9c6400cba64dc1538c801972c9b82a7190032b5937250e3203f17292c9a9464378bd86dd1528c8551790eb22a5190032d1c56454a320065b326e2a946400cb564dc5528c85b17f0cba665190aa2fe1d64cca320064ebb4e99946400c9d765d3328c80195aed32665190032b5d964cca3201c5f426eab0c64008bd84dd5618c80717d09baac1190022f61375582320061eba4a9b2a64008bf845ce654c80717908b9cca990022fe11729953201c5e422e532a6400c3f751d1654c80196ee9b8aca990032d1d371595320065bba0e2b2a6400cb4741c5654c8019cee438aca990032edd370595320065c3a6e0b2a6400cf371dc1654c8019e0e3b82ca990032edd070595320065c3a0e0b2a6400cdb731c1654c8019e6e2382ca990033c1c470595320043fc3aca32a6400a3c84594654c801878c83aac8990521fa1f75591320061e218eab226400c3c421d5644c80187e823aac8990030fd0075591320061e3aee8b2264028f687dc5644c8018eeebb8ac8990031d1d771591320063bba8e2b226400c74751c5644c8031f50fb82c8990031edd770591320063c3aee0b226400cf371dc1644c8019e0e3b82c8990031edd470591320063c3a8e0b226400cf3711c1644c8019e0e2382c8990028f61764d513203c6e432e7aa26400c9f645cf544c81b1d90cb96a8990032bd9172d51320043fc2aecaa264008f7815d9544c8051e902bb2a8990023ee01765513200c7c402ecaa26400c3c74d95534c801878e832aa69901e2fe1d6490d320051e42ac921a64008bf845d9524c80717908bb2a49900a3d205765493200c7c402eca926400c3c74d95524c801878e832aa49900317d97735493206c5fc3ac92126400a3c85592424c80117f08baec29900e2f21175d85320045fc22ebb0264038bc845d7604c80f0f90aba4ca1901e1f21571994320051f424a33286400a3d84946650c80f0f90ab84ca190028fa1250994320051ec24a13286414c3f749d2650c80147d0938cca190028f61271994320a63bb8ce33286400a7a808c6650c8014f30118cca190028fa1270994320051ec24e13286400a7681882650c8014eb03104ca1900e2fa1f745943203c3f43ca8b286400c3f74951650c80187ee82a2ca190028fa1251594320051ec24a2b286400c7771945650c8014f50028aca190029e600
  | 11 => 0x508014bb07b2ca6a10063ea027654d420047cc04eca9a84008f7815d853508051e902bb0a6a1002a760e6590d4213c5ec3ec721a8414c3c655d352508018e8e3b2aa4a10031d1c465549420061fb2ee8a928400c3c65dd1525086f17b0f32c84a10deab60a659094201c5ec3ec72128400c9e73d8e42508011f700b9ec2a10063e20173d85420063a308eab0a8400c777194565cc8014f30028acb99036a7a0e61993320055d404c33266400ab98098664cc8015750130ac999002ae60261593320061fbaceab26640da9e839d564cc80147f0ab92c9990028f21572593320055bc0ae4b266400ab4815c964cc80157700b92c999002ae20172593320051f42ce2b266400a3d859c564cc81b53d0738ac999002a760e71593320055d404e2b266400ab9809c564cc80117d0f28ac9990022f61e515933206d4f418a2b266400a9d8314564cc8015750028ac999002ae60051593320055d40462b266400ab9808c564cc85b17d0e10ac9990022f61c21593320051f42842b266400a3d8508564cc81b53d0610ac999002a760c21593320055d40042b266400ab98008564cc80147f0ab82c9990028f215705933206d4e41ae0b2664008be8794164cc80117b0f282c999036a7a0c50593320054ec18a0b266400ab68114164cc80156b02282c999002ada0620593320055ac0c40b26642d8be8708164cc80117b0e102c999036a7a0f10593320054ec1e20b26640d8bf8759354cc80147f0ab26a999037279cd64d53320064eb22e7aa6640d8bc8759154cc81bc3ca6b26a79911e2f61b7454f3216c5e43ac8a9e6400cb87059153cc801974c9b82a7990032e5937054f3206e4f39ac9a966400c9d645cf52cc8018e8e332aa5990031d1c56554b320045ec36e8a9664008bc8759152cc801968e2b22a5990032d9937154b320065ab26e2a966400c9d64dcd42cc80717d09baac3990022f613755873201c5f426eab0664008bd84dd560cc8018f6e1282cb190029d604505963203d57414c13246400ab681982648c80156b03304c919002ada0660592320055ac0cc0b246400c3f759d5648c80f55d053aac9190028fe1573592320051e42ae6b246400ab7815cd648c80156902b9ac919002aee0173592320055c402e6b246400a3f855c5648c8014790ab8ac91901eab20971592320065ab88e2b2464008be87945648c80117b0f28ac91901eaba08515923200556c10a2b246400aba80145648c8015730028ac919002aea0231592320055cc0462b24642a8be870c5648c80117b0e18ac9190028fa1670592320051ec2ce0b246407aae829c1648c80155b05382c919002ada0670592320055ac0ce0b2464008be87941648c80117b0f282c91901eaba08505923200556c10a0b246400ab681141648c80156b02282c9190aa2fa1c30592320045ec3860
  | 12 => 0x23d61e20d85520055b42041b0aa400ab5840836154801968c3ba2c2a90022fa1f64585520045f438c8b0aa400cb676d906154801c6aebb20c2a9003ac9c3641855200758b86c830aa4008f587990615480156d09320c2a90023de1d641855200573c12c830aa400ab686190615480196cec320c2a90038d5d4641855200759380c830aa400eb17019061548011eb0f318c2a9002ada1263185520055ac24c630aa4008f78758c615480156f08b18c2a9002ad211631855200573c12c630aa400af38058c61548015e100b18c2a91329da1463185520071bb26a630aa400e3464d4c6154801c6ec8a98c2a90038d19153185520072bb1aa630aa400b708054c6154801d48c9a90c2a90038d19252185520055b424c030aa400ab58498061548015cb05300c2a90038dd9250185520071a324a030aa400e706094061548012eb0e280c2a90038dd9050185520071a320a030aa400e3a50d93605480187aea326c0a90038e94064d815200739286c3b02a45fc767518760548018eaea30ec0a90039c94061d81521ac3ec3ea7b02a435a7a80d4f605486b4f100a9ec0a90022fa1f64581520065a38ec8b02a4008be871916054801968e2322c0a900327d9373581520064e326e6b02a400c9f641cd6054801938c839ac0a90033618073581520065bb26e2b02a400cb464dc560548011ed0fb0ac0a90032ddd361581520065a3a6c2b02a400cd773d8560548019a8e7b0ac0a90023da1c61581520065bba0c2b02a400cb47418560548019aee630ac0a9003351cc615815203c6e41ae9318a414c5f535da53148778f0e132aa6290023ee017650c5200c7c402eca18a400c3f76dd1521480187eec3a2a4290031dddb71548520063bbb0e2a90a400d34741c5521480195eedba2a4290032bdd8745485200673bb6e2a90a400ce7761c55214801b48e838aa4290028f61250996420051ec24a0b2c8400c7b7094165908014eb02282cb210de8f61a65d52421d45fc3acbaa4843aa3f87597549080187f0eb2ea9210022fe1973d52421ec5fc32e5aa4843d9af865cb549080195f0cb96a921002a760f5498e420052ec2860b1c8400a9d840c1639080f59d04182c721002b56043058e4201cd6422e5a9c84008fb805d953908031f100bb2a7210031e1c26554e420063c382caa9c8400c3e65dd1539080187acbba2a72100327dd26354e420066c384c6a9c8400cd87058d539080135b053aa872109e2f61b7250e420051ec24a3b2a8400c757194765508014f30028ecaa100a3da1f71595420065bba6e2b2a8400c77751c5655080196ee838acaa100339dc871595420043fc3aca32a8400a7481594655080193886b98caa10023ee01731954200c7c402e632a8400a3d8494465508010ff0ab8ec6a10521f21571d8d420046fc3ac631a84038ec865cb53
  | 13 => 0x45f43863b22a4008bd870c7645480117d0e10ec8a90de2f61c21d91520051f42843b22a400a9e83087645480153b0610ec8a9002aea0021d91520055cc0043b22a400a3d85dc3645480117b0f286c8a9002ada0450d91520055ac08a1b22a4008be870c3645480117b0e186c8a90028fa1430d91520051ec2861b22a400aae820c3645480155b04186c8a9002ada0430d91520055ac0861b22a400ab681883645480156b03106c8a90022fa1c20d91521bc5ec3841b22a400cb464dc5645480157500308c8a9002ae60061191520051ec2cc0322a400ab681980645480156b03300c8a90028fa1850191520059ac08a0322a400caf641c954548019c8c2392a8a90029761430d8d5200566c1061b1aa400cb671d92635480196ce2324c6a90032dd917198d520065a322e331aa4008be87d916354801968e3b22c6a90032e1c36458d520045f438c8b1aa400cb4711916354801970e0322c6a90032dd937158d520065a326e2b1aa400cbb64dc16354801970c9b82c6a900237e1d6318d520056c402c631aa400c3e7619353548990f90cb8ea6a91331d18571d4d520070fb26a729aa481e1c64d4e5354901ca8c3a9ca6a90022fa1b7454d520065a30ee8a9aa4008be87d915354801970e1b22a6a9003361c36354d520066c380c6a9aa400ce4611c95354801976c9b82a6a90032e1937054d520067830ee0a9aa400e3461dd15354801c68c23a2a6a90034e1c36454d520069c380c8a9aa47ee5461dcd5354801ab0e1b1aa6a900387d906354d52006ac380c6a9aa400e6461dc95354801a5ee8392a6a9003991847254d522363a30ee2a9aa43597a87dc15354801ce0c3b82a6a90034edd07054d520069c3a0e0a9aa400d6b721c15354801ce0c2382a6a90023de057690d520147a40aed21aa400c74619d643548018e8c2bac86a90030f9d76490d520061ebaec921aa400caf649ca43548019c8c339486a9003391857290d520147b40eeca1aa4008f581dd943548f96d100a9ea4a90038bd9362949520047dc02e7b0aa4018f8805cf615480156d0931ec2a9002ad61263d85520055bc22c7b0aa400ab48458f61548015e700b1ec2a9002bc20163d85522363b3b2a7b0aa400b708054f615480156d09306c2a9002ad61260d855230e3b3b4a1b0aa400976871436154801c6ea92a6c2a9002ada1273d85520055ac24e7b0aa400af3805cf61548015e100b9ec2a90029d61473d85520072ba9ca7b0aa400ab78454f615480156908a9ec2a9002bce0153d855200578402a7b0aa400e675294b61548014eb0bb86c2a9002ada1250d85520055ac24a1b0aa4008f687143615486d1eb0e286c2a90023da1c30d85520047ac3861b0aa400a76850c361548014eb0a186c2a9002ada1030d85520055ac2061b0aa400ae6820c361548015cb04186c2a9
  | 14 => 0xa830876054c015b30610ec0a98032e18374581530045f43ec8b02a6008be871916054c01974edb20c0a98038e5d764181530075938ec8302a600eb171d906054c011f30f320c0a9802aea1264181530047dc3ac8302a600adb835906054c015750c320c0a98032e9d864181530071cba8c8302a600eb2711906054c01d62e2320c0a9803a619353181530071c324a6302a688e5b6394c6054c011f30f310c0a9802aea1262181530055cc24c4302a6008fb875886054c0157708b10c0a9802ae211621815300579c0ac4302a600af0815886054c011f30f308c0a9802aea1261181530055cc24c2302a600ad9839846054c011f70eb08c0a9802aee1161181530055c422c2302a600aeb825846054c015d104b08c0a997a9e21461181530053d434a2302a600e3b649446054c01c70c9288c0a98039cd8651181530073830ca2302a600979871446054c01c76c8288c0a98038e19051181530061fbb6e8a98a600c3f761d15314c018f6edb82a6298031edd87054c530069c3a0e0a98a60dc5f85dd95314c298b90bbb2a62980327ddb7454c530064fbb0e8a98a600cdb76dc15314c019b6ec382a629803661d07054c5303c76412e9310a600a3d849466590c0147b0928acb218031ddc651596430053cc00a2b2c8647a3d869975490c9517f0eb2ea92192a8fe1d65d52430061fc3acbaa4864d8bf865cf5490c9b33f0cb9ea92180327e1973d52430045fc32e5aa48600aad82d526290c014db0a10ac521802ab6102158a4306d6741842b148600ae9800856290c0147b09286caa18031e5c250d95430053ac08a1b2a8681c5f75dcd6550c031f50fb82caa18032edd370595430063dba8e0b2a8600cbb741c16550c019b6e6382caa18021fe1d65195430053c402ca32a8600cac425c86550c011ef02b90caa180a3d20572195430051ec24a032a8600c7870d955350c018f0e032aa6a18030fd977454d430061e32ee8a9a86478bd879964350c8f53b0732c86a180e2f61e43d89430055741487b12860087f855c36250c290f90ab86c4a18023be1d62189430047bc0ae5b0286028f4815cb6050c018f0c03aac0a18529761e63d4f5206e2ec3cc7a9ea400c3f761d153d488d0fb0db8aa7a911b1d9877154f520069dba0e0a9ea400d38741c153d480753908b1c87a900e3721d6350f521dc3e43aa6b06a43ba788054d60d48012db05baa8729002cbe1153d4a523edb4402a7a94a4018fa80dcd61948011f301b9ac3290028f61641d91520055d400c3b22a400ab980187645480156d03306c8a9002ad60660d91520059ac08a1b22a400a3d851cf645480155b0439ec8a90028fa1471d91520051ec28e3b22a400aba801c764548015730038ec8a90022f61e51d91520055d400a3b22a400ab98014764548015750118ec8a9002ae60231d915200
  | 15 => 0x2b10c4aa0023ee0173d855400c7c402e7b0aa800ce4611c961550011ef02b96c0aa00a3d20572d81540066c300e6b02a800b1f845cb5394d0363908b96a729853561c170d4e5306e2e39ea6b14a60dc5c73d4d6094c051ed03b92c1298023d60772582530051ec2c81b22a600aba809876454c015730130ec8a9802ce60051d91530055b408c1b22a600ab5811836454c0147b0a396c8a9802a760c72d91530051ec2ee3b22a600cb7719c76454c0117b0f28ec8a9802aea0051d91530055cc00a3b22a600aba808c76454c015730118ec8a98022fa1c31d915323c5ec3863b22a6008be870876454c0117b0e10ec8a98028fa1421d91530051ec2843b22a600a9e830876454c0153b0610ec8a9802aea0021d91530055cc0043b22a600a3e851c36454c0147b0a386c8a9802ada0470d91530055ac08e1b22a6008bd879436454c0156d02286c8a9802ad60450d91530045f43861b22a6478bd870c36454c0147d0a186c8a9802aba0830d915300556c1061b22a600ab6810c36454c0156b02186c8a9802ada0620d91530055ac0c41b22a6008be870836454c0117b0e106c8a98032e19370591530051ec2cc2322a600aba809846454c0157301308c8a98028fa1851191530059cc00a2322a600ab6811806454c0156b02300c8a980327d9073551530066c300e6aa2a600e1f64d8e5354d03c38c9b1ca6a98029b61421d895300566c1843b12a600cba70d926254c01974e0324c4a98032ed9170989530065c322e1312a6008be87d916254c01968e3b22c4a98032e1c364589530045f438c8b12a600cb4711916254c01970e0322c4a98032dd9371589530065a326e2b12a600cbb64dc16254c01970c9b82c4a98023be1d62189530057240ac4312a600e3651d936154c0187aea326c2a98038d94464d85530045f43ec8b0aa600cb870d916154c0117d0e322c2a98032e1c0645855300657b26e4b0aa600cac64dc96154c0195ec8392c2a98032b190725855300672308e4b0aa600cbb64dc16154c01970c9b82c2a98023de0572d81530147a40ae5b02a600aba8498b6054c0157309316c0a9802aee1162d81530055c422c5b02a600af38158b6054c015e102b16c0a9802aea1261d81530055cc24c3b02a600abb845876054c0157108b0ec0a9802bae0961d815300574412c3b02a660c7a769476054c01ce6c328ec0a98025ea1c51d81530071daa4a9b02a600e5b5394f6054c0157509396c0a9802ae61272d815300579c0ae5b02a600af0815cb6054c014f30a396c0a98029e61771d81530055d424a3b02a600ab9849476054c011f50e28ec0a99163e61c51d81530047cc3c63b02a600aba840c76054c015730818ec0a98023ea1c21d81530047cc3843b02a600a7a850876054c014f30a10ec0a9802aea1021d81530055cc2043b02a600ad
  | 16 => 0x80080200500000000080581200001800001100000500480080100080000180180380300080080480880000300880300000500000601980000181480200100300000000500000280580480700300180100181380380000a80100a00880180000000180100c00500180300180082580100780000080380d00000200180280280100000200000100000b81300000180800280100400700300c80000600f01e80000100380080102700700000400000001000000100980000180080000180400300f00000000200100380800481200180000480000380000b00300080400101480700100400d80300200001180580000100100080000080000300000081080300780280101100180b80180280580100300000080000100000000a80280280200000200c00801080900080181600100180080500400080000201500080080080a80080283100181300080180300000080000080300080200100180080401301000001380101580280800080700480081480180a00280780480100000680380081180e00380000300180080000100280100000400180400200000300000c80400481280000180202380000000480580000401f00100680400b81280180183880201380000100100700700380180480080000000000200100280180000080000400001d00080000f00400381c80080180000180e80000a80081000000400600000100200080080000081680000480100481000080880000380500400600900180000180080180000080000d80381680080280b80380280101580180680100100080100900000500000000000b80180080580300100080000080000380000000b80780200600300400000000000200180480480600301400100100081100180300400480002880000280000980200081280080300180280700680a80600002600000000380200880000100000080080080a00500780b80000300501180b80700380300200780680000002300c80080000580100000700100380780000600300180800080680980080900080100180180000580000000000000300080000000080080900081380600200100a80000880000100100700680000300780000080880000300600700080000280480a80000e80380500100800580080880500100500780400000280c80280080180580000180280000180780080800100280380300600380000600400400700900200000502980200180180000480d83180280500000900000780080101200580200300600800500000200400880500100000100200180280400080f00b80000000880000b00401e00000600200600080000000080e80780c80e00080080800000d8020029761430d8d540054ec2061b1aa8008df8758c63550015b100b18c6aa0029b61421d895400556c2043b12a8008ef8758862550015c90
  | 17 => 0xdd0da1d704467ae188840070c81307f16dcd781a13e39d840004d814800008c65ae2c180bc0c80002998000a380003ac0d04c0e34f1d880004dc7bb2cf09a40004f23b688d03840022988cb444e3f51941dec5c02d100021840000000002058c900db07814144b05db110887cc163141de0000000000000173821a0002d68000b9063b31e086c054000270000053c21c0000000abe19d0eb00008120000001d4087c1e20001d100000001060000bca0ce2e618e400053422b800010c0003be94c84104eb12581c8cd60700029710f521d324d21fcb3a8111682104aa412915685044de23212d182027c6a80099914f7c40605c85a0b206fe077a0482d47e53ad95701d062223698a48343340a11b7cd6625b0340000fe82292b98b350f873316f96e0bdc78620790443b270c0510bbced487d39d9758ae434e09e19a4f108a23a71b250e04b9315885c65c3151b5970c38e132000000097c1963249f5490c0cc000048c0006342f889784e46da2a79284ea67a00001d3cd126e626a12245b000017f800000065a42a201000047917700008a455b3ed88787e243604793048f64bf34008588c847e25700008c47ec0081a1cec43d2378852c9ac8051b91c041120d919a8a2c3dc6672e493b0a3a7240849c406c20002118cec0002ae1fe00004608a60119d18000585055a00892610118f02944980003fc830025e12637a800004c08c43200003623640001f5072a1f900a000000066033800340001c817501b87c62a23c3800017e1620730ca47ae0000000000fcc00026589940787ea0d40e0c16686208d95d079000c35487f800054e26480004d455400015c0bf669d40006680000b843380000000000001b908a689e3931cf08b61e81801b003920000b9a03c20e6ba00013d80000d200000009b206a2e79ca482c4d342c000073a6bb1e28000d2a0000000a5c0002c00000d7cf2a8b00cc96c456a15e1d520a85104b5353a050b4a4460c411800ec11534ca13815c69e2218d6d06823c22b00003a018c0548a2400015a1f08000258000273000000089a0001a1066434841617bc9e21e644d8f643008242c106480003bd0001884af685d29c1cc00007de2d499f03e0000331814cbf011d090000000008205a1368dd65c204f1b8c71469f0bc1a3c7bc0002a115e0b142662ab1fe03ca47f0e601808bc41d1fb000037014c02e9d280007cc1819ae40000001338000ad88ac01680080000980000000500200980080000f80600000080000580100000000100100600181280000200d80901300801380000780300000000480100080280680180280b00000200000000400000200000680780000400300480180380100080d80000780b00780000200000200100380380100400580500c80380200000580180100800a80001280000100400000102e006
  | 18 => 0xdcc4fc301065800080483c3330000000000000015054e87141d047c9c22ce0ea174cf1c65f0001dfc1c600040c800000069a1c380007a861a192000000039b1d21840c0000021600cc5ac00044b99d4b5627406a1a0882a6513e105a4f7412b33504cc81800034b02a048400025213780982193c5962d1005b2422020c9a44b00c69d5013849d0001b38f8667b3ee9a902ec5a82ff9edcf946903889c548a00523209748c263712e08204a4a62438e8a643f03d500e0a8079c16e14d15e4b327690bb971d0ca31603691bc30229800e9a0c61044d25689c50d806c35c17d454c5bc1cf99a078474d195995c4f84c820983d414281f128800d12058f3e89ac43a225613c973403c2593a107046721b915f86cc8b44e5222007c47c3090f78b8c3300003a885ec4f64a522a044c0001ea0909f2cbcc30b000069035857a1c420286ca78c1488c5d1027f03130410cf228100016480006920be1afccb20001f1123ca3e2110579bcc8562c93669f887e664203e9638dce08b10108eca864a7068000000050721c80000000002481940010782336872d0f000012f9bdc1261f3116826c1dc00032003d84da7ab3901b4cebe61629b1f400be6ef1d121a87564b61ce03148cc73a000077c0000da0000acc01e3ed3e208a8e6e1180c21b94f9284a00010a053675731aa13070414a0b185841ca22c1c7059800000a0f58c805e47a51a587681b04e30000a900762e12c222c46ce70528a926d08400410217880003c63b40f1c1da8a50d81b190b80440000000f780000000a8c1300003bb164c524381000000106c28c00000000006c84568b88d0c7d62891bf06781911bb93dce163272979b507e83763ba0fb8d302731a3057c9e838d36d83a48540473e785accec84304d179ce368b41090be06180fd4289cb42e05de4231bb8ebc3e84521ed426a2430091a20bb24a30871eb4bbe0d708a1de8ba05610631b4450654a1e005101c20591e616ecab05a33cb0b64a4802e05b0be8d4044a1081a2865827d25791d4c6e22204e9ab0f2036c3780ac081c4731588000b7216d457853cc667412c8800079204f33120d4ece00024e22706247d307600011102f51130814cfc0921199ef40ee2c72e281680006611da1f8c9f67e734284482346940fe18940fe0000001d00c960000001438fae2fb00013e498c42e000000000022007c11642b039e41403cc0000000ae0000f5067d1a888ac1784822ba800027e0c122a9690cfe1462e304d101600029e8000a1017f00014240000000a895640007ed0980000c3c7840001e8451e2e73990d4cd607d814e01bc0008010ba945cc0c7fd44a9aa90f403f19785e47b60f100008f51283c10000d1c0006550001e88b583c33d3883448e3d329aa26400059c01a0000f363ad4421b80722342428035497671a2f4009c7706
  | 19 => 0x3f800004e800038b2b50000f701312f5a1cc5ae5f033200000006813061f3482822e1ff84302060690000954b746c129d86b483252310c16f44708630581c20c2446701e8d885d849708893a85e256e2130ba0d4c62a403159806000015a000000000001b010000072e2420ca90a61bd2f2175c80a3ba000127c7c864704380000504d1020908905e00001c06150705e105318646747144390fb000000008c94a08ba521000120c59046c16219c400000023822600006740cd8984dc20a7223a1480005e91179ea87be1e73328380a302a91551c84b184d52d1165c43481c02f181448a6d81529f80d6c1cd2f6863cc744371851db8e2e4ba3cd215463817e27e09483524613d19d1c09c57719b8fdcca88931768b784c66c32bf0a08e9050f37921b400052c00000008d40fc2da149d08018744709346a00000000000dfe000179820000005b00021b847e1650000988000203000030cada2950a71b885b64252a309000004c3012959038088b000140c0000a01a19048bfc0002149a840000942681010f125ea0ca9b58c2a45f19c0000b2a636381892901a0000000790000476112000012200012400011667e93270000b5e73840d13b800000000018506601ba42c9ddc54244b1aa20780e80000111080e620001428a0040c81b00020acb362490b798046260001340dfc0004330f18000fbe3962cf800021642141f2060d8e82910a800104a00000015444ec4ce21682f408a3922821fd514e4851a2131cfa488f2531fb877e62f17c837c76409925b9af852630f21f81285f848841b8d30e441722720c8410a04d06998b400005700014e50ac28722781987205f217f0500a020ff00000000008271d60000ae20000000a185580003518ff4df40000000f343bc0003a580005ba60a3011040f2e5653da068c9d240725e0580ee413b36a983c16407b1b18a740d608820f1408aba07c1bf000009622500000008e467a000010800069b4540000bb823a23282c40007fa3fd8000000139255000000029626206d40000000001d30000079237000000072a41c80000005fd38499c819212e000000000074941e800000000005d8c6c00037a23c124869400000013fc0005cb22090c800087b00018b81e48763089ec407c4f532f0ef8f0a44c00002e8f1a545003818c00000000c9308ff84b41868e3c04202026e98c47d23b624f09e82d807512306800c411e2a39a344620004558c7505c4803f90850680000000100cee25622f1852092a55a0328ee453e59a0e218c002250019b1c48e1c4963591e70eaa50d40ea13ca884ca178000000012430d80682ae7b22ec000012e5aa0001f386d400b0001db107e8a138990d43ba07e13a942c00c6ab25589e06c024f2fa169cdae26b0a495250c054b21e03582c828d105876c9fc2a82fb1fd80004f02c30
  | 20 => 0xb988e22fd3e086948ee8490f9078502e00000020247b002d0e71b64a320000001c94e000002d9983510c5c00b39a7056c4e70000000000145329000091a1f11271488ade3fe3691be08487f30000e808e85111ab823822000042d944c0000000000000f663ea1d194dc0001d212a1bec7081be061150458a0002069f70d8443d36204b46925300001e60b427c50e5208099a3851d28000c580000fa921c6fa89126f84187f66e81f80b5097a2d22b39b2ce6803a09416000000673d620c4000587000083c7d657615e10ec000000000133040e20900003e8f4c78f3f8902c8fa4ed1ba1c585d643117a2274a9088702812649de0950ae80000007e13261418f223d10aa80007528890001c08a7e66c1f292cca1864a3869810f244cf3cc87d82542d30cfa234cb686f2211e50c5089224612500f022809c06780003552201abc75e71e128031c30c65315b9ba857039932c16d82f454c35e8980a7464414708d911431f1ae8054ef01ab35a8db80720241659a4406a86b1f3051c9d02370fea0842047062bf85c4c9a0960fb91ac31402916110289521a700d8e5d0cc2cc31f1df0d448221b8102076a369365189d01c3b33371e0c0e231a1e80388f7e8791381d8c0ac52a31e8d342a68301ed1f189588331989f90b4c08a15d0dd474e5682a9897402e57c376a01d0d07233b2202003080c2c08000be645129000006080a33b01d480007282fe12c40007b62601c70b7e85f00022140000b50ffa20801c72c004a27c7507c839e97503440cf2e88420d2e7b01bd8f28f1451417200006b800018116f800000008e1970cde3b010080011184303979388bba1d73b8208cdfa3a607c834457c793374a1208007452b00b04e6a7430db993c1ba6431828f110bc8ae35a175480223931015780c21430878b9464c48e00006f000000032e8fe40f44a800000011061b238380c4ad24983ad0a10b6a84d2a80904e6c6ec0000e2432e0001a280008680000000aecdf20f70e290bc15a1fa28f0120a5651a0d700008b00cd2b586389445632d006fc83e032109978066600010ea0980a200027984d8d8a5ca3d7a11459e0002ca0d64c461902968e843da2350000fe90ea0902138f7419087e0ba0000a2073e00017e45860001830000d2600010518fcf0272b1360970c3851b20d96c0ede4f802e21dc3e84c51bc06246da2530e18b6835e1173b5895d0766b71af19dc6462c62c482345ee0e418c00001587731f7800000010a3f792280004481f38b281bc68e1590000aaa0002970da0f3e63837b1cfc0002ab0001c280002dc1ad0edc9b60e720b800000070f0938e500007f72340000bd800000012c80000000a6810c0002b91c60f702440002348000000000000135c02c7eb0001e78000000000000000029407a0000e3e0002fd1660000718062064d146
  | 21 => 0x1f648f83580ce191861c6d00000000c2e12509b8c8800000004f86ec0b00002249ffc2b682d293029000000000000000006ae3ae80ac2a47a442b9a2c83000019f862d15273916aa0c800220e188032839e0000000458de85963939b780005292a00c640000000be800016e0002c401cc0000ea1b300000008b200000005ec61d00004f467a00000007ec38c000000000114043800009900000003ac811800027f1b787b102a00030f800060e53c0001df8ce600000000005140003b30cf8d5a00002aa168970775000122c0006181c998c800089622e204075c8030ab06d864a58d2ed22a87c03791ab14581f67560ee1b3108e41c15e8ba46a46780f00eec88a7790ec18386f81541eb0f3c3d253e0ca05640927c00160e68e086a51c0091030679d00011e820a6cf000113834c4a03c01ff80000be346000000084b3ed0000cac00021d00000005570000000c1220024094289b82771cc15349f486924886a806e0dc1e580000000001f900010e860336e15f49fa7e80ea82103040aa2fb80002a07b90758abce32765000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2202a10ed005824a4000e0000001cf2e6b021e000b2050c198dba2a6a10c8904000b0c81000401c31755c764181530070c5d5711906054c0183987d9051181530060e61c641446054c01271981847054d520070cdd0611c15354801c30741847054d5200718dc8611c153548018727620153d85520070c5d570d906154801c31755c064185520045c65c8054c6154801a336420153185520068c1908054c6154801a536320153185520060d61f6414061548018358719050185520054c640711d1525440142c955d0624c9410051c640815d4624c401531911c07454d50005072557418d3250001077985c471597200051c644805d46348001464925c572195102fc1d25c86549514400107496614724c5102f41e25c8654d50440010789661473481100067021d324c520440016c0964c93148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x63250004010200303198dd0611c15354801818cc0e8308e0a9aa400c18663721847054d520040e3533b100a9ec2a900303197d908054c6154801818cb8c8402a630aa400c1465f632015318552
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x5
  | 4 => 0x94d
  | 5 => 0x98a
  | 6 => 0x98d
  | 7 => 0x3
  | 8 => 0x150a
  | 9 => 0x150d
  | 10 => 0x9ca
  | 11 => 0x9cd
  | 12 => 0x168a
  | 13 => 0x4
  | 14 => 0x168d
  | 15 => 0xa0a
  | 16 => 0xa4a
  | 17 => 0xa4d
  | 18 => 0x198a
  | 19 => 0x198d
  | 20 => 0x6
  | 21 => 0xb09
  | 22 => 0xb0d
  | 23 => 0x1549
  | 24 => 0x154d
  | 25 => 0xb49
  | 26 => 0xb4d
  | 27 => 0x16c9
  | 28 => 0x16cd
  | 29 => 0xb89
  | 30 => 0xbc9
  | 31 => 0xbcd
  | 32 => 0x19c9
  | 33 => 0x19cd
  | 34 => 0x3c9
  | 35 => 0x3ca
  | 36 => 0x3cd
  | 37 => 0xcc9
  | 38 => 0xcca
  | 39 => 0xccd
  | 40 => 0x15c9
  | 41 => 0x15ca
  | 42 => 0x15cd
  | 43 => 0x1709
  | 44 => 0x170a
  | 45 => 0x170d
  | 46 => 0xd09
  | 47 => 0xd0a
  | 48 => 0x1609
  | 49 => 0x160a
  | 50 => 0x449
  | 51 => 0x44a
  | 52 => 0x44d
  | 53 => 0xd49
  | 54 => 0xd4a
  | 55 => 0xd4d
  | 56 => 0x1649
  | 57 => 0x164a
  | 58 => 0x164d
  | 59 => 0x1a09
  | 60 => 0x1a0a
  | 61 => 0x1a0d
  | 62 => 0xe89
  | 63 => 0xe8a
  | 64 => 0x1789
  | 65 => 0x178a
  | 66 => 0x5c9
  | 67 => 0x5ca
  | 68 => 0x5cd
  | 69 => 0xec9
  | 70 => 0xeca
  | 71 => 0xecd
  | 72 => 0x17c9
  | 73 => 0x17ca
  | 74 => 0x17cd
  | 75 => 0x1a49
  | 76 => 0x1a4a
  | 77 => 0x1a4d
  | 78 => 0x1049
  | 79 => 0x104a
  | 80 => 0x1a89
  | 81 => 0x1a8a
  | 82 => 0x209
  | 83 => 0x8a
  | 84 => 0x1409
  | 85 => 0x128a
  | 86 => 0x249
  | 87 => 0xca
  | 88 => 0x1449
  | 89 => 0x12ca
  | 90 => 0x1849
  | 91 => 0x1489
  | 92 => 0x180a
  | 93 => 0x130a
  | 94 => 0x2c9
  | 95 => 0x14a
  | 96 => 0x14c9
  | 97 => 0x134a
  | 98 => 0x409
  | 99 => 0x1889
  | 100 => 0x589
  | 101 => 0x18c9
  | 102 => 0x138d
  | 103 => 0x124d
  | 104 => 0x8d
  | 105 => 0x128d
  | 106 => 0xcd
  | 107 => 0x12cd
  | 108 => 0x749
  | 109 => 0x14d
  | 110 => 0x1949
  | 111 => 0x134d
  | 112 => 0x40a
  | 113 => 0x188a
  | 114 => 0x58a
  | 115 => 0x18ca
  | 116 => 0x20d
  | 117 => 0x140d
  | 118 => 0x24d
  | 119 => 0x144d
  | 120 => 0x74a
  | 121 => 0x2cd
  | 122 => 0x194a
  | 123 => 0x14cd
  | 124 => 0x1a0d51
  | 125 => 0x1a1651
  | 126 => 0x1a4ed2
  | 127 => 0x1a57d1
  | 128 => 0x1a57d2
  | 129 => 0x1a57d5
  | 130 => 0x15692
  | 131 => 0x2d551
  | 132 => 0x19d4d1
  | 133 => 0x1a9951
  | 134 => 0x19d4d5
  | 135 => 0x1a9952
  | 136 => 0x17da51
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2627
  | 6 => 8702
  | 5 => 2229
  | 4 => 31
  | 3 => 7
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
  | 7 => packedAt gbK7 (107699+((h/875+packedAt gbK7 (97199+(h % 875)*12) 12) % 3814)*13) 13
  | 6 => packedAt gbK6 (458296+((h/2900+packedAt gbK6 (417696+(h % 2900)*14) 14) % 12635)*15) 15
  | 5 => packedAt gbK5 (140427+((h/743+packedAt gbK5 (131511+(h % 743)*12) 12) % 2675)*13) 13
  | 4 => packedAt gbK4 (2230+((h/10+packedAt gbK4 (2170+(h % 10)*6) 6) % 41)*6) 6
  | 3 => packedAt gbK3 (575+((h/2+packedAt gbK3 (567+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffc1f00ffff80f07fffffe0005e3b1ce8fc3fc
  | 1 => 0x1fe000f80fffff83f007fff1a7c5e710cfccf
  | 2 => 0xfffffff000ffffffc0007fffe380607ff0ff0f
  | 3 => 0x1ffffffff000fffffff8000fc007f81ff0ff0
  | 4 => 0x1fffffffffff00000000000ffff8001fff000
  | 5 => 0xfe0000000000000000000000fffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2ac05082993983026953720600e190c685c15c
  | 1 => 0x214a0105a84a95483a0554aa086c16510c54c5
  | 2 => 0xcc94b69010952a96800a29546380602ab0ab0a
  | 3 => 0x41272b2962020ce514ac0018bc006b015a0ea0
  | 4 => 0x89f9cdce7ce7c04218303060dfb68001eff000
  | 5 => 0xf0000e004004008420c04180f75b7dfc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeee0fac0eac0feeeeee0fac0eac0feeeeee0fac0eac0feeeeee0fac0eac0feeeeee0fac0eac0feeeeee0fac0eac0feeeeee0fac0eac0feeeeee0fac0eac0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37195
namespace PEqualNP.Outside.L_meta_37195
open PEqualNP.Outside.L_meta_37195.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 92 := (concat bs1_4_0 (concat bs1_4_32 bs1_4_64))
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
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bs5_4_0 : Interval s5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1 := bs5_4_0
theorem alls5 : ∀ k ≤ 4, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 7 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 31 := bgb_4_0
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
theorem bgb_5_2208 : Interval gbAtlas 5 2208 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2229 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)))) (concat (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))))) (concat (concat (concat (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344))) (concat (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))))) (concat (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)) (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))))))
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
theorem bgb_6_8672 : Interval gbAtlas 6 8672 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 8702 := (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))) (concat (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896)) (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)))))) (concat (concat (concat (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312))) (concat (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))))) (concat (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856))) (concat (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984)) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))))))) (concat (concat (concat (concat (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400))) (concat (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688))))) (concat (concat (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944))) (concat (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 bgb_6_3072)) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232)))))) (concat (concat (concat (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360)) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488))) (concat (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616)) (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776))))) (concat (concat (concat (concat bgb_6_3808 bgb_6_3840) (concat bgb_6_3872 bgb_6_3904)) (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 bgb_6_4032))) (concat (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 bgb_6_4160)) (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320)))))))) (concat (concat (concat (concat (concat (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 bgb_6_4448)) (concat (concat bgb_6_4480 bgb_6_4512) (concat bgb_6_4544 bgb_6_4576))) (concat (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 bgb_6_4704)) (concat (concat bgb_6_4736 bgb_6_4768) (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864))))) (concat (concat (concat (concat bgb_6_4896 bgb_6_4928) (concat bgb_6_4960 bgb_6_4992)) (concat (concat bgb_6_5024 bgb_6_5056) (concat bgb_6_5088 bgb_6_5120))) (concat (concat (concat bgb_6_5152 bgb_6_5184) (concat bgb_6_5216 bgb_6_5248)) (concat (concat bgb_6_5280 bgb_6_5312) (concat bgb_6_5344 (concat bgb_6_5376 bgb_6_5408)))))) (concat (concat (concat (concat (concat bgb_6_5440 bgb_6_5472) (concat bgb_6_5504 bgb_6_5536)) (concat (concat bgb_6_5568 bgb_6_5600) (concat bgb_6_5632 bgb_6_5664))) (concat (concat (concat bgb_6_5696 bgb_6_5728) (concat bgb_6_5760 bgb_6_5792)) (concat (concat bgb_6_5824 bgb_6_5856) (concat bgb_6_5888 (concat bgb_6_5920 bgb_6_5952))))) (concat (concat (concat (concat bgb_6_5984 bgb_6_6016) (concat bgb_6_6048 bgb_6_6080)) (concat (concat bgb_6_6112 bgb_6_6144) (concat bgb_6_6176 bgb_6_6208))) (concat (concat (concat bgb_6_6240 bgb_6_6272) (concat bgb_6_6304 bgb_6_6336)) (concat (concat bgb_6_6368 bgb_6_6400) (concat bgb_6_6432 (concat bgb_6_6464 bgb_6_6496))))))) (concat (concat (concat (concat (concat (concat bgb_6_6528 bgb_6_6560) (concat bgb_6_6592 bgb_6_6624)) (concat (concat bgb_6_6656 bgb_6_6688) (concat bgb_6_6720 bgb_6_6752))) (concat (concat (concat bgb_6_6784 bgb_6_6816) (concat bgb_6_6848 bgb_6_6880)) (concat (concat bgb_6_6912 bgb_6_6944) (concat bgb_6_6976 (concat bgb_6_7008 bgb_6_7040))))) (concat (concat (concat (concat bgb_6_7072 bgb_6_7104) (concat bgb_6_7136 bgb_6_7168)) (concat (concat bgb_6_7200 bgb_6_7232) (concat bgb_6_7264 bgb_6_7296))) (concat (concat (concat bgb_6_7328 bgb_6_7360) (concat bgb_6_7392 bgb_6_7424)) (concat (concat bgb_6_7456 bgb_6_7488) (concat bgb_6_7520 (concat bgb_6_7552 bgb_6_7584)))))) (concat (concat (concat (concat (concat bgb_6_7616 bgb_6_7648) (concat bgb_6_7680 bgb_6_7712)) (concat (concat bgb_6_7744 bgb_6_7776) (concat bgb_6_7808 bgb_6_7840))) (concat (concat (concat bgb_6_7872 bgb_6_7904) (concat bgb_6_7936 bgb_6_7968)) (concat (concat bgb_6_8000 bgb_6_8032) (concat bgb_6_8064 (concat bgb_6_8096 bgb_6_8128))))) (concat (concat (concat (concat bgb_6_8160 bgb_6_8192) (concat bgb_6_8224 bgb_6_8256)) (concat (concat bgb_6_8288 bgb_6_8320) (concat bgb_6_8352 bgb_6_8384))) (concat (concat (concat bgb_6_8416 bgb_6_8448) (concat bgb_6_8480 bgb_6_8512)) (concat (concat bgb_6_8544 bgb_6_8576) (concat bgb_6_8608 (concat bgb_6_8640 bgb_6_8672)))))))))
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
theorem bgb_7_2624 : Interval gbAtlas 7 2624 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2627 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)))))) (concat (concat (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600)))) (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 (concat bgb_7_1728 bgb_7_1760))) (concat (concat bgb_7_1792 (concat bgb_7_1824 bgb_7_1856)) (concat bgb_7_1888 (concat bgb_7_1920 bgb_7_1952))))) (concat (concat (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112))) (concat (concat bgb_7_2144 bgb_7_2176) (concat bgb_7_2208 (concat bgb_7_2240 bgb_7_2272)))) (concat (concat (concat bgb_7_2304 bgb_7_2336) (concat bgb_7_2368 (concat bgb_7_2400 bgb_7_2432))) (concat (concat bgb_7_2464 (concat bgb_7_2496 bgb_7_2528)) (concat bgb_7_2560 (concat bgb_7_2592 bgb_7_2624)))))))
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
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 40, 42),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 36, 37),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 5 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeee0fac0eac0feeeeee0fac0eac0feeeeee0fac0eac0feeeeee0fac0eac0feeeeee0fac0eac0feeeeee0fac0eac0feeeeee0fac0eac0feeeeee0fac0eac0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071584 * 2 ^ 32 + 4206947008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37195.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[3,5]⟩,⟨.and,[0,7]⟩,⟨.and,[1,5]⟩,⟨.or,[6,8]⟩,⟨.or,[8,9]⟩,⟨.or,[3,4]⟩,⟨.or,[1,10]⟩,⟨.and,[11,12]⟩,⟨.or,[2,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4206947008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4206947008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37195

open PEqualNP.Outside.L_meta_37195 in
theorem PEqualNP.Outside.L_meta_37195 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4206947008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4206947008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
