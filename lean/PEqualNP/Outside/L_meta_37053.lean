import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37053.Model
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


end PEqualNP.Outside.L_meta_37053.Model

namespace PEqualNP.Outside.L_meta_37053
open PEqualNP.Outside.L_meta_37053.Model
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

def SBf (j : Nat) : Nat := [6, 7, 4, 4, 6, 6].getD j 0

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

def mirrorSteps : List Move := [swapRows 50,swapRows 84]

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

end PEqualNP.Outside.L_meta_37053

namespace PEqualNP.Outside.L_meta_37053
open PEqualNP.Outside.L_meta_37053.Model
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
end PEqualNP.Outside.L_meta_37053
namespace PEqualNP.Outside.L_meta_37053
open PEqualNP.Outside.L_meta_37053.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1450a802b4e000005200800388d0221a14318486d289087cb91244c00b0000d00003c01e2c00000005418000040260084e80002002c0e005000000c8c1c082440100680000e103800204100ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21ee21fd21fc21ec21f421e421ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x40f80e001cc4a181909c7a331301cd8030117400110f988a219111f8525b0e990de05001b8d4611b1ec34711e1dc72683e96814132300046001b9d4e04e0011450172494cae66001d8f2002580074000419cb80026010a0060f0bc000000100a4121883048001f000846d0000076590008440000786c88651a9e8860d17000822a058d0386b000b060001f800a814001a4be013c0b4bc15390589e001c120ac00159341258239fcc6553a181004a03808100098084080283818501000504810004828204819101850000000486050001190302870280060b0a5b94b43b6a96877651d0eeaa3a1db94a43b6a9487765190eeaa321e750c43af29e855d53d0aeca3a15d54742bba8a85745150a7ca9994f55332bb28e657551ccaeea2995d14532af29e835d53d06dca5a0db54b41b7a92836c525067ca998cf55331b7296636d52cc6dea498db14931bb28c436e51886cca310f948421b728843e651087ce8210f990421f2a0843e441087ce6210f98c421f298843e431086eca410f994821f3a1043e642087ca8410f910821f399043e632087ca6410f90c821f3aa043e654087caa810f915021f3a9843e653087caa610f914c21f3a1843e643087ca8610f910c21f3a8043e650087caa010f914021f210e81e421902bea6a05714d40b7a92816c52502eea2a05d14540f210a815e53102baa6205b94840b6a90817651102eaa2207908440f210e61e4218c27ea8984f15130b7a92616c524c2eea2985d14530f210a613e540c27aa8185b94830b6a906176510c2eaa2187908430f210e417651882eaa31079086209faa2413c54482bea6905714d20bba8a417451483c842907908420f210e216e52842daa50879086109faa2213c54442bea6885714d10b7a92216c52443c842887908410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1200189b00000080161c800f801900119d000a82800d001d88159e000000000008800000000015000000000011020001800c05a08b830000000793948b002180070500040d8f0109000616800000001800001f899c038c9b80001280109a8e9f00100e211e931a170a142004868000001980000017808004043000e180010038081040800100004009918552d0e646254743991855290e646254643b198f41086c563d0421a999331086a564cc421b198f42086c563d0821a999332086a564cc821b198f54086c563d5021b198e54086c56395021c955054086a664d4c21a959353086a66494c21a959253087455314c2199997430866565d0c219999643086656590c21e150c43086a76454021a919150086c76354021b118d50086a66414021a959050086c66314021b158c500866661d49409998b515026665085409919421503475308540d114c2150264615484099189511026765084409959421103465308440d154c211026661d49309998b514c266650853099194214c3275408530c9150214c264615483099189510c267650843099594210c3265408430c9550210c3275408520c915021483475308520d114c21482646114910c9d5021443245408510d1d4c21443445308510
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
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
  | 5 => packedAt s1K5 (825+((h/15+packedAt s1K5 (720+(h % 15)*7) 7) % 72)*7) 7
  | 4 => packedAt s1K4 (3827+((h/43+packedAt s1K4 (3483+(h % 43)*8) 8) % 155)*9) 9
  | 3 => packedAt s1K3 (2738+((h/22+packedAt s1K3 (2584+(h % 22)*7) 7) % 118)*8) 8
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffffffffffc0fffffffffffffff0fffff
  | 2 => 0x1fc0fc0fe07e07fff0f07c1f03e0f81ff53267
  | 3 => 0x1fff000fff8007ffff007fe003ff001ff9c387
  | 4 => 0xe000000ffffff83fffff800003ffffe0fe03f8
  | 5 => 0xfffffff00000003ffffffffffc000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc04208002104000001108c21186108c10054ab
  | 2 => 0x4a9631964728aa9cb074351a29a8d15a753265
  | 3 => 0x930c5aaa8a1d352d57085b4852da429cb9c386
  | 4 => 0x1a28a34d1451a1b66aad0210831ce708de0350
  | 5 => 0x1c30c38e1861c63b8cce639ce0108410efa800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37053
namespace PEqualNP.Outside.L_meta_37053
open PEqualNP.Outside.L_meta_37053.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffff03ffffc183fffe0ffffc1ffff0073f3fc
  | 1 => 0xf83ffc1f07fffc3c1ff0f03fe1e07ffaccccf
  | 3 => 0xf003fffe007ffffc01fff003ffe007ffcf0f0f
  | 4 => 0x3ffffff801ffffe000003fffff801f00ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x210011842000200442601118c022310c01515c
  | 1 => 0xa225228c84a90941d0a90a2952145254a4c4c5
  | 3 => 0x454a45106952129c2152a052a540a4a94b0b0a
  | 4 => 0x4a7388294c1b5ceab41888833999c031f00ea0
  | 5 => 0x8c630e318e639f33399ccce0311100c1fea000
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaeeaacc00eeaaeeaaeeaacc00eeaaeeaaeeaacc00eeaaeeaaeeaacc00eeaaeeaaeeaacc00eeaaeeaaeeaacc00eeaaeeaaeeaacc00eeaaeeaaeeaacc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37053
namespace PEqualNP.Outside.L_meta_37053
open PEqualNP.Outside.L_meta_37053.Model
def s3K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (6+((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffff03ffffc183fffe0ffffc1ffff0073f3fc
  | 1 => 0xf83ffc1f07fffc3c1ff0f03fe1e07ffaccccf
  | 2 => 0xf003fffe007ffffc01fff003ffe007ffcf0f0f
  | 4 => 0x3ffffff801ffffe000003fffff801f00ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x210011842000200442601118c022310c01515c
  | 1 => 0xa225228c84a90941d0a90a2952145254a4c4c5
  | 2 => 0x454a45106952129c2152a052a540a4a94b0b0a
  | 4 => 0x4a7388294c1b5ceab41888833999c031f00ea0
  | 5 => 0x8c630e318e639f33399ccce0311100c1fea000
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeaeaeac0c0eaeaeaeaeaeac0c0eaeaeaeaeaeac0c0eaeaeaeaeaeac0c0eaeaeaeaeaeac0c0eaeaeaeaeaeac0c0eaeaeaeaeaeac0c0eaeaeaeaeaeac0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37053
namespace PEqualNP.Outside.L_meta_37053
open PEqualNP.Outside.L_meta_37053.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x80be40bc40
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
  | 0 => 0x1ffffe03fe1f087fc3fc3ffff0fe070133f7cc
  | 1 => 0xe07c3ffc3fffff83fc3fc380ff0ffffeccc8ff
  | 2 => 0xff803fffc01ffffc003ffc00fff007ff0f0f0f
  | 3 => 0x3fffffe00fffffc00000fffff803f00ff0
  | 5 => 0xffffc00000000fffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xc31802388422100cc04c048e701231181153cc
  | 1 => 0x4900444890080101441441121104924844c055
  | 2 => 0x842aa8910d548ab4222aa824aaa044b30b0d0a
  | 3 => 0x165331222906acdaaa822048ccc96023b00ea0
  | 5 => 0x186221c33198cf6333333270088180c3eea000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37053
namespace PEqualNP.Outside.L_meta_37053
open PEqualNP.Outside.L_meta_37053.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x20be40bc40
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (34+((h/1+packedAt s5K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1ffffe03fe1f087fc3fc3ffff0fe070133f7cc
  | 1 => 0xe07c3ffc3fffff83fc3fc380ff0ffffeccc8ff
  | 2 => 0xff803fffc01ffffc003ffc00fff007ff0f0f0f
  | 3 => 0x3fffffe00fffffc00000fffff803f00ff0
  | 4 => 0xffffc00000000fffffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xc31802388422100cc04c048e701231181153cc
  | 1 => 0x4900444890080101441441121104924844c055
  | 2 => 0x842aa8910d548ab4222aa824aaa044b30b0d0a
  | 3 => 0x165331222906acdaaa822048ccc96023b00ea0
  | 4 => 0x186221c33198cf6333333270088180c3eea000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeeeaecc0eeeaecc0eeeaecc0eeeaecc0eeeaecc0eeeaecc0eeeaecc0eeeaecc0eeeaecc0eeeaecc0eeeaecc0eeeaecc0eeeaecc0eeeaecc0eeeaecc0eeeaecc0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37053
namespace PEqualNP.Outside.L_meta_37053
open PEqualNP.Outside.L_meta_37053.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x6000e8042e00220c50abd261002e6a60016000048066a0bb96cbc58a10a9d004e0001f000800000f078c76006be0070740490cd0062012916eb118064650423c416a6246c000000000000000340c381821404000040850002380850000001007f95001fd54007f15001ff52007f94801fd52007f14801ff42007f90801fd42007f10801fe32007f4c801fc32007fd0403fe41007f50403fc41007fc8403fe21007f48403fc21007fd0001fe40007f50001fc40007fc8001fe20007f48001fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x824000ffd0120017fc8090003fd4048005fe2024000ffcc120017fc6090003fd3048001ff9024000fec8120017fc409000bee204800dff8824002ff04120017feca1000aff6508005ff3284005bf99420017faca10002fd6508005fe3284002bf19420017fec81000aff6408005ff3204003bf99020017fac810002fd6408005fe3204002bf19020007fea810003fe5408001feaa04000ff15020017fec61000aff6308005ff3184000bf98c20017fac610002fd6308005fe3184002bf18c20007fea610003fe5308001fea984000ff14c20007fe8610003fe4308001fea184000ff10c20005fcc410003ff5208001ff2904000ff54820007f8a410003ff4208001ff2104000ff50820007f88410003ff3208001ff1904000ff4c820007f8641000bff6108005ff3084001bf98420017fac210002fd6108005fe3084002bf18420007fea210013fe5108001fea884004ff14420007fe8210013fe4108001fea084004ff10420007fe6210013fe3108001fe9884004ff0c420007fe4210013fe2108001fe9084004ff08420015fcc01000bff5008005ff2804002ff54020017f8a01000bff4008005ff2004002ff50020017f8801000bff3008005ff1804002ff4c020017f8601000bff2008005f79004002ff88020017f4401000bfd2008005f69004000fe48020017fe201000bfc1008005ffb242002bfd9210017fcc90800efe6484005feb242000bf59210017f8c90800afc6484001ff2a42000ff55210007f8a90800bff62840057fb142002ff98a10005fcc50800bfd62840017eb142002ff18a10015f8c508003ff5284001ff2942000ff54a10007f8a508003ff4284001ff2142000ff50a10007f88508003fe3284001fe9942000ff0ca1000dfac308007ff4184003ff20c2001ff5061000ff88308007ff2184003ff10c2001ff4861000ff8430800afe6084005ffa042002ff90210017fa810800bfc4084005ff9042002ff88210017f4410800bfd2084001fc9042002ff08210017fe210800bf71084003fd8842002ff04210017f02108003ff64440017fb222000ff9911001dfcc888003fd64440017eb222000ff1911001df8c888003fe5444001feaa22000ff15110007fec488002ff6244001ff3122000bf98910007fac488002fd6244001fe3122000bf18910007fea488003fe5244001fea922000ff14910007fe8488003fe4244001fea122000ff10910007fc6488003fd3244001fe1922002bfd851000ffe8288007fe4144003fb20a2001ff50510007ea8288007fc4144003ff90a2001ff8851000ffa4288007fc21440037fb022000ffd0110017fc8088003fd4044005fe2022000ffc8110017fc4088003fa2044001fe9022000fe48110017f84088007ff1044003fd8822002ff84110017ec208800bfc1044005fa0822001fe04110
  | 1 => 0x3ee52c8001fea964000fb54b20007f8a590003ff42c8001ff2164000fb90b20007fa8590003ed42c8001fe2164000ffccb20007fc6590003fd32c8001fe1964000ffd8720047fcc390006fe61c8001feb0e4000bf58720047f8c390006fc61c8001ffa8e4008ff94720007faa390023fc51c8001ffa0e4008ff90720007fa8390023fc41c8001ff98e4008ff8c720007fa6390023fc31c8001ff90e4008ff88720007fa4390023fc21c8001ffa864002ff94320007faa19000bfc50c8001ffa064002ff90320007fa819000bfc40c8001ff9864008ffc4320017f8219000bff65880057fb2c4002ff9962002dfccb1000bfd65880017eb2c4002ff19620015f8cb1000bff64880057fb244002ff9922001dfcc91000bfd64880017eb244002ff19220015f8c910003ff5488001ff2a44000ff55220007f8a91000bff63880057fb1c4002ff98e20005fcc71000bfd63880017eb1c4002ff18e20007fea710003fe5388001fea9c4000ff14e20007fe8710003fe4388001fea1c4000ff10e20005fac510003ff5288001ff2944000ff54a20007f8a510003ff4288001ff2144000ff50a20007f88510003ff3288001ff1944000ff4ca20007f8651000bff6188005ff30c4001bf98620017fac310002fd6188005fe30c4002bf18620007fea31001ffe5188001fea8c4007ff14620007fe831001ffe4188001fea0c4007ff10620007fe631001ffe3188001fe98c4007ff0c620007fe431001ffe2188001fe90c4007ff08620015fcc11000bff5088005ff2844002ff54220017f8a11000bff4088005ff2044002ff50220017f8811000bff3088005ff1844002ffc8220017de4110003fb2088005ff8844002ff04220007feca90002ff6548001bfb2a40009fd9520007fcca90016fe6548001feb2a4000bf59520007f8ca90016fc6548001be32a40009f19520007fec890002ff6448001dfb224000afd9120007fcc89000efe6448001feb224000bf59120007f8c89000efc6448001de3224000af19120007fea890003fe5448001feaa24000ff15120007fec690002ff6348001ff31a4000bf98d20007fac690002fd6348001fe31a4000bf18d20007fea690003fe5348001fea9a4000ff14d20007fe8690003fe4348001fea1a4000ff10d20007fea490003fe5248001f72924000ff54920007daa490003fc5248001ffa124000ff90920007dc8490003fd4248001f6a124000ff10920007fe6490003fe3248001fe9924000ff0c920007fec290002ff614800dff30a4001bf98520007fac29001bfc61480037e30a4000ffd4520037fca290003fd514800dfe28a4000ffd0520037fc8290003fd414800dfe20a4000ffcc520037fc6290003fd314800dfe18a4000ffc8520037fc4290003fd214800dfe10a4000ffd4120017fca090003fd5048005fe2
  | 2 => 0x40007fccaa0016fe6550001feb2a8000bf59540007f8caa0016fc6550001be32a80009f19540007fea8a000ffe5450001df2a28000ff551400077aa8a000ffc5450001ffb1a8000bfd8d40007fcc6a0003fd6350001fe31a8000bf18d40007fea6a0003fe5350001fea9a8000ff14d4001ffe86a0003fe4350001fea1a8003ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0002fc6250001ffa928000ff94940007faa4a0003fc5250007ffa128000ff90940007fa84a000ffc4250001ff9928000ff8c940007fa64a0003fc3250001ffb0a8000bfd8540057fcc2a0006fe6150001feb0a800aff1854000df8c2a0003ff5150015ff28a8000ff54540057f8a2a000fff4150015ff20a8000ff5054001ff882a0003ff3150015ff18a8000ff4c540057f862a0003ff2150015ff10a8000ff48540057f842a0003ff5050005ff2828000ff5414001ffe80a000ffb4050005ff2028002ef90140057fe20a000bfc1050005ffb288002bfd9440017fcca20016fe6510005bf32880009f99440017faca20002fd6510005beb2880009f59440017f8ca2000afc65100077f3208003ffd50400077ea82000ffe5410007feaa08003ff1504001f78a82000bff6310005ff3188000bf98c40017bcc620002de6310005feb188000bf58c40017bac620002dd6310005fe3188000ffd4c40007fca620003fd5310001fe2988003ffd0c4001ffc8620003be4310007fea188003ff10c4001f78862000bff6210005ff3108000bf98840017dcc420002ee6210005feb108000bf58840017dac420002ed6210005fe3108000ffd4840007fca420003fd5210001fe2908003ffd084001ffc8420003be4210007fea108003ff1084001f788420003ff3210001ff1908000ff4c840007f8642000bff6110005ff3088001bf98440017ecc220006f66110005feb088000bf58440017eac220002f56110005fe3088002bf18440007fea220027fe5110001fea888009ff1444001ffe822000fbf4110007ff2088003ff504400077a822000ffc4110001ff9888009ff8c440007fa6220027fc3110001ff9088009ff88440007fa4220027fc21100057f3008002ffd4040017fca02000bfd5010005fe2808002ffd00400177e802000bfe4010005fd2008002ff500400177a802000ff94010005ff8808002ff04040007fecb90002ff65c8001ff32e4005bf99720007facb90002fd65c8001fe32e4005bf19720007fec990002ff64c8001ff3264003bf99320007fac990002fd64c8001fe3264003bf19320007fea990003fe54c8001feaa64000ff15320007fec790003fe63c80017f31e4000ff58f20005fac790003fc63c80017e31e4000ffd4f20007fca790003fd53c8001fe29e4000ffd0f20007fc8790003fd43c8001fe21e4000ffd4b20007fca59000
  | 3 => 0xe2a24200ffd8d21005fec690803df63484016fb1a4200ff98d21005fcc690803fd63484017eb1a4200ff18d21005f8c690803dc63484016e31a4200ffd4d21007fca690803fd5348401fe29a4200ffd0d21007fc8690803fd4348401fe21a4201bfd8921007fea490803fe5248401fea924200ff14921007fe8490803fe4248401fea124200ff10921007fe6490803fe3248401f71924200ff4c921007da6490803fc32484037fb0a4201ffd452100ffca290807fd5148403fe28a4201ffd052100ffc8290807fd4148403fe20a4201ffcc52100ffc6290807fd3148403fe18a4201ffc8521007ee4290807fe2148403f710a4201ff0852100fd84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024202bf1812100ffe2090807fc1048407ffb2e8003ff9974002dfccba000ffd65d00017eb2e8003ff1974001df8cba000fff54d0007ff2a68003ef9534001ffaa9a0003bd54d0007fe2a68003ffd8f4001ffcc7a0002fe63d0007feb1e8000bf58f4001ff8c7a0003ff53d0001ff29e8000ff54f40007f8a7a000fff43d0007ff21e8003ff50f4001ff887a000fff62d0007ff3168000bf98b4001ffac5a0002fd62d0007fe3168000ffd4b40007fca5a0003fd52d0001fe2968003ffd0b4001ffc85a000ffd42d0007fe2168000ffccb40007fc65a0003fd32d0001fe1968003ffd874001ffcc3a0006fe61d0007feb0e8000bf5874001ff8c3a0006fc61d0001ffa8e800cff94740007faa3a0033fc51d0007ffa0e8003ff9074001ffa83a000ffc41d0001ff98e800cff8c740007fa63a0033fc31d0001ff90e800cff88740007fa43a0033fc21d0001ffa86800cffc4340017f821a000bff65900057fb2c8002ff9964002dfccb2000bfd65900017eb2c8002ff19640005fac920003ff5490001dfaa48003ff95240007faa92000ffc5490001de2a48002ffd8e40017fcc720002fe6390005feb1c8000bf58e40017f8c720003ff5390001ff29c8000ff54e40007f8a72000fff4390001ff21c8000ef90e40007fa872000ffc4390001de21c8002ffd8a40017fcc520002fe6290005feb148000bf58a40017f8c520003ff5290001ff2948000ff54a40007f8a52000fff4290001ff2148000ef90a40007fa852000ffc4290001de2148000ffcca40007fc6520003fd3290001fe1948002ffd8640017fcc320006fe6190005feb0c8000bf58640017f8c32000afc6190001ffa8c800bff94640007faa32002ffc5190007ffa0c8000efd064005ffc8320003fd4190001dea0c8003ff10640007fe632002ffe3190001fe98c800bff0c640007fe432002ffe2190001fe90c800bff08640015fcc12000bff5090005ff2848002ffd02400177e812000ffb4090005ff8848002ff04240007fecaa0002ff6550001bfb2a80009fd95
  | 4 => 0x803fd53d0401fe29e8203ffd0f4101f7e87a080ffe43d0407fea1e8200ef50f4101ff887a080fff62d0407ff3168200bf98b4101ffac5a0802fd62d0407fe3168200ffd4b41007fca5a0803fd52d0401fe2968203ffd0b4101f7e85a080ffe42d0407fea168200ef50b4101ff885a0803ff32d0401ff1968200ff4cb41007f865a0806fd61d0403ffa8e8201ff9474100ff8a3a0807fe41d0403df20e8201fd9074100ff883a0807bc41d0403ff18e8201ff0c74100ffc43a0807fc21d0407ffb068203ff98341015fcc1a080ffd60d04017eb068203ff1834100ffe21a0807fc10d0401ffb2a8200bfd9541007fccaa0816fe6550401feb2a8200bf59541007f8caa0816fc65504037fb228200ffd514101ffca8a0803be5450401feaa28200ef5514101ff8a8a0803ff63504017fb1a8200ff98d41007fac6a0803fc63504017e31a8200ffd4d41007fca6a0803fd5350401fe29a8203ffd0d410077e86a0803fe4350401fea1a8200ef50d4101ff886a0803ff62504017fb128200ff98941007fac4a0803fc62504017e3128200ffd4941007fca4a0803fd5250401fe2928203ffd09410077e84a0803fe4250401fea128200ef5094101ff884a0803ff3250401ff1928200ff4c941007f864a0806ff6150403ffa8a8201ff9454100ffaa2a0807fc5150403ffa0a8203fdd054100ffc82a0807be4150403fe20a8201ef1054100fe882a0807fe3150403fe18a8201ff8854100ff842a0803ff60504017fb028200ff98141007fac0a0803fc60504057e3028201ffc414100fee20a0807fc1050401ffb2e4200bfd9721007fccb90816fe65c8401feb2e4200bf59721007f8cb90816fc65c8401ffb264200bfd9321007fcc99080efe64c8401feb264200bf59321007f8c99080efc64c8401ffaa64200ff95321007faa990803fc54c8401ffb1e4200ff98f21005fcc790803fd63c84017eb1e4200ff18f21005f8c790803ff53c8401ff29e4200ff54f21007f8a790803ff43c8401ff21e4200ff50f21007f88790806fe62c8401ffa964200ff94b21007faa590803fc52c8401ffa164200ff90b21007fa8590803fc42c8401ff9964200ff8cb21007dc6590803fd32c8401f69964200ff0cb2100dfac390807ff51c8403ff28e4201ff5472100ff8a390807ff41c8403ff20e4201ff5072100ff88390807ff31c8401fb98e4201ff8c72100ff86390807f431c8403ff10e4201fb8872100fec4390807fc21c8403f610e4200ffd8321007fcc19080afe60c8401feb064200bf58321007f8c190807ff10c8403fe0864200ffd9521005feca90803fe654840b7f32a4200ff59521005faca90803fc654840b7e32a4200ffd9121005fec890803fe64484077f3224200ff59121005fac890803fc64484077e3224200ffd5121007fca890803fd5448401f
  | 5 => 0x8c4201ff8c621003ff5310801ff2988400ff54c42007f8a62100fff4310807ff2188403ff50c4201ff88621002fe6210801ffa908400ff94842007faa421003fc5210807ffa108403efd084201ffc842100fee4210807fea108400ef5084201fda842100fff6110807ff3088401bf9844201ffac221002fd6110807fe3088401bf18442087fca221043fc5110807ff2088403ff10442087fc6221043fc3110821ff1088410ff0844201ffec02100ffe60108057f3008403ff58042005fac02100ffc6010821ff8808410ff04042007fecb19002ff658c801ff32c6405bf99632007facb19002fd658c801fe32c6405bf19632007fec919002ff648c801ff3246403bf99232007fac919002fd648c801fe3246403bf19232007fea919003fe548c801feaa46400ff15232005fac719003ff538c801ff29c6400ff54e32007f8a719003ff438c801ff21c6400ff50e32007f88719002fe628c801ffa946400ff94a32007faa519003fc528c801ffa146400ff90a32007fa8519003fc428c801ff9946400fbcca32007fec31903ffe618c8037f30c6400ff58632005fac31903ffc618c8037e30c640fff9463207ff8a31903ffe418c81ffe20c640fff8c63207fbc631903ffc318c81fee18c640fff8863207ff84319003ff608c801ff3046402bf98232007fac119002fd608c801fe304640fffc423207ff82119003ff644c8017fb226400ff9913201dfcc899003fd644c8017eb226400ff1913201df8c899003fe544c801feaa26400ff15132007fea499003fe524c801fea926400ff14932007fe8499003fe424c801fea126400ff10932007fc6499003de324c801ffb0a6400bfd8532007eec299002f7614c81dff30a6401bf98532007fac29903bfc614c8037e30a6400fd1853200de8c29903bfe414c81dfe20a640eff88532077f84299003ff604c8017fb026400ff98132007fac099003fc604c8057e302640effc4132077f82099003ff640c8017fb206400ff9903201dfcc819003fd640c8017eb206400ff1903201df8c819003fe540c801feaa06400ff15032005fcc419003ff520c801ff2906400ff54832007f8a419003ff420c801ff2106400ff50832007f88419003fe320c801f71906400ff4c832007da6419003cd320c801ffb08640dff9843200dfcc219003fd610c8017eb08640dff1843200df8c219037fe410c81bfe208640dff8843206fdc4219037fc210c81bf61086400ffd8032007fcc01900afe600c801feb006400bf58032007f8c019037ff100c81bfe0806403ffd974101ffccba0816fe65d0407feb2e8200bf5974101ff8cba080efc65d04037f3268203ffd534101ffca9a080fbe54d0407feaa68200ef5534101ff8a9a080fff63d0407ff31e8200bf98f4101ffac7a0802fd63d0407fe31e8200ffd4f41007fca7a0
  | 6 => 0x1ff218a400ff50c52007f88629002fe621480bffa90a405dfd485202ffca429017ee521480bfea90a400df5485202fdaa429017ff611480bff308a401bf9845202ffac229002fd611480bfe308a401bf1845202ffca229017fc5114829ff208a414ff104520a7fc6229053fc3114829ff108a414ff0845202ffec029017fe60148057f300a405ff58052005fac029017fc6014829ff880a414ff0405201ffecba100eff65d0807ff32e8405bf9974201efccba10027e65d0807feb2e8400bf5974201efacba10027d65d0807fe32e8403bf1974201ffea9a100ffe54d0807feaa68403ff1534201ffec7a100ffe63d08017f31e8403ff58f42005fac7a100ffc63d0801ffa9e8403ffd0f4201ffc87a100ffd43d0807fe21e8400ffd4b42007fca5a1003fd52d0801fe2968403ffd874201ffcc3a1006fe61d0807feb0e8400bf5874201ff8c3a1006fc61d0827ff28e8413ff1474201ffc83a100ffc41d0827ff18e8413ff0c74209ffc43a104ffc21d0807ffb068403ff98342015fcc1a100ffd60d08017eb068403ff1834209ffe21a104ffc10d0801ffb2c8400bfd9642007fccb21016fe6590801feb2c8400bf59642007f8cb21016fc65908017eb248400ffd524201ffca921003be5490801feaa48400ef5524201ff8a921003ff6390801ff31c8400bf98e42007fac721002fd6390801fe31c8400ffd4e42007fca72100fff4390801ff21c8400ff50e4201ff8872100efe6290801ffa948400ff94a42007faa521003fc5290807ffa148400efd0a4201fde8521003ff6190825ff30c8401bf98642007fac321002fd6190825fe30c8401bf18642097fca32104bfc5190825ff20c8403ff10642097fc632104bfc3190825ff10c8412ff08642007fec121003fe60908057f3048400ff58242005fac121003fc6090825ff8848412ff04242007fecaa1002ff6550801ff32a8405bf99542007facaa1002fd6550801fe32a8405bf19542007fea8a100ffe5450801feaa28403ff15142007fec6a1002ff6350801ff31a8400ff58d42007f8c6a1002fc6350801ffa9a8400ff94d42007faa6a100fff4350801ff21a8400ff50d4201ff886a1003ff5250801ff2928400ff54942007f8a4a100fff4250807f7a128400ff909420077c84a1003ff61508017fb0a8411ff9854200dfcc2a1003fd6150823fe30a8401bf1854208ffca2a1047fc5150823ff20a8403ff1054208ffc62a1047fc3150823ff10a8411ff08542007fec0a1002ff6050801ff3028400ff58142007f8c0a100afc6050823ff8828411ff0414201ffeca2100eff6510807ff3288405bf9944201ffaca21002fd6510807fe3288403bf1944201dfcc82100fff5410807ff2a08403ef9504201ffaa821003bd5410807fe2a08403ffd8c4201ffcc621002fe6310807feb188400bf5
  | 7 => 0x2a002fd6095007fe304a81affc42540d7f8212a00ffe5455007bf2a2a800ffd8954005fec4aa003fe6255001feb12a800ff18954005f8c4aa003ff61550017fb0aa819ff9855400dfcc2aa003fd6155033fe30aa801bf185540cffc82aa00ffc4155033ff10aa819ff08554007fec0aa002ff6055001ff302a800ff58154007f8c0aa00afc6055033ff882a819ff0415401dfcc82a00ffe5415007df2a0a803ff5505402f7aa82a0033d5415007ffb10a803ff98854005fcc42a00ffd62150017eb10a803ff1885401ffec22a00ffe61150037f308a803ff58454005fac22a00ffc61150037e308a803ff9045401ff8822a063fe2115031fe108a803ffd805401ffcc02a00afe6015007feb00a800bf5805401ff8c02a063ff1015031fe080a805ffd935202ffcc9a900efe64d480bdf326a400af9935202ffac9a9002fd64d480bdeb26a400af5935202ff8c9a9017ff54d480bff2a6a405ff5535202ff8a9a9017ff63d480bff31ea400bf98f5202ffac7a9002fd63d480bfe31ea400ffd0f5202ffec3a9017fe61d48037f30ea405ff58752005fac3a9017fc61d48037e30ea405ff9475202ff8a3a905ffe41d482ffe20ea417ff8c7520bff863a905ffe21d482ffe10ea405ffd835202ffcc1a900afe60d480bfeb06a400bf5835202ff8c1a905fff10d482ffe086a400bf59652007fec929003fe64948077f324a400ff59252005fac929003fc649480bffaa4a400dfd5252007fca929003fd5494801beaa4a405ff15252007fec729003fe63948017f31ca400ff58e52005fac729003fc6394801ffa1ca400ff90e5202dfcc529017ff5294801bfa94a405fbd4a52006dea529003ff619482dff30ca401bf98652007fac329002fd619482dfe30ca401bf186520b7fca329017fc519482dff20ca416ff106520b7fc632905bfc319482dff10ca416ff08652007fec129003fe60948057f304a400ff58252005fac129003fc609482dff884a416ff04252007fec8a9002ff6454801ff322a400ff59152007f8c8a900efc645480bffaa2a400ff95152007faa8a9017fc5454801ffb1aa400bfd8d52007fcc6a9003fd6354801fe31aa400bf18d52007fe86a9003fe4354801fea1aa405ffd495202fdea4a9003fe5254801bf292a400ffd8552005fec2a9057fe61548037f30aa400ff585520aff8c2a9006fc615482bff28aa405ff145520affc82a9057fc415482bff18aa415ff0c5520affc42a9057fc2154801ffb02a400bfd8152007fcc0a9003fd6054801fe302a402bf181520affe20a9057fc105480b7f328a405ffd905202ffcc82900efe641480bfeb20a400bf5905202ff8c829017ff541480bbfaa0a405ff9505202ffaa8290037d541480bfe2a0a405ffd8c5202ffcc629002fe631480bfeb18a400bf58c5202ff8c629003ff431480
  | 8 => 0x200180100080000000280200280380180280680000280600680000000b00b80000100000480200080780280280380180400400000080100000180080180200080300000700680480080980e80600280300180300080800080000080600380200080300200b00000380200280480000080800000000080600080000180100000180000380000080000b80100480480000000000080200000180580280000700d00180700100b00080800000000200380000900000600580500080200100580100280500080f00400080180080080880000000680000200b00100080000000080000100180680600280100000000182300180d80100480100000680080200000000b00100000000080000000980601400000080180000980580980400300d00600080000980700100000000200100480100100000380500081380400100080280100100180600000000580300200180181e00600500480200600080000100480400000100080080100000081b00000080201480200000200000000400300800080500180000900780000000000200000100800100000080480080000080080600180a80080a00a00a00680100580300100901000880380080080000200000080400180000080600c00000d80080000000300180080000000200480000000080501f00500101700080000200380080080480000100780480201200580000100600081980600080100100200000380000780580000200001c80200000000b80000000180080100000280081700000180c80500600400600380180180a80080080200000200380f80280300b00180000880000080000100080200000100600080500a00080000100100800081700580100180000280180200400300d00200000580200000300180080180100000200480000400100080000000000300100400000580100000000100600080000080080300000f80400080280700080080400c00a00200180200000000200080100080180180080100500080080100d00100000380000000000000180000880080000000200680180000180000a00001400200080080080100080600080001d02b000000000806802003000006803808802002800003800003006800800000000800000800003000802002001000800001002001801800001006000000000803802000000001001804000001002800001002fd65950077f324a803ffd525402f7ea92a0033f5495007ffb1ca803ff98e54005fcc72a00ffd63950017eb1ca803ff18e5401ffec52a00ffe62950017f314a803ff58a54005fac52a00ffc6295007ffb0ca803ff9865400dfcc32a00ffd61950017eb0ca803ff1865400df8c32a06bfe519500bfe28ca803ff9065401ff8832a06bfe3195035fe18ca81aff886540d7f8432a00fff6095007ff304a802bf9825401ffac1
  | 9 => 0x2ba36300062d46e0000f0a3422d5e20ae3150000005d38006994ad0006ac0005ae30800000016aea2dcf04667f3660b10b46af0005996111bf1838003a824865045cad556e0000005c23a531e8002516c22e86fe53e3974a280025280027c8a09c20000000e236b0762653a2bda454cbb85700000023a3c50002d84a268a40c00049959200f951cbe5390000366b46424f086044b46d0d54cd0000003653f84b822c8d26280b03d61c4dee2b726dbd90db5c70000fd15a00000000022f0002c100022500005c6864891c13b63146094ff63d53b64e21a15067653ceee5b404a3904965524750002d75ba1aa0000003e603a5930000005796e29583874e55286480006d05e466e1c74db2cd574205470034c5407ed084afc37a871f108db7c6d6368e5100018334f4a707b153e7200007416109663412cc4065b55c68b17b0d4494ce6320ae1c221423ef1adc5d885dae9cb34b0df20b9a40369810923aa5a252f0006a25fe5a505fb754781460000bc00058d41567363738b25f2b40c054d6c31cd9204313ca1a00cc00050b239816a3b8003d80006980001ea3a58001cc2af2ce0649c93e202f0000000000000003af4c18000002e255f37e00070e70149580069e333000000163280bc813e27000030e052800000110692011473318352c372525be06d67141480000041b59f36e0a235705d2020005bd0006e08a002204f0001142183540006010003768000006c025500041ec5d0109b00b606140ce274c552556a15d4df27dc2300042d00006e41a2c054e7066e1e771ae4a46f314838138000011c00050259d02a0141270000002be0000005732e2c810458504f66a749297a4c81da2726c380024f04680000000046080000000010fe9a4bd8000000c88ed63e8004170004682ed32159bc720005e323ca1256880063c0245d80102df2644bc1cf80000001c0005fc26c0006431a90002ad00066916b5663efbba8000000000000000000000006d422136a3bd3b000900000002380080000280280100c80600380100300000a00000000180180000000400000000200500c00280080100080600080180080e00900300180200000280000400100480100480500000b00300200000080700000580000300f00380100000300480000480000080200400080180480500000380600000600080000000080280001080100080000100080480000500000280082000580400300181400700000680400501480080380000000000400680300380180080300000600000000080280200800000100000000380080500100480000000080700780980280080680680080400000080100000000000080000180280200880380080500180080400000200d80480b00080400000600480080000380400000200100480080000101680201580e81000080080600080
  | 10 => 0xbed9b0404a92e3ebe3fa5651088e08006ce06daee2e5800225a26e2502ec0405f0000000afa8256764016d0453c000069000000e0002963772969d88004dcdf1384022ea30480be365c73c3b1800000198f768068e6645c469f0d34ae0fb80a2f945e5e7000000000000404bb39ce0fe5a000020653300051c00036200000062000015626bc4eb2aae40ad16e81952c96c60b21c00024031b5b2362d4a3e85b544227e00000000000059558e57c0000000002811be00044c0000003a9cf40003229ee0000004bf00000000033f0000000269e32d300065c603000000000000000048eb23440001fd0000000004e708b6124eac75dbf6ba00050c0218002e947d6950004b70000da000616616ed300057f6845a362a6d6999168ae00b1dd1b2207dae69525cd10e142c098002eb0092a7063d53310227bfb2801bfe260ddc853e546c1d61d16c2dec2ef06b00000000056c00014e5b4d515e9705258800186309d7010c8845561774ee587020c626d906c0000000002263ed00049560a405a9415eb745a90000004740004612bc00019300024223557d0004e132b8000004c30669f51c50c969c25190a1a380067e0005ff0005c01fda2402a800463261084aabb5f1132360ca249363b3c0aa6d510d000443109b090005df61e00000042f3b7c8728a1bc06600000000038592825d49395e436007cec80000800000001a80000000039347a15c6244b160643500004fd2747733400032b5c62ca2086173d201a0002f03b4c825a7e19ded2f85e0dd434edb94463e953f45a03044810c5f71a5b1902c8000000000001ff89b000000472a996f500022c67d0593ce0b813fd7a039c7f60ca1b4c40004473f4427049c8e9304f10003ee6dfd6d449674a1426d1e06584d04ab6d4eeb4f80001715ab00053252e00000057680000070bd9c07ca6b50432e96cad6e57406ee680004d1185210002c400000022242800062929028401f8003964b280014535923757081e48a8ef0bb3508378780a45d28005031384640003df4918985590f139f6f05ce2194f705b0eb09d1699b343c49d64f0495fd10aea0d0000000012a0000000000003eb62200013d3bc0004c92c320b00050600012c0003c7000558000000618465000000239000535bac2db3b232d2761220000004b697529f2b905604bea90000000000000001e100029b48300049b2dc1de2f98004b1f082543b588000000000000012e1540ee8001f400060da033675db13260c63842a069cf239531c0131166970b25370fb07718f28950530600000050f0070006cf0f93794883391414026f100024d3ed8002d893600070c6081c36c55900000bca922828006b880c2d90003a0eaa0c34b0af54e864768f0003055d72e500005ebae00f0288000006b800011f4013538000006236750003d700027b403
  | 11 => 0x658119b1a106ca153c2814c581e800030352ea7a4ea00000031cc89aa96df2b10002b380000061c0004bb3cd00041c61597e5ef0001790996e13db000484d723310000f980053c00000052206f86be2b30d4125b300067680000041f27fa0d703000000000459000571d8f12102b18832c0000003554941f20000f865e1694920005643233400353350000005f24838880470006c7c113a6ddc8b38645c534e60531241e4de23c105059b8f5360001a65e10040951192b599650e28e0050435c37091115802a40001778d16ad4b48392286fc4bcec0bab0e753786a5dc1df00024c1a353a1470000000002b36a80000001150000004e3223add5acf0b5830324d900037a36f40e0338e6e2c00000049a00007c00061300000000000000048c6bb27d4240005bc1d40d885dcfcdcc11d0659ded2a6490f309fd9800000031dc768005a15880358003ea0589d80258004a567818a4b38df80040d45394025628195ccf51264764eeb485436c46d20650006592010bd88f679c974b33616d78003850002102d40b500000000064463f00000000002e1742bb0423b957380019d6d70ac6634c15e61c3bf60005166c85622ab22b8150000003bb6070003f72ffee4857a166b6eae1bd1dc3c66ea1664f491a57831300000036c5f80000002fa6d85382d20000000000000408004330000385263e03f90002500001ec80000000000044bc829bdafb6704804f1b0123053aa073678b344521d1b85233686b03b52411094e42691d222480e94987d4b935b61f0004d100043e4c2b604d50003b80a638865a195b361706c48005400721c40000f5301c3a8518410002da66213a80067900049855b2750001ab0001b600000042b43f4a09418bf98b5346ed6416390510002c60e459e80066b23d1c84c655d00000029c0671b0bf10270000000006f65b000000020e8006020000003e10004142635e84790003b700066f70766d00000044cef40000000000000002f71600002fd000361c180c14416ca00009f3520cd48b0002e16f800006280067a0000005845550003760002d00000000de0000004be80000000000066de52000217056c0b9ad2434f90281f60006cbb57bd50bd42c646c90ada9ca0733372bd566c084393d10550000000002cf3473710006e408fd241ff08e0006de3a11cd1ba45c3430004f38b738d51046000000018c2e30000000000c410e93c26f0342aa10739d19c0004519f84ba29d3de125192d9138216e02c2f23c200b5f41e90005686a531a69469126652a80063a00000002100033a54262e0002096655011c18000003e32ff0004038004b5a29bf30000ce0006da6e03020002a34503dd2bdccb0000000004160000003b9c4dd470000003a90006a630700016a51e1db2005af0c65d600000057700028aba659a04c4bf9fb1f33f29
  | 12 => 0x541b763166c57881810bec92d9e0f61464a70435600000d8006ab043aa06d12c72e7646565e2f0000a106320e3ba00048880003b55a00000000053008c0006e800014b8683454fd20c03f48e0003ad3783530534fb33825e4071af38928bd0902dc063b684da5819a61d5ca0004eb9060000e90bf4b02bf03af021446e65f04c08c254637254c1762a8245529862332013e0ee1b4531cf2330f040a1f757601b28506f0006540002916f200015100000066040aae62d28af0001551122a2ce8c303640c5000000283800000248800518000647e870dd4b52378000d84710ea00012900000029e00063b3a441044f44e3cb1c0000490038c096fd3d4b8390dc0f0aecc066666717f1ac0d7a1f6b31ef2d60cf2776322c0ab607f5d483d1fa25349149316bbc31670ff00000065f0004520000006530003c968100000038a1e65d018e0120c7000000260358471ea469358a00039865d0a31310790000000000006745f347e14b6bf0690013b8a6a8000e60ec6b709e000000000018acc0001b10002cb0000002c20003ec1680004ac56f0000ded63095ccf51b35d2470000a84510003d00004da28c80045b80000000000000005c80000000029300032180000048a0000003e72389b90005943d46835fa63647c009bff0f26ec4131cc9148000000000002c84e9b2600012b2fe0003fe5855c9029e4980025a6e39eb70d4b638c5e00005444190004bd04e53d12312d6c5897ca16686a016f1851e556937b0e116ddda324071e8227c1390000000006f74342d7bfd015cd320a3be68c16230f59655e43893400000000023e15946631b8ee5bb5753c42f112f6195eb4323f2024800061b75bf06c15b11330711aeb7d1173e445b67c4212980000000005f50000002d3a0c800047af40000002ea0000000088000004e000017c32f46736d3b40000000d630cd865492d498248b8005a828324a44a4205a8940ccc0000001d715b4ef2ec184354e9b00028fb5e2716dc5483115ac4d63bf0a970034900048400043a00009000bb910238000000000e800033e0006b55a0b7f05e2c95450002441bb22300035019e02311e42e0024382de2320975712ac0cb4e217833d10828614a5cb1fc54f59e1350000004c700330b0001a567b0001c619bea150280034a0001a85f60914d707e2f60001f3b2a4138000000830003692b500000000000000056b00051261a00027851700032e00018d19f5d331625aa6a19221349e2ae1ec12eba329a63f9034dc51a194e04143569cfa5aa49c21e1ebee363501d4ce485c8fd7e1ed1188b90ab00aefa4f328c2d5e4551f2886dd63010f49f1b42314a324b4fc1f060e34131e0d700025931fbc134641d3f0b4c0006e5da9d3688d0d00931010003b152003170a00000000005800059700000000655704454150d00000024
  | 13 => 0x8917d1002574ed28b0000004050000e02beecb00000000039b52d81281f415c4f84c80000005219728f48193b5d10006bc000563e0d07a21131d38300000000047f8f88002a50003a20e302908103298700032000000000000024e37880000000000022e45f0000001e71370002b000069615f19051d1b2119b9c19dd0727f00000027e9f584b68500000046f4e90000f400000051546b1020000000dc0005d54253a4870ca83043d3675989eb7cec54b027c4d20400002d0003dc5600b2a3b26716416fb5158b45648f31f527c879e40001570005b600064d0000003c38fa3cf2a980039e000050e17d8908522b3489d0426260e6a6c66560376100004a600d68d5a726e0e56ef3990003940000004eb4575e56c999432980069d00000000045087000011b28d0001896b12a10004a180052d0005b85316b60000006ff020000086c18d0a29764b2684c26bd0005fb0acc86c29042b730003004fe02fa7332715b9c0bfc00000000000000022880022748659c8001788005ddb701a74692fc0255f94ed97310b0c80002628001e222a36f80061511b8003253294b20174ca0000006210005b76e25290a2c004d43a76555dd30a8000006cc04ed194fa9240003920000004078001d500052c678d615c14d20000000d900064c47b00020f00000003e33b05bca00000753cc4f014c3a00001651d9364b860000004440000003c5e3e5500002296b58006c700000034d0000fc00000009400009a0003306e9041ce7b0c61ad649536f952b6ca8bacb400045280030a0002d10006b94968000001a20000000e88000000002793ce8006335c848d34235a2b2474904044c6a22014d6db3f513a2951c280005a8a51dd00013f38e22a8002f7cdd0000330260866894555a625b6c1e9f83c5d94af274083ee505a5289fe1b50000006cd0f62c558c0ba4aed9dc9f9955ad39a6d58870005df9ea88a0005de00017aaa20b09f955426251400000009c3b34ba8160ceb5c5ea238408ad1d1357b1d30006e72b819800000014968802ba3f193c3d25c5112a608260001bb173668a714f2f358206eb28172017d355a44b780006a8000608004d80005d26fb0000000006610000ad80c80019140b4aa
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc76149100067f651491002e7c6514910006ef6214910006ec621491000df67114910005f57114910015fa7014910005f9701491001cff76d0910004fe76d0910004fd76d091001cfc76d09100057e75d09100057d75d0910006ef62d0910006ec62d091000df671d0910005f571d0910004ff7690910004fe7690910004fd7690910004fc7690910006bf649091001ebc6490910015fa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc765091001cff7610910004fe7610910004fd761091001cfc7610910006bf641091001ebc6410910006ef6210910006ec621091000df67110910005f57110910015fa7010910005f97010910004ff768c910004fe768c910004fd768c910004fc768c910006df638c910006dc638c910015fa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c910005f7714c91000df4714c910004ff760c910004fe760c910004fd760c910004fc760c910006ef620c910006ec620c910007cd320c91000df6710c910005f5710c910015fa700c910005f9700c910015f4765051001ef47650510014f47650510005f77550510005f5755051000df7745051000fb77450510007b7645051001ef6645051001ef46450510007b46450510007b65450510007b55450510007b74350510007b54350510007b74250510007b54250510007f37050510015f67050510015f47050510007f0705051000ef7605051000ff360505100dfb640505100dfb4405051000cfe76d011000cfc76d0110006bf64d011001ebc64d011000df671d0110005f571d011001cff765011000cfe7650110054fd765011000cfc76501100057f75501100057c7550110006bf645011001ebc6450110005f7715011000df4715011000cfe76c811000cfc76c8110006ef62c8110006ec62c811000df671c8110005f571c8110025fa7688110016fa7688110015fb7388110005f97388110035f97288110006fa6288110006f8628811000dfa7188110015f87188110016fb6188110017f3618811003ff25188110007f1518811003ff24188110007f14188110044ff764811000cfe7648110034fd764811000cfc76481100057f75481100057c7548110005bf7448110005bc7448110006ef6248110006ec6248110005f7714811000df4714811000df87648110036f8764811000cf876481100077b7548110007787548110007bb7448110007b87448110005fb7348110005f97348110015fb7248110017eb7248110007eb6248110006fa6248110006f86248110007e86248110007ea5248110007e95248110007ea4248110007e94248110007f3714811000dfa714811000df87148110037f07148110016fb6148110017f36148110037f25148110007f15148110037f24148110007f14148110
  | 1 => 0x911000cfc71d911005ebf41d911005ebd41d9110014fe70d9110014fc70d9110006bf6499110055f970991100057f75591100057c7559110005df7359110005dc7359110005ef7259110005ec7259110065fb7059110004ff75591100067f75591100047f755911002cfc75591100067c755911002c7c7559110006bf7459110004ff7359110006df7359110004df7359110004fc7359110006dc7359110004dc7359110004ff7259110006ef7259110004ef7259110004fc7259110006ec7259110004ec7259110054ff7159110006f77159110064ff7059110006fb70591100debe40591100debc405911005cfe76191100057e75191100057d751911001ebe6419110006bd641911001cff7695110004fe7695110004fd769511001cfc76951100067f659511002e7c659511001ebe6495110006bd64951100073f549511000df67195110005f57195110004ff7655110004fe7655110004fd7655110004fc765511001ebe6455110006bd645511000df67155110005fb7055110015f8705511001cff7615110004fe7615110004fd761511001cfc7615110006bf641511001ebc64151100073d541511000df67115110005f5711511002cfe75d8910004fd75d891001cfe74d8910004fd74d8910004fe73d8910004fd73d8910014ff71d8910014fd71d891003eef21d891003eed21d8910006ef6298910035f9709891002cfe7598910004fd759891001cfe7498910004fd7498910004fe7398910004fd7398910024fe7298910044fd7198910006f57198910034fd7098910006f970989100057f75589100057c7558910005bf7458910005bc7458910005df7358910005dc7358910045fb7058910004ff75589100067f75589100047f755891002cfc75589100067c755891002c7c7558910004ff7458910006bf7458910004bf745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910004fc7358910006dc7358910004dc7358910006ef7258910034ff7158910006f77158910044ff7058910006fb705891003cfe7618910006ed621891002cfe7518910004fd751891001cfe7418910004fd7418910004fe7318910004fd7318910006ee7218910014ff711891000cfe7118910014fd711891000cfc7118910026ef2118910026ed2118910014fe7018910026f97018910014fc701891002cff76d4910004fe76d4910004fd76d491002cfc76d4910005be74d4910005bd74d4910006ef62d4910006ec62d491000df671d4910005f571d4910004ff7694910004fe7694910004fd7694910004fc76949100067f659491002e7c65949100076f5294910015fa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc765491002cff7614910004fe7614910004fd761491002cf
  | 2 => 0x2cfc7559210016bf7459210004ff7359210004fc7359210004ff7259210004fc7259210056bf4159210056bd4159210014ff7059210014fe7059210014fd7059210014fc7059210016be4059210016bc4059210016f71059210016f5105921001cff7695210014fe7695210004fd7695210014fc769521001ebe6495210006bd64952100073f5495210004ff7655210014fe7655210004fd7655210014fc765521001ebe6455210006bd6455210005fb7055210015f8705521001cff7615210014fe7615210004fd7615210014fc76152100073d541521002cfe7598a10004fd7598a1001cfe7498a10004fd7498a10004fe7398a10004fd7398a10016ee7298a10046ef2198a10046ed2198a10014fe7098a10016fa7098a10014fa7098a10014fc7098a10016ee2098a10016fa2098a10016ec2098a10004ff7558a1002cfc7558a10004ff7458a1001cfc7458a10004ff7358a10004fc7358a10016ef7258a10036ef2158a10036ed2158a10014ff7058a10014fe7058a10014fd7058a10014fc7058a10016ee2058a10016ec2058a1002cff76d4a10014fe76d4a10004fd76d4a10014fc76d4a10005be74d4a10005bd74d4a10004ff7694a10014fe7694a10004fd7694a10014fc7694a10006ee6294a10006ed6294a100076f5294a10015fa7094a10005f97094a10004ff7654a10014fe7654a10004fd7654a10014fc7654a10006ee6254a10006ed6254a1002cff7614a10014fe7614a10004fd7614a10014fc7614a10015fa7014a10005f97014a1001cff76d0a10014fe76d0a10004fd76d0a10014fc76d0a100057e75d0a100057d75d0a10004ff7690a10014fe7690a10004fd7690a10014fc7690a10006ee6290a10006ed6290a10015fa7090a10005f97090a10004ff7650a10014fe7650a10004fd7650a10014fc7650a10006ee6250a10006ed6250a1001cff7610a10014fe7610a10004fd7610a10014fc7610a10015fa7010a10005f97010a10004ff768ca10014fe768ca10004fd768ca10014fc768ca10006de638ca10006dd638ca10015fa708ca10005f9708ca10004ff764ca10014fe764ca10004fd764ca10014fc764ca10005f7714ca1000df4714ca10015fa704ca10004ff760ca10014fe760ca10004fd760ca10014fc760ca10006ee620ca10006ed620ca10007cd320ca10015fa700ca10005f9700ca10015fb7648210006fb76482100077b7548210007787548210007bb7448210007b87448210005fb7348210005f97348210017eb7248210006fa6248210016f86248210007ea5248210007e95248210007ea4248210007e9424821000dfa714821000df8714821001cfe76d911002cfe75d9110004fd75d9110004fe73d9110004fd73d9110004fe72d9110004fd72d9110014ff71d911000cfe71d9110014fd71d
  | 3 => 0xd64d0c20004ff7690c20014fe7690c20004fd7690c20014fc7690c20006de6390c20006dd6390c20005ee7290c20005ed7290c20004ff7650c20014fe7650c20004fd7650c20014fc7650c2001ebe6450c20006bd6450c20006de6350c20006dd6350c2001cff7610c20014fe7610c20004fd7610c20014fc7610c2002cfe7598820004fd759882001cfe7498820004fd7498820004fd739882000cfe7198820016ee2098820016fa2098820016ec2098820004fd76d4820005be74d4820005bd74d4820004ff769482002cfd769482002e7e65948200067d6594820006ee62948200076f5294820015fa7094820005f97094820004ff7654820006ee625482002cff7614820014fe7614820004fd7614820014fc761482002e7e65148200067d6514820015fa7014820005f97014820004fd76d08200057e75d08200057d75d0820004ff769082001cfd769082001ebe6490820006bd6490820006ee6290820015fa7090820005f97090820004ff7650820006ee625082001cff7610820014fe7610820004fd7610820014fc761082001ebe6410820006bd6410820015fa7010820005f97010820004fd76cc820004ff768c820004fd768c820006de638c820006dd638c820015fa708c820005f9708c820004ff764c820005f7714c820025f4714c820004ff760c820014fe760c820004fd760c820014fc760c820006de630c820006dd630c820007cd320c820015fa700c820005f9700c820004ff755842002cfc7558420004ff745842001cfc7458420004ff7358420004fc735842000cfd7258420016f77158420026f65158420026f64158420026f63158420026f42158420014ff7058420014fd7058420014fc7058420016fa2058420016f61058420016f4105842002cff76d4420014fe76d4420004fd76d442002e7e65d44200067d65d4420004ff7654420004fd7654420014fc765442002e7e65544200067d6554420005ef7254420005ec725442000ef66154420006f5615442001cff76d0420014fe76d0420004fd76d042001ebe64d0420006bd64d0420004ff7650420004fd7650420014fc765042001ebe6450420006bd6450420005ef7250420005ec725042000ef66150420006f56150420004ff76cc420014fe76cc420004fd76cc420006de63cc420006dd63cc420004ff764c420004fd764c420014fc764c420006de634c420006dd634c420005ef724c420005ec724c42000ef6614c420006f5614c42000cfd76c842000ef661c8420006f561c8420015fa70c8420005f970c8420044ff7648420005df7348420005dc7348420015fb7648020006fb7648020004fb76480200077b7548020007787548020007bb7448020007b87448020015fb7248020017eb7248020006fa6248020017ea6248020006f96148020004ff7559210
  | 4 => 0x1200067f65d01200067c65d0120006bf64d012001ebc64d0120005ee72d0120005ed72d012001cff7650120004fd765012001cfc76501200057f75501200057c75501200067f65501200067c6550120006bf645012001ebc6450120005ef7250120005ec7250120004fe76cc1200067f65cc1200067c65cc120006bf64cc120006bc64cc120006df63cc120006dc63cc120005ee72cc120005ed72cc120004fd764c120004fc764c120005bf744c120005bc744c120006bf644c120006bc644c120005ef724c120005ec724c1200067f65c81200067c65c8120006bf64c8120006bc64c8120015ee72c8120014fa76c81200077b65c81200077865c8120007bb64c8120007b864c8120015fa72c8120017eb62c8120007ea52c8120007e952c8120007ea42c8120007e942c8120005f971c81200167f7559420004ff745942001cfc7459420004ff7359420004fc735942002cff725942002cfd7259420004ff715942000cfe715942000cfc7159420014fe7059420014fc70594200167e50594200167c5059420016ef2059420016ed2059420004ff755902002cfc7559020016bf7459020004ff7359020004fc735902001cff725902001cfd7259020004ff715902000cfe715902000cfc7159020014fe7059020014fc7059020016be4059020016bc4059020016ef2059020016ed205902002cff76d5020014fe76d5020004fd76d5020014fc76d502002e7e65d50200067d65d502001cff7695020014fe7695020004fd7695020014fc769502001ebe6495020006bd64950200073f5495020004ff7655020014fe7655020004fd7655020014fc765502002e7e65550200067d655502001ebe6455020006bd6455020005fb7055020015f8705502001cff7615020014fe7615020004fd7615020014fc76150200073d541502002cfe7598c20004fd7598c2001cfe7498c20004fd7498c20016de7398c2000cfe7198c20004fd7198c2000cfc7198c20014fe7098c20016de3098c20016dc3098c20004ff7558c2002cfc7558c20004ff7458c2001cfc7458c20016df7358c200e4ff7258c20074fd7258c20004ff7158c2000cfe7158c2000cfc7158c20014fe7058c20014fc7058c20016de3058c20016dc3058c2002cff76d4c20014fe76d4c20004fd76d4c20014fc76d4c2002e7e65d4c200067d65d4c20005be74d4c20005bd74d4c20004ff7694c20014fe7694c20004fd7694c20006de6394c20006dd6394c200075f5394c20005ee7294c20005ed7294c20004ff7654c20014fe7654c20004fd7654c20014fc7654c2002e7e6554c200067d6554c20006de6354c20006dd6354c2002cff7614c20014fe7614c20004fd7614c2001cff76d0c20014fe76d0c20004fd76d0c20014fc76d0c200057e75d0c200057d75d0c2001ebe64d0c20006b
  | 5 => 0x5ef7550920005ed75509200076f65509200076c6550920007af7450920007af645092001eee645092001eec6450920007ac6450920007eb7050920015ee7050920015ec7050920007e87050920004fe76109200067f65109200067c6510920006bf641092001ebc6410920005ee7210920014fe76cc9200067f65cc9200067c65cc920006bf64cc920006bc64cc920006df63cc920006dc63cc920015fa70cc920005f970cc920004fe768c9200067f658c9200067c658c920006bf648c920006bc648c920014fc764c9200067f654c9200067c654c920006bf644c920006bc644c920006df634c920006dc634c920005f7714c920035f4714c920005fb704c920015f8704c920004fe760c9200067f650c9200067c650c920006bf640c920006bc640c920007cd320c92000cfe76d85200067f65d85200067c65d8520006bf64d8520006bc64d8520036f661d852002cfe75d8520004fd75d852001cfe74d8520004fd74d8520004fe73d8520004fd73d8520014fd72d852000cfc72d8520036f431d8520036f621d8520014fe70d8520014fc70d8520036f710d85200057f75585200057c75585200067f65585200067c6558520005bf7458520005bc7458520006bf6458520006bc6458520005df7358520005dc7358520036f46158520004fe76d4520004fd76d452002cfc76d45200067f65d452002e7c65d4520006bf64d4520006bc64d4520005ee72d4520005ed72d45200076d52d4520004ff7654520004fe7654520004fc76545200067f655452002e7c6554520006bf6454520006bc64545200076d5254520004fe76d0520004fd76d052001cfc76d05200067f65d05200067c65d0520006bf64d052001ebc64d0520005ee72d0520005ed72d0520007ad42d0520004ff7650520004fe7650520004fc76505200067f65505200067c6550520006bf645052001ebc6450520007ad4250520004fe76cc520004fd76cc520004fc76cc5200067f65cc5200067c65cc520006bf64cc520006bc64cc520006f761cc52000ef461cc520004ff764c520004fe764c520004fc764c5200067f654c5200067c654c520006bf644c520006bc644c520005ef724c520005ec724c52003cfe76c85200067f65c85200067c65c8520006bf64c8520006bc64c8520014fc76485200067f65485200067c6548520006bf6448520006bc6448520005df7348520005dc7348520006f7614852000ef46148520037e42148520005fb7048520015f87048520004fe76d41200067f65d412002e7c65d4120006bf64d4120006bc64d4120005ee72d4120005ed72d41200177a50d412002cff7654120004fd765412002cfc76541200067f655412002e7c6554120005bf7454120005bc7454120006bf6454120006bc6454120005ef7254120005ec7254120004fe76d
  | 6 => 0xc64d4d20005ee72d4d20005ed72d4d20004ff7694d20004fe7694d20004fd7694d20004fc7694d200067f6594d2002e7c6594d20006bf6494d20006bc6494d200075f5394d20004ff7654d20004fe7654d20004fc7654d200067f6554d2002e7c6554d20006bf6454d20006bc6454d2002cff7614d20004fe7614d20004fd7614d2002cfc7614d200067f6514d2002e7c6514d20006bf6414d20006bc6414d20005ee7214d20005ed7214d2001cff76d0d20004fe76d0d20004fd76d0d2001cfc76d0d200057e75d0d200057d75d0d200067f65d0d200067c65d0d20006bf64d0d2001ebc64d0d20005ee72d0d20005ed72d0d20004ff7690d20004fe7690d20004fd7690d20004fc7690d200067f6590d200067c6590d20006bf6490d2001ebc6490d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d200067c6550d20006bf6450d2001ebc6450d2001cff7610d20004fe7610d20004fd7610d2001cfc7610d200067f6510d200067c6510d20006bf6410d2001ebc6410d20005ee7210d20005ed7210d20014fe76d4920014fc76d49200067f65d492002e7c65d4920005be74d4920005bd74d4920006bf64d4920006bc64d4920015fa70d4920005f970d4920004fe76949200067f659492002e7c6594920006bf6494920006bc64949200076f5294920005ee7694920006ee7694920005ed75949200076f659492002eee659492002eec65949200076c659492002e6c6594920005ed7494920007af6494920007ac64949200076f54949200076d5494920015ee7094920015ec70949200f76e50949200f76c5094920014fc76549200067f655492002e7c6554920006bf6454920006bc6454920005fb7054920015f87054920015ec765492002eec7654920014ec76549200076f75549200076f655492002eee655492002eec65549200076c6554920005ef7454920007af6454920007ac6454920007eb7054920015ee7054920015ec7054920007e87054920004fe76149200067f651492002e7c6514920006bf6414920006bc6414920005ee7214920014fe76d0920014fc76d09200057e75d09200057d75d09200067f65d09200067c65d0920006bf64d092001ebc64d0920015fa70d0920005f970d0920004fe76909200067f65909200067c6590920006bf649092001ebc6490920005ee7690920006ee7690920005ef7590920005ed75909200076f65909200076c6590920005ed7490920007af649092001eee649092001eec6490920007ac649092001eac6490920007ae5490920007ad5490920015ee7090920015ec70909200efae40909200efac4090920014fc76509200067f65509200067c6550920006bf645092001ebc6450920005fb7050920015f87050920015ec765092001eec7650920014ec7650920
  | 7 => 0x9120007ad7219120006be6119120006bc61191200ffae20191200ffac201912001ebf751912001ebe751912001ebd751912001ebc751912001ebf731912001ebe731912001ebd731912001ebc731912001ebf721912001ebd721912001ead721912001ebf711912001ebe711912001ebd711912001ebc7119120006be5119120006bc5119120006be3119120006bc3119120006be2119120006bc211912001ebf701912001ebe701912001ebd701912001ebc70191200febe50191200febc50191200febe30191200febc30191200febe2019120006bd20191200febc2019120006bf10191200febe10191200febc101912002cff76d5120004fe76d5120004fd76d512002cfc76d51200067f65d512002e7c65d5120006bf64d512001ebc64d5120005ee72d5120005ed72d512001cff7695120004fe7695120004fd769512001cfc76951200067f659512002e7c6595120006bf649512001ebc64951200073f5495120005ee7295120005ed7295120004ff7655120004fe7655120004fd7655120004fc76551200067f655512002e7c6555120006bf645512001ebc645512001cff7615120004fe7615120004fd761512001cfc76151200067f651512002e7c6515120006bf641512001ebc64151200073d5415120005ee7215120005ed72151200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d2002cfe75d8d20004fd75d8d2001cfe74d8d20004fd74d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20006de31d8d20006dc31d8d200057e7598d200057d7598d200067f6598d200067c6598d20005be7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d2002cfe7598d200067e7598d2002c7e7598d20004fd7598d200067d7598d200047d7598d2001cfe7498d20006be7498d2001cbe7498d20004fd7498d20006bd7498d20004bd7498d20006ed7298d2000cfe7198d20004fd7198d2000cfc7198d20006f97098d200057f7558d200057c7558d200067f6558d200067c6558d20005bf7458d20005bc7458d20006bf6458d20006bc6458d20005f77158d20035f47158d20004ff7458d20006bf7458d20004bf7458d2001cfc7458d20006bc7458d2001cbc7458d20006ef7258d20004ff7158d20006f77158d20004f77158d2000cfe7158d2000cfc7158d20006f47158d2000cf47158d20004ff7058d20006fb7058d20004fe7618d200067f6518d200067c6518d20006bf6418d20006bc6418d20006dd6318d2002cfe7518d20004fd7518d2001cfe7418d20004fd7418d20006de7318d2006cfc7218d2000cfe7118d20004fd7118d2000cfc7118d20006de3118d20006dc3118d20004fe76d4d20004fd76d4d2002cfc76d4d200067f65d4d2002e7c65d4d20005be74d4d20005bd74d4d20006bf64d4d20006b
  | 8 => 0xf67e10d95200f67c10d95200067f6599520005be7499520005bd7499520005bf7459520005bc74595200067f7559520004ff7459520006bf7459520004bf745952001cfc7459520006bc745952001cbc7459520004ff7359520004fc7359520004ff7259520006ef7259520004ff715952000cfe715952000cfc7159520004ff7059520006fb7059520004fe761952002e7e65195200067d65195200057e76195200067e76195200047e76195200076d72195200067e61195200067c61195201076e20195201076c201952002e7f741952002e7e741952002e7d741952002e7c741952002e7f731952002e7e731952002e7d731952002e7c731952002e7f721952002e7d721952002e6d721952002e7f711952002e7e711952002e7d711952002e7c71195200067e41195200067c41195200067e31195200067c31195200067e21195200067c211952002e7f701952002e7e701952002e7d701952002e7c70195201067e40195201067c40195201067e30195201067c30195201067e20195200067d20195201067c20195200067f10195201067e10195201067c101952001cfe76d91200067f65d91200067c65d912002cfe75d9120004fd75d9120004fe73d9120004fd73d912001cfe72d912001cfc72d912000cfe71d9120004fd71d912000cfc71d9120006be41d9120006bc41d912001cbe76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d91200efaf72d9120006be61d9120006bc61d91200efae20d91200efac20d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d91200eebf72d9120006bd72d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006be51d9120006bc51d9120006be31d9120006bc31d9120006be21d9120006bc21d9120006bf70d91200eebe70d9120006bd70d91200eebc70d91200eebe50d91200eebc50d91200eebe30d91200eebc30d91200eebe20d91200eebc20d9120006bf10d91200eebe10d91200eebc10d91200057e75991200057d75991200067f65991200067c6599120006bf64991200057f75591200057c75591200067f65591200067c6559120004ff75591200067f75591200047f755912002cfc75591200067c755912002c7c7559120006bf7459120004ff7359120004fc7359120004ff7259120006ef7259120004ff715912000cfe715912000cfc7159120004ff7059120006fb7059120004fe76191200067f65191200067c651912001ebe6419120006bd6419120005be7619120006be7619120004be7619120006bf65191200073f65191200063f6519120006be6519120006bd6519120006bc65191200073c65191200063c651
  | 9 => 0xd6390e20005ee7290e20005ed7290e20004ff7650e20014fe7650e20004fd7650e20014fc7650e20006de6350e20006dd6350e2001cff7610e20014fe7610e20004fd7610e20016ee2058a2002e7e65d4a200067d65d4a20005be74d4a20005bd74d4a20015fa70d4a20005f970d4a200f67f6594a2002e7c6594a200076f5294a2002cff7654a2002e7e6554a200067d6554a20005fb7054a20015f87054a201067f6514a2002e7c6514a200057e75d0a200057d75d0a2001ebe64d0a20006bd64d0a20015fa70d0a20005f970d0a200eebf6490a2001ebc6490a2001cff7650a2001ebe6450a20006bd6450a20005fb7050a20015f87050a200febf6410a2001ebc6410a20006de63cca20006dd63cca20015fa70cca20005f970cca20006de634ca20006dd634ca20005f7714ca2003df4714ca20005fb704ca20015f8704ca20007cd320ca20004ff755862002cfc7558620004ff745862001cfc7458620004ff7358620004fc7358620016f7715862003ef6515862003ef6415862003ef4315862003ef62158620014fc7058620016f61058620016f4105862002cff76d4620014fe76d4620004fd76d462011e7f65d462002e7c65d4620004ff7654620004fd7654620014fc76546201167f655462002e7c6554620005ef7254620005ec725462000ef66154620006f5615462001cff76d0620014fe76d0620004fd76d062010ebf64d062001ebc64d0620004ff7650620004fd7650620014fc76506200debf645062001ebc6450620005ef7250620005ec725062000ef66150620006f56150620004ff76cc620014fe76cc620004fd76cc62000ef661cc620006f561cc620004ff764c620004fd764c620014fc764c620005ef724c620005ec724c620034fd76c8620015f870c862000cff7648620005df7348620005dc734862000ef66148620006f56148620005fb7048620015f87048620015f976c8220006f976c8220017ea72c8220007ea52c8220007e952c8220005f971c822002cfe76d952001cfe74d9520004fd74d9520004fe73d9520004fd73d952002cfe72d952002cfc72d952000cfe71d9520004fd71d952000cfc71d95200067e51d95200067c51d952002c7e76d95200f76f72d95200067e61d95200067c61d95200f76e20d95200f76c20d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200f67f72d95200067d72d95200067f71d95200067e71d95200067d71d95200067c71d95200067e41d95200067c41d95200067e31d95200067c31d95200067e21d95200067c21d95200067f70d95200f67e70d95200067d70d95200f67c70d95200f67e40d95200f67c40d95200f67e30d95200f67c30d95200f67e20d95200f67c20d95200067f10d9520
  | 10 => 0x47200076d525472001cff76d0720004fe76d0720004fd76d072001ebe64d0720006bd64d0720005ee72d0720005ed72d0720007ad42d0720004ff7650720004fd7650720004fc765072001ebe6450720006bd6450720007ad4250720004ff76cc720004fe76cc720004fd76cc720006de63cc720006dd63cc720004ff764c720004fd764c720004fc764c720006de634c720006dd634c720005ef724c720005ec724c720014fd76c872000ef661c8720006f561c8720015fa70c8720005f970c8720024ff7648720005df7348720005dc7348720047e4214872002e7e65d43200067d65d4320005ee72d4320005ed72d432002cff765432002e7e65543200067d6554320005bf7454320005bc7454320005ef7254320005ec7254320017ea205432001ebe64d0320006bd64d0320005ee72d0320005ed72d032001cff76503200057f75503200057c755032001ebe6450320006bd6450320005ef7250320005ec7250320005ee72cc320005ed72cc3200167f7559620004ff745962001cfc7459620004ff7359620004fc7359620004ff715962000cfe715962000cfc7159620014fc70596200167e50596200167c5059620016ef2059620016ed2059620004ff755922002cfc7559220016bf7459220004ff7359220004fc7359220004ff715922000cfe715922000cfc7159220014fc7059220016be4059220016bc4059220016ef2059220016ed205922002cff76d5220014fe76d5220004fd76d5220014fc76d522002e7e65d52200067d65d522001cff7695220014fe7695220004fd7695220014fc769522001ebe6495220006bd64952200073f5495220004ff7655220014fe7655220004fd7655220014fc765522002e7e65552200067d655522001ebe6455220006bd645522001cff7615220014fe7615220004fd7615220014fc76152200073d541522002cfe7598e20004fd7598e2001cfe7498e20004fd7498e20016de7398e2000cfe7198e20004fd7198e2000cfc7198e20006de3198e20006dc3198e20014fe7098e20016de3098e20016dc3098e20004ff7558e2002cfc7558e20004ff7458e2001cfc7458e20016df7358e20004ff7158e2000cfe7158e2000cfc7158e20006de3158e20006dc3158e20016de3058e20016dc3058e20016fa1058e2002cff76d4e20014fe76d4e20004fd76d4e20005be74d4e20005bd74d4e20004ff7694e20014fe7694e20004fd7694e20006de6394e20006dd6394e200075f5394e20005ee7294e20005ed7294e20004ff7654e20004fd7654e20014fc7654e20006de6354e20006dd6354e2002cff7614e20014fe7614e20004fd7614e2001cff76d0e20014fe76d0e20004fd76d0e20014fc76d0e200057e75d0e200057d75d0e20004ff7690e20014fe7690e20004fd7690e20006de6390e20006d
  | 11 => 0x4fd7118f2000cfc7118f20006f97018f2002cff76d4f20004fe76d4f20004fd76d4f20005be74d4f20005bd74d4f20006de63d4f20006dd63d4f20005ee72d4f20005ed72d4f20004ff7694f20004fe7694f20004fd7694f2002e7e6594f200067d6594f200075f5394f20004ff7654f20004fd7654f20004fc7654f2002cff7614f20004fe7614f20004fd7614f2002e7e6514f200067d6514f20006de6314f20006dd6314f20005ee7214f20005ed7214f2001cff76d0f20004fe76d0f20004fd76d0f200057e75d0f200057d75d0f20006de63d0f20006dd63d0f20005ee72d0f20005ed72d0f20004ff7690f20004fe7690f20004fd7690f20004fc7690f2001ebe6490f20006bd6490f20004ff7650f20004fd7650f20004fc7650f2001cff7610f20004fe7610f20004fd7610f2001cfc7610f2001ebe6410f20006bd6410f20006de6310f20006dd6310f20005ee7210f20005ed7210f20005be74d4b20005bd74d4b20014fd7694b2002e7e6594b200067d6594b200076f5294b20015fa7094b20005f97094b20015ed7694b2002eed7694b20014ed7694b2002eee6594b200076e6594b2002e6e6594b200076d6594b2002eec6594b20005ed7494b200076f5494b200076d5494b20015ee7094b20007ea7094b20007e97094b20015ec7094b200f76e5094b200f76c5094b20005ef7654b20006ef7654b200076f7554b2002eee6554b2002eec6554b20005ef7454b20015ee7054b20015ec7054b20014fd7614b2002e7e6514b200067d6514b20015fa7014b20005f97014b200057e75d0b200057d75d0b20014fd7690b2001ebe6490b20006bd6490b20015fa7090b20005f97090b20015ed7690b2001eed7690b20014ed7690b20005ef7590b20005ed7590b2001eee6490b20007ae6490b20007ad6490b2001eec6490b20007ae5490b20007ad5490b20015ee7090b20007ea7090b20007e97090b20015ec7090b200efae4090b200efac4090b20005ef7650b20006ef7650b20005ef7550b20005ed7550b20007af7450b2001eee6450b2001eec6450b20015ee7050b20015ec7050b20014fd7610b2001ebe6410b20006bd6410b20015fa7010b20005f97010b20014fd768cb20006de638cb20006dd638cb20015fa708cb20005f9708cb20005f7714cb20045f4714cb20014fd760cb20006de630cb20006dd630cb20007cd320cb20015fa700cb20005f9700cb20046f661d8720046f46158720004ff755872002cfc7558720004ff745872001cfc7458720004ff7358720004fc7358720014fc7258720046f42158720046f7105872002cff76d4720004fe76d4720004fd76d472002e7e65d47200067d65d4720005ee72d4720005ed72d47200076d52d4720004ff7654720004fd7654720004fc765472002e7e65547200067d655
  | 12 => 0xc724c440006ee624c440006ed624c44000ef6614c440006f5614c440004ff76c8440014fe76c8440004fd76c84400067e65c84400067d65c8440005bf74c844001dbc74c8440006de63c8440006dd63c8440006ee62c8440006ed62c844000ef661c8440006f561c8440004ff7648440004fd7648440014fc76484400067e65484400067d6548440005bf744844001dbc7448440005df7348440005dc7348440006de6348440006dd6348440006ee6248440006ed624844000ef66148440006f56148440005be74d9720005bd74d9720005de73d9720005dd73d972001cfe74d9720006be74d972001cbe74d9720004fd74d9720006bd74d9720004bd74d9720004fe73d9720006de73d9720004de73d9720004fd73d9720006dd73d9720004dd73d9720006ee72d972000cfe71d9720004fd71d972000cfc71d9720006f970d97200f67e50d97200f67c50d97200067f6599720005be7499720005bd74997200067f7559720004ff745972001cfc7459720004ff7359720004fc7359720004ff715972000cfe715972000cfc715972002e7e65197200067d65197200057e75d93200057d75d9320005de73d9320005dd73d932002cfe75d93200067e75d932002c7e75d9320004fd75d93200067d75d93200047d75d9320004fe73d9320006de73d9320004de73d9320004fd73d9320006dd73d9320004dd73d9320006ee72d932000cfe71d9320004fd71d932000cfc71d9320006f970d93200eebe40d93200eebc40d93200057e75993200057d7599320006bf6499320004ff755932002cfc7559320006bf7459320004ff7359320004fc7359320004ff715932000cfe715932000cfc715932001ebe6419320006bd641932002cff76d5320004fe76d5320004fd76d532002cfc76d53200067f65d532002e7c65d532001ebe64d5320006bd64d5320005ee72d5320005ed72d532001cff7695320004fe7695320004fd769532001cfc769532002e7e65953200067d6595320006bf649532001ebc64953200073f5495320005ee7295320005ed7295320004ff7655320004fe7655320004fd7655320004fc76553200067f655532002e7c6555320006bf645532001ebc6455320005fb7055320015f8705532001cff7615320004fe7615320004fd761532001cfc761532002e7e65153200067d651532001ebe6415320006bd64153200073d5415320005ee7215320005ed72153200057e75d8f200057d75d8f20005be74d8f20005bd74d8f20006df6398f2002cfe7598f20004fd7598f2001cfe7498f20004fd7498f2000cfe7198f20004fd7198f2000cfc7198f20004ff7558f2002cfc7558f20004ff7458f2001cfc7458f20004ff7158f2000cfe7158f2000cfc7158f20006dd6318f2001cfe7418f20004fd7418f20006ee7218f2000cfe7118f20
  | 13 => 0xc840014fe760c840004fd760c8400067e650c8400067d650c840005bf740c84001dbc740c840006de630c840006dd630c840006ee620c840006ed620c840007cd320c84006ef6610c840004ff755844002cfc755844000cfd7458440004ff7358440004fc7358440004ff7258440004fc7258440014ff7158440016f7715844004ef6515844004ef4515844001ef7415844001ef4415844004ef6315844004ef4315844004ef6215844004ef42158440014fc7058440016f61058440016f41058440006f77558440006f67558440006f57558440006f4755844001ef7745844001ef6745844001ef4745844001ef7545844001ef6545844001ef5545844001ef45458440006f77358440006f67358440006f57358440006f47358440006f75358440006f65358440006f55358440006f4535844001ef7435844001ef6435844001ef5435844001ef44358440006f77258440006f67258440006f57258440006f47258440006f75258440006f65258440006f55258440006f4525844001ef7425844001ef6425844001ef5425844001ef44258440006f73258440006f63258440006f53258440006f43258440016f77058440016f67058440016f47058440016f75058440016f65058440016f55058440016f45058440016f74058440016f64058440016f54058440016f44058440016f73058440016f63058440016f53058440016f43058440016f72058440016f62058440016f52058440016f4205844002cff76d4440014fe76d4440004fd76d444002e7e65d44400067d65d444001dbc74d44401273f54d4440006de63d4440006dd63d4440006ee62d4440006ed62d444000ef661d4440006f561d4440004ff7654440004fd7654440014fc765444002e7e65544400067d6554440005bf745444001dbc74544400073f5454440006de6354440006dd6354440006ee6254440006ed625444000ef66154440006f5615444001dbf7650440066bf7650440125be7550440125bc755044001ebf655044001f3e6550440006bd655044001f3d65504400063d6550440005bc735044001f9e6350440006bd635044001f9d63504400069d6350440005bc725044001fae6250440006bd625044001fad6250440006ad625044001dbf715044001fb7715044000ebe615044001fb6615044000eb6615044001fb5615044000ebc61504400ddbf70504400debe605044001fba60504400dfb71050440004ff76cc440014fe76cc440004fd76cc4400067e65cc4400067d65cc440005bf74cc44001dbc74cc440006de63cc440006dd63cc440006ee62cc440006ed62cc44000ef661cc440006f561cc440004ff764c440004fd764c440014fc764c4400067e654c4400067d654c440005bf744c44001dbc744c440006de634c440006dd634c440005ef724c440005e
  | 14 => 0x16ec2058840006ef7558840006ee7558840006ed7558840006ec755884001eef745884001eee745884001eec745884001eef545884001eee545884001eed545884001eec5458840006ef7358840006ee7358840006ed7358840006ec7358840006ef5358840006ee5358840006ed5358840006ec535884001eef435884001eee435884001eed435884001eec4358840006ef7158840006ee7158840006ed7158840006ec7158840006ee5158840006ec515884001eef415884001eaf415884001eee415884001eed415884001eec4158840006ee3158840006ec3158840016ef7058840016ee7058840016ec7058840016ef5058840016ee5058840016ed5058840016ec5058840016ef4058840016ee4058840016ed4058840016ec4058840016ef3058840016ee3058840016ed3058840016ec3058840016ef1058840016ee1058840016ed1058840016ec105884002cff76d4840014fe76d4840004fd76d484002e7e65d48400067d65d484001dbe74d4840005bd74d4840006de63d4840006dd63d4840006ee62d4840006ed62d48400bef661d4840004ff7694840014fe7694840004fd769484002e7e65948400067d659484001dbe7494840005bd74948400073f5494840006de6394840006dd6394840006ee6294840006ed62948400076f52948400b6f66194840004ff7654840004fd7654840014fc765484002e7e65548400067d6554840005bf745484001dbc7454840006de6354840006dd6354840006ee6254840006ed62548400aef66154840005fb7054840015f8705484002cff7614840014fe7614840004fd761484002e7e65148400067d651484001dbc74148401273f5414840006de6314840006dd6314840006ee6214840006ed62148400a6f6611484001dbd7690840006bd7690840125be7590840125bc759084001ebf659084001f3e6590840006bd659084001f3d65908400063d6590840005be739084001f9e639084001f9d639084001dbe729084001fae729084001fae6290840006bd629084001fad6290840006ad6290840005bd719084001fb6619084001fb561908400edbd70908400eebe609084001fba6090840004ff76cc840014fe76cc840004fd76cc8400067e65cc8400067d65cc84001dbe74cc840005bd74cc840006de63cc840006dd63cc840006ee62cc840006ed62cc8400e6f661cc840004ff768c840014fe768c840004fd768c8400067e658c8400067d658c84001dbe748c840005bd748c840006de638c840006dd638c840006ee628c840006ed628c84007ef6618c840004ff764c840004fd764c840014fc764c8400067e654c8400067d654c840005bf744c84001dbc744c840006de634c840006dd634c840006ee624c840006ed624c840005f7714c84004df4714c840076f6614c840004ff760
  | 15 => 0xc2158c40016df7058c40016de7058c40016dc7058c40016df5058c40016de5058c40016dd5058c40016dc5058c40016df4058c40016de4058c40016dd4058c40016dc4058c40016df2058c40016de2058c40016dd2058c40016dc2058c40016df1058c40016de1058c40016dd1058c40016dc1058c4002cff76d4c40014fe76d4c40004fd76d4c4002e7e65d4c400067d65d4c4001dbe74d4c40005bd74d4c40006de63d4c40006dd63d4c4014ef661d4c40004ff7694c40014fe7694c40004fd7694c4002e7e6594c400067d6594c4001dbe7494c40005bd7494c400073f5494c40006de6394c40006dd6394c400075f5394c40146f66194c40004ff7654c40004fd7654c40014fc7654c4002e7e6554c400067d6554c40005bf7454c4001dbc7454c40006de6354c40006dd6354c4013ef66154c40005fb7054c40015f87054c4002cff7614c40014fe7614c40004fd7614c4002e7e6514c400067d6514c4001dbc7414c401273f5414c40006de6314c40006dd6314c40136f66114c4001dbd7690c40006bd7690c40125be7590c40125bc7590c4001ebf6590c4001f3e6590c40006bd6590c4001f3d6590c400063d6590c4001dbe7390c4001f9e7390c4001f9e6390c40006bd6390c4001f9d6390c400069d6390c40005be7290c4001fae6290c4001fad6290c40005bd7190c4001fb66190c4001fb56190c4012dbd7090c4012ebe6090c4001fba6090c4002cfe7598840004fd7598840004fe7398840004fd7398840016ee729884001eef429884001eec429884000cfe7198840004fd719884000cfc7198840006ee2198840006ec2198840016ee2098840016ec2098840006ef7598840006ee7598840006ed7598840006ec759884001eee749884001eed749884001eec749884001eef549884001eee549884001eed549884001eec5498840006ef7398840006ee7398840006ed7398840006ec7398840006ef5398840006ee5398840006ed5398840006ec539884001eef439884001eee439884001eed439884001eec4398840006ef7198840006ee7198840006ed7198840006ec7198840006ee5198840006ec519884001eef419884001eee419884001eed419884001eec4198840006ee3198840006ec3198840016ee7098840016ed7098840016ec7098840016ef5098840016ee5098840016ed5098840016ec5098840016ef4098840016ee4098840016ed4098840016ec4098840016ef3098840016ee3098840016ed3098840016ec3098840016ef1098840016ee1098840016ed1098840016ec1098840004ff755884002cfc7558840004ff7358840004fc7358840016ef725884001eef425884001ebc425884001eec4258840004ff715884000cfe715884000cfc715884001ebf4158840006ee2158840006ec2158840016ee2058840
  | 16 => 0x94400067e71594400067d71594400067c715944001e7f415944001e3f415944001e7e415944001e7d415944001e7c41594400067e31594400067c31594400067e21594400067c21594400167f70594400167e70594400167d70594400167c70594400167f40594400163f40594400167e40594400167d40594400163d40594400167c40594400167f30594400167e30594400167d30594400167c30594400167f20594400167e20594400167d20594400167c20594400167f10594400167e10594400167d10594400167c105944001dbd76d5040126bd76d5040004bd76d504001dbe75d504001f3e75d504001ebf65d504001f3e65d5040126bd65d504001f3d65d50400063d65d5040005be73d504001f9e63d504001f9d63d5040005be72d504001fae62d504001fad62d5040005bd71d504001fb661d504001fb561d5040155bf70d5040155bd70d5040156be60d504001fba60d50401573f50d50401573d50d504002cfe7598c40004fd7598c40016de7398c4001edf4398c4001edc4398c40004fe7298c40004fd7298c4000cfe7198c40004fd7198c4000cfc7198c40006de3198c40006dc3198c40016de3098c40016dc3098c40006df7598c40006de7598c40006dd7598c40006dc7598c4001ede7498c4001edd7498c4001edc7498c4001edf5498c4001ede5498c4001edd5498c4001edc5498c40006df7298c40006de7298c40006dd7298c40006dc7298c4001edf4298c4001ede4298c4001edd4298c4001edc4298c40006df7198c40006de7198c40006dd7198c40006dc7198c40006de5198c40006dc5198c4001edf4198c4001ede4198c4001edd4198c4001edc4198c40006de2198c40006dc2198c40016de7098c40016dd7098c40016dc7098c40016df5098c40016de5098c40016dd5098c40016dc5098c40016df4098c40016de4098c40016dd4098c40016dc4098c40016df2098c40016de2098c40016dd2098c40016dc2098c40016df1098c40016de1098c40016dd1098c40016dc1098c40004ff7558c4002cfc7558c40016df7358c4001edf4358c4001ebc4358c4001edc4358c40004ff7258c40004fc7258c40004ff7158c4000cfe7158c4000cfc7158c4001ebf4158c40006de3158c40006dc3158c40016de3058c40016dc3058c40006df7558c40006de7558c40006dd7558c40006dc7558c4001edf7458c4001ede7458c4001edc7458c4001edf5458c4001ede5458c4001edd5458c4001edc5458c40006df7258c40006de7258c40006dd7258c40006dc7258c4001edf4258c4001ede4258c4001edd4258c4001edc4258c40006df7158c40006de7158c40006dd7158c40006dc7158c40006de5158c40006dc5158c4001edf4158c4001e9f4158c4001ede4158c4001edd4158c4001edc4158c40006de2158c40006d
  | 17 => 0x67f65585400067c6558540005df7358540005dc7358540005ef7258540005ec7258540056f46158540004fe76d4540004fd76d454002cfc76d45400067f65d454002e7c65d454001dbe74d4540005bd74d45400073d54d4540004ff7654540004fe7654540004fc76545400067f655454002e7c65545400073d5454540014fc76505400067f65505400067c6550540006f7615054000ef46150540005fb7050540015f87050540004fe76cc540004fd76cc540004fc76cc5400067f65cc5400067c65cc540004ff764c540004fe764c540004fc764c5400067f654c5400067c654c540005ef724c540005ec724c540004fe76c8540004fd76c8540004fc76c85400067f65c85400067c65c8540004ff7648540004fe7648540004fc76485400067f65485400067c6548540005df7348540005dc734854001cfe76d414001cfc76d41400067f65d414002e7c65d414001dbe74d4140005bd74d41400073d54d41400177a50d4140004fd765414001cfc7654140005bf745414001dbc74541400073d545414001e7f749944001e7e749944001e7d749944001e7c749944002e7f739944002e7e739944002e7d739944002e7c739944001e7f439944001e7e439944001e7d439944001e7c439944002e7f729944002e7e729944002e7d729944002e7c729944001e7f429944001e7e429944001e7d429944001e7c429944002e7f719944002e7e719944002e7d719944002e7c719944001e7f419944001e7e419944001e7d419944001e7c41994400067e31994400067c31994400067e21994400067c21994400167f70994400167e70994400167d70994400167c70994400167f40994400167e40994400167d40994400167c40994400167f30994400167e30994400167d30994400167c30994400167f20994400167e20994400167d20994400167c20994400167f10994400167e10994400167d10994400167c1099440014ff75594400167f755944001cff745944001cfe745944001cfd745944001cfc745944001ebc745944001cbc745944001e7e545944001e7c545944001ebc545944001e3c5459440004ff7359440004fc735944001ebc4359440004ff7259440004fc725944001ebc4259440004ff715944000cfe715944000cfc71594400067e51594400067c515944001ebf4159440014fe7059440014fc70594400167e50594400167c5059440016bf4059440016bd405944001e7f745944001e7e745944001e7d745944001e7c745944001e3c74594400067f73594400067e73594400067d73594400067c735944001e7f435944001e7e435944001e7d435944001e7c435944001e3c43594400067f72594400067e72594400067d72594400067c725944001e7f425944001e7e425944001e7d425944001e7c425944001e3c42594400067f715
  | 18 => 0xf65d4d4002e7c65d4d4001dbe74d4d40005bd74d4d40004fe7694d40004fd7694d40004fc7694d400067f6594d4002e7c6594d400073d5494d400075f5394d40004ff7654d40004fe7654d40004fc7654d400067f6554d4002e7c6554d40004fe7614d40004fd7614d4002cfc7614d400067f6514d4002e7c6514d4001dbe7414d40005bd7414d400073d5414d40014fe7690d400067f6590d400067c6590d40006df6390d40006dc6390d40015fa7090d40005f97090d40014fc7650d400067f6550d400067c6550d40006df6350d40006dc6350d40005fb7050d40015f87050d400067f65d89400067c65d894002cfe75d8940004fd75d8940004fe73d8940004fd73d894000cfe71d8940004fd71d894000cfc71d8940006ee21d8940006ec21d89400057e75989400057d75989400067f65989400067c6598940005de7398940005dd7398940006ef62989400057f75589400057c75589400067f65589400067c65589400067f65189400067c6518940006ed621894002cfe7518940004fd7518940006be5418940006bd5418940004fe7318940004fd731894000cfe7118940004fd711894000cfc7118940006ee2118940006ec21189400febe40189400febc4018940004fe76d4940004fd76d494002cfc76d49400067f65d494002e7c65d494001dbe74d4940005bd74d4940004fe7694940004fd7694940004fc76949400067f659494002e7c65949400073d54949400076f5294940004ff7654940004fe7654940004fc76549400067f655494002e7c6554940004fe7614940004fd761494002cfc76149400067f651494002e7c651494001dbe7414940005bd74149400073d5414940014fe76909400067f65909400067c6590940006ef6290940006ec6290940015fa7090940005f97090940014fc76509400067f65509400067c6550940006ef6250940006ec6250940005fb7050940015f87050940004fe76cc940004fd76cc940004fc76cc9400067f65cc9400067c65cc940006df63cc940006dc63cc940004fe768c940004fd768c940004fc768c9400067f658c9400067c658c940006ef628c940006ec628c940004ff764c940004fe764c940004fc764c9400067f654c9400067c654c940006df634c940006dc634c940006ef624c940006ec624c940005f7714c940055f4714c940004fe760c940004fd760c940004fc760c9400067f650c9400067c650c94001dbe740c940005bd740c940007cd320c94000cfe76d85400067f65d85400067c65d8540056f661d854002cfe75d8540004fd75d8540014fd74d854000cfc74d8540006be54d8540006bd54d8540004fe73d8540004fd73d8540004fe72d8540004fd72d8540056f641d854001cfd70d854010ebe40d854010ebc40d8540056f710d85400057f75585400057c7558540
  | 19 => 0x95400067c71d954017e7f41d95400067e41d954017e7c41d95400067e31d95400067c31d95400067e21d95400067c21d954017e7f70d95401667e70d95400067d70d95401667c70d954017e7f40d95401667e40d95401667c40d95401667e30d95401667c30d95401667e20d95401667c20d95400067f10d95401667e10d95401667c10d95400067f6599540156bf6499540006bf7459540004ff7259540004fc7259540004ff715954000cfe715954000cfc7159540004ff7059540006fb7059540004fe761954002e7e65195400067d651954016ebf64195400057e76195400067e76195400047e76195400073d74195400067e61195400067c61195401777b401954016f3e401954016f3c401954017778401954002e7f741954002e7e741954002e7c741954002e7f731954002e7e731954002e7d731954002e7c73195401767f43195401767c431954002e7f721954002e7e721954002e7d721954002e7c72195401767f42195401767c421954002e7f711954002e7e711954002e7d711954002e7c71195401767f41195400067e41195401767c41195400067e31195400067c31195400067e21195400067c211954002e7f701954002e7e701954002e7d701954002e7c70195401767f401954016e7e401954016e3e40195400067d401954016e7c401954016e3c401954016e7e301954016e7c301954016e7e201954016e7c20195400067f101954016e7e101954016e7c1019540014fe76d51400067f65d514002e7c65d514001f3e54d5140015fa70d5140005f970d5140005be769514001ebe7695140004be7695140005bd75951400073f659514002ebe659514002ebc65951400073c659514002e3c6595140015be7095140015bc709514001ebf609514001fbb60951401673e5095140014fc76551400067f655514002e7c655514001f3c5455140005fb7055140015f87055140014bc765514001dbf755514001f3f75551400073f655514002ebe655514002ebc65551400073c655514002e3c6555140007bb7055140015be7055140015bc7055140007b8705514001ebf605514001fbb60551400067f65d8d400067c65d8d4002cfe75d8d40004fd75d8d40004fe72d8d40004fd72d8d4000cfe71d8d40004fd71d8d4000cfc71d8d40006de31d8d40006dc31d8d400057e7598d400057d7598d400067f6598d400067c6598d40006df6398d40005ee7298d40005ed7298d400057f7558d400057c7558d400067f6558d400067c6558d400067f6518d400067c6518d40006dd6318d4002cfe7518d40004fd7518d40006be5418d40006bd5418d40004fe7218d40004fd7218d4000cfe7118d40004fd7118d4000cfc7118d40006de3118d40006dc3118d4015ebe4018d4015ebc4018d40004fe76d4d40004fd76d4d4002cfc76d4d400067
  | 20 => 0xefba7090a400edbd7090a40007b97090a4001ebe6090a40006ee6250a40006ed6250a40005fb7050a40015f87050a400fdbd7610a4001ebd7610a40185be7510a4001dbc7510a400febf6510a40006bd6510a40005be7310a4001fae7210a40006bd6210a40005bd7110a4001dbf7010a400fdbd7010a4001fba6010a40004ff76cca40014fe76cca40004fd76cca4001dbe74cca40005bd74cca40004ff768ca40014fe768ca40004fd768ca4001dbe748ca40005bd748ca40004ff764ca40004fd764ca40014fc764ca40005bf744ca4001dbc744ca40005f7714ca4005df4714ca40004ff760ca40014fe760ca40004fd760ca40005bf740ca4001dbc740ca40007cd320ca40004ff755864002cfc7558640004ff7358640004fc7358640004ff7258640004fc7258640016f7715864005ef6515864005ef64158640014fc7058640016f61058640016f4105864002cff76d4640014fe76d4640004fd76d464002e7c65d46401873f54d4640004ff7654640004fd7654640014fc7654640005bf745464001dbc74546400073f545464000ef66154640006f5615464010dbd76d064001ebd76d0640185be75d064001dbc75d064010ebf65d0640006bd65d0640005be73d0640006bd63d0640005be72d0640006bd62d064000ebe61d064000ebc61d064001dbf70d064010dbd70d064001fba60d064000cff765064000ef66150640006f56150640005fb7050640015f870506400ddbf765064000ebf765064000cbf7650640185be7550640185bc75506400debf6550640006bd6550640005bc7350640006bd6350640005bc7250640006bd625064001dbf715064001fb7715064000ebe61506400dfb661506400dfb5615064000ebc61506400ddbf7050640007bb70506400dfb8705064001ebe60506400dfb71050640004ff76cc640014fe76cc640004fd76cc640005bf74cc64001dbc74cc640004ff764c640004fd764c640014fc764c640005bf744c64001dbc744c640005ef724c640005ec724c640004ff76c8640014fe76c8640004fd76c8640005bf74c864001dbc74c8640004ff7648640004fd7648640014fc7648640005bf744864001dbc7448640005df7348640005dc734864001cfe74d9540004fe73d9540004fd73d9540004fe72d9540004fd72d954000cfe71d9540004fd71d954000cfc71d95400067e51d95400067c51d95401673f74d95400067e61d95400067c61d954017f7b40d95401673e40d95401673c40d954017f7840d95401667f74d954017e7e74d95400067d74d954017e7c74d95400067f73d95400067e73d95400067d73d95400067c73d954017e7f43d954017e7c43d95400067f72d95400067e72d95400067d72d95400067c72d954017e7f42d954017e7c42d95400067f71d95400067e71d95400067d71d
  | 21 => 0x8705524001fbb405524016dbd761524001ebd761524001f3e751524016ebf651524016f3f651524016e3f6515240186bd651524016f3c6515240005be7315240005be7215240005bd711524001dbf701524016dbd701524001fba601524016f3e501524016f3c501524002cfe7598e40004fd7598e40016de7398e40004fe7298e40004fd7298e4000cfe7198e40004fd7198e4000cfc7198e40014fe7098e40016de3098e40016dc3098e40004ff7558e400067f7558e400047f7558e4002cfc7558e400067c7558e4002c7c7558e40016df7358e40004ff7258e40004fc7258e40004ff7158e4000cfe7158e4000cfc7158e40014fc7058e40016de3058e40016dc3058e4002cff76d4e40014fe76d4e40004fd76d4e4001dbe74d4e40005bd74d4e40004ff7694e40014fe7694e40004fd7694e4001dbe7494e40005bd7494e400073f5494e40006de6394e40006dd6394e400075f5394e40004ff7654e40004fd7654e40014fc7654e40005bf7454e4001dbc7454e40006de6354e40006dd6354e4002cff7614e40014fe7614e40004fd7614e4002e7c6514e401873f5414e40006de6390e40006dd6390e40015fa7090e40005f97090e40185be7590e40185bc7590e40006bd6590e4001dbe7390e4012f9e6390e40006bd6390e4012f9d6390e40005be7290e40005bd7190e4012fba7090e4012dbd7090e40007b97090e4001ebe6090e40006de6350e40006dd6350e40005fb7050e40015f87050e4015dbd7610e4001ebd7610e40185be7510e4001dbc7510e40006bd6510e4001f9e7310e40006bd6310e40005be7210e40005bd7110e4001dbf7010e4015dbd7010e4001fba6010e4002cfe7598a40004fd7598a40004fe7398a40004fd7398a40016ee7298a4000cfe7198a40004fd7198a4000cfc7198a40014fe7098a40016ee2098a40016ec2098a40004ff7558a400067f7558a400047f7558a4002cfc7558a400067c7558a4002c7c7558a40004ff7358a40004fc7358a40016ef7258a40004ff7158a4000cfe7158a4000cfc7158a40014fc7058a40016ee2058a40016ec2058a4002cff76d4a40014fe76d4a40004fd76d4a4001dbe74d4a40005bd74d4a40004ff7694a40014fe7694a40004fd7694a400f67f6594a4001dbe7494a40005bd7494a400073f5494a40006ee6294a40006ed6294a400076f5294a40004ff7654a40004fd7654a40014fc7654a40005bf7454a4001dbc7454a40006ee6254a40006ed6254a4002cff7614a40014fe7614a40004fd7614a401067f6514a4002e7c6514a401873f5414a40006ee6290a40006ed6290a40015fa7090a40005f97090a40185be7590a40185bc7590a400eebf6590a40006bd6590a40005be7390a4001dbe7290a400efae6290a40006bd6290a400efad6290a40005bd7190a40
  | 22 => 0x4f40004fd7654f4001cfc7654f40005fb7054f40015f87054f4002cff7614f4001cfe7614f40004fd7614f4002e7e6514f400067d6514f4001dbe7414f40005bd7414f400073d5414f4002cfe7598b40004fd7598b40014fe7498b4001ebe5498b40006bd5498b40004fe7398b40004fd7398b4001eee7298b4001eef4298b4001eec4298b4000cfe7198b40004fd7198b4000cfc7198b400eebe4098b4001ebc4098b40004ff7558b4002cfc7558b40014fc7458b40004ff7358b40004fc7358b4001eef7258b4001eef4258b4001eec4258b40004ff7158b4000cfe7158b4000cfc7158b4002cff76d4b4001cfe76d4b40004fd76d4b4001dbe74d4b40005bd74d4b40004ff7694b4001cfe7694b40004fd7694b4002e7e6594b400067d6594b400073d5494b400076f5294b40004ff7654b40004fd7654b4001cfc7654b40005fb7054b40015f87054b4002cff7614b4001cfe7614b40004fd7614b4002e7e6514b400067d6514b4001dbe7414b40005bd7414b400073d5414b40004ff76ccb4001cfe76ccb40004fd76ccb40004ff768cb4001cfe768cb40004fd768cb40004ff764cb40004fd764cb4001cfc764cb40005f7714cb40065f4714cb40004ff760cb4001cfe760cb40004fd760cb4001dbe740cb40005bd740cb40007cd320cb40004ff755874002cfc7558740014fc745874001ebe5458740006bd5458740004ff7358740004fc7358740004ff7258740004fc725874001ef7715874001ef7415874001ef441587400debe405874001ebc4058740066f7105874002cff76d474001cfe76d4740004fd76d474002e7e65d47400067d65d474001dbe74d4740005bd74d47400073d54d4740004ff7654740004fd765474001cfc765474002e7e65547400067d65547400073d5454740004ff76cc74001cfe76cc740004fd76cc740004ff764c740004fd764c74001cfc764c740005ef724c740005ec724c740004ff76c874001cfe76c8740004fd76c8740004ff7648740004fd764874001cfc7648740005df7348740005dc734874001dbe74d4340005bd74d43400073d54d43400167f7559640004ff7359640004fc7359640004ff7259640004fc7259640004ff715964000cfe715964000cfc7159640014fc70596400167e50596400167c5059640016bf4059640016bd405964001efb4059240016be4059240016bc4059240016f8405924002e7e65d52400067d65d524001f3e54d5240015fa70d5240005f970d524001dbe75d5240156bf65d52401573e65d5240186bd65d52401573d65d52400063d65d5240005be73d5240005be72d5240005bd71d5240157ba70d5240155bd70d5240187b970d5240005b970d524001ebe60d52401573f50d524002cff765524002e7e65552400067d655524001f3c5455240005fb7055240015f
  | 23 => 0x5f571d0921084fe7690921006df6390921006dc639092101cff765092100cfe765092108cfd765092100cfc7650921006bf645092101ebc6450921006df6350921006dc6350921005f7715092100df47150921094fe7610921006df6310921006dc631092100cfe76cc92100cfc76cc921006df63cc921006dc63cc9210e6ef62cc92100df671cc921005f571cc9210e7e421cc92106cfe768c92107edf638c921006dc638c92106dee768c921006ee768c92106cee768c921075ed738c92107fcf638c921006ee638c921006ec638c921007cc638c921006cc638c92100dee718c92100dec718c92107eef618c92107fce318c92107fcc318c9210e4ff764c92100cfe764c921074fd764c92100cfc764c921006df634c921006dc634c921005f7714c92100df4714c92100dec764c921076ec764c92100cec764c921007cf734c921007cf634c921006ee634c921006ec634c921007cc634c921006cc634c921007e7714c92100dee714c92100dec714c921077e4714c92100de4714c921076ef614c921077cf314c921077cd314c92107cfe760c921006df630c92106edc630c92107dee720c92106eef620c921007cd320c92106fe4210c921007d763c8521006f663c8521006f463c8521007d463c8521006d463c852100df672c852100fe672c852100ef762c852100fe762c8521007e632c8521007e532c8521006df63d8121006dc63d812102cfe75d8121004fd75d812101cfe74d8121004fd74d8121004fe73d8121004fd73d8121046fa10d8121005de7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581210057c7558121005bf7458121005bc7458121005df7358121005dc7358121006df6358121006dc6358121006df6318121006dc6318121016fa6018121006f9601812101e7f7559740014fc745974001e7e545974001e7c5459740004ff7359740004fc7359740004ff7259740004fc7259740004ff715974000cfe715974000cfc715974001dbf7655340006bf765534001f3f755534001f3f655534002ebe655534001ebc655534001f3c655534001e3c6555340015be7055340015bc705534002cfe7598f40004fd7598f40014fe7498f4001ebe5498f40006bd5498f4001ede7398f4001edf4398f4001edc4398f40004fe7298f40004fd7298f4000cfe7198f40004fd7198f4000cfc7198f4012ebe4098f4001ebc4098f40004ff7558f4002cfc7558f40014fc7458f4001edf7358f4001edf4358f4001edc4358f40004ff7258f40004fc7258f40004ff7158f4000cfe7158f4000cfc7158f4002cff76d4f4001cfe76d4f40004fd76d4f4001dbe74d4f40005bd74d4f40004ff7694f4001cfe7694f40004fd7694f4002e7e6594f400067d6594f400073d5494f400075f5394f40004ff765
  | 24 => 0xe7618d21006dd6318d2102cfe7518d21004fd7518d2101cfe7418d21004fd7418d21006de7318d2106eed7218d2106cff7118d2106cfd7118d2106edf3118d2106edd3118d2106eee2118d2106eec2118d2106ef42118d21014fe7018d21004fd7018d2107dde7618d21006de7618d2107cde7618d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d21006de6418d21006dd6418d21006dc6418d2106fcd7218d2106fce2118d2106fcc2118d2106fd42118d21006df7518d21006de7518d21006dd7518d21006dc7518d21006df7418d21006de7418d21006dd7418d21006dc7418d21006df5418d21006de5418d21006dd5418d21006dc5418d2106edf7218d2106edd7218d2106ecd7218d2106edf7118d2106ede7118d2106edd7118d2106edc7118d2106edf5118d2106ede5118d2106edd5118d2106edc5118d2106edf4118d2106ede4118d2106edd4118d2106edc4118d2106edf2118d2106ede2118d2106ece2118d2106edd2118d2106edc2118d2106ecc2118d2106ed42118d21006df7018d21006de7018d21006dd7018d21006dc7018d2106edf1018d2106ede1018d2106edd1018d2106edc1018d21004fe76d4d21004fd76d4d2102cfc76d4d21005be74d4d21005bd74d4d21006df63d4d21006dc63d4d21004ff7694d21004fe7694d21004fd7694d21004fc7694d21006df6394d21006dc6394d210075f5394d21005ee7294d21005ed7294d21004ff7654d21004fe7654d21004fc7654d21006df6354d21006dc6354d2102cff7614d21004fe7614d21004fd7614d2102cfc7614d21006df6314d21006dc6314d21005ee7214d21005ed7214d2101cff76d0d21004fe76d0d21004fd76d0d2101cfc76d0d210057e75d0d210057d75d0d21006df63d0d21006dc63d0d21004ff7690d21004fe7690d21004fd7690d21004fc7690d21006df6390d21006dc6390d21005ee7290d21005ed7290d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006df6350d21006dc6350d2101cff7610d21004fe7610d21004fd7610d2101cfc7610d21006df6310d21006dc6310d21005ee7210d21005ed7210d2100cfe76d492100cfc76d49210067f65d492102e7c65d4921005be74d4921005bd74d4921006df63d4921006dc63d492100df671d4921005f571d49210a4fe7694921006df6394921006dc63949210076f52949210b7e4219492102cff765492100cfe76549210acfd765492100cfc76549210067f655492102e7c6554921006df6354921006dc6354921005f7715492100df471549210afe421549210b4fe7614921006df6314921006dc631492100cfe76d092100cfc76d09210057e75d09210057d75d0921006bf64d092101ebc64d0921006df63d0921006dc63d092100df671d0921
  | 25 => 0x9521005de7399521005dd73995210aded7299521005df7359521005dc73595210bdef72595210067f7559521004ff745952101cfc7459521004ff7359521006df7359521004df7359521004fc7359521006dc7359521004dc73595210bcff7259521006ef72595210acff7159521006f77159521004ff7059521014fc70595210b4fe761952102e7e65195210067d651952101cfe76d912102cfe75d9121004fd75d9121004fe73d9121004fd73d9121094ff71d9121094fd71d9121096bf41d9121096bd41d9121014fe70d9121004fd70d91210057e75991210057d7599121006bf6499121005de7399121005dd739912108ded7299121005df7359121005dc735912109def7259121004ff755912102cfc7559121006bf7459121004ff7359121006df7359121004df7359121004fc7359121006dc7359121004dc735912109cff7259121006ef725912108cff7159121006f77159121004ff7059121014fc7059121094fe761912101ebe6419121006bd641912102cff76d5121004fe76d5121004fd76d512102cfc76d51210067f65d512102e7c65d512101cff7695121004fe7695121004fd769512101cfc7695121006bf649512101ebc64951210073f5495121004ff7655121004fe7655121004fd7655121004fc76551210067f655512102e7c6555121006bf645512101ebc645512101cff7615121004fe7615121004fd761512101cfc76151210073d541512102cfe75d8d21004fd75d8d2101cfe74d8d21004fd74d8d2107edf31d8d21014fe70d8d21004fd70d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d2107fcf72d8d2107fce21d8d2107fcc21d8d2107fd421d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d2107edf72d8d2107edd72d8d2107edf71d8d2107ede71d8d2107edd71d8d2107edc71d8d2107edf51d8d2107ede51d8d2107edd51d8d2107edc51d8d2107edf41d8d2107ede41d8d2107edd41d8d2107edc41d8d2107edf21d8d2107ede21d8d2107edc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d2107edf10d8d2107ede10d8d2107edd10d8d2107edc10d8d21006df6398d21075ed7298d2102cfe7598d21004fd7598d2101cfe7498d21004fd7498d2106cfe7398d2106cde7398d21074fd7298d21006ed7298d210e4fd7198d21006f57198d210e6ee2198d210e6ec2198d210e6f42198d21014fe7098d21004fd7098d210e5ef7258d21004ff7458d2101cfc7458d21006ef7258d21074ff7158d21006f77158d21004f77158d21004ff7058d21014fc7058d2107cf
  | 26 => 0xdf47154f2102cff7614f21004fe7614f21004fd7614f21005ee7214f21005ed7214f2101cff76d0f21004fe76d0f21004fd76d0f210057e75d0f210057d75d0f2100df671d0f21005f571d0f21004ff7690f21004fe7690f21004fd7690f21004fc7690f21005ee7290f21005ed7290f21004ff7650f21004fd7650f21004fc7650f21005f77150f2100df47150f2101cff7610f21004fe7610f21004fd7610f2101cfc7610f21005ee7210f21005ed7210f210acfd76d4b210067f65d4b2102e7c65d4b21005be74d4b21005bd74d4b2100cff7694b2100cfd7694b2102e7e6594b210067d6594b210076f5294b2100df67194b21005f57194b210b7e62194b210bcff7654b210067f6554b2102e7c6554b210afe62154b2100cff7614b2100cfd7614b2102cfc7614b2102e7e6514b210067d6514b2100df67114b21005f57114b2108cfd76d0b210057e75d0b210057d75d0b21006bf64d0b2101ebc64d0b2100cff7690b2100cfd7690b2101ebe6490b21006bd6490b2100df67190b21005f57190b2109cff7650b21006bf6450b2101ebc6450b2100cff7610b2100cfd7610b2101cfc7610b2101ebe6410b21006bd6410b2100df67110b21005f57110b21074fd76ccb210e6ee62ccb2100df471ccb2100cfd768cb21006de638cb21006dd638cb2100df6718cb21005f5718cb2107fd4318cb2100ded768cb2107eed768cb2100ced768cb21006ee638cb21007ce638cb21007cd638cb21006ec638cb2100dee718cb2107fe6718cb21007e5718cb2100dec718cb2107fce318cb2107fcc318cb2107fe4318cb2107fc4318cb210e4ff764cb2100df4714cb210e5ef764cb21006ef764cb210e4ef764cb21007cf734cb21007cf634cb21006ee634cb21006ec634cb21007cc634cb21006cc634cb21007e7714cb2100dee714cb2100dec714cb21077e4714cb2100de4714cb21077cf314cb21077e4314cb2100cff760cb2100cfd760cb21006de630cb21006dd630cb2106eee620cb21007cd320cb2100df6710cb21005f5710cb2106fd4310cb21006f576cc721007e672cc721005f572cc721007e572cc72100ef662cc72100fe662cc721007e632cc721007e532cc721007c532cc721006fb60983210057f75583210057c7558321005bf7458321005bc7458321004ff75583210067f75583210047f755832102cfc75583210067c755832102c7c7558321004ff7458321006bf7458321004bf745832101cfc7458321006bc745832101cbc7458321004ff7358321004fc7358321036fa1058321016fa6018321006f9601832102cfe76d952101cfe74d9521004fd74d9521004fe73d9521004fd73d95210b4ff71d95210b4fd71d95210b67f51d95210b67d51d9521014fe70d9521004fd70d95210067f6599521005be7499521005bd749
  | 27 => 0xe748c941005bd748c941006df638c941006dc638c941004ff764c941004fe764c941004fc764c94101dbe744c941005bd744c941005f7714c94100df4714c941004fe760c941004fd760c941004fc760c94101dbe740c941005bd740c941006df630c941006dc630c941006ef620c941006ec620c941007cd320c94102cfe75d8141004fd75d8141066bd74d8141006be54d8141006bd54d8141004fe73d8141004fd73d8141004fe72d8141004fd72d814101cfd71d8141066fa10d8141006fb60981410057f75581410057c7558141005df7358141005dc7358141005ef7258141005ec7258141016fa6018141006f960181410a5ee72d972101cfe74d9721004fd74d9721004fe73d9721004fd73d97210a4fe72d9721006ee72d9721006f571d9721014fe70d9721004fd70d97210acfd76997210067f6599721005be7499721005bd749972102cff76597210067f7559721004ff745972101cfc7459721004ff7359721004fc73597210ae7f51597210ae7d5159721004ff7059721014fc705972102e7e65197210067d65197210b5ee7219721085ee72d932102cfe75d9321004fd75d9321004fe73d9321004fd73d9321084fe72d9321006ee72d9321006f571d9321014fe70d9321004fd70d932108cfd76993210057e75993210057d7599321006bf649932101cff7659321004ff755932102cfc7559321006bf7459321004ff7359321004fc735932108ebf415932108ebd4159321004ff7059321014fc705932101ebe6419321006bd6419321095ee721932102cff76d5321004fe76d5321004fd76d532102cfc76d53210067f65d532102e7c65d532101cff7695321004fe7695321004fd769532101cfc7695321006bf649532101ebc64953210073f5495321004ff7655321004fe7655321004fd7655321004fc76553210067f655532102e7c6555321006bf645532101ebc645532101cff7615321004fe7615321004fd761532101cfc76153210073d541532107fd431d8f21006df6398f2102cfe7598f21004fd7598f2101cfe7498f21004fd7498f210e6ee7298f210e6dd3198f210e6ee2198f210e6ec2198f21014fe7098f21004fd7098f21004ff7558f2102cfc7558f21004ff7458f2101cfc7458f21006f77158f21076df3158f21076f43158f21004ff7058f21014fc7058f21006dd6318f2107dee7218f2106fd43118f2101cfe7418f21004fd7418f2107cfe7218f21006ee7218f21006f57118f2106eee2118f2106eec2118f21014fe7018f21004fd7018f2102cff76d4f21004fe76d4f21004fd76d4f21005be74d4f21005bd74d4f2100df671d4f21005f571d4f21004ff7694f21004fe7694f21004fd7694f210075f5394f21005ee7294f21005ed7294f21004ff7654f21004fd7654f21004fc7654f21005f77154f21
  | 28 => 0x4d4101dbe74d4d41005bd74d4d41004fe7694d41004fd7694d41004fc7694d4101dbe7494d41005bd7494d410073d5494d41006df6394d41006dc6394d410075f5394d41004ff7654d41004fe7654d41004fc7654d41006df6354d41006dc6354d41004fe7614d41004fd7614d4102cfc7614d4101dbe7414d41005bd7414d410073d5414d4119dbe76d0d4101ebe76d0d4101dbf75d0d4101f3e75d0d41005bd75d0d4101f3d75d0d410053d75d0d41006bc63d0d41005bd72d0d4100dbe71d0d4100dbc71d0d4101ebf61d0d4101fb761d0d410ddbe70d0d41197b710d0d4100cfe7690d4118dbd7490d41006df6390d41006dc6390d4100df67190d41005f57190d4100cfc7650d41006df6350d41006dc6350d41005f77150d4100df47150d4100dbc7650d4118ebc7650d4100cbc7650d41005bf7550d41005bd7550d4101dbf7350d4101f9f7350d410079f6350d41006bc6350d410079c6350d41005bf7250d41007b77150d4100dbe7150d4100dbc7150d4118fb47150d4101ebf6150d4101fb76150d410ddbc7050d4118fb71050d4102cfe75d8941004fd75d8941004fe73d8941004fd73d894101cfd71d894109eef21d8941014fe70d8941004fd70d8941006ef6298941005df7358941005dc7358941006ed621894102cfe7518941004fd7518941086bd7418941006be5418941006bd5418941004fe7318941004fd731894101cfd7118941086ed2118941014fe7018941004fd7018941004fe76d4941004fd76d494102cfc76d494101dbe74d4941005bd74d4941004fe7694941004fd7694941004fc769494101dbe7494941005bd74949410073d5494941006ef6294941006ec62949410076f5294941004ff7654941004fe7654941004fc7654941006ef6254941006ec6254941004fe7614941004fd761494102cfc761494101dbe7414941005bd74149410073d5414941085be76d094101ebe76d094101dbf75d094101f3e75d0941005bd75d094101f3d75d09410053d75d0941005bd73d0941006bc62d094100dbe71d094100dbc71d094101ebf61d094101fb761d09410ddbe70d094109fb710d094100cfe769094108dbd7490941006ef6290941006ec629094100df67190941005f5719094100cfc7650941006ef6250941006ec6250941005f7715094100df4715094100dbc765094108ebc765094100cbc7650941005bf7550941005bd7550941005bf735094101dbf725094101faf7250941007af6250941006bc6250941007ac6250941007b7715094100dbe715094100dbc715094108fb4715094101ebf615094101fb761509410ddbc705094108fb71050941004fe76cc941004fd76cc941004fc76cc94101dbe74cc941005bd74cc941006ef62cc941006ec62cc941004fe768c941004fd768c941004fc768c94101db
  | 29 => 0x6ee6214b41006ed6214b4101dbf7650b41006bf7650b41005bf7550b41005bd7550b41005bf7350b4101faf7250b41006be6250b4100dbe7150b4100dbc7150b4110dbc7050b41004ff76ccb4101cfe76ccb41004fd76ccb4101dbe74ccb41005bd74ccb41006ee62ccb41006ed62ccb41004ff768cb4101cfe768cb41004fd768cb4101dbe748cb41005bd748cb41006de638cb41006dd638cb41004ff764cb41004fd764cb4101cfc764cb4101dbe744cb41005bd744cb41005f7714cb4100df4714cb41004ff760cb4101cfe760cb41004fd760cb4101dbe740cb41005bd740cb41006de630cb41006dd630cb41006ee620cb41006ed620cb41007cd320cb41004ff75583410067f75583410047f755834102cfc75583410067c755834102c7c755834100cfc745834101ebc745834100cbc745834101ebe5458341006bd5458341004ff7358341004fc7358341004ff7258341004fc725834101ef6415834101ef5415834101efb705834101efb405834101ebc405834101ef84058341056fa105834102cfe76d9541004fe73d9541004fd73d9541004fe72d9541004fd72d954101cfd71d95410d67f51d9541014fe70d9541004fd70d95410d6f710d95410067f65995410cdbd7499541005de7399541005dd7399541005ee7299541005ed72995411a5bf7459541006bf7459541004ff7259541004fc72595410ccff7159541006f77159541004ff7059541014fc70595410cef710595410d4fe761954102e7e65195410067d651954100cfe76d514100cfc76d51410067f65d514102e7c65d514101f3e54d514100df671d5141005f571d51410c5be769514101ebe76951410cdbd759514102ebe659514102ebc6595141005bd7395141005bd729514100dbe719514100dbc719514101ebf619514101fb761951410ddbe70951410d7b7109514102cff765514100cfe76551410ccfd765514100cfc76551410067f655514102e7c655514101f3c5455141005f7715514100df4715514101fb4415514100dbc765514102ebc765514100cbc765514101dbf755514101f3f75551410073f655514102ebe655514102ebc65551410073c655514102e3c6555141005bf7355141005bf7255141007b7715514100dbe715514100dbc71551410cfb4715514101ebf615514101fb761551410cf3f51551410cf3d51551410ddbc70551410cfb7105514102cfe75d8d41004fd75d8d41004fe72d8d41004fd72d8d4101cfd71d8d41196df31d8d41014fe70d8d41004fd70d8d41006df6398d41005ef7258d41005ec7258d41006dd6318d4102cfe7518d41004fd7518d4119ebd7418d41006be5418d41006bd5418d41004fe7218d41004fd7218d4101cfd7118d4119edd3118d41014fe7018d41004fd7018d41004fe76d4d41004fd76d4d4102cfc76d
  | 30 => 0xd32d8032007cd3298032006fb6098032005bf7458032005bc7458032007cd3258032004ff7458032006bf7458032004bf745803201cfc7458032006bc745803201cbc7458032004ff715803200cfe715803200cfc7158032005be7418032005bd7418032007cd321803206df67118032005f57118032016fa6018032006f9601803201e7f755974100cfc745974101e7e545974101e7c5459741004ff7359741004fc7359741004ff7259741004fc72597410ce7f5159741004ff7059741014fc705974101dbf7655341006bf765534101f3f755534101f3f655534102ebe655534101ebc655534101f3c655534101e3c6555341005bf7355341005bf725534100dbe715534100dbc71553410cf3f515534110dbc705534102cfe7598f41004fd7598f4100cfe7498f4101ebe7498f4100cbe7498f4101ebe5498f41006bd5498f4101ede7398f4101ebf4398f4101edf4398f4101edc4398f41004fe7298f41004fd7298f411aedd3198f41014fe7098f41004fd7098f4101ebc4098f41004ff7558f4102cfc7558f4100cfc7458f4101edf7358f4101edf4358f4101edc4358f41004ff7258f41004fc7258f4118edf3158f41004ff7058f41014fc7058f4102cff76d4f4101cfe76d4f41004fd76d4f4101dbe74d4f41005bd74d4f41006de63d4f41006dd63d4f41004ff7694f4101cfe7694f41004fd7694f4102e7e6594f410067d6594f4101dbe7494f41005bd7494f410073d5494f410075f5394f41004ff7654f41004fd7654f4101cfc7654f4101dbe7454f4102cff7614f4101cfe7614f41004fd7614f4102e7e6514f410067d6514f4101dbe7414f41005bd7414f410073d5414f41006de6314f41006dd6314f4101dbf7650f41006bf7650f41005bf7550f41005bd7550f4101f9f7350f41006be6350f41005bf7250f4100dbe7150f4100dbc7150f4110dbc7050f4102cfe7598b41004fd7598b4100cfe7498b4101ebe7498b4100cbe7498b4101ebe5498b41006bd5498b41004fe7398b41004fd7398b4101eee7298b4101ebf4298b4101eef4298b4101eec4298b41096ed2198b41014fe7098b41004fd7098b4101ebc4098b41004ff7558b4102cfc7558b4100cfc7458b41004ff7358b41004fc7358b4101eef7258b4101eef4258b4101eec4258b4108eef2158b41004ff7058b41014fc7058b4102cff76d4b4101cfe76d4b41004fd76d4b4101dbe74d4b41005bd74d4b41006ee62d4b41006ed62d4b41004ff7694b4101cfe7694b41004fd7694b4102e7e6594b410067d6594b4101dbe7494b41005bd7494b410073d5494b410076f5294b41004ff7654b41004fd7654b4101cfc7654b4101dbe7454b4102cff7614b4101cfe7614b41004fd7614b4102e7e6514b410067d6514b4101dbe7414b41005bd7414b410073d5414b41
  | 31 => 0x90320067d75d90320047d75d9032004fe73d9032006de73d9032004fe72d9032006ee72d903200cfe71d9032004fd71d903200cfc71d9032014fe70d9032004fd70d9032004fd76990320057e75990320057d7599032006bf649903201cff7659032004ff755903202cfc7559032006bf7459032004ff715903200cfe715903200cfc7159032004ff7059032014fc705903201ebe6419032006bd641903201cff7695032004fe7695032004fd769503201cfc769503202e7e65950320067d6595032006bf649503201ebc64950320073f5495032004ff7655032004fe7655032004fd7655032004fc7655032006bf645503201ebc645503201cff7615032004fe7615032004fd761503201cfc761503201ebe6415032006bd64150320073d541503202cfe7598832004fd759883201cfe7498832004fd749883200cfe7198832004fd76d4832005be74d4832005bd74d4832004ff769483202cfd769483202e7e65948320067d6594832005de7394832005dd73948320076f5294832004ff765483202cff7614832004fd761483202e7e65148320067d6514832005de7314832005dd7314832004fd76d08320057e75d08320057d75d0832004ff769083201cfd769083201ebe6490832006bd6490832005de7390832005dd7390832004ff765083201cff7610832004fe7610832004fd761083201cfc761083201ebe6410832006bd6410832005de7310832005dd7310832005ed738c832005cd738c832006ee638c832007ce638c83206dee718c83206dec718c8321bfce318c8321bfcc318c832004ff764c832005f7714c83206df4714c832005ef764c832006ef764c832004ef764c832005ef734c832006ee634c832007ce634c832007cf534c832007ce534c832007cd534c832007cc534c832007cf434c832007ce434c832007cd434c832007cc434c832007e7714c83206dee714c83206dec714c832007e4714c83206de4714c8321b7ce314c8321b7cc314c832007cf764c832005cf764c832006cf764c832007cf744c832007ce744c832007cd744c832007cc744c832007cf644c832007ce644c832007cd644c832007cc644c832007ce544c832007cd544c832007cc544c832007cf714c832007c7714c8321b7ce714c83206dce714c832007cd714c8321b7cc714c83206dcc714c832007c4714c83206dc4714c8321b7ce614c8321b7cc614c8321b7ce414c8321b7cc414c832007cf704c832007ce704c832007cd704c832007cc704c8321b7cf104c8321b7cc104c832007cd32d843206ef661d843200cff7658432007cd325843206ef4615843206fe42158432004ff745843201cfc7458432006ee3258432006ed3258432006cd325843206eee215843206eec215843206ef42158432004ff7058432014fc705843206ef71058432007c
  | 32 => 0x6bf7459132004ff7359132006df7359132004ff7259132006ef7259132004ff7159132006f77159132004f7715913200cfe715913200cfc7159132006f4715913200cf47159132004ff7059132014fc7059132004fe761913201ebe6419132006bd641913201cff7695132004fe7695132004fd769513201cfc7695132006bf649513201ebc64951320073f5495132005de7395132005dd7395132005ee7295132005ed72951320d6f46195132004ff7655132004fe7655132004fd7655132004fc7655132006bf645513201ebc64551320cef4615513201cff7615132004fe7615132004fd761513201cfc76151320073d54151320c6f46115132004fe76d49320067f65d493202e7c65d4932005be74d4932005bd74d4932005de73d4932005dd73d49320bef461d4932004fe76949320076f52949320b6f4619493202cfc76549320067f655493202e7c6554932005df7354932005dc73549320aef46154932004fe76149320076d52149320a6f46114932004fe76d09320057e75d09320057d75d0932006bf64d093201ebc64d0932005de73d0932005dd73d093209ef461d0932004fe7690932096f4619093201cff7650932004fd765093201cfc7650932006bf645093201ebc6450932005df7350932005dc735093208ef46150932004fe7610932007ad4210932086f46110932007cf628c932005dd718c93207ede618c93207edc618c93200cfe76d8532076f661d853201cfe74d8532004fd74d8532076f641d8532076f441d8532076f621d8532014fe70d8532004fd70d8532076f710d8532076f410d8532075f676d853200cf676d8532006f764d8532006f664d8532006f564d8532006f464d8532007e772d8532007d632d8532006f774d8532006f674d8532006f574d8532006f474d8532006f654d8532006f554d8532006f454d8532006f772d8532076f672d8532006f752d8532006f652d8532006f552d8532006f452d8532006f742d8532006f642d8532006f542d8532006f442d8532006f632d8532006f770d8532006f670d8532006f570d8532006f470d8532076f46158532005f67618532076f67618532077b67418532077b57418532006f76418532006f66418532006f56418532006f46418532077e572185320e6f762185320e6e76218532007d63218532077f27018532077f17018532006f761d8132006f461d813201cfe74d8132004fd74d813200cfe71d8132004fd71d813200cfc71d8132075f67198132005f57198132006f76198132006f46198132006fb6098132005bf7458132005bc7458132005f77158132075f47158132006f76158132006f46158132006f76118132006f46118132016fa6018132006f960181320057e75d90320057d75d903202cfe75d90320067e75d903202c7e75d9032004fd75d
  | 33 => 0xd71d963200cfc71d9632014fe70d9632004fd70d96320067f65996320067f7559632004ff745963201cfc7459632004ff715963200cfe715963200cfc7159632004ff7059632014fc705963202e7e65196320067d6519632005be7419632005bd741963202cfe75d9232004fd75d9232006dd73d9232006ee72d923200cfe71d9232004fd71d923200cfc71d9232014fe70d9232004fd70d9232006bf6499232004ff755923202cfc7559232006bf7459232004ff715923200cfe715923200cfc7159232004ff7059232014fc70592320057e75192320057d751923201ebe6419232006bd641923202cff76d5232004fe76d5232004fd76d523202cfc76d523202e7e65d52320067d65d5232005ee72d5232005ed72d523201cff7695232004fe7695232004fd769523201cfc769523201ebe6495232006bd64952320073f5495232005ee7295232005ed7295232004ff7655232004fe7655232004fd7655232004fc765523202e7e65552320067d655523201ebe6455232006bd645523201cff7615232004fe7615232004fd761523201cfc76152320073d541523202e7e65d4e320067d65d4e32005be74d4e32005bd74d4e32005ee72d4e32005ed72d4e320075f5394e3202cff7654e3202e7e6554e320067d6554e32005ef7254e32005ec7254e320057e75d0e320057d75d0e3201ebe64d0e32006bd64d0e32005ee72d0e32005ed72d0e3201cff7650e3201ebe6450e32006bd6450e32005ef7250e32005ec7250e32005be74d4a32005bd74d4a3202cfd7694a3202e7e6594a320067d6594a32005de7394a32005dd7394a320076f5294a32007cf3294a32007cf3254a3202e7e6514a320067d6514a32005de7314a32005dd7314a320076d5214a320057e75d0a320057d75d0a3201cfd7690a3201ebe6490a32006bd6490a32005de7390a32005dd7390a3201ebe6410a32006bd6410a32005de7310a32005dd7310a32007ad4210a32005ed76cca32006ed76cca32007ce53cca32007cd53cca320e6ee61cca320e6ec61cca3207ef661d863207fd431d863207ef4615863207fd63158632004ff755863202cfc7558632004ff745863201cfc7458632006df325863207ede315863207ef6315863207edc315863207ef42158632004ff7058632014fc70586320057e75d82320057d75d8232005be74d8232005bd74d8232006fb6098232004ff755823202cfc7558232004ff745823201cfc7458232004ff715823200cfe715823200cfc7158232016fa6018232006f9601823201cfe76d913202cfe75d9132004fd75d913200cfe71d9132004fd71d913200cfc71d9132014fe70d9132004fd70d91320057e75991320057d7599132006bf6499132075f67199132005f57199132005f77159132075f47159132004ff755913202cfc7559132
  | 34 => 0x8542004fd70d8542005df7358542005dc735854208ef4615854202cfe75d8142004fd75d8142004fe73d8142004fd73d814200cfe71d8142004fd71d814200cfc71d8142006fb60981420057f75581420057c75581420eebf6418142016fa6018142006f9601814201e7f755944201cfe745944201cfc745944201e7e545944201e7c5459442004ff7359442004fc7359442004ff715944200cfe715944200cfc7159442004ff7059442014fc705944201dbf7655042006bf765504201dbf755504201f3f755504201f3f655504202ebe655504201ebc655504201f3c655504201e3c6555042005bf725504201fae62550420fdbc705504202cfe7598c42004fd7598c4201ebe5498c42006bd5498c4201ede7398c4201edf4398c4201edc4398c4200cfe7198c42004fd7198c4200cfc7198c42014fe7098c42004fd7098c4201ebc4098c42004ff7558c4202cfc7558c4201edf7358c4201edf4358c4201edc4358c42004ff7158c4200cfe7158c4200cfc7158c42004ff7058c42014fc7058c4202cff76d4c4201cfe76d4c42004fd76d4c4201dbe74d4c42005bd74d4c42006de63d4c42006dd63d4c42004ff7694c4201cfe7694c42004fd7694c4202e7e6594c420067d6594c420073d5494c420075f5394c42004ff7654c42004fd7654c4201cfc7654c4201cfe7614c42004fd7614c4201dbe7414c42005bd7414c420073d5414c42005ee7214c42005ed7214c4202cfe7598842004fd759884201ebe5498842006bd549884201ebf429884201eef429884201eec429884200cfe7198842004fd76d484201dbe74d4842005bd74d4842004ff769484202cfd769484202e7e65948420067d659484201dbe7494842005bd74948420073d54948420076f5294842004ff765484201dbe745484202cff761484201cfe7614842004fd761484201cfc761484202e7e65148420067d651484201dbe7414842005bd74148420073d541484201dbf7650842006bf7650842004bf7650842005bf7550842005bd755084201dbf725084201faf7250842006be625084201fae6250842007ae5250842007ad52508420fdbc7050842004ff755844202cfc755844201ebe5458442006bd5458442004ff7358442004fc735844201ebf4258442006bd425844201ef7715844201ef7415844201ef44158442086f42158442004ff7058442014fc705844201ebc4058442086f71058442004ff75580420067f75580420047f755804202cfc75580420067c755804202c7c755804201ebe5458042006bd5458042004ff7358042004fc735804201eee425804201eed4258042004ff715804200cfe715804200cfc715804201efb705804201efb405804201ebc405804201ef8405804201cfe74d9632004fd74d9632006dd73d9632006ee72d963200cfe71d9632004f
  | 35 => 0x1dbe7414a42005bd7414a420073d5414a42005bd76d0a4201ebd76d0a4201dbf75d0a4201f3e75d0a42005bd75d0a4201f3d75d0a420053d75d0a4201fae62d0a42007ae52d0a42007ad52d0a420edbe70d0a42096f661d8642096f46158642004ff755864202cfc7558642006be5458642006bd5458642004ff7358642004fc735864201cfc7258642006bf4258642096f64158642096f42158642004ff7058642014fc70586420057e75d82420057d75d8242005de73d8242005dd73d8242006fb6098242004ff755824202cfc7558242006be5458242006bd5458242004ff7358242004fc7358242004ff715824200cfe715824200cfc7158242016fa6018242006f9601824202cfe76d9542004fe73d9542004fd73d954200cfe71d9542004fd71d954200cfc71d9542014fe70d9542004fd70d95420067f6599542005fb7059542005f870595420067f7559542004ff7459542006bf7459542004ff7359542004fc7359542004ff7259542006ef7259542004ff715954200cfe715954200cfc7159542004ff7059542006fb7059542004fb7059542014fc7059542006f87059542014f87059542004fe761954202e7e65195420067d6519542004fe76d51420067f65d514202e7c65d514201f3e54d5142005ee72d5142005ed72d514202cfc76551420067f655514202e7c655514201f3c5455142005ef7255142005ec725514201fac425514202cfe75d8d42004fd75d8d4200cfe71d8d42004fd71d8d4200cfc71d8d42006de31d8d42006dc31d8d42014fe70d8d42004fd70d8d42006df6398d42005f77158d4208df47158d42006dd6318d4202cfe7518d42004fd7518d4200cfe7118d42004fd7118d4200cfc7118d42006de3118d42006dc3118d42014fe7018d42004fd7018d42004fe76d4d42004fd76d4d4202cfc76d4d4201dbe74d4d42005bd74d4d42004fe7694d42004fd7694d42004fc7694d4201dbe7494d42005bd7494d420075f5394d42005ee7294d42005ed7294d42004fe7654d42004fc7654d42006df6390d42006dc6390d42005ee7290d42005ed7290d42006df6350d42006dc6350d4201f9c4350d42005ef7250d42005ec7250d4201fac4250d4201cfe76d494201cfc76d49420067f65d494202e7c65d494201dbe74d4942005bd74d4942004fe769494202e7e65949420067d65949420076f529494202cff7654942004fd765494201cfc76549420067f655494202e7c6554942005bf745494201dbc7454942004fe761494202e7e65149420067d651494201dee7290942006bf6590942006bd659094201dbe729094201faf6290942005bd719094200cfe76d854208ef661d854202cfe75d8542004fd75d8542004fe73d8542004fd73d854201cfd72d854208ef641d854208ef431d854208ef621d8542014fe70d
  | 36 => 0xe7198f42004fd7198f4200cfc7198f42006de3198f42006dc3198f42014fe7098f42004fd7098f42004ff7558f4202cfc7558f4201edf7358f4201edf4358f4201edc4358f42004ff7158f4200cfe7158f4200cfc7158f4201ebf4158f42006de3158f42006dc3158f42004ff7058f42014fc7058f4201cfe76d4f42004fd76d4f4201dbe74d4f42005bd74d4f420075e53d4f4202e7e65d4b420067d65d4b4201dbe74d4b42005bd74d4b4202e7e6594b420067d6594b420076f5294b4202cff7654b4202e7e6554b420067d6554b42005bf7454b4201dbc7454b4202e7e6514b420067d6514b42004ff755874202cfc7558742004ff7358742004fc735874201ef7715874201ef7415874201ef4415874209ef4315874209ef62158742004ff7058742014fc705874209ef71058742004ff755834202cfc7558342004ff7358342004fc735834201eee425834201eed4258342004ff715834200cfe715834200cfc715834201efb705834201efb405834201ef84058342006bd74d9642004fe73d9642004fd73d9642006ee72d964200cfe71d9642004fd71d964200cfc71d9642014fe70d9642004fd70d96420067f65996420067f7559642004ff7359642004fc7359642004ff715964200cfe715964200cfc7159642004ff7059642014fc705964202e7e65196420067d6519642005de7319642005dd731964201eef425924202e7e65d52420067d65d524201f3e54d5242005ee72d5242005ed72d5242005bd769524201ebd769524202ebe659524202ebc6595242005bd729524201fae62952420edbe709524202cff765524202e7e65552420067d655524201f3c5455242005ef7255242005ec725524201faf425524202ebf765524202cbf765524201f3f755524202ebe65552420073e655524202e3e65552420073d655524202ebc6555242005bf7255242007af7255242007ac725524201ebe62552420edbc7055242006df6398e4202cfe7598e42004fd7598e42006be5498e42006bd5498e4200cfe7198e42004fd7198e4200cfc7198e42014fe7098e42004fd7098e42004ff7558e4202cfc7558e42004ff7158e4200cfe7158e4200cfc7158e42004ff7058e42014fc7058e420057e7518e420057d7518e42006dd6318e4202cff76d4e42004fe76d4e42004fd76d4e4202e7e65d4e420067d65d4e4201dbe74d4e42005bd74d4e42004fe7694e42004fd7694e420073d5494e420075f5394e42005ee7294e42005ed7294e42006de6390e42006dd6390e42005ee7290e42005ed7290e42006de6350e42006dd6350e42005ef7250e42005ec7250e4201dbe74d4a42005bd74d4a4201cfd7694a4202e7e6594a420067d6594a4201dbe7494a42005bd7494a420073d5494a420076f5294a4201cfd7614a4202e7e6514a420067d6514a42
  | 37 => 0xc52006dd63d0c52004ff7690c5202cfe7690c52004fd7690c5201ebe6490c52006bd6490c520073d5490c52004ff7650c52004fd7650c5202cfc7650c5202cfe7610c52004fd7610c5201ebe6410c52006bd6410c520073d5410c52005ee7210c52005ed7210c5202e7f54988520067d549885202e7f529885202eef529885202e6f529885202eec529885200cfe719885202d7f76548520067f76548520047f76548520057f745485202d7f725485202f6f72548520067e625485202f6e62548521057c7054852004ff745845201cfc745845202e7f54584520067d5458452004ff7358452004fc735845202e7f52584520067d525845202ef7715845202ef7515845202ef451584520a6f42158452004ff7058452014fc705845202e7c50584520a6f71058452004ff7458052006bf7458052004bf745805201cfc7458052006bc745805201cbc745805202e7f54580520067d5458052004ff7358052004fc735805202eee525805202eed5258052004ff715805200cfe715805200cfc715805202efb705805202efb505805202e7c505805202ef8505805201e7f749974201e7e749974201e7d749974201e7c749974202e7f739974202e7e739974202e7d739974202e7c739974201e7f439974201e7e439974201e7d439974201e7c439974202e7f729974202e7d729974201e7f429974201e7e429974201e7d429974201e7c429974202e7f719974202e7e719974202e7d719974202e7c719974201e7f419974201e7e419974201e7d419974201e7c41997420067e31997420067c31997420067e21997420067c219974202e7f709974202e7e709974202e7d709974202e7c709974201e7f409974201e7e409974201e7d409974201e7c40997420067f10997420067c109974201e7f755974201cfc745974201e7e545974201e7c5459742004ff7359742004fc735974201ebc4259742004ff715974200cfe715974200cfc71597420067e51597420067c515974201ebf4159742004ff7059742014fc705974201e7f745974201e7e745974201e7d745974201e7c74597420067f73597420067e73597420067d73597420067c735974201e7f435974201e7e435974201e7d435974201e7c43597420067f72597420067d725974201e7f425974201e7e425974201e7d425974201e7c425974201e3c42597420067f71597420067e71597420067d71597420067c715974201e7f415974201e3f415974201e7e415974201e7d415974201e7c41597420067e31597420067c31597420067e21597420067c21597420067f70597420067e70597420067d70597420067c705974201e7f405974201e7e405974201e7d405974201e7c40597420067f10597420067c105974202cfe7598f42004fd7598f4201ede7398f4201edf4398f4201edc4398f4200cf
  | 38 => 0x4ff7358652004fc735865202cfc72586520067f52586520b6f651586520b6f42158652004ff7058652014fc7058652005be74d8252005bd74d8252005de73d8252005dd73d82520076f52d82520076f5298252006fb60982520076f5258252004ff745825201cfc74582520067f54582520067d5458252004ff7358252004fc7358252004ff715825200cfe715825200cfc71582520067a50582520076f5218252016fa6018252006f96018252004fe73d9152004fd73d915200cfe71d9152004fd71d915200cfc71d9152014fe70d9152004fd70d9152006bf6499152005fb7059152005f8705915201ebe6419152006bd6419152006bf649515201ebc649515202f3f5495152005ee7295152005ed729515201cfc7655152006bf645515201ebc645515202f3c5455152005ef7255152005ec725515201cfe74d8d52004fd74d8d5200cfe71d8d52004fd71d8d5200cfc71d8d52006de31d8d52006dc31d8d52014fe70d8d52004fd70d8d52006df6398d52005f77158d520adf47158d52006dd6318d5201cfe7418d52004fd7418d5200cfe7118d52004fd7118d5200cfc7118d52006de3118d52006dc3118d52014fe7018d52004fd7018d52004fe76d0d52004fd76d0d5201cfc76d0d5202d7e75d0d520057d75d0d52004fe7690d52004fd7690d52004fc7690d5202d7e7590d520057d7590d52005ee7290d52005ed7290d52004fe7650d52004fc7650d5202dee72949520067f649495202d7e729495202f6f62949520057d719495200cfe76d85520aef661d855201cfe74d8552004fd74d8552004fe73d8552004fd73d855202cfd72d85520aef651d85520aef431d85520aef621d8552014fe70d8552004fd70d8552005df7358552005dc73585520aef4615855201cfe74d8152004fd74d8152004fe73d8152004fd73d815200cfe71d8152004fd71d815200cfc71d8152006fb6098152005bf7458152005bc74581520f67f6518152016fa6018152006f9601815202ebf745905202ebf545905202ebc5459052004ff7359052004fc7359052004ff715905200cfe715905200cfc7159052004ff7059052014fc705905202d7f76550520067f765505202d7f745505202f3f745505202f3f645505201e7e645505201e7c645505202f3c64550520057f725505202f6e62550521057c705505201cfe7498c52004fd7498c5202e7f5498c520067d5498c5202ede7398c5202edf5398c5202edc5398c5200cfe7198c52004fd7198c5200cfc7198c52014fe7098c52004fd7098c5202e7c5098c52004ff7458c5201cfc7458c5202edf7358c5202edf5358c5202edc5358c52004ff7158c5200cfe7158c5200cfc7158c52004ff7058c52014fc7058c5201cff76d0c5202cfe76d0c52004fd76d0c5202d7e75d0c520057d75d0c52006de63d
  | 39 => 0xd76d0f5201ebe64d0f52006bd64d0f52004ff745875201cfc7458752004ff7358752004fc735875202ef7715875202ef7515875202ef451587520bef431587520bef62158752004ff7058752014fc70587520bef71058752004ff745835201cfc7458352004ff7358352004fc735835202eee525835202eed5258352004ff715835200cfe715835200cfc715835202efb705835202efb505835202ef8505835202eef5259652006bf6499252004ff7359252004fc7359252004ff715925200cfe715925200cfc7159252004ff7059252014fc705925201ebe6419252006bd6419252005de7319252005dd73192520057d76d525202e7d76d525201e7e64d525201e7c64d52520057d72d525202f6e62d52520f57e70d525201ebe6495252006bd649525202f3f5495252005ee7295252005ed729525202f6f529525201cff765525201ebe6455252006bd645525202f3c5455252005ef7255252005ec725525202f6f525525201c7f765525202f3f745525201e7e64552520073e645525201e3e64552520073d645525201e7c64552520057f72552520076f72552520056f72552520076c725525202e7e62552520f57c7055252006df6398e5201cfe7498e52004fd7498e520067f5498e520067d5498e5200cfe7198e52004fd7198e5200cfc7198e52014fe7098e52004fd7098e52004ff7458e5201cfc7458e52004ff7158e5200cfe7158e5200cfc7158e52004ff7058e52014fc7058e52005be7418e52005bd7418e52006dd6318e5201cff76d0e52004fe76d0e52004fd76d0e5202d7e75d0e520057d75d0e5201ebe64d0e52006bd64d0e52004fe7690e52004fd7690e520073d5490e52005ee7290e52005ed7290e520057d76d4a5202e7d76d4a5202f3e74d4a520057d74d4a5202f3d74d4a520053d74d4a5202f6e62d4a520076f32d4a521c76e21d4a521c76c21d4a520f57e70d4a5202f6d76d4a520056d76d4a5202e6d76d4a5202f6f74d4a5202f6e74d4a5202f2e74d4a5202f6d74d4a5202f2d74d4a5202f6c74d4a520076f64d4a520076e64d4a520076d64d4a520076c64d4a5202f6f73d4a5202f6e73d4a5202f6d73d4a5202f6c73d4a520076f63d4a520076e63d4a520076d63d4a520076c63d4a520076f43d4a520076e43d4a520076d43d4a520076c43d4a5202f6f71d4a5202f6e71d4a5202f6d71d4a5202f6c71d4a521c76e61d4a521c76c61d4a521c76e41d4a521c76c41d4a520076f31d4a521c76e31d4a520076d31d4a521c76c31d4a5202f6f70d4a5202f6e70d4a5202f6d70d4a5202f6c70d4a520076f30d4a520076e30d4a520076d30d4a520076c30d4a521c76f10d4a521c76c10d4a520076f52d86520b6f661d86520076f52586520b6f46158652004ff745865201cfc74586520067f54586520067d5458652
  | 40 => 0x885401eee729885402eef529885402eec529885401eef429885401eec429885400cfe7198854004fd719885400cfc7198854014fe7098854004fd709885402e7c509885401ebc4098854004ff7358854004fc735885401eef725885402eef525885402eec525885401eef425885401eec4258854004ff715885400cfe715885400cfc7158854004ff7058854014fc705885401ebe545845402ebd54584540063d5458454004ff7258454004fc725845401cff715845401ef7715845401ef7415845401ef44158454004ff7058454014fc705845401ebc40584540c6f7105845401ebe545805402ebd54580540063d5458054004ff7258054004fc7258054004ff715805400cfe715805400cfc715805401efb705805401efb405805401ebc405805401ef8405805401ebf759935201ebe759935201ebd759935201ebc759935201ebf739935201ebe739935201ebd739935201ebc739935202ebf539935202ebe539935202ebd539935202ebc539935201ebf729935201ebd729935202ebf529935202ebe529935202ebd529935202ebc529935201ebf719935201ebe719935201ebd719935201ebc719935202ebf519935202ebe519935202ebd519935202ebc5199352006be3199352006bc3199352006be2199352006bc219935201ebf709935201ebe709935201ebd709935201ebc709935202ebf509935202ebe509935202ebd509935202ebc5099352006bf1099352006bc109935202ebf745935202ebf545935202ebc5459352004ff7359352004fc735935202e7c5259352004ff715935200cfe715935200cfc715935202e7f5159352006be4159352006bc4159352004ff7059352014fc705935202ebf755935202ebe755935202ebc7559352006bf7359352006be7359352006bd7359352006bc735935202ebf535935202ebe535935202ebd535935202ebc5359352006bf7259352006bd725935202ebf525935202ebe525935202ebd525935202ebc525935202e3c5259352006bf7159352006be7159352006bd7159352006bc715935202ebf515935202e3f515935202ebe515935202ebd515935202ebc5159352006be3159352006bc3159352006be2159352006bc2159352006bf7059352006be7059352006bd7059352006bc705935202ebf505935202ebe505935202ebd505935202ebc5059352006bf1059352006bc105935201cfe7498f52004fd7498f5202ede7398f5202edf5398f5202edc5398f5200cfe7198f52004fd7198f5200cfc7198f52006de3198f52006dc3198f52014fe7098f52004fd7098f52004ff7458f5201cfc7458f5202edf7358f5202edf5358f5202edc5358f52004ff7158f5200cfe7158f5200cfc7158f5202e7f5158f52006de3158f52006dc3158f52004ff7058f52014fc7058f5202cfe76d0f52004f
  | 41 => 0x1d73f10d52541d73c10d525401cfe7498e5401e7f5498e5401e7d5498e5401ede7398e5401edf4398e5401edc4398e54004fe7298e54004fd7298e5400cfe7198e54004fd7198e5400cfc7198e54006de3198e54006dc3198e54014fe7098e54004fd7098e5401cfc7458e5401cbc7458e5401edf7358e5401edf4358e5401ebc4358e5401edc4358e54004ff7258e54004fc7258e54004ff7158e5400cfe7158e5400cfc7158e5401ebf4158e54006de3158e54006dc3158e54004ff7058e54014fc7058e5401cfe7498a5401e7f5498a5401e7d5498a54004fe7398a54004fd7398a5401eee7298a5401eef4298a5401eec4298a5400cfe7198a54004fd7198a5400cfc7198a54006ee2198a54006ec2198a54014fe7098a54004fd7098a5401cfc7458a5401cbc7458a54004ff7358a54004fc7358a5401eef7258a5401eef4258a5401ebc4258a5401eec4258a54004ff7158a5400cfe7158a5400cfc7158a5401ebf4158a54006ee2158a54006ec2158a54004ff7058a54014fc7058a5401cfc745865401e7f545865401e7d5458654004ff7358654004fc7358654004ff7258654004fc725865401ef771586540d6f6515865401ef7415865401ef44158654004ff7058654014fc70586540d6f7105865401cfc745825401e7f545825401e7d5458254004ff7358254004fc7358254004ff7258254004fc7258254004ff715825400cfe715825400cfc715825401efb705825401efb405825401ef84058254004fe73d8954004fd73d895400cfe71d8954004fd71d895400cfc71d8954014fe70d8954004fd70d8954006ef6298954005fb7058954005f87058954006ed6218954004fe7318954004fd731895400cfe7118954004fd711895400cfc7118954014fe7018954004fd701895400cfe76d85540cef661d855402cfd74d8554004fe72d8554004fd72d85540cef641d8554014fe70d8554004fd70d85540cef46158554004fe72d8154004fd72d815400cfe71d8154004fd71d815400cfc71d8154006fb6098154156bf6418154005ee7218154005ed72181540cdf67118154005f57118154016fa6018154006f9601815401f3f765505401d3f76550540063f76550540043f76550540073f72550540073e72550540073d72550540073c725505401f3f625505401f3e625505401f3d625505401f3c62550540073f71550541cf3e71550540073d71550541cf3c715505401f3f615505401f3e615505401f3d615505401f3c61550541cf3e21550541cf3c21550540073f70550540073e70550540073d70550540073c705505416d3c705505401f3f605505401f3e605505401f3d605505401f3c60550541cf3f10550541cf3c105505401e7f549885401ebe549885401e7d549885402ebd54988540063d5498854004fe7398854004fd739
  | 42 => 0x70048001006c0000030000001c001002800200100010040003000000000000000008002000000f00ec0060008003000800000000000000000000802a00040090000001000400300100050004002003c00400000030000004000400200100010014006001000000c0004000400c0068028000800200880010020001000402b0000001000000c0018007000c00d00480030000007000c00000880000090001002400000bc0000000001004400100580070000000000400700040170000003001c01a000000100000030000000001c000001400b001000b00040000000001006000b002c0290004000001c00000100010078009000c000000000f0040000003c0020020036000000000200000000000000000200400380018015001c00000600000030009000000800100010014001000c003001c0030030000001c0050000000000001900000160018001001c000001c05f001c00d005400400b0000001800d000001c005000000140060140000000400000040180024002000401a000c00000a4014009c003002800800200030024013001c00000a002e000001a000c00000480030004000004000d0020002000001e0040004000c00000000070028000004c03c0000007005c00600100040008000007800100180020004000001c00b0018000000000300dc000000001400380050020014000c01e00040010000003000801b000400b000002c004c0070000002007800000dc0020000000004400000480000018001002000a003400100000000008003000c004000000a002800800a800100000000000000000000100000030000001008c01d000000600c8000003000800280020004005000000b001400100740000030001000000100000010008000006c00c00140000000006000c03f0010016007c0080044000000c00c0100018000800a0050000002800d0078004006c001002c000000800200040520000000005c000000800000280070008000000801100080270008004000800f00000010010004000000b00080050050003001801c0024004000000300180240038001002c007000000d004c0080000002008800d000401900000000018004001002f0004010000000100100090044002000c000001001a000c00f0000001000c00600280040018010000000000100000038000000400c000000600740050000006000c00400680000024002002c002001801d00080030004000001401b01e7e545965401ebc545965401e3c545965401f3d76d525402e3d76d525402f3f72d525402f3e72d525402f3d72d525402f3c72d525401f3f62d525401f3e62d525401f3d62d525401f3c62d525401f3f61d525401f3e61d525401f3d61d525401f3c61d52541d73e21d52541d73c21d525401f3f60d525401f3e60d525401f3d60d525401f3c60d5254
  | 43 => 0x1801700000040028000001c0020094001000c016000000300280660008001003800d00000000000004000400e003402a00780000000008000400300000000020017002800300000020010005000c02600980050000001002000000000050004002000c003000801e000c007000000100300120000000001001400500010038000002000100000080018000000c012015400300140130000006000400200000370038002000401900140060000007001c002000c0010194000000000a000800000300050054001008400400080040064000000800200840000048015001800e004c002001800500400180000008001000300140000004001000800b00380200000048000c00c00540010008013001c0000004000000c008012401d0004007000800200500180010009004c0100008000001c00000000020008006000000800100000018000001000400040010018007001400000000010000001007c00000000000008001000000e001000300100080008002000001100b0000009c0020064004003802e001800f0000006000000000280530000003000c0000060000003800d000400000080000090007000c031002c000002c013002400400040000004008001800000000010000007000400b0020006000c016001800000100160004000009c00f009800a00180270004022000c0000044001002800b0010002007c008001001e001800000000080034000000000000400020014007004400a0018000002c0000028000000c016001800e00180040018001003000d00380050078003000800500600000018000005c0090004019000000200040110004000006c002000c00d013400f0040000000c01d0004000000800600080060000000000802b0020001007401a007c0000014001000800100b401b00340040004000000000a000c00100080070010013000c003000001600480280004008000400c0038000016800300080000024004000c01a006000200040000010000000800100f800600340000004000000c00100400040000002000000e00000070004000003400700000050050000000c037001805e000c00a0004004000002800080040038001000c0060010001005c00c000000900e4002000402800000010028004000000d0010009000c0030008004000400000b400500380120004000001c07300000010000000003801600100070018003000800c00540000000003000401f000c001003800c00040070000006000400000140000008000000403000600020008028000400000000030034007005c00a00c802700080010000009002001e000000000000000004000002c024003400a0000003000400600a400e00100010008001000800100240050008015002c000000000500d0000006800100e800d001000100000100034000000400
  | 44 => 0x1001400900480000000000000400d0038000000002c002401c00080130000003000003e004000c00800000034000000000000180020014007000400700300160020001004c00a000401e00300000004002000400100100010034003006400f0004002000800500a40000044000002400400080010038004003800300040000010000002000f00000000014000000c000001001e00b400c0000008000001a0040002000000b0004001006000000000130010038001c04500000000044004000c001000001e0000008000802b0010003000000800540000000002000c00700040250008000009c003001c017000000e0000006002c00000bc01d0010015001c006000c004001c002000000a0040004006002f00000040024000001000400800000010004000002a0048001001000500180020000001001400a009c042016000d000800a000003c000000a00c0010000400200140000010001007400000540050000005007000100640040058009001000000080010024007000000000140050004004000c0190004001000000c0054016000c00b0020001000001500240090010009000800a002402b000000000340060038002002001800080360050002013400e00040000000004001400f003000a0040023001000100a800000b8004000001b000800c00000000004009000c000004c00300040000010028003401c00180000000026005c0000038000001c02b0034003002c00d0004008000000300380090000001000000200280020030000000000a010000200040080008004002c0040010017001801d000400f000400300480170050001000c02700040120038007000400000040170004004000000a0078000000401100000090018002000c00000000010000005005c000000c002002800e010c009001c000000c001000002200000000040002000400e00440200004004000800200040010000000002400b000006200180190060000001000f00040000004023004c01100440000010006000001700540000010004000c01a0004003000c02e000400c002c0010000000001c019004400100680000004006003c003011c00a000800000100010084000009c000000c00000180010000004002800600500050000005000800600000080008014002800800180030014001000c0160020000002000000000010030009001c00b0000000008801a00bc023003800100000070018009000000400000000008000003c00e0000007001c00b0014000000000b002c00000140010000021001400b0000000008000200580060000010012401b0004001000400100380000044000000000b0000014001c01a000001b000800000040300000003000000a0058011001800a002800f002003b000000a000400b01ec015000001e00900000010000000000200
  | 45 => 0x7000c0550034000009c0210000001002000000940010014000000c000004401c01b400702200010058002014802100000370044006002c002000001600080000024000001c00300000000000000000000c001000e000801c00400020000009003400400080000034000000c0070000010000800f0054005000c018000000d003c0160004002002803400600000028008000000f0000001007800000000010028000000800500dc0000008014000c0050008000003800e00a8006008c000000800a0018000006000600ac00a002c00c0110000004000700000040044000000000000cc0010000008000000000000020028000001001d001000e006c00000340020020001000001a003800100500070004000001c00d0064003000400100000000028002005000f005c012004000100080150004026000002c004000400000020018000000001500000090004011003c0000024002002400c00a801a000c00c0000002006c009005800200a400d002402f00080090000011000400000040230028000000c01200000b40050000001405d00100000078018000800000040180014011001c0010028019002c00c0070001002000000140110000007000401b0004007002800200000060010015000000400200000030000000c001000000500180030018002002000300040030004002000401d000400e00540030008000000000000b8007008c0010000006005c014000400100000120024016002c01a00340010000000001800600c400001080060000043003c00800000020088000001c00700040010038008001c002001400300180210010000006c00a00000020000005000800b00040030008003004000e0018016000000f00000040030014000c00c0008000000000000400010010002002800000980010000003002c00800000110048000006c0060024001000404000a8000002000d0048008001c0000068000003c01f002000a00300000014002000800f0038016002400f001400000140060050000008c004000000b0014004006c00000040030014050002000300000100040001000400100000000010009010c001003c00b001c011000801000080280004003001801100d8001002c000000c0420014002000000c0000000009c00300080060004002008c0160028065001000e0004006008000000000040004001000400000000090100033000401a00b800000900020004003002c003004001f002400000080090014001001c000005800100000020004005008000600100000020015001c001000400b0044003000400d00780070018001003c0000020002005000200180120014009000c041000000a000000100400010004013002800b004c00400f8002000c00a0018005000001a01a4007016c00800000040048026001000600540
  | 46 => 0x2ffa88a0001614be880000000000caf90e000000000000bf0a3c331a0001586c16b25c00010003551494000056481f6130ce78ba800027985a725402af26fa2c70332b0c337e0001ef223cdb9c7e217308198124b488228549815ad781c084b0ab907b50000d5e0ef25e9a4e2968b6568fd11573739662d298f8d86e9fdc9c0a75839dedf05d48798042807a17e80000f7230e36f83e660e07b26882f001d10a7a50015908960fb4a505f3acd50000d2ab3523871390bb8872e33f4002000c01e00040000010000000c00900500000000005003c00b00200130028010005c0000030000002801b00c00000098004001c000000000900040060138005002c00b00440080058015001c0010000040000c00a000000c00a40040014001001c00100240010004007001001b0000021001c00800900060000016000800700280030008005002c003000001300000060130000000000c0000000000000000980030004000000c00300200040008020000801a000400a0000008000400f00c400400000000008001005400000000000060001001c006001c0020000003000c00800000000008002003c01500bc002000000d002c00200180010000006001c01a0000004000c00f000000b0000000001c0230004012001400000040140000000000402a000800c0008032000000700a00000174000001000600040010014034000800d000c000000000d0000000004c004004401100ac008001c00d0080008000c00200000090000013003400b000c03800180000000006000000e000001e006c000001802502d80090008004000000300040010010002000000a001401b002c00e0014000000800100240170054005002c00000000180000002003001a00000000008001000803e001c003000400000e00030000006002c0010000017002400b0008000000400000000150008000007000300040000000003001000a00400020000003000400a00100020000000000800000000000000009011000000c4004007000300d000300300090000008000c00300000010004016001000e0038015002400a0050000002400b000400000180230028019001000c0028000003c0030004005000000000440000000002000000000300050000009000005500040330024016000c004010c005002c00b00040000048001000c0050004021002807d000400000200000018000002801a0000000000c0140000007000800e00000000124000001000200900050008001003c02a000400600000050000008000000000100050018001004000e00040010004001000400d0070002000c00e004800100000010008000003800a001402f005800200ac00d0038000002001b001400d0014008001000600040050000001000c003000800000c40310000002001800000040060
  | 47 => 0x27334c476519297702a78dd69242b13040414d0000c8c2efcc7e0fda53596da5738495db0035e92e066065000006981bcdc95243e18b6b4e4ac72a69024000baea60ea4b0000000083e90b50589708ee9b8c185ec5a82ac2df145832140009d40c70b3bb09e1f7013c744209c6d600427352e4a80a0f2225a021ed2d000050896cc10b0318dfb0000d6f016f7afa1fba2bc3f684519a0876aaf71764e3c69f2ee8d768bfade4a1b43f116ee1389c3a00016ce56aa4588a080008f20a547a5858a00021a69c1b0f4d4e06bb73d69302c400400cc30ce00031883bf8000599000000007e06f6ac1e00024109170cf48c888f41198046c1fa74264f88948928000b04800054d098428736f29d71ababf00822c81c00000000000002da400011c60000000000108000004e8000000089d80000001d44612a4ceaa933708b00000b6580002082da00af2c5ed7d08748a922fe0000d4ab8818d4be99f3ca0f227471fb2a862d9eeed111df69540b00746ac7e8f7511681ea75923b08f83a708dc1860000a140000889b5ac1804064000119e37a9ed6c12357c1081dd20af882cd5d05eb63929260001aea7329c1ca848ad80b22ea628c9b2400029ab0000d5aacd13941a60558512a5a800036ac86ca74c2a79566b7414cc0002a3a67f00000002396974aeee48800decddaa8416317ec8d5b454000254d965892f000110cd9a2a06761b790000025100020b9cc0b24a87a8db66340f00b5680003390508062246e7599906ae4c000d43a311d650000c3537a285e67fcaf88000b9f801ccae317c0800000c000536a17b3b48349ee058088ff0249468d4f1869349353eb1db1320e18cdaba510309f63708b6a29f44712ef13fce722be50aaeb889eaf53e800079511cd5932a98ad2e048d56a8f25558e585fca56e00004a6291d18241a1b60000297ca812c0ab75000000001680471f42583362868d85290f800007ac30da1031916350a106bd6b236b960752271400084d36766d092b68d900007fd8913b829dcdd8e966a72513bc90dde13a9d76e93313592d94908106a00b8d1b17549b41e3407886542c60996d179da60bd25e44813440483b1965fb8bb8c502b09a98a57a37f2dfea7449720358df0cff01d28e080ae15c9eb74cd042a3a0835971d87b6094aba0dfd913a1042c82ab265841d59bd38be802c7a69fca347e5303719b2e4749d5abb429cc8a3948cb6fac8a65704a45079a1cd831816b9b1630cd4d3dc17721888da00b35af28208b20428ac8083477224aa1c4a4f794528089f8376aca6224e81cc0009f52d8c9ac09dc5f51c2000005326f9cbf458d8d7861186b400029361900000a24250c00000000002a0e6401d9c00c0bea566973645e506c1bb0eac74b9706000000062722b53f20000034000000030a0023b486085832a000329c0000
  | 48 => 0x60494b400019d0000000097793f600000007219e6c0001bd600025903ac8000cfd22688be36322df8632439ebbe73e360a0f222c472b685c00023800002fc60a223d84da0000000332e949a7c00000c94be72dc4c9025cca6aa18c0e686367f41aaa81b8a1611698e0dcc84f4d3632dc978ab1b4cc1824d0d14dad07ae010001fe097e06169441d3d8999ad62988c5294b8ada5c46726ade0b5842827409e3adaadd02b6f64114a6775b7824c2084460506f6a9ae7621dc1dfac6b067c821a0c2126978b3a82fe4c9c8d0aa131bf83520a74e077296a6c88eaabfa12f64cd5923cb972a0260000000273e73b8e163b01918590b77c450339c969030a872aeffc1b93cecbfaf589868302663866e2926184e03055631d8000146ab8675aa632a0d86c48baaacec3c8c49110dc0aad48c4845e361815645779f12b1914e000036c800000014b25d92142d5c91dc4ce89584ab0eb8cf42c320000136269d710542da94cd1978ca36940a6f62a2072bd9ac6eb08600002486b2302f09c6b730c32988c8bb80687d1264ca99af6bb03a208393570b0300e9a91882760000062c539878cab696d0e62ad068a03bebac1d78247c0e22ca92e60002b7a3ff0000bb7776830f1844447965223f938214381482b41df2c6004c26e0227c2b992d4c3616ec855a972c2a18b2e0b34a4ac95f5e4192450ab098c69ab307625c03efda307d25601a7444d0fd4703897a95d9be278004ff78980b692108ae0a876ded8d98220ff2d644fd37b0a3b1b626dfccb6c032a4e783331ed009bbadcb856828c0ccc3451b8402b2cabd2fb54664e29ea603334035027de0000000b0700009438000000319297631100fbad887cdb49647ca7a0000000000014c6c7336eda929d6d090937661a891085780000000000ac1095a51bb212d2db506779914661895c838324f6288a39896ca290741acaad48a39c8e8912cc86323e6469f9113eb1ea6e89fbca1884a0440acfcdf6a46c22c0000be780001a1a96286b8000c9fb45ac7d2932d213304000008200000002a4a6ad812a634933d68636a22f5b28a91c41f448e614057dbf619947b1aa8a4a0a6e8d27b4f29a419cab01a0f341ed8e22101e5cb96ab08c451ba00f7c531592d9ab1c083880000f4c28d6f342411770c6cb3ccd2cab1c6b81fd1b80079c39b0876d8aaa4549e9274adc16b28cc116cba6a04f1da87faa90ac040f09b5c324a9f61ec2dae32041081eac7ce3979fba8040ea62fca5e0c841fbe39c9024000332a9d99c9e877b3c84592c90b47289b7180000a8632b6b7d3586465a89878e31b8e0805929f71f75000264e0712b3354f340ea4fb37487b947219d0be4092b7f04ca1cb1279a41fcaf05738341d1c9bb0a522980000529237a91cb8082244c7ca6fb5e23faa4820a69ebbb572886923d9549168430
  | 49 => 0xa165c76c687b55498f2556cbc8eee32a13aa133b064072ab0a689b7e6ba22c946941c5a6080134ab723548091fce0001e1009f06fc85b33ee00012e0242a3d31aba98a86e1dae73740e65108000791ad84000000000015fa3ce80f869b9ef80000482b9b800047510e85b476da00007152e6a53dad7a7643be9e0b66029200001fdaaec06de5ae01b2abb8002adcb3bcc462bb2a531238092034e0001f64b87800000034c2569a6660001ef6da5104368fa278d73895949ba4c46a28fb0524974884bac506bf1e0aaf49ea4ad9ab1784e030462800008b423aa43d8000618165e0001c1630304e6a6709f096d1d0e4c8250373a80000000992875147412c8f9d58e8fa80000000ca2c0003dc2224cb2a74b0dcc0007a49e2cb86800070c0a9034e00006ea48467f30000000018b0002a23cffa9a838c675b1828000e0933a65a30000000041e0000590310b1746988d06b908de4d214000c7e8000a04843c0c14cf8a318a707679f1a5938000517800022a15dc544adf6dabce8c000049e37626750000000b5800000002746716000079f0000000239acfc12b8315ce56212a46720497b8671a760a3126040ca05cd8f08f60000257c658156a7230ed2153a86c0a8a7546c112ce5f7800000000009878000da01fbd6f79a42dde22f700000dabe58000000352600027180000000004057a13b2efa67c0f2a588380111cb33ec4994edb30b426ab1f67ec1100000000e5c94a8eb607e8e6219a2392d925df8a5faf8800033ce707a8841f000005af9d4ad0b0000807125200029450001ccc1f306badb81dcc83193e8c8c829c6661834df3913c164eae0000275e0000e4a5a34de000000000000000000000041a63f097c09c200036dc0000b4000032fc47d9f6fc0f9414253cdcb04e848a5879b1199131fe7461f500000c305c88000a6127c10002a4fdfd35be18817f66151716c0493d29a8f3da3882b2d71509114a7a2b9de50000c1b01fcc4b17d600000005b93644000000074000000000974551b8070002900cc28000000308c00020ea39f354855499dcc3f1b94a2540000f183166f080009df700896530f867980cc5b492249968d60636858bc738000974320e0002fce3aa69d7c8d2a86bf13128a09170230cb6e667b25bca47b536b4b8cceaeb20969bf2d182c2b285cc5a95d1a010a8c45907803668d6d67b67020731c42b83274d9e76ca6b0868ac262bfcae98f4210f88a602720e21e111547b081ec5a982b2c069cf22be0fb5bf0958e000319cdaca7da894119400f9a698bf2a80c5912400001d4200000000001ad80000000097008cbd840000000cb8df232b393200000268000a299a1200032700002c980001ad48a715e6c289f4a40f0e5176d851ca4301e45b08cfc6508cb00aa196461b041c8a61e2e45d1bfe82a2fb49628000000
  | 50 => 0x9eece88842682f4a3df18e86880f301f6868175a1211bc8cd648847211294be39cd188c89a19906c80dc10490a2a31aaca317da9f38f0628daf6aa542192de935c8648286e4b20d964f6240636e1af685487ae1928990063161016c81d4dce992ab73e2ec3b180000001070d7e184c4ca9d54b94305e3d0111a85695fc79da2b246ca3a5ddba4a61bc1712aef38106d2a41605d088828e9f7f69e0f1e4ba1ca946b35ee9b1a743a93480e1f600d83644e948fdb0bcdc15b7e2ab15d400020933fac0000001b9a00017d20000000b5b1ef43e1b4c0a158ac62eda62b49406c50bb0aaa7879e42307239d9a52c722a500001b04a4ad6aaa248fa057c000000000000000002f1cd16000042185debc1400000016e8abb754445eb120d9d1604a58063e0000000abbee24b4429c10a3a07699880a03c620047f180000001e609770000000099a72e8000479000055b0000000194600000000000db40000000df81e080001e9400009be0001432a59368400000009e1800000020b03ae533600000002d3000000036a40000a4e000000000007f000000000000000ae100003549e709b0879e10394e0c3780c21b200001d528520001e1200000000002bec31aa312d0bb77400000004462eb827b800000033a47dc26dacfd8000ccc8ee290c24ee6e30000ce500004088000000165a3ed8232afd000000029f84ae89d81c431e000026143d180000000fce62c2f0f64709fa393c0001a8b362bf70c4a0000d7e08d87a23d6ddc267bb5cc9f2ac92ac197e80000000a618fe400baf1e0001ff4a5100001b3000000001aecd7f6205a2b63c74f896c497aff200008d379bb3486a18c5472c34ec63e86e8ba4b58405c0000bb82f63000345238015c200002f89271a7e790197a21780009252c4229b0926bf326084c906a68782f227fe02e99510284b970d616f50cc959419586dc27789bda37400008506df13a4000287e000013000000000000000710217800007c800022aa83e8381b15a7e850e29cb348b54080691a2a65b2426d9a9d34691cd6a6884d443715981b4b74e2c91eba44a2bf87e724fc886a22884d95ec8b981102e3907a91329b155d8000d390000b182b62034b3140001a93dc3092a000301066b728e00011f819d9ce45580000000000000010100002b2e0000d4c5e3734e0000000b782e0308b93f8b71b5c0412800015c00c8283f70600000000001ece44009ac8d81e84065073cc02a8fa9af90965ddacc390ce56427a8b1a158749c4f8b576543508a0002e7ac1e09b46c4e32cdc8067aa549fdb1cc18e603500000000faba68cb2c0000000022297000004b60001b105c68156e00b825aaf06f83b6829056b00000002bf9dc92aecc210e7a5a12fc8a8b00006b42203ca12ebc56ea08a3a59bb46529ebcdb3ad2c820af2c3e086e62eea80
  | 51 => 0x1a00000000000000cdaa75600021c0328a6a200000000001c3e413d6485c1c0000002f0b796a0691fa20204269c8f185c4c06429490be931dca1df75c0000000d2492ec00000000001fea000121cce0a69a00000000000000cdb0000b99921490d2342bc65e2ab97d2b4a1c977e66a8000000375e13b872492380008d3887e63f9d0a35f4cbb3541b18000000028797b1c2b00000002633000202642aac2e5da12d04069b7bcb3887a15d963800011f47289f7c00023fa83500003788214a0f920c72af784bee34163cd06643d5b7fc400dcfbe098a66179b14cdc70fc60701a2a5e030fec931098b57a4e65fc22a2000166cc0fc5acaf01ab41cb1a72ce42b10272a9cdb5406f20001fe2b29a5200bca4320000000252c000870aa5233b121244e00005ea80000aa7052ab88374b4aa0676c5800040a014a1e77206d6208d43559b861360a8c1535646269a8461e2928064907ea9128f102e0a78cd1c10f4b35a90274781ba29bab2b0000000cbe05000001446c9f1404c3700000dc32d88ca4f9230d10c40001156c691715910811833008ee00024b4000310cd559bfac561ac600008260002cb84640dfaa8792b27dd800041bac9e282862857308d86fb32d4b2d400060b0f7b0000000000335088a6704a2940008a7ddc3000000082ed96a3ac0422dbeadea00025fe2e183521c20000c41031e3909dc4ac9f1826c6c0003002bb6988a09045203ea000361c0ae36161866f1d7c7aa694bc8000c7b82469722b363409db2ab480000000000000000066f00002eb8c6200004da94f95360000000000152000023a00001992df1b0460000000734800000026c8bf528e40001136c2bb4fec56914ccc827e645c036603a35b2029a4295c3d1809011e8eb699680aa7360667203fa5a5266a67a31c8181940859526ca6c3729a5ada0fe35d9450c0e9278017817671d2f8cd6d8e3297b93b89e693f000031308db0d4905b09172c0ac0cc2d80000003276cb9915cd0d8000c5c000054c00003b6f0a1acea2544af8f48ddd98720ed956ec6a28ac6279ed275b8000000205c7cab3c6000228a72d8000000207067fb1bc8618a2b378f4140000d4e9d9e3de41a8000b38d4ca38aa94f8470000a22532c045a097aa09b6d519004e4130000c810cedb46a2f9aba7634011052c18e0000b8180003536e2696300001f785e73ef80003f5a33644ba95400002cec95958a131878c0ba3060d3c04a745095223a78dda2401e1c0d702a47792816b32343cce884c3602a4d4bca102e6a03640196247c7a61e32768925c306135e74596980210d361b687c94f108f603117b01eea89ac4e806e45ba728393096668c2196b5d91bc7ec918eb160d0048aa04db7eb3f853b0fd2859e1e6202aa5aa82b4cea2f8b9c20a06876ef83f2a722c883f88646241b822c59aad8c4
  | 52 => 0xd99d7f4b899746b320772120364cdeb6eb268246a71aaf909a491e681fa3765c00474a169c1a83a366e000288b63b0000000016adaf83c9d4600000002a8b411905225468cc41ca8ce9ce14f47301b2c28a1644172a1dcd9ccd348e1aef9a59a140a1fe9d68a1999aabc9914d62865c000182a0002a2871a33aa96b0d8bcb1b7f87519a32624a90ac94348208280003d4255ac69a09296b9b560002e0c34400007610000bfa97320aa9f2e00036d8000057416f29e81d436b0bb4b3d6622192633cecdc8d2e51ed5471380000a5654282c417d90caac8e3f28f48f669cba01210c43c41ca855d82300003df8000c14103e0001b6a68b8000b09a9dc3db9c884b68233d974000d1e00000001076c0af0ba4fab5681b08da60d69f0200034e814c074a0000000bff8000000069cced8000b85908e000163d000357a0001f1200000006bb328900000be1d80000653046c814852a3cc1d0203b2318af5800000000000000c8a00000008a2d959a79a50000035962f46776ad00000c28d1220000598000028025e01fe60a0000c63a7a813e0ecea73cc9a3172352673685878640000002c3cbf41c5c0000df6953800007d1d8c4bb80003c131f2000236a46a18f43470716001aaeac268540d9b2eb4c961f6912fb01600022e0c52199cb2e52901dd83d2a8b9e184bf30d23910bd82f40000aa7c0006dd20540de8000000000000004f2587100575bc0005ce25d4b4e0e48739abe369e88b298929c45792630ccc29b47659bb7b1897e192787862020dd0498249ac076ba9c448309da1a0d8cde19667ad2f0c0c9a5eac8016d48fd6bb81a6ab2f0f69ae400aa774d15a7cc1933659c3eacf8959b0e052702620002bfa34b800097c88b60001d8e936840a4ed2cd250934fdb0d0cea0498f28028866a000191edaa9ca4c091ea80519a44d7a9c141c9a77a48b8000ca5f5700000d5f000326219e61740001b780000000b5584ae58b07d60000fa45ff80000002b6c6d68000a88aa88219800030e9fe4cc980000002426000122649610560001ce00000000b7ef0227e0a99a811b13e5801c2854e0502ae3c66f009946c99f1bf44358da2dd119a60000e5205f1f0c6bca50a9cf0a768dc12fe00000000000000c882fd6000294e0bba3e06e040003be26e29965b548b4a29e31c8952ab00a260002bbdb68979621a00007aa9762089382dd2b215466314180001f185b221722af80000003222dd5877c7e7f16e00000000000dc43a8a4928e2925a40100000000b9226e988a3adc00019ac000c8a35f68e98aba268e1a4cc405da22b21e440c9911ad1ac7a59d338070b99b894d197ea86b268576138aa128caa3e9974e37280003b991de1a51af8d21c5c8c71800000021644e5a94393f98840002a051718000d3ba7844f8091c00020ca0002f4e000302c00013
  | 53 => 0x62400026a7ab68b6c00010f821f0400000364c00000000002dc800023b636390d48bf68a43b09fc4b6c8c1a62b97ef00037130ec24546d300000001a8e000154c8e907344231d7413ec53db05841806391448321ce2964800a24d1436dc899f2c51077a87c8dd4a6cd50ec468b5e38223c6a439afed9885e81202177dae1744c5f95441e8062fa3f942c74106d8b7cd2884290fde39e0000dc284581b292cadb8ac1ac6d22ce0000bc418984b75f22fdabb0095b6f92c4e5f94ba62a00000c2d368200000001c610bc77722d68fb2e2e000000037206a40003696b100000057cd30b1236f8c0cc90e000248c0449b1f4dd287c00000000000000cfb12300002b1360c0000552a57400000000000c0fc79918c377c0003d39806c0d66825e404620ef17ce64a0b0c70e21eca6baf7493905453e5a402ad41e1448029db56f18024ac055472f000009c08320001e0600035dc88daf0ecd106d600000000d59a1089ca2e2d5297743b52e861d3a739000000000028400000f6a520000028a800068b32ec00006c6cd7036e0001ac0b151e44d2020f63d6800057c8000cee364b0000d63000191979e8000a8700004ea0000abac0001a320dc2550eb4762044649c018256da2be00017b23de800045a0eec152939e4b5978345f0fe589e80000000de86e90e144d380006e21a1605e800000000000000fee7579ef000010c2220302003d80006caa7b6320000046e000013e4000bc8f3c49ebb4f878e8d1800034987e81fd5c859b22be80b62d6a37bc26bad80a201cdacbda366c2919d61a42be6c58095c26a1158be69da816981e66434f7981d2b9e553a7d02cd84a2263133800014e280d1beaccd09a50000000777716c7b0400027faaf15560d7532f669bb5a9a15000237831410f2634a326a74aaa092028c2b1706f745f818f234728a653b79e0000000000000000000001f986fa00014708812554000000000025ec0002655b5302200000372c34284200020deb9c32ae1f100004ba96de9e01b30313977a2a98b5aa488000757d21600008c04c884690339e881634cd2c8280004e3acac40308ce3c5967c00008f239f6bde0002870bb58c4083d271537273f271217b4ce1a19a3701d30d9f24a400000000002c3625234a23242f142720000b61ace40000acce05c9d4d9e0c10d7292e44338d7000000000002f32bca9c90dca1a2266cb55e2f0a987cbb80000001574ad2000023228d411fb5ec481b1d65c228d27d491fea9218680968748bb780004322734c0b96cac15aa96cc8adcbd31c50a421099b5e11ce9dd3231c44a99d868329f0ae0c3925bc11cc3342b0cafc30c282b0c122c5178e05847226542be8469b39a24a14763e7aff86c715fe5ef2b3566b941c813a10843185ee62883826060f1461c2f560cf2b227cc2a5e48f06849842b14b
  | 54 => 0x235a04c93b1d28d8c2dfc0000da06790aa06f4b819e06c0008c8f0a6abe51e05ea301ea7d5a0215304cc77b83ec2db86720001bf0000000098a000065a000000000009030a420000000bbd0b122fb2d12dc99d6066e8fc5bdf800023ea76e24f00004820000ca5684e4928dcc0e5a74ebe02d94bbdc0006a834185019094a8c2e40584852b5c9000000014aa0f599b39d4ae68d19200ec9692de20bb03c03e4bbc4a99a3c9259cde860203abb2800000035340001444a3700000000000466000068210124538f8e000144ea78000075ecac22b5315e00013b03e821ac3b600003ef04fc3918000000130c00014d200000000000000000000000000005f5cce9a01a6767f58416ab788cc5209cc2000288ec489057baa8ce20001e64000098ecf78000bcf9ca600001a287d0000000100e5e52c2812e0eca1050310c54aca9d19aa390000af45258000cf0946296036b630d83f447b0000000028600000000001a5a7e10c849d76586810a0a35bd8f0e3af1f941de05c27962b82840062200017c0d40b44600028ee48ca9c69e50fac000000008f9a79a572d0c64b855e2ae1e9330b1ceb8ac06be6b7a20c000171c3661236a8032de84a8000d40301400e36c289c2c6e98005f0cb08788ab9ea435e69b1482d93b691134e2cefa21eb1e211a962000009c93028c0259a80a95be72ca0229eb03b25570ac00ee119aac01b6c80aeca0ce8217606d15b04f0acfa16ba310aa4cd6c4ec899dc5280004a358902f20c9ca07aecc00032640002b16909c000d4aa206000247800000001049f46d421f8c26e0000bd2265c00000009fc80000002c2c1d600003b80000e071192ae25772bc29c4c18c23c01ebef8276be06bb0024432d7128c1cd8f322ba9dfc0001faed398d670841166b93877225f3766119000085ba5360c4934a0001c5ebadb1f6667a16adc69ec8a6a47063ebd8c255c240e6e793d60741582a2ba06a69637a800005a4d240f6ca8fa42021cac24ac69a248889d4100012dc00ca36e000292aa9f2f36da713100000c9891cc0000000000d4500004f900000000000afb9e0280fb74a43919ce5a588863991cc4a6e2072bd404f0875862caa40ba22031eda1120a389961de00b9db6e2d9672496827ee33de0b39c4165872451aea191bb00d256a201f1ea59efa13a829b04274e2a177c103380d0ad82cb834cc2e9f3584b30d68000000000017400002570692a733775ce12d6d18983aa90f05610dc20003106b9500180000e7e61d179e70180149848000a9725610000986dc441444b000003bf0b4a3052b5662f9f28ccf371d424b64d6b29b08b6b0cb944faf04c250b48aaaaa54dcb1b1215235fe8560b7288b02dc24c2acc5b1ab6a000322c1540fc028baac8293010c00021e25ef77aa9fe929a117b51a67aa3585338000cbead340001
  | 55 => 0x247f0002cdf02c0f7c000368a2f2aec23208d125040166d238f940761b348b734509aa864e000381a49a0e3e52def01c67891e000313c7b0130e7cf910a0002ae460da5da2f18000381b2c400027200001de8bf9ad8a4348be69aa326c66a1ac494b50820002522a69c000967a3c49e2800000000000000a593f70b800001498bb19420e0102d800025482dda6de000030e000306635929140000000ae6b5d20f92e64d4482e25032262022ab4960426e010d0000361c00074ea6b817c482a22aa4c070caa590003368000136400017c40001ca800000000000d8a0002148c3b075d00006bc7d8800042b000046e8000b4f8bdf31ea52caeac8a420500001712ec879f9460af3350c21feebe32d13045fd378e8061fc80002173bc8267e921760e1cf5344267c000456b7fadc78f029fb00b54ff88b4b8d80003432c5a577b2861a780002f89634144c0000000000818aba4397510e66d000097103ca0000000cb9000092fa9d44c02b5490b8dae0e4066ca9410088a6ad92aa86e187eae0be082090712af5c20038000ac45a820001554000183c95a00009ce80006298000a8406bf81a09d69ee940e7c8001a6f980000000000c390000ca50b9e000241e4e4a2b424ace3a8e9cb64df106b500000348c7addabbb35f2349a2140f60036abe036c64225d604b268435786049a31d56bb9ab7c36323aea1db5d8613a9587a19c43c3b8b1600024d0890a3bc8cbaf1a987096e3e406c000201068aed053000067800037807e90ebe89ba93f0c0115512bc7c634ab7ee0c7323829a0d5c5db83504622d36d040d8039d6b9bc2293d40d60e220001316a910000ce60000000336388b966edc3b61200004b487daf543ececa457e2aba7b7a287e0627b268692f00a512464a480009f96d08c24297800000000001f6c0000000ca20000d8b066988f88df0000ce8004b0c8d4900006332ac61d7a54a55f246846aac4aa831d82da800043a254a9ac604382e128d058f371462a80000000df20000d6dcba8000a3f11e200000000002b5a00000000000e70a06800059a2c025ab80000390000546000035b8234cfa17783e7000000024f21ab000000037ea2ec0bd68d00264b1a92667190000d1fa42408380000001a9cd3f02540b42ec48bc9858d92205697f04deb9a8836bce927e65696fc8f718485651de200019c730088be9bd5c26bde949e056dd7ec06f02700035e86559e3c63e03d4000000031a1c92bcf1bc60c934ba5b1365757c193c1af565c000000000000001ab699200023edd6731d8d85180e6fa000000000000000000ca4b3840000000c652c1419eca461110b0690bc0001fd82e656a14de00033e200016d6b8f181ed8b8000a379074826b1292eb049c54fa730148b5107714000093881e405a5c6d89195e1f881220123562708877e99b63ca
  | 56 => 0x6cc974cc188c78d1234fa862809e6f00f4a1abf5bac5a244600021c632815409922c4431629d5ad635c6223c52eb5e025e0002f5eb5d1826547175e7adacb3c79089600000000003721000000000010bea0e0000bfe8000bef8cb700000005f880fedcdb1b689804bc363436299c6a6800004a8997ae11d3822a00000df80000ae20000e98000262c000000081100006e2b46069320eed26773cdf91440884c68e255976c00000007718000213000000027b00000357d908000d60800000006000000f2cab59dce31680008651e9c3e324d2abd0000000000070f00000001a0ac3aad42000000043a6b0200027bb1506e525789202958b7d80a5b226844a64a03c810436b19843950ca4900cb68ada147c67950ae74337120002bd46548a5c00000003a280002fb80000001fb800000001a80cac3810000c632120179210abf78baa14780006dc8000ded8ab000031e275d8142c2ab2089ae937e69a240b0380322e02b3d262512fa046812ec55b00e330ae800f0134c8af2edc810075a653da66237ad6e0770fa25c28b7800015f4d97258ea931fc2acde367581b7be0251332b73ae7691007927a088c21f358d81cf8667b12d4dc0962680d47039c6c0abd02f334c8baa0b443f09e669e71b1a69d9db4aff53129449af08a1374663388308210cbaba888040000800476224c2ea43200000000786f31cd820a8869d76ec0002f705169cfc0001eea9b700007a812f45b41ab6bbfab4d44c07bc38a0c837198000a4200009ad0a58013000021480001e5874262d23dab91aadba38b12eacc85f811b9d653e2871abd023f7c5c9e2087fd86418dc6b68aa16087371d807e69d9200010884369c4a91f824415ee0f05f2b0b2d4b16fe3ad60e60003698697672a9049bc400012d885f44aa3378000a529f240000000000043201e0000b75aef614f355caa4800000000000000000894800000000009b63700e02c454b7f40000fa0c7e28317ba895aa8c14b73ca09d0940d411340c8919cc99a071e8a969405301c4252132da00028229a1f7d4175929c8b280005450000d0700009a9b81601295885d80000dab8ae86f71e4cb2c80000000000b53800057496701eb00000001e955829c8a81e2bb4000226a8ef903a280b488e0aca2cbd711b6dcaa86a6c7affc8b6034813db04aace03600000000a808000000000024b8677c661a6a0000000a0b0944321a8140000cd40002a037d715cad35000037d769ed77a81c7e9850608a8000000000000035fa000000099b323c0000000a5680004a10a1b7683800a9d96320000000d8897a479aac64ac36d1482b941a2818d410b9054796fab4c5cb003c11ec8cdb29c39e0000000d6422e441831ca0000000858ded8000062a161ed0284b148a0b5287857427a40000a64bcb80000ad0dba650c0007498a5aaac
  | 57 => 0x3070535d200678a400098e944897e96a44a88c56b810b67c5e800043f05ecd2a1c7a0780000ba5800092b8000a790d72a32823827d343e67783685da80000001690db22c9ca679880ca3f5309be061a000086e036d0c0d329e620001d9800000006af8000c1a0ace21a8456695b7dc23f11c02d598d6c7c29061fbb2f02a115da0000a50d4b9ca01480e3874832a4959de163983762ab10c965a216ba00030027dc4000694aceba2f01ded99a732ce229ca2279ea6b8e2afa0000d3a5b8b05800001c6acb0902000242c11f000087e073842799d412c64f949384c52b7088e21c00000001150c0e2bbb1fe000002e9ea2a0c8a9a3d100ca5b826986c9b5fc0ed0584a6996d590661c8863b4b0bd29adc2e33716a0a042413729280958bdcd68074c8c52c188f9a96b1e901ac0001071800131498e22cc526a230387827ab41a5ba3dda292db1a94790046ce07218ded9a42ca4eea678af1083811c306d1252ba23ef74c6b58a94246829941230be80000fcc3510492b21b1ba000000075f1a544a8298e00000007041b964922bd8a3a091b725b54c19230961aa09d000029a51b519f637d041a0000ddcc740120000020c00002218a010202ac9f14e03c5b67eb3710b3b02267a01fc16aa27c24123823c868e2c00021aa64c0000ad2b6f63d7800000037520003760a89e7e2aafa1fa85a0d1a20f20c4303b108461ae628bd23b2b8863ba9983004aa991d67c181b647ba9a47208340de31cf0b8f8d7a25fb0c624e0cf16788cf6c748d945861fde4af2f6e90d955e8871f980000bce00017889d5cf9945827a2615800000000004c794f0c0d0000df0000031b82a000034205a6a1a2000335a65ba3f1d69322e0000d869a814120002e9817880008442cbecca0478bfa00007ae00003fb0000000000000024e00000000000000036a905e47e8982354435458a9b20467126a81b0eccce4a3ac11a0000240c9325712d9a5aa18dc06120aaa4eb50a1e6aff45f98953da39c5692d8020d791d588f240000c20000322124c3898824000000083e09b6215a4ca0000000b0800004d62f4c0000000b45b47a62e0b2810dc00088423f8786a94d08c730842e15ea7f9b26a0001f483b8d948000247b8ff245eb762a943fe92c4dee202e64da00a00006fe559282a0002b5c890135c6ea900620631c2a1e8b6a61b84a33611e0e0a62f60cf51f38af388f00002618cc3243875a5f5a7e03092c06400042cb0360001a961d458860000c1e000000077a8ed60000e536b2c0009148000da8ac66d6980002450a4800023eb000106202f3006a8996b40c51c78add2d2d0000b200001c9c6f2b3960faee9e76ab71b53dc0008ca8ce6dff8000c1a91b0a8a80007b99f569db0000515b422000313693090186c297428201b68b3e6532c878054b864b460000000000000
  | 58 => 0xba73db5d64d209b2648922800005527cc800091c08d20002cb110e800027e3650a578f3cd4c89167f4a652532138091d6cf46e989a21d91c3651e21220549e48253147e5678fc753aabdd2449c180000000000307a5d42ff094a0c06000000000000006a6000000001be5f80000a9d0000cc92616000206000000004360000e0480002f81f1c4c28000000003ac2f8000daf000000000009bca294000191d93300000d3000000008b98332cea6ea03de2c9a693693ad9065b253c4efa9180000fe8565b08200036641d8a3b44a3a30c23694ee85100003eaa0bc000053e06aab5f00001ee8978c0aa2f5d62b3614cda7b950c82c81b8a4e02f654a2b640000d7c2f561554be0b08cac104951e86145bd021217f54d43b072e80cd819892b04065ceb2b28ea237ea012f18942168ea4b8005dad09646cf8000af937c2a9277488d680003d53660b78c0001820000a51820416a0000a6b35d08d7269eb338278c58b815bc36f167c58000b6785627570aa80e88000db41346b4c0000afa8eaf0b32af6d3d9ffab499aac2840802d9613ec9662882b11a55e77fa736950f69a1d3cba468121b60000000d84129800000002a2800085f8000afc8d2817fa830aeb943cb5cb318db953062a38fd3345a87d1d980009f19e240bfb6efa9b17ea3f0505f00023b900000007b8a4f8000000000000007deb7d60001804239037805009769220a14905078071c2f461149cc6b3f84500573408dd0969e685182b04532a276b400050d0000c0cb36e0001d7a873a54c950819916f8f6840085bbbc99488dcfa7c880da688d97e3240000f88a3823041db8e904fb80002dd06dc000233e0003552000019a4f328b46ee0000a2714b8a9808ba0000000109acfb3185c6e23a2464beb2b8a95ca17a0002e8437582a69daacf68ffab0f8b7aef2ad8143adce26e6238d84f37a53520b02e0791debc6845af52bc0f2915ac11da546a5ce3d744e006c17047da00002f6ad20000000008ea5460000d88000001ebab1ac9b353764db44000c085318abce8f6aaa0c204a5b28274b04361310e029dfaf1300029658f1c000c5db7a04b48b3e00020492a0861276e214a029171e4eb952cb5f9ecc42990668f5b54eadf89f60000467d6310eabeba9f942e971475c032eae49f009fe013e0ce8c2b0ad8634a3d216040aa5047be9e5274c863ca249b3a0ab5d392bc800c2b293acc35b2d64e99f66c2e03f82ad9516e0390b05e1881014321625b623389acb718c9e81607da855a1e061653d7088a42d2c212ad28961669ad2b2f548668d1934319326e0a0b09c4d99756b77107cc5717186a78e860a2a1414549ff06ce0a3c3b4126cbc48cf00001f089bf9aa63fd9dba4de25c0b50019ea58631a1c02b3ccee97c630995d6014238ea2805e05b9a05a189246517416519580cb2cd
  | 59 => 0xfe0bc7ab74000000000048fb20cb268000907088293c265082516260642e602d3a5f6a8d0df9b479d5056328944072d4ae00c5aa3f61f22a7011c8d0a085c49512646861ae813f777a317a334de2a6646c2e2b891ea6424492712af5e8b27488000a41230a37fa8c05d700003b1260a33c9454500a56c79e30e267eaab8c91ad9c6cf0000d66000000000000000794b4380000001e74dc0f32cdfcb43800011b405e156899d155a1d00d53d7109e0a6f2a564dbaccdc332dc22f7970c474056c00005284b1ae3a5670516bcc14f29a3a264a9180009c3d0fa0e32b966f38d088bd8de680b20bf509b1c0a5a675a17f16786f41dec63f06e0d8f8189441342a77681da6d3806a03ff4d639426e45f61ec43abb796016340054181802bc0172d9eae4ca1d056e61f89e8c2204e478d8f84a7782220732ea0859816e1c72b1d0203369c239d3611bf4ea530ab0e0002c3884fa39e405145cb40346a8ee2d32ca82edf2b91f78c408000d638f38b799fc09c383c707ab43236729fa50b83acb5480003eee53a0002b8e0001e2800005961b912865a48d040002967cad2128100a1bcb7a337ca962910bef01a4cab2e7879417d000036fc1460c9e000000089109420001f2cde9a0e00000000000000029101ce72d08b85be9234c0c25166c30ffe29cb6540818e680940c66a6169ad8c2dd90851b4768f5431a82e31505c276042810ef400024dc42da51a04790a2e02605e1d706710002c74b1a2bca00005c0b3160a0a4f05463c6b38e4e600006bb90e257a2faa9bc6cdadb9d9440e12ae8830010e1573692b9f0f12000263e9b96aac01ca8eace3038a000265433829c952c0ee400024ba00029dd00000005540aa454e80b43c22a16a7400002ce22d4162289e6a1152e7084b886e3861e7df667a8278000226898708c13d07d01054c9131ae1f28408588adde30586aa00023500002e086be8f0ad6c0ec840d34ae3c993a0473aea43956606a2e816d800936c2589f58cb88b0473d0504c62b7d0701102c7c4235eb1b2f8a0b5893ab95aef82bf08ef1738e6e8a20bc0aaca0290000db02280000a03207c19980000003558163a0baab2857e88821612c888a2571951e61680007b280007fb23e40002216a4580002a719a2000379acf90a5501b0e1a59da5b0d36a030bd894ac3bd8a9641440246c38cc61341dd86801d0867e28a2000348c1ac04880000000d86a70865e1e8a1653202087f5d4a0d335ea6d80006ac016493a310e021800000026ce000200800002ba4aa941600020890003028b83ae8a5bc8fd75132a8e0000cc5cb3282627390730002d047538000b7c9f6e0ab96c011e89bd0df89ec0808ad645789e49918000444800000017200000d9e000185c271a6cca6200001ae12ae0001f4c39d22fb59f89d2358814e07cb2140001dde00036
  | 60 => 0x3d00002c224de845c90f324e8c580b247c27eacae8f80000083a9c7400000008d0bdb0ede4da8000c76b6d6815c0000002d54a2315a060e95246ac85aba851682c68a7b86ae245609b177c6628f0c3131b7a4f2a7e4000312400037540000000e07c0007ea85d80000000b28633a8829caa0000000b9798ba0000000c0a40003a3935a34f000087400001b419c000011760000fb2af08d0e00032524744b5065f24288abaf8613481921c523729e78652482b6f405500003e6896ac152cb6d9c8a780000f8f7322476b3300aa005b4bc620abba38bad588ca2f845e802ead4e8000b0e9cd84a9173c75b2b6d9a7770284c87b4d9c564552f022c67800000001c8b85f0980000376cb8d000009803ce15138143328000b0402a3c979fa300031de0002a21539000042436f000011e89b5837617a8000257a2a6bce0bd41a4824b61f0000b2f0b94195b6a600020e4bdc93865cd00006c184fe401f3663649fa83482b1ed049356000223a0f89d40ae71ce83748edc0e1429e000000000007b8dfa25e600026fdd5903f00000000337000088f2b292319038154415000000006ec80001bab3ae174b5a28498000c170000c08e466000053a00000a800000000000d5bde70000000282e8f04000000297a00027d6ac540000902cd39f4a24866fa01e92a000000026027df9fd7d4836d496998e8000000040d67967fa3468484029229f10f384094fe01dad68000267f0999af4cf60decb92037ca03aef07a30a86000000000012eb00014b1b1f00dc1bba68a93e8000000000000000000000000cd55cae7e2b81318400003d935b8836b56c72cdb439e999764d8b6d2de18c91c9e262005635503110cd6149819c9471a462b11eec232b02ad031bfc718a8d87750b982bba10450a2cae90625cac66b3acccdaba8bb51e4aa8e23ee238856aaf236e80001fee88626d4b9cb5e62cea77c9d29b28413ae7406590cc0f64000e01943e0533677749231db3010262b7a0f264c89b06e62502cf703a69570000adb80009b0364e0002e82857000055ea772af7099899449a4d3d1c7211db4725928000e04582e4170eea00000000001162928000029fa976aea8000267000066db51e0000000ae620af896800012c0000000148e000070a88025e8aabae100000000000174600000005484000aff80009d12b283fc40000000000b2580006d79f7456cb5f0bb92dbc3a024de5e280003a10496703d7b30002d2800028aa0000523b28e70c000329d0f40000770665dddc000054c93605281b487ac8d82c1c80008cc9d728faa4911a5a0160002b9f216026a34bc70e3fd0afe168a490871241a16e892069714e619c382a24f9db02581c0221503ba9c52296b7e0d1e0ff9c444e68000df8acb78b1aa478ec3074a520d7ba9ab7ca53a2e9c3f2827e24929900d2b65a2
  | 61 => 0xbb2c4a80000002a7263c1fd400017e3dd62384697972680c99f40000a1f04a80006301dbe85401a06ebb6906c000001f52e12abd4ea474a965671195083cda9da9a92b942fd93e644c806653400c61bd5cb80b79c6c2bd8a12173ce0e28827f040fef8fcce80009fd179231b214c21f58ea7fc81a68338fae00001f0000060c92c80005d9b24872f8905000024c0001f4ed12a5240002d24a826f6800020870002d460000cb549d8e365cb9372598000060c80001da023c8731d52b7271463c70c3803e87f281fd0ec1e999c479ca40034fa19c2232e9063219d228908e683585145149cc9a322cba34b0ca601d1f9e692271e4f021fc95a9fa2b3a1d3cabc27f6015dcec67b40001448b60457ceba0001a906ef059c9ba5eacbec0000afdc0000002518c1313da92569b03d4889200000009f7d0d024600000000ac8a9fb6e35b718f27e255ee0003280061a6d298a88e064495c0906c000db90000bf4af449adab8c32323cd56d2d7ac4b5cce1b47750a1824d82bb2de405f9e68b89d52a730da92df7b66b96700b1b1c1efc5692b2678f93c67e19ca39ed28480d9c195183943088b5808175065ed66a19ea2deb8807e116a2cf181a7629c9a377927c110a2e8caaa238c55099e000000051a80f48c05ee8df3244e83f22c2c429bb6b0aaa32a78a62e56ba868276adec816d33e9180d6628d34933560c4615e270a258dea76708e76d2e2aa5bb68000a46a1b01182e320cd3474000211e1fb18bc736f6cf80b54f8000163ec478000386222a1eaa3fbd02af761e41cd011316a0db105a0000078e0000000d349b82000000065c9c3409bab30941863919898ac0c3c0000000000247522c0001050442124458d67bc43780000001c2c10bdf547978000000000000020a2000000000000004bd99dacdca9d852ac000d379b4400023ccb2d00002d50000000291200000000000000add80000000e5ad0eb30e0000ff07452cca47080005f70b52a9c00008bfc1c232f07b35d28f78000217581417b6000226c0000000a9bc000a9009bc0001c524df2be096d99b0cc494ba6a8a6f44f782d224d91205baa7c76438000a6813a235a9ffc6b8962ecb4227e8e5200c86a248a9e20a5ea8a6635387d32616e2d482862782c5e2ab460f40001fd34302710346e014e928f14560c13935487c086c33ea95f16188645400c74b14aeaedeb1782d98c80600000000cfa431396ca40000175800017ac9c586440ea366ac8e81bc000105ac6125f4704a34c39a9502ba3092c00028b017d2b42816313463d961a0000fba1ca13506f32d059af17fc5fe0b7ad5b9d5b92f1114b21131c0172db88c36198cb013c800020140001e9e8239840c09a8a3d6b9c4e449aa9eb63a8e6cd91f340eaa6725e899a455c80000000ff263ba72c000336003dc0000002cf2d282
  | 62 => 0x8f3e00009509ffaf98b6c0cc838909fc0002db49eaaa07931b1427530ef096a904476680000b1b44285c28001d180228222344000100a6d4894a47f0aa2ded000000002c27263638d1ba6361c1006038c23460d11abcdbf99827092aa2e07a30640d8cfeca9688876921be0e8179c1f09f90bdf0e598431a8cb27c0005be154200011101d358c46ab95043aa11b71262b4421e128aa5261e8132000071f1eae6002980dee8dbc77297cc366adb6b37ae28da229ce80f0bbec2c183e928a6268a32cc477c0f98abf0000cec818a619967acd5eb7326a901e0c1a13cd5f859e6902f92bed93428c20b0e265211814935572779b6400021d829a800000000000002dcc8a2690300003077ec1c8eafdb1d4bf8815ecfe9cac92c2a5b8e8666e19fa2157e38988beeb62604023e304ca934d919f924ff00eabac9e4e6432eea1732696a112d3ab3069fe9da13700002ce638cd5786cd8b42ac9093d683a08336916aa6070b663fe005abf8048690473062e288c408680000001f262272e1cb020b90d019fb68c0c898b8268546f80e4e5f173008df01285839d34905400052ba124a8cf5601a0a2129d22cc6309214e883c580bc1b186d2343948c1f0806b39728acaad0ad598862000121a4c7e3621f68c08000338a8f508422cc9c505522cb0ad14c22b23821c190a064d2696acaa68b343156f08a6310ee399a43a68e92a83e8538c960a3ce462a71c486380dd251b9073f84ca00013f219b40000000000b5f1c808c800564611dbc30a9d71d97a9243dca0a4d340000159da6c64fdd6400014f600000000da9a38874af241ac970e3c92968ba397fa5311dacb4f00005cf8c2e000335656e1ada8e224d617c80fc95f9c0010b994bb3c1e303840d90bd0af023c80000000000000029c25e06a3c0a31aa40000102a5a99886d00f583fde9d9b2a33e0908b47c9b10d327e58162bfb00003518000c7a00526d40000d80b6cc00004eaa9e800030a0a3e0001a77000225c427024900000007811ca503d40000001996ad1c0007c3b1fc18724eac6c000000000002f74000e0840007958d2dacc62460000fe622411ca8c090e6ae00000498a770000260c11a8000a71f44ec6400009a040007ed0218a6bddf4382862e59024f460dc000626ad44a00a190640838e0002f102868ba061d80006b20c8e04e1042d8796280beafb2000341a1b1c00049cb10007a000043f8000990e9350000000262b77e88d30e68809ffeb3819bb0000b30ac4a99811035280cb2937180b6008f6cc607dcaa36487ab0bbde1ae63b7f0860b834625f90c3e19429ecc99891a00005665781ddf8e42ed84a55a061ea1e227b7220e606c582025a44832f98a4568afa816c240800031a0000007e1f40ad2c7b0000b80aa31519a96e5eb80000000000d1733b00002ff655fa5b80001ed0
  | 63 => 0x3a4a7f18a85440000cf000008e30000cce0b7000029f2000081ad50854252a23e7b59855b6d1b3a82800380c3c0ee89ba8000bd937880000cae8bc06b782604ba9a1ade20000e345589172b0f9c0c20584acca436ee1969cfa3ee00003f81f601ff1d48cd2b4040000b96deca9820002fca52fa69c144073269c29561c800000002a0877a66ae00000009364000c1f02fc2422ad4674679061084d6df48000c982cc70000a0e536000000020a10000b1ec311f0a91ae3e2113870c4cb88bc6e35a9a9eae49853f26ee03c311c0ac37ae4e222ac1ff94b6e0a1ee40001e90a2da86600036a800009f266180000000000000348a000000001c000050a80000000000000321c0000946cfa80004e10000d130fd08b6b580dc1e70059c890cd54d7be33ba0ec8aea640b7480004888000599800000032f40002ab6829485a2488afa0002dee00000000000000410000000007e40000a2f6990a080001852c102dc0902a810dc7dd57818c000b6615f6000009000000002a6283a3fa77720001efe65c25783d8b2d2000114a000187a054e33cb5c0b2e39005b4de62a64cf98000be1e96cb340000acf800000007821ceafee495b22ad459962623992c00030f6b729b9200a22b60002e14c1c30e8000265690a80000002ce2a2e11066fbadba99c0000b9106f45f0a55803b8000b8aa038993764adcd334285ecbb42914f74861c84e9bc0e88ab9b0c082d111c75a1c2a46f874bcb20774112b29e301208b0db74245e6030c2ff02da64ea8188439bf6dbc65384e709e22538000c070cd80001910d371bf277436ea0758000a3e31bed5a80002700000000297487f907e0002348649d33cb5651ea6dd9cf177469baa9b98966a21616c0614a28d28dee91d00000eb9d127f607be48ea79200021826642e2c4feabda95481757a7c6e20000000632
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xaac8259254440051e90cb8ca8880031dd9571951100045fc22ecaa220008ef825d954440011d904bb2a8880162f21d645511002d1e42ac8aa22000a9c83591544400155904b22a8880063ea1b705511001c5e422ec2a220008ef825d854440011d904bb0a8880022f61f64151100049fc3aa82a22000a3e8655054440014790caa0a88800f0fdd954151100061ebb2a82a2202db388055054440051e90cb88a88800f2d19171151100069aaa2e22a22000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000c6c75dc96244001958e9b92c488003331cf72589100066a39ee2b1220008ef8758862440014d90ab10c488002ab21162189100056641ac43122000a6d85d8b524400195ce9b16a4880032b9d062d49100147a432e3a922000ce7625c7524400717d09bb4a4880022f61376949100046f41eed29220008dd83dda52440014db05b2ca4880063e21970949100063db2ae1292200087f855d9524400117f08bb2a48800e2f21176549100046fc1aeca9220008dc835d952440011df04bb2a4880161f21576149100045fc22ec29220038bc845d852440011bf06bb0a4880023720d761491000476c38c429220028f4865c452440019c8c4b88a4880063e2197014910006373aec5a122000c6e7518b42440051e90cb8e84880161fa1776909100043ec2eed21220008de83dda42440011bb07bb484880063e21970909100043fc2aeca12200587c855d9424400117f08bb2848800237e0d76509100046e41aeca1220008ef825d942440010ff0abb084880161f215761091001c5e422ec21220008df835d842440011b906bb084880023b61c62109100147a432e221220018f8865c0424400b0fd0bbb464880021f617768c91001c5f426ed19220008bd84dda32440031f10cb8464880022fe11764c91001c5e422ec99220008ef825d932440011ef02bb264880063d204764c9100147b436e299220008bf845d8324400717908bb0648800e2fa10760c9100045ec20ec19220008ed87188324400159b063106488002b3a19320c9100056643264192200dbc4814c832440051e90cb886488003714c9710c91000c7c432e019220028f4865d5414400166b0a322828806eec20154505100059ac2e86a0a2000b3585d09414403717b0fb2680880bb0f19075501100061e3aec8a022000c6c75d892044001958e9b1240880031b1d46248110006563a0c490220028f686dc520440018f0edbaa40880031e1d875481100065c3b6e89022000cb8761d12044001a70ea3a240880063e219734811000c7d43cc490220008fa871892044001ec2a4a8a4088003e85094148110
  | 1 => 0x6c5b2e40900171e9d865c81200ee5d3b6c99024003cba761932048001c70ca326409000a3e20176550200143e43acaaa04003a3c8459554080051790eb22a8100168f21564550200049fc3aa82a04003c3f76550540800187aecaa0a8100b6ce201541502002e1f32ae9a984000c3d655d353080051bb0f31ca61001697a166394c200146e43ac6a984003c3e645d7430800187aeab26861000a3761e6390c200145e43ac8a1840028dc8758d430800717d09bb4a4100022f61376948200046f41eed29040008dd83dda520800b4df04b2ca41000a3b61e629482002d3742cc52904000a6d86d4a520800b0fd0bbb484100021f61776908200046f41eed21040008dd83dda42080051db0f31484100161fa17768c8200043ec2eed19040038be84dda320800117b09bb464100f2b3609630c8201dde240a64190400587e851cd61080010fb0a39ac21000e2fa1073584200045ec20e6b0840018ed821cd61080011bf06bb2a2100023720d76544200143e43acaa884000ce47258551080011bf06bb282100023720d76504200145e43ac8a084000ce47258541080051bb0f31e62100723be09764c4200146e43ac69884000cce631c9310800199ac6392621003739984724c42000672392c29884000c7b76dd520080018f6ec3aa40100032eddb74480200065dbb0e89004000d38751d120080051f100bb2a90800a2f21d645521002d1e42ac8aa4200093f87550548400787eecaa0a9080030f5d9541521016d9c402a82a420038be84dda528400117b09bb4a50800237a0f7694a100046ec1eed29420028fa80dda52840051db0f314a5080169ba166294a100147643ac4a94200587e85dda42840010fb0bbb4850800237a0f7690a100046ec1eed21420028fa80dda42840051db0f314850800a3b21d6250a1002c3f42eed194200087d85dda328400717d09bb465080022f613768ca100147d406ed19420028df8758e32840051f501bb2650800a3ea03760ca1001476c3cc41942000acd83988328400159f0c9906508002b3619320ca1006de240a641942000d38751d120840033e102b9a410800a3ea1e62482100043fc2ae7b22200587c855cf64440010ff0ab96c8880161f21572d91100061e3aee8b222000c5f75dcd64440018b8ebb9ac88800317dd473591100062e3a8e6b222000c9f741cd644400193c8039ac88800327100735911000637baee4b222000c6c75dc9644400199ee7b92c888003331cf725911000637ba8e4b222000c6c751c9644400195ee8392c88800333dcc725911000666398e4b222000cae401c9644400195880392c88800f0f99175191100045fc3ac83222000a3c85590644400187aeab20c888002a720d641911000556412c832220038be849da544400147b09b2ca8880168f21564951100054e41ac92a22000
  | 2 => 0x3714c92000727b2a641924000e4c654c83248001d1ec89906490003a3191320c9201ede240a64192400587e859cf61480010fb0b39ec29000e2fa1273d85200045ec24e7b0a40018ee829cf61480010fd0fb2ac2900021fa1c65585200061fb2ee8b0a4000c3c65dd1614800187eca3a2c2900030f19474585200045f43ec8b0a4000c3f75d916148001878ebb22c2900022fa1c64585200061fba8c8b0a4000c3c7519161480018becbb9ac2900031719773585200064fb26e6b0a4000c9c64dcd61480018beca39ac2900031719473585200064fb20e6b0a4000c9c641cd61480019a8c239ac2900061f21576d45200045fc22eda8a40038bc845db514800b8d8cb396a2900032b19272d452002e3632ae5a8a4000cac645cb514800b4d90ca96a29000e2fa1376545200045ec26eca8a400187e87d95514800b4d90ca92a2900031b1d952545200043fc2aeda0a400587c855db414800317908bb682900031b19672d052001e56324e5a0a4000c6c655cb4148007958c8b96829000eab21942d052002c3f42eeca0a400087d85dd9414800317d0fb22829000eab2194250520006563b284a0a400087f855db314800b0f90abb662900022fe1176cc52001c5e422ed98a400587e85dd931480010fb0bbb2629000e2fa13764c5200045ec26ec98a400d8ec821d931480018decbb9262900031b197724c52000657b26e498a4000cac64dc931480018deca39262900031b194724c52000657b20e498a4000cac641c93148001cc843b2a429000317d9773485200062e32ee690a4000c9f64dcd2148001938c9b9a429000317d9473485200062e328e690a4000c9f641cd2148001938c839a42900373518473485201eee2108e690a4000cd473d85214803d8f4a13b6a0900778e94364d412002e3632ce5a8240008bf845d9504800717908bb2a0900022fa1b74541200061fb2ee8a824030c3c65dd1504800117d0c3a2a0900030fd9474541201261e328e8a8240248be87d9150480611790fb22a0900c22fa1c645412001c5e438c8a824000c6f65dc950480018deca392a09000f2b19272d01200043fc2aeca02400587c855d940480010fd0dbaa80900bf0f19375501200043f430eaa02402ec3c641d5404805d0fd0fb2a80900be1f21f655012017c3f438caa02400587c87195404800187eebb2280900030f1d7645012000657b20e4a024000c6c659cb3048001958c939660900031b19572cc12000656322e59824000ccc635cb304800117f08bb2609000e2f211764c12000c7a40aec98240008be86dd1304800187ecbba260900022fa18744c1200061fb28e89824000c3c651d1304800117d0fb2260900022f21f644c1200061fbaec898240008be8719130480071790e32260900030fdd4644c1200061e3a8c8982401ec7a76d97204803dcd
  | 3 => 0x2b1a4000c7465dc5634800196ec9b8ac6900032d1937158d200061fbaee8b1a4000c3f751d16348001878ea3a2c6900032ddd37158d200065a3a6e2b1a4000cb7741c56348001968e838ac69000339dc87158d200046fc3ac631a4000ad48158c634800159b04188c6900022fe1176d4d2001c5e422eda9a40008be869d3534800187ecb3a6a6900170f19674d4d200045e432e9a9a4000c3f655d3534800b878caba6a6900022fe1f64d4d200045ec3ec9a9a40038bf87193534800117b0e326a6900171b19672d4d2001476432e5a9a40038be84dda534800117b09bb4a6900022fe117694d2001c5e422ed29a4000a5d83d965348001c3ec9a9ca690003871935394d2001c5f426eca9a40008bd84dd9534800117f08bb0a69000e2f2117614d2002e3632ce429a4000cac649c8534800b8d8cab90a6900032b1917214d200043fc2aeda1a400587c855db43480010fd0d3ae869000f0f19275d0d200043e432eba1a4003c3c645d743480010ff0fb2e86900021f61f65d0d2002c3fc38cba1a400087d87197434800187cebb2686900030f5d764d0d2001e56324e5a1a40028ec865cb434800b0fd0bbb486900021f6177690d200043fc2aed21a400587c855da434800b0fd0bbb286900021f6177650d200043fc2aeca1a400587c855d943480011ef02bb286900063d2057650d200043fc2aec21a400587c855d843480018d8cb390869000f2b1927210d200063632ae421a4003cac645c8434803b17d0d3a6a4900030fd9674d492002e1e32ce9a92401f8bc865d3524800187ecaba6a4900170f19574d49200ec5fc3ec9a9240008bd87d93524800717f0e326a4900022f61c64d49200f537436a52924000b2d84d4a5248001c5ec9a94a4900038b193529492001476432eb2924000c6e76d965248001c58cbb24a4900038b194649492000536432a9292401ec7870d95524803f970e0322a4900032e193705492002e363b6eaa92401ec6c76d95524800b8d8ec32aa4900772b1db64549200fe563b0c8a92401ed6b751c1524800b8d8cb390a49007a1fa1a75d092001e1e324eba12402087c865d74248007878c8bae849007a1fe1f65d09200043ec3ecba12400587f8719742480010fb0e32e84900030f9d764d09200061ebaec9a1240028ec865d2424800195cedb2484900038bd94649092000716328c92124000aac8655242480418f0e032a84900772e1c364509200063c32ee0a1240028ec865d5424803d8d8edb2a84900831b1d8655092001e563b6e8a12401dcac76d914248007958ec32284900038bd9464509200eed5ba0e0a124003cac649c842480018e8e3b2a64900031d1c4654c9200065a38ec89924000cb47119132480019a8e3b1a6490003351c4634c9200063bb2ee29924000c7465dc5324800196ec9b8a64900032d19
  | 4 => 0x44800147d0b38ec8900028f61671d91200ed5d400e3b224000ab9801c7644800117d0e28ec8900022f61c51d91200045f43863b2240008bd870c7644800147d0a18ec8900028f61431d91200055741063b224000aad820c7644803b5750018ec890002ae60031d91200045f43843b2240008bd87087644800147d0a10ec8900028f61421d91200054f41843b224000a9d83087644803b5750010ec8900028fa1770d91200051ec2ee1b224000a9e83dc3644800153b07b86c8900022fa1f10d91200045ec3e21b224000a3e85c43644800147b0b886c89000f0f192759912001e1e322eb3224000c3e75d92644800187aebb24c8900021fa1f65591200043f438cab224000c3f75dd16448001878ebba2c8900031e1d770591200045fc3ac83224000a3f8559064480014790ab20c8900030f9db65191200045ec3cca32240008bf87594644800187cec328c8900038b608651912000717b2ae43224000e2c655c8644800147d0b308c8900028f61661191200fd5d404a23224000ab980944644800717d0e288c8900022f61c511912001c5f4386232240008bd870c4644800147d0a188c8900028f614311912000557410623224000aad820c4644803f57500188c890002ae600311912001c5f4384232240008bd87084644800147d0a108c8900028f61421191200054f418423224000a9d83084644803f57500108c8900028fe1520191200051e42a4032240038be87c40644800117b0f880c8900028fa1710191200051ec2e20322400387c855db544800147b0bb26a8900171b19672d512000657b24e5aa240028ec865cb544800195ec8b96a89000e2f21176951200051ec26cb2a24000a3e86d52544800b4790daa4a8900030f9db549512001e1e3b6a92a24000c6f659ca5448007958c9394a89000a3b219729512000637b2ae52a240008fb805d954480070fd0fb2aa89000e8fa13655512002c5f43ec8aa24005a3e85d91544800127f0eaa0a8900028fa1954151200051e432a82a24000c3e765505448007878ecaa0a8900171b196721512001e56324e42a24000d2d549c854480051d90cb90a89000f2b191721512000566c1063b1a4000ad9800c7634800187ecb3a4c6900030f1967498d200061fb2ae931a4000c3c655d2634800187cebb24c6900030f5d76498d200061f3a8c931a4000c3d75192634800187ceb3a4c6900030f5d67498d200061f3aae931a4000c3d755d263480018dceab94c6900032b9d17298d200043f43ecab1a4000c7471d9563480010fd0e32ac6900031d1c46558d200061fb2ee8b1a4000c3c65dd1634800187eca3a2c6900030f1947458d200045f43ec8b1a4000c3f75d916348001878ebb22c6900032d1c76458d200045f438c8b1a4000c3f751916348001878ea322c6900032d1c46458d200063bb2ee
  | 5 => 0x930f99474543200061eb28e8a86401d8bf8759340c805d87cc83aa81900030f1d564503200143e43acaaa44003a3c8459554880051790eb22a9100168f21564552200049fc3aa82a44003c3f76550548800187aecaa0a910002976143198e200054ec206331c4000acd820c663880014bb0a18ac710002a76103158e2000566c1062b1c4002ada800c5638800717d09bb4a7100022f6137694e200146ec3cc729c4005a5e8598e538800199cc6b94a7100161fa177690e200043ec2eed21c40028dd8798e438800199cc6b9487100821fe1d65d4a2002e1f32ae9a944000c3d655d3528800787cc8bae851007e2fe1d64d0a200061ebaac9a144000cd47198d32880019a8e2b1a65100faf1205320ca2000c3e42aeda8c400187d85dd9518800317908bb683100062f613765062006e6b308e690c4000cd473585218800117f08b9eca9000e2f21173d95200051f420a3b2a4000a3d84147654800147d0930eca900028f61261d95200061fba4e9b2a4000c3d741d365480014bd063a6ca900029760c74d95200f536c10e9b2a4000a3f845cf654800147908b9eca90003175cc73d95200051fc22e5b2a4000a3c845cb654800147d0938eca900028f61271d95200f53d400e3b2a4000a79801c765480010fd0e20eca900021f61c41d95200043f43863b2a400087d870c7654800147d0818eca900028f61031d95200053741063b2a4000a6d820c7654803d4f50018eca900029e60031d95200043f43843b2a400087d87087654800147d0810eca900028f61021d95200052f41843b2a4000a5d83087654803d4f50010eca900028fa1370d95200051ec26e1b2a4000a5e83dc365480014bb07b86ca900021fa1f10d95200043ec3e21b2a4000a3e84c43654800147b09886ca900030fd96749952002e1e32ce932a4000c3f655d2654800b878caba4ca900030fdd774595200061fba8e8b2a4000cb874dc165480010ff0eb28ca900028fe1165195200051e422ca32a4000a3e84984654800147b09308ca900829ea0241195200053cc048232a400587e8710465480010fb0e208ca900161fa1c31195200043ec386232a4000a3e840c4654800147b08188ca900029ba08311952000536c106232a4020a7a800c465480014f300188ca900161fa1c21195200043ec384232a4000a3e84084654800147b08108ca9000297a0c21195200052ec184232a4020a7a80084654800b0fd0f880ca900021f61f10195200051f4262032a4000a3d84c4065480010ff0ab9ec8900161f21573d91200051f42883b224000a3d851076448001c5b0432ec8900028fa1661d91200051ec2cc3b224000c3f759d7644800187aea3aec890002a7a0c75d91200054ec18ebb22401daad821d7644800147f0ab9ec8900028f21573d91200051fc2ae5b224000a3c855cb6
  | 6 => 0x7e6b30ee690880008dd861cd21100018bcca39a422000317594734844006e6b308e690880008de8798d21100011b90f31a422000237a1d63484400046e43ac69088000ccf739892110001998e7312422000a3b21d624844000657ba2c49088000ccf735892110001998e6b1242200032ddd161484400066bb9ac29088000cd473585211000193ce939ecb90003275d273d97200062f284e7b2e4000c5c509cf65c800193ce8b9ecb90003275d173d972000666b9ce5b2e4000a3e84d9665c80014bd07b2ccb900030fd95749972002e1e32ae932e4000a3e84dd565c80014bd07baacb9000e2fa1373597200045ec26e6b2e400087f8759465c80018bceb39ec990003175d673d93200064f204e7b264000c9c409cf64c80018bceab9ec990003175d573d932000666b9ce5b264003c3c645d664c800147d0bb24c9900030f5d764993200054f41ec93264000a3e85dd164c800153d07ba2c9900161fa1773593200043ec2ee6b2640008bf8759064c80070f90abb6a99000e8fa1365d53200052f41ecbaa64000a3f8559354c80051db0d396a9900032b59272d532001c5e422ed2a64000a3f8459654c800b47d0bb24a990002a7a0f649532001476c34e52a640008de839d954c80011bb073b2a99000e1fa1f655532001d1f426caaa64000a5e83d9554c800b17d0fb22a9900168fa1764553200054f41ec8aa640008de839d854c80011bb073b0a9900021fe1d65153200045fc3ac82a6400093f8755054c800147f0caa0a9900028f61954153200061f3b2a82a64003c3c7655054c805b67100aa0a99000a3b61a721532002e3732ce42a64003cae649c854c8001a5aa9390a99000297a176398f200054f426c731e40008df8758c63c800193ce931ea79000297e1563d4f200064f3a2c7a9e4000ccd639cb53c80014bf06b2ca79000e2fa127614f200045ec24ec29e4005c6e659c853c800199cc7390a790003179d663d0f200062f3aac7a1e4000ccd639cb43c800b0fd0a3b487900021f6147690f2002c3f42cec21e400087d859d843c800795cc93908790002cb6135294b200063cb2ae12964000b2d8499652c80014df0caa4a59007ada2015494b2001476c36eb2164000b2d8599242c803b75100aa4859000a7a2017550b201fde240a64196400187e859db51c800717d093b6a3900022f61276d47200046f41ceda8e40008dd839db51c800b8dccb396a3900061f21d655472002c3f42ceda0e400087d859db41c800317d093b6839000237a0e76d07200046ec1ceda0e4003cae649cb41c80031790eb2283900161fa1676cc7200043ec2ced98e40038be849db31c800117b093b663900063761e63cc72000c6e43ac698e4001ad48158d31c800199cc639263900033358c724c7201fee2108e690e401e87f8759750c800b8dccb396a19
  | 7 => 0xe662dc532100019cac5b8a642000f0f1d1650c8400045ec36e8190802493e85dd0321000187acbba06420002b360a630c84000566c1cc41908000acf864c8321000159b0c990642000333dd9320c84000666bb2641908000e4e654c83210001c9aca9906420102f1205320c8401b76330a64190800587e851cd61100010fb0a39ac2200062f610735844000477410e6b0880008ed821cd611000b0fd0a392c2200021f614725844000c5ec20e4b0880008de831c961100011bb06392c22000ead211755844001d5b420eab088009ab5841d5611000756908b9ac220002b9e09735844000572412e6b088000a76851cd61100014eb0a39ac22000eada10735844004d5ac20e6b088000ae6821cd61100015cb0439ac22000abca00735844004d78c00e6b088003ab684d4d611000156b09a9ac22000eada1253584400055ac24a6b088000e575394d611000756908b92c220002b5e0d72584400056a41ae4b088000a76851c961100014eb0a392c22000eada10725844004d5ac20e4b088000ad6831c961100015ab06392c22000abca00725844004d78c00e4b088003ab684d49611000156b09a92c22000eada1252584400055ac24a4b088000e6752949611000756d09992c220002ad613325844001d5b42464b088000ab5848c961100011ef0e992c2200023d21d32584400076299064b08800287d855db511000717908bb6a2200930fd5176d444001e1e3a2cba88800287c85dd951100050f90eb2aa22000f0f1d165544400061eb2ee8a888000a3d86d51511000196ee8b0aa2200922f21d65504401261e3aacaa088024c3f8759541100018790eb2a822000f0fdc5655044001f1bb8acaa08801bc3f70595411003787ae0b2a822006f8dc4165504400df1a882caa088000c3d651cd41100019390eb1a822000fa5dc563504400df4b882c6a08801be951058d411000187aca39282200032b21d625044001f53b8ac4a08801bea7105894110037d4a20b12822000f0f1d165cc4400061eb2ee998880028dd8798f311000193ee8b1e62200023be09764c44000476412ec9888003c3c74595311000187acbba2622000a3721d634c4400064fba2c698880008ed86dc931100018dccbb9262200031b597724c4400066731ee49888000ccd63dc931100399ccc3b9262200023b618724c44000637328e49888000c6d651c9311000199cc639262200033358c724c44006e73308e498880008ee8798931100011d90f31262200023ba1d624c4400047643ac49888000cb77458531100019cee4b0a6220003391c9614c44001e1e3a2cb9088000c3d65dd321100051db0f31642200032bdd162c84400147a40eec90880008df835d921100011b906bb2422000f0f1d165484400061eb2ee890880008dd86dcd21100018bccbb9a42200031759773484400
  | 8 => 0x828cc4200023ba1c319884000476c38633108000a6e850c662100014db0a18cc42000eaba10319884000556c20633108002aea800c662100015d30018cc42000eaba1221588400053742842b108000a6d85085621000755d0810ac420002b3a0c215884000566c1842b108002aea8008562100018deeb3aac42000eaba12755884001d56422eab108002ae8805d5621000755d0939ac42000eab211735884000573c0ae6b108000ae4815cd621000199ae639ac42000eaba13535884000556c26a6b108003aae8494d621000155b0929ac42000393d4e535884001d56426e2b108003aae849c5621000155b0938ac42000eab211715884000567c1ae2b108000acc835c562100014dd0a38ac4200029b614715884001d57420e2b108000aad841c5621000159d0638ac420002b360c715884001575400e2b108000ae9801c5621000755d0928ac420002ab612515884001575404a2b108000ae980945621000755d0828ac420002ab610515884001d5742462b108000aad848c562100011dd0e18ac4200023b61c31588400053742862b108000a6d850c5621000755d0818ac420002ab61031588400157540062b108000ae9800c5621000b17b08bb6a42000f0f9d165d484002e1f32ae9a908000c3d655d3521000196cc2ba6a42000f279d263d48400064eba4c7a908003c9e7458f521000193ae8b1ea42000f2b9d262d484000656ba4c5a908000a6f8558b521000795ce8b16a4200032b5d162d484001e1f3a2cb2908000a6f82596521000187acaba4a4200028f61b549484001e4f3a2c72908000c9d7458e521000b4dd0b314a4200032b5d2629484002d37c36a52908000a6d86d4a52100018deeda94a4200031b5db52948400072731ea52908000e4d63d4a5210071cccc3a94a42000f0f1d165548400061eb2ee8a908000caf7458952100018f2cbb82a4200033a58b70548401261faa2ec2908003c3c74594521004917f0eb2c84200930f9d565908400061fc3acb2108024c3c87596421000787ce4b2c842000f8b9c965908400ee1fb82cb210801dc3d70596421003bc5e40b2c84200778b48165908400061eb2ce72108000c3d655c6421000195ac4b8c842000f0f9d165cc8400061eb2ae99908000c9d7498f321000795ce8b1664200032b5d162cc84001e1f3a2cb1908000c3d655d2321000793ce8b1c6420003275d1638c84000656ba4c519080018f481dd932100011ef02bb264200063d205764c8400063a38cca9908003c3c7459532100018e8e2b2a64200030f597744c8400066a38cc69908000c9f7458d321000159904b1a6420003351c5634c8400067238cc49908000caf74589321000159906b126420003391c5624c8400047ac36e29908000c7665dc532100018eacbb8a64200033598f714c8400066ab1ee29908000c
  | 9 => 0x7298c400056a40ae53188000ccd721ca631000159f04b8cc620002b32097198c400052f428e33188000a5d851c6631000753d0838cc620002a76107198c4000567410e33188000acd821c663100055b50038cc620002b66007198c4001d4f420a33188000a9d8414663100011bd0e10cc6200023761c2198c400052f428433188000a5d85086631000753d0810cc620002a76102198c400156d400433188000ad980086631000753d0918ac62000297a143158c400052ec2862b188003a9e840c5631000159d0418ac620002b36083158c400156d40062b188000c5f759d5631000753d093aac62000ea72117558c400156c402eab188003a9e849c9631000753908b92c620002b5e057258c400056a40ae4b188000ccd721c9631000753909b8ac62000ea7a127158c400054ec24e2b188003a9c845c5631000159f04b8ac620002b32097158c400052f428e2b188000a5d851c5631000753d0838ac620002a76107158c4000567410e2b188000acd821c563100055b50038ac620002b66007158c4001d4f424a2b188000a9d8494563100055b50128ac620002b66025158c4001d4f420a2b188000a9d84145631000753d0910ac620002a76122158c400046f43842b1880008dd8708563100014bd0a10ac620002976142158c4001d4f42042b188000a9d8408563100055b50010ac620002b66002158c4002c5ec22eda988003c3e74597531000b87ccaba6a6200030f59574d4c400065b30ae9a988003c9e7498f531000193ae931ea62000297e1563d4c4001e4f3a2c7a988000c9d7458f531000787ce8b2ca62000297e0d6594c400061eb2ae92988000a3d86d52531000b4bd0b31ca620003275d26394c4002d2fc36a72988000a5d86d4e53100018beeda9ca620003175db5394c4020f2b30ea72988003c3c74595531000187acbba2a62000327dd16354c400063cb2ee0a988000cd963dc1531004987ea8bb0a62000f0f1d16514c401245fc3acb2188024c3e75596431000187f0eb2c86200930f21d6590c4001e1f39acb2188003e1e73596431004b87ee0b2c86200970f5c16590c4012f0f982cb2188025e1d30596431000187acb39486200030f5957190c400064eb1ae321880008f7815ce62100031e902b9cc42000237e0d71988400046e41ae33108000a6e8508662100014db0a10cc420002b3a0c219884000566c18433108003aae84dd662100018deeb3acc42000eaba12759884001d57426e73108000ae7815ce62100015c902b9cc420003335cc739884001d57426a73108000aad84d4e6210001c9ea729cc420002b3e0d71988400056641ae33108000a6e851c662100014db0a38cc42000eaba10719884000556c20e33108000ace831c6621000159b0638cc42000abaa00719884000574c00e33108003aae84146621000155b
  | 10 => 0xb0a80008ed829cf615000b0fd0b396c2a00021f61672d854000c5f424e5b0a80008de839cb61500011bb07396c2a00c30fd9075585400043f43ecab0a800087e8719561500018becbb9ac2a00031719773585400062fb28e6b0a8000c5c651cd61500018decbb92c2a00031b197725854000637b28e4b0a8000c6c651c961500030f90abb6a2a00c22fe1176d454002e1e32ae9a8a8005c3c76553515000b0f90a3b2a2a00061fa1f655454002d1e432a8a8a8000c3c7655151500010ff0abb662a00161f21576cc54002c3f42eec98a800087d85dd931500011dd053b262a00023b60a764c54000637b2ee498a8000c6c65dc931500018deca39262a00031b194724c5400043fc2aed90a800587c855db215000b0fd0bbb242a00021f61776485400046f41cec90a80008dd839d921500018becbb9a42a00031719773485400062fb28e690a8000c5c651cd215000b878caba6a0a000a8f21954d414001e1e3b2a9a82802a8bf845d9505000187ecbba2a0a00c30f19774541400151e432a8a828003c3c76551505000567100aa2a0a00161fa1c31994400043ec38633288003a3e840c6651000147b0818cca200029ba08319944000536c10633288002a7a800c665100014f30018cca200161fa1c21994400043ec38433288003a3e84086651000147b0810cca2000297a0c21994400052ec18433288002a7a8008665100014f30010cca2000e8fa12515944001d1f420a2b288003a3e84dcd651000747d0939aca2000317dce735944001d1e422e6b288002a78805cd65100074790839aca2000e8fa13725944001d1f424e4b288000c6f729c9651000747908b92ca2000a9e201725944001d1e420e4b288003a3c84dc5651000747d0938aca200028f61271594400153d404e2b288000a79809c5651000747908b8aca2000e8fa1071594400051ec20e2b288003a3e848c5651000147b0918aca200021fa1c31594400043ec3862b288003a3e840c5651000147b0818aca200029ba08315944000536c1062b288002a7a800c565100014f30018aca2000e8fa1221594400051ec2442b28800087e8708565100010fb0e10aca2000e8fa1021594400051ec2042b288000a5e8308565100014bb0610aca2000a9ea0021594400053cc0042b288003c3e855db541000787b0abb6a8200930f14d76d50401261e292edaa08024c3f515db541005587ea0bb6a8200ab0f54176d504001d1fc3acbaa08003c3f87597541005587ee0b2ea8200ab0f5c165d50400061eb2ce7aa08000c3d659cb541000187acab8ea8200023de057298c4000c7a40ae531880008ef825c663100011d904b8cc62000297a143198c400052ec28633188000ace820c6631000159b0418cc62000ea7a137598c400062fbaceb3188003a9e849d6631000753d09b94c620002b5e05
  | 11 => 0x5000147b0938ecaa00021fa1c31d95400043ec3863b2a802fa3e840c7655000147b0818ecaa00029ba0831d954000536c1063b2a802ca7a800c765500014f30018ecaa00021fa1c21d95400043ec3843b2a802fa3e84087655000147b0810ecaa000297a0c21d95400052ec1843b2a802ca7a8008765500014f30010ecaa00021f61f10d954017d1f42621b2a8000a3d84c4365500010ff0eb28caa00b69ea0241195400053cc048232a800587e870c465500010fb0e188caa00ba8fa1031195400051ec206232a8000a6e820c465500014db04188caa00b69ea0031195400053cc006232a800587e8708465500010fb0e108caa00ba8fa1021195400051ec204232a8000a5e8308465500014bb06108caa00b69ea0021195400053cc004232a802da3f8450065500010fb0f880caa00ba8fa1310195400051ec262032a8003a3c84d975450055976c8b86a8a00b70fe16769514016e1f284ed2a2802dc3c509da545000187cedb2ca8a00b70f9d8659514001d1f426caaa2802cc7870d95545000b47d0db2aa8a00b30f1db655514016e1f3b0caaa2802cd3b751c1545000153b0818ec6a0002b360831d8d400056cc0063b1a8030c3f649d663500018decb394c6a00031b1967298d4000637b2ae531a8000c6c655ca635000199ec6b94c6a00021fa1f6558d400043f438cab1a80008df8758c63500011df04b88c6a00023b2097118d4000566c106231a80038bc849db535005f87ce9b2ea6a00030fd9574d4d4002e1e32ae9a9a8000a5d83d96535000b4790caa4a6a00030f9d95494d4002e1e32ae829a8005c3c76550535005b8f0e032a86a00031e1977050d4000556c2043b128000acd8308762500015d30010ec4a00c30fd9275989400062fb2ce73128000c5c659ce62500018becab9cc4a000317195739894000666b9ec5312800087e87d9562500010fd0e32ac4a00023be1d62189400046fc1ae231280008dc835c4625000159b06108c4a000e2f21276d494017e1f3a6cba928000c3f655d3525000b878caba6a4a00029b60b659494002d1e432a92928000c3e76552525000b878caba0a4a00170f1d9541494016e3c380caa128000c7865dc142500010ff0abb664a00161f21576cc9400043fc2aed192800587c855da325000b0fd0bbb264a00021f617764c94000c7b40cec99280008f5819d932500018e8e3b2a64a00031d1c4654c94000567416c69928000cd471d8d32500019a8e231a64a0002b3a0f624c9400067238ec49928000ce47118932500018eecbb8a64a00031d197714c9400043fc2aec192800587c855d8325005d87ce832864a00030f195740c940006673b2641928000ccc764c83250001c9eca99064a000393195320c940215e240a64192800587e859cf61500010fb0b39ec2a00062fa1273d854000477414e7
  | 12 => 0x83f331db634c92107ee238ec69924236ace8398d32484399c8e331a64908023ba1c634c92122e67b98c6992420dce47118d324841b998ec31a6490837711c4634c92100567438c69924200cce8718d324846d59f0231a64908dab3604634c92106e67388c6992420dccc7118d3248479d88e231a6490837311c4634c92100cf343ee2992420ece476dc53248401d88c7b8a6490836b3a19320c92106d6643264192420dbc4814c8324841d1eb0f31e4290836b5a0e63c852106f62c10c790a420dcd67218f214841bd8ce431e4290803b118e32c85210e4f3c3a6590a4201ae4864cb2148401d88c699642908f7335c863981210046f43ec6b024200c5f75d8d60484018b8ebb1ac09080327dd363581210064e3a6c6b0242008de8718d60484018beea31ac090803171d463581210064fba0c6b024200c9c7418d604847d99ee431ac0908023ee1d601812101e1fbaeecaa68005c3e7555263d00014bf06b2ca7a000f0f9d95494f401245fc32e829e8005c3e7555262d00014df04b2ca5a000f0f9d95494b401245fc32e829680008f7815d932d00031e902bb265a00161fa17760cb400043ec2eec19680028be84dd832d00897890299065a00170f1d554587401245fc32e9a8e800187c8759551d0007878ecaa2a3a00023be09764c74000476412ec98e80008df835d921d00011b906bb243a00aa2fe1974d434016c3fc3acbaa48030a3f87597549005b87f0eb2ea9200b60fe1d65d5240154ddc32e1aa48024cbb865c3549000187ecb390a9200030fd95711524000477416ed29c80008ed82dda539000b4bd0b31ca720016972156394e401861faa2ec29c8000a3f8558e439006117f0eb2887200c30f9d56510e400051fc2ac621c80008de83dda52900011bb07bb4a5200169ba166294a4002d3642ac52948030c3f545d8529000147f0ab1485200c22fe1d6510a401861f3aaca2148000a3f85588429000b0fd0bbb665200021f61776cca4002c3f42eed194800087d85dda32900010ff0abb265200161f215764ca400047bc0aec99480018f4815d932900010ff0abb065200161f215760ca401849f42ee81948043bc4814c832900030f90abb6a3200c30fd5176d464000c3ec2eeca8c80008df835d951900011b906bb2a3200023be09765464000476412eca8c80308bf87597419006187ceab2e83200028fe1563d06400051fc2ac5a0c8000a3f8558d419000147f0ab1283200021fe1576cc64002c3e42aed98c800087f855d9319000b0f90abb263200023be09764c64000476412ec98c800087f855db219000b0f90abb643200021fe15764864002c3e42aec90c80008df835d921900011b906bb243200028f61051d95401661e3a2e9b2a8000a3f845cf65500018bae639ecaa00028fe1172d954000636b90e5b2a802fa3e849c765
  | 13 => 0xc5f43ec8aa24205a3e85d9154484011bf06bb0a8908023720d76151210049fc3aa82a24200c3e765505448407878ecaa0a890802a7a1265d8d210054ec24cbb1a4200a5e8599363484014bb0b326c690803175d475d8d210054f420ebb1a4200a9d841d763484014bd0a3a6c6908029761474d8d210070faa4a9b1a4200e1d5415363484014bd0bb86c6908029761770d8d210054f426e1b1a4200a9d84dc363484011bf0eb18c69091ab3e096318d211e566c14e631a420087f855c0634840b0f90ab80c6908022fe117018d2101c5e422e031a42008dd87994634840153d09328c690802a76126518d2123d66c14ca31a42008df87594634849759f04b28c6908023761e6418d210052f42cc831a4200a5d85990634849559b05320c69080237e1d6418d2124d67c12c831a4200a9e84dd4634840153b09ba8c690836b360b7518d210062fbacea31a4200a9e849d4634840153b093a8c690836b36087518d210052f42ee831a4200a5d85dd0634841b59b05ba0c69080297a167418d210052ec2ce831a420dacd821d06348401c3ea92a0c690803875505418d2106d66c16e031a4200a5f855c063484014b90ab80c690802a7e117018d210054e422e031a4200a5e851c063484014bb0a380c690802a7a107018d210054ec20e031a420dacd821c063484015ab02380c6908029761763d4d210064f3a6c7a9a4200c9d74d8f534840193ce831ea690803275d063d4d2101c5f420ed29a42008bd841da534840b1bb0e31ca69081697a146394d210066631ce529a42018ec865ca5348401998c6b94a690806792057294d2102c6f43ec6a9a42008dd8718c5348401998c7390a6908063b2197214d210066631ae429a4200c5e75d8f43484018baebb1e8690803179d463d0d210062eba8c7a1a420587e851da43484010fb0a3b4869080e3761c6390d210066631ce521a42018ec865ca4348401998c6b94869080237e0d7650d2100477c12eca1a42008f7815d943484071bd0fb1a86908023761c6310d210066631ce421a42018ec865c84348401998c6b9086908030fd9574d492102e1e32ae9a924200c9e74d8f524840193ae9b1ea490803279d063d49210064eba0c7a92420dcd67118f52484019a8c6b8ea490923b1084639492100727b1ea52924200e4c63d4a524841b9a8e231aa49091fb108463549210066a31ee2a924203c3c645d7424840187aebb268490803179d763d09210062ebaec7a124200c5e7518f42484018baea31e8490837359c463d09210066a31ae3a12420dcd47118d42484019a8c7b8a8490837359c463cc92123762108c79924200cd4635c7324841b99cec31c6490837339c4638c92106e66388c7192420fcd471d8d324841b9a8e231a64908033518f714c9211b567436e6992420fccc76dcd324841fb88e3b9a6490
  | 14 => 0xc835da52504011bd063b4a4a08023760c769494100c5e432e9292820393f87552525040187cecaa4a4a0802cbe09549494102c76c38c52928205a6e8518a5250401c5aa8314a4a08163ba1f625494100c5e432e82928205c3c76550525040787ec2bae84a080f4dd8575d09410069b882eba128200c3d7518b42504031790cbaa84a086e6e201755094102c3f428ed992820087d851db32504031790cba664a08161fa14768c9410043ec28ed19282018bc865d232504031790cba264a08062f219740c9410064eba0c61928200acd8218c325040195ae831064a0802b360c620c94100567432641928200acc864c8325041b7890299064a086e2f61e54d814102e1f3aca9b0282248bf8755360504011f70eb00c0a08031e94170d97210061fb2ae932e4205c3c655d265c84010ff0eb28cb9080f0f19175993210061ebaec932642008bf8759064c84070f90abb6a99080e2f21176953210047dc02ecaa642028f8805d954c84070fd0fb2aa99080e8fa13655532102c5f43ec8aa64205a3e85d9154c840127f0eaa0a9908030f9d9541532101e1e3b2a82a6424cace82d8e63c84011bf0eb18c7908022fe117018f2101c5e422e031e42018ed869ca53c84031db0d390a79080e3de1971d0f2102c3f428ed21e420087d851da43c84031db0d39487908063b61a7210f210061fb2ae9a964205c3c655d352c84018eacab8ca5908021fe1d6514b2101e1e322eba164200c3d75d9342c840117f0eb208590873391c7764cb2107ee238ee699642019ce87d8d32c840178b03b1a659083f711c7634cb210e67238cc699642008ee8718d32c841b9c8e231a659080273a1c634cb2123667bb0c6996420ddc47118d32c840159d0e31a659080333a1c634cb2100762c08c6996420dcce7118d32c841b998e231a65908f3b11c4634cb2106e62388c699642019e687dc532c84019ceedb8a6590803b118f714cb2123567c3264196420dbc4814c832c8401b8a64b88659083f719ce72cc7210e47bc32e598e421cae7865cb31c841d3cb0f196639083af160e32cc72107ee339c6598e420f9e7874cb31c84395cf0c9966390872f1e1932cc72100763c326598e421cac7864cb31c840187eebba2c1908030f1d774583210061fba8e8b064200c3c751d160c84011f70eb00c1908030fd95749952102e1e32ae932a4238c6f75dc96548401998e7b92ca90803351cf71595210043fc3aca32a4203c3c645d6644840187aebb24c890803331cf72591210066a39ee2b2242008bf8759064484070f90abb6a89080237e0d76d51210046e41aedaa242038bc845da54484011bf06bb4a8908023720d76951210046f41eecaa242008dd83dd954484011bf06bb2a8908023720d76551210047dc02ecaa242028f8805d954484070fd0fb2aa89080e8fa13655512102
  | 15 => 0x838a64190dbf0a00714c8321b7e0c00e29906400dc471dc1320c80159b0d38264190daf1a06704c832005e2c0ce09906400dc4719c1320c80159f0cb826419002e3e11704c832005c6422e09906400bc7815c1320c86d78902b826419003711c5704c832006e2388e099064009cf874cb610c81b78902996c2190367321d325843206de240a64b08640d8ee878c9610c81b5cd03192c2190dfb10c6325843206c7643a64b08640dae4814c9610c80199f0e992c219036b321d32584321b66643a64b08640d8cc874c9610c801d8f02992c219036b3a05325843206d6640a64b086436ec4814c9610c81b58902992c2190dbb1c413258432004e7c3a65b006400bc4814cb600c80178902994c01900363dd13258032006c63a264b006400bc4814c9600c80187eebba2c0190030fdd474580320061e3a8e8b0064009cf874c8600c801b1ce8990c019003635d13218032005e240a643006436dc6714c8600c801b8a64b88c01900b3c98171180320047dc3ac03006400cf171580600c80747d0bbb2a9a080f0fdd776553410045fc3aa931e8205c3e7555263d040793ce931ea7a080297e1563d4f4101e4f3a2c7a9e82018be84dda53d040787ce8b2ca7a080297e0d6594f4101e1f3b2a929e8200b1f8355253d040317d09bb2a7a080f279d26314f410070eaa4c629e82219b8805d543d040117f0eaa4c5a08170f9d55498b4101e573a4c5a968200a6f8558b52d040795ce8b16a5a08062fa137694b4101e1f3a2cb2968200a6f8259652d040787cecaa4a5a0802cbe095494b4100c5f426eca968203cae7498852d0401c5aa9310a5a08866e2017550b4100c5f426ed9968203cae7458b32d040317d09bb465a080f279d1638cb4100c5f426ec99682019b4815d132d040b0fd0bbb065a08021f617760cb4100c5f426ec1968200acd8298c32d040159b0731065a0802b3e19320cb4100566c3264196820dbc4814c832d045f878e9baac1a08c30fdd075583411761e3a0eab0682218bc8755160d040b878eaaa2c1a08eb0fdd774595410043fc3aca32a8205a3e86d9554504011bf0eb18c6a0802b32096318d410045ec3ca831a8205c3e7595063504010ff0ab80c6a08161f2157018d4100c5e432e9a9a82008ef825da53504011d904bb4a6a08023ba087694d4100476c10ed29a82018bc865d2535040727f0eaa4a6a08030f9d95494d410058fc1aa929a82058dd8718e535040b4bd0a31ca6a0803875506394d4102c6f43ec6a9a82018bc865d0535040b878ecaa0a6a080f0fd8575d0d4101e9bb0aeba1a8200d37105d7435040187aea31e86a08062f2197550d410dcdc402eaa1a82008ef87588625040159906b10c4a08022f61e541894102e1f3aca8312820087f855c0625040b0f90ab80c4a08062f21974d49410046fc1aed29282008d
  | 16 => 0x354932004b7c3aa42926400c74619d7424c807878c8bae84990031d18575d09320061ebaec9a126400cd4619cf424c8031e902bb2849900335184735093207c6e432e3192640fcd4615c6324c80117f08b86c29900e2f21170d85320053b42cc9b0a6400a7585993614c8014ed0b3a6c2990029d61674d85320071baa4a9b0a6400e3554153614c80156d09a96c299002ad61352d853200733a94a5b0a6400a7685d0b614c8014eb0ba16c299002ade1170d85320055a422e1b0a64008f587990614c8014ed0b320c2990029d61664185320056ac1cc830a6400ae582990614c8011ef0eb20c299002b5e0d641853200573c12c830a64008f687d85604c80196ee9b0ac0990032d1d361581320047b438c2b026400cb774185604c801968e830ac0990023ee1d60181320062ebace7b206400c6d759cb640c807878c8bacc8190028fa1764990320061ebaec93206400a3e85dd1640c80117f0eb20c81900e2f21176950320051fc22cb2a06405a3e85d92540c8011f700bb2a81900a3e201765503202c5f43ec8aa06405a3e85d91540c80117f0eb20a8190024fe1d54150320051fc32a82a06400a3d86550540c80187cecaa0a81900f0f1d954150320062eb2ce72906405c5e659cc520c80193ac939c84190161fa1676108320043ec2cec21064008ed8798e320c8399c8e331a6419002e3a13534c832005c6c26a69906457dc471d4d320c80199eed29a641915b711c6534c83200667bb2a69906455dc47154d320c8a9b88e229a6419002d3a17434c832005a6c2e869906453dc471d0d320c8a5b88e321a6419147711c5434c832286e238886990640d9e687dc5320c8019ceedb8a641900339dd8714c83222ee3b98e29906400ccd86dd9320c80199ecbbb2641900333597764c83206ce740eec990640d9cc81dd9320c80199d0fbb2641900333dd7764c83200666baeec9906400acd81dd9320c80159b0d3a26419002d3a16744c832005a6c2ce89906436bc6819d1320c80178b033a26419002b3e19744c832005e3c0ae89906436bc4815d1320c80139d0fb226419002d3a17644c832005a6c2ec89906400dc471d91320c80169d0b3226419002d3616644c832006e238cc89906400dc471591320c80139d0e3226419003a3590644c832006e2388c89906400ace86951320c80159b0d2a26419003c3d52544c83227ee238ca8990644edc471551320c801e1aa82a26419137711c4544c83206ce743ee29906436bc687dc5320c81b38d0fb8a6419003b1e1b714c832006e3bb6e29906400ec776dc5320c80159f0cb8a64190db711c5714c832005e3438e2990643cdc6871c5320c86dd8b0c38a641900371dd8714c83200763bb0e29906436f86841c5320c86df0b0838a641900371dd0714c832006e33a0e29906400dc5741c5320c801b88e
  | 17 => 0xc841d8be87951609080b878eb2a2c1210922f21d54582420047dc3ac03048400c7a505c365508018f6ea382caa10032edd070595420043fc3aca32a8400a788059465508018decbb92a8a1002a761031d8d4200566c1063b1a84008df8758c63508015a902b18c6a1002b36083118d420043fc2ae031a840587c855c0635080187ecaba6a4a10170f19574d494200537c12cb292841ea7880596525080187ecbba2a4a10021fe1d65149421053c402ca292841dab88059642508010ff0ab86c2a10161f21570d854200c5e422e1b0a8400cd4611cd61508018f6a0baec0a10023ee1d60181420053c42ac03028403c3f75dd9541080b87ceaaa4c62100f279d263d4c420052fc2ac7a988403c9e7458f53108014bf06b2ca62100f0f9d95494c4202e3732ce42988400d2d549c8531080199cc7390a6210170f9d5549884201e1f3a2cb290840393f87552521080165f04aa4a421002cb613529484201e1e3b2a829084008bf865d5421083f37100baa84210032bdda525084200657bb2a4a108405c3c75551611080317b09b82c2210bf0f1d375580421861fba0eab00842ec3c741d5601083f1790eaa2c0210170f1d5545804200666b9ce5b2c640087f87594658c80b87ccaba0cb190030f595741963200666b9ce5b246403c3e645d4648c80117f0eb20c9190030f5d5641923201c3f42cedaa464058ed869cb548c80b8dccb396a91900e2fa12769523201c76c34e52a464028fa809d9548c8011f3013b2a91900e1f21d655523201d1e422caaa464058bc87591548c80b4790ab22a9190024fe1d541523201e1fbb2a82a46400c3d76550548c80b4bd06b2ea7190170f99574d4e320061eb2ae9a9c6405c6e659cb538c80787cc8bae87190030f5d564d0e320062eb2ae72946400acd86cca528c80159b0d992a519017179957314a32004b7c3aa42946403c9e645cc428c81f1bd0f992c31903eb5a07325863202c3f42ee0b0c640087d85dc1618c80717d09b82c3190022f61370586320047dc3ac03046403c3c645d6644c80187aebb24c89900335dcc715913200673b90e2b2264008bf87590644c80717908bb4a8990023de05769513200c7a40aed2a2643ae3461d52544c8019a8c339ca89900e372197395132004e6412e72a26400cd4615ce544c8019c8c3394a89900e3b2197295132004e641ae52a26400ce4615ca544c8031ed03bb2a8990023d60776551320047bc0aecaa264018f4815d9544c8011f700bb2a89900a3e201765513202c5f43ec8aa26405a3e85d91544c8011ef02bb0a8990063d20576151320049fc3aa82a26400c3e76550544c807878ecaa0a8990e78d18554151320065a30ce9a926400c3f655d3524c80b878caba6a4990032d18574d49320066a30ce7a926438e6461d4a524c8018becbb9aa499003351847
  | 18 => 0x48014bb0b18ec6a90029761431d8d5200566c1063b1aa4008df8758c63548015a902b18c6a9002b36083118d520045fc22e031aa4038bc845c0635480117f08b86c2a900e2f21170d85520066a308e6b0aa4008fb87580605480157108b00c0a90170fdd3765505201e1f3a2a9318a405c5e7598f431480b8bceab1e86290170f9d95490c5201e57324e4218a400d2d549c8431480199cc7390862900f0f9d1549885202e37c16eca90a405c6c82dd95214807878e8aa2c2290c30f1d7745805217e1fba8e8b00a424c3c751d160148410f90eaa2c02900f0f1d1545805202c3f4386332e840087d870c665d080747d0818ccba10028f6103199742005374106332e8400a6d820c665d08014f50018ccba10029e600319974202c3f4384332e8403a3e8408665d080147b0810ccba100297a0c21997420052ec184332e8400a7a8008665d08014f30010ccba10161fa1f10997420043ec3e2132e8403a3e84c4265d080147b09884cba10031794f735974201d1f424a2b2e8403a3e8414565d080747d09b9acba100e8fa1273597420062fb9ce6b2e8400a7b805c965d08014f100b92cba100e8fa1271597420051ec24e2b2e8400a7a809c565d08014f30138acba100e8fa1071597420051ec20e2b2e8403a3e848c565d080147b0918acba10021fa1c31597420043ec3862b2e8403a3e840c565d080147b0818acba10029ba08315974200536c1062b2e8400a7a800c565d08014f30018acba100e8fa1221597420051ec2442b2e840087d8708565d080747d0810acba10028f61021597420052f41842b2e8400a5d8308565d08014f50010acba10029e600215974201d1e422e0b2e8403a3e841c165d08014bd06382cba10029760c705974200536c10e0b2e8400a76811c165d08014eb02382cba10021fa1f10597420043ec3e20b2e8403a3e84c4165d080147b09882cba100e8fa1010597420051ec2020b2e8400acd820c663d08015b30018cc7a10021fe157098f4202c3e42ae131e8403a9e840c563d080159b0418ac7a1002b66003158f4202e1f32ae9a9e8400c3d655d353d080787ce8b2ea5a10170f99574d4b420061eb2ae9a968400b2d84d4a52d0807878e8b2aa5a10030f5977454b4202c3f428e6b0e840087d851cd61d080b0fd0bb82c3a10021f61770587420043fc3aca32c8405c5e655cc65908018bacab98cb210171b99672d52420043fc2ae131c840587c855c263908011bf0eb18c721003175d56318e4202e1f32ae9a9c8400c3d655d3539080187aecaa4a7210034b5527294e420061eb2ae9294840393f87552529080b47f0caa4a52100f0f5d95494a4200597c12a92948405c3e655d0529080b47f0caa0a52100f4b98975d0a4202c3f428e6b0c840087d851cd619080147b0ba12c3210161fa1770586420043ec2ee0b
  | 19 => 0x30f21d545805416c1e43aa8b00a800e3b80551601505b47d00aa2c02a0b68f20154580540071c402a8b00a82da38805516015007c76e0aa2c02a0030f55072580540061eaa6e2b00a8038be870c664d480117b0e18cc9a90168fa1431993520051ec2863326a400aae820c664d480155b0418cc9a9002aea0031993520055cc0063326a4038be8708664d480b47d0a10cc9a90028f61421993520054f41843326a400a9d8308664d48015750010cc9a9002ae600219935201c5f43e21326a4008bd87c4264d480b47d0b884c9a90028f617109935202d1f42c82b26a405a3e8510564d480b47d0bb9ac9a90168fa1673593520055dc02e4b26a400ab8805c964d480b47d0b38ac9a90028f61671593520055d404e2b26a400ab9809c564d480b47d0a38ac9a90028f614715935202d1f42c62b26a400a3d858c564d480117d0e18ac9a90022f61c315935202d1f42862b26a400a3d850c564d480155d0418ac9a9002ab60831593520055d40062b26a400ab9800c564d480b47d0b10ac9a90028f61621593520045ec3842b26a405a3e8508564d480147b0a10ac9a9002a7a0c21593520054ec1842b26a400aba8008564d48015730010ac9a90168f215705935202d1f428e0b26a400a9e831c164d480153b06382c9a9002ab60870593520055b408e0b26a400ab5811c164d480117d0f882c9a90022f61f105935202d1f42e20b26a400a3d85c4164d480b47d0a082c9a90028f614105935202d2f4286331ea400acd820c663d48015b30018cc7a90022fe117098f5201c5e422e131ea405a5e850c563d480159b0418ac7a9002b66003158f5202e1f3aac9a1ea400c3d7559343d480717d0839ac3a90022f610735875201c5f426e0b0ea4008bd84dc161d480117f0eb20c92900f2799173192520064eb22e6324a40096d86dc954948018db0db92a9290022fe117098e5201c5e422e131ca4008df8758c639480193ae8b18c72900f0f99175d0e52004b7c12eba1ca400c3d75593439480187aecaa487290165ba167290e5200696aa4e521ca400d2f825d3529480ba5cc4ba6a5290025b61f64d4a52004b6c38c9a94a400b4e83193529480169b06326a5290025b61f63d4a5200636bb6c7a94a400c6d7658f52948012db0e31ea529002cba1063d4a5200596c20c7a94a400e4d6318f529480165f08986a529002cb21130d4a52004b6c3ea5b0ca4038be841cd619480117b0839ac3290028f613525865202e36396a4b0ca4038be84dc1619480117b09b82c3290025b61f52d8252006973a6a5b04a400d2d74d4b6094801a9ce7a96c129003535cf52d82520f43f43ea8b04a403c3c74d51609483d4f501aa2c1290ba1f21d54582520053d43ca0b04a41ec7a8794160948012db0fa90c1290023ee1d60182520045fc3ac8322a400ab880590645
  | 20 => 0x700a80b00500780200080280380300380280180180000601000000000181700000100000100080000200200104480082580080000403d80000080280000900084e80000280100000000000200100100680c00080200100680080180980180300080480000080200280180380300200180000b80080181000000200300a00000200080f80000181780280100200680a00000000500000080080b80000080c00800301f80680700b00080080180580380100101a01981180000b80580180280301f80300c80400400080080300000080d00d80300000000180a80880200780000000780900000180080200180000100300300000000100000180800000200280400300e00400000f80600680080000000400200000481b00280000283a80080180200200100080100800400d00381d00001c80680100101000581980780b00101c80880100680601180581100700680000400200080380000d81a80000000000680080501000a80000002280180000100600080280101f0023be097198e5400476412e331ca800acd820c663950015b30018cc72a002976143158e5401d4f42062b1ca800acd820c563950015b30018ac72a00237e0d7198a540046e41ae3314a800acd8308662950015d30010cc52a0029b6142158a5401d5742042b14a800acd8308562950015d30010ac52a0023ba08735865400476c10e6b0ca8008de831c961950011bb06392c32a0023be1d62189540047dc3ac0302a803c3e87dd9541500147d05bb2a82a0028f60776550540061f38eecaa0a800c3c71dd9541500147b01bb2a82a0030fe0b76550540061f416ecaa0a800c3d82dd9541500187905bb2a82a0030fe0776550540061f40eecaa0a800c3d81dd9541500187903bb2a82a0030f88776550540061e10eecaa0a800c3f80dd9541500187d01bb2a82a0030f60376550540061e406ecaa0a800c3f10dd9541500187821bb2a82a0030fddb72550540051ec34e4aa0a800c3f769c9541500147f0cb92a82a0030fdd972550540059dc02e4aa0a800b38805c9541500187eec392a82a0030fddb71550540051fc32e2aa0a800c3f765c5541505b27d0fb82a82a0030fddb70550540051ec34e0aa0a800c3f769c1541505b27f0eb82a82a0028fe1970550540061fbb2e0aa0a800c3f761c1541500165d04382a82a002cb60870550541cd9b408e0aa0a800b35811c1541505ba74e0382a82a0030fe1d54988540061e43aa9310a800e2f825526215001c5904aa4c42a00f8b9c954988540051e402a9310a800c3d549ce621500187aa8b8cc42a0030f55170988540061fc3aa8b08a839c3c875516115001c6f02aa2c22a0e78d205545845401f1bb8aa8b08a800a3c805516115073c6e20aa2c22a0030f55072584540061eaa6e0b08a800c3f87551601505b4790eaa2c02a0
  | 21 => 0x200080080200000800100302881280200180200280000000401180480180280280000700600180001480f80000100280600000700400380001201480280e80280000200300400180700f00000502c80780300380000080380000500500180300000680000200600501a81100700080000000180380300100100302080000b80381080400800700000000080280380400780180200500100500800000080000500382400b80380080280000000500000e00000001b03580000880580180e00000000400c02200c00300680480580000a80200400081380300000000180200a80080300000000080880f00080a00080d00302100180000700001900100000000000400400080500180680500000580000400180480c80780300000000000182180700000081180200181d80780080e80080500100882200100300203400080080280080200380180000380001680100000500200080880000b00600b80000780380000780200400000580080900c80480100b80a80080880000300100084280000481080000280080102881380080200080e00000080080380180080b00200082600000f80080b00000000900080080780a00080280000200000100000080e00002e00080c80080001480000100081b01100480080180000000680300280000000000100080000c80100000100080000b80180080000080380000100200380000400100080e01200280081b00100300000a01600101680080080001a00000300100080000002f00200000e00200100f00380180101100081700500000c80000080300500380000400400000a80000280300300800000100400b80000e00000380200a80000280080080480100580400400e00880180001280180300080000580300b00580000000480181200480580380000000080100200080080180201101100300500280200f80803a01780281e00400080000180380202c80680380080081580500000a00d00500101700002880100580080000100080100000000280000782300200d00280480000580303600000700080000000000100001980003481900b80000500000180380200000000100200380080580880080100582380280000080383b80080900381d80000000000000501680480b80000280b80180200481f80800a80980181a00200500000001300000100100500483f00400100000100580000000000600101400080400480b00000200000e81e80400200200180301280200000200500000180100180080000280180380100800182a00600e00000100300380180580281100c80500480000201180000a00080180a00000000100000100501e00080380a80000080480081182881280500000080780600000000080280101780d80181a80300080380200601180100b80380180001f8018120058050
  | 22 => 0x10464e4e12f8a74a2f85211678d3ceaa65500099b064084b1fd27d86fd9f74be1714936056511187c0d4b1d0cd06411de40a54b23dc9009d02a725b95d00c624c8f40420000543ab7007400033800001ec46e421c08c5b806d575da88a2c0000b601dce10a9432394746529e10aa22b923a25913003a100ca4120246f465cb2f3af1e9d22ea0c54b87e0fc0b008490fc93b86523c417c0cf08ad4560d16cdc1ec3309d0485c0bc4ff16fd5080a244052c92b67bc4a9906847057e8ce0e38109687b0714a906c9ff1439cac6288d03c49d149c011c0002b9c7f61f908000000000002fbab18326000000000016658730d800136687b000248d4a01db0001f4af36b198000ea41fa00042e00014387ef0000ba8b0c77c4d805304ae0fe32d8000000851437809402c00e54995bc01e440000007885202121e8000556a3b1e91f98000444199a964a323a73cf9a18d86890158aca4da681b820a88c0d82f6aa3097537248709700200000544338000b38a3e2f99edd25c0004e9078427c0001551bcd04a00042917f42225f22f38000df64fd2d728647986c100003b800018200018910423da0000342de800044480000001fe05b406824a1245671abd2523b03d49883160b12bb60ad14244df294805cc6a5cc27cac607ac220800109c22600057d2c6482082923180014340f13948d401f4a240000d640007052e79e740007ff2bb133ca2a013490a9552940ca0001d585489c0578027c2a6837187241d22b5224b8a4fd5be84924580000005d942a8ad400080e070a3cce6447900000002bd541087252c0003484a400002b4000000000093400000026d0c6c0002828a1869c8b1a2d8bd0f7127949c26ad5123214ce16c436c38a0000624ff40000b921582e29a95801b2529897f0d580004b50000228648cb0abb49120c400069d0000000000000000282d12a914b4610b082c6cf1fc04ace54a664088e8452a00025600014089b116380013b20002be00015f23d741720f00006ac41d00d534f0a40001c9140a8f44349fec21a1ff1950958e6e6bb48c83008e25d1000107c12c86219786fd230ad81ff9d2416e79c0000d805c27dd3658cdcbae7462bc0a3c00011d1e69c08aa695c04e081521408f2538db50fe00055c99e80000003e80b680001fd00000010c86d744d212924c086ca72adc10c0a613f8890f5622326093d8c71a7b00300580000000200100480100002000000200f80600300080880000381f80000602400980000600580100c00000000000280180000680f80282d00000d00000080400001680c00100080880380500400000200001780000281180700a80880300000780380000080000800100900000900200180000180300000080900600e80000280181801c01900000380300181480200000600a00000301a80180180c00000
  | 23 => 0x1fc7340001b400001e901e9840dec5c49fc0001480b7c91b557261423400013780003720001bd25ecbd601c3670000000af700000000000001370000000000174190493807d8ecc1700503b2471db2800031b02b90440de569353074881a8a24a3d1514bc39d2a1a220672521bee59b4d0e98e13b19c890604323aa6a1624046800151d37022180007dc7b01be00017b40003bf11993487d6972396118838400048744293a82810002a2015a2ec0002781130784510a07400031800003706066b800011084e46ba3eb8000f7e90c38f80011660004e590146a41b005662c20006e720a266a1d40a926298f0fb469600025a93440003259aa55620b543a800083000031f8000000acd00000b80000005919eec0007c829200003d41eb56d86a400000028118592f700055e9a904d24781aa09f00000004ad00013020004e215b0d4229b31b957443227322ea5c15b448f1ae90d91d858303300652085c945200000007203d50e956050000d9a28c00059a0002aa433a7f009d814ab4846c1dc000000009500029cc000215269833c0000004f90bd923e0003399a791cc32b00000010f42bd0000000710000000000021f7edb5aa3a40009178001e3d5060000da00000003ec1619bb02738010001ea0120b100508228c3084543b19113d88e14789eb935c1058132aa127c13d593800151e47b0000f848fe4aa3b0868083800000017d800077e1c605c143c4a558429a148887413e94985cea350116b40a500003189350c2081a1c199d06fc0003ed804802846645a800000001050129380226e90c1a3df2ed0d3246196925a6ab2bd91940001980f1a69800001d00027e106d9f30000dd0a4a0005509cd800000045a017c3223db0000f2c8e427558e0000000b0c8001e78c180000000eb8c7600000000000000004ba92f0000575000231cd833474efa90800071c3411bf44f0116c4ea134962349038ac1099a000377051af0c118485a8000000000d4181471a78d5370ad88aa110d8babc36128b1255800119272f4c99794d2e540000065800006b10c1b652fc8133928000dd015b5878000000000546ac0809400011d000000001fccf000000030b26d000000074a044a104552a1836e400038e00000000000000003f08000e8d50900017d0f7a80c00016654d80002d6063d44a4d700000001cc7de0841e0018442d2b800008d2000049abcd65816456c823866446443bcfb4a38490000037c0000d94b600000003af00004240360004fea68c01460b457895440e0fed828d891ca85e2cf93600007eb456e4f497000000018ad38a00000000003ca4a63c082bc012920c21287c000136c7d8000e427fd448a4c8cf20003489f7c000a4323398c0f83ae522247ecdbe000481ecb93064b70d291f0000000000048800000014127e451404cc40d
  | 24 => 0x879907635800026206c800008cd0ec000aa64389f8c31400006d1d9cb189164e7abfc00008d9150c925ca0063108280d1c00037d0e040003ac3b88000e120004d508480000004cd8b5493e9eb4ce679823966019cddf4ba60002fda63c00000052b00001e18b20000000b040002c2993060012c49d00000009a526327a80001cbb7a8000ce29794199e94d4a08b2f9c00054220d1670b1400005532800000ff5e406904022a2a150001b48574a0e18b00015e823621c80067902fe0001ff8e0c4263a3d23466f00014f86b12fa07807d95a0f7c2343cbd2503a078318e01e85129e744d8c1457090e18800310ba0002fc52d84d05ca249a1f431800055a16dcaff02f25d8000d32a4011e00c80001c60f6a8f448413340e0fa80007f82b9000029e1595350c3c000a5d4849c613a13060001cc000040b07996f42272fd54a8ead10911f56928bd308aca00000000006ef3599ecc000af1435200c15048619a9e487c893419604186782ec8000000000000000000126a2c200000000dc36e01e800e0008b29b514694ea00016f15c454400027b994c39c0002cb88043a69c91df16d8b9a0f88819e4118caf810f000000000041623ae0000005648bbcdaa26d0000000dcc3d41eaa44b10a5a83eb000067000056797180006d80001f080000c755d0000000000000000084a4213100ab000082a545948c00000000013751ebb11aed0a8c4cd4333d6e1f9588a482ad000085000049b234c63e000000000026f00018ca18517ab2d00018f837d4f83b707cd6286154068e6078c35b2bc85fcb603b90b9800000051e1a580000003c93a91e689cc00000000007c4afe0002c8118034a33780012de8bf48800000008fe1382634ba4ab2506a450de09ce1ee0000dac6b04ba17501824561b196590729584de112136e000488d3889ca7ea48a8b741540db0fd01d5266000480955418b7b7bca976d474b13800143d2d28db0001870b1a9900001fd00007070d0a6002b004400019a14f08df156865c00047300000009bc00000000002940000c3047830200021529d00003702049af438173b39a11147ea3ba0b38f14eba0020000b590121b129717745720d44ce83b160216d1641c487dc6264e4230ca6a030196a540e2092cbb9980812200020798d010a3312b21a0c1182a5256841c0684fa413147cbd2aa7393acc01df3fd391051860207448f1e590b28cc4c4a8f345c64332b0c1b64861a589922557c1d72be8994216b0e2301e4d280222a92486848611b013c5988fb1ef4cc92e87056752271ee4b447c514f26600003a611da2f15140003a9800162c48a106240800008980025140001452ec15647ec5ad2038000e700004458f8c550115099213092e27126c86651f88cf13080003901620bda09114e3f94fa8858b841e958f00000000001c818a40ca
  | 25 => 0xe0003f49b88b9070d41c22dc0001f1090a69d656000444500c00091f9110c30acc341250274c0000002bb80003783b1000200808434011815703b000004d166cfb23b380020f910200017d80000000000000de524e5980000000a185ee5579a480009bb06c0b5c0006e1519214c9446dd09791ad42807b41a9e094c8226ac061acd4e8ea56a9c78d6e7984000b40ec67851ca858103081007296e81649cd0619874b4622547125dc71f5e310e233422e155118a3c034b2fa52d0fd07360633b59e9073e9a421e1de011016f1f4a8d010f50008b05250aea9e391a22882e88636d9f7f5dc45155a9da000e7ba02c98e03367010f814f03c44e335b0bad1ea83d54c009a31a12a47faa014c68d40f7093153698601b13ec2c20fad37929698e0610ee29aca8a6be2618d34506a739ba880cd645361649b90e7c93921faa94b8e52b5769f3560c95f27f1995466764097692ce162bb0ba12bc99c6a321f1528ed441950d8502eb60be12996a8e8476549524ecedab049ec8d542323863bd01c0a243c32ca0698a928ecc2428d86e64d000027687841522899bf0df0b0c33306508621d13b823e278e47d12a047ebde71700000000f237f92226501e46fe05b1eb1560ae00001915067ae90001d983a8a0a518aa7c5380cb0001ac40000478001fd40006c8000164c19a4b35721f950be7603ad00540002d42b1906c1dd6ed3b900012868e7000170e00000018480001000003898e593e8412115800161733f9d6aa90dc63a314223753a22d346d0a20946758555224cbc27f20ef23ee8746c519f9fa08962f046503cf4f445c01442b028804d8158c1cb5660d2b08b26d02a7106228b515faa04d629885f8139366a5fa4cc58e3851534096a7c0f2030e99048531ca8585ccad713ba0810f200000c03d15ac6da000045036402d0000c1e28b0000188fcc000323227a3155bc7740000000b4c000000103103c00000020887e023d3f5c0001a08e8000185138e3020000b1000089e57314fd48e1c1135896683a7ecc802c288863e707188505ea53d27a8af004ea772dd96f0a748d11171d1c6e42584230cd91888e43078dbcfee28c492204948a5371bc178846e8ee5558c8844017e51c08d4c58b0741a18289d23841ef909136486e2bd0a4d2c640e176ab20dd492025706bc2506c04df25e887f1c346713283b707d446223950253e3e8a7b92a98281dbe2083e820a0fb0d9c2a045e35f980c2c65a94a908b144e16a06ea70c4968fa1f01d3d5445a73ee00fc30e3150d501f09ce4be3f208f33f4317279199c1ee1c9902134434802a000193821b22d5369e4e980334272094076c89c33b8d9848a85828a095eaa44eb53026b4e7e4ea2d029e42ea59528411308c255e30c9f500e43110231918f7050e46b81d819874d8069e8419239c14e8134f6c48e3b4
  | 26 => 0xca1dc0484b447198a8ceca1718f02ec0081261b8998cfdc4d50bc83bc52474b0002418adc7480000f94c746c400000011bc9314b207c80000f901c073d28226c00001a12c097830900006f83a82660b44aae37c99dc3f64b609b159210cbea6511001e9825a86d0d71e286fa81b44ba7903922a739ca55c7cc80a2ef9fa294845a20080012aa19f0422bc639634c51c8edca9e7cc47905d87889612e228209880b92020f394920531239bc8000ac11720000c9224d4eb2380f1647a00000011d65301de946132c4922e59de504600000022588608b92b380002070000a124ac0009464530000a1660637f8000000000000077c00000034516780000001c2a1988d034518ee40c9e800047cabc80000004438000984a0735680014ed13817194400006f628693b80006aa40c6a74000657107c0000000d1000000080400000028ad57e00000000007a23fc293e4a050aa54163000000a02900000cc000ae24c5aa4468898d80014c939818500000001d696257b261e3167503db4cf4058118b87837894206204bab7224b9a10ab27b40000000be80004bc0002dc8000000b14d6125cc102a2a40b25b44ab0ff1251ff148c5733af93fd2ce5ff52d8000540000224873537e00011f807d5fb72d14022bad1275700012754ae0980000e5c00010456597f0c7594f000185ce1c28d000048c0005e642200007bca5c4041fccf6462f2bfa94868415d34a9a6122225f556a6e8c807c302d1b8008e9fb1ae18f54e019e2f240825f2391398a2a082535e4891cf0e6a74425a8000e36ac33cb80014b0a7251f89701e077f277869c19c45f217a8dcbaa2462d2a840000aeb3f244925c0a820001d50cfc840331094436a00006c40005be4064a499a87441205562354c4eb0d00021685307c60eaaa4073c80b2a8952cb3a55f5308140ada4a92ba11bc0061f2a97a7c042617a0f41c4471645854d0160eec87c06410780983040001ded20f73a53b2138000b2232ac0006c213c0000000aa0751238000124a72615f97047a66801609d38a0c8c811c83e15980ab5048bdc0000003d7a71820a5d00eb20bcf6a31200000ec2f032b8000000e1847448d5a40308a8c14813c00a28b64ca83b6e7a7d811241f963eb0b2ad83a4a90a7e0e29bc46aca13366e5987de3e83119fb089459235e1e646860dc8e9e804c9e53b23f22a558a9b5000216cb087cb14724c145858f2099758560737be7077443e863296267cc1087225c95302be0ed2ef04093ba168027a9341c8a861530a654fa9af39986ec0006cc42399905663c0563aca063a50709a06b510f23257e089ce9a56046c1508072435131a1a102e4950300570d343f102d88993d25c34c388847baad4513243d37a7c91691046e28000455a630f220b3820085cc0051138e82c4000b260b2a064c5c223824a75cf8
  | 27 => 0x9e15e2411d64cbe3f709d195000069c36a0eeca664b0402042e22900035c93c40270000fa94e48ae6ae2aa07653e26c634695944807f1344000038b0e700000000000003c70b34bf0000000000000000000010dd04e00048282088ecae31bf8000d283650c42c440007040000bfc26c00000000000007ed00020b5056000314000000095e48d1c5800027b00000000000001d205b84ce1c00111d001f800017902176065ea402ac5493061e10493f12a2562296981c29c94741753b4c9a10f30896e0782a1d193417515444d235155888c3cf437df5455c68b00016207049592c0ccf925800058d247061490843c23cf4fe087000012130425a47a49a8bf21b8560000000029432e1a3cbd87d344914c400089f46b2a380000003b114e15468b813d09f8000000368146c0b796819818940002f305fa2920000000ed24dcbf49d50a1cc98c2696b07fde810a81124400b28f6080f2da9dbc00029a4a21f9e2d63aa4b2a28000000005c214129a39447c0d44e8648807ac0000003803940000cf83fe000000026a08d0002284a0f63252621b02eea6913a0138d680002ee083d17497618d1aa134077524f1cb956c0001178000c441cc00009886266eb0002bec0002490000d7c0ce2be2809c68000179ac4a20c8401374f400003467a25709f10cf63890002210c02a203f12b4c97a6932e3525804371505d0e8084638f4468c9424e8a3d751975538020265a574516a51248a23d36c0c504f0b00b9c1ba070108907e534568665c1ac2d959083f25dc8dc43006380782973ca0500ff28d9282050467656b19d055c1322cb4f78da52266c75089b709ac1304279d30e065b21ab8e6521a6c22c509480004081071c22b807e7000093c0004841cae97d40c5174192bf44226e51030e4c00054449e1eb55de7c02239f049b865e05802d13221b70a59429475000000000000050303991dccd600019404c25228ed2d78b6c0005274e50404d40a034ba435c17a07e9662294c900e24382a152842f803223046ee37633488a11ec1ca1209bdc6d80a30000001184a6706d4adc00042b2bf24b67783b427600000004c9098978132478c51487808b230d0f39f281065a10001c0052c20b497a7041f778734f844117662d057050d3844503e91824225b2a11ec8f80d298a40a18112a864a59282500007b1127087414a5b30000dac5b0a651322acd41ea3000003d4344a4f2ac0000fec0001241be4e6dadd01f097200000021a0000d081fc00010e07243464cd000000000000000000007771a9a928000481000201c00000054920c000000021900dd4a600044c800000000b000000028e685126cf289d04520ca886c950000174a7888da00006a8e1c97e00033e800059f9e32c896d027e7a35760000b208650796760da22080002c6c0009db4a8453519681f38
  | 28 => 0xf683b52c58ecc218a9945f193a5e2229514000014e35a4f299fd128af5094a8f00005fe1578178b00324439a3495781804ef05a482a6de04ea3f43888154ab136cad46420292b44bd0000279800029063332c80004040000002ae080069b3ae0000b02000229a5e2f
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x142e92e1d54584540040fe61541c9611500103f98553705845416c0fa6387551601505b23a98e0154580540050e241541c960150014389055371580540061361d6318f5294801c0d5498e7210c5200703552639c853108018c48218573951320063120c615ca544c80183461e1d54151320048de6154153614c80103f97619541503216c8e24186550540c80103e989d95415032006611c684d4d320c80198471613534c832006511c685d0d320c80194471617434c83200651a1471d91320c801945851c7644c83200651a1471991320c801945851c6644c8320072159071191320c8018c471a1a544c832006311c586951320c8b3d0471d52544c832004c3e6154151320c8b1d0471550544c8320053165a741c5320c801546959d0714c83200551656741c5320c8018c7861c5704c83200661e10715c1320c801984841c5704c83206c33a63874c9610c81b2c698e0532584321b63121f814c9610c801987742053258032006611d0814c9600c81b1c7972053218032006619d0814c8600c80198574205321803200471261325c4600c81b4c497604634cb2100631a1d8118d32c84398c483ddb714cb2100531a5c63dc532c841b8c68718f714cb2106c71261325c432c848d4c7964c9710cb2100487e6154153634840121f985505418d2106e31204635ca534841b8c68718f714c92123631e1c634cb21484018c6821c7634c94000631a0c71d8932500018c4819d9320c94000631204764c83250001a4481d95320c94000691204654c832500014c4915c87298c4000531245721c963100014c4915cc739884000531245731cd62100018c4821c5634c8400063120c71589321004903f98597740c84006cb12458298c321001b2c49160e620c84006cb1247864c8321001b2c491619320c84000631207764c832100018c4815d9320c84000691206654c83210001a4481595320c8400053125d320c9611000141d9414273d972000507a4f655d265c800141d9510273d9320006075d683d9264c800103f9761954153200040fa627655054c800141e939d954153200060e2027655054c800142f9655272153200054a241549c854c801b4c49158c724c7200040fe61741d3654800103f985d475d91200040fa5b87550544800103d97a1954151200040f26276550544800142c96552721512000691207654c83248001a4481195320c920006a1207644c83248001a8481191320c92000711087651cd214805b838805d9541502016e0e20176550548400141d9510073591100050b654401c9644400181d7520d64191100060b5d482590644400103d97a1954151100040f26176550544400142c925d954151100060e2017655054440014349655171151100054c241545c4544401b2c491219320c91006c71261325c432440014c4964c9710c910
  | 1 => 0xe6070014218000012400000000048002000110510018e5a00431e00d1a030000000001d24a000000000002580000001a0000078b900000003e07c0000000000000000000000358000000000007a000a80097000008d0d2c278010000188202461800c8005a360e42c42151f8000000000000049804003b19800000048800c000000005c49b4874380000000147b00000ee2b000dc000000000000000000d40531898b2001f000000000000fa0047a24a40000000c88ea60848a0000160bc000000022000000000000021d140002000001e000009a903a982400b3d0a09c0030a1e827909834cc5b3895400001d0600000001fd28622e86c20841b20c000000000000000000008c0000044170000c008f8015c000026520000000194dc3f00000ec0000158000000000ce00219127068000005e8b1aa4800002203cb80000204040000000a000428640074180000000000f1042900000000000024a662bce38a81425000006f00000e000000001c0023146005f0011c0048800000000000000000000000000001b44e8d00002030003002080000c0601000000e00008080000000040201018280000018000000008000007000000005000180600000080400008000206018080201000240143a909c776550540050e64271dd9541500703d981c7765505400507a4c82dd9541500141d9320b76550540050ba4b81dd9541500142d92e0776550540040fa6021dd9541500103d98087765505400507a4c21dd9541500141d9308776550540050ea4021dd954150014399008776550540050ba4880dd9541500142d9220376550540050da4480dd954150014359120376550540040fa6310dd9541500103d98c43765505401c0f66376dc9541500183b76e0172550540060edd8805c9541505b8387061a705505401c0f25f865c1541505b03e98dd9705505401c0f663761c1541500183681dd870550540060bdda821c1541500182f7660870550540060ddd9811c1541500141e9321d54988540040f261545c26215
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x440800310471e6154151320c80180d499013b2a82a64000c0a248805d95415110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x1
  | 3 => 0x5
  | 4 => 0x8a
  | 5 => 0x6
  | 6 => 0x98a
  | 7 => 0x128a
  | 8 => 0x150a
  | 9 => 0x10a
  | 10 => 0xa0a
  | 11 => 0x130a
  | 12 => 0x180a
  | 13 => 0x3ca
  | 14 => 0xcca
  | 15 => 0x15ca
  | 16 => 0x40a
  | 17 => 0xd0a
  | 18 => 0x160a
  | 19 => 0x188a
  | 20 => 0x44a
  | 21 => 0xd4a
  | 22 => 0x164a
  | 23 => 0x1a0a
  | 24 => 0x74a
  | 25 => 0x104a
  | 26 => 0x194a
  | 27 => 0xb89
  | 28 => 0x170a
  | 29 => 0x1609
  | 30 => 0x1649
  | 31 => 0x409
  | 32 => 0x449
  | 33 => 0x1849
  | 34 => 0xbc9
  | 35 => 0x19c9
  | 36 => 0x10e
  | 37 => 0x1789
  | 38 => 0x5ca
  | 39 => 0xeca
  | 40 => 0x17ca
  | 41 => 0x1a4a
  | 42 => 0x1a89
  | 43 => 0x589
  | 44 => 0x1949
  | 45 => 0x749
  | 46 => 0x14d
  | 47 => 0x134d
  | 48 => 0x130e
  | 49 => 0xe8a
  | 50 => 0x18ca
  | 51 => 0x58a
  | 52 => 0x1a8a
  | 53 => 0x178a
  | 54 => 0xcc3d2
  | 55 => 0x15c3d2
  | 56 => 0x1a1652
  | 57 => 0x104752
  | 58 => 0x1a9952
  | 59 => 0x3c092
  | 60 => 0x3ccd2
  | 61 => 0x3c992
  | 62 => 0x3d292
  | 63 => 0x3d512
  | 64 => 0x3c112
  | 65 => 0x1a57d2
  | 66 => 0x3ca12
  | 67 => 0x3d312
  | 68 => 0x3d812
  | 69 => 0x3d5d2
  | 70 => 0x3d712
  | 71 => 0x3cd52
  | 72 => 0x3d652
  | 73 => 0x3d892
  | 74 => 0x3cd12
  | 75 => 0x3da12
  | 76 => 0x1703d2
  | 77 => 0x743d2
  | 78 => 0x1043d2
  | 79 => 0x1943d2
  | 80 => 0x583d2
  | 81 => 0xe83d2
  | 82 => 0x1783d2
  | 83 => 0x18c3d2
  | 84 => 0x5c3d2
  | 85 => 0xec3d2
  | 86 => 0x17c3d2
  | 87 => 0x1a43d2
  | 88 => 0x104743da
  | 89 => 0x1a9943da
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 34
  | 7 => 1807
  | 6 => 7191
  | 5 => 2865
  | 4 => 149
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
  | 8 => packedAt gbK8 (1024+((h/20+packedAt gbK8 (884+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (76147+((h/774+packedAt gbK7 (66859+(h % 774)*12) 12) % 3067)*12) 12
  | 6 => packedAt gbK6 (383486+((h/2737+packedAt gbK6 (345168+(h % 2737)*14) 14) % 9856)*14) 14
  | 5 => packedAt gbK5 (181515+((h/1040+packedAt gbK5 (169035+(h % 1040)*12) 12) % 3746)*13) 13
  | 4 => packedAt gbK4 (10934+((h/56+packedAt gbK4 (10430+(h % 56)*9) 9) % 355)*9) 9
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfff87fc0ff81fffff07f807000274cfd33f7cc
  | 1 => 0xf00f83ff07fe0f00ff83fffff0dab332ccc8ff
  | 2 => 0xffc0007fff000fffc007fff1cc3c30f0f0f
  | 3 => 0xffffff8000000ffffff800fe0fc03f00ff0
  | 4 => 0xfffffffffffff000000000fff0003fff000
  | 5 => 0xfff0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10e00cc00980110e70048310600004541153cc
  | 1 => 0xa121015102a20a1210812925204a113044c055
  | 2 => 0x24ab4084555a024ad68044ac714c2c30b0d0a
  | 3 => 0x48cdaaad0108048ce7256008ba0ec03b00ea0
  | 4 => 0x880f633ce679ccf0042018030dff0003eea000
  | 5 => 0xcf000030806108800840600c0efffba8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeaeeeaecc0feeaeeeaeeeaecc0feeaeeeaeeeaecc0feeaeeeaeeeaecc0feeaeeeaeeeaecc0feeaeeeaeeeaecc0feeaeeeaeeeaecc0feeaeeeaeeeaecc0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37053
namespace PEqualNP.Outside.L_meta_37053
open PEqualNP.Outside.L_meta_37053.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_64 : Interval s1Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 68 := (concat bs1_3_0 (concat bs1_3_32 bs1_3_64))
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
theorem bs1_4_128 : Interval s1Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 129 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 45 := (concat bs1_5_0 bs1_5_32)
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
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
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
theorem bs5_4_0 : Interval s5Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 2 := bs5_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
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
theorem bgb_4_128 : Interval gbAtlas 4 128 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 149 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128)))
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
theorem bgb_5_2848 : Interval gbAtlas 5 2848 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2865 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 (concat bgb_5_448 bgb_5_480))) (concat (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)) (concat bgb_5_608 (concat bgb_5_640 bgb_5_672))))) (concat (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832))) (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))) (concat (concat (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)) (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216))) (concat (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))))) (concat (concat (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568))) (concat (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664)) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)))) (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920))) (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))))) (concat (concat (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272))) (concat (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)))) (concat (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656))) (concat (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)))))))
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
theorem bgb_6_7168 : Interval gbAtlas 6 7168 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7191 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)))))) (concat (concat (concat (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984))) (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)) (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432))) (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 bgb_6_2656))))) (concat (concat (concat (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)))) (concat (concat (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)) (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 bgb_6_3328))) (concat (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)) (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552))))))) (concat (concat (concat (concat (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 bgb_6_3776))) (concat (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)) (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000)))) (concat (concat (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)) (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 bgb_6_4224))) (concat (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320)) (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 bgb_6_4448))))) (concat (concat (concat (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544)) (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 bgb_6_4672))) (concat (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768)) (concat (concat bgb_6_4800 bgb_6_4832) (concat bgb_6_4864 bgb_6_4896)))) (concat (concat (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)) (concat (concat bgb_6_5024 bgb_6_5056) (concat bgb_6_5088 bgb_6_5120))) (concat (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)) (concat (concat bgb_6_5248 bgb_6_5280) (concat bgb_6_5312 bgb_6_5344)))))) (concat (concat (concat (concat (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)) (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568))) (concat (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)) (concat (concat bgb_6_5696 bgb_6_5728) (concat bgb_6_5760 bgb_6_5792)))) (concat (concat (concat bgb_6_5824 (concat bgb_6_5856 bgb_6_5888)) (concat (concat bgb_6_5920 bgb_6_5952) (concat bgb_6_5984 bgb_6_6016))) (concat (concat bgb_6_6048 (concat bgb_6_6080 bgb_6_6112)) (concat (concat bgb_6_6144 bgb_6_6176) (concat bgb_6_6208 bgb_6_6240))))) (concat (concat (concat (concat bgb_6_6272 (concat bgb_6_6304 bgb_6_6336)) (concat (concat bgb_6_6368 bgb_6_6400) (concat bgb_6_6432 bgb_6_6464))) (concat (concat bgb_6_6496 (concat bgb_6_6528 bgb_6_6560)) (concat (concat bgb_6_6592 bgb_6_6624) (concat bgb_6_6656 bgb_6_6688)))) (concat (concat (concat bgb_6_6720 (concat bgb_6_6752 bgb_6_6784)) (concat (concat bgb_6_6816 bgb_6_6848) (concat bgb_6_6880 bgb_6_6912))) (concat (concat (concat bgb_6_6944 bgb_6_6976) (concat bgb_6_7008 bgb_6_7040)) (concat (concat bgb_6_7072 bgb_6_7104) (concat bgb_6_7136 bgb_6_7168))))))))
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
theorem bgb_7_1792 : Interval gbAtlas 7 1792 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1807 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)) (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 bgb_7_416)))) (concat (concat (concat bgb_7_448 (concat bgb_7_480 bgb_7_512)) (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640))) (concat (concat bgb_7_672 (concat bgb_7_704 bgb_7_736)) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864))))) (concat (concat (concat (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312)))) (concat (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536))) (concat (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664)) (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 34 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 44, 60),(inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeaeeeaecc0feeaeeeaeeeaecc0feeaeeeaeeeaecc0feeaeeeaeeeaecc0feeaeeeaeeeaecc0feeaeeeaeeeaecc0feeaeeeaeeeaecc0feeaeeeaeeeaecc0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4008373440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37053.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.and,[2,3]⟩,⟨.or,[4,7]⟩,⟨.and,[6,7]⟩,⟨.or,[2,3]⟩,⟨.and,[0,8]⟩,⟨.and,[1,10]⟩,⟨.or,[11,12]⟩,⟨.or,[9,13]⟩,⟨.and,[0,5]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008373440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008373440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37053

open PEqualNP.Outside.L_meta_37053 in
theorem PEqualNP.Outside.L_meta_37053 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008373440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008373440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
