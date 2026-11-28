import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37277.Model
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


end PEqualNP.Outside.L_meta_37277.Model

namespace PEqualNP.Outside.L_meta_37277
open PEqualNP.Outside.L_meta_37277.Model
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

def SBf (j : Nat) : Nat := [5, 6, 6, 6, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37277

namespace PEqualNP.Outside.L_meta_37277
open PEqualNP.Outside.L_meta_37277.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xe421
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | 3 => packedAt s0K3 (i*16) 16
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s0K3 (17+((h/1+packedAt s0K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffe03ff81fffffffffffc03f1fffc7
  | 2 => 0x3fc07f00fffffffe0f80f81f80fffffe64cff
  | 3 => 0x3fff8000fffffffff000ffe000ffffff870ff
  | 4 => 0xfc0000000fffc0fffffff000000fffc0ff80f8
  | 5 => 0xfffffffff00000fffffffffffff00000ffff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x186450a1802382180318d18a28e2c6190a95c3
  | 2 => 0xa929314696449469606a46a1b1255a6a664c5d
  | 3 => 0x5250a26b2a8928b2ad048b6c8249acb4b870ae
  | 4 => 0x6362c58dcd120edcd6b6e049248e3718df80f0
  | 5 => 0x8383060e0e1c30e718c70c71c7003820f56a00
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcccccccf000c000fcccccccf000c000fcccccccf000c000fcccccccf000c000fcccccccf000c000fcccccccf000c000fcccccccf000c000fcccccccf000c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37277
namespace PEqualNP.Outside.L_meta_37277
open PEqualNP.Outside.L_meta_37277.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xc82000748c0b28020508000080bf42bd42de32dc32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x70000112009200a3300f26aa3a15594632c6a10652d52d069ca518e55043196a9081355110298a4985514530
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
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
  | 4 => packedAt s1K4 (212+((h/4+packedAt s1K4 (192+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s1K3 (282+((h/3+packedAt s1K3 (270+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff83ffffffe07ffffffff03fffff1ff1ff
  | 2 => 0x3f03ffc1ffc1fff878383e0ffc3fc1fe94e73
  | 3 => 0xfc003fffe0ffe0fff803fc00fffc3fe0f18f9c
  | 4 => 0x3fffff0000fffffc0000ffffc000fe0fe0
  | 5 => 0xffffc000000000ffffffffff00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x104000880008000008840422200444840210a5
  | 2 => 0x48a65910ca5138658321a3445642a85a694652
  | 3 => 0x292aaa2146a309aab042e9089aa83342b18b18
  | 4 => 0xb2cd344a943a52d35de84212ed33018cde0de0
  | 5 => 0xc30e387318c39cfc6673739c0e222210fde000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37277
namespace PEqualNP.Outside.L_meta_37277
open PEqualNP.Outside.L_meta_37277.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x6a418e400569100a0024de43dd43ee42ed42df32dd32de31dc31de30dc30ee20ec20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x21840aa28a874d520c6aca3184b55020
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
  | 3 => packedAt s2K3 (112+((h/1+packedAt s2K3 (108+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc1ffe0fffffffe0ff07f07f03ffffffe4ccfff
  | 1 => 0xfe07ff0f81ff07f0ff87f87fc1f07f81b3727c
  | 3 => 0xfff8000ffe1fffff0007ff8001ff87ffc3838f
  | 4 => 0xfffe007fffff8000001fff801fc03f0
  | 5 => 0xfffffff0000007fffffffffffe000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4450810084020001300900908c5088940444b5
  | 1 => 0x8c3148111c442a305283282384b4550c91525c
  | 3 => 0x10a25aaa28d8a6d60a46b505112d4669c3830a
  | 4 => 0x39c59ccc518eb76beb50a40a29ce6431fc03e0
  | 5 => 0x210610886110c58c8c64c64c300800416aa800
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeeeaa88aa00eeeeeeeeaa88aa00eeeeeeeeaa88aa00eeeeeeeeaa88aa00eeeeeeeeaa88aa00eeeeeeeeaa88aa00eeeeeeeeaa88aa00eeeeeeeeaa88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37277
namespace PEqualNP.Outside.L_meta_37277
open PEqualNP.Outside.L_meta_37277.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x20480a40214702c0030c400c00de43dd43ee42ed42df32dd32de31dc31de30dc30ee20ec20
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1a0080aa28a874d520c6aca3184b55020
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
  | 4 => packedAt s3K4 (212+((h/4+packedAt s3K4 (192+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s3K3 (111+((h/1+packedAt s3K3 (108+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc1ffe0fffffffe0ff07f07f03ffffffe4ccfff
  | 1 => 0xfe07ff0f81ff07f0ff87f87fc1f07f81b3727c
  | 2 => 0xfff8000ffe1fffff0007ff8001ff87ffc3838f
  | 4 => 0xfffe007fffff8000001fff801fc03f0
  | 5 => 0xfffffff0000007fffffffffffe000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4450810084020001300900908c5088940444b5
  | 1 => 0x8c3148111c442a305283282384b4550c91525c
  | 2 => 0x10a25aaa28d8a6d60a46b505112d4669c3830a
  | 4 => 0x39c59ccc518eb76beb50a40a29ce6431fc03e0
  | 5 => 0x210610886110c58c8c64c64c300800416aa800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeeeeeea8a8a0a0eeeeeeeea8a8a0a0eeeeeeeea8a8a0a0eeeeeeeea8a8a0a0eeeeeeeea8a8a0a0eeeeeeeea8a8a0a0eeeeeeeea8a8a0a0eeeeeeeea8a8a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37277
namespace PEqualNP.Outside.L_meta_37277
open PEqualNP.Outside.L_meta_37277.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x160048007ab003851626000090a0040000001a1201939b3430b84327969f02711184c2c9072a0800d4074a285494880008d4830120d204e1c0000180100ff43fe43de43fd43dd43fc43ff42fe42ee42fd42ed42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x441e702332002c002f5527305b002e0d0a2811412665362a12004c1a00421b074d201f724000352d1504740000343d644a635d37003e0038002150006954006f004b000000006a5c5e18566e0e090b294f030c3962006000610068536b452500583c17000052571c0000224e104608133b002b0f00731d473a24713f6d005a0148005933003100490600661400165f51430500006700006c19020000808d8002828300870100000180008201828003800000058300828088850184050d81808f0180db94b43b6a96875d5490eeea2a1dd14543cfaa287d75150fa8a2a1d794c43b7290876d5210ebca7a15754f42cea1e856d5490b9c87217350e42cea1a85775150ae8a2a16bd5142d7a1a85ce4350b5a86a17350d42c6a1a85e75150bc8a2a15794c42aea98856e5210a7ca8194f55032e6990655e53d06baa7a0db94b41b6a96839d439075a8520d794c41aea98839d43106dca420db54841d6a10837a50106f2a020cf953319eaa6636e52cc6daa598cf953219eaa6435e53c86baa790d794f40aea9e819d43d02dca5a05b54b40d6a16817651902eaa3206750d40d6a12815e53102baa6205b94840b6a90817651102eaa2205d94630baa8c616f524c2d8a4984f950309eaa0616e520c2daa4185d94430baa88617651882eaa31057d4d20ae29a413e540827aa8105794c20aea98417651082eaa2107590f10eaa1e21e642c43ca85885d546109faa2213c54442bea6885714d10b7a92216c524436ea8886d15110eba9a21d453443ac86887550d10f3a9221e452443cc84887950910f9a8221f240443e280885d94410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x14418282b0c18038899a59e000a9c922b928040280001886758069c550c5150a8d6490d42a91854350b876150d42e11854350b8543d4542e150c5150b0d544c832c350d521070d5350841c650d50107294254041c350d52d030d5350b408b590524c21d6414d20e150d42c43145414d1095195434432454149109919542443854350910e450d40443a14250110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x194000a0cebb0a86a14877650f5150a823aa86a1221811954350910
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s4K5 (826+((h/15+packedAt s4K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s4K4 (3471+((h/39+packedAt s4K4 (3159+(h % 39)*8) 8) % 155)*8) 8
  | 3 => packedAt s4K3 (952+((h/8+packedAt s4K3 (912+(h % 8)*5) 5) % 29)*6) 6
  | 2 => packedAt s4K2 (199+((h/1+packedAt s4K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x83ff0ff87fffff07e1fc3f81fe1ffffe9331ff
  | 1 => 0xfc1ff0ff81e1e1f8fe1fc3fe1fe1c1c16dcecc
  | 2 => 0xffe000fffe01ffff001ffc001ffe01ff8e0f0f
  | 3 => 0xfffffe01ffffe000001ffffe01f00ff0
  | 5 => 0xffffff00000001ffffffffffe0000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x88401009040000002024048442024444011055
  | 1 => 0x18c601111c424218620c411c4e208c8c2546cc
  | 2 => 0x218aaaa228d5916b111aa828955411398e0b0a
  | 3 => 0x7314ccc45190d5b5d542205119993811f00da0
  | 5 => 0x42188886611919c69993326181102021daa000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeeeeeeeeeaa0eaa0eeeeeeeeeaa0eaa0eeeeeeeeeaa0eaa0eeeeeeeeeaa0eaa0eeeeeeeeeaa0eaa0eeeeeeeeeaa0eaa0eeeeeeeeeaa0eaa0eeeeeeeeeaa0eaa0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37277
namespace PEqualNP.Outside.L_meta_37277
open PEqualNP.Outside.L_meta_37277.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x4817e53902faa7206f90e40de21c817e52902faa5206f90a40de214817e51903eca3205d94640bea8c81f551902eaa3206fd0640dea0c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a817c515037c82a06f10540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081be421037884205f94440bea8881bf411037a82205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630bea8c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa9261ef524c2dea4985f14930f6292616c524c3be6498774c930bfa8a61f7514c2eea2985f14530fa28a6174514c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa418778c830ee190617e510c3eca2185d94430bea8861f5510c2eaa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f719641ed32c82fca3905f54720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef32883d865105f94620bea8c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f719241ed32482fea2907dd4520bba8a417c51483e8a2905d14520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4107bcc820f6190417e51083eca2105d94420bea8841f551082eaa2105f94020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fba0e21f441c43ec63887d4c710fb10e21f521c42fea9085f95210df2a4213e54842faa9086f552109eaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087d90610faa0c21f731843e863087dc8610fa10c217e50843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fba0a21f441443ec62887d4c510fb10a21f521443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f641043ea82087dcc410fa18821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4290afca3215f54642bf284857d5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a85f75150aeea2a15f14542fa28a85745150afea0a15f14142bf2a0857e5310afaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210afca2217d94442bb288857d5110beaa2215d54442bf280857d5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccafca3997d94732bb28e657d51ccbeaa3995d54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7195f94a32ef99465ef328cafca3197d94632bb28c657d518cbeaa3195d54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cafaa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cb9a64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea9683bf42d077a85a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41df21483bc42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077a86a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077c8620ef10c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa0883b541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea94637e518c7ec8318fd50631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131bfa92637c524c7ec8298fd50531fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf298637e520c6faa418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fba0e43f441c87ec6390fd4c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621fb20c43f541887ee6310fd0c621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21fb20a43f541487ee6290fd0c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53086faa610df14c21bf290437e51087ee8210fd10421fb18843f531087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e81f651d02eca3a05f54740faa8e817551d037c83a06f10740beaa
  | 2 => 0x2d2734d000000021c208002f600131000000a280009a0000000000016a000000910007900000000032800000054000001c8000000b1800000000000d441e7f0001a5000374a6274214000280dc0008fc00000000000001a600000000000000000001e73201b40011252400000000000000000000001b80009f274000000000000009280005205033a4b00061000168000000000000000000005d000000a40000000000008b00000000000000001120000003f8000000003d400000000000ec8001605340e9bb2fa850c480000008c00000000000002770007000003c28c89d4327c00000000000000000000000000013b000350000830003cc00000229292768f880041a00000000000358000fc0000ec6b88c00048508849000000d194b000000388000008e44c000374000000003be0008f8000007053a8002a6000000000000000000024e0c0e1000000990000004886490580006e001098e03300000024d000000000003c01e4000000000000000021c6550b8000000000000026c90902804072001499720004a81300031c001230004b400077a120000000016700000000000236000000000000004280003c5acc9800000994ad0770000000000000039c001cf1ee1c80000000000049800000000000000000ac0000000000000000000000c58fb000000af0c62b04ec0e0344fe3b0000963ae0006f1fe00000000000000000250000d2008000010060020000000000a00400000000004038000020000000100400400800000000000020000100080001000401800000010000000000000280100e000000060020000200000001000001000000000020080040080200000c000000180000080200200006800000008008000080000000000000000002000000010020040040080200000c0000000a0040000000200000000000000028010000000100000000000001000000000000000000200000800000000006000040010020000080000000400001000004000020000000000100200c050030000040000200200000001010000000020000000000000000001802002004000080000000080100400000000000000000010000000400100001400000004004060000000040000000200800001000000008020040000000100000afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1fdd4543bba8a877c5150fe8a2a1dd14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221fd94443bb288877d5110feaa221dd54443bf280877d5010efca7a15f54f42df21e85bc43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485e
  | 3 => 0x8000009700088d0000005c8003ba000ad80026a000b6a67520134d891831076d150001448e9218000000000018a0000011d9f73e67a8000003aa5140012450e7d89a1034e40000024a1820011c1140bc000000002ea000b980312800000111000590948004380000024000000000000000001170ae000000320000e6a308580000000000000000000000c5332000000001c28d0000e20000007887f2380000000000000000000000000d08000009a80000000030c0000000017cafa8b5007d144800000000000000002b4000000008840013c000858000003960010800000000000000022000e88000006b00020e000000001440008f887800000488000000000000000000000000070270000cd000000000000000004c4d20ac098788eb03e086144598b60009ac0020c0a4001240560005c4ee000000000fc8d0000000001f8000000000450000000000011e000201c52849b0000000d439451919462894000d8000000000000007d40c8000006f400000000000a085844074c990003d00000000000004c000000009c04d9a74509bc7703a2ba558000000000000023535a15ca72792ec960b821a4a6584a782145800000000000000000000000f4000aa0000000700000025c968ba408000000000fc8000025f00000066800106958000d300000000068000000001ee17608000000202000000000005b000108164948001620006c000000036000ae1660b80009e8000005bc0009d20a0003d80000070d440e900000000075000000c88000840010aa3c000000638003520000019b1c6354970fd45a00000000000000000c400011c000004ae000078001086e00003f000000000003de00000000034000fd1811be000670ab00033cb280000040064000000000000000000000000043a0000018d000000000000008bc000000007c8000000000002c8002f200000000000650000004c0000000004fc0000000008c0000000040261800000066000000bd00000130800000000000000000000012f13c0010c28e0002dc002514f6254bc00000000000000000001261fb1f26ac450ff5280012a0a917005c270a10001f000000000000f5a41000344da800000348000000000002d00000000000000048000000004608246c8001b400000206000000001af1d616c128c0000000068000000000000033e0012e952110608d1000000000812910000000000000000000000000000000000000000000000000000000000000000000003e0000093e0048000280005440000021a0000017c3007a40000000039800000000000000000002f0000002080e00014700000000000306000001ec000a6000000436000001430000001390932c270000001681bc2200c37248c001591d40000011627e0004016014c000740000006f8d9263000000a80903b00000000
  | 4 => 0x670000060000000000003e614500000000000027a2d418c000003668c800000000000000000004740000000063000000000000000000000000004800000128000196000171cc0007940029915e0005387d0ec00000000004000e8174096000fe800000000000000009cc00000000000000000007180000000000146800000820bf82f000a582a11033a48000000000000c38000003b40024f00065c001aa47a0000000050a0007a20a0000000506222e0004c800000000472782340013ea680000000007a06400000284000000001330000000000000000000000000001158000004300005300000000000000000002951f4294002360004ac0000000078c00000000000000b100096c0000036c2a0790000000000000000000000000000000000000000000025e0001b0002070000c4df9574446b8ef21f09e33000137000a3c980a400001400086000001229134aa184000000000554b9bc4cc49800000000000001b71c80004924e4060005f8354b20009600022a0010f26e00000000000000728040000008dce2000000000a006600000000000000000000180009b5348000000008f00039c000000003929c4e91c706c8080008133c0000018f0000000000b0000004102c0001ac00000000000000c9000000000db432a08000005060007b000000000f68000003080002d0000000000027c0000007802001c00000000a040016e0005551180011200000000044924000003a85dc0000000000000128000000300000002f8798000ca41c781390e87840014a02c898001ff2f491caa1b42fc0000000000000000000000001198000000002a
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x353c827661d4f209d58753c823e6494f208f59253c82766194f209d58653c834c534cb208fd9151c823c64547209d987548827561d52209d986548827561952208fd91538823c6454e209dd8553882746154e208f990538823d6414e209d98453882756114e20d3d4c328823e64946208f592518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534825e6514d20c7d50534831c5414d20d3588534826e658c920d314e324826c654c920d314d324833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c514834c53881209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530834c6254c208f990530823d6414c209798c530826e6214c209d98453082756114c209b597320834d53cc8209b594320834d530c820cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420d354f200826f6548020b318d200834d53480209ed95200833461553108f99353c423d64d4f109b98b53c426d62d4f108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b108f99052c423d6414b10cd55341c43355410710cd55231c42b4644c710cd55131c43355488710ad19121c43355448710cd586548423e64d4e108f593538423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6414a108f590528425e6314a109758c52843365490610cd951418433654cc610ad5903184336540c610cd95321842b56408610cd95021842b564c4210cd9531084275619511097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d109dd85534423e6414d108f590534423f64549108f191524425f63549109718d524427761549108f990524423d64149109d99741442766510510cd5504144276658c5109d19531442b4644c5109d99621442746548510ad19121442b664841109d987540425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b58853042766114c108fd91520423c64548108f990520423d64148109798c520425d63148109d984520423e64944108f592510427565904109dd95410433454504109d5973104275650c410ad590310427565c84109d59421042b564084108f992500423d6494010ad593100427965840109dd95100427b6544010
  | 1 => 0xc66d62152318fd91528c63c6454a31cd151418c63e64942318f592508c63e64951319dd85544c63e6515131cd584544c6766590531cd152414c6746550531cd151414c73454cc5318f596540c73461550318f990540c67661150319d597410c73554d04319d594410c7355410431cd552310c65f654c4319dd95310c6b4644c431cd551310c65e63d53219758f54c863e64d4f218f59353c863e6494f218f59253c87375410721ad19131c863f64543218f19150c865e63152219758c548863f6454e218f191538863e6414e218f59053887345450621ad590318863e64942218f592508863e64951219dd85544863e6515121cd584544863e6494d218f59253486756194d218fd91534863c6454d219ed8153486786054d219d996414873454905219d195414873454505219d997314873454cc5219d99431486b5640c521cd150314873454c85218f596540873461550218f990540867661150218f993530863d64d4c219d987530863e6414c218f590530867a6014c219e580530867565d0421cd55341086756510421cd5504108675658c421cd5523108677654c421ad1913108735544c421cd552210866f65484219dd9521086b46448421cd55121086b46150f40ad18542d03374354740cd50d51d03374254740cd50951d03355190740cd54441d02b56110e40ad58442903364394640cd10e51903364294640cd10a519033651d0640cd94541902b561d0240cd94740902766114d409d584535023e65d0d40ad185435027661149409d584525023e65d0940ad185425023e6510540ad98640502776154c409d185531023d6590c40ad584431027761548409d185521023d6590840ad584421023f6550440ad587401023f65500409ed95401027761553309d18554cc27661153309d58454cc23e6494b308f59252cc2766194b309d58652cc23f64547308f19151cc27661d52309d587548c27661952309d586548c23f6454a308f191528c2776154a309d185528c23e64946308f592518c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c32f54d4930cb153524c32f5414930cb150524c25e65cc930d314b324c34c524c930cdd53514c33454d4530d9d4b514c36452d4530cdd50514c3345414530d9d48514c3645214530d314a304c26e62d50309b58b540c27661d50309d587540c23d65950308f990540c26e62150309b588540c27661150309d584540c32e5494830cb552520c32e5454830cb551520c25d658c830d354a320c34d520c830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430d354b300c25f654c030b3189300c34d524c0309ed95300c27761553209d18554c827661153209d58454c823e64d4f208f59
  | 2 => 0x498003547f800000380000000000000003585b0003403b000040000d60000e41001f0002b01944f1b32a4000a2956000000290d80000009f18c0440006d81b0008700c0003e05c48187c29c0009900c000758808f40ae810698690004e8ce9911f8010e78000f66c06e19e2560004780016c4e01c800000000000f8000000000000006b4511fc3dc4b4ec8003d27e8fb0e20000001a80000000000119000570e321500045c6f1620da478929974285d0cd21d1fc1dce20612280004489c000000000003d604839800346000000000006200000000018c000004205cc908340000340006407000030040200002008000200b00c0101c0200801004020240300c040000905020004120000d008090340200001008020040202407014000000c000020380b000000180002c0100812000000500c004020080000003068020000c02001010020000c0181a01c0700000000000280600801000000040300812018000100601c01000000100000c0200802004000001704c09038000040103c030040602c00040010001301801004000100204801010010100001400008030000500c0201c080000001c040040000009020000040801c0a014000000300c0102401014100100b002776154b439d18552d0e7661943439d58650d0e766194a439d5865290e7761542439d1855090f3643145438fd954310eb46150c4397d954310f374354443cd50d5110e776154f429d18553d0ab56110f429d98650d0a7561943429d9865390a756194e42ad1854390a7761542429d1855090a3e6510d42ad5844350b364314542cd10c5150b3642145428fd954310ab46150c428fd954210ab461508429bd954210b374354442cd50d5110b374254442cd5095110a7661d53329d58754cca7661153329d58454ccb365494732cd55251ccb365454732cd55151cca7661d52329d587548ca7661152329d584548cb365494632cd552518cb365454632cd551518ca7761551329d185544ca7b60551329e181544ca7661151329d584544ca3e64145328f590514ca3e64141328f590504ca7661141329d584504ca7761550329d185540ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca3e64948328f592520cacd638c83297d95320ca6f654c832b3d95320cb4f654c832b3181320ca3f64544328f191510ca3f64540328f191500cb4d32540329dd85500ca746154032ad18543d06b46150b41ad58443906b56110a418f99743506b46150d418f99742506b461509418f59643106b56110c418f59642106b56110841ad592411063f65504419dd9541106b76550441cdd9541106b46350441cd54d41106b46250441cd54941106b76050441cd506501066e62d53319b58b54cc63e6494b318f59252cc73754107318fd9150cc63c64543319b988548
  | 3 => 0x6800780008481c8280013e2d4000272ce74c9100b2d24182204a0b2024000000007ec0017c1d83206715a10a000fc9242f0000588000000002409128220c071040500007306f2c808ced16a0000011219c2a87e0cc1c80fa5c07a800424808728003146640000031e530ca08d3fa09010a2143e7843720c0003bc8a8cd000740db9273aa204530000000000f80000075c00000000428000000000002b00008c84c0008425c3dc0c94b0d40005e00039c41cc092f4024745f8bb06e1e80011b0000009b81c00021c659b42520c02a8df446000bf8b31540000f08e000000b60000001e4001e60000009e8751525f87d9461d225000000000000bb80005c528f607f43c000e38000c86c400134394818e91ab278828e28001c2000509c12d03ccb080015a00096000132000622253367dc4b800372000d29b50100000e9a23700007700026a2c0941f40004a80021a00000000000224058000002be4ecf79bc18e3a80009a0007fc001ea19e000000f1262578401932ae2c8a69400d8248df0660e238c15a03000690a3900000460c317b15885c650a828850cef80006210c9302f000144000360000006b8ff21a84500000234820689660006bcf380015e44c859a7156000001e0352138001f30000007e83d3000000005d00022c0000020454c068003c4000001bb3a85748b0ba1b45649809031c17c00032172004791871b248c2a0603c64304d8a01c80ec7b053000130738ae3e40b0b91c935c770000000066e82e067000000000002dc258b00a5308314030503862f8b1a05070524001cc33e4cc23a2042c3ad048002204e4e10980000005e8d400000000183000380c587e0bc6850706802210413025198000410000000e800111000324000002b6300430b81aa000000002f48988f8c24301c0ef1081f4648c681508a000ed96b41a3a0539e502e7c45b9b23c81240008a32c888001a60000001681a2fa0000005a284000f680029e0003c000000554000000e8000001cd000000000000000005a11c41e6f4038000b072d0d8d6000050bc8950146fc0016d1da4d8c11652a243c521751f24240804b004318460003505bc519d83ba3c01483c00082c0000006604c6e800186134000003120000000000064015000000000028c1000000000000000000010e0000009f8622ec000440000006149009d000654000d2000000a42193a25401f9b609e000001f53d
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x38800660c12269290a52001c78099001608000432280fc28c6a9a8220e24625494110693396a820e63495c85450631868ecaa26218d1673d5041c868ab98a8a0c430d5d8540c521868ecaa26210c347655121086263b2a6900410d1d9544c710868ecaa2438843576950318421abb4a810c210d5da54c4210a28e6aa0828852472550414428ab98a8a0821495c85450410
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 20
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (i*5) 5
  | 6 => packedAt s5K6 (i*16) 16
  | 5 => packedAt s5K5 (i*27) 27
  | 4 => packedAt s5K4 (i*38) 38
  | 3 => packedAt s5K3 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (20424+((h/222+packedAt s5K5 (17982+(h % 222)*11) 11) % 1556)*11) 11
  | 4 => packedAt s5K4 (22768+((h/183+packedAt s5K4 (20938+(h % 183)*10) 10) % 800)*11) 11
  | 3 => packedAt s5K3 (1010+((h/6+packedAt s5K3 (980+(h % 6)*5) 5) % 25)*6) 6
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffffc1fffffff03c1ffffffc1fffffc1ff1ff
  | 1 => 0xf81fffe03f0fc3fc01f0f87ffe3c0f03127ecc
  | 2 => 0xffe0ffffc00ffffffe00ff83ffc00fffe38f0f
  | 3 => 0xfffffff003ffffff0003fffff003fc0ff0
  | 4 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x840044488020000805128844045214804b055
  | 1 => 0x92c6c8c39294a72c30b85c69f2286a1b1256cc
  | 2 => 0x218a5109062921555200952294808cb1630b0a
  | 3 => 0x8514a21224818a9a652a00432932c022b80da0
  | 4 => 0xc618c39c38ce33e3b9cce670302308c3dfe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfaa8eaa0faa8eaa0faa8eaa0faa8eaa0faa8eaa0faa8eaa0faa8eaa0faa8eaa0faa8eaa0faa8eaa0faa8eaa0faa8eaa0faa8eaa0faa8eaa0faa8eaa0faa8eaa0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37277
namespace PEqualNP.Outside.L_meta_37277
open PEqualNP.Outside.L_meta_37277.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001017fd5003fe54017f55003fc54017fd4c05fe53017f54c05fc5300ffd0c01fe43007f50c03fc43017fd4805fe52017f54805fc5200ffd0801fe42007f50803fc42007fcc801fe32007f4c801fc32017fd4405fe51017f54405fc5100ffd0401fe41007f50403fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc5000ffd0001fe40007f50003fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842007ff5421003ff2a108013fc5084019ffa042004ff90210007fa8108013fc4084001ff9842004ff8c210007fa6108013fc3084001ff9042004ff88210007fa4108013fc2084007ff8842000fdc421001ff6210802fff65440177fb2a2000dfd9510004feca8802ffe65440057f32a200bff5951005dfaca8802ffc65440057e32a200bdf19510014f8ca88003ff64440017fb22200aff9911000dfcc888003fd64440017eb22200aff1911000df8c88802fff5444015ff2a2200bff55110057f8a888003ff63440017fb1a2000ff98d1004dfcc688003fd63440017eb1a2000ff18d1004df8c68802fff5344017ff29a200bff54d1005ff8a68802bff4344001ff21a2000ff50d10057f88688003ff62440017fb122000ff98910045fcc488003fd62440017eb122000ff18910045f8c48802fff5244017ff292200bff5491005ff8a48802bff4244001ff2122000ff50910057f88488003ff3244001ff1922000ff4c910007f8648802fff5144007ff28a200bfd9451005ffaa28802ff55144007fe28a200affd0510057ee828800ffe4144001fea0a2003ff10510057e88288003ff3144007ff18a2000fd8c510007fa6288003f53144007fe18a2000ffc851001ffc4288003f62144001fe90a2000fd4851001ff8428802fff5044017ff282200bfe9411005ffaa08802ff95044017fe282200affd0110007fc8088003fd4044015fe2022000ffcc110007fc6088003fd3044001fe1822000ffc8110007fc4088003fd2044001fe1022003ffc411001ff62088003fe1044001fb0822004ffd941001dfeca0800ffe65040057f3282003ff59410035faca08013fc65040077e3282004ffd901001dfec80800ffe64040037f3202003ff59010005fac808013fc64040077e3202006ffd501002ffca80801bfd540400bfe2a02004ffd8c1001dfec60800ffe63040137f3182003ff58c10005fac608013fc63040077e3182006ffd4c10037fca60801bfd530400dfe2982005ffd0c10007fc8608003fd430400bfe2182004ffd881001dfec40800ffe62040117f3102003ff58810005fac408013fc62040077e3102006ffd4810037fca40801bfd520400dfe2902005ffd0810007fc8408003fd420400bfe2102000ffcc810007fc6408003fd3204001fe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff0841003dfcc00801bff5004009ff2802006ff54010027f8a008017ff4004009ff2002000ff50010027f88008003ff3004009ff1802000ff4c010027f86008003ff2004009ff1002000ff48010027f8400800fff1004007fb8802004ff8401001ff4200800ffd1004001fa8802003fe44010
  | 1 => 0x3fd61080017eb084008fd58420005eac210013fc6108021ffa884010ff94420087faa210043fc510801fffa084000ff90420007fa821003ffc4108001ff9884000ff8c420007fa6210003fc3108011ff9084008ff88420047fa4210023fc21080237f3004010ffd4020027fca010043fd5008009fe280400fffd0020027fc8010003fd4008009fe2004000ffcc020027fc6010003fd3008009fe1804008ffc8020047de4010013fe2008011fd1004008ff48020007da4010023f92008007ffb2e2003bfd971001ffccb8800afe65c4007feb2e200ebf5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc988006fe64c4007df3262001af9931001ffac988002fd64c4007deb262000af5931001ff8c98800efc64c401dffaa6200dff95310077faa988037fc54c4007ffb1e2003bfd8f1001ffcc788026fe63c4007feb1e2000bf58f1001ff8c78800efc63c401dffa9e200eff94f10077faa78803bfc53c401bffa1e2000ff90f10007fa8788037fc43c4007ffb162003bfd8b1001ffcc588022fe62c4007feb162000bf58b1001ff8c58800efc62c401dffa96200eff94b10077faa58803bfc52c401bffa162000ff90b10007fa8588037fc42c4001ff9962000ff8cb10007fa6588003fc32c4007ffa8e2003ff9471001feca38800ffd51c401dfaa8e2003ff1471001ffe8388037f741c4007ff20e2003ff5071001ff8838800ff441c4007ff98e2003ff8c71001fec638800ffd31c4001fa98e2003ff0c71001ffe438800ffe21c4007fb10e2003ff48710007ea438800ffc21c401dffa86200eff94310077faa18803bfc50c401bffa062000ff90310007fa8188037fc40c4001ff9862000ff8c310007fa6188003fc30c4001ff9062000ff88310007fa4188003fc20c4009ffb2c2007bfd961003ffccb0800afe658400ffeb2c2007bf59610027f8cb0800afc6584009ffb242000bfd9210067fcc908006fe6484001df3242001af99210007fac908002fd6484001deb242000af59210027f8c908006fc648400fffaa4200cff9521003ffaa908033fc5484009ffb1c2000bfd8e10007fcc708026fe6384001feb1c2000bf58e10027f8c708026fc638400fffa9c2007ff94e1003ffaa70801ffc5384019ffa1c2000ff90e10007fa8708033fc4384009ffb142000bfd8a10007fcc508022fe6284001feb142000bf58a10027f8c508022fc628400fffa942007ff94a1003ffaa50801ffc5284019ffa142000ff90a10007fa8508033fc4284001ff9942000ff8ca10007fa6508003fc32840177eb0c2007ffd461001ffca30801ffd5184007fe28c200cffd061001ffc8308003fd4184007fe20c2000ffcc61001ffc6308003fd3184007fe18c2000ffc861001ffc4308003fd2184007fe10c2003bf9821003ffea108013fe508400ffd2
  | 2 => 0x20007fa8710053fc43880277eb144011ffd4a20047fca510047fd5288011fe2944014ffd0a20047fc8510003fd4288011fe2144000ffcca20007de6510023fe3288001fe9944008ff0ca20007d86510013ff6188001ff30c4003bf98620007fac310002fd6188009fe30c4011ffd462008ffca310047fd5188023fe28c4014ffd0620007fc8310003fd4188029fe20c4000ffcc620007fc6310003fd3188001fe18c4008ffc8620007fc4310003fd2188011fe10c4008bf9822008ffea110013fe5088023fea844004ff142200a7fe8110013fe4088001fea044004ff10220007fe6110013fe3088001fe9844004ff0c220047fe4110003ef2088011fd9044013ffd952009dfeca9004ffe65480057f32a4013ff5952009dfaca9004ffc65480057e32a4000ffd9120005fec890003bf64480015fb224012ff9912000dfcc890003fd64480017eb224012ff1912000df8c890003bc64480035e3224013ffd5120097fca89004ffd5448025fe2a24000ffd8d20005fec690003df63480016fb1a4000ff98d2004dfcc690003fd63480017eb1a4000ff18d2004df8c690003dc63480016e31a4013ffd4d2009ffca69004ffd5348027fe29a4012ffd0d20007fc8690003fd4348025fe21a4013ffd4920047fca49004fee5248027fea924013fb54920047f8a49004bff4248011ff2124000ff50920047f88490003ff3248011ff1924000fb8c920007fa6490003ed3248011fe1924000ffd8520005fec290003fe6148001feb0a4000ff1852001df8c29004fff5148027ff28a4013ff5452009ff8a29004bff4148001ff20a4000ff50520097f88290003ff3148001ff18a4000ff4c520007f86290023ff2148001ff10a4000ff48520047f8429004fff5048027ff2824013ff5412009ff8a09004bff4048001ff2024000ff50120097f88090003ff3048001ff1824000ff4c120007f86090023ff2048011fd9024000ff88120007dc4090013ff65080117fb284008ff99420015fcca100237e65080053f3284008ff59420085faca100237d65080013eb284004ff19420045f8ca10013ff64080117fb204008ff9902000dfcc810023be64080035f3204008ff59020005fac810023bd64080015eb204004ff19020045f8c810043ff540801fff2a04010ff5502007ff8a810013ff63080117fb184008ff98c2004dfcc610023de63080016f3184008ff58c20005fac610023dd63080016eb184004ff18c20045f8c610043ff5308021ff2984010ff54c20087f8a61003fff4308001ff2184000ff50c2007ff88610022fe6208011ffa904008ff94820047faa410023fc5208011ffa104008ff90820047fa8410023fc4208011ff9904000fbcc820047fc6410023fd3208011fe1904008fb0c820027fec210023fe61080077f3084008fd98420005ecc21002
  | 3 => 0xfb286009ff99430015fcca180277e650c0053f3286009ff594300c5faca180277d650c0013eb286004ff1943004df8ca18013ff640c0137fb206009ff9903000dfcc818027be640c0035f3206009ff59030005fac818027bd640c0015eb206004ff1903004df8c818063ff540c02fff2a06018ff550300bff8a818026fe630c013ffa986009ff94c3004ffaa618027fc530c013ffa186009ff90c3004ffa8618027fc430c009ffb106009ff98830045fcc418027ee620c001773106009ff58830005fac418027ed620c00176b106004ff188300c7fea418063fe520c031fea906018ff148300bffe8418003fe420c001fea106017ff1083004ffe6418027fe320c001ef1906009ff4c83004ff86418027dc320c009ffb086009ff9843001dfcc218027f6610c0017b3086009ff58430005fac218027f5610c0017ab086004ff184300c7fea218063fe510c031fea886018ff144300bffe8218003fe410c001fea086017ff1043004ffe6218027fe310c013fe9886009ff0c430007fe4218003fe210c001fe9086000ff084300cdfcc018063ff500c009ff2806018ff54030027f8a01805fff400c009ff2006000ff50030027f88018027ff300c013ef9806004ff8c03004ff46018027fd300c001ee9806009fe4c030047fecb90022ff65c8011ff32e4002bf99720047facb9005afd65c8011fe32e4008bf19720047fec990022ff64c8011ff3264001bf99320047fac990002fd64c8011fe3264008bf193200b7fea990057fe54c802dfeaa64015ff15320047fec790022ff63c8011ff31e4009bf98f20047fac790002fd63c8011fe31e4008bf18f200b7fea79005bfe53c802dfea9e4016ff14f200affe8790003fe43c8001fea1e4015ff10f20047fea590023fe52c8011f72964008ff54b200b7daa590023fc52c8011ffa164008ff90b20047fa8590023fc42c8011ff9964008ff8cb20047dc6590023fd32c8001f69964008ff0cb20047fec390023fe61c80077f30e4008ff58720005fac390023fc61c802dffa8e4016ff947200b7faa39005bfc51c802bffa0e4000ff90720007fa8390057fc41c8001ff98e4000ff8c720007fa6390003fc31c8011ff90e4008ff88720047fa4390023fc21c802dffa864016ff943200b7faa19005bfc50c802bffa064000ff90320007fa8190057fc40c8001ff9864000ff8c320007fa6190003fc30c8009ffb2c4011bfd962008ffccb1000afe6588023feb2c4011bf59620027f8cb1000afc6588009ffb244000bfd92200a7fcc910006fe6488001feb244000bf59220027f8c910006fc6488023ffaa44014ff9522008ffaa910053fc5488009ffb1c4000bfd8e20007fcc710026fe6388001feb1c4000bf58e20027f8c710026fc6388023ffa9c4011ff94e2008ffaa710047fc5388029ffa1c4000ff90e
  | 4 => 0x27fc62cc03dffa96601eff94b300f7faa59807bfc52cc03bffa166000ff90b30007fa8598077fc42cc013ff9966009f7ccb3004ffc6598027fd32cc001ee9966009ff0cb3004ffec398027fe61cc0077f30e6009ff58730005fac398027fc61cc03dffa8e601eff947300f7faa39807bfc51cc03bffa0e6000ff90730007fa8398077fc41cc013ff98e6009ff8c73004ffa6398027fc31cc001ff90e6000ff88730007fa4398003fc21cc03dffa86601eff943300f7faa19807bfc50cc03bffa066000ff90330007fa8198077fc40cc009ffb2c6019bfd96300cffccb1800afe658c033feb2c6019bf59630027f8cb1800afc658c009ffb246000bfd92300e7fcc918006fe648c001feb246000bf59230027f8c918006fc648c033ffaa4601cff952300cffaa918073fc548c0377eb1c6019ffd4e3004ffca718067fd538c013fe29c601cffd0e3004ffc8718003fd438c013fe21c6004ffd8a30007fcc518022fe628c001feb146000bf58a30027f8c518067ff528c033ff2946019ff54a300cff8a518073ff428c001ff2146000ff50a300e7f88518027ff328c001ff1946000f78ca30007fa6518027fc328c001ee1946004ffd8630007fcc31800efe618c001feb0c6000bf58630027f8c318067ff518c033ff28c6019ff546300cff8a318073ff418c001ff20c6000ff506300e7f88318027ff318c001ff18c6000ff4c63004ff86318003ff218c001ff10c6000ff48630007f84318026fe608c033ffa846004ff942300cffaa118013fc508c039ffa046004ff90230007fa8118013fc408c013ff9846000f7cc23004ff6611806fff654c0377fb2a601bff99530015fcca9806ffd654c0377eb2a601bff19530015f8ca98003ff644c0017fb226000efd91300057ec89806bfe644c0037f3226000ff59130005fac89806bfc644c0037e3226000ef1913000d78c89806fff544c035ff2a2601bff551300d7f8a89806fff534c013ff29a601bf794d300dffaa69806fdd534c013fe29a601affd0d3004ffc8698003fd434c013fe21a6000ffd8930005fec498003ef624c00177b126000ff98930007fac498003fc624c0117e3126000fb18930005d8c49806fff524c037ff292601bff549300dff8a49806bff424c001ff2126000ff509300d7f88498027ff324c001ef9926000ff8c930007fa6498003dd324c013fe1926000ffd8530005fec298003fe614c001feb0a6000ff1853001df8c29806fff514c037ff28a601bff545300dff8a29806bff414c001ff20a6000ff505300d7f88298027ff314c001ff18a6000ff4c53004ff86298003ff214c001ff10a6000ff48530007f8429806fff504c037ff282601bff541300dff8a09806bff404c001ff2026000ff501300d7f88098027ff304c013fd9826000ff8c130007bc6098013ff650c0137
  | 5 => 0x842101ffec01080ffe60084017f3004203ff58021005fac01080ffc6008445ffa804222ff94021117faa01088bfc5008443ffa004221ff10021027fecb20082ff6590041ff32c8002bf99640107facb20082fd6590009fe32c8002bf1964000dfac920007ff5490003ff2a48001ff5524000ff8a920013ff6390001ff31c8009bf98e40007fac720002fd6390009fe31c8020ffd4e40107fca720083fd5390041fe29c8001ffd0e4000ffc8720003be4390003fea1c8001ff10e4000f788720013ff6290001ff3148008bf98a40007fac520002fd6290009fe3148020ffd4a40107fca520083fd5290041fe2948001ffd0a4000ffc8520003be4290003fea148001ff10a4000f788520003ff3290001ff1948000ff4ca40007f86520013ff6190001ff30c8003bf98640007ecc320002f66190001feb0c8000bf58640007eac320002f56190009fe30c8020ffd4640107fca320083fd5190041fe28c8001ffd064000f7e8320007fe4190003fea0c8000ef5064000ff88320003ff3190001ff18c8000ff4c640007f86320003ff2190001ff10c8000ff48640007f84320006fe6090041ffa848004ff94240107faa120013fc5090003ffa048001efd024000ff68120013fc4090003fc204801fffd95400fdfecaa007ffe65500057f32a801fff595400fdfacaa007ffc65500057e32a8001bfd914000ffea8a0007fe5450003df2a28001ff551400ff7aa8a0007fc5450001ffb1a8000bfd8d40007fcc6a0003fd6350001fe31a8009bf18d400fffea6a007ffe535003ffea9a801fff14d4000ffe86a0007bf4350003ff21a8001ff50d400077a86a0007fc4350001ffb128000bfd8940007fcc4a0003fd6250001fe3128008bf189400fffea4a007ffe525003ffea92801fff1494000ffe84a0007bf4250003ff2128001ff509400077a84a0007fc4250001ff9928000ff8c940007fa64a0003fc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8003bf185400fffea2a007ffe515003ffea8a801fff1454000ffe82a0007fe4150001df20a8001ff5054000ff882a0007bc4150001ff98a8000ff8c540007fa62a0003fc3150001ff90a8000ff88540007fa42a0003fc21500037fb02801fffd41400fffca0a007ffd505003ffe2828001ffd014000ff680a0007fe4050001df2028001ff1014000f7880a0007f84050013ffb2e6009bfd973004ffccb9800afe65cc013feb2e601ebf5973004ff8cb98026fc65cc013ffb266009bfd933004ffcc998006fe64cc013feb266000bf5933004ff8c998026fc64cc03dffaa6601dff953300f7faa998077fc54cc013ffa9e6009ff94f3004fbca798027fd53cc03deea9e6009ff14f3004ffe8798027fe43cc013fea1e6009ff10f3004ffec598027fe62cc0117f3166009ff58b30005fac598
  | 6 => 0x7ff3244201bf9922101ffac910802fd6488407fe3244203bf19221137fea910897fe548844dfeaa44225ff1522101ffec71080eff6388407ff31c4209bf98e2101ffac710802fd6388407fe31c4203bf18e21137fea71089bfe538844dfea9c4226ff14e2112ffe8710803fe4388401fea1c4225ff10e21125fac51089bff5288411ff2944226ff54a21047f8a510897ff4288411ff2144200ff50a21047f88510803ff3288411ff1944200ff4ca21047f8651080efe6188407ffa8c4203ff9462101ffaa31080ffc5188407ffa0c4203ff9062101ffa831080ffc4188407ff98c4203ff8c62101ffa631080ffc3188407ff90c4203fbc8621047ee431080fff6088407ff3044200bf9822101ffac110802fd6088407fe3044226ffd4221137fca11089bfd508844dfe2844225ffd022112ff88110893ff65484497fb2a4224ff99521015fcca90893fd65484497eb2a4224ff19521015f8ca90803ff64484017fb224200efd91210057ec89088ffe64484037f3224200ff59121005fac89088ffc64484037e3224200ef1912100d78c890893ff5448447ff2a24224ff5512111ff8a890803ff63484017fb1a4200ff98d2104dfcc690803fd63484017eb1a4200ff18d2104df8c690893ff5348449ff29a4224ff54d21127f8a69088fff4348401ff21a4200ff50d2111ff88690893ff5248411ff2924224fb94921127faa490893ed5248411fe2924223ffd0921047fc8490803fd4248411fe2124200ffcc921047fc6490803fd3248411fe1924224ffd452101ffca290893fd5148407fe28a4223ffd052101ffc8290803fd4148407fe20a4200ffcc52101ffc6290803fd3148407fe18a4208ffc8521047ee429080ffe2148407f710a4200ffd8121005fec090803fe6048401feb024200ff18121005f8c090893ff5048449ff2824224ff54121127f8a09088fff4048447fe2024203ffd942101dfeca1080ffe65084057f3284203ff59421115faca1080ffc65084077e3284203ffd902101dfec81080ffe64084037f3204203ef9902100d7cc81080ffd64084017eb204203ef590210057ac81080ffc64084077e3204222ffd502110ffca81088bfd5408443fe2a04203ffd8c2101dfec61080ffe63084137f3184203ff58c21005fac61080ffc63084077e3184222ffd4c21117fca61088bfd5308445fe2984221ffd0c21007fc8610803fd4308443fe2184208bf98821047fea410823fe5208411fea904208ff14821047fe8410823fe4208411fea104208ff10821047fe6410823fe3208411fe9904208ff0c82101dfcc21080fff5108407ff2884203ff5442101ff8a21080fff4108407ff2084203ff5042101ff8821080fff3108407ff1884203ff4c42101ff8621080fff2108407f79084203ff8842101fec421080ffd2108407f69084208fd4
  | 7 => 0x988b3fd544c457fe2a2622cffd4d3104ffca6988b3de534c459fea9a622cf754d3104ff8a6988afff434c413ff21a6200ff50d3104ff88698803ff624c4017fb126200ff98931007fac498803fc624c4117e312622cffd4931167fca4988b3fd524c459fe292622bffd0931007fc8498803fd424c457fe2126209ffcc931007fc6498803fd324c413fe192622cffd453101ffca2988b3fd514c407fe28a622bffd053101ffc8298803fd414c407fe20a6209ffcc53104fee629880ffe314c407ef18a6200ffd8131005fec098803fe604c401feb026200ff18131005f8c0988b3ff504c459ff282622cff54131167f8a0988afff404c457fe2026203ffd943101dfeca1880ffe650c4057f3286203ff59431155faca1880ffc650c4077e3286203ffd903101dfec81880ffe640c4037f3206203ef9903100d7cc81880ffd640c4017eb206203ef590310057ac81880ffc640c4077e320622affd503114ffca8188abfd540c453fe2a06209bf98c3104ffea618827fe530c413fea986209ff14c3104ffe8618827fe430c413fea186209ff10c3101ffec41880ffe620c4117f3106203ff58831005fac41880ffc620c455ffa90622aff94831157faa4188abfc520c453ffa106200ff90831007fa84188a7fc420c413ff9906209ff8c83104ffa6418827fc320c4077f3086203ffd443101ffca21880ffd510c407fe2886203ffd043101ffc821880ffd410c407fe2086203ffcc43101fbe621880ffe310c407fb1886203ff4c43101fba6218827f5310c407ffb006203ff98031005fcc01880ffd600c4017eb006203ff18031157fea0188abfe500c455fea80622aff1403114ffe80188a7fc400c411ffb2e4208bfd9721047fccb9080afe65c8411bf32e42029f99721047facb908a2fd65c8411beb2e42009f59721047f8cb90822fc65c8411ffb264208bfd9321047fcc990806fe64c8411feb264200bf59321047f8c990822fc64c8451ffaa64227ff95321147faa99089ffc54c8411ffb1e4208bfd8f21047fcc790826fe63c8411feb1e4200bf58f21047f8c790822fc63c8451ffa9e4228ff94f21147faa7908a3fc53c844fffa1e4200ff90f21007fa879089ffc43c8411ffa964208ff94b21047dca590823fd52c8451f6a964208ff14b21047fe8590823fe42c8411fea164208ff10b21047fe6590823fe32c8411fe9964208ff0cb21147fea39080ffe51c8451fea8e4203ff1472113ffe839080ffe41c8401fea0e4203ff10721007fe639080ffe31c8401fe98e4203ff0c721047fec190823fe60c84017f3064208ff58321005fac190823fc60c8451ffa864228ff94321147faa1908a3fc50c844fffa064227ff1032101ffecb1080eff6588407ff32c4202bf9962101ffacb1089afd6588407fe32c4203bf1962101ffec91080eff648840
  | 8 => 0xf18d4104df8c6a08c7ff5350463ff29a8231ff54d4118ff8a6a0807ff4350403dfa1a8201ff90d4100ffa86a0803bd4350403fe21a8200ffd8941005fec4a0803fe6250401feb128200ff18941045f8c4a08c7ff5250463ff2928231ff5494118ff8a4a0807ff4250403dfa128201ff9094100ffa84a0803bd4250403fe2128200ffcc941007fc64a0803fd3250401fe1928201bfd854118ffea2a080ffe5150463fea8a8203ff1454100ffe82a0807f74150407ff20a8203ef9054101ff882a080fbc4150403fa20a8200ffd8141005fec0a0803fe6050401feb028200ff18141005f8c0a08c7ff5050463ff2828231ff5414118ff8a0a0807ff4050403fe2028201ef1014104ffecb98826ff65cc413ff32e6202bf9973104efccb9880a7e65cc413feb2e6230bf5973104efacb988027d65cc413fe32e6209bf1973104ffec998826ff64cc413ff3266201bf9933104ffac998802fd64cc413fe3266209bf19331187fea9988bffe54cc461feaa6622fff1533104ffea798827fe53cc413ef29e6209ff54f31187baa798827fc53cc413ffa1e6209ff90f3104ffa8798827fc43cc413ffb166209ff98b31045fcc598827fd62cc4017eb166209ff18b31187fea5988c3fe52cc461fea966230ff14b3117ffe8598803fe42cc401fea16622fff10b3104ffe6598827fe32cc413fe9966209ff0cb31187fea39880ffe51cc461fea8e6203ff1473117ffe839880ffe41cc401fea0e6203ff1073104ffec198827fe60cc4017f3066209ff58331005fac198827fc60cc461ffa866230ff94331187faa1988c3fc50cc45fffa06622fff1033101ffecb1880eff658c407ff32c6202bf9963101ffacb188bafd658c407fe32c6203bf1963101ffec91880eff648c407ff3246201bf9923101ffac918802fd648c407fe3246203bf19231177fea9188b7fe548c45dfeaa4622dff15231165fac7188bbff538c413ff29c622eff54e3104ff8a7188b7ff438c413ff21c6200ff50e3104ff8871880fff628c407ff3146208bf98a3101ffac518802fd628c407fe314622effd4a31177fca5188bbfd528c45dfe294622dffd0a31007fc8518803fd428c45bfe2146209ffcca31007fc6518803fd328c413fe1946203bf9863101ffea31880ffe518c407fea8c6203ff1463101ffe831880ffe418c407fea0c6203ff1063101ffe631880fdf318c413fb98c6203ffd823101ffcc118802fe608c407feb046200bf5823101ff8c1188bbff508c45dff284622eff54231177f8a1188b7ff408c45bfe204622cffd9531165feca988b3fe654c4057f32a622cff59531165faca988b3fc654c4057e32a6200ffd9131005fec898803bf644c4015fb22622bff9913100dfcc898803fd644c4017eb22622bff1913100df8c898803bc644c4035e322622cffd513115ffca8
  | 9 => 0x801feb226400bf591321aff8c899006fc644c86dffaa26435ff951321b7faa8990d7fc544c86dffa9a6409ff94d321b7faa699027fc534c86bffa1a6409ff90d32007fa8699027fc434c86dffa926408ff949321b7faa499023fc524c86bffa126408ff90932007fa8499023fc424c813ff9926409fbcc932047fc6499023de324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6403bf185321b7fea2990dbfe514c86dfea8a6436ff145321affe82990d7fc414c801ffb026400bfd8132007fcc099003fd604c801fe3026400bf181321b7fea0990dbfe504c86dfea826436ff141321affe80990d7fc404c811ffb286408bfd9432047fcca1900afe650c811bf32864029f99432047faca190d2fd650c811beb2864009f59432047f8ca19022fc650c811ffb206408bfd9032047fcc819006fe640c811feb206400bf59032047f8c819022fc640c869ffaa06433ff950321a7faa8190cffc540c8137f3186409ffd4c3204ffca619027de530c813fea986434f754c3204ff8a619027ff430c813ff2186409ff50c3204ff88619022fe620c811ffa906408ff94832047dca419023fd520c869f6a906408ff14832047fe8419023fe420c811fea106408ff10832047fe6419023df320c811ff1906408fb8c832047fa6419023dd320c813f69906400f34c832047fec219023fe610c8077f3086408ff58432005fac219023fc610c869ffa886434ff944321a7faa2190d3fc510c867ffa086433ff10432047fec019023fe600c8017f3006408ff58032005fac019023fc600c869ffa806434ff940321a7faa0190d3fc500c867ffa006433ff1003201ffecb2080eff6590407ff32c8202bf9964101ffacb208cafd6590407fe32c8203bf1964100dfac920807ff5490403ff2a48201ff5524100ff8a92080fff6390407ff31c8209bf98e4101ffac720802fd6390407fe31c8232ffd4e41197fca7208cbfd5390465fe29c8201ffd0e4100ffc8720803be4390403fea1c8201ff10e4100f78872080fff6290407ff3148208bf98a4101ffac520802fd6290407fe3148232ffd4a41197fca5208cbfd5290465fe2948201ffd0a4100ffc8520803be4290403fea148201ff10a4100f788520803ff3290401ff1948200ff4ca41007f8652080efe6190407ffa8c8203ff9464101ffaa32080ffc5190407ffa0c8203efd064100fee832080ffc4190407fa20c8203ffd824101ffcc120802fe6090407feb048200bf5824101ff8c1208cbff5090465ff2848232ff54241197f8a120807ff4090403dfa048201ff1024118ffecaa08c6ff6550463ff32a8202bf9954118ffacaa08c6fd6550463fe32a8202bf1954101dfec8a0807ff5450403ff2a28201ef9514100ffaa8a08c7bd5450403fe2a28200ffd8d41005fec6a0803fe6350401feb1a8200f
  | 10 => 0xa1210f3fd5090879fe2848401ffd024200ff88121007bc4090877ffb2a843bbfd95421dffccaa100afe6550877feb2a843bbf595421dff8caa100afc65508117fb228401ffd514200ffca8a1007fd5450803fe2a28400ffd8d42005fec6a1003fe6350801feb1a8400ff18d4204df8c6a10efff5350877ff29a843bff54d421dff8a6a1007ff4350803ff21a8400ef90d4200ffa86a1007fc4350803de21a8401bfd89421dffea4a1023fe5250877fea928408ff1494200ffe84a1007ef4250811ff2128408ef90942047f884a1023bc4250803f62128400ffd8542005fec2a1003fe6150801feb0a8400ff1854201df8c2a10efff5150877ff28a843bff545421dff8a2a1007ff4150803dfa0a8401ff10542007fec0a1002ff6050801ff3028400ff58142007f8c0a1002fc6050877ffa82843bff941421dffaa0a10effc5050803ffa028401efd014200ff880a1027ff65cc8137fb2e6409ff99732015fccb99027fd65cc8757eb2e6409ff1973204df8cb99027ff64cc8137fb266409ff9933200dfcc999027be64cc8035f3266409ff59332005fac999027bd64cc8015eb266409ff1933204df8c9990ebff54cc873ff2a6643aff553321cff8a999027ff53cc813ff29e6409ff54f3204ff8a799027ff43cc813ff21e6409ff50f3204ff887990ebff52cc811ff296643afb94b321d7faa5990ebed52cc811fe2966439ffd0b32047fc8599003fd42cc811fe2166409ffd873204ffcc39900efe61cc813feb0e6400bf5873204ff8c3990ebff51cc875ff28e643aff547321d7f8a3990e7ff41cc873fe20e6409ffd833204ffcc199002fe60cc813feb066400bf5833204ff8c1990ebff50cc875ff286643aff543321d7f8a1990e7ff40cc873fe2066408ffd9632045fecb19023fe658c8057f32c6408ff596321c5facb19023fc658c8117e32c6408ffd9232045fec919023fe648c8037f3246408ef9923200d7cc919023fd648c8017eb246408ef592320057ac919023fc648c8117e3246438ffd52321bffca9190e3fd548c86ffe2a46436bf58e321c7fea719027fe538c871ef29c6438ff54e321c7baa719027fc538c86fffa1c6409ff90e32007fa8719027fc438c8117f3146408ffd4a32047fca519023fd528c811fe2946408ffd0a32047fc8519023fd428c811fe2146408ffcca32047be6519027ef328c811ffb0c6408ff9863201dfcc319023fd618c8017eb0c6408ff186321c7fea3190e3fe518c871fea8c6438ff146321bffe83190dffc418c811ffb046408ff98232005fcc119023fd608c8017eb046408ff182321c7fea1190e3fe508c871fea846438ff142321bffe81190dffc408c86dffb2a6436bfd95321b7fcca9900afe654c86dfeb2a6436bf595321b7f8ca9900afc654c801ffb226400bfd91321affcc899006fe644c
  | 11 => 0x20004008005002800000a0000068020000000002800001c000004000c002001000000000000100080040000000030004000001000800401000200080000020000058000008000000801400200200080040080010030000000001001001000e002002800400000000000000020050068000000002000000001a00600080040040000000000002001000800000a007000000800409ffd964304dfecb21827fe6590c057f32c8609ff596431f5facb21827fc6590c137e32c8601bf5924300ffea921807fe5490c03df2a48601ff552431f77aa921807fc5490c137f31c8609ffd4e4304ffca721827fd5390c13fe29c8609ffd0e4304f7e8721807df4390c13fe21c8609f710e4304ffec521827fe6290c117f3148609ff58a43005fac521827fc6290c7dffa94863eff94a431f7faa5218fbfc5290c03ffa148601efd0a4300ff88521827ff6190c13ff30c8603bf9864304ffac321802fd6190c13fe30c863effd46431f7fca3218fbfd5190c7dfe28c8601ffd064300ff88321807bc4190c13ffb048609ff98243005fcc121827fd6090c017eb048609ff182431f7fea1218fbfe5090c7dfea84863eff1424300ffe8121807fc4090c03de204863dffd95431edfecaa18f7fe6550c057f32a863dff595431edfacaa18f7fc6550c057e32a8609bfd914300ffea8a1807fe5450c03feaa28601ff1514300dfec6a18f7ff5350c13ff29a863dff54d4304ff8a6a1807ff4350c03efa1a8609ff90d4304f7c86a1827fc4350c13de21a8601f710d43007fec4a1802ff6250c01ff3128600ff58943007f8c4a1822fc6250c7bffa92863dff949431effaa4a18f7fc5250c03ffa128601ff1094300f7884a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c077e30a863dffd45431effca2a18f7fd5150c7bfe28a8601ffd054300f7e82a1807fc4150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028600bf181431effea0a18f7fe5050c7bfea82863dff1414300ffe80a1807bf4050c03fe2028608ffd9642045fecb21023fe65908057f32c8408ff596421e5facb21023fc65908117e32c8401bf5924200ffea921007fe5490803df2a48401ff552421e77aa921007fc5490811ffb1c8408ff98e4204dfcc721023fd63908017eb1c8408ff18e421e7fea7210f3fe5390879fea9c843cff14e4200ffe8721007bf4390803ff21c8401ff50e420077a8721007fc43908117f3148408ffd4a42047fca521023fd5290811fe2948408ffd0a420477e8521007ef4290811fe2148408fb10a42047fec321023fe61908077f30c8408ff58642005fac321023fc6190879ffa8c843cff946421e7faa3210f3fc5190803ffa0c8401ff1064200f788321023ff6090811ff3048400bf98242047fac121002fd6090811fe304843cffd42421e7fc
  | 12 => 0x20000010000002000000000403400300000040040000010014002002000000000600100000040000060018000008000000000c018001000800400200a0010000020004001000000400a000000400200700280040040030010004000000000801800200000080040020000028004004000003000000e007002000400a0000030000000005001800800200400100040000020008018002000001002400000800000080000000028018000000000000800000a002000400a0010000010000000000000400a0000030000000000000000c000002009000000000000080000020000000010006000002800c000000000003001c003000001400c000002800001400500000000000060008020006006000802800000c00080380060000030004018001000001c012000001801c0120000000000002002001000400600c000000000800200600040000010028004006000000802c000004004001400000400000480000060008048008000000801c0060000000004004001000800800000000180340260050000028000000003000400000000000000060020008000000000001002c00000000180080020020000000002007001000400400000000040020000018010004000000800800000500280000000030008008000017000000c000000002800000400600100440020000000000002004000000800600e00000000000000000034000008002800c00a0000088008034004000000000200000180040020010010008004000000000c0000040010004000001002000000e002000000000000000200000000060000004000001000000400000000780040000020028004004000001001c000006000000800000a0008008014000001000000e00100180000000020008014000006000000c00000200080080020020028004000003000001c00000100000000000050000004002004000000c00a000000801400400100000000000030040000000002003002c000001000800001a010000000400800000000000020000028000002008004800800200000100340000000010028004003001000401a004000001800200500000100040010028014002000000000400e0010000014004000001000800800500200080020000028000000000001000800200600280200080010050000002001000000400a003002000001200400000000020000020010004008000000000800100080040000000030008002006000003400000300000040000020010010004003000001000000000800540000200000000010005003001800000000000000040020010008000002000000400000300880000000000010004002000000000800a00000280040040040010000000002009000801c000001000400000000100400000030010010000006001000800000c00000080160000
  | 13 => 0x28d86b47fe000235c2300000000000384a0e1fa19a000009f4a38d0c00065c00015a400000041880010b201802d00000000004ad0ef0000713000000000044b0001ab800004c3b4841c0007974f600005e61fa09d91d4000912336800000048300004a495a7541da800000000002b138400033e40b0000f940ae2fd00000e40000e6800129c0000051c6532c8804cf9d886e6000275000135e5f04f100000000002c180d400000011d8000000000000000104200008980011b200000008c46c06371aa217cfca2f806925e874650141b9760a30057000000020898d36580000002ab35f9d440009980001d28000932332a3fcd4e1dd2409dac000a2c4f887004e40004bd89340006a30848218a1a78f000000000000039998c906000038812ac00093d1bc277c00044d1b3800000089500000000001a43478000f2271f48a08f4f1a65404d9b48000000423064874e00000025a000000000000000006400000c200008a5247000139200045e93f43cc00000003913cc000000028877614c1ac000000000000014c07700002238000000000000276068a000000209937200038181ec0008cc0000d9066400000000000006101ec16a907a5481b58a8c0000000d98e1c00055f0000000000000033000118616922d26300003b100002d4b720d50bda475044000294000127e877000000000058111183d448a4c640a9f540000000000000032484000000000090b43ca28400027b50485b800000050a0000a2e6440780b8800000000002900006ac36a082000000000000000006bb31d13080006aa0000a84000370000000124e0000000b1000048a0002604000000000000079c5c6353171c0000000b1800000000030b95e09b6000459a2042bc508000000000000000000000000001eb12c08c00000d30000d9e0004330e2874a9210002370ad006900004144a427322786140007a600000000000000000000000a032ae000000091720b80000000d9000000000013400000010202000531b8400000015416f83ea81b07328b8000000000042c0000000000660ea600008e00000000000000c6000000080000000010000000008005006800400200100b0004000004003800400a001001001000000000000000040000000000000004003800000e001000000001200200000000000010050010000001000801000000600100040000070010000000001001802001200100180040040000000004004000000003c0000020000000000002000000000000300000000000000000018000002000000000200100000040060010048024002002001801400000100380240040040010008000000000000c00a0010038010000003001000800200000080040000080008000016001000000c010000000000400000e0000000002000002800400c0000000000
  | 14 => 0xb949364fa0001a60a408640000000a123cc00000001340000000000ada0001da0000b2600049a80b4d6e7d700000000000000001ed4a3a1fe2a980005541801d580000007550000000000000000172c1c200030680554664ac20900005c05f329626e8d1400000028a12c200000000000000001039bd0000000253800000000013e800063259a000000070c982000000028400000000009523000001e8c00000000000000008670001de40002ee0000a240000d1000000025e1d628600008120004e080007c600003b05f050a0004bf00000000001d600000000000568000ee40000001960d7c0004e60000b0000000000006f40003d482d8e220072aba88c3b20001cf16fc0009db000000054400000000002d60003090c191de54d14a1a74f7000000000000004da00000009007f0000000088600000000007240000001d900000000001b64000240000000000031729a822c0000003ec216c0009010001cd4fa62f22618000000000000000113a0004c980013969782ce1a503c20000001fe4f3e2e8143843cb0a132012192125a66c20090a10a63e6397800069494915000000000004bc96b40004f600000a83700000000000f604910000df800000000000000000002f205b400000051113a04de00000019592540002cb9f6814200000000000000004240eb498a0000000920ef04661f5186043a7211c411a8eea0002a18000f263b7000000055200000007dd3680e2275a61452a0002d281dcde400001a0000d2200005c17100000001d417b05ae000000050c0000000000000edc0004e9800000068c00026a066e3f600019e07ca00000010980004e913f000000022c4bb80012ec00000000000000004b9800000000047c80000000002229344000a3800000009047fc034000038c0000001370fcc07e25f84d4000128376a3c0a1c38042d12541b67340a7000000067c42b26752b056c28e0564346a24000258c0000000000cb8ca40000000000baa00000b17447ce0002d4800000000000000000000003fa85540001122118afc0008b800000000000002cf80000003fd4279cac7bc050341051c00000033b1f2000000002380013e600000016b03e880b2f700000000003b307b44ae2b91388f2c0000004568d0400000000000001d6000000000111c00000008b89a64980000000000000000000000000000000947b49b23ce09041886b54b31ce8c060001828000c5c87600000000000000001d5ccf278609c97a4dec83a31102e93362630a50000000000000000000000000000000000002a8051800000000027744520000b7800000000000000000009a24718000c8c52d1f81a200000002fb1c8c71835144425181c600000018d487884c2640000eb800038788dcab00002fea03c00049623d86c80009090000be819e7c900001e4000
  | 15 => 0x405e26b80011c05e71bc8ccc0005dc4a5800000097c0000000ff63ee31223ccc7c284371a74116c3034ca118844a1f94478854f2833537e917d436152491a8ed4560aa42e1cd81ec00046d800068c00000000000000001938000cde46f00000000000000e4a5f52782c01b2a8190260000000000ae809e06f1e40fbe00036a80000000000000000bbc4580010000ee243239600010a0000000000000047045200012364b70c9a57cd0a000000123495032b0000000000000000000042e2ad1ec800000090d2f68bd12da5240e198f0f0e0000000000d0066e1f2207c00000000000003180002070d8861a01032d98802e622d33a800000000031380000008af19da6d80006600000000b6e00019304f8ed05760e896ed3168912e6800019c9ce0001564000000000000000000013000000002be0001ba54809bf3730000708000429254441600039721e0000000315800134829d11300012828874601140000131000000086a73b3058000000000141a40899e000000199d2320002909aa0ebe4c1000222c0001451eda5d0dbe9c419416c80123d133a1da8c606a434c9df929e8f40002844eb60002349a414720ed1a710fcc4c0000000000a0e83b1ca90e40000003e78d0800000044c0754e1a95025783ccba60004831be400096b00013600000004a628f00f01cb0001d3c0000000002350a620000000000f864bb1e0a69d2600003c223d503a00000000012d8000000111000031b04980000004340001068000000000000000000000000000000004218000e387525108000c5000000000001fa54133481d40000003b60e34e9200000000000888353d99eb8dae71743805c800063600021a0d5e6c442000000b2000000000000077444e12f493c4b215c27ecbcc00000000000000b70002044f100001308000000000025800092843644987100008b72bc80003d43e823f8b500005490001fa04400000002414c344410000604d900554cd00000000000000000000000000113075c00000023900003851b50739226a0727185010704e2307019400000000000001be0003810000000000000209400000000000008260003e68810d9a9ca00026445c674b37da54877a73036128dc51a00021521540008c108c8000bfc00000023ec000000000197800000000000003f80000ec1ec4b5e40d0cf00004dc00000022314241eb43da6c000000000000000007cc3de8ec87f041f33d24e14742501a5a3d800000004483b8000000424936400000000001e800000000000013ae000000000000054b00000000001b90001b1412000000000008322091ff80000007dc4c014640002f700011c8000000061800021c69e0000000e4a8272639c100000000000000da600005c9240fee61518926a400000000000000006f00a6800000025d0cb0000000546000
  | 16 => 0x50f140000000000000000000000232800028e000186400066226a00000003e0156000136e1fd000066837c00029f00000000001b60ba8ef8625166a06000000000000000006430630c70fb600045880001580000001b0c000000048800094617700000000008711879954000000434977c00098f00020340005b30001eec0008f20000000a7254421480000000000bc8000e0e2d100002950c076d10c046d1f44333680098fa260826518e521c0622eb0a7c8bc9202c4927071e000000000000079e00005d0504281000000033e5a30b204fcc0a09d0001ff473696a00023e000000000000000006cc0700b7000061b0000b304444b100026f4f7e0000000928520a16000056800000000000001ae5f800014ec0007083a700b800000000000000000000000000b94916000200ce503e922984f000023900000000004030ff800000054a0001714000000000000074c50340201d136642b4fa82a432e572272980400000014500000006c043117bd1468fc1949c3800000004c0b3800000000021a80003c900013d0d6c81737f859d3de19d000000045e526000096872e5c20db8000b4292b02a00005c82983e11630dca3e100000001a000026800000004b600000000000002de800007800000000000000000000d7000012e000129424400000005d84a6808000000000067b28027e440a00049400013bc00000011b05844140000e080608652c8090c2f0356000000000000016e98a43c0000000000067a6041ba80000008df4ff0000000000326800000056628a000135a00000000000003be47680000000c0000092400000000010290e48ac00000000006b851824e45382554051654b1602b0000d102a000037b92f07a4141086a684f0064f2fa0a4886e5da43e99280000003d100000000000ab80007200000001eb00000004ff80009aa692515255c46a9f4109800007e00000019080089d534f9e60ffe4550000000eaca170001e9c62800035e26b06ee000000000128000000000000003c228d00008c606e0000000b1a000000000110a000000000062000000000002cc9240b082c881800000027a8d2a000000000000019531c00008b81b40f99fb40000001ad966c000000000000084800000000009cc000045247c51670a12e15dc00000051a80000002a500009c00000000000000be28cb0000000bba00041e13300003e21c180000005670219e486da2163f99e7431a3242bda8fc4667122270d48ab61c70000d3c0646c64f5819c0003f10001de8f88000198245400000036e00000000000000000c3c000000000132e000270178424669700004f4000a0d000000095400000023b800064e0000aec7e400044100004345021ea80013c00003b79b7531474400026c40006ea0000fe82fa26900000000008cd2b78dc80000000000000fd
  | 17 => 0x260002cc24c453c00000017505ec00032c8000000000386000113c03b3b99e940002c31be000101800028f000115c000000165046c96e4da900800000000005c0000a0c4fb000023e0000000000000000000000000000000000012c067d00001bc258000000057c00000000000000000000001990e8400044b0c88b0895b0002110d068c238ea68c92e0000000000c54000000000000000000000000001cc0d68000c040002648314e0a00041416084060ab32480000005f7000000109c6c11ae80004ca47a0000ce142612400000010a80ef12c15e80000000000000ce03c6000000000000011c14f07ba8ce0001a34f9c58a000195cd4235f0d890e0b5000000026b93f07eb00000006a624200b80000007f645480000005c30000000a565fc50c105420600003697640000003ac1acd2ca00000001280009a61dfa6641ee7f100024b838270b4f70000000562080a60c4242cf44a1d7435859e0000000184000000194000000013500000c80000001af47d8000000000000000000000000000001dd0000aaa46b2339d0062247800010c000000047480000000000f415f0d1c0001d4a618cd600000017a800086c43f8000c7e0003f196e85fa22a1030d54db40003b3800026ea270061c508c892500194bce8a8d020d979466231335006b92d28323ef0d8ca987e932980000000000000bc000082b1310000b5672610f2574d8e000000000128471a41fa03918e2280e400008b29c82892874000000288077000000019199f81f215100000009e012d00009a12386db000250d0965c800000005ac3df25c908000000002e80e85cc73e0000000f3200015999040003ef00027503423ca000004400000000021340001303920004b988c50001d353108d800000006de0004101f901e80004c7264862c398000176d0fc1e9092958400000004697e44149e30300af017e33f1270a90ef67e00000e743e00000000000474000448085065e45b2af20bcb1c82308d08f82106eb00000000000000002478ce20f1323a8640000003bf8e58d603d3000000000000000014dcaa2000478a70c0000000000bf0eb200024900006e840604a0000000000475000000087400027c12666e04d00ac506c4311181738b688293771c1801e6110b8a3780000000001d412de1d728d80e0c468f732e932cf0a63346900010ba1753dd00003f639f0b280005d80061650ad4b4e7370588000000970000083094056b18d000000062f1c0a8bcce40000000c2d3ce10c464037448c00000000000000000000c9476c00050f80001f673c1ab94544fe22430b0da00000000000000000715419912400025118200000007d900016740b80002a720500006e24e294e80000000000000f420000000000f1200021ea61034a2da455a76528800027c23180003f504b19dc0009c048
  | 18 => 0x9a0a980007270000000000000000141800000045d04d837aa0427703680005042088000cc252200002648e220f000000010432d0001ef80000002b180000a400000000000006f1000000000061d0000e80000452018800000073f0000a5815e2750000000c1e900164261c8200003558000d929aa4fe1aa449e30236f21cc0006ce328818c3104e72a902200002d825302304041a22448bf80000004cf16c4d4a00023b226c07218b006a2889880004f417fc85a3cf00000000000000000f1d0dc00000000000000000000000dfc8fe0000000f04a08316800022a0002e000000000810479f040007ad00000008ca48f27c8bb5252000000000000005f000000064004d0001b6124c00000026ec000000000240c0000003ca800000000030a00002408070001a6c00000000000000002932b989e08765540000e8800082a2c7a62461848822000010ea49a0000000000000000239400000048400f42fe738000001400000000e04ac574000000000010800000000000003d400001180005ae475800000000000000009ac60c3be800000027c0aa00dca6c0001ce000000000004a8bbc0000000001cf40006ba49d9bd456487c12f1058a3e0000fb14b835e0c1000122c000000000000000002800013f06926b10000000aea0000000000b0c0000000ecc0006ec13ba558510777069800087c34c0388000000000000056c0001df21728f49422101e0000056e2c94f480000000000de0000b6a3930f906280001e402d8000ad48842a3800030e00050a80000006ca41693d40663fb1d7807c00000025c1e9000033922113c88382fb3f61f508fa54211f874c000000000000000000032f969000000037d0f700000000000000f5427915e800023c3aa000000141650b16d800000000000000001b02e1158000077261301181840000be50d2160a54000000000000000014783200000000001cc86743a40e521845aa2b400025140002df000000000000000023982fc000000000000000044f80000000001908000f6c0000aea29c84a00000017802420294e68078d0c91029289b00008ec000000000024700022c8000000000226880819b2d314e000000010c9884a1e000335155800070940ca7940002f94450000000000394800129a0000000000ce60000000000e8c1580df80001ac000501000000000000004088e64fe0000000582000000000000000044926acff41e34dc0000000809431a73cf7286b0100b2cfce2f108016208e800000000000003f300005b00000003cb000019a78a28980007d618610880000006fc000000005e000278a8f800057f00006a87ee7813e901a8c0c0002b00c24a4e1cf00012e8ec093600000000009be000000000084200000000000000000b9c0000001258ca885e0000000000bea0000000000e9805300002c00
  | 19 => 0x8f225651680011789fa2e496800360000000b4c7fc10a000000000000000000011a207300008acf8a5cf00000003604613da0a1907218e1b88f3462a000417000024c2d90f100000000002d125fc4b692200008340000000001d6829600000009ad21e8a850f0000b8227600004412c80000000fe41f447e0070a6c0587d600000013b861f32d2654000000000057000069c0000000000000000000000000000014440003761e200000000000002718000a264af0000000a00000009d3ac30e3b091508160003f700008ee0000d403511ba68947387e11c200023404e800080100000000002c63d4000000078b2de1fd00000002dc00003280001a000000000002bf00000000ff497879406c8340001c580009550000000000a324a50000fba8860000d8400011618ea35800026d000000000000046a9a10b6c00002c1ba0000000000000010a6813a3800000000000028700000000e8000000092c400178856c0122240000d440000c813b108a5873db9c7800000042f28a4bd05922078074d2c0cc02104183ce46d10d83940000000000f4000063422b90009de5053498f206fa000000148cc9648c05a1d8cd6890411380000000004500000194000000000000000000000003329900001870fe40000000000000000000000046400000000000000a721100013a234d1b717c800000000007b800000000000000009484ba8d412741d2469912898075e210a25c24e6ef3f100000000000ed8000ae200011a244400000038015b800000034d00000280004ac80011fa42c000097c2228124e10000d1609722b000103445d25a1c811d0a203b809e865800029903f117e84707400000004081bd800000000000006a40000000000000d5a78e0000000e869e10000cf127c9370000cd0000000000000073400024f80011725d03f7a7900006f303598283de4a442084cd4200000659e30e5481e19b0a9c0000ec38d80011320001638000000000000000000019c000101c00020e000181d0f4000000000000000000000000003661eb8000f7800014d07150a25651a384501665d237c0e5060272d31602f499c5b03bb093018e6d1079175c3127c6000039cf403694ce1d941781b500022a80003b02f198c4000000000271c00000000013dc00000035c8000000000000000000000009c22f91120210000a440fa0a325f0870c766e40000000f8e00000000000009f729e90e836c00000000000000000000000000307467800000090700022c0092000000283c00000031e9118e8200000004a89440e90000c7800000000000004cc00044680013a44ae4368680f365161e1877809c000243215c0007314d280000002d0425087c1f08b4000000100c8830002460e440001af20703560000000e44fa000000007500002af228810400000048d000000082c2
  | 20 => 0x34828519300000001c700000000000000000000022000000000053f0001ebc000000000000000017a299a76852e570000000000007c25980000008c400022d40001680dd951400066600012640004ff20e87c49bc00045300000000001cc9334f0600006498243d85fb1c480000000000000000000a0500000005a400000025c828816a000000030680500000000006e73590370478599000000000000027201b003448520f0990dac00016f0000000000000153c000087000259c0000a011086e800057d0000248000000500a2ec010162028a82800000020c0000c002e9000013c00029900000012a600012c8e2c0009f20470000000000000000000000000013cc0007b226ea1bc7da000202863c10042700024d0e9095c175a7f43080000000000742000000000000049d276a8953da00000000f800000000025500000000000c7d00400000009d00000000000000000000000124c00055a0b000002920000000d6434e5293d58bd400000000000007f80000000dfc00079a07f000000066346480000002ae000000000000000000009be0002b201c000008300000000000000001fe0000739000002c0000003e0054c0fe14f13382ec09011d0750a301504fb00019fd2e2000162a3888dc2544121574fc2701000000000000000000001387180000100000000100a0f93780002a011f050024451896443047cb000000000000017fa368000156000191546800002285203b44d22438c280001174b1165896a00000000000000000000000d0e5eb000000121819100000000000000000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc725901002ebf425901001cff715901001cfe715901001cfd715901001cfc715901001ebe415901001ebc415901000cff7059010024fe705901000cfd7059010024fc7059010026be4059010026bc4059010004ff7558c10014fe7558c10004fd7558c10014fc7558c10004ff7458c10006bf7458c10004bf7458c1000cfe7458c1000cfc7458c10006bc7458c1000cbc7458c10024ff7358c10026df7358c10006de5358c10006dd5358c10004ff7258c10044fc7258c1001cff7158c1001cfe7158c1001cfd7158c1001cfc7158c1001ede3158c1001edc3158c1004cff7058c10024fe7058c1004cfd7058c10024fc7058c10026de3058c10026dc3058c1001ef71058c1004cff7690c10024fe7690c10004fd7690c10024fc7690c1020ebf6490c1000ebc6490c1004ede6390c10006dd6390c10004ff7650c10024fe7650c10004fd7650c10024fc7650c1000ebe6450c10006bd6450c1004ede6350c10006dd6350c10004ff7558810014fe7558810004fd7558810014fc7558810004ff7458810006bf7458810004bf745881000cfe745881000cfc7458810006bc745881000cbc7458810004ff735881004cfc7358810024ff7258810026ef7258810006ee5258810006ed525881001cff715881001cfe715881001cfd715881001cfc715881001eee215881001eec2158810044ff7058810024fe7058810044fd7058810024fc7058810026ee2058810026ec205881001ef71058810044ff7690810024fe7690810004fd7690810024fc7690810206bf649081000ebc6490810046ee6290810006ed6290810004ff7650810024fe7650810004fd7650810024fc765081000ebe6450810006bd6450810046ee6250810006ed625081004cff76cc810024fe76cc810004fd76cc810024fc76cc81002dbe74cc810005bd74cc81004ede63cc810006dd63cc810044ff768c810024fe768c810004fd768c810024fc768c81002dbe748c810005bd748c810046ee628c810006ed628c810004ff764c810024fe764c810004fd764c810024fc764c81004ede634c810006dd634c810046ee624c810006ed624c810044ff760c810024fe760c810004fd760c810024fc760c8100357e750c8100057d750c810007cd320c810064ff7650010026bf6450010026bc6450010004fd76cc010004ff764c010005bf744c01002dbc744c010005ef724c010005ec724c010004fd76c8010004ff7648010005bf744801002dbc7448010005df7348010005dc7348010025f77644010006f77644010004f776440100077775440101ff747544010026f765440101fef56544010056f66444010026f46444010026f76344010006f56344010026f76244010006f56244010025f7704401001ff37044010026f66044010027f26044010027f250440101fff15044010
  | 1 => 0x8510046f46288510025f6708851001ef7608851001ff36088510237f25088510237f15088510044fc76485100067f65485101267c6548510005bf7448510055bc7448510006ef6248510046ec6248510005fb7048510005f87048510046f47648510044f4764851022df7754851022df57548510007776548510227746548510007b77448510055f67448510055f47448510007b47448510055b47448510005f77348510005f5734851001df7724851001fe77248510007e76248510046f66248510046f46248510007e46248510227e65248510227e55248510007f37048510025f47048510007f0704851001ef7604851001ff36048510227f25048510227f1504851006cfe76901100067f65901101067c659011000ebe6490110006bd649011001df67190110055f57190110057b7419011000cff7650110054fd765011001cfc76501100067f65501100fe7c6550110006bf645011000ebc6450110005f7715011001df47150110057b4415011001cfe76cc11001cfc76cc1100067f65cc1100f67c65cc110006df63cc11004edc63cc11001df671cc110005f571cc110004fe768c1100067f658c1100ce7c658c11004cff764c110004fd764c11001cfc764c1100067f654c1100de7c654c110005bf744c110055bc744c110006df634c11004edc634c110005ef724c110005ec724c110005f7714c11001df4714c110004fe760c11005d7e750c1100057d750c1100067f650c1100c67c650c110055be740c110005bd740c110005ee720c110005ed720c11001df6710c110005f5710c11001cfe76c811001cfc76c81100067f65c81100b67c65c8110006ef62c8110046ec62c811001df671c8110005f571c8110004fe76881100067f658811008e7c6588110044ff7648110004fd764811001cfc76481100067f654811009e7c6548110005bf7448110055bc7448110005df7348110005dc7348110006ef6248110046ec6248110005f7714811001df47148110004fe760811005d7e75081100057d75081100067f65081100867c6508110055be7408110005bd7408110005de7308110005dd730811001df67108110005f571081100067f658411003e7c6584110055be7484110005bd748411001dfa708411001efb608411001df67684110026f6768411001cf67684110025f7758411021df57584110007776584110217746584110055f67484110027b67484110055b67484110027b57484110025f47484110025f77384110005f57384110025f77284110005f57284110025f67084110026f7608411001ff36084110027f25084110217f15084110004ff7559010014fe7559010004fd7559010014fc7559010024ff7459010026bf745901002ebe5459010006bd5459010004ff735901004cfc735901002ebf4359010004ff7259010044f
  | 2 => 0x6fb7058910004fe76189100067f65189100067c6518910055be7418910005bd7418910046ee6218910006ed6218910044ff7690910004fe7690910004fd7690910044fc76909100067f65909101e67c6590910006bf649091000ebc649091001df67190910005f57190910057b44190910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101de7c655091000ebe6450910006bd6450910005f7715091001df47150910057b7415091004cff76cc910004fe76cc910004fd76cc91004cfc76cc9100067f65cc9101d67c65cc910055be74cc910005bd74cc910006ef62cc910046ec62cc91001df671cc910005f571cc910044ff768c910004fe768c910004fd768c910044fc768c9100067f658c9101c67c658c910055be748c910005bd748c910006df638c91004edc638c91001df6718c910005f5718c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101b67c654c910044ff760c910004fe760c910004fd760c910044fc760c91005d7e750c9100057d750c9100067f650c9101a67c650c910006df630c91004edc630c910006ef620c910046ec620c910007cd320c91001df6710c910005f5710c910005fa700c910005f9700c91000cfc76505100067f655051018e7c6550510006bf645051000ebc6450510055f7715051001fb44150510005fb7050510005f87050510004fe76cc510024fc76cc51005d7e75cc5100057d75cc5100067f65cc5101867c65cc510006df63cc51004edc63cc510005fa70cc510005f970cc510005f6768c51001ef6768c51001df7758c51025df5758c51000777658c51025774658c510055f6748c51001df4748c51024df5738c51004ef6638c51004ef4638c510005f5728c510025f6708c51001ef7608c51001ff3608c510257f2508c510257f1508c51004cfc764c5100067f654c5101667c654c510005bf744c510055bc744c510006df634c51004edc634c510005fb704c510005f8704c51004ef4764c51004cf4764c51024df7754c51024df5754c51000777654c51024774654c510007b7744c510055f6744c510055f4744c510007b4744c510055b4744c51001df7734c51001fd7734c510007d7634c51004ef6634c51004ef4634c510007d4634c510247d6534c510247d5534c510005f7724c510007f3704c510025f4704c510007f0704c51001ef7604c51001ff3604c510247f2504c510247f1504c510004fe76c8510024fc76c851005d7e75c85100057d75c85100067f65c85101467c65c8510006ef62c8510046ec62c8510005fa70c8510005f970c8510005f6768851001ef6768851001df7758851023df57588510007776588510237746588510055f6748851001df4748851001df77388510005f5738851022df57288510046f6628
  | 3 => 0xe5459110006bd5459110004ff7359110006df7359110004df735911004cfc7359110006dc735911004cdc7359110056bf4359110004ff7259110006ef7259110004ef7259110044fc7259110006ec7259110044ec7259110056bf4259110064ff7159110006f77159110056f74159110266be4159110266bc4159110056f4415911006cff7059110006fb7059110056bc405911004cfe76d8d100067f65d8d100067c65d8d10004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d1000cfe74d8d10004fd74d8d1000cfc74d8d10006df43d8d10006dc43d8d10044fe72d8d10004fd72d8d1001cfe71d8d1001cfc71d8d10024fe70d8d10024fc70d8d1005d7e7598d100057d7598d100067f6598d100067c6598d10006df6398d100057f7558d1005d7c7558d100067f6558d100067c6558d10005bf7458d10055bc7458d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d1000cfe7458d1000cfc7458d10006bc7458d1000cbc7458d10006df7358d10006de5358d10006dd5358d10004ff7258d10006ef7258d10004ef7258d10044fc7258d10006ec7258d10044ec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10055be7418d10005bd7418d1004ede6318d10006dd6318d1004cff7690d10004fe7690d10004fd7690d1004cfc7690d100067f6590d101f67c6590d10006bf6490d1000ebc6490d1001df67190d10005f57190d10057b44190d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d101ee7c6550d1000ebe6450d10006bd6450d10005f77150d1001df47150d10057b74150d10044fe76d89100067f65d89100067c65d8910004ff75d8910014fe75d8910004fd75d8910014fc75d891000cfe74d8910004fd74d891000cfc74d891004cfe73d8910004fd73d8910006ef42d8910006ec42d891001cfe71d891001cfc71d8910024fe70d8910024fc70d891005d7e75989100057d75989100067f65989100067c6598910006ef62989100057f755891005d7c75589100067f65589100067c6558910005bf7458910055bc7458910005df7358910005dc7358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf745891000cfe745891000cfc7458910006bc745891000cbc7458910004ff7358910006df7358910004df735891004cfc7358910006dc735891004cdc7358910006ef7258910006ee5258910006ed5258910004ff7158910006f77158910004ff7058910
  | 4 => 0x61000ebe6450610006bd6450610005fb7050610025f8705061003d7e75cc6100057d75cc61017ebe64cc610006bd64cc61004ede63cc610006dd63cc610025fa70cc610005f970cc61004cff764c610005bf744c610065bc744c61015ebe644c610006bd644c61004ede634c610006dd634c610005fb704c610025f8704c61003d7e75c86100057d75c861013ebe64c8610006bd64c8610046ee62c8610006ed62c8610025fa70c8610005f970c8610044ff7648610005bf7448610065bc744861011ebe6448610006bd6448610046ee6248610006ed6248610005fb7048610025f8704861002cff765021000ebe6450210006bd64502100eebe64cc210006bd64cc210005bf744c210065bc744c2100d6be644c210006bd644c210005ef724c210005ec724c2100aebe64c8210006bd64c8210005bf7448210065bc7448210096be6448210006bd6448210005df7348210005dc7348210025f576c421001ef576c4210026f765c4210276f565c421001fb674c421001fb574c421006ef664c4210027b664c421006eb664c4210027b564c4210026f464c4210026f763c4210006f563c4210026f762c4210006f562c4210027f260c421005d7e76d951005e7e76d95100147e76d95100067e64d95100067c64d95100077771d951005f7471d95100077741d95100077441d951026f7b70d951005f7870d951026f7b10d951026f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067c42d95100067f71d951026e7e71d951005e7d71d951026e7c71d95100067f41d951026e7e41d951026e7c41d951026e7e31d951026e7c31d951026e7e21d951026e7c21d951026e7f70d951005e7e70d951005e7d70d951005e7c70d95100067f40d95100067c40d951026e7f10d951005e7d10d951026e7c10d951000cfe76d91100067f65d91100067c65d9110056be64d911001df671d9110057b741d9110004ff75d9110014fe75d9110004fd75d9110014fc75d911004cfe73d9110004fd73d9110056bc43d9110044fe72d9110004fd72d9110056bc42d911001cfe71d9110054fd71d9110056f571d9110054f571d911001cfc71d9110056bf41d9110056f741d9110056f441d9110024fe70d911001cfd70d9110024fc70d9110056bf40d91100057f755911005d7c75591100067f65591100067c6559110056bc6459110005df7359110005dc7359110005ef7259110005ec7259110057b44159110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c7559110054ff7459110006bf7459110056b
  | 5 => 0x6bf7159210266be7159210006bd7159210266bc7159210006bf5159210266be5159210006bd5159210266bc5159210266be3159210266bc3159210266be2159210266bc2159210066bf7059210026be7059210026bc7059210006bf5059210026be5059210006bd5059210026bc5059210026be3059210026bc3059210026be2059210026bc2059210266bf1059210026be1059210026bc1059210024ff75d8e10014fe75d8e10004fd75d8e10024fc75d8e1000cfe74d8e10026be74d8e1000cbe74d8e10004fd74d8e10026bd74d8e10004bd74d8e10024fc74d8e10044fe72d8e10004fd72d8e10026f571d8e10026fa70d8e10004fd7698e10006be6498e10006bd6498e10026df6398e10026dc6398e1004cff7658e10006be6458e10006bd6458e10026dc6358e10004ff7558e10014fe7558e10004fd7558e10014fc7558e10004ff7458e1000cfe7458e1000cfc7458e10026df7358e10006de5358e10006dd5358e10004ff7258e10044fc7258e10024fc7058e10026de3058e10026dc3058e1004cff7690e10024fe7690e10004fd7690e10024fc7690e1000ebe6490e10006bd6490e10004ff7650e10024fe7650e10004fd7650e10024fc7650e1000ebe6450e10006bd6450e10024ff75d8a10014fe75d8a10004fd75d8a10024fc75d8a1000cfe74d8a10026be74d8a1000cbe74d8a10004fd74d8a10026bd74d8a10004bd74d8a10024fc74d8a1004cfe73d8a10004fd73d8a10026f571d8a10026fa70d8a10004fd7698a10006be6498a10006bd6498a10026ef6298a10026ec6298a10044ff7658a10006be6458a10006bd6458a10026ec6258a10004ff7558a10014fe7558a10004fd7558a10014fc7558a10004ff7458a1000cfe7458a1000cfc7458a10004ff7358a1004cfc7358a10026ef7258a10006ee5258a10006ed5258a10024fc7058a10026ee2058a10026ec2058a10044ff7690a10024fe7690a10004fd7690a10024fc7690a1000ebe6490a10006bd6490a10004ff7650a10024fe7650a10004fd7650a10024fc7650a1000ebe6450a10006bd6450a1004cff76cca10024fe76cca10004fd76cca10024fc76cca10065be74cca10005bd74cca101cebe64cca10006bd64cca1004ede63cca10006dd63cca10044ff768ca10024fe768ca10004fd768ca10024fc768ca10065be748ca10005bd748ca101bebe648ca10006bd648ca10046ee628ca10006ed628ca10004ff764ca10024fe764ca10004fd764ca10024fc764ca101aebe644ca10006bd644ca1004ede634ca10006dd634ca10046ee624ca10006ed624ca10044ff760ca10024fe760ca10004fd760ca10024fc760ca1003d7e750ca100057d750ca1019ebe640ca10006bd640ca10007cd320ca10025fa700ca10005f9700ca1000cff7650610024fc765
  | 6 => 0x7744871006df6744871006df47448710007b4744871006db4744871001fb6644871001fb56448710005f77348710005f5734871001fe77248710046f6624871001ef46248710287e65248710287e55248710025f47048710054fd769031000ebe6490310006bd649031001df67190310005f5719031006fb7419031000cff765031001cfc765031000ebe6450310006bd6450310005f7715031001df47150310267b441503100eebe64cc310006bd64cc31004ede63cc310006dd63cc31001df671cc310005f571cc3100e6be648c310006bd648c310025f4718c31004cff764c310005bf744c31006dbc744c3100d6be644c310006bd644c31004ede634c310006dd634c310005ef724c310005ec724c310005f7714c31001df4714c3100757e750c3100057d750c31006dbe740c310005bd740c3100bebe640c310006bd640c310005ee720c310005ed720c31001df6710c310005f5710c3100aebe64c8310006bd64c8310046ee62c8310006ed62c831001df671c8310005f571c83100a6be6488310006bd6488310025f47188310044ff7648310005bf744831006dbc7448310096be6448310006bd6448310005df7348310005dc7348310046ee6248310006ed6248310005f7714831001df471483100757e75083100057d750831006dbe7408310005bd740831007ebe6408310006bd6408310005de7308310005dd730831001df67108310005f57108310024ff75d9210014fe75d9210004fd75d9210024fc75d9210064fd74d921004cfe73d9210004fd73d9210044fe72d9210004fd72d9210026f571d9210026fa70d9210004bd7699210026bf6599210006be6599210006bd6599210026bc6599210026bf6399210026bc6399210026bf6299210026bc6299210026be6099210027ba5099210007b9509921027fbb1099210027b8109921000cff7659210026bc6459210004ff7559210014fe7559210004fd7559210014fc7559210026bf7459210006bf5459210066be5459210006bd5459210066bc5459210004ff735921004cfc7359210066bf4359210066bc4359210004ff7259210044fc7259210066bf4259210066bc4259210066bf4159210024fc7059210026be4059210026bc4059210025bf7659210066bf765921000cbf7659210026bf6559210006be6559210006bd6559210026bc6559210026bf6359210026bc6359210026bf6259210026bc6259210027ba5059210007b95059210267bb1059210027b81059210006bf7559210006be7559210006bd7559210006bc7559210006bf7359210006be7359210006bd7359210006bc7359210006bf5359210006be5359210006bd5359210006bc5359210006bf7259210006be7259210006bd7259210006bc7259210006bf5259210006be5259210006bd5259210006bc5259210
  | 7 => 0x9310006be7259310006bd7259310006bc7259310006bf5259310006be5259310006bd5259310006bc525931001ebf715931006eb7715931001ebe715931001ebd715931001ebc715931001eb4715931001ebf515931001ebe515931001ebd515931001ebc515931001ebf315931001ebe315931001ebd315931001ebc315931001ebf215931001ebe215931001ebd215931001ebc2159310006bf7059310006bd705931006ebc7059310006bf5059310006be5059310006bd5059310006bc505931001ebf105931001ebe105931001ebd105931001ebc1059310004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f1000cfe7458f1000cfc7458f1001edf7358f10006de5358f10006dd5358f10004ff7258f10044fc7258f1001cfc7158f1001ede3158f1001edc3158f1004cff7690f1001cfe7690f10004fd7690f1001cfc7690f1000ebe6490f10006bd6490f1001df67190f10005f57190f1020fb44190f10004ff7650f1001cfe7650f10004fd7650f1001cfc7650f1000ebe6450f10006bd6450f10005f77150f1001df47150f1006fb74150f10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b1000cfe7458b1000cfc7458b10004ff7358b1004cfc7358b1001eef7258b10006ee5258b10006ed5258b1001cfc7158b1001eee2158b1001eec2158b10044ff7690b1001cfe7690b10004fd7690b1001cfc7690b1000ebe6490b10006bd6490b1001df67190b10005f57190b10207b44190b10004ff7650b1001cfe7650b10004fd7650b1001cfc7650b1000ebe6450b10006bd6450b10005f77150b1001df47150b1006fb74150b1004cff76ccb1001cfe76ccb10004fd76ccb1001cfc76ccb1006dbe74ccb10005bd74ccb101cebe64ccb10006bd64ccb10046ee62ccb10006ed62ccb1001df671ccb10005f571ccb10044ff768cb1001cfe768cb10004fd768cb1001cfc768cb1006dbe748cb10005bd748cb101bebe648cb10006bd648cb1004ede638cb10006dd638cb1001df6718cb10005f5718cb10004ff764cb1001cfe764cb10004fd764cb1001cfc764cb101aebe644cb10006bd644cb1001df6714cb10044ff760cb1001cfe760cb10004fd760cb1001cfc760cb100757e750cb100057d750cb1019ebe640cb10006bd640cb1004ede630cb10006dd630cb10046ee620cb10006ed620cb10007cd320cb1001df6710cb10005f5710cb1001df7764c710006f7764c71029df7754c71029df5754c710007b7744c71006df6744c71006df4744c710007b4744c71006db4744c71001fb6644c71001fb5644c71001fd7734c71004ef6634c71001ef4634c710297d6534c710297d5534c710005f7724c710025f4704c71001df77648710006f7764871028df7754871028df57548710007b
  | 8 => 0x6de6390420006dd639042001ef66190420006f56190420004ff7650420004fd7650420024fc765042018e7e65504200067d655042000ebe6450420006bd6450420006de6350420006dd6350420005ef7250420045ec725042001ef66150420006f5615042004cff76cc420024fe76cc420004fd76cc4200857e75cc4200057d75cc4201867e65cc4200067d65cc42017ebe64cc420006bd64cc42004ede63cc420006dd63cc42001ef661cc420006f561cc42001cff768c420024fe768c420004fd768c4201767e658c4200067d658c42016ebe648c420006bd648c42004ede638c420006dd638c420045ee728c420005ed728c42001ef6618c420006f5618c420004ff764c420004fd764c420024fc764c4201667e654c4200067d654c420005bf744c42007dbc744c42015ebe644c420006bd644c42004ede634c420006dd634c420005ef724c420045ec724c42001ef6614c420006f5614c42001cff760c420024fe760c420004fd760c4201567e650c4200067d650c42007dbe740c420005bd740c42014ebe640c420006bd640c42004ede630c420006dd630c42001ef6610c420006f5610c4200a4ff76500200fe7e65500200067d655002000ebe6450020006bd6450020006de6350020006dd6350020006f66150020006f56150020004fd76cc0200f67e65cc0200067d65cc0200eebe64cc020006bd64cc02004ede63cc020006dd63cc020045ec72cc0202a7cf32cc020006f661cc020006f561cc020004ff764c0200de7e654c0200067d654c020005bf744c02007dbc744c0200d6be644c020006bd644c02004ede634c020006dd634c020005ef724c020045ec724c020007cf324c020006f6614c020006f5614c020025ef7648020006ef7648020004ef7648020026ef65480200276e65480202aeed65480200276d65480200066d6548020007af7448020007ac7448020027ae6448020027ad6448020007cf73480202a5ee73480202a5ec7348020007cc7348020005cc7348020026ef6348020027ce6348020006ed6348020027cd6348020006cd6348020027e66148020027e56148020025ef7048020047eb7048020026ee6048020027ea6048020004ff7559310014fe7559310004fd7559310014fc755931001ebf7459310006bf545931006ebe5459310006bd545931006ebc5459310004ff735931004cfc735931006ebf435931006ebc4359310004ff7259310044fc725931006ebf425931006ebc425931001cfc715931001ef4715931001cf4715931006ef7415931001ebe415931001ebc415931001ef4415931006ebf4059310006bf7559310006be7559310006bd7559310006bc7559310006bf7359310006be7359310006bd7359310006bc7359310006bf5359310006be5359310006bd5359310006bc5359310006bf725
  | 9 => 0xd7650c20024fc7650c201ee7e6550c200067d6550c2000ebe6450c20006bd6450c2004ede6350c20006dd6350c20005ef7250c20045ec7250c20045ed76cc8202a6ed76cc820004ed76cc820046ef65cc8200476e65cc8202beed65cc8200476d65cc8200066d65cc8202a7ae74cc8202a7ad74cc820047ae64cc820047ad64cc820045ee73cc820047ce73cc820046ef63cc820047ce63cc8202a6ed63cc820047cd63cc820006cd63cc820047e661cc820047e561cc820005ed70cc8202b6ee60cc820047ea60cc82001ef7759842001ef6759842001ef5759842001ef4759842001ef7749842001ef6749842001ef5749842001ef47498420006f75498420006f65498420006f55498420006f4549842001ef7739842001ef6739842001ef5739842001ef47398420006f75398420006f65398420006f55398420006f45398420006f74398420006f64398420006f54398420006f4439842001ef7729842001ef6729842001ef5729842001ef47298420046f75298420046f65298420046f55298420046f45298420046f74298420046f64298420046f54298420046f44298420046f73298420046f63298420046f53298420046f43298420026f67098420026f47098420006f75098420026f65098420006f55098420026f45098420006f74098420026f64098420026f44098420026f63098420026f43098420046f72098420026f62098420046f52098420026f42098420004ff7558420014fe7558420004fd7558420014fc7558420004ff745842000cfe745842000cfc7458420004ff735842004cfc7358420026f77158420006f75158420006f65158420006f55158420006f45158420006f74158420006f44158420046f72158420046f4215842001cff7058420026f61058420026f41058420006f77558420006f67558420006f57558420006f47558420006f77458420006f67458420006f57458420006f47458420006f75458420006f65458420006f55458420006f45458420006f77358420006f67358420006f57358420006f47358420006f75358420006f65358420006f55358420006f45358420006f74358420006f64358420006f54358420006f44358420046f77258420046f67258420046f47258420046f75258420046f65258420046f55258420046f45258420046f74258420046f64258420046f54258420046f44258420046f73258420046f63258420046f53258420046f43258420026f67058420026f47058420006f75058420026f65058420006f55058420026f45058420006f74058420026f64058420026f44058420026f63058420026f43058420046f72058420026f62058420046f52058420026f4205842001cff7690420024fe7690420004fd76904201967e65904200067d659042000ebe6490420006bd6490420
  | 10 => 0x9020046be2159020046bd2159020046bc215902007ebf7059020026be7059020026bc7059020006bf5059020026be5059020006bd5059020026bc5059020026be3059020026bc3059020046bf2059020026be2059020046bd2059020026bc2059020026be1059020026bc105902004edf7598c2004ede7598c2004edd7598c2004edc7598c2004edf7498c2004ede7498c2004edd7498c2004edc7498c20006df5498c20006de5498c20006dd5498c20006dc5498c20046df7298c20046de7298c20046dd7298c20046dc7298c20046df5298c20046de5298c20046dd5298c20046dc5298c20046df4298c20046de4298c20046dd4298c20046dc4298c2004edf7198c2004ede7198c2004edd7198c2004edc7198c20006df5198c20006de5198c20006dd5198c20006dc5198c20006df4198c20006dc4198c20046df2198c20046de2198c20046dd2198c20046dc2198c20026de7098c20026dc7098c20006df5098c20026de5098c20006dd5098c20026dc5098c20006df4098c20026de4098c20026dc4098c20046df2098c20026de2098c20046dd2098c20026dc2098c20026de1098c20026dc1098c20004ff7558c20014fe7558c20004fd7558c20014fc7558c20004ff7458c2000cfe7458c2000cfc7458c20024ff7358c20026df7358c20006df5358c20006de5358c20006dd5358c20006dc5358c20006df4358c20006dc4358c20044ff7258c20044fe7258c20044fd7258c20044fc7258c20046ec7258c20044ec7258c20046de3258c20046dc3258c20046ec3258c20046cc3258c20004ff7158c2001cfc7158c20024fe7058c20024fc7058c20026de3058c20026dc3058c20046ef2058c20006df7558c20006de7558c20006dd7558c20006dc7558c20006df7458c20006de7458c20006dd7458c20006dc7458c20006df5458c20006de5458c20006dd5458c20006dc5458c20046df7258c20046de7258c20046dd7258c20046dc7258c20046cc7258c20046df5258c20046de5258c20046dd5258c20046dc5258c20046df4258c20046de4258c20046dd4258c20046dc4258c20006df7158c20006de7158c20006dd7158c20006dc7158c20006df5158c20006de5158c20006dd5158c20006dc5158c20006df4158c20006dc4158c20046df2158c20046de2158c20046dd2158c20046dc2158c20026de7058c20026dc7058c20006df5058c20026de5058c20006dd5058c20026dc5058c20006df4058c20026de4058c20026dc4058c20046df2058c20046cf2058c20026de2058c20046dd2058c20026dc2058c20026de1058c20026dc1058c2004cff7690c20024fe7690c20004fd7690c20024fc7690c201f67e6590c200067d6590c2000ebe6490c20006bd6490c2004ede6390c20006dd6390c20004ff7650c20024fe7650c20004f
  | 11 => 0x44fe76cc120044fc76cc120006bf64cc1200eebc64cc120006df63cc12004edc63cc120045ee72cc120005ed72cc120007cd32cc120004fe768c120006bf648c1200e6bc648c120006df638c12004edc638c120007ce328c12004cff764c120004fd764c120044fc764c120005bf744c120095bc744c120006bf644c1200d6bc644c120006df634c12004edc634c120005ef724c120045ec724c120007cd324c120004fe760c12009d7e750c1200057d750c120095be740c120005bd740c120006bf640c1200bebc640c120006df630c12004edc630c120045ee720c120005ed720c120007ce320c120005f6710c120005f5710c120006bf64881200a6bc6488120006df6388120006dc6388120045fa7088120046fb6088120025ef75881202c5ed7588120007af6488120007ac6488120025ef7388120005ed7388120007cf63881202b6ee63881202b6ec6388120007cc6388120006cc6388120025ee7088120026ef6088120047eb60881200067f74594200067e74594200067d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067c43594200467f72594200467e72594200467d72594200467c72594200467f42594200467e42594200467d42594200467c42594200467f32594200467e32594200467d32594200467c32594200466c32594200067f71594200067e71594200067d71594200067c71594200067f41594200067c41594200467f21594200467e21594200467d21594200467c21594200867f70594200267e70594200867d70594200267c70594200067f40594200267e40594200267c40594200267e30594200267c30594200467f20594200466f20594200267e20594200467d20594200267c20594200267e10594200267c1059420004ff7559020014fe7559020004fd7559020014fc7559020024ff7459020026bf7459020006bf545902007ebe5459020006bd545902007ebc5459020004ff735902004cfc735902007ebf435902007ebc4359020044ff7259020044fe7259020044fd7259020044fc7259020046be4259020046bc4259020004ff715902001cfc715902007ebf415902007ebc4159020024fe7059020024fc7059020026be4059020026bc4059020006bf7559020006be7559020006bd7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf5359020006be5359020006bd5359020006bc5359020046bf7259020046be7259020046bd7259020046bc7259020046bf5259020046be5259020046bd5259020046bc5259020046bf3259020046be3259020046bd3259020046bc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf5159020006be5159020006bd5159020006bc5159020046bf215
  | 12 => 0xf648c920007ac648c9202cded738c920007cf638c92004eee638c92004eec638c920007cc638c92004ecc638c9202d7ce538c9202d7cd538c920025ee708c920046ef608c920047eb608c92004cfc764c920006bf644c9201aebc644c920006df634c92004edc634c920047cc324c920005fb704c920005f8704c92004eec764c92004cec764c9202cdef754c9202cded754c920007af644c920007ac644c920045ef734c920047cf734c920007cf634c92004eee634c92004eec634c920007cc634c92004ecc634c920007eb704c920025ec704c920007e8704c920046ef604c920047eb604c920006bf64d8520006bc64d8520006df63d8520006dc63d8520004ff75d8520014fe75d8520004fd75d8520014fc75d852000cfe74d8520004fd74d852000cfc74d852004cfe73d8520004fd73d8520006ee52d8520006ed52d8520006f751d8520006f451d8520024fe70d8520095be7498520005bd7498520006bf6498520006bc6498520005de7398520005dd7398520006df6398520006dc6398520006f761985200057f755852009d7c7558520005bf7458520095bc7458520006bf6458520006bc6458520005df7358520005dc7358520006df6358520006dc6358520006bf6418520006bc6418520006df6318520006dc631852001ef66118520006f56118520004fe7690520004fd769052001cfc7690520006bf649052000ebc6490520006df6390520006dc6390520004ff7650520004fe7650520004fc7650520006bf645052000ebc6450520006df6350520006dc6350520004fe76cc520004fd76cc52004cfc76cc52009d7e75cc5200057d75cc520006bf64cc52017ebc64cc520006df63cc52004edc63cc520045ee72cc520005ed72cc520004fe768c520004fd768c52001cfc768c520006bf648c52016ebc648c520006df638c52004edc638c520004ff764c520004fe764c520004fc764c520005bf744c520095bc744c520006bf644c52015ebc644c520006df634c52004edc634c520004fe760c520004fd760c52001cfc760c520095be740c520005bd740c520006bf640c52014ebc640c520006df630c52004edc630c520045ee720c520005ed720c520005fa700c520005f9700c520006bf648852012ebc6488520006df6388520006dc6388520006f7618852001ef46188520005fa7088520005f9708852001cfc7648520005bf7448520095bc7448520006bf644852011ebc6448520006df6348520006dc6348520006f7614852001ef46148520005fb7048520005f870485200acfe7690120006bf649012000ebc6490120006df6390120006dc6390120005f67190120005f5719012000cff7650120094fd7650120044fc7650120006bf645012000ebc6450120006df6350120006dc6350120005ef7250120045ec7250120
  | 13 => 0x8d20006dd71d8d20006dc71d8d20006df51d8d20006de51d8d20006dd51d8d20006dc51d8d20006df41d8d20006dc41d8d202eedf21d8d202eedc21d8d202eedf70d8d20006dd70d8d20006df50d8d20006de50d8d20006dd50d8d20006dc50d8d20006df40d8d20006dc40d8d202eedf20d8d202eedc20d8d20095be7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d20005bf7458d20095bc7458d20006bf6458d20006bc6458d20004ff7558d20014fe7558d20004fd7558d20014fc7558d20004ff7458d20006bf7458d20004bf7458d2000cfe7458d2000cfc7458d20006bc7458d2000cbc7458d20006df7358d20004ff7258d20006ef7258d20004ef7258d20004ff7158d2001cfc7158d20004ff7058d20006fb7058d20004fe7618d2009d7e7518d200057d7518d20006bf6418d20006bc6418d2004ede6318d20006dd6318d20005de7618d20006de7618d20004de7618d200075e7518d200075d7518d20006df6518d20006de6518d20006dd6518d20006dc6518d20006df6418d200079f6418d200069f6418d20006de6418d20006dd6418d20006dc6418d200079c6418d200069c6418d20007cd7218d20007ce5218d20007cd5218d202e7db2018d202e7d82018d2004edf7518d2004ede7518d2004e5e7518d2004edd7518d2004e5d7518d2004edc7518d2004edf7418d2004ede7418d2004edd7418d2004edc7418d20006df5418d20006de5418d20006dd5418d20006dc5418d2004edf7218d2004ede7218d2004edd7218d2004ecd7218d2004edc7218d20006df5218d202e6de5218d20006ce5218d20006dd5218d20006cd5218d202e6dc5218d20006df4218d202e6de4218d202e6dc4218d2004edf7118d2004ede7118d2004edd7118d2004edc7118d20006df5118d20006de5118d20006dd5118d20006dc5118d20006df4118d20006dc4118d202e6df2118d202e6dc2118d2004edf7018d2004edd7018d20006df5018d20006de5018d20006dd5018d20006dc5018d20006df4018d20006dc4018d202e6df2018d20006dd2018d202e6dc2018d2004cff7690d20004fe7690d20004fd7690d2004cfc7690d20006bf6490d2000ebc6490d20006df6390d2004edc6390d20045ee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d2000ebc6450d20006df6350d2004edc6350d2000cfc7650920006bf645092000ebc6450920006df6350920006dc6350920005fb7050920005f87050920004fe76cc920024fc76cc920095be74cc920005bd74cc920006bf64cc9201cebc64cc920006df63cc92004edc63cc920005fa70cc920005f970cc920005ee768c920046ee768c920004ee768c920045ef758c9202dded758c920047ae748c920047ad748c920007a
  | 14 => 0xcfe76d9120096be64d9120004ff75d9120014fe75d9120004fd75d9120014fc75d9120006bf54d9120096be54d9120006bd54d9120096bc54d912004cfe73d9120004fd73d9120096bf43d9120096bc43d9120044fe72d9120094fd72d9120044fc72d9120096bf42d912001cfe71d9120004fd71d9120096bf41d9120096bc41d9120044fd70d9120096bf40d9120095be76d912000cbe76d9120006bf65d9120006be65d9120006bd65d9120006bc65d9120007ae52d9120007ad52d91202ffbb20d91202ffb820d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d9120006bf72d91202febe72d9120006bd72d91202febc72d9120006bf52d91202febe52d9120006bd52d91202febc52d91202febe32d91202febc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d91202febf21d91202febc21d91202febf70d9120096be70d9120006bd70d9120006bf50d9120006be50d9120006bd50d9120006bc50d91202febf20d91202febc20d9120096bc6459120005df7359120005dc7359120004ff7559120014fe7559120004fd7559120014fc7559120094ff7459120006bf7459120004ff7359120006df7359120004df735912004cfc7359120006dc735912004cdc73591200a4ff7259120006ef7259120004ff715912001cfc71591200acff7059120006fb7059120005be7619120096be7619120004be7619120006bf6519120006be6519120006bd6519120006bc6519120007ae5219120007ad52191202f6bf60191202f7bb20191202f7b8201912004cfe76d8d20006bf64d8d20006bc64d8d20004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d2000cfe74d8d20004fd74d8d2000cfc74d8d20006df53d8d20006de53d8d20006dd53d8d20006dc53d8d20006df43d8d20006dc43d8d20044fe72d8d20044fc72d8d2001cfe71d8d20004fd71d8d2004cde76d8d20006df65d8d20006de65d8d20006dd65d8d20006dc65d8d20006df64d8d200079f64d8d200069f64d8d20006de64d8d20006dd64d8d20006dc64d8d200079c64d8d200069c64d8d20007cf72d8d20007ce52d8d20007cd52d8d202efdb20d8d202efd820d8d20006df75d8d20006de75d8d20006dd75d8d20006dc75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d20006df72d8d202eede72d8d20006dd72d8d202eedc72d8d20006df52d8d202eede52d8d20006dd52d8d202eedc52d8d20006df42d8d202eede42d8d202eedc42d8d20006df71d8d20006de71d
  | 15 => 0xf7158e2001cfc7158e20024fc7058e20026de3058e20026dc3058e2004cff7690e20024fe7690e20004fd7690e20024fc7690e20006bf6490e2000ebc6490e20004ff7650e20024fe7650e20004fd7650e20024fc7650e2000ebe6450e20006bd6450e20005ef7250e20045ec7250e2000cff7650a20024fc7650a2000ebe6450a20006bd6450a20005fb7050a20025f87050a200a5be74cca20005bd74cca2004ede63cca20006dd63cca20025fa70cca20005f970cca202b6ed76cca2031eef65cca2031eed65cca202b7ae74cca202b7ad74cca20045ee73cca202b6ef63cca202b7ce63cca202b6ed63cca20007cd63cca202b7ea70cca20005ed70cca202b7e970cca20046ee60cca2004cff764ca2004ede634ca20006dd634ca20047cc324ca20005fb704ca20025f8704ca20005ed760ca20046ed760ca200476e750ca200476d750ca20316ef650ca20316ed650ca20047ce730ca202b6ef630ca2030fcf630ca20006cf630ca202b6ed630ca2030fcc630ca202b7ce530ca20317cd530ca20005ed700ca20047ea600ca2030fce300ca2030fcc300ca200a5be7498620005bd7498620026f76198620026f461986200057f755862008d7c7558620026f46158620004ff75586200067f75586200047f7558620014fe7558620004fd7558620014fc75586200067c75586200147c7558620004ff745862000cfe745862000cfc7458620004ff735862004cfc7358620006f65158620006f55158620006f74158620006f44158620024fc7058620026f61058620026f4105862001cff7690620024fe7690620004fd769062000ebe6490620006bd6490620004ff7650620004fd7650620024fc7650620006bf645062000ebc6450620005ef7250620045ec725062004cff76cc620024fe76cc620004fd76cc62008d7e75cc6200057d75cc62001cff768c620024fe768c620004fd768c620045ee728c620005ed728c62001ef6618c620006f5618c620004ff764c620004fd764c620024fc764c620005bf744c6200a5bc744c620005ef724c620045ec724c62001ef6614c620006f5614c62001cff760c620024fe760c620004fd760c6200a5be740c620005bd740c620025fa700c620005f9700c62001ef66188620006f56188620025fa7088620005f9708862001cff7648620005bf74486200a5bc744862001ef66148620006f56148620005fb7048620025f8704862007cff7650220026bf6450220026bc6450220026df63cc220026dc63cc2202b7cf32cc220005bf744c2200a5bc744c220026df634c220026dc634c220005ef724c220045ec724c220007cf324c220025ed76c8220046ed76c8220026ef65c8220306ed65c82202b5ee73c8220045ec73c8220026ef63c8220006ed63c8220027ea60c8220027ea50c8220307e950c8220
  | 16 => 0xcb20047cf734cb20047cf634cb2004eee634cb20046ec634cb20047cc634cb20046cc634cb20025ec704cb20004ff7558720014fe7558720004fd7558720014fc7558720004ff7458720006bf7458720004bf745872000cfe745872000cfc7458720006bc745872000cbc7458720004ff735872004cfc7358720046ee5258720006ed5258720046f77158720046f72158720046f4215872001cff7690720044fe7690720004fd7690720326bf649072000ebc6490720004ff7650720004fd7650720044fc765072000ebe6450720006bd645072004cff76cc720044fe76cc720004fd76cc7200b57e75cc7200057d75cc720045ee72cc720005ed72cc72001cff768c720044fe768c720004fd768c720004ff764c720004fd764c720044fc764c720005bf744c7200adbc744c72001cff760c720044fe760c720004fd760c7200adbe740c720005bd740c720045ee720c720005ed720c720094fd76903202febf649032000ebc6490320005f67190320005f5719032000cff7650320044fc765032000ebe6450320006bd6450320005ef7250320045ec725032004ede63cc320006dd63cc320045ee72cc320005ed72cc320007cd32cc3202eedf638c32004edc638c320025ec728c3202efce328c32004cff764c320005bf744c3200adbc744c32004ede634c320006dd634c320005ef724c320045ec724c320007cd324c3200b57e750c3200057d750c3200adbe740c320005bd740c3202e6df630c32004edc630c320045ee720c320005ed720c3202e7ce320c320005f6710c320005f5710c320024ff75d9220014fe75d9220004fd75d9220024fc75d92200a4fd74d922004cfe73d9220004fd73d92200a6bc43d9220026ed72d92202febe42d92202febc42d922001cfe71d9220026f671d922001cf671d9220004fd71d9220026f571d9220004f571d92200a6bf41d9220026fa70d9220026bf40d922000cff7659220026bc6459220004ff7559220014fe7559220004fd7559220014fc7559220026bf74592200a6be5459220006bd5459220004ff735922004cfc73592200a6bf43592200a6bf4259220004ff715922001cfc71592200a6bc4159220024fc7059220026be4059220026bc4059220024ff75d8e20014fe75d8e20004fd75d8e20024fc75d8e2000cfe74d8e20004fd74d8e20024fc74d8e20026ed72d8e202eede32d8e202eedc32d8e2001cfe71d8e20004fd71d8e20026fa70d8e20004fd7698e20026df6398e20026dc6398e2004cff7658e20005bf7458e200a5bc7458e20026dc6358e20004ff7558e20014fe7558e20004fd7558e20014fc7558e20004ff7458e20006bf7458e20004bf7458e2000cfe7458e2000cfc7458e20006bc7458e2000cbc7458e20026df7358e20006de5358e20006dd5358e20006ef7258e20004f
  | 17 => 0x26f65058430006f55058430026f45058430006f74058430026f64058430026f4405843004ef73058430026f6305843004ef53058430026f43058430026f62058430026f4205843001cff7690430024fe7690430004fd76904301967e65904300067d659043000ebe6490430006bd6490430006ee6290430006ed629043001ef66190430006f56190430004ff7650430004fd7650430024fc765043018e7e65504300067d655043000ebe6450430006bd6450430005df735043004ddc7350430006ee6250430006ed625043001ef66150430006f56150430044ff76c8430024fe76c8430004fd76c84300c57e75c84300057d75c84301467e65c84300067d65c843013ebe64c8430006bd64c8430046ee62c8430006ed62c843001ef661c8430006f561c843001cff7688430024fe7688430004fd76884301367e65884300067d658843012ebe6488430006bd648843004dde7388430005dd7388430046ee6288430006ed628843001ef66188430006f56188430004ff7648430004fd7648430024fc76484301267e65484300067d6548430005bf74484300bdbc744843011ebe6448430006bd6448430005df734843004ddc7348430046ee6248430006ed624843001ef66148430006f5614843001cff7608430024fe7608430004fd76084301167e65084300067d65084300bdbe7408430005bd740843010ebe6408430006bd6408430046ee6208430006ed620843001ef66108430006f561084300e4ff76500300fe7e65500300067d655003000ebe6450030006bd6450030006ee6250030006ed6250030006f66150030006f56150030025df764c030006df764c030004df764c030026df654c0300275e654c03033edd654c0300275d654c0300065d654c0300079f744c0300079c744c0300279e644c0300279d644c030007cf724c0302e5dc724c030007cc724c030005cc724c030027ce624c030006dd624c030027cd624c030006cd624c030027d6614c030027d5614c030025df704c03004fdb704c030026de604c030027da604c030004ff7559320014fe7559320004fd7559320014fc7559320046bf7459320004ff735932004cfc73593200aebc4359320044fc7259320046be4259320046bc4259320004ff715932001cfc71593200aebf41593200aebf4059320004ff7558f20014fe7558f20004fd7558f20014fc7558f20004ff7458f2000cfe7458f2000cfc7458f20046df7358f20044fc7258f20046de3258f20046dc3258f20004ff7158f2001cfc7158f2004cff7690f20044fe7690f20004fd7690f20044fc7690f2000ebe6490f20006bd6490f20045ee7290f20005ed7290f20004ff7650f20044fe7650f20004fd7650f20044fc7650f20336bf6450f2000ebc6450f20045ef764cb20006ef764cb2032def754cb2032ded754
  | 18 => 0xf4058830026ee4058830026ec405883004eef305883004ecf3058830026ee305883004eed3058830026ec3058830026ee1058830026ec1058830044ff7690830024fe7690830004fd76908301e67e65908300067d659083000ebe6490830006bd6490830046ee6290830006ed6290830004ff7650830004fd7650830024fc76508301de7e65508300067d655083000ebe6450830006bd6450830005df735083004ddc7350830046ee6250830006ed625083004ddd768c8302e6dd768c830004dd768c83004edf658c83004f5e658c830346dd658c83004f5d658c8300065d658c8302e79e748c8302e79d748c83004f9e648c83004f9d648c83004dde728c83004fce728c83004edf628c83004fce628c8302e6dd628c83004fcd628c830006cd628c83004fd6618c83004fd5618c830005dd708c8302eede608c83004fda608c83001ef7759843001ef6759843001ef5759843001ef4759843001ef7749843001ef6749843001ef5749843001ef47498430006f75498430006f65498430006f55498430006f4549843001ef7739843001ef6739843001ef5739843001ef4739843004ef7539843004ef6539843004ef5539843004ef4539843004ef7439843004ef6439843004ef5439843004ef4439843001ef7729843001ef6729843001ef5729843001ef47298430006f75298430006f65298430006f55298430006f45298430006f74298430006f64298430006f54298430006f4429843004ef7329843004ef6329843004ef5329843004ef43298430026f67098430026f47098430006f75098430026f65098430006f55098430026f45098430006f74098430026f64098430026f4409843004ef73098430026f6309843004ef53098430026f43098430026f62098430026f42098430004ff7558430014fe7558430004fd7558430014fc7558430004ff745843000cfe745843000cfc7458430004ff7258430044fc7258430026f77158430006f75158430006f65158430006f55158430006f45158430006f74158430006f4415843004ef7315843004ef43158430026f61058430026f41058430006f77558430006f67558430006f57558430006f47558430006f77458430006f67458430006f57458430006f47458430006f75458430006f65458430006f55458430006f4545843004ef7735843004ef6735843004ef4735843004ef7535843004ef6535843004ef5535843004ef4535843004ef7435843004ef6435843004ef5435843004ef44358430006f77258430006f67258430006f57258430006f47258430006f75258430006f65258430006f55258430006f45258430006f74258430006f64258430006f54258430006f4425843004ef7325843004ef6325843004ef5325843004ef43258430026f67058430026f47058430006f75058430
  | 19 => 0x9030006bf7559030006be7559030006bd7559030006bc755903004ebf735903004ebe735903004ebd735903004ebc735903004ebf535903004ebe535903004ebd535903004ebc5359030006bf7259030006be7259030006bd7259030006bc7259030006bf5259030006be5259030006bd5259030006bc525903004ebf325903004ebe325903004ebd325903004ebc3259030006bf7159030006be7159030006bd7159030006bc7159030006bf5159030006be5159030006bd5159030006bc515903004ebf315903004ebe315903004ebd315903004ebc31590300bebf7059030026be7059030026bc7059030006bf5059030026be5059030006bd5059030026bc505903004ebf3059030026be305903004ebd3059030026bc3059030026be2059030026bc2059030026be1059030026bc1059030046ef7598830046ee7598830046ed7598830046ec7598830046ef7498830046ee7498830046ed7498830046ec7498830006ef5498830006ee5498830006ed5498830006ec5498830046ef7398830046ee7398830046ed7398830046ec739883004eef539883004eee539883004eed539883004eec539883004eef439883004eee439883004eed439883004eec4398830046ef7198830046ee7198830046ed7198830046ec7198830006ef5198830006ee5198830006ed5198830006ec5198830006ef4198830006ec419883004eef319883004eee319883004eed319883004eec3198830026ee7098830026ec7098830006ef5098830026ee5098830006ed5098830026ec5098830006ef4098830026ee4098830026ec409883004eef3098830026ee309883004eed3098830026ec3098830026ee1098830026ec1098830004ff7558830014fe7558830004fd7558830014fc7558830004ff745883000cfe745883000cfc7458830026ef7258830006ef5258830006ee5258830006ed5258830006ec5258830006ef4258830006ec425883004eef325883004edc325883004eec325883004ecc3258830004ff715883001cfc715883004edf3058830026ee2058830026ec2058830006ef7558830006ee7558830006ed7558830006ec7558830006ef7458830006ee7458830006ed7458830006ec7458830006ef5458830006ee5458830006ed5458830006ec545883004eef735883004eee735883004eec735883004eef535883004eee535883004eed535883004eec535883004eef435883004eee435883004eed435883004eec4358830006ef7158830006ee7158830006ed7158830006ec7158830006ef5158830006ee5158830006ed5158830006ec5158830006ef4158830006ec415883004eef315883004eee315883004eed315883004eec3158830026ee7058830026ec7058830006ef5058830026ee5058830006ed5058830026ec5058830006e
  | 20 => 0x6ec6250530006bf648c53016ebc648c530006ef628c530006ec628c530006f7618c53001ef4618c530005fa708c530005f9708c53001cfc764c530005bf744c5300d5bc744c530006bf644c53015ebc644c530006ef624c530006ec624c530006f7614c53001ef4614c530005fb704c530005f8704c530004fe76c8530004fd76c8530044fc76c85300dd7e75c85300057d75c8530006bf64c853013ebc64c853004dde73c8530005dd73c8530006ef62c8530046ec62c8530004fe7688530004fd768853001cfc7688530006bf648853012ebc6488530006ef6288530046ec6288530004ff7648530004fe7648530004fc7648530005bf74485300d5bc7448530006bf644853011ebc6448530006ef6248530046ec6248530004fe7608530004fd760853001cfc76085300d5be7408530005bd7408530006bf640853010ebc640853004dde7308530005dd7308530006ef6208530046ec6208530005fa7008530005f970085300ecfe7690130006bf649013000ebc6490130006ef6290130006ec6290130005f67190130005f5719013000cff76501300d4fd765013004cfc7650130006bf645013000ebc6450130005df735013004ddc7350130006ef6250130006ec6250130006bf648c1300e6bc648c130006ef628c130006ec628c13004dfa708c13004efb608c130025df758c13034ddd758c1300079f648c1300079c648c130005dd728c130007cf628c1302eedc628c130007cc628c130006cc628c130025de708c130026df608c13004fdb608c1300067f74594300067e74594300067d74594300067c745943004e7f735943004e7e735943004e7d735943004e7c735943004e7f435943004e7e435943004e7d435943004e7c43594300067f72594300067e72594300067d72594300067c72594300067f42594300067c425943004e7f325943004e7e325943004e7d325943004e7c325943004e5c32594300067f71594300067e71594300067d71594300067c71594300067f41594300067c415943004e7f315943004e7e315943004e7d315943004e7c31594300c67f70594300267e70594300c67d70594300267c70594300067f40594300267e40594300267c405943004e7f305943004e5f30594300267e305943004e7d30594300267c30594300267e20594300267c20594300267e10594300267c1059430004ff7559030014fe7559030004fd7559030014fc7559030024ff7459030026bf7459030006bf54590300bebe5459030006bd54590300bebc545903004cff735903004cfe735903004cfd735903004cfc735903004ebe435903004ebc4359030004ff7259030044fc72590300bebf42590300bebc4259030004ff715903001cfc71590300bebf41590300bebc4159030024fe7059030024fc7059030026be4059030026bc405
  | 21 => 0xd75189300466d7518930046ec7518930046ef7418930046ee7418930046ed7418930046ec7418930006ef5418930006ee5418930006ed5418930006ec5418930046ef7318930046ee7318930046ec7318930006ef53189302a6ee5318930006ce5318930006ed5318930006cd53189302a6ec5318930006ef43189302a6ee4318930006ed43189302a6ec4318930046ef7118930046ee7118930046ed7118930046ec7118930006ef5118930006ee5118930006ed5118930006ec5118930006ef4118930006ec41189302a6ef31189302a6ec3118930046ef7018930046ed7018930006ef5018930006ee5018930006ed5018930006ec5018930006ef4018930006ec40189302a6ef3018930006ed30189302a6ec3018930004fe7690930004fd7690930044fc7690930006bf649093000ebc649093004dde7390930005dd7390930006ef6290930046ec6290930004ff7650930004fe7650930004fc7650930006bf645093000ebc6450930006ef6250930046ec6250930005de76cc93004ede76cc930004de76cc93004ddf75cc930365dd75cc93004f9e74cc93004f9d74cc9300079f64cc9300079c64cc930007cf62cc930046de62cc930046dc62cc930007cc62cc930046cc62cc93035fce52cc93035fcd52cc930025de70cc93004edf60cc93004fdb60cc9300d5be748c930005bd748c930006bf648c9301bebc648c930355dd738c930006ef628c930046ec628c930005fa708c930005f9708c930044fc764c930006bf644c9301aebc644c930006ef624c930046ec624c93004fcc324c930005fb704c930005f8704c930044dc764c930355df754c930355dd754c9300079f644c9300079c644c93004ddf724c93004fcf724c930007cf624c930046de624c930046dc624c930007cc624c930046cc624c930007db704c930025dc704c930007d8704c93004edf604c93004fdb604c930006bf64d8530006bc64d8530006ef62d8530006ec62d8530004ff75d8530014fe75d8530004fd75d8530014fc75d853000cfe74d8530004fd74d853000cfc74d8530006de53d8530006dd53d8530044fe72d8530004fd72d8530006f751d8530006f451d85300d5be7498530005bd7498530006bf6498530006bc6498530005ee7298530005ed7298530006ef6298530006ec6298530006f761985300057f75585300dd7c7558530005bf74585300d5bc7458530006bf6458530006bc6458530005ef7258530005ec7258530006ef6258530006ec6258530006bf6418530006bc6418530006ef6218530006ec621853001ef66118530006f56118530004fe7690530004fd769053001cfc7690530006bf649053000ebc6490530006ef6290530006ec6290530004ff7650530004fe7650530004fc7650530006bf645053000ebc6450530006ef6250530
  | 22 => 0x9130006bf51d9130006be51d9130006bd51d9130006bc51d9130376bf31d9130376bc31d9130376bf70d91300d6be70d9130006bd70d9130006bf50d9130006be50d9130006bd50d9130006bc50d9130376bf30d9130376bc30d91300d6bc6459130005ef7259130005ec7259130004ff7559130014fe7559130004fd7559130014fc75591300d4ff7459130006bf74591300e4ff7359130006df7359130004ff7259130006ef7259130004ef7259130044fc7259130006ec7259130044ec7259130004ff715913001cfc71591300ecff7059130006fb7059130005be76191300d6be7619130004be7619130006bf6519130006be6519130006bd6519130006bc65191300079e53191300079d531913036ebf601913036fbb301913036fb8301913000cfc7650d30006bf6450d3000ebc6450d30005fb7050d30005f87050d30006bf64d8930006bc64d8930004ff75d8930014fe75d8930004fd75d8930014fc75d893000cfe74d8930004fd74d893000cfc74d8930006ef52d8930006ee52d8930006ed52d8930006ec52d8930006ef42d8930006ec42d893001cfe71d8930004fd71d8930006ef65d8930006ee65d8930006ed65d8930006ec65d8930006ef64d8930007af64d8930006af64d8930006ee64d8930006ed64d8930006ec64d8930007ac64d8930006ac64d8930007cf73d8930007ce53d8930007cd53d89302b7eb30d89302b7e830d8930006ef75d8930006ee75d8930006ed75d8930006ec75d8930006ef74d8930006ee74d8930006ed74d8930006ec74d8930006ef54d8930006ee54d8930006ed54d8930006ec54d8930006ef73d89302b6ee73d8930006ef53d89302b6ee53d8930006ed53d89302b6ec53d8930006ef43d89302b6ee43d8930006ed43d89302b6ec43d8930006ef71d8930006ee71d8930006ed71d8930006ec71d8930006ef51d8930006ee51d8930006ed51d8930006ec51d8930006ef41d8930006ec41d89302b6ef31d89302b6ec31d89302b6ef70d8930006ed70d8930006ef50d8930006ee50d8930006ed50d8930006ec50d8930006ef40d8930006ec40d89302b6ef30d89302b6ec30d89300d5be7498930005bd7498930006bf6498930006bc6498930006ef6298930005bf74589300d5bc7458930006bf6458930006bc64589300dd7e75189300057d7518930006bf6418930006bc6418930046ee6218930006ed6218930005ee7618930006ee76189300076e75189300076d7518930006ef6518930006ee6518930006ed6518930006ec6518930006ef6418930007af6418930006af6418930006ee6418930006ed6418930006ec6418930007ac6418930006ac6418930007cd7318930007ce5318930007cd53189302a7eb30189302a7e83018930046ef7518930046ee75189300466e7518930046e
  | 23 => 0x44ff764ca30046ee624ca30006ed624ca3004fcc324ca30005fb704ca30025f8704ca30005dd760ca3004edd760ca3004f5e750ca3004f5d750ca30386df650ca30386dd650ca3004fce720ca3030fcf620ca302eedd620ca3030fcc620ca302efce520ca30387cd520ca30005dd700ca3004fda600ca3030fcc200ca300e5be7498630005bd7498630026f76198630026f461986300057f75586300cd7c7558630026f46158630004ff75586300067f75586300047f7558630014fe7558630004fd7558630014fc75586300067c75586300147c7558630004ff745863000cfe745863000cfc7458630004ff7258630044fc7258630006f65158630006f55158630006f74158630006f44158630024fc7058630026f61058630026f4105863001cff7690630024fe7690630004fd769063000ebe6490630006bd6490630004ff7650630004fd7650630024fc7650630006bf645063000ebc6450630005df735063004ddc735063001ef6618c630006f5618c630025fa708c630005f9708c63001cff764c630005bf744c6300e5bc744c63001ef6614c630006f5614c630005fb704c630025f8704c630044ff76c8630024fe76c8630004fd76c86300cd7e75c86300057d75c863001cff7688630024fe7688630004fd768863004dde7388630005dd738863001ef66188630006f56188630004ff7648630004fd7648630024fc7648630005bf74486300e5bc7448630005df734863004ddc734863001ef66148630006f5614863001cff7608630024fe7608630004fd76086300e5be7408630005bd7408630025fa7008630005f970086300bcff7650230026bf6450230026bc6450230025dd76cc23004edd76cc230026df65cc23037edd65cc2302edde72cc230006dd62cc230027da60cc230027da50cc23037fd950cc23000cfe76d91300d6be64d9130004ff75d9130014fe75d9130004fd75d9130014fc75d9130006bf54d91300d6be54d9130006bd54d91300d6bc54d913004cfe73d91300d4fd73d913004cfc73d91300d6bf43d9130044fe72d9130004fd72d91300d6bf42d91300d6bc42d913001cfe71d9130004fd71d91300d6bf41d91300d6bc41d913004cfd70d91300d6bf40d91300d5be76d913000cbe76d9130006bf65d9130006be65d9130006bd65d9130006bc65d91300079e53d91300079d53d9130377bb30d9130377b830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130006bf73d9130376be73d9130006bd73d9130376bc73d9130006bf53d9130376be53d9130006bd53d9130376bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d9130376bf32d9130376bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d
  | 24 => 0xf6450b3000ebc6450b3004ddf764cb30006df764cb3039ddf754cb3039ddd754cb3004fcf724cb3004fcf624cb30046de624cb30046dc624cb3004fcc624cb30025dc704cb30004ff7558730014fe7558730004fd7558730014fc7558730004ff7458730006bf7458730004bf745873000cfe745873000cfc7458730006bc745873000cbc745873004ede5358730006dd5358730004ff7258730044fc725873004ef7715873004ef7315873004ef4315873001cff769073004cfe7690730004fd7690730396bf649073000ebc6490730004ff7650730004fd765073004cfc765073000ebe6450730006bd6450730044ff76c873004cfe76c8730004fd76c87300f57e75c87300057d75c873004dde73c8730005dd73c873001cff768873004cfe7688730004fd7688730004ff7648730004fd764873004cfc7648730005bf74487300edbc744873001cff760873004cfe7608730004fd76087300edbe7408730005bd740873004dde7308730005dd73087300d4fd7690330376bf649033000ebc6490330005f67190330005f5719033000cff765033004cfc765033000ebe6450330006bd6450330005df735033004ddc7350330024ff75d9230014fe75d9230004fd75d9230024fc75d92300e4fd74d9230026dd73d9230376be43d9230376bc43d9230044fe72d9230004fd72d92300e6bc42d923001cfe71d9230026f671d923001cf671d9230004fd71d9230026f571d9230004f571d92300e6bf41d9230026fa70d9230026bf40d923000cff7659230026bc6459230004ff7559230014fe7559230004fd7559230014fc7559230026bf74592300e6be5459230006bd54592300e6bf4359230004ff7259230044fc72592300e6bf4259230004ff715923001cfc71592300e6bc4159230024fc7059230026be4059230026bc405923000cff7650e30024fc7650e3000ebe6450e30006bd6450e30005fb7050e30025f87050e30026ef6298a30026ec6298a30005bf7458a300e5bc7458a30026ec6258a30004ff7558a30014fe7558a30004fd7558a30014fc7558a30004ff7458a30006bf7458a30004bf7458a3000cfe7458a3000cfc7458a30006bc7458a3000cbc7458a30006ee5258a30006ed5258a30004ff7158a3001cfc7158a30024fc7058a30026ee2058a30026ec2058a30044ff7690a30024fe7690a30004fd7690a30006bf6490a3000ebc6490a30004ff7650a30004fd7650a30024fc7650a3000ebe6450a30006bd6450a30005df7350a3004ddc7350a300e5be748ca30005bd748ca30046ee628ca30006ed628ca30025fa708ca30005f9708ca3038edf658ca3038edd658ca302ef9e748ca302ef9d748ca3004dde728ca302efce628ca302eedd628ca30007cd628ca302efda708ca30005dd708ca302efd9708ca3004ede608ca30
  | 25 => 0xc940004ff764c940004fe764c940004fc764c94000dbe744c940005bd744c940004fe760c940004fd760c940044fc760c9400fd7e750c9400057d750c94000dbe740c940005bd740c940006df630c94004edc630c940006ef620c940046ec620c940007cd320c940005fa700c940005f9700c940004ff75d8540014fe75d8540004fd75d8540014fc75d8540066be54d8540006bd54d854004cfe73d8540004fd73d8540066bf43d8540006bd43d8540044fe72d8540004fd72d8540066bf42d8540006bd42d8540066f641d8540066f541d8540266bc41d8540066bc40d8540006f76198540267b44198540055f970985400057f75585400fd7c7558540005df7358540005dc7358540005ef7258540005ec7258540057b4415854006dfb705854001ef66118540006f56118540265bf75905403b5bd7590540005bd7390540396bc6390540005bd7290540326bc629054000dbe719054000fb67190540266bf6190540007b76190540267b46190540025be7090540267ba7090540267b9709054000ebf609054000fbb6090540004fe76cc540004fd76cc54004cfc76cc5400fd7e75cc5400057d75cc54000dbe74cc540005bd74cc540004fe768c540004fd768c54001cfc768c540265bf748c54000dbc748c540006df638c54004edc638c540004ff764c540004fe764c540004fc764c540005bf744c54000dbc744c540004fe760c540004fd760c54001cfc760c54000dbe740c540005bd740c540006df630c54004edc630c540004fe76c8540004fd76c8540044fc76c85400fd7e75c85400057d75c854000dbe74c8540005bd74c8540004fe7688540004fd768854001cfc7688540265bf748854000dbc7488540006ef6288540046ec6288540004ff7648540004fe7648540004fc7648540005bf744854000dbc7448540004fe7608540004fd760854001cfc760854000dbe7408540005bd7408540006ef6208540046ec6208540025bf75901403adbd7590140005bd7390140376bc6390140005bd72901402febc6290140265be7190140027b67190140005b67190140027b57190140006bf6190140025be7090140027ba7090140026bf609014000fbb6090140004ff7559330014fe7559330004fd7559330014fc755933004ebf745933004cfc735933004ebe435933004ebc4359330004ff7259330044fc72593300eebc4259330004ff715933001cfc71593300eebf41593300eebf4059330004ff7558b30014fe7558b30004fd7558b30014fc7558b30004ff7458b3000cfe7458b3000cfc7458b3004eef7258b3004eef3258b3004eec3258b30004ff7158b3001cfc7158b30044ff7690b3004cfe7690b30004fd7690b3000ebe6490b30006bd6490b3004dde7390b30005dd7390b30004ff7650b30004fd7650b3004cfc7650b303a6b
  | 26 => 0x56f54058640026f44058640026f63058640026f43058640026f62058640026f4205864001cbf76506403cebf65506403cebd6550640375bc7350640006bd63506402fdbc7250640006bd625064000dbf715064000fb7715064001ebe6150640007b6615064001eb66150640007b5615064001ebc6150640005bf7050640007bb7050640007b8705064000ebe605064000fba605064004cff76cc640024fe76cc640004fd76cc6401057e75cc6400057d75cc640375bf74cc64000dbc74cc64001ef661cc640006f561cc64001cff768c640024fe768c640004fd768c64000dbe748c640005bd748c64001ef6618c640006f5618c640004ff764c640004fd764c640024fc764c640005bf744c64000dbc744c64001ef6614c640006f5614c64001cff760c640024fe760c640004fd760c64000dbe740c640005bd740c64001ef6610c640006f5610c640044ff76c8640024fe76c8640004fd76c86401057e75c86400057d75c86402fdbf74c864000dbc74c864001ef661c8640006f561c864001cff7688640024fe7688640004fd768864000dbe7488640005bd748864001ef66188640006f56188640004ff7648640004fd7648640024fc7648640005bf744864000dbc744864001ef66148640006f5614864001cff7608640024fe7608640004fd760864000dbe7408640005bd740864001ef66108640006f56108640004ff75d8d40014fe75d8d40004fd75d8d40014fc75d8d40006de53d8d40006dd53d8d400e6de43d8d400e6dd43d8d40044fe72d8d40004fd72d8d4001cfe71d8d40004fd71d8d40006df6398d400d5f97098d40005ef7258d40005ec7258d400edfb7058d4004ede6318d40006dd6318d4004cbc7650d403c5bf7550d403c5bd7550d4000dbf7350d4000f9f7350d400079f6350d4004ebe6350d4004ebc6350d400079c6350d40005bf7250d40336bc6250d40265bc7150d40007bb7050d40025bc7050d40007b87050d4000ebf6050d4000fbb6050d40004ff75d8940014fe75d8940004fd75d8940014fc75d894004cfe73d8940004fd73d8940006ee52d8940006ed52d89400a6ee42d89400a6ed42d894001cfe71d8940004fd71d8940006ef6298940095f97098940005df7358940005dc73589400adfb7058940046ee6218940006ed6218940044bc76509403bdbf75509403bdbd7550940005bf73509403a6bc635094000dbf725094000faf7250940007af6250940046be6250940046bc6250940007ac6250940265bc7150940007bb7050940025bc7050940007b8705094000ebf605094000fbb6050940004fe76cc940004fd76cc94004cfc76cc94000dbe74cc940005bd74cc940006ef62cc940046ec62cc940004fe768c940004fd768c940044fc768c94000dbe748c940005bd748c940006df638c94004edc638
  | 27 => 0xa700ca40005f9700ca40026f76198640026f46198640026f76598640006f66598640006f56598640026f4659864006fb67498640007b57498640026f76398640006f66398640006f56398640026f46398640007b6439864006fb44398640026f76298640006f66298640006f56298640026f46298640007b6429864006fb44298640027b7409864006ff34098640027f0409864001ef7759864001ef6759864001ef5759864001ef4759864001ef7749864001ef6749864001eb6749864001ef4749864006ef7549864006ef6549864006ef5549864006ef4549864001ef7739864001ef6739864001ef5739864001ef47398640006f75398640006f65398640006f55398640006f4539864006ef7439864006ef64398640006b6439864006ef5439864006ef4439864006eb4439864001ef7729864001ef6729864001ef5729864001ef47298640006f75298640006f65298640006f55298640006f4529864006ef7429864006ef64298640006b6429864006ef5429864006ef4429864006eb44298640006f73298640006f63298640006f53298640006f43298640026f67098640026f47098640006f75098640026f65098640006f55098640026f4509864006ef7409864006eb7409864006ef54098640026f44098640026f63098640026f43098640026f62098640026f42098640026f46158640004ff7558640014fe7558640004fd7558640014fc7558640004ff735864004cfc7358640004ff7258640044fc7258640006f75158640006f65158640006f55158640006f45158640056f64158640056f54158640024fc7058640026f61058640026f41058640025f77658640006f77658640026f76558640006f66558640006f56558640026f46558640057b67458640007b57458640026f76358640006f66358640006f56358640026f46358640007b64358640057b44358640026f76258640006f66258640006f56258640026f46258640007b64258640057b44258640027b74058640057f34058640027f04058640006f77558640006f67558640006f57558640006f47558640056f67458640056f57458640056f47458640056f75458640056f65458640056f55458640056f45458640006f77358640006f67358640006f57358640006f47358640006f75358640006f65358640006f55358640006f45358640056f74358640056f64358640056f54358640056f44358640006f77258640006f67258640006f57258640006f47258640006f75258640006f65258640006f55258640006f45258640056f74258640056f64258640056f54258640056f44258640006f73258640006f63258640006f53258640006f43258640026f67058640026f47058640006f75058640026f65058640006f55058640026f45058640056f74058640026f64058640
  | 28 => 0x8c2101cff7358c2101edf7358c21006de5358c21006dd5358c21044fe7258c21044fc7258c21046de3258c21046dc3258c2101cfe7158c2101cfc7158c2101ede3158c2101edc3158c21004ff7058c21024fc7058c2104cff7690c2101cfe7690c21004fd7690c2101cfc7690c2100ebe6490c21006bd6490c21045ee7290c21005ed7290c21004ff7650c2101cfe7650c21004fd7650c2101cfc7650c2100ebe6450c21006bd6450c21024ff7598021014fe7598021004fd7598021024fc759802100cfe7498021004fd7498021024fc749802104cfe7398021004fd7398021024fe7098021026fa7098021026fa5098021006f95098021046fb2098021026f8209802101efb1098021026f81098021004ff7558021014fe7558021004fd7558021014fc7558021004ff745802100cfe745802100cfc7458021004ff735802104cfc735802101ef62158021046f5215802101efb7058021006fa5058021006f95058021046fb2058021046f8205802101efb105802101ef81058021026df6398e40026dc6398e40026dc6358e40004ff7558e40014fe7558e40004fd7558e40014fc7558e40006de5358e40006dd5358e400d6de4358e400d6dd4358e40376bc4358e40004ff7258e40044fc7258e400d6bc4258e40004ff7158e4001cfc7158e400d6bf4158e40024fc7058e400d6bf4058e40026de3058e40026dc3058e403debf6590e403debd6590e4000dbe7390e4000f9e7390e403779e6390e40376bd6390e400079d6390e402fdbe7290e40005bd7190e4020ebe6190e40377ba7090e40005bd7090e40377b97090e4000ebe6090e4000fba6090e40026ef6298a40026ec6298a40026ec6258a40004ff7558a40014fe7558a40004fd7558a40014fc7558a40004ff7358a4004cfc7358a40006be4358a40096bc4358a40006ee5258a40006ed5258a40096ee4258a40096ed4258a402febc4258a40004ff7158a4001cfc7158a40096bf4158a40024fc7058a40096bf4058a40026ee2058a40026ec2058a403d6bf6590a403d6bd6590a40375be7390a40006bd6390a4000dbe7290a4000fae7290a402ffae6290a402febd6290a40007ad6290a40005bd7190a40206be6190a402ffba7090a40005bd7090a402ffb97090a4000ebe6090a4000fba6090a4004cff76cca40024fe76cca40004fd76cca4000dbe74cca40005bd74cca4004ede63cca40006dd63cca40044ff768ca40024fe768ca40004fd768ca4000dbe748ca40005bd748ca40046ee628ca40006ed628ca40004ff764ca40004fd764ca40024fc764ca40005bf744ca4000dbc744ca4004ede634ca40006dd634ca40046ee624ca40006ed624ca40044ff760ca40024fe760ca40004fd760ca401057e750ca400057d750ca402fdbf740ca4000dbc740ca40007cd320ca40025f
  | 29 => 0x5bd74cc921006bf64cc9211cebc64cc921006df63cc92104edc63cc92101df671cc921005f571cc92101cfc764c921006bf644c9211aebc644c921006df634c92104edc634c921047cc324c921005f7714c92101df4714c92100cff765052111cfd7650521044fc7650521006bf645052100ebc6450521005ef7250521045ec725052101fb44150521044fe76cc521044fc76cc5211257e75cc5210057d75cc521006bf64cc52117ebc64cc521006df63cc52104edc63cc521045ee72cc521005ed72cc52104cff764c521004fd764c521044fc764c521005bf744c52111dbc744c521006bf644c52115ebc644c521006df634c52104edc634c521005ef724c521045ec724c521006bf64d8121006bc64d8121004ff75d8121014fe75d8121004fd75d8121014fc75d812100cfe74d8121004fd74d812100cfc74d812104cfe73d8121004fd73d8121006ee52d8121006ed52d812111dbe7498121005bd7498121006bf6498121006bc6498121006fb60981210057f75581211257c7558121005bf745812111dbc7458121006bf6458121006bc6458121005df7358121005dc7358121006bf6418121006bc6418121006f96018121024ff7518121014fe7518121004fd7518121024fc751812100cfe7418121004fd7418121024fc741812104cfe7318121004fd7318121004ff7559021014fe7559021004fd7559021014fc755902101cff745902101ebf7459021006bf545902110ebe5459021006bd545902110ebc5459021004ff735902104cfc735902110ebf435902110ebc4359021044fe7259021044fc7259021046be4259021046bc425902101cfe715902101cfc715902101ebe415902101ebc4159021004ff7059021024fc705902110ebf405902110ebc4059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006be5359021006bd5359021006bc5359021046bf7259021046be7259021046bd7259021046bc7259021046bf5259021046be5259021046bd5259021046bc5259021046bf3259021046be3259021046bd3259021046bc325902101ebf715902101ebe715902101ebd715902101ebc715902101ebf515902101ebe515902101ebd515902101ebc515902101ebf315902101ebe315902101ebd315902101ebc315902101ebf215902101ebe215902101ebd215902101ebc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf5059021006be5059021006bd5059021006bc5059021046bf2059021046be2059021046bd2059021046bc205902101ebf105902101ebe105902101ebd105902101ebc1059021004ff7558c21014fe7558c21004fd7558c21014fc7558c21004ff7458c2100cfe7458c2100cfc745
  | 30 => 0xd54d912111ebc54d912104cfe73d9121004fd73d912111ebf43d912111ebc43d912101cfd72d912111ebf42d9121044fd71d912111ebf41d9121024fe70d9121004fd70d912111ebf40d912111ebc40d912111dbe76d912100cbe76d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121007ae52d9121007ad52d9121327b721d9121207ae21d9121207ac21d9121327b421d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bd53d9121006bc53d9121206bf72d9121326be72d9121006bd72d9121326bc72d9121006bf52d9121326be52d9121006bd52d9121326bc52d9121326be32d9121326bc32d9121326bf71d9121206be71d9121006bd71d9121206bc71d9121006bf51d9121206be51d9121006bd51d9121206bc51d9121206be31d9121206bc31d9121326bf21d9121206be21d9121206bc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bd50d9121006bc50d9121326bf20d9121326bc20d9121206bf10d9121206bc10d912111ebc6459121004ff7559121014fe7559121004fd7559121014fc755912111cff7459121006bf7459121004ff735912104cfc735912112cff7259121006ef725912113cff7159121006f77159121004ff7059121024fc7059121005be761912111ebe7619121004be7619121006bf6519121006be6519121006bd6519121006bc65191213eebf6219121007ae5219121007ad52191213e6bf61191213e7b721191213efae21191213efac21191213e7b4211912104cfe76d8d21006bf64d8d21006bc64d8d21004ff75d8d21014fe75d8d21004fd75d8d21014fc75d8d2100cfe74d8d21004fd74d8d2100cfc74d8d21006de53d8d21006dd53d8d21024fe70d8d21004fd70d8d211257e7598d210057d7598d2111dbe7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d21005bf7458d2111dbc7458d21006bf6458d21006bc6458d21004ff7558d21014fe7558d21004fd7558d21014fc7558d21004ff7458d21006bf7458d21004bf7458d2100cfe7458d2100cfc7458d21006bc7458d2100cbc7458d21006df7358d21004ff7258d21006ef7258d21004ff7158d21006f77158d21004ff7058d21024fc7058d21004fe7618d21006bf6418d21006bc6418d2104ede6318d21006dd6318d2104cff7690d21004fe7690d21004fd7690d2104cfc7690d21006bf6490d2100ebc6490d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2100ebc6450d2101cfc7650921006bf645092100ebc6450921005f7715092101df4715092101cfe76cc92101cfc76cc92111dbe74cc921
  | 31 => 0x721005ef7250721045ec72507211457e75cc7210057d75cc7211867e65cc7210067d65cc72104ede63cc721006dd63cc721045ee72cc721005ed72cc72104cff764c7211667e654c7210067d654c721005bf744c72113dbc744c72104ede634c721006dd634c721005ef724c721045ec724c721024ff7598321014fe7598321004fd7598321024fc759832100cfe7498321004fd7498321024fc749832104cfe7398321004fd739832101cfe7298321026fa7098321046fb2098321026f82098321004ff7558321014fe7558321004fd7558321014fc7558321004ff7458321006bf7458321004bf745832100cfe745832100cfc7458321006bc745832100cbc7458321004ff735832104cfc735832101cfc7258321046ee5258321006ed5258321046f62158321046f52158321046fb7058321046fb2058321046f82058321004ff7559221014fe7559221004fd7559221014fc755922101ebf745922112ebe5459221006bd5459221004ff735922104cfc735922112ebf435922112ebf425922101cfc715922101ebe415922101ebc4159221004ff7059221024fc705922112ebc4059221004ff7558e21014fe7558e21004fd7558e21014fc7558e21004ff7458e21006bf7458e21004bf7458e2100cfe7458e2100cfc7458e21006bc7458e2100cbc7458e2101edf7358e21006de5358e21006dd5358e2101cfc7158e2101ede3158e2101edc3158e21004ff7058e21024fc7058e2101ef71058e2104cff7690e2101cfe7690e21004fd7690e2101cfc7690e2120ebf6490e2100ebc6490e2104ede6390e21006dd6390e21045ee7290e21005ed7290e21004ff7650e2101cfe7650e21004fd7650e2101cfc7650e2100ebe6450e21006bd6450e2104ede6350e21006dd6350e2100cff7650a2101cfc7650a2100ebe6450a21006bd6450a21005f77150a2101df47150a2112dbe74cca21005bd74cca2104ede63cca21006dd63cca2101df671cca21005f571cca2104cff764ca2104ede634ca21006dd634ca21047cc324ca21005f7714ca2101df4714ca21024ff7598221014fe7598221004fd7598221024fc759822100cfe7498221026be749822100cbe7498221004fd7498221026bd7498221004bd7498221024fc749822104cfe7398221004fd739822101cfe719822101cf67198221026fa7098221026fa5098221006f95098221026f7109822101efb1098221026f81098221004ff7558221014fe7558221004fd7558221014fc7558221004ff745822100cfe745822100cfc7458221004ff735822104cfc735822101cfc715822101efb7058221006fa5058221006f9505822101efb105822101ef8105822100cfe76d912111ebe64d9121004ff75d9121014fe75d9121004fd75d9121014fc75d9121006bf54d912111ebe54d9121006b
  | 32 => 0x6bc505903104ebf305903104ebe305903104ebd305903104ebc305903101ebf105903101ebe105903101ebd105903101ebc1059031004ff7558831014fe7558831004fd7558831014fc7558831004ff745883100cfe745883100cfc745883101eef7258831006ee5258831006ed525883104eef325883104eec325883101eee215883101eec2158831004ff7058831024fc7058831044ff769083101cfe7690831004fd769083100ebe6490831006bd649083104dde7390831005dd7390831004ff7650831004fd765083101cfc765083100ebe6450831006bd6450831024ff7598031014fe7598031004fd7598031024fc759803100cfe7498031004fd7498031024fc7498031044fe7298031004fd7298031024fe7098031026fa7098031026fa5098031006f9509803104efb3098031026f8309803101efb1098031026f81098031004ff7558031014fe7558031004fd7558031014fc7558031004ff745803100cfe745803100cfc7458031004ff7258031044fc725803101ef6315803104ef5315803101efb7058031006fa5058031006f9505803104efb305803104ef8305803101efb105803101ef810580310067f74597210067e74597210067d74597210067c74597210067f73597210067e73597210067d73597210067c73597210067f43597210067c43597210467f72597210467e72597210467d72597210467c72597210467f42597210467e42597210467d42597210467c42597210467f32597210467e32597210467d32597210467c32597211467f71597213f67e71597210067d71597213f67c71597210067f41597213f67e41597213f67c41597213f67e31597213f67c31597210467f21597210467e21597210467d21597210467c21597210067f70597210067e70597210067d70597210067c70597210067f40597210067c40597210467f20597210467e20597210467d20597210467c20597213f67f10597213f67c1059721004ff7559321014fe7559321004fd7559321014fc7559321046bf7459321004ff735932104cfc735932113ebc435932101cfc7259321046be4259321046bc425932113ebf4159321004ff7059321024fc705932113ebf4059321004ff7558f21014fe7558f21004fd7558f21014fc7558f21004ff7458f2100cfe7458f2100cfc7458f21046df7358f21006df4358f21006dc4358f2101cfc7258f21046de3258f21046dc3258f21004ff7058f21024fc7058f2104cff7690f21044fe7690f21004fd7690f21044fc7690f211f67e6590f210067d6590f2100ebe6490f21006bd6490f21004ff7650f21044fe7650f21004fd7650f21044fc7650f211ee7e6550f210067d6550f21336bf6450f2100ebc6450f2100cff7650721044fc765072118e7e65507210067d655072100ebe6450721006bd645
  | 33 => 0xe75d8931004fd75d8931014fc75d893100cfe74d8931004fd74d893100cfc74d8931006ee52d8931006ed52d8931024fe70d8931004fd70d89311657e75989310057d759893115dbe7498931005bd7498931006bf6498931006bc6498931006ef6298931005bf745893115dbc7458931006bf6458931006bc6458931006bf6418931006bc6418931046ee6218931006ed6218931004fe7690931004fd7690931044fc7690931006bf649093100ebc6490931004ff7650931004fe7650931004fc7650931006bf645093100ebc645093101cfe768c93115dbe748c931005bd748c931006bf648c9311bebc648c931006ef628c931046ec628c93101df6718c931005f5718c93101cfc764c931006bf644c9311aebc644c931006ef624c931046ec624c93104fcc324c931005f7714c93101df4714c93100cff765053115cfd765053104cfc7650531006bf645053100ebc6450531005df735053104ddc735053101fb44150531006bf64d8131006bc64d8131004ff75d8131014fe75d8131004fd75d8131014fc75d813100cfe74d8131004fd74d813100cfc74d8131006de53d8131006dd53d8131044fe72d8131004fd72d813115dbe7498131005bd7498131006bf6498131006bc6498131006fb60981310057f75581311657c7558131005bf745813115dbc7458131006bf6458131006bc6458131005ef7258131005ec7258131006bf6418131006bc6418131006f96018131024ff7518131014fe7518131004fd7518131024fc751813100cfe7418131004fd7418131024fc7418131044fe7218131004fd7218131004ff7559031014fe7559031004fd7559031014fc755903101cff745903101ebf7459031006bf545903114ebe5459031006bd545903114ebc545903104cfe735903104cfc735903104ebe435903104ebc4359031004ff7259031044fc725903114ebf425903114ebc425903101cfe715903101cfc715903101ebe415903101ebc4159031004ff7059031024fc705903114ebf405903114ebc4059031006bf7559031006be7559031006bd7559031006bc755903104ebf735903104ebe735903104ebd735903104ebc735903104ebf535903104ebe535903104ebd535903104ebc5359031006bf7259031006be7259031006bd7259031006bc7259031006bf5259031006be5259031006bd5259031006bc525903104ebf325903104ebe325903104ebd325903104ebc325903101ebf715903101ebe715903101ebd715903101ebc715903101ebf515903101ebe515903101ebd515903101ebc515903101ebf315903101ebe315903101ebd315903101ebc315903101ebf215903101ebe215903101ebd215903101ebc2159031006bf7059031006be7059031006bd7059031006bc7059031006bf5059031006be5059031006bd5059031
  | 34 => 0xa31006bd6450a31046ee6250a31006ed6250a3116dbe748ca31005bd748ca31046ee628ca31006ed628ca3101df6718ca31005f5718ca31044ff764ca31046ee624ca31006ed624ca3104fcc324ca31005f7714ca3101df4714ca31024ff7598231014fe7598231004fd7598231024fc759823100cfe7498231026be749823100cbe7498231004fd7498231026bd7498231004bd7498231024fc7498231044fe7298231004fd729823101cfe719823101cf67198231026fa7098231026fa5098231006f95098231026f7109823101efb1098231026f81098231004ff7558231014fe7558231004fd7558231014fc7558231004ff745823100cfe745823100cfc7458231004ff7258231044fc725823101cfc715823101efb7058231006fa5058231006f9505823101efb105823101ef8105823100cfe76d913115ebe64d9131004ff75d9131014fe75d9131004fd75d9131014fc75d9131006bf54d913115ebe54d9131006bd54d913115ebc54d913101cfd73d913115ebf43d9131044fe72d9131004fd72d913115ebf42d913115ebc42d913104cfd71d913115ebf41d9131024fe70d9131004fd70d913115ebf40d913115ebc40d913115dbe76d913100cbe76d9131006bf65d9131006be65d9131006bd65d9131006bc65d91310079e53d91310079d53d9131397b731d913120f9e31d913120f9c31d9131397b431d9131006bf75d9131006be75d9131006bd75d9131006bc75d913120ebf73d9131396be73d9131006bd73d9131396bc73d9131006bf53d9131396be53d9131006bd53d9131396bc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006be52d9131006bd52d9131006bc52d9131396bf32d9131396bc32d9131396bf71d913120ebe71d9131006bd71d913120ebc71d9131006bf51d913120ebe51d9131006bd51d913120ebc51d9131396bf31d913120ebe31d913120ebc31d913120ebe21d913120ebc21d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d9131396bf30d9131396bc30d913120ebf10d913120ebc10d913115ebc6459131004ff7559131014fe7559131004fd7559131014fc755913115cff7459131006bf745913116cff7359131006df7359131004ff7259131044fc725913117cff7159131006f77159131004ff7059131024fc7059131005be761913115ebe7619131004be7619131006bf6519131006be6519131006bd6519131006bc6519131406bf63191310079e53191310079d53191313febf61191313ffb731191314079e31191314079c31191313ffb4311913101cfc7650d31006bf6450d3100ebc6450d31005f77150d3101df47150d31006bf64d8931006bc64d8931004ff75d8931014f
  | 35 => 0x4e7f325973104e7e325973104e7d325973104e7c32597311867f715973140e7e71597310067d715973140e7c71597310067f415973140e7e415973140e7c415973104e7f315973104e7e315973104e7d315973104e7c315973140e7e215973140e7c21597310067f70597310067e70597310067d70597310067c70597310067f40597310067c405973104e7f305973104e7e305973104e7d305973104e7c305973140e7f105973140e7c1059731004ff7559331014fe7559331004fd7559331014fc755933104ebf745933101cfc735933104ebe435933104ebc4359331004ff7259331044fc725933117ebc425933117ebf4159331004ff7059331024fc705933117ebf4059331004ff7558b31014fe7558b31004fd7558b31014fc7558b31004ff7458b3100cfe7458b3100cfc7458b3101cfc7358b3104eef7258b31006ef4258b31006ec4258b3104eef3258b3104eec3258b31004ff7058b31024fc7058b31044ff7690b3104cfe7690b31004fd7690b311e67e6590b310067d6590b3100ebe6490b31006bd6490b31004ff7650b31004fd7650b3104cfc7650b311de7e6550b310067d6550b313a6bf6450b3100ebc6450b3100cff765073104cfc765073118e7e65507310067d655073100ebe6450731006bd6450731005df735073104ddc7350731024ff7598331014fe7598331004fd7598331024fc759833100cfe7498331004fd7498331024fc749833101cfe7398331044fe7298331004fd7298331026fa709833104efb3098331026f83098331004ff7558331014fe7558331004fd7558331014fc7558331004ff7458331006bf7458331004bf745833100cfe745833100cfc7458331006bc745833100cbc745833101cfc735833104ede5358331006dd5358331004ff7258331044fc725833104ef6315833104ef5315833104efb705833104efb305833104ef83058331004ff7559231014fe7559231004fd7559231014fc755923101ebf745923116ebe5459231006bd545923116ebf4359231004ff7259231044fc725923116ebf425923101cfc715923101ebe415923101ebc4159231004ff7059231024fc705923116ebc405923100cff7650e3101cfc7650e3100ebe6450e31006bd6450e31005f77150e3101df47150e31004ff7558a31014fe7558a31004fd7558a31014fc7558a31004ff7458a31006bf7458a31004bf7458a3100cfe7458a3100cfc7458a31006bc7458a3100cbc7458a3101eef7258a31006ee5258a31006ed5258a3101cfc7158a3101eee2158a3101eec2158a31004ff7058a31024fc7058a3101ef71058a31044ff7690a3101cfe7690a31004fd7690a31206bf6490a3100ebc6490a3104dde7390a31005dd7390a31046ee6290a31006ed6290a31004ff7650a31004fd7650a3101cfc7650a3100ebe645
  | 36 => 0xd74d8d41006de53d8d41006dd53d8d4116ede43d8d4116edd43d8d41044fe72d8d41004fd72d8d41024fe70d8d41004fd70d8d4118d7e7598d410057d7598d4120ebf6498d41006df6398d41005ee7298d41005ed7298d4115df57198d4117df77158d41406bf6418d4104ede6318d41006dd6318d4101cbc7650d4141dbf7550d4141dbd7550d4100dbf7350d4100f9f7350d410079f6350d4104ebe6350d4104ebc6350d410079c6350d41005bf7250d41336bc6250d41007b77150d4101dbe7150d4101dbc7150d41007b47150d4100ebf6150d4100fb76150d41005bc7050d41004ff75d8941014fe75d8941004fd75d8941014fc75d894101cfd74d894104cfe73d8941004fd73d8941006ee52d8941006ed52d894112eee42d894112eed42d8941024fe70d8941004fd70d894118d7e75989410057d7598941206bf6498941005de7398941005dd7398941006ef629894111df5719894113df771589413eebf6418941046ee6218941006ed621894101cbc7650941415bf7550941415bd7550941005bf73509413a6bc635094100dbf725094100faf7250941007af6250941046be6250941046bc6250941007ac6250941007b7715094101dbe715094101dbc7150941007b4715094100ebf615094100fb76150941005bc7050941004fe76cc941004fd76cc94104cfc76cc94100dbe74cc941005bd74cc941006df63cc94104edc63cc941004fe768c941004fd768c941044fc768c94100dbe748c941005bd748c941006ef628c941046ec628c941004ff764c941004fe764c941004fc764c94100dbe744c941005bd744c941006df634c94104edc634c941006ef624c941046ec624c941004fe760c941004fd760c941044fc760c94118d7e750c9410057d750c94100dbe740c941005bd740c941007cd320c94101df6710c941005f5710c941004ff75d8141014fe75d8141004fd75d8141014fc75d814101cfd74d814106ebe54d8141006bd54d814104cfe73d8141004fd73d814106ebf43d8141006bd43d8141044fe72d8141004fd72d814106ebf42d8141006bd42d814106ef741d814127ebe41d814127ebc41d814106ef441d814106efa40d814106ebc40d8141006fb60981410057f755814118d7c7558141005df7358141005dc7358141005ef7258141005ec7258141006f96018141024ff7518141014fe7518141004fd7518141024fc751814101cfd741814104cfe7318141004fd7318141044fe7218141004fd7218141026fa401814102ef940181410067f74597310067e74597310067d74597310067c745973104e7f735973104e7e735973104e7d735973104e7c735973104e7f435973104e7e435973104e7d435973104e7c43597310067f72597310067e72597310067d72597310067c72597310067f42597310067c4259731
  | 37 => 0x8032014fc7558032004ff7458032006bf7458032004bf745803200cfe745803200cfc7458032006bc745803200cbc745803204ede5358032006dd5358032046ee5258032006ed5258032046df3258032046ee3258032046dd325803204eed3258032006cd3258032004ff715803201cfc7158032046fb705803204efb305803204edc305803204ef83058032046fb2058032046ec2058032046f82058032004ff7558e41014fe7558e41004fd7558e41014fc7558e4101edf7358e41006de5358e41006dd5358e4115ede4358e4115edd4358e41396bc4358e41004ff7258e41044fc7258e4115ebc4258e4101cfc7158e4101ebf4158e4101ebd4158e4101ede3158e4101edc3158e41004ff7058e41024fc7058e4115ebf4058e4120ebf6590e4142ebd6590e4100dbe7390e4100f9e7390e4120ebf6390e4120f9e6390e41396bd6390e4120f9d6390e41325be7290e4120fb67190e4120dbd7190e41397b57190e4100ebe6190e4100fb66190e41005bd7090e41004ff7558a41014fe7558a41004fd7558a41014fc7558a41004ff7358a4104cfc7358a41006be4358a4111ebc4358a4101eef7258a41006ee5258a41006ed5258a4111eee4258a4111eed4258a41326bc4258a4101cfc7158a4101ebf4158a4101ebd4158a4101eee2158a4101eec2158a41004ff7058a41024fc7058a4111ebf4058a41206bf6590a41426bd6590a41395be7390a41006bd6390a4100dbe7290a4100fae7290a41206bf6290a41207ae6290a41326bd6290a41207ad6290a41207b67190a41205bd7190a41327b57190a4100ebe6190a4100fb66190a41005bd7090a4104cff76cca4101cfe76cca41004fd76cca4100dbe74cca41005bd74cca41044ff768ca4101cfe768ca41004fd768ca4100dbe748ca41005bd748ca41004ff764ca41004fd764ca4101cfc764ca41005bf744ca4100dbc744ca41044ff760ca4101cfe760ca41004fd760ca411957e750ca410057d750ca41325bf740ca4100dbc740ca41007cd320ca4101df6710ca41005f5710ca41024ff7598241014fe7598241004fd7598241024fc759824104cfe7398241004fd7398241006be4398241066bc4398241044fe7298241004fd7298241006be4298241066bc429824101cfe7198241024fc719824101ebf419824101ebd4198241026fa7098241026fa5098241006f95098241026bf4098241026fa4098241066f9409824101efb1098241026f81098241004ff7558241014fe7558241004fd7558241014fc7558241004ff735824104cfc7358241004ff7258241044fc725824101cfc7158241056f7415824101ef4415824101efb7058241006fa5058241006f95058241056fa405824101efb105824101ef81058241004ff75d8d41014fe75d8d41004fd75d8d41014fc75d8d4101cf
  | 38 => 0x4fd7118132026f57118132004f571181320067f74594320067e74594320067d74594320067c745943204e7f735943204e7e735943204e7d735943204e7c735943204e7f435943204e7e435943204e7d435943204e7c43594320467f72594320467e72594320467d72594320467c72594320467f42594320467e42594320467d42594320467c42594320467f32594320467e32594320467d32594320467c32594320067f71594320067e71594320067d71594320067c71594320067f41594320067c415943204e7f315943204e7e315943204e7d315943204e7c31594320467f21594320467e21594320467d21594320467c21594320067f70594320067e70594320067d70594320067c70594320067f40594320067c405943204e7f305943204e7e305943204e7d305943204e7c30594320467f20594320467e20594320467d20594320467c2059432004ff7559032014fe7559032004fd7559032014fc7559032044ff7459032046bf745903204cfe735903204cfc735903204ebe435903204ebc4359032044fe7259032044fc7259032046be4259032046bc4259032004ff715903201cfc715903219ebf4159032004ff7059032024fc705903219ebf4059032047cf764c832045cf764c832006cf764c832447cf754c832445cf754c83243fce754c832447cd754c832445cd754c83243fcc754c832047cf654c832047ce654c8320474e654c832047cd654c8320474d654c832047cc654c832007cf744c832437ce744c832007cd744c832437cc744c832047cf644c832047ce644c832047cd644c832047cc644c83243fcf544c832437ce544c83243fcd544c832437cc544c832007cf714c832007ce714c832007cd714c832007cc714c832047cf614c832047ce614c832047cd614c832047cc614c83243fcf514c83243fce514c83243fcd514c83243fcc514c832437cf414c832437cc414c832007cf704c832007ce704c832007cd704c832007cc704c832005cc704c832047cf604c832047ce604c832047cd604c832047cc604c83243fcf504c83243fce504c83243fcd504c83243fcc504c832437cf404c832437cc404c832004ff7558432014fe7558432004fd7558432014fc7558432004ff7458432006bf7458432004bf745843200cfe745843200cfc7458432006bc745843200cbc745843204ede5358432006dd5358432046ee5258432006ed5258432046f7715843204ef7315843204ef43158432046f72158432046f42158432004ff7058432024fc7058432024ff7598032014fe7598032004fd7598032024fc759803200cfe7498032004fd7498032024fc749803201cfe7198032004fd7198032024fe7098032026fa709803204efb3098032026f83098032046fb2098032026f82098032004ff7558032014fe7558032004fd755
  | 39 => 0xe6450e32006bd6450e32005ef7250e32045ec7250e32004ff7558632014fe7558632004fd7558632014fc7558632004ff745863200cfe745863200cfc7458632006de5358632006dd5358632044fc7258632046f77158632006f75158632006f45158632046f72158632046f42158632004ff7058632024fc7058632024ff7598232014fe7598232004fd7598232024fc759823200cfe7498232004fd7498232024fc7498232044fe7298232044ee72982322b6ef3298232046ec329823201cfe7198232004fd7198232026fa7098232026ef2098232046fb2098232026f82098232004ff7558232014fe7558232004fd7558232014fc7558232004ff745823200cfe745823200cfc7458232006de5358232006dd5358232044fc7258232046df3258232046dd3258232004ff715823201cfc7158232046fb7058232046fb2058232046f8205823200cfe76d91321aebe64d9132004ff75d9132014fe75d9132004fd75d9132014fc75d91321aebe54d9132006bd54d9132044fd73d91321aebf43d913204cfd72d91321aebf42d913201cfe71d9132004fd71d91321aebc41d9132024fe70d9132004fd70d91321aebc40d91321aebc6459132004ff7559132014fe7559132004fd7559132014fc75591321acff7459132006bf74591321bcff7359132006df73591323a6be43591323a6bc43591321ccff7259132006ef7259132336be4259132336bc4259132004ff715913201cfc71591321aebf4159132004ff7059132024fc70591321aebf4059132044fc7650d32006bf6450d3200ebc6450d32005ef7250d32045ec7250d3204fcc3250d3200cff76509321acfd765093204cfc7650932006bf645093200ebc6450932005df735093204ddc7350932047cc32509321b57e75d85320057d75d8532004ff75d8532014fe75d85320067e75d85320147e75d8532004fd75d85320067d75d85320047d75d8532014fc75d853200cfe74d8532004fd74d853200cfc74d8532024fe70d8532004fd70d8532006f76198532005bf74585321adbc74585321adbe7418532005bd741853201ef66118532006f56118532004ff75d8132014fe75d8132004fd75d8132014fc75d813200cfe74d8132004fd74d813200cfc74d813201cfe71d8132004fd71d8132006fb6098132005bf74581321adbc74581321b57e75181320057d75181321adbe7418132005bd7418132005f67118132005f57118132006f96018132024ff7518132014fe75181320267e75181320147e7518132004fd75181320267d75181320047d7518132024fc751813200cfe7418132026be741813200cbe7418132004fd7418132026bd7418132004bd7418132024fc74181322a6ef32181322e6de32181322e6dc32181322a6ec321813201cfe7118132026f6711813201cf67118132
  | 40 => 0x9332006bd7259332336bc7259332006bf5259332336be5259332006bd5259332336bc525933204ebf325933204ebe325933204ebd325933204ebc3259332006bf7159332006be7159332006bd7159332006bc7159332006bf5159332006be5159332006bd5159332006bc515933204ebf315933204ebe315933204ebd315933204ebc3159332336bf2159332336bc2159332006bf7059332006be7059332006bd7059332006bc7059332006bf5059332006be5059332006bd5059332006bc505933204ebf305933204ebe305933204ebd305933204ebc3059332336bf2059332336bc205933200cff7650b3204cfc7650b3200ebe6450b32006bd6450b32005df7350b3204ddc7350b32004ff7558732014fe7558732004fd7558732014fc7558732004ff745873200cfe745873200cfc7458732044fc7358732006ee5258732006ed525873204ef77158732006f75158732006f4515873204ef7315873204ef43158732004ff7058732024fc7058732024ff7598332014fe7598332004fd7598332024fc759833200cfe7498332004fd7498332024fc7498332044fe7398332044de73983322eede329833204edc329833201cfe7198332004fd7198332026fa7098332026df309833204efb3098332026f83098332004ff7558332014fe7558332004fd7558332014fc7558332004ff745833200cfe745833200cfc7458332044fc7358332006ee5258332006ed525833204eee325833204eed3258332004ff715833201cfc715833204efb705833204efb305833204ef83058332004ff7559232014fe7559232004fd7559232014fc7559232046bf7459232006bf54592321bebe5459232006bd54592321bebc54592321bebf4359232044fc7259232046be4259232046bc4259232004ff715923201cfc71592321bebf41592321bebc4159232004ff7059232024fc70592321bebf40592321bebc4059232006bf7559232006be7559232006bd7559232006bc7559232006bf73592323a6be7359232006bd73592323a6bc7359232006bf53592323a6be5359232006bd53592323a6bc5359232046bf7259232046be7259232046bd7259232046bc7259232046bf5259232046be5259232046bd5259232046bc5259232046bf3259232046be3259232046bd3259232046bc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf5159232006be5159232006bd5159232006bc51592323a6bf31592323a6bc3159232046bf2159232046be2159232046bd2159232046bc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bd5059232006bc50592323a6bf30592323a6bc3059232046bf2059232046be2059232046bd2059232046bc205923200cff7650e32044fc7650e3200eb
  | 41 => 0x44fc7258642046bf4258642046bd4258642046f7715864211ef64158642206bc4158642046f72158642046f42158642004ff7058642024fc705864211ebc4058642024ff7598242014fe7598242004fd7598242024fc759824204cfe7398242004fd7398242044fe7298242024fc729824201cfe7198242004fd7198242026fa7098242026fa40982420a6f94098242046fb2098242026f82098242004ff7558242014fe7558242004fd7558242014fc7558242096be5458242006bd5458242004ff735824204cfc7358242096bf4358242006bd4358242044fc7258242046bf4258242046bd4258242004ff715824201cfc7158242096bc4158242046fb7058242096fa4058242096bc4058242046fb2058242046f82058242004ff75d8d42014fe75d8d42004fd75d8d42014fc75d8d42044fd74d8d42006de53d8d42006dd53d8d421bede43d8d421bedd43d8d423a6bc43d8d42456be42d8d42456bc42d8d4201cfe71d8d42004fd71d8d421bebf41d8d42024fe70d8d42004fd70d8d421bebf40d8d42006df6398d421aded7298d421cdef7258d4204ede6318d42006dd6318d42044be7690d4244ebf6590d4244ebd6590d4200dbe7390d4200f9e7390d423a6bf6390d420079f6390d423a79c6390d42045be7290d423a7ae7290d423a7ad7290d42045bc7290d4200ebf6290d4200faf6290d42005bd7190d4220ebc6190d42005bd7090d42004ff75d8542014fe75d8542004fd75d8542014fc75d8542044fd74d854204cfe73d8542004fd73d8542006f751d8542006f451d854213ef641d8542024fe70d8542004fd70d8542006f76198542206bf641854201ef66118542006f56118542004ff75d8142014fe75d8142004fd75d8142014fc75d8142044fd74d814204cfe73d8142004fd73d814201cfe71d8142004fd71d81420aefa40d8142005f67198142005f57198142006fb6098142005df7358142005dc7358142006f96018142024ff7518142014fe7518142004fd7518142024fc7518142044fd741814204cfe7318142004fd7318142006be431814207ebc43181422f6be42181422f6bc421814201cfe7118142004fd711814207ebf4118142026bf4018142026fa401814207ef94018142004ff7559332014fe7559332004fd7559332014fc755933204ebf7459332006bf54593321cebe5459332006bd54593321cebc5459332044fc735933204ebe435933204ebc43593321cebf4259332004ff715933201cfc71593321cebf41593321cebc4159332004ff7059332024fc70593321cebf40593321cebc4059332006bf7559332006be7559332006bd7559332006bc755933204ebf735933204ebe735933204ebd735933204ebc735933204ebf535933204ebe535933204ebd535933204ebc5359332006bf7259332336be725
  | 42 => 0xf3258a4304eec3258a43004ff7158a4301cfc7158a43004ff7058a43024fc7058a43004ff7558643014fe7558643004fd7558643014fc755864315ebe5458643006bd545864304cfc735864304ebf435864304ebd4358643004ff7258643044fc725864315ebf425864304ef7715864315ef6415864320ebc415864304ef7315864304ef43158643004ff7058643024fc705864315ebc4058643024ff7598243014fe7598243004fd7598243024fc759824304cfe7398243024fc7398243044fe7298243004fd729824301cfe7198243004fd7198243026fa7098243026fa40982430e6f9409824304efb3098243026f83098243004ff7558243014fe7558243004fd7558243014fc75582430d6be5458243006bd545824304cfc735824304ebf435824304ebd4358243004ff7258243044fc72582430d6bf4258243004ff715824301cfc71582430d6bc415824304efb70582430d6fa40582430d6bc405824304efb305824304ef83058243004ff75d8943014fe75d8943004fd75d8943014fc75d894304cfd74d8943466be43d8943466bc43d8943006ee52d8943006ed52d89431ceee42d8943336bc42d894301cfe71d8943004fd71d89431cebf41d8943024fe70d8943004fd70d89431cebf40d8943006ef6298943046ee6218943006ed6218943004ff75d8543014fe75d8543004fd75d8543014fc75d854304cfd74d8543044fe72d8543004fd72d8543006f751d8543006f451d854317ef641d8543024fe70d8543004fd70d8543006f7619854320ebf641854301ef66118543006f56118543004ff75d8143014fe75d8143004fd75d8143014fc75d814304cfd74d8143044fe72d8143004fd72d814301cfe71d8143004fd71d81430eefa40d8143005f67198143005f57198143006fb6098143005ef7258143005ec7258143006f96018143024ff7518143014fe7518143004fd7518143024fc751814304cfd741814336ebe431814336ebc4318143044fe7218143004fd72181430bebc421814301cfe7118143004fd71181430bebf4118143026bf4018143026fa40181430bef94018143004ff7558e42014fe7558e42004fd7558e42014fc7558e42046df7358e42006de5358e42006dd5358e421aede4358e421aedd4358e42044fc7258e42046de3258e42046dc3258e42004ff7158e4201cfc7158e42004ff7058e42024fc7058e4204cbf7650e4245dbf7550e4245dbd7550e4200dbf7350e4200f9f7350e4204ebe6350e423379e6350e423379d6350e4204ebc6350e42335bf7250e42007af7250e42337ac7250e4200ebe6250e4200fae6250e42205bc7150e42005bc7050e42004ff7558642014fe7558642004fd7558642014fc755864211ebe5458642006bd5458642004ff735864204cfc735864211ebf4358642006bd4358642
  | 43 => 0x4004000c002000c00600040020008001000001a0004003000c00000000010000004000000c00080010000000000000000000050008005000000f002801800080080008000000000100000000000000001000000400030010000008800300080030024006001400b000400400080000004006000c00a0000021000000000000010020000001c002004000200080000018009000000000140000054000000c004001401700000010000012000800500300060000006000400000040000000000001c000000c01f0008003003c001001c005002000000140010018000002c00d0008000001400000040000000010000000600000010034000001000000000010004000000400100200030014000000000000080020014000003000000140030048000000800000440000000003003c0020020004000c0000038015000800500340070018008001c003000000200600000008016003c000000000000000030004002001c00200200090000004001800000140030004001003c0010004008000000700000000000000000c004000c00000280000020003000001600040050000000000000a000000a0000003000000000040010000000008c002001c00000040010010004000000100000000014010000000100700030008003000400000000000008006000800300000100004002003c000006c00e00200010004008005001200200000078001000c001002400100080120030001009801a0000006003000100000020004010000c01b00000000024007000000a00100010000000000400a0024002000c00300080000030007000000d000000500000040000004000c005000000b0008004000c002002c00900000000010002000c00500180060000003000c0000004001001c0000000003005000b000c00300000090038006001c005000400000100000008001005400100000080000000000401100000000004002000001300040000010004001400700100010010001003c0010000000001c003000c00100040010024001000c000001c00200000000000001000c00a007400b000000600000000000001000000a00000000018004000c00000140020010000000000300000030008002002401000180040014000000400400000000000019000400600000040000000001000000000000000003000c003001800000000010000001000400e005c005001c0000004001000000000000060000001000000c0008001000400b0018018000400100080000000002000c000000c000000000100080060004001000000500040050004000001400000040050000013000001400040030000002000000000140020000004004ff7558a43014fe7558a43004fd7558a43014fc7558a4304cfc7358a4304eef7258a43006ee5258a43006ed5258a431aeee4258a4304ee
  | 44 => 0x28003001000100d0001000000000040000000000000400a000001600080030014001000000c000400a000001100180100010000000400a000400500000000000007000000500100050010001000400600540010000004000c014003c0030004007001c0020014000000801000000020038005000000300040010014000006000d0000000000000f0000005000c007002400700500010004002000c00500d40000014002005400900480040000000003000900000010008000000c001001c00200100010000006001000400140000008001001c00000000190040004000c02800100080008010000000800140040034001000400900000060000001000c0020034003000400a001400f00440030008001000000d0028013003000100000030000000001000100300010008003000c00000000020010004000400200040010000000005c00000000000000000000000000040000000000000c00e000000b000000200000070000006000000500000000000009001400600040000008005000000b0000001000000100240040004000000c00200000030000004004800b00080000004004002000f00080000008000000c0010010000008400c00180010024004001000900180000020002003000e00080010004009000000000180160000004000400c00000000004002001800900000020004002000c0000008002000400d000000800040000000003000000000000080008004002c00b001c0010000001000c000000400000480000018001000c0190000006004c01000080010000004009c013000c0110000010000000600100010000000000400b000400300000000000002000c0050000004000c007000c0070000000005c0050000002001800b000400000180100008001000c00300000010000000000c0010000000001c0000010000000c003001c00e002c0010000000001400400000030000000002000000ec0020000002000c001003c001000c00000040050010009001800100000050000001000400400340000000008000001e005800e0014003000400000000000034001000c0060010005000c00f000c021000001200140050028035000001800140000000007000c00f00200000000004001c00400000010008002000400400200000008008000c00d002c006002800000040010004009000400e0014001003800d005c00200000050024006000000900180000004000000400100080020028007002400000040150004010000400400240080000018000801500000000018000000400800500000004000000c0020018007000800000740010004006001800000300000000000000000b0004004000c000006400000100050010004000000000440010008003002c0020000003000400700000000010001000000a00140010010000000
  | 45 => 0x25001c003000000e00300000010000000000100040000000009004000100000000028000000400000000100020009000c00100600010018002002c0020000003000c00500040000004004000c0000000012000001e00000020014013001401b00040050004001001400200000180000001001401c000000200200000000003000400500100020004000000c0000004001000c00300880000008003000000200000020004000001000000000030010000001c00200100000000007000400900440030028004001400000040020004002000000b000400000280020040001000000000100000004000001c003002400e001c00f0014000000c001000c00c00000010004005000000700040010004001002c000000400000000030000001000400d002000700080040004000000000a000400700040020000000000400500280000000002000c00d002c00700000000008004000000000080050000001001400100000000000007000001000100040024002000c001002000400200080008000000000e000000300040000008004000000f0000002000000300000080018000001c00e00000010000000000c002001400b0008008001800700080010000000000001300200060000005000800000440180050000000c015000c00100040050010006002c01e008400300000040000005001000000100040028000000c009001c0040000001000c00200080000004001001c000001000300300030018005000800500140030050000000400800000010010006004401100200000008008000c00800040070028006002800400080000000015002000400000030008000002c00700140020000001002400500080070010000002400e0028000001c0030000003000000000000070044002000000e00140060008001002800200080070000003000000a000000a000800500000000010000000400700280010008009003400f007c00a0058004000c0000000022000c0040008004003c001000c00100000000010006000400100000020050003001c0000010012001400a0004001002c00000140000008009002c014001400200100000020007000000600000080050039000800000000000020000001400a0010000000c0080008001000c0030000002000000000080070000004000800000000090038000001c008000000100080020004002000c000001400300000000000001001c0020000009001c000001c0080010000000000600080020010000001400000000010018003000c000000401600040030008009000c004000c01000000010004002000c0060094002000c0000000000000400b00240000000008000000f005000000140000000004000000300140150008001001c000002c0000010000000000100000000000000000c016000000d000000
  | 46 => 0x800000040020000000000000400280000000000003400100040000000001000000000000020000004001c0020034000004c00200080020004000000c00100180010014019000c000004c007000000500000050004000001403a000c0020010000000c00a0000003000000000000060000000002c004000000e00180000020000000000200040000004000000000100040070000000000000200380000000004000000000000180000002000000400080000000003001c00100000050018001005c0000004010001c006000c010000000100a400200100020008001000c00200000000014001002c000000c0010000001000000300000010010000002400000000000020003001001400200000000005000000100080090008003000000000000010000004000400000240010000008000400000100130004001002000c000c0020000005000000000080000000002000402400200090000001000400400d0000000400a00000010004002003c000000000200000020034001000800100040010004000000000d00000010014000000000000040120000007000400b000801100180050028000000400000180000008002000800b000400000000000000000006c007000000d0010004003c00200340020008001005c02500a0007004400300440010008000000000a003400600780060030001002400a005c0000000008004800100300000000004001400000040030020002003c00100080060008001001000200000020004000000000000000040004009000c00200080000028014000c00a0004002000000000280000004005000000000000010004001000000000080050004001000000000000010010002000800200000060000002001c01b000400200040000004000005000100780000008004004800200180010000008004000800000000034004001001100040060000003003400400180100034000000c00d001400f00040130028013000001b000400200100040010002000400c0004000000800400100160000000001c00c000c00d0014007001401b00000020000005002000d0004000000c0000000001001000300280020024001000c004000000500280000014001000000000480020018000000000c001000100180080020001001c00000240130058001000c002002c000000c00000000000018000002000600080050010003000c0050000003000000000000030010004002000100000020004002004000c000c0000008000006c00000080030000004002000000100000010002000c00b000400100000080000001000000400340020004002006c000000000c00000050004000000800e000c0040008001000800000080000000000001000d00000060004006001801800000030000002000001d000c0110000015004400400
  | 47 => 0x1e0000a09af7e9150000dd61b08da705e663124b41e203e4bbb00001acb95c2ed0000a1ca2d20000000d88330ce4c35941f689b40000c400fa80000000e6400015e8b560000000000000005d42fb31bcd47800000006e49aeb804a05247c000118a53c80000002876000000052980007a52dd632225920000000000245eb9780000000000e1a3238000000079280009f9800050b3860561abb805c920401786c23811f9898510b639700006e58000000162cae6800000000002c5000005a000000015720000000c788000000177e000000000000005fd9ebe00023bc57b9a024470000bf32ba000032307ca0000c519d9e13a1f1c10e35b800017826658c5c581834a55e8b7aa2eafc8bb114ca12f8ca8572060400024f494b8000000264cce9000009615402741ae8a080000b403562000342c87a801e00026fe953a2d8ccb0000e1234b200032bc000273cac82ad8c1136e6000392600005e8000314ea4a0000c3880000000000000000000013440000922000252800000000b51838093af1c41039180000000000000061e00008d7198a3219ff8000000000015944c8b3f07fe878408b987a0c700001d711f4000395249bb1943000f6ad8f216e838b73c28e21187e1808abc885ee7d69c6200017e80000000000000093100000000fb267f8ad400014dccea0b22000329edb693ee45f03120aead888fd8000b3a9990000000056d8d54ce628e213e2166928a35895c36a6526aac2c12965e3b987f459b148cb4c9ffccd4093618d865c80480001568edc7248000000000054c07140002bbc075adf089c35520002d764ad800048098d493688080000000b40ab1c00000000002a888ca01b0b890ac84ea0bc4d4b382a000208a0f1307e84200004cca5be25aa06c00002dccad8000000164673f228497814a83c5ab048c6800014b8000ab20a7000036ce6d28000000204e00022ea8d13514b2f1704aaba5e22640ed45a1a3decb2a8ee0f4a47ae0736702d221eca96078a631abb2b610b300508358769a666b390dc647c3696747000049f08d8000356a6bb0000e5885901fb88a87ae982600017b2b7438dc45980120000004005400000080000000000000000200040030000001001000100240070018001000c00400000000008001000000000040050004001000000900280050014005000800000400000000003003000000080000010000000002100140090000000000c0040048001000000400040000010000000c0070000033003800200080000044000000c00200000000008006000400000000000008000000001000040010030000000c009000000e002800000100010004003000c000000400c005400100000020008003000c00400140060000003001c001000c0020004000000400a0000000000c005000c0060028006000000f00340
  | 48 => 0x95cc73000000000002d98000bfc29d01d50000000000042e240800026dcd57000098b93087640000ab38000b76acf00003932000000000025a200000000002bce77231fc000000019b389221db77200000002662a5000000008d58000000000039c85c0685997202400003608330adcb0484490000000355442f82d86d38000a17800086f00000002fa8c5b2a180000000dfd930ae3415905e98000000000000005c8dda36303a5000000000000000000512b78a019800002238c600000000000000b5c38f0000038e00028a48a98000a8a0724e5215120001c3675a80000000000a75800000000009c090c243a29ee161a07e023238cdbb0c4cbe60da6557b90cd7ea5ac0802596d162a2e476b3b6e1912c470d2eb647f1c1ad35b55667c040c25a2398750a3da0000000b53a0e60002feedaa0e2e6092b327e41bf0150265c101882a4728a2c8749a2878795fa782a3d2779ad987bf1b6ca1c175275fb7e445f99664e10b5e0000462c8a0df40003732000000028d80000001fda0000000000000072f2e6400019c8133a5c8d1b800074d83760000abc2118448c0100000088c24a2f1c9ccb217c600000560000000d8c9af044400000000136b161ada7d48cd6c6e8e7e67034a06ef00004b40d0800000000000574000000000014723203070bfa000098aa214e069ddcbd88000000000019698f60002b3800000f4598323c86d2ada88a2e10e518b8087ea86e07f263e33d0000b9f1526b4bb22056e2ff21bd8602000388a3b319ba00000000001272000318400005e2e22169876dad9a5898d9e41e1136c9c30d60000000c84931edfd0fc24af094e0000000af58000abeb8b600038ee00008a000005dc4e69016d19800012db4c600000006903846afe3412b590fa200013b6df580000001e4edc080000000000a00257400001001eb2424891abf4634287c7a302680000000000283400000000002b8c0000000000000000036fcdf813dc6129fb066218b0dbe00000000b90000293e5e426247c80174bde86589258b9885c00000000000af4395400000002990980324a85cbc48244993a25a00005a6df384880b7b318815815c9aba4ce9c9b59015f00002ec92fc51d0000a4500000ed05dae2698a876392983928f906c300000003304000086200000003ef1c9eb1b18f2adf000000020826e421e209685c6e4f8c7027e91aa36e0000000000031d15ba0000000e422ab231a93c6def1ae0c2ab47410f9812852a6a88d78000ca18000b5c80000000316b2c0000b4d84ea00014a000004cad0000000000000000270c536301e5391a8400013a60000000000000000000007918db0db1186272e00de0002e5c00000000000000000000000033101c989ce598afc42f196a80001b440d3800068100000330000abb800000027b20000fe000000003
  | 49 => 0x29f431b330ad7b9ecc00017f2c0e94c254c8000cda069415e1e660000000991800049116d60002d087c910ea0499a48000000000030d478427b40000b328d0b58c0002ec89f78000d128000d92a00400000000000e0a28f800000004ba0c0961404bb2908448deca4c0cc4619946e29fb3741ddb35800021da00012b09712eba00000000001b1a0000000a128cda000160c746b00e00020a4000000095600007ca907a9ff381e08a0000d9f0000283b39e6d08b9a0000000000323a0000000838251e70112a01bf2df8108a0b405c15ac4de1dc47da1ab8c5ca5e611389b85f715044839228a9aaa8e85a894400026fc000000092fa092000000000035f800000007ea800000000009f90000000000000000002f080000001bd00e5af3c3d59f7a29618f42b1932c000000003e859c5cf800000037ac00016120001e926220000bb180000001bf6000347a0000000095a4120002c3a5b2a33c0302aa44371d8681d90cea2f80000000cac0000d5e4179aeaa568912a298e50afa2fde92437386b0b4b8890250282f909ac6425783bf03b6000201466626540e28fdacd19d960002c1e00004260002324a14800049534904b39a3456129e298400000001bf845e1e5c00000000000000c298d7c000101e5e5a6de53d800078b30e05b63612cca80000000000131a10c4060000c6e1aa00000000000000075e963000006ba000000071b0000000261cc0f800000000002ef332ed7100004ec80000000bba00005d80000ef400018160350038000000040280005b1800050313ce286b0320000000aa000009bc1b2678923f80000f7076007ca00000003a71a2654e00006b38000e1013cc2c2a6b2a5d9e1a3af000000000004fc0000aae144600032dc000337ea078ce45e69f703da3812a4180005cf15a27d580009f0b5b0655885207e1b2e2722d3e0cd24c20d73958b28b86c0000000000022438a0786b0b0a7c00024a86488000b4e9e64cee1cb2b4a928200a8000a1821f4a7089ae2df299414f9d325948c2e00018d60000000000154cbbc288200003529600000000208c003852c0001d50405356000000000001dda0000000d4800000000aceaa41c0849909562d9315c32e943095800daa3c832c00000002668000ba28e884d8347c3f780000000000dbaa4680000000bbb8000b6f050400000004d43454677ad6a000000016900000002e16a3480001eb8dc890c80005aaa91e6130000c278000854000092b936e0002bd8a3d975c0002ac000013f6106800030080002a7836edec00000002c1c000000000000000000000000000000011081201a7e23f8f06d5a00003a9abc6da8246200027a6000188e005800000002427729588a500000dc8a7d400027e09ef0c16a9714ec0000000000081c6e200005aba122cc380000000000a0c200064f2
  | 50 => 0x320800008ac328000028888aeb0c1cfe000026689d1b745db80006bf000092200000000000e2e0000e19800000000008a433661df1c12000000058b99ea4aa09e0000365ec97a31276a26363299bde4bd0834000003e97a13c841b28fc000104c000235a21e859a00038f64170fc495b01be61a965424d2050383276468f16820640000a6401e452900000000000c10aa16b170000000306c9248000ade80005c080002e7a05e000000000036900000000000018c000088ac1bb3de6b60f36000352630793bee330542688b648000000057190a84e39fbc0d880000000000000395e00024068e5093ea2b8bd60000000d68abe0bcc00009a20000000000077eabf6d4187d41071ae2000000000029349d189c667602e010d33c47b19f1410b9c900000000000000031618fe7b80000dcf9efa0a0800000000006140000b23a034404a0bc57c82d6d7388b02b70d661299d92728185200000000001cf66da0532a7102a8d1b1da08a1854c9b0082e0e4858ed5133d20f89bfacf98d1694200000dfb8c20002a06066000063282b00732aca0000000db6000003f8d2084580001af17be3fd30a038e377a6da883c64a2e6abe50000a8d9d440002f96b8eb82ee2080000001f0a1ee938a30535342b7ab4c9230000d69848a64d064ed0225388130b6e0002e4cbd7858477a236067bb22c473a71c4362df4d5f9fd2ac42caa94ab6bc576000096d1ed8d4433622db2c500000000000000079602a416d9a6ce2ba198c3721cc2f7800000033be0000000d7c9c4a3e70000acdaaa0c86b182116b92200000000000fb651900000000000644affab8b00005b428581870ae400000008e40000af50000308b68e0003284e391f6ecf2835ad469f2684709be0002bde139251200000004b68000445800078ea4fcdb7b40ebf089e497b0000d8891d4b5281ac00022345998822ad129ecc739d027bb00008908000cfba888304274000000a61ee386200000000000a760fb800019336565ac2c02000000000019da0000000b8f337800000006cf80686110000b8c370400000e276b07d000000000a20000e3d2f8a00001620000000000223a9aa8000a3d0000b0380005638ab8000119266a97248bb800000031609d08760c01af06b44800000001401ae0000af6b028986a8187f9240e6ab29b201ba8c20000000d1c92225f380000001100dc980000c10000c2e879a31e867c00000000000000bdd1cc057000000001f9c7142fca5eb000000000000000000000158c7bc8ec2000000026d800080380000000958d7800000000000288000000000000000000d6a868c00020689d211decec242e00000000a58000000369a000054e9148000dd480003730000c968000000000017f9d700a890c0e50362845d89e6acb0000984b96434f19500000000c6200009c2992e
  | 51 => 0x41580000000000a4830b00a8000000000000000000d8e00002f20ab422324721b48000000357067e05d2707b12c3910eaa1b811f600000000002bace33a4640000000000378e1430fac256b1d2aa98680000091e0000000d4728f8bf5336c78c983000000000000000000000000000000000000c4880008621c205e33814000000006b910c6a0800092d987ec40ae2a84b98e60000942afb9c5a0000b72ab8388022eb4d0562b0f072896208323382d5e36748ee850e89380000001160000244e28f2abc738a24a64e95780002438e55a6600002040bee000000031e4dfe1cea00017d84d18000a9f31d0d268e80c06800065200000000000bec00000000000b6d80007c880000000bca4ca0ff6a272ae2c9f0000c2f0520374206a00000b0843883e00025d686e9d64cb18000d1a377035d800048f8000b9c9490a380000d96000000c1b700000bda000387c126b4c045e80002399be6584000024eaef4b482a267589c88000165ab0f9f9e2fe00004a9000000000000000000000000000016a400000009dd164e000057aa9ba0200f72d2c2c5a2f6000208e05baaf47808000000321e148800098e0d58b5eb8026f5852a7dca33820129d2e3f9fa427d8000c692f6600000004281a3288401322bc84fe43f9d8cdaa80001dea72e6870000000000000000000000000d7a80004eb87f0e45ae82419000000000002a280007a700000440000b500000000363600000000000fd63d50254a97a9f008b1486000226438900000001e3e000336000025bc0000f880000000da208cce2104240000000caf9a72752205432d3700e471b0eb470c683f8b09030a0d36c6b800016a2bba8910c526be108c00017285ba8ea800032646208000000039adfeadc6c7e00000000000000089a00000000010000929183e6b79fba23928362a996180610000de9200274faf820001102000000000000000df000000020fa00023a200000604bb80001661e6c0000000000000000000000000cf04f62b740002adc00000005dd08d64f0afc6a1d02cea9fa5948ea869cc17aaaa2461b3accd0054b372ec09fa18320000b38000000027e084c0e0376a00018f80001432000273a7b99366000093251b0414d4c12004ad347e22a851c0c52ee2d3d2cae900b4022be2ae60002348000000018c0d60d388000b258ec658d963a32a94f0dc30000220a58a0002bb49ba8000e231fc857f0000000135202f81debd380000001e9e00009d6000010c16f800000028de0003494c7580000d097b4cf4000000000000000000d7c00001818fee2f800000002a820002b3e8e9a788342912e9719470d96800000000000001a9a5f2243ed230000ad28000d3606fa73280008f902bca058000b42800028780003838b3a1a680000fd10da00001b8dcc0cb885a23c641480eccd138ac000
  | 52 => 0x580000000000bd326ee00000000000f822e380006718202e0c1c2203984b280c9310a1a00003cb0000ced17fa00015b46c100000001ec005db014045a99c306132e2290e3250e1f2cb358000bf8b14a000196eae3800000006cccb0b4da4242b3011b0a9c00014d2297123c000143e27b98ec98c8000168800038e800010d8000ba1919eb5231a241c8abed66142401f00000001326000369e7bdb820dee835049e3198d1807aade316760000000aa3000000011e8000000018a800000000000000000d509e9600000000000000a322b6a00000007ac800000000009f130180002aec8e780001b1a61e00033c600000002851fea3c2000000013980002dd88e800002a600001f10000bfb1e20477000098d001a0000000000000000000000000000ce9849c384000000039660001380ca8800093e202a0001cfa000000000018cea068e845cb031a21e000000004500002eac00018ae0000000ade000000000001f5af8c00008fa65b2ad28999e5200037b200024d6d0fadf20000000d13000000000003c2a2941da000000011220000000761000000007a8000071a1240000ada0000988318e9631e621949c7023f122c0003258411a1aca660180e410000911270012e15ce8db237e270a9fa00004e656820068c9a80e9e00dd607d0b46146afc0aec0052a8018645288db6a458b4456aa76cb18294a453009859cad149452926cb9361467e88b83c431128453712b43262c6eaa16c09708b6d3b00006ac0000366800000031f000014b00001ba800024cc000000093188742dd082c7332b7000030540002968c2f864000019688b70000b302c8c4f58ece6c084d6156349c1510000d382d28c632988d6d80006949020c233624cec8000b9a076600027964da331eb130b8c51598e011c87e4d7480009d1294c59080000000000dbf8ae266389fe75804f6c4f03840362b2ec7b8000da4b86abc98da4bd6170c000102c2ef95280001a700000000134074e0001466a4a8e62adfabea7ed2f76152b0ea4fa1df03fb1ee8949886a99a35ca00000007800000000183a2fe800058f0000000192a0000cf20002262391a5a075480008d49b6604197de8e4971876607dea548cde6070102ae92808000159a42288280f2b43abc02756d5b03c200335742890d989898ec031f9b1400032720002178cf700000001df288831660002c28000000000007e866ba80cb98b592c2685cc0003492d9317c000000000001c1c6052b56000000000000000238000000124297e06960992edabce2366000155c0000000b0029b463c29b0cdeadd2e0917b00000000000205c00037de3c70a5a95580003fa0000000000000000000000000000145a9252080cbcb7b6000000000000003402a74000000033a80c20000000000004a000000058ca6d200032ce710879c000000
  | 53 => 0xc45708f5262723001b232740000000d67371a0000000607b1640000000848314400012bad4e00000002a420002222c60000025f8000000000034f800091400002e711527e10000000000078b82e489b063c8778000209310cb5129d4902896c745972a86e126a70e21a69041abe78aabaaa0b900482630ca6b92d9422381284ac88960e40000000315ae1080001741a184568dbe42b9a3a9c220b800034e4669af782900fbecd480000000000000000000000000001dc0000013000000000002cc600000003de000047e0000000037a0000000000000066000000a78000674a3c887c800000007cc3372350a9c28380001eaa4fe2cee0001ad0e03b2941109880cf082909da077e25e177a50133564be0000326b3e2000315e684820e8ab1f30313a230863a46070c0000c8180000000c9e000000030d00000551ff67f1b7063259eda9921ef00001a00941a48ead734ce000150874534f0000230e94cb37c6ab9484a26130e3418eba3bf890648caab4c8d360439a253651a96c467cb3e8a1197f4481995a6aa33aa6a5a17a35e110a2861448de58dde1a8979241b9e88b6701a2957aeea7f7236403db5b4260b1423abaa241d101c66b00f3cd9091b44632b5ed08896e5d41dbe3210000328800000026b6673000000000000000000aac14b232baf2cb0582fa5200000000277a000000000020460000e16966952c6bb80000000c262bd9eb4041007211c000030b00000f20000276b8ea55918bc0a68c0c0002fe40000000744000045580008c10000677317a81b8f4e15bb524e28acd2cbe1c8a000000000000000003428246968e0000e7c000131acf514f81c80aa821c0ef8225000068906e24dc80000000b020002fd67018000d9a22c84278af4ba50b12a408000ad3a084db2ac06c3f824845426980002c68c1a8d2e5359e5028b937c76e800045b176c1d096880000a8e35180002ea2692d02a3b8d310cf60003232894b85009d98928feb6bea3a38d231f0d240002d10da30ba61fe973a9670eee05fada84b6000000000004c919a40000000cc98000a6080000000bd2611b27a000000000000002f400005d3821cdfc8000000000000000000000000d16800049d3126000384a61027c6b6580e8ab117e697d954ec5c04ccddbb3ced5b8000c482dca2770000567a1f098e925aae5aa3859e20a29d6316ed0d00003618150250221a0a2a33e0521436b7387121b3860e934921c739023ab1194182c61dcca7787b2bb92b48b211c7647314b8825921acb000000000d4800009e8ae48d8e08c891c87100004b1839c6d4a0de00000001d580000002d06856824a8c82c943a291a8a2c8ea00c31ef450680002bb19e2b2900004f1321cc02a0220000000370199c65317e27b38be2000236a4ee02b803b8000000000000000000002a3e7bf8a1675
  | 54 => 0x7e8000000269a00000008e0a148683a27eafc8d8400000007691034aca10f83b11c18b9b800000b2980000000000012c80003596000076e564a24c0002ef2000000000000003899bdad51800000000000000000bed91d2559ae12b678a4ad8a937645600007e08d02000218c00000003e39a6edf13010000000000012beaf9b8523cc8f2e35d2038a7300004f691840001f4cb041cb600021be82aa2c03e3211a00017767238b1adcd37cc0000df8d0f0fa09828be8b218000a6b0000000000033200000b9857218b25d400002461d301e6861316a0001b1e85c8000c00313a0ec00005b90ae66ee9d28c3b8000000095000000006c4000081ca1540003008c54a9861b10d309f7035416e0000000000038c0d6e0000000db8097084c04f0d5f0000bcc9c56d37a8fa774a622b24203a3db928a089800000000004a000dc714a3f050525b825227ea573216260db616cbb317ed2c2cce69982082ac20f8388afa2d2b12a696bb762a19a9fcbfab4a6cf5a370d2d2e322c78000649352857280006a21d064108000afe8d5064b0d6cdac8d4e24ab61ea8c1fe65ba2b5067d85aea132416145a68e1409340d52ae76a7200008702ff8287000000001f000028107ae0000a63adf6000252c00035be6e334ea66c03da5b4816ab36334e1e89abcd05039e85784a80ee9db00002dec8072d1a9f8aac600000008be0ddab81b246387026064080001f204fc0001d4e000062ee3e1d88b2d80000002afc000000005e000041680006e38000bb48000ca90000c94a74a547201ee0600000002cb484a080c5dc1fd01f9a37400022a2a9300008c229b628d000017c81a41918000000000052a9fc0a782680766a8800bf1afa408800000000000001c0a1a7a944543375ca7e27acac181863d10000a5b00002212cdac3e99d4000094a000259e0ef112ca2d32d800016ee339afaa4ec31f484e2ed43c686a8d1094c86a5271477b1ac844a88166cc23e6332b2260ce800000016ec0002e0200001640000000000255cde512e800000006c80000000000079200000000770d3b80007f1000000027ca000311e000166400012e6a5236fa00021f8158a388d3f12a2291217ca91a1a200011b000024e2e4e2ccc00000000002cf6000000000000000978000c62a84030c8f7acc88000bcd06441ba045ea8217a8e4d178e7eb140abec863e00030528e911388cc8ef01de357a75a3646060962a22f09146c2a1d420da43400014209158cbcb642a640e3000000029f60ba08403c8231e4d5000000034169060e784e310e0d7f80004248cc26c006a6ce490f000005103ba8456a949e080c98370b0621406519b186678000abc8000bbf80000001aa21be000054f16b41c2849683c92484961cf253534400000000428890ccc18000bf38dfa1f7087cc081074ac585dee01b1
  | 55 => 0x6c03580003c9383655f800000006aeca0b94e52d90ba7da8e02919b1a0bf60bf60000000000260086c889800005aa00035ba0000fd00000e4e0001b4088f82ac3e608dc61a000000015820002d5074c0a8ca5996e2000363400000000000000000000000000000002a623ddac3400000000d200000000cd4263368a000000023080007c3aade007014a0001364db5360a8dc9936a69a7f400000aac0b9276655086c00000007cd80000000000ca8000000000000000000a683808000355a4d3126200000000002588737819200015ae0002e920002dc855d05cabdf0000b648000bfd99105460e74000324c64f9e4408e24f2a9e800028297ea1f021100000000e26000012d000000000008de000000000006630000d431f5e2a437868ca8a84826a88a000000048597060000000000308a43910b40000000000000000000005d080000000138000387823026160000afe4793754000000069d0aa246036c09e4a42293e80000000000da093624f4a8240000000000124c0001ad2ccda2c407500004f40000ac2b3f8aad9d223c3a0d60000000da900005e280000000000000000000000002b59e769bb15f06ef800000038e2c6fadc000000000001cac00000005b38484000000000000001ceb94280580002fd36d65961b94d6c93aa945988c00000000ca18fc943034c000000000026440002dde1efab9800025f000000007672e282d597bc75680009d4800098f31dc8f52c726ce0e1a34a8c48cb4ace07f580000001444000000093618b40000c2a1fb0000b89a7660003150c6a229200014c600032568a3821edc80234b1e370865629781182a92000174aa28a572bd2a0ec3ac9c5480f000000010e60000000b1b928600018c889c8d80ac21a54d76065ee2a00000d1122e000000000026e44db00001aa80006f3391a0000d6800021642ab85b0a6a8fb40000000000000000011fe000000057800000002706437873836e97ee000153a00036b00fe2f1ac16a3020001c96bff90826d588e244a07fc30f8000b19aa10de20000e3b109c57b019a69e073c000000046380006b735dadb09f3a382301c9569212000210472624a000020ea9c3878c0001d3400035084ce35a4dc2944093417ba09038b4b0100004dc1942b7a85680000000000000089a04162ad8210e4a813e0002c2e999000000000000003602a2e32ae0bc800038b000052f94283b405f8de80000c46032ea2528ec0000000000000000000000000f5c35ea7906e6b50497a800000000006240000000133ed7402b4000000000027ec8b500000000d140001410000000000001dcae7b7d2000342e28ab7da91c133a051926cca2a46c401b2b4bb2a99e4b493ea219000073e0000958b4040000be688381a62040fb0000000000000005580000207acfe000000000000009c480000
  | 56 => 0xa12c92db180c8202b34a0000000d189f420002da0685302aaf01e1cb0e00007a90b9400024487fd04ac0002678000000000017486cd000002a0000217000057522361f3b8740cf967083c2dfa00000000000afa550b2ac0002018000000084000000002e18000271e00038b2906996000023a833180005790000350319aae716221e0942a94f8f121daae964b8a60800019629a803240001df66c711c60061aa6b639a1aa6b897214e8000000000000000000f41918740237cde785260160c4a5c4113a36f30fc0000000c290000cfd0000c9b80000002eb820803ecd638000db706664122accc658c6e0002530cc8353a000000000000007c632220000000e3a0000e3815b03499daa000000000000004212a2ca5f07e200000003b60b969ca0924b5714d0254ab6468b28289b50c500000b882519978a0f144c00022580002fba5f59d380000670a631b8400022bc937160000005520000000b7f0664000387eaba241477b8f3a84f9fbe2ba36f252297aaae5191c4153340bc59bc80b1968a00037fc400000000000000000000000000077791d658929ca3d003e0600b7608808900db8a954606a29c0e88dea690ae90a358ada318a208d53afe0cc4960274907580001cc8668b2b25548000a92365c13600001f600001279458406a6b400f29e6000222613c9860d8416feca6969a4beb2980a3047c30d9388ce80000879800078d800027d2e34581221e0000000000095493a000066680000001bfe00035bc13b000000000002d0920c134800042a8000a43acc40002fbc000198683f000036315c4c9992de8e0048e0001d043f296c00002c560c8a1a400035d4700000071c8b76d7d00006439a2a2498f3029a8000000098400005127d921c243f2598000000000000001cd040e3e980005f50144b0202cc70ea1561c59f96e3eb66a400a48a0000a0216b0000000067e9e60000d6116a276b8bf0000000000000000000fcc812ad30000274c2fb9ad67de2e42bc80000e4d9c9a00000e052780a0bd18b00a5b8000a9527d81ff9cd637ca8ac0000c3000033ac0ca80003762daa0001f544939e301e4185e14504a44fc8f3eb4d0fce000097c010868ab8f93422ff000096413a494803a871980000001b46000000095a9252502000009e079200017a4738000000000006fc80002de0000e15b2aa0000000000119800c8000000296a6bf80ca00000340000f2a00000000001ed29fdb13e63601fe2b4af1471a34520000000000000000018c2afc27361f1800094d00ae40c00c663680006f48ede8cda4b00000ce00002754000293631780005e5005cae0b52e0002c980001036cca0108001a72ce1ca6c802e305000021a8cfe800095f0c82187a912616913cc4d1f883e52f3a1a21aaa88c8dcaa1b00001581f06626014c2ff800000034bcde08
  | 57 => 0x11868e1a18241c0cb23ac0000000000069780000000000b478000457000000000000002c32ce2902e000291a6bd8000000194a83002ee0000000000038297fb20ade8800000009c00001d760001fa8b578d8a602011200000004cf300c0000000cbe800089200000001ca80001fb8390838600000005f41e1683731e0cf6976843402868ec8474c9400002ca8000ae9b7b435c1e7e64c80008e680000b8b0827438e3400009de000000046e0430c6a8000a2380004d2b8101bc0b28a5c02c2000000000034fa0003608c04a9927789fb66818f587d88000b050df60001acad2ab8de421b4ae4700080cd700000e20bb6e27269c9001db832927ae000000000000007b09ae6c860000d6680007599256364357295a28ea3b2a6d63fa8c3800000008f31a4e000042c00035ec00012380000000d0703d60000166c098000b0982502e10040c3b08ee5a70ed200038d8ab583d45fb0b82703380a0002106be78c8a0001bee0001b480001e06b87131400035d6c0f1656000000062100001e031c8387acc2399ac9a000000054da23cb91aedc00005924c72f72ac080d20000000b5b000056a00001dd000049fa974bf71c0e00000000002b6297382ea8a238aa295960a00000000000e6a3f700000000272000000000023f491ba5c258704fa5bc3480defa3ee0000000000254a07d89fc1d216c23010fa8530205a30187b667a28e438f01e03781a36700a2cc95f9cb4cce0000138279e48ab8705d68000000000000002d0c5da90006c80008a90000b9e371614d80006830ce2d9000000000d427518000000000014e1e7aa019d2e0000de46e2910e3e00ed675793bc08800006cb307460a2ffc3448e7689f1964a51908027600c4c41b388bb985068dd800019831140002d683070000842a8d8a18800051f29621dc9deaaa70000c79826c000114a77623341ad9dfe0000000a210000000291cc7da65233a2d165b5084e0002b8600000003f60c7200030a89a400000001b3200000000000ff2d93800000000000000000000099c0000000000000000001c00001eeed30800068410ac00000009fc930211fb2fe6478d1ce2807465e000005ffa67410a0e18c7caf0a814a5de479b2969ac2c6271a8cfa84da306d0624309dc0000073858c00000002099066000029cba689aadd407f82819e708b6b2d0b04aa4e5d32cec582000000d80001d9214e2110b8aa4305ea5182186303aaa22e930c85c0384e4721f4a5c5254c00000001f803ae0d98cccc8d800096a947a0850f1e1ad16940e9b49663924367b5b1320001c466498f0c1c100000000000a1698cc674068400037c00000394000000000000003f4800068e346400011148318a722d61d7c0000a300000000594231473c0d2c4318000000000017b000023106680000000a6f8000baa1b281421112
  | 58 => 0x62800000000003240000a4e01a875e206290a91ec72e875035580004a38000c85376451d9164063a34a10003603df053cb802a78b462f649210faead037c223d32400fca9ea04f1a6a6d818a00001e54131070695405460000aba7861296149000026286ec1d000003788000000276a20083080001e8e0a0000000038bc71232ea17c08d4a7a0000d2129b8a4e80002df9f2e9b101d86d8ac0a4a50ffe000142654022b40000000000015688b0194e1114968281f920002f803ff0000000122679f0000000371c00000000001ea82da350ed4f9854bdba12a6c48000072934ea10b2d611d80004038dc27c78000db333ba3cd2794660b4f606a92240002cbac81000024099be184b3e0acd2a5692f3600162b71e3fe03fc5451f5000000000001e74000335a000086829a0f1496d80b624b1a76bd6a5d8d990000d0ab23ed4c83c6000000000020b0d2a1df8ad6ac880002cf426c80b200000002129c1011289d24ffb25c0001ab4af22d74c52264083b800000033d8000000000000000000000000000088aa66219892f6000379c9171b2a56c9c326fab24e00013c0c6700000000000e0f31b0157ab52000196a000000000027a00002676e1700009218000b6900000000000bf6800000037422b631c2a3026969c61140ce38e6c468195c026a0d283d1132873a19eb1db4f834cb718a4619b8abf828e4e825f20eb00001550000000303800000000000000b9e80008f130dad118000a62800057980bc14016a63a5808400003f096380000000000a558000cd2135eba398be00000d069a0000000307c4ab0000160ae8431833ec000090400000007932c5400000000001b986288b26cdc0000c139be07b7995edebb8a68f710385a1292200408da16d2c9c9af83209c88000a76b1244091eb60000c464f51c7a547a07a0001712000000000000000000cce00000006f892b89a1ae5a9a299381520120283194427134567d3b7e21a62e504dd297e3ee07324a78d5a4e4280491e15484410c0a78e217e0002a607202ce8067ac7e0000bd436a92609ab00008d3046a4b53564233a8b609c00006d6329c0142baec4da984c338064df29c2cb79207c62500002c40ba205622aa8338000aed8ba0a3307a414d000099b207491a8000446817aa2c04406269a4a5dab798000394453fa9bc760a7b0474251ad6200000460000dea0000000257600000000001416e4385768cb27c0000241c3e9000000020a800038cacc91f3436580000000000e44800022f94125c7000000000007a1800000000003c000000000d880000642a53830000027aa806aaf000037ea2b0000000022be357000000000007d80dee71386f2067191480d809c4d62c445c82498ad503e67968e560001680c37800000000000002d7c00014e68b81d0a55890d2021a4e08c70cc04a7
  | 59 => 0x6a7fa000000003c914200031c639e8000e169e5657736a2bac1c1483425489dba10211e0a8800001960000000085800003f00007c680000000000000000000012f20001bc600028a843880006d93686b03000000000007f8800049192f00000000147a21619e8ac20000e3608aa49c00017161b71126943aecec5f23d66e1addc2dc2ca88191058000026a0000000000000000000000003276d9c9cd236d0000000127a73b27d0980800099a8000849150a000000038f80007db00006412dc4000293220e800046ba28a00038166a714cc832b6ee8a5800000000001e58000be10000c6b00000001f6600000004328000de40000c1c9fb23411e84000000094006da4351edca718dfc000000000021e8000000061d9d2a0000000106256e000000000023ea67923d0e239fecd0d88d0425b1ec08c2200a0e9dd49c1008286b80942a6957c71f87103348000565800000037360000678d7f1134000000000023c000000000000000000000000000000000000788b3f2db41a5846d800009b860ab2e26e8682800089e0e60130b5dc0000000e4a01ba000387a455040800000007250d64094a7f850f00005d527d62d28000bd80d6200009ccb92b60c0000d1846507bc744a9ba261b498d0e000000011ac00022e80000692b88000000006760000f62972a81c00000008a30000c288000c4027847422ba8000000000021b0a1f92fe323ad8c00015d2469b53c74e9dbc877205800000002a1b5ae98c000057400000000000000278c00000000003540908006200001eeaf100ce5fe1db25a4392ed4015f6d293384ccfaa3cda11de00000000098afa499c0fbab2783f62039f5c00000000000336000002600016e63d309a8c921a8a8658000dd100000001be4000000099b80007219e420000000ddb3778cbd26f6b0800000000000c5e00003d08000de98000000333c878265aa702dc2e5280002ee2a660390f5aba22724883000060d2a0e1461e7875d2e0e45100001921d0c1ac0000beb1870929800000032100000000220000000000007c200004d206be65000000000000000000000000000000000762800080b00004f880000000000192800000001c800019bc0002ebe0000000785000000030607c0a7a48aa000000008d20002f02c558000dcb95ea7530000000000000008f6932000000000002931e3ce479ba207b000054800000000f26a1a80009b984646972b008b28000462006a000180484994520000000c100000cff35503bb086e5c994e000000000001ba45ee17b600030221fa859484c866adcea29885300000000000000000000000008e5a95ee408000d7217326a40c3c0000000e4001da51780000000000000000018d000020c81e2000159c486173600000004c197fc1b40000e4b116e6a1b9201ed00004940000c159fee3d1800
  | 60 => 0xd20c2a8020000a32000000000030e40ef8000627b6180000000aa1af6c0002a32c588000e3000acde12da6524800000000000001284688221843d8c64bdc1570316aa6800005f6000314c0000e6edfb31080000000a2795d60000092000000053ba1920000000000000043580000002a1c1c890a4a352f244f2b19e000000086280004dfa56600000008b9390a43b1e04501800039603181208000000175e42623b0994000037c379aa1eaa7699f8a2600007b00000b3ccb9800000025fc3158a967b20000cc70000c7280008b7811c0002cd44b92ad47f08556d61928c23b0000dae08b25d62f92bca07d26e8046600024e60002c3600000005e80000000000000000000d1a782000000000033300001aa45c3800000016441c7ac420001b1610a8000000000041f933400000000000000000000000000000000000937967ab498458b588000d9b923abf411fa0d015e229b903aaa6a34e3b925cc4099f46d07b910000000000016cc52ba618c43961ed278000ac99236c908000000070807a1eae000204425e8f96000000036521520002ea65bd8a7806219ca5e6340600029a844f800000013b4000000000038c8ae12440a15b20e00037d000000000000000be38000df6367a0001bacb6b9fca42c0000a900000aef9522c56000000a38f2d09331a0002ea0000000085600008ae00005e228c65238a2800011ee0000000000000000004860002672b9fb5a00000000c8a9bae2c7141ec92b34ce0b0bc000036f67e818586c9348a0002f54b6ea4fe4331bf40002ee8b34085600000001a900000da0e548e2b0b489a82042e1af3e0dc803a70980004eeb4ba10821740000000000000071800009f3b5a80000000000000039000009770000000000000000007a0800000008921c0a75a43d06acba78000641911e9e88b6a0000000081800070a08580c426cc0292f420001a7c000000000016dc5ae8000c2627ba00000007208aee2068410881089060832ded2099c44113748194217600000000001e5e5f4800000002c000001b6a190000000009eb22a6d84640000e56800006d0000be6b7e600030927c422ba0000b049ef800097ea75e0a50000c19387687f211e5bd00006389786000225e2948b4c1b2b07674f085ec85869001c0000bb7a1c6b51a0905221af2592b5ac0c79ba634689b000000000a990eec21a83e000242897400000000000e2f8000000372a000273e5188000e0996ac7b280005458a1058f87001b780000000000ce88000000000000000000a48000000011e69320a600000000001842b1480004e5b5c6895a3306a300000002f2a95480000002b1ed52260482500002a8352256909d446c80002220d92860000053d192060b80003d80000000142e00037aaa26820a0000d44c55000055400002c2000000015da62b208691
  | 61 => 0x6fa09cc3637568361b4c000000000030d00002ecc2458e126f12ea24dab0840ffb72c71d037801f949846893a24c632a6d2882b25d825b20000d7e0001fd4adba19c0001c78000000015f9b5000018569ae01bc8942ad00000d52290800011a022290e80003a08000b9c0000b1d34ca3d2a9607f802aece72260d709bd469810c4b78899eaddb4e6ae41210bad24bae00187c8181e902ea997e51a2890ae0279a4b2b478c7017e4ad086d650d2c40a3fa3c2104879863eb0e819b84bc4c10c4218606260002878cb680126420000bdaa1d68b5ae526f39766d56130c000326241f0994bb4279c0002f86d1c01a08dea65ea398ef629d089ea912a22000351255632e808da510819aa4a000219a66100000002a2add186d8dd9ab1430e875a38a80746a60d72d4580000000000159b2880001f8e00000000001be8af480008a080001d7971ad23a0429d43854000361ac2e292e00030f811b9e6a13d21b6a2ab7fe000000000024f642f02980000000cdb84e25ac8000cda9a1eb8e00002f7000093513e4000150e33f000066516b8000197a41800000000000000000057e00ba000000015b0f921c3a94254fa2240d7b0c40d58000e3125a45a58000000229a2f317f01a0ac6a5c204d400022aebed31387d10000c4a17c483100006469bb45bc800062e8b240bfae8000025848761598cc093e6d778c540000b20c4c06749302854000000000000000002b0c388375a85180008350000d138000000227a5be8afc5698000a8e800000025229cd0000c23837428480000000842000000036a24ecbc300006301a5600035e8000020c33b80000001c2ea9b24821e985e46eda13a013021a0000000000000037fa088c6c80005ce2d527a9a0b28b1800024a13ec000383ebbeb1a64fd0000b922f101c307947d009a20daa9e4000362e3f00000ac88000000000000008540af800008f8000932a44a000000000000003d20632d0322fe46080000003698664a32e89d98b8d1d800000027c8aff0988000000063487f2a258e00aa52f903a3a3ac000000000000000002efc0001a3ec0d8000981800003c000046f307a9958bb08b3947e95918a45f080009e19faed5980003e280004eb202899f073005b2cfa78a12880000000691243c55a1d94b411eb0b092af80ad800000000000000000000095ec619f746ff00009a7b33200000000ec810e0000a6000000000000dc40001bec23a8818d3a389e00021aa00038da80913fa000233a7af2e4429236acaf7090a961917400020dab138f6c3df872c000000000038d68c3000080c0000bb5a6584e489965e8800036b000068b904e000000000036624c480000000000ca48000162311c556945480bab8a26812700001f000000000aa609a4df70000000000011526fad7db030b9b174450e907621200ea7ba8d
  | 62 => 0x316cbba2b00002b3c00008f06d50f2847832d497d103c7f3b27e4c5a0e44b7169e979119ab29800000033fea689510c332fe6b6e000098382f0002071c000240452d0000476327868c0f1800000000cc858065f30f463a00005de000000000007d60000afb0d4a18580007ff84ee0000000c318a542b116be2d819d6000000000000000001a62171161ad7000005d92f0895095fe3270000bb080002d3887e00003aa049310a5a31d2697bb6c8d79000060300000000000c008000000012c613a3ec54d0000a8d1c84000000000000000000c6600019a04713168000000000000005f28000ba71dd000002180001d1e0002cc800033c0000162864c0ab200021ca3a68000418aee000011bab62ae1a0000000a3c1356c270000acea39c47ab54c74b1482ae225443a788001260ee8dad240c80299701148ef25f6b8d47dd847a2a4b1fad9d99ec43203b85a4ad80baa9eac3a900000c384ae00800000289554a230f72492800058d1dd6237a812af299b20002c8083f80009df14de000352ad17800071b80001b01734ce188304e78ff01c60fc6d172dee4658000c05b0b25be000017e8000b7fae0c9a3000000000007503660a410000b0a800000022800090000000093c2a50000308272a4e722fa7190f7409e800000033bc9ea343218e00008f88000b95abe27fc800073611be7b41fd80000000b129e9a0bdb04677913820001bb8b55aabe99eaa9ec2b2b60a13a49a046966a5920bac1cfa2384b31556a3400006b50a6c48818a60002d8635a925ea24aaa86c1a8da6a4b02c057a53a4b59cda9e3acbe37a351833618480000000d9484a0b5b96e0d9b1952000388640a28dc9c580005972d7849a0b3e34305d6b3989a6a54264291608c6000000002d1f0c5c2aef600019a86db88a260a80008b89d200001f9a6c88f648fc921e00000000000cd0da50000603b1b69a9350aaa29c5e22d0c9845c0000b962dacaab1b9c9bd280abda08e09a9b924c440dae34e8564546800000026c600032801b9b3f6b9d1ca4000383264333964d72720d2f8a623f217cc0001acc0000000e4f2be486832cc4b0af0415423ae9b423ce54b9d4a5270d9c1db2eaebd2106aac6800061700000001a08000105012500000002426b4f1ca6b5fa6f21230000000182266b101c0aa80005251b72132393a0000076173a684db48fe45e7253cbe20000000000092e108e016800000036f0d4d945c000000000016bc600000000025da1bf80009b2800055199766018cecde0241e4aa8f5e00000000000000ddd9f1239680003b218dc1b5188a6cda9725602da232300002e4800000009f20002cca7e51bc23ae37141d4800081e08c83c08eac402328e9b0a3541ba800017818b2a7c861073410a6b59a22e000358a14a04449d70acc0000eb40000762c4119fc2728e485
  | 63 => 0x4ff000000000960000306000000025d11467c11cce78d221c84d14e832500000002f4471600009700000694209eb82391493ab7f05f81106c4ab45000000007e32c7c000129a00009e2cbc20262d52cac0000a4ecf932c40000000000000034880008f29db42a01f386061f80beb81d210e8000717100c4a40000c2bb03491d0000cb81fa63e113948849ee214c1b7c4b0060cdaeb67e0001330aae800039300008c4000043e9576000186cd8b22a0c468000d3320080000cb00001ac624c0000882800000030d20001af48bf22f070f2b58a21b202b08817c735292400014da0000000b58000062aa4ac8e39ec48fa0000d080000b6f9e80739b2fc70fa00cd372c6425338fc446000062596384c800000ce062000015440000000c890aca000000000011727900d0ebbe095c0000000dc380003c8ade6a0a99f44a4af2e9de21e4533a2f2b9501c284b1b762b81ce818eb3aeac931d87460000c750baedbd0c76000000000000000002fbe000000083312ec000000036c80000003426000000000000009b83606acaaa047cf203e000000091d9234d8ea3fc2198da272badcc7e89dc2b87a8488b08000dd380009518f6601e2ed80000000983000073d012a48280000000000b06800000009200001bd82f909ba0002e408ed102a000000000000000000000c98000000005bc5d89cdcb0f326c583b80cb28242cd04311664284da2d88000bc78aea00013364ba872a7091f48a110aacbc623d80002a1ad1a80005d1904ab378cfe500a19471f0000db91fcc66d30660741872000065645a1a649428ebec9ab20cb1c36ae23e322ebe980000000bf2a83000000000000000e5e00000000001b7e00031fec220000002940e26380004ca8608c1e00009cc8000000213c9551d5421c99e6a65b41a9a513e04250000d7989ac6738000b8d8000c39acfc8ad81140001f161302de8c4b8000513800000037e8ce416169dfaf0e3f98000cc01b80c2d9caa3750364c1880004f7b7281a180000002a72a0c8efa2810000b6ca25400023fe00016a005494ea72fb4b6000000000000006e7872eb82a760dadb024000328ce0d1a9e0000000b4e000000000000001cc43ce1b5c51e2e8c44c0c1aa878a501950ee0a4b171e81c2c480001b9232d9e6e113023c63794bae1600008da244c9c683d83a4aff48a7ad420001ee400016689fb9bc00002d542cd274ecac34885c8800000000000000000ddd27103e78000000089caa58000dee0000000000000000001fd8000000000000004b00000000000230a000078e2aa8000cfa90b2cb88bcec172d5a8d88b3615c390628200447fc0f9a216945000009ea0001bca96a0000000314007a80000002a0a000000070a800000016fc000121433e167c5d0375e000000000502c89a8aea400006220002f5ce1b8e520003
  | 64 => 0x2ec0001e260002bc2000090ecd9319200009bc00000002b4000000000000000000cd52e2200000003a89da2b1ea78a53880000003666000000000000002c1800000027f000000007a8330800000006f70000186b080000216082da318b178b0e0008b2e000180a0003822000000000026daddf0000c3ca0ae5d5b448a1400000000000229800000005a01e80b0c259800000032bad21b59e00000000001f7c25d80000000492000000010283a418a0134d9422d000000000000eda0000c088c580000000596000358200011f2711125c0712b6c00027623c1251896c04dc000331420e0600000108804eb83896e9ac400007c2000014ed8f8dce0e81a8e0003342c30b1ea00024f0482000016798b673b80006aea776de4950253104debd0103e40429ce552af9c15a9c4c95eb7d42cb0e90830a524d3f8404dd2a93cabda15c0001b3c490000075cab0e5e7ae4e7cf8000a7fb83a00000002440000b43800050880000001e68000000018500000002ebc00000006d782f4000194e000079e24e00000001524cd780000be0bea0003244784b626000000018900486aca5827739cc212a8000000000045a8de687fa1f6c6d01228ef843cdf1abccb38aae42bc000021800002590000a4400000f0384c0001a5ae2533800b4b4f2c130e98a851a7a0b28000b488000b999974000166eba615063ea8000d731fde478ac820000000000225c0000000000027c850b376c8000000003254297ae2e000394c3443960a42027400000007b52aead8700000000d4c8d199001cd800000000003a30bd82a0a144205244681228cacf3309400000005cc000000000000001c8c00021ee00005fc000000000022e634a00006e080009410ffada0164cad18000000096000000000cf00000000000a969df494700000002de0000371000032a800000000000000ccea7daa882e60d111a4691080000000000000000089b935aa8080004c000003a1afd2b81358092cacf805818864e1845caff9874b60acb200009ec0000000dc90f50000000029198ee0000e14a339cc67df827e0002f50e0a27d20f303de01e94bcb490000804039857d0000baca3848bb15deb5330580000000000000000000006ec000000000000001e60d838ee200000005dc956e82e85f40fa2b660000b50d9138ba6d6903200024eece692e05071ab6242156a00022065b68b40ddf836c2d4944200000000001d6c00000003478eb619c8000a849d58a283268c3da7b85eba36e000000046717840000000705a6e203e254000000004abb50253ea47e1d299c2c7780000000000458b4d2a5e800000000000000000000385e0000da0783115e000041e0000fd487200004de8000a0b19160000000d57a8c400000009699148a088000a66b7c8b6d000000000002328000000000000000000002190
  | 65 => 0x167428e977c00000007719d6e07c88f29a0800010c80002d708064690000ce53576ce32a842d6a7385adadb0b750d380001ea2000000061b8000000004e0000000000000034d000016c8000000000083a0000ac6000010080000000e0643c8000783952a0000000056b4302140c120feb95056f0000a760a6600000000000000927982c0000000c258cbee39b8906eca958a7723e01ca296441a0000000000048c31e8cae004659f8e701bd18eac3030689dc9b7a170844600011c2b3ca2f49cc290a7cc82c4b8523b6cf220f6000000059032f600021d08ac8000258892e0003896ac4a3408c8850ae2c0000d9e02126a026ced95337229e8000264940052b00001a3800060f2f569be000000016c8dfb80001288000377000000000000000000dd000009ff912016e80000000000000114edd3000092a8000bd4800000002da000000000019b600000000001ef87a2981000016de0000000042a4e43e188121a814fc0930000000264a2801c40000000097486ee757000098a0000be8000015700000001f8aae8a9a49ed80000000000c5d2c5a0000aa40000000c76800000020ac00036e8499b4d45cb9fe823a38a4d320c4472c1e726780000000002e7a62f3655b00009af1b78000248077f0886000000000035e20f3800000009f09f3
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xcb4761d121440091e90cb9a428802a6d2117348510024f8402e690a2000da474d892144001b48e831242880036c1d3704851026e3b38ecb2022000c7571d96404400717f0eb2480881baa720d64901102fd56412c9202204ccb671592404401536908b8e60880062fa12768c1100045ec24ed18220048f5819da30440010ff0abb2608800a1f215764c1100045fc22ec98220018bc845d930440011df04bb260880223b209764c1100061e3a6ca9822000c3f65dd13044001878cbba26088003271d3634c11000637b2ee49822000c6c65dc930440018deca39260880031b194724c11000667b18e49822054ccc631c930440018e8cbb8a608800a1f216760c1100247a40cec182201887c865d430440010ff0fb28608802e1f61f650c1100061f3a6ca182204dc7671d94304400187ecaba060880030f195740c11000637b2ce41822000c6c659c830440018decab9060880031b195720c1100063bb2ae21822000c74655c4304401536908b8e40880062fa1276881100045ec24ed10220048f5819da20440010ff0abb2408800a1f21576481100045fc22ec90220018bc845d920440011bf06bb240880263720d76481100061e3a6ca9022000c3f65dd12044001878cbba2408800317d9773481100062e32ee69022000c5f651cd20440018b8ca39a4088173331887348110006563a6c49022000ccc73d8920440091ed0db8a40880031d19771481100143e42cec10220048f4819d820440210f90cba840880021fe1f650811005c3ec3eca1022000c3e74d94204409b8ece3b2840880030fd9574081100061e32ae81022000c5f659cc20440018b8cb398408800317d9573081100062e32ae61022000c77655c420440018e8cab8840880030f9d365841100061fb2ae90822000c3c655d2104409b8ecedb2c20880034d9d365841100245e43aa8b2020008bf845d5630400317908baac60800e3d2057558c1000c5f43ee8b182090c9c7494d63040091b90ea9ac60823f271d15358c1000d4e422c721820418bf845d943040091790eb2286080123721d6350c100045fc22eab1020018bc845d562040071e902baac4080062fa1f7458810476563a4a4b1020048ec87549620411b958e8a92c408006ab21162908102045fc22eca1020048bc8759142040091d90eb1284080272798d74cc8100064eba2c79902008cae625d2320400195ae8b1464080022fe11764c81000c5e422ec99020048dc8758d320401159904b1a64080123b21d624c81004d6641ac499020008bf845d8320400317908bb0640802333dd9320c81000666bb26419020008bf845db300400317908bb660080022fe1176c801000c5e422ed9002000c7475dd9100401556d09bb220080032da1376440100065ac26ec8802000c7776dd5100401556908b1a200802aad2116244010
  | 1 => 0x90eb228688026a720d6450d1033556412c8a1a20048f686dc543440018e8cbb8a86880022fe1173d891000c5e422e7b12200287e86dd562440010fd0fb2ac4880030f1d365589100043f438cab122000c3c74195624400187ecbba2c4880030f19774589100062fb2ee6b122000c5c65dcd62440018beca39ac4880031719473589100045fc22eab1220018bc845d562440011bf06baac4880263720d75589100047bc0aeab122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000cac74dc96244001998e7b92c48800b1b1d65258910476563a4a4b122092ccc7394962440051d90ea92c4882372b1d1525891048e6639aa4b122000c7475dc5624400187ce9b28c4880030f9d065189100061fb2ae83122000c3c655d062440011df0eb10c488002ab21162189100056641ac4312200087f855da42440050f90abb484880123d21971909100143f42eeca12200087d85dd942440010ff0abb2848800a1f21576509100046fc1aeca1220098dc835d942440011df04bb284880222f21d64509103a54e41ac8a122008aac8259142440091ed0db8a84880031d19771509100043fc2aed992200287c855db324400187ce9b2e64880030fd9574cc9100061e32ae99922000cae74d8b32440091e90cb8e64880031d19571cc9100043fc2aed192200287c855da324400187ce9b2c64880030fd95748c9100061e32ae91922000c9e74d8e32440091e90cb8c64880031d195718c9100143f42eec992200087d85dd932440010ff0abb2648800a1f215764c9100045fc22ec99220018bc845d9324400317d083b264880022f610764c9100143e42cec192200087f855d832440050f90abb064880022fe11760c91000c5e422ec192200087c865d432440010ff0fb2864880021f61f650c91000567432641922000acc864c83244001c9eca990648821f93195320c9100247a432e2192200a9b4845c432440071f10cb806488003724c9700c91027ed820ee0a0a200287c859db31440010f90cbae62880021fe1f65cc5100043ec3ecb98a2000c74659da314401536d093b4628802a6d211728c5100061e3a6ca98a2000c3f65dd13144001878cbba26288003271d3634c5100069a3a6ca98a200a9b687dd131440e5968edba262881ff2d1d8744c510006ca3a6c698a2000d947418d3144001b60e9b82628800a1f21676c85100043e432eb90a200087f87d9721440010fb0fb2e42880031d1967688510054db424ed10a200a9b4845ce2144001878e9b2a42880030fd9774485100061e32ee890a2000cac74d892144001a68e9b2a428802a6da1f74485103265a3b6e890a207c
  | 2 => 0xd644c21000657326e49842000cad64dc9308400195cc839261080032b590724c2100945ec36e8904200c8bc87591208400193cc9b9a41080032759373482100064f320e69042000c9d641cd20840174ed0db8eca88002cda1371d951026d3b40ee9b2a2000a7581dd365440014bf06ba6ca880029720d74d951000537c12e9b2a2000a6c825d3654400187ae83a6ca880028fe1173d95100051e422e7b2a2000a6f825cf65440014d904b9eca880028fa1073d95100051ec20e7b2a2000c5d731cf654409b4ed0239eca880029d60473d95100051fc22e5b2a2000a3c845cb65440014bf06b96ca880029720d72d95100051f420e5b2a2000a3d841cb654409b4ed02396ca880029d60472d95100051f426e3b2a2000a3d84dc7654407f4f501b8eca880038dd0765d91100063ab88cbb2220048f581dd764440010fd0fb2ac8880021fa1c65591100071a208cab222000c5f65dcd64440018b8cbb9ac88800317d9473591100062e328e6b222000c9c641cd6444001b288239ac8880031bd9772591100063632ee4b222000c6f651c964440018d8ca392c8880032b1907259110006d2208e4b22200287e87dd564440011bf06baac8880263720d755911000477c12eab2220088ec825d564440010fd0e3aac88800a2f21d54591104b64e39aa8b222095cac72551644409956902aa2c88802637a1f73591100062fbaee6b222000c5c75dcd64440018beea39ac888003171d473591100064fba0e6b2220088ee87dc964440018deebb92c8880031b1d7725911000667b9ee4b222000ccc73dc964440018deea392c8880031b1d4725911000657ba0e4b222000ccf731c96444001998e6392c8880022fe1172d8d1000c5e422e5b1a200087e87d956344001878e9b2ac6880021fa1c6558d100061e3a0cab1a2000c3f65dd16344001878cbba2c6880031bd977258d100063632ee4b1a2000c6f651c963440018d8ca392c6880022fe117558d1000c5e422eab1a20008ef825d563440111d904baac6880023de057558d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100064e3a6e6b1a2002c5c7594d6344121938e929ac688253331ca5358d100146e43aa6b1a208fc9c7454d6344127998e4a9ac6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100063a3aee2b1a2000c3e74d94634400187ce8328c6880030fd957418d100061e32ae831a20008df8758c634400153908b18c688002b32096318d100043fc2aed21a200287c855da43440091e90cb8c868800a1fa177650d100043ec2eeca1a200087f855d943440050f90abb2868800237e0d7650d1000477c12eca1a20088ec825d9434401317
  | 3 => 0x4196200d9b4845c432c400196ac8b8865882026da1f744c7103ecdb43ee890e200d9b4845cd21c400796ce2b24818802b2d99171903100065ab22e32062004ab48159140c400196ac9b8a81880366d21171cc3100045ec36e8986206e8be8759130c40db1790eb2261880032b993724c31000656b26e49862000cae641c930c400195ac839261881533398c724c31000666b18e49862000c3e645d430c402f17f0cba061880362fe1d640c3100061f3aac81862000c3d7559030c400796ce2b2061880032b992720c31000656b24e41862000cae645c830c400195ac8b9061880032d991710c3100065ab22e2186200d9b4845c720c400117b0dba2418817e2fa1d64483102f45e43ac89062000c9e64dcd20c400193ac9b9a41880032799073483100064eb20e6906205ccce621cd20c4001998e6b1241880030f991750831007c5fc32e8106200d8bf8759020c400187ceab2041880030f5d5640831001e5b38ac81062000c9e649cc20c400193ac939841880032799173083100064eb22e61062000cb6645c420c400196ac8b884188012aea0265992104bf58b0aa132420048be87d51648400187eebaa2c908002a7a0f54592100054ec1ea8b242000aae82d51648400155b05aa2c9080122f21d54592100255d404cab242004e3a50995648400187eeb3aac908002a7a0e75592100054ec1ceab242000aae829d5648400155b053aac908012aea0275592100055cc04eab2420008be87d4d648400117b0fa9ac908002aba0b535921000556c16a6b242000e1f5394d648400117d0fa92c9080022f61f52592100054f41ea4b242000a9d83d49648400147f0ab8ac9080028f21571592100054fc1ae2b242000a9c835c5648400155f04b8ac908002ab20971592100246e43aa6b1c20018be84dc9638400117b09b92c7080122fe1d6490e100245e43ac8a1c20018be84dcd628400117b09b9ac5080123b21d5258a100245fc3ac921420048bc84dd942840091790eb2285080062fa1176cca100045fc32e999420008bf87593328400117b0eb2665080062fa11768ca100045fc32e919420008bf87592328400117b0eb2465080123721d634ca1004566412c699420048ec87589328401359906b1265080030f991750ca100061f3aac81942000c3d755903284009974e0b20650802333dd9320ca1000666bb2641942086e8e644c83284001d1ac899065080032e591700ca10006e4992e01942000cb964dc1418400187cc8bae63080271798d75cc6100061f3aac998c2000c3d7559331840018baeab1e63080022f61b744c6103945f43ac898c207f8bc87591318400187cc8bae43080231b98975c86100061f3aac990c2000c3d7559321840018daeab1643080022f61b74486103245f43ac890c207c8bc87591218403517b0dba261080322f21
  | 4 => 0x8001b18e839a401018673e18734802030e67430e690040619cd861cd20080a999b0c39a401015353a1473480202a6a6c28e69004061ccf651cd20080c3a9cca39a401000333594734802030ea6b28e69004000c4d651cd20080c3b1cc839a401018763590734802030ee3308e69004061dc5611cd20080c399cc039a40101877298073480202a47643ac69004054ccc7358d20080a999f0eb1a4010002b3a1d63480200056643ac69004000ccc8758d20080011990eb1a4010003a3dd16348020007463a2c69004004ccf7058d2008011d96e0b1a40100123d205755931001c5f43ea8b262000c3f75d5164c400153d07aa2c988002a760f545931000557416a8b262000aad82d5164c40071790eaa2c98800ead20554593100061fbaceab262000a9e839d564c400153b073aac988002aba0a755931000556c14eab262003ab6819d564c400156b033aac988002ade05755931001d5a40aeab262000a3e859cd64c400147b0b39ac988002aba0a735931000556c14e6b262003ab6819cd64c4083968e339ac98800ead20573593104065a388e6b2620008be87d4d64c400117b0fa9ac988002aba0b535931000556c16a6b262000e1f5394d64c400756d0329ac988002ad60653593100051f42ce4b262000a3d859c964c400153d07392c988002a760e725931001d5b40ce4b262040cb4719c964c400756902b92c9881f72d1c472593100045f43ea4b2620008bd87d4964c400153d07a92c988002a760f525931001d5b40ca4b262000ab58194964c409f968e3b82c9880028fe1570593100051e42ae0b262000a9f835c164c400153906b82c988002abe09705931000556412e0b262000ab78154164c400756902a82c9880362fa1c50593100045ec38a0b262000a9e8314164c400153b06282c988002aba08505931000556c10a0b262003ab68114164c400156b02282c98800e3721d5358f1000c5f426e4b1e20008bd84dc963c400717f0eb248788106ad2056490f1001e5b38ac921e2000cb5645c643c40091e902bb2878800e2f21d6450f100065ab26e2a1e20018be84dcd62c400117b09b9ac58800e3b21d5258b1001c5fc3ac92162040ab48159242c400796ce2b2485880032d5917190b1001c5e426eca1620048f4815d942c40071790eb2285880032d5937150b1000c5f422ed99620008bf865d332c400117f0eb2665880022f61d64ccb1001c77c3ac599620018be845da32c400117f0cba465880022fe1d648cb100045ec3ac919620038df8758e32c40050fd0bbb265880021f617764cb100247b40eec9962000c3e645d432c40138bcc6ba865880231b989750cb100061f3aac81962000c3d7559032c400796ce2b206588003175d5630cb1000636baac41962000acf864c832c400159b0c990658821ba3991320cb1000746b226
  | 5 => 0x2bc600755842004572412e8b084000ad683d5161080015ab07aa2c210022b9a0b545842000572c16a8b084000e375495161080014ed0b39ac2100029d61673584200055bc22e6b084000ab4845cd61080115c904b9ac210002ada1073584200055ac20e6b084000ab684d4d610800156b09a9ac210022b9a0b535842000572c16a6b084000e575394d61080115cd05a1ac210002b960b43584200245e426eca084008c6c725954108011998e4b1a82100031b597725042000656b26e4a084000ccd63dc941080091e90eb0a821000339dc961504200143f42aed988400087f865d7310800187cc8bae62100271798d75cc42040e3b30aeb988400087f8759731080010fb0eb2e62100030f9d564cc4200061ebaac99884000c5e7558f31080018baeab1e62100031d9d561cc4200063abaac39884008c6e72596310801195ce4b246210023339c9638c42000636b2ae51884000cad645ca310800199ac6b94621000f39985728c42000c5e426ec98840008bf845d9310800317908bb262100030f1d1654c42004636392ca98840008bd86dd1310800187ccbba262100030f597744c4203964f31ee89884041cb661dd1310800117d0eb2262100022f21d644c4200064fba2c69884000c9c7458d3108011998e4b1a62100031b597724c42000666b1ee49884000cb7745853108001968e8b0a621000339dc9614c42000c5f422ec1884000c3e74594310800117f0cba062100030f995740c4200061eb2ae81884009c9e635d0310800796cc2ba062100022fe1d640c4200045ec3ac81884000c9e7458c310800193ae8b1862100032d9d1610c4200065aba2c218840048dd835db30080111d904bb6601015333cc976cc02004636392cb9804000e4f325973008011998e4b1e60100062f213764c0200246e41eec98040568ef82dd93008001878e8b2a60100231b1c9654c0200d45ec36e89804000c3e65dd1300800187acbba260101bb2798f744c0200045f43ac8980400f8bc875913008011958e4b22601000327dd1634c0200064e3a2c69804008ccc7258d30080018dccbb9260100031b597724c02000657326e49804000cad64dc930080ad99cc7b9260100033358f724c02030ce743e649804000acd86cc930080ad99eed992601000393597324c0200065bba4c29804000cb47498530080019cee530a6010023391ca614c0200065bba2c29804000cb47458530080019cee4b0a6010023391c9614c02000657c26ec9004000cac84dd9200800199f07bb240100033320f76480200063739aca9004000c6c7359520080098dee0b2a40100239adc1654802000657bb6e89004000e2d65dd1200800195eec3a240100038b594744802030ce743ee69004000ccf76dcd2008001c9acbb9a401000333dd8734802000726b28e69004000d8f741cd2
  | 6 => 0x253d400e2b284010a79801c5650800917d0faa2c8100030fdd754590200054f41ea8b204000a9d83d51640801155d05aa2c8100122f21d54590200061fbaceab204000a9e839d5640800153b073aac810022aba0a755902000556c14eab204008aac825cd640800117d0fa9ac8100022f61f535902004557416a6b204000aad82d4d6408001c3ea729ac810022ab20971590200045f438a2b2040008bd87145640800153d0628ac810002a760c515902004557410a2b204000aad8214564080095750028ac810002ae600515902004c6f43ea931840008dd87d52630801159d05aa4c610002b360b5498c200070faa4a931840098de8714663080011bb0e28cc610002a7a105198c200054ec20a33184008ace82146630800159b0428cc610012b6a005198c200056cc00a33184094ccc32dd563080111d904baac61024f330c97558c200246f43ea6b184000c5f75d4d630800153d09a9ac610002a76135358c2004567416a6b184002c5e7594d6308129998e529ac6100123721d5358c2004566412a6b184093ccc7254d63080091bd0fa1ac610022b3a0b4358c200143f42ee2b18400087d85dc56308129998e5baac61000317dd67558c200054f424eab184000a9d849d5630801159d053aac610002b360a7558c2000567c12eab184008acc825d56308127998e4baac610022b3a0a7458c2000566c14e8b184008acc825d163080011bd0faa2c6100023761f5458c2004567416a8b184000acd82d516308001c3ea92a2c61000297a177158c200052ec2ee2b184008ace829c5630800153f08b8ac610002a72117158c2004566412e2b184000a9e841c5630800153b0838ac61000237a1c5158c200046ec38a2b184000a9e84145630800153b0828ac610022b3a085158c2000566c10a2b184004ada8014563080015b30028ac6100122fe1d6490c2004476412eca184008c6c7259543080091790eb2286100123721d6350c2004666392c6a184000c6d65dc9430800195ac9b9286100033358f7250c2000657422ed9904000cad845db320801199d06bb664100233360d76cc8202a667982ed9904000e2e745973208001c5ae8b2e64100231b9cd65cc8200472739acb9904008acf8758f32080a9d1ce8b1e6410153a35d163cc82000636b2ae19904000ccd635c332080015ad07aa4c210002b560f549842004573416a93084000ae582d526108001c6ea92a4c210002ada1353984200055ac26a73084008ae682d4e61080015cb05a9cc21000395d4e53984200247b43ea2b0840048f487545610800156d0828ac210002ad61051584200056b418a2b084000ad58314561080115cd0428ac210012bca0051584200055b420eab084000ab5841d561080015ad063aac210002b560c755842004573410eab084000ae5821d561080095e5003aac21
  | 7 => 0x5c635d7314800187cebb2662900030f5d764cc5200062f3aec798a4000c5d75d8f3148001958c8b9662900273318d72cc5200045fc22ed18a40018bc845da314800317d09bb262900022f613764c52000c5f424ec98a40008bd849d93148003179083b262900022fa1b744c5203964e31ee898a40008be87d9131480011790fb22629000327dd3634c5200064e3a6c698a40018bc849d8314800117f08bb062900062f211760c5200045e432e818a4009c9c635d0314800117f0fb2062900022f61f640c5200064f3a6c618a4000c9d74d8c3148013998c6b9062900273618e700c5200045f436e890a407d8be87d91214800193ee9b1a4290003271d363485200064fba0c690a4000c9c7418d214800196ec938c80900372d19271901200066bb1ce32024000cd4639c6404800196ec8b8c809002b2d19171901200066bb1ae32024000cd4635c640480bf958e5b228090173331c863501200066631ee4a024009ccc635cb30480095990c9966090023331d932cc12002476c14ed1824061ace868ca30480b999ced19460900022fe11764c12000c5e422ec982405e8be86dd130480dd938c7ba260901b62fa1f644c1202fc5e43ec8982405fcac72d91304800193ee9b1a6090003271d3634c1202ee66396c69824000caf64dc93048001958c9b92609015b3318f724c120024e643a649824004acc864c93048011998ec9926090012f2201324c12000c5e424ec18240048ec829d83048001878c8ba860900271718d750c1200bc5e432e81824009c9c635d0304800117f0fb20609004a2f61f640c1200061f3aec81824000c3d75d9030480bf95ce5b206090003179d7630c1200062ebaec61824000c9e74d8c304800193ae9b186090177339cb630c12000657b22e41824000cac645c8304800199ec6b9060900273318d720c120004e6c3c641824061ace868c830480bb99ced1906090003535d6320c1200065bb24e21824000cb4649c430480019aec738860900273518e710c1200065bb22e21824000cb4645c430480019aec6b8860900273518d710c1202fe573b6c91024001cae7619220480111d90cb9c409015b3318d73881202ee673b6c71024009cce7618e2048001d1ec831c4090003a3190638812030e67438c71024056ccd8718e20480adc9d0a31c409015b93614638812030e67ba8c71024000ccd7518e20480014bd07ba2ca100029760f745942004537416e8b284010a6d82dd1650800187ee93a2ca100028fa1373594200051ec26e6b284008a6e82dcd65080214db05b9aca1000317dce73594204a726194e6b284098a6f825cd65080114d904b9aca1024f930c973594200453741686b284000a6d82d0d650800147d0838aca100028f61071594200052f418e2b284000a5d831c565080114dd0438aca100429b60871594200
  | 8 => 0xcaa90c690003a3d915218d2000746322a431a40098de87d5063480011bb0faa0c690172b3a0b5418d2000566c16a831a4000e1f5495063480b959d042a0c690002b36085418d2004c6f43ea431a40008dd87d48634800153d09a90c690002a76135218d202e567c3ca431a4092acd87948634812359b0b290c69024b939d65218d2049726baca431a4061ace80948634812359f0ea90c690246b361d5218d202e567c2aa431a405ce4f855486348123c9ceaa90c690247935d55218d2030d66402a431a405cace82d44634800159b05a88c6900039354a5118d2004c6f438a231a40008dd87144634800153d08288c690002a76105118d202e567410a231a4000acd821446348001c9aa4288c690002b6a005118d200056cc00a231a405cace82104634800159b04208c690172b3a0b5018d2000566c16a031a4000e4d52d40634800159f04a80c690172b32095018d2000726a92a031a40098de8714063480011bb0e280c690002a7a105018d200054ec20a031a405cace82140634800159b04280c690002b5a045018d200056ac08a031a405cace82d00634800159b05a00c690002a7e112018d200054e4224031a40098dc835da43480bf95ce5b2486900123b2197290d2004e6631ae521a40008df835d943480011df04bb286900262fa1f6450d2000c6f43ec6a1a4000cbb641c14248003179093b664900022f21974cc92004e4e31ae999240008bf87d93324800117b0fb266490003279d363cc9200064eba6c79924009cd8639c3324800195f093b464900032b212768c92030e67c1ced1924056cce539da324800199aa73b464900032b9db648c920006573b0c91924009ace86d8e324800199cedb1c6490002d3614638c92000747b20c71924000e8c6418e32480bfd1865b226490022b3a0b634c9200066db18e09924009ace86d8d3248001d1ec831a6490003a3190634c9202e6e5b98e09924002c6e7554b61480015cb05a8ec290002b960851d852000732a90a3b0a4000af180147614800193ec939cc2900032719273985200064fb22e730a4000c9c645ce614800193ce9b1cc290003275d363985200064f3a0c730a4000c9d7418e614800117d0fb22c2900030fdd764585200061e3aec8b0a40008be87191614800187eea322c2900030f1d464585200064fb26e6b0a4000c9c64dcd614800193ec839ac2900032719073585200046f43ec6b0a4000c5f75d8d61480018b8ebb1ac29000327dd363585200064e3a6c6b0a40008de8718d61480018beea31ac290003171d463585200064fba0c6b0a4000c9c7418d61480011ef0eb08c2900029d21561185200046fc1aed20a40098dc835da41480131bd07bb282900023760f765052001d5b40ec8a0a40008bf845db314800317908bb6629000e3720d76cc5200061e322eb98a4009c
  | 9 => 0x51d91200045ec38a3b224000a9e83147644800153b0628ec89017eaba0851d912000556c10a3b224000aba8014764480015730028ec8900022fa1c50d91200945ec38a1b224000a9e83143644800153b06286c89017eaba0850d912000556c10a1b224000ab681143644800156b02286c8900032719373591200064e320e6b2240008bf845d564480011bf06baac8900263720d75591200047bc0aeab2240038f4815d564480131bd0fb9ac89000327dd373591200064fba0e6b224000ccc73dc9644800117b0f328c890002a7a0e65191200054ec1cca3224000aad82994644800117f0eb28c890002a7e0d65191200054e41aca3224000ab781594644800156902b28c89017aaba08651912000556432a43224000e2f6554864480018baeba9ec690002a7a1353d8d200054ec26a7b1a4000acd82d4f63480051bf0ea9ec6900021fe1571d8d200143e42ae3b1a4000a9e84997634800153b0932ec690002a7e1165d8d200054e422cbb1a4000ad78159763480015a902b2ec690003a319252d8d2000746322a5b1a4000c5d751d7634800153d083aec690002a761075d8d202ed67410ebb1a4000acd821d763480011bd0faa6c6900023761f54d8d202ed67416a9b1a4000acd82d536348001c3ea92a6c690187339cb72d8d200054fc22e5b1a4000a9c845cb63480011bd0fa96c6900023761f52d8d200054f426a5b1a4000a9d84d4b634800153d09b8ec690002a761371d8d200054f424e3b1a4000a9d849c763480014bf0ab8ec6900029721571d8d200046f438a3b1a40008dd87147634800153d0828ec690002a761051d8d202ed67410a3b1a4000acd8214763480015b50028ec690002b660051d8d200046f438a1b1a40008dd87143634800153d08286c690002a761050d8d202ed67410a1b1a4000acd8214363480015ad02286c690002b560450d8d2004e4e31ae931a4000c9e74d8e634800193ae9b1cc6900022fa1f6458d200045f438c8b1a40008bf845d5634800317908baac69000237e0d7558d2000477c12eab1a40008f7815d563480071e902baac69000327dd37358d200064e3a6e6b1a4000caf74dc96348001958e9b92c6900271718d7518d200061f3aec831a4000c3d75d90634800187cea320c6900030f5d46418d200046fc3ac631a4000a9f8458c634800153908b18c690003179da7518d200062f3b2ea31a40008dd87994634800153d09328c690002a76126518d200046fc3aca31a4000a9f84594634800153908b28c690002b5e056518d200056a40aca31a4000c9e76d906348001c3cebb20c690003875d76418d200046ec3cc831a40008df87590634800193cec320c690003879d46418d200070eba8c831a4000e8f645c86348001d18c8b90c690002b3a1a5218d2000747b24a431a4000e8c649486348001c9e
  | 10 => 0x9806000c9f761d1300c001c3aca3a2601818673a1f724c03000667bb6e49806000e4d65dc9300c00199eec392601800393594724c030006c7ba0e49806000d8c741c9300c0c339f0c392601818733a18724c03030ce6c30e4980605cccd861c9300c0b9a9d0a392601817353614724c03030e67b28e49806061d4e651c9300c00199aca392601818753594724c03000626b28e49806061d8e641c9300c0c3b1ac8392601818771984724c03030ee2b08e49806061cce601c9300c0c3b94c039260181723721d624c0302e666392c49806000ace87589300c0015990eb1260180033321d624c03000747ba2c49806000e8c74589300c013d96e0b1260180023de05755932001c7a40aeab26400287e85dc563c80010fb0bb8ac7900222fe1d6490f2004c5ec26eca1e40008bf845d561c800317908baac3900062fa1f745872046e563a2a4b0e40008bf845da31c800317908bb463900022fe11764c72000c5e422ec98e4000cb7649c640c801b968c938c819017237e1d63cc3202e4e7c3a659864008ccc7258d30c80018bec6ba861900271718d750c320006a7192ea186405cccf635c830c8013998c6b9061900122f21d54592200043fc2ae3b1c400287c855c7638800117f08baac7100062f2117558e200047bc0aeab1c40038f4815d5638800317d0fba2c710243271d25358e200246e43aa6b1c408fc9c7454d638800195ee9b92c7100032b1d37258e2020d5b40ec921c40008bf845d943880091790eb22871017637e1d63cca2030ce7c3ac799440548ef865c332880bb59b0fb1865101873361f630ca2030d67c2ec61944000acd85d8c32880bbc9cebb186510177935d7630ca2030d67406c61944061eca80d8c32880c399ee1b18651018733d8d700ca200163a3aca2b0c40048f48754561880010ff0abb2831000a1f21576506200046fc1aeca0c40098dc835d9418800717d0fb22831000eada0764506200045fc22ed98c40018bc845db31880010ff0abb2631000a1f215764c6200045fc22ec98c40018bc845d93188001968e8b0a63100032d1d1614862030ce743e6498440568ef8758f20880ad99ce6b1e41100030f5d754d91200054f41ea9b224000a9d83d53644800155b05aa6c89000a2fe1d54d91200054f41ccbb224000a9d83997644800153f06b2ec890002a720d65d91200055bc0acbb224000ab481597644811b95ceca96c8900030f5d475d91200054f418ebb224000a9d831d764480bf55d043aec890002ab60875d91200051f428e7b224000a3d851cf644800155b0439ec8900022fa1f53d91200045ec3ea7b22405faae82d4f644800155b05a9ec89000387d4e53d91200055b40ee5b224000ab581dcb644800117d0fa96c8900022f61f52d91200054f41ea5b224000a9d83d4b644800196ee338ec8900022fa1c
  | 11 => 0xc0011db0e28ac418002aba10515883000556c20a2b106009ace83145620c00159b0628ac418012baa00515883000574c00a2b106009c5c73595420c0018bacbb9a84180032759373508300247643ac4a106000ccf73589420c013998e6b12841800327a11768c8300064ec22ed1906009cce825da320c01399b04bb46418003879d1658c8300070eba2cb1906009c5e72596320c013c9ce4b2c6418173a39d1628c8302e746ba2c51906000c5d655c2320c00199ac4b846418026b5a0f54984300056ac1ea93086000ae682d52610c0015cb05aa4c2180038dd5254984300055b426a53086000ab584d4a610c0135ad07a94c218002b560f52984300247b43ea2b0860048f487545610c00156d0828ac218002ad610515843004d6b418a2b086000ae682145610c0015cb0428ac218012bca0051584300055b420eab086000ab5841d5610c0135ad063aac218002b560c755843000573410eab086000ae5821d5610c0095e5003aac218002bc600755843004d6a41ae8b086009ad683d51610c0015ab07aa2c218002b9a0b545843000572c16a8b086000e3754951610c0014ed0b392c2180029d61672584300055bc22e4b086000ab4845c9610c0135a906b92c218002ada1072584300055ac20e4b086000ab684d49610c00156b09a92c218026b5a0f52584300056ac1ea4b086009ad683d09610c0015ab07a12c2180122f213765043004e2e39acaa086000c5d65dcd410c00193ac9b9a821800333dcd625043004e6639ac4a0860048f487585410c0019aee6b0a821800a1fa1576c84300043fc32eb9086000c3e645d7210c0118dcc4bae42181fb1d98575c84300043fc3acb908600087d87597210c00187ceab2642180030f5d564c8430006373aac59086000c6d7558b210c0018eceab0e42180031d5d561c843004e2f39acb1086009c9e73592210c0018bacab9c421800327591738843001e6b30ae71086009cce7358a210c00199ae6b1442180062f21376484300045fc22ec90860018bc845d9210c001878e8b2a4218027171cd65484300045ec36e89086000c3e65dd1210c00187acbba242181932b98b74484302065b30ee890860008be87591210c0011790eb22421800317597734843000657ba2c49086000cac74589210c00199ee6b124218027331cd62484300065bba2c29086000cb474585210c0019aee6b0a42180062fa1176084300061f3a2ca10860008bf865d0210c00187ccaba042180030f595740843004657312e81086003cb6615d0210c00117f0eb2042180022f61d6408430006573a2c41086000cad74588210c00196ce8b0842180032d5d161084300064fc26ec9806000c9c84dd9300c00199f05bb260180033320b764c0300062e392ca9806004c5f70595300c013cb6e0b2a601800327ddb744c0300070eb2ee8
  | 12 => 0x22f612764853000c5e420ec90a60008be86dd1214c0c9958c5ba242980022fa1f64485300045e43ec890a6000caf74d89214c001958e9b1242980062f21276085300045fc22ec10a60018bc845d8214c0011790cba042980232b18974085300045fc3ec810a60008bd87d90214c011998c4b9842980032b9d3620853000656ba6c410a6008ce8629c0214c00196ec938c80980372d192719013000673b14e32026000ce4629c6404c00196ec8b8c809802b2d191719013000673b12e32026000ce4625c6404c0dd938e7b22809800333dcc62501302a666398c4a02606ec9e76d92304c00393cec324609802637219728c1302ee66312e51826000e8f6418a304c001d18c8314609818733a1c628c1302ee66c38c5182605de4e8518a304c0bbc9b0a314609818733dd4628c13000666ba8c51826009a5e83dd1650c0314bb07ba2ca180029ba0b745943000536c16e8b286000c3f749d1650c00147d09b92ca180028f613725943004d2f41ee4b286018a5d83dc9650c125c9865392ca1826697e0d725943004d2e41ae4b286091e4c325c9650c0134bd07a12ca180029760f42594300051f420e2b286000a3d841c5650c0134bd0638aca180629760c715943000537410e2b286000a6d821c5650c0094f50038aca180629e60071594300245f43ea8b206000c3f75d51640c01353d07aa2c818002aba0b545903000556c16a8b2060048bc87551640c00187eeb3aac818026a7a0e75590300054ec1ceab206000aae829d5640c00155b053aac818026a720d72590300045f43ea4b2060008bd87d49640c01353d07a92c818002a760f525903004d4e41ae2b2060008be87145640c00117b0e28ac818026a7a0c51590300054ec18a2b206000aae82145640c00155b0428ac818012aea0051590300055cc00a2b2060088ee87d52620c0011db0faa4c418026b3a0f549883000566c1ea93106000e2f54952620c0111dd0e28cc4180023b61c519883000557420a33106000aad84146620c01359d0628cc418002b360c519883002575400a33106000ae980146620c12599865baac4180263720d755883048e66192eab1060048ee87d49620c00155d09a92c418002ab613525883004d6741ea4b1060048ec87549620c01359906a92c418026b3a0f42588300143f42ee2b10600087d85dc5620c125998e7baac418002aba12755883000556c24eab106009ace839d5620c00159b073aac418002b3e0d755883004d6641aeab106009ace839d1620c00159b073a2c418026b320d74588300047743ea8b1060008ed87d51620c01359d07aa2c418002b360f545883000717aa4a8b106000a6e85dc5620c0014db0bb8ac418026b3a0e715883000557c22e2b106000aac845c5620c01359906b8ac418002aba10715883000556c20e2b1060008ee8714562
  | 13 => 0x717aa4a83126054ace83150624c00159b062a0c4980223ba1f531893000476c3ea63126000aae84d4c624c00155b09a98c4981539394f53189304a567c3ca63126094acd8794c624c129c9ceb298c498253935d6531893030d67404a63126093acf8754c624c0a9c9f0aa98c49824f939d5531893049f26baaa63126061acc8054c624c0a959d07a88c498002b360f511893000726a9ca231260088ee87144624c0011db0e288c498002aba10511893000556c20a23126054ace83144624c00159b06288c4980039354c511893000575400a23126000ae980144624c0a959d06208c498002b360c41189302a56741ea03126000acd83d40624c001c9aa7a80c498002b3e0d50189302a56641aa03126000e4d53540624c0111dd0e280c4980023b61c501893000557420a03126000aad84140624c0a959d06280c498002b360c501893000573408a03126000ae581140624c0a959d07a00c498002b360f401893000557c22603126000aac844c0624c0111d904bb484981bb279cf649093004666312e721260018ee87d89424c00193f093b664980032721276cc93030e67c14ed992605dcce529db324c00199aa53b66498003279db64cc9300064f3b0c99926000cce76d8b324c00169b0a3166498003a3d9062cc93000746320c599260008bc865d2324c011958c4ba464980022f61f648c930006573a6c51926000cad74d8a324c0119d0c538464981bba30cb644c93000675b10e09926008ace86d89324c001d1ec83126498003a3190624c9302a6e5b90e09926002c5e7554f614c0015ab07a8ec298002b560c51d85300072aa98a3b0a6000af180147614c00195ec9394c2980032b192729853000657b22e530a6000cac645ca614c00195ce9b14c2980032b5d36298530006573a0c530a6000cad7418a614c00117d0fb22c2980030fdd764585300061e3aec8b0a60008be87191614c00187eea322c2980030f1d4645853000657b26e4b0a6000cac64dc9614c00195ec8392c2980032b19072585300047743ec4b0a6000c6f75d89614c0018d8ebb12c2980032bdd36258530006563a6c4b0a60008ee87189614c0018deea312c2980031b1d4625853000657ba0c4b0a6000cac74189614c0011ef0eb08c2980029d215611853000477c12ed20a60088ec825da414c0111dd05bb282980023b60b765053001d5b40ec8a0a60008be86dd1314c10117d0fb2262980032bdd3624c530006563a6c498a6000caf74189314c001958e831262980022fe1176c853000c5e422ed90a60038ec825db214c001878c8bae42980231b18975c85300061f3aec990a6000c3d75d93214c001938c8b9e42980233318973c8530006373aec590a6000c6d75d8b214c00117f08bb442980062f211768853000c5f426ec90a60008bd84dd9214c00317d093b24298
  | 14 => 0xd831cb644c00117d0fa96c8980022f61f52d91303754f41ea5b226000a9d83d4b644c00196ee338ec8980022fa1c51d91300045ec38a3b22606ea9e83147644c00153b0628ec898002aba0851d913000556c10a3b226000aba80147644c0015730028ec8980038ed4250d91300045f438a1b22601a8bd87143644c0dd53d06286c898002a760c50d913000557410a1b226000aad82143644c00156d02286c898002ad60450d913000656326e4b226000cac641c9644c00117f08baac8980023be09755913004476412eab2260008f7815d5644c0071e902baac8980032bdd3725913000657ba0e4b226000ccf731c9644c00117b0f328c898002a760e651913000557414ca3226000aad82994644c00117f0eb28c898002abe09651913000556412ca3226000ab781594644c00156902b28c8981b6a7a0c65191300054e432a63226000e1f6554c644c001976c83828698002aba1352d893000556c26a5b126000acd83d4b624c0051df0ea96c4980021fe1571d89300143e42ae3b126000aae84997624c00155b0932ec498002abe1165d893000556422cbb126000ae781597624c0015c902b2ec498003a319253d893000746322a7b126000aae841d7624c00155b083aec49815ab3a0c75d893000566c18ebb1260008ee87d53624c0011db0faa6c49815ab3a0f54d893000566c1ea9b126000e2f54953624c0011dd0fa9ec4980023b61f53d893000557426a7b126000aad84d4f624c0adc9ca7a9ec498002aba1371d893000556c26e3b126000aae849c7624c00155b0938ec4980029be1571d89300053642ae3b1260008ee87147624c0011db0e28ec498002aba1051d893000556c20a3b126056ace83147624c00159b0628ec498002baa0051d893000574c00a3b1260008ee87143624c0011db0e286c498002aba1050d893000556c20a1b126056ace83143624c00159b06286c498002b9a0450d893000572c08a1b126008cac625d2624c00195ce9b14c4980032b5d362989300045f43ec8b1260008be87191624c0118d8c4ba8c4980030f9d764189300061ebaec83126000c3e75190624c00187aea320c4980023be1d621893000557c22c43126000aac84588624c0018dced3a8c4980031b9d9751893000476c3cca3126000aae84994624c00155b09328c4980023be1d651893000557c22ca3126000aac84594624c0015cf02b28c498002b92056518930006573b6c83126000e2e75d90624c001c5aebb20c4980023b61e641893000477c3ac83126000cae76190624c001c5cea320c4980038b5d4641893000747b22e63126000e8c645cc624c00159d0d298c498003a3d92531893000746324a63126000e4f6554c624c001d1ec8a98c498003a319153189300447743ea831260008ed87d50624c0a959d07aa0c498002b360f541893000
  | 15 => 0x8b0863200032d5d1610c6403f63b30aeb90c8000c767558721900018eaeab0e432000f2d98574886400247a40eec90c8040cb661dd12190015968e8b0a43200123d605760864001e5b30ae810c800acb674584219000196ae8b08432000a37e1d53d8d400043fc2ae3b1a800287c855c763500011bf0eb18c6a0002b32096318d400045f436e4a1a8066cac62dc943500051df0ea96c4a00021fe1571d89400143e42ae3b1280008ef87588625000159906b10c4a00022fa1b73509403a64e31ee6a1280098bc849db32500cd958c4ba664a00222f212768c9403a64e31ae919280048bc865d132500138b8c6ba864a00231b189750c9400062ebaec61928000c6d75d88325000159d0c99064a0002b3219320c9400447c432e01928000dc9325c032500ff17f0ea1ec2a01f22fe1d42d85400047bc3ac230a80008bc865ce41500011790cb9482a002a6d61f61905400245ec24ed18a80018bc841d93150007179093b062a00023be09760c54004476412ec18a8000c9d74d8c315000917b093b442a00062f210764854001c5e424ec10a80008df835d821500131b906bb042a00032b5d3620854000c5e432e7202806ec9c635ce40500031790cb9480a017f2b18972901402665b434e32028000cb4639c64050001968c538c80a00132dd82719014006ed9b04e320280018bd87d86405009996ce3b0c80a00023de05755933001c7a40aeab26600287e85dc562cc0010fb0bb8ac5980222f6137650b300045fc22eab0e60018bc845d561cc00317d0fba2c39823f271d153587300045fc22ed10e60018bc845da21cc00117f08bb243980062f21176487300065bb24e3206600dcb4649c640cc0091790eaa2c9180022fe117558a3000c5e422eab1460008f7815d5628c0071e902baac51823b2b1d25258a300247643aa4b14608dcac74549628c08156d03b24851815a3be1d628ca3030ce7c3ac51946002c7475945618c0091e90ea8ac3180021fe1576506300143e42aeca0c60008ef825d9418c0111d904bb2831800e2fa1f645063001d5b40ec8a0c6000cb474585318c00117f08bb643180062f21176c86300043fc2aec90c600287c855d9218c00117f08bb243180062f21176486300065a3a2c290c605d8df8758b308c0bb99ce4b1661180030f5d754d91300054ec1ea9b226000aae82d53644c00155b05aa6c89800a2fe1d54d913000557414cbb226000aad82997644c00155f04b2ec898002ab20965d91300055bc0acbb226000ab481597644c11f93ceca9ec8980030f5d475d91303754f418ebb226000a9d831d7644c00155d043aec898002ab60875d91300055b40ee7b226000ab581dcf644c00117d0fa9ec8980022f61f53d91303770f29ea7b226000aae82d4f644c00155b05a9ec8980028fa1472d91300051ec28e5b226000a9
  | 16 => 0x3590210055ac0ca6b204203ab6819c1640840153f06b82c810802a720d705902104556412e0b204200ab781541640840756902a82c8108022fa1c50590210045ec38a0b204200a9e83141640840153b06282c810822aba08505902100556c10a0b204203ab681141640840156b02282c81080e3721d5358c2101c5fc3ac92184200cad645ca43084071790eb2286108022fe11739802100c5e422e730042038f88754160084091b90ea9ac7200022fe197190e4020e5b30ae321c806d8bf865c2439000117d0f21ac52017eaba0a4358a400247643aa4b1480008bf8758e42900dd93ce6b1c85200022fe197190a402065b30ae3214805e8bf865c2429000193ae8b1e65200032b5d1628ca4004566412c69948009acc83589329001199eec9906520003335d9320ca4000cdc422e01948000dc9325c03290001d2cc721cc320003a998a429864006d5b426a730c8000ab584d4e61900015cd05a9cc320002b960b53986400072ba9ca730c809de944394e619000156f08a9cc320036ad21153986404e74a21aa730c8041ab58790e619010156d0721cc320037a5a0e43986400055b4148730c8000ab58090e619001b56d09a94c320002ad61352986400056b41ea530c8000ad583d4a6190137d4885294c320002ade11529864006d5a422a530c809aea44254a619008156b0f214c320002ada0e42986403ed5b4148530c800dea68290a619000156b01214c320036ada1332986400055ac266530c800dab6848ca619000156b09194c320002ade11329864006d5a4226530c8000a76850ca61900014eb0a194c320002ade10329864006d5a4206530c8000ec5320ca61900091e90ea8ac320002ad61051586400056b418a2b0c8000ad58314561900015cd0428ac320002b9608515864002579400a2b0c8003cb674dd9619000172906ba2c320002e920974586400555b420eab0c8000ab5841d561900015ad063aac320002b560c755864000573410eab0c8000ae5821d561900095e5003aac320002bc60075586400053b42ce6b0c8000a75859cd619000156f08b9ac320002ad61073586400555b426a6b0c8000ab584d4d61900015cd05a9ac320002b960b53586400072ba9ca6b0c8000a76859c961900014eb0b392c320002ade1172586400055ac20e4b0c800aab684d49619000156b09a92c320002b5a0f52586400056ac1ea4b0c800aab684cc9619000156b09992c32002aada1232586400055ac2464b0c8000a76850c961900014eb0a192c320003b14c832586400257940064b0c8000af1800c961901011790eb1a83201f62f21d625064001d5bc32c2a0c800a8bd86dc1419001bb66e3b8283202071d98575cc6400063b3aac398c8000c7575587319000796cc2ba463201072d987744c6400565a3a2c298c8003cb6615d0319001596ce
  | 17 => 0x64200cb681dd160c840196b03ba2c19080b1b9d5525832146e563a2a4b0642038bc87551648840117f08baac7108062f2117558e2101c7a40aeab1c42018be87dd16388521938e929ac71080e3721d5358e2147e4e3a2a6b1c4201a9c8458e43884131df0cb9487108273398d7290e2120c5fc22eca1c42038bc8759143884071b90eb1a87108272798d74cca210064eba2c799442038f887541608840187aebaa6c890802a7a0f54d91210054ec1ea9b224200aad82d53644840517f0eaa6c890802a7a0e65d91210054ec1ccbb224240aac8654b644851b95ceca96c8908030f5d475d91210054f418ebb224200a9d831d764484c955d043aec890902ab60875d91210045f43ea7b2242008bd87d4f64484c955d05a9ec890802ab60b53d91210070fa9ca7b2242408be87d4b644840117b0fa96c890802a7a0f52d91210054ec1ea5b224264e2e52d4b6448481c6ca3a8ec890992ad60470d91210045f438a1b2242008bd87143644840153d06286c890802a760c50d912132557410a1b224200aad82143644848156d02286c890802ad60450d91210045fc22eab2242008f7815d5644840117b0f328c890802a7a0e65191210054ec1cca3224200aad82994644840117f0eb28c890802ade0565191213e557410ca322427daac865486448401c5ecaa90c8908038b19552191210447ac0eebb1a42028df8754f63484138b8c6bacc6908030f9d76498d210061ebaec931a4200c3e75192634840187aea324c690803175d76398d210045f43ec8b1a42008be87191634840117f08baac6908062f2117558d210047dc02eab1a42048f8805d563484050fd0bb8ac6908021f6177158d210046fc3ac631a42098be87d914348481968e3b2284909f62f21974cc9212045fc3ec999242008bd87d9332484c9d1865b2264909932b1cb64505210061e322eb98a4209c5c635d7314840187cebb2662908030f5d764cc5210062ebaec798a4200cac645cb3148413998c6b9662908022fe11764c52100c5e422ec98a427c8be86dd131484ff17d0fb2262909922f21f644c5212045e436e8b0242008be87d91604840187eebb22c0908030f1d764581210045f438c8b024200c3f751916048401878ea322c09080327d9373581210064e326e6b024200c9f641cd6048401938c839ac0908023ee1d60181210045fc22e630242018bc845cc60484071e902baac81080e2fa1f54590210061fbaea8b204200a9e83d51640840153b07aa2c810822aba0b545902101c5e43aa8b204203ab481551640840187eeb3aac810802a7a0e75590210054ec1ceab204208aae829d5640840155b053aac810802ade05755902101d5a40aeab204208aae829cd640840117d0fa9ac8108022f61f535902104557416a6b204200aad82d4d6408401c3ea729ac81080eada065
  | 18 => 0xc40156b02286c8988022fe1175591310047bc0aeab2262008bd87994644c40153b07328c898802aba0a651913100556c14ca32262008bf87594644c40156f02b28c8989fea7a0c65191314054e432a63226200e1f6554c644c401c38caa98c8989072d1c76450d3104c7ac0eebb1262028ef8754b624c4118d8c4bacc4988030f9d764989310061ebaec93126200c3e75192624c40187aea324c4988031b5d762989310045f43ec8b1262008be87191624c4011df0eb10c498a022f219748c9310045ec3ec91926272e8c32d91324c4e5938e7b2282989062f21b74581310045f43ec8b026200c3f75d91604c401878ebb22c0988022fa1c64581310061fba8c8b026200c3c75191604c40195ec9b92c0988032b193725813100657b20e4b026200cac641c9604c4011f70eb00c0988022fe11721813100c5e422e430262038f4815d5640c40717d0faa2c8188030fdd7545903104d4f41ea8b206200aae82d51640c40155b05aa2c81880e2f21d545903101d5a40aa8b206200c3f759d5640c41353d073aac818802a760e755903100557414eab206200aad829d5640c40156f02baac81880ead205755903104d4f41ce4b2062008be87d49640c40117b0fa92c818826a7a0f52590310054ec1ea4b206203ab681949640c40156b03292c81880eada06705903104d4e41ae0b206200aaf825c1640c40155904b82c818802ade05505903101d5a40aa0b2062008be87141640c40117b0e282c818826a7a0c50590310054ec18a0b206200aae82141640c40155b04282c81880eada0450590310055ac08a0b2062038ec87549620c40193ac8b9c84188022fe11729803100c5e422e530062038f887541600c4014bd07ba2cb908029760f745972104537416e8b2e4228a6d82dd165c840187ee93a2cb908029de0574597213f53a40ae8b2e4200a3e84dcd65c840147b09b9acb908229ba0b735972114536c16e6b2e4200a3e849cd65c840147b0939acb9080317dce73597213f53b40ce6b2e4200a75819cd65c84114dd05a1acb908029b60b43597210051fc22e2b2e4200a3c845c565c853d4df04b8acb908028fe1170597210051e422e0b2e4200a77815c165c84fd4e902b82cb908028fa1070597210051ec20e0b2e4200a5e831c165c84014bb06382cb908229ba08705972114536c10e0b2e427ea76811c165c84014eb02382cb908229ba08405972100536c1080b2e42088de87d0d63c841159d05a1ac7908222fe1d6490f2104c5ec26eca1e4208c6c7259541c84018dacbb9283908021fe1975cc7210043fc3acb98e4200c3c7459531c84118d8e4b2a63908030f997744c7210061eb2ee898e4200c9c7458d31c8411998e4b1a63908031b597724c7210045fc22e730642018bc845ce60c840117f08baac1908062f211755832100c5f43ee8b
  | 19 => 0xe3b21d5258a410045fc3ac721482008bf865c2429040336908b8865208022f61e43982410045ec3c8530482038f4815d560904071f10ea82c12080a37e1d53d8d4104e2e31aeb31a8200c5d75d8e63504c995ec9394c6a080333d8d7298d4104e6631ae531a82008df8758c63504fb17d0db9286a093e2fa187050d4101477c3aa5b128208c6c625d662504c993ec939cc4a082333189739894100636baec53128200ccd73d8a62504011df0eb10c4a0a022fa1b735094127c5f430e0a1282088dc835db325040193ae9b1e64a08223b209768c94100656ba6c5192820287e85dd932504010fb0bbb264a080e2f219744c94104567416c69928209ace83d89325040199cec99064a0823331d9320c9410447a432e219282018f581dd7605049f56902aa6c0a09b62fe1d43d81412f45fc3a85b0282a0cf171d8260504e593ec839ac0a09932bd9072581410047dc3ac03028209a5e83dd165cc4614bb07ba2cb988029ba0b745973100536c16e8b2e6200c3f749d165cc4014ef02ba2cb98a069d20574597310051f426e4b2e6200a3d84dc965cc4134bd07b92cb988c29760f72597310051f424e4b2e6200a3d849c965cc5034ed03392cb988029d606725973104d2f41e84b2e6200a5d83d0965cc40147f08b8acb988028f21171597314fd2fc1ae2b2e6200a3f845c165cc40147908b82cb988029de05705973140d3a40ae0b2e6200a3e841c165cc40147b08382cb9882697a0c70597311852ec18e0b2e6200a6e821c165cc4014db04382cb98a069da0470597310053ac08e0b2e6209a5e8310165cc4014bb06202cb98826b3a0f4258b310445ec26eca166209c5c7359541cc4018bacbb9a83988022fe11729833100c5e422e530662008bf845d560cc40317908baac1988062fa1f74583310065b40ee8b066200cb581dd160cc4058bceaa9ac198a3f271d1535833101c5e43aa8b2462008bf845d5628c40317908baac51880e3d2057558a3100c5f43ee8b14628ecac74949628c4071d90ea92c518a372b1d15258a3104667312e72146201aac8458a428c4071d90eb1285188232b989748ca3100656ba2c519462038f887541608c40187aebaa6c898802a760f54d913100557416a9b226200aad82d53644c40517f0eaa6c898802aba0a65d913100556c14cbb226241a9c8654f644c51f93ceca9ec8988030f5d475d91313954f418ebb226241a9d831d7644c40155d043aec898802ab60875d913120c5f43ea7b2262008bd87d4f644c4e5c3ca7a9ec898802aba0b53d913100556c16a7b2262008be87d4b644c40117b0fa96c8989caa7a0f52d91310054ec1ea5b226241e3651d47644c4e556b02386c8988022fa1c50d91310045ec38a1b226272a9e83143644c40153b06286c898802aba0850d913100556c10a1b226241ab681143644
  | 20 => 0x5f426e2b0464008bd84dc5608c80517f0eaa6c8990023de05755913201c7a40aeab2264008fb805d5644c8091f100baac8990022fe1170d853200c5e422e1b0a64008f787584614c80117f08b8ec0990062f21171d81320047dc3ac03026400c6f325d4604c8018bc64ba8c099003170c9751813200636192ea3026404c5f305d4604c8098ba60ba8c0990131bc81751813202636902ea3026409a5e83dd1650c8694bb07ba2ca190229ba0b74594321a536c16e8b286400c3f749d1650c8014ef02ba2ca190029d20574594320051fc22e2b286400a3c845c5650c80147d0838aca190028f610715943204d2f418e2b286434a5d831c5650c8114dd0438aca190d29b60871594320053d400e2b286400a79801c5650c8134bd0620aca190029760c41594320453741082b286400a6d82105650c80147f08b82ca190028f21170594323852fc1ae0b286409a5c835c1650c8c54df04b82ca190229b20970594320053bc0ae0b286400a74815c1650c80147d08382ca190028f610705943204d2f418e0b286434a5d831c1650c8114dd04382ca190d29b60870594320053b408e0b286400a75811c1650c8011ef02baac81900e3d20575590320466743eec9906400ccf75dd9320c80199aebbb26419003a3a13764c83200746c26ec9906400acd80dd9320c80159f0cba2641921ed3a17714c832005a6c2ee29906400acd869c5320c80159f0cb8a6419002e3e11714c832435c6422e29906486b8e841c5320c80171b0838a6419002b361a704c83200567c32e09906400b8f845c1320c90d71908b82641921ed3a14704c832005a6c28e09906486b8e841c1320c80171b083826419002f1a04704c832005e2c08e099064619cf861c1320c8b939b0c382641918733618704c83230ce7c28e09906461d4e851c1320c80139b0a382641918753614704c832004a6c28e0990645cd4e651c1320c8b9a9aca382641918763a10704c83230ec6c20e09906461dc6811c1320c8c3b8b02382641918733d80704c83230ee5300e0990645cdc9601c1320c80117f08baac2190062f211755843200c5f43ee8b08648fc9c7454d610c91b958e8a92c2190039354d52584320043fc2ae3300640287c855c6600c80117f08baac0190062f21175580320047bc0aeab0064038f4815d5600c80317d0fba2c0191bb271cf74580322fe56396e8b00646dc9c731d1600c8bd958e43a2c01900b179d5535803247e4e3a2a6b006402c6e75549600c91b958e8a92c0190039354d525803200667c3a64b006400acc874c9600c8019990e992c019002b3e15325803200566c2a64b006400e8f744c9600c801d18e8992c019003b2e01325803230d6640264b006400ec8804c9600c80159100992c019023b2dc1325803201c6e43aa6b1c82008bf865c2439040117d0f21ac5208
  | 21 => 0xc000800000e000002001400200300080000060010000000004003000000000600000000040000000000263b21d5258a430143f42ee2b14860087d85dc56290c010ff0ab8cc12180a1f21571982430047bc0aeab0486038f4815d56090c051df0ea96c4a18023be1d62189430063abaea3b0a8600ab5841476150c015ab0628ec2a1802bc60051d85430047bc3ac230a8641cb7649c66050c011f70eb00c0a18223721d5358e420143f42ee2b1c840087d85dc5639080117b0c38287211fe2f21d43586420043fc2ae3304840287c855c660908011ef02baac12100e3d205755824236c5e43a86b0484028df8754f63508011bf0eb18c6a11f22f2197190d422f45e432e121a8400c7575d47615080156b0828ec2a1002b960851d854200578c00a3b0a84008f787584615088196ec938cc0a10023ee1d60181420045ec3c8630284098be87d5164cc80187eebaa2c999026a7a0f545933200556c16a8b2664098bc8755164cc80187eeb3aac999026a7a0e75593320054ec1ceab266466aae829d564cc80155b053aac9990022fa1f52593320045ec3ea4b266409a9e83d4964cc80153b07a92c999026a720d71593320045f438a2b2664008bd8714564cc81353d0628ac999002a760c515933233557410a2b266400aad8214564cc8015750028ac999002ae600515933204d4f41ce0b266400ab6819c164cc80156b03382c999002abe0970593320045f438a0b2664008bd8714164cc81353d06282c999002a760c505933233557410a0b266400aad8214164cc80156d02282c999002ad60450593320064eb26e6a166402c6c7554961cc8015cb05a8ac399026b5a0c515873200572c10a2b0e6400e655214561cc8015e30028ac3990062fa1370587320045ec26e0b0e640087f855c660cc8050f90ab8cc1990062fa1371583320045ec26e2b0664088be87d51648c80187eebaa2c919002a760f545923204557416a8b2464088bc87551648c80187eeb3aac9191d2a7a0e75592320054ec1ceab246408aae829d5648c80155b053aac9190022fa1f53592320045ec3ea6b246474e1e53d4d648c81155d05a9ac919002ab60b535923204556412e2b2464008be87145648c80117b0e28ac9191d2a7a0c51592320054ec18a2b246408aae82145648c80155b0428ac919002aea0051592320055cc00a2b246408aae829c1648c80156d03382c919002ad60670592320054fc1ae0b2464008be87141648c80117b0e282c9191d2a7a0c50592320054ec18a0b246408aae82141648c80155b04282c919002ada0450592320055ac08a0b246400cad64dc9438c8058b8eaa9ac319002b560f51586320056ac18a2b0c6400e5553145618c8115cd0428ac319002bc600515863200c5f426e0b0c64008bd84dc1618c8010ff0ab8cc11900a1f215719823200c
  | 22 => 0x6001000800c008001000800c0000010000000008000001800800a001000000000000000000000020010020000002000000000000200300000040020070008000002000000000000e00500200000000010008000006001000000000000600100180140000000000002007000802400a0050000000000000000000000000500280040040020010000002003000800000400200300040040000000000002000000000000000000000100020000018000000004000000400200300000040000000010000000004000000800200000300140040030018010000000000001400c00000000040000000018004002000000800c000000000800000800200480000080000008008002000000800400c0010008000002000000000000200a0000004004004000800800400000200280000010008000002006000800400400000000040000010040010000003003001400400a006000000400a001000400600000380000060010000000000000000001401200400000000080030008008008000003000400200a00100000020000030004000000000000000000000200000040020038008002003000800000000f000001800000000080100000010000004004001000000c00200900000080000000008000000007000800400000100200000000020010000002000001000400a000000800001800000000280000030020000002000000000800000100280000000000028028000001001800800a000000800802400400000000020070018000004000000004000000000080000000040008000016001000000400400100000000020000020040000001007800c002002000800401200c008800400600100080000060000000000004000000000000000000380140000010030000000001001000000000300100000060020008000004000000000000200300080080040030008020004001003003c00a0020010000004001000800800a00200100000000060000008000002001000c00400300000040060010008018002001000800c00000400080100000030048008000000000800000000a001800001e001000000c00000200680340000050070000006005000800000600000000000020000000000002000000804800400000000100040000018000000000000000000000100000000020000018000004000000000c0000030008004002003000000c0000080018014000002001800c004000001800800a005001000400e00e00000200000010018010016000003800c00200f0010000002000001800c00600100400040060050020008000002000000800e0030000008008007000801800800100100040060000000004000001000000400400200100000020000008024000003000800400200200300000040010000000000000000000400000100380000000
  | 23 => 0x4b45d233280015e40005042584a5075756aac28296000000000146a000590800000000000000000000002b600000000000000000000000000000000000034600000008dd00026541520002fe0000cbe00000011915bc3965d50a00bd600000001411261b300004dc4a266e000000019e84756d96500000001bf000000000033da8c0000000000085830e0000000fb40000001431af400000027b000024c2a51539d6c0000001bc88d821e5ec00023f17ce0720002ca0000094233218c000718000000071a21a00000010000761aaa414000000168800000035300000000000000001f080003a80000000150000000151c00000000016ec00000000000016346e94a395f00000fa27987f907200032619c80288dc0002548c420000001c5011c00052893ece9647c11784a108610b000254c0002ea000095c0006093dd8fe527c3db00000001540000000000744000000017c000ae311d87d033253315611749526cb4a602104a86890c8800000000000025413ba983071979d52ca6c28914d13020000001ac84dabc600012500e80000002ae9180000246000000000036b00000000000001ccc0000000000000000000000000000025a0008000004001000000800000000180020000028020016001000001800c000000000000e0000000000010000000001000200000000080000000010000006001001000000000a00000000040020000000000000000000c00000000080000020000000004002000001000c0000060008004004000000000000a0000010000012002001000400600000180000000060038000000000000800c002000006002400c0010010004000000000000000200200100000000090028000000000002000c0000000010004002000000000400000100180140000000000000000005001800400200000080040040040000000004000000801800000100380200040060008000000000002001400200000580000000000028000002004000002000000200000000020080008000002002000800000a0000020020000003001800c000000000000c000002000800c00800300000080000000000000000003004800000600300080040020000018004002001000000001e00500000040080000008020000001001000800a000002000400000300000140020010028000002026000001800c001000000400400200300080000000070000004000000000c006000000000400000100200000000000000000000000000800800400500080040000020008000000000000000c0020020000000000000000000c002000000000800200000000000040040000014004000000000000600a00000040040010000014000000001000c00e0000018008000004000001800e00200000000000000000000000001000001400400000000040040030030
  | 24 => 0x6e40003ca083958931e0005dc8000e6c3b85789af800000033004744506bb16e9cc0834a6200000010061dd0000000000980000000000000000000000000000fb168400000038f80007f63aa044880532698225f8f310324aa0000000000000090000110e00037396e8000a7932b800000000000000011c219200000000000004b88328be6000000000000080c16a800000000000000000006025638000eec00048f9248000017000000000000012480000000004ad1334000345000000157eac538382d455000015b2b3cd700001a499c0f540005a800013142821351974fa613500014349320000f9000171a0005c8800082a56400000000000000ec80000006a800000000007ed00000004ca00000000000000000001dc800015c1d09aa8000000129a0792de0004b280000000000000000000000000000070e00000003fd44e10323c80014b00000001630f8e0160830000a1e8045c58ffc71c17e000049cf6a00000000000000001b10000ce22bf5bf0000f98a4e43000000f80001002bd800069e245a35907a9e5000000025200000017c92fa59529b000000042609a2f140d6b5a218000000000000000003805a2076000000000000000008ee28d2d808494f80000a60000000af70001e7173254648a96115502320000000000917000000093e00012f098c00000006480016000000000864fb28410ab10509c6825000000150aa3a176800096400000000004886f33e4007c67095c2838605434230185800000051700000017360001010000d9e9d721782cc00000010b99b0aae0000000e0c00000000006f970e6e458800d00000000001fe00000000138bc40005b6023ac7d5d600007380000002c9000166800000000000008dab2e5b311b8c326fc00000009687ac000000000000000000015ce00000000000000001e892404cc76c03a8aed3228ea00010b80007292c40c402303e9384800000062b483800000000016100000004a3370ab48a184e138d800128a54800000000000002db8000bda00000022285f647f560092d69a0000001c053fe000000002ce685aa000171800033e0001d480009e90001e6161ea9d3660000672000000000177aa3e495000163a0000001cf41a000000008340000000001770000000000000084696e0002c803c20000000f08ef40000000000000aa3000000000000042a11c10b80005729204c6a9252109238000bc74ea81180009c30000000000a250002d00000000000000177e227544875435036b43d22d941e00000027d04420000000000000000312a5e17184c303115bc3dc70516c03980000000002f20d488ed5111b390f200000000000000000000000000000000243864c39000020c0b940000002d300d04cb2af28ec000469394184c0000003f9a4100005505aa88804e09e21662731
  | 25 => 0x83a00000007dc7970000000f2240a000032c0009c800013bc00083800000000000000000b9400000018a8000fc400000000000002f35cb800092a00000019f8000000000000000000000002c4cf000000020048bcb563ed9f700000000000000000000000000000000000000000000002f500000006ff0002b912100000001cfc53e0004bf8b5c40a00000000000000001f5955544000056fa7d915449d54a000000047400000a00002c500000000007eb4a227c000000049600000006564780000dae3dd00000000004610001f4400000017580011ec06a2daacd800091d00000000003a34d6803c000ad65b6ac24000000000000081600012088cc2f2000101929000000013880012161e213d0fa848c00030d966166447b1cc088cc9c6d3000000150800054ca2909ceb83532172c90c4e458b8e940009fc0002d3800092058c9128d1643559f800000000000021d8000000000000000000000000000000002528000cd2000000000000027408000003ea5372b01d0c19c0005b600000000560001780dfc74d3851d9400018639e0e6d0ee0b045d15491e2ad7000179572800000000014a40002ec000000000000000014ca0000001c7800008700002180004335bba838000459000000000099b5a400014825180000000000b5d3c48000000000000000000091c0000000000493000137c00000559100000000000000000b720004c4a24400072a18780000004271bb00000009ce388104956a0001cc9d4400000028d01201ae0004c39a4c000b65000022ce8a0000620e2c000b3b2cb943899800000000000005d1000000000000025da12c0000003f6000145232a35c87e91a80004441ee03b0a1e4f999d109a0005a18f50f5206f052a728bde0003fd800106e0554cd06b067a9eb498000109400022a8c706c60002cfa1b4000000593800097c599000000025a0000002f58000a920fe000050a0000002dcd1c000043c015d4ce340000000000017f0002ec00006850000000000000189244000091e00000004741b808b87800007c92d600011946462ce0e9853c0f83da294ced61b106b08897400000001a846840000000d40666af500000000000000000000fa40000002e410c200058c2ba01066082d913290e4acc1b625640000000000000f2a00000000014ac000000097040c044000000125c00000000012660000000000b06b7b0001c0000000008da4a00000004ff290950035b5a91364ecc00000000000000000000000000a69382000000000011b80014e4a773fe2a0c000000000048576a000072800000097011e00000000003ec2df400000000000000000000370000000000000000130a29607e88100000005d40000022000000000016c0005252cc515251b1da889117840659295a80000000000b700000000001a7c000000
  | 26 => 0x1a1980c77e7880002e9800059b000000144c000000000000000005e00000000000000dd000000000000000003010002ce52285095388c7c14800000007fc00000000000000000000001110000000307a3480000000001234f1e0005e9000000000000015dcc9a2724dc000000068f0001aaca4e000029821558ca160000d910fa000000000088400017c01840001640000000000000155aa4000000000000016d600000000000000000000000000000000000000000000004500000000001a5088ea381f30d44544000000000157aa5d000094800000000000000006e53282f4cd8e000000000034c4d500005500760002da013400027d2fb0f0c36a0003cb00000008c600022756068242ce800128c3a93a0010c00000000000000000003170000a8a30a00007b01a46124979e8cafc65949c11140002fe00000000000000002f6089e000550aecc0000000002bb4c6e0000000000000b140001cec0000000000d50974000000000153c00000024695e600000000000009e60c40a740006a00000000a2272100000c40000003c08000226a0a00027bc000afd5ce1f5c00000000d00003400002ad000101200004b0000e4c00000000000002830000b5000000000023940000000000a4800000000003780c04c64e9ac914021c30002a4400000033980000007ba000000000000000000011880000000160130000000000000000000000009584180001d8c00000048900016c8a3746c892000032300003d80005f53e686000000004cc80000009c00000000000000000000166840204813380007cf5b38cd40000002b88000a4202b0a69f0cf046281282544418b53475800000009900000004d200007900000005c300024d8610bba3fb000000000000024e427eab800003dc0003c14509c895ba00000028c53540000001d855fe4c437a00017ca000000206c00000000000007620002b307409dc9352a980014720000002b10000000388800000010e1b2800000000053f1c3400000000003bce9e00000000000007f22d01be800064932d000006049e16513ac0000000000280db666606e15240000000001df959a76452814ac76eb7000008f8f424e800015e47260004eb248466e6330cf2a88eda5d4254000c00057300000000ee6e62ba0ee40384405498000314af901010b4000b0b0000000000000000121454013d07da1f956c52056caf680000000001ba0000000000000000000000000017aea95000000000000001e855400008f3cf80000000002eb1ad0802a2c0fc94e4d801f30000000000000173a3e880800014800012d400000015715f80000000d3c00000000007c14f02795342ac80cc8230000000000a551e00000dc637f0b98b100008b41ab00000000000a707191ae0ed00025e80000004b6ad055cc7ef0000000cd4000000000
  | 27 => 0x6936216900009800a400000016bc62c06c47383d105e0400d50000000000000000000056e12aad7c00080820488d41a86f9011942000000035ba4e8000783000114d16200000001ec00000010519200000000e62ab44300005772fa01d031b000115000064036f0000d4a00019491380000000001cac000a98000255850854a0000000000000000000000000000000000000000001c740000000000000000000446a5d00000000ba850c0000005b90000d600000001c309bc4410b880014487690fb8000000000377ad1801800017703680000005ab97c516600000026197046ca00020cc000000415000000000000005d0aeab1b0b2aba87746bc0f1980065a0005530dbc30868329d000000040d000000000000000004b8000000000000020a000072274400089e0001f98f7c0d55560c602aebdc00000000000005142b0414413e00001700001d1000000000000000000000000003d890940002590000a30000000000000000000047a8000000b0800000000000000000000000973000000000000000000009e035a00000014d41490000000000000000100cf1676e0001398000000523ae7800078700000000001191d5862c00000000000007e6a13000069d4320005e200000000000000000ef641700000000009a90000000000000000000056a0004df06ac4ac5f01fd2e8800000000009b0000a07000000000000000023e54de0000001a6012660a539a6308183714e7acac186000250800165200000000000002e20a7800000045c4718af8000000006a4080000000001e78f60b9a0000f4c6da8bd4f20000000142525800000000000019e4f2000000000013b20001b99bc800076f082205005449c5f080007fc262000287c69600029e80016b08ae0000000000b6a050acbcdaa0000002f500000005108c34c1600029c14b532e2bd39722009145a60da150c0005921899b8800033f351297c8f0b9d0000b200009c649e00010427ee000000000000013d800000014700026d942a00000000900000000e5aa3c00000027a0000d8a2260a500000009640000000a960730002048cf80003ca0ff40004dd0001a40000b261ea8689296000000138800062926d0001124b8021b8000000be000000005744760318000168325000000000000046712088481ef0002dd1282aa900014f86c282636c0384000732183aca8eaa0003c2823054c000000000000000020da2580000000002038470a440000d740001630000ff00000000001ee44161c542f07e133833a19895c0282bab195a14c0f403c236000000000000000015b804e0000ae000000046c000146c6760f28000a9a68227aae38c3a00040ea6c091e44b000000000000003eaa38e8c3e80000001608be40000000c76000000000000000000000000000000000b90d38000095162400000
  | 28 => 0x31027b800000000015440002fd21e80000005c000021b902e1d734b80004d60c700000009925140000000000b0d3578000f36681000000000000000018c1150000000000094e0000000d7c0000003472ebc0006b13ab14640000000000e688580002950000b226952421a9878800000018400002cf2c015e80003271818f60000744000034d1ee0003eb0000000000000164c00014032d800000000043a8000f244af5778000000000132000072e6d4000000000075300003640007a400000014b289b14997b89782c63ff8cd111e842410168cd080000001bac0000003ea000167c00028a86694cc8df00010ad0de0000000000000ae000000000000003d70000000000292178979600000000000000005e6067c18aa4d30a26dd0b00000000000000ace00000000009f2000174c02a0f94cb00000000000002bf869071605c00000000001450000ea07930000c30000000000000000075400000000008be000000048600025810a800000047700000000000000aa5196148000000162c0000002684b7a0000780dec5d80000001f40000a0300000000004d80000000c949d038185e800000000000013ce0001fc000105aa572389d296c0000486187c0000180001e3576800000024250300000000cb80000000002dd40001702088000000b7c00018c4000a181082288000000530000000058d0000000000000000000000000000000000000af280800000000000380000000000000000d2200008100000003cf49e80017cc47a000257d0e62c12640de95a600017a0001104ad116d9ab00000002350d9c51600000008fcab258500010fcd9a1c400017844540003b981e52468970001d38c08b861be85b4bcc9e845f9349014000000000167400052d9180868429599af0000061100000000000005de000150e0cc1149f280008845242a091de0001e4800083c9f8000000000000000012f42d4b4700000008ca06d0b700012520000c60000000357000149952e00000000005d20df000227c0002153d7800000000017aad28002000000158cb1c5cd1b48000da20000edad2cc684320000f8073e8703341c680000e900000000000002899e9514aad81df1cc400050a4a705bc0000005ed9914000000262aa3058000000000010ca0003840000f080002b4800013a16726a0454ae47bd0000ed00000000002d7118a0004da8510d3a5f4538070800040f00005c8cbc9c104519080fc0003d5a8454f600052280000006dd2aea71400000000000010440000002cd495c00004da02c0009190b40001556000000000000050200000008b4000000000077a0003938c78000000000235578200000000000009a049200000005900002cf55900004991afc0000004da257540c00000017e800024f10a1de422000002e8000b3c00004f21
  | 29 => 0x6a400000043e0000db800000000000000000000000b9e000000028c00002d1f2000066400013e259c72283e0e52e10c6c68700000000000000000a7026000021d896d55c00023400001b043931f17694ea4ff15b8e5150c0000001df0000758300a68936603a2f20000000bdf00000000000000be000032600018d000000000000000000000004878a9030a00022c181d4d628e00028300000000000000da4000000063d72c866075a92400000000000000003ac000176c00000000000000004630000000000311027800000000000000007b200000000000008c800022b4000000000000133a000000000000075c0000f8c000000000000000000000000000005ff4c70f3400000000000004dc00000000000000001c52d8d660000537107c0000003131f040520005890000f66b450000bc0000000000000017c00000005140000000002a2c00000000000011bc0002028000dd404c3918d700000000001cf80002751270000000000000000000053c000222443e0000000000422000000025c0003440b0223004c000000019c00000030700000000000170a8c49400057daae4000a40000000097252e5d200e4000a100000000a82000000240000066f44c800098e0000000000000000000000000004a00000000000000001f815f000032080010524960d782089e41cf00027d54000000000000dee0001a7000000000000024d000000000020700002da0002eec1c471717e28b80000003c5000082662f00000006a42684b90000c724db00000010d80fe0b081e0cf49e330b9b4129000000000d803c0005d600000000000000000000b420c1000000000000000003d45c10002c4400000000028249fc139000000000000017d1df551a00000000000006c200000015a01bf3622f340001d6377199c00077f000000175c0000258cec0000003b500000000003c700000000000000000000bc956a2188fd44b50000000000aaa00010800008a000000000009ba0000268000000000032133c38122626bc15a94f00006a418039c00006d8000000000213c78a000000262c0000002be80000005c236d00000009db00000000000004191870000a8a0000124a5888b00021908861a510799ac81c00047904b10200ea0bba3cc0002765c4a648000b493ea8000cee6c137800000008363bb80000003000002cdc8389a800006e87480000000e24000a61002188c0001d43c62bd0a0c0b93921d74fba19c298201c00057f0000244f0c5cc0000064ee84b601a80000000db00000010768d100000013b80a700000001e697b5918f88cea67d000000000070e0000000000000000111915e00000000000005be33f9d0800000005613a502a2df3a61858ab61783641ce47bc6180000000000b1511680000002d957d0000c9e00000000000000000000000fca0
  | 30 => 0x237a40d49e3ec00004bc9d4a5415809e16d04a6139856c2385581b71f9d40a0000469e9c00005900000014fe3a7440aaf80006a94bb800000089500018e800000014d00c8b4800010d800000096023100000b62e60002c055d265501f09840000000000ca00002090000e54e6e5d9000000000000058f000000000000000000000003b88000000000000000108a16259c24880d22d01b91d792308e83112d8860a8c9540800000000058610a055c52200000000000ba32580014bc911000000000095e0000d1800000023980012ec00000000000007e90000a540000000000000000000000000045889800018311fc0000001f140008a74fe88940000003cd09f8512000383047916e1c700009142a400000000013bca0d0000c80000000000147000000000011f83c8aa43baab8400000028800000006ae055842400028813780004be2990000aa8000a0b00017380000002680000b1e0003ef8000000850000000000066300000000000000001200000000000161c7b82390002b2c8ae3b65e780000000004e6a6b09809f126b9f2d2769df36fa9b40008e25760e21170ab70000168000760255ae60c7000000024ac0000004720000000b88243a29800000008903f00000000000000306ba909e2ed80000005ec80003ce5c4000057c00000000003800a29c941fa8b400000005d8d2960a000000000110a0000002a7174284900007ac33000022900006989ec1f280000009b200010417aa3140669e75408b690000000000000157a0ac00009c5b7000000000009c10e000094d00002c800000047615d859a53500004d877600000005d8cc2a465260000fc600000000011861a4000157c0000005f180007241220001c0800000000006ec210196000115800008000000000000005e887796fe0000000001328b7a0002d512a8542402a2c82a646b0112ef800000000008b88fa00000000016de15e00001509ca0005898000c3c00038e15b4000000000000000036a5d902200003f200000000006ba59e0d640009b90000000930606000245858e1fd3af800000012b18baa6cef000038900000000002ee80009ac00058e08700001e60000000f640000cd948c0008133f080013c20001cf000000000000000000007c02a200011980000001a6c0000000bd800000000032197ec57887f19b1cd400086a000207c7e207f0e0933c00000032c14c836e000080a56122600006300000000000000000f4400046111c9388b5e000000101a000434099c000000000149465e065000059800000000010200000000000fdce5a88e39c27b400000000000015e06c600026fc6c000000000000008ab0000000000000467a398b0c000441a2400000000000ae400003f2df8fc052e0000000000000a1400000007082c300000000001c822d85180007f00001
  | 31 => 0x9740002070000b78e4065400013dcffa12400023fcaf01a132e00012b665300000001827f10000000e1e0a63fa0000000000000000035a624000000051e0000001ea00001df00012240005fd2c0800000000004a9cbc0000000001b6400029400025081843af000000000000047a000000000006e8000000000000000159400017900000002e1000000138e84e19600000005000000000000ada228a98d3108561bb800000000029780000000004de80000000002f40001320422458194813e43a438ab0800015000023f421827f1d980017029fb31fa1482765680000c7455a0004bc917c00c0000000000a2c000000000000000000008f40000005159bf4000000000000000000042da2680000000002c1864280f0d19370c58b5b2611f910900004d58000000a9a0000000000a1c34323e0000000000062487c000000000000000000000000007c4268a2b03781fb000000036412300000001e20410000bfc08400033680000000000ce80016580002d9aabc00000019e00000000000ad00000009372d88f68000000012803945e0381a080012c669a2ab0000000000258800000000034522188a06fb00026985de9315caa4040009ea35b00000000001c28f493a46961d721014787a65a200001dc0005bc23ec000000241a01800000042c9e0000000000007240003824cf80000000000000000000000000134c0000000000000000000434800176211137027602140002a71a640000000000000456000000065400024754400000004885d2800171e000000000000000051e94ec15c0000e9a8d0ba00f50000d1ca527b64a515ec0000005b080003600004dd87380000000000f5c37a358511800114600000000005ac41612c000000000037c000000097531ea4982b2846000000000000000000013a8000000000000000000000000000000000000000bce392a50000000000000016b23090001d689e20004d727e400000000000000000000000001592000000000006e000000000000096900020d0000000000217c5ee0100002ac000060d00000000000002c580007780330001a205c6605000000134a0000000f1c000a7a17417a40004b700000000006800000e0000000019200000004313138000000000000000000000035180000000000000000ff40000000000000b9300000010981dc00000003da00800000000000000a8a5880003021698000000000000024879672c2a6000000000000000000000005011da07c20002858000000000000000000081a00000003a4664000063960493f0000000e920000000000000000558a3410225050000000000000000128000000055d8000b5a651068a270ece762519a90c8ea46700027093467133b82e9d4e800000000014b8835000000021a00036495ac000000000000000083c0001edc000
  | 32 => 0x28742e800000000022497f978400000000005300000cbaf7400051d00000000e0000000000049a1251070000c54bde00996095c44ad466991c32007120380000000002e380282744ed000231c0005ae00000000000004aa800121a000000000092e00000021540000000ae8fd9454b2d0000de175a1331f38000000b0743d9bb4bf286700d8da00009981981d1cd5a00005f940c98282e2a790d97a03660be9efc000b761e7236c00000053b00000003860000c38c78306000263400000000000000000003fa80000000002a000000000000f48000b565541af017816ea9f14080000002405a7800000097c42b926cde211600000000003f53fc80005367ce0000dd4bf00000000d340008c117013e400092d00000005684fd44a1fdcc2a3ef248a46c2d87c60002e157944485599658bc6b9f45d80000000003ff09300000000000000000bb75b8800105023400900000000005dc00000000000000000000000000241826400000016f0dd80001b821d06080001fa25240001cd316a72c00043c1589fa146400046d00009340004358000000000000000000000000000005a4000150800000000000000000004f8000113400000050e87c400000000012cc000000121000000000000004691d25613cc800000000029f9778f782082efa111786644000200800031937b0f7c0005d50000000000000000000102c1e820c80000000000001f780c80000000000bee0003ed084c0000210000000d2427755e26f15860001e404c40005c51e329f40005042c500000000000000878000a121be000000096b00000000002b3000000071e00000000010584ec0000000b4e0004c2000000000000022e42d63d60000ec0b505653a0ac38e162ce20ea5f800000041380016a20001c60000000000000285c00000037a800000011f0000a447a06a7200172547e5b83a427dc9f47ad11880000004a200000016f2be200027680000001d92428ace3a0000000000000000018680000000000001062000000087464400000000000002cb00000000000000002ad00002f9000000154e0000001a3400000000002040000000001b0d3c05a527001143b48b51ce8ac8a3caa0000000017a02f49380000004b8000259934e4fc28f800003a9fa4288000000ba338c80080000004a1800000000000000000000003599ce80000000d70eb401200000000000009680c68000000000000000000063200019885ec5c800025b14360002ebae28000aa538a9e803288d33ac80000009570ac00b00000000002690a620000002e48d6a000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x3e32003000865a00000000000000000004400000666a68206e1e5e1a62022216148a0e5200005000822800722a6c2400544e7a4264883a000000120070608c2e0018004a2c080a0044004678584c5c063800001c36100c008e263456747e84007600800000487c3c0000005000c0050c0030b021420004042920a00000006985498014561cc801a5153600515863230d13a4a325d4604c8c38c87061a704c83200453e59851c1320c80114d96614704c83230e13d81851c1320c8c384d60614704c83250f031d153549610c943c0c7454d525803200493654874c9600c8c30cc97615325803230cb2241854c9600c80188c87dd132580320062321c744c9600c8c32ca98e013258032005a2650804c9600c8016c19120132580322ecb2a5c804c9600c8c38ca97201325803230e92a54804c9600c8c3a4995201325803230ea2a50804c9600c8c3a89942013258032006a2dd0804c9600c801a8874201325803230eb0a44804c9600c8c3ac1912013258032006b04c9800c961900014c8964c9700c9400061361d53144624c001a495360051189302ee139d98518b324c001a0d8519062cc9300069454d80147614c001c0d65dd0724c03000703594741c9300c00144f98594724c03000513661651c9300c00188c87dd1624c0300062321c74589300c0c344e92d8d750c3200061361d521446348001a49526005118d202b6139d98518e3248001a0d85190638c920006985498014761480c384e865d6320c12030c33a5d86cc930080c384e87597324c02030e13a1d65dcd2008001c0d65dd0734802000703594741cd200800144f98594734802000513661651cd20080c30ce97a1d634802000613a548758d200800184d9521d63480200062321f7458d200800188c871d16348020006291c6829cd64c400189471a0e7259310006251c4835c164c40018a471209705931000493657864c832c401b0b498591710cb1000722591325c03284001c1465104735911000709194411c964440014c8964c9700c9100041b660651c9304400105d981947348110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa03694871d13258032
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4d
  | 6 => 0x4e
  | 7 => 0x124e
  | 8 => 0x3
  | 9 => 0x4
  | 10 => 0x94d
  | 11 => 0x94e
  | 12 => 0x124d
  | 13 => 0x138d
  | 14 => 0x138e
  | 15 => 0x8d
  | 16 => 0x8e
  | 17 => 0x128e
  | 18 => 0x98d
  | 19 => 0x98e
  | 20 => 0x128d
  | 21 => 0x150d
  | 22 => 0x150e
  | 23 => 0xcd
  | 24 => 0xce
  | 25 => 0x12ce
  | 26 => 0x9cd
  | 27 => 0x9ce
  | 28 => 0x12cd
  | 29 => 0x168d
  | 30 => 0x168e
  | 31 => 0xa0e
  | 32 => 0x130e
  | 33 => 0x20d
  | 34 => 0x20e
  | 35 => 0xb0d
  | 36 => 0xb0e
  | 37 => 0x140d
  | 38 => 0x140e
  | 39 => 0x154d
  | 40 => 0x154e
  | 41 => 0x24d
  | 42 => 0x24e
  | 43 => 0xb4d
  | 44 => 0xb4e
  | 45 => 0x144d
  | 46 => 0x144e
  | 47 => 0x16cd
  | 48 => 0x16ce
  | 49 => 0xb8e
  | 50 => 0x148e
  | 51 => 0x3cd
  | 52 => 0x3ce
  | 53 => 0xccd
  | 54 => 0xcce
  | 55 => 0x15cd
  | 56 => 0x15ce
  | 57 => 0x170d
  | 58 => 0x170e
  | 59 => 0xd0e
  | 60 => 0x160e
  | 61 => 0xe8e
  | 62 => 0x178e
  | 63 => 0x94056
  | 64 => 0x160a
  | 65 => 0x178a
  | 66 => 0x124956
  | 67 => 0x95256
  | 68 => 0xb0956
  | 69 => 0x94b16
  | 70 => 0x140956
  | 71 => 0x95416
  | 72 => 0xb4956
  | 73 => 0x94b56
  | 74 => 0x144956
  | 75 => 0x95456
  | 76 => 0xa0a
  | 77 => 0x134a
  | 78 => 0x139256
  | 79 => 0x180a
  | 80 => 0xb1396
  | 81 => 0x138b16
  | 82 => 0xb5396
  | 83 => 0x138b56
  | 84 => 0x8c
  | 85 => 0x98096
  | 86 => 0x128c
  | 87 => 0x170096
  | 88 => 0x99296
  | 89 => 0x98cd6
  | 90 => 0x15c996
  | 91 => 0x995d6
  | 92 => 0xcb
  | 93 => 0x12cb
  | 94 => 0x10b
  | 95 => 0x130b
  | 96 => 0x151296
  | 97 => 0x3c9
  | 98 => 0x3d296
  | 99 => 0x171296
  | 100 => 0x148b
  | 101 => 0x150cd6
  | 102 => 0xe8b
  | 103 => 0x9c0d6
  | 104 => 0x15c0d6
  | 105 => 0x9d2d6
  | 106 => 0x9ccd6
  | 107 => 0x1709d6
  | 108 => 0x9d716
  | 109 => 0x10c
  | 110 => 0x130c
  | 111 => 0x1692d6
  | 112 => 0x3d2d6
  | 113 => 0x15d2d6
  | 114 => 0x148c
  | 115 => 0x168cd6
  | 116 => 0xd0c
  | 117 => 0xa1316
  | 118 => 0xa1496
  | 119 => 0xa0d16
  | 120 => 0xa0e96
  | 121 => 0xb9316
  | 122 => 0x161316
  | 123 => 0x179316
  | 124 => 0x28b
  | 125 => 0x40a
  | 126 => 0xd4a
  | 127 => 0x28c
  | 128 => 0x58a
  | 129 => 0xeca
  | 130 => 0xb8d16
  | 131 => 0xb8e96
  | 132 => 0x161496
  | 133 => 0x179496
  | 134 => 0xcc3d5
  | 135 => 0xcc3d6
  | 136 => 0x3ccd6
  | 137 => 0x178d16
  | 138 => 0x18cb
  | 139 => 0x160e96
  | 140 => 0x188c
  | 141 => 0xd4d
  | 142 => 0x164d
  | 143 => 0xecd
  | 144 => 0x17cd
  | 145 => 0xd4c
  | 146 => 0x164c
  | 147 => 0xecb
  | 148 => 0x17cb
  | 149 => 0x104b
  | 150 => 0x104c
  | 151 => 0xa4955
  | 152 => 0x9716
  | 153 => 0xd5d6
  | 154 => 0xd5395
  | 155 => 0x165395
  | 156 => 0xed395
  | 157 => 0x17d395
  | 158 => 0x155416
  | 159 => 0x16d456
  | 160 => 0x138955
  | 161 => 0xecd55
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2625
  | 6 => 7348
  | 5 => 3049
  | 4 => 72
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
  | 7 => packedAt gbK7 (108500+((h/875+packedAt gbK7 (97125+(h % 875)*13) 13) % 4612)*13) 13
  | 6 => packedAt gbK6 (386990+((h/2449+packedAt gbK6 (352704+(h % 2449)*14) 14) % 10668)*14) 14
  | 5 => packedAt gbK5 (193099+((h/1016+packedAt gbK5 (179891+(h % 1016)*13) 13) % 5889)*13) 13
  | 4 => packedAt gbK4 (5208+((h/24+packedAt gbK4 (5040+(h % 24)*7) 7) % 104)*8) 8
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xf807f81e01fffffff03ffffff049a4cc1ff1ff
  | 1 => 0x3ff81fe001f07c1fffc3c07801b65b73127ecc
  | 2 => 0xc0001ffffe007fe0fffc007ffe386383e38f0f
  | 3 => 0x1fffffff8000ffffff800fc07c03fc0ff0
  | 4 => 0x1fffffffffff000000000fff8003fff000
  | 5 => 0xffffe00000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4810c00400509421100449092000804404b055
  | 1 => 0x10f0596030b42d1a76428350609209531256cc
  | 2 => 0x81210aaad2004b48aaa80466c6386381630b0a
  | 3 => 0x24214d3652d0010cd3336008bc07c02b80da0
  | 4 => 0x4849f1db9ce739c060218430dff8003dfe000
  | 5 => 0x27070001c0080200082020040f6d76a8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeeeefaa8eaa0feeeeeeefaa8eaa0feeeeeeefaa8eaa0feeeeeeefaa8eaa0feeeeeeefaa8eaa0feeeeeeefaa8eaa0feeeeeeefaa8eaa0feeeeeeefaa8eaa0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37277
namespace PEqualNP.Outside.L_meta_37277
open PEqualNP.Outside.L_meta_37277.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
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
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 10 := bs1_3_0
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
theorem bs4_3_0 : Interval s4Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 24 := bs4_3_0
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
theorem bs4_4_96 : Interval s4Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 117 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_3_0 : Interval s5Atlas 3 0 20 := block_range (n:=20) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 20 := bs5_3_0
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
theorem bs5_4_544 : Interval s5Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 551 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96)) (concat (concat bs5_4_128 bs5_4_160) (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)))) (concat (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384)) (concat (concat bs5_4_416 bs5_4_448) (concat bs5_4_480 (concat bs5_4_512 bs5_4_544)))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 666 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 (concat bs5_5_512 bs5_5_544)) (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)))))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
  · exact alls5_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 72 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_3040 : Interval gbAtlas 5 3040 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3049 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)))))) (concat (concat (concat (concat (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))) (concat (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792)) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)))) (concat (concat (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)) (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080))) (concat (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176)) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272))))) (concat (concat (concat (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464))) (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)))) (concat (concat (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848))) (concat (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944)) (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040)))))))
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
theorem bgb_6_7328 : Interval gbAtlas 6 7328 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7348 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792)))))) (concat (concat (concat (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 bgb_6_2016))) (concat (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 bgb_6_2240)))) (concat (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464))) (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 bgb_6_2720))))) (concat (concat (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944))) (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168)))) (concat (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392))) (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)) (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648))))))) (concat (concat (concat (concat (concat (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872))) (concat (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 bgb_6_4096)))) (concat (concat (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)) (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 bgb_6_4320))) (concat (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)) (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 bgb_6_4544))))) (concat (concat (concat (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)) (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 bgb_6_4768))) (concat (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)) (concat (concat bgb_6_4896 bgb_6_4928) (concat bgb_6_4960 bgb_6_4992)))) (concat (concat (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088)) (concat (concat bgb_6_5120 bgb_6_5152) (concat bgb_6_5184 bgb_6_5216))) (concat (concat (concat bgb_6_5248 bgb_6_5280) (concat bgb_6_5312 bgb_6_5344)) (concat (concat bgb_6_5376 bgb_6_5408) (concat bgb_6_5440 bgb_6_5472)))))) (concat (concat (concat (concat (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568)) (concat (concat bgb_6_5600 bgb_6_5632) (concat bgb_6_5664 bgb_6_5696))) (concat (concat bgb_6_5728 (concat bgb_6_5760 bgb_6_5792)) (concat (concat bgb_6_5824 bgb_6_5856) (concat bgb_6_5888 bgb_6_5920)))) (concat (concat (concat bgb_6_5952 (concat bgb_6_5984 bgb_6_6016)) (concat (concat bgb_6_6048 bgb_6_6080) (concat bgb_6_6112 bgb_6_6144))) (concat (concat (concat bgb_6_6176 bgb_6_6208) (concat bgb_6_6240 bgb_6_6272)) (concat (concat bgb_6_6304 bgb_6_6336) (concat bgb_6_6368 bgb_6_6400))))) (concat (concat (concat (concat bgb_6_6432 (concat bgb_6_6464 bgb_6_6496)) (concat (concat bgb_6_6528 bgb_6_6560) (concat bgb_6_6592 bgb_6_6624))) (concat (concat bgb_6_6656 (concat bgb_6_6688 bgb_6_6720)) (concat (concat bgb_6_6752 bgb_6_6784) (concat bgb_6_6816 bgb_6_6848)))) (concat (concat (concat bgb_6_6880 (concat bgb_6_6912 bgb_6_6944)) (concat (concat bgb_6_6976 bgb_6_7008) (concat bgb_6_7040 bgb_6_7072))) (concat (concat (concat bgb_6_7104 bgb_6_7136) (concat bgb_6_7168 bgb_6_7200)) (concat (concat bgb_6_7232 bgb_6_7264) (concat bgb_6_7296 bgb_6_7328))))))))
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
theorem bgb_7_2624 : Interval gbAtlas 7 2624 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2625 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)))))) (concat (concat (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600)))) (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 (concat bgb_7_1728 bgb_7_1760))) (concat (concat bgb_7_1792 (concat bgb_7_1824 bgb_7_1856)) (concat bgb_7_1888 (concat bgb_7_1920 bgb_7_1952))))) (concat (concat (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112))) (concat (concat bgb_7_2144 bgb_7_2176) (concat bgb_7_2208 (concat bgb_7_2240 bgb_7_2272)))) (concat (concat (concat bgb_7_2304 bgb_7_2336) (concat bgb_7_2368 (concat bgb_7_2400 bgb_7_2432))) (concat (concat bgb_7_2464 (concat bgb_7_2496 bgb_7_2528)) (concat bgb_7_2560 (concat bgb_7_2592 bgb_7_2624)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeeeefaa8eaa0feeeeeeefaa8eaa0feeeeeeefaa8eaa0feeeeeeefaa8eaa0feeeeeeefaa8eaa0feeeeeeefaa8eaa0feeeeeeefaa8eaa0feeeeeeefaa8eaa0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071598 * 2 ^ 32 + 4205374112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37277.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,4]⟩,⟨.or,[2,6]⟩,⟨.or,[0,1]⟩,⟨.or,[3,7]⟩,⟨.or,[1,4]⟩,⟨.and,[5,8]⟩,⟨.and,[0,9]⟩,⟨.and,[3,10]⟩,⟨.and,[2,13]⟩,⟨.or,[11,12]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071598 * 2 ^ 32 + 4205374112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071598 * 2 ^ 32 + 4205374112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37277

open PEqualNP.Outside.L_meta_37277 in
theorem PEqualNP.Outside.L_meta_37277 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071598 * 2 ^ 32 + 4205374112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071598 * 2 ^ 32 + 4205374112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
