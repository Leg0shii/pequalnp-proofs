import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36396.Model
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


end PEqualNP.Outside.L_meta_36396.Model

namespace PEqualNP.Outside.L_meta_36396
open PEqualNP.Outside.L_meta_36396.Model
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

def SBf (j : Nat) : Nat := [7, 6, 6, 8, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36396

namespace PEqualNP.Outside.L_meta_36396
open PEqualNP.Outside.L_meta_36396.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x16ab081868f300462c005ce1f200c02300215146200915140002f2cc088000010070064002006d2805015724009cf21122c01d0068000524d3221c00586000c04704060000f1e00300ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4d28750c0c0001e001e920000000080000001c66530004800004b80000930002c0000110d800004c80000003b280000000000005e2500000000000000201d0440000240004e5646800fa1b390ac420000000182800000000000138d60030134000000000005700269300000000ba004b020e200178001a4700000b00000000aa000000000001e9bd00003f0012a0000000003b51a89385f0021c02040b164e80000000000000150f8001f0000000000000000000000a9b440006e243420400001e104001d0000118004100000000000084a400000007b2e0008c0045000cc890005400790a0c800521c96c000000000004b00000d8000000000000000000000000000730000034a1308986a0028000009100000006e32800c60000000005a0000000310000116000000124003c040000000144006700000700035000120000000002a00000000a278000000000fcfe290000000001600000000000000000019068840011400000010c061f00274006d010000c00000011e83000004a86000000019000000000118710a2e3b8001e2d0000000002600000000000200000000200018000200000000400000000200000000205008000200000000003000000000000240000010000001008040200008000002004f94e439ea94873e5190e7aa121db94843b6a90873e5310f3ca621eb948439ea9087ad5210e5aa421cf944439ea80873e53d0a7ca3a14f543429eaa4855e5390abaa7214f14d42d7a92853c5150a7ea0a14f95042af298855d5310a7ea9994f15332cf21e659c43ccb3ea9996715332cfa16659d42cca7ca9194f55232aea9c65ad428ca7ea8994f15132cf21a659c434cb5a849967d5132ce2a265cf524cb3e84997390932cea1265cd424cb1a84994f950329eaa0655e530cabca720d754e419f29c839e539063ca720e754e419ea94839f329073a6520cf946419ea84833e531067aa420e7cc841ce990833e511076ca220cf540419f2a6633d54cc7388798db94b31b6a96633e548c67aa918cfd51319e2a2639c434c67ea818cf150319f2a6433d54c86bca790d754f219faa4433c548879a6510cfd51219e2a2433e540867aa810d794c21aea9843cd32086f4a010de540219f29e813d52d033e65a0674cb409f28e813d54902bea6a05714d40cfa9a813c5350338a6a04714d409fa92819f325033a64a04f14540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f20e6996413e548827aa9104f951209eaa241cd324827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | 1 => 0x18800690000092004f238880e0000000700b800009f00
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x3800000292802a655b500a458d30e5b330a98411045d18c002401d08bddb8060001f001800036dc82c38c401254b80000051013000110042000272c01d003c01a01601d400003c01a48b4032000008081144838104240010020005000c100c394d5210f0e63548438798e51d0a1c63543428d98754cca8d62d5332a598754cca8d62153328b195424ca8d6490932a3995424ca8c6550932a3185424ca8f60509329358a539062d6294e41a358a539070e6294e418758a539070d6294e418358a539061f65cca4187d95329070d524c8418718d501068d6210f31c310d52cc68d6210d318798f540c62d62150318e580540c61e63d5221c3d51328861e63d5121c355132087493254021c354932d021e639474093588535022d6214d40a3588535030e6214d4087588535030d6214d4083588535021c65cc94087195325022d6215330a3588438c21d6510c30a3588430c30c4354830c510d510c30d544cb208718d548821c63551208d185544830d544c9208798f54c421c6355210
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x120080c428000180e242c0a82b8cc6a9087219c6655093281ae431aa020c0d7298f5448606b94c728e81415c84354430818ecaa26490504715513248206b94c7aa621035c86355210
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
  | 4 => packedAt s0K4 (4950+((h/55+packedAt s0K4 (4455+(h % 55)*9) 9) % 381)*9) 9
  | 3 => packedAt s0K3 (2420+((h/20+packedAt s0K3 (2280+(h % 20)*7) 7) % 88)*7) 7
  | 2 => packedAt s0K2 (502+((h/3+packedAt s0K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 2 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 3 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 4 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x14000408402040004402404802504088045045
  | 2 => 0x212108848148040a0a20841220849414312512
  | 3 => 0x421251102a9220d4a1112a8554092941828a28
  | 4 => 0xb556225281aa96733542207992c0c45d80f80
  | 5 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36396
namespace PEqualNP.Outside.L_meta_36396
open PEqualNP.Outside.L_meta_36396.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x8ee21ec21
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (34+((h/1+packedAt s1K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffe07ffff083fc3fc3fffe1fffe0113f3fc
  | 2 => 0xf07c3ff83e1fffc3fc3fc381fe1c0ffeeccccf
  | 3 => 0xff803fffc01ffffc003ffc01ffe00fff0f0f0f
  | 4 => 0x3fffffe00fffffc00001fffff003f00ff0
  | 5 => 0xffffc00000000ffffffffffe00000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x6108023084001004404c048c6024621801515c
  | 2 => 0xa5104451902a0141c4144114a208a4a864c4c5
  | 3 => 0x422aa8a20d548a9c222aa829554149530b0b0a
  | 4 => 0x8a5331052906aceaaa82204199938063b00ea0
  | 5 => 0xc6221c63198cf333333327011020183dea000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000fafafaaafaaaf000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36396
namespace PEqualNP.Outside.L_meta_36396
open PEqualNP.Outside.L_meta_36396.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x49c805000b414061046310dbf43bd43ee32ed32bf41bd41ee21ec21be40bc40ef20ed20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xd841009400058d434ca3aa7a0d354c21b4a80431d531026aa2205354f20
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
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
  | 3 => packedAt s2K3 (197+((h/2+packedAt s2K3 (189+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf87fffc1fe1fe1e1f87f0fffc3f87f0749f673
  | 1 => 0xff8787fe3fe1fffe1f87f0e0fc3f87ffb6499f
  | 3 => 0xfff807ffc001fe3fe007ff00ffc007f8c78e1c
  | 4 => 0x7fffffe003ffff80000fffff800f80fe0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x9010044042002002009012240481112009231
  | 1 => 0x10200888100280040882104404120244124086
  | 3 => 0xa31355148d55506ae445aa0aea8134b2c58e18
  | 4 => 0x86546621291054b355508810b3256020e80d40
  | 5 => 0xc4664439b199993d9e66cc9c220640c4ff6000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36396
namespace PEqualNP.Outside.L_meta_36396
open PEqualNP.Outside.L_meta_36396.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x15a51a440001000aa800302190c800260024503242cd210000f23524c7813000000007c38000500222c9cb9b00715003a0870048008050000004040300b103100043ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x613e540c2faa8186f550309eaa0617c540c2fca6185f94830f7290616e520c2faa4187b54830b6a90617e510c3eca2185d94430bea8861f5510c2eaa2186fd0430dea08617e500c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c83de85907b90b20f6a1641ec42c83de65907b8cb20f699641ec32c82fca3905f54720dfa0e41bd41c83de43907b88720f690e41ec21c83dea9907b95320f6aa641ec54c83dea7907b94f20f6a9e41ec53c83de87907b90f20f6a1e41ec43c83dea3907b94720f6a8e41ec51c83de83906bd0720f720e41ed41c835a83907b10720f798e41ee31c83da63907b0c720f7a0641ee40c83da81907b10320f798641ee30c83da61907b0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94416d52882fca3105f54620dfa0c41bd41882fca1107bc8220fd904417f544837ea8904fd5120bf2a2417d54482f8a8906f151209e2a2417f53482fca6905f54d20be29a41ef42483dc84907b50920f621241ef32483dc64907b4c920f6192417f51482f8a2906fd0520dea0a41ef21483dc42907b48520f610a41fb20483dc40907bd5120d7aa241ee54483daa8907b15120d62a241ef53483dca6907b54d20f629a41ef43483dc86907b50d20f621a41ef51483dca2907b54520f628a41ef414835e82907b90520f6a0a41ad41483d882907bcc520f718a41ed31483d862907bd4120f5a8241ef40483dc80907b50120f620241ef30483dc60907b4c120f6182417f54082fca8105f55020be2a0417f53082fca6105f54c20be298417e52082dca4105f94420bea8841bf410837a82105f94020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21f641c437a83887d50710daa0e21f631c43ea63887bc8310f6906217f54842fca9085f55210be2a4217f53842fca7085f54e10be29c217f52842fca5087b94a10b7294217d52843daa5085b54a10be294217d518437e83086f50610bf28421fa30843f261087bc8210fd10421ed20843f241087a48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c524437e82887d90510dea0a21f5414436a82887d8c510fa98a21fa30443f260887bc8110fd10221ed20443f240887a48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2086fd0410dea08217e50043de40087b48010fb88021fa10043ea20087e44010
  | 1 => 0xe541067ca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31ef99663dd32cc77e8398ef50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31bea94637e518c77e8318ef50631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa9263ef524c6dea498df14931f6292636c524c7be6498f74c931dfa0a63bd414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831f7290636e520c6faa418fb54831b6a90637e510c77e8218ef50431ef98863f6310c7ba6218fd4c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87dc6590fb4cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53886faa710df14e21bea9443ef42887d88510fbcca21f6194437e518877e8310ef50621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f719243ed324877e8290ef50521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043ef42087d88410fbcc821f6190437e510877e8210ef50421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40dfa1e81bd43d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c52502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2206fd0440dea08817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3bc87987750f30bf296617d52cc2fca3985f54730dfa0e61bd41cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c617e528c3dca5185b94a30bea9461ed528c2daa5185f94630bea8c61bf418c37a83185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c2fea2985f14530dfa0a61bd414c3be6298774c530fd98261de304c2fea8185f95030df2a
  | 2 => 0x380100a034050060160040100100000c0480100000c018000020000600002c04400000000000050010080080a8030020180800002802c0b00d00c02404003004048038060020040200000206001006000004000000080000100100000403809004018000030000280001500800000016000000010020040480000301c01000803000010000000000000180200003403000020000000020020080000000a004018050100180380100a0000000801e024020000020000980000000002005006000010030000800080000c0000180e000000028010020080000000a06c050010020000500400e008018000060080080100a0000000000200c030000120300180100001c0080c02c010018090040200200201c000070000000000200600001800002000038008090020180100300200c0200cbf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521fb94a43b7294877d5290fdaa521db54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885bf4310b7a86215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbde85197b10a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde84997b10932f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef94341dea8683bc50d06faa920cf55241bf29c837d53906fca520df54a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0efd0d41df21a83bd435077886a0dfd4941f7a92836f52506f8a4a0fb14941b629283bf425077c84a0ef50941de21283f7415077c82a0dfd4141be28283bf535077ca6a0ef54d41de29a83bf525075ea4a0ef94941dea9283bc5250758a4a0efcc941df19283bd325077864a0efd4541dba8a83bf505077ca0a0ef54141de282837
  | 3 => 0x9fc62800000086442840920c91549000024a000000000003b40005685d0002a4000005bc64c002e91f6a68ee80021044c4299957a3043ea0d0002d8962751fc114002b83cc478000005b80014680f63c000002fd000000000000007d00024336814c4b8ed1889780013a0ca00142000260001288000780d4ad1cb1100942d099000000000002b85cc002622a2020001c8540000000000000009900000030800000000001819350009557c1795ee7e0b314b2b00000019e354600000ca02e000520003e03981da1253a4194d8000586b93c000278b48d787500002c001a01b8818000000007e4a40001a80000023e1569244804e1fa9047c0601a6824881ed202400a5000374454791bf346608d332c1b04b5918a1084c256d9464dc135958f12d63841a02f3ea1acee0c555285cf610c5d874d3e00000006915858000cc9558333220f80000027e29cb29d448800012155042914d100044ca4d7aae05f29a0002a7022801290db000274002b0000000d985417e88847000000000000824ec0002d8004046ac00000000000002294ee000001763380008b000000000002f2000000002c5000c4400000510001088000000010a86e5ae6ed5b15e0000fc000000009998500008e000ca2e32727bd3ea854460004f28a0983485c8050547d8528af6385f0e800032c00557800000000db98c19c7dc4186a3fa628003134500dc000744daab40009a0dac04001715505c8000005e8b040000000056d7f8ae4e4000191de51e00173800000000000000000001ead9000000000a632aca89116900000000000466000b08935f695d5297d070000288de2341049b17a578c640016d4b2cc47d0e701444928219000510a107116e2b0ff2dd29e001261e710e62d741a70181415918465a67d1ba131e6b1d6413e2686617824d21a1e4821884348949898d1625a0000ef4f6a891603a1640000000053e81578a923c6c3527b0213e5fc462560008c4b6031150c54380bd2048d0000000007c4c2800000000000005c400000283138550ea9d11a2a50c7884000bcd5f000000000000e40001791388f5328e8243085f4b902a8690000011e000334000518e22d4001890002f013c0000000080d0600043c000000000003ad2c0403ac97d5203000000000177586bd8011cf000000000000000000000046a000a681b61e000091a461c184000001ea2000029762eb10773261be04c948fc0c8000941ad23e45185abf362b313a000436010d91674fe000002b337c5d11528b2f61bd688cf45c6d9508e80009ad929a13e4000002071d299c8c8005941a06d2900720b4231cc63a6e1881c700c00200000805004008000030000040180202e00c0000500c0000200100000401000000018088000060040280800005c038110000180080300a0180580d006020008000040040
  | 4 => 0xaece680041442c00000286c14000000000000a800254000000000000000000000099000000000b7cf0800000860000004e200130acf1ac0004088926e000a928e03cb3400094000000e0afc00000158aae3845d42b8e0000000141a900612800280266501300003244f4000000002800000000000000000020000001d900035c7fa3847aa8cf5a6524c2d4ec0e50f42f95cb182121c8f50006400ac8da462beb09920594483541387c3c455cf9873166558819c30006757f0000ac638fd1e40000015b90a5020014f000558c00000002c4880aeb21000000003295b45c0489860003400006c000000248003029e529800000000002c020e001648005a6234000983200012a2e541e4800c9ac6500010b00000054014a3000000000000000b180000003a001020cc18e4943c00056a8c8631410009f80000043a49cd2b33000000000631440000e25b01c0008c08a3be000000003dc0000a28645e7801b00028e75d0080036a198001bc0008207526a00000148b2f360738ac82e5b0850002ce0009bc761c52c8254a994525c374e209663ec30dca5d65c01d05a985da00170960178000e484b0008d800062000728de80029c48568000350000002ba000000102eb00000000000000000000000eec9d1d8c000045c00295000a1c0f816636000000f00000009d90519a0000000000000000000000000ed800000718000c8116000130003361f89187b0000018b0f621c52411a1f5128fc7a1d21b28e5270f916092088aef660a582f91c13665c3b1380a42483f8ba3d0111168005aa018958220004bc8e94c5a80014101864458d8d00016832d3d1ff4d2839258c35ac000f2a6c0009cc000bb000bb8fda47568908f49835185f965a7060e19cc496e4b861d553065385bc0004354c87071ae60b8024003044b400000000170000000f7000001751c001a000000004c600087
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xb530823e6414c208f590530826e6214c209d98453082756114c208f992510823d6494420cb94b410832e5250420cd945410833551504209bd95200827b6548020da949200833661953109bd8954c426c6255310cbd8954c432c62553108f99353c423d64d4f109bd8953c426c6254f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b108f99052c423d6414b109798c52c425d6314b10cd95141c42b76550710cdd9541c43a76250710e918941c42b5648c710cb95320c432d54c8310e950720c432e5448310cb55120c43a541483109b98b548426d62d52109798c548425d63152109b988548426d62152109b98b538426d62d4e108fd91538423c6454e108f990538423d6414e109b988538426d6214e10da982528423f6454a108f191528432f6454a10cb191528432e52d0610cb54b418432e5250610cb54941842e9628c210da94920842eb6548210dad9520843ab6448210ea19120843ab4148210ea505208425f63551109718d544426f62551109b189544423f6454d108f191534426f6254d109b189534423e6414d108f590534426e6214d109b588534423f64549108f191524425f63549109718d52442b564905109d19541443376550510cd19541443a76250510e918941443b36050510ec18141442b5648c5109d19531442e9628c110ec5063044278654c110ec50530443d1314c110e950720442e96288110ec50620443a541481109e19520443b14148110dad9520443686548110ead9120443a86448110f8d8520443e06148110ead0520443e24148110ea50520443e14148110e850520443e23148110f84c520443b141c4110f8482104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c109d984530427a6014c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520426f60548109b581520423e64148108f590520425e63148109758c520426e62148109e980520423e64944108f592510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410433651504109b98a500426d62940109b597200432e54c8010cb553200434e53c8010d354f200426f6548010cb951200432d5448010d394d200434d5348010da941200433554c4010d554f10042796584010d654e100436952840109dd9510043355444010d554d100427b6544010d654d10043695244010
  | 1 => 0xc31d544c030d5545300c27b654c030dc545300c25e63d53209758f54c823e64d4f208f59353c823e6494f208f59253c82ae64ccb20ab59332c834d530cb208f99251c823d6494720ab99221c82ad6488720ab99021c82ad6408720b398c21c82cd6308720b398f54c82cd63d5320ba58354c82e96015320ab99353c82ad64d4f20ba58353c82ae6494f20ab59253c834d5314f20ba58053c826e6590f209b59643c82e960d4720ab99251c82ad6494720ab99051c82ad6414720b398c51c82cd6314720ba58051c826f65507209b19541c832f6550720cb19541c83a76150720ab99231c82ad648c7209bd9531c826c654c7209b99431c826d650c720ab99031c82ad640c720ba98031c82e9600c720b398c40c82cd6310320b998440c82e56110320abd9130c82ac644c320ab99030c82ad640c320b998430c82e5610c3209798c548825d63152209d984548827561152208f990538823d6414e209d98453882756114e208f992518823d6494620cd94541883355150620cb58b544823d61d51208f992544823e6515120cb588544823d61151208f992534823d6494d208fd91534823c6454d209dd8553482746154d209b997424832c54909209b195424832f54109209b99732482ae64cc920ab593324832c548c9209b195324832c544c920d314d324823e64145208f590514825e63145209758c514823e65d05208f197414823e65505208f19541482ae6488520ab592214832c5488520ba98221482ae6408520ab590214832c5408520b398c21482cd6308520ba98021482ad61d5120ab99254482e96095120bad8154482ae6515120cb99454482ad6115120cb15353482ae6494d20ab59253482e96094d20abd9153482ac6454d20cb15153482e76154d20b918553482eb6054d20d354c534826e6590d209b59643482eb6050d20ba18143482ea6010d20ba58043482ae6494520ab592514832c5494520ba58251482af6454520ab19151482cf6354520b318d51482eb6054520ab99051482ad6414520cb15051482ce6314520b358c51482ae65d0520ab19741482ad6490520ba98241482e960905209bd95414826c6550520cbd9541482ae6550520ab195414832c65505208b19541483a76150520ab99041482ea6010520ba58041482ae648c520ab59231482ea608c520ba582314826f654c5209b195314826e650c5209b59431482ae640c520ab59031482ea600c520ba580314832f54d4120cb15350483ab54d4120ea15350482e961d4120ead0750483a941d41209b996404826e6510120b398c40482cd6310120b998440482e56110120ea500404826e658c120abd9130482ac644c1209b99430482ae640c120ab59030482e6610c120b958430483c9300c1209b98b540825e63150209758c540826e62150209d984540827561150209b98
  | 2 => 0x60d50219e583540863d6595021cb189540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530874c6254c218f990530863d6414c219798c530866e6214c219e98053086796014c21cb553420874d53d08219b594420874d5310821b9584420866d65cc821ab993320874d53cc8219b594320874d530c8218f992510863d64944218f597410871e53d0421c754f410863f6550421c794d410871d5350421d354f210866f6548421d354d21087a541484219dd95210873a5494021ce552500875a5394021d654e500873b4194021ce506500873a5454021ce551500875a5354021d654d500876a6254021dad0950087684254021dacc950087683254021ced0550087394154021dac85500876921540219b98a53d026d6294f409bd8951d026c6254740cd54741d02ae6290e40cb548429032e52d0640cb54b41902ac6250640cb949419032d5250640cd945419033551506408f997435033751505408f596431031d5390c40ab98a431031d5310c40d394e521034d5394840d394d521034d5354840c754e421032d5290840c754c42102b96010840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cd99151103364354440cd10d51103364254440cd109511031e53d0440c754f411032e52d0440cb54b411033551d0440c794d411031d5350440ab189411032e5250440cb54941103365150440c754f401033551d00408fd95401031d5350040cd545401027b65500409b98b54cc26d62d53308f99251cc23d64947309bd8951cc26c62547309b98b548c26d62d52309b988548c26d62152309d984548c27561152308fd91528c23c6454a30cbd91528c32c6454a308f992518c23d6494630cb94b418c32d52d0630cb949418c32d5250630cd945418c33551506309b98b544c26d62d5130cb98b544c32d62d51308f587544c23e64951308f994544c31d63151308f584544c31c5490d3097195434c2d86050d308f990514c23d64145309b988514c26d62145308f997414c23c65d05308f995414c23c65505309b98b540c26d62d50309d987540c27561d50308f596540c23d61950308fd85540c23e64150309798c540c26e62150309b588540c27661150309d584540c32e5494830cb552520c32e5454830cb551520c23e64944308f592510c3365494430cd552510c3665294430d954a510c3366494430cd592510c3365454430cd551510c3665254430d9549510c3366454430cd591510c23f65d04308f597410c32e52d0430cb54b410c33651d0430cd547410c23f65504308f595410c32e5250430cb549410c3365150430cd545410c31d54cc030d5547300c371518c03097d95300
  | 3 => 0x1329b997424cace63d0932ab993324ca3e64145328f590514ca7a60145329e580514ca6e62d50329d984540ca7561150329e980540ca7960150328f992530ca3d6494c3297d95320ca6f654c8328f992510ca3d64944328fd91500ca3c64540329b98a53d066d6294f41ab98a43d06ad6290f41c754c43d066e62943419b58a50d06ae62d4f41ab58b53d06b561d4f41ab98a53d06ad6294f41c754c53d06b56114f41a798f52d069d63d4b41ad58752d06b56114b418f99732d063d65ccb41ab98a50d06ad6294341a798c50d069d6314341ab98850d06ad62143419b98a509066d6294241ab98a43506ad6290d41c714d435066d60d4941cbd0c525072d43149419b580525072c52d0941cbd48425065e63141419758c505066e62141419b58850506ae6294d41ab58a53506b56194d41abd8953506ac6254d41add8553506bb6054d41ae181535071d5314d41ab58352506ae6294941ad58652506b76154941ab994525072e6514941cbd4c525072d5314941ab580525063e65cc9418f59732506b7614c941ad18532506b6610c941ad584325072f52d4541cb14b51507a752d4541e914b51506b560d4541ab98a50506ad6294141cb14a505069f6354141a718d50506af6254141ab189505069e6314141a758c50506ae6214141ab588505072c52141418fd9541106776550441cd951411066e62940419b58a501066e62d53319b58b54cc66e62943319b58a50cc63f64543318f19150cc66f62552319b189548c72f6255231cb189548c66e62942319b58a508c66e62951319b58a544c66f62551319b189544c67b60551319e181544c63e64d49318f593524c72e64d4931cb593524c66d60d49319b580524c74c52cc931b5185324c72f52d0531cb14b414c72f5250531cb149414c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f990540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c66d6094831cb951520c72d54548319bd81520c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc43197d95310c74d524c431e5505310c677654c4319b98a500c66d6294031ce952500c7395494031da94a500c7695294031da98a500c7696294031ced06500c7394194031ce951500c7395454031da949500c7695254031da989500c7696254031ced05500c7394154031d6cc5500c7723154031d64c5500c77131540318f99253c863d6494f218fd9150c863c6454321cbd89548863e64d4e218f593538863e6414e218f590538867a6014e219e580538872d5410a21ab993328865e63951219758e544866f62551218f992534863d6494d219bd89534866e658c9219b195324865e63d50219758f540867a
  | 4 => 0x91ae90003e0790273bc4cc6fb4a2e4720cd9fd364868a49c43b4000fe3250d8b850b97a54a1002c00017cd158c2c955cbd42d9ae2166a14286b3b2001ae8000002046c0940b236c113220601280017e6aa385941e62083305d1f428cd78f419d446a6d101681d287cee87f0bed859a8b05ec475898e636a449609e452a230698185dec04a60000144841415867008480a7d5f026d532f06042a8e112d000001969824e4830000005320013db100004f4001740a2338002280ce000000a44e6001340000000000034339e0016a8000c8d888191b34200000049000be402b030260016c839494000739ef000d080499e5869c4869ee00000041987000db400079004554000e86720012d36b42aac4f81f15d072d160721f64e50883452647c9023f03c000000000000100887a63a000000f4678c6c8b3585162899f8cb096001548004024f8341281a45e168a43638ccd15270504c5400314000b4000091278000de23a330001279c91aad90000000ba7885d88b53cdec4ca7f4d6000d1800000504df8005002294d11e5563c4aca062a6071128030a0900d825f49ac9c83abf0000007f9e72c04b8531c02b4a29488824ee10d7dafe1d4cc51e376002834cc9d467a6315e10e306570038c916e7809800501403a114000140000000000500204000000018068000000360d00300101800c0200100800c0200101400405008008008000000000100280101a04000002036010020000060280180700000c008110021c4080040100180181900e00c0600109a004018010000000501e0000180700000c00c0400000c01c0280a00c01c000010001380480b0ba000038010000180081000400c088060180000180802e03803000038000020050220100580b0000080780102600001800008020130180020000c80803e080038010100380200002000c0080101c02c0000100400c038010240040482c006000000080060000300000200800009002000058570000000000200200807801000000010070040080c02500c000000060000000480c00000c00826002064040000000b800001000010098120120080f8000100080581f04000c0180601000800003004008008170120180080300805c0000001202416801004044018000000080001a0060280080306a0080401107c0c803002002004000070000180480a000008000010040141801200c00c0f806000010040089b98a50d0e6d6294343cbd0e5290e6d6094a439bd815290e6e62942439b58a5090eae6290d439b9885050e6d62141439d9845050e7561141438fd954310e5f6550c439bd895110e6c62544439b98a5010e6d6294043c794d4390a3f65508429bd954210a3d61953328fd8554cca3e64947328f59251cca7a60d52329e583548caae64cca328f992518ca3d64946329d986544ca756195
  | 5 => 0x17e0524f463c9490524868876b3b1fa988642be0c60000000003e5ac071883746d8471fe00000184a8c4060949fb0d38657951800000bb18d0a0000000f92b45e24d80031102cc5c9b8450320010c29664ca51370e3506b80572590e66ac7c94359835d3b07c05e030991d34c8001be10f1241a4382f25ba4701c1a95fa0d86f06055e3f9a984c3fe0007b9186827140017531a8845e1e96ee810001b96c6c389285a000001a81062f8a490736900000000000000bac0b82d000c780007d0009715c2f30c2364a696229e4086017d35494c79a4211e9556736554e464a59713f23b15c88643c8cc4c26c39c000a81e153867d6226d45aa386286f47c1791cb46058a845c000554d5800312308048c91ea0f096cda12c150bfc0d0000001200015b24cd503db6013c001afa97000b19a434e1e06f5172a2000cb8002650668484e1a422e00000080000585ba000000000aa20f1520002e16f00058d6500051e000001342d480893a13642625982470ae000002b302008c00000584d6400000062000001d550c8c80e80018e544000004c22ad9a00035e001722b01ac188231b31423ac468000001b4482a46985083f32f0008580024e4c0001829906e45911325849891171aa8000000bf9086320016e00000055dba8006885748d0004c6670cb0005b00003500007cb1c619130e84ac05b5c590cb09a9095f41090801534c000000b1680af50513a4a0d693a00050e920001eb32e66842800280000000000008152f00d38e0219188859ada134ae66f2394e902b60eb4d5018e468001330d1370a05a880000ccc8979cc3ac81cc527830c538bbb6600086c5c800432001858006a45b4711f348cde0ca00000000167a416485102a82e4f8b88002673260011da362e0bdd4ea8d2ec304779dc3f0440b30001880d5a5aad000b692e94809c000000002f6ca9002222189483b875322704b4ab214eb6d22b49078b9c001fb22a21c0003f13492d37b370407e8bc8955800006a0005087dc578000a800118814000d9c00229000b58801651f400117a092765b0851e33a0c1987aba000950001cd4f20f5041e543a2d10e0000000001b82a0000017700066c8f51a9db5a44e1481521ecba9b630c1f85cc4b3006d47b55b3162dc8dd6f8a516ca24cab043000c8610b218c959a683a0528515d9311ba2d4a2b4f17e2f5be8891b87d8d002607669d6f27e6e09458433e1b48e0888e03ae2b4a522b3767b07a94761414c3728838c77c771d15e872976a5709a39051b7141625d62ab7640b50c0a2768e55823a6a53e34118114166b5c4204434a890d69224ea4a9b9b7a63e59c679b730a06c4f9b1082ce9b70936de275958240001c4001d80ca00027b5b316d5c0015f19a6f9658ac4927d42b2b51941d9949ac5ca03d560000cca6
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x101f080596110d060700000b02140e0e9b079e0015a0801c8f9c12800680050480150c801d9917090c1680038002800a1b981e8400008000030f01001897a1000b921a8a8d99909a000000000014801311a00008a1939d099f8180050800385040001d000018600480833e0c00a8d2e0312a221c3571191500ca8c382a629a834a1c15314941962e030a64a0e0d631485050694b80a428283345c0614c93185ceda928298f0552505310c788a0a62a80639154d611082194ae33266410e0e6454f3208782a9a8290843585c44254021a54e9992a010f21414855008706a9cc5218812a5c26290c40c32a6b0084205267290d5110298b8084a88818354c6250440952e0312822042c76549418c268b88c0a1a610b5d85408520a4ae22a0429060c5458c21483122a0c2a9a41511c55314d209c2e230286905257115051483062a2c628a410b9d66550520858eab246290689635004048350b0a80202410b9d7644c120d12c898060906c1614c030482163b2a890621291d94148310858eca9283084a8765052084312328c4a0a21685c06250510b22e630282885a1721814144350310c0a0a21a8589418c110948eca0a40884b0765052044314328c890221685c46448110b42e830a40886a06418520442e0b98c290221685d24148110950eca0a40884e0765052044351bb28290221689d94148110b40eca0a40886a07650520442503b28290221685d23148110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x85b520004833280238185038001c03c09635c05214141a058199153cc821921819d33254021c09535c26290c40921809ca4354440c09535c06250440a05811516308520a05811516314520c20655c06250510c817318860505108a087589418c110c20655c46448110c80645cc61481108a2869d941481108a0865d23148110
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
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
  | 6 => packedAt s3K6 (788+((h/14+packedAt s3K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s3K5 (25143+((h/273+packedAt s3K5 (22140+(h % 273)*11) 11) % 1191)*11) 11
  | 4 => packedAt s3K4 (37250+((h/298+packedAt s3K4 (33972+(h % 298)*11) 11) % 1073)*11) 11
  | 3 => packedAt s3K3 (3486+((h/22+packedAt s3K3 (3332+(h % 22)*7) 7) % 90)*8) 8
  | 2 => packedAt s3K2 (925+((h/5+packedAt s3K2 (900+(h % 5)*5) 5) % 19)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x8ff87fff07f8fe3878c7e3ffe3f0fe0e09f673
  | 1 => 0xf07f878ff8ff1fff80f8fc707c7f0ffe36499f
  | 2 => 0x7ff80fff001fc7ff00ff807f800ff1c78e1c
  | 4 => 0xff80000fffffe007ffff00007ffff001f80fe0
  | 5 => 0xfffffff000000007ffffffff80000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x81090101101100400801209120902224009231
  | 1 => 0x4102012204028010048442204240488124086
  | 2 => 0x6b2313245232540ab900a90569026964c58e18
  | 4 => 0x2206544884a00494d2920008524ac041680d40
  | 5 => 0x4c446600e6c4992764e4d24e000c8189bf6000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefeeaeaeeeec8c8fefeeaeaeeeec8c8fefeeaeaeeeec8c8fefeeaeaeeeec8c8fefeeaeaeeeec8c8fefeeaeaeeeec8c8fefeeaeaeeeec8c8fefeeaeaeeeec8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36396
namespace PEqualNP.Outside.L_meta_36396
open PEqualNP.Outside.L_meta_36396.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x920018000285c0003e3000b003c01b4eac01d0434000484140a389400000200112aa4d16001150500981980e811a20084c893c000131c3c0100044040004000003ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x842ce0f901680014990d2c00485d20002800000000e558000000bcc4a0d80165309c004d2400f0003488fc1ca851615d1d3c094000000000003c0c00381800f49400300064005800b00518780000dd080040000090000000d0b80000000020014cb480546cd4000000a40000c110e8000128006800000001054844acc8000114ed44747c008d5001542400700138cc6011343a00020a12001000000208002400020e06000002000202040404000c00017a5090ef2a121de94242bca84853e540ca7aa819734c832bb2886575510caf4a0195e540329f286833d54906f6a0a0de14141dba8a83bb5050678a0a0ee141419c282833e541067ca918cf55231b7a92636c524c67ca818cf55031b7290636d520c6f4a018de540319f2a4433d54886bea690d714d219f2a0433d54086bca610d754c21bd2804379500867aa3204f94240af298815d53102dca4205b54840bb2888175511033ca6206754c40d729081ad521036ca2204f54440daa888135511027ca0206e940409f2a6613d54cc2dca5185b54a30dc204613f544c278a8986e101309f2a6413d54c82bca7105754e20dc204413f5448278a8906e101209f2a6213d54c436a83886e103109faa4213c548427ea8884f15110daa0a213e540427aa8085794c10aea98216e52042daa4086e10010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1e000000a800002a400e00000050002202809a30012000002658019cb12c0002e40000001820004004000013453254432c698c50507196314141ca988505072962141418e181548c6386055221c354d52103165354440c554d51103265254440c954951103306054440ca548408c2b16110230ac584404c3195310220ac58440882b16110120ac18141c42b161103108d19541442396510010c654c40043295210010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x642000818258d6214141a22e6302a220521721815110310a92c2204618454d6110220
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s4K5 (788+((h/14+packedAt s4K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s4K4 (2697+((h/30+packedAt s4K4 (2457+(h % 30)*8) 8) % 146)*8) 8
  | 3 => packedAt s4K3 (998+((h/8+packedAt s4K3 (950+(h % 8)*6) 6) % 57)*6) 6
  | 2 => packedAt s4K2 (248+((h/1+packedAt s4K2 (245+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fe3fffc0e3c78e3c71f8fffc7070e1e19fc93
  | 1 => 0xe1fc3e3ff03ffffc07e3f1c0f807fffe6640ff
  | 2 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 3 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x44288c0460489100c1048246c131224c089c91
  | 1 => 0x8410048809020040221108808024490224026
  | 2 => 0x94881491240940294802a41252500944858518
  | 3 => 0x4012a9224820125295480024a4a4a009580ac0
  | 5 => 0x991330038d32649f2693493800c0c191f76000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafcc8fcc8feeafeeafcc8fcc8feeafeeafcc8fcc8feeafeeafcc8fcc8feeafeeafcc8fcc8feeafeeafcc8fcc8feeafeeafcc8fcc8feeafeeafcc8fcc8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36396
namespace PEqualNP.Outside.L_meta_36396
open PEqualNP.Outside.L_meta_36396.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe81bf41d037a83a05f55240bf29c817d539037e87206f50e40bf294817d529037e85206f50a40bf28c817d519037c83206f10640bf28481bf40903f681205fd4d40be29a817f52502f8a4a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40dfa1881bd43102fca4207b94840b7290817d52103daa4205b54840dfa1081bd42102fca2207d94440bb288817d51103eaa2205d54440df20881bc41102fca0206fd0040fd20081bd40103f280206e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330ef21e61dd43cc2fca5985f54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30f7294616e528c2faa5187b54a30b6a94617e518c2faa3185f94230fda0461f8408c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930ef19261dc324c2fea2985f14530ef98a61dd314c3f680987e10130fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea94417e51882faa3105f94220fda0441f840883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc84907b50920f799241ec32482fea2905f14520f790a41ed21483f680907e10120fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f481087e50210fd18421f930843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fd20221f940443f460887e4c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xe4250afea2a15f14542bfa82857c5050afca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbdc85997b50b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65de438cbba87195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865de430cbba86195f94832f721065ed420cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83bf43d077a87a0df94b41bea9683bf42d077a85a0df94341bea86837d54906fca720df54e41bf294837d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077a86a0dfd4941be29283bf425077a84a0fdd0541df20a837f50507f6a0a0ded4141be28283f850506f0a0a0df95041bf29883de53106bca620df54c41eea98835d53106fca420fb94841b7290837d52107daa420db54841bf28883bf41107ec8220ef50441faa08837e50107f4a020de94041bea8083f950106f2a020dfd5331bf2a6637d54cc6f8a998f790f31eea1e637e52cc6faa598f7ccb31ee996637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31bf294637d528c7bc6518f70ca31bf28c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263de434c7ba8698dfd4931f7a92636f524c6f8a498fb14931b629263df324c7ba6498fdcc531ef18a637f504c6f8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31bf29063ee520c6dca418df54831f6a90636d520c7bc6418f70c831bf28863df310c7ec6218f74c431fa988637e500c7f4a018de94031bea8063f9500c6f2a018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fb90b21f6a1643ee32c87da6590df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52887de6510fb0ca21bf28c43f631887ea6310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21efa9a435f53486fca690df54d21be29a43dc53486b8a690fb90921f6a1243ee32487da6490fd8c521fa98a43f721487dc4290dfd4121be282437f54086fca810ef950219f2a0437d540877aa810cf55021be2a0437f53086fca610f794c21af298437d53087baa610d754c21be298437e52087de6410fb0c821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e817e52d02faa5a05f94740bea8
  | 2 => 0x30200000024000000ae0003ac9ac3800500069c528ed0000014b1c6000000002210009a0000f40002600000001e000860002380010225450a8a0000000004ac00000000a8d2b9f74866991580000000096a7a094000001a1000228618f81e66b8eb9e8500818001460ae00000000000178000004460002da8c0000000000000000005881000000001d42ae0000ca9a48e00000000224000001f30f4000b89172d273011a6c0007786700000000000000000000c9000000174ce0000146c46c0291aa0a8000000004a8000530003c9198cb32c114aa1140000389d00000084c0015f068958489394da3b01998631c848a42631ba4405d94a3161f11b00000003400000000854568830000540000000082ce10000008244e0a724e600002400003a40000000000000000000000949081c60012e1781900f0a721d51000152941000000bb2a93c8898000001560009114702e565258003884e0dda2e0000001b1bd0007fc00000000000e1a0f0006303988c0000000021c0006248700000000000000000000001ad00000108121000190dc1f62400010390b2da3ace39a536aa812d00034436c8b0000000fcb395b000424000005389f00002b18c9d404800000000001aa1720013b80000000e004008010020240000200004000002006008010000240080000501001c0080000400c0180f0000040080201a0100080000000003800000028000030000180000700000801003000000040000020000000001e0000780000a00400800004000010010000040100200c02c03805000008010000040380000500400800007000000040060000000000500000c0000a0000040500301801400004000058000010000000080e00200803000000000000050000040c800004000040020060480000a00a0000100000e010000000020040080f0000180000000c00409009000000030020060040000200400c01001008028020020140240480200000008009002004008040180000000501800806804000000018000000000100200a01c01001006004008020080001280000e000008000020080300001000efca5a1fb94b43b7296877d52d0fdaa5a1db54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf28487fa5090ef4a121df54243fca8487795090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a17794f42af29e857d53d0bbaa7a15754f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1217e94242bd284857d5090bf2a1215e54242bfa9a857c5350b7e86a16f50d42f7a1285b
  | 3 => 0xee0004a425d178004e4490000000400ec000001828880000041a324cb98852019c001621287611e8481f41fc7e9ef018000ca2450e80010b2340284c0001e00003ed1e22915e16835a531261f8181e31746744e8a82f652c000e847e1190c0783e86f94186545a7f40014d0007c52f9db2d4560110000001d8e29022e0308191ca0004b800000000000780001245f42480036e000000004921640029454e348828850007ed01a4f000000000004e29bc6e09b0003987b88b0000e8f50004889cd162660506c8bc94921e53000000164130ea8523561605aa37314094e998d320a1c8c9a03fc700000001521bcab0002fe000000000000000000000048c1625d4280002a0000002dc0000004e86c8391a148220001404720010626a00441899800000a489a0cd0006080000000035c001af00038800000000000000004c8000ad224000000001f817e17c000004760013d8c5000000001d1000330fd0be1044dc0008f3da000cd8000d40e530096410590000003504d8000000704ec0b0900065b88d8b8002140311c105c400f2a84000544d20de000018000004f21383609536c1dc0015e2a600009000000000000181422b80002f000000000c7352829088080cc000109bf00011c0000005a2d00000044e000002351f800000000000800000000000000200026a100002310aa0011c0000000007f1eb1f2380928002d626400000498000c7972000000000004ca7348881e47c368c2000374218b013248228d0725148c50c000d13ba2c4bd00032a768aaa202301592aa6e54c5d0000f13f837d2c24800085d49a1f484410080000000010c8003e40000028133c8083aaa8000000d98000000008f89f3d240c00000000a5cbf1d017a8140017c000764f800021a0740013d00000000000000000000000000013ea9d1ce7b8a804f1a8664bb9e11789640000028a044218ef0c65d4c98f536801c94072000584268000d000128000454a84e58004b6310698aa10e4f000000000000531e70000013f8004d29f8000004bc0dc720003460009891d0881ed4a8261940000028a4c40f80023039c53cb40b351e000348003ea0013c13f214000000420da0c4b31ec51c06c708002885094580015800000000544724000002ca000d80601fe00089800000000dc9520004040006e2d88c800225000000000790000014da9f1ac7e4002671400013b09e0000000007d50c0005b282000000728003780000008e000a900001c39e000001ac000000001d230aa78cf80019e0680003d0000000021a24c0008a95d3300000004b000000000801eca34b7835000000288000000014c8a21d479838800108000000891809391d29811a6684d00030e804c88005220000000039000096000000000000003be9852681f27c8788f24a2c604cb98b025e184680003c49c000
  | 4 => 0x5c000000000005123b8c1a74082364
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x32c834d530cb20b958432c832d54c8720cb55121c82cc63487209798f548825d63d52209798c548825d63152209d984548827561152208f992538823d6494e20c7992538831d6494e20d6982538835953d0220ce55040882d96310220d654c40882f16110220d694d308834e53c8220ae993208825e63951209758e544823e6494d208f59253482ea60909209b195424826e65cc920ab590324834d530c920b958432482ea600c9208f990514823d64145209798c514825d6314520b318d214827a65d0120ce55040482d96310120ba98840483a94210120bc58440482ea628c1209e19530483c8324c120ae99320482ce63881209e983540825e63150209758c540826e62150209d984540827561150209b98b530823e6414c208f59053082766114c209d584530827a6014c208f992520823d64948209798e500825d63940209bd95200827b65480209798c54c425d63153109b98854c426d62153109bd8953c426c6254f108f99053c423d6414f109b98853c426d6214f1097d8d52c425c6354b108f99052c423d6414b109798c52c425d6314b10bc18141c43b141d0310ced5040c42f16110310ec90440c425e63152109758c548426e62152109b588548426e62d4e109b58b538423e6494e108f592538425e63d4a109758f528423e6494a108f59252843385450210ba58a30842d963882108f992544427b60551109798c544425d63151109b988544426d62151108f994544431e6315110c758c544432e6215110cb58854443356115110ce580544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524433454905109d195414427a6590110ce15240443b241901109e19540443385450110ec5054044338548c110ba58a3044278654c110ce15130443385488110b658e20442786548110ce151204433854c41109798f540425d63d50109b98b540426d62d50108f596540433860550108f990540425e63150109758c540426e62150109b588540427661150109e980540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530427a6014c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109e980520427965d0010ce553400435953d0010da54b40042796510010ce55040043595310010da54840042f16110010cd55310042796584010ce55210043595384010da54a10042776544010cd551100427b6544010ae19110043395444010d654d10043695244010
  | 1 => 0x86e960909219b195424874c53509219b996324874c538c9219b195324874c534c921d514e31487c6328c5219d19531487c5324c521d314e214865e63d50219758f540867a60d50219e583540863d65950218f990540865e63150219758c540866e62150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530874c6254c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530866d65cc821cb553320874d53cc8219b594320872d540c821d354c32086e5610c821cb553210874d53c8421d554e210866f6548421cb55121086cc6348421d354d21086776548421d554d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b3254021da0c9500876b2154021da48550086b86050740ab58b439029d63d0a40a758c41902ad6210640ae580419026e62d4d409b58b535025e63d49409758f525025e63145409758c515026e62145409b588515023e65d0540ae181415035a6094c40ab58b43102b960d0c40c794d431034e5394840d354e521036a6094840d394d521034d5354840cbd0d521032d4354840a758f421031d53d0840ae583421031d5350840cb94942103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103374354440cd50d51103374254440cd509511037060544408f59641103355190440a758c41102ad6210440cd54441102b96010440cd54740102b96490040dc546401023f6550040cd545401027b6550040dc54540102bb6550040ced9540102bb6350040e694d40103995350040aed8940103aa5250040ea54940102b86150040ec94540103395150040ec545401033151500409b98a54cc26d6295330c798e54cc32e6295330cb58a54cc31e5450f30c755232cc29d640cb30c755032cc34d520cb30b558432cc31d54cc730c755131cc2cc624c7309b98b548c26d62d52309b988548c26d62152309d984548c27561152308f992528c23d6494a30cb992528c32d6494a30da982528c36952d0230ce550408c2e96210230da548408c2f16110230d394b308c2ba64cc2309b98a544c26d6295130b6982434c25c6550d30a7590324c2d5610c930b6980324c23e64145308f590514c26e62145309b588514c2cc624c5309e997404c3395410130b698c404c3994310130ba588404c2f16110130ae993304c2ce628c1309e983540c25e63150309b988540c26d62150309d984540c27561150308f992530c23d6494c3097d95300c27b654c0309798e54c825d6395320c798e54c831d6395320cb98a54c823e64d4f208f59353c823e6414f208f59053c82766114f209d58453c832e5450b20cb55332c82ad640cb20cb55
  | 2 => 0x654c832d3d95320cacf644c832b3591320cb8e544c832e3551320cacc614c832b3d81320cb365494432cd552510cbc53294432d34c9510cb365454432cd551510cbc53254432d590d510cb554354432d9909510cb654254432d5cc9510cb663254432d54c9510cb653254432d14c9510cb3a5494032ce552500cbc93294032dc946500cb715194032ce951500cb395454032f24c9500cb725154032dc545500cb5a4354032d650d500cb6a4254032da509500ca7a6094f419e58253d06ad62d0f419e98252d06796094b41a758f42d066f6254e419b189539065f6354a419718d52906ad62d0d41a758f425065e63141419758c505066e62141419b588505075a6314141d658c505073b4314141ce50c505076a6214141da588505073b4214141ce508505073a4114141d394e521074d5394841d394d521074d5354841c754f411072d52d04418fd95411071d5350441cb54941106b860504419dd95411075a5394041d654e501076a5294041da54a501075a5354041d654d501076a5254041da549501073b4154041dc90550107394154041dc505501067a60d53319e58354cc66e62953319b58a54cc6d96090f319b98a50cc66d62943319ed81548c67860552319b988548c66d62152319e980548c6796015231b5584328c63f64542318f191508c66e62951319b58a544c66f62551319b189544c67b60551319e181544c6d96090d3197195434c63e64149318f590524c67a60149319e580524c72e6414931cb590524c74e4314931d350c524c7656114931da980524c769601493197997324c74c52cc931d3149324c74c528c5319b98b540c66d62d50319e983540c67960d50318f596540c63e64150319798c540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c72e5454831cb551520c65d658c831c7552320c74d528c831c7550320c74d520c831b5584320c71d54cc431d354b310c765528c43197d95310c71d544c431b3189310c74d524c4319dd95310c765524c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c7695254031d68c9500c7583254031d6cc5500c75931540319e98354c867960d53219798e54c865d63953218f99053c863d6414f219e98053c86796014f21ba58242c874c534cb219798e50c865d63943219ed81548867860552219798c548865d63152219e980548867960152218f990538863d6414e219e98053886796014e21d3d4c32886e5610ca21f10ca31886e4624c621f1cc9318863f64542218f191508865e63951219758e544865f63551219718d544867b60551219e181544865e6394d219bd89534863e6414d218f590534867a6014d219e580534865e6514d21c7990534871d6414d21d358853487556114d21d698053487596014d21d314e424
  | 3 => 0xe2a1650c916e1204f0000983480011457a5595f00027c07ccfac20000012e095000add069821e400000000000000c3000000589180002580011a8174ca6a07f0b9334865418000166f43f80033c00000000548458450373f8260d21120ba2bd59ab25520004bac81647b8701c20004040016b000000b28000d2890018360003c0e2000000000000002b0000000002b82e800212000000bf9be35649c981ef42296c33aaf4a606c128005368fd130d62ea9283222b0007e94680010a0007080039a001340f54983fd3a9491267ac9210a0281d920a4b530b342f0de13e790002170000800006f17a00133a030000006d00038226d698000000003e0e701eb25629320009f8002b00008a8000923e4724550000666fc00000268000000000000000000054400071800280000e9a3208a0000000018c51860acb32e2412c02700000000001003000010000060020040000000c0000000600000402800000000008050100000000100c0000300200a00c008000000080080500200800003002000000020000000000000001c000000020080000400a0100180400000401800006000000020000200000101a00006001000014018050000200000c01000c018010020040000000c00400000004020030020020040300300200000005000010008000020200080400400000803000000028020000440100101a0040000201800000006002000020070020040000800001c000070000040000500400805804000008000020160080000000201c0200103000c0c80100001c008030040000280a000010018000060040200001e010008130000040000000000011000000000008010020000080000000400002012000020000000040180700c00012801000000040100220000000800a000000000000627a6094b439e58252d0f6a6094b43da58252d0ece62d0e439b98a5090e6d6294243ced0e5090f6a6294243da58a5090ece62d0d43ae9824350e6e62145439b5885150e7a60145439e5805150e3f6550c4397d954310e7a6094f429e58253d0b5a6094f42d658253d0b1e5350f42b398f4290a5e63942429758e5090b5a6394242d658e5090b3b4294242ab98b4350ace63d0942ae9824250a5e63145429758c5150a7a60145429e5805150a3f65508429bd954210a7a60d53329e58354ccae96090b329e983548ca7960d5232b6582438ca7a60d51329e583544ca5d63951329b58a544ca3e64145328f590514ca7a60145329e580514ca3e64d41328f593504ca7661d50329d587540ca7a60d50329e583540ca3d6595032c798e540cb2e62950328f990540ca7661150329d584540ca7a60150329e580540ca5d6590c32b358a430cad96090c32c7951430ca6d6590832b358e420cae96090832cb951420cb8d4350832b358e320ca5f654c8329bd95320cacf
  | 4 => 0x72047218000000000000b00000004f254a7c43273000574001b22560b40011f4c0000001534e2000c78000c0b452400038a2a54a955000ad88422e556a84001840006640011b000000000610006a41c00020e0f8000000002fc8f04e0ee000001d40000000000055400000000000694a7a81588a70e61f04360b8ef96a0d80d4a68f63160e487019324a8c970124429c8000f12c0000b68c749ca51538ea010085160ef278ae52e89d34c0006600023a520619fe31823060029000918a6000476001268004d2aecba0001a20a0000004748285c046000a75639a30003340002600084c000002d80013a02f1667991391954c808000005347400080030a4dc001791481681126600c5c80000000000000280284794569104ec235129351f4a24f68421ee4153b8dc2f0ad1589253ea0745894116825104a540f2000e7a7f000000000112b6154de030000ab800299000000201fb00e5144d000102000000000b2aa0e58a548e9652f1aa1608f0448f80744712d1b422200110000000000000a32fa134002d20000000020100000000000262a1065800000000350000000288b81e0000000000000000000128000000000000001d1218312425ec999c64507a91985f358674820c8372afcd100000a00032a2d2ae0005085c5989ec3695425a00000000000000000000000000a8fd00087ca70a000000000000000000001bb000000001f453c0013d0c42341d400000000764f48f900000016000000000678002ec83c0016900048800000000910eea50580288000831ae398ff8002a2001110003b00000723947c850000a60003880000040c000e880000000072800000000948002a00015aa9345e000001c7000258b394a340270af800000000000000005480000032811000000000000000003362095600000000000000000000002050e61ec082100000ec6a00050a000458003c40011baa046ca081a0880e40000000047a000001392b4000191b64fa000b780036a000002002f800086acf4ac52c002450921040000050e628628000f405806800000010a3a7c078001201020000000026f0000000006822a001451961e814c000dd0007d92b9b130078c5f1a158c8c400000000000000004109a800071374460670ac52ca5c358d50549091c28e10000161863000000c8800000000001ae00004c000000c41e0000000003b0c080031a000048004e024485998000000dc144492068330233120000020c1320000017116a7e0680874c40015c0000000600021c056150ac800000778c9a0b0001f51188424c4bc5b000000000b7000000620ce0564da8d0002c11dc481458023940003f0d84a43a000000000000001900005f90390f000000002514d8000c18ed0004ec47800000000b9aa53fa598381873ce000bd0005a0a3d0a800000000f029027
  | 5 => 0x18412d0f0000dc0008321a32a3cc000d91565a00000000076ce00003ee000000db0004e853a1d00070c120000000000000008607000000194000e71132120000003f574000b180000015cbb8003c20009e9d60000002d8003aa93cb080035e11d5e2041f8000000000000000000050c001461b03d0030a18003b43902900000048c00000000000001ad000000fc9030003a4af000218000000eb3e2639440000000009c0bc000000281dc4c2a49370ae0005c0f600026c000f983d34ea445da5f4f2000000005a86dc00000000000698004aa00025000200001321d255a75c288fb42c8a46f8004c69e0000000000013596441c6cd67000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2c0054002e645cc242c6c8b61278a63c5e6680243e0eae709c7c6218007644688a88008200863000a06acab47e58160050561aa21c00001e0000008400003a34c002aa000a005a0840729422144ea8bc969a984a04b8b026366cb23238607446288c9ea47a48006e068e522aac4c90200000beba9210c4000c00000e50180204008000002004202c0300003801008f01201c10a2200d01020a64b86c899065235d0614c832992e030a641948d74d81320cb832a264a8865c15513254432a8ae521aa2195517090d510caa2b9c84a8865585c24254432e0a86a12a219544764c9510caa3ba264a8865515d13254432a8ee0992a21974132546500cb84aa264a8065d04c95154032e1286a12a01952972d0c5050724b1ac428283465cf4214141c32a63028220e295218141106a4b848629263895916114931c52c8b00a498e6161580524c70aaa2c21906383550624c431aa2e2192a018d48724c5500c723a9ac219443319db324c621c2ac8b08a690e4562584534870cb22c029a43945856014d21c90a6b048490d46758ca314872232a6498a4389551610c821c8aa6b086410e0d5418d21086263b2a690843585c43254021a90e690aa010d2572d0d5110298b8686a8881455cf4254440a62e1a12a2205517318151102b0b90c0a88818558d5110440c4ac4a8882204a972d8d401024cb9ec4a0081c254d5250040932e630a80204a972185401038929aa2a0081c454d5150040e44a4a8a80207215254540103183b2a2a00818cd8d5150040c66c4a8a80206155458432cc322a92c21966183550624c730c62a8b08811866152584408c344a1ac4202618c5516110130d2286b0880986255458432c8322a9ac219641835506348720c62a8b088110651535844088322a9ac219241a258d4210120c62a8b0880906a14258440482c4ba06498241705c4324c120c66a8b0881884b17690440c4306b1ac42a2218558d6115110c4ac4b08a88863161580544431932c83202214c1d54150110c50a8b1460886185458e2044318aa2c2200219454d6110010cc2a4b08800843876551100430c322a6880218a1915244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x482ca000e00060005905841d93254432941801d9325443294180dd1325443290584dc13254432a11831d95150040a21821d95150040a2182d8d5150040a1183d895150040
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 682
  | 4 => 725
  | 3 => 102
  | 2 => 8
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
  | 5 => packedAt s5K5 (20911+((h/227+packedAt s5K5 (18414+(h % 227)*11) 11) % 1089)*11) 11
  | 4 => packedAt s5K4 (30201+((h/241+packedAt s5K4 (27550+(h % 241)*11) 11) % 1158)*11) 11
  | 3 => packedAt s5K3 (5236+((h/34+packedAt s5K3 (4998+(h % 34)*7) 7) % 123)*8) 8
  | 2 => packedAt s5K2 (488+((h/2+packedAt s5K2 (480+(h % 2)*4) 4) % 15)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e3f8ff1fc1c71c73c63e3f1fc7071c71b3c93
  | 1 => 0x1fc7f1fe3fe07fffc07c7c7e0f807fff24c0ff
  | 2 => 0xe007fe003fff81f8ff807f800fff81f8c70f1c
  | 3 => 0xfff800003ffffe00ffff80000ffffe00f80fe0
  | 4 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xc290a46204c0a2880c20a0906c131456091c91
  | 1 => 0x4010000480100000004042000802080004026
  | 2 => 0x413220a49148250154806904a5250132470518
  | 3 => 0x88804d4922904092a96900094a4a4c04b80ac0
  | 4 => 0x11244980031a4924f252524d800c0820f6a000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeefcc8feeefcc8feeefcc8feeefcc8feeefcc8feeefcc8feeefcc8feeefcc8feeefcc8feeefcc8feeefcc8feeefcc8feeefcc8feeefcc8feeefcc8feeefcc8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36396
namespace PEqualNP.Outside.L_meta_36396
open PEqualNP.Outside.L_meta_36396.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12454f12967a3178f428dc2c00d40000001c8012890006c0402b3c2c0283218fb06e21a2e36485334c1c83b06000322a0002d289cbba1ac42803a60e04263889a520698a011830000240cc0006081800c00a00027fd5007fe54027f55007fc54017fd4c05fe53017f54c05fc53017fd0c05fe43017f50c05fc43027fd4809fe52027f54809fc5201ffd0801fe42007f50807fc42017fcc805fe32017f4c805fc32027fd44097f51027f94409fd51005f54409fc5101ffd0401fe41007f50407fc41017fcc405fe31017f4c405fc31007fc8401fe21007f48401fc21027fd4003fe50027f54003fc5001ffd0003fe40007f50003fc40017fcc003fe30017f4c003fc30007fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24001fb0812000ff04090007fe1048003fd0824001ff0412002ffecb88016ff65c400bff32e2004bf9971002efccb880127e65c400bfeb2e200abf5971002efacb880027d65c400bfe32e2005bf1971002ffec988016ff64c400bff3262003bf9931002ffac988002fd64c400bfe3262005bf19310057fea988033fe54c4015feaa6200cff1531002ffec788016ff63c400bff31e2002bf98f1002ffac78802efd63c400bfe31e2005bf18f1005ffea78802ffe53c4017fea9e200bff14f1005ffe878802ffe43c4017fea1e200bff10f1002ffec588016ff62c400bff3162009bf98b1002ffac588002fd62c400bfe3162005bf18b10057fea58802bfe52c4015fea96200aff14b10067fe8588003fe42c4001fea16200cff10b1005ffe658802ffe32c4017fe996200bff0cb1000dfcc388017ff51c400bbfa8e2005ff9471002feca388017fd51c400bbea8e200afd54710006eaa388017fc51c400bffa0e2005ff9071002fec8388017fd41c4001faa0e2005ff1071002ffe6388017fe31c400bfe98e2005ff0c71002ffe4388017fe21c400bfe90e2005ff0871000dfac188007ff50c4003ff2862001ff5431000ff8a188007ff40c4003ff2062001ff5031000ff88188007ff30c4003ff1862001ff4c31000ff86188007ff20c4003ff1062001ff4831000ff84188007fe10c4003fb0862001fe8431000ff82188007f410c4011ffb2a2008bfd9510047fcca88012fe6544011feb2a2008bf59510047f8ca88012fc6544001ffb222000bfd911003ffcc88800efe6444001feb222000bf5911003ff8c88800efc6444011ffaa22007ff95110047faa88801ffc544400dffb1a2006bfd8d10037fcc68800afe634400dfeb1a2006bf58d10037f8c68800afc634400dffa9a2006ff94d10037faa68801bfc534400dffa1a2006ff90d10037fa868801bfc4344001ffb122000bfd8910007fcc488026fe6244001feb122000bf58910007f8c488026fc6244011ffa922008ff94910047faa488023fc524400fffa122000ff90910007fa848801ffc424400dff9922006ff8c910037fa648801bfc32440037fb0a2008ffd4510046fea288017fe5144011fb28a2008ff54510006faa288023f55144001baa8a2005ff1451003ffe8288017fe4144001fb20a2000ff50510007ea8288017fc414400dff98a2005ff8c510037fa6288017fc3144001ff90a2005ff88510007fa4288017fc21440037fb022001ffd411000ffca088007fd5044003fe2822001ffd011000ffc8088007fa4044003fea022000fe5011000ff88088007ff3044003ff1822001fe8c11000ffa608801bf93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff104400bfd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x7ff4050007fda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffe60a0007fe3050003fe9828001ff0c14000ffc40a0007fc2050003ff0828001fe8414000ff820a0027ff65c80137fb2e4009ff99720025fccb90027fd65c80257eb2e4009ff1972004df8cb90027ff64c80137fb264009ff9932001dfcc990027fd64c80017eb264009ff1932004df8c99004bff54c8023ff2a64012ff5532008ff8a990027ff63c80137fb1e4009ff98f20015fcc790027fd63c80217eb1e4009ff18f2004df8c790043ff53c8021ff29e4010ff54f20087f8a790043ff43c8021ff21e4010ff50f20087f88790006fe62c8013ffa964009ff94b2004fdca590027fd52c8025f6a964009ff14b2004ffe8590027fe42c8013f72164009ff50b20007da8590027fc42c8013ff9964010fbccb2004ffc6590027fd32c8013fe1964009fb0cb2004ffec390027fe61c800b7f30e4009ff58720005fac390027fc61c8025ffa8e4012dfd4720097fca39004bfd51c8001bea8e4012ff1472008ffe8390003fe41c8001fea0e4011ff10720087fe6390043fe31c8021fe98e4010ff0c72004ffe4390027ef21c8013ff10e4009ff48720007da4390027fc21c80037eb064001ffd432000ffca190007fd50c8003fe2864001ffd032000ffc8190007fd40c8003fe2064001ffcc32000ffc6190007fd30c8003fe1864001ff8832000fdc4190007fa20c8003fe1064001fb0832000ffc2190007fc10c801fffb2a400fbfd9520006feca900027f654801fff32a4004bf9952007ffaca9003efd654801ffe32a4004bf1952007ef8ca900127c6548001ffb224000bfd9120077fcc89000efe6448001feb224000bf59120077f8c89000efc644801fffaa2400eff9512007ffaa89003bfc544801bffb1a400dbfd8d2006ffcc69000afe634801bfeb1a400dbf58d2006ff8c69000afc634801bffa9a400dff94d2006ffaa690037fc534801bffa1a400dff90d2006ffa8690037fc43480037fb12400fffd492004ffca49003fee524801ffea92400ffb5492004ff8a49003bff4248013ff2124000fb90920007fa8490003ed4248013fe212400dffcc92006fde6490027fe324801bfe9924009ff0c92006fd86490003ff61480017fb0a4000ff98520007fac290003fc614800b7e30a400fffd452007efea29003ffe514801ffea8a4000df5452007ff8a29003bff4148001ff20a4000ff50520077f88290037ff314801bff18a400dff4c52006ff86290027ff2148001f790a4000ff88520007fa4290003ed2148013fe10a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fd1824001ff4c12006ff26090007fc3048003ff9024009fec812000ffc4090007ee2048003fe1
  | 2 => 0x210d7ea6290817fc3148413ff90a4209fdc852102ffc4290817ee2148401ffb024200bfd81210cffcc090806fe6048401feb024219ff1812100df8c090873ff5048433ff282421cff541210cff8a09086fff4048433ff2024219ff101210d7fe6090867fe3048435fe9824219ff0c1210cffc4090827fc2048433ff0824205ff0412102ffeca10816ff650840bff3284204bf9942102efcca108127e650840bfeb284218bf5942102efaca108027d650840bfe3284205bf1942102ffec810816ff640840bff3204203bf9902102f7cc81080ebe640840bfeb204200bf5902102f7ac810802bd640840bfe3204205bf190210c7fea81085ffe5408431feaa04217ff1502102ffec610816ff630840bff3184202bf98c2102fbcc61080ade630840bfeb184216bf58c2102fbac610802dd630840bfe3184205bf18c210b7fea61085bfe530842dfea984216ff14c210b7fe861085bfe430842dfea184216ff10c2104dfcc410827ff5208413ff2904209ff5482104ff8a410827ff4208413ff2104209ff5082104ff88410827ff3208413ff1904209ff4c82104ff86410816fe610840bffa884205dfd442102ffca210817fd510840bbea884205ff1442102ffe8210817fe410840bfea084205ff1042102ffe6210817fe310840bfe9884205ff0c42102ffe4210817ef210840bff1084205fd8842102ffa4210817ed2108413fa9084205ffd802102ffcc010806fe600840bfd3004201be9802102ffac010802fd600840bfcb004200be5802102ff8c010806fc6008431ffa804215ff940210c7faa010857fc500842fffa004215ff900210aff8801085bff300842bff1804216ff4c0210aff86010827fe2008413fe1004205ff8402102ff82010853ff65500297fb2a8000dfd9540004fecaa0053fe65500097f32a8014ff595400a5facaa0053fc65500097e32a8014df19540024f8caa0006ff6450007ffaa28003ff9514001f7ca8a000ffd5450029deaa28003ff1514009ffec6a004eff6350027ff31a8002bf98d4009ffac6a004efd6350027fe31a8002bf18d4009ffea6a004ffe5350027fea9a8013ff14d4001ffe86a000ffe4350007fea1a8003ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0026fc6250029ffa928014ff949400a7faa4a0053fc5250007ffa128003ff9094001ffa84a000ffc4250027ff9928013ff8c94009ffa64a004ffc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8005bf185400a7fea2a00537f5150029ff28a8014ff54540006faa2a0053fc5150007ffa0a8003efd054001ffc82a000ffd4150001dea0a8003ff1054009ffe62a004ffe3150027fe98a8013ff0c540007fe42a0003fe2150001fe90a8000ff0854000dfec0a0007ff5050003ff2828001ff5414000ff8a0a000
  | 3 => 0xe29e4222ffd0f21117fc879088bfd43c8445fe21e4209ffd4b2104ffca590827fd52c8413fe2964209ffd0b2104ffc8590827ee42c8413fea164200fb50b2104ff88590827ff32c8413ff1964209fb8cb2104ffa659088bed32c8413fe1964224ffd4721126fea390817fe51c8449fea8e4200df5472102ff8a39088fff41c840bff20e4200ff5072102ff8839088bff31c840bff18e4222ff4c72102ff86390827ff60c8413ff3064201bf9832104ffac190802fd60c8413fe3064201bf18321127fea190887fe50c8449fea864221ff1432111ffe8190887fe40c8443fe2064222ffcc32110ffc619088bfd30c8443fe1864209ff8832104ff84190887fe10c840bfe0864205ffd962102dfecb10817fe65884097f32c4205df99621024fccb10817fd65884417eb2c4205df59621004facb10817fc658840b7e32c4205ffd922102dfec910817fe64884077f3244205ff59221005fac910817fc648840b7e3244220ffd52210fffca910883fd548843ffe2a44205ffd8e2102dfec710817fe63884057f31c4205ff58e210f5fac710817fc638840b7e31c421effd4e210f7fca71087bfd538843dfe29c421effd0e210f7fc871087bfd438843dfe21c421abf58a21107fea510827fe5288441fea944209ff14a210fffe8510827fe4288401fea144209ff10a210f7fe6510827fe328843dfe9944209ff0ca2102dfcc310817ff518840bbfa8c4205ff9462102ffaa3108177d518840bfe28c4205ffd062102ffc8310817fd418840bfe20c4205ffcc62102ffc6310817f6318840bfe98c421efd4c62102ff86310817ff218840bf790c4209fdc862102ffec110817fe60884037f3044205ff58221005fac110817fc60884037e3044220ffd42210effca110883fd508843bfe284421fffd02210effc8110877fc408843dff984421dff8c2210f7fa6110877fc308843bff1044209ff0822102ffc2110817fc1088439ffb2a421cbfd95210e7fcca90812fe6548439feb2a421cbf595210e7f8ca90812fc6548401ffb224200bfd91210dffcc89080efe6448401feb224200bf591210dff8c89080efc6448439ffaa2421bff951210e7faa89086ffc5448435ffb1a421abfd8d21007bec690802df6348435ff31a4202bf98d210d7fac69086afd6348435fe31a4202bf18d210d7b8c69080adc6348435ffa9a421aff94d210d7faa69086bfc5348435ffa1a421aff90d210d7fa869086bfc4348439ffa924209ff949210e7faa490827fc5248437ffa124209ff90921007dc8490803fd4248401f6a124209ff109210d7fe6490827fe3248435f7192421aff4c9210d7da6490827fc3248439ffa8a421cdfd452102ffca290873fd5148401bea8a4205ff145210dffe8290817fe4148401fea0a4205ff105210d7fe6290817fe3148435fb18a421aff4c5
  | 4 => 0x8af7c4054459bf982a22bdf8c151166fa60a88af7c3054457bf102a22bdf0815115efc20a88177c105440bffb2c8205bfd964102ffccb20812fe659040bbf32c82049f9964102ffacb208aafd659040bbeb2c82009f5964102ff8cb20816fc65904077eb248203ffd524101ffca92080ffd5490407fe2a48205ffd8e4102dfec720817fe63904057f31c8205ff58e4114dfac720817fc639040b7e31c8229ffd4e4114ffca7208a7fd5390453fe29c8203ffd0e4101ffc872080ffd4390407fe21c8205ffd8a4102ffcc520826fe629040bfeb148200bf58a4102ff8c5208abff5290455ff294822aff54a41157f8a52080fff4290407ff2148203ff50a4101ff885208a7ff3290453ff1948229ff4ca4114ff86520816fe619040bffa8c8205dfd464102ffca320817fd519040bbea8c8205ff1464102ffe8320817bf4190407fba0c8205ff1064102fe88320817ff319040bff18c8205ff4c64102ff86320817ff609040bff3048201bf9824102ffac120802fd609040bfe3048201bf18241157fea1208a3fe5090455fea848228ff1424101ffe812080ffe4090407fe2048229ffcc241147fc61208a7fd3090451fe1848228ff88241147f84120817fe109040bfe0848227ffd954113dfecaa089ffe65504097f32a8227ff5954113dfacaa089ffc65504097e32a8205bfd914101ffea8a080ffe5450407feaa28203ff15141137fec6a089aff635044dff31a8202bf98d41137fac6a089afd635044dfe31a8202bf18d41137fea6a089bfe535044dfea9a8226ff14d4101ffe86a080fbf4350407ff21a8203ff50d411377a86a080ffc4350401ffb128200bfd8941007fcc4a0803fd6250401fe3128209bf1894113ffea4a089ffe525044ffea928227ff1494101ffe84a080fbf4250407ff2128203ff509410077a84a080ffc425044dff9928226ff8c941137fa64a089bfc32504077fb0a8227ffd454113efea2a0817fe515044ffea8a8200df5454102ff8a2a080fff4150407fba0a8205ff9054102f7c82a0817fc415040bde20a8203fd10541137fe62a0817fe315044dfe98a8205ff0c541007fec0a0802ff605044bff3028201bf98141007fac0a0897fc60504037e3028227ffd414112ffca0a089ffd505044bfe2828203ffd014101f7e80a080ffe4050407fe2028226ffcc14112ffc60a089bfd305044bfe1828225ff8814112ff840a0897fe105040bfe0828209ffd972104dfecb90827fe65c84097f32e4209ff59721125facb90827fc65c84137e32e4209ffd932104dfec990827fe64c84077f3264209ff59321005fac990827fc64c84137e3264224ffd532111ffca990893fd54c8447fe2a64209ffd8f2104dfec790827fe63c84057f31e4209ff58f21115fac790827fc63c84137e31e4222ffd4f21117fca79088bfd53c8445f
  | 5 => 0x10006010080000080040c8110000000380001a0780000103c028018060020000100300201c0280001a00c050050000041880200001c0780800202400827ff65908137fb2c8409ff99642025fccb21027fd65908677eb2c8409ff1964204df8cb2100efd6490807ffaa48403ff9524201ffaa92100ffc5490813ffb1c8409bfd8e4204ffcc72100afe6390813feb1c8432bf58e4204ff8c721026fc6390865ffa9c8432ff94e42197faa7210cbfc5390807ffa1c8403ff90e4201ffa872100ffc43908137f3148409ffd4a4204ffca521027fd5290813fe2948409ffd0a4204f7e852100fef4290813fe2148409fb10a4204ffe6521027fe3290813fe9948409ff0ca4204ffec321027fe619080b7f30c8409ff58642005fac321027fc6190867ffa8c8433dfd464219ffca3210cffd5190867fe28c8403ffd064201ff883210cbff3190865ff18c8432ff4c642197f86321027ff6090813ff3048401bf9824204ffac121002fd6090813fe3048401bf1824219ffea1210c7fe5090867fea848431ff1424201ffe812100ffe4090807fe2048432ffcc24218ffc61210cbfd3090863fe1848409ff8824204ff841210c7fe1090863fe0848430ffd9542185fecaa10c3fe65508097f32a8430ff59542185facaa10c3fc65508097e32a8409bfd914201ffea8a100ffe5450807feaa28403ff1514217ffec6a10beff635085fff31a8402bf98d4217ffac6a10befd635085ffe31a8402bf18d4217ffea6a10bffe535085ffea9a842fff14d4201ffe86a100fbf4350807ff21a8403ff50d4217f7a86a100ffc43508077fb128430ffd494204ffca4a10c3fd5250813fe2928403ffd094201fde84a1027fe4250813df2128409ff1094204f7884a100fec425085fff9928409ff8c94217ffa64a1027fc3250801ffb0a8400bfd8542007fcc2a1003fd6150801fe30a8405bf18542187fea2a10c37f5150861ff28a8430ff54542187f8a2a100fff4150807dfa0a8403ff1054217ffe62a10bffe315085ffe98a842fff0c542007fec0a1002ff605085dff3028401bf98142007fac0a10bbfc60508037e3028430ffd4142177fca0a10c3fd505085dfe2828403ffd014201ffc80a100ffc405085fff982842eff8c14217ffa60a10bbfc305085dff1028409ff08142177fc20a10bbfc1050801bfb22a22ddf99151006fac8a88b77c6454459bfb1aa22cdf98d51166fac6a88b37c6354459bfa1aa22cdf90d51166fa86a88b37c4354401bfb12a200df98951006fac4a88037c625445bbfa12a200df90951006fa84a88b77c4254459bf992a22cdf8c951166fa64a88b37c3254409bfb0aa2049fd8551026eec2a88b77f415440bbe20aa22cdfcc55102efc62a88b37d315440bbe18aa200dfd815115efcc0a88037d6054457be302a22ddfd015115efc80a8
  | 6 => 0x89004000378060000ab8000ad90ac9ad0e0000000d04000911280a849300000009bcb9c8e40000000000000007b525400095c548598e18e4cb101dc000a9000129800000076cfb42b80000008f10a9060720fe06551e0b406ccc705e80000007140000007641b0b79030b84560ae4e24750051020000000000cb8bc039093c00c0002e43285c46812900006b8d080013f8c806b4ebc000fcc1b400131434400000054c6e53ed19000000134004c001224a441e11550f8fc8f040007ec6f00006700000000009c0a990f49a00000013a84710993205cc43cff42ed200dc10148045180588fc638428df93b00000c50f053000114000000142c71800000000070cdf00f079029d0847f0f65024ce84c0cbd4280a0744f6104ce0c6751f80009d4710e200010e510c000000000000000001138028000000ed936c0003092a4000e803a4bf101d3980b12c46d0e445bc000f0c8188ad47c3f40c0000c2c000508820000064890d647fc4445f40000000005b80d06f4ec078c1f0d9c0003bc0000f40006490808f8ff8000d2c0002400011fc000b6c9704e00000000000000000002812751d4e3cf88e00000a3c3a8208d18000c6800113cf58080000000000fb8cd1000c64110aa8000000000f38c000000010dc9044a0b2d094000d485e5364514000e74bb800801814002014090040000040080a002000090090040140701501c054020030080e4008020040000200000000005803004008040070080140181d0000040500d00002c0000000c000028020040140300000a01c0180c006024048000000000f00c0200040000407c0000080200200007807002008008000200180d00000000401800000008000000480080080100200000003002000060010260380101101a0040280000c000018000000e806801000000000060000040780500000c0a000002010050030100200001500200800800000020018020020d400001006044008020000000181f000008000000060000b8000040180400400a0080080603a0000081201a0180180200000002001004004048270220140000000400c0100903400000800006018008030080080000000a00c008020000101c00100602c0000101e04400802000010000070040040080000200002801018004050030520140080101403c0300300000000002000000070000000181b80700001c00004000014008020040000380303000c0f0000020a40080404c0200180301e0000001200000c0000100000004000002008118100060100a801000000010020020dc0080002e0380280100c0580000400c038000000000100e803008000008050040040080e00001001808002000088000060100100000e01c068010280140180f0060180000301001c0001f00a0080080000400019005000000000010020300382b00e00
  | 7 => 0x4cf906ce9c16c1251a400019c4c82f0b141ccffcb443b4000830000c34000000000d240004f0ea01c8fb0fe8ca4ef8000c0800080d0c06e13e0bc80000004c4978000a100002003e40450d446ce10c140011e40052e8cacd540004b885c00040849cdbc228000e052d40000000011c0000d7830c68ca646ac7cd1cc6003dc42c998c60cd4e142986bc000000260d4c034968fc4000300fd00013845f061c3d924538c2e0c752d128cac14552509a4990340a752f422123c9143b85a51bcd284648d49c41d1204f84000db800118ca5114400021c5b00011191740004fd2700007a00000000011680003c8c20000a80e7c2040000011f0a882940008e11d00002e80000006280008e88b803d45c0012191ec000a94828a1d13000000000000000000069c8f48693e93f0ac512c4dc000000000df4000918f74000f0131c000000000424000cc80008948b4f94000000fa4001248c88000e1ca4c0001040012f8dec0000000000000005d400132c0000007e07753112bc000f4497535cd90f3126516ce6c0010680000000000006a8000af0000ea417045c71cae0a349492400000010d0000001028db400000044c7c4fa00004789392b8add1650b44007acda4dc54153540547c121d16040c2ac2907dce642c0c28b0cd709dd3d45710b915c284c980a8b38734934aa0568dfc00090082cd7c0e8000254484e6867c0006e8a0ca7007103c66ca60ab546c0008087a48d0858264fecb508c4b6000000035c000000380dd13080003249f9114b9144000129c9c8511438e2c00135811800005c00102c000ca88440000002cc0009f40009b026c5dc4193fc840f18474000001230d3ccb4108bbc00066000000011ca20cb0000b8816000000002c00000000043086c14436c008878c7c000001410d8453ccd8364000b34b4810ca68754f2cb206d852cad075c0008c800098c164b28348318a8c2704d00012b4c78fe42fc000924898af80009810181c00014608ed2c8f9919c000000f4c2a0fa8a589e0824d304b51b80008c0b8c0403cc09c001304000190e34534a543c50fcf346440012687800009208bc000000ed4000ce509d0747280011d8a2c870000000a253f4accf082148a4ed0d400000000009600b8b582100000012dcc4c00137c0000000013d8784000ec4e90b747381951c40000000010cc7404e88a83540010410a11b453823c6902b43110485004386ec74cd94001368000000c9d4700e4ff0de888c4bd054e780000007a8000950000e087d90780000013393dd43d1dc00128870809400020c278b1ce60398f6d444f3cbfcccc0383054353444cc9e91886a0614000ef5350000000000e546fcaa4000000d0c13cb040000004f51587f4c30138bb45e0000684000cec7c80002f4bb000033864c0ad3241e4ac90bc7b81b911091c6640003
  | 8 => 0x1bc0000000006300300001d4cdc00000000000012c00062c000f147883300dc0007b00b400059ca0097c4d400039404877c09868907c61800008d3b4bcc00055107084c1a90a40010100d44512ccda873c00108d2a023434d3b9044edc00065031cb9899c00000074801d220ee51980010b001096cd34c8d3c5370e382a50507bc1acef0be8000e84001400000000000000000994d98000f1c000a0400000000025006920d480d447580000014487e9108000000000850000c3914c49930c658440000000174000bf80005204ed4203e91ac090c188380006941010c8bd0544f8c5041680c91e85652ecad54305c8cc0d5881d1f427c38d23492cc04000814089128f6876879c00000092863d134c0cbd448d05d390f54e7022c6b00240743151a8b70488000dd80840005f8ba4000000c3c000dd44f93e406cb300fcd683f8fbc2d459460d41c988eac0003ad22d3a0000018f500007d40000002d0d1c245360efcab13aceb40007050905293cc000ec80008880000001f8000678000000000700a784d80005a0000000000a140005a85780008d800000073100d34c33cc6cb18000d88a2903890c5b5348e5c554000000e58874c5c604b3c5c00011200000005fc00000117c0013751940009cc420b01464958000e50d140013a52ac9fd294370c587f8e8894cb554749a8e285748602a87703a0f28bf49f02bc1c432d064c24b6524cf9d258f79468b953009b940d3bd44ceb8ce14590e8e94be5170af51046c86340f8bc40006d41ed180f90ee80012e483c1480ed39c9b4624848128eb00003580000003f12e0454000320b80000000fdc4680bcdac0011c8000810000b7c62115015087c14c25c0cd210d603fcb4d328ba8d75178590d6cb25408abd3782885d8fd46c0c105403d4c91394180e8c238f245840010c400089c2481541344045eca414843b0facd38410414ca0bed0d8724fc09e5284834d204608a0185334afc000c48000c94d80ecc524458000e480000002580009d12d800000050cdb051c0002f8000000799278000bdc2681fc000a300006a41a06c4cc40013d03d0000000b5c28d1b05580d896400111cbd84e5208fd8954aac000000000c84f807d14180001a44b090914841c000e40bac668218c440004905893c8f2065c8b0a6c8ccdccc50ddc610481228c1c5ac6409ec941405380795479451388a48aec0002d90090884a4188000ae80792a85805d06983500002c807c57cf10f7c944f484ac38480047c2b11a00004350ec000a18b68e98158dc8ee0a7c18cd8c3ec7e4d113c039c4488dc0a527c1d8d5ceec3e055c02125c608864000f70da02c4d5126000000015c2741e8a3856c22472d26c12103542424cf5d214a5c374230198000de51000000000012b133ccfd488778a9c368c411840140e0f400003348806f8c5
  | 9 => 0x9841f4178ba0e307601412c0be0360494cf00001140003c013058cea837c9d8de04a8cf4000a08b086dcd008552f00002dc00000017c8840012380000013190592fc000001125330
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x3705451015f76705451015f75705451015f74705451015f70705451002f77605451002e77605451002f73605451015f77405451015f76405451015f72405451015f75405451015f74405451015f77305451015f76305451015f72305451015f7530545101ff71305451015f74305451015f77205451015f76205451015f72205451015f75205451015f7420545101f5f6769051002ef6769051002df7759051002f7675905101edf5759051002f75759051000575759051012df5749051001ef6649051001ef4649051002ff3709051000df6709051000df4709051002ff0709051002ef7609051002ff36090510147f24090510147f230905101e7f13090510147f2209051001cff765051000cfe765051012cfd765051000cfc7650510006bf645051001ebc64505101df77515051000775515051002fb44150510005fb705051000df8705051002ff0105051000df4765051001ef4765051000cf476505101d5f775505101d5f5755051002df7745051002fb77450510007b7645051001ef6645051001ef4645051003fb4645051003fb743505101cfb5435051003fb74250510007b54250510007f3705051000df6705051000df4705051012ff0705051002ef7605051002ff3605051012fb7405051012ff2405051012fb5405051012ff230505101cff1305051012ff2205051000cfe76c851000cfc76c8510006ef62c851004eec62c85100077551c851000dfa70c8510005f970c851004cff764851000cfe76485100ccfd764851000cfc7648510005df7348510035dc7348510006ef624851004eec6248510007755148510005fb704851000df8704851002df8765011001ef8765011002cf876501100077b75501101bf78755011000dfb745011000fbb7450110007bb645011001efa645011001ef8645011003fb8645011003fba54501101bfb954501101c5fb73501101c5f97350110005fb7250110007f3715011002dfa715011002df87150110007f0715011000efb615011000ff361501101bf7b51501101bff251501100077951501101bff1515011000771515011003fbb415011003ff24150110007b9415011003ff14150110007b1415011002df8764811004ef8764811002cf876481100077b75481101a7787548110005fb7448110005f974481101b5fb73481101b5f973481101aefb63481101aef9634811000dfb724811000feb7248110007eb624811004efa624811004ef86248110007e862481101a7ea52481101a7e95248110007ea4248110007e942481101afeb32481101afe83248110007f3714811002dfa714811002df87148110007f0714811000efb614811000ff361481101a77b51481101a7f251481100077951481101a7f15148110007715148110007f24148110007f14148110007eb2148110007e92148110
  | 1 => 0x9110004ff725911004cfc725911021cff7159110006f771591100067f515911012cff7059110006fb705911004cfe76d8910004ff75d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d8910004ff73d8910014fe73d8910004fd73d8910014fc73d891002cfe71d891002cfc71d89100067f51d891002cff70d891000cfe70d891002cfd70d891000cfc70d89100eefa30d8910006f930d89100eeef20d89100eeed20d8910006ef62989100cdf571989100057f75589100457c7558910005bf745891003dbc7458910005df7358910035dc735891010df77158910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc7358910006ef725891010cff7158910006f771589100067f51589100ccff7058910006fb70589100cefa3058910006f930589100ecfe761891004eee6218910006ed621891004cff7690910004fe7690910004fd769091004cfc7690910006bf649091001ebc649091004eee6290910006ed629091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc765091004eee6250910006ed625091000dfa70509100267f765451015e7e765451015e7d76545100267c76545100067f645451016e7e64545100067d645451016e7c64545101fe7f63545101667e63545101fe7d63545101667c63545100067f62545102167e62545100067d62545102167c625451002d7f715451004777715451002e7f615451020777415451002f76415451002f7441545101ff77315451002f7631545101ff75315451002f74315451002f76215451002f7421545100077b705451015f78705451002e7f605451015f7a405451015f7a30545101ff79305451015f7a205451002f7b105451015f76105451002f74105451002f78105451004777765451002677765451015f74765451002674765451000777745451020776745451000775745451020774745451000777645451020776645451000775645451020774645451020f7773545101ff76735451020f7573545101ff7473545101ff7763545101ff7663545101ff7563545101ff7463545101ff7743545101ff7643545101ff7543545101ff7443545100077772545100077672545100077572545100077472545100077762545100077662545100077562545100077462545102077742545100077642545100077542545102077442545101ff7732545101ff7632545101ff7532545101ff74325451015f7770545100077
  | 2 => 0x2efa105931002ef91059310004ff7558b10024fe7558b10004fd7558b10024fc7558b10004ff7458b1001cfe7458b1001cfc7458b10004ff7358b10006df7358b10004df7358b10014fe7358b10004fd7358b10014fc7358b10006dc7358b10014dc7358b1002eef7258b10006ee3258b10006ed3258b1002cff7158b1000cfe7158b1002cfd7158b1000cfc7158b1002e7f5158b1002e7d5158b1002eee2158b1002eec2158b100ceef2058b100ceed2058b1002efa1058b1002ef91058b1004cff7690b1002cfe7690b10004fd7690b1002cfc7690b1019e7e6590b100067d6590b1004eee6290b10006ed6290b10004ff7650b1002cfe7650b10004fd7650b1002cfc7650b101867e6550b100067d6550b1001ebe6450b10006bd6450b1004eee6250b10006ed6250b1002f77765471002d77765471025677765471000777745471024776745471000775745471024774745471002f77645471002f76645471002f75645471002f74645471024f77735471023f76735471024f75735471023f74735471002f77635471002f76635471002f75635471002f74635471023f77435471023f76435471023f75435471023f74435471000777725471000776725471000775725471000774725471002f77625471002f76625471002f75625471002f74625471024777425471000776425471000775425471024774425471023f77325471023f76325471023f75325471023f74325471015f77705471015f76705471015f75705471015f74705471015e75605471015f77405471015f76405471015f75405471015f74405471015f77305471015f76305471015f75305471015f74305471015f77205471015f76205471015f75205471015f74205471002df77650710236f7765071022df7755071022df5755071002f76655071002f75655071002fb7745071002fb7645071001ef6645071002ef4645071002fb46450710067b74350710227b54350710067b74250710007b5425071000df6705071000df4705071012fb7405071012fb5405071001cfe76d911003ebe64d9110004ff75d9110024fe75d9110004fd75d9110024fc75d9110006bf54d911003ebc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d911003ebf43d9110006bd43d911004cfe72d9110004fd72d911003ebc42d911002cfe71d911000cfd71d911002cfc71d91100067f51d911003ebf41d911002cff70d911000cfe70d911002cfd70d911000cfc70d9110146bf40d9110146bd40d91100057f75591100457c755911003ebc645911021df77159110004ff75591100067f75591100047f7559110024fe7559110004fd7559110024fc75591100067c75591100247c7559110144ff7459110006bf7459110004ff7359110014fe7359110004fd7359110014fc735
  | 3 => 0xe6450520006bd6450520007ad42505200adee76c852004eee76c852004def75c8520285ed75c85200076f65c852027f6c65c852004def74c8520005ed74c8520006ef64c8520006ed64c852006dee73c852004dec73c8520276ef63c8520276ed63c852002eee61c852002eec61c852027f6f51c85200076d51c852004feb70c852000dee70c852000dec70c852004fe870c852004eef60c852004feb60c852010fea30c8520277e930c852010fea10c852000cfe768852007d7e75885200057d75885200067f65885201067c65885200cded7288520006f7618852002ef4618852000dfa7088520005f9708852000cfc76485200067f65485200e67c6548520005df734852006ddc7348520006f7614852002ef46148520005fb704852000df8704852004fe8204852000dec764852002eec764852000cec764852026def754852026ded75485200076f65485202676c6548520005ef7448520005ed7448520006ef6448520006ed6448520007cf734852006dee734852006dec734852025fcc734852006dcc734852025eef634852025eed634852004def714852004fe77148520007e7614852002eee614852002eec6148520007e461485202676f51485200076d514852025fe6314852025fe53148520007eb704852000dee704852000dec70485200cfe8704852004eef604852004feb60485200cfea304852025fe930485200cfea10485200067f74597100067e74597100067d74597100067c74597100067f73597100067e73597100067d73597100067c73597100067f43597100067e43597100067d43597100067c43597100067f72597100067e72597100067d72597100067c72597100067f42597100067c42597100067f32597100067e32597100067d32597100067c325971002e7f715971002c7f715971002e7e715971002e7d715971002c7d715971002e7c715971002e7f415971002e7e415971002e7d415971002e7c415971002e7f315971002e7e315971002e7d315971002e7c315971002e7f215971002e7e215971002e7d215971002e7c215971015e7f705971015e7e705971015e7d705971015e7c705971015e7f405971015e7e405971015e7d405971015e7c405971015e7f305971015e7e305971015e7d305971015e7c305971015e7f205971015e7e205971015e7d205971015e7c205971002e7f105971002e7e105971002e7d105971002e7c1059710004ff7559310024fe7559310004fd7559310024fc755931002ebf7459310004ff7359310014fe7359310004fd7359310014fc7359310066bf4359310006bd4359310004ff725931004cfc7259310066bf425931002cff715931000cfe715931002cfd715931000cfc715931002e7f515931002e7d515931002ebe415931002ebc415931012ebf405931012ebd4059310
  | 4 => 0x9120004ff715912002cfc71591200067f5159120076bf4159120174ff7059120006fb7059120176fa10591202cdee769092004eee769092004def75909202c5ed75909200076f65909202bf6c6590920175ed749092001eee649092001eec649092006dee739092004dec7390920005ed71909202bf6f519092000dee709092000dec709092004eef609092004feb609092018fea30909202b7e9309092018fea109092001cff765092000cfe7650920174fd765092000cfc76509200067f65509201867c6550920006bf645092001ebc6450920005fb705092000df8705092000dec765092001eec765092000cec76509202adef75509202aded75509200076f65509202a76c655092004def745092004faf7450920007af645092001eee645092001eec6450920077ac645092006dee735092006dec7350920077af435092029fad4350920005ef71509202a76f5150920077af4150920007eb705092000dee705092000dec7050920177e8705092004eef605092004feb6050920177ea305092029fe93050920177ea105092002cfe76d852007d7c75d85200067f65d85200067c65d8520004ff75d85200067f75d8520024fe75d8520004fd75d8520024fc75d85200067c75d85200247c75d852001cfe74d8520004fd74d852001cfc74d8520004ff73d8520014fe73d8520004fd73d8520014fc73d8520006ee42d8520006ed42d85200067f51d852000cfe70d852004cfd70d852000cfc70d852010efa30d8520006f930d852010ef710d852007d7e75985200057d75985200067f65985200067c6598520006f761985200057f755852007d7c75585200067f65585200067c6558520005bf7458520075bc7458520005df735852006ddc735852007d7e75185200057d75185200067f65185200067c6518520075be7418520005bd741852006dde7318520005dd731852002ef66118520006f561185200067f76545200057e76545200067e76545200047e76545200067d76545200057c76545200067c76545200047c76545200067f645452016e7e64545200067d645452016e7c645452028e7f63545201667e635452028e7d63545201667c63545200076e72545200076d725452015e7f62545200076e42545200076d425452028f6f325452028f6c32545202957f715452007f7771545200067f615452002e7e615452002e7c615452015e7f605452015f7a305452028f7930545202177b205452015f6e205452015f6c205452015f78205452015f7a1054520004fe7690520004fd769052002cfc769052007d7e75905200057d75905200067f65905201567c6590520006bf649052001ebc649052004dee7290520005ed729052000dfa7090520005f97090520004ff7650520004fe7650520004fc76505200067f655052013e7c655052001eb
  | 5 => 0x67d615472002e7c61547202176f215472015e7d605472015f6e205472015f7a205472015f6c205472002cff769072004cfe7690720004fd76907200957e75907200057d759072004dee7290720005ed7290720004ff7650720004fd765072004cfc765072001ebe6450720006bd645072004dee7250720007ad425072004def7648720006ef7648720305ef7548720305ed7548720005ef7448720005ed744872004eef6448720006ed6448720007cf7348720085ee7348720085ec73487202f7cc7348720085cc734872004eef63487202f6ed634872004fe7714872002eee614872002eec61487202ff6f51487200076d51487202f7e631487202f7e5314872000dee704872000dec70487202ed7e76d952007e7e76d95200247e76d95200067e64d95200067c64d95200067f63d95200067e63d95200067d63d95200067c63d95202df6f72d95202df6c72d95200076f32d95200076c32d95200057d71d95202df7a30d95200077930d95202e77b20d95202df6e20d95202df6c20d95202df7820d95202df7a10d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95202de7f72d95202e67e72d95202de7d72d95202de7c72d95200067f42d95202e67e42d95202e67c42d95200067f32d95202e67e32d95200067d32d95202e67c32d95200067f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95202e67f21d95202e67c21d95202de7f70d95202de7e70d95202de7d70d95202de7c70d95202de7f40d95202de7e40d95202de7d40d95202de7c40d95202de7f30d95202de7e30d95202de7d30d95202de7c30d95202de7f20d95202de7e20d95202de7d20d95202de7c20d95202de7f10d95202de7e10d95202de7d10d95202de7c10d952001cfe76d91200067f65d91200067c65d9120076be64d9120004ff75d9120024fe75d9120004fd75d9120024fc75d9120004ff73d9120014fe73d9120004fd73d9120014fc73d9120076bf43d9120006bd43d912004cfe72d912000cfd72d912004cfc72d9120076bf42d912002cfe71d9120004fd71d91200067f51d9120076bc41d912004cff70d912004cfd70d912018ebf40d912018ebd40d912018efa10d91200057f755912007d7c75591200067f65591200067c6559120076bc64591202d5ef7259120004ff75591200067f75591200047f7559120024fe7559120004fd7559120024fc75591200067c75591200247c755912018cff7459120006bf7459120004ff7359120014fe7359120004fd7359120014fc73591202d4ff7259120006ef725
  | 6 => 0xc765454016f3e74545400073d745454015e7f645454034e7f63545401667e635454034e7d63545401667c63545400067f62545402167c62545402957f71545400a77771545400067f615454002e7e615454002e7c615454016f3f415454015e7f605454016f7b405454015f3e405454015f3c405454015f78405454015f7a105454000dbc765054002ebc765054000cbc7650540345bf7550540345bd75505400073f65505403373c655054033ebf635054033ebd6350540006bf625054001dbf715054001fb77150540007b7615054002ebe615054002ebc6150540007b461505403373f51505400073d5150540007bb705054000dbe705054000dbc705054012fb8705054001ebf605054001fbb605054012fba1050540004fe76c8540004fd76c854004cfc76c85400067f65c85401267c65c854004eee62c8540004fe7688540004fd768854002cfc76885400a57e75885400057d75885400067f65885401067c658854001dbe7488540005bd748854000dfa7088540005f97088540004ff7648540004fe7648540004fc76485400067f65485400e67c6548540005df734854009ddc7348540004fe7608540004fd760854002cfc76085400a57e75085400057d75085400067f65085400c67c650854001dbe7408540005bd740854009dde7308540005dd730854000dfa7008540005f97008540004ff7559320024fe7559320004fd7559320024fc755932004ebf7459320006bf545932008ebc5459320004ff7359320014fe7359320004fd7359320014fc735932008ebf4359320006bd435932004cff725932000cfe725932004cfd725932000cfc725932004ebe425932004ebc4259320004ff715932002cfc71593200067f515932008ebf415932004eef2159320176bf4059320176bd405932004def7650b2032eef7650b20325ef7550b20325ed7550b2004faf7450b2001eee6450b2004eec6450b20085ee7350b20085ec7350b2008faf4350b2031fad4350b20005ef7150b203176f5150b2008faf4150b2000dee7050b2000dec7050b20004ff7558720024fe7558720004fd7558720024fc7558720004ff745872001cfe745872001cfc7458720004ff7358720014fe7358720004fd7358720014fc735872000cfc725872004eee4258720006ed425872004ef771587200067f5158720006f63158720006f5315872004ef7215872004ef4215872004efa205872004ef920587200cef710587200067f76547202167e76547200067d76547202167c76547202167f645472016e7e64547200067d64547202167c64547202167f63547201667e635472030e7d63547202167c63547202176e72547200076d725472015e7e62547202176e42547200076d425472030f6f32547202176c32547202957f715472009777715472002e7e6154720
  | 7 => 0x802102efa215802102ef9215802102ee9215802102ef821580213757e76d95400a67e76d95400247e76d95403673f74d95403673c74d95400067f63d95400067e63d95400067d63d95400067c63d95400057d71d954036f3f41d954036f7b40d95403673e40d95403673c40d95403677840d95403677a10d95403667f74d954036e7e74d95403667d74d95403667c74d95400067f73d95400067e73d95400067d73d95400067c73d954036e7f43d954036e7e43d954036e7d43d954036e7c43d95400067f72d95400067e72d95400067d72d95400067c72d954036e7f42d954036e7e42d954036e7d42d954036e7c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400047d71d95400067c71d954036e7f41d954036e7e41d954036e7d41d954036e7c41d95400067f31d95400067e31d95400067d31d95400067c31d95403667f70d95403667e70d95403667d70d95403667c70d95403667f40d95403667e40d95403667d40d95403667c40d95403667f30d95403667e30d95403667d30d95403667c30d95403667f20d95403667e20d95403667d20d95403667c20d95403667f10d95403667e10d95403667d10d95403667c10d954004cfe76d89400067f65d89400067c65d894009dde73d8940005dd73d8940004ff75d8940024fe75d8940004fd75d8940024fc75d894000cfd74d8940004ff73d8940014fe73d8940006de73d8940014de73d8940004fd73d8940006dd73d8940004dd73d8940014fc73d894035eee42d894035eed42d894002cfe71d8940004fd71d89400067f51d894035ebf41d894001cfd70d89402d6ef20d89402d6fa10d89400a57e75989400057d75989400067f65989400067c6598940006ef6298940075f970989400057f75589400a57c75589400067f65589400067c655894008dfb70589400067f65189400067c651894004eee6218940006ed621894002cfe76d85400a57c75d85400067f65d85400067c65d8540004ff75d85400067f75d8540024fe75d8540004fd75d8540024fc75d85400067c75d85400247c75d854000cfd74d8540004ff73d8540014fe73d8540004fd73d8540014fc73d854004cfe72d8540004fd72d85400067f51d8540356f641d8540356f541d854001cfd70d854021ef710d85400a57e75985400057d75985400067f65985400067c6598540006f7619854003df970985400057f75585400a57c75585400067f65585400067c6558540065fb70585400a57e75185400057d75185400067f65185400067c651854009dde7318540005dd7318540005ee7218540005ed721854002ef66118540006f561185400067f76545400057e76545400067e76545400047e76545400067d76545400057c76545400067c76545400047
  | 8 => 0x6bd5059021006bc5059021006bf3059021006be3059021006bd3059021006bc305902104ebf205902104ebe205902104ebd205902104ebc205902102ebf105902102ebe105902102ebd105902102ebc1059021006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c2104edf7258c2104ede7258c2104edd7258c2104edc7258c2104edf5258c2104ede5258c2104edd5258c2104edc5258c2104edf4258c2104ede4258c2104edd4258c2104edc4258c2102edf7158c2102ede7158c2102edd7158c2102edc7158c2102edf5158c2102e5f5158c2102ede5158c2102edd5158c2102e5d5158c2102edc5158c2102edf4158c2102ede4158c2102edd4158c2102edc4158c2102edf2158c2102ecf2158c2102ede2158c2102ed62158c2102edd2158c2102ecd2158c2104ed52158c2102edc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dd5058c21006dc5058c21006df4058c21006de4058c21006dc4058c2104edf2058c2104ede2058c2104edd2058c2104edc2058c2102edf1058c2102ede1058c2102edd1058c2102edc1058c21004ff7558021024fe7558021004fd7558021024fc7558021004ff745802101cfe745802101cfc7458021004ff7358021014fe7358021004fd7358021014fc735802100cfd725802100cfd715802102e7f515802102e7d515802102eef215802102eed215802102cff705802102efb7058021006fb50580210aefa5058021006f950580210aef85058021006fb40580210aefa40580210aef84058021006fb30580210aefa3058021006f930580210aef8305802104efb205802104ef8205802102efb105802102ef81058021006fb7558021006fa7558021006f97558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb5458021006fa5458021006f95458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f8435802104efb725802104efa725802104ef8725802104efb525802104efa525802104ef9525802104ef8525802104efb425802104efa425802104ef9425802104ef8425802104efb325802104efa325802104ef9325802104ef8325802102efb715802102efa715802102ef8715802102efb515802102e7b515802102efa515802102ef9515802102e79515802102ef8515802102efb415802102efa415802102ef9415802102ef8415802102efb315802102efa315802102ef9315802102ef8315802102efb215802102eeb215
  | 9 => 0xe74d8121004fd74d812101cfc74d8121004ff73d8121014fe73d8121004fd73d8121014fc73d812102cfd72d812100cfc72d8121006ee42d8121006ed42d812104cfd71d812100cfc71d81210067f51d81210067d51d81210cefa20d81210cefa10d81210057f75581210e57c7558121005bf74581210ddbc7458121005df73581210d5dc7358121006df6358121006dc63581210cef860581210067f74594210067e74594210067d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067f43594210067e43594210067d43594210067c435942104e7f725942104e7e725942104e7d725942104e7c725942104e7f425942104e7e425942104e7d425942104e7c425942104e7f325942104e7e325942104e7d325942104e7c325942102e7f715942102e7e715942102e7d715942102e7c715942102e7f415942102e7e415942102e7d415942102e7c415942102e7f315942102e7e315942102e7d315942102e7c315942102e7f215942102e7e215942102e7d215942102e7c21594210067f70594210067e70594210067d70594210067c70594210067f40594210067e40594210067c40594210067f30594210067e30594210067d30594210067c305942104e7f205942104e7e205942104e7d205942104e7c205942102e7f105942102e7e105942102e7d105942102e7c1059421004ff7559021024fe7559021004fd7559021024fc755902102cff745902102ebf7459021006bf54590210bebe5459021006bd54590210bebc5459021004ff7359021014fe7359021004fd7359021014fc73590210bebf4359021006be4359021006bd43590210bebc435902104cfe725902104cfc725902104ebe425902104ebc425902102cfe715902102cfc715902102e7f515902102e7d515902102ebe415902102ebc415902102eef215902102eed2159021004ff705902100cfe705902100cfc70590210bebf4059021006be40590210bebc4059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006be5359021006bd5359021006bc535902104ebf725902104ebe725902104ebd725902104ebc725902104ebf525902104ebe525902104ebd525902104ebc525902104ebf325902104ebe325902104ebd325902104ebc325902102ebf715902102ebe715902102ebd715902102ebc715902102ebf515902102e3f515902102ebe515902102ebd515902102e3d515902102ebc515902102ebf315902102ebe315902102ebd315902102ebc315902102ebf215902102eaf215902102ebe215902102ebd215902102ead215902102ebc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf5059021006be5059021
  | 10 => 0x8d210075f51d8d213bfd721d8d213b7ce21d8d213b7cc21d8d213bfd421d8d21006de60d8d21006dc60d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d213b6df72d8d213bede72d8d210d6dd72d8d213bedc72d8d21006df52d8d213bede52d8d21006dd52d8d213bedc52d8d21006df42d8d213bede42d8d213bedc42d8d213bedf71d8d213b6de71d8d210d6dd71d8d213b6dc71d8d21006df51d8d210065f51d8d213b6de51d8d21006dd51d8d213b6dc51d8d21006df41d8d213b6de41d8d213b6dc41d8d213bedf21d8d213b6de21d8d210d6dd21d8d213b6dc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dc40d8d213bedf20d8d21006de20d8d213bedc20d8d213b6df10d8d21006de10d8d213b6dc10d8d21005ee769092104eee76909210dded749092101eee649092101eec649092104def73909213aded7390921007cf639092139fcc639092102dee719092102dec719092104eef619092104fe761909213a76f519092139fe6319092139fe53190921005ed709092102cfc7650921006bf645092101ebc6450921006df635092117edc635092104fac4250921005f7715092102df4715092102dec765092101eec765092102cec765092104def745092104faf7450921007af645092101eee645092101eec64509210dfac6450921395ef7350921395ed7350921007cf6350921387cc63509210dfaf4350921387ad4350921007e7715092102dee715092102dec7150921007e4715092104eef615092104fe7615092138f6f51509210dfaf4150921387e63150921387e53150921005ef70509210267f76545212167e76545210e67d76545210267c76545210067f645452116e7e64545210067d645452116e7c645452137e7f63545210075f63545210065f63545211667e635452137e7d63545211667c635452137f5c63545211665c63545210076f72545210076c725452102e7f62545210076e42545210076d425452137f6e325452137f6d325452102d7f71545210e777715452102e7f615452102f76415452102f76315452137f75315452121777215452102f6e215452102f6c215452102f74215452102f64215452115e7e605452115e7c605452102f77105452101cff76505210dcfd765052104cfc7650521006bf645052101ebc6450521006df6350521136dc6350521005ef725052104dec7250521007ad425052100775515052100cfe76d8121006df63d8121006dc63d81210cefa60d8121004ff75d8121024fe75d8121004fd75d8121024fc75d812101cf
  | 11 => 0x67d73596210067c73596210067f43596210067e43596210067d43596210067c43596211067f72596212167e72596210067d72596212167c72596210067f42596212167e42596212167c42596210067f32596212167e32596210067d32596212167c325962102e7f715962102e7e715962102e7d715962102e7c715962102e7f415962102e7e415962102e7d415962102e7c415962102e7f315962102e7e315962102e7d315962102e7c315962102e7f215962102e7e215962102e7d215962102e7c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067e40596210067c40596210067f30596210067e30596210067d30596210067c30596212167f20596210067e20596212167c205962102e7f105962102e7e105962102e7d105962102e7c1059621004ff7559221024fe7559221004fd7559221024fc755922102ebf7459221004ff7359221014fe7359221004fd7359221014fc73592210febf4359221006bd43592210febf425922102cfc715922102e7f515922102e7d515922102ebe415922102ebc415922102eef215922102eed2159221004ff705922100cfe705922100cfc70592210febf405922101cff7650a2102cfc7650a211867e6550a210067d6550a2101ebe6450a21006bd6450a21005f77150a2102df47150a21004ff7558221024fe7558221004fd7558221024fc7558221004ff745822101cfe745822101cfc7458221004ff7358221014fe7358221004fd7358221014fc735822102cfc715822102e7f515822102e7d515822102eef215822102eed215822102efb70582210eefa40582210eefa3058221006f930582210eefa205822102efb105822102ef8105822101cfe76d91210debe64d9121006dc63d9121004ff75d9121024fe75d9121004fd75d9121024fc75d91210debe54d9121006bd54d9121004ff73d9121014fe73d9121004fd73d9121014fc73d912102cfd72d91210debf42d912104cfd71d91210067f51d91210debf41d912100cfe70d9121004fd70d912100cfc70d9121006be40d91210debc40d91210debc6459121005df73591210d5dc7359121006dc6359121004ff7559121024fe7559121004fd7559121024fc75591210dcff7459121006bf7459121004ff7359121006df7359121004df7359121014fe7359121004fd7359121014fc7359121006dc7359121014dc73591210debf4359121006bd43591210fcff7259121006ef725912111cff7159121006f771591210067f5159121004ff705912100cfe705912100cfc70591210d5de76d8d210d6de76d8d21014de76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d213b7cf72d8d210d7cc72d8d213bfd771d8d210d7d471d
  | 12 => 0xd73509413f6bf63509413f6bd635094101dbf725094101faf7250941007af625094104ebe625094104ebc6250941007ac6250941007b7715094102dbe715094102dbc7150941007b4715094101ebf615094101fb761509413ef3f5150941005bf70509410267f765454116e7e765454116e7d76545410267c76545410073f745454116f3c745454102e7f64545413e67f63545411667e63545413e67d63545411667c635454116f3f43545413e73d43545410067f62545412167c625454116f3f42545410073d425454102d7f715454113f77715454102e7f615454116f77415454102f3e415454102f3c415454102f74415454102f76215454115e7e605454115e7c605454116f3f405454102f77105454100cfe76d814112efa60d8141004ff75d8141024fe75d8141004fd75d8141024fc75d814102cfd74d814100cfc74d8141004ff73d8141014fe73d8141004fd73d8141014fc73d814104cfe72d8141004fd72d814101cfd71d81410067f51d81410067d51d8141006fb50d814112ef850d814112efa40d814112efa10d81410057f755814113d7c755814112ef86058141004ff7559321024fe7559321004fd7559321024fc755932104ebf7459321004ff7359321014fe7359321004fd7359321014fc735932111ebf4359321006bd435932102cfc725932104ebe425932104ebc42593210067f515932111ebf4159321004ff705932100cfe705932100cfc705932104eef205932104def7650b210beef7650b2104faf7450b2104faf6450b2101eee6450b2104eec6450b2104fac6450b213ddef7350b213dded7350b2111faf4350b213d7ad4350b2102dee7150b2102dec7150b213cf6f5150b2111faf4150b21005ef7050b210267f76547210267c76547212167f645472116e7e64547210067d64547212167c64547212167f63547211667e63547213c67d63547212167c63547210076f72547212176c725472102e7e62547212176e42547210076d42547212176e32547213c76d325472102d7f715472112777715472102e7d615472102f6e215472102f76215472102f6c215472115e7e605472115e7c605472102f77105472101cff765072104cfc765072101ebe6450721006bd6450721005ef725072104dec7250721007ad4250721004ff75583210067f75583210047f7558321024fe7558321004fd7558321024fc75583210067c75583210247c7558321004ff745832101cfe745832101cfc7458321004ff7358321014fe7358321004fd7358321014fc735832102cfc725832104eee4258321006ed42583210067f51583210067d515832104efb705832110efa3058321006f9305832104efb205832104ef8205832110efa10583210067f74596210067e74596210067d74596210067c74596210067f73596210067e7359621
  | 13 => 0x815115f7840d815115f7a10d81510057f74581510073f74581510053f745815116d7e745815116d7c74581510073c745815116d3c74581510067f64581510067d64581510057f73581511657e73581510057d73581511657c73581510057f72581512157c72581514057f71581510077771581514057771581510467f615815104777615815115d7f70581510077b605815115e7e605815115e7c605815115f78605815116e7f745964116e7e745964116e7d745964116e7c74596410067f73596410067e73596410067d73596410067c735964116e7f435964116e7e435964116e7d435964116e7c43596410067f72596410067e72596410067d72596410067c725964116e7f425964116e7e425964116e7d425964116e7c42596410067f32596410067e32596410067d32596410067c325964102e7f715964102e7e715964102e7d715964102e7c715964102e7f415964102e7e415964102e7d415964102e7c415964102e7f315964102e7e315964102e7d315964102e7c315964102e7f215964102e7e215964102e7d215964102e7c21596410067f70596410067e70596410067d70596410067c705964116e7f405964116e7e405964116e7d405964116e7c40596410067f30596410067e30596410067d30596410067c30596410067e20596410067c205964102e7f105964102e77105964102e7e105964102e7d105964102e7c1059641004ff7558a41024fe7558a41004fd7558a41024fc7558a41004ff7358a41006df7358a41004df7358a41014fe7358a41004fd7358a41014fc7358a41006dc7358a41014dc7358a4102eef7258a410deee4258a410deed4258a41006ee3258a41006ed3258a4102cfc7158a4102e7f5158a4102e7d5158a4102ebf4158a4102ebd4158a4102eee2158a4102eec2158a41004ff7058a4100cfe7058a4100cfc7058a41004ff7558241024fe7558241004fd7558241024fc7558241004ff7358241014fe7358241004fd7358241014fc7358241004ff725824104cfc725824102cfe715824102cfc715824102e7f515824102e7d515824102ebf415824102ebd415824102efb7058241146fa4058241146fa3058241006f93058241146fa205824102efb105824102ef8105824113d7e75d89410057d75d8941004ff75d8941024fe75d89410067e75d89410247e75d8941004fd75d89410067d75d89410047d75d8941024fc75d894102cfd74d8941004ff73d8941014fe73d8941004fd73d8941014fc73d89410febf43d8941006bd43d89410feee42d89410feed42d8941006ef32d8941006ec32d89410067f51d894100cfe70d8941004fd70d894100cfc70d8941006ef62989410ddf57198941005df7358941135dc735894111df7715894104eee6218941006ed621894102cbc76509413fdbf73509413fdb
  | 14 => 0x1657c73591510067f63591510067d635915116f3f43591510073d43591510057f72591512157c72591514357f715915100777715915143577715915113e7f615915113f7761591510057f70591510077b70591510057b705915115d7e705915115d7c705915100778705915115d78705915116f3f405915116d7e74d89510057d74d895116d7c74d89510057f73d89511657e73d89510057d73d89511657c73d89510067f63d89510067d63d89510076f32d89510076c32d89511067f61d89511077761d895115d7e70d89510057d70d895115d7c70d895116d7e74989510057d74989512157c74989510067f64989510067d64989512157f73989511657e73989510057d73989512157c73989512157e72989512167f62989510076f62989510e57d71989512177571989510e57571989514267f619895112777619895115d7e70989510057d709895115d7c70989510067e60989510067c60989510057f745895116d7e745895116d7c74589510057f73589510075f73589510055f73589511657e73589510057d73589511657c73589510075c73589511655c73589510067f63589510067d63589510076f62589512167e62589511257f71589510077771589511257771589510e67f61589510e77761589510057f705895115d7e705895115d7c70589511057e761895116d7e74189510057d74189512157c74189510067f64189510067d64189512157f73189511657e73189510057d73189512157c73189512167f62189512176e62189512167d62189510076d62189510076f32189512176c32189514267f61189510c777611895115d7e70189510057d701895115d7c70189510067e60189510067c60189512157f76909510057e76909510057d76909512157c769095116d7d74909512157f73909511657e739095142d7d73909512157c73909512157e72909512173f429095116f6f42909512176c429095102d7e71909510057d719095102d7c71909514267f619095119f77619095115d7e70909510057d709095115d7c70909510057f76509510057e76509510057d76509510057c76509512157f745095141d7f73509511657e735095141d7d73509511657c735095116f3f43509514173d435095116d7f725095116f6f42509512173e42509512173c425095116f6c42509510057f715095102d7e715095102d7c715095140e7f615095118777615095116f3f41509510057f705095115d7e705095115d7c705095115d7e76d815116d7e74d81510057d74d815116d7c74d81510067f64d81510067d64d81510057f73d81511657e73d81510057d73d81511657c73d81512157e72d81510057d72d81510577771d815102d7e71d81510257d71d81510567f61d81510577761d815115e7e60d815115f7a60d815115e7c60d81510077b40d
  | 15 => 0x8003000000400100480080000000010000002000002000c0000110008000004007001000c00000200000080100040028000006009008800000a00c002003c006009000000001a000001801001a00000000140040000030000000007000000000c0050010020000001000001c0040010000018000001000002c000000000000c00200000700000100000018004020006000000000800000400000000000000018000005000800401200700200000020000058000006000000800000000000500040000000028004010001000000400a0030040000002001001800c0060030060000002001000000800200000100280020000010048000004000002000a004003003c00a007004ff7558642024fe7558642004fd7558642024fc7558642004ff7358642014fe7358642004fd7358642014fc735864204cfc725864204ebf425864204ebd425864204ef771586420067f51586420def64158642006f63158642006f5315864204ef7215864204ef42158642004ff705864200cfe705864200cfc705864204eef2058642004ff7558242024fe7558242004fd7558242024fc7558242004ff7358242014fe7358242004fd7358242014fc735824204cfe725824204cfc7258242004ff715824202cfc71582420067f515824204eef215824204efb7058242006fb505824218ef8505824218efa405824218efa3058242006f9305824204efb205824204ef8205824218efa1058242004ff75d8542024fe75d8542004fd75d8542024fc75d854204cfd74d8542004ff73d8542014fe73d8542004fd73d8542014fc73d854211ebf43d8542006bd43d85420067f51d854211ef641d854200cfe70d8542004fd70d854200cfc70d85421857e75985420057d7598542006f76198542005df735854217ddc73585421857e75185420057d751854217dde7318542005dd731854202ef66118542006f56118542175fa7018542005f9701854200cfe76d8142176fa60d8142004ff75d8142024fe75d8142004fd75d8142024fc75d814204cfd74d8142004ff73d8142014fe73d8142004fd73d8142014fc73d814201cfd72d814202cfe71d8142004fd71d81420067f51d814208ebf41d8142176fa40d8142176fa20d81420057f75581421857c7558142176f8605814216d7e76d915116e7e64d915116f3e64d915116e3e64d915116e7c64d91510057f73d91511657e73d91510057d73d91511657c73d91510067f63d91510067d63d91512157e72d91510057d72d915102d7e71d91510257d71d91511567f61d91511577761d915116f3f41d915115d7e70d91510057d70d915115d7c70d91510073e40d915116f3c40d915116d7f74591510073f645915116e7e645915116e7c645915116f3c645915116e3c64591510057f73591511657e73591510057d7359151
  | 16 => 0x1c00400400680000080010010014004005000800000800000480180000030000008002000000801c002002000000000a00800180040100000020010000001000001c000003002002800a002008800c0000010000000000000000000000200000680040020000008000004000001800400000400100040060000000000002006000800800c00400080180020000000000000000005801400200000280000000000048094004000000801c0000030028000000001000000000000300080000080000018010000002002801c00400400180040040000000034000000001800000000d006001c00e004003800400000300000040020000000004002002008801800c0010000050006004000001401000000000000000040000004000001000000000000a000002400c00000400000020000000028022002000000001c0000000010000005001800000000b00400140040000000008000014000800c00000000000040040000000024002000005000000c00000a800400a0000000000004002003001c00000a005001000c00a000000c0000000000000000000001800000400b0000004002000001000001c00000000000000010000000000000001004000200100b00040000040098024002002003002c00a0000048000004000000800400000b0008004000002000000400200600280080020020038008002002000000000000700e8008000000000800400400d0008000000005000800800000000380080080070000000004000001800c000002004800000001400000040000010000038010003002800800a014003801000200500300000020040020010002002001801000000600080100020010010000012002000800000600b00300000160010000020000000007800c006005005805800400100580000000010030018006000001000001600600080040060000000000006002000001400800000b0018000000001003400a000001800000200b00000040020040010008000008008000800a000002000000001200000000020010018000002006000001800a0060018000002007000000400000000000000040030010000004001003002400000000000040000000018004004000000002c00a002001800c002001001000000000000000840060020010000004001000800400000100180000000060008000000000000000800600100200000020020000000002001001003c000000004800400200000a8000002000001003c010005005003c0040080000008010000002000000e008000800c0060010028000000000002002800200a000800c00e0000000010010000004804c000012000800000000000080000080010008000006004003000400e0030000000012000000000401800200b80200000000018018004000000000000
  | 17 => 0x211d400000017280000003400000c220004fe16f40000003792344ee00000001dad0c875938e9ed40004b3364a198e841aa2931108ae631a29c224911c9a6000260c5983051d528489c241745198a00005e50e88000a4a0bb400a7c81d6000000247c0b47d9000000124400000015e4000000101160800043e35e9d5c00000000000001a00004fc00011b406450c80014ba60409f80000003ea0000000000000000000000000000006fc00000000000003bc1920000800c6e76424588780000420000a78d3400000025f45ee3f43508000000a5047a00000006401fd8000e9600000027854169a20d09cc80be3d426d1dcce6a32500023f523a8a10579f28000898341a2289fc72614b81a917c30c0019880a6039519c0000b7600000000000009930929d10cb20000c600000006e73f71eb899e9b23961f8d0484f247380003a024d00000006747620000c284b497141121d400000032507140000004d6800081e6501442430eec00024293702d42c632103100000003f480006163eb49b000077077801600000c60fa4ec01b80004ec00025043ce000300000000000000000000000002c4800107800026c885c0009920d8800000008b24a1c194626ef153800000000000000244827a61dd8a1014400047880000000000000000da60000002008e2e41139228c096a40423020bc2061f117f995c28a61433d0000cd40002d0a1c4000648533000102031d000000131a46116f800147a9163de9fec59e1c439f129924250b01a9f3d4765df35900005b81900b3000000001e4579790a0a19a2520d9800000000000012be000250000071c88f000000117445132200000000000000c880000004190000f4002200000000000003f890e123893843b185c000000000000000086c122000000000044d00000300003c880003e0320000089c4c40000000000000000000000000093a00009300006f63e119b8000821000059c00000000007300000004fb0000c600000000000cb600000025bc00026700000000003e10001550c0c7ed5008000000000000142473c467295115042071c42400000005e9000000125e00004c00000000000002744d1c6e0000263c0000000000000d888f948080007aa3260ce8dc0d5600000011040000000001f6097a3f20ea800072272e36ca2780664f00d180000000000000000000000002000200200080080020090008010000000003800800000c000805c0000010000004008001000000000c00000000000020000020004014000001000000400000000040020010000004000002000000800000300080180000000000008006001002001000600400200000000080000000004002002800800200a000000c0020000010008004007001000400c0020038000002000000800c0020000000000000002005800000000300
  | 18 => 0x32000000000000034b86340006e818c05b858423d10a800004800029608c0e460001fb0000590000000000000092b05e96044529de42880000007fe0bd19d41ac7213c51bd4dc200000000004be000000000000000000008d81b868f2628a9000000006480007bc0000001c3946a1d60000428000000000283879200000003d400000007600010dc41d461988433c0ae1c915d48c86de40400003fa0000001238a487310232868d583d90bb2908b720000428b0c00000000019194d04cd3588d4005e2b04f60dc46529260000e9800070700000002d600026600f06583ca0e68bb8962a0a000000000000036e1740a2e1fe43f0000d526820f680009583fa1248c200000022e30000000000000000104c21a000104c61c000000055c4a437c1ee0000d704f4000197898c35801f20b40000000001c0005600000000014a452800000000000004c29fe82be8254f380000000001d883c413c379538800000024025700004a200000021280007e84bb29a8e682d4474800013200004489e8f4400044c98b89f49420bca91103c44600000013f27274a3a3a00003e722e000000031900028e000070442625c8000334298800000000041f95c0d4a00000000000000000000c25394a7413726ac0000000000be4fbe3e250899bd1b800049e0dec000000000000000000000000000000001fe13a000076f31c872856825317a000000059d00000006c284153286bd3209cc1a1026c37a1621301ce00006611dc8000000a51000144044876a00000006e87ad3be80000005560000f580c093707ba4b905c30608980000003c11a2a628a4e0002cf800076e1f62ad800123600035d8000d6c6893c30be8fe800000022fcae883046d800000035f1e7a8d0e327eb076800102400000000009fa00000023ec000000000115c0000a40000000000000000000000049c24f9f98000000000000000076700000008249bb19c8604a7659a2370000fa20cf00000001dc00c28f00008ba00048915880000000001650000a1b3c3855940c87740300004ec00032b07081d480f19e8000d960000fa9ebc5b400043a000032600525b8000b400002c6060803a72f000144c0000004dc80000000000cc00000001832268000e800003cc95b4d10a181c625b910287f26098246d075f2db9db54081d32548a58000793000217c0009431e3a918fd81a218391f12507ef3d880002769654d01b381063372caa25000000045697b062071b000159804e0c800000011a084b00006d8bac475227908529800007f0000000000000045400000048c8000040000000000028474303b28249ee40d396800083218735aa41000000000000000007880f3031c0b22c93e980008c497035c80000000000001d4cdf600028400000de945000025800000002d80000000001d78000fd400000029
  | 19 => 0xe000008c50000dd473e2e2000061432c0002ec8cc499483a2b2a9dc9b000045e963c71484e3af1d4840800008f16d48626431ad892005c4e900023092cc000178a438230000159a5654f426a519183509a2352d18a3400007f51780000001e409e91c80000004f2a324fee5f700000000000000002274a2800005900190ca15e2bd00012d0173000000000000000000000000000000000d24000000000000000000005100008e625f80000000003ca18bc42c9300001d5434e9d322000004580e4000000000000050e0ab45ba6a40000e9cddc8cd13917480c27020498000d4020f0f084bc0007a40ec03010a46940a8a4cd3a826500000010aa8b14319d24000000000235cef801900000003147b34be028c5de0000000000332000000000000085900000000e65ac00027b471aa4a15c8dd8b70000000000000004b00025e4ec61da22828dc0f047b0001c5516470a09c000062640e00015bc0000001d090f000016800010180d27822e798092d26a2000000082099600000000007bb056179cdfa0000001bb49f6000000000061a233240800143e34c47d00c40f62094e48548000000000000063e00010e000000000021c868140e394536a76508428003585813286e41758fe4f380672d6921c6601f934696e90d2a5300026e13328f02d3225412e5ee0000620e5201a2f3007c000a4e26a80000000002d7800000027e0b4823884a95b5169e586ca61e1b6997040a0e700023c802093e00000006ba9d7000000058a95c00000000000000b81f843d08f700000000001954ed800000000840d1abc00061618d93980000f60f188e80007ac22d000047c60100009ad4f000000000005629cb50b0b48b20000201800000015300014089420005398000000000050800000000000000007a49b5107182c7384e20d200006c00002ea8000000000000220800000000018e94820924fb8f140ca2914e70d7843e9ff0020000ef25451ffa9ad4fc0000001e540000000000adc0009c14299128db035651107ccbd000022d88dc232a54353973926463116c0000000638000000005a00000000000000000be80000004de3718000a1c0004f997f919c85a27200002de91446317eccf80000000d108de6132f7800097487b2d50000000025000154cad20a806c85f0316000074930d2ee00049d838444c6ca439800000000016801f40bc124090a9f141a0000dc00011200002799d3c4143883780a14d98a3f0000ecd1be44c52b8000c46000000201c0000fb39ba5340000000000398b660000000000d908683ed8000000000000000000000018b80009f073c000000000000030c00005f61a92fe1ba87b490f3f985380009b100009640000da1d491d108c0003a88a8800000023401c00000004ad0000df82e603e0000cc80f90099fe00005584f20000d221
  | 20 => 0x4c900000000000000b60dac00065d00000007fc4732aa8e15410000000000118e0003a39ad0b3697f00000000008b40000000c7a70b00019d122e0000000000b800e03e2a5a800005800001a0f02a2614e8ae000000000000005800001bc00008a61352b5a96c0885f21e113d91c26d6000000000025b4e19bc4a7266702000007900002220b5c00081c2e88000000000000102c00000006f00001a800053b0aeccc689f29480000000000001dfc00000026880003ca73a49687004727254c480005f80000000000c8e1fc0000000f0685700023f00000000000d280000f3000064482a6e5481000097000000000000007a52a600005504990000000fec00000000000420000001c88c6c50f000000000000000008b80001ab24819949044d737c000000041b4718000b3200000000008443ab2a0948c3965da395136c00000019d8b380009b70f500002ca8c816b00000003d11d2013ce563ae00017812c40364c599b44a89462e099e06ee32e3c79d2800077b1658a4d3500001fc0fc00000003f1000018a2c70ef800000000000022ac0004650460000fcea173128474b4e1200859458208000000134c0009ae0000550ce600720f11e400000029f9db800000038f800030899a000000000000019e000000073023880000000000001720000a101cb000111800005819451dc0001458000924000084a0612965be0000c9c0000003450000000000000000052000029a000000003245000000001c10531f542860000001f788523ed00021740007010000000ae20000001ef00009be0988f302600002a11b74d2a05634b18b4d0c77a37c9750a32324136000000076c00019600007b20000fa0a38000000208c0000002c994188da47748a80000001c82d10174f187ba11e29c800000000005fc00021229e86dd1081b348d266d4ce00047680002248723eb09754582ac1d91488bea67b173950d0fa2422a81b9877c08f000000056434909397c42c244e0a4835d2168c4143265cb9a0000fb9f2c1546df40b1ab92d69c200012340008110000e942540c641b2394000158000000062c207246109c5da0004070bb00009074522080f607682ac8d48b0ca472228028de89604fd8e5c9340001f30ca000000039e800018278000000007348d647a8000a6c88b1e017100007c84159ee4b2c00037f0bf8402998066a234a146544eb0a840000b805e2160cee41a0999a6000022a1c1249c8309e00a092bc528a053310f942444be45c81dc0001ef2f99accc103721c1986c00031c00000012f6860082800000062b0fc1e240001ad00014ac0009080001ff129200045b80ec000258000000000000000016c07580002ee000000036a39f800000000000012280003c629d25400003214cf852c00000000000014ea0df3341b08000a404b2000000075635f8
  | 21 => 0x8000eea79d515229c7748130d919f488e79b1c82830c068b8422000000000050a80000002f500006240000000001b340000000000268a06000000000000042309f097000041c22a800000063f00000000002e00001ce54b206c51725e06fa0003e193514bc22f402182825800025d88d11fe1dc2ff844477a500067000022e17400012587fa2ea3faa6001620000000000000000000202d15c00002a0000000a4d000000000000053c800000000025115f80000001c083e0c3a5972a0207d262225000259c00000004e00010e04e0000293112c76143100006de00024797843ae0002a3925cc0a8930e708a0ec04e74d0a8cd39e0663e6034cdaa1d90dc8884984a6220104d076855f51594b408a047510000109269900015493dc78410180014b04aa00000000008800ae89d132a34300017094aa00041e9f0400012900000011ec4cb000000008200022187b87a00001aa9ba4b5213c0ffa9b8e301d235d09b41fe2e451d1c152582381d1a4d000042e2318000000000000000080a14f000000116a00034298d000062c0001a054c6693422a7740000e8494a1bc444012000188800000033910fc2da75c14c8000fa07dc4f1a7c03680f4000083400000012f17c000051852b152000000000011fc17c74d4c880010360000000d9c000000046800129c00043380014289aa179000137827b04a8940d1657b000009800075a00009e400000000000000000000000c8d47c6693290c3c03600000000000000000de0000d5a476000000000017b0aa800116c7283151224098000453283cb3c000244000000000000026fc0009100150cbc00000052d000000000000000e4000000000024000000000000000000001bd00000000000001528c787e03e70d4cfe094005c93c4a6a0570000f4c00096c37f987c49491108da720000000000000000000033f948401e5ab4819e7c8489ac0000000000000000000007e000000000000000000017e800036400000000a4000011a27000067048f098543a46916f2808f1a0004048a480000000410b453fc00016d8cc8000a4b1ac9f2400065a0000000f8e9af00009fd254000000274000025722f000000083b000000000036e0000b840000000000000000831000082c000336000000139a94f0f91f906a8000000119886012814e00000003e9200000000000000015d800037e1450218000000000042081095730712185e664f269202877e5460000531200491491a44cdf40001448000000000000054000030300000000004c8000105934812321a972496c52f33b00000000000df00000006790001ea438c3f72fe80009fe175000000000000000016204769df13e000018603a0a0000000043315a80000000001e70000a8851f06e94f08407854a8800134a1f40001e38da48cf080a170a189484c105640e2
  | 22 => 0x803000000000000002510a80009582f59d9505000000000000002772d21b3c0000000f4800000055a0000000e3c4b4000164400000000000011981dd0000b4c0009b40fd187079a64947f000144e0000000000000000000000051c00000022a919413a40680000000002401a7000081d2751f6800000026f80013800000000000e8c000000000000000010d82801e09ea26b02b52ea7c61a89da40902471ce90240009252eb865d12e92000000006fe000252952c7164fc1418000000000000274800000000016d818400035315240000000001628ac215b2420a3c1104b213c04dd1e656822b04b457a53245294dc2187661668f7400087a0001694ea00000f60518c525ed1db0b8c00074e00000000006d73191ed93c40003758e6400000028096a0000246329800000000000000000009f141a00000000000001cec6560000001f000000000001cd80005920000c510a02bf51b038800055e09b1b18c20401475800043260711fa26c45a00000005f92e609448681402e42b623d251000000000000000000001eb90300008152c21d7420400026e8ba40009fa0bb8124d5449b3ac0528000346000034400079240a00001f87d40000938d2010e000000000057f000000147858b00000005366c14bf0a0800011c000000000058d08fa2c0b301e218a9dd1080708258000016c58324c23052ba000000000107c5041650a8d37a8354d398d4f7c8a939990280004930001d1549e6f300000000009ba2be1df9388000414a5b446200021d271ce9887c203971416e0004511a747dc62610e83bc4cc00000009911bc4ad0000000290302000213c00000017c00007607e53898cfc00034e000000036066b2ef00000009f5048a8e4000087000000069a0340000d8822899e0b223552f482a00000013cc94a4691bb087a95500000000000005219590fae8881f18c0051801c483098c6820002779edcaae0002df9a8c00000000021ac000a7d000000104e000000000000000000018f8bd442d49f8e6c0b82bc27c80000000000000000e209d52e58434a9a6e24658ca80008dd2c29574740000000049800005553781e8b988bb2f11b5085653e1b1802c25c3e41d120cd4261eb00022b033e8f800000004fa0000b8961c68e01438b11ac7268bc4760f60588448028a2cc000459534800097814d1a7a9b14467410001160fba9180000000e2449517b10508e019b1cc22180005bc0000000000a6143513ac93c7cd3cd0e3d492100000174c00042c32a863c0001bb00015e000051b000014c000909362a61c9880000000000ace5f800003f4f3c1c90001efcffa0e506c22443582a0014000000000000020e094e0b400000000000003ff8cd40006db000000000000000023600005db00000000000002b51ed013e34b13490ec3385ae2290000000000083
  | 23 => 0x320800000093d00000013d69240e38db04de7a8386a1790ac0001b480000001fb4b18000000000000000098ea6008d00000520000000ab800000000000000000000000cf8000000000000000000031200001c6000469863800051d3078000d8e7902258000d60000214000030022006917d87d850d1f884ac6e64d037b958054c00004000000e804300000010b677252f88200009fd3d38c0400209d2be86985d09353849e8c85e000000005c6660000001e5c000000000000014e386000261000000000021b40005b100a8cb4e226b72351aa10860004d81e84000000485073c8d88e253d976006095303906e81980000001f100003120b180008682fd1e580001e40001da800000000025c800000000034d88443c00814542380c2499c1ab800046461a00000f455415a2b600000000003a4000084c0000ea00004aa35a00000013b8000000000055600000000000000004ab141c00004d42395c80000001f9891400034815f16000000ab111843d0f00d500000000006d000026cc7be00026701e40005f90a380005b201100000000000001c219b000069f23ea05cf160840658000000961442a7a00006193aa02fc0004ed00012749ea7aa33886b82b808a326a8940000005120b540008371d6a6d940625613a8d700000000c31c504260000001b68b38206154977452a2ba000000100a00022fa5d07780000000abc0009a34aa00000001100000f6c0009e9000000000098c3b89124c6600000025494e0000000000000024f00000000000db2601c690c2000326158c00065f1528a607ea218115989ce0600000024e40000000001a30000000000215118000e333000000043600000000da000000000058200040604180002143e90b953521a500009c51dea5c14d19f802c43712580000000b323c083000000027286513e8000000000000000000000000c40002bb8f0c000268000148036a82c000220c01a8e44ce90c8c960003fc80000004a83301570e4054f0000000a2a80044380010720005229538c2a60c139a8784e06d11888e24f30981000000090600000016d13b40003600000000000000000000000000000000009c54af146800029f178144531c2870e1a8854520003d593b8d3c70f3dc12acc9c63b5141d6c60855100000006801160000f100000000548000000000000000000007e2e18000000a64027000048600000000007de0000002414eee6c338600002f00381f023649c653300027180000000000000b1c0003f921e406e0ba297222400000000000000000003420c79310000000235000000005280003506be140800000081909c8000b8e0001c383288fc3a84f79af0adc6872d91914a2441f2f182d40ea1db50026189460002fa000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe3664d9151440012ef0eb22a2880225d21d645451015db8406e4a8a202ba76869c951440014eb0d392a2880931d1da725451015db9404e4a8a2000b71809c951440014ef0cb92a2880ae9d2197254510005abc1ae4a8a203fb54835c951440016e700b92a2880aedc20172545100c63a3b0e4a8a202bb72801c951440016e300392a2880025de1d6254510044ba43ac4a8a2000b3784589514408166908b12a288002d5e0d62545101fdaa41ac4a8a2000e656218951440576e501212a288002dc602425451015db940284a8a202bb7287dc15144057ae50fb82a288016dca1b705451002db8436e0a8a202bd7276dc15144057ae0edb82a288002dc6137054510006b9ba6e0a8a2000d7174dc151440016e707b82a288002dc60f7054510005b8c16e0a8a2000d73805d64144001ae100bac82880171dd81759051002eb9b02eb20a2040d72405d64144081ae280bac82880035c8c17590510006b8982eb20a2000d72205d641440578e8eca8a82880035c547705051015e3b3b2a390a202bd72705472144001ae2a2b8642880af1d1d95148510006abb9aa290a203fd54735452144085cc8c4a8a42880063ea1b7048510006b8a8ee090a206dc7876dd540440013b307b928088002dc6147150110004bc43aa2a022005c78765454044081e6682a8a80880035ce1d5150110005b943aa2a022000b70875454044001ae10ea8a80880175c9d9515011002eb83b2a2a022040f32845454044001e6308a8a80880af5cdd1515011015f99ba2a2a022000f33645454044081e60c8a8a80882335cdcd5150110466b8b9aa2a022000d737254540440033710ea0a80880172e1d9415011002ed838a82a02208af33515054044001e62a2a0a8088006ec21d415011002ed843a82a022001bb28650540440037610ca0a808800fac219415011001f59bb282a022005db276505404400bb60eca0a808800fac1d9415011045dd9c2a82a02208bbb1855054044001e66eaa0a808822bcc1d5415011044ed9b9a82a022089db1735054044001b66e4a0a80881731e1db754811002c7c432e89022000b71851c520440017630838a40880025e21d514811002e3c3b2a29022000d738754520440016e50ea8a4088002dc21d5148110006b843aa29022005d7276545204400bae0eca8a40880035cdd15148110006b8ba2a29022088d73735452044111ae2e6a8a4088003d8a095148110007b0c12a2902202bd73725452044057ec6e4a8a4088003d8d895148110007b0312a29022000f62425452044001ec284a8a408821fd8cc9514811043fb0192a29022000b71859052044001b66e920a40880036c5d14148110007d0a12829022005ce876c852044001ec2a390a40880067a21d214811002e743b2429022035bc883485204400bbc0e290a4088003d85452148110
  | 1 => 0xee93a2cb880169da06745971022d3ac0ce8b2e2000a7b805d165c40574f100ba2cb880030f5d074597100052f418e8b2e2000a5d831d165c40014df04b9acb880029b20973597100051f420e6b2e2000a3d841cd65c40010fd0e21acb880021f61c43597100052fc1ae4b2e2000a5c835c965c40010fd0fa12cb880021f61f42597100052f41e84b2e2000a5d83d0965c400b4ed02212cb880029d60442597100043f43864b2e200087d870c965c400147d08192cb880028f61032597100072699064b2e2005a76810c965c40014eb02192cb880ae9ea0032597100053cc0064b2e20008ef825cd64c40131d904b9ac9880162f21d43593100243f42ee4b26200087d85dc964c40011bf06baac58800a3720d7558b100146f43ee6b162076c5f51dcd62c40ed8baa3b9ac5881db368437358b103b66c886e6b1620768de871cd62c4005998e7192c5880163b21d3258b100166639a64b1620008df835d942c40051b906bb285880162f21d6450b1002c7643ac4a162000a77865d151c4091a68e8ba2a388002dce01745471015db8402e8a8e2000a75869c951c40014ef0cb92a388002d5e0d725471023daa41ae4a8e2000c3d75d53644400156b03aa6c88800a2fe1d43d91100043fc2ae5b22200487c855cb64440011bf06b96c88800a3720d72d91100243f43eeab2220008bf845d564440011f700baac8880021fa1c75591100061e3aee8b22200087f855cd64440090f90ab9ac8880023be09735911004c76412e6b22200087e87d4564440090f90fa8ac8880031e1d770591100166d39a61b12200487e87dd5624400117f08baac48800e2f21175589100046fc1aeab1220028dc835d562440010fd0e3aac48800e2fa1f74589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100146f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b12200087f855cd62440090f90ab9ac4880022fe11735891001c5e422e6b1220008de871cd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd62440010fd0fa8ac4880121f21f51589100061fba6a2b122081c3c74d4562440018bee7a8ac48823b171cf51589100147c43a60b1220008ef8758862440131dd053b4848800eab211629091002c7c432e1212200087f855d942440090f90abb284880022fe1176509100046fc1aeca1220028dc835d942440071d90eb1284880ae9d607645451046f1ba0ec8a8a200087f8759151440090f90eb22a2880021fe1d62545100243e43ac4a8a2000a3f84589514405b47908b12a28800297e0d62545101652e41ac4a8a2005a7a86dc151440576e101ba2a288003cc90374545100053bc32e8a8a202ba74865d15144081a68e8ba2a288002dce01745451015db8402e8a8a208d
  | 2 => 0xc43d95202dc3f43e85b2a400087d87d0b65480014bd07a16ca900029760f42d95202e72619265b2a4000a3e841c7654800147b0838eca9000297a0c71d95200052ec18e3b2a405ca6e821c765480b74db0438eca9016e9ea0071d95202e53cc00e3b2a400087e8710765480010fb0e20eca9000297a0c41d95200052ec1883b2a405ca6e8210765480014db0420eca9016e9ea0041d95200053cc0083b2a400087e878c765480010fb0f18eca900021fa1c31d95200043ec3863b2a4000a3e840c7654800147b0818eca901729ba0831d952000536c1063b2a405ba7a800c765480014f30018eca900263e60375d912000c76c16e7b2240028bf8750f64480010fd0fb2ac8900021fa1c65591200243f43eeab22400087d81dd564480010fd0e3aac8900021fe1573591200243e42ae6b2240008f7815cd644800b1e902b9ac8900021fa1f51591200243e43ea2b22405bc6c76d954248001c58c9b2a84900029d60775d85200053ac08ebb0a400087f855d361480090f90aba6c2900063b60b73d85200043fc2ae7b0a400487c855cf61480090fd0dbaac29016e1f21b75585200043f43ecab0a4000c3c74d9561480018b8e7b2ac2900021fa1c65585200061e3a0cab0a4000c5c73195614800187ecbba2c2900030f19774585200062fb2ee6b0a4000c5c65dcd614801f0fb0fb28c2900030f9d365185200062f39eca30a4000a7581d94614800187ce8328c290003179cc65185202ee36b90ca30a4000a7581194614811f8f2e0328c2900030fd9574185200061e32ae830a4000c5f655cc61480018b8cab98c2900023de1d61185200043f434eca8a4000a75819d951480018eb033b2a2900031dc4276545200051fc22eca8a402da3c845d951480014bf06bb2a2900b29720d76545200053bc0aeca8a4000c6d821d951480018de643b2a2900031b0c876545200063b880eca8a4000c7a101d951480018ea203b2a2900021fe1d64545200043e43ac8a8a4000c6c769c9514809b6cb03392a2900ae9b219725452028da641ae4a8a4050b67815c951480574d90ca12a2900121f21676905200043fc2aed20a400487c855da41480011bf06bb4829000a3720d76905200043e432eb20a400087f87d9641480010fb0fb2c82900063b219729052006ce641ae520a400487e85dd941480010fb0bbb282900162f21d645052000536432a390a405d87c865d621480b70ff0fb2c42900021f61f65885200062e39eca90a4000c5f65dcd21480018b8cbb9a429016f1b1db6548520006a639eca90a40018ec865d1214801b39906ba242900163b21d644852002d7240ac890a400d9ce87dcd21480ed998edb9a429000399d946148520005e2c18c290a4000a6c86545214800b8d8eca8a4290147531cd514852002f3230aa290a4000dc873dc1214800187
  | 3 => 0xab0a8094c7b7019561500290fb0fb28c2a0003179cf65185400053ac0eca30a806ec3d7419461500018bce6328c2a00029d604651854049e3cb80ca30a8000c5f655cc61500018b8cab98c2a00031bd9672185400063632ce430a8000c6f655c861500018d8cab90c2a00023de1d61185400043f434eca8a8000a75819d951500018eb033b2a2a00031dc4276545400051fc22eca8a8000a77815d951500014f700bb2a2a00b297a0c76545400052ec18eca8a8000c3e841d9515000187b083b2a2a000317a0c76545400062ec18eca8a8000c3f411d951500018f6803b2a2a00030f90076545400061e200eca8a8000c78401d951500018ee203b2a2a00031e84076545400063a880eca8a802ba3c865d15150001878ecba2a2a024acde05745454015d9c402e8a8a802ca5e83d8951500014bb07b12a2a01b30f1db65505400054ec1ec4a0a8000a3c86545415000b878eca8a82a000a37a0e76c85400046ec1ced90a80058ee829db21500010ff0abb642a00121f21576c85400243e42ced10a800087f855da21500090f90abb442a00021f21975885400043fc3ecb10a800087d87d9621500031790cba442a00163e21970885400243f42eec90a800087d85dd921500051bd073b242a00023760e76485400062e39eca90a8000c5f65dcd21500018b8cbb9a42a00121f216760854002c5e424ec10a80018f8809d821500010ff0abb042a00121f21576085400043e432ea10a800087f87d9421500010fb0fb2842a01b70f9d365085400062f39eca10a806cc7a70d9421500031790cba042a00030fd9574085400061e32ae810a8000c5f655cc21500018b8cab9842a00163e21970085400063db2ae010a8000c78655c0215001317d0faa2c9900030fdd7545932004d57416a8b2640018ec825cd64c80131790ea1ac990026ab20943593200243f42ee8b0e400087d85dd161c80031d904b9ac3900263d21d315872015d37416eca8e4042c6e72dd951c80014ef02bb2a390186d320d725472048db3c0ae4a8e40109cc835ca41c80090fd0bbb283900021f617765072000c77416eca0e40109cc835d121c812139d0fb9a4390187531cd514872002f3230aa290e4000a5e8399365480014bb07326ca900021f61e63d95200051f424c7b2a4000a3d8498f65480010ff0eb1eca9016e9ba1b32d952000727b1e65b2a400096e870cb654800165b08196ca900039358c32d9520005b2c0865b2a405bb6a800cb65480b94f10c986ca90003d20c930d95202dd3d406e9b2a405ca7980dd3654800187ee93a6ca9000297a0e74d95200052ec1ce9b2a4000c3d741d365480b94dd043a6ca9016e9b60874d95202e537416e7b2a405ba6d82dcf654800147d0939eca900028f61273d95202dd3d400e7b2a405ca79801cf65480010fd0e21eca900021f61
  | 4 => 0x30840153d083aac610802a76107558c214d567c12e8b184209acc825d163084014bd0a3a2c610802976147458c210070faa4a8b1842008de8715163084011bb0e2a2c61080297a177058c210052ec2ee0b184200a9e84dc1630840153b09b82c610826b3a0a7058c214cd66c14e0b1842008de8714163084011bb0e282c610802a7a105058c210054ec20a0b184209ace82141630840159b04282c610816b5a045058c210056ac08a0b1842008de8710163084011bb0e202c61080297a144058c210052ec2880b184209ace82101630840159b04202c610816b5a044058c210056ac0880b1842018ed82dcd600840b1f50fa82c0108163e21d505802102c7d43e60b004200a7a85cc160084014f30b982c010802aea1330580210055cc2660b0042058f8874c16008401575083aac010802ae61075580210056d418eab004200ad9831d560084135d5043aac010856ba608755802102d79408eab004215af1811d560084014f70aba2c0108029e21574580210053d428e8b004200a79851d160084015b5063a2c010802b660c745802104d75410e8b004215ae9821d1600840b5e5023a2c010856bc60474580210071daa4a8b004200ada8315160084015b3062a2c010826baa0b73580210ad74c16e6b004200a7a859cd60084014f30b39ac010802aea1273580210055cc24e6b004200aeb8254d60084135d104a9ac010802aea1053580210055cc20a6b004200aeb8250d60084135d104a1ac0108029ea1443580210053cc2886b00420087d8798f655013147b0931ecaa00021fe1d63d954000537416e7b2a8000a6d82dcf65500db47d0939ecaa02628f61273d95400052f41ee5b2a8000a5d83dcb65500010fd0e196caa00021f61c32d954036d1f42065b2a8000a3d840cb6550001c9a64196caa00029da0432d95400053ac0865b2a806ca7a800cb65500014f300196caa01b68fa1071d95403651ec20e3b2a8000a5e831c765500014bb0638ecaa00029ba0871d954000536c10e3b2a806ca7a801c765500db4f30038ecaa00021fa1e31d95400043ec3c63b2a800087e870c765500010fb0e18ecaa01b68fa1031d95400051ec2063b2a8000a6e820c765500014db0418ecaa01b29ea0031d95400053cc0063b2a8000c5e73d9762500018bce632ec4a000317d9573d89400062e32ae7b1280028de83dd762500011bb07baec4a00023761e73d89400146fc3ae7b128000c9f415cf62500019b420b9ec4a023b179cf51d89400062eb9ea3b128097c3d74196625012d8f2e032cc4a00021fa1f65589400043f438cab1280008ef8758862500014eb03baec2a00029d60475d85400043fc2ae7b0a800487c855cf61500010ff0ab96c2a00121f21572d85400243f436eab0a806c87c86dd561500010fd0fb2ac2a00021fa1c65585404ae1fba0c
  | 5 => 0x8023761f42d8d210052f42e85b1a4200a5d85d0b63484ed4bb03a8ec69080297e1570d8d210052e42ae1b1a4200a9f845c3634840153908b86c6909deb3a0870d8d213b566c10e1b1a42008de8714363484011bb0e286c690802a7a1050d8d210054ec20a1b1a4277ace82143634840159b04286c6909dab5a0450d8d210056ac08a1b1a42008de8710363484011bb0e206c69080297a1440d8d210052ec2881b1a4277ace82103634840159b04206c6909dab5a0440d8d210056ac0881b1a42008dd878836348401998c73b484909db331db6350921005e2c18e2a124200a5f8359151484594b906b22a290a7697a1b63545213b7a210ec6a8a4276c5f71d8d5148401caee3b1aa2909db95c4363545210072631ee4a8a4200e4c631c9514840b6c902392a290816d9206425452102d3643284a8a4205b64815095148401998c7b9282908166b21d425052102d5643284a0a4205ba48150941484858e8eca8a829090b591c9515052100792a12a2a0a42018ec825cf604840b8e8e2a8ec09080a37a1b73581213b46e436e6b0242008de87d8d60484018beebb1ac090803171d763581210064fba6c6b024200c9c74d8d60484011bd0e31ac09080317dd463581210062e3a8c6b024200c9f7418d6048401938e831ac0908030fdd274594210052f418e8b284200a5d831d165085394df04b9aca108269b20973594210051f420e6b284200a3d841cd65084010fd0e21aca108021f61c43594210051f420e0b284200a3d841c165084014bd06382ca108029760c705942104d37410e0b284218a6d821c1650840b4ed02382ca108629d60470594210043f43880b28420087d8710165084014bd06202ca108029760c405942104d3741080b284200a6d82101650840b4ed02202ca108029d60440594210043f43e60b28420087d87cc1650840147d09982ca108028f613305942104d3741460b284200a6d828c1650840b17d0faa2c8108030fdd7545902102c5e43aa8b2042098ec825cd640840b17d0f21ac8108162f21d435902104d5641286b204200c3f759d5640840153d063aac810802a760c755902100557c12e6b204209aac825cd640840147d0a39ac8108028f614735902100557c12a6b204209aac8254d640840117d0e29ac8108022f61c53590210051fc2ae0b204200a3c855c1640840147d0a382c8108028f61470590210054f418e0b204200a9d831c1640841355d04382c81085eab608705902102d5b408e0b204217ab5811c1640840117d0e282c8108022f61c50590210054f418a0b204200a9d83141640841355d04282c810802ab608505902102d5b408a0b204200ab581141640840117d0f982c8108022f61f30590210051f42e60b204200a3d85cc1640841355d05182c810802ab60a30590214dd67c12eab184209acc825d56
  | 6 => 0x52ec1c40b2c8205a768188165904014eb03102cb208169da0420596410053ac0840b2c82008df835d562904051b906baac52080a37a1f7358a413b62fa8ee6b148276c5d51dcd62904ed93e83b9ac5209db275077358a410166639c64b1482058ec874c96290405998e6992c5208163e21d30582410243fc3aebb128200c3f435d762505030ff02baec4a08121fa1773d89410043ec2ee7b128200c3d7550f625040593ce6a1ec4a0802ab61032d894100667b9865b128200e8d430cb62504015cb02196c4a08121fe1f51d89410043ec3ea3b1282008ef87588625040159906b10c4a0802ec600715094116e1f3b6e8a8a821887e87d89515045b0fb0fb12a2a08168f219425454100477c12e7b0282098ec825cf60504011bf06b96c0a080a3720d72d814104c5e43a86b2642059ac8750941c84090fd0fbaac1909721fa1c75583210053ac08eab06420087f855cd60c84090f90ab9ac1908021fa1f51583212543e43aa2b0642098f8874c160c840187ee93a2cb108029ee0174596210053c402e8b2c4200c3d741d165884014bd063a2cb108029760c745962102d3b40ce6b2c429fa75819cd65884014df04b9acb1090a9b20973596210051f420e6b2c4200a3d841cd65884010fd0e21acb108021f61c43596210052fc1ae4b2c4200a5c835c9658853d4ef02b92cb108021fa1f42596210043ec3e84b2c4200a5e83d0965884014bb07a12cb1090b930c932596210051fc22e0b2c4200a3c845c1658840147d08382cb108028f61070596210052f418e0b2c4200a5d831c165884854dd04382cb108029b608705962102d3b408e0b2c4220a75811c165884010fd0e202cb108021f61c40596210052f41880b2c4200a5d8310165884854dd04202cb108029b608405962102d3b40880b2c4200a758110165884010fd0f982cb108021f61f30596210051f42660b2c4200a3d84cc165884854dd05182cb108029b60a305962102d3b40860b2c4200a75810c165884014bd07102cb108029760e205962102d3b40c40b2c4200a758188165884011f700baac9108063e201755922102c5e43a86b2442008bf845d5608840717908baac1108163e21d30582210245fc3aa9b2242008df835d564484051b906baac8908023ee01755912100c7c402eab2242028de87dcd64484011df04b9ac89080237a1c73591210145e43a86b224200ccc73dc964484018bee7a8ac890a3b171cf51591210046ec3ccbb1a4200a9e84997634840153b0932ec69080237e1d65d8d210046ec3cc9b1a4200a5e8599363484014bb0b326c69080237e1d64d8d214ee2f3b6a3b1a4200a9e849d7634840153b093aec69080297a1674d8d210052ec2ce9b1a4277ace821d363484ed59b043a6c69080387d5254d8d210046f438a9b1a42008dd8715363484ed1bd0fa16c69
  | 7 => 0x7870d8d64544590f90eb1ac8a88b68f211635915100536412c6b22a200c787058d64544592790ea1ac8a88028f21943591510070eb1a86b22a2a9d377150d6454551a70e0a1ac8a8a9f4ddd371591515371a326e2b22a22b97a87dc16454401c70c9b82c8a88035cdc77059151006b9c0ee0b22a200c7b61dc16454401ae6c3b82c8a88031edd870591510069dba0e0b22a200e38641c16454401ae6e2382c8a890a1f61f63d895121536412c7b12a200a6d86ccb62544014db0c196c4a880353dcc32d895100727b1865b12a200b65810cb625445b87ce8b24c4a88029e201649895152eb2b8ec5312a200a3d8418262544014db04304c4a88b257a1f73589510062fb0ee6b12a200d5761dcd62544012df04b9ac4a88025de057358951004af438e6b12a22cc5c73d8d62544850f90eb1ac4a8803531cf6258951006abb9ee2b12a200d5473dc56254549acee5b8ac4a88b61f61f641895116e1f3a6c8312a200a788059062544852d904b98c4a890b530c97318951004b7c3ac4312a200b4c8358862545476cf02b10c4a88028f61060189510063cb80c0312a200977815da42544012eb03bb284a880257e0d7650951164ae41aeca12a200977815d942544012f700bb284a88ae5e2017650951434bbc0ae9b02a205974815d360544570fb0fb26c0a88b70f9d364d81510071c206c9b02a20087f87593605445b878e8b26c0a88ae9e20164d8151004b7c12e7b02a24296c825cf60545452ef02b9ec0a88165d20573d8151004afc1ae5b02a22c95c835cb60544492ef02b96c0a88165d20572d81510053cc3681b02a200e3964d03605445b27d0fba2c0a88030fd8774581510069bb0ee8b02a200d3710dd16054401a6a21ba2c0a88030fdd874581510043f43ec8b02a22dc3c74d9160544570f90eb22c0a88b70f1d1645815115d3c402c8b02a20093f845cd605445b27908b9ac0a88025be097358151214b6412e6b02a200977815cd6054401a6ee9b8ac0a88034d1d371581510069c3a6c0b02a2a1d7371d8160544014df04b9acb208029b209735964116d1f420e6b2c8200a3d841cd65904014bf06b92cb208029720d72596410043f43864b2c820087d870c9659045b47d08192cb208028f61032596410072699064b2c8205a76810c965904014eb02192cb208029ea0032596410053cc0064b2c8205a76819c165905414eb03382cb208028fe11705964116d1e422e0b2c822da3e841c1659040147b08382cb2080297a0c70596410052ec18e0b2c8200a6e821c165904014db04382cb208169da0470596411553ac08e0b2c820087e87cc165904010fb0f982cb208b68fa1330596410051ec2660b2c8200a6e828c165904014db05182cb208169da0630596410053ac0c60b2c8205a76810c165904014eb02182cb2080297a0e20596410
  | 8 => 0x7127f2970001453ec0001d80000001d509824219d00044f0ff3332ba35615b0803584603920003080bc2880ce05a2c42931070c32ce3e431c0000560ee3e71da2c816246516700d2cf02a0000003c53792d009b2860df2304211b022c3a70072f81ec0cf0a92713e521f0bb3bc37f1902132764613830be07240b3520e40282981063d03d742a30f3691fa1bf2543ce0023df28f45128706714f3c725f22d0d709a0111b922e14222732336815629f2a12b84070004290d10001653d33da1042790a52052fe0002010000000f52683c408b2bb0530eb2a01a61ff0400f73ba32a26000007514c2eb3a43c12173a144c00000014b4431f526a0c220c19b41233f11400b22810b18405811504e01819738f4681e737c3554541ce0700001fe44712b3cf0000000002a21eb1d01742ac0b63c900000000000018707600045d0000000000002743b20032361430003863953fd13e3811630461ad25737b21800000a0000000009c03c0000105408c0181000201c0000300000c018000000000e0090040180100000206c000000160040000504e01000002014014000050020000180b00e0200000400a000000020540000000202a0440001200401c0880801e0180100b02602c0180104c04c0980000a0140780600802c1400200c0000d00600002801812014004018010000180e800002008020000040540b0080180040101c000000010000180141a8090100080000000609c1600a01a18c10000008010000010000241300d008018038020020000081c02c06c0280200200c0680200604c0481000c0141000904a00007001000000000040000040384900203c0380700200c0600000c0000180500c014000070000000480200e00000000006000068030080000000002001401818006018030020000140081f02802400003006078000020020040000300202400803000024190000020040500100203800000002014000020280280800000e0580082000a000040000020140181e0000000000100a02400004076014048000180100380a00807c000050000180002f00200010002002028288020020100a813008050038130000000080a00800c000090440000080003205c0100002e050028010020980480a0080300382e0020000281400006c1180502000003010000034000020000000e00000800401005004014000020000040001905e0540c80304c7a43a62b0c840487e85dc161908010fb0bb82c3210263e21d30582420043fc2ae1b0a840487c855c361508011ef0eb08c2a10b21f61f63d915116d1f426c7b22a200a6c8258f64544012bf06b96c8a88b25720d72d91510051ec3481b22a200b3581903645445b47d0db22c8a88025be097359151214b6412e6b22a200977815cd64544012f700b9ac8a88ae5e201735915116d1e426c6b22a200c
  | 9 => 0x410f25102d4102192fc00c00025e0a200034143500609f3b30002560002ad2cc0001d10cd0003890c82e111929e11300022f45a00000000012d45f0d826e35c1a905221600000036400013b00000004d0000f820705000000041600000000000000006b4250003144080002230002632340330001c046a2c90602250ca14a3f23b61684330cb04b0dd3ad3b83340003ae2703a82662060000000000002fa36124e0000000000000000001d200023a2b300000000023800000028c4633ef0003d200007b09e0000ef2201b400006900046439800008f00010821200000000000000e00026130001018b00000011b0003751bb0291b638b3c31960d526b2f105114409706640329005c1182911533d844133a1400003590b730c2031e80003052840d035725d30e12a24a38d45518c1342043d401e3be27e4522ef2851e23463d935d34d0ed2b229d0b30f100511620d25b3181270140000000000842c504912c3883e34260000b800021113c38736300000031142436a1e03fe21a3e225018d4182ee18631642d0483eb15432b4322ff2260940f02ae2de3f50ba2690990454500002f72772991c51e44490003270ac13000025a41143d3b500028929239737806e41715728a21d3bd06a24717f38a0003d135f2e80002ed31200040532623f1202451a31011a132205f34b1503ca1911e511c1511ea0003f00001493fa0000f42411943820000620001f227d26c17937e0ae00016d2a73b43dd2780b900a2942e01b117203a2b640a1114380e23dc4580003bb3280410593190003911780000000770254670001953311f733b0af11a3b93482a922b0f612e2f610a2f429638c1cf3b732f17a07d2e93de03f1522f23371240931db4401e32d32ca40615a08e0e934a3e63cc03526f3aa0d30d63304280131c11b80000b10122150c400000000000000044b2672f04420000322df1330000003cb06304436d44e00019f0a634044d2c236f0000002d441f37045900013f07400000019c0883321222e42a42a600002e0f200014808600038e00004734317b00023c0000003af17d19e43a40c2223621a22fb23727a07906f32e1823f90912951990b01f83a200011e3a50000543060001883a016c3e81e61b71383d60010390001092440cc2d80000000684130000fd41419300015d0ec1230310e03ff0c92d71aa4563b115e27c0ea10d3741ef32c1c41fc33534205b33d1e136006517c0000001800003072490000003090003451ed08a0000000000000001fb35328d1a51a002c41c0004442b144a1f03762b93210b235b0950bd00424b0570821ae23e0004691050000000210001102aa0000000730001d700000029b00015800000036c06400042b0852812532c308c15f2d60001310960000372e600045336720e00038500026d00034e1be0223e10bf0
  | 10 => 0x34403b2bc1250da43b2331a72dd1020e301f0b53962d53f728e20f07842f43710c18a0000002830000361a82fd41e16b1e91280a84021f11df35a1812b526530b17002644608124c0173103770c023200029c39c04f4572241600003722ab0002390000e639300033e2cd14122a02300835e39e0e713727334c43c3fc00000012624f1b53a316600005500019208914d0e142e0004221ac0e82750a40000003c20001c71f40fa05d0a034920002000025213216a3c040d3ee45c06d02b00021c3db2550a71c34193b00900dc46611f40142c0a300038401a16121e0922594200c14340421c643f43919a00022137300046b0002620002140002642bd2460002b009d20a05e04c33c40e3501dd0f33ac2a342328217e1d43e024330125832d08d3f402f41503d0003bf3a900016437a00036b13a09c3f804a01d0aa4003f63542c60fc39003e2e731e0001760191753381ba28b0c612939a39900f07f4452e303836e30232424d1f345b3f130d3a61032d112f1893ed31a0ad24000020b43100037d01600000000027223d0db00031b17101b2db0d201c2c70830c53043390ab0d41dc2f910e3201b318e1001f641b20800021b00039b4363941c900018327b4272d90d90de2da17339f29a4301c22482f31353660300b42dc3804093510e52af2e540f1551980872ea1592351cc0a12101f93473252c03172b41773293653360003c643e13d1af0c725c0152a816e0002be1ca06c1d63cd2a52cb2bf31307a03c07e3ab3151de2311853031b21ee34f0090002d231f0003f32c12f53d51fd1c80fb1a411d1170fe41a1121bd1bc2291212b737118f2093fb3e931d1cb0000270001361cd3c802400015c3ea23b41d2ec00000014e28004307c1461391ab39d0004621d945e2e230a0f916940400044816f0612021470001d303
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xe904ec3c080050e0d52c6c00341064c828b40048048018c0f0b1280000380000610c0000dc9c00007c00a91868787000211c54a53001002cd80090f84000fc00bc4400a00cb8d0007400c400000000000030002400ad1458e4000015104c9909201ccc0088849401240000008c005cf40400502183820800181060818114087020010001000c0103f9761a40d91510060e21070d8d6454401838841c163591510061a2087058d645440183870219435915116c872616350d645440160c9258d4359151007061c16350d645440143a9719370591510058664c64dc1645440143a96dd070591510050ea5c641c1645440161993190705915100651dcd810cb6254401a476360432d89510060e9d0805926254401839845c060189510058c64440d93605440123b9859340d81510050ee5d64d036054401a4532604325964100631dcd810cb6250401a854360432d89410040fe61741d16588401438905d07459621006075d1831d1658840b524975095150521006914c9810cb655000105d989cc65d89400061c5c181194615000146591195721854000607611831d951500014359190076545400040f660401d951500014359110076545400051c644401d9515000141d931d974545400060e200765d1515000124f9858c32d95200069158d810cb654800154a970c930d9520005c2650324c36548001741910c930d952000607dd1839d3654800103f985d074d95200061c5c181194614800143591195741852000515644655cc614800106d980c8765452000519644321d95148001a476560c6148520006131cc86545214800103f985d07459710006075d1831d165c4001a453260432597100061c1d9801c95144057470965d37054510004d8e4983dc151440013539360b70545100054c650805d6414400155193201759051000558648805d64144001561928c175905100055464e205d641440019337421d51501100055464c8754540440575309761151501100064c21d8454540440576309661151501100055464f7254540440015309754541501100056464f72505404405756097609514811043dd024d82545204400156097545214811002f181d951485204410fb40835452148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xe000860c42a0001000681124382c6a1ac8a8802419a3a5b741c1645440140cd1ce8402c9312a200a062817460c745962100603326400ecba2a2a00030309621d845454044001488d190ec22a2a022000c5020c975452148110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x60109668c876115150110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x94c
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x3
  | 10 => 0x138e
  | 11 => 0x138c
  | 12 => 0x138d
  | 13 => 0x98c
  | 14 => 0x98d
  | 15 => 0x98e
  | 16 => 0x150c
  | 17 => 0x150d
  | 18 => 0x150e
  | 19 => 0xa0c
  | 20 => 0xa0e
  | 21 => 0x209
  | 22 => 0x20c
  | 23 => 0x20d
  | 24 => 0x20e
  | 25 => 0xb09
  | 26 => 0xb0c
  | 27 => 0xb0d
  | 28 => 0xb0e
  | 29 => 0x1409
  | 30 => 0x140c
  | 31 => 0x140d
  | 32 => 0x140e
  | 33 => 0x1549
  | 34 => 0x154c
  | 35 => 0x154d
  | 36 => 0x154e
  | 37 => 0xb89
  | 38 => 0xb8c
  | 39 => 0xb8e
  | 40 => 0x1489
  | 41 => 0x148c
  | 42 => 0x148e
  | 43 => 0xbc9
  | 44 => 0xbcc
  | 45 => 0xbcd
  | 46 => 0xd09
  | 47 => 0xd0c
  | 48 => 0xd0e
  | 49 => 0x1609
  | 50 => 0x160c
  | 51 => 0x160e
  | 52 => 0x98956
  | 53 => 0x98954
  | 54 => 0x94994
  | 55 => 0xa0956
  | 56 => 0x94a14
  | 57 => 0xb8954
  | 58 => 0x94b96
  | 59 => 0xb8956
  | 60 => 0x148954
  | 61 => 0x95496
  | 62 => 0x289
  | 63 => 0xbc954
  | 64 => 0xbc955
  | 65 => 0x94bd4
  | 66 => 0xbcb
  | 67 => 0x1849
  | 68 => 0xb9394
  | 69 => 0x138b96
  | 70 => 0x4d
  | 71 => 0xbd394
  | 72 => 0xbd395
  | 73 => 0x138bd4
  | 74 => 0x4e
  | 75 => 0xb0994
  | 76 => 0xb0996
  | 77 => 0x98b16
  | 78 => 0x154994
  | 79 => 0x154996
  | 80 => 0x99556
  | 81 => 0xbc994
  | 82 => 0x19c9
  | 83 => 0xd0994
  | 84 => 0xd0996
  | 85 => 0x98d16
  | 86 => 0x160994
  | 87 => 0x160996
  | 88 => 0x99616
  | 89 => 0x409
  | 90 => 0x1889
  | 91 => 0x1649
  | 92 => 0x134b
  | 93 => 0x449
  | 94 => 0xb1514
  | 95 => 0xb1516
  | 96 => 0x150b16
  | 97 => 0xbd514
  | 98 => 0xd1516
  | 99 => 0xd1514
  | 100 => 0x150d16
  | 101 => 0x8d
  | 102 => 0xb8a16
  | 103 => 0xb8a14
  | 104 => 0xa0b96
  | 105 => 0xbca14
  | 106 => 0x124d
  | 107 => 0x128d
  | 108 => 0x1949
  | 109 => 0x134d
  | 110 => 0x749
  | 111 => 0xbcb14
  | 112 => 0xd0b14
  | 113 => 0xd0b16
  | 114 => 0xb0d14
  | 115 => 0x160b14
  | 116 => 0x160b16
  | 117 => 0xb1614
  | 118 => 0x15ca
  | 119 => 0x144b
  | 120 => 0xbd554
  | 121 => 0xd1556
  | 122 => 0xd1554
  | 123 => 0x154d14
  | 124 => 0xbcb94
  | 125 => 0xd0b96
  | 126 => 0xd0b94
  | 127 => 0xb8d14
  | 128 => 0x124e
  | 129 => 0x19cd
  | 130 => 0xd0bd4
  | 131 => 0xbcd14
  | 132 => 0x19cb
  | 133 => 0xbd614
  | 134 => 0x184e
  | 135 => 0xbc9895c
  | 136 => 0xbc9499c
  | 137 => 0xb894a1c
  | 138 => 0xb8a095e
  | 139 => 0xa094b9e
  | 140 => 0xbc94a1c
  | 141 => 0x94bd5
  | 142 => 0x19cc
  | 143 => 0x14b
  | 144 => 0x24b
  | 145 => 0x151556
  | 146 => 0xa1856
  | 147 => 0x14d
  | 148 => 0x15395
  | 149 => 0x75491
  | 150 => 0x14995
  | 151 => 0x74d11
  | 152 => 0x194e91
  | 153 => 0x20994
  | 154 => 0x21894
  | 155 => 0x21a14
  | 156 => 0x21716
  | 157 => 0x3ca
  | 158 => 0x141556
  | 159 => 0x140b56
  | 160 => 0x148956
  | 161 => 0x139256
  | 162 => 0x16ce
  | 163 => 0x21556
  | 164 => 0x155416
  | 165 => 0x140b16
  | 166 => 0x19cbd5
  | 167 => 0x185496
  | 168 => 0xe8bd1
  | 169 => 0xe9856
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1315
  | 6 => 2687
  | 5 => 1132
  | 4 => 77
  | 3 => 8
  | 2 => 1
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (53473+((h/438+packedAt gbK7 (48655+(h % 438)*11) 11) % 1736)*12) 12
  | 6 => packedAt gbK6 (140611+((h/895+packedAt gbK6 (128976+(h % 895)*13) 13) % 4291)*13) 13
  | 5 => packedAt gbK5 (70935+((h/377+packedAt gbK5 (66788+(h % 377)*11) 11) % 1359)*12) 12
  | 4 => packedAt gbK4 (5565+((h/25+packedAt gbK4 (5390+(h % 25)*7) 7) % 112)*8) 8
  | 3 => packedAt gbK3 (656+((h/2+packedAt gbK3 (648+(h % 2)*4) 4) % 15)*4) 4
  | 2 => packedAt gbK2 (93+((h/1+packedAt gbK2 (92+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc3f8fff9e187e3f07f8e038383c8219f1b3c93
  | 1 => 0xfc3f1c0601f87c7f81f003ffffd0c66424c0ff
  | 2 => 0x3fe007fe007f8001fffc03fc271878c70f1c
  | 3 => 0xffc00007ffff800001fffffc00381f80f80fe0
  | 4 => 0x7fffffffffe000000003fe000fff000
  | 5 => 0xfffffff80000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x404824306080a0900d82188889800089091c91
  | 1 => 0x84110840000804240010012122004224004026
  | 2 => 0x2a4092a200690114a4a80258830858470518
  | 3 => 0x6a80012555d500022949525801381580b80ac0
  | 4 => 0x220002079966524b70006010103da000f6a000
  | 5 => 0xb33493c01044000c40018060623eff76000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeeafeeefcc8fefefeeafeeefcc8fefefeeafeeefcc8fefefeeafeeefcc8fefefeeafeeefcc8fefefeeafeeefcc8fefefeeafeeefcc8fefefeeafeeefcc8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36396
namespace PEqualNP.Outside.L_meta_36396
open PEqualNP.Outside.L_meta_36396.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_4_0 : Interval s1Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 2 := bs1_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 7 := bs2_3_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 15 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_64 : Interval s3Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 68 := (concat bs3_3_0 (concat bs3_3_32 bs3_3_64))
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
theorem bs3_4_512 : Interval s3Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_544 : Interval s3Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_608 : Interval s3Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_640 : Interval s3Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_704 : Interval s3Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_736 : Interval s3Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_800 : Interval s3Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_832 : Interval s3Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_864 : Interval s3Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 894 := (concat (concat (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat (concat bs3_4_96 bs3_4_128) (concat bs3_4_160 bs3_4_192))) (concat (concat bs3_4_224 (concat bs3_4_256 bs3_4_288)) (concat (concat bs3_4_320 bs3_4_352) (concat bs3_4_384 bs3_4_416)))) (concat (concat (concat bs3_4_448 (concat bs3_4_480 bs3_4_512)) (concat (concat bs3_4_544 bs3_4_576) (concat bs3_4_608 bs3_4_640))) (concat (concat bs3_4_672 (concat bs3_4_704 bs3_4_736)) (concat (concat bs3_4_768 bs3_4_800) (concat bs3_4_832 bs3_4_864)))))
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
theorem bs3_5_640 : Interval s3Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_704 : Interval s3Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_736 : Interval s3Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_800 : Interval s3Atlas 5 800 20 := block_range (n:=20) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 820 := (concat (concat (concat (concat bs3_5_0 (concat bs3_5_32 bs3_5_64)) (concat bs3_5_96 (concat bs3_5_128 bs3_5_160))) (concat (concat bs3_5_192 (concat bs3_5_224 bs3_5_256)) (concat (concat bs3_5_288 bs3_5_320) (concat bs3_5_352 bs3_5_384)))) (concat (concat (concat bs3_5_416 (concat bs3_5_448 bs3_5_480)) (concat bs3_5_512 (concat bs3_5_544 bs3_5_576))) (concat (concat bs3_5_608 (concat bs3_5_640 bs3_5_672)) (concat (concat bs3_5_704 bs3_5_736) (concat bs3_5_768 bs3_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 44 := (concat bs3_6_0 bs3_6_32)
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
theorem bs4_4_64 : Interval s4Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 91 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 8 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 102 := (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 bs5_3_96))
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
theorem bs5_4_704 : Interval s5Atlas 4 704 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 725 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 (concat bs5_4_192 bs5_4_224)) (concat bs5_4_256 (concat bs5_4_288 bs5_4_320)))) (concat (concat (concat bs5_4_352 (concat bs5_4_384 bs5_4_416)) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512))) (concat (concat bs5_4_544 (concat bs5_4_576 bs5_4_608)) (concat bs5_4_640 (concat bs5_4_672 bs5_4_704)))))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 682 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 (concat bs5_5_192 bs5_5_224)) (concat bs5_5_256 (concat bs5_5_288 bs5_5_320)))) (concat (concat (concat bs5_5_352 bs5_5_384) (concat bs5_5_416 (concat bs5_5_448 bs5_5_480))) (concat (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)) (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)))))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 1 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 8 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 77 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_1120 : Interval gbAtlas 5 1120 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1132 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120))))))
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
theorem bgb_6_2656 : Interval gbAtlas 6 2656 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2687 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)))) (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)))))) (concat (concat (concat (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472))) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)))) (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792))) (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984))))) (concat (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)))) (concat (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464))) (concat (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)))))))
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
theorem bgb_7_1312 : Interval gbAtlas 7 1312 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1315 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat bgb_7_576 (concat bgb_7_608 bgb_7_640))))) (concat (concat (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800))) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)))) (concat (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120))) (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeafeeefcc8fefefeeafeeefcc8fefefeeafeeefcc8fefefeeafeeefcc8fefefeeafeeefcc8fefefeeafeeefcc8fefefeeafeeefcc8fefefeeafeeefcc8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124266 * 2 ^ 32 + 4277075144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36396.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,5]⟩,⟨.or,[1,3]⟩,⟨.and,[2,7]⟩,⟨.or,[0,4]⟩,⟨.or,[4,5]⟩,⟨.and,[0,10]⟩,⟨.or,[1,6]⟩,⟨.or,[11,12]⟩,⟨.or,[3,9]⟩,⟨.and,[13,14]⟩,⟨.or,[8,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277075144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277075144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36396

open PEqualNP.Outside.L_meta_36396 in
theorem PEqualNP.Outside.L_meta_36396 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277075144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277075144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
